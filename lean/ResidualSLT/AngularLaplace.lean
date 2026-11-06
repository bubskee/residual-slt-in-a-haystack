module
public import ResidualSLT.WeightedLaplace
public import ResidualSLT.QuantitativeCharts

/-! Quantitative critical angular integration on actual transverse chart images. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Filter Metric

@[expose] def criticalAngularKernel {n : ℕ} (r : ℕ) (f : (Fin n → ℝ) → ℝ)
    (N : ℝ) (z : ℝ × (Fin n → ℝ)) : ℝ :=
  z.1 ^ (r - 1) * Real.exp (-N * (z.1 ^ (2 * r) * (f z.2 ^ 2 + z.1 ^ (2 * r))))

theorem criticalAngularKernel_nonneg {n : ℕ} (r : ℕ) (f : (Fin n → ℝ) → ℝ)
    (N : ℝ) (z : ℝ × (Fin n → ℝ)) (hz : 0 ≤ z.1) : 0 ≤ criticalAngularKernel r f N z := by
  unfold criticalAngularKernel
  positivity

theorem criticalAngularKernel_integrable {n : ℕ} (r : ℕ) (f : (Fin n → ℝ) → ℝ)
    (hf : Continuous f) (N ε R : ℝ) :
    IntegrableOn (criticalAngularKernel r f N) (Ioo 0 ε ×ˢ closedBall 0 R) volume := by
  have hc : Continuous (criticalAngularKernel r f N) := by unfold criticalAngularKernel; fun_prop
  exact (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall 0 R))).mono_set
    (prod_mono Ioo_subset_Icc_self Subset.rfl)

theorem criticalAngularCylinder_integrable {n : ℕ} (r : ℕ) (j : Fin (n + 1))
    (N ε δ : ℝ) (B : Set (Fin n → ℝ)) (hB : volume B ≠ ⊤) (hB0 : volume B ≠ 0) :
    IntegrableOn (criticalAngularKernel r (fun y => y j) N)
      (Ioo 0 ε ×ˢ angularCylinder j (Ioo (-δ) δ) B) volume := by
  apply (angularCylinder_integrable_iff j (Ioo 0 ε) (Ioo (-δ) δ) B hB hB0
    (fun z : ℝ × ℝ => z.1 ^ (r - 1) * Real.exp (-N * (z.1 ^ (2*r) * (z.2 ^ 2 + z.1 ^ (2*r)))))).mpr
  exact ((by fun_prop : Continuous (fun z : ℝ × ℝ =>
    z.1 ^ (r - 1) * Real.exp (-N * (z.1 ^ (2*r) * (z.2 ^ 2 + z.1 ^ (2*r)))))).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)

theorem criticalAngularCylinder_integral {n : ℕ} (r : ℕ) (j : Fin (n + 1))
    (N ε δ : ℝ) (B : Set (Fin n → ℝ)) :
    (∫ z in Ioo 0 ε ×ˢ angularCylinder j (Ioo (-δ) δ) B, criticalAngularKernel r (fun y => y j) N z) =
      (volume B).toReal * weightedLaplaceSymmetric r ε δ N :=
  angularCylinder_integral j (Ioo 0 ε) (Ioo (-δ) δ) B
    (fun z : ℝ × ℝ => z.1 ^ (r-1) * Real.exp (-N * (z.1 ^ (2*r) * (z.2 ^ 2 + z.1 ^ (2*r)))))

/-- Numerical upper bound on a genuine chart patch using its proved outer cylinder. -/
theorem criticalAngular_patch_upper {n : ℕ} (r : ℕ) (hr : 0 < r)
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (c : TransverseChart f)
    (ε : ℝ) (hε : 0 < ε) {D : Set (Fin (n + 1) → ℝ)} (hD : MeasurableSet D)
    (hK : D ⊆ closedBall 0 1) (hsub : D ⊆ c.chart.source)
    (ht : ∀ y ∈ D, f y ∈ Ioo (-1) 1) :
    CriticalLaplaceUpper (fun N => ∫ z in Ioo 0 ε ×ˢ D, criticalAngularKernel r f N z) := by
  let B := ball (0 : Fin n → ℝ) 2
  have hB : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hB0 : volume B ≠ 0 := (measure_ball_pos volume 0 (by norm_num)).ne'
  have hv : 0 < (volume B).toReal := ENNReal.toReal_pos hB0 hB
  have houter : c.chart '' D ⊆ angularCylinder c.index (Ioo (-1) 1) B := by
    apply c.image_subset_cylinder ht
    intro y hy
    apply mem_ball_zero_iff.mpr
    apply lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg zero_le_one).mpr ?_) (by norm_num : (1:ℝ)<2)
    intro i
    exact (norm_le_pi_norm y _).trans (mem_closedBall_zero_iff.mp (hK hy))
  have hi := (weightedLaplaceSymmetric_has_order r hr ε 1 hε zero_lt_one).2.const_mul
    (c.lower⁻¹ * (volume B).toReal) (mul_pos (inv_pos.mpr c.lower_pos) hv)
  apply hi.mono
  apply Filter.Eventually.of_forall
  intro N
  let g := criticalAngularKernel r (fun y => y c.index) N
  have he : (fun z : ℝ × (Fin (n + 1) → ℝ) => g (z.1,c.chart z.2)) = criticalAngularKernel r f N := by
    funext z
    simp [g, criticalAngularKernel, c.coe_eq, transverseMap]
  have hsrc := (criticalAngularKernel_integrable r f hf.continuous N ε 1).mono_set (prod_mono Subset.rfl hK)
  have hchart := c.radial_integral_bounds hf measurableSet_Ioo hD hsub g
    (by rwa [he]) (by
      intro z hz
      change 0 ≤ (fun z => g (z.1,c.chart z.2)) z
      rw [he]
      exact criticalAngularKernel_nonneg r f N z hz.1.1.le)
  rw [he] at hchart
  have hmono := setIntegral_mono_set
    (criticalAngularCylinder_integrable r c.index N ε 1 B hB hB0)
    (by filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod
          ((measurableSet_Ioo.prod measurableSet_ball).preimage
            (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) c.index).measurable))] with z hz
        exact criticalAngularKernel_nonneg r _ N z hz.1.1.le)
    (Filter.Eventually.of_forall (prod_mono Subset.rfl houter))
  rw [criticalAngularCylinder_integral] at hmono
  have h := mul_le_mul_of_nonneg_left (hchart.1.trans hmono) (inv_nonneg.mpr c.lower_pos.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ c.lower_pos.ne', one_mul] using h

/-- An interior regular zero gives a quantitative lower witness with positive unused-coordinate volume. -/
theorem criticalAngular_lower_of_zero {n : ℕ} (r : ℕ) (hr : 0 < r)
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (ε : ℝ) (hε : 0 < ε) (y : Fin (n + 1) → ℝ) (hy : y ∈ ball 0 1)
    (hz : f y = 0) (hreg : ∃ j, fderiv ℝ f y (Pi.single j 1) ≠ 0) :
    CriticalLaplaceLower (fun N => ∫ z in Ioo 0 ε ×ˢ closedBall 0 1, criticalAngularKernel r f N z) := by
  obtain ⟨j,hj⟩ := hreg
  obtain ⟨c,hyc⟩ := exists_mem_transverseChart hf y j hj
  let D := ball (0 : Fin (n + 1) → ℝ) 1 ∩ c.chart.source
  have hD : IsOpen D := isOpen_ball.inter c.chart.open_source
  obtain ⟨δ,hδ,_,hinner⟩ := c.exists_inner_cylinder hD inter_subset_right ⟨hy,hyc⟩ hz
  let B := ball (fun i => y (c.index.succAbove i)) δ
  have hB : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hB0 : volume B ≠ 0 := (measure_ball_pos volume _ hδ).ne'
  have hv : 0 < (volume B).toReal := ENNReal.toReal_pos hB0 hB
  have hlo := (weightedLaplaceSymmetric_has_order r hr ε δ hε hδ).1.const_mul
    (c.upper⁻¹ * (volume B).toReal) (mul_pos (inv_pos.mpr c.upper_pos) hv)
  apply hlo.mono
  apply Filter.Eventually.of_forall
  intro N
  let g := criticalAngularKernel r (fun v => v c.index) N
  have he : (fun z : ℝ × (Fin (n+1) → ℝ) => g (z.1,c.chart z.2)) = criticalAngularKernel r f N := by
    funext z; simp [g,criticalAngularKernel,c.coe_eq,transverseMap]
  have hKD : D ⊆ closedBall 0 1 := fun _ h => ball_subset_closedBall h.1
  have hfull := criticalAngularKernel_integrable r f hf.continuous N ε 1
  have hsrc := hfull.mono_set (prod_mono Subset.rfl hKD)
  have himg : IntegrableOn g (Ioo 0 ε ×ˢ (c.chart '' D)) volume :=
    (c.radial_integrableOn_image_iff hf measurableSet_Ioo hD.measurableSet inter_subset_right g).mpr (by rwa [he])
  have hchart := c.radial_integral_bounds hf measurableSet_Ioo hD.measurableSet inter_subset_right g
    (by rwa [he]) (by
      intro z hz'
      change 0 ≤ (fun z => g (z.1,c.chart z.2)) z
      rw [he]
      exact criticalAngularKernel_nonneg r f N z hz'.1.1.le)
  rw [he] at hchart
  have hmono := setIntegral_mono_set himg
    (by filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod
          (c.chart.isOpen_image_of_subset_source hD inter_subset_right).measurableSet)] with z hz'
        exact criticalAngularKernel_nonneg r _ N z hz'.1.1.le)
    (Filter.Eventually.of_forall (prod_mono Subset.rfl hinner))
  rw [criticalAngularCylinder_integral] at hmono
  have hsrcfull := setIntegral_mono_set hfull
    (by filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_closedBall)] with z hz'
        exact criticalAngularKernel_nonneg r f N z hz'.1.1.le)
    (Filter.Eventually.of_forall (prod_mono Subset.rfl hKD))
  have h := mul_le_mul_of_nonneg_left (hmono.trans hchart.2) (inv_nonneg.mpr c.upper_pos.le)
  have hh : c.upper⁻¹ * (volume B).toReal * weightedLaplaceSymmetric r ε δ N ≤
      ∫ z in Ioo 0 ε ×ˢ D, criticalAngularKernel r f N z := by
    simpa only [← mul_assoc, inv_mul_cancel₀ c.upper_pos.ne', one_mul] using h
  exact hh.trans hsrcfull


/-- The off-zero radial Gaussian is bounded by the critical product model.
This avoids assigning a logarithm to the off-zero region itself. -/
theorem critical_radial_gaussian_upper (r : ℕ) (hr : 0 < r) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (c : ℝ) (hc : 0 < c) :
    CriticalLaplaceUpper (fun N => ∫ ρ : ℝ in Ioo 0 ε,
      ρ ^ (r-1) * Real.exp (-N * c ^ 2 * ρ ^ (2*r))) := by
  apply ((weightedLaplaceBox_has_order r hr ε 1 hε zero_lt_one).2.comp_mul (c ^ 2 / 2) (by positivity)).mono
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  let g : ℝ × ℝ → ℝ := fun z => z.1 ^ (r-1) *
    Real.exp (-(c ^ 2 / 2 * N) * (z.1 ^ (2*r) * (z.2 ^ 2 + z.1 ^ (2*r))))
  have hi : IntegrableOn g (Ioo 0 ε ×ˢ Ioo 0 1) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact ((by fun_prop : Continuous g).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hsections : IntegrableOn (fun ρ => ∫ t : ℝ in Ioo 0 1, g (ρ,t)) (Ioo 0 ε) volume := by
    rw [IntegrableOn, ← Measure.prod_restrict] at hi
    exact hi.integral_prod_left
  change _ ≤ ∫ z in Ioo 0 ε ×ˢ Ioo 0 1, g z
  rw [Measure.volume_eq_prod, setIntegral_prod _ hi]
  apply setIntegral_mono_on
    (((by fun_prop : Continuous (fun ρ : ℝ => ρ ^ (r-1) * Real.exp (-N*c^2*ρ^(2*r))))).continuousOn.integrableOn_compact
      isCompact_Icc |>.mono_set Ioo_subset_Icc_self) hsections measurableSet_Ioo
  intro ρ hρ
  have h := setIntegral_mono_on
    (integrableOn_const (by simp [Real.volume_Ioo]) : IntegrableOn
      (fun _ : ℝ => ρ ^ (r-1) * Real.exp (-N*c^2*ρ^(2*r))) (Ioo 0 1) volume)
    (((by fun_prop : Continuous (fun t => g (ρ,t)))).continuousOn.integrableOn_compact
      isCompact_Icc |>.mono_set Ioo_subset_Icc_self) measurableSet_Ioo ?_
  · simpa using h
  · intro t ht
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hρ.1.le _)
    apply Real.exp_le_exp.mpr
    have hρp : ρ ^ (2*r) ≤ 1 := pow_le_one₀ hρ.1.le (hρ.2.le.trans hε1)
    have htp : t ^ 2 ≤ 1 := pow_le_one₀ ht.1.le ht.2.le
    have hp : 0 ≤ N * c ^ 2 * ρ ^ (2*r) := mul_nonneg (mul_nonneg hN (sq_nonneg c)) (pow_nonneg hρ.1.le _)
    dsimp [g]
    nlinarith [mul_le_mul_of_nonneg_left (show t ^ 2 + ρ ^ (2*r) ≤ 2 by linarith) hp]

/-- Uniformly nonzero angular regions have a quantitative upper bound. -/
theorem criticalAngular_off_zero_upper {n : ℕ} (r : ℕ) (hr : 0 < r)
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D) (hK : D ⊆ closedBall 0 1)
    (c : ℝ) (hc : 0 < c) (hb : ∀ y ∈ D, c ≤ |f y|) :
    CriticalLaplaceUpper (fun N => ∫ z in Ioo 0 ε ×ˢ D, criticalAngularKernel r f N z) := by
  have hfinite : volume D ≠ ⊤ := ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hK)
  have hupper := (critical_radial_gaussian_upper r hr ε hε hε1 c hc).const_mul_nonneg
    (volume D).toReal ENNReal.toReal_nonneg
  apply hupper.mono
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  let g : ℝ → ℝ := fun ρ => ρ ^ (r-1) * Real.exp (-N*c^2*ρ^(2*r))
  have hg : IntegrableOn g (Ioo 0 ε) volume :=
    ((by fun_prop : Continuous g).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hprod := hg.mul_prod (integrableOn_const hfinite : IntegrableOn (fun _ : Fin n → ℝ => (1:ℝ)) D volume)
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hprod
  have hi := (criticalAngularKernel_integrable r f hf N ε 1).mono_set (prod_mono Subset.rfl hK)
  have h := setIntegral_mono_on hi hprod (measurableSet_Ioo.prod hD) ?_
  · rw [Measure.volume_eq_prod, setIntegral_prod_mul (μ := volume) (ν := volume) g (fun _ : Fin n → ℝ => (1:ℝ)) (Ioo 0 ε) D] at h
    simpa [g,Measure.real,mul_comm,Measure.volume_eq_prod] using! h
  · intro z hz
    simp only [mul_one]
    unfold criticalAngularKernel
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hz.1.1.le _)
    apply Real.exp_le_exp.mpr
    have hcf : c ^ 2 ≤ f z.2 ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ hc.le (hb z.2 hz.2) 2
    have hρ : 0 ≤ z.1 ^ (2*r) := pow_nonneg hz.1.1.le _
    nlinarith [mul_le_mul_of_nonneg_left (show c^2 ≤ f z.2 ^ 2 + z.1 ^ (2*r) by linarith)
      (mul_nonneg hN hρ)]

/-- Finite transverse charts and their noncancellation complement give a whole-cube upper bound. -/
theorem criticalAngular_regular_upper (r n : ℕ) (hr : 0 < r)
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hreg : ∀ y ∈ closedBall 0 1, f y = 0 → ∃ j, fderiv ℝ f y (Pi.single j 1) ≠ 0) :
    CriticalLaplaceUpper (fun N => ∫ z in Ioo 0 ε ×ˢ closedBall 0 1, criticalAngularKernel r f N z) := by
  classical
  let K := closedBall (0 : Fin (n+1) → ℝ) 1
  obtain ⟨charts,hcover⟩ := finite_transverse_chart_cover hf
    ((isCompact_closedBall (0 : Fin (n+1) → ℝ) 1).inter_right
      (isClosed_singleton.preimage hf.continuous)) (fun y hy => hreg y hy.1 hy.2)
  let Uc := fun c : TransverseChart f => c.chart.source ∩ f ⁻¹' Ioo (-1) 1
  let U := ⋃ c ∈ charts, Uc c
  have hUc (c : TransverseChart f) : IsOpen (Uc c) :=
    c.chart.open_source.inter (hf.continuous.isOpen_preimage _ isOpen_Ioo)
  have hU : IsOpen U := isOpen_iUnion fun c => isOpen_iUnion fun _ => hUc c
  have hzU : ∀ y ∈ K, f y = 0 → y ∈ U := by
    intro y hy hz
    obtain ⟨c,hc,hyc⟩ := mem_iUnion₂.mp (hcover ⟨hy,hz⟩)
    exact mem_iUnion₂.mpr ⟨c,hc,hyc,by change f y ∈ Ioo (-1) 1; rw [hz]; norm_num⟩
  obtain ⟨b,hb,hbK⟩ := compact_complement_abs_lower hf.continuous (isCompact_closedBall 0 1) hU hzU
  have hoff := criticalAngular_off_zero_upper r hr f hf.continuous ε hε hε1
    (measurableSet_closedBall.diff hU.measurableSet) sdiff_subset b hb hbK
  have hp (c : TransverseChart f) : CriticalLaplaceUpper
      (fun N => ∫ z in Ioo 0 ε ×ˢ (K ∩ Uc c), criticalAngularKernel r f N z) :=
    criticalAngular_patch_upper r hr f hf c ε hε
      (measurableSet_closedBall.inter (hUc c).measurableSet) inter_subset_left
      (fun _ h => h.2.1) (fun _ h => h.2.2)
  apply (hoff.add (CriticalLaplaceUpper.finset_sum charts _ (fun c _ => hp c))).mono
  apply Filter.Eventually.of_forall
  intro N
  have hi := criticalAngularKernel_integrable r f hf.continuous N ε 1
  apply setIntegral_le_add_sum_of_cover volume charts (criticalAngularKernel r f N)
    (Ioo 0 ε ×ˢ K) (Ioo 0 ε ×ˢ (K \ U)) (fun c => Ioo 0 ε ×ˢ (K ∩ Uc c))
    (measurableSet_Ioo.prod measurableSet_closedBall)
    (measurableSet_Ioo.prod (measurableSet_closedBall.diff hU.measurableSet))
    (fun c _ => measurableSet_Ioo.prod (measurableSet_closedBall.inter (hUc c).measurableSet))
    hi (hi.mono_set (prod_mono Subset.rfl sdiff_subset))
    (fun _ _ => hi.mono_set (prod_mono Subset.rfl inter_subset_left))
  · intro z hz
    by_cases hu : z.2 ∈ U
    · obtain ⟨c,hc,hzc⟩ := mem_iUnion₂.mp hu
      exact Or.inr (mem_iUnion₂.mpr ⟨c,hc,hz.1,hz.2,hzc⟩)
    · exact Or.inl ⟨hz.1,hz.2,hu⟩
  · intro z hz
    apply criticalAngularKernel_nonneg
    rcases hz with hz | hz
    · exact hz.1.1.le
    · obtain ⟨c,hc,hzc⟩ := mem_iUnion₂.mp hz
      exact hzc.1.1.le

/-- Critical angular Laplace order, including the logarithm, for any regular zero set
with one interior zero. -/
theorem criticalAngular_has_order (r n : ℕ) (hr : 0 < r)
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hreg : ∀ y ∈ closedBall 0 1, f y = 0 → ∃ j, fderiv ℝ f y (Pi.single j 1) ≠ 0)
    (hzero : ∃ y ∈ ball 0 1, f y = 0) :
    HasCriticalLaplaceOrder (fun N => ∫ z in Ioo 0 ε ×ˢ closedBall 0 1, criticalAngularKernel r f N z) := by
  obtain ⟨y,hy,hz⟩ := hzero
  exact ⟨criticalAngular_lower_of_zero r hr f hf ε hε y hy hz
    (hreg y (ball_subset_closedBall hy) hz), criticalAngular_regular_upper r n hr f hf ε hε hε1 hreg⟩

end ResidualSLT
