module
public import ResidualSLT.AngularLaplace
public import ResidualSLT.PowerWeightedLaplace
public import ResidualSLT.QuantitativeCharts

/-! Off-critical angular integration with arbitrary radial density and exact pure-power rates. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Filter Metric

@[expose] def powerAngularKernel {n : ℕ} (a r q : ℕ) (f : (Fin n → ℝ) → ℝ)
    (N : ℝ) (z : ℝ × (Fin n → ℝ)) : ℝ :=
  z.1 ^ (a - 1) * Real.exp (-N * (z.1 ^ (2 * r) * (f z.2 ^ 2 + z.1 ^ (2 * q))))

theorem powerAngularKernel_nonneg {n : ℕ} (a r q : ℕ) (f : (Fin n → ℝ) → ℝ)
    (N : ℝ) (z : ℝ × (Fin n → ℝ)) (hz : 0 ≤ z.1) : 0 ≤ powerAngularKernel a r q f N z := by
  unfold powerAngularKernel
  positivity

theorem powerAngularKernel_integrable {n : ℕ} (a r q : ℕ) (f : (Fin n → ℝ) → ℝ)
    (hf : Continuous f) (N ε R : ℝ) :
    IntegrableOn (powerAngularKernel a r q f N) (Ioo 0 ε ×ˢ closedBall 0 R) volume := by
  have hc : Continuous (powerAngularKernel a r q f N) := by unfold powerAngularKernel; fun_prop
  exact (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall 0 R))).mono_set
    (prod_mono Ioo_subset_Icc_self Subset.rfl)

theorem powerAngularCylinder_integrable {n : ℕ} (a r q : ℕ) (j : Fin (n + 1))
    (N ε δ : ℝ) (B : Set (Fin n → ℝ)) (hB : volume B ≠ ⊤) (hB0 : volume B ≠ 0) :
    IntegrableOn (powerAngularKernel a r q (fun y => y j) N)
      (Ioo 0 ε ×ˢ angularCylinder j (Ioo (-δ) δ) B) volume := by
  apply (angularCylinder_integrable_iff j (Ioo 0 ε) (Ioo (-δ) δ) B hB hB0
    (fun z : ℝ × ℝ => z.1 ^ (a - 1) * Real.exp (-N * (z.1 ^ (2*r) * (z.2 ^ 2 + z.1 ^ (2*q)))))).mpr
  exact ((by fun_prop : Continuous (fun z : ℝ × ℝ =>
    z.1 ^ (a - 1) * Real.exp (-N * (z.1 ^ (2*r) * (z.2 ^ 2 + z.1 ^ (2*q)))))).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)

theorem powerAngularCylinder_integral {n : ℕ} (a r q : ℕ) (j : Fin (n + 1))
    (N ε δ : ℝ) (B : Set (Fin n → ℝ)) :
    (∫ z in Ioo 0 ε ×ˢ angularCylinder j (Ioo (-δ) δ) B, powerAngularKernel a r q (fun y => y j) N z) =
      (volume B).toReal * powerWeightedSymmetric a r q ε δ N :=
  angularCylinder_integral j (Ioo 0 ε) (Ioo (-δ) δ) B
    (fun z : ℝ × ℝ => z.1 ^ (a-1) * Real.exp (-N * (z.1 ^ (2*r) * (z.2 ^ 2 + z.1 ^ (2*q)))))

/-- Numerical upper bound on a genuine chart patch using its proved outer cylinder. -/
theorem powerAngular_patch_upper {n : ℕ} (a r q : ℕ) (ha : 0 < a) (hr : 0 < r) (hq : 0 < q) (hne : a ≠ r)
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (c : TransverseChart f)
    (ε : ℝ) (hε : 0 < ε) {D : Set (Fin (n + 1) → ℝ)} (hD : MeasurableSet D)
    (hK : D ⊆ closedBall 0 1) (hsub : D ⊆ c.chart.source)
    (ht : ∀ y ∈ D, f y ∈ Ioo (-1) 1) :
    PowerLaplaceUpper (coneLaplaceExponent a r q) (fun N => ∫ z in Ioo 0 ε ×ˢ D, powerAngularKernel a r q f N z) := by
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
  have hi := (powerWeightedSymmetric_has_order a r q ha hr hq hne ε 1 hε zero_lt_one).2.const_mul
    (c.lower⁻¹ * (volume B).toReal) (mul_pos (inv_pos.mpr c.lower_pos) hv)
  apply hi.mono
  apply Filter.Eventually.of_forall
  intro N
  let g := powerAngularKernel a r q (fun y => y c.index) N
  have he : (fun z : ℝ × (Fin (n + 1) → ℝ) => g (z.1,c.chart z.2)) = powerAngularKernel a r q f N := by
    funext z
    simp [g, powerAngularKernel, c.coe_eq, transverseMap]
  have hsrc := (powerAngularKernel_integrable a r q f hf.continuous N ε 1).mono_set (prod_mono Subset.rfl hK)
  have hchart := c.radial_integral_bounds hf measurableSet_Ioo hD hsub g
    (by rwa [he]) (by
      intro z hz
      change 0 ≤ (fun z => g (z.1,c.chart z.2)) z
      rw [he]
      exact powerAngularKernel_nonneg a r q f N z hz.1.1.le)
  rw [he] at hchart
  have hmono := setIntegral_mono_set
    (powerAngularCylinder_integrable a r q c.index N ε 1 B hB hB0)
    (by filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod
          ((measurableSet_Ioo.prod measurableSet_ball).preimage
            (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) c.index).measurable))] with z hz
        exact powerAngularKernel_nonneg a r q _ N z hz.1.1.le)
    (Filter.Eventually.of_forall (prod_mono Subset.rfl houter))
  rw [powerAngularCylinder_integral] at hmono
  have h := mul_le_mul_of_nonneg_left (hchart.1.trans hmono) (inv_nonneg.mpr c.lower_pos.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ c.lower_pos.ne', one_mul] using h

/-- An interior regular zero gives a quantitative lower witness with positive unused-coordinate volume. -/
theorem powerAngular_lower_of_zero {n : ℕ} (a r q : ℕ) (ha : 0 < a) (hr : 0 < r) (hq : 0 < q) (hne : a ≠ r)
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (R ε : ℝ) (hε : 0 < ε) (y : Fin (n + 1) → ℝ) (hy : y ∈ ball 0 R)
    (hz : f y = 0) (hreg : ∃ j, fderiv ℝ f y (Pi.single j 1) ≠ 0) :
    PowerLaplaceLower (coneLaplaceExponent a r q) (fun N => ∫ z in Ioo 0 ε ×ˢ closedBall 0 R, powerAngularKernel a r q f N z) := by
  obtain ⟨j,hj⟩ := hreg
  obtain ⟨c,hyc⟩ := exists_mem_transverseChart hf y j hj
  let D := ball (0 : Fin (n + 1) → ℝ) R ∩ c.chart.source
  have hD : IsOpen D := isOpen_ball.inter c.chart.open_source
  obtain ⟨δ,hδ,_,hinner⟩ := c.exists_inner_cylinder hD inter_subset_right ⟨hy,hyc⟩ hz
  let B := ball (fun i => y (c.index.succAbove i)) δ
  have hB : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hB0 : volume B ≠ 0 := (measure_ball_pos volume _ hδ).ne'
  have hv : 0 < (volume B).toReal := ENNReal.toReal_pos hB0 hB
  have hlo := (powerWeightedSymmetric_has_order a r q ha hr hq hne ε δ hε hδ).1.const_mul
    (c.upper⁻¹ * (volume B).toReal) (mul_pos (inv_pos.mpr c.upper_pos) hv)
  apply hlo.mono
  apply Filter.Eventually.of_forall
  intro N
  let g := powerAngularKernel a r q (fun v => v c.index) N
  have he : (fun z : ℝ × (Fin (n+1) → ℝ) => g (z.1,c.chart z.2)) = powerAngularKernel a r q f N := by
    funext z; simp [g,powerAngularKernel,c.coe_eq,transverseMap]
  have hKD : D ⊆ closedBall 0 R := fun _ h => ball_subset_closedBall h.1
  have hfull := powerAngularKernel_integrable a r q f hf.continuous N ε R
  have hsrc := hfull.mono_set (prod_mono Subset.rfl hKD)
  have himg : IntegrableOn g (Ioo 0 ε ×ˢ (c.chart '' D)) volume :=
    (c.radial_integrableOn_image_iff hf measurableSet_Ioo hD.measurableSet inter_subset_right g).mpr (by rwa [he])
  have hchart := c.radial_integral_bounds hf measurableSet_Ioo hD.measurableSet inter_subset_right g
    (by rwa [he]) (by
      intro z hz'
      change 0 ≤ (fun z => g (z.1,c.chart z.2)) z
      rw [he]
      exact powerAngularKernel_nonneg a r q f N z hz'.1.1.le)
  rw [he] at hchart
  have hmono := setIntegral_mono_set himg
    (by filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod
          (c.chart.isOpen_image_of_subset_source hD inter_subset_right).measurableSet)] with z hz'
        exact powerAngularKernel_nonneg a r q _ N z hz'.1.1.le)
    (Filter.Eventually.of_forall (prod_mono Subset.rfl hinner))
  rw [powerAngularCylinder_integral] at hmono
  have hsrcfull := setIntegral_mono_set hfull
    (by filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_closedBall)] with z hz'
        exact powerAngularKernel_nonneg a r q f N z hz'.1.1.le)
    (Filter.Eventually.of_forall (prod_mono Subset.rfl hKD))
  have h := mul_le_mul_of_nonneg_left (hmono.trans hchart.2) (inv_nonneg.mpr c.upper_pos.le)
  have hh : c.upper⁻¹ * (volume B).toReal * powerWeightedSymmetric a r q ε δ N ≤
      ∫ z in Ioo 0 ε ×ˢ D, powerAngularKernel a r q f N z := by
    simpa only [← mul_assoc, inv_mul_cancel₀ c.upper_pos.ne', one_mul] using h
  exact hh.trans hsrcfull


/-- Uniformly nonzero angular regions have a quantitative upper bound. -/
theorem powerAngular_off_zero_upper {n : ℕ} (a r q : ℕ) (ha : 0 < a) (hr : 0 < r)
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) (ε : ℝ) (_hε : 0 < ε) (_hε1 : ε ≤ 1)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D) (hK : D ⊆ closedBall 0 1)
    (c : ℝ) (hc : 0 < c) (hb : ∀ y ∈ D, c ≤ |f y|) :
    PowerLaplaceUpper (coneLaplaceExponent a r q) (fun N => ∫ z in Ioo 0 ε ×ˢ D, powerAngularKernel a r q f N z) := by
  have hfinite : volume D ≠ ⊤ := ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hK)
  have hgauss : PowerLaplaceUpper ((a:ℝ)/(2*r)) (fun N => ∫ u : ℝ in Ioo 0 ε,
      u^(a-1)*Real.exp (-N*c^2*u^(2*r))) := by
    have hh := (radialGamma_laplace_upper a r ha hr ε).comp_mul (c^2) (sq_pos_of_pos hc)
    simpa only [mul_comm (c^2),neg_mul] using hh
  have hupper := (hgauss.weaken (min_le_left _ _ : coneLaplaceExponent a r q ≤ (a:ℝ)/(2*r))).const_mul_nonneg
    (volume D).toReal ENNReal.toReal_nonneg
  apply hupper.mono
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  let g : ℝ → ℝ := fun ρ => ρ ^ (a-1) * Real.exp (-N*c^2*ρ^(2*r))
  have hg : IntegrableOn g (Ioo 0 ε) volume :=
    ((by fun_prop : Continuous g).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hprod := hg.mul_prod (integrableOn_const hfinite : IntegrableOn (fun _ : Fin n → ℝ => (1:ℝ)) D volume)
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hprod
  have hi := (powerAngularKernel_integrable a r q f hf N ε 1).mono_set (prod_mono Subset.rfl hK)
  have h := setIntegral_mono_on hi hprod (measurableSet_Ioo.prod hD) ?_
  · rw [Measure.volume_eq_prod, setIntegral_prod_mul (μ := volume) (ν := volume) g (fun _ : Fin n → ℝ => (1:ℝ)) (Ioo 0 ε) D] at h
    simpa [g,Measure.real,mul_comm,Measure.volume_eq_prod] using! h
  · intro z hz
    simp only [mul_one]
    unfold powerAngularKernel
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hz.1.1.le _)
    apply Real.exp_le_exp.mpr
    have hcf : c ^ 2 ≤ f z.2 ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ hc.le (hb z.2 hz.2) 2
    have hρ : 0 ≤ z.1 ^ (2*r) := pow_nonneg hz.1.1.le _
    nlinarith [mul_le_mul_of_nonneg_left (show c^2 ≤ f z.2 ^ 2 + z.1 ^ (2*q) by linarith [pow_nonneg hz.1.1.le (2*q)])
      (mul_nonneg hN hρ)]

/-- Finite transverse charts and their noncancellation complement give a whole-cube upper bound. -/
theorem powerAngular_regular_upper (a r q n : ℕ) (ha : 0 < a) (hr : 0 < r) (hq : 0 < q) (hne : a ≠ r)
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hreg : ∀ y ∈ closedBall 0 1, f y = 0 → ∃ j, fderiv ℝ f y (Pi.single j 1) ≠ 0) :
    PowerLaplaceUpper (coneLaplaceExponent a r q) (fun N => ∫ z in Ioo 0 ε ×ˢ closedBall 0 1, powerAngularKernel a r q f N z) := by
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
  have hoff := powerAngular_off_zero_upper a r q ha hr f hf.continuous ε hε hε1
    (measurableSet_closedBall.diff hU.measurableSet) sdiff_subset b hb hbK
  have hp (c : TransverseChart f) : PowerLaplaceUpper (coneLaplaceExponent a r q)
      (fun N => ∫ z in Ioo 0 ε ×ˢ (K ∩ Uc c), powerAngularKernel a r q f N z) :=
    powerAngular_patch_upper a r q ha hr hq hne f hf c ε hε
      (measurableSet_closedBall.inter (hUc c).measurableSet) inter_subset_left
      (fun _ h => h.2.1) (fun _ h => h.2.2)
  apply (hoff.add (PowerLaplaceUpper.finset_sum charts _ (fun c _ => hp c))).mono
  apply Filter.Eventually.of_forall
  intro N
  have hi := powerAngularKernel_integrable a r q f hf.continuous N ε 1
  apply setIntegral_le_add_sum_of_cover volume charts (powerAngularKernel a r q f N)
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
    apply powerAngularKernel_nonneg
    rcases hz with hz | hz
    · exact hz.1.1.le
    · obtain ⟨c,hc,hzc⟩ := mem_iUnion₂.mp hz
      exact hzc.1.1.le


end ResidualSLT
