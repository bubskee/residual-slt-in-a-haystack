module
public import ResidualSLT.ConeReduction

/-! Product regions for actual angular chart images and integration of unused coordinates. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Metric

@[expose] def angularCylinder {n : ℕ} (j : Fin (n + 1)) (T : Set ℝ)
    (B : Set (Fin n → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j) ⁻¹' (T ×ˢ B)

/-- Splitting off the selected angular coordinate preserves volume exactly. -/
theorem angularCylinder_integrable_iff {n : ℕ} (j : Fin (n + 1))
    (R T : Set ℝ) (B : Set (Fin n → ℝ)) (hB : volume B ≠ ⊤) (hB0 : volume B ≠ 0)
    (g : ℝ × ℝ → ℝ) :
    IntegrableOn (fun z : ℝ × (Fin (n + 1) → ℝ) => g (z.1, z.2 j))
      (R ×ˢ angularCylinder j T B) volume ↔ IntegrableOn g (R ×ˢ T) volume := by
  let M := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
  let e := ((MeasurableEquiv.refl ℝ).prodCongr M).trans
    (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × (Fin n → ℝ) ≃ᵐ ℝ × (ℝ × (Fin n → ℝ))).symm
  have he : MeasurePreserving e volume volume :=
    (MeasurePreserving.symm _ volume_preserving_prodAssoc).comp
      ((MeasurePreserving.id volume).prod (volume_preserving_piFinSuccAbove _ j))
  have hi := he.integrableOn_comp_preimage e.measurableEmbedding
    (f := fun z : (ℝ × ℝ) × (Fin n → ℝ) => g z.1) (s := (R ×ˢ T) ×ˢ B)
  have hpre : e ⁻¹' ((R ×ˢ T) ×ˢ B) = R ×ˢ angularCylinder j T B := by
    ext z
    change (z.1 ∈ R ∧ z.2 j ∈ T) ∧ (fun i => z.2 (j.succAbove i)) ∈ B ↔
      z.1 ∈ R ∧ z.2 j ∈ T ∧ (fun i => z.2 (j.succAbove i)) ∈ B
    tauto
  rw [hpre] at hi
  change IntegrableOn (fun z : ℝ × (Fin (n + 1) → ℝ) => g (z.1, z.2 j)) _ volume ↔ _ at hi
  rw [hi, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  let : IsFiniteMeasure (volume.restrict B) := ⟨by simpa using hB.lt_top⟩
  exact Integrable.comp_fst_iff (by intro h; exact hB0 (Measure.restrict_eq_zero.mp h))

/-- The genuine chart image has an outer product bound when the selected function
and the unchanged angular coordinates have the displayed bounds. -/
theorem TransverseChart.image_subset_cylinder {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (c : TransverseChart f)
    {D : Set (Fin (n + 1) → ℝ)} {T : Set ℝ} {B : Set (Fin n → ℝ)}
    (ht : ∀ y ∈ D, f y ∈ T)
    (hb : ∀ y ∈ D, (fun i => y (c.index.succAbove i)) ∈ B) :
    c.chart '' D ⊆ angularCylinder c.index T B := by
  rintro _ ⟨y, hy, rfl⟩
  change c.chart y c.index ∈ T ∧ (fun i => c.chart y (c.index.succAbove i)) ∈ B
  rw [c.coe_eq]
  simpa only [transverseMap, ite_true, Fin.succAbove_ne, ite_false] using ⟨ht y hy, hb y hy⟩

/-- An open chart image around a zero contains a genuine product region. -/
theorem TransverseChart.exists_inner_cylinder {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (c : TransverseChart f)
    {D : Set (Fin (n + 1) → ℝ)} (hD : IsOpen D) (hsub : D ⊆ c.chart.source)
    {a : Fin (n + 1) → ℝ} (ha : a ∈ D) (hzero : f a = 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      angularCylinder c.index (Ioo (-δ) δ)
        (ball (fun i => a (c.index.succAbove i)) δ) ⊆ c.chart '' D := by
  have hopen : IsOpen (c.chart '' D) := c.chart.isOpen_image_of_subset_source hD hsub
  obtain ⟨η, hη, hb⟩ := Metric.isOpen_iff.mp hopen _ ⟨a, ha, rfl⟩
  let δ := min η 1
  have hδ : 0 < δ := lt_min hη zero_lt_one
  refine ⟨δ, hδ, min_le_right _ _, ?_⟩
  intro u hu
  apply hb
  apply ball_subset_ball (min_le_left η 1)
  rw [mem_ball, dist_pi_lt_iff hδ]
  intro i
  change u c.index ∈ Ioo (-δ) δ ∧
    (fun k => u (c.index.succAbove k)) ∈ ball (fun k => a (c.index.succAbove k)) δ at hu
  rw [c.coe_eq]
  by_cases hi : i = c.index
  · subst i
    simpa [transverseMap, hzero, Real.dist_eq, abs_lt] using hu.1
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
    simpa only [transverseMap, Fin.succAbove_ne, ite_false] using
      (dist_pi_lt_iff hδ).mp (mem_ball.mp hu.2) k


/-- Convergence on the entire compact angular cube follows from finite charts,
proved outer cylinder containment, and the complementary noncancellation region. -/
theorem weightedAngular_integrable_cube (r n : ℕ) (hr : 0 < r)
    (a : ℝ) (ha : 0 < a) (s : ℝ) (hs : 0 ≤ s)
    (hcrit : s < min (a / (2 * r)) ((a + r) / (2 * ((r : ℝ) + r)))) :
    IntegrableOn (fun z : ℝ × (Fin (n + 1) → ℝ) =>
      weightedCancellation a r r s (z.1, angularFermat r 1 z.2))
      (Ioo 0 1 ×ˢ closedBall 0 1) volume := by
  classical
  let f := @angularFermat r 1 (n + 1)
  let K := closedBall (0 : Fin (n + 1) → ℝ) 1
  obtain ⟨charts, hcover⟩ := angularFermat_finite_cover r (n + 1) hr 1 (by norm_num) 1
  let Uc := fun c : TransverseChart f => c.chart.source ∩ f ⁻¹' Ioo (-1) 1
  let U := ⋃ c ∈ charts, Uc c
  have hUc (c : TransverseChart f) : IsOpen (Uc c) :=
    c.chart.open_source.inter ((angularFermat_contDiff r (n + 1) 1).continuous.isOpen_preimage _ isOpen_Ioo)
  have hU : IsOpen U := isOpen_iUnion fun c => isOpen_iUnion fun _ => hUc c
  have hzU : ∀ y ∈ K, f y = 0 → y ∈ U := by
    intro y hy hz
    obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.mp (hcover ⟨hy, hz⟩)
    exact mem_iUnion₂.mpr ⟨c, hc, hyc, by change f y ∈ Ioo (-1) 1; rw [hz]; norm_num⟩
  obtain ⟨b, hb, hbK⟩ := compact_complement_abs_lower
    (angularFermat_contDiff r (n + 1) 1).continuous (isCompact_closedBall 0 1) hU hzU
  have hoff : IntegrableOn (fun z : ℝ × (Fin (n + 1) → ℝ) =>
      weightedCancellation a r r s (z.1, f z.2)) (Ioo 0 1 ×ˢ (K \ U)) volume := by
    rw [Measure.volume_eq_prod]
    apply weightedAngular_integrable_off_zero volume (measurableSet_closedBall.diff hU.measurableSet)
      (ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono sdiff_subset))
      (angularFermat_contDiff r (n + 1) 1).continuous.measurable hb hbK a r s hs _ 1 zero_lt_one
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * (r : ℝ))).mp (lt_min_iff.mp hcrit).1
    nlinarith
  have hpatch (c : TransverseChart f) : IntegrableOn
      (fun z : ℝ × (Fin (n + 1) → ℝ) => weightedCancellation a r r s (z.1, f z.2))
      (Ioo 0 1 ×ˢ (K ∩ Uc c)) volume := by
    have houter : c.chart '' (K ∩ Uc c) ⊆
        angularCylinder c.index (Ioo (-1) 1) (ball (0 : Fin n → ℝ) 2) := by
      apply c.image_subset_cylinder
      · intro y hy; exact hy.2.2
      · intro y hy
        apply mem_ball_zero_iff.mpr
        apply lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr ?_) (by norm_num : (1 : ℝ) < 2)
        intro i
        exact (norm_le_pi_norm y _).trans (mem_closedBall_zero_iff.mp hy.1)
    have hi := (angularCylinder_integrable_iff c.index (Ioo 0 1) (Ioo (-1) 1)
      (ball (0 : Fin n → ℝ) 2) measure_ball_lt_top.ne
      (measure_ball_pos volume 0 (by norm_num)).ne' (weightedCancellation a r r s)).mpr
        ((weightedCancellation_symmetric_integrableOn_iff a ha r r hr hr s).mpr hcrit)
    exact (weightedAngular_chart_iff (angularFermat_contDiff r (n + 1) 1) c
      measurableSet_Ioo (measurableSet_closedBall.inter (hUc c).measurableSet)
      (fun _ h => h.2.1) a r s).mpr (hi.mono_set (prod_mono Subset.rfl houter))
  have hall := hoff.union ((integrableOn_finset_iUnion (s := charts)).mpr (fun c _ => hpatch c))
  apply hall.mono_set
  intro z hz
  by_cases hu : z.2 ∈ U
  · obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp hu
    exact Or.inr (mem_iUnion₂.mpr ⟨c, hc, hz.1, hz.2, hzc⟩)
  · exact Or.inl ⟨hz.1, hz.2, hu⟩

/-- An interior angular cancellation point supplies a product region of positive
unused-coordinate measure, hence both strict inequalities including endpoint failure. -/
theorem weightedAngular_necessary_of_interior_zero (r n : ℕ) (hr : 0 < r)
    (a : ℝ) (ha : 0 < a) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ)
    (y : Fin (n + 1) → ℝ) (hy : y ∈ ball 0 1) (hz : angularFermat r 1 y = 0)
    (hi : IntegrableOn (fun z : ℝ × (Fin (n + 1) → ℝ) =>
      weightedCancellation a r r s (z.1, angularFermat r 1 z.2))
      (Ioo 0 ε ×ˢ closedBall 0 1) volume) :
    s < min (a / (2 * r)) ((a + r) / (2 * ((r : ℝ) + r))) := by
  obtain ⟨c, hyc, _⟩ := angularFermat_exists_chart r (n + 1) hr 1 (by norm_num) y hz
  let D := ball (0 : Fin (n + 1) → ℝ) 1 ∩ c.chart.source
  have hD : IsOpen D := isOpen_ball.inter c.chart.open_source
  obtain ⟨δ, hδ, hδ1, hinner⟩ := c.exists_inner_cylinder hD inter_subset_right ⟨hy, hyc⟩ hz
  have hlocal := (weightedAngular_chart_iff (angularFermat_contDiff r (n + 1) 1) c
    measurableSet_Ioo hD.measurableSet inter_subset_right a r s).mp
      (hi.mono_set (prod_mono Subset.rfl (fun _ h => ball_subset_closedBall h.1)))
  have hrect := (angularCylinder_integrable_iff c.index (Ioo 0 ε) (Ioo (-δ) δ)
    (ball (fun i => y (c.index.succAbove i)) δ) measure_ball_lt_top.ne
    (measure_ball_pos volume _ hδ).ne' (weightedCancellation a r r s)).mp
      (hlocal.mono_set (prod_mono Subset.rfl hinner))
  exact (weightedCancellation_local_integrableOn_iff a ha r r hr hr ε δ hε hε1 hδ hδ1 s).mp hrect


/-- A nonzero angular measure already forces the radial obstruction. This also
handles depth two without assuming an interior cancellation point in its angular cube. -/
theorem weightedAngular_radial_necessary {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] {K : Set α} (_hK : MeasurableSet K) (hK0 : μ K ≠ 0)
    (f : α → ℝ) (a : ℝ) (r : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (s : ℝ) (hs : 0 ≤ s)
    (hi : IntegrableOn (fun z : ℝ × α => weightedCancellation a r r s (z.1, f z.2))
      (Ioo 0 ε ×ˢ K) (volume.prod μ)) : 2 * r * s < a := by
  rw [IntegrableOn, ← Measure.prod_restrict] at hi
  let : NeZero (μ.restrict K) := ⟨by intro h; exact hK0 (Measure.restrict_eq_zero.mp h)⟩
  obtain ⟨y, hy⟩ := hi.prod_left_ae.exists
  let C := f y ^ 2 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hpow : IntegrableOn (fun x : ℝ => C ^ (-s) * x ^ (a - 1 - 2 * r * s))
      (Ioo 0 ε) volume := by
    apply hy.mono_nonneg (by fun_prop) _ _
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact mul_nonneg (Real.rpow_nonneg hC.le _) (Real.rpow_nonneg hx.1.le _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [weightedCancellation_factor a r r s x (f y) hx.1, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.1.le _)
      apply Real.rpow_le_rpow_of_nonpos
        (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hx.1 _)) _ (neg_nonpos.mpr hs)
      dsimp [C]
      linarith [pow_le_one₀ (n := 2 * r) hx.1.le (hx.2.le.trans hε1)]
  have hint := (integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (Real.rpow_pos_of_pos hC (-s)).ne') _).mp hpow
  have hp := (intervalIntegral.integrableOn_Ioo_rpow_iff hε).mp hint
  linarith

/-- With at least two angular coordinates, odd Fermat cancellation has a point
strictly inside the unit cube. It is not a boundary-only witness. -/
theorem odd_angularFermat_interior_zero (r n : ℕ) (hr : 0 < r) (hodd : Odd r) (hn : 2 ≤ n) :
    ∃ y : Fin n → ℝ, y ∈ ball 0 1 ∧ angularFermat r 1 y = 0 := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_trans zero_lt_one hn'
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  let b : ℝ := ((n : ℝ)⁻¹) ^ ((r : ℝ)⁻¹)
  have hb : 0 < b := Real.rpow_pos_of_pos (inv_pos.mpr hn0) _
  have hb1 : b < 1 := Real.rpow_lt_one (inv_nonneg.mpr hn0.le)
    ((inv_lt_one₀ hn0).mpr hn') (inv_pos.mpr hr')
  have hbr : b ^ r = (n : ℝ)⁻¹ := Real.rpow_inv_natCast_pow (inv_nonneg.mpr hn0.le) hr.ne'
  refine ⟨fun _ => -b, ?_, ?_⟩
  · rw [mem_ball_zero_iff, pi_norm_lt_iff zero_lt_one]
    intro i
    simpa [Real.norm_eq_abs, abs_of_pos hb] using hb1
  · simp only [angularFermat, weightPowerSum, hodd.neg_pow, hbr, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    norm_num

end ResidualSLT
