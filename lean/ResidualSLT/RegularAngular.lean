module
public import ResidualSLT.AngularIntegration

/-! Regular angular cancellation with independent radial degrees.
The proofs retain actual chart images and derive both product-region inclusions.
No homogeneity or Fermat form is required of the angular function. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Metric

/-- Transverse straightening of the weighted integrand on the actual chart image.
The image is retained explicitly; it is not replaced by a rectangle. -/
theorem weightedAngular_chart_iff_general {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) (c : TransverseChart f) {R : Set ℝ} (hR : MeasurableSet R)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D) (hsub : D ⊆ c.chart.source)
    (a : ℝ) (r q : ℕ) (s : ℝ) :
    IntegrableOn (fun z : ℝ × (Fin n → ℝ) => weightedCancellation a r q s (z.1, f z.2))
      (R ×ˢ D) volume ↔
    IntegrableOn (fun z : ℝ × (Fin n → ℝ) => weightedCancellation a r q s (z.1, z.2 c.index))
      (R ×ˢ (c.chart '' D)) volume := by
  have hi := c.radial_integrableOn_image_iff hf hR hD hsub
    (fun z => weightedCancellation a r q s (z.1, z.2 c.index))
  simpa only [c.coe_eq, transverseMap, ite_true] using hi.symm

/-- Off the cancellation set, the ordinary radial condition proves convergence.
Only a finite angular measure and a positive lower bound for |f| are needed. -/
theorem weightedAngular_integrable_off_zero_general {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] {K : Set α} (hK : MeasurableSet K) (hfinite : μ K ≠ ⊤)
    {f : α → ℝ} (hf : Measurable f) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ y ∈ K, c ≤ |f y|) (a : ℝ) (r q : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hthreshold : 2 * r * s < a) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun z : ℝ × α => weightedCancellation a r q s (z.1, f z.2))
      (Ioo 0 ε ×ˢ K) (volume.prod μ) := by
  have hrad : IntegrableOn (fun x : ℝ => x ^ (a - 1 - 2 * r * s)) (Ioo 0 ε) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hε).mpr (by linarith)
  have hang : IntegrableOn (fun _ : α => (c ^ 2) ^ (-s)) K μ := integrableOn_const hfinite
  have hprod := hrad.mul_prod hang
  rw [Measure.prod_restrict] at hprod
  apply hprod.mono_nonneg (by unfold weightedCancellation; fun_prop) _ _
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod hK)] with z hz
    have hx : 0 < z.1 := hz.1.1
    unfold weightedCancellation
    positivity
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod hK)] with z hz
    rw [weightedCancellation_factor a r q s z.1 (f z.2) hz.1.1]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hz.1.1.le _)
    have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
    have hcf : c ^ 2 ≤ (f z.2) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ hc.le (hbound z.2 hz.2) 2
    have hx : 0 < z.1 := hz.1.1
    exact Real.rpow_le_rpow_of_nonpos hc2 (hcf.trans (le_add_of_nonneg_right (by positivity)))
      (neg_nonpos.mpr hs)

/-- Convergence on the entire compact angular cube follows from finite charts,
proved outer cylinder containment, and the complementary noncancellation region. -/
theorem weightedAngular_integrable_regular (r q n : ℕ) (hr : 0 < r) (hq : 0 < q)
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (R : ℝ) (hR : 0 < R)
    (hreg : ∀ y ∈ closedBall 0 R, f y = 0 →
      ∃ j, fderiv ℝ f y (Pi.single j 1) ≠ 0)
    (a : ℝ) (ha : 0 < a) (s : ℝ) (hs : 0 ≤ s)
    (hcrit : s < min (a / (2 * r)) ((a + q) / (2 * ((r : ℝ) + q)))) :
    IntegrableOn (fun z : ℝ × (Fin (n + 1) → ℝ) =>
      weightedCancellation a r q s (z.1, f z.2))
      (Ioo 0 1 ×ˢ closedBall 0 R) volume := by
  classical
  let K := closedBall (0 : Fin (n + 1) → ℝ) R
  obtain ⟨charts, hcover⟩ := finite_transverse_chart_cover hf
    ((isCompact_closedBall (0 : Fin (n + 1) → ℝ) R).inter_right
      (isClosed_singleton.preimage hf.continuous))
    (fun y hy => hreg y hy.1 hy.2)
  let Uc := fun c : TransverseChart f => c.chart.source ∩ f ⁻¹' Ioo (-1) 1
  let U := ⋃ c ∈ charts, Uc c
  have hUc (c : TransverseChart f) : IsOpen (Uc c) :=
    c.chart.open_source.inter (hf.continuous.isOpen_preimage _ isOpen_Ioo)
  have hU : IsOpen U := isOpen_iUnion fun c => isOpen_iUnion fun _ => hUc c
  have hzU : ∀ y ∈ K, f y = 0 → y ∈ U := by
    intro y hy hz
    obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.mp (hcover ⟨hy, hz⟩)
    exact mem_iUnion₂.mpr ⟨c, hc, hyc, by change f y ∈ Ioo (-1) 1; rw [hz]; norm_num⟩
  obtain ⟨b, hb, hbK⟩ := compact_complement_abs_lower
    hf.continuous (isCompact_closedBall 0 R) hU hzU
  have hoff : IntegrableOn (fun z : ℝ × (Fin (n + 1) → ℝ) =>
      weightedCancellation a r q s (z.1, f z.2)) (Ioo 0 1 ×ˢ (K \ U)) volume := by
    rw [Measure.volume_eq_prod]
    apply weightedAngular_integrable_off_zero_general volume (measurableSet_closedBall.diff hU.measurableSet)
      (ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono sdiff_subset))
      hf.continuous.measurable hb hbK a r q s hs _ 1 zero_lt_one
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * (r : ℝ))).mp (lt_min_iff.mp hcrit).1
    nlinarith
  have hpatch (c : TransverseChart f) : IntegrableOn
      (fun z : ℝ × (Fin (n + 1) → ℝ) => weightedCancellation a r q s (z.1, f z.2))
      (Ioo 0 1 ×ˢ (K ∩ Uc c)) volume := by
    have houter : c.chart '' (K ∩ Uc c) ⊆
        angularCylinder c.index (Ioo (-1) 1) (ball (0 : Fin n → ℝ) (R + 1)) := by
      apply c.image_subset_cylinder
      · intro y hy; exact hy.2.2
      · intro y hy
        apply mem_ball_zero_iff.mpr
        apply lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg hR.le).mpr ?_) (by linarith : R < R + 1)
        intro i
        exact (norm_le_pi_norm y _).trans (mem_closedBall_zero_iff.mp hy.1)
    have hi := (angularCylinder_integrable_iff c.index (Ioo 0 1) (Ioo (-1) 1)
      (ball (0 : Fin n → ℝ) (R + 1)) measure_ball_lt_top.ne
      (measure_ball_pos volume 0 (by linarith : 0 < R + 1)).ne' (weightedCancellation a r q s)).mpr
        ((weightedCancellation_symmetric_integrableOn_iff a ha r q hr hq s).mpr hcrit)
    exact (weightedAngular_chart_iff_general hf c
      measurableSet_Ioo (measurableSet_closedBall.inter (hUc c).measurableSet)
      (fun _ h => h.2.1) a r q s).mpr (hi.mono_set (prod_mono Subset.rfl houter))
  have hall := hoff.union ((integrableOn_finset_iUnion (s := charts)).mpr (fun c _ => hpatch c))
  apply hall.mono_set
  intro z hz
  by_cases hu : z.2 ∈ U
  · obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp hu
    exact Or.inr (mem_iUnion₂.mpr ⟨c, hc, hz.1, hz.2, hzc⟩)
  · exact Or.inl ⟨hz.1, hz.2, hu⟩

/-- An interior angular cancellation point supplies a product region of positive
unused-coordinate measure, hence both strict inequalities including endpoint failure. -/
theorem weightedAngular_regular_necessary (r q n : ℕ) (hr : 0 < r) (hq : 0 < q)
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (R : ℝ)
    (a : ℝ) (ha : 0 < a) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ)
    (y : Fin (n + 1) → ℝ) (hy : y ∈ ball 0 R) (hz : f y = 0)
    (hreg : ∃ j, fderiv ℝ f y (Pi.single j 1) ≠ 0)
    (hi : IntegrableOn (fun z : ℝ × (Fin (n + 1) → ℝ) =>
      weightedCancellation a r q s (z.1, f z.2))
      (Ioo 0 ε ×ˢ closedBall 0 R) volume) :
    s < min (a / (2 * r)) ((a + q) / (2 * ((r : ℝ) + q))) := by
  obtain ⟨j, hj⟩ := hreg
  obtain ⟨c, hyc⟩ := exists_mem_transverseChart hf y j hj
  let D := ball (0 : Fin (n + 1) → ℝ) R ∩ c.chart.source
  have hD : IsOpen D := isOpen_ball.inter c.chart.open_source
  obtain ⟨δ, hδ, hδ1, hinner⟩ := c.exists_inner_cylinder hD inter_subset_right ⟨hy, hyc⟩ hz
  have hlocal := (weightedAngular_chart_iff_general hf c
    measurableSet_Ioo hD.measurableSet inter_subset_right a r q s).mp
      (hi.mono_set (prod_mono Subset.rfl (fun _ h => ball_subset_closedBall h.1)))
  have hrect := (angularCylinder_integrable_iff c.index (Ioo 0 ε) (Ioo (-δ) δ)
    (ball (fun i => y (c.index.succAbove i)) δ) measure_ball_lt_top.ne
    (measure_ball_pos volume _ hδ).ne' (weightedCancellation a r q s)).mp
      (hlocal.mono_set (prod_mono Subset.rfl hinner))
  exact (weightedCancellation_local_integrableOn_iff a ha r q hr hq ε δ hε hε1 hδ hδ1 s).mp hrect



/-- Bounded angular functions give convergence for every nonpositive singular exponent.
Only the radial density needs integration near zero. -/
theorem weightedAngular_integrable_nonpos_general {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) (R : ℝ)
    (a : ℝ) (ha : 0 < a) (r q : ℕ) (s : ℝ) (hs : s ≤ 0) :
    IntegrableOn (fun z : ℝ × (Fin n → ℝ) =>
      weightedCancellation a r q s (z.1, f z.2))
      (Ioo 0 1 ×ˢ closedBall 0 R) volume := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin n → ℝ) R).exists_bound_of_continuousOn
    hf.continuousOn
  have hrad : IntegrableOn (fun x : ℝ => x ^ (a - 1)) (Ioo 0 1) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)
  have hang : IntegrableOn (fun _ : Fin n → ℝ => (C ^ 2 + 1) ^ (-s))
      (closedBall 0 R) volume := integrableOn_const measure_closedBall_lt_top.ne
  have hi := hrad.mul_prod hang
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hi
  have hfm := hf.measurable
  apply hi.mono_nonneg (by unfold weightedCancellation; fun_prop) _ _
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_closedBall)] with z hz
    have hx : 0 < z.1 := hz.1.1
    unfold weightedCancellation
    exact mul_nonneg (Real.rpow_nonneg hz.1.1.le _) (Real.rpow_nonneg (by positivity) _)
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_closedBall)] with z hz
    have hx : 0 < z.1 := hz.1.1
    have hfC : (f z.2) ^ 2 ≤ C ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using
        pow_le_pow_left₀ (norm_nonneg (f z.2)) (hC z.2 hz.2) 2
    have hsum : 0 ≤ (f z.2) ^ 2 + z.1 ^ (2 * q) := by positivity
    have hb : z.1 ^ (2 * r) * ((f z.2) ^ 2 + z.1 ^ (2 * q)) ≤ C ^ 2 + 1 := by
      calc
        _ ≤ 1 * ((f z.2) ^ 2 + z.1 ^ (2 * q)) :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hz.1.1.le hz.1.2.le) hsum
        _ ≤ C ^ 2 + 1 := by
          have := pow_le_one₀ (n := 2 * q) hz.1.1.le hz.1.2.le
          linarith
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hb (neg_nonneg.mpr hs))
      (Real.rpow_nonneg hz.1.1.le _)

/-- Exact threshold on a compact angular cube for any C¹ function with regular zeros
and one interior zero. The conclusion covers all real exponents, including the boundary. -/
theorem weightedAngular_regular_integrableOn_iff (r q n : ℕ) (hr : 0 < r) (hq : 0 < q)
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (R : ℝ) (hR : 0 < R)
    (hreg : ∀ y ∈ closedBall 0 R, f y = 0 →
      ∃ j, fderiv ℝ f y (Pi.single j 1) ≠ 0)
    (hzero : ∃ y ∈ ball 0 R, f y = 0)
    (a : ℝ) (ha : 0 < a) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ) :
    IntegrableOn (fun z : ℝ × (Fin (n + 1) → ℝ) =>
      weightedCancellation a r q s (z.1, f z.2))
      (Ioo 0 ε ×ˢ closedBall 0 R) volume ↔
      s < min (a / (2 * r)) ((a + q) / (2 * ((r : ℝ) + q))) := by
  constructor
  · intro hi
    obtain ⟨y, hy, hz⟩ := hzero
    exact weightedAngular_regular_necessary r q n hr hq f hf R a ha ε hε hε1 s y hy hz
      (hreg y (ball_subset_closedBall hy) hz) hi
  · intro hs
    have hsub : Ioo (0 : ℝ) ε ×ˢ closedBall (0 : Fin (n + 1) → ℝ) R ⊆
        Ioo 0 1 ×ˢ closedBall 0 R := prod_mono (Ioo_subset_Ioo le_rfl hε1) Subset.rfl
    by_cases hs0 : 0 ≤ s
    · exact (weightedAngular_integrable_regular r q n hr hq f hf R hR hreg a ha s hs0 hs).mono_set hsub
    · exact (weightedAngular_integrable_nonpos_general f hf.continuous R a ha r q s
        (le_of_not_ge hs0)).mono_set hsub

end ResidualSLT
