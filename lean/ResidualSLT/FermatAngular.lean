module
public import ResidualSLT.TransverseChart
public import ResidualSLT.CancellationGeometry
public import ResidualSLT.WeightedCancellation

/-! Transverse charts on affine angular patches of the Fermat cone.
The angular polynomial c+Σyᵢ^r arises by fixing a nonzero homogeneous coordinate.
These charts are local, and the finite cover is derived from compactness. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Metric

@[expose] def angularFermat (r : ℕ) (c : ℝ) {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  c + weightPowerSum r y

theorem angularFermat_contDiff (r n : ℕ) (c : ℝ) :
    ContDiff ℝ 1 (@angularFermat r c n) := by
  unfold angularFermat weightPowerSum
  fun_prop

theorem angularFermat_hasFDerivAt (r n : ℕ) (c : ℝ) (y : Fin n → ℝ) :
    HasFDerivAt (angularFermat r c) (fermatDifferential r y) y :=
  (weightPowerSum_hasFDerivAt r n y).const_add c

/-- The nonzero fixed coordinate guarantees regularity of every angular zero. -/
theorem angularFermat_zero_regular (r n : ℕ) (hr : 0 < r) (c : ℝ) (hc : c ≠ 0)
    (y : Fin n → ℝ) (hy : angularFermat r c y = 0) :
    ∃ j : Fin n, fderiv ℝ (angularFermat r c) y (Pi.single j 1) ≠ 0 := by
  have hne : y ≠ 0 := by
    intro hz
    simp [angularFermat, weightPowerSum, hz, hr.ne'] at hy
    exact hc hy
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra! hn
    exact hne (funext hn)
  refine ⟨j, ?_⟩
  rw [(angularFermat_hasFDerivAt r n c y).fderiv]
  simpa [fermatDifferential_apply, Pi.single_apply, mul_ite] using
    mul_ne_zero (Nat.cast_ne_zero.mpr hr.ne') (pow_ne_zero (r - 1) hj)

/-- Actual local angular coordinates, smooth inverses, and derived Jacobian bounds. -/
theorem angularFermat_exists_chart (r n : ℕ) (hr : 0 < r) (c : ℝ) (hc : c ≠ 0)
    (y : Fin n → ℝ) (hy : angularFermat r c y = 0) :
    ∃ chart : TransverseChart (@angularFermat r c n),
      y ∈ chart.chart.source ∧ chart.chart y chart.index = 0 := by
  obtain ⟨j, hj⟩ := angularFermat_zero_regular r n hr c hc y hy
  obtain ⟨chart, hchart⟩ := exists_mem_transverseChart (angularFermat_contDiff r n c) y j hj
  refine ⟨chart, hchart, ?_⟩
  rw [chart.coe_eq]
  simpa [transverseMap] using hy

/-- A finite collection covers all cancellation points in a closed angular ball. -/
theorem angularFermat_finite_cover (r n : ℕ) (hr : 0 < r) (c : ℝ) (hc : c ≠ 0) (R : ℝ) :
    ∃ charts : Finset (TransverseChart (@angularFermat r c n)),
      (closedBall 0 R ∩ (angularFermat r c) ⁻¹' {0}) ⊆ ⋃ chart ∈ charts, chart.chart.source := by
  apply finite_transverse_chart_cover (angularFermat_contDiff r n c)
  · exact (isCompact_closedBall (0 : Fin n → ℝ) R).inter_right
      (isClosed_singleton.preimage (angularFermat_contDiff r n c).continuous)
  · intro y hy
    exact angularFermat_zero_regular r n hr c hc y hy.2

/-- The finite chart union and its complement account for the whole compact angular domain. -/
theorem angularFermat_finite_cover_and_complement (r n : ℕ) (hr : 0 < r)
    (c : ℝ) (hc : c ≠ 0) (R : ℝ) :
    ∃ charts : Finset (TransverseChart (@angularFermat r c n)),
      (closedBall 0 R ∩ (angularFermat r c) ⁻¹' {0}) ⊆ (⋃ chart ∈ charts, chart.chart.source) ∧
      ∃ b : ℝ, 0 < b ∧ ∀ y ∈ closedBall (0 : Fin n → ℝ) R \
        (⋃ chart ∈ charts, chart.chart.source), b ≤ |angularFermat r c y| := by
  obtain ⟨charts, hcharts⟩ := angularFermat_finite_cover r n hr c hc R
  refine ⟨charts, hcharts, ?_⟩
  apply compact_complement_abs_lower (angularFermat_contDiff r n c).continuous
    (isCompact_closedBall (0 : Fin n → ℝ) R)
    (isOpen_iUnion fun _ => isOpen_iUnion fun _ => OpenPartialHomeomorph.open_source _)
  intro y hy hzero
  exact hcharts ⟨hy, hzero⟩

/-- Homogeneous affine angular coordinates are exactly c=1 Fermat polynomials. -/
theorem weightPowerSum_fixed_coordinate (r n : ℕ) (j : Fin (n + 1)) (z : Fin (n + 1) → ℝ) :
    weightPowerSum r (Function.update z j 1) =
      angularFermat r 1 (fun i : Fin n => z (j.succAbove i)) := by
  unfold weightPowerSum angularFermat
  rw [Fin.sum_univ_succAbove _ j]
  simp only [Function.update_self, one_pow, Function.update_of_ne (Fin.succAbove_ne j _)]
  rfl

/-- Transverse straightening of the weighted integrand on the actual chart image.
The image is retained explicitly; it is not replaced by a rectangle. -/
theorem weightedAngular_chart_iff {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) (c : TransverseChart f) {R : Set ℝ} (hR : MeasurableSet R)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D) (hsub : D ⊆ c.chart.source)
    (a : ℝ) (r : ℕ) (s : ℝ) :
    IntegrableOn (fun z : ℝ × (Fin n → ℝ) => weightedCancellation a r r s (z.1, f z.2))
      (R ×ˢ D) volume ↔
    IntegrableOn (fun z : ℝ × (Fin n → ℝ) => weightedCancellation a r r s (z.1, z.2 c.index))
      (R ×ˢ (c.chart '' D)) volume := by
  have hi := c.radial_integrableOn_image_iff hf hR hD hsub
    (fun z => weightedCancellation a r r s (z.1, z.2 c.index))
  simpa only [c.coe_eq, transverseMap, ite_true] using hi.symm

/-- Off the cancellation set, the ordinary radial condition proves convergence.
Only a finite angular measure and a positive lower bound for |f| are needed. -/
theorem weightedAngular_integrable_off_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] {K : Set α} (hK : MeasurableSet K) (hfinite : μ K ≠ ⊤)
    {f : α → ℝ} (hf : Measurable f) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ y ∈ K, c ≤ |f y|) (a : ℝ) (r : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hthreshold : 2 * r * s < a) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun z : ℝ × α => weightedCancellation a r r s (z.1, f z.2))
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
    rw [weightedCancellation_factor a r r s z.1 (f z.2) hz.1.1]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hz.1.1.le _)
    have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
    have hcf : c ^ 2 ≤ (f z.2) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ hc.le (hbound z.2 hz.2) 2
    have hx : 0 < z.1 := hz.1.1
    exact Real.rpow_le_rpow_of_nonpos hc2 (hcf.trans (le_add_of_nonneg_right (by positivity)))
      (neg_nonpos.mpr hs)

end ResidualSLT
