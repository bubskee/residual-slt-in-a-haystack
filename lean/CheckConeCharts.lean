module
import ResidualSLT

noncomputable section
namespace ResidualSLT.Examples
open Set MeasureTheory

/-- A cubic angular cancellation point has an actual local chart, not just a nonzero gradient. -/
theorem cubic_angular_chart :
    ∃ c : TransverseChart (@angularFermat 3 1 1),
      (fun _ => (-1 : ℝ)) ∈ c.chart.source ∧ c.chart (fun _ => -1) c.index = 0 := by
  apply angularFermat_exists_chart 3 1 (by decide) 1 (by norm_num)
  norm_num [angularFermat, weightPowerSum]

theorem cubic_transverse_jacobian (y : Fin 2 → ℝ) (j : Fin 2) :
    (transverseDeriv j (fermatDifferential 3 y)).det = 3 * y j ^ 2 := by
  rw [transverseDeriv_det]
  simp [fermatDifferential_apply, Pi.single_apply, mul_ite]

theorem three_dimensional_radial_jacobian (z : Fin 3 → ℝ) :
    (radialBlowupDeriv 0 z).det = z 0 ^ 2 := radialBlowupDeriv_det 0 z

theorem radial_inverse_checked (w : Fin 3 → ℝ) (hw : w 1 ≠ 0) :
    radialBlowup 1 (radialBlowupInverse 1 w) = w := radialBlowup_right_inverse 1 w hw

theorem cubic_angular_finite_cover :
    ∃ charts : Finset (TransverseChart (@angularFermat 3 1 2)),
      (Metric.closedBall 0 1 ∩ (angularFermat 3 1) ⁻¹' {0}) ⊆
        (⋃ c ∈ charts, c.chart.source) ∧
      ∃ b : ℝ, 0 < b ∧ ∀ y ∈ Metric.closedBall (0 : Fin 2 → ℝ) 1 \
        (⋃ c ∈ charts, c.chart.source), b ≤ |angularFermat 3 1 y| :=
  angularFermat_finite_cover_and_complement 3 2 (by decide) 1 (by norm_num) 1

theorem three_dimensional_signed_cover (ε : ℝ) (w : Fin 3 → ℝ)
    (hw : w ∈ Metric.ball 0 ε) (hne : w ≠ 0) :
    ∃ j : Fin 3, ∃ z : Fin 3 → ℝ, 0 < z j ∧ z j < ε ∧
      (∀ i, i ≠ j → |z i| ≤ 1) ∧ (w = radialBlowup j z ∨ w = -radialBlowup j z) :=
  signed_radialBlowup_cover ε w hw hne

/-- Away from angular cancellation, only the usual radial exponent condition is needed. -/
theorem cubic_noncancellation_integrable (s : ℝ) (hs : 0 ≤ s) (hcrit : s < 1 / 2) :
    IntegrableOn (fun z : ℝ × ℝ => weightedCancellation 3 3 3 s (z.1, 1))
      (Ioo 0 1 ×ˢ Icc (-1) 1) (volume.prod volume) := by
  exact weightedAngular_integrable_off_zero volume measurableSet_Icc (by simp)
    measurable_const (c := 1) (by norm_num) (by intro y hy; norm_num)
    3 3 s hs (by norm_num; linarith) 1 zero_lt_one

/-- Actual network/prior to weighted chart integrand; no numerical network threshold claimed. -/
theorem cubic_population_chart_transfer (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 3 3))
    (c : TransverseChart (@angularFermat 3 1 2))
    {D : Set (Fin 2 → ℝ)} (hD : MeasurableSet D)
    (hbound : ∀ y ∈ D, ∀ i, |y i| ≤ 1) (hsub : D ⊆ c.chart.source)
    (ρ : (Fin 3 → ℝ) → NNReal)
    (hρ : BoundedPositivePriorOn ρ (projectiveConePatch 0 (Ioo 0 1) D) volume) (s : ℝ) :
    IntegrableOn (fun w => networkPopulationLoss μ 3 w ^ (-s))
      (projectiveConePatch 0 (Ioo 0 1) D) (volume.withDensity (fun w => (ρ w : ENNReal))) ↔
      IntegrableOn (fun z : ℝ × (Fin 2 → ℝ) => weightedCancellation 3 3 3 s (z.1, z.2 c.index))
        (Ioo 0 1 ×ˢ (c.chart '' D)) volume := by
  convert signed_network_prior_transverse_cone_iff μ 3 (by decide) h 0 c
    measurableSet_Ioo (fun _ h => h.1) (fun _ h => h.2) hD hbound hsub ρ hρ s using 1
  norm_num

#print axioms cubic_angular_chart
#print axioms cubic_transverse_jacobian
#print axioms three_dimensional_radial_jacobian
#print axioms radial_inverse_checked
#print axioms cubic_angular_finite_cover
#print axioms three_dimensional_signed_cover
#print axioms cubic_noncancellation_integrable
#print axioms cubic_population_chart_transfer
end ResidualSLT.Examples
