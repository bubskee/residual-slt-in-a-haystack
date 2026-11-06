module
import ResidualSLT

noncomputable section
namespace ResidualSLT.Examples
open Set MeasureTheory Metric

/-- Unequal degrees, no Fermat polynomial: x₀²+‖x‖⁶ in dimension two. -/
theorem linear_sextic_threshold (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ) :
    IntegrableOn (fun w : Fin 2 → ℝ => (w 0 ^ 2 + ‖w‖ ^ 6) ^ (-s))
      (ball 0 ε) volume ↔ s < 2 / 3 := by
  have hreg : ∀ w : Fin 2 → ℝ, w ≠ 0 → w 0 = 0 →
      fderiv ℝ (fun x : Fin 2 → ℝ => x 0) w ≠ 0 := by
    intro w _ _ he
    rw [(hasFDerivAt_apply (𝕜 := ℝ) 0 w).fderiv] at he
    have hval := congrArg (fun A : (Fin 2 → ℝ) →L[ℝ] ℝ => A (Pi.single 0 1)) he
    simp at hval
  have hz : ∃ w : Fin 2 → ℝ, w ≠ 0 ∧ w 0 = 0 := by
    refine ⟨Pi.single 1 1, ?_, by norm_num⟩
    intro he
    have := congrFun he 1
    norm_num at this
  have hi := homogeneousConeLoss_integrableOn_iff 0 1 2 (by omega) (by omega)
    (fun w : Fin 2 → ℝ => w 0) (by fun_prop) (by intro t w; simp)
    hreg hz ε hε hε1 s
  norm_num [homogeneousConeLoss] at hi ⊢
  exact hi

/-- Two dimensions require the enlarged interior witness, not a zero in the open unit cube. -/
theorem cubic_depth_two_via_general_cone (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 3 2))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (p : (Fin 2 → ℝ) → NNReal) (hp : BoundedPositivePriorOn p (ball 0 ε) volume) :
    ¬ IntegrableOn (fun w => networkPopulationLoss μ 3 w ^ (-(1 / 3 : ℝ))) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal))) := by
  rw [odd_network_prior_integrableOn_iff_via_homogeneous μ 3 2 (by omega)
    (by decide) (by omega) h ε hε hε1 p hp]
  norm_num

/-- The critical cubic depth-three threshold is recovered without claiming multiplicity. -/
theorem cubic_critical_via_general_cone (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 3 3))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (p : (Fin 3 → ℝ) → NNReal) (hp : BoundedPositivePriorOn p (ball 0 ε) volume) (s : ℝ) :
    IntegrableOn (fun w => networkPopulationLoss μ 3 w ^ (-s)) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal))) ↔ s < 1 / 2 := by
  convert odd_network_prior_integrableOn_iff_via_homogeneous μ 3 3 (by omega)
    (by decide) (by omega) h ε hε hε1 p hp s using 1; norm_num

end ResidualSLT.Examples

#print axioms ResidualSLT.Examples.linear_sextic_threshold
#print axioms ResidualSLT.Examples.cubic_depth_two_via_general_cone
#print axioms ResidualSLT.Examples.cubic_critical_via_general_cone
