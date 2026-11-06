module
import ResidualSLT

noncomputable section
namespace ResidualSLT.Examples
open Set MeasureTheory Metric

/-- Independent correction degree and a non-Fermat zero set in the n>d regime. -/
theorem linear_sextic_laplace (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasPowerLaplaceOrder (2/3) (fun N => ∫ w : Fin 2 → ℝ in ball 0 ε,
      Real.exp (-N*(w 0^2+‖w‖^6))) := by
  have hreg : ∀ w : Fin 2 → ℝ, ‖w‖ = 1 → w 0 = 0 →
      fderiv ℝ (fun x : Fin 2 → ℝ => x 0) w ≠ 0 := by
    intro w _ _ he
    rw [(hasFDerivAt_apply (𝕜 := ℝ) 0 w).fderiv] at he
    have hv := congrArg (fun A : (Fin 2 → ℝ) →L[ℝ] ℝ => A (Pi.single 0 1)) he
    simp at hv
  have hz : ∃ w : Fin 2 → ℝ, ‖w‖ = 1 ∧ w 0 = 0 := by
    refine ⟨Pi.single 1 1, ?_, by norm_num⟩
    simp [Pi.norm_single]
  have h := homogeneous_offcritical_spherical_laplace_order 2 1 3 (by omega) (by omega)
    (by omega) (fun w : Fin 2 → ℝ => w 0) (by fun_prop)
    (by intro t w; simp) hreg hz ε hε hε1
  norm_num [homogeneousConeLoss] at h ⊢
  exact h

/-- Arbitrary odd Fermat degree away from the critical dimension, from the general
theorem. This also tests the enlarged-patch lower witness at boundary zeros. -/
theorem odd_offcritical_fermat_via_general (n r : ℕ) (hr : 3 ≤ r) (hodd : Odd r)
    (hne : n+2 ≠ r) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasPowerLaplaceOrder (coneLaplaceExponent (n+2) r r)
      (fun N => ∫ w : Fin (n+2) → ℝ in ball 0 ε,
        Real.exp (-N*(weightPowerSum r w^2+‖w‖^(4*r)))) := by
  have hf : ContDiff ℝ 1 (@weightPowerSum r (n+2)) := by unfold weightPowerSum; fun_prop
  have hreg : ∀ w : Fin (n+2) → ℝ, w ≠ 0 → weightPowerSum r w = 0 →
      fderiv ℝ (weightPowerSum r) w ≠ 0 := by
    intro w hw _
    rw [(weightPowerSum_hasFDerivAt r (n+2) w).fderiv]
    exact fermatDifferential_ne_zero r (n+2) (by omega) w hw
  obtain ⟨w,hw,hnorm⟩ := odd_fermat_sphere_nonempty r (n+2) hodd (by omega)
  have hz : ∃ w : Fin (n+2) → ℝ, w ≠ 0 ∧ weightPowerSum r w = 0 := by
    refine ⟨w,?_,hw⟩
    intro he
    simp [he,weightPowerSum] at hnorm
  have h := homogeneous_offcritical_laplace_order n r r (by omega) (by omega) hne
    (weightPowerSum r) hf (weightPowerSum_smul r (n+2)) hreg hz ε hε hε1
  simpa only [homogeneousConeLoss,show 2*(r+r) = 4*r by omega] using h

theorem cubic_dimension_two_laplace (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasPowerLaplaceOrder (1/3) (fun N => ∫ w : Fin 2 → ℝ in ball 0 ε,
      Real.exp (-N*(weightPowerSum 3 w^2+‖w‖^12))) := by
  have h := odd_offcritical_fermat_via_general 0 3 (by omega) (by decide) (by omega) ε hε hε1
  norm_num [coneLaplaceExponent] at h ⊢
  exact h

theorem cubic_dimension_four_laplace (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasPowerLaplaceOrder (7/12) (fun N => ∫ w : Fin 4 → ℝ in ball 0 ε,
      Real.exp (-N*(weightPowerSum 3 w^2+‖w‖^12))) := by
  have h := odd_offcritical_fermat_via_general 2 3 (by omega) (by decide) (by omega) ε hε hε1
  norm_num [coneLaplaceExponent] at h ⊢
  exact h

/-- Non-unit cutoffs and q>d; upper and lower rates agree below the transition. -/
theorem weighted_subcritical_laplace :
    HasPowerLaplaceOrder (1/3) (powerWeightedSymmetric 2 3 5 (1/2) (1/3)) := by
  have h := powerWeightedSymmetric_has_order 2 3 5 (by omega) (by omega) (by omega)
    (by omega) (1/2) (1/3) (by norm_num) (by norm_num)
  norm_num [coneLaplaceExponent] at h ⊢
  exact h

/-- Non-unit cutoffs and q<d; upper and lower rates agree above the transition. -/
theorem weighted_supercritical_laplace :
    HasPowerLaplaceOrder (3/4) (powerWeightedSymmetric 5 3 1 (1/2) (1/3)) := by
  have h := powerWeightedSymmetric_has_order 5 3 1 (by omega) (by omega) (by omega)
    (by omega) (1/2) (1/3) (by norm_num) (by norm_num)
  norm_num [coneLaplaceExponent] at h ⊢
  exact h

end ResidualSLT.Examples

#print axioms ResidualSLT.Examples.linear_sextic_laplace
#print axioms ResidualSLT.Examples.odd_offcritical_fermat_via_general
#print axioms ResidualSLT.Examples.cubic_dimension_two_laplace
#print axioms ResidualSLT.Examples.cubic_dimension_four_laplace
#print axioms ResidualSLT.Examples.weighted_subcritical_laplace
#print axioms ResidualSLT.Examples.weighted_supercritical_laplace
