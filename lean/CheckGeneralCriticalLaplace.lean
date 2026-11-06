module
import ResidualSLT

noncomputable section
namespace ResidualSLT.Examples
open Set MeasureTheory Metric

/-- A non-Fermat even-degree example: its angular zeros are on the boundaries of
both unit pivot patches. Also k=3 is strictly less than the old k=2d=4 case. -/
theorem quadratic_saddle_sextic_laplace (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasCriticalLaplaceOrder (fun N => ∫ w : Fin 2 → ℝ in ball 0 ε,
      Real.exp (-N*((w 0^2-w 1^2)^2+‖w‖^6))) := by
  let f : (Fin 2 → ℝ) → ℝ := fun w => w 0^2-w 1^2
  have hreg : ∀ w : Fin 2 → ℝ, ‖w‖ = 1 → f w = 0 → fderiv ℝ f w ≠ 0 := by
    intro w hw _ he
    have hd := ((hasFDerivAt_apply (𝕜 := ℝ) 0 w).pow 2).sub
      ((hasFDerivAt_apply (𝕜 := ℝ) 1 w).pow 2)
    change HasFDerivAt f _ w at hd
    rw [hd.fderiv] at he
    have h0 := congrArg (fun A : (Fin 2 → ℝ) →L[ℝ] ℝ => A (Pi.single 0 1)) he
    have h1 := congrArg (fun A : (Fin 2 → ℝ) →L[ℝ] ℝ => A (Pi.single 1 1)) he
    norm_num at h0 h1
    have hz : w = 0 := by
      ext i
      fin_cases i <;> simp_all
    simp [hz] at hw
  have hz : ∃ w : Fin 2 → ℝ, ‖w‖ = 1 ∧ f w = 0 := by
    refine ⟨1,?_,by norm_num [f]⟩
    exact norm_one
  have h := homogeneous_critical_spherical_laplace_order 2 3 (by omega) f (by dsimp [f]; fun_prop)
    (by intro t w; simp only [f,Pi.smul_apply,smul_eq_mul,mul_pow]; ring) hreg hz ε hε hε1
  simpa only [homogeneousConeLoss,f] using h

/-- A correction degree on the other side, q>d, with non-unit cutoffs. -/
theorem cubic_large_correction_laplace :
    HasCriticalLaplaceOrder (generalWeightedSymmetric 3 5 (1/2) (1/3)) :=
  generalWeightedSymmetric_has_order 3 5 (by omega) (by omega) (1/2) (1/3) (by norm_num) (by norm_num)

/-- The former weighted critical model is a literal specialization q=d. -/
theorem original_weighted_model_via_general (r : ℕ) (hr : 0 < r)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    HasCriticalLaplaceOrder (weightedLaplaceSymmetric r ε δ) :=
  generalWeightedSymmetric_has_order r r hr hr ε δ hε hδ

/-- The previous arbitrary odd critical Fermat model follows from the new theorem,
without invoking its specialized Laplace certificate. -/
theorem odd_critical_fermat_via_general (r : ℕ) (hr : 3 ≤ r) (hodd : Odd r)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasCriticalLaplaceOrder (fun N => ∫ w : Fin r → ℝ in ball 0 ε,
      Real.exp (-N*(weightPowerSum r w^2+‖w‖^(4*r)))) := by
  have hf : ContDiff ℝ 1 (@weightPowerSum r r) := by unfold weightPowerSum; fun_prop
  have hreg : ∀ w : Fin r → ℝ, w ≠ 0 → weightPowerSum r w = 0 →
      fderiv ℝ (weightPowerSum r) w ≠ 0 := by
    intro w hw _
    rw [(weightPowerSum_hasFDerivAt r r w).fderiv]
    exact fermatDifferential_ne_zero r r (by omega) w hw
  obtain ⟨w,hw,hnorm⟩ := odd_fermat_sphere_nonempty r r hodd (by omega)
  have hz : ∃ w : Fin r → ℝ, w ≠ 0 ∧ weightPowerSum r w = 0 := by
    refine ⟨w,?_,hw⟩
    intro he
    simp [he,weightPowerSum] at hnorm
  obtain ⟨n,rfl⟩ : ∃ n, r = n+2 := ⟨r-2,by omega⟩
  have h := homogeneous_critical_laplace_order n (n+2) (by omega) (weightPowerSum (n+2)) hf
    (weightPowerSum_smul (n+2) (n+2)) hreg hz ε hε hε1
  simpa only [homogeneousConeLoss,show 2*(n+2+(n+2)) = 4*(n+2) by omega] using h

end ResidualSLT.Examples
#print axioms ResidualSLT.Examples.quadratic_saddle_sextic_laplace
#print axioms ResidualSLT.Examples.cubic_large_correction_laplace
#print axioms ResidualSLT.Examples.original_weighted_model_via_general

#print axioms ResidualSLT.Examples.odd_critical_fermat_via_general
