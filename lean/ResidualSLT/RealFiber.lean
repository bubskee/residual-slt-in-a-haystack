module
public import ResidualSLT.Coefficients
public import ResidualSLT.Degree
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Over the reals, the first two residual coefficients already detect the full identity fiber.
This is an algebraic certificate; no input distribution or loss has been defined here. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset

/-- Two coefficients suffice over `ℝ`; the analogous statement over `ℂ` is not asserted. -/
theorem real_two_coefficients_zero_iff (r : ℕ) (hr : 2 ≤ r) (u : ℕ → ℝ) (n : ℕ) :
    ((network r u n).coeff r = 0 ∧ (network r u n).coeff (2 * r - 1) = 0) ↔
      ∀ i < n, u i = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    have hS : ∑ i ∈ range n, u i = 0 := by rwa [network_coeff_r r hr] at h1
    have hQ := network_coeff_two_mul_sub_one r hr u n
    rw [h2, hS] at hQ
    have hrpos : 0 < (r : ℝ) := by positivity
    have hz : ∑ i ∈ range n, u i ^ 2 = 0 := by nlinarith
    simpa using ((sum_sq_eq_zero_iff (range n) u).mp hz)
  · intro hu
    rw [(network_eq_X_iff r hr u n).mpr hu]
    simp [coeff_X, show 1 ≠ r by omega, show 1 ≠ 2 * r - 1 by omega]

/-- Raw real weights are recovered from those two vanishing coefficients, for every depth. -/
theorem real_raw_two_coefficients_zero_iff (r : ℕ) (hr : 2 ≤ r) (w : ℕ → ℝ) (n : ℕ) :
    ((network r (fun i => w i ^ r) n).coeff r = 0 ∧
      (network r (fun i => w i ^ r) n).coeff (2 * r - 1) = 0) ↔
      ∀ i < n, w i = 0 := by
  rw [real_two_coefficients_zero_iff r hr]
  simp [pow_eq_zero_iff (by omega : r ≠ 0)]
end ResidualSLT
