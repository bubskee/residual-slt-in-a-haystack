module
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Tactic

/-! Scalar residual networks, with effective coefficients `u i` in any commutative ring.
The chronological block indices are `0, ..., L-1`. Raw weights are substituted by `u i = w i ^ r`.
-/
public section
noncomputable section
namespace ResidualSLT
open Polynomial
variable {R : Type*} [CommRing R]

/-- Actual output polynomial, including the identity skip. -/
@[expose] def network (r : ℕ) (u : ℕ → R) : ℕ → R[X]
  | 0 => X
  | n + 1 => network r u n + C (u n) * network r u n ^ r

/-- Graded output: `network = X * graded.comp (X^(r-1))` for `r ≥ 1`. -/
@[expose] def graded (r : ℕ) (u : ℕ → R) : ℕ → R[X]
  | 0 => 1
  | n + 1 => graded r u n + C (u n) * X * graded r u n ^ r

@[simp] theorem graded_coeff_zero (r : ℕ) (u : ℕ → R) (n : ℕ) :
    (graded r u n).coeff 0 = 1 := by
  induction n with
  | zero => simp [graded]
  | succ n ih => simp [graded, ih]

/-- Exact grading identity; no analytic coordinate change is involved. -/
theorem network_eq_graded (r : ℕ) (hr : 1 ≤ r) (u : ℕ → R) (n : ℕ) :
    network r u n = X * (graded r u n).comp (X ^ (r - 1)) := by
  induction n with
  | zero => simp [network, graded]
  | succ n ih =>
    simp only [network, graded, add_comp, mul_comp, C_comp, X_comp, pow_comp, ih,
      mul_pow]
    have hx : (X : R[X]) ^ r = X * X ^ (r - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hx]
    ring

@[simp] theorem network_zero_weights (r n : ℕ) :
    network r (fun _ => (0 : R)) n = X := by
  induction n with
  | zero => rfl
  | succ n ih => simp [network, ih]

/-- A zero effective coefficient deletes the last block. -/
theorem network_succ_of_zero (r n : ℕ) (u : ℕ → R) (h : u n = 0) :
    network r u (n + 1) = network r u n := by
  simp [network, h]

/-- The polynomial recursion evaluates to the scalar residual recursion. -/
theorem eval_network_succ (r n : ℕ) (u : ℕ → R) (x : R) :
    (network r u (n + 1)).eval x =
      (network r u n).eval x + u n * ((network r u n).eval x) ^ r := by
  simp [network]
end ResidualSLT
