module
public import ResidualSLT.PolynomialNetworks
public import Mathlib.Algebra.Polynomial.Expand

/-! Universal first two coefficient identities. All identities are division-free,
so they hold over arbitrary commutative rings, including polynomial parameter rings. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset
variable {R : Type*} [CommRing R]

/-- Coefficient of the linear term of a power with constant term one. -/
theorem coeff_one_pow (p : R[X]) (hp : p.coeff 0 = 1) (r : ℕ) :
    (p ^ r).coeff 1 = (r : R) * p.coeff 1 := by
  induction r with
  | zero => simp [coeff_one]
  | succ r ih =>
    rw [pow_succ, mul_coeff_one, ih]
    have h0 : (p ^ r).coeff 0 = 1 := by
      simpa only [constantCoeff_apply, hp, one_pow] using (map_pow constantCoeff p r)
    rw [h0, hp, Nat.cast_add, Nat.cast_one]
    ring

/-- The first graded coefficient is the sum of effective weights. -/
theorem graded_coeff_one (r : ℕ) (u : ℕ → R) (n : ℕ) :
    (graded r u n).coeff 1 = ∑ i ∈ range n, u i := by
  induction n with
  | zero => simp [graded, coeff_one]
  | succ n ih =>
    rw [graded, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul]
    have h0 : (graded r u n ^ r).coeff 0 = 1 := by
      simpa only [constantCoeff_apply, graded_coeff_zero, one_pow] using
        (map_pow constantCoeff (graded r u n) r)
    simp [ih, h0, sum_range_succ]

/-- The second graded coefficient is `r` times the ordered pair sum. -/
theorem graded_coeff_two (r : ℕ) (u : ℕ → R) (n : ℕ) :
    (graded r u n).coeff 2 =
      (r : R) * ∑ j ∈ range n, (∑ i ∈ range j, u i) * u j := by
  induction n with
  | zero => simp [graded, coeff_one]
  | succ n ih =>
    rw [graded, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul,
      coeff_one_pow _ (graded_coeff_zero r u n), graded_coeff_one, ih, sum_range_succ]
    ring

/-- A division-free form of `B = r/2 * (S²-Q)`. -/
theorem graded_coeff_two_SQ (r : ℕ) (u : ℕ → R) (n : ℕ) :
    2 * (graded r u n).coeff 2 =
      (r : R) * ((∑ i ∈ range n, u i) ^ 2 - ∑ i ∈ range n, (u i) ^ 2) := by
  induction n with
  | zero => simp [graded, coeff_one]
  | succ n ih =>
    rw [graded, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul,
      coeff_one_pow _ (graded_coeff_zero r u n), graded_coeff_one]
    simp only [sum_range_succ]
    linear_combination ih

/-- Transfer any graded coefficient to the actual output polynomial. -/
theorem network_coeff_graded (r : ℕ) (hr : 2 ≤ r) (u : ℕ → R) (n k : ℕ) :
    (network r u n).coeff (k * (r - 1) + 1) = (graded r u n).coeff k := by
  rw [network_eq_graded r (by omega), coeff_X_mul,
    ← expand_eq_comp_X_pow, coeff_expand_mul (by omega : 0 < r - 1)]

theorem network_coeff_r (r : ℕ) (hr : 2 ≤ r) (u : ℕ → R) (n : ℕ) :
    (network r u n).coeff r = ∑ i ∈ range n, u i := by
  have h := network_coeff_graded r hr u n 1
  simpa [graded_coeff_one, Nat.sub_add_cancel (by omega : 1 ≤ r)] using h

theorem network_coeff_two_mul_sub_one (r : ℕ) (hr : 2 ≤ r) (u : ℕ → R) (n : ℕ) :
    2 * (network r u n).coeff (2 * r - 1) =
      (r : R) * ((∑ i ∈ range n, u i) ^ 2 - ∑ i ∈ range n, (u i) ^ 2) := by
  have hidx : 2 * r - 1 = 2 * (r - 1) + 1 := by omega
  rw [hidx, network_coeff_graded r hr, graded_coeff_two_SQ]

/-- The exact raw-weight identity used in the loss reduction. -/
theorem raw_coefficients (r : ℕ) (hr : 2 ≤ r) (w : ℕ → R) (n : ℕ) :
    (network r (fun i => w i ^ r) n).coeff r = ∑ i ∈ range n, w i ^ r ∧
    2 * (network r (fun i => w i ^ r) n).coeff (2 * r - 1) =
      (r : R) * ((∑ i ∈ range n, w i ^ r) ^ 2 - ∑ i ∈ range n, w i ^ (2 * r)) := by
  refine ⟨network_coeff_r r hr _ n, ?_⟩
  simpa [pow_mul, mul_comm] using network_coeff_two_mul_sub_one r hr (fun i => w i ^ r) n
/-- The two nontrivial coefficients of the residual polynomial itself, in ordered-pair form.
This uses the existing arbitrary-depth recursion and does not assert an analytic loss bound. -/
theorem raw_residual_coefficients (r : ℕ) (hr : 2 ≤ r) (w : ℕ → R) (n : ℕ) :
    (network r (fun i => w i ^ r) n - X).coeff r = ∑ i ∈ range n, w i ^ r ∧
    (network r (fun i => w i ^ r) n - X).coeff (2 * r - 1) =
      (r : R) * ∑ j ∈ range n, (∑ i ∈ range j, w i ^ r) * w j ^ r := by
  constructor
  · simpa [coeff_sub, coeff_X, show 1 ≠ r by omega] using network_coeff_r r hr (fun i => w i ^ r) n
  · have hidx : 2 * r - 1 = 2 * (r - 1) + 1 := by omega
    rw [coeff_sub, coeff_X, ite_eq_right (by omega : 1 ≠ 2 * r - 1), sub_zero, hidx,
      network_coeff_graded r hr, graded_coeff_two]
end ResidualSLT
