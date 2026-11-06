module
public import ResidualSLT.PolynomialNetworks
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.Units

/-! The coprimality step in the arbitrary-active-block induction.
This module does not claim the full direction-family independence or any local loss equivalence. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial
variable {F : Type*} [Field F]

/-- A general separator. For an appended degree-r block use `a = r*e`, `n = r-2`. -/
@[expose] def separator (H : F[X]) (a : F) (n : ℕ) : F[X] :=
  1 + C a * H ^ (n + 1)

/-- Explicit Bezout certificate, independent of real-root behavior. -/
theorem separator_coprime (H : F[X]) (a : F) (n : ℕ) :
    IsCoprime (separator H a n) H := by
  refine ⟨1, -(C a * H ^ n), ?_⟩
  simp only [separator, pow_succ]
  ring

theorem separator_natDegree (H : F[X]) (a : F) (ha : a ≠ 0) (n : ℕ) :
    (separator H a n).natDegree = H.natDegree * (n + 1) := by
  rw [separator, natDegree_one_add, natDegree_C_mul ha, natDegree_pow]
  exact Nat.mul_comm _ _

/-- A new active direction cannot be absorbed by any polynomial multiple of the separator.
In particular it cannot be absorbed by the span of multiplied old directions. -/
theorem separator_relation (H Q : F[X]) (a t : F) (ha : a ≠ 0)
    (hH : 0 < H.natDegree) (n m : ℕ)
    (h : separator H a n * Q + C t * H ^ m = 0) : Q = 0 ∧ t = 0 := by
  have hdeg : 0 < (separator H a n).natDegree := by
    rw [separator_natDegree H a ha n]
    exact Nat.mul_pos hH (by omega)
  have hp : separator H a n ≠ 0 := by
    intro hz
    simp [hz] at hdeg
  have hd : separator H a n ∣ C t * H ^ m := by
    refine ⟨-Q, ?_⟩
    linear_combination h
  have hd' : separator H a n ∣ C t :=
    (separator_coprime H a n).pow_right.dvd_of_dvd_mul_right hd
  have ht : t = 0 := by
    by_contra ht
    have hle := natDegree_le_of_dvd hd' (C_ne_zero.mpr ht)
    simp only [natDegree_C] at hle
    omega
  refine ⟨?_, ht⟩
  simpa [ht, hp] using h

/-- The exact active-block factor in the paper, over any characteristic-zero field. -/
theorem active_factor_relation [CharZero F] (r : ℕ) (hr : 2 ≤ r)
    (H Q : F[X]) (e t : F) (he : e ≠ 0) (hH : 0 < H.natDegree)
    (h : (1 + C ((r : F) * e) * H ^ (r - 1)) * Q + C t * H ^ r = 0) :
    Q = 0 ∧ t = 0 := by
  apply separator_relation H Q ((r : F) * e) t
    (mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) he) hH (r - 2) r
  simpa [separator, show r - 2 + 1 = r - 1 by omega] using h

/-- The two strict degree gaps used for odd degrees (indeed all r≥3). -/
theorem two_direction_degree_gaps (r D : ℕ) (hr : 3 ≤ r) (hD : 0 < D) :
    (3 * r - 2) * D < r ^ 2 * D ∧ r ^ 2 * D < r * (2 * r - 1) * D := by
  constructor <;> apply Nat.mul_lt_mul_of_pos_right _ hD
  · have hm : 3 * r ≤ r * r := Nat.mul_le_mul_right r hr
    have hs : 3 * r - 2 + 2 = 3 * r := by omega
    nlinarith
  · rw [pow_two]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
end ResidualSLT
