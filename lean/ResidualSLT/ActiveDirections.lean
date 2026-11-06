module
public import ResidualSLT.Separation
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.BilinearMap

/-! An indexed active-direction extension step.
The full inactive-group family, coordinate maps, and analytic remainder estimates are separate. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Set
variable {F : Type*} [Field F] {ι : Type*}

/-- Multiplying an independent old family by a separator and adjoining a new power
preserves linear independence. The index type need not be finite. -/
theorem separator_family_independent (H : F[X]) (a : F) (ha : a ≠ 0)
    (hH : 0 < H.natDegree) (n m : ℕ) (v : ι → F[X]) (hv : LinearIndependent F v) :
    LinearIndependent F (fun o : Option ι =>
      Option.casesOn' o (H ^ m) (fun i => separator H a n * v i)) := by
  let T : F[X] →ₗ[F] F[X] := LinearMap.mulLeft F (separator H a n)
  have hp : separator H a n ≠ 0 := by
    intro hz
    have hd := separator_natDegree H a ha n
    rw [hz, natDegree_zero] at hd
    have := Nat.mul_pos hH (by omega : 0 < n + 1)
    omega
  have hinj : Function.Injective T := by
    intro x y hxy
    exact mul_left_cancel₀ hp hxy
  have hv' : LinearIndependent F (fun i => separator H a n * v i) :=
    hv.map' T (LinearMap.ker_eq_bot.mpr hinj)
  apply hv'.option
  have hspan : Submodule.span F (range (fun i => separator H a n * v i)) ≤ T.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨v i, rfl⟩
  intro hh
  obtain ⟨Q, hQ⟩ := hspan hh
  change separator H a n * Q = H ^ m at hQ
  have hz : separator H a n * Q + C (-1 : F) * H ^ m = 0 := by
    rw [hQ, map_neg, map_one]
    ring
  have ht := (separator_relation H Q a (-1) ha hH n m hz).2
  exact neg_ne_zero.mpr one_ne_zero ht

/-- The exact new-active-block extension, over a characteristic-zero field. -/
theorem active_family_independent [CharZero F] (r : ℕ) (hr : 2 ≤ r)
    (H : F[X]) (e : F) (he : e ≠ 0) (hH : 0 < H.natDegree)
    (v : ι → F[X]) (hv : LinearIndependent F v) :
    LinearIndependent F (fun o : Option ι => Option.casesOn' o (H ^ r)
      (fun i => (1 + C ((r : F) * e) * H ^ (r - 1)) * v i)) := by
  simpa [separator, show r - 2 + 1 = r - 1 by omega] using
    separator_family_independent H ((r : F) * e)
      (mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) he) hH (r - 2) r v hv
end ResidualSLT
