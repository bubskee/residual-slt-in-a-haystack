module
public import ResidualSLT.ActiveDirections
public import Mathlib.RingTheory.Polynomial.Basic

/-! Independent retained directions at one nonzero active block. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Set

/-- Distinct increasing polynomial degrees give independence, including a constant first column. -/
theorem polynomial_family_independent_of_strictMono_degree {n : ℕ} (v : Fin n → ℝ[X])
    (hne : ∀ i, v i ≠ 0) (hdeg : StrictMono (fun i => (v i).natDegree)) :
    LinearIndependent ℝ v := by
  induction n with
  | zero => exact linearIndependent_empty_type
  | succ n ih =>
    rw [linearIndependent_finSucc']
    constructor
    · apply ih
      · intro i; exact hne i.castSucc
      · intro i j hij; exact hdeg (by exact hij)
    · have hs : Submodule.span ℝ (range (fun i : Fin n => v i.castSucc)) ≤
          degreeLT ℝ (v (Fin.last n)).natDegree := by
        apply Submodule.span_le.mpr
        rintro _ ⟨i,rfl⟩
        change v i.castSucc ∈ degreeLT ℝ (v (Fin.last n)).natDegree
        rw [mem_degreeLT]
        exact degree_le_natDegree.trans_lt (by exact_mod_cast hdeg (Fin.castSucc_lt_last i))
      intro hh
      have ht := mem_degreeLT.mp (hs hh)
      rw [degree_eq_natDegree (hne _)] at ht
      exact lt_irrefl _ ht

@[expose] def activeTarget (r : ℕ) (c : ℝ) : ℝ[X] := X + C c * X^r
@[expose] def activeDerivativeFactor (r : ℕ) (c : ℝ) : ℝ[X] :=
  1 + C ((r:ℝ)*c)*X^(r-1)

@[expose] def oneActiveSignedDirections (r : ℕ) (c : ℝ) : Fin 5 → ℝ[X] :=
  ![X^r, activeDerivativeFactor r c*X^r, activeDerivativeFactor r c*X^(2*r-1),
    activeTarget r c^r, activeTarget r c^(2*r-1)]

@[expose] def oneActiveEvenDirections (r : ℕ) (c : ℝ) : Fin 3 → ℝ[X] :=
  ![X^r, activeDerivativeFactor r c*X^r, activeTarget r c^r]

theorem activeTarget_natDegree (r : ℕ) (hr : 2 ≤ r) (c : ℝ) (hc : c ≠ 0) :
    (activeTarget r c).natDegree = r := by
  unfold activeTarget
  rw [natDegree_add_eq_right_of_natDegree_lt, natDegree_C_mul hc, natDegree_X_pow]
  rw [natDegree_X, natDegree_C_mul hc, natDegree_X_pow]
  omega

theorem activeDerivativeFactor_natDegree (r : ℕ) (hr : 2 ≤ r) (c : ℝ) (hc : c ≠ 0) :
    (activeDerivativeFactor r c).natDegree = r-1 := by
  unfold activeDerivativeFactor
  rw [natDegree_one_add, natDegree_C_mul (mul_ne_zero (by exact_mod_cast (by omega : r ≠ 0)) hc),natDegree_X_pow]

theorem oneActiveSignedDirections_degrees (r : ℕ) (hr : 3 ≤ r) (c : ℝ) (hc : c ≠ 0) :
    (fun i => (oneActiveSignedDirections r c i).natDegree) =
      ![r,2*r-1,3*r-2,r^2,r*(2*r-1)] := by
  have hp := activeDerivativeFactor_natDegree r (by omega) c hc
  have hpne : activeDerivativeFactor r c ≠ 0 := by intro hz; simp [hz] at hp; omega
  funext i
  fin_cases i <;> norm_num [oneActiveSignedDirections, natDegree_mul hpne,
    natDegree_X_pow, natDegree_pow,activeTarget_natDegree r (by omega) c hc,hp, pow_two, Nat.mul_comm] <;> omega

/-- All five virtual signed directions are independent for r≥3.
Deleting columns for empty or singleton groups preserves this fact. -/
theorem oneActiveSignedDirections_independent (r : ℕ) (hr : 3 ≤ r) (c : ℝ) (hc : c ≠ 0) :
    LinearIndependent ℝ (oneActiveSignedDirections r c) := by
  have hd := oneActiveSignedDirections_degrees r hr c hc
  apply polynomial_family_independent_of_strictMono_degree
  · intro i hi
    have he := congrFun hd i
    rw [hi,natDegree_zero] at he
    fin_cases i <;> norm_num at he <;> first | omega | nlinarith
  · rw [hd]
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    have hg := two_direction_degree_gaps r 1 hr (by omega)
    fin_cases i <;> norm_num at * <;> omega

/-- Even degrees require only three directions; their independence includes r=2. -/
theorem oneActiveEvenDirections_independent (r : ℕ) (hr : 2 ≤ r) (c : ℝ) (hc : c ≠ 0) :
    LinearIndependent ℝ (oneActiveEvenDirections r c) := by
  have hp := activeDerivativeFactor_natDegree r hr c hc
  have hpne : activeDerivativeFactor r c ≠ 0 := by intro hz; simp [hz] at hp; omega
  have hd : (fun i => (oneActiveEvenDirections r c i).natDegree) = ![r,2*r-1,r^2] := by
    funext i
    fin_cases i <;> norm_num [oneActiveEvenDirections, natDegree_mul hpne,
      natDegree_X_pow, natDegree_pow,activeTarget_natDegree r hr c hc,hp, pow_two, Nat.mul_comm]
    omega
  apply polynomial_family_independent_of_strictMono_degree
  · intro i hi
    have he := congrFun hd i
    rw [hi,natDegree_zero] at he
    fin_cases i <;> norm_num at he <;> first | omega | nlinarith
  · rw [hd]
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> norm_num <;> nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ 2*r)]

end ResidualSLT
