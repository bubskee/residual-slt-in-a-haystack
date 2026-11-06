module
public import ResidualSLT.InactiveGroupRemainder

/-! Actual group coefficients in a fixed finite auxiliary space, padded to retain two slots. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset

@[simp] theorem graded_zero_weights (r n : ℕ) : graded r (fun _ => (0:ℝ)) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [graded,ih]

theorem graded_natDegree_le (r n : ℕ) (hr : 2 ≤ r) (u : ℕ → ℝ) :
    (graded r u n).natDegree ≤ r^n := by
  have hn := network_natDegree_le r hr u n
  have hnet : network r u n ≠ 0 := by
    intro hz
    have hh := network_coeff_graded r hr u n 0
    simp [hz] at hh
  have hp : (graded r u n).comp (X^(r-1)) ≠ 0 := by
    intro hz
    apply hnet
    rw [network_eq_graded r (by omega),hz,mul_zero]
  rw [network_eq_graded r (by omega),natDegree_X_mul hp,natDegree_comp,natDegree_X_pow] at hn
  have hh := Nat.mul_le_mul_left (graded r u n).natDegree (by omega : 1 ≤ r-1)
  omega

@[expose] def inactiveAuxVector (r n : ℕ) (u : Fin n → ℝ) : Fin (r^n+2) → ℝ :=
  fun j => (graded r (zeroExtend u) n).coeff (j.val+1)

@[expose] def inactiveAuxRemainder (r n : ℕ) (u : Fin n → ℝ) : Fin (r^n+2) → ℝ :=
  fun j => if j.val<2 then 0 else inactiveAuxVector r n u j

theorem inactiveAuxVector_continuous (r n : ℕ) (hr : 2 ≤ r) :
    Continuous (inactiveAuxVector r n) := by
  apply continuous_pi_iff.mpr
  intro j
  unfold inactiveAuxVector
  simp_rw [← network_coeff_graded r hr]
  apply network_coeff_continuous
  intro i
  unfold zeroExtend
  split_ifs <;> fun_prop

@[simp] theorem inactiveAuxVector_zero (r n : ℕ) : inactiveAuxVector r n 0 = 0 := by
  have he : zeroExtend (0:Fin n → ℝ) = fun _ => 0 := by funext i; simp [zeroExtend]
  funext j
  simp [inactiveAuxVector,he,coeff_one]

/-- The two retained entries are exactly S and B, even when the group is empty or a singleton. -/
theorem inactiveAuxVector_split (r n : ℕ) (u : Fin n → ℝ) :
    inactiveAuxVector r n u =
      Pi.single ⟨0,by omega⟩ (∑ i, u i) +
      Pi.single ⟨1,by omega⟩ ((graded r (zeroExtend u) n).coeff 2) +
      inactiveAuxRemainder r n u := by
  funext j
  by_cases h0 : j.val=0
  · have hj : j = ⟨0,by omega⟩ := Fin.ext h0
    rw [hj]
    simp [inactiveAuxVector,inactiveAuxRemainder,graded_coeff_one,
      ← Fin.sum_univ_eq_sum_range,zeroExtend]
  · by_cases h1 : j.val=1
    · have hj : j = ⟨1,by omega⟩ := Fin.ext h1
      rw [hj]
      simp [inactiveAuxVector,inactiveAuxRemainder]
    · have hj0 : j ≠ ⟨0,by omega⟩ := by intro he; exact h0 (congrArg Fin.val he)
      have hj1 : j ≠ ⟨1,by omega⟩ := by intro he; exact h1 (congrArg Fin.val he)
      simp [inactiveAuxRemainder,show ¬ j.val<2 by omega,Fin.ext_iff,h0,h1]

/-- Uniform vector version of the cancellation-safe relative remainder bound. -/
theorem inactiveAuxRemainder_bound (r n : ℕ) (hr : 2 ≤ r) (u : Fin n → ℝ)
    (hu : ‖u‖ ≤ 1) (hS : |∑ i, u i| ≤ 1) :
    ‖inactiveAuxRemainder r n u‖ ≤
      (signedRemainderEnvelope r n*n*n)*‖u‖*
        (|∑ i, u i|+|(graded r (zeroExtend u) n).coeff 2|) := by
  apply (pi_norm_le_iff_of_nonneg (by positivity [signedRemainderEnvelope_nonneg r n])).mpr
  intro j
  by_cases hj : j.val<2
  · simp only [inactiveAuxRemainder,ite_eq_left hj,norm_zero]
    positivity [signedRemainderEnvelope_nonneg r n]
  · simpa only [inactiveAuxRemainder,ite_eq_right hj,inactiveAuxVector,Real.norm_eq_abs] using
      graded_omitted_coeff_relative_bound r n (j.val+1) hr (by omega) u hu hS

/-- Padding the actual graded coefficient vector gives an exact polynomial evaluation. -/
theorem inactiveAuxVector_eval (r n : ℕ) (hr : 2 ≤ r) (u : Fin n → ℝ) (x : ℝ) :
    (network r (zeroExtend u) n).eval x =
      x+∑ j : Fin (r^n+2), inactiveAuxVector r n u j*x^(r+j.val*(r-1)) := by
  rw [network_eq_graded r (by omega)]
  simp only [eval_mul,eval_X,eval_comp,eval_pow]
  rw [eval_eq_sum_range' (show (graded r (zeroExtend u) n).natDegree < (r^n+2)+1 by
    have hh := graded_natDegree_le r n hr (zeroExtend u); omega)]
  rw [show r^n+2+1=1+(r^n+2) by omega,sum_range_add]
  simp only [sum_range_one,graded_coeff_zero,pow_zero,mul_one]
  rw [mul_add,mul_one,mul_sum,← Fin.sum_univ_eq_sum_range]
  congr 1
  apply sum_congr rfl
  intro j _
  dsimp only [inactiveAuxVector]
  rw [show 1+j.val=j.val+1 by omega,← pow_mul]
  have he : r+j.val*(r-1) = (r-1)*(j.val+1)+1 := by
    have hh : r-1+1=r := by omega
    nlinarith
  rw [he,pow_succ]
  ring

end ResidualSLT
