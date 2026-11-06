module
public import ResidualSLT.SparseNetworkFeatures

/-! Uniform third-order control of the omitted inactive-group coefficients.
Effective weights remain algebraic inputs; no change of parameter measure is used. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset NormedSpace

/-- Effective scaling is input scaling of the graded polynomial. -/
theorem graded_scale (r n : ℕ) (u : ℕ → ℝ) (a : ℝ) :
    graded r (fun i => a*u i) n = (graded r u n).comp (C a * X) := by
  induction n with
  | zero => simp [graded]
  | succ n ih =>
    simp only [graded, ih, add_comp, mul_comp, C_comp, X_comp, pow_comp, map_mul]
    ring

/-- Each graded coefficient is exactly homogeneous in the effective weights. -/
theorem graded_coeff_scale (r n k : ℕ) (u : ℕ → ℝ) (a : ℝ) :
    (graded r (fun i => a*u i) n).coeff k = a^k*(graded r u n).coeff k := by
  rw [graded_scale, comp_C_mul_X_coeff, mul_comm]

/-- Zero padding commutes with scalar multiplication. -/
theorem zeroExtend_smul (n : ℕ) (u : Fin n → ℝ) (a : ℝ) :
    zeroExtend (a • u) = fun i => a*zeroExtend u i := by
  funext i
  unfold zeroExtend
  split_ifs <;> simp

/-- A finite envelope for a graded coefficient of order at least two on the unit cube. -/
theorem graded_high_coeff_unit_bound (r n k : ℕ) (hr : 2 ≤ r) (hk : 2 ≤ k)
    (u : Fin n → ℝ) (hu : ‖u‖ ≤ 1) :
    |(graded r (zeroExtend u) n).coeff k| ≤ signedRemainderEnvelope r n * n * n := by
  have hw : ∀ i < n, |zeroExtend u i| ≤ 1 := by
    intro i hi
    simpa [zeroExtend,hi] using (norm_le_pi_norm u ⟨i,hi⟩).trans hu
  have hidx : k*(r-1)+1 ≠ r := by
    have hh := Nat.mul_le_mul_right (r-1) hk
    omega
  have hb := signed_higher_coeff_bound r n (zeroExtend u) hw (k*(r-1)+1) hidx
  rw [coeff_sub, coeff_X, ite_eq_right (by have hp := Nat.mul_pos (by omega : 0 < k) (by omega : 0 < r-1); omega : 1 ≠ k*(r-1)+1), sub_zero,
    network_coeff_graded r hr] at hb
  have hq : ∑ i ∈ range n, zeroExtend u i ^ 2 ≤ (n:ℝ) := by
    calc
      _ ≤ ∑ _i ∈ range n, (1:ℝ) := by
        apply sum_le_sum
        intro i hi
        have hh := hw i (mem_range.mp hi)
        nlinarith [sq_abs (zeroExtend u i),abs_nonneg (zeroExtend u i)]
      _ = _ := by simp
  exact hb.trans (mul_le_mul_of_nonneg_left hq (by positivity [signedRemainderEnvelope_nonneg r n]))

/-- The omitted coefficients have a uniform cubic bound, including cancellation directions. -/
theorem graded_omitted_coeff_cubic_bound (r n k : ℕ) (hr : 2 ≤ r) (hk : 3 ≤ k)
    (u : Fin n → ℝ) (hu : ‖u‖ ≤ 1) :
    |(graded r (zeroExtend u) n).coeff k| ≤
      (signedRemainderEnvelope r n*n*n)*‖u‖^3 := by
  by_cases hz : u = 0
  · subst u
    have he : zeroExtend (0:Fin n → ℝ) = fun _ => 0 := by funext i; simp [zeroExtend]
    rw [he]
    have hg : ∀ m, graded r (fun _ => (0:ℝ)) m = 1 := by
      intro m
      induction m with
      | zero => rfl
      | succ n ih => simp [graded,ih]
    simp [hg,coeff_one,show k ≠ 0 by omega]
  · have hn := norm_normalize hz
    have hb := graded_high_coeff_unit_bound r n k hr (by omega) (normalize u) hn.le
    have he : u = ‖u‖ • normalize u := (norm_smul_normalize u).symm
    conv_lhs => rw [he,zeroExtend_smul,graded_coeff_scale]
    rw [abs_mul,abs_pow,abs_of_nonneg (norm_nonneg u)]
    have hp : ‖u‖^k ≤ ‖u‖^3 := pow_le_pow_of_le_one (norm_nonneg u) hu hk
    calc
      _ ≤ ‖u‖^k*(signedRemainderEnvelope r n*n*n) :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg (norm_nonneg u) _)
      _ ≤ ‖u‖^3*(signedRemainderEnvelope r n*n*n) :=
        mul_le_mul_of_nonneg_right hp (by positivity [signedRemainderEnvelope_nonneg r n])
      _ = _ := mul_comm _ _

/-- The maximum norm is bounded by the effective sum of squares, also for an empty group. -/
theorem effective_norm_sq_le_sum (n : ℕ) (u : Fin n → ℝ) :
    ‖u‖^2 ≤ ∑ i, u i^2 := by
  have hq : 0 ≤ ∑ i, u i^2 := sum_nonneg (fun i _ => sq_nonneg _)
  have hb : ‖u‖ ≤ Real.sqrt (∑ i, u i^2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    have hi : u i^2 ≤ ∑ j, u j^2 := single_le_sum (fun j _ => sq_nonneg _) (mem_univ i)
    rw [Real.norm_eq_abs]
    nlinarith [Real.sq_sqrt hq,Real.sqrt_nonneg (∑ i, u i^2),sq_abs (u i),abs_nonneg (u i)]
  nlinarith [Real.sq_sqrt hq,Real.sqrt_nonneg (∑ i, u i^2),norm_nonneg u]

/-- The first two retained coefficients control the sum of squares even at exact cancellation. -/
theorem effective_sum_sq_le_retained (r n : ℕ) (hr : 2 ≤ r) (u : Fin n → ℝ)
    (hS : |∑ i, u i| ≤ 1) :
    (∑ i, u i^2) ≤ |∑ i, u i| + |(graded r (zeroExtend u) n).coeff 2| := by
  have he := graded_coeff_two_SQ r (zeroExtend u) n
  simp only [← Fin.sum_univ_eq_sum_range,zeroExtend,dite_eq_left (Fin.isLt _)] at he
  have hr' : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hb := neg_abs_le ((graded r (zeroExtend u) n).coeff 2)
  have hS2 : (∑ i, u i)^2 ≤ |∑ i, u i| := by
    nlinarith [sq_abs (∑ i, u i),abs_nonneg (∑ i, u i)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hr') (abs_nonneg ((graded r (zeroExtend u) n).coeff 2))]

/-- Precisely the relative error needed for the signed one-active comparison.
No division by a retained coefficient is used. -/
theorem graded_omitted_coeff_relative_bound (r n k : ℕ) (hr : 2 ≤ r) (hk : 3 ≤ k)
    (u : Fin n → ℝ) (hu : ‖u‖ ≤ 1) (hS : |∑ i, u i| ≤ 1) :
    |(graded r (zeroExtend u) n).coeff k| ≤
      (signedRemainderEnvelope r n*n*n)*‖u‖*
        (|∑ i, u i| + |(graded r (zeroExtend u) n).coeff 2|) := by
  have hq := (effective_norm_sq_le_sum n u).trans (effective_sum_sq_le_retained r n hr u hS)
  have hc : 0 ≤ signedRemainderEnvelope r n*n*n := by positivity [signedRemainderEnvelope_nonneg r n]
  apply (graded_omitted_coeff_cubic_bound r n k hr hk u hu).trans
  nlinarith [mul_le_mul_of_nonneg_left hq (mul_nonneg hc (norm_nonneg u))]

/-- In a nonnegative effective group, every omitted coefficient is small relative to S.
This is the separate even-degree argument, including r=2. -/
theorem effective_nonneg_higher_relative_bound (r n k : ℕ) (hk : k ≠ r)
    (u : Fin n → ℝ) (hu : ‖u‖ ≤ 1) (hpos : ∀ i, 0 ≤ u i) :
    |(network r (zeroExtend u) n-X).coeff k| ≤
      (signedRemainderEnvelope r n*n)*‖u‖*(∑ i, u i) := by
  have hw : ∀ i < n, |zeroExtend u i| ≤ 1 := by
    intro i hi
    simpa [zeroExtend,hi] using (norm_le_pi_norm u ⟨i,hi⟩).trans hu
  have hb := signed_higher_coeff_bound r n (zeroExtend u) hw k hk
  simp only [← Fin.sum_univ_eq_sum_range,zeroExtend,dite_eq_left (Fin.isLt _)] at hb
  have hq : (∑ i, u i^2) ≤ ‖u‖*(∑ i, u i) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    have hi : u i ≤ ‖u‖ := (le_abs_self _).trans (norm_le_pi_norm u i)
    nlinarith [mul_le_mul_of_nonneg_right hi (hpos i)]
  have hc : 0 ≤ signedRemainderEnvelope r n*n := by positivity [signedRemainderEnvelope_nonneg r n]
  exact hb.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hq hc)

end ResidualSLT
