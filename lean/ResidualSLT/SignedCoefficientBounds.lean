module
public import ResidualSLT.CoefficientBounds
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Signed coefficient control after removing the exact linear effective-weight term.
No sign condition is imposed on the weights. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset

/-- Coefficientwise absolute majorization by a real polynomial. -/
@[expose] def CoeffMajorized (p q : ℝ[X]) : Prop := ∀ k, |p.coeff k| ≤ q.coeff k

theorem CoeffMajorized.nonneg {p q : ℝ[X]} (h : CoeffMajorized p q) (k : ℕ) :
    0 ≤ q.coeff k := (abs_nonneg _).trans (h k)

theorem CoeffMajorized.add {p q a b : ℝ[X]} (h : CoeffMajorized p q)
    (g : CoeffMajorized a b) : CoeffMajorized (p + a) (q + b) := by
  intro k
  simp only [coeff_add]
  exact (abs_add_le _ _).trans (add_le_add (h k) (g k))

theorem CoeffMajorized.mul {p q a b : ℝ[X]} (h : CoeffMajorized p q)
    (g : CoeffMajorized a b) : CoeffMajorized (p * a) (q * b) := by
  intro k
  simp only [coeff_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro ij _
  rw [abs_mul]
  exact mul_le_mul (h ij.1) (g ij.2) (abs_nonneg _) (h.nonneg _)

theorem CoeffMajorized.pow {p q : ℝ[X]} (h : CoeffMajorized p q) (m : ℕ) :
    CoeffMajorized (p ^ m) (q ^ m) := by
  induction m with
  | zero => intro k; simp only [pow_zero, coeff_one]; split_ifs <;> norm_num
  | succ m ih => simpa only [pow_succ] using ih.mul h

theorem coeffMajorized_X : CoeffMajorized (X : ℝ[X]) X := by
  intro k
  simp only [coeff_X]; split_ifs <;> norm_num

theorem coeffMajorized_C (a : ℝ) : CoeffMajorized (C a) (C |a|) := by
  intro k
  simp only [coeff_C]; split_ifs <;> simp

theorem CoeffMajorized.pow_sub_X {p q : ℝ[X]} (h : CoeffMajorized p q)
    (hd : CoeffMajorized (p - X) (q - X)) (m : ℕ) :
    CoeffMajorized (p ^ m - X ^ m) (q ^ m - X ^ m) := by
  induction m with
  | zero => intro k; simp
  | succ m ih =>
    have he (a : ℝ[X]) : a ^ (m + 1) - X ^ (m + 1) =
        (a ^ m - X ^ m) * a + X ^ m * (a - X) := by ring
    rw [he p, he q]
    exact (ih.mul h).add ((coeffMajorized_X.pow m).mul hd)

/-- The network and residual are majorized by replacing effective weights with absolutes. -/
theorem network_abs_majorized (r n : ℕ) (u : ℕ → ℝ) :
    CoeffMajorized (network r u n) (network r (fun i => |u i|) n) ∧
    CoeffMajorized (network r u n - X) (network r (fun i => |u i|) n - X) := by
  induction n with
  | zero => exact ⟨coeffMajorized_X, by intro k; simp [network]⟩
  | succ n ih =>
    have ht := (coeffMajorized_C (u n)).mul (ih.1.pow r)
    constructor
    · exact ih.1.add ht
    · have he (v : ℕ → ℝ) : network r v (n + 1) - X =
          (network r v n - X) + C (v n) * network r v n ^ r := by rw [network]; ring
      rw [he u, he (fun i => |u i|)]
      exact ih.2.add ht

/-- Remove the exact term linear in the effective weights. -/
@[expose] def networkRemainder (r n : ℕ) (u : ℕ → ℝ) : ℝ[X] :=
  network r u n - X - C (∑ i ∈ range n, u i) * X ^ r

theorem networkRemainder_succ (r n : ℕ) (u : ℕ → ℝ) :
    networkRemainder r (n + 1) u = networkRemainder r n u +
      C (u n) * (network r u n ^ r - X ^ r) := by
  simp only [networkRemainder, network, sum_range_succ, map_add]
  ring

theorem networkRemainder_abs_majorized (r n : ℕ) (u : ℕ → ℝ) :
    CoeffMajorized (networkRemainder r n u) (networkRemainder r n (fun i => |u i|)) := by
  induction n with
  | zero => intro k; simp [networkRemainder, network]
  | succ n ih =>
    rw [networkRemainder_succ, networkRemainder_succ]
    have h := network_abs_majorized r n u
    exact ih.add ((coeffMajorized_C (u n)).mul (h.1.pow_sub_X h.2 r))

/-- A finite envelope for the second-order effective-weight remainder. -/
@[expose] def signedRemainderEnvelope (r : ℕ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => signedRemainderEnvelope r n +
      networkEnvelope r n * r * networkEnvelope r n ^ (r - 1)

theorem signedRemainderEnvelope_nonneg (r n : ℕ) : 0 ≤ signedRemainderEnvelope r n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hb : 0 ≤ networkEnvelope r n := le_trans zero_le_one (networkEnvelope_one_le r n)
    simp only [signedRemainderEnvelope]
    positivity

/-- Evaluation of the power increment is linear in the absolute effective-weight sum. -/
theorem network_power_eval_bound (r n : ℕ) (v : ℕ → ℝ)
    (hv : ∀ i < n, 0 ≤ v i ∧ v i ≤ 1) :
    (network r v n).eval 1 ^ r - 1 ≤
      (networkEnvelope r n * r * networkEnvelope r n ^ (r - 1)) * ∑ i ∈ range n, v i := by
  obtain ⟨ha, hb, hd⟩ := network_eval_one_control r n v hv
  have h0 : 0 ≤ (network r v n).eval 1 := le_trans zero_le_one ha
  have he := abs_pow_sub_pow_le (a := (network r v n).eval 1) (b := (1 : ℝ)) (n := r)
  simp only [one_pow, abs_of_nonneg h0, abs_one, max_eq_left ha,
    abs_of_nonneg (sub_nonneg.mpr ha)] at he
  have hpow := pow_le_pow_left₀ h0 hb (r - 1)
  have hsum : 0 ≤ ∑ i ∈ range n, v i := Finset.sum_nonneg (fun i hi => (hv i (mem_range.mp hi)).1)
  have hB : 0 ≤ networkEnvelope r n := le_trans zero_le_one (networkEnvelope_one_le r n)
  have hmul := mul_le_mul (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg r)) hpow
    (pow_nonneg h0 _) (by positivity : 0 ≤ networkEnvelope r n * (∑ i ∈ range n, v i) * r)
  calc
    _ ≤ |(network r v n).eval 1 ^ r - 1| := le_abs_self _
    _ ≤ _ := he
    _ ≤ _ := hmul
    _ = _ := by ring

/-- The absolute-weight remainder is second order in the total absolute weight. -/
theorem networkRemainder_eval_bound (r n : ℕ) (v : ℕ → ℝ)
    (hv : ∀ i < n, 0 ≤ v i ∧ v i ≤ 1) :
    (networkRemainder r n v).eval 1 ≤
      signedRemainderEnvelope r n * (∑ i ∈ range n, v i) ^ 2 := by
  induction n with
  | zero => simp [networkRemainder, network, signedRemainderEnvelope]
  | succ n ih =>
    have hv' : ∀ i < n, 0 ≤ v i ∧ v i ≤ 1 := fun i hi => hv i (by omega)
    have hn := (hv n (by omega)).1
    have ht : 0 ≤ ∑ i ∈ range n, v i := Finset.sum_nonneg (fun i hi => (hv' i (mem_range.mp hi)).1)
    have hd := signedRemainderEnvelope_nonneg r n
    have hB : 0 ≤ networkEnvelope r n := le_trans zero_le_one (networkEnvelope_one_le r n)
    have hF : 0 ≤ networkEnvelope r n * r * networkEnvelope r n ^ (r - 1) := by positivity
    have hp := mul_le_mul_of_nonneg_left (network_power_eval_bound r n v hv') hn
    have hi := ih hv'
    rw [networkRemainder_succ, eval_add, eval_mul, eval_C, eval_sub, eval_pow, eval_pow, eval_X, one_pow]
    rw [signedRemainderEnvelope, sum_range_succ]
    have hsq : (∑ i ∈ range n, v i) ^ 2 ≤ ((∑ i ∈ range n, v i) + v n) ^ 2 := by nlinarith
    have hprod : v n * (∑ i ∈ range n, v i) ≤ ((∑ i ∈ range n, v i) + v n) ^ 2 := by nlinarith [sq_nonneg ((∑ i ∈ range n, v i) - v n)]
    have h1 := mul_le_mul_of_nonneg_left hsq hd
    have h2 := mul_le_mul_of_nonneg_left hprod hF
    nlinarith

/-- Signed remainder coefficients are O(Σuᵢ²), uniformly on the effective unit cube. -/
theorem signed_remainder_coeff_bound (r n : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i < n, |u i| ≤ 1) (k : ℕ) :
    |(networkRemainder r n u).coeff k| ≤
      (signedRemainderEnvelope r n * n) * ∑ i ∈ range n, u i ^ 2 := by
  have h := networkRemainder_abs_majorized r n u
  have hv : ∀ i < n, 0 ≤ |u i| ∧ |u i| ≤ 1 := fun i hi => ⟨abs_nonneg _, hu i hi⟩
  have hcs : (∑ i ∈ range n, |u i|) ^ 2 ≤ (n : ℝ) * ∑ i ∈ range n, u i ^ 2 := by
    simpa [sq_abs, mul_comm] using
      Finset.sum_mul_sq_le_sq_mul_sq (range n) (fun i => |u i|) (fun _ => (1 : ℝ))
  calc
    _ ≤ (networkRemainder r n (fun i => |u i|)).coeff k := h k
    _ ≤ (networkRemainder r n (fun i => |u i|)).eval 1 := coeff_le_eval_one _ h.nonneg k
    _ ≤ signedRemainderEnvelope r n * (∑ i ∈ range n, |u i|) ^ 2 :=
      networkRemainder_eval_bound r n _ hv
    _ ≤ signedRemainderEnvelope r n * ((n : ℝ) * ∑ i ∈ range n, u i ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (signedRemainderEnvelope_nonneg r n)
    _ = _ := by ring

/-- In particular, every coefficient other than the leading one is O(Σuᵢ²). -/
theorem signed_higher_coeff_bound (r n : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i < n, |u i| ≤ 1) (k : ℕ) (hk : k ≠ r) :
    |(network r u n - X).coeff k| ≤
      (signedRemainderEnvelope r n * n) * ∑ i ∈ range n, u i ^ 2 := by
  have h := signed_remainder_coeff_bound r n u hu k
  simpa only [networkRemainder, coeff_sub, coeff_C_mul, coeff_X_pow,
    ite_eq_right hk, mul_zero, sub_zero] using h
end ResidualSLT
