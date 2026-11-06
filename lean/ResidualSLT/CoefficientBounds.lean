module
public import ResidualSLT.Coefficients
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Uniform coefficient bounds for nonnegative effective weights.
These are derived directly from the recursion, without assuming loss comparison or
using cancellations. They apply to even-degree raw weights on the unit cube. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset

/-- A polynomial with nonnegative coefficients retains that property under powers. -/
theorem coeff_pow_nonneg (p : ℝ[X]) (hp : ∀ k, 0 ≤ p.coeff k) (m k : ℕ) :
    0 ≤ (p ^ m).coeff k := by
  induction m generalizing k with
  | zero => simp only [pow_zero, coeff_one]; split_ifs <;> norm_num
  | succ m ih =>
    rw [pow_succ, coeff_mul]
    exact Finset.sum_nonneg (fun ij _ => mul_nonneg (ih ij.1) (hp ij.2))

/-- Both the network and its residual have nonnegative coefficients when u≥0. -/
theorem network_residual_coeff_nonneg (r n : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i < n, 0 ≤ u i) (k : ℕ) :
    0 ≤ (network r u n).coeff k ∧ 0 ≤ (network r u n - X).coeff k := by
  induction n generalizing k with
  | zero => simp only [network, coeff_X, sub_self, coeff_zero, le_refl, and_true]; split_ifs <;> norm_num
  | succ n ih =>
    have hp : ∀ j, 0 ≤ (network r u n).coeff j := fun j => (ih (fun i hi => hu i (by omega)) j).1
    have hr := (ih (fun i hi => hu i (by omega)) k).2
    have ht : 0 ≤ u n * (network r u n ^ r).coeff k :=
      mul_nonneg (hu n (by omega)) (coeff_pow_nonneg _ hp r k)
    constructor
    · simpa only [network, coeff_add, coeff_C_mul] using add_nonneg (hp k) ht
    · have heq : network r u (n + 1) - X =
          (network r u n - X) + C (u n) * network r u n ^ r := by rw [network]; ring
      simpa only [heq, coeff_add, coeff_C_mul] using add_nonneg hr ht

/-- Every nonnegative coefficient is bounded by evaluation at one. -/
theorem coeff_le_eval_one (p : ℝ[X]) (hp : ∀ k, 0 ≤ p.coeff k) (k : ℕ) :
    p.coeff k ≤ p.eval 1 := by
  rw [eval_eq_sum_range]
  simp only [one_pow, mul_one]
  by_cases hk : k < p.natDegree + 1
  · exact Finset.single_le_sum (fun j _ => hp j) (mem_range.mpr hk)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact Finset.sum_nonneg (fun j _ => hp j)

/-- Explicit finite envelope: the network with every effective weight equal to one, at x=1. -/
@[expose] def networkEnvelope (r : ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => networkEnvelope r n + networkEnvelope r n ^ r

theorem networkEnvelope_one_le (r n : ℕ) : 1 ≤ networkEnvelope r n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [networkEnvelope]
    linarith [pow_nonneg (by linarith : 0 ≤ networkEnvelope r n) r]

/-- Uniform control of evaluation and of the residual by the sum of effective weights. -/
theorem network_eval_one_control (r n : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i < n, 0 ≤ u i ∧ u i ≤ 1) :
    1 ≤ (network r u n).eval 1 ∧
    (network r u n).eval 1 ≤ networkEnvelope r n ∧
    (network r u n).eval 1 - 1 ≤ networkEnvelope r n * ∑ i ∈ range n, u i := by
  induction n with
  | zero => simp [network, networkEnvelope]
  | succ n ih =>
    obtain ⟨ha, hab, hd⟩ := ih (fun i hi => hu i (by omega))
    obtain ⟨hun, hu1⟩ := hu n (by omega)
    have hb := networkEnvelope_one_le r n
    have hp : 0 ≤ (network r u n).eval 1 ^ r := pow_nonneg (by linarith) r
    have hpow : (network r u n).eval 1 ^ r ≤ networkEnvelope r n ^ r :=
      pow_le_pow_left₀ (by linarith) hab r
    have hm : u n * (network r u n).eval 1 ^ r ≤ networkEnvelope r n ^ r :=
      (mul_le_mul_of_nonneg_left hpow hun).trans (by nlinarith [pow_nonneg (by linarith : 0 ≤ networkEnvelope r n) r])
    have hsum : 0 ≤ ∑ i ∈ range n, u i := Finset.sum_nonneg (fun i hi => (hu i (by have := mem_range.mp hi; omega)).1)
    rw [eval_network_succ, networkEnvelope, sum_range_succ]
    refine ⟨by nlinarith [mul_nonneg hun hp], by linarith, ?_⟩
    have hterm := mul_le_mul_of_nonneg_left hpow hun
    have hcross1 := mul_nonneg (pow_nonneg (by linarith : 0 ≤ networkEnvelope r n) r) hsum
    have hcross2 := mul_nonneg (by linarith : 0 ≤ networkEnvelope r n) hun
    nlinarith

/-- Every residual coefficient, including all higher coefficients, is uniformly O(Σuᵢ).
The envelope depends only on depth and degree. -/
theorem residual_coeff_uniform_bound (r n : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i < n, 0 ≤ u i ∧ u i ≤ 1) (k : ℕ) :
    0 ≤ (network r u n - X).coeff k ∧
      (network r u n - X).coeff k ≤ networkEnvelope r n * ∑ i ∈ range n, u i := by
  have hnon : ∀ j, 0 ≤ (network r u n - X).coeff j :=
    fun j => (network_residual_coeff_nonneg r n u (fun i hi => (hu i hi).1) j).2
  refine ⟨hnon k, (coeff_le_eval_one _ hnon k).trans ?_⟩
  simpa only [eval_sub, eval_X] using (network_eval_one_control r n u hu).2.2
end ResidualSLT
