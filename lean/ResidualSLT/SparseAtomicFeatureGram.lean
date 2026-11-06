module
public import ResidualSLT.AtomicFeatureGram
public import ResidualSLT.SparseNetworkFeatures

/-! Sparse arithmetic-power Grams and a strict-weakening witness. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Matrix Finset

/-- Vandermonde positivity for an arithmetic progression of monomial degrees. -/
theorem atomic_arithmeticPower_gram (r d N : ℕ) (v : Fin N → ℝ)
    (hv : Function.Injective (fun i => v i ^ d)) (hne : ∀ i, v i ≠ 0) :
    FinitePositiveFeatureGram (atomicInput v)
      (fun j : Fin N => fun x : ℝ => x ^ (r + j.val * d)) := by
  let φ : Fin N → ℝ → ℝ := fun j x => x ^ (r + j.val * d)
  have hi : ∀ i j, Integrable (fun x => φ i x * φ j x) (atomicInput v) :=
    fun i j => atomicInput_integrable v _
  refine ⟨hi, ?_⟩
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp [featureGram, Matrix.conjTranspose_apply, mul_comm]
  · intro c hc
    have heq : gramValue (featureGram (atomicInput v) φ) c =
        ∑ k, (∑ j, c j * v k ^ (r + j.val * d)) ^ 2 := by
      rw [← feature_integral_eq_gram (atomicInput v) φ hi c, atomicInput_integral]
    have hpos : 0 < gramValue (featureGram (atomicInput v) φ) c := by
      rw [heq]
      by_contra hn
      have hzero : (∑ k, (∑ j, c j * v k ^ (r + j.val * d)) ^ 2) = 0 :=
        le_antisymm (not_lt.mp hn) (Finset.sum_nonneg (fun k _ => sq_nonneg _))
      have hz : ∀ k, (∑ j, c j * v k ^ (r + j.val * d)) = 0 := by
        intro k
        have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg
          (∑ j, c j * v k ^ (r + j.val * d)))).mp hzero k (mem_univ k)
        exact eq_zero_of_pow_eq_zero hk
      apply hc
      apply Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero hv
      intro k
      have hmul : v k ^ r * (∑ j, c j * (v k ^ d) ^ j.val) = 0 := by
        simpa [pow_add, ← pow_mul, Nat.mul_comm, Finset.mul_sum,
          mul_comm, mul_left_comm, mul_assoc] using hz k
      exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero r (hne k))
    simpa [gramValue, dotProduct, mulVec, Finset.mul_sum, mul_assoc,
      mul_comm, mul_left_comm, φ] using hpos

/-- The sparse Gram needs only as many positive atoms as retained features. -/
theorem network_atomic_sparse_gram (r L : ℕ) (hr : 2 ≤ r) :
    FinitePositiveFeatureGram
      (atomicInput (fun i : Fin (sparseNetworkFeatureCount r L) => (i.val : ℝ) + 1))
      (sparseNetworkFeatures r L) := by
  apply atomic_arithmeticPower_gram
  · intro i j hij
    have heq : (i.val : ℝ) + 1 = (j.val : ℝ) + 1 :=
      (pow_left_inj₀ (by positivity) (by positivity) (by omega : r-1 ≠ 0)).mp hij
    apply Fin.ext
    exact_mod_cast (add_right_cancel heq)
  · intro i
    positivity

/-- A concrete input satisfies the new hypothesis and fails the old one.
Its four atoms are 1,2,3,4; the sparse cubic depth-two features are x³,x⁵,x⁷,x⁹. -/
theorem sparse_gram_strictly_weaker_cubic_two :
    let μ := atomicInput (fun i : Fin 4 => (i.val : ℝ) + 1)
    FinitePositiveFeatureGram μ (sparseNetworkFeatures 3 2) ∧
      ¬ FinitePositiveFeatureGram μ (networkFeatures 3 2) := by
  dsimp only
  constructor
  · exact network_atomic_sparse_gram 3 2 (by norm_num)
  · intro h
    let c : Fin 7 → ℝ := ![24,-50,35,-10,1,0,0]
    have hc : c ≠ 0 := by
      intro hz
      have hz0 := congrFun hz 0
      norm_num [c] at hz0
    have hp := gramValue_pos _ h.positive c hc
    rw [← feature_integral_eq_gram _ _ h.integrable c, atomicInput_integral] at hp
    change 0 < ∑ k : Fin 4, (∑ j : Fin 7, c j * ((k.val : ℝ)+1)^(3+j.val))^2 at hp
    norm_num [c, Fin.sum_univ_succ] at hp

end ResidualSLT
