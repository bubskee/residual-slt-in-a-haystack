module
public import ResidualSLT.SparseAtomicFeatureGram

/-! More input observations than features preserve sparse Gram positivity. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Matrix Finset

theorem atomic_arithmeticPower_gram_embedded (r d N M : ℕ) (v : Fin M → ℝ)
    (e : Fin N → Fin M) (hv : Function.Injective (fun i => v (e i) ^ d))
    (hne : ∀ i, v (e i) ≠ 0) :
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
      have hmul : v (e k) ^ r * (∑ j, c j * (v (e k) ^ d) ^ j.val) = 0 := by
        simpa [pow_add, ← pow_mul, Nat.mul_comm, Finset.mul_sum,
          mul_comm, mul_left_comm, mul_assoc] using hz (e k)
      exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero r (hne k))
    simpa [gramValue, dotProduct, mulVec, Finset.mul_sum, mul_assoc,
      mul_comm, mul_left_comm, φ] using hpos


/-- Any sufficiently long positive integer observation grid has the required sparse Gram. -/
theorem network_sparse_gram_many_atoms (r L M : ℕ) (hr : 2 ≤ r)
    (hM : sparseNetworkFeatureCount r L ≤ M) :
    FinitePositiveFeatureGram (atomicInput (fun i : Fin M => (i.val:ℝ)+1))
      (sparseNetworkFeatures r L) := by
  let e : Fin (sparseNetworkFeatureCount r L) → Fin M := fun i => ⟨i.val,i.isLt.trans_le hM⟩
  apply atomic_arithmeticPower_gram_embedded r (r-1) _ M _ e
  · intro i j hij
    have heq : (i.val:ℝ)+1=(j.val:ℝ)+1 :=
      (pow_left_inj₀ (by positivity) (by positivity) (by omega : r-1 ≠ 0)).mp hij
    apply Fin.ext
    exact_mod_cast add_right_cancel heq
  · intro i
    positivity

end ResidualSLT
