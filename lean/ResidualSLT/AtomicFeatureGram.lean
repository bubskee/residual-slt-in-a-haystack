module
public import ResidualSLT.NetworkLoss
public import Mathlib.LinearAlgebra.Vandermonde

/-! Concrete nonvacuity witnesses for every finite shifted-monomial feature Gram.
Distinct nonzero atoms suffice; no numerical determinant oracle is used. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Matrix Finset

@[expose] def atomicInput {N : ℕ} (v : Fin N → ℝ) : Measure ℝ :=
  ∑ i, Measure.dirac (v i)

theorem atomicInput_integrable {N : ℕ} (v : Fin N → ℝ) (f : ℝ → ℝ) :
    Integrable f (atomicInput v) := by
  exact integrable_finsetSum_measure.mpr (fun i _ => integrable_dirac (by finiteness))

theorem atomicInput_integral {N : ℕ} (v : Fin N → ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂atomicInput v) = ∑ i, f (v i) := by
  unfold atomicInput
  rw [integral_finsetSum_measure (fun i _ => integrable_dirac (by finiteness))]
  simp

/-- A Vandermonde argument proves positive definiteness for any finite shifted-power basis. -/
theorem atomic_shiftedPower_gram (r N : ℕ) (v : Fin N → ℝ)
    (hv : Function.Injective v) (hne : ∀ i, v i ≠ 0) :
    FinitePositiveFeatureGram (atomicInput v) (fun j : Fin N => fun x : ℝ => x ^ (r + j.val)) := by
  let φ : Fin N → ℝ → ℝ := fun j x => x ^ (r + j.val)
  have hi : ∀ i j, Integrable (fun x => φ i x * φ j x) (atomicInput v) :=
    fun i j => atomicInput_integrable v _
  refine ⟨hi, ?_⟩
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp [featureGram, Matrix.conjTranspose_apply, mul_comm]
  · intro c hc
    have heq : gramValue (featureGram (atomicInput v) φ) c =
        ∑ k, (∑ j, c j * v k ^ (r + j.val)) ^ 2 := by
      rw [← feature_integral_eq_gram (atomicInput v) φ hi c, atomicInput_integral]
    have hpos : 0 < gramValue (featureGram (atomicInput v) φ) c := by
      rw [heq]
      by_contra hn
      have hzero : (∑ k, (∑ j, c j * v k ^ (r + j.val)) ^ 2) = 0 :=
        le_antisymm (not_lt.mp hn) (Finset.sum_nonneg (fun k _ => sq_nonneg _))
      have hz : ∀ k, (∑ j, c j * v k ^ (r + j.val)) = 0 := by
        intro k
        have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg
          (∑ j, c j * v k ^ (r + j.val)))).mp hzero k (mem_univ k)
        exact eq_zero_of_pow_eq_zero hk
      apply hc
      apply Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero hv
      intro k
      have hmul : v k ^ r * (∑ j, c j * v k ^ j.val) = 0 := by
        simpa [pow_add, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hz k
      exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero r (hne k))
    simpa [gramValue, dotProduct, mulVec, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm, φ] using hpos

/-- An explicit admissible input exists at every degree and positive depth: atoms 1,...,N. -/
theorem network_atomic_gram (r L : ℕ) :
    FinitePositiveFeatureGram
      (atomicInput (fun i : Fin (networkFeatureCount r L) => (i.val : ℝ) + 1))
      (networkFeatures r L) := by
  apply atomic_shiftedPower_gram
  · intro i j hij
    apply Fin.ext
    exact_mod_cast (add_right_cancel hij)
  · intro i
    positivity
end ResidualSLT
