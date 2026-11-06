module
public import ResidualSLT.RadialThreshold
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Finite feature Gram representation, input integrability, and derived coercive bounds. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Finset Matrix
variable {ι : Type*} [Fintype ι]

@[expose] def featureGram (μ : Measure ℝ) (φ : ι → ℝ → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∫ x, φ i x * φ j x ∂μ

@[expose] def gramValue (G : Matrix ι ι ℝ) (c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * G i j

/-- These assumptions concern input moments and a standard positive-definite matrix,
not a comparison estimate or an integrability threshold. -/
structure FinitePositiveFeatureGram (μ : Measure ℝ) (φ : ι → ℝ → ℝ) : Prop where
  integrable : ∀ i j, Integrable (fun x => φ i x * φ j x) μ
  positive : (featureGram μ φ).PosDef

theorem feature_square_expansion (φ : ι → ℝ → ℝ) (c : ι → ℝ) (x : ℝ) :
    (∑ i, c i * φ i x) ^ 2 = ∑ i, ∑ j, c i * c j * (φ i x * φ j x) := by
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem feature_square_integrable (μ : Measure ℝ) (φ : ι → ℝ → ℝ)
    (h : ∀ i j, Integrable (fun x => φ i x * φ j x) μ) (c : ι → ℝ) :
    Integrable (fun x => (∑ i, c i * φ i x) ^ 2) μ := by
  simp_rw [feature_square_expansion]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (h i j).const_mul (c i * c j)

theorem feature_integral_eq_gram (μ : Measure ℝ) (φ : ι → ℝ → ℝ)
    (h : ∀ i j, Integrable (fun x => φ i x * φ j x) μ) (c : ι → ℝ) :
    (∫ x, (∑ i, c i * φ i x) ^ 2 ∂μ) = gramValue (featureGram μ φ) c := by
  simp_rw [feature_square_expansion]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (h i j).const_mul (c i * c j)))]
  unfold gramValue featureGram
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (h i j).const_mul (c i * c j))]
  simp_rw [integral_const_mul]

theorem gramValue_continuous (G : Matrix ι ι ℝ) : Continuous (gramValue G) := by
  unfold gramValue
  fun_prop

theorem gramValue_smul (G : Matrix ι ι ℝ) (a : ℝ) (c : ι → ℝ) :
    gramValue G (a • c) = a ^ 2 * gramValue G c := by
  simp only [gramValue, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem gramValue_pos (G : Matrix ι ι ℝ) (hG : G.PosDef) (c : ι → ℝ) (hc : c ≠ 0) :
    0 < gramValue G c := by
  have h := hG.dotProduct_mulVec_pos hc
  simpa [gramValue, dotProduct, mulVec, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h

/-- Positive definiteness yields uniform bounds, by compactness of the unit sphere. -/
theorem gramValue_bounds [Nonempty ι] (G : Matrix ι ι ℝ) (hG : G.PosDef) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ v, c * ‖v‖ ^ 2 ≤ gramValue G v ∧ gramValue G v ≤ C * ‖v‖ ^ 2 := by
  exact positive_homogeneous_bounds 2 (by omega) (gramValue_continuous G)
    (gramValue_pos G hG) (fun a _ v => gramValue_smul G a v)
end ResidualSLT
