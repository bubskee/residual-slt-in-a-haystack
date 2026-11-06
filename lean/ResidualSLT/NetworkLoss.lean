module
public import ResidualSLT.Degree
public import ResidualSLT.Coefficients
public import ResidualSLT.FeatureGram
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Actual arbitrary-depth population loss and its finite coefficient-Gram representation.
The feature basis is x^r,...,x^(r^L). All pairwise feature moments and positive definiteness
are explicit assumptions when the Gram representation is used analytically. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial MeasureTheory Finset

/-- Extend the finite raw-weight vector only to feed the existing chronological recursion. -/
@[expose] def zeroExtend {L : ℕ} (w : Fin L → ℝ) (i : ℕ) : ℝ :=
  if h : i < L then w ⟨i, h⟩ else 0

@[expose] def networkFeatureCount (r L : ℕ) : ℕ := r ^ L + 1 - r
@[expose] def networkFeatures (r L : ℕ) (j : Fin (networkFeatureCount r L)) (x : ℝ) : ℝ :=
  x ^ (r + j.val)
@[expose] def networkCoefficients (r : ℕ) {L : ℕ} (w : Fin L → ℝ)
    (j : Fin (networkFeatureCount r L)) : ℝ :=
  (network r (fun i => zeroExtend w i ^ r) L - X).coeff (r + j.val)
@[expose] def networkSquaredError (r : ℕ) {L : ℕ} (w : Fin L → ℝ) (x : ℝ) : ℝ :=
  ((network r (fun i => zeroExtend w i ^ r) L).eval x - x) ^ 2
@[expose] def networkPopulationLoss (μ : Measure ℝ) (r : ℕ) {L : ℕ} (w : Fin L → ℝ) : ℝ :=
  ∫ x, networkSquaredError r w x ∂μ
@[expose] def weightPowerSum (r : ℕ) {L : ℕ} (w : Fin L → ℝ) : ℝ := ∑ i, w i ^ r

/-- Evaluation is exactly the raw-weight residual recursion hₙ₊₁=hₙ+(wₙhₙ)^r. -/
theorem network_raw_step (r L n : ℕ) (w : Fin L → ℝ) (x : ℝ) :
    (network r (fun i => zeroExtend w i ^ r) (n + 1)).eval x =
      (network r (fun i => zeroExtend w i ^ r) n).eval x +
        (zeroExtend w n * (network r (fun i => zeroExtend w i ^ r) n).eval x) ^ r := by
  simp [network, mul_pow]

/-- The feature basis is nonempty for every positive depth. -/
theorem networkFeatureCount_pos (r L : ℕ) (hL : 0 < L) : 0 < networkFeatureCount r L := by
  have := Nat.le_pow (a := r) hL
  unfold networkFeatureCount
  omega

/-- Every residual term is divisible by X^r; no irrelevant lower features are introduced. -/
theorem network_residual_X_pow_dvd (r : ℕ) (hr : 1 ≤ r) (u : ℕ → ℝ) (L : ℕ) :
    X ^ r ∣ network r u L - X := by
  induction L with
  | zero => simp [network]
  | succ L ih =>
    have hx : X ∣ network r u L := by
      rw [network_eq_graded r hr]
      exact dvd_mul_right _ _
    have ht : X ^ r ∣ C (u L) * network r u L ^ r :=
      dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hx r) _
    convert dvd_add ih ht using 1; rw [network]; ring

/-- Exact finite feature expansion of the residual, valid for every raw-weight sign. -/
theorem network_feature_expansion (r : ℕ) (hr : 2 ≤ r) (L : ℕ) (hL : 0 < L)
    (u : ℕ → ℝ) (x : ℝ) :
    (network r u L).eval x - x =
      ∑ j : Fin (networkFeatureCount r L), (network r u L - X).coeff (r + j.val) *
        networkFeatures r L j x := by
  let p := network r u L - X
  have hlow : ∀ k < r, p.coeff k = 0 :=
    X_pow_dvd_iff.mp (network_residual_X_pow_dvd r (by omega) u L)
  have hdeg : p.natDegree < r ^ L + 1 := by
    have hbound := natDegree_sub_le (network r u L) X
    have hn := network_natDegree_le r hr u L
    have hd := Nat.le_pow (a := r) hL
    simp only [natDegree_X] at hbound
    dsimp [p]
    omega
  have hsplit : r ^ L + 1 = r + networkFeatureCount r L := by
    have := Nat.le_pow (a := r) hL
    unfold networkFeatureCount
    omega
  have heval : p.eval x = (network r u L).eval x - x := by simp [p]
  rw [← heval]
  rw [eval_eq_sum_range' hdeg, hsplit, Finset.sum_range_add]
  have hz : (∑ k ∈ range r, p.coeff k * x ^ k) = 0 :=
    Finset.sum_eq_zero (fun k hk => by rw [hlow k (mem_range.mp hk), zero_mul])
  rw [hz, zero_add, ← Fin.sum_univ_eq_sum_range]
  rfl

theorem network_squaredError_eq (r : ℕ) (hr : 2 ≤ r) (L : ℕ) (hL : 0 < L)
    (w : Fin L → ℝ) (x : ℝ) :
    networkSquaredError r w x =
      (∑ j, networkCoefficients r w j * networkFeatures r L j x) ^ 2 := by
  unfold networkSquaredError networkCoefficients
  rw [network_feature_expansion r hr L hL]

/-- Finiteness is established separately from the totalized integral identity. -/
theorem network_squaredError_integrable (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r)
    (L : ℕ) (hL : 0 < L) (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (w : Fin L → ℝ) : Integrable (networkSquaredError r w) μ := by
  change Integrable (fun x => networkSquaredError r w x) μ
  simp_rw [network_squaredError_eq r hr L hL]
  exact feature_square_integrable μ _ h.integrable _

/-- Actual population loss as its coefficient Gram form at arbitrary finite depth. -/
theorem network_loss_eq_gram (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r)
    (L : ℕ) (hL : 0 < L) (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (w : Fin L → ℝ) :
    networkPopulationLoss μ r w = gramValue (featureGram μ (networkFeatures r L)) (networkCoefficients r w) := by
  simp only [networkPopulationLoss, network_squaredError_eq r hr L hL]
  exact feature_integral_eq_gram μ _ h.integrable _

/-- The leading residual coefficient is the raw-weight power sum. -/
theorem networkCoefficients_first (r : ℕ) (hr : 2 ≤ r) (L : ℕ) (hL : 0 < L)
    (w : Fin L → ℝ) :
    networkCoefficients r w ⟨0, networkFeatureCount_pos r L hL⟩ = weightPowerSum r w := by
  simp only [networkCoefficients, Nat.add_zero]
  rw [(raw_residual_coefficients r hr (zeroExtend w) L).1,
    ← Fin.sum_univ_eq_sum_range]
  simp [zeroExtend, weightPowerSum]

/-- Finite coefficient convolution preserves continuity, without a polynomial topology. -/
theorem continuous_coeff_pow {A : Type*} [TopologicalSpace A] (p : A → ℝ[X])
    (hp : ∀ k, Continuous (fun w => (p w).coeff k)) (m k : ℕ) :
    Continuous (fun w => ((p w) ^ m).coeff k) := by
  induction m generalizing k with
  | zero => simp only [pow_zero]; exact continuous_const
  | succ m ih =>
    simp only [pow_succ, coeff_mul]
    exact continuous_finsetSum _ (fun ij _ => (ih ij.1).mul (hp ij.2))

theorem network_coeff_continuous {A : Type*} [TopologicalSpace A] (r L : ℕ)
    (u : ℕ → A → ℝ) (hu : ∀ i, Continuous (u i)) (k : ℕ) :
    Continuous (fun w => (network r (fun i => u i w) L).coeff k) := by
  induction L generalizing k with
  | zero => simp only [network]; exact continuous_const
  | succ L ih =>
    simp only [network, coeff_add, coeff_C_mul]
    exact (ih k).add ((hu L).mul (continuous_coeff_pow _ ih r k))

theorem networkCoefficients_continuous (r L : ℕ) :
    Continuous (@networkCoefficients r L) := by
  apply continuous_pi_iff.mpr
  intro j
  unfold networkCoefficients
  simp only [coeff_sub]
  apply Continuous.sub _ continuous_const
  apply network_coeff_continuous
  intro i
  unfold zeroExtend
  by_cases hi : i < L
  · simp only [dite_eq_left hi]
    fun_prop
  · simp only [dite_eq_right hi]
    exact continuous_const

theorem networkPopulationLoss_continuous (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r)
    (L : ℕ) (hL : 0 < L) (h : FinitePositiveFeatureGram μ (networkFeatures r L)) :
    Continuous (@networkPopulationLoss μ r L) := by
  have heq := funext (network_loss_eq_gram μ r hr L hL h)
  rw [heq]
  exact (gramValue_continuous _).comp (networkCoefficients_continuous r L)
end ResidualSLT
