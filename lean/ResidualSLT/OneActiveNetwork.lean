module
public import ResidualSLT.SparseNetworkFeatures
public import ResidualSLT.OneActiveDirections

/-! Actual target loss, its sparse Gram representation, and chronological composition. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset MeasureTheory

/-- Agreement of effective coefficients up to the depth determines the output. -/
theorem network_congr_prefix {R : Type*} [CommRing R] (r n : ℕ) (u v : ℕ → R)
    (h : ∀ i < n, u i = v i) : network r u n = network r v n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [network,network,ih (fun i hi => h i (by omega)),h n (by omega)]

/-- Exact chronological concatenation, including either empty group. -/
theorem network_add_depth {R : Type*} [CommRing R] (r p q : ℕ) (u : ℕ → R) :
    network r u (p+q) = (network r (fun i => u (p+i)) q).comp (network r u p) := by
  induction q with
  | zero => simp [network]
  | succ q ih =>
    rw [show p+(q+1)=p+q+1 by omega,network,ih]
    simp [network,add_comp,mul_comp,pow_comp]

/-- A single active block with the exact before/after networks. -/
theorem network_one_active_split {R : Type*} [CommRing R] (r p q : ℕ) (u : ℕ → R) :
    network r u (p+1+q) = (network r (fun i => u (p+1+i)) q).comp
      ((X+C (u p)*X^r).comp (network r u p)) := by
  rw [network_add_depth,network]
  simp

@[expose] def oneActiveSquaredError (r : ℕ) (c : ℝ) {L : ℕ}
    (w : Fin L → ℝ) (x : ℝ) : ℝ :=
  ((network r (fun i => zeroExtend w i^r) L).eval x-(x+c*x^r))^2

@[expose] def oneActivePopulationLoss (μ : Measure ℝ) (r : ℕ) (c : ℝ) {L : ℕ}
    (w : Fin L → ℝ) : ℝ := ∫ x, oneActiveSquaredError r c w x ∂μ

@[expose] def oneActiveSparseCoefficients (r : ℕ) (c : ℝ) {L : ℕ}
    (w : Fin L → ℝ) (j : Fin (sparseNetworkFeatureCount r L)) : ℝ :=
  sparseNetworkCoefficients r w j - if j.val=0 then c else 0

/-- Target subtraction stays in exactly the same sparse feature space. -/
theorem oneActive_feature_expansion (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (c : ℝ) (w : Fin L → ℝ) (x : ℝ) :
    (network r (fun i => zeroExtend w i^r) L).eval x-(x+c*x^r) =
      ∑ j, oneActiveSparseCoefficients r c w j*sparseNetworkFeatures r L j x := by
  have hs : (∑ j : Fin (sparseNetworkFeatureCount r L),
      (if j.val=0 then c else 0)*sparseNetworkFeatures r L j x) = c*x^r := by
    rw [sum_eq_single ⟨0,sparseNetworkFeatureCount_pos r L hr hL⟩]
    · simp [sparseNetworkFeatures]
    · intro j _ hj
      have hj0 : j.val ≠ 0 := by intro hh; apply hj; exact Fin.ext hh
      simp [hj0]
    · simp
  simp only [oneActiveSparseCoefficients,sub_mul,sum_sub_distrib,hs]
  rw [← sparse_network_feature_expansion r L hr hL]
  ring

theorem oneActive_squaredError_integrable (μ : Measure ℝ) (r L : ℕ)
    (hr : 2 ≤ r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (c : ℝ) (w : Fin L → ℝ) :
    Integrable (oneActiveSquaredError r c w) μ := by
  unfold oneActiveSquaredError
  simp_rw [oneActive_feature_expansion r L hr hL]
  exact feature_square_integrable μ _ h.integrable _

theorem oneActive_loss_eq_gram (μ : Measure ℝ) (r L : ℕ)
    (hr : 2 ≤ r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (c : ℝ) (w : Fin L → ℝ) :
    oneActivePopulationLoss μ r c w =
      gramValue (featureGram μ (sparseNetworkFeatures r L)) (oneActiveSparseCoefficients r c w) := by
  simp only [oneActivePopulationLoss,oneActiveSquaredError,oneActive_feature_expansion r L hr hL]
  exact feature_integral_eq_gram μ _ h.integrable _

theorem oneActive_loss_coefficient_bounds (μ : Measure ℝ) (r L : ℕ)
    (hr : 2 ≤ r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ (c : ℝ) (w : Fin L → ℝ),
      a*‖oneActiveSparseCoefficients r c w‖^2 ≤ oneActivePopulationLoss μ r c w ∧
      oneActivePopulationLoss μ r c w ≤ A*‖oneActiveSparseCoefficients r c w‖^2 := by
  let : Nonempty (Fin (sparseNetworkFeatureCount r L)) := ⟨⟨0,sparseNetworkFeatureCount_pos r L hr hL⟩⟩
  obtain ⟨a,A,ha,hA,hb⟩ := gramValue_bounds _ h.positive
  exact ⟨a,A,ha,hA,fun c w => by rw [oneActive_loss_eq_gram μ r L hr hL h]; exact hb _⟩

end ResidualSLT
