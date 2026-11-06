module
public import ResidualSLT.ArrangementRawCertificate
public import ResidualSLT.SparseIdentityCertificate

/-! Unified local arrangement theorem, including the preserved identity-target case. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Metric Set Finset

theorem networkTargetLoss_zero_target (μ : Measure ℝ) (r L : ℕ) (hr : 0 < r) (w : Fin L → ℝ) :
    networkTargetLoss μ r 0 w = networkPopulationLoss μ r w := by
  have hz : (fun i => zeroExtend (0 : Fin L → ℝ) i^r) = fun _ => (0:ℝ) := by
    funext i
    simp [zeroExtend,hr.ne']
  simp only [networkTargetLoss,hz,network_zero_weights,Polynomial.eval_X,networkPopulationLoss,networkSquaredError]

theorem arrangementLearningPair_zero (r : ℕ) (n : Fin 1 → ℕ) :
    arrangementLearningPair r 0 n = identityLearningPair r (n 0) := by
  have hm : 0 < (identityLearningPair r (n 0)).2 := by
    unfold identityLearningPair
    split_ifs <;> norm_num
  apply Prod.ext
  · simp [arrangementLearningPair]
  · simp only [arrangementLearningPair,Nat.reduceAdd,Fin.sum_univ_one]
    omega

/-- Unified arbitrary-active certificate: all active counts k≥0, positive total depth,
all degrees r≥2, every nonzero active value, all inactive group sizes and bounded positive
local priors. The loss and measure are on the original ordered raw-weight space. -/
theorem arrangement_raw_network_rlct_laplace_certificate_of_depth_pos
    (μ : Measure ℝ) (r k : ℕ) (hr : 2 ≤ r) (n : Fin (k+1) → ℕ)
    (hL : 0 < arrangementDepth k n k le_rfl)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r (arrangementDepth k n k le_rfl)))
    (τ : Fin k → ℝ) (hτ : ∀ j,τ j ≠ 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ ρ : (Fin (arrangementDepth k n k le_rfl) → ℝ) → NNReal,
        BoundedPositivePriorOn ρ (ball (arrangementFlatten k n τ 0 k le_rfl) ε) volume →
      (∀ s : ℝ, IntegrableOn (fun w => (networkTargetLoss μ r (arrangementFlatten k n τ 0 k le_rfl) w)^(-s))
        (ball (arrangementFlatten k n τ 0 k le_rfl) ε) (volume.withDensity (fun w => (ρ w : ENNReal))) ↔
          s < (arrangementLearningPair r k n).1) ∧
      HasLaplaceOrder (arrangementLearningPair r k n).1 (arrangementLearningPair r k n).2
        (fun N => ∫ w in ball (arrangementFlatten k n τ 0 k le_rfl) ε,
          Real.exp (-N*networkTargetLoss μ r (arrangementFlatten k n τ 0 k le_rfl) w)
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  by_cases hk : 0 < k
  · exact arrangement_raw_network_rlct_laplace_certificate μ r k hr hk n hμ τ hτ
  have hk0 : k = 0 := by omega
  subst k
  have ht : arrangementFlatten 0 n τ 0 0 le_rfl = 0 := rfl
  simp only [ht,arrangementLearningPair_zero,networkTargetLoss_zero_target μ r _ (by omega)]
  refine ⟨1,zero_lt_one,le_rfl,?_⟩
  intro ε hε hε1 ρ hρ
  exact sparse_identity_network_rlct_laplace_certificate μ r (n 0) hr hL hμ ε hε hε1 ρ hρ

/-- Endpoint divergence in the original raw-weight neighborhood. -/
theorem arrangement_raw_network_boundary_divergence (μ : Measure ℝ) (r k : ℕ) (hr : 2 ≤ r)
    (n : Fin (k+1) → ℕ) (hL : 0 < arrangementDepth k n k le_rfl)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r (arrangementDepth k n k le_rfl)))
    (τ : Fin k → ℝ) (hτ : ∀ j,τ j ≠ 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ ρ : (Fin (arrangementDepth k n k le_rfl) → ℝ) → NNReal,
        BoundedPositivePriorOn ρ (ball (arrangementFlatten k n τ 0 k le_rfl) ε) volume →
      ¬ IntegrableOn (fun w => (networkTargetLoss μ r (arrangementFlatten k n τ 0 k le_rfl) w)^(-(arrangementLearningPair r k n).1))
        (ball (arrangementFlatten k n τ 0 k le_rfl) ε) (volume.withDensity (fun w => (ρ w : ENNReal))) := by
  obtain ⟨ε₀,hε₀,hε₀1,hcert⟩ := arrangement_raw_network_rlct_laplace_certificate_of_depth_pos μ r k hr n hL hμ τ hτ
  refine ⟨ε₀,hε₀,hε₀1,?_⟩
  intro ε hε hεsmall ρ hρ
  rw [(hcert ε hε hεsmall ρ hρ).1]
  exact lt_irrefl _

/-- For odd degree, each and only each critical group contributes one logarithmic factor. -/
theorem arrangementLearningPair_odd_multiplicity (r k : ℕ) (n : Fin (k+1) → ℕ) (hodd : Odd r) :
    (arrangementLearningPair r k n).2 = 1+(univ.filter (fun g => n g = r)).card := by
  classical
  have hh (g : Fin (k+1)) : (identityLearningPair r (n g)).2-1 = if n g = r then 1 else 0 := by
    by_cases he : n g = r
    · simp [identityLearningPair,Nat.not_even_iff_odd.mpr hodd,he]
    · by_cases hl : n g < r <;> simp [identityLearningPair,Nat.not_even_iff_odd.mpr hodd,he,hl]
  simp [arrangementLearningPair,hh]

/-- Even degree has no logarithm, irrespective of the arrangement. -/
theorem arrangementLearningPair_even (r k : ℕ) (n : Fin (k+1) → ℕ) (heven : Even r) :
    arrangementLearningPair r k n = ((k:ℝ)/2+(∑ g,(n g:ℝ))/(2*r),1) := by
  simp [arrangementLearningPair,identityLearningPair_even r _ heven,Finset.sum_div]

/-- The arbitrary-active pair specializes exactly to the preserved one-active pair. -/
theorem arrangementLearningPair_one (r p q : ℕ) :
    arrangementLearningPair r 1 ![p,q] = oneActiveLearningPair r p q := by
  have hp : 0 < (identityLearningPair r p).2 := by
    unfold identityLearningPair
    split_ifs <;> norm_num
  have hq : 0 < (identityLearningPair r q).2 := by
    unfold identityLearningPair
    split_ifs <;> norm_num
  apply Prod.ext
  · simp [arrangementLearningPair,oneActiveLearningPair,Fin.sum_univ_two,add_assoc]
  · simp only [arrangementLearningPair,oneActiveLearningPair,Nat.reduceAdd,Fin.sum_univ_two,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    omega

end ResidualSLT
