module
public import ResidualSLT.SparseNetworkFeatures
public import ResidualSLT.AtomicFeatureGram
public import ResidualSLT.LaplacePairTransfer

/-! The unified identity-target certificate under the sparse graded feature Gram.
The old theorem is preserved and used at a certified reference input measure;
coercivity on the actual coefficient space transfers its conclusions to the given input. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Metric

/-- Exact RLCT and Laplace multiplicity under the sparse Gram hypothesis.
The supplied input measure need not have a positive definite contiguous Gram. -/
theorem sparse_identity_network_rlct_laplace_certificate (μ : Measure ℝ)
    (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    (∀ s : ℝ, IntegrableOn (fun w => networkPopulationLoss μ r w^(-s)) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ENNReal))) ↔ s < (identityLearningPair r L).1) ∧
    HasLaplaceOrder (identityLearningPair r L).1 (identityLearningPair r L).2
      (fun N => ∫ w : Fin L → ℝ in ball 0 ε, Real.exp (-N*networkPopulationLoss μ r w)
        ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  let : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
  let ν := atomicInput (fun i : Fin (networkFeatureCount r L) => (i.val:ℝ)+1)
  have hν : FinitePositiveFeatureGram ν (networkFeatures r L) := network_atomic_gram r L
  have hsν := sparse_gram_of_contiguous ν r L hr hν
  have hbase := identity_network_rlct_laplace_certificate ν r L hr hL hν ε hε hε1 ρ hρ
  obtain ⟨c,C,hc,hC,hb⟩ := sparse_network_losses_comparable μ ν r L hr hL h hsν
  have hcK := networkPopulationLoss_continuous ν r hr L hL hν
  have hcJ := sparse_networkPopulationLoss_continuous μ r L hr hL h
  constructor
  · intro s
    rw [integrableOn_withDensity_iff_of_boundedPositive measurableSet_ball hρ]
    have hpos : ∀ᵐ w ∂volume.restrict (ball (0:Fin L → ℝ) ε), 0 < networkPopulationLoss ν r w := by
      filter_upwards [ae_restrict_mem measurableSet_ball,
        ae_restrict_of_ae ((volume : Measure (Fin L → ℝ)).ae_ne 0)] with w hw hne
      exact sparse_network_loss_pos ν r L hr hL hsν w (ball_subset_ball hε1 hw) hne
    rw [integrableOn_rpow_iff_of_comparable_all hcK.measurable.aemeasurable hcJ.measurable.aemeasurable
      hpos hc hC (Filter.Eventually.of_forall (fun w => (hb w).1))
      (Filter.Eventually.of_forall (fun w => (hb w).2)) s]
    rw [← integrableOn_withDensity_iff_of_boundedPositive measurableSet_ball hρ]
    exact hbase.1 s
  · apply laplace_pair_order_of_comparable (volume.withDensity (fun w => (ρ w : ENNReal))) (ball 0 ε)
      (networkPopulationLoss ν r) (networkPopulationLoss μ r)
      (fun N => (integrableOn_withDensity_iff_of_boundedPositive measurableSet_ball hρ).mpr
        (((by fun_prop : Continuous (fun w : Fin L → ℝ => Real.exp (-N*networkPopulationLoss ν r w))).continuousOn.integrableOn_compact
          (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall))
      (fun N => (integrableOn_withDensity_iff_of_boundedPositive measurableSet_ball hρ).mpr
        (((by fun_prop : Continuous (fun w : Fin L → ℝ => Real.exp (-N*networkPopulationLoss μ r w))).continuousOn.integrableOn_compact
          (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall))
      c C hc hC (Filter.Eventually.of_forall hb) hbase.2

/-- Expanded two-sided bounds with the unchanged unified learning pair. -/
theorem sparse_identity_network_laplace_bounds (μ : Measure ℝ)
    (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    ∃ c C N₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      c*(N^(-(identityLearningPair r L).1)*(Real.log N)^((identityLearningPair r L).2-1)) ≤
        (∫ w : Fin L → ℝ in ball 0 ε, Real.exp (-N*networkPopulationLoss μ r w)
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) ∧
      (∫ w : Fin L → ℝ in ball 0 ε, Real.exp (-N*networkPopulationLoss μ r w)
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) ≤
        C*(N^(-(identityLearningPair r L).1)*(Real.log N)^((identityLearningPair r L).2-1)) :=
  (sparse_identity_network_rlct_laplace_certificate μ r L hr hL h ε hε hε1 ρ hρ).2.2

theorem sparse_identity_network_prior_integrableOn_iff (μ : Measure ℝ)
    (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume)
    (s : ℝ) :
    IntegrableOn (fun w => networkPopulationLoss μ r w^(-s)) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ENNReal))) ↔ s < (identityLearningPair r L).1 :=
  (sparse_identity_network_rlct_laplace_certificate μ r L hr hL h ε hε hε1 ρ hρ).1 s

theorem sparse_identity_network_prior_not_integrable (μ : Measure ℝ)
    (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume)
    (s : ℝ) (hs : (identityLearningPair r L).1 ≤ s) :
    ¬ IntegrableOn (fun w => networkPopulationLoss μ r w^(-s)) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ENNReal))) := by
  rw [sparse_identity_network_prior_integrableOn_iff μ r L hr hL h ε hε hε1 ρ hρ s]
  exact not_lt.mpr hs

end ResidualSLT
