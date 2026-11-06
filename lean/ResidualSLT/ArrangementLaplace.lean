module
public import ResidualSLT.ArrangementModelComparison

/-! Two-sided Laplace bounds for arbitrary active-block arrangements. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Filter Metric Set

theorem arrangementPopulationLoss_continuous (μ : Measure ℝ) (r k : ℕ) (hr : 2 ≤ r)
    (n : Fin (k+1) → ℕ) (hL : 0 < arrangementDepth k n k le_rfl)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r (arrangementDepth k n k le_rfl)))
    (τ : Fin k → ℝ) : Continuous (arrangementPopulationLoss μ r k n τ) :=
  (networkTargetLoss_continuous μ r _ hr hL hμ _).comp (arrangementFlatten_continuous k n τ k le_rfl)

theorem arrangementComparisonLoss_continuous (r k : ℕ) (n : Fin (k+1) → ℕ) (hr : 2 ≤ r) :
    Continuous (arrangementComparisonLoss r k n) := by
  have hg (g : Fin (k+1)) : Continuous (fun w : ArrangementAux k n => identityReferenceLoss r (n g) (w.2 g)) :=
    (identityReferenceLoss_continuous r (n g) hr).comp ((continuous_apply g).comp continuous_snd)
  unfold arrangementComparisonLoss
  exact (by fun_prop : Continuous (fun w : ArrangementAux k n => ∑ j,w.1 j^2)).add (continuous_finsetSum _ (fun g _ => hg g))

/-- A local loss comparison with the certified product model suffices, on every smaller
full product ball and with every bounded positive prior. -/
theorem arrangement_laplace_of_local_comparison (r k : ℕ) (n : Fin (k+1) → ℕ) (hr : 2 ≤ r)
    (K : ArrangementAux k n → ℝ) (hK : Continuous K)
    (hcomp : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ w in nhds 0,
      c*arrangementComparisonLoss r k n w ≤ K w ∧ K w ≤ C*arrangementComparisonLoss r k n w) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ ρ : ArrangementAux k n → NNReal, BoundedPositivePriorOn ρ (ball 0 ε) volume →
      HasLaplaceOrder (arrangementLearningPair r k n).1 (arrangementLearningPair r k n).2
        (fun N => ∫ w in ball 0 ε, Real.exp (-N*K w)
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  obtain ⟨c,C,hc,hC,hb⟩ := hcomp
  obtain ⟨δ,hδ,hb⟩ := Metric.eventually_nhds_iff_ball.mp hb
  refine ⟨min δ 1,lt_min hδ zero_lt_one,min_le_right _ _,?_⟩
  intro ε hε hεδ ρ hρ
  have hJ := arrangementComparisonLoss_continuous r k n hr
  have hiK (N : ℝ) : IntegrableOn (fun w => Real.exp (-N*K w)) (ball 0 ε) volume :=
    ((by fun_prop : Continuous (fun w => Real.exp (-N*K w))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall
  have hiJ (N : ℝ) : IntegrableOn (fun w => Real.exp (-N*arrangementComparisonLoss r k n w)) (ball 0 ε) volume :=
    ((by fun_prop : Continuous (fun w => Real.exp (-N*arrangementComparisonLoss r k n w))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall
  have hbound : ∀ᵐ w ∂(volume : Measure (ArrangementAux k n)).restrict (ball 0 ε),
      c*arrangementComparisonLoss r k n w ≤ K w ∧ K w ≤ C*arrangementComparisonLoss r k n w := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    exact hb w (ball_subset_ball (hεδ.trans (min_le_left _ _)) hw)
  have horder := laplace_pair_order_of_comparable volume (ball 0 ε)
    (arrangementComparisonLoss r k n) K hiJ hiK c C hc hC hbound
    (arrangementComparisonLoss_laplace_order r k hr n ε hε (hεδ.trans (min_le_right _ _)))
  exact laplace_pair_order_withDensity volume measurableSet_ball K hiK ρ hρ horder

/-- Actual squared-error population loss, for every finite active arrangement. -/
theorem arrangement_network_laplace_order (μ : Measure ℝ) (r k : ℕ) (hr : 2 ≤ r)
    (n : Fin (k+1) → ℕ) (hL : 0 < arrangementDepth k n k le_rfl)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r (arrangementDepth k n k le_rfl)))
    (τ : Fin k → ℝ) (hτ : ∀ j,τ j ≠ 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ ρ : ArrangementAux k n → NNReal, BoundedPositivePriorOn ρ (ball 0 ε) volume →
      HasLaplaceOrder (arrangementLearningPair r k n).1 (arrangementLearningPair r k n).2
        (fun N => ∫ w in ball 0 ε, Real.exp (-N*arrangementPopulationLoss μ r k n τ w)
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) :=
  arrangement_laplace_of_local_comparison r k n hr _
    (arrangementPopulationLoss_continuous μ r k hr n hL hμ τ)
    (arrangement_network_local_comparison μ r k hr n hL hμ τ hτ)

end ResidualSLT
