module
public import ResidualSLT.RawArrangementDecomposition

/-! Global RLCT and Laplace multiplicity for every realized target, at arbitrary active count. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial MeasureTheory Metric Set Filter

/-- Nonzero effective powers count exactly the nonzero raw weights. -/
theorem raw_activeCount_eq (r L : ℕ) (hr : 0<r) (t : Fin L → ℝ) :
    activeCount (fun i => zeroExtend t i^r) L=activeCount (zeroExtend t) L := by
  unfold activeCount
  congr 1
  apply Finset.filter_congr
  intro i _
  exact not_congr (pow_eq_zero_iff hr.ne')

/-- Every realized population-loss zero fiber is finite under the positive sparse Gram. -/
theorem networkTargetLoss_fiber_finite (μ : Measure ℝ) (r L : ℕ) (hr : 2≤r) (hL : 0<L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (t : Fin L → ℝ) :
    {w : Fin L → ℝ | networkTargetLoss μ r t w=0}.Finite := by
  apply (network_full_raw_fiber_finite r L L hr t).subset
  intro w hw
  exact (networkTargetLoss_eq_zero_iff μ r L hr hL hμ t w).mp hw

/-- The finite-fiber assembly now applies to every raw target, including zero active blocks. -/
theorem arbitrary_active_global_network_laplace (μ : Measure ℝ) (r L k : ℕ)
    (hr : 2≤r) (hL : 0<L) (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (t : Fin L → ℝ) (hk : activeCount (fun i => zeroExtend t i^r) L=k)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : Measurable ρ)
    (hfinite : (∫⁻ w,(ρ w:ENNReal) ∂volume)<⊤)
    (hprior : ∀ w,networkTargetLoss μ r t w=0 → ContinuousAt ρ w ∧ 0<ρ w) :
    HasLaplaceOrder (globalLearningPair r k (L-k)).1 (globalLearningPair r k (L-k)).2
      (fun N => ∫ w,Real.exp (-N*networkTargetLoss μ r t w)
        ∂volume.withDensity (fun w => (ρ w:ENNReal))) := by
  have hkL : k≤L := hk ▸ activeCount_le (fun i => zeroExtend t i^r) L
  apply finite_arrangement_fiber_global_laplace μ r L k hr hL hkL hμ t
    (networkTargetLoss_fiber_finite μ r L hr hL hμ t) _ ρ hρ hfinite hprior
  intro w hw
  apply raw_vector_arrangement_of_activeCount r L k hr w
  exact (network_eq_activeCount r L L hr _ _
    ((networkTargetLoss_eq_zero_iff μ r L hr hL hμ t w).mp hw)).trans hk

/-- Every degree r≥2 and positive depth, with arbitrary target active count:
full-space inverse-power threshold and the exact two-sided power/logarithmic Laplace order. -/
theorem arbitrary_active_global_rlct_laplace_certificate (μ : Measure ℝ) (r L k : ℕ)
    (hr : 2≤r) (hL : 0<L) (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (t : Fin L → ℝ) (hk : activeCount (fun i => zeroExtend t i^r) L=k)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : Measurable ρ)
    (hfinite : (∫⁻ w,(ρ w:ENNReal) ∂volume)<⊤)
    (hprior : ∀ w,networkTargetLoss μ r t w=0 → ContinuousAt ρ w ∧ 0<ρ w) :
    (∀ s : ℝ,0<s → (Integrable (fun w => (networkTargetLoss μ r t w)^(-s))
      (volume.withDensity (fun w => (ρ w:ENNReal))) ↔ s<(globalLearningPair r k (L-k)).1)) ∧
    HasLaplaceOrder (globalLearningPair r k (L-k)).1 (globalLearningPair r k (L-k)).2
      (fun N => ∫ w,Real.exp (-N*networkTargetLoss μ r t w)
        ∂volume.withDensity (fun w => (ρ w:ENNReal))) := by
  have ho := arbitrary_active_global_network_laplace μ r L k hr hL hμ t hk ρ hρ hfinite hprior
  exact ⟨fun s hs => network_global_inversePower_iff μ r L hr hL hμ t
    (networkTargetLoss_fiber_finite μ r L hr hL hμ t) ρ hfinite _ _ ho s hs,ho⟩

theorem globalLearningPair_pos_of_depth (r L k : ℕ) (hr : 2≤r) (hL : 0<L) :
    0<(globalLearningPair r k (L-k)).1 := by
  by_cases hk : k=0
  · have hp : 0<(identityLearningPair r L).1 := by
      unfold identityLearningPair
      split_ifs <;> dsimp <;> positivity
    simpa [globalLearningPair,hk] using hp
  · exact globalLearningPair_pos r k (L-k) (by omega)

/-- Explicit divergence at the global threshold, including identity targets. -/
theorem arbitrary_active_global_boundary_diverges (μ : Measure ℝ) (r L k : ℕ)
    (hr : 2≤r) (hL : 0<L) (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (t : Fin L → ℝ) (hk : activeCount (fun i => zeroExtend t i^r) L=k)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : Measurable ρ)
    (hfinite : (∫⁻ w,(ρ w:ENNReal) ∂volume)<⊤)
    (hprior : ∀ w,networkTargetLoss μ r t w=0 → ContinuousAt ρ w ∧ 0<ρ w) :
    ¬Integrable (fun w => (networkTargetLoss μ r t w)^(-(globalLearningPair r k (L-k)).1))
      (volume.withDensity (fun w => (ρ w:ENNReal))) := by
  have hh := (arbitrary_active_global_rlct_laplace_certificate μ r L k hr hL hμ t hk ρ hρ hfinite hprior).1
  rw [hh _ (globalLearningPair_pos_of_depth r L k hr hL)]
  exact lt_irrefl _

end ResidualSLT
