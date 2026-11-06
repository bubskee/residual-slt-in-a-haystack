module
public import ResidualSLT.NetworkLocalCertificate

/-! One end-to-end certificate for full raw fibers, exact counts, and local/global
RLCT and Laplace multiplicity of every realized scalar residual-network target. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial MeasureTheory Metric Set

/-- Named conclusions of the unified theorem. Local statements use actual reconstructed
raw arrangements; all analytic fields use the same fixed population loss and prior. -/
structure UnifiedNetworkCertificate (μ : Measure ℝ) (r L k : ℕ)
    (t : Fin L → ℝ) (ρ : (Fin L → ℝ) → NNReal) : Prop where
  active_count_le : k≤L
  loss_fiber : {w : Fin L → ℝ | networkTargetLoss μ r t w=0}=rawNetworkFiber r L L t
  ordered_fiber : ∀ w : Fin L → ℝ,networkTargetLoss μ r t w=0 ↔
    activeWord (fun i => zeroExtend w i^r) L=activeWord (fun i => zeroExtend t i^r) L
  odd_fiber : Odd r → ∀ w : Fin L → ℝ,networkTargetLoss μ r t w=0 ↔
    activeWord (zeroExtend w) L=activeWord (zeroExtend t) L
  even_fiber : Even r → ∀ w : Fin L → ℝ,networkTargetLoss μ r t w=0 ↔
    (activeWord (zeroExtend w) L).map abs=(activeWord (zeroExtend t) L).map abs
  finite_fiber : (rawNetworkFiber r L L t).Finite
  fiber_cardinality : (rawNetworkFiber r L L t).ncard=(if Even r then 2^k else 1)*L.choose k
  local_certificates : ∀ x : Fin L → ℝ,networkTargetLoss μ r t x=0 →
    ∃ n : Fin (k+1) → ℕ,∃ τ : Fin k → ℝ,(∀ j,τ j≠0) ∧ (∑ g,n g)=L-k ∧
      ∃ hd : arrangementDepth k n k le_rfl=L,
        (∀ i : Fin (arrangementDepth k n k le_rfl),x (Fin.cast hd i)=arrangementFlatten k n τ 0 k le_rfl i) ∧
        LocalNetworkCertificate μ r t x ρ (arrangementLearningPair r k n)
  local_at_arrangement : ∀ (x : Fin L → ℝ),networkTargetLoss μ r t x=0 →
    ∀ (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ),(∀ j,τ j≠0) →
      ∀ hd : arrangementDepth k n k le_rfl=L,
        (∀ i : Fin (arrangementDepth k n k le_rfl),x (Fin.cast hd i)=arrangementFlatten k n τ 0 k le_rfl i) →
        LocalNetworkCertificate μ r t x ρ (arrangementLearningPair r k n)
  global_dominance : ∀ n : Fin (k+1) → ℕ,(∑ g,n g)=L-k →
    (globalLearningPair r k (L-k)).1≤(arrangementLearningPair r k n).1 ∧
    ((arrangementLearningPair r k n).1=(globalLearningPair r k (L-k)).1 →
      (arrangementLearningPair r k n).2≤(globalLearningPair r k (L-k)).2)
  global_attained : ∃ x : Fin L → ℝ,networkTargetLoss μ r t x=0 ∧
    LocalNetworkCertificate μ r t x ρ (globalLearningPair r k (L-k))
  global_integrability : ∀ s : ℝ,0<s →
    (Integrable (fun w => (networkTargetLoss μ r t w)^(-s))
      (volume.withDensity (fun w => (ρ w:ENNReal))) ↔ s<(globalLearningPair r k (L-k)).1)
  global_boundary : ¬Integrable (fun w => (networkTargetLoss μ r t w)^(-(globalLearningPair r k (L-k)).1))
    (volume.withDensity (fun w => (ρ w:ENNReal)))
  global_laplace : HasLaplaceOrder (globalLearningPair r k (L-k)).1 (globalLearningPair r k (L-k)).2
    (fun N => ∫ w,Real.exp (-N*networkTargetLoss μ r t w)
      ∂volume.withDensity (fun w => (ρ w:ENNReal)))

/-- Unified actual-network theorem. All degrees r≥2, positive depths, all active counts
including zero, and arbitrary raw target values. No genericity assumptions. The prior is
measurable with finite mass and continuous and positive at every point of the full fiber. -/
theorem unified_residual_network_certificate (μ : Measure ℝ) (r L k : ℕ)
    (hr : 2≤r) (hL : 0<L) (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (t : Fin L → ℝ) (hk : activeCount (zeroExtend t) L=k)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : Measurable ρ)
    (hfinite : (∫⁻ w,(ρ w:ENNReal) ∂volume)<⊤)
    (hprior : ∀ w,networkTargetLoss μ r t w=0 → ContinuousAt ρ w ∧ 0<ρ w) :
    UnifiedNetworkCertificate μ r L k t ρ := by
  have hke : activeCount (fun i => zeroExtend t i^r) L=k := (raw_activeCount_eq r L (by omega) t).trans hk
  have hglobal := arbitrary_active_global_rlct_laplace_certificate μ r L k hr hL hμ t hke ρ hρ hfinite hprior
  have hcard := raw_network_fiber_cardinality r L L k hr t hk
  refine {
    active_count_le := hk ▸ activeCount_le (zeroExtend t) L
    loss_fiber := ?_
    ordered_fiber := ?_
    odd_fiber := ?_
    even_fiber := ?_
    finite_fiber := hcard.1
    fiber_cardinality := hcard.2
    local_certificates := network_local_certificate_at_every_fiber μ r L k hr hL hμ t hk ρ hρ hprior
    local_at_arrangement := fun x hx n τ hτ hd hcoord =>
      network_local_certificate_at_arrangement μ r L k hr hL hμ t x hx n τ hτ hd hcoord
        ρ hρ (hprior x hx).1 (hprior x hx).2
    global_dominance := ?_
    global_attained := network_global_pair_locally_attained μ r L k hr hL hμ t hk ρ hρ hprior
    global_integrability := hglobal.1
    global_boundary := arbitrary_active_global_boundary_diverges μ r L k hr hL hμ t hke ρ hρ hfinite hprior
    global_laplace := hglobal.2 }
  · ext w
    exact networkTargetLoss_eq_zero_iff μ r L hr hL hμ t w
  · intro w
    exact (networkTargetLoss_eq_zero_iff μ r L hr hL hμ t w).trans (network_full_raw_fiber r L L hr w t)
  · intro ho w
    exact (networkTargetLoss_eq_zero_iff μ r L hr hL hμ t w).trans (network_full_raw_fiber_odd r L L hr ho w t)
  · intro he w
    exact (networkTargetLoss_eq_zero_iff μ r L hr hL hμ t w).trans (network_full_raw_fiber_even r L L hr he w t)
  · intro n hn
    constructor
    · simpa only [hn] using arrangement_global_exponent_le r k hr n
    · intro he
      have hh := arrangement_global_multiplicity_le_of_exponent_eq r k hr n (by simpa only [hn] using he)
      simpa only [hn] using hh

/-- Convenient population-loss zero-fiber count extracted from the unified certificate. -/
theorem UnifiedNetworkCertificate.loss_fiber_cardinality {μ : Measure ℝ} {r L k : ℕ}
    {t : Fin L → ℝ} {ρ : (Fin L → ℝ) → NNReal} (h : UnifiedNetworkCertificate μ r L k t ρ) :
    {w : Fin L → ℝ | networkTargetLoss μ r t w=0}.Finite ∧
      {w : Fin L → ℝ | networkTargetLoss μ r t w=0}.ncard=(if Even r then 2^k else 1)*L.choose k := by
  rw [h.loss_fiber]
  exact ⟨h.finite_fiber,h.fiber_cardinality⟩

end ResidualSLT
