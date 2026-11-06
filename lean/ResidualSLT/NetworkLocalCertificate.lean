module
public import ResidualSLT.RawFiberCardinality

/-! Local certificates for every realization of a fixed target, with the same prior as
its global certificate. All prior coordinate and analytic proofs are reused unchanged. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial MeasureTheory Metric Set

/-- A local inverse-power threshold, endpoint divergence, and two-sided Laplace order
on every sufficiently small raw-coordinate ball, for the specified target and prior. -/
@[expose] def LocalNetworkCertificate (μ : Measure ℝ) (r : ℕ) {L : ℕ}
    (t x : Fin L → ℝ) (ρ : (Fin L → ℝ) → NNReal) (p : ℝ × ℕ) : Prop :=
  ∃ ε₀ : ℝ,0<ε₀ ∧ ε₀≤1 ∧ ∀ ε : ℝ,0<ε → ε≤ε₀ →
    (∀ s : ℝ,IntegrableOn (fun w => (networkTargetLoss μ r t w)^(-s)) (ball x ε)
      (volume.withDensity (fun w => (ρ w:ENNReal))) ↔ s<p.1) ∧
    (¬IntegrableOn (fun w => (networkTargetLoss μ r t w)^(-p.1)) (ball x ε)
      (volume.withDensity (fun w => (ρ w:ENNReal)))) ∧
    HasLaplaceOrder p.1 p.2 (fun N => ∫ w in ball x ε,Real.exp (-N*networkTargetLoss μ r t w)
      ∂volume.withDensity (fun w => (ρ w:ENNReal)))

/-- Reindex the complete existing arrangement certificate, retaining its integrability part. -/
theorem arrangement_raw_full_certificate_at (μ : Measure ℝ) (r L k : ℕ) (hr : 2≤r) (hL : 0<L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ) (hτ : ∀ j,τ j≠0)
    (hd : arrangementDepth k n k le_rfl=L) (x : Fin L → ℝ)
    (hx : ∀ i : Fin (arrangementDepth k n k le_rfl),x (Fin.cast hd i)=arrangementFlatten k n τ 0 k le_rfl i) :
    ∃ ε₀ : ℝ,0<ε₀ ∧ ε₀≤1 ∧ ∀ ε : ℝ,0<ε → ε≤ε₀ →
      ∀ ρ : (Fin L → ℝ) → NNReal,BoundedPositivePriorOn ρ (ball x ε) volume →
      (∀ s : ℝ,IntegrableOn (fun w => (networkTargetLoss μ r x w)^(-s)) (ball x ε)
        (volume.withDensity (fun w => (ρ w:ENNReal))) ↔ s<(arrangementLearningPair r k n).1) ∧
      HasLaplaceOrder (arrangementLearningPair r k n).1 (arrangementLearningPair r k n).2
        (fun N => ∫ w in ball x ε,Real.exp (-N*networkTargetLoss μ r x w)
          ∂volume.withDensity (fun w => (ρ w:ENNReal))) := by
  subst L
  have hx' : x=arrangementFlatten k n τ 0 k le_rfl := funext hx
  subst x
  exact arrangement_raw_network_rlct_laplace_certificate_of_depth_pos μ r k hr n hL hμ τ hτ

/-- The actual target loss at a fiber point has the local pair of its exact arrangement. -/
theorem network_local_certificate_at_arrangement (μ : Measure ℝ) (r L k : ℕ) (hr : 2≤r) (hL : 0<L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (t x : Fin L → ℝ) (hzero : networkTargetLoss μ r t x=0)
    (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ) (hτ : ∀ j,τ j≠0)
    (hd : arrangementDepth k n k le_rfl=L)
    (hx : ∀ i : Fin (arrangementDepth k n k le_rfl),x (Fin.cast hd i)=arrangementFlatten k n τ 0 k le_rfl i)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : Measurable ρ) (hc : ContinuousAt ρ x) (hp : 0<ρ x) :
    LocalNetworkCertificate μ r t x ρ (arrangementLearningPair r k n) := by
  have heq : networkTargetLoss μ r t=networkTargetLoss μ r x := networkTargetLoss_congr_target μ r L t x
    ((networkTargetLoss_eq_zero_iff μ r L hr hL hμ t x).mp hzero).symm
  obtain ⟨R,hR,hR1,hcert⟩ := arrangement_raw_full_certificate_at μ r L k hr hL hμ n τ hτ hd x hx
  obtain ⟨δ,hδ,hprior⟩ := continuous_positive_prior_local_bounds volume ρ hρ x hc hp
  refine ⟨min R δ,lt_min hR hδ,(min_le_left _ _).trans hR1,?_⟩
  intro ε hε hs
  have hb := hprior.mono (ball_subset_ball (hs.trans (min_le_right R δ)))
  obtain ⟨hi,ho⟩ := hcert ε hε (hs.trans (min_le_left R δ)) ρ hb
  simp only [heq]
  refine ⟨hi,?_,ho⟩
  rw [hi]
  exact lt_irrefl _

/-- Every fiber point has actual inactive groups, a raw center reconstruction, and its
complete local certificate for the fixed target and prior. Includes zero active blocks. -/
theorem network_local_certificate_at_every_fiber (μ : Measure ℝ) (r L k : ℕ)
    (hr : 2≤r) (hL : 0<L) (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (t : Fin L → ℝ) (hk : activeCount (zeroExtend t) L=k)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : Measurable ρ)
    (hprior : ∀ w,networkTargetLoss μ r t w=0 → ContinuousAt ρ w ∧ 0<ρ w)
    (x : Fin L → ℝ) (hzero : networkTargetLoss μ r t x=0) :
    ∃ n : Fin (k+1) → ℕ,∃ τ : Fin k → ℝ,(∀ j,τ j≠0) ∧ (∑ g,n g)=L-k ∧
      ∃ hd : arrangementDepth k n k le_rfl=L,
        (∀ i : Fin (arrangementDepth k n k le_rfl),x (Fin.cast hd i)=arrangementFlatten k n τ 0 k le_rfl i) ∧
        LocalNetworkCertificate μ r t x ρ (arrangementLearningPair r k n) := by
  have hxk : activeCount (fun i => zeroExtend x i^r) L=k := by
    rw [network_eq_activeCount r L L hr _ _ ((networkTargetLoss_eq_zero_iff μ r L hr hL hμ t x).mp hzero),
      raw_activeCount_eq r L (by omega) t,hk]
  obtain ⟨n,τ,hτ,hn,hd,hx⟩ := raw_vector_arrangement_of_activeCount r L k hr x hxk
  exact ⟨n,τ,hτ,hn,hd,hx,network_local_certificate_at_arrangement μ r L k hr hL hμ t x hzero
    n τ hτ hd hx ρ hρ (hprior x hzero).1 (hprior x hzero).2⟩

/-- The globally selected pair is attained by a genuine local realization, with both
inverse-power and Laplace certificates, under the same target loss and prior. -/
theorem network_global_pair_locally_attained (μ : Measure ℝ) (r L k : ℕ)
    (hr : 2≤r) (hL : 0<L) (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (t : Fin L → ℝ) (hk : activeCount (zeroExtend t) L=k)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : Measurable ρ)
    (hprior : ∀ w,networkTargetLoss μ r t w=0 → ContinuousAt ρ w ∧ 0<ρ w) :
    ∃ x : Fin L → ℝ,networkTargetLoss μ r t x=0 ∧
      LocalNetworkCertificate μ r t x ρ (globalLearningPair r k (L-k)) := by
  have hkL : k≤L := hk ▸ activeCount_le (zeroExtend t) L
  have hke : activeCount (fun i => zeroExtend t i^r) L=k := (raw_activeCount_eq r L (by omega) t).trans hk
  obtain ⟨m,τ,hτ,_,hdm,htm⟩ := raw_vector_arrangement_of_activeCount r L k hr t hke
  have htpoly := arrangement_center_polynomial r L k hr m τ hdm t htm
  let n := concentratedGroups k (L-k)
  have hd : arrangementDepth k n k le_rfl=L := by
    rw [arrangementDepth_eq_sum]
    simp only [Fin.eta,concentratedGroups_sum,n]
    omega
  let x : Fin L → ℝ := fun i => arrangementFlatten k n τ 0 k le_rfl (Fin.cast hd.symm i)
  have hx : ∀ i : Fin (arrangementDepth k n k le_rfl),x (Fin.cast hd i)=arrangementFlatten k n τ 0 k le_rfl i := by
    intro i; simp [x]
  have hxpoly := arrangement_center_polynomial r L k hr n τ hd x hx
  have hz : networkTargetLoss μ r t x=0 :=
    (networkTargetLoss_eq_zero_iff μ r L hr hL hμ t x).mpr (hxpoly.trans htpoly.symm)
  refine ⟨x,hz,?_⟩
  have hh := network_local_certificate_at_arrangement μ r L k hr hL hμ t x hz n τ hτ hd hx
    ρ hρ (hprior x hz).1 (hprior x hz).2
  simpa only [n,arrangementLearningPair_concentrated r k (L-k) hr] using hh

end ResidualSLT
