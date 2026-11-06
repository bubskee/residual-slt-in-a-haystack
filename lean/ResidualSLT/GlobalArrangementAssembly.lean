module
public import ResidualSLT.LocalPositivePrior
public import ResidualSLT.SmallArrangementRealizations

/-! From a finite classified fiber to full-space network Laplace bounds. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial MeasureTheory Metric Set Filter

theorem networkTargetLoss_congr_target (μ : Measure ℝ) (r L : ℕ) (t z : Fin L → ℝ)
    (he : network r (fun i => zeroExtend t i^r) L=network r (fun i => zeroExtend z i^r) L) :
    networkTargetLoss μ r t=networkTargetLoss μ r z := by
  funext w
  simp only [networkTargetLoss,he]

theorem arrangement_center_polynomial (r L k : ℕ) (hr : 2 ≤ r) (n : Fin (k+1) → ℕ)
    (τ : Fin k → ℝ) (hd : arrangementDepth k n k le_rfl=L) (t : Fin L → ℝ)
    (ht : ∀ i : Fin (arrangementDepth k n k le_rfl), t (Fin.cast hd i)=arrangementFlatten k n τ 0 k le_rfl i) :
    network r (fun i => zeroExtend t i^r) L=network r (zeroExtend (fun j => τ j^r)) k := by
  subst L
  have ht' : t=arrangementFlatten k n τ 0 k le_rfl := funext ht
  rw [ht',arrangementFlatten_target r k hr]

/-- Concentrating the inactive blocks gives an actual raw realization of the same target
and attains the proposed global pair. -/
theorem concentrated_realization_local_order (μ : Measure ℝ) (r L k : ℕ) (hr : 2 ≤ r)
    (hL : 0<L) (hk : k≤L) (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (t : Fin L → ℝ) (τ : Fin k → ℝ) (hτ : ∀ j,τ j≠0)
    (ht : network r (fun i => zeroExtend t i^r) L=network r (zeroExtend (fun j => τ j^r)) k) :
    ∃ z : Fin L → ℝ, networkTargetLoss μ r t z=0 ∧
      ∃ ε₀ : ℝ,0<ε₀ ∧ ε₀≤1 ∧ ∀ ε : ℝ,0<ε → ε≤ε₀ →
        ∀ ρ : (Fin L → ℝ) → NNReal,BoundedPositivePriorOn ρ (ball z ε) volume →
          HasLaplaceOrder (globalLearningPair r k (L-k)).1 (globalLearningPair r k (L-k)).2
            (fun N => ∫ w in ball z ε,Real.exp (-N*networkTargetLoss μ r t w)
              ∂volume.withDensity (fun w => (ρ w:ENNReal))) := by
  let n := concentratedGroups k (L-k)
  have hd : arrangementDepth k n k le_rfl=L := by
    rw [arrangementDepth_eq_sum]
    simp only [Fin.eta,concentratedGroups_sum,n]
    omega
  let z : Fin L → ℝ := fun i => arrangementFlatten k n τ 0 k le_rfl (Fin.cast hd.symm i)
  have hz : ∀ i : Fin (arrangementDepth k n k le_rfl), z (Fin.cast hd i)=arrangementFlatten k n τ 0 k le_rfl i := by
    intro i; simp [z]
  have hpoly := arrangement_center_polynomial r L k hr n τ hd z hz
  have heq : networkTargetLoss μ r t=networkTargetLoss μ r z := networkTargetLoss_congr_target μ r L t z (ht.trans hpoly.symm)
  refine ⟨z,(networkTargetLoss_eq_zero_iff μ r L hr hL hμ t z).mpr (hpoly.trans ht.symm),?_⟩
  have hh := arrangement_raw_certificate_at μ r L k hr hL hμ n τ hτ hd z hz
  simpa only [n,arrangementLearningPair_concentrated r k (L-k) hr,heq] using hh

/-- A finite fiber whose every point has the certified k-active arrangement form has the
concentrated global pair. Finiteness and the arrangement descriptions are verified separately
for the one- and two-active fibers. -/
theorem finite_arrangement_fiber_global_laplace (μ : Measure ℝ) (r L k : ℕ) (hr : 2 ≤ r)
    (hL : 0<L) (hk : k≤L) (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (t : Fin L → ℝ)
    (hf : {w : Fin L → ℝ | networkTargetLoss μ r t w=0}.Finite)
    (harr : ∀ w : Fin L → ℝ, networkTargetLoss μ r t w=0 →
      ∃ n : Fin (k+1) → ℕ,∃ τ : Fin k → ℝ,(∀ j,τ j≠0) ∧ (∑ g,n g)=L-k ∧
        ∃ hd : arrangementDepth k n k le_rfl=L,
          ∀ i : Fin (arrangementDepth k n k le_rfl), w (Fin.cast hd i)=arrangementFlatten k n τ 0 k le_rfl i)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : Measurable ρ)
    (hfinite : (∫⁻ w,(ρ w:ENNReal) ∂volume)<⊤)
    (hprior : ∀ w,networkTargetLoss μ r t w=0 → ContinuousAt ρ w ∧ 0<ρ w) :
    HasLaplaceOrder (globalLearningPair r k (L-k)).1 (globalLearningPair r k (L-k)).2
      (fun N => ∫ w,Real.exp (-N*networkTargetLoss μ r t w)
        ∂volume.withDensity (fun w => (ρ w:ENNReal))) := by
  classical
  let K := networkTargetLoss μ r t
  let ν := volume.withDensity (fun w => (ρ w:ENNReal))
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity hfinite.ne
  let F := {w : Fin L → ℝ | K w=0}
  let : Fintype F := hf.fintype
  have hK : Measurable K := (networkTargetLoss_continuous μ r L hr hL hμ t).measurable
  have hpos (w) : 0≤K w := integral_nonneg (fun _ => sq_nonneg _)
  have hlocal (x : F) : ∃ ε : ℝ,0<ε ∧ ∃ C : ℝ,0<C ∧ ∀ᶠ N : ℝ in atTop,
      (∫ w in ball x.val ε,Real.exp (-N*K w) ∂ν) ≤ C*laplaceRate
        (globalLearningPair r k (L-k)).1 (globalLearningPair r k (L-k)).2 N := by
    obtain ⟨n,τ,hτ,hn,hd,hx⟩ := harr x.val x.property
    have heq : K=networkTargetLoss μ r x.val := networkTargetLoss_congr_target μ r L t x.val
      ((networkTargetLoss_eq_zero_iff μ r L hr hL hμ t x.val).mp x.property).symm
    have hc := arrangement_raw_certificate_at μ r L k hr hL hμ n τ hτ hd x.val hx
    obtain ⟨ε,hε,ho⟩ := local_laplace_with_continuous_prior volume K x.val
      (arrangementLearningPair r k n).1 (arrangementLearningPair r k n).2
      (by simpa only [heq] using hc) ρ hρ (hprior x.val x.property).1 (hprior x.val x.property).2
    have hle := arrangement_global_exponent_le r k hr n
    rw [hn] at hle
    have hdom : (globalLearningPair r k (L-k)).1 < (arrangementLearningPair r k n).1 ∨
        (globalLearningPair r k (L-k)).1 = (arrangementLearningPair r k n).1 ∧
        (arrangementLearningPair r k n).2 ≤ (globalLearningPair r k (L-k)).2 := by
      rcases lt_or_eq_of_le hle with hh | hh
      · exact Or.inl hh
      · refine Or.inr ⟨hh,?_⟩
        have hm := arrangement_global_multiplicity_le_of_exponent_eq r k hr n (by rw [hn]; exact hh.symm)
        simpa only [hn] using hm
    exact ⟨ε,hε,ho.upper_of_dominates hdom⟩
  choose ε hε C hC hu using hlocal
  let D : F → Set (Fin L → ℝ) := fun x => ball x.val (ε x)
  let U := ⋃ x : F,D x
  have hU : IsOpen U := isOpen_iUnion (fun _ => isOpen_ball)
  have hzero : ∀ w,K w=0 → w∈U := by
    intro w hw
    exact mem_iUnion.mpr ⟨⟨w,hw⟩,mem_ball_self (hε ⟨w,hw⟩)⟩
  obtain ⟨b,hb,hgap⟩ := networkTargetLoss_gap_outside μ r L hr hL hμ t U hU hzero
  have hself : K t=0 := by simp [K,networkTargetLoss]
  obtain ⟨n,τ,hτ,_,hd,ht⟩ := harr t hself
  have htpoly := arrangement_center_polynomial r L k hr n τ hd t ht
  obtain ⟨z,hz,hl⟩ := concentrated_realization_local_order μ r L k hr hL hk hμ t τ hτ htpoly
  obtain ⟨δ,hδ,hlower⟩ := local_laplace_with_continuous_prior volume K z
    (globalLearningPair r k (L-k)).1 (globalLearningPair r k (L-k)).2 hl ρ hρ (hprior z hz).1 (hprior z hz).2
  exact finite_local_laplace_assembly ν K hK hpos D (fun _ => measurableSet_ball) b hb
    (fun w hw => hgap w (by simpa only [U,mem_iUnion,not_exists] using hw))
    _ _ (fun x => ⟨C x,hC x,hu x⟩) (ball z δ) hlower

end ResidualSLT
