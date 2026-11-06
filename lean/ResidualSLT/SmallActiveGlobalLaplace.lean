module
public import ResidualSLT.GlobalArrangementAssembly
public import ResidualSLT.GlobalLaplaceThreshold

/-! Global one- and two-active network Laplace exponents and multiplicities. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial MeasureTheory Metric Set Filter

/-- Full-space one-active certificate at any realization of the target. -/
theorem one_active_global_network_laplace (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 0<L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (c : ℝ) (hc : c≠0)
    (t : Fin L → ℝ) (ht : network r (fun i => zeroExtend t i^r) L=activeTarget r c)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : Measurable ρ)
    (hfinite : (∫⁻ w,(ρ w:ENNReal) ∂volume)<⊤)
    (hprior : ∀ w,networkTargetLoss μ r t w=0 → ContinuousAt ρ w ∧ 0<ρ w) :
    HasLaplaceOrder (globalLearningPair r 1 (L-1)).1 (globalLearningPair r 1 (L-1)).2
      (fun N => ∫ w,Real.exp (-N*networkTargetLoss μ r t w)
        ∂volume.withDensity (fun w => (ρ w:ENNReal))) := by
  apply finite_arrangement_fiber_global_laplace μ r L 1 hr hL hL hμ t _ _ ρ hρ hfinite hprior
  · apply (one_active_raw_fiber_finite r L hr c hc).subset
    intro w hw
    exact ((networkTargetLoss_eq_zero_iff μ r L hr hL hμ t w).mp hw).trans ht
  · intro w hw
    exact one_active_realization_arrangement r L hr c hc w
      (((networkTargetLoss_eq_zero_iff μ r L hr hL hμ t w).mp hw).trans ht)

/-- Full-space two-active certificate: the ordered coefficients may be equal or opposite. -/
theorem two_active_global_network_laplace (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 2≤L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (c d : ℝ) (hc : c≠0) (hd : d≠0)
    (t : Fin L → ℝ) (ht : network r (fun i => zeroExtend t i^r) L=twoActiveTarget r c d)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : Measurable ρ)
    (hfinite : (∫⁻ w,(ρ w:ENNReal) ∂volume)<⊤)
    (hprior : ∀ w,networkTargetLoss μ r t w=0 → ContinuousAt ρ w ∧ 0<ρ w) :
    HasLaplaceOrder (globalLearningPair r 2 (L-2)).1 (globalLearningPair r 2 (L-2)).2
      (fun N => ∫ w,Real.exp (-N*networkTargetLoss μ r t w)
        ∂volume.withDensity (fun w => (ρ w:ENNReal))) := by
  apply finite_arrangement_fiber_global_laplace μ r L 2 hr (by omega) hL hμ t _ _ ρ hρ hfinite hprior
  · apply (two_active_raw_fiber_finite r L hr c d hc hd).subset
    intro w hw
    exact ((networkTargetLoss_eq_zero_iff μ r L hr (by omega) hμ t w).mp hw).trans ht
  · intro w hw
    exact two_active_realization_arrangement r L hr c d hc hd w
      (((networkTargetLoss_eq_zero_iff μ r L hr (by omega) hμ t w).mp hw).trans ht)

/-- Finite fibers are null for every density against Lebesgue measure. -/
theorem network_finite_fiber_ae_pos (μ : Measure ℝ) (r L : ℕ) (hL : 0<L) (t : Fin L → ℝ)
    (hf : {w : Fin L → ℝ | networkTargetLoss μ r t w=0}.Finite)
    (ρ : (Fin L → ℝ) → NNReal) :
    ∀ᵐ w ∂volume.withDensity (fun w => (ρ w:ENNReal)), 0<networkTargetLoss μ r t w := by
  let : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
  have hn : ∀ᵐ w ∂volume.withDensity (fun w => (ρ w:ENNReal)), networkTargetLoss μ r t w≠0 := by
    rw [ae_iff]
    exact withDensity_absolutelyContinuous volume _ (by simpa only [not_not] using hf.measure_zero volume)
  filter_upwards [hn] with w hw
  exact lt_of_le_of_ne (integral_nonneg (fun _ => sq_nonneg _)) (Ne.symm hw)

/-- Global inverse-power threshold for positive exponents under a finite prior measure.
Negative exponents would require additional tail moments and are deliberately not assumed. -/
theorem network_global_inversePower_iff (μ : Measure ℝ) (r L : ℕ) (hr : 2≤r) (hL : 0<L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (t : Fin L → ℝ)
    (hf : {w : Fin L → ℝ | networkTargetLoss μ r t w=0}.Finite)
    (ρ : (Fin L → ℝ) → NNReal) (hfinite : (∫⁻ w,(ρ w:ENNReal) ∂volume)<⊤)
    (a : ℝ) (m : ℕ)
    (ho : HasLaplaceOrder a m (fun N => ∫ w,Real.exp (-N*networkTargetLoss μ r t w)
      ∂volume.withDensity (fun w => (ρ w:ENNReal)))) (s : ℝ) (hs : 0<s) :
    Integrable (fun w => (networkTargetLoss μ r t w)^(-s))
      (volume.withDensity (fun w => (ρ w:ENNReal))) ↔ s<a := by
  let ν := volume.withDensity (fun w => (ρ w:ENNReal))
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity hfinite.ne
  have hK := (networkTargetLoss_continuous μ r L hr hL hμ t).measurable
  exact inversePower_integrable_iff_of_laplace_order_pos ν (networkTargetLoss μ r t) hK
    (network_finite_fiber_ae_pos μ r L hL t hf ρ)
    (fun N hN => integrable_exp_neg_loss ν _ hK (fun _ => integral_nonneg (fun _ => sq_nonneg _)) N hN.le)
    a m ho s hs

theorem globalLearningPair_pos (r k n : ℕ) (hk : 0<k) : 0<(globalLearningPair r k n).1 := by
  have hn : 0≤(identityLearningPair r n).1 := by
    unfold identityLearningPair
    split_ifs <;> dsimp <;> positivity
  exact add_pos_of_pos_of_nonneg (by positivity) hn

/-- The global one-active RLCT and multiplicity, with boundary divergence included in the iff. -/
theorem one_active_global_rlct_laplace_certificate (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 0<L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (c : ℝ) (hc : c≠0)
    (t : Fin L → ℝ) (ht : network r (fun i => zeroExtend t i^r) L=activeTarget r c)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : Measurable ρ)
    (hfinite : (∫⁻ w,(ρ w:ENNReal) ∂volume)<⊤)
    (hprior : ∀ w,networkTargetLoss μ r t w=0 → ContinuousAt ρ w ∧ 0<ρ w) :
    (∀ s : ℝ,0<s → (Integrable (fun w => (networkTargetLoss μ r t w)^(-s))
      (volume.withDensity (fun w => (ρ w:ENNReal))) ↔ s<(globalLearningPair r 1 (L-1)).1)) ∧
    HasLaplaceOrder (globalLearningPair r 1 (L-1)).1 (globalLearningPair r 1 (L-1)).2
      (fun N => ∫ w,Real.exp (-N*networkTargetLoss μ r t w)
        ∂volume.withDensity (fun w => (ρ w:ENNReal))) := by
  have ho := one_active_global_network_laplace μ r L hr hL hμ c hc t ht ρ hρ hfinite hprior
  refine ⟨?_,ho⟩
  intro s hs
  apply network_global_inversePower_iff μ r L hr hL hμ t _ ρ hfinite _ _ ho s hs
  apply (one_active_raw_fiber_finite r L hr c hc).subset
  intro w hw
  exact ((networkTargetLoss_eq_zero_iff μ r L hr hL hμ t w).mp hw).trans ht

/-- The global two-active RLCT and multiplicity, with the same proper-prior hypotheses. -/
theorem two_active_global_rlct_laplace_certificate (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 2≤L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (c d : ℝ) (hc : c≠0) (hd : d≠0)
    (t : Fin L → ℝ) (ht : network r (fun i => zeroExtend t i^r) L=twoActiveTarget r c d)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : Measurable ρ)
    (hfinite : (∫⁻ w,(ρ w:ENNReal) ∂volume)<⊤)
    (hprior : ∀ w,networkTargetLoss μ r t w=0 → ContinuousAt ρ w ∧ 0<ρ w) :
    (∀ s : ℝ,0<s → (Integrable (fun w => (networkTargetLoss μ r t w)^(-s))
      (volume.withDensity (fun w => (ρ w:ENNReal))) ↔ s<(globalLearningPair r 2 (L-2)).1)) ∧
    HasLaplaceOrder (globalLearningPair r 2 (L-2)).1 (globalLearningPair r 2 (L-2)).2
      (fun N => ∫ w,Real.exp (-N*networkTargetLoss μ r t w)
        ∂volume.withDensity (fun w => (ρ w:ENNReal))) := by
  have ho := two_active_global_network_laplace μ r L hr hL hμ c d hc hd t ht ρ hρ hfinite hprior
  refine ⟨?_,ho⟩
  intro s hs
  apply network_global_inversePower_iff μ r L hr (by omega) hμ t _ ρ hfinite _ _ ho s hs
  apply (two_active_raw_fiber_finite r L hr c d hc hd).subset
  intro w hw
  exact ((networkTargetLoss_eq_zero_iff μ r L hr (by omega) hμ t w).mp hw).trans ht

/-- The endpoint fails to be integrable whenever the global exponent is positive. -/
theorem network_global_boundary_diverges (μ : Measure ℝ) (r L : ℕ) (hr : 2≤r) (hL : 0<L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (t : Fin L → ℝ)
    (hf : {w : Fin L → ℝ | networkTargetLoss μ r t w=0}.Finite)
    (ρ : (Fin L → ℝ) → NNReal) (hfinite : (∫⁻ w,(ρ w:ENNReal) ∂volume)<⊤)
    (a : ℝ) (m : ℕ) (ha : 0<a)
    (ho : HasLaplaceOrder a m (fun N => ∫ w,Real.exp (-N*networkTargetLoss μ r t w)
      ∂volume.withDensity (fun w => (ρ w:ENNReal)))) :
    ¬Integrable (fun w => (networkTargetLoss μ r t w)^(-a))
      (volume.withDensity (fun w => (ρ w:ENNReal))) := by
  rw [network_global_inversePower_iff μ r L hr hL hμ t hf ρ hfinite a m ho a ha]
  exact lt_irrefl a

/-- Every nonzero raw active weight gives a realized one-active target at every positive depth. -/
theorem one_active_raw_target_exists (r L : ℕ) (hr : 2≤r) (hL : 0<L)
    (α : ℝ) (hα : α≠0) :
    ∃ t : Fin L → ℝ, network r (fun i => zeroExtend t i^r) L=activeTarget r (α^r) := by
  classical
  let i : Fin L := ⟨0,hL⟩
  refine ⟨Pi.single i α,(one_active_raw_fiber r L hr _ (pow_ne_zero _ hα) _).mpr ?_⟩
  exact ⟨i,by simp,fun j hj => by simp [Pi.single_eq_of_ne hj]⟩

/-- Every ordered pair of nonzero raw active weights is realized at depth at least two. -/
theorem two_active_raw_target_exists (r L : ℕ) (hr : 2≤r) (hL : 2≤L)
    (α β : ℝ) (hα : α≠0) (hβ : β≠0) :
    ∃ t : Fin L → ℝ, network r (fun i => zeroExtend t i^r) L=twoActiveTarget r (α^r) (β^r) := by
  classical
  let i : Fin L := ⟨0,by omega⟩
  let j : Fin L := ⟨1,by omega⟩
  have hij : i<j := by exact Nat.zero_lt_one
  have hne : i≠j := ne_of_lt hij
  refine ⟨fun a => if a=i then α else if a=j then β else 0,
    (two_active_raw_fiber r L hr _ _ (pow_ne_zero _ hα) (pow_ne_zero _ hβ) _).mpr ?_⟩
  exact ⟨i,j,hij,by simp,by simp [Ne.symm hne],fun a hai haj => by simp [hai,haj]⟩

/-- Explicit endpoint divergence for the globally dominant network exponent. -/
theorem one_active_global_boundary_diverges (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 0<L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (c : ℝ) (hc : c≠0)
    (t : Fin L → ℝ) (ht : network r (fun i => zeroExtend t i^r) L=activeTarget r c)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : Measurable ρ)
    (hfinite : (∫⁻ w,(ρ w:ENNReal) ∂volume)<⊤)
    (hprior : ∀ w,networkTargetLoss μ r t w=0 → ContinuousAt ρ w ∧ 0<ρ w) :
    ¬Integrable (fun w => (networkTargetLoss μ r t w)^(-(globalLearningPair r 1 (L-1)).1))
      (volume.withDensity (fun w => (ρ w:ENNReal))) := by
  have hh := (one_active_global_rlct_laplace_certificate μ r L hr hL hμ c hc t ht ρ hρ hfinite hprior).1
  rw [hh _ (globalLearningPair_pos r 1 (L-1) (by omega))]
  exact lt_irrefl _

/-- Explicit endpoint divergence for the globally dominant network exponent. -/
theorem two_active_global_boundary_diverges (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 2≤L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (c d : ℝ) (hc : c≠0) (hd : d≠0)
    (t : Fin L → ℝ) (ht : network r (fun i => zeroExtend t i^r) L=twoActiveTarget r c d)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : Measurable ρ)
    (hfinite : (∫⁻ w,(ρ w:ENNReal) ∂volume)<⊤)
    (hprior : ∀ w,networkTargetLoss μ r t w=0 → ContinuousAt ρ w ∧ 0<ρ w) :
    ¬Integrable (fun w => (networkTargetLoss μ r t w)^(-(globalLearningPair r 2 (L-2)).1))
      (volume.withDensity (fun w => (ρ w:ENNReal))) := by
  have hh := (two_active_global_rlct_laplace_certificate μ r L hr hL hμ c d hc hd t ht ρ hρ hfinite hprior).1
  rw [hh _ (globalLearningPair_pos r 2 (L-2) (by omega))]
  exact lt_irrefl _

end ResidualSLT
