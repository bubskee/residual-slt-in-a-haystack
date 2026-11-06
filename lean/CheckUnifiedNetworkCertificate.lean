import ResidualSLT

open ResidualSLT MeasureTheory Metric Set

-- All conclusions are obtained from the single assembled certificate.
example (μ : Measure ℝ) (t : Fin 6 → ℝ) (ρ : (Fin 6 → ℝ) → NNReal)
    (h : UnifiedNetworkCertificate μ 3 6 3 t ρ) :
    {w : Fin 6 → ℝ | networkTargetLoss μ 3 t w=0}.ncard=20 := by
  simpa [Nat.choose,show ¬Even 3 by decide] using h.loss_fiber_cardinality.2

example (μ : Measure ℝ) (t : Fin 6 → ℝ) (ρ : (Fin 6 → ℝ) → NNReal)
    (h : UnifiedNetworkCertificate μ 2 6 3 t ρ) :
    {w : Fin 6 → ℝ | networkTargetLoss μ 2 t w=0}.ncard=160 := by
  simpa [Nat.choose] using h.loss_fiber_cardinality.2

example (μ : Measure ℝ) (t : Fin 6 → ℝ) (ρ : (Fin 6 → ℝ) → NNReal)
    (h : UnifiedNetworkCertificate μ 3 6 3 t ρ) :
    HasLaplaceOrder 2 2 (fun N => ∫ w,Real.exp (-N*networkTargetLoss μ 3 t w)
      ∂volume.withDensity (fun w => (ρ w:ENNReal))) := by
  convert h.global_laplace using 1 <;> norm_num [globalLearningPair,identityLearningPair]

example (μ : Measure ℝ) (t : Fin 6 → ℝ) (ρ : (Fin 6 → ℝ) → NNReal)
    (h : UnifiedNetworkCertificate μ 3 6 3 t ρ) :
    ¬Integrable (fun w => (networkTargetLoss μ 3 t w)^(-(2:ℝ)))
      (volume.withDensity (fun w => (ρ w:ENNReal))) := by
  convert h.global_boundary using 1
  norm_num [globalLearningPair,identityLearningPair]

-- Same function and the same prior, but different local arrangement pairs.
example (μ : Measure ℝ) (ρ : (Fin 5 → ℝ) → NNReal)
    (h : UnifiedNetworkCertificate μ 3 5 1 (![1,0,0,0,0] : Fin 5 → ℝ) ρ) :
    LocalNetworkCertificate μ 3 (![1,0,0,0,0] : Fin 5 → ℝ) ![0,1,0,0,0] ρ ((7/6:ℝ),2) := by
  have hz : networkTargetLoss μ 3 (![1,0,0,0,0] : Fin 5 → ℝ) ![0,1,0,0,0]=0 := by
    rw [h.odd_fiber (by decide)]
    norm_num [activeWord,zeroExtend]
  have hd : arrangementDepth 1 ![1,3] 1 le_rfl=5 := by norm_num [arrangementDepth]
  have hc := h.local_at_arrangement ![0,1,0,0,0] hz ![1,3] ![1]
    (by intro j; fin_cases j; norm_num) hd (by
      intro i
      rw [arrangement_one_center]
      fin_cases i <;> norm_num [Fin.cast])
  norm_num [arrangementLearningPair,identityLearningPair,Fin.sum_univ_succ] at hc
  exact hc

-- The central (2,2) split has the same exponent but multiplicity one.
example (μ : Measure ℝ) (ρ : (Fin 5 → ℝ) → NNReal)
    (h : UnifiedNetworkCertificate μ 3 5 1 (![1,0,0,0,0] : Fin 5 → ℝ) ρ) :
    LocalNetworkCertificate μ 3 (![1,0,0,0,0] : Fin 5 → ℝ) ![0,0,1,0,0] ρ ((7/6:ℝ),1) := by
  have hz : networkTargetLoss μ 3 (![1,0,0,0,0] : Fin 5 → ℝ) ![0,0,1,0,0]=0 := by
    rw [h.odd_fiber (by decide)]
    norm_num [activeWord,zeroExtend]
  have hd : arrangementDepth 1 ![2,2] 1 le_rfl=5 := by norm_num [arrangementDepth]
  have hc := h.local_at_arrangement ![0,0,1,0,0] hz ![2,2] ![1]
    (by intro j; fin_cases j; norm_num) hd (by
      intro i
      rw [arrangement_one_center]
      fin_cases i <;> norm_num [Fin.cast])
  norm_num [arrangementLearningPair,identityLearningPair,Fin.sum_univ_succ] at hc
  exact hc

example (μ : Measure ℝ) (ρ : (Fin 5 → ℝ) → NNReal)
    (h : UnifiedNetworkCertificate μ 3 5 1 (![1,0,0,0,0] : Fin 5 → ℝ) ρ) :
    LocalNetworkCertificate μ 3 (![1,0,0,0,0] : Fin 5 → ℝ) ![1,0,0,0,0] ρ ((13/12:ℝ),1) := by
  have hz : networkTargetLoss μ 3 (![1,0,0,0,0] : Fin 5 → ℝ) ![1,0,0,0,0]=0 := by
    simp [networkTargetLoss]
  have hd : arrangementDepth 1 ![0,4] 1 le_rfl=5 := by norm_num [arrangementDepth]
  have hc := h.local_at_arrangement ![1,0,0,0,0] hz ![0,4] ![1]
    (by intro j; fin_cases j; norm_num) hd (by
      intro i
      rw [arrangement_one_center]
      fin_cases i <;> norm_num [Fin.cast])
  norm_num [arrangementLearningPair,identityLearningPair,Fin.sum_univ_succ] at hc
  exact hc

-- Identity targets remain included, with an actual attaining local realization.
example (μ : Measure ℝ) (t : Fin 3 → ℝ) (ρ : (Fin 3 → ℝ) → NNReal)
    (h : UnifiedNetworkCertificate μ 3 3 0 t ρ) :
    ∃ x : Fin 3 → ℝ,networkTargetLoss μ 3 t x=0 ∧ LocalNetworkCertificate μ 3 t x ρ ((1/2:ℝ),2) := by
  have hh := h.global_attained
  norm_num [globalLearningPair,identityLearningPair] at hh
  exact hh

-- The unified theorem constructs the record from shared hypotheses, without asking
-- for fiber, coordinate, dominance, or analytic certificates as assumptions.
example (μ : Measure ℝ) (r L k : ℕ) (hr : 2≤r) (hL : 0<L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (t : Fin L → ℝ) (hk : activeCount (zeroExtend t) L=k)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : Measurable ρ)
    (hf : (∫⁻ w,(ρ w:ENNReal) ∂volume)<⊤)
    (hp : ∀ w,networkTargetLoss μ r t w=0 → ContinuousAt ρ w ∧ 0<ρ w) :
    UnifiedNetworkCertificate μ r L k t ρ :=
  unified_residual_network_certificate μ r L k hr hL hμ t hk ρ hρ hf hp
