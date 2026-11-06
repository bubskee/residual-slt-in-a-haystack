module
public import ResidualSLT.ArrangementCoordinates

/-! End-to-end arbitrary-active arrangement certificate in original raw coordinates. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Filter Metric Set

theorem HasLaplaceOrder.const_mul {a : ℝ} {m : ℕ} {Z : ℝ → ℝ}
    (h : HasLaplaceOrder a m Z) (d : ℝ) (hd : 0 < d) :
    HasLaplaceOrder a m (fun N => d*Z N) := by
  obtain ⟨hm,c,C,T,hc,hC,hT,hb⟩ := h
  refine ⟨hm,d*c,d*C,T,mul_pos hd hc,mul_pos hd hC,hT,?_⟩
  intro N hN
  simpa only [mul_assoc] using
    And.intro (mul_le_mul_of_nonneg_left (hb N hN).1 hd.le)
      (mul_le_mul_of_nonneg_left (hb N hN).2 hd.le)

theorem HasLaplaceOrder.of_const_mul {a d : ℝ} {m : ℕ} {Z : ℝ → ℝ}
    (h : HasLaplaceOrder a m (fun N => d*Z N)) (hd : 0 < d) : HasLaplaceOrder a m Z := by
  have hh := h.const_mul d⁻¹ (inv_pos.mpr hd)
  simpa only [← mul_assoc,inv_mul_cancel₀ hd.ne',one_mul] using hh

/-- Arbitrary positive active count, every nonzero active value and all group sizes.
The domain is the original chronological raw-weight ball about the realization.
The inverse-power threshold includes divergence at the boundary; multiplicity is the
logarithmic exponent in quantitative two-sided Laplace bounds. -/
theorem arrangement_raw_network_rlct_laplace_certificate (μ : Measure ℝ) (r k : ℕ) (hr : 2 ≤ r) (hk : 0 < k)
    (n : Fin (k+1) → ℕ)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r (arrangementDepth k n k le_rfl)))
    (τ : Fin k → ℝ) (hτ : ∀ j,τ j ≠ 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ ρ : (Fin (arrangementDepth k n k le_rfl) → ℝ) → NNReal,
        BoundedPositivePriorOn ρ (ball (arrangementFlatten k n τ 0 k le_rfl) ε) volume →
      (∀ s : ℝ, IntegrableOn (fun w : Fin (arrangementDepth k n k le_rfl) → ℝ => (networkTargetLoss μ r (arrangementFlatten k n τ 0 k le_rfl) w)^(-s))
        (ball (arrangementFlatten k n τ 0 k le_rfl) ε) (volume.withDensity (fun w => (ρ w : ENNReal))) ↔
          s < (arrangementLearningPair r k n).1) ∧
      HasLaplaceOrder (arrangementLearningPair r k n).1 (arrangementLearningPair r k n).2
        (fun N => ∫ w : Fin (arrangementDepth k n k le_rfl) → ℝ in ball (arrangementFlatten k n τ 0 k le_rfl) ε,
          Real.exp (-N*networkTargetLoss μ r (arrangementFlatten k n τ 0 k le_rfl) w)
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  obtain ⟨ε₀,hε₀,hε₀1,hcert⟩ := arrangement_network_rlct_laplace_certificate μ r k hr hk n hμ τ hτ
  refine ⟨ε₀,hε₀,hε₀1,?_⟩
  intro ε hε hεsmall ρ hρ
  have hρone : BoundedPositivePriorOn (fun _ : ArrangementAux k n => (1:NNReal)) (ball 0 ε) volume :=
    ⟨measurable_const,1,1,by norm_num,Eventually.of_forall (fun _ => ⟨le_rfl,le_rfl⟩)⟩
  obtain ⟨hthreshold,horder⟩ := hcert ε hε hεsmall _ hρone
  have hvol : (volume : Measure (ArrangementAux k n)).withDensity (fun _ => (1:ENNReal)) = volume := withDensity_one
  simp only [ENNReal.coe_one,hvol,arrangementPopulationLoss] at hthreshold horder
  obtain ⟨d,hd,hmeasure⟩ := arrangementCoordinateEquiv_measure_comparison k n τ
  let e := arrangementCoordinateEquiv k n τ
  have hmp : MeasurePreserving e
      ((volume : Measure (ArrangementAux k n)).restrict (ball 0 ε))
      ((d • (volume : Measure (Fin (arrangementDepth k n k le_rfl) → ℝ))).restrict (ball (arrangementFlatten k n τ 0 k le_rfl) ε)) := by
    have hh := hmeasure.restrict_preimage
      (measurableSet_ball (x := arrangementFlatten k n τ 0 k le_rfl) (ε := ε))
    simpa only [arrangementCoordinateEquiv_preimage_ball] using hh
  have hK := networkTargetLoss_continuous μ r _ hr (hk.trans_le (arrangementDepth_ge k n k le_rfl)) hμ (arrangementFlatten k n τ 0 k le_rfl)
  constructor
  · intro s
    rw [integrableOn_withDensity_iff_of_boundedPositive measurableSet_ball hρ]
    have he := hmp.integrable_comp ((hK.measurable.pow_const (-s)).aestronglyMeasurable)
    have he' : IntegrableOn
        (fun w : ArrangementAux k n => (networkTargetLoss μ r (arrangementFlatten k n τ 0 k le_rfl) (arrangementFlatten k n τ w k le_rfl))^(-s))
          (ball 0 ε) volume ↔
        IntegrableOn (fun w : Fin (arrangementDepth k n k le_rfl) → ℝ => (networkTargetLoss μ r (arrangementFlatten k n τ 0 k le_rfl) w)^(-s))
          (ball (arrangementFlatten k n τ 0 k le_rfl) ε) (d • volume) := by
      simpa only [IntegrableOn,Function.comp_def,e,arrangementCoordinateEquiv_apply] using he
    have hs : IntegrableOn (fun w : Fin (arrangementDepth k n k le_rfl) → ℝ =>
          (networkTargetLoss μ r (arrangementFlatten k n τ 0 k le_rfl) w)^(-s))
          (ball (arrangementFlatten k n τ 0 k le_rfl) ε) (d • volume) ↔
        IntegrableOn (fun w : Fin (arrangementDepth k n k le_rfl) → ℝ =>
          (networkTargetLoss μ r (arrangementFlatten k n τ 0 k le_rfl) w)^(-s))
          (ball (arrangementFlatten k n τ 0 k le_rfl) ε) volume := by
      simp only [IntegrableOn,Measure.restrict_smul]
      exact integrable_smul_measure (by exact_mod_cast hd.ne') ENNReal.coe_ne_top
    exact hs.symm.trans (he'.symm.trans (hthreshold s))
  · have he (N : ℝ) :
        (∫ w : ArrangementAux k n in ball 0 ε,
          Real.exp (-N*networkTargetLoss μ r (arrangementFlatten k n τ 0 k le_rfl) (arrangementFlatten k n τ w k le_rfl))) =
        ∫ w : Fin (arrangementDepth k n k le_rfl) → ℝ in ball (arrangementFlatten k n τ 0 k le_rfl) ε,
          Real.exp (-N*networkTargetLoss μ r (arrangementFlatten k n τ 0 k le_rfl) w) ∂(d • volume) := by
      simpa only [e,arrangementCoordinateEquiv_apply] using
        hmp.integral_comp e.measurableEmbedding (fun w => Real.exp (-N*networkTargetLoss μ r (arrangementFlatten k n τ 0 k le_rfl) w))
    simp_rw [he,Measure.restrict_smul,integral_smul_nnreal_measure] at horder
    have horder := horder.of_const_mul (by exact_mod_cast hd)
    apply laplace_pair_order_withDensity volume measurableSet_ball _ _ ρ hρ horder
    intro N
    exact ((by fun_prop : Continuous (fun w : Fin (arrangementDepth k n k le_rfl) → ℝ => Real.exp (-N*networkTargetLoss μ r (arrangementFlatten k n τ 0 k le_rfl) w))).continuousOn.integrableOn_compact
      (isCompact_closedBall (arrangementFlatten k n τ 0 k le_rfl) ε)).mono_set ball_subset_closedBall


end ResidualSLT
