module
public import ResidualSLT.FermatAngular
public import ResidualSLT.RadialBlowup

/-! Composition of explicit radial measure transport and bounded-Jacobian angular
straightening. The resulting chart image remains explicit: it is not asserted to be a box. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory

/-- The positive cone patch associated with a radial set and an angular set. -/
@[expose] def projectiveConePatch {n : ℕ} (j : Fin (n + 1)) (R : Set ℝ)
    (D : Set (Fin n → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  radialBlowup j '' ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j) ⁻¹' (R ×ˢ D))

/-- Exact reduction of the reduced loss on a cone patch to a radial/angular integral.
The radial power n is derived from the (n+1)-dimensional Jacobian and product volume. -/
theorem cancellationModel_projective_integrableOn_iff {n : ℕ} (r : ℕ) (j : Fin (n + 1))
    {R : Set ℝ} (hR : MeasurableSet R) (hpos : ∀ ρ ∈ R, 0 < ρ)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D)
    (hbound : ∀ y ∈ D, ∀ i, |y i| ≤ 1) (s : ℝ) :
    IntegrableOn (fun w => cancellationModel r w ^ (-s)) (projectiveConePatch j R D) volume ↔
      IntegrableOn (fun z : ℝ × (Fin n → ℝ) =>
        weightedCancellation (n + 1) r r s (z.1, angularFermat r 1 z.2)) (R ×ˢ D) volume := by
  let M := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
  have hfst (z : Fin (n + 1) → ℝ) : (M z).1 = z j := rfl
  have hsnd (z : Fin (n + 1) → ℝ) : (M z).2 = fun i => z (j.succAbove i) := rfl
  have hdom : MeasurableSet (M ⁻¹' (R ×ˢ D)) := (hR.prod hD).preimage M.measurable
  have hp : ∀ z ∈ M ⁻¹' (R ×ˢ D), 0 < z j := fun z hz => hpos _ hz.1
  have ha : ∀ z ∈ M ⁻¹' (R ×ˢ D), ∀ i, i ≠ j → |z i| ≤ 1 := by
    intro z hz i hi
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
    exact hbound _ hz.2 k
  change IntegrableOn _ (radialBlowup j '' (M ⁻¹' (R ×ˢ D))) volume ↔ _
  rw [cancellationModel_on_radial_patch_iff r j hdom hp ha s]
  change IntegrableOn _ _ (volume.withDensity
    (fun z : Fin (n + 1) → ℝ => (Real.toNNReal (z j ^ (n + 1 - 1)) : ENNReal))) ↔ _
  rw [integrableOn_withDensity_iff_weighted hdom (by fun_prop)]
  have heq : EqOn (fun z : Fin (n + 1) → ℝ =>
      (Real.toNNReal (z j ^ (n + 1 - 1)) : ℝ) *
        (z j ^ (2 * r) * (weightPowerSum r (Function.update z j 1) ^ 2 + z j ^ (2 * r))) ^ (-s))
      ((fun z : ℝ × (Fin n → ℝ) =>
        weightedCancellation (n + 1) r r s (z.1, angularFermat r 1 z.2)) ∘ M)
      (M ⁻¹' (R ×ˢ D)) := by
    intro z hz
    dsimp only [Function.comp_def]
    rw [Real.coe_toNNReal _ (pow_nonneg (hp z hz).le _)]
    rw [hfst, hsnd, weightPowerSum_fixed_coordinate]
    simp [weightedCancellation, Real.rpow_natCast]
  rw [integrableOn_congr_fun heq hdom]
  exact (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j).integrableOn_comp_preimage M.measurableEmbedding

/-- The reduced loss is now connected to the certified two-variable integrand, with
unused angular coordinates and the true transformed image kept in the statement. -/
theorem cancellationModel_transverse_cone_iff {n : ℕ} (r : ℕ) (j : Fin (n + 1))
    (c : TransverseChart (@angularFermat r 1 n))
    {R : Set ℝ} (hR : MeasurableSet R) (hpos : ∀ ρ ∈ R, 0 < ρ)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D)
    (hbound : ∀ y ∈ D, ∀ i, |y i| ≤ 1) (hsub : D ⊆ c.chart.source) (s : ℝ) :
    IntegrableOn (fun w => cancellationModel r w ^ (-s)) (projectiveConePatch j R D) volume ↔
      IntegrableOn (fun z : ℝ × (Fin n → ℝ) =>
        weightedCancellation (n + 1) r r s (z.1, z.2 c.index))
        (R ×ˢ (c.chart '' D)) volume := by
  rw [cancellationModel_projective_integrableOn_iff r j hR hpos hD hbound s]
  exact weightedAngular_chart_iff (angularFermat_contDiff r n 1) c hR hD hsub (n + 1) r s

/-- Cone images are measurable by the differentiable injective image theorem. -/
theorem projectiveConePatch_measurableSet {n : ℕ} (j : Fin (n + 1))
    {R : Set ℝ} (hR : MeasurableSet R) (hpos : ∀ ρ ∈ R, 0 < ρ)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D) :
    MeasurableSet (projectiveConePatch j R D) := by
  apply measurable_image_of_fderivWithin
    ((hR.prod hD).preimage (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j).measurable)
    (fun z _ => (radialBlowup_hasFDerivAt j z).hasFDerivWithinAt)
  apply (radialBlowup_injOn j).mono
  intro z hz
  exact (hpos _ hz.1).ne'

/-- Bounded angular coordinates place every chart image inside the intended raw ball. -/
theorem projectiveConePatch_subset_ball {n : ℕ} (j : Fin (n + 1))
    {R : Set ℝ} (hpos : ∀ ρ ∈ R, 0 < ρ) {ε : ℝ} (hRε : ∀ ρ ∈ R, ρ < ε)
    {D : Set (Fin n → ℝ)} (hbound : ∀ y ∈ D, ∀ i, |y i| ≤ 1) :
    projectiveConePatch j R D ⊆ Metric.ball 0 ε := by
  rintro w ⟨z, hz, rfl⟩
  have hp : 0 < z j := hpos _ hz.1
  have hnorm : ‖radialBlowup j z‖ ≤ z j := by
    apply (pi_norm_le_iff_of_nonneg hp.le).mpr
    intro i
    by_cases hi : i = j
    · simp [radialBlowup, hi, Real.norm_eq_abs, abs_of_pos hp]
    · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hi
      have hb : |z i| ≤ 1 := by rw [← hk]; exact hbound _ hz.2 k
      simpa [radialBlowup, hi, Real.norm_eq_abs, abs_mul, abs_of_pos hp] using
        mul_le_mul_of_nonneg_left hb hp.le
  exact mem_ball_zero_iff.mpr (hnorm.trans_lt (hRε _ hz.1))

/-- The signed network comparison applies on arbitrary measurable subsets of the unit ball,
including the actual cone-chart images, with the same bounded positive prior assumptions. -/
theorem signed_network_prior_integrableOn_iff_model_on_subset (μ : Measure ℝ)
    (r : ℕ) (hr : 2 ≤ r) (L : ℕ) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    {D : Set (Fin L → ℝ)} (hD : MeasurableSet D) (hsub : D ⊆ Metric.ball 0 1)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ D volume) (s : ℝ) :
    IntegrableOn (fun w => networkPopulationLoss μ r w ^ (-s)) D
      (volume.withDensity (fun w => (ρ w : ENNReal))) ↔
      IntegrableOn (fun w => cancellationModel r w ^ (-s)) D volume := by
  rw [integrableOn_withDensity_iff_of_boundedPositive hD hρ]
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  obtain ⟨c, C, hc, hC, hb⟩ := signed_network_loss_comparison μ r hr L hL h
  apply integrableOn_rpow_iff_of_comparable_all
    (cancellationModel_continuous r L).measurable.aemeasurable
    (networkPopulationLoss_continuous μ r hr L hL h).measurable.aemeasurable _ hc hC _ _ s
  · filter_upwards [ae_restrict_of_ae ((volume : Measure (Fin L → ℝ)).ae_ne 0)] with w hw
    exact cancellationModel_pos r L w hw
  · filter_upwards [ae_restrict_mem hD] with w hw
    exact (hb w (hsub hw)).1
  · filter_upwards [ae_restrict_mem hD] with w hw
    exact (hb w (hsub hw)).2

/-- End-to-end local chart reduction for the actual population loss and positive prior.
The right side is the weighted model on a genuine angular image, with no numeric threshold
assumed and no assertion that this image is a rectangle or that one chart covers the sphere. -/
theorem signed_network_prior_transverse_cone_iff (μ : Measure ℝ) {n : ℕ}
    (r : ℕ) (hr : 2 ≤ r) (h : FinitePositiveFeatureGram μ (networkFeatures r (n + 1)))
    (j : Fin (n + 1)) (c : TransverseChart (@angularFermat r 1 n))
    {R : Set ℝ} (hR : MeasurableSet R) (hpos : ∀ t ∈ R, 0 < t) (hR1 : ∀ t ∈ R, t < 1)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D)
    (hbound : ∀ y ∈ D, ∀ i, |y i| ≤ 1) (hsub : D ⊆ c.chart.source)
    (ρ : (Fin (n + 1) → ℝ) → NNReal)
    (hρ : BoundedPositivePriorOn ρ (projectiveConePatch j R D) volume) (s : ℝ) :
    IntegrableOn (fun w => networkPopulationLoss μ r w ^ (-s)) (projectiveConePatch j R D)
      (volume.withDensity (fun w => (ρ w : ENNReal))) ↔
      IntegrableOn (fun z : ℝ × (Fin n → ℝ) =>
        weightedCancellation (n + 1) r r s (z.1, z.2 c.index))
        (R ×ˢ (c.chart '' D)) volume := by
  rw [signed_network_prior_integrableOn_iff_model_on_subset μ r hr (n + 1) (by omega) h
    (projectiveConePatch_measurableSet j hR hpos hD)
    (projectiveConePatch_subset_ball j hpos hR1 hbound) ρ hρ s]
  exact cancellationModel_transverse_cone_iff r j c hR hpos hD hbound hsub s

end ResidualSLT
