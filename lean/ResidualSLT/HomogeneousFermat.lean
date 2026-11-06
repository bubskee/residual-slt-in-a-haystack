module
public import ResidualSLT.HomogeneousCone
public import ResidualSLT.OddNetwork

/-! Fermat and actual-network specializations of the general homogeneous theorem.
These proofs do not invoke the existing odd-network numerical threshold. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Metric

/-- Recover the Fermat norm model in every dimension with a nonempty cancellation cone. -/
theorem odd_fermat_integrableOn_iff_via_homogeneous (r L : ℕ)
    (hr : 0 < r) (hodd : Odd r) (hL : 2 ≤ L)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ) :
    IntegrableOn (fun w : Fin L → ℝ =>
      (weightPowerSum r w ^ 2 + ‖w‖ ^ (4 * r)) ^ (-s)) (ball 0 ε) volume ↔
      s < min ((L : ℝ) / (2 * r)) (((L : ℝ) + r) / (4 * r)) := by
  have hf : ContDiff ℝ 1 (@weightPowerSum r L) := by unfold weightPowerSum; fun_prop
  have hreg : ∀ w : Fin L → ℝ, w ≠ 0 → weightPowerSum r w = 0 →
      fderiv ℝ (weightPowerSum r) w ≠ 0 := by
    intro w hw _
    rw [(weightPowerSum_hasFDerivAt r L w).fderiv]
    exact fermatDifferential_ne_zero r L hr w hw
  obtain ⟨w, hw, hnorm⟩ := odd_fermat_sphere_nonempty r L hodd hL
  have hzero : ∃ w : Fin L → ℝ, w ≠ 0 ∧ weightPowerSum r w = 0 := by
    refine ⟨w, ?_, hw⟩
    intro he
    simp [he, weightPowerSum] at hnorm
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 2 := ⟨L - 2, by omega⟩
  have hi := homogeneousConeLoss_integrableOn_iff n r r hr hr (weightPowerSum r) hf
    (weightPowerSum_smul r (n + 2)) hreg hzero ε hε hε1 s
  simpa only [homogeneousConeLoss, show 2 * (r + r) = 4 * r by omega,
    show 2 * ((r : ℝ) + r) = 4 * r by ring, Nat.cast_add, Nat.cast_ofNat] using hi

/-- The actual population loss and prior inherit the odd-degree threshold from the
new homogeneous theorem, through the previously certified signed loss comparison. -/
theorem odd_network_prior_integrableOn_iff_via_homogeneous (μ : Measure ℝ)
    (r L : ℕ) (hr : 3 ≤ r) (hodd : Odd r) (hL : 2 ≤ L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (p : (Fin L → ℝ) → NNReal) (hp : BoundedPositivePriorOn p (ball 0 ε) volume)
    (s : ℝ) :
    IntegrableOn (fun w => networkPopulationLoss μ r w ^ (-s)) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal))) ↔
      s < min ((L : ℝ) / (2 * r)) (((L : ℝ) + r) / (4 * r)) := by
  rw [signed_network_prior_integrableOn_iff_radial μ r (by omega) L (by omega)
    h ε hε1 p hp s]
  exact odd_fermat_integrableOn_iff_via_homogeneous r L (by omega) hodd hL ε hε hε1 s


/-- All positive depths: the new cone theorem handles L≥2; L=1 uses the preserved
one-dimensional reduced-loss certificate, since its cancellation sphere is empty. -/
theorem odd_network_prior_all_depths_via_homogeneous (μ : Measure ℝ)
    (r L : ℕ) (hr : 3 ≤ r) (hodd : Odd r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (p : (Fin L → ℝ) → NNReal) (hp : BoundedPositivePriorOn p (ball 0 ε) volume)
    (s : ℝ) :
    IntegrableOn (fun w => networkPopulationLoss μ r w ^ (-s)) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal))) ↔
      s < min ((L : ℝ) / (2 * r)) (((L : ℝ) + r) / (4 * r)) := by
  by_cases hL2 : 2 ≤ L
  · exact odd_network_prior_integrableOn_iff_via_homogeneous μ r L hr hodd hL2 h ε hε hε1 p hp s
  · have hL1 : L = 1 := by omega
    subst L
    rw [signed_network_prior_integrableOn_iff_model μ r (by omega) 1 (by omega)
      h ε hε1 p hp s, cancellationModel_one_integrableOn_iff r (by omega) ε hε hε1 s]
    have hr' : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    rw [min_eq_left]
    · norm_num
    · rw [div_le_div_iff₀ (by positivity : 0 < 2 * (r : ℝ)) (by positivity : 0 < 4 * (r : ℝ))]
      have hh : (3 : ℝ) ≤ r := by exact_mod_cast hr
      norm_num only [Nat.cast_one]
      nlinarith

end ResidualSLT
