module
public import ResidualSLT.SignedNetwork
public import ResidualSLT.SumPowers
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Pi

/-! Fermat cancellation geometry. Differential regularity and radial comparisons
are proved here; a change-of-variables or angular integration theorem is not asserted. -/
public section
noncomputable section
namespace ResidualSLT
open Finset MeasureTheory Metric

/-- The actual Fréchet differential of the Fermat sum. -/
@[expose] def fermatDifferential (r : ℕ) {L : ℕ} (w : Fin L → ℝ) :
    (Fin L → ℝ) →L[ℝ] ℝ :=
  ∑ i, ((r : ℝ) * w i ^ (r - 1)) • ContinuousLinearMap.proj i

theorem weightPowerSum_hasFDerivAt (r L : ℕ) (w : Fin L → ℝ) :
    HasFDerivAt (weightPowerSum r) (fermatDifferential r w) w := by
  unfold weightPowerSum fermatDifferential
  simpa only [nsmul_eq_mul, ContinuousLinearMap.proj_apply] using
    HasFDerivAt.fun_sum (u := (univ : Finset (Fin L)))
      (fun i _ => ((ContinuousLinearMap.proj i : (Fin L → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := w)).pow r)

theorem fermatDifferential_apply (r L : ℕ) (w v : Fin L → ℝ) :
    fermatDifferential r w v = ∑ i, (r : ℝ) * w i ^ (r - 1) * v i := by
  simp [fermatDifferential]

/-- Euler's identity, at the level of the certified differential. -/
theorem fermatDifferential_radial (r L : ℕ) (hr : 0 < r) (w : Fin L → ℝ) :
    fermatDifferential r w w = (r : ℝ) * weightPowerSum r w := by
  rw [fermatDifferential_apply, weightPowerSum, mul_sum]
  apply sum_congr rfl
  intro i _
  rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hr]

/-- Every nonzero point has a nonzero Fermat differential, with no parity restriction. -/
theorem fermatDifferential_ne_zero (r L : ℕ) (hr : 0 < r)
    (w : Fin L → ℝ) (hw : w ≠ 0) : fermatDifferential r w ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra! hn
    exact hw (funext hn)
  intro hz
  have hval := congrArg (fun f : (Fin L → ℝ) →L[ℝ] ℝ => f (Pi.single i 1)) hz
  simp [fermatDifferential_apply, Pi.single_apply, mul_ite, Finset.sum_ite_eq',
    hr.ne', hi] at hval

/-- Zero is a regular value on the Euclidean sphere: a tangent vector changes S.
The sphere is specified by Σ wᵢ²=1, independently of the ambient maximum norm. -/
theorem fermat_sphere_transverse (r L : ℕ) (hr : 0 < r) (w : Fin L → ℝ)
    (hS : weightPowerSum r w = 0) (hSphere : weightPowerSum 2 w = 1) :
    ∃ v : Fin L → ℝ, fermatDifferential 2 w v = 0 ∧ fermatDifferential r w v ≠ 0 := by
  have hw : w ≠ 0 := by
    intro hz
    simp [hz, weightPowerSum] at hSphere
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra! hn
    exact hw (funext hn)
  have he (n : ℕ) : fermatDifferential n w (Pi.single i 1) =
      (n : ℝ) * w i ^ (n - 1) := by
    simp [fermatDifferential_apply, Pi.single_apply, mul_ite, Finset.sum_ite_eq']
  refine ⟨Pi.single i 1 - w i • w, ?_, ?_⟩
  · rw [map_sub, map_smul, he, fermatDifferential_radial 2 L (by norm_num), hSphere]
    simp; ring
  · rw [map_sub, map_smul, he, fermatDifferential_radial r L hr, hS]
    simpa using mul_ne_zero (Nat.cast_ne_zero.mpr hr.ne') (pow_ne_zero _ hi)

/-- The radial fourth-order term can be replaced uniformly by a norm power.
This is a pointwise comparison, not a polar-coordinate integration statement. -/
theorem cancellationModel_radial_comparison (r L : ℕ) (hr : 0 < r) (hL : 0 < L) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ w : Fin L → ℝ,
      c * (weightPowerSum r w ^ 2 + ‖w‖ ^ (4 * r)) ≤ cancellationModel r w ∧
      cancellationModel r w ≤ C * (weightPowerSum r w ^ 2 + ‖w‖ ^ (4 * r)) := by
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  obtain ⟨c, C, hc, hC, hb⟩ := positive_homogeneous_bounds
    (2 * r) (by omega) (sumEvenPowers_continuous L r) (sumEvenPowers_pos L r)
    (fun a _ w => sumEvenPowers_smul L r a w)
  refine ⟨min 1 (c ^ 2), max 1 (C ^ 2), lt_min zero_lt_one (sq_pos_of_pos hc),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro w
  have hQ0 := weightSquareSum_nonneg r L w
  have he : weightSquareSum r w = sumEvenPowers r w := weightSquareSum_eq r L w
  obtain ⟨hl, hu⟩ := hb w
  rw [← he] at hl hu
  have hl2 := pow_le_pow_left₀ (by positivity : 0 ≤ c * ‖w‖ ^ (2 * r)) hl 2
  have hu2 := pow_le_pow_left₀ hQ0 hu 2
  have hn : (‖w‖ ^ (2 * r)) ^ 2 = ‖w‖ ^ (4 * r) := by rw [← pow_mul]; congr 1; omega
  simp only [mul_pow, hn] at hl2 hu2
  unfold cancellationModel
  constructor
  · calc
      min 1 (c ^ 2) * (weightPowerSum r w ^ 2 + ‖w‖ ^ (4 * r)) ≤
          weightPowerSum r w ^ 2 + c ^ 2 * ‖w‖ ^ (4 * r) := by
        rw [mul_add]
        exact add_le_add (by simpa using mul_le_mul_of_nonneg_right (min_le_left 1 (c ^ 2)) (sq_nonneg _))
          (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
      _ ≤ _ := add_le_add_right hl2 _
  · calc
      _ ≤ weightPowerSum r w ^ 2 + C ^ 2 * ‖w‖ ^ (4 * r) := add_le_add_right hu2 _
      _ ≤ max 1 (C ^ 2) * (weightPowerSum r w ^ 2 + ‖w‖ ^ (4 * r)) := by
        rw [mul_add]
        exact add_le_add (by simpa using mul_le_mul_of_nonneg_right (le_max_left 1 (C ^ 2)) (sq_nonneg _))
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

/-- Odd Fermat cancellation occurs on the Euclidean sphere in every dimension at least two. -/
theorem odd_fermat_sphere_nonempty (r L : ℕ) (hr : Odd r) (hL : 2 ≤ L) :
    ∃ w : Fin L → ℝ, weightPowerSum r w = 0 ∧ weightPowerSum 2 w = 1 := by
  let i : Fin L := ⟨0, by omega⟩
  let j : Fin L := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  let v : Fin L → ℝ := fun k => if k = i then 1 else if k = j then -1 else 0
  have hv (n : ℕ) (hn : 0 < n) : weightPowerSum n v = 1 + (-1 : ℝ) ^ n := by
    have hfilter : Finset.filter (fun k : Fin L => k = i) univ = {i} := by ext; simp
    simp [weightPowerSum, v, ite_pow, hn.ne', Finset.sum_ite, Ne.symm hij, hfilter]
  have hS : weightPowerSum r v = 0 := by rw [hv r hr.pos, hr.neg_one_pow]; norm_num
  have hQ : weightPowerSum 2 v = 2 := by rw [hv 2 (by norm_num)]; norm_num
  refine ⟨(Real.sqrt 2)⁻¹ • v, ?_, ?_⟩
  · rw [weightPowerSum_smul, hS, mul_zero]
  · rw [weightPowerSum_smul, hQ, inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num

/-- Exact integrability transfer to S²+‖w‖^(4r); the angular reduction remains separate. -/
theorem cancellationModel_integrableOn_iff_radial (r L : ℕ) (hr : 0 < r) (hL : 0 < L)
    (ε s : ℝ) :
    IntegrableOn (fun w : Fin L → ℝ => cancellationModel r w ^ (-s)) (ball 0 ε) volume ↔
      IntegrableOn (fun w : Fin L → ℝ =>
        (weightPowerSum r w ^ 2 + ‖w‖ ^ (4 * r)) ^ (-s)) (ball 0 ε) volume := by
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  obtain ⟨c, C, hc, hC, hb⟩ := cancellationModel_radial_comparison r L hr hL
  apply integrableOn_rpow_iff_of_comparable_all (by unfold weightPowerSum; fun_prop)
    (cancellationModel_continuous r L).measurable.aemeasurable _ hc hC _ _ s
  · filter_upwards [ae_restrict_of_ae ((volume : Measure (Fin L → ℝ)).ae_ne 0)] with w hw
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos (norm_pos_iff.mpr hw) _)
  · exact Filter.Eventually.of_forall (fun w => (hb w).1)
  · exact Filter.Eventually.of_forall (fun w => (hb w).2)

/-- Actual population loss with a bounded positive prior reduces to the radial Fermat model.
No numeric odd-degree threshold is an assumption or conclusion. -/
theorem signed_network_prior_integrableOn_iff_radial (μ : Measure ℝ)
    (r : ℕ) (hr : 2 ≤ r) (L : ℕ) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε1 : ε ≤ 1) (ρ : (Fin L → ℝ) → NNReal)
    (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) (s : ℝ) :
    IntegrableOn (fun w => networkPopulationLoss μ r w ^ (-s)) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ENNReal))) ↔
      IntegrableOn (fun w : Fin L → ℝ =>
        (weightPowerSum r w ^ 2 + ‖w‖ ^ (4 * r)) ^ (-s)) (ball 0 ε) volume := by
  rw [signed_network_prior_integrableOn_iff_model μ r hr L hL h ε hε1 ρ hρ s]
  exact cancellationModel_integrableOn_iff_radial r L (by omega) hL ε s

end ResidualSLT
