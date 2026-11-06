module
public import ResidualSLT.RadialThreshold
public import ResidualSLT.PriorMeasure
public import Mathlib.MeasureTheory.Constructions.Pi

/-! Arbitrary-dimensional sums of even powers, with explicit Lebesgue and prior measures. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Metric
open scoped NNReal ENNReal

@[expose] def sumEvenPowers {L : ℕ} (r : ℕ) (w : Fin L → ℝ) : ℝ :=
  ∑ i, w i ^ (2 * r)

theorem sumEvenPowers_continuous (L r : ℕ) : Continuous (@sumEvenPowers L r) := by
  unfold sumEvenPowers
  fun_prop

theorem sumEvenPowers_pos (L r : ℕ) (w : Fin L → ℝ) (hw : w ≠ 0) :
    0 < sumEvenPowers r w := by
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra! hn
    exact hw (funext hn)
  apply Finset.sum_pos' (fun j _ => by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) r)
  exact ⟨i, Finset.mem_univ _, by rw [pow_mul]; exact pow_pos (sq_pos_of_ne_zero hi) r⟩

theorem sumEvenPowers_smul (L r : ℕ) (a : ℝ) (w : Fin L → ℝ) :
    sumEvenPowers r (a • w) = a ^ (2 * r) * sumEvenPowers r w := by
  simp [sumEvenPowers, mul_pow, Finset.mul_sum]

/-- Exact dimension/(2r) criterion on every full norm-ball neighborhood, for all real s. -/
theorem sumEvenPowers_integrableOn_iff (L : ℕ) (hL : 0 < L) (r : ℕ) (hr : 0 < r)
    (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    IntegrableOn (fun w : Fin L → ℝ => sumEvenPowers r w ^ (-s)) (ball 0 ε) volume ↔
      s < (L : ℝ) / (2 * r) := by
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  simpa using positive_homogeneous_integrableOn_iff (volume : Measure (Fin L → ℝ))
    (2 * r) (by omega) (sumEvenPowers_continuous L r) (sumEvenPowers_pos L r)
    (fun a _ w => sumEvenPowers_smul L r a w) ε hε s

/-- Reusable arbitrary-dimensional threshold, distinct from a pole multiplicity. -/
theorem sumEvenPowers_threshold (L : ℕ) (hL : 0 < L) (r : ℕ) (hr : 0 < r)
    (ε : ℝ) (hε : 0 < ε) :
    HasIntegrabilityThresholdOn (@sumEvenPowers L r) (ball 0 ε) volume ((L : ℝ) / (2 * r)) := by
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  simpa using positive_homogeneous_threshold (volume : Measure (Fin L → ℝ))
    (2 * r) (by omega) (sumEvenPowers_continuous L r) (sumEvenPowers_pos L r)
    (fun a _ w => sumEvenPowers_smul L r a w) ε hε

/-- The same all-real-exponent criterion under a locally bounded positive density. -/
theorem sumEvenPowers_prior_integrableOn_iff (L : ℕ) (hL : 0 < L) (r : ℕ) (hr : 0 < r)
    (ε : ℝ) (hε : 0 < ε) (ρ : (Fin L → ℝ) → ℝ≥0)
    (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) (s : ℝ) :
    IntegrableOn (fun w => sumEvenPowers r w ^ (-s)) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ℝ≥0∞))) ↔ s < (L : ℝ) / (2 * r) := by
  rw [integrableOn_withDensity_iff_of_boundedPositive measurableSet_ball hρ]
  exact sumEvenPowers_integrableOn_iff L hL r hr ε hε s
end ResidualSLT
