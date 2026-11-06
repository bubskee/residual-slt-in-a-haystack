module
public import ResidualSLT.Integrability
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! Positive prior densities change the parameter measure, not the loss.
All bounds are local and almost everywhere. No probability normalization or smoothness
is required. Finite nonnegative densities are represented by `ℝ≥0`. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Set
open scoped NNReal ENNReal

/-- A measurable density with finite upper and strictly positive lower bounds on D.
No bounds or positivity are required outside D. -/
structure BoundedPositivePriorOn {α : Type*} [MeasurableSpace α]
    (ρ : α → ℝ≥0) (D : Set α) (μ : Measure α) : Prop where
  measurable : Measurable ρ
  bounds : ∃ c C : ℝ≥0, 0 < c ∧
    ∀ᵐ x ∂μ.restrict D, c ≤ ρ x ∧ ρ x ≤ C

/-- The conventional prior-weighted integrand is exactly integrability under withDensity. -/
theorem integrableOn_withDensity_iff_weighted {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {D : Set α} {ρ : α → ℝ≥0} {f : α → ℝ}
    (hD : MeasurableSet D) (hρ : Measurable ρ) :
    IntegrableOn f D (μ.withDensity (fun x => (ρ x : ℝ≥0∞))) ↔
      IntegrableOn (fun x => (ρ x : ℝ) * f x) D μ := by
  unfold IntegrableOn
  rw [restrict_withDensity hD]
  exact integrable_withDensity_iff_integrable_coe_smul hρ

/-- Two-sided local density bounds preserve integrability of every real integrand.
The proof uses measure domination; in particular it also transfers non-integrability. -/
theorem integrableOn_withDensity_iff_of_boundedPositive {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {D : Set α} {ρ : α → ℝ≥0} {f : α → ℝ}
    (hD : MeasurableSet D) (hρ : BoundedPositivePriorOn ρ D μ) :
    IntegrableOn f D (μ.withDensity (fun x => (ρ x : ℝ≥0∞))) ↔
      IntegrableOn f D μ := by
  rcases hρ.bounds with ⟨c, C, hc, hb⟩
  have hl : (c : ℝ≥0∞) • μ.restrict D ≤
      (μ.restrict D).withDensity (fun x => (ρ x : ℝ≥0∞)) := by
    rw [← withDensity_const]
    exact withDensity_mono (hb.mono fun x hx => ENNReal.coe_le_coe.mpr hx.1)
  have hu : (μ.restrict D).withDensity (fun x => (ρ x : ℝ≥0∞)) ≤
      (C : ℝ≥0∞) • μ.restrict D := by
    rw [← withDensity_const]
    exact withDensity_mono (hb.mono fun x hx => ENNReal.coe_le_coe.mpr hx.2)
  unfold IntegrableOn
  rw [restrict_withDensity hD]
  constructor
  · intro hf
    exact (integrable_smul_measure (by exact_mod_cast ne_of_gt hc)
      ENNReal.coe_ne_top).mp (hf.mono_measure hl)
  · intro hf
    exact (hf.smul_measure ENNReal.coe_ne_top).mono_measure hu

/-- The threshold, including a.e. strict positivity, transfers to the prior measure. -/
theorem HasIntegrabilityThresholdOn.withDensity {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {D : Set α} {ρ : α → ℝ≥0} {K : α → ℝ} {t : ℝ}
    (h : HasIntegrabilityThresholdOn K D μ t) (hD : MeasurableSet D)
    (hρ : BoundedPositivePriorOn ρ D μ) :
    HasIntegrabilityThresholdOn K D (μ.withDensity (fun x => (ρ x : ℝ≥0∞))) t := by
  constructor
  · rw [restrict_withDensity hD]
    exact (withDensity_absolutelyContinuous _ _).ae_le h.1
  · intro s hs
    rw [integrableOn_withDensity_iff_of_boundedPositive hD hρ]
    exact h.2 s hs
end ResidualSLT
