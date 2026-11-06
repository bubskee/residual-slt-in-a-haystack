module
public import ResidualSLT.PriorMeasure
public import Mathlib.MeasureTheory.Integral.Prod

/-! Product integrability and exact normal-crossing power thresholds.
Nonzero factors and nonzero measures are explicit; no multiplicity is inferred. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Set
open scoped NNReal ENNReal

/-- Fubini's a.e. integrable sections give the converse to product integrability. -/
theorem integrable_prod_mul_iff_of_ae_ne_zero
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (hμ : μ ≠ 0) (hν : ν ≠ 0) {f : α → ℝ} {g : β → ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0) (hg : ∀ᵐ y ∂ν, g y ≠ 0) :
    Integrable (fun z : α × β => f z.1 * g z.2) (μ.prod ν) ↔
      Integrable f μ ∧ Integrable g ν := by
  let : NeZero μ := ⟨hμ⟩
  let : NeZero ν := ⟨hν⟩
  constructor
  · intro h
    obtain ⟨y, hy, hgy⟩ := (h.prod_left_ae.and hg).exists
    obtain ⟨x, hx, hfx⟩ := (h.prod_right_ae.and hf).exists
    constructor
    · apply (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hgy) f).mp
      simpa only [mul_comm] using hy
    · exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hfx) g).mp hx
  · rintro ⟨hf', hg'⟩
    exact hf'.mul_prod hg'

/-- Exact threshold for x^(2a)y^(2b) on a full square; all real s are allowed. -/
theorem productPowers_integrableOn_iff (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    IntegrableOn (fun z : ℝ × ℝ => (z.1 ^ (2 * a) * z.2 ^ (2 * b)) ^ (-s))
      ((Ioo (-ε) ε) ×ˢ (Ioo (-ε) ε)) volume ↔
      s < min (1 / (2 * (a : ℝ))) (1 / (2 * (b : ℝ))) := by
  have hμ : (volume.restrict (Ioo (-ε) ε) : Measure ℝ) ≠ 0 := by
    intro hzero
    have hp : 0 < (volume : Measure ℝ) (Ioo (-ε) ε) := by
      rw [Real.volume_Ioo, ENNReal.ofReal_pos]
      linarith
    exact hp.ne' (Measure.restrict_eq_zero.mp hzero)
  have hpow (r : ℕ) : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Ioo (-ε) ε),
      (x ^ (2 * r)) ^ (-s) ≠ 0 := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with x hx
    exact (Real.rpow_pos_of_pos (by rw [pow_mul]; exact pow_pos (sq_pos_of_ne_zero hx) r) _).ne'
  have heq : (fun z : ℝ × ℝ => (z.1 ^ (2 * a) * z.2 ^ (2 * b)) ^ (-s)) =
      fun z => (z.1 ^ (2 * a)) ^ (-s) * (z.2 ^ (2 * b)) ^ (-s) := by
    funext z
    apply Real.mul_rpow <;> rw [pow_mul] <;> positivity
  rw [heq, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict,
    integrable_prod_mul_iff_of_ae_ne_zero hμ hμ (hpow a) (hpow b)]
  change (IntegrableOn _ _ volume ∧ IntegrableOn _ _ volume) ↔ _
  rw [monomial_integrableOn_symmetric_iff a ha ε hε s,
    monomial_integrableOn_symmetric_iff b hb ε hε s, lt_min_iff]

/-- A normal-crossing model with threshold min(1/(2a),1/(2b)), not a pole certificate. -/
theorem productPowers_threshold (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (ε : ℝ) (hε : 0 < ε) :
    HasIntegrabilityThresholdOn (fun z : ℝ × ℝ => z.1 ^ (2 * a) * z.2 ^ (2 * b))
      ((Ioo (-ε) ε) ×ˢ (Ioo (-ε) ε)) volume
      (min (1 / (2 * (a : ℝ))) (1 / (2 * (b : ℝ)))) := by
  constructor
  · rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [(monomial_thresholdOn_symmetric a ha ε hε).1] with x hx
    filter_upwards [(monomial_thresholdOn_symmetric b hb ε hε).1] with y hy
    exact mul_pos hx hy
  · intro s _
    exact productPowers_integrableOn_iff a b ha hb ε hε s
/-- Locally bounded positive priors preserve the product-monomial criterion. -/
theorem productPowers_prior_integrableOn_iff (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (ε : ℝ) (hε : 0 < ε) (ρ : (ℝ × ℝ) → ℝ≥0)
    (hρ : BoundedPositivePriorOn ρ ((Ioo (-ε) ε) ×ˢ (Ioo (-ε) ε)) volume) (s : ℝ) :
    IntegrableOn (fun z : ℝ × ℝ => (z.1 ^ (2 * a) * z.2 ^ (2 * b)) ^ (-s))
      ((Ioo (-ε) ε) ×ˢ (Ioo (-ε) ε))
      (volume.withDensity (fun z => (ρ z : ℝ≥0∞))) ↔
      s < min (1 / (2 * (a : ℝ))) (1 / (2 * (b : ℝ))) := by
  rw [integrableOn_withDensity_iff_of_boundedPositive (measurableSet_Ioo.prod measurableSet_Ioo) hρ]
  exact productPowers_integrableOn_iff a b ha hb ε hε s
end ResidualSLT
