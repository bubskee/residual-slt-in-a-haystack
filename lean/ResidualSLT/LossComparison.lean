module
public import ResidualSLT.Integrability
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Positive-factor invariance of integrability thresholds. All comparisons are a.e.
on an explicit restricted measure. No pole-order or Laplace-asymptotic claim is made. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Set
variable {α : Type*} [MeasurableSpace α] {K J U : α → ℝ}
  {D : Set α} {μ : Measure α} {c C threshold : ℝ}

/-- Multiplying a nonnegative loss by a positive constant preserves every power-integrability
condition, without assuming the loss is already integrable. -/
theorem integrableOn_rpow_const_mul_iff (hc : 0 < c)
    (hK : ∀ᵐ x ∂μ.restrict D, 0 ≤ K x) (s : ℝ) :
    IntegrableOn (fun x => (c * K x) ^ (-s)) D μ ↔
      IntegrableOn (fun x => K x ^ (-s)) D μ := by
  have heq : (fun x => (c * K x) ^ (-s)) =ᵐ[μ.restrict D]
      (fun x => c ^ (-s) * K x ^ (-s)) := by
    filter_upwards [hK] with x hx
    exact Real.mul_rpow hc.le hx
  rw [integrableOn_congr_fun_ae heq]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
    (Real.rpow_pos_of_pos hc (-s)).ne') _

/-- Positive scalar multiplication preserves the existing threshold predicate. -/
theorem HasIntegrabilityThresholdOn.const_mul
    (h : HasIntegrabilityThresholdOn K D μ threshold) (hc : 0 < c) :
    HasIntegrabilityThresholdOn (fun x => c * K x) D μ threshold := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1] with x hx
    exact mul_pos hc hx
  · intro s hs
    rw [integrableOn_rpow_const_mul_iff hc (h.1.mono fun _ hx => hx.le)]
    exact h.2 s hs

/-- Two-sided positive loss comparisons preserve integrability of every nonnegative
negative-power exponent. Measurability cannot be omitted from this assertion. -/
theorem integrableOn_rpow_iff_of_comparable
    (hK : AEMeasurable K (μ.restrict D)) (hJ : AEMeasurable J (μ.restrict D))
    (hKpos : ∀ᵐ x ∂μ.restrict D, 0 < K x) (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ᵐ x ∂μ.restrict D, c * K x ≤ J x)
    (hupper : ∀ᵐ x ∂μ.restrict D, J x ≤ C * K x)
    (s : ℝ) (hs : 0 ≤ s) :
    IntegrableOn (fun x => J x ^ (-s)) D μ ↔
      IntegrableOn (fun x => K x ^ (-s)) D μ := by
  have hJpos : ∀ᵐ x ∂μ.restrict D, 0 < J x := by
    filter_upwards [hKpos, hlower] with x hx hl
    exact lt_of_lt_of_le (mul_pos hc hx) hl
  have hKm : AEStronglyMeasurable (fun x => K x ^ (-s)) (μ.restrict D) :=
    (hK.pow_const (-s)).aestronglyMeasurable
  have hJm : AEStronglyMeasurable (fun x => J x ^ (-s)) (μ.restrict D) :=
    (hJ.pow_const (-s)).aestronglyMeasurable
  constructor
  · intro hInt
    have hInt' : Integrable (fun x => C ^ (-s) * K x ^ (-s)) (μ.restrict D) := by
      apply hInt.mono_nonneg (hKm.const_mul _) _ _
      · filter_upwards [hKpos] with x hx
        exact mul_nonneg (Real.rpow_pos_of_pos hC _).le (Real.rpow_nonneg hx.le _)
      · filter_upwards [hKpos, hJpos, hupper] with x hx hj hu
        rw [← Real.mul_rpow hC.le hx.le]
        exact Real.rpow_le_rpow_of_nonpos hj hu (neg_nonpos.mpr hs)
    exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
      (Real.rpow_pos_of_pos hC (-s)).ne') _).mp hInt'
  · intro hInt
    apply (hInt.const_mul (c ^ (-s))).mono_nonneg hJm _ _
    · filter_upwards [hJpos] with x hx
      exact Real.rpow_nonneg hx.le _
    · filter_upwards [hKpos, hlower] with x hx hl
      rw [← Real.mul_rpow hc.le hx.le]
      exact Real.rpow_le_rpow_of_nonpos (mul_pos hc hx) hl (neg_nonpos.mpr hs)

/-- Transfer a threshold along a two-sided comparison on the same domain and measure. -/
theorem HasIntegrabilityThresholdOn.of_comparable
    (h : HasIntegrabilityThresholdOn K D μ threshold)
    (hK : AEMeasurable K (μ.restrict D)) (hJ : AEMeasurable J (μ.restrict D))
    (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ᵐ x ∂μ.restrict D, c * K x ≤ J x)
    (hupper : ∀ᵐ x ∂μ.restrict D, J x ≤ C * K x) :
    HasIntegrabilityThresholdOn J D μ threshold := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1, hlower] with x hx hl
    exact lt_of_lt_of_le (mul_pos hc hx) hl
  · intro s hs
    rw [integrableOn_rpow_iff_of_comparable hK hJ h.1 hc hC hlower hupper s hs]
    exact h.2 s hs

/-- A measurable loss factor bounded above and below by positive constants preserves
its threshold. Bounds and measurability are needed only a.e. on the chosen domain. -/
theorem HasIntegrabilityThresholdOn.mul_bounded
    (h : HasIntegrabilityThresholdOn K D μ threshold)
    (hK : AEMeasurable K (μ.restrict D)) (hU : AEMeasurable U (μ.restrict D))
    (hc : 0 < c) (hC : 0 < C)
    (hbound : ∀ᵐ x ∂μ.restrict D, c ≤ U x ∧ U x ≤ C) :
    HasIntegrabilityThresholdOn (fun x => U x * K x) D μ threshold := by
  apply h.of_comparable hK (hU.mul hK) hc hC
  · filter_upwards [h.1, hbound] with x hx hb
    exact mul_le_mul_of_nonneg_right hb.1 hx.le
  · filter_upwards [h.1, hbound] with x hx hb
    exact mul_le_mul_of_nonneg_right hb.2 hx.le
/-- Two-sided positive comparisons also preserve power integrability for negative s.
This extends the original nonnegative-exponent interface without changing it. -/
theorem integrableOn_rpow_iff_of_comparable_all
    (hK : AEMeasurable K (μ.restrict D)) (hJ : AEMeasurable J (μ.restrict D))
    (hKpos : ∀ᵐ x ∂μ.restrict D, 0 < K x) (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ᵐ x ∂μ.restrict D, c * K x ≤ J x)
    (hupper : ∀ᵐ x ∂μ.restrict D, J x ≤ C * K x) (s : ℝ) :
    IntegrableOn (fun x => J x ^ (-s)) D μ ↔
      IntegrableOn (fun x => K x ^ (-s)) D μ := by
  by_cases hs : 0 ≤ s
  · exact integrableOn_rpow_iff_of_comparable hK hJ hKpos hc hC hlower hupper s hs
  have hs' : 0 ≤ -s := by linarith
  have hJpos : ∀ᵐ x ∂μ.restrict D, 0 < J x := by
    filter_upwards [hKpos, hlower] with x hx hl
    exact lt_of_lt_of_le (mul_pos hc hx) hl
  constructor
  · intro hInt
    have hi : Integrable (fun x => c ^ (-s) * K x ^ (-s)) (μ.restrict D) := by
      apply hInt.mono_nonneg ((hK.pow_const (-s)).aestronglyMeasurable.const_mul _) _ _
      · filter_upwards [hKpos] with x hx
        exact mul_nonneg (Real.rpow_pos_of_pos hc _).le (Real.rpow_nonneg hx.le _)
      · filter_upwards [hKpos, hlower] with x hx hl
        rw [← Real.mul_rpow hc.le hx.le]
        exact Real.rpow_le_rpow (mul_pos hc hx).le hl hs'
    exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
      (Real.rpow_pos_of_pos hc (-s)).ne') _).mp hi
  · intro hInt
    apply (hInt.const_mul (C ^ (-s))).mono_nonneg (hJ.pow_const (-s)).aestronglyMeasurable _ _
    · filter_upwards [hJpos] with x hx
      exact Real.rpow_nonneg hx.le _
    · filter_upwards [hKpos, hJpos, hupper] with x hx hj hu
      rw [← Real.mul_rpow hC.le hx.le]
      exact Real.rpow_le_rpow hj.le hu hs'
end ResidualSLT
