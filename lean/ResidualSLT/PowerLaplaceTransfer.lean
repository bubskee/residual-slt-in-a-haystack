module
public import ResidualSLT.PowerLaplaceOrder
public import ResidualSLT.PriorMeasure

/-! Quantitative Laplace order is preserved by two-sided loss and prior comparisons. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Filter
variable {ℓ : ℝ}

/-- Comparable losses have the same power Laplace order. The proof rescales N,
not a power-integrability exponent. -/
theorem power_laplace_order_of_comparable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (D : Set α) (K J : α → ℝ)
    (hiK : ∀ N : ℝ, IntegrableOn (fun x => Real.exp (-N*K x)) D μ)
    (hiJ : ∀ N : ℝ, IntegrableOn (fun x => Real.exp (-N*J x)) D μ)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ᵐ x ∂μ.restrict D, c*K x ≤ J x ∧ J x ≤ C*K x)
    (horder : HasPowerLaplaceOrder ℓ (fun N => ∫ x in D, Real.exp (-N*K x) ∂μ)) :
    HasPowerLaplaceOrder ℓ (fun N => ∫ x in D, Real.exp (-N*J x) ∂μ) := by
  constructor
  · apply (horder.1.comp_mul C hC).mono
    filter_upwards [eventually_ge_atTop (0:ℝ)] with N hN
    apply integral_mono_ae (hiK (C*N)) (hiJ N)
    filter_upwards [hb] with x hx
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hx.2 hN]
  · apply (horder.2.comp_mul c hc).mono
    filter_upwards [eventually_ge_atTop (0:ℝ)] with N hN
    apply integral_mono_ae (hiJ N) (hiK (c*N))
    filter_upwards [hb] with x hx
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hx.1 hN]

/-- A bounded positive measurable prior preserves numerical two-sided Laplace order. -/
theorem power_laplace_order_withDensity {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {D : Set α} (hD : MeasurableSet D) (K : α → ℝ)
    (hi : ∀ N : ℝ, IntegrableOn (fun x => Real.exp (-N*K x)) D μ)
    (ρ : α → NNReal) (hρ : BoundedPositivePriorOn ρ D μ)
    (horder : HasPowerLaplaceOrder ℓ (fun N => ∫ x in D, Real.exp (-N*K x) ∂μ)) :
    HasPowerLaplaceOrder ℓ (fun N => ∫ x in D, Real.exp (-N*K x)
      ∂μ.withDensity (fun x => (ρ x : ENNReal))) := by
  obtain ⟨c,C,hc,hb⟩ := hρ.bounds
  have hiw (N : ℝ) : IntegrableOn (fun x => (ρ x : ℝ) * Real.exp (-N*K x)) D μ :=
    (integrableOn_withDensity_iff_weighted hD hρ.measurable).mp
      ((integrableOn_withDensity_iff_of_boundedPositive hD hρ).mpr (hi N))
  have he (N : ℝ) : (∫ x in D, Real.exp (-N*K x) ∂μ.withDensity (fun x => (ρ x : ENNReal))) =
      ∫ x in D, (ρ x : ℝ) * Real.exp (-N*K x) ∂μ := by
    rw [setIntegral_withDensity_eq_setIntegral_smul₀ hρ.measurable.aemeasurable _ hD]
    rfl
  constructor
  · apply (horder.1.const_mul (c:ℝ) (by exact_mod_cast hc)).mono
    apply Filter.Eventually.of_forall
    intro N
    rw [he, ← integral_const_mul]
    apply integral_mono_ae ((hi N).const_mul _) (hiw N)
    filter_upwards [hb] with x hx
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hx.1) (Real.exp_pos _).le
  · apply (horder.2.const_mul ((C:ℝ)+1) (by positivity)).mono
    apply Filter.Eventually.of_forall
    intro N
    rw [he, ← integral_const_mul]
    apply integral_mono_ae (hiw N) ((hi N).const_mul _)
    filter_upwards [hb] with x hx
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have hh : (ρ x : ℝ) ≤ C := by exact_mod_cast hx.2
    linarith

end ResidualSLT
