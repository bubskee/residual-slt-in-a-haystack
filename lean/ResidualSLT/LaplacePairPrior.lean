module
public import ResidualSLT.LaplaceProduct

/-! Bounded positive priors preserve every power/logarithmic Laplace pair. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Set

theorem laplace_pair_order_withDensity {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {D : Set α} (hD : MeasurableSet D) (K : α → ℝ)
    (hi : ∀ N : ℝ, IntegrableOn (fun x => Real.exp (-N*K x)) D μ)
    (ρ : α → NNReal) (hρ : BoundedPositivePriorOn ρ D μ)
    {a : ℝ} {m : ℕ}
    (horder : HasLaplaceOrder a m (fun N => ∫ x in D, Real.exp (-N*K x) ∂μ)) :
    HasLaplaceOrder a m (fun N => ∫ x in D, Real.exp (-N*K x)
      ∂μ.withDensity (fun x => (ρ x : ENNReal))) := by
  obtain ⟨b,B,hb,hρb⟩ := hρ.bounds
  have hiw (N : ℝ) : IntegrableOn (fun x => (ρ x : ℝ)*Real.exp (-N*K x)) D μ :=
    (integrableOn_withDensity_iff_weighted hD hρ.measurable).mp
      ((integrableOn_withDensity_iff_of_boundedPositive hD hρ).mpr (hi N))
  have he (N : ℝ) : (∫ x in D, Real.exp (-N*K x) ∂μ.withDensity (fun x => (ρ x : ENNReal))) =
      ∫ x in D, (ρ x : ℝ)*Real.exp (-N*K x) ∂μ := by
    rw [setIntegral_withDensity_eq_setIntegral_smul₀ hρ.measurable.aemeasurable _ hD]
    rfl
  have hl (N : ℝ) : (b:ℝ)*(∫ x in D, Real.exp (-N*K x) ∂μ) ≤
      ∫ x in D, Real.exp (-N*K x) ∂μ.withDensity (fun x => (ρ x : ENNReal)) := by
    rw [he,← integral_const_mul]
    apply integral_mono_ae ((hi N).const_mul _) (hiw N)
    filter_upwards [hρb] with x hx
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hx.1) (Real.exp_pos _).le
  have hu (N : ℝ) : (∫ x in D, Real.exp (-N*K x) ∂μ.withDensity (fun x => (ρ x : ENNReal))) ≤
      ((B:ℝ)+1)*(∫ x in D, Real.exp (-N*K x) ∂μ) := by
    rw [he,← integral_const_mul]
    apply integral_mono_ae (hiw N) ((hi N).const_mul _)
    filter_upwards [hρb] with x hx
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have hh : (ρ x : ℝ) ≤ B := by exact_mod_cast hx.2
    linarith
  obtain ⟨hm,c,C,N₀,hc,hC,hN₀,hZ⟩ := horder
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  refine ⟨hm,(b:ℝ)*c,((B:ℝ)+1)*C,N₀,by positivity,by positivity,hN₀,?_⟩
  intro N hN
  constructor
  · calc
      _ = (b:ℝ)*(c*laplaceRate a m N) := by ring
      _ ≤ (b:ℝ)*(∫ x in D, Real.exp (-N*K x) ∂μ) :=
        mul_le_mul_of_nonneg_left (hZ N hN).1 hb'.le
      _ ≤ _ := hl N
  · calc
      _ ≤ ((B:ℝ)+1)*(∫ x in D, Real.exp (-N*K x) ∂μ) := hu N
      _ ≤ ((B:ℝ)+1)*(C*laplaceRate a m N) :=
        mul_le_mul_of_nonneg_left (hZ N hN).2 (by positivity)
      _ = _ := by ring

end ResidualSLT
