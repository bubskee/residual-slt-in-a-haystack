module
public import ResidualSLT.ProductPowers
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-! A logarithmic calculation for a normal crossing, with a precise cutoff convention.
This is a critical-power cutoff integral, not a Laplace asymptotic or pole multiplicity. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Set Filter Asymptotics
open scoped Topology

@[expose] def normalCrossingCutoff (δ : ℝ) : ℝ :=
  ∫ z : ℝ × ℝ in (Ioo δ 1) ×ˢ (Ioo δ 1), (z.1 ^ 2 * z.2 ^ 2) ^ (-(1 / 2 : ℝ))

/-- The cutoff kernel is integrable; its totalized Bochner integral is therefore ordinary. -/
theorem normalCrossingCutoff_integrable (δ : ℝ) (hδ : 0 < δ) :
    IntegrableOn (fun z : ℝ × ℝ => (z.1 ^ 2 * z.2 ^ 2) ^ (-(1 / 2 : ℝ)))
      ((Ioo δ 1) ×ˢ (Ioo δ 1)) volume := by
  have hc : ContinuousOn (fun x : ℝ => x⁻¹) (Icc δ 1) :=
    continuousOn_id.inv₀ (fun x hx => ne_of_gt (lt_of_lt_of_le hδ hx.1))
  have hi : IntegrableOn (fun x : ℝ => x⁻¹) (Ioo δ 1) volume :=
    (hc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hp : IntegrableOn (fun z : ℝ × ℝ => z.1⁻¹ * z.2⁻¹)
      ((Ioo δ 1) ×ˢ (Ioo δ 1)) volume := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact hi.mul_prod hi
  apply hp.congr_fun _ (measurableSet_Ioo.prod measurableSet_Ioo)
  intro z hz
  have he {x : ℝ} (hx : 0 < x) : (x ^ 2) ^ (-(1 / 2 : ℝ)) = x⁻¹ := by
    rw [← Real.rpow_natCast_mul hx.le]
    norm_num [Real.rpow_neg_one]
  dsimp only
  rw [Real.mul_rpow (sq_nonneg _) (sq_nonneg _), he (lt_trans hδ hz.1.1), he (lt_trans hδ hz.2.1)]

/-- Exact squared-logarithmic divergence of the critical-power integral with a square cutoff. -/
theorem normalCrossingCutoff_eq (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    normalCrossingCutoff δ = (Real.log δ) ^ 2 := by
  have hp {x : ℝ} (hx : 0 < x) : (x ^ 2) ^ (-(1 / 2 : ℝ)) = x⁻¹ := by
    rw [← Real.rpow_natCast_mul hx.le]
    norm_num [Real.rpow_neg_one]
  have hi : (∫ x : ℝ in Ioo δ 1, x⁻¹) = -Real.log δ := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hδ1,
      integral_inv_of_pos hδ zero_lt_one]
    simp
  unfold normalCrossingCutoff
  calc
    _ = ∫ z : ℝ × ℝ in (Ioo δ 1) ×ˢ (Ioo δ 1), z.1⁻¹ * z.2⁻¹ := by
      apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
      intro z hz
      dsimp only
      rw [Real.mul_rpow (sq_nonneg _) (sq_nonneg _), hp (lt_trans hδ hz.1.1), hp (lt_trans hδ hz.2.1)]
    _ = (Real.log δ) ^ 2 := by
      rw [Measure.volume_eq_prod, setIntegral_prod_mul, hi]
      ring

/-- A right-hand logarithmic asymptotic, using the exact cutoff formula.
It makes no assertion about zeta continuation or the multiplicity of a network. -/
theorem normalCrossingCutoff_log_equivalent :
    normalCrossingCutoff ~[𝓝[>] (0 : ℝ)] (fun δ => (Real.log δ) ^ 2) := by
  apply IsEquivalent.refl.congr_left
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with δ hδ hδ1
  exact (normalCrossingCutoff_eq δ hδ hδ1.le).symm
end ResidualSLT
