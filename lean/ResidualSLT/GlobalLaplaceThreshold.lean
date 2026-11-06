module
public import ResidualSLT.LocalPositivePrior
public import ResidualSLT.LaplaceThreshold
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Positive-time Mellin transfer for proper priors on an unbounded parameter space.
The original stronger local lemmas are preserved; no negative-time exponential moment is assumed. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Set Filter

/-- Tonelli/Fubini and the positive Gamma integral, with no assumption that either side is finite. -/
theorem inversePower_integrable_iff_mellin_pos {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] (K : α → ℝ) (hK : Measurable K)
    (hpos : ∀ᵐ x ∂μ, 0 < K x)
    (hi : ∀ t : ℝ, 0<t → Integrable (fun x => Real.exp (-t*K x)) μ)
    (s : ℝ) (hs : 0 < s) :
    Integrable (fun x => (K x)^(-s)) μ ↔
      IntegrableOn (fun t : ℝ => t^(s-1)*(∫ x, Real.exp (-t*K x) ∂μ)) (Ioi 0) := by
  let ν : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ × α → ℝ := fun v => v.1^(s-1)*Real.exp (-v.1*K v.2)
  have hf : AEStronglyMeasurable f (ν.prod μ) := by
    apply Measurable.aestronglyMeasurable
    dsimp [f]
    exact (measurable_fst.pow_const _).mul ((measurable_fst.neg.mul (hK.comp measurable_snd)).exp)
  have hleft : ∀ᵐ t ∂ν, Integrable (fun x => f (t,x)) μ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hi t ht).const_mul (t^(s-1))
  have hright : ∀ᵐ x ∂μ, Integrable (fun t => f (t,x)) ν := by
    filter_upwards [hpos] with x hx
    have hh := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s-1) (b := K x)
      (by linarith) zero_lt_one hx
    simpa [f,ν,IntegrableOn,Real.rpow_one,neg_mul,mul_comm] using hh
  have hinner : (fun x => ∫ t, ‖f (t,x)‖ ∂ν) =ᵐ[μ] (fun x => Real.Gamma s*(K x)^(-s)) := by
    filter_upwards [hpos] with x hx
    have he : (∫ t, ‖f (t,x)‖ ∂ν) = ∫ t in Ioi (0:ℝ), t^(s-1)*Real.exp (-(K x*t)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [f,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)]
      congr 2
      ring
    rw [he,Real.integral_rpow_mul_exp_neg_mul_Ioi hs hx]
    rw [one_div,Real.inv_rpow hx.le,← Real.rpow_neg hx.le,mul_comm]
  have houter : (fun t => ∫ x, ‖f (t,x)‖ ∂μ) =ᵐ[ν]
      (fun t => t^(s-1)*(∫ x, Real.exp (-t*K x) ∂μ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      simp only [f,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)])
  have he := (integrable_prod_iff hf).symm.trans (integrable_prod_iff' hf)
  simp only [hleft,hright,true_and] at he
  calc
    Integrable (fun x => (K x)^(-s)) μ ↔ Integrable (fun x => Real.Gamma s*(K x)^(-s)) μ :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (Real.Gamma_pos_of_pos hs).ne') _).symm
    _ ↔ Integrable (fun x => ∫ t, ‖f (t,x)‖ ∂ν) μ := (integrable_congr hinner).symm
    _ ↔ Integrable (fun t => ∫ x, ‖f (t,x)‖ ∂μ) ν := he.symm
    _ ↔ _ := integrable_congr houter

/-- A finite parameter measure and an a.e. positive loss: positive inverse powers
are integrable exactly below the certified Laplace exponent, including endpoint failure. -/
theorem inversePower_integrable_iff_of_laplace_order_pos {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (K : α → ℝ) (hK : Measurable K)
    (hpos : ∀ᵐ x ∂μ, 0 < K x)
    (hi : ∀ t : ℝ, 0<t → Integrable (fun x => Real.exp (-t*K x)) μ)
    (a : ℝ) (m : ℕ)
    (horder : HasLaplaceOrder a m (fun t => ∫ x, Real.exp (-t*K x) ∂μ))
    (s : ℝ) (hs : 0 < s) :
    Integrable (fun x => (K x)^(-s)) μ ↔ s < a := by
  rw [inversePower_integrable_iff_mellin_pos μ K hK hpos hi s hs]
  apply mellin_integrable_iff_of_laplace_order _ _ (μ.real univ) _ a m horder s hs
  · have hm : StronglyMeasurable (fun v : ℝ × α => Real.exp (-v.1*K v.2)) :=
      ((measurable_fst.neg.mul (hK.comp measurable_snd)).exp).stronglyMeasurable
    exact hm.integral_prod_right'.measurable
  · intro t ht
    refine ⟨integral_nonneg (fun _ => (Real.exp_pos _).le),?_⟩
    calc
      _ ≤ ∫ _x, (1:ℝ) ∂μ := by
        apply integral_mono_ae (hi t ht) (integrable_const 1)
        filter_upwards [hpos] with x hx
        exact Real.exp_le_one_iff.mpr (by nlinarith [mul_pos ht hx])
      _ = μ.real univ := by simp


end ResidualSLT
