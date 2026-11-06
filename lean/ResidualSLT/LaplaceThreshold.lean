module
public import ResidualSLT.LaplaceMellin
public import Mathlib.MeasureTheory.Integral.Asymptotics

/-! Exact real inverse-power thresholds, including the boundary, from quantitative Laplace order. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Set Filter Asymptotics

/-- The Mellin integral of a bounded positive Laplace profile has exactly the power threshold.
All logarithmic multiplicities m≥1 give divergence at the boundary. -/
theorem mellin_integrable_iff_of_laplace_order (Z : ℝ → ℝ) (hZ : Measurable Z)
    (B : ℝ) (hB : ∀ t : ℝ, 0 < t → 0 ≤ Z t ∧ Z t ≤ B)
    (a : ℝ) (m : ℕ) (horder : HasLaplaceOrder a m Z)
    (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => t^(s-1)*Z t) (Ioi 0) ↔ s < a := by
  obtain ⟨_,c,C,N₀,hc,hC,hN₀,hb⟩ := horder
  have hm : Measurable (fun t : ℝ => t^(s-1)*Z t) := (measurable_id.pow_const _).mul hZ
  constructor
  · intro hi
    let T := max N₀ (Real.exp 1)
    have hT : 0 < T := (zero_lt_one.trans hN₀).trans_le (le_max_left _ _)
    have hint : IntegrableOn (fun t : ℝ => c*t^(s-a-1)) (Ioi T) := by
      apply (hi.mono_set (Ioi_subset_Ioi hT.le)).mono' ((measurable_id.pow_const _).const_mul _).aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := hT.trans ht
      have htN : N₀ ≤ t := (le_max_left _ _).trans ht.le
      have hlog : 1 ≤ Real.log t := by
        have hh : Real.exp 1 ≤ t := (le_max_right _ _).trans ht.le
        simpa using Real.log_le_log (Real.exp_pos 1) hh
      have hp : 1 ≤ (Real.log t)^(m-1) := one_le_pow₀ hlog
      have hlo := mul_le_mul_of_nonneg_left (hb t htN).1 (Real.rpow_nonneg ht0.le (s-1))
      have hprod : t^(s-1)*laplaceRate a m t = t^(s-a-1)*(Real.log t)^(m-1) := by
        rw [laplaceRate,← mul_assoc,← Real.rpow_add ht0]
        congr 2
        ring
      rw [mul_left_comm,hprod] at hlo
      rw [Real.norm_eq_abs]
      change |c*t^(s-a-1)| ≤ _
      rw [abs_of_nonneg (mul_nonneg hc.le (Real.rpow_nonneg ht0.le _))]
      exact (by nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg hc.le (Real.rpow_nonneg ht0.le (s-a-1)))] :
        c*t^(s-a-1) ≤ t^(s-1)*Z t)
    have hh : IntegrableOn (fun t : ℝ => t^(s-a-1)) (Ioi T) :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc.ne') _).mp hint
    have hh' := (integrableOn_Ioi_rpow_iff hT).mp hh
    linarith
  · intro hsa
    let δ : ℝ := (a-s)/2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hlog := (isLittleO_log_rpow_rpow_atTop ((m-1:ℕ):ℝ) hδ).bound zero_lt_one
    obtain ⟨U,hU⟩ := eventually_atTop.mp hlog
    let T := max 1 (max N₀ U)
    have hT : 0 < T := zero_lt_one.trans_le (le_max_left _ _)
    have hsmall : IntegrableOn (fun t : ℝ => t^(s-1)*Z t) (Ioc 0 T) := by
      have hp : IntegrableOn (fun t : ℝ => t^(s-1)) (Ioc 0 T) := by
        rw [integrableOn_Ioc_iff_integrableOn_Ioo]
        exact (intervalIntegral.integrableOn_Ioo_rpow_iff hT).mpr (by linarith)
      apply (hp.mul_const B).mono' hm.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (hB t ht.1).1)]
      exact mul_le_mul_of_nonneg_left (hB t ht.1).2 (Real.rpow_nonneg ht.1.le _)
    have hlarge : IntegrableOn (fun t : ℝ => t^(s-1)*Z t) (Ioi T) := by
      have hexp : s-a-1+δ < -1 := by dsimp [δ]; linarith
      apply ((integrableOn_Ioi_rpow_of_lt hexp hT).const_mul C).mono' hm.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := hT.trans ht
      have ht1 : 1 ≤ t := (le_max_left _ _).trans ht.le
      have htN : N₀ ≤ t := ((le_max_left _ _).trans (le_max_right _ _)).trans ht.le
      have htU : U ≤ t := ((le_max_right _ _).trans (le_max_right _ _)).trans ht.le
      have hlogt : (Real.log t)^(m-1) ≤ t^δ := by
        simpa only [Real.rpow_natCast,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (Real.log_nonneg ht1) _),
          abs_of_nonneg (Real.rpow_nonneg ht0.le _),one_mul] using hU t htU
      have hu := mul_le_mul_of_nonneg_left (hb t htN).2 (Real.rpow_nonneg ht0.le (s-1))
      have he : t^(s-1)*(C*laplaceRate a m t) = C*t^(s-a-1)*(Real.log t)^(m-1) := by
        unfold laplaceRate
        calc
          _ = C*(t^(s-1)*t^(-a))*(Real.log t)^(m-1) := by ring
          _ = _ := by rw [← Real.rpow_add ht0,show s-1+-a=s-a-1 by ring]
      rw [he] at hu
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (hB t ht0).1)]
      apply hu.trans
      calc
        _ ≤ C*t^(s-a-1)*t^δ := mul_le_mul_of_nonneg_left hlogt (mul_nonneg hC.le (Real.rpow_nonneg ht0.le _))
        _ = C*t^(s-a-1+δ) := by rw [mul_assoc,← Real.rpow_add ht0]
    rw [← Ioc_union_Ioi_eq_Ioi hT.le]
    exact hsmall.union hlarge

/-- A finite parameter measure and an a.e. positive loss: positive inverse powers
are integrable exactly below the certified Laplace exponent, including endpoint failure. -/
theorem inversePower_integrable_iff_of_laplace_order {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (K : α → ℝ) (hK : Measurable K)
    (hpos : ∀ᵐ x ∂μ, 0 < K x)
    (hi : ∀ t : ℝ, Integrable (fun x => Real.exp (-t*K x)) μ)
    (a : ℝ) (m : ℕ)
    (horder : HasLaplaceOrder a m (fun t => ∫ x, Real.exp (-t*K x) ∂μ))
    (s : ℝ) (hs : 0 < s) :
    Integrable (fun x => (K x)^(-s)) μ ↔ s < a := by
  rw [inversePower_integrable_iff_mellin μ K hK hpos hi s hs]
  apply mellin_integrable_iff_of_laplace_order _ _ (μ.real univ) _ a m horder s hs
  · have hm : StronglyMeasurable (fun v : ℝ × α => Real.exp (-v.1*K v.2)) :=
      ((measurable_fst.neg.mul (hK.comp measurable_snd)).exp).stronglyMeasurable
    exact hm.integral_prod_right'.measurable
  · intro t ht
    refine ⟨integral_nonneg (fun _ => (Real.exp_pos _).le),?_⟩
    calc
      _ ≤ ∫ _x, (1:ℝ) ∂μ := by
        apply integral_mono_ae (hi t) (integrable_const 1)
        filter_upwards [hpos] with x hx
        exact Real.exp_le_one_iff.mpr (by nlinarith [mul_pos ht hx])
      _ = μ.real univ := by simp

end ResidualSLT
