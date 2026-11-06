module
public import ResidualSLT.OneDimensionalLaplace
public import ResidualSLT.RadialThreshold

/-! Pure-power Laplace order for continuous positive homogeneous losses.
The radial measure identity holds for any finite-dimensional norm and additive Haar measure. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Metric Filter

/-- A positive radial density gives the dimension/degree Laplace power. -/
theorem weighted_radial_interval_laplace_order (a r : ℕ) (ha : 0 < a) (hr : 0 < r)
    (ε : ℝ) (hε : 0 < ε) :
    HasPowerLaplaceOrder ((a:ℝ)/(2*r)) (fun N => ∫ x : ℝ in Ioo 0 ε,
      x^(a-1)*Real.exp (-N*x^(2*r))) := by
  constructor
  · have hl := powerWeightedBox_lower a r 0 0 ha hr le_rfl ε 1 hε zero_lt_one
    norm_num only [Nat.cast_zero,add_zero] at hl
    apply hl.mono
    filter_upwards [eventually_ge_atTop (0:ℝ)] with N hN
    have hi := powerWeighted_integrable a r 0 N ε 0 1
    rw [Measure.volume_eq_prod] at hi
    unfold powerWeightedBox
    rw [Measure.volume_eq_prod,setIntegral_prod _ hi]
    have hrad : IntegrableOn (fun x : ℝ => x^(a-1)*Real.exp (-N*x^(2*r))) (Ioo 0 ε) volume :=
      ((by fun_prop : Continuous (fun x : ℝ => x^(a-1)*Real.exp (-N*x^(2*r)))).continuousOn.integrableOn_compact
        isCompact_Icc).mono_set Ioo_subset_Icc_self
    apply setIntegral_mono_on (by rw [IntegrableOn,← Measure.prod_restrict] at hi; exact hi.integral_prod_left)
      hrad measurableSet_Ioo
    intro x hx
    calc
      _ ≤ ∫ t : ℝ in Ioo 0 1, x^(a-1)*Real.exp (-N*x^(2*r)) := by
        apply setIntegral_mono_on
          (((by unfold powerWeightedKernel; fun_prop : Continuous (fun t : ℝ => powerWeightedKernel a r 0 N (x,t))).continuousOn.integrableOn_compact
            isCompact_Icc).mono_set Ioo_subset_Icc_self)
          (((continuous_const : Continuous (fun _ : ℝ => x^(a-1)*Real.exp (-N*x^(2*r)))).continuousOn.integrableOn_compact
            isCompact_Icc).mono_set Ioo_subset_Icc_self) measurableSet_Ioo
        intro t _
        simp only [powerWeightedKernel,mul_zero,pow_zero]
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hx.1.le _)
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (mul_nonneg hN (pow_nonneg hx.1.le (2*r))) (sq_nonneg t)]
      _ = _ := by simp
  · exact radialGamma_laplace_upper a r ha hr ε

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Exact radial integration on a norm ball, obtained from Haar-to-sphere integration
by restricting the radial variable. No smoothness of the norm sphere is required. -/
theorem integral_norm_on_ball (f : ℝ → ℝ) (ε : ℝ) :
    (∫ w in ball (0:E) ε, f ‖w‖ ∂μ) =
      ((Module.finrank ℝ E:ℝ)*μ.real (ball 0 1)) *
        ∫ x : ℝ in Ioo 0 ε, x^(Module.finrank ℝ E-1)*f x := by
  have he : (ball (0:E) ε).indicator (fun w => f ‖w‖) = fun w => (Iio ε).indicator f ‖w‖ := by
    funext w
    simp [indicator]
  rw [← integral_indicator measurableSet_ball,he,integral_fun_norm_addHaar μ]
  simp only [nsmul_eq_mul,smul_eq_mul,mul_assoc]
  congr 1
  have hi : (fun x : ℝ => x^(Module.finrank ℝ E-1)*(Iio ε).indicator f x) =
      (Iio ε).indicator (fun x : ℝ => x^(Module.finrank ℝ E-1)*f x) := by
    funext x
    by_cases hx : x < ε <;> simp [indicator,hx]
  rw [hi,setIntegral_indicator measurableSet_Iio]
  congr 1

/-- Every even norm power has pure-power local Laplace order on a positive ball. -/
theorem normPower_laplace_order (r : ℕ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    HasPowerLaplaceOrder ((Module.finrank ℝ E:ℝ)/(2*r))
      (fun N => ∫ w in ball (0:E) ε, Real.exp (-N*‖w‖^(2*r)) ∂μ) := by
  have hd : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hc : 0 < (Module.finrank ℝ E:ℝ)*μ.real (ball (0:E) 1) := by
    apply mul_pos (by exact_mod_cast hd)
    exact ENNReal.toReal_pos (ne_of_gt (measure_ball_pos μ 0 zero_lt_one))
      measure_ball_lt_top.ne
  have h := weighted_radial_interval_laplace_order (Module.finrank ℝ E) r hd hr ε hε
  have he (N : ℝ) : (∫ w in ball (0:E) ε, Real.exp (-N*‖w‖^(2*r)) ∂μ) =
      ((Module.finrank ℝ E:ℝ)*μ.real (ball 0 1)) *
        ∫ x : ℝ in Ioo 0 ε, x^(Module.finrank ℝ E-1)*Real.exp (-N*x^(2*r)) :=
    integral_norm_on_ball μ (fun x => Real.exp (-N*x^(2*r))) ε
  constructor
  · simpa only [he] using h.1.const_mul _ hc
  · simpa only [he] using h.2.const_mul _ hc

/-- Compactness derives the norm comparison for a continuous homogeneous loss
positive away from zero. The conclusion is a quantitative Laplace order. -/
theorem positive_homogeneous_laplace_order {Q : E → ℝ} (r : ℕ) (hr : 0 < r)
    (hQ : Continuous Q) (hpos : ∀ w, w ≠ 0 → 0 < Q w)
    (hhom : ∀ (a : ℝ), 0 ≤ a → ∀ w, Q (a • w) = a^(2*r)*Q w)
    (ε : ℝ) (hε : 0 < ε) :
    HasPowerLaplaceOrder ((Module.finrank ℝ E:ℝ)/(2*r))
      (fun N => ∫ w in ball (0:E) ε, Real.exp (-N*Q w) ∂μ) := by
  obtain ⟨c,C,hc,hC,hb⟩ := positive_homogeneous_bounds (2*r) (by omega) hQ hpos hhom
  apply power_laplace_order_of_comparable μ (ball 0 ε) (fun w => ‖w‖^(2*r)) Q
    (fun N => ((by fun_prop : Continuous (fun w : E => Real.exp (-N*‖w‖^(2*r)))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall)
    (fun N => ((by fun_prop : Continuous (fun w => Real.exp (-N*Q w))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall)
    c C hc hC (Eventually.of_forall hb) (normPower_laplace_order μ r hr ε hε)

end ResidualSLT
