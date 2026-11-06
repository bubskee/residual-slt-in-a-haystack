module
public import ResidualSLT.PowerLaplaceOrder
public import Mathlib.MeasureTheory.Integral.Gamma

/-! Off-critical two-variable Laplace estimates with arbitrary positive radial density. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Filter

@[expose] def coneLaplaceExponent (a r q : ℕ) : ℝ :=
  min ((a:ℝ)/(2*r)) (((a:ℝ)+q)/(2*((r:ℝ)+q)))

@[expose] def powerWeightedKernel (a r q : ℕ) (N : ℝ) (z : ℝ × ℝ) : ℝ :=
  z.1^(a-1)*Real.exp (-N*(z.1^(2*r)*(z.2^2+z.1^(2*q))))

@[expose] def powerWeightedBox (a r q : ℕ) (ε δ N : ℝ) : ℝ :=
  ∫ z in Ioo 0 ε ×ˢ Ioo 0 δ, powerWeightedKernel a r q N z

@[expose] def radialGammaConstant (a r : ℕ) : ℝ :=
  (1/(2*(r:ℝ)))*Real.Gamma ((a:ℝ)/(2*r))

theorem radialGammaConstant_pos (a r : ℕ) (ha : 0 < a) (hr : 0 < r) :
    0 < radialGammaConstant a r := by unfold radialGammaConstant; positivity

theorem radialGamma_integrable (a r : ℕ) (_ha : 0 < a) (hr : 0 < r) (b : ℝ) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x^(a-1)*Real.exp (-b*x^(2*r))) (Ioi 0) volume := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := ((a-1:ℕ):ℝ))
    (p := ((2*r:ℕ):ℝ)) (by have hh : (0:ℝ) ≤ (a-1:ℕ) := Nat.cast_nonneg _; linarith) (by positivity) hb
  simpa only [Real.rpow_natCast] using h

theorem radialGamma_integral (a r : ℕ) (ha : 0 < a) (hr : 0 < r) (b : ℝ) (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0, x^(a-1)*Real.exp (-b*x^(2*r))) =
      b^(-((a:ℝ)/(2*r)))*radialGammaConstant a r := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (q := ((a-1:ℕ):ℝ))
    (p := ((2*r:ℕ):ℝ)) (by positivity) (by have hh : (0:ℝ) ≤ (a-1:ℕ) := Nat.cast_nonneg _; linarith) hb
  simp only [Real.rpow_natCast] at h
  simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub (show 1 ≤ a by omega),
    Nat.cast_one,sub_add_cancel,neg_div,radialGammaConstant,mul_assoc] using h

theorem powerWeighted_integrable (a r q : ℕ) (N ε b c : ℝ) :
    IntegrableOn (powerWeightedKernel a r q N) (Ioo 0 ε ×ˢ Ioo b c) volume :=
  ((by unfold powerWeightedKernel; fun_prop : Continuous (powerWeightedKernel a r q N)).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)

/-- Every finite radial Gaussian interval is bounded by its exact Gamma integral. -/
theorem radialGamma_interval_le (a r : ℕ) (ha : 0 < a) (hr : 0 < r) (b ε : ℝ) (hb : 0 < b) :
    (∫ x : ℝ in Ioo 0 ε, x^(a-1)*Real.exp (-b*x^(2*r))) ≤
      b^(-((a:ℝ)/(2*r)))*radialGammaConstant a r := by
  rw [← radialGamma_integral a r ha hr b hb]
  exact setIntegral_mono_set (radialGamma_integrable a r ha hr b hb)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact mul_nonneg (pow_nonneg hx.le _) (Real.exp_pos _).le)
    (Filter.Eventually.of_forall Ioo_subset_Ioi_self)

/-- Gaussian sections on any finite transverse interval. -/
theorem gaussian_interval_le (b δ : ℝ) (hb : 0 < b) :
    (∫ t : ℝ in Ioo 0 δ, Real.exp (-b*t^2)) ≤ Real.sqrt Real.pi*b^(-(1/2:ℝ)) := by
  calc
    _ ≤ ∫ t : ℝ, Real.exp (-b*t^2) := setIntegral_le_integral (integrable_exp_neg_mul_sq hb)
      (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))
    _ = _ := by
      rw [integral_gaussian,Real.sqrt_div Real.pi_pos.le,Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,
        Real.rpow_neg,div_eq_mul_inv]
      exact hb.le

/-- When the density degree is below the homogeneous degree, a radial Gamma
section leaves an integrable transverse power. -/
theorem powerWeightedBox_upper_lt (a r q : ℕ) (ha : 0 < a) (hr : 0 < r) (har : a < r)
    (ε δ : ℝ) (hδ : 0 < δ) :
    PowerLaplaceUpper ((a:ℝ)/(2*r)) (powerWeightedBox a r q ε δ) := by
  let v : ℝ := -((a:ℝ)/(r:ℝ))
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have har' : (a:ℝ) < r := by exact_mod_cast har
  have hv : -1 < v := by dsimp [v]; rw [neg_lt_neg_iff,div_lt_one hr']; exact har'
  have ht : IntegrableOn (fun t : ℝ => t^v) (Ioo 0 δ) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hδ).mpr hv
  let T := ∫ t : ℝ in Ioo 0 δ, t^v
  have hT : 0 ≤ T := integral_nonneg_of_ae (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le _)
  refine ⟨radialGammaConstant a r*(T+1), mul_pos (radialGammaConstant_pos a r ha hr) (by linarith), ?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with N hN
  have hi := powerWeighted_integrable a r q N ε 0 δ
  rw [Measure.volume_eq_prod] at hi
  have hs : IntegrableOn (fun z : ℝ × ℝ => powerWeightedKernel a r q N z.swap)
      (Ioo 0 δ ×ˢ Ioo 0 ε) (volume.prod volume) := hi.swap
  have hsections : IntegrableOn (fun t => ∫ u : ℝ in Ioo 0 ε, powerWeightedKernel a r q N (u,t)) (Ioo 0 δ) volume := by
    rw [IntegrableOn,← Measure.prod_restrict] at hs
    exact hs.integral_prod_left
  have hpoint (t : ℝ) (ht : t ∈ Ioo 0 δ) :
      (∫ u : ℝ in Ioo 0 ε, powerWeightedKernel a r q N (u,t)) ≤
        N^(-((a:ℝ)/(2*r)))*radialGammaConstant a r*t^v := by
    have ht0 : 0 < t := ht.1
    have hdrop : (∫ u : ℝ in Ioo 0 ε, powerWeightedKernel a r q N (u,t)) ≤
        ∫ u : ℝ in Ioo 0 ε, u^(a-1)*Real.exp (-(N*t^2)*u^(2*r)) := by
      apply setIntegral_mono_on
        (((by unfold powerWeightedKernel; fun_prop : Continuous (fun u => powerWeightedKernel a r q N (u,t))).continuousOn.integrableOn_compact
          isCompact_Icc).mono_set Ioo_subset_Icc_self)
        ((radialGamma_integrable a r ha hr (N*t^2) (by positivity)).mono_set Ioo_subset_Ioi_self) measurableSet_Ioo
      intro u hu
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu.1.le _)
      apply Real.exp_le_exp.mpr
      have hp : 0 ≤ N*u^(2*r)*u^(2*q) := mul_nonneg (mul_nonneg hN.le (pow_nonneg hu.1.le _)) (pow_nonneg hu.1.le _)
      nlinarith
    have hb := radialGamma_interval_le a r ha hr (N*t^2) ε (by positivity)
    have he : (N*t^2)^(-((a:ℝ)/(2*r)))*radialGammaConstant a r =
        N^(-((a:ℝ)/(2*r)))*radialGammaConstant a r*t^v := by
      rw [Real.mul_rpow hN.le (sq_nonneg t), ← Real.rpow_natCast t 2, ← Real.rpow_mul ht.1.le]
      have hv' : (2:ℝ)*(-((a:ℝ)/(2*r))) = v := by dsimp [v]; field_simp
      norm_num only [Nat.cast_ofNat]
      rw [hv']; ring
    exact hdrop.trans (he ▸ hb)
  have hm := setIntegral_mono_on hsections (ht.const_mul (N^(-((a:ℝ)/(2*r)))*radialGammaConstant a r))
    measurableSet_Ioo hpoint
  rw [integral_const_mul] at hm
  unfold powerWeightedBox
  rw [Measure.volume_eq_prod,← setIntegral_prod_swap (Ioo (0:ℝ) ε) (Ioo (0:ℝ) δ),setIntegral_prod _ hs]
  have hpow : 0 < N^(-((a:ℝ)/(2*r))) := Real.rpow_pos_of_pos hN _
  have hG := radialGammaConstant_pos a r ha hr
  dsimp only [Prod.swap_prod_mk]
  change _ ≤ radialGammaConstant a r*(T+1)*N^(-((a:ℝ)/(2*r)))
  change _ ≤ N^(-((a:ℝ)/(2*r)))*radialGammaConstant a r*T at hm
  nlinarith [mul_pos hpow hG]

/-- Above the homogeneous degree, transverse Gaussian integration leaves a
positive radial Gamma exponent, with the correction degree controlling scaling. -/
theorem powerWeightedBox_upper_gt (a r q : ℕ) (hr : 0 < r) (hqa : 0 < q) (hra : r < a)
    (ε δ : ℝ) :
    PowerLaplaceUpper (((a:ℝ)+q)/(2*((r:ℝ)+q))) (powerWeightedBox a r q ε δ) := by
  have har : 0 < a-r := by omega
  have hk : 0 < r+q := by omega
  have hC := radialGammaConstant_pos (a-r) (r+q) har hk
  refine ⟨Real.sqrt Real.pi*radialGammaConstant (a-r) (r+q), mul_pos (Real.sqrt_pos.mpr Real.pi_pos) hC, ?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with N hN
  have hi := powerWeighted_integrable a r q N ε 0 δ
  rw [Measure.volume_eq_prod] at hi
  have hsections : IntegrableOn (fun u => ∫ t : ℝ in Ioo 0 δ, powerWeightedKernel a r q N (u,t)) (Ioo 0 ε) volume := by
    rw [IntegrableOn,← Measure.prod_restrict] at hi
    exact hi.integral_prod_left
  have hpoint (u : ℝ) (hu : u ∈ Ioo 0 ε) :
      (∫ t : ℝ in Ioo 0 δ, powerWeightedKernel a r q N (u,t)) ≤
      (Real.sqrt Real.pi*N^(-(1/2:ℝ))) * (u^(a-r-1)*Real.exp (-N*u^(2*(r+q)))) := by
    have hu0 : 0 < u := hu.1
    have he (t : ℝ) : powerWeightedKernel a r q N (u,t) =
        (u^(a-1)*Real.exp (-N*u^(2*(r+q)))) * Real.exp (-(N*u^(2*r))*t^2) := by
      unfold powerWeightedKernel
      dsimp only
      rw [mul_assoc,← Real.exp_add]
      congr 2
      have hp : u^(2*(r+q)) = u^(2*r)*u^(2*q) := by rw [← pow_add]; congr 1; ring
      rw [hp]; ring
    rw [setIntegral_congr_fun measurableSet_Ioo (fun t _ => he t), integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left (gaussian_interval_le (N*u^(2*r)) δ (by positivity))
      (mul_nonneg (pow_nonneg hu0.le (a-1)) (Real.exp_pos (-N*u^(2*(r+q)))).le)
    have hp : u^(a-1)*(N*u^(2*r))^(-(1/2:ℝ)) = N^(-(1/2:ℝ))*u^(a-r-1) := by
      rw [Real.mul_rpow hN.le (pow_nonneg hu0.le _),← Real.rpow_natCast u (2*r),← Real.rpow_mul hu0.le]
      have he' : ((2*r:ℕ):ℝ)*(-(1/2:ℝ)) = -(r:ℝ) := by push_cast; ring
      rw [he',Real.rpow_neg hu0.le (r:ℝ),Real.rpow_natCast]
      have ha' : a-1 = r+(a-r-1) := by omega
      rw [ha',pow_add]
      field_simp
    calc
      _ ≤ _ := hh
      _ = _ := by
        calc
          _ = Real.sqrt Real.pi*(u^(a-1)*(N*u^(2*r))^(-(1/2:ℝ)))*Real.exp (-N*u^(2*(r+q))) := by ring
          _ = _ := by rw [hp]; ring
  have hg := (radialGamma_integrable (a-r) (r+q) har hk N hN).mono_set (s := Ioo 0 ε) Ioo_subset_Ioi_self
  have hm := setIntegral_mono_on hsections (hg.const_mul (Real.sqrt Real.pi*N^(-(1/2:ℝ)))) measurableSet_Ioo hpoint
  rw [integral_const_mul] at hm
  have hGamma := mul_le_mul_of_nonneg_left (radialGamma_interval_le (a-r) (r+q) har hk N ε hN)
    (mul_nonneg (Real.sqrt_nonneg Real.pi) (Real.rpow_nonneg hN.le (-(1/2:ℝ))))
  have he : Real.sqrt Real.pi*N^(-(1/2:ℝ)) *
      (N^(-((a-r:ℕ):ℝ)/(2*(r+q:ℕ)))*radialGammaConstant (a-r) (r+q)) =
      (Real.sqrt Real.pi*radialGammaConstant (a-r) (r+q))*N^(-(((a:ℝ)+q)/(2*((r:ℝ)+q)))) := by
    calc
      _ = (Real.sqrt Real.pi*radialGammaConstant (a-r) (r+q)) *
          (N^(-(1/2:ℝ))*N^(-((a-r:ℕ):ℝ)/(2*(r+q:ℕ)))) := by ring
      _ = _ := by
        rw [← Real.rpow_add hN]
        congr 2
        rw [Nat.cast_sub hra.le,Nat.cast_add]
        field_simp
        ring
  unfold powerWeightedBox
  rw [Measure.volume_eq_prod,setIntegral_prod _ hi]
  exact (hm.trans hGamma).trans_eq (by simpa only [neg_div] using he)

/-- Elementary weighted volume of a positive radial interval. -/
theorem integral_radial_nat_power (a : ℕ) (ha : 0 < a) (s : ℝ) (hs : 0 < s) :
    (∫ u : ℝ in Ioo 0 s, u^(a-1)) = s^a/(a:ℝ) := by
  have h := integral_radial_power_substitution a ha s hs (fun _ => (1:ℝ)) continuous_const
  simpa [Real.volume_Ioo,(pow_pos hs a).le,div_eq_mul_inv,mul_comm] using h

/-- A single family of genuine inner boxes gives both off-critical lower powers.
The transverse exponent b can be any integer between 0 and q. -/
theorem powerWeightedBox_inner_lower (a r q b : ℕ) (ha : 0 < a) (hbq : b ≤ q)
    (ε δ N s : ℝ) (hδ : 0 < δ) (hs : 0 < s) (hs1 : s ≤ 1) (hsε : s ≤ ε)
    (hN : 0 < N) (hscale : N*s^(2*(r+b)) = 1) :
    (Real.exp (-(δ^2+1))*δ/(a:ℝ))*s^(a+b) ≤ powerWeightedBox a r q ε δ N := by
  have hsb : 0 < δ*s^b := by positivity
  have hsub : Ioo (0:ℝ) s ×ˢ Ioo 0 (δ*s^b) ⊆ Ioo 0 ε ×ˢ Ioo 0 δ :=
    prod_mono (Ioo_subset_Ioo le_rfl hsε) (Ioo_subset_Ioo le_rfl
      (by simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hs.le hs1 (n := b)) hδ.le))
  have hpoint (z : ℝ × ℝ) (hz : z ∈ Ioo 0 s ×ˢ Ioo 0 (δ*s^b)) :
      z.1^(a-1)*Real.exp (-(δ^2+1)) ≤ powerWeightedKernel a r q N z := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hz.1.1.le _)
    apply Real.exp_le_exp.mpr
    have hrp := pow_le_pow_left₀ hz.1.1.le hz.1.2.le (2*r)
    have hqp := pow_le_pow_left₀ hz.1.1.le hz.1.2.le (2*q)
    have hqb := pow_le_pow_of_le_one hs.le hs1 (show 2*b ≤ 2*q by omega)
    have ht := pow_le_pow_left₀ hz.2.1.le hz.2.2.le 2
    have hbase : z.2^2+z.1^(2*q) ≤ (δ^2+1)*s^(2*b) := by
      rw [mul_pow,← pow_mul,show b*2 = 2*b by omega] at ht
      nlinarith
    have hprod := mul_le_mul hrp hbase (add_nonneg (sq_nonneg z.2) (pow_nonneg hz.1.1.le (2*q))) (pow_nonneg hs.le _)
    have hpow : s^(2*r)*((δ^2+1)*s^(2*b)) = (δ^2+1)*s^(2*(r+b)) := by
      rw [mul_left_comm,← pow_add]; congr 2; ring
    rw [hpow] at hprod
    nlinarith [mul_le_mul_of_nonneg_left hprod hN.le]
  have hconst : IntegrableOn (fun z : ℝ × ℝ => z.1^(a-1)*Real.exp (-(δ^2+1)))
      (Ioo 0 s ×ˢ Ioo 0 (δ*s^b)) volume :=
    ((by fun_prop : Continuous (fun z : ℝ × ℝ => z.1^(a-1)*Real.exp (-(δ^2+1)))).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hlo := setIntegral_mono_on hconst (powerWeighted_integrable a r q N s 0 (δ*s^b))
    (measurableSet_Ioo.prod measurableSet_Ioo) hpoint
  have he : (∫ z : ℝ × ℝ in Ioo 0 s ×ˢ Ioo 0 (δ*s^b), z.1^(a-1)*Real.exp (-(δ^2+1))) =
      (Real.exp (-(δ^2+1))*δ/(a:ℝ))*s^(a+b) := by
    rw [Measure.volume_eq_prod,setIntegral_prod_mul (μ := volume) (ν := volume)
      (fun u : ℝ => u^(a-1)) (fun _ : ℝ => Real.exp (-(δ^2+1))) (Ioo 0 s) (Ioo 0 (δ*s^b)),
      integral_radial_nat_power a ha s hs,setIntegral_const,Measure.real,Real.volume_Ioo,sub_zero,
      ENNReal.toReal_ofReal hsb.le,smul_eq_mul,pow_add]
    ring
  rw [he] at hlo
  exact hlo.trans (setIntegral_mono_set (powerWeighted_integrable a r q N ε 0 δ)
    (by filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
        exact mul_nonneg (pow_nonneg hz.1.1.le _) (Real.exp_pos _).le)
    (Filter.Eventually.of_forall hsub))

/-- Eventual lower power from the inner-box scaling parameter. -/
theorem powerWeightedBox_lower (a r q b : ℕ) (ha : 0 < a) (hr : 0 < r) (hbq : b ≤ q)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    PowerLaplaceLower (((a:ℝ)+b)/(2*((r:ℝ)+b))) (powerWeightedBox a r q ε δ) := by
  let D : ℝ := 2*((r:ℝ)+b)
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨Real.exp (-(δ^2+1))*δ/(a:ℝ), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp (D*(|Real.log ε|+1)))] with N hN
  have hN0 : 0 < N := (Real.exp_pos _).trans_le hN
  have hlog : D*(|Real.log ε|+1) ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos _) hN
  let s := Real.exp (-Real.log N/D)
  have hs : 0 < s := Real.exp_pos _
  have harg : -Real.log N/D ≤ -(|Real.log ε|+1) := (div_le_iff₀ hD).mpr (by nlinarith)
  have hs1 : s < 1 := Real.exp_lt_one_iff.mpr (by linarith [abs_nonneg (Real.log ε)])
  have hsε : s ≤ ε := by
    rw [← Real.exp_log hε]
    exact Real.exp_le_exp.mpr (by linarith [neg_abs_le (Real.log ε)])
  have hcast : ((2*(r+b):ℕ):ℝ) = D := by dsimp [D]; push_cast; ring
  have hscale : N*s^(2*(r+b)) = 1 := by
    rw [← Real.exp_nat_mul,hcast]
    have he : D*(-Real.log N/D) = -Real.log N := by field_simp
    rw [he,Real.exp_neg,Real.exp_log hN0]
    exact mul_inv_cancel₀ hN0.ne'
  have hp : s^(a+b) = N^(-(((a:ℝ)+b)/(2*((r:ℝ)+b)))) := by
    rw [Real.rpow_def_of_pos hN0,← Real.exp_nat_mul]
    congr 1
    dsimp [D]
    push_cast
    ring
  have h := powerWeightedBox_inner_lower a r q b ha hbq ε δ N s hδ hs hs1.le hsε hN0 hscale
  rwa [hp] at h

theorem coneLaplaceExponent_of_le (a r q : ℕ) (hr : 0 < r) (har : a ≤ r) :
    coneLaplaceExponent a r q = (a:ℝ)/(2*r) := by
  unfold coneLaplaceExponent
  apply min_eq_left
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have har' : (a:ℝ) ≤ r := by exact_mod_cast har
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr har') (Nat.cast_nonneg q : (0:ℝ) ≤ q)]

theorem coneLaplaceExponent_of_ge (a r q : ℕ) (hr : 0 < r) (hra : r ≤ a) :
    coneLaplaceExponent a r q = ((a:ℝ)+q)/(2*((r:ℝ)+q)) := by
  unfold coneLaplaceExponent
  apply min_eq_right
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have hra' : (r:ℝ) ≤ a := by exact_mod_cast hra
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hra') (Nat.cast_nonneg q : (0:ℝ) ≤ q)]

/-- Both off-critical regimes, with their exact expected power and no logarithm. -/
theorem powerWeightedBox_has_order (a r q : ℕ) (ha : 0 < a) (hr : 0 < r) (hq : 0 < q)
    (hne : a ≠ r) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    HasPowerLaplaceOrder (coneLaplaceExponent a r q) (powerWeightedBox a r q ε δ) := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [coneLaplaceExponent_of_le a r q hr h.le]
    exact ⟨by simpa using powerWeightedBox_lower a r q 0 ha hr (Nat.zero_le _) ε δ hε hδ,
      powerWeightedBox_upper_lt a r q ha hr h ε δ hδ⟩
  · rw [coneLaplaceExponent_of_ge a r q hr h.le]
    exact ⟨powerWeightedBox_lower a r q q ha hr le_rfl ε δ hε hδ,
      powerWeightedBox_upper_gt a r q hr hq h ε δ⟩

@[expose] def powerWeightedSymmetric (a r q : ℕ) (ε δ N : ℝ) : ℝ :=
  ∫ z in Ioo 0 ε ×ˢ Ioo (-δ) δ, powerWeightedKernel a r q N z

theorem powerWeightedSymmetric_eq (a r q : ℕ) (ε δ N : ℝ) (hδ : 0 < δ) :
    powerWeightedSymmetric a r q ε δ N = 2*powerWeightedBox a r q ε δ N := by
  have hi (b c : ℝ) : IntegrableOn (powerWeightedKernel a r q N)
      (Ioo 0 ε ×ˢ Ioo b c) (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using powerWeighted_integrable a r q N ε b c
  unfold powerWeightedSymmetric powerWeightedBox
  rw [Measure.volume_eq_prod,setIntegral_prod _ (hi (-δ) δ),setIntegral_prod _ (hi 0 δ),← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u _
  exact integral_even_Ioo (fun t => powerWeightedKernel a r q N (u,t))
    (by unfold powerWeightedKernel; fun_prop) (fun t => by simp [powerWeightedKernel]) δ hδ

theorem powerWeightedSymmetric_has_order (a r q : ℕ) (ha : 0 < a) (hr : 0 < r) (hq : 0 < q)
    (hne : a ≠ r) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    HasPowerLaplaceOrder (coneLaplaceExponent a r q) (powerWeightedSymmetric a r q ε δ) := by
  have h := powerWeightedBox_has_order a r q ha hr hq hne ε δ hε hδ
  constructor
  · exact (h.1.const_mul 2 (by norm_num)).mono (Filter.Eventually.of_forall (fun N =>
      (powerWeightedSymmetric_eq a r q ε δ N hδ).ge))
  · exact (h.2.const_mul 2 (by norm_num)).mono (Filter.Eventually.of_forall (fun N =>
      (powerWeightedSymmetric_eq a r q ε δ N hδ).le))

/-- Off-zero angular regions admit the faster ordinary radial power bound. -/
theorem radialGamma_laplace_upper (a r : ℕ) (ha : 0 < a) (hr : 0 < r) (ε : ℝ) :
    PowerLaplaceUpper ((a:ℝ)/(2*r)) (fun N => ∫ u : ℝ in Ioo 0 ε, u^(a-1)*Real.exp (-N*u^(2*r))) := by
  refine ⟨radialGammaConstant a r,radialGammaConstant_pos a r ha hr,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with N hN
  simpa only [mul_comm] using radialGamma_interval_le a r ha hr N ε hN

end ResidualSLT
