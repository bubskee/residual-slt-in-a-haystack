module
public import ResidualSLT.WeightedLaplace

/-! Critical weighted Laplace bounds with independent positive radial degrees. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Filter

@[expose] def generalWeightedKernel (r q : ℕ) (N : ℝ) (z : ℝ × ℝ) : ℝ :=
  z.1^(r-1) * Real.exp (-N * (z.1^(2*r)*(z.2^2+z.1^(2*q))))

@[expose] def generalWeightedBox (r q : ℕ) (ε δ N : ℝ) : ℝ :=
  ∫ z in Ioo 0 ε ×ˢ Ioo 0 δ, generalWeightedKernel r q N z

theorem generalWeighted_integrable (r q : ℕ) (N ε a b : ℝ) :
    IntegrableOn (generalWeightedKernel r q N) (Ioo 0 ε ×ˢ Ioo a b) volume :=
  ((by unfold generalWeightedKernel; fun_prop : Continuous (generalWeightedKernel r q N)).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)

/-- The pure product Gaussian is controlled by two existing critical kernels,
one for each ordering of the coordinates. -/
theorem productGaussian_upper (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    CriticalLaplaceUpper (fun N => ∫ z : ℝ × ℝ in Ioo 0 a ×ˢ Ioo 0 b,
      Real.exp (-N*(z.1^2*z.2^2))) := by
  have h1 := (normalizedLaplaceBox_has_order a b ha hb).2.comp_mul (1/2) (by norm_num)
  have h2 := (normalizedLaplaceBox_has_order b a hb ha).2.comp_mul (1/2) (by norm_num)
  apply (h1.add h2).mono
  filter_upwards [eventually_ge_atTop (0:ℝ)] with N hN
  have hi (g : ℝ × ℝ → ℝ) (hg : Continuous g) : IntegrableOn g (Ioo 0 a ×ˢ Ioo 0 b) volume :=
    (hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  let g : ℝ × ℝ → ℝ := fun z => Real.exp (-(1/2*N)*(z.1^2*(z.2^2+z.1^2)))
  have hs : (∫ z in Ioo 0 a ×ˢ Ioo 0 b, g z.swap) = normalizedLaplaceBox b a (1/2*N) := by
    change _ = ∫ z in Ioo 0 b ×ˢ Ioo 0 a, g z
    rw [Measure.volume_eq_prod, ← setIntegral_prod_swap (Ioo (0:ℝ) b) (Ioo (0:ℝ) a)]
  change _ ≤ (∫ z in Ioo 0 a ×ˢ Ioo 0 b, g z) + _
  rw [← hs, ← integral_add (hi g (by fun_prop)) (hi (fun z => g z.swap) (by fun_prop))]
  apply setIntegral_mono_on (hi _ (by fun_prop)) ((hi _ (by fun_prop)).add (hi _ (by fun_prop)))
    (measurableSet_Ioo.prod measurableSet_Ioo)
  intro z _
  dsimp [g]
  rcases le_total (z.1^2) (z.2^2) with h | h
  · have he : Real.exp (-N*(z.1^2*z.2^2)) ≤ Real.exp (-(1/2*N)*(z.1^2*(z.2^2+z.1^2))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg hN (sq_nonneg z.1))]
    exact he.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have he : Real.exp (-N*(z.1^2*z.2^2)) ≤ Real.exp (-(1/2*N)*(z.2^2*(z.1^2+z.2^2))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg hN (sq_nonneg z.2))]
    exact he.trans (le_add_of_nonneg_left (Real.exp_pos _).le)

/-- Upper bound independent of the correction exponent: drop the nonnegative correction. -/
theorem generalWeightedBox_upper (r q : ℕ) (hr : 0 < r) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) : CriticalLaplaceUpper (generalWeightedBox r q ε δ) := by
  have hu := (productGaussian_upper (ε^r) δ (pow_pos hε r) hδ).const_mul (r:ℝ)⁻¹ (by positivity)
  apply hu.mono
  filter_upwards [eventually_ge_atTop (0:ℝ)] with N hN
  let g : ℝ × ℝ → ℝ := fun z => z.1^(r-1)*Real.exp (-N*(z.1^(2*r)*z.2^2))
  have hi (g : ℝ × ℝ → ℝ) (hg : Continuous g) (a b : ℝ) :
      IntegrableOn g (Ioo 0 a ×ˢ Ioo 0 b) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have he : (∫ z in Ioo 0 ε ×ˢ Ioo 0 δ, g z) = (r:ℝ)⁻¹ *
      ∫ z : ℝ × ℝ in Ioo 0 (ε^r) ×ˢ Ioo 0 δ, Real.exp (-N*(z.1^2*z.2^2)) := by
    rw [Measure.volume_eq_prod, ← setIntegral_prod_swap (Ioo (0:ℝ) ε) (Ioo (0:ℝ) δ),
      ← setIntegral_prod_swap (Ioo (0:ℝ) (ε^r)) (Ioo (0:ℝ) δ)]
    have hs : IntegrableOn (fun z : ℝ × ℝ => g z.swap) (Ioo 0 δ ×ˢ Ioo 0 ε) (volume.prod volume) := (hi g (by fun_prop) ε δ).swap
    have ht : IntegrableOn (fun z : ℝ × ℝ => Real.exp (-N*(z.swap.1^2*z.swap.2^2)))
        (Ioo 0 δ ×ˢ Ioo 0 (ε^r)) (volume.prod volume) := (hi (fun z : ℝ × ℝ => Real.exp (-N*(z.1^2*z.2^2))) (by fun_prop) (ε^r) δ).swap
    rw [setIntegral_prod _ hs, setIntegral_prod _ ht, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t _
    have hh := integral_radial_power_substitution r hr ε hε
      (fun u => Real.exp (-N*(u^2*t^2))) (by fun_prop)
    simpa only [g, Prod.swap_prod_mk, ← pow_mul, Nat.mul_comm r 2] using! hh
  rw [← he]
  apply setIntegral_mono_on (generalWeighted_integrable r q N ε 0 δ)
    (by simpa only [Measure.volume_eq_prod] using hi g (by fun_prop) ε δ)
    (measurableSet_Ioo.prod measurableSet_Ioo)
  intro z hz
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hz.1.1.le _)
  apply Real.exp_le_exp.mpr
  have hp : 0 ≤ N*z.1^(2*r)*z.1^(2*q) :=
    mul_nonneg (mul_nonneg hN (pow_nonneg hz.1.1.le _)) (pow_nonneg hz.1.1.le _)
  nlinarith

/-- Explicit positive strip lower bound. Both variable interval inclusions are proved. -/
theorem generalWeightedBox_strip_lower (r q : ℕ) (hr : 0 < r) (hq : 0 < q)
    (ε δ N a : ℝ) (hδ : 0 < δ) (ha : 0 < a) (ha1 : a < 1)
    (haε : a^r ≤ ε) (hN : 0 < N) (hscale : N*a^(2*r*(r+q)) = 1) :
    Real.exp (-(δ^2+1))*δ*a^(r*(r+q))*((q:ℝ)*(-Real.log a)) ≤ generalWeightedBox r q ε δ N := by
  let F := fun u : ℝ => ∫ t : ℝ in Ioo 0 δ, generalWeightedKernel r q N (u,t)
  have hi := generalWeighted_integrable r q N ε 0 δ
  have hF : IntegrableOn F (Ioo 0 ε) volume := by
    rw [IntegrableOn,Measure.volume_eq_prod,← Measure.prod_restrict] at hi
    exact hi.integral_prod_left
  have hab : a^(r+q) ≤ a^r := pow_le_pow_of_le_one ha.le ha1.le (by omega)
  have hsection (u : ℝ) (hu : u ∈ Ioo (a^(r+q)) (a^r)) :
      Real.exp (-(δ^2+1))*δ*a^(r*(r+q))*u⁻¹ ≤ F u := by
    have hu0 : 0 < u := (pow_pos ha _).trans hu.1
    let b := δ*a^(r*(r+q))/u^r
    have hb0 : 0 < b := by dsimp [b]; positivity
    have hpow : a^(r*(r+q)) ≤ u^r := by
      have hh := pow_le_pow_left₀ (pow_nonneg ha.le (r+q)) hu.1.le r
      simpa only [← pow_mul, Nat.mul_comm (r+q) r] using hh
    have hbδ : b ≤ δ := (div_le_iff₀ (pow_pos hu0 r)).mpr (mul_le_mul_of_nonneg_left hpow hδ.le)
    have hk (t : ℝ) (ht : t ∈ Ioo 0 b) :
        u^(r-1)*Real.exp (-(δ^2+1)) ≤ generalWeightedKernel r q N (u,t) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu0.le _)
      apply Real.exp_le_exp.mpr
      have hut : u^r*t ≤ δ*a^(r*(r+q)) := by
        have hh := (le_div_iff₀ (pow_pos hu0 r)).mp ht.2.le
        simpa only [mul_comm] using hh
      have hut2 := pow_le_pow_left₀ (mul_nonneg (pow_nonneg hu0.le _) ht.1.le) hut 2
      have hup := pow_le_pow_left₀ hu0.le hu.2.le (2*(r+q))
      have he : u^(2*r)*(t^2+u^(2*q)) = (u^r*t)^2+u^(2*(r+q)) := by
        rw [mul_add,mul_pow,← pow_mul,← pow_add]
        rw [show r*2 = 2*r by omega, show 2*r+2*q = 2*(r+q) by ring]
      have hae1 : (a^(r*(r+q)))^2 = a^(2*r*(r+q)) := by rw [← pow_mul]; congr 1; ring
      have hae2 : (a^r)^(2*(r+q)) = a^(2*r*(r+q)) := by rw [← pow_mul]; congr 1; ring
      rw [show (δ*a^(r*(r+q)))^2 = δ^2*a^(2*r*(r+q)) by rw [mul_pow,hae1]] at hut2
      rw [hae2] at hup
      dsimp only [generalWeightedKernel]
      rw [he]
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add hut2 hup) hN.le]
    have hsmall := setIntegral_mono_on
      (integrableOn_const (by simp [Real.volume_Ioo]) : IntegrableOn
        (fun _ : ℝ => u^(r-1)*Real.exp (-(δ^2+1))) (Ioo 0 b) volume)
      (((by unfold generalWeightedKernel; fun_prop : Continuous (fun t => generalWeightedKernel r q N (u,t))).continuousOn.integrableOn_compact
        isCompact_Icc).mono_set Ioo_subset_Icc_self) measurableSet_Ioo hk
    have he : (∫ _t : ℝ in Ioo 0 b, u^(r-1)*Real.exp (-(δ^2+1))) =
        Real.exp (-(δ^2+1))*δ*a^(r*(r+q))*u⁻¹ := by
      rw [setIntegral_const,Measure.real,Real.volume_Ioo,sub_zero,ENNReal.toReal_ofReal hb0.le,smul_eq_mul]
      dsimp [b]
      have huR : u^r = u^(r-1)*u := by rw [← pow_succ]; congr 1; omega
      rw [huR]
      field_simp
    rw [he] at hsmall
    exact hsmall.trans (setIntegral_mono_set
      (((by unfold generalWeightedKernel; fun_prop : Continuous (fun t => generalWeightedKernel r q N (u,t))).continuousOn.integrableOn_compact
        isCompact_Icc).mono_set Ioo_subset_Icc_self)
      (Filter.Eventually.of_forall (fun _ => mul_nonneg (pow_nonneg hu0.le _) (Real.exp_pos _).le))
      (Filter.Eventually.of_forall (Ioo_subset_Ioo le_rfl hbδ)))
  have hlo := setIntegral_mono_on
    ((integrableOn_Ioo_inv_positive (a^(r+q)) (a^r) (pow_pos ha _)).const_mul
      (Real.exp (-(δ^2+1))*δ*a^(r*(r+q))))
    (hF.mono_set (Ioo_subset_Ioo (pow_nonneg ha.le _) haε)) measurableSet_Ioo hsection
  rw [integral_const_mul, integral_Ioo_inv_positive _ _ (pow_pos ha _) (pow_pos ha _) hab,
    Real.log_pow,Real.log_pow] at hlo
  have helog : (r:ℝ)*Real.log a - (r+q:ℕ)*Real.log a = (q:ℝ)*(-Real.log a) := by push_cast; ring
  rw [helog] at hlo
  unfold generalWeightedBox
  rw [Measure.volume_eq_prod,setIntegral_prod _ (by simpa only [Measure.volume_eq_prod] using hi)]
  exact hlo.trans (setIntegral_mono_set hF
    (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        exact integral_nonneg (fun t => mul_nonneg (pow_nonneg hu.1.le _) (Real.exp_pos _).le))
    (Filter.Eventually.of_forall (Ioo_subset_Ioo (pow_nonneg ha.le _) haε)))

/-- Every positive correction degree retains the critical logarithm. -/
theorem generalWeightedBox_lower (r q : ℕ) (hr : 0 < r) (hq : 0 < q)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    CriticalLaplaceLower (generalWeightedBox r q ε δ) := by
  let D : ℝ := 2*(r:ℝ)*((r:ℝ)+q)
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨Real.exp (-(δ^2+1))*δ*(q:ℝ)/D, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp (D*(|Real.log ε|+1)))] with N hN
  have hN0 : 0 < N := (Real.exp_pos _).trans_le hN
  have hlog : D*(|Real.log ε|+1) ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos _) hN
  let a := Real.exp (-Real.log N/D)
  have ha : 0 < a := Real.exp_pos _
  have harg : -Real.log N/D ≤ -(|Real.log ε|+1) := (div_le_iff₀ hD).mpr (by nlinarith)
  have ha1 : a < 1 := Real.exp_lt_one_iff.mpr (by linarith [abs_nonneg (Real.log ε)])
  have haε : a^r ≤ ε := by
    have haa : a^r ≤ a := by simpa using pow_le_pow_of_le_one ha.le ha1.le hr
    apply haa.trans
    rw [← Real.exp_log hε]
    exact Real.exp_le_exp.mpr (by linarith [neg_abs_le (Real.log ε)])
  have hcast : ((2*r*(r+q):ℕ):ℝ) = D := by dsimp [D]; push_cast; ring
  have hscale : N*a^(2*r*(r+q)) = 1 := by
    rw [← Real.exp_nat_mul, hcast]
    have he : D*(-Real.log N/D) = -Real.log N := by field_simp
    rw [he,Real.exp_neg,Real.exp_log hN0]
    exact mul_inv_cancel₀ hN0.ne'
  have hap : a^(r*(r+q)) = N^(-(1/2:ℝ)) := by
    rw [Real.rpow_def_of_pos hN0, ← Real.exp_nat_mul]
    congr 1
    have hc : ((r*(r+q):ℕ):ℝ) = D/2 := by dsimp [D]; push_cast; ring
    rw [hc]
    field_simp
  have halog : Real.log a = -Real.log N/D := Real.log_exp _
  have hl := generalWeightedBox_strip_lower r q hr hq ε δ N a hδ ha ha1 haε hN0 hscale
  rw [hap,halog] at hl
  convert hl using 1; unfold criticalLaplaceRate; ring

/-- Independent homogeneous and correction degrees on every fixed positive rectangle. -/
theorem generalWeightedBox_has_order (r q : ℕ) (hr : 0 < r) (hq : 0 < q)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    HasCriticalLaplaceOrder (generalWeightedBox r q ε δ) :=
  ⟨generalWeightedBox_lower r q hr hq ε δ hε hδ, generalWeightedBox_upper r q hr ε δ hε hδ⟩

@[expose] def generalWeightedSymmetric (r q : ℕ) (ε δ N : ℝ) : ℝ :=
  ∫ z in Ioo 0 ε ×ˢ Ioo (-δ) δ, generalWeightedKernel r q N z

theorem generalWeightedSymmetric_eq (r q : ℕ) (ε δ N : ℝ) (hδ : 0 < δ) :
    generalWeightedSymmetric r q ε δ N = 2 * generalWeightedBox r q ε δ N := by
  have hi (a b : ℝ) : IntegrableOn (generalWeightedKernel r q N)
      (Ioo 0 ε ×ˢ Ioo a b) (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using generalWeighted_integrable r q N ε a b
  unfold generalWeightedSymmetric generalWeightedBox
  rw [Measure.volume_eq_prod, setIntegral_prod _ (hi (-δ) δ), setIntegral_prod _ (hi 0 δ), ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u _
  exact integral_even_Ioo (fun t => generalWeightedKernel r q N (u,t))
    (by unfold generalWeightedKernel; fun_prop) (fun t => by simp [generalWeightedKernel]) δ hδ

theorem generalWeightedSymmetric_has_order (r q : ℕ) (hr : 0 < r) (hq : 0 < q)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    HasCriticalLaplaceOrder (generalWeightedSymmetric r q ε δ) := by
  have h := generalWeightedBox_has_order r q hr hq ε δ hε hδ
  constructor
  · exact (h.1.const_mul 2 (by norm_num)).mono (Filter.Eventually.of_forall (fun N =>
      (generalWeightedSymmetric_eq r q ε δ N hδ).ge))
  · exact (h.2.const_mul 2 (by norm_num)).mono (Filter.Eventually.of_forall (fun N =>
      (generalWeightedSymmetric_eq r q ε δ N hδ).le))

end ResidualSLT
