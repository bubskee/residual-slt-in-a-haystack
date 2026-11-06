module
public import ResidualSLT.CriticalSectorMellin
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Quantitative Laplace bounds for the normalized critical cancellation model. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Filter
open scoped Topology

@[expose] def criticalLaplaceKernel (q : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.exp (-(z.1 ^ 2 * (z.2 ^ 2 + z.1 ^ 2)) / q ^ 4)

@[expose] def criticalLaplace (N : ℝ) : ℝ :=
  ∫ z : ℝ × ℝ in cancellationRectangle,
    Real.exp (-N * (z.1 ^ 2 * (z.2 ^ 2 + z.1 ^ 2)))

/-- A Gaussian section bound with a uniform constant. -/
theorem gaussian_unit_section_le (a : ℝ) (ha : 0 < a) :
    (∫ t : ℝ in Ioo 0 1, Real.exp (-((a * t) ^ 2))) ≤ Real.sqrt Real.pi / a := by
  have he : (fun t : ℝ => Real.exp (-((a * t) ^ 2))) =
      (fun t : ℝ => Real.exp (-(a ^ 2) * t ^ 2)) := by funext t; congr 1; ring
  rw [he]
  calc
    _ ≤ ∫ t : ℝ, Real.exp (-(a ^ 2) * t ^ 2) :=
      setIntegral_le_integral (integrable_exp_neg_mul_sq (sq_pos_of_pos ha))
        (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))
    _ = Real.sqrt Real.pi / a := by
      rw [integral_gaussian, Real.sqrt_div (Real.pi_pos.le), Real.sqrt_sq_eq_abs, abs_of_pos ha]

/-- The normalized kernel is continuous, positive, and bounded by one. -/
theorem criticalLaplaceKernel_bounds (q : ℝ) (z : ℝ × ℝ) :
    0 ≤ criticalLaplaceKernel q z ∧ criticalLaplaceKernel q z ≤ 1 := by
  refine ⟨(Real.exp_pos _).le, ?_⟩
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)

theorem criticalLaplaceKernel_integrable (q : ℝ) :
    IntegrableOn (criticalLaplaceKernel q) cancellationRectangle volume := by
  have hc : Continuous (criticalLaplaceKernel q) := by unfold criticalLaplaceKernel; fun_prop
  exact (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)

theorem criticalLaplaceKernel_section_integrable (q u a b : ℝ) :
    IntegrableOn (fun t => criticalLaplaceKernel q (u, t)) (Ioo a b) volume := by
  have hc : Continuous (fun t => criticalLaplaceKernel q (u, t)) := by
    unfold criticalLaplaceKernel; fun_prop
  exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

/-- Gaussian domination of a transverse section. -/
theorem criticalLaplaceKernel_section_upper (q u : ℝ) (hq : 0 < q) (hu : 0 < u) :
    (∫ t : ℝ in Ioo 0 1, criticalLaplaceKernel q (u, t)) ≤ Real.sqrt Real.pi * q ^ 2 / u := by
  calc
    _ ≤ ∫ t : ℝ in Ioo 0 1, Real.exp (-(((u / q ^ 2) * t) ^ 2)) := by
      apply setIntegral_mono_on (criticalLaplaceKernel_section_integrable q u 0 1)
        ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-(((u / q ^ 2) * t) ^ 2)))).continuousOn.integrableOn_compact
          isCompact_Icc |>.mono_set Ioo_subset_Icc_self) measurableSet_Ioo
      intro t _
      apply Real.exp_le_exp.mpr
      dsimp [criticalLaplaceKernel]
      have hq4 : 0 < q ^ 4 := pow_pos hq _
      field_simp
      nlinarith [sq_nonneg (u ^ 2)]
    _ ≤ Real.sqrt Real.pi / (u / q ^ 2) := gaussian_unit_section_le _ (by positivity)
    _ = Real.sqrt Real.pi * q ^ 2 / u := by field_simp

/-- The shrinking lower-bound strip is contained in the unit transverse interval. -/
theorem criticalLaplaceKernel_strip_lower (q u t : ℝ) (hq : 0 < q) (hu : q ^ 2 ≤ u)
    (huq : u ≤ q) (ht : 0 < t) (htu : t ≤ q ^ 2 / u) :
    Real.exp (-2) ≤ criticalLaplaceKernel q (u, t) := by
  have hu0 : 0 < u := lt_of_lt_of_le (sq_pos_of_pos hq) hu
  have hut : u * t ≤ q ^ 2 := by nlinarith [(le_div_iff₀ hu0).mp htu]
  have hut2 : u ^ 2 * t ^ 2 ≤ q ^ 4 := by
    have := pow_le_pow_left₀ (mul_nonneg hu0.le ht.le) hut 2
    nlinarith
  have hu4 : u ^ 4 ≤ q ^ 4 := pow_le_pow_left₀ hu0.le huq 4
  apply Real.exp_le_exp.mpr
  change -2 ≤ -(u ^ 2 * (t ^ 2 + u ^ 2)) / q ^ 4
  apply (le_div_iff₀ (pow_pos hq 4)).mpr
  nlinarith


/-- Additivity on adjacent open intervals, with integrability supplied explicitly. -/
theorem integral_Ioo_split {g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hi : IntegrableOn g (Ioo a c) volume) :
    (∫ x in Ioo a c, g x) = (∫ x in Ioo a b, g x) + ∫ x in Ioo b c, g x := by
  have h1 := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr
    (hi.mono_set (Ioo_subset_Ioo le_rfl hbc))
  have h2 := (intervalIntegrable_iff_integrableOn_Ioo_of_le hbc).mpr
    (hi.mono_set (Ioo_subset_Ioo hab le_rfl))
  simpa only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hbc,
    intervalIntegral.integral_of_le (hab.trans hbc), integral_Ioc_eq_integral_Ioo] using
    (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm

theorem criticalLaplaceKernel_sections_integrable (q : ℝ) :
    IntegrableOn (fun u => ∫ t : ℝ in Ioo 0 1, criticalLaplaceKernel q (u, t)) (Ioo 0 1) volume := by
  have hi := criticalLaplaceKernel_integrable q
  rw [IntegrableOn, cancellationRectangle, Measure.volume_eq_prod, ← Measure.prod_restrict] at hi
  exact hi.integral_prod_left

theorem criticalLaplaceKernel_fubini (q : ℝ) :
    (∫ z in cancellationRectangle, criticalLaplaceKernel q z) =
      ∫ u : ℝ in Ioo 0 1, ∫ t : ℝ in Ioo 0 1, criticalLaplaceKernel q (u, t) := by
  have hi := criticalLaplaceKernel_integrable q
  rw [cancellationRectangle, Measure.volume_eq_prod] at hi ⊢
  exact setIntegral_prod _ hi

theorem integral_Ioo_inv_positive (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    (∫ u : ℝ in Ioo a b, u⁻¹) = Real.log b - Real.log a := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
    integral_inv_of_pos ha hb, Real.log_div hb.ne' ha.ne']

theorem integrableOn_Ioo_inv_positive (a b : ℝ) (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => u⁻¹) (Ioo a b) volume := by
  exact ((continuousOn_id.inv₀ (fun u hu => (ha.trans_le hu.1).ne')).integrableOn_compact
    isCompact_Icc).mono_set Ioo_subset_Icc_self

/-- Explicit lower strip contribution, prior to absorbing constants into asymptotic notation. -/
theorem criticalLaplaceKernel_lower (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    Real.exp (-2) * q ^ 2 * (-Real.log q) ≤
      ∫ z in cancellationRectangle, criticalLaplaceKernel q z := by
  let F : ℝ → ℝ := fun u => ∫ t : ℝ in Ioo 0 1, criticalLaplaceKernel q (u, t)
  have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq
  have hqq : q ^ 2 < q := by nlinarith
  have hF := criticalLaplaceKernel_sections_integrable q
  have hsection (u : ℝ) (hu : u ∈ Ioo (q ^ 2) q) :
      Real.exp (-2) * q ^ 2 * u⁻¹ ≤ F u := by
    have hu0 : 0 < u := hq2.trans hu.1
    have hb0 : 0 < q ^ 2 / u := div_pos hq2 hu0
    have hb1 : q ^ 2 / u ≤ 1 := (div_le_one hu0).mpr hu.1.le
    have hmono := setIntegral_mono_set (criticalLaplaceKernel_section_integrable q u 0 1)
      (Filter.Eventually.of_forall (fun t => (criticalLaplaceKernel_bounds q (u,t)).1))
      (Filter.Eventually.of_forall (Ioo_subset_Ioo (a₁ := (0 : ℝ)) le_rfl hb1))
    have hlo : (∫ _t : ℝ in Ioo 0 (q ^ 2 / u), Real.exp (-2)) ≤
        ∫ t : ℝ in Ioo 0 (q ^ 2 / u), criticalLaplaceKernel q (u,t) := by
      apply setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Ioo]))
        (criticalLaplaceKernel_section_integrable q u 0 _) measurableSet_Ioo
      intro t ht
      exact criticalLaplaceKernel_strip_lower q u t hq hu.1.le hu.2.le ht.1 ht.2.le
    have he : (∫ _t : ℝ in Ioo 0 (q ^ 2 / u), Real.exp (-2)) = Real.exp (-2) * q ^ 2 * u⁻¹ := by
      rw [setIntegral_const, Measure.real, Real.volume_Ioo, sub_zero,
        ENNReal.toReal_ofReal hb0.le, smul_eq_mul]
      ring
    rw [he] at hlo
    exact hlo.trans hmono
  have hi := (integrableOn_Ioo_inv_positive (q ^ 2) q hq2).const_mul (Real.exp (-2) * q ^ 2)
  have hlo := setIntegral_mono_on hi (hF.mono_set (Ioo_subset_Ioo hq2.le hq1.le))
    measurableSet_Ioo hsection
  have he : (∫ u : ℝ in Ioo (q ^ 2) q, Real.exp (-2) * q ^ 2 * u⁻¹) =
      Real.exp (-2) * q ^ 2 * (-Real.log q) := by
    rw [integral_const_mul, integral_Ioo_inv_positive _ _ hq2 hq hqq.le, Real.log_pow]
    ring
  rw [he] at hlo
  rw [criticalLaplaceKernel_fubini]
  exact hlo.trans (setIntegral_mono_set hF
    (Filter.Eventually.of_forall (fun u => integral_nonneg (fun t => (criticalLaplaceKernel_bounds q (u,t)).1)))
    (Filter.Eventually.of_forall (Ioo_subset_Ioo hq2.le hq1.le)))

/-- The product Gaussian majorant gives the logarithmic upper bound. -/
theorem criticalLaplaceKernel_upper (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    (∫ z in cancellationRectangle, criticalLaplaceKernel q z) ≤
      q ^ 2 * (1 - 2 * Real.sqrt Real.pi * Real.log q) := by
  let F : ℝ → ℝ := fun u => ∫ t : ℝ in Ioo 0 1, criticalLaplaceKernel q (u,t)
  have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq
  have hq21 : q ^ 2 < 1 := by nlinarith
  have hF := criticalLaplaceKernel_sections_integrable q
  have hsmall : (∫ u : ℝ in Ioo 0 (q ^ 2), F u) ≤ q ^ 2 := by
    have hb (u : ℝ) : F u ≤ 1 := by
      have h := setIntegral_mono_on (criticalLaplaceKernel_section_integrable q u 0 1)
        (integrableOn_const (by simp [Real.volume_Ioo]) : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 1) volume)
        measurableSet_Ioo (fun t _ => (criticalLaplaceKernel_bounds q (u,t)).2)
      simpa using h
    have h := setIntegral_mono_on (hF.mono_set (Ioo_subset_Ioo le_rfl hq21.le))
      (integrableOn_const (by simp [Real.volume_Ioo]) : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 (q ^ 2)) volume)
      measurableSet_Ioo (fun u _ => hb u)
    simpa [Real.volume_Ioo, hq2.le] using h
  have hlarge : (∫ u : ℝ in Ioo (q ^ 2) 1, F u) ≤
      Real.sqrt Real.pi * q ^ 2 * (-2 * Real.log q) := by
    have hi := (integrableOn_Ioo_inv_positive (q ^ 2) 1 hq2).const_mul (Real.sqrt Real.pi * q ^ 2)
    have h := setIntegral_mono_on (hF.mono_set (Ioo_subset_Ioo hq2.le le_rfl)) hi measurableSet_Ioo
      (fun u hu => by simpa only [div_eq_mul_inv] using
        criticalLaplaceKernel_section_upper q u hq (hq2.trans hu.1))
    rw [integral_const_mul, integral_Ioo_inv_positive _ _ hq2 zero_lt_one hq21.le, Real.log_one,
      Real.log_pow] at h
    norm_num only [Nat.cast_ofNat, zero_sub] at h
    simpa only [neg_mul] using h
  rw [criticalLaplaceKernel_fubini, integral_Ioo_split hq2.le hq21.le hF]
  dsimp only [F] at hsmall hlarge
  nlinarith


/-- Explicit two-sided critical model bounds for every N≥exp(4). -/
theorem criticalLaplace_bounds (N : ℝ) (hN : Real.exp 4 ≤ N) :
    (Real.exp (-2) / 4) * (N ^ (-(1 / 2 : ℝ)) * Real.log N) ≤ criticalLaplace N ∧
    criticalLaplace N ≤ (1 + Real.sqrt Real.pi) * (N ^ (-(1 / 2 : ℝ)) * Real.log N) := by
  have hN0 : 0 < N := (Real.exp_pos 4).trans_le hN
  have hlog : 4 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 4) hN
  let q := Real.exp (-Real.log N / 4)
  have hq : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hq4 : q ^ 4 = N⁻¹ := by
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    have he : (4 : ℝ) * (-Real.log N / 4) = -Real.log N := by ring
    rw [he, Real.exp_neg, Real.exp_log hN0]
  have hq2 : q ^ 2 = N ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_def_of_pos hN0, ← Real.exp_nat_mul]
    congr 1
    ring
  have hqlog : Real.log q = -Real.log N / 4 := Real.log_exp _
  have hmodel : (∫ z in cancellationRectangle, criticalLaplaceKernel q z) = criticalLaplace N := by
    apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
    intro z _
    unfold criticalLaplaceKernel
    rw [hq4, div_inv_eq_mul]
    congr 1
    ring
  have hlo := criticalLaplaceKernel_lower q hq hq1
  have hup := criticalLaplaceKernel_upper q hq hq1
  rw [hmodel, hq2, hqlog] at hlo hup
  have hpow : 0 < N ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hpi : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  constructor
  · nlinarith
  · nlinarith [mul_nonneg hpi hpow.le, mul_nonneg hpi (show 0 ≤ Real.log N by linarith),
      mul_le_mul_of_nonneg_left hlog hpow.le]

/-- A genuine Laplace-order certificate for the critical model, separate from its
integrability threshold and real Mellin pole calculation. -/
theorem criticalLaplace_two_sided :
    ∃ c C N₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      c * (N ^ (-(1 / 2 : ℝ)) * Real.log N) ≤ criticalLaplace N ∧
      criticalLaplace N ≤ C * (N ^ (-(1 / 2 : ℝ)) * Real.log N) := by
  exact ⟨Real.exp (-2) / 4, 1 + Real.sqrt Real.pi, Real.exp 4, by positivity,
    by positivity, Real.one_lt_exp_iff.mpr (by norm_num), criticalLaplace_bounds⟩

end ResidualSLT
