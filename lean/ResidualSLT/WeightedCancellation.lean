module
public import ResidualSLT.ProductPowers

/-! Weighted cancellation integrals. All measures in this file are raw Lebesgue
measure; the radial Jacobian is included explicitly in the integrand. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Set

@[expose] def cancellationRectangle : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo 0 1

@[expose] def weightedCancellation (a : ℝ) (r d : ℕ) (s : ℝ) (z : ℝ × ℝ) : ℝ :=
  z.1 ^ (a - 1) * (z.1 ^ (2 * r) * (z.2 ^ 2 + z.1 ^ (2 * d))) ^ (-s)

theorem weightedCancellation_measurable (a : ℝ) (r d : ℕ) (s : ℝ) :
    Measurable (weightedCancellation a r d s) := by
  unfold weightedCancellation
  fun_prop

/-- Product powers on the positive unit square, including endpoint divergence. -/
theorem rectangle_rpow_integrable_iff (p q : ℝ) :
    IntegrableOn (fun z : ℝ × ℝ => z.1 ^ p * z.2 ^ q) cancellationRectangle volume ↔
      -1 < p ∧ -1 < q := by
  have hm : (volume.restrict (Ioo (0 : ℝ) 1)) ≠ 0 := by
    simp [Measure.restrict_eq_zero, Real.volume_Ioo]
  have hn (e : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Ioo 0 1), x ^ e ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (Real.rpow_pos_of_pos hx.1 _).ne'
  rw [IntegrableOn, cancellationRectangle, Measure.volume_eq_prod, ← Measure.prod_restrict,
    integrable_prod_mul_iff_of_ae_ne_zero hm hm (hn p) (hn q)]
  exact and_congr (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num))
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num))

/-- A factorized majorant: split the singular exponent between transverse and radial terms. -/
theorem weightedCancellation_le_product (a : ℝ) (r d : ℕ) (u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (z : ℝ × ℝ) (hz : z ∈ cancellationRectangle) :
    weightedCancellation a r d (u + v) z ≤
      z.1 ^ (a - 1 - 2 * r * (u + v) - 2 * d * v) * z.2 ^ (-2 * u) := by
  obtain ⟨hx, ht⟩ := hz
  have hx0 : 0 < z.1 := hx.1
  have ht0 : 0 < z.2 := ht.1
  have hsum : 0 < z.2 ^ 2 + z.1 ^ (2 * d) := by positivity
  have h1 : (z.2 ^ 2 + z.1 ^ (2 * d)) ^ (-u) ≤ (z.2 ^ 2) ^ (-u) :=
    Real.rpow_le_rpow_of_nonpos (pow_pos ht.1 _) (le_add_of_nonneg_right (by positivity)) (by linarith)
  have h2 : (z.2 ^ 2 + z.1 ^ (2 * d)) ^ (-v) ≤ (z.1 ^ (2 * d)) ^ (-v) :=
    Real.rpow_le_rpow_of_nonpos (pow_pos hx.1 _) (le_add_of_nonneg_left (sq_nonneg _)) (by linarith)
  have hb := mul_le_mul h1 h2 (Real.rpow_nonneg hsum.le _) (Real.rpow_nonneg (by positivity) _)
  rw [← Real.rpow_add hsum, ← neg_add] at hb
  unfold weightedCancellation
  rw [Real.mul_rpow (by positivity) hsum.le]
  have hmul := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ z.1 ^ (a - 1) * (z.1 ^ (2 * r)) ^ (-(u + v)) by positivity)
  simp only [← mul_assoc] at hmul ⊢
  convert hmul using 1
  rw [← Real.rpow_natCast_mul hx.1.le, ← Real.rpow_natCast_mul hx.1.le,
    ← Real.rpow_natCast_mul ht.1.le]
  push_cast
  rw [show (2 : ℝ) * -u = -2 * u by ring]
  calc
    z.1 ^ (a - 1 - 2 * r * (u + v) - 2 * d * v) * z.2 ^ (-2 * u) =
      (z.1 ^ (a - 1) * z.1 ^ ((2 * r) * -(u + v)) * z.1 ^ ((2 * d) * -v)) *
        z.2 ^ (-2 * u) := by
          rw [← Real.rpow_add hx.1, ← Real.rpow_add hx.1]
          congr 2; ring
    _ = _ := by ring

/-- Strict threshold inequalities provide exponents for the product majorant. -/
theorem cancellation_exponent_split (a R D s : ℝ) (_hR : 0 < R) (hD : 0 < D)
    (hs : 0 < s) (h1 : 2 * R * s < a) (h2 : 2 * (R + D) * s < a + D) :
    ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ u + v = s ∧ 2 * u < 1 ∧
      2 * R * s + 2 * D * v < a := by
  have hgap : max 0 (s - 1 / 2) < min s ((a - 2 * R * s) / (2 * D)) := by
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    constructor
    · exact ⟨hs, div_pos (by linarith) (by positivity)⟩
    · constructor
      · linarith
      · rw [lt_div_iff₀ (by positivity : 0 < 2 * D)]
        nlinarith
  obtain ⟨v, hv, hv'⟩ := exists_between hgap
  have hv0 := (max_lt_iff.mp hv).1
  have hvs := (lt_min_iff.mp hv').1
  have hvb := (lt_div_iff₀ (by positivity : 0 < 2 * D)).mp (lt_min_iff.mp hv').2
  refine ⟨s - v, v, by linarith, hv0.le, by ring, ?_, ?_⟩
  · have := (max_lt_iff.mp hv).2
    linarith
  · nlinarith

/-- Convergence below both candidate thresholds, for positive singular exponents. -/
theorem weightedCancellation_integrable_of_pos (a : ℝ) (r d : ℕ)
    (hr : 0 < r) (hd : 0 < d) (s : ℝ) (hs : 0 < s)
    (h1 : 2 * r * s < a) (h2 : 2 * ((r : ℝ) + d) * s < a + d) :
    IntegrableOn (weightedCancellation a r d s) cancellationRectangle volume := by
  obtain ⟨u, v, hu, hv, huv, hut, hvr⟩ := cancellation_exponent_split a r d s
    (by exact_mod_cast hr) (by exact_mod_cast hd) hs h1 h2
  have hi := (rectangle_rpow_integrable_iff
    (a - 1 - 2 * r * (u + v) - 2 * d * v) (-2 * u)).mpr
    (by rw [huv]; constructor <;> linarith)
  apply hi.mono_nonneg (weightedCancellation_measurable a r d s).aestronglyMeasurable _ _
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
    have hx0 : 0 < z.1 := hz.1.1
    exact mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.rpow_nonneg (by positivity) _)
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
    rw [← huv]
    exact weightedCancellation_le_product a r d u v hu hv z hz

/-- Separate the radial homogeneous factor on the positive half-plane. -/
theorem weightedCancellation_factor (a : ℝ) (r d : ℕ) (s : ℝ)
    (x t : ℝ) (hx : 0 < x) :
    weightedCancellation a r d s (x, t) =
      x ^ (a - 1 - 2 * r * s) * (t ^ 2 + x ^ (2 * d)) ^ (-s) := by
  have hsum : 0 ≤ t ^ 2 + x ^ (2 * d) := by positivity
  unfold weightedCancellation
  dsimp only
  rw [Real.mul_rpow (by positivity) hsum, ← Real.rpow_natCast_mul hx.le,
    ← mul_assoc, ← Real.rpow_add hx]
  congr 2
  push_cast
  ring

/-- A lower bound on every transverse section; it detects the radial obstruction. -/
theorem weightedCancellation_lower_flat (a : ℝ) (r d : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (x t : ℝ) (hx : x ∈ Ioo 0 1) (ht : t ∈ Ioo 0 1) :
    (2 : ℝ) ^ (-s) * x ^ (a - 1 - 2 * r * s) ≤
      weightedCancellation a r d s (x, t) := by
  have hx0 : 0 < x := hx.1
  have ht0 : 0 < t := ht.1
  have hsum : 0 < t ^ 2 + x ^ (2 * d) := by positivity
  have hb : t ^ 2 + x ^ (2 * d) ≤ 2 := by
    have := pow_le_one₀ (n := 2 * d) hx.1.le hx.2.le
    have := pow_le_one₀ (n := 2) ht.1.le ht.2.le
    linarith
  rw [weightedCancellation_factor a r d s x t hx.1, mul_comm]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hsum hb (by linarith)) (Real.rpow_nonneg hx.1.le _)

/-- On the shrinking core 0<t<x^d, the loss has radial order 2(r+d). -/
theorem weightedCancellation_lower_core (a : ℝ) (r d : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (x t : ℝ) (hx : 0 < x) (ht : t ∈ Ioo 0 (x ^ d)) :
    (2 : ℝ) ^ (-s) * x ^ (a - 1 - 2 * ((r : ℝ) + d) * s) ≤
      weightedCancellation a r d s (x, t) := by
  have ht0 : 0 < t := ht.1
  have hsum : 0 < t ^ 2 + x ^ (2 * d) := by positivity
  have hb : t ^ 2 + x ^ (2 * d) ≤ 2 * x ^ (2 * d) := by
    have hp := pow_le_pow_left₀ ht.1.le ht.2.le 2
    rw [← pow_mul, Nat.mul_comm d 2] at hp
    linarith
  have h := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hsum hb (neg_nonpos.mpr hs))
    (Real.rpow_nonneg hx.le (a - 1 - 2 * r * s))
  rw [← weightedCancellation_factor a r d s x t hx] at h
  convert h using 1
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity),
    ← Real.rpow_natCast_mul hx.le, ← mul_assoc,
    mul_comm (x ^ (a - 1 - 2 * r * s)), mul_assoc, mul_assoc, ← Real.rpow_add hx]
  congr 2
  push_cast
  ring

/-- Integrability forces the first strict inequality, including exclusion of equality. -/
theorem weightedCancellation_radial_necessary (a : ℝ) (r d : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hi : IntegrableOn (weightedCancellation a r d s) cancellationRectangle volume) :
    2 * r * s < a := by
  have hg : IntegrableOn (fun z : ℝ × ℝ =>
      (2 : ℝ) ^ (-s) * (z.1 ^ (a - 1 - 2 * r * s) * z.2 ^ (0 : ℝ)))
      cancellationRectangle volume := by
    apply hi.mono_nonneg (by fun_prop) _ _
    · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
      have hx : 0 < z.1 := hz.1.1
      positivity
    · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
      simpa only [Real.rpow_zero, mul_one] using
        weightedCancellation_lower_flat a r d s hs z.1 z.2 hz.1 hz.2
  have hg' := (integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-s)).ne') _).mp hg
  have h := (rectangle_rpow_integrable_iff (a - 1 - 2 * r * s) 0).mp hg'
  linarith [h.1]

/-- Fubini plus integration over the shrinking core forces the second strict inequality. -/
theorem weightedCancellation_core_necessary (a : ℝ) (r d : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hi : IntegrableOn (weightedCancellation a r d s) cancellationRectangle volume) :
    2 * ((r : ℝ) + d) * s < a + d := by
  rw [IntegrableOn, cancellationRectangle, Measure.volume_eq_prod, ← Measure.prod_restrict] at hi
  have hsections := hi.prod_right_ae
  have hnorm := hi.integral_norm_prod_left
  have hg : IntegrableOn (fun x : ℝ => (2 : ℝ) ^ (-s) *
      x ^ (a - 1 - 2 * ((r : ℝ) + d) * s + d)) (Ioo 0 1) volume := by
    apply hnorm.mono_nonneg (by fun_prop) _ _
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hx.1.le _)
    · filter_upwards [hsections, ae_restrict_mem measurableSet_Ioo] with x hi hx
      have hx0 : 0 < x := hx.1
      have hxd : 0 < x ^ d := pow_pos hx.1 _
      have hsub : Ioo 0 (x ^ d) ⊆ Ioo (0 : ℝ) 1 :=
        Ioo_subset_Ioo le_rfl (pow_le_one₀ (n := d) hx.1.le hx.2.le)
      have hiNorm : IntegrableOn (fun t => ‖weightedCancellation a r d s (x, t)‖)
          (Ioo 0 1) volume := hi.norm
      have hi' := hiNorm.mono_set hsub
      have hb : (∫ t in Ioo 0 (x ^ d),
          (2 : ℝ) ^ (-s) * x ^ (a - 1 - 2 * ((r : ℝ) + d) * s)) ≤
          ∫ t in Ioo 0 (x ^ d), ‖weightedCancellation a r d s (x, t)‖ := by
        apply setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Ioo])) hi' measurableSet_Ioo
        intro t ht
        exact (weightedCancellation_lower_core a r d s hs x t hx.1 ht).trans (le_abs_self _)
      have hmono := setIntegral_mono_set hiNorm (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        (Filter.Eventually.of_forall hsub)
      have heq : (∫ t in Ioo 0 (x ^ d),
          (2 : ℝ) ^ (-s) * x ^ (a - 1 - 2 * ((r : ℝ) + d) * s)) =
          (2 : ℝ) ^ (-s) * x ^ (a - 1 - 2 * ((r : ℝ) + d) * s + d) := by
        rw [setIntegral_const, Measure.real, Real.volume_Ioo, sub_zero,
          ENNReal.toReal_ofReal hxd.le, smul_eq_mul, Real.rpow_add hx.1,
          Real.rpow_natCast]
        ring
      rw [heq] at hb
      exact hb.trans hmono
  have hg' := (integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-s)).ne') _).mp hg
  have h := (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).mp hg'
  linarith

/-- Nonpositive singular exponents are integrable for every positive radial dimension. -/
theorem weightedCancellation_integrable_of_nonpos (a : ℝ) (ha : 0 < a) (r d : ℕ)
    (s : ℝ) (hs : s ≤ 0) :
    IntegrableOn (weightedCancellation a r d s) cancellationRectangle volume := by
  have hi := ((rectangle_rpow_integrable_iff (a - 1) 0).mpr
    (by constructor <;> linarith)).const_mul ((2 : ℝ) ^ (-s))
  apply hi.mono_nonneg (weightedCancellation_measurable a r d s).aestronglyMeasurable _ _
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
    have hx : 0 < z.1 := hz.1.1
    unfold weightedCancellation
    positivity
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
    have hx : 0 < z.1 := hz.1.1
    have ht : 0 < z.2 := hz.2.1
    have hsum : 0 ≤ z.2 ^ 2 + z.1 ^ (2 * d) := by positivity
    have hsum2 : z.2 ^ 2 + z.1 ^ (2 * d) ≤ 2 := by
      have := pow_le_one₀ (n := 2) ht.le hz.2.2.le
      have := pow_le_one₀ (n := 2 * d) hx.le hz.1.2.le
      linarith
    have hb : z.1 ^ (2 * r) * (z.2 ^ 2 + z.1 ^ (2 * d)) ≤ 2 :=
      (mul_le_mul_of_nonneg_right (pow_le_one₀ hx.le hz.1.2.le) hsum).trans
        (by simpa using hsum2)
    have hp := Real.rpow_le_rpow (by positivity) hb (neg_nonneg.mpr hs)
    simpa only [weightedCancellation, Real.rpow_zero, mul_one, one_mul, mul_comm] using
      mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hx.le (a - 1))

/-- Exact weighted model criterion for every real exponent. No coordinate reduction is assumed.
The two strict inequalities also certify divergence at both candidate endpoints. -/
theorem weightedCancellation_integrableOn_iff (a : ℝ) (ha : 0 < a) (r d : ℕ)
    (hr : 0 < r) (hd : 0 < d) (s : ℝ) :
    IntegrableOn (weightedCancellation a r d s) cancellationRectangle volume ↔
      s < min (a / (2 * r)) ((a + d) / (2 * ((r : ℝ) + d))) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [lt_min_iff, lt_div_iff₀ (by positivity : 0 < 2 * (r : ℝ)),
    lt_div_iff₀ (by positivity : 0 < 2 * ((r : ℝ) + d))]
  by_cases hs : 0 < s
  · constructor
    · intro hi
      exact ⟨by nlinarith [weightedCancellation_radial_necessary a r d s hs.le hi],
        by nlinarith [weightedCancellation_core_necessary a r d s hs.le hi]⟩
    · rintro ⟨h1, h2⟩
      exact weightedCancellation_integrable_of_pos a r d hr hd s hs
        (by nlinarith) (by nlinarith)
  · have hs' : s ≤ 0 := le_of_not_gt hs
    constructor
    · intro _
      constructor <;> nlinarith
    · intro _
      exact weightedCancellation_integrable_of_nonpos a ha r d s hs'

/-- Network model specialization, with the radial dimension kept as a positive real. -/
theorem weightedNetworkModel_integrableOn_iff (a : ℝ) (ha : 0 < a) (r : ℕ)
    (hr : 0 < r) (s : ℝ) :
    IntegrableOn (weightedCancellation a r r s) cancellationRectangle volume ↔
      s < min (a / (2 * r)) ((a + r) / (4 * r)) := by
  simpa only [show 2 * ((r : ℝ) + r) = 4 * r by ring] using
    weightedCancellation_integrableOn_iff a ha r r hr hr s

/-- Reflection gives the full transverse neighborhood, with its zero slice handled a.e. -/
theorem integrableOn_even_transverse_iff (f : ℝ × ℝ → ℝ)
    (hf : ∀ x t, f (x, -t) = f (x, t)) :
    IntegrableOn f (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) volume ↔
      IntegrableOn f cancellationRectangle volume := by
  have hn : IntegrableOn f (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 0) volume ↔
      IntegrableOn f cancellationRectangle volume := by
    have hp := (MeasurePreserving.id (volume : Measure ℝ)).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
    have he := hp.integrableOn_comp_preimage
      ((Homeomorph.refl ℝ).prodCongr (Homeomorph.neg ℝ)).measurableEmbedding
      (f := f) (s := cancellationRectangle)
    have hcomp : f ∘ Prod.map id Neg.neg = f := by
      funext z
      exact hf z.1 z.2
    have hpre : (Prod.map (id : ℝ → ℝ) Neg.neg) ⁻¹' cancellationRectangle =
        Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 0 := by
      ext z
      change (0 < z.1 ∧ z.1 < 1) ∧ (0 < -z.2 ∧ -z.2 < 1) ↔
        (0 < z.1 ∧ z.1 < 1) ∧ (-1 < z.2 ∧ z.2 < 0)
      constructor <;> rintro ⟨hx, ht, ht'⟩ <;> exact ⟨hx, by linarith, by linarith⟩
    rw [hcomp, hpre] at he
    simpa only [Measure.volume_eq_prod] using he
  have hsets : (Ioo (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1) =ᵐ[volume]
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
    rw [Measure.volume_eq_prod]
    apply Measure.set_prod_ae_eq Filter.EventuallyEq.rfl
    filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
    simp only [mem_Ico, mem_Ioo]
    exact propext ⟨fun h => ⟨lt_of_le_of_ne h.1 (Ne.symm ht), h.2⟩,
      fun h => ⟨h.1.le, h.2⟩⟩
  rw [← Ioo_union_Ico_eq_Ioo (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) ≤ 1),
    prod_union, integrableOn_union, hn, integrableOn_congr_set_ae hsets]
  simp only [cancellationRectangle, and_self]

/-- Full transverse interval version of the exact weighted criterion. -/
theorem weightedCancellation_symmetric_integrableOn_iff (a : ℝ) (ha : 0 < a) (r d : ℕ)
    (hr : 0 < r) (hd : 0 < d) (s : ℝ) :
    IntegrableOn (weightedCancellation a r d s) (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) volume ↔
      s < min (a / (2 * r)) ((a + d) / (2 * ((r : ℝ) + d))) := by
  rw [integrableOn_even_transverse_iff _ (by intros; simp [weightedCancellation])]
  exact weightedCancellation_integrableOn_iff a ha r d hr hd s

/-- Explicit phase transition for the weighted network model, not yet a network theorem. -/
theorem weightedNetworkModel_phase_transition (L r : ℕ) (hL : 0 < L) (hr : 0 < r) (s : ℝ) :
    IntegrableOn (weightedCancellation L r r s) (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) volume ↔
      s < (if L < r then (L : ℝ) / (2 * r)
        else if L = r then 1 / 2 else ((L : ℝ) + r) / (4 * r)) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rw [weightedCancellation_symmetric_integrableOn_iff L (by exact_mod_cast hL) r r hr hr]
  have heq : 2 * ((r : ℝ) + r) = 4 * r := by ring
  rw [heq]
  split_ifs with hlt heqL
  · rw [min_eq_left]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h : (L : ℝ) < r := by exact_mod_cast hlt
    nlinarith
  · subst L
    have h1 : (r : ℝ) / (2 * r) = 1 / 2 := by field_simp
    have h2 : ((r : ℝ) + r) / (4 * r) = 1 / 2 := by field_simp; ring
    rw [h1, h2, min_self]
  · rw [min_eq_right]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h : (r : ℝ) ≤ L := by exact_mod_cast (Nat.le_of_not_gt hlt)
    nlinarith

/-- Both obstructions persist on every smaller positive rectangle. -/
theorem weightedCancellation_smallRectangle_necessary (a : ℝ) (r d : ℕ) (hd : 0 < d)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (s : ℝ) (hs : 0 ≤ s)
    (hi : IntegrableOn (weightedCancellation a r d s) (Ioo 0 ε ×ˢ Ioo 0 δ) volume) :
    2 * r * s < a ∧ 2 * ((r : ℝ) + d) * s < a + d := by
  have hp := hi
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hp
  have hm : (volume.restrict (Ioo (0 : ℝ) δ)) ≠ 0 := by
    simp [Measure.restrict_eq_zero, Real.volume_Ioo, hδ]
  let : NeZero (volume.restrict (Ioo (0 : ℝ) δ)) := ⟨hm⟩
  obtain ⟨t, htInt, ht⟩ := (hp.prod_left_ae.and (ae_restrict_mem measurableSet_Ioo)).exists
  have hg : IntegrableOn (fun x : ℝ => (2 : ℝ) ^ (-s) * x ^ (a - 1 - 2 * r * s))
      (Ioo 0 ε) volume := by
    apply htInt.mono_nonneg (by fun_prop) _ _
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hx.1.le _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact weightedCancellation_lower_flat a r d s hs x t
        ⟨hx.1, hx.2.trans_le hε1⟩ ⟨ht.1, ht.2.trans_le hδ1⟩
  have hc : IsUnit ((2 : ℝ) ^ (-s)) :=
    isUnit_iff_ne_zero.mpr (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-s)).ne'
  have hfirst := (intervalIntegral.integrableOn_Ioo_rpow_iff hε).mp
    ((integrable_const_mul_iff hc _).mp hg)
  refine ⟨by linarith, ?_⟩
  let η := min ε δ
  have hη : 0 < η := lt_min hε hδ
  have hiSmall : IntegrableOn (weightedCancellation a r d s) (Ioo 0 η ×ˢ Ioo 0 δ) volume :=
    hi.mono_set (Set.prod_mono (Ioo_subset_Ioo le_rfl (min_le_left _ _)) Subset.rfl)
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hiSmall
  have hnorm := hiSmall.integral_norm_prod_left
  have hg : IntegrableOn (fun x : ℝ => (2 : ℝ) ^ (-s) *
      x ^ (a - 1 - 2 * ((r : ℝ) + d) * s + d)) (Ioo 0 η) volume := by
    apply hnorm.mono_nonneg (by fun_prop) _ _
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hx.1.le _)
    · filter_upwards [hiSmall.prod_right_ae, ae_restrict_mem measurableSet_Ioo] with x hiX hx
      have hx1 : x ≤ 1 := hx.2.le.trans ((min_le_left ε δ).trans hε1)
      have hxd : 0 < x ^ d := pow_pos hx.1 _
      have hsub : Ioo 0 (x ^ d) ⊆ Ioo (0 : ℝ) δ :=
        Ioo_subset_Ioo le_rfl ((pow_le_of_le_one hx.1.le hx1 hd.ne').trans
          (hx.2.le.trans (min_le_right ε δ)))
      have hiNorm : IntegrableOn (fun t => ‖weightedCancellation a r d s (x, t)‖)
          (Ioo 0 δ) volume := hiX.norm
      have hb : (∫ t in Ioo 0 (x ^ d),
          (2 : ℝ) ^ (-s) * x ^ (a - 1 - 2 * ((r : ℝ) + d) * s)) ≤
          ∫ t in Ioo 0 (x ^ d), ‖weightedCancellation a r d s (x, t)‖ := by
        apply setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Ioo]))
          (hiNorm.mono_set hsub) measurableSet_Ioo
        intro t ht
        exact (weightedCancellation_lower_core a r d s hs x t hx.1 ht).trans (le_abs_self _)
      have hmono := setIntegral_mono_set hiNorm (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        (Filter.Eventually.of_forall hsub)
      have heq : (∫ t in Ioo 0 (x ^ d),
          (2 : ℝ) ^ (-s) * x ^ (a - 1 - 2 * ((r : ℝ) + d) * s)) =
          (2 : ℝ) ^ (-s) * x ^ (a - 1 - 2 * ((r : ℝ) + d) * s + d) := by
        rw [setIntegral_const, Measure.real, Real.volume_Ioo, sub_zero,
          ENNReal.toReal_ofReal hxd.le, smul_eq_mul, Real.rpow_add hx.1, Real.rpow_natCast]
        ring
      rw [heq] at hb
      exact hb.trans hmono
  have hsecond := (intervalIntegral.integrableOn_Ioo_rpow_iff hη).mp
    ((integrable_const_mul_iff hc _).mp hg)
  linarith

/-- Exact local criterion on every 0<ε,δ≤1, with a full transverse neighborhood. -/
theorem weightedCancellation_local_integrableOn_iff (a : ℝ) (ha : 0 < a) (r d : ℕ)
    (hr : 0 < r) (hd : 0 < d) (ε δ : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (s : ℝ) :
    IntegrableOn (weightedCancellation a r d s) (Ioo 0 ε ×ˢ Ioo (-δ) δ) volume ↔
      s < min (a / (2 * r)) ((a + d) / (2 * ((r : ℝ) + d))) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · intro hi
    by_cases hs : 0 ≤ s
    · have hp := hi.mono_set (Set.prod_mono Subset.rfl
        (Ioo_subset_Ioo (by linarith : -δ ≤ 0) le_rfl))
      obtain ⟨h1, h2⟩ := weightedCancellation_smallRectangle_necessary a r d hd
        ε δ hε hε1 hδ hδ1 s hs hp
      rw [lt_min_iff, lt_div_iff₀ (by positivity : 0 < 2 * (r : ℝ)),
        lt_div_iff₀ (by positivity : 0 < 2 * ((r : ℝ) + d))]
      constructor <;> nlinarith
    · exact (lt_of_not_ge hs).trans (lt_min (by positivity) (by positivity))
  · intro hs
    exact ((weightedCancellation_symmetric_integrableOn_iff a ha r d hr hd s).mpr hs).mono_set
      (Set.prod_mono (Ioo_subset_Ioo le_rfl hε1) (Ioo_subset_Ioo (by linarith) hδ1))

/-- The same local theorem with the radial Jacobian in the measure itself. -/
theorem cancellationNormalForm_weightedMeasure_iff (a : ℝ) (ha : 0 < a) (r d : ℕ)
    (hr : 0 < r) (hd : 0 < d) (ε δ : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (s : ℝ) :
    IntegrableOn (fun z : ℝ × ℝ =>
      (z.1 ^ (2 * r) * (z.2 ^ 2 + z.1 ^ (2 * d))) ^ (-s))
      (Ioo 0 ε ×ˢ Ioo (-δ) δ)
      (volume.withDensity (fun z : ℝ × ℝ => ENNReal.ofReal (z.1 ^ (a - 1)))) ↔
      s < min (a / (2 * r)) ((a + d) / (2 * ((r : ℝ) + d))) := by
  change IntegrableOn _ _ (volume.withDensity
    (fun z : ℝ × ℝ => (Real.toNNReal (z.1 ^ (a - 1)) : ENNReal))) ↔ _
  rw [integrableOn_withDensity_iff_weighted (measurableSet_Ioo.prod measurableSet_Ioo)
    (by fun_prop)]
  have he : EqOn (fun z : ℝ × ℝ => (Real.toNNReal (z.1 ^ (a - 1)) : ℝ) *
      (z.1 ^ (2 * r) * (z.2 ^ 2 + z.1 ^ (2 * d))) ^ (-s))
      (weightedCancellation a r d s) (Ioo 0 ε ×ˢ Ioo (-δ) δ) := by
    intro z hz
    dsimp only
    rw [Real.coe_toNNReal _ (Real.rpow_nonneg hz.1.1.le _)]
    rfl
  rw [integrableOn_congr_fun he (measurableSet_Ioo.prod measurableSet_Ioo)]
  exact weightedCancellation_local_integrableOn_iff a ha r d hr hd ε δ hε hε1 hδ hδ1 s

/-- The network model phase transition holds on every small rectangular neighborhood. -/
theorem weightedNetworkModel_local_phase_transition (L r : ℕ) (hL : 0 < L) (hr : 0 < r)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (s : ℝ) :
    IntegrableOn (weightedCancellation L r r s) (Ioo 0 ε ×ˢ Ioo (-δ) δ) volume ↔
      s < (if L < r then (L : ℝ) / (2 * r)
        else if L = r then 1 / 2 else ((L : ℝ) + r) / (4 * r)) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  exact (weightedCancellation_local_integrableOn_iff L hL' r r hr hr
    ε δ hε hε1 hδ hδ1 s).trans
      ((weightedCancellation_symmetric_integrableOn_iff L hL' r r hr hr s).symm.trans
        (weightedNetworkModel_phase_transition L r hL hr s))

/-- Explicit endpoint and supercritical divergence for the local weighted model. -/
theorem weightedCancellation_local_not_integrable (a : ℝ) (ha : 0 < a) (r d : ℕ)
    (hr : 0 < r) (hd : 0 < d) (ε δ : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (s : ℝ)
    (hs : min (a / (2 * r)) ((a + d) / (2 * ((r : ℝ) + d))) ≤ s) :
    ¬ IntegrableOn (weightedCancellation a r d s) (Ioo 0 ε ×ˢ Ioo (-δ) δ) volume := by
  rw [weightedCancellation_local_integrableOn_iff a ha r d hr hd ε δ hε hε1 hδ hδ1 s]
  exact not_lt.mpr hs

end ResidualSLT
