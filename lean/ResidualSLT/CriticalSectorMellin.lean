module
public import ResidualSLT.WeightedCancellation
public import ResidualSLT.LossComparison
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! An exact critical two-sector Mellin calculation.
The normalized loss is u² max(u²,t²), with sectors 0<t<u<1 and 0<u<t<1.
This file proves real double-pole growth, not meromorphic continuation or a Laplace
asymptotic, and does not identify a network multiplicity. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Filter
open scoped Topology

@[expose] def criticalCoreSection (s u : ℝ) : ℝ :=
  ∫ _t : ℝ in Ioo 0 u, (u ^ 4) ^ (-s)

@[expose] def criticalOuterSection (s t : ℝ) : ℝ :=
  ∫ u : ℝ in Ioo 0 t, (u ^ 2 * t ^ 2) ^ (-s)

@[expose] def criticalSectorMellin (s : ℝ) : ℝ :=
  (∫ u : ℝ in Ioo 0 1, criticalCoreSection s u) +
    ∫ t : ℝ in Ioo 0 1, criticalOuterSection s t

/-- Positive-interval power integral, with its convergence hypothesis explicit. -/
theorem integral_Ioo_zero_rpow (b p : ℝ) (hb : 0 < b) (hp : -1 < p) :
    (∫ x : ℝ in Ioo 0 b, x ^ p) = b ^ (p + 1) / (p + 1) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hb.le,
    integral_rpow (Or.inl hp), Real.zero_rpow (by linarith : p + 1 ≠ 0), sub_zero]

theorem criticalCoreSection_eq (s u : ℝ) (hu : 0 < u) :
    criticalCoreSection s u = u ^ (1 - 4 * s) := by
  rw [criticalCoreSection, setIntegral_const, Measure.real, Real.volume_Ioo, sub_zero,
    ENNReal.toReal_ofReal hu.le, smul_eq_mul, ← Real.rpow_natCast_mul hu.le]
  norm_num only [Nat.cast_ofNat]
  rw [show (4 : ℝ) * -s = -4 * s by ring]
  nth_rw 1 [← Real.rpow_one u]
  rw [← Real.rpow_add hu]
  congr 1
  ring

theorem criticalOuterSection_eq (s t : ℝ) (ht : 0 < t) (hs : s < 1 / 2) :
    criticalOuterSection s t = t ^ (1 - 4 * s) / (1 - 2 * s) := by
  have he : EqOn (fun u : ℝ => (u ^ 2 * t ^ 2) ^ (-s))
      (fun u => u ^ (-2 * s) * t ^ (-2 * s)) (Ioo 0 t) := by
    intro u hu
    dsimp only
    rw [Real.mul_rpow (sq_nonneg _) (sq_nonneg _),
      ← Real.rpow_natCast_mul hu.1.le, ← Real.rpow_natCast_mul ht.le]
    norm_num
  rw [criticalOuterSection, setIntegral_congr_fun measurableSet_Ioo he, integral_mul_const,
    integral_Ioo_zero_rpow t (-2 * s) ht (by linarith)]
  rw [div_mul_eq_mul_div, ← Real.rpow_add ht]
  rw [show -2 * s + 1 + -2 * s = 1 - 4 * s by ring,
    show -2 * s + 1 = 1 - 2 * s by ring]

/-- Every inner integral and both outer section integrals are genuinely integrable
below one half; none of the exact formulas use a totalized divergent integral. -/
theorem criticalSectorMellin_integrable (s : ℝ) (hs : s < 1 / 2) :
    (∀ u : ℝ, 0 < u → IntegrableOn (fun _ : ℝ => (u ^ 4) ^ (-s)) (Ioo 0 u) volume) ∧
    (∀ t : ℝ, 0 < t → IntegrableOn (fun u : ℝ => (u ^ 2 * t ^ 2) ^ (-s)) (Ioo 0 t) volume) ∧
    IntegrableOn (criticalCoreSection s) (Ioo 0 1) volume ∧
    IntegrableOn (criticalOuterSection s) (Ioo 0 1) volume := by
  have hp : IntegrableOn (fun u : ℝ => u ^ (1 - 4 * s)) (Ioo 0 1) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u _; exact integrableOn_const (by simp [Real.volume_Ioo])
  · intro t ht
    have hi : IntegrableOn (fun u : ℝ => u ^ (-2 * s)) (Ioo 0 t) volume :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff ht).mpr (by linarith)
    apply IntegrableOn.congr_fun (hi.mul_const (t ^ (-2 * s))) _ measurableSet_Ioo
    intro u hu
    dsimp only
    rw [Real.mul_rpow (sq_nonneg _) (sq_nonneg _),
      ← Real.rpow_natCast_mul hu.1.le, ← Real.rpow_natCast_mul ht.le]
    norm_num
  · exact hp.congr_fun (fun u hu => (criticalCoreSection_eq s u hu.1).symm) measurableSet_Ioo
  · exact IntegrableOn.congr_fun (hp.div_const (1 - 2 * s))
      (fun t ht => (criticalOuterSection_eq s t ht.1 hs).symm) measurableSet_Ioo

/-- Exact two-sector Mellin integral. The outer sector supplies the double pole. -/
theorem criticalSectorMellin_eq (s : ℝ) (hs : s < 1 / 2) :
    criticalSectorMellin s = 1 / (2 - 4 * s) + 1 / ((1 - 2 * s) * (2 - 4 * s)) := by
  have hc : (∫ u : ℝ in Ioo 0 1, criticalCoreSection s u) = 1 / (2 - 4 * s) := by
    rw [setIntegral_congr_fun measurableSet_Ioo (fun u hu => criticalCoreSection_eq s u hu.1),
      integral_Ioo_zero_rpow 1 (1 - 4 * s) zero_lt_one (by linarith), Real.one_rpow]
    rw [show 1 - 4 * s + 1 = 2 - 4 * s by ring]
  have ho : (∫ t : ℝ in Ioo 0 1, criticalOuterSection s t) =
      1 / ((1 - 2 * s) * (2 - 4 * s)) := by
    rw [setIntegral_congr_fun measurableSet_Ioo (fun t ht => criticalOuterSection_eq s t ht.1 hs),
      integral_div, integral_Ioo_zero_rpow 1 (1 - 4 * s) zero_lt_one (by linarith), Real.one_rpow]
    rw [show 1 - 4 * s + 1 = 2 - 4 * s by ring, div_div]
    rw [mul_comm]
  rw [criticalSectorMellin, hc, ho]

/-- Real double-pole growth of the explicit model, with its exact leading coefficient. -/
theorem criticalSectorMellin_scaled_limit :
    Tendsto (fun s : ℝ => (1 / 2 - s) ^ 2 * criticalSectorMellin s)
      (𝓝[<] (1 / 2 : ℝ)) (𝓝 (1 / 8 : ℝ)) := by
  have he : (fun s : ℝ => (1 / 2 - s) ^ 2 * criticalSectorMellin s) =ᶠ[𝓝[<] (1 / 2 : ℝ)]
      (fun s => (1 - s) / 4) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s < 1 / 2 := hs
    rw [criticalSectorMellin_eq s hs']
    have h1 : 1 - 2 * s ≠ 0 := by linarith
    rw [show 2 - 4 * s = 2 * (1 - 2 * s) by ring]
    field_simp [h1]
    ; ring
  have ht : Tendsto (fun s : ℝ => (1 - s) / 4) (𝓝[<] (1 / 2 : ℝ)) (𝓝 (1 / 8 : ℝ)) := by
    convert ((((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).sub continuous_id).div_const (4 : ℝ)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds) using 1 <;> norm_num
  exact ht.congr' he.symm


/-- Continuous maximum-monomial model on the two sectors. -/
@[expose] def criticalSectorLoss (z : ℝ × ℝ) : ℝ :=
  max (z.1 ^ 4) (z.1 ^ 2 * z.2 ^ 2)

/-- The two-sector model is uniformly comparable to the normalized smooth model. -/
theorem criticalSectorLoss_comparison (z : ℝ × ℝ) :
    criticalSectorLoss z ≤ z.1 ^ 2 * (z.2 ^ 2 + z.1 ^ 2) ∧
    z.1 ^ 2 * (z.2 ^ 2 + z.1 ^ 2) ≤ 2 * criticalSectorLoss z := by
  have ha : 0 ≤ z.1 ^ 4 := by positivity
  have hb : 0 ≤ z.1 ^ 2 * z.2 ^ 2 := by positivity
  have he : z.1 ^ 2 * (z.2 ^ 2 + z.1 ^ 2) = z.1 ^ 4 + z.1 ^ 2 * z.2 ^ 2 := by ring
  rw [he, criticalSectorLoss]
  constructor
  · exact max_le (le_add_of_nonneg_right hb) (le_add_of_nonneg_left ha)
  · linarith [le_max_left (z.1 ^ 4) (z.1 ^ 2 * z.2 ^ 2),
      le_max_right (z.1 ^ 4) (z.1 ^ 2 * z.2 ^ 2)]

theorem criticalSectorLoss_integrable (s : ℝ) (hs : s < 1 / 2) :
    IntegrableOn (fun z => criticalSectorLoss z ^ (-s)) cancellationRectangle volume := by
  have hi := (weightedCancellation_integrableOn_iff 1 zero_lt_one 1 1
    (by omega) (by omega) s).mpr (by norm_num; exact hs)
  have hi' : IntegrableOn (fun z : ℝ × ℝ => (z.1 ^ 2 * (z.2 ^ 2 + z.1 ^ 2)) ^ (-s))
      cancellationRectangle volume := by
    change IntegrableOn (fun z : ℝ × ℝ => z.1 ^ (1 - 1 : ℝ) *
      (z.1 ^ (2 * 1) * (z.2 ^ 2 + z.1 ^ (2 * 1))) ^ (-s)) _ _ at hi
    simpa only [sub_self, Real.rpow_zero, one_mul, Nat.mul_one] using hi
  apply (integrableOn_rpow_iff_of_comparable_all (by fun_prop)
    (by unfold criticalSectorLoss; fun_prop) _ (by norm_num : (0 : ℝ) < 1 / 2)
    zero_lt_one _ _ s).mpr hi'
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
    have hu : 0 < z.1 := hz.1.1
    positivity
  · exact Filter.Eventually.of_forall (fun z => by linarith [(criticalSectorLoss_comparison z).2])
  · exact Filter.Eventually.of_forall (fun z => by simpa using (criticalSectorLoss_comparison z).1)

theorem criticalSectorLoss_core (u t : ℝ) (ht : 0 ≤ t) (htu : t ≤ u) :
    criticalSectorLoss (u, t) = u ^ 4 := by
  apply max_eq_left
  have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht htu 2) (sq_nonneg u)
  nlinarith

theorem criticalSectorLoss_outer (u t : ℝ) (hu : 0 ≤ u) (hut : u ≤ t) :
    criticalSectorLoss (u, t) = u ^ 2 * t ^ 2 := by
  apply max_eq_right
  have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu hut 2) (sq_nonneg u)
  nlinarith


/-- Fubini identifies the iterated sector calculation with the actual square integral.
The diagonal is included in the core; its one-dimensional sections are null endpoints. -/
theorem criticalSectorMellin_eq_square_integral (s : ℝ) (hs : s < 1 / 2) :
    criticalSectorMellin s =
      ∫ z : ℝ × ℝ in cancellationRectangle, criticalSectorLoss z ^ (-s) := by
  let g : ℝ × ℝ → ℝ := fun z => criticalSectorLoss z ^ (-s)
  let C : Set (ℝ × ℝ) := {z | z.2 ≤ z.1}
  have hC : MeasurableSet C := (isClosed_le continuous_snd continuous_fst).measurableSet
  have hi : IntegrableOn g (Ioo 0 1 ×ˢ Ioo 0 1) (volume.prod volume) := by
    have h := criticalSectorLoss_integrable s hs
    change IntegrableOn g (Ioo 0 1 ×ˢ Ioo 0 1) volume at h
    rwa [Measure.volume_eq_prod] at h
  have hA := hi.indicator hC
  have hB := hi.indicator hC.compl
  have hcore (u : ℝ) (hu : u ∈ Ioo 0 1) :
      (∫ t : ℝ in Ioo 0 1, C.indicator g (u, t)) = criticalCoreSection s u := by
    calc
      _ = ∫ t : ℝ in Ioo 0 1, (Iic u).indicator (fun _ => (u ^ 4) ^ (-s)) t := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro t ht
        by_cases htu : t ≤ u
        · simp [C, g, indicator_of_mem, htu, criticalSectorLoss_core u t ht.1.le htu]
        · simp [C, htu]
      _ = ∫ t : ℝ in Ioc 0 u, (u ^ 4) ^ (-s) := by
        rw [setIntegral_indicator measurableSet_Iic]
        have he : Ioo (0 : ℝ) 1 ∩ Iic u = Ioc 0 u := by
          ext t
          simp only [mem_inter_iff, mem_Ioo, mem_Iic, mem_Ioc]
          constructor
          · exact fun h => ⟨h.1.1, h.2⟩
          · intro h; exact ⟨⟨h.1, h.2.trans_lt hu.2⟩, h.2⟩
        rw [he]
      _ = criticalCoreSection s u := integral_Ioc_eq_integral_Ioo
  have houter (t : ℝ) (ht : t ∈ Ioo 0 1) :
      (∫ u : ℝ in Ioo 0 1, Cᶜ.indicator g (u, t)) = criticalOuterSection s t := by
    calc
      _ = ∫ u : ℝ in Ioo 0 1, (Iio t).indicator (fun u => (u ^ 2 * t ^ 2) ^ (-s)) u := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro u hu
        by_cases hut : u < t
        · simp [C, g, not_le.mpr hut, hut, criticalSectorLoss_outer u t hu.1.le hut.le]
        · simp [C, not_lt.mp hut, hut]
      _ = ∫ u : ℝ in Ioo 0 t, (u ^ 2 * t ^ 2) ^ (-s) := by
        rw [setIntegral_indicator measurableSet_Iio]
        have he : Ioo (0 : ℝ) 1 ∩ Iio t = Ioo 0 t := by
          ext u
          simp only [mem_inter_iff, mem_Ioo, mem_Iio]
          constructor
          · exact fun h => ⟨h.1.1, h.2⟩
          · intro h; exact ⟨⟨h.1, h.2.trans ht.2⟩, h.2⟩
        rw [he]
      _ = criticalOuterSection s t := rfl
  have hcInt : (∫ z in Ioo 0 1 ×ˢ Ioo 0 1, C.indicator g z ∂volume.prod volume) =
      ∫ u in Ioo 0 1, criticalCoreSection s u := by
    rw [setIntegral_prod _ hA]
    exact setIntegral_congr_fun measurableSet_Ioo hcore
  have hoInt : (∫ z in Ioo 0 1 ×ˢ Ioo 0 1, Cᶜ.indicator g z ∂volume.prod volume) =
      ∫ t in Ioo 0 1, criticalOuterSection s t := by
    rw [← setIntegral_prod_swap (Ioo (0 : ℝ) 1) (Ioo (0 : ℝ) 1)]
    have hswap : IntegrableOn (fun z : ℝ × ℝ => Cᶜ.indicator g z.swap)
        (Ioo 0 1 ×ˢ Ioo 0 1) (volume.prod volume) := hB.swap
    rw [setIntegral_prod _ hswap]
    exact setIntegral_congr_fun measurableSet_Ioo houter
  rw [criticalSectorMellin, ← hcInt, ← hoInt, ← integral_add hA hB]
  change _ = ∫ z in Ioo 0 1 ×ˢ Ioo 0 1, g z ∂volume
  rw [Measure.volume_eq_prod]
  apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
  intro z _
  by_cases hz : z ∈ C <;> simp [hz]


/-- The one-sided double-pole limit holds for the actual two-dimensional integral. -/
theorem criticalSectorMellin_square_scaled_limit :
    Tendsto (fun s : ℝ => (1 / 2 - s) ^ 2 *
      ∫ z : ℝ × ℝ in cancellationRectangle, criticalSectorLoss z ^ (-s))
      (𝓝[<] (1 / 2 : ℝ)) (𝓝 (1 / 8 : ℝ)) := by
  apply criticalSectorMellin_scaled_limit.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [criticalSectorMellin_eq_square_integral s hs]

end ResidualSLT
