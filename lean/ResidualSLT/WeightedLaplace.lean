module
public import ResidualSLT.LaplaceOrder
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Fixed product regions and the critical radial substitution. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Filter
open scoped Topology Pointwise

@[expose] def normalizedLaplaceBox (a b N : ℝ) : ℝ :=
  ∫ z : ℝ × ℝ in Ioo 0 a ×ˢ Ioo 0 b,
    Real.exp (-N * (z.1 ^ 2 * (z.2 ^ 2 + z.1 ^ 2)))

theorem normalizedLaplaceBox_integrable (a b N : ℝ) :
    IntegrableOn (fun z : ℝ × ℝ => Real.exp (-N * (z.1 ^ 2 * (z.2 ^ 2 + z.1 ^ 2))))
      (Ioo 0 a ×ˢ Ioo 0 b) volume := by
  exact ((by fun_prop : Continuous (fun z : ℝ × ℝ =>
    Real.exp (-N * (z.1 ^ 2 * (z.2 ^ 2 + z.1 ^ 2))))).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)

/-- Exact scaling of the actual square image and its two-dimensional volume. -/
theorem normalizedLaplaceBox_square (b N : ℝ) (hb : 0 < b) :
    normalizedLaplaceBox b b N = b ^ 2 * criticalLaplace (b ^ 4 * N) := by
  let : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by rw [Measure.volume_eq_prod]; infer_instance
  have hdom : b • cancellationRectangle = Ioo 0 b ×ˢ Ioo 0 b := by
    ext z
    rw [mem_smul_set_iff_inv_smul_mem₀ hb.ne']
    change (0 < b⁻¹ * z.1 ∧ b⁻¹ * z.1 < 1) ∧ (0 < b⁻¹ * z.2 ∧ b⁻¹ * z.2 < 1) ↔ _
    simp only [← div_eq_inv_mul, div_pos_iff_of_pos_right hb, div_lt_one hb, mem_prod, mem_Ioo]
  have he := Measure.setIntegral_comp_smul_of_pos (volume : Measure (ℝ × ℝ))
    (fun z : ℝ × ℝ => Real.exp (-N * (z.1 ^ 2 * (z.2 ^ 2 + z.1 ^ 2)))) cancellationRectangle hb
  rw [hdom] at he
  have hf : (fun z : ℝ × ℝ => Real.exp (-N * ((b • z).1 ^ 2 * ((b • z).2 ^ 2 + (b • z).1 ^ 2)))) =
      (fun z : ℝ × ℝ => Real.exp (-(b ^ 4 * N) * (z.1 ^ 2 * (z.2 ^ 2 + z.1 ^ 2)))) := by
    funext z
    congr 1
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [hf] at he
  norm_num only [Module.finrank_prod, Module.finrank_self, smul_eq_mul] at he
  change criticalLaplace (b ^ 4 * N) = (b ^ 2)⁻¹ * normalizedLaplaceBox b b N at he
  have hb2 : b ^ 2 ≠ 0 := pow_ne_zero _ hb.ne'
  rw [he]
  field_simp

theorem normalizedLaplaceBox_mono (a b c d N : ℝ) (hac : a ≤ c) (hbd : b ≤ d) :
    normalizedLaplaceBox a b N ≤ normalizedLaplaceBox c d N :=
  setIntegral_mono_set (normalizedLaplaceBox_integrable c d N)
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))
    (Filter.Eventually.of_forall (prod_mono (Ioo_subset_Ioo le_rfl hac) (Ioo_subset_Ioo le_rfl hbd)))

/-- Both bounds persist on every fixed positive rectangle. -/
theorem normalizedLaplaceBox_has_order (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasCriticalLaplaceOrder (normalizedLaplaceBox a b) := by
  have hl := (criticalLaplace_has_order.1.comp_mul ((min a b) ^ 4) (by positivity)).const_mul
    ((min a b) ^ 2) (by positivity)
  have hu := (criticalLaplace_has_order.2.comp_mul ((max a b) ^ 4) (by positivity)).const_mul
    ((max a b) ^ 2) (by positivity)
  constructor
  · apply hl.mono
    exact Filter.Eventually.of_forall (fun N => by
      rw [← normalizedLaplaceBox_square (min a b) N (lt_min ha hb)]
      exact normalizedLaplaceBox_mono _ _ _ _ _ (min_le_left _ _) (min_le_right _ _))
  · apply hu.mono
    exact Filter.Eventually.of_forall (fun N => by
      rw [← normalizedLaplaceBox_square (max a b) N (lt_of_lt_of_le ha (le_max_left _ _))]
      exact normalizedLaplaceBox_mono _ _ _ _ _ (le_max_left _ _) (le_max_right _ _))

/-- Exact critical radial substitution on a finite interval, including its Jacobian. -/
theorem integral_radial_power_substitution (r : ℕ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε)
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ ρ : ℝ in Ioo 0 ε, ρ ^ (r - 1) * g (ρ ^ r)) =
      (r : ℝ)⁻¹ * ∫ u : ℝ in Ioo 0 (ε ^ r), g u := by
  have h := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := ε)
    (f := fun x : ℝ => x ^ r) (f' := fun x => (r : ℝ) * x ^ (r - 1))
    (fun x _ => hasDerivAt_pow r x) (by fun_prop) hg
  rw [zero_pow hr.ne', intervalIntegral.integral_of_le hε.le,
    intervalIntegral.integral_of_le (pow_pos hε r).le, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at h
  have he : (fun x : ℝ => (g ∘ (fun x => x ^ r)) x * ((r : ℝ) * x ^ (r - 1))) =
      (fun x => (r : ℝ) * (x ^ (r - 1) * g (x ^ r))) := by funext x; dsimp; ring
  rw [he, integral_const_mul] at h
  have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  rw [← h]
  field_simp

@[expose] def weightedLaplaceBox (r : ℕ) (ε δ N : ℝ) : ℝ :=
  ∫ z : ℝ × ℝ in Ioo 0 ε ×ˢ Ioo 0 δ,
    z.1 ^ (r - 1) * Real.exp (-N * (z.1 ^ (2 * r) * (z.2 ^ 2 + z.1 ^ (2 * r))))

/-- The weighted critical model is exactly a normalized rectangle, with factor 1/r. -/
theorem weightedLaplaceBox_eq (r : ℕ) (hr : 0 < r) (ε δ N : ℝ) (hε : 0 < ε) :
    weightedLaplaceBox r ε δ N = (r : ℝ)⁻¹ * normalizedLaplaceBox (ε ^ r) δ N := by
  let g : ℝ × ℝ → ℝ := fun z =>
    z.1 ^ (r - 1) * Real.exp (-N * (z.1 ^ (2 * r) * (z.2 ^ 2 + z.1 ^ (2 * r))))
  have hg : IntegrableOn g (Ioo 0 ε ×ˢ Ioo 0 δ) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact ((by fun_prop : Continuous g).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hn := normalizedLaplaceBox_integrable (ε ^ r) δ N
  rw [Measure.volume_eq_prod] at hn
  change (∫ z in Ioo 0 ε ×ˢ Ioo 0 δ, g z) = _
  rw [normalizedLaplaceBox, Measure.volume_eq_prod]
  rw [← setIntegral_prod_swap (Ioo (0 : ℝ) ε) (Ioo (0 : ℝ) δ),
    ← setIntegral_prod_swap (Ioo (0 : ℝ) (ε ^ r)) (Ioo (0 : ℝ) δ)]
  have hs : IntegrableOn (fun z : ℝ × ℝ => g z.swap) (Ioo 0 δ ×ˢ Ioo 0 ε) (volume.prod volume) := hg.swap
  have hns : IntegrableOn (fun z : ℝ × ℝ => Real.exp (-N * (z.swap.1 ^ 2 * (z.swap.2 ^ 2 + z.swap.1 ^ 2))))
      (Ioo 0 δ ×ˢ Ioo 0 (ε ^ r)) (volume.prod volume) := hn.swap
  rw [setIntegral_prod _ hs, setIntegral_prod _ hns, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t _
  have h := integral_radial_power_substitution r hr ε hε
    (fun u => Real.exp (-N * (u ^ 2 * (t ^ 2 + u ^ 2)))) (by fun_prop)
  simpa only [g, Prod.swap_prod_mk, ← pow_mul, Nat.mul_comm r 2] using! h

theorem weightedLaplaceBox_has_order (r : ℕ) (hr : 0 < r) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) : HasCriticalLaplaceOrder (weightedLaplaceBox r ε δ) := by
  have h := normalizedLaplaceBox_has_order (ε ^ r) δ (pow_pos hε r) hδ
  have hr0 : 0 < (r : ℝ)⁻¹ := by positivity
  constructor
  · exact (h.1.const_mul _ hr0).mono (Filter.Eventually.of_forall (fun N =>
      (weightedLaplaceBox_eq r hr ε δ N hε).ge))
  · exact (h.2.const_mul _ hr0).mono (Filter.Eventually.of_forall (fun N =>
      (weightedLaplaceBox_eq r hr ε δ N hε).le))


/-- Reflection for continuous even functions on a full transverse interval. -/
theorem integral_even_Ioo (g : ℝ → ℝ) (hg : Continuous g) (he : ∀ t, g (-t) = g t)
    (δ : ℝ) (hδ : 0 < δ) : (∫ t in Ioo (-δ) δ, g t) = 2 * ∫ t in Ioo 0 δ, g t := by
  have hi : IntegrableOn g (Ioo (-δ) δ) volume :=
    (hg.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  rw [integral_Ioo_split (neg_nonpos.mpr hδ.le) hδ.le hi]
  have hn := intervalIntegral.integral_comp_neg (f := g) (a := 0) (b := δ)
  have hf : (fun x => g (-x)) = g := funext he
  rw [hf, neg_zero, intervalIntegral.integral_of_le hδ.le,
    intervalIntegral.integral_of_le (neg_nonpos.mpr hδ.le),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at hn
  rw [← hn]
  ring

@[expose] def weightedLaplaceSymmetric (r : ℕ) (ε δ N : ℝ) : ℝ :=
  ∫ z : ℝ × ℝ in Ioo 0 ε ×ˢ Ioo (-δ) δ,
    z.1 ^ (r - 1) * Real.exp (-N * (z.1 ^ (2 * r) * (z.2 ^ 2 + z.1 ^ (2 * r))))

theorem weightedLaplaceSymmetric_eq (r : ℕ) (ε δ N : ℝ) (hδ : 0 < δ) :
    weightedLaplaceSymmetric r ε δ N = 2 * weightedLaplaceBox r ε δ N := by
  let g : ℝ × ℝ → ℝ := fun z =>
    z.1 ^ (r - 1) * Real.exp (-N * (z.1 ^ (2 * r) * (z.2 ^ 2 + z.1 ^ (2 * r))))
  have hi (a b : ℝ) : IntegrableOn g (Ioo 0 ε ×ˢ Ioo a b) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact ((by fun_prop : Continuous g).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  change (∫ z in Ioo 0 ε ×ˢ Ioo (-δ) δ, g z) = 2 * ∫ z in Ioo 0 ε ×ˢ Ioo 0 δ, g z
  rw [Measure.volume_eq_prod, setIntegral_prod _ (hi (-δ) δ), setIntegral_prod _ (hi 0 δ), ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u _
  exact integral_even_Ioo (fun t => g (u,t)) (by fun_prop) (fun t => by simp [g]) δ hδ

theorem weightedLaplaceSymmetric_has_order (r : ℕ) (hr : 0 < r) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) : HasCriticalLaplaceOrder (weightedLaplaceSymmetric r ε δ) := by
  have h := weightedLaplaceBox_has_order r hr ε δ hε hδ
  constructor
  · exact (h.1.const_mul 2 (by norm_num)).mono (Filter.Eventually.of_forall (fun N =>
      (weightedLaplaceSymmetric_eq r ε δ N hδ).ge))
  · exact (h.2.const_mul 2 (by norm_num)).mono (Filter.Eventually.of_forall (fun N =>
      (weightedLaplaceSymmetric_eq r ε δ N hδ).le))

end ResidualSLT
