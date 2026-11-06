module
public import ResidualSLT.AngularIntegration

/-! Quantitative integral bounds for the existing certified coordinate maps. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Metric

/-- Bounded Jacobians give numerical integral bounds, beyond integrability transfer. -/
theorem integral_image_bounds_of_bounded_jacobian
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} (hf : ContDiff ℝ 1 f) {D : Set E} (hD : MeasurableSet D)
    (hinj : Set.InjOn f D) {c C : ℝ} (hc : 0 < c)
    (hb : ∀ x ∈ D, c ≤ |(fderiv ℝ f x).det| ∧ |(fderiv ℝ f x).det| ≤ C)
    (g : E → ℝ) (hi : IntegrableOn (fun x => g (f x)) D μ)
    (hpos : ∀ x ∈ D, 0 ≤ g (f x)) :
    c * (∫ x in D, g (f x) ∂μ) ≤ ∫ y in f '' D, g y ∂μ ∧
    (∫ y in f '' D, g y ∂μ) ≤ C * ∫ x in D, g (f x) ∂μ := by
  have hder : ∀ x ∈ D, HasFDerivWithinAt f (fderiv ℝ f x) D x := fun x (_ : x ∈ D) => (hf.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt
  have himg := (integrableOn_image_iff_of_bounded_jacobian μ hf hD hinj hc hb g).mpr hi
  have hj := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hD hder hinj g).mp himg
  rw [integral_image_eq_integral_abs_det_fderiv_smul μ hD hder hinj]
  constructor
  · rw [← integral_const_mul]
    exact setIntegral_mono_on (hi.const_mul c) hj hD
      (fun x hx => mul_le_mul_of_nonneg_right (hb x hx).1 (hpos x hx))
  · rw [← integral_const_mul]
    exact setIntegral_mono_on hj (hi.const_mul C) hD
      (fun x hx => mul_le_mul_of_nonneg_right (hb x hx).2 (hpos x hx))

/-- Angular transfer with its actual image and explicit chart determinant constants. -/
theorem TransverseChart.radial_integral_bounds {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (c : TransverseChart f) (hf : ContDiff ℝ 1 f) {R : Set ℝ} (hR : MeasurableSet R)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D) (hsub : D ⊆ c.chart.source)
    (g : ℝ × (Fin n → ℝ) → ℝ)
    (hi : IntegrableOn (fun z => g (z.1,c.chart z.2)) (R ×ˢ D) volume)
    (hp : ∀ z ∈ R ×ˢ D, 0 ≤ g (z.1,c.chart z.2)) :
    c.lower * (∫ z in R ×ˢ D, g (z.1,c.chart z.2)) ≤ ∫ z in R ×ˢ (c.chart '' D), g z ∧
    (∫ z in R ×ˢ (c.chart '' D), g z) ≤ c.upper * ∫ z in R ×ˢ D, g (z.1,c.chart z.2) := by
  let F := transverseMap c.index f
  let Ψ : ℝ × (Fin n → ℝ) → ℝ × (Fin n → ℝ) := Prod.map id F
  have hF : ContDiff ℝ 1 F := transverseMap_contDiff c.index hf
  have hΨ : ContDiff ℝ 1 Ψ := contDiff_id.prodMap hF
  have hderiv (z : ℝ × (Fin n → ℝ)) : HasFDerivAt Ψ
      ((ContinuousLinearMap.id ℝ ℝ).prodMap (fderiv ℝ F z.2)) z :=
    HasFDerivAt.prodMap z (hasFDerivAt_id z.1) (hF.differentiable (by norm_num) z.2).hasFDerivAt
  have hdet (z : ℝ × (Fin n → ℝ)) : (fderiv ℝ Ψ z).det = (fderiv ℝ F z.2).det := by
    rw [(hderiv z).fderiv]
    change LinearMap.det ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap (fderiv ℝ F z.2).toLinearMap) = _
    rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul]
  have hinj : InjOn Ψ (R ×ˢ D) := by
    intro x hx y hy hxy
    apply Prod.ext
    · have h := congrArg Prod.fst hxy
      exact h
    · apply c.chart.injOn (hsub hx.2) (hsub hy.2)
      rw [c.coe_eq]
      exact congrArg Prod.snd hxy
  let : (volume : Measure (ℝ × (Fin n → ℝ))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have heq : (fun z => g (Ψ z)) = (fun z => g (z.1,c.chart z.2)) := by
    funext z; rw [c.coe_eq]; rfl
  have himage : Ψ '' (R ×ˢ D) = R ×ˢ (c.chart '' D) := by
    simp only [Ψ, prodMap_image_prod, image_id, c.coe_eq, F]
  have h := integral_image_bounds_of_bounded_jacobian volume hΨ (hR.prod hD) hinj c.lower_pos
    (fun z hz => by rw [hdet]; exact c.jacobian_bounds z.2 (hsub hz.2)) g
    (by rwa [heq]) (by
      intro z hz
      change 0 ≤ (fun z => g (Ψ z)) z
      rw [heq]
      exact hp z hz)
  simpa only [himage, heq] using h

/-- Exact integration of the unused angular coordinates. -/
theorem angularCylinder_integral {n : ℕ} (j : Fin (n + 1))
    (R T : Set ℝ) (B : Set (Fin n → ℝ)) (g : ℝ × ℝ → ℝ) :
    (∫ z : ℝ × (Fin (n + 1) → ℝ) in R ×ˢ angularCylinder j T B, g (z.1,z.2 j)) =
      (volume B).toReal * ∫ z in R ×ˢ T, g z := by
  let M := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
  let e := ((MeasurableEquiv.refl ℝ).prodCongr M).trans
    (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × (Fin n → ℝ) ≃ᵐ ℝ × (ℝ × (Fin n → ℝ))).symm
  have he : MeasurePreserving e volume volume :=
    (MeasurePreserving.symm _ volume_preserving_prodAssoc).comp
      ((MeasurePreserving.id volume).prod (volume_preserving_piFinSuccAbove _ j))
  have hpre : e ⁻¹' ((R ×ˢ T) ×ˢ B) = R ×ˢ angularCylinder j T B := by
    ext z
    change (z.1 ∈ R ∧ z.2 j ∈ T) ∧ (fun i => z.2 (j.succAbove i)) ∈ B ↔
      z.1 ∈ R ∧ z.2 j ∈ T ∧ (fun i => z.2 (j.succAbove i)) ∈ B
    tauto
  have hi := he.setIntegral_preimage_emb e.measurableEmbedding (fun z : (ℝ × ℝ) × (Fin n → ℝ) => g z.1)
    ((R ×ˢ T) ×ˢ B)
  rw [hpre] at hi
  change (∫ z : ℝ × (Fin (n + 1) → ℝ) in R ×ˢ angularCylinder j T B, g (z.1,z.2 j)) = _ at hi
  rw [hi, Measure.volume_eq_prod]
  calc
    _ = ∫ z : (ℝ × ℝ) × (Fin n → ℝ) in (R ×ˢ T) ×ˢ B, g z.1 * (1 : ℝ) ∂volume.prod volume := by simp
    _ = _ := by
      have h := setIntegral_prod_mul (μ := volume) (ν := volume) g (fun _ : Fin n → ℝ => (1 : ℝ)) (R ×ˢ T) B
      simpa [Measure.real, mul_comm] using h

/-- Exact radial change of variables for arbitrary real integrands. -/
theorem radialBlowup_integral_image {n : ℕ} (j : Fin n) {D : Set (Fin n → ℝ)}
    (hD : MeasurableSet D) (hpos : ∀ z ∈ D, 0 < z j) (g : (Fin n → ℝ) → ℝ) :
    (∫ w in radialBlowup j '' D, g w) = ∫ z in D, z j ^ (n - 1) * g (radialBlowup j z) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hD
    (fun z _ => (radialBlowup_hasFDerivAt j z).hasFDerivWithinAt)
    ((radialBlowup_injOn j).mono (fun z hz => (hpos z hz).ne'))]
  apply setIntegral_congr_fun hD
  intro z hz
  dsimp only
  rw [radialBlowupDeriv_det, abs_of_nonneg (pow_nonneg (hpos z hz).le _), smul_eq_mul]


/-- An overlapping finite cover gives an upper bound, without any disjointness assumption. -/
theorem setIntegral_le_add_sum_of_cover {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (g : α → ℝ) (A B : Set α) (D : ι → Set α)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hD : ∀ i ∈ s, MeasurableSet (D i))
    (hiA : IntegrableOn g A μ) (hiB : IntegrableOn g B μ) (hiD : ∀ i ∈ s, IntegrableOn g (D i) μ)
    (hcover : A ⊆ B ∪ ⋃ i ∈ s, D i)
    (hp : ∀ x ∈ B ∪ ⋃ i ∈ s, D i, 0 ≤ g x) :
    (∫ x in A, g x ∂μ) ≤ (∫ x in B, g x ∂μ) + ∑ i ∈ s, ∫ x in D i, g x ∂μ := by
  classical
  have hiB' := hiB.integrable_indicator hB
  have hiD' (i) (hi : i ∈ s) := (hiD i hi).integrable_indicator (hD i hi)
  have hsum : Integrable (fun x => ∑ i ∈ s, (D i).indicator g x) μ :=
    integrable_finsetSum _ (fun i hi => hiD' i hi)
  have hpt (x : α) : A.indicator g x ≤ B.indicator g x + ∑ i ∈ s, (D i).indicator g x := by
    have hBpos : 0 ≤ B.indicator g x := by
      by_cases hx : x ∈ B
      · simpa [hx] using hp x (Or.inl hx)
      · simp [hx]
    have hDpos (i) (hi : i ∈ s) : 0 ≤ (D i).indicator g x := by
      by_cases hx : x ∈ D i
      · simpa [hx] using hp x (Or.inr (mem_iUnion₂.mpr ⟨i,hi,hx⟩))
      · simp [hx]
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx]
      rcases hcover hx with hb | hd
      · rw [indicator_of_mem hb]
        exact le_add_of_nonneg_right (Finset.sum_nonneg hDpos)
      · obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hd
        have h := Finset.single_le_sum hDpos hi
        rw [indicator_of_mem hxi] at h
        exact h.trans (le_add_of_nonneg_left hBpos)
    · rw [indicator_of_notMem hx]
      exact add_nonneg hBpos (Finset.sum_nonneg hDpos)
  have h := integral_mono (hiA.integrable_indicator hA) (hiB'.add hsum) hpt
  simp only [Pi.add_apply] at h
  rw [integral_indicator hA, integral_add hiB' hsum, integral_indicator hB,
    integral_finsetSum s (fun i hi => hiD' i hi)] at h
  have he : (∑ i ∈ s, ∫ x, (D i).indicator g x ∂μ) = ∑ i ∈ s, ∫ x in D i, g x ∂μ :=
    Finset.sum_congr rfl (fun i hi => integral_indicator (hD i hi))
  rwa [he] at h

end ResidualSLT
