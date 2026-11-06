module
public import ResidualSLT.PriorMeasure
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Constructions.Pi

/-! Local transverse coordinates with actual Jacobians and Lebesgue integrability transfer.
No global chart or radial measure formula is assumed. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Finset
open scoped Topology

/-- Replace coordinate j by a scalar function, keeping all other coordinates. -/
@[expose] def transverseMap {n : ℕ} (j : Fin n) (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ := fun i => if i = j then f x else x i

@[expose] def transverseDeriv {n : ℕ} (j : Fin n) (A : (Fin n → ℝ) →L[ℝ] ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i => if i = j then A else ContinuousLinearMap.proj i)

theorem transverseMap_hasFDerivAt {n : ℕ} (j : Fin n) {f : (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ} {A : (Fin n → ℝ) →L[ℝ] ℝ} (hf : HasFDerivAt f A x) :
    HasFDerivAt (transverseMap j f) (transverseDeriv j A) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i = j
  · simpa [transverseMap, transverseDeriv, hi] using hf
  · simpa [transverseMap, transverseDeriv, hi] using hasFDerivAt_apply i x

theorem transverseMap_contDiff {n : ℕ} (j : Fin n) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 (transverseMap j f) := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i = j
  · simpa [transverseMap, hi] using hf
  · simpa [transverseMap, hi] using contDiff_apply ℝ (fun _ : Fin n => ℝ) i

/-- The coordinate replacement Jacobian is exactly the chosen partial derivative. -/
theorem transverseDeriv_det {n : ℕ} (j : Fin n) (A : (Fin n → ℝ) →L[ℝ] ℝ) :
    (transverseDeriv j A).det = A (Pi.single j 1) := by
  change LinearMap.det (transverseDeriv j A).toLinearMap = _
  rw [← LinearMap.det_toMatrix']
  have hm : LinearMap.toMatrix' (transverseDeriv j A).toLinearMap =
      (1 : Matrix (Fin n) (Fin n) ℝ).updateRow j (fun k => A (Pi.single k 1)) := by
    ext i k
    simp only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe,
      transverseDeriv, ContinuousLinearMap.pi_apply, Matrix.updateRow_apply]
    split_ifs with h
    · rfl
    · simp [ContinuousLinearMap.proj_apply, Matrix.one_apply, Pi.single_apply]
  rw [hm]
  have hrow : (fun k => A (Pi.single k 1)) =
      ∑ k : Fin n, A (Pi.single k 1) • (1 : Matrix (Fin n) (Fin n) ℝ) k := by
    ext i
    simp [Matrix.one_apply]
  rw [hrow, Matrix.det_updateRow_sum, Matrix.det_one, smul_eq_mul, mul_one]

/-- Nonzero transverse partial derivative gives an invertible linear derivative. -/
theorem transverseDeriv_bijective {n : ℕ} (j : Fin n) (A : (Fin n → ℝ) →L[ℝ] ℝ)
    (hA : A (Pi.single j 1) ≠ 0) : Function.Bijective (transverseDeriv j A) := by
  have hd : IsUnit (LinearMap.det (transverseDeriv j A).toLinearMap) := by
    change IsUnit (transverseDeriv j A).det
    rw [transverseDeriv_det]
    exact isUnit_iff_ne_zero.mpr hA
  have he := (LinearMap.equivOfIsUnitDet hd).bijective
  simpa only [Function.Bijective, Function.Injective, Function.Surjective,
    LinearMap.equivOfIsUnitDet_apply, ContinuousLinearMap.coe_coe] using he

/-- A genuine Jacobian formula plus positive finite bounds removes the density factor.
The integrand need not be assumed measurable or integrable in advance. -/
theorem integrableOn_image_iff_of_bounded_jacobian
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} (hf : ContDiff ℝ 1 f) {D : Set E} (hD : MeasurableSet D)
    (hinj : Set.InjOn f D) {c C : ℝ} (hc : 0 < c)
    (hb : ∀ x ∈ D, c ≤ |(fderiv ℝ f x).det| ∧ |(fderiv ℝ f x).det| ≤ C)
    (g : E → ℝ) :
    IntegrableOn g (f '' D) μ ↔ IntegrableOn (fun x => g (f x)) D μ := by
  have hJ : Continuous (fun x => |(fderiv ℝ f x).det|) :=
    (ContinuousLinearMap.continuous_det.comp (hf.continuous_fderiv (by norm_num))).abs
  let ρ : E → NNReal := fun x => Real.toNNReal |(fderiv ℝ f x).det|
  have hρ : BoundedPositivePriorOn ρ D μ := by
    refine ⟨(continuous_real_toNNReal.comp hJ).measurable, Real.toNNReal c,
      Real.toNNReal C, Real.toNNReal_pos.mpr hc, ?_⟩
    filter_upwards [ae_restrict_mem hD] with x hx
    exact ⟨Real.toNNReal_le_toNNReal (hb x hx).1,
      Real.toNNReal_le_toNNReal (hb x hx).2⟩
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hD
    (fun x _ => (hf.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt) hinj]
  have he : (fun x => |(fderiv ℝ f x).det| • g (f x)) =
      (fun x => (ρ x : ℝ) * g (f x)) := by
    funext x
    simp [ρ]
  rw [he, ← integrableOn_withDensity_iff_weighted hD hρ.measurable,
    integrableOn_withDensity_iff_of_boundedPositive hD hρ]

/-- Actual local transverse coordinates with bounded Jacobian, smooth inverse, and
both directions of Lebesgue integrability transfer. Bounds and inverse are derived. -/
theorem exists_transverse_chart {n : ℕ} (j : Fin n) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) (a : Fin n → ℝ)
    (ha : fderiv ℝ f a (Pi.single j 1) ≠ 0) :
    ∃ e : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ),
      a ∈ e.source ∧ (⇑e = transverseMap j f) ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        (∀ x ∈ e.source, c ≤ |(fderiv ℝ (transverseMap j f) x).det| ∧
          |(fderiv ℝ (transverseMap j f) x).det| ≤ C) ∧
        (∀ g : (Fin n → ℝ) → ℝ,
          IntegrableOn g e.target volume ↔
            IntegrableOn (fun x => g (transverseMap j f x)) e.source volume) := by
  let F := transverseMap j f
  have hF : ContDiff ℝ 1 F := transverseMap_contDiff j hf
  have hD (x : Fin n → ℝ) : HasFDerivAt F (transverseDeriv j (fderiv ℝ f x)) x :=
    transverseMap_hasFDerivAt j (hf.differentiable (by norm_num) x).hasFDerivAt
  have hdet (x : Fin n → ℝ) : (fderiv ℝ F x).det = fderiv ℝ f x (Pi.single j 1) := by
    rw [(hD x).fderiv, transverseDeriv_det]
  let A := (LinearEquiv.ofBijective (transverseDeriv j (fderiv ℝ f a)).toLinearMap
    (transverseDeriv_bijective j _ ha)).toContinuousLinearEquiv
  have hA : HasFDerivAt F (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) a := hD a
  let e₀ := hF.contDiffAt.toOpenPartialHomeomorph F hA (by norm_num)
  have ha₀ : a ∈ e₀.source := hF.contDiffAt.mem_toOpenPartialHomeomorph_source hA (by norm_num)
  let J : (Fin n → ℝ) → ℝ := fun x => |(fderiv ℝ F x).det|
  have hJ : Continuous J :=
    (ContinuousLinearMap.continuous_det.comp (hF.continuous_fderiv (by norm_num))).abs
  have hJa : 0 < J a := by simpa only [J, hdet] using abs_pos.mpr ha
  let U : Set (Fin n → ℝ) := {x | J a / 2 < J x ∧ J x < 2 * J a}
  have hU : IsOpen U := (isOpen_lt continuous_const hJ).inter (isOpen_lt hJ continuous_const)
  let e := e₀.restr U
  have hes : e.source = e₀.source ∩ U := e₀.restr_source' U hU
  have heF : (⇑e : (Fin n → ℝ) → (Fin n → ℝ)) = F := rfl
  have hb : ∀ x ∈ e.source, J a / 2 ≤ J x ∧ J x ≤ 2 * J a := by
    intro x hx
    rw [hes] at hx
    exact ⟨hx.2.1.le, hx.2.2.le⟩
  refine ⟨e, ?_, heF, ?_, J a / 2, 2 * J a, by positivity, by positivity, hb, ?_⟩
  · rw [hes]
    exact ⟨ha₀, by change J a / 2 < J a ∧ J a < 2 * J a; constructor <;> linarith⟩
  · intro y hy
    have hx := e.map_target hy
    have hnonzero : fderiv ℝ f (e.symm y) (Pi.single j 1) ≠ 0 := by
      have hj : 0 < J (e.symm y) := lt_of_lt_of_le (by positivity) (hb _ hx).1
      simpa only [J, hdet, abs_pos] using hj
    let B := (LinearEquiv.ofBijective (transverseDeriv j (fderiv ℝ f (e.symm y))).toLinearMap
      (transverseDeriv_bijective j _ hnonzero)).toContinuousLinearEquiv
    have hB : HasFDerivAt e (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (e.symm y) := by
      rw [heF]
      exact hD _
    exact (e.contDiffAt_symm hy hB (by rw [heF]; exact hF.contDiffAt)).contDiffWithinAt
  · intro g
    have hi := integrableOn_image_iff_of_bounded_jacobian volume hF e.open_source.measurableSet
      (show InjOn F e.source by rw [← heF]; exact e.injOn) (by positivity : 0 < J a / 2) hb g
    have heImage : F '' e.source = e.target := by rw [← heF]; exact e.image_source_eq_target
    rwa [heImage] at hi

/-- A chart certificate records geometry and Jacobian bounds, not any integrability conclusion. -/
structure TransverseChart {n : ℕ} (f : (Fin n → ℝ) → ℝ) where
  index : Fin n
  chart : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)
  coe_eq : ⇑chart = transverseMap index f
  inverse_contDiff : ContDiffOn ℝ 1 chart.symm chart.target
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  jacobian_bounds : ∀ x ∈ chart.source,
    lower ≤ |(fderiv ℝ (transverseMap index f) x).det| ∧
      |(fderiv ℝ (transverseMap index f) x).det| ≤ upper

/-- Every point with a nonzero partial derivative lies in a certified chart. -/
theorem exists_mem_transverseChart {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) (a : Fin n → ℝ) (j : Fin n)
    (ha : fderiv ℝ f a (Pi.single j 1) ≠ 0) :
    ∃ c : TransverseChart f, a ∈ c.chart.source := by
  obtain ⟨e, he, heq, hinv, c, C, hc, hC, hb, _⟩ := exists_transverse_chart j hf a ha
  exact ⟨⟨j, e, heq, hinv, c, C, hc, hC, hb⟩, he⟩

/-- The chosen output coordinate is exactly f, also along the genuine inverse. -/
theorem TransverseChart.inverse_coordinate {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (c : TransverseChart f) (y : Fin n → ℝ) (hy : y ∈ c.chart.target) :
    f (c.chart.symm y) = y c.index := by
  have h := congrFun (c.chart.right_inv hy) c.index
  rw [c.coe_eq] at h
  simpa [transverseMap] using h

/-- The chart also preserves every other coordinate along its inverse. -/
theorem TransverseChart.inverse_other {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (c : TransverseChart f) (y : Fin n → ℝ) (hy : y ∈ c.chart.target)
    (i : Fin n) (hi : i ≠ c.index) : c.chart.symm y i = y i := by
  have h := congrFun (c.chart.right_inv hy) i
  rw [c.coe_eq] at h
  simpa [transverseMap, hi] using h

/-- Transfer on any measurable subdomain, not only the full chart source. -/
theorem TransverseChart.integrableOn_image_iff {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (c : TransverseChart f) (hf : ContDiff ℝ 1 f) {D : Set (Fin n → ℝ)}
    (hD : MeasurableSet D) (hsub : D ⊆ c.chart.source) (g : (Fin n → ℝ) → ℝ) :
    IntegrableOn g (c.chart '' D) volume ↔
      IntegrableOn (fun x => g (c.chart x)) D volume := by
  rw [c.coe_eq]
  exact integrableOn_image_iff_of_bounded_jacobian volume (transverseMap_contDiff c.index hf)
    hD (by rw [← c.coe_eq]; exact c.chart.injOn.mono hsub) c.lower_pos
    (fun x hx => c.jacobian_bounds x (hsub hx)) g

/-- Compact regular loci admit a finite collection of actual bounded-Jacobian charts. -/
theorem finite_transverse_chart_cover {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hreg : ∀ x ∈ K, ∃ j : Fin n, fderiv ℝ f x (Pi.single j 1) ≠ 0) :
    ∃ charts : Finset (TransverseChart f), K ⊆ ⋃ c ∈ charts, c.chart.source := by
  classical
  apply hK.elim_finite_subcover (fun c : TransverseChart f => c.chart.source)
    (fun c => c.chart.open_source)
  intro x hx
  obtain ⟨j, hj⟩ := hreg x hx
  obtain ⟨c, hc⟩ := exists_mem_transverseChart hf x j hj
  exact mem_iUnion.mpr ⟨c, hc⟩

/-- Outside an open neighborhood of all zeros in a compact set, |f| is uniformly positive. -/
theorem compact_complement_abs_lower {E : Type*} [TopologicalSpace E] [T2Space E]
    {f : E → ℝ} (hf : Continuous f) {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hcover : ∀ x ∈ K, f x = 0 → x ∈ U) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K \ U, c ≤ |f x| := by
  by_cases hn : (K \ U).Nonempty
  · obtain ⟨a, ha, hmin⟩ := (hK.diff hU).exists_isMinOn hn hf.abs.continuousOn
    refine ⟨|f a|, abs_pos.mpr ?_, hmin⟩
    intro hz
    exact ha.2 (hcover a ha.1 hz)
  · exact ⟨1, zero_lt_one, fun x hx => False.elim (hn ⟨x, hx⟩)⟩

/-- Angular charts preserve integrability with an additional radial variable. The
integrand may include any radial weight; the product Jacobian is computed explicitly. -/
theorem TransverseChart.radial_integrableOn_image_iff {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (c : TransverseChart f) (hf : ContDiff ℝ 1 f) {R : Set ℝ} (hR : MeasurableSet R)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D) (hsub : D ⊆ c.chart.source)
    (g : ℝ × (Fin n → ℝ) → ℝ) :
    IntegrableOn g (R ×ˢ (c.chart '' D)) volume ↔
      IntegrableOn (fun z => g (z.1, c.chart z.2)) (R ×ˢ D) volume := by
  let F := transverseMap c.index f
  let Ψ : ℝ × (Fin n → ℝ) → ℝ × (Fin n → ℝ) := Prod.map id F
  have hF : ContDiff ℝ 1 F := transverseMap_contDiff c.index hf
  have hΨ : ContDiff ℝ 1 Ψ := contDiff_id.prodMap hF
  have hderiv (z : ℝ × (Fin n → ℝ)) : HasFDerivAt Ψ
      ((ContinuousLinearMap.id ℝ ℝ).prodMap (fderiv ℝ F z.2)) z :=
    HasFDerivAt.prodMap z (hasFDerivAt_id z.1) (hF.differentiable (by norm_num) z.2).hasFDerivAt
  have hdet (z : ℝ × (Fin n → ℝ)) : (fderiv ℝ Ψ z).det = (fderiv ℝ F z.2).det := by
    rw [(hderiv z).fderiv]
    change LinearMap.det ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap
      (fderiv ℝ F z.2).toLinearMap) = _
    rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul]
  have hinj : InjOn Ψ (R ×ˢ D) := by
    intro x hx y hy hxy
    apply Prod.ext
    · have ht := congrArg Prod.fst hxy
      exact ht
    · apply c.chart.injOn (hsub hx.2) (hsub hy.2)
      rw [c.coe_eq]
      exact congrArg Prod.snd hxy
  let : (volume : Measure (ℝ × (Fin n → ℝ))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hi := integrableOn_image_iff_of_bounded_jacobian volume hΨ (hR.prod hD)
    hinj c.lower_pos (fun z hz => by rw [hdet]; exact c.jacobian_bounds z.2 (hsub hz.2)) g
  have himage : Ψ '' (R ×ˢ D) = R ×ˢ (c.chart '' D) := by
    simp only [Ψ, Set.prodMap_image_prod, Set.image_id, c.coe_eq, F]
  rw [himage] at hi
  have hfun : (fun x => g (Ψ x)) = (fun z => g (z.1, c.chart z.2)) := by
    funext z
    rw [c.coe_eq]
    rfl
  rwa [hfun] at hi

end ResidualSLT
