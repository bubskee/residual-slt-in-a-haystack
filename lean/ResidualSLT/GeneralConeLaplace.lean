module
public import ResidualSLT.GeneralAngularLaplace
public import ResidualSLT.ConeLaplace
public import ResidualSLT.LaplaceTransfer

/-! Critical homogeneous cancellation, including projective-boundary zero witnesses. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Filter Metric

/-- Exact integration on the actual radial image, for an arbitrary real integrand. -/
theorem projectiveConePatch_integral {n : ℕ} (j : Fin (n+1))
    {R : Set ℝ} (hR : MeasurableSet R) (hp : ∀ t ∈ R, 0 < t)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D) (g : (Fin (n+1) → ℝ) → ℝ) :
    (∫ w in projectiveConePatch j R D, g w) =
      ∫ z : ℝ × (Fin n → ℝ) in R ×ˢ D, z.1^n * g (z.1 • j.insertNth 1 z.2) := by
  let M := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) j
  have hdom : MeasurableSet (M ⁻¹' (R ×ˢ D)) := (hR.prod hD).preimage M.measurable
  rw [projectiveConePatch,radialBlowup_integral_image j hdom (fun z hz => hp _ hz.1)]
  have he (z : Fin (n+1) → ℝ) : Function.update z j 1 = j.insertNth 1 (M z).2 := by
    apply funext
    refine j.forall_iff_succAbove.mpr ⟨?_,?_⟩
    · simp
    · intro i; simp [M,Fin.succAbove_ne,Fin.removeNth]
  have heq : (fun z : Fin (n+1) → ℝ => z j^(n+1-1)*g (radialBlowup j z)) =
      (fun z => (M z).1^n*g ((M z).1 • j.insertNth 1 (M z).2)) := by
    funext z
    rw [radialBlowup_eq_smul,he]
    rfl
  rw [heq]
  exact (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) j).setIntegral_preimage_emb
    M.measurableEmbedding (fun z : ℝ × (Fin n → ℝ) => z.1^n*g (z.1 • j.insertNth 1 z.2)) (R ×ˢ D)

/-- Quantitative comparison on a bounded projective image. Enlarged angular patches
have the explicit loss factor B^(2(r+q)), rather than being identified with a unit patch. -/
theorem homogeneous_critical_projective_bounds {n : ℕ} (r q : ℕ) (hdim : n+1 = r)
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hhom : ∀ t w, f (t • w) = t^r*f w) (j : Fin (n+1))
    (B : ℝ) (hB : 1 ≤ B) (ε N : ℝ) (hN : 0 ≤ N) :
    (∫ z in Ioo 0 ε ×ˢ closedBall 0 B,
      generalAngularKernel r q (projectiveAngular f j) (B^(2*(r+q))*N) z) ≤
      (∫ w in projectiveConePatch j (Ioo 0 ε) (closedBall 0 B),
        Real.exp (-N*homogeneousConeLoss f (r+q) w)) ∧
    (∫ w in projectiveConePatch j (Ioo 0 ε) (closedBall 0 B),
        Real.exp (-N*homogeneousConeLoss f (r+q) w)) ≤
      ∫ z in Ioo 0 ε ×ˢ closedBall 0 B, generalAngularKernel r q (projectiveAngular f j) N z := by
  rw [projectiveConePatch_integral j measurableSet_Ioo (fun _ h => h.1) measurableSet_closedBall]
  have hinsert : Continuous (fun y : Fin n → ℝ => (j.insertNth (1:ℝ) y : Fin (n+1) → ℝ)) :=
    continuous_iff_continuousAt.mpr (fun y => (projectiveInsert_hasFDerivAt j y).continuousAt)
  have hcparam : Continuous (fun z : ℝ × (Fin n → ℝ) => (z.1 • j.insertNth (1:ℝ) z.2 : Fin (n+1) → ℝ)) :=
    continuous_fst.smul (hinsert.comp continuous_snd)
  have hcf : Continuous f := hf.continuous
  have hK : Continuous (homogeneousConeLoss f (r+q)) := by unfold homogeneousConeLoss; fun_prop
  have hi : IntegrableOn (fun z : ℝ × (Fin n → ℝ) => z.1^n *
      Real.exp (-N*homogeneousConeLoss f (r+q) (z.1 • j.insertNth 1 z.2)))
      (Ioo 0 ε ×ˢ closedBall 0 B) volume :=
    ((by fun_prop : Continuous (fun z : ℝ × (Fin n → ℝ) => z.1^n *
      Real.exp (-N*homogeneousConeLoss f (r+q) (z.1 • j.insertNth 1 z.2)))).continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_closedBall 0 B))).mono_set (prod_mono Ioo_subset_Icc_self Subset.rfl)
  have hb (z : ℝ × (Fin n → ℝ)) (hz : z ∈ Ioo 0 ε ×ˢ closedBall 0 B) :
      z.1^(2*r)*((projectiveAngular f j z.2)^2+z.1^(2*q)) ≤
        homogeneousConeLoss f (r+q) (z.1 • j.insertNth 1 z.2) ∧
      homogeneousConeLoss f (r+q) (z.1 • j.insertNth 1 z.2) ≤
        B^(2*(r+q))*(z.1^(2*r)*((projectiveAngular f j z.2)^2+z.1^(2*q))) := by
    let v : Fin (n+1) → ℝ := j.insertNth z.1 z.2
    have he : Function.update v j 1 = j.insertNth 1 z.2 := by
      apply funext
      refine j.forall_iff_succAbove.mpr ⟨?_,?_⟩
      · simp [v]
      · intro l; simp [v,Fin.succAbove_ne]
    have hh := homogeneousConeLoss_radial_bounds f r q hhom j v (by simpa [v] using hz.1.1)
      B hB (by
        intro i hi
        obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq hi
        simpa [v] using (norm_le_pi_norm z.2 l).trans (mem_closedBall_zero_iff.mp hz.2))
    simpa only [radialBlowup_eq_smul,he,v,Fin.insertNth_apply_same,projectiveAngular] using hh
  have hpow (z : ℝ × (Fin n → ℝ)) : z.1^n = z.1^(r-1) := by congr 1; omega
  constructor
  · apply setIntegral_mono_on (generalAngularKernel_integrable r q _ (projectiveAngular_contDiff f hf j).continuous _ ε B)
      hi (measurableSet_Ioo.prod measurableSet_closedBall)
    intro z hz
    rw [hpow]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hz.1.1.le _)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (hb z hz).2 hN]
  · apply setIntegral_mono_on hi
      (generalAngularKernel_integrable r q _ (projectiveAngular_contDiff f hf j).continuous _ ε B)
      (measurableSet_Ioo.prod measurableSet_closedBall)
    intro z hz
    rw [hpow]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hz.1.1.le _)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (hb z hz).1 hN]

/-- Upper bounds on the finite signed cover require no zero in every individual patch. -/
theorem laplace_upper_of_projective_cones {n : ℕ} (K : (Fin (n+1) → ℝ) → ℝ)
    (hK : Continuous K) (heven : ∀ w, K (-w) = K w) (ε : ℝ)
    (hcones : ∀ j : Fin (n+1), CriticalLaplaceUpper (fun N =>
      ∫ w in projectiveConePatch j (Ioo 0 ε) (closedBall 0 1), Real.exp (-N*K w))) :
    CriticalLaplaceUpper (fun N => ∫ w in ball 0 ε, Real.exp (-N*K w)) := by
  classical
  let P := fun j : Fin (n+1) => projectiveConePatch j (Ioo 0 ε) (closedBall 0 1)
  have hm (j) : MeasurableSet (P j) := projectiveConePatch_measurableSet j
    measurableSet_Ioo (fun _ h => h.1) measurableSet_closedBall
  have hsub (j) : P j ⊆ ball 0 ε := projectiveConePatch_subset_ball j
    (fun _ h => h.1) (fun _ h => h.2)
    (fun y hy i => (norm_le_pi_norm y i).trans (mem_closedBall_zero_iff.mp hy))
  have hnsub (j) : Neg.neg '' P j ⊆ ball 0 ε := by
    rintro w ⟨v,hv,rfl⟩
    simpa using hsub j hv
  have hi (N : ℝ) : IntegrableOn (fun w => Real.exp (-N*K w)) (ball 0 ε) volume :=
    ((by fun_prop : Continuous (fun w => Real.exp (-N*K w))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall
  have hneg (j) (N : ℝ) :
      (∫ w in Neg.neg '' P j, Real.exp (-N*K w)) = ∫ w in P j, Real.exp (-N*K w) := by
    rw [(Measure.measurePreserving_neg (volume : Measure (Fin (n+1) → ℝ))).setIntegral_image_emb
      (Homeomorph.neg (Fin (n+1) → ℝ)).measurableEmbedding]
    simp only [heven]
  have hsum := CriticalLaplaceUpper.finset_sum (Finset.univ : Finset (Fin (n+1)))
    (fun j N => (∫ w in P j, Real.exp (-N*K w)) + ∫ w in Neg.neg '' P j, Real.exp (-N*K w))
    (fun j _ => (hcones j).add (by simpa only [hneg] using hcones j))
  apply (criticalLaplaceUpper_zero.add hsum).mono
  apply Filter.Eventually.of_forall
  intro N
  let g := fun w => Real.exp (-N*K w)
  have hbound (j) : (∫ w in P j ∪ Neg.neg '' P j, g w) ≤
      (∫ w in P j, g w) + ∫ w in Neg.neg '' P j, g w := by
    have hnm : MeasurableSet (Neg.neg '' P j) :=
      (Homeomorph.neg _).measurableEmbedding.measurableSet_image.mpr (hm j)
    have hh := setIntegral_le_add_sum_of_cover volume ({()} : Finset Unit) g
      (P j ∪ Neg.neg '' P j) (P j) (fun _ => Neg.neg '' P j)
      ((hm j).union hnm) (hm j) (fun _ _ => hnm)
      (((hi N).mono_set (hsub j)).union ((hi N).mono_set (hnsub j)))
      ((hi N).mono_set (hsub j)) (fun _ _ => (hi N).mono_set (hnsub j))
      (by
        intro w hw
        rcases hw with hw | hw
        · exact Or.inl hw
        · exact Or.inr (mem_iUnion₂.mpr ⟨(),by simp,hw⟩))
      (fun _ _ => (Real.exp_pos _).le)
    simpa using hh
  have hcover : ball 0 ε ⊆ {0} ∪ ⋃ j ∈ (Finset.univ : Finset (Fin (n+1))), P j ∪ Neg.neg '' P j := by
    intro w hw
    by_cases hz : w = 0
    · exact Or.inl hz
    · obtain ⟨j,z,hz0,hzε,hza,hwz⟩ := signed_radialBlowup_cover ε w hw hz
      have hp : radialBlowup j z ∈ P j := by
        refine ⟨z, ?_, rfl⟩
        change (z j ∈ Ioo 0 ε) ∧ (fun i => z (j.succAbove i)) ∈ closedBall 0 1
        refine ⟨⟨hz0,hzε⟩, ?_⟩
        rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
        intro i
        exact hza _ (Fin.succAbove_ne j i)
      apply Or.inr
      apply mem_iUnion₂.mpr
      refine ⟨j,Finset.mem_univ _,?_⟩
      rcases hwz with hwz | hwz
      · exact Or.inl (hwz.symm ▸ hp)
      · exact Or.inr ⟨radialBlowup j z,hp,hwz.symm⟩
  have h := setIntegral_le_add_sum_of_cover volume Finset.univ g (ball 0 ε) {0}
    (fun j => P j ∪ Neg.neg '' P j) measurableSet_ball (measurableSet_singleton 0)
    (fun j _ => (hm j).union ((Homeomorph.neg _).measurableEmbedding.measurableSet_image.mpr (hm j)))
    (hi N) (integrableOn_singleton (hx := by simp))
    (fun j _ => ((hi N).mono_set (hsub j)).union ((hi N).mono_set (hnsub j))) hcover
    (fun _ _ => (Real.exp_pos _).le)
  simp only [integral_singleton, Measure.real, measure_singleton, ENNReal.toReal_zero, zero_smul, zero_add] at h
  simpa only [zero_add] using h.trans (Finset.sum_le_sum (fun j _ => hbound j))


/-- Whole-neighborhood critical order. The single lower witness may lie on every
unit-patch boundary: radius-two angular coordinates and radius ε/2 resolve this. -/
theorem homogeneous_critical_laplace_order (n q : ℕ) (hq : 0 < q)
    (f : (Fin (n+2) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hhom : ∀ t w, f (t • w) = t^(n+2)*f w)
    (hreg : ∀ w, w ≠ 0 → f w = 0 → fderiv ℝ f w ≠ 0)
    (hzero : ∃ w, w ≠ 0 ∧ f w = 0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasCriticalLaplaceOrder (fun N => ∫ w in ball 0 ε,
      Real.exp (-N*homogeneousConeLoss f (n+2+q) w)) := by
  have hregular (j : Fin (n+2)) (y : Fin (n+1) → ℝ) (hz : projectiveAngular f j y = 0) :
      ∃ i, fderiv ℝ (projectiveAngular f j) y (Pi.single i 1) ≠ 0 := by
    apply projectiveAngular_zero_regular f hf (n+2) hhom j y hz
    apply exists_nonzero_coordinate_partial
    apply hreg _ _ hz
    intro he
    have hh := congrFun he j
    simp at hh
  have hcf : Continuous f := hf.continuous
  have hK : Continuous (homogeneousConeLoss f (n+2+q)) := by unfold homogeneousConeLoss; fun_prop
  constructor
  · obtain ⟨j,y,hy,hz⟩ := homogeneous_projective_zero f (n+2) hhom hzero
    have hl := generalAngular_lower_of_zero (n+2) q (by omega) hq (projectiveAngular f j)
      (projectiveAngular_contDiff f hf j) 2 (ε/2) (by positivity) y
      (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hy).trans_lt (by norm_num))) hz
      (hregular j y hz)
    apply (hl.comp_mul (2^(2*(n+2+q))) (by positivity)).mono
    filter_upwards [eventually_ge_atTop (0:ℝ)] with N hN
    have hb := homogeneous_critical_projective_bounds (n+2) q rfl f hf hhom j 2 (by norm_num) (ε/2) N hN
    have hs := projectiveConePatch_subset_scaled_ball j 2 (by norm_num) ε
      (fun v hv i => (norm_le_pi_norm v i).trans (mem_closedBall_zero_iff.mp hv))
    have hi : IntegrableOn (fun w => Real.exp (-N*homogeneousConeLoss f (n+2+q) w)) (ball 0 ε) volume :=
      ((by fun_prop : Continuous (fun w => Real.exp (-N*homogeneousConeLoss f (n+2+q) w))).continuousOn.integrableOn_compact
        (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall
    exact hb.1.trans (setIntegral_mono_set hi (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))
      (Filter.Eventually.of_forall hs))
  · apply laplace_upper_of_projective_cones _ hK
      (homogeneousConeLoss_neg f (n+2) (n+2+q) hhom) ε
    intro j
    have hu := generalAngular_regular_upper (n+2) q n (by omega) hq (projectiveAngular f j)
      (projectiveAngular_contDiff f hf j) ε hε hε1 (fun y _ hz => hregular j y hz)
    apply hu.mono
    filter_upwards [eventually_ge_atTop (0:ℝ)] with N hN
    exact (homogeneous_critical_projective_bounds (n+2) q rfl f hf hhom j 1 le_rfl ε N hN).2

/-- Nonempty regular spherical cancellation already forces dimension at least two.
Thus the chart dimension restriction is a consequence, not an additional hypothesis. -/
theorem homogeneous_regular_spherical_zero_dimension (N r : ℕ)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hhom : ∀ t w, f (t • w) = t^r*f w)
    (hreg : ∀ u, ‖u‖ = 1 → f u = 0 → fderiv ℝ f u ≠ 0)
    (hzero : ∃ u, ‖u‖ = 1 ∧ f u = 0) : 2 ≤ N := by
  have hz : ∃ w, w ≠ 0 ∧ f w = 0 := by
    obtain ⟨u,hu,hf⟩ := hzero
    exact ⟨u,by intro he; simp [he] at hu,hf⟩
  have hreg' := homogeneous_regular_of_unit_sphere f hf r hhom hreg
  by_contra hn
  have hcases : N = 0 ∨ N = 1 := by omega
  rcases hcases with he | he
  · subst N
    obtain ⟨w,hw,_⟩ := hz
    exact hw (Subsingleton.elim _ _)
  · subst N
    obtain ⟨j,y,_,hy⟩ := homogeneous_projective_zero f r hhom hz
    have hh := projectiveAngular_zero_regular f hf r hhom j y hy
      (exists_nonzero_coordinate_partial _ (hreg' _ (by
        intro he
        have hv := congrFun he j
        simp at hv) hy))
    obtain ⟨i,_⟩ := hh
    exact Fin.elim0 i

end ResidualSLT
