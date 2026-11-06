module
public import ResidualSLT.RegularAngular
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! Homogeneous losses in projective cones. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Metric

@[expose] def homogeneousConeLoss {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (k : ℕ) (w : Fin n → ℝ) : ℝ := f w ^ 2 + ‖w‖ ^ (2 * k)

@[expose] def projectiveAngular {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ)
    (j : Fin (n + 1)) (y : Fin n → ℝ) : ℝ := f (j.insertNth 1 y)

/-- Uniform comparison on a bounded projective patch. The norm is the existing
finite-product maximum norm; the pivot is fixed at one. -/
theorem homogeneousConeLoss_radial_bounds {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (r q : ℕ) (hhom : ∀ t w, f (t • w) = t ^ r * f w)
    (j : Fin n) (z : Fin n → ℝ) (hz : 0 < z j)
    (B : ℝ) (hB : 1 ≤ B) (hbound : ∀ i, i ≠ j → |z i| ≤ B) :
    z j ^ (2 * r) * (f (Function.update z j 1) ^ 2 + z j ^ (2 * q)) ≤
        homogeneousConeLoss f (r + q) (radialBlowup j z) ∧
    homogeneousConeLoss f (r + q) (radialBlowup j z) ≤
        B ^ (2 * (r + q)) *
          (z j ^ (2 * r) * (f (Function.update z j 1) ^ 2 + z j ^ (2 * q))) := by
  let u := Function.update z j 1
  have hu1 : 1 ≤ ‖u‖ := by
    simpa [u] using (norm_le_pi_norm u j)
  have huB : ‖u‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg (le_trans zero_le_one hB)).mpr
    intro i
    by_cases hi : i = j
    · subst i; simpa [u] using hB
    · simpa [u, hi, Real.norm_eq_abs] using hbound i hi
  have he : homogeneousConeLoss f (r + q) (radialBlowup j z) =
      z j ^ (2 * r) * (f u ^ 2 + z j ^ (2 * q) * ‖u‖ ^ (2 * (r + q))) := by
    rw [homogeneousConeLoss, radialBlowup_eq_smul, hhom, norm_smul, Real.norm_eq_abs,
      abs_of_pos hz, mul_pow, mul_pow]
    simp only [← pow_mul]
    rw [show 2 * (r + q) = 2 * r + 2 * q by omega, pow_add]
    ring
  have hlow : 1 ≤ ‖u‖ ^ (2 * (r + q)) := one_le_pow₀ hu1
  have hupp : ‖u‖ ^ (2 * (r + q)) ≤ B ^ (2 * (r + q)) :=
    pow_le_pow_left₀ (norm_nonneg _) huB _
  have hBB : 1 ≤ B ^ (2 * (r + q)) := one_le_pow₀ hB
  rw [he]
  constructor
  · apply mul_le_mul_of_nonneg_left _ (pow_nonneg hz.le _)
    nlinarith [mul_le_mul_of_nonneg_left hlow (pow_nonneg hz.le (2 * q))]
  · rw [mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hz.le _)
    nlinarith [mul_le_mul_of_nonneg_left hupp (pow_nonneg hz.le (2 * q)),
      mul_le_mul_of_nonneg_right hBB (sq_nonneg (f u))]

/-- The old radial Jacobian theorem applies to any homogeneous scalar function. -/
theorem homogeneousConeLoss_on_radial_patch_iff {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f)
    (r q : ℕ) (hhom : ∀ t w, f (t • w) = t ^ r * f w)
    (j : Fin n) {D : Set (Fin n → ℝ)} (hD : MeasurableSet D)
    (hpos : ∀ z ∈ D, 0 < z j) (B : ℝ) (hB : 1 ≤ B)
    (hbound : ∀ z ∈ D, ∀ i, i ≠ j → |z i| ≤ B) (s : ℝ) :
    IntegrableOn (fun w => homogeneousConeLoss f (r + q) w ^ (-s))
      (radialBlowup j '' D) volume ↔
    IntegrableOn (fun z => (z j ^ (2 * r) *
      (f (Function.update z j 1) ^ 2 + z j ^ (2 * q))) ^ (-s)) D
      (volume.withDensity (fun z => ENNReal.ofReal (z j ^ (n - 1)))) := by
  let ν := volume.withDensity (fun z : Fin n → ℝ => ENNReal.ofReal (z j ^ (n - 1)))
  have hchange : IntegrableOn (fun w => homogeneousConeLoss f (r + q) w ^ (-s))
      (radialBlowup j '' D) volume ↔
      IntegrableOn (fun z => homogeneousConeLoss f (r + q) (radialBlowup j z) ^ (-s)) D ν := by
    rw [radialBlowup_integrableOn_image_iff j hD hpos]
    change _ ↔ IntegrableOn _ D (volume.withDensity
      (fun z : Fin n → ℝ => (Real.toNNReal (z j ^ (n - 1)) : ENNReal)))
    rw [integrableOn_withDensity_iff_weighted hD (by fun_prop)]
    apply integrableOn_congr_fun _ hD
    intro z hz
    dsimp only
    rw [Real.coe_toNNReal _ (pow_nonneg (hpos z hz).le _)]
  rw [hchange]
  have hfm := hf.measurable
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  apply integrableOn_rpow_iff_of_comparable_all
    (by fun_prop) (by unfold homogeneousConeLoss radialBlowup; fun_prop)
    _ zero_lt_one (pow_pos hB0 (2 * (r + q))) _ _ s
  · filter_upwards [ae_restrict_mem hD] with z hz
    have hx : 0 < z j := hpos z hz
    positivity
  · filter_upwards [ae_restrict_mem hD] with z hz
    simpa only [one_mul] using
      (homogeneousConeLoss_radial_bounds f r q hhom j z (hpos z hz) B hB (hbound z hz)).1
  · filter_upwards [ae_restrict_mem hD] with z hz
    exact (homogeneousConeLoss_radial_bounds f r q hhom j z (hpos z hz) B hB (hbound z hz)).2

/-- Exact reduction of the reduced loss on a cone patch to a radial/angular integral.
The radial power n is derived from the (n+1)-dimensional Jacobian and product volume. -/
theorem homogeneousConeLoss_projective_iff {n : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : Continuous f)
    (r q : ℕ) (hhom : ∀ t w, f (t • w) = t ^ r * f w)
    (j : Fin (n + 1)) (B : ℝ) (hB : 1 ≤ B)
    {R : Set ℝ} (hR : MeasurableSet R) (hpos : ∀ ρ ∈ R, 0 < ρ)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D)
    (hbound : ∀ y ∈ D, ∀ i, |y i| ≤ B) (s : ℝ) :
    IntegrableOn (fun w => homogeneousConeLoss f (r + q) w ^ (-s)) (projectiveConePatch j R D) volume ↔
      IntegrableOn (fun z : ℝ × (Fin n → ℝ) =>
        weightedCancellation (n + 1) r q s (z.1, projectiveAngular f j z.2)) (R ×ˢ D) volume := by
  let M := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
  have hfst (z : Fin (n + 1) → ℝ) : (M z).1 = z j := rfl
  have hsnd (z : Fin (n + 1) → ℝ) : (M z).2 = fun i => z (j.succAbove i) := rfl
  have hdom : MeasurableSet (M ⁻¹' (R ×ˢ D)) := (hR.prod hD).preimage M.measurable
  have hp : ∀ z ∈ M ⁻¹' (R ×ˢ D), 0 < z j := fun z hz => hpos _ hz.1
  have ha : ∀ z ∈ M ⁻¹' (R ×ˢ D), ∀ i, i ≠ j → |z i| ≤ B := by
    intro z hz i hi
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
    exact hbound _ hz.2 k
  change IntegrableOn _ (radialBlowup j '' (M ⁻¹' (R ×ˢ D))) volume ↔ _
  rw [homogeneousConeLoss_on_radial_patch_iff f hf r q hhom j hdom hp B hB ha s]
  change IntegrableOn _ _ (volume.withDensity
    (fun z : Fin (n + 1) → ℝ => (Real.toNNReal (z j ^ (n + 1 - 1)) : ENNReal))) ↔ _
  rw [integrableOn_withDensity_iff_weighted hdom (by fun_prop)]
  have heq : EqOn (fun z : Fin (n + 1) → ℝ =>
      (Real.toNNReal (z j ^ (n + 1 - 1)) : ℝ) *
        (z j ^ (2 * r) * (f (Function.update z j 1) ^ 2 + z j ^ (2 * q))) ^ (-s))
      ((fun z : ℝ × (Fin n → ℝ) =>
        weightedCancellation (n + 1) r q s (z.1, projectiveAngular f j z.2)) ∘ M)
      (M ⁻¹' (R ×ˢ D)) := by
    intro z hz
    dsimp only [Function.comp_def]
    rw [Real.coe_toNNReal _ (pow_nonneg (hp z hz).le _)]
    rw [hfst, hsnd]
    have he : Function.update z j 1 = j.insertNth 1 (fun i => z (j.succAbove i)) := by
      apply funext
      refine j.forall_iff_succAbove.mpr ⟨?_, ?_⟩
      · simp
      · intro k; simp [Fin.succAbove_ne]
    rw [he]
    unfold projectiveAngular
    simp [weightedCancellation, Real.rpow_natCast]
  rw [integrableOn_congr_fun heq hdom]
  exact (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j).integrableOn_comp_preimage M.measurableEmbedding



/-- The fixed-pivot embedding has a constant, explicit derivative. -/
@[expose] def projectiveInsertLinear {n : ℕ} (j : Fin (n + 1)) :
    (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi (j.insertNth 0 (fun i => ContinuousLinearMap.proj i))

theorem projectiveInsertLinear_apply {n : ℕ} (j : Fin (n + 1)) (v : Fin n → ℝ) :
    projectiveInsertLinear j v = j.insertNth 0 v := by
  apply funext
  refine j.forall_iff_succAbove.mpr ⟨?_, ?_⟩
  · simp [projectiveInsertLinear]
  · intro i; simp [projectiveInsertLinear]

theorem projectiveInsert_hasFDerivAt {n : ℕ} (j : Fin (n + 1)) (y : Fin n → ℝ) :
    HasFDerivAt (fun v : Fin n → ℝ => j.insertNth (1 : ℝ) v) (projectiveInsertLinear j) y := by
  apply hasFDerivAt_pi.mpr
  refine j.forall_iff_succAbove.mpr ⟨?_, ?_⟩
  · simpa [projectiveInsertLinear] using (hasFDerivAt_const (c := (1 : ℝ)) y)
  · intro i
    simpa [projectiveInsertLinear] using!
      (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := y)

theorem projectiveAngular_contDiff {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) (j : Fin (n + 1)) : ContDiff ℝ 1 (projectiveAngular f j) := by
  apply hf.comp
  apply contDiff_pi.mpr
  refine j.forall_iff_succAbove.mpr ⟨?_, ?_⟩
  · simpa using (contDiff_const : ContDiff ℝ 1 (fun _ : Fin n → ℝ => (1 : ℝ)))
  · intro i; simp only [Fin.insertNth_apply_succAbove]; fun_prop

/-- Euler's identity turns ambient regularity at a homogeneous zero into angular
regularity in every fixed-pivot chart. No global sphere chart is assumed. -/
theorem projectiveAngular_zero_regular {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) (r : ℕ) (hhom : ∀ t w, f (t • w) = t ^ r * f w)
    (j : Fin (n + 1)) (y : Fin n → ℝ) (hz : projectiveAngular f j y = 0)
    (hreg : ∃ i, fderiv ℝ f (j.insertNth 1 y) (Pi.single i 1) ≠ 0) :
    ∃ i, fderiv ℝ (projectiveAngular f j) y (Pi.single i 1) ≠ 0 := by
  classical
  let u : Fin (n + 1) → ℝ := j.insertNth 1 y
  let A := fderiv ℝ f u
  have hdiff := (hf.differentiable (by norm_num) u).hasFDerivAt
  have heuler : A u = 0 := by
    have h := hdiff.apply_self_eq_nsmul_of_homogeneous (k := r) hhom
    simpa [A, u, projectiveAngular] using h.trans (by simp [show f u = 0 from hz])
  have hder : fderiv ℝ (projectiveAngular f j) y = A.comp (projectiveInsertLinear j) :=
    (hdiff.comp y (projectiveInsert_hasFDerivAt j y)).fderiv
  by_contra! hall
  have hother (i : Fin n) : A (Pi.single (j.succAbove i) 1) = 0 := by
    have he : projectiveInsertLinear j (Pi.single i 1) = Pi.single (j.succAbove i) 1 := by
      rw [projectiveInsertLinear_apply]
      apply funext
      refine j.forall_iff_succAbove.mpr ⟨?_, ?_⟩
      · simp
      · intro l; simp [Pi.single_apply, Fin.succAbove_right_injective.eq_iff]
    simpa [hder, ContinuousLinearMap.comp_apply, he] using hall i
  have hexpand (v : Fin (n + 1) → ℝ) : A v = ∑ i, v i * A (Pi.single i 1) := by
    conv_lhs => rw [← Finset.univ_sum_single v, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have he : Pi.single i (v i) = v i • Pi.single i (1 : ℝ) := by
      ext l
      by_cases h : l = i <;> simp [h]
    rw [he, map_smul, smul_eq_mul]
  have hj : A (Pi.single j 1) = 0 := by
    rw [hexpand, j.sum_univ_succAbove] at heuler
    simpa [u, hother] using heuler
  obtain ⟨i, hi⟩ := hreg
  by_cases hij : i = j
  · subst i; exact hi hj
  · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hij
    exact hi (hother l)


/-- A nonzero scalar differential has a nonzero coordinate partial. -/
theorem exists_nonzero_coordinate_partial {n : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] ℝ) (hA : A ≠ 0) : ∃ i, A (Pi.single i 1) ≠ 0 := by
  classical
  by_contra! h
  apply hA
  ext v
  rw [← Finset.univ_sum_single v, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  have he : Pi.single i (v i) = v i • Pi.single i (1 : ℝ) := by
    ext l
    by_cases hl : l = i <;> simp [hl]
  simp [he, h]

/-- Every nonzero homogeneous zero has a bounded projective representative.
The representative is strictly inside the angular cube of radius two. -/
theorem homogeneous_projective_zero {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ)
    (r : ℕ) (hhom : ∀ t w, f (t • w) = t ^ r * f w)
    (hzero : ∃ w, w ≠ 0 ∧ f w = 0) :
    ∃ j : Fin (n + 1), ∃ y : Fin n → ℝ,
      y ∈ closedBall 0 1 ∧ projectiveAngular f j y = 0 := by
  obtain ⟨w, hw, hf⟩ := hzero
  obtain ⟨j, z, hz0, _, hza, hwz⟩ := signed_radialBlowup_cover (‖w‖ + 1) w
    (mem_ball_zero_iff.mpr (by linarith)) hw
  let y : Fin n → ℝ := fun i => z (j.succAbove i)
  have he : Function.update z j 1 = j.insertNth 1 y := by
    apply funext
    refine j.forall_iff_succAbove.mpr ⟨?_, ?_⟩
    · simp
    · intro i; simp [y, Fin.succAbove_ne]
  refine ⟨j, y, ?_, ?_⟩
  · rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    exact fun i => hza _ (Fin.succAbove_ne j i)
  · have hb : f (radialBlowup j z) = 0 := by
      rcases hwz with h | h
      · rwa [← h]
      · have hn := hhom (-1) (radialBlowup j z)
        simp only [neg_one_smul] at hn
        rw [← h, hf] at hn
        exact (mul_eq_zero.mp hn.symm).resolve_left (pow_ne_zero _ (by norm_num))
    rw [radialBlowup_eq_smul, hhom, he] at hb
    exact (mul_eq_zero.mp hb).resolve_left (pow_pos hz0 r).ne'

/-- Enlarging an angular patch requires shrinking the radial interval.
This proves the inclusion for the actual image of the blow-up map. -/
theorem projectiveConePatch_subset_scaled_ball {n : ℕ} (j : Fin (n + 1))
    (B : ℝ) (hB : 1 ≤ B) (ε : ℝ)
    {D : Set (Fin n → ℝ)} (hbound : ∀ y ∈ D, ∀ i, |y i| ≤ B) :
    projectiveConePatch j (Ioo 0 (ε / B)) D ⊆ ball 0 ε := by
  rintro w ⟨z, hz, rfl⟩
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hz0 : 0 < z j := hz.1.1
  have hzε : z j * B < ε := (lt_div_iff₀ hB0).mp hz.1.2
  apply mem_ball_zero_iff.mpr
  apply lt_of_le_of_lt _ hzε
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hz0.le hB0.le)).mpr
  intro i
  by_cases hij : i = j
  · subst i
    simpa [radialBlowup, Real.norm_eq_abs, abs_of_pos hz0] using
      mul_le_mul_of_nonneg_left hB hz0.le
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij
    simpa [radialBlowup, Fin.succAbove_ne, Real.norm_eq_abs, abs_mul, abs_of_pos hz0, Fin.removeNth] using!
      mul_le_mul_of_nonneg_left (hbound _ hz.2 k) hz0.le

/-- Squaring a homogeneous scalar function makes the loss invariant under reflection. -/
theorem homogeneousConeLoss_neg {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (r k : ℕ) (hhom : ∀ t w, f (t • w) = t ^ r * f w) (w : Fin n → ℝ) :
    homogeneousConeLoss f k (-w) = homogeneousConeLoss f k w := by
  have h := hhom (-1) w
  simp only [neg_one_smul] at h
  have hsq : ((-1 : ℝ) ^ r) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm r 2, pow_mul]; norm_num
  simp [homogeneousConeLoss, h, mul_pow, hsq]

/-- Positive and negative pivot patches cover the full raw ball, including all
angular chart overlaps; the origin is added explicitly. -/
theorem homogeneousConeLoss_integrable_of_angular (r q n : ℕ)
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : Continuous f)
    (hhom : ∀ t w, f (t • w) = t ^ r * f w) (ε : ℝ) (s : ℝ)
    (hi : ∀ j : Fin (n + 1), IntegrableOn (fun z : ℝ × (Fin (n) → ℝ) =>
      weightedCancellation (n + 1) r q s (z.1, projectiveAngular f j z.2))
      (Ioo 0 ε ×ˢ closedBall 0 1) volume) :
    IntegrableOn (fun w : Fin (n + 1) → ℝ => homogeneousConeLoss f (r + q) w ^ (-s)) (ball 0 ε) volume := by
  let P := fun j : Fin (n + 1) => projectiveConePatch j (Ioo 0 ε)
    (closedBall (0 : Fin (n) → ℝ) 1)
  have hbound : ∀ y ∈ closedBall (0 : Fin (n) → ℝ) 1, ∀ i, |y i| ≤ 1 := by
    intro y hy i
    exact (norm_le_pi_norm y i).trans (mem_closedBall_zero_iff.mp hy)
  have hpos (j : Fin (n + 1)) : IntegrableOn
      (fun w => homogeneousConeLoss f (r + q) w ^ (-s)) (P j) volume := by
    apply (homogeneousConeLoss_projective_iff f hf r q hhom j 1 le_rfl measurableSet_Ioo
      (fun _ h => h.1) measurableSet_closedBall hbound s).mpr
    exact hi j
  have hneg (j : Fin (n + 1)) : IntegrableOn
      (fun w => homogeneousConeLoss f (r + q) w ^ (-s)) (Neg.neg '' P j) volume := by
    have he := (Measure.measurePreserving_neg (volume : Measure (Fin (n + 1) → ℝ))).integrableOn_comp_preimage
      (Homeomorph.neg (Fin (n + 1) → ℝ)).measurableEmbedding
      (f := fun w => homogeneousConeLoss f (r + q) w ^ (-s)) (s := P j)
    have hc : (fun w : Fin (n + 1) → ℝ => homogeneousConeLoss f (r + q) w ^ (-s)) ∘ Neg.neg =
        (fun w => homogeneousConeLoss f (r + q) w ^ (-s)) := by
      funext w; simp only [Function.comp_apply, homogeneousConeLoss_neg f r (r + q) hhom]
    have hp : Neg.neg ⁻¹' P j = Neg.neg '' P j := by
      ext w
      constructor
      · intro hw; exact ⟨-w, hw, neg_neg w⟩
      · rintro ⟨v, hv, rfl⟩; simpa using hv
    rw [hc, hp] at he
    exact he.mpr (hpos j)
  have hall : IntegrableOn (fun w : Fin (n + 1) → ℝ => homogeneousConeLoss f (r + q) w ^ (-s))
      ({0} ∪ ⋃ j, (P j ∪ Neg.neg '' P j)) volume :=
    (integrableOn_singleton (μ := volume) (f := fun w : Fin (n + 1) → ℝ => homogeneousConeLoss f (r + q) w ^ (-s)) (x := 0) (hx := by simp)).union (integrableOn_finite_iUnion.mpr (fun j => (hpos j).union (hneg j)))
  apply hall.mono_set
  intro w hw
  by_cases hz : w = 0
  · exact Or.inl hz
  · obtain ⟨j, z, hz0, hzε, hza, hwz⟩ := signed_radialBlowup_cover ε w hw hz
    have hp : radialBlowup j z ∈ P j := by
      refine ⟨z, ?_, rfl⟩
      change (z j ∈ Ioo 0 ε) ∧ (fun i => z (j.succAbove i)) ∈ closedBall 0 1
      refine ⟨⟨hz0, hzε⟩, ?_⟩
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
      intro i
      exact hza _ (Fin.succAbove_ne j i)
    apply Or.inr
    apply mem_iUnion.mpr
    refine ⟨j, ?_⟩
    rcases hwz with hwz | hwz
    · exact Or.inl (hwz.symm ▸ hp)
    · exact Or.inr ⟨radialBlowup j z, hp, hwz.symm⟩



/-- Exact whole-neighborhood threshold for a homogeneous function with nonempty,
simple cancellation. Regularity is stated on the punctured zero cone. The radial
exponent is k=r+q with r,q positive. All real singular exponents are covered. -/
theorem homogeneousConeLoss_integrableOn_iff (n r q : ℕ) (hr : 0 < r) (hq : 0 < q)
    (f : (Fin (n + 2) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hhom : ∀ t w, f (t • w) = t ^ r * f w)
    (hreg : ∀ w, w ≠ 0 → f w = 0 → fderiv ℝ f w ≠ 0)
    (hzero : ∃ w, w ≠ 0 ∧ f w = 0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ) :
    IntegrableOn (fun w => homogeneousConeLoss f (r + q) w ^ (-s)) (ball 0 ε) volume ↔
      s < min ((n + 2 : ℝ) / (2 * r))
        (((n + 2 : ℝ) + q) / (2 * ((r : ℝ) + q))) := by
  have hregular (j : Fin (n + 2)) (y : Fin (n + 1) → ℝ)
      (hz : projectiveAngular f j y = 0) :
      ∃ i, fderiv ℝ (projectiveAngular f j) y (Pi.single i 1) ≠ 0 := by
    apply projectiveAngular_zero_regular f hf r hhom j y hz
    apply exists_nonzero_coordinate_partial
    apply hreg _ _ hz
    intro he
    have := congrFun he j
    simp at this
  constructor
  · intro hi
    obtain ⟨j, y, hy, hz⟩ := homogeneous_projective_zero f r hhom hzero
    have hb : ∀ v ∈ closedBall (0 : Fin (n + 1) → ℝ) 2, ∀ i, |v i| ≤ 2 :=
      fun v hv i => (norm_le_pi_norm v i).trans (mem_closedBall_zero_iff.mp hv)
    have hsub := projectiveConePatch_subset_scaled_ball j 2 (by norm_num) ε hb
    have hpatch := (homogeneousConeLoss_projective_iff f hf.continuous r q hhom j 2
      (by norm_num) measurableSet_Ioo (fun _ h => h.1) measurableSet_closedBall hb s).mp
      (hi.mono_set hsub)
    simp only [Nat.cast_add, Nat.cast_one] at hpatch
    have ha : 0 < (n + 1 + 1 : ℝ) := by positivity
    have hneed := weightedAngular_regular_necessary r q n hr hq (projectiveAngular f j)
      (projectiveAngular_contDiff f hf j) 2 (n + 1 + 1) ha (ε / 2)
      (by positivity) (by linarith) s y
      (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hy).trans_lt (by norm_num))) hz
      (hregular j y hz) hpatch
    simpa only [show (n : ℝ) + 1 + 1 = n + 2 by ring] using hneed
  · intro hs
    apply homogeneousConeLoss_integrable_of_angular r q (n + 1) f hf.continuous hhom ε s
    intro j
    simp only [Nat.cast_add, Nat.cast_one]
    have hsub : Ioo (0 : ℝ) ε ×ˢ closedBall (0 : Fin (n + 1) → ℝ) 1 ⊆
        Ioo 0 1 ×ˢ closedBall 0 1 := prod_mono (Ioo_subset_Ioo le_rfl hε1) Subset.rfl
    by_cases hs0 : 0 ≤ s
    · apply (weightedAngular_integrable_regular r q n hr hq (projectiveAngular f j)
        (projectiveAngular_contDiff f hf j) 1 zero_lt_one (fun y _ hz => hregular j y hz)
        (n + 1 + 1) (by positivity) s hs0 _).mono_set hsub
      simpa only [show (n : ℝ) + 1 + 1 = n + 2 by ring] using hs
    · exact (weightedAngular_integrable_nonpos_general (projectiveAngular f j)
        (projectiveAngular_contDiff f hf j).continuous 1 (n + 1 + 1) (by positivity)
        r q s (le_of_not_ge hs0)).mono_set hsub


/-- Scaling preserves a zero differential of a C¹ homogeneous function. -/
theorem homogeneous_fderiv_zero_smul {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) (r : ℕ) (hhom : ∀ t w, f (t • w) = t ^ r * f w)
    (t : ℝ) (ht : t ≠ 0) (w : Fin n → ℝ) (hw : fderiv ℝ f w = 0) :
    fderiv ℝ f (t • w) = 0 := by
  have hl := ((hf.differentiable (by norm_num) (t • w)).hasFDerivAt).comp w
    ((hasFDerivAt_id w).const_smul t)
  have hr := ((hf.differentiable (by norm_num) w).hasFDerivAt).const_smul (t ^ r)
  have he : (fun v => f (t • v)) = (fun v => t ^ r • f v) := funext (hhom t)
  change HasFDerivAt (fun v => f (t • v)) _ w at hl
  rw [he] at hl
  have hmap := hl.unique hr
  rw [hw, smul_zero] at hmap
  ext v
  have hv := congrArg (fun A : (Fin n → ℝ) →L[ℝ] ℝ => A (t⁻¹ • v)) hmap
  simpa [ContinuousLinearMap.comp_apply, smul_smul, ht] using hv

/-- Checking ambient regularity only on the unit sphere suffices for the entire
punctured homogeneous zero cone. The sphere uses the ambient norm. -/
theorem homogeneous_regular_of_unit_sphere {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) (r : ℕ) (hhom : ∀ t w, f (t • w) = t ^ r * f w)
    (hreg : ∀ u, ‖u‖ = 1 → f u = 0 → fderiv ℝ f u ≠ 0) :
    ∀ w, w ≠ 0 → f w = 0 → fderiv ℝ f w ≠ 0 := by
  intro w hw hz hder
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let t := ‖w‖⁻¹
  have ht : 0 < t := inv_pos.mpr hn
  have hu : ‖t • w‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact inv_mul_cancel₀ hn.ne'
  have hzero : f (t • w) = 0 := by rw [hhom, hz, mul_zero]
  exact hreg _ hu hzero (homogeneous_fderiv_zero_smul f hf r hhom t ht.ne' w hder)

/-- User-facing degree notation: k>d, ambient dimension N≥2, and a bounded positive
prior. The loss J is measurable and comparable a.e. to f²+‖w‖^(2k). Regularity is an
explicit nonzero differential condition on homogeneous zeros of the unit sphere. -/
theorem homogeneous_cancellation_prior_integrableOn_iff (N d k : ℕ)
    (hN : 2 ≤ N) (hd : 0 < d) (hdk : d < k)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hhom : ∀ t w, f (t • w) = t ^ d * f w)
    (hreg : ∀ u, ‖u‖ = 1 → f u = 0 → fderiv ℝ f u ≠ 0)
    (hzero : ∃ w, w ≠ 0 ∧ f w = 0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (J : (Fin N → ℝ) → ℝ) (hJ : AEMeasurable J (volume.restrict (ball 0 ε)))
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hlo : ∀ᵐ w ∂volume.restrict (ball 0 ε), c * homogeneousConeLoss f k w ≤ J w)
    (hup : ∀ᵐ w ∂volume.restrict (ball 0 ε), J w ≤ C * homogeneousConeLoss f k w)
    (p : (Fin N → ℝ) → NNReal) (hp : BoundedPositivePriorOn p (ball 0 ε) volume)
    (s : ℝ) :
    IntegrableOn (fun w => J w ^ (-s)) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal))) ↔
      s < min ((N : ℝ) / (2 * d)) (((N : ℝ) + k - d) / (2 * k)) := by
  rw [integrableOn_withDensity_iff_of_boundedPositive measurableSet_ball hp]
  have hpos : ∀ᵐ w ∂volume.restrict (ball (0 : Fin N → ℝ) ε),
      0 < homogeneousConeLoss f k w := by
    let : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
    filter_upwards [ae_restrict_of_ae ((volume : Measure (Fin N → ℝ)).ae_ne 0)] with w hw
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos (norm_pos_iff.mpr hw) _)
  have hm : Measurable (homogeneousConeLoss f k) := by
    have hfm := hf.continuous.measurable
    unfold homogeneousConeLoss
    fun_prop
  rw [integrableOn_rpow_iff_of_comparable_all hm.aemeasurable hJ hpos hc hC hlo hup]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  have he : d + (k - d) = k := Nat.add_sub_of_le hdk.le
  have ht := homogeneousConeLoss_integrableOn_iff n d (k - d) hd (by omega) f hf hhom
    (homogeneous_regular_of_unit_sphere f hf d hhom hreg) hzero ε hε hε1 s
  rw [he] at ht
  have hden : (d : ℝ) + (k - d : ℕ) = k := by exact_mod_cast he
  rw [hden, Nat.cast_sub hdk.le] at ht
  simpa only [Nat.cast_add, Nat.cast_ofNat, add_sub_assoc] using ht

/-- Explicit endpoint and supercritical failure for the comparable loss and prior. -/
theorem homogeneous_cancellation_prior_not_integrable (N d k : ℕ)
    (hN : 2 ≤ N) (hd : 0 < d) (hdk : d < k)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hhom : ∀ t w, f (t • w) = t ^ d * f w)
    (hreg : ∀ u, ‖u‖ = 1 → f u = 0 → fderiv ℝ f u ≠ 0)
    (hzero : ∃ w, w ≠ 0 ∧ f w = 0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (J : (Fin N → ℝ) → ℝ) (hJ : AEMeasurable J (volume.restrict (ball 0 ε)))
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hlo : ∀ᵐ w ∂volume.restrict (ball 0 ε), c * homogeneousConeLoss f k w ≤ J w)
    (hup : ∀ᵐ w ∂volume.restrict (ball 0 ε), J w ≤ C * homogeneousConeLoss f k w)
    (p : (Fin N → ℝ) → NNReal) (hp : BoundedPositivePriorOn p (ball 0 ε) volume)
    (s : ℝ) (hs : min ((N : ℝ) / (2 * d)) (((N : ℝ) + k - d) / (2 * k)) ≤ s) :
    ¬ IntegrableOn (fun w => J w ^ (-s)) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal))) := by
  rw [homogeneous_cancellation_prior_integrableOn_iff N d k hN hd hdk f hf hhom hreg hzero
    ε hε hε1 J hJ c C hc hC hlo hup p hp s]
  exact not_lt.mpr hs

end ResidualSLT
