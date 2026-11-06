module
public import ResidualSLT.TransverseChart
public import ResidualSLT.CancellationGeometry

/-! Explicit projective radial coordinates. The blow-up is injective away from
zero radius, with exact Jacobian rho^(n-1) and a genuine change-of-variables theorem. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Finset

@[expose] def radialBlowup {n : ℕ} (j : Fin n) (z : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i = j then z j else z j * z i

@[expose] def radialBlowupInverse {n : ℕ} (j : Fin n) (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i = j then w j else w i / w j

@[expose] def radialBlowupDeriv {n : ℕ} (j : Fin n) (z : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i => if i = j then ContinuousLinearMap.proj j
    else z i • ContinuousLinearMap.proj j + z j • ContinuousLinearMap.proj i)

theorem radialBlowup_hasFDerivAt {n : ℕ} (j : Fin n) (z : Fin n → ℝ) :
    HasFDerivAt (radialBlowup j) (radialBlowupDeriv j z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i = j
  · simpa [radialBlowup, radialBlowupDeriv, hi] using hasFDerivAt_apply j z
  · simpa [radialBlowup, radialBlowupDeriv, hi, add_comm] using
      (hasFDerivAt_apply (𝕜 := ℝ) j z).fun_mul (hasFDerivAt_apply (𝕜 := ℝ) i z)

theorem radialBlowup_contDiff {n : ℕ} (j : Fin n) : ContDiff ℝ 1 (radialBlowup j) := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i = j
  · simpa [radialBlowup, hi] using contDiff_apply ℝ (fun _ : Fin n => ℝ) j
  · simpa [radialBlowup, hi] using
      (contDiff_apply ℝ (fun _ : Fin n => ℝ) j).mul (contDiff_apply ℝ (fun _ : Fin n => ℝ) i)

/-- Exact inverse, with the nonzero radius hypothesis explicit. -/
theorem radialBlowup_left_inverse {n : ℕ} (j : Fin n) (z : Fin n → ℝ) (hz : z j ≠ 0) :
    radialBlowupInverse j (radialBlowup j z) = z := by
  ext i
  by_cases hi : i = j
  · simp [radialBlowup, radialBlowupInverse, hi]
  · simp [radialBlowup, radialBlowupInverse, hi, hz]

theorem radialBlowup_right_inverse {n : ℕ} (j : Fin n) (w : Fin n → ℝ) (hw : w j ≠ 0) :
    radialBlowup j (radialBlowupInverse j w) = w := by
  ext i
  by_cases hi : i = j
  · simp [radialBlowup, radialBlowupInverse, hi]
  · simp [radialBlowup, radialBlowupInverse, hi, hw, mul_div_cancel₀]

theorem radialBlowup_injOn {n : ℕ} (j : Fin n) :
    InjOn (radialBlowup j) {z : Fin n → ℝ | z j ≠ 0} := by
  intro x hx y hy hxy
  have h := congrArg (radialBlowupInverse j) hxy
  rwa [radialBlowup_left_inverse j x hx, radialBlowup_left_inverse j y hy] at h

/-- The exact dimension-dependent radial Jacobian, including dimension one. -/
theorem radialBlowupDeriv_det {n : ℕ} (j : Fin n) (z : Fin n → ℝ) :
    (radialBlowupDeriv j z).det = z j ^ (n - 1) := by
  change LinearMap.det (radialBlowupDeriv j z).toLinearMap = _
  rw [← LinearMap.det_toMatrix']
  let v := Function.update z j 1
  have hm : LinearMap.toMatrix' (radialBlowupDeriv j z).toLinearMap =
      (z j • (1 : Matrix (Fin n) (Fin n) ℝ)).updateCol j v := by
    ext i k
    simp only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe,
      radialBlowupDeriv, ContinuousLinearMap.pi_apply, Matrix.updateCol_apply]
    by_cases hi : i = j <;> by_cases hk : k = j
    · simp [hi, hk, v]
    · simp [hi, hk, Ne.symm hk, v]
    · simp [hi, hk, v]
    · simp [hi, hk, v, Pi.single_apply, Matrix.one_apply]
  rw [hm, Matrix.det_updateCol_smul_left]
  have hv : v = fun i => ∑ k : Fin n, v k • (1 : Matrix (Fin n) (Fin n) ℝ) i k := by
    ext i
    simp [Matrix.one_apply]
  conv_lhs => arg 2; rw [hv, Matrix.det_updateCol_sum, Matrix.det_one]
  simp [v]

/-- Change of variables derives the radial density; it is not an assumed measure identity. -/
theorem radialBlowup_integrableOn_image_iff {n : ℕ} (j : Fin n) {D : Set (Fin n → ℝ)}
    (hD : MeasurableSet D) (hpos : ∀ z ∈ D, 0 < z j) (g : (Fin n → ℝ) → ℝ) :
    IntegrableOn g (radialBlowup j '' D) volume ↔
      IntegrableOn (fun z => z j ^ (n - 1) * g (radialBlowup j z)) D volume := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hD
    (fun z _ => (radialBlowup_hasFDerivAt j z).hasFDerivWithinAt)
    ((radialBlowup_injOn j).mono (fun z hz => (hpos z hz).ne'))]
  apply integrableOn_congr_fun _ hD
  intro z hz
  dsimp only
  rw [radialBlowupDeriv_det, abs_of_nonneg (pow_nonneg (hpos z hz).le _), smul_eq_mul]

/-- Radial scaling exposes the angular Fermat polynomial without changing effective weights. -/
theorem radialBlowup_eq_smul {n : ℕ} (j : Fin n) (z : Fin n → ℝ) :
    radialBlowup j z = z j • Function.update z j 1 := by
  ext i
  by_cases hi : i = j <;> simp [radialBlowup, hi, Function.update_of_ne]

/-- Exact pullback of the reduced loss in a projective radial patch. -/
theorem cancellationModel_radialBlowup {n : ℕ} (r : ℕ) (j : Fin n) (z : Fin n → ℝ) :
    cancellationModel r (radialBlowup j z) =
      z j ^ (2 * r) * (weightPowerSum r (Function.update z j 1) ^ 2 +
        z j ^ (2 * r) * weightSquareSum r (Function.update z j 1) ^ 2) := by
  have hQ (a : ℝ) (w : Fin n → ℝ) : weightSquareSum r (a • w) =
      a ^ (2 * r) * weightSquareSum r w := by
    simpa only [weightSquareSum_eq, sumEvenPowers] using sumEvenPowers_smul n r a w
  rw [radialBlowup_eq_smul, cancellationModel, weightPowerSum_smul, hQ]
  simp only [mul_pow, ← pow_mul, Nat.mul_comm r 2]
  ring

/-- The inverse is smooth wherever the radius is nonzero. -/
theorem radialBlowupInverse_contDiffOn {n : ℕ} (j : Fin n) :
    ContDiffOn ℝ 1 (radialBlowupInverse j) {w : Fin n → ℝ | w j ≠ 0} := by
  intro w hw
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_pi.mpr
  intro i
  by_cases hi : i = j
  · simpa [radialBlowupInverse, hi] using contDiffAt_apply ℝ (fun _ : Fin n => ℝ) j w
  · simpa [radialBlowupInverse, hi] using
      (contDiffAt_apply ℝ (fun _ : Fin n => ℝ) i w).fun_div
        (contDiffAt_apply ℝ (fun _ : Fin n => ℝ) j w) hw

/-- Uniform angular bounds include the fixed coordinate, so Q is bounded away from zero. -/
theorem radialBlowup_angular_Q_bounds {n : ℕ} (r : ℕ) (j : Fin n) (z : Fin n → ℝ)
    (hz : ∀ i, i ≠ j → |z i| ≤ 1) :
    1 ≤ weightSquareSum r (Function.update z j 1) ∧
      weightSquareSum r (Function.update z j 1) ≤ n := by
  constructor
  · have h := Finset.single_le_sum (fun i _ => sq_nonneg ((Function.update z j 1 i) ^ r))
      (Finset.mem_univ j)
    simpa [weightSquareSum] using h
  · unfold weightSquareSum
    calc
      (∑ i, (Function.update z j 1 i ^ r) ^ 2) ≤ ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i = j
        · simp [hi]
        · rw [Function.update_of_ne hi]
          have hp : |z i ^ r| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hz i hi)
          have := pow_le_pow_left₀ (abs_nonneg (z i ^ r)) hp 2
          simpa only [sq_abs, one_pow] using this
      _ = n := by simp

/-- The transformed loss is uniformly comparable to the radial/angular normal form. -/
theorem cancellationModel_radialBlowup_bounds {n : ℕ} (r : ℕ) (j : Fin n) (z : Fin n → ℝ)
    (hz : ∀ i, i ≠ j → |z i| ≤ 1) :
    let H := z j ^ (2 * r) * (weightPowerSum r (Function.update z j 1) ^ 2 + z j ^ (2 * r))
    H ≤ cancellationModel r (radialBlowup j z) ∧
      cancellationModel r (radialBlowup j z) ≤ (n + 1 : ℝ) ^ 2 * H := by
  dsimp only
  obtain ⟨hl, hu⟩ := radialBlowup_angular_Q_bounds r j z hz
  have hp : 0 ≤ z j ^ (2 * r) := by rw [pow_mul]; positivity
  have hq0 := weightSquareSum_nonneg r n (Function.update z j 1)
  have hq1 : 1 ≤ weightSquareSum r (Function.update z j 1) ^ 2 := by nlinarith
  have hq2 : weightSquareSum r (Function.update z j 1) ^ 2 ≤ (n + 1 : ℝ) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hn : (1 : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  rw [cancellationModel_radialBlowup]
  constructor
  · exact mul_le_mul_of_nonneg_left (add_le_add_right (by nlinarith :
        z j ^ (2 * r) ≤ z j ^ (2 * r) * weightSquareSum r (Function.update z j 1) ^ 2) _) hp
  · have hS := sq_nonneg (weightPowerSum r (Function.update z j 1))
    calc
      _ ≤ z j ^ (2 * r) * ((n + 1 : ℝ) ^ 2 *
          (weightPowerSum r (Function.update z j 1) ^ 2 + z j ^ (2 * r))) := by
        apply mul_le_mul_of_nonneg_left _ hp
        nlinarith [mul_le_mul_of_nonneg_left hq2 hp, mul_le_mul_of_nonneg_right hn hS]
      _ = _ := by ring

/-- Exact integrability reduction on a positive projective cone patch, with the derived
radial measure and uniform angular Q comparison. It stops before transverse straightening. -/
theorem cancellationModel_on_radial_patch_iff {n : ℕ} (r : ℕ) (j : Fin n)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D)
    (hpos : ∀ z ∈ D, 0 < z j) (hangular : ∀ z ∈ D, ∀ i, i ≠ j → |z i| ≤ 1) (s : ℝ) :
    IntegrableOn (fun w => cancellationModel r w ^ (-s)) (radialBlowup j '' D) volume ↔
      IntegrableOn (fun z => (z j ^ (2 * r) *
        (weightPowerSum r (Function.update z j 1) ^ 2 + z j ^ (2 * r))) ^ (-s)) D
        (volume.withDensity (fun z => ENNReal.ofReal (z j ^ (n - 1)))) := by
  let ν := volume.withDensity (fun z : Fin n → ℝ => ENNReal.ofReal (z j ^ (n - 1)))
  have hchange : IntegrableOn (fun w => cancellationModel r w ^ (-s))
      (radialBlowup j '' D) volume ↔
      IntegrableOn (fun z => cancellationModel r (radialBlowup j z) ^ (-s)) D ν := by
    rw [radialBlowup_integrableOn_image_iff j hD hpos]
    change _ ↔ IntegrableOn _ D (volume.withDensity
      (fun z : Fin n → ℝ => (Real.toNNReal (z j ^ (n - 1)) : ENNReal)))
    rw [integrableOn_withDensity_iff_weighted hD (by fun_prop)]
    apply integrableOn_congr_fun _ hD
    intro z hz
    dsimp only
    rw [Real.coe_toNNReal _ (pow_nonneg (hpos z hz).le _)]
  rw [hchange]
  apply integrableOn_rpow_iff_of_comparable_all
    (by unfold weightPowerSum; fun_prop)
    (by unfold cancellationModel weightPowerSum weightSquareSum radialBlowup; fun_prop)
    _ (by norm_num : (0 : ℝ) < 1) (by positivity : (0 : ℝ) < (n + 1 : ℝ) ^ 2) _ _ s
  · filter_upwards [ae_restrict_mem hD] with z hz
    have hx : 0 < z j := hpos z hz
    positivity
  · filter_upwards [ae_restrict_mem hD] with z hz
    simpa only [one_mul] using (cancellationModel_radialBlowup_bounds r j z (hangular z hz)).1
  · filter_upwards [ae_restrict_mem hD] with z hz
    exact (cancellationModel_radialBlowup_bounds r j z (hangular z hz)).2

/-- A point with a positive dominating coordinate belongs to its explicit cone chart. -/
theorem radialBlowup_dominating_representation {n : ℕ} (j : Fin n) (w : Fin n → ℝ)
    (hj : 0 < w j) (hdom : ∀ i, |w i| ≤ w j) :
    ∃ z : Fin n → ℝ, z j = w j ∧ (∀ i, i ≠ j → |z i| ≤ 1) ∧ radialBlowup j z = w := by
  refine ⟨radialBlowupInverse j w, by simp [radialBlowupInverse], ?_,
    radialBlowup_right_inverse j w hj.ne'⟩
  intro i hi
  simp only [radialBlowupInverse, ite_eq_right hi, abs_div, abs_of_pos hj]
  exact (div_le_one hj).mpr (hdom i)

/-- All nonzero points of a raw parameter ball are covered by finitely many signed
projective cone patches. No globally defined angular chart is used. -/
theorem signed_radialBlowup_cover {n : ℕ} (ε : ℝ) (w : Fin n → ℝ)
    (hw : w ∈ Metric.ball 0 ε) (hne : w ≠ 0) :
    ∃ j : Fin n, ∃ z : Fin n → ℝ, 0 < z j ∧ z j < ε ∧
      (∀ i, i ≠ j → |z i| ≤ 1) ∧ (w = radialBlowup j z ∨ w = -radialBlowup j z) := by
  obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
    by_contra! hn
    exact hne (funext hn)
  let : Nonempty (Fin n) := ⟨k⟩
  obtain ⟨j, _, hmax⟩ := Finset.exists_max_image univ (fun i => |w i|) univ_nonempty
  have hmax' (i : Fin n) : |w i| ≤ |w j| := hmax i (mem_univ i)
  have habs : 0 < |w j| := lt_of_lt_of_le (abs_pos.mpr hk) (hmax' k)
  have heps : |w j| < ε := (show |w j| ≤ ‖w‖ by simpa using norm_le_pi_norm w j).trans_lt
    (mem_ball_zero_iff.mp hw)
  by_cases hj : 0 < w j
  · have hd (i : Fin n) : |w i| ≤ w j := by simpa only [abs_of_pos hj] using hmax' i
    obtain ⟨z, hzj, hz, hwz⟩ := radialBlowup_dominating_representation j w hj hd
    exact ⟨j, z, hzj.symm ▸ hj, by simpa [hzj, abs_of_pos hj] using heps, hz, Or.inl hwz.symm⟩
  · have hjneg : w j < 0 := by have hn := abs_pos.mp habs; exact lt_of_le_of_ne (le_of_not_gt hj) hn
    have hd (i : Fin n) : |(-w) i| ≤ (-w) j := by
      simpa only [Pi.neg_apply, abs_neg, abs_of_neg hjneg] using hmax' i
    obtain ⟨z, hzj, hz, hwz⟩ := radialBlowup_dominating_representation j (-w) (by simpa using neg_pos.mpr hjneg) hd
    refine ⟨j, z, by rw [hzj]; simpa using neg_pos.mpr hjneg, ?_, hz, Or.inr ?_⟩
    · simpa only [hzj, Pi.neg_apply, abs_of_neg hjneg] using heps
    · rw [hwz, neg_neg]

end ResidualSLT
