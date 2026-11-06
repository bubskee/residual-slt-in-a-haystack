module
public import ResidualSLT.LossComparison
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Radial thresholds and positive homogeneous losses in arbitrary finite dimension.
The measure and norm ball are explicit; no multiplicity statement is made. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Set Metric NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Exact radial criterion, including divergence, for any norm and additive Haar measure. -/
theorem norm_rpow_integrableOn_ball_iff (ε : ℝ) (hε : 0 < ε) (p : ℝ) :
    IntegrableOn (fun x : E => ‖x‖ ^ p) (ball 0 ε) μ ↔
      -(Module.finrank ℝ E : ℝ) < p := by
  rw [integrableOn_fun_norm_addHaar μ (f := fun y : ℝ => y ^ p)]
  have hd : 0 < Module.finrank ℝ E := Module.finrank_pos
  have heq : EqOn (fun y : ℝ => y ^ (Module.finrank ℝ E - 1) • y ^ p)
      (fun y => y ^ ((Module.finrank ℝ E : ℝ) - 1 + p)) (Ioo 0 ε) := by
    intro y hy
    dsimp only
    rw [smul_eq_mul, ← Real.rpow_natCast, ← Real.rpow_add hy.1]
    rw [Nat.cast_sub (by omega : 1 ≤ Module.finrank ℝ E), Nat.cast_one]
  rw [integrableOn_congr_fun heq measurableSet_Ioo,
    intervalIntegral.integrableOn_Ioo_rpow_iff hε]
  constructor <;> intro h <;> linarith

/-- A norm power of degree m has threshold dimension/m, for every real exponent s. -/
theorem normPower_integrableOn_ball_iff (m : ℕ) (hm : 0 < m)
    (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    IntegrableOn (fun x : E => (‖x‖ ^ m) ^ (-s)) (ball 0 ε) μ ↔
      s < (Module.finrank ℝ E : ℝ) / m := by
  have heq : (fun x : E => (‖x‖ ^ m) ^ (-s)) = fun x => ‖x‖ ^ (-(m : ℝ) * s) := by
    funext x
    rw [← Real.rpow_natCast_mul (norm_nonneg x)]
    congr 1
    ring
  rw [heq, norm_rpow_integrableOn_ball_iff μ ε hε, lt_div_iff₀ (by positivity : (0 : ℝ) < m)]
  constructor <;> intro h <;> nlinarith

/-- Radial threshold with a.e. positivity; the origin is Haar-null. -/
theorem normPower_threshold (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) :
    HasIntegrabilityThresholdOn (fun x : E => ‖x‖ ^ m) (ball 0 ε) μ
      ((Module.finrank ℝ E : ℝ) / m) := by
  constructor
  · filter_upwards [ae_restrict_of_ae (μ.ae_ne (0 : E))] with x hx
    exact pow_pos (norm_pos_iff.mpr hx) m
  · intro s _
    exact normPower_integrableOn_ball_iff μ m hm ε hε s

omit [MeasurableSpace E] [BorelSpace E] in
/-- Compactness of the unit sphere supplies uniform bounds; no bound is assumed. -/
theorem positive_homogeneous_bounds {Q : E → ℝ} (m : ℕ) (hm : 0 < m)
    (hQ : Continuous Q) (hpos : ∀ x, x ≠ 0 → 0 < Q x)
    (hhom : ∀ (a : ℝ), 0 ≤ a → ∀ x, Q (a • x) = a ^ m * Q x) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c * ‖x‖ ^ m ≤ Q x ∧ Q x ≤ C * ‖x‖ ^ m := by
  have hs : (sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hs hQ.continuousOn
  obtain ⟨v, hv, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hs hQ.continuousOn
  have hn (x : E) (hx : x ∈ sphere (0 : E) 1) : x ≠ 0 := by
    intro he
    simp [he] at hx
  refine ⟨Q u, Q v, hpos u (hn u hu), hpos v (hn v hv), ?_⟩
  intro x
  by_cases hx : x = 0
  · have hzero := hhom 0 (le_refl 0) (0 : E)
    simp only [zero_smul, zero_pow (by omega : m ≠ 0), zero_mul] at hzero
    simp [hx, hzero, hm.ne']
  · have hnx : normalize x ∈ sphere (0 : E) 1 := by
      simpa only [mem_sphere_zero_iff_norm] using norm_normalize hx
    have heq : Q x = ‖x‖ ^ m * Q (normalize x) := by
      rw [← hhom ‖x‖ (norm_nonneg x), norm_smul_normalize]
    rw [heq]
    constructor
    · simpa [mul_comm] using mul_le_mul_of_nonneg_left (hmin hnx) (pow_nonneg (norm_nonneg x) m)
    · simpa [mul_comm] using mul_le_mul_of_nonneg_left (hmax hnx) (pow_nonneg (norm_nonneg x) m)

/-- Every continuous, positive-away-from-zero homogeneous loss has the radial threshold. -/
theorem positive_homogeneous_threshold {Q : E → ℝ} (m : ℕ) (hm : 0 < m)
    (hQ : Continuous Q) (hpos : ∀ x, x ≠ 0 → 0 < Q x)
    (hhom : ∀ (a : ℝ), 0 ≤ a → ∀ x, Q (a • x) = a ^ m * Q x)
    (ε : ℝ) (hε : 0 < ε) :
    HasIntegrabilityThresholdOn Q (ball 0 ε) μ ((Module.finrank ℝ E : ℝ) / m) := by
  obtain ⟨c, C, hc, hC, hb⟩ := positive_homogeneous_bounds m hm hQ hpos hhom
  apply (normPower_threshold μ m hm ε hε).of_comparable
    (continuous_norm.pow m).measurable.aemeasurable hQ.measurable.aemeasurable hc hC
  · exact Filter.Eventually.of_forall (fun x => (hb x).1)
  · exact Filter.Eventually.of_forall (fun x => (hb x).2)
/-- The homogeneous criterion holds for all real exponents, including negative s. -/
theorem positive_homogeneous_integrableOn_iff {Q : E → ℝ} (m : ℕ) (hm : 0 < m)
    (hQ : Continuous Q) (hpos : ∀ x, x ≠ 0 → 0 < Q x)
    (hhom : ∀ (a : ℝ), 0 ≤ a → ∀ x, Q (a • x) = a ^ m * Q x)
    (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    IntegrableOn (fun x => Q x ^ (-s)) (ball 0 ε) μ ↔
      s < (Module.finrank ℝ E : ℝ) / m := by
  obtain ⟨c, C, hc, hC, hb⟩ := positive_homogeneous_bounds m hm hQ hpos hhom
  rw [integrableOn_rpow_iff_of_comparable_all (continuous_norm.pow m).measurable.aemeasurable
    hQ.measurable.aemeasurable (normPower_threshold μ m hm ε hε).1 hc hC
    (Filter.Eventually.of_forall (fun x => (hb x).1))
    (Filter.Eventually.of_forall (fun x => (hb x).2)) s]
  exact normPower_integrableOn_ball_iff μ m hm ε hε s
end ResidualSLT
