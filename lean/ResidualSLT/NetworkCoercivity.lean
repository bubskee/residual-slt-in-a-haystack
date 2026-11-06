module
public import ResidualSLT.SmallRawFiber

/-! Global compact sublevels and a positive loss gap outside any open fiber neighborhood. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset Set MeasureTheory Metric

theorem network_raw_norm_le_coefficients (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L) (w : Fin L → ℝ) :
    ‖w‖ ≤ 1+‖networkCoefficients r w‖^2+‖networkCoefficients r w‖ := by
  let M := ‖networkCoefficients r w‖
  have hM : 0 ≤ M := norm_nonneg _
  have hS : |weightPowerSum r w| ≤ M := by
    have hh := residual_coeff_le_norm r hr L hL w r
    rw [(raw_residual_coefficients r hr (zeroExtend w) L).1] at hh
    simpa [weightPowerSum,← Fin.sum_univ_eq_sum_range,zeroExtend] using hh
  have hB := residual_coeff_le_norm r hr L hL w (2*r-1)
  have hrel := residual_second_SQ r hr L w
  have hr' : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hQ : weightSquareSum r w ≤ M^2+M := by
    have hs : weightPowerSum r w^2 ≤ M^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (weightPowerSum r w)) hS 2
    have hb : -(M) ≤ (network r (fun i => zeroExtend w i^r) L-X).coeff (2*r-1) := (abs_le.mp hB).1
    have hR : (r:ℝ)*weightSquareSum r w ≤ (r:ℝ)*(M^2+M) := by
      nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (r:ℝ)),mul_nonneg (sub_nonneg.mpr hr') hM]
    exact le_of_mul_le_mul_left hR (by positivity)
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 1+M^2+M)).mpr
  intro i
  change |w i| ≤ _
  by_cases hi : |w i| ≤ 1
  · nlinarith
  · have hi' : 1 ≤ |w i| := (lt_of_not_ge hi).le
    have hp : |w i| ≤ |w i|^(2*r) := le_self_pow₀ hi' (by omega)
    have hsum : |w i|^(2*r) ≤ weightSquareSum r w := by
      have he : |w i|^(2*r) = (w i^r)^2 := by
        rw [Nat.mul_comm 2 r,pow_mul,← abs_pow,sq_abs]
      rw [he]
      exact Finset.single_le_sum (f := fun j : Fin L => (w j^r)^2)
        (fun j _ => sq_nonneg _) (mem_univ i)
    exact (hp.trans hsum).trans (by linarith)

theorem networkTargetLoss_sublevel_bounded (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (t : Fin L → ℝ) (B : ℝ) :
    ∃ R : ℝ, ∀ w : Fin L → ℝ, networkTargetLoss μ r t w ≤ B → ‖w‖ ≤ R := by
  obtain ⟨a,A,ha,_,hb⟩ := networkTargetLoss_coefficient_bounds μ r L hr hL hμ
  let H := |B|/a+1+‖sparseNetworkCoefficients r t‖
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨1+H^2+H,?_⟩
  intro w hw
  have hd : ‖networkTargetCoefficients r t w‖^2 ≤ |B|/a :=
    (le_div_iff₀ ha).mpr (by nlinarith [(hb t w).1,le_abs_self B])
  have hn : ‖networkTargetCoefficients r t w‖ ≤ |B|/a+1 := by
    have hp : 0 ≤ |B|/a := by positivity
    nlinarith [sq_nonneg (‖networkTargetCoefficients r t w‖-1)]
  have hM : ‖networkCoefficients r w‖ ≤ H := by
    rw [← sparseNetworkCoefficients_norm r L hr]
    have hh := norm_sub_le (sparseNetworkCoefficients r w-sparseNetworkCoefficients r t) (-sparseNetworkCoefficients r t)
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at hh
    apply hh.trans
    dsimp [H,networkTargetCoefficients] at *
    linarith
  have hh := network_raw_norm_le_coefficients r L hr hL w
  have hs := pow_le_pow_left₀ (norm_nonneg (networkCoefficients r w)) hM 2
  linarith

theorem networkTargetLoss_isCompact_sublevel (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (t : Fin L → ℝ) (B : ℝ) :
    IsCompact {w : Fin L → ℝ | networkTargetLoss μ r t w ≤ B} := by
  obtain ⟨R,hR⟩ := networkTargetLoss_sublevel_bounded μ r L hr hL hμ t B
  exact (isCompact_closedBall (0 : Fin L → ℝ) R).of_isClosed_subset
    (isClosed_le (networkTargetLoss_continuous μ r L hr hL hμ t) continuous_const)
    (fun w hw => mem_closedBall_zero_iff.mpr (hR w hw))

/-- A fixed positive gap holds on the entire complement, including the unbounded tail. -/
theorem networkTargetLoss_gap_outside (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (t : Fin L → ℝ)
    (U : Set (Fin L → ℝ)) (hU : IsOpen U) (hzero : ∀ w, networkTargetLoss μ r t w=0 → w∈U) :
    ∃ b : ℝ, 0 < b ∧ ∀ w, w∉U → b ≤ networkTargetLoss μ r t w := by
  let K := networkTargetLoss μ r t
  let S := {w : Fin L → ℝ | K w ≤ 1} ∩ Uᶜ
  have hS : IsCompact S := (networkTargetLoss_isCompact_sublevel μ r L hr hL hμ t 1).inter_right hU.isClosed_compl
  by_cases he : S.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hS.exists_isMinOn he (networkTargetLoss_continuous μ r L hr hL hμ t).continuousOn
    have hxpos : 0 < K x := by
      have hn : 0 ≤ K x := integral_nonneg (fun _ => sq_nonneg _)
      have hz : K x ≠ 0 := fun hz => hx.2 (hzero x hz)
      exact lt_of_le_of_ne hn (Ne.symm hz)
    refine ⟨min 1 (K x),lt_min zero_lt_one hxpos,?_⟩
    intro w hw
    by_cases hK : K w ≤ 1
    · exact (min_le_right _ _).trans (hmin ⟨hK,hw⟩)
    · exact (min_le_left _ _).trans (le_of_not_ge hK)
  · refine ⟨1,zero_lt_one,?_⟩
    intro w hw
    by_contra hh
    exact he ⟨w,le_of_not_ge hh,hw⟩

end ResidualSLT
