module
public import ResidualSLT.OneActiveLossComparison
public import ResidualSLT.OneActiveModelLaplace

/-! Relate the retained quantities to the two already-certified identity losses. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset MeasureTheory Filter Metric

@[expose] def groupSecondCoefficient (r n : ℕ) (w : Fin n → ℝ) : ℝ :=
  (graded r (zeroExtend (fun i => w i^r)) n).coeff 2
@[expose] def groupRetainedSquare (r n : ℕ) (w : Fin n → ℝ) : ℝ :=
  weightPowerSum r w^2+groupSecondCoefficient r n w^2

/-- Empty groups contribute zero loss; all other groups admit the same retained comparison. -/
theorem identityReferenceLoss_retained_comparison (r n : ℕ) (hr : 2 ≤ r) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ᶠ w : Fin n → ℝ in nhds 0,
      a*groupRetainedSquare r n w ≤ identityReferenceLoss r n w ∧
      identityReferenceLoss r n w ≤ A*groupRetainedSquare r n w := by
  by_cases hn : n = 0
  · subst n
    refine ⟨1,1,by norm_num,by norm_num,Filter.Eventually.of_forall (fun w => ?_)⟩
    simp [groupRetainedSquare,weightPowerSum,groupSecondCoefficient,graded,
      identityReferenceLoss,networkPopulationLoss,networkSquaredError,network,coeff_one]
  · have hn0 : 0 < n := by omega
    let μ := atomicInput (fun i : Fin (networkFeatureCount r n) => (i.val:ℝ)+1)
    have hμ := sparse_gram_of_contiguous μ r n hr (network_atomic_gram r n)
    obtain ⟨a,A,ha,hA,hb⟩ := sparse_network_loss_coefficient_bounds μ r n hr hn0 hμ
    let D := signedRemainderEnvelope r n*n
    have hD : 0 ≤ D := by dsimp [D]; positivity [signedRemainderEnvelope_nonneg r n]
    refine ⟨a/2,A*(2*(1+D)^2),by positivity,by positivity,?_⟩
    have hSc : Tendsto (fun w : Fin n → ℝ => |weightPowerSum r w|) (nhds 0) (nhds 0) := by
      have hc : Continuous (fun w : Fin n → ℝ => |weightPowerSum r w|) := by unfold weightPowerSum; fun_prop
      simpa [weightPowerSum,show r ≠ 0 by omega] using hc.tendsto 0
    filter_upwards [Metric.ball_mem_nhds (0:Fin n → ℝ) zero_lt_one,
      hSc.eventually (Iio_mem_nhds zero_lt_one)] with w hw hS
    have hs := (signed_network_coefficients_lower r hr n hn0 w hw).1
    have hB : |groupSecondCoefficient r n w| ≤ ‖networkCoefficients r w‖ := by
      have hh := residual_coeff_le_norm r hr n hn0 w (2*r-1)
      simpa only [coeff_sub,coeff_X,ite_eq_right (by omega : 1 ≠ 2*r-1),sub_zero,
        show 2*r-1=2*(r-1)+1 by omega,ite_eq_right (by omega : 1 ≠ 2*(r-1)+1),network_coeff_graded r hr,groupSecondCoefficient,
        zeroExtend_pow n r (by omega)] using hh
    have hQ : weightSquareSum r w ≤ |weightPowerSum r w|+|groupSecondCoefficient r n w| := by
      simpa only [weightSquareSum,weightPowerSum,groupSecondCoefficient] using
        effective_sum_sq_le_retained r n hr (fun i => w i^r) hS.le
    have hu := signed_network_coefficients_upper r hr n hn0 w hw
    have hu' : ‖networkCoefficients r w‖ ≤
        (1+D)*(|weightPowerSum r w|+|groupSecondCoefficient r n w|) := by
      change ‖networkCoefficients r w‖ ≤ |weightPowerSum r w|+D*weightSquareSum r w at hu
      nlinarith [mul_le_mul_of_nonneg_left hQ hD,abs_nonneg (groupSecondCoefficient r n w)]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hu' 2
    have hsum : (|weightPowerSum r w|+|groupSecondCoefficient r n w|)^2 ≤
        2*groupRetainedSquare r n w := by
      unfold groupRetainedSquare
      nlinarith [sq_nonneg (|weightPowerSum r w|-|groupSecondCoefficient r n w|),
        sq_abs (weightPowerSum r w),sq_abs (groupSecondCoefficient r n w)]
    have hs2 := pow_le_pow_left₀ (abs_nonneg _) hs 2
    have hB2 := pow_le_pow_left₀ (abs_nonneg _) hB 2
    rw [sq_abs] at hs2 hB2
    have hupper : ‖networkCoefficients r w‖^2 ≤ (2*(1+D)^2)*groupRetainedSquare r n w := by
      rw [mul_pow] at hsq
      nlinarith [mul_le_mul_of_nonneg_left hsum (sq_nonneg (1+D))]
    obtain ⟨hlo,hup⟩ := hb w
    change a*‖networkCoefficients r w‖^2 ≤ identityReferenceLoss r n w at hlo
    change identityReferenceLoss r n w ≤ A*‖networkCoefficients r w‖^2 at hup
    constructor
    · have hlow : groupRetainedSquare r n w ≤ 2*‖networkCoefficients r w‖^2 := by
        unfold groupRetainedSquare
        linarith
      nlinarith [mul_le_mul_of_nonneg_left hlow ha.le]
    · nlinarith [mul_le_mul_of_nonneg_left hupper hA.le]

/-- The product comparison model and the full retained vector have equivalent losses. -/
theorem oneActive_model_retained_comparison (r p q : ℕ) (hr : 2 ≤ r) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ᶠ w : OneActiveAux p q in nhds 0,
      a*‖oneActiveRetained r p q w‖^2 ≤ oneActiveComparisonLoss r p q w ∧
      oneActiveComparisonLoss r p q w ≤ A*‖oneActiveRetained r p q w‖^2 := by
  obtain ⟨a,A,ha,hA,hp⟩ := identityReferenceLoss_retained_comparison r p hr
  obtain ⟨b,B,hb,hB,hq⟩ := identityReferenceLoss_retained_comparison r q hr
  let c := min 1 (min a b)
  let C := max 1 (max A B)
  have hc : 0 < c := lt_min zero_lt_one (lt_min ha hb)
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨c,C*5,hc,by positivity,?_⟩
  have hpre : Tendsto (fun w : OneActiveAux p q => w.2.1) (nhds 0) (nhds 0) :=
    (continuous_fst.comp continuous_snd).tendsto 0
  have hpost : Tendsto (fun w : OneActiveAux p q => w.2.2) (nhds 0) (nhds 0) :=
    (continuous_snd.comp continuous_snd).tendsto 0
  have hp' := hpre.eventually hp
  have hq' := hpost.eventually hq
  filter_upwards [hp',hq'] with w hpw hqw
  have hnorm := finite_sum_sq_bounds 5 (oneActiveRetained r p q w)
  have he : (∑ i, oneActiveRetained r p q w i^2) =
      w.1^2+groupRetainedSquare r p w.2.1+groupRetainedSquare r q w.2.2 := by
    simp [oneActiveRetained,Fin.sum_univ_succ,groupRetainedSquare,weightPowerSum,groupSecondCoefficient]
    ring
  rw [he] at hnorm
  norm_num only [Nat.cast_ofNat] at hnorm
  have hpp : 0 ≤ groupRetainedSquare r p w.2.1 := by unfold groupRetainedSquare; positivity
  have hqp : 0 ≤ groupRetainedSquare r q w.2.2 := by unfold groupRetainedSquare; positivity
  have hc1 : c ≤ 1 := min_le_left _ _
  have hca : c ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hcb : c ≤ b := (min_le_right _ _).trans (min_le_right _ _)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCA : A ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCB : B ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  dsimp only [oneActiveComparisonLoss]
  constructor
  · have hm := mul_le_mul_of_nonneg_left hnorm.1 hc.le
    nlinarith [mul_le_mul_of_nonneg_right hc1 (sq_nonneg w.1),
      mul_le_mul_of_nonneg_right hca hpp,mul_le_mul_of_nonneg_right hcb hqp]
  · have hm := mul_le_mul_of_nonneg_left hnorm.2 hC.le
    nlinarith [mul_le_mul_of_nonneg_right hC1 (sq_nonneg w.1),
      mul_le_mul_of_nonneg_right hCA hpp,mul_le_mul_of_nonneg_right hCB hqp]

end ResidualSLT
