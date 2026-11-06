module
public import ResidualSLT.OffCriticalLaplace

/-! Radial Laplace bounds for the depth-one case, where no cancellation cone exists. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Metric Filter

/-- The radial Gaussian has the expected power on every fixed positive interval. -/
theorem radial_interval_laplace_order (r : ℕ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    HasPowerLaplaceOrder (1/(2*(r:ℝ))) (fun N => ∫ x : ℝ in Ioo 0 ε,
      Real.exp (-N*x^(2*r))) := by
  constructor
  · have hl := powerWeightedBox_lower 1 r 0 0 (by omega) hr le_rfl ε 1 hε zero_lt_one
    norm_num only [Nat.cast_one,Nat.cast_zero,add_zero] at hl
    apply hl.mono
    filter_upwards [eventually_ge_atTop (0:ℝ)] with N hN
    have hi := powerWeighted_integrable 1 r 0 N ε 0 1
    rw [Measure.volume_eq_prod] at hi
    unfold powerWeightedBox
    rw [Measure.volume_eq_prod,setIntegral_prod _ hi]
    have hrad : IntegrableOn (fun x : ℝ => Real.exp (-N*x^(2*r))) (Ioo 0 ε) volume :=
      ((by fun_prop : Continuous (fun x : ℝ => Real.exp (-N*x^(2*r)))).continuousOn.integrableOn_compact
        isCompact_Icc).mono_set Ioo_subset_Icc_self
    apply setIntegral_mono_on (by rw [IntegrableOn,← Measure.prod_restrict] at hi; exact hi.integral_prod_left)
      hrad measurableSet_Ioo
    intro x hx
    calc
      _ ≤ ∫ t : ℝ in Ioo 0 1, Real.exp (-N*x^(2*r)) := by
        apply setIntegral_mono_on
          (((by unfold powerWeightedKernel; fun_prop : Continuous (fun t : ℝ => powerWeightedKernel 1 r 0 N (x,t))).continuousOn.integrableOn_compact
            isCompact_Icc).mono_set Ioo_subset_Icc_self)
          (integrableOn_const (by simp) (by simp)) measurableSet_Ioo
        intro t _
        simp only [powerWeightedKernel,Nat.sub_self,pow_zero,one_mul,mul_zero]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (mul_nonneg hN (pow_nonneg hx.1.le (2*r))) (sq_nonneg t)]
      _ = _ := by simp
  · simpa using radialGamma_laplace_upper 1 r (by omega) hr ε

/-- Lebesgue volume on Fin 1 is transported exactly to the real line. -/
theorem fin_one_norm_laplace_order (r : ℕ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    HasPowerLaplaceOrder (1/(2*(r:ℝ))) (fun N => ∫ w : Fin 1 → ℝ in ball 0 ε,
      Real.exp (-N*‖w‖^(2*r))) := by
  have hn (w : Fin 1 → ℝ) : ‖w‖ = |w 0| := by
    have he : w = fun _ => w 0 := funext (fun i => congrArg w (Subsingleton.elim i 0))
    rw [he]
    simp
  have heq (N : ℝ) : (∫ w : Fin 1 → ℝ in ball 0 ε, Real.exp (-N*‖w‖^(2*r))) =
      2*(∫ x : ℝ in Ioo 0 ε, Real.exp (-N*x^(2*r))) := by
    let e := MeasurableEquiv.funUnique (Fin 1) ℝ
    have hset : ball (0 : Fin 1 → ℝ) ε = e ⁻¹' Ioo (-ε) ε := by
      ext w
      simp only [mem_ball_zero_iff,hn,abs_lt,mem_preimage,mem_Ioo]
      rfl
    have hp (x : ℝ) : |x|^(2*r) = x^(2*r) := by
      rw [show 2*r = r*2 by omega,pow_mul,pow_mul,← abs_pow,sq_abs]
    simp_rw [hn,hp]
    rw [hset]
    have ht := (volume_preserving_funUnique (Fin 1) ℝ).setIntegral_preimage_emb e.measurableEmbedding
      (fun x : ℝ => Real.exp (-N*x^(2*r))) (Ioo (-ε) ε)
    change (∫ w : Fin 1 → ℝ in e ⁻¹' Ioo (-ε) ε, Real.exp (-N*w 0^(2*r))) =
      (∫ x : ℝ in Ioo (-ε) ε, Real.exp (-N*x^(2*r))) at ht
    rw [ht]
    exact integral_even_Ioo _ (by fun_prop) (fun x => by rw [Even.neg_pow (even_two_mul r)]) ε hε
  constructor
  · simpa only [heq] using (radial_interval_laplace_order r hr ε hε).1.const_mul 2 (by norm_num)
  · simpa only [heq] using (radial_interval_laplace_order r hr ε hε).2.const_mul 2 (by norm_num)

/-- The depth-one Fermat norm model is comparable to its ordinary radial term. -/
theorem one_fermat_laplace_order (r : ℕ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasPowerLaplaceOrder (1/(2*(r:ℝ))) (fun N => ∫ w : Fin 1 → ℝ in ball 0 ε,
      Real.exp (-N*homogeneousConeLoss (weightPowerSum r) (r+r) w)) := by
  let K := fun w : Fin 1 → ℝ => ‖w‖^(2*r)
  let J := homogeneousConeLoss (@weightPowerSum r 1) (r+r)
  have hcK : Continuous K := by unfold K; fun_prop
  have hcJ : Continuous J := by unfold J homogeneousConeLoss weightPowerSum; fun_prop
  apply power_laplace_order_of_comparable volume (ball 0 ε) K J
    (fun N => ((by fun_prop : Continuous (fun w => Real.exp (-N*K w))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall)
    (fun N => ((by fun_prop : Continuous (fun w => Real.exp (-N*J w))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall)
    1 2 zero_lt_one (by norm_num) _ (fin_one_norm_laplace_order r hr ε hε)
  filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
  have hn : ‖w‖ = |w 0| := by
    have he : w = fun _ => w 0 := funext (fun i => congrArg w (Subsingleton.elim i 0))
    rw [he]; simp
  have hs : weightPowerSum r w^2 = ‖w‖^(2*r) := by
    simp only [weightPowerSum,Fin.sum_univ_one,hn]
    rw [show 2*r=r*2 by omega,pow_mul,← abs_pow,sq_abs]
  have hp : ‖w‖^(2*(r+r)) = (‖w‖^(2*r))^2 := by rw [← pow_mul]; congr 1; omega
  have hb : ‖w‖^(2*r) ≤ 1 := pow_le_one₀ (norm_nonneg _) ((mem_ball_zero_iff.mp hw).le.trans hε1)
  have hpos : 0 ≤ ‖w‖^(2*r) := pow_nonneg (norm_nonneg _) _
  dsimp [K,J,homogeneousConeLoss]
  rw [hs,hp]
  constructor <;> nlinarith

end ResidualSLT
