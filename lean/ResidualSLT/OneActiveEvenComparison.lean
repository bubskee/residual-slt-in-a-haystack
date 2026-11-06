module
public import ResidualSLT.OneActiveEvenLinearization
public import ResidualSLT.OneActiveLaplace
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset MeasureTheory Filter

/-- Three retained directions suffice for every even degree, including two. -/
theorem oneActive_even_loss_retained_comparison (μ : Measure ℝ) (r p q : ℕ) (hr : 2 ≤ r) (heven : Even r)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r (p+1+q)))
    (τ : ℝ) (hτ : τ ≠ 0) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ᶠ w : OneActiveAux p q in nhds 0,
      a*‖oneActiveEvenRetained r p q w‖^2 ≤
        oneActivePopulationLoss μ r (τ^r) (oneActiveAssemble p q τ w) ∧
      oneActivePopulationLoss μ r (τ^r) (oneActiveAssemble p q τ w) ≤
        A*‖oneActiveEvenRetained r p q w‖^2 := by
  let M := sparseNetworkFeatureCount r (p+1+q)+r^2+2*r+1
  let x : Fin M → ℝ := fun i => (i.val:ℝ)+1
  let ν := atomicInput x
  have hM : 0 < M := by dsimp [M]; omega
  have hν : FinitePositiveFeatureGram ν (sparseNetworkFeatures r (p+1+q)) :=
    network_sparse_gram_many_atoms r (p+1+q) M (by omega) (by dsimp [M]; omega)
  obtain ⟨a,A,ha,hA,hb⟩ := oneActive_losses_comparable μ ν r (p+1+q) (by omega) (by omega) hμ hν
  have hx : Function.Injective x := by
    intro i j hij
    apply Fin.ext
    exact_mod_cast add_right_cancel hij
  have hd : ∀ j, (oneActiveEvenDirections r (τ^r) j).natDegree < Fintype.card (Fin M) := by
    intro j
    have hc : τ^r ≠ 0 := pow_ne_zero _ hτ
    have hp := activeDerivativeFactor_natDegree r hr (τ^r) hc
    have hpne : activeDerivativeFactor r (τ^r) ≠ 0 := by intro hz; simp [hz] at hp; omega
    dsimp [M]
    fin_cases j <;> norm_num [oneActiveEvenDirections, natDegree_mul hpne,
      natDegree_X_pow,natDegree_pow,activeTarget_natDegree r hr (τ^r) hc,hp,pow_two] <;>
      nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ r)]
  obtain ⟨b,B,hb0,hB0,hobs⟩ := oneActiveEvenRaw_observation_comparison r p q hr heven τ hτ x hx hd
  let f (w : OneActiveAux p q) (i : Fin M) :=
    (network r (fun j => zeroExtend (oneActiveAssemble p q τ w) j^r) (p+1+q)).eval (x i)
      -(x i+(τ^r)*(x i)^r)
  have he (w : OneActiveAux p q) :
      oneActivePopulationLoss ν r (τ^r) (oneActiveAssemble p q τ w) = ∑ i, f w i^2 := by
    unfold oneActivePopulationLoss
    rw [atomicInput_integral]
    rfl
  refine ⟨a*b^2,A*(M:ℝ)*B^2,by positivity,by positivity,?_⟩
  filter_upwards [hobs] with w hw
  simp only [oneActiveRawAux_eval_network r p q (by omega),oneActiveAuxEval_zero] at hw
  change b*‖oneActiveEvenRetained r p q w‖ ≤ ‖f w‖ ∧ ‖f w‖ ≤ B*‖oneActiveEvenRetained r p q w‖ at hw
  have hl := pow_le_pow_left₀ (mul_nonneg hb0.le (norm_nonneg _)) hw.1 2
  have hu := pow_le_pow_left₀ (norm_nonneg _) hw.2 2
  simp only [mul_pow] at hl hu
  have hf := finite_sum_sq_bounds M (f w)
  obtain ⟨hlo,hup⟩ := hb (τ^r) (oneActiveAssemble p q τ w)
  rw [he] at hlo hup
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (hl.trans hf.1) ha.le]
  · have hh := hf.2.trans (mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg M))
    nlinarith [mul_le_mul_of_nonneg_left hh hA.le]


/-- Near zero, nonnegative effective weights make B no larger than S. -/
theorem even_groupSecondCoefficient_le_sum (r n : ℕ) (hr : 2 ≤ r) (heven : Even r) :
    ∀ᶠ w : Fin n → ℝ in nhds 0, |groupSecondCoefficient r n w| ≤ weightPowerSum r w := by
  let C := signedRemainderEnvelope r n*n
  have hu : Tendsto (fun w : Fin n → ℝ => fun i => w i^r) (nhds 0) (nhds 0) := by
    have hh : Continuous (fun w : Fin n → ℝ => fun i => w i^r) := by fun_prop
    simpa [Pi.zero_def,show r ≠ 0 by omega] using hh.tendsto 0
  have hn : Tendsto (fun w : Fin n → ℝ => ‖fun i => w i^r‖) (nhds 0) (nhds 0) := by simpa using hu.norm
  have hC : Tendsto (fun w : Fin n → ℝ => C*‖fun i => w i^r‖) (nhds 0) (nhds 0) := by simpa using hn.const_mul C
  filter_upwards [hn.eventually (Iio_mem_nhds zero_lt_one),hC.eventually (Iio_mem_nhds zero_lt_one)] with w hw hcw
  have hh := inactiveEvenRemainder_bound r n hr (fun i => w i^r) hw.le (fun i => heven.pow_nonneg _)
  have hi := norm_le_pi_norm (inactiveEvenRemainder r n (fun i => w i^r)) ⟨1,by omega⟩
  have hb : |groupSecondCoefficient r n w| ≤ C*‖fun i => w i^r‖*weightPowerSum r w := by
    simpa [inactiveEvenRemainder,inactiveAuxVector,groupSecondCoefficient,weightPowerSum,C] using hi.trans hh
  exact hb.trans (by simpa using mul_le_mul_of_nonneg_right hcw.le (weightPowerSum_nonneg r n heven w))

/-- The five- and three-coordinate retained norms coincide locally in every even degree. -/
theorem oneActiveEvenRetained_norm_eq (r p q : ℕ) (hr : 2 ≤ r) (heven : Even r) :
    ∀ᶠ w : OneActiveAux p q in nhds 0,
      ‖oneActiveRetained r p q w‖ = ‖oneActiveEvenRetained r p q w‖ := by
  have hpre : Tendsto (fun w : OneActiveAux p q => w.2.1) (nhds 0) (nhds 0) :=
    (continuous_fst.comp continuous_snd).tendsto 0
  have hpost : Tendsto (fun w : OneActiveAux p q => w.2.2) (nhds 0) (nhds 0) :=
    (continuous_snd.comp continuous_snd).tendsto 0
  filter_upwards [hpre.eventually (even_groupSecondCoefficient_le_sum r p hr heven),
    hpost.eventually (even_groupSecondCoefficient_le_sum r q hr heven)] with w hp hq
  have h0 := norm_le_pi_norm (oneActiveEvenRetained r p q w) 0
  have h1 := norm_le_pi_norm (oneActiveEvenRetained r p q w) 1
  have h2 := norm_le_pi_norm (oneActiveEvenRetained r p q w) 2
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact hp.trans ((le_abs_self _).trans h1)
    · exact h2
    · exact hq.trans ((le_abs_self _).trans h2)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    fin_cases j
    · exact norm_le_pi_norm (oneActiveRetained r p q w) 0
    · exact norm_le_pi_norm (oneActiveRetained r p q w) 1
    · exact norm_le_pi_norm (oneActiveRetained r p q w) 3

end ResidualSLT
