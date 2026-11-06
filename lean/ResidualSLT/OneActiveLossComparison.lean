module
public import ResidualSLT.OneActiveAssembly
public import ResidualSLT.RectangularAtomicGram

/-! Local population-loss comparison derived from the actual raw composition. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset MeasureTheory Filter

/-- Changing an input measure with positive sparse Gram only rescales target losses. -/
theorem oneActive_losses_comparable (μ ν : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (hν : FinitePositiveFeatureGram ν (sparseNetworkFeatures r L)) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ c (w : Fin L → ℝ),
      a*oneActivePopulationLoss ν r c w ≤ oneActivePopulationLoss μ r c w ∧
      oneActivePopulationLoss μ r c w ≤ A*oneActivePopulationLoss ν r c w := by
  obtain ⟨a,A,ha,hA,hμb⟩ := oneActive_loss_coefficient_bounds μ r L hr hL hμ
  obtain ⟨b,B,hb,hB,hνb⟩ := oneActive_loss_coefficient_bounds ν r L hr hL hν
  refine ⟨a/B,A/b,div_pos ha hB,div_pos hA hb,?_⟩
  intro c w
  constructor
  · calc
      _ ≤ (a/B)*(B*‖oneActiveSparseCoefficients r c w‖^2) :=
        mul_le_mul_of_nonneg_left (hνb c w).2 (div_pos ha hB).le
      _ = a*‖oneActiveSparseCoefficients r c w‖^2 := by field_simp
      _ ≤ _ := (hμb c w).1
  · calc
      _ ≤ A*‖oneActiveSparseCoefficients r c w‖^2 := (hμb c w).2
      _ = (A/b)*(b*‖oneActiveSparseCoefficients r c w‖^2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hνb c w).1 (div_pos hA hb).le

theorem finite_sum_sq_bounds (n : ℕ) (v : Fin n → ℝ) :
    ‖v‖^2 ≤ ∑ i, v i^2 ∧ (∑ i, v i^2) ≤ (n:ℝ)*‖v‖^2 := by
  refine ⟨effective_norm_sq_le_sum n v,?_⟩
  calc
    _ ≤ ∑ _i : Fin n, ‖v‖^2 := by
      apply sum_le_sum
      intro i _
      have hh := norm_le_pi_norm v i
      rw [Real.norm_eq_abs] at hh
      nlinarith [sq_abs (v i),abs_nonneg (v i),norm_nonneg v]
    _ = _ := by simp

/-- Actual one-active population loss is locally equivalent to the retained norm,
for every r≥3 and arbitrary before/after lengths, including empty groups. -/
theorem oneActive_loss_retained_comparison (μ : Measure ℝ) (r p q : ℕ) (hr : 3 ≤ r)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r (p+1+q)))
    (τ : ℝ) (hτ : τ ≠ 0) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ᶠ w : OneActiveAux p q in nhds 0,
      a*‖oneActiveRetained r p q w‖^2 ≤
        oneActivePopulationLoss μ r (τ^r) (oneActiveAssemble p q τ w) ∧
      oneActivePopulationLoss μ r (τ^r) (oneActiveAssemble p q τ w) ≤
        A*‖oneActiveRetained r p q w‖^2 := by
  let M := sparseNetworkFeatureCount r (p+1+q)+r*(2*r-1)+1
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
  have hd : ∀ j, (oneActiveSignedDirections r (τ^r) j).natDegree < Fintype.card (Fin M) := by
    intro j
    have he := congrFun (oneActiveSignedDirections_degrees r hr (τ^r) (pow_ne_zero _ hτ)) j
    rw [he,Fintype.card_fin]
    have hg := two_direction_degree_gaps r 1 hr (by omega)
    dsimp [M]
    fin_cases j <;> norm_num at * <;> omega
  obtain ⟨b,B,hb0,hB0,hobs⟩ := oneActiveRaw_observation_comparison r p q hr τ hτ x hx hd
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
  change b*‖oneActiveRetained r p q w‖ ≤ ‖f w‖ ∧ ‖f w‖ ≤ B*‖oneActiveRetained r p q w‖ at hw
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

end ResidualSLT
