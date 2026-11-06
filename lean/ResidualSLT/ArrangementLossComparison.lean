module
public import ResidualSLT.ArrangementAssembly
public import ResidualSLT.NetworkTargetLoss
public import ResidualSLT.OneActiveEvenComparison

/-! The arbitrary-active-count local comparison for the actual squared-error population loss. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset MeasureTheory Filter

@[expose] def arrangementPopulationLoss (μ : Measure ℝ) (r k : ℕ) (n : Fin (k+1) → ℕ)
    (τ : Fin k → ℝ) (w : ArrangementAux k n) : ℝ :=
  networkTargetLoss μ r (arrangementFlatten k n τ 0 k le_rfl) (arrangementFlatten k n τ w k le_rfl)

/-- Finite observation comparisons transfer through positive sparse Gram matrices. -/
theorem networkTargetLoss_retained_of_observations {α V : Type*} [NormedAddCommGroup V]
    (μ : Measure ℝ) (r L M : ℕ) (hr : 2 ≤ r) (hL : 0 < L) (hM0 : 0 < M)
    (hM : sparseNetworkFeatureCount r L ≤ M)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (l : Filter α)
    (t : Fin L → ℝ) (σ : α → Fin L → ℝ) (z : α → V)
    (hobs : ∃ b B : ℝ, 0 < b ∧ 0 < B ∧ ∀ᶠ w in l,
      b*‖z w‖ ≤ ‖fun i : Fin M =>
        (network r (fun j => zeroExtend (σ w) j^r) L).eval ((i.val:ℝ)+1)-
        (network r (fun j => zeroExtend t j^r) L).eval ((i.val:ℝ)+1)‖ ∧
      ‖fun i : Fin M =>
        (network r (fun j => zeroExtend (σ w) j^r) L).eval ((i.val:ℝ)+1)-
        (network r (fun j => zeroExtend t j^r) L).eval ((i.val:ℝ)+1)‖ ≤ B*‖z w‖) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ᶠ w in l,
      a*‖z w‖^2 ≤ networkTargetLoss μ r t (σ w) ∧ networkTargetLoss μ r t (σ w) ≤ A*‖z w‖^2 := by
  let ν := atomicInput (fun i : Fin M => (i.val:ℝ)+1)
  have hν := network_sparse_gram_many_atoms r L M hr hM
  obtain ⟨a,A,ha,hA,hb⟩ := networkTargetLoss_comparable μ ν r L hr hL hμ hν
  obtain ⟨b,B,hb0,hB0,hobs⟩ := hobs
  let f (w : α) (i : Fin M) :=
    (network r (fun j => zeroExtend (σ w) j^r) L).eval ((i.val:ℝ)+1)-
    (network r (fun j => zeroExtend t j^r) L).eval ((i.val:ℝ)+1)
  have he (w : α) : networkTargetLoss ν r t (σ w) = ∑ i, f w i^2 := by
    unfold networkTargetLoss
    rw [atomicInput_integral]
  refine ⟨a*b^2,A*(M:ℝ)*B^2,by positivity,by positivity,?_⟩
  filter_upwards [hobs] with w hw
  change b*‖z w‖ ≤ ‖f w‖ ∧ ‖f w‖ ≤ B*‖z w‖ at hw
  have hl := pow_le_pow_left₀ (mul_nonneg hb0.le (norm_nonneg _)) hw.1 2
  have hu := pow_le_pow_left₀ (norm_nonneg _) hw.2 2
  simp only [mul_pow] at hl hu
  have hf := finite_sum_sq_bounds M (f w)
  obtain ⟨hlo,hup⟩ := hb t (σ w)
  rw [he] at hlo hup
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (hl.trans hf.1) ha.le]
  · have hh := hf.2.trans (mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg M))
    nlinarith [mul_le_mul_of_nonneg_left hh hA.le]

theorem arrangement_signed_loss_retained_comparison (μ : Measure ℝ) (r k : ℕ) (hr : 3 ≤ r)
    (n : Fin (k+1) → ℕ) (hL : 0 < arrangementDepth k n k le_rfl)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r (arrangementDepth k n k le_rfl)))
    (τ : Fin k → ℝ) (hτ : ∀ j,τ j ≠ 0) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ᶠ w in nhds (0:ArrangementAux k n),
      a*‖arrangementSignedRetained r k n w‖^2 ≤ arrangementPopulationLoss μ r k n τ w ∧
      arrangementPopulationLoss μ r k n τ w ≤ A*‖arrangementSignedRetained r k n w‖^2 := by
  let M := sparseNetworkFeatureCount r (arrangementDepth k n k le_rfl)+(2*r-1)*r^k+1
  let x : Fin M → ℝ := fun i => (i.val:ℝ)+1
  have hx : Function.Injective x := by
    intro i j hij
    apply Fin.ext
    exact_mod_cast add_right_cancel hij
  have hc : ∀ j<k,zeroExtend (fun i => (τ i)^r) j ≠ 0 := by
    intro j hj
    simpa [zeroExtend,hj] using pow_ne_zero r (hτ ⟨j,hj⟩)
  have hκ : ∀ j, (r:ℝ)*(τ j)^(r-1) ≠ 0 := fun j =>
    mul_ne_zero (by exact_mod_cast (by omega : r ≠ 0)) (pow_ne_zero _ (hτ j))
  have hd := hasFDerivAt_pi.mpr (fun i : Fin M => arrangementAuxEval_hasFDerivAt r k
    (fun g => r^(n g)+2) (zeroExtend (fun j => (τ j)^r)) (x i) k)
  have hobs := controlled_linearization_comparison _ _ hd _ _ _ _
    (arrangementRawAux_tendsto r k (by omega) n τ)
    (arrangementSignedRemainder_isLittleO r k (by omega) n τ)
    (arrangementRawAux_signed_decomposition r k n τ)
    (arrangementSignedInsert_deriv_injective r k hr (fun g => r^(n g)) _ hc _ hκ x hx
      (by dsimp [M]; simp only [Fintype.card_fin]; omega))
  simp only [arrangementRawAux_eval_network r k (by omega) n τ _ _ k le_rfl,
    arrangementAuxEval_zero,← arrangementFlatten_target r k (by omega) n τ] at hobs
  exact networkTargetLoss_retained_of_observations μ r _ M (by omega) hL (by dsimp [M]; omega)
    (by dsimp [M]; omega) hμ (nhds 0) _ _ _ hobs

theorem arrangement_even_loss_retained_comparison (μ : Measure ℝ) (r k : ℕ) (hr : 2 ≤ r) (heven : Even r)
    (n : Fin (k+1) → ℕ) (hL : 0 < arrangementDepth k n k le_rfl)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r (arrangementDepth k n k le_rfl)))
    (τ : Fin k → ℝ) (hτ : ∀ j,τ j ≠ 0) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ᶠ w in nhds (0:ArrangementAux k n),
      a*‖arrangementEvenRetained r k n w‖^2 ≤ arrangementPopulationLoss μ r k n τ w ∧
      arrangementPopulationLoss μ r k n τ w ≤ A*‖arrangementEvenRetained r k n w‖^2 := by
  let M := sparseNetworkFeatureCount r (arrangementDepth k n k le_rfl)+r*r^k+1
  let x : Fin M → ℝ := fun i => (i.val:ℝ)+1
  have hx : Function.Injective x := by
    intro i j hij
    apply Fin.ext
    exact_mod_cast add_right_cancel hij
  have hc : ∀ j<k,zeroExtend (fun i => (τ i)^r) j ≠ 0 := by
    intro j hj
    simpa [zeroExtend,hj] using pow_ne_zero r (hτ ⟨j,hj⟩)
  have hκ : ∀ j, (r:ℝ)*(τ j)^(r-1) ≠ 0 := fun j =>
    mul_ne_zero (by exact_mod_cast (by omega : r ≠ 0)) (pow_ne_zero _ (hτ j))
  have hd := hasFDerivAt_pi.mpr (fun i : Fin M => arrangementAuxEval_hasFDerivAt r k
    (fun g => r^(n g)+2) (zeroExtend (fun j => (τ j)^r)) (x i) k)
  have hobs := controlled_linearization_comparison _ _ hd _ _ _ _
    (arrangementRawAux_tendsto r k hr n τ)
    (arrangementEvenRemainder_isLittleO r k hr heven n τ)
    (arrangementRawAux_even_decomposition r k n τ)
    (arrangementEvenInsert_deriv_injective r k hr (fun g => r^(n g)) _ hc _ hκ x hx
      (by dsimp [M]; simp only [Fintype.card_fin]; omega))
  simp only [arrangementRawAux_eval_network r k hr n τ _ _ k le_rfl,
    arrangementAuxEval_zero,← arrangementFlatten_target r k hr n τ] at hobs
  exact networkTargetLoss_retained_of_observations μ r _ M hr hL (by dsimp [M]; omega)
    (by dsimp [M]; omega) hμ (nhds 0) _ _ _ hobs

/-- The virtual second group coefficients are smaller than the first ones locally in even degree. -/
theorem arrangementEvenRetained_norm_eq (r k : ℕ) (hr : 2 ≤ r) (heven : Even r)
    (n : Fin (k+1) → ℕ) :
    ∀ᶠ w : ArrangementAux k n in nhds 0,
      ‖arrangementSignedRetained r k n w‖ = ‖arrangementEvenRetained r k n w‖ := by
  have hg (g : Fin (k+1)) : ∀ᶠ w : ArrangementAux k n in nhds 0,
      |groupSecondCoefficient r (n g) (w.2 g)| ≤ weightPowerSum r (w.2 g) := by
    have ht : Tendsto (fun w : ArrangementAux k n => w.2 g) (nhds 0) (nhds 0) := by
      simpa [Function.comp_def] using ((continuous_apply g).comp continuous_snd).tendsto (0:ArrangementAux k n)
    exact ht.eventually (even_groupSecondCoefficient_le_sum r (n g) hr heven)
  filter_upwards [Filter.eventually_all.mpr hg] with w hw
  have hb : ‖(arrangementSignedRetained r k n w).2.2‖ ≤ ‖(arrangementSignedRetained r k n w).2.1‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro g
    exact (hw g).trans ((le_abs_self _).trans (norm_le_pi_norm (arrangementSignedRetained r k n w).2.1 g))
  simp only [Prod.norm_def] at hb ⊢
  rw [max_eq_left hb]
  rfl

/-- Uniform actual loss comparison, including r=2, every active count, and every group size. -/
theorem arrangement_loss_retained_comparison (μ : Measure ℝ) (r k : ℕ) (hr : 2 ≤ r)
    (n : Fin (k+1) → ℕ) (hL : 0 < arrangementDepth k n k le_rfl)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r (arrangementDepth k n k le_rfl)))
    (τ : Fin k → ℝ) (hτ : ∀ j,τ j ≠ 0) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ᶠ w in nhds (0:ArrangementAux k n),
      a*‖arrangementSignedRetained r k n w‖^2 ≤ arrangementPopulationLoss μ r k n τ w ∧
      arrangementPopulationLoss μ r k n τ w ≤ A*‖arrangementSignedRetained r k n w‖^2 := by
  by_cases h3 : 3 ≤ r
  · exact arrangement_signed_loss_retained_comparison μ r k h3 n hL hμ τ hτ
  · have heven : Even r := by
      have he : r=2 := by omega
      rw [he]
      decide
    obtain ⟨a,A,ha,hA,hb⟩ := arrangement_even_loss_retained_comparison μ r k hr heven n hL hμ τ hτ
    refine ⟨a,A,ha,hA,?_⟩
    filter_upwards [hb,arrangementEvenRetained_norm_eq r k hr heven n] with w hw he
    simpa only [he] using hw

end ResidualSLT
