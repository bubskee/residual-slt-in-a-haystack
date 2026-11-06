module
public import Mathlib.Data.Finset.Lattice.Fold
public import ResidualSLT.ArrangementLossComparison
public import ResidualSLT.ArrangementModelLaplace

/-! Uniform comparison with the factorized model, for every finite group configuration. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset MeasureTheory Filter

/-- Maximum norm and the sum of squares on a three-part finite coordinate space. -/
theorem three_component_sum_sq_bounds (a b c : ℕ)
    (z : (Fin a → ℝ) × (Fin b → ℝ) × (Fin c → ℝ)) :
    ‖z‖^2 ≤ (∑ i,z.1 i^2)+(∑ i,z.2.1 i^2)+(∑ i,z.2.2 i^2) ∧
    (∑ i,z.1 i^2)+(∑ i,z.2.1 i^2)+(∑ i,z.2.2 i^2) ≤ ((a:ℝ)+b+c)*‖z‖^2 := by
  have hA := finite_sum_sq_bounds a z.1
  have hB := finite_sum_sq_bounds b z.2.1
  have hC := finite_sum_sq_bounds c z.2.2
  have ha := pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le z) 2
  have hb := pow_le_pow_left₀ (norm_nonneg _) ((norm_fst_le z.2).trans (norm_snd_le z)) 2
  have hc := pow_le_pow_left₀ (norm_nonneg _) ((norm_snd_le z.2).trans (norm_snd_le z)) 2
  constructor
  · have hn : ‖z‖^2 ≤ ‖z.1‖^2+‖z.2.1‖^2+‖z.2.2‖^2 := by
      simp only [Prod.norm_def]
      rcases le_total ‖z.2.1‖ ‖z.2.2‖ with hh | hh
      · rw [max_eq_right hh]
        rcases le_total ‖z.1‖ ‖z.2.2‖ with hi | hi
        · rw [max_eq_right hi]; nlinarith [sq_nonneg ‖z.1‖,sq_nonneg ‖z.2.1‖]
        · rw [max_eq_left hi]; nlinarith [sq_nonneg ‖z.2.1‖,sq_nonneg ‖z.2.2‖]
      · rw [max_eq_left hh]
        rcases le_total ‖z.1‖ ‖z.2.1‖ with hi | hi
        · rw [max_eq_right hi]; nlinarith [sq_nonneg ‖z.1‖,sq_nonneg ‖z.2.2‖]
        · rw [max_eq_left hi]; nlinarith [sq_nonneg ‖z.2.1‖,sq_nonneg ‖z.2.2‖]
    linarith
  · nlinarith [mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg a),
      mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg b),mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg c)]

@[expose] def arrangementRetainedSquare (r k : ℕ) (n : Fin (k+1) → ℕ) (w : ArrangementAux k n) : ℝ :=
  (∑ j,w.1 j^2)+(∑ g,groupRetainedSquare r (n g) (w.2 g))

theorem arrangementRetainedSquare_bounds (r k : ℕ) (n : Fin (k+1) → ℕ) (w : ArrangementAux k n) :
    ‖arrangementSignedRetained r k n w‖^2 ≤ arrangementRetainedSquare r k n w ∧
    arrangementRetainedSquare r k n w ≤ (3*(k:ℝ)+2)*‖arrangementSignedRetained r k n w‖^2 := by
  have hh := three_component_sum_sq_bounds k (k+1) (k+1) (arrangementSignedRetained r k n w)
  have he : (k:ℝ)+((k+1:ℕ):ℝ)+((k+1:ℕ):ℝ)=3*k+2 := by push_cast; ring
  rw [he] at hh
  simpa only [arrangementSignedRetained,arrangementRetainedSquare,groupRetainedSquare,
    weightPowerSum,groupSecondCoefficient,sum_add_distrib,add_assoc] using hh

/-- A finite family of group comparisons gives one neighborhood and fixed positive constants. -/
theorem arrangement_model_retained_comparison (r k : ℕ) (hr : 2 ≤ r) (n : Fin (k+1) → ℕ) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ᶠ w : ArrangementAux k n in nhds 0,
      a*‖arrangementSignedRetained r k n w‖^2 ≤ arrangementComparisonLoss r k n w ∧
      arrangementComparisonLoss r k n w ≤ A*‖arrangementSignedRetained r k n w‖^2 := by
  classical
  choose a A ha hA hb using (fun g : Fin (k+1) => identityReferenceLoss_retained_comparison r (n g) hr)
  let c := min 1 (univ.inf' univ_nonempty a)
  let C := max 1 (univ.sup' univ_nonempty A)
  have hc : 0 < c := lt_min zero_lt_one ((Finset.lt_inf'_iff univ_nonempty).mpr (fun g _ => ha g))
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  have hca (g) : c ≤ a g := (min_le_right _ _).trans (inf'_le _ (mem_univ g))
  have hAC (g) : A g ≤ C := (le_sup' _ (mem_univ g)).trans (le_max_right _ _)
  have hg (g : Fin (k+1)) : ∀ᶠ w : ArrangementAux k n in nhds 0,
      a g*groupRetainedSquare r (n g) (w.2 g) ≤ identityReferenceLoss r (n g) (w.2 g) ∧
      identityReferenceLoss r (n g) (w.2 g) ≤ A g*groupRetainedSquare r (n g) (w.2 g) := by
    have ht : Tendsto (fun w : ArrangementAux k n => w.2 g) (nhds 0) (nhds 0) := by
      simpa [Function.comp_def] using ((continuous_apply g).comp continuous_snd).tendsto (0:ArrangementAux k n)
    exact ht.eventually (hb g)
  refine ⟨c,C*(3*(k:ℝ)+2),hc,by positivity,?_⟩
  filter_upwards [Filter.eventually_all.mpr hg] with w hw
  have hsq (g) : 0 ≤ groupRetainedSquare r (n g) (w.2 g) := by unfold groupRetainedSquare; positivity
  have hl : c*arrangementRetainedSquare r k n w ≤ arrangementComparisonLoss r k n w := by
    unfold arrangementRetainedSquare arrangementComparisonLoss
    simp only [mul_add,mul_sum]
    apply add_le_add
    · apply sum_le_sum
      intro j _
      simpa using mul_le_mul_of_nonneg_right (show c ≤ 1 from min_le_left _ _) (sq_nonneg (w.1 j))
    · apply sum_le_sum
      intro g _
      exact (mul_le_mul_of_nonneg_right (hca g) (hsq g)).trans (hw g).1
  have hu : arrangementComparisonLoss r k n w ≤ C*arrangementRetainedSquare r k n w := by
    unfold arrangementRetainedSquare arrangementComparisonLoss
    simp only [mul_add,mul_sum]
    apply add_le_add
    · apply sum_le_sum
      intro j _
      simpa using mul_le_mul_of_nonneg_right (show 1 ≤ C from le_max_left _ _) (sq_nonneg (w.1 j))
    · apply sum_le_sum
      intro g _
      exact (hw g).2.trans (mul_le_mul_of_nonneg_right (hAC g) (hsq g))
  have hn := arrangementRetainedSquare_bounds r k n w
  exact ⟨(mul_le_mul_of_nonneg_left hn.1 hc.le).trans hl,
    hu.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hn.2 hC.le)⟩

/-- The complete local comparison with k regular directions and k+1 identity groups. -/
theorem arrangement_network_local_comparison (μ : Measure ℝ) (r k : ℕ) (hr : 2 ≤ r)
    (n : Fin (k+1) → ℕ) (hL : 0 < arrangementDepth k n k le_rfl)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r (arrangementDepth k n k le_rfl)))
    (τ : Fin k → ℝ) (hτ : ∀ j,τ j ≠ 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ w : ArrangementAux k n in nhds 0,
      c*arrangementComparisonLoss r k n w ≤ arrangementPopulationLoss μ r k n τ w ∧
      arrangementPopulationLoss μ r k n τ w ≤ C*arrangementComparisonLoss r k n w := by
  obtain ⟨a,A,ha,hA,hactual⟩ := arrangement_loss_retained_comparison μ r k hr n hL hμ τ hτ
  obtain ⟨b,B,hb,hB,hmodel⟩ := arrangement_model_retained_comparison r k hr n
  refine ⟨a/B,A/b,div_pos ha hB,div_pos hA hb,?_⟩
  filter_upwards [hactual,hmodel] with w hw hv
  constructor
  · calc
      _ ≤ (a/B)*(B*‖arrangementSignedRetained r k n w‖^2) := mul_le_mul_of_nonneg_left hv.2 (div_pos ha hB).le
      _ = a*‖arrangementSignedRetained r k n w‖^2 := by field_simp
      _ ≤ _ := hw.1
  · calc
      _ ≤ A*‖arrangementSignedRetained r k n w‖^2 := hw.2
      _ = (A/b)*(b*‖arrangementSignedRetained r k n w‖^2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hv.1 (div_pos hA hb).le

end ResidualSLT
