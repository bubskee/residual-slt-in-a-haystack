module
public import ResidualSLT.SignedNetwork

/-! The exact graded residual feature space, omitting identically zero coefficients. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial MeasureTheory Finset

@[expose] def sparseNetworkFeatureCount (r L : ℕ) : ℕ := (r^L-1)/(r-1)
@[expose] def sparseNetworkFeatures (r L : ℕ) (j : Fin (sparseNetworkFeatureCount r L)) (x : ℝ) : ℝ :=
  x^(r+j.val*(r-1))
@[expose] def sparseNetworkCoefficients (r : ℕ) {L : ℕ} (w : Fin L → ℝ)
    (j : Fin (sparseNetworkFeatureCount r L)) : ℝ :=
  (network r (fun i => zeroExtend w i^r) L-X).coeff (r+j.val*(r-1))

/-- This is the manuscript's exponent 1+(j+1)(r-1), with a zero-based Lean index. -/
theorem sparseNetworkFeature_degree (r : ℕ) (hr : 2 ≤ r) (j : ℕ) :
    r+j*(r-1) = 1+(j+1)*(r-1) := by
  rw [add_mul,one_mul]
  omega

theorem sparseNetworkFeatureCount_pos (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L) :
    0 < sparseNetworkFeatureCount r L := by
  have hp := Nat.le_pow (a := r) hL
  unfold sparseNetworkFeatureCount
  have hh : 1 ≤ (r^L-1)/(r-1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  omega

theorem sparseNetworkIndex_bound (r L : ℕ) (hr : 2 ≤ r)
    (j : Fin (sparseNetworkFeatureCount r L)) : j.val*(r-1) < networkFeatureCount r L := by
  have hk : 0 < r-1 := by omega
  have hj : j.val+1 ≤ (r^L-1)/(r-1) := j.isLt
  have hh := (Nat.le_div_iff_mul_le hk).mp hj
  rw [add_mul,one_mul] at hh
  unfold networkFeatureCount
  omega

@[expose] def sparseNetworkIndex (r L : ℕ) (hr : 2 ≤ r)
    (j : Fin (sparseNetworkFeatureCount r L)) : Fin (networkFeatureCount r L) :=
  ⟨j.val*(r-1),sparseNetworkIndex_bound r L hr j⟩

theorem sparseNetworkIndex_injective (r L : ℕ) (hr : 2 ≤ r) :
    Function.Injective (sparseNetworkIndex r L hr) := by
  intro i j hij
  apply Fin.ext
  have hh := congrArg Fin.val hij
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < r-1) hh

/-- The grading forces every omitted coefficient to vanish for every raw weight. -/
theorem networkCoefficients_zero_off_sparse (r L : ℕ) (hr : 2 ≤ r)
    (w : Fin L → ℝ) (i : Fin (networkFeatureCount r L))
    (hi : i ∉ Set.range (sparseNetworkIndex r L hr)) : networkCoefficients r w i = 0 := by
  have hk : 0 < r-1 := by omega
  have hn : ¬ r-1 ∣ i.val := by
    intro hd
    have hb : (i.val/(r-1)+1)*(r-1) ≤ r^L-1 := by
      rw [add_mul,one_mul,Nat.div_mul_cancel hd]
      have hh := i.isLt
      unfold networkFeatureCount at hh
      omega
    have hj : i.val/(r-1) < sparseNetworkFeatureCount r L :=
      (Nat.le_div_iff_mul_le hk).mpr hb
    apply hi
    exact ⟨⟨i.val/(r-1),hj⟩,Fin.ext (Nat.div_mul_cancel hd)⟩
  unfold networkCoefficients
  rw [coeff_sub,coeff_X,ite_eq_right (by omega : 1 ≠ r+i.val),sub_zero,
    network_eq_graded r (by omega)]
  have he : r+i.val = (r-1+i.val)+1 := by omega
  rw [he,coeff_X_mul,← expand_eq_comp_X_pow,coeff_expand hk]
  apply ite_eq_right
  intro hd
  exact hn ((Nat.dvd_add_iff_right (dvd_refl (r-1))).mpr hd)

/-- Sparse reindexing of the exact network expansion. -/
theorem sparse_network_feature_expansion (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (w : Fin L → ℝ) (x : ℝ) :
    (network r (fun i => zeroExtend w i^r) L).eval x-x =
      ∑ j, sparseNetworkCoefficients r w j*sparseNetworkFeatures r L j x := by
  rw [network_feature_expansion r hr L hL]
  symm
  apply Fintype.sum_of_injective (sparseNetworkIndex r L hr) (sparseNetworkIndex_injective r L hr)
  · intro i hi
    change networkCoefficients r w i*networkFeatures r L i x = 0
    rw [networkCoefficients_zero_off_sparse r L hr w i hi,zero_mul]
  · intro j
    rfl

/-- Removing exactly the forced zero coordinates preserves the maximum coefficient norm. -/
theorem sparseNetworkCoefficients_norm (r L : ℕ) (hr : 2 ≤ r) (w : Fin L → ℝ) :
    ‖sparseNetworkCoefficients r w‖ = ‖networkCoefficients r w‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    exact norm_le_pi_norm (networkCoefficients r w) (sparseNetworkIndex r L hr j)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    by_cases hi : i ∈ Set.range (sparseNetworkIndex r L hr)
    · obtain ⟨j,rfl⟩ := hi
      exact norm_le_pi_norm (sparseNetworkCoefficients r w) j
    · rw [networkCoefficients_zero_off_sparse r L hr w i hi,norm_zero]
      exact norm_nonneg _

theorem sparse_network_squaredError_eq (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (w : Fin L → ℝ) (x : ℝ) :
    networkSquaredError r w x = (∑ j, sparseNetworkCoefficients r w j*sparseNetworkFeatures r L j x)^2 := by
  unfold networkSquaredError
  rw [sparse_network_feature_expansion r L hr hL]

theorem sparse_network_squaredError_integrable (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (w : Fin L → ℝ) :
    Integrable (networkSquaredError r w) μ := by
  change Integrable (fun x => networkSquaredError r w x) μ
  simp_rw [sparse_network_squaredError_eq r L hr hL]
  exact feature_square_integrable μ _ h.integrable _

theorem sparse_network_loss_eq_gram (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (w : Fin L → ℝ) :
    networkPopulationLoss μ r w =
      gramValue (featureGram μ (sparseNetworkFeatures r L)) (sparseNetworkCoefficients r w) := by
  simp only [networkPopulationLoss,sparse_network_squaredError_eq r L hr hL]
  exact feature_integral_eq_gram μ _ h.integrable _

theorem sparseNetworkCoefficients_continuous (r L : ℕ) (hr : 2 ≤ r) :
    Continuous (@sparseNetworkCoefficients r L) := by
  apply continuous_pi_iff.mpr
  intro j
  exact (continuous_apply (sparseNetworkIndex r L hr j)).comp (networkCoefficients_continuous r L)

theorem sparse_networkPopulationLoss_continuous (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) :
    Continuous (@networkPopulationLoss μ r L) := by
  rw [funext (sparse_network_loss_eq_gram μ r L hr hL h)]
  exact (gramValue_continuous _).comp (sparseNetworkCoefficients_continuous r L hr)

/-- The sparse Gram gives global coercivity in the original coefficient norm. -/
theorem sparse_network_loss_coefficient_bounds (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ w : Fin L → ℝ,
      c*‖networkCoefficients r w‖^2 ≤ networkPopulationLoss μ r w ∧
      networkPopulationLoss μ r w ≤ C*‖networkCoefficients r w‖^2 := by
  let : Nonempty (Fin (sparseNetworkFeatureCount r L)) := ⟨⟨0,sparseNetworkFeatureCount_pos r L hr hL⟩⟩
  obtain ⟨c,C,hc,hC,hb⟩ := gramValue_bounds _ h.positive
  refine ⟨c,C,hc,hC,?_⟩
  intro w
  simpa only [sparse_network_loss_eq_gram μ r L hr hL h,sparseNetworkCoefficients_norm r L hr w] using
    hb (sparseNetworkCoefficients r w)

/-- The previous contiguous Gram hypothesis implies the new sparse hypothesis. -/
theorem sparse_gram_of_contiguous (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L)) :
    FinitePositiveFeatureGram μ (sparseNetworkFeatures r L) := by
  refine ⟨fun i j => h.integrable (sparseNetworkIndex r L hr i) (sparseNetworkIndex r L hr j),?_⟩
  exact h.positive.submatrix (sparseNetworkIndex_injective r L hr)

/-- Any two input measures coercive on the sparse feature space give globally
comparable population losses. The comparison constants are derived. -/
theorem sparse_network_losses_comparable (μ ν : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (hν : FinitePositiveFeatureGram ν (sparseNetworkFeatures r L)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ w : Fin L → ℝ,
      c*networkPopulationLoss ν r w ≤ networkPopulationLoss μ r w ∧
      networkPopulationLoss μ r w ≤ C*networkPopulationLoss ν r w := by
  obtain ⟨a,A,ha,hA,hμb⟩ := sparse_network_loss_coefficient_bounds μ r L hr hL hμ
  obtain ⟨b,B,hb,hB,hνb⟩ := sparse_network_loss_coefficient_bounds ν r L hr hL hν
  refine ⟨a/B,A/b,div_pos ha hB,div_pos hA hb,?_⟩
  intro w
  constructor
  · calc
      _ ≤ (a/B)*(B*‖networkCoefficients r w‖^2) :=
        mul_le_mul_of_nonneg_left (hνb w).2 (div_pos ha hB).le
      _ = a*‖networkCoefficients r w‖^2 := by field_simp
      _ ≤ _ := (hμb w).1
  · calc
      _ ≤ A*‖networkCoefficients r w‖^2 := (hμb w).2
      _ = (A/b)*(b*‖networkCoefficients r w‖^2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hνb w).1 (div_pos hA hb).le

/-- Sparse Gram positivity makes the actual loss positive off the identity parameter
on the unit neighborhood, independently of parity. -/
theorem sparse_network_loss_pos (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (w : Fin L → ℝ)
    (hw : w ∈ Metric.ball 0 1) (hne : w ≠ 0) : 0 < networkPopulationLoss μ r w := by
  obtain ⟨c,C,hc,_,hb⟩ := sparse_network_loss_coefficient_bounds μ r L hr hL h
  have hnorm : 0 < ‖networkCoefficients r w‖^2 := by
    have hh := (signed_network_coefficients_bounds r hr L hL w hw).1
    have hp := cancellationModel_pos r L w hne
    by_contra hn
    have hz : ‖networkCoefficients r w‖^2 = 0 := le_antisymm (not_lt.mp hn) (sq_nonneg _)
    rw [hz,mul_zero] at hh
    exact (not_le_of_gt hp) hh
  exact (mul_pos hc hnorm).trans_le (hb w).1

end ResidualSLT
