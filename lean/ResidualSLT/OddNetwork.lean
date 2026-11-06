module
public import ResidualSLT.AngularIntegration

/-! Whole-neighborhood odd-degree integration and actual population-loss thresholds. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Metric

/-- Reflection of all raw coordinates leaves the reduced loss unchanged. -/
theorem cancellationModel_neg (r L : ℕ) (w : Fin L → ℝ) :
    cancellationModel r (-w) = cancellationModel r w := by
  have hs : weightPowerSum r (-w) = (-1 : ℝ) ^ r * weightPowerSum r w := by
    simpa using weightPowerSum_smul r L (-1) w
  have hq : weightSquareSum r (-w) = weightSquareSum r w := by
    rw [weightSquareSum_eq, weightSquareSum_eq]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.neg_apply, pow_mul, neg_sq]
  have hu : ((-1 : ℝ) ^ r) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm r 2, pow_mul]
    norm_num
  simp only [cancellationModel, hs, hq, mul_pow, hu, one_mul]

/-- Positive and negative pivot patches cover the full raw ball, including all
angular chart overlaps; the origin is added explicitly. -/
theorem cancellationModel_integrable_of_angular (r n : ℕ) (ε : ℝ) (s : ℝ)
    (hi : IntegrableOn (fun z : ℝ × (Fin (n) → ℝ) =>
      weightedCancellation (n + 1) r r s (z.1, angularFermat r 1 z.2))
      (Ioo 0 ε ×ˢ closedBall 0 1) volume) :
    IntegrableOn (fun w : Fin (n + 1) → ℝ => cancellationModel r w ^ (-s)) (ball 0 ε) volume := by
  let P := fun j : Fin (n + 1) => projectiveConePatch j (Ioo 0 ε)
    (closedBall (0 : Fin (n) → ℝ) 1)
  have hbound : ∀ y ∈ closedBall (0 : Fin (n) → ℝ) 1, ∀ i, |y i| ≤ 1 := by
    intro y hy i
    exact (norm_le_pi_norm y i).trans (mem_closedBall_zero_iff.mp hy)
  have hpos (j : Fin (n + 1)) : IntegrableOn
      (fun w => cancellationModel r w ^ (-s)) (P j) volume := by
    apply (cancellationModel_projective_integrableOn_iff r j measurableSet_Ioo
      (fun _ h => h.1) measurableSet_closedBall hbound s).mpr
    exact hi
  have hneg (j : Fin (n + 1)) : IntegrableOn
      (fun w => cancellationModel r w ^ (-s)) (Neg.neg '' P j) volume := by
    have he := (Measure.measurePreserving_neg (volume : Measure (Fin (n + 1) → ℝ))).integrableOn_comp_preimage
      (Homeomorph.neg (Fin (n + 1) → ℝ)).measurableEmbedding
      (f := fun w => cancellationModel r w ^ (-s)) (s := P j)
    have hc : (fun w : Fin (n + 1) → ℝ => cancellationModel r w ^ (-s)) ∘ Neg.neg =
        (fun w => cancellationModel r w ^ (-s)) := by
      funext w; simp only [Function.comp_apply, cancellationModel_neg]
    have hp : Neg.neg ⁻¹' P j = Neg.neg '' P j := by
      ext w
      constructor
      · intro hw; exact ⟨-w, hw, neg_neg w⟩
      · rintro ⟨v, hv, rfl⟩; simpa using hv
    rw [hc, hp] at he
    exact he.mpr (hpos j)
  have hall : IntegrableOn (fun w : Fin (n + 1) → ℝ => cancellationModel r w ^ (-s))
      ({0} ∪ ⋃ j, (P j ∪ Neg.neg '' P j)) volume :=
    (integrableOn_singleton (μ := volume) (f := fun w : Fin (n + 1) → ℝ => cancellationModel r w ^ (-s)) (x := 0) (hx := by simp)).union (integrableOn_finite_iUnion.mpr (fun j => (hpos j).union (hneg j)))
  apply hall.mono_set
  intro w hw
  by_cases hz : w = 0
  · exact Or.inl hz
  · obtain ⟨j, z, hz0, hzε, hza, hwz⟩ := signed_radialBlowup_cover ε w hw hz
    have hp : radialBlowup j z ∈ P j := by
      refine ⟨z, ?_, rfl⟩
      change (z j ∈ Ioo 0 ε) ∧ (fun i => z (j.succAbove i)) ∈ closedBall 0 1
      refine ⟨⟨hz0, hzε⟩, ?_⟩
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
      intro i
      exact hza _ (Fin.succAbove_ne j i)
    apply Or.inr
    apply mem_iUnion.mpr
    refine ⟨j, ?_⟩
    rcases hwz with hwz | hwz
    · exact Or.inl (hwz.symm ▸ hp)
    · exact Or.inr ⟨radialBlowup j z, hp, hwz.symm⟩

/-- A whole-ball integral restricts to a genuine positive cone, yielding the
radial/angular integral with its derived density. -/
theorem cancellationModel_angular_of_integrable (r n : ℕ) (ε : ℝ) (s : ℝ)
    (hi : IntegrableOn (fun w : Fin (n + 1) → ℝ => cancellationModel r w ^ (-s)) (ball 0 ε) volume) :
    IntegrableOn (fun z : ℝ × (Fin (n) → ℝ) =>
      weightedCancellation (n + 1) r r s (z.1, angularFermat r 1 z.2))
      (Ioo 0 ε ×ˢ closedBall 0 1) volume := by
  have hb : ∀ y ∈ closedBall (0 : Fin (n) → ℝ) 1, ∀ i, |y i| ≤ 1 := by
    intro y hy i
    exact (norm_le_pi_norm y i).trans (mem_closedBall_zero_iff.mp hy)
  have hc := hi.mono_set (projectiveConePatch_subset_ball (0 : Fin (n + 1))
    (R := Ioo 0 ε) (fun _ h => h.1) (fun _ h => h.2) hb)
  have ha := (cancellationModel_projective_integrableOn_iff r (0 : Fin (n + 1))
    measurableSet_Ioo (fun _ h => h.1) measurableSet_closedBall hb s).mp hc
  exact ha

/-- Nonpositive singular exponents are integrable on every bounded raw ball. -/
theorem cancellationModel_integrable_nonpos (r L : ℕ) (ε : ℝ) (s : ℝ) (hs : s ≤ 0) :
    IntegrableOn (fun w : Fin L → ℝ => cancellationModel r w ^ (-s)) (ball 0 ε) volume := by
  have hc := (cancellationModel_continuous r L).rpow_const (fun _ => Or.inr (neg_nonneg.mpr hs))
  exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall

/-- Exact odd-degree reduced-loss threshold on the entire raw neighborhood.
The necessity proof includes equality; no angular rectangle is assumed. -/
theorem odd_cancellationModel_integrableOn_iff (r : ℕ) (hr : 3 ≤ r) (hodd : Odd r)
    (L : ℕ) (hL : 2 ≤ L) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ) :
    IntegrableOn (fun w : Fin L → ℝ => cancellationModel r w ^ (-s)) (ball 0 ε) volume ↔
      s < min ((L : ℝ) / (2 * r)) (((L : ℝ) + r) / (4 * r)) := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 2 := ⟨L - 2, by omega⟩
  have hr0 : 0 < r := by omega
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr0
  have ha : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have he : 2 * ((r : ℝ) + r) = 4 * r := by ring
  constructor
  · intro hi
    by_cases hs : s ≤ 0
    · exact hs.trans_lt (lt_min (by positivity) (by positivity))
    have hs0 : 0 ≤ s := (lt_of_not_ge hs).le
    have hang := cancellationModel_angular_of_integrable r (n + 1) ε s hi
    have hcast : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
    rw [hcast] at hang
    by_cases hn : n = 0
    · subst n
      have hrad := weightedAngular_radial_necessary volume measurableSet_closedBall
        (ne_of_gt ((measure_ball_pos volume (0 : Fin 1 → ℝ) zero_lt_one).trans_le
          (measure_mono ball_subset_closedBall)))
        (angularFermat r 1) 2 r ε hε hε1 s hs0 (by simpa [Measure.volume_eq_prod] using hang)
      have hr3 : (3 : ℝ) ≤ r := by exact_mod_cast hr
      rw [lt_min_iff, lt_div_iff₀ (by positivity : 0 < 2 * (r : ℝ)),
        lt_div_iff₀ (by positivity : 0 < 4 * (r : ℝ))]
      norm_num only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero, zero_add]
      constructor <;> nlinarith
    · obtain ⟨y, hy, hz⟩ := odd_angularFermat_interior_zero r (n + 1) hr0 hodd (by omega)
      have hh := weightedAngular_necessary_of_interior_zero r n hr0 (n + 2) ha ε hε hε1 s y hy hz hang
      simpa only [he, Nat.cast_add, Nat.cast_ofNat] using hh
  · intro hcrit
    by_cases hs : s ≤ 0
    · exact cancellationModel_integrable_nonpos r (n + 2) ε s hs
    have hi := weightedAngular_integrable_cube r n hr0 (n + 2) ha s (lt_of_not_ge hs).le
      (by simpa only [he, Nat.cast_add, Nat.cast_ofNat] using hcrit)
    apply cancellationModel_integrable_of_angular r (n + 1) ε s
    have hcast : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
    rw [hcast]
    exact hi.mono_set (prod_mono (Ioo_subset_Ioo le_rfl hε1) Subset.rfl)


/-- The one-dimensional reduced loss has the ordinary radial threshold. -/
theorem cancellationModel_one_integrableOn_iff (r : ℕ) (hr : 0 < r)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ) :
    IntegrableOn (fun w : Fin 1 → ℝ => cancellationModel r w ^ (-s)) (ball 0 ε) volume ↔
      s < 1 / (2 * r) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  constructor
  · intro hi
    by_cases hs : s ≤ 0
    · exact hs.trans_lt (by positivity)
    have hang := cancellationModel_angular_of_integrable r 0 ε s hi
    norm_num only [Nat.cast_zero, zero_add] at hang
    have hrad := weightedAngular_radial_necessary volume measurableSet_closedBall
      (ne_of_gt ((measure_ball_pos volume (0 : Fin 0 → ℝ) zero_lt_one).trans_le
        (measure_mono ball_subset_closedBall)))
      (angularFermat r 1) 1 r ε hε hε1 s (lt_of_not_ge hs).le
      (by simpa only [Measure.volume_eq_prod] using hang)
    rw [lt_div_iff₀ (by positivity : 0 < 2 * (r : ℝ))]
    nlinarith
  · intro hcrit
    by_cases hs : s ≤ 0
    · exact cancellationModel_integrable_nonpos r 1 ε s hs
    apply cancellationModel_integrable_of_angular r 0 ε s
    norm_num only [Nat.cast_zero, zero_add]
    rw [Measure.volume_eq_prod]
    apply weightedAngular_integrable_off_zero volume measurableSet_closedBall measure_closedBall_lt_top.ne
      (angularFermat_contDiff r 0 1).continuous.measurable (c := 1) zero_lt_one
      (by intro y hy; simp [angularFermat, weightPowerSum]) 1 r s (lt_of_not_ge hs).le _ ε hε
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * (r : ℝ))).mp hcrit
    nlinarith

/-- The reduced odd-degree threshold holds at every positive depth, including one. -/
theorem odd_cancellationModel_all_depths_integrableOn_iff (r : ℕ) (hr : 3 ≤ r) (hodd : Odd r)
    (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ) :
    IntegrableOn (fun w : Fin L → ℝ => cancellationModel r w ^ (-s)) (ball 0 ε) volume ↔
      s < min ((L : ℝ) / (2 * r)) (((L : ℝ) + r) / (4 * r)) := by
  by_cases hL2 : 2 ≤ L
  · exact odd_cancellationModel_integrableOn_iff r hr hodd L hL2 ε hε hε1 s
  · have hL1 : L = 1 := by omega
    subst L
    rw [cancellationModel_one_integrableOn_iff r (by omega) ε hε hε1 s]
    have hr' : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    rw [min_eq_left]
    · norm_num
    · rw [div_le_div_iff₀ (by positivity : 0 < 2 * (r : ℝ)) (by positivity : 0 < 4 * (r : ℝ))]
      have hh : (3 : ℝ) ≤ r := by exact_mod_cast hr
      norm_num only [Nat.cast_one]
      nlinarith

/-- Restricting the local prior to a measurable cone does not add a density assumption. -/
theorem BoundedPositivePriorOn.mono {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {p : α → NNReal} {D E : Set α}
    (hp : BoundedPositivePriorOn p E μ) (hsub : D ⊆ E) : BoundedPositivePriorOn p D μ := by
  obtain ⟨c, C, hc, hb⟩ := hp.bounds
  refine ⟨hp.measurable, c, C, hc, ?_⟩
  exact ae_restrict_of_ae_restrict_of_subset hsub hb

/-- Direct divergence obstruction for the actual population loss: the interior
product witness is transported through the existing network/prior cone chart theorem. -/
theorem signed_network_prior_necessary_of_interior_zero (μ : Measure ℝ) (r n : ℕ)
    (hr : 2 ≤ r) (h : FinitePositiveFeatureGram μ (networkFeatures r (n + 2)))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (p : (Fin (n + 2) → ℝ) → NNReal) (hp : BoundedPositivePriorOn p (ball 0 ε) volume)
    (y : Fin (n + 1) → ℝ) (hy : y ∈ ball 0 1) (hz : angularFermat r 1 y = 0) (s : ℝ)
    (hi : IntegrableOn (fun w => networkPopulationLoss μ r w ^ (-s)) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal)))) :
    s < min (((n + 2 : ℕ) : ℝ) / (2 * r)) ((((n + 2 : ℕ) : ℝ) + r) / (4 * r)) := by
  obtain ⟨c, hyc, _⟩ := angularFermat_exists_chart r (n + 1) (by omega) 1 (by norm_num) y hz
  let D := ball (0 : Fin (n + 1) → ℝ) 1 ∩ c.chart.source
  have hD : IsOpen D := isOpen_ball.inter c.chart.open_source
  have hb : ∀ z ∈ D, ∀ i, |z i| ≤ 1 := by
    intro z hz i
    exact (norm_le_pi_norm z i).trans (mem_ball_zero_iff.mp hz.1).le
  have hcone := projectiveConePatch_subset_ball (0 : Fin (n + 2))
    (R := Ioo 0 ε) (fun _ h => h.1) (fun _ h => h.2) hb
  have hlocal := (signed_network_prior_transverse_cone_iff μ r hr h (0 : Fin (n + 2)) c
    measurableSet_Ioo (fun _ h => h.1) (fun _ h => h.2.trans_le hε1)
    hD.measurableSet hb inter_subset_right p (hp.mono hcone) s).mp (hi.mono_set hcone)
  obtain ⟨δ, hδ, hδ1, hinner⟩ := c.exists_inner_cylinder hD inter_subset_right ⟨hy, hyc⟩ hz
  have hrect := (angularCylinder_integrable_iff c.index (Ioo 0 ε) (Ioo (-δ) δ)
    (ball (fun i => y (c.index.succAbove i)) δ) measure_ball_lt_top.ne
    (measure_ball_pos volume _ hδ).ne' (weightedCancellation ((n + 1 : ℕ) + 1) r r s)).mp
      (hlocal.mono_set (prod_mono Subset.rfl hinner))
  have ht := (weightedCancellation_local_integrableOn_iff ((n + 1 : ℕ) + 1) (by positivity)
    r r (by omega) (by omega) ε δ hε hε1 hδ hδ1 s).mp hrect
  convert ht using 1
  push_cast
  congr 2 <;> ring

/-- End-to-end exact odd-degree population-loss threshold, with a measurable prior
bounded above and away from zero on the full raw neighborhood, at every positive depth. -/
theorem odd_network_prior_integrableOn_iff (μ : Measure ℝ) (r : ℕ) (hr : 3 ≤ r) (hodd : Odd r)
    (L : ℕ) (hL : 0 < L) (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (p : (Fin L → ℝ) → NNReal)
    (hp : BoundedPositivePriorOn p (ball 0 ε) volume) (s : ℝ) :
    IntegrableOn (fun w => networkPopulationLoss μ r w ^ (-s)) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal))) ↔
      s < min ((L : ℝ) / (2 * r)) (((L : ℝ) + r) / (4 * r)) := by
  constructor
  · intro hi
    by_cases hL3 : 3 ≤ L
    · obtain ⟨n, rfl⟩ : ∃ n, L = n + 3 := ⟨L - 3, by omega⟩
      obtain ⟨y, hy, hz⟩ := odd_angularFermat_interior_zero r (n + 2) (by omega) hodd (by omega)
      exact signed_network_prior_necessary_of_interior_zero μ r (n + 1) (by omega) h
        ε hε hε1 p hp y hy hz s hi
    · exact (odd_cancellationModel_all_depths_integrableOn_iff r hr hodd L hL ε hε hε1 s).mp
        ((signed_network_prior_integrableOn_iff_model μ r (by omega) L hL h ε hε1 p hp s).mp hi)
  · intro hs
    exact (signed_network_prior_integrableOn_iff_model μ r (by omega) L hL h ε hε1 p hp s).mpr
      ((odd_cancellationModel_all_depths_integrableOn_iff r hr hodd L hL ε hε hε1 s).mpr hs)


/-- The explicit three-regime formula for the actual network and its local prior. -/
theorem odd_network_prior_phase_transition (μ : Measure ℝ) (r : ℕ) (hr : 3 ≤ r) (hodd : Odd r)
    (L : ℕ) (hL : 0 < L) (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (p : (Fin L → ℝ) → NNReal)
    (hp : BoundedPositivePriorOn p (ball 0 ε) volume) (s : ℝ) :
    IntegrableOn (fun w => networkPopulationLoss μ r w ^ (-s)) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal))) ↔
      s < (if L < r then (L : ℝ) / (2 * r)
        else if L = r then 1 / 2 else ((L : ℝ) + r) / (4 * r)) := by
  rw [odd_network_prior_integrableOn_iff μ r hr hodd L hL h ε hε hε1 p hp s]
  have hm : IntegrableOn (weightedCancellation L r r s)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) volume ↔
      s < min ((L : ℝ) / (2 * r)) (((L : ℝ) + r) / (4 * r)) := by
    simpa only [show 2 * ((r : ℝ) + r) = 4 * r by ring] using
      weightedCancellation_symmetric_integrableOn_iff L (by exact_mod_cast hL) r r
        (by omega) (by omega) s
  exact hm.symm.trans (weightedNetworkModel_phase_transition L r hL (by omega) s)

/-- Raw Lebesgue version of the exact actual-network threshold. -/
theorem odd_network_integrableOn_iff (μ : Measure ℝ) (r : ℕ) (hr : 3 ≤ r) (hodd : Odd r)
    (L : ℕ) (hL : 0 < L) (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ) :
    IntegrableOn (fun w : Fin L → ℝ => networkPopulationLoss μ r w ^ (-s)) (ball 0 ε) volume ↔
      s < min ((L : ℝ) / (2 * r)) (((L : ℝ) + r) / (4 * r)) := by
  rw [signed_network_integrableOn_iff_model μ r (by omega) L hL h ε hε1 s]
  exact odd_cancellationModel_all_depths_integrableOn_iff r hr hodd L hL ε hε hε1 s

/-- The prior appears outside the singular power in the equivalent weighted-integrand form. -/
theorem odd_network_prior_weighted_integrableOn_iff (μ : Measure ℝ)
    (r : ℕ) (hr : 3 ≤ r) (hodd : Odd r) (L : ℕ) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (p : (Fin L → ℝ) → NNReal)
    (hp : BoundedPositivePriorOn p (ball 0 ε) volume) (s : ℝ) :
    IntegrableOn (fun w => (p w : ℝ) * networkPopulationLoss μ r w ^ (-s)) (ball 0 ε) volume ↔
      s < min ((L : ℝ) / (2 * r)) (((L : ℝ) + r) / (4 * r)) := by
  rw [← integrableOn_withDensity_iff_weighted measurableSet_ball hp.measurable]
  exact odd_network_prior_integrableOn_iff μ r hr hodd L hL h ε hε hε1 p hp s

/-- Threshold certificate includes a.e. strict positivity, excluding the totalized-zero trap. -/
theorem odd_network_threshold (μ : Measure ℝ) (r : ℕ) (hr : 3 ≤ r) (hodd : Odd r)
    (L : ℕ) (hL : 0 < L) (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasIntegrabilityThresholdOn (@networkPopulationLoss μ r L) (ball 0 ε) volume
      (min ((L : ℝ) / (2 * r)) (((L : ℝ) + r) / (4 * r))) := by
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  constructor
  · obtain ⟨c, C, hc, _, hb⟩ := signed_network_loss_comparison μ r (by omega) L hL h
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae ((volume : Measure (Fin L → ℝ)).ae_ne 0)] with w hw hn
    exact (mul_pos hc (cancellationModel_pos r L w hn)).trans_le (hb w (ball_subset_ball hε1 hw)).1
  · intro s _
    exact odd_network_integrableOn_iff μ r hr hodd L hL h ε hε hε1 s

/-- End-to-end certificate: input finiteness, exact population Gram formula, and
arbitrary-depth odd-degree threshold under the bounded positive prior. -/
theorem odd_network_certificate (μ : Measure ℝ) (r : ℕ) (hr : 3 ≤ r) (hodd : Odd r)
    (L : ℕ) (hL : 0 < L) (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (p : (Fin L → ℝ) → NNReal)
    (hp : BoundedPositivePriorOn p (ball 0 ε) volume) :
    (∀ w : Fin L → ℝ, Integrable (networkSquaredError r w) μ) ∧
    (∀ w : Fin L → ℝ, networkPopulationLoss μ r w =
      gramValue (featureGram μ (networkFeatures r L)) (networkCoefficients r w)) ∧
    HasIntegrabilityThresholdOn (@networkPopulationLoss μ r L) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal)))
      (min ((L : ℝ) / (2 * r)) (((L : ℝ) + r) / (4 * r))) := by
  exact ⟨network_squaredError_integrable μ r (by omega) L hL h,
    network_loss_eq_gram μ r (by omega) L hL h,
    (odd_network_threshold μ r hr hodd L hL h ε hε hε1).withDensity measurableSet_ball hp⟩

/-- Divergence at the threshold and every larger exponent for the actual network/prior. -/
theorem odd_network_prior_not_integrable (μ : Measure ℝ) (r : ℕ) (hr : 3 ≤ r) (hodd : Odd r)
    (L : ℕ) (hL : 0 < L) (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (p : (Fin L → ℝ) → NNReal)
    (hp : BoundedPositivePriorOn p (ball 0 ε) volume) (s : ℝ)
    (hs : min ((L : ℝ) / (2 * r)) (((L : ℝ) + r) / (4 * r)) ≤ s) :
    ¬ IntegrableOn (fun w => networkPopulationLoss μ r w ^ (-s)) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal))) := by
  rw [odd_network_prior_integrableOn_iff μ r hr hodd L hL h ε hε hε1 p hp s]
  exact not_lt.mpr hs

end ResidualSLT
