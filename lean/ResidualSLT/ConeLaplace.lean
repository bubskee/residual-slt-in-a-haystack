module
public import ResidualSLT.AngularLaplace
public import ResidualSLT.HomogeneousCone

/-! Quantitative assembly of critical Laplace bounds over signed projective cones. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Filter Metric

/-- The norm model has exactly the critical angular integral on each unit projective patch. -/
theorem criticalFermat_projective_integral {n : ℕ} (r : ℕ) (hdim : n+1 = r)
    (j : Fin (n+1)) (ε N : ℝ) :
    (∫ w in projectiveConePatch j (Ioo 0 ε) (closedBall 0 1),
      Real.exp (-N * homogeneousConeLoss (weightPowerSum r) (r+r) w)) =
    ∫ z : ℝ × (Fin n → ℝ) in Ioo 0 ε ×ˢ closedBall 0 1, criticalAngularKernel r (angularFermat r 1) N z := by
  let M := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) j
  have hD : MeasurableSet (M ⁻¹' (Ioo 0 ε ×ˢ closedBall 0 1)) :=
    (measurableSet_Ioo.prod measurableSet_closedBall).preimage M.measurable
  have hp : ∀ z ∈ M ⁻¹' (Ioo 0 ε ×ˢ closedBall 0 1), 0 < z j := fun _ hz => hz.1.1
  rw [projectiveConePatch, radialBlowup_integral_image j hD hp]
  have heq : EqOn (fun z : Fin (n+1) → ℝ => z j ^ (n+1-1) *
      Real.exp (-N * homogeneousConeLoss (weightPowerSum r) (r+r) (radialBlowup j z)))
      (fun z => criticalAngularKernel r (angularFermat r 1) N (M z))
      (M ⁻¹' (Ioo 0 ε ×ˢ closedBall 0 1)) := by
    intro z hz
    have hb : ∀ i, i ≠ j → |z i| ≤ 1 := by
      intro i hi
      obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hi
      exact (norm_le_pi_norm (M z).2 k).trans (mem_closedBall_zero_iff.mp hz.2)
    have h := homogeneousConeLoss_radial_bounds (weightPowerSum r) r r
      (weightPowerSum_smul r (n+1)) j z (hp z hz) 1 le_rfl hb
    simp only [one_pow,one_mul] at h
    have he := le_antisymm h.2 h.1
    dsimp only
    rw [he, weightPowerSum_fixed_coordinate]
    simp only [criticalAngularKernel,hdim]
    rfl
  rw [setIntegral_congr_fun hD heq]
  exact (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) j).setIntegral_preimage_emb
    M.measurableEmbedding _ _

/-- Continuous even losses can be assembled from finitely many signed cone estimates.
Overlaps only enlarge the upper bound; one actual cone supplies the lower bound. -/
theorem laplace_order_of_projective_cones {n : ℕ} (K : (Fin (n+1) → ℝ) → ℝ)
    (hK : Continuous K) (heven : ∀ w, K (-w) = K w) (ε : ℝ)
    (hcones : ∀ j : Fin (n+1), HasCriticalLaplaceOrder (fun N =>
      ∫ w in projectiveConePatch j (Ioo 0 ε) (closedBall 0 1), Real.exp (-N*K w))) :
    HasCriticalLaplaceOrder (fun N => ∫ w in ball 0 ε, Real.exp (-N*K w)) := by
  classical
  let P := fun j : Fin (n+1) => projectiveConePatch j (Ioo 0 ε) (closedBall 0 1)
  have hm (j) : MeasurableSet (P j) := projectiveConePatch_measurableSet j
    measurableSet_Ioo (fun _ h => h.1) measurableSet_closedBall
  have hsub (j) : P j ⊆ ball 0 ε := projectiveConePatch_subset_ball j
    (fun _ h => h.1) (fun _ h => h.2)
    (fun y hy i => (norm_le_pi_norm y i).trans (mem_closedBall_zero_iff.mp hy))
  have hnsub (j) : Neg.neg '' P j ⊆ ball 0 ε := by
    rintro w ⟨v,hv,rfl⟩
    simpa using hsub j hv
  have hi (N : ℝ) : IntegrableOn (fun w => Real.exp (-N*K w)) (ball 0 ε) volume :=
    ((by fun_prop : Continuous (fun w => Real.exp (-N*K w))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall
  have hneg (j) (N : ℝ) :
      (∫ w in Neg.neg '' P j, Real.exp (-N*K w)) = ∫ w in P j, Real.exp (-N*K w) := by
    rw [(Measure.measurePreserving_neg (volume : Measure (Fin (n+1) → ℝ))).setIntegral_image_emb
      (Homeomorph.neg (Fin (n+1) → ℝ)).measurableEmbedding]
    simp only [heven]
  constructor
  · apply (hcones 0).1.mono
    exact Filter.Eventually.of_forall fun N => setIntegral_mono_set (hi N)
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
      (Filter.Eventually.of_forall (hsub 0))
  · have hsum := CriticalLaplaceUpper.finset_sum (Finset.univ : Finset (Fin (n+1)))
      (fun j N => (∫ w in P j, Real.exp (-N*K w)) + ∫ w in Neg.neg '' P j, Real.exp (-N*K w))
      (fun j _ => (hcones j).2.add (by simpa only [hneg] using (hcones j).2))
    apply (criticalLaplaceUpper_zero.add hsum).mono
    apply Filter.Eventually.of_forall
    intro N
    let g := fun w => Real.exp (-N*K w)
    have hbound (j) : (∫ w in P j ∪ Neg.neg '' P j, g w) ≤
        (∫ w in P j, g w) + ∫ w in Neg.neg '' P j, g w := by
      have hnm : MeasurableSet (Neg.neg '' P j) :=
        (Homeomorph.neg _).measurableEmbedding.measurableSet_image.mpr (hm j)
      have hh := setIntegral_le_add_sum_of_cover volume ({()} : Finset Unit) g
        (P j ∪ Neg.neg '' P j) (P j) (fun _ => Neg.neg '' P j)
        ((hm j).union hnm) (hm j) (fun _ _ => hnm)
        (((hi N).mono_set (hsub j)).union ((hi N).mono_set (hnsub j)))
        ((hi N).mono_set (hsub j)) (fun _ _ => (hi N).mono_set (hnsub j))
        (by
          intro w hw
          rcases hw with hw | hw
          · exact Or.inl hw
          · exact Or.inr (mem_iUnion₂.mpr ⟨(),by simp,hw⟩))
        (fun _ _ => (Real.exp_pos _).le)
      simpa using hh
    have hcover : ball 0 ε ⊆ {0} ∪ ⋃ j ∈ (Finset.univ : Finset (Fin (n+1))), P j ∪ Neg.neg '' P j := by
      intro w hw
      by_cases hz : w = 0
      · exact Or.inl hz
      · obtain ⟨j,z,hz0,hzε,hza,hwz⟩ := signed_radialBlowup_cover ε w hw hz
        have hp : radialBlowup j z ∈ P j := by
          refine ⟨z, ?_, rfl⟩
          change (z j ∈ Ioo 0 ε) ∧ (fun i => z (j.succAbove i)) ∈ closedBall 0 1
          refine ⟨⟨hz0,hzε⟩, ?_⟩
          rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
          intro i
          exact hza _ (Fin.succAbove_ne j i)
        apply Or.inr
        apply mem_iUnion₂.mpr
        refine ⟨j,Finset.mem_univ _,?_⟩
        rcases hwz with hwz | hwz
        · exact Or.inl (hwz.symm ▸ hp)
        · exact Or.inr ⟨radialBlowup j z,hp,hwz.symm⟩
    have h := setIntegral_le_add_sum_of_cover volume Finset.univ g (ball 0 ε) {0}
      (fun j => P j ∪ Neg.neg '' P j) measurableSet_ball (measurableSet_singleton 0)
      (fun j _ => (hm j).union ((Homeomorph.neg _).measurableEmbedding.measurableSet_image.mpr (hm j)))
      (hi N) (integrableOn_singleton (hx := by simp))
      (fun j _ => ((hi N).mono_set (hsub j)).union ((hi N).mono_set (hnsub j))) hcover
      (fun _ _ => (Real.exp_pos _).le)
    simp only [integral_singleton, Measure.real, measure_singleton, ENNReal.toReal_zero, zero_smul, zero_add] at h
    simpa only [zero_add] using h.trans (Finset.sum_le_sum (fun j _ => hbound j))

/-- Odd critical Fermat loss: the full raw neighborhood has logarithmic multiplicity two. -/
theorem criticalFermat_laplace_order (r : ℕ) (hr : 3 ≤ r) (hodd : Odd r)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasCriticalLaplaceOrder (fun N => ∫ w : Fin r → ℝ in ball 0 ε,
      Real.exp (-N * homogeneousConeLoss (weightPowerSum r) (r+r) w)) := by
  obtain ⟨n,rfl⟩ : ∃ n, r = n+2 := ⟨r-2,by omega⟩
  apply laplace_order_of_projective_cones _ (by unfold homogeneousConeLoss weightPowerSum; fun_prop)
    (fun w => homogeneousConeLoss_neg (weightPowerSum (n+2)) (n+2) ((n+2)+(n+2))
      (weightPowerSum_smul (n+2) (n+2)) w) ε
  intro j
  simp only [criticalFermat_projective_integral (n+2) rfl j]
  exact criticalAngular_has_order (n+2) n (by omega) (angularFermat (n+2) 1)
    (angularFermat_contDiff (n+2) (n+1) 1) ε hε hε1
    (fun y _ hy => angularFermat_zero_regular (n+2) (n+1) (by omega) 1 one_ne_zero y hy)
    (odd_angularFermat_interior_zero (n+2) (n+1) (by omega) hodd (by omega))

end ResidualSLT
