module
public import ResidualSLT.SmallRawFiber
public import ResidualSLT.ArrangementGlobalPair

/-! Every one- or two-active raw realization is an instance of the arrangement certificate. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial MeasureTheory Metric Set

theorem arrangement_one_depth (p q : ℕ) : arrangementDepth 1 ![p,q] 1 le_rfl = p+1+q := by
  simp [arrangementDepth]

theorem arrangement_two_depth (p q s : ℕ) : arrangementDepth 2 ![p,q,s] 2 le_rfl = p+1+q+1+s := by
  simp [arrangementDepth]

theorem arrangement_one_center (p q : ℕ) (α : ℝ)
    (i : Fin (arrangementDepth 1 ![p,q] 1 le_rfl)) :
    arrangementFlatten 1 ![p,q] ![α] 0 1 le_rfl i = if i.val=p then α else 0 := by
  change (if i.val<p then (0:ℝ) else if i.val=p then α+0 else 0) = _
  simp only [add_zero]
  split_ifs <;> simp_all

theorem arrangement_two_center (p q s : ℕ) (α β : ℝ)
    (i : Fin (arrangementDepth 2 ![p,q,s] 2 le_rfl)) :
    arrangementFlatten 2 ![p,q,s] ![α,β] 0 2 le_rfl i =
      if i.val=p then α else if i.val=p+1+q then β else 0 := by
  change (if i.val<p+1+q then (if i.val<p then (0:ℝ) else if i.val=p then α+0 else 0)
    else if i.val=p+1+q then β+0 else 0) = _
  simp only [add_zero]
  by_cases hi : i.val=p
  · have hlt : i.val<p+1+q := by omega
    simp only [ite_eq_left hi,ite_eq_left hlt,ite_eq_right (show ¬i.val<p by omega)]
  · by_cases hj : i.val=p+1+q
    · simp only [ite_eq_right hi,ite_eq_left hj,ite_eq_right (show ¬i.val<p+1+q by omega)]
    · by_cases hlt : i.val<p+1+q
      · simp only [ite_eq_left hlt,ite_eq_right hi,ite_eq_right hj,ite_self]
      · simp only [ite_eq_right hlt,ite_eq_right hi,ite_eq_right hj]

/-- Reindexing equal finite depths adds no measure assumption. -/
theorem arrangement_raw_certificate_at (μ : Measure ℝ) (r L k : ℕ) (hr : 2 ≤ r) (hL : 0<L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ) (hτ : ∀ j,τ j≠0)
    (hd : arrangementDepth k n k le_rfl=L) (t : Fin L → ℝ)
    (ht : ∀ i : Fin (arrangementDepth k n k le_rfl), t (Fin.cast hd i)=arrangementFlatten k n τ 0 k le_rfl i) :
    ∃ ε₀ : ℝ, 0<ε₀ ∧ ε₀≤1 ∧ ∀ ε : ℝ, 0<ε → ε≤ε₀ →
      ∀ ρ : (Fin L → ℝ) → NNReal, BoundedPositivePriorOn ρ (ball t ε) volume →
      HasLaplaceOrder (arrangementLearningPair r k n).1 (arrangementLearningPair r k n).2
        (fun N => ∫ w in ball t ε, Real.exp (-N*networkTargetLoss μ r t w)
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  subst L
  have ht' : t=arrangementFlatten k n τ 0 k le_rfl := funext ht
  subst t
  obtain ⟨ε₀,hε₀,hε₀1,hcert⟩ := arrangement_raw_network_rlct_laplace_certificate_of_depth_pos μ r k hr n hL hμ τ hτ
  exact ⟨ε₀,hε₀,hε₀1,fun ε hε hs ρ hρ => (hcert ε hε hs ρ hρ).2⟩

/-- A one-active realization has its exact before/after group lengths. -/
theorem one_active_realization_arrangement (r L : ℕ) (hr : 2 ≤ r) (c : ℝ) (hc : c≠0)
    (w : Fin L → ℝ) (hw : network r (fun i => zeroExtend w i^r) L=activeTarget r c) :
    ∃ n : Fin 2 → ℕ, ∃ τ : Fin 1 → ℝ,
      (∀ j,τ j≠0) ∧ (∑ g,n g)=L-1 ∧
      ∃ hd : arrangementDepth 1 n 1 le_rfl=L,
        ∀ i : Fin (arrangementDepth 1 n 1 le_rfl), w (Fin.cast hd i)=arrangementFlatten 1 n τ 0 1 le_rfl i := by
  obtain ⟨j,hj,hz⟩ := (one_active_raw_fiber r L hr c hc w).mp hw
  let p := j.val
  let q := L-(j.val+1)
  have hdepth : arrangementDepth 1 ![p,q] 1 le_rfl=L := by rw [arrangement_one_depth]; dsimp [p,q]; omega
  have hnz : w j≠0 := by intro he; rw [he,zero_pow (by omega : r≠0)] at hj; exact hc hj.symm
  refine ⟨![p,q],![w j],?_,?_,hdepth,?_⟩
  · intro a; fin_cases a; exact hnz
  · simp [Fin.sum_univ_two,p,q]; omega
  · intro i
    rw [arrangement_one_center]
    split_ifs with hi
    · have he : Fin.cast hdepth i=j := Fin.ext hi
      rw [he]
    · apply hz
      intro he
      exact hi (congrArg Fin.val he)

/-- A two-active realization has the exact three chronological inactive groups. -/
theorem two_active_realization_arrangement (r L : ℕ) (hr : 2 ≤ r) (c d : ℝ) (hc : c≠0) (hd : d≠0)
    (w : Fin L → ℝ) (hw : network r (fun i => zeroExtend w i^r) L=twoActiveTarget r c d) :
    ∃ n : Fin 3 → ℕ, ∃ τ : Fin 2 → ℝ,
      (∀ j,τ j≠0) ∧ (∑ g,n g)=L-2 ∧
      ∃ he : arrangementDepth 2 n 2 le_rfl=L,
        ∀ i : Fin (arrangementDepth 2 n 2 le_rfl), w (Fin.cast he i)=arrangementFlatten 2 n τ 0 2 le_rfl i := by
  obtain ⟨i,j,hij,hi,hj,hz⟩ := (two_active_raw_fiber r L hr c d hc hd w).mp hw
  let p := i.val
  let q := j.val-(i.val+1)
  let s := L-(j.val+1)
  have hpq : p+1+q=j.val := by dsimp [p,q]; exact Nat.add_sub_of_le (by exact hij)
  have hdepth : arrangementDepth 2 ![p,q,s] 2 le_rfl=L := by rw [arrangement_two_depth,hpq]; dsimp [s]; omega
  have hni : w i≠0 := by intro he; rw [he,zero_pow (by omega : r≠0)] at hi; exact hc hi.symm
  have hnj : w j≠0 := by intro he; rw [he,zero_pow (by omega : r≠0)] at hj; exact hd hj.symm
  refine ⟨![p,q,s],![w i,w j],?_,?_,hdepth,?_⟩
  · intro a; fin_cases a <;> assumption
  · simp [Fin.sum_univ_succ,p,q,s]; have hi' := i.isLt; have hj' := j.isLt; have hij' : i.val<j.val := hij; omega
  · intro a
    rw [arrangement_two_center]
    split_ifs with hai haj
    · have he : Fin.cast hdepth a=i := Fin.ext hai
      rw [he]
    · have he : Fin.cast hdepth a=j := Fin.ext (haj.trans hpq)
      rw [he]
    · apply hz
      · intro he; exact hai (congrArg Fin.val he)
      · intro he; exact haj ((congrArg Fin.val he).trans hpq.symm)

end ResidualSLT
