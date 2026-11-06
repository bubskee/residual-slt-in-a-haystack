module
public import ResidualSLT.SparseIdentityCertificate
public import ResidualSLT.LaplaceProduct

/-! The arrangement pair for a regular direction and two independent identity groups. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Metric Set

@[expose] def identityReferenceLoss (r n : ℕ) (w : Fin n → ℝ) : ℝ :=
  networkPopulationLoss
    (atomicInput (fun i : Fin (networkFeatureCount r n) => (i.val:ℝ)+1)) r w

@[expose] def oneActiveLearningPair (r p q : ℕ) : ℝ × ℕ :=
  (1/2+(identityLearningPair r p).1+(identityLearningPair r q).1,
    (identityLearningPair r p).2+(identityLearningPair r q).2-1)

@[expose] def oneActiveComparisonLoss (r p q : ℕ)
    (w : ℝ × (Fin p → ℝ) × (Fin q → ℝ)) : ℝ :=
  w.1^2+(identityReferenceLoss r p w.2.1+identityReferenceLoss r q w.2.2)

theorem identityLearningPair_zero (r : ℕ) (hr : 2 ≤ r) : identityLearningPair r 0 = (0,1) := by
  by_cases he : Even r <;> simp [identityLearningPair,he,show 0 < r by omega]

/-- Empty groups have integral one and pair (0,1). -/
theorem identityReferenceLoss_laplace_order (r n : ℕ) (hr : 2 ≤ r)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasLaplaceOrder (identityLearningPair r n).1 (identityLearningPair r n).2
      (fun N => ∫ w : Fin n → ℝ in ball 0 ε, Real.exp (-N*identityReferenceLoss r n w)) := by
  by_cases hn : n = 0
  · subst n
    rw [identityLearningPair_zero r hr]
    have hball : ball (0:Fin 0 → ℝ) ε = univ := by
      ext w
      simp [show w = 0 from Subsingleton.elim _ _,hε]
    refine ⟨by norm_num,1,1,2,by norm_num,by norm_num,by norm_num,?_⟩
    intro N _
    rw [hball]
    simp [identityReferenceLoss,networkPopulationLoss,networkSquaredError,network,laplaceRate,Measure.real,MeasureTheory.volume_pi]
  · have hρ : BoundedPositivePriorOn (fun _ : Fin n → ℝ => (1:NNReal)) (ball 0 ε) volume :=
      ⟨measurable_const,1,1,by norm_num,Filter.Eventually.of_forall (fun _ => ⟨le_rfl,le_rfl⟩)⟩
    have hh := identity_network_laplace_order _ r n hr (by omega) (network_atomic_gram r n)
      ε hε hε1 _ hρ
    have hvol : (volume : Measure (Fin n → ℝ)).withDensity (fun _ => (1:ENNReal)) = volume :=
      withDensity_one
    simpa only [identityReferenceLoss,ENNReal.coe_one,hvol] using hh

/-- Explicit two-sided Laplace bounds for the whole one-active comparison model.
The full product neighborhood includes both signs and empty or singleton inactive groups. -/
theorem oneActiveComparisonLoss_laplace_order (r p q : ℕ) (hr : 2 ≤ r)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasLaplaceOrder (oneActiveLearningPair r p q).1 (oneActiveLearningPair r p q).2
      (fun N => ∫ w : ℝ × (Fin p → ℝ) × (Fin q → ℝ) in ball 0 ε,
        Real.exp (-N*oneActiveComparisonLoss r p q w)) := by
  have hp := identityReferenceLoss_laplace_order r p hr ε hε hε1
  have hq := identityReferenceLoss_laplace_order r q hr ε hε hε1
  have hg : HasLaplaceOrder (1/2) 1
      (fun N => ∫ x : ℝ in ball 0 ε, Real.exp (-N*x^2)) := by
    have hh := (normPower_laplace_order (volume : Measure ℝ) 1 (by norm_num) ε hε).toLaplaceOrder
    simpa using hh
  have hh := laplace_order_add_prod (volume : Measure ℝ)
    ((volume : Measure (Fin p → ℝ)).prod (volume : Measure (Fin q → ℝ)))
    (fun x => x^2) (fun w => identityReferenceLoss r p w.1+identityReferenceLoss r q w.2)
    (ball 0 ε) ((ball 0 ε) ×ˢ (ball 0 ε)) hg
    (laplace_order_add_prod volume volume _ _ (ball 0 ε) (ball 0 ε) hp hq)
  simpa only [← Measure.volume_eq_prod,ball_prod_same,oneActiveLearningPair,
    oneActiveComparisonLoss,Prod.fst,Prod.snd,add_assoc,Nat.add_sub_cancel_left,Prod.zero_eq_mk] using hh

end ResidualSLT
