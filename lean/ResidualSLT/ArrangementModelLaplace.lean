module
public import ResidualSLT.FiniteLaplaceProduct
public import ResidualSLT.OneActiveModelLaplace
public import ResidualSLT.ArrangementComposition

/-! Arbitrary-active-count arrangement pair for the product comparison model. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Metric Set Finset

@[expose] def arrangementLearningPair (r k : ℕ) (n : Fin (k+1) → ℕ) : ℝ × ℕ :=
  ((k:ℝ)/2+∑ g,(identityLearningPair r (n g)).1,
    1+∑ g,((identityLearningPair r (n g)).2-1))

@[expose] def arrangementComparisonLoss (r k : ℕ) (n : Fin (k+1) → ℕ)
    (w : ArrangementAux k n) : ℝ :=
  (∑ j,w.1 j^2)+(∑ g,identityReferenceLoss r (n g) (w.2 g))

/-- All regular directions and all inactive groups factor on the full product ball. -/
theorem arrangementComparisonLoss_laplace_order (r k : ℕ) (hr : 2 ≤ r)
    (n : Fin (k+1) → ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasLaplaceOrder (arrangementLearningPair r k n).1 (arrangementLearningPair r k n).2
      (fun N => ∫ w : ArrangementAux k n in ball 0 ε, Real.exp (-N*arrangementComparisonLoss r k n w)) := by
  have hg : HasLaplaceOrder (1/2) 1 (fun N => ∫ x : ℝ in ball 0 ε, Real.exp (-N*x^2)) := by
    have hh := (normPower_laplace_order (volume : Measure ℝ) 1 (by norm_num) ε hε).toLaplaceOrder
    simpa using hh
  have ha := laplace_order_sum_pi (fun _ : Fin k => (volume : Measure ℝ)) (fun _ x => x^2)
    (fun _ => ball 0 ε) (fun _ => (1/2:ℝ)) (fun _ => 1) (fun _ => hg)
  have hp := laplace_order_sum_pi (fun g : Fin (k+1) => (volume : Measure (Fin (n g) → ℝ)))
    (fun g => identityReferenceLoss r (n g)) (fun _ => ball 0 ε)
    (fun g => (identityLearningPair r (n g)).1) (fun g => (identityLearningPair r (n g)).2)
    (fun g => identityReferenceLoss_laplace_order r (n g) hr ε hε hε1)
  have hba : Set.pi univ (fun _ : Fin k => ball (0:ℝ) ε) = ball (0:Fin k → ℝ) ε := by
    simpa only [Pi.zero_apply] using (ball_pi (0:Fin k → ℝ) hε).symm
  have hbg : Set.pi univ (fun g : Fin (k+1) => ball (0:Fin (n g) → ℝ) ε) =
      ball (0:∀ g : Fin (k+1),Fin (n g) → ℝ) ε := by
    simpa only [Pi.zero_apply] using (ball_pi (0:∀ g : Fin (k+1),Fin (n g) → ℝ) hε).symm
  simp only [← MeasureTheory.volume_pi,hba,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.sub_self,Nat.mul_zero,Nat.add_zero] at ha
  simp only [← MeasureTheory.volume_pi,hbg] at hp
  have hh := laplace_order_add_prod volume volume _ _ (ball 0 ε) (ball 0 ε) ha hp
  simpa only [← Measure.volume_eq_prod,ball_prod_same,Prod.zero_eq_mk,arrangementComparisonLoss,
    arrangementLearningPair,Prod.fst,Prod.snd,Nat.add_sub_cancel_left,div_eq_mul_inv,one_div,one_mul] using hh

end ResidualSLT
