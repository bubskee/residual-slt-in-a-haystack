module
public import ResidualSLT.OneActiveComposition
public import ResidualSLT.ArrangementJet

/-! A finite-dimensional composition map with arbitrarily many active blocks and groups. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset ContinuousLinearMap

abbrev ArrangementAux (k : ℕ) (d : Fin (k+1) → ℕ) :=
  (Fin k → ℝ) × (∀ g : Fin (k+1), Fin (d g) → ℝ)

@[expose] def arrangementActiveL (k : ℕ) (d : Fin (k+1) → ℕ) (j : ℕ) :
    ArrangementAux k d →L[ℝ] ℝ :=
  if hj : j<k then (proj ⟨j,hj⟩).comp (fst ℝ _ _) else 0

@[expose] def arrangementGroupL (r k : ℕ) (d : Fin (k+1) → ℕ) (g : ℕ) (x : ℝ) :
    ArrangementAux k d →L[ℝ] ℝ :=
  if hg : g<k+1 then (gradedEvalL r (d ⟨g,hg⟩) x).comp ((proj (⟨g,hg⟩ : Fin (k+1))).comp (snd ℝ _ _)) else 0

@[expose] def arrangementAuxEval (r k : ℕ) (d : Fin (k+1) → ℕ) (c : ℕ → ℝ)
    (x : ℝ) : ℕ → ArrangementAux k d → ℝ
  | 0, v => x+arrangementGroupL r k d 0 x v
  | n+1, v =>
    let y := arrangementAuxEval r k d c x n v
    let z := y+(c n+arrangementActiveL k d n v)*y^r
    z+arrangementGroupL r k d (n+1) z v

@[expose] def arrangementAuxDeriv (r k : ℕ) (d : Fin (k+1) → ℕ) (c : ℕ → ℝ)
    (x : ℝ) : ℕ → ArrangementAux k d →L[ℝ] ℝ
  | 0 => arrangementGroupL r k d 0 x
  | n+1 =>
    (1+(r:ℝ)*c n*((network r c n).eval x)^(r-1)) • arrangementAuxDeriv r k d c x n +
      ((network r c n).eval x)^r • arrangementActiveL k d n +
      arrangementGroupL r k d (n+1) ((network r c (n+1)).eval x)

@[simp] theorem arrangementAuxEval_zero (r k : ℕ) (d : Fin (k+1) → ℕ) (c : ℕ → ℝ)
    (x : ℝ) (n : ℕ) : arrangementAuxEval r k d c x n 0 = (network r c n).eval x := by
  induction n with
  | zero => simp [arrangementAuxEval,network]
  | succ n ih => simp [arrangementAuxEval,ih,network]

/-- Varying the group input causes no extra first-order term because its coefficients vanish at zero. -/
theorem arrangementGroup_hasFDerivAt (r k : ℕ) (d : Fin (k+1) → ℕ) (g : ℕ)
    (Y : ArrangementAux k d → ℝ) (D : ArrangementAux k d →L[ℝ] ℝ)
    (hY : HasFDerivAt Y D 0) :
    HasFDerivAt (fun v => arrangementGroupL r k d g (Y v) v)
      (arrangementGroupL r k d g (Y 0)) 0 := by
  by_cases hg : g<k+1
  · simp only [arrangementGroupL,dite_eq_left hg,comp_apply,proj_apply,coe_snd',gradedEvalL_apply]
    let G : ArrangementAux k d →L[ℝ] (Fin (d ⟨g,hg⟩) → ℝ) :=
      (proj (⟨g,hg⟩ : Fin (k+1))).comp (snd ℝ _ _)
    have hG (j : Fin (d ⟨g,hg⟩)) : HasFDerivAt (fun v : ArrangementAux k d => v.2 ⟨g,hg⟩ j)
        ((proj j).comp G) 0 := ((proj j).comp G).hasFDerivAt
    have hh := HasFDerivAt.fun_sum (u := univ) (fun j (_ : j ∈ (univ : Finset (Fin (d ⟨g,hg⟩)))) =>
      (hG j).mul (hY.pow (r+j.val*(r-1))))
    apply hh.congr_fderiv
    apply ContinuousLinearMap.ext
    intro v
    simp [gradedEvalL,G]
  · simp only [arrangementGroupL,dite_eq_right hg,zero_apply]
    exact (hasFDerivAt_const (c := (0:ℝ)) (0 : ArrangementAux k d))

/-- Exact differential of the arbitrary-active-count finite auxiliary composition. -/
theorem arrangementAuxEval_hasFDerivAt (r k : ℕ) (d : Fin (k+1) → ℕ) (c : ℕ → ℝ)
    (x : ℝ) (n : ℕ) :
    HasFDerivAt (arrangementAuxEval r k d c x n) (arrangementAuxDeriv r k d c x n) 0 := by
  induction n with
  | zero => exact (arrangementGroupL r k d 0 x).hasFDerivAt.const_add x
  | succ n ih =>
    let Y := arrangementAuxEval r k d c x n
    let Z : ArrangementAux k d → ℝ := fun v => Y v+(c n+arrangementActiveL k d n v)*(Y v)^r
    let DZ := (1+(r:ℝ)*c n*((network r c n).eval x)^(r-1)) • arrangementAuxDeriv r k d c x n +
      ((network r c n).eval x)^r • arrangementActiveL k d n
    have hZ : HasFDerivAt Z DZ 0 := by
      apply (ih.add (((arrangementActiveL k d n).hasFDerivAt.const_add (c n)).mul (ih.pow r))).congr_fderiv
      apply ContinuousLinearMap.ext
      intro v
      simp [DZ,arrangementAuxEval_zero,nsmul_eq_mul]
      ring
    have hZ0 : Z 0=(network r c (n+1)).eval x := by simp [Z,Y,network]
    have hh := hZ.fun_add (arrangementGroup_hasFDerivAt r k d (n+1) Z DZ hZ)
    simpa only [hZ0,arrangementAuxEval,arrangementAuxDeriv,DZ,Z,Y,Pi.add_apply] using hh

end ResidualSLT
