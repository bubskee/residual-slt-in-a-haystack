module
public import ResidualSLT.OneActiveDirections
public import ResidualSLT.ControlledLinearization
public import Mathlib.Analysis.Calculus.FDeriv.Pow

/-! The auxiliary finite-dimensional one-active composition and its exact differential. -/
public section
noncomputable section
namespace ResidualSLT
open Finset
open ContinuousLinearMap

abbrev OneActiveAux (a b : ℕ) := ℝ × (Fin a → ℝ) × (Fin b → ℝ)

@[expose] def gradedEvalL (r a : ℕ) (x : ℝ) : (Fin a → ℝ) →L[ℝ] ℝ :=
  ∑ j : Fin a, x^(r+j.val*(r-1)) • ContinuousLinearMap.proj j

theorem gradedEvalL_apply (r a : ℕ) (x : ℝ) (u : Fin a → ℝ) :
    gradedEvalL r a x u = ∑ j, u j*x^(r+j.val*(r-1)) := by
  simp [gradedEvalL,mul_comm]

@[expose] def auxActiveL (a b : ℕ) : OneActiveAux a b →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ _
@[expose] def auxPreL (a b : ℕ) : OneActiveAux a b →L[ℝ] (Fin a → ℝ) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ ℝ _)
@[expose] def auxPostL (a b : ℕ) : OneActiveAux a b →L[ℝ] (Fin b → ℝ) :=
  (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ ℝ _)

@[expose] def oneActiveAuxPre (r a b : ℕ) (x : ℝ) (v : OneActiveAux a b) : ℝ :=
  x+(gradedEvalL r a x) (auxPreL a b v)
@[expose] def oneActiveAuxMiddle (r a b : ℕ) (c x : ℝ) (v : OneActiveAux a b) : ℝ :=
  oneActiveAuxPre r a b x v+(c+auxActiveL a b v)*(oneActiveAuxPre r a b x v)^r
@[expose] def oneActiveAuxEval (r a b : ℕ) (c x : ℝ) (v : OneActiveAux a b) : ℝ :=
  oneActiveAuxMiddle r a b c x v+
    ∑ j : Fin b, auxPostL a b v j*(oneActiveAuxMiddle r a b c x v)^(r+j.val*(r-1))

@[expose] def oneActiveAuxDeriv (r a b : ℕ) (c x : ℝ) : OneActiveAux a b →L[ℝ] ℝ :=
  x^r • auxActiveL a b +
    (1+(r:ℝ)*c*x^(r-1)) • (gradedEvalL r a x).comp (auxPreL a b) +
    (gradedEvalL r b (x+c*x^r)).comp (auxPostL a b)

/-- The differential is explicit on arbitrary auxiliary coefficient perturbations,
not only along raw network parameters. -/
theorem oneActiveAuxEval_hasFDerivAt (r a b : ℕ) (c x : ℝ) :
    HasFDerivAt (oneActiveAuxEval r a b c x) (oneActiveAuxDeriv r a b c x) 0 := by
  let A := (gradedEvalL r a x).comp (auxPreL a b)
  let T := auxActiveL a b
  have hA : HasFDerivAt (oneActiveAuxPre r a b x) A 0 :=
    A.hasFDerivAt.const_add x
  have hT : HasFDerivAt (fun v => c+auxActiveL a b v) T 0 :=
    T.hasFDerivAt.const_add c
  let Y := oneActiveAuxMiddle r a b c x
  let DY : OneActiveAux a b →L[ℝ] ℝ := x^r • T + (1+(r:ℝ)*c*x^(r-1)) • A
  have hY : HasFDerivAt Y DY 0 := by
    apply (hA.add (hT.mul (hA.pow r))).congr_fderiv
    apply ContinuousLinearMap.ext
    intro v
    simp [DY,T,A,oneActiveAuxPre,auxActiveL,nsmul_eq_mul]
    ring
  have hY0 : Y 0 = x+c*x^r := by simp [Y,oneActiveAuxMiddle,oneActiveAuxPre]
  have hpost : HasFDerivAt
      (fun v => ∑ j : Fin b, auxPostL a b v j*(Y v)^(r+j.val*(r-1)))
      ((gradedEvalL r b (x+c*x^r)).comp (auxPostL a b)) 0 := by
    have hh := HasFDerivAt.fun_sum (u := univ) (fun j (_ : j ∈ (univ : Finset (Fin b))) =>
      (((ContinuousLinearMap.proj j).comp (auxPostL a b)).hasFDerivAt).mul
        (hY.pow (r+j.val*(r-1))))
    apply hh.congr_fderiv
    apply ContinuousLinearMap.ext
    intro v
    simp [gradedEvalL,auxPostL,hY0]
  exact hY.add hpost

/-- A finite family of observation values has the corresponding vector differential. -/
theorem oneActiveAuxEval_pi_hasFDerivAt {ι : Type*} [Fintype ι]
    (r a b : ℕ) (c : ℝ) (x : ι → ℝ) :
    HasFDerivAt (fun v i => oneActiveAuxEval r a b c (x i) v)
      (ContinuousLinearMap.pi (fun i => oneActiveAuxDeriv r a b c (x i))) 0 :=
  hasFDerivAt_pi.mpr (fun i => oneActiveAuxEval_hasFDerivAt r a b c (x i))

end ResidualSLT
