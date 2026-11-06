module
public import ResidualSLT.OneActiveNetwork
public import ResidualSLT.OneActiveRawLinearization

/-! Reassemble the raw before/active/after parameters into the chronological network. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial

@[expose] def oneActiveAssemble (p q : ℕ) (τ : ℝ) (w : OneActiveAux p q) :
    Fin (p+1+q) → ℝ := fun i =>
  if hi : i.val < p then w.2.1 ⟨i.val,hi⟩ else
  if he : i.val=p then τ+w.1 else w.2.2 ⟨i.val-(p+1),by have hh := i.isLt; omega⟩

theorem oneActiveAssemble_pre (p q : ℕ) (τ : ℝ) (w : OneActiveAux p q) (i : ℕ) (hi : i < p) :
    zeroExtend (oneActiveAssemble p q τ w) i = zeroExtend w.2.1 i := by
  simp [zeroExtend,oneActiveAssemble,hi,show i < p+1+q by omega]

theorem oneActiveAssemble_active (p q : ℕ) (τ : ℝ) (w : OneActiveAux p q) :
    zeroExtend (oneActiveAssemble p q τ w) p = τ+w.1 := by
  simp [zeroExtend,oneActiveAssemble,show p < p+1+q by omega]

theorem oneActiveAssemble_post (p q : ℕ) (τ : ℝ) (w : OneActiveAux p q) (i : ℕ) (hi : i < q) :
    zeroExtend (oneActiveAssemble p q τ w) (p+1+i) = zeroExtend w.2.2 i := by
  simp [zeroExtend,oneActiveAssemble,hi,show p+1+i < p+1+q by omega,
    show ¬ p+1+i < p by omega,show p+1+i ≠ p by omega]

theorem zeroExtend_pow (n r : ℕ) (hr : 0 < r) (u : Fin n → ℝ) :
    zeroExtend (fun i => u i^r) = fun i => zeroExtend u i^r := by
  funext i
  unfold zeroExtend
  split_ifs <;> simp [hr.ne']

/-- Exact polynomial identity for the actual raw network in grouped parameters. -/
theorem oneActiveAssemble_network (r p q : ℕ) (τ : ℝ) (w : OneActiveAux p q) :
    network r (fun i => zeroExtend (oneActiveAssemble p q τ w) i^r) (p+1+q) =
      (network r (fun i => zeroExtend w.2.2 i^r) q).comp
        ((X+C ((τ+w.1)^r)*X^r).comp (network r (fun i => zeroExtend w.2.1 i^r) p)) := by
  rw [network_one_active_split]
  have hpre := network_congr_prefix r p
    (fun i => zeroExtend (oneActiveAssemble p q τ w) i^r)
    (fun i => zeroExtend w.2.1 i^r) (fun i hi => by rw [oneActiveAssemble_pre p q τ w i hi])
  have hpost := network_congr_prefix r q
    (fun i => zeroExtend (oneActiveAssemble p q τ w) (p+1+i)^r)
    (fun i => zeroExtend w.2.2 i^r) (fun i hi => by rw [oneActiveAssemble_post p q τ w i hi])
  rw [hpre,hpost,oneActiveAssemble_active]

/-- Auxiliary evaluation agrees with the full actual network, including every omitted coefficient. -/
theorem oneActiveRawAux_eval_network (r p q : ℕ) (hr : 2 ≤ r) (τ x : ℝ) (w : OneActiveAux p q) :
    oneActiveAuxEval r (r^p+2) (r^q+2) (τ^r) x (oneActiveRawAux r p q τ w) =
      (network r (fun i => zeroExtend (oneActiveAssemble p q τ w) i^r) (p+1+q)).eval x := by
  have hpre : oneActiveAuxPre r (r^p+2) (r^q+2) x (oneActiveRawAux r p q τ w) =
      (network r (fun i => zeroExtend w.2.1 i^r) p).eval x := by
    simp only [oneActiveAuxPre,oneActiveRawAux,auxPreL,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',gradedEvalL_apply]
    rw [← inactiveAuxVector_eval r p hr,zeroExtend_pow p r (by omega)]
  have hmid : oneActiveAuxMiddle r (r^p+2) (r^q+2) (τ^r) x (oneActiveRawAux r p q τ w) =
      ((X+C ((τ+w.1)^r)*X^r).comp (network r (fun i => zeroExtend w.2.1 i^r) p)).eval x := by
    unfold oneActiveAuxMiddle
    rw [hpre]
    simp [oneActiveRawAux,auxActiveL]
  unfold oneActiveAuxEval
  rw [hmid]
  simp only [oneActiveRawAux,auxPostL,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd']
  rw [← inactiveAuxVector_eval r q hr,zeroExtend_pow q r (by omega),oneActiveAssemble_network]
  simp

@[simp] theorem oneActiveAuxEval_zero (r a b : ℕ) (c x : ℝ) :
    oneActiveAuxEval r a b c x 0 = x+c*x^r := by
  simp [oneActiveAuxEval,oneActiveAuxMiddle,oneActiveAuxPre]

end ResidualSLT
