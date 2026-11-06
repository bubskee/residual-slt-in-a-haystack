module
public import ResidualSLT.ArrangementRawLinearization
public import ResidualSLT.OneActiveLaplace

/-! Chronological assembly into the original residual network, without changing raw powers. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset

@[expose] def arrangementDepth (k : ℕ) (n : Fin (k+1) → ℕ) : (m : ℕ) → m ≤ k → ℕ
  | 0, _ => n ⟨0,by omega⟩
  | m+1, hm => arrangementDepth k n m (by omega)+1+n ⟨m+1,by omega⟩

@[expose] def arrangementFlatten (k : ℕ) (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ)
    (w : ArrangementAux k n) : (m : ℕ) → (hm : m ≤ k) → (Fin (arrangementDepth k n m hm) → ℝ)
  | 0, _ => w.2 ⟨0,by omega⟩
  | m+1, hm => oneActiveAssemble (arrangementDepth k n m (by omega)) (n ⟨m+1,by omega⟩) (τ ⟨m,by omega⟩)
      (w.1 ⟨m,by omega⟩,arrangementFlatten k n τ w m (by omega),w.2 ⟨m+1,by omega⟩)

theorem arrangementDepth_ge (k : ℕ) (n : Fin (k+1) → ℕ) (m : ℕ) (hm : m ≤ k) :
    m ≤ arrangementDepth k n m hm := by
  induction m with
  | zero => omega
  | succ m ih =>
    have hh := ih (by omega)
    simp only [arrangementDepth]
    omega

theorem arrangementFlatten_continuous (k : ℕ) (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ)
    (m : ℕ) (hm : m ≤ k) : Continuous (fun w : ArrangementAux k n => arrangementFlatten k n τ w m hm) := by
  induction m with
  | zero => exact (continuous_apply _).comp continuous_snd
  | succ m ih =>
    have hi := ih (by omega)
    exact (oneActiveAssemble_continuous _ _ _).comp
      (((continuous_apply _).comp continuous_fst).prodMk (hi.prodMk ((continuous_apply _).comp continuous_snd)))

theorem arrangementActiveL_rawAux (r k : ℕ) (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ)
    (w : ArrangementAux k n) (j : Fin k) :
    arrangementActiveL k (fun g => r^(n g)+2) j.val (arrangementRawAux r k n τ w) =
      (τ j+w.1 j)^r-(τ j)^r := by
  simp [arrangementActiveL,arrangementRawAux,j.isLt]

theorem arrangementGroupL_rawAux (r k : ℕ) (hr : 2 ≤ r) (n : Fin (k+1) → ℕ)
    (τ : Fin k → ℝ) (w : ArrangementAux k n) (g : Fin (k+1)) (x : ℝ) :
    x+arrangementGroupL r k (fun g => r^(n g)+2) g.val x (arrangementRawAux r k n τ w) =
      (network r (fun i => zeroExtend (w.2 g) i^r) (n g)).eval x := by
  have hh := inactiveAuxVector_eval r (n g) hr (fun i => w.2 g i^r) x
  simpa [arrangementGroupL,arrangementRawAux,g.isLt,gradedEvalL_apply,zeroExtend_pow (n g) r (by omega)] using hh.symm

/-- The auxiliary map evaluated at the actual group coefficients is the chronological raw network. -/
theorem arrangementRawAux_eval_network (r k : ℕ) (hr : 2 ≤ r) (n : Fin (k+1) → ℕ)
    (τ : Fin k → ℝ) (w : ArrangementAux k n) (x : ℝ) (m : ℕ) (hm : m ≤ k) :
    arrangementAuxEval r k (fun g => r^(n g)+2) (zeroExtend (fun j => (τ j)^r)) x m
      (arrangementRawAux r k n τ w) =
      (network r (fun i => zeroExtend (arrangementFlatten k n τ w m hm) i^r)
        (arrangementDepth k n m hm)).eval x := by
  induction m with
  | zero => exact arrangementGroupL_rawAux r k hr n τ w ⟨0,by omega⟩ x
  | succ m ih =>
    have hi := ih (by omega)
    simp only [arrangementFlatten,arrangementDepth,oneActiveAssemble_network,eval_comp]
    simp only [arrangementAuxEval]
    rw [arrangementGroupL_rawAux r k hr n τ w ⟨m+1,by omega⟩]
    congr 1
    rw [hi,arrangementActiveL_rawAux r k n τ w ⟨m,by omega⟩]
    simp [zeroExtend,show m<k by omega]

theorem arrangementRawAux_zero (r k : ℕ) (hr : 2 ≤ r) (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ) :
    arrangementRawAux r k n τ 0 = 0 := by
  have hz (m : ℕ) : inactiveAuxVector r m (fun _ => 0) = fun _ => 0 := by
    simpa only [Pi.zero_def] using inactiveAuxVector_zero r m
  simp [arrangementRawAux,Pi.zero_def,Prod.zero_eq_mk,show r ≠ 0 by omega,hz]

/-- At the realization, every inactive group disappears and exactly the prescribed active chain remains. -/
theorem arrangementFlatten_target (r k : ℕ) (hr : 2 ≤ r) (n : Fin (k+1) → ℕ)
    (τ : Fin k → ℝ) :
    network r (fun i => zeroExtend (arrangementFlatten k n τ 0 k le_rfl) i^r) (arrangementDepth k n k le_rfl) =
      network r (zeroExtend (fun j => (τ j)^r)) k := by
  apply Polynomial.funext
  intro x
  have hh := arrangementRawAux_eval_network r k hr n τ 0 x k le_rfl
  rw [arrangementRawAux_zero r k hr,arrangementAuxEval_zero] at hh
  exact hh.symm

end ResidualSLT
