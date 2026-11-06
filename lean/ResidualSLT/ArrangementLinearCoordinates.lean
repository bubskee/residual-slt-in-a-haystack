module
public import ResidualSLT.ArrangementIntegrability
public import ResidualSLT.OneActiveCoordinates

/-! The chronological assembly is an affine bijection of all raw parameters. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Metric Set Finset

theorem oneActiveAssemble_zero_norm (p q : ℕ) (w : OneActiveAux p q) :
    ‖oneActiveAssemble p q 0 w‖ = ‖w‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    unfold oneActiveAssemble
    split_ifs
    · exact (norm_le_pi_norm w.2.1 _).trans ((norm_fst_le w.2).trans (norm_snd_le w))
    · simpa using norm_fst_le w
    · exact (norm_le_pi_norm w.2.2 _).trans ((norm_snd_le w.2).trans (norm_snd_le w))
  · rw [Prod.norm_def,Prod.norm_def]
    apply max_le
    · have hh := norm_le_pi_norm (oneActiveAssemble p q 0 w) ⟨p,by omega⟩
      simpa [oneActiveAssemble] using hh
    · apply max_le
      · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
        intro i
        have hh := norm_le_pi_norm (oneActiveAssemble p q 0 w) ⟨i.val,by have hi := i.isLt; omega⟩
        simpa [oneActiveAssemble,i.isLt] using hh
      · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
        intro i
        have hh := norm_le_pi_norm (oneActiveAssemble p q 0 w) ⟨p+1+i.val,by have hi := i.isLt; omega⟩
        simpa [oneActiveAssemble,show ¬p+1+i.val<p by omega,show p+1+i.val ≠ p by omega] using hh

theorem arrangementFlatten_prefix_norm_le (k : ℕ) (n : Fin (k+1) → ℕ)
    (w : ArrangementAux k n) (m : ℕ) (hm : m ≤ k) :
    ‖arrangementFlatten k n 0 w m hm‖ ≤ ‖w‖ := by
  induction m with
  | zero => exact (norm_le_pi_norm w.2 _).trans (norm_snd_le w)
  | succ m ih =>
    change ‖oneActiveAssemble _ _ 0 (w.1 ⟨m,by omega⟩,arrangementFlatten k n 0 w m (by omega),w.2 ⟨m+1,by omega⟩)‖ ≤ _
    rw [oneActiveAssemble_zero_norm,Prod.norm_def,Prod.norm_def]
    exact max_le ((norm_le_pi_norm w.1 _).trans (norm_fst_le w))
      (max_le (ih (by omega)) ((norm_le_pi_norm w.2 _).trans (norm_snd_le w)))

theorem arrangementFlatten_prefix_coordinates_le (k : ℕ) (n : Fin (k+1) → ℕ)
    (w : ArrangementAux k n) (m : ℕ) (hm : m ≤ k) :
    (∀ j : Fin k, j.val < m → ‖w.1 j‖ ≤ ‖arrangementFlatten k n 0 w m hm‖) ∧
    (∀ g : Fin (k+1), g.val ≤ m → ‖w.2 g‖ ≤ ‖arrangementFlatten k n 0 w m hm‖) := by
  induction m with
  | zero =>
    refine ⟨fun j hj => by omega,?_⟩
    intro g hg
    have he : g = ⟨0,by omega⟩ := Fin.ext (show g.val = 0 by omega)
    rw [he]
    exact le_rfl
  | succ m ih =>
    have hi := ih (by omega)
    change (∀ j : Fin k, j.val < m+1 → ‖w.1 j‖ ≤ ‖oneActiveAssemble _ _ 0 (w.1 ⟨m,by omega⟩,arrangementFlatten k n 0 w m (by omega),w.2 ⟨m+1,by omega⟩)‖) ∧
      (∀ g : Fin (k+1), g.val ≤ m+1 → ‖w.2 g‖ ≤ ‖oneActiveAssemble _ _ 0 (w.1 ⟨m,by omega⟩,arrangementFlatten k n 0 w m (by omega),w.2 ⟨m+1,by omega⟩)‖)
    simp only [oneActiveAssemble_zero_norm,Prod.norm_def]
    constructor
    · intro j hj
      by_cases he : j.val = m
      · have hj' : j = ⟨m,by omega⟩ := Fin.ext he
        rw [hj']
        exact le_max_left _ _
      · exact (hi.1 j (by omega)).trans ((le_max_left _ _).trans (le_max_right _ _))
    · intro g hg
      by_cases he : g.val = m+1
      · have hg' : g = ⟨m+1,by omega⟩ := Fin.ext he
        rw [hg']
        exact (le_max_right _ _).trans (le_max_right _ _)
      · exact (hi.2 g (by omega)).trans ((le_max_left _ _).trans (le_max_right _ _))

theorem arrangementFlatten_zero_norm (k : ℕ) (n : Fin (k+1) → ℕ) (w : ArrangementAux k n) :
    ‖arrangementFlatten k n 0 w k le_rfl‖ = ‖w‖ := by
  apply le_antisymm (arrangementFlatten_prefix_norm_le k n w k le_rfl)
  have hh := arrangementFlatten_prefix_coordinates_le k n w k le_rfl
  rw [Prod.norm_def]
  apply max_le
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun j => hh.1 j j.isLt)
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun g => hh.2 g (by have hi := g.isLt; omega))

theorem oneActiveAssemble_zero_add (p q : ℕ) (u v : OneActiveAux p q) :
    oneActiveAssemble p q 0 (u+v) = oneActiveAssemble p q 0 u+oneActiveAssemble p q 0 v := by
  funext i
  simp only [Pi.add_apply]
  unfold oneActiveAssemble
  split_ifs <;> simp

theorem oneActiveAssemble_zero_smul (p q : ℕ) (a : ℝ) (w : OneActiveAux p q) :
    oneActiveAssemble p q 0 (a • w) = a • oneActiveAssemble p q 0 w := by
  funext i
  simp only [Pi.smul_apply]
  unfold oneActiveAssemble
  split_ifs <;> simp

theorem arrangementFlatten_add (k : ℕ) (n : Fin (k+1) → ℕ)
    (u v : ArrangementAux k n) (m : ℕ) (hm : m ≤ k) :
    arrangementFlatten k n 0 (u+v) m hm = arrangementFlatten k n 0 u m hm+arrangementFlatten k n 0 v m hm := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext i
    simp only [Pi.add_apply]
    simp only [arrangementFlatten,oneActiveAssemble]
    split_ifs <;> simp [ih]

theorem arrangementFlatten_smul (k : ℕ) (n : Fin (k+1) → ℕ)
    (a : ℝ) (w : ArrangementAux k n) (m : ℕ) (hm : m ≤ k) :
    arrangementFlatten k n 0 (a • w) m hm = a • arrangementFlatten k n 0 w m hm := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext i
    simp only [Pi.smul_apply]
    simp only [arrangementFlatten,oneActiveAssemble]
    split_ifs <;> simp [ih]

@[expose] def arrangementZeroLinearMap (k : ℕ) (n : Fin (k+1) → ℕ) :
    ArrangementAux k n →ₗ[ℝ] (Fin (arrangementDepth k n k le_rfl) → ℝ) where
  toFun w := arrangementFlatten k n 0 w k le_rfl
  map_add' u v := arrangementFlatten_add k n u v k le_rfl
  map_smul' a w := arrangementFlatten_smul k n a w k le_rfl

theorem arrangementDepth_eq_sum (k : ℕ) (n : Fin (k+1) → ℕ) (m : ℕ) (hm : m ≤ k) :
    arrangementDepth k n m hm = m+∑ g : Fin (m+1), n ⟨g.val,by have hg := g.isLt; omega⟩ := by
  induction m with
  | zero => simp [arrangementDepth]
  | succ m ih =>
    rw [arrangementDepth,ih (by omega)]
    rw [Fin.sum_univ_castSucc (fun g : Fin (m+1+1) => n ⟨g.val,by have hg := g.isLt; omega⟩)]
    simp only [Fin.val_castSucc,Fin.val_last]
    omega

theorem arrangement_finrank (k : ℕ) (n : Fin (k+1) → ℕ) :
    Module.finrank ℝ (ArrangementAux k n) = Module.finrank ℝ (Fin (arrangementDepth k n k le_rfl) → ℝ) := by
  simp only [ArrangementAux,Module.finrank_prod,Module.finrank_pi,Module.finrank_pi_fintype,Fintype.card_fin]
  simpa using (arrangementDepth_eq_sum k n k le_rfl).symm

@[expose] def arrangementZeroLinearEquiv (k : ℕ) (n : Fin (k+1) → ℕ) :
    ArrangementAux k n ≃ₗ[ℝ] (Fin (arrangementDepth k n k le_rfl) → ℝ) :=
  (arrangementZeroLinearMap k n).linearEquivOfInjective
    (LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (fun w hw => by
      have hh : ‖w‖ = 0 := by rw [← arrangementFlatten_zero_norm k n w]; simpa [arrangementZeroLinearMap] using congrArg norm hw
      exact norm_eq_zero.mp hh))) (arrangement_finrank k n)

end ResidualSLT
