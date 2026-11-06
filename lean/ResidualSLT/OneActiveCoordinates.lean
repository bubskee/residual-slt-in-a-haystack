module
public import ResidualSLT.OneActiveIntegrability

/-! The before/active/after parameter split is a volume-preserving affine coordinate equivalence. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Metric Set

@[expose] def oneActiveIndexEquiv (p q : ℕ) : Unit ⊕ (Fin p ⊕ Fin q) ≃ Fin (p+1+q) where
  toFun j := match j with
    | .inl _ => ⟨p,by omega⟩
    | .inr (.inl i) => ⟨i.val,by have hh := i.isLt; omega⟩
    | .inr (.inr i) => ⟨p+1+i.val,by have hh := i.isLt; omega⟩
  invFun i := if hi : i.val<p then .inr (.inl ⟨i.val,hi⟩) else
    if he : i.val=p then .inl () else .inr (.inr ⟨i.val-(p+1),by have hh := i.isLt; omega⟩)
  left_inv j := by
    rcases j with ⟨⟩ | (i | i)
    · simp
    · simp [i.isLt]
    · simp [show ¬p+1+i.val<p by omega,show p+1+i.val ≠ p by omega]
  right_inv i := by
    dsimp only
    split_ifs <;> apply Fin.ext <;> simp_all; omega

@[expose] def oneActiveZeroEquiv (p q : ℕ) : OneActiveAux p q ≃ᵐ (Fin (p+1+q) → ℝ) :=
  (((MeasurableEquiv.piUnique (fun _ : Unit => ℝ)).symm.prodCongr
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin p ⊕ Fin q => ℝ)).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ (Fin p ⊕ Fin q) => ℝ)).symm).trans
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (p+1+q) => ℝ) (oneActiveIndexEquiv p q))

theorem oneActiveZeroEquiv_apply (p q : ℕ) (w : OneActiveAux p q) :
    oneActiveZeroEquiv p q w = oneActiveAssemble p q 0 w := by
  funext i
  obtain ⟨j,rfl⟩ := (oneActiveIndexEquiv p q).surjective i
  simp only [oneActiveZeroEquiv,MeasurableEquiv.trans_apply,MeasurableEquiv.piCongrLeft_apply_apply]
  rcases j with ⟨⟩ | (j | j)
  · simp [oneActiveIndexEquiv,oneActiveAssemble,MeasurableEquiv.sumPiEquivProdPi,MeasurableEquiv.prodCongr,MeasurableEquiv.piUnique]
  · simp [oneActiveIndexEquiv,oneActiveAssemble,MeasurableEquiv.sumPiEquivProdPi,MeasurableEquiv.prodCongr,j.isLt]
  · simp [oneActiveIndexEquiv,oneActiveAssemble,MeasurableEquiv.sumPiEquivProdPi,MeasurableEquiv.prodCongr,
      show ¬p+1+j.val<p by omega,show p+1+j.val ≠ p by omega]

theorem oneActiveZeroEquiv_measurePreserving (p q : ℕ) :
    MeasurePreserving (oneActiveZeroEquiv p q) volume volume := by
  have h0 : MeasurePreserving (MeasurableEquiv.piUnique (fun _ : Unit => ℝ)).symm volume volume :=
    (measurePreserving_piUnique (fun _ : Unit => (volume : Measure ℝ))).symm _
  have h1 := h0.prod (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin p ⊕ Fin q => ℝ))
  have h2 := (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Unit ⊕ (Fin p ⊕ Fin q) => ℝ)).comp h1
  have h3 := (volume_measurePreserving_piCongrLeft (fun _ : Fin (p+1+q) => ℝ) (oneActiveIndexEquiv p q)).comp h2
  simpa only [← Measure.volume_eq_prod,oneActiveZeroEquiv,MeasurableEquiv.coe_trans,
    MeasurableEquiv.prodCongr,MeasurableEquiv.coe_mk,Equiv.prodCongr_apply,MeasurableEquiv.coe_toEquiv,Function.comp_assoc] using h3

@[expose] def oneActiveCoordinateEquiv (p q : ℕ) (τ : ℝ) : OneActiveAux p q ≃ᵐ (Fin (p+1+q) → ℝ) :=
  (oneActiveZeroEquiv p q).trans (MeasurableEquiv.addLeft (oneActiveAssemble p q τ 0))

theorem oneActiveCoordinateEquiv_apply (p q : ℕ) (τ : ℝ) (w : OneActiveAux p q) :
    oneActiveCoordinateEquiv p q τ w = oneActiveAssemble p q τ w := by
  change oneActiveAssemble p q τ 0+oneActiveZeroEquiv p q w = _
  rw [oneActiveZeroEquiv_apply]
  funext i
  simp only [Pi.add_apply,oneActiveAssemble]
  split_ifs <;> simp

theorem oneActiveCoordinateEquiv_measurePreserving (p q : ℕ) (τ : ℝ) :
    MeasurePreserving (oneActiveCoordinateEquiv p q τ) volume volume :=
  (measurePreserving_add_left volume (oneActiveAssemble p q τ 0)).comp
    (oneActiveZeroEquiv_measurePreserving p q)

/-- Exact full neighborhood preimage: a product norm ball is the original raw-weight cube. -/
theorem oneActiveCoordinateEquiv_preimage_ball (p q : ℕ) (τ ε : ℝ) :
    (oneActiveCoordinateEquiv p q τ) ⁻¹' ball (oneActiveAssemble p q τ 0) ε =
      ball (0 : OneActiveAux p q) ε := by
  ext w
  simp only [mem_preimage,mem_ball,oneActiveCoordinateEquiv_apply,dist_eq_norm]
  have hdiff : oneActiveAssemble p q τ w-oneActiveAssemble p q τ 0 = oneActiveAssemble p q 0 w := by
    funext i
    simp only [Pi.sub_apply,oneActiveAssemble]
    split_ifs <;> simp
  rw [hdiff,sub_zero]
  suffices ‖oneActiveAssemble p q 0 w‖ = ‖w‖ by rw [this]
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

end ResidualSLT
