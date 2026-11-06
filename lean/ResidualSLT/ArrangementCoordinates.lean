module
public import ResidualSLT.ArrangementLinearCoordinates
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Exact neighborhood correspondence and a positive finite Haar measure factor. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Metric Set

theorem arrangementFlatten_affine (k : ℕ) (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ)
    (w : ArrangementAux k n) (m : ℕ) (hm : m ≤ k) :
    arrangementFlatten k n τ w m hm =
      arrangementFlatten k n τ 0 m hm+arrangementFlatten k n 0 w m hm := by
  induction m with
  | zero =>
    funext i
    change w.2 ⟨0,by omega⟩ i = (0:ℝ)+w.2 ⟨0,by omega⟩ i
    exact (zero_add _).symm
  | succ m ih =>
    funext i
    simp only [Pi.add_apply]
    simp only [arrangementFlatten,oneActiveAssemble]
    split_ifs <;> simp [ih]

@[expose] def arrangementCoordinateEquiv (k : ℕ) (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ) :
    ArrangementAux k n ≃ᵐ (Fin (arrangementDepth k n k le_rfl) → ℝ) :=
  (arrangementZeroLinearEquiv k n).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.trans
    (MeasurableEquiv.addLeft (arrangementFlatten k n τ 0 k le_rfl))

theorem arrangementCoordinateEquiv_apply (k : ℕ) (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ)
    (w : ArrangementAux k n) :
    arrangementCoordinateEquiv k n τ w = arrangementFlatten k n τ w k le_rfl := by
  change arrangementFlatten k n τ 0 k le_rfl+arrangementFlatten k n 0 w k le_rfl = _
  exact (arrangementFlatten_affine k n τ w k le_rfl).symm

/-- Product-coordinate balls are exactly the original full raw-weight balls. -/
theorem arrangementCoordinateEquiv_preimage_ball (k : ℕ) (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ) (ε : ℝ) :
    (arrangementCoordinateEquiv k n τ) ⁻¹' ball (arrangementFlatten k n τ 0 k le_rfl) ε =
      ball (0 : ArrangementAux k n) ε := by
  ext w
  simp only [mem_preimage,mem_ball,arrangementCoordinateEquiv_apply,dist_eq_norm,sub_zero]
  rw [arrangementFlatten_affine k n τ w k le_rfl,add_sub_cancel_left,arrangementFlatten_zero_norm]

/-- Haar uniqueness supplies a finite strictly positive comparison factor. No Jacobian or
measure equivalence is assumed, and no rectangle replaces the actual neighborhood. -/
theorem arrangementCoordinateEquiv_measure_comparison (k : ℕ) (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ) :
    ∃ d : NNReal, 0 < d ∧ MeasurePreserving (arrangementCoordinateEquiv k n τ)
      volume (d • (volume : Measure (Fin (arrangementDepth k n k le_rfl) → ℝ))) := by
  let : (volume : Measure (ArrangementAux k n)).IsAddHaarMeasure := by
    change (volume : Measure ((Fin k → ℝ) × (∀ g, Fin (n g) → ℝ))).IsAddHaarMeasure
    rw [Measure.volume_eq_prod]
    exact Measure.prod.instIsAddHaarMeasure _ _
  let e := arrangementZeroLinearEquiv k n
  let ν := (volume : Measure (ArrangementAux k n)).map e
  let : ν.IsAddHaarMeasure := e.toContinuousLinearEquiv.isAddHaarMeasure_map volume
  let d := ν.addHaarScalarFactor volume
  have hd : 0 < d := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν volume
  have he : MeasurePreserving e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv volume
      (d • (volume : Measure (Fin (arrangementDepth k n k le_rfl) → ℝ))) :=
    ⟨e.toContinuousLinearEquiv.continuous.measurable,Measure.isAddLeftInvariant_eq_smul ν volume⟩
  exact ⟨d,hd,(measurePreserving_add_left (d • volume) (arrangementFlatten k n τ 0 k le_rfl)).comp he⟩

end ResidualSLT
