module
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Tactic

/-! An integrability certificate, deliberately separate from pole multiplicity.
`HasIntegrabilityThresholdOn` requires a.e. positivity: the totalized real power at zero
must not accidentally certify an identically zero loss. Domains and measures are explicit.
No equivalence with zeta poles or Laplace asymptotics is asserted. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Set

/-- An exact nonnegative-exponent integrability threshold on a specified domain.
It is a property, not a supremum with silently chosen empty-set conventions. -/
@[expose] def HasIntegrabilityThresholdOn {α : Type*} [MeasurableSpace α]
    (K : α → ℝ) (D : Set α) (μ : Measure α) (threshold : ℝ) : Prop :=
  (∀ᵐ x ∂μ.restrict D, 0 < K x) ∧
  ∀ s : ℝ, 0 ≤ s → (IntegrableOn (fun x => (K x) ^ (-s)) D μ ↔ s < threshold)

/-- Exact toy calculation for `x^(2r)` on every positive interval `(0, ε)`.
This declaration concerns a monomial on a sector; the population-loss bridge is in `OneBlock`. -/
theorem monomial_integrableOn_iff (r : ℕ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    IntegrableOn (fun x : ℝ => (x ^ (2 * r)) ^ (-s)) (Ioo 0 ε) ↔
      s < 1 / (2 * (r : ℝ)) := by
  have hc : 0 < 2 * (r : ℝ) := by positivity
  have heq : EqOn (fun x : ℝ => (x ^ (2 * r)) ^ (-s))
      (fun x : ℝ => x ^ (-(2 * (r : ℝ) * s))) (Ioo 0 ε) := by
    intro x hx
    dsimp only
    rw [← Real.rpow_natCast_mul hx.1.le]
    congr 1
    push_cast
    ring
  rw [integrableOn_congr_fun heq measurableSet_Ioo,
    intervalIntegral.integrableOn_Ioo_rpow_iff hε]
  rw [lt_div_iff₀ hc]
  constructor <;> intro h <;> nlinarith

theorem monomial_thresholdOn (r : ℕ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    HasIntegrabilityThresholdOn (fun x : ℝ => x ^ (2 * r)) (Ioo 0 ε) volume
      (1 / (2 * (r : ℝ))) := by
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact pow_pos hx.1 _
  · intro s _
    exact monomial_integrableOn_iff r hr ε hε s
/-- The same threshold on a full two-sided neighborhood; the single zero point is null. -/
theorem monomial_integrableOn_symmetric_iff (r : ℕ) (hr : 0 < r)
    (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    IntegrableOn (fun x : ℝ => (x ^ (2 * r)) ^ (-s)) (Ioo (-ε) ε) ↔
      s < 1 / (2 * (r : ℝ)) := by
  have hneg : IntegrableOn (fun x : ℝ => (x ^ (2 * r)) ^ (-s)) (Ioo (-ε) 0) ↔
      IntegrableOn (fun x : ℝ => (x ^ (2 * r)) ^ (-s)) (Ioo 0 ε) := by
    have hm := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding
      (f := fun x : ℝ => (x ^ (2 * r)) ^ (-s)) (s := Ioo 0 ε)
    simpa [Function.comp_def, neg_pow, pow_mul] using hm
  rw [← Ioo_union_Ico_eq_Ioo (by linarith : -ε < (0 : ℝ)) hε.le,
    integrableOn_union, integrableOn_Ico_iff_integrableOn_Ioo, hneg, and_self]
  exact monomial_integrableOn_iff r hr ε hε s

/-- Full-neighborhood threshold certificate for the toy loss, with no multiplicity claim. -/
theorem monomial_thresholdOn_symmetric (r : ℕ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    HasIntegrabilityThresholdOn (fun x : ℝ => x ^ (2 * r)) (Ioo (-ε) ε) volume
      (1 / (2 * (r : ℝ))) := by
  constructor
  · filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with x hx
    rw [pow_mul]
    exact pow_pos (sq_pos_of_ne_zero hx) r
  · intro s _
    exact monomial_integrableOn_symmetric_iff r hr ε hε s
end ResidualSLT
