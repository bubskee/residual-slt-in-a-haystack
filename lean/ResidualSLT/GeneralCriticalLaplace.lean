module
public import ResidualSLT.GeneralConeLaplace

/-! At dimension=homogeneous degree, every strictly higher radial correction
has logarithmic Laplace multiplicity two under regular nonempty cancellation. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Metric

/-- Critical homogeneous model, with regularity and nonemptiness stated only on
the unit sphere. Dimension at least two follows from these assumptions. -/
theorem homogeneous_critical_spherical_laplace_order (d k : ℕ) (hdk : d < k)
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hhom : ∀ t w, f (t • w) = t^d*f w)
    (hreg : ∀ u, ‖u‖ = 1 → f u = 0 → fderiv ℝ f u ≠ 0)
    (hzero : ∃ u, ‖u‖ = 1 ∧ f u = 0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasCriticalLaplaceOrder (fun N => ∫ w in ball 0 ε,
      Real.exp (-N*homogeneousConeLoss f k w)) := by
  have hd := homogeneous_regular_spherical_zero_dimension d d f hf hhom hreg hzero
  have hz : ∃ w, w ≠ 0 ∧ f w = 0 := by
    obtain ⟨u,hu,hfu⟩ := hzero
    exact ⟨u,by intro he; simp [he] at hu,hfu⟩
  obtain ⟨n,rfl⟩ : ∃ n, d = n+2 := ⟨d-2,by omega⟩
  have h := homogeneous_critical_laplace_order n (k-(n+2)) (by omega) f hf hhom
    (homogeneous_regular_of_unit_sphere f hf (n+2) hhom hreg) hz ε hε hε1
  simpa only [Nat.add_sub_of_le hdk.le] using h

/-- Local a.e. comparison suffices for finite Laplace integrals even when the
compared loss is only a.e. measurable. No continuity of that loss is required. -/
theorem integrable_laplace_of_comparable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (D : Set α) (K J : α → ℝ)
    (hiK : ∀ N : ℝ, IntegrableOn (fun x => Real.exp (-N*K x)) D μ)
    (hK : ∀ᵐ x ∂μ.restrict D, 0 ≤ K x) (hJ : AEMeasurable J (μ.restrict D))
    (c C : ℝ) (hc : 0 < c)
    (hb : ∀ᵐ x ∂μ.restrict D, c*K x ≤ J x ∧ J x ≤ C*K x) (N : ℝ) :
    IntegrableOn (fun x => Real.exp (-N*J x)) D μ := by
  apply (hiK (-|N| * C)).mono' (by fun_prop)
  filter_upwards [hb,hK] with x hx hKx
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hJx : 0 ≤ J x := (mul_nonneg hc.le hKx).trans hx.1
  nlinarith [mul_le_mul_of_nonneg_left hx.2 (abs_nonneg N),
    mul_le_mul_of_nonneg_right (neg_le_abs N) hJx]

/-- Comparable measurable losses and bounded positive priors preserve the critical
logarithm. All geometric assumptions concern f, not charts or transformed rectangles. -/
theorem homogeneous_critical_prior_laplace_order (d k : ℕ) (hdk : d < k)
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hhom : ∀ t w, f (t • w) = t^d*f w)
    (hreg : ∀ u, ‖u‖ = 1 → f u = 0 → fderiv ℝ f u ≠ 0)
    (hzero : ∃ u, ‖u‖ = 1 ∧ f u = 0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (J : (Fin d → ℝ) → ℝ) (hJ : AEMeasurable J (volume.restrict (ball 0 ε)))
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hlo : ∀ᵐ w ∂volume.restrict (ball 0 ε), c*homogeneousConeLoss f k w ≤ J w)
    (hup : ∀ᵐ w ∂volume.restrict (ball 0 ε), J w ≤ C*homogeneousConeLoss f k w)
    (p : (Fin d → ℝ) → NNReal) (hp : BoundedPositivePriorOn p (ball 0 ε) volume) :
    HasCriticalLaplaceOrder (fun N => ∫ w in ball 0 ε, Real.exp (-N*J w)
      ∂volume.withDensity (fun w => (p w : ENNReal))) := by
  have hcf := hf.continuous
  have hK : Continuous (homogeneousConeLoss f k) := by unfold homogeneousConeLoss; fun_prop
  have hiK (N : ℝ) : IntegrableOn (fun w => Real.exp (-N*homogeneousConeLoss f k w)) (ball 0 ε) volume :=
    ((by fun_prop : Continuous (fun w => Real.exp (-N*homogeneousConeLoss f k w))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall
  have hiJ := integrable_laplace_of_comparable volume (ball 0 ε) (homogeneousConeLoss f k) J hiK
    (Filter.Eventually.of_forall (fun w => by unfold homogeneousConeLoss; positivity)) hJ c C hc (hlo.and hup)
  apply laplace_order_withDensity volume measurableSet_ball J hiJ p hp
  exact laplace_order_of_comparable volume (ball 0 ε) (homogeneousConeLoss f k) J hiK hiJ
    c C hc hC (hlo.and hup) (homogeneous_critical_spherical_laplace_order d k hdk f hf hhom hreg hzero ε hε hε1)

/-- Expanded certificate: at n=d and k>d the local Laplace pair is (1/2,2).
This is a two-sided order statement, not a leading-constant or meromorphic-continuation assertion. -/
theorem homogeneous_critical_prior_laplace_bounds (d k : ℕ) (hdk : d < k)
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hhom : ∀ t w, f (t • w) = t^d*f w)
    (hreg : ∀ u, ‖u‖ = 1 → f u = 0 → fderiv ℝ f u ≠ 0)
    (hzero : ∃ u, ‖u‖ = 1 ∧ f u = 0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (J : (Fin d → ℝ) → ℝ) (hJ : AEMeasurable J (volume.restrict (ball 0 ε)))
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hlo : ∀ᵐ w ∂volume.restrict (ball 0 ε), c*homogeneousConeLoss f k w ≤ J w)
    (hup : ∀ᵐ w ∂volume.restrict (ball 0 ε), J w ≤ C*homogeneousConeLoss f k w)
    (p : (Fin d → ℝ) → NNReal) (hp : BoundedPositivePriorOn p (ball 0 ε) volume) :
    ∃ a A N₀ : ℝ, 0 < a ∧ 0 < A ∧ 1 < N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      a*(N^(-(1/2:ℝ))*Real.log N) ≤
        (∫ w in ball 0 ε, Real.exp (-N*J w) ∂volume.withDensity (fun w => (p w : ENNReal))) ∧
      (∫ w in ball 0 ε, Real.exp (-N*J w) ∂volume.withDensity (fun w => (p w : ENNReal))) ≤
        A*(N^(-(1/2:ℝ))*Real.log N) :=
  (homogeneous_critical_prior_laplace_order d k hdk f hf hhom hreg hzero ε hε hε1
    J hJ c C hc hC hlo hup p hp).bounds

end ResidualSLT
