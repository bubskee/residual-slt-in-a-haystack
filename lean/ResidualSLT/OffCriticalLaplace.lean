module
public import ResidualSLT.PowerConeLaplace
public import ResidualSLT.PowerLaplaceTransfer

/-! Off-critical homogeneous cancellation: exact RLCT with pure-power Laplace order. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Metric

/-- Off-critical homogeneous model, with regularity and nonemptiness stated only on
the unit sphere. Dimension at least two follows from these assumptions. -/
theorem homogeneous_offcritical_spherical_laplace_order (n d k : ℕ) (hd : 0 < d) (hdk : d < k) (hne : n ≠ d)
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hhom : ∀ t w, f (t • w) = t^d*f w)
    (hreg : ∀ u, ‖u‖ = 1 → f u = 0 → fderiv ℝ f u ≠ 0)
    (hzero : ∃ u, ‖u‖ = 1 ∧ f u = 0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasPowerLaplaceOrder (min ((n:ℝ)/(2*d)) (((n:ℝ)+k-d)/(2*k))) (fun N => ∫ w in ball 0 ε,
      Real.exp (-N*homogeneousConeLoss f k w)) := by
  have hdim := homogeneous_regular_spherical_zero_dimension n d f hf hhom hreg hzero
  have hz : ∃ w, w ≠ 0 ∧ f w = 0 := by
    obtain ⟨u,hu,hfu⟩ := hzero
    exact ⟨u,by intro he; simp [he] at hu,hfu⟩
  obtain ⟨a,rfl⟩ : ∃ a, n = a+2 := ⟨n-2,by omega⟩
  have h := homogeneous_offcritical_laplace_order a d (k-d) hd (by omega) hne f hf hhom
    (homogeneous_regular_of_unit_sphere f hf d hhom hreg) hz ε hε hε1
  rw [Nat.add_sub_of_le hdk.le] at h
  have hden : (d:ℝ)+(k-d:ℕ) = k := by exact_mod_cast Nat.add_sub_of_le hdk.le
  unfold coneLaplaceExponent at h
  rw [hden,Nat.cast_sub hdk.le] at h
  simpa only [Nat.cast_add,Nat.cast_ofNat,add_sub_assoc] using h

/-- Comparable measurable losses and bounded positive priors preserve the off-critical
power. All geometric assumptions concern f, not charts or transformed rectangles. -/
theorem homogeneous_offcritical_prior_laplace_order (n d k : ℕ) (hd : 0 < d) (hdk : d < k) (hne : n ≠ d)
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hhom : ∀ t w, f (t • w) = t^d*f w)
    (hreg : ∀ u, ‖u‖ = 1 → f u = 0 → fderiv ℝ f u ≠ 0)
    (hzero : ∃ u, ‖u‖ = 1 ∧ f u = 0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (J : (Fin n → ℝ) → ℝ) (hJ : AEMeasurable J (volume.restrict (ball 0 ε)))
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hlo : ∀ᵐ w ∂volume.restrict (ball 0 ε), c*homogeneousConeLoss f k w ≤ J w)
    (hup : ∀ᵐ w ∂volume.restrict (ball 0 ε), J w ≤ C*homogeneousConeLoss f k w)
    (p : (Fin n → ℝ) → NNReal) (hp : BoundedPositivePriorOn p (ball 0 ε) volume) :
    HasPowerLaplaceOrder (min ((n:ℝ)/(2*d)) (((n:ℝ)+k-d)/(2*k))) (fun N => ∫ w in ball 0 ε, Real.exp (-N*J w)
      ∂volume.withDensity (fun w => (p w : ENNReal))) := by
  have hcf := hf.continuous
  have hK : Continuous (homogeneousConeLoss f k) := by unfold homogeneousConeLoss; fun_prop
  have hiK (N : ℝ) : IntegrableOn (fun w => Real.exp (-N*homogeneousConeLoss f k w)) (ball 0 ε) volume :=
    ((by fun_prop : Continuous (fun w => Real.exp (-N*homogeneousConeLoss f k w))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall
  have hiJ := integrable_laplace_of_comparable volume (ball 0 ε) (homogeneousConeLoss f k) J hiK
    (Filter.Eventually.of_forall (fun w => by unfold homogeneousConeLoss; positivity)) hJ c C hc (hlo.and hup)
  apply power_laplace_order_withDensity volume measurableSet_ball J hiJ p hp
  exact power_laplace_order_of_comparable volume (ball 0 ε) (homogeneousConeLoss f k) J hiK hiJ
    c C hc hC (hlo.and hup) (homogeneous_offcritical_spherical_laplace_order n d k hd hdk hne f hf hhom hreg hzero ε hε hε1)

/-- Expanded certificate: at n≠d and k>d the local Laplace pair has m=1.
This is a two-sided order statement, not a leading-constant or meromorphic-continuation assertion. -/
theorem homogeneous_offcritical_prior_laplace_bounds (n d k : ℕ) (hd : 0 < d) (hdk : d < k) (hne : n ≠ d)
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hhom : ∀ t w, f (t • w) = t^d*f w)
    (hreg : ∀ u, ‖u‖ = 1 → f u = 0 → fderiv ℝ f u ≠ 0)
    (hzero : ∃ u, ‖u‖ = 1 ∧ f u = 0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (J : (Fin n → ℝ) → ℝ) (hJ : AEMeasurable J (volume.restrict (ball 0 ε)))
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hlo : ∀ᵐ w ∂volume.restrict (ball 0 ε), c*homogeneousConeLoss f k w ≤ J w)
    (hup : ∀ᵐ w ∂volume.restrict (ball 0 ε), J w ≤ C*homogeneousConeLoss f k w)
    (p : (Fin n → ℝ) → NNReal) (hp : BoundedPositivePriorOn p (ball 0 ε) volume) :
    ∃ a A N₀ : ℝ, 0 < a ∧ 0 < A ∧ 1 < N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      a*(N^(-(min ((n:ℝ)/(2*d)) (((n:ℝ)+k-d)/(2*k))))) ≤
        (∫ w in ball 0 ε, Real.exp (-N*J w) ∂volume.withDensity (fun w => (p w : ENNReal))) ∧
      (∫ w in ball 0 ε, Real.exp (-N*J w) ∂volume.withDensity (fun w => (p w : ENNReal))) ≤
        A*(N^(-(min ((n:ℝ)/(2*d)) (((n:ℝ)+k-d)/(2*k))))) :=
  (homogeneous_offcritical_prior_laplace_order n d k hd hdk hne f hf hhom hreg hzero ε hε hε1
    J hJ c C hc hC hlo hup p hp).bounds

/-- One certificate combines multiplicity-one Laplace bounds with the exact power-integrability threshold, including boundary divergence. -/
theorem homogeneous_offcritical_prior_certificate (n d k : ℕ) (hd : 0 < d) (hdk : d < k) (hne : n ≠ d)
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hhom : ∀ t w, f (t • w) = t^d*f w)
    (hreg : ∀ u, ‖u‖ = 1 → f u = 0 → fderiv ℝ f u ≠ 0)
    (hzero : ∃ u, ‖u‖ = 1 ∧ f u = 0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (J : (Fin n → ℝ) → ℝ) (hJ : AEMeasurable J (volume.restrict (ball 0 ε)))
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hlo : ∀ᵐ w ∂volume.restrict (ball 0 ε), c*homogeneousConeLoss f k w ≤ J w)
    (hup : ∀ᵐ w ∂volume.restrict (ball 0 ε), J w ≤ C*homogeneousConeLoss f k w)
    (p : (Fin n → ℝ) → NNReal) (hp : BoundedPositivePriorOn p (ball 0 ε) volume) :
    HasPowerLaplaceOrder (min ((n:ℝ)/(2*d)) (((n:ℝ)+k-d)/(2*k))) (fun N => ∫ w in ball 0 ε, Real.exp (-N*J w)
      ∂volume.withDensity (fun w => (p w : ENNReal))) ∧
    ∀ s : ℝ, IntegrableOn (fun w => J w^(-s)) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal))) ↔ s < min ((n:ℝ)/(2*d)) (((n:ℝ)+k-d)/(2*k)) := by
  constructor
  · exact homogeneous_offcritical_prior_laplace_order n d k hd hdk hne f hf hhom hreg hzero
      ε hε hε1 J hJ c C hc hC hlo hup p hp
  · have hdim := homogeneous_regular_spherical_zero_dimension n d f hf hhom hreg hzero
    have hz : ∃ w, w ≠ 0 ∧ f w = 0 := by
      obtain ⟨u,hu,hfu⟩ := hzero
      exact ⟨u,by intro he; simp [he] at hu,hfu⟩
    intro s
    exact homogeneous_cancellation_prior_integrableOn_iff n d k hdim hd hdk f hf hhom hreg hz
      ε hε hε1 J hJ c C hc hC hlo hup p hp s

end ResidualSLT
