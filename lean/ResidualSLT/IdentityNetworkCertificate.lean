module
public import ResidualSLT.EvenNetworkLaplace
public import ResidualSLT.OffCriticalNetworkLaplace
public import ResidualSLT.CriticalNetworkLaplace

/-! Unified identity-target learning pair at every degree r≥2 and positive depth.
Multiplicity means the logarithmic exponent in two-sided Laplace order. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Metric

/-- The real-power/logarithmic rate for a learning pair (ℓ,m). -/
@[expose] def laplaceRate (ℓ : ℝ) (m : ℕ) (N : ℝ) : ℝ :=
  N^(-ℓ)*(Real.log N)^(m-1)

/-- A positive multiplicity and explicit eventual two-sided bounds.
This does not assert a leading constant or complex meromorphic continuation. -/
@[expose] def HasLaplaceOrder (ℓ : ℝ) (m : ℕ) (Z : ℝ → ℝ) : Prop :=
  0 < m ∧ ∃ c C N₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
    c*laplaceRate ℓ m N ≤ Z N ∧ Z N ≤ C*laplaceRate ℓ m N

theorem HasPowerLaplaceOrder.toLaplaceOrder {ℓ : ℝ} {Z : ℝ → ℝ}
    (h : HasPowerLaplaceOrder ℓ Z) : HasLaplaceOrder ℓ 1 Z := by
  refine ⟨by omega,?_⟩
  simpa only [laplaceRate,Nat.sub_self,pow_zero,mul_one] using h.bounds

theorem HasCriticalLaplaceOrder.toLaplaceOrder {Z : ℝ → ℝ}
    (h : HasCriticalLaplaceOrder Z) : HasLaplaceOrder (1/2) 2 Z := by
  refine ⟨by omega,?_⟩
  simpa only [laplaceRate,show 2-1=1 by omega,pow_one,criticalLaplaceRate] using h.bounds

/-- Exact identity-target pair: even degree or shallow odd depth is radial;
odd depth=degree has the logarithm; deeper odd networks have cancellation order. -/
@[expose] def identityLearningPair (r L : ℕ) : ℝ × ℕ :=
  if Even r then ((L:ℝ)/(2*r),1)
  else if L < r then ((L:ℝ)/(2*r),1)
  else if L = r then (1/2,2)
  else (((L:ℝ)+r)/(4*r),1)

theorem identityLearningPair_even (r L : ℕ) (heven : Even r) :
    identityLearningPair r L = ((L:ℝ)/(2*r),1) := by
  simp [identityLearningPair,heven]

theorem identityLearningPair_odd_lt (r L : ℕ) (hodd : Odd r) (hlt : L < r) :
    identityLearningPair r L = ((L:ℝ)/(2*r),1) := by
  simp [identityLearningPair,Nat.not_even_iff_odd.mpr hodd,hlt]

theorem identityLearningPair_odd_eq (r : ℕ) (hodd : Odd r) :
    identityLearningPair r r = (1/2,2) := by
  simp [identityLearningPair,Nat.not_even_iff_odd.mpr hodd]

theorem identityLearningPair_odd_gt (r L : ℕ) (hodd : Odd r) (hgt : r < L) :
    identityLearningPair r L = (((L:ℝ)+r)/(4*r),1) := by
  simp [identityLearningPair,Nat.not_even_iff_odd.mpr hodd,not_lt_of_ge hgt.le,ne_of_gt hgt]

/-- The unified pair gives the exact integrability threshold for every real exponent. -/
theorem identity_network_prior_integrableOn_iff (μ : Measure ℝ)
    (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume)
    (s : ℝ) :
    IntegrableOn (fun w => networkPopulationLoss μ r w^(-s)) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ENNReal))) ↔ s < (identityLearningPair r L).1 := by
  by_cases heven : Even r
  · rw [identityLearningPair_even r L heven]
    exact even_network_prior_integrableOn_iff μ r hr heven L hL h ε hε hε1 ρ hρ s
  · have hodd := Nat.not_even_iff_odd.mp heven
    have hr3 : 3 ≤ r := by obtain ⟨k,hk⟩ := hodd; omega
    have hh := odd_network_prior_phase_transition μ r hr3 hodd L hL h ε hε hε1 ρ hρ s
    by_cases hlt : L < r
    · rw [identityLearningPair_odd_lt r L hodd hlt]
      simpa only [ite_eq_left hlt,Prod.fst] using hh
    · by_cases heq : L = r
      · subst L
        rw [identityLearningPair_odd_eq r hodd]
        simpa using hh
      · rw [identityLearningPair_odd_gt r L hodd (by omega)]
        simpa only [ite_eq_right hlt,ite_eq_right heq,Prod.fst] using hh

/-- Unified two-sided Laplace order of the actual squared-error population loss.
No parity or dimension/degree branch is assumed by the caller. -/
theorem identity_network_laplace_order (μ : Measure ℝ)
    (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    HasLaplaceOrder (identityLearningPair r L).1 (identityLearningPair r L).2
      (fun N => ∫ w : Fin L → ℝ in ball 0 ε, Real.exp (-N*networkPopulationLoss μ r w)
        ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  by_cases heven : Even r
  · rw [identityLearningPair_even r L heven]
    exact (even_network_laplace_order μ r L hr heven hL h ε hε hε1 ρ hρ).toLaplaceOrder
  · have hodd := Nat.not_even_iff_odd.mp heven
    have hr3 : 3 ≤ r := by obtain ⟨k,hk⟩ := hodd; omega
    by_cases heq : L = r
    · subst L
      rw [identityLearningPair_odd_eq r hodd]
      exact (odd_critical_network_laplace_order μ r hr3 hodd h ε hε hε1 ρ hρ).toLaplaceOrder
    · have hp := (odd_offcritical_network_laplace_order μ r L hr3 hodd hL heq h ε hε hε1 ρ hρ).toLaplaceOrder
      by_cases hlt : L < r
      · rw [identityLearningPair_odd_lt r L hodd hlt]
        have hm := coneLaplaceExponent_of_le L r r (by omega) hlt.le
        simp only [coneLaplaceExponent,show 2*((r:ℝ)+r)=4*r by ring] at hm
        rwa [hm] at hp
      · have hgt : r < L := by omega
        rw [identityLearningPair_odd_gt r L hodd hgt]
        have hm := coneLaplaceExponent_of_ge L r r (by omega) hgt.le
        simp only [coneLaplaceExponent,show 2*((r:ℝ)+r)=4*r by ring] at hm
        rwa [hm] at hp

/-- Explicit bounds with the unified RLCT and multiplicity. -/
theorem identity_network_laplace_bounds (μ : Measure ℝ)
    (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    ∃ c C N₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      c*(N^(-(identityLearningPair r L).1)*(Real.log N)^((identityLearningPair r L).2-1)) ≤
        (∫ w : Fin L → ℝ in ball 0 ε, Real.exp (-N*networkPopulationLoss μ r w)
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) ∧
      (∫ w : Fin L → ℝ in ball 0 ε, Real.exp (-N*networkPopulationLoss μ r w)
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) ≤
        C*(N^(-(identityLearningPair r L).1)*(Real.log N)^((identityLearningPair r L).2-1)) :=
  (identity_network_laplace_order μ r L hr hL h ε hε hε1 ρ hρ).2

/-- End-to-end unified certificate: exact RLCT, including boundary divergence,
and directly proved Laplace multiplicity for all r≥2 and L>0. -/
theorem identity_network_rlct_laplace_certificate (μ : Measure ℝ)
    (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    (∀ s : ℝ, IntegrableOn (fun w => networkPopulationLoss μ r w^(-s)) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ENNReal))) ↔ s < (identityLearningPair r L).1) ∧
    HasLaplaceOrder (identityLearningPair r L).1 (identityLearningPair r L).2
      (fun N => ∫ w : Fin L → ℝ in ball 0 ε, Real.exp (-N*networkPopulationLoss μ r w)
        ∂volume.withDensity (fun w => (ρ w : ENNReal))) :=
  ⟨identity_network_prior_integrableOn_iff μ r L hr hL h ε hε hε1 ρ hρ,
    identity_network_laplace_order μ r L hr hL h ε hε hε1 ρ hρ⟩

/-- Boundary and super-threshold divergence under the same unified hypotheses. -/
theorem identity_network_prior_not_integrable (μ : Measure ℝ)
    (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume)
    (s : ℝ) (hs : (identityLearningPair r L).1 ≤ s) :
    ¬ IntegrableOn (fun w => networkPopulationLoss μ r w^(-s)) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ENNReal))) := by
  rw [identity_network_prior_integrableOn_iff μ r L hr hL h ε hε hε1 ρ hρ s]
  exact not_lt.mpr hs

end ResidualSLT
