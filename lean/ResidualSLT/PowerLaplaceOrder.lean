module
public import ResidualSLT.GeneralCriticalLaplace

/-! Positive two-sided pure-power Laplace bounds, representing multiplicity one. -/
public section
noncomputable section
namespace ResidualSLT
open Filter MeasureTheory Set

@[expose] def PowerLaplaceUpper (ℓ : ℝ) (F : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in atTop, F N ≤ C*N^(-ℓ)
@[expose] def PowerLaplaceLower (ℓ : ℝ) (F : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ N in atTop, c*N^(-ℓ) ≤ F N
@[expose] def HasPowerLaplaceOrder (ℓ : ℝ) (F : ℝ → ℝ) : Prop :=
  PowerLaplaceLower ℓ F ∧ PowerLaplaceUpper ℓ F

variable {ℓ : ℝ}

theorem PowerLaplaceUpper.mono {F G : ℝ → ℝ} (h : PowerLaplaceUpper ℓ G)
    (hFG : ∀ᶠ N in atTop, F N ≤ G N) : PowerLaplaceUpper ℓ F := by
  obtain ⟨C, hC, hG⟩ := h
  exact ⟨C, hC, hFG.and hG |>.mono (fun _ h => h.1.trans h.2)⟩

theorem PowerLaplaceLower.mono {F G : ℝ → ℝ} (h : PowerLaplaceLower ℓ F)
    (hFG : ∀ᶠ N in atTop, F N ≤ G N) : PowerLaplaceLower ℓ G := by
  obtain ⟨c, hc, hF⟩ := h
  exact ⟨c, hc, hF.and hFG |>.mono (fun _ h => h.1.trans h.2)⟩

theorem PowerLaplaceUpper.const_mul {F : ℝ → ℝ} (h : PowerLaplaceUpper ℓ F)
    (a : ℝ) (ha : 0 < a) : PowerLaplaceUpper ℓ (fun N => a * F N) := by
  obtain ⟨C, hC, hF⟩ := h
  refine ⟨a * C, mul_pos ha hC, hF.mono ?_⟩
  intro N hN
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hN ha.le

theorem PowerLaplaceLower.const_mul {F : ℝ → ℝ} (h : PowerLaplaceLower ℓ F)
    (a : ℝ) (ha : 0 < a) : PowerLaplaceLower ℓ (fun N => a * F N) := by
  obtain ⟨c, hc, hF⟩ := h
  refine ⟨a * c, mul_pos ha hc, hF.mono ?_⟩
  intro N hN
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hN ha.le


theorem PowerLaplaceUpper.comp_mul {F : ℝ → ℝ} (h : PowerLaplaceUpper ℓ F)
    (b : ℝ) (hb : 0 < b) : PowerLaplaceUpper ℓ (fun N => F (b*N)) := by
  obtain ⟨C,hC,hF⟩ := h
  have ht : Tendsto (fun N : ℝ => b*N) atTop atTop := (tendsto_const_mul_atTop_of_pos hb).mpr tendsto_id
  refine ⟨C*b^(-ℓ), by positivity, ?_⟩
  filter_upwards [ht.eventually hF,eventually_ge_atTop (0:ℝ)] with N hN hN0
  rw [Real.mul_rpow hb.le hN0] at hN
  simpa only [mul_assoc] using hN

theorem PowerLaplaceLower.comp_mul {F : ℝ → ℝ} (h : PowerLaplaceLower ℓ F)
    (b : ℝ) (hb : 0 < b) : PowerLaplaceLower ℓ (fun N => F (b*N)) := by
  obtain ⟨c,hc,hF⟩ := h
  have ht : Tendsto (fun N : ℝ => b*N) atTop atTop := (tendsto_const_mul_atTop_of_pos hb).mpr tendsto_id
  refine ⟨c*b^(-ℓ), by positivity, ?_⟩
  filter_upwards [ht.eventually hF,eventually_ge_atTop (0:ℝ)] with N hN hN0
  rw [Real.mul_rpow hb.le hN0] at hN
  simpa only [mul_assoc] using hN

theorem PowerLaplaceUpper.add {F G : ℝ → ℝ} (hF : PowerLaplaceUpper ℓ F)
    (hG : PowerLaplaceUpper ℓ G) : PowerLaplaceUpper ℓ (fun N => F N + G N) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hG⟩ := hG
  refine ⟨C + D, add_pos hC hD, ?_⟩
  filter_upwards [hF, hG] with N hN hN'
  nlinarith

theorem powerLaplaceUpper_zero (ℓ : ℝ) : PowerLaplaceUpper ℓ (fun _ => 0) := by
  refine ⟨1, zero_lt_one, (eventually_ge_atTop (0:ℝ)).mono ?_⟩
  intro N hN
  simpa using Real.rpow_nonneg hN (-ℓ)

theorem PowerLaplaceUpper.finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ)
    (hF : ∀ i ∈ s, PowerLaplaceUpper ℓ (F i)) : PowerLaplaceUpper ℓ (fun N => ∑ i ∈ s, F i N) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using powerLaplaceUpper_zero ℓ
  | @insert i s hi ih =>
    simpa [Finset.sum_insert hi] using (hF i (by simp)).add
      (ih (fun j hj => hF j (by simp [hj])))

/-- Recover explicit eventual two-sided constants from the order predicate. -/
theorem HasPowerLaplaceOrder.bounds {F : ℝ → ℝ} (h : HasPowerLaplaceOrder ℓ F) :
    ∃ c C N₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < N₀ ∧ ∀ N, N₀ ≤ N →
      c * N^(-ℓ) ≤ F N ∧ F N ≤ C * N^(-ℓ) := by
  obtain ⟨⟨c,hc,hl⟩,⟨C,hC,hu⟩⟩ := h
  obtain ⟨N₁,hN⟩ := eventually_atTop.mp (hl.and hu)
  refine ⟨c,C,max N₁ 2,hc,hC, by simp, ?_⟩
  intro N hN'
  exact hN N (le_trans (le_max_left _ _) hN')


theorem PowerLaplaceUpper.const_mul_nonneg {F : ℝ → ℝ} (h : PowerLaplaceUpper ℓ F)
    (a : ℝ) (ha : 0 ≤ a) : PowerLaplaceUpper ℓ (fun N => a * F N) := by
  rcases eq_or_lt_of_le ha with he | he
  · simp only [← he, zero_mul]
    exact powerLaplaceUpper_zero ℓ
  · exact h.const_mul a he

/-- An upper bound with faster decay also bounds any slower power rate. -/
theorem PowerLaplaceUpper.weaken {F : ℝ → ℝ} {κ : ℝ} (h : PowerLaplaceUpper κ F)
    (hle : ℓ ≤ κ) : PowerLaplaceUpper ℓ F := by
  obtain ⟨C,hC,hF⟩ := h
  refine ⟨C,hC,?_⟩
  filter_upwards [hF,eventually_ge_atTop (1:ℝ)] with N hN hN1
  exact hN.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg hle)) hC.le)

end ResidualSLT
