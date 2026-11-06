module
public import ResidualSLT.CriticalLaplace
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Eventual positive bounds for the critical Laplace rate; no pole-order definition
is inferred from a power-integrability threshold. -/
public section
noncomputable section
namespace ResidualSLT
open Filter MeasureTheory Set
open scoped Topology

@[expose] def criticalLaplaceRate (N : ℝ) : ℝ := N ^ (-(1 / 2 : ℝ)) * Real.log N

@[expose] def CriticalLaplaceUpper (F : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in atTop, F N ≤ C * criticalLaplaceRate N

@[expose] def CriticalLaplaceLower (F : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ N in atTop, c * criticalLaplaceRate N ≤ F N

@[expose] def HasCriticalLaplaceOrder (F : ℝ → ℝ) : Prop :=
  CriticalLaplaceLower F ∧ CriticalLaplaceUpper F

theorem criticalLaplaceRate_eventually_pos : ∀ᶠ N : ℝ in atTop, 0 < criticalLaplaceRate N := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  exact mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hN) _) (Real.log_pos hN)

/-- Positive fixed rescaling preserves the critical rate, with explicit factors. -/
theorem criticalLaplaceRate_scale (b : ℝ) (hb : 0 < b) :
    ∀ᶠ N : ℝ in atTop,
      (b ^ (-(1 / 2 : ℝ)) / 2) * criticalLaplaceRate N ≤ criticalLaplaceRate (b * N) ∧
      criticalLaplaceRate (b * N) ≤ (2 * b ^ (-(1 / 2 : ℝ))) * criticalLaplaceRate N := by
  filter_upwards [eventually_ge_atTop (Real.exp (2 * |Real.log b| + 1))] with N hN
  have hN0 : 0 < N := (Real.exp_pos _).trans_le hN
  have hlog : 2 * |Real.log b| + 1 ≤ Real.log N := by
    simpa using Real.log_le_log (Real.exp_pos _) hN
  have hbpow : 0 < b ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hb _
  have hNpow : 0 < N ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hl : Real.log N / 2 ≤ Real.log b + Real.log N := by
    linarith [neg_abs_le (Real.log b)]
  have hu : Real.log b + Real.log N ≤ 2 * Real.log N := by
    linarith [le_abs_self (Real.log b)]
  unfold criticalLaplaceRate
  rw [Real.mul_rpow hb.le hN0.le, Real.log_mul hb.ne' hN0.ne']
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hl (mul_pos hbpow hNpow).le]
  · nlinarith [mul_le_mul_of_nonneg_left hu (mul_pos hbpow hNpow).le]

theorem CriticalLaplaceUpper.mono {F G : ℝ → ℝ} (h : CriticalLaplaceUpper G)
    (hFG : ∀ᶠ N in atTop, F N ≤ G N) : CriticalLaplaceUpper F := by
  obtain ⟨C, hC, hG⟩ := h
  exact ⟨C, hC, hFG.and hG |>.mono (fun _ h => h.1.trans h.2)⟩

theorem CriticalLaplaceLower.mono {F G : ℝ → ℝ} (h : CriticalLaplaceLower F)
    (hFG : ∀ᶠ N in atTop, F N ≤ G N) : CriticalLaplaceLower G := by
  obtain ⟨c, hc, hF⟩ := h
  exact ⟨c, hc, hF.and hFG |>.mono (fun _ h => h.1.trans h.2)⟩

theorem CriticalLaplaceUpper.const_mul {F : ℝ → ℝ} (h : CriticalLaplaceUpper F)
    (a : ℝ) (ha : 0 < a) : CriticalLaplaceUpper (fun N => a * F N) := by
  obtain ⟨C, hC, hF⟩ := h
  refine ⟨a * C, mul_pos ha hC, hF.mono ?_⟩
  intro N hN
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hN ha.le

theorem CriticalLaplaceLower.const_mul {F : ℝ → ℝ} (h : CriticalLaplaceLower F)
    (a : ℝ) (ha : 0 < a) : CriticalLaplaceLower (fun N => a * F N) := by
  obtain ⟨c, hc, hF⟩ := h
  refine ⟨a * c, mul_pos ha hc, hF.mono ?_⟩
  intro N hN
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hN ha.le

theorem CriticalLaplaceUpper.comp_mul {F : ℝ → ℝ} (h : CriticalLaplaceUpper F)
    (b : ℝ) (hb : 0 < b) : CriticalLaplaceUpper (fun N => F (b * N)) := by
  obtain ⟨C, hC, hF⟩ := h
  have hT : Tendsto (fun N : ℝ => b * N) atTop atTop := (tendsto_const_mul_atTop_of_pos hb).mpr tendsto_id
  refine ⟨C * (2 * b ^ (-(1 / 2 : ℝ))), by positivity, ?_⟩
  filter_upwards [hT.eventually hF, criticalLaplaceRate_scale b hb] with N hN hscale
  nlinarith [mul_le_mul_of_nonneg_left hscale.2 hC.le]

theorem CriticalLaplaceLower.comp_mul {F : ℝ → ℝ} (h : CriticalLaplaceLower F)
    (b : ℝ) (hb : 0 < b) : CriticalLaplaceLower (fun N => F (b * N)) := by
  obtain ⟨c, hc, hF⟩ := h
  have hT : Tendsto (fun N : ℝ => b * N) atTop atTop := (tendsto_const_mul_atTop_of_pos hb).mpr tendsto_id
  refine ⟨c * (b ^ (-(1 / 2 : ℝ)) / 2), by positivity, ?_⟩
  filter_upwards [hT.eventually hF, criticalLaplaceRate_scale b hb] with N hN hscale
  nlinarith [mul_le_mul_of_nonneg_left hscale.1 hc.le]

theorem CriticalLaplaceUpper.add {F G : ℝ → ℝ} (hF : CriticalLaplaceUpper F)
    (hG : CriticalLaplaceUpper G) : CriticalLaplaceUpper (fun N => F N + G N) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hG⟩ := hG
  refine ⟨C + D, add_pos hC hD, ?_⟩
  filter_upwards [hF, hG] with N hN hN'
  nlinarith

theorem criticalLaplaceUpper_zero : CriticalLaplaceUpper (fun _ => 0) := by
  exact ⟨1, zero_lt_one, criticalLaplaceRate_eventually_pos.mono (fun N h => by simpa using h.le)⟩

theorem CriticalLaplaceUpper.finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ)
    (hF : ∀ i ∈ s, CriticalLaplaceUpper (F i)) : CriticalLaplaceUpper (fun N => ∑ i ∈ s, F i N) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using criticalLaplaceUpper_zero
  | @insert i s hi ih =>
    simpa [Finset.sum_insert hi] using (hF i (by simp)).add
      (ih (fun j hj => hF j (by simp [hj])))

theorem criticalLaplace_has_order : HasCriticalLaplaceOrder criticalLaplace := by
  obtain ⟨c,C,N₀,hc,hC,_,h⟩ := criticalLaplace_two_sided
  exact ⟨⟨c,hc,(eventually_ge_atTop N₀).mono (fun N hN => (h N hN).1)⟩,
    ⟨C,hC,(eventually_ge_atTop N₀).mono (fun N hN => (h N hN).2)⟩⟩

/-- Recover explicit eventual two-sided constants from the order predicate. -/
theorem HasCriticalLaplaceOrder.bounds {F : ℝ → ℝ} (h : HasCriticalLaplaceOrder F) :
    ∃ c C N₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < N₀ ∧ ∀ N, N₀ ≤ N →
      c * criticalLaplaceRate N ≤ F N ∧ F N ≤ C * criticalLaplaceRate N := by
  obtain ⟨⟨c,hc,hl⟩,⟨C,hC,hu⟩⟩ := h
  obtain ⟨N₁,hN⟩ := eventually_atTop.mp (hl.and hu)
  refine ⟨c,C,max N₁ 2,hc,hC, by simp, ?_⟩
  intro N hN'
  exact hN N (le_trans (le_max_left _ _) hN')


theorem CriticalLaplaceUpper.const_mul_nonneg {F : ℝ → ℝ} (h : CriticalLaplaceUpper F)
    (a : ℝ) (ha : 0 ≤ a) : CriticalLaplaceUpper (fun N => a * F N) := by
  rcases eq_or_lt_of_le ha with he | he
  · simp only [← he, zero_mul]
    exact criticalLaplaceUpper_zero
  · exact h.const_mul a he

end ResidualSLT
