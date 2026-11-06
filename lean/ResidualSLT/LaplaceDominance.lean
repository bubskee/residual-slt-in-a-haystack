module
public import ResidualSLT.ArrangementGlobalPair
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Lexicographic selection of power/logarithmic rates and exponential tails. -/
public section
noncomputable section
namespace ResidualSLT
open Filter MeasureTheory Set

/-- A smaller exponent dominates any logarithmic power; at equal exponent the larger
multiplicity dominates. Equal contributions never add their logarithmic exponents. -/
theorem laplaceRate_eventually_le (a b : ℝ) (m n : ℕ)
    (h : a<b ∨ a=b ∧ n≤m) : ∀ᶠ N : ℝ in atTop, laplaceRate b n N ≤ laplaceRate a m N := by
  have hlog : ∀ᶠ N : ℝ in atTop, 0<N ∧ 1≤Real.log N := by
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
    exact ⟨(Real.exp_pos 1).trans_le hN,by simpa using Real.log_le_log (Real.exp_pos 1) hN⟩
  rcases h with hab | ⟨rfl,hnm⟩
  · have hh := (isLittleO_log_rpow_rpow_atTop ((n-1:ℕ):ℝ) (sub_pos.mpr hab)).bound zero_lt_one
    filter_upwards [hh,hlog] with N hN hNlog
    have hnp : (Real.log N)^(n-1) ≤ N^(b-a) := by
      simpa only [Real.rpow_natCast,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (zero_le_one.trans hNlog.2) (n-1)),
        abs_of_nonneg (Real.rpow_nonneg hNlog.1.le _),one_mul] using hN
    have hm : 1 ≤ (Real.log N)^(m-1) := one_le_pow₀ hNlog.2
    calc
      laplaceRate b n N ≤ N^(-b)*N^(b-a) := mul_le_mul_of_nonneg_left hnp (Real.rpow_nonneg hNlog.1.le _)
      _ = N^(-a) := by rw [← Real.rpow_add hNlog.1]; congr 1; ring
      _ ≤ laplaceRate a m N := by
        simpa only [mul_one,laplaceRate] using mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hNlog.1.le (-a))
  · filter_upwards [hlog] with N hN
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hN.1.le (-a))
    exact pow_le_pow_right₀ hN.2 (Nat.sub_le_sub_right hnm 1)

theorem exp_neg_eventually_le_laplaceRate (a : ℝ) (m : ℕ) (b : ℝ) (hb : 0 < b) :
    ∀ᶠ N : ℝ in atTop, Real.exp (-b*N) ≤ laplaceRate a m N := by
  have hh := (isLittleO_exp_neg_mul_rpow_atTop hb (-a)).bound zero_lt_one
  filter_upwards [hh,eventually_ge_atTop (Real.exp 1)] with N hN hlarge
  have hN0 : 0<N := (Real.exp_pos _).trans_le hlarge
  have hlog : 1≤Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) hlarge
  have he : Real.exp (-b*N) ≤ N^(-a) := by
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),abs_of_nonneg (Real.rpow_nonneg hN0.le _),one_mul] using hN
  exact he.trans (by simpa only [mul_one,laplaceRate] using
    mul_le_mul_of_nonneg_left (one_le_pow₀ hlog (n := m-1)) (Real.rpow_nonneg hN0.le (-a)))

/-- Local upper bounds can be compared directly with a globally dominant pair. -/
theorem HasLaplaceOrder.upper_of_dominates {a b : ℝ} {m n : ℕ} {Z : ℝ → ℝ}
    (hZ : HasLaplaceOrder b n Z) (h : a<b ∨ a=b ∧ n≤m) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℝ in atTop, Z N ≤ C*laplaceRate a m N := by
  obtain ⟨_,c,C,T,_,hC,_,hb⟩ := hZ
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop T,laplaceRate_eventually_le a b m n h] with N hN hr
  exact (hb N hN).2.trans (mul_le_mul_of_nonneg_left hr hC.le)

end ResidualSLT
