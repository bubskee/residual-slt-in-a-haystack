module
public import ResidualSLT.SmallActiveFiber
public import Mathlib.Algebra.Polynomial.Roots

/-! Full raw-weight fibers, including every even-degree sign choice. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset Set MeasureTheory

theorem one_active_raw_fiber (r L : ℕ) (hr : 2 ≤ r) (c : ℝ) (hc : c ≠ 0) (w : Fin L → ℝ) :
    network r (fun i => zeroExtend w i^r) L = activeTarget r c ↔
      ∃ i : Fin L, w i^r=c ∧ ∀ j, j ≠ i → w j=0 := by
  rw [one_active_effective_fiber r L hr c hc]
  constructor
  · rintro ⟨i,hi,hc',hz⟩
    refine ⟨⟨i,hi⟩,by simpa [zeroExtend,hi] using hc',?_⟩
    intro j hji
    have he : j.val ≠ i := by intro he; apply hji; exact Fin.ext he
    have hh := hz j.val j.isLt he
    simpa [zeroExtend,j.isLt,pow_eq_zero_iff (by omega : r ≠ 0)] using hh
  · rintro ⟨i,hc',hz⟩
    refine ⟨i.val,i.isLt,by simpa [zeroExtend,i.isLt] using hc',?_⟩
    intro j hj hji
    have he : (⟨j,hj⟩ : Fin L) ≠ i := by intro hh; exact hji (congrArg Fin.val hh)
    simp [zeroExtend,hj,hz ⟨j,hj⟩ he,show r ≠ 0 by omega]

theorem two_active_raw_fiber (r L : ℕ) (hr : 2 ≤ r) (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) (w : Fin L → ℝ) :
    network r (fun i => zeroExtend w i^r) L = twoActiveTarget r c d ↔
      ∃ i j : Fin L, i<j ∧ w i^r=c ∧ w j^r=d ∧ ∀ a, a ≠ i → a ≠ j → w a=0 := by
  rw [two_active_effective_fiber r L hr c d hc hd]
  constructor
  · rintro ⟨i,j,hij,hj,hi',hj',hz⟩
    refine ⟨⟨i,by omega⟩,⟨j,hj⟩,hij,by simpa [zeroExtend,show i<L by omega] using hi',
      by simpa [zeroExtend,hj] using hj',?_⟩
    intro a hai haj
    have hia : a.val ≠ i := by intro he; apply hai; exact Fin.ext he
    have hja : a.val ≠ j := by intro he; apply haj; exact Fin.ext he
    have hh := hz a.val a.isLt hia hja
    simpa [zeroExtend,a.isLt,pow_eq_zero_iff (by omega : r ≠ 0)] using hh
  · rintro ⟨i,j,hij,hi',hj',hz⟩
    refine ⟨i.val,j.val,hij,j.isLt,by simpa [zeroExtend,i.isLt] using hi',
      by simpa [zeroExtend,j.isLt] using hj',?_⟩
    intro a ha hai haj
    have hi : (⟨a,ha⟩ : Fin L) ≠ i := by intro he; exact hai (congrArg Fin.val he)
    have hj : (⟨a,ha⟩ : Fin L) ≠ j := by intro he; exact haj (congrArg Fin.val he)
    simp [zeroExtend,ha,hz ⟨a,ha⟩ hi hj,show r ≠ 0 by omega]

theorem one_active_raw_fiber_odd (r L : ℕ) (hr : 2 ≤ r) (hodd : Odd r) (α : ℝ) (hα : α ≠ 0) (w : Fin L → ℝ) :
    network r (fun i => zeroExtend w i^r) L = activeTarget r (α^r) ↔
      ∃ i : Fin L, w i=α ∧ ∀ j, j ≠ i → w j=0 := by
  simp only [one_active_raw_fiber r L hr _ (pow_ne_zero _ hα),hodd.pow_inj]

theorem one_active_raw_fiber_even (r L : ℕ) (hr : 2 ≤ r) (heven : Even r) (α : ℝ) (hα : α ≠ 0) (w : Fin L → ℝ) :
    network r (fun i => zeroExtend w i^r) L = activeTarget r (α^r) ↔
      ∃ i : Fin L, (w i=α ∨ w i= -α) ∧ ∀ j, j ≠ i → w j=0 := by
  simp only [one_active_raw_fiber r L hr _ (pow_ne_zero _ hα),
    pow_eq_pow_iff_of_ne_zero (by omega : r ≠ 0),heven,and_true]

theorem two_active_raw_fiber_odd (r L : ℕ) (hr : 2 ≤ r) (hodd : Odd r)
    (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0) (w : Fin L → ℝ) :
    network r (fun i => zeroExtend w i^r) L = twoActiveTarget r (α^r) (β^r) ↔
      ∃ i j : Fin L, i<j ∧ w i=α ∧ w j=β ∧ ∀ a, a ≠ i → a ≠ j → w a=0 := by
  simp only [two_active_raw_fiber r L hr _ _ (pow_ne_zero _ hα) (pow_ne_zero _ hβ),hodd.pow_inj]

theorem two_active_raw_fiber_even (r L : ℕ) (hr : 2 ≤ r) (heven : Even r)
    (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0) (w : Fin L → ℝ) :
    network r (fun i => zeroExtend w i^r) L = twoActiveTarget r (α^r) (β^r) ↔
      ∃ i j : Fin L, i<j ∧ (w i=α ∨ w i= -α) ∧ (w j=β ∨ w j= -β) ∧
        ∀ a, a ≠ i → a ≠ j → w a=0 := by
  simp only [two_active_raw_fiber r L hr _ _ (pow_ne_zero _ hα) (pow_ne_zero _ hβ),
    pow_eq_pow_iff_of_ne_zero (by omega : r ≠ 0),heven,and_true]

theorem finite_real_power_fiber (r : ℕ) (hr : 0 < r) (c : ℝ) : {x : ℝ | x^r=c}.Finite := by
  have hn : (X^r-C c : ℝ[X]) ≠ 0 := by
    intro he
    have hh := congrArg (fun p : ℝ[X] => p.coeff r) he
    simp [coeff_sub,coeff_C,hr.ne'] at hh
  simpa [Polynomial.IsRoot,sub_eq_zero] using Polynomial.finite_setOfPred_isRoot hn

theorem one_active_raw_fiber_finite (r L : ℕ) (hr : 2 ≤ r) (c : ℝ) (hc : c ≠ 0) :
    {w : Fin L → ℝ | network r (fun i => zeroExtend w i^r) L = activeTarget r c}.Finite := by
  have hf := Set.Finite.pi' (fun _ : Fin L => (Set.finite_singleton (0:ℝ)).union (finite_real_power_fiber r (by omega) c))
  apply hf.subset
  intro w hw a
  obtain ⟨i,hi,hz⟩ := (one_active_raw_fiber r L hr c hc w).mp hw
  by_cases he : a=i
  · subst a; exact Or.inr hi
  · exact Or.inl (hz a he)

theorem two_active_raw_fiber_finite (r L : ℕ) (hr : 2 ≤ r) (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) :
    {w : Fin L → ℝ | network r (fun i => zeroExtend w i^r) L = twoActiveTarget r c d}.Finite := by
  have hf := Set.Finite.pi' (fun _ : Fin L => ((Set.finite_singleton (0:ℝ)).union
    (finite_real_power_fiber r (by omega) c)).union (finite_real_power_fiber r (by omega) d))
  apply hf.subset
  intro w hw a
  obtain ⟨i,j,hij,hi,hj,hz⟩ := (two_active_raw_fiber r L hr c d hc hd w).mp hw
  by_cases he : a=i
  · subst a; exact Or.inl (Or.inr hi)
  by_cases he' : a=j
  · subst a; exact Or.inr hj
  · exact Or.inl (Or.inl (hz a he he'))

/-- Positive sparse Gram makes zero population loss equivalent to exact polynomial equality. -/
theorem networkTargetLoss_eq_zero_iff (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (t w : Fin L → ℝ) :
    networkTargetLoss μ r t w=0 ↔
      network r (fun i => zeroExtend w i^r) L = network r (fun i => zeroExtend t i^r) L := by
  constructor
  · intro he
    obtain ⟨a,A,ha,_,hb⟩ := networkTargetLoss_coefficient_bounds μ r L hr hL hμ
    have hh := (hb t w).1
    rw [he] at hh
    have hs : ‖networkTargetCoefficients r t w‖^2 ≤ 0 := le_of_mul_le_mul_left (show a*‖networkTargetCoefficients r t w‖^2 ≤ a*0 by simpa using hh) ha
    have hn : ‖networkTargetCoefficients r t w‖=0 := by nlinarith [norm_nonneg (networkTargetCoefficients r t w)]
    have hz := norm_eq_zero.mp hn
    apply Polynomial.funext
    intro x
    have h := networkTarget_feature_expansion r L hr hL t w x
    simp only [hz,Pi.zero_apply,zero_mul,sum_const_zero] at h
    exact sub_eq_zero.mp h
  · intro he
    simp [networkTargetLoss,he]

end ResidualSLT
