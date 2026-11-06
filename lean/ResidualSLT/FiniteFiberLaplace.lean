module
public import ResidualSLT.LaplaceDominance
public import ResidualSLT.NetworkCoercivity

/-! Full-space assembly from a finite collection of local contributions and a positive tail gap. -/
public section
noncomputable section
namespace ResidualSLT
open Filter MeasureTheory Set Finset

theorem integrable_exp_neg_loss {E : Type*} [MeasurableSpace E] (ν : Measure E) [IsFiniteMeasure ν]
    (K : E → ℝ) (hK : Measurable K) (hpos : ∀ x, 0 ≤ K x) (N : ℝ) (hN : 0 ≤ N) :
    Integrable (fun x => Real.exp (-N*K x)) ν := by
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [hpos x])

/-- A finite cover need not be disjoint: nonnegativity gives the upper sum bound. -/
theorem laplace_integral_le_finite_local_sum {E ι : Type*} [MeasurableSpace E] [Fintype ι]
    (ν : Measure E) [IsFiniteMeasure ν] (K : E → ℝ) (hK : Measurable K) (hpos : ∀ x,0≤K x)
    (D : ι → Set E) (hD : ∀ i,MeasurableSet (D i)) (b : ℝ)
    (hgap : ∀ x, (∀ i,x∉D i) → b≤K x) (N : ℝ) (hN : 0≤N) :
    (∫ x,Real.exp (-N*K x) ∂ν) ≤
      (∑ i,∫ x in D i,Real.exp (-N*K x) ∂ν)+ν.real univ*Real.exp (-b*N) := by
  classical
  let f := fun x => Real.exp (-N*K x)
  have hi : Integrable f ν := integrable_exp_neg_loss ν K hK hpos N hN
  have hind (i : ι) : Integrable ((D i).indicator f) ν := hi.indicator (hD i)
  have hbound (x : E) : f x ≤ (∑ i,(D i).indicator f x)+Real.exp (-b*N) := by
    have hn (i : ι) : 0 ≤ (D i).indicator f x := indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x
    by_cases hh : ∃ i,x∈D i
    · obtain ⟨i,hi⟩ := hh
      have hs : f x ≤ ∑ j,(D j).indicator f x := by
        simpa only [indicator_of_mem hi] using single_le_sum (f := fun j => (D j).indicator f x) (fun j _ => hn j) (mem_univ i)
      linarith [Real.exp_pos (-b*N)]
    · have hx : b≤K x := hgap x (by simpa using hh)
      have he : f x ≤ Real.exp (-b*N) := Real.exp_le_exp.mpr (by nlinarith)
      exact he.trans (le_add_of_nonneg_left (sum_nonneg (fun i _ => hn i)))
  have hh := integral_mono hi ((integrable_finsetSum univ (fun i _ => hind i)).add (integrable_const (Real.exp (-b*N)))) hbound
  change (∫ x,f x ∂ν) ≤ ∫ x, (∑ i,(D i).indicator f x)+Real.exp (-b*N) ∂ν at hh
  simpa only [integral_add (integrable_finsetSum univ (fun i _ => hind i)) (integrable_const _),
    integral_finsetSum univ (fun i _ => hind i),integral_indicator (hD _),integral_const,smul_eq_mul] using hh

/-- Quantitative global selection: one attaining local contribution supplies the lower bound;
all local contributions and the exponentially small tail supply the upper bound. -/
theorem finite_local_laplace_assembly {E ι : Type*} [MeasurableSpace E] [Fintype ι]
    (ν : Measure E) [IsFiniteMeasure ν] (K : E → ℝ) (hK : Measurable K) (hpos : ∀ x,0≤K x)
    (D : ι → Set E) (hD : ∀ i,MeasurableSet (D i)) (b : ℝ) (hb : 0<b)
    (hgap : ∀ x, (∀ i,x∉D i) → b≤K x) (a : ℝ) (m : ℕ)
    (hupper : ∀ i, ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℝ in atTop,
      (∫ x in D i,Real.exp (-N*K x) ∂ν) ≤ C*laplaceRate a m N)
    (W : Set E) (hlower : HasLaplaceOrder a m (fun N => ∫ x in W,Real.exp (-N*K x) ∂ν)) :
    HasLaplaceOrder a m (fun N => ∫ x,Real.exp (-N*K x) ∂ν) := by
  classical
  choose C hC hu using hupper
  obtain ⟨hm,c,A,T,hc,_,hT,hl⟩ := hlower
  let B := (∑ i,C i)+ν.real univ+1
  have hB : 0<B := by
    have hh : 0≤∑ i,C i := sum_nonneg (fun i _ => (hC i).le)
    dsimp [B]
    positivity
  have hbounds : ∀ᶠ N : ℝ in atTop,
      c*laplaceRate a m N ≤ (∫ x,Real.exp (-N*K x) ∂ν) ∧
      (∫ x,Real.exp (-N*K x) ∂ν) ≤ B*laplaceRate a m N := by
    filter_upwards [Filter.eventually_all.mpr hu,exp_neg_eventually_le_laplaceRate a m b hb,
      eventually_ge_atTop T] with N hN he hNT
    have hN0 : 0<N := (zero_lt_one.trans hT).trans_le hNT
    constructor
    · exact (hl N hNT).1.trans (setIntegral_le_integral (integrable_exp_neg_loss ν K hK hpos N hN0.le)
        (Eventually.of_forall (fun _ => (Real.exp_pos _).le)))
    · have hsum := sum_le_sum (fun i (_ : i∈Finset.univ) => hN i)
      have htail := mul_le_mul_of_nonneg_left he (show 0 ≤ ν.real Set.univ from measureReal_nonneg)
      have hi := laplace_integral_le_finite_local_sum ν K hK hpos D hD b hgap N hN0.le
      have hr : 0≤laplaceRate a m N := by
        unfold laplaceRate
        exact mul_nonneg (Real.rpow_nonneg hN0.le _) (pow_nonneg (Real.log_nonneg (hT.le.trans hNT)) _)
      rw [← sum_mul] at hsum
      dsimp [B]
      nlinarith
  obtain ⟨U,hU⟩ := eventually_atTop.mp hbounds
  exact ⟨hm,c,B,max U 2,hc,hB,by simp,fun N hN => hU N ((le_max_left _ _).trans hN)⟩

end ResidualSLT
