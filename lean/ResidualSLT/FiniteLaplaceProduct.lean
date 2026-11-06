module
public import ResidualSLT.LaplaceProduct
public import Mathlib.MeasureTheory.Integral.Pi

/-! Exact finite products add learning exponents and logarithmic powers. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Set Finset

theorem HasLaplaceOrder.finset_prod {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (m : ι → ℕ) (Z : ι → ℝ → ℝ)
    (h : ∀ i ∈ s, HasLaplaceOrder (a i) (m i) (Z i)) :
    HasLaplaceOrder (∑ i ∈ s,a i) (1+∑ i ∈ s,(m i-1)) (fun N => ∏ i ∈ s,Z i N) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty,Nat.add_zero]
    refine ⟨by norm_num,1,1,2,by norm_num,by norm_num,by norm_num,?_⟩
    intro N _
    simp [laplaceRate]
  | @insert i s his ih =>
    have hi := h i (mem_insert_self _ _)
    have hh := hi.mul (ih (fun j hj => h j (mem_insert_of_mem hj)))
    have hm : m i+(1+∑ j ∈ s,(m j-1))-1 = 1+((m i-1)+∑ j ∈ s,(m j-1)) := by
      have hp := hi.1
      omega
    simpa only [sum_insert his,prod_insert his,hm] using hh

/-- Fubini on the actual product region, also for an empty index set. -/
theorem laplace_integral_sum_pi {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] (μ : ∀ i, Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (K : ∀ i, E i → ℝ) (D : ∀ i, Set (E i)) (N : ℝ) :
    (∫ w in Set.pi univ D, Real.exp (-N*∑ i,K i (w i)) ∂Measure.pi μ) =
      ∏ i, ∫ x in D i, Real.exp (-N*K i x) ∂μ i := by
  rw [Measure.restrict_pi_pi]
  simp_rw [mul_sum,Real.exp_sum]
  exact integral_fintype_prod_eq_prod (fun i x => Real.exp (-N*K i x))
    (μ := fun i => (μ i).restrict (D i))

theorem laplace_order_sum_pi {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] (μ : ∀ i, Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (K : ∀ i, E i → ℝ) (D : ∀ i, Set (E i)) (a : ι → ℝ) (m : ι → ℕ)
    (h : ∀ i, HasLaplaceOrder (a i) (m i) (fun N => ∫ x in D i,Real.exp (-N*K i x) ∂μ i)) :
    HasLaplaceOrder (∑ i,a i) (1+∑ i,(m i-1))
      (fun N => ∫ w in Set.pi univ D, Real.exp (-N*∑ i,K i (w i)) ∂Measure.pi μ) := by
  simpa only [laplace_integral_sum_pi] using
    HasLaplaceOrder.finset_prod univ a m (fun i N => ∫ x in D i,Real.exp (-N*K i x) ∂μ i) (fun i _ => h i)

end ResidualSLT
