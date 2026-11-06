module
public import ResidualSLT.LaplacePairTransfer
public import Mathlib.MeasureTheory.Integral.Prod

/-! Addition of independent loss contributions adds exponents and logarithmic powers. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Set

theorem laplaceRate_mul (a b : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (N : ℝ) (hN : 0 < N) :
    laplaceRate a m N*laplaceRate b n N = laplaceRate (a+b) (m+n-1) N := by
  have he : m+n-1-1 = (m-1)+(n-1) := by omega
  simp only [laplaceRate,he,pow_add,neg_add,Real.rpow_add hN]
  ring

/-- Logarithmic powers, rather than multiplicities, add under products. -/
theorem HasLaplaceOrder.mul {a b : ℝ} {m n : ℕ} {Z T : ℝ → ℝ}
    (hZ : HasLaplaceOrder a m Z) (hT : HasLaplaceOrder b n T) :
    HasLaplaceOrder (a+b) (m+n-1) (fun N => Z N*T N) := by
  obtain ⟨hm,c,C,N₀,hc,hC,hN₀,hZ⟩ := hZ
  obtain ⟨hn,d,D,M₀,hd,hD,_,hT⟩ := hT
  refine ⟨by omega,c*d,C*D,max N₀ M₀,mul_pos hc hd,mul_pos hC hD,
    hN₀.trans_le (le_max_left _ _),?_⟩
  intro N hN
  have hN' := (le_max_left N₀ M₀).trans hN
  have hM' := (le_max_right N₀ M₀).trans hN
  have hN1 : 1 < N := hN₀.trans_le hN'
  have hN0 : 0 < N := zero_lt_one.trans hN1
  have hr (a : ℝ) (m : ℕ) : 0 ≤ laplaceRate a m N := by
    unfold laplaceRate
    exact mul_nonneg (Real.rpow_pos_of_pos hN0 _).le (pow_nonneg (Real.log_nonneg hN1.le) _)
  have hZ0 : 0 ≤ Z N := (mul_nonneg hc.le (hr a m)).trans (hZ N hN').1
  have hT0 : 0 ≤ T N := (mul_nonneg hd.le (hr b n)).trans (hT N hM').1
  rw [← laplaceRate_mul a b m n hm hn N hN0]
  constructor
  · have hh := mul_le_mul (hZ N hN').1 (hT N hM').1 (mul_nonneg hd.le (hr b n)) hZ0
    nlinarith only [hh]
  · have hh := mul_le_mul (hZ N hN').2 (hT N hM').2 hT0 (mul_nonneg hC.le (hr a m))
    nlinarith only [hh]

/-- Exact factorization on the actual product domain, with the product measure explicit. -/
theorem laplace_integral_add_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (K : α → ℝ) (J : β → ℝ) (D : Set α) (E : Set β) (N : ℝ) :
    (∫ x in D ×ˢ E, Real.exp (-N*(K x.1+J x.2)) ∂μ.prod ν) =
      (∫ x in D, Real.exp (-N*K x) ∂μ)*(∫ y in E, Real.exp (-N*J y) ∂ν) := by
  simp_rw [mul_add,Real.exp_add]
  exact setIntegral_prod_mul (fun x => Real.exp (-N*K x)) (fun y => Real.exp (-N*J y)) D E

/-- A product-region sum inherits the exact Laplace pair of its two summands. -/
theorem laplace_order_add_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (K : α → ℝ) (J : β → ℝ) (D : Set α) (E : Set β)
    {a b : ℝ} {m n : ℕ}
    (hK : HasLaplaceOrder a m (fun N => ∫ x in D, Real.exp (-N*K x) ∂μ))
    (hJ : HasLaplaceOrder b n (fun N => ∫ y in E, Real.exp (-N*J y) ∂ν)) :
    HasLaplaceOrder (a+b) (m+n-1)
      (fun N => ∫ x in D ×ˢ E, Real.exp (-N*(K x.1+J x.2)) ∂μ.prod ν) := by
  simpa only [laplace_integral_add_prod] using hK.mul hJ

end ResidualSLT
