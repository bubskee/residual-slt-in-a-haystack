module
public import ResidualSLT.IdentityNetworkCertificate

/-! Quantitative loss comparison preserves a power/logarithmic Laplace pair. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Filter

/-- Positive rescaling preserves any power/log rate, with explicit constants. -/
theorem laplaceRate_scale (ℓ : ℝ) (m : ℕ) (b : ℝ) (hb : 0 < b) :
    ∀ᶠ N : ℝ in atTop,
      (b^(-ℓ)*(1/2:ℝ)^(m-1))*laplaceRate ℓ m N ≤ laplaceRate ℓ m (b*N) ∧
      laplaceRate ℓ m (b*N) ≤ (b^(-ℓ)*2^(m-1))*laplaceRate ℓ m N := by
  filter_upwards [eventually_ge_atTop (Real.exp (2*|Real.log b|+1))] with N hN
  have hN0 : 0 < N := (Real.exp_pos _).trans_le hN
  have hlog : 2*|Real.log b|+1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos _) hN
  have hlog0 : 0 ≤ Real.log N := by linarith [abs_nonneg (Real.log b)]
  have hl : (1/2:ℝ)*Real.log N ≤ Real.log b+Real.log N := by linarith [neg_abs_le (Real.log b)]
  have hu : Real.log b+Real.log N ≤ 2*Real.log N := by linarith [le_abs_self (Real.log b)]
  have hpos : 0 ≤ Real.log b+Real.log N := (by positivity : 0 ≤ (1/2:ℝ)*Real.log N).trans hl
  have hlp := pow_le_pow_left₀ (by positivity : 0 ≤ (1/2:ℝ)*Real.log N) hl (m-1)
  have hup := pow_le_pow_left₀ hpos hu (m-1)
  rw [mul_pow] at hlp hup
  have hp : 0 ≤ b^(-ℓ)*N^(-ℓ) := mul_nonneg (Real.rpow_pos_of_pos hb _).le (Real.rpow_pos_of_pos hN0 _).le
  unfold laplaceRate
  rw [Real.mul_rpow hb.le hN0.le,Real.log_mul hb.ne' hN0.ne']
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlp hp]
  · nlinarith [mul_le_mul_of_nonneg_left hup hp]

theorem HasLaplaceOrder.comp_mul {ℓ : ℝ} {m : ℕ} {Z : ℝ → ℝ}
    (h : HasLaplaceOrder ℓ m Z) (b : ℝ) (hb : 0 < b) :
    HasLaplaceOrder ℓ m (fun N => Z (b*N)) := by
  obtain ⟨hm,c,C,N₀,hc,hC,_,hZ⟩ := h
  have ht : Tendsto (fun N : ℝ => b*N) atTop atTop := (tendsto_const_mul_atTop_of_pos hb).mpr tendsto_id
  have he : ∀ᶠ N : ℝ in atTop,
      (c*(b^(-ℓ)*(1/2:ℝ)^(m-1)))*laplaceRate ℓ m N ≤ Z (b*N) ∧
      Z (b*N) ≤ (C*(b^(-ℓ)*2^(m-1)))*laplaceRate ℓ m N := by
    filter_upwards [ht.eventually (eventually_ge_atTop N₀),laplaceRate_scale ℓ m b hb] with N hN hs
    constructor
    · calc
        _ = c*((b^(-ℓ)*(1/2:ℝ)^(m-1))*laplaceRate ℓ m N) := mul_assoc _ _ _
        _ ≤ c*laplaceRate ℓ m (b*N) := mul_le_mul_of_nonneg_left hs.1 hc.le
        _ ≤ _ := (hZ _ hN).1
    · calc
        _ ≤ C*laplaceRate ℓ m (b*N) := (hZ _ hN).2
        _ ≤ C*((b^(-ℓ)*2^(m-1))*laplaceRate ℓ m N) := mul_le_mul_of_nonneg_left hs.2 hC.le
        _ = _ := (mul_assoc _ _ _).symm
  obtain ⟨T,hT⟩ := eventually_atTop.mp he
  exact ⟨hm,c*(b^(-ℓ)*(1/2:ℝ)^(m-1)),C*(b^(-ℓ)*2^(m-1)),max T 2,
    by positivity,by positivity,by simp,fun N hN => hT N ((le_max_left _ _).trans hN)⟩

/-- Direct numerical transfer of both Laplace exponents through a.e. loss comparison. -/
theorem laplace_pair_order_of_comparable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (D : Set α) (K J : α → ℝ)
    (hiK : ∀ N : ℝ, IntegrableOn (fun x => Real.exp (-N*K x)) D μ)
    (hiJ : ∀ N : ℝ, IntegrableOn (fun x => Real.exp (-N*J x)) D μ)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ᵐ x ∂μ.restrict D, c*K x ≤ J x ∧ J x ≤ C*K x)
    {ℓ : ℝ} {m : ℕ} (horder : HasLaplaceOrder ℓ m (fun N => ∫ x in D, Real.exp (-N*K x) ∂μ)) :
    HasLaplaceOrder ℓ m (fun N => ∫ x in D, Real.exp (-N*J x) ∂μ) := by
  obtain ⟨hm,a,A,T,ha,_,hT,hl⟩ := horder.comp_mul C hC
  obtain ⟨_,b,B,U,_,hB,_,hu⟩ := horder.comp_mul c hc
  refine ⟨hm,a,B,max T U,ha,hB,hT.trans_le (le_max_left _ _),?_⟩
  intro N hN
  have hNT : T ≤ N := (le_max_left _ _).trans hN
  have hNU : U ≤ N := (le_max_right _ _).trans hN
  have hN0 : 0 ≤ N := (zero_lt_one.trans (hT.trans_le hNT)).le
  constructor
  · apply (hl N hNT).1.trans
    apply integral_mono_ae (hiK (C*N)) (hiJ N)
    filter_upwards [hb] with x hx
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hx.2 hN0]
  · apply le_trans _ (hu N hNU).2
    apply integral_mono_ae (hiJ N) (hiK (c*N))
    filter_upwards [hb] with x hx
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hx.1 hN0]

end ResidualSLT
