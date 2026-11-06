module
public import ResidualSLT.FiniteFiberLaplace

/-! Positive continuous densities supply the local bounded-prior hypotheses. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Metric Set Filter

theorem continuous_positive_prior_local_bounds {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] (μ : Measure E) (ρ : E → NNReal)
    (hρ : Measurable ρ) (x : E) (hc : ContinuousAt ρ x) (hp : 0<ρ x) :
    ∃ ε : ℝ, 0<ε ∧ BoundedPositivePriorOn ρ (ball x ε) μ := by
  have he : ∀ᶠ w in nhds x, ρ x/2 < ρ w ∧ ρ w < ρ x+1 :=
    hc (Ioo_mem_nhds (half_lt_self hp) (lt_add_one (ρ x)))
  obtain ⟨ε,hε,hb⟩ := Metric.eventually_nhds_iff_ball.mp he
  refine ⟨ε,hε,hρ,ρ x/2,ρ x+1,by positivity,?_⟩
  filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
  exact ⟨(hb w hw).1.le,(hb w hw).2.le⟩

/-- Choose one ball satisfying both the certified radius and the continuous positive prior. -/
theorem local_laplace_with_continuous_prior {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (K : E → ℝ) (x : E) (a : ℝ) (m : ℕ)
    (hlocal : ∃ ε₀ : ℝ,0<ε₀ ∧ ε₀≤1 ∧ ∀ ε : ℝ,0<ε → ε≤ε₀ →
      ∀ ρ : E → NNReal,BoundedPositivePriorOn ρ (ball x ε) μ →
        HasLaplaceOrder a m (fun N => ∫ w in ball x ε,Real.exp (-N*K w) ∂μ.withDensity (fun w => (ρ w:ENNReal))))
    (ρ : E → NNReal) (hρ : Measurable ρ) (hc : ContinuousAt ρ x) (hp : 0<ρ x) :
    ∃ ε : ℝ,0<ε ∧ HasLaplaceOrder a m
      (fun N => ∫ w in ball x ε,Real.exp (-N*K w) ∂μ.withDensity (fun w => (ρ w:ENNReal))) := by
  obtain ⟨ε₀,hε₀,_,hl⟩ := hlocal
  obtain ⟨δ,hδ,hprior⟩ := continuous_positive_prior_local_bounds μ ρ hρ x hc hp
  exact ⟨min ε₀ δ,lt_min hε₀ hδ,hl _ (lt_min hε₀ hδ) (min_le_left _ _) ρ
    (hprior.mono (ball_subset_ball (min_le_right _ _)))⟩

end ResidualSLT
