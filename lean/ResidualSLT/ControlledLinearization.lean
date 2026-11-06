module
public import ResidualSLT.SparseNetworkFeatures
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Operator.Asymptotics

/-! Differentiable composition with a retained vector and a relative remainder. -/
public section
noncomputable section
namespace ResidualSLT
open Filter Asymptotics
variable {E V W α : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A controlled auxiliary remainder survives a differentiable nonlinear composition.
The retained vector need not be a coordinate system or an independent function of raw weights. -/
theorem controlled_linearization_remainder {l : Filter α}
    (Ψ : E → W) (D : E →L[ℝ] W) (hD : HasFDerivAt Ψ D 0)
    (J : V →L[ℝ] E) (v : α → E) (z : α → V) (R : α → E)
    (hv : Tendsto v l (nhds 0)) (hR : R =o[l] z)
    (he : ∀ x, v x = J (z x)+R x) :
    (fun x => Ψ (v x)-Ψ 0-(D.comp J) (z x)) =o[l] z := by
  have hvz : v =O[l] z := ((J.isBigO_comp z l).add hR.isBigO).congr_left (fun x => (he x).symm)
  have hmain : (fun x => Ψ (v x)-Ψ 0-D (v x)) =o[l] z := by
    have hh := hD.isLittleO.comp_tendsto hv
    simp only [sub_zero,Function.comp_def] at hh
    exact hh.trans_isBigO hvz
  have hrem : (fun x => D (R x)) =o[l] z := (D.isBigO_comp R l).trans_isLittleO hR
  apply (hmain.add hrem).congr_left
  intro x
  simp only [ContinuousLinearMap.comp_apply,he x,map_add]
  abel

/-- Absorbing the relative error gives uniform two-sided norm comparison. -/
theorem controlled_linearization_comparison [FiniteDimensional ℝ V] {l : Filter α}
    (Ψ : E → W) (D : E →L[ℝ] W) (hD : HasFDerivAt Ψ D 0)
    (J : V →L[ℝ] E) (v : α → E) (z : α → V) (R : α → E)
    (hv : Tendsto v l (nhds 0)) (hR : R =o[l] z)
    (he : ∀ x, v x = J (z x)+R x) (hinj : Function.Injective (D.comp J)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ x in l,
      c*‖z x‖ ≤ ‖Ψ (v x)-Ψ 0‖ ∧ ‖Ψ (v x)-Ψ 0‖ ≤ C*‖z x‖ := by
  let A := D.comp J
  obtain ⟨K,hK,ha⟩ := A.toLinearMap.injective_iff_antilipschitz.mp hinj
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  have herror := controlled_linearization_remainder Ψ D hD J v z R hv hR he
  have hsmall := herror.bound (by positivity : (0:ℝ) < 1/(2*(K:ℝ)))
  refine ⟨1/(2*(K:ℝ)),‖A‖+1/(2*(K:ℝ)),by positivity,by positivity,?_⟩
  filter_upwards [hsmall] with x hx
  have hl : ‖z x‖ ≤ (K:ℝ)*‖A (z x)‖ := ZeroHomClass.bound_of_antilipschitz A ha (z x)
  have hu := A.le_opNorm (z x)
  have ht := norm_sub_le (Ψ (v x)-Ψ 0) (A (z x))
  have ht1 := norm_le_norm_add_norm_sub (A (z x)) (Ψ (v x)-Ψ 0)
  have ht2 := norm_le_norm_add_norm_sub (Ψ (v x)-Ψ 0) (A (z x))
  rw [norm_sub_rev (A (z x))] at ht1
  change ‖Ψ (v x)-Ψ 0-A (z x)‖ ≤ _ at hx
  constructor
  · have heq : (K:ℝ)*(1/(2*(K:ℝ))) = 1/2 := by field_simp
    have hxK := mul_le_mul_of_nonneg_left hx hK0.le
    rw [← mul_assoc,heq] at hxK
    apply (mul_le_mul_iff_right₀ hK0).mp
    rw [← mul_assoc,heq]
    nlinarith [mul_le_mul_of_nonneg_left ht2 hK0.le]
  · linarith

end ResidualSLT
