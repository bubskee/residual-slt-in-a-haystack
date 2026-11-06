module
public import ResidualSLT.OneActiveComposition
public import ResidualSLT.PolynomialObservation
public import ResidualSLT.InactiveGroupCoordinates

/-! Retained coordinates and the injective one-active differential. -/
public section
noncomputable section
namespace ResidualSLT
open Finset Polynomial Filter Asymptotics

@[expose] def signedRetainedInsert (a b : ℕ) (κ : ℝ) :
    (Fin 5 → ℝ) →L[ℝ] OneActiveAux (a+2) (b+2) :=
  ({ toFun := fun z => (κ*z 0,
        Pi.single 0 (z 1)+Pi.single 1 (z 2),
        Pi.single 0 (z 3)+Pi.single 1 (z 4))
     map_add' := by
       intro x y
       ext i <;> simp [Pi.single_apply,mul_add] <;> (try split_ifs) <;> ring
     map_smul' := by
       intro t z
       ext i <;> simp [Pi.single_apply]
       ring
   } : (Fin 5 → ℝ) →ₗ[ℝ] OneActiveAux (a+2) (b+2)).toContinuousLinearMap

theorem gradedEvalL_single (r n : ℕ) (x t : ℝ) (j : Fin n) :
    gradedEvalL r n x (Pi.single j t) = t*x^(r+j.val*(r-1)) := by
  rw [gradedEvalL_apply]
  simp [Pi.single_apply,ite_mul]

/-- Explicit retained differential at one observation value. -/
theorem signedRetainedInsert_deriv (r a b : ℕ) (hr : 2 ≤ r) (c κ x : ℝ) (z : Fin 5 → ℝ) :
    oneActiveAuxDeriv r (a+2) (b+2) c x (signedRetainedInsert a b κ z) =
      κ*z 0*x^r + z 1*((1+(r:ℝ)*c*x^(r-1))*x^r) +
      z 2*((1+(r:ℝ)*c*x^(r-1))*x^(2*r-1)) +
      z 3*(x+c*x^r)^r+z 4*(x+c*x^r)^(2*r-1) := by
  have he : r+(r-1)=2*r-1 := by omega
  simp [oneActiveAuxDeriv,signedRetainedInsert,auxActiveL,auxPreL,auxPostL,
    gradedEvalL_single,he]
  ring

/-- Injectivity after observing all retained polynomials below the interpolation bound. -/
theorem signedRetainedInsert_deriv_injective {ι : Type*} [Fintype ι]
    (r a b : ℕ) (hr : 3 ≤ r) (c κ : ℝ) (hc : c ≠ 0) (hκ : κ ≠ 0)
    (x : ι → ℝ) (hx : Function.Injective x)
    (hd : ∀ j, (oneActiveSignedDirections r c j).natDegree < Fintype.card ι) :
    Function.Injective ((ContinuousLinearMap.pi
      (fun i => oneActiveAuxDeriv r (a+2) (b+2) c (x i))).comp (signedRetainedInsert a b κ)) := by
  let T := (ContinuousLinearMap.pi
    (fun i => oneActiveAuxDeriv r (a+2) (b+2) c (x i))).comp (signedRetainedInsert a b κ)
  have hv := polynomial_observation_independent _ (oneActiveSignedDirections_independent r hr c hc) x hx hd
  have hker : ∀ z, T z = 0 → z = 0 := by
    intro z hz
    let t : Fin 5 → ℝ := ![κ*z 0,z 1,z 2,z 3,z 4]
    have hs : (∑ j, t j • (fun i => (oneActiveSignedDirections r c j).eval (x i))) = 0 := by
      funext i
      have hh := congrFun hz i
      change oneActiveAuxDeriv r (a+2) (b+2) c (x i) (signedRetainedInsert a b κ z) = 0 at hh
      rw [signedRetainedInsert_deriv r a b (by omega)] at hh
      simpa [t,Fin.sum_univ_succ,oneActiveSignedDirections,activeTarget,activeDerivativeFactor,add_assoc] using hh
    have ht := Fintype.linearIndependent_iff.mp hv t hs
    funext j
    fin_cases j
    · exact (mul_eq_zero.mp (ht 0)).resolve_left hκ
    · exact ht 1
    · exact ht 2
    · exact ht 3
    · exact ht 4
  intro u v huv
  have hh : T (u-v) = 0 := by rw [map_sub,huv,sub_self]
  exact sub_eq_zero.mp (hker _ hh)

/-- A coefficient remainder bound with a vanishing relative factor is little-o. -/
theorem isLittleO_of_relative_bound {α E V : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup V] {l : Filter α}
    (R : α → E) (z : α → V) (e : α → ℝ)
    (he : Tendsto e l (nhds 0)) (hb : ∀ᶠ x in l, ‖R x‖ ≤ e x*‖z x‖) :
    R =o[l] z := by
  apply IsLittleO.of_bound
  intro δ hδ
  filter_upwards [he.eventually (Iio_mem_nhds hδ),hb] with x hx hb
  exact hb.trans (mul_le_mul_of_nonneg_right hx.le (norm_nonneg _))

/-- Omitted group coefficients are little-o of any retained vector controlling S and B. -/
theorem inactiveAuxRemainder_isLittleO {α V : Type*} [NormedAddCommGroup V] {l : Filter α}
    (r n : ℕ) (hr : 2 ≤ r) (u : α → Fin n → ℝ) (z : α → V)
    (hu : Tendsto u l (nhds 0))
    (hz : ∀ x, |∑ i, u x i|+|(graded r (zeroExtend (u x)) n).coeff 2| ≤ 2*‖z x‖) :
    (fun x => inactiveAuxRemainder r n (u x)) =o[l] z := by
  let C := signedRemainderEnvelope r n*n*n
  have hC : 0 ≤ C := by dsimp [C]; positivity [signedRemainderEnvelope_nonneg r n]
  have hn : Tendsto (fun x => ‖u x‖) l (nhds 0) := by simpa using hu.norm
  have hs : Tendsto (fun x => |∑ i, u x i|) l (nhds 0) := by
    have hh : Continuous (fun v : Fin n → ℝ => |∑ i, v i|) := by fun_prop
    simpa [Function.comp_def] using hh.continuousAt.tendsto.comp hu
  apply isLittleO_of_relative_bound _ _ (fun x => C*‖u x‖*2)
  · simpa using (hn.const_mul C).mul_const 2
  · filter_upwards [hn.eventually (Iio_mem_nhds zero_lt_one),hs.eventually (Iio_mem_nhds zero_lt_one)] with x hux hsx
    apply (inactiveAuxRemainder_bound r n hr (u x) hux.le hsx.le).trans
    simpa [C,mul_assoc] using mul_le_mul_of_nonneg_left (hz x) (mul_nonneg hC (norm_nonneg _))

end ResidualSLT
