module
public import ResidualSLT.OneActiveRawLinearization

/-! The separate three-direction expansion for nonnegative effective weights. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset Filter Asymptotics

@[expose] def evenRetainedInsert (a b : ℕ) (κ : ℝ) :
    (Fin 3 → ℝ) →L[ℝ] OneActiveAux (a+2) (b+2) :=
  ({ toFun := fun z => (κ*z 0, Pi.single 0 (z 1), Pi.single 0 (z 2))
     map_add' := by intro x y; ext i <;> simp [Pi.single_apply,mul_add] <;> split_ifs <;> ring
     map_smul' := by intro t z; ext i <;> simp [Pi.single_apply]; ring
   } : (Fin 3 → ℝ) →ₗ[ℝ] OneActiveAux (a+2) (b+2)).toContinuousLinearMap

theorem evenRetainedInsert_deriv (r a b : ℕ) (c κ x : ℝ) (z : Fin 3 → ℝ) :
    oneActiveAuxDeriv r (a+2) (b+2) c x (evenRetainedInsert a b κ z) =
      κ*z 0*x^r + z 1*((1+(r:ℝ)*c*x^(r-1))*x^r) + z 2*(x+c*x^r)^r := by
  simp [oneActiveAuxDeriv,evenRetainedInsert,auxActiveL,auxPreL,auxPostL,gradedEvalL_single]
  ring

theorem evenRetainedInsert_deriv_injective {ι : Type*} [Fintype ι]
    (r a b : ℕ) (hr : 2 ≤ r) (c κ : ℝ) (hc : c ≠ 0) (hκ : κ ≠ 0)
    (x : ι → ℝ) (hx : Function.Injective x)
    (hd : ∀ j, (oneActiveEvenDirections r c j).natDegree < Fintype.card ι) :
    Function.Injective ((ContinuousLinearMap.pi
      (fun i => oneActiveAuxDeriv r (a+2) (b+2) c (x i))).comp (evenRetainedInsert a b κ)) := by
  let T := (ContinuousLinearMap.pi
    (fun i => oneActiveAuxDeriv r (a+2) (b+2) c (x i))).comp (evenRetainedInsert a b κ)
  have hv := polynomial_observation_independent _ (oneActiveEvenDirections_independent r hr c hc) x hx hd
  have hker : ∀ z, T z = 0 → z = 0 := by
    intro z hz
    let t : Fin 3 → ℝ := ![κ*z 0,z 1,z 2]
    have hs : (∑ j, t j • (fun i => (oneActiveEvenDirections r c j).eval (x i))) = 0 := by
      funext i
      have hh := congrFun hz i
      change oneActiveAuxDeriv r (a+2) (b+2) c (x i) (evenRetainedInsert a b κ z) = 0 at hh
      rw [evenRetainedInsert_deriv] at hh
      simpa [t,Fin.sum_univ_succ,oneActiveEvenDirections,activeTarget,activeDerivativeFactor,add_assoc] using hh
    have ht := Fintype.linearIndependent_iff.mp hv t hs
    funext j
    fin_cases j
    · exact (mul_eq_zero.mp (ht 0)).resolve_left hκ
    · exact ht 1
    · exact ht 2
  intro u v huv
  have hh : T (u-v) = 0 := by rw [map_sub,huv,sub_self]
  exact sub_eq_zero.mp (hker _ hh)

@[expose] def inactiveEvenRemainder (r n : ℕ) (u : Fin n → ℝ) : Fin (r^n+2) → ℝ :=
  fun j => if j.val=0 then 0 else inactiveAuxVector r n u j

theorem inactiveEvenRemainder_split (r n : ℕ) (u : Fin n → ℝ) :
    inactiveAuxVector r n u = Pi.single ⟨0,by omega⟩ (∑ i, u i)+inactiveEvenRemainder r n u := by
  funext j
  by_cases hj : j.val=0
  · have he : j = ⟨0,by omega⟩ := Fin.ext hj
    rw [he]
    simp [inactiveAuxVector,inactiveEvenRemainder,graded_coeff_one,← Fin.sum_univ_eq_sum_range,zeroExtend]
  · simp [inactiveEvenRemainder,hj,Fin.ext_iff]

theorem inactiveEvenRemainder_bound (r n : ℕ) (hr : 2 ≤ r) (u : Fin n → ℝ)
    (hu : ‖u‖ ≤ 1) (hpos : ∀ i, 0 ≤ u i) :
    ‖inactiveEvenRemainder r n u‖ ≤ (signedRemainderEnvelope r n*n)*‖u‖*(∑ i, u i) := by
  have hS : 0 ≤ ∑ i, u i := sum_nonneg (fun i _ => hpos i)
  apply (pi_norm_le_iff_of_nonneg (by positivity [signedRemainderEnvelope_nonneg r n])).mpr
  intro j
  by_cases hj : j.val=0
  · simp only [inactiveEvenRemainder,ite_eq_left hj,norm_zero]
    positivity [signedRemainderEnvelope_nonneg r n]
  · have hidx : (j.val+1)*(r-1)+1 ≠ r := by
      have hh := Nat.mul_le_mul_right (r-1) (by omega : 2 ≤ j.val+1)
      omega
    have hh := effective_nonneg_higher_relative_bound r n ((j.val+1)*(r-1)+1) hidx u hu hpos
    rw [coeff_sub,coeff_X,ite_eq_right (by have hh := Nat.mul_pos (by omega : 0 < j.val+1) (by omega : 0 < r-1); omega : 1 ≠ (j.val+1)*(r-1)+1),sub_zero,
      network_coeff_graded r hr] at hh
    simpa only [inactiveEvenRemainder,ite_eq_right hj,inactiveAuxVector,Real.norm_eq_abs] using hh

theorem inactiveEvenRemainder_isLittleO {α V : Type*} [NormedAddCommGroup V] {l : Filter α}
    (r n : ℕ) (hr : 2 ≤ r) (u : α → Fin n → ℝ) (z : α → V)
    (hu : Tendsto u l (nhds 0)) (hpos : ∀ x i, 0 ≤ u x i)
    (hz : ∀ x, (∑ i, u x i) ≤ ‖z x‖) :
    (fun x => inactiveEvenRemainder r n (u x)) =o[l] z := by
  let C := signedRemainderEnvelope r n*n
  have hC : 0 ≤ C := by dsimp [C]; positivity [signedRemainderEnvelope_nonneg r n]
  have hn : Tendsto (fun x => ‖u x‖) l (nhds 0) := by simpa using hu.norm
  apply isLittleO_of_relative_bound _ _ (fun x => C*‖u x‖)
  · simpa using hn.const_mul C
  · filter_upwards [hn.eventually (Iio_mem_nhds zero_lt_one)] with x hx
    exact (inactiveEvenRemainder_bound r n hr (u x) hx.le (hpos x)).trans
      (mul_le_mul_of_nonneg_left (hz x) (mul_nonneg hC (norm_nonneg _)))

@[expose] def oneActiveEvenRetained (r p q : ℕ) (w : OneActiveAux p q) : Fin 3 → ℝ :=
  ![w.1, ∑ i, w.2.1 i^r, ∑ i, w.2.2 i^r]

@[expose] def oneActiveEvenRawRemainder (r p q : ℕ) (τ : ℝ) (w : OneActiveAux p q) :
    OneActiveAux (r^p+2) (r^q+2) :=
  ((τ+w.1)^r-τ^r-((r:ℝ)*τ^(r-1))*w.1,
    inactiveEvenRemainder r p (fun i => w.2.1 i^r),
    inactiveEvenRemainder r q (fun i => w.2.2 i^r))

theorem oneActiveEvenRawAux_decomposition (r p q : ℕ) (τ : ℝ) (w : OneActiveAux p q) :
    oneActiveRawAux r p q τ w =
      evenRetainedInsert (r^p) (r^q) ((r:ℝ)*τ^(r-1)) (oneActiveEvenRetained r p q w) +
      oneActiveEvenRawRemainder r p q τ w := by
  apply Prod.ext
  · simp [oneActiveRawAux,evenRetainedInsert,oneActiveEvenRetained,oneActiveEvenRawRemainder]
  · apply Prod.ext
    · simpa [oneActiveRawAux,evenRetainedInsert,oneActiveEvenRetained,oneActiveEvenRawRemainder] using
        inactiveEvenRemainder_split r p (fun i => w.2.1 i^r)
    · simpa [oneActiveRawAux,evenRetainedInsert,oneActiveEvenRetained,oneActiveEvenRawRemainder] using
        inactiveEvenRemainder_split r q (fun i => w.2.2 i^r)

theorem oneActiveEvenRawRemainder_isLittleO (r p q : ℕ) (hr : 2 ≤ r) (heven : Even r) (τ : ℝ) :
    oneActiveEvenRawRemainder r p q τ =o[nhds 0] oneActiveEvenRetained r p q := by
  let z := oneActiveEvenRetained r p q
  have hpre : Tendsto (fun w : OneActiveAux p q => fun i => w.2.1 i^r) (nhds 0) (nhds 0) := by
    have hh : Continuous (fun w : OneActiveAux p q => fun i => w.2.1 i^r) := by fun_prop
    simpa [Pi.zero_def,show r ≠ 0 by omega] using hh.tendsto 0
  have hpost : Tendsto (fun w : OneActiveAux p q => fun i => w.2.2 i^r) (nhds 0) (nhds 0) := by
    have hh : Continuous (fun w : OneActiveAux p q => fun i => w.2.2 i^r) := by fun_prop
    simpa [Pi.zero_def,show r ≠ 0 by omega] using hh.tendsto 0
  have hp := inactiveEvenRemainder_isLittleO r p hr _ z hpre (fun _ i => heven.pow_nonneg _) (fun w => by
    exact (le_abs_self _).trans (by simpa [z,oneActiveEvenRetained] using norm_le_pi_norm (z w) 1))
  have hq := inactiveEvenRemainder_isLittleO r q hr _ z hpost (fun _ i => heven.pow_nonneg _) (fun w => by
    exact (le_abs_self _).trans (by simpa [z,oneActiveEvenRetained] using norm_le_pi_norm (z w) 2))
  have hd : HasDerivAt (fun h : ℝ => (τ+h)^r-τ^r) ((r:ℝ)*τ^(r-1)) 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).const_add τ).pow r).sub_const (τ^r)
  have ha : (fun h : ℝ => (τ+h)^r-τ^r-((r:ℝ)*τ^(r-1))*h) =o[nhds 0] (fun h => h) := by
    simpa [mul_comm] using hd.hasFDerivAt.isLittleO
  have hz : (fun w : OneActiveAux p q => w.1) =O[nhds 0] z :=
    (Asymptotics.isBigOWith_of_le' (c := 1) (nhds 0) (fun w => by
      simpa [z,oneActiveEvenRetained] using norm_le_pi_norm (z w) 0)).isBigO
  have ha' := (ha.comp_tendsto (continuous_fst.tendsto (0:OneActiveAux p q))).trans_isBigO hz
  exact isLittleO_prod_left.mpr ⟨ha',isLittleO_prod_left.mpr ⟨hp,hq⟩⟩

theorem oneActiveEvenRaw_observation_comparison {ι : Type*} [Fintype ι]
    (r p q : ℕ) (hr : 2 ≤ r) (heven : Even r) (τ : ℝ) (hτ : τ ≠ 0)
    (x : ι → ℝ) (hx : Function.Injective x)
    (hd : ∀ j, (oneActiveEvenDirections r (τ^r) j).natDegree < Fintype.card ι) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ w : OneActiveAux p q in nhds 0,
      c*‖oneActiveEvenRetained r p q w‖ ≤
        ‖fun i => oneActiveAuxEval r (r^p+2) (r^q+2) (τ^r) (x i) (oneActiveRawAux r p q τ w)
          -oneActiveAuxEval r (r^p+2) (r^q+2) (τ^r) (x i) 0‖ ∧
      ‖fun i => oneActiveAuxEval r (r^p+2) (r^q+2) (τ^r) (x i) (oneActiveRawAux r p q τ w)
          -oneActiveAuxEval r (r^p+2) (r^q+2) (τ^r) (x i) 0‖ ≤
        C*‖oneActiveEvenRetained r p q w‖ := by
  exact controlled_linearization_comparison _ _
    (oneActiveAuxEval_pi_hasFDerivAt r (r^p+2) (r^q+2) (τ^r) x)
    _ _ _ _ (oneActiveRawAux_tendsto r p q hr τ)
    (oneActiveEvenRawRemainder_isLittleO r p q hr heven τ) (oneActiveEvenRawAux_decomposition r p q τ)
    (evenRetainedInsert_deriv_injective r (r^p) (r^q) hr (τ^r) ((r:ℝ)*τ^(r-1))
      (pow_ne_zero _ hτ) (mul_ne_zero (by exact_mod_cast (by omega : r ≠ 0)) (pow_ne_zero _ hτ)) x hx hd)

end ResidualSLT
