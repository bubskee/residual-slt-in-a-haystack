module
public import ResidualSLT.OneActiveRetainedMap
public import Mathlib.Analysis.Asymptotics.Prod
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Pull the auxiliary expansion back to all raw directions near a one-active realization. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset Filter Asymptotics

@[expose] def oneActiveRawAux (r p q : ℕ) (τ : ℝ)
    (w : OneActiveAux p q) : OneActiveAux (r^p+2) (r^q+2) :=
  ((τ+w.1)^r-τ^r, inactiveAuxVector r p (fun i => w.2.1 i^r),
    inactiveAuxVector r q (fun i => w.2.2 i^r))

@[expose] def oneActiveRetained (r p q : ℕ) (w : OneActiveAux p q) : Fin 5 → ℝ :=
  ![w.1, ∑ i, w.2.1 i^r, (graded r (zeroExtend (fun i => w.2.1 i^r)) p).coeff 2,
    ∑ i, w.2.2 i^r, (graded r (zeroExtend (fun i => w.2.2 i^r)) q).coeff 2]

@[expose] def oneActiveRawRemainder (r p q : ℕ) (τ : ℝ) (w : OneActiveAux p q) :
    OneActiveAux (r^p+2) (r^q+2) :=
  ((τ+w.1)^r-τ^r-((r:ℝ)*τ^(r-1))*w.1,
    inactiveAuxRemainder r p (fun i => w.2.1 i^r),
    inactiveAuxRemainder r q (fun i => w.2.2 i^r))

theorem oneActiveRawAux_decomposition (r p q : ℕ) (τ : ℝ) (w : OneActiveAux p q) :
    oneActiveRawAux r p q τ w =
      signedRetainedInsert (r^p) (r^q) ((r:ℝ)*τ^(r-1)) (oneActiveRetained r p q w) +
      oneActiveRawRemainder r p q τ w := by
  apply Prod.ext
  · simp [oneActiveRawAux,signedRetainedInsert,oneActiveRetained,oneActiveRawRemainder]
  · apply Prod.ext
    · simpa [oneActiveRawAux,signedRetainedInsert,oneActiveRetained,oneActiveRawRemainder] using
        inactiveAuxVector_split r p (fun i => w.2.1 i^r)
    · simpa [oneActiveRawAux,signedRetainedInsert,oneActiveRetained,oneActiveRawRemainder] using
        inactiveAuxVector_split r q (fun i => w.2.2 i^r)

theorem oneActiveRawAux_tendsto (r p q : ℕ) (hr : 2 ≤ r) (τ : ℝ) :
    Tendsto (oneActiveRawAux r p q τ) (nhds 0) (nhds 0) := by
  have hpre : Continuous (fun w : OneActiveAux p q => inactiveAuxVector r p (fun i => w.2.1 i^r)) :=
    (inactiveAuxVector_continuous r p hr).comp (by fun_prop)
  have hpost : Continuous (fun w : OneActiveAux p q => inactiveAuxVector r q (fun i => w.2.2 i^r)) :=
    (inactiveAuxVector_continuous r q hr).comp (by fun_prop)
  have hh : Continuous (oneActiveRawAux r p q τ) := by
    unfold oneActiveRawAux
    exact (by fun_prop : Continuous (fun w : OneActiveAux p q => (τ+w.1)^r-τ^r)).prodMk (hpre.prodMk hpost)
  have hz (n : ℕ) : inactiveAuxVector r n (fun _ => 0) = fun _ => 0 := by
    simpa only [Pi.zero_def] using inactiveAuxVector_zero r n
  simpa [oneActiveRawAux,Pi.zero_def,Prod.zero_eq_mk,show r ≠ 0 by omega,hz] using hh.tendsto 0

/-- The actual raw pullback has a relative remainder along every approach to the realization. -/
theorem oneActiveRawRemainder_isLittleO (r p q : ℕ) (hr : 2 ≤ r) (τ : ℝ) :
    oneActiveRawRemainder r p q τ =o[nhds 0] oneActiveRetained r p q := by
  let z := oneActiveRetained r p q
  have hpre : Tendsto (fun w : OneActiveAux p q => fun i => w.2.1 i^r) (nhds 0) (nhds 0) := by
    have hh : Continuous (fun w : OneActiveAux p q => fun i => w.2.1 i^r) := by fun_prop
    simpa [Pi.zero_def,show r ≠ 0 by omega] using hh.tendsto 0
  have hpost : Tendsto (fun w : OneActiveAux p q => fun i => w.2.2 i^r) (nhds 0) (nhds 0) := by
    have hh : Continuous (fun w : OneActiveAux p q => fun i => w.2.2 i^r) := by fun_prop
    simpa [Pi.zero_def,show r ≠ 0 by omega] using hh.tendsto 0
  have hp := inactiveAuxRemainder_isLittleO r p hr _ z hpre (fun w => by
    have h1 := norm_le_pi_norm (z w) 1
    have h2 := norm_le_pi_norm (z w) 2
    simpa [z,oneActiveRetained,two_mul] using add_le_add h1 h2)
  have hq := inactiveAuxRemainder_isLittleO r q hr _ z hpost (fun w => by
    have h1 := norm_le_pi_norm (z w) 3
    have h2 := norm_le_pi_norm (z w) 4
    simpa [z,oneActiveRetained,two_mul] using add_le_add h1 h2)
  have hd : HasDerivAt (fun h : ℝ => (τ+h)^r-τ^r) ((r:ℝ)*τ^(r-1)) 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).const_add τ).pow r).sub_const (τ^r)
  have ha : (fun h : ℝ => (τ+h)^r-τ^r-((r:ℝ)*τ^(r-1))*h) =o[nhds 0] (fun h => h) := by
    simpa [mul_comm] using hd.hasFDerivAt.isLittleO
  have hz : (fun w : OneActiveAux p q => w.1) =O[nhds 0] z :=
    (Asymptotics.isBigOWith_of_le' (c := 1) (nhds 0) (fun w => by
      simpa [z,oneActiveRetained] using norm_le_pi_norm (z w) 0)).isBigO
  have ha' := (ha.comp_tendsto (continuous_fst.tendsto (0:OneActiveAux p q))).trans_isBigO hz
  exact isLittleO_prod_left.mpr ⟨ha',isLittleO_prod_left.mpr ⟨hp,hq⟩⟩

/-- Local two-sided comparison for actual group composition at sufficiently many observations.
The raw active derivative is nonzero; inactive powers remain raw-weight functions. -/
theorem oneActiveRaw_observation_comparison {ι : Type*} [Fintype ι]
    (r p q : ℕ) (hr : 3 ≤ r) (τ : ℝ) (hτ : τ ≠ 0)
    (x : ι → ℝ) (hx : Function.Injective x)
    (hd : ∀ j, (oneActiveSignedDirections r (τ^r) j).natDegree < Fintype.card ι) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ w : OneActiveAux p q in nhds 0,
      c*‖oneActiveRetained r p q w‖ ≤
        ‖fun i => oneActiveAuxEval r (r^p+2) (r^q+2) (τ^r) (x i) (oneActiveRawAux r p q τ w)
          -oneActiveAuxEval r (r^p+2) (r^q+2) (τ^r) (x i) 0‖ ∧
      ‖fun i => oneActiveAuxEval r (r^p+2) (r^q+2) (τ^r) (x i) (oneActiveRawAux r p q τ w)
          -oneActiveAuxEval r (r^p+2) (r^q+2) (τ^r) (x i) 0‖ ≤
        C*‖oneActiveRetained r p q w‖ := by
  exact controlled_linearization_comparison _ _
    (oneActiveAuxEval_pi_hasFDerivAt r (r^p+2) (r^q+2) (τ^r) x)
    _ _ _ _ (oneActiveRawAux_tendsto r p q (by omega) τ)
    (oneActiveRawRemainder_isLittleO r p q (by omega) τ) (oneActiveRawAux_decomposition r p q τ)
    (signedRetainedInsert_deriv_injective r (r^p) (r^q) hr (τ^r) ((r:ℝ)*τ^(r-1))
      (pow_ne_zero _ hτ) (mul_ne_zero (by exact_mod_cast (by omega : r ≠ 0)) (pow_ne_zero _ hτ)) x hx hd)

end ResidualSLT
