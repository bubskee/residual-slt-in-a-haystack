module
public import ResidualSLT.ArrangementRetained
public import ResidualSLT.OneActiveEvenLinearization

/-! Uniform relative remainder in all raw directions, for arbitrary finite arrangements. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset Filter Asymptotics

@[expose] def arrangementRawAux (r k : ℕ) (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ)
    (w : ArrangementAux k n) : ArrangementAux k (fun g => r^(n g)+2) :=
  (fun j => (τ j+w.1 j)^r-(τ j)^r,
    fun g => inactiveAuxVector r (n g) (fun i => w.2 g i^r))

@[expose] def arrangementSignedRetained (r k : ℕ) (n : Fin (k+1) → ℕ)
    (w : ArrangementAux k n) : ArrangementSignedRetained k :=
  (w.1,fun g => ∑ i, w.2 g i^r,
    fun g => (graded r (zeroExtend (fun i => w.2 g i^r)) (n g)).coeff 2)

@[expose] def arrangementEvenRetained (r k : ℕ) (n : Fin (k+1) → ℕ)
    (w : ArrangementAux k n) : ArrangementEvenRetained k := (w.1,fun g => ∑ i, w.2 g i^r)

@[expose] def arrangementSignedRemainder (r k : ℕ) (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ)
    (w : ArrangementAux k n) : ArrangementAux k (fun g => r^(n g)+2) :=
  (fun j => (τ j+w.1 j)^r-(τ j)^r-((r:ℝ)*(τ j)^(r-1))*w.1 j,
    fun g => inactiveAuxRemainder r (n g) (fun i => w.2 g i^r))

@[expose] def arrangementEvenRemainder (r k : ℕ) (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ)
    (w : ArrangementAux k n) : ArrangementAux k (fun g => r^(n g)+2) :=
  (fun j => (τ j+w.1 j)^r-(τ j)^r-((r:ℝ)*(τ j)^(r-1))*w.1 j,
    fun g => inactiveEvenRemainder r (n g) (fun i => w.2 g i^r))

theorem arrangementRawAux_signed_decomposition (r k : ℕ) (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ)
    (w : ArrangementAux k n) :
    arrangementRawAux r k n τ w =
      arrangementSignedInsert k (fun g => r^(n g)) (fun j => (r:ℝ)*(τ j)^(r-1))
        (arrangementSignedRetained r k n w)+arrangementSignedRemainder r k n τ w := by
  apply Prod.ext
  · funext j
    simp [arrangementRawAux,arrangementSignedInsert,arrangementSignedRetained,arrangementSignedRemainder]
  · funext g
    simpa [arrangementRawAux,arrangementSignedInsert,arrangementSignedRetained,arrangementSignedRemainder] using
      inactiveAuxVector_split r (n g) (fun i => w.2 g i^r)

theorem arrangementRawAux_even_decomposition (r k : ℕ) (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ)
    (w : ArrangementAux k n) :
    arrangementRawAux r k n τ w =
      arrangementEvenInsert k (fun g => r^(n g)) (fun j => (r:ℝ)*(τ j)^(r-1))
        (arrangementEvenRetained r k n w)+arrangementEvenRemainder r k n τ w := by
  apply Prod.ext
  · funext j
    simp [arrangementRawAux,arrangementEvenInsert,arrangementEvenRetained,arrangementEvenRemainder]
  · funext g
    simpa [arrangementRawAux,arrangementEvenInsert,arrangementEvenRetained,arrangementEvenRemainder] using
      inactiveEvenRemainder_split r (n g) (fun i => w.2 g i^r)

theorem arrangementRawAux_tendsto (r k : ℕ) (hr : 2 ≤ r) (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ) :
    Tendsto (arrangementRawAux r k n τ) (nhds 0) (nhds 0) := by
  have hg : Continuous (fun w : ArrangementAux k n => fun g => inactiveAuxVector r (n g) (fun i => w.2 g i^r)) := by
    apply continuous_pi_iff.mpr
    intro g
    exact (inactiveAuxVector_continuous r (n g) hr).comp (by fun_prop)
  have hh : Continuous (arrangementRawAux r k n τ) := by
    unfold arrangementRawAux
    exact (by fun_prop : Continuous (fun w : ArrangementAux k n => fun j => (τ j+w.1 j)^r-(τ j)^r)).prodMk hg
  have hz (m : ℕ) : inactiveAuxVector r m (fun _ => 0) = fun _ => 0 := by
    simpa only [Pi.zero_def] using inactiveAuxVector_zero r m
  simpa [arrangementRawAux,Pi.zero_def,Prod.zero_eq_mk,show r ≠ 0 by omega,hz] using hh.tendsto 0

/-- The regular raw-weight Taylor error is little-o of any retained vector controlling that weight. -/
theorem active_power_remainder_isLittleO {α V : Type*} [NormedAddCommGroup V] {l : Filter α}
    (r : ℕ) (τ : ℝ) (h : α → ℝ) (z : α → V)
    (hh : Tendsto h l (nhds 0)) (hz : ∀ x, ‖h x‖ ≤ ‖z x‖) :
    (fun x => (τ+h x)^r-τ^r-((r:ℝ)*τ^(r-1))*h x) =o[l] z := by
  have hd : HasDerivAt (fun t : ℝ => (τ+t)^r-τ^r) ((r:ℝ)*τ^(r-1)) 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).const_add τ).pow r).sub_const (τ^r)
  have ha : (fun t : ℝ => (τ+t)^r-τ^r-((r:ℝ)*τ^(r-1))*t) =o[nhds 0] (fun t => t) := by
    simpa [mul_comm] using hd.hasFDerivAt.isLittleO
  exact (ha.comp_tendsto hh).trans_isBigO ((isBigOWith_of_le' (c := 1) l (fun x => by simpa using hz x)).isBigO)

theorem arrangementSignedRemainder_isLittleO (r k : ℕ) (hr : 2 ≤ r)
    (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ) :
    arrangementSignedRemainder r k n τ =o[nhds 0] arrangementSignedRetained r k n := by
  apply isLittleO_prod_left.mpr
  constructor
  · apply isLittleO_pi.mpr
    intro j
    exact active_power_remainder_isLittleO r (τ j) (fun w : ArrangementAux k n => w.1 j) _
      (by simpa [Function.comp_def] using ((continuous_apply j).comp continuous_fst).tendsto (0 : ArrangementAux k n))
      (fun w => (norm_le_pi_norm w.1 j).trans (norm_fst_le (arrangementSignedRetained r k n w)))
  · apply isLittleO_pi.mpr
    intro g
    have hu : Tendsto (fun w : ArrangementAux k n => fun i => w.2 g i^r) (nhds 0) (nhds 0) := by
      have hh : Continuous (fun w : ArrangementAux k n => fun i => w.2 g i^r) := by fun_prop
      simpa [Pi.zero_def,show r ≠ 0 by omega] using hh.tendsto 0
    apply inactiveAuxRemainder_isLittleO r (n g) hr _ _ hu
    intro w
    have hs := (norm_le_pi_norm (arrangementSignedRetained r k n w).2.1 g).trans
      ((norm_fst_le (arrangementSignedRetained r k n w).2).trans (norm_snd_le _))
    have hb := (norm_le_pi_norm (arrangementSignedRetained r k n w).2.2 g).trans
      ((norm_snd_le (arrangementSignedRetained r k n w).2).trans (norm_snd_le _))
    simpa [arrangementSignedRetained,two_mul] using add_le_add hs hb

theorem arrangementEvenRemainder_isLittleO (r k : ℕ) (hr : 2 ≤ r) (heven : Even r)
    (n : Fin (k+1) → ℕ) (τ : Fin k → ℝ) :
    arrangementEvenRemainder r k n τ =o[nhds 0] arrangementEvenRetained r k n := by
  apply isLittleO_prod_left.mpr
  constructor
  · apply isLittleO_pi.mpr
    intro j
    exact active_power_remainder_isLittleO r (τ j) (fun w : ArrangementAux k n => w.1 j) _
      (by simpa [Function.comp_def] using ((continuous_apply j).comp continuous_fst).tendsto (0 : ArrangementAux k n))
      (fun w => (norm_le_pi_norm w.1 j).trans (norm_fst_le (arrangementEvenRetained r k n w)))
  · apply isLittleO_pi.mpr
    intro g
    have hu : Tendsto (fun w : ArrangementAux k n => fun i => w.2 g i^r) (nhds 0) (nhds 0) := by
      have hh : Continuous (fun w : ArrangementAux k n => fun i => w.2 g i^r) := by fun_prop
      simpa [Pi.zero_def,show r ≠ 0 by omega] using hh.tendsto 0
    apply inactiveEvenRemainder_isLittleO r (n g) hr _ _ hu (fun _ i => heven.pow_nonneg _)
    intro w
    exact (le_abs_self _).trans ((norm_le_pi_norm (arrangementEvenRetained r k n w).2 g).trans (norm_snd_le _))

end ResidualSLT
