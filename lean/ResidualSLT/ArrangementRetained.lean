module
public import ResidualSLT.ArrangementComposition
public import ResidualSLT.OneActiveRetainedMap

/-! Injective observed retained differential at every active count. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset ContinuousLinearMap

abbrev ArrangementSignedRetained (k : ℕ) :=
  (Fin k → ℝ) × (Fin (k+1) → ℝ) × (Fin (k+1) → ℝ)
abbrev ArrangementEvenRetained (k : ℕ) := (Fin k → ℝ) × (Fin (k+1) → ℝ)

@[expose] def arrangementSignedInsert (k : ℕ) (d : Fin (k+1) → ℕ) (κ : Fin k → ℝ) :
    ArrangementSignedRetained k →L[ℝ] ArrangementAux k (fun g => d g+2) :=
  ({ toFun := fun z => (fun j => κ j*z.1 j,
        fun g : Fin (k+1) => Pi.single (⟨0,by omega⟩ : Fin (d g+2)) (z.2.1 g)+Pi.single (⟨1,by omega⟩ : Fin (d g+2)) (z.2.2 g))
     map_add' := by
       intro x y
       ext i j <;> simp [Pi.single_apply,mul_add]; split_ifs <;> ring
     map_smul' := by
       intro t z
       ext i j <;> simp [Pi.single_apply] <;> (try split_ifs) <;> ring
   } : ArrangementSignedRetained k →ₗ[ℝ] ArrangementAux k (fun g => d g+2)).toContinuousLinearMap

@[expose] def arrangementEvenInsert (k : ℕ) (d : Fin (k+1) → ℕ) (κ : Fin k → ℝ) :
    ArrangementEvenRetained k →L[ℝ] ArrangementAux k (fun g => d g+2) :=
  ({ toFun := fun z => (fun j => κ j*z.1 j,fun g : Fin (k+1) => Pi.single (⟨0,by omega⟩ : Fin (d g+2)) (z.2 g))
     map_add' := by
       intro x y
       ext i j <;> simp [Pi.single_apply,mul_add]; split_ifs <;> ring
     map_smul' := by
       intro t z
       ext i j <;> simp [Pi.single_apply]; ring
   } : ArrangementEvenRetained k →ₗ[ℝ] ArrangementAux k (fun g => d g+2)).toContinuousLinearMap

theorem arrangementActiveL_signedInsert (k : ℕ) (d : Fin (k+1) → ℕ) (κ : Fin k → ℝ)
    (j : ℕ) (z : ArrangementSignedRetained k) :
    arrangementActiveL k (fun g => d g+2) j (arrangementSignedInsert k d κ z) = zeroExtend (fun i => κ i*z.1 i) j := by
  unfold arrangementActiveL zeroExtend
  split_ifs <;> simp [arrangementSignedInsert]

theorem arrangementGroupL_signedInsert (r k : ℕ) (hr : 2 ≤ r) (d : Fin (k+1) → ℕ)
    (κ : Fin k → ℝ) (g : ℕ) (x : ℝ) (z : ArrangementSignedRetained k) :
    arrangementGroupL r k (fun g => d g+2) g x (arrangementSignedInsert k d κ z) =
      zeroExtend z.2.1 g*x^r+zeroExtend z.2.2 g*x^(2*r-1) := by
  unfold arrangementGroupL zeroExtend
  split_ifs <;> simp [arrangementSignedInsert,gradedEvalL_single,show r+(r-1)=2*r-1 by omega]

theorem arrangementActiveL_evenInsert (k : ℕ) (d : Fin (k+1) → ℕ) (κ : Fin k → ℝ)
    (j : ℕ) (z : ArrangementEvenRetained k) :
    arrangementActiveL k (fun g => d g+2) j (arrangementEvenInsert k d κ z) = zeroExtend (fun i => κ i*z.1 i) j := by
  unfold arrangementActiveL zeroExtend
  split_ifs <;> simp [arrangementEvenInsert]

theorem arrangementGroupL_evenInsert (r k : ℕ) (d : Fin (k+1) → ℕ)
    (κ : Fin k → ℝ) (g : ℕ) (x : ℝ) (z : ArrangementEvenRetained k) :
    arrangementGroupL r k (fun g => d g+2) g x (arrangementEvenInsert k d κ z) =
      zeroExtend z.2 g*x^r := by
  unfold arrangementGroupL zeroExtend
  split_ifs <;> simp [arrangementEvenInsert,gradedEvalL_single]

/-- The exact auxiliary differential restricts to the signed polynomial jet. -/
theorem arrangementAuxDeriv_signedInsert (r k : ℕ) (hr : 2 ≤ r) (d : Fin (k+1) → ℕ)
    (c : ℕ → ℝ) (κ : Fin k → ℝ) (x : ℝ) (n : ℕ) (z : ArrangementSignedRetained k) :
    arrangementAuxDeriv r k (fun g => d g+2) c x n (arrangementSignedInsert k d κ z) =
      (arrangementSignedJet r c (zeroExtend (fun i => κ i*z.1 i)) (zeroExtend z.2.1) (zeroExtend z.2.2) n).eval x := by
  induction n with
  | zero => simpa [arrangementAuxDeriv,arrangementSignedJet] using arrangementGroupL_signedInsert r k hr d κ 0 x z
  | succ n ih =>
    simp [arrangementAuxDeriv,arrangementSignedJet,ih,arrangementActiveL_signedInsert,
      arrangementGroupL_signedInsert r k hr]
    ring

theorem arrangementAuxDeriv_evenInsert (r k : ℕ) (d : Fin (k+1) → ℕ)
    (c : ℕ → ℝ) (κ : Fin k → ℝ) (x : ℝ) (n : ℕ) (z : ArrangementEvenRetained k) :
    arrangementAuxDeriv r k (fun g => d g+2) c x n (arrangementEvenInsert k d κ z) =
      (arrangementEvenJet r c (zeroExtend (fun i => κ i*z.1 i)) (zeroExtend z.2) n).eval x := by
  induction n with
  | zero => simpa [arrangementAuxDeriv,arrangementEvenJet] using arrangementGroupL_evenInsert r k d κ 0 x z
  | succ n ih =>
    simp [arrangementAuxDeriv,arrangementEvenJet,ih,arrangementActiveL_evenInsert,arrangementGroupL_evenInsert]
    ring

theorem arrangementSignedInsert_deriv_injective {ι : Type*} [Fintype ι]
    (r k : ℕ) (hr : 3 ≤ r) (d : Fin (k+1) → ℕ) (c : ℕ → ℝ) (hc : ∀ j<k,c j ≠ 0)
    (κ : Fin k → ℝ) (hκ : ∀ j, κ j ≠ 0) (x : ι → ℝ) (hx : Function.Injective x)
    (hM : (2*r-1)*r^k < Fintype.card ι) :
    Function.Injective ((ContinuousLinearMap.pi
      (fun i => arrangementAuxDeriv r k (fun g => d g+2) c (x i) k)).comp (arrangementSignedInsert k d κ)) := by
  let T := (ContinuousLinearMap.pi
    (fun i => arrangementAuxDeriv r k (fun g => d g+2) c (x i) k)).comp (arrangementSignedInsert k d κ)
  have hker : ∀ z, T z=0 → z=0 := by
    intro z hz
    let P := arrangementSignedJet r c (zeroExtend (fun i => κ i*z.1 i)) (zeroExtend z.2.1) (zeroExtend z.2.2) k
    have hP : P=0 := by
      apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hx
      · intro i
        have hh := congrFun hz i
        change arrangementAuxDeriv r k (fun g => d g+2) c (x i) k (arrangementSignedInsert k d κ z)=0 at hh
        rwa [arrangementAuxDeriv_signedInsert r k (by omega)] at hh
      · exact ((arrangementSignedJet_degree r hr c _ _ _ k hc).trans
          (Nat.mul_le_mul_left _ (network_natDegree_le r (by omega) c k))).trans_lt hM
    obtain ⟨ha,hs,hb⟩ := arrangementSignedJet_kernel r hr c _ _ _ k hc hP
    apply Prod.ext
    · funext j
      have hh := ha j.val j.isLt
      simp only [zeroExtend,dite_eq_left j.isLt,Fin.eta] at hh
      exact (mul_eq_zero.mp hh).resolve_left (hκ j)
    · apply Prod.ext
      · funext j
        simpa [zeroExtend,j.isLt] using hs j.val (by omega)
      · funext j
        simpa [zeroExtend,j.isLt] using hb j.val (by omega)
  intro u v huv
  have hh : T (u-v)=0 := by rw [map_sub,huv,sub_self]
  exact sub_eq_zero.mp (hker _ hh)

theorem arrangementEvenInsert_deriv_injective {ι : Type*} [Fintype ι]
    (r k : ℕ) (hr : 2 ≤ r) (d : Fin (k+1) → ℕ) (c : ℕ → ℝ) (hc : ∀ j<k,c j ≠ 0)
    (κ : Fin k → ℝ) (hκ : ∀ j, κ j ≠ 0) (x : ι → ℝ) (hx : Function.Injective x)
    (hM : r*r^k < Fintype.card ι) :
    Function.Injective ((ContinuousLinearMap.pi
      (fun i => arrangementAuxDeriv r k (fun g => d g+2) c (x i) k)).comp (arrangementEvenInsert k d κ)) := by
  let T := (ContinuousLinearMap.pi
    (fun i => arrangementAuxDeriv r k (fun g => d g+2) c (x i) k)).comp (arrangementEvenInsert k d κ)
  have hker : ∀ z, T z=0 → z=0 := by
    intro z hz
    let P := arrangementEvenJet r c (zeroExtend (fun i => κ i*z.1 i)) (zeroExtend z.2) k
    have hP : P=0 := by
      apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hx
      · intro i
        have hh := congrFun hz i
        change arrangementAuxDeriv r k (fun g => d g+2) c (x i) k (arrangementEvenInsert k d κ z)=0 at hh
        rwa [arrangementAuxDeriv_evenInsert] at hh
      · exact ((arrangementEvenJet_degree r hr c _ _ k hc).trans
          (Nat.mul_le_mul_left _ (network_natDegree_le r hr c k))).trans_lt hM
    obtain ⟨ha,hs⟩ := arrangementEvenJet_kernel r hr c _ _ k hc hP
    apply Prod.ext
    · funext j
      have hh := ha j.val j.isLt
      simp only [zeroExtend,dite_eq_left j.isLt,Fin.eta] at hh
      exact (mul_eq_zero.mp hh).resolve_left (hκ j)
    · funext j
      simpa [zeroExtend,j.isLt] using hs j.val (by omega)
  intro u v huv
  have hh : T (u-v)=0 := by rw [map_sub,huv,sub_self]
  exact sub_eq_zero.mp (hker _ hh)

end ResidualSLT
