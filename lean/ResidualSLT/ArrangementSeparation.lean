module
public import ResidualSLT.OneActiveDirections

/-! The complete algebraic separation step for arbitrary active count. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial

/-- A nonzero higher-degree column cannot be cancelled by lower-degree terms. -/
theorem high_degree_column_separation (Q H : ℝ[X]) (a : ℝ)
    (hdeg : Q.natDegree < H.natDegree) (hz : Q+C a*H=0) : Q=0 ∧ a=0 := by
  have hH : H ≠ 0 := by intro hh; simp [hh] at hdeg
  have hh := congrArg (fun P : ℝ[X] => P.coeff H.natDegree) hz
  rw [coeff_add,coeff_C_mul,coeff_eq_zero_of_natDegree_lt hdeg,coeff_natDegree,coeff_zero,zero_add] at hh
  have ha := (mul_eq_zero.mp hh).resolve_right (leadingCoeff_ne_zero.mpr hH)
  exact ⟨by simpa [ha] using hz,ha⟩

/-- Appending a nonzero active block multiplies the output degree exactly by r. -/
theorem append_active_natDegree (r : ℕ) (hr : 2 ≤ r) (H : ℝ[X])
    (hH : 0 < H.natDegree) (e : ℝ) (he : e ≠ 0) :
    (H+C e*H^r).natDegree = r*H.natDegree := by
  rw [natDegree_add_eq_right_of_natDegree_lt,natDegree_C_mul he,natDegree_pow,Nat.mul_comm]
  rw [natDegree_C_mul he,natDegree_pow]
  nlinarith

theorem append_factor_natDegree (r : ℕ) (hr : 2 ≤ r) (H : ℝ[X]) (e : ℝ) (he : e ≠ 0) :
    (1+C ((r:ℝ)*e)*H^(r-1)).natDegree = (r-1)*H.natDegree := by
  rw [natDegree_one_add,natDegree_C_mul (mul_ne_zero (by exact_mod_cast (by omega : r ≠ 0)) he),natDegree_pow,Nat.mul_comm]

/-- Signed case: the new active column and both new group columns separate from every
old polynomial of the induction degree bound. No assumption of generic active values. -/
theorem signed_arrangement_extension_separation (r : ℕ) (hr : 3 ≤ r)
    (H Q : ℝ[X]) (hH : 0 < H.natDegree) (e a s b : ℝ) (he : e ≠ 0)
    (hQ : Q.natDegree ≤ (2*r-1)*H.natDegree)
    (hz : (1+C ((r:ℝ)*e)*H^(r-1))*Q+C a*H^r+
      C s*(H+C e*H^r)^r+C b*(H+C e*H^r)^(2*r-1)=0) :
    Q=0 ∧ a=0 ∧ s=0 ∧ b=0 := by
  let P := 1+C ((r:ℝ)*e)*H^(r-1)
  let T := H+C e*H^r
  have hT : T.natDegree = r*H.natDegree := append_active_natDegree r (by omega) H hH e he
  have hP : P.natDegree = (r-1)*H.natDegree := append_factor_natDegree r (by omega) H e he
  have hlow : (P*Q+C a*H^r).natDegree ≤ (3*r-2)*H.natDegree := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · apply (natDegree_mul_le).trans
      rw [hP]
      have hh := Nat.add_le_add_left hQ ((r-1)*H.natDegree)
      have hidx : (r-1)+(2*r-1)=3*r-2 := by omega
      simpa only [← Nat.add_mul,hidx] using hh
    · apply (natDegree_C_mul_le _ _).trans
      rw [natDegree_pow]
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_right H.natDegree (by omega : r ≤ 3*r-2)
  have hg := two_direction_degree_gaps r H.natDegree hr hH
  have hsdeg : (T^r).natDegree = r^2*H.natDegree := by rw [natDegree_pow,hT]; ring
  have hbdeg : (T^(2*r-1)).natDegree = r*(2*r-1)*H.natDegree := by rw [natDegree_pow,hT]; ring
  have hsbound : (P*Q+C a*H^r+C s*T^r).natDegree ≤ r^2*H.natDegree := by
    apply (natDegree_add_le _ _).trans
    exact max_le (hlow.trans hg.1.le) ((natDegree_C_mul_le _ _).trans hsdeg.le)
  have hb0 := high_degree_column_separation (P*Q+C a*H^r+C s*T^r) (T^(2*r-1)) b
    (hsbound.trans_lt (hbdeg ▸ hg.2)) hz
  have hs0 := high_degree_column_separation (P*Q+C a*H^r) (T^r) s
    (hlow.trans_lt (hsdeg ▸ hg.1)) hb0.1
  have ha0 := active_factor_relation r (by omega) H Q e a he hH hs0.1
  exact ⟨ha0.1,ha0.2,hs0.2,hb0.2⟩

/-- Even case: only one group column is retained, and the separation includes r=2. -/
theorem even_arrangement_extension_separation (r : ℕ) (hr : 2 ≤ r)
    (H Q : ℝ[X]) (hH : 0 < H.natDegree) (e a s : ℝ) (he : e ≠ 0)
    (hQ : Q.natDegree ≤ r*H.natDegree)
    (hz : (1+C ((r:ℝ)*e)*H^(r-1))*Q+C a*H^r+C s*(H+C e*H^r)^r=0) :
    Q=0 ∧ a=0 ∧ s=0 := by
  let P := 1+C ((r:ℝ)*e)*H^(r-1)
  let T := H+C e*H^r
  have hT : T.natDegree = r*H.natDegree := append_active_natDegree r hr H hH e he
  have hP : P.natDegree = (r-1)*H.natDegree := append_factor_natDegree r hr H e he
  have hlow : (P*Q+C a*H^r).natDegree ≤ (2*r-1)*H.natDegree := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · apply (natDegree_mul_le).trans
      rw [hP]
      have hh := Nat.add_le_add_left hQ ((r-1)*H.natDegree)
      simpa only [← Nat.add_mul,show r-1+r=2*r-1 by omega] using hh
    · apply (natDegree_C_mul_le _ _).trans
      rw [natDegree_pow]
      nlinarith [Nat.mul_le_mul_right H.natDegree (by omega : r ≤ 2*r-1)]
  have hgap : (2*r-1)*H.natDegree < r^2*H.natDegree := by
    apply Nat.mul_lt_mul_of_pos_right _ hH
    nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ 2*r)]
  have hsdeg : (T^r).natDegree = r^2*H.natDegree := by rw [natDegree_pow,hT]; ring
  have hs0 := high_degree_column_separation (P*Q+C a*H^r) (T^r) s
    (hlow.trans_lt (hsdeg ▸ hgap)) hz
  have ha0 := active_factor_relation r hr H Q e a he hH hs0.1
  exact ⟨ha0.1,ha0.2,hs0.2⟩

end ResidualSLT
