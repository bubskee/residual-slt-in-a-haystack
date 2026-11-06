module
public import ResidualSLT.ArrangementSeparation
public import ResidualSLT.Degree

/-! Full retained polynomial jets at arbitrary active count, including both end groups. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial

@[expose] def arrangementSignedJet (r : ℕ) (c a s b : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => C (s 0)*X^r+C (b 0)*X^(2*r-1)
  | k+1 =>
    (1+C ((r:ℝ)*c k)*(network r c k)^(r-1))*arrangementSignedJet r c a s b k +
      C (a k)*(network r c k)^r + C (s (k+1))*(network r c (k+1))^r +
      C (b (k+1))*(network r c (k+1))^(2*r-1)

@[expose] def arrangementEvenJet (r : ℕ) (c a s : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => C (s 0)*X^r
  | k+1 =>
    (1+C ((r:ℝ)*c k)*(network r c k)^(r-1))*arrangementEvenJet r c a s k +
      C (a k)*(network r c k)^r + C (s (k+1))*(network r c (k+1))^r

theorem network_natDegree_pos (r : ℕ) (hr : 2 ≤ r) (c : ℕ → ℝ) (k : ℕ) :
    0 < (network r c k).natDegree := by
  rw [network_natDegree r hr]
  exact pow_pos (by omega) _

theorem arrangementSignedJet_degree (r : ℕ) (hr : 3 ≤ r) (c a s b : ℕ → ℝ) (k : ℕ)
    (hc : ∀ i < k, c i ≠ 0) :
    (arrangementSignedJet r c a s b k).natDegree ≤ (2*r-1)*(network r c k).natDegree := by
  induction k with
  | zero =>
    simp only [arrangementSignedJet,network,natDegree_X,mul_one]
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; omega)
    · exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow])
  | succ k ih =>
    have ih' := ih (fun i hi => hc i (by omega))
    let D := (network r c k).natDegree
    have hD : 0 < D := network_natDegree_pos r (by omega) c k
    have ht : (network r c (k+1)).natDegree = r*D :=
      append_active_natDegree r (by omega) _ hD (c k) (hc k (by omega))
    have hp := append_factor_natDegree r (by omega) (network r c k) (c k) (hc k (by omega))
    have hg := two_direction_degree_gaps r D hr hD
    have hlow : ((1+C ((r:ℝ)*c k)*(network r c k)^(r-1))*arrangementSignedJet r c a s b k).natDegree ≤
        (3*r-2)*D := by
      apply (natDegree_mul_le).trans
      rw [hp]
      have hh := Nat.add_le_add_left ih' ((r-1)*D)
      simpa only [D,← Nat.add_mul,show r-1+(2*r-1)=3*r-2 by omega] using hh
    simp only [arrangementSignedJet,ht]
    apply (natDegree_add_le _ _).trans
    apply max_le
    · apply (natDegree_add_le _ _).trans
      apply max_le
      · apply (natDegree_add_le _ _).trans
        apply max_le
        · nlinarith [hlow,hg.1,hg.2]
        · apply (natDegree_C_mul_le _ _).trans
          rw [natDegree_pow]
          dsimp [D] at *
          nlinarith [Nat.mul_le_mul_left (r*(network r c k).natDegree) (by omega : 1 ≤ 2*r-1)]
      · apply (natDegree_C_mul_le _ _).trans
        rw [natDegree_pow,ht]
        nlinarith [hg.2]
    · apply (natDegree_C_mul_le _ _).trans
      rw [natDegree_pow,ht]

theorem arrangementEvenJet_degree (r : ℕ) (hr : 2 ≤ r) (c a s : ℕ → ℝ) (k : ℕ)
    (hc : ∀ i < k, c i ≠ 0) :
    (arrangementEvenJet r c a s k).natDegree ≤ r*(network r c k).natDegree := by
  induction k with
  | zero =>
    simp only [arrangementEvenJet,network,natDegree_X,mul_one]
    exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow])
  | succ k ih =>
    have ih' := ih (fun i hi => hc i (by omega))
    let D := (network r c k).natDegree
    have hD : 0 < D := network_natDegree_pos r hr c k
    have ht : (network r c (k+1)).natDegree = r*D :=
      append_active_natDegree r hr _ hD (c k) (hc k (by omega))
    have hp := append_factor_natDegree r hr (network r c k) (c k) (hc k (by omega))
    simp only [arrangementEvenJet,ht]
    apply (natDegree_add_le _ _).trans
    apply max_le
    · apply (natDegree_add_le _ _).trans
      apply max_le
      · apply (natDegree_mul_le).trans
        rw [hp]
        have hh := Nat.add_le_add_left ih' ((r-1)*D)
        have hidx : r-1+r=2*r-1 := by omega
        have hgap : 2*r-1 ≤ r*r := by nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ 2*r)]
        have hh' : (r-1)*D+r*D ≤ r*(r*D) := by
          rw [← Nat.add_mul,hidx,← Nat.mul_assoc]
          exact Nat.mul_le_mul_right D hgap
        exact hh.trans hh'
      · apply (natDegree_C_mul_le _ _).trans
        rw [natDegree_pow]
        dsimp [D]
        nlinarith [Nat.mul_le_mul_left (r*(network r c k).natDegree) (by omega : 1 ≤ r)]
    · apply (natDegree_C_mul_le _ _).trans
      rw [natDegree_pow,ht]

/-- All signed retained coefficients vanish if their full jet vanishes, at every active count. -/
theorem arrangementSignedJet_kernel (r : ℕ) (hr : 3 ≤ r) (c a s b : ℕ → ℝ) (k : ℕ)
    (hc : ∀ i < k, c i ≠ 0) (hz : arrangementSignedJet r c a s b k=0) :
    (∀ i < k, a i=0) ∧ (∀ i ≤ k, s i=0) ∧ (∀ i ≤ k, b i=0) := by
  induction k with
  | zero =>
    have h0 := high_degree_column_separation (C (s 0)*X^r) (X^(2*r-1)) (b 0)
      (by apply (natDegree_C_mul_le _ _).trans_lt; simp only [natDegree_X_pow]; omega) hz
    have hs : s 0=0 := by simpa using h0.1
    exact ⟨by simp,by simpa using hs,by simpa using h0.2⟩
  | succ k ih =>
    have hc' : ∀ i < k, c i ≠ 0 := fun i hi => hc i (by omega)
    have hh := signed_arrangement_extension_separation r hr (network r c k)
      (arrangementSignedJet r c a s b k) (network_natDegree_pos r (by omega) c k)
      (c k) (a k) (s (k+1)) (b (k+1)) (hc k (by omega))
      (arrangementSignedJet_degree r hr c a s b k hc') hz
    obtain ⟨ha,hs,hb⟩ := ih hc' hh.1
    refine ⟨?_,?_,?_⟩
    · intro i hi
      by_cases he : i=k
      · simpa [he] using hh.2.1
      · exact ha i (by omega)
    · intro i hi
      by_cases he : i=k+1
      · simpa [he] using hh.2.2.1
      · exact hs i (by omega)
    · intro i hi
      by_cases he : i=k+1
      · simpa [he] using hh.2.2.2
      · exact hb i (by omega)

/-- The separate three-direction induction, including quadratic degree. -/
theorem arrangementEvenJet_kernel (r : ℕ) (hr : 2 ≤ r) (c a s : ℕ → ℝ) (k : ℕ)
    (hc : ∀ i < k, c i ≠ 0) (hz : arrangementEvenJet r c a s k=0) :
    (∀ i < k, a i=0) ∧ (∀ i ≤ k, s i=0) := by
  induction k with
  | zero =>
    have hs : s 0=0 := by simpa [arrangementEvenJet] using hz
    exact ⟨by simp,by simpa using hs⟩
  | succ k ih =>
    have hc' : ∀ i < k, c i ≠ 0 := fun i hi => hc i (by omega)
    have hh := even_arrangement_extension_separation r hr (network r c k)
      (arrangementEvenJet r c a s k) (network_natDegree_pos r hr c k)
      (c k) (a k) (s (k+1)) (hc k (by omega)) (arrangementEvenJet_degree r hr c a s k hc') hz
    obtain ⟨ha,hs⟩ := ih hc' hh.1
    refine ⟨?_,?_⟩
    · intro i hi
      by_cases he : i=k
      · simpa [he] using hh.2.1
      · exact ha i (by omega)
    · intro i hi
      by_cases he : i=k+1
      · simpa [he] using hh.2.2
      · exact hs i (by omega)

end ResidualSLT
