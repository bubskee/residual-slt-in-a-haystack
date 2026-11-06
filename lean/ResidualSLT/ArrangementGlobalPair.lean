module
public import ResidualSLT.ArrangementCertificate

/-! The dominant pair among all placements of a fixed ordered active chain. -/
public section
noncomputable section
namespace ResidualSLT
open Finset

@[expose] def globalLearningPair (r k n : ℕ) : ℝ × ℕ :=
  ((k:ℝ)/2+(identityLearningPair r n).1,(identityLearningPair r n).2)

theorem sum_nat_sub_le {ι : Type*} (s : Finset ι) (n : ι → ℕ) (r : ℕ) :
    (∑ i ∈ s,(n i-r)) ≤ (∑ i ∈ s,n i)-r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [sum_insert hi]
    omega

/-- Equality in the supercritical deficit bound forces all inactive blocks into one gap. -/
theorem sum_nat_sub_saturation {ι : Type*} (s : Finset ι) (n : ι → ℕ) (r : ℕ)
    (hr : 0 < r) (hgt : r < ∑ i ∈ s,n i)
    (he : (∑ i ∈ s,(n i-r)) = (∑ i ∈ s,n i)-r) :
    ∃ i∈s, r<n i ∧ ∀ j∈s, j ≠ i → n j=0 := by
  classical
  obtain ⟨i,hi,hn⟩ := exists_ne_zero_of_sum_ne_zero (s := s) (f := fun i => n i-r) (show (∑ i ∈ s,(n i-r)) ≠ 0 by omega)
  have hni : r<n i := by omega
  have hsum := sum_erase_add s n hi
  have hsub := sum_erase_add s (fun j => n j-r) hi
  have hle := sum_nat_sub_le (s.erase i) n r
  have hz : ∑ j ∈ s.erase i,n j=0 := by omega
  refine ⟨i,hi,hni,?_⟩
  intro j hj hji
  have hh : n j ≤ ∑ a ∈ s.erase i,n a := single_le_sum (fun _ _ => Nat.zero_le _) (mem_erase.mpr ⟨hji,hj⟩)
  omega

theorem identityLearningPair_odd_deficit (r n : ℕ) (hr : 0 < r) (hodd : Odd r) :
    (identityLearningPair r n).1 = (n:ℝ)/(2*r)-((n-r:ℕ):ℝ)/(4*r) := by
  have hr0 : (r:ℝ) ≠ 0 := by positivity
  by_cases hl : n<r
  · simp [identityLearningPair,Nat.not_even_iff_odd.mpr hodd,hl,Nat.sub_eq_zero_of_le hl.le]
  by_cases he : n=r
  · subst n
    simp only [identityLearningPair_odd_eq r hodd,Nat.sub_self,Nat.cast_zero,zero_div,sub_zero]
    field_simp
  · have hge : r ≤ n := by omega
    simp only [identityLearningPair,Nat.not_even_iff_odd.mpr hodd,ite_false,hl,he,Nat.cast_sub hge]
    field_simp
    ring

theorem identityLearningPair_empty (r : ℕ) (hr : 0 < r) : identityLearningPair r 0 = (0,1) := by
  by_cases he : Even r <;> simp [identityLearningPair,he,hr]

theorem arrangement_global_exponent_le (r k : ℕ) (hr : 2 ≤ r) (n : Fin (k+1) → ℕ) :
    (globalLearningPair r k (∑ g,n g)).1 ≤ (arrangementLearningPair r k n).1 := by
  rcases Nat.even_or_odd r with he | ho
  · simp [globalLearningPair,arrangementLearningPair_even r k n he,identityLearningPair_even r _ he,Nat.cast_sum]
  · have hd := sum_nat_sub_le univ n r
    have hd' : ((∑ g,(n g-r) : ℕ):ℝ) ≤ ((∑ g,n g)-r : ℕ) := by exact_mod_cast hd
    simp only [globalLearningPair,arrangementLearningPair,identityLearningPair_odd_deficit r _ (by omega) ho,
      sum_sub_distrib,← sum_div,Nat.cast_sum]
    have hr0 : (0:ℝ) < 4*r := by positivity
    have hh := div_le_div_of_nonneg_right hd' hr0.le
    push_cast at hh
    linarith

theorem arrangement_global_multiplicity_le_of_exponent_eq (r k : ℕ) (hr : 2 ≤ r)
    (n : Fin (k+1) → ℕ)
    (heq : (arrangementLearningPair r k n).1 = (globalLearningPair r k (∑ g,n g)).1) :
    (arrangementLearningPair r k n).2 ≤ (globalLearningPair r k (∑ g,n g)).2 := by
  classical
  rcases Nat.even_or_odd r with he | ho
  · simp [arrangementLearningPair_even r k n he,globalLearningPair,identityLearningPair_even r _ he]
  rw [arrangementLearningPair_odd_multiplicity r k n ho]
  by_cases hl : (∑ g,n g)<r
  · have hz : (univ.filter (fun g => n g=r)).card=0 := by
      apply card_eq_zero.mpr
      apply filter_eq_empty_iff.mpr
      intro g _ he
      have hh : n g ≤ ∑ a,n a := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ g)
      omega
    simp [globalLearningPair,identityLearningPair_odd_lt r _ ho hl,hz]
  by_cases ht : (∑ g,n g)=r
  · have hc : (univ.filter (fun g => n g=r)).card ≤ 1 := by
      apply card_le_one.mpr
      intro i hi j hj
      by_contra hij
      have hh : ∑ a ∈ ({i,j} : Finset (Fin (k+1))),n a ≤ ∑ a,n a := sum_le_sum_of_subset (by simp)
      simp only [sum_pair hij,(mem_filter.mp hi).2,(mem_filter.mp hj).2] at hh
      omega
    simpa [globalLearningPair,ht,identityLearningPair_odd_eq r ho] using Nat.add_le_add_left hc 1
  · have hgt : r < ∑ g,n g := by omega
    have he : (∑ g,(n g-r)) = (∑ g,n g)-r := by
      simp only [globalLearningPair,arrangementLearningPair,
        identityLearningPair_odd_deficit r _ (by omega) ho,sum_sub_distrib,← sum_div,← Nat.cast_sum] at heq
      have hr0 : (r:ℝ) ≠ 0 := by positivity
      have hh : ((∑ g,(n g-r) : ℕ):ℝ) = ((∑ g,n g)-r : ℕ) := by
        field_simp at heq
        nlinarith
      exact_mod_cast hh
    obtain ⟨i,_,hi,hz⟩ := sum_nat_sub_saturation univ n r (by omega) hgt he
    have hc : (univ.filter (fun g => n g=r)).card=0 := by
      apply card_eq_zero.mpr
      apply filter_eq_empty_iff.mpr
      intro g _ hg
      by_cases hgi : g=i
      · subst g; omega
      · have hh := hz g (mem_univ _) hgi; omega
    simp [globalLearningPair,identityLearningPair_odd_gt r _ ho hgt,hc]

@[expose] def concentratedGroups (k n : ℕ) : Fin (k+1) → ℕ := Pi.single 0 n

theorem concentratedGroups_sum (k n : ℕ) : (∑ g,concentratedGroups k n g)=n := by
  simp [concentratedGroups]

theorem arrangementLearningPair_concentrated (r k n : ℕ) (hr : 2 ≤ r) :
    arrangementLearningPair r k (concentratedGroups k n) = globalLearningPair r k n := by
  classical
  have he := identityLearningPair_empty r (by omega)
  have ha : (∑ g,(identityLearningPair r (concentratedGroups k n g)).1) = (identityLearningPair r n).1 := by
    rw [sum_eq_single 0]
    · simp [concentratedGroups]
    · intro g _ hg; simp [concentratedGroups,hg,he]
    · simp
  have hm : (∑ g,((identityLearningPair r (concentratedGroups k n g)).2-1)) = (identityLearningPair r n).2-1 := by
    rw [sum_eq_single 0]
    · simp [concentratedGroups]
    · intro g _ hg; simp [concentratedGroups,hg,he]
    · simp
  have hp : 0 < (identityLearningPair r n).2 := by
    unfold identityLearningPair
    split_ifs <;> norm_num
  simp only [arrangementLearningPair,globalLearningPair,ha,hm]
  congr 1
  omega

end ResidualSLT
