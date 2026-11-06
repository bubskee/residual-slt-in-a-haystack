module
public import ResidualSLT.ActiveChainRecovery

/-! Complete arbitrary-depth fibers: delete zero coefficients, retaining chronological order.
Words below are stored in reverse chronological order to match the network recursion. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset

@[expose] def activeWord (u : ℕ → ℝ) : ℕ → List ℝ
  | 0 => []
  | n+1 => if u n=0 then activeWord u n else u n :: activeWord u n

@[expose] def wordPolynomial (r : ℕ) : List ℝ → ℝ[X]
  | [] => X
  | c::l => wordPolynomial r l+C c*(wordPolynomial r l)^r

theorem power_coeff_one_zero (H : ℝ[X]) (h0 : H.coeff 0=0) (r : ℕ) (hr : 2≤r) :
    (H^r).coeff 1=0 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hr
  simp [pow_add,pow_two,mul_coeff_one,h0]

theorem wordPolynomial_normalized (r : ℕ) (hr : 2≤r) (l : List ℝ) :
    (wordPolynomial r l).coeff 0=0 ∧ (wordPolynomial r l).coeff 1=1 := by
  induction l with
  | nil => simp [wordPolynomial]
  | cons c l ih =>
    have hz : ((wordPolynomial r l)^r).coeff 0=0 := by
      rw [coeff_zero_eq_eval_zero,eval_pow,← coeff_zero_eq_eval_zero,ih.1,zero_pow (by omega : r≠0)]
    simp [wordPolynomial,ih.1,ih.2,power_coeff_one_zero _ ih.1 r hr,hz]

theorem wordPolynomial_natDegree (r : ℕ) (hr : 2≤r) (l : List ℝ)
    (hl : ∀ c∈l,c≠0) : (wordPolynomial r l).natDegree=r^l.length := by
  induction l with
  | nil => simp [wordPolynomial]
  | cons c l ih =>
    have hc := hl c (by simp)
    have hh := ih (fun a ha => hl a (by simp [ha]))
    have hp : 0<(wordPolynomial r l).natDegree := by rw [hh]; positivity
    rw [wordPolynomial,append_active_natDegree r hr _ hp c hc,hh,List.length_cons,pow_succ,Nat.mul_comm]

/-- No exceptional active coefficients: the ordered nonzero word is determined by the output. -/
theorem wordPolynomial_injective (r : ℕ) (hr : 2≤r) (l m : List ℝ)
    (hl : ∀ c∈l,c≠0) (hm : ∀ c∈m,c≠0)
    (he : wordPolynomial r l=wordPolynomial r m) : l=m := by
  have hlen : l.length=m.length := by
    apply Nat.pow_right_injective hr
    dsimp only
    rw [← wordPolynomial_natDegree r hr l hl,← wordPolynomial_natDegree r hr m hm,he]
  induction l generalizing m with
  | nil => exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | cons c l ih =>
    cases m with
    | nil => simp at hlen
    | cons d m =>
      obtain ⟨hH,hc⟩ := normalized_residual_append_injective r hr _ _
        (wordPolynomial_normalized r hr l).1 (wordPolynomial_normalized r hr m).1
        (wordPolynomial_normalized r hr l).2 (wordPolynomial_normalized r hr m).2
        c d (hl c (by simp)) (hm d (by simp)) he
      have htail := ih m (fun a ha => hl a (by simp [ha])) (fun a ha => hm a (by simp [ha])) hH (by simpa using hlen)
      rw [hc,htail]

theorem activeWord_nonzero (u : ℕ → ℝ) (L : ℕ) : ∀ c∈activeWord u L,c≠0 := by
  induction L with
  | zero => simp [activeWord]
  | succ L ih =>
    simp only [activeWord]
    split_ifs with h
    · exact ih
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact h
      · exact ih c hc

theorem activeWord_length (u : ℕ → ℝ) (L : ℕ) : (activeWord u L).length=activeCount u L := by
  induction L with
  | zero => simp [activeWord]
  | succ L ih => simp only [activeWord,activeCount_succ]; split_ifs <;> simp [ih]

theorem network_eq_wordPolynomial (r L : ℕ) (u : ℕ → ℝ) :
    network r u L=wordPolynomial r (activeWord u L) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [activeWord]
    split_ifs with h
    · simp [network,h,ih]
    · simp [network,wordPolynomial,ih]

/-- Full effective-coefficient fiber at any active count and any pair of depths. -/
theorem network_full_effective_fiber (r L M : ℕ) (hr : 2≤r) (u v : ℕ → ℝ) :
    network r u L=network r v M ↔ activeWord u L=activeWord v M := by
  rw [network_eq_wordPolynomial,network_eq_wordPolynomial]
  exact ⟨wordPolynomial_injective r hr _ _ (activeWord_nonzero u L) (activeWord_nonzero v M),congrArg (wordPolynomial r)⟩

/-- Full raw fiber: take r-th powers, delete zeros, and compare the ordered active words. -/
theorem network_full_raw_fiber (r L M : ℕ) (hr : 2≤r) (w : Fin L → ℝ) (t : Fin M → ℝ) :
    network r (fun i => zeroExtend w i^r) L=network r (fun i => zeroExtend t i^r) M ↔
      activeWord (fun i => zeroExtend w i^r) L=activeWord (fun i => zeroExtend t i^r) M :=
  network_full_effective_fiber r L M hr _ _

theorem mem_activeWord (u : ℕ → ℝ) (L : ℕ) (c : ℝ) :
    c∈activeWord u L ↔ c≠0 ∧ ∃ i<L,u i=c := by
  induction L with
  | zero => simp [activeWord]
  | succ L ih =>
    simp only [activeWord]
    split_ifs with h
    · rw [ih]
      constructor
      · rintro ⟨hc,i,hi,he⟩; exact ⟨hc,i,by omega,he⟩
      · rintro ⟨hc,i,hi,he⟩
        have hne : i≠L := by intro he'; subst i; exact hc (he.symm.trans h)
        exact ⟨hc,i,by omega,he⟩
    · rw [List.mem_cons,ih]
      constructor
      · rintro (rfl | ⟨hc,i,hi,he⟩)
        · exact ⟨h,L,by omega,rfl⟩
        · exact ⟨hc,i,by omega,he⟩
      · rintro ⟨hc,i,hi,he⟩
        by_cases hiL : i=L
        · exact Or.inl (by simpa [hiL] using he.symm)
        · exact Or.inr ⟨hc,i,by omega,he⟩

/-- Every fiber is finite, with no restriction on the number of active blocks. -/
theorem network_full_raw_fiber_finite (r L M : ℕ) (hr : 2≤r) (t : Fin M → ℝ) :
    {w : Fin L → ℝ | network r (fun i => zeroExtend w i^r) L=network r (fun i => zeroExtend t i^r) M}.Finite := by
  let V := (activeWord (fun i => zeroExtend t i^r) M).toFinset
  have hf : (⋃ c∈V, {x : ℝ | x^r=c}).Finite := V.finite_toSet.biUnion (fun c _ => finite_real_power_fiber r (by omega) c)
  apply (Set.Finite.pi' (fun _ : Fin L => (Set.finite_singleton (0:ℝ)).union hf)).subset
  intro w hw i
  by_cases hi : w i=0
  · exact Or.inl hi
  · apply Or.inr
    have he := (network_full_raw_fiber r L M hr w t).mp hw
    have hm : w i^r∈activeWord (fun j => zeroExtend w j^r) L := (mem_activeWord _ _ _).mpr
      ⟨pow_ne_zero _ hi,i.val,i.isLt,by simp [zeroExtend,i.isLt]⟩
    rw [he] at hm
    exact Set.mem_iUnion.mpr ⟨w i^r,Set.mem_iUnion.mpr ⟨by simpa [V] using hm,rfl⟩⟩

/-- Taking a nonzero power preserves the inactive positions and maps the retained word. -/
theorem activeWord_pow (u : ℕ → ℝ) (L r : ℕ) (hr : r≠0) :
    activeWord (fun i => u i^r) L=(activeWord u L).map (fun c => c^r) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [activeWord,pow_eq_zero_iff hr]
    split_ifs <;> simp [ih]

/-- Odd degrees preserve the exact raw active word, including all signs. -/
theorem network_full_raw_fiber_odd (r L M : ℕ) (hr : 2≤r) (ho : Odd r)
    (w : Fin L → ℝ) (t : Fin M → ℝ) :
    network r (fun i => zeroExtend w i^r) L=network r (fun i => zeroExtend t i^r) M ↔
      activeWord (zeroExtend w) L=activeWord (zeroExtend t) M := by
  rw [network_full_raw_fiber r L M hr,activeWord_pow _ _ _ (by omega),activeWord_pow _ _ _ (by omega)]
  exact (List.map_injective_iff.mpr ho.pow_injective).eq_iff

/-- For even degrees the only raw ambiguity at each active position is its independent sign. -/
theorem network_full_raw_fiber_even (r L M : ℕ) (hr : 2≤r) (he : Even r)
    (w : Fin L → ℝ) (t : Fin M → ℝ) :
    network r (fun i => zeroExtend w i^r) L=network r (fun i => zeroExtend t i^r) M ↔
      (activeWord (zeroExtend w) L).map abs=(activeWord (zeroExtend t) M).map abs := by
  rw [network_full_raw_fiber r L M hr,activeWord_pow _ _ _ (by omega),activeWord_pow _ _ _ (by omega)]
  have hh (l m : List ℝ) : l.map (fun c => c^r)=m.map (fun c => c^r) ↔ l.map abs=m.map abs := by
    induction l generalizing m with
    | nil => cases m <;> simp
    | cons a l ih =>
      cases m with
      | nil => simp
      | cons b m =>
        simp only [List.map_cons,List.cons.injEq,ih,pow_eq_pow_iff_of_ne_zero (by omega : r≠0),he,and_true,abs_eq_abs]
  exact hh _ _

/-- With all blocks active, equality recovers every effective coefficient in its original position. -/
theorem network_nonzero_prefix_injective (r k : ℕ) (hr : 2≤r) (u v : ℕ → ℝ)
    (hu : ∀ i<k,u i≠0) (hv : ∀ i<k,v i≠0) (he : network r u k=network r v k) :
    ∀ i<k,u i=v i := by
  have hw := (network_full_effective_fiber r k k hr u v).mp he
  clear he
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [activeWord,ite_eq_right (hu k (by omega)),ite_eq_right (hv k (by omega)),List.cons.injEq] at hw
    intro i hi
    by_cases hik : i=k
    · simpa [hik] using hw.1
    · exact ih (fun j hj => hu j (by omega)) (fun j hj => hv j (by omega)) hw.2 i (by omega)

end ResidualSLT
