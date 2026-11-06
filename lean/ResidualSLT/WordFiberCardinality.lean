module
public import ResidualSLT.ArbitraryActiveGlobalCertificate
public import Mathlib.Data.Set.Card

/-! Exact weighted counts for a fixed ordered word with arbitrary zero insertion. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Set

theorem activeWord_congr_prefix (L : ℕ) (u v : ℕ → ℝ) (h : ∀ i<L,u i=v i) :
    activeWord u L=activeWord v L := by
  induction L with
  | zero => rfl
  | succ L ih => rw [activeWord,activeWord,h L (by omega),ih (fun i hi => h i (by omega))]

theorem activeWord_nil_iff (u : ℕ → ℝ) (L : ℕ) : activeWord u L=[] ↔ ∀ i<L,u i=0 := by
  constructor
  · intro h i hi
    by_contra hn
    have hh := (mem_activeWord u L (u i)).mpr ⟨hn,i,hi,rfl⟩
    simp [h] at hh
  · intro h
    have hh := activeWord_congr_prefix L u (fun _ => 0) h
    rw [hh]
    clear hh h u
    induction L with
    | zero => rfl
    | succ L ih => simp only [activeWord,ite_true]; exact ih

/-- Appending one raw coordinate either inserts a zero or retains one new leading entry. -/
theorem activeWord_snoc (f : ℝ → ℝ) (L : ℕ) (w : Fin L → ℝ) (a : ℝ) :
    activeWord (fun i => f (zeroExtend (Fin.snoc w a) i)) (L+1)=
      if f a=0 then activeWord (fun i => f (zeroExtend w i)) L
      else f a :: activeWord (fun i => f (zeroExtend w i)) L := by
  have hp : activeWord (fun i => f (zeroExtend (Fin.snoc w a) i)) L=
      activeWord (fun i => f (zeroExtend w i)) L := by
    apply activeWord_congr_prefix
    intro i hi
    simp only [zeroExtend,dite_eq_left hi,dite_eq_left (show i<L+1 by omega)]
    congr 1
    exact Fin.snoc_castSucc (α := fun _ : Fin (L+1) => ℝ) a w ⟨i,hi⟩
  have he : zeroExtend (Fin.snoc w a) L=a := by
    simp only [zeroExtend,dite_eq_left (show L<L+1 by omega)]
    exact Fin.snoc_last (α := fun _ : Fin (L+1) => ℝ) a w
  rw [activeWord,hp,he]

@[expose] def wordFiber (f : ℝ → ℝ) (L : ℕ) (l : List ℝ) : Set (Fin L → ℝ) :=
  {w | activeWord (fun i => f (zeroExtend w i)) L=l}

theorem wordFiber_nil (f : ℝ → ℝ) (hf : ∀ x,f x=0 ↔ x=0) (L : ℕ) :
    wordFiber f L []={0} := by
  ext w
  change (activeWord (fun i => f (zeroExtend w i)) L=[]) ↔ w=0
  rw [activeWord_nil_iff]
  constructor
  · intro h
    funext i
    have hh := (hf _).mp (h i.val i.isLt)
    simpa [zeroExtend,i.isLt] using hh
  · rintro rfl i hi
    exact (hf _).mpr (by simp [zeroExtend])

theorem wordFiber_zero_cons (f : ℝ → ℝ) (c : ℝ) (l : List ℝ) :
    wordFiber f 0 (c::l)=∅ := by
  ext w
  simp [wordFiber,activeWord]

theorem snoc_pair_injective (L : ℕ) :
    Function.Injective (fun p : ℝ × (Fin L → ℝ) => Fin.snoc (α := fun _ : Fin (L+1) => ℝ) p.2 p.1) := by
  intro x y h
  obtain ⟨h₂,h₁⟩ := Fin.snoc_inj.mp h
  exact Prod.ext h₁ h₂

/-- Disjoint last-coordinate alternatives, expressed as actual images of finite product sets. -/
theorem wordFiber_succ_cons (f : ℝ → ℝ) (hf : ∀ x,f x=0 ↔ x=0)
    (L : ℕ) (c : ℝ) (hc : c≠0) (l : List ℝ) :
    wordFiber f (L+1) (c::l)=
      (fun p : ℝ × (Fin L → ℝ) => Fin.snoc p.2 p.1) ''
        (({0} ×ˢ wordFiber f L (c::l)) ∪ ({x | f x=c} ×ˢ wordFiber f L l)) := by
  ext w
  constructor
  · intro hw
    change activeWord (fun i => f (zeroExtend w i)) (L+1)=c::l at hw
    rw [← Fin.snoc_init_self w,activeWord_snoc] at hw
    refine ⟨(w (Fin.last L),Fin.init w),?_,Fin.snoc_init_self w⟩
    by_cases hz : f (w (Fin.last L))=0
    · rw [ite_eq_left hz] at hw
      exact Or.inl ⟨(hf _).mp hz,hw⟩
    · rw [ite_eq_right hz] at hw
      exact Or.inr (List.cons.inj hw)
  · rintro ⟨⟨a,v⟩,hv,rfl⟩
    change activeWord (fun i => f (zeroExtend (Fin.snoc v a) i)) (L+1)=c::l
    rw [activeWord_snoc]
    rcases hv with ⟨ha,hv⟩ | ⟨ha,hv⟩
    · have hz : f a=0 := (hf a).mpr ha
      rw [ite_eq_left hz]
      exact hv
    · rw [ha,ite_eq_right hc]
      exact congrArg (List.cons c) hv

/-- A fixed nonzero word of length k, with q raw choices for each letter, has exactly
q^k * choose(L,k) realizations. The count is zero automatically when k>L. -/
theorem wordFiber_finite_ncard (f : ℝ → ℝ) (hf : ∀ x,f x=0 ↔ x=0) (q L : ℕ)
    (l : List ℝ) (hl : ∀ c∈l,c≠0)
    (hroot : ∀ c∈l, {x : ℝ | f x=c}.Finite ∧ {x : ℝ | f x=c}.ncard=q) :
    (wordFiber f L l).Finite ∧ (wordFiber f L l).ncard=q^l.length*L.choose l.length := by
  induction L generalizing l with
  | zero =>
    cases l with
    | nil => simp [wordFiber_nil f hf]
    | cons c l => simp [wordFiber_zero_cons]
  | succ L ih =>
    cases l with
    | nil => simp [wordFiber_nil f hf]
    | cons c l =>
      have hc := hl c (by simp)
      have hrc := hroot c (by simp)
      have hcons := ih (c::l) hl hroot
      have htail := ih l (fun a ha => hl a (by simp [ha])) (fun a ha => hroot a (by simp [ha]))
      have hd : Disjoint ({0} ×ˢ wordFiber f L (c::l)) ({x : ℝ | f x=c} ×ˢ wordFiber f L l) := by
        apply Set.disjoint_left.mpr
        rintro ⟨a,v⟩ ⟨ha,_⟩ ⟨he,_⟩
        exact hc (he.symm.trans ((hf a).mpr ha))
      have hz := (Set.finite_singleton (0:ℝ)).prod hcons.1
      have hn := hrc.1.prod htail.1
      rw [wordFiber_succ_cons f hf L c hc l]
      refine ⟨(hz.union hn).image _,?_⟩
      rw [Set.ncard_image_of_injective _ (snoc_pair_injective L),Set.ncard_union_eq hd hz hn,
        Set.ncard_prod,Set.ncard_prod,Set.ncard_singleton,hcons.2,htail.2,hrc.2,List.length_cons,
        Nat.choose_succ_succ,pow_succ]
      ring

end ResidualSLT
