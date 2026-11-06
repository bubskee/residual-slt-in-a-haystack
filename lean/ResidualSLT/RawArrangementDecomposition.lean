module
public import ResidualSLT.ActiveWordFiber
public import Mathlib.Data.Finset.Sort

/-! Every raw vector has its exact chronological active-block arrangement. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset

/-- Ordered active positions, together with the right endpoint of the vector. -/
@[expose] def activeBoundary (L k : ℕ) (p : Fin k → Fin L) (j : ℕ) : ℕ :=
  if h : j<k then (p ⟨j,h⟩).val else L

@[expose] def activeGaps (L k : ℕ) (p : Fin k → Fin L) (g : Fin (k+1)) : ℕ :=
  if g.val=0 then activeBoundary L k p 0
  else activeBoundary L k p g.val-(activeBoundary L k p (g.val-1)+1)

theorem activeBoundary_end (L k : ℕ) (p : Fin k → Fin L) : activeBoundary L k p k=L := by
  simp [activeBoundary]

theorem activeBoundary_mono (L k : ℕ) (p : Fin k → Fin L) (hp : StrictMono p)
    (i j : ℕ) (hij : i<j) (hj : j≤k) : activeBoundary L k p i<activeBoundary L k p j := by
  have hi : i<k := by omega
  by_cases hj' : j<k
  · simpa only [activeBoundary,dite_eq_left hi,dite_eq_left hj'] using (show (p ⟨i,hi⟩).val < (p ⟨j,hj'⟩).val from hp (show (⟨i,hi⟩:Fin k)<⟨j,hj'⟩ from hij))
  · simp only [activeBoundary,dite_eq_left hi,dite_eq_right hj']
    exact (p ⟨i,hi⟩).isLt

theorem activeGaps_depth (L k : ℕ) (p : Fin k → Fin L) (hp : StrictMono p)
    (m : ℕ) (hm : m≤k) :
    arrangementDepth k (activeGaps L k p) m hm=activeBoundary L k p m := by
  induction m with
  | zero => simp [arrangementDepth,activeGaps]
  | succ m ih =>
    have hh := ih (by omega)
    have hstep := activeBoundary_mono L k p hp m (m+1) (by omega) hm
    simp only [arrangementDepth,hh,activeGaps,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false,
      Nat.add_sub_cancel_right]
    omega

/-- Flattening these exact gaps and raw active values reconstructs every coordinate. -/
theorem activeGaps_flatten (L k : ℕ) (w : Fin L → ℝ) (p : Fin k → Fin L) (hp : StrictMono p)
    (hz : ∀ i : Fin L,w i≠0 → ∃ j,p j=i)
    (m : ℕ) (hm : m≤k) (i : Fin (arrangementDepth k (activeGaps L k p) m hm)) :
    arrangementFlatten k (activeGaps L k p) (fun j => w (p j)) 0 m hm i =
      zeroExtend w i.val := by
  have hdepth := activeGaps_depth L k p hp m hm
  have hi : i.val<activeBoundary L k p m := hdepth ▸ i.isLt
  have hbound : activeBoundary L k p m≤L := by
    unfold activeBoundary
    split_ifs with h
    · exact (p ⟨m,h⟩).isLt.le
    · exact le_rfl
  have hiL : i.val<L := hi.trans_le hbound
  have hzero (a : ℕ) (ha : a≤k) (hlo : activeBoundary L k p a ≤ i.val)
      (hhi : i.val<activeBoundary L k p (a+1)) (he : i.val≠activeBoundary L k p a) : zeroExtend w i.val=0 := by
    by_contra hn
    have hw : w ⟨i.val,hiL⟩≠0 := by simpa [zeroExtend,hiL] using hn
    obtain ⟨j,hj⟩ := hz ⟨i.val,hiL⟩ hw
    have hji : activeBoundary L k p j.val=i.val := by simp only [activeBoundary,dite_eq_left j.isLt]; exact congrArg Fin.val hj
    by_cases hja : j.val≤a
    · by_cases hje : j.val=a
      · exact he (hje ▸ hji.symm)
      · have hh := activeBoundary_mono L k p hp j.val a (by omega) ha
        omega
    · have hh : activeBoundary L k p (a+1)≤activeBoundary L k p j.val := by
        by_cases hje : a+1=j.val
        · exact (congrArg (activeBoundary L k p) hje).le
        · exact (activeBoundary_mono L k p hp (a+1) j.val (by omega) j.isLt.le).le
      omega
  induction m with
  | zero =>
    change 0=zeroExtend w i.val
    by_contra hn
    have hw : w ⟨i.val,hiL⟩≠0 := by simpa [zeroExtend,hiL,eq_comm] using hn
    obtain ⟨j,hj⟩ := hz ⟨i.val,hiL⟩ hw
    have hjv : (p j).val=i.val := congrArg Fin.val hj
    have hle : activeBoundary L k p 0≤(p j).val := by
      by_cases hj0 : j.val=0
      · simp only [activeBoundary,dite_eq_left (show 0<k by omega)]
        exact (congrArg (fun a : Fin k => (p a).val) (Fin.ext hj0.symm)).le
      · have hh := activeBoundary_mono L k p hp 0 j.val (by omega) j.isLt.le
        simpa only [activeBoundary,dite_eq_left j.isLt] using hh.le
    omega
  | succ m ih =>
    change oneActiveAssemble _ _ _ (0,arrangementFlatten k (activeGaps L k p) (fun j => w (p j)) 0 m (by omega),0) i=zeroExtend w i.val
    unfold oneActiveAssemble
    split_ifs with hbefore hat
    · have hd := activeGaps_depth L k p hp m (by omega)
      exact ih (by omega) ⟨i.val,hbefore⟩ hd (hbefore.trans_eq hd)
        ((activeBoundary_mono L k p hp m (m+1) (by omega) hm).le.trans hbound) hiL hzero
    · simp only [add_zero]
      have hid : i.val=activeBoundary L k p m := hat.trans (activeGaps_depth L k p hp m (by omega))
      have hm' : m<k := by omega
      rw [activeBoundary,dite_eq_left hm'] at hid
      simp only [zeroExtend,dite_eq_left hiL]
      exact congrArg w (Fin.ext hid.symm)
    · change 0=zeroExtend w i.val
      apply Eq.symm
      apply hzero m (by omega)
      · have hd := activeGaps_depth L k p hp m (by omega); omega
      · exact hi
      · have hd := activeGaps_depth L k p hp m (by omega); omega

/-- Every vector is an actual arrangement center, including the all-zero vector. -/
theorem raw_vector_arrangement (L : ℕ) (w : Fin L → ℝ) :
    ∃ k : ℕ,∃ n : Fin (k+1) → ℕ,∃ τ : Fin k → ℝ,(∀ j,τ j≠0) ∧
      ∃ hd : arrangementDepth k n k le_rfl=L,
        ∀ i : Fin (arrangementDepth k n k le_rfl),w (Fin.cast hd i)=arrangementFlatten k n τ 0 k le_rfl i := by
  classical
  let s := univ.filter (fun i : Fin L => w i≠0)
  let k := s.card
  let p : Fin k ↪o Fin L := s.orderEmbOfFin rfl
  have hp : StrictMono (fun j => p j) := p.strictMono
  have hn (j : Fin k) : w (p j)≠0 := (mem_filter.mp (s.orderEmbOfFin_mem rfl j)).2
  have hz (i : Fin L) (hi : w i≠0) : ∃ j,p j=i := by
    have hm : i∈s := mem_filter.mpr ⟨mem_univ _,hi⟩
    have hh : i∈Set.range p := by rw [Finset.range_orderEmbOfFin]; exact hm
    exact hh
  have hd : arrangementDepth k (activeGaps L k p) k le_rfl=L :=
    (activeGaps_depth L k p hp k le_rfl).trans (activeBoundary_end L k p)
  refine ⟨k,activeGaps L k p,fun j => w (p j),hn,hd,?_⟩
  intro i
  rw [activeGaps_flatten L k w p hp hz k le_rfl i]
  simp only [zeroExtend,dite_eq_left (show i.val<L from i.isLt.trans_eq hd)]
  exact congrArg w (Fin.ext (by simp))

theorem activeCount_nonzero_prefix (u : ℕ → ℝ) (k : ℕ) (hu : ∀ i<k,u i≠0) :
    activeCount u k=k := by
  unfold activeCount
  rw [filter_eq_self.mpr (fun i hi => hu i (mem_range.mp hi)),card_range]

theorem network_eq_activeCount (r L M : ℕ) (hr : 2≤r) (u v : ℕ → ℝ)
    (he : network r u L=network r v M) : activeCount u L=activeCount v M := by
  have hh := congrArg List.length ((network_full_effective_fiber r L M hr u v).mp he)
  simpa only [activeWord_length] using hh

/-- Exact inactive groups at a specified active count; the all-inactive case is included. -/
theorem raw_vector_arrangement_of_activeCount (r L k : ℕ) (hr : 2≤r) (w : Fin L → ℝ)
    (hk : activeCount (fun i => zeroExtend w i^r) L=k) :
    ∃ n : Fin (k+1) → ℕ,∃ τ : Fin k → ℝ,(∀ j,τ j≠0) ∧ (∑ g,n g)=L-k ∧
      ∃ hd : arrangementDepth k n k le_rfl=L,
        ∀ i : Fin (arrangementDepth k n k le_rfl),w (Fin.cast hd i)=arrangementFlatten k n τ 0 k le_rfl i := by
  obtain ⟨j,n,τ,hτ,hd,hw⟩ := raw_vector_arrangement L w
  have hc : activeCount (zeroExtend (fun a => τ a^r)) j=j := by
    apply activeCount_nonzero_prefix
    intro i hi
    simpa [zeroExtend,hi] using pow_ne_zero r (hτ ⟨i,hi⟩)
  have he := network_eq_activeCount r L j hr _ _ (arrangement_center_polynomial r L j hr n τ hd w hw)
  rw [hc,hk] at he
  subst j
  refine ⟨n,τ,hτ,?_,hd,hw⟩
  have hh := arrangementDepth_eq_sum k n k le_rfl
  simp only [Fin.eta,hd] at hh
  omega

end ResidualSLT
