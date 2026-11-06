module
public import ResidualSLT.SmallActiveRecovery

/-! Complete effective-coefficient fibers for one- and two-active targets. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset

theorem network_single_support (r L i : ℕ) (u : ℕ → ℝ)
    (hi : i < L) (hs : ∀ j<L, j ≠ i → u j = 0) : network r u L = activeTarget r (u i) := by
  have hp : network r u i = X := by
    apply network_congr_prefix r i u (fun _ => 0) (fun j hj => hs j (by omega) (by omega)) |>.trans
    exact network_zero_weights r i
  have hh (m : ℕ) (hm : i < m) (hmL : m ≤ L) : network r u m = activeTarget r (u i) := by
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases he : m=i
      · subst m; simp [network,hp,activeTarget]
      · rw [network_succ_of_zero r m u (hs m (by omega) he)]
        exact ih (by omega) (by omega)
  exact hh L hi le_rfl

theorem network_pair_support (r L i j : ℕ) (u : ℕ → ℝ)
    (hij : i < j) (hj : j < L) (hs : ∀ a<L, a ≠ i → a ≠ j → u a = 0) :
    network r u L = twoActiveTarget r (u i) (u j) := by
  have hp : network r u j = activeTarget r (u i) :=
    network_single_support r j i u hij (fun a ha hai => hs a (by omega) hai (by omega))
  have hh (m : ℕ) (hm : j < m) (hmL : m ≤ L) : network r u m = twoActiveTarget r (u i) (u j) := by
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases he : m=j
      · subst m; simp [network,hp,twoActiveTarget,activeTarget]
      · rw [network_succ_of_zero r m u (hs m (by omega) (by omega) he)]
        exact ih (by omega) (by omega)
  exact hh L hj le_rfl

theorem one_active_effective_fiber (r L : ℕ) (hr : 2 ≤ r) (c : ℝ) (hc : c ≠ 0) (u : ℕ → ℝ) :
    network r u L = activeTarget r c ↔
      ∃ i<L, u i=c ∧ ∀ j<L, j ≠ i → u j=0 := by
  classical
  constructor
  · intro he
    have hcard : activeCount u L=1 := by
      apply Nat.pow_right_injective hr
      dsimp only
      rw [← network_natDegree r hr,he,activeTarget_natDegree r hr c hc,pow_one]
    obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hcard
    have him : i ∈ (range L).filter (fun j => u j ≠ 0) := by rw [hi]; simp
    have hiL : i<L := (mem_filter.mp him).1 |> mem_range.mp
    have hs : ∀ j<L, j ≠ i → u j=0 := by
      intro j hj hji
      by_contra hn
      have hm : j ∈ (range L).filter (fun j => u j ≠ 0) := mem_filter.mpr ⟨mem_range.mpr hj,hn⟩
      simp [hi,hji] at hm
    refine ⟨i,hiL,?_,hs⟩
    exact activeTarget_injective r hr ((network_single_support r L i u hiL hs).symm.trans he)
  · rintro ⟨i,hi,hc',hs⟩
    rw [network_single_support r L i u hi hs,hc']

theorem two_active_effective_fiber (r L : ℕ) (hr : 2 ≤ r) (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) (u : ℕ → ℝ) :
    network r u L = twoActiveTarget r c d ↔
      ∃ i j, i<j ∧ j<L ∧ u i=c ∧ u j=d ∧ ∀ a<L, a ≠ i → a ≠ j → u a=0 := by
  classical
  constructor
  · intro he
    have hcard : activeCount u L=2 := by
      apply Nat.pow_right_injective hr
      dsimp only
      rw [← network_natDegree r hr,he,twoActiveTarget_natDegree r hr c d hc hd]
    obtain ⟨a,b,hab,hs⟩ := Finset.card_eq_two.mp hcard
    have hi : ∃ i j, i<j ∧ (range L).filter (fun a => u a ≠ 0) = {i,j} := by
      rcases lt_or_gt_of_ne hab with hab | hab
      · exact ⟨a,b,hab,hs⟩
      · exact ⟨b,a,hab,by simpa [pair_comm] using hs⟩
    obtain ⟨i,j,hij,hs⟩ := hi
    have hjm : j ∈ (range L).filter (fun a => u a ≠ 0) := by rw [hs]; simp
    have hjL : j<L := mem_range.mp (mem_filter.mp hjm).1
    have hz : ∀ a<L, a ≠ i → a ≠ j → u a=0 := by
      intro a ha hai haj
      by_contra hn
      have hm : a ∈ (range L).filter (fun a => u a ≠ 0) := mem_filter.mpr ⟨mem_range.mpr ha,hn⟩
      simp [hs,hai,haj] at hm
    obtain ⟨huc,hud⟩ := twoActiveTarget_injective r hr c d (u i) (u j) hc hd
      ((network_pair_support r L i j u hij hjL hz).symm.trans he)
    exact ⟨i,j,hij,hjL,huc,hud,hz⟩
  · rintro ⟨i,j,hij,hjL,huc,hud,hz⟩
    rw [network_pair_support r L i j u hij hjL hz,huc,hud]

end ResidualSLT
