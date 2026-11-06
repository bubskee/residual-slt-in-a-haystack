module
public import ResidualSLT.WordFiberCardinality

/-! Exact raw-fiber cardinalities at every active count, including all independent even signs. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Set MeasureTheory

@[expose] def rawNetworkFiber (r L M : ℕ) (t : Fin M → ℝ) : Set (Fin L → ℝ) :=
  {w | network r (fun i => zeroExtend w i^r) L=network r (fun i => zeroExtend t i^r) M}

theorem rawNetworkFiber_eq_wordFiber (r L M : ℕ) (hr : 2≤r) (t : Fin M → ℝ) :
    rawNetworkFiber r L M t=wordFiber (fun x => x^r) L (activeWord (fun i => zeroExtend t i^r) M) := by
  ext w
  exact network_full_raw_fiber r L M hr w t

theorem rawNetworkFiber_finite (r L M : ℕ) (hr : 2≤r) (t : Fin M → ℝ) :
    (rawNetworkFiber r L M t).Finite := network_full_raw_fiber_finite r L M hr t

theorem odd_power_fiber_ncard (r : ℕ) (ho : Odd r) (a : ℝ) :
    {x : ℝ | x^r=a^r}.ncard=1 := by
  have he : {x : ℝ | x^r=a^r}={a} := by ext x; simp only [mem_ofPred_eq,mem_singleton_iff,ho.pow_inj]
  rw [he,Set.ncard_singleton]

theorem even_power_fiber_ncard (r : ℕ) (hr : r≠0) (he : Even r) (a : ℝ) (ha : a≠0) :
    {x : ℝ | x^r=a^r}.ncard=2 := by
  have hh : {x : ℝ | x^r=a^r}={a,-a} := by
    ext x
    simp only [mem_ofPred_eq,mem_insert_iff,mem_singleton_iff,pow_eq_pow_iff_of_ne_zero hr,he,and_true]
  rw [hh]
  apply Set.ncard_pair
  intro hz
  apply ha
  linarith

/-- Exact odd-degree fiber size: one raw value for each ordered active coefficient,
with choose(L,k) choices of its occupied positions. Different target depth M is allowed. -/
theorem raw_network_fiber_ncard_odd (r L M k : ℕ) (hr : 2≤r) (ho : Odd r)
    (t : Fin M → ℝ) (hk : activeCount (zeroExtend t) M=k) :
    (rawNetworkFiber r L M t).ncard=L.choose k := by
  rw [rawNetworkFiber_eq_wordFiber r L M hr t]
  have hh := wordFiber_finite_ncard (fun x => x^r) (fun _ => pow_eq_zero_iff (by omega : r≠0))
    1 L (activeWord (fun i => zeroExtend t i^r) M) (activeWord_nonzero _ _) (by
      intro a ha
      obtain ⟨_,i,_,he⟩ := (mem_activeWord (fun i => zeroExtend t i^r) M a).mp ha
      refine ⟨finite_real_power_fiber r (by omega) a,?_⟩
      rw [← he]
      exact odd_power_fiber_ncard r ho _)
  simpa only [one_pow,one_mul,activeWord_length,raw_activeCount_eq r M (by omega) t,hk] using hh.2

/-- Exact even-degree fiber size: the two signs at each of k active positions are
independent, including repeated active magnitudes and the quadratic case. -/
theorem raw_network_fiber_ncard_even (r L M k : ℕ) (hr : 2≤r) (he : Even r)
    (t : Fin M → ℝ) (hk : activeCount (zeroExtend t) M=k) :
    (rawNetworkFiber r L M t).ncard=2^k*L.choose k := by
  rw [rawNetworkFiber_eq_wordFiber r L M hr t]
  have hh := wordFiber_finite_ncard (fun x => x^r) (fun _ => pow_eq_zero_iff (by omega : r≠0))
    2 L (activeWord (fun i => zeroExtend t i^r) M) (activeWord_nonzero _ _) (by
      intro a ha
      obtain ⟨ha0,i,_,hi⟩ := (mem_activeWord (fun i => zeroExtend t i^r) M a).mp ha
      refine ⟨finite_real_power_fiber r (by omega) a,?_⟩
      rw [← hi]
      apply even_power_fiber_ncard r (by omega) he
      intro hz
      rw [hz,zero_pow (by omega : r≠0)] at hi
      exact ha0 hi.symm)
  simpa only [activeWord_length,raw_activeCount_eq r M (by omega) t,hk] using hh.2

/-- Uniform finite-fiber cardinality for every realized target, including k=0 and L<k. -/
theorem raw_network_fiber_cardinality (r L M k : ℕ) (hr : 2≤r)
    (t : Fin M → ℝ) (hk : activeCount (zeroExtend t) M=k) :
    (rawNetworkFiber r L M t).Finite ∧
      (rawNetworkFiber r L M t).ncard=(if Even r then 2^k else 1)*L.choose k := by
  refine ⟨rawNetworkFiber_finite r L M hr t,?_⟩
  rcases Nat.even_or_odd r with he | ho
  · simpa only [ite_eq_left he] using raw_network_fiber_ncard_even r L M k hr he t hk
  · simpa only [ite_eq_right (Nat.not_even_iff_odd.mpr ho),one_mul] using raw_network_fiber_ncard_odd r L M k hr ho t hk

/-- The same exact count for the actual population-loss zero fiber under the sparse Gram. -/
theorem networkTargetLoss_fiber_cardinality (μ : Measure ℝ) (r L k : ℕ) (hr : 2≤r) (hL : 0<L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (t : Fin L → ℝ) (hk : activeCount (zeroExtend t) L=k) :
    {w : Fin L → ℝ | networkTargetLoss μ r t w=0}.Finite ∧
      {w : Fin L → ℝ | networkTargetLoss μ r t w=0}.ncard=(if Even r then 2^k else 1)*L.choose k := by
  have he : {w : Fin L → ℝ | networkTargetLoss μ r t w=0}=rawNetworkFiber r L L t := by
    ext w
    exact networkTargetLoss_eq_zero_iff μ r L hr hL hμ t w
  rw [he]
  exact raw_network_fiber_cardinality r L L k hr t hk

end ResidualSLT
