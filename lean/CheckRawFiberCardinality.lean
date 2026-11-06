import ResidualSLT

open ResidualSLT Set

-- Repeated and opposite raw coefficients do not introduce an extra permutation factor.
example : (rawNetworkFiber 3 6 3 (![1,-1,1] : Fin 3 → ℝ)).ncard=20 := by
  have hk : activeCount (zeroExtend (![1,-1,1] : Fin 3 → ℝ)) 3=3 := by
    rw [← activeWord_length]
    norm_num [activeWord,zeroExtend]
  simpa [Nat.choose] using raw_network_fiber_ncard_odd 3 6 3 3 (by omega) (by decide) _ hk

-- Quadratic repeated magnitudes: exactly eight independent sign assignments per support.
example : (rawNetworkFiber 2 6 3 (![1,-1,2] : Fin 3 → ℝ)).ncard=160 := by
  have hk : activeCount (zeroExtend (![1,-1,2] : Fin 3 → ℝ)) 3=3 := by
    rw [← activeWord_length]
    norm_num [activeWord,zeroExtend]
  simpa [Nat.choose] using raw_network_fiber_ncard_even 2 6 3 3 (by omega) (by decide) _ hk

-- Fully occupied support: unique odd raw realization, all 2^k even sign choices.
example (t : Fin 4 → ℝ) (hk : activeCount (zeroExtend t) 4=4) :
    (rawNetworkFiber 3 4 4 t).ncard=1 := by
  simpa using raw_network_fiber_ncard_odd 3 4 4 4 (by omega) (by decide) t hk
example (t : Fin 4 → ℝ) (hk : activeCount (zeroExtend t) 4=4) :
    (rawNetworkFiber 4 4 4 t).ncard=16 := by
  simpa using raw_network_fiber_ncard_even 4 4 4 4 (by omega) (by decide) t hk

-- The empty active chain has one realization, regardless of available depth and parity.
example (t : Fin 0 → ℝ) : (rawNetworkFiber 3 5 0 t).ncard=1 := by
  simpa using raw_network_fiber_ncard_odd 3 5 0 0 (by omega) (by decide) t (by simp)
example (t : Fin 0 → ℝ) : (rawNetworkFiber 2 5 0 t).ncard=1 := by
  simpa using raw_network_fiber_ncard_even 2 5 0 0 (by omega) (by decide) t (by simp)
example (t : Fin 0 → ℝ) : (rawNetworkFiber 2 0 0 t).ncard=1 := by
  simpa using raw_network_fiber_ncard_even 2 0 0 0 (by omega) (by decide) t (by simp)

-- A target with more active coefficients than available positions has no realizations.
example (t : Fin 4 → ℝ) (hk : activeCount (zeroExtend t) 4=4) :
    (rawNetworkFiber 3 2 4 t).ncard=0 := by
  simpa [Nat.choose] using raw_network_fiber_ncard_odd 3 2 4 4 (by omega) (by decide) t hk
example (t : Fin 4 → ℝ) (hk : activeCount (zeroExtend t) 4=4) :
    (rawNetworkFiber 2 2 4 t).ncard=0 := by
  simpa [Nat.choose] using raw_network_fiber_ncard_even 2 2 4 4 (by omega) (by decide) t hk

-- Arbitrary active count remains symbolic; no fixed-depth enumeration is used.
example (r L M k : ℕ) (hr : 2≤r) (t : Fin M → ℝ)
    (hk : activeCount (zeroExtend t) M=k) :
    (rawNetworkFiber r L M t).Finite ∧
      (rawNetworkFiber r L M t).ncard=(if Even r then 2^k else 1)*L.choose k :=
  raw_network_fiber_cardinality r L M k hr t hk
