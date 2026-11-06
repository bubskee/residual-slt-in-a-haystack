import ResidualSLT

open ResidualSLT Polynomial

-- Three active coefficients, including a repeated coefficient and an opposite pair.
-- Arbitrary zero insertion changes depth without changing the function.
example :
    network 3 (fun i => zeroExtend (![0,1,0,-1,1,0] : Fin 6 → ℝ) i^3) 6 =
      network 3 (fun i => zeroExtend (![1,-1,1] : Fin 3 → ℝ) i^3) 3 := by
  rw [network_full_raw_fiber_odd 3 6 3 (by omega) (by decide)]
  norm_num [activeWord,zeroExtend]

-- Independent even-degree raw signs, repeated magnitudes, and zero insertion.
example :
    network 2 (fun i => zeroExtend (![0,-1,2,0,-1] : Fin 5 → ℝ) i^2) 5 =
      network 2 (fun i => zeroExtend (![1,2,1] : Fin 3 → ℝ) i^2) 3 := by
  rw [network_full_raw_fiber_even 2 5 3 (by omega) (by decide)]
  norm_num [activeWord,zeroExtend]

-- Order matters even in the repeated/opposite-coefficient case.
example :
    network 3 (fun i => zeroExtend (![1,-1,1] : Fin 3 → ℝ) i^3) 3 ≠
      network 3 (fun i => zeroExtend (![-1,1,1] : Fin 3 → ℝ) i^3) 3 := by
  rw [ne_eq,network_full_raw_fiber_odd 3 3 3 (by omega) (by decide)]
  norm_num [activeWord,zeroExtend]

-- Explicit raw active count of the depth-six realization above.
example : activeCount (fun i => zeroExtend (![0,1,0,-1,1,0] : Fin 6 → ℝ) i^3) 6=3 := by
  rw [← activeWord_length]
  norm_num [activeWord,zeroExtend]

-- Critical, supercritical, even-degree, all-active, and identity-target limits.
example : globalLearningPair 3 3 (6-3)=((2:ℝ),2) := by
  norm_num [globalLearningPair,identityLearningPair]
example : globalLearningPair 3 3 (7-3)=((25/12:ℝ),1) := by
  norm_num [globalLearningPair,identityLearningPair]
example : globalLearningPair 3 4 (10-4)=((11/4:ℝ),1) := by
  norm_num [globalLearningPair,identityLearningPair]
example : globalLearningPair 2 3 (8-3)=((11/4:ℝ),1) := by
  norm_num [globalLearningPair,identityLearningPair]
example : globalLearningPair 4 4 0=((2:ℝ),1) := by
  norm_num [globalLearningPair,identityLearningPair]
example : globalLearningPair 3 0 3=((1/2:ℝ),2) := by
  norm_num [globalLearningPair,identityLearningPair]

-- Four critical inactive groups produce a local logarithm power four, but that
-- realization is globally subdominant to concentrating the twelve inactive blocks.
example : arrangementLearningPair 3 3 ![3,3,3,3]=((7/2:ℝ),5) := by
  norm_num [arrangementLearningPair,identityLearningPair,Fin.sum_univ_succ]
example : globalLearningPair 3 3 12=((11/4:ℝ),1) := by
  norm_num [globalLearningPair,identityLearningPair]

-- The fully-active recovery theorem has no fixed bound on active count.
example (r k : ℕ) (hr : 2≤r) (u v : ℕ → ℝ)
    (hu : ∀ i<k,u i≠0) (hv : ∀ i<k,v i≠0) (h : network r u k=network r v k) :
    ∀ i<k,u i=v i := network_nonzero_prefix_injective r k hr u v hu hv h
