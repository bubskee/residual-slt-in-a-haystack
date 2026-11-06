import ResidualSLT

open ResidualSLT Polynomial

-- Critical and noncritical global pairs, including every-block-active limits.
example : globalLearningPair 3 1 (4-1) = ((1:ℝ),2) := by
  norm_num [globalLearningPair,identityLearningPair]
example : globalLearningPair 3 1 (5-1) = ((13/12:ℝ),1) := by
  norm_num [globalLearningPair,identityLearningPair]
example : globalLearningPair 3 2 (5-2) = ((3/2:ℝ),2) := by
  norm_num [globalLearningPair,identityLearningPair]
example : globalLearningPair 3 2 (8-2) = ((7/4:ℝ),1) := by
  norm_num [globalLearningPair,identityLearningPair]
example : globalLearningPair 2 2 (6-2) = ((2:ℝ),1) := by
  norm_num [globalLearningPair,identityLearningPair]
example : globalLearningPair 3 1 0 = ((1/2:ℝ),1) := by
  norm_num [globalLearningPair,identityLearningPair]
example : globalLearningPair 2 2 0 = ((1:ℝ),1) := by
  norm_num [globalLearningPair,identityLearningPair]

-- Two critical groups have local multiplicity three, but their larger exponent
-- makes them globally subdominant to the one-gap realization at this same depth.
example : arrangementLearningPair 3 2 ![3,3,0] = ((2:ℝ),3) := by
  norm_num [arrangementLearningPair,identityLearningPair,Fin.sum_univ_succ]

-- Equal and opposite coefficients are covered by exact ordered recovery.
example (u v : ℝ) (h : twoActiveTarget 3 u v=twoActiveTarget 3 1 (-1)) :
    u=1 ∧ v= -1 := by
  exact twoActiveTarget_injective 3 (by omega) 1 (-1) u v (by norm_num) (by norm_num) h
example (u v : ℝ) (h : twoActiveTarget 2 u v=twoActiveTarget 2 1 1) :
    u=1 ∧ v=1 := by
  exact twoActiveTarget_injective 2 (by omega) 1 1 u v (by norm_num) (by norm_num) h

-- All quadratic raw signs survive, independently at the two active positions.
example (w : Fin 4 → ℝ) :
    network 2 (fun i => zeroExtend w i^2) 4=twoActiveTarget 2 1 1 ↔
      ∃ i j : Fin 4,i<j ∧ (w i=1 ∨ w i= -1) ∧ (w j=1 ∨ w j= -1) ∧
        ∀ a,a≠i → a≠j → w a=0 := by
  simpa using two_active_raw_fiber_even 2 4 (by omega) (by decide) 1 1 (by norm_num) (by norm_num) w

-- Realizability hypotheses are inhabited also for opposite coefficients.
example : ∃ t : Fin 5 → ℝ,
    network 3 (fun i => zeroExtend t i^3) 5=twoActiveTarget 3 1 (-1) := by
  simpa only [one_pow,show (-1:ℝ)^3= -1 by norm_num] using two_active_raw_target_exists 3 5 (by omega) (by omega) 1 (-1) (by norm_num) (by norm_num)
