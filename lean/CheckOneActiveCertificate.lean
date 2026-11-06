import ResidualSLT
open ResidualSLT

example : oneActiveLearningPair 3 0 4 = (13/12,1) := by
  norm_num [oneActiveLearningPair,identityLearningPair,Nat.even_iff]
example : oneActiveLearningPair 3 1 3 = (7/6,2) := by
  norm_num [oneActiveLearningPair,identityLearningPair,Nat.even_iff]
example : oneActiveLearningPair 3 2 2 = (7/6,1) := by
  norm_num [oneActiveLearningPair,identityLearningPair,Nat.even_iff]
example : oneActiveLearningPair 3 3 3 = (3/2,3) := by
  norm_num [oneActiveLearningPair,identityLearningPair,Nat.even_iff]
example (r : ℕ) (hr : 2 ≤ r) : oneActiveLearningPair r 0 0 = (1/2,1) := by
  simp [oneActiveLearningPair,identityLearningPair_zero r hr]
example : oneActiveLearningPair 2 0 4 = (3/2,1) := by
  norm_num [oneActiveLearningPair,identityLearningPair,Nat.even_iff]
example : oneActiveLearningPair 2 1 3 = (3/2,1) := by
  norm_num [oneActiveLearningPair,identityLearningPair,Nat.even_iff]
