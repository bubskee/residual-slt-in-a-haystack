import ResidualSLT
open ResidualSLT

-- Three simultaneously critical groups, two active blocks: logarithmic power three.
example : arrangementLearningPair 3 2 ![3,3,3] = ((5/2:ℝ),4) := by
  norm_num [arrangementLearningPair,identityLearningPair,Fin.sum_univ_succ]

-- Same ordered active chain, different group arrangements, different learning pairs.
example : arrangementLearningPair 3 2 ![0,6,0] = ((7/4:ℝ),1) := by
  norm_num [arrangementLearningPair,identityLearningPair,Fin.sum_univ_succ]
example : arrangementLearningPair 3 2 ![3,0,3] = ((2:ℝ),3) := by
  norm_num [arrangementLearningPair,identityLearningPair,Fin.sum_univ_succ]

-- Quadratic degree, empty and singleton groups, three active blocks.
example : arrangementLearningPair 2 3 ![0,1,2,0] = ((9/4:ℝ),1) := by
  norm_num [arrangementLearningPair,identityLearningPair,Fin.sum_univ_succ]

-- Odd degree with one critical and one supercritical group.
example : arrangementLearningPair 5 2 ![0,5,7] = ((21/10:ℝ),2) := by
  norm_num [arrangementLearningPair,identityLearningPair,Fin.sum_univ_succ]

-- Preserved depth-five, same-function one-active contrast.
example : arrangementLearningPair 3 1 ![0,4] = ((13/12:ℝ),1) := by
  norm_num [arrangementLearningPair,identityLearningPair,Fin.sum_univ_succ]
example : arrangementLearningPair 3 1 ![1,3] = ((7/6:ℝ),2) := by
  norm_num [arrangementLearningPair,identityLearningPair,Fin.sum_univ_succ]

-- Zero inactive variables: a regular three-parameter model.
example : arrangementLearningPair 3 3 ![0,0,0,0] = ((3/2:ℝ),1) := by
  norm_num [arrangementLearningPair,identityLearningPair,Fin.sum_univ_succ]

-- No active variables: identity-target specialization.
example : arrangementLearningPair 3 0 ![5] = ((2/3:ℝ),1) := by
  norm_num [arrangementLearningPair,identityLearningPair,Fin.sum_univ_succ]

#check arrangement_raw_network_rlct_laplace_certificate_of_depth_pos
#check arrangement_raw_network_boundary_divergence
#check arrangement_network_local_comparison
#check arrangementCoordinateEquiv_preimage_ball
#check arrangementCoordinateEquiv_measure_comparison
#check arrangementLearningPair_odd_multiplicity
#check arrangementLearningPair_even
#check arrangementLearningPair_one
#check arrangementFlatten_target

#print axioms arrangement_raw_network_rlct_laplace_certificate_of_depth_pos
#print axioms arrangement_raw_network_boundary_divergence
