module
import ResidualSLT

#check @ResidualSLT.PowerLaplaceUpper
#print axioms ResidualSLT.PowerLaplaceUpper
#check @ResidualSLT.PowerLaplaceLower
#print axioms ResidualSLT.PowerLaplaceLower
#check @ResidualSLT.HasPowerLaplaceOrder
#print axioms ResidualSLT.HasPowerLaplaceOrder
#check @ResidualSLT.PowerLaplaceUpper.mono
#print axioms ResidualSLT.PowerLaplaceUpper.mono
#check @ResidualSLT.PowerLaplaceLower.mono
#print axioms ResidualSLT.PowerLaplaceLower.mono
#check @ResidualSLT.PowerLaplaceUpper.const_mul
#print axioms ResidualSLT.PowerLaplaceUpper.const_mul
#check @ResidualSLT.PowerLaplaceLower.const_mul
#print axioms ResidualSLT.PowerLaplaceLower.const_mul
#check @ResidualSLT.PowerLaplaceUpper.comp_mul
#print axioms ResidualSLT.PowerLaplaceUpper.comp_mul
#check @ResidualSLT.PowerLaplaceLower.comp_mul
#print axioms ResidualSLT.PowerLaplaceLower.comp_mul
#check @ResidualSLT.PowerLaplaceUpper.add
#print axioms ResidualSLT.PowerLaplaceUpper.add
#check @ResidualSLT.powerLaplaceUpper_zero
#print axioms ResidualSLT.powerLaplaceUpper_zero
#check @ResidualSLT.PowerLaplaceUpper.finset_sum
#print axioms ResidualSLT.PowerLaplaceUpper.finset_sum
#check @ResidualSLT.HasPowerLaplaceOrder.bounds
#print axioms ResidualSLT.HasPowerLaplaceOrder.bounds
#check @ResidualSLT.PowerLaplaceUpper.const_mul_nonneg
#print axioms ResidualSLT.PowerLaplaceUpper.const_mul_nonneg
#check @ResidualSLT.PowerLaplaceUpper.weaken
#print axioms ResidualSLT.PowerLaplaceUpper.weaken
#check @ResidualSLT.coneLaplaceExponent
#print axioms ResidualSLT.coneLaplaceExponent
#check @ResidualSLT.powerWeightedKernel
#print axioms ResidualSLT.powerWeightedKernel
#check @ResidualSLT.powerWeightedBox
#print axioms ResidualSLT.powerWeightedBox
#check @ResidualSLT.radialGammaConstant
#print axioms ResidualSLT.radialGammaConstant
#check @ResidualSLT.radialGammaConstant_pos
#print axioms ResidualSLT.radialGammaConstant_pos
#check @ResidualSLT.radialGamma_integrable
#print axioms ResidualSLT.radialGamma_integrable
#check @ResidualSLT.radialGamma_integral
#print axioms ResidualSLT.radialGamma_integral
#check @ResidualSLT.powerWeighted_integrable
#print axioms ResidualSLT.powerWeighted_integrable
#check @ResidualSLT.radialGamma_interval_le
#print axioms ResidualSLT.radialGamma_interval_le
#check @ResidualSLT.gaussian_interval_le
#print axioms ResidualSLT.gaussian_interval_le
#check @ResidualSLT.powerWeightedBox_upper_lt
#print axioms ResidualSLT.powerWeightedBox_upper_lt
#check @ResidualSLT.powerWeightedBox_upper_gt
#print axioms ResidualSLT.powerWeightedBox_upper_gt
#check @ResidualSLT.integral_radial_nat_power
#print axioms ResidualSLT.integral_radial_nat_power
#check @ResidualSLT.powerWeightedBox_inner_lower
#print axioms ResidualSLT.powerWeightedBox_inner_lower
#check @ResidualSLT.powerWeightedBox_lower
#print axioms ResidualSLT.powerWeightedBox_lower
#check @ResidualSLT.coneLaplaceExponent_of_le
#print axioms ResidualSLT.coneLaplaceExponent_of_le
#check @ResidualSLT.coneLaplaceExponent_of_ge
#print axioms ResidualSLT.coneLaplaceExponent_of_ge
#check @ResidualSLT.powerWeightedBox_has_order
#print axioms ResidualSLT.powerWeightedBox_has_order
#check @ResidualSLT.powerWeightedSymmetric
#print axioms ResidualSLT.powerWeightedSymmetric
#check @ResidualSLT.powerWeightedSymmetric_eq
#print axioms ResidualSLT.powerWeightedSymmetric_eq
#check @ResidualSLT.powerWeightedSymmetric_has_order
#print axioms ResidualSLT.powerWeightedSymmetric_has_order
#check @ResidualSLT.radialGamma_laplace_upper
#print axioms ResidualSLT.radialGamma_laplace_upper
#check @ResidualSLT.power_laplace_order_of_comparable
#print axioms ResidualSLT.power_laplace_order_of_comparable
#check @ResidualSLT.power_laplace_order_withDensity
#print axioms ResidualSLT.power_laplace_order_withDensity
#check @ResidualSLT.powerAngularKernel
#print axioms ResidualSLT.powerAngularKernel
#check @ResidualSLT.powerAngularKernel_nonneg
#print axioms ResidualSLT.powerAngularKernel_nonneg
#check @ResidualSLT.powerAngularKernel_integrable
#print axioms ResidualSLT.powerAngularKernel_integrable
#check @ResidualSLT.powerAngularCylinder_integrable
#print axioms ResidualSLT.powerAngularCylinder_integrable
#check @ResidualSLT.powerAngularCylinder_integral
#print axioms ResidualSLT.powerAngularCylinder_integral
#check @ResidualSLT.powerAngular_patch_upper
#print axioms ResidualSLT.powerAngular_patch_upper
#check @ResidualSLT.powerAngular_lower_of_zero
#print axioms ResidualSLT.powerAngular_lower_of_zero
#check @ResidualSLT.powerAngular_off_zero_upper
#print axioms ResidualSLT.powerAngular_off_zero_upper
#check @ResidualSLT.powerAngular_regular_upper
#print axioms ResidualSLT.powerAngular_regular_upper
#check @ResidualSLT.homogeneous_power_projective_bounds
#print axioms ResidualSLT.homogeneous_power_projective_bounds
#check @ResidualSLT.power_laplace_upper_of_projective_cones
#print axioms ResidualSLT.power_laplace_upper_of_projective_cones
#check @ResidualSLT.homogeneous_offcritical_laplace_order
#print axioms ResidualSLT.homogeneous_offcritical_laplace_order
#check @ResidualSLT.homogeneous_offcritical_spherical_laplace_order
#print axioms ResidualSLT.homogeneous_offcritical_spherical_laplace_order
#check @ResidualSLT.homogeneous_offcritical_prior_laplace_order
#print axioms ResidualSLT.homogeneous_offcritical_prior_laplace_order
#check @ResidualSLT.homogeneous_offcritical_prior_laplace_bounds
#print axioms ResidualSLT.homogeneous_offcritical_prior_laplace_bounds
#check @ResidualSLT.homogeneous_offcritical_prior_certificate
#print axioms ResidualSLT.homogeneous_offcritical_prior_certificate

#print ResidualSLT.HasPowerLaplaceOrder
#print ResidualSLT.PowerLaplaceLower
#print ResidualSLT.PowerLaplaceUpper
#print ResidualSLT.coneLaplaceExponent
#print ResidualSLT.homogeneousConeLoss
#print ResidualSLT.BoundedPositivePriorOn
