import NRS3DeSitter

/-! Only `propext`, `Classical.choice` and `Quot.sound` are expected. -/

open Cosmology.FLRW.FriedmannEquation

#print axioms deSitterHorizonArea_eq
#print axioms deSitterHorizonRadius_eq_div_abs_hubbleConstant
#print axioms deSitterEntropy_eq
#print axioms deSitterEntropy_pos
#print axioms cosmologicalConstant_eq_of_deSitterEntropy
#print axioms deSitterEntropy_entropyCosmologicalConstant
#print axioms entropyCosmologicalConstant_firstOrderFriedmann
#print axioms entropyCosmologicalConstant_secondOrderFriedmann
#print axioms sq_hubbleConstant_entropyCosmologicalConstant
#print axioms entropyCosmologicalConstant_strictAntiOn
#print axioms einsteinHilbertLambdaDensity_zero
#print axioms einsteinHilbertLambdaDensity_entropyCosmologicalConstant
#print axioms vacuumEnergyDensity_entropyCosmologicalConstant
#print axioms vacuumEnergyDensity_entropyCosmologicalConstant_strictAntiOn

open StateCondition

#print axioms floor_eq
#print axioms det_eq_of_two_three
#print axioms floor_lt_det_of_four_le
#print axioms det_four

open HorizonCount

#print axioms numCross_eq
#print axioms numCross_centre
#print axioms blind_below_rupture
#print axioms quantumDefect_pos
#print axioms quantumDefect_lt_defect
#print axioms entropy_eq_mul_quantumDefect
#print axioms countCosmologicalConstant_eq
#print axioms deSitterEntropy_countCosmologicalConstant
#print axioms countCosmologicalConstant_firstOrderFriedmann
#print axioms countCosmologicalConstant_secondOrderFriedmann
#print axioms countCosmologicalConstant_strictAnti
#print axioms lower_bound_simpleCountCosmologicalConstant
#print axioms lower_bound_centre
#print axioms countCosmologicalConstant_pos
#print axioms tendsto_countCosmologicalConstant
