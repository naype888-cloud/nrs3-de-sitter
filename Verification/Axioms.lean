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

open NRSDeterminant

#print axioms robertson_pair
#print axioms robertson_axis
#print axioms omega_eq_blockDiagonal
#print axioms det_omega
#print axioms sigma_psiStar_eq_blockDiagonal
#print axioms det_sigma_psiStar
#print axioms det_sigma_psiStar_eq_det_omegaNRS
#print axioms det_omega_eq_det_sigma_psiStar
#print axioms det_omega_lt_det_sigma_psiStar
#print axioms det_sigma_psiStar_four
