/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3DeSitter.DeSitterHorizon
/-!

# The vacuum term of the gravitational Lagrangian

## i. Overview

The gravitational Lagrangian density with a cosmological constant is
`c⁴ / (16 π G) (R - 2 Λ)`, with `R` the scalar curvature. Its value at `R = 0` is minus the vacuum
energy density `ρ_Λ c² = Λ c⁴ / (8 π G)`.

With the cosmological constant `Λ = 3 π / (ℓ² S)` fixed by the entropy `S` of a de Sitter horizon,
the vacuum term reads `R - 6 π / (ℓ² S)`: only the vacuum term carries `S`, the coefficient
`c⁴ / (16 π G)` of `R` is unchanged. The vacuum energy density becomes
`3 c⁴ / (8 G ℓ² S)`, strictly decreasing in `S`.

These are pointwise statements about the density. The action integral and the curvature of the
metric are not formalized here.

## ii. Key results

- `einsteinHilbertLambdaDensity`: `c⁴ / (16 π G) (R - 2 Λ)`.
- `vacuumEnergyDensity`: `Λ c⁴ / (8 π G)`.
- `einsteinHilbertLambdaDensity_zero`: the density at `R = 0` is `-ρ_Λ c²`.
- `einsteinHilbertLambdaDensity_entropyCosmologicalConstant`: the vacuum term is
  `R - 6 π / (ℓ² S)`.
- `vacuumEnergyDensity_entropyCosmologicalConstant`: `ρ_Λ c² = 3 c⁴ / (8 G ℓ² S)`.
- `vacuumEnergyDensity_entropyCosmologicalConstant_strictAntiOn`: it is strictly decreasing
  in `S`.

## iii. Table of contents

- A. The density and the vacuum energy
- B. The vacuum term fixed by the entropy

## iv. References

- A. Einstein, *Kosmologische Betrachtungen zur allgemeinen Relativitätstheorie*,
  Sitzungsber. Preuss. Akad. Wiss. (1917) 142.

-/

@[expose] public section

namespace Cosmology.FLRW.FriedmannEquation

open Real

/-!

## A. The density and the vacuum energy

-/

/-- The gravitational Lagrangian density `c⁴ / (16 π G) (R - 2 Λ)` at scalar curvature `R`. -/
noncomputable def einsteinHilbertLambdaDensity (G c Λ R : ℝ) : ℝ :=
  c ^ 4 / (16 * π * G) * (R - 2 * Λ)

/-- The vacuum energy density `ρ_Λ c² = Λ c⁴ / (8 π G)` of the cosmological constant. -/
noncomputable def vacuumEnergyDensity (G c Λ : ℝ) : ℝ := Λ * c ^ 4 / (8 * π * G)

/-- At zero curvature the density is minus the vacuum energy density. -/
lemma einsteinHilbertLambdaDensity_zero (G c Λ : ℝ) :
    einsteinHilbertLambdaDensity G c Λ 0 = -vacuumEnergyDensity G c Λ := by
  unfold einsteinHilbertLambdaDensity vacuumEnergyDensity
  ring

/-!

## B. The vacuum term fixed by the entropy

-/

/-- With `Λ = 3 π / (ℓ² S)` the vacuum term is `R - 6 π / (ℓ² S)`; the coefficient of `R` does
  not depend on `S`. -/
lemma einsteinHilbertLambdaDensity_entropyCosmologicalConstant (G c S ℓ R : ℝ) :
    einsteinHilbertLambdaDensity G c (entropyCosmologicalConstant S ℓ) R =
      c ^ 4 / (16 * π * G) * (R - 6 * π / (ℓ ^ 2 * S)) := by
  unfold einsteinHilbertLambdaDensity entropyCosmologicalConstant
  ring

/-- The vacuum energy density of a de Sitter horizon of entropy `S` is `3 c⁴ / (8 G ℓ² S)`. -/
lemma vacuumEnergyDensity_entropyCosmologicalConstant (G c S ℓ : ℝ) :
    vacuumEnergyDensity G c (entropyCosmologicalConstant S ℓ) =
      3 * c ^ 4 / (8 * G * ℓ ^ 2 * S) := by
  unfold vacuumEnergyDensity entropyCosmologicalConstant
  field_simp

/-- The vacuum energy density of a de Sitter horizon is strictly decreasing in its entropy. -/
lemma vacuumEnergyDensity_entropyCosmologicalConstant_strictAntiOn {G c ℓ : ℝ} (hG : 0 < G)
    (hc : c ≠ 0) (hℓ : ℓ ≠ 0) :
    StrictAntiOn (fun S => vacuumEnergyDensity G c (entropyCosmologicalConstant S ℓ))
      (Set.Ioi 0) := by
  intro S₁ hS₁ S₂ _ h
  have hS₁ : (0 : ℝ) < S₁ := hS₁
  simp only [vacuumEnergyDensity_entropyCosmologicalConstant]
  gcongr

end Cosmology.FLRW.FriedmannEquation
