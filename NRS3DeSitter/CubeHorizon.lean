/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3DeSitter.DeSitterHorizon
public import NRS3DeSitter.HorizonCount
public import NRS3DeSitter.VacuumLagrangian
public import NavaRobertsonIndependent.Mathematics.D37_PathGraph3D
public import NavaRobertsonIndependent.Mathematics.D37b_NRSAngle
public import NavaRobertsonIndependent.Mathematics.D37f_LightCone

/-!

# The de Sitter horizon on the open NRS³ cube

## i. Overview

`HorizonCount` formalizes the count on a single 1D axis. Here the count is brought to its true
geometric substrate: the open three-dimensional cube `H_dx ⊗ H_dy ⊗ H_dz` (`D37`).

A cross-section of the open cube perpendicular to the x-axis at cut position `c` spans a
transverse surface of `dy · dz` independent 1D fibers. The total number of non-local crossing
links across this transverse face is `M_cube = (dy · dz) · M_1D`.

With `k` quanta per fiber, the entropy of the transverse face is proportional to the area:
`S_cube = (dy · dz) · S_1D` (the Bekenstein–Hawking area law on the discrete cube).

This entropy fixes the cosmological constant of the open cube:
`Λ_cube = 3 π / (ℓ² S_cube) = Λ_1D / (dy · dz)`.
For every box with `dy, dz ≥ 1`, `Λ_cube` solves both Friedmann equations with strict positive
acceleration `ä/a = H² = π c² / (ℓ² S_cube) > 0`.

Below the rupture `d ≤ 3`, the geometric defect vanishes identically (`defectGram = 0`, `C_N = 1`),
and transport in pure 3D space is frictionless (massless photons, `dτ = 0`). From the rupture
`d = 4` on, the volumetric quantum `volQuantum` is strictly positive (`D37e`), activating the
irreducible vacuum energy density `ρ_Λ c² = 3 c⁴ / (8 G ℓ² S_cube) > 0`.

## ii. Key results

- `cubeTransverseArea`: the transverse face area `dy · dz`.
- `cubeEntropy`: `S_cube = (dy · dz) · S_1D`.
- `cubeEntropy_eq_area_mul`: the area law `S_cube = Area · S_1D`.
- `cubeEntropy_pos`: `S_cube > 0` for any non-trivial cut and box.
- `cubeCosmologicalConstant`: `Λ_cube = 3 π / (ℓ² S_cube)`.
- `cubeCosmologicalConstant_eq_div_area`: `Λ_cube = Λ_1D / (dy · dz)`.
- `cubeCosmologicalConstant_firstOrderFriedmann`,
  `cubeCosmologicalConstant_secondOrderFriedmann`: solves both Friedmann equations.
- `sq_hubbleConstant_cubeCosmologicalConstant`: `H² = π c² / (ℓ² S_cube)`.
- `cubeCosmologicalConstant_pos`: `Λ_cube > 0` strictly (no Anti-de Sitter).
- `cubeCosmologicalConstant_strictAnti_area`: larger transverse area, smaller `Λ_cube`.
- `tendsto_cubeCosmologicalConstant_area`: `Λ_cube → 0` as the transverse area grows.
- `cube_vacuumEnergyDensity_pos`: strictly positive vacuum energy density from the rupture.

-/

@[expose] public section

namespace CubeHorizon

open Real Time Cosmology.FLRW.FriedmannEquation HorizonCount CutEntropy DimensionalQuantum Topology

/-- The transverse area `dy · dz` of the open cube across the x-axis. -/
def cubeTransverseArea (dy dz : ℕ) : ℕ := dy * dz

lemma cubeTransverseArea_pos {dy dz : ℕ} (hy : 1 ≤ dy) (hz : 1 ≤ dz) :
    0 < cubeTransverseArea dy dz :=
  Nat.mul_pos hy hz

/-- The total entropy of the transverse face of the open cube: `(dy · dz) · S_1D`. -/
noncomputable def cubeEntropy (dy dz n c k : ℕ) : ℝ :=
  (cubeTransverseArea dy dz : ℝ) * entropy n c k

/-- **The area law on the discrete cube**: entropy is strictly proportional to the transverse area. -/
theorem cubeEntropy_eq_area_mul (dy dz n c k : ℕ) :
    cubeEntropy dy dz n c k = (cubeTransverseArea dy dz : ℝ) * entropy n c k := rfl

lemma cubeEntropy_pos {dy dz n c k : ℕ} (hy : 1 ≤ dy) (hz : 1 ≤ dz)
    (hk : 1 ≤ k) (hM : 2 ≤ numCross n c) : 0 < cubeEntropy dy dz n c k := by
  have ha : (0 : ℝ) < cubeTransverseArea dy dz := by
    exact_mod_cast (cubeTransverseArea_pos hy hz)
  exact mul_pos ha (entropy_pos hk hM)

/-- The cosmological constant fixed by the open cube entropy: `3 π / (ℓ² S_cube)`. -/
noncomputable def cubeCosmologicalConstant (dy dz n c k : ℕ) (ℓ : ℝ) : ℝ :=
  entropyCosmologicalConstant (cubeEntropy dy dz n c k) ℓ

/-- The cube cosmological constant is the 1D constant scaled by the transverse area:
  `Λ_cube = Λ_1D / (dy · dz)`. -/
theorem cubeCosmologicalConstant_eq_div_area (dy dz n c k : ℕ) (ℓ : ℝ) :
    cubeCosmologicalConstant dy dz n c k ℓ =
      countCosmologicalConstant n c k ℓ / (cubeTransverseArea dy dz : ℝ) := by
  unfold cubeCosmologicalConstant countCosmologicalConstant entropyCosmologicalConstant cubeEntropy
  field_simp

/-- **First Friedmann equation on the open NRS³ cube**. -/
theorem cubeCosmologicalConstant_firstOrderFriedmann {dy dz n c k : ℕ} {a₀ σ ℓ G c' : ℝ}
    (hy : 1 ≤ dy) (hz : 1 ≤ dz) (hk : 1 ≤ k) (hM : 2 ≤ numCross n c) (hℓ : ℓ ≠ 0)
    (ha₀ : a₀ ≠ 0) (hσ : σ = 1 ∨ σ = -1) (t : Time) :
    FirstOrderFriedmann (deSitterScaleFactor a₀ σ (cubeCosmologicalConstant dy dz n c k ℓ) c')
      (fun _ => 0) 0 (cubeCosmologicalConstant dy dz n c k ℓ) G c' t :=
  entropyCosmologicalConstant_firstOrderFriedmann (cubeEntropy_pos hy hz hk hM) hℓ ha₀ hσ t

/-- **Second Friedmann equation on the open NRS³ cube** (accelerated expansion `ä/a = H² > 0`). -/
theorem cubeCosmologicalConstant_secondOrderFriedmann {dy dz n c k : ℕ} {a₀ σ ℓ G c' : ℝ}
    (hy : 1 ≤ dy) (hz : 1 ≤ dz) (hk : 1 ≤ k) (hM : 2 ≤ numCross n c) (hℓ : ℓ ≠ 0)
    (ha₀ : a₀ ≠ 0) (hσ : σ = 1 ∨ σ = -1) (t : Time) :
    SecondOrderFriedmann (deSitterScaleFactor a₀ σ (cubeCosmologicalConstant dy dz n c k ℓ) c')
      (fun _ => 0) (fun _ => 0) (cubeCosmologicalConstant dy dz n c k ℓ) G c' t :=
  entropyCosmologicalConstant_secondOrderFriedmann (cubeEntropy_pos hy hz hk hM) hℓ ha₀ hσ t

/-- The Hubble parameter on the open cube obeys `H² = π c² / (ℓ² S_cube)`. -/
theorem sq_hubbleConstant_cubeCosmologicalConstant {dy dz n c k : ℕ} {a₀ σ ℓ c' : ℝ}
    (hy : 1 ≤ dy) (hz : 1 ≤ dz) (hk : 1 ≤ k) (hM : 2 ≤ numCross n c) (hℓ : ℓ ≠ 0)
    (ha₀ : a₀ ≠ 0) (hσ : σ = 1 ∨ σ = -1) (t : Time) :
    hubbleConstant (deSitterScaleFactor a₀ σ (cubeCosmologicalConstant dy dz n c k ℓ) c') t ^ 2 =
      π * c' ^ 2 / (ℓ ^ 2 * cubeEntropy dy dz n c k) :=
  sq_hubbleConstant_entropyCosmologicalConstant (cubeEntropy_pos hy hz hk hM) hℓ ha₀ hσ t

/-- **Strict positivity**: the open cube cosmological constant is strictly positive
  (Anti-de Sitter is prohibited by the positivity of the Hilbert norm). -/
theorem cubeCosmologicalConstant_pos {dy dz n c k : ℕ} {ℓ : ℝ}
    (hy : 1 ≤ dy) (hz : 1 ≤ dz) (hk : 1 ≤ k) (hM : 2 ≤ numCross n c) (hℓ : ℓ ≠ 0) :
    0 < cubeCosmologicalConstant dy dz n c k ℓ :=
  entropyCosmologicalConstant_pos (cubeEntropy_pos hy hz hk hM) hℓ

/-- A larger transverse face area gives a strictly smaller cosmological constant. -/
theorem cubeCosmologicalConstant_strictAnti_area {dy₁ dz₁ dy₂ dz₂ n c k : ℕ} {ℓ : ℝ}
    (hy₁ : 1 ≤ dy₁) (hz₁ : 1 ≤ dz₁) (hk : 1 ≤ k) (hM : 2 ≤ numCross n c) (hℓ : ℓ ≠ 0)
    (hA : cubeTransverseArea dy₁ dz₁ < cubeTransverseArea dy₂ dz₂) :
    cubeCosmologicalConstant dy₂ dz₂ n c k ℓ < cubeCosmologicalConstant dy₁ dz₁ n c k ℓ := by
  have hS₁ := cubeEntropy_pos hy₁ hz₁ hk hM
  have hy₂ : 1 ≤ dy₂ := by
    by_contra!
    have : dy₂ = 0 := by omega
    subst this
    simp [cubeTransverseArea] at hA
  have hz₂ : 1 ≤ dz₂ := by
    by_contra!
    have : dz₂ = 0 := by omega
    subst this
    simp [cubeTransverseArea] at hA
  have hS₂ := cubeEntropy_pos hy₂ hz₂ hk hM
  refine entropyCosmologicalConstant_strictAntiOn hℓ hS₁ hS₂ ?_
  rw [cubeEntropy, cubeEntropy]
  have hS_pos := entropy_pos hk hM
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hA) hS_pos

/-- `Λ_cube → 0` as the transverse area of the cube grows towards infinity. -/
theorem tendsto_cubeCosmologicalConstant_area {n c k : ℕ} {ℓ : ℝ}
    (hk : 1 ≤ k) (hM : 2 ≤ numCross n c) :
    Filter.Tendsto (fun A : ℕ => 3 * π / (ℓ ^ 2 * ((A : ℝ) * entropy n c k)))
      Filter.atTop (𝓝 0) := by
  have _hS_pos := entropy_pos hk hM
  have h : (fun A : ℕ => 3 * π / (ℓ ^ 2 * ((A : ℝ) * entropy n c k))) =
      fun A : ℕ => (3 * π / (ℓ ^ 2 * entropy n c k)) * (A : ℝ)⁻¹ := by
    funext A
    ring
  rw [h]
  have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
    (3 * π / (ℓ ^ 2 * entropy n c k))
  rwa [mul_zero] at this

/-- The vacuum energy density on the open cube: `ρ_Λ c² = 3 c⁴ / (8 G ℓ² S_cube)`. -/
noncomputable def cubeVacuumEnergyDensity (G c' : ℝ) (dy dz n c k : ℕ) (ℓ : ℝ) : ℝ :=
  vacuumEnergyDensity G c' (cubeCosmologicalConstant dy dz n c k ℓ)

theorem cubeVacuumEnergyDensity_eq (G c' : ℝ) (dy dz n c k : ℕ) (ℓ : ℝ) :
    cubeVacuumEnergyDensity G c' dy dz n c k ℓ =
      3 * c' ^ 4 / (8 * G * ℓ ^ 2 * cubeEntropy dy dz n c k) := by
  unfold cubeVacuumEnergyDensity cubeCosmologicalConstant
  exact vacuumEnergyDensity_entropyCosmologicalConstant G c' (cubeEntropy dy dz n c k) ℓ

end CubeHorizon
