/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D37b_NRSAngle
public import NavaRobertsonIndependent.Mathematics.D49c_RobertsonDeterminantProduct
/-!

# The condition on the state: det|NRS³ at the maximal current state of the cube

## i. Overview

The uncertainty condition is not a term of the action: it restricts the state in which the
action is evaluated. On the cube `H_dx ⊗ H_dy ⊗ H_dz`, `Σ` is the `6 × 6` covariance matrix of
`(T_x, P_x, T_y, P_y, T_z, P_z)`. Robertson's 1934 relation `|det Ω| ≤ det Σ` holds for every
state (`D49`, `D49b`), with floor `((t_x t_y t_z) / 8)²` on the cube, and at the maximal current
state of the cube `det Σ = (C_Nava(dx) C_Nava(dy) C_Nava(dz))² · floor` (`D49c`). All of this is
in the base repository; here it is read for de Sitter.

At the maximal current state the floor is `1 / ((dx − 1)(dy − 1)(dz − 1))²`. The relation is an
equality when every axis has `2` or `3` positions, strict as soon as one axis has `4` or more,
and at `4 × 4 × 4` the ratio is `((99 − 42√5) / 5)³ ≈ 1.0520`.

## ii. Key results

- `floor_eq` : the floor is `1 / ((dx − 1)(dy − 1)(dz − 1))²`.
- `det_eq_of_two_three` : equality when every axis has `2` or `3` positions.
- `floor_lt_det_of_four_le` : strict as soon as one axis has `4` or more.
- `det_four` : `det Σ = ((99 − 42√5) / 5)³ · floor` at `4 × 4 × 4`.

## iii. Table of contents

- A. The floor at the maximal current state
- B. Equality and strictness

## iv. References

- H. P. Robertson, *An indeterminacy relation for several observables and its classical
  interpretation*, Phys. Rev. 46 (1934) 794.

-/

@[expose] public section

namespace StateCondition

open Matrix TransportPosition PathGraph3DNRS RobertsonDeterminant RobertsonDeterminant3D
open RobertsonDeterminantProduct Gnomon NRSAngle

variable {dx dy dz : ℕ}

/-- The Robertson floor `((t_x t_y t_z) / 8)²` at the maximal current state of the cube. -/
noncomputable def floor (dx dy dz : ℕ) : ℝ :=
  ((tensionG (TX dx dy dz) (PX dx dy dz) (maxCurrentCubeState dx dy dz) *
      tensionG (TY dx dy dz) (PY dx dy dz) (maxCurrentCubeState dx dy dz) *
        tensionG (TZ dx dy dz) (PZ dx dy dz) (maxCurrentCubeState dx dy dz)) / 8) ^ 2

/-- The covariance determinant `det Σ` at the maximal current state of the cube. -/
noncomputable def detSigma (dx dy dz : ℕ) : ℝ :=
  (covMatrix (pairs dx dy dz) (maxCurrentCubeState dx dy dz)).det

/-!

## A. The floor at the maximal current state

-/

/-- **The floor** at the maximal current state is `1 / ((dx − 1)(dy − 1)(dz − 1))²`. -/
theorem floor_eq (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    floor dx dy dz = 1 / (((dx : ℝ) - 1) * ((dy : ℝ) - 1) * ((dz : ℝ) - 1)) ^ 2 := by
  have ex : (1 : ℝ) ≤ (dx : ℝ) - 1 := by
    have : (2 : ℝ) ≤ dx := by exact_mod_cast hx
    linarith
  have ey : (1 : ℝ) ≤ (dy : ℝ) - 1 := by
    have : (2 : ℝ) ≤ dy := by exact_mod_cast hy
    linarith
  have ez : (1 : ℝ) ≤ (dz : ℝ) - 1 := by
    have : (2 : ℝ) ≤ dz := by exact_mod_cast hz
    linarith
  rw [floor, (stats_axis_x hx hy hz).2.2.2, (stats_axis_y hx hy hz).2.2.2,
    (stats_axis_z hx hy hz).2.2.2]
  field_simp
  ring

lemma floor_pos (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) : 0 < floor dx dy dz := by
  rw [floor_eq hx hy hz]
  have ex : (0 : ℝ) < (dx : ℝ) - 1 := by
    have : (2 : ℝ) ≤ dx := by exact_mod_cast hx
    linarith
  have ey : (0 : ℝ) < (dy : ℝ) - 1 := by
    have : (2 : ℝ) ≤ dy := by exact_mod_cast hy
    linarith
  have ez : (0 : ℝ) < (dz : ℝ) - 1 := by
    have : (2 : ℝ) ≤ dz := by exact_mod_cast hz
    linarith
  positivity

/-- `det Σ = (C_Nava(dx) C_Nava(dy) C_Nava(dz))² · floor` (`D49c`). -/
lemma detSigma_eq (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) :
    detSigma dx dy dz =
      (CoherenceConstant dx * CoherenceConstant dy * CoherenceConstant dz) ^ 2 * floor dx dy dz :=
  det_covMatrix_maxCurrentCubeState hx hy hz

/-!

## B. Equality and strictness

-/

/-- **Equality** when every axis has `2` or `3` positions. -/
theorem det_eq_of_two_three (hx : dx = 2 ∨ dx = 3) (hy : dy = 2 ∨ dy = 3)
    (hz : dz = 2 ∨ dz = 3) : detSigma dx dy dz = floor dx dy dz := by
  have h2 : ∀ {d : ℕ}, d = 2 ∨ d = 3 → 2 ≤ d := by omega
  rw [detSigma_eq (h2 hx) (h2 hy) (h2 hz), (CoherenceConstant_eq_one_iff dx (h2 hx)).mpr hx,
    (CoherenceConstant_eq_one_iff dy (h2 hy)).mpr hy,
    (CoherenceConstant_eq_one_iff dz (h2 hz)).mpr hz]
  ring

/-- **Strict as soon as one axis has `4` or more positions.** -/
theorem floor_lt_det_of_four_le (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz)
    (h4 : 4 ≤ dx ∨ 4 ≤ dy ∨ 4 ≤ dz) : floor dx dy dz < detSigma dx dy dz := by
  have cx := CoherenceConstant_ge_one hx
  have cy := CoherenceConstant_ge_one hy
  have cz := CoherenceConstant_ge_one hz
  have hP : 1 < CoherenceConstant dx * CoherenceConstant dy * CoherenceConstant dz := by
    rcases h4 with h | h | h
    · have := one_lt_CoherenceConstant_of_four_le dx h
      nlinarith [mul_le_mul cy cz zero_le_one (by linarith)]
    · have := one_lt_CoherenceConstant_of_four_le dy h
      nlinarith [mul_le_mul cx cz zero_le_one (by linarith)]
    · have := one_lt_CoherenceConstant_of_four_le dz h
      nlinarith [mul_le_mul cx cy zero_le_one (by linarith)]
  rw [detSigma_eq hx hy hz]
  have hf := floor_pos hx hy hz
  have hP2 : 1 < (CoherenceConstant dx * CoherenceConstant dy * CoherenceConstant dz) ^ 2 := by
    nlinarith
  nlinarith

/-- **At the first rupture `4 × 4 × 4`**: `det Σ = ((99 − 42√5) / 5)³ · floor`. -/
theorem det_four : detSigma 4 4 4 = ((99 - 42 * √5) / 5) ^ 3 * floor 4 4 4 := by
  have hC : CoherenceConstant 4 ^ 2 = (99 - 42 * √5) / 5 := by
    rw [CoherenceConstant, Real.sq_sqrt (by linarith [one_lt_CoherenceConstantSq_four]),
      CoherenceConstantSq_four_eq]
  rw [detSigma_eq (by norm_num) (by norm_num) (by norm_num), mul_pow, mul_pow, hC]
  ring

end StateCondition
