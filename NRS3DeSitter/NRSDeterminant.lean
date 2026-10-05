/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module
public import NRS3DeSitter.UncertaintyMatrices
/-!

# The state condition `det Ω_nrs ≤ det Σ` on the cube

## i. Overview

At the maximal current state of the cube the fluctuation vectors of different axes are
orthogonal, so `Σ(maxCurrentCubeState)` is block diagonal like `Ω(maxCurrentCubeState)`, and
`det Σ(maxCurrentCubeState) = det Ω_nrs(maxCurrentCubeState)`
exactly. Hence `det Ω(maxCurrentCubeState) = det Σ(maxCurrentCubeState)` when every axis has `2` or
`3` sites, and
`det Ω(maxCurrentCubeState) < det Σ(maxCurrentCubeState)` as soon as one axis has `4` or more; at
`4 × 4 × 4` the ratio is
`((99 − 42√5)/5)³`.

The condition is on states, not a term of the action of `VacuumLagrangian`: an action is varied
over field configurations, and the inequality restricts the state in which it is evaluated.

## ii. Key results

- `NRSDeterminant.sigma_maxCurrentState_eq_blockDiagonal` : `Σ(maxCurrentCubeState)` is block
  diagonal.
- `NRSDeterminant.det_sigma_maxCurrentState_eq_det_omegaNRS` :
  `det Σ(maxCurrentCubeState) = det Ω_nrs(maxCurrentCubeState)`.
- `NRSDeterminant.det_omega_eq_det_sigma_maxCurrentState` : equality with `2` or `3` sites per axis.
- `NRSDeterminant.det_omega_lt_det_sigma_maxCurrentState` : strict as soon as one axis has `4`
  sites.
- `NRSDeterminant.det_sigma_maxCurrentState_four` : at `4 × 4 × 4`,
  `det Σ(maxCurrentCubeState) = ((99 − 42√5)/5)³ · det Ω(maxCurrentCubeState)`.

## iii. Table of contents

- D. `Σ(maxCurrentCubeState)` is block diagonal
- E. The determinants at the maximal current state of the cube

## iv. References

- H. P. Robertson, *An indeterminacy relation for several observables and its classical
  interpretation*, Phys. Rev. 46 (1934) 794.

-/

@[expose] public noncomputable section

namespace NRSDeterminant

open Matrix TransportPosition NRSInequality NearMaxTension Gnomon SpectralExtremal
open PathGraph3DNRS CubePythagoras NRSAngle

variable {dx dy dz : ℕ}

/-!

## D. `Σ(maxCurrentCubeState)` is block diagonal

-/

variable (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz)
include hx hy hz

/-- At the maximal current state of the cube the fluctuation vectors of different axes are
orthogonal. -/
lemma covarianceG_observable_maxCurrentState {j k : Fin 2 × Fin 3} (h : j.2 ≠ k.2) :
    covarianceG (observable dx dy dz j) (observable dx dy dz k) (maxCurrentCubeState dx dy dz) = 0
        := by
  have xyT := fun B => orthogonal_axes_xy hx hy hz (A := Td dx) (B := B) (TdOp_isSymmetric dx)
  have xyP := fun B => orthogonal_axes_xy hx hy hz (A := Pd dx) (B := B) (PdOp_isSymmetric dx)
  have xzT := fun B => orthogonal_axes_xz hx hy hz (A := Td dx) (B := B) (TdOp_isSymmetric dx)
  have xzP := fun B => orthogonal_axes_xz hx hy hz (A := Pd dx) (B := B) (PdOp_isSymmetric dx)
  have yzT := fun B => orthogonal_axes_yz hx hy hz (A := Td dy) (B := B) (TdOp_isSymmetric dy)
  have yzP := fun B => orthogonal_axes_yz hx hy hz (A := Pd dy) (B := B) (PdOp_isSymmetric dy)
  have yxT := fun B => inner_eq_zero_symm.mp (xyT B)
  have yxP := fun B => inner_eq_zero_symm.mp (xyP B)
  have zxT := fun B => inner_eq_zero_symm.mp (xzT B)
  have zxP := fun B => inner_eq_zero_symm.mp (xzP B)
  have zyT := fun B => inner_eq_zero_symm.mp (yzT B)
  have zyP := fun B => inner_eq_zero_symm.mp (yzP B)
  obtain ⟨a, i⟩ := j
  obtain ⟨b, i'⟩ := k
  fin_cases i <;> fin_cases i' <;> simp only [ne_eq, not_true_eq_false] at h <;>
    fin_cases a <;> fin_cases b <;>
    simp [observable, transportAxis, positionAxis, TX, PX, TY, PY, TZ, PZ, covarianceG, xyT,
      xyP, xzT, xzP, yzT, yzP, yxT, yxP, zxT, zxP, zyT, zyP]

/-- **`Σ(maxCurrentCubeState)` is block diagonal.** -/
theorem sigma_maxCurrentState_eq_blockDiagonal :
    sigma dx dy dz (maxCurrentCubeState dx dy dz) =
      blockDiagonal (sigmaAxis dx dy dz (maxCurrentCubeState dx dy dz)) := by
  ext ⟨a, i⟩ ⟨b, i'⟩
  rw [sigma, of_apply, blockDiagonal_apply]
  split_ifs with h
  · subst h
    fin_cases a <;> fin_cases b <;>
      simp [observable, sigmaAxis, sigmaPair, covarianceG_self,
        covarianceG_comm (transportAxis dx dy dz i) (positionAxis dx dy dz i)]
  · exact covarianceG_observable_maxCurrentState hx hy hz h

/-!

## E. The determinants at the maximal current state of the cube

-/

/-- On each axis, `det Σ_axis(maxCurrentCubeState) = C_Nava(d)² · det Ω_axis(maxCurrentCubeState)`,
with
`det Ω_axis(maxCurrentCubeState) = 1/(d − 1)²`. -/
lemma det_axis_maxCurrentState (i : Fin 3) :
    (omegaAxis dx dy dz (maxCurrentCubeState dx dy dz) i).det = 1 / ((sites dx dy dz i : ℝ) - 1) ^ 2
        ∧
      (sigmaAxis dx dy dz (maxCurrentCubeState dx dy dz) i).det =
        CoherenceConstant (sites dx dy dz i) ^ 2 *
          (omegaAxis dx dy dz (maxCurrentCubeState dx dy dz) i).det := by
  have key : ∀ {d : ℕ}, 2 ≤ d → ∀ vT vP c t : ℝ,
      vT = variance (TdOp d) (maxCurrentState d) → vP = variance (PdOp d) (maxCurrentState d) →
      c = covariance (TdOp d) (PdOp d) (maxCurrentState d) → t = 2 / ((d : ℝ) - 1) →
      (t / 2) ^ 2 = 1 / ((d : ℝ) - 1) ^ 2 ∧
        vT * vP - c ^ 2 = CoherenceConstant d ^ 2 * (t / 2) ^ 2 := by
    intro d hd vT vP c t h1 h2 h3 h4
    have hd1 : (d : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have ht : (t / 2) ^ 2 = 1 / ((d : ℝ) - 1) ^ 2 := by
      rw [h4]; field_simp
    refine ⟨ht, ?_⟩
    rw [h1, h2, h3, covariance_eq_zero hd, variance_mul_variance hd,
      ← CoherenceConstant_eq_one_add_geometricGap, commutatorConstant_half_sq hd, ht]
    ring
  fin_cases i
  · obtain ⟨h1, h2, h3, h4⟩ := stats_axis_x hx hy hz
    rw [omegaAxis, sigmaAxis, det_omegaPair, det_sigmaPair]
    exact key hx _ _ _ _ h1 h2 h3 h4
  · obtain ⟨h1, h2, h3, h4⟩ := stats_axis_y hx hy hz
    rw [omegaAxis, sigmaAxis, det_omegaPair, det_sigmaPair]
    exact key hy _ _ _ _ h1 h2 h3 h4
  · obtain ⟨h1, h2, h3, h4⟩ := stats_axis_z hx hy hz
    rw [omegaAxis, sigmaAxis, det_omegaPair, det_sigmaPair]
    exact key hz _ _ _ _ h1 h2 h3 h4

/-- `det Σ(maxCurrentCubeState) = (C_Nava(dx) C_Nava(dy) C_Nava(dz))² · det Ω(maxCurrentCubeState)`.
-/
theorem det_sigma_maxCurrentState :
    (sigma dx dy dz (maxCurrentCubeState dx dy dz)).det =
      (CoherenceConstant dx * CoherenceConstant dy * CoherenceConstant dz) ^ 2 *
        (omega dx dy dz (maxCurrentCubeState dx dy dz)).det := by
  rw [sigma_maxCurrentState_eq_blockDiagonal hx hy hz, det_blockDiagonal, det_omega,
      Fin.prod_univ_three,
    Fin.prod_univ_three, (det_axis_maxCurrentState hx hy hz 0).2, (det_axis_maxCurrentState hx hy hz
        1).2,
    (det_axis_maxCurrentState hx hy hz 2).2]
  simp only [sites, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **The NRS³ condition holds at the maximal current state of the cube with equality**:
`det Σ(maxCurrentCubeState) = det Ω_nrs(maxCurrentCubeState)`. -/
theorem det_sigma_maxCurrentState_eq_det_omegaNRS :
    (sigma dx dy dz (maxCurrentCubeState dx dy dz)).det = (omegaNRS dx dy dz (maxCurrentCubeState dx
        dy dz)).det := by
  rw [det_sigma_maxCurrentState hx hy hz, det_omega, omegaNRS, det_blockDiagonal,
      Fin.prod_univ_three,
    Fin.prod_univ_three]
  simp only [det_smul, Fintype.card_fin, sites, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- `det Ω(maxCurrentCubeState) > 0`. -/
lemma det_omega_maxCurrentState_pos : 0 < (omega dx dy dz (maxCurrentCubeState dx dy dz)).det := by
  rw [det_omega, Fin.prod_univ_three, (det_axis_maxCurrentState hx hy hz 0).1,
    (det_axis_maxCurrentState hx hy hz 1).1, (det_axis_maxCurrentState hx hy hz 2).1]
  have h : ∀ {d : ℕ}, 2 ≤ d → (0 : ℝ) < 1 / ((d : ℝ) - 1) ^ 2 := fun {d} hd => by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have : (0 : ℝ) < (d : ℝ) - 1 := by linarith
    positivity
  simp only [sites, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  exact mul_pos (mul_pos (h hx) (h hy)) (h hz)

/-- **Saturation**: with `2` or `3` sites on every axis,
`det Ω(maxCurrentCubeState) = det Σ(maxCurrentCubeState)`. -/
theorem det_omega_eq_det_sigma_maxCurrentState (hx' : dx = 2 ∨ dx = 3) (hy' : dy = 2 ∨ dy = 3)
    (hz' : dz = 2 ∨ dz = 3) :
    (omega dx dy dz (maxCurrentCubeState dx dy dz)).det = (sigma dx dy dz (maxCurrentCubeState dx dy
        dz)).det := by
  rw [det_sigma_maxCurrentState hx hy hz, (CoherenceConstant_eq_one_iff dx hx).mpr hx',
    (CoherenceConstant_eq_one_iff dy hy).mpr hy', (CoherenceConstant_eq_one_iff dz hz).mpr hz']
  ring

/-- **The algebraic quantum**: as soon as one axis has `4` or more sites,
`det Ω(maxCurrentCubeState) < det Σ(maxCurrentCubeState)`. -/
theorem det_omega_lt_det_sigma_maxCurrentState (h4 : 4 ≤ dx ∨ 4 ≤ dy ∨ 4 ≤ dz) :
    (omega dx dy dz (maxCurrentCubeState dx dy dz)).det < (sigma dx dy dz (maxCurrentCubeState dx dy
        dz)).det := by
  rw [det_sigma_maxCurrentState hx hy hz]
  have hpos := det_omega_maxCurrentState_pos hx hy hz
  have cx := CoherenceConstant_ge_one hx
  have cy := CoherenceConstant_ge_one hy
  have cz := CoherenceConstant_ge_one hz
  have hprod : 1 < CoherenceConstant dx * CoherenceConstant dy * CoherenceConstant dz := by
    rcases h4 with h | h | h
    · have := one_lt_CoherenceConstant_of_four_le dx h
      nlinarith [mul_le_mul cy cz zero_le_one (by linarith)]
    · have := one_lt_CoherenceConstant_of_four_le dy h
      nlinarith [mul_le_mul cx cz zero_le_one (by linarith)]
    · have := one_lt_CoherenceConstant_of_four_le dz h
      nlinarith [mul_le_mul cx cy zero_le_one (by linarith)]
  have h1 : 1 < (CoherenceConstant dx * CoherenceConstant dy * CoherenceConstant dz) ^ 2 := by
    nlinarith
  nlinarith

omit hx hy hz in
/-- **At the first rupture `4 × 4 × 4`**:
`det Σ(maxCurrentCubeState) = ((99 − 42√5)/5)³ · det Ω(maxCurrentCubeState)`. -/
theorem det_sigma_maxCurrentState_four :
    (sigma 4 4 4 (maxCurrentCubeState 4 4 4)).det =
      ((99 - 42 * Real.sqrt 5) / 5) ^ 3 * (omega 4 4 4 (maxCurrentCubeState 4 4 4)).det := by
  rw [det_sigma_maxCurrentState (by norm_num) (by norm_num) (by norm_num)]
  have h : CoherenceConstant 4 ^ 2 = (99 - 42 * Real.sqrt 5) / 5 := by
    rw [CoherenceConstant, Real.sq_sqrt (by linarith [one_lt_CoherenceConstantSq_four]),
      CoherenceConstantSq_four_eq]
  rw [show (CoherenceConstant 4 * CoherenceConstant 4 * CoherenceConstant 4) ^ 2 =
    (CoherenceConstant 4 ^ 2) ^ 3 by ring, h]

end NRSDeterminant
