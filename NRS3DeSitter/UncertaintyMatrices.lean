/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module
public import NavaRobertsonIndependent.Mathematics.D37d_CubePythagoras
/-!

# Covariance and commutator matrices on the cube

## i. Overview

On the cube `H_dx ⊗ H_dy ⊗ H_dz` each axis carries the pair `(T, P)`. For a state `Ψ` the
covariance matrix `Σ(Ψ)` of the six observables `(T_x, P_x, T_y, P_y, T_z, P_z)` has entries
`Re ⟪(A − ⟨A⟩)Ψ, (B − ⟨B⟩)Ψ⟫`, and the commutator matrix `Ω(Ψ)` has entries `½ ⟨i[A, B]⟩`.

Pairs on different axes commute, so `Ω(Ψ)` is block diagonal at every state, one `2 × 2` block
per axis. On each axis Robertson–Schrödinger is `det Ω_axis ≤ det Σ_axis`, at every state.
The NRS matrix `Ω_nrs` multiplies the block of each axis by `C_Nava(d_axis)`.

## ii. Key results

- `NRSDeterminant.robertson_pair` : `det Ω ≤ det Σ` for a pair of symmetric operators.
- `NRSDeterminant.robertson_axis` : `det Ω_axis(Ψ) ≤ det Σ_axis(Ψ)` for every state and axis.
- `NRSDeterminant.omega_eq_blockDiagonal` : `Ω(Ψ)` is block diagonal at every state.
- `NRSDeterminant.omegaNRS` : the NRS commutator matrix.

## iii. Table of contents

- A. The `2 × 2` matrices of a pair and Robertson–Schrödinger
- B. The six observables of the cube
- C. `Ω` is block diagonal

## iv. References

- H. P. Robertson, *An indeterminacy relation for several observables and its classical
  interpretation*, Phys. Rev. 46 (1934) 794.
- E. Schrödinger, *Zum Heisenbergschen Unschärfeprinzip*, Sitzungsber. Preuss. Akad. Wiss.
  (1930) 296.

-/

@[expose] public noncomputable section

namespace NRSDeterminant

open Matrix TransportPosition NRSInequality NearMaxTension Gnomon SpectralExtremal
open PathGraph3DNRS CubePythagoras NRSAngle

/-!

## A. The `2 × 2` matrices of a pair and Robertson–Schrödinger

-/

section Pair

variable {ι : Type*} [Fintype ι] (L M : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
  (Ψ : EuclideanSpace ℂ ι)

/-- The covariance matrix of the pair `(L, M)` at `Ψ`. -/
def sigmaPair : Matrix (Fin 2) (Fin 2) ℝ :=
  !![varianceG L Ψ, covarianceG L M Ψ; covarianceG L M Ψ, varianceG M Ψ]

/-- The commutator matrix of the pair `(L, M)` at `Ψ`: `½ ⟨i[L, M]⟩` off the diagonal. -/
def omegaPair : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, tensionG L M Ψ / 2; -(tensionG L M Ψ / 2), 0]

lemma det_sigmaPair :
    (sigmaPair L M Ψ).det = varianceG L Ψ * varianceG M Ψ - covarianceG L M Ψ ^ 2 := by
  rw [sigmaPair, det_fin_two_of]
  ring

lemma det_omegaPair : (omegaPair L M Ψ).det = (tensionG L M Ψ / 2) ^ 2 := by
  rw [omegaPair, det_fin_two_of]
  ring

lemma covarianceG_self : covarianceG L L Ψ = varianceG L Ψ := by
  rw [covarianceG, varianceG, inner_self_eq_norm_sq_to_K]
  norm_cast

lemma covarianceG_comm : covarianceG M L Ψ = covarianceG L M Ψ := by
  rw [covarianceG, covarianceG, ← inner_conj_symm, Complex.conj_re]

lemma opCommutator_comm : opCommutator M L = -opCommutator L M := by
  simp only [opCommutator, neg_sub]

lemma tensionG_self : tensionG L L Ψ = 0 := by
  simp [tensionG, observableTension, opCommutator]

lemma tensionG_swap : tensionG M L Ψ = -tensionG L M Ψ := by
  simp only [tensionG, observableTension, opCommutator, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.comp_apply]
  rw [← neg_sub, smul_neg, inner_neg_right, Complex.neg_re]

lemma tensionG_eq_zero_of_opCommutator (h : opCommutator L M = 0) : tensionG L M Ψ = 0 := by
  simp [tensionG, observableTension, h]

variable {L M}

/-- For symmetric `L`, `M` the tension is `−2 Im ⟪(L − ⟨L⟩)Ψ, (M − ⟨M⟩)Ψ⟫`. -/
lemma tensionG_eq_neg_two_im (hL : L.IsSymmetric) (hM : M.IsSymmetric) :
    tensionG L M Ψ = -2 * (inner ℂ (centeredG L Ψ) (centeredG M Ψ)).im := by
  have hLΨ : (inner ℂ (L Ψ) Ψ).im = 0 := by
    rw [← hL.coe_re_inner_apply_self Ψ]; simp
  have hMΨ : (inner ℂ Ψ (M Ψ)).im = 0 := by
    rw [← hM Ψ Ψ, ← hM.coe_re_inner_apply_self Ψ]; simp
  have hΨ : (inner ℂ Ψ Ψ).im = 0 := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  simp only [tensionG, observableTension, opCommutator, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, inner_smul_right, inner_sub_right]
  rw [← hL Ψ (M Ψ), ← hM Ψ (L Ψ), ← inner_conj_symm (M Ψ) (L Ψ)]
  simp only [centeredG, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, hLΨ,
    hMΨ, hΨ]
  ring

/-- **Robertson–Schrödinger on a pair.** For symmetric `L`, `M`, at every state,
`det Ω ≤ det Σ`: `(½ ⟨i[L, M]⟩)² ≤ Var L · Var M − Cov(L, M)²`. -/
theorem robertson_pair (hL : L.IsSymmetric) (hM : M.IsSymmetric) :
    (omegaPair L M Ψ).det ≤ (sigmaPair L M Ψ).det := by
  set z := inner ℂ (centeredG L Ψ) (centeredG M Ψ)
  have hcs : ‖z‖ ≤ ‖centeredG L Ψ‖ * ‖centeredG M Ψ‖ := norm_inner_le_norm _ _
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h2 := pow_le_pow_left₀ (norm_nonneg z) hcs 2
  rw [det_omegaPair, det_sigmaPair, tensionG_eq_neg_two_im Ψ hL hM, varianceG, varianceG,
    covarianceG]
  nlinarith [h2, hz]

end Pair

/-!

## B. The six observables of the cube

-/

section Lift

variable {ι α β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]

/-- A hermitian matrix of one axis, lifted to the product, is symmetric. -/
lemma isSymmetric_liftAlong (e : ι ≃ α × β) {A : Matrix α α ℂ} (hA : A.IsHermitian) :
    (toEuclideanLin (liftAlong e A)).IsSymmetric := by
  rw [isSymmetric_toEuclideanLin_iff]
  refine IsHermitian.ext fun p q => ?_
  simp only [liftAlong, of_apply, star_mul', hA.apply]
  by_cases h : (e q).2 = (e p).2
  · simp [h]
  · simp [h, Ne.symm h]

end Lift

variable (dx dy dz : ℕ)

/-- The transport operators of the three axes. -/
def transportAxis : Fin 3 → (H3D dx dy dz →ₗ[ℂ] H3D dx dy dz) :=
  ![TX dx dy dz, TY dx dy dz, TZ dx dy dz]

/-- The position operators of the three axes. -/
def positionAxis : Fin 3 → (H3D dx dy dz →ₗ[ℂ] H3D dx dy dz) :=
  ![PX dx dy dz, PY dx dy dz, PZ dx dy dz]

/-- The six observables, indexed by `(slot, axis)`: slot `0` is `T`, slot `1` is `P`. -/
def observable (k : Fin 2 × Fin 3) : H3D dx dy dz →ₗ[ℂ] H3D dx dy dz :=
  ![transportAxis dx dy dz k.2, positionAxis dx dy dz k.2] k.1

/-- The `6 × 6` covariance matrix `Σ(Ψ)`. -/
def sigma (Ψ : H3D dx dy dz) : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℝ :=
  of fun j k => covarianceG (observable dx dy dz j) (observable dx dy dz k) Ψ

/-- The `6 × 6` commutator matrix `Ω(Ψ)`, with entries `½ ⟨i[A, B]⟩`. -/
def omega (Ψ : H3D dx dy dz) : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℝ :=
  of fun j k => tensionG (observable dx dy dz j) (observable dx dy dz k) Ψ / 2

/-- The `2 × 2` block of one axis of `Σ(Ψ)`. -/
def sigmaAxis (Ψ : H3D dx dy dz) (i : Fin 3) : Matrix (Fin 2) (Fin 2) ℝ :=
  sigmaPair (transportAxis dx dy dz i) (positionAxis dx dy dz i) Ψ

/-- The `2 × 2` block of one axis of `Ω(Ψ)`. -/
def omegaAxis (Ψ : H3D dx dy dz) (i : Fin 3) : Matrix (Fin 2) (Fin 2) ℝ :=
  omegaPair (transportAxis dx dy dz i) (positionAxis dx dy dz i) Ψ

/-- The number of sites of each axis. -/
def sites : Fin 3 → ℕ := ![dx, dy, dz]

/-- The NRS commutator matrix: the block of each axis multiplied by `C_Nava(d_axis)`. -/
def omegaNRS (Ψ : H3D dx dy dz) : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℝ :=
  blockDiagonal fun i => CoherenceConstant (sites dx dy dz i) • omegaAxis dx dy dz Ψ i

variable {dx dy dz}

lemma transportAxis_isSymmetric (i : Fin 3) : (transportAxis dx dy dz i).IsSymmetric := by
  fin_cases i <;> exact isSymmetric_liftAlong _ (Td_isHermitian _)

lemma positionAxis_isSymmetric (i : Fin 3) : (positionAxis dx dy dz i).IsSymmetric := by
  fin_cases i <;> exact isSymmetric_liftAlong _ (Pd_isHermitian _)

/-- **Robertson–Schrödinger on each axis**, at every state of the cube. -/
theorem robertson_axis (Ψ : H3D dx dy dz) (i : Fin 3) :
    (omegaAxis dx dy dz Ψ i).det ≤ (sigmaAxis dx dy dz Ψ i).det :=
  robertson_pair Ψ (transportAxis_isSymmetric i) (positionAxis_isSymmetric i)

/-!

## C. `Ω` is block diagonal

-/

/-- Operators of different axes commute. -/
lemma opCommutator_observable {j k : Fin 2 × Fin 3} (h : j.2 ≠ k.2) :
    opCommutator (observable dx dy dz j) (observable dx dy dz k) = 0 := by
  have xy := commutator_axes_xy dx dy dz
  have xz := commutator_axes_xz dx dy dz
  have yz := commutator_axes_yz dx dy dz
  have yx : ∀ A B, opCommutator (toEuclideanLin (liftAlong (eY dx dy dz) B))
      (toEuclideanLin (liftAlong (eX dx dy dz) A)) = 0 := fun A B => by
    rw [opCommutator_comm, xy, neg_zero]
  have zx : ∀ A B, opCommutator (toEuclideanLin (liftAlong (eZ dx dy dz) B))
      (toEuclideanLin (liftAlong (eX dx dy dz) A)) = 0 := fun A B => by
    rw [opCommutator_comm, xz, neg_zero]
  have zy : ∀ A B, opCommutator (toEuclideanLin (liftAlong (eZ dx dy dz) B))
      (toEuclideanLin (liftAlong (eY dx dy dz) A)) = 0 := fun A B => by
    rw [opCommutator_comm, yz, neg_zero]
  obtain ⟨a, i⟩ := j
  obtain ⟨b, i'⟩ := k
  fin_cases i <;> fin_cases i' <;> simp only [ne_eq, not_true_eq_false] at h <;>
    fin_cases a <;> fin_cases b <;>
    simp [observable, transportAxis, positionAxis, TX, PX, TY, PY, TZ, PZ, xy, xz, yz, yx, zx,
      zy]

/-- **`Ω` is block diagonal at every state**: only `T` and `P` of the same axis collide. -/
theorem omega_eq_blockDiagonal (Ψ : H3D dx dy dz) :
    omega dx dy dz Ψ = blockDiagonal (omegaAxis dx dy dz Ψ) := by
  ext ⟨a, i⟩ ⟨b, i'⟩
  rw [omega, of_apply, blockDiagonal_apply]
  split_ifs with h
  · subst h
    fin_cases a <;> fin_cases b <;>
      simp [observable, omegaAxis, omegaPair, tensionG_self, neg_div,
        tensionG_swap (transportAxis dx dy dz i) (positionAxis dx dy dz i)]
  · rw [tensionG_eq_zero_of_opCommutator _ _ _ (opCommutator_observable h), zero_div]

/-- `det Ω(Ψ) = ∏ (½ ⟨K_axis⟩)²` at every state. -/
theorem det_omega (Ψ : H3D dx dy dz) :
    (omega dx dy dz Ψ).det = ∏ i, (omegaAxis dx dy dz Ψ i).det := by
  rw [omega_eq_blockDiagonal, det_blockDiagonal]

end NRSDeterminant
