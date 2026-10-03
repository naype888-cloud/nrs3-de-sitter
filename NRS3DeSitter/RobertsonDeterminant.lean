/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3DeSitter.UncertaintyMatrices
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.PosDef
/-!

# Robertson's determinant inequality on the cube

## i. Overview

For every state `Ψ` of the cube, `det Ω(Ψ) ≤ det Σ(Ψ)`, with `Σ` the `6 × 6` covariance matrix of
`(T_x, P_x, T_y, P_y, T_z, P_z)` and `Ω` the matrix of `½ ⟨i[A, B]⟩` (Robertson 1934).

The proof: `Σ − iΩ` is the Gram matrix of the six fluctuation vectors and `Σ + iΩ` its
transpose, so both are positive semidefinite. For `A` positive definite and `B` hermitian with
`A ± B` positive semidefinite, the congruence `T A Tᴴ = 1` gives `−1 ≤ T B Tᴴ ≤ 1`, so every
eigenvalue of `T B Tᴴ` lies in `[−1, 1]` and `‖det B‖ ≤ det A`. With `A = Σ + ε` and `B = iΩ`,
letting `ε → 0` gives `|det Ω| ≤ det Σ`.

## ii. Key results

- `NRSDeterminant.norm_det_le_re_det` : `‖det B‖ ≤ re (det A)` for `A > 0` and `A ± B ≥ 0`.
- `NRSDeterminant.abs_det_le_det` : `|det W| ≤ det S` for real `S`, `W` with `S ∓ iW ≥ 0`.
- `NRSDeterminant.robertson_cube` : `det Ω(Ψ) ≤ det Σ(Ψ)` for every state of the cube.

## iii. Table of contents

- A. A determinant bound for positive matrices
- B. Real matrices
- C. The cube

## iv. References

- H. P. Robertson, *An indeterminacy relation for several observables and its classical
  interpretation*, Phys. Rev. 46 (1934) 794.

-/

@[expose] public noncomputable section

namespace NRSDeterminant

open Matrix Unitary Filter Topology PathGraph3DNRS
open scoped ComplexOrder

/-!

## A. A determinant bound for positive matrices

-/

section Bound

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The eigenvalues of a hermitian `K` with `1 ∓ K ≥ 0` lie in `[−1, 1]`. -/
lemma abs_eigenvalues_le_one {K : Matrix n n ℂ} (hK : K.IsHermitian) (hm : (1 - K).PosSemidef)
    (hp : (1 + K).PosSemidef) (i : n) : |hK.eigenvalues i| ≤ 1 := by
  set v := hK.eigenvectorBasis i
  have hv : star (v : n → ℂ) ⬝ᵥ (v : n → ℂ) = 1 := by
    have := hK.eigenvectorBasis.orthonormal.1 i
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
      this]
    simp
  have h0 := hm.re_dotProduct_nonneg (v : n → ℂ)
  have h1 := hp.re_dotProduct_nonneg (v : n → ℂ)
  rw [sub_mulVec, one_mulVec, dotProduct_sub, hK.mulVec_eigenvectorBasis, dotProduct_smul,
    hv] at h0
  rw [add_mulVec, one_mulVec, dotProduct_add, hK.mulVec_eigenvectorBasis, dotProduct_smul,
    hv] at h1
  simp at h0 h1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **A determinant bound.** If `A` is positive definite, `B` hermitian and `A − B`, `A + B`
positive semidefinite, then `‖det B‖ ≤ re (det A)`. -/
theorem norm_det_le_re_det {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.IsHermitian)
    (h₁ : (A - B).PosSemidef) (h₂ : (A + B).PosSemidef) : ‖B.det‖ ≤ (A.det).re := by
  set U : Matrix n n ℂ := (hA.1.eigenvectorUnitary : Matrix n n ℂ)
  set α := hA.1.eigenvalues
  have hα : ∀ i, 0 < α i := hA.eigenvalues_pos
  have hUU : star U * U = 1 := coe_star_mul_self _
  have hAU : A = U * diagonal (fun i => (α i : ℂ)) * star U := by
    conv_lhs => rw [hA.1.spectral_theorem, conjStarAlgAut_apply]
    rfl
  set D : Matrix n n ℂ := diagonal fun i => ((Real.sqrt (α i))⁻¹ : ℂ)
  set T : Matrix n n ℂ := D * star U
  have hDD : D * diagonal (fun i => (α i : ℂ)) * D = 1 := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    have hs : (Real.sqrt (α i) : ℂ) ^ 2 = α i := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (hα i).le]
    have hne : (Real.sqrt (α i) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (hα i)).ne'
    rw [← hs]
    field_simp
  have hTH : Tᴴ = U * D := by
    simp [T, D, conjTranspose_mul, diagonal_conjTranspose, Pi.star_def, star_eq_conjTranspose]
  have hT : T * A * Tᴴ = 1 := by
    rw [hTH, hAU]
    calc D * star U * (U * diagonal (fun i => (α i : ℂ)) * star U) * (U * D)
        = D * (star U * U) * diagonal (fun i => (α i : ℂ)) * (star U * U) * D := by
          simp only [mul_assoc]
      _ = 1 := by rw [hUU, mul_one, mul_one, hDD]
  set K := T * B * Tᴴ
  have hK : K.IsHermitian := by
    simp only [IsHermitian, K, conjTranspose_mul, conjTranspose_conjTranspose, hB.eq, mul_assoc]
  have hKm : (1 - K).PosSemidef := by
    have := h₁.mul_mul_conjTranspose_same T
    rwa [mul_sub, sub_mul, hT] at this
  have hKp : (1 + K).PosSemidef := by
    have := h₂.mul_mul_conjTranspose_same T
    rwa [mul_add, add_mul, hT] at this
  have hle := abs_eigenvalues_le_one hK hKm hKp
  have hdetK : ‖K.det‖ ≤ 1 := by
    rw [hK.det_eq_prod_eigenvalues, norm_prod]
    refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => ?_
    rw [RCLike.norm_ofReal]
    exact hle i
  have hdetA : A.det = ((∏ i, α i : ℝ) : ℂ) := by
    rw [hA.1.det_eq_prod_eigenvalues]
    push_cast
    rfl
  have hprod : 0 < ∏ i, α i := Finset.prod_pos fun i _ => hα i
  have hBK : B.det = K.det * A.det := by
    have h := congrArg det hT
    rw [det_mul, det_mul, det_one] at h
    simp only [K, det_mul]
    linear_combination (-B.det) * h
  rw [hBK, norm_mul, hdetA, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hprod]
  nlinarith [norm_nonneg K.det]

end Bound

/-!

## B. Real matrices

-/

section Real

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A real matrix as a complex matrix. -/
abbrev toC (M : Matrix n n ℝ) : Matrix n n ℂ := M.map (↑)

lemma det_toC (M : Matrix n n ℝ) : (toC M).det = (M.det : ℂ) :=
  (RingHom.map_det Complex.ofRealHom M).symm

omit [Fintype n] in
lemma toC_add_smul_one (S : Matrix n n ℝ) (ε : ℝ) :
    toC (S + ε • 1) = toC S + (ε : ℂ) • 1 := by
  ext i j
  by_cases h : i = j <;> simp [one_apply, h]

/-- **Robertson's determinant inequality for real matrices.** If `S ∓ iW` are positive
semidefinite, then `|det W| ≤ det S`. -/
theorem abs_det_le_det {S W : Matrix n n ℝ}
    (h₁ : (toC S - Complex.I • toC W).PosSemidef)
    (h₂ : (toC S + Complex.I • toC W).PosSemidef) : |W.det| ≤ S.det := by
  have hS : (toC S).PosSemidef := by
    have h12 : (0 : ℂ) ≤ ((1 / 2 : ℝ) : ℂ) := Complex.zero_le_real.mpr (by norm_num)
    have h := (h₁.add h₂).smul h12
    convert h using 1
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    push_cast
    ring
  have hB : (Complex.I • toC W).IsHermitian := by
    have e : Complex.I • toC W = toC S - (toC S - Complex.I • toC W) := by abel
    rw [e]
    exact hS.1.sub h₁.1
  have key : ∀ ε : ℝ, 0 < ε → |W.det| ≤ (S + ε • 1).det := by
    intro ε hε
    have hε1 : ((ε : ℂ) • (1 : Matrix n n ℂ)).PosSemidef :=
      PosSemidef.one.smul (Complex.zero_le_real.mpr hε.le)
    have hA : (toC (S + ε • 1)).PosDef := by
      rw [toC_add_smul_one]
      exact PosDef.posSemidef_add hS (PosDef.one.smul (Complex.zero_lt_real.mpr hε))
    have h₁' : (toC (S + ε • 1) - Complex.I • toC W).PosSemidef := by
      rw [toC_add_smul_one, add_sub_right_comm]
      exact h₁.add hε1
    have h₂' : (toC (S + ε • 1) + Complex.I • toC W).PosSemidef := by
      rw [toC_add_smul_one, add_right_comm]
      exact h₂.add hε1
    have h := norm_det_le_re_det hA hB h₁' h₂'
    rwa [det_smul, det_toC, det_toC, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re] at h
  have hlim : Tendsto (fun ε : ℝ => (S + ε • (1 : Matrix n n ℝ)).det) (𝓝[>] 0) (𝓝 S.det) := by
    have hc : Continuous fun ε : ℝ => (S + ε • (1 : Matrix n n ℝ)).det :=
      (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)

end Real

/-!

## C. The cube

-/

variable {dx dy dz : ℕ}

lemma observable_isSymmetric (k : Fin 2 × Fin 3) : (observable dx dy dz k).IsSymmetric := by
  obtain ⟨a, i⟩ := k
  fin_cases a
  · simpa [observable] using transportAxis_isSymmetric i
  · simpa [observable] using positionAxis_isSymmetric i

/-- The six fluctuation vectors `(A − ⟨A⟩)Ψ`. -/
def fluctuation (Ψ : H3D dx dy dz) (k : Fin 2 × Fin 3) : H3D dx dy dz :=
  centeredG (observable dx dy dz k) Ψ

/-- `Σ − iΩ` is the Gram matrix of the fluctuation vectors. -/
lemma gram_fluctuation (Ψ : H3D dx dy dz) :
    gram ℂ (fluctuation Ψ) = toC (sigma dx dy dz Ψ) - Complex.I • toC (omega dx dy dz Ψ) := by
  ext j k
  have ht := tensionG_eq_neg_two_im Ψ (observable_isSymmetric j) (observable_isSymmetric k)
  simp only [gram, sigma, omega, fluctuation, covarianceG, of_apply, Matrix.map_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, ht]
  apply Complex.ext
  · simp
  · simp
    ring

/-- `Σ + iΩ` is the transpose of the Gram matrix. -/
lemma gram_fluctuation_transpose (Ψ : H3D dx dy dz) :
    (gram ℂ (fluctuation Ψ))ᵀ = toC (sigma dx dy dz Ψ) + Complex.I • toC (omega dx dy dz Ψ) := by
  ext j k
  have ht := tensionG_eq_neg_two_im Ψ (observable_isSymmetric j) (observable_isSymmetric k)
  simp only [transpose_apply, gram, sigma, omega, fluctuation, covarianceG, of_apply,
    Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ht]
  rw [← inner_conj_symm (centeredG (observable dx dy dz k) Ψ)]
  apply Complex.ext <;>
    simp only [Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] <;>
    ring

/-- **Robertson 1934 on the cube.** For every state, `det Ω(Ψ) ≤ det Σ(Ψ)`. -/
theorem robertson_cube (Ψ : H3D dx dy dz) : (omega dx dy dz Ψ).det ≤ (sigma dx dy dz Ψ).det :=
  (le_abs_self _).trans <| abs_det_le_det
    (by rw [← gram_fluctuation]; exact posSemidef_gram ℂ _)
    (by rw [← gram_fluctuation_transpose]; exact (posSemidef_gram ℂ _).transpose)

end NRSDeterminant
