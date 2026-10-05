/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3DeSitter.DeSitterHorizon
public import NavaRobertsonIndependent.Mathematics.D16g_CutEntropy
public import NavaRobertsonIndependent.Mathematics.D25_DimensionalQuantum
/-!

# The cosmological constant from a count of states

## i. Overview

`DeSitterHorizon` reads `Λ = 3 π / (ℓ² S)` backwards from the entropy `S` of the horizon. Here
`S` is counted first, with no `Λ` in the input, and `Λ` comes out.

Cut the axis of `n + 1` positions between `c` and `c + 1`. The non-local links across the cut
number `M = (c + 1)(n − c) − 1`; each one closes a cycle and carries one quantum (`D16g`). With
`k` quanta on the cut there are `W = M^k` states and `S = log W = k log M`. The constant
`3 π / (ℓ² log W)` solves both Friedmann equations, and its horizon has entropy exactly
`log W`. If the quanta sit on distinct links, `S ≤ M log 2`, and the count bounds the constant
from below: `Λ ≥ 3 π / (ℓ² M log 2)`. On the central cut of `2m + 2` positions,
`M = m (m + 2)`.

The quantum of `H_d` is `δ(d)` (`D25`). At `d = 2, 3` it vanishes: every configuration of the cut
carries no defect, and the count sees nothing. From the rupture `d = 4` on, `0 < δ(d) < δ_∞`, and
the entropy is proportional to the defect, `S = (log M / δ(d)) · Ω_d`.

## ii. Key results

- `numCross_eq` : `M = (c + 1)(n − c) − 1`.
- `numCross_centre` : `M = m (m + 2)` on the central cut.
- `blind_below_rupture` : at `d = 2, 3` the defect of every configuration is `0`.
- `quantumDefect_pos`, `quantumDefect_lt_defect` : from `d = 4`, `0 < k δ(d) < k δ_∞`.
- `entropy_eq_mul_quantumDefect` : `S = (log M / δ(d)) · Ω_d` from `d = 4`.
- `countCosmologicalConstant_eq` : `Λ = 3 π / (ℓ² k log ((c + 1)(n − c) − 1))`.
- `deSitterEntropy_countCosmologicalConstant` : the horizon has entropy `log W`.
- `countCosmologicalConstant_firstOrderFriedmann`,
  `countCosmologicalConstant_secondOrderFriedmann` : both Friedmann equations hold.
- `countCosmologicalConstant_strictAnti` : more quanta, smaller `Λ`.
- `lower_bound_simpleCountCosmologicalConstant` : `3 π / (ℓ² M log 2) ≤ Λ`.
- `lower_bound_centre` : `3 π / (ℓ² m (m + 2) log 2) ≤ Λ` on the central cut.

## iii. Table of contents

- A. The crossing links
- B. The quanta and the rupture
- C. The constant counted
- D. Distinct links: the bound

## iv. References

- G. W. Gibbons and S. W. Hawking, *Cosmological event horizons, thermodynamics, and particle
  creation*, Phys. Rev. D 15 (1977) 2738.
- T. Banks, *Cosmological breaking of supersymmetry or little Lambda goes back to the future*,
  arXiv:hep-th/0007146 (2000).

-/

@[expose] public section

namespace HorizonCount

open Real Time CutEntropy DimensionalQuantum Cosmology.FLRW.FriedmannEquation

/-!

## A. The crossing links

-/

lemma card_left (n c : ℕ) (hc : c ≤ n) :
    (Finset.univ.filter fun a : Fin (n + 1) => a.val ≤ c).card = c + 1 := by
  have : (Finset.univ.filter fun a : Fin (n + 1) => a.val ≤ c) =
      (Finset.range (c + 1)).attachFin (fun m hm => by simp at hm; omega) := by
    ext a
    simp
  rw [this, Finset.card_attachFin, Finset.card_range]

lemma card_right (n c : ℕ) :
    (Finset.univ.filter fun b : Fin (n + 1) => c < b.val).card = n - c := by
  have : (Finset.univ.filter fun b : Fin (n + 1) => c < b.val) =
      (Finset.Ioo c (n + 1)).attachFin (fun m hm => by simp at hm; omega) := by
    ext b
    simp [b.isLt]
  rw [this, Finset.card_attachFin, Nat.card_Ioo]
  omega

/-- **The number of crossing links**: `M = (c + 1)(n − c) − 1`. -/
theorem numCross_eq {n c : ℕ} (hc : c < n) : numCross n c = (c + 1) * (n - c) - 1 := by
  set L := Finset.univ.filter fun a : Fin (n + 1) => a.val ≤ c
  set R := Finset.univ.filter fun b : Fin (n + 1) => c < b.val
  have hp : ((⟨c, by omega⟩ : Fin (n + 1)), (⟨c + 1, by omega⟩ : Fin (n + 1))) ∈ L ×ˢ R := by
    simp [L, R]
  have h : crossLinks n c = (L ×ˢ R).erase (⟨c, by omega⟩, ⟨c + 1, by omega⟩) := by
    ext ⟨a, b⟩
    simp only [mem_crossLinks, Finset.mem_erase, Finset.mem_product, L, R, Finset.mem_filter,
      Finset.mem_univ, true_and, ne_eq, Prod.mk.injEq, Fin.ext_iff]
    omega
  rw [numCross, h, Finset.card_erase_of_mem hp, Finset.card_product, card_left n c hc.le,
    card_right]

/-- On the central cut of `2m + 2` positions, `M = m (m + 2)`. -/
theorem numCross_centre (m : ℕ) : numCross (2 * m + 1) m = m * (m + 2) := by
  rw [numCross_eq (by omega)]
  have : 2 * m + 1 - m = m + 1 := by omega
  rw [this]
  ring_nf
  omega

/-- A cut with two positions on each side has at least three crossing links. -/
lemma three_le_numCross {n c : ℕ} (hc : 1 ≤ c) (hcn : c + 2 ≤ n) : 3 ≤ numCross n c := by
  rw [numCross_eq (by omega)]
  have : 2 * 2 ≤ (c + 1) * (n - c) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-!

## B. The quanta and the rupture

-/

/-- The defect `k δ(d)` of `k` quanta of `H_d`. -/
noncomputable def quantumDefect (d k : ℕ) : ℝ := k * dimQuantum d

/-- **Blind below the rupture.** At `d = 2, 3` no configuration carries a defect. -/
theorem blind_below_rupture {d : ℕ} (hd : d = 2 ∨ d = 3) (k : ℕ) : quantumDefect d k = 0 := by
  rw [quantumDefect, (dimQuantum_eq_zero_iff (by omega)).mpr hd, mul_zero]

/-- From the rupture `d = 4` on, `k ≥ 1` quanta carry a positive defect. -/
theorem quantumDefect_pos {d k : ℕ} (hd : 4 ≤ d) (hk : 1 ≤ k) : 0 < quantumDefect d k := by
  have : (0 : ℝ) < k := by exact_mod_cast hk
  exact mul_pos this (dimQuantum_pos hd)

/-- The defect of `H_d` stays below the limit `k δ_∞`, never reaching it. -/
theorem quantumDefect_lt_defect {d k : ℕ} (hd : 4 ≤ d) (hk : 1 ≤ k) :
    quantumDefect d k < defect k := by
  have : (0 : ℝ) < k := by exact_mod_cast hk
  rw [quantumDefect, defect_eq]
  exact mul_lt_mul_of_pos_left (dimQuantum_lt_deltaInf hd) this

/-- **Area law from the rupture on**: `S = (log M / δ(d)) · Ω_d`. -/
theorem entropy_eq_mul_quantumDefect (n c k : ℕ) {d : ℕ} (hd : 4 ≤ d) :
    entropy n c k = Real.log (numCross n c) / dimQuantum d * quantumDefect d k := by
  rw [entropy_eq, quantumDefect]
  field_simp [(dimQuantum_pos hd).ne']

/-!

## C. The constant counted

-/

/-- The entropy of `k ≥ 1` quanta on a cut with `M ≥ 2` is positive. -/
lemma entropy_pos {n c k : ℕ} (hk : 1 ≤ k) (hM : 2 ≤ numCross n c) : 0 < entropy n c k := by
  rw [entropy_eq]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hM' : (1 : ℝ) < numCross n c := by exact_mod_cast hM
  exact mul_pos hk' (Real.log_pos hM')

/-- The cosmological constant fixed by the count `W = M^k`: `3 π / (ℓ² log W)`. -/
noncomputable def countCosmologicalConstant (n c k : ℕ) (ℓ : ℝ) : ℝ :=
  entropyCosmologicalConstant (entropy n c k) ℓ

/-- **The constant counted**: `Λ = 3 π / (ℓ² k log ((c + 1)(n − c) − 1))`. -/
theorem countCosmologicalConstant_eq {n c : ℕ} (hc : c < n) (k : ℕ) (ℓ : ℝ) :
    countCosmologicalConstant n c k ℓ =
      3 * π / (ℓ ^ 2 * (k * Real.log (((c + 1) * (n - c) - 1 : ℕ) : ℝ))) := by
  rw [countCosmologicalConstant, entropyCosmologicalConstant, entropy_eq, numCross_eq hc]

/-- The horizon of the counted constant has entropy exactly `log W`. -/
theorem deSitterEntropy_countCosmologicalConstant {n c k : ℕ} {ℓ : ℝ} (hk : 1 ≤ k)
    (hM : 2 ≤ numCross n c) (hℓ : ℓ ≠ 0) :
    deSitterEntropy (countCosmologicalConstant n c k ℓ) ℓ = entropy n c k :=
  deSitterEntropy_entropyCosmologicalConstant (entropy_pos hk hM) hℓ

theorem countCosmologicalConstant_firstOrderFriedmann {n c k : ℕ} {a₀ σ ℓ G c' : ℝ}
    (hk : 1 ≤ k) (hM : 2 ≤ numCross n c) (hℓ : ℓ ≠ 0) (ha₀ : a₀ ≠ 0)
    (hσ : σ = 1 ∨ σ = -1) (t : Time) :
    FirstOrderFriedmann (deSitterScaleFactor a₀ σ (countCosmologicalConstant n c k ℓ) c')
      (fun _ => 0) 0 (countCosmologicalConstant n c k ℓ) G c' t :=
  entropyCosmologicalConstant_firstOrderFriedmann (entropy_pos hk hM) hℓ ha₀ hσ t

theorem countCosmologicalConstant_secondOrderFriedmann {n c k : ℕ} {a₀ σ ℓ G c' : ℝ}
    (hk : 1 ≤ k) (hM : 2 ≤ numCross n c) (hℓ : ℓ ≠ 0) (ha₀ : a₀ ≠ 0)
    (hσ : σ = 1 ∨ σ = -1) (t : Time) :
    SecondOrderFriedmann (deSitterScaleFactor a₀ σ (countCosmologicalConstant n c k ℓ) c')
      (fun _ => 0) (fun _ => 0) (countCosmologicalConstant n c k ℓ) G c' t :=
  entropyCosmologicalConstant_secondOrderFriedmann (entropy_pos hk hM) hℓ ha₀ hσ t

/-- More quanta on the cut, a strictly smaller constant. -/
theorem countCosmologicalConstant_strictAnti {n c k₁ k₂ : ℕ} {ℓ : ℝ} (hk : 1 ≤ k₁)
    (h : k₁ < k₂) (hM : 2 ≤ numCross n c) (hℓ : ℓ ≠ 0) :
    countCosmologicalConstant n c k₂ ℓ < countCosmologicalConstant n c k₁ ℓ := by
  have h₁ := entropy_pos hk hM
  have h₂ := entropy_pos (hk.trans h.le) hM
  refine entropyCosmologicalConstant_strictAntiOn hℓ h₁ h₂ ?_
  rw [entropy_eq, entropy_eq]
  have hM' : (0 : ℝ) < Real.log (numCross n c) :=
    Real.log_pos (by exact_mod_cast hM)
  exact mul_lt_mul_of_pos_right (by exact_mod_cast h) hM'

/-!

## D. Distinct links: the bound

-/

/-- `1 ≤ k < M` distinct links have positive entropy. -/
lemma simpleEntropy_pos {n c k : ℕ} (hk : 1 ≤ k) (hkM : k < numCross n c) :
    0 < simpleEntropy n c k := by
  rw [simpleEntropy_eq]
  have h : k + 1 ≤ (numCross n c).choose k := by
    rw [← Nat.choose_succ_self_right]
    exact Nat.choose_le_choose k hkM
  exact Real.log_pos (by exact_mod_cast (show 1 < (numCross n c).choose k by omega))

/-- The cosmological constant fixed by `k` distinct links on the cut. -/
noncomputable def simpleCountCosmologicalConstant (n c k : ℕ) (ℓ : ℝ) : ℝ :=
  entropyCosmologicalConstant (simpleEntropy n c k) ℓ

/-- **The count bounds the constant from below**: `3 π / (ℓ² M log 2) ≤ Λ`. -/
theorem lower_bound_simpleCountCosmologicalConstant {n c k : ℕ} {ℓ : ℝ} (hk : 1 ≤ k)
    (hkM : k < numCross n c) (hℓ : ℓ ≠ 0) :
    3 * π / (ℓ ^ 2 * (numCross n c * Real.log 2)) ≤
      simpleCountCosmologicalConstant n c k ℓ := by
  have hS := simpleEntropy_pos hk hkM
  have hmax := simpleEntropy_le_max hkM.le
  rw [simpleCountCosmologicalConstant, entropyCosmologicalConstant]
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  gcongr

/-- **The bound on the central cut**: `3 π / (ℓ² m (m + 2) log 2) ≤ Λ`. -/
theorem lower_bound_centre {m k : ℕ} {ℓ : ℝ} (hk : 1 ≤ k) (hkM : k < m * (m + 2))
    (hℓ : ℓ ≠ 0) :
    3 * π / (ℓ ^ 2 * ((m * (m + 2) : ℕ) * Real.log 2)) ≤
      simpleCountCosmologicalConstant (2 * m + 1) m k ℓ := by
  rw [← numCross_centre]
  exact lower_bound_simpleCountCosmologicalConstant hk (by rwa [numCross_centre]) hℓ

end HorizonCount
