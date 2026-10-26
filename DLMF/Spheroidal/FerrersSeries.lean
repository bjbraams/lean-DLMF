/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.FerrersDefs
public import DLMF.Legendre.Associated

/-!
# Expansions in series of Ferrers functions (DLMF §30.8)

Statement acquisition from NIST DLMF (version 1.2.8), checked 2026-10-26. Admitted statements
are not completed proofs; see `DLMF30Acquisition.md`.

* §30.8(i): the expansion 30.8.1 of `𝖯s^m_n` in Ferrers functions with the coefficients 30.8.2,
  the three-term recurrence 30.8.4 with the coefficients 30.8.3 (`A_{-R} = 0` proved), the
  normalization 30.8.5–30.8.6 and the asymptotic ratios 30.8.7, 30.8.8;
* §30.8(ii): the expansion 30.8.9 of `𝖰s^m_n` with the recessive coefficients `a'^m_{n,k}`
  (30.8.10, 30.8.11) and the extended coefficients `a^m_{n,k}`, `-N ≤ k < -R`.

Indices: `R = ⌊(n-m)/2⌋`, `N = ⌊(n+m)/2⌋`; sums over `k ≥ -R` are written over `j : ℕ` with
`k = j - R`. Numerical checks: the recurrence and normalization were used to compute `𝖯s` and
`𝖰s` (compared with SciPy and with 30.4.1); the series 30.8.9 reproduces the Wronskian 30.5.4
and the parity 30.5.2 to 25 digits, provided the extended coefficients are included in `A^m_n`;
the project's `ferrersQ` agrees with mpmath at the low degrees `-m ≤ ν < m` that occur in 30.8.9.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics DLMF.Legendre
open scoped Topology Real

namespace DLMF.Spheroidal

/-! ### §30.8(i) Functions of the first kind -/

/-- **The integral formula** (DLMF 30.8.2): for `k ≥ -R`,
`a^m_{n,k}(γ²) = (-1)^k (n+2k+1/2) (n-m+2k)!/(n+m+2k)! ∫_{-1}^1 𝖯s^m_n(x, γ²) 𝖯^m_{n+2k}(x) dx`.
Proved (definition). -/
@[dlmf 30.8.E2]
theorem spheroidalCoeff_of_le {n m : ℕ} (γ2 : ℝ) {k : ℤ} (hk : -(((n - m) / 2 : ℕ) : ℤ) ≤ k) :
    spheroidalCoeff n m γ2 k = (-1 : ℝ) ^ k * ((n : ℝ) + 2 * k + 1 / 2) *
      ((((n : ℤ) - m + 2 * k).toNat.factorial : ℝ) / (((n : ℤ) + m + 2 * k).toNat.factorial)) *
      ∫ x in (-1 : ℝ)..1, spheroidalPs n m x γ2 * (ferrersP ((n : ℂ) + 2 * k) m x).re := by
  unfold spheroidalCoeff
  simp only [hk, ↓reduceIte]
  rfl

/-- **The Ferrers expansion** (DLMF 30.8.1):
`𝖯s^m_n(x, γ²) = ∑_{k ≥ -R} (-1)^k a^m_{n,k}(γ²) 𝖯^m_{n+2k}(x)` on `(-1, 1)`. -/
@[dlmf 30.8.E1]
theorem hasSum_spheroidalPs_ferrers {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun j : ℕ =>
        let k : ℤ := (j : ℤ) - ((n - m) / 2 : ℕ)
        (-1 : ℝ) ^ k * spheroidalCoeff n m γ2 k * (ferrersP ((n : ℂ) + 2 * k) m x).re)
      (spheroidalPs n m x γ2) := by
  sorry

/-- `A_{-R} = 0` (DLMF §30.8(i), note after 30.8.4). Proved. -/
@[dlmf 30.8.E4]
theorem spheroidalRecA_neg_R {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    spheroidalRecA n m γ2 (-(((n - m) / 2 : ℕ) : ℤ)) = 0 := by
  have key : ∀ R : ℕ, (n - m) / 2 = R → spheroidalRecA n m γ2 (-(R : ℤ)) = 0 := by
    intro R hR
    have h := Nat.div_add_mod (n - m) 2
    rw [hR] at h
    have hcast : (n : ℝ) - m = 2 * R + ((n - m) % 2 : ℕ) := by
      have : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := by rw [Nat.cast_sub hmn]
      rw [← this]; exact_mod_cast h.symm
    unfold spheroidalRecA
    have hnum : ((n : ℝ) - m + 2 * ((-(R : ℤ) : ℤ) : ℝ) - 1) *
        ((n : ℝ) - m + 2 * ((-(R : ℤ) : ℤ) : ℝ)) = 0 := by
      rw [hcast]
      rcases Nat.mod_two_eq_zero_or_one (n - m) with h' | h' <;> rw [h'] <;> push_cast <;> ring
    rw [hnum]; ring
  exact key _ rfl

/-- **The recurrence** (DLMF 30.8.4, §30.8(ii)): the coefficients `a^m_{n,k}(γ²)` satisfy
`A_k a_{k-1} + (B_k - λ^m_n(γ²)) a_k + C_k a_{k+1} = 0` for all `k ∈ ℤ` (with `a_k = 0` for
`k < -N` and the extension of §30.8(ii) for `-N ≤ k < -R`), when the forward solution does not
vanish at `k = -R`. -/
@[dlmf 30.8.E4]
theorem spheroidalCoeff_recurrence {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) (k : ℤ) :
    spheroidalRecA n m γ2 k * spheroidalCoeff n m γ2 (k - 1) +
        (spheroidalRecB n m γ2 k - spheroidalEigenvalue n m γ2) * spheroidalCoeff n m γ2 k +
      spheroidalRecC n m γ2 k * spheroidalCoeff n m γ2 (k + 1) = 0 := by
  sorry

/-- **The recurrence for `k ≥ -R`** (DLMF 30.8.4): the coefficients of 30.8.1 solve the difference
equation from `k = -R` on (no hypothesis needed). -/
@[dlmf 30.8.E4]
theorem spheroidalCoeff_recurrence_of_le {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) {k : ℤ}
    (hk : -(((n - m) / 2 : ℕ) : ℤ) ≤ k) :
    spheroidalRecA n m γ2 k * (if -(((n - m) / 2 : ℕ) : ℤ) ≤ k - 1 then
        spheroidalCoeff n m γ2 (k - 1) else 0) +
        (spheroidalRecB n m γ2 k - spheroidalEigenvalue n m γ2) * spheroidalCoeff n m γ2 k +
      spheroidalRecC n m γ2 k * spheroidalCoeff n m γ2 (k + 1) = 0 := by
  sorry

/-- **The normalization** (DLMF 30.8.5):
`∑_{k ≥ -R} a^m_{n,k}(γ²) a^{-m}_{n,k}(γ²)/(2n+4k+1) = 1/(2n+1)` (equivalent to 30.4.1). -/
@[dlmf 30.8.E5]
theorem hasSum_spheroidalCoeff_normalization {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    HasSum (fun j : ℕ =>
        let k : ℤ := (j : ℤ) - ((n - m) / 2 : ℕ)
        spheroidalCoeff n m γ2 k * spheroidalCoeffNeg n m γ2 k / (2 * (n : ℝ) + 4 * k + 1))
      (1 / (2 * (n : ℝ) + 1)) := by
  sorry

/-- **The coefficients `a^{-m}_{n,k}`** (DLMF 30.8.6): for `k ≥ -R`,
`a^{-m}_{n,k} = (n-m)!(n+m+2k)!/((n+m)!(n-m+2k)!) a^m_{n,k}`. Proved (definition). -/
@[dlmf 30.8.E6]
theorem spheroidalCoeffNeg_of_le {n m : ℕ} (γ2 : ℝ) {k : ℤ}
    (hk : -(((n - m) / 2 : ℕ) : ℤ) ≤ k) :
    spheroidalCoeffNeg n m γ2 k =
      (((n - m).factorial : ℝ) * (((n : ℤ) + m + 2 * k).toNat.factorial : ℝ)) /
        (((n + m).factorial : ℝ) * (((n : ℤ) - m + 2 * k).toNat.factorial : ℝ)) *
          spheroidalCoeff n m γ2 k := by
  unfold spheroidalCoeffNeg
  simp only [hk, ↓reduceIte]

/-- **Ratio asymptotics** (DLMF 30.8.7): `k² a^m_{n,k}(γ²)/a^m_{n,k-1}(γ²) = γ²/16 + O(1/k)` as
`k → ∞`. -/
@[dlmf 30.8.E7]
theorem spheroidalCoeff_ratio_isBigO {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    (fun k : ℕ => (k : ℝ) ^ 2 * spheroidalCoeff n m γ2 k / spheroidalCoeff n m γ2 ((k : ℤ) - 1) -
        γ2 / 16) =O[atTop] (fun k : ℕ => (k : ℝ)⁻¹) := by
  sorry

/-- **Ratio asymptotics** (DLMF 30.8.8):
`(λ^m_n(γ²) - B_k)/A_k · a^m_{n,k}(γ²)/a^m_{n,k-1}(γ²) = 1 + O(k⁻⁴)` as `k → ∞`. -/
@[dlmf 30.8.E8]
theorem spheroidalCoeff_ratio_isBigO_four {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ) :
    (fun k : ℕ => (spheroidalEigenvalue n m γ2 - spheroidalRecB n m γ2 k) /
        spheroidalRecA n m γ2 k *
          (spheroidalCoeff n m γ2 k / spheroidalCoeff n m γ2 ((k : ℤ) - 1)) - 1)
      =O[atTop] (fun k : ℕ => ((k : ℝ) ^ 4)⁻¹) := by
  sorry

/-! ### §30.8(ii) Functions of the second kind -/

/-- **The expansion of `𝖰s`** (DLMF 30.8.9–30.8.11): for `-1 < x < 1`,
`𝖰s^m_n(x, γ²) = ∑_{k ≤ -N-1} (-1)^k a'^m_{n,k}(γ²) 𝖯^m_{n+2k}(x)
  + ∑_{k ≥ -N} (-1)^k a^m_{n,k}(γ²) 𝖰^m_{n+2k}(x)`, with `a'` the recessive solution of 30.8.4
normalized by 30.8.10–30.8.11 and `a^m_{n,k}` extended to `-N ≤ k < -R` by forward recursion
(hypothesis: the forward solution does not vanish at `-R`, else `𝖰s` does not exist). -/
@[dlmf 30.8.E9, dlmf 30.8.E10, dlmf 30.8.E11]
theorem spheroidalQs_eq_ferrers_series {n m : ℕ} (hmn : m ≤ n) (γ2 : ℝ)
    (hf : spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) ≠ 0) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ∃ S₁ S₂ : ℝ,
      HasSum (fun j : ℕ =>
          let k : ℤ := -(((n + m) / 2 : ℕ) : ℤ) - 1 - j
          (-1 : ℝ) ^ k * spheroidalCoeffPrime n m γ2 k * (ferrersP ((n : ℂ) + 2 * k) m x).re)
        S₁ ∧
      HasSum (fun j : ℕ =>
          let k : ℤ := -(((n + m) / 2 : ℕ) : ℤ) + j
          (-1 : ℝ) ^ k * spheroidalCoeff n m γ2 k * (ferrersQ ((n : ℂ) + 2 * k) m x).re)
        S₂ ∧
      spheroidalQs n m x γ2 = S₁ + S₂ := by
  sorry

/-- **The extended coefficients** (DLMF §30.8(ii)): for `-N ≤ k < -R` they are obtained by
forward recursion from `a^m_{n,-N-1} = 0`, matched to `a^m_{n,-R}`. Proved (definition). -/
@[dlmf 30.8.ii]
theorem spheroidalCoeff_of_lt {n m : ℕ} (γ2 : ℝ) {k : ℤ} (hk : k < -(((n - m) / 2 : ℕ) : ℤ))
    (hk' : -(((n + m) / 2 : ℕ) : ℤ) ≤ k) :
    spheroidalCoeff n m γ2 k = spheroidalCoeff n m γ2 (-(((n - m) / 2 : ℕ) : ℤ)) *
      spheroidalFwd n m γ2 (k + ((n + m) / 2 : ℕ) + 1).toNat /
        spheroidalFwd n m γ2 ((n + m) / 2 - (n - m) / 2 + 1) := by
  have h1 : ¬ (-(((n - m) / 2 : ℕ) : ℤ) ≤ k) := not_le.mpr hk
  have h2 : spheroidalCoeff n m γ2 (-(((n - m) / 2 : ℕ) : ℤ)) =
      spheroidalCoeffMain n m γ2 (-(((n - m) / 2 : ℕ) : ℤ)) := by
    unfold spheroidalCoeff
    simp only [le_refl, ↓reduceIte]
  rw [h2]
  unfold spheroidalCoeff
  simp only [h1, hk', ↓reduceIte]

end DLMF.Spheroidal
