/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.SpectralExistence
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-!
# Asymptotic expansions for large `q` (DLMF §28.8)

With `h = √q → +∞` (real): the eigenvalue expansion 28.8.1 and the exponentially small gap
28.8.2; Sips' expansions 28.8.3–28.8.7 near `x = π/2` and Goldstein's expansions 28.8.8–28.8.12
away from `π/2`, both in terms of `D_m(ξ) = e^{-ξ²/4} He_m(ξ)` (`He_m` is Mathlib's
probabilists' Hermite polynomial `Polynomial.hermite m`).

DLMF gives the functions `U_m`, `V_m`, `Ĉ_m`, `Ŝ_m`, `σ_m`, `τ_{m+1}`, `P_m`, `Q_m` only through
their asymptotic series. Here the printed truncations are inserted and the resulting
approximation is stated with a relative error: `O(h⁻³)` for Sips' expansions at fixed `λ`
(the first omitted terms are of order `h⁻³`), and `O(h⁻¹)` for Goldstein's expansions at fixed
`μ ≥ 1` (a safe order: the printed `P_m`, `Q_m` are series in `1/(h cos² x)` with
`cos x ≍ μ h^{-1/4}`). Both were checked numerically (Fourier eigenvectors at 60 digits;
Sips: `h = 10, 20, 40`, `m ≤ 2`, `λ ∈ {0, 0.5, 1}`; Goldstein: `h = 6, 9, 12`, `m ≤ 2`,
`μ ∈ {1.5, 2.5}`). DLMF notes that Sips' results are derived formally.

The uniform approximations of Barrett and Dunster (§28.8(iv)) are described only in words in
DLMF and are not acquired.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Mathieu

/-! ### Eigenvalues (§28.8(i)) -/

/-- **DLMF 28.8.1** (`a_m`): with `s = 2m + 1`, as `h → +∞`,
`a_m(h²) = -2h² + 2sh - (s²+1)/8 - (s³+3s)/(2⁷h) - (5s⁴+34s²+9)/(2¹²h²)
- (33s⁵+410s³+405s)/(2¹⁷h³) - (63s⁶+1260s⁴+2943s²+486)/(2²⁰h⁴)
- (527s⁷+15617s⁵+69001s³+41607s)/(2²⁵h⁵) + O(h⁻⁶)`. -/
@[dlmf 28.8.E1]
theorem mathieuA_large_q (m : ℕ) :
    (fun h : ℝ => mathieuA m (h ^ 2) - (-2 * h ^ 2 + 2 * (2 * m + 1 : ℝ) * h -
      ((2 * m + 1 : ℝ) ^ 2 + 1) / 8 - ((2 * m + 1 : ℝ) ^ 3 + 3 * (2 * m + 1)) / (2 ^ 7 * h) -
      (5 * (2 * m + 1 : ℝ) ^ 4 + 34 * (2 * m + 1) ^ 2 + 9) / (2 ^ 12 * h ^ 2) -
      (33 * (2 * m + 1 : ℝ) ^ 5 + 410 * (2 * m + 1) ^ 3 + 405 * (2 * m + 1)) / (2 ^ 17 * h ^ 3) -
      (63 * (2 * m + 1 : ℝ) ^ 6 + 1260 * (2 * m + 1) ^ 4 + 2943 * (2 * m + 1) ^ 2 + 486) /
        (2 ^ 20 * h ^ 4) -
      (527 * (2 * m + 1 : ℝ) ^ 7 + 15617 * (2 * m + 1) ^ 5 + 69001 * (2 * m + 1) ^ 3 +
        41607 * (2 * m + 1)) / (2 ^ 25 * h ^ 5))) =O[atTop] (fun h => h⁻¹ ^ 6) := by
  sorry

/-- **DLMF 28.8.1** (`b_{m+1}`): `b_{m+1}(h²)` has the same expansion as `a_m(h²)`. -/
@[dlmf 28.8.E1]
theorem mathieuB_large_q (m : ℕ) :
    (fun h : ℝ => mathieuB (m + 1) (h ^ 2) - (-2 * h ^ 2 + 2 * (2 * m + 1 : ℝ) * h -
      ((2 * m + 1 : ℝ) ^ 2 + 1) / 8 - ((2 * m + 1 : ℝ) ^ 3 + 3 * (2 * m + 1)) / (2 ^ 7 * h) -
      (5 * (2 * m + 1 : ℝ) ^ 4 + 34 * (2 * m + 1) ^ 2 + 9) / (2 ^ 12 * h ^ 2) -
      (33 * (2 * m + 1 : ℝ) ^ 5 + 410 * (2 * m + 1) ^ 3 + 405 * (2 * m + 1)) / (2 ^ 17 * h ^ 3) -
      (63 * (2 * m + 1 : ℝ) ^ 6 + 1260 * (2 * m + 1) ^ 4 + 2943 * (2 * m + 1) ^ 2 + 486) /
        (2 ^ 20 * h ^ 4) -
      (527 * (2 * m + 1 : ℝ) ^ 7 + 15617 * (2 * m + 1) ^ 5 + 69001 * (2 * m + 1) ^ 3 +
        41607 * (2 * m + 1)) / (2 ^ 25 * h ^ 5))) =O[atTop] (fun h => h⁻¹ ^ 6) := by
  sorry

/-- **DLMF 28.8.2**: as `h → +∞`,
`b_{m+1}(h²) - a_m(h²) = 2^{4m+5}/m! (2/π)^{1/2} h^{m+3/2} e^{-4h}
(1 - (6m²+14m+7)/(32h) + O(h⁻²))`. -/
@[dlmf 28.8.E2]
theorem mathieuB_sub_mathieuA_large_q (m : ℕ) :
    ∃ ε : ℝ → ℝ, ε =O[atTop] (fun h => h⁻¹ ^ 2) ∧ ∀ᶠ h in atTop,
      mathieuB (m + 1) (h ^ 2) - mathieuA m (h ^ 2) =
        2 ^ (4 * m + 5) / (m.factorial : ℝ) * Real.sqrt (2 / π) * h ^ ((m : ℝ) + 3 / 2) *
          Real.exp (-4 * h) * (1 - (6 * (m : ℝ) ^ 2 + 14 * m + 7) / (32 * h) + ε h) := by
  sorry

/-! ### Sips' expansions (§28.8(ii)) -/

/-- **Sips' expansions** (DLMF 28.8.3–28.8.7): let `|λ| < 2^{1/4}`, `x = π/2 + λh^{-1/4}`,
`ξ = 2√h cos x` and `D_k(ξ) = e^{-ξ²/4} He_k(ξ)`. Then, as `h → +∞`,
`ce_m(x, h²) = Ĉ_m (U_m(ξ) + V_m(ξ))` and `se_{m+1}(x, h²)/sin x = Ŝ_m (U_m(ξ) - V_m(ξ))`, where
`U_m`, `V_m`, `Ĉ_m`, `Ŝ_m` have the asymptotic expansions 28.8.4–28.8.7. With these expansions
truncated after the `h⁻²` terms, the relative error is `O(h⁻³)`. (`D_k` with `k < 0` only
occurs with vanishing binomial coefficients.) -/
@[dlmf 28.8.E3, dlmf 28.8.E4, dlmf 28.8.E5, dlmf 28.8.E6, dlmf 28.8.E7]
theorem mathieu_sips (m : ℕ) {lam : ℝ} (hlam : |lam| < 2 ^ (1 / 4 : ℝ)) :
    let x : ℝ → ℝ := fun h => π / 2 + lam * h ^ (-(1 / 4 : ℝ))
    let ξ : ℝ → ℝ := fun h => 2 * Real.sqrt h * Real.cos (x h)
    let D : ℕ → ℝ → ℝ := fun k t => Real.exp (-t ^ 2 / 4) * Polynomial.aeval t
      (Polynomial.hermite k)
    let U : ℝ → ℝ := fun h => D m (ξ h) -
      (D (m + 4) (ξ h) - 24 * (m.choose 4 : ℝ) * D (m - 4) (ξ h)) / (2 ^ 6 * h) +
      (D (m + 8) (ξ h) - 2 ^ 5 * (m + 2 : ℝ) * D (m + 4) (ξ h) +
        24 * 2 ^ 5 * ((m : ℝ) - 1) * (m.choose 4 : ℝ) * D (m - 4) (ξ h) +
        (Nat.factorial 8 : ℝ) * (m.choose 8 : ℝ) * D (m - 8) (ξ h)) / (2 ^ 13 * h ^ 2)
    let V : ℝ → ℝ := fun h =>
      (-D (m + 2) (ξ h) - (m : ℝ) * (m - 1) * D (m - 2) (ξ h)) / (2 ^ 4 * h) +
      (D (m + 6) (ξ h) + ((m : ℝ) ^ 2 - 25 * m - 36) * D (m + 2) (ξ h) -
        (m : ℝ) * (m - 1) * ((m : ℝ) ^ 2 + 27 * m - 10) * D (m - 2) (ξ h) -
        (Nat.factorial 6 : ℝ) * (m.choose 6 : ℝ) * D (m - 6) (ξ h)) / (2 ^ 10 * h ^ 2)
    let Chat : ℝ → ℝ := fun h => (π * h / (2 * (m.factorial : ℝ) ^ 2)) ^ (1 / 4 : ℝ) *
      (1 + (2 * m + 1 : ℝ) / (8 * h) +
        ((m : ℝ) ^ 4 + 2 * m ^ 3 + 263 * m ^ 2 + 262 * m + 108) / (2048 * h ^ 2)) ^ (-(1 / 2 : ℝ))
    let Shat : ℝ → ℝ := fun h => (π * h / (2 * (m.factorial : ℝ) ^ 2)) ^ (1 / 4 : ℝ) *
      (1 - (2 * m + 1 : ℝ) / (8 * h) +
        ((m : ℝ) ^ 4 + 2 * m ^ 3 - 121 * m ^ 2 - 122 * m - 84) / (2048 * h ^ 2)) ^ (-(1 / 2 : ℝ))
    ∃ ε₁ ε₂ : ℝ → ℂ, ε₁ =O[atTop] (fun h => h⁻¹ ^ 3) ∧ ε₂ =O[atTop] (fun h => h⁻¹ ^ 3) ∧
      ∀ᶠ h in atTop,
        mathieuCe m (x h) (h ^ 2) = (Chat h * (U h + V h) : ℝ) * (1 + ε₁ h) ∧
        mathieuSe (m + 1) (x h) (h ^ 2) / Real.sin (x h) =
          (Shat h * (U h - V h) : ℝ) * (1 + ε₂ h) := by
  sorry

/-! ### Goldstein's expansions (§28.8(iii)) -/

/-- **Goldstein's expansions** (DLMF 28.8.8–28.8.12): let `μ ≥ 1`, `x = π/2 - μh^{-1/4}`,
`s = 2m + 1`. As `h → +∞`,
`ce_m(x, h²)/ce_m(0, h²) = 2^{m-1/2}/σ_m (W⁺(P_m - Q_m) + W⁻(P_m + Q_m))` and
`se_{m+1}(x, h²)/se'_{m+1}(0, h²) = 2^{m-1/2}/τ_{m+1} (W⁺(P_m - Q_m) - W⁻(P_m + Q_m))` with
`W^± = e^{±2h sin x} (cos x)^{-m-1} (cos(x/2 + π/4))^{2m+1}` resp. `(sin(x/2 + π/4))^{2m+1}`
(28.8.9) and the asymptotic series 28.8.10–28.8.12 for `σ_m`, `τ_{m+1}`, `P_m`, `Q_m`. With the
printed truncations, the relative error is `O(h⁻¹)`. -/
@[dlmf 28.8.E8, dlmf 28.8.E9, dlmf 28.8.E10, dlmf 28.8.E11, dlmf 28.8.E12]
theorem mathieu_goldstein (m : ℕ) {μ : ℝ} (hμ : 1 ≤ μ) :
    let s : ℝ := 2 * m + 1
    let x : ℝ → ℝ := fun h => π / 2 - μ * h ^ (-(1 / 4 : ℝ))
    let Wp : ℝ → ℝ := fun h => Real.exp (2 * h * Real.sin (x h)) / Real.cos (x h) ^ (m + 1) *
      Real.cos (x h / 2 + π / 4) ^ (2 * m + 1)
    let Wm : ℝ → ℝ := fun h => Real.exp (-2 * h * Real.sin (x h)) / Real.cos (x h) ^ (m + 1) *
      Real.sin (x h / 2 + π / 4) ^ (2 * m + 1)
    let σ : ℝ → ℝ := fun h => 1 + s / (2 ^ 3 * h) + (4 * s ^ 2 + 3) / (2 ^ 7 * h ^ 2) +
      (19 * s ^ 3 + 59 * s) / (2 ^ 11 * h ^ 3)
    let τ : ℝ → ℝ := fun h => 2 * h - s / 4 - (2 * s ^ 2 + 3) / (2 ^ 6 * h) -
      (7 * s ^ 3 + 47 * s) / (2 ^ 10 * h ^ 2)
    let P : ℝ → ℝ := fun h => 1 + s / (2 ^ 3 * h * Real.cos (x h) ^ 2) +
      ((s ^ 4 + 86 * s ^ 2 + 105) / (2 ^ 11 * Real.cos (x h) ^ 4) -
        (s ^ 4 + 22 * s ^ 2 + 57) / (2 ^ 11 * Real.cos (x h) ^ 2)) / h ^ 2
    let Q : ℝ → ℝ := fun h => Real.sin (x h) / Real.cos (x h) ^ 2 *
      ((s ^ 2 + 3) / (2 ^ 5 * h) +
        (s ^ 3 + 3 * s + (4 * s ^ 3 + 44 * s) / Real.cos (x h) ^ 2) / (2 ^ 9 * h ^ 2))
    ∃ ε₁ ε₂ : ℝ → ℂ, ε₁ =O[atTop] (fun h => h⁻¹) ∧ ε₂ =O[atTop] (fun h => h⁻¹) ∧
      ∀ᶠ h in atTop,
        mathieuCe m (x h) (h ^ 2) / mathieuCe m 0 (h ^ 2) =
          (2 ^ ((m : ℝ) - 1 / 2) / σ h * (Wp h * (P h - Q h) + Wm h * (P h + Q h)) : ℝ) *
            (1 + ε₁ h) ∧
        mathieuSe (m + 1) (x h) (h ^ 2) / deriv (fun z => mathieuSe (m + 1) z (h ^ 2)) 0 =
          (2 ^ ((m : ℝ) - 1 / 2) / τ h * (Wp h * (P h - Q h) - Wm h * (P h + Q h)) : ℝ) *
            (1 + ε₂ h) := by
  sorry

end DLMF.Mathieu
