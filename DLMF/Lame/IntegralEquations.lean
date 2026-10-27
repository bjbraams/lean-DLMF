/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Basic
public import DLMF.Lame.Basic

/-!
# Lamé functions: integral equations (DLMF §29.8)

The integral equation 29.8.2 for a solution `w` of Lamé's equation 29.2.1 with
`w(z + 2K) = σw(z)` and its special cases 29.8.5, 29.8.7–29.8.9 for the Lamé functions.

Convention: DLMF writes the kernel as the Ferrers function `𝖯_ν`, but the arguments `x` of
29.8.1 and `y = dn(z) dn(z₁)/k'` of 29.8.6 are not confined to `[-1, 1]` (for real `z, z₁`,
`k' ≤ dn ≤ 1` gives `y ∈ [k', 1/k']`, which straddles `1`). The function meant is the
hypergeometric function `F(-ν, ν + 1; 1; (1 - x)/2)`, which is the Legendre function `P_ν` of
§14.3(ii) and agrees with `𝖯_ν` on `(-1, 1)`; it is `DLMF.Legendre.legendreP ν` (complex,
principal branch, the real kernel being its restriction). With this reading 29.8.2, 29.8.5 and
29.8.7–29.8.9 were verified numerically for `ν = 2.7`, `k = 0.6` (ratios `1 ± 10⁻¹²`), the
second solution `w₂` being computed by shooting. The Wronskian of two solutions of 29.2.1 is
constant (no first-derivative term), so it is evaluated at `0`.
All statements are admitted.
-/

@[expose] public section

open DLMF.JacobiElliptic DLMF.Elliptic
open scoped Real

noncomputable section

namespace DLMF.Lame

variable {h ν k : ℝ}

/-- 29.8.2–29.8.4: let `w` solve 29.2.1 with `w(z + 2K) = σw(z)`, `σ = ±1` (so `w` has period
`4K`), and let `w₂` be a second solution with `w₂(z + 2K) = τw(z) + σw₂(z)` and nonzero
Wronskian `W = w w₂' - w' w₂`. Then with `μ = 2στ/W` and (29.8.1)
`x = k² sn z sn z₁ sn z₂ sn z₃ - (k²/k'²) cn z cn z₁ cn z₂ cn z₃ + (1/k'²) dn z dn z₁ dn z₂ dn z₃`,
`μ w(z₁) w(z₂) w(z₃) = ∫_{-2K}^{2K} P_ν(x) w(z) dz` for real `z₁, z₂, z₃`. `P_ν` is
`DLMF.Legendre.legendreP` (see the module docstring). Admitted. -/
@[dlmf 29.8.E1, dlmf 29.8.E2, dlmf 29.8.E3, dlmf 29.8.E4]
theorem Real.lame_integral_equation (hk0 : 0 < k) (hk1 : k < 1) {w w₂ : ℝ → ℝ}
    (hw : Real.IsLameSolution h ν k w) (hw₂ : Real.IsLameSolution h ν k w₂) {σ τ : ℝ}
    (hσ : σ = 1 ∨ σ = -1)
    (hwσ : ∀ z, w (z + 2 * Real.compEllIntKm (k ^ 2)) = σ * w z)
    (hw₂τ : ∀ z, w₂ (z + 2 * Real.compEllIntKm (k ^ 2)) = τ * w z + σ * w₂ z)
    (hW : w 0 * deriv w₂ 0 - deriv w 0 * w₂ 0 ≠ 0) (z₁ z₂ z₃ : ℝ) :
    ((2 * σ * τ / (w 0 * deriv w₂ 0 - deriv w 0 * w₂ 0) * w z₁ * w z₂ * w z₃ : ℝ) : ℂ) =
      ∫ z in (-(2 * Real.compEllIntKm (k ^ 2)))..(2 * Real.compEllIntKm (k ^ 2)),
        DLMF.Legendre.legendreP ν
            ((k ^ 2 * Real.jacobiSnm z (k ^ 2) * Real.jacobiSnm z₁ (k ^ 2) *
                Real.jacobiSnm z₂ (k ^ 2) * Real.jacobiSnm z₃ (k ^ 2) -
              k ^ 2 / (1 - k ^ 2) * Real.jacobiCnm z (k ^ 2) * Real.jacobiCnm z₁ (k ^ 2) *
                Real.jacobiCnm z₂ (k ^ 2) * Real.jacobiCnm z₃ (k ^ 2) +
              1 / (1 - k ^ 2) * Real.jacobiDnm z (k ^ 2) * Real.jacobiDnm z₁ (k ^ 2) *
                Real.jacobiDnm z₂ (k ^ 2) * Real.jacobiDnm z₃ (k ^ 2) : ℝ) : ℂ) *
          (w z : ℂ) := by
  sorry

/-- 29.8.5–29.8.6: for a solution `w₂` of 29.2.1 (with `h = a^{2m}_ν(k²)`) independent of
`Ec^{2m}_ν`, `Ec^{2m}_ν(z₁, k²) (w₂(K) - w₂(-K))/w₂'(0) = ∫_{-K}^K P_ν(y) Ec^{2m}_ν(z, k²) dz`
with `y = dn(z, k) dn(z₁, k)/k'`. Admitted. -/
@[dlmf 29.8.E5, dlmf 29.8.E6]
theorem Real.lameEck_even_integral_equation (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) {w₂ : ℝ → ℝ}
    (hw₂ : Real.IsLameSolution (Real.lameAk ν (2 * m) k) ν k w₂)
    (hind : Real.lameEck ν (2 * m) 0 k * deriv w₂ 0 -
      deriv (fun z => Real.lameEck ν (2 * m) z k) 0 * w₂ 0 ≠ 0) (z₁ : ℝ) :
    ((Real.lameEck ν (2 * m) z₁ k *
        ((w₂ (Real.compEllIntKm (k ^ 2)) - w₂ (-Real.compEllIntKm (k ^ 2))) / deriv w₂ 0) :
        ℝ) : ℂ) =
      ∫ z in (-Real.compEllIntKm (k ^ 2))..Real.compEllIntKm (k ^ 2),
        DLMF.Legendre.legendreP ν
            ((Real.jacobiDnm z (k ^ 2) * Real.jacobiDnm z₁ (k ^ 2) / Real.sqrt (1 - k ^ 2) :
              ℝ) : ℂ) *
          (Real.lameEck ν (2 * m) z k : ℂ) := by
  sorry

/-- 29.8.7: `Ec^{2m+1}_ν(z₁, k²) (w₂(K) + w₂(-K))/w₂(0) =
-k² sn(z₁, k) ∫_{-K}^K sn(z, k) P_ν'(y) Ec^{2m+1}_ν(z, k²) dz` (`h = a^{2m+1}_ν(k²)`, `w₂`
independent of `Ec^{2m+1}_ν`, `y` as in 29.8.6). Admitted. -/
@[dlmf 29.8.E7]
theorem Real.lameEck_odd_integral_equation (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) {w₂ : ℝ → ℝ}
    (hw₂ : Real.IsLameSolution (Real.lameAk ν (2 * m + 1) k) ν k w₂)
    (hind : Real.lameEck ν (2 * m + 1) 0 k * deriv w₂ 0 -
      deriv (fun z => Real.lameEck ν (2 * m + 1) z k) 0 * w₂ 0 ≠ 0) (z₁ : ℝ) :
    ((Real.lameEck ν (2 * m + 1) z₁ k *
        ((w₂ (Real.compEllIntKm (k ^ 2)) + w₂ (-Real.compEllIntKm (k ^ 2))) / w₂ 0) : ℝ) : ℂ) =
      ((-(k ^ 2 * Real.jacobiSnm z₁ (k ^ 2)) : ℝ) : ℂ) *
        ∫ z in (-Real.compEllIntKm (k ^ 2))..Real.compEllIntKm (k ^ 2),
          (Real.jacobiSnm z (k ^ 2) : ℂ) *
            deriv (DLMF.Legendre.legendreP ν)
              ((Real.jacobiDnm z (k ^ 2) * Real.jacobiDnm z₁ (k ^ 2) / Real.sqrt (1 - k ^ 2) :
                ℝ) : ℂ) *
            (Real.lameEck ν (2 * m + 1) z k : ℂ) := by
  sorry

/-- 29.8.8: `Es^{2m+1}_ν(z₁, k²) (w₂'(K) + w₂'(-K))/w₂'(0) =
(k²/k') cn(z₁, k) ∫_{-K}^K cn(z, k) P_ν'(y) Es^{2m+1}_ν(z, k²) dz` (`h = b^{2m+1}_ν(k²)`, `w₂`
independent of `Es^{2m+1}_ν`). Admitted. -/
@[dlmf 29.8.E8]
theorem Real.lameEsk_odd_integral_equation (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) {w₂ : ℝ → ℝ}
    (hw₂ : Real.IsLameSolution (Real.lameBk ν (2 * m + 1) k) ν k w₂)
    (hind : Real.lameEsk ν (2 * m + 1) 0 k * deriv w₂ 0 -
      deriv (fun z => Real.lameEsk ν (2 * m + 1) z k) 0 * w₂ 0 ≠ 0) (z₁ : ℝ) :
    ((Real.lameEsk ν (2 * m + 1) z₁ k *
        ((deriv w₂ (Real.compEllIntKm (k ^ 2)) + deriv w₂ (-Real.compEllIntKm (k ^ 2))) /
          deriv w₂ 0) : ℝ) : ℂ) =
      ((k ^ 2 / Real.sqrt (1 - k ^ 2) * Real.jacobiCnm z₁ (k ^ 2) : ℝ) : ℂ) *
        ∫ z in (-Real.compEllIntKm (k ^ 2))..Real.compEllIntKm (k ^ 2),
          (Real.jacobiCnm z (k ^ 2) : ℂ) *
            deriv (DLMF.Legendre.legendreP ν)
              ((Real.jacobiDnm z (k ^ 2) * Real.jacobiDnm z₁ (k ^ 2) / Real.sqrt (1 - k ^ 2) :
                ℝ) : ℂ) *
            (Real.lameEsk ν (2 * m + 1) z k : ℂ) := by
  sorry

/-- 29.8.9: `Es^{2m+2}_ν(z₁, k²) (w₂'(K) - w₂'(-K))/w₂(0) =
-(k⁴/k') sn(z₁, k) cn(z₁, k) ∫_{-K}^K sn(z, k) cn(z, k) P_ν''(y) Es^{2m+2}_ν(z, k²) dz`
(`h = b^{2m+2}_ν(k²)`, `w₂` independent of `Es^{2m+2}_ν`). Admitted. -/
@[dlmf 29.8.E9]
theorem Real.lameEsk_even_integral_equation (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ) {w₂ : ℝ → ℝ}
    (hw₂ : Real.IsLameSolution (Real.lameBk ν (2 * m + 2) k) ν k w₂)
    (hind : Real.lameEsk ν (2 * m + 2) 0 k * deriv w₂ 0 -
      deriv (fun z => Real.lameEsk ν (2 * m + 2) z k) 0 * w₂ 0 ≠ 0) (z₁ : ℝ) :
    ((Real.lameEsk ν (2 * m + 2) z₁ k *
        ((deriv w₂ (Real.compEllIntKm (k ^ 2)) - deriv w₂ (-Real.compEllIntKm (k ^ 2))) /
          w₂ 0) : ℝ) : ℂ) =
      ((-(k ^ 4 / Real.sqrt (1 - k ^ 2) * Real.jacobiSnm z₁ (k ^ 2) *
          Real.jacobiCnm z₁ (k ^ 2)) : ℝ) : ℂ) *
        ∫ z in (-Real.compEllIntKm (k ^ 2))..Real.compEllIntKm (k ^ 2),
          (Real.jacobiSnm z (k ^ 2) * Real.jacobiCnm z (k ^ 2) : ℂ) *
            deriv (deriv (DLMF.Legendre.legendreP ν))
              ((Real.jacobiDnm z (k ^ 2) * Real.jacobiDnm z₁ (k ^ 2) / Real.sqrt (1 - k ^ 2) :
                ℝ) : ℂ) *
            (Real.lameEsk ν (2 * m + 2) z k : ℂ) := by
  sorry

end DLMF.Lame
