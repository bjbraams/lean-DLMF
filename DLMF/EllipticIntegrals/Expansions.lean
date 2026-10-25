/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.LegendreIdentities

/-!
# Maclaurin and related expansions of Legendre's integrals (DLMF §19.5)

Complex-modulus forms of DLMF 19.5.1–19.5.11. Series are stated with `HasSum`; the Appell
function is the project's `DLMF.Hypergeometric.appF1` (DLMF 16.13.1, the totalized double
series) — written out here as the `tsum` over `ℕ × ℕ` of the terms `ei19a_appF1Term`, because the module
`DLMF.GeneralizedHypergeometric.Appell` cannot be imported together with `lean-codes` (both
import a declaration `DifferentiableOn.analyticOnNhd_of_finiteDimensional`, from TauCeti and
from `SeveralComplexVariables`) — and `₂F₁` is Mathlib's `ordinaryHypergeometric`. The nome
is the Chapter 22 definition
`DLMF.JacobiElliptic.jacobiNomek k = exp(-πK'(k)/K(k))` (with the literal `K'`, which is DLMF's
`K'` for `Re k > 0`). The expansions 19.5.5–19.5.6 with "`+ ⋯`" are stated as `O`-estimates of
the remainder as `k → 0+`.

The real-parameter forms of 19.5.1–19.5.2 are the existing
`DLMF.Elliptic.Real.compEllIntKm_eq_ordinaryHypergeometric` and
`Real.compEllIntEm_eq_ordinaryHypergeometric` (tagged there); all statements of this module are
admitted.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Real Topology

namespace DLMF.EllipticIntegrals

open DLMF.JacobiElliptic DLMF.Hypergeometric

/-- The `(p₁, p₂)` term of Appell's double series
`F₁(a; b, b'; c; x, y) = ∑ (a)_{p₁+p₂} (b)_{p₁} (b')_{p₂}/((c)_{p₁+p₂} p₁! p₂!) x^{p₁} y^{p₂}`
(DLMF 16.13.1), summed with `tsum` over `ℕ × ℕ` below. -/
def ei19a_appF1Term (a b b' c x y : ℂ) (p : ℕ × ℕ) : ℂ :=
  poch a (p.1 + p.2) * poch b p.1 * poch b' p.2 /
    (poch c (p.1 + p.2) * (Nat.factorial p.1 * Nat.factorial p.2 : ℂ)) * x ^ p.1 * y ^ p.2

/-- **Admitted.** DLMF 19.5.1: for `|k| < 1`,
`K(k) = (π/2) ∑ₘ (1/2)ₘ (1/2)ₘ/(m! m!) k^{2m} = (π/2) ₂F₁(1/2, 1/2; 1; k²)`. -/
@[dlmf 19.5.E1]
theorem compEllIntKk_hasSum {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => (π / 2 : ℂ) *
        (poch (1 / 2) m * poch (1 / 2) m / (Nat.factorial m * Nat.factorial m : ℂ)) *
        k ^ (2 * m)) (compEllIntKk k) ∧
      compEllIntKk k = (π / 2 : ℂ) * ₂F₁ (1 / 2 : ℂ) (1 / 2) 1 (k ^ 2) := by
  sorry

/-- **Admitted.** DLMF 19.5.2: for `|k| < 1`,
`E(k) = (π/2) ∑ₘ (-1/2)ₘ (1/2)ₘ/(m! m!) k^{2m} = (π/2) ₂F₁(-1/2, 1/2; 1; k²)`. -/
@[dlmf 19.5.E2]
theorem compEllIntEk_hasSum {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => (π / 2 : ℂ) *
        (poch (-(1 / 2)) m * poch (1 / 2) m / (Nat.factorial m * Nat.factorial m : ℂ)) *
        k ^ (2 * m)) (compEllIntEk k) ∧
      compEllIntEk k = (π / 2 : ℂ) * ₂F₁ (-(1 / 2) : ℂ) (1 / 2) 1 (k ^ 2) := by
  sorry

/-- **Admitted.** DLMF 19.5.3: for `|k| < 1`,
`D(k) = (π/4) ∑ₘ (3/2)ₘ (1/2)ₘ/((m+1)! m!) k^{2m} = (π/4) ₂F₁(3/2, 1/2; 2; k²)`. -/
@[dlmf 19.5.E3]
theorem compEllIntDk_hasSum {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => (π / 4 : ℂ) *
        (poch (3 / 2) m * poch (1 / 2) m / (Nat.factorial (m + 1) * Nat.factorial m : ℂ)) *
        k ^ (2 * m)) (compEllIntDk k) ∧
      compEllIntDk k = (π / 4 : ℂ) * ₂F₁ (3 / 2 : ℂ) (1 / 2) 2 (k ^ 2) := by
  sorry

/-- **Admitted.** DLMF 19.5.4: for `|k| < 1` and `|α| < 1` (here `|α²| < 1`),
`Π(α², k) = (π/2) ∑ₙ (1/2)ₙ/n! ∑_{m ≤ n} (1/2)ₘ/m! k^{2m} α^{2n-2m}
= (π/2) F₁(1/2; 1/2, 1; 1; k², α²)`. -/
@[dlmf 19.5.E4]
theorem compEllIntPik_hasSum {α2 k : ℂ} (hk : ‖k‖ < 1) (hα : ‖α2‖ < 1) :
    HasSum (fun n : ℕ => (π / 2 : ℂ) * (poch (1 / 2) n / Nat.factorial n *
        ∑ m ∈ Finset.range (n + 1), poch (1 / 2) m / Nat.factorial m * k ^ (2 * m) * α2 ^ (n - m)))
        (compEllIntPik α2 k) ∧
      compEllIntPik α2 k = (π / 2 : ℂ) * ∑' p : ℕ × ℕ, ei19a_appF1Term (1 / 2) (1 / 2) 1 1 (k ^ 2) α2 p := by
  sorry

/-- **Admitted.** DLMF 19.5.4_1: for real `|φ| < π/2` and `|k| < 1`,
`F(φ, k) = ∑ₘ (1/2)ₘ sin^{2m+1}φ/((2m+1) m!) ₂F₁(m + 1/2, 1/2; m + 3/2; sin²φ) k^{2m}
= sin φ F₁(1/2; 1/2, 1/2; 3/2; sin²φ, k² sin²φ)`. -/
@[dlmf 19.5.E4_1]
theorem incEllIntFk_hasSum {φ : ℝ} (hφ : |φ| < π / 2) {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => poch (1 / 2) m * (Real.sin φ : ℂ) ^ (2 * m + 1) /
        ((2 * m + 1) * Nat.factorial m : ℂ) *
        ₂F₁ ((m : ℂ) + 1 / 2) (1 / 2) ((m : ℂ) + 3 / 2) ((Real.sin φ : ℂ) ^ 2) * k ^ (2 * m))
        (incEllIntFk φ k) ∧
      incEllIntFk φ k = Real.sin φ * ∑' p : ℕ × ℕ,
        ei19a_appF1Term (1 / 2) (1 / 2) (1 / 2) (3 / 2) ((Real.sin φ : ℂ) ^ 2)
          (k ^ 2 * (Real.sin φ : ℂ) ^ 2) p := by
  sorry

/-- **Admitted.** DLMF 19.5.4_2: for real `|φ| < π/2` and `|k| < 1`,
`E(φ, k) = ∑ₘ (-1/2)ₘ sin^{2m+1}φ/((2m+1) m!) ₂F₁(m + 1/2, 1/2; m + 3/2; sin²φ) k^{2m}
= sin φ F₁(1/2; 1/2, -1/2; 3/2; sin²φ, k² sin²φ)`. -/
@[dlmf 19.5.E4_2]
theorem incEllIntEk_hasSum {φ : ℝ} (hφ : |φ| < π / 2) {k : ℂ} (hk : ‖k‖ < 1) :
    HasSum (fun m : ℕ => poch (-(1 / 2)) m * (Real.sin φ : ℂ) ^ (2 * m + 1) /
        ((2 * m + 1) * Nat.factorial m : ℂ) *
        ₂F₁ ((m : ℂ) + 1 / 2) (1 / 2) ((m : ℂ) + 3 / 2) ((Real.sin φ : ℂ) ^ 2) * k ^ (2 * m))
        (incEllIntEk φ k) ∧
      incEllIntEk φ k = Real.sin φ * ∑' p : ℕ × ℕ,
        ei19a_appF1Term (1 / 2) (1 / 2) (-(1 / 2)) (3 / 2) ((Real.sin φ : ℂ) ^ 2)
          (k ^ 2 * (Real.sin φ : ℂ) ^ 2) p := by
  sorry

/-- **Admitted.** DLMF 19.5.4_3: for real `|φ| < π/2`, `|k| < 1` and `|α²| < 1`,
`Π(φ, α², k) = ∑ₘ (1/2)ₘ sin^{2m+1}φ/((2m+1) m!) F₁(m + 1/2; 1/2, 1; m + 3/2; sin²φ, α² sin²φ)
k^{2m}`. -/
@[dlmf 19.5.E4_3]
theorem incEllIntPik_hasSum {φ : ℝ} (hφ : |φ| < π / 2) {α2 k : ℂ} (hk : ‖k‖ < 1)
    (hα : ‖α2‖ < 1) :
    HasSum (fun m : ℕ => poch (1 / 2) m * (Real.sin φ : ℂ) ^ (2 * m + 1) /
        ((2 * m + 1) * Nat.factorial m : ℂ) *
        (∑' p : ℕ × ℕ, ei19a_appF1Term ((m : ℂ) + 1 / 2) (1 / 2) 1 ((m : ℂ) + 3 / 2)
          ((Real.sin φ : ℂ) ^ 2) (α2 * (Real.sin φ : ℂ) ^ 2) p) * k ^ (2 * m))
        (incEllIntPik φ α2 k) := by
  sorry

/-- **Admitted.** DLMF 19.5.5: Jacobi's nome `q = exp(-πK'(k)/K(k)) = r + 8r² + 84r³ + 992r⁴ + ⋯`
with `r = k²/16`, as `k → 0+` (the remainder is `O(r⁵)`). -/
@[dlmf 19.5.E5]
theorem jacobiNomek_isBigO :
    (fun k : ℝ => jacobiNomek k - ((k ^ 2 / 16 : ℝ) + 8 * (k ^ 2 / 16 : ℝ) ^ 2 +
        84 * (k ^ 2 / 16 : ℝ) ^ 3 + 992 * (k ^ 2 / 16 : ℝ) ^ 4 : ℂ)) =O[𝓝[>] 0]
      fun k : ℝ => (k ^ 2 / 16) ^ 5 := by
  sorry

/-- **Admitted.** DLMF 19.5.6–19.5.7: with `λ = (1 - √k')/(2(1 + √k'))`,
`q = λ + 2λ⁵ + 15λ⁹ + 150λ¹³ + 1707λ¹⁷ + ⋯` as `k → 0+` (the remainder is `O(λ²¹)`). -/
@[dlmf 19.5.E6, dlmf 19.5.E7]
theorem jacobiNomek_isBigO_lambda :
    let lam : ℝ → ℝ := fun k =>
      (1 - Real.sqrt (Real.sqrt (1 - k ^ 2))) / (2 * (1 + Real.sqrt (Real.sqrt (1 - k ^ 2))))
    (fun k : ℝ => jacobiNomek k - ((lam k + 2 * lam k ^ 5 + 15 * lam k ^ 9 + 150 * lam k ^ 13 +
        1707 * lam k ^ 17 : ℝ) : ℂ)) =O[𝓝[>] 0] fun k : ℝ => lam k ^ 21 := by
  sorry

/-- **Admitted.** DLMF 19.5.8: `K(k) = (π/2)(1 + 2∑_{n ≥ 1} q^{n²})²` with `q = jacobiNomek k`, on
`jacobiModulusDomain` (`Re k > 0`, `k ∉ [1, ∞)`, where `|q| < 1`). -/
@[dlmf 19.5.E8]
theorem compEllIntKk_eq_nome_series {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    compEllIntKk k = (π / 2 : ℂ) * (1 + 2 * ∑' n : ℕ, jacobiNomek k ^ ((n + 1) ^ 2)) ^ 2 := by
  sorry

/-- **Admitted.** DLMF 19.5.9:
`E(k) = K(k) + (2π²/K(k)) ∑_{n≥1} (-1)ⁿ n² q^{n²} / (1 + 2∑_{n≥1} (-1)ⁿ q^{n²})` on
`jacobiModulusDomain`. -/
@[dlmf 19.5.E9]
theorem compEllIntEk_eq_nome_series {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    compEllIntEk k = compEllIntKk k + 2 * π ^ 2 / compEllIntKk k *
      ((∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * ((n + 1 : ℕ) : ℂ) ^ 2 * jacobiNomek k ^ ((n + 1) ^ 2)) /
        (1 + 2 * ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * jacobiNomek k ^ ((n + 1) ^ 2))) := by
  sorry

/-- The descending Landen sequence of moduli of DLMF 19.5.11: `k₀ = k`,
`k_{m+1} = (1 - √(1 - k_m²))/(1 + √(1 - k_m²))` (principal square roots). -/
@[dlmf 19.5.E11]
def landenModulusSeq (k : ℂ) : ℕ → ℂ
  | 0 => k
  | m + 1 =>
    (1 - (1 - landenModulusSeq k m ^ 2) ^ (1 / 2 : ℂ)) /
      (1 + (1 - landenModulusSeq k m ^ 2) ^ (1 / 2 : ℂ))

/-- **Admitted.** DLMF 19.5.10: `K(k) = (π/2) ∏_{m ≥ 1} (1 + k_m)` with the moduli of 19.5.11, in
the principal domain `1 - k² ∈ ℂ \ (-∞, 0]` (natural-order partial products). -/
@[dlmf 19.5.E10]
theorem compEllIntKk_eq_landen_prod {k : ℂ} (hk : 1 - k ^ 2 ∈ slitPlane) :
    Tendsto (fun N => (π / 2 : ℂ) * ∏ m ∈ Finset.range N, (1 + landenModulusSeq k (m + 1))) atTop
      (𝓝 (compEllIntKk k)) := by
  sorry

end DLMF.EllipticIntegrals
