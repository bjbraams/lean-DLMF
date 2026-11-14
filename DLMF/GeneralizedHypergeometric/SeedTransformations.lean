/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic

/-!
# Hypergeometric transformation generators and beta transforms

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018), §8.5,
(8.32)–(8.45), synopses RL-8.16/18/19/21/23/24. Germ identities use
ordinary globally regular lower parameters. Singular simultaneous terminating
specializations require separate limits, not arbitrary finite truncation.
-/

@[expose] public noncomputable section
open Complex Filter
open scoped Topology Real
namespace DLMF.Hypergeometric

/-- Contiguous quadratic generator 9, Rao–Lakshminarayanan (8.32), RL-8.16. -/
theorem eventuallyEq_quadratic_contiguous_threeF2 (a b : ℂ)
    (hreg : LowerParametersRegular {b, a - 1 / 2}) :
    ∀ᶠ t : ℂ in 𝓝 0,
      (1 + t) * ordinaryHypergeometric a (a + 1 / 2) b (-4 * t / (1 - t) ^ 2) =
        (1 - t) ^ (2 * a) * generalizedHypergeometric
          {2 * a - 1, a + 1 / 2, 2 * a - b} {a - 1 / 2, b} (-t) := by
  sorry

/-- Contiguous quadratic generator 11, Rao–Lakshminarayanan (8.36), RL-8.18. -/
theorem eventuallyEq_quadratic_veryWellPoised_fourF3 (a b c : ℂ)
    (hreg : LowerParametersRegular {a / 2, b, c}) :
    ∀ᶠ t : ℂ in 𝓝 0,
      (1 + t) * generalizedHypergeometric {(a + 1) / 2, 1 + a / 2, -a + b + c - 1}
          {b, c} (-4 * t / (1 - t) ^ 2) =
        (1 - t) ^ (a + 1) * generalizedHypergeometric
          {a, 1 + a / 2, 1 + a - b, 1 + a - c} {a / 2, b, c} t := by
  sorry

/-- Andrews–Stanton generator 12, Rao–Lakshminarayanan (8.38), RL-8.19. -/
theorem eventuallyEq_andrews_stanton_fourF3 (a b : ℂ)
    (hreg : LowerParametersRegular {b + 3 / 2, 1 + a - b, (a + 1) / 3,
      2 + 2 * b, 1 + 2 * a - 2 * b, 2 * (1 + a) / 3}) :
    ∀ᶠ t : ℂ in 𝓝 0,
      (1 - t / 2) * generalizedHypergeometric
          {1 + a, a - 2 * b, 1 - a + 2 * b, (a + 4) / 3}
          {b + 3 / 2, 1 + a - b, (a + 1) / 3} (-t ^ 2 / (4 * (1 - t))) =
        (1 - 2 * t) * (1 - t) ^ (1 + a) * generalizedHypergeometric
          {1 + a, 1 + b, a - b + 1 / 2, (5 + 2 * a) / 3}
          {2 + 2 * b, 1 + 2 * a - 2 * b, 2 * (1 + a) / 3} (4 * t * (1 - t)) := by
  sorry

/-- Cubic generator 14, Rao–Lakshminarayanan second (8.40), RL-8.21. -/
theorem eventuallyEq_cubic_threeF2_squared_argument (a b : ℂ)
    (hreg : LowerParametersRegular {b, 3 * a - b + 3 / 2, 2 * b - 1, 2 + 6 * a - 2 * b}) :
    ∀ᶠ t : ℂ in 𝓝 0,
      (1 - t) ^ (-3 * a) * generalizedHypergeometric {a, a + 1 / 3, a + 2 / 3}
          {b, 3 * a - b + 3 / 2} (27 * t ^ 2 / (4 * (1 - t) ^ 3)) =
        generalizedHypergeometric {3 * a, b - 1 / 2, 1 + 3 * a - b}
          {2 * b - 1, 2 + 6 * a - 2 * b} (4 * t) := by
  sorry

/-- Beta transform of the connection generator, Rao–Lakshminarayanan first (8.45),
RL-8.23. All three unit-argument series have positive excess. -/
theorem generalizedHypergeometric_threeF2_connection_sum (a b c d e : ℂ)
    (hreg : LowerParametersRegular {d, e, 1 + a + b - d, 1 + d - a - b,
      d + e - a - b})
    (hdiff : ∀ n : ℤ, d - a - b ≠ n)
    (hex : 0 < (d + e - a - b - c).re) (hex' : 0 < (1 + c - d).re) :
    generalizedHypergeometric {a, b, c} {d, e} 1 =
      Gamma d * Gamma (d - a - b) / (Gamma (d - a) * Gamma (d - b)) *
        generalizedHypergeometric {a, b, e - c} {1 + a + b - d, e} 1 +
      Gamma (a + b - d) * Gamma d * Gamma e * Gamma (d + e - a - b - c) /
        (Gamma a * Gamma b * Gamma (e - c) * Gamma (d + e - a - b)) *
        generalizedHypergeometric {d - a, d - b, d + e - a - b - c}
          {1 + d - a - b, d + e - a - b} 1 := by
  sorry

/-- Beta transform of the even–odd generator, Rao–Lakshminarayanan second (8.45), RL-8.24. -/
theorem generalizedHypergeometric_half_argument_even_odd (a b d e : ℂ)
    (hd : 0 < d.re) (hed : 0 < (e - d).re)
    (hex : 0 < (e - d + (1 + a + b) / 2 - a - b).re)
    (hreg : LowerParametersRegular {(1 + a + b) / 2, e}) :
    generalizedHypergeometric {a, b, e - d} {(1 + a + b) / 2, e} (1 / 2) =
      (Real.sqrt Real.pi : ℂ) * Gamma ((1 + a + b) / 2) /
        (Gamma ((a + 1) / 2) * Gamma ((b + 1) / 2)) *
        generalizedHypergeometric {a / 2, b / 2, d / 2, (d + 1) / 2}
          {1 / 2, e / 2, (e + 1) / 2} 1 +
      Gamma (-1 / 2) * Gamma ((1 + a + b) / 2) /
        (Gamma (a / 2) * Gamma (b / 2)) * d / e *
        generalizedHypergeometric {(a + 1) / 2, (b + 1) / 2, (d + 1) / 2, (d + 2) / 2}
          {3 / 2, (e + 1) / 2, (e + 2) / 2} 1 := by
  sorry

end DLMF.Hypergeometric
