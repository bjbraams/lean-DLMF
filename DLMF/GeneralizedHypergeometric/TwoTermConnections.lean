/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic

/-!
# The two-term three-over-two connection at unity

Andrews, Askey and Roy, *Special Functions*, Theorem 2.4.4 and Corollary 2.4.5,
pp. 91–93. The hypotheses make all three unit series ordinarily convergent.
The displayed nonresonant form excludes gamma-factor poles; resonant values are limits.
-/

@[expose] public section

open Complex

namespace DLMF.Hypergeometric

/-- The two-term three-over-two connection formula, with both transformed sums convergent.
Andrews–Askey–Roy, *Special Functions*, Theorem 2.4.4, pp. 91–92
(synopsis AAR-2.4.1–2.4.6). The noninteger difference excludes the two resonant
connection gamma factors without restricting individual upper parameters. -/
theorem generalizedHypergeometric_threeFTwo_two_term (a b c d e : ℂ)
    (hregular : LowerParametersRegular
      {d, e, 1 + a + b - d, d + e - a - b, d + 1 - a - b})
    (hs : 0 < (d + e - a - b - c).re) (hc : 0 < (1 + c - d).re)
    (hnonresonant : ∀ k : ℤ, d - a - b ≠ k) :
    generalizedHypergeometric {a, b, c} {d, e} 1 =
      Gamma d * Gamma (d - a - b) / (Gamma (d - a) * Gamma (d - b)) *
        generalizedHypergeometric {a, b, e - c} {e, 1 + a + b - d} 1 +
      Gamma d * Gamma e * Gamma (d + e - a - b - c) * Gamma (a + b - d) /
        (Gamma a * Gamma b * Gamma (d + e - a - b) * Gamma (e - c)) *
          generalizedHypergeometric {d - a, d - b, d + e - a - b - c}
            {d + e - a - b, d + 1 - a - b} 1 := by
  sorry

/-- The balanced specialization of the two-term connection, after Gauss summation of
its first transformed series. Andrews–Askey–Roy, *Special Functions*,
Corollary 2.4.5, pp. 92–93 (synopsis AAR-2.4.1–2.4.6). -/
theorem generalizedHypergeometric_threeFTwo_balanced_two_term (a b c d e : ℂ)
    (hbalance : d + e = a + b + c + 1)
    (hregular : LowerParametersRegular {d, e, c + 1, d + 1 - a - b})
    (hc : 0 < (1 + c - d).re) (hnonresonant : ∀ k : ℤ, d - a - b ≠ k) :
    generalizedHypergeometric {a, b, c} {d, e} 1 =
      Gamma d * Gamma (d - a - b) * Gamma e * Gamma (e - a - b) /
        (Gamma (d - a) * Gamma (d - b) * Gamma (e - a) * Gamma (e - b)) +
      Gamma d * Gamma e * Gamma (a + b - d) /
        (Gamma a * Gamma b * Gamma (c + 1) * Gamma (e - c)) *
          generalizedHypergeometric {d - a, d - b, 1} {c + 1, d + 1 - a - b} 1 := by
  sorry

end DLMF.Hypergeometric
