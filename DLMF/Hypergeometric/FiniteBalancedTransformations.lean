/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic

/-!
# Finite balanced hypergeometric transformations

Andrews, Askey and Roy, *Special Functions*, Theorem 3.3.3 and Corollary 3.3.4,
pp. 140–143. The finite sums exclude denominator zeros only through their
terminating index, retaining poles that occur strictly after termination.
-/

@[expose] public section

namespace DLMF.Hypergeometric

/-- Whipple's terminating balanced `4F3` transformation with finite regularity.
Andrews–Askey–Roy, *Special Functions*, Theorem 3.3.3, pp. 140–142
(synopsis AAR-3.3.3). Also Rao–Lakshminarayanan, Chapter 6, (6.76),
synopsis RL-6.09, after permuting the three nonterminating upper parameters.
Both finite expressions have their displayed regular domains. -/
theorem balanced_fourFThree_of_finite_regular (n : ℕ) (a b c d e f : ℂ)
    (hbal : d + e + f = 1 + a + b + c - n)
    (hleft : ∀ k ≤ n, pochhammerProduct {d, e, f} k ≠ 0)
    (hright : ∀ k ≤ n,
      pochhammerProduct {d, 1 + a - n - e, 1 + a - n - f} k ≠ 0) :
    generalizedHypergeometricTruncated n {-(n : ℂ), a, b, c} {d, e, f} 1 =
      pochhammer (e - a) n * pochhammer (f - a) n /
        (pochhammer e n * pochhammer f n) *
          generalizedHypergeometricTruncated n {-(n : ℂ), a, d - b, d - c}
            {d, 1 + a - n - e, 1 + a - n - f} 1 := by
  sorry

/-- Sheppard's terminating `3F2` transformation with finite regularity.
Andrews–Askey–Roy, *Special Functions*, Corollary 3.3.4, pp. 142–143
(synopsis AAR-3.3.3). No denominator is restricted after degree `n`. -/
theorem sheppard_of_finite_regular (n : ℕ) (a b d e : ℂ)
    (hleft : ∀ k ≤ n, pochhammerProduct {d, e} k ≠ 0)
    (hright : ∀ k ≤ n, pochhammerProduct {d, 1 + a - n - e} k ≠ 0) :
    generalizedHypergeometricTruncated n {-(n : ℂ), a, b} {d, e} 1 =
      pochhammer (e - a) n / pochhammer e n *
        generalizedHypergeometricTruncated n {-(n : ℂ), a, d - b}
          {d, 1 + a - n - e} 1 := by
  sorry


/-- Reflection of a terminating Gauss polynomial about one, with only finite denominator
regularity. Andrews–Askey–Roy, *Special Functions*, Corollary 2.3.3, pp. 83–84
(synopsis AAR-2.3.1–2.3.3). The identity is polynomial in the complex argument. -/
theorem terminating_gauss_one_sub_of_finite_regular (n : ℕ) (b c z : ℂ)
    (hc : ∀ k ≤ n, pochhammer c k ≠ 0)
    (hd : ∀ k ≤ n, pochhammer (b + 1 - c - n) k ≠ 0) :
    generalizedHypergeometricTruncated n {-(n : ℂ), b} {c} z =
      pochhammer (c - b) n / pochhammer c n *
        generalizedHypergeometricTruncated n {-(n : ℂ), b}
          {b + 1 - c - n} (1 - z) := by
  sorry

end DLMF.Hypergeometric
