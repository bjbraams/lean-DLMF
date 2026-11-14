/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic.MultipleSeries
public import DLMF.GeneralizedHypergeometric.Basic.PrincipalContinuation

/-!
# Kampé de Fériet transformations and finite summations

The mathematical specifications are Rao–Lakshminarayanan, *Generalized
Hypergeometric Functions* (2018), §7.8, (7.109)–(7.146). Unnormalized series
use global regularity only in unbounded indices; terminating indices require
nonvanishing denominators only through their final degree. Nonterminating identities
carry absolute-summability conclusions or hypotheses. Upper parameter termination is retained
in the two-index family, including triangular termination by `(-N)_(m+n)`.
-/

@[expose] public noncomputable section
open Complex
open scoped Nat
namespace DLMF.Hypergeometric.KampeDeFeriet

/-- Absolute convergence at `(1,1)` on the excess domain of
Rao–Lakshminarayanan (7.110), synopsis RL-7.13. -/
theorem summable_term_one {B B' D D' : Multiset ℂ} {d : ℂ}
    (hB : B.card = D.card + 2) (hB' : B'.card = D'.card + 2)
    (hd : LowerParametersRegular {d})
    (hD : LowerParametersRegular D) (hD' : LowerParametersRegular D')
    (h₁ : 0 < (d + D.sum - B.sum).re) (h₂ : 0 < (d + D'.sum - B'.sum).re) :
    Summable (term ∅ B B' {d} D D' 1 1) := by
  sorry

/-- The general Euler transformation, labelled Proposition, Rao–Lakshminarayanan
(7.111)–(7.112), synopsis RL-7.14. -/
theorem euler_transformation (a b c d e : ℂ) (F G : Multiset ℂ)
    (hF : F.card = G.card + 2)
    (hreg₁ : LowerParametersRegular {d, e, d + e - a - b - c})
    (hreg₂ : LowerParametersRegular ((d + e - b - c) ::ₘ G))
    (h₁ : 0 < (a + G.sum - F.sum).re) (h₂ : 0 < (d - a).re)
    (h₃ : 0 < (d + e - a - b - c).re)
    (hΓ : Gamma (d - a) ≠ 0 ∧ Gamma (d + e - b - c) ≠ 0) :
    Summable (term ∅ {a, b, c} ((d - a) ::ₘ F)
      {d} {e} ((d + e - a - b - c) ::ₘ G) 1 1) ∧
    Summable (term ∅ {a, e - b, e - c} F {d + e - b - c} {e} G 1 1) ∧
    value ∅ {a, b, c} ((d - a) ::ₘ F) {d} {e} ((d + e - a - b - c) ::ₘ G) 1 1 =
      Gamma d * Gamma (d + e - a - b - c) /
        (Gamma (d - a) * Gamma (d + e - b - c)) *
        value ∅ {a, e - b, e - c} F {d + e - b - c} {e} G 1 1 := by
  sorry

/-- The K-to-H transformation, labelled Proposition, Rao–Lakshminarayanan
(7.127), synopsis RL-7.15. -/
theorem terminating_to_coupled (N : ℕ) (a b a' b' d e e' : ℂ)
    (hreg : LowerParametersRegular {d, e', d - b})
    (hfinite : ∀ k ≤ N, pochhammer e k * pochhammer (1 + a - e - N) k *
      pochhammer (1 - b - N) k ≠ 0)
    (hex : 0 < (e' - a' - b' - N).re) :
    Summable (term ∅ {-(N : ℂ), a, b} {d + N, a', b'} {d} {e} {e'} 1 1) ∧
    Summable (term {d - b} {-(N : ℂ), 1 - e - N} {a', b'} ∅
      {1 + a - e - N, 1 - b - N} {e', d - b} 1 1) ∧
    value ∅ {-(N : ℂ), a, b} {d + N, a', b'} {d} {e} {e'} 1 1 =
      pochhammer (e - a) N * pochhammer b N / (pochhammer d N * pochhammer e N) *
        value {d - b} {-(N : ℂ), 1 - e - N} {a', b'} ∅
          {1 + a - e - N, 1 - b - N} {e', d - b} 1 1 := by
  sorry

/-- First labelled Corollary, Rao–Lakshminarayanan (7.131), synopsis RL-7.16. -/
theorem coupled_reduction_complementary (N : ℕ) (a a' b' c d e : ℂ)
    (hreg : LowerParametersRegular {e, 1 + e - c})
    (hfinite : ∀ k ≤ N, pochhammer c k * pochhammer d k *
      pochhammer (1 + a - d - N) k * pochhammer (c - e + a' + b') k ≠ 0)
    (hex : 0 < (1 + e - c - a' - b' - N).re) :
    Summable (term {e} {a, -(N : ℂ)} {a', b'} ∅ {c, d} {1 + e - c, e} 1 1) ∧
    value {e} {a, -(N : ℂ)} {a', b'} ∅ {c, d} {1 + e - c, e} 1 1 =
      pochhammer (d - a) N / pochhammer d N *
        (Gamma (1 + e - c) * Gamma (1 + e - c - a' - b') /
          (Gamma (1 + e - c - a') * Gamma (1 + e - c - b'))) *
        generalizedHypergeometricTruncated N
          {-(N : ℂ), a, c - e + a', c - e + b'}
          {c, 1 + a - d - N, c - e + a' + b'} 1 := by
  sorry

/-- Second labelled Corollary, Rao–Lakshminarayanan (7.132), synopsis RL-7.16. -/
theorem coupled_reduction_shared_lower (N : ℕ) (a a' b' c c' e : ℂ)
    (hreg : LowerParametersRegular {c', e})
    (hfinite : ∀ k ≤ N, pochhammer c k * pochhammer (1 + a - c - N) k *
      pochhammer (1 + a' + b' - c') k ≠ 0)
    (hex : 0 < (c' - a' - b' - N).re) :
    Summable (term {e} {a, -(N : ℂ)} {a', b'} ∅ {c, e} {c', e} 1 1) ∧
    value {e} {a, -(N : ℂ)} {a', b'} ∅ {c, e} {c', e} 1 1 =
      pochhammer (c - a) N / pochhammer c N *
        (Gamma c' * Gamma (c' - a' - b') / (Gamma (c' - a') * Gamma (c' - b'))) *
        generalizedHypergeometricTruncated N {-(N : ℂ), a, a', b'}
          {e, 1 + a - c - N, 1 + a' + b' - c'} 1 := by
  sorry

/-- Triangular terminating transformation, labelled Proposition,
Rao–Lakshminarayanan (7.134), synopsis RL-7.17. -/
theorem triangular_transformation (N : ℕ) (a b a' c c' d : ℂ)
    (hreg : ∀ k ≤ N, pochhammer c k * pochhammer d k * pochhammer c' k *
      pochhammer (1 - d - N) k * pochhammer (c + d - a - b) k *
      pochhammer (1 + a' - c' - N) k ≠ 0) :
    value {-(N : ℂ)} {a, b} {a', 1 + a + b - c - d - N} ∅
      {c, d} {c', 1 - d - N} 1 1 =
      pochhammer (c + d - a - b) N * pochhammer (c' - a') N /
        (pochhammer d N * pochhammer c' N) *
        generalizedHypergeometricTruncated N {-(N : ℂ), c - a, c - b, 1 - c' - N}
          {c, c + d - a - b, 1 + a' - c' - N} 1 := by
  sorry

/-- First Carlitz finite sum, Rao–Lakshminarayanan (7.139)–(7.142),
synopsis RL-7.18. -/
theorem carlitz_sum (m n : ℕ) (a a' c c' e : ℂ)
    (ha' : a' = 1 + a - c - n) (ha : a = 1 + a' - c' - m)
    (hreg : pochhammer c n * pochhammer e n * pochhammer c' m * pochhammer e m ≠ 0) :
    value {e} {a, -(n : ℂ)} {a', -(m : ℂ)} ∅ {c, e} {c', e} 1 1 =
      pochhammer e (m + n) * pochhammer (c - a) n * pochhammer (c' - a') m /
        (pochhammer c n * pochhammer e n * pochhammer c' m * pochhammer e m) := by
  sorry

/-- Second Carlitz finite sum, Rao–Lakshminarayanan (7.143), synopsis RL-7.18. -/
theorem carlitz_complementary_sum (m n : ℕ) (a c e : ℂ)
    (hreg : pochhammer c n * pochhammer e n *
      pochhammer (1 + e - c) m * pochhammer e m ≠ 0) :
    value {e} {a, -(n : ℂ)} {1 + a - c - n, -(m : ℂ)} ∅
      {c, e} {1 + e - c, e} 1 1 =
      pochhammer e (m + n) * pochhammer (c - a) n * pochhammer (e - a) m /
        (pochhammer c n * pochhammer e n * pochhammer (1 + e - c) m * pochhammer e m) := by
  sorry

/-- Triangular Carlitz finite sum, Rao–Lakshminarayanan (7.146), synopsis RL-7.18. -/
theorem carlitz_triangular_sum (N : ℕ) (a b c d : ℂ)
    (hreg : ∀ k ≤ N, pochhammer c k * pochhammer d k *
      pochhammer (1 - c - N) k * pochhammer (1 - d - N) k ≠ 0) :
    value {-(N : ℂ)} {a, b} {-a, 1 + a + b - c - d - N} ∅
      {c, d} {1 - c - N, 1 - d - N} 1 1 =
      pochhammer (c - a) N * pochhammer (d - a) N /
        (pochhammer c N * pochhammer d N) := by
  sorry

/-- The labelled Corollary (7.123), Rao–Lakshminarayanan §7.8, synopsis RL-7.19. -/
theorem unit_argument_reduction (a b c c' d' e f : ℂ)
    (hf : 0 < f.re) (hfc : 0 < (f - c).re)
    (hex : 0 < (e + f - a - b - c).re)
    (hreg : LowerParametersRegular {e, f, e + f - a - b - c, c + c' + d',
      e + f - a - b})
    (hs : Summable (term ∅ {a, b, c} {e - a, e - b, c', d'} {e} {f}
      {e + f - a - b - c, c + c' + d'} 1 1)) :
    value ∅ {a, b, c} {e - a, e - b, c', d'} {e} {f}
      {e + f - a - b - c, c + c' + d'} 1 1 =
      Gamma f * Gamma (e + f - a - b - c) /
        (Gamma (f - c) * Gamma (e + f - a - b)) *
        generalizedHypergeometric {e - a, e - b, c + c', c + d'}
          {e, e + f - a - b, c + c' + d'} 1 := by
  sorry

end DLMF.Hypergeometric.KampeDeFeriet
