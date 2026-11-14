/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic

/-!
# Canceled very-well-poised summations

Andrews, Askey and Roy, *Special Functions*, §§3.4–3.5, pp. 143–150.
The apparent factor `(a/2+1)_k/(a/2)_k` is canceled against `(a)_k`
before evaluation. Conditional minus-one sums use ordered partial sums.
-/

@[expose] public noncomputable section

open Finset Filter Complex

namespace DLMF.Hypergeometric

namespace VeryWellPoised

/-- The canceled very-well-poised coefficient, including its removable value at `a = 0`.
Andrews–Askey–Roy, *Special Functions*, §3.4, pp. 143–144
(synopsis AAR-3.4.1–3.5.5). Upper parameters other than `a,a/2+1` form `b`. -/
def coefficient (a : ℂ) (b : Multiset ℂ) (k : ℕ) : ℂ :=
  if k = 0 then 1 else
    (a + 2 * k) * pochhammer (a + 1) (k - 1) * pochhammerProduct b k /
      (pochhammerProduct (b.map fun u => 1 + a - u) k * k.factorial)

/-- The defining canceled coefficient formula. -/
theorem coefficient_def (a : ℂ) (b : Multiset ℂ) (k : ℕ) :
    coefficient a b k = if k = 0 then 1 else
      (a + 2 * k) * pochhammer (a + 1) (k - 1) * pochhammerProduct b k /
        (pochhammerProduct (b.map fun u => 1 + a - u) k * k.factorial) := rfl

/-- The constant coefficient is one for every parameter, including `a = 0`. -/
@[simp] theorem coefficient_zero (a : ℂ) (b : Multiset ℂ) : coefficient a b 0 = 1 := by
  simp [coefficient]

end VeryWellPoised

/-- Bailey's terminating well-poised five-to-four transformation.
Andrews–Askey–Roy, *Special Functions*, Lemma 3.4.2, p. 144
(synopsis AAR-3.4.1–3.5.5). Denominator regularity is required only through termination. -/
theorem bailey_terminating_fiveFFour (a b c d : ℂ) (m : ℕ)
    (hleft : ∀ u ∈ ({1 + a - b, 1 + a - c, 1 + a - d, 1 + a + m} : Multiset ℂ),
      ∀ k ≤ m, pochhammer u k ≠ 0)
    (hright : ∀ u ∈ ({1 + a - b, 1 + a - c, d - a / 2 - m} : Multiset ℂ),
      ∀ k ≤ m, pochhammer u k ≠ 0)
    (hfactor : pochhammer (1 + a / 2) m ≠ 0) :
    generalizedHypergeometricTruncated m {a, b, c, d, -(m : ℂ)}
      {1 + a - b, 1 + a - c, 1 + a - d, 1 + a + m} 1 =
      pochhammer (1 + a) m * pochhammer (1 + a / 2 - d) m /
        (pochhammer (1 + a / 2) m * pochhammer (1 + a - d) m) *
          generalizedHypergeometricTruncated m {a / 2, 1 + a - b - c, d, -(m : ℂ)}
            {1 + a - b, 1 + a - c, d - a / 2 - m} 1 := by
  sorry

/-- The terminating very-well-poised five-over-four summation with canceled parameters.
Andrews–Askey–Roy, *Special Functions*, Corollary 3.4.3, p. 144
(synopsis AAR-3.4.1–3.5.5). -/
theorem sum_veryWellPoised_fiveFFour (a c d : ℂ) (m : ℕ)
    (hregular : ∀ u ∈ ({1 + a - c, 1 + a - d, 1 + a + m} : Multiset ℂ),
      ∀ k ≤ m, pochhammer u k ≠ 0) :
    ∑ k ∈ range (m + 1), VeryWellPoised.coefficient a {c, d, -(m : ℂ)} k =
      pochhammer (1 + a) m * pochhammer (1 + a - c - d) m /
        (pochhammer (1 + a - c) m * pochhammer (1 + a - d) m) := by
  sorry

/-- Dougall's balanced terminating seven-over-six sum in the canceled convention.
Andrews–Askey–Roy, *Special Functions*, Theorem 3.5.1, p. 147
(synopsis AAR-3.4.1–3.5.5). -/
theorem sum_veryWellPoised_dougall (a b c d e : ℂ) (m : ℕ)
    (hbalance : 2 * a + 1 = b + c + d + e - m)
    (hregular : ∀ u ∈ ({1 + a - b, 1 + a - c, 1 + a - d, 1 + a - e,
      1 + a + m, 1 + a - b - c - d} : Multiset ℂ), ∀ k ≤ m, pochhammer u k ≠ 0) :
    ∑ k ∈ range (m + 1), VeryWellPoised.coefficient a {b, c, d, e, -(m : ℂ)} k =
      pochhammer (1 + a) m * pochhammer (1 + a - b - c) m *
        pochhammer (1 + a - b - d) m * pochhammer (1 + a - c - d) m /
        (pochhammer (1 + a - b) m * pochhammer (1 + a - c) m *
          pochhammer (1 + a - d) m * pochhammer (1 + a - b - c - d) m) := by
  sorry

/-- Dougall's nonterminating five-over-four sum, after cancellation of the artificial
`a/2` singularity. Andrews–Askey–Roy, *Special Functions*, Corollary 3.5.2,
p. 148 (synopsis AAR-3.4.1–3.5.5). -/
theorem hasSum_veryWellPoised_dougall (a c d e : ℂ)
    (hregular : LowerParametersRegular {1 + a - c, 1 + a - d, 1 + a - e})
    (hconv : 0 < (1 + a - c - d - e).re) :
    HasSum (VeryWellPoised.coefficient a {c, d, e})
      (Gamma (1 + a - c) * Gamma (1 + a - d) * Gamma (1 + a - e) *
        Gamma (1 + a - c - d - e) /
        (Gamma (1 + a) * Gamma (1 + a - d - e) *
          Gamma (1 + a - c - e) * Gamma (1 + a - c - d))) := by
  sorry

/-- The very-well-poised minus-one summation in its ordinary convergence half-space.
Andrews–Askey–Roy, *Special Functions*, Corollary 3.5.3, p. 149
(synopsis AAR-3.4.1–3.5.5). Conditional convergence is an ordered limit. -/
theorem tendsto_sum_veryWellPoised_minus_one (a c d : ℂ)
    (hregular : LowerParametersRegular {1 + a - c, 1 + a - d})
    (hconv : -1 < (1 + a - 2 * c - 2 * d).re) :
    Tendsto (fun N : ℕ => ∑ k ∈ range N,
      VeryWellPoised.coefficient a {c, d} k * (-1 : ℂ) ^ k)
      atTop (nhds (Gamma (1 + a - c) * Gamma (1 + a - d) /
        (Gamma (1 + a) * Gamma (1 + a - c - d)))) := by
  sorry

/-- Whipple's minus-one transformation into a convergent three-over-two unit sum.
Andrews–Askey–Roy, *Special Functions*, Theorem 3.4.6, p. 146
(synopsis AAR-3.4.1–3.5.5). -/
theorem tendsto_sum_veryWellPoised_minus_one_threeFTwo (a b c d e : ℂ)
    (hregular : LowerParametersRegular {1 + a - b, 1 + a - c, 1 + a - d, 1 + a - e})
    (hleft : -1 < (3 + 3 * a - 2 * (b + c + d + e)).re)
    (hright : 0 < (1 + a - d - e).re) :
    Tendsto (fun N : ℕ => ∑ k ∈ range N,
      VeryWellPoised.coefficient a {b, c, d, e} k * (-1 : ℂ) ^ k)
      atTop (nhds (Gamma (1 + a - d) * Gamma (1 + a - e) /
        (Gamma (1 + a) * Gamma (1 + a - d - e)) *
          generalizedHypergeometric {1 + a - b - c, d, e} {1 + a - b, 1 + a - c} 1)) := by
  sorry


/-- Whipple's terminating `7F6` transformation with the central `a/2` factor canceled.
Andrews–Askey–Roy, *Special Functions*, Theorem 3.4.4, pp. 145–146
(synopsis AAR-3.4.1–3.5.5). The removable central value `a=0` is retained;
all lower-parameter exclusions stop at the terminating degree. -/
theorem sum_veryWellPoised_whipple (m : ℕ) (a b c d e : ℂ)
    (hleft : ∀ k ≤ m,
      pochhammerProduct {1 + a - b, 1 + a - c, 1 + a - d,
        1 + a - e, 1 + a + m} k ≠ 0)
    (hright : ∀ k ≤ m,
      pochhammerProduct {1 + a - b, 1 + a - c, d + e - a - m} k ≠ 0) :
    (∑ k ∈ range (m + 1), VeryWellPoised.coefficient a {b, c, d, e, -(m : ℂ)} k) =
      pochhammer (1 + a) m * pochhammer (1 + a - d - e) m /
        (pochhammer (1 + a - d) m * pochhammer (1 + a - e) m) *
          generalizedHypergeometricTruncated m {1 + a - b - c, d, e, -(m : ℂ)}
            {1 + a - b, 1 + a - c, d + e - a - m} 1 := by
  sorry

end DLMF.Hypergeometric
