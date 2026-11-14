/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic

/-!
# Bailey's finite reciprocity and terminating evaluation

Andrews, Askey and Roy, *Special Functions*, Theorem 2.4.6 and equation (3.11.7).
All truncated sums use the existing canonical finite-sum definition. Their
regularity hypotheses concern only the retained terms.
-/

@[expose] public section

open scoped Classical

namespace DLMF.Hypergeometric

/-- Bailey's reciprocity between two finite initial hypergeometric sums.
Andrews–Askey–Roy, *Special Functions*, Theorem 2.4.6, pp. 92–94
(synopsis AAR-2.4.1–2.4.6). -/
theorem bailey_finite_sum_reciprocity {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (x y u : ℂ)
    (hu : ∀ k ≤ max m n, pochhammer u k ≠ 0)
    (hcm : ∀ k < n, pochhammer (x + y + m) k ≠ 0)
    (hcn : ∀ k < m, pochhammer (x + y + n) k ≠ 0)
    (hgamma : ∀ z ∈ ({x + m, y + m, x + y + m,
      x + n, y + n, x + y + n} : Finset ℂ), ∀ k : ℕ, z ≠ -(k : ℂ)) :
    Complex.Gamma (x + m) * Complex.Gamma (y + m) /
        (Complex.Gamma m * Complex.Gamma (x + y + m)) *
      generalizedHypergeometricTruncated (n - 1)
        {x, y, u + m - 1} {u, x + y + m} 1 =
      Complex.Gamma (x + n) * Complex.Gamma (y + n) /
        (Complex.Gamma n * Complex.Gamma (x + y + n)) *
      generalizedHypergeometricTruncated (m - 1)
        {x, y, u + n - 1} {u, x + y + n} 1 := by
  sorry

/-- Bailey's terminating half-parameter ₄F₃ evaluation.
Andrews–Askey–Roy, *Special Functions*, equation (3.11.7), also §3.12
(synopsis AAR-3.10–3.12). -/
theorem bailey_terminating_fourFThree (a b : ℂ) (n : ℕ)
    (h₁ : ∀ k ≤ n, pochhammer (b / 2) k ≠ 0)
    (h₂ : ∀ k ≤ n, pochhammer ((b + 1) / 2) k ≠ 0)
    (h₃ : ∀ k ≤ n, pochhammer (a + 1) k ≠ 0)
    (hb : pochhammer b n ≠ 0) :
    generalizedHypergeometricTruncated n
      {a / 2, (a + 1) / 2, b + n, -(n : ℂ)} {b / 2, (b + 1) / 2, a + 1} 1 =
      pochhammer (b - a) n / pochhammer b n := by
  sorry

/-- The second-order Pfaff recurrence for the rational value in Bailey's evaluation.
Andrews–Askey–Roy, *Special Functions*, §§3.11–3.12
(synopsis AAR-3.10–3.12). -/
theorem bailey_pochhammer_ratio_recurrence (a b : ℂ) (n : ℕ)
    (hb : ∀ k ≤ n + 2, pochhammer b k ≠ 0) :
    (n + 1 : ℂ) * (a - b - n) * (pochhammer (b - a) n / pochhammer b n) +
      (-a ^ 2 + a * b - a + 2 * n * b + 3 * b + 2 + 4 * n + 2 * (n : ℂ) ^ 2) *
        (pochhammer (b - a) (n + 1) / pochhammer b (n + 1)) -
      (b + n + 1) * (a + n + 2) *
        (pochhammer (b - a) (n + 2) / pochhammer b (n + 2)) = 0 := by
  sorry

/-- Pfaff's first-order recurrence for the terminating Vandermonde quotient.
Andrews–Askey–Roy, *Special Functions*, §3.12 (synopsis AAR-3.10–3.12).
The shifted Vandermonde sum has parameters `a+1,b+1`, so its numerator is unchanged. -/
theorem vandermonde_pochhammer_ratio_recurrence (a b : ℂ) (n : ℕ)
    (hb : b ≠ 0) (hbn : pochhammer b n ≠ 0) (hbn' : b + n ≠ 0) :
    pochhammer (b - a) (n + 1) / pochhammer b (n + 1) -
      pochhammer (b - a) n / pochhammer b n =
      -(a / b) * pochhammer (b - a) n / pochhammer (b + 1) n := by
  have hshift : b * pochhammer (b + 1) n = pochhammer b n * (b + n) := by
    have h := congrArg (fun p : Polynomial ℂ => p.eval b)
      (ascPochhammer_succ_left ℂ n)
    simpa only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_one, ← pochhammer_succ] using h.symm
  have hs : pochhammer (b + 1) n ≠ 0 := by
    intro h
    rw [h, mul_zero] at hshift
    exact mul_ne_zero hbn hbn' hshift.symm
  rw [pochhammer_succ, pochhammer_succ]
  field_simp
  linear_combination -a * pochhammer (b - a) n * hshift

end DLMF.Hypergeometric
