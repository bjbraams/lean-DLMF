/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Selberg.ContinuationAndAomoto
public import DLMF.Gamma.Multidimensional.SelbergLimits

/-!
# Mixed Selberg moments, simplex moments and the Dixon–Anderson integral

Andrews, Askey and Roy, *Special Functions*, §§8.1–8.4. The Laguerre moment
statement extends the existing positive-coupling theorem to its full convergence domain.
All powers of positive real bases use the real logarithm.
-/

@[expose] public section

open MeasureTheory Finset Set Complex

noncomputable section

namespace DLMF.Selberg

/-- The Laguerre–Selberg moment integral on the full convergence domain.
Andrews–Askey–Roy, *Special Functions*, Corollary 8.2.2 and Theorem 8.3.3,
pp. 406–410 (synopsis AAR-8.1.1–8.3.3). For `n = 1`, coupling has no effect. -/
theorem laguerre_selberg_moment {n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    {a c : ℂ} (ha : 0 < a.re)
    (hc : n = 1 ∨ (-1 / (n : ℝ) < c.re ∧
      0 < a.re + ((n - 1 : ℕ) : ℝ) * c.re)) :
    (∫ t : Fin n → ℝ in Set.pi Set.univ (fun _ => Ioi (0 : ℝ)),
      (∏ i ∈ initialSegment n k, (t i : ℂ)) *
        (∏ i, (t i : ℂ) ^ (a - 1) * exp (-(t i : ℂ))) *
        vandermondeAbsPow n c t) =
      (Finset.prod (Finset.range k) (fun i => a + ((n - 1 - i : ℕ) : ℂ) * c)) *
        ∏ j ∈ Finset.range n, Gamma (a + j * c) *
          (if j = 0 then 1 else Gamma (1 + (j + 1) * c) / Gamma (1 + c)) := by
  sorry

/-- Inserting an elementary symmetric polynomial in Selberg's integral multiplies the
single-monomial Aomoto moment by `n.choose k`. Andrews–Askey–Roy, *Special Functions*,
Theorem 8.1.2, pp. 404–405 (synopsis AAR-8.1.1–8.3.3). -/
theorem selberg_elementary_symmetric_moment {n k : ℕ} (hk : k ≤ n)
    {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : c ∈ selbergConvergenceDomain n a b) :
    (∫ t in unitCube n,
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, monomialProduct S t) *
        selbergIntegrand n a b c t) =
      (n.choose k : ℂ) * aomotoIntegral n a b c (initialSegment n k) := by
  sorry

/-- The mixed Selberg moment with arbitrary overlapping sets of inserted factors.
Andrews–Askey–Roy, *Special Functions*, Theorem 8.3.1, p. 408
(synopsis AAR-8.1.1–8.3.3). The displayed rational expression is evaluated at regular
denominators; removable parameter values require its canceled continuation. -/
theorem selberg_mixed_moment {n : ℕ} {a b c : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : c ∈ selbergConvergenceDomain n a b)
    (S T : Finset (Fin n))
    (hden : ∀ i < S.card + T.card, a + b + ((2 * n : ℂ) - i - 2) * c ≠ 0)
    (hoverlap : ∀ i < (S ∩ T).card,
      a + b + 1 + ((2 * n : ℂ) - i - 2) * c ≠ 0) :
    (∫ t in unitCube n, monomialProduct S t * (∏ i ∈ T, (1 - (t i : ℂ))) *
      selbergIntegrand n a b c t) =
      selbergIntegral n a b c *
        (∏ i ∈ Finset.range (S ∩ T).card,
          (a + b + ((n : ℂ) - i - 2) * c) /
            (a + b + 1 + ((2 * n : ℂ) - i - 2) * c)) *
        ((Finset.prod (Finset.range S.card) (fun i => a + ((n : ℂ) - i - 1) * c)) *
          (Finset.prod (Finset.range T.card) (fun i => b + ((n : ℂ) - i - 1) * c))) /
        (Finset.prod (Finset.range (S.card + T.card))
          (fun i => a + b + ((2 * n : ℂ) - i - 2) * c)) := by
  sorry

/-- The simplex Selberg moment includes the factor omitted in the supplied printing.
Andrews–Askey–Roy, *Special Functions*, Theorem 8.3.3, p. 410
(synopsis AAR-8.1.1–8.3.3; see ERRATA-AAR.md). -/
theorem simplex_selberg_moment {n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : n = 1 ∨ (-1 / (n : ℝ) < c.re ∧
      0 < a.re + ((n - 1 : ℕ) : ℝ) * c.re)) :
    (∫ t : Fin n → ℝ in {t | (∀ i, 0 < t i) ∧ ∑ i, t i < 1},
      monomialProduct (initialSegment n k) t *
        (∏ i, (t i : ℂ) ^ (a - 1)) *
        (1 - (∑ i, t i : ℝ) : ℂ) ^ (b - 1) * vandermondeAbsPow n c t) =
      Gamma b * (Finset.prod (Finset.range k) (fun i => a + ((n - 1 - i : ℕ) : ℂ) * c)) /
        Gamma (b + k + n * a + n * (n - 1 : ℕ) * c) *
        ∏ j ∈ Finset.range n, Gamma (a + j * c) *
          (if j = 0 then 1 else Gamma (1 + (j + 1) * c) / Gamma (1 + c)) := by
  sorry

/-- Dixon–Anderson's interlacing integral, with complex exponents of positive real bases.
Andrews–Askey–Roy, *Special Functions*, Theorem 8.4.4, p. 414
(synopsis AAR-8.4.1–8.4.4). -/
theorem dixon_anderson_integral (n : ℕ) (a : Fin (n + 1) → ℝ) (ha : StrictAnti a)
    (s : Fin (n + 1) → ℂ) (hs : ∀ j, 0 < (s j).re) :
    (∫ t : Fin n → ℝ in {t | ∀ i : Fin n, a i.succ < t i ∧ t i < a i.castSucc},
      (∏ i, ∏ j, if i < j then ((t i - t j : ℝ) : ℂ) else 1) *
        ∏ i : Fin n, ∏ j : Fin (n + 1), ((|t i - a j| : ℝ) : ℂ) ^ (s j - 1)) =
      (∏ j, Gamma (s j)) / Gamma (∑ j, s j) *
        ∏ i, ∏ j, if i < j then ((a i - a j : ℝ) : ℂ) ^ (s i + s j - 1) else 1 := by
  sorry

/-- Interlacing roots determine positive partial-fraction residues with sum one.
Andrews–Askey–Roy, *Special Functions*, Lemmas 8.4.1–8.4.2, pp. 411–413
(synopsis AAR-8.4.1–8.4.4). -/
theorem interlacing_partial_fractions (n : ℕ) (a : Fin (n + 1) → ℝ)
    (ha : StrictAnti a) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, a i.succ < t i ∧ t i < a i.castSucc) :
    ∃ u : Fin (n + 1) → ℝ, (∀ j, 0 < u j) ∧ (∑ j, u j) = 1 ∧
      ∀ z : ℂ, (∀ j, z ≠ (a j : ℂ)) →
        (∏ i : Fin n, (z - (t i : ℂ))) /
          (∏ j : Fin (n + 1), (z - (a j : ℂ))) =
          ∑ j, (u j : ℂ) / (z - (a j : ℂ)) := by
  sorry

/-- The mixed Selberg moment with its overlapping denominator factors canceled first.
Andrews–Askey–Roy, *Special Functions*, Theorem 8.3.1, p. 408
(synopsis AAR-8.1.1–8.3.3). This includes every parameter in the convergence domain;
no exclusion of a removable rational factor is imposed. -/
theorem selberg_mixed_moment_canceled {n : ℕ} {a b c : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : c ∈ selbergConvergenceDomain n a b)
    (S T : Finset (Fin n)) :
    let r := S.card + T.card - n
    (∫ t in unitCube n, monomialProduct S t * (∏ i ∈ T, (1 - (t i : ℂ))) *
      selbergIntegrand n a b c t) =
      selbergIntegral n a b c *
        (∏ i ∈ Finset.Ico r (S ∩ T).card, (a + b + ((n : ℂ) - i - 2) * c)) /
          (∏ i ∈ Finset.range (S ∩ T).card,
            (a + b + 1 + ((2 * n : ℂ) - i - 2) * c)) *
        ((∏ i ∈ Finset.range S.card, (a + ((n : ℂ) - i - 1) * c)) *
          (∏ i ∈ Finset.range T.card, (b + ((n : ℂ) - i - 1) * c))) /
          (∏ i ∈ Finset.range (min (S.card + T.card) n),
            (a + b + ((2 * n : ℂ) - i - 2) * c)) := by
  sorry

end DLMF.Selberg
