/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic.SecondKind
public import DLMF.Bessel.DiniZeros
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Order dependence and interlacing of cylinder zeros

Olver, *Asymptotics and Special Functions*, Chapter 7, Theorems 6.2–6.4,
7.1–7.2, pp. 245–249. Every zero enumeration here is complete and strictly
increasing, so the index starts at the first positive zero. The derivative is
complex differentiation of a fixed analytic branch; points on its cut are not
silently included as analytic points.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology ContDiff

namespace DLMF.Bessel

/-- A neighborhood of the positive origin is zero-free uniformly for orders bounded
away from `-1`. Olver, Chapter 7, Lemma 6.1, p. 246. -/
theorem exists_uniform_besselJ_ne_zero {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ν x : ℝ, -1 + ε ≤ ν → 0 < x → x ≤ δ →
      besselJ ν x ≠ 0 := by
  sorry

/-- Derivatives are zero-free near the positive origin uniformly for orders bounded
away from zero. Olver, Chapter 7, Lemma 6.1, p. 246. -/
theorem exists_uniform_deriv_besselJ_ne_zero {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ν x : ℝ, ε ≤ ν → 0 < x → x ≤ δ →
      deriv (besselJ ν) x ≠ 0 := by
  sorry

/-- For an order between `-1` and zero, exactly one pair of nonreal derivative zeros
lies on the imaginary axis; all other zeros of the derivative on the principal
analytic branch are real. Olver, Chapter 7, Theorem 6.2, p. 245. -/
theorem existsUnique_imaginary_deriv_besselJ_zero {ν : ℝ} (hν : -1 < ν) (hν' : ν < 0) :
    ∃ r : ℝ, 0 < r ∧ deriv (besselJ ν) (r * I) = 0 ∧
      deriv (besselJ ν) (-(r * I)) = 0 ∧
      (∀ s : ℝ, 0 < s → deriv (besselJ ν) (s * I) = 0 → s = r) ∧
      ∀ z ∈ slitPlane, deriv (besselJ ν) z = 0 →
        z.im = 0 ∨ z = r * I ∨ z = -(r * I) := by
  sorry

/-- The positive `J` zeros form a complete ordered family that is `C1` and strictly
increasing in the order on `(-1,infinity)`. Olver, Chapter 7, Theorems 6.3–6.4,
p. 246, including the extension of monotonicity discussed there. -/
theorem exists_positive_besselJ_zero_family :
    ∃ j : ℝ → ℕ → ℝ,
      (∀ ν : ℝ, -1 < ν → StrictMono (j ν) ∧ Tendsto (j ν) atTop atTop ∧
        (∀ n : ℕ, 0 < j ν n ∧ besselJ ν (j ν n) = 0) ∧
        ∀ x : ℝ, (0 < x ∧ besselJ ν x = 0) ↔ ∃ n : ℕ, j ν n = x) ∧
      ∀ n : ℕ, ContDiffOn ℝ 1 (fun ν => j ν n) (Ioi (-1)) ∧
        StrictMonoOn (fun ν => j ν n) (Ioi (-1)) := by
  sorry

/-- The positive derivative zeros form a complete ordered `C1` family for positive
order, and the first derivative zero exceeds the order. Olver, Chapter 7,
Theorems 6.3–6.4, p. 246. -/
theorem exists_positive_deriv_besselJ_zero_family :
    ∃ j : ℝ → ℕ → ℝ,
      (∀ ν : ℝ, 0 < ν → StrictMono (j ν) ∧ Tendsto (j ν) atTop atTop ∧
        (∀ n : ℕ, 0 < j ν n ∧ deriv (besselJ ν) (j ν n) = 0) ∧
        ν < j ν 0 ∧
        ∀ x : ℝ, (0 < x ∧ deriv (besselJ ν) x = 0) ↔ ∃ n : ℕ, j ν n = x) ∧
      ∀ n : ℕ, ContDiffOn ℝ 1 (fun ν => j ν n) (Ioi 0) := by
  sorry

/-- Ordered function and derivative zeros strictly interlace, including their first
members. Olver, Chapter 7, §6, p. 246. -/
theorem besselJ_deriv_positive_zeros_interlace {ν : ℝ} (hν : 0 < ν)
    (j d : ℕ → ℝ) (hj : StrictMono j) (hd : StrictMono d)
    (hJ : ∀ x : ℝ, (0 < x ∧ besselJ ν x = 0) ↔ ∃ n : ℕ, j n = x)
    (hD : ∀ x : ℝ, (0 < x ∧ deriv (besselJ ν) x = 0) ↔ ∃ n : ℕ, d n = x) :
    ∀ n : ℕ, d n < j n ∧ j n < d (n + 1) := by
  sorry

/-- Between consecutive positive zeros of one real cylinder function lies exactly
one zero of an independent real cylinder function. Olver, Chapter 7, Theorem 7.1,
p. 248. The coefficient determinant expresses their linear independence. -/
theorem existsUnique_cylinder_zero_between {ν A B C D a b : ℝ}
    (hindependent : A * D - B * C ≠ 0) (ha : 0 < a) (hab : a < b)
    (hleft : A * (besselJ ν a).re + B * (besselY ν a).re = 0)
    (hright : A * (besselJ ν b).re + B * (besselY ν b).re = 0)
    (hnext : ∀ x ∈ Ioo a b, A * (besselJ ν x).re + B * (besselY ν x).re ≠ 0) :
    ∃! x : ℝ, x ∈ Ioo a b ∧ C * (besselJ ν x).re + D * (besselY ν x).re = 0 := by
  sorry

/-- The positive `Y` zeros form a complete ordered `C1` family increasing in the
order for `nu > -1/2`. Olver, Chapter 7, Theorem 7.2, pp. 248–249. -/
theorem exists_positive_besselY_zero_family :
    ∃ y : ℝ → ℕ → ℝ,
      (∀ ν : ℝ, -(1 / 2) < ν → StrictMono (y ν) ∧ Tendsto (y ν) atTop atTop ∧
        (∀ n : ℕ, 0 < y ν n ∧ besselY ν (y ν n) = 0) ∧
        ∀ x : ℝ, (0 < x ∧ besselY ν x = 0) ↔ ∃ n : ℕ, y ν n = x) ∧
      ∀ n : ℕ, ContDiffOn ℝ 1 (fun ν => y ν n) (Ioi (-(1 / 2))) ∧
        StrictMonoOn (fun ν => y ν n) (Ioi (-(1 / 2))) := by
  sorry

/-- Ordered `Y` and `J` zeros strictly interlace with `Y` first for `nu > -1/2`.
Olver, Chapter 7, Theorem 7.2, p. 248. -/
theorem besselY_besselJ_positive_zeros_interlace {ν : ℝ} (hν : -(1 / 2) < ν)
    (j y : ℕ → ℝ) (hj : StrictMono j) (hy : StrictMono y)
    (hJ : ∀ x : ℝ, (0 < x ∧ besselJ ν x = 0) ↔ ∃ n : ℕ, j n = x)
    (hY : ∀ x : ℝ, (0 < x ∧ besselY ν x = 0) ↔ ∃ n : ℕ, y n = x) :
    ∀ n : ℕ, y n < j n ∧ j n < y (n + 1) := by
  sorry

end DLMF.Bessel
