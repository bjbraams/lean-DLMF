/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic.SecondKind
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Alternating forward differences of cylinder-function zeros

Andrews, Askey and Roy, *Special Functions*, Corollary 4.15.2, pp. 230–231
(synopsis AAR-4.14.1–4.16.4). Real coefficients specify a nontrivial cylinder
solution. Index zero is the first zero in the selected consecutive sequence.
-/

@[expose] public noncomputable section
open MeasureTheory Set
namespace DLMF.Bessel

/-- Every order of arch and zero differences for real cylinder solutions of order
`|ν|>1/2`. Andrews–Askey–Roy, Corollary 4.15.2. -/
theorem cylinder_arch_and_zero_forwardDifferences_pos {nu A B : ℝ}
    (hnu : 1 / 2 < |nu|) (hAB : A ≠ 0 ∨ B ≠ 0) {x : ℕ → ℝ}
    (hx : StrictMono x) (hxpositive : ∀ k, 0 < x k)
    (hzero : ∀ k, A * (Complex.besselJ nu (x k)).re + B * (besselY nu (x k)).re = 0)
    (hnext : ∀ k, ∀ t ∈ Ioo (x k) (x (k + 1)),
      A * (Complex.besselJ nu t).re + B * (besselY nu t).re ≠ 0)
    {lam : ℝ} (hlam : -1 < lam) :
    (∀ k, IntervalIntegrable
      (fun t => t ^ (lam / 2) * |A * (Complex.besselJ nu t).re + B * (besselY nu t).re| ^ lam)
      volume (x k) (x (k + 1))) ∧
    (∀ n k, 0 < (-1 : ℝ) ^ n * (fwdDiff (1 : ℕ))^[n]
      (fun j => ∫ t in x j..x (j + 1),
        t ^ (lam / 2) * |A * (Complex.besselJ nu t).re + B * (besselY nu t).re| ^ lam) k) ∧
    ∀ n, 1 ≤ n → ∀ k,
      0 < (-1 : ℝ) ^ (n - 1) * (fwdDiff (1 : ℕ))^[n] x k := by
  sorry

/-- Positive-zero gaps increase below the half-integer threshold and decrease above it.
Andrews–Askey–Roy, §4.15, following Corollary 4.15.2. -/
theorem cylinder_consecutive_zero_gaps_strictMono_or_strictAnti {nu A B : ℝ}
    (hAB : A ≠ 0 ∨ B ≠ 0) {x : ℕ → ℝ}
    (hx : StrictMono x) (hxpositive : ∀ k, 0 < x k)
    (hzero : ∀ k, A * (Complex.besselJ nu (x k)).re + B * (besselY nu (x k)).re = 0)
    (hnext : ∀ k, ∀ t ∈ Ioo (x k) (x (k + 1)),
      A * (Complex.besselJ nu t).re + B * (besselY nu t).re ≠ 0) :
    (|nu| < 1 / 2 → StrictMono (fun k => x (k + 1) - x k)) ∧
    (1 / 2 < |nu| → StrictAnti (fun k => x (k + 1) - x k)) := by
  sorry

/-- All alternating differences of corresponding cylinder zeros, allowing a fixed index
shift. Andrews–Askey–Roy, Corollary 4.15.2, final assertion. -/
theorem cylinder_zero_offset_forwardDifferences_pos {nu A B C D : ℝ}
    (hnu : 1 / 2 < |nu|) (hAB : A ≠ 0 ∨ B ≠ 0) (hCD : C ≠ 0 ∨ D ≠ 0)
    {x z : ℕ → ℝ} (hx : StrictMono x) (hz : StrictMono z)
    (hxpositive : ∀ k, 0 < x k) (hzpositive : ∀ k, 0 < z k)
    (hzero : ∀ k,
      A * (Complex.besselJ nu (x k)).re + B * (besselY nu (x k)).re = 0 ∧
      C * (Complex.besselJ nu (z k)).re + D * (besselY nu (z k)).re = 0)
    (hnext : ∀ k,
      (∀ t ∈ Ioo (x k) (x (k + 1)),
        A * (Complex.besselJ nu t).re + B * (besselY nu t).re ≠ 0) ∧
      ∀ t ∈ Ioo (z k) (z (k + 1)),
        C * (Complex.besselJ nu t).re + D * (besselY nu t).re ≠ 0)
    (horder : x 0 < z 0) :
    ∀ n k, 0 < (-1 : ℝ) ^ n * (fwdDiff (1 : ℕ))^[n] (fun j => z j - x j) k := by
  sorry

end DLMF.Bessel
