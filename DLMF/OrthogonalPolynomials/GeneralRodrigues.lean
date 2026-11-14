/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.General
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Rodrigues' criterion on finite or infinite intervals

Duverney, *An Introduction to Hypergeometric Functions*, Chapter 9, Theorem 9.6,
equations (9.19)–(9.21). Extended-real endpoints permit finite intervals, half-lines
and the whole real line. Endpoint hypotheses are genuine limits of all polynomially
weighted derivatives, through order `n-1`, of the Rodrigues numerator.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Polynomial
open scoped Topology ContDiff

namespace DLMF.OrthogonalPolynomials

/-- The Rodrigues orthogonality criterion with the norm formula and explicit endpoint
limits. Duverney Theorem 9.6, equations (9.19)–(9.21), synopsis DU-9.04. -/
theorem orthogonal_and_norm_of_rodrigues {a b : EReal} (hab : a < b)
    {w : ℝ → ℝ} {g : ℕ → ℝ → ℝ} {c : ℕ → ℝ} {p : ℕ → ℝ[X]}
    (hw : ContDiffOn ℝ ∞ w {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b})
    (hwpos : ∀ x : ℝ, a < (x : EReal) → (x : EReal) < b → 0 < w x)
    (hmom : ∀ m : ℕ, IntegrableOn (fun x : ℝ => x ^ m * w x)
      {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b})
    (hg : ∀ n, ContDiffOn ℝ ∞ (g n)
      {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b})
    (hdegree : ∀ n, (p n).natDegree = n)
    (hp : ∀ (n : ℕ) (x : ℝ), a < (x : EReal) → (x : EReal) < b →
      (p n).eval x = c n * iteratedDeriv n (fun t => w t * g n t) x / w x)
    (hleft : ∀ n m h : ℕ, h < n →
      Tendsto (fun x : ℝ => x ^ m * iteratedDeriv h (fun t => w t * g n t) x)
        (comap (fun x : ℝ => (x : EReal)) (𝓝[>] a)) (𝓝 0))
    (hright : ∀ n m h : ℕ, h < n →
      Tendsto (fun x : ℝ => x ^ m * iteratedDeriv h (fun t => w t * g n t) x)
        (comap (fun x : ℝ => (x : EReal)) (𝓝[<] b)) (𝓝 0)) :
    (∀ m n : ℕ, m ≠ n →
      (∫ x in {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b},
        (p m).eval x * (p n).eval x * w x) = 0) ∧
      ∀ n : ℕ, (∫ x in {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b},
        (p n).eval x ^ 2 * w x) = (-1 : ℝ) ^ n * n.factorial * c n *
          (p n).leadingCoeff *
            ∫ x in {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}, w x * g n x := by
  sorry

end DLMF.OrthogonalPolynomials
