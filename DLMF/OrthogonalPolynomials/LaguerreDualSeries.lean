/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Integrals.LaguerreAndHermite
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Mixed and dual Laguerre expansions

Andrews, Askey and Roy, *Special Functions*, Theorems 6.2.1–6.2.2, pp. 292–293
(synopsis AAR-6.1–6.2). The mixed expansion uses the corrected inner-series
coefficient. The dual-series theorem states explicit convergence and domination
assumptions rather than assigning a value to a conditional termwise operation.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace DLMF.OrthogonalPolynomials

/-- Mixed Laguerre expansion with low coefficients in one parameter and high coefficients
in another. Andrews–Askey–Roy, Theorem 6.2.1, with its corrected inner coefficient.
The conclusion is convergence in the weighted L² seminorm. -/
theorem tendsto_mixed_laguerre_expansion {alpha lam c : ℝ}
    (halpha : -1 < alpha) (hlam : -1 < lam)
    (hc : (lam - 2 * alpha - 1) / 2 < c) (N : ℕ) {f : ℝ → ℂ}
    (hfLam : MemLp f 2
      ((volume.restrict (Ioi 0)).withDensity
        (fun x => ENNReal.ofReal (x ^ lam * _root_.Real.exp (-x)))))
    (hfBeta : MemLp f 2
      ((volume.restrict (Ioi 0)).withDensity
        (fun x => ENNReal.ofReal (x ^ (alpha + c) * _root_.Real.exp (-x))))) :
    let beta := alpha + c
    let a := fun k => ∫ x : ℝ in Ioi 0,
      f x * laguerreExtended alpha k x * (x ^ beta * _root_.Real.exp (-x) : ℝ)
    let b := fun k => ∫ x : ℝ in Ioi 0,
      f x * laguerreExtended lam k x * (x ^ lam * _root_.Real.exp (-x) : ℝ)
    let d := fun n => if n ≤ N then
      (n.factorial : ℂ) / Gamma (n + beta + 1) *
        ∑ k ∈ Finset.range (n + 1),
          DLMF.Hypergeometric.pochhammer c (n - k) / (n - k).factorial * a k
      else ∑' r : ℕ, DLMF.Hypergeometric.pochhammer (lam - beta) r *
        (n + r).factorial / ((r.factorial : ℂ) * Gamma (n + r + lam + 1)) * b (n + r)
    (∀ n, N < n → Summable (fun r : ℕ =>
      DLMF.Hypergeometric.pochhammer (lam - beta) r * (n + r).factorial /
        ((r.factorial : ℂ) * Gamma (n + r + lam + 1)) * b (n + r))) ∧
    Tendsto (fun M => eLpNorm
      (fun x => f x - ∑ n ∈ Finset.range M, d n * laguerreExtended beta n x) 2
      ((volume.restrict (Ioi 0)).withDensity
        (fun x => ENNReal.ofReal (x ^ beta * _root_.Real.exp (-x))))) atTop (𝓝 0) := by
  sorry

/-- The left fractional derivative applied to a finite weighted Laguerre series.
Andrews–Askey–Roy, Theorem 6.2.2. -/
def laguerreFractionalLeftPartial (alpha delta : ℝ) (a : ℕ → ℂ) (M : ℕ) (x : ℝ) : ℂ :=
  deriv (fun u : ℝ => ∫ t in (0 : ℝ)..u,
    (∑ n ∈ Finset.range M, a n * Gamma (n + delta + 1) / Gamma (n + alpha + 1) *
      laguerreExtended alpha n t) * ((t ^ alpha * (u - t) ^ (delta - alpha) : ℝ) : ℂ)) x /
    Gamma (delta - alpha + 1)

/-- The defining left fractional derivative of finite partial sums. -/
theorem laguerreFractionalLeftPartial_def (alpha delta : ℝ) (a : ℕ → ℂ) (M : ℕ) (x : ℝ) :
    laguerreFractionalLeftPartial alpha delta a M x =
      deriv (fun u : ℝ => ∫ t in (0 : ℝ)..u,
        (∑ n ∈ Finset.range M, a n * Gamma (n + delta + 1) / Gamma (n + alpha + 1) *
          laguerreExtended alpha n t) *
          ((t ^ alpha * (u - t) ^ (delta - alpha) : ℝ) : ℂ)) x /
        Gamma (delta - alpha + 1) := rfl

/-- The right fractional integral applied to a finite Laguerre series.
Andrews–Askey–Roy, Theorem 6.2.2. -/
def laguerreFractionalRightPartial (alpha delta : ℝ) (a : ℕ → ℂ) (M : ℕ) (x : ℝ) : ℂ :=
  (∫ t : ℝ in Ioi x, (∑ n ∈ Finset.range M, a n * laguerreExtended alpha n t) *
    ((_root_.Real.exp (-t) * (t - x) ^ (alpha - delta - 1) : ℝ) : ℂ)) /
      Gamma (alpha - delta)

/-- The defining right fractional integral of finite partial sums. -/
theorem laguerreFractionalRightPartial_def (alpha delta : ℝ) (a : ℕ → ℂ) (M : ℕ) (x : ℝ) :
    laguerreFractionalRightPartial alpha delta a M x =
      (∫ t : ℝ in Ioi x, (∑ n ∈ Finset.range M, a n * laguerreExtended alpha n t) *
        ((_root_.Real.exp (-t) * (t - x) ^ (alpha - delta - 1) : ℝ) : ℂ)) /
          Gamma (alpha - delta) := rfl

/-- The coefficients of the dual Laguerre series under explicit dominated convergence.
Andrews–Askey–Roy, Theorem 6.2.2. The functions `F,G` are the limits of the printed
fractional operations, on the two sides of the prescribed splitting point. -/
theorem laguerre_dual_series_coefficients {alpha delta y : ℝ}
    (hdelta : -1 < delta) (hda : delta < alpha)
    (had : alpha < min (delta + 1) (2 * delta + 1)) (hy : 0 < y)
    (a : ℕ → ℂ) {F G : ℝ → ℂ}
    (hF : ∀ x ∈ Ioo 0 y,
      Tendsto (fun M => laguerreFractionalLeftPartial alpha delta a M x) atTop (𝓝 (F x)))
    (hG : ∀ x ∈ Ioi y,
      Tendsto (fun M => laguerreFractionalRightPartial alpha delta a M x) atTop (𝓝 (G x)))
    (hdomF : ∀ n, ∃ B : ℝ → ℝ, IntegrableOn B (Ioo 0 y) ∧
      ∀ M x, x ∈ Ioo 0 y →
        ‖laguerreFractionalLeftPartial alpha delta a M x * laguerreExtended delta n x *
          _root_.Real.exp (-x)‖ ≤ B x)
    (hdomG : ∀ n, ∃ B : ℝ → ℝ, IntegrableOn B (Ioi y) ∧
      ∀ M x, x ∈ Ioi y →
        ‖laguerreFractionalRightPartial alpha delta a M x * laguerreExtended delta n x *
          (x ^ delta : ℝ)‖ ≤ B x) :
    ∀ n, a n = (n.factorial : ℂ) / Gamma (n + delta + 1) *
      ((∫ x : ℝ in Ioo 0 y, F x * laguerreExtended delta n x * _root_.Real.exp (-x)) +
        ∫ x : ℝ in Ioi y, G x * laguerreExtended delta n x * (x ^ delta : ℝ)) := by
  sorry

end DLMF.OrthogonalPolynomials
