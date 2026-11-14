/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Forced modified Bessel equations at large order

The coefficient functions are actual rational functions defined by the differential
recursion. A single particular solution is defined by its convergent `I`/`K`
variation-of-parameters integrals; it is independent of the truncation index.
Source: Olver, *Asymptotics and Special Functions*, Chapter 10, §11,
pp. 388–390.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set
open scoped Real BigOperators

namespace DLMF.Bessel

/-- The coefficient functions of the forced scaled modified Bessel equation.
Olver, Chapter 10, §11, pp. 388–389. -/
def forcedModifiedBesselCoefficient (m : ℕ) : ℕ → ℂ → ℂ
  | 0 => fun z => -z ^ (m + 1) / (1 + z ^ 2)
  | n + 1 => fun z =>
      (z ^ 2 * deriv (deriv (forcedModifiedBesselCoefficient m n)) z +
        z * deriv (forcedModifiedBesselCoefficient m n) z) / (1 + z ^ 2)

/-- The leading forced coefficient has the sign of the inverse large parameter term. -/
@[simp] theorem forcedModifiedBesselCoefficient_zero (m : ℕ) (z : ℂ) :
    forcedModifiedBesselCoefficient m 0 z = -z ^ (m + 1) / (1 + z ^ 2) := rfl

/-- The defining forced-coefficient differential recursion. -/
theorem forcedModifiedBesselCoefficient_succ (m n : ℕ) (z : ℂ) :
    forcedModifiedBesselCoefficient m (n + 1) z =
      (z ^ 2 * deriv (deriv (forcedModifiedBesselCoefficient m n)) z +
        z * deriv (forcedModifiedBesselCoefficient m n) z) / (1 + z ^ 2) := rfl

/-- The forced coefficient functions are rational, with poles only at `+i,-i`.
The explicit denominator exponent records the recursion's pole growth.
Olver, Chapter 10, §11, pp. 388–389. -/
theorem exists_polynomial_forcedModifiedBesselCoefficient (m n : ℕ) :
    ∃ P : Polynomial ℂ, ∀ z : ℂ, 1 + z ^ 2 ≠ 0 →
      forcedModifiedBesselCoefficient m n z = P.eval z / (1 + z ^ 2) ^ (3 * n + 1) := by
  sorry

/-- The exact residual of the forced inverse-even-power truncation.
Olver, Chapter 10, §11, pp. 388–389. -/
theorem forcedModifiedBesselPartialSum_residual (m N : ℕ) {ν z : ℂ}
    (hν : ν ≠ 0) (hz : 1 + z ^ 2 ≠ 0) :
    let L := fun w : ℂ =>
      ∑ n ∈ Finset.range N, forcedModifiedBesselCoefficient m n w / ν ^ (2 * n + 2)
    z ^ 2 * deriv (deriv L) z + z * deriv L z - ν ^ 2 * (1 + z ^ 2) * L z -
      z ^ (m + 1) = (1 + z ^ 2) * forcedModifiedBesselCoefficient m N z / ν ^ (2 * N) := by
  sorry

/-- One particular solution selected by the lower `I` and upper `K` ray integrals.
For positive real `nu` and `Re z>0` these integrals converge. This definition
is independent of the asymptotic truncation. Olver, Chapter 10, §11, pp. 389–390. -/
def forcedModifiedBesselParticular (m : ℕ) (ν : ℝ) (z : ℂ) : ℂ :=
  -z ^ (m + 1) *
    (besselI ν (ν * z) * (∫ s : ℝ in Ioi 1, besselK ν (ν * z * s) * (s : ℂ) ^ m) +
      besselK ν (ν * z) * (∫ s : ℝ in 0..1, besselI ν (ν * z * s) * (s : ℂ) ^ m))

/-- The two actual ray integrals defining the particular solution. -/
theorem forcedModifiedBesselParticular_def (m : ℕ) (ν : ℝ) (z : ℂ) :
    forcedModifiedBesselParticular m ν z = -z ^ (m + 1) *
      (besselI ν (ν * z) * (∫ s : ℝ in Ioi 1, besselK ν (ν * z * s) * (s : ℂ) ^ m) +
        besselK ν (ν * z) * (∫ s : ℝ in 0..1, besselI ν (ν * z * s) * (s : ℂ) ^ m)) := rfl

/-- Both endpoint integrals for the particular solution converge absolutely.
Olver, Chapter 10, §11, pp. 389–390. -/
theorem integrable_forcedModifiedBesselParticular (m : ℕ) {ν : ℝ} (hν : 0 < ν)
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun s : ℝ => besselK ν (ν * z * s) * (s : ℂ) ^ m) (Ioi 1) ∧
      IntervalIntegrable (fun s : ℝ => besselI ν (ν * z * s) * (s : ℂ) ^ m) volume 0 1 := by
  sorry

/-- The ray-integral function solves the forced equation with exactly the book's
right-hand side. Olver, Chapter 10, §11, pp. 389–390. -/
theorem forcedModifiedBesselParticular_equation (m : ℕ) {ν : ℝ} (hν : 0 < ν)
    {z : ℂ} (hz : 0 < z.re) :
    z ^ 2 * deriv (deriv (forcedModifiedBesselParticular m ν)) z +
      z * deriv (forcedModifiedBesselParticular m ν) z -
      (ν : ℂ) ^ 2 * (1 + z ^ 2) * forcedModifiedBesselParticular m ν z = z ^ (m + 1) := by
  sorry

/-- The same particular solution has every inverse-even-power expansion,
uniformly on an unbounded proper right subsector. The explicit argument weight
retains growth when `m>1` and vanishing at the origin. Olver, Chapter 10,
§11, pp. 389–390. -/
theorem exists_uniform_forcedModifiedBesselParticular_remainder (m N : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi / 2) :
    ∃ C ν₀ : ℝ, 0 < C ∧ (m : ℝ) + 2 ≤ ν₀ ∧ ∀ ν : ℝ, ν₀ ≤ ν → ∀ z : ℂ,
      0 < z.re → |arg z| ≤ Real.pi / 2 - δ →
      ‖forcedModifiedBesselParticular m ν z -
        ∑ n ∈ Finset.range N, forcedModifiedBesselCoefficient m n z / (ν : ℂ) ^ (2 * n + 2)‖ ≤
          C * ‖z‖ ^ (m + 1) / ‖1 + z ^ 2‖ / ν ^ (2 * N + 2) := by
  sorry

end DLMF.Bessel
