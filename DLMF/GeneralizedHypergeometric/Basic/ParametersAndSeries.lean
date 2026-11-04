/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Basic
public import DLMF.Hypergeometric.Basic.GaussCoefficients
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Parameter multisets, coefficients and finite hypergeometric series

## Main definitions

* `parametersOfFin`: vector parameters represented as a multiset.
* `pochhammerProduct`, `gammaProduct`: products of rising factorials and of Gamma values over a
  multiset.
* `generalizedHypergeometricCoeff`: the coefficient of the generalized hypergeometric series, DLMF
  16.2.1.
* `parameterExcess`: the unit-circle excess parameter, DLMF 16.2.2.
* `LowerParametersRegular`, `IsTerminating`: regular lower parameters and terminating series.
* `generalizedHypergeometricSeries`, `generalizedHypergeometricTruncated`: the formal series and
  finite retained sums.
* `HypergeometricSeriesConvergesTo`, `HypergeometricSeriesAbsolutelyConverges`: natural-order and
  absolute convergence of the series.
* `IsWellPoised`, `IsVeryWellPoised`: well-poised parameter vectors, DLMF 16.4.1.
* `IsKBalanced`: `k`-balanced terminating series, DLMF 16.4.2.
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open Finset

namespace DLMF.Hypergeometric

/-- Vector parameters represented as a multiset; no order-dependent normalization. -/
def parametersOfFin {p : ℕ} (a : Fin p → ℂ) : Multiset ℂ := (List.ofFn a : Multiset ℂ)

/-- Product of rising factorials in a parameter multiset (DLMF16.1). -/
def pochhammerProduct (a : Multiset ℂ) (n : ℕ) : ℂ := (a.map fun x => pochhammer x n).prod

/-- Product of parameter Gamma factors. -/
def gammaProduct (a : Multiset ℂ) : ℂ := (a.map Complex.Gamma).prod

/-- The ordinary generalized hypergeometric coefficient (16.2.1). -/
@[dlmf 16.2.E1]
def generalizedHypergeometricCoeff (a b : Multiset ℂ) (n : ℕ) : ℂ :=
  pochhammerProduct a n / (pochhammerProduct b n * n.factorial)

/-- Lower parameters avoid the nonpositive integers, unless a formula explicitly overrides this. -/
def LowerParametersRegular (b : Multiset ℂ) : Prop := ∀ x ∈ b, ∀ n : ℕ, x ≠ -n

/-- At least one upper parameter terminates the series. -/
def IsTerminating (a : Multiset ℂ) : Prop := ∃ x ∈ a, ∃ n : ℕ, x = -n

/-- The formal scalar series, meaningful even where the analytic series diverges. -/
def generalizedHypergeometricSeries (a b : Multiset ℂ) : PowerSeries ℂ :=
    PowerSeries.mk (generalizedHypergeometricCoeff a b)

/-- A finite retained sum; denominator exceptions beyond its degree are permitted. -/
def generalizedHypergeometricTruncated (m : ℕ) (a b : Multiset ℂ) (z : ℂ) : ℂ :=
  ∑ n ∈ range (m + 1), generalizedHypergeometricCoeff a b n * z ^ n

/-- Natural-order hypergeometric series convergence; unlike `HasSum`, permits conditional
convergence. -/
def HypergeometricSeriesConvergesTo (a b : Multiset ℂ) (z v : ℂ) : Prop :=
  Tendsto (fun N : ℕ => ∑ n ∈ range N, generalizedHypergeometricCoeff a b n * z ^ n) atTop (𝓝 v)

/-- Absolute convergence of the ordinary coefficient series. -/
def HypergeometricSeriesAbsolutelyConverges (a b : Multiset ℂ) (z : ℂ) : Prop :=
  Summable (fun n : ℕ => ‖generalizedHypergeometricCoeff a b n * z ^ n‖)

/-- The unit-circle excess parameter (16.2.2). -/
@[dlmf 16.2.E2]
def parameterExcess (a b : Multiset ℂ) : ℂ := b.sum - a.sum

/-- Shifting every parameter by the same complex number. -/
def shiftParameters (a : Multiset ℂ) (t : ℂ) : Multiset ℂ := a.map (· + t)

/-- Well-poised parameter vectors, in exactly the indexing order of16.4.1. -/
@[dlmf 16.4.E1]
def IsWellPoised {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ) : Prop :=
  ∀ j, a j.castSucc + b j = a (Fin.last q) + 1

/-- Very well-poised vectors also differ by one in their first corresponding entries. -/
def IsVeryWellPoised {q : ℕ} (a : Fin (q + 2) → ℂ) (b : Fin (q + 1) → ℂ) : Prop :=
  IsWellPoised a b ∧ a 0 = b 0 + 1

/-- A k-balanced terminating unity series (16.4.2); balanced means k=1. -/
@[dlmf 16.4.E2]
def IsKBalanced {q : ℕ} (k : ℤ) (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ) : Prop :=
  (∃ n : ℕ, a (Fin.last q) = -n) ∧ (∑ j, a j) + k = ∑ j, b j

end DLMF.Hypergeometric
