/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework
public import DLMF.Hypergeometric.Basic.GaussCoefficients
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Parameter multisets, coefficients and finite hypergeometric series
-/

@[expose] public noncomputable section

open Complex Filter Set Polynomial
open scoped Real Nat Topology ENNReal Interval
open Finset

namespace DLMF.Hypergeometric

/-- Vector parameters represented as a multiset; no order-dependent normalization. -/
def genParams {p : ℕ} (a : Fin p → ℂ) : Multiset ℂ := (List.ofFn a : Multiset ℂ)

/-- Product of rising factorials in a parameter multiset (DLMF16.1). -/
def genPoch (a : Multiset ℂ) (n : ℕ) : ℂ := (a.map fun x => poch x n).prod

/-- Product of parameter Gamma factors. -/
def genGamma (a : Multiset ℂ) : ℂ := (a.map Complex.Gamma).prod

/-- The ordinary generalized hypergeometric coefficient (16.2.1). -/
@[dlmf 16.2.E1]
def genCoeff (a b : Multiset ℂ) (n : ℕ) : ℂ :=
  genPoch a n / (genPoch b n * n.factorial)

/-- Lower parameters avoid the nonpositive integers, unless a formula explicitly overrides this. -/
def GenDenRegular (b : Multiset ℂ) : Prop := ∀ x ∈ b, ∀ n : ℕ, x ≠ -n

/-- At least one upper parameter terminates the series. -/
def GenTerminates (a : Multiset ℂ) : Prop := ∃ x ∈ a, ∃ n : ℕ, x = -n

/-- The formal scalar series, meaningful even where the analytic series diverges. -/
def genFormalSeries (a b : Multiset ℂ) : PowerSeries ℂ := PowerSeries.mk (genCoeff a b)

/-- A finite retained sum; denominator exceptions beyond its degree are permitted. -/
def genFiniteHG (m : ℕ) (a b : Multiset ℂ) (z : ℂ) : ℂ :=
  ∑ n ∈ range (m + 1), genCoeff a b n * z ^ n

/-- Natural-order hypergeometric series convergence; unlike `HasSum`, permits conditional convergence. -/
def GenSeriesConvergesTo (a b : Multiset ℂ) (z v : ℂ) : Prop :=
  Tendsto (fun N : ℕ => ∑ n ∈ range N, genCoeff a b n * z ^ n) atTop (𝓝 v)

/-- Absolute convergence of the ordinary coefficient series. -/
def GenSeriesAbsolutelyConverges (a b : Multiset ℂ) (z : ℂ) : Prop :=
  Summable (fun n : ℕ => ‖genCoeff a b n * z ^ n‖)

/-- The unit-circle excess parameter (16.2.2). -/
@[dlmf 16.2.E2]
def genExcess (a b : Multiset ℂ) : ℂ := b.sum - a.sum

/-- Shifting every parameter by the same complex number. -/
def genShift (a : Multiset ℂ) (t : ℂ) : Multiset ℂ := a.map (· + t)

end DLMF.Hypergeometric
