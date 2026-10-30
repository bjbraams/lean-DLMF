/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import DLMFMathlib.Analysis.ODE.P1oEntireLinear
public import DLMFMathlib.Analysis.ODE.P1oParamHolomorphic
public import DLMFMathlib.Analysis.ODE.P2sSturmSpectrum
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

/-!
# Mathieu equation, canonical solutions and Floquet data
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real Classical

namespace DLMF.Mathieu

/-- **Mathieu's equation** (DLMF 28.2.1) `w'' + (a - 2q cos 2z) w = 0` in standard form, with
complex parameters `(a, q)` and complex variable `z`: `w` is entire and its derivative has
derivative `(2q cos 2z - a) w(z)` at every point. -/
@[dlmf 28.2.E1]
structure IsMathieuSolution (a q : ℂ) (w : ℂ → ℂ) : Prop where
  /-- Solutions are entire (DLMF §28.2(ii)). -/
  differentiable : Differentiable ℂ w
  /-- The equation `w'' = (2q cos 2z - a) w`. -/
  hasDerivAt_deriv : ∀ z, HasDerivAt (deriv w) ((2 * q * Complex.cos (2 * z) - a) * w z) z

/-- The **basic solution** `w_I(z; a, q)` of Mathieu's equation (DLMF 28.2.5): the solution with
`w_I(0) = 1`, `w_I'(0) = 0`; defined by choice (junk `0` if no such solution existed, which
`exists_isMathieuSolution` excludes). -/
@[dlmf 28.2.E5]
def mathieuWI (a q : ℂ) : ℂ → ℂ :=
  if h : ∃ w, IsMathieuSolution a q w ∧ w 0 = 1 ∧ deriv w 0 = 0 then h.choose else 0

/-- The **basic solution** `w_II(z; a, q)` of Mathieu's equation (DLMF 28.2.5): the solution with
`w_II(0) = 0`, `w_II'(0) = 1`; defined by choice. -/
@[dlmf 28.2.E5]
def mathieuWII (a q : ℂ) : ℂ → ℂ :=
  if h : ∃ w, IsMathieuSolution a q w ∧ w 0 = 0 ∧ deriv w 0 = 1 then h.choose else 0

/-! ### Floquet theory (§28.2(iii)–(iv)) -/

/-- The **monodromy matrix** of Mathieu's equation (DLMF 28.2.15):
`[[w_I(π), w_II(π)], [w_I'(π), w_II'(π)]]`. -/
@[dlmf 28.2.E15]
def mathieuMonodromy (a q : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![mathieuWI a q π, mathieuWII a q π; deriv (mathieuWI a q) π, deriv (mathieuWII a q) π]

/-- `ν` is a **characteristic exponent** of Mathieu's equation with parameters `(a, q)`: it
solves the characteristic equation `cos(πν) = w_I(π; a, q)` (DLMF 28.2.16). The principal
exponent `ν̂ = π⁻¹ arccos w_I(π; a, q)` with `0 ≤ ℜν̂ ≤ 1` is one solution; all solutions are
`±ν̂ + 2n`, `n ∈ ℤ`. -/
@[dlmf 28.2.E16]
def IsMathieuCharExp (a q ν : ℂ) : Prop :=
  Complex.cos (π * ν) = mathieuWI a q π

/-- A **Floquet solution** with respect to `ν` (DLMF 28.2.14, §28.2(iv)): a nontrivial solution of
Mathieu's equation with `w(z + π) = e^{πiν} w(z)`. -/
@[dlmf 28.2.E14]
def IsFloquetSolution (a q ν : ℂ) (w : ℂ → ℂ) : Prop :=
  IsMathieuSolution a q w ∧ w ≠ 0 ∧ ∀ z, w (z + π) = Complex.exp (π * I * ν) * w z

end DLMF.Mathieu
