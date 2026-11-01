/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Polylogarithms and Lerch's transcendent (DLMF §§25.12, 25.14)

The polylogarithm `Li_s(z)` of complex order (DLMF §25.12), Lerch's transcendent `Φ(z, s, a)`
(DLMF §25.14), and the Fermi–Dirac and Bose–Einstein integrals (DLMF §25.12(iii)). The two
transcendental functions are defined by analytic continuation of their power series from the
unit disk to the cut plane `ℂ \ [1, ∞)`.

## Main definitions

* `slitOne`: the cut plane `ℂ \ [1, ∞)`.
* `slitContinuation`: the analytic continuation from the unit disk to `ℂ \ [1, ∞)`, if one
  exists.
* `polylogSeries`, `polylog`: the series `∑_{n≥1} zⁿ/n^s` (DLMF 25.12.10) and `Li_s(z)`.
* `lerchPhiSeries`, `lerchPhi`: Lerch's series (DLMF 25.14.1) and `Φ(z, s, a)`.
* `fermiDiracF`, `boseEinsteinG`: the Fermi–Dirac and Bose–Einstein integrals
  (DLMF 25.12.14–25.12.15).

## Main results

* `mem_slitOne_of_norm_lt_one`, `isOpen_slitOne`: the cut plane contains the unit disk and is
  open.
* `slitContinuation_eq_of_norm_lt_one`, `polylog_eq_polylogSeries_of_norm_lt_one`,
  `lerchPhi_eq_lerchPhiSeries_of_norm_lt_one`: in the unit disk the functions are their series.
* `polylogSeries_natCast`, `polylogSeries_ofNat`: the series of natural order with natural
  powers.
* `polylog_zero_arg`, `polylogSeries_zero_arg`: `Li_s(0) = 0`.

## Implementation notes

`polylog s z` and `lerchPhi z s a` are the analytic continuations on `ℂ \ [1, ∞)` and the values
of the series on the cut `[1, ∞)`. The continuation is chosen when it exists
(`slitContinuation`); since `ℂ \ [1, ∞)` is connected, it is unique. Its existence, uniqueness
and the other properties are in `DLMF.Zeta.LerchContinuation`, `DLMF.Zeta.Polylog` and
`DLMF.Zeta.Lerch`. The real dilogarithm and trilogarithm `DLMF.Polylog.Real.dilog`,
`DLMF.Polylog.Real.trilog` are the real integral forms; `DLMF.Zeta.Polylog` bridges them to
`polylog`.
-/

@[expose] public section

open Complex Set MeasureTheory

noncomputable section

namespace DLMF.Zeta

/-- The cut plane `ℂ \ [1, ∞)`. -/
def slitOne : Set ℂ := {z | z.im ≠ 0 ∨ z.re < 1}

open scoped Classical in
/-- The analytic continuation of `f` from the open unit disk to `ℂ \ [1, ∞)`, if one exists
(unique, the cut plane being connected); otherwise `f` itself. -/
def slitContinuation (f : ℂ → ℂ) : ℂ → ℂ :=
  if h : ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F slitOne ∧ ∀ z, ‖z‖ < 1 → F z = f z then h.choose
  else f

/-- **The polylogarithm series of complex order** `∑_{n≥1} zⁿ/n^s` (DLMF 25.12.10), as a `tsum`
(principal powers `n^s = e^{s ln n}`). Convergent for `|z| < 1`, and for `|z| = 1` when
`Re s > 1`. -/
@[dlmf 25.12.E10]
def polylogSeries (s z : ℂ) : ℂ := ∑' n : ℕ, z ^ (n + 1) / ((n : ℂ) + 1) ^ s

open scoped Classical in
/-- **The polylogarithm** `Li_s(z)` (DLMF §25.12(ii), and `Li₂` of §25.12(i)): the analytic
continuation of 25.12.10 to `ℂ \ [1, ∞)` (principal branch); on `[1, ∞)` the value of the series
(so `Li_s(1) = ζ(s)` for `Re s > 1`, and junk on `(1, ∞)`). -/
@[dlmf 25.12.ii]
def polylog (s z : ℂ) : ℂ :=
  if z ∈ slitOne then slitContinuation (polylogSeries s) z else polylogSeries s z

/-- For natural order the powers in the series 25.12.10 are natural powers. -/
theorem polylogSeries_natCast (n : ℕ) (z : ℂ) :
    polylogSeries n z = ∑' k : ℕ, z ^ (k + 1) / ((k : ℂ) + 1) ^ n := by
  simp only [polylogSeries, cpow_natCast]

/-- `polylogSeries_natCast` for numeric literals. -/
theorem polylogSeries_ofNat (n : ℕ) [n.AtLeastTwo] (z : ℂ) :
    polylogSeries ofNat(n) z = ∑' k : ℕ, z ^ (k + 1) / ((k : ℂ) + 1) ^ ofNat(n) := by
  simpa using polylogSeries_natCast ofNat(n) z

/-- The series vanishes at `z = 0`. -/
@[simp]
theorem polylogSeries_zero_arg (s : ℂ) : polylogSeries s 0 = 0 := by
  simp [polylogSeries]

/-- Formula under the stated hypotheses: `z ∈ slitOne`. -/
theorem mem_slitOne_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : z ∈ slitOne :=
  Or.inr (lt_of_le_of_lt (re_le_norm z) hz)

/-- The indicated domain is open: `IsOpen slitOne`. -/
theorem isOpen_slitOne : IsOpen slitOne :=
  (isOpen_ne_fun continuous_im continuous_const).union
    (isOpen_lt continuous_re continuous_const)

/-- **Lerch's series** `∑_{n≥0} zⁿ/(a+n)^s` (DLMF 25.14.1), as a `tsum`, principal powers. -/
@[dlmf 25.14.E1]
def lerchPhiSeries (z s a : ℂ) : ℂ := ∑' n : ℕ, z ^ n / (a + n) ^ s

open scoped Classical in
/-- **Lerch's transcendent** `Φ(z, s, a)` (DLMF §25.14(i)): the analytic continuation in `z` of
25.14.1 from the unit disk to `ℂ \ [1, ∞)`, and the series on `[1, ∞)`. -/
@[dlmf 25.14.i]
def lerchPhi (z s a : ℂ) : ℂ :=
  if z ∈ slitOne then slitContinuation (fun w => lerchPhiSeries w s a) z
  else lerchPhiSeries z s a

/-- **Fermi–Dirac integral** (DLMF 25.12.14): `F_s(x) = (1/Γ(s+1)) ∫_0^∞ t^s/(e^{t-x} + 1) dt`,
`s > -1`. -/
@[dlmf 25.12.E14]
def fermiDiracF (s x : ℝ) : ℝ :=
  1 / Real.Gamma (s + 1) * ∫ t in Ioi (0 : ℝ), t ^ s / (Real.exp (t - x) + 1)

/-- **Bose–Einstein integral** (DLMF 25.12.15): `G_s(x) = (1/Γ(s+1)) ∫_0^∞ t^s/(e^{t-x} - 1) dt`,
for `s > -1`, `x < 0`, or `s > 0`, `x ≤ 0`. -/
@[dlmf 25.12.E15]
def boseEinsteinG (s x : ℝ) : ℝ :=
  1 / Real.Gamma (s + 1) * ∫ t in Ioi (0 : ℝ), t ^ s / (Real.exp (t - x) - 1)

/-- On the open unit disk the continuation `slitContinuation f` agrees with `f`. -/
theorem slitContinuation_eq_of_norm_lt_one (f : ℂ → ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    slitContinuation f z = f z := by
  unfold slitContinuation
  split_ifs with h
  · exact h.choose_spec.2 z hz
  · rfl

/-- In the open unit disk `Li_s(z)` is the value of the series 25.12.10. -/
theorem polylog_eq_polylogSeries_of_norm_lt_one (s : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    polylog s z = polylogSeries s z := by
  rw [polylog, ite_cond_eq_true _ _ (eq_true (mem_slitOne_of_norm_lt_one hz)),
    slitContinuation_eq_of_norm_lt_one _ hz]

/-- `Li_s(0) = 0`. -/
@[simp]
theorem polylog_zero_arg (s : ℂ) : polylog s 0 = 0 := by
  rw [polylog_eq_polylogSeries_of_norm_lt_one s (by simp), polylogSeries]
  simp

/-- In the open unit disk `Φ(z, s, a)` is the value of the series 25.14.1. -/
theorem lerchPhi_eq_lerchPhiSeries_of_norm_lt_one (s a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    lerchPhi z s a = lerchPhiSeries z s a := by
  rw [lerchPhi, ite_cond_eq_true _ _ (eq_true (mem_slitOne_of_norm_lt_one hz)),
    slitContinuation_eq_of_norm_lt_one _ hz]

end DLMF.Zeta

end
