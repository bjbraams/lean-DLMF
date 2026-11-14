/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bessel functions: definitions

Mathlib provides the first-kind Bessel function `Complex.besselJ`. This file defines the
second-kind, Hankel and modified Bessel functions (DLMF §§10.2, 10.4, 10.25, 10.27), with
integer orders given by limits in the order parameter. The calculus of the series `₀F̃₁` is in
`DLMF.Bessel.Basic.RegularizedSeries`; Bessel's equation, derivatives, recurrences and
Wronskians are in `DLMF.Bessel.Basic.Equation` and `DLMF.Bessel.Basic.SecondKind`.

## Main definitions

* `besselY`: Weber's function `Y_ν` (DLMF 10.2.3).
* `besselI`: the modified Bessel function `I_ν` (DLMF 10.25.2).
* `besselK`: Macdonald's function `K_ν` (DLMF 10.27.4).
* `hankelH1`, `hankelH2`: the Hankel functions `H_ν^{(1,2)} = J_ν ± i Y_ν` (DLMF 10.4.3).
* `sphericalJ`, `sphericalI`: the spherical Bessel functions `j_n` and `i_n` (DLMF §10.47), as
  entire functions through `₀F̃₁`, with their removable values at `0`.
-/

@[expose] public noncomputable section

open Complex
open scoped Real Nat Topology

namespace DLMF.Bessel

/-- Bessel function of the second kind (Weber's `Y_ν`), with integer orders
defined by their limits in the order parameter (AAR §4.6). -/
@[dlmf 10.2.E3]
def besselY (ν z : ℂ) : ℂ := by
  classical
  exact if ∃ k : ℤ, ν = k then
    Filter.limUnder (𝓝[≠] ν) (fun μ =>
      (besselJ μ z * cos (μ * π) - besselJ (-μ) z) / sin (μ * π))
  else (besselJ ν z * cos (ν * π) - besselJ (-ν) z) / sin (ν * π)

/-- Modified Bessel function of the first kind. -/
@[dlmf 10.25.E2]
def besselI (ν z : ℂ) : ℂ :=
  (z / 2) ^ ν * regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (z ^ 2 / 4)

/-- Modified Bessel function of the second kind (Macdonald's `K_ν`), with integer
orders defined by their limits in the order parameter (AAR (4.12.3)). -/
@[dlmf 10.27.E4]
def besselK (ν z : ℂ) : ℂ := by
  classical
  exact if ∃ k : ℤ, ν = k then
    Filter.limUnder (𝓝[≠] ν) (fun μ =>
      π / 2 * (besselI (-μ) z - besselI μ z) / sin (μ * π))
  else π / 2 * (besselI (-ν) z - besselI ν z) / sin (ν * π)

/-- Hankel's function of the first kind, `H_ν^{(1)} = J_ν + i Y_ν` (DLMF 10.4.3). -/
@[dlmf 10.4.E3]
def hankelH1 (ν z : ℂ) : ℂ := besselJ ν z + I * besselY ν z

/-- Hankel's function of the second kind, `H_ν^{(2)} = J_ν - i Y_ν` (DLMF 10.4.3). -/
@[dlmf 10.4.E3]
def hankelH2 (ν z : ℂ) : ℂ := besselJ ν z - I * besselY ν z

/-- Spherical j_n, with the removable value at zero supplied explicitly. -/
def sphericalJ (n : ℕ) (z : ℂ) : ℂ :=
  Real.sqrt π * z ^ n / (2 : ℂ) ^ (n+1) *
    regularizedHGFun ∅ {(n : ℂ)+3/2} (-z^2/4)
/-- Modified spherical i_n, including its removable value at zero. -/
def sphericalI (n : ℕ) (z : ℂ) : ℂ :=
  Real.sqrt π * z ^ n / (2 : ℂ) ^ (n+1) *
    regularizedHGFun ∅ {(n : ℂ)+3/2} (z^2/4)


/-- First-kind Bessel function on the logarithmic plane `z=exp w`, with power
`exp(ν(w-log 2))`, Temme §9.7, (9.49)–(9.55), synopsis TEM-09-09. -/
def besselJOnLog (ν w : ℂ) : ℂ :=
  exp (ν * (w - Real.log 2)) * regularizedHGFun ∅ {ν + 1} (-((exp w / 2) ^ 2))

/-- Modified first-kind Bessel function on the logarithmic plane,
Temme §9.7, (9.49)–(9.55), synopsis TEM-09-09. -/
def besselIOnLog (ν w : ℂ) : ℂ :=
  exp (ν * (w - Real.log 2)) * regularizedHGFun ∅ {ν + 1} ((exp w) ^ 2 / 4)

/-- Second-kind Bessel function on the logarithmic plane, with removable
integer orders defined by the order limit, Temme §§9.3 and 9.7, TEM-09-02/09. -/
def besselYOnLog (ν w : ℂ) : ℂ := by
  classical
  exact if ∃ k : ℤ, ν = k then
    Filter.limUnder (𝓝[≠] ν) (fun μ =>
      (besselJOnLog μ w * cos (μ * π) - besselJOnLog (-μ) w) / sin (μ * π))
  else (besselJOnLog ν w * cos (ν * π) - besselJOnLog (-ν) w) / sin (ν * π)

/-- Modified second-kind Bessel function on the logarithmic plane, with
removable integer orders defined by their order limits, Temme §9.5/9.7, TEM-09-06/09. -/
def besselKOnLog (ν w : ℂ) : ℂ := by
  classical
  exact if ∃ k : ℤ, ν = k then
    Filter.limUnder (𝓝[≠] ν) (fun μ =>
      π / 2 * (besselIOnLog (-μ) w - besselIOnLog μ w) / sin (μ * π))
  else π / 2 * (besselIOnLog (-ν) w - besselIOnLog ν w) / sin (ν * π)

/-- First Hankel function on the logarithmic plane, Temme §§9.3 and 9.7, TEM-09-09. -/
def hankelH1OnLog (ν w : ℂ) : ℂ := besselJOnLog ν w + I * besselYOnLog ν w

/-- Second Hankel function on the logarithmic plane, Temme §§9.3 and 9.7, TEM-09-09. -/
def hankelH2OnLog (ν w : ℂ) : ℂ := besselJOnLog ν w - I * besselYOnLog ν w

/-- The series defining the lifted first-kind Bessel function, Temme (9.12). -/
theorem besselJOnLog_def (ν w : ℂ) : besselJOnLog ν w =
    exp (ν * (w - Real.log 2)) *
      regularizedHGFun ∅ {ν + 1} (-((exp w / 2) ^ 2)) := rfl

/-- The series defining the lifted modified first-kind Bessel function, Temme (9.26). -/
theorem besselIOnLog_def (ν w : ℂ) : besselIOnLog ν w =
    exp (ν * (w - Real.log 2)) * regularizedHGFun ∅ {ν + 1} ((exp w) ^ 2 / 4) := rfl

/-- The two order cases defining the lifted Bessel function of the second kind,
Temme §§9.3 and 9.7, synopsis TEM-09-02/09. -/
theorem besselYOnLog_def (ν w : ℂ) :
    ((∃ k : ℤ, ν = k) → besselYOnLog ν w =
      Filter.limUnder (𝓝[≠] ν) (fun μ =>
        (besselJOnLog μ w * cos (μ * π) - besselJOnLog (-μ) w) / sin (μ * π))) ∧
    ((∀ k : ℤ, ν ≠ k) → besselYOnLog ν w =
      (besselJOnLog ν w * cos (ν * π) - besselJOnLog (-ν) w) / sin (ν * π)) := by
  classical
  constructor
  · intro h
    simp only [besselYOnLog, h, ↓reduceIte]
  · intro h
    simp only [besselYOnLog, not_exists.mpr h, ↓reduceIte]

/-- The two order cases defining the lifted modified Bessel function of the second kind,
Temme §§9.5 and 9.7, synopsis TEM-09-06/09. -/
theorem besselKOnLog_def (ν w : ℂ) :
    ((∃ k : ℤ, ν = k) → besselKOnLog ν w =
      Filter.limUnder (𝓝[≠] ν) (fun μ =>
        π / 2 * (besselIOnLog (-μ) w - besselIOnLog μ w) / sin (μ * π))) ∧
    ((∀ k : ℤ, ν ≠ k) → besselKOnLog ν w =
      π / 2 * (besselIOnLog (-ν) w - besselIOnLog ν w) / sin (ν * π)) := by
  classical
  constructor
  · intro h
    simp only [besselKOnLog, h, ↓reduceIte]
  · intro h
    simp only [besselKOnLog, not_exists.mpr h, ↓reduceIte]

/-- The first lifted Hankel function's defining linear combination, Temme (9.8). -/
theorem hankelH1OnLog_def (ν w : ℂ) :
    hankelH1OnLog ν w = besselJOnLog ν w + I * besselYOnLog ν w := rfl

/-- The second lifted Hankel function's defining linear combination, Temme (9.9). -/
theorem hankelH2OnLog_def (ν w : ℂ) :
    hankelH2OnLog ν w = besselJOnLog ν w - I * besselYOnLog ν w := rfl

/-- The nonintegral lifted second-kind connection, Temme (9.5)–(9.7). -/
theorem besselYOnLog_of_not_int {ν : ℂ} (hν : ∀ k : ℤ, ν ≠ k) (w : ℂ) :
    besselYOnLog ν w =
      (besselJOnLog ν w * cos (ν * π) - besselJOnLog (-ν) w) / sin (ν * π) := by
  simp [besselYOnLog, not_exists.mpr hν]

/-- The nonintegral lifted modified connection, Temme (9.29). -/
theorem besselKOnLog_of_not_int {ν : ℂ} (hν : ∀ k : ℤ, ν ≠ k) (w : ℂ) :
    besselKOnLog ν w = π / 2 *
      (besselIOnLog (-ν) w - besselIOnLog ν w) / sin (ν * π) := by
  simp [besselKOnLog, not_exists.mpr hν]

/-- The first spherical Hankel function on the principal branch for nonzero argument,
normalized by `sqrt(π/(2z)) Hₙ₊₁/₂⁽¹⁾(z)`. Temme Chapter 10, (10.10), TEM-10-07. -/
def sphericalH1 (n : ℕ) (z : ℂ) : ℂ :=
  (π / (2 * z)) ^ (1 / 2 : ℂ) * hankelH1 (n + 1 / 2) z

/-- The defining spherical Hankel normalization, Temme (10.10), TEM-10-07. -/
theorem sphericalH1_def (n : ℕ) (z : ℂ) :
    sphericalH1 n z = (π / (2 * z)) ^ (1 / 2 : ℂ) * hankelH1 (n + 1 / 2) z := rfl

end DLMF.Bessel
