/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.LogarithmicAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Cylinder functions on every logarithmic branch

Olver, *Asymptotics and Special Functions*, Chapter 7, §§5–8, pp. 238–253
(synopsis O-7.06–O-7.07, O-7.13), and Chapter 10, §3. Integer half-turns
use the entire polynomial `U_(m-1)(cos(pi*nu))` in place of a singular sine
quotient, retaining integer orders. Every derivative is with respect to the
logarithmic coordinate `w`, so the ordinary derivative includes `exp(w)`.
-/

@[expose] public noncomputable section

open Complex Filter Asymptotics
open scoped Real Topology

namespace DLMF.Bessel

/-- Joint analyticity of the four lifted cylinder functions in order and logarithmic
argument, including the removable integer orders. Olver, Chapter 7, §§5–8,
pp. 238–253, synopsis O-7.06/O-7.13. -/
theorem analyticOnNhd_cylinderOnLog :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => besselJOnLog p.1 p.2) Set.univ ∧
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => besselYOnLog p.1 p.2) Set.univ ∧
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => besselIOnLog p.1 p.2) Set.univ ∧
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => besselKOnLog p.1 p.2) Set.univ := by
  sorry

/-- The two order recurrences and the logarithmic derivative for all four ordinary
cylinder families, on every lift. Olver, Chapter 7, §§5–6, synopsis O-7.06. -/
theorem cylinderOnLog_recurrences (ν w : ℂ) :
    ∀ C ∈ ({besselJOnLog, besselYOnLog, hankelH1OnLog, hankelH2OnLog} :
      Set (ℂ → ℂ → ℂ)),
      C (ν - 1) w + C (ν + 1) w = 2 * ν * exp (-w) * C ν w ∧
      HasDerivAt (C ν) (exp w / 2 * (C (ν - 1) w - C (ν + 1) w)) w := by
  sorry

/-- Modified cylinder recurrences and logarithmic derivatives on every branch.
Olver, Chapter 7, §8, pp. 250–253, synopsis O-7.13. -/
theorem modifiedCylinderOnLog_recurrences (ν w : ℂ) :
    besselIOnLog (ν - 1) w - besselIOnLog (ν + 1) w =
      2 * ν * exp (-w) * besselIOnLog ν w ∧
    HasDerivAt (besselIOnLog ν)
      (exp w / 2 * (besselIOnLog (ν - 1) w + besselIOnLog (ν + 1) w)) w ∧
    besselKOnLog (ν + 1) w - besselKOnLog (ν - 1) w =
      2 * ν * exp (-w) * besselKOnLog ν w ∧
    HasDerivAt (besselKOnLog ν)
      (-(exp w / 2) * (besselKOnLog (ν - 1) w + besselKOnLog (ν + 1) w)) w := by
  sorry

/-- The lifted Bessel equations use `D_w² = z²D_z²+zD_z`.
Olver, Chapter 7, §§5–8, synopsis O-7.06/O-7.13. -/
theorem cylinderOnLog_ode (ν w : ℂ) :
    (∀ C ∈ ({besselJOnLog, besselYOnLog, hankelH1OnLog, hankelH2OnLog} :
      Set (ℂ → ℂ → ℂ)),
      iteratedDeriv 2 (C ν) w + ((exp w) ^ 2 - ν ^ 2) * C ν w = 0) ∧
    iteratedDeriv 2 (besselIOnLog ν) w - ((exp w) ^ 2 + ν ^ 2) * besselIOnLog ν w = 0 ∧
    iteratedDeriv 2 (besselKOnLog ν) w - ((exp w) ^ 2 + ν ^ 2) * besselKOnLog ν w = 0 := by
  sorry

/-- The exact I/J rotation with a correlated logarithmic half-turn.
Olver, Chapter 7, §8, synopsis O-7.13. -/
theorem besselIOnLog_eq_besselJOnLog (ν w : ℂ) :
    besselIOnLog ν w = exp (-I * π * ν / 2) * besselJOnLog ν (w + I * π / 2) := by
  sorry

/-- First-kind cylinder monodromy for every integer half-turn and complex order.
Olver, Chapter 7, §§5–8 and Chapter 10, §3, synopsis O-7.06/O-7.13/O-10.08. -/
theorem besselFirstKindOnLog_add_int_mul_pi (ν w : ℂ) (m : ℤ) :
    besselJOnLog ν (w + m * π * I) = exp (m * π * I * ν) * besselJOnLog ν w ∧
    besselIOnLog ν (w + m * π * I) = exp (m * π * I * ν) * besselIOnLog ν w := by
  sorry

/-- Second-kind cylinder monodromy, cleared at every integer order by the Chebyshev
sine polynomial. Olver, Chapter 7, §§5–6 and Chapter 10, §3,
synopsis O-7.06/O-10.08. -/
theorem besselYOnLog_add_int_mul_pi (ν w : ℂ) (m : ℤ) :
    besselYOnLog ν (w + m * π * I) =
      exp (-m * π * I * ν) * besselYOnLog ν w +
        2 * I * cos (π * ν) * (Polynomial.Chebyshev.U ℂ (m - 1)).eval (cos (π * ν)) *
          besselJOnLog ν w := by
  sorry

/-- Modified second-kind monodromy with the removable sine quotient cleared.
This includes all integer orders and positive or negative integer half-turns.
Olver, Chapter 7, §8 and Chapter 10, §3, synopsis O-7.13/O-10.08. -/
theorem besselKOnLog_add_int_mul_pi (ν w : ℂ) (m : ℤ) :
    besselKOnLog ν (w + m * π * I) =
      exp (-m * π * I * ν) * besselKOnLog ν w -
        π * I * (Polynomial.Chebyshev.U ℂ (m - 1)).eval (cos (π * ν)) * besselIOnLog ν w := by
  sorry

/-- The exact connection producing both I exponentials in the upper or lower continued
sector. Olver, Chapter 7, §8, synopsis O-7.13. -/
theorem besselIOnLog_eq_besselKOnLog_connection (ν w : ℂ) (upper : Bool) :
    besselIOnLog ν w =
      if upper then
        (besselKOnLog ν (w - π * I) - exp (π * I * ν) * besselKOnLog ν w) / (π * I)
      else
        (exp (-π * I * ν) * besselKOnLog ν w - besselKOnLog ν (w + π * I)) / (π * I) := by
  sorry

/-- Full two-exponential I expansion, with absolute envelope rather than relative error
at zeros of either exponential combination. The lower sector is the reflected upper
sector. Olver, Chapter 7, §8, pp. 250–253, synopsis O-7.13. -/
theorem isBigO_besselIOnLog_two_exponentials (ν : ℂ) (upper : Bool) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    let sign : ℂ := if upper then 1 else -1
    let lower := if upper then -π / 2 + δ else -(3 * π / 2) + δ
    let higher := if upper then 3 * π / 2 - δ else π / 2 - δ
    IsBigO (comap (fun w : ℂ => w.re) atTop ⊓
      𝓟 {w : ℂ | lower ≤ w.im ∧ w.im ≤ higher})
      (fun w : ℂ => besselIOnLog ν w -
        exp (-w / 2) / (Real.sqrt (2 * π) : ℂ) *
          (exp (exp w) * ∑ k ∈ Finset.range N,
              (-1 : ℂ) ^ k * largeArgumentCoefficient ν k * exp (-k * w) +
            exp (sign * I * π * (ν + 1 / 2) - exp w) *
              ∑ k ∈ Finset.range N,
                largeArgumentCoefficient ν k * exp (-k * w)))
      (fun w : ℂ => Real.exp (-(N + 1 / 2) * w.re) *
        (Real.exp ((exp w).re) + Real.exp (-(exp w).re))) := by
  sorry

end DLMF.Bessel
