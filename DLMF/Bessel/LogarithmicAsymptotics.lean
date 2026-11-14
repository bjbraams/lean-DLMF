/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic
public import DLMF.Core.Basic
public import DLMF.Hypergeometric.Basic.Pochhammer
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion

/-!
# Full lifted-sector Bessel asymptotics

Temme, *Special Functions* (1996), §9.7, (9.49)–(9.55), synopsis TEM-09-09.
The logarithmic variable preserves continuation beyond a principal cut; the
Hankel sectors are centered at `±π/2` on that covering.
-/

@[expose] public noncomputable section
open Complex Filter Asymptotics DLMF.Core DLMF.Hypergeometric
open scoped Real Nat Topology
namespace DLMF.Bessel

/-- The classical Hankel coefficient `a_n(ν)`, Temme (9.49)–(9.55), TEM-09-09. -/
def largeArgumentCoefficient (ν : ℂ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ n * pochhammer (ν + 1 / 2) n * pochhammer (1 / 2 - ν) n /
    (2 ^ n * n.factorial)

/-- The defining Pochhammer formula for the classical Hankel coefficients,
Temme (9.49)–(9.55), TEM-09-09. -/
theorem largeArgumentCoefficient_def (ν : ℂ) (n : ℕ) :
    largeArgumentCoefficient ν n =
      (-1 : ℂ) ^ n * pochhammer (ν + 1 / 2) n * pochhammer (1 / 2 - ν) n /
        (2 ^ n * n.factorial) := rfl

/-- Initial Hankel coefficient, Temme (9.49), synopsis TEM-09-09. -/
@[simp] theorem largeArgumentCoefficient_zero (ν : ℂ) : largeArgumentCoefficient ν 0 = 1 := by
  simp [largeArgumentCoefficient, pochhammer]

/-- The coefficient recurrence, Temme (9.49), synopsis TEM-09-09. -/
theorem largeArgumentCoefficient_succ (ν : ℂ) (n : ℕ) :
    largeArgumentCoefficient ν (n + 1) =
      (4 * ν ^ 2 - (2 * n + 1) ^ 2) /
        (8 * (n + 1)) * largeArgumentCoefficient ν n := by
  sorry

/-- Principal-branch agreement for the lifted first kind,
Temme §§9.2–9.3, synopses TEM-09-01/09. -/
theorem besselJOnLog_log (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    besselJOnLog ν (log z) = besselJ ν z := by
  sorry

/-- Principal-branch agreement for the lifted second kind,
Temme §§9.3 and 9.7, synopses TEM-09-02/09. -/
theorem besselYOnLog_log (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    besselYOnLog ν (log z) = besselY ν z := by
  sorry

/-- Principal-branch agreement for the lifted modified first kind,
Temme §§9.5 and 9.7, synopses TEM-09-06/09. -/
theorem besselIOnLog_log (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    besselIOnLog ν (log z) = besselI ν z := by
  sorry

/-- Principal-branch agreement for the lifted modified second kind,
Temme §§9.5 and 9.7, synopses TEM-09-06/09. -/
theorem besselKOnLog_log (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    besselKOnLog ν (log z) = besselK ν z := by
  sorry

/-- Full lifted-sector `K` expansion, Temme (9.49)–(9.55), synopsis TEM-09-09. -/
theorem hasAsymptoticExpansion_besselKOnLog (ν : ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < 3 * Real.pi / 2) :
    HasAsymptoticExpansion (logSector (3 * Real.pi / 2 - δ))
      (fun n w => exp (-(n : ℂ) * w)) (largeArgumentCoefficient ν)
      (fun w => Real.sqrt (2 / Real.pi) * exp (w / 2 + exp w) * besselKOnLog ν w) := by
  sorry

/-- Full lifted-sector `I` expansion, Temme (9.49)–(9.55), synopsis TEM-09-09. -/
theorem hasAsymptoticExpansion_besselIOnLog (ν : ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < Real.pi / 2) :
    HasAsymptoticExpansion (logSector (Real.pi / 2 - δ))
      (fun n w => exp (-(n : ℂ) * w))
      (fun n => (-1 : ℂ) ^ n * largeArgumentCoefficient ν n)
      (fun w => Real.sqrt (2 * Real.pi) * exp (w / 2 - exp w) * besselIOnLog ν w) := by
  sorry

/-- First Hankel expansion on `-π+δ ≤ Im w ≤ 2π-δ`,
Temme (9.49)–(9.55), synopsis TEM-09-09. -/
theorem hasAsymptoticExpansion_hankelH1OnLog (ν : ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < 3 * Real.pi / 2) :
    HasAsymptoticExpansion
      (comap (fun w : ℂ => w - I * Real.pi / 2) (logSector (3 * Real.pi / 2 - δ)))
      (fun n w => exp (-(n : ℂ) * w))
      (fun n => I ^ n * largeArgumentCoefficient ν n)
      (fun w => Real.sqrt (Real.pi / 2) *
        exp (w / 2 - I * (exp w - ν * Real.pi / 2 - Real.pi / 4)) *
        hankelH1OnLog ν w) := by
  sorry

/-- Second Hankel expansion on `-2π+δ ≤ Im w ≤ π-δ`,
Temme (9.49)–(9.55), synopsis TEM-09-09. -/
theorem hasAsymptoticExpansion_hankelH2OnLog (ν : ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < 3 * Real.pi / 2) :
    HasAsymptoticExpansion
      (comap (fun w : ℂ => w + I * Real.pi / 2) (logSector (3 * Real.pi / 2 - δ)))
      (fun n w => exp (-(n : ℂ) * w))
      (fun n => (-I) ^ n * largeArgumentCoefficient ν n)
      (fun w => Real.sqrt (Real.pi / 2) *
        exp (w / 2 + I * (exp w - ν * Real.pi / 2 - Real.pi / 4)) *
        hankelH2OnLog ν w) := by
  sorry

/-- The ordinary first-kind expansion with the full complex-sector error scale,
Temme (9.49)–(9.55), synopsis TEM-09-09. -/
theorem isBigO_besselJOnLog_remainder (ν : ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < Real.pi) (N : ℕ) :
    (fun w : ℂ => besselJOnLog ν w - Real.sqrt (2 / Real.pi) * exp (-w / 2) *
      ∑ n ∈ Finset.range N, largeArgumentCoefficient ν n * exp (-(n : ℂ) * w) *
        cos (exp w - ν * Real.pi / 2 - Real.pi / 4 + n * Real.pi / 2))
      =O[logSector (Real.pi - δ)]
        (fun w : ℂ => Real.exp (|(exp w).im| - ((N : ℝ) + 1 / 2) * w.re)) := by
  sorry

/-- The ordinary second-kind expansion with the full complex-sector error scale,
Temme (9.49)–(9.55), synopsis TEM-09-09. -/
theorem isBigO_besselYOnLog_remainder (ν : ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < Real.pi) (N : ℕ) :
    (fun w : ℂ => besselYOnLog ν w - Real.sqrt (2 / Real.pi) * exp (-w / 2) *
      ∑ n ∈ Finset.range N, largeArgumentCoefficient ν n * exp (-(n : ℂ) * w) *
        sin (exp w - ν * Real.pi / 2 - Real.pi / 4 + n * Real.pi / 2))
      =O[logSector (Real.pi - δ)]
        (fun w : ℂ => Real.exp (|(exp w).im| - ((N : ℝ) + 1 / 2) * w.re)) := by
  sorry

end DLMF.Bessel
