/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic
public import DLMFMathlib.Analysis.ODE.CircuitMonodromy
public import Mathlib.Analysis.Asymptotics.Defs
public import DLMFMathlib.Analysis.Normed.Field.RelativeErrorQuotient

/-!
# Simple-pole circuit coefficients and their quantitative denominator

Olver, *Asymptotics and Special Functions*, Chapter 13, §§4–6,
pp. 483–491, synopses O-13.02–O-13.03. The recessive solution is the
actual Frobenius series with Bessel-I normalization. The second solution's
coefficient is computed from its continued solution matrix.
-/

@[expose] public noncomputable section
open Complex Filter Set DLMF.Bessel
open scoped Topology
namespace DLMF.AsymptoticApproximations.SimplePoleConnection

/-- The normalized simple-pole potential, with u absorbed into the coordinate.
Olver, Chapter 13, §4, pp. 483–486. -/
def potential (ν : ℝ) (ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  1 / (4 * z) + ((ν : ℂ) ^ 2 - 1) / (4 * z ^ 2) + ψ z / z

/-- The actual normalized recessive Frobenius coefficients.
Olver, Chapter 13, §4. For ν≥0 every recurrence denominator is nonzero. -/
def coefficient (ν : ℝ) (ψ : ℂ → ℂ) : ℕ → ℂ
  | 0 => (2 : ℂ) ^ (-(ν : ℂ)) / Gamma ((ν : ℂ) + 1)
  | n + 1 => (coefficient ν ψ n / 4 + ∑ k : Fin (n + 1),
      iteratedDeriv k ψ 0 / k.val.factorial * coefficient ν ψ (n - k)) /
        ((n + 1 : ℂ) * (n + 1 + ν))

/-- The recessive solution on the logarithmic cover, with leading coefficient
2^(-ν)/Gamma(ν+1). Olver, Chapter 13, §4. -/
def recessive (ν : ℝ) (ψ : ℂ → ℂ) (w : ℂ) : ℂ :=
  exp (((1 + (ν : ℂ)) / 2) * w) * ∑' n : ℕ, coefficient ν ψ n * exp w ^ n

/-- The canonical Bessel-I comparison on the same logarithmic sheet. -/
def comparisonRecessive (ν : ℝ) (w : ℂ) : ℂ :=
  exp (w / 2) * DLMF.Bessel.besselIOnLog ν (w / 2)

/-- The canonical Bessel-K comparison on the same logarithmic sheet. -/
def comparisonDominant (ν : ℝ) (w : ℂ) : ℂ :=
  exp (w / 2) * DLMF.Bessel.besselKOnLog ν (w / 2)

/-- The actual relative recessive error. -/
def recessiveError (ν : ℝ) (ψ : ℂ → ℂ) (w : ℂ) : ℂ :=
  recessive ν ψ w / comparisonRecessive ν w - 1

/-- The actual relative dominant error of a reference-selected solution. -/
def dominantError (ν : ℝ) (S : ℂ → ℂ) (w : ℂ) : ℂ :=
  S w / comparisonDominant ν w - 1

/-- The upper-right entry of the actual continued fundamental matrix is A.
Olver, Chapter 13, §4. Nonzero Wronskian hypotheses are retained by theorems. -/
def monodromyCoefficient (ν : ℝ) (ψ S : ℂ → ℂ) (w₀ : ℂ) : ℂ :=
  Complex.CircuitMonodromy.circuitMatrix ![recessive ν ψ, S] w₀ 0 1

/-- The defining simple-pole potential. -/
theorem potential_def (ν : ℝ) (ψ : ℂ → ℂ) (z : ℂ) : potential ν ψ z =
    1 / (4 * z) + ((ν : ℂ) ^ 2 - 1) / (4 * z ^ 2) + ψ z / z := rfl

/-- The defining leading Frobenius normalization. -/
theorem coefficient_zero (ν : ℝ) (ψ : ℂ → ℂ) : coefficient ν ψ 0 =
    (2 : ℂ) ^ (-(ν : ℂ)) / Gamma ((ν : ℂ) + 1) := by
  rw [coefficient]

/-- The defining finite Frobenius recurrence. -/
theorem coefficient_succ (ν : ℝ) (ψ : ℂ → ℂ) (n : ℕ) : coefficient ν ψ (n + 1) =
    (coefficient ν ψ n / 4 + ∑ k : Fin (n + 1),
      iteratedDeriv k ψ 0 / k.val.factorial * coefficient ν ψ (n - k)) /
        ((n + 1 : ℂ) * (n + 1 + ν)) := by
  rw [coefficient]

/-- The defining logarithmic-cover series. -/
theorem recessive_def (ν : ℝ) (ψ : ℂ → ℂ) (w : ℂ) : recessive ν ψ w =
    exp (((1 + (ν : ℂ)) / 2) * w) * ∑' n : ℕ, coefficient ν ψ n * exp w ^ n := rfl

/-- The defining Bessel-I comparison. -/
theorem comparisonRecessive_def (ν : ℝ) (w : ℂ) : comparisonRecessive ν w =
    exp (w / 2) * DLMF.Bessel.besselIOnLog ν (w / 2) := rfl

/-- The defining Bessel-K comparison. -/
theorem comparisonDominant_def (ν : ℝ) (w : ℂ) : comparisonDominant ν w =
    exp (w / 2) * DLMF.Bessel.besselKOnLog ν (w / 2) := rfl

/-- The defining relative recessive error. -/
theorem recessiveError_def (ν : ℝ) (ψ : ℂ → ℂ) (w : ℂ) : recessiveError ν ψ w =
    recessive ν ψ w / comparisonRecessive ν w - 1 := rfl

/-- The defining relative dominant error. -/
theorem dominantError_def (ν : ℝ) (S : ℂ → ℂ) (w : ℂ) :
    dominantError ν S w = S w / comparisonDominant ν w - 1 := rfl

/-- The defining circuit coefficient. -/
theorem monodromyCoefficient_def (ν : ℝ) (ψ S : ℂ → ℂ) (w₀ : ℂ) :
    monodromyCoefficient ν ψ S w₀ =
      Complex.CircuitMonodromy.circuitMatrix ![recessive ν ψ, S] w₀ 0 1 := rfl

/-- The Frobenius series converges on the full coefficient disc and solves the
normalized equation. Olver, Chapter 13, §4, pp. 483–486. -/
theorem recessive_isLiftedSolution {ν R : ℝ} (hν : 0 ≤ ν) (hR : 0 < R) {ψ : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (Metric.ball 0 R)) :
    Complex.CircuitMonodromy.IsLiftedSolution (fun _ => 0) (fun z => -potential ν ψ z)
      R (recessive ν ψ) := by
  sorry

/-- The exact all-circuit recessive multiplier. Olver, Chapter 13, §4. -/
theorem recessive_add_circuit (ν : ℝ) (ψ : ℂ → ℂ) (w : ℂ) (m : ℤ) :
    recessive ν ψ (w + 2 * Real.pi * I * m) =
      exp ((1 + (ν : ℂ)) * m * Real.pi * I) * recessive ν ψ w := by
  have hperiod : exp (2 * Real.pi * I * m) = 1 := by
    convert exp_int_mul_two_pi_mul_I m using 1
    congr 1
    ring
  have hsum : (fun n : ℕ => coefficient ν ψ n *
      exp (w + 2 * Real.pi * I * m) ^ n) =
        (fun n : ℕ => coefficient ν ψ n * exp w ^ n) := by
    funext n
    rw [exp_add, hperiod, mul_one]
  simp only [recessive]
  rw [hsum, show (1 + (ν : ℂ)) / 2 * (w + 2 * Real.pi * I * m) =
    (1 + (ν : ℂ)) * m * Real.pi * I + (1 + (ν : ℂ)) / 2 * w by ring, exp_add]
  ring

/-- Independence from the recessive Frobenius solution is the nonzero dominant
coefficient condition. Its exact circuit is A*R-exp(-pi*i*nu)*S.
Olver, Chapter 13, §4, pp. 483–486. -/
theorem dominant_add_circuit {ν R : ℝ} (hν : 0 ≤ ν) (hR : 0 < R) {ψ S : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (Metric.ball 0 R))
    (hS : Complex.CircuitMonodromy.IsLiftedSolution
      (fun _ => 0) (fun z => -potential ν ψ z) R S)
    {w₀ : ℂ} (hw₀ : w₀ ∈ Complex.CircuitMonodromy.logDomain R)
    (hdet : (Complex.CircuitMonodromy.fundamentalMatrix ![recessive ν ψ, S] w₀).det ≠ 0)
    {w : ℂ} (hw : w ∈ Complex.CircuitMonodromy.logDomain R) :
    S (w + 2 * Real.pi * I) = monodromyCoefficient ν ψ S w₀ * recessive ν ψ w -
      exp (-Real.pi * I * ν) * S w := by
  sorry

/-- Evaluation at a positive Y_nu zero gives the exact error quotient, retaining
both boundary sheets and the necessary nonzero denominator. Olver §4. -/
theorem monodromyCoefficient_eq_besselY_zero_error_quotient
    {ν R y : ℝ} (hν : 0 ≤ ν) (hR : 0 < R) (hy : 0 < y) (hyR : y ^ 2 < R)
    (hY : besselY ν y = 0) {ψ S : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (Metric.ball 0 R))
    (hS : Complex.CircuitMonodromy.IsLiftedSolution
      (fun _ => 0) (fun z => -potential ν ψ z) R S)
    {w₀ : ℂ} (hw₀ : w₀ ∈ Complex.CircuitMonodromy.logDomain R)
    (hdet : (Complex.CircuitMonodromy.fundamentalMatrix ![recessive ν ψ, S] w₀).det ≠ 0)
    (hden : 1 + recessiveError ν ψ ((2 * Real.log y : ℝ) - Real.pi * I) ≠ 0) :
    monodromyCoefficient ν ψ S w₀ = Real.pi * I *
      (1 + (dominantError ν S ((2 * Real.log y : ℝ) + Real.pi * I) +
        dominantError ν S ((2 * Real.log y : ℝ) - Real.pi * I)) / 2) /
          (1 + recessiveError ν ψ ((2 * Real.log y : ℝ) - Real.pi * I)) := by
  sorry

/-- The exact circuit coefficient has a certified relative bound as soon as the
recessive error is below one. The comparison envelope/variation estimates for
each sheet may be substituted independently in this bound. Olver, Chapter 13,
§4, pp. 483–486. -/
theorem norm_monodromyCoefficient_div_pi_mul_I_sub_one_le
    {ν R y : ℝ} (hν : 0 ≤ ν) (hR : 0 < R) (hy : 0 < y) (hyR : y ^ 2 < R)
    (hY : besselY ν y = 0) {ψ S : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (Metric.ball 0 R))
    (hS : Complex.CircuitMonodromy.IsLiftedSolution
      (fun _ => 0) (fun z => -potential ν ψ z) R S)
    {w₀ : ℂ} (hw₀ : w₀ ∈ Complex.CircuitMonodromy.logDomain R)
    (hdet : (Complex.CircuitMonodromy.fundamentalMatrix ![recessive ν ψ, S] w₀).det ≠ 0)
    (hsmall : ‖recessiveError ν ψ ((2 * Real.log y : ℝ) - Real.pi * I)‖ < 1) :
    let η := recessiveError ν ψ ((2 * Real.log y : ℝ) - Real.pi * I)
    let ε := (dominantError ν S ((2 * Real.log y : ℝ) + Real.pi * I) +
      dominantError ν S ((2 * Real.log y : ℝ) - Real.pi * I)) / 2
    ‖monodromyCoefficient ν ψ S w₀ / (Real.pi * I) - 1‖ ≤
      (‖ε‖ + ‖η‖) / (1 - ‖η‖) := by
  dsimp only
  have hden : 1 + recessiveError ν ψ ((2 * Real.log y : ℝ) - Real.pi * I) ≠ 0 := by
    intro h
    have he : recessiveError ν ψ ((2 * Real.log y : ℝ) - Real.pi * I) = -1 := by
      linear_combination h
    rw [he, norm_neg, norm_one] at hsmall
    exact lt_irrefl _ hsmall
  rw [monodromyCoefficient_eq_besselY_zero_error_quotient hν hR hy hyR hY
    hψ hS hw₀ hdet hden]
  have hpi : (Real.pi : ℂ) * I ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) I_ne_zero
  have hid (ε η : ℂ) : Real.pi * I * (1 + ε) / (1 + η) / (Real.pi * I) =
      (1 + ε) / (1 + η) := by
    field_simp
  rw [hid]
  exact norm_div_relativeError_sub_one_le hsmall

end DLMF.AsymptoticApproximations.SimplePoleConnection
