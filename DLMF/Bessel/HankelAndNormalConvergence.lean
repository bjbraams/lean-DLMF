/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Elementary
public import DLMFMathlib.Topology.Algebra.InfiniteSum.EvenInt
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Hankel representation and normal convergence of Bessel series

Olver, *Asymptotics and Special Functions*, Chapter 2, §§9–10,
pp. 55–61, synopses O-2.22–O-2.24. Hankel banks and the finite circle
are written explicitly, with a logarithmic-coordinate argument for `J`.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set

namespace DLMF.Bessel

/-- Fixed-radius Hankel representation for arbitrary Bessel order, on its logarithmic cover.
Olver, Chapter 2, §9, synopsis O-2.22. -/
theorem besselJOnLog_eq_hankel (ν w : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    besselJOnLog ν w = exp (ν * (w - Real.log 2)) / (2 * Real.pi * I) *
      ((∫ t : ℝ in Ioi ρ, exp (-t + exp (2 * w) / (4 * t)) *
        (exp (-(ν + 1) * ((Real.log t : ℂ) - Real.pi * I)) -
          exp (-(ν + 1) * ((Real.log t : ℂ) + Real.pi * I)))) +
        ∫ θ : ℝ in -Real.pi..Real.pi,
          exp (ρ * exp (θ * I) - exp (2 * w) / (4 * ρ * exp (θ * I))) *
            exp (-(ν + 1) * ((Real.log ρ : ℂ) + θ * I)) *
              (I * ρ * exp (θ * I))) := by
  sorry

/-- The bilateral generating series is absolutely normally convergent jointly in both variables.
Olver, Chapter 2, (9.06), synopsis O-2.22. -/
theorem summableLocallyUniformlyOn_besselJ_generating :
    SummableLocallyUniformlyOn
      (fun n : ℤ => fun p : ℂ × ℂ => besselJ n p.1 * p.2 ^ n) {p | p.2 ≠ 0} := by
  sorry

/-- The bilateral addition series is absolutely normally convergent in both arguments.
Olver, Chapter 2, Exercise 9.2, synopsis O-2.23. -/
theorem summableLocallyUniformly_besselJ_add (n : ℤ) :
    SummableLocallyUniformlyOn
      (fun k : ℤ => fun p : ℂ × ℂ => besselJ k p.1 * besselJ (n - k) p.2) univ := by
  sorry

/-- Poisson's sharp complex-argument bound, including the endpoint order `-1/2`.
Olver, Chapter 2, Exercise 9.6, synopsis O-2.23. -/
theorem norm_besselJ_le_exp_abs_im {ν : ℝ} (hν : -(1 / 2 : ℝ) ≤ ν)
    {z : ℂ} (hz : z ≠ 0) :
    ‖besselJ ν z‖ ≤ (‖z‖ / 2) ^ ν * Real.exp |z.im| / Real.Gamma (ν + 1) := by
  sorry

/-- The modified bilateral generating series is absolutely normally convergent jointly.
Olver, Chapter 2, §10, synopsis O-2.24. -/
theorem summableLocallyUniformlyOn_besselI_generating :
    SummableLocallyUniformlyOn
      (fun n : ℤ => fun p : ℂ × ℂ => besselI n p.1 * p.2 ^ n) {p | p.2 ≠ 0} := by
  sorry

/-- The bilateral sum of the integer-order Bessel squares is one.
Olver, Chapter 2, Exercise 9.2, synopsis O-2.23. -/
theorem hasSum_besselJ_int_sq (z : ℂ) : HasSum (fun m : ℤ => besselJ m z ^ 2) 1 := by
  convert hasSum_besselJ_add 0 z (-z) using 1
  · funext m
    simp [Complex.besselJ_neg_comm, pow_two]
  · simp [Complex.besselJ_zero]

/-- Pairing equal positive/negative orders gives the one-sided sum of Bessel squares.
Olver, Chapter 2, Exercise 9.2, synopsis O-2.23. -/
theorem hasSum_besselJ_nat_succ_sq (z : ℂ) :
    HasSum (fun n : ℕ => besselJ (n + 1) z ^ 2) ((1 - besselJ 0 z ^ 2) / 2) := by
  have heven (m : ℤ) : besselJ (-m) z ^ 2 = besselJ m z ^ 2 := by
    rw [besselJ_neg_int, mul_pow]
    have h : ((-1 : ℂ) ^ m) ^ 2 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp
    rw [h, one_mul]
  simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_zero] using
    (hasSum_besselJ_int_sq z).nat_succ_of_even
      (fun m => by simpa only [Int.cast_neg] using heven m)

end DLMF.Bessel
