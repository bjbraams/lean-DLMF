/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.LaplaceTransform
public import DLMF.Bessel.YIntegralRep

/-!
# Classical closed forms for Bessel transforms

Temme, *Special Functions* (1996), Chapter 9, (9.2)–(9.4), (9.11),
pp. 220–226, synopses TEM-09-04 and TEM-09-17. The Poisson formula uses
the principal branch on the entire slit plane; the Laplace parameter is positive real.
-/

@[expose] public noncomputable section
open Complex MeasureTheory Set
namespace DLMF.Bessel

/-- The elementary Laplace transform of `J_ν`, Temme (9.11), p. 226,
synopsis TEM-09-17. -/
theorem integral_exp_mul_besselJ_eq_cpow {ν : ℂ} (hν : -1 < ν.re)
    {s : ℝ} (hs : 0 < s) :
    (∫ t : ℝ in Ioi 0, exp (-(s : ℂ) * t) * besselJ ν t) =
      ((s + Real.sqrt (1 + s ^ 2) : ℝ) : ℂ) ^ (-ν) /
        Real.sqrt (1 + s ^ 2) := by
  sorry

/-- Poisson's integral on the full principal slit plane, Temme Chapter 9,
(9.2)–(9.4), synopsis TEM-09-04. The symmetric integration interval encodes
the parity cancellation of the sine part. -/
theorem besselJ_eq_poisson_exponential {ν z : ℂ} (hν : -1 / 2 < ν.re)
    (hz : z ∈ slitPlane) :
    besselJ ν z = (z / 2) ^ ν / (Real.sqrt Real.pi * Gamma (ν + 1 / 2)) *
      ∫ t : ℝ in (-1 : ℝ)..1,
        exp (I * z * t) * (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2) := by
  sorry

/-- The corrected angular-minus-ray integral for arbitrary complex order,
Temme (9.35)–(9.47), pp. 235–238, synopsis TEM-09-08. The ray is absolutely
integrable throughout the right half-plane. -/
theorem integrableOn_and_besselI_eq_angular_sub_ray (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => exp (-z * Real.cosh t - ν * t)) (Ioi 0) ∧
      besselI ν z = (1 / (Real.pi : ℂ)) *
        (∫ θ : ℝ in (0 : ℝ)..Real.pi, exp (z * Real.cos θ) * cos (ν * θ)) -
          sin (Real.pi * ν) / Real.pi *
            ∫ t : ℝ in Ioi 0, exp (-z * Real.cosh t - ν * t) := by
  sorry

end DLMF.Bessel
