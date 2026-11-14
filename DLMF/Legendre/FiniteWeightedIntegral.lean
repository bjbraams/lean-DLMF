/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Basic
public import DLMF.Hypergeometric.EulerIntegral

/-!
# A finite weighted integral for the Legendre Q function

Duverney, *An Introduction to Hypergeometric Functions*, Chapter 4,
equations (4.74)–(4.75), gives this integral for every real degree greater than -1.
It uses the standard principal Legendre Q normalization on the real ray `x>1`.
-/

@[expose] public noncomputable section

open Complex MeasureTheory

namespace DLMF.Legendre

/-- Absolute convergence and evaluation of the weighted finite integral for `Q_ν`.
Duverney (4.74)–(4.75), synopsis DU-4.21. -/
theorem legendreQ_eq_finite_weighted_integral {ν x : ℝ} (hν : -1 < ν) (hx : 1 < x) :
    IntervalIntegrable (fun t : ℝ => (1 - t ^ 2) ^ ν * (x - t) ^ (-ν - 1))
      volume (-1) 1 ∧
      legendreQ ν x = (((2 : ℝ) ^ (-ν - 1) : ℝ) : ℂ) *
        ∫ t in (-1 : ℝ)..1, ((1 - t ^ 2) ^ ν * (x - t) ^ (-ν - 1) : ℝ) := by
  sorry

end DLMF.Legendre
