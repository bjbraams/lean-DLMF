/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The ordinary Mellin transform of the first-kind Bessel function

Temme, *Special Functions* (1996), Chapter 9, Exercises 9.9–9.10,
pp. 251–252, synopsis TEM-09-17. The full strip includes conditional convergence;
the upper-endpoint limit is therefore stated using finite-interval integrals.
-/

@[expose] public noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology
namespace DLMF.Bessel

/-- Local integrability of the Mellin kernel at zero. Temme Chapter 9,
Exercises 9.9–9.10, synopsis TEM-09-17. -/
theorem intervalIntegrable_besselJ_mellin {ν s : ℂ} (hzero : 0 < (ν + s).re)
    {R : ℝ} (hR : 0 < R) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s - 1) * besselJ ν t)
      volume 0 R := by
  sorry

/-- The Mellin integral of `J_ν` converges in its full ordinary strip.
Temme Chapter 9, Exercises 9.9–9.10, synopsis TEM-09-17. The conclusion retains
natural increasing truncation even when absolute integrability fails. -/
theorem tendsto_integral_besselJ_mellin {ν s : ℂ}
    (hzero : 0 < (ν + s).re) (hinfty : s.re < 3 / 2) :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R,
      (t : ℂ) ^ (s - 1) * besselJ ν t) atTop
      (𝓝 ((2 : ℂ) ^ (s - 1) * Gamma ((ν + s) / 2) /
        Gamma ((ν - s + 2) / 2))) := by
  sorry

/-- Absolute convergence on the narrower Mellin strip, Temme Chapter 9,
Exercises 9.9–9.10, synopsis TEM-09-17. Exceptional integral orders can enlarge
the lower strip; the stated condition is uniform in the complex order. -/
theorem integrableOn_besselJ_mellin {ν s : ℂ}
    (hzero : 0 < (ν + s).re) (hinfty : s.re < 1 / 2) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * besselJ ν t) (Ioi 0) := by
  sorry

end DLMF.Bessel
