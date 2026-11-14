/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The beta transform on the principal cut plane

Andrews, Askey and Roy, *Special Functions*, Theorem 2.2.4, pp. 67–69
(synopsis AAR-2.2.1–2.2.7). The regularized continued Gauss function, rather
than the totalized disk series outside its convergence disk, is used throughout.
-/

@[expose] public section

open Complex MeasureTheory

namespace DLMF.Hypergeometric

/-- The fractional beta transform on the full principal cut plane.
Andrews–Askey–Roy, *Special Functions*, Theorem 2.2.4, pp. 67–69
(synopsis AAR-2.2.1–2.2.7). The positive real-part hypotheses guarantee absolute
endpoint convergence; the complete weighted integrand is explicitly integrable. -/
theorem regularizedGaussHypergeometric_eq_beta_integral {a b c d z : ℂ}
    (hd : 0 < d.re) (hcd : 0 < (c - d).re) (hz : z ∈ cutPlane) :
    IntervalIntegrable (fun t : ℝ =>
      regularizedGaussHypergeometric a b d (z * t) *
        (t : ℂ) ^ (d - 1) * (1 - t : ℂ) ^ (c - d - 1)) volume 0 1 ∧
    regularizedGaussHypergeometric a b c z =
      (Gamma (c - d))⁻¹ * ∫ t : ℝ in (0 : ℝ)..1,
        regularizedGaussHypergeometric a b d (z * t) *
          (t : ℂ) ^ (d - 1) * (1 - t : ℂ) ^ (c - d - 1) := by
  sorry


/-- Erdélyi's product beta integral on the full principal cut plane, in regularized
normalization. Andrews–Askey–Roy, *Special Functions*, Theorem 2.9.1,
pp. 111–114 (synopsis AAR-2.9.1); also Rao–Lakshminarayanan (8.7), RL-8.03.
The two regularization factors cancel the beta prefactor completely. -/
theorem regularizedGaussHypergeometric_eq_erdelyi_product_integral
    (a b c μ lam : ℂ) (hμ : 0 < μ.re) (hcμ : 0 < (c - μ).re) {z : ℂ}
    (hz : z ∈ cutPlane) :
    let F := fun t : ℝ => (t : ℂ) ^ (μ - 1) * (1 - t : ℂ) ^ (c - μ - 1) *
      (1 - z * t) ^ (lam - a - b) *
        regularizedGaussHypergeometric (lam - a) (lam - b) μ (z * t) *
        regularizedGaussHypergeometric (a + b - lam) (lam - μ) (c - μ)
          (z * (1 - t) / (1 - z * t))
    IntervalIntegrable F volume 0 1 ∧
      regularizedGaussHypergeometric a b c z = ∫ t : ℝ in (0 : ℝ)..1, F t := by
  sorry

end DLMF.Hypergeometric
