/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Recurrences
public import DLMF.Hypergeometric.ConnectionFormulas

/-!
# Ordinary Legendre series at zero and at the logarithmic endpoint

Temme, *Special Functions* (1996), Chapter 8, equations (8.15)–(8.23),
pages 198–200. The degree is genuinely complex. The endpoint series covers its
entire slit disk, including points outside the lens where both original Gauss
power series converge.
-/

@[expose] public noncomputable section

open Complex DLMF.Hypergeometric
open scoped Real

namespace DLMF.Legendre

/-- The even/odd zero-centered expansion of the Legendre function for every complex degree.
Gamma quotients are interpreted as products of entire reciprocal Gamma values.
Temme (8.15)–(8.17), synopsis TEM-08-03. -/
theorem legendreP_eq_even_add_odd_hypergeometric (ν : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    legendreP ν z =
      (Real.sqrt π : ℂ) / (Gamma ((1 - ν) / 2) * Gamma (1 + ν / 2)) *
        ordinaryHypergeometric (-ν / 2) ((ν + 1) / 2) (1 / 2) (z ^ 2) -
      2 * (Real.sqrt π : ℂ) / (Gamma (-ν / 2) * Gamma ((ν + 1) / 2)) * z *
        ordinaryHypergeometric ((1 - ν) / 2) ((ν + 2) / 2) (3 / 2) (z ^ 2) := by
  sorry

/-- The ordinary complex derivative at zero, including all exceptional Gamma parameters.
Temme (8.17), synopsis TEM-08-03. -/
theorem deriv_legendreP_zero (ν : ℂ) :
    deriv (legendreP ν) 0 =
      -2 * (Real.sqrt π : ℂ) / (Gamma (-ν / 2) * Gamma ((ν + 1) / 2)) := by
  sorry

/-- The full logarithmic endpoint expansion for every nonintegral complex degree.
The whole slit disk `|1+z|<2`, `1+z∈slitPlane` is included.
Temme (8.18)–(8.23), synopsis TEM-08-03. -/
theorem hasSum_legendreP_logarithmic_endpoint {ν z : ℂ}
    (hν : ∀ k : ℤ, ν ≠ k) (hz : ‖1 + z‖ < 2) (hcut : 1 + z ∈ slitPlane) :
    HasSum (fun n : ℕ =>
      (Gamma (-ν) * Gamma (ν + 1))⁻¹ * pochhammer (-ν) n * pochhammer (ν + 1) n /
        (n.factorial : ℂ) ^ 2 *
          (2 * digamma (n + 1) - digamma ((n : ℂ) - ν) - digamma (n + ν + 1) -
            log ((1 + z) / 2)) * ((1 + z) / 2) ^ n) (legendreP ν z) := by
  sorry

end DLMF.Legendre
