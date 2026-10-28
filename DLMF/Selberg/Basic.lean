/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Selberg.Basic.IntegrationByParts
public import DLMF.Selberg.Basic.DimensionAndParameters
public import DLMF.Selberg.Basic.ContinuationAndAomoto

/-!
# The Selberg and Aomoto integrals (AAR §§8.1–8.4)

Mathlib has the Selberg *sieve*, not Selberg's integral. The `n = 1` case is the Beta
integral already in Mathlib (`Complex.betaIntegral`).

## Proof of Selberg's integral

We follow Aomoto's proof (AAR §8.1), completed by Carlson's theorem and a recursion in the
dimension, and extend to the full domain of convergence by analytic continuation.

1. *Integration by parts* in one coordinate (`integral_cube_ibp`), with the Vandermonde factor
   handled off the diagonal, gives **Aomoto's recurrence** (`aomoto_step`) for `Re c ≥ 1/2`,
   and hence the shift `S(a+1) = ∏ⱼ (a+(n-1-j)c)/(a+b+(2n-2-j)c) · S(a)`
   (`selbergInt_add_one`).
2. `S/R` is therefore `1`-periodic in `a`; it is holomorphic and of polynomial growth on
   vertical strips, so it is constant by **Carlson's theorem** (`selbergRatio_eq_one_left`).
   By the symmetry `a ↔ b` it depends on `c` only.
3. A boundary integration by parts gives the **dimension recursion**
   `(a + n c) S_{n+1}(a, 1, c) = S_n(a, 1 + 2c, c)` (`selbergInt_succ_one`), which the
   right-hand side also satisfies, so the constant is `1` (`selbergInt_eq_of_half_le`).
4. The identity extends to `Re c > 0` by analytic continuation in `c`. Integrability on the
   full domain `Re c > -min(1/n, Re a/(n-1), Re b/(n-1))` follows from a **Landau-type
   theorem** for Mellin transforms of positive measures
   (`integrable_mul_rpow_of_analytic`), after which the identity theorem gives
   `selberg_integral`.
-/
