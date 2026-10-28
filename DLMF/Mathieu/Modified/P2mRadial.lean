/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Mathieu.Modified.P2mRadial.SeriesEquation
public import DLMF.Mathieu.Modified.P2mRadial.IntegerCrossProducts

/-!
# The cross-product series of the modified Mathieu functions (proof of DLMF 28.24.1)

* `p2m_floquet_coeff_rec`: integration by parts gives the recurrence 28.14.4 for the exponential
  Fourier coefficients over `[0, π]` of a Floquet solution of Mathieu's equation;
* `p2m_mathieuMeInt_floquet`: `me_k(·, q)` (integer `k`, real `q`) is a Floquet solution with
  multiplier `(-1)^k`;
* `p2m_coeff_facts`: for admissible `(ν, h)` the coefficients `c^ν_{2m}(h²)` solve 28.14.4 with
  `a = λ_ν(h²)` and are bounded;
* `p2m_hasSum_modMathieuTerm`: DLMF 28.24.1, from the abstract theorem `p2m_cross_series`;
* derivatives of the continued Bessel functions in `z` (all orders, `Y` at integer orders by
  uniform limits in the order), locally uniform bounds for the shifted cross-product series
  `p2m_F` (`p2m_fam_locally_uniform`, giving §28.24's locally uniform convergence) and their
  termwise derivatives (`p2m_hasDerivAt_F`);
* `p2m_isModMathieuSolution_modMathieuM`: `M^{(j)}_ν` solves 28.20.1 (`p2m_F_ode`: the second
  derivative is reduced termwise with the Bessel recurrences and summed with 28.14.4);
* the integer-order expansions 28.24.2–28.24.5: the coefficients `c^{±N}_{2k}` as cosine and sine
  integrals of `ce_N`, `se_N` (`p2m_mathieuMeCoeff_ce`, `p2m_mathieuMeCoeff_se`), the parity
  `𝒞_{-k} = (-1)^k 𝒞_k` of the continued cylinder functions, and folding of 28.24.1 over `ℤ`.
-/
