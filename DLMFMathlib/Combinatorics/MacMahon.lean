/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# MacMahon's master theorem

The determinant coefficient identity used in Andrews, Askey and Roy, *Special Functions*,
§7.2 (synopsis AAR-7.2.1–7.2.7). The formula is formal and has no analytic assumptions.
-/

@[expose] public section

namespace MvPowerSeries

/-- The coefficient of a reciprocal determinant is the corresponding diagonal coefficient
of a product of linear forms. Andrews–Askey–Roy, *Special Functions*, §7.2, pp. 369–370
(synopsis AAR-7.2.1–7.2.7). -/
theorem coeff_det_inv_eq_coeff_prod_linear_forms {ι K : Type*} [Fintype ι]
    [DecidableEq ι] [Field K] [CharZero K] (A : Matrix ι ι K) (n : ι →₀ ℕ) :
    coeff n ((Matrix.det (fun i j : ι =>
      ((if i = j then 1 else 0) - X i * C (A i j) : MvPowerSeries ι K)))⁻¹) =
      (∏ i : ι,
        (∑ j : ι, MvPolynomial.C (A i j) * MvPolynomial.X j) ^ n i).coeff n := by
  sorry

end MvPowerSeries
