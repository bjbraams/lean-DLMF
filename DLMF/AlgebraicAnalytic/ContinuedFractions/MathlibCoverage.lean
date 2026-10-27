/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Core.Upstream
public import Mathlib.Algebra.ContinuedFractions.ConvergentsEquiv
public import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
public import Mathlib.Algebra.ContinuedFractions.Determinant
public import Mathlib.Algebra.ContinuedFractions.Euler

/-!
# DLMF §1.12 results already in Mathlib

Checked pointers from DLMF §1.12 (continued fractions) to Mathlib's `GenContFract` API. Mathlib
indexes the pairs `(a_n, b_n)` from `0`, so its `a₀, b₀` are DLMF's `a₁, b₁` and its head `h`
is DLMF's `b₀`; `GenContFract.nums n`, `GenContFract.dens n` are DLMF's `A_n`, `B_n`. The
DLMF-indexed restatements are in `DLMF.AlgebraicAnalytic.ContinuedFractions.Convergents`.
-/

/- §1.12(ii): convergents. -/
dlmf_upstream 1.12.E4 GenContFract.convs_eq_convs'
  "special case: A_n/B_n equals the nested fraction when all a_k, b_k are positive (ordered
  field); the general nonvanishing-tail form is the local contFrac_convs'_eq_convs"
dlmf_upstream 1.12.E5 GenContFract.conts_recurrence
  "exact: A_n = b_n A_{n-1} + a_n A_{n-2}, B_n = b_n B_{n-1} + a_n B_{n-2}, Mathlib indexing"
dlmf_upstream 1.12.E6 GenContFract.zeroth_contAux_eq_one_zero
  "exact: (A_{-1}, B_{-1}) = (1, 0)"
dlmf_upstream 1.12.E6 GenContFract.first_contAux_eq_h_one
  "exact: (A_0, B_0) = (b_0, 1)"
dlmf_upstream 1.12.E7 GenContFract.determinant
  "exact: A_n B_{n+1} - B_n A_{n+1} = ∏ (-a_k), the negative of DLMF's
  A_n B_{n-1} - B_n A_{n-1} = (-1)^{n-1} ∏ a_k after an index shift"
dlmf_upstream 1.12.E9 GenContFract.convs_eq_sum_of_forall_le
  "exact: C_n = b_0 + ∑ (-1)^k a_1⋯a_{k+1}/(B_k B_{k+1}) when B_0, …, B_n ≠ 0"

/- §1.12(ii): Euler's series continued fraction. -/
dlmf_upstream 1.12.E18 GenContFract.convs_euler
  "different convention: the Euler fraction h + ρ₀/(1 - ρ₁/(1 + ρ₁ - ⋯)) has convergents
  h + ρ₀ + ρ₀ρ₁ + ⋯, i.e. the series with term ratios ρ_k; DLMF's form (1.12.18) is the local
  contFrac_euler_series"
