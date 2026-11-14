/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.Classical
public import DLMF.Bessel.Basic.RegularizedSeries
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Jacobi zero angles converge to Bessel zeros

Andrews, Askey and Roy, *Special Functions*, Theorem 4.14.1, pp. 225–226
(synopsis AAR-4.14.1–4.16.4). Counts below a zero encode its increasing index,
so no competing global choice of a zero sequence is introduced.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology Real
namespace DLMF.OrthogonalPolynomials

/-- The kth Jacobi zero angle, multiplied by its degree, converges to the kth positive
Bessel zero. Andrews–Askey–Roy, Theorem 4.14.1; index zero denotes the first positive zero. -/
theorem tendsto_degree_mul_jacobi_zero_angle {alpha beta : ℝ}
    (halpha : -1 < alpha) (hbeta : -1 < beta) (k : ℕ) {theta : ℕ → ℝ}
    (htheta : ∀ n, k < n → theta n ∈ Ioo 0 Real.pi ∧
      jacobiPolynomialP alpha beta n (Real.cos (theta n)) = 0 ∧
      {t : ℝ | t ∈ Ioo 0 (theta n) ∧ jacobiPolynomialP alpha beta n (Real.cos t) = 0}.ncard = k)
    {j : ℝ} (hjpositive : 0 < j) (hjzero : Complex.besselJ alpha j = 0)
    (hjindex : {t : ℝ | t ∈ Ioo 0 j ∧ Complex.besselJ alpha t = 0}.ncard = k) :
    Tendsto (fun n : ℕ => (n : ℝ) * theta n) atTop (𝓝 j) := by
  sorry

end DLMF.OrthogonalPolynomials
