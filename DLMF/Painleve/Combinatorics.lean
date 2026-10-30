/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.Basic.Solutions
public import DLMF.Airy.Framework

/-!
# Combinatorics and orthogonal polynomials (DLMF §32.14, §32.15)

§32.14: the Baik–Deift–Johansson theorem: the length `ℓ_N(π)` of the longest increasing
subsequence of a uniformly random permutation, centred by `2√N` and scaled by `N^{1/6}`,
converges in distribution to the Tracy–Widom distribution `F(s)` of 32.14.2, built from the
Hastings–McLeod solution of `PII` with `α = 0` (32.14.3–32.14.4). The random-matrix
interpretation of `F` (Gaussian Unitary Ensemble, §32.14 second paragraph) is not formalized.

§32.15: for the weight `exp(-ξ⁴/4 - zξ²)` of 32.15.1 the squared recurrence coefficients
`u_n = a_n²` (`freudRecurrenceSq`, Hankel-determinant form) satisfy the discrete equation
32.15.3 and, as functions of `z`, `PIV` with `α = -n/2`, `β = -n²/2`. Both were checked
numerically (moments by quadrature, `n ≤ 3`, residuals below `10⁻³⁹`).

All statements are admitted.
-/

@[expose] public noncomputable section

open Set Filter Asymptotics
open scoped Topology Nat
open DLMF.Airy

namespace DLMF.Painleve

open Classical in
/-- DLMF 32.14.1, 32.14.3–32.14.4: there is a real solution `w` of `PII` with `α = 0` on `ℝ`
with `w(x) ~ Ai(x)` as `x → +∞` and `w(x) ~ √(-x/2)` as `x → -∞` (the Hastings–McLeod
solution) such that, for every real `s`,
`Prob((ℓ_N(π) - 2√N)/N^{1/6} ≤ s) → F(s)` as `N → ∞`, for `π` uniform on the permutations of
`N` letters and `F` the distribution function 32.14.2 (`tracyWidomF`). -/
@[dlmf 32.14.E1, dlmf 32.14.E3, dlmf 32.14.E4]
theorem longestIncreasing_tracyWidom :
    ∃ w : ℝ → ℝ, IsRealODE2SolutionOn (realPainleveIIRhs 0) w univ ∧
      (w ~[atTop] airyAiReal) ∧ (w ~[atBot] fun x => Real.sqrt (-x / 2)) ∧
      ∀ s : ℝ, Tendsto (fun N : ℕ =>
        ((Finset.univ.filter fun π : Equiv.Perm (Fin N) =>
          ((longestIncreasingLength π : ℝ) - 2 * Real.sqrt N) / (N : ℝ) ^ (1 / 6 : ℝ) ≤ s).card :
            ℝ) / (N ! : ℝ)) atTop (𝓝 (tracyWidomF w s)) := by
  sorry

/-- DLMF 32.15.3: the squared recurrence coefficients `u_n(z) = a_n(z)²` of the orthonormal
polynomials for the weight `exp(-ξ⁴/4 - zξ²)` satisfy the discrete Painlevé equation
`(u_{n+1} + u_n + u_{n-1})u_n = n - 2zu_n`, `n = 1, 2, …` (with `u_0 = 0`). -/
@[dlmf 32.15.E3]
theorem freudRecurrenceSq_discretePainleveI (z : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (freudRecurrenceSq z (n + 1) + freudRecurrenceSq z n + freudRecurrenceSq z (n - 1)) *
      freudRecurrenceSq z n = n - 2 * z * freudRecurrenceSq z n := by
  sorry

/-- §32.15: for `n = 1, 2, …` the squared recurrence coefficient `u_n(z)` is positive and, as a
function of real `z`, satisfies `PIV` with `α = -n/2` and `β = -n²/2`. -/
@[dlmf 32.15]
theorem freudRecurrenceSq_painleveIV {n : ℕ} (hn : 1 ≤ n) :
    (∀ z, 0 < freudRecurrenceSq z n) ∧
      IsRealODE2SolutionOn (realPainleveIVRhs (-(n : ℝ) / 2) (-(n : ℝ) ^ 2 / 2))
        (fun z => freudRecurrenceSq z n) univ := by
  sorry

end DLMF.Painleve
