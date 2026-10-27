/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Series

/-!
# Generating functions: the ultraspherical example (DLMF §1.10(xi))

DLMF 1.10.28–1.10.29 illustrate generating functions with the ultraspherical (Gegenbauer)
polynomials `C_n^{(λ)}(x)` (`DLMF.OrthogonalPolynomials.ultrasphPoly`). The generating function
1.10.28 is DLMF 18.12.4 (`DLMF.OrthogonalPolynomials.ultrasphPoly_generating_function`); the
`x`-derivative 1.10.29 is proved here from 18.12.4 and the derivative formula 18.9.19
(`DLMF.OrthogonalPolynomials.ultrasphPoly_derivative`). The domain is that of the
Chapter 18 statements: real `x ∈ [-1, 1]`, `ℜλ > -½`, `|z| < 1`, principal powers.
-/

@[expose] public noncomputable section

open Complex Filter
open DLMF.OrthogonalPolynomials

namespace DLMF.AlgebraicAnalytic

/-- DLMF 1.10.28: `(1 - 2xz + z²)^{-λ} = ∑ C_n^{(λ)}(x) zⁿ`, `|z| < 1` (here `x ∈ [-1, 1]`,
`ℜλ > -½`); this is DLMF 18.12.4. -/
@[dlmf 1.10.E28]
theorem ultrasph_generatingFunction {lam : ℂ} (hlam : -1 / 2 < lam.re) {x : ℝ} (hx : |x| ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => ultrasphPoly lam n x * z ^ n) ((1 - 2 * x * z + z ^ 2) ^ (-lam)) :=
  ultrasphPoly_generating_function hlam hx hz

/-- DLMF 1.10.29: differentiating the generating function in `x`,
`∑ (d/dx) C_n^{(λ)}(x) zⁿ = 2λz(1 - 2xz + z²)^{-λ-1} = ∑ 2λ C_n^{(λ+1)}(x) z^{n+1}`
(`x ∈ [-1, 1]`, `ℜλ > -½`, `|z| < 1`). -/
@[dlmf 1.10.E29]
theorem ultrasph_generatingFunction_deriv {lam : ℂ} (hlam : -1 / 2 < lam.re) {x : ℝ}
    (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => deriv (ultrasphPoly lam n) x * z ^ n)
        (2 * lam * z * (1 - 2 * x * z + z ^ 2) ^ (-lam - 1)) ∧
      HasSum (fun n : ℕ => 2 * lam * ultrasphPoly (lam + 1) n x * z ^ (n + 1))
        (2 * lam * z * (1 - 2 * x * z + z ^ 2) ^ (-lam - 1)) := by
  have hlam1 : -1 / 2 < (lam + 1).re := by simp; linarith
  have h := (ultrasphPoly_generating_function hlam1 hx hz).mul_left (2 * lam * z)
  have h2 : HasSum (fun n : ℕ => 2 * lam * ultrasphPoly (lam + 1) n x * z ^ (n + 1))
      (2 * lam * z * (1 - 2 * x * z + z ^ 2) ^ (-lam - 1)) := by
    convert h using 1
    · funext n; ring
    · rw [neg_add']
  refine ⟨?_, h2⟩
  refine (hasSum_nat_add_iff' 1).mp ?_
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one]
  have h0 : deriv (ultrasphPoly lam 0) (x : ℂ) = 0 := by
    have : ultrasphPoly lam 0 = fun _ => 1 := funext fun y => ultrasphPoly_zero lam y
    rw [this, deriv_const]
  rw [h0, sub_zero]
  convert h2 using 1
  funext n
  rw [ultrasphPoly_derivative hlam]
