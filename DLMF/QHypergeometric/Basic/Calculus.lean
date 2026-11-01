/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic

/-!
# The extended `q`-derivative and the bilateral Jackson integral (DLMF §17.2(iv)–(v))

This file defines Jackson's `q`-derivative with the value at the origin prescribed by DLMF, its
iterates, and the bilateral Jackson integral, and proves the product rule and the limit
`q → 1`.

## Main definitions

* `qDerivExtended`: the `q`-derivative, equal to `DLMF.QSeries.qDeriv` at nonzero arguments
  and to the ordinary derivative at the origin (DLMF 17.2.41).
* `qDerivIterate`: its `n`-fold iterate.
* `jacksonBilateral`: the bilateral Jackson integral `∫₀^∞ f(t) d_q t` (DLMF 17.2.48).

## Main results

* `qDerivExtended_of_ne_zero`, `qDerivExtended_zero`: unfolding at and away from the origin.
* `qDeriv_product_extended`: the `q`-product rule (DLMF 17.2.43).
* `qDeriv_limit`: the `q`-derivative tends to the derivative as `q → 1`.

## Implementation notes

The bilateral Jackson integral is a totalized `tsum`, used only together with convergence
hypotheses. The finite-difference form, the Leibniz rule and the limits of iterates are in
`DLMF.QHypergeometric.Calculus.QDerivative`.
-/

@[expose] public noncomputable section
open Complex Filter
open scoped Topology
open DLMF.QSeries
namespace DLMF.QHypergeometric

/-- Jackson's q-derivative with the derivative value at the origin specified in DLMF. -/
@[dlmf 17.2.E41]
def qDerivExtended (q : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z=0 then deriv f 0 else DLMF.QSeries.qDeriv q f z

/-- The n-fold q-derivative, including its DLMF value at the origin. -/
def qDerivIterate (n : ℕ) (q : ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  (fun g : ℂ → ℂ => qDerivExtended q g)^[n] f

/-- Away from the origin the existing q-derivative is reused exactly. -/
theorem qDerivExtended_of_ne_zero {z : ℂ} (hz : z≠0) (q : ℂ) (f : ℂ → ℂ) :
    qDerivExtended q f z=DLMF.QSeries.qDeriv q f z := by simp [qDerivExtended,hz]

/-- The value at the origin is the ordinary derivative, rather than division by zero. -/
theorem qDerivExtended_zero (q : ℂ) (f : ℂ → ℂ) : qDerivExtended q f 0=deriv f 0 := by
  simp [qDerivExtended]

/-- The q-product rule `D_q(fg)(z) = g(z) D_q f(z) + f(zq) D_q g(z)` (DLMF 17.2.E43). -/
@[dlmf 17.2.E43]
theorem qDeriv_product_extended (q z : ℂ) (f g : ℂ → ℂ)
    (hf : z=0 → DifferentiableAt ℂ f 0) (hg : z=0 → DifferentiableAt ℂ g 0) :
    qDerivExtended q (fun w => f w*g w) z=
      g z*qDerivExtended q f z+f (z*q)*qDerivExtended q g z := by
  by_cases hz : z=0
  · subst z
    simpa [qDerivExtended,mul_comm] using deriv_fun_mul (hf rfl) (hg rfl)
  · simpa [qDerivExtended,hz,mul_comm] using qDeriv_mul q f g z

/-- As `q → 1`, the q-derivative of a differentiable function tends to its derivative. -/
theorem qDeriv_limit {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    Tendsto (fun q : ℂ => qDerivExtended q f z) (𝓝[≠] 1) (𝓝 (deriv f z)) := by
  by_cases hz : z=0
  · subst z
    simp [qDerivExtended]
  · simpa [qDerivExtended,hz] using DLMF.QSeries.tendsto_qDeriv hf.hasDerivAt hz

/-- The bilateral Jackson integral, used only together with convergence hypotheses. -/
@[dlmf 17.2.E48]
def jacksonBilateral (q : ℂ) (f : ℂ → ℂ) : ℂ :=
  (1-q)*∑' n : ℤ, q^n*f (q^n)

end DLMF.QHypergeometric
