/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Transforms.Basic
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Summability methods (DLMF §1.15): definitions

DLMF §1.15 defines summation methods for series and integrals, the Poisson and Fejér kernels
of Fourier series and Fourier integrals, the Abel and Cesàro means, and the Riemann–Liouville
fractional integrals and derivatives.

* Series (§1.15(i)): `seriesPartialSum` (1.15.1), the predicates `HasAbelSum` (1.15.2–1.15.3),
  `HasCesaroSum` (1.15.4–1.15.5), `HasCesaroSumOfOrder` (1.15.6–1.15.7) and `HasBorelSum`
  (1.15.8–1.15.9). The Abel and Borel predicates include the convergence of the power series
  for `0 < x < 1` (respectively of the exponential series for `t ≥ 0`), which DLMF leaves
  implicit; without it Lean's `tsum` would assign the junk value `0`.
* Fourier series (§1.15(iii)): the Poisson kernel `abelPoissonKernel` (1.15.12), the Fejér kernel
  `fejerKernel` (1.15.15), the Fourier coefficients `F(n)` (1.15.19) are Mathlib's
  `fourierCoeffOn Real.two_pi_pos f n` (bridge `fourierCoeffOn_two_pi_eq`), the Abel mean
  `abelMean` (1.15.18), the partial sums `fourierPartialSum` (1.15.22), the Cesàro means
  `fourierCesaroMean` (1.15.21) and the analytic extension `fourierAnalyticExtension` (1.15.27).
* Integrals (§1.15(iv)–(v)): `HasAbelIntegral` (1.15.29–1.15.30), `HasCesaroIntegral`
  (1.15.31–1.15.32), the half-plane Poisson kernel `halfPlanePoissonKernel` (1.15.33), the Abel
  mean of a Fourier integral `fourierAbelMean` (1.15.36), the Cauchy integral
  `poissonCauchyIntegral` (1.15.39), the Fejér kernel on the line `fejerKernelLine` (1.15.41)
  and the Cesàro mean of a Fourier integral `fourierCesaroMeanIntegral` (1.15.44).
* Fractional calculus (§1.15(vi)–(vii)): `fractionalIntegral` (1.15.47), its variants with
  other limits `riemannLiouvilleIntegralFrom`, `riemannLiouvilleIntegralUpper` and
  `weylFractionalIntegral` (§1.15(vi)), and `fractionalDerivative` (1.15.51) with
  `n = ⌊ℜα⌋ + 1`.

The kernels are stated with DLMF's normalizations: the circle kernels have mean `1` over
`[0, 2π]`, the half-plane kernel has `(1/2π) ∫ P = 1`, the Fejér kernel on the line has integral
`1`. At `θ ∈ 2πℤ` the quotient formula 1.15.15 is `0/0`; Lean's `fejerKernel n θ` is `0` there,
not the limit value `n + 1` (a null set, irrelevant for the integrals of §1.15).
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter Topology Finset
open scoped Nat

namespace DLMF.AlgebraicAnalytic

/-! ### Summability of series (§1.15(i)) -/

/-- DLMF 1.15.1: the partial sums `s_n = ∑_{k=0}^{n} a_k`. -/
@[dlmf 1.15.E1]
def seriesPartialSum (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ range (n + 1), a k

/-- DLMF 1.15.2–1.15.3: `∑ a_n = s (A)`, Abel summability: `∑ a_n x^n` converges for
`0 < x < 1` and tends to `s` as `x → 1⁻`. -/
@[dlmf 1.15.E2, dlmf 1.15.E3]
def HasAbelSum (a : ℕ → ℂ) (s : ℂ) : Prop :=
  (∀ x ∈ Ioo (0 : ℝ) 1, Summable fun n => a n * (x : ℂ) ^ n) ∧
    Tendsto (fun x : ℝ => ∑' n, a n * (x : ℂ) ^ n) (𝓝[<] 1) (𝓝 s)

/-- The Cesàro (C,1) means `(s_0 + ⋯ + s_n)/(n + 1)` of 1.15.5. -/
def cesaroMean (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (∑ m ∈ range (n + 1), seriesPartialSum a m) / (n + 1)

/-- DLMF 1.15.4–1.15.5: `∑ a_n = s (C,1)`, Cesàro summability. -/
@[dlmf 1.15.E4, dlmf 1.15.E5]
def HasCesaroSum (a : ℕ → ℂ) (s : ℂ) : Prop :=
  Tendsto (cesaroMean a) atTop (𝓝 s)

/-- The general Cesàro means `(n!/(α+1)_n) ∑_{k=0}^{n} ((α+1)_k/k!) a_{n-k}` of 1.15.7. -/
def cesaroMeanOfOrder (α : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (((n ! : ℝ) / (ascPochhammer ℝ n).eval (α + 1) : ℝ) : ℂ) *
    ∑ k ∈ range (n + 1), ((((ascPochhammer ℝ k).eval (α + 1) / k ! : ℝ)) : ℂ) * a (n - k)

/-- The Cesàro mean of order zero is the ordinary partial sum. -/
@[simp] theorem cesaroMeanOfOrder_zero (a : ℕ → ℂ) (n : ℕ) :
    cesaroMeanOfOrder 0 a n = seriesPartialSum a n := by
  simp only [cesaroMeanOfOrder, zero_add, ascPochhammer_eval_one]
  simp only [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _), ne_eq, not_false_eq_true,
    div_self, Complex.ofReal_one, one_mul]
  simpa only [seriesPartialSum, Nat.add_sub_cancel] using
    (Finset.sum_range_reflect (f := a) (n + 1))

/-- DLMF 1.15.6–1.15.7: `∑ a_n = s (C,α)`, general Cesàro summability (DLMF: `α > -1`; the
predicate is defined for every real `α`; regularity requires `0 ≤ α`). -/
@[dlmf 1.15.E6, dlmf 1.15.E7]
def HasCesaroSumOfOrder (α : ℝ) (a : ℕ → ℂ) (s : ℂ) : Prop :=
  Tendsto (cesaroMeanOfOrder α a) atTop (𝓝 s)

/-- DLMF 1.15.8–1.15.9: `∑ a_n = s (B)`, Borel summability: `∑ s_n tⁿ/n!` converges for
`t ≥ 0` and `e^{-t} ∑ s_n tⁿ/n! → s` as `t → ∞`. -/
@[dlmf 1.15.E8, dlmf 1.15.E9]
def HasBorelSum (a : ℕ → ℂ) (s : ℂ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → Summable fun n => seriesPartialSum a n * (t : ℂ) ^ n / (n ! : ℂ)) ∧
    Tendsto (fun t : ℝ => (Real.exp (-t) : ℂ) * ∑' n, seriesPartialSum a n * (t : ℂ) ^ n /
      (n ! : ℂ)) atTop (𝓝 s)

/-! ### Summability of Fourier series (§1.15(iii)) -/

/-- DLMF 1.15.12: the Poisson kernel `P(r, θ) = (1 - r²)/(1 - 2r cos θ + r²)`, `0 ≤ r < 1`. -/
@[dlmf 1.15.E12]
def abelPoissonKernel (r θ : ℝ) : ℝ :=
  (1 - r ^ 2) / (1 - 2 * r * Real.cos θ + r ^ 2)

/-- DLMF 1.15.15: the Fejér kernel `K_n(θ) = (1/(n+1)) (sin(½(n+1)θ)/sin(½θ))²`. At
`θ ∈ 2πℤ` the Lean value is `0` (division by zero), not the limit `n + 1`. -/
@[dlmf 1.15.E15]
def fejerKernel (n : ℕ) (θ : ℝ) : ℝ :=
  (1 / (n + 1 : ℝ)) * (Real.sin ((n + 1) * θ / 2) / Real.sin (θ / 2)) ^ 2

/-- DLMF 1.15.19: the Fourier coefficients `F(n) = (1/2π) ∫₀^{2π} f(t) e^{-int} dt` are
Mathlib's `fourierCoeffOn Real.two_pi_pos f n`. -/
@[dlmf 1.15.E19]
theorem fourierCoeffOn_two_pi_eq (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn (E := ℂ) Real.two_pi_pos f n =
      ((2 * Real.pi : ℝ)⁻¹ : ℂ) * ∫ t in (0 : ℝ)..2 * Real.pi, f t * cexp (-(n * t * I)) := by
  rw [fourierCoeffOn_eq_integral, sub_zero, Complex.real_smul]
  congr 1
  · push_cast; ring
  apply intervalIntegral.integral_congr
  intro t _
  simp only [smul_eq_mul]
  rw [fourier_coe_apply, mul_comm]
  congr 2
  have : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  push_cast
  field_simp

/-- DLMF 1.15.18: the Abel means `A(r, θ) = ∑_{n ∈ ℤ} r^{|n|} F(n) e^{inθ}` of the Fourier series
of `f`, with `F(n)` the Fourier coefficients 1.15.19 on `[0, 2π]`. -/
@[dlmf 1.15.E18]
def abelMean (f : ℝ → ℂ) (r θ : ℝ) : ℂ :=
  ∑' n : ℤ, ((r ^ n.natAbs : ℝ) : ℂ) * fourierCoeffOn Real.two_pi_pos f n * cexp (n * θ * I)

/-- DLMF 1.15.22: the symmetric partial sums `s_n(θ) = ∑_{k=-n}^{n} F(k) e^{ikθ}`. -/
@[dlmf 1.15.E22]
def fourierPartialSum (f : ℝ → ℂ) (n : ℕ) (θ : ℝ) : ℂ :=
  ∑ k ∈ Icc (-(n : ℤ)) n, fourierCoeffOn Real.two_pi_pos f k * cexp (k * θ * I)

/-- DLMF 1.15.21: the Cesàro (C,1) means `σ_n(θ) = (s_0(θ) + ⋯ + s_n(θ))/(n + 1)`. -/
@[dlmf 1.15.E21]
def fourierCesaroMean (f : ℝ → ℂ) (n : ℕ) (θ : ℝ) : ℂ :=
  (∑ m ∈ range (n + 1), fourierPartialSum f m θ) / (n + 1)

/-- DLMF 1.15.27: `G(z) = F(0) + 2 ∑_{n ≥ 1} F(n) zⁿ`, the analytic function in the unit disc
whose boundary series is 1.15.26. -/
@[dlmf 1.15.E27]
def fourierAnalyticExtension (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  fourierCoeffOn Real.two_pi_pos f 0 +
    2 * ∑' n : ℕ, fourierCoeffOn Real.two_pi_pos f (n + 1 : ℕ) * z ^ (n + 1)

/-! ### Summability of integrals (§1.15(iv)) -/

/-- DLMF 1.15.29–1.15.30: `∫ f = L (A)`: `e^{-ε|t|} f(t)` is integrable for every `ε > 0` and
`∫ e^{-ε|t|} f(t) dt → L` as `ε → 0⁺`. -/
@[dlmf 1.15.E29, dlmf 1.15.E30]
def HasAbelIntegral (f : ℝ → ℂ) (L : ℂ) : Prop :=
  (∀ ε : ℝ, 0 < ε → Integrable fun t => (Real.exp (-ε * |t|) : ℂ) * f t) ∧
    Tendsto (fun ε : ℝ => ∫ t, (Real.exp (-ε * |t|) : ℂ) * f t) (𝓝[>] 0) (𝓝 L)

/-- DLMF 1.15.31–1.15.32: `∫ f = L (C,1)`: `∫_{-R}^{R} (1 - |t|/R) f(t) dt → L` as `R → ∞`. -/
@[dlmf 1.15.E31, dlmf 1.15.E32]
def HasCesaroIntegral (f : ℝ → ℂ) (L : ℂ) : Prop :=
  Tendsto (fun R : ℝ => ∫ t in -R..R, ((1 - |t| / R : ℝ) : ℂ) * f t) atTop (𝓝 L)

/-! ### Summability of Fourier integrals (§1.15(v)) -/

/-- DLMF 1.15.33: the Poisson kernel of the upper half-plane `P(x, y) = 2y/(x² + y²)`, `y > 0`. -/
@[dlmf 1.15.E33]
def halfPlanePoissonKernel (x y : ℝ) : ℝ :=
  2 * y / (x ^ 2 + y ^ 2)

/-- DLMF 1.15.36: the Abel mean of the Fourier integral,
`h(x, y) = (2π)^{-1/2} ∫ e^{-y|t|} e^{-ixt} F(t) dt` with `F = 𝓕(f)` (1.14.1). -/
@[dlmf 1.15.E36]
def fourierAbelMean (f : ℝ → ℂ) (x y : ℝ) : ℂ :=
  ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) *
    ∫ t : ℝ, (Real.exp (-y * |t|) : ℂ) * cexp (-(I * x * t)) * fourierTransform f t

/-- DLMF 1.15.39: `Φ(x + iy) = (i/π) ∫ f(t)/((x - t) + iy) dt`, `y > 0`. -/
@[dlmf 1.15.E39]
def poissonCauchyIntegral (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  (I / Real.pi) * ∫ t : ℝ, f t / ((z.re - t) + I * z.im)

/-- DLMF 1.15.41: the Fejér kernel on the line `K_R(s) = (1/(πR)) (1 - cos(Rs))/s²`. -/
@[dlmf 1.15.E41]
def fejerKernelLine (R s : ℝ) : ℝ :=
  1 / (Real.pi * R) * ((1 - Real.cos (R * s)) / s ^ 2)

/-- DLMF 1.15.44: the Cesàro mean of the Fourier integral,
`σ_R(θ) = (2π)^{-1/2} ∫_{-R}^{R} (1 - |t|/R) e^{-iθt} F(t) dt` with `F = 𝓕(f)`. -/
@[dlmf 1.15.E44]
def fourierCesaroMeanIntegral (f : ℝ → ℂ) (R θ : ℝ) : ℂ :=
  ((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) *
    ∫ t in -R..R, ((1 - |t| / R : ℝ) : ℂ) * cexp (-(I * θ * t)) * fourierTransform f t

/-! ### Fractional integrals and derivatives (§1.15(vi)–(vii)) -/

/-- DLMF 1.15.47: the Riemann–Liouville fractional integral
`I^α f(x) = (1/Γ(α)) ∫₀^x (x - t)^{α-1} f(t) dt`, for `ℜα > 0` and `x ≥ 0` (principal power of
the nonnegative real `x - t`). -/
@[dlmf 1.15.E47]
def fractionalIntegral (α : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Complex.Gamma α)⁻¹ * ∫ t in (0 : ℝ)..x, ((x - t : ℝ) : ℂ) ^ (α - 1) * f t

/-- DLMF §1.15(vi), after 1.15.50: the fractional integral with lower limit `a` in place of `0`,
`(1/Γ(α)) ∫ₐ^x (x - t)^{α-1} f(t) dt` for `a ≤ x`. -/
@[dlmf 1.15.vi]
def riemannLiouvilleIntegralFrom (a : ℝ) (α : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Complex.Gamma α)⁻¹ * ∫ t in a..x, ((x - t : ℝ) : ℂ) ^ (α - 1) * f t

/-- DLMF §1.15(vi), after 1.15.50: the right-sided fractional integral with limits `x` and `a`,
`(1/Γ(α)) ∫ₓ^a (t - x)^{α-1} f(t) dt` for `x ≤ a`. -/
@[dlmf 1.15.vi]
def riemannLiouvilleIntegralUpper (a : ℝ) (α : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Complex.Gamma α)⁻¹ * ∫ t in x..a, ((t - x : ℝ) : ℂ) ^ (α - 1) * f t

/-- DLMF §1.15(vi), after 1.15.50: the right-sided fractional integral with `a = ∞` (the Weyl
fractional integral), `(1/Γ(α)) ∫ₓ^∞ (t - x)^{α-1} f(t) dt`, as a Lebesgue integral over
`(x, ∞)`. -/
@[dlmf 1.15.vi]
def weylFractionalIntegral (α : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Complex.Gamma α)⁻¹ * ∫ t in Ioi x, ((t - x : ℝ) : ℂ) ^ (α - 1) * f t

/-- The order `n = ⌊ℜα⌋ + 1` used in `fractionalDerivative`; it satisfies `ℜα < n`. -/
def fractionalDerivativeOrder (α : ℂ) : ℕ :=
  ⌊α.re⌋₊ + 1

/-- DLMF 1.15.51: the fractional derivative `D^α f(x) = (dⁿ/dxⁿ) I^{n-α} f(x)` for
`0 < ℜα < n`, with the choice `n = ⌊ℜα⌋ + 1`; independence of `n` is
`fractionalDerivative_eq_iteratedDeriv`. -/
@[dlmf 1.15.E51]
def fractionalDerivative (α : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  iteratedDeriv (fractionalDerivativeOrder α)
    (fractionalIntegral ((fractionalDerivativeOrder α : ℂ) - α) f) x

end DLMF.AlgebraicAnalytic
