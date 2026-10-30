/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Sums.Basic
public import DLMF.GeneralizedHypergeometric.ParameterAndSeriesProperties
public import DLMF.OrthogonalPolynomials.Series

/-!
# Entire functions and Darboux's method (DLMF §2.10(iii)–(iv))

* §2.10(iii): the example `₀F₂(-; 1, 1; x)` (2.10.19–2.10.24). The series 2.10.19 is matched with
  the project's generalized hypergeometric coefficients `genCoeff` (16.2.1, proved); the
  partial sums are written as contour integrals over the contour `𝒞` of Figure 2.10.1
  (`contourIntegralC`, 2.10.20, 2.10.22); the cotangent identities 2.10.21 are proved.
* §2.10(iv): Laurent coefficients (2.10.25–2.10.26) and Darboux's method (2.10.27–2.10.32),
  with the Legendre example 2.10.33–2.10.36. The generating function 2.10.33 is the project's
  `DLMF.OrthogonalPolynomials.legendre_generating_function` (18.12.11) at `x = cos α`.

Erratum: in the Legendre example DLMF takes `α ∈ (0, 2π)`, but 2.10.34–2.10.36 need
`α ∈ (0, π)`: for `π < α < 2π`, `sin α < 0`, so `(2 sin α)^{-1/2}` and the right side of 2.10.36
are not real, while `P_n(cos α)` is real; with `α' = 2π - α` the correct phase is
`nα' + α'/2 - π/4`, not `nα + α/2 - π/4`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology Real Nat

namespace DLMF.AsymptoticApproximations

/-! ### §2.10(iii) The example `₀F₂(-; 1, 1; x)` -/

/-- DLMF 2.10.19 (coefficients): the coefficients of `₀F₂(-; 1, 1; x)` in the normalization
16.2.1 are `1/(j!)³`. -/
@[dlmf 2.10.E19]
theorem genCoeff_zero_one_one (j : ℕ) :
    DLMF.Hypergeometric.genCoeff 0 {1, 1} j = 1 / (j.factorial : ℂ) ^ 3 := by
  simp only [DLMF.Hypergeometric.genCoeff, DLMF.Hypergeometric.genPoch,
    Multiset.map_zero, Multiset.prod_zero, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton,
    DLMF.Hypergeometric.poch, ascPochhammer_eval_one]
  have : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  field_simp

/-- The series `∑ x^j/(j!)³` converges absolutely for every `x`. -/
lemma g2b_summable_0F2 (x : ℂ) : Summable fun j : ℕ => x ^ j / (j.factorial : ℂ) ^ 3 := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖x‖) fun j => ?_
  rw [norm_div, norm_pow, norm_pow, Complex.norm_natCast]
  have h1 : (1 : ℝ) ≤ j.factorial := by exact_mod_cast j.factorial_pos
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  calc (j.factorial : ℝ) = (j.factorial : ℝ) ^ 1 := (pow_one _).symm
    _ ≤ (j.factorial : ℝ) ^ 3 := pow_le_pow_right₀ h1 (by norm_num)

/-- DLMF 2.10.19: `₀F₂(-; 1, 1; x) = ∑_{j ≥ 0} x^j/(j!)³`, i.e. the project's generalized
hypergeometric series with upper parameters `()` and lower parameters `(1, 1)` converges to
`hypergeometric0F2OneOne x` for every complex `x`. -/
@[dlmf 2.10.E19]
theorem hypergeometric0F2OneOne_hasSum (x : ℂ) :
    HasSum (fun j : ℕ => DLMF.Hypergeometric.genCoeff 0 {1, 1} j * x ^ j)
      (hypergeometric0F2OneOne x) := by
  have h := (g2b_summable_0F2 x).hasSum
  refine h.congr_fun fun j => ?_
  rw [genCoeff_zero_one_one]
  ring

/-- DLMF 2.10.19 in the project's convergence predicate for generalized hypergeometric series. -/
@[dlmf 2.10.E19]
theorem genSeriesConvergesTo_0F2 (x : ℂ) :
    DLMF.Hypergeometric.genSeriesConvergesTo 0 {1, 1} x
      (hypergeometric0F2OneOne x) :=
  (hypergeometric0F2OneOne_hasSum x).tendsto_sum_nat

/-- DLMF 2.10.20: for `x > 0` and `n ≥ 1`,
`∑_{j=0}^{n-1} x^j/(j!)³ = (2i)⁻¹ ∫_𝒞 x^t/Γ(t+1)³ cot(πt) dt`, with `𝒞` the contour of
Figure 2.10.1 (`contourIntegralC`); the residue of `cot(πt)` at `t = j` is `1/π`. -/
@[dlmf 2.10.E20]
theorem sum_0F2_eq_contourIntegral {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range n, (x : ℂ) ^ j / (j.factorial : ℂ) ^ 3 =
      (2 * I)⁻¹ * contourIntegralC (fun t => g2b_0F2Integrand x t * Complex.cot (π * t)) n := by
  sorry

/-- DLMF 2.10.21: for `t ∉ ℤ`,
`cot(πt)/(2i) = -1/2 - 1/(e^{-2πit} - 1) = 1/2 + 1/(e^{2πit} - 1)`. -/
@[dlmf 2.10.E21]
theorem cot_div_two_I {t : ℂ} (ht : ∀ k : ℤ, t ≠ k) :
    Complex.cot (π * t) / (2 * I) = -(1 / 2) - 1 / (Complex.exp (-(2 * π * I * t)) - 1) ∧
      Complex.cot (π * t) / (2 * I) = 1 / 2 + 1 / (Complex.exp (2 * π * I * t) - 1) := by
  have hE : Complex.exp (2 * π * I * t) ≠ 1 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h
    apply ht k
    have hπ : (2 * π * I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : 2 * π * I * t = 2 * π * I * k := by rw [hk]; ring
    exact mul_left_cancel₀ hπ this
  have hE0 : Complex.exp (2 * π * I * t) ≠ 0 := Complex.exp_ne_zero _
  have h1 : Complex.exp (2 * π * I * t) - 1 ≠ 0 := sub_ne_zero.2 hE
  have h2 : 1 - Complex.exp (2 * π * I * t) ≠ 0 := sub_ne_zero.2 (Ne.symm hE)
  have hneg : Complex.exp (-(2 * π * I * t)) = (Complex.exp (2 * π * I * t))⁻¹ :=
    Complex.exp_neg _
  have h3 : (Complex.exp (2 * π * I * t))⁻¹ - 1 ≠ 0 := by
    rw [sub_ne_zero, Ne, inv_eq_one]; exact hE
  rw [Complex.cot_pi_eq_exp_ratio, hneg]
  constructor
  · field_simp
    rw [Complex.I_sq]
    ring
  · field_simp
    ring_nf
    rw [Complex.I_sq]
    ring

/-- DLMF 2.10.22: for `x > 0` and `n ≥ 1`,
`∑_{j=0}^{n-1} x^j/(j!)³ = ∫_{-1/2}^{n-1/2} x^t/Γ(t+1)³ dt - ∫_{𝒞₁} x^t/Γ(t+1)³ dt/(e^{-2πit}-1)
  + ∫_{𝒞₂} x^t/Γ(t+1)³ dt/(e^{2πit}-1)`, with `𝒞₁`, `𝒞₂` the upper and lower halves of `𝒞`. -/
@[dlmf 2.10.E22]
theorem sum_0F2_eq_real_integral_add {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range n, (x : ℂ) ^ j / (j.factorial : ℂ) ^ 3 =
      (∫ t in (-(1 / 2) : ℝ)..(n - 1 / 2), g2b_0F2Integrand x t) -
        contourIntegralC₁ (fun t => g2b_0F2Integrand x t / (Complex.exp (-(2 * π * I * t)) - 1))
          n +
        contourIntegralC₂ (fun t => g2b_0F2Integrand x t / (Complex.exp (2 * π * I * t) - 1))
          n := by
  sorry

/-- DLMF 2.10.23 (first equality): for `x > 0`,
`₀F₂(-; 1, 1; x) = ∫_{-1/2}^∞ x^t/Γ(t+1)³ dt + 2ℜ ∫_{-1/2}^{i∞} x^t/Γ(t+1)³ dt/(e^{-2πit}-1)`,
the path from `-1/2` to `i∞` being the quarter circle `|t| = 1/2` from `-1/2` to `i/2` followed
by the imaginary axis. The integrals converge absolutely. -/
@[dlmf 2.10.E23]
theorem hypergeometric0F2OneOne_eq_integrals {x : ℝ} (hx : 0 < x) :
    let F : ℂ → ℂ := fun t => g2b_0F2Integrand x t / (Complex.exp (-(2 * π * I * t)) - 1)
    hypergeometric0F2OneOne x =
      (∫ t in Ioi (-(1 / 2) : ℝ), g2b_0F2Integrand x t) +
        2 * ((g2b_semicirclePath F (1 / 2) π (π / 2) +
          ∫ y in Ioi (1 / 2 : ℝ), F (I * y) * I).re : ℂ) := by
  sorry

/-- DLMF 2.10.23 (second equality): `₀F₂(-; 1, 1; x) = ∫_0^∞ x^t/Γ(t+1)³ dt + O(1)` as
`x → +∞`. -/
@[dlmf 2.10.E23]
theorem hypergeometric0F2OneOne_sub_integral_isBigO :
    (fun x : ℝ => hypergeometric0F2OneOne x - ∫ t in Ioi (0 : ℝ), g2b_0F2Integrand x t)
      =O[atTop] fun _ => (1 : ℝ) := by
  sorry

/-- DLMF 2.10.24: `₀F₂(-; 1, 1; x) ∼ exp(3x^{1/3})/(2π 3^{1/2} x^{1/3})` as `x → +∞`. -/
@[dlmf 2.10.E24]
theorem hypergeometric0F2OneOne_isEquivalent :
    (fun x : ℝ => hypergeometric0F2OneOne x) ~[atTop]
      fun x : ℝ => ((Real.exp (3 * x ^ (1 / 3 : ℝ)) /
        (2 * π * Real.sqrt 3 * x ^ (1 / 3 : ℝ)) : ℝ) : ℂ) := by
  sorry

/-! ### §2.10(iv) Laurent coefficients and Darboux's method -/

/-- DLMF 2.10.25–2.10.26: if `f` is analytic on `0 < |z| < r`, then for `0 < ρ < r` the
coefficients `f_n = (2πi)⁻¹ ∮_{|z|=ρ} f(z) z^{-n-1} dz` do not depend on `ρ`, and
`f(z) = ∑_{n ∈ ℤ} f_n z^n` for `0 < |z| < r`. -/
@[dlmf 2.10.E25, dlmf 2.10.E26]
theorem laurent_expansion {f : ℂ → ℂ} {r : ℝ} (hf : DifferentiableOn ℂ f (g2b_punctured r))
    {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hρ' : 0 < ρ') (hρ'r : ρ' < r) :
    laurentCoeff f ρ = laurentCoeff f ρ' ∧
      ∀ z ∈ g2b_punctured r, HasSum (fun n : ℤ => laurentCoeff f ρ n * z ^ n) (f z) := by
  sorry

/-- DLMF 2.10.27–2.10.29 (Darboux's method, conditions (a)–(c)): let `f` and the comparison
function `g` be analytic on `0 < |z| < r` (`g_n` its Laurent coefficients, 2.10.27), and let
`f - g` extend to a function `h` continuous on `0 < |z| ≤ r`. Then for `0 < ρ < r`,
`f_n - g_n = (2π rⁿ)⁻¹ ∫_0^{2π} h(re^{iθ}) e^{-niθ} dθ` (2.10.28), and
`f_n = g_n + o(r^{-n})` as `n → ±∞` (2.10.29). -/
@[dlmf 2.10.E27, dlmf 2.10.E28, dlmf 2.10.E29, dlmf 2.10.iv]
theorem darboux {f g h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (g2b_punctured r)) (hg : DifferentiableOn ℂ g (g2b_punctured r))
    (hh : ContinuousOn h {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ r})
    (hfg : EqOn h (f - g) (g2b_punctured r)) {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) :
    (∀ n : ℤ, laurentCoeff f ρ n - laurentCoeff g ρ n =
      (2 * π * (r : ℂ) ^ n)⁻¹ *
        ∫ θ in (0 : ℝ)..2 * π, h (r * Complex.exp (θ * I)) * Complex.exp (-(n * θ * I))) ∧
    Tendsto (fun n : ℤ => (laurentCoeff f ρ n - laurentCoeff g ρ n) * (r : ℂ) ^ n) cofinite
      (𝓝 0) := by
  sorry

/-- DLMF 2.10.30 (Darboux's method with condition (b′)): the conclusion 2.10.29 holds when, on
`|z| = r`, `f - g` has finitely many singularities `z_j` with
`f(z) - g(z) = O((z - z_j)^{σ_j - 1})` as `z → z_j` (`σ_j > 0`), and extends continuously to
the rest of the closed annulus. -/
@[dlmf 2.10.E30, dlmf 2.10.iv]
theorem darboux_singular {f g h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (g2b_punctured r)) (hg : DifferentiableOn ℂ g (g2b_punctured r))
    {Z : Finset ℂ} (hZ : ∀ w ∈ Z, ‖w‖ = r)
    (hh : ContinuousOn h ({z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ r} \ Z))
    (hfg : EqOn h (f - g) (g2b_punctured r)) (σ : ℂ → ℝ) (hσ : ∀ w ∈ Z, 0 < σ w)
    (hsing : ∀ w ∈ Z, (f - g) =O[𝓝[g2b_punctured r] w] fun z => ‖z - w‖ ^ (σ w - 1))
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) :
    Tendsto (fun n : ℤ => (laurentCoeff f ρ n - laurentCoeff g ρ n) * (r : ℂ) ^ n) cofinite
      (𝓝 0) := by
  sorry

/-- DLMF 2.10.31: if in addition `θ ↦ h(re^{iθ})` (the boundary values of `f - g`) is `m` times
continuously differentiable, then `f_n = g_n + o(r^{-n} |n|^{-m})` as `n → ±∞`. -/
@[dlmf 2.10.E31]
theorem darboux_smooth {f g h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (g2b_punctured r)) (hg : DifferentiableOn ℂ g (g2b_punctured r))
    (hh : ContinuousOn h {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ r})
    (hfg : EqOn h (f - g) (g2b_punctured r)) {m : ℕ}
    (hm : ContDiff ℝ m fun θ : ℝ => h (r * Complex.exp (θ * I))) {ρ : ℝ} (hρ : 0 < ρ)
    (hρr : ρ < r) :
    Tendsto (fun n : ℤ => (laurentCoeff f ρ n - laurentCoeff g ρ n) * (r : ℂ) ^ n *
      ((|n| : ℤ) : ℂ) ^ m) cofinite (𝓝 0) := by
  sorry

/-- DLMF 2.10.32: 2.10.31 remains valid when the derivatives of `f - g` of orders `≤ m` extend
continuously to `|z| = r` except at finitely many points `z_j`, near which
`f^{(m)}(z) - g^{(m)}(z) = O((z - z_j)^{σ_j - 1})`, `σ_j > 0`. -/
@[dlmf 2.10.E32]
theorem darboux_smooth_singular {f g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (g2b_punctured r)) (hg : DifferentiableOn ℂ g (g2b_punctured r))
    {Z : Finset ℂ} (hZ : ∀ w ∈ Z, ‖w‖ = r) {m : ℕ}
    (hext : ∀ k ≤ m, ∃ hk : ℂ → ℂ, ContinuousOn hk ({z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ r} \ Z) ∧
      EqOn hk (iteratedDeriv k (f - g)) (g2b_punctured r))
    (σ : ℂ → ℝ) (hσ : ∀ w ∈ Z, 0 < σ w)
    (hsing : ∀ w ∈ Z, iteratedDeriv m (f - g) =O[𝓝[g2b_punctured r] w]
      fun z => ‖z - w‖ ^ (σ w - 1))
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) :
    Tendsto (fun n : ℤ => (laurentCoeff f ρ n - laurentCoeff g ρ n) * (r : ℂ) ^ n *
      ((|n| : ℤ) : ℂ) ^ m) cofinite (𝓝 0) := by
  sorry

/-! ### Example: Legendre polynomials of large degree (2.10.33–2.10.36) -/

/-- DLMF 2.10.33: `(1 - 2z cos α + z²)^{-1/2} = ∑ P_n(cos α) zⁿ` for `|z| < 1` and real `α`
(principal power). Corollary of the project's generating function 18.12.11. -/
@[dlmf 2.10.E33]
theorem legendre_generating_cos (α : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => DLMF.OrthogonalPolynomials.legendrePolyP n (Real.cos α) * z ^ n)
      ((1 - 2 * (Real.cos α : ℂ) * z + z ^ 2) ^ (-1 / 2 : ℂ)) :=
  DLMF.OrthogonalPolynomials.legendre_generating_function (Real.abs_cos_le_one α) hz

/-- DLMF 2.10.35: for `0 < α < π` the comparison function 2.10.34 has the Maclaurin
coefficients `g_n = (2/(π sin α))^{1/2} Γ(n + 1/2)/n! cos(nα + α/2 - π/4)`, `|z| < 1`.
DLMF states the example for `α ∈ (0, 2π)`; the formula needs `α ∈ (0, π)`. -/
@[dlmf 2.10.E35 "corrected: α ∈ (0, π), not (0, 2π)", dlmf 2.10.E34]
theorem legendreComparison_hasSum {α : ℝ} (hα : α ∈ Ioo 0 π) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (((2 / (π * Real.sin α)) ^ (1 / 2 : ℝ) *
        Real.Gamma (n + 1 / 2) / n.factorial * Real.cos (n * α + α / 2 - π / 4) : ℝ) : ℂ) *
        z ^ n)
      (legendreComparison α z) := by
  sorry

/-- DLMF 2.10.36: for `0 < α < π`,
`P_n(cos α) = (2/(πn sin α))^{1/2} cos(nα + α/2 - π/4) + o(n^{-1})` as `n → ∞`.
DLMF states the example for `α ∈ (0, 2π)`; for `π < α < 2π` the right side is not real. -/
@[dlmf 2.10.E36 "corrected: α ∈ (0, π), not (0, 2π)", dlmf 2.10.iv]
theorem legendrePolyP_cos_asymptotic {α : ℝ} (hα : α ∈ Ioo 0 π) :
    Tendsto (fun n : ℕ => (n : ℝ) * ‖DLMF.OrthogonalPolynomials.legendrePolyP n (Real.cos α) -
      (((2 / (π * n * Real.sin α)) ^ (1 / 2 : ℝ) *
        Real.cos (n * α + α / 2 - π / 4) : ℝ) : ℂ)‖) atTop (𝓝 0) := by
  sorry

end DLMF.AsymptoticApproximations
