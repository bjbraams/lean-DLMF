/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Summability.Defs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Fractional integrals and derivatives (DLMF §1.15(vi)–(vii))

The Riemann–Liouville fractional integral `fractionalIntegral` (1.15.47) and the fractional
derivative `fractionalDerivative` (1.15.51, with `n = ⌊ℜα⌋ + 1`) are defined in
`Summability/Defs.lean`. The statements are for `x ≥ 0` (DLMF erratum of version 1.0.1); we take
`x > 0` where derivatives in `x` occur and `f` continuous on `[0, ∞)`.

Proved: the power rule `I^α t^μ = Γ(μ+1)/Γ(μ+α+1) x^{μ+α}` (the termwise form of 1.15.50, by
Mathlib's Beta integral `Complex.Gamma_mul_Gamma_eq_betaIntegral`) and the agreement of
`fractionalIntegral` with the variant of §1.15(vi) with lower limit `0`. Admitted: the semigroup
law 1.15.48, the power-series formula 1.15.49–1.15.50, the independence of `n` in 1.15.51, the
rule 1.15.52, the law 1.15.53 and the remark `D^{1/2} D ≠ D^{3/2}`.

**Missing hypothesis (1.15.53).** DLMF states `D^α D^β = D^{α+β}` whenever none of `α`, `β`,
`α + β` is an integer, without a condition on `f`. This fails in general: for `f(x) = x^{β-1}`
(`ℜβ > 0`), `I^{n-β} f = (Γ(β)/Γ(n)) x^{n-1}` by the power rule, so `D^β f = 0` and
`D^α D^β f = 0`, while `D^{α+β} f = (Γ(β)/Γ(-α)) x^{-α-1} ≠ 0`; e.g. `α = 1/2`, `β = 1/3`. We
acquire 1.15.53 for power functions `x^μ` with `ℜμ > -1` and `ℜ(μ - β) > -1`
(`fractionalDerivative_fractionalDerivative_cpow`), where it holds by the power rule.
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped Nat

namespace DLMF.AlgebraicAnalytic

/-- DLMF §1.15(vi): `fractionalIntegral` (1.15.47) is the variant with lower limit `a = 0`. -/
@[dlmf 1.15.vi]
theorem fractionalIntegral_eq_riemannLiouvilleIntegralFrom (α : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    fractionalIntegral α f x = riemannLiouvilleIntegralFrom 0 α f x := rfl

/-- DLMF 1.15.48: `I^α I^β = I^{α+β}` for `ℜα > 0`, `ℜβ > 0`, applied to a function continuous on
`[0, ∞)` at `x ≥ 0`. -/
@[dlmf 1.15.E48]
theorem fractionalIntegral_fractionalIntegral {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re)
    {f : ℝ → ℂ} (hf : ContinuousOn f (Ici 0)) {x : ℝ} (hx : 0 ≤ x) :
    fractionalIntegral α (fractionalIntegral β f) x = fractionalIntegral (α + β) f x := by
  sorry

/-- DLMF 1.15.50 for a single power (power rule): for `ℜα > 0`, `ℜμ > -1` and `x > 0`,
`I^α t^μ = Γ(μ+1)/Γ(μ+α+1) x^{μ+α}`. For `μ = k` this is the `k`-th term of 1.15.50,
`k!/Γ(k+α+1) x^{k+α}`; stronger than DLMF (complex `μ`). -/
@[dlmf 1.15.E50]
theorem fractionalIntegral_cpow {α μ : ℂ} (hα : 0 < α.re) (hμ : -1 < μ.re) {x : ℝ}
    (hx : 0 < x) :
    fractionalIntegral α (fun t => (t : ℂ) ^ μ) x =
      Complex.Gamma (μ + 1) / Complex.Gamma (μ + α + 1) * (x : ℂ) ^ (μ + α) := by
  unfold fractionalIntegral
  set g : ℝ → ℂ := fun t => ((x - t : ℝ) : ℂ) ^ (α - 1) * (t : ℂ) ^ μ with hg
  have hx0 : (0 : ℝ) ≤ x := hx.le
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have h1 : x • (∫ u in (0 : ℝ)..1, g (x * u)) = ∫ t in (0 : ℝ)..x, g t := by
    have := intervalIntegral.smul_integral_comp_mul_left g x (a := 0) (b := 1)
    simp only [mul_zero, mul_one] at this
    exact this
  have h2 : (∫ u in (0 : ℝ)..1, g (x * u)) =
      (x : ℂ) ^ (α - 1 + μ) * Complex.betaIntegral (μ + 1) α := by
    unfold Complex.betaIntegral
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le zero_le_one] at hu
    simp only [hg]
    have e1 : ((x - x * u : ℝ) : ℂ) = ((x * (1 - u) : ℝ) : ℂ) := by push_cast; ring
    rw [e1, Complex.ofReal_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hx0 (by linarith [hu.2]),
      Complex.mul_cpow_ofReal_nonneg hx0 hu.1, Complex.cpow_add _ _ hxc]
    push_cast
    ring_nf
  have h3 : (∫ t in (0 : ℝ)..x, g t) = (x : ℂ) ^ (μ + α) * Complex.betaIntegral (μ + 1) α := by
    rw [← h1, h2, Complex.real_smul, ← mul_assoc]
    congr 1
    have hp : (x : ℂ) ^ (μ + α) = x * (x : ℂ) ^ (α - 1 + μ) := by
      rw [show μ + α = 1 + (α - 1 + μ) by ring, Complex.cpow_add _ _ hxc, Complex.cpow_one]
    exact hp.symm
  rw [h3]
  have hb := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := μ + 1) (t := α)
    (by simp; linarith) hα
  have hG : Complex.Gamma α ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hα
  have hG2 : Complex.Gamma (μ + 1 + α) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have e : μ + α + 1 = μ + 1 + α := by ring
  rw [e]
  field_simp
  linear_combination (-(x : ℂ) ^ (μ + α)) * hb

/-- DLMF 1.15.49–1.15.50: if `f(t) = ∑ a_k t^k` on `[0, x]` with `∑ |a_k| x^k < ∞`, then
`I^α f(x) = ∑ k!/Γ(k+α+1) a_k x^{k+α}` for `ℜα > 0`, `x > 0`. -/
@[dlmf 1.15.E49, dlmf 1.15.E50]
theorem hasSum_fractionalIntegral_of_hasSum {α : ℂ} (hα : 0 < α.re) {a : ℕ → ℂ}
    {f : ℝ → ℂ} {x : ℝ} (hx : 0 < x) (hs : Summable fun k => ‖a k‖ * x ^ k)
    (hf : ∀ t ∈ Icc 0 x, HasSum (fun k => a k * (t : ℂ) ^ k) (f t)) :
    HasSum (fun k : ℕ => (k ! : ℂ) / Complex.Gamma (k + α + 1) * a k * (x : ℂ) ^ (k + α))
      (fractionalIntegral α f x) := by
  sorry

/-- DLMF 1.15.51 (independence of `n`): for any integer `n > ℜα > 0`, `f` continuous on `[0, ∞)`
and `x > 0`, `(dⁿ/dxⁿ) I^{n-α} f(x)` equals `fractionalDerivative α f x` (defined with
`n = ⌊ℜα⌋ + 1`). -/
@[dlmf 1.15.E51]
theorem fractionalDerivative_eq_iteratedDeriv {α : ℂ} (hα : 0 < α.re) {n : ℕ}
    (hn : α.re < n) {f : ℝ → ℂ} (hf : ContinuousOn f (Ici 0)) {x : ℝ} (hx : 0 < x) :
    fractionalDerivative α f x = iteratedDeriv n (fractionalIntegral ((n : ℂ) - α) f) x := by
  sorry

/-- DLMF 1.15.52: `D^k I^α = D^n I^{α+n-k}` for `k = 1, …, n` (`D^k` the ordinary `k`-th
derivative), for `ℜα > 0`, `f` continuous on `[0, ∞)` and `x > 0`. -/
@[dlmf 1.15.E52]
theorem iteratedDeriv_fractionalIntegral {α : ℂ} (hα : 0 < α.re) {k n : ℕ} (hk : k ≤ n)
    {f : ℝ → ℂ} (hf : ContinuousOn f (Ici 0)) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (fractionalIntegral α f) x =
      iteratedDeriv n (fractionalIntegral (α + n - k) f) x := by
  sorry

/-- DLMF 1.15.53, for power functions: if none of `α`, `β`, `α + β` is an integer, `ℜα > 0`,
`ℜβ > 0`, `ℜμ > -1` and `ℜ(μ - β) > -1`, then `D^α D^β x^μ = D^{α+β} x^μ` for `x > 0`. DLMF states
1.15.53 without a hypothesis on `f`, which is false in general (see the module docstring). -/
@[dlmf 1.15.E53]
theorem fractionalDerivative_fractionalDerivative_cpow {α β μ : ℂ} (hα : 0 < α.re)
    (hβ : 0 < β.re) (hαi : ∀ m : ℤ, α ≠ m) (hβi : ∀ m : ℤ, β ≠ m) (hαβi : ∀ m : ℤ, α + β ≠ m)
    (hμ : -1 < μ.re) (hμβ : -1 < (μ - β).re) {x : ℝ} (hx : 0 < x) :
    fractionalDerivative α (fractionalDerivative β fun t => (t : ℂ) ^ μ) x =
      fractionalDerivative (α + β) (fun t => (t : ℂ) ^ μ) x := by
  sorry

/-- DLMF §1.15(vii), after 1.15.53: `D^{1/2} D ≠ D^{3/2}`. For `f = 1`, `D^{1/2}(f') = 0` while
`D^{3/2} f(1) = 1/Γ(-1/2) = -1/(2√π) ≠ 0`. -/
@[dlmf 1.15.vii]
theorem fractionalDerivative_half_deriv_ne :
    fractionalDerivative (1 / 2) (deriv fun _ : ℝ => (1 : ℂ)) 1 ≠
      fractionalDerivative (3 / 2) (fun _ : ℝ => (1 : ℂ)) 1 := by
  sorry

end DLMF.AlgebraicAnalytic
