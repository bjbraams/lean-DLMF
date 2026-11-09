/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.ODE.Basic
public import Mathlib.Algebra.Group.ForwardDiff

public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion

/-!
# Difference equations (DLMF §2.9)

Asymptotic solutions of the three-term recurrence `w(n+2) + f(n) w(n+1) + g(n) w(n) = 0`
(2.9.1) when `f(n) ~ ∑ f_s n^{-s}`, `g(n) ~ ∑ g_s n^{-s}` (2.9.3), `g₀ ≠ 0`. The solutions
are sequences on all of `ℕ`, so the theorems that produce them also assume `g(n) ≠ 0` for every
`n`; DLMF works with large `n` only.

## Main results

* `recurrence_eq_difference`, `recurrence_iff_difference`: 2.9.1 is equivalent to the
  difference equation 2.9.2.
* `difference_distinct_roots_solution`, `difference_distinct_roots_independent`,
  `difference_distinct_roots_independent'`: the solutions 2.9.8 with the formal series 2.9.4–2.9.7
  when the roots of the characteristic equation 2.9.5 are distinct, and their independence
  (§2.9(i)).
* `difference_recessive`: recessive and dominant solutions (§2.9(i)).
* `difference_coincident_sqrt`, `difference_coincident_power`,
  `difference_coincident_power_int`, `difference_coincident_log`: coincident characteristic
  values (DLMF 2.9.9–2.9.13).

## Implementation notes

Expansions are `Asymptotics.HasAsymptoticExpansion atTop` in the scales
`n ↦ ρⁿ n^{α-s}` (2.9.8, 2.9.12) and `n ↦ ρⁿ e^{±κ√n} n^{α-s/2}` (2.9.9), with complex powers
`(n : ℂ) ^ (α - s)` (principal branch, `n > 0`). The coefficient `a_{s,j}` is `differenceCoeff`.
-/

@[expose] public noncomputable section

open Filter Asymptotics Finset
open scoped Topology

namespace DLMF.AsymptoticApproximations

/-- DLMF 2.9.1 ⇔ 2.9.2: the three-term recurrence `w(n+2) + f(n)w(n+1) + g(n)w(n) = 0` is
equivalent to the second-order difference equation
`Δ²w(n) + (2 + f(n)) Δw(n) + (1 + f(n) + g(n)) w(n) = 0`; the two left sides are equal. -/
@[dlmf 2.9.E1, dlmf 2.9.E2]
theorem recurrence_eq_difference (f g w : ℕ → ℂ) (n : ℕ) :
    fwdDiff 1 (fwdDiff 1 w) n + (2 + f n) * fwdDiff 1 w n + (1 + f n + g n) * w n =
      w (n + 2) + f n * w (n + 1) + g n * w n := by
  simp only [fwdDiff]; ring

/-- DLMF 2.9.1 ⇔ 2.9.2 for all `n = 0, 1, 2, …`. -/
@[dlmf 2.9.E1, dlmf 2.9.E2]
theorem recurrence_iff_difference (f g w : ℕ → ℂ) :
    IsRecurrenceSolution f g w ↔
      ∀ n, fwdDiff 1 (fwdDiff 1 w) n + (2 + f n) * fwdDiff 1 w n +
        (1 + f n + g n) * w n = 0 := by
  simp only [IsRecurrenceSolution, recurrence_eq_difference]

/-- DLMF 2.9.4–2.9.8 (distinct characteristic values): let `f(n) ~ ∑ f_s n^{-s}` and
`g(n) ~ ∑ g_s n^{-s}` as `n → ∞` (2.9.3) with `g₀ ≠ 0` and `f₀² ≠ 4g₀`, and let `ρ` be a root
of `ρ² + f₀ρ + g₀ = 0` (2.9.5). Assume also `g(n) ≠ 0` for every `n`, so that a solution for
large `n` extends backwards to all of `ℕ`; DLMF states the result for large `n`, and without
this hypothesis it fails on `ℕ` (for `f = (0, -3, -3, …)`, `g = (0, 2, 2, …)` and `ρ = 1`,
every solution is `B(2ⁿ - 4)` for `n ≥ 1`). Then 2.9.1 has a solution
`w(n) ~ ρⁿ n^{α} ∑ a_s n^{-s}` with `α` from 2.9.6 and `a_s` from 2.9.7. Applied to the two
roots it gives the linearly independent solutions `w₁`, `w₂`. -/
@[dlmf 2.9.E3, dlmf 2.9.E4, dlmf 2.9.E5, dlmf 2.9.E8, dlmf 2.9.i]
theorem difference_distinct_roots_solution {f g : ℕ → ℂ} {fs gs : ℕ → ℂ}
    (hf : HasAsymptoticExpansion atTop invPowScale fs f)
    (hg : HasAsymptoticExpansion atTop invPowScale gs g) (hg0 : gs 0 ≠ 0)
    (hgn : ∀ n, g n ≠ 0)
    (hdisc : fs 0 ^ 2 ≠ 4 * gs 0) {ρ : ℂ} (hρ : ρ ^ 2 + fs 0 * ρ + gs 0 = 0) :
    ∃ w : ℕ → ℂ, IsRecurrenceSolution f g w ∧
      HasAsymptoticExpansion atTop (geomCpowScale ρ (differenceExponent fs gs ρ))
        (differenceCoeff fs gs ρ) w := by
  sorry

/-- `(n+1)^α / n^α → 1`. -/
private lemma tendsto_natCast_add_one_cpow_div (α : ℂ) :
    Tendsto (fun n : ℕ => ((n : ℂ) + 1) ^ α / (n : ℂ) ^ α) atTop (𝓝 1) := by
  have h0 : Tendsto (fun n : ℕ => Real.log (1 + (n : ℝ)⁻¹)) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add (1 : ℝ)
    rw [add_zero] at h
    have h' := (Real.continuousAt_log one_ne_zero).tendsto.comp h
    rwa [Real.log_one] at h'
  have h1 : Tendsto (fun n : ℕ => Complex.exp (α * (Real.log (1 + (n : ℝ)⁻¹) : ℂ)))
      atTop (𝓝 1) := by
    have hc : Continuous fun y : ℝ => Complex.exp (α * (y : ℂ)) := by fun_prop
    have := (hc.tendsto 0).comp h0
    simpa [Function.comp_def] using this
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hn1, Complex.cpow_def_of_ne_zero (by exact_mod_cast (by linarith : (n : ℝ) + 1 ≠ 0)),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn0.ne'), ← Complex.exp_sub,
    ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le, ← Complex.ofReal_log (by linarith)]
  congr 1
  rw [show (1 : ℝ) + (n : ℝ)⁻¹ = (n + 1) / n by field_simp, Real.log_div (by linarith) hn0.ne']
  push_cast
  ring

/-- Leading-order form of an expansion in `geomCpowScale`. -/
private lemma tendsto_div_geomCpowScale {ρ α : ℂ} (hρ : ρ ≠ 0) {a : ℕ → ℂ} (ha : a 0 = 1)
    {w : ℕ → ℂ}
    (hw : HasAsymptoticExpansion atTop (geomCpowScale ρ α) a w) :
    Tendsto (fun n => w n / geomCpowScale ρ α 0 n) atTop (𝓝 1) := by
  have h1 := hw 1
  simp only [range_one, sum_singleton, ha, smul_eq_mul, mul_one] at h1
  have hev : ∀ᶠ n : ℕ in atTop, geomCpowScale ρ α 0 n ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    simp only [geomCpowScale]
    exact mul_ne_zero (pow_ne_zero _ hρ) (by rw [Ne, Complex.cpow_eq_zero_iff]; tauto)
  have h2 : (fun n => (w n - geomCpowScale ρ α 0 n) / geomCpowScale ρ α 0 n) =O[atTop]
      fun n : ℕ => ((n : ℂ))⁻¹ := by
    refine (h1.mul (isBigO_refl (fun n => (geomCpowScale ρ α 0 n)⁻¹) atTop)).congr' ?_ ?_
    · exact Eventually.of_forall fun n => by simp [div_eq_mul_inv]
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      simp only [geomCpowScale, Nat.cast_one, Nat.cast_zero, sub_zero]
      rw [Complex.cpow_sub _ _ this, Complex.cpow_one]
      have h3 : (n : ℂ) ^ α ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; tauto
      field_simp
  have h3 : Tendsto (fun n : ℕ => ((n : ℂ))⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).ofReal
  have h4 := (h2.trans_tendsto h3).add_const 1
  rw [zero_add] at h4
  refine h4.congr' ?_
  filter_upwards [hev] with n hn
  field_simp
  ring

/-- DLMF §2.9(i) (independence of the two solutions of 2.9.8): solutions with the expansions
2.9.8 for the two distinct roots `ρ₁ ≠ ρ₂` of 2.9.5 are linearly independent; their
Casoratian `w₁(n) w₂(n+1) - w₁(n+1) w₂(n)` is eventually nonzero. This is stronger than DLMF, which
also assumes the expansions (2.9.3) of `f` and `g`; here `fs`, `gs` are arbitrary sequences with
`gs 0 ≠ 0`. -/
@[dlmf 2.9.i]
theorem difference_distinct_roots_independent' {fs gs : ℕ → ℂ} (hg0 : gs 0 ≠ 0)
    {ρ₁ ρ₂ : ℂ} (h12 : ρ₁ ≠ ρ₂) (hρ₁ : ρ₁ ^ 2 + fs 0 * ρ₁ + gs 0 = 0)
    (hρ₂ : ρ₂ ^ 2 + fs 0 * ρ₂ + gs 0 = 0) {w₁ w₂ : ℕ → ℂ}
    (hw₁ : HasAsymptoticExpansion atTop (geomCpowScale ρ₁ (differenceExponent fs gs ρ₁))
      (differenceCoeff fs gs ρ₁) w₁)
    (hw₂ : HasAsymptoticExpansion atTop (geomCpowScale ρ₂ (differenceExponent fs gs ρ₂))
      (differenceCoeff fs gs ρ₂) w₂) :
    ∀ᶠ n in atTop, w₁ n * w₂ (n + 1) - w₁ (n + 1) * w₂ n ≠ 0 := by
  -- only the leading terms of the two expansions are needed
  have hρne : ∀ ρ : ℂ, ρ ^ 2 + fs 0 * ρ + gs 0 = 0 → ρ ≠ 0 := fun ρ h h0 =>
    hg0 (by subst h0; simpa using h)
  set α₁ := differenceExponent fs gs ρ₁
  set α₂ := differenceExponent fs gs ρ₂
  have hu₁ := tendsto_div_geomCpowScale (hρne _ hρ₁) (by simp [differenceCoeff]) hw₁
  have hu₂ := tendsto_div_geomCpowScale (hρne _ hρ₂) (by simp [differenceCoeff]) hw₂
  have hu₁' := hu₁.comp (tendsto_add_atTop_nat 1)
  have hu₂' := hu₂.comp (tendsto_add_atTop_nat 1)
  have hr₁ := tendsto_natCast_add_one_cpow_div α₁
  have hr₂ := tendsto_natCast_add_one_cpow_div α₂
  have hE := ((((tendsto_const_nhds (x := ρ₂)).mul hr₂).mul hu₁).mul hu₂').sub
    ((((tendsto_const_nhds (x := ρ₁)).mul hr₁).mul hu₁').mul hu₂)
  simp only [mul_one] at hE
  filter_upwards [hE.eventually_ne (sub_ne_zero.mpr h12.symm), eventually_ge_atTop 1]
    with n hEn hn hC
  apply hEn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
  have hp : ∀ α : ℂ, (n : ℂ) ^ α ≠ 0 := fun α => by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hp1 : ∀ α : ℂ, ((n : ℂ) + 1) ^ α ≠ 0 := fun α => by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have h1 := hρne _ hρ₁
  have h2 := hρne _ hρ₂
  simp only [Function.comp, geomCpowScale, Nat.cast_zero, sub_zero, Nat.cast_add, Nat.cast_one]
  have hz : w₁ n * w₂ (n + 1) = w₁ (n + 1) * w₂ n := sub_eq_zero.mp hC
  have hp' := hp α₁
  have hp'' := hp α₂
  have hq' := hp1 α₁
  have hq'' := hp1 α₂
  field_simp
  rw [pow_succ, pow_succ]
  linear_combination (ρ₁ * ρ₂ * ρ₁ ^ n * ρ₂ ^ n) * hz

/-- DLMF §2.9(i) (independence of the two solutions of 2.9.8): solutions with the expansions
2.9.8 for the two distinct roots `ρ₁ ≠ ρ₂` of 2.9.5 are linearly independent; their
Casoratian `w₁(n) w₂(n+1) - w₁(n+1) w₂(n)` is eventually nonzero. -/
@[dlmf 2.9.i]
theorem difference_distinct_roots_independent {f g : ℕ → ℂ} {fs gs : ℕ → ℂ}
    (_hf : HasAsymptoticExpansion atTop invPowScale fs f)
    (_hg : HasAsymptoticExpansion atTop invPowScale gs g) (hg0 : gs 0 ≠ 0)
    {ρ₁ ρ₂ : ℂ} (h12 : ρ₁ ≠ ρ₂) (hρ₁ : ρ₁ ^ 2 + fs 0 * ρ₁ + gs 0 = 0)
    (hρ₂ : ρ₂ ^ 2 + fs 0 * ρ₂ + gs 0 = 0) {w₁ w₂ : ℕ → ℂ}
    (hw₁ : HasAsymptoticExpansion atTop (geomCpowScale ρ₁ (differenceExponent fs gs ρ₁))
      (differenceCoeff fs gs ρ₁) w₁)
    (hw₂ : HasAsymptoticExpansion atTop (geomCpowScale ρ₂ (differenceExponent fs gs ρ₂))
      (differenceCoeff fs gs ρ₂) w₂) :
    ∀ᶠ n in atTop, w₁ n * w₂ (n + 1) - w₁ (n + 1) * w₂ n ≠ 0 :=
  difference_distinct_roots_independent' hg0 h12 hρ₁ hρ₂ hw₁ hw₂

/-- DLMF §2.9(i) (recessive and dominant solutions): in the situation of
`difference_distinct_roots_solution`, if `|ρ₂| > |ρ₁|`, or `|ρ₂| = |ρ₁|` and
`Re α₂ > Re α₁`, then `w₁` is recessive, `w₁(n)/w₂(n) → 0`, and it is unique up to a constant
factor: every solution `v` of 2.9.1 with `v(n)/w₂(n) → 0` is a multiple of `w₁`. -/
@[dlmf 2.9.i]
theorem difference_recessive {f g : ℕ → ℂ} {fs gs : ℕ → ℂ}
    (hf : HasAsymptoticExpansion atTop invPowScale fs f)
    (hg : HasAsymptoticExpansion atTop invPowScale gs g) (hg0 : gs 0 ≠ 0)
    {ρ₁ ρ₂ : ℂ} (h12 : ρ₁ ≠ ρ₂) (hρ₁ : ρ₁ ^ 2 + fs 0 * ρ₁ + gs 0 = 0)
    (hρ₂ : ρ₂ ^ 2 + fs 0 * ρ₂ + gs 0 = 0)
    (hdom : ‖ρ₁‖ < ‖ρ₂‖ ∨ (‖ρ₁‖ = ‖ρ₂‖ ∧
      (differenceExponent fs gs ρ₁).re < (differenceExponent fs gs ρ₂).re))
    {w₁ w₂ : ℕ → ℂ} (hs₁ : IsRecurrenceSolution f g w₁) (hs₂ : IsRecurrenceSolution f g w₂)
    (hw₁ : HasAsymptoticExpansion atTop (geomCpowScale ρ₁ (differenceExponent fs gs ρ₁))
      (differenceCoeff fs gs ρ₁) w₁)
    (hw₂ : HasAsymptoticExpansion atTop (geomCpowScale ρ₂ (differenceExponent fs gs ρ₂))
      (differenceCoeff fs gs ρ₂) w₂) :
    Tendsto (fun n => w₁ n / w₂ n) atTop (𝓝 0) ∧
      ∀ v : ℕ → ℂ, IsRecurrenceSolution f g v → Tendsto (fun n => v n / w₂ n) atTop (𝓝 0) →
        ∃ c : ℂ, v = c • w₁ := by
  sorry

/-- DLMF 2.9.9–2.9.10 (coincident characteristic values, `2g₁ ≠ f₀f₁`): if `f₀² = 4g₀ ≠ 0`
with double root `ρ = -f₀/2` of 2.9.5, and `κ`, `α` satisfy `√g₀ κ = √(2f₀f₁ - 4g₁)` and
`4g₀α = g₀ + 2g₁` (any choice of the square roots, `κ ≠ 0`), then 2.9.1 has independent
solutions `w_j(n) ~ ρⁿ exp((-1)^j κ√n) n^{α} ∑ (-1)^{js} c_s n^{-s/2}`, `j = 1, 2`, with
`c₀ = 1` and the higher `c_s` determined by formal substitution. -/
@[dlmf 2.9.E9, dlmf 2.9.E10, dlmf 2.9.ii]
theorem difference_coincident_sqrt {f g : ℕ → ℂ} {fs gs : ℕ → ℂ}
    (hf : HasAsymptoticExpansion atTop invPowScale fs f)
    (hg : HasAsymptoticExpansion atTop invPowScale gs g) (hg0 : gs 0 ≠ 0)
    (hgn : ∀ n, g n ≠ 0)
    (hdisc : fs 0 ^ 2 = 4 * gs 0) (h1 : 2 * gs 1 ≠ fs 0 * fs 1) {κ α : ℂ}
    (hκ : κ ^ 2 * gs 0 = 2 * fs 0 * fs 1 - 4 * gs 1) (hα : 4 * gs 0 * α = gs 0 + 2 * gs 1) :
    ∃ c : ℕ → ℂ, c 0 = 1 ∧ ∃ w₁ w₂ : ℕ → ℂ,
      IsRecurrenceSolution f g w₁ ∧ IsRecurrenceSolution f g w₂ ∧
      HasAsymptoticExpansion atTop (geomExpSqrtScale (-fs 0 / 2) κ α (-1)) c w₁ ∧
      HasAsymptoticExpansion atTop (geomExpSqrtScale (-fs 0 / 2) κ α 1)
        (fun s => (-1) ^ s * c s) w₂ ∧
      ∀ᶠ n in atTop, w₁ n * w₂ (n + 1) - w₁ (n + 1) * w₂ n ≠ 0 := by
  sorry

/-- DLMF 2.9.11–2.9.12 (coincident characteristic values, `2g₁ = f₀f₁`): if `f₀² = 4g₀ ≠ 0`,
`ρ = -f₀/2`, and `α` is a root of `2g₀α² - (f₀f₁ + 2g₀)α + 2g₂ - f₀f₂ = 0` (2.9.11) whose
difference from the other root `α'` is not an integer, then 2.9.1 has a solution
`w(n) ~ ρⁿ n^{α} ∑ a_s n^{-s}` with `a₀ = 1` and the `a_s` satisfying 2.9.7 (whose left side
now vanishes). Applied to both roots it gives the independent solutions `w₁`, `w₂`. -/
@[dlmf 2.9.E11, dlmf 2.9.E12, dlmf 2.9.ii]
theorem difference_coincident_power {f g : ℕ → ℂ} {fs gs : ℕ → ℂ}
    (hf : HasAsymptoticExpansion atTop invPowScale fs f)
    (hg : HasAsymptoticExpansion atTop invPowScale gs g) (hg0 : gs 0 ≠ 0)
    (hgn : ∀ n, g n ≠ 0)
    (hdisc : fs 0 ^ 2 = 4 * gs 0) (h1 : 2 * gs 1 = fs 0 * fs 1) {α α' : ℂ}
    (hroots : ∀ x : ℂ, 2 * gs 0 * x ^ 2 - (fs 0 * fs 1 + 2 * gs 0) * x + 2 * gs 2 -
      fs 0 * fs 2 = 2 * gs 0 * (x - α) * (x - α'))
    (hint : ∀ m : ℤ, α' - α ≠ m) :
    ∃ a : ℕ → ℂ, IsDifferenceCoeffRel fs gs (-fs 0 / 2) α a ∧ ∃ w : ℕ → ℂ,
      IsRecurrenceSolution f g w ∧
          HasAsymptoticExpansion atTop (geomCpowScale (-fs 0 / 2) α) a w := by
  sorry

/-- DLMF 2.9.12 for `j = 1` when `α₂ - α₁ ∈ {0, 1, 2, …}` (§2.9(ii)): with the hypotheses of
`difference_coincident_power` and roots `α₁`, `α₂` of 2.9.11 with `α₂ - α₁ = d ∈ ℕ`, 2.9.1 has
a solution `w₁(n) ~ ρⁿ n^{α₁} ∑ a_s n^{-s}` with `a₀ = 1` and the `a_s` satisfying 2.9.7. -/
@[dlmf 2.9.E12, dlmf 2.9.ii]
theorem difference_coincident_power_int {f g : ℕ → ℂ} {fs gs : ℕ → ℂ}
    (hf : HasAsymptoticExpansion atTop invPowScale fs f)
    (hg : HasAsymptoticExpansion atTop invPowScale gs g) (hg0 : gs 0 ≠ 0)
    (hgn : ∀ n, g n ≠ 0)
    (hdisc : fs 0 ^ 2 = 4 * gs 0) (h1 : 2 * gs 1 = fs 0 * fs 1) {α₁ α₂ : ℂ}
    (hroots : ∀ x : ℂ, 2 * gs 0 * x ^ 2 - (fs 0 * fs 1 + 2 * gs 0) * x + 2 * gs 2 -
      fs 0 * fs 2 = 2 * gs 0 * (x - α₁) * (x - α₂))
    {d : ℕ} (hd : α₂ - α₁ = d) :
    ∃ a : ℕ → ℂ, IsDifferenceCoeffRel fs gs (-fs 0 / 2) α₁ a ∧ ∃ w : ℕ → ℂ,
      IsRecurrenceSolution f g w ∧
          HasAsymptoticExpansion atTop (geomCpowScale (-fs 0 / 2) α₁) a w := by
  sorry

/-- DLMF 2.9.13 (coincident characteristic values, `2g₁ = f₀f₁`, `α₂ - α₁ = d ∈ ℕ`): given the
solution `w₁` of `difference_coincident_power_int`, there is an independent solution
`w₂(n) ~ ρⁿ n^{α₂} ∑_{s ≠ d} b_s n^{-s} + c w₁(n) ln n`; that is, `w₂ - c w₁ ln` has the
expansion with coefficients `b_s` and `b_d = 0`. The normalization is `c = 1` when `d = 0` and
`b₀ = 1` when `d ≥ 1`. -/
@[dlmf 2.9.E13, dlmf 2.9.ii]
theorem difference_coincident_log {f g : ℕ → ℂ} {fs gs : ℕ → ℂ}
    (hf : HasAsymptoticExpansion atTop invPowScale fs f)
    (hg : HasAsymptoticExpansion atTop invPowScale gs g) (hg0 : gs 0 ≠ 0)
    (hgn : ∀ n, g n ≠ 0)
    (hdisc : fs 0 ^ 2 = 4 * gs 0) (h1 : 2 * gs 1 = fs 0 * fs 1) {α₁ α₂ : ℂ}
    (hroots : ∀ x : ℂ, 2 * gs 0 * x ^ 2 - (fs 0 * fs 1 + 2 * gs 0) * x + 2 * gs 2 -
      fs 0 * fs 2 = 2 * gs 0 * (x - α₁) * (x - α₂))
    {d : ℕ} (hd : α₂ - α₁ = d) {a : ℕ → ℂ} {w₁ : ℕ → ℂ} (hs₁ : IsRecurrenceSolution f g w₁)
    (hw₁ : HasAsymptoticExpansion atTop (geomCpowScale (-fs 0 / 2) α₁) a w₁) :
    ∃ (b : ℕ → ℂ) (c : ℂ) (w₂ : ℕ → ℂ), b d = 0 ∧ (d = 0 → c = 1) ∧ (1 ≤ d → b 0 = 1) ∧
      IsRecurrenceSolution f g w₂ ∧
      HasAsymptoticExpansion atTop (geomCpowScale (-fs 0 / 2) α₂) b
        (fun n => w₂ n - c * w₁ n * Real.log n) ∧
      ∀ᶠ n in atTop, w₁ n * w₂ (n + 1) - w₁ (n + 1) * w₂ n ≠ 0 := by
  sorry

end DLMF.AsymptoticApproximations
