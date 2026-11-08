/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Sums.Basic
public import DLMF.GeneralizedHypergeometric.Basic.PrincipalContinuationExistence
public import DLMF.GeneralizedHypergeometric.Basic
public import DLMF.Hypergeometric.Basic.GeneralizedCalculus
public import Mathlib.RingTheory.PowerSeries.Basic
public import DLMF.Hypergeometric.ArgumentContinuation
public import DLMF.Hypergeometric.Solutions
public import DLMF.OrthogonalPolynomials.Series
public import DLMF.AlgebraicAnalytic.Complex.Functions
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import DLMF.Hypergeometric.Saalschutz
public import DLMFMathlib.Analysis.Complex.BoundarySingularities
public import DLMFMathlib.Analysis.Complex.LaurentPowerSeries
public import DLMF.AsymptoticApproximations.Sums.LegendreDarboux
public import DLMF.AsymptoticApproximations.Sums.DarbouxDerivatives

/-!
# Entire functions and Darboux's method

This file covers DLMF §2.10(iii)–(iv): the example `₀F₂(-; 1, 1; x)` of an entire function
whose partial sums are written as contour integrals over the contour `𝒞` of Figure 2.10.1
(`contourIntegralC`), Laurent coefficients, and Darboux's method with the Legendre example.

## Main results

* `hypergeometric0F2OneOne_hasSum`, `generalizedHypergeometricCoeff_zero_one_one`: the series DLMF
  2.10.19, matched with the generalized hypergeometric coefficients `generalizedHypergeometricCoeff`
  of DLMF 16.2.1.
* `sum_0F2_eq_contourIntegral`, `cot_div_two_I`, `sum_0F2_eq_real_integral_add`: the contour
  integral representations DLMF 2.10.20–2.10.22.
* `hypergeometric0F2OneOne_eq_integrals`, `hypergeometric0F2OneOne_sub_integral_isBigO`,
  `hypergeometric0F2OneOne_isEquivalent`: DLMF 2.10.23–2.10.24.
* `laurent_expansion`: Laurent coefficients (DLMF 2.10.25–2.10.26).
* `darboux`, `darboux_singular`, `darboux_smooth`, `darboux_smooth_singular`: Darboux's method
  (DLMF 2.10.27–2.10.32).
* `legendre_generating_cos`: DLMF 2.10.33, the generating function
  `DLMF.OrthogonalPolynomials.legendre_generating_function` (DLMF 18.12.11) at `x = cos α`.
* `legendreComparison_hasSum`, `legendrePolynomialP_cos_asymptotic`: DLMF 2.10.35–2.10.36.

## Implementation notes

Erratum: in the Legendre example DLMF takes `α ∈ (0, 2π)`, but 2.10.34–2.10.36 need
`α ∈ (0, π)`: for `π < α < 2π`, `sin α < 0`, so `(2 sin α)^{-1/2}` and the right side of 2.10.36
are not real, while `P_n(cos α)` is real; with `α' = 2π - α` the correct phase is
`nα' + α'/2 - π/4`, not `nα + α/2 - π/4`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Asymptotics Complex Metric
open scoped Topology Real Nat

namespace DLMF.AsymptoticApproximations

/-! ### §2.10(iii) The example `₀F₂(-; 1, 1; x)` -/

/-- DLMF 2.10.19 (coefficients): the coefficients of `₀F₂(-; 1, 1; x)` in the normalization
16.2.1 are `1/(j!)³`. -/
@[dlmf 2.10.E19]
theorem generalizedHypergeometricCoeff_zero_one_one (j : ℕ) :
    DLMF.Hypergeometric.generalizedHypergeometricCoeff 0 {1, 1} j = 1 / (j.factorial : ℂ) ^ 3 := by
  simp only [DLMF.Hypergeometric.generalizedHypergeometricCoeff,
      DLMF.Hypergeometric.pochhammerProduct,
    Multiset.map_zero, Multiset.prod_zero, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton,
    DLMF.Hypergeometric.pochhammer, ascPochhammer_eval_one]
  have : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  field_simp

/-- The series `∑ x^j/(j!)³` converges absolutely for every `x`. -/
private lemma summable_pow_div_factorial_cube (x : ℂ) : Summable fun j : ℕ => x ^ j /
    (j.factorial : ℂ) ^ 3 := by
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
    HasSum (fun j : ℕ => DLMF.Hypergeometric.generalizedHypergeometricCoeff 0 {1, 1} j * x ^ j)
      (hypergeometric0F2OneOne x) := by
  have h := (summable_pow_div_factorial_cube x).hasSum
  refine h.congr_fun fun j => ?_
  rw [generalizedHypergeometricCoeff_zero_one_one]
  ring

/-- DLMF 2.10.19 in the project's convergence predicate for generalized hypergeometric series. -/
@[dlmf 2.10.E19]
theorem hypergeometricSeriesConvergesTo_0F2 (x : ℂ) :
    DLMF.Hypergeometric.HypergeometricSeriesConvergesTo 0 {1, 1} x
      (hypergeometric0F2OneOne x) :=
  (hypergeometric0F2OneOne_hasSum x).tendsto_sum_nat

/-- DLMF 2.10.20: for `x > 0` and `n ≥ 1`,
`∑_{j=0}^{n-1} x^j/(j!)³ = (2i)⁻¹ ∫_𝒞 x^t/Γ(t+1)³ cot(πt) dt`, with `𝒞` the contour of
Figure 2.10.1 (`contourIntegralC`); the residue of `cot(πt)` at `t = j` is `1/π`. -/
@[dlmf 2.10.E20]
theorem sum_0F2_eq_contourIntegral {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range n, (x : ℂ) ^ j / (j.factorial : ℂ) ^ 3 =
      (2 * I)⁻¹ * contourIntegralC
          (fun t => hypergeometric0F2OneOneIntegrand x t * Complex.cot (π * t)) n := by
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
      (∫ t in (-(1 / 2) : ℝ)..(n - 1 / 2), hypergeometric0F2OneOneIntegrand x t) -
        contourIntegralC₁ (fun t => hypergeometric0F2OneOneIntegrand x t /
            (Complex.exp (-(2 * π * I * t)) - 1))
          n +
        contourIntegralC₂ (fun t => hypergeometric0F2OneOneIntegrand x t /
            (Complex.exp (2 * π * I * t) - 1))
          n := by
  sorry

/-- DLMF 2.10.23 (first equality): for `x > 0`,
`₀F₂(-; 1, 1; x) = ∫_{-1/2}^∞ x^t/Γ(t+1)³ dt + 2ℜ ∫_{-1/2}^{i∞} x^t/Γ(t+1)³ dt/(e^{-2πit}-1)`,
the path from `-1/2` to `i∞` being the quarter circle `|t| = 1/2` from `-1/2` to `i/2` followed
by the imaginary axis. The integrals converge absolutely. -/
@[dlmf 2.10.E23]
theorem hypergeometric0F2OneOne_eq_integrals {x : ℝ} (hx : 0 < x) :
    let F : ℂ → ℂ := fun t => hypergeometric0F2OneOneIntegrand x t /
        (Complex.exp (-(2 * π * I * t)) - 1)
    hypergeometric0F2OneOne x =
      (∫ t in Ioi (-(1 / 2) : ℝ), hypergeometric0F2OneOneIntegrand x t) +
        2 * ((arcPathIntegral F (1 / 2) π (π / 2) +
          ∫ y in Ioi (1 / 2 : ℝ), F (I * y) * I).re : ℂ) := by
  sorry

/-- DLMF 2.10.23 (second equality): `₀F₂(-; 1, 1; x) = ∫_0^∞ x^t/Γ(t+1)³ dt + O(1)` as
`x → +∞`. -/
@[dlmf 2.10.E23]
theorem hypergeometric0F2OneOne_sub_integral_isBigO :
    (fun x : ℝ => hypergeometric0F2OneOne x - ∫ t in Ioi (0 : ℝ),
        hypergeometric0F2OneOneIntegrand x t)
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

/-- The punctured disc as the annulus `0 < |z - 0| < r` of §1.10. -/
private lemma puncturedDisc_eq (r : ℝ) :
    puncturedDisc r = {z : ℂ | 0 < ‖z - 0‖ ∧ ‖z - 0‖ < r} := by
  simp only [puncturedDisc, sub_zero]

/-- The punctured disc is open. -/
private lemma isOpen_puncturedDisc (r : ℝ) : IsOpen (puncturedDisc r) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

/-- Radius independence of the Laurent coefficients in a punctured disc. -/
private lemma laurentCoeff_zero_eq_of_le_puncturedDisc {f : ℂ → ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (puncturedDisc r)) {ρ ρ' : ℝ} (hρ : 0 < ρ) (hle : ρ ≤ ρ')
    (hρ' : ρ' < r) (n : ℤ) : AlgebraicAnalytic.laurentCoeff f 0 ρ' n =
        AlgebraicAnalytic.laurentCoeff f 0 ρ n := by
  simp only [laurentCoeff_zero_eq]
  congr 1
  have hsub : closedBall (0 : ℂ) ρ' \ ball 0 ρ ⊆ puncturedDisc r := by
    intro z hz
    simp only [Set.mem_sdiff, mem_closedBall, mem_ball, dist_zero_right, not_lt] at hz
    exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have hdiff : ∀ z ∈ closedBall (0 : ℂ) ρ' \ ball 0 ρ,
      DifferentiableAt ℂ (fun z => f z * z ^ (-(n + 1))) z := by
    intro z hz
    have hzA := hsub hz
    have hz0 : z ≠ 0 := fun h => by
      have h1 := hzA.1; rw [h, norm_zero] at h1; exact lt_irrefl _ h1
    exact (hf.differentiableAt ((isOpen_puncturedDisc r).mem_nhds hzA)).mul
      (differentiableAt_id.zpow (Or.inl hz0))
  exact circleIntegral_eq_of_differentiable_on_annulus_off_countable hρ hle
    countable_empty (fun z hz => (hdiff z hz).continuousAt.continuousWithinAt)
    (fun z hz => hdiff z ⟨ball_subset_closedBall hz.1.1, fun h => hz.1.2
      (ball_subset_closedBall h)⟩)

/-- Laurent coefficients do not depend on the radius in the punctured disc. -/
private lemma laurentCoeff_zero_eq_puncturedDisc {f : ℂ → ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (puncturedDisc r)) {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hρ' : 0 < ρ') (hρ'r : ρ' < r) (n : ℤ) : AlgebraicAnalytic.laurentCoeff f 0 ρ n =
        AlgebraicAnalytic.laurentCoeff f 0 ρ' n := by
  rcases le_total ρ ρ' with h | h
  · exact (laurentCoeff_zero_eq_of_le_puncturedDisc hf hρ h hρ'r n).symm
  · exact laurentCoeff_zero_eq_of_le_puncturedDisc hf hρ' h hρr n

/-- The Laurent coefficient as a Fourier coefficient on the circle `|z| = s`. -/
private lemma laurentCoeff_zero_eq_integral (h : ℂ → ℂ) {s : ℝ} (hs : 0 < s) (n : ℤ) :
    AlgebraicAnalytic.laurentCoeff h 0 s n = (2 * π * (s : ℂ) ^ n)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * π, h (s * Complex.exp (θ * I)) * Complex.exp (-(n * θ * I)) := by
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.2 hs.ne'
  rw [laurentCoeff_zero_eq, circleIntegral]
  simp only [deriv_circleMap, circleMap, zero_add, smul_eq_mul]
  have hpt : ∀ θ : ℝ, (s : ℂ) * Complex.exp (θ * I) * I * (h (s * Complex.exp (θ * I)) *
      ((s : ℂ) * Complex.exp (θ * I)) ^ (-(n + 1))) =
      (I * (s : ℂ) ^ (-n)) * (h (s * Complex.exp (θ * I)) * Complex.exp (-(n * θ * I))) := by
    intro θ
    have he : Complex.exp (θ * I) ≠ 0 := Complex.exp_ne_zero _
    rw [show -(n + 1) = -n - 1 by ring, zpow_sub_one₀ (mul_ne_zero hs0 he), mul_zpow,
      show -((n : ℂ) * θ * I) = ((-n : ℤ) : ℂ) * (θ * I) by push_cast; ring, exp_int_mul]
    field_simp
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, zpow_neg]
  generalize (∫ θ in (0 : ℝ)..2 * π,
    h (s * Complex.exp (θ * I)) * Complex.exp (-(n * θ * I))) = J
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hsn : (s : ℂ) ^ n ≠ 0 := zpow_ne_zero n hs0
  field_simp

/-- Riemann–Lebesgue lemma for Fourier coefficients on `[0, 2π]`. -/
private lemma tendsto_integral_mul_exp_cofinite (ψ : ℝ → ℂ) :
    Tendsto (fun n : ℤ => ∫ θ in (0 : ℝ)..2 * π, ψ θ * Complex.exp (-(n * θ * I))) cofinite
      (𝓝 0) := by
  set F : ℝ → ℂ := (Ioc 0 (2 * π)).indicator ψ
  have hmap : Tendsto (fun n : ℤ => (n : ℝ) / (2 * π)) cofinite (cocompact ℝ) := by
    have h1 := Int.tendsto_coe_cofinite
    rw [cocompact_eq_atBot_atTop] at h1 ⊢
    have h2 : Tendsto (fun x : ℝ => x / (2 * π)) (atBot ⊔ atTop) (atBot ⊔ atTop) :=
      tendsto_sup.2 ⟨(tendsto_id.atBot_div_const (by positivity)).mono_right le_sup_left,
        (tendsto_id.atTop_div_const (by positivity)).mono_right le_sup_right⟩
    exact h2.comp h1
  have h0 := (Real.tendsto_integral_exp_smul_cocompact F).comp hmap
  refine h0.congr fun n => ?_
  simp only [Function.comp_apply, F]
  rw [intervalIntegral.integral_of_le (by positivity), ← integral_indicator measurableSet_Ioc]
  congr 1; funext θ
  simp only [indicator]
  split_ifs
  · rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
    congr 2
    push_cast
    field_simp
  · simp

/-- The derivative of a periodic function is periodic. -/
private lemma periodic_deriv {ψ : ℝ → ℂ} {T : ℝ} (hper : Function.Periodic ψ T) :
    Function.Periodic (deriv ψ) T := fun x => by
  have h := deriv_comp_add_const (f := ψ) (a := T) (x := x)
  have he : (fun x => ψ (x + T)) = ψ := funext hper
  rw [he] at h
  exact h.symm

/-- Iterated derivatives of a periodic function are periodic. -/
private lemma periodic_iterate_deriv {ψ : ℝ → ℂ} {T : ℝ} (hper : Function.Periodic ψ T)
    (k : ℕ) : Function.Periodic (deriv^[k] ψ) T := by
  induction k with
  | zero => exact hper
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact periodic_deriv ih

/-- One integration by parts in a Fourier coefficient of a periodic `C¹` function. -/
private lemma integral_mul_exp_eq_deriv {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 1 ψ)
    (hper : Function.Periodic ψ (2 * π)) {n : ℤ} (hn : n ≠ 0) :
    ∫ θ in (0 : ℝ)..2 * π, ψ θ * Complex.exp (-(n * θ * I)) =
      ((n : ℂ) * I)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, deriv ψ θ * Complex.exp (-(n * θ * I)) := by
  have hnI : (n : ℂ) * I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hn) I_ne_zero
  set v : ℝ → ℂ := fun θ => Complex.exp (-(n * θ * I)) / (-((n : ℂ) * I))
  have hv : ∀ θ : ℝ, HasDerivAt v (Complex.exp (-(n * θ * I))) θ := by
    intro θ
    have hc : HasDerivAt (fun w : ℂ => Complex.exp (-(n * w * I)))
        (Complex.exp (-(n * θ * I)) * (-((n : ℂ) * 1 * I))) (θ : ℂ) :=
      (((hasDerivAt_id' (θ : ℂ)).const_mul (n : ℂ)).mul_const I).neg.cexp
    have := (hc.comp_ofReal).div_const (-((n : ℂ) * I))
    convert this using 1
    field_simp
  have hu : ∀ θ : ℝ, HasDerivAt ψ (deriv ψ θ) θ := fun θ =>
    ((hψ.differentiable one_ne_zero) θ).hasDerivAt
  have hcd : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hce : Continuous fun θ : ℝ => Complex.exp (-(n * θ * I)) := by fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 2 * π)
    (fun θ _ => hu θ) (fun θ _ => hv θ) (hcd.intervalIntegrable _ _) (hce.intervalIntegrable _ _)
  rw [hibp]
  have hp : ψ (2 * π) = ψ 0 := by simpa using hper 0
  have hv2 : v (2 * π) = v 0 := by
    simp only [v]
    congr 1
    rw [show -((n : ℂ) * ((2 * π : ℝ) : ℂ) * I) = (-n : ℤ) * (2 * π * I) by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I]
    simp
  rw [hp, hv2, sub_self, zero_sub]
  simp only [v, mul_div_assoc']
  rw [intervalIntegral.integral_div]
  generalize (∫ θ in (0 : ℝ)..2 * π, deriv ψ θ * Complex.exp (-(n * θ * I))) = J
  field_simp


/-- `k` integrations by parts in a Fourier coefficient of a periodic `Cᵐ` function, `k ≤ m`. -/
private lemma integral_mul_exp_eq_iterate_deriv {ψ : ℝ → ℂ} {m : ℕ} (hψ : ContDiff ℝ m ψ)
    (hper : Function.Periodic ψ (2 * π)) {n : ℤ} (hn : n ≠ 0) {k : ℕ} (hk : k ≤ m) :
    ∫ θ in (0 : ℝ)..2 * π, ψ θ * Complex.exp (-(n * θ * I)) =
      ((n : ℂ) * I)⁻¹ ^ k * ∫ θ in (0 : ℝ)..2 * π, deriv^[k] ψ θ * Complex.exp (-(n * θ * I)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih (by omega), Function.iterate_succ_apply', pow_succ, mul_assoc]
    congr 1
    refine integral_mul_exp_eq_deriv ?_ (periodic_iterate_deriv hper k) hn
    exact ContDiff.iterate_deriv' 1 k (hψ.of_le (by exact_mod_cast (show 1 + k ≤ m by omega)))

/-- DLMF 2.10.25–2.10.26: if `f` is analytic on `0 < |z| < r`, then for `0 < ρ < r` the
coefficients `f_n = (2πi)⁻¹ ∮_{|z|=ρ} f(z) z^{-n-1} dz` do not depend on `ρ`, and
`f(z) = ∑_{n ∈ ℤ} f_n z^n` for `0 < |z| < r`. -/
@[dlmf 2.10.E25, dlmf 2.10.E26]
theorem laurent_expansion {f : ℂ → ℂ} {r : ℝ} (hf : DifferentiableOn ℂ f (puncturedDisc r))
    {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hρ' : 0 < ρ') (hρ'r : ρ' < r) :
    AlgebraicAnalytic.laurentCoeff f 0 ρ = AlgebraicAnalytic.laurentCoeff f 0 ρ' ∧
      ∀ z ∈ puncturedDisc r,
          HasSum (fun n : ℤ => AlgebraicAnalytic.laurentCoeff f 0 ρ n * z ^ n) (f z) := by
  refine ⟨funext fun n => laurentCoeff_zero_eq_puncturedDisc hf hρ hρr hρ' hρ'r n, fun z hz => ?_⟩
  rw [puncturedDisc_eq] at hf hz
  have := DLMF.AlgebraicAnalytic.hasSum_laurentSeries le_rfl hf ⟨hρ, hρr⟩ hz
  simpa only [sub_zero] using this

/-- DLMF 2.10.27–2.10.29 (Darboux's method, conditions (a)–(c)): let `f` and the comparison
function `g` be analytic on `0 < |z| < r` (`g_n` its Laurent coefficients, 2.10.27), and let
`f - g` extend to a function `h` continuous on `0 < |z| ≤ r`. Then for `0 < ρ < r`,
`f_n - g_n = (2π rⁿ)⁻¹ ∫_0^{2π} h(re^{iθ}) e^{-niθ} dθ` (2.10.28), and
`f_n = g_n + o(r^{-n})` as `n → ±∞` (2.10.29). -/
@[dlmf 2.10.E27, dlmf 2.10.E28, dlmf 2.10.E29, dlmf 2.10.iv]
theorem darboux {f g h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (puncturedDisc r)) (hg : DifferentiableOn ℂ g (puncturedDisc r))
    (hh : ContinuousOn h {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ r})
    (hfg : EqOn h (f - g) (puncturedDisc r)) {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) :
    (∀ n : ℤ, AlgebraicAnalytic.laurentCoeff f 0 ρ n - AlgebraicAnalytic.laurentCoeff g 0 ρ n =
      (2 * π * (r : ℂ) ^ n)⁻¹ *
        ∫ θ in (0 : ℝ)..2 * π, h (r * Complex.exp (θ * I)) * Complex.exp (-(n * θ * I))) ∧
    Tendsto (fun n : ℤ =>
        (AlgebraicAnalytic.laurentCoeff f 0 ρ n - AlgebraicAnalytic.laurentCoeff g 0 ρ n) *
        (r : ℂ) ^ n) cofinite
      (𝓝 0) := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hhd : DifferentiableOn ℂ h (puncturedDisc r) :=
    (hf.sub hg).congr fun z hz => hfg hz
  have hsph : ∀ s, 0 < s → s < r → sphere (0 : ℂ) s ⊆ puncturedDisc r := fun s hs hsr z hz => by
    rw [mem_sphere, dist_zero_right] at hz
    exact ⟨hz ▸ hs, hz ▸ hsr⟩
  -- `f_n - g_n` is the Laurent coefficient of `h`
  have hsubc : ∀ n : ℤ, AlgebraicAnalytic.laurentCoeff f 0 ρ n -
      AlgebraicAnalytic.laurentCoeff g 0 ρ n =
      AlgebraicAnalytic.laurentCoeff h 0 ρ n := by
    intro n
    have hci : ∀ F : ℂ → ℂ, DifferentiableOn ℂ F (puncturedDisc r) →
        CircleIntegrable (fun z => F z * z ^ (-(n + 1))) 0 ρ := fun F hF => by
      refine ContinuousOn.circleIntegrable hρ.le ?_
      intro z hz
      have hz' := hsph ρ hρ hρr hz
      have hz0 : z ≠ 0 := fun h0 => by
        have h1 := hz'.1; rw [h0, norm_zero] at h1; exact lt_irrefl _ h1
      exact ((hF.continuousOn.mono (hsph ρ hρ hρr)) z hz).mul
        ((continuous_id.continuousAt.zpow₀ _ (Or.inl hz0)).continuousWithinAt)
    rw [laurentCoeff_zero_eq, laurentCoeff_zero_eq, laurentCoeff_zero_eq, ← mul_sub,
      ← circleIntegral.integral_sub (hci f hf) (hci g hg)]
    congr 1
    refine circleIntegral.integral_congr hρ.le fun z hz => ?_
    rw [hfg (hsph ρ hρ hρr hz)]
    simp only [Pi.sub_apply]; ring
  -- the Fourier integrals on circles of radius `s`
  set Φ : ℤ → ℝ → ℂ := fun n s => ∫ θ in (0 : ℝ)..2 * π,
    h (s * Complex.exp (θ * I)) * Complex.exp (-(n * θ * I)) with hΦ
  have key : ∀ n : ℤ, AlgebraicAnalytic.laurentCoeff h 0 ρ n = (2 * π * (r : ℂ) ^ n)⁻¹ * Φ n r := by
    intro n
    set c : ℝ → ℝ := fun s => max ρ (min s r)
    have hc : Continuous c := continuous_const.max (continuous_id.min continuous_const)
    have hcmem : ∀ s θ : ℝ, ((c s : ℂ) * Complex.exp (θ * I)) ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ r} := by
      intro s θ
      have h1 : ρ ≤ c s := le_max_left _ _
      have h2 : c s ≤ r := max_le hρr.le (min_le_right _ _)
      show 0 < ‖_‖ ∧ ‖_‖ ≤ r
      simp only [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (hρ.trans_le h1)]
      exact ⟨hρ.trans_le h1, h2⟩
    have hΨ : Continuous fun s => ∫ θ in (0 : ℝ)..2 * π,
        h (c s * Complex.exp (θ * I)) * Complex.exp (-(n * θ * I)) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      refine Continuous.mul ?_ (by fun_prop)
      refine hh.comp_continuous ?_ fun p => hcmem p.1 p.2
      exact (continuous_ofReal.comp (hc.comp continuous_fst)).mul (by fun_prop)
    have heq : ∀ s ∈ Ioo ρ r, (∫ θ in (0 : ℝ)..2 * π,
        h (c s * Complex.exp (θ * I)) * Complex.exp (-(n * θ * I))) =
        2 * π * (s : ℂ) ^ n * AlgebraicAnalytic.laurentCoeff h 0 ρ n := by
      intro s hs
      have hcs : c s = s := by
        simp only [c, min_eq_left hs.2.le, max_eq_right hs.1.le]
      rw [hcs, laurentCoeff_zero_eq_puncturedDisc hhd hρ hρr (hρ.trans hs.1) hs.2 n,
        laurentCoeff_zero_eq_integral h (hρ.trans hs.1) n]
      have hsn : (s : ℂ) ^ n ≠ 0 := zpow_ne_zero n (ofReal_ne_zero.2 (hρ.trans hs.1).ne')
      rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero hpi) hsn), one_mul]
    have hcr : c r = r := by simp only [c, min_self, max_eq_right hρr.le]
    have hlim1 := (hΨ.tendsto r).mono_left (nhdsWithin_le_nhds (s := Iio r))
    have hlim2 : Tendsto
        (fun s : ℝ => 2 * π * (s : ℂ) ^ n * AlgebraicAnalytic.laurentCoeff h 0 ρ n) (𝓝[<] r)
        (𝓝 (2 * π * (r : ℂ) ^ n * AlgebraicAnalytic.laurentCoeff h 0 ρ n)) := by
      refine ((tendsto_const_nhds.mul ?_).mul tendsto_const_nhds).mono_left nhdsWithin_le_nhds
      exact ((continuous_ofReal.continuousAt.zpow₀ n (Or.inl hr0))).tendsto
    have hev : (fun s => ∫ θ in (0 : ℝ)..2 * π,
        h (c s * Complex.exp (θ * I)) * Complex.exp (-(n * θ * I))) =ᶠ[𝓝[<] r]
        fun s : ℝ => 2 * π * (s : ℂ) ^ n * AlgebraicAnalytic.laurentCoeff h 0 ρ n := by
      filter_upwards [Ioo_mem_nhdsLT hρr] with s hs using heq s hs
    have huniq := tendsto_nhds_unique (hlim1.congr' hev) hlim2
    simp only [hcr] at huniq
    rw [hΦ]; dsimp only
    rw [huniq]
    have hrn : (r : ℂ) ^ n ≠ 0 := zpow_ne_zero n hr0
    rw [← mul_assoc, inv_mul_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero hpi) hrn), one_mul]
  refine ⟨fun n => by rw [hsubc, key], ?_⟩
  have hRL := tendsto_integral_mul_exp_cofinite fun θ => h (r * Complex.exp (θ * I))
  have hRL' := hRL.const_mul ((2 * π : ℂ)⁻¹)
  rw [mul_zero] at hRL'
  refine hRL'.congr fun n => ?_
  rw [hsubc, key]
  have hrn : (r : ℂ) ^ n ≠ 0 := zpow_ne_zero n hr0
  simp only [hΦ]
  generalize (∫ θ in (0 : ℝ)..2 * π,
    h (r * Complex.exp (θ * I)) * Complex.exp (-(n * θ * I))) = J
  field_simp

/-- DLMF 2.10.30 (Darboux's method with condition (b′)): the conclusion 2.10.29 holds when, on
`|z| = r`, `f - g` has finitely many singularities `z_j` with
`f(z) - g(z) = O((z - z_j)^{σ_j - 1})` as `z → z_j` (`σ_j > 0`), and extends continuously to
the rest of the closed annulus. -/
@[dlmf 2.10.E30, dlmf 2.10.iv]
theorem darboux_singular {f g h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (puncturedDisc r)) (hg : DifferentiableOn ℂ g (puncturedDisc r))
    {Z : Finset ℂ} (hZ : ∀ w ∈ Z, ‖w‖ = r)
    (hh : ContinuousOn h ({z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ r} \ Z))
    (hfg : EqOn h (f - g) (puncturedDisc r)) (σ : ℂ → ℝ) (hσ : ∀ w ∈ Z, 0 < σ w)
    (hsing : ∀ w ∈ Z, (f - g) =O[𝓝[puncturedDisc r] w] fun z => ‖z - w‖ ^ (σ w - 1))
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) :
    Tendsto (fun n : ℤ =>
        (AlgebraicAnalytic.laurentCoeff f 0 ρ n - AlgebraicAnalytic.laurentCoeff g 0 ρ n) *
        (r : ℂ) ^ n) cofinite
      (𝓝 0) := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hpi : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hsH : ∀ w ∈ Z, h =O[𝓝[puncturedDisc r] w]
      (fun z => ‖z - w‖ ^ (σ w - 1)) := by
    intro w hw
    apply (hsing w hw).congr' _ Filter.EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hfg hz).symm
  let c : ℤ → ℂ := fun n => AlgebraicAnalytic.laurentCoeff f 0 ρ n -
    AlgebraicAnalytic.laurentCoeff g 0 ρ n
  let J : ℤ → ℂ := fun n => ∫ θ in (0 : ℝ)..2 * π,
    Complex.CircleSingularities.trace h Z r r θ * Complex.exp (-(n * θ * I))
  have hcoef (n : ℤ) : c n * (r : ℂ) ^ n = (2 * π : ℂ)⁻¹ * J n := by
    have hlim := Complex.CircleSingularities.tendsto_integral_circle_mul_exp hr hZ hh
      σ hσ hsH n (by positivity : (0 : ℝ) ≤ 2 * π)
    have heq : (fun s : ℝ => ∫ θ in (0 : ℝ)..2 * π,
        h (Complex.CircleSingularities.circle s θ) * Complex.exp (-(n * θ * I)))
        =ᶠ[𝓝[<] r] fun s => (2 * π : ℂ) * (s : ℂ) ^ n * c n := by
      filter_upwards [Ioo_mem_nhdsLT hρr] with s hs
      have hs0 : 0 < s := hρ.trans hs.1
      have hd : puncturedDisc s ⊆ puncturedDisc r := fun z hz => ⟨hz.1, hz.2.trans hs.2⟩
      have hc : ContinuousOn h {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ s} := by
        apply hh.mono
        intro z hz
        refine ⟨⟨hz.1, hz.2.trans hs.2.le⟩, ?_⟩
        intro hzZ
        have H := hZ z hzZ
        linarith [hz.2, hs.2]
      have H := (darboux hs0 (hf.mono hd) (hg.mono hd) hc
        (hfg.mono hd) hρ hs.1).1 n
      have hsn : (s : ℂ) ^ n ≠ 0 := zpow_ne_zero n (ofReal_ne_zero.mpr hs0.ne')
      change c n = _ at H
      change _ = (2 * π : ℂ) * (s : ℂ) ^ n * c n
      rw [H]
      dsimp only [Complex.CircleSingularities.circle]
      rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero hpi hsn), one_mul]
    have hrad : Tendsto (fun s : ℝ => (2 * π : ℂ) * (s : ℂ) ^ n * c n) (𝓝[<] r)
        (𝓝 ((2 * π : ℂ) * (r : ℂ) ^ n * c n)) := by
      exact ((tendsto_const_nhds.mul
        ((continuous_ofReal.continuousAt.zpow₀ n (Or.inl hr0)).tendsto)).mul
          tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    have H := tendsto_nhds_unique (hlim.congr' heq) hrad
    change J n = (2 * π : ℂ) * (r : ℂ) ^ n * c n at H
    rw [H]
    field_simp
  have HR := (tendsto_integral_mul_exp_cofinite
    (fun θ => Complex.CircleSingularities.trace h Z r r θ)).const_mul ((2 * π : ℂ)⁻¹)
  simp only [mul_zero] at HR
  exact HR.congr (fun n => (hcoef n).symm)

/-- DLMF 2.10.31: if in addition `θ ↦ h(re^{iθ})` (the boundary values of `f - g`) is `m` times
continuously differentiable, then `f_n = g_n + o(r^{-n} |n|^{-m})` as `n → ±∞`. -/
@[dlmf 2.10.E31]
theorem darboux_smooth {f g h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (puncturedDisc r)) (hg : DifferentiableOn ℂ g (puncturedDisc r))
    (hh : ContinuousOn h {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ r})
    (hfg : EqOn h (f - g) (puncturedDisc r)) {m : ℕ}
    (hm : ContDiff ℝ m fun θ : ℝ => h (r * Complex.exp (θ * I))) {ρ : ℝ} (hρ : 0 < ρ)
    (hρr : ρ < r) :
    Tendsto (fun n : ℤ =>
        (AlgebraicAnalytic.laurentCoeff f 0 ρ n - AlgebraicAnalytic.laurentCoeff g 0 ρ n)
        * (r : ℂ) ^ n *
      ((|n| : ℤ) : ℂ) ^ m) cofinite (𝓝 0) := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  set Ψ : ℝ → ℂ := fun θ => h (r * Complex.exp (θ * I))
  have hper : Function.Periodic Ψ (2 * π) := fun θ => by
    simp only [Ψ]
    congr 2
    rw [show ((θ + 2 * π : ℝ) : ℂ) * I = θ * I + 2 * π * I by push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hJ := (tendsto_integral_mul_exp_cofinite (deriv^[m] Ψ)).norm.const_mul (2 * π)⁻¹
  rw [norm_zero, mul_zero] at hJ
  refine squeeze_zero_norm' ?_ hJ
  filter_upwards [eventually_cofinite_ne 0] with n hn
  rw [(darboux hr hf hg hh hfg hρ hρr).1 n, integral_mul_exp_eq_iterate_deriv hm hper hn le_rfl]
  have hrn : (r : ℂ) ^ n ≠ 0 := zpow_ne_zero n hr0
  have hn' : ((n : ℂ) * I) ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hn) I_ne_zero
  have habs : ‖(((|n| : ℤ) : ℂ))‖ = ‖((n : ℂ) * I)‖ := by
    rw [norm_mul, norm_I, mul_one, norm_intCast, norm_intCast, Int.cast_abs, abs_abs]
  rw [show (2 * π * (r : ℂ) ^ n)⁻¹ * (((n : ℂ) * I)⁻¹ ^ m *
      ∫ θ in (0 : ℝ)..2 * π, deriv^[m] Ψ θ * Complex.exp (-(n * θ * I))) * (r : ℂ) ^ n *
      ((|n| : ℤ) : ℂ) ^ m = (2 * π : ℂ)⁻¹ * (((n : ℂ) * I)⁻¹ ^ m * ((|n| : ℤ) : ℂ) ^ m) *
      ∫ θ in (0 : ℝ)..2 * π, deriv^[m] Ψ θ * Complex.exp (-(n * θ * I)) by
    field_simp]
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, habs, ← mul_pow]
  simp only [norm_inv]
  rw [inv_mul_cancel₀ (norm_ne_zero_iff.2 hn'), one_pow, mul_one, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat]

/-- DLMF 2.10.32: 2.10.31 remains valid when the derivatives of `f - g` of orders `≤ m` extend
continuously to `|z| = r` except at finitely many points `z_j`, near which
`f^{(m)}(z) - g^{(m)}(z) = O((z - z_j)^{σ_j - 1})`, `σ_j > 0`. -/
@[dlmf 2.10.E32]
theorem darboux_smooth_singular {f g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (puncturedDisc r)) (hg : DifferentiableOn ℂ g (puncturedDisc r))
    {Z : Finset ℂ} (hZ : ∀ w ∈ Z, ‖w‖ = r) {m : ℕ}
    (hext : ∀ k ≤ m, ∃ hk : ℂ → ℂ, ContinuousOn hk ({z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ r} \ Z) ∧
      EqOn hk (iteratedDeriv k (f - g)) (puncturedDisc r))
    (σ : ℂ → ℝ) (hσ : ∀ w ∈ Z, 0 < σ w)
    (hsing : ∀ w ∈ Z, iteratedDeriv m (f - g) =O[𝓝[puncturedDisc r] w]
      fun z => ‖z - w‖ ^ (σ w - 1))
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) :
    Tendsto (fun n : ℤ =>
        (AlgebraicAnalytic.laurentCoeff f 0 ρ n - AlgebraicAnalytic.laurentCoeff g 0 ρ n)
        * (r : ℂ) ^ n *
      ((|n| : ℤ) : ℂ) ^ m) cofinite (𝓝 0) := by
  let H : ℂ → ℂ := f - g
  have hH : DifferentiableOn ℂ H (puncturedDisc r) := hf.sub hg
  have hA := DarbouxDerivatives.analyticOnNhd_puncturedDisc hH
  have hDm : DifferentiableOn ℂ (iteratedDeriv m H) (puncturedDisc r) := by
    rw [iteratedDeriv_eq_iterate]
    exact (hA.iterated_deriv m).differentiableOn
  obtain ⟨hmFun, hmCont, hmEq⟩ := hext m le_rfl
  have hEq : EqOn hmFun (iteratedDeriv m H - 0) (puncturedDisc r) := by
    simpa only [sub_zero] using hmEq
  have hSing : ∀ w ∈ Z, (iteratedDeriv m H - 0) =O[𝓝[puncturedDisc r] w]
      (fun z => ‖z - w‖ ^ (σ w - 1)) := by
    simpa only [sub_zero] using hsing
  have hT := darboux_singular hr hDm (differentiableOn_const (c := (0 : ℂ))) hZ
    hmCont hEq σ hσ hSing hρ hρr
  have hZero (k : ℤ) : AlgebraicAnalytic.laurentCoeff (fun _ : ℂ => 0) 0 ρ k = 0 := by
    simp [AlgebraicAnalytic.laurentCoeff, circleIntegral]
  simp only [hZero, sub_zero] at hT
  let c : ℤ → ℂ := fun n => AlgebraicAnalytic.laurentCoeff f 0 ρ n -
    AlgebraicAnalytic.laurentCoeff g 0 ρ n
  let P : ℤ → ℂ := fun n => ∏ j ∈ Finset.range m, ((n : ℂ) - (j : ℂ))
  have hderiv (n : ℤ) : AlgebraicAnalytic.laurentCoeff (iteratedDeriv m H) 0 ρ (n - m) =
      P n * c n := by
    rw [DarbouxDerivatives.laurentCoeff_iteratedDeriv hH hρ hρr,
      DarbouxDerivatives.laurentCoeff_sub hf hg hρ hρr]
  have hshift : Function.Injective (fun n : ℤ => n - (m : ℤ)) := by
    intro n k he
    have H := congrArg (fun z : ℤ => z + (m : ℤ)) he
    simpa only [sub_add_cancel] using H
  have hlim := (hT.comp hshift.tendsto_cofinite).mul_const ((r : ℂ) ^ (m : ℤ))
  simp only [zero_mul] at hlim
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hpoly : Tendsto (fun n : ℤ => P n * (c n * (r : ℂ) ^ n)) cofinite (𝓝 0) := by
    apply hlim.congr
    intro n
    simp only [Function.comp_apply]
    rw [hderiv, zpow_sub₀ hr0]
    field_simp
  have hbound := hpoly.norm.const_mul ((2 : ℝ) ^ m)
  simp only [norm_zero, mul_zero] at hbound
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [Complex.eventually_norm_int_pow_le_prod_sub m] with n hn
  change ‖c n * (r : ℂ) ^ n * ((|n| : ℤ) : ℂ) ^ m‖ ≤
    (2 : ℝ) ^ m * ‖P n * (c n * (r : ℂ) ^ n)‖
  have hnorm : ‖((|n| : ℤ) : ℂ)‖ = ‖(n : ℂ)‖ := by
    rw [norm_intCast, norm_intCast, Int.cast_abs, abs_abs]
  rw [norm_mul, norm_pow, hnorm]
  calc _ ≤ ‖c n * (r : ℂ) ^ n‖ * ((2 : ℝ) ^ m * ‖P n‖) :=
      mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = _ := by simp only [norm_mul]; ring

/-! ### Example: Legendre polynomials of large degree (2.10.33–2.10.36) -/

/-- DLMF 2.10.33: `(1 - 2z cos α + z²)^{-1/2} = ∑ P_n(cos α) zⁿ` for `|z| < 1` and real `α`
(principal power). Corollary of the project's generating function 18.12.11. -/
@[dlmf 2.10.E33]
theorem legendre_generating_cos (α : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => DLMF.OrthogonalPolynomials.legendrePolynomialP n (Real.cos α) * z ^ n)
      ((1 - 2 * (Real.cos α : ℂ) * z + z ^ 2) ^ (-1 / 2 : ℂ)) :=
  DLMF.OrthogonalPolynomials.legendre_generating_function (Real.abs_cos_le_one α) hz

/-- `(1/2)ₙ/n! = Γ(n + 1/2)/(√π n!)`. -/
private lemma pochhammer_half_div_factorial (n : ℕ) :
    DLMF.Hypergeometric.pochhammer (1 / 2) n / n ! =
      ((Real.Gamma (n + 1 / 2) / Real.sqrt π / n ! : ℝ) : ℂ) := by
  have h := DLMF.Hypergeometric.Gamma_add_nat_eq_pochhammer_mul_Gamma (α := (1 / 2 : ℂ))
    (by norm_num) n
  have hG : Complex.Gamma (1 / 2) = (Real.sqrt π : ℂ) := by
    rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]
    norm_num
  have hs : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 Real.pi_pos).ne'
  rw [hG] at h
  have hc : Complex.Gamma (1 / 2 + n) = ((Real.Gamma (n + 1 / 2) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  rw [hc] at h
  push_cast
  rw [h]
  field_simp

/-- DLMF 2.10.35: for `0 < α < π` the comparison function 2.10.34 has the Maclaurin
coefficients `g_n = (2/(π sin α))^{1/2} Γ(n + 1/2)/n! cos(nα + α/2 - π/4)`, `|z| < 1`.
DLMF states the example for `α ∈ (0, 2π)`; the formula needs `α ∈ (0, π)`. -/
@[dlmf 2.10.E35 "corrected: α ∈ (0, π), not (0, 2π)", dlmf 2.10.E34]
theorem legendreComparison_hasSum {α : ℝ} (hα : α ∈ Ioo 0 π) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (((2 / (π * Real.sin α)) ^ (1 / 2 : ℝ) *
        Real.Gamma (n + 1 / 2) / n.factorial * Real.cos (n * α + α / 2 - π / 4) : ℝ) : ℂ) *
        z ^ n)
      (legendreComparison α z) := by
  have hsin : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2
  set K : ℝ := (2 * Real.sin α) ^ (-(1 / 2 : ℝ))
  have hnorm : ∀ t : ℝ, ‖z * Complex.exp (t * I)‖ < 1 := fun t => by
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]; exact hz
  have h1 := DLMF.Hypergeometric.hasSum_one_sub_cpow_neg (1 / 2) (z := z * Complex.exp (I * α))
    (by rw [mul_comm I]; exact hnorm α)
  have h2 := DLMF.Hypergeometric.hasSum_one_sub_cpow_neg (1 / 2)
    (z := z * Complex.exp (-(I * α))) (by rw [← mul_neg, mul_comm I, ← ofReal_neg]; exact hnorm _)
  have h := (h1.mul_left (Complex.exp (-(π * I / 4)) * (K : ℂ) * Complex.exp (I * α / 2))).add
    (h2.mul_left (Complex.exp (π * I / 4) * (K : ℂ) * Complex.exp (-(I * α / 2))))
  unfold legendreComparison
  convert h using 1
  · funext n
    rw [mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    have hc := pochhammer_half_div_factorial n
    -- coefficient identity
    have hK : ((2 / (π * Real.sin α)) ^ (1 / 2 : ℝ) : ℝ) = 2 * K / Real.sqrt π := by
      simp only [K]
      rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
        Real.sqrt_div' _ (by positivity), Real.sqrt_mul' _ hsin.le,
        Real.sqrt_mul' _ hsin.le]
      have h2 : Real.sqrt 2 ≠ 0 := by positivity
      have hp : Real.sqrt π ≠ 0 := by positivity
      have hs : Real.sqrt (Real.sin α) ≠ 0 := (Real.sqrt_pos.2 hsin).ne'
      field_simp
      rw [Real.sq_sqrt (by norm_num)]
    have hcos := Complex.two_cos (((n * α + α / 2 - π / 4 : ℝ)) : ℂ)
    have e1 : Complex.exp (-(π * I / 4)) * Complex.exp (I * α / 2) * Complex.exp (n * (I * α)) =
        Complex.exp (((n * α + α / 2 - π / 4 : ℝ)) * I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    have e2 : Complex.exp (π * I / 4) * Complex.exp (-(I * α / 2)) *
        Complex.exp (n * (-(I * α))) = Complex.exp (-((n * α + α / 2 - π / 4 : ℝ)) * I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    rw [hc]
    set c : ℝ := Real.Gamma (n + 1 / 2) / Real.sqrt π / (n ! : ℝ)
    have hR : Complex.exp (-(π * I / 4)) * (K : ℂ) * Complex.exp (I * α / 2) *
        ((c : ℂ) * (z ^ n * Complex.exp (n * (I * α)))) +
        Complex.exp (π * I / 4) * (K : ℂ) * Complex.exp (-(I * α / 2)) *
        ((c : ℂ) * (z ^ n * Complex.exp (n * (-(I * α))))) =
        (K : ℂ) * c * z ^ n * (Complex.exp (-(π * I / 4)) * Complex.exp (I * α / 2) *
          Complex.exp (n * (I * α)) + Complex.exp (π * I / 4) * Complex.exp (-(I * α / 2)) *
          Complex.exp (n * (-(I * α)))) := by ring
    rw [hR, e1, e2, ← hcos, hK]
    simp only [c]
    push_cast
    ring
  · ring

/-- DLMF 2.10.36: for `0 < α < π`,
`P_n(cos α) = (2/(πn sin α))^{1/2} cos(nα + α/2 - π/4) + o(n^{-1})` as `n → ∞`.
DLMF states the example for `α ∈ (0, 2π)`; for `π < α < 2π` the right side is not real. -/
@[dlmf 2.10.E36 "corrected: α ∈ (0, π), not (0, 2π)", dlmf 2.10.iv]
theorem legendrePolynomialP_cos_asymptotic {α : ℝ} (hα : α ∈ Ioo 0 π) :
    Tendsto (fun n : ℕ => (n : ℝ) * ‖DLMF.OrthogonalPolynomials.legendrePolynomialP n (Real.cos α) -
      (((2 / (π * n * Real.sin α)) ^ (1 / 2 : ℝ) *
        Real.cos (n * α + α / 2 - π / 4) : ℝ) : ℂ)‖) atTop (𝓝 0) := by
  let F := LegendreDarboux.generatingFunction α
  let G := LegendreDarboux.rootComparison α
  let u := exp (-(I * α))
  let v := exp (I * α)
  let Z : Finset ℂ := {u, v}
  have hu : ‖u‖ = 1 := by
    simpa only [u, ← mul_neg, ← ofReal_neg] using LegendreDarboux.norm_phase (-α)
  have hv : ‖v‖ = 1 := LegendreDarboux.norm_phase α
  have huv : u ≠ v := (LegendreDarboux.phase_ne_neg_phase hα).symm
  have hZ : ∀ w ∈ Z, ‖w‖ = 1 := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hu
    · rw [Finset.mem_singleton] at hw
      simpa only [hw] using hv
  have hroots {z : ℂ} (hz : ‖z‖ < 1) : z ≠ u ∧ z ≠ v := by
    constructor <;> intro he <;> subst z <;> linarith
  have hF {z : ℂ} (hz : ‖z‖ ≤ 1) (hzu : z ≠ u) (hzv : z ≠ v) : AnalyticAt ℂ F z :=
    LegendreDarboux.analyticAt_generatingFunction α hz hzu hzv
  have hG {z : ℂ} (hz : ‖z‖ ≤ 1) (hzu : z ≠ u) (hzv : z ≠ v) : AnalyticAt ℂ G z :=
    LegendreDarboux.analyticAt_rootComparison α hz hzu hzv
  have hFd : DifferentiableOn ℂ F (puncturedDisc 1) := by
    intro z hz
    exact (hF hz.2.le (hroots hz.2).1 (hroots hz.2).2).differentiableAt.differentiableWithinAt
  have hGd : DifferentiableOn ℂ G (puncturedDisc 1) := by
    intro z hz
    exact (hG hz.2.le (hroots hz.2).1 (hroots hz.2).2).differentiableAt.differentiableWithinAt
  have hext : ∀ k ≤ (1 : ℕ), ∃ hk : ℂ → ℂ,
      ContinuousOn hk ({z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ 1} \ Z) ∧
        EqOn hk (iteratedDeriv k (F - G)) (puncturedDisc 1) := by
    intro k hk
    refine ⟨iteratedDeriv k (F - G), ?_, fun _ _ => rfl⟩
    intro z hz
    have hzu : z ≠ u := fun he => hz.2 (by simp [Z, he])
    have hzv : z ≠ v := fun he => hz.2 (by simp [Z, he])
    rw [iteratedDeriv_eq_iterate]
    exact ((hF hz.1.2 hzu hzv).sub (hG hz.1.2 hzu hzv)).iterated_deriv k
      |>.continuousAt.continuousWithinAt
  have hsing : ∀ w ∈ Z, iteratedDeriv 1 (F - G) =O[𝓝[puncturedDisc 1] w]
      fun z => ‖z - w‖ ^ ((1 / 2 : ℝ) - 1) := by
    intro w hw
    rw [iteratedDeriv_one]
    norm_num only [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact LegendreDarboux.isBigO_deriv_sub_rootComparison α huv
    · rw [Finset.mem_singleton] at hw
      subst w
      exact LegendreDarboux.isBigO_deriv_sub_rootComparison_pos α huv
  have hD := darboux_smooth_singular (f := F) (g := G) (r := 1) (by norm_num)
    hFd hGd hZ hext (fun _ => (1 / 2 : ℝ)) (by intro w hw; norm_num) hsing
    (ρ := 1 / 2) (by norm_num) (by norm_num)
  have hFc : DifferentiableOn ℂ F (closedBall (0 : ℂ) (1 / 2)) := by
    intro z hz
    have hz1 : ‖z‖ < 1 := by
      rw [mem_closedBall, dist_zero_right] at hz
      linarith
    exact (hF hz1.le (hroots hz1).1 (hroots hz1).2).differentiableAt.differentiableWithinAt
  have hGc : DifferentiableOn ℂ G (closedBall (0 : ℂ) (1 / 2)) := by
    intro z hz
    have hz1 : ‖z‖ < 1 := by
      rw [mem_closedBall, dist_zero_right] at hz
      linarith
    exact (hG hz1.le (hroots hz1).1 (hroots hz1).2).differentiableAt.differentiableWithinAt
  let K : ℝ := (2 / (π * Real.sin α)) ^ (1 / 2 : ℝ)
  let c : ℕ → ℂ := fun n => ((K * Real.Gamma (n + 1 / 2) / n.factorial *
    Real.cos (n * α + α / 2 - π / 4) : ℝ) : ℂ)
  have hcf : ∀ n : ℕ, AlgebraicAnalytic.laurentCoeff F 0 (1 / 2) n =
      DLMF.OrthogonalPolynomials.legendrePolynomialP n (Real.cos α) := by
    intro n
    apply Complex.circleIntegral_mul_zpow_neg_nat_eq (by norm_num) hFc
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
    simpa only [zero_add] using LegendreDarboux.hasSum_generatingFunction α
      (by simpa only [mem_ball, dist_zero_right] using hz)
  have hcg : ∀ n : ℕ, AlgebraicAnalytic.laurentCoeff G 0 (1 / 2) n = c n := by
    intro n
    apply Complex.circleIntegral_mul_zpow_neg_nat_eq (by norm_num) hGc
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
    have hh := legendreComparison_hasSum hα (by simpa only [mem_ball, dist_zero_right] using hz)
    rw [LegendreDarboux.legendreComparison_eq_rootComparison hα] at hh
    simpa only [zero_add] using hh
  have hN := hD.comp ((tendsto_natCast_atTop_atTop (R := ℤ)).mono_right atTop_le_cofinite)
  have hN' : Tendsto (fun n : ℕ =>
      (DLMF.OrthogonalPolynomials.legendrePolynomialP n (Real.cos α) - c n) * (n : ℂ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_one, hcf, hcg, one_zpow, mul_one, pow_one,
      abs_of_nonneg (Int.natCast_nonneg _), Int.cast_natCast] using hN
  have hPc : Tendsto (fun n : ℕ => (n : ℝ) *
      ‖DLMF.OrthogonalPolynomials.legendrePolynomialP n (Real.cos α) - c n‖) atTop (𝓝 0) := by
    simpa only [norm_zero, Function.comp_def, norm_mul, Complex.norm_natCast, mul_comm] using
      continuous_norm.tendsto (0 : ℂ) |>.comp hN'
  have hsin : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2
  have hK : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  have hΓ : Tendsto (fun n : ℕ => (n : ℝ) *
      |Real.Gamma (n + 1 / 2) / n.factorial - (n : ℝ) ^ (-(1 / 2) : ℝ)|) atTop (𝓝 0) := by
    have hh := LegendreDarboux.tendsto_nat_mul_gammaRatio_error
    convert hh using 1
    ext n
    have hGN : Gamma ((n : ℂ) + 1 / 2) = ((Real.Gamma (n + 1 / 2) : ℝ) : ℂ) := by
      rw [← Gamma_ofReal]
      push_cast
      ring_nf
    have hpn : (((n : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) = (n : ℂ) ^ (-(1 / 2) : ℂ) := by
      rw [ofReal_cpow (Nat.cast_nonneg n)]
      norm_num
    rw [hGN, Gamma_nat_eq_factorial, ← hpn, ← ofReal_natCast, ← ofReal_div,
      ← ofReal_sub, norm_real, Real.norm_eq_abs]
  let l : ℕ → ℂ := fun n => ((K * (n : ℝ) ^ (-(1 / 2) : ℝ) *
    Real.cos (n * α + α / 2 - π / 4) : ℝ) : ℂ)
  have hcl : Tendsto (fun n : ℕ => (n : ℝ) * ‖c n - l n‖) atTop (𝓝 0) := by
    have hb : ∀ n : ℕ, ‖c n - l n‖ ≤ K *
        |Real.Gamma (n + 1 / 2) / n.factorial - (n : ℝ) ^ (-(1 / 2) : ℝ)| := by
      intro n
      have he : c n - l n = ((K *
          (Real.Gamma (n + 1 / 2) / n.factorial - (n : ℝ) ^ (-(1 / 2) : ℝ)) *
          Real.cos (n * α + α / 2 - π / 4) : ℝ) : ℂ) := by
        dsimp [c, l]
        push_cast
        ring
      rw [he, norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hK]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
    have hlim : Tendsto (fun n : ℕ => K * ((n : ℝ) *
        |Real.Gamma (n + 1 / 2) / n.factorial - (n : ℝ) ^ (-(1 / 2) : ℝ)|))
        atTop (𝓝 0) := by simpa only [mul_zero] using hΓ.const_mul K
    refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hlim
    exact Eventually.of_forall fun n => by
      simpa only [mul_left_comm (n : ℝ) K] using
        mul_le_mul_of_nonneg_left (hb n) (Nat.cast_nonneg n)
  have ht := hPc.add hcl
  simp only [zero_add] at ht
  refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ ht
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : (2 / (π * n * Real.sin α)) ^ (1 / 2 : ℝ) =
      K * (n : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [show 2 / (π * n * Real.sin α) = (2 / (π * Real.sin α)) / n by ring,
      ← Real.sqrt_eq_rpow, Real.sqrt_div (by positivity), Real.rpow_neg hnr.le,
      ← Real.sqrt_eq_rpow]
    dsimp [K]
    rw [← Real.sqrt_eq_rpow]
    ring
  rw [hs]
  change (n : ℝ) * ‖DLMF.OrthogonalPolynomials.legendrePolynomialP n (Real.cos α) - l n‖ ≤ _
  have hb : ‖DLMF.OrthogonalPolynomials.legendrePolynomialP n (Real.cos α) - l n‖ ≤
      ‖DLMF.OrthogonalPolynomials.legendrePolynomialP n (Real.cos α) - c n‖ + ‖c n - l n‖ := by
    simpa only [dist_eq_norm] using
      dist_triangle (DLMF.OrthogonalPolynomials.legendrePolynomialP n (Real.cos α)) (c n) (l n)
  simpa only [mul_add] using mul_le_mul_of_nonneg_left hb hnr.le

end DLMF.AsymptoticApproximations
