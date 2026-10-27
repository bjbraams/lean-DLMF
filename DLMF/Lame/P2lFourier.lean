/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.Eigenvalues
public import DLMF.Legendre.AdditionTools

/-!
# Fourier series of `C²` periodic functions, for the Lamé expansions of §29.6

Real cosine and sine series of an even (odd), `2π`-periodic `C²` function, with coefficients
`(2/π) ∫₀^π F(t) cos(nt) dt` (resp. `sin`), from the exponential series of
`DLMF.Legendre.legAdd_hasSum_cos` and the coefficient decay `DLMF.Legendre.legAdd_coeff_bound`
(Mathlib's `has_pointwise_sum_fourier_series_of_summable`).
-/

@[expose] public section

open Complex Filter Set MeasureTheory
open scoped Real Topology

noncomputable section

namespace DLMF.Lame

open DLMF.Legendre DLMF.Elliptic DLMF.JacobiElliptic

/-- The paired exponential Fourier series of a `2π`-periodic `C²` function. -/
lemma p2l_hasSum_exp_pair {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hper : Function.Periodic f (2 * π)) (u : ℝ) :
    HasSum (fun n : ℕ => legAdd_coeff f n * exp (n * u * I) +
      legAdd_coeff f (-(n : ℤ)) * exp (-(n * u * I))) (f u + legAdd_coeff f 0) := by
  have : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
  let g : C(AddCircle (2 * π), ℂ) := ⟨hper.lift, continuous_coinduced_dom.mpr hf.continuous⟩
  have hgx : ∀ x : ℝ, g (x : AddCircle (2 * π)) = f x := fun x => rfl
  have hgc : ∀ n : ℤ, fourierCoeff g n = legAdd_coeff f n := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral _ n (-π), show -π + 2 * π = π by ring, legAdd_coeff,
      Complex.real_smul]
    congr 1
    · push_cast; ring
    · refine intervalIntegral.integral_congr fun x _ => ?_
      rw [fourier_coe_apply, hgx, smul_eq_mul]
      congr 2
      push_cast
      field_simp
  obtain ⟨M, hM0, hM⟩ := legAdd_coeff_bound hf hper
  have hsum : Summable (fourierCoeff g) := by
    refine Summable.of_norm_bounded_eventually (g := fun n : ℤ => M * (1 / (n : ℝ) ^ 2))
      ((Real.summable_one_div_int_pow.mpr (by norm_num)).mul_left M) ?_
    have : {n : ℤ | n ≠ 0} ∈ Filter.cofinite := by
      simp only [Filter.mem_cofinite, ne_eq]
      convert Set.finite_singleton (0 : ℤ) using 1
      ext n; simp
    filter_upwards [this] with n hn
    rw [hgc, mul_one_div]
    exact hM n hn
  have hp := (has_pointwise_sum_fourier_series_of_summable hsum
    (u : AddCircle (2 * π))).nat_add_neg
  convert hp using 1
  · funext n
    rw [hgc, hgc, fourier_coe_apply, fourier_coe_apply, smul_eq_mul, smul_eq_mul]
    congr 2
    · congr 1; push_cast; field_simp
    · congr 1; push_cast; field_simp
  · rw [hgx, hgc, fourier_zero, smul_eq_mul, mul_one]

/-- Integral over `[-π, π]` as an integral over `[0, π]`. -/
lemma p2l_integral_symm {g : ℝ → ℂ} (hg : Continuous g) :
    ∫ t in (-π)..π, g t = ∫ t in (0 : ℝ)..π, (g (-t) + g t) := by
  have h1 : ∫ t in (-π)..0, g t = ∫ t in (0 : ℝ)..π, g (-t) := by
    rw [intervalIntegral.integral_comp_neg]; simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hg.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _), h1]
  exact (intervalIntegral.integral_add ((hg.comp continuous_neg).intervalIntegrable _ _)
    (hg.intervalIntegrable _ _)).symm

/-- The coefficients of an even real function. -/
lemma p2l_coeff_even {F : ℝ → ℝ} (hF : Continuous F) (hev : ∀ t, F (-t) = F t) (n : ℤ) :
    legAdd_coeff (fun t => (F t : ℂ)) n =
      ((1 / π * ∫ t in (0 : ℝ)..π, F t * Real.cos (n * t) : ℝ) : ℂ) := by
  have hc : Continuous fun t : ℝ => exp (-(n * (t : ℂ) * I)) * (F t : ℂ) := by fun_prop
  rw [legAdd_coeff, p2l_integral_symm hc]
  have key : ∀ t : ℝ, exp (-(n * ((-t : ℝ) : ℂ) * I)) * ((F (-t) : ℝ) : ℂ) +
      exp (-(n * (t : ℂ) * I)) * (F t : ℂ) = 2 * ((F t * Real.cos (n * t) : ℝ) : ℂ) := by
    intro t
    rw [hev, ofReal_mul, ofReal_cos, Complex.cos]
    push_cast; ring_nf
  rw [intervalIntegral.integral_congr (fun t _ => key t), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal]
  push_cast
  field_simp

/-- The coefficients of an odd real function. -/
lemma p2l_coeff_odd {F : ℝ → ℝ} (hF : Continuous F) (hodd : ∀ t, F (-t) = -F t) (n : ℤ) :
    legAdd_coeff (fun t => (F t : ℂ)) n =
      -I * ((1 / π * ∫ t in (0 : ℝ)..π, F t * Real.sin (n * t) : ℝ) : ℂ) := by
  have hc : Continuous fun t : ℝ => exp (-(n * (t : ℂ) * I)) * (F t : ℂ) := by fun_prop
  rw [legAdd_coeff, p2l_integral_symm hc]
  have key : ∀ t : ℝ, exp (-(n * ((-t : ℝ) : ℂ) * I)) * ((F (-t) : ℝ) : ℂ) +
      exp (-(n * (t : ℂ) * I)) * (F t : ℂ) = (-2 * I) * ((F t * Real.sin (n * t) : ℝ) : ℂ) := by
    intro t
    rw [hodd, ofReal_neg, ofReal_mul, ofReal_sin, Complex.sin]
    push_cast
    ring_nf
    rw [I_sq]; ring
  rw [intervalIntegral.integral_congr (fun t _ => key t), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal]
  push_cast
  field_simp

/-- **Cosine series** of an even, `2π`-periodic `C²` real function, with coefficients
`(2/π) ∫₀^π F(t) cos(nt) dt` (the zeroth term halved). -/
theorem p2l_hasSum_cos {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hper : Function.Periodic F (2 * π))
    (hev : ∀ t, F (-t) = F t) (u : ℝ) :
    HasSum (fun n : ℕ => (if n = 0 then 1 / 2 else 1) *
      (2 / π * ∫ t in (0 : ℝ)..π, F t * Real.cos (n * t)) * Real.cos (n * u)) (F u) := by
  have hf : ContDiff ℝ 2 (fun t => (F t : ℂ)) := ofRealCLM.contDiff.comp hF
  have hp := p2l_hasSum_exp_pair hf (fun t => by simp [hper t]) u
  have h0 := hasSum_ite_eq (0 : ℕ) (legAdd_coeff (fun t => (F t : ℂ)) 0)
  have hd := hp.sub h0
  rw [add_sub_cancel_right] at hd
  rw [← hasSum_ofReal]
  convert hd using 1
  funext n
  have e1 := p2l_coeff_even hF.continuous hev n
  have e2 := p2l_coeff_even hF.continuous hev (-(n : ℤ))
  simp only [Int.cast_neg, Int.cast_natCast, neg_mul, Real.cos_neg] at e1 e2
  split_ifs with hn
  · subst hn
    simp only [zero_mul, Real.cos_zero, mul_one, neg_zero,
      Complex.exp_zero, CharP.cast_eq_zero] at e1 ⊢
    rw [e1]
    push_cast
    ring
  · rw [e1, e2]
    generalize (∫ t in (0 : ℝ)..π, F t * Real.cos (n * t)) = A
    have hc : exp ((n : ℂ) * u * I) + exp (-((n : ℂ) * u * I)) = 2 * Real.cos (n * u) := by
      rw [ofReal_cos, Complex.cos]; push_cast; ring_nf
    push_cast at hc ⊢
    linear_combination (-(1 / (π : ℂ)) * (A : ℂ)) * hc

/-- **Sine series** of an odd, `2π`-periodic `C²` real function, with coefficients
`(2/π) ∫₀^π F(t) sin(nt) dt`. -/
lemma p2l_hasSum_sin {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hper : Function.Periodic F (2 * π))
    (hodd : ∀ t, F (-t) = -F t) (u : ℝ) :
    HasSum (fun n : ℕ =>
      (2 / π * ∫ t in (0 : ℝ)..π, F t * Real.sin (n * t)) * Real.sin (n * u)) (F u) := by
  have hf : ContDiff ℝ 2 (fun t => (F t : ℂ)) := ofRealCLM.contDiff.comp hF
  have hp := p2l_hasSum_exp_pair hf (fun t => by simp [hper t]) u
  rw [p2l_coeff_odd hF.continuous hodd 0] at hp
  simp only [Int.cast_zero, zero_mul, Real.sin_zero, mul_zero, intervalIntegral.integral_zero,
    ofReal_zero, add_zero] at hp
  rw [← hasSum_ofReal]
  convert hp using 1
  funext n
  have e1 := p2l_coeff_odd hF.continuous hodd n
  have e2 := p2l_coeff_odd hF.continuous hodd (-(n : ℤ))
  simp only [Int.cast_neg, Int.cast_natCast, neg_mul, Real.sin_neg, mul_neg,
    intervalIntegral.integral_neg] at e1 e2
  rw [e1, e2]
  generalize (∫ t in (0 : ℝ)..π, F t * Real.sin (n * t)) = A
  have hs : exp ((n : ℂ) * u * I) - exp (-((n : ℂ) * u * I)) = 2 * I * Real.sin (n * u) := by
    rw [ofReal_sin, Complex.sin]; push_cast; field_simp; ring_nf; rw [I_sq]; ring_nf
  push_cast at hs ⊢
  linear_combination (I * (1 / (π : ℂ)) * A) * hs +
    (2 / (π : ℂ) * A * Complex.sin (n * u)) * I_sq

/-! ### The Lamé functions as functions of `φ = π/2 - am(x, k)` -/

section Lame

variable {k : ℝ}

/-- `dφ/dx = -dn(x, k)` (moved here from `DLMF.Lame.FourierSeries`). -/
theorem p1l_hasDerivAt_phi (hk : k ^ 2 < 1) (x : ℝ) :
    HasDerivAt (fun x => Real.lamePhi x k) (-Real.jacobiDnm x (k ^ 2)) x := by
  have := (Real.hasDerivAt_jacobiAmm hk x).const_sub (π / 2)
  simpa [Real.lamePhi, Real.jacobiDnm, Real.jacobiSnm] using this

/-- The weight `ρ(φ) = 1` (`weighted`) or `dn = (1 - k² cos²φ)^{1/2}` in the variable `φ`. -/
def p2lRho (k : ℝ) (weighted : Bool) (φ : ℝ) : ℝ :=
  if weighted then 1 else (1 - k ^ 2 * Real.cos φ ^ 2) ^ (1 / 2 : ℝ)

/-- A real function `w(x)` divided by the weight, as a function of `φ`:
`F(φ) = w(F(π/2 - φ | k²)) / ρ(φ)`, so that `F(φ(x)) = w(x)/ρ`. -/
def p2lPhiFun (w : ℝ → ℝ) (k : ℝ) (weighted : Bool) (φ : ℝ) : ℝ :=
  w (Real.incEllIntFm (π / 2 - φ) (k ^ 2)) / p2lRho k weighted φ

theorem p2l_one_sub_pos (hk : k ^ 2 < 1) (φ : ℝ) : 0 < 1 - k ^ 2 * Real.cos φ ^ 2 := by
  have := Real.cos_sq_le_one φ
  nlinarith [sq_nonneg k, sq_nonneg (Real.cos φ)]

theorem p2lRho_pos (hk : k ^ 2 < 1) (weighted : Bool) (φ : ℝ) : 0 < p2lRho k weighted φ := by
  unfold p2lRho; split_ifs
  · exact one_pos
  · exact Real.rpow_pos_of_pos (p2l_one_sub_pos hk φ) _

lemma p2l_contDiff_rho (hk : k ^ 2 < 1) (weighted : Bool) : ContDiff ℝ 2 (p2lRho k weighted) := by
  unfold p2lRho; cases weighted
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (contDiff_const.sub (contDiff_const.mul (Real.contDiff_cos.pow 2))).rpow_const_of_ne
      fun φ => (p2l_one_sub_pos hk φ).ne'
  · simpa using contDiff_const

lemma p2l_contDiff_incEllIntFm (hk : k ^ 2 < 1) :
    ContDiff ℝ 2 (fun ψ => Real.incEllIntFm ψ (k ^ 2)) := by
  have hd : deriv (fun ψ => Real.incEllIntFm ψ (k ^ 2)) =
      fun ψ => (1 - k ^ 2 * Real.sin ψ ^ 2) ^ (-(1 / 2) : ℝ) :=
    funext fun ψ => (Real.hasDerivAt_incEllIntFm hk ψ).deriv
  have hpos : ∀ ψ, 0 < 1 - k ^ 2 * Real.sin ψ ^ 2 := fun ψ => by
    have := Real.sin_sq_le_one ψ
    nlinarith [sq_nonneg k, sq_nonneg (Real.sin ψ)]
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun ψ => (Real.hasDerivAt_incEllIntFm hk ψ).differentiableAt, by simp, ?_⟩
  rw [hd]
  exact (contDiff_const.sub (contDiff_const.mul (Real.contDiff_sin.pow 2))).rpow_const_of_ne
    fun ψ => (hpos ψ).ne'

/-- A solution of Lamé's equation is `C²`. -/
theorem p2l_contDiff_lame {h ν : ℝ} {w : ℝ → ℝ} (hk : k ^ 2 < 1) (hw : Real.IsLameSolution h ν k w) :
    ContDiff ℝ 2 w := by
  have hdd : deriv (deriv w) =
      fun x => -(h - ν * (ν + 1) * k ^ 2 * Real.jacobiSnm x (k ^ 2) ^ 2) * w x :=
    funext fun x => (hw.hasDerivAt_deriv x).deriv
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨hw.differentiable, by simp, ?_⟩
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (hw.hasDerivAt_deriv x).differentiableAt, ?_⟩
  rw [hdd]
  exact ((continuous_const.sub (continuous_const.mul ((l29_continuous_sn hk).pow 2))).neg).mul
    hw.differentiable.continuous

variable {w : ℝ → ℝ} {weighted : Bool}

lemma p2lPhiFun_contDiff (hk : k ^ 2 < 1) (hw : ContDiff ℝ 2 w) :
    ContDiff ℝ 2 (p2lPhiFun w k weighted) :=
  (hw.comp ((p2l_contDiff_incEllIntFm hk).comp (contDiff_const.sub contDiff_id))).div
    (p2l_contDiff_rho hk weighted) fun φ => (p2lRho_pos hk weighted φ).ne'

lemma p2l_incEllIntFm_sub_two_pi (hk : k ^ 2 < 1) (ψ : ℝ) :
    Real.incEllIntFm (ψ - 2 * π) (k ^ 2) =
      Real.incEllIntFm ψ (k ^ 2) - 4 * Real.compEllIntKm (k ^ 2) := by
  have h1 := Real.incEllIntFm_add_pi hk (ψ - 2 * π)
  have h2 := Real.incEllIntFm_add_pi hk (ψ - 2 * π + π)
  rw [show ψ - 2 * π + π + π = ψ by ring] at h2
  linarith

lemma p2lRho_neg (φ : ℝ) : p2lRho k weighted (-φ) = p2lRho k weighted φ := by
  simp [p2lRho, Real.cos_neg]

lemma p2lRho_pi_sub (φ : ℝ) : p2lRho k weighted (π - φ) = p2lRho k weighted φ := by
  simp [p2lRho, Real.cos_pi_sub]

lemma p2lRho_add_two_pi (φ : ℝ) : p2lRho k weighted (φ + 2 * π) = p2lRho k weighted φ := by
  simp [p2lRho, Real.cos_add_two_pi]

theorem p2lPhiFun_periodic (hk : k ^ 2 < 1)
    (h4 : ∀ x, w (x + 4 * Real.compEllIntKm (k ^ 2)) = w x) :
    Function.Periodic (p2lPhiFun w k weighted) (2 * π) := fun φ => by
  simp only [p2lPhiFun, p2lRho_add_two_pi]
  rw [show π / 2 - (φ + 2 * π) = (π / 2 - φ) - 2 * π by ring, p2l_incEllIntFm_sub_two_pi hk]
  congr 1
  have := h4 (Real.incEllIntFm (π / 2 - φ) (k ^ 2) - 4 * Real.compEllIntKm (k ^ 2))
  rw [sub_add_cancel] at this
  exact this.symm

theorem p2lPhiFun_neg (hk : k ^ 2 < 1) {σ : ℝ}
    (hσ : ∀ x, w (2 * Real.compEllIntKm (k ^ 2) - x) = σ * w x) (φ : ℝ) :
    p2lPhiFun w k weighted (-φ) = σ * p2lPhiFun w k weighted φ := by
  simp only [p2lPhiFun, p2lRho_neg]
  have : Real.incEllIntFm (π / 2 - -φ) (k ^ 2) =
      2 * Real.compEllIntKm (k ^ 2) - Real.incEllIntFm (π / 2 - φ) (k ^ 2) := by
    rw [show π / 2 - -φ = -(π / 2 - φ) + π by ring, Real.incEllIntFm_add_pi hk,
      Real.incEllIntFm_neg]
    ring
  rw [this, hσ, mul_div_assoc]

lemma p2lPhiFun_pi_sub {δ : ℝ} (hδ : ∀ x, w (-x) = δ * w x) (φ : ℝ) :
    p2lPhiFun w k weighted (π - φ) = δ * p2lPhiFun w k weighted φ := by
  simp only [p2lPhiFun, p2lRho_pi_sub]
  rw [show π / 2 - (π - φ) = -(π / 2 - φ) by ring, Real.incEllIntFm_neg, hδ, mul_div_assoc]

theorem p2l_lamePhi_cos (x : ℝ) : Real.cos (Real.lamePhi x k) = Real.jacobiSnm x (k ^ 2) := by
  simp [Real.lamePhi, Real.cos_pi_div_two_sub, Real.jacobiSnm]

lemma p2lRho_lamePhi (x : ℝ) :
    p2lRho k weighted (Real.lamePhi x k) =
      if weighted then 1 else Real.jacobiDnm x (k ^ 2) := by
  simp [p2lRho, p2l_lamePhi_cos, Real.jacobiDnm]

lemma p2lPhiFun_lamePhi (hk : k ^ 2 < 1) (x : ℝ) :
    p2lPhiFun w k weighted (Real.lamePhi x k) =
      w x / (if weighted then 1 else Real.jacobiDnm x (k ^ 2)) := by
  rw [p2lPhiFun, p2lRho_lamePhi]
  congr 2
  rw [Real.lamePhi, sub_sub_cancel, Real.incEllIntFm_jacobiAmm hk]

/-- The Fourier integrals of `DLMF.Lame.Basic` in the variable `φ`:
`∫₀^K w(x) τ(φ(x)) ρ(x) dx = ∫₀^{π/2} F(t) τ(t) dt`. -/
lemma p2l_integral_lamePhi (hk0 : 0 < k) (hk1 : k < 1) (hw : Continuous w) {τ : ℝ → ℝ}
    (hτ : Continuous τ) :
    ∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
      w x * τ (Real.lamePhi x k) * (if weighted then Real.jacobiDnm x (k ^ 2) else 1) =
      ∫ t in (0 : ℝ)..π / 2, p2lPhiFun w k weighted t * τ t := by
  have hk := l29_sq_lt_one hk0 hk1
  have hF : Continuous (p2lPhiFun w k weighted) :=
    (hw.comp (((p2l_contDiff_incEllIntFm hk).continuous).comp
      (continuous_const.sub continuous_id))).div (p2l_contDiff_rho hk weighted).continuous
      fun φ => (p2lRho_pos hk weighted φ).ne'
  have hdn : Continuous fun x => Real.jacobiDnm x (k ^ 2) :=
    continuous_iff_continuousAt.2 fun x => (Real.hasDerivAt_jacobiDnm hk x).continuousAt
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := Real.compEllIntKm (k ^ 2))
    (f := fun x => Real.lamePhi x k) (f' := fun x => -Real.jacobiDnm x (k ^ 2))
    (g := fun t => p2lPhiFun w k weighted t * τ t) (fun x _ => p1l_hasDerivAt_phi hk x)
    hdn.neg.continuousOn (hF.mul hτ)
  have h0 : Real.lamePhi 0 k = π / 2 := by simp [Real.lamePhi, Real.jacobiAmm_zero hk]
  have hK : Real.lamePhi (Real.compEllIntKm (k ^ 2)) k = 0 := by
    rw [Real.lamePhi, Real.jacobiAmm_compEllIntKm hk, sub_self]
  rw [h0, hK] at hsub
  have hsub' : ∫ t in (0 : ℝ)..π / 2, p2lPhiFun w k weighted t * τ t =
      -∫ x in (0 : ℝ)..Real.compEllIntKm (k ^ 2),
        ((fun t => p2lPhiFun w k weighted t * τ t) ∘ fun x => Real.lamePhi x k) x *
          -Real.jacobiDnm x (k ^ 2) := by
    rw [hsub, intervalIntegral.integral_symm]
  rw [hsub', ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [Function.comp_apply, p2lPhiFun_lamePhi hk]
  have := Real.jacobiDnm_pos hk x
  cases weighted
  · simp only [Bool.false_eq_true, ↓reduceIte]; field_simp
  · simp only [↓reduceIte, div_one]; ring

/-- Folding `∫₀^π` onto `∫₀^{π/2}` for `g(π - s) = c g(s)`. -/
lemma p2l_integral_fold {g : ℝ → ℝ} (hg : Continuous g) {c : ℝ} (hc : ∀ s, g (π - s) = c * g s) :
    ∫ t in (0 : ℝ)..π, g t = (1 + c) * ∫ t in (0 : ℝ)..π / 2, g t := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2) (hg.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _)]
  have h2 : ∫ t in π / 2..π, g t = c * ∫ t in (0 : ℝ)..π / 2, g t := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := π / 2) g π
    rw [show π - π / 2 = π / 2 by ring, sub_zero] at this
    rw [← this, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun s _ => hc s
  rw [h2]; ring

/-- **Cosine series of a Lamé-type function** in `φ = π/2 - am(x, k)`: if `w` is `C²`, has
period `4K`, `w(2K - x) = w(x)` and `w(-x) = δ w(x)`, then
`w(x)/ρ(x) = ∑ⱼ c_j ((1 + δ(-1)^j)/2) C_j cos(jφ)` with `c₀ = 1/2`, `cⱼ = 1` otherwise, the
coefficients `C_j = Real.lameCosCoeff w k weighted j` and `ρ = 1` (`weighted`) or `dn`. -/
theorem p2l_lame_hasSum_cos (hk0 : 0 < k) (hk1 : k < 1) (hw : ContDiff ℝ 2 w)
    (h4 : ∀ x, w (x + 4 * Real.compEllIntKm (k ^ 2)) = w x)
    (hσ : ∀ x, w (2 * Real.compEllIntKm (k ^ 2) - x) = w x) {δ : ℝ}
    (hδ : ∀ x, w (-x) = δ * w x) (weighted : Bool) (x : ℝ) :
    HasSum (fun j : ℕ => (if j = 0 then 1 / 2 else 1) *
      ((1 + δ * (-1) ^ j) / 2 * Real.lameCosCoeff w k weighted j) *
        Real.cos (j * Real.lamePhi x k))
      (w x / (if weighted then 1 else Real.jacobiDnm x (k ^ 2))) := by
  have hk := l29_sq_lt_one hk0 hk1
  have hF := p2lPhiFun_contDiff (weighted := weighted) hk hw
  have hσ' : ∀ x, w (2 * Real.compEllIntKm (k ^ 2) - x) = 1 * w x := fun x => by
    rw [one_mul]; exact hσ x
  have hev : ∀ t, p2lPhiFun w k weighted (-t) = p2lPhiFun w k weighted t := fun t => by
    have := p2lPhiFun_neg (weighted := weighted) hk hσ' t
    rwa [one_mul] at this
  have hs := p2l_hasSum_cos hF (p2lPhiFun_periodic hk h4) hev (Real.lamePhi x k)
  rw [p2lPhiFun_lamePhi hk] at hs
  convert hs using 3 with j
  rw [Real.lameCosCoeff, p2l_integral_lamePhi hk0 hk1 hw.continuous
    (τ := fun t => Real.cos (j * t)) (by fun_prop),
    p2l_integral_fold (g := fun t => p2lPhiFun w k weighted t * Real.cos (j * t))
      (hF.continuous.mul (by fun_prop)) (c := δ * (-1) ^ j) fun s => by
      rw [p2lPhiFun_pi_sub hδ, mul_sub, Real.cos_nat_mul_pi_sub]; ring]
  ring

/-- **Sine series of a Lamé-type function** in `φ`: if `w` is `C²`, has period `4K`,
`w(2K - x) = -w(x)` and `w(-x) = δ w(x)`, then
`w(x)/ρ(x) = ∑ⱼ ((1 - δ(-1)^j)/2) S_j sin(jφ)` with `S_j = Real.lameSinCoeff w k weighted j`. -/
theorem p2l_lame_hasSum_sin (hk0 : 0 < k) (hk1 : k < 1) (hw : ContDiff ℝ 2 w)
    (h4 : ∀ x, w (x + 4 * Real.compEllIntKm (k ^ 2)) = w x)
    (hσ : ∀ x, w (2 * Real.compEllIntKm (k ^ 2) - x) = -w x) {δ : ℝ}
    (hδ : ∀ x, w (-x) = δ * w x) (weighted : Bool) (x : ℝ) :
    HasSum (fun j : ℕ => ((1 - δ * (-1) ^ j) / 2 * Real.lameSinCoeff w k weighted j) *
        Real.sin (j * Real.lamePhi x k))
      (w x / (if weighted then 1 else Real.jacobiDnm x (k ^ 2))) := by
  have hk := l29_sq_lt_one hk0 hk1
  have hF := p2lPhiFun_contDiff (weighted := weighted) hk hw
  have hσ' : ∀ x, w (2 * Real.compEllIntKm (k ^ 2) - x) = -1 * w x := fun x => by
    rw [neg_one_mul]; exact hσ x
  have hodd : ∀ t, p2lPhiFun w k weighted (-t) = -p2lPhiFun w k weighted t := fun t => by
    have := p2lPhiFun_neg (weighted := weighted) hk hσ' t
    rwa [neg_one_mul] at this
  have hs := p2l_hasSum_sin hF (p2lPhiFun_periodic hk h4) hodd (Real.lamePhi x k)
  rw [p2lPhiFun_lamePhi hk] at hs
  convert hs using 2 with j
  rw [Real.lameSinCoeff, p2l_integral_lamePhi hk0 hk1 hw.continuous
    (τ := fun t => Real.sin (j * t)) (by fun_prop),
    p2l_integral_fold (g := fun t => p2lPhiFun w k weighted t * Real.sin (j * t))
      (hF.continuous.mul (by fun_prop)) (c := -(δ * (-1) ^ j)) fun s => by
      rw [p2lPhiFun_pi_sub hδ, mul_sub, Real.sin_nat_mul_pi_sub]; ring]
  ring

/-! ### Absolute convergence and termwise integration -/

/-- Absolute summability of the cosine coefficients of an even, `2π`-periodic `C²` function. -/
lemma p2l_summable_cos_coeff {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hper : Function.Periodic F (2 * π)) (hev : ∀ t, F (-t) = F t) :
    Summable fun n : ℕ => |2 / π * ∫ t in (0 : ℝ)..π, F t * Real.cos (n * t)| := by
  have hf : ContDiff ℝ 2 (fun t => (F t : ℂ)) := ofRealCLM.contDiff.comp hF
  obtain ⟨M, hM0, hM⟩ := legAdd_coeff_bound hf (fun t => by simp [hper t])
  refine Summable.of_norm_bounded_eventually_nat (g := fun n : ℕ => 2 * M * (1 / (n : ℝ) ^ 2))
    ((Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left _) ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have h := hM n (by exact_mod_cast hn)
  rw [p2l_coeff_even hF.continuous hev, Complex.norm_real, Real.norm_eq_abs] at h
  simp only [Int.cast_natCast] at h
  rw [Real.norm_eq_abs, abs_abs, show 2 / π * ∫ t in (0 : ℝ)..π, F t * Real.cos (n * t) =
    2 * (1 / π * ∫ t in (0 : ℝ)..π, F t * Real.cos (n * t)) by ring, abs_mul, abs_two]
  calc 2 * |1 / π * ∫ t in (0 : ℝ)..π, F t * Real.cos (n * t)| ≤ 2 * (M / (n : ℝ) ^ 2) := by
        gcongr
    _ = _ := by ring

/-- Absolute summability of the sine coefficients of an odd, `2π`-periodic `C²` function. -/
lemma p2l_summable_sin_coeff {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hper : Function.Periodic F (2 * π)) (hodd : ∀ t, F (-t) = -F t) :
    Summable fun n : ℕ => |2 / π * ∫ t in (0 : ℝ)..π, F t * Real.sin (n * t)| := by
  have hf : ContDiff ℝ 2 (fun t => (F t : ℂ)) := ofRealCLM.contDiff.comp hF
  obtain ⟨M, hM0, hM⟩ := legAdd_coeff_bound hf (fun t => by simp [hper t])
  refine Summable.of_norm_bounded_eventually_nat (g := fun n : ℕ => 2 * M * (1 / (n : ℝ) ^ 2))
    ((Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left _) ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have h := hM n (by exact_mod_cast hn)
  rw [p2l_coeff_odd hF.continuous hodd, norm_mul, norm_neg, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs] at h
  simp only [Int.cast_natCast] at h
  rw [Real.norm_eq_abs, abs_abs, show 2 / π * ∫ t in (0 : ℝ)..π, F t * Real.sin (n * t) =
    2 * (1 / π * ∫ t in (0 : ℝ)..π, F t * Real.sin (n * t)) by ring, abs_mul, abs_two]
  calc 2 * |1 / π * ∫ t in (0 : ℝ)..π, F t * Real.sin (n * t)| ≤ 2 * (M / (n : ℝ) ^ 2) := by
        gcongr
    _ = _ := by ring

/-- Termwise integration of an absolutely convergent series of bounded continuous terms
against a continuous function. -/
theorem p2l_hasSum_integral_mul {c : ℕ → ℝ} {τ : ℕ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hc : Summable fun n => |c n|) (hτ : ∀ n, Continuous (τ n)) (hτb : ∀ n t, |τ n t| ≤ 1)
    (hg : Continuous g) (hsum : ∀ t, HasSum (fun n => c n * τ n t) (f t)) (a b : ℝ) :
    HasSum (fun n => c n * ∫ t in a..b, τ n t * g t) (∫ t in a..b, f t * g t) := by
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := a)
    (b := b) (F := fun n t => c n * τ n t * g t) (f := fun t => f t * g t)
    (fun n t => |c n| * |g t|)
    (fun n => ((continuous_const.mul (hτ n)).mul hg).aestronglyMeasurable)
    (fun n => ae_of_all _ fun t _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right (abs_nonneg _) (hτb n t)) (abs_nonneg _))
    (ae_of_all _ fun t _ => hc.mul_right _)
    (by
      simp_rw [tsum_mul_right]
      exact (continuous_const.mul hg.abs).intervalIntegrable _ _)
    (ae_of_all _ fun t _ => (hsum t).mul_right (g t))
  convert h using 1
  funext n
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext t; ring

/-- The folded coefficient identity behind `p2l_lame_hasSum_cos`. -/
lemma p2l_lame_coeff_cos (hk0 : 0 < k) (hk1 : k < 1) (hw : ContDiff ℝ 2 w) {δ : ℝ}
    (hδ : ∀ x, w (-x) = δ * w x) (weighted : Bool) (j : ℕ) :
    (1 + δ * (-1) ^ j) / 2 * Real.lameCosCoeff w k weighted j =
      2 / π * ∫ t in (0 : ℝ)..π, p2lPhiFun w k weighted t * Real.cos (j * t) := by
  have hF := p2lPhiFun_contDiff (weighted := weighted) (l29_sq_lt_one hk0 hk1) hw
  rw [Real.lameCosCoeff, p2l_integral_lamePhi hk0 hk1 hw.continuous
    (τ := fun t => Real.cos (j * t)) (by fun_prop),
    p2l_integral_fold (g := fun t => p2lPhiFun w k weighted t * Real.cos (j * t))
      (hF.continuous.mul (by fun_prop)) (c := δ * (-1) ^ j) fun s => by
      rw [p2lPhiFun_pi_sub hδ, mul_sub, Real.cos_nat_mul_pi_sub]; ring]
  ring

/-- The folded coefficient identity behind `p2l_lame_hasSum_sin`. -/
theorem p2l_lame_coeff_sin (hk0 : 0 < k) (hk1 : k < 1) (hw : ContDiff ℝ 2 w) {δ : ℝ}
    (hδ : ∀ x, w (-x) = δ * w x) (weighted : Bool) (j : ℕ) :
    (1 - δ * (-1) ^ j) / 2 * Real.lameSinCoeff w k weighted j =
      2 / π * ∫ t in (0 : ℝ)..π, p2lPhiFun w k weighted t * Real.sin (j * t) := by
  have hF := p2lPhiFun_contDiff (weighted := weighted) (l29_sq_lt_one hk0 hk1) hw
  rw [Real.lameSinCoeff, p2l_integral_lamePhi hk0 hk1 hw.continuous
    (τ := fun t => Real.sin (j * t)) (by fun_prop),
    p2l_integral_fold (g := fun t => p2lPhiFun w k weighted t * Real.sin (j * t))
      (hF.continuous.mul (by fun_prop)) (c := -(δ * (-1) ^ j)) fun s => by
      rw [p2lPhiFun_pi_sub hδ, mul_sub, Real.sin_nat_mul_pi_sub]; ring]
  ring

/-- Absolute summability of the Lamé cosine coefficients. -/
theorem p2l_lame_summable_cos (hk0 : 0 < k) (hk1 : k < 1) (hw : ContDiff ℝ 2 w)
    (h4 : ∀ x, w (x + 4 * Real.compEllIntKm (k ^ 2)) = w x)
    (hσ : ∀ x, w (2 * Real.compEllIntKm (k ^ 2) - x) = w x) {δ : ℝ}
    (hδ : ∀ x, w (-x) = δ * w x) (weighted : Bool) :
    Summable fun j : ℕ => |(if j = 0 then 1 / 2 else 1) *
      ((1 + δ * (-1) ^ j) / 2 * Real.lameCosCoeff w k weighted j)| := by
  have hk := l29_sq_lt_one hk0 hk1
  have hσ' : ∀ x, w (2 * Real.compEllIntKm (k ^ 2) - x) = 1 * w x := fun x => by
    rw [one_mul]; exact hσ x
  have hev : ∀ t, p2lPhiFun w k weighted (-t) = p2lPhiFun w k weighted t := fun t => by
    have := p2lPhiFun_neg (weighted := weighted) hk hσ' t
    rwa [one_mul] at this
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun j => ?_)
    (p2l_summable_cos_coeff (p2lPhiFun_contDiff hk hw) (p2lPhiFun_periodic hk h4) hev)
  rw [p2l_lame_coeff_cos hk0 hk1 hw hδ, abs_mul]
  refine mul_le_of_le_one_left (abs_nonneg _) ?_
  split_ifs <;> norm_num

/-- Absolute summability of the Lamé sine coefficients. -/
theorem p2l_lame_summable_sin (hk0 : 0 < k) (hk1 : k < 1) (hw : ContDiff ℝ 2 w)
    (h4 : ∀ x, w (x + 4 * Real.compEllIntKm (k ^ 2)) = w x)
    (hσ : ∀ x, w (2 * Real.compEllIntKm (k ^ 2) - x) = -w x) {δ : ℝ}
    (hδ : ∀ x, w (-x) = δ * w x) (weighted : Bool) :
    Summable fun j : ℕ => |(1 - δ * (-1) ^ j) / 2 * Real.lameSinCoeff w k weighted j| := by
  have hk := l29_sq_lt_one hk0 hk1
  have hσ' : ∀ x, w (2 * Real.compEllIntKm (k ^ 2) - x) = -1 * w x := fun x => by
    rw [neg_one_mul]; exact hσ x
  have hodd : ∀ t, p2lPhiFun w k weighted (-t) = -p2lPhiFun w k weighted t := fun t => by
    have := p2lPhiFun_neg (weighted := weighted) hk hσ' t
    rwa [neg_one_mul] at this
  refine (p2l_summable_sin_coeff (p2lPhiFun_contDiff hk hw) (p2lPhiFun_periodic hk h4)
    hodd).congr fun j => ?_
  rw [p2l_lame_coeff_sin hk0 hk1 hw hδ]

end Lame

end DLMF.Lame
