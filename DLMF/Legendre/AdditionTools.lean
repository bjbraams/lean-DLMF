/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Series
public import DLMF.Legendre.Harmonics

/-!
# Tools for the Legendre addition theorems of general degree

Infrastructure for the addition theorems DLMF 14.18.1–14.18.5 and 14.28.1 for complex degree `ν`,
proved coefficientwise in the Fourier expansion in the angle `φ`, with Carlson's theorem in `ν`
carrying the integer case (the polynomial addition theorem) to all degrees.

* `legAdd_coeff`, `legAdd_hasSum_cos`: Fourier coefficients on `[-π, π]` and the cosine expansion
  of an even, `2π`-periodic `C²` function (absolute convergence from two integrations by parts).
* `legAdd_carlson`: Carlson's theorem (`Complex.eqOn_zero_of_natCast_eq_zero`) for entire
  functions bounded by `C exp (A |Re ν| + B |Im ν|)`, `B < π`, extended to all of `ℂ` by the
  identity theorem.
* Laplace-type bounds on `(1, ∞)`: `legAdd_norm_legendreP_le` (`|P_ν(x)| ≤ (2x)^{|Re ν|}`, from
  Laplace's first integral `legendreP_laplace`), `legAdd_norm_associatedP_nat_le` (from 14.12.7) and
  `legAdd_norm_associatedP_neg_le` (from the fractional integral 14.12.5).
* `legAdd_coeff_kernel`, `legAdd_hyp_nat`: Fourier coefficients of the finite Legendre angular
  kernel, giving the integer-degree identity.
* `legAdd_hyp_coeff_eq`, `legAdd_associatedP_addition`: the Fourier coefficients of
  `φ ↦ P_ν(cosh ξ₁ cosh ξ₂ - sinh ξ₁ sinh ξ₂ cos φ)` for all complex `ν`, and 14.18.4.

* `legAdd_regGHG_one_eq_integral`, `legAdd_norm_ferrersP_zero_le`: the representation
  `𝖯_ν(cos θ) = π^{-1/2} ∫₀^π 𝐅(ν+1, -ν; 1/2; sin²(θ/2) sin² t) dt` (termwise, with Wallis'
  integral), which with 15.4.14 is the Mehler–Dirichlet integral in disguise, and the sharp bound
  `|𝖯_ν(cos θ)| ≤ e^{θ |Im ν|} / cos (θ/2)` for `0 ≤ θ < π` and all complex `ν`.
* `legAdd_norm_ferrersP_neg_le`, `legAdd_ferrersP_nat_eq`: bounds for `𝖯^{-m}_ν` (from 14.12.2)
  and `𝖯^m_ν = (-1)^m (ν-m+1)_{2m} 𝖯^{-m}_ν` for every complex `ν`.
* `legAdd_fer_coeff_eq`, `legAdd_ferrersP_addition_of_nat`: Carlson's theorem with type
  `θ₁ + θ₂ < π` and 14.18.1, given the integer case `legAdd_fer_nat` (from the polynomial
  addition theorem).
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory DLMF.Hypergeometric DLMF
open scoped Real Topology Nat

namespace DLMF.Legendre

/-- Fourier coefficient on `[-π, π]`. -/
def legAdd_coeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  1 / (2 * π) * ∫ t in (-π)..π, exp (-(n * t * I)) * f t

theorem legAdd_exp_pi (n : ℤ) : exp (-(n * (π:ℝ) * I)) = exp (-(n * ((-π : ℝ):ℂ) * I)) := by
  rw [show -((n:ℂ) * ((-π:ℝ):ℂ) * I) = -(n * (π:ℝ) * I) + n * (2 * π * I) by push_cast; ring,
    exp_add, exp_int_mul_two_pi_mul_I, mul_one]

/-- One integration by parts for a periodic function. -/
theorem legAdd_integral_exp_mul_eq {g g' : ℝ → ℂ} (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : Continuous g') (hper : g π = g (-π)) {n : ℤ} (hn : n ≠ 0) :
    (∫ t in (-π)..π, exp (-(n * t * I)) * g t) =
      1 / (n * I) * ∫ t in (-π)..π, exp (-(n * t * I)) * g' t := by
  have hu : ∀ t : ℝ, HasDerivAt (fun t : ℝ => exp (-(n * t * I)))
      (exp (-(n * t * I)) * (-(n * I))) t := by
    intro t
    have := ((hasDerivAt_id (t:ℂ)).mul_const (-(n * I))).cexp.comp_ofReal (z := t)
    convert this using 1
    · funext s; simp only [id]; ring_nf
    · simp only [id]; ring_nf
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -π) (b := π)
    (fun t _ => hu t) (fun t _ => hg t)
    ((by fun_prop : Continuous fun t : ℝ => exp (-(n * t * I)) * (-(n * I))).intervalIntegrable _ _)
    (hg'.intervalIntegrable _ _)
  have hb : exp (-(n * ((π:ℝ):ℂ) * I)) * g π - exp (-(n * ((-π:ℝ):ℂ) * I)) * g (-π) = 0 := by
    rw [legAdd_exp_pi n, hper, sub_self]
  rw [hb, zero_sub] at hparts
  have hnI : (n:ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hn) I_ne_zero
  have hc : (∫ t in (-π)..π, exp (-(n * t * I)) * (-(n * I)) * g t) =
      (-(n * I)) * ∫ t in (-π)..π, exp (-(n * t * I)) * g t := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by ring
  calc (∫ t in (-π)..π, exp (-(n * t * I)) * g t)
      = 1 / (n * I) * ((n * I) * ∫ t in (-π)..π, exp (-(n * t * I)) * g t) := by
        rw [← mul_assoc, one_div, inv_mul_cancel₀ hnI, one_mul]
    _ = _ := by rw [hparts, hc]; ring


/-- Periodicity passes to the derivative. -/
theorem legAdd_deriv_periodic {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π)) :
    Function.Periodic (deriv f) (2 * π) := by
  intro t
  have h : f = fun s => f (s + 2 * π) := funext fun s => (hper s).symm
  conv_rhs => rw [h]
  rw [deriv_comp_add_const]

/-- Second-order decay of the Fourier coefficients of a periodic `C²` function. -/
theorem legAdd_coeff_bound {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hper : Function.Periodic f (2 * π)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ, n ≠ 0 → ‖legAdd_coeff f n‖ ≤ M / (n:ℝ) ^ 2 := by
  have hd1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hc1 : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  have hd2 : Differentiable ℝ (deriv f) := hc1.differentiable (by norm_num)
  have hc2 : Continuous (deriv (deriv f)) := hc1.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -π) (b := π)).exists_bound_of_continuousOn
    hc2.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun n hn => ?_⟩
  have h1 := legAdd_integral_exp_mul_eq (g := f) (g' := deriv f) (fun t => (hd1 t).hasDerivAt)
    hc1.continuous (by have := hper (-π); rw [show -π + 2 * π = π by ring] at this; exact this) hn
  have h2 := legAdd_integral_exp_mul_eq (g := deriv f) (g' := deriv (deriv f))
    (fun t => (hd2 t).hasDerivAt) hc2
    (by have := legAdd_deriv_periodic hper (-π); rw [show -π + 2 * π = π by ring] at this;
        exact this) hn
  have hI : ‖∫ t : ℝ in (-π)..π, exp (-((n:ℂ) * (t:ℂ) * I)) * deriv (deriv f) t‖ ≤ max M 0 * |π - -π| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [uIoc_of_le (by linarith [Real.pi_pos])] at ht
    rw [norm_mul, show -((n:ℂ) * t * I) = ((-(n * t) : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I, one_mul]
    exact (hM t ⟨ht.1.le, ht.2⟩).trans (le_max_left _ _)
  have hn2 : (0:ℝ) < (n:ℝ) ^ 2 := by positivity
  rw [legAdd_coeff, h1, h2, norm_mul, norm_mul, norm_mul]
  have hnI : ‖(1:ℂ) / (n * I)‖ = 1 / |(n:ℝ)| := by
    rw [norm_div, norm_one, norm_mul, norm_I, mul_one, norm_intCast]
  rw [hnI, show ‖(1:ℂ) / (2 * π)‖ = 1 / (2 * π) by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]]
  have habs : |(n:ℝ)| * |(n:ℝ)| = (n:ℝ) ^ 2 := by rw [← abs_mul, abs_mul_self, sq]
  have hπ := Real.pi_pos
  have hna : 0 < |(n:ℝ)| := abs_pos.2 (by exact_mod_cast hn)
  calc 1 / (2 * π) * (1 / |(n:ℝ)| * (1 / |(n:ℝ)| *
        ‖∫ t : ℝ in (-π)..π, exp (-((n:ℂ) * (t:ℂ) * I)) * deriv (deriv f) t‖))
      ≤ 1 / (2 * π) * (1 / |(n:ℝ)| * (1 / |(n:ℝ)| * (max M 0 * |π - -π|))) := by gcongr
    _ = max M 0 / (n:ℝ) ^ 2 := by rw [← habs, abs_of_pos (show (0:ℝ) < π - -π by linarith)]; field_simp; ring


/-- The coefficients of an even function are even in the index. -/
theorem legAdd_coeff_neg {f : ℝ → ℂ} (hev : ∀ t, f (-t) = f t) (n : ℤ) :
    legAdd_coeff f (-n) = legAdd_coeff f n := by
  rw [legAdd_coeff, legAdd_coeff]
  congr 1
  have h := intervalIntegral.integral_comp_neg (a := -π) (b := π)
    (fun t : ℝ => exp (-(n * t * I)) * f t)
  simp only [neg_neg, ofReal_neg] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [hev, Int.cast_neg]
  ring_nf

/-- **Fourier cosine expansion** of an even, `2π`-periodic `C²` function:
`f(u) = c₀ + 2 ∑_{m ≥ 1} cₘ cos(mu)`, with `cₘ = (2π)⁻¹ ∫_{-π}^{π} e^{-imt} f(t) dt`. -/
theorem legAdd_hasSum_cos {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hper : Function.Periodic f (2 * π))
    (hev : ∀ t, f (-t) = f t) (u : ℝ) :
    HasSum (fun j : ℕ => 2 * legAdd_coeff f ((j + 1 : ℕ) : ℤ) * Real.cos (((j + 1 : ℕ) : ℝ) * u))
      (f u - legAdd_coeff f 0) := by
  have : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
  let g : C(AddCircle (2 * π), ℂ) := ⟨hper.lift, continuous_coinduced_dom.mpr hf.continuous⟩
  have hgx : ∀ x : ℝ, g (x : AddCircle (2 * π)) = f x := fun x => rfl
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
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
    refine Summable.of_norm_bounded_eventually (g := fun n : ℤ => M * (1 / (n:ℝ) ^ 2))
      ((Real.summable_one_div_int_pow.mpr (by norm_num)).mul_left M) ?_
    have : {n : ℤ | n ≠ 0} ∈ Filter.cofinite := by
      simp only [Filter.mem_cofinite, ne_eq]
      convert Set.finite_singleton (0:ℤ) using 1
      ext n; simp
    filter_upwards [this] with n hn
    rw [hgc, mul_one_div]
    exact hM n hn
  have hp := (has_pointwise_sum_fourier_series_of_summable hsum
    (u : AddCircle (2 * π))).nat_add_neg
  have hterm : ∀ n : ℕ, fourierCoeff g n • fourier (n : ℤ) (u : AddCircle (2 * π)) +
      fourierCoeff g (-(n : ℤ)) • fourier (-(n : ℤ)) (u : AddCircle (2 * π)) =
      2 * legAdd_coeff f n * Real.cos ((n : ℝ) * u) := by
    intro n
    rw [hgc, hgc, legAdd_coeff_neg hev, fourier_coe_apply, fourier_coe_apply, smul_eq_mul,
      smul_eq_mul, ofReal_cos, Complex.cos]
    rw [show 2 * (π : ℂ) * I * ((n : ℤ) : ℂ) * (u : ℂ) / ((2 * π : ℝ) : ℂ) =
        ((n:ℝ) * u : ℝ) * I by push_cast; field_simp,
      show 2 * (π : ℂ) * I * ((-(n : ℤ) : ℤ) : ℂ) * (u : ℂ) / ((2 * π : ℝ) : ℂ) =
        -(((n:ℝ) * u : ℝ) * I) by push_cast; field_simp]
    ring_nf
  have hR : HasSum (fun n : ℕ => 2 * legAdd_coeff f n * Real.cos ((n : ℝ) * u))
      (f u + legAdd_coeff f 0) := by
    convert hp using 1
    · funext n; exact (hterm n).symm
    · rw [hgx, hgc, fourier_zero, smul_eq_mul, mul_one]
  rw [← hasSum_nat_add_iff' 1] at hR
  convert hR using 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_mul, Real.cos_zero,
    ofReal_one, mul_one, CharP.cast_eq_zero]
  ring


/-- Carlson's theorem in the form used here: an entire function bounded by
`C exp (A |Re ν| + B |Im ν|)` on `Re ν ≥ 0`, with `B < π`, vanishing on `ℕ`, vanishes. -/
theorem legAdd_carlson {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hBπ : B < π)
    (hb : ∀ ν : ℂ, 0 ≤ ν.re → ‖f ν‖ ≤ C * Real.exp (A * |ν.re| + B * |ν.im|))
    (hz : ∀ n : ℕ, f n = 0) (ν : ℂ) : f ν = 0 := by
  have hC : ∀ ν : ℂ, 0 ≤ ν.re → f ν = 0 :=
    Complex.eqOn_zero_of_natCast_eq_zero (f := f) hf.diffContOnCl (C := C) (τ := A + B) (c := B)
      (fun z hz => (hb z hz).trans (by
        have h0 : 0 ≤ C := by
          have h1 := (norm_nonneg _).trans (hb z hz)
          have h2 := Real.exp_pos (A * |z.re| + B * |z.im|)
          by_contra hc; have := lt_of_not_ge hc; nlinarith
        gcongr
        nlinarith [abs_re_le_norm z, abs_im_le_norm z]))
      (fun y => by
        have := hb (y * I) (by simp)
        simpa using this) hBπ hz
  have han : AnalyticOnNhd ℂ f univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hev : f =ᶠ[𝓝 (1:ℂ)] 0 := by
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (0:ℝ) < (1:ℂ).re)] with z hz
    exact hC z hz.le
  exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ 1) hev
    (mem_univ ν)


/-- A power of a number in `[B⁻¹, B]`, `B ≥ 1`, is at most `B^{|r|}`. -/
theorem legAdd_rpow_le {b B r : ℝ} (hb : 0 < b) (h1 : B⁻¹ ≤ b) (h2 : b ≤ B) :
    b ^ r ≤ B ^ |r| := by
  have hB : 0 < B := hb.trans_le h2
  rcases le_or_gt 0 r with hr | hr
  · rw [abs_of_nonneg hr]; exact Real.rpow_le_rpow hb.le h2 hr
  · rw [abs_of_neg hr, show b ^ r = (b⁻¹) ^ (-r) by
      rw [Real.inv_rpow hb.le, ← Real.rpow_neg hb.le, neg_neg]]
    exact Real.rpow_le_rpow (inv_pos.2 hb).le (by
      rw [inv_le_comm₀ hb hB]; exact h1) (by linarith)

/-- The Laplace base `x + √(x²-1) cos u` lies in `[(2x)⁻¹, 2x]` for `x ≥ 1`. -/
theorem legAdd_laplace_base_mem {x : ℝ} (hx : 1 ≤ x) (u : ℝ) :
    0 < x + Real.sqrt (x ^ 2 - 1) * Real.cos u ∧
    (2 * x)⁻¹ ≤ x + Real.sqrt (x ^ 2 - 1) * Real.cos u ∧
    x + Real.sqrt (x ^ 2 - 1) * Real.cos u ≤ 2 * x := by
  set s := Real.sqrt (x ^ 2 - 1) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = x ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hsx : s < x := by nlinarith
  have hc1 := Real.cos_le_one u
  have hc2 := Real.neg_one_le_cos u
  have hlow : x - s ≤ x + s * Real.cos u := by nlinarith
  have hxs : 0 < x - s := by linarith
  have hprod : (x - s) * (x + s) = 1 := by nlinarith
  refine ⟨by linarith, ?_, by nlinarith⟩
  refine le_trans ?_ hlow
  rw [inv_le_iff_one_le_mul₀ (by linarith)]
  nlinarith

/-- `associatedP ν 0 = legendreP ν` on `[1, ∞)`. -/
theorem legAdd_associatedP_zero {ν : ℂ} {x : ℝ} (hx : 1 ≤ x) :
    associatedP ν 0 x = legendreP ν x := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h
    rw [ofReal_one, legendreP_one]
    simp only [associatedP, zero_div, zero_mul, exp_zero, one_mul, sub_zero, sub_self]
    rw [regularizedGaussHG_zero_of_regular]
    · simp
    · intro k hk
      have := congrArg Complex.re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  · exact associatedP_zero_order ν (legInt_one_lt_mem h)

/-- Laplace bound `|P_ν(x)| ≤ (2x)^{|Re ν|}` for real `x ≥ 1`. -/
theorem legAdd_norm_legendreP_le (ν : ℂ) {x : ℝ} (hx : 1 ≤ x) :
    ‖legendreP ν x‖ ≤ (2 * x) ^ |ν.re| := by
  rw [legendreP_laplace ν hx, norm_mul]
  have hI : ‖∫ u in (0:ℝ)..π, (((x + Real.sqrt (x ^ 2 - 1) * Real.cos u : ℝ)) : ℂ) ^ ν‖ ≤
      (2 * x) ^ |ν.re| * |π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => ?_
    obtain ⟨h0, h1, h2⟩ := legAdd_laplace_base_mem hx u
    rw [norm_cpow_eq_rpow_re_of_pos h0]
    exact legAdd_rpow_le h0 h1 h2
  have hπ := Real.pi_pos
  rw [sub_zero, abs_of_pos hπ] at hI
  rw [show ‖(1:ℂ) / π‖ = 1 / π by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ]]
  calc 1 / π * ‖∫ u in (0:ℝ)..π, (((x + Real.sqrt (x ^ 2 - 1) * Real.cos u : ℝ)) : ℂ) ^ ν‖
      ≤ 1 / π * ((2 * x) ^ |ν.re| * π) := by gcongr
    _ = (2 * x) ^ |ν.re| := by field_simp

/-- Bound for nonnegative integer order on `(1, ∞)` from 14.12.7. -/
theorem legAdd_norm_associatedP_nat_le (ν : ℂ) (m : ℕ) {x : ℝ} (hx : 1 < x) :
    ‖associatedP ν m x‖ ≤ ‖poch (ν + 1) m‖ * (2 * x) ^ |ν.re| := by
  rw [associatedP_fourier_integral ν m hx, norm_mul, norm_div]
  have hI : ‖∫ θ : ℝ in (0:ℝ)..π, (x + Real.sqrt (x ^ 2 - 1) * Real.cos θ : ℂ) ^ ν *
      Real.cos (m * θ)‖ ≤ (2 * x) ^ |ν.re| * |π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => ?_
    obtain ⟨h0, h1, h2⟩ := legAdd_laplace_base_mem hx.le u
    rw [norm_mul, show (x + Real.sqrt (x ^ 2 - 1) * Real.cos u : ℂ) =
      ((x + Real.sqrt (x ^ 2 - 1) * Real.cos u : ℝ) : ℂ) by push_cast; ring,
      norm_cpow_eq_rpow_re_of_pos h0, Complex.norm_real, Real.norm_eq_abs]
    calc (x + Real.sqrt (x ^ 2 - 1) * Real.cos u) ^ ν.re * |Real.cos (m * u)|
        ≤ (2 * x) ^ |ν.re| * 1 := by
          gcongr
          · exact legAdd_rpow_le h0 h1 h2
          · exact Real.abs_cos_le_one _
      _ = _ := mul_one _
  have hπ := Real.pi_pos
  rw [sub_zero, abs_of_pos hπ] at hI
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ]
  calc ‖poch (ν + 1) m‖ / π * ‖∫ θ : ℝ in (0:ℝ)..π,
        (x + Real.sqrt (x ^ 2 - 1) * Real.cos θ : ℂ) ^ ν * Real.cos (m * θ)‖
      ≤ ‖poch (ν + 1) m‖ / π * ((2 * x) ^ |ν.re| * π) := by gcongr
    _ = _ := by field_simp


/-- Bound for negative integer order on `(1, ∞)` from the fractional integral 14.12.5. -/
theorem legAdd_norm_associatedP_neg_le (ν : ℂ) {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : 1 < x) :
    ‖associatedP ν (-(m:ℂ)) x‖ ≤ ‖((x:ℂ) ^ 2 - 1) ^ (-(m:ℂ) / 2) / Gamma m‖ *
      ((2 * x) ^ |ν.re| * (x - 1) ^ (m - 1) * (x - 1)) := by
  have hm' : (0:ℝ) < (m:ℂ).re := by simp; exact_mod_cast hm
  rw [associatedP_fractional_integral hm' ν hx, norm_mul]
  gcongr
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := x)
    (C := (2 * x) ^ |ν.re| * (x - 1) ^ (m - 1))
    (f := fun t : ℝ => associatedP ν 0 t * ((x:ℂ) - t) ^ ((m:ℂ) - 1)) (fun t ht => by
      rw [uIoc_of_le hx.le] at ht
      rw [norm_mul, legAdd_associatedP_zero ht.1.le, show (m:ℂ) - 1 = ((m - 1 : ℕ) : ℂ) by
        rw [Nat.cast_sub hm]; simp, cpow_natCast, norm_pow]
      gcongr
      · exact (legAdd_norm_legendreP_le ν ht.1.le).trans
          (Real.rpow_le_rpow (by linarith [ht.1]) (by linarith [ht.2]) (abs_nonneg _))
      · rw [show (x:ℂ) - t = ((x - t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
        linarith [ht.1])
  rwa [abs_of_pos (by linarith : (0:ℝ) < x - 1)] at hI

/-- `|(ν+1)_m| ≤ m! e^m e^{|ν|}`. -/
theorem legAdd_norm_poch_le (ν : ℂ) (m : ℕ) :
    ‖poch (ν + 1) m‖ ≤ m ! * Real.exp m * Real.exp ‖ν‖ := by
  have h1 : ‖poch (ν + 1) m‖ ≤ (‖ν‖ + m) ^ m := by
    have key : ∀ k : ℕ, k ≤ m → ‖poch (ν + 1) k‖ ≤ (‖ν‖ + m) ^ k := by
      intro k
      induction k with
      | zero => intro _; simp [poch_zero]
      | succ k ih =>
        intro hk
        rw [poch_succ, norm_mul, pow_succ]
        gcongr
        · exact ih (by omega)
        · calc ‖ν + 1 + k‖ ≤ ‖ν‖ + ‖(1:ℂ) + k‖ := by
                rw [add_assoc]; exact norm_add_le _ _
            _ ≤ ‖ν‖ + m := by
                gcongr
                rw [show (1:ℂ) + k = ((1 + k : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
                exact_mod_cast (by omega : 1 + k ≤ m)
    exact key m le_rfl
  have h2 := Real.pow_div_factorial_le_exp (x := ‖ν‖ + m) (by positivity) m
  have hf : (0:ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
  rw [div_le_iff₀ hf, Real.exp_add] at h2
  calc ‖poch (ν + 1) m‖ ≤ (‖ν‖ + m) ^ m := h1
    _ ≤ Real.exp ‖ν‖ * Real.exp m * m ! := h2
    _ = _ := by ring


/-- The order-zero function in hypergeometric form, for every argument. -/
theorem legAdd_associatedP_zero_eq (ν z : ℂ) :
    associatedP ν 0 z = regularizedGaussHG (ν + 1) (-ν) 1 ((1 - z) / 2) := by
  simp [associatedP]

/-- A real number below `1` lies in the cut plane. -/
theorem legAdd_ofReal_mem_cutPlane {r : ℝ} (hr : r < 1) : (r : ℂ) ∈ cutPlane := by
  rw [mem_cutPlane]; left; simp; linarith

/-- The argument `cosh ξ₁ cosh ξ₂ - sinh ξ₁ sinh ξ₂ cos t` of the hyperbolic addition theorem. -/
def legAdd_hX (ξ₁ ξ₂ t : ℝ) : ℝ :=
  Real.cosh ξ₁ * Real.cosh ξ₂ - Real.sinh ξ₁ * Real.sinh ξ₂ * Real.cos t

theorem legAdd_hX_mem {ξ₁ ξ₂ : ℝ} (h1 : 0 ≤ ξ₁) (h2 : 0 ≤ ξ₂) (t : ℝ) :
    1 ≤ legAdd_hX ξ₁ ξ₂ t ∧ legAdd_hX ξ₁ ξ₂ t ≤ Real.cosh (ξ₁ + ξ₂) := by
  have hs : 0 ≤ Real.sinh ξ₁ * Real.sinh ξ₂ :=
    mul_nonneg (Real.sinh_nonneg_iff.2 h1) (Real.sinh_nonneg_iff.2 h2)
  have hc1 := Real.cos_le_one t
  have hc2 := Real.neg_one_le_cos t
  have hsub := Real.one_le_cosh (ξ₁ - ξ₂)
  rw [Real.cosh_sub] at hsub
  rw [Real.cosh_add]
  unfold legAdd_hX
  constructor <;> nlinarith

/-- The order-zero Legendre function along `legAdd_hX` is `C²` in the angle. -/
theorem legAdd_hX_contDiff (ν : ℂ) {ξ₁ ξ₂ : ℝ} (h1 : 0 ≤ ξ₁) (h2 : 0 ≤ ξ₂) :
    ContDiff ℝ 2 (fun t : ℝ => associatedP ν 0 (legAdd_hX ξ₁ ξ₂ t)) := by
  have hG : DifferentiableOn ℂ (fun z => regularizedGaussHG (ν + 1) (-ν) 1 z) cutPlane :=
    DifferentiableOn.regularizedGaussHG (differentiableOn_const _) (differentiableOn_const _)
      (differentiableOn_const _) differentiableOn_id fun w hw => hw
  have hG2 : ContDiffOn ℝ 2 (fun z => regularizedGaussHG (ν + 1) (-ν) 1 z) cutPlane :=
    (hG.contDiffOn isOpen_cutPlane).restrict_scalars ℝ
  have hh : ContDiff ℝ 2 (fun t : ℝ => (((1 - legAdd_hX ξ₁ ξ₂ t) / 2 : ℝ) : ℂ)) := by
    refine ofRealCLM.contDiff.comp ?_
    unfold legAdd_hX
    exact (contDiff_const.sub (contDiff_const.sub (contDiff_const.mul Real.contDiff_cos))).div_const 2
  have := hG2.comp_contDiff hh fun t =>
    legAdd_ofReal_mem_cutPlane (by linarith [(legAdd_hX_mem h1 h2 t).1])
  convert this using 1
  funext t
  simp only [Function.comp, legAdd_associatedP_zero_eq]
  congr 1; push_cast; ring


/-- Order-zero values along `legAdd_hX` are bounded by `(2 cosh (ξ₁+ξ₂))^{|Re ν|}`. -/
theorem legAdd_hX_norm_le (ν : ℂ) {ξ₁ ξ₂ : ℝ} (h1 : 0 ≤ ξ₁) (h2 : 0 ≤ ξ₂) (t : ℝ) :
    ‖associatedP ν 0 (legAdd_hX ξ₁ ξ₂ t)‖ ≤ (2 * Real.cosh (ξ₁ + ξ₂)) ^ |ν.re| := by
  obtain ⟨hX1, hX2⟩ := legAdd_hX_mem h1 h2 t
  rw [legAdd_associatedP_zero hX1]
  exact (legAdd_norm_legendreP_le ν hX1).trans
    (Real.rpow_le_rpow (by linarith) (by linarith) (abs_nonneg _))

/-- Bound on the Fourier coefficients in the hyperbolic case. -/
theorem legAdd_hyp_coeff_bound (ν : ℂ) {ξ₁ ξ₂ : ℝ} (h1 : 0 ≤ ξ₁) (h2 : 0 ≤ ξ₂) (m : ℤ) :
    ‖legAdd_coeff (fun t => associatedP ν 0 (legAdd_hX ξ₁ ξ₂ t)) m‖ ≤
      (2 * Real.cosh (ξ₁ + ξ₂)) ^ |ν.re| := by
  rw [legAdd_coeff, norm_mul]
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := -π) (b := π)
    (C := (2 * Real.cosh (ξ₁ + ξ₂)) ^ |ν.re|)
    (f := fun t : ℝ => exp (-((m:ℂ) * t * I)) * associatedP ν 0 (legAdd_hX ξ₁ ξ₂ t))
    (fun t _ => by
      rw [norm_mul, show -((m:ℂ) * t * I) = ((-(m * t) : ℝ) : ℂ) * I by push_cast; ring,
        norm_exp_ofReal_mul_I, one_mul]
      exact legAdd_hX_norm_le ν h1 h2 t)
  have hπ := Real.pi_pos
  rw [abs_of_pos (by linarith : (0:ℝ) < π - -π)] at hI
  rw [show ‖(1:ℂ) / (2 * π)‖ = 1 / (2 * π) by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hπ]]
  calc 1 / (2 * π) * ‖∫ t : ℝ in (-π)..π, exp (-((m:ℂ) * t * I)) *
        associatedP ν 0 (legAdd_hX ξ₁ ξ₂ t)‖
      ≤ 1 / (2 * π) * ((2 * Real.cosh (ξ₁ + ξ₂)) ^ |ν.re| * (π - -π)) := by gcongr
    _ = _ := by field_simp; ring

/-- The order-zero function at a fixed argument in the cut plane is entire in the degree. -/
theorem legAdd_differentiable_associatedP_zero {z : ℂ} (hz : (1 - z) / 2 ∈ cutPlane) :
    Differentiable ℂ (fun ν : ℂ => associatedP ν 0 z) := by
  simp only [legAdd_associatedP_zero_eq]
  exact differentiable_regularizedGaussHG_comp (A := fun ν : ℂ => ν + 1) (B := fun ν : ℂ => -ν)
    (C := fun _ => 1) (by fun_prop) (by fun_prop) (by fun_prop) hz

/-- The Fourier coefficients in the hyperbolic case are entire in the degree. -/
theorem legAdd_hyp_coeff_differentiable {ξ₁ ξ₂ : ℝ} (h1 : 0 ≤ ξ₁) (h2 : 0 ≤ ξ₂) (m : ℤ) :
    Differentiable ℂ (fun ν => legAdd_coeff (fun t => associatedP ν 0 (legAdd_hX ξ₁ ξ₂ t)) m) := by
  have hz : ∀ t, (1 - ((legAdd_hX ξ₁ ξ₂ t : ℝ) : ℂ)) / 2 ∈ cutPlane := fun t => by
    rw [show (1 - ((legAdd_hX ξ₁ ξ₂ t : ℝ) : ℂ)) / 2 = (((1 - legAdd_hX ξ₁ ξ₂ t) / 2 : ℝ) : ℂ) by
      push_cast; ring]
    exact legAdd_ofReal_mem_cutPlane (by linarith [(legAdd_hX_mem h1 h2 t).1])
  have key : DifferentiableOn ℂ (fun ν => ∫ t in (-π)..π, exp (-((m:ℂ) * t * I)) *
      associatedP ν 0 (legAdd_hX ξ₁ ξ₂ t)) univ := by
    apply Complex.differentiableOn_intervalIntegral_of_locally_dominated isOpen_univ
    · intro ν _
      exact ((by fun_prop : Continuous fun t : ℝ => exp (-((m:ℂ) * t * I))).mul
        (legAdd_hX_contDiff ν h1 h2).continuous).aestronglyMeasurable
    · refine ae_of_all _ fun t => ?_
      exact ((differentiable_const _).mul
        (legAdd_differentiable_associatedP_zero (hz t))).differentiableOn
    · intro ν₀ _
      refine ⟨Metric.ball ν₀ 1, Metric.ball_mem_nhds _ one_pos,
        fun _ => (2 * Real.cosh (ξ₁ + ξ₂)) ^ (|ν₀.re| + 1),
        integrableOn_const (by rw [uIoc_of_le (by linarith [Real.pi_pos])]; simp), ae_of_all _ ?_⟩
      intro t y hy
      rw [norm_mul, show -((m:ℂ) * t * I) = ((-(m * t) : ℝ) : ℂ) * I by push_cast; ring,
        norm_exp_ofReal_mul_I, one_mul]
      refine (legAdd_hX_norm_le y h1 h2 t).trans (Real.rpow_le_rpow_of_exponent_le ?_ ?_)
      · have := Real.one_le_cosh (ξ₁ + ξ₂); linarith
      · have hd : ‖y - ν₀‖ < 1 := by simpa [dist_eq_norm] using hy
        have h3 := abs_re_le_norm (y - ν₀)
        rw [sub_re] at h3
        have h4 := abs_sub_abs_le_abs_sub y.re ν₀.re
        linarith
  rw [← differentiableOn_univ]
  exact (key.const_mul _).congr fun ν _ => rfl


/-- `associatedP ν μ z` is entire in the degree for `(1 - z)/2` in the cut plane. -/
theorem legAdd_differentiable_associatedP (μ : ℂ) {z : ℂ} (hz : (1 - z) / 2 ∈ cutPlane) :
    Differentiable ℂ (fun ν : ℂ => associatedP ν μ z) := by
  unfold associatedP
  exact (differentiable_const _).mul (differentiable_regularizedGaussHG_comp
    (A := fun ν : ℂ => ν + 1) (B := fun ν : ℂ => -ν) (C := fun _ => 1 - μ)
    (by fun_prop) (by fun_prop) (by fun_prop) hz)

/-- `(2x)^{|r|} = exp (log (2x) |r|)`. -/
theorem legAdd_rpow_eq_exp {x : ℝ} (hx : 0 < x) (r : ℝ) :
    (2 * x) ^ |r| = Real.exp (Real.log (2 * x) * |r|) := by
  rw [Real.rpow_def_of_pos (by linarith)]

/-- The right-hand side coefficients of the hyperbolic addition theorem satisfy a Carlson bound. -/
theorem legAdd_hyp_rhs_bound {x₁ x₂ : ℝ} (hx₁ : 1 < x₁) (hx₂ : 1 < x₂) (m : ℕ) :
    ∃ C : ℝ, ∀ ν : ℂ, ‖(-1:ℂ) ^ m * associatedP ν (-(m:ℂ)) x₁ * associatedP ν m x₂‖ ≤
      C * Real.exp ((Real.log (2 * x₁) + Real.log (2 * x₂) + 1) * |ν.re| + 1 * |ν.im|) := by
  have hl1 : 0 ≤ Real.log (2 * x₁) := Real.log_nonneg (by linarith)
  have hl2 : 0 ≤ Real.log (2 * x₂) := Real.log_nonneg (by linarith)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨1, fun ν => ?_⟩
    rw [pow_zero, one_mul, Nat.cast_zero, neg_zero, norm_mul]
    have e1 := (legAdd_norm_associatedP_nat_le ν 0 hx₁).trans_eq (by
      rw [poch_zero, norm_one, one_mul, legAdd_rpow_eq_exp (by linarith)])
    have e2 := (legAdd_norm_associatedP_nat_le ν 0 hx₂).trans_eq (by
      rw [poch_zero, norm_one, one_mul, legAdd_rpow_eq_exp (by linarith)])
    simp only [Nat.cast_zero] at e1 e2
    calc ‖associatedP ν 0 x₁‖ * ‖associatedP ν 0 x₂‖
        ≤ Real.exp (Real.log (2 * x₁) * |ν.re|) * Real.exp (Real.log (2 * x₂) * |ν.re|) :=
          mul_le_mul e1 e2 (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ 1 * Real.exp ((Real.log (2 * x₁) + Real.log (2 * x₂) + 1) * |ν.re| + 1 * |ν.im|) := by
          rw [← Real.exp_add]
          refine (Real.exp_le_exp.mpr ?_).trans (le_of_eq (one_mul _).symm)
          nlinarith [abs_nonneg ν.re, abs_nonneg ν.im]
  · set C₁ := ‖((x₁:ℂ) ^ 2 - 1) ^ (-(m:ℂ) / 2) / Gamma m‖ * ((x₁ - 1) ^ (m - 1) * (x₁ - 1))
    have hC₁ : 0 ≤ C₁ := by
      have : 0 ≤ x₁ - 1 := by linarith
      positivity
    refine ⟨C₁ * (m ! * Real.exp m), fun ν => ?_⟩
    have e1 : ‖associatedP ν (-(m:ℂ)) x₁‖ ≤ C₁ * Real.exp (Real.log (2 * x₁) * |ν.re|) := by
      refine (legAdd_norm_associatedP_neg_le ν hm hx₁).trans_eq ?_
      rw [legAdd_rpow_eq_exp (by linarith)]; ring
    have e2 : ‖associatedP ν m x₂‖ ≤ m ! * Real.exp m * Real.exp ‖ν‖ *
        Real.exp (Real.log (2 * x₂) * |ν.re|) := by
      refine (legAdd_norm_associatedP_nat_le ν m hx₂).trans ?_
      rw [legAdd_rpow_eq_exp (by linarith)]
      gcongr
      exact legAdd_norm_poch_le ν m
    have hn : ‖ν‖ ≤ |ν.re| + |ν.im| := norm_le_abs_re_add_abs_im ν
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc ‖associatedP ν (-(m:ℂ)) x₁‖ * ‖associatedP ν m x₂‖
        ≤ (C₁ * Real.exp (Real.log (2 * x₁) * |ν.re|)) * (m ! * Real.exp m * Real.exp ‖ν‖ *
            Real.exp (Real.log (2 * x₂) * |ν.re|)) :=
          mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
      _ = C₁ * (m ! * Real.exp m) * Real.exp (Real.log (2 * x₁) * |ν.re| + ‖ν‖ +
            Real.log (2 * x₂) * |ν.re|) := by
          rw [Real.exp_add, Real.exp_add]; ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          nlinarith [abs_nonneg ν.re, abs_nonneg ν.im]


/-- `∫_{-π}^{π} e^{ikt} dt = 2π δ_{k0}` for integer `k`. -/
theorem legAdd_integral_exp_int (k : ℤ) :
    (∫ t : ℝ in (-π)..π, exp (k * t * I)) = if k = 0 then 2 * (π:ℂ) else 0 := by
  split_ifs with hk
  · subst hk; simp; ring
  · have hc : (k:ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hk) I_ne_zero
    have h := integral_exp_mul_complex (a := -π) (b := π) hc
    have he : exp ((k:ℂ) * I * ((π:ℝ):ℂ)) = exp ((k:ℂ) * I * ((-π:ℝ):ℂ)) := by
      have := legAdd_exp_pi (-k)
      push_cast at this ⊢
      rw [show (k:ℂ) * I * π = -(-(k:ℂ) * π * I) by ring,
        show (k:ℂ) * I * -π = -(-(k:ℂ) * -π * I) by ring, this]
    rw [show (fun t : ℝ => exp ((k:ℂ) * t * I)) = fun t : ℝ => exp ((k:ℂ) * I * t) by
      funext t; ring_nf, h, he, sub_self, zero_div]

/-- Linearity of the Fourier coefficient: sums. -/
theorem legAdd_coeff_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (m : ℤ) :
    legAdd_coeff (fun t => f t + g t) m = legAdd_coeff f m + legAdd_coeff g m := by
  simp only [legAdd_coeff, mul_add]
  rw [intervalIntegral.integral_add, mul_add]
  · exact ((by fun_prop : Continuous fun t : ℝ => exp (-((m:ℂ) * t * I))).mul
      hf).intervalIntegrable _ _
  · exact ((by fun_prop : Continuous fun t : ℝ => exp (-((m:ℂ) * t * I))).mul
      hg).intervalIntegrable _ _

/-- Linearity of the Fourier coefficient: scalars. -/
theorem legAdd_coeff_const_mul (c : ℂ) (f : ℝ → ℂ) (m : ℤ) :
    legAdd_coeff (fun t => c * f t) m = c * legAdd_coeff f m := by
  simp only [legAdd_coeff]
  rw [show (fun t : ℝ => exp (-((m:ℂ) * t * I)) * (c * f t)) =
    fun t : ℝ => c * (exp (-((m:ℂ) * t * I)) * f t) by funext t; ring,
    intervalIntegral.integral_const_mul]
  ring

/-- Linearity of the Fourier coefficient: finite sums. -/
theorem legAdd_coeff_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℂ) (hF : ∀ i, Continuous (F i))
    (m : ℤ) : legAdd_coeff (fun t => ∑ i ∈ s, F i t) m = ∑ i ∈ s, legAdd_coeff (F i) m := by
  simp only [legAdd_coeff, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum, Finset.mul_sum]
  intro i _
  exact ((by fun_prop : Continuous fun t : ℝ => exp (-((m:ℂ) * t * I))).mul
    (hF i)).intervalIntegrable _ _

/-- The Fourier coefficients of a constant. -/
theorem legAdd_coeff_const (a : ℂ) (m : ℕ) :
    legAdd_coeff (fun _ => a) m = if m = 0 then a else 0 := by
  have h := legAdd_integral_exp_int (-(m:ℤ))
  rw [legAdd_coeff, show (fun t : ℝ => exp (-(((m:ℤ):ℂ) * t * I)) * a) =
    fun t : ℝ => a * exp (((-(m:ℤ) : ℤ):ℂ) * t * I) by funext t; push_cast; ring_nf,
    intervalIntegral.integral_const_mul, h]
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  by_cases hm : m = 0
  · subst hm; simp; field_simp
  · simp [hm]

/-- The Fourier coefficients of `cos (j t)`, `j ≥ 1`. -/
theorem legAdd_coeff_cos {j : ℕ} (hj : 1 ≤ j) (m : ℕ) :
    legAdd_coeff (fun t : ℝ => cos ((j:ℂ) * t)) m = if j = m then 1 / 2 else 0 := by
  have h1 := legAdd_integral_exp_int ((j:ℤ) - m)
  have h2 := legAdd_integral_exp_int (-((j:ℤ) + m))
  have hsplit : (fun t : ℝ => exp (-(((m:ℤ):ℂ) * t * I)) * cos ((j:ℂ) * t)) =
      fun t : ℝ => (1/2:ℂ) * exp ((((j:ℤ) - m : ℤ):ℂ) * t * I) +
        (1/2:ℂ) * exp (((-((j:ℤ) + m) : ℤ):ℂ) * t * I) := by
    funext t
    have e1 : exp ((((j:ℤ) - m : ℤ):ℂ) * t * I) =
        exp (-(((m:ℤ):ℂ) * t * I)) * exp ((j:ℂ) * t * I) := by
      rw [← exp_add]; congr 1; push_cast; ring
    have e2 : exp (((-((j:ℤ) + m) : ℤ):ℂ) * t * I) =
        exp (-(((m:ℤ):ℂ) * t * I)) * exp (-((j:ℂ) * t) * I) := by
      rw [← exp_add]; congr 1; push_cast; ring
    rw [e1, e2, Complex.cos]
    ring
  rw [legAdd_coeff, hsplit, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, h1, h2]
  · have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    have hjm : -((j:ℤ) + m) ≠ 0 := by omega
    simp only [hjm, ite_false, mul_zero, add_zero]
    by_cases h : j = m
    · subst h; simp; field_simp
    · have : (j:ℤ) - m ≠ 0 := by omega
      simp [this, h]
  · exact ((by fun_prop : Continuous fun t : ℝ =>
      exp ((((j:ℤ) - m : ℤ):ℂ) * t * I)).const_mul _).intervalIntegrable _ _
  · exact ((by fun_prop : Continuous fun t : ℝ =>
      exp (((-((j:ℤ) + m) : ℤ):ℂ) * t * I)).const_mul _).intervalIntegrable _ _


open DLMF.OrthogonalPolynomials.LegendreAddition in
/-- The Fourier coefficients of the finite Legendre angular kernel are its coefficients. -/
theorem legAdd_coeff_kernel (n : ℕ) (x y s t : ℂ) (m : ℕ) :
    legAdd_coeff (fun u : ℝ => kernel n x y s t u) m = coeff n m x y s t := by
  have hc : ∀ k : ℕ, Continuous fun u : ℝ => coeff n (k+1) x y s t * cos (((k:ℂ)+1) * u) :=
    fun k => by fun_prop
  have hg : Continuous fun u : ℝ => ∑ k ∈ Finset.range n,
      coeff n (k+1) x y s t * cos (((k:ℂ)+1) * u) := continuous_finsetSum _ fun k _ => hc k
  unfold kernel
  rw [legAdd_coeff_add (f := fun _ : ℝ => coeff n 0 x y s t) (g := fun u : ℝ => 2 *
      ∑ k ∈ Finset.range n, coeff n (k+1) x y s t * cos (((k:ℂ)+1) * u)) continuous_const
      (continuous_const.mul hg), legAdd_coeff_const,
    legAdd_coeff_const_mul (f := fun u : ℝ => ∑ k ∈ Finset.range n,
      coeff n (k+1) x y s t * cos (((k:ℂ)+1) * u)),
    legAdd_coeff_sum (F := fun k (u : ℝ) => coeff n (k+1) x y s t * cos (((k:ℂ)+1) * u)) _
      fun k => hc k]
  have hterm : ∀ k : ℕ, legAdd_coeff (fun u : ℝ => coeff n (k+1) x y s t *
      cos (((k:ℂ)+1) * u)) m = if k + 1 = m then coeff n (k+1) x y s t / 2 else 0 := by
    intro k
    rw [legAdd_coeff_const_mul]
    have := legAdd_coeff_cos (j := k + 1) (by omega) m
    push_cast at this
    rw [this]
    split_ifs <;> ring
  simp only [hterm]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [show (if m = 0 then coeff n 0 x y s t else 0) = 0 by simp; omega, zero_add]
    obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    simp only [add_left_inj, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with hp
    · ring
    · rw [coeff_eq_zero (by omega)]; ring


open DLMF.OrthogonalPolynomials.LegendreAddition in
/-- Integer degree and order on `(1, ∞)`: `P^m_n(x) = (x²-1)^{m/2} P_n^{(m)}(x)`. -/
theorem legAdd_associatedP_nat_nat (n m : ℕ) {x : ℝ} (hx : 1 < x) :
    associatedP n m x = (Real.sqrt (x ^ 2 - 1) : ℂ) ^ m * jet n m x := by
  have hz := legInt_one_lt_mem hx
  have hev : associatedP (n:ℂ) 0 =ᶠ[𝓝 (x:ℂ)] DLMF.OrthogonalPolynomials.legendrePolyP n := by
    filter_upwards [(isOpen_slitPlane.preimage (by fun_prop : Continuous fun w : ℂ => w-1)).mem_nhds
      hz] with w hw
    rw [associatedP_zero_order _ hw, legendreP_nat n (one_add_mem_slitPlane_of_sub_one hw)]
  rw [associatedP_nat_order_derivative n m hz, hev.iteratedDeriv_eq,
    legInt_legendreBranchPower_real _ hx]
  have hpow : ((x:ℂ)^2-1)^((m:ℂ)/2) = (Real.sqrt (x^2-1):ℂ)^m := by
    rw [show (x:ℂ)^2-1 = ((x^2-1:ℝ):ℂ) by push_cast; ring,
      show (m:ℂ)/2 = (((m:ℝ)/2 : ℝ):ℂ) by push_cast; ring, ← ofReal_cpow (by nlinarith),
      ← ofReal_pow]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by nlinarith)]
    ring_nf
  rw [hpow]; rfl

/-- `√(cosh² ξ - 1) = sinh ξ` for `ξ ≥ 0`. -/
theorem legAdd_sqrt_cosh_sq {ξ : ℝ} (h : 0 ≤ ξ) : Real.sqrt (Real.cosh ξ ^ 2 - 1) = Real.sinh ξ := by
  rw [Real.cosh_sq, add_sub_cancel_right, Real.sqrt_sq (Real.sinh_nonneg_iff.2 h)]

open DLMF.OrthogonalPolynomials.LegendreAddition in
/-- The hyperbolic addition theorem at integer degree, coefficientwise. -/
theorem legAdd_hyp_nat (n : ℕ) {ξ₁ ξ₂ : ℝ} (h1 : 0 < ξ₁) (h2 : 0 < ξ₂) (m : ℕ) :
    legAdd_coeff (fun t => associatedP (n:ℂ) 0 (legAdd_hX ξ₁ ξ₂ t)) m =
      (-1:ℂ) ^ m * associatedP n (-(m:ℂ)) (Real.cosh ξ₁) * associatedP n m (Real.cosh ξ₂) := by
  have hsq : ∀ ξ : ℝ, (I * (Real.sinh ξ : ℂ)) ^ 2 = 1 - (Real.cosh ξ : ℂ) ^ 2 := by
    intro ξ
    have h' : ((Real.cosh ξ : ℝ) : ℂ) ^ 2 = (Real.sinh ξ : ℂ) ^ 2 + 1 := by
      rw [← ofReal_pow, Real.cosh_sq]; push_cast; ring
    rw [mul_pow, I_sq, h']; ring
  have hfun : (fun u : ℝ => associatedP (n:ℂ) 0 (legAdd_hX ξ₁ ξ₂ u)) =
      fun u : ℝ => kernel n (Real.cosh ξ₁) (Real.cosh ξ₂) (I * Real.sinh ξ₁) (I * Real.sinh ξ₂) u := by
    funext u
    obtain ⟨hX1, -⟩ := legAdd_hX_mem h1.le h2.le u
    rw [legAdd_associatedP_zero hX1, legendreP_nat n (Or.inl (by simp; linarith)),
      ← legendre_eq_kernel n _ _ _ _ u (hsq ξ₁) (hsq ξ₂)]
    congr 1
    have hI : (I * (Real.sinh ξ₁ : ℂ)) * (I * Real.sinh ξ₂) = -((Real.sinh ξ₁ : ℂ) * Real.sinh ξ₂) := by
      rw [show (I * (Real.sinh ξ₁ : ℂ)) * (I * Real.sinh ξ₂) = I ^ 2 * ((Real.sinh ξ₁ : ℂ) * Real.sinh ξ₂) by ring,
        I_sq]; ring
    rw [hI, legAdd_hX]
    push_cast
    ring
  have hc1 : (1:ℝ) < Real.cosh ξ₁ := Real.one_lt_cosh.2 h1.ne'
  have hc2 : (1:ℝ) < Real.cosh ξ₂ := Real.one_lt_cosh.2 h2.ne'
  rw [hfun, legAdd_coeff_kernel]
  rcases le_or_gt m n with hmn | hmn
  · have hG : ∀ j : ℕ, (n:ℂ) - m + 1 ≠ -j := by
      intro j h
      have : ((n - m + 1 + j : ℕ) : ℂ) = 0 := by push_cast [Nat.cast_sub hmn]; linear_combination h
      exact absurd (Nat.cast_eq_zero.1 this) (by omega)
    rw [associatedP_negative_integer_order (n:ℂ) m hG (legInt_one_lt_mem hc1),
      show (n:ℂ) - m + 1 = ((n - m : ℕ) : ℂ) + 1 by push_cast [Nat.cast_sub hmn]; ring,
      show (n:ℂ) + m + 1 = ((n + m : ℕ) : ℂ) + 1 by push_cast; ring,
      Gamma_nat_eq_factorial, Gamma_nat_eq_factorial,
      legAdd_associatedP_nat_nat n m hc1, legAdd_associatedP_nat_nat n m hc2,
      legAdd_sqrt_cosh_sq h1.le, legAdd_sqrt_cosh_sq h2.le]
    simp only [coeff, weight]
    rw [show (I * (Real.sinh ξ₁ : ℂ) * (I * Real.sinh ξ₂)) = -((Real.sinh ξ₁ : ℂ) * Real.sinh ξ₂) by
      rw [show (I * (Real.sinh ξ₁ : ℂ)) * (I * Real.sinh ξ₂) = I ^ 2 * ((Real.sinh ξ₁ : ℂ) * Real.sinh ξ₂) by ring,
        I_sq]; ring, neg_pow, mul_pow]
    ring
  · rw [coeff_eq_zero hmn, legAdd_associatedP_nat_nat n m hc2, jet_eq_zero hmn]
    simp


/-- The Fourier coefficients of `φ ↦ P_ν(cosh ξ₁ cosh ξ₂ - sinh ξ₁ sinh ξ₂ cos φ)`, for every
complex degree (Carlson's theorem from the integer case). -/
theorem legAdd_hyp_coeff_eq (ν : ℂ) {ξ₁ ξ₂ : ℝ} (h1 : 0 < ξ₁) (h2 : 0 < ξ₂) (m : ℕ) :
    legAdd_coeff (fun t => associatedP ν 0 (legAdd_hX ξ₁ ξ₂ t)) m =
      (-1:ℂ) ^ m * associatedP ν (-(m:ℂ)) (Real.cosh ξ₁) * associatedP ν m (Real.cosh ξ₂) := by
  have hc1 : (1:ℝ) < Real.cosh ξ₁ := Real.one_lt_cosh.2 h1.ne'
  have hc2 : (1:ℝ) < Real.cosh ξ₂ := Real.one_lt_cosh.2 h2.ne'
  have hz : ∀ x : ℝ, 1 < x → (1 - (x:ℂ)) / 2 ∈ cutPlane := fun x hx => by
    rw [show (1 - (x:ℂ)) / 2 = (((1 - x) / 2 : ℝ) : ℂ) by push_cast; ring]
    exact legAdd_ofReal_mem_cutPlane (by linarith)
  obtain ⟨C, hC⟩ := legAdd_hyp_rhs_bound hc1 hc2 m
  set A := Real.log (2 * Real.cosh ξ₁) + Real.log (2 * Real.cosh ξ₂) + 1
  set K := 2 * Real.cosh (ξ₁ + ξ₂)
  have hK : 1 ≤ K := by have := Real.one_le_cosh (ξ₁ + ξ₂); simp only [K]; linarith
  have hlK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hA : 0 ≤ A := by
    have := Real.log_nonneg (by linarith : (1:ℝ) ≤ 2 * Real.cosh ξ₁)
    have := Real.log_nonneg (by linarith : (1:ℝ) ≤ 2 * Real.cosh ξ₂)
    simp only [A]; linarith
  have key := legAdd_carlson (f := fun ν => legAdd_coeff (fun t => associatedP ν 0
      (legAdd_hX ξ₁ ξ₂ t)) m - (-1:ℂ) ^ m * associatedP ν (-(m:ℂ)) (Real.cosh ξ₁) *
      associatedP ν m (Real.cosh ξ₂))
    ((legAdd_hyp_coeff_differentiable h1.le h2.le m).sub
      (((differentiable_const _).mul (legAdd_differentiable_associatedP _ (hz _ hc1))).mul
        (legAdd_differentiable_associatedP _ (hz _ hc2))))
    (C := 1 + |C|) (A := Real.log K + A) (B := 1) (by linarith) zero_le_one
    (by linarith [Real.pi_gt_three])
    (fun w _ => by
      refine (norm_sub_le _ _).trans ?_
      have e1 := legAdd_hyp_coeff_bound w h1.le h2.le m
      rw [show (2 * Real.cosh (ξ₁ + ξ₂)) = 2 * (Real.cosh (ξ₁ + ξ₂)) from rfl,
        legAdd_rpow_eq_exp (Real.cosh_pos _)] at e1
      have e2 := hC w
      have hE1 : Real.exp (Real.log K * |w.re|) ≤
          Real.exp ((Real.log K + A) * |w.re| + 1 * |w.im|) :=
        Real.exp_le_exp.mpr (by nlinarith [abs_nonneg w.re, abs_nonneg w.im])
      have hE2 : Real.exp (A * |w.re| + 1 * |w.im|) ≤
          Real.exp ((Real.log K + A) * |w.re| + 1 * |w.im|) :=
        Real.exp_le_exp.mpr (by nlinarith [abs_nonneg w.re, abs_nonneg w.im])
      have hCa : C * Real.exp (A * |w.re| + 1 * |w.im|) ≤
          |C| * Real.exp ((Real.log K + A) * |w.re| + 1 * |w.im|) :=
        (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le).trans
          (mul_le_mul_of_nonneg_left hE2 (abs_nonneg C))
      have e1' : ‖legAdd_coeff (fun t => associatedP w 0 (legAdd_hX ξ₁ ξ₂ t)) m‖ ≤
          Real.exp (Real.log K * |w.re|) := e1
      nlinarith)
    (fun n => by rw [legAdd_hyp_nat n h1 h2 m, sub_self]) ν
  exact sub_eq_zero.mp key

/-- **Addition theorem for `P_ν` on `(1, ∞)`** (DLMF 14.18.4), in the form of the project. -/
theorem legAdd_associatedP_addition (ν : ℂ) {ξ₁ ξ₂ : ℝ} (h1 : 0 < ξ₁) (h2 : 0 < ξ₂) (phi : ℝ) :
    HasSum (fun j : ℕ => let m := j + 1; 2 * (-1) ^ m * associatedP ν (-m) (Real.cosh ξ₁) *
      associatedP ν m (Real.cosh ξ₂) * Real.cos (m * phi))
      (associatedP ν 0 (Real.cosh ξ₁ * Real.cosh ξ₂ - Real.sinh ξ₁ * Real.sinh ξ₂ * Real.cos phi) -
        associatedP ν 0 (Real.cosh ξ₁) * associatedP ν 0 (Real.cosh ξ₂)) := by
  have hper : Function.Periodic (fun t : ℝ => associatedP ν 0 (legAdd_hX ξ₁ ξ₂ t)) (2 * π) :=
    fun t => by simp only [legAdd_hX, Real.cos_add_two_pi]
  have hev : ∀ t, (fun t : ℝ => associatedP ν 0 (legAdd_hX ξ₁ ξ₂ t)) (-t) =
      (fun t : ℝ => associatedP ν 0 (legAdd_hX ξ₁ ξ₂ t)) t :=
    fun t => by simp only [legAdd_hX, Real.cos_neg]
  have hF := legAdd_hasSum_cos (legAdd_hX_contDiff ν h1.le h2.le) hper hev phi
  have h0 := legAdd_hyp_coeff_eq ν h1 h2 0
  simp only [pow_zero, one_mul, Nat.cast_zero, neg_zero] at h0
  convert hF using 1
  · funext j
    rw [legAdd_hyp_coeff_eq ν h1 h2 (j + 1)]
    push_cast
    ring
  · rw [h0, legAdd_hX]; push_cast; rfl

/-! ### The Ferrers case (14.18.1) -/

/-- Wallis' integral in Gamma form: `∫₀^π sin^{2n} t dt = √π Γ(n + 1/2)/n!`. -/
theorem legAdd_integral_sin_pow_even (n : ℕ) :
    (∫ t : ℝ in (0:ℝ)..π, (((Real.sin t) ^ 2 : ℝ) : ℂ) ^ n) =
      (Real.sqrt π : ℂ) * Gamma (1 / 2 + n) / n ! := by
  have hR : ∀ n : ℕ, (∫ t : ℝ in (0:ℝ)..π, (((Real.sin t) ^ 2 : ℝ) : ℂ) ^ n) =
      ((∫ t : ℝ in (0:ℝ)..π, Real.sin t ^ (2 * n) : ℝ) : ℂ) := by
    intro n
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t _ => ?_
    push_cast; ring
  rw [hR]
  induction n with
  | zero =>
    simp only [mul_zero, pow_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one,
      CharP.cast_eq_zero, add_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    rw [legendre_Gamma_one_half, ← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  | succ n ih =>
    have h := integral_sin_pow (a := 0) (b := π) (n := 2 * n)
    simp only [Real.sin_zero, Real.sin_pi, zero_pow (Nat.succ_ne_zero _), zero_mul, sub_self,
      zero_div, zero_add] at h
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, h, ofReal_mul, ih]
    have hG : Gamma (1 / 2 + ((n + 1 : ℕ) : ℂ)) = (1 / 2 + n) * Gamma (1 / 2 + n) := by
      rw [show (1:ℂ) / 2 + ((n + 1 : ℕ) : ℂ) = (1 / 2 + n) + 1 by push_cast; ring,
        Gamma_add_one _ (by
          intro h0; have := congrArg Complex.re h0; simp at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])]
    rw [hG, Nat.factorial_succ]
    push_cast
    field_simp
    ring


/-- `𝐅(ν+1, -ν; 1; s) = π^{-1/2} ∫₀^π 𝐅(ν+1, -ν; 1/2; s sin² t) dt` for `0 ≤ s < 1`
(the Mehler–Dirichlet integral in disguise). -/
theorem legAdd_regGHG_one_eq_integral (ν : ℂ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    regularizedGaussHGFun (ν + 1) (-ν) 1 s = 1 / (Real.sqrt π : ℂ) *
      ∫ t : ℝ in (0:ℝ)..π, regularizedGaussHGFun (ν + 1) (-ν) (1 / 2) ((s * Real.sin t ^ 2 : ℝ)) := by
  have hsn : ‖(s:ℂ)‖ < 1 := by rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]; exact hs1
  set e : ℕ → ℂ := fun n => (ascPochhammer ℂ n).eval (ν + 1) * (ascPochhammer ℂ n).eval (-ν) *
    (s:ℂ) ^ n / n.factorial * (Gamma (1 / 2 + n))⁻¹ with he_def
  have he : Summable (fun n => ‖e n‖) := summable_norm_regularizedGaussHGFun_term _ _ _ hsn
  set F : ℕ → ℝ → ℂ := fun n t => e n * (((Real.sin t) ^ 2 : ℝ) : ℂ) ^ n with hF_def
  have hFc : ∀ n, Continuous (F n) := fun n => by simp only [hF_def]; fun_prop
  have hs := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := π) (μ := MeasureTheory.volume) (F := F)
    (f := fun t => regularizedGaussHGFun (ν + 1) (-ν) (1 / 2) ((s * Real.sin t ^ 2 : ℝ)))
    (fun n _ => ‖e n‖) (fun n => (hFc n).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun t _ => by
      simp only [hF_def, norm_mul, norm_pow]
      have : ‖(((Real.sin t) ^ 2 : ℝ) : ℂ)‖ ≤ 1 := by
        rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (Real.cos t)]
      calc ‖e n‖ * ‖(((Real.sin t) ^ 2 : ℝ) : ℂ)‖ ^ n ≤ ‖e n‖ * 1 ^ n := by gcongr
        _ = ‖e n‖ := by simp)
    (Filter.Eventually.of_forall fun t _ => he)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ => by
      have hz : ‖(((s * Real.sin t ^ 2 : ℝ)) : ℂ)‖ < 1 := by
        rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h1 : Real.sin t ^ 2 ≤ 1 := by nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (Real.cos t)]
        nlinarith
      refine (hasSum_regularizedGaussHGFun (ν + 1) (-ν) (1 / 2) hz).congr_fun fun n => ?_
      simp only [hF_def, he_def]
      push_cast
      ring)
  have hint : ∀ n, (∫ t : ℝ in (0:ℝ)..π, F n t) = (Real.sqrt π : ℂ) *
      ((ascPochhammer ℂ n).eval (ν + 1) * (ascPochhammer ℂ n).eval (-ν) * (s:ℂ) ^ n /
        n.factorial * (Gamma (1 + n))⁻¹) := by
    intro n
    simp only [hF_def]
    rw [intervalIntegral.integral_const_mul, legAdd_integral_sin_pow_even,
      show (1:ℂ) + n = (n:ℂ) + 1 by ring, Gamma_nat_eq_factorial]
    have hG : Gamma (1 / 2 + n) ≠ 0 := Gamma_ne_zero_of_re_pos (by
      simp; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    simp only [he_def]
    generalize Gamma (1 / 2 + n) = G at hG ⊢
    field_simp
  simp only [hint] at hs
  have h1 := (hasSum_regularizedGaussHGFun (ν + 1) (-ν) 1 hsn).mul_left (Real.sqrt π : ℂ)
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 Real.pi_pos).ne'
  rw [hs.unique h1]
  field_simp


/-- `(1 - cos θ)/2 = sin²(θ/2)`. -/
theorem legAdd_one_sub_cos_half (θ : ℝ) : (1 - Real.cos θ) / 2 = Real.sin (θ / 2) ^ 2 := by
  have h := Real.cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  have := Real.sin_sq_add_cos_sq (θ / 2)
  linarith

/-- **Sharp exponential bound for Ferrers functions of order zero**:
`|𝖯_ν(cos θ)| ≤ e^{θ |Im ν|} / cos(θ/2)` for `0 ≤ θ < π` and all complex `ν`. -/
theorem legAdd_norm_ferrersP_zero_le (ν : ℂ) {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ < π) :
    ‖ferrersP ν 0 (Real.cos θ)‖ ≤ Real.exp (θ * |ν.im|) / Real.cos (θ / 2) := by
  set c := Real.sin (θ / 2) with hc
  have hc0 : 0 ≤ c := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hc1 : c < 1 := by
    rw [hc, ← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) le_rfl (by linarith)
  have hcos : 0 < Real.cos (θ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs1 : c ^ 2 < 1 := by nlinarith
  have hF : ferrersP ν 0 (Real.cos θ) = regularizedGaussHGFun (ν + 1) (-ν) 1 ((c ^ 2 : ℝ)) := by
    simp only [ferrersP, zero_div, cpow_zero, one_mul, sub_zero]
    rw [show (1 - ((Real.cos θ : ℝ) : ℂ)) / 2 = ((c ^ 2 : ℝ) : ℂ) by
      rw [hc, ← legAdd_one_sub_cos_half]; push_cast; ring]
    exact regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by
      rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hs1)
  rw [hF, legAdd_regGHG_one_eq_integral ν (sq_nonneg c) hs1]
  have hsq : (Real.sqrt π : ℝ) ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  have hsqp : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  set B := Real.exp (θ * |ν.im|) / Real.cos (θ / 2) with hB
  have hpt : ∀ t : ℝ, ‖regularizedGaussHGFun (ν + 1) (-ν) (1 / 2) ((c ^ 2 * Real.sin t ^ 2 : ℝ))‖ ≤
      B / Real.sqrt π := by
    intro t
    set y := c * Real.sin t
    have hy1 : |y| ≤ c := by
      rw [abs_mul, abs_of_nonneg hc0]
      exact mul_le_of_le_one_right hc0 (Real.abs_sin_le_one t)
    set w := Real.arcsin y
    have hw : |w| ≤ θ / 2 := by
      have hθ2 : Real.arcsin c = θ / 2 := by
        rw [hc]; exact Real.arcsin_sin (by linarith) (by linarith)
      rw [abs_le]
      constructor
      · have := Real.arcsin_le_arcsin (neg_le_of_abs_le hy1)
        rw [Real.arcsin_neg, hθ2] at this; exact this
      · have := Real.arcsin_le_arcsin (le_of_abs_le hy1)
        rw [hθ2] at this; exact this
    have hwπ : |w| < π / 2 := by linarith
    have hsw : Real.sin w = y := Real.sin_arcsin (by linarith [neg_abs_le y]) (by
      linarith [le_abs_self y])
    have hcw : Real.cos (θ / 2) ≤ Real.cos w := by
      rw [← Real.cos_abs w]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) hw
    have hcw0 : 0 < Real.cos w := hcos.trans_le hcw
    have hc12 : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [show ((c ^ 2 * Real.sin t ^ 2 : ℝ) : ℂ) = (Real.sin w : ℂ) ^ 2 by
        rw [hsw]; simp only [y]; push_cast; ring,
      regularizedGaussHGFun_eq_div_Gamma hc12, legendre_Gamma_one_half,
      show -ν = 1 - (ν + 1) by ring, sin_sq_cos_quotient (ν + 1) hwπ, norm_div, norm_div,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hcw0, abs_of_pos hsqp]
    gcongr
    rw [hB]
    refine div_le_div₀ (Real.exp_pos _).le ?_ hcos hcw
    refine (legFour_norm_cos_le _).trans (Real.exp_le_exp.mpr ?_)
    have him : ((2 * (ν + 1) - 1) * (w : ℂ)).im = 2 * ν.im * w := by simp
    rw [him, abs_mul, abs_mul, abs_two]
    nlinarith [abs_nonneg ν.im]
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π)
    (C := B / Real.sqrt π)
    (f := fun t : ℝ => regularizedGaussHGFun (ν + 1) (-ν) (1 / 2) ((c ^ 2 * Real.sin t ^ 2 : ℝ)))
    (fun t _ => hpt t)
  rw [sub_zero, abs_of_pos Real.pi_pos] at hI
  rw [norm_mul, show ‖(1:ℂ) / (Real.sqrt π : ℂ)‖ = 1 / Real.sqrt π by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqp]]
  calc 1 / Real.sqrt π * ‖∫ t : ℝ in (0:ℝ)..π,
        regularizedGaussHGFun (ν + 1) (-ν) (1 / 2) ((c ^ 2 * Real.sin t ^ 2 : ℝ))‖
      ≤ 1 / Real.sqrt π * (B / Real.sqrt π * π) := by gcongr
    _ = B * (π / Real.sqrt π ^ 2) := by ring
    _ = B := by rw [hsq, div_self Real.pi_ne_zero, mul_one]


/-- The bound `legAdd_norm_ferrersP_zero_le` on `[cos Θ, 1]`. -/
theorem legAdd_norm_ferrersP_zero_le_of_mem (ν : ℂ) {Θ x : ℝ} (h0 : 0 ≤ Θ) (hπ : Θ < π)
    (hx1 : Real.cos Θ ≤ x) (hx2 : x ≤ 1) :
    ‖ferrersP ν 0 x‖ ≤ Real.exp (Θ * |ν.im|) / Real.cos (Θ / 2) := by
  have hxm : -1 ≤ x := le_trans (Real.neg_one_le_cos Θ) hx1
  set γ := Real.arccos x
  have hγ0 : 0 ≤ γ := Real.arccos_nonneg x
  have hγ : γ ≤ Θ := by
    have := Real.arccos_le_arccos hx1
    rwa [Real.arccos_cos h0 (by linarith)] at this
  have hxγ : Real.cos γ = x := Real.cos_arccos hxm hx2
  have h := legAdd_norm_ferrersP_zero_le ν hγ0 (by linarith)
  rw [hxγ] at h
  refine h.trans (div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (by
    nlinarith [abs_nonneg ν.im])) (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
    (Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)))

/-- The argument `cos θ₁ cos θ₂ + sin θ₁ sin θ₂ cos t` of the Ferrers addition theorem. -/
def legAdd_fY (θ₁ θ₂ t : ℝ) : ℝ :=
  Real.cos θ₁ * Real.cos θ₂ + Real.sin θ₁ * Real.sin θ₂ * Real.cos t

theorem legAdd_fY_mem {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂) (hs : θ₁ + θ₂ < π) (t : ℝ) :
    Real.cos (θ₁ + θ₂) ≤ legAdd_fY θ₁ θ₂ t ∧ legAdd_fY θ₁ θ₂ t ≤ 1 := by
  have hs1 : 0 ≤ Real.sin θ₁ := Real.sin_nonneg_of_nonneg_of_le_pi h1 (by linarith)
  have hs2 : 0 ≤ Real.sin θ₂ := Real.sin_nonneg_of_nonneg_of_le_pi h2 (by linarith)
  have hss := mul_nonneg hs1 hs2
  have hc1 := Real.cos_le_one t
  have hc2 := Real.neg_one_le_cos t
  have hsub := Real.cos_le_one (θ₁ - θ₂)
  rw [Real.cos_sub] at hsub
  rw [Real.cos_add]
  unfold legAdd_fY
  constructor <;> nlinarith

/-- The Ferrers function in hypergeometric form at order zero. -/
theorem legAdd_ferrersP_zero_eq (ν : ℂ) (x : ℝ) :
    ferrersP ν 0 x = regularizedGaussHG (ν + 1) (-ν) 1 ((1 - x) / 2) := by
  simp [ferrersP]

/-- The order-zero Ferrers function along `legAdd_fY` is `C²` in the angle. -/
theorem legAdd_fY_contDiff (ν : ℂ) {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂) (hs : θ₁ + θ₂ < π) :
    ContDiff ℝ 2 (fun t : ℝ => ferrersP ν 0 (legAdd_fY θ₁ θ₂ t)) := by
  have hG : DifferentiableOn ℂ (fun z => regularizedGaussHG (ν + 1) (-ν) 1 z) cutPlane :=
    DifferentiableOn.regularizedGaussHG (differentiableOn_const _) (differentiableOn_const _)
      (differentiableOn_const _) differentiableOn_id fun w hw => hw
  have hG2 : ContDiffOn ℝ 2 (fun z => regularizedGaussHG (ν + 1) (-ν) 1 z) cutPlane :=
    (hG.contDiffOn isOpen_cutPlane).restrict_scalars ℝ
  have hh : ContDiff ℝ 2 (fun t : ℝ => (((1 - legAdd_fY θ₁ θ₂ t) / 2 : ℝ) : ℂ)) := by
    refine ofRealCLM.contDiff.comp ?_
    unfold legAdd_fY
    exact (contDiff_const.sub (contDiff_const.add (contDiff_const.mul Real.contDiff_cos))).div_const 2
  have hc : -1 < Real.cos (θ₁ + θ₂) := by
    rw [← Real.cos_pi]; exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) le_rfl hs
  have := hG2.comp_contDiff hh fun t =>
    legAdd_ofReal_mem_cutPlane (by linarith [(legAdd_fY_mem h1 h2 hs t).1])
  convert this using 1
  funext t
  simp only [Function.comp, legAdd_ferrersP_zero_eq]
  congr 1; push_cast; ring

/-- `-1 < cos (θ₁ + θ₂)`. -/
theorem legAdd_neg_one_lt_cos {θ : ℝ} (h0 : 0 ≤ θ) (hs : θ < π) : -1 < Real.cos θ := by
  rw [← Real.cos_pi]; exact Real.cos_lt_cos_of_nonneg_of_le_pi h0 le_rfl hs

/-- Order-zero Ferrers values along `legAdd_fY` obey the sharp exponential bound. -/
theorem legAdd_fY_norm_le (ν : ℂ) {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂) (hs : θ₁ + θ₂ < π)
    (t : ℝ) : ‖ferrersP ν 0 (legAdd_fY θ₁ θ₂ t)‖ ≤
      Real.exp ((θ₁ + θ₂) * |ν.im|) / Real.cos ((θ₁ + θ₂) / 2) :=
  legAdd_norm_ferrersP_zero_le_of_mem ν (by linarith) hs (legAdd_fY_mem h1 h2 hs t).1
    (legAdd_fY_mem h1 h2 hs t).2

/-- Bound on the Fourier coefficients in the Ferrers case. -/
theorem legAdd_fer_coeff_bound (ν : ℂ) {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂) (hs : θ₁ + θ₂ < π)
    (m : ℤ) : ‖legAdd_coeff (fun t => ferrersP ν 0 (legAdd_fY θ₁ θ₂ t)) m‖ ≤
      Real.exp ((θ₁ + θ₂) * |ν.im|) / Real.cos ((θ₁ + θ₂) / 2) := by
  rw [legAdd_coeff, norm_mul]
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := -π) (b := π)
    (C := Real.exp ((θ₁ + θ₂) * |ν.im|) / Real.cos ((θ₁ + θ₂) / 2))
    (f := fun t : ℝ => exp (-((m:ℂ) * t * I)) * ferrersP ν 0 (legAdd_fY θ₁ θ₂ t))
    (fun t _ => by
      rw [norm_mul, show -((m:ℂ) * t * I) = ((-(m * t) : ℝ) : ℂ) * I by push_cast; ring,
        norm_exp_ofReal_mul_I, one_mul]
      exact legAdd_fY_norm_le ν h1 h2 hs t)
  have hπ := Real.pi_pos
  rw [abs_of_pos (by linarith : (0:ℝ) < π - -π)] at hI
  rw [show ‖(1:ℂ) / (2 * π)‖ = 1 / (2 * π) by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hπ]]
  calc 1 / (2 * π) * ‖∫ t : ℝ in (-π)..π, exp (-((m:ℂ) * t * I)) *
        ferrersP ν 0 (legAdd_fY θ₁ θ₂ t)‖
      ≤ 1 / (2 * π) * (Real.exp ((θ₁ + θ₂) * |ν.im|) / Real.cos ((θ₁ + θ₂) / 2) * (π - -π)) := by
        gcongr
    _ = _ := by field_simp; ring

/-- `ferrersP ν μ x` is entire in the degree for `x ∈ (-1, 1]`. -/
theorem legAdd_differentiable_ferrersP (μ : ℂ) {x : ℝ} (hx : -1 < x) :
    Differentiable ℂ (fun ν : ℂ => ferrersP ν μ x) := by
  unfold ferrersP
  refine (differentiable_const _).mul (differentiable_regularizedGaussHG_comp
    (A := fun ν : ℂ => ν + 1) (B := fun ν : ℂ => -ν) (C := fun _ => 1 - μ)
    (by fun_prop) (by fun_prop) (by fun_prop) ?_)
  rw [show (1 - (x:ℂ)) / 2 = (((1 - x) / 2 : ℝ) : ℂ) by push_cast; ring]
  exact legAdd_ofReal_mem_cutPlane (by linarith)

/-- The Fourier coefficients in the Ferrers case are entire in the degree. -/
theorem legAdd_fer_coeff_differentiable {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂) (hs : θ₁ + θ₂ < π)
    (m : ℤ) :
    Differentiable ℂ (fun ν => legAdd_coeff (fun t => ferrersP ν 0 (legAdd_fY θ₁ θ₂ t)) m) := by
  have hc := legAdd_neg_one_lt_cos (by linarith) hs
  have key : DifferentiableOn ℂ (fun ν => ∫ t in (-π)..π, exp (-((m:ℂ) * t * I)) *
      ferrersP ν 0 (legAdd_fY θ₁ θ₂ t)) univ := by
    apply Complex.differentiableOn_intervalIntegral_of_locally_dominated isOpen_univ
    · intro ν _
      exact ((by fun_prop : Continuous fun t : ℝ => exp (-((m:ℂ) * t * I))).mul
        (legAdd_fY_contDiff ν h1 h2 hs).continuous).aestronglyMeasurable
    · refine ae_of_all _ fun t => ?_
      exact ((differentiable_const _).mul (legAdd_differentiable_ferrersP 0
        (by linarith [(legAdd_fY_mem h1 h2 hs t).1]))).differentiableOn
    · intro ν₀ _
      refine ⟨Metric.ball ν₀ 1, Metric.ball_mem_nhds _ one_pos,
        fun _ => Real.exp ((θ₁ + θ₂) * (|ν₀.im| + 1)) / Real.cos ((θ₁ + θ₂) / 2),
        integrableOn_const (by rw [uIoc_of_le (by linarith [Real.pi_pos])]; simp), ae_of_all _ ?_⟩
      intro t y hy
      rw [norm_mul, show -((m:ℂ) * t * I) = ((-(m * t) : ℝ) : ℂ) * I by push_cast; ring,
        norm_exp_ofReal_mul_I, one_mul]
      refine (legAdd_fY_norm_le y h1 h2 hs t).trans (div_le_div_of_nonneg_right
        (Real.exp_le_exp.mpr ?_) (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).le)
      have hd : ‖y - ν₀‖ < 1 := by simpa [dist_eq_norm] using hy
      have h3 := abs_im_le_norm (y - ν₀)
      rw [sub_im] at h3
      have h4 := abs_sub_abs_le_abs_sub y.im ν₀.im
      have : |y.im| ≤ |ν₀.im| + 1 := by linarith
      nlinarith
  rw [← differentiableOn_univ]
  exact (key.const_mul _).congr fun ν _ => rfl


/-- Ferrers functions of nonzero real order vanish at `x = 1` (where `(1+x)/(1-x)` is totalized
to `0`). -/
theorem legAdd_ferrersP_one {μ : ℂ} (hμ : μ ≠ 0) (ν : ℂ) : ferrersP ν μ 1 = 0 := by
  simp only [ferrersP]
  rw [show ((1:ℝ) + 1) / (1 - 1) = 0 by norm_num, ofReal_zero,
    zero_cpow (div_ne_zero hμ two_ne_zero), zero_mul]

/-- Bound for negative integer order on `[0, π)` from the fractional integral 14.12.2. -/
theorem legAdd_norm_ferrersP_neg_le {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ < π) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ν : ℂ, ‖ferrersP ν (-(m:ℂ)) (Real.cos θ)‖ ≤ K * Real.exp (θ * |ν.im|) := by
  have hm0 : (m:ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rcases eq_or_lt_of_le h0 with h | h
  · subst h
    refine ⟨0, le_rfl, fun ν => ?_⟩
    rw [Real.cos_zero, legAdd_ferrersP_one (neg_ne_zero.2 hm0)]; simp
  set x := Real.cos θ
  have hx : x ∈ Ioo (-1:ℝ) 1 := ⟨legAdd_neg_one_lt_cos h0 hπ, by
    rw [← Real.cos_zero]; exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hπ.le h⟩
  have hcos : 0 < Real.cos (θ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  refine ⟨‖(1 - (x:ℂ) ^ 2) ^ (-(m:ℂ) / 2) / Gamma m‖ * ((1 - x) ^ (m - 1) * (1 - x)) /
    Real.cos (θ / 2), by have : 0 ≤ 1 - x := by linarith [hx.2]
                         positivity, fun ν => ?_⟩
  have hm' : (0:ℝ) < (m:ℂ).re := by simp; exact_mod_cast hm
  rw [ferrersP_fractional_integral hm' ν hx, norm_mul]
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := 1)
    (C := Real.exp (θ * |ν.im|) / Real.cos (θ / 2) * (1 - x) ^ (m - 1))
    (f := fun t : ℝ => ferrersP ν 0 t * ((t:ℂ) - x) ^ ((m:ℂ) - 1)) (fun t ht => by
      rw [uIoc_of_le hx.2.le] at ht
      rw [norm_mul, show (m:ℂ) - 1 = ((m - 1 : ℕ) : ℂ) by
        rw [Nat.cast_sub hm]; simp, cpow_natCast, norm_pow]
      gcongr
      · exact legAdd_norm_ferrersP_zero_le_of_mem ν h0 hπ ht.1.le ht.2
      · rw [show (t:ℂ) - x = ((t - x : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1])]
        linarith [ht.2])
  rw [abs_of_pos (by linarith [hx.2] : (0:ℝ) < 1 - x)] at hI
  calc ‖(1 - (x:ℂ) ^ 2) ^ (-(m:ℂ) / 2) / Gamma m‖ *
        ‖∫ t : ℝ in x..1, ferrersP ν 0 t * ((t:ℂ) - x) ^ ((m:ℂ) - 1)‖
      ≤ ‖(1 - (x:ℂ) ^ 2) ^ (-(m:ℂ) / 2) / Gamma m‖ *
        (Real.exp (θ * |ν.im|) / Real.cos (θ / 2) * (1 - x) ^ (m - 1) * (1 - x)) := by gcongr
    _ = _ := by field_simp

/-- `|(a)_k| ≤ k! ε^{-k} e^{ε (|a| + k)}`. -/
theorem legAdd_norm_poch_le_exp (a : ℂ) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ‖poch a k‖ ≤ k ! / ε ^ k * Real.exp (ε * (‖a‖ + k)) := by
  have h1 : ‖poch a k‖ ≤ (‖a‖ + k) ^ k := by
    have key : ∀ j : ℕ, j ≤ k → ‖poch a j‖ ≤ (‖a‖ + k) ^ j := by
      intro j
      induction j with
      | zero => intro _; simp [poch_zero]
      | succ j ih =>
        intro hj
        rw [poch_succ, norm_mul, pow_succ]
        gcongr
        · exact ih (by omega)
        · calc ‖a + j‖ ≤ ‖a‖ + ‖(j:ℂ)‖ := norm_add_le _ _
            _ ≤ ‖a‖ + k := by
                gcongr
                rw [Complex.norm_natCast]; exact_mod_cast (by omega : j ≤ k)
    exact key k le_rfl
  have h2 := Real.pow_div_factorial_le_exp (x := ε * (‖a‖ + k)) (by positivity) k
  have hf : (0:ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ hf, mul_pow] at h2
  calc ‖poch a k‖ ≤ (‖a‖ + k) ^ k := h1
    _ = (ε ^ k * (‖a‖ + k) ^ k) / ε ^ k := by field_simp
    _ ≤ (Real.exp (ε * (‖a‖ + k)) * k !) / ε ^ k := by gcongr
    _ = _ := by ring


/-- `𝖯^m_ν(x) = (-1)^m (ν-m+1)_{2m} 𝖯^{-m}_ν(x)` for every complex `ν` (14.9.3 without the
exceptional degrees, by continuation in `ν`). -/
theorem legAdd_ferrersP_nat_eq (ν : ℂ) (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν m x = (-1) ^ m * poch (ν - m + 1) (2 * m) * ferrersP ν (-(m:ℂ)) x := by
  set D : ℂ → ℂ := fun ν => ferrersP ν m x - (-1) ^ m * poch (ν - m + 1) (2 * m) *
    ferrersP ν (-(m:ℂ)) x
  have hD : Differentiable ℂ D := by
    refine (legAdd_differentiable_ferrersP _ hx.1).sub (((differentiable_const _).mul ?_).mul
      (legAdd_differentiable_ferrersP _ hx.1))
    show Differentiable ℂ (fun ν : ℂ => (ascPochhammer ℂ (2 * m)).eval (ν - m + 1))
    exact ((ascPochhammer ℂ (2 * m)).differentiable).comp (by fun_prop)
  have hgen : ∀ ν : ℂ, (m:ℝ) < ν.re → D ν = 0 := by
    intro ν hν
    have hre : 1 < (ν - m + 1).re := by simp; linarith
    have hh : ∀ n : ℕ, ν - m + 1 ≠ -n := fun n h => by
      have := congrArg Complex.re h; simp at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    have hGa : Gamma (ν - m + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
    have hP := DLMF.Gamma.poch_mul_recip_Gamma_add_nat (ν - m + 1) (2 * m)
    rw [show ν - m + 1 + ((2 * m : ℕ) : ℂ) = ν + m + 1 by push_cast; ring] at hP
    have hGb : Gamma (ν + m + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    simp only [D]
    rw [ferrersP_negative_integer_order ν m hh hx]
    have hs : ((-1:ℂ)) ^ m * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
    have : poch (ν - m + 1) (2 * m) * Gamma (ν - m + 1) / Gamma (ν + m + 1) = 1 := by
      rw [mul_div_assoc, div_eq_mul_inv, mul_comm (Gamma _), ← mul_assoc, hP, inv_mul_cancel₀ hGa]
    rw [show (-1:ℂ) ^ m * poch (ν - m + 1) (2 * m) * ((-1) ^ m * Gamma (ν - m + 1) /
        Gamma (ν + m + 1) * ferrersP ν m x) = ((-1:ℂ) ^ m * (-1) ^ m) *
        (poch (ν - m + 1) (2 * m) * Gamma (ν - m + 1) / Gamma (ν + m + 1)) * ferrersP ν m x by
      ring, hs, this]
    ring
  have han : AnalyticOnNhd ℂ D univ := hD.differentiableOn.analyticOnNhd isOpen_univ
  have hev : D =ᶠ[𝓝 ((m:ℂ) + 1)] 0 := by
    have hopen : IsOpen {z : ℂ | (m:ℝ) < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (m:ℝ) < ((m:ℂ) + 1).re)] with z hz
    exact hgen z hz
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ _) hev
    (mem_univ ν)
  exact sub_eq_zero.mp this


/-- The right-hand side coefficients of the Ferrers addition theorem satisfy a Carlson bound of
type `θ₁ + θ₂ + ε` on the imaginary axis. -/
theorem legAdd_fer_rhs_bound {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂) (hs : θ₁ + θ₂ < π) (m : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ ν : ℂ, ‖(-1:ℂ) ^ m * ferrersP ν (-(m:ℂ)) (Real.cos θ₁) *
      ferrersP ν m (Real.cos θ₂)‖ ≤ C * Real.exp (ε * |ν.re| + (θ₁ + θ₂ + ε) * |ν.im|) := by
  have hπ1 : θ₁ < π := by linarith
  have hπ2 : θ₂ < π := by linarith
  have hc1 : 0 < Real.cos (θ₁ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc2 : 0 < Real.cos (θ₂ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hn : ∀ ν : ℂ, ‖ν‖ ≤ |ν.re| + |ν.im| := norm_le_abs_re_add_abs_im
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨1 / (Real.cos (θ₁ / 2) * Real.cos (θ₂ / 2)), fun ν => ?_⟩
    rw [pow_zero, one_mul, Nat.cast_zero, neg_zero, norm_mul]
    have e1 := legAdd_norm_ferrersP_zero_le ν h1 hπ1
    have e2 := legAdd_norm_ferrersP_zero_le ν h2 hπ2
    calc ‖ferrersP ν 0 (Real.cos θ₁)‖ * ‖ferrersP ν 0 (Real.cos θ₂)‖
        ≤ (Real.exp (θ₁ * |ν.im|) / Real.cos (θ₁ / 2)) *
          (Real.exp (θ₂ * |ν.im|) / Real.cos (θ₂ / 2)) :=
          mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
      _ = 1 / (Real.cos (θ₁ / 2) * Real.cos (θ₂ / 2)) * Real.exp (θ₁ * |ν.im| + θ₂ * |ν.im|) := by
          rw [Real.exp_add]; field_simp
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          nlinarith [abs_nonneg ν.re, abs_nonneg ν.im]
  · obtain ⟨K₁, hK₁, hb₁⟩ := legAdd_norm_ferrersP_neg_le hm h1 hπ1
    obtain ⟨K₂, hK₂, hb₂⟩ := legAdd_norm_ferrersP_neg_le hm h2 hπ2
    rcases eq_or_lt_of_le h2 with h | h
    · subst h
      refine ⟨0, fun ν => ?_⟩
      rw [Real.cos_zero, legAdd_ferrersP_one (by exact_mod_cast hm.ne') ν]; simp
    have hx2 : Real.cos θ₂ ∈ Ioo (-1:ℝ) 1 := ⟨legAdd_neg_one_lt_cos h2 hπ2, by
      rw [← Real.cos_zero]; exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hπ2.le h⟩
    set P : ℝ := (2 * m) ! / ε ^ (2 * m) * Real.exp (ε * (m + 1 + (2 * m : ℕ)))
    refine ⟨K₁ * K₂ * P, fun ν => ?_⟩
    rw [legAdd_ferrersP_nat_eq ν m hx2]
    have hp : ‖poch (ν - m + 1) (2 * m)‖ ≤ P * Real.exp (ε * ‖ν‖) := by
      refine (legAdd_norm_poch_le_exp _ _ hε).trans ?_
      have : ‖ν - m + 1‖ ≤ ‖ν‖ + (m + 1) := by
        calc ‖ν - m + 1‖ ≤ ‖ν‖ + ‖(m:ℂ)‖ + ‖(1:ℂ)‖ := by
              refine (norm_add_le _ _).trans ?_
              gcongr; exact norm_sub_le _ _
          _ = ‖ν‖ + (m + 1) := by rw [Complex.norm_natCast, norm_one]; ring
      simp only [P]
      rw [mul_assoc, ← Real.exp_add]
      gcongr
      nlinarith
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc ‖ferrersP ν (-(m:ℂ)) (Real.cos θ₁)‖ * (‖poch (ν - m + 1) (2 * m)‖ *
          ‖ferrersP ν (-(m:ℂ)) (Real.cos θ₂)‖)
        ≤ (K₁ * Real.exp (θ₁ * |ν.im|)) * ((P * Real.exp (ε * ‖ν‖)) *
          (K₂ * Real.exp (θ₂ * |ν.im|))) := by
          gcongr
          · exact hb₁ ν
          · exact hb₂ ν
      _ = K₁ * K₂ * P * Real.exp (θ₁ * |ν.im| + ε * ‖ν‖ + θ₂ * |ν.im|) := by
          rw [Real.exp_add, Real.exp_add]; ring
      _ ≤ _ := by
          have : 0 ≤ P := by positivity
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left (hn ν) hε.le, abs_nonneg ν.re, abs_nonneg ν.im]

/-- The Fourier coefficients of `φ ↦ 𝖯_ν(cos θ₁ cos θ₂ + sin θ₁ sin θ₂ cos φ)` for every complex
degree, given the integer case (Carlson's theorem with type `θ₁ + θ₂ < π`). -/
theorem legAdd_fer_coeff_eq {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂) (hs : θ₁ + θ₂ < π) (m : ℕ)
    (hnat : ∀ n : ℕ, legAdd_coeff (fun t => ferrersP n 0 (legAdd_fY θ₁ θ₂ t)) m =
      (-1:ℂ) ^ m * ferrersP n (-(m:ℂ)) (Real.cos θ₁) * ferrersP n m (Real.cos θ₂)) (ν : ℂ) :
    legAdd_coeff (fun t => ferrersP ν 0 (legAdd_fY θ₁ θ₂ t)) m =
      (-1:ℂ) ^ m * ferrersP ν (-(m:ℂ)) (Real.cos θ₁) * ferrersP ν m (Real.cos θ₂) := by
  set ε := (π - (θ₁ + θ₂)) / 2 with hεdef
  have hε : 0 < ε := by simp only [hεdef]; linarith
  obtain ⟨C, hC⟩ := legAdd_fer_rhs_bound h1 h2 hs m hε
  have hcos : 0 < Real.cos ((θ₁ + θ₂) / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hπ1 : -1 < Real.cos θ₁ := legAdd_neg_one_lt_cos h1 (by linarith)
  have hπ2 : -1 < Real.cos θ₂ := legAdd_neg_one_lt_cos h2 (by linarith)
  have key := legAdd_carlson (f := fun ν => legAdd_coeff (fun t => ferrersP ν 0
      (legAdd_fY θ₁ θ₂ t)) m - (-1:ℂ) ^ m * ferrersP ν (-(m:ℂ)) (Real.cos θ₁) *
      ferrersP ν m (Real.cos θ₂))
    ((legAdd_fer_coeff_differentiable h1 h2 hs m).sub
      (((differentiable_const _).mul (legAdd_differentiable_ferrersP _ hπ1)).mul
        (legAdd_differentiable_ferrersP _ hπ2)))
    (C := 1 / Real.cos ((θ₁ + θ₂) / 2) + |C|) (A := ε) (B := θ₁ + θ₂ + ε) hε.le
    (by linarith) (by simp only [hεdef]; linarith)
    (fun w _ => by
      refine (norm_sub_le _ _).trans ?_
      have e1 := legAdd_fer_coeff_bound w h1 h2 hs m
      have hE1 : Real.exp ((θ₁ + θ₂) * |w.im|) ≤ Real.exp (ε * |w.re| + (θ₁ + θ₂ + ε) * |w.im|) :=
        Real.exp_le_exp.mpr (by nlinarith [abs_nonneg w.re, abs_nonneg w.im])
      have e1' : ‖legAdd_coeff (fun t => ferrersP w 0 (legAdd_fY θ₁ θ₂ t)) m‖ ≤
          1 / Real.cos ((θ₁ + θ₂) / 2) * Real.exp (ε * |w.re| + (θ₁ + θ₂ + ε) * |w.im|) := by
        refine e1.trans ?_
        rw [div_eq_mul_inv, one_div, mul_comm]
        exact mul_le_mul_of_nonneg_left hE1 (inv_pos.2 hcos).le
      have hCa : C * Real.exp (ε * |w.re| + (θ₁ + θ₂ + ε) * |w.im|) ≤
          |C| * Real.exp (ε * |w.re| + (θ₁ + θ₂ + ε) * |w.im|) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
      have e2 := hC w
      nlinarith)
    (fun n => by rw [hnat n, sub_self]) ν
  exact sub_eq_zero.mp key

/-- **Addition theorem for Ferrers functions** (DLMF 14.18.1), given its integer case. -/
theorem legAdd_ferrersP_addition_of_nat {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂)
    (hs : θ₁ + θ₂ < π)
    (hnat : ∀ m n : ℕ, legAdd_coeff (fun t => ferrersP n 0 (legAdd_fY θ₁ θ₂ t)) m =
      (-1:ℂ) ^ m * ferrersP n (-(m:ℂ)) (Real.cos θ₁) * ferrersP n m (Real.cos θ₂))
    (ν : ℂ) (phi : ℝ) :
    HasSum (fun j : ℕ => let m := j + 1; 2 * (-1) ^ m * ferrersP ν (-m) (Real.cos θ₁) *
      ferrersP ν m (Real.cos θ₂) * Real.cos (m * phi))
      (ferrersP ν 0 (Real.cos θ₁ * Real.cos θ₂ + Real.sin θ₁ * Real.sin θ₂ * Real.cos phi) -
        ferrersP ν 0 (Real.cos θ₁) * ferrersP ν 0 (Real.cos θ₂)) := by
  have hper : Function.Periodic (fun t : ℝ => ferrersP ν 0 (legAdd_fY θ₁ θ₂ t)) (2 * π) :=
    fun t => by simp only [legAdd_fY, Real.cos_add_two_pi]
  have hev : ∀ t, (fun t : ℝ => ferrersP ν 0 (legAdd_fY θ₁ θ₂ t)) (-t) =
      (fun t : ℝ => ferrersP ν 0 (legAdd_fY θ₁ θ₂ t)) t :=
    fun t => by simp only [legAdd_fY, Real.cos_neg]
  have hF := legAdd_hasSum_cos (legAdd_fY_contDiff ν h1 h2 hs) hper hev phi
  have h0 := legAdd_fer_coeff_eq h1 h2 hs 0 (hnat 0) ν
  simp only [pow_zero, one_mul, Nat.cast_zero, neg_zero] at h0
  convert hF using 1
  · funext j
    rw [legAdd_fer_coeff_eq h1 h2 hs (j + 1) (hnat (j + 1)) ν]
    push_cast
    ring
  · rw [h0]; rfl

/-! ### The integer case of 14.18.1 -/

/-- Nonnegative integer order Ferrers P agrees with the polynomial form on `(-1, 1]`. -/
theorem legAdd_ferrersP_nat_eq_ferrersPNat (n k : ℕ) {x : ℝ} (hx : x ∈ Ioc (-1:ℝ) 1) :
    ferrersP n k x = ferrersPNat n k x := by
  rcases eq_or_lt_of_le hx.2 with rfl | hlt
  · rw [ferrersPNat_one]
    rcases k with _ | k
    · simp only [ferrersP, Nat.cast_zero, zero_div, cpow_zero, one_mul, sub_zero, sub_self,
        ite_true]
      have hc : ∀ j : ℕ, (1:ℂ) ≠ -(j:ℂ) := by
        intro j h; have := congrArg Complex.re h; simp at this; linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]
      rw [show ((1:ℂ) - ((1:ℝ):ℂ))/2 = 0 by simp, regularizedGaussHG_zero_of_regular hc]
      simp
    · simp [ferrersP]
      left; exact_mod_cast Nat.succ_ne_zero k
  · exact (ferrersPNat_eq n k ⟨hx.1, hlt⟩).symm

/-- Negative integer order Ferrers P in polynomial form on `(-1, 1]`. -/
theorem legAdd_ferrersP_neg_nat_eq_ferrersPNat (n k : ℕ) (hk : k ≤ n) {x : ℝ}
    (hx : x ∈ Ioc (-1:ℝ) 1) :
    ferrersP n (-(k:ℂ)) x = (-1)^k * ((n-k).factorial / (n+k).factorial : ℂ) * ferrersPNat n k x := by
  rcases eq_or_lt_of_le hx.2 with rfl | hlt
  · rw [ferrersPNat_one]
    rcases k with _ | k
    · rw [Nat.cast_zero, neg_zero, ← Nat.cast_zero, legAdd_ferrersP_nat_eq_ferrersPNat n 0 hx,
        ferrersPNat_one]
      simp [Nat.factorial_ne_zero]
    · simp [ferrersP]
      left; intro h; have := congrArg Complex.re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  · have hG : ∀ j : ℕ, (n:ℂ) - k + 1 ≠ -j := by
      intro j h
      have : ((n - k + 1 + j : ℕ) : ℂ) = 0 := by push_cast [Nat.cast_sub hk]; linear_combination h
      exact absurd (Nat.cast_eq_zero.1 this) (by omega)
    rw [ferrersP_negative_integer_order (n:ℂ) k hG ⟨hx.1, hlt⟩, ferrersPNat_eq n k ⟨hx.1, hlt⟩,
      show (n:ℂ) - k + 1 = ((n - k : ℕ) : ℂ) + 1 by push_cast [Nat.cast_sub hk]; ring,
      show (n:ℂ) + k + 1 = ((n + k : ℕ) : ℂ) + 1 by push_cast; ring,
      Gamma_nat_eq_factorial, Gamma_nat_eq_factorial]
    ring

open DLMF.OrthogonalPolynomials.LegendreAddition in
/-- The Ferrers addition theorem at integer degree, coefficientwise: the Fourier coefficients of
`φ ↦ P_n(cos θ₁ cos θ₂ + sin θ₁ sin θ₂ cos φ)` are `(-1)^m 𝖯^{-m}_n(cos θ₁) 𝖯^m_n(cos θ₂)`. -/
theorem legAdd_fer_nat {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂) (hs : θ₁ + θ₂ < π) (m n : ℕ) :
    legAdd_coeff (fun t => ferrersP n 0 (legAdd_fY θ₁ θ₂ t)) m =
      (-1:ℂ) ^ m * ferrersP n (-(m:ℂ)) (Real.cos θ₁) * ferrersP n m (Real.cos θ₂) := by
  have hθ1 : θ₁ < π := by linarith
  have hθ2 : θ₂ < π := by linarith
  have hcos : ∀ θ, 0 ≤ θ → θ < π → Real.cos θ ∈ Ioc (-1:ℝ) 1 := fun θ h0 hπ =>
    ⟨by rw [← Real.cos_pi]; exact Real.cos_lt_cos_of_nonneg_of_le_pi h0 le_rfl hπ, Real.cos_le_one θ⟩
  have hx1 := hcos θ₁ h1 hθ1
  have hx2 := hcos θ₂ h2 hθ2
  have hsq : ∀ θ : ℝ, (Real.sin θ : ℂ) ^ 2 = 1 - (Real.cos θ : ℂ) ^ 2 := fun θ => by
    rw [← ofReal_pow, ← ofReal_pow, Real.sin_sq]; push_cast; ring
  have hfun : (fun t : ℝ => ferrersP (n:ℂ) 0 (legAdd_fY θ₁ θ₂ t)) =
      fun t : ℝ => kernel n (Real.cos θ₁) (Real.cos θ₂) (Real.sin θ₁) (Real.sin θ₂) t := by
    funext t
    have hY := legAdd_fY_mem h1 h2 hs t
    have hY1 : -1 < legAdd_fY θ₁ θ₂ t := lt_of_lt_of_le (legAdd_neg_one_lt_cos (by linarith) hs) hY.1
    rw [ferrersP_zero _ hY1, legendreP_nat n (Or.inl (by simp; linarith)),
      ← legendre_eq_kernel n _ _ _ _ t (hsq θ₁) (hsq θ₂), legAdd_fY]
    push_cast; ring_nf
  have hsin : ∀ θ, 0 ≤ θ → θ < π → Real.sqrt (1 - Real.cos θ^2) = Real.sin θ := fun θ h0 hπ =>
    (Real.sin_eq_sqrt_one_sub_cos_sq h0 hπ.le).symm
  have hF : ∀ k : ℕ, ∀ θ, 0 ≤ θ → θ < π → ferrersPNat n k (Real.cos θ) =
      (-1)^k * (Real.sin θ:ℂ)^k * jet n k (Real.cos θ) := by
    intro k θ h0 hπ
    rw [ferrersPNat, hsin θ h0 hπ]; rfl
  rw [hfun, legAdd_coeff_kernel]
  rcases le_or_gt m n with hmn | hmn
  · rw [legAdd_ferrersP_neg_nat_eq_ferrersPNat n m hmn hx1, legAdd_ferrersP_nat_eq_ferrersPNat n m hx2,
      hF m θ₁ h1 hθ1, hF m θ₂ h2 hθ2]
    have h4 : ((-1:ℂ)) ^ m * (-1) ^ m * ((-1) ^ m * (-1) ^ m) = 1 := by
      rw [← mul_pow, ← mul_pow]; norm_num
    simp only [coeff, weight]
    linear_combination (-(((n - m).factorial / (n + m).factorial : ℂ) * (Real.sin θ₁ * Real.sin θ₂ : ℂ) ^ m *
      jet n m (Real.cos θ₁) * jet n m (Real.cos θ₂))) * h4 + 0 * (mul_pow (Real.sin θ₁ : ℂ) (Real.sin θ₂) m)
  · rw [coeff_eq_zero hmn, legAdd_ferrersP_nat_eq_ferrersPNat n m hx2, hF m θ₂ h2 hθ2, jet_eq_zero hmn]
    simp

end DLMF.Legendre
