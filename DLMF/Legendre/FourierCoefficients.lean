/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Series
public import DLMF.Legendre.Harmonics

/-!
# Fourier coefficients and Carlson's theorem for the addition theorems

The Fourier coefficient on `[-π, π]`, the cosine expansion of an even, `2π`-periodic `C²` function
and Carlson's theorem, used for the Legendre addition theorems DLMF 14.18.1–14.18.5 and 14.28.1
in `DLMF.Legendre.AdditionTools`.

## Main definitions

* `AdditionTheorem.coeff`: the Fourier coefficient on `[-π, π]`.

## Main results

* `AdditionTheorem.hasSum_cos`: the cosine expansion of an even, `2π`-periodic `C²` function
  (absolute convergence from two integrations by parts, `AdditionTheorem.coeff_bound`).
* `AdditionTheorem.eq_zero_of_carlson`: Carlson's theorem (`Complex.eqOn_zero_of_natCast_eq_zero`)
  for entire functions bounded by `C exp (A |Re ν| + B |Im ν|)`, `B < π`, extended to all of `ℂ`
  by the identity theorem.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory DLMF.Hypergeometric DLMF
open scoped Real Topology Nat

namespace DLMF.Legendre

/-- Fourier coefficient on `[-π, π]`. -/
def AdditionTheorem.coeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  1 / (2 * π) * ∫ t in (-π)..π, exp (-(n * t * I)) * f t

/-- For an integer `n`, `exp (-(n π i)) = exp (-(n (-π) i))`, i.e. the Fourier kernel takes equal
values at `t = π` and `t = -π`. -/
theorem AdditionTheorem.exp_pi (n : ℤ) : exp (-(n * (π:ℝ) * I)) =
    exp (-(n * ((-π : ℝ):ℂ) * I)) := by
  rw [show -((n:ℂ) * ((-π:ℝ):ℂ) * I) = -(n * (π:ℝ) * I) + n * (2 * π * I) by push_cast; ring,
    exp_add, exp_int_mul_two_pi_mul_I, mul_one]

/-- One integration by parts for a periodic function. -/
theorem AdditionTheorem.integral_exp_mul_eq {g g' : ℝ → ℂ} (hg : ∀ t, HasDerivAt g (g' t) t)
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
    rw [AdditionTheorem.exp_pi n, hper, sub_self]
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
theorem AdditionTheorem.deriv_periodic {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π)) :
    Function.Periodic (deriv f) (2 * π) := by
  intro t
  have h : f = fun s => f (s + 2 * π) := funext fun s => (hper s).symm
  conv_rhs => rw [h]
  rw [deriv_comp_add_const]

/-- Second-order decay of the Fourier coefficients of a periodic `C²` function. -/
theorem AdditionTheorem.coeff_bound {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hper : Function.Periodic f (2 * π)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ, n ≠ 0 → ‖AdditionTheorem.coeff f n‖ ≤ M / (n:ℝ) ^ 2 := by
  have hd1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hc1 : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  have hd2 : Differentiable ℝ (deriv f) := hc1.differentiable (by norm_num)
  have hc2 : Continuous (deriv (deriv f)) := hc1.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -π) (b := π)).exists_bound_of_continuousOn
    hc2.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun n hn => ?_⟩
  have h1 := AdditionTheorem.integral_exp_mul_eq (g := f) (g' := deriv f)
      (fun t => (hd1 t).hasDerivAt)
    hc1.continuous (by have := hper (-π); rw [show -π + 2 * π = π by ring] at this; exact this) hn
  have h2 := AdditionTheorem.integral_exp_mul_eq (g := deriv f) (g' := deriv (deriv f))
    (fun t => (hd2 t).hasDerivAt) hc2
    (by have := AdditionTheorem.deriv_periodic hper (-π); rw [show -π + 2 * π = π by ring] at this;
        exact this) hn
  have hI : ‖∫ t : ℝ in (-π)..π, exp (-((n:ℂ) * (t:ℂ) * I)) * deriv (deriv f) t‖ ≤
      max M 0 * |π - -π| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [uIoc_of_le (by linarith [Real.pi_pos])] at ht
    rw [norm_mul, show -((n:ℂ) * t * I) = ((-(n * t) : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I, one_mul]
    exact (hM t ⟨ht.1.le, ht.2⟩).trans (le_max_left _ _)
  have hn2 : (0:ℝ) < (n:ℝ) ^ 2 := by positivity
  rw [AdditionTheorem.coeff, h1, h2, norm_mul, norm_mul, norm_mul]
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
    _ = max M 0 / (n:ℝ) ^ 2 := by rw [← habs, abs_of_pos (show (0:ℝ) < π - -π by linarith)];
                                  field_simp; ring


/-- The coefficients of an even function are even in the index. -/
theorem AdditionTheorem.coeff_neg {f : ℝ → ℂ} (hev : ∀ t, f (-t) = f t) (n : ℤ) :
    AdditionTheorem.coeff f (-n) = AdditionTheorem.coeff f n := by
  rw [AdditionTheorem.coeff, AdditionTheorem.coeff]
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
theorem AdditionTheorem.hasSum_cos {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hper : Function.Periodic f (2 * π))
    (hev : ∀ t, f (-t) = f t) (u : ℝ) :
    HasSum (fun j : ℕ => 2 * AdditionTheorem.coeff f ((j + 1 : ℕ) : ℤ) *
        Real.cos (((j + 1 : ℕ) : ℝ) * u))
      (f u - AdditionTheorem.coeff f 0) := by
  have : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
  let g : C(AddCircle (2 * π), ℂ) := ⟨hper.lift, continuous_coinduced_dom.mpr hf.continuous⟩
  have hgx : ∀ x : ℝ, g (x : AddCircle (2 * π)) = f x := fun x => rfl
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hgc : ∀ n : ℤ, fourierCoeff g n = AdditionTheorem.coeff f n := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral _ n (-π), show -π + 2 * π = π by ring,
                                                                            AdditionTheorem.coeff,
      Complex.real_smul]
    congr 1
    · push_cast; ring
    · refine intervalIntegral.integral_congr fun x _ => ?_
      rw [fourier_coe_apply, hgx, smul_eq_mul]
      congr 2
      push_cast
      field_simp
  obtain ⟨M, hM0, hM⟩ := AdditionTheorem.coeff_bound hf hper
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
      2 * AdditionTheorem.coeff f n * Real.cos ((n : ℝ) * u) := by
    intro n
    rw [hgc, hgc, AdditionTheorem.coeff_neg hev, fourier_coe_apply, fourier_coe_apply, smul_eq_mul,
      smul_eq_mul, ofReal_cos, Complex.cos]
    rw [show 2 * (π : ℂ) * I * ((n : ℤ) : ℂ) * (u : ℂ) / ((2 * π : ℝ) : ℂ) =
        ((n:ℝ) * u : ℝ) * I by push_cast; field_simp,
      show 2 * (π : ℂ) * I * ((-(n : ℤ) : ℤ) : ℂ) * (u : ℂ) / ((2 * π : ℝ) : ℂ) =
        -(((n:ℝ) * u : ℝ) * I) by push_cast; field_simp]
    ring_nf
  have hR : HasSum (fun n : ℕ => 2 * AdditionTheorem.coeff f n * Real.cos ((n : ℝ) * u))
      (f u + AdditionTheorem.coeff f 0) := by
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
theorem AdditionTheorem.eq_zero_of_carlson {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {C A B : ℝ} (hA : 0 ≤ A)
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

end DLMF.Legendre
