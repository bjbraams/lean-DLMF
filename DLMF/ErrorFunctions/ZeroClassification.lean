/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.Integrals
public import DLMF.Core.ZeroCounting

/-!
# Where the zeros of `erf` and `erfc` can lie, DLMF §7.13(i)–(ii)

Elementary localization of the complex zeros of the error functions, used to reduce the zero
classifications of `DLMF/ErrorFunctions/Zeros.lean` to the modulus enumerations there.

* `zcnt_erf_conj`, `zcnt_erfc_conj`: `erf (z̄) = conj (erf z)`, by the identity theorem for the
  derivative (`HasDerivAt.conj_conj`).
* `zcnt_erfc_ne_zero_of_re_pos`: `erfc z ≠ 0` for `Re z > 0`, from the Cauchy integral
  `∫ e^{-t²}/(t - u) dt = π i w(u)` (DLMF 7.7.2) of the Faddeeva function at `u = iz`, whose
  imaginary part is a positive integral.
* `zcnt_norm_erfc_le_one`: `‖erfc z‖ ≤ 1` for `Re z ≥ 0`, `Re z² ≥ 0`, from the Laplace form
  `erfc z = π^{-1/2} e^{-z²} ∫₀^∞ e^{-zr - r²/4} dr`.
* `zcnt_erfc_zero_arg`: every zero of `erfc` satisfies `π/2 < |ph z| < 3π/4`.
* `zcnt_erf_ofReal_ne_zero`, `zcnt_erf_I_mul_ofReal_ne_zero`: `erf` has no zero on the real or
  imaginary axis other than `0`.
* Fresnel integrals: the symmetries `C(-z) = -C(z)`, `C(z̄) = conj C(z)`, `C(iz) = i C(z)` and
  `S(iz) = -i S(z)` (`zcnt_fresnelCosInt_neg` …); no zeros on the diagonal `ℝ(1+i)`
  (`C((1+i)x) = (1+i)x ∫₀¹ cosh(πt²x²) dt`); no real zeros (`zcnt_fresnelCosInt_ofReal_ne_zero`,
  `zcnt_fresnelSinInt_ofReal_ne_zero`): for `0 < x ≤ 1` the integrand is positive, and for `x ≥ 1`
  `C = 1/2 + f sin − g cos` with `‖f‖ + ‖g‖ < 1/2` from the Laplace integrals 7.7.10–11.
* `zcnt_octant_classification`: the eight-fold symmetry reduces a zero classification to the
  modulus enumeration in the octant `0 < ph z < π/4`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory DLMF.Hypergeometric DLMF
open scoped Real Topology ComplexConjugate

namespace DLMF.Confluent

/-- `erf` commutes with complex conjugation. -/
theorem zcnt_erf_conj (z : ℂ) : erf (conj z) = conj (erf z) := by
  have hd : ∀ w, HasDerivAt (fun w => conj (erf (conj w)) - erf w) 0 w := by
    intro w
    have h1 := (hasDerivAt_erf_complex (conj w)).conj_conj
    rw [conj_conj] at h1
    have h2 := hasDerivAt_erf_complex w
    convert h1.sub h2 using 1
    · rfl
    · rw [map_mul, map_div₀, Complex.conj_ofReal, map_ofNat, ← Complex.exp_conj, map_neg,
        map_pow, conj_conj, sub_self]
  have hc := is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt)
    (fun w => (hd w).deriv) z 0
  simp only [map_zero, erf_zero, sub_zero] at hc
  rw [← conj_conj (erf (conj z)), sub_eq_zero.mp hc]

/-- `erfc` is entire. -/
theorem zcnt_differentiable_erfc : Differentiable ℂ erfc := by
  unfold erfc
  exact (differentiable_const _).sub differentiable_erf_complex

/-- `erfc` commutes with complex conjugation. -/
theorem zcnt_erfc_conj (z : ℂ) : erfc (conj z) = conj (erfc z) := by
  simp [erfc, zcnt_erf_conj]

/-- Integrability of the Cauchy kernel of the Faddeeva function off the real axis. -/
theorem zcnt_integrable_cauchy {u : ℂ} (hu : 0 < u.im) :
    Integrable (fun t : ℝ => exp (-(t : ℂ) ^ 2) / ((t : ℂ) - u)) := by
  have hne : ∀ t : ℝ, (t : ℂ) - u ≠ 0 := fun t h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  refine Integrable.mono' ((integrable_exp_neg_mul_sq one_pos).div_const u.im) ?_ ?_
  · exact (Continuous.div (by fun_prop) (by fun_prop) hne).aestronglyMeasurable
  · refine Eventually.of_forall fun t => ?_
    rw [norm_div]
    have him : u.im ≤ ‖(t : ℂ) - u‖ := by
      calc u.im = |((t : ℂ) - u).im| := by simp [abs_of_pos hu]
        _ ≤ ‖(t : ℂ) - u‖ := abs_im_le_norm _
    have hnum : ‖exp (-(t : ℂ) ^ 2)‖ = Real.exp (-1 * t ^ 2) := by
      rw [norm_exp]; congr 1; simp [← ofReal_pow]
    rw [hnum]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hu him

/-- **No zeros of `erfc` in the open right half-plane.** -/
theorem zcnt_erfc_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : erfc z ≠ 0 := by
  intro h0
  set u := I * z with hu
  have hui : 0 < u.im := by simpa [hu] using hz
  have hW : faddeevaW u = 0 := by
    rw [faddeevaW, show -I * u = z by rw [hu]; ring_nf; rw [I_sq]; ring, h0, mul_zero]
  have hint := (faddeevaW_cauchy_integral hui).1
  rw [hW, mul_zero] at hint
  have hInt := zcnt_integrable_cauchy hui
  have him := integral_im (𝕜 := ℂ) hInt
  rw [hint] at him
  simp only [RCLike.im_to_complex, Complex.zero_im] at him
  -- the imaginary part of the integrand is positive
  have hpos : ∀ t : ℝ, 0 < (exp (-(t : ℂ) ^ 2) / ((t : ℂ) - u)).im := by
    intro t
    have hne : (t : ℂ) - u ≠ 0 := fun h => by
      have := congrArg Complex.im h
      simp at this
      linarith
    rw [show exp (-(t : ℂ) ^ 2) = ((Real.exp (-t ^ 2) : ℝ) : ℂ) by push_cast; rfl,
      div_eq_mul_inv]
    rw [Complex.im_ofReal_mul, Complex.inv_im]
    have hns : 0 < Complex.normSq ((t : ℂ) - u) := Complex.normSq_pos.mpr hne
    have : -((t : ℂ) - u).im = u.im := by simp
    rw [this]
    positivity
  have hpos' : 0 < ∫ t : ℝ, (exp (-(t : ℂ) ^ 2) / ((t : ℂ) - u)).im := by
    refine (integral_pos_iff_support_of_nonneg (fun t => (hpos t).le) hInt.im).2 ?_
    have : Function.support (fun t : ℝ => (exp (-(t : ℂ) ^ 2) / ((t : ℂ) - u)).im) = univ :=
      Set.eq_univ_of_forall fun t => (hpos t).ne'
    rw [this]
    simp
  linarith

/-- On the imaginary axis `Re erfc z = 1`, so `erfc` has no zero there. -/
theorem zcnt_erfc_ne_zero_of_re_eq_zero {z : ℂ} (hz : z.re = 0) : erfc z ≠ 0 := by
  have hc : conj z = -z := by
    apply Complex.ext <;> simp [hz]
  have hre : (erf z).re = 0 := by
    have h := zcnt_erf_conj z
    rw [hc, erf_negative] at h
    have := congrArg Complex.re h
    simp at this
    linarith
  intro h0
  have := congrArg Complex.re h0
  simp [erfc, hre] at this

/-- **No zeros of `erfc` in the closed right half-plane.** -/
theorem zcnt_erfc_ne_zero_of_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) : erfc z ≠ 0 := by
  rcases hz.lt_or_eq with h | h
  · exact zcnt_erfc_ne_zero_of_re_pos h
  · exact zcnt_erfc_ne_zero_of_re_eq_zero h.symm

/-- `‖erfc z‖ ≤ 1` in the closed quarter-plane sector `Re z ≥ 0`, `Re z² ≥ 0`
(that is, `|ph z| ≤ π/4`). -/
theorem zcnt_norm_erfc_le_one {z : ℂ} (hz : 0 ≤ z.re) (hz2 : 0 ≤ (z ^ 2).re) :
    ‖erfc z‖ ≤ 1 := by
  have h := erfc_eq_integral_rotate (θ := 0) (by simp [Real.pi_pos]) z
  simp only [ofReal_zero, zero_mul, Complex.exp_zero, mul_one, one_mul] at h
  have hbound : ‖∫ r in Ioi (0 : ℝ), cexp (-(z * r)) * cexp (-((r : ℂ) ^ 2 / 4))‖ ≤
      ∫ r in Ioi (0 : ℝ), Real.exp (-(1 / 4) * r ^ 2) := by
    refine norm_integral_le_of_norm_le
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).integrableOn ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [norm_mul, norm_exp, norm_exp]
    have h1 : Real.exp (-(z * r)).re ≤ 1 := by
      rw [Real.exp_le_one_iff]
      simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      have : 0 ≤ z.re * r := mul_nonneg hz (le_of_lt hr)
      linarith
    have h2 : Real.exp (-((r : ℂ) ^ 2 / 4)).re = Real.exp (-(1 / 4) * r ^ 2) := by
      congr 1
      rw [← ofReal_pow]
      simp only [neg_re, div_ofNat_re, ofReal_re]
      ring
    rw [h2]
    calc Real.exp (-(z * r)).re * Real.exp (-(1 / 4) * r ^ 2)
        ≤ 1 * Real.exp (-(1 / 4) * r ^ 2) := by gcongr
      _ = _ := one_mul _
  rw [integral_gaussian_Ioi] at hbound
  have hsq : Real.sqrt (π / (1 / 4)) / 2 = Real.sqrt π := by
    rw [show π / (1 / 4) = 2 ^ 2 * π by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
    ring
  rw [hsq] at hbound
  have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hexp : ‖cexp (-z ^ 2)‖ ≤ 1 := by
    rw [norm_exp, Real.exp_le_one_iff]
    simp only [neg_re]
    linarith
  rw [h, norm_mul, norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hsp]
  calc 1 / Real.sqrt π * ‖cexp (-z ^ 2)‖ *
        ‖∫ r in Ioi (0 : ℝ), cexp (-(z * r)) * cexp (-((r : ℂ) ^ 2 / 4))‖
      ≤ 1 / Real.sqrt π * 1 * Real.sqrt π := by gcongr
    _ = 1 := by field_simp

/-- `(z²).re = ‖z‖² cos (2 ph z)`. -/
theorem zcnt_re_sq (z : ℂ) : (z ^ 2).re = ‖z‖ ^ 2 * Real.cos (2 * arg z) := by
  rw [Real.cos_two_mul, pow_two, mul_re]
  have hc := norm_mul_cos_arg z
  have hs := norm_mul_sin_arg z
  have hsc := Real.sin_sq_add_cos_sq (arg z)
  rw [← hc, ← hs]
  nlinarith [hsc]

/-- **Zeros of `erfc` lie in the sectors `π/2 < |ph z| < 3π/4`** (DLMF §7.13(ii)). -/
theorem zcnt_erfc_zero_arg {z : ℂ} (h0 : erfc z = 0) :
    π / 2 < |arg z| ∧ |arg z| < 3 * π / 4 := by
  have hre : z.re < 0 := by
    by_contra h
    exact zcnt_erfc_ne_zero_of_re_nonneg (not_lt.mp h) h0
  have hz0 : z ≠ 0 := fun h => by simp [h] at hre
  have hcos : Real.cos (arg z) < 0 := by
    rw [← norm_mul_cos_arg z] at hre
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    by_contra h
    push Not at h
    nlinarith
  have habs := abs_arg_le_pi z
  constructor
  · by_contra h
    push Not at h
    have : 0 ≤ Real.cos (arg z) := by
      rw [← Real.cos_abs]
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg (arg z), Real.pi_pos], h⟩
    linarith
  · by_contra h
    push Not at h
    -- `ζ = -z` lies in `|ph ζ| ≤ π/4`
    have hre' : 0 ≤ (-z).re := by simp; linarith
    have hre2 : 0 ≤ ((-z) ^ 2).re := by
      rw [neg_sq, zcnt_re_sq]
      have hc2 : 0 ≤ Real.cos (2 * arg z) := by
        rw [← Real.cos_abs, abs_mul, abs_two,
          show 2 * |arg z| = (2 * |arg z| - 2 * π) + 2 * π by ring, Real.cos_add_two_pi]
        exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      positivity
    have hle := zcnt_norm_erfc_le_one hre' hre2
    have h2 : erfc (-z) = 2 := by rw [erfc_negative, h0, sub_zero]
    rw [h2] at hle
    norm_num at hle

/-- A zero of `erfc` lies in the open sector `π/2 < ph z < 3π/4` or its conjugate does. -/
theorem zcnt_erfc_zero_mem_sector {z : ℂ} (h0 : erfc z = 0) :
    (π / 2 < arg z ∧ arg z < 3 * π / 4) ∨
      (π / 2 < arg (conj z) ∧ arg (conj z) < 3 * π / 4) := by
  obtain ⟨h1, h2⟩ := zcnt_erfc_zero_arg h0
  have hpi : arg z ≠ π := fun h => by rw [h, abs_of_pos Real.pi_pos] at h2; linarith [Real.pi_pos]
  rcases le_or_gt 0 (arg z) with h | h
  · left
    rw [abs_of_nonneg h] at h1 h2
    exact ⟨h1, h2⟩
  · right
    rw [abs_of_neg h] at h1 h2
    rw [arg_conj, ite_eq_right_iff.mpr (fun h => absurd h hpi)]
    exact ⟨h1, h2⟩

/-- `erf` has no zero on the real axis other than `0`. -/
theorem zcnt_erf_ofReal_ne_zero {x : ℝ} (hx : x ≠ 0) : erf (x : ℂ) ≠ 0 := by
  rw [erf_ofReal, Complex.ofReal_ne_zero]
  rcases hx.lt_or_gt with h | h
  · have := TauCeti.Real.erf_pos (neg_pos.mpr h)
    rw [TauCeti.Real.erf_neg] at this
    linarith
  · exact (TauCeti.Real.erf_pos h).ne'

/-- `erf (i y) = (2/√π) i e^{y²} F(y)` with Dawson's integral `F`. -/
theorem zcnt_erf_I_mul (z : ℂ) :
    erf (I * z) = 2 / Real.sqrt π * I * (exp (z ^ 2) * dawsonF z) := by
  have he : erf (I*z)=2/Real.sqrt π*I*primitive (fun t => exp (t^2)) z := by
    rw [erf_complex_segment_integral]
    simp only [primitive, segmentIntegral, sub_zero, zero_add]
    have harg (t : ℝ) : -((t:ℂ)*(I*z))^2=((t:ℂ)*z)^2 := by simp [mul_pow, I_sq]
    simp_rw [harg]
    ring
  rw [he, dawsonF, ← mul_assoc (cexp (z ^ 2)), ← Complex.exp_add]
  simp

/-- `erf` has no zero on the imaginary axis other than `0`. -/
theorem zcnt_erf_I_mul_ofReal_ne_zero {y : ℝ} (hy : y ≠ 0) : erf (I * (y : ℂ)) ≠ 0 := by
  have hD : ∀ x : ℝ, 0 < x → 0 < Real.dawsonF x := by
    intro x hx
    have h := (Real.dawsonF_integral_bounds hx).1
    have hs : 0 < Real.sinh (x ^ 2) / x := div_pos (Real.sinh_pos_iff.mpr (by positivity)) hx
    have := hs.trans h
    exact pos_of_mul_pos_right this (Real.exp_pos _).le
  have hne : Real.dawsonF y ≠ 0 := by
    rcases hy.lt_or_gt with h | h
    · have h1 := hD (-y) (neg_pos.mpr h)
      have hodd : Real.dawsonF (-y) = -Real.dawsonF y := by
        have hc : dawsonF (-(y : ℂ)) = -dawsonF (y : ℂ) := by
          rw [dawsonF_eq_kummerM, dawsonF_eq_kummerM, neg_sq]; ring
        rw [← Complex.ofReal_neg, dawsonF_ofReal, dawsonF_ofReal] at hc
        exact_mod_cast hc
      linarith
    · exact (hD y h).ne'
  rw [zcnt_erf_I_mul, dawsonF_ofReal]
  have hsp : (Real.sqrt π : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  refine mul_ne_zero (mul_ne_zero (div_ne_zero two_ne_zero hsp) I_ne_zero)
    (mul_ne_zero (Complex.exp_ne_zero _) (by exact_mod_cast hne))

/-- Two functions with the same derivative everywhere and the same value at `0` agree. -/
theorem zcnt_eq_of_hasDerivAt {f g f' : ℂ → ℂ} (hf : ∀ z, HasDerivAt f (f' z) z)
    (hg : ∀ z, HasDerivAt g (f' z) z) (h0 : f 0 = g 0) (z : ℂ) : f z = g z := by
  have hd : ∀ w, HasDerivAt (fun w => f w - g w) 0 w := fun w => by
    have h := (hf w).sub (hg w)
    rwa [sub_self] at h
  have hc := is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt)
    (fun w => (hd w).deriv) z 0
  simp only [h0, sub_self] at hc
  exact sub_eq_zero.mp hc

/-- `C` is odd. -/
theorem zcnt_fresnelCosInt_neg (z : ℂ) : fresnelCosInt (-z) = -fresnelCosInt z :=
  zcnt_eq_of_hasDerivAt (f' := fun z => -cos (π * z ^ 2 / 2))
    (fun z => by
      have := (hasDerivAt_fresnelCosInt_complex (-z)).comp z (hasDerivAt_neg z)
      simpa [neg_sq] using this)
    (fun z => (hasDerivAt_fresnelCosInt_complex z).neg)
    (by simp [fresnelCosInt, primitive_zero]) z

/-- `S` is odd. -/
theorem zcnt_fresnelSinInt_neg (z : ℂ) : fresnelSinInt (-z) = -fresnelSinInt z :=
  zcnt_eq_of_hasDerivAt (f' := fun z => -sin (π * z ^ 2 / 2))
    (fun z => by
      have := (hasDerivAt_fresnelSinInt_complex (-z)).comp z (hasDerivAt_neg z)
      simpa [neg_sq] using this)
    (fun z => (hasDerivAt_fresnelSinInt_complex z).neg)
    (by simp [fresnelSinInt, primitive_zero]) z

/-- `C` commutes with conjugation. -/
theorem zcnt_fresnelCosInt_conj (z : ℂ) : fresnelCosInt (conj z) = conj (fresnelCosInt z) := by
  have h := zcnt_eq_of_hasDerivAt (f' := fun z => cos (π * z ^ 2 / 2))
    (f := fun z => conj (fresnelCosInt (conj z)))
    (fun z => by
      have h1 := (hasDerivAt_fresnelCosInt_complex (conj z)).conj_conj
      rw [conj_conj] at h1
      convert h1 using 1
      · rfl
      rw [← Complex.cos_conj]
      simp only [map_div₀, map_mul, Complex.conj_ofReal, map_pow, conj_conj, map_ofNat])
    hasDerivAt_fresnelCosInt_complex (by simp [fresnelCosInt, primitive_zero]) z
  rw [← h, conj_conj]

/-- `S` commutes with conjugation. -/
theorem zcnt_fresnelSinInt_conj (z : ℂ) : fresnelSinInt (conj z) = conj (fresnelSinInt z) := by
  have h := zcnt_eq_of_hasDerivAt (f' := fun z => sin (π * z ^ 2 / 2))
    (f := fun z => conj (fresnelSinInt (conj z)))
    (fun z => by
      have h1 := (hasDerivAt_fresnelSinInt_complex (conj z)).conj_conj
      rw [conj_conj] at h1
      convert h1 using 1
      · rfl
      rw [← Complex.sin_conj]
      simp only [map_div₀, map_mul, Complex.conj_ofReal, map_pow, conj_conj, map_ofNat])
    hasDerivAt_fresnelSinInt_complex (by simp [fresnelSinInt, primitive_zero]) z
  rw [← h, conj_conj]

/-- `C(iz) = i C(z)`. -/
theorem zcnt_fresnelCosInt_I_mul (z : ℂ) : fresnelCosInt (I * z) = I * fresnelCosInt z :=
  zcnt_eq_of_hasDerivAt (f' := fun z => I * cos (π * z ^ 2 / 2))
    (fun z => by
      have := (hasDerivAt_fresnelCosInt_complex (I * z)).comp z ((hasDerivAt_id z).const_mul I)
      convert this using 1
      simp only [mul_one, mul_pow, I_sq]
      rw [show π * (-1 * z ^ 2) / 2 = -(π * z ^ 2 / 2) by ring, Complex.cos_neg]
      ring)
    (fun z => (hasDerivAt_fresnelCosInt_complex z).const_mul I)
    (by simp [fresnelCosInt, primitive_zero]) z

/-- `S(iz) = -i S(z)`. -/
theorem zcnt_fresnelSinInt_I_mul (z : ℂ) : fresnelSinInt (I * z) = -I * fresnelSinInt z :=
  zcnt_eq_of_hasDerivAt (f' := fun z => -I * sin (π * z ^ 2 / 2))
    (fun z => by
      have := (hasDerivAt_fresnelSinInt_complex (I * z)).comp z ((hasDerivAt_id z).const_mul I)
      convert this using 1
      simp only [mul_one, mul_pow, I_sq]
      rw [show π * (-1 * z ^ 2) / 2 = -(π * z ^ 2 / 2) by ring, Complex.sin_neg]
      ring)
    (fun z => (hasDerivAt_fresnelSinInt_complex z).const_mul (-I))
    (by simp [fresnelSinInt, primitive_zero]) z

/-- On the diagonal, `C((1+i)x) = (1+i) x ∫₀¹ cosh(π t² x²) dt`. -/
theorem zcnt_fresnelCosInt_diag (x : ℝ) :
    fresnelCosInt ((1 + I) * x) =
      (1 + I) * x * ((∫ t in (0 : ℝ)..1, Real.cosh (π * t ^ 2 * x ^ 2) : ℝ) : ℂ) := by
  rw [fresnelCosInt, primitive, segmentIntegral, sub_zero, ← intervalIntegral.integral_ofReal]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [zero_add]
  have : π * ((t : ℂ) * ((1 + I) * x)) ^ 2 / 2 = (π * t ^ 2 * x ^ 2 : ℝ) * I := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [this, Complex.cos_mul_I]
  push_cast
  rfl

/-- On the diagonal, `S((1+i)x) = (1+i) x i ∫₀¹ sinh(π t² x²) dt`. -/
theorem zcnt_fresnelSinInt_diag (x : ℝ) :
    fresnelSinInt ((1 + I) * x) =
      (1 + I) * x * (I * ((∫ t in (0 : ℝ)..1, Real.sinh (π * t ^ 2 * x ^ 2) : ℝ) : ℂ)) := by
  rw [fresnelSinInt, primitive, segmentIntegral, sub_zero, ← intervalIntegral.integral_ofReal,
    ← intervalIntegral.integral_const_mul I]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [zero_add]
  have : π * ((t : ℂ) * ((1 + I) * x)) ^ 2 / 2 = (π * t ^ 2 * x ^ 2 : ℝ) * I := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [this, Complex.sin_mul_I]
  push_cast
  ring

/-- `C` has no zero on the diagonal `ℝ(1+i)` other than `0`. -/
theorem zcnt_fresnelCosInt_diag_ne_zero {x : ℝ} (hx : x ≠ 0) :
    fresnelCosInt ((1 + I) * x) ≠ 0 := by
  rw [zcnt_fresnelCosInt_diag]
  have hpos : 0 < ∫ t in (0 : ℝ)..1, Real.cosh (π * t ^ 2 * x ^ 2) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (Continuous.intervalIntegrable (by fun_prop) _ _)
      (fun t _ => Real.cosh_pos _) one_pos
  have h1 : (1 + I) ≠ 0 := fun h => by simpa using congrArg Complex.re h
  exact mul_ne_zero (mul_ne_zero h1 (by exact_mod_cast hx)) (by exact_mod_cast hpos.ne')

/-- `S` has no zero on the diagonal `ℝ(1+i)` other than `0`. -/
theorem zcnt_fresnelSinInt_diag_ne_zero {x : ℝ} (hx : x ≠ 0) :
    fresnelSinInt ((1 + I) * x) ≠ 0 := by
  rw [zcnt_fresnelSinInt_diag]
  have hpos : 0 < ∫ t in (0 : ℝ)..1, Real.sinh (π * t ^ 2 * x ^ 2) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (Continuous.intervalIntegrable (by fun_prop) _ _)
      (fun t ht => Real.sinh_pos_iff.mpr (by
        have : 0 < t := ht.1
        have : 0 < x ^ 2 := by positivity
        positivity)) one_pos
  have h1 : (1 + I) ≠ 0 := fun h => by simpa using congrArg Complex.re h
  exact mul_ne_zero (mul_ne_zero h1 (by exact_mod_cast hx))
    (mul_ne_zero I_ne_zero (by exact_mod_cast hpos.ne'))

/-- A Laplace-type integral with a kernel bounded by `t^{s-1} e^{-at}` is at most `a^{-s} Γ(s)`. -/
theorem zcnt_norm_laplace_le {s a : ℝ} (hs : 0 < s) (ha : 0 < a) {g : ℝ → ℂ}
    (hg : ∀ t : ℝ, 0 < t → ‖g t‖ ≤ t ^ (s - 1) * Real.exp (-(a * t))) :
    ‖∫ t in Ioi (0 : ℝ), g t‖ ≤ (1 / a) ^ s * Real.Gamma s := by
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi hs ha]
  refine norm_integral_le_of_norm_le ?_ ?_
  · have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1) (b := a)
      (by linarith) one_pos ha
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp [Real.rpow_one, neg_mul]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hg t ht

/-- The Fresnel auxiliary functions on the positive axis: `‖f(x)‖ ≤ 1/(πx)` and
`‖g(x)‖ ≤ (π√2)⁻¹ (2/(πx²))^{3/2} Γ(3/2)`. -/
lemma zcnt_fresnelAux_norm_le {x : ℝ} (hx : 0 < x) :
    ‖fresnelAuxFComplex x‖ ≤ 1 / (π * Real.sqrt 2) * ((1 / (π * x ^ 2 / 2)) ^ (1 / 2 : ℝ) *
        Real.Gamma (1 / 2)) ∧
      ‖fresnelAuxGComplex x‖ ≤ 1 / (π * Real.sqrt 2) * ((1 / (π * x ^ 2 / 2)) ^ (3 / 2 : ℝ) *
        Real.Gamma (3 / 2)) := by
  have harg : |arg (x : ℂ)| ≤ π / 4 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  have ha : 0 < π * x ^ 2 / 2 := by positivity
  have hc : (0 : ℝ) < 1 / (π * Real.sqrt 2) := by positivity
  have hkey : ∀ (p : ℂ) (s : ℝ), p.re = s - 1 → ∀ t : ℝ, 0 < t →
      ‖(t : ℂ) ^ p * exp (-π * (x : ℂ) ^ 2 * t / 2) / ((t : ℂ) ^ 2 + 1)‖ ≤
        t ^ (s - 1) * Real.exp (-(π * x ^ 2 / 2 * t)) := by
    intro p s hp t ht
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, hp, norm_exp]
    have hre : (-π * (x : ℂ) ^ 2 * t / 2).re = -(π * x ^ 2 / 2 * t) := by
      rw [show -π * (x : ℂ) ^ 2 * t / 2 = ((-(π * x ^ 2 / 2 * t) : ℝ) : ℂ) by push_cast; ring,
        ofReal_re]
    rw [hre]
    have hden : 1 ≤ ‖(t : ℂ) ^ 2 + 1‖ := by
      rw [← ofReal_pow, ← ofReal_one, ← ofReal_add, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      nlinarith [sq_nonneg t]
    have hnum : 0 ≤ t ^ (s - 1) * Real.exp (-(π * x ^ 2 / 2 * t)) := by positivity
    calc t ^ (s - 1) * Real.exp (-(π * x ^ 2 / 2 * t)) / ‖(t : ℂ) ^ 2 + 1‖
        ≤ t ^ (s - 1) * Real.exp (-(π * x ^ 2 / 2 * t)) / 1 :=
          div_le_div_of_nonneg_left hnum one_pos hden
      _ = _ := div_one _
  constructor
  · rw [fresnelAuxFComplex_laplace_integral harg, norm_mul]
    have h1 : ‖(1 : ℂ) / (π * Real.sqrt 2)‖ = 1 / (π * Real.sqrt 2) := by
      rw [show (1 : ℂ) / (π * Real.sqrt 2) = ((1 / (π * Real.sqrt 2) : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    rw [h1]
    gcongr
    exact zcnt_norm_laplace_le (by norm_num) ha (hkey _ _ (by norm_num))
  · rw [fresnelAuxGComplex_laplace_integral harg, norm_mul]
    have h1 : ‖(1 : ℂ) / (π * Real.sqrt 2)‖ = 1 / (π * Real.sqrt 2) := by
      rw [show (1 : ℂ) / (π * Real.sqrt 2) = ((1 / (π * Real.sqrt 2) : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    rw [h1]
    gcongr
    exact zcnt_norm_laplace_le (by norm_num) ha (hkey _ _ (by norm_num))

/-- For `x ≥ 1`, `‖f(x)‖ + ‖g(x)‖ < 1/2`. -/
lemma zcnt_fresnelAux_sum_lt {x : ℝ} (hx : 1 ≤ x) :
    ‖fresnelAuxFComplex x‖ + ‖fresnelAuxGComplex x‖ < 1 / 2 := by
  obtain ⟨hF, hG⟩ := zcnt_fresnelAux_norm_le (by linarith : (0 : ℝ) < x)
  have hpi := Real.pi_gt_d2
  have hs2 : (1.41 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hr : 1 / (π * x ^ 2 / 2) ≤ 2 / π := by
    rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
    have : 1 ≤ x ^ 2 := by nlinarith
    nlinarith [Real.pi_pos]
  have hr0 : 0 ≤ 1 / (π * x ^ 2 / 2) := by positivity
  have hr1 : 1 / (π * x ^ 2 / 2) ≤ 1 := hr.trans (by rw [div_le_one Real.pi_pos]; linarith)
  -- Γ(1/2) = √π, Γ(3/2) = √π/2
  have hG12 : Real.Gamma (1 / 2) = Real.sqrt π := Real.Gamma_one_half_eq
  have hG32 : Real.Gamma (3 / 2) = Real.sqrt π / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), hG12]; ring
  -- (1/r)^{1/2} = √(1/r)
  have hF' : ‖fresnelAuxFComplex x‖ ≤ 1 / (π * Real.sqrt 2) *
      (Real.sqrt (2 / π) * Real.sqrt π) := by
    refine hF.trans ?_
    rw [hG12, ← Real.sqrt_eq_rpow]
    gcongr
  have hG' : ‖fresnelAuxGComplex x‖ ≤ 1 / (π * Real.sqrt 2) * (2 / π * (Real.sqrt π / 2)) := by
    refine hG.trans ?_
    rw [hG32]
    gcongr
    calc (1 / (π * x ^ 2 / 2)) ^ (3 / 2 : ℝ) ≤ (1 / (π * x ^ 2 / 2)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by positivity) hr1 (by norm_num)
      _ ≤ 2 / π := by rw [Real.rpow_one]; exact hr
  have hsp : Real.sqrt (2 / π) * Real.sqrt π = Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by positivity), div_mul_cancel₀ _ Real.pi_ne_zero]
  rw [hsp] at hF'
  have hF'' : 1 / (π * Real.sqrt 2) * Real.sqrt 2 = 1 / π := by
    field_simp
  rw [hF''] at hF'
  have hspi : Real.sqrt π < 1.78 := by
    rw [Real.sqrt_lt' (by norm_num)]; linarith [Real.pi_lt_d2]
  have hG'' : 1 / (π * Real.sqrt 2) * (2 / π * (Real.sqrt π / 2)) < 0.17 := by
    rw [show 1 / (π * Real.sqrt 2) * (2 / π * (Real.sqrt π / 2)) =
      Real.sqrt π / (π ^ 2 * Real.sqrt 2) by field_simp]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.sqrt_nonneg π]
  have h1pi : 1 / π < 0.32 := by
    rw [div_lt_iff₀ Real.pi_pos]; linarith
  linarith

/-- `C(x) ≠ 0` for real `x ≠ 0`. -/
theorem zcnt_fresnelCosInt_ofReal_ne_zero {x : ℝ} (hx : x ≠ 0) : fresnelCosInt (x : ℂ) ≠ 0 := by
  wlog hpos : 0 < x generalizing x
  · have hneg : 0 < -x := neg_pos.mpr (lt_of_le_of_ne (not_lt.mp hpos) hx)
    have := this (neg_ne_zero.mpr hx) hneg
    rwa [ofReal_neg, zcnt_fresnelCosInt_neg, neg_ne_zero] at this
  rcases le_or_gt x 1 with h1 | h1
  · rw [fresnelCosInt_ofReal, Complex.ofReal_ne_zero]
    refine (intervalIntegral.intervalIntegral_pos_of_pos_on
      (Continuous.intervalIntegrable (by fun_prop) _ _) (fun t ht => ?_) hpos).ne'
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have : 0 ≤ π * t ^ 2 / 2 := by positivity
      linarith [Real.pi_pos]
    · have ht1 : t < 1 := ht.2.trans_le h1
      have : t ^ 2 < 1 := by nlinarith [ht.1]
      nlinarith [Real.pi_pos]
  · intro h0
    have h := fresnelCosInt_aux (x : ℂ)
    rw [h0] at h
    have hsum := zcnt_fresnelAux_sum_lt h1.le
    have hsin : ‖sin (π * (x : ℂ) ^ 2 / 2)‖ ≤ 1 := by
      rw [show π * (x : ℂ) ^ 2 / 2 = ((π * x ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_sin, Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_sin_le_one _
    have hcos : ‖cos (π * (x : ℂ) ^ 2 / 2)‖ ≤ 1 := by
      rw [show π * (x : ℂ) ^ 2 / 2 = ((π * x ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
    have : (1 / 2 : ℂ) = -(fresnelAuxFComplex x * sin (π * (x : ℂ) ^ 2 / 2)) +
        fresnelAuxGComplex x * cos (π * (x : ℂ) ^ 2 / 2) := by linear_combination -h
    have hn := congrArg norm this
    rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num] at hn
    have := norm_add_le (-(fresnelAuxFComplex x * sin (π * (x : ℂ) ^ 2 / 2)))
      (fresnelAuxGComplex x * cos (π * (x : ℂ) ^ 2 / 2))
    rw [norm_neg, norm_mul, norm_mul] at this
    have := mul_le_of_le_one_right (norm_nonneg (fresnelAuxFComplex x)) hsin
    have := mul_le_of_le_one_right (norm_nonneg (fresnelAuxGComplex x)) hcos
    linarith

/-- `S(x) ≠ 0` for real `x ≠ 0`. -/
theorem zcnt_fresnelSinInt_ofReal_ne_zero {x : ℝ} (hx : x ≠ 0) : fresnelSinInt (x : ℂ) ≠ 0 := by
  wlog hpos : 0 < x generalizing x
  · have hneg : 0 < -x := neg_pos.mpr (lt_of_le_of_ne (not_lt.mp hpos) hx)
    have := this (neg_ne_zero.mpr hx) hneg
    rwa [ofReal_neg, zcnt_fresnelSinInt_neg, neg_ne_zero] at this
  rcases le_or_gt x 1 with h1 | h1
  · rw [fresnelSinInt_ofReal, Complex.ofReal_ne_zero]
    refine (intervalIntegral.intervalIntegral_pos_of_pos_on
      (Continuous.intervalIntegrable (by fun_prop) _ _) (fun t ht => ?_) hpos).ne'
    apply Real.sin_pos_of_pos_of_lt_pi
    · have := ht.1; positivity
    · have ht1 : t < 1 := ht.2.trans_le h1
      have : t ^ 2 < 1 := by nlinarith [ht.1]
      nlinarith [Real.pi_pos]
  · intro h0
    have h := fresnelSinInt_aux (x : ℂ)
    rw [h0] at h
    have hsum := zcnt_fresnelAux_sum_lt h1.le
    have hsin : ‖sin (π * (x : ℂ) ^ 2 / 2)‖ ≤ 1 := by
      rw [show π * (x : ℂ) ^ 2 / 2 = ((π * x ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_sin, Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_sin_le_one _
    have hcos : ‖cos (π * (x : ℂ) ^ 2 / 2)‖ ≤ 1 := by
      rw [show π * (x : ℂ) ^ 2 / 2 = ((π * x ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
    have : (1 / 2 : ℂ) = fresnelAuxFComplex x * cos (π * (x : ℂ) ^ 2 / 2) +
        fresnelAuxGComplex x * sin (π * (x : ℂ) ^ 2 / 2) := by linear_combination -h
    have hn := congrArg norm this
    rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num] at hn
    have := norm_add_le (fresnelAuxFComplex x * cos (π * (x : ℂ) ^ 2 / 2))
      (fresnelAuxGComplex x * sin (π * (x : ℂ) ^ 2 / 2))
    rw [norm_mul, norm_mul] at this
    have := mul_le_of_le_one_right (norm_nonneg (fresnelAuxFComplex x)) hcos
    have := mul_le_of_le_one_right (norm_nonneg (fresnelAuxGComplex x)) hsin
    linarith

/-- `0 < Im w < Re w` places `w` in the open sector `0 < ph w < π/4`. -/
theorem zcnt_arg_mem_of_im_lt_re {w : ℂ} (h0 : 0 < w.im) (h1 : w.im < w.re) :
    0 < arg w ∧ arg w < π / 4 := by
  have hre : 0 < w.re := h0.trans h1
  have hw : w ≠ 0 := fun h => by simp [h] at hre
  constructor
  · refine lt_of_le_of_ne (arg_nonneg_iff.mpr h0.le) (fun h => ?_)
    have := (arg_eq_zero_iff.mp h.symm).2
    linarith
  · have habs : |arg w| < π / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
    have htan : Real.tan (arg w) < Real.tan (π / 4) := by
      rw [tan_arg, Real.tan_pi_div_four, div_lt_one hre]; exact h1
    by_contra hge
    push Not at hge
    have := Real.strictMonoOn_tan.monotoneOn
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      ⟨by linarith [abs_lt.mp habs], (abs_lt.mp habs).2⟩ hge
    linarith

/-- **Octant classification.** Let `f` vanish at `0`, have zero set invariant under `w ↦ -w`,
`w ↦ w̄` and `w ↦ iw`, and have no zero on the real axis or the diagonal `ℝ(1+i)` other than `0`.
If the modulus enumeration of its zeros in the octant `0 < ph z < π/4` is well defined, every zero
of `f` is `0` or one of the eight images `±u, ±ū, ±iu, ±iū` of an enumerated zero `u`. -/
theorem zcnt_octant_classification {f : ℂ → ℂ}
    (hfin : ∀ r : ℝ, {w : ℂ | w ∈ {z : ℂ | 0 < arg z ∧ arg z < π / 4} ∧ f w = 0 ∧
      ‖w‖ < r}.Finite)
    (hspec : ∀ k : ℕ, 1 ≤ k →
      orderedZero f {z : ℂ | 0 < arg z ∧ arg z < π / 4} k ∈ {z : ℂ | 0 < arg z ∧ arg z < π / 4} ∧
      f (orderedZero f {z : ℂ | 0 < arg z ∧ arg z < π / 4} k) = 0 ∧
      ({w : ℂ | w ∈ {z : ℂ | 0 < arg z ∧ arg z < π / 4} ∧ f w = 0 ∧
        ‖w‖ < ‖orderedZero f {z : ℂ | 0 < arg z ∧ arg z < π / 4} k‖} : Set ℂ).ncard = k - 1)
    (h00 : f 0 = 0) (hneg : ∀ w, f (-w) = 0 ↔ f w = 0) (hconj : ∀ w, f (star w) = 0 ↔ f w = 0)
    (hI : ∀ w, f (I * w) = 0 ↔ f w = 0) (hreal : ∀ x : ℝ, x ≠ 0 → f x ≠ 0)
    (hdiag : ∀ x : ℝ, x ≠ 0 → f ((1 + I) * x) ≠ 0) (z : ℂ) :
    f z = 0 ↔ z = 0 ∨ ∃ k : ℕ, 1 ≤ k ∧
      let u := orderedZero f {z : ℂ | 0 < arg z ∧ arg z < π / 4} k
      z = u ∨ z = -u ∨ z = star u ∨ z = -star u ∨ z = I * u ∨ z = -I * u ∨ z = I * star u ∨
        z = -I * star u := by
  set S : Set ℂ := {z : ℂ | 0 < arg z ∧ arg z < π / 4}
  have henum : ∀ w : ℂ, 0 < w.im → w.im < w.re → f w = 0 →
      ∃ k : ℕ, 1 ≤ k ∧ w = orderedZero f S k := fun w h1 h2 h0 =>
    zcnt_eq_orderedZero hfin hspec (zcnt_arg_mem_of_im_lt_re h1 h2) h0
  have hnegI : ∀ w, f (-I * w) = 0 ↔ f w = 0 := fun w => by
    rw [show -I * w = -(I * w) by ring, hneg, hI]
  constructor
  · intro h0
    by_cases hz : z = 0
    · exact Or.inl hz
    right
    set x := z.re
    set y := z.im
    have hzxy : z = x + y * I := (Complex.re_add_im z).symm
    have hy : y ≠ 0 := by
      intro hy
      have : z = (x : ℂ) := by rw [hzxy, hy]; simp
      have hx : x ≠ 0 := fun hx => hz (by rw [this, hx]; simp)
      exact hreal x hx (this ▸ h0)
    have hx : x ≠ 0 := by
      intro hx
      have : z = I * (y : ℂ) := by rw [hzxy, hx]; simp; ring
      exact hreal y hy ((hI _).mp (this ▸ h0))
    have hd1 : x ≠ y := by
      intro hxy
      have : z = (1 + I) * (x : ℂ) := by rw [hzxy, ← hxy]; ring
      exact hdiag x hx (this ▸ h0)
    have hd2 : x ≠ -y := by
      intro hxy
      have : z = star ((1 + I) * (x : ℂ)) := by
        rw [hzxy, hxy]; apply Complex.ext <;> simp
      exact hdiag x hx ((hconj _).mp (this ▸ h0))
    rcases hx.lt_or_gt with hx0 | hx0 <;> rcases hy.lt_or_gt with hy0 | hy0
    · -- third quadrant
      rcases lt_or_gt_of_ne hd1 with h | h
      · -- y < x < 0 ... here x < y
        obtain ⟨k, hk, hw⟩ := henum (-z) (by simp; linarith) (by simp; linarith)
          ((hneg z).mpr h0)
        exact ⟨k, hk, Or.inr (Or.inl (by rw [← hw, neg_neg]))⟩
      · obtain ⟨k, hk, hw⟩ := henum (star (I * z)) (by simp; linarith)
          (by simp; linarith) ((hconj _).mpr ((hI z).mpr h0))
        refine ⟨k, hk, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))⟩
        rw [← hw, star_star]
        linear_combination z * I_sq
    · -- second quadrant: x < 0 < y
      rcases lt_or_gt_of_ne hd2 with h | h
      · obtain ⟨k, hk, hw⟩ := henum (-star z) (by simp; linarith)
          (by simp; linarith) ((hneg _).mpr ((hconj z).mpr h0))
        exact ⟨k, hk, Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hw, star_neg, star_star, neg_neg]))))⟩
      · -- -x < y
        obtain ⟨k, hk, hw⟩ := henum (-I * z) (by simp; linarith)
          (by simp; linarith) ((hnegI z).mpr h0)
        refine ⟨k, hk, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))⟩
        rw [← hw]
        linear_combination z * I_sq
    · -- fourth quadrant: y < 0 < x
      rcases lt_or_gt_of_ne hd2 with h | h
      · -- x < -y
        obtain ⟨k, hk, hw⟩ := henum (I * z) (by simp; linarith)
          (by simp; linarith) ((hI z).mpr h0)
        refine ⟨k, hk, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))⟩
        rw [← hw]
        linear_combination z * I_sq
      · obtain ⟨k, hk, hw⟩ := henum (star z) (by simp; linarith)
          (by simp; linarith) ((hconj z).mpr h0)
        exact ⟨k, hk, Or.inr (Or.inr (Or.inl (by rw [← hw, star_star])))⟩
    · -- first quadrant
      rcases lt_or_gt_of_ne hd1 with h | h
      · obtain ⟨k, hk, hw⟩ := henum (star (-I * z)) (by simp; linarith)
          (by simp; linarith) ((hconj _).mpr ((hnegI z).mpr h0))
        refine ⟨k, hk, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))⟩
        rw [← hw, star_star]
        linear_combination z * I_sq
      · obtain ⟨k, hk, hw⟩ := henum z hy0 h h0
        exact ⟨k, hk, Or.inl hw⟩
  · rintro (rfl | ⟨k, hk, h⟩)
    · exact h00
    have hu := (hspec k hk).2.1
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hu
    · exact (hneg _).mpr hu
    · exact (hconj _).mpr hu
    · exact (hneg _).mpr ((hconj _).mpr hu)
    · exact (hI _).mpr hu
    · exact (hnegI _).mpr hu
    · exact (hI _).mpr ((hconj _).mpr hu)
    · exact (hnegI _).mpr ((hconj _).mpr hu)

end DLMF.Confluent
