/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.AngerWeber.IntegralAndSeries

/-!
# Lommel connections of Anger and Weber functions

Regularized Lommel solutions, noninteger-order connections and integral consequences for Anger
and Weber functions.

Source references and common attribution are retained in
`DLMF.Struve.AngerWeber`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Struve

open DLMF.Bessel DLMF.Confluent

/-- `(0, ν)` is a regular Lommel pair off the integers. -/
theorem lommelRegular_zero_of_not_int {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) : LommelRegular 0 ν :=
  fun n => ⟨fun h => hν (2*n+1) (by push_cast; linear_combination -h),
    fun h => hν (-(2*n+1)) (by push_cast; linear_combination h)⟩

/-- `(-1, ν)` is a regular Lommel pair off the integers. -/
theorem lommelRegular_neg_one_of_not_int {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) : LommelRegular (-1) ν :=
  fun n => ⟨fun h => hν (2*n) (by push_cast; linear_combination -h),
    fun h => hν (-(2*n)) (by push_cast; linear_combination h)⟩

/-- The Gamma factors of `s_{0,ν}` and `s_{-1,ν}` off the integers. -/
theorem lommel_Gamma_factors {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) :
    Gamma ((0-ν+1)/2)*Gamma ((0+ν+1)/2) = π/cos (π*ν/2) ∧
    Gamma ((-1-ν+1)/2)*Gamma ((-1+ν+1)/2) = -2*π/(ν*sin (π*ν/2)) := by
  constructor
  · have h := Complex.Gamma_mul_Gamma_one_sub ((1+ν)/2)
    rw [show π*((1+ν)/2) = π*ν/2 + π/2 by ring, Complex.sin_add_pi_div_two,
      show 1-(1+ν)/2 = (0-ν+1)/2 by ring, show (1+ν)/2 = (0+ν+1)/2 by ring] at h
    rw [mul_comm, h]
  · have hν0 : ν ≠ 0 := by simpa using hν 0
    have h2 : -ν/2 ≠ 0 := by
      intro h; apply hν0; linear_combination -2*h
    have h := Complex.Gamma_mul_Gamma_one_sub (ν/2)
    have ha := Complex.Gamma_add_one (-ν/2) h2
    have hs := sin_pi_mul_ne_zero_of_not_int (not_int_half hν)
    rw [show -ν/2+1 = 1-ν/2 by ring] at ha
    rw [show (-1-ν+1)/2 = -ν/2 by ring, show (-1+ν+1)/2 = ν/2 by ring]
    rw [ha] at h
    have h' := (eq_div_iff hs).1 h
    rw [show π*ν/2 = π*(ν/2) by ring, eq_div_iff (mul_ne_zero hν0 hs)]
    linear_combination (-2:ℂ)*h'

/-- `s_{0,ν}` and `s_{-1,ν}` as regularized `₁F₂` functions off the integers. -/
theorem lommel_zero_neg_one_regularized {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (z : ℂ) :
    lommelS 0 ν z = z/2*(π/(2*cos (π*ν/2)))*
      regularizedHGFun {1} {ν/2+3/2, -ν/2+3/2} (-z^2/4) ∧
    lommelS (-1) ν z = -π/(2*ν*sin (π*ν/2))*
      regularizedHGFun {1} {ν/2+1, -ν/2+1} (-z^2/4) := by
  obtain ⟨hG0, hG1⟩ := lommel_Gamma_factors hν
  constructor
  · rw [lommelS_eq_regularized (lommelRegular_zero_of_not_int hν), hG0, zero_add, cpow_one,
      show (0-ν+3)/2 = -ν/2+3/2 by ring, show (0+ν+3)/2 = ν/2+3/2 by ring,
      Multiset.pair_comm]
    ring
  · rw [lommelS_eq_regularized (lommelRegular_neg_one_of_not_int hν), hG1, neg_add_cancel,
      cpow_zero, show (-1-ν+3)/2 = -ν/2+1 by ring, show (-1+ν+3)/2 = ν/2+1 by ring,
      Multiset.pair_comm]
    ring

/-- Identity under the stated parameter and domain assumptions: `angerJ ν z = sin (π*ν)/π*(lommelS
0 ν z-ν*lommelS (-1) ν z)`. -/
@[dlmf 11.10.E17]
theorem angerJ_lommel {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) {z : ℂ} (hz : z ∈ slitPlane) :
    angerJ ν z = sin (π*ν)/π*(lommelS 0 ν z-ν*lommelS (-1) ν z) := by
  obtain ⟨h0, h1⟩ := lommel_zero_neg_one_regularized hν z
  have hν0 : ν ≠ 0 := by simpa using hν 0
  have hs := sin_pi_mul_ne_zero_of_not_int (not_int_half hν)
  have hc : cos (π*ν/2) ≠ 0 := by
    have := sin_pi_mul_ne_zero_of_not_int (not_int_half_add hν)
    rwa [show π*((1+ν)/2) = π*ν/2 + π/2 by ring, Complex.sin_add_pi_div_two] at this
  rw [show π*(ν/2) = π*ν/2 by ring] at hs
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [angerJ_series, angerS1_eq_regularized, angerS2_eq_regularized, h0, h1,
    show π*ν = 2*(π*ν/2) by ring, Complex.sin_two_mul]
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `weberE ν z = -(1+cos
(π*ν))/π*lommelS 0 ν z-ν/π*(1-cos (π*ν))*lommelS (-1) ν z`. -/
@[dlmf 11.10.E18]
theorem weberE_lommel {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) {z : ℂ} (hz : z ∈ slitPlane) :
    weberE ν z = -(1+cos (π*ν))/π*lommelS 0 ν z-ν/π*(1-cos (π*ν))*lommelS (-1) ν z := by
  obtain ⟨h0, h1⟩ := lommel_zero_neg_one_regularized hν z
  have hν0 : ν ≠ 0 := by simpa using hν 0
  have hs := sin_pi_mul_ne_zero_of_not_int (not_int_half hν)
  have hc : cos (π*ν/2) ≠ 0 := by
    have := sin_pi_mul_ne_zero_of_not_int (not_int_half_add hν)
    rwa [show π*((1+ν)/2) = π*ν/2 + π/2 by ring, Complex.sin_add_pi_div_two] at this
  rw [show π*(ν/2) = π*ν/2 by ring] at hs
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hsc := Complex.sin_sq_add_cos_sq (π*ν/2)
  rw [weberE_series, angerS1_eq_regularized, angerS2_eq_regularized, h0, h1,
    show π*ν = 2*(π*ν/2) by ring, Complex.cos_two_mul]
  field_simp
  linear_combination (4 * cos (π*ν/2) *
    regularizedHGFun {1} {(ν + 2) / 2, (-ν + 2) / 2} (-(z ^ 2 / 4))) * hsc

/-- The sum of the complex Fresnel cosine and sine integrals used in half-integer Anger formulas. -/
@[dlmf 11.10.E21]
def angerFresnelPlus (z : ℂ) : ℂ :=
  fresnelCosInt z+fresnelSinInt z

/-- The difference of the complex Fresnel cosine and sine integrals used in half-integer Anger
formulas. -/
@[dlmf 11.10.E21]
def angerFresnelMinus (z : ℂ) : ℂ :=
  fresnelCosInt z-fresnelSinInt z

/-- Weighted derivative identity `z 𝐉_ν' + ν 𝐉_ν = z 𝐉_{ν-1} + sin(πν)/π` away from the origin. -/
theorem angerHalf_weighted_add (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    z*deriv (angerJ ν) z+(1:ℂ)*ν*angerJ ν z = (1:ℂ)*z*angerJ (ν-1) z+(1:ℂ)*(sin (π*ν))/π := by
  rw [(hasDerivAt_angerJ_shift ν z).deriv]
  have := angerJ_recurrence_aux ν hz
  rw [show angerJ (ν+1) z = 2*ν/z*angerJ ν z-2/(π*z)*(sin (π*ν))-angerJ (ν-1) z by
    linear_combination this]
  field_simp
  ring

/-- Weighted derivative identity `z 𝐉_ν' - ν 𝐉_ν = -z 𝐉_{ν+1} - sin(πν)/π` away from the
origin. -/
theorem angerHalf_weighted_sub (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    z*deriv (angerJ ν) z+(-1:ℂ)*ν*angerJ ν z =
      (-1:ℂ)*z*angerJ (ν-(-1)) z+(-1:ℂ)*(sin (π*ν))/π := by
  rw [(hasDerivAt_angerJ_shift ν z).deriv, sub_neg_eq_add]
  have := angerJ_recurrence_aux ν hz
  rw [show angerJ (ν-1) z = 2*ν/z*angerJ ν z-2/(π*z)*(sin (π*ν))-angerJ (ν+1) z by
    linear_combination this]
  field_simp
  ring

/-- Defect of DLMF 11.10.20, scaled by `√(πx/2)`, on the real line. -/
noncomputable def angerHalfDefectF (x : ℝ) : ℂ :=
  (Real.sqrt (π * x / 2) : ℂ) * angerJ (1/2) x -
    (angerFresnelPlus (Real.sqrt (2 * x / π)) * sin x +
      angerFresnelMinus (Real.sqrt (2 * x / π)) * cos x)

/-- Defect of DLMF 11.10.19, scaled by `√(πx/2)`, on the real line. -/
noncomputable def angerHalfDefectG (x : ℝ) : ℂ :=
  (Real.sqrt (π * x / 2) : ℂ) * angerJ (-1/2) x -
    (angerFresnelPlus (Real.sqrt (2 * x / π)) * cos x -
      angerFresnelMinus (Real.sqrt (2 * x / π)) * sin x)

/-- `d/dx √(cx) = √(cx)/(2x)` for `c, x > 0`, as a complex-valued function. -/
theorem hasDerivAt_sqrt_mul (c : ℝ) (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (Real.sqrt (c * x) : ℂ))
      ((Real.sqrt (c * x) : ℂ) / (2 * x)) x := by
  have h := ((Real.hasDerivAt_sqrt (by positivity : c * x ≠ 0)).comp x
    ((hasDerivAt_id x).const_mul c)).ofReal_comp
  refine h.congr_deriv ?_
  have hs : Real.sqrt (c * x) ^ 2 = c * x := Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (c * x) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have h0 : ((Real.sqrt (c * x)) : ℂ) ≠ 0 := ofReal_ne_zero.2 hs0
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have : ((Real.sqrt (c * x)) : ℂ) ^ 2 = c * x := by exact_mod_cast hs
  push_cast
  field_simp
  linear_combination -this

/-- Derivatives of `C(√(2x/π))` and `S(√(2x/π))`. -/
theorem hasDerivAt_fresnel_sqrt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => fresnelCosInt (Real.sqrt (2 * x / π)))
        (cos x * ((Real.sqrt (2 * x / π) : ℂ) / (2 * x))) x ∧
      HasDerivAt (fun x : ℝ => fresnelSinInt (Real.sqrt (2 * x / π)))
        (sin x * ((Real.sqrt (2 * x / π) : ℂ) / (2 * x))) x := by
  have hw := hasDerivAt_sqrt_mul (2 / π) (by positivity) hx
  simp only [show ∀ y : ℝ, 2 / π * y = 2 * y / π from fun y => by ring] at hw
  have hw2 : π * ((Real.sqrt (2 * x / π) : ℝ) : ℂ) ^ 2 / 2 = x := by
    have : Real.sqrt (2 * x / π) ^ 2 = 2 * x / π := Real.sq_sqrt (by positivity)
    have h' : ((Real.sqrt (2 * x / π) : ℝ) : ℂ) ^ 2 = 2 * x / π := by exact_mod_cast this
    rw [h']
    have : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    field_simp
  constructor
  · have := (hasDerivAt_fresnelCosInt_complex _).comp x hw
    rwa [hw2] at this
  · have := (hasDerivAt_fresnelSinInt_complex _).comp x hw
    rwa [hw2] at this

/-- `sin(π/2) = 1` in complex form. -/
theorem sin_pi_mul_half_complex : sin (π * (1/2 : ℂ)) = 1 := by
  rw [show π * (1/2 : ℂ) = (π/2 : ℝ) by push_cast; ring, ← ofReal_sin, Real.sin_pi_div_two]
  simp

/-- `2√(πx/2) = π√(2x/π)`. -/
theorem two_mul_sqrt_eq_pi_mul_sqrt (x : ℝ) :
    2 * (Real.sqrt (π * x / 2) : ℂ) = π * Real.sqrt (2 * x / π) := by
  have h : 2 * Real.sqrt (π * x / 2) = π * Real.sqrt (2 * x / π) := by
    rw [← Real.sqrt_sq (zero_le_two : (0:ℝ) ≤ 2), ← Real.sqrt_mul (sq_nonneg _),
      ← Real.sqrt_sq Real.pi_pos.le, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq zero_le_two,
      Real.sqrt_sq Real.pi_pos.le]
    congr 1
    have := Real.pi_pos
    field_simp
  exact_mod_cast h

/-- The scaled defects satisfy `F' = G`. -/
theorem hasDerivAt_angerHalfDefectF {x : ℝ} (hx : 0 < x) :
    HasDerivAt angerHalfDefectF (angerHalfDefectG x) x := by
  have hs := hasDerivAt_sqrt_mul (π / 2) (by positivity) hx
  simp only [show ∀ y : ℝ, π / 2 * y = π * y / 2 from fun y => by ring] at hs
  have ha := (angerJ_entire (1/2) (x : ℂ)).hasDerivAt.comp_ofReal
  obtain ⟨hC, hS⟩ := hasDerivAt_fresnel_sqrt hx
  have hsin := (Complex.hasDerivAt_sin (x : ℂ)).comp_ofReal
  have hcos := (Complex.hasDerivAt_cos (x : ℂ)).comp_ofReal
  have h := (hs.mul ha).sub (((hC.add hS).mul hsin).add ((hC.sub hS).mul hcos))
  unfold angerHalfDefectF
  refine h.congr_deriv ?_
  have hw := angerHalf_weighted_add (1/2) (ofReal_ne_zero.2 hx.ne')
  rw [show (1/2 : ℂ) - 1 = -1/2 by norm_num, sin_pi_mul_half_complex] at hw
  have hsw := two_mul_sqrt_eq_pi_mul_sqrt x
  have htrig := sin_sq_add_cos_sq (x : ℂ)
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  unfold angerHalfDefectG angerFresnelPlus angerFresnelMinus
  simp only [Pi.add_apply, Pi.sub_apply]
  set s : ℂ := (Real.sqrt (π * x / 2) : ℂ)
  set w : ℂ := (Real.sqrt (2 * x / π) : ℂ)
  set D := deriv (angerJ (1/2)) (x : ℂ)
  have hD : D = (x * angerJ (-1/2) x + 1 / π - angerJ (1/2) x / 2) / x := by
    rw [eq_div_iff hx0]; linear_combination hw
  rw [hD]
  field_simp
  linear_combination hsw - π * w * htrig

/-- The scaled defects satisfy `G' = -F`. -/
theorem hasDerivAt_angerHalfDefectG {x : ℝ} (hx : 0 < x) :
    HasDerivAt angerHalfDefectG (-angerHalfDefectF x) x := by
  have hs := hasDerivAt_sqrt_mul (π / 2) (by positivity) hx
  simp only [show ∀ y : ℝ, π / 2 * y = π * y / 2 from fun y => by ring] at hs
  have ha := (angerJ_entire (-1/2) (x : ℂ)).hasDerivAt.comp_ofReal
  obtain ⟨hC, hS⟩ := hasDerivAt_fresnel_sqrt hx
  have hsin := (Complex.hasDerivAt_sin (x : ℂ)).comp_ofReal
  have hcos := (Complex.hasDerivAt_cos (x : ℂ)).comp_ofReal
  have h := (hs.mul ha).sub (((hC.add hS).mul hcos).sub ((hC.sub hS).mul hsin))
  unfold angerHalfDefectG
  refine h.congr_deriv ?_
  have hw := angerHalf_weighted_sub (-1/2) (ofReal_ne_zero.2 hx.ne')
  have hsn : sin (π * (-1/2 : ℂ)) = -1 := by
    rw [show π * (-1/2 : ℂ) = -(π * (1/2 : ℂ)) by ring, sin_neg, sin_pi_mul_half_complex]
  rw [show (-1/2 : ℂ) - (-1) = 1/2 by norm_num, hsn] at hw
  have hsw := two_mul_sqrt_eq_pi_mul_sqrt x
  have htrig := sin_sq_add_cos_sq (x : ℂ)
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  unfold angerHalfDefectF angerFresnelPlus angerFresnelMinus
  simp only [Pi.add_apply, Pi.sub_apply]
  set s : ℂ := (Real.sqrt (π * x / 2) : ℂ)
  set w : ℂ := (Real.sqrt (2 * x / π) : ℂ)
  set D := deriv (angerJ (-1/2)) (x : ℂ)
  have hD : D = (-(x * angerJ (1/2) x) + 1 / π - angerJ (-1/2) x / 2) / x := by
    rw [eq_div_iff hx0]; linear_combination hw
  rw [hD]
  field_simp
  linear_combination hsw - π * w * htrig

/-- Continuity of the defect `F`. -/
theorem continuous_angerHalfDefectF : Continuous angerHalfDefectF := by
  have h1 : Continuous fun x : ℝ => angerJ (1/2) x := (angerJ_entire _).continuous.comp continuous_ofReal
  have hw : Continuous fun x : ℝ => ((Real.sqrt (2 * x / π) : ℝ) : ℂ) :=
    continuous_ofReal.comp (by fun_prop)
  have hC := fresnelCosInt_entire.continuous.comp hw
  have hS := fresnelSinInt_entire.continuous.comp hw
  unfold angerHalfDefectF angerFresnelPlus angerFresnelMinus
  exact ((continuous_ofReal.comp (by fun_prop)).mul h1).sub
    (((hC.add hS).mul (by fun_prop)).add ((hC.sub hS).mul (by fun_prop)))

/-- Continuity of the defect `G`. -/
theorem continuous_angerHalfDefectG : Continuous angerHalfDefectG := by
  have h1 : Continuous fun x : ℝ => angerJ (-1/2) x :=
    (angerJ_entire _).continuous.comp continuous_ofReal
  have hw : Continuous fun x : ℝ => ((Real.sqrt (2 * x / π) : ℝ) : ℂ) :=
    continuous_ofReal.comp (by fun_prop)
  have hC := fresnelCosInt_entire.continuous.comp hw
  have hS := fresnelSinInt_entire.continuous.comp hw
  unfold angerHalfDefectG angerFresnelPlus angerFresnelMinus
  exact ((continuous_ofReal.comp (by fun_prop)).mul h1).sub
    (((hC.add hS).mul (by fun_prop)).sub ((hC.sub hS).mul (by fun_prop)))

/-- Both defects vanish at the origin. -/
theorem angerHalfDefect_zero : angerHalfDefectF 0 = 0 ∧ angerHalfDefectG 0 = 0 := by
  simp [angerHalfDefectF, angerHalfDefectG, angerFresnelPlus, angerFresnelMinus,
    fresnelCosInt, fresnelSinInt]

/-- A function on `[0, ∞)` with zero derivative on `(0, ∞)` and continuous at `0` is constant. -/
theorem angerHalf_eq_of_hasDerivAt_zero {u : ℝ → ℂ} (hu : Continuous u)
    (hd : ∀ x, 0 < x → HasDerivAt u 0 x) {x : ℝ} (hx : 0 < x) : u x = u 0 := by
  have hconst : ∀ y, 0 < y → u y = u x := fun y hy =>
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hd z hz).deriv) hy hx
  have ht : Tendsto u (𝓝[>] 0) (𝓝 (u 0)) := (hu.tendsto 0).mono_left nhdsWithin_le_nhds
  have ht' : Tendsto u (𝓝[>] 0) (𝓝 (u x)) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun y hy => (hconst y hy).symm)
  exact tendsto_nhds_unique ht' ht

/-- Both defects vanish on `(0, ∞)`: `F cos - G sin` and `F sin + G cos` are constant. -/
theorem angerHalfDefect_eq_zero {x : ℝ} (hx : 0 < x) :
    angerHalfDefectF x = 0 ∧ angerHalfDefectG x = 0 := by
  set u : ℝ → ℂ := fun y => angerHalfDefectF y * cos y - angerHalfDefectG y * sin y
  set v' : ℝ → ℂ := fun y => angerHalfDefectF y * sin y + angerHalfDefectG y * cos y
  have hsin (y : ℝ) := (Complex.hasDerivAt_sin (y : ℂ)).comp_ofReal
  have hcos (y : ℝ) := (Complex.hasDerivAt_cos (y : ℂ)).comp_ofReal
  have hu : ∀ y, 0 < y → HasDerivAt u 0 y := fun y hy => by
    have := ((hasDerivAt_angerHalfDefectF hy).mul (hcos y)).sub
      ((hasDerivAt_angerHalfDefectG hy).mul (hsin y))
    refine this.congr_deriv ?_
    ring
  have hv : ∀ y, 0 < y → HasDerivAt v' 0 y := fun y hy => by
    have := ((hasDerivAt_angerHalfDefectF hy).mul (hsin y)).add
      ((hasDerivAt_angerHalfDefectG hy).mul (hcos y))
    refine this.congr_deriv ?_
    ring
  have hcu : Continuous u := by
    exact (continuous_angerHalfDefectF.mul (by fun_prop)).sub
      (continuous_angerHalfDefectG.mul (by fun_prop))
  have hcv : Continuous v' := by
    exact (continuous_angerHalfDefectF.mul (by fun_prop)).add
      (continuous_angerHalfDefectG.mul (by fun_prop))
  have hu0 := angerHalf_eq_of_hasDerivAt_zero hcu hu hx
  have hv0 := angerHalf_eq_of_hasDerivAt_zero hcv hv hx
  obtain ⟨hF0, hG0⟩ := angerHalfDefect_zero
  simp only [u, v', hF0, hG0, zero_mul, sub_zero, add_zero] at hu0 hv0
  have htrig := sin_sq_add_cos_sq (x : ℂ)
  constructor
  · linear_combination cos (x : ℂ) * hu0 + sin (x : ℂ) * hv0 +
      -angerHalfDefectF x * htrig
  · linear_combination -sin (x : ℂ) * hu0 + cos (x : ℂ) * hv0 +
      -angerHalfDefectG x * htrig

/-- `r^{1/2} = √r` for `r ≥ 0`. -/
theorem ofReal_cpow_half {r : ℝ} (hr : 0 ≤ r) : (r : ℂ) ^ (1/2 : ℂ) = (Real.sqrt r : ℂ) := by
  rw [Real.sqrt_eq_rpow, ofReal_cpow hr]; push_cast; ring_nf

/-- `r^{-1/2} = (√r)⁻¹` for `r ≥ 0`. -/
theorem ofReal_cpow_neg_half {r : ℝ} (hr : 0 ≤ r) :
    (r : ℂ) ^ (-1/2 : ℂ) = ((Real.sqrt r : ℂ))⁻¹ := by
  rw [show (-1/2 : ℂ) = -(1/2) by ring, cpow_neg, ofReal_cpow_half hr]

/-- The slit plane is invariant under positive real scaling. -/
theorem mul_mem_slitPlane_of_pos {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ slitPlane) :
    (r : ℂ) * z ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, mul_im, add_zero]
  rcases hz with h | h
  · exact Or.inl (mul_pos hr h)
  · exact Or.inr (mul_ne_zero hr.ne' h)

/-- Positive reals accumulate at `1` in the punctured complex neighbourhood. -/
theorem frequently_ofReal_pos {P : ℂ → Prop} (hP : ∀ x : ℝ, 0 < x → P x) :
    ∃ᶠ z in 𝓝[≠] (1 : ℂ), P z := by
  have hu : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
      rw [add_zero] at this
      have h2 := (continuous_ofReal.tendsto _).comp this
      simpa [Function.comp_def] using h2
    · simp only [mem_compl_iff, mem_singleton_iff]
      intro h
      have h' : (1 + 1 / ((n:ℝ) + 1) : ℝ) = 1 := by exact_mod_cast h
      have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      linarith
  exact hu.frequently (Frequently.of_forall fun n => hP _ (by positivity))

/-- The Fresnel right-hand sides of DLMF 11.10.19–20 are holomorphic on the slit plane. -/
theorem differentiableOn_angerHalf_rhs (A B : ℂ → ℂ) (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) :
    DifferentiableOn ℂ (fun z : ℂ => (π*z/2)^(-1/2:ℂ) *
      (angerFresnelPlus ((2*z/π)^(1/2:ℂ)) * A z - angerFresnelMinus ((2*z/π)^(1/2:ℂ)) * B z))
      slitPlane := by
  intro z hz
  have h1 : π * z / 2 ∈ slitPlane := by
    have := mul_mem_slitPlane_of_pos (by positivity : (0:ℝ) < π / 2) hz
    convert this using 1; push_cast; ring
  have h2 : 2 * z / π ∈ slitPlane := by
    have := mul_mem_slitPlane_of_pos (by positivity : (0:ℝ) < 2 / π) hz
    convert this using 1; push_cast; ring
  have hc1 : DifferentiableAt ℂ (fun z : ℂ => (π*z/2)^(-1/2:ℂ)) z :=
    DifferentiableAt.cpow (by fun_prop) (differentiableAt_const _) h1
  have hc2 : DifferentiableAt ℂ (fun z : ℂ => (2*z/π)^(1/2:ℂ)) z :=
    DifferentiableAt.cpow (by fun_prop) (differentiableAt_const _) h2
  have hP : DifferentiableAt ℂ (fun z : ℂ => angerFresnelPlus ((2*z/π)^(1/2:ℂ))) z := by
    unfold angerFresnelPlus
    exact ((fresnelCosInt_entire _).comp z hc2).add ((fresnelSinInt_entire _).comp z hc2)
  have hM : DifferentiableAt ℂ (fun z : ℂ => angerFresnelMinus ((2*z/π)^(1/2:ℂ))) z := by
    unfold angerFresnelMinus
    exact ((fresnelCosInt_entire _).comp z hc2).sub ((fresnelSinInt_entire _).comp z hc2)
  exact (hc1.mul ((hP.mul (hA z)).sub (hM.mul (hB z)))).differentiableWithinAt

/-- The slit plane is preconnected. -/
theorem isPreconnected_slitPlane' : IsPreconnected slitPlane :=
  (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected

/-- Identity under the stated parameter and domain assumptions: `angerJ (-1/2) z =
(π*z/2)^(-1/2:ℂ)*(angerFresnelPlus ((2*z/π)^(1/2:ℂ))*cos z-angerFresnelMinus
((2*z/π)^(1/2:ℂ))*sin z)`. -/
@[dlmf 11.10.E19]
theorem angerJ_half_19 {z : ℂ} (hz : z ∈ slitPlane) :
    angerJ (-1/2) z = (π*z/2)^(-1/2:ℂ)*(angerFresnelPlus ((2*z/π)^(1/2:ℂ))*cos z-angerFresnelMinus ((2*z/π)^(1/2:ℂ))*sin z) := by
  have hf : AnalyticOnNhd ℂ (angerJ (-1/2)) slitPlane :=
    (analyticOnNhd_univ_iff_differentiable.2 (angerJ_entire _)).mono (subset_univ _)
  have hg := (differentiableOn_angerHalf_rhs cos sin differentiable_cos differentiable_sin).analyticOnNhd
    isOpen_slitPlane
  refine hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_slitPlane' one_mem_slitPlane
    (frequently_ofReal_pos fun x hx => ?_) hz
  have h := (angerHalfDefect_eq_zero hx).2
  unfold angerHalfDefectG at h
  have hs0 : (Real.sqrt (π * x / 2) : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (Real.sqrt_pos.2 (by positivity)).ne'
  rw [show π * (x : ℂ) / 2 = ((π * x / 2 : ℝ) : ℂ) by push_cast; ring,
    show 2 * (x : ℂ) / π = ((2 * x / π : ℝ) : ℂ) by push_cast; ring,
    ofReal_cpow_neg_half (by positivity), ofReal_cpow_half (by positivity),
    eq_inv_mul_iff_mul_eq₀ hs0]
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `angerJ (1/2) z =
(π*z/2)^(-1/2:ℂ)*(angerFresnelPlus ((2*z/π)^(1/2:ℂ))*sin z+angerFresnelMinus
((2*z/π)^(1/2:ℂ))*cos z)`. -/
@[dlmf 11.10.E20]
theorem angerJ_half_20 {z : ℂ} (hz : z ∈ slitPlane) :
    angerJ (1/2) z = (π*z/2)^(-1/2:ℂ)*(angerFresnelPlus ((2*z/π)^(1/2:ℂ))*sin z+angerFresnelMinus ((2*z/π)^(1/2:ℂ))*cos z) := by
  have hf : AnalyticOnNhd ℂ (angerJ (1/2)) slitPlane :=
    (analyticOnNhd_univ_iff_differentiable.2 (angerJ_entire _)).mono (subset_univ _)
  have hg := (differentiableOn_angerHalf_rhs sin (fun z => -cos z) differentiable_sin
    differentiable_cos.neg).analyticOnNhd isOpen_slitPlane
  have key := hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_slitPlane'
    one_mem_slitPlane (frequently_ofReal_pos fun x hx => ?_) hz
  · rw [key]; ring
  have h := (angerHalfDefect_eq_zero hx).1
  unfold angerHalfDefectF at h
  have hs0 : (Real.sqrt (π * x / 2) : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (Real.sqrt_pos.2 (by positivity)).ne'
  rw [show π * (x : ℂ) / 2 = ((π * x / 2 : ℝ) : ℂ) by push_cast; ring,
    show 2 * (x : ℂ) / π = ((2 * x / π : ℝ) : ℂ) by push_cast; ring,
    ofReal_cpow_neg_half (by positivity), ofReal_cpow_half (by positivity),
    eq_inv_mul_iff_mul_eq₀ hs0]
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `angerJ (-1/2) z = weberE (1/2) z
∧ angerJ (1/2) z = -weberE (-1/2) z`. -/
@[dlmf 11.10.E19, dlmf 11.10.E20]
theorem anger_weber_half (z : ℂ) :
    angerJ (-1/2) z = weberE (1/2) z ∧ angerJ (1/2) z = -weberE (-1/2) z := by
  have hc : cos (π*(1/2:ℂ)) = 0 := by
    rw [show π*(1/2:ℂ) = (π/2:ℝ) by push_cast; ring, ← ofReal_cos, Real.cos_pi_div_two]; simp
  have hs : sin (π*(1/2:ℂ)) = 1 := by
    rw [show π*(1/2:ℂ) = (π/2:ℝ) by push_cast; ring, ← ofReal_sin, Real.sin_pi_div_two]; simp
  have h1 := weber_anger (1/2) z
  have h2 := anger_weber (1/2) z
  rw [hc, hs] at h1 h2
  rw [show (-1/2:ℂ) = -(1/2) by ring]
  constructor
  · linear_combination -h1
  · linear_combination h2

/-- Number of terms floor((n-1)/2)+1, with empty case n=0. This is `(n+1)/2` in
natural-number division (corrected 2026-10-20 from `n/2`, which gave no term at `n = 1`). -/
@[dlmf 11.10.E24]
def weberM1 (n : ℕ) : ℕ :=
  (n+1)/2

/-- Number of terms ceil((n-3)/2)+1 for n positive. -/
@[dlmf 11.10.E24]
def weberM2 (n : ℕ) : ℕ :=
  n/2

/-- `cos(nπ) = (-1)ⁿ` in `ℂ`. -/
theorem cos_nat_mul_pi_complex (n : ℕ) : cos ((n:ℂ)*π) = (-1)^n := by
  rw [show (n:ℂ)*π = ((n*π:ℝ):ℂ) by push_cast; ring, ← ofReal_cos, Real.cos_nat_mul_pi]
  push_cast; ring

/-- `Γ(1/2 + j) Γ(1/2 - j) = (-1)^j π`. -/
theorem Gamma_half_add_mul_Gamma_half_sub (j : ℕ) :
    Gamma (1/2+j) * Gamma (1/2-j) = (-1)^j * π := by
  have h := Complex.Gamma_mul_Gamma_one_sub (1/2+j)
  rw [show 1-(1/2+(j:ℂ)) = 1/2-j by ring, show (π:ℂ)*(1/2+j) = j*π + π/2 by ring,
    Complex.sin_add_pi_div_two, cos_nat_mul_pi_complex] at h
  rw [h]
  rcases neg_one_pow_eq_or ℂ j with h1 | h1 <;> rw [h1] <;> ring

/-- DLMF 11.10.22 for even order `2m`. -/
theorem weberE_nat_even (m : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    weberE ((2*m:ℕ):ℂ) z = -struveH ((2*m:ℕ):ℂ) z+1/π*∑ k ∈ Finset.range m,
      Gamma (k+1/2)/Gamma (((2*m:ℕ):ℂ)+1/2-k)*(z/2)^(((2*m:ℕ):ℤ)-2*k-1) := by
  have hz2 : z/2 ≠ 0 := div_ne_zero (slitPlane_ne_zero hz) two_ne_zero
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [weberE_series]
  have hs : sin (π*((2*m:ℕ):ℂ)/2) = 0 := by
    rw [show π*((2*m:ℕ):ℂ)/2 = (m:ℂ)*π by push_cast; ring, Complex.sin_nat_mul_pi]
  have hc : cos (π*((2*m:ℕ):ℂ)/2) = (-1)^m := by
    rw [show π*((2*m:ℕ):ℂ)/2 = (m:ℂ)*π by push_cast; ring, cos_nat_mul_pi_complex]
  rw [hs, hc, zero_mul, zero_sub]
  set f : ℕ → ℂ := fun k => (-1)^k*(z/2)^(2*k+1)/(Gamma (k+((2*m:ℕ):ℂ)/2+3/2)*
    Gamma (k-((2*m:ℕ):ℂ)/2+3/2))
  have h := hasSum_angerS2 ((2*m:ℕ):ℂ) z
  rw [← hasSum_nat_add_iff' m] at h
  have hH : HasSum (fun k => f (k+m)) ((-1)^m*struveH ((2*m:ℕ):ℂ) z) := by
    rw [struveH, show ((2*m:ℕ):ℂ)+1 = ((2*m+1:ℕ):ℂ) by push_cast; ring, cpow_natCast,
      ← mul_assoc]
    refine ((hasSum_struveHCore _ z).mul_left ((-1)^m*(z/2)^(2*m+1))).congr_fun fun k => ?_
    simp only [f, struveCoeff]
    rw [show ((k+m:ℕ):ℂ)+((2*m:ℕ):ℂ)/2+3/2 = (k:ℂ)+((2*m:ℕ):ℂ)+3/2 by push_cast; ring,
      show ((k+m:ℕ):ℂ)-((2*m:ℕ):ℂ)/2+3/2 = (k:ℂ)+3/2 by push_cast; ring]
    rw [show 2*(k+m)+1 = (2*m+1)+2*k by ring, pow_add, pow_add, pow_mul]
    ring
  have hu := h.unique hH
  have hsum : (-1)^m * ∑ i ∈ Finset.range m, f i = -(1/π*∑ k ∈ Finset.range m,
      Gamma (k+1/2)/Gamma (((2*m:ℕ):ℂ)+1/2-k)*(z/2)^(((2*m:ℕ):ℤ)-2*k-1)) := by
    rw [← Finset.sum_range_reflect, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨k, rfl⟩ : ∃ k, m = k+j+1 := ⟨m-j-1, by simp at hj; omega⟩
    rw [show k+j+1-1-j = k by omega]
    simp only [f]
    have hG := Gamma_half_add_mul_Gamma_half_sub j
    rw [show (k:ℂ)+((2*(k+j+1):ℕ):ℂ)/2+3/2 = ((2*(k+j+1):ℕ):ℂ)+1/2-j by push_cast; ring,
      show (k:ℂ)-((2*(k+j+1):ℕ):ℂ)/2+3/2 = 1/2-j by push_cast; ring,
      show ((2*(k+j+1):ℕ):ℤ)-2*(j:ℤ)-1 = ((2*k+1:ℕ):ℤ) by push_cast; ring, zpow_natCast]
    have hG2 : Gamma (1/2-(j:ℂ)) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hG
      exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) hπ) hG.symm
    rw [show (j:ℂ)+1/2 = 1/2+j by ring]
    have hGi : (Gamma (1/2-(j:ℂ)))⁻¹ = Gamma (1/2+j) * ((-1:ℂ)^j * (π:ℂ))⁻¹ := by
      have hG1 : Gamma (1/2+(j:ℂ)) ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hG
        exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) hπ) hG.symm
      rw [← hG, mul_inv, ← mul_assoc, mul_inv_cancel₀ hG1, one_mul]
    rw [div_eq_mul_inv _ (_ * Gamma (1/2-(j:ℂ))), mul_inv, hGi]
    rw [pow_add, pow_add, pow_one]
    have e : ((-1:ℂ))^k * (-1)^k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    have e2 : ((-1:ℂ))^j ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
    rw [sq, e, one_mul]
  have e : ((-1:ℂ))^m * (-1)^m - 1 = 0 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination -(-1:ℂ)^m*hu - hsum - struveH ((2*m:ℕ):ℂ) z*e

/-- DLMF 11.10.22 for odd order `2m+1`. -/
theorem weberE_nat_odd (m : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    weberE ((2*m+1:ℕ):ℂ) z = -struveH ((2*m+1:ℕ):ℂ) z+1/π*∑ k ∈ Finset.range (m+1),
      Gamma (k+1/2)/Gamma (((2*m+1:ℕ):ℂ)+1/2-k)*(z/2)^(((2*m+1:ℕ):ℤ)-2*k-1) := by
  have hz2 : z/2 ≠ 0 := div_ne_zero (slitPlane_ne_zero hz) two_ne_zero
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [weberE_series]
  have hs : sin (π*((2*m+1:ℕ):ℂ)/2) = (-1)^m := by
    rw [show π*((2*m+1:ℕ):ℂ)/2 = (m:ℂ)*π + π/2 by push_cast; ring, Complex.sin_add_pi_div_two,
      cos_nat_mul_pi_complex]
  have hc : cos (π*((2*m+1:ℕ):ℂ)/2) = 0 := by
    rw [show π*((2*m+1:ℕ):ℂ)/2 = (m:ℂ)*π + π/2 by push_cast; ring, Complex.cos_add_pi_div_two,
      Complex.sin_nat_mul_pi, neg_zero]
  rw [hs, hc, zero_mul, sub_zero]
  set f : ℕ → ℂ := fun k => (-1)^k*(z/2)^(2*k)/(Gamma (k+((2*m+1:ℕ):ℂ)/2+1)*
    Gamma (k-((2*m+1:ℕ):ℂ)/2+1))
  have h := hasSum_angerS1 ((2*m+1:ℕ):ℂ) z
  rw [← hasSum_nat_add_iff' (m+1)] at h
  have hH : HasSum (fun k => f (k+(m+1))) (-(-1)^m*struveH ((2*m+1:ℕ):ℂ) z) := by
    rw [struveH, show ((2*m+1:ℕ):ℂ)+1 = ((2*m+2:ℕ):ℂ) by push_cast; ring, cpow_natCast,
      ← mul_assoc]
    refine ((hasSum_struveHCore _ z).mul_left (-(-1)^m*(z/2)^(2*m+2))).congr_fun fun k => ?_
    simp only [f, struveCoeff]
    rw [show ((k+(m+1):ℕ):ℂ)+((2*m+1:ℕ):ℂ)/2+1 = (k:ℂ)+((2*m+1:ℕ):ℂ)+3/2 by push_cast; ring,
      show ((k+(m+1):ℕ):ℂ)-((2*m+1:ℕ):ℂ)/2+1 = (k:ℂ)+3/2 by push_cast; ring]
    rw [show 2*(k+(m+1)) = (2*m+2)+2*k by ring, pow_add]
    ring
  have hu := h.unique hH
  have hsum : (-1)^m * ∑ i ∈ Finset.range (m+1), f i = 1/π*∑ k ∈ Finset.range (m+1),
      Gamma (k+1/2)/Gamma (((2*m+1:ℕ):ℂ)+1/2-k)*(z/2)^(((2*m+1:ℕ):ℤ)-2*k-1) := by
    rw [← Finset.sum_range_reflect, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨k, rfl⟩ : ∃ k, m = k+j := ⟨m-j, by simp at hj; omega⟩
    rw [show k+j+1-1-j = k by omega]
    simp only [f]
    have hG := Gamma_half_add_mul_Gamma_half_sub j
    rw [show (k:ℂ)+((2*(k+j)+1:ℕ):ℂ)/2+1 = ((2*(k+j)+1:ℕ):ℂ)+1/2-j by push_cast; ring,
      show (k:ℂ)-((2*(k+j)+1:ℕ):ℂ)/2+1 = 1/2-j by push_cast; ring,
      show ((2*(k+j)+1:ℕ):ℤ)-2*(j:ℤ)-1 = ((2*k:ℕ):ℤ) by push_cast; ring, zpow_natCast]
    rw [show (j:ℂ)+1/2 = 1/2+j by ring]
    have hGi : (Gamma (1/2-(j:ℂ)))⁻¹ = Gamma (1/2+j) * ((-1:ℂ)^j * (π:ℂ))⁻¹ := by
      have hG1 : Gamma (1/2+(j:ℂ)) ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hG
        exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) hπ) hG.symm
      rw [← hG, mul_inv, ← mul_assoc, mul_inv_cancel₀ hG1, one_mul]
    rw [div_eq_mul_inv _ (_ * Gamma (1/2-(j:ℂ))), mul_inv, hGi]
    rw [pow_add]
    have e : ((-1:ℂ))^k * (-1)^k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    have e2 : ((-1:ℂ))^j ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
    rw [sq, e, one_mul]
  have e : ((-1:ℂ))^m * (-1)^m - 1 = 0 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination (-1:ℂ)^m*hu + hsum - struveH ((2*m+1:ℕ):ℂ) z*e

/-- DLMF 11.10.23 for even order `-2m`. -/
theorem weberE_neg_nat_even (m : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    weberE (-((2*m:ℕ):ℂ)) z = -struveH (-((2*m:ℕ):ℂ)) z+(-1)^(2*m+1)/π*∑ k ∈ Finset.range m,
      Gamma (((2*m:ℕ):ℂ)-k-1/2)/Gamma (k+3/2)*(z/2)^(-((2*m:ℕ):ℤ)+2*k+1) := by
  have hz2 : z/2 ≠ 0 := div_ne_zero (slitPlane_ne_zero hz) two_ne_zero
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [weberE_series]
  have hs : sin (π*(-((2*m:ℕ):ℂ))/2) = 0 := by
    rw [show π*(-((2*m:ℕ):ℂ))/2 = -((m:ℂ)*π) by push_cast; ring, Complex.sin_neg,
      Complex.sin_nat_mul_pi, neg_zero]
  have hc : cos (π*(-((2*m:ℕ):ℂ))/2) = (-1)^m := by
    rw [show π*(-((2*m:ℕ):ℂ))/2 = -((m:ℂ)*π) by push_cast; ring, Complex.cos_neg, cos_nat_mul_pi_complex]
  rw [hs, hc, zero_mul, zero_sub]
  set h : ℕ → ℂ := fun j => (-1)^j*(z/2)^(2*(j:ℤ)+1-2*m)/(Gamma (j+3/2)*Gamma (j-((2*m:ℕ):ℂ)+3/2))
  have hH : HasSum h (struveH (-((2*m:ℕ):ℂ)) z) := by
    rw [struveH, show -((2*m:ℕ):ℂ)+1 = (((1-2*m:ℤ)):ℂ) by push_cast; ring, cpow_intCast]
    refine ((hasSum_struveHCore _ z).mul_left _).congr_fun fun j => ?_
    simp only [h, struveCoeff]
    rw [show (2*(j:ℤ)+1-2*m) = (1-2*m) + ((2*j:ℕ):ℤ) by push_cast; ring, zpow_add₀ hz2,
      zpow_natCast, show (j:ℂ)+-((2*m:ℕ):ℂ)+3/2 = (j:ℂ)-((2*m:ℕ):ℂ)+3/2 by ring]
    ring
  rw [← hasSum_nat_add_iff' m] at hH
  have hS := (hasSum_angerS2 (-((2*m:ℕ):ℂ)) z).mul_left ((-1:ℂ)^m)
  have hT := hH.unique (hS.congr_fun fun k => ?_)
  rotate_left
  · simp only [h]
    rw [show (2*((k+m:ℕ):ℤ)+1-2*m) = ((2*k+1:ℕ):ℤ) by push_cast; ring, zpow_natCast,
      show ((k+m:ℕ):ℂ)+3/2 = (k:ℂ)-(-((2*m:ℕ):ℂ))/2+3/2 by push_cast; ring,
      show ((k+m:ℕ):ℂ)-((2*m:ℕ):ℂ)+3/2 = (k:ℂ)+(-((2*m:ℕ):ℂ))/2+3/2 by push_cast; ring,
      pow_add]
    ring
  have hsum : ∑ j ∈ Finset.range m, h j = (-1)^(2*m+1)/π*∑ k ∈ Finset.range m,
      Gamma (((2*m:ℕ):ℂ)-k-1/2)/Gamma (k+3/2)*(z/2)^(-((2*m:ℕ):ℤ)+2*k+1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j < m := by simpa using hj
    obtain ⟨i, hi⟩ : ∃ i, 2*m = i+j+1 := ⟨2*m-j-1, by omega⟩
    simp only [h]
    have hG := Gamma_half_add_mul_Gamma_half_sub i
    have e1 : (j:ℂ)-((2*m:ℕ):ℂ)+3/2 = 1/2-i := by
      rw [hi]; push_cast; ring
    have e2 : ((2*m:ℕ):ℂ)-j-1/2 = 1/2+i := by
      rw [hi]; push_cast; ring
    rw [e1, e2, show (2*(j:ℤ)+1-2*m) = -((2*m:ℕ):ℤ)+2*j+1 by push_cast; ring]
    have hG1 : Gamma (1/2+(i:ℂ)) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hG
      exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) hπ) hG.symm
    have hGi : (Gamma (1/2-(i:ℂ)))⁻¹ = Gamma (1/2+i) * ((-1:ℂ)^i * (π:ℂ))⁻¹ := by
      rw [← hG, mul_inv, ← mul_assoc, mul_inv_cancel₀ hG1, one_mul]
    rw [div_eq_mul_inv _ (_ * Gamma (1/2-(i:ℂ))), mul_inv, hGi]
    have hp : ((-1:ℂ))^(2*m+1) = (-1)^i * (-1)^j := by
      rw [show 2*m+1 = i+j+2 by omega, pow_add, pow_add]; norm_num
    rw [hp]
    have e2 : ((-1:ℂ))^i ≠ 0 := pow_ne_zero _ (by norm_num)
    have ei : (((-1:ℂ))^i)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    field_simp
    rw [ei, mul_one]
  linear_combination hT + hsum

/-- DLMF 11.10.23 for odd order `-(2m+1)`. -/
theorem weberE_neg_nat_odd (m : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    weberE (-((2*m+1:ℕ):ℂ)) z = -struveH (-((2*m+1:ℕ):ℂ)) z+(-1)^(2*m+1+1)/π*
      ∑ k ∈ Finset.range m,
      Gamma (((2*m+1:ℕ):ℂ)-k-1/2)/Gamma (k+3/2)*(z/2)^(-((2*m+1:ℕ):ℤ)+2*k+1) := by
  have hz2 : z/2 ≠ 0 := div_ne_zero (slitPlane_ne_zero hz) two_ne_zero
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [weberE_series]
  have hs : sin (π*(-((2*m+1:ℕ):ℂ))/2) = -(-1)^m := by
    rw [show π*(-((2*m+1:ℕ):ℂ))/2 = -((m:ℂ)*π + π/2) by push_cast; ring, Complex.sin_neg,
      Complex.sin_add_pi_div_two, cos_nat_mul_pi_complex]
  have hc : cos (π*(-((2*m+1:ℕ):ℂ))/2) = 0 := by
    rw [show π*(-((2*m+1:ℕ):ℂ))/2 = -((m:ℂ)*π + π/2) by push_cast; ring, Complex.cos_neg,
      Complex.cos_add_pi_div_two, Complex.sin_nat_mul_pi, neg_zero]
  rw [hs, hc, zero_mul, sub_zero]
  set h : ℕ → ℂ := fun j => (-1)^j*(z/2)^(2*(j:ℤ)-2*m)/(Gamma (j+3/2)*
    Gamma (j-((2*m+1:ℕ):ℂ)+3/2))
  have hH : HasSum h (struveH (-((2*m+1:ℕ):ℂ)) z) := by
    rw [struveH, show -((2*m+1:ℕ):ℂ)+1 = (((-2*m:ℤ)):ℂ) by push_cast; ring, cpow_intCast]
    refine ((hasSum_struveHCore _ z).mul_left _).congr_fun fun j => ?_
    simp only [h, struveCoeff]
    rw [show (2*(j:ℤ)-2*m) = (-2*m) + ((2*j:ℕ):ℤ) by push_cast; ring, zpow_add₀ hz2,
      zpow_natCast, show (j:ℂ)+-((2*m+1:ℕ):ℂ)+3/2 = (j:ℂ)-((2*m+1:ℕ):ℂ)+3/2 by ring]
    ring
  rw [← hasSum_nat_add_iff' m] at hH
  have hS := (hasSum_angerS1 (-((2*m+1:ℕ):ℂ)) z).mul_left ((-1:ℂ)^m)
  have hT := hH.unique (hS.congr_fun fun k => ?_)
  rotate_left
  · simp only [h]
    rw [show (2*((k+m:ℕ):ℤ)-2*m) = ((2*k:ℕ):ℤ) by push_cast; ring, zpow_natCast,
      show ((k+m:ℕ):ℂ)+3/2 = (k:ℂ)-(-((2*m+1:ℕ):ℂ))/2+1 by push_cast; ring,
      show ((k+m:ℕ):ℂ)-((2*m+1:ℕ):ℂ)+3/2 = (k:ℂ)+(-((2*m+1:ℕ):ℂ))/2+1 by push_cast; ring,
      pow_add]
    ring
  have hsum : ∑ j ∈ Finset.range m, h j = (-1)^(2*m+1+1)/π*∑ k ∈ Finset.range m,
      Gamma (((2*m+1:ℕ):ℂ)-k-1/2)/Gamma (k+3/2)*(z/2)^(-((2*m+1:ℕ):ℤ)+2*k+1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j < m := by simpa using hj
    obtain ⟨i, hi⟩ : ∃ i, 2*m+1 = i+j+1 := ⟨2*m-j, by omega⟩
    simp only [h]
    have hG := Gamma_half_add_mul_Gamma_half_sub i
    have e1 : (j:ℂ)-((2*m+1:ℕ):ℂ)+3/2 = 1/2-i := by
      rw [hi]; push_cast; ring
    have e2 : ((2*m+1:ℕ):ℂ)-j-1/2 = 1/2+i := by
      rw [hi]; push_cast; ring
    rw [e1, e2, show (2*(j:ℤ)-2*m) = -((2*m+1:ℕ):ℤ)+2*j+1 by push_cast; ring]
    have hG1 : Gamma (1/2+(i:ℂ)) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hG
      exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) hπ) hG.symm
    have hGi : (Gamma (1/2-(i:ℂ)))⁻¹ = Gamma (1/2+i) * ((-1:ℂ)^i * (π:ℂ))⁻¹ := by
      rw [← hG, mul_inv, ← mul_assoc, mul_inv_cancel₀ hG1, one_mul]
    rw [div_eq_mul_inv _ (_ * Gamma (1/2-(i:ℂ))), mul_inv, hGi]
    have hp : ((-1:ℂ))^(2*m+1+1) = (-1)^i * (-1)^j := by
      rw [show 2*m+1+1 = i+j+2 by omega, pow_add, pow_add]; norm_num
    rw [hp]
    have e2 : ((-1:ℂ))^i ≠ 0 := pow_ne_zero _ (by norm_num)
    have ei : (((-1:ℂ))^i)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    field_simp
    rw [ei, mul_one]
  linear_combination hT + hsum

/-- Formula under the stated hypotheses: `weberE n z = -struveH n z+1/π*∑ k ∈ Finset.range
(weberM1 n), Gamma (k+1/2)/Gamma (n+1/2-k)*(z/2)^((n:ℤ)-2*k-1)`. -/
@[dlmf 11.10.E22]
theorem weberE_nat (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    weberE n z = -struveH n z+1/π*∑ k ∈ Finset.range (weberM1 n), Gamma (k+1/2)/Gamma (n+1/2-k)*(z/2)^((n:ℤ)-2*k-1) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show weberM1 (2*m) = m by simp only [weberM1]; omega]
    exact weberE_nat_even m hz
  · rw [show weberM1 (2*m+1) = m+1 by simp only [weberM1]; omega]
    exact weberE_nat_odd m hz

/-- Formula under the stated hypotheses: `weberE (-n) z = -struveH (-n) z+(-1)^(n+1)/π*∑ k ∈
Finset.range (weberM2 n), Gamma (n-k-1/2)/Gamma (k+3/2)*(z/2)^(-(n:ℤ)+2*k+1)`. -/
@[dlmf 11.10.E23]
theorem weberE_neg_nat (n : ℕ) (hn : 0 < n) {z : ℂ} (hz : z ∈ slitPlane) :
    weberE (-n) z = -struveH (-n) z+(-1)^(n+1)/π*∑ k ∈ Finset.range (weberM2 n), Gamma (n-k-1/2)/Gamma (k+3/2)*(z/2)^(-(n:ℤ)+2*k+1) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show weberM2 (2*m) = m by simp only [weberM2]; omega]
    exact weberE_neg_nat_even m hz
  · rw [show weberM2 (2*m+1) = m by simp only [weberM2]; omega]
    exact weberE_neg_nat_odd m hz

/-- Special value with the removable order-zero value retained. -/
@[dlmf 11.10.E25]
theorem angerJ_zero (ν : ℂ) :
    angerJ ν 0 = if ν=0 then 1 else sin (π*ν)/(π*ν) := by
  by_cases hν : ν=0
  · subst ν
    simp [angerJ]
  · rw [if_neg hν]
    unfold angerJ
    simp only [zero_mul, sub_zero]
    rw [integral_cos_mul_complex hν]
    try simp only [Complex.ofReal_zero, mul_zero, sin_zero, zero_div, sub_zero]
    rw [mul_comm ν (π:ℂ)]
    ring

/-- Special value with the removable order-zero value retained. -/
@[dlmf 11.10.E25]
theorem weberE_zero (ν : ℂ) :
    weberE ν 0 = if ν=0 then 0 else (1-cos (π*ν))/(π*ν) := by
  by_cases hν : ν=0
  · subst ν
    simp [weberE]
  · rw [if_neg hν]
    have hd (t : ℝ) : HasDerivAt (fun t : ℝ => -cos (ν*t)/ν) (sin (ν*t)) t := by
      have hh := (((Complex.hasDerivAt_cos (ν*t)).comp (t:ℂ)
        ((hasDerivAt_id (t:ℂ)).const_mul ν)).neg.div_const ν).comp_ofReal
      convert hh using 1
      · funext x; simp only [Function.comp_apply, Pi.neg_apply]
      · field_simp
    have hi:=intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((by fun_prop : Continuous (fun t : ℝ => sin (ν*t))).intervalIntegrable 0 π)
    unfold weberE
    simp only [zero_mul,sub_zero]
    rw [hi]
    simp only [Complex.ofReal_zero, mul_zero, cos_zero]
    rw [mul_comm ν (π:ℂ)]
    ring

/-- Identity under the stated parameter and domain assumptions: `weberE 0 z = -struveH 0 z`. -/
@[dlmf 11.10.E26]
theorem weberE_zero_order (z : ℂ) :
    weberE 0 z = -struveH 0 z := by
  rw [weberE_series]
  simp only [mul_zero, zero_div, sin_zero, cos_zero, zero_mul, one_mul, zero_sub, neg_inj]
  refine (hasSum_angerS2 0 z).unique ?_
  rw [struveH, zero_add, cpow_one]
  refine ((hasSum_struveHCore 0 z).mul_left (z/2)).congr_fun fun k => ?_
  simp only [struveCoeff, zero_div, add_zero, sub_zero]
  ring

/-- `Γ(3/2) Γ(1/2) = π/2`. -/
theorem Gamma_three_halves_mul_Gamma_one_half :
    Gamma (3/2) * Gamma (1/2) = π/2 := by
  rw [show (3/2:ℂ) = 1/2+1 by norm_num, Complex.Gamma_add_one _ (by norm_num),
    Complex.Gamma_one_half_eq]
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [mul_assoc, ← cpow_add _ _ hπ]
  norm_num
  ring

/-- Identity under the stated parameter and domain assumptions: `weberE 1 z = 2/π-struveH 1 z`. -/
@[dlmf 11.10.E26]
theorem weberE_one_order (z : ℂ) :
    weberE 1 z = 2/π-struveH 1 z := by
  rw [weberE_series]
  have hs : sin (π*(1:ℂ)/2) = 1 := by
    rw [show π*(1:ℂ)/2 = ((π/2:ℝ):ℂ) by push_cast; ring, ← ofReal_sin, Real.sin_pi_div_two]; simp
  have hc : cos (π*(1:ℂ)/2) = 0 := by
    rw [show π*(1:ℂ)/2 = ((π/2:ℝ):ℂ) by push_cast; ring, ← ofReal_cos, Real.cos_pi_div_two]; simp
  rw [hs, hc, one_mul, zero_mul, sub_zero]
  have h := hasSum_angerS1 1 z
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_add, mul_zero,
    pow_zero, one_mul] at h
  have h0 : (1:ℂ) / (Gamma (1/2+1) * Gamma (0-1/2+1)) = 2/π := by
    rw [show (1/2:ℂ)+1 = 3/2 by norm_num, show (0:ℂ)-1/2+1 = 1/2 by norm_num,
      Gamma_three_halves_mul_Gamma_one_half]
    field_simp
  rw [show (1:ℂ)/2 = 1/2 from rfl] at h
  have hH : HasSum (fun k : ℕ => (-1)^(k+1)*(z/2)^(2*(k+1))/(Gamma (((k+1:ℕ):ℂ)+1/2+1)*
      Gamma (((k+1:ℕ):ℂ)-1/2+1))) (-struveH 1 z) := by
    rw [struveH, show (1:ℂ)+1 = ((2:ℕ):ℂ) by norm_num, cpow_natCast, ← neg_mul]
    refine ((hasSum_struveHCore 1 z).mul_left (-(z/2)^2)).congr_fun fun k => ?_
    simp only [struveCoeff]
    rw [show ((k+1:ℕ):ℂ)+1/2+1 = (k:ℂ)+1+3/2 by push_cast; ring,
      show ((k+1:ℕ):ℂ)-1/2+1 = (k:ℂ)+3/2 by push_cast; ring]
    ring
  have := h.unique hH
  rw [h0] at this
  linear_combination this

/-- At `0`, the function `(fun ν => angerJ ν z)` has derivative `(π/2*struveH 0 z)`. -/
@[dlmf 11.10.E27]
theorem angerJ_order_deriv_zero (z : ℂ) :
    HasDerivAt (fun ν => angerJ ν z) (π/2*struveH 0 z) 0 := by
  convert angerJ_hasDerivAt_order 0 z using 1
  have hE := weberE_zero_order z
  simp only [weberE, zero_mul, zero_sub, sin_neg] at hE
  rw [intervalIntegral.integral_neg] at hE
  have := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => -(sin (0*(θ:ℂ)-z*Real.sin θ)*θ)) (a := 0) (b := π) π
  simp only [sub_self, sub_zero, Real.sin_pi_sub] at this
  have hsplit : (∫ x in (0:ℝ)..π, -(sin (0*((π-x:ℝ):ℂ)-z*Real.sin x)*((π-x:ℝ):ℂ))) =
      π*(∫ x in (0:ℝ)..π, sin (z*Real.sin x)) -
        ∫ x in (0:ℝ)..π, -(sin (0*(x:ℂ)-z*Real.sin x)*x) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (intervalIntegrable_zero_pi _ (by fun_prop))
        (intervalIntegrable_zero_pi _ (by fun_prop))]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [zero_mul, zero_sub, sin_neg]
    push_cast; ring
  rw [hsplit] at this
  have hI : (∫ x in (0:ℝ)..π, -(sin (0*(x:ℂ)-z*Real.sin x)*x)) =
      π*(∫ x in (0:ℝ)..π, sin (z*Real.sin x))/2 := by linear_combination -this/2
  rw [hI]
  have hπ := pi_complex_ne_zero
  have hH : struveH 0 z = 1/π*∫ x in (0:ℝ)..π, sin (z*Real.sin x) := by
    linear_combination hE
  rw [hH]
  field_simp

/-- At `0`, the function `(fun ν => weberE ν z)` has derivative `(π/2*besselJ 0 z)`. -/
@[dlmf 11.10.E28]
theorem weberE_order_deriv_zero (z : ℂ) :
    HasDerivAt (fun ν => weberE ν z) (π/2*besselJ 0 z) 0 := by
  convert weberE_hasDerivAt_order 0 z using 1
  have hJ := besselJ_int_eq_integral_cos 0 z
  simp only [Int.cast_zero, zero_mul, sub_zero] at hJ
  have := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => cos (0*(θ:ℂ)-z*Real.sin θ)*θ) (a := 0) (b := π) π
  simp only [sub_self, sub_zero, Real.sin_pi_sub] at this
  have hsplit : (∫ x in (0:ℝ)..π, cos (0*((π-x:ℝ):ℂ)-z*Real.sin x)*((π-x:ℝ):ℂ)) =
      π*(∫ x in (0:ℝ)..π, cos (z*sin x)) - ∫ x in (0:ℝ)..π, cos (0*(x:ℂ)-z*Real.sin x)*x := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (intervalIntegrable_zero_pi _ (by fun_prop)) (intervalIntegrable_zero_pi _ (by fun_prop))]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only
    simp only [zero_mul, zero_sub, cos_neg, ofReal_sin]
    push_cast; ring
  rw [hsplit] at this
  have hI : (∫ x in (0:ℝ)..π, cos (0*(x:ℂ)-z*Real.sin x)*x) =
      π*(∫ x in (0:ℝ)..π, cos (z*sin x))/2 := by linear_combination -this/2
  rw [hJ, hI]
  have hπ := pi_complex_ne_zero
  field_simp

/-- Identity under the stated parameter and domain assumptions: `angerJ n z = besselJ n z`. -/
@[dlmf 11.10.E29]
theorem angerJ_int (n : ℤ) {z : ℂ} (hz : z ∈ slitPlane) :
    angerJ n z = besselJ n z := by
  exact angerJ_int_aux n hz

/-- Folding `[0, π]` about `π/2`: `∫₀^π f = ∫₀^{π/2} (f(π/2+ψ) + f(π/2-ψ)) dψ`. -/
theorem integral_zero_pi_fold {f : ℝ → ℂ} (hf : Continuous f) :
    ∫ θ in (0:ℝ)..π, f θ = ∫ ψ in (0:ℝ)..(π / 2), (f (π / 2 + ψ) + f (π / 2 - ψ)) := by
  have h1 : IntervalIntegrable (fun ψ => f (π / 2 + ψ)) volume 0 (π / 2) :=
    (hf.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun ψ => f (π / 2 - ψ)) volume 0 (π / 2) :=
    (hf.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2)
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _),
    intervalIntegral.integral_add h1 h2, add_comm]
  congr 1
  · rw [intervalIntegral.integral_comp_add_left (fun x => f x) (π / 2)]
    norm_num [add_halves]
  · rw [intervalIntegral.integral_comp_sub_left (fun x => f x) (π / 2)]
    norm_num

/-- The folded Anger integrand: `cos(ν(π/2±ψ) - z cos ψ)` summed over both signs. -/
theorem angerFold_cos (ν z : ℂ) (ψ : ℝ) :
    cos (ν * ((π / 2 + ψ : ℝ) : ℂ) - z * Real.sin (π / 2 + ψ)) +
      cos (ν * ((π / 2 - ψ : ℝ) : ℂ) - z * Real.sin (π / 2 - ψ)) =
    2 * (((2 * sin (ν * π / 2)) / 2 * sin (z * Real.cos ψ) +
      (2 * cos (ν * π / 2)) / 2 * cos (z * Real.cos ψ)) * cos (ν * ψ)) := by
  rw [add_comm (π / 2) ψ, Real.sin_add_pi_div_two, Real.sin_pi_div_two_sub, add_comm ψ]
  push_cast
  have e1 : ν * (π / 2 + ψ) - z * cos (ψ : ℂ) = (ν * π / 2 - z * cos (ψ : ℂ)) + ν * ψ := by ring
  have e2 : ν * (π / 2 - ψ) - z * cos (ψ : ℂ) = (ν * π / 2 - z * cos (ψ : ℂ)) - ν * ψ := by ring
  rw [e1, e2]
  simp only [cos_add, cos_sub, sin_sub]
  ring

/-- The folded Weber integrand: `sin(ν(π/2±ψ) - z cos ψ)` summed over both signs. -/
theorem angerFold_sin (ν z : ℂ) (ψ : ℝ) :
    sin (ν * ((π / 2 + ψ : ℝ) : ℂ) - z * Real.sin (π / 2 + ψ)) +
      sin (ν * ((π / 2 - ψ : ℝ) : ℂ) - z * Real.sin (π / 2 - ψ)) =
    2 * (((-2 * cos (ν * π / 2)) / 2 * sin (z * Real.cos ψ) +
      (2 * sin (ν * π / 2)) / 2 * cos (z * Real.cos ψ)) * cos (ν * ψ)) := by
  rw [add_comm (π / 2) ψ, Real.sin_add_pi_div_two, Real.sin_pi_div_two_sub, add_comm ψ]
  push_cast
  have e1 : ν * (π / 2 + ψ) - z * cos (ψ : ℂ) = (ν * π / 2 - z * cos (ψ : ℂ)) + ν * ψ := by ring
  have e2 : ν * (π / 2 - ψ) - z * cos (ψ : ℂ) = (ν * π / 2 - z * cos (ψ : ℂ)) - ν * ψ := by ring
  rw [e1, e2]
  simp only [sin_add, sin_sub, cos_sub]
  ring

/-- The series with terms `(fun k : ℕ => 2*sin (ν*π/2)*(-1)^k*besselJ (k-ν/2+1/2) (z/2)*besselJ
(k+ν/2+1/2) (z/2)+2*cos (ν*π/2)*(if k=0 then 1/2 else 1)*(-1)^k*besselJ (k-ν/2) (z/2)*besselJ
(k+ν/2) (z/2))` converges to `(angerJ ν z)`. -/
@[dlmf 11.10.E30]
theorem angerJ_bessel_products (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => 2*sin (ν*π/2)*(-1)^k*besselJ (k-ν/2+1/2) (z/2)*besselJ (k+ν/2+1/2) (z/2)+2*cos (ν*π/2)*(if k=0 then 1/2 else 1)*(-1)^k*besselJ (k-ν/2) (z/2)*besselJ (k+ν/2) (z/2)) (angerJ ν z) := by
  convert hasSum_besselJ_products_integral (2 * sin (ν * π / 2)) (2 * cos (ν * π / 2)) ν hz
    using 1
  rw [angerJ, integral_zero_pi_fold (by fun_prop)]
  simp_rw [angerFold_cos]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- The series with terms `(fun k : ℕ => -2*cos (ν*π/2)*(-1)^k*besselJ (k-ν/2+1/2) (z/2)*besselJ
(k+ν/2+1/2) (z/2)+2*sin (ν*π/2)*(if k=0 then 1/2 else 1)*(-1)^k*besselJ (k-ν/2) (z/2)*besselJ
(k+ν/2) (z/2))` converges to `(weberE ν z)`. -/
@[dlmf 11.10.E31]
theorem weberE_bessel_products (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => -2*cos (ν*π/2)*(-1)^k*besselJ (k-ν/2+1/2) (z/2)*besselJ (k+ν/2+1/2) (z/2)+2*sin (ν*π/2)*(if k=0 then 1/2 else 1)*(-1)^k*besselJ (k-ν/2) (z/2)*besselJ (k+ν/2) (z/2)) (weberE ν z) := by
  convert hasSum_besselJ_products_integral (-2 * cos (ν * π / 2)) (2 * sin (ν * π / 2)) ν hz
    using 1
  rw [weberE, integral_zero_pi_fold (by fun_prop)]
  simp_rw [angerFold_sin]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Identity under the stated parameter and domain assumptions: `angerJ (ν-1) z+angerJ (ν+1) z =
2*ν/z*angerJ ν z-2/(π*z)*(sin (π*ν))`. -/
@[dlmf 11.10.E32]
theorem angerJ_recurrence (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    angerJ (ν-1) z+angerJ (ν+1) z = 2*ν/z*angerJ ν z-2/(π*z)*(sin (π*ν)) := by
  exact angerJ_recurrence_aux ν hz

/-- At `z`, the function `(angerJ ν)` has derivative `((angerJ (ν-1) z-angerJ (ν+1) z)/2)`. -/
@[dlmf 11.10.E34]
theorem angerJ_deriv (ν z : ℂ) :
    HasDerivAt (angerJ ν) ((angerJ (ν-1) z-angerJ (ν+1) z)/2) z := by
  exact hasDerivAt_angerJ_shift ν z

/-- Identity under the stated parameter and domain assumptions: `z*deriv (angerJ ν)
z+(1:ℂ)*ν*angerJ ν z = (1:ℂ)*z*angerJ (ν-1) z+(1:ℂ)*(sin (π*ν))/π`. -/
@[dlmf 11.10.E36]
theorem angerJ_weighted_deriv_add (ν z : ℂ) :
    z*deriv (angerJ ν) z+(1:ℂ)*ν*angerJ ν z = (1:ℂ)*z*angerJ (ν-1) z+(1:ℂ)*(sin (π*ν))/π := by
  rw [(hasDerivAt_angerJ_shift ν z).deriv]
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [zero_mul, zero_add, mul_zero]
    rw [angerJ_zero ν]
    split_ifs with h
    · subst h; simp
    · field_simp
  · have := angerJ_recurrence_aux ν hz
    rw [show angerJ (ν+1) z = 2*ν/z*angerJ ν z-2/(π*z)*(sin (π*ν))-angerJ (ν-1) z by linear_combination this]
    field_simp
    ring

/-- Identity under the stated parameter and domain assumptions: `z*deriv (angerJ ν)
z+(-1:ℂ)*ν*angerJ ν z = (-1:ℂ)*z*angerJ (ν-(-1)) z+(-1:ℂ)*(sin (π*ν))/π`. -/
@[dlmf 11.10.E36]
theorem angerJ_weighted_deriv_sub (ν z : ℂ) :
    z*deriv (angerJ ν) z+(-1:ℂ)*ν*angerJ ν z = (-1:ℂ)*z*angerJ (ν-(-1)) z+(-1:ℂ)*(sin (π*ν))/π := by
  rw [(hasDerivAt_angerJ_shift ν z).deriv, sub_neg_eq_add]
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [zero_mul, zero_add, mul_zero]
    rw [angerJ_zero ν]
    split_ifs with h
    · subst h; simp
    · field_simp
  · have := angerJ_recurrence_aux ν hz
    rw [show angerJ (ν-1) z = 2*ν/z*angerJ ν z-2/(π*z)*(sin (π*ν))-angerJ (ν+1) z by linear_combination this]
    field_simp
    ring

/-- Identity under the stated parameter and domain assumptions: `weberE (ν-1) z+weberE (ν+1) z =
2*ν/z*weberE ν z-2/(π*z)*(1-cos (π*ν))`. -/
@[dlmf 11.10.E33]
theorem weberE_recurrence (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    weberE (ν-1) z+weberE (ν+1) z = 2*ν/z*weberE ν z-2/(π*z)*(1-cos (π*ν)) := by
  exact weberE_recurrence_aux ν hz

/-- At `z`, the function `(weberE ν)` has derivative `((weberE (ν-1) z-weberE (ν+1) z)/2)`. -/
@[dlmf 11.10.E35]
theorem weberE_deriv (ν z : ℂ) :
    HasDerivAt (weberE ν) ((weberE (ν-1) z-weberE (ν+1) z)/2) z := by
  exact hasDerivAt_weberE_shift ν z

/-- Identity under the stated parameter and domain assumptions: `z*deriv (weberE ν)
z+(1:ℂ)*ν*weberE ν z = (1:ℂ)*z*weberE (ν-1) z+(1:ℂ)*(1-cos (π*ν))/π`. -/
@[dlmf 11.10.E37]
theorem weberE_weighted_deriv_add (ν z : ℂ) :
    z*deriv (weberE ν) z+(1:ℂ)*ν*weberE ν z = (1:ℂ)*z*weberE (ν-1) z+(1:ℂ)*(1-cos (π*ν))/π := by
  rw [(hasDerivAt_weberE_shift ν z).deriv]
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [zero_mul, zero_add, mul_zero]
    rw [weberE_zero ν]
    split_ifs with h
    · subst h; simp
    · field_simp
  · have := weberE_recurrence_aux ν hz
    rw [show weberE (ν+1) z = 2*ν/z*weberE ν z-2/(π*z)*(1-cos (π*ν))-weberE (ν-1) z by linear_combination this]
    field_simp
    ring

/-- Identity under the stated parameter and domain assumptions: `z*deriv (weberE ν)
z+(-1:ℂ)*ν*weberE ν z = (-1:ℂ)*z*weberE (ν-(-1)) z+(-1:ℂ)*(1-cos (π*ν))/π`. -/
@[dlmf 11.10.E37]
theorem weberE_weighted_deriv_sub (ν z : ℂ) :
    z*deriv (weberE ν) z+(-1:ℂ)*ν*weberE ν z = (-1:ℂ)*z*weberE (ν-(-1)) z+(-1:ℂ)*(1-cos (π*ν))/π := by
  rw [(hasDerivAt_weberE_shift ν z).deriv, sub_neg_eq_add]
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [zero_mul, zero_add, mul_zero]
    rw [weberE_zero ν]
    split_ifs with h
    · subst h; simp
    · field_simp
  · have := weberE_recurrence_aux ν hz
    rw [show weberE (ν-1) z = 2*ν/z*weberE ν z-2/(π*z)*(1-cos (π*ν))-weberE (ν+1) z by linear_combination this]
    field_simp
    ring

end DLMF.Struve

end
