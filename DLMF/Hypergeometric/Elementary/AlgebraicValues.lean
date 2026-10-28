/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.SpecialValueTools
public import DLMF.Gamma.Digamma
public import DLMF.Gamma.SpecialValues

/-!
# Elementary and algebraic Gauss values

Elementary specializations and exact algebraic values of Gaussian hypergeometric functions.

Source references and common attribution are retained in
`DLMF.Hypergeometric.Elementary`.
-/

@[expose] public section

open Complex Filter

open scoped Real Topology Nat ComplexConjugate

noncomputable section

namespace DLMF.Hypergeometric

/-- Identity under the stated parameter and domain assumptions: `2 * z * ₂F₁ (1 / 2 : ℂ) 1 (3 / 2)
(z ^ 2) = log ((1 + z) / (1 - z))`. -/
@[dlmf 15.4.E2]
theorem log_ratio {z : ℂ} (hz : ‖z‖ < 1) :
    2 * z * ₂F₁ (1 / 2 : ℂ) 1 (3 / 2) (z ^ 2) =
      log ((1 + z) / (1 - z)) := by
  have h := arctan_eq_ordinaryHypergeometric (x := -I * z) (by simpa using hz)
  have hi : -I * z * I = z := by
    calc
      _ = -(I * I) * z := by ring
      _ = z := by simp
  have hs : -((-I * z) ^ 2) = z ^ 2 := by simp [mul_pow, I_sq]
  rw [Complex.arctan, hi, hs] at h
  have hh := congrArg (fun w : ℂ => 2 * I * w) h
  ring_nf at hh
  simp only [I_sq] at hh
  convert hh.symm using 1 <;> ring

/-- Principal powers of right-half-plane numbers are multiplicative. -/
theorem cpow_mul_cpow_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) (s : ℂ) :
    x ^ s * y ^ s = (x * y) ^ s := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have hax := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx))
  have hay := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy))
  rw [cpow_def_of_ne_zero hx0, cpow_def_of_ne_zero hy0, cpow_def_of_ne_zero (mul_ne_zero hx0 hy0),
    log_mul hx0 hy0 ⟨by linarith, by linarith⟩, ← exp_add]
  ring_nf

/-- The square root `r = √(1+z²)` on the unit disk, with `u = r + z`, `v = r - z`, `uv = 1`. -/
theorem sqrt_one_add_sq_data {z : ℂ} (hz : ‖z‖ < 1) :
    0 < (1 + z ^ 2).re ∧ 0 < ((1 + z ^ 2) ^ (1 / 2 : ℂ)).re ∧
      ((1 + z ^ 2) ^ (1 / 2 : ℂ)) ^ 2 = 1 + z ^ 2 ∧
      ((1 + z ^ 2) ^ (1 / 2 : ℂ) + z) * ((1 + z ^ 2) ^ (1 / 2 : ℂ) - z) = 1 ∧
      0 < ((1 + z ^ 2) ^ (1 / 2 : ℂ) + z).re ∧ 0 < ((1 + z ^ 2) ^ (1 / 2 : ℂ) - z).re := by
  have hw : 0 < (1 + z ^ 2).re := by
    have h1 := neg_le_of_abs_le (abs_re_le_norm (z ^ 2))
    rw [norm_pow] at h1
    have h2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
    simp only [add_re, one_re]; linarith
  have hw0 : 1 + z ^ 2 ≠ 0 := by intro h; rw [h] at hw; simp at hw
  set r := (1 + z ^ 2) ^ (1 / 2 : ℂ) with hr
  have hrre : 0 < r.re := re_cpow_half_pos hw
  have hrsq : r ^ 2 = 1 + z ^ 2 := cpow_half_sq hw0
  have huv : (r + z) * (r - z) = 1 := by linear_combination hrsq
  have hu0 : r + z ≠ 0 := by intro h; rw [h, zero_mul] at huv; exact zero_ne_one huv
  have hv : r - z = (r + z)⁻¹ := eq_inv_of_mul_eq_one_right huv
  have hsum : (r + z).re + (r - z).re = 2 * r.re := by simp; ring
  have hns : 0 < normSq (r + z) := normSq_pos.mpr hu0
  have hvre : (r - z).re = (r + z).re / normSq (r + z) := by rw [hv, inv_re]
  have hure : 0 < (r + z).re := by
    by_contra h
    push Not at h
    have : (r - z).re ≤ 0 := by rw [hvre]; exact div_nonpos_of_nonpos_of_nonneg h hns.le
    linarith
  exact ⟨hw, hrre, hrsq, huv, hure, by rw [hvre]; positivity⟩

/-- Identity under the stated parameter and domain assumptions: `z * ₂F₁ (1 / 2 : ℂ) (1 / 2) (3 /
2) (-z ^ 2) = log (z + (1 + z ^ 2) ^ (1 / 2 : ℂ))`. -/
@[dlmf 15.4.E5]
theorem log_add_sqrt {z : ℂ} (hz : ‖z‖ < 1) :
    z * ₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2) (-z ^ 2) =
      log (z + (1 + z ^ 2) ^ (1 / 2 : ℂ)) := by
  have hc32 : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  set f : ℂ → ℂ := fun w => w * ₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2) (-w ^ 2) with hf
  set g : ℂ → ℂ := fun w => log (w + (1 + w ^ 2) ^ (1 / 2 : ℂ)) with hg
  have hdisk : ∀ w : ℂ, ‖w‖ < 1 → ‖-w ^ 2‖ < 1 := fun w hw => by
    rw [norm_neg, norm_pow]; nlinarith [norm_nonneg w]
  have hfd : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt f ((1 + w ^ 2) ^ (-(1 / 2 : ℂ))) w := by
    intro w hw
    have hF := hasDerivAt_ordinaryHypergeometric (a := (1 / 2 : ℂ)) (b := 1 / 2) hc32 (hdisk w hw)
    have hsq : HasDerivAt (fun w : ℂ => -w ^ 2) (-(2 * w)) w :=
      (hasDerivAt_pow 2 w).neg.congr_deriv (by simp)
    refine ((hasDerivAt_id w).mul (hF.comp w hsq)).congr_deriv ?_
    have hid := ordinaryHypergeometric_arcsin_ident (hdisk w hw)
    rw [show (1 : ℂ) - -w ^ 2 = 1 + w ^ 2 by ring] at hid
    rw [← hid, show (1 / 2 + 1 : ℂ) = 3 / 2 by norm_num, show (3 / 2 + 1 : ℂ) = 5 / 2 by norm_num]
    simp only [id, Function.comp_apply, ordinaryHypergeometric]
    ring
  have hgd : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt g ((1 + w ^ 2) ^ (-(1 / 2 : ℂ))) w := by
    intro w hw
    obtain ⟨hre, hrre, -, -, hu, -⟩ := sqrt_one_add_sq_data hw
    have hslit : 1 + w ^ 2 ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hre)
    have hr0 : (1 + w ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by intro h; rw [h] at hrre; simp at hrre
    have hu0 : w + (1 + w ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
      intro h; rw [add_comm] at h; rw [h] at hu; simp at hu
    have hr := ((hasDerivAt_const w (1 : ℂ)).add ((hasDerivAt_id w).pow 2)).cpow_const
      (c := (1 / 2 : ℂ)) hslit
    have hu' := ((hasDerivAt_id w).add hr).clog
      (by rw [add_comm]; exact mem_slitPlane_iff.mpr (Or.inl hu))
    refine hu'.congr_deriv ?_
    simp only [id, Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl,
      pow_one, zero_add]
    rw [show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num, cpow_neg]
    field_simp
    ring
  have hdiff : DifferentiableOn ℂ (fun w => f w - g w) (Metric.ball 0 1) := fun w hw =>
    (((hfd w (by simpa using hw)).sub (hgd w (by simpa using hw))).differentiableAt).differentiableWithinAt
  have hderiv : Set.EqOn (deriv (fun w => f w - g w)) 0 (Metric.ball 0 1) := by
    intro w hw
    have hw' : ‖w‖ < 1 := by simpa using hw
    have h' : HasDerivAt (fun w => f w - g w) _ w := (hfd w hw').sub (hgd w hw')
    rw [h'.deriv, sub_self, Pi.zero_apply]
  have h0 := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
    hdiff hderiv (x := z) (y := 0) (by simpa using hz) (by simp)
  simp only [hf, hg, zero_mul, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, one_cpow, log_one, sub_zero] at h0
  exact sub_eq_zero.mp h0

/-- Duplication for rising factorials: `(2a)_{2m} = 4^m (a)_m (a + 1/2)_m`. -/
theorem poch_two_mul_two_mul (a : ℂ) (m : ℕ) :
    poch (2 * a) (2 * m) = 4 ^ m * poch a m * poch (a + 1 / 2) m := by
  induction m with
  | zero => simp [poch_zero]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, poch_succ, poch_succ, ih, poch_succ a,
      poch_succ (a + 1 / 2), pow_succ]
    push_cast
    ring

/-- Even part of a series: if `f` vanishes at odd indices, sum over even indices. -/
theorem hasSum_even_of_odd_eq_zero {f : ℕ → ℂ} {s : ℂ} (hf : HasSum f s)
    (hodd : ∀ m, f (2 * m + 1) = 0) : HasSum (fun m => f (2 * m)) s := by
  refine ((mul_right_injective₀ (two_ne_zero' ℕ)).hasSum_iff fun n hn => ?_).mpr hf
  obtain ⟨m, h | h⟩ := Nat.even_or_odd' n
  · exact absurd ⟨m, h.symm⟩ hn
  · rw [h]; exact hodd m

/-- Odd part of a series: if `f` vanishes at even indices, sum over odd indices. -/
theorem hasSum_odd_of_even_eq_zero {f : ℕ → ℂ} {s : ℂ} (hf : HasSum f s)
    (heven : ∀ m, f (2 * m) = 0) : HasSum (fun m => f (2 * m + 1)) s := by
  refine ((show Function.Injective (fun m : ℕ => 2 * m + 1) from fun a b h => by
    simp only at h; omega).hasSum_iff fun n hn => ?_).mpr hf
  obtain ⟨m, h | h⟩ := Nat.even_or_odd' n
  · rw [h]; exact heven m
  · exact absurd ⟨m, h.symm⟩ hn

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a (a + 1 / 2) (1 / 2) (z ^ 2)
= ((1 + z) ^ (-2 * a) + (1 - z) ^ (-2 * a)) / 2`. -/
@[dlmf 15.4.E7]
theorem even_binomial (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    ₂F₁ a (a + 1 / 2) (1 / 2) (z ^ 2) =
      ((1 + z) ^ (-2 * a) + (1 - z) ^ (-2 * a)) / 2 := by
  have hz' : ‖-z‖ < 1 := by rwa [norm_neg]
  have hf := hasSum_poch_div_factorial (β := 2 * a) hz
  have hg := hasSum_poch_div_factorial (β := 2 * a) hz'
  have hh := ((hf.add hg).div_const 2)
  have heven := hasSum_even_of_odd_eq_zero hh fun m => by
    rw [Odd.neg_pow ⟨m, rfl⟩]; ring
  have hz2 : ‖z ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg z) hz (by norm_num)
  have hF := (hasFPowerSeriesOnBall_ordinaryHypergeometric a (a + 1 / 2) (1 / 2)).hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one hz2)
  have hfac : ∀ m : ℕ, ((2 * m) ! : ℂ) = 4 ^ m * poch (1 / 2) m * m ! := by
    intro m
    have := poch_two_mul_two_mul (1 / 2 : ℂ) m
    rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num,
      poch_nat_one, poch_nat_one] at this
    exact_mod_cast this
  refine hF.unique (heven.congr_fun fun m => ?_) |>.trans ?_
  · have h1 : ((2 * m) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : poch (1 / 2 : ℂ) m ≠ 0 := by
      intro h; apply h1; rw [hfac, h]; simp
    have h3 : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    unfold gaussHGCoeff
    rw [Even.neg_pow ⟨m, by ring⟩, poch_two_mul_two_mul, hfac, pow_mul]
    field_simp
    ring
  · rw [sub_neg_eq_add, neg_mul]
    ring

/-- `|tan x| < 1` for `|x| < π/4`. -/
theorem abs_tan_lt_one {x : ℝ} (hx : |x| < π / 4) : |Real.tan x| < 1 := by
  have hpi := Real.pi_pos
  rw [abs_lt] at hx ⊢
  constructor
  · have := Real.tan_lt_tan_of_lt_of_lt_pi_div_two (x := -(π / 4)) (y := x) (by linarith)
      (by linarith) hx.1
    rwa [Real.tan_neg, Real.tan_pi_div_four] at this
  · have := Real.tan_lt_tan_of_lt_of_lt_pi_div_two (x := x) (y := π / 4) (by linarith)
      (by linarith) hx.2
    rwa [Real.tan_pi_div_four] at this

/-- For `|x| < π/2`, `(1 ± i tan x)^w = cos^{-w} x · e^{± i w x}`. -/
theorem one_add_I_tan_cpow {x : ℝ} (hx : |x| < π / 2) (s : ℝ) (hs : s = 1 ∨ s = -1) (w : ℂ) :
    (1 + s * I * Real.tan x) ^ w = (Real.cos x : ℂ) ^ (-w) * exp (s * I * x * w) := by
  have hpi := Real.pi_pos
  have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hx).1],
    (abs_lt.mp hx).2⟩
  have hc' : (Real.cos x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  have hcC : Complex.cos (x : ℂ) ≠ 0 := by rw [← ofReal_cos]; exact hc'
  have hlog : log (Real.cos x : ℂ) = Real.log (Real.cos x) := (ofReal_log hc.le).symm
  have key : (1 : ℂ) + s * I * Real.tan x = exp (s * I * x - Real.log (Real.cos x)) := by
    rw [exp_sub, ← hlog, exp_log hc', Real.tan_eq_sin_div_cos]
    rcases hs with rfl | rfl
    · rw [show ((1 : ℝ) : ℂ) * I * x = x * I by push_cast; ring, exp_mul_I]
      push_cast; field_simp
    · rw [show ((-1 : ℝ) : ℂ) * I * x = (-x : ℂ) * I by push_cast; ring, exp_mul_I, cos_neg,
        sin_neg]
      push_cast; field_simp
  have him : (s * I * x - Real.log (Real.cos x) : ℂ).im = s * x := by simp
  rw [key, cpow_def_of_ne_zero (exp_ne_zero _), log_exp, cpow_def_of_ne_zero hc', hlog,
    ← exp_add]
  · congr 1; ring
  · rw [him]; rcases hs with rfl | rfl <;> simp <;> linarith [(abs_lt.mp hx).1, (abs_lt.mp hx).2]
  · rw [him]; rcases hs with rfl | rfl <;> simp <;> linarith [(abs_lt.mp hx).1, (abs_lt.mp hx).2]

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a (a + 1 / 2) (1 / 2)
(-((Real.tan x : ℂ) ^ 2)) = (Real.cos x : ℂ) ^ (2 * a) * cos (2 * a * x)`. -/
@[dlmf 15.4.E8]
theorem tan_cos (a : ℂ) {x : ℝ} (hx : |x| < Real.pi / 4) :
    ₂F₁ a (a + 1 / 2) (1 / 2) (-((Real.tan x : ℂ) ^ 2)) =
      (Real.cos x : ℂ) ^ (2 * a) * cos (2 * a * x) := by
  have hx2 : |x| < π / 2 := by linarith [Real.pi_pos]
  have hz : ‖I * Real.tan x‖ < 1 := by
    rw [norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs]; exact abs_tan_lt_one hx
  have h := even_binomial a hz
  rw [mul_pow, I_sq, neg_one_mul] at h
  rw [h, show (1 : ℂ) + I * Real.tan x = 1 + ((1 : ℝ) : ℂ) * I * Real.tan x by push_cast; ring,
    show (1 : ℂ) - I * Real.tan x = 1 + ((-1 : ℝ) : ℂ) * I * Real.tan x by push_cast; ring,
    one_add_I_tan_cpow hx2 1 (Or.inl rfl), one_add_I_tan_cpow hx2 (-1) (Or.inr rfl),
    Complex.cos]
  push_cast
  ring_nf

/-- Identity under the stated parameter and domain assumptions: `(2 - 4 * a) * z * ₂F₁ a (a + 1 /
2) (3 / 2) (z ^ 2) = (1 + z) ^ (1 - 2 * a) - (1 - z) ^ (1 - 2 * a)`. -/
@[dlmf 15.4.E9]
theorem odd_binomial (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (2 - 4 * a) * z * ₂F₁ a (a + 1 / 2) (3 / 2) (z ^ 2) =
      (1 + z) ^ (1 - 2 * a) - (1 - z) ^ (1 - 2 * a) := by
  have hz' : ‖-z‖ < 1 := by rwa [norm_neg]
  have hf := hasSum_poch_div_factorial (β := 2 * a - 1) hz
  have hg := hasSum_poch_div_factorial (β := 2 * a - 1) hz'
  have hh := hg.sub hf
  have hodd := hasSum_odd_of_even_eq_zero hh fun m => by
    rw [Even.neg_pow ⟨m, by ring⟩]; ring
  have hz2 : ‖z ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg z) hz (by norm_num)
  have hF := ((hasFPowerSeriesOnBall_ordinaryHypergeometric a (a + 1 / 2) (3 / 2)).hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one hz2)).mul_left ((2 - 4 * a) * z)
  have hfac : ∀ m : ℕ, ((2 * m + 1) ! : ℂ) = 4 ^ m * poch (3 / 2) m * m ! := by
    intro m
    have := poch_two_mul_two_mul (1 : ℂ) m
    rw [mul_one, poch_nat_two, show (1 : ℂ) + 1 / 2 = 3 / 2 by norm_num, poch_nat_one] at this
    linear_combination this
  refine hF.unique (hodd.congr_fun fun m => ?_) |>.trans ?_
  · have h1 : ((2 * m + 1) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : poch (3 / 2 : ℂ) m ≠ 0 := by
      intro h; apply h1; rw [hfac, h]; simp
    have h3 : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    unfold gaussHGCoeff
    rw [Odd.neg_pow ⟨m, rfl⟩, show 2 * m + 1 = 1 + 2 * m by ring, poch_add, poch_one,
      show 2 * a - 1 + (1 : ℕ) = 2 * a by push_cast; ring, poch_two_mul_two_mul,
      show 1 + 2 * m = 2 * m + 1 by ring, hfac, pow_succ z (2 * m), pow_mul z 2 m]
    field_simp
    ring
  · rw [sub_neg_eq_add, show -(2 * a - 1) = 1 - 2 * a by ring]

/-- Identity under the stated parameter and domain assumptions: `(1 - 2 * a) * (Real.sin x : ℂ) *
₂F₁ a (a + 1 / 2) (3 / 2) (-((Real.tan x : ℂ) ^ 2)) = (Real.cos x : ℂ) ^ (2 * a) * sin ((1 - 2
* a) * x)`. -/
@[dlmf 15.4.E10]
theorem tan_sin (a : ℂ) {x : ℝ} (hx : |x| < Real.pi / 4) :
    (1 - 2 * a) * (Real.sin x : ℂ) * ₂F₁ a (a + 1 / 2) (3 / 2) (-((Real.tan x : ℂ) ^ 2)) =
      (Real.cos x : ℂ) ^ (2 * a) * sin ((1 - 2 * a) * x) := by
  have hpi := Real.pi_pos
  have hx2 : |x| < π / 2 := by linarith
  have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hx2).1],
    (abs_lt.mp hx2).2⟩
  have hc' : (Real.cos x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  have hz : ‖I * Real.tan x‖ < 1 := by
    rw [norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs]; exact abs_tan_lt_one hx
  have h := odd_binomial a hz
  rw [mul_pow, I_sq, neg_one_mul,
    show (1 : ℂ) + I * Real.tan x = 1 + ((1 : ℝ) : ℂ) * I * Real.tan x by push_cast; ring,
    show (1 : ℂ) - I * Real.tan x = 1 + ((-1 : ℝ) : ℂ) * I * Real.tan x by push_cast; ring,
    one_add_I_tan_cpow hx2 1 (Or.inl rfl), one_add_I_tan_cpow hx2 (-1) (Or.inr rfl)] at h
  have hpow : (Real.cos x : ℂ) ^ (2 * a) = (Real.cos x : ℂ) ^ (-(1 - 2 * a)) * Real.cos x := by
    have := cpow_add (x := (Real.cos x : ℂ)) (-(1 - 2 * a)) 1 hc'
    rwa [cpow_one, show -(1 - 2 * a) + 1 = 2 * a by ring] at this
  have ht : (Real.sin x : ℂ) = Real.tan x * Real.cos x := by
    have hcC : Complex.cos (x : ℂ) ≠ 0 := by rw [← ofReal_cos]; exact hc'
    rw [Real.tan_eq_sin_div_cos]; push_cast; field_simp
  rw [show ((1 : ℝ) : ℂ) * I * x * (1 - 2 * a) = (1 - 2 * a) * x * I by push_cast; ring,
    show ((-1 : ℝ) : ℂ) * I * x * (1 - 2 * a) = -((1 - 2 * a) * x) * I by push_cast; ring] at h
  rw [hpow, ht, Complex.sin]
  linear_combination ((Real.cos x : ℂ) * (-I) / 2) * h +
    ((1 - 2 * a) * Real.tan x * Real.cos x * ₂F₁ a (a + 1 / 2) (3 / 2) (-(Real.tan x : ℂ) ^ 2)) *
      I_sq

/-- Identity under the stated parameter and domain assumptions: `₂F₁ (-a) a (1 / 2) (-z ^ 2) =
(((1 + z ^ 2) ^ (1 / 2 : ℂ) + z) ^ (2 * a) + ((1 + z ^ 2) ^ (1 / 2 : ℂ) - z) ^ (2 * a)) / 2`. -/
@[dlmf 15.4.E11]
theorem opposite_parameters_sqrt (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    ₂F₁ (-a) a (1 / 2) (-z ^ 2) =
      (((1 + z ^ 2) ^ (1 / 2 : ℂ) + z) ^ (2 * a) + ((1 + z ^ 2) ^ (1 / 2 : ℂ) - z) ^ (2 * a)) / 2 := by
  set r : ℂ → ℂ := fun z => (1 + z ^ 2) ^ (1 / 2 : ℂ) with hrdef
  have hc12 : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hdisk : ∀ w : ℂ, ‖w‖ < 1 → ‖-w ^ 2‖ < 1 := fun w hw => by
    rw [norm_neg, norm_pow]; nlinarith [norm_nonneg w]
  -- Near the origin: Pfaff's transformation and the even binomial evaluation.
  have hball : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 2), ₂F₁ (-a) a (1 / 2) (-w ^ 2) =
      ((r w + w) ^ (2 * a) + (r w - w) ^ (2 * a)) / 2 := by
    intro w hw
    have hw' : ‖w‖ < 1 / 2 := by simpa using hw
    have hw1 : ‖w‖ < 1 := by linarith
    obtain ⟨hre, hrre, hrsq, -, -, -⟩ := sqrt_one_add_sq_data hw1
    show _ = (((1 + w ^ 2) ^ (1 / 2 : ℂ) + w) ^ (2 * a) +
      ((1 + w ^ 2) ^ (1 / 2 : ℂ) - w) ^ (2 * a)) / 2
    set R := (1 + w ^ 2) ^ (1 / 2 : ℂ) with hR
    have hr0 : R ≠ 0 := by intro h; rw [h] at hrre; simp at hrre
    set t := w / R with htdef
    have h1w2 : 1 + w ^ 2 ≠ 0 := by intro h; rw [h] at hre; simp at hre
    have ht2 : t ^ 2 = w ^ 2 / (1 + w ^ 2) := by rw [htdef, div_pow, hrsq]
    have hn1 : 3 / 4 ≤ ‖1 + w ^ 2‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-(w ^ 2))
      rw [norm_one, norm_neg, norm_pow, sub_neg_eq_add] at this
      nlinarith [norm_nonneg w]
    have ht2n : ‖t ^ 2‖ < 1 := by
      rw [ht2, norm_div, norm_pow, div_lt_one (by linarith)]
      nlinarith [norm_nonneg w]
    have htn : ‖t‖ < 1 := by
      rw [norm_pow] at ht2n
      nlinarith [norm_nonneg t]
    have hpf : -w ^ 2 / (-w ^ 2 - 1) = t ^ 2 := by
      rw [ht2]
      have : -w ^ 2 - 1 = -(1 + w ^ 2) := by ring
      rw [this]; field_simp
    have h1p : 0 < (1 + t).re := by
      have := neg_le_of_abs_le (abs_re_le_norm t); simp; linarith
    have h1m : 0 < (1 - t).re := by
      have := re_le_norm t; simp; linarith
    rw [pfaff_transformation_of_ne_neg_nat hc12 (hdisk w hw1) (by rw [hpf]; exact ht2n), hpf,
      show (1 / 2 : ℂ) - a = -a + 1 / 2 by ring, even_binomial (-a) htn,
      show -(-a) = a by ring, show -2 * -a = 2 * a by ring,
      show (1 : ℂ) - -w ^ 2 = R ^ 2 by rw [hrsq]; ring, sq_cpow hrre]
    have e1 : R ^ (2 * a) * (1 + t) ^ (2 * a) = (R + w) ^ (2 * a) := by
      rw [cpow_mul_cpow_of_re_pos hrre h1p, htdef]; congr 1; field_simp
    have e2 : R ^ (2 * a) * (1 - t) ^ (2 * a) = (R - w) ^ (2 * a) := by
      rw [cpow_mul_cpow_of_re_pos hrre h1m, htdef]; congr 1; field_simp
    rw [← e1, ← e2]
    ring
  -- Continuation over the unit disk.
  have hLan : AnalyticOnNhd ℂ (fun w : ℂ => ₂F₁ (-a) a (1 / 2) (-w ^ 2)) (Metric.ball 0 1) :=
    fun w hw => (analyticAt_ordinaryHypergeometric (hdisk w (by simpa using hw))).comp
      (f := fun w : ℂ => -w ^ 2) (analyticAt_id.pow 2).neg
  have hRan : AnalyticOnNhd ℂ (fun w : ℂ => ((r w + w) ^ (2 * a) + (r w - w) ^ (2 * a)) / 2)
      (Metric.ball 0 1) := by
    intro w hw
    obtain ⟨hre, -, -, -, hu, hv⟩ := sqrt_one_add_sq_data (by simpa using hw : ‖w‖ < 1)
    have hra : AnalyticAt ℂ r w :=
      (analyticAt_const.add (analyticAt_id.pow 2)).cpow analyticAt_const
        (mem_slitPlane_iff.mpr (Or.inl hre))
    exact (((hra.add analyticAt_id).cpow analyticAt_const (mem_slitPlane_iff.mpr (Or.inl hu))).add
      ((hra.sub analyticAt_id).cpow analyticAt_const (mem_slitPlane_iff.mpr (Or.inl hv)))).div
      analyticAt_const two_ne_zero
  have hev : (fun w : ℂ => ₂F₁ (-a) a (1 / 2) (-w ^ 2)) =ᶠ[𝓝 0]
      fun w => ((r w + w) ^ (2 * a) + (r w - w) ^ (2 * a)) / 2 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with w hw
    exact hball w hw
  exact hLan.eqOn_of_preconnected_of_eventuallyEq hRan (convex_ball 0 1).isPreconnected
    (by simp) hev (by simpa using hz)

/-- Restriction of a complex-analytic function to the real line is real-analytic. -/
theorem analyticAt_comp_ofReal {f : ℂ → ℂ} {x0 : ℝ} (hf : AnalyticAt ℂ f x0) :
    AnalyticAt ℝ (fun x : ℝ => f x) x0 :=
  (hf.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt x0)

/-- `x ↦ ₂F₁(a,b;c;sin² x)` is real-analytic on `(-π/2, π/2)`. -/
theorem analyticAt_ordinaryHypergeometric_sin_sq (a b c : ℂ) {x0 : ℝ} (hx : |x0| < π / 2) :
    AnalyticAt ℝ (fun x : ℝ => ₂F₁ a b c ((Real.sin x : ℂ) ^ 2)) x0 := by
  have h : ‖((Real.sin x0 : ℂ)) ^ 2‖ < 1 := by
    rw [norm_pow, norm_real, Real.norm_eq_abs, sq_abs, ← Real.cos_sq_add_sin_sq x0]
    have : 0 < Real.cos x0 := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hx).1],
      (abs_lt.mp hx).2⟩
    nlinarith
  have hF : AnalyticAt ℂ (₂F₁ a b c) (sin (x0 : ℂ) ^ 2) :=
    (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).analyticAt_of_mem
      (by rw [← ofReal_sin]; simpa using mem_eball_one_of_norm_lt_one h)
  have hG : AnalyticAt ℂ (fun w : ℂ => ₂F₁ a b c (sin w ^ 2)) x0 :=
    hF.comp (f := fun w : ℂ => sin w ^ 2) (by fun_prop)
  simpa [ofReal_sin] using analyticAt_comp_ofReal hG

/-- Positive real bases: `r^w = exp (log r * w)`. -/
theorem ofReal_cpow_eq_exp {r : ℝ} (hr : 0 < r) (w : ℂ) :
    (r : ℂ) ^ w = exp ((Real.log r : ℂ) * w) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), ofReal_log hr.le]

/-- Extension from `|x| < π/4` to `|x| < π/2` of an identity between real-analytic
functions. -/
theorem eq_of_analytic_of_abs_lt_pi_div_four {f g : ℝ → ℂ}
    (hf : ∀ x, |x| < π / 2 → AnalyticAt ℝ f x) (hg : ∀ x, |x| < π / 2 → AnalyticAt ℝ g x)
    (h : ∀ x, |x| < π / 4 → f x = g x) {x : ℝ} (hx : |x| < π / 2) : f x = g x := by
  have hpi := Real.pi_pos
  have hU : ∀ y ∈ Set.Ioo (-(π / 2)) (π / 2), |y| < π / 2 := fun y hy => abs_lt.mpr hy
  have hfg : AnalyticOnNhd ℝ (f - g) (Set.Ioo (-(π / 2)) (π / 2)) := fun y hy =>
    (hf y (hU y hy)).sub (hg y (hU y hy))
  have h0 : (f - g) =ᶠ[𝓝 0] 0 := by
    filter_upwards [Ioo_mem_nhds (show -(π / 4) < 0 by linarith) (show (0 : ℝ) < π / 4 by
      linarith)] with y hy
    simp [h y (abs_lt.mpr hy)]
  have := hfg.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioo
    ⟨by linarith, by linarith⟩ h0 (abs_lt.mp hx)
  simpa [sub_eq_zero] using this

/-- Pfaff's transformation at `z = -tan² x`: for `|x| < π/4`,
`₂F₁(a,b;c;-tan² x) = cos^{2a} x · ₂F₁(a,c-b;c;sin² x)`. -/
theorem ordinaryHypergeometric_neg_tan_sq (a b : ℂ) {c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) {x : ℝ}
    (hx : |x| < π / 4) :
    ₂F₁ a b c (-((Real.tan x : ℂ) ^ 2)) =
      (Real.cos x : ℂ) ^ (2 * a) * ₂F₁ a (c - b) c ((Real.sin x : ℂ) ^ 2) := by
  have hpi := Real.pi_pos
  have hx2 : |x| < π / 2 := by linarith
  have hcx : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hx2).1],
    (abs_lt.mp hx2).2⟩
  have ht := abs_tan_lt_one hx
  have hz : ‖-((Real.tan x : ℂ) ^ 2)‖ < 1 := by
    rw [norm_neg, norm_pow, norm_real, Real.norm_eq_abs, sq_abs]
    exact (sq_lt_one_iff_abs_lt_one _).mpr ht
  have hsin : -((Real.tan x : ℂ) ^ 2) / (-((Real.tan x : ℂ) ^ 2) - 1) =
      (Real.sin x : ℂ) ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    have hc' : (Real.cos x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hcx.ne'
    have hsum : (Real.sin x : ℂ) ^ 2 + (Real.cos x : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq x
    have hd : -((Real.sin x : ℂ) / Real.cos x) ^ 2 - 1 ≠ 0 := by
      rw [div_pow]; field_simp
      rw [show -(Real.sin x : ℂ) ^ 2 - (Real.cos x : ℂ) ^ 2 = -1 by linear_combination -hsum]
      exact div_ne_zero (by norm_num) (pow_ne_zero 2 hc')
    rw [ofReal_div, div_eq_iff hd]
    field_simp
    linear_combination (Real.sin x : ℂ) ^ 2 * hsum
  have hzt : ‖-((Real.tan x : ℂ) ^ 2) / (-((Real.tan x : ℂ) ^ 2) - 1)‖ < 1 := by
    rw [hsin, norm_pow, norm_real, Real.norm_eq_abs, sq_abs, ← Real.cos_sq_add_sin_sq x]
    nlinarith
  have hP := pfaff_transformation_of_ne_neg_nat (a := a) (b := b) hc hz hzt
  rw [hsin] at hP
  have h1t : (1 : ℂ) - -((Real.tan x : ℂ) ^ 2) = ((1 + Real.tan x ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  have hpos : 0 < 1 + Real.tan x ^ 2 := by positivity
  have hcos : (Real.cos x : ℂ) ^ (2 * a) = ((1 + Real.tan x ^ 2 : ℝ) : ℂ) ^ (-a) := by
    rw [ofReal_cpow_eq_exp hcx, ofReal_cpow_eq_exp hpos, ← inv_inv (1 + Real.tan x ^ 2),
      Real.inv_one_add_tan_sq hcx.ne', Real.log_inv, Real.log_pow]
    push_cast; ring_nf
  rw [hP, h1t, hcos]

/-- Identity under the stated parameter and domain assumptions: `₂F₁ (-a) a (1 / 2) ((Real.sin x :
ℂ) ^ 2) = cos (2 * a * x)`. -/
@[dlmf 15.4.E12]
theorem sin_sq_cos (a : ℂ) {x : ℝ} (hx : |x| < Real.pi / 2) :
    ₂F₁ (-a) a (1 / 2) ((Real.sin x : ℂ) ^ 2) =
      cos (2 * a * x) := by
  refine eq_of_analytic_of_abs_lt_pi_div_four (f := fun x : ℝ => ₂F₁ (-a) a (1 / 2)
    ((Real.sin x : ℂ) ^ 2)) (g := fun x : ℝ => cos (2 * a * x))
    (fun x hx => analyticAt_ordinaryHypergeometric_sin_sq _ _ _ hx)
    (fun x _ => analyticAt_comp_ofReal (f := fun w => cos (2 * a * w)) (by fun_prop))
    (fun x hx => ?_) hx
  have hc : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hcx : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hx).1,
    Real.pi_pos], by linarith [(abs_lt.mp hx).2, Real.pi_pos]⟩
  have hP := ordinaryHypergeometric_neg_tan_sq a (a + 1 / 2) hc hx
  rw [tan_cos a hx, show (1 / 2 : ℂ) - (a + 1 / 2) = -a by ring,
    ordinaryHypergeometric_symm] at hP
  exact (mul_left_cancel₀ (by rw [ofReal_cpow_eq_exp hcx]; exact exp_ne_zero _) hP).symm

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a (1 - a) (1 / 2) (-z ^ 2) =
(((1 + z ^ 2) ^ (1 / 2 : ℂ) + z) ^ (2 * a - 1) + ((1 + z ^ 2) ^ (1 / 2 : ℂ) - z) ^ (2 * a -
1)) / (2 * (1 + z ^ 2) ^ (1 / 2 : ℂ))`. -/
@[dlmf 15.4.E13]
theorem complementary_parameters_sqrt (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    ₂F₁ a (1 - a) (1 / 2) (-z ^ 2) =
      (((1 + z ^ 2) ^ (1 / 2 : ℂ) + z) ^ (2 * a - 1) + ((1 + z ^ 2) ^ (1 / 2 : ℂ) - z) ^ (2 * a - 1)) / (2 *
        (1 + z ^ 2) ^ (1 / 2 : ℂ)) := by
  have hc12 : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hx : ‖-z ^ 2‖ < 1 := by rw [norm_neg, norm_pow]; nlinarith [norm_nonneg z]
  obtain ⟨hre, hrre, -, -, -, -⟩ := sqrt_one_add_sq_data hz
  have hr0 : (1 + z ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by intro h; rw [h] at hrre; simp at hrre
  have h := opposite_parameters_sqrt (a - 1 / 2) hz
  rw [show -(a - 1 / 2) = 1 / 2 - a by ring, show 2 * (a - 1 / 2) = 2 * a - 1 by ring] at h
  rw [euler_transformation_of_ne_neg_nat hc12 hx, show (1 / 2 : ℂ) - a - (1 - a) = -(1 / 2) by ring,
    show (1 / 2 : ℂ) - (1 - a) = a - 1 / 2 by ring, h, show (1 : ℂ) - -z ^ 2 = 1 + z ^ 2 by ring,
    cpow_neg]
  field_simp

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a (1 - a) (1 / 2) ((Real.sin
x : ℂ) ^ 2) = cos ((2 * a - 1) * x) / (Real.cos x : ℂ)`. -/
@[dlmf 15.4.E14]
theorem sin_sq_cos_quotient (a : ℂ) {x : ℝ} (hx : |x| < Real.pi / 2) :
    ₂F₁ a (1 - a) (1 / 2) ((Real.sin x : ℂ) ^ 2) =
      cos ((2 * a - 1) * x) / (Real.cos x : ℂ) := by
  have hc : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hcx : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hx).1,
    Real.pi_pos], by linarith [(abs_lt.mp hx).2, Real.pi_pos]⟩
  have hz : ‖(Real.sin x : ℂ) ^ 2‖ < 1 := by
    rw [norm_pow, norm_real, Real.norm_eq_abs, sq_abs, ← Real.cos_sq_add_sin_sq x]
    nlinarith
  rw [euler_transformation_of_ne_neg_nat hc hz, show (1 / 2 : ℂ) - a = -(a - 1 / 2) by ring,
    show (1 / 2 : ℂ) - (1 - a) = a - 1 / 2 by ring, sin_sq_cos (a - 1 / 2) hx,
    show -(a - 1 / 2) - (1 - a) = -(1 / 2 : ℂ) by ring,
    show 2 * (a - 1 / 2) = 2 * a - 1 by ring,
    show (1 : ℂ) - (Real.sin x : ℂ) ^ 2 = ((Real.cos x ^ 2 : ℝ) : ℂ) by
      rw [ofReal_pow]; linear_combination -(by exact_mod_cast Real.sin_sq_add_cos_sq x :
        (Real.sin x : ℂ) ^ 2 + (Real.cos x : ℂ) ^ 2 = 1),
    ofReal_cpow_eq_exp (by positivity), Real.log_pow]
  have hc' : (Real.cos x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hcx.ne'
  rw [show ((((2 : ℕ) : ℝ) * Real.log (Real.cos x) : ℝ) : ℂ) * -(1 / 2) =
    -(Real.log (Real.cos x) : ℂ) by push_cast; ring, exp_neg, ofReal_log hcx.le,
    exp_log hc']
  ring

/-- Identity under the stated parameter and domain assumptions: `(2 - 4 * a) * z * ₂F₁ a (1 - a)
(3 / 2) (-z ^ 2) = ((1 + z ^ 2) ^ (1 / 2 : ℂ) + z) ^ (1 - 2 * a) - ((1 + z ^ 2) ^ (1 / 2 : ℂ)
- z) ^ (1 - 2 * a)`. -/
@[dlmf 15.4.E15]
theorem complementary_parameters_odd_sqrt (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (2 - 4 * a) * z * ₂F₁ a (1 - a) (3 / 2) (-z ^ 2) =
      ((1 + z ^ 2) ^ (1 / 2 : ℂ) + z) ^ (1 - 2 * a) - ((1 + z ^ 2) ^ (1 / 2 : ℂ) - z) ^ (1 - 2 * a) := by
  set r : ℂ → ℂ := fun z => (1 + z ^ 2) ^ (1 / 2 : ℂ) with hrdef
  have hc32 : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hdisk : ∀ w : ℂ, ‖w‖ < 1 → ‖-w ^ 2‖ < 1 := fun w hw => by
    rw [norm_neg, norm_pow]; nlinarith [norm_nonneg w]
  have hball : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 2), (2 - 4 * a) * w * ₂F₁ a (1 - a) (3 / 2) (-w ^ 2) =
      (r w + w) ^ (1 - 2 * a) - (r w - w) ^ (1 - 2 * a) := by
    intro w hw
    have hw' : ‖w‖ < 1 / 2 := by simpa using hw
    have hw1 : ‖w‖ < 1 := by linarith
    obtain ⟨hre, hrre, hrsq, -, -, -⟩ := sqrt_one_add_sq_data hw1
    show _ = ((1 + w ^ 2) ^ (1 / 2 : ℂ) + w) ^ (1 - 2 * a) -
      ((1 + w ^ 2) ^ (1 / 2 : ℂ) - w) ^ (1 - 2 * a)
    set R := (1 + w ^ 2) ^ (1 / 2 : ℂ) with hR
    have hr0 : R ≠ 0 := by intro h; rw [h] at hrre; simp at hrre
    set t := w / R with htdef
    have h1w2 : 1 + w ^ 2 ≠ 0 := by intro h; rw [h] at hre; simp at hre
    have ht2 : t ^ 2 = w ^ 2 / (1 + w ^ 2) := by rw [htdef, div_pow, hrsq]
    have hn1 : 3 / 4 ≤ ‖1 + w ^ 2‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-(w ^ 2))
      rw [norm_one, norm_neg, norm_pow, sub_neg_eq_add] at this
      nlinarith [norm_nonneg w]
    have ht2n : ‖t ^ 2‖ < 1 := by
      rw [ht2, norm_div, norm_pow, div_lt_one (by linarith)]
      nlinarith [norm_nonneg w]
    have htn : ‖t‖ < 1 := by
      rw [norm_pow] at ht2n
      nlinarith [norm_nonneg t]
    have hpf : -w ^ 2 / (-w ^ 2 - 1) = t ^ 2 := by
      rw [ht2]
      have : -w ^ 2 - 1 = -(1 + w ^ 2) := by ring
      rw [this]; field_simp
    have h1p : 0 < (1 + t).re := by
      have := neg_le_of_abs_le (abs_re_le_norm t); simp; linarith
    have h1m : 0 < (1 - t).re := by
      have := re_le_norm t; simp; linarith
    have hwt : w = R * t := by rw [htdef]; field_simp
    have hodd := odd_binomial a htn
    rw [pfaff_transformation_of_ne_neg_nat hc32 (hdisk w hw1) (by rw [hpf]; exact ht2n), hpf,
      show (3 / 2 : ℂ) - (1 - a) = a + 1 / 2 by ring,
      show (1 : ℂ) - -w ^ 2 = R ^ 2 by rw [hrsq]; ring, sq_cpow hrre]
    have e1 : R ^ (1 - 2 * a) * (1 + t) ^ (1 - 2 * a) = (R + w) ^ (1 - 2 * a) := by
      rw [cpow_mul_cpow_of_re_pos hrre h1p]; congr 1; rw [hwt]; ring
    have e2 : R ^ (1 - 2 * a) * (1 - t) ^ (1 - 2 * a) = (R - w) ^ (1 - 2 * a) := by
      rw [cpow_mul_cpow_of_re_pos hrre h1m]; congr 1; rw [hwt]; ring
    have e3 : R ^ (1 - 2 * a) = R * R ^ (2 * -a) := by
      rw [show 1 - 2 * a = 1 + 2 * -a by ring, cpow_add _ _ hr0, cpow_one]
    rw [← e1, ← e2, e3]
    conv_lhs => rw [hwt]
    linear_combination (R * R ^ (2 * -a)) * hodd
  have hLan : AnalyticOnNhd ℂ (fun w : ℂ => (2 - 4 * a) * w * ₂F₁ a (1 - a) (3 / 2) (-w ^ 2))
      (Metric.ball 0 1) :=
    fun w hw => (analyticAt_const.mul analyticAt_id).mul
      ((analyticAt_ordinaryHypergeometric (hdisk w (by simpa using hw))).comp
        (f := fun w : ℂ => -w ^ 2) (analyticAt_id.pow 2).neg)
  have hRan : AnalyticOnNhd ℂ (fun w : ℂ => (r w + w) ^ (1 - 2 * a) - (r w - w) ^ (1 - 2 * a))
      (Metric.ball 0 1) := by
    intro w hw
    obtain ⟨hre, -, -, -, hu, hv⟩ := sqrt_one_add_sq_data (by simpa using hw : ‖w‖ < 1)
    have hra : AnalyticAt ℂ r w :=
      (analyticAt_const.add (analyticAt_id.pow 2)).cpow analyticAt_const
        (mem_slitPlane_iff.mpr (Or.inl hre))
    exact ((hra.add analyticAt_id).cpow analyticAt_const (mem_slitPlane_iff.mpr (Or.inl hu))).sub
      ((hra.sub analyticAt_id).cpow analyticAt_const (mem_slitPlane_iff.mpr (Or.inl hv)))
  have hev : (fun w : ℂ => (2 - 4 * a) * w * ₂F₁ a (1 - a) (3 / 2) (-w ^ 2)) =ᶠ[𝓝 0]
      fun w => (r w + w) ^ (1 - 2 * a) - (r w - w) ^ (1 - 2 * a) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with w hw
    exact hball w hw
  exact hLan.eqOn_of_preconnected_of_eventuallyEq hRan (convex_ball 0 1).isPreconnected
    (by simp) hev (by simpa using hz)

/-- Identity under the stated parameter and domain assumptions: `(2 * a - 1) * (Real.sin x : ℂ) *
₂F₁ a (1 - a) (3 / 2) ((Real.sin x : ℂ) ^ 2) = sin ((2 * a - 1) * x)`. -/
@[dlmf 15.4.E16]
theorem sin_sq_sin (a : ℂ) {x : ℝ} (hx : |x| < Real.pi / 2) :
    (2 * a - 1) * (Real.sin x : ℂ) * ₂F₁ a (1 - a) (3 / 2) ((Real.sin x : ℂ) ^ 2) =
      sin ((2 * a - 1) * x) := by
  have hsinA : ∀ x : ℝ, AnalyticAt ℝ (fun x : ℝ => (Real.sin x : ℂ)) x := fun x => by
    simpa [ofReal_sin] using analyticAt_comp_ofReal (f := Complex.sin) (x0 := x) (by fun_prop)
  refine eq_of_analytic_of_abs_lt_pi_div_four (f := fun x : ℝ => (2 * a - 1) * (Real.sin x : ℂ) *
    ₂F₁ a (1 - a) (3 / 2) ((Real.sin x : ℂ) ^ 2)) (g := fun x : ℝ => sin ((2 * a - 1) * x))
    (fun x hx => (analyticAt_const.mul (hsinA x)).mul
      (analyticAt_ordinaryHypergeometric_sin_sq _ _ _ hx))
    (fun x _ => analyticAt_comp_ofReal (f := fun w => sin ((2 * a - 1) * w)) (by fun_prop))
    (fun x hx => ?_) hx
  have hc : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hcx : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hx).1,
    Real.pi_pos], by linarith [(abs_lt.mp hx).2, Real.pi_pos]⟩
  have hP := ordinaryHypergeometric_neg_tan_sq a (a + 1 / 2) hc hx
  have hT := tan_sin a hx
  rw [hP, show (3 / 2 : ℂ) - (a + 1 / 2) = 1 - a by ring] at hT
  have hne : (Real.cos x : ℂ) ^ (2 * a) ≠ 0 := by
    rw [ofReal_cpow_eq_exp hcx]; exact exp_ne_zero _
  have h := mul_left_cancel₀ hne (show (Real.cos x : ℂ) ^ (2 * a) *
    ((1 - 2 * a) * (Real.sin x : ℂ) * ₂F₁ a (1 - a) (3 / 2) ((Real.sin x : ℂ) ^ 2)) =
    (Real.cos x : ℂ) ^ (2 * a) * sin ((1 - 2 * a) * x) by rw [← hT]; ring)
  rw [show (2 * a - 1) * (x : ℂ) = -((1 - 2 * a) * x) by ring, Complex.sin_neg]
  linear_combination -h

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a (a + 1 / 2) (1 + 2 * a) z =
((1 + (1 - z) ^ (1 / 2 : ℂ)) / 2) ^ (-2 * a)`. -/
@[dlmf 15.4.E17]
theorem quadratic_binomial {a z : ℂ} (hc : ∀ k : ℕ, 1 + 2 * a ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    ₂F₁ a (a + 1 / 2) (1 + 2 * a) z =
      ((1 + (1 - z) ^ (1 / 2 : ℂ)) / 2) ^ (-2 * a) := by
  obtain ⟨h1, -, -, -⟩ := quadratic_lobe_of_mem_ball hz
  have hk := kummer_quadratic (a := a) (b := a + 1 / 2)
    (by rw [show a + (a + 1 / 2) + 1 / 2 = 1 + 2 * a by ring]; exact hc) hz
  rw [show a + (a + 1 / 2) + 1 / 2 = 1 + 2 * a by ring,
    show 2 * (a + 1 / 2) = 1 + 2 * a by ring] at hk
  rw [hk, ordinaryHypergeometric_eq_one_sub_neg_cpow
    (fun k hk' => hc k (neg_eq_iff_eq_neg.mp hk'.symm)) h1]
  congr 1 <;> ring_nf

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a (a + 1 / 2) (2 * a) z = (1
- z) ^ (-(1 / 2 : ℂ)) * ((1 + (1 - z) ^ (1 / 2 : ℂ)) / 2) ^ (1 - 2 * a)`. -/
@[dlmf 15.4.E18]
theorem quadratic_binomial_derivative {a z : ℂ} (hc : ∀ k : ℕ, 2 * a ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    ₂F₁ a (a + 1 / 2) (2 * a) z =
      (1 - z) ^ (-(1 / 2 : ℂ)) * ((1 + (1 - z) ^ (1 / 2 : ℂ)) / 2) ^ (1 - 2 * a) := by
  obtain ⟨h1, -, -, -⟩ := quadratic_lobe_of_mem_ball hz
  have hk := kummer_quadratic (a := a) (b := a - 1 / 2)
    (by rw [show a + (a - 1 / 2) + 1 / 2 = 2 * a by ring]; exact hc) hz
  rw [show a + (a - 1 / 2) + 1 / 2 = 2 * a by ring,
    show 2 * (a - 1 / 2) = 2 * a - 1 by ring, ordinaryHypergeometric_symm (2 * a)] at hk
  rw [euler_transformation_of_ne_neg_nat hc hz, show 2 * a - a - (a + 1 / 2) = -(1 / 2) by ring,
    show 2 * a - a = a by ring, show 2 * a - (a + 1 / 2) = a - 1 / 2 by ring, hk,
    ordinaryHypergeometric_eq_one_sub_neg_cpow (fun k hk' => hc k (neg_eq_iff_eq_neg.mp hk'.symm)) h1]
  congr 2 <;> ring_nf

/-- Identity under the stated parameter and domain assumptions: `₂F₁ (a + 1) b a z = (1 - (1 - b /
a) * z) * (1 - z) ^ (-1 - b)`. -/
@[dlmf 15.4.E19]
theorem successor_binomial {a b z : ℂ} (ha : ∀ k : ℕ, a ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    ₂F₁ (a + 1) b a z =
      (1 - (1 - b / a) * z) * (1 - z) ^ (-1 - b) := by
  have ha0 : a ≠ 0 := by simpa using ha 0
  have ha1 : ∀ k : ℕ, a + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat ha 1
  have h := contiguous_shift_b (a := b) (b := a) ha hz
  have hsymm : ₂F₁ b (a + 1) a z = ₂F₁ (a + 1) b a z := by
    unfold ordinaryHypergeometric
    rw [ordinaryHypergeometricSeries_symm]
  rw [hsymm, ordinaryHypergeometric_eq_one_sub_neg_cpow (fun k hk => ha k (neg_eq_iff_eq_neg.mp hk.symm)) hz,
    ordinaryHypergeometric_eq_one_sub_neg_cpow (fun k hk => ha1 k (neg_eq_iff_eq_neg.mp hk.symm)) hz] at h
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz
  have hp : (1 - z) ^ (-b) = (1 - z) * (1 - z) ^ (-1 - b) := by
    calc
      _ = (1 - z) ^ ((1 : ℂ) + (-1 - b)) := by congr 1; ring
      _ = _ := by rw [cpow_add _ _ (sub_ne_zero.mpr hz1.symm), cpow_one]
  rw [hp, show -(b + 1) = -1 - b by ring] at h
  apply mul_left_cancel₀ ha0
  field_simp [ha0]
  linear_combination -h

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a b ((a + b + 1) / 2) (1 / 2)
= (Real.sqrt Real.pi : ℂ) * Gamma ((a + b + 1) / 2) / (Gamma ((a + 1) / 2) * Gamma ((b + 1) /
2))`. -/
@[dlmf 15.4.E28]
theorem gauss_second_summation {a b : ℂ} (hc : ∀ k : ℕ, (a + b + 1) / 2 ≠ -(k : ℂ)) :
    ₂F₁ a b ((a + b + 1) / 2) (1 / 2) =
      (Real.sqrt Real.pi : ℂ) * Gamma ((a + b + 1) / 2) / (Gamma ((a + 1) / 2) * Gamma ((b + 1) / 2)) := by
  set C := (a + b + 1) / 2 with hC
  have hC' : ∀ k : ℕ, a / 2 + b / 2 + 1 / 2 ≠ -(k : ℂ) := by
    rw [show a / 2 + b / 2 + 1 / 2 = C by rw [hC]; ring]; exact hc
  have hre : 0 < (C - a / 2 - b / 2).re := by
    rw [show C - a / 2 - b / 2 = 1 / 2 by rw [hC]; ring]; norm_num
  -- Along real `x → 1/2⁻`, Gauss's quadratic transformation relates both sides.
  have hL : Tendsto (fun x : ℝ => ₂F₁ a b C (x : ℂ)) (𝓝[<] (1 / 2)) (𝓝 (₂F₁ a b C (1 / 2))) := by
    have hc0 := (continuous_ofReal.tendsto (1 / 2 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Iio (1 / 2 : ℝ)))
    rw [show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by push_cast; ring] at hc0
    exact (analyticAt_ordinaryHypergeometric (a := a) (b := b) (c := C)
      (show ‖(1 / 2 : ℂ)‖ < 1 by norm_num)).continuousAt.tendsto.comp hc0
  have hmap : Tendsto (fun x : ℝ => 4 * x * (1 - x)) (𝓝[<] (1 / 2)) (𝓝[<] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := ((show Continuous (fun x : ℝ => 4 * x * (1 - x)) by fun_prop).tendsto (1 / 2)).mono_left
        (nhdsWithin_le_nhds (s := Set.Iio (1 / 2 : ℝ)))
      rw [show (4 : ℝ) * (1 / 2) * (1 - 1 / 2) = 1 by norm_num] at this
      exact this
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_Iio] at hx ⊢
      nlinarith [sq_nonneg (1 - 2 * x)]
  have hR := (tendsto_ordinaryHypergeometric_left_one (a := a / 2) (b := b / 2) hre).comp hmap
  have heq : ∀ᶠ x : ℝ in 𝓝[<] (1 / 2), ₂F₁ a b C (x : ℂ) =
      ₂F₁ (a / 2) (b / 2) C ((4 * x * (1 - x) : ℝ) : ℂ) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 / 2 by norm_num)] with x hx
    have hxn : ‖(x : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]; linarith [hx.2]
    have hyn : ‖4 * (x : ℂ) * (1 - x)‖ < 1 := by
      rw [show 4 * (x : ℂ) * (1 - x) = ((4 * x * (1 - x) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by nlinarith [hx.1, hx.2])]
      nlinarith [sq_nonneg (1 - 2 * x), hx.2]
    have hq := gauss_quadratic (a := a / 2) (b := b / 2) hC' hxn hyn (by simpa using hx.2)
    rw [show a / 2 + b / 2 + 1 / 2 = C by rw [hC]; ring, show 2 * (a / 2) = a by ring,
      show 2 * (b / 2) = b by ring] at hq
    rw [hq]
    push_cast
    ring_nf
  have hlim := tendsto_nhds_unique hL (hR.congr' (by
    filter_upwards [heq] with x hx
    simp only [Function.comp_apply]
    rw [hx]))
  rw [hlim, gauss_summation (a := a / 2) (b := b / 2) (fun k => hc k) hre,
    show C - a / 2 - b / 2 = 1 / 2 by rw [hC]; ring, show C - a / 2 = (b + 1) / 2 by rw [hC]; ring,
    show C - b / 2 = (a + 1) / 2 by rw [hC]; ring, Complex.Gamma_one_half_eq,
    show (Real.sqrt Real.pi : ℂ) = (Real.pi : ℂ) ^ (1 / 2 : ℂ) by
      rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf]
  ring_nf

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a b ((a + b) / 2 + 1) (1 / 2)
= 2 * (Real.sqrt Real.pi : ℂ) / (a - b) * Gamma ((a + b) / 2 + 1) * (1 / (Gamma (a / 2) *
Gamma ((b + 1) / 2)) - 1 / (Gamma ((a + 1) / 2) * Gamma (b / 2)))`. -/
@[dlmf 15.4.E29]
theorem gauss_second_summation_contiguous
    {a b : ℂ}
    (hc : ∀ k : ℕ,
    (a + b) / 2 + 1 ≠ -(k : ℂ))
    (hab : a ≠ b) :
    ₂F₁ a b ((a + b) / 2 + 1) (1 / 2) =
      2 * (Real.sqrt Real.pi : ℂ) / (a - b) * Gamma ((a + b) / 2 + 1) * (1 / (Gamma (a / 2) * Gamma ((b + 1)
        / 2)) - 1 / (Gamma ((a + 1) / 2) * Gamma (b / 2))) := by
  set c := (a + b) / 2 + 1 with hcdef
  have h12 : ‖(1 / 2 : ℂ)‖ < 1 := by norm_num
  have hcon := contiguous_ab (a := a) (b := b) hc h12
  have h1 := gauss_second_summation (a := a + 1) (b := b)
    (by rw [show (a + 1 + b + 1) / 2 = c by rw [hcdef]; ring]; exact hc)
  have h2 := gauss_second_summation (a := a) (b := b + 1)
    (by rw [show (a + (b + 1) + 1) / 2 = c by rw [hcdef]; ring]; exact hc)
  rw [show (a + 1 + b + 1) / 2 = c by rw [hcdef]; ring, show (a + 1 + 1) / 2 = a / 2 + 1 by ring]
    at h1
  rw [show (a + (b + 1) + 1) / 2 = c by rw [hcdef]; ring, show (b + 1 + 1) / 2 = b / 2 + 1 by ring]
    at h2
  have hG (x : ℂ) : x * (Gamma (x / 2 + 1))⁻¹ = 2 * (Gamma (x / 2))⁻¹ := by
    by_cases hx : x = 0
    · subst hx; simp [Complex.Gamma_zero]
    · rw [Complex.Gamma_add_one _ (by simpa using hx), mul_inv]
      field_simp
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have key : (a - b) * ₂F₁ a b c (1 / 2) = a * ₂F₁ (a + 1) b c (1 / 2) - b * ₂F₁ a (b + 1) c (1 / 2) := by
    linear_combination -hcon
  rw [h1, h2] at key
  apply mul_left_cancel₀ hab'
  rw [key, show (a - b) * (2 * (Real.sqrt Real.pi : ℂ) / (a - b) * Gamma c *
      (1 / (Gamma (a / 2) * Gamma ((b + 1) / 2)) - 1 / (Gamma ((a + 1) / 2) * Gamma (b / 2)))) =
      2 * (Real.sqrt Real.pi : ℂ) * Gamma c *
      (1 / (Gamma (a / 2) * Gamma ((b + 1) / 2)) - 1 / (Gamma ((a + 1) / 2) * Gamma (b / 2))) by
    field_simp]
  linear_combination ((Real.sqrt Real.pi : ℂ) * Gamma c * (Gamma ((b + 1) / 2))⁻¹) * hG a -
    ((Real.sqrt Real.pi : ℂ) * Gamma c * (Gamma ((a + 1) / 2))⁻¹) * hG b

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a (1 - a) b (1 / 2) = (2 : ℂ)
^ (1 - b) * (Real.sqrt Real.pi : ℂ) * Gamma b / (Gamma ((a + b) / 2) * Gamma ((b - a + 1) /
2))`. -/
@[dlmf 15.4.E30]
theorem bailey_summation {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -(k : ℂ)) :
    ₂F₁ a (1 - a) b (1 / 2) =
      (2 : ℂ) ^ (1 - b) * (Real.sqrt Real.pi : ℂ) * Gamma b / (Gamma ((a + b) / 2) * Gamma ((b - a + 1) /
        2)) := by
  have h12 : ‖(1 / 2 : ℂ)‖ < 1 := by norm_num
  have hg := gauss_second_summation (a := b - a) (b := b + a - 1)
    (by rw [show (b - a + (b + a - 1) + 1) / 2 = b by ring]; exact hb)
  rw [show (b - a + (b + a - 1) + 1) / 2 = b by ring, show (b + a - 1 + 1) / 2 = (a + b) / 2 by ring]
    at hg
  have harg2 : (2 : ℂ).arg ≠ Real.pi := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, arg_ofReal_of_nonneg (by norm_num)]
    exact Real.pi_pos.ne
  rw [euler_transformation_of_ne_neg_nat hb h12, show b - a - (1 - a) = b - 1 by ring,
    show b - (1 - a) = b + a - 1 by ring, hg,
    show (1 : ℂ) - 1 / 2 = (2 : ℂ)⁻¹ by norm_num, inv_cpow _ _ harg2, ← cpow_neg,
    show -(b - 1) = 1 - b by ring]
  ring

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a (a + 1 / 2) (3 / 2 - 2 * a)
(-1 / 3) = (8 / 9 : ℂ) ^ (-2 * a) * Gamma (4 / 3) * Gamma (3 / 2 - 2 * a) / (Gamma (3 / 2) *
Gamma (4 / 3 - 2 * a))`. -/
@[dlmf 15.4.E31]
theorem value_neg_one_third {a : ℂ} (hc : ∀ k : ℕ, 3 / 2 - 2 * a ≠ -(k : ℂ)) :
    ₂F₁ a (a + 1 / 2) (3 / 2 - 2 * a) (-1 / 3) =
      (8 / 9 : ℂ) ^ (-2 * a) * Gamma (4 / 3) * Gamma (3 / 2 - 2 * a) / (Gamma (3 / 2) * Gamma (4 / 3 - 2 *
        a)) := by
  set A : ℂ := 1 / 3 - a with hA
  have hcA : ∀ k : ℕ, 2 * A + 5 / 6 ≠ -(k : ℂ) := by
    rw [show 2 * A + 5 / 6 = 3 / 2 - 2 * a by rw [hA]; ring]; exact hc
  have hre : 0 < (2 * A + 5 / 6 - A - (A + 1 / 2)).re := by
    rw [show 2 * A + 5 / 6 - A - (A + 1 / 2) = 1 / 3 by ring]; norm_num
  set G : ℂ → ℂ := ₂F₁ (3 * A) (3 * A + 1 / 2) (2 * A + 5 / 6) with hG
  -- Euler's transformation reduces the left side to `G(-1/3)`.
  have hE : ₂F₁ a (a + 1 / 2) (3 / 2 - 2 * a) (-1 / 3) =
      (4 / 3 : ℂ) ^ (1 - 4 * a) * G (-1 / 3) := by
    rw [euler_transformation_of_ne_neg_nat hc (by norm_num), hG,
      show (3 : ℂ) / 2 - 2 * a - a - (a + 1 / 2) = 1 - 4 * a by ring,
      show (1 : ℂ) - -1 / 3 = 4 / 3 by norm_num,
      show (3 : ℂ) / 2 - 2 * a - a = 3 * A + 1 / 2 by rw [hA]; ring,
      show (3 : ℂ) / 2 - 2 * a - (a + 1 / 2) = 3 * A by rw [hA]; ring,
      show (3 : ℂ) / 2 - 2 * a = 2 * A + 5 / 6 by rw [hA]; ring, ordinaryHypergeometric_symm]
  -- the value `G(-1/3)` through the cubic transformation and Abel's theorem
  have hsq : (Real.sqrt Real.pi : ℂ) = (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf
  have hΓ43 : Gamma (4 / 3) = Gamma (1 / 3) / 3 := by
    rw [show (4 / 3 : ℂ) = 1 / 3 + 1 by norm_num, Gamma_add_one _ (by norm_num)]; ring
  have hΓ32 : Gamma (3 / 2) = (Real.sqrt Real.pi : ℂ) / 2 := by
    rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num), Gamma_one_half_eq,
      hsq]; ring
  have hdup : Gamma (2 * A + 5 / 6 - A) * Gamma (2 * A + 5 / 6 - (A + 1 / 2)) =
      Gamma (4 / 3 - 2 * a) * (2 : ℂ) ^ (1 - 2 * (2 / 3 - a)) * (Real.sqrt Real.pi : ℂ) := by
    rw [show 2 * A + 5 / 6 - A = 2 / 3 - a + 1 / 2 by rw [hA]; ring,
      show 2 * A + 5 / 6 - (A + 1 / 2) = 2 / 3 - a by rw [hA]; ring, mul_comm,
      Gamma_mul_Gamma_add_half, show 2 * (2 / 3 - a) = 4 / 3 - 2 * a by ring]
  have hpow : (4 / 3 : ℂ) ^ (1 - 4 * a) * (4 : ℂ) ^ (-2 * A) =
      2 / 3 * (8 / 9 : ℂ) ^ (-2 * a) * (2 : ℂ) ^ (1 - 2 * (2 / 3 - a)) := by
    have e1 : (4 / 3 : ℂ) ^ (1 - 4 * a) = exp (Real.log (4 / 3) * (1 - 4 * a)) := by
      have := ofReal_cpow_eq_exp_log (u := 4 / 3) (by norm_num) (1 - 4 * a); push_cast at this; exact this
    have e2 : (4 : ℂ) ^ (-2 * A) = exp (Real.log 4 * (-2 * A)) := by
      have := ofReal_cpow_eq_exp_log (u := 4) (by norm_num) (-2 * A); push_cast at this; exact this
    have e3 : (8 / 9 : ℂ) ^ (-2 * a) = exp (Real.log (8 / 9) * (-2 * a)) := by
      have := ofReal_cpow_eq_exp_log (u := 8 / 9) (by norm_num) (-2 * a); push_cast at this; exact this
    have e4 : (2 : ℂ) ^ (1 - 2 * (2 / 3 - a)) = exp (Real.log 2 * (1 - 2 * (2 / 3 - a))) := by
      have := ofReal_cpow_eq_exp_log (u := 2) (by norm_num) (1 - 2 * (2 / 3 - a))
      push_cast at this; exact this
    have e5 : (2 / 3 : ℂ) = exp (Real.log (2 / 3)) := by
      rw [← ofReal_exp, Real.exp_log (by norm_num)]; push_cast; ring
    rw [e1, e2, e3, e4]
    nth_rw 1 [e5]
    rw [← exp_add, ← exp_add, ← exp_add]
    congr 1
    have l1 : Real.log (4 / 3) = 2 * Real.log 2 - Real.log 3 := by
      rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    have l2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have l3 : Real.log (8 / 9) = 3 * Real.log 2 - 2 * Real.log 3 := by
      rw [Real.log_div (by norm_num) (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num,
        show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow, Real.log_pow]
      push_cast; ring
    have l4 : Real.log (2 / 3) = Real.log 2 - Real.log 3 := Real.log_div (by norm_num) (by norm_num)
    rw [l1, l2, l3, l4, hA]
    push_cast
    ring
  rw [hE, hG, hypSV_cubic_psi_neg_one_third hcA, gauss_summation hcA hre, hdup, hΓ43, hΓ32,
    show 2 * A + 5 / 6 - A - (A + 1 / 2) = 1 / 3 by ring,
    show 2 * A + 5 / 6 = 3 / 2 - 2 * a by rw [hA]; ring, ← mul_assoc, hpow]
  have h2 : (2 : ℂ) ^ (1 - 2 * (2 / 3 - a)) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; norm_num
  have hs : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  by_cases hg : Gamma (4 / 3 - 2 * a) = 0
  · simp [hg]
  · field_simp

/-- Identity under the stated parameter and domain assumptions: `₂F₁ a (a + 1 / 2) (5 / 6 + 2 * a
/ 3) (1 / 9) = (Real.sqrt Real.pi : ℂ) * (3 / 4 : ℂ) ^ a * Gamma (5 / 6 + 2 * a / 3) / (Gamma
(1 / 2 + a / 3) * Gamma (5 / 6 + a / 3))`. -/
@[dlmf 15.4.E32]
theorem value_one_ninth {a : ℂ} (hc : ∀ k : ℕ, 5 / 6 + 2 * a / 3 ≠ -(k : ℂ)) :
    ₂F₁ a (a + 1 / 2) (5 / 6 + 2 * a / 3) (1 / 9) =
      (Real.sqrt Real.pi : ℂ) * (3 / 4 : ℂ) ^ a * Gamma (5 / 6 + 2 * a / 3) / (Gamma (1 / 2 + a / 3) * Gamma
        (5 / 6 + a / 3)) := by
  set A : ℂ := a / 3 with hA
  have hcA : ∀ k : ℕ, 2 * A + 5 / 6 ≠ -(k : ℂ) := by
    rw [show 2 * A + 5 / 6 = 5 / 6 + 2 * a / 3 by rw [hA]; ring]; exact hc
  have hre : 0 < (2 * A + 5 / 6 - A - (A + 1 / 3)).re := by
    rw [show 2 * A + 5 / 6 - A - (A + 1 / 3) = 1 / 2 by ring]; norm_num
  set G : ℂ → ℂ := ₂F₁ (3 * A) (1 / 3 - A) (2 * A + 5 / 6) with hG
  -- Pfaff's transformation reduces the left side to `G(-1/8)`.
  have hE : ₂F₁ a (a + 1 / 2) (5 / 6 + 2 * a / 3) (1 / 9) = (8 / 9 : ℂ) ^ (-a) * G (-1 / 8) := by
    rw [pfaff_transformation_of_ne_neg_nat hc (by norm_num) (by norm_num), hG,
      show (1 : ℂ) / 9 / (1 / 9 - 1) = -1 / 8 by norm_num, show (1 : ℂ) - 1 / 9 = 8 / 9 by norm_num,
      show 5 / 6 + 2 * a / 3 - (a + 1 / 2) = 1 / 3 - A by rw [hA]; ring,
      show 5 / 6 + 2 * a / 3 = 2 * A + 5 / 6 by rw [hA]; ring, show a = 3 * A by rw [hA]; ring]
  set sr : ℝ → ℝ := fun x => 27 * x / (4 * x - 1) ^ 3 with hsr
  have hsc : ∀ x : ℝ, ((sr x : ℝ) : ℂ) = 27 * (x : ℂ) / (4 * x - 1) ^ 3 := by
    intro x; simp only [hsr]; push_cast; ring
  have hs1 : ∀ x : ℝ, -1 / 8 < x → x ≤ 0 → 0 ≤ sr x ∧ sr x < 1 := by
    intro x hx1 hx2
    have hq : (4 * x - 1) ^ 3 < 0 := by
      have : 4 * x - 1 < 0 := by linarith
      nlinarith [pow_two_nonneg (4 * x - 1)]
    simp only [hsr]
    constructor
    · exact div_nonneg_of_nonpos (by linarith) hq.le
    · rw [div_lt_one_of_neg hq]
      have hid : 27 * x - (4 * x - 1) ^ 3 = (8 * x + 1) ^ 2 * (1 - x) := by ring
      have : 0 < (8 * x + 1) ^ 2 * (1 - x) := mul_pos (pow_pos (by linarith) 2) (by linarith)
      linarith
  have hmap : Tendsto sr (𝓝[>] (-1 / 8)) (𝓝[<] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hcont : ContinuousAt sr (-1 / 8) := by
        simp only [hsr]
        exact ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
      have := hcont.tendsto
      rw [show sr (-1 / 8) = 1 by simp only [hsr]; norm_num] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (-1 / 8 : ℝ) < 0 by norm_num)] with x hx
      exact (hs1 x hx.1 hx.2.le).2
  have hR := (tendsto_ordinaryHypergeometric_left_one hre).comp hmap
  have hP : Tendsto (fun x : ℝ => (1 - 4 * (x : ℂ)) ^ (-3 * A)) (𝓝[>] (-1 / 8))
      (𝓝 ((3 / 2 : ℂ) ^ (-3 * A))) := by
    have h4 : (1 : ℂ) - 4 * ((-1 / 8 : ℝ) : ℂ) = 3 / 2 := by push_cast; norm_num
    have hcont : ContinuousAt (fun x : ℝ => (1 - 4 * (x : ℂ)) ^ (-3 * A)) (-1 / 8) := by
      apply ContinuousAt.cpow (by fun_prop) continuousAt_const
      rw [h4]; exact mem_slitPlane_iff.mpr (Or.inl (by norm_num))
    have := hcont.tendsto
    rw [h4] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hL : Tendsto (fun x : ℝ => G (x : ℂ)) (𝓝[>] (-1 / 8)) (𝓝 (G (-1 / 8))) := by
    have hc0 := (continuous_ofReal.tendsto (-1 / 8 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (-1 / 8 : ℝ)))
    rw [show ((-1 / 8 : ℝ) : ℂ) = -1 / 8 by push_cast; ring] at hc0
    exact (analyticAt_ordinaryHypergeometric (a := 3 * A) (b := 1 / 3 - A) (c := 2 * A + 5 / 6)
      (show ‖(-1 / 8 : ℂ)‖ < 1 by norm_num)).continuousAt.tendsto.comp hc0
  have heq : ∀ᶠ x : ℝ in 𝓝[>] (-1 / 8), G (x : ℂ) =
      (1 - 4 * (x : ℂ)) ^ (-3 * A) * ₂F₁ A (A + 1 / 3) (2 * A + 5 / 6) ((sr x : ℝ) : ℂ) := by
    filter_upwards [Ioo_mem_nhdsGT (show (-1 / 8 : ℝ) < 0 by norm_num)] with x hx
    obtain ⟨h0, h1⟩ := hs1 x hx.1 hx.2.le
    rw [hsc x]
    refine hypSV_cubic_two hcA ?_ ?_ ?_
    · simp; linarith [hx.1]
    · simp; linarith [hx.2]
    · rw [← hsc x, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have hlim := tendsto_nhds_unique hL ((hP.mul hR).congr' (by
    filter_upwards [heq] with x hx
    simp only [Function.comp_apply]
    rw [hx]))
  have hsq : (Real.sqrt Real.pi : ℂ) = (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf
  have hpow : (8 / 9 : ℂ) ^ (-a) * (3 / 2 : ℂ) ^ (-3 * A) = (3 / 4 : ℂ) ^ a := by
    have e1 : (8 / 9 : ℂ) ^ (-a) = exp (Real.log (8 / 9) * (-a)) := by
      have := ofReal_cpow_eq_exp_log (u := 8 / 9) (by norm_num) (-a); push_cast at this; exact this
    have e2 : (3 / 2 : ℂ) ^ (-3 * A) = exp (Real.log (3 / 2) * (-3 * A)) := by
      have := ofReal_cpow_eq_exp_log (u := 3 / 2) (by norm_num) (-3 * A); push_cast at this; exact this
    have e3 : (3 / 4 : ℂ) ^ a = exp (Real.log (3 / 4) * a) := by
      have := ofReal_cpow_eq_exp_log (u := 3 / 4) (by norm_num) a; push_cast at this; exact this
    rw [e1, e2, e3, ← exp_add]
    congr 1
    have l1 : Real.log (8 / 9) = 3 * Real.log 2 - 2 * Real.log 3 := by
      rw [Real.log_div (by norm_num) (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num,
        show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow, Real.log_pow]
      push_cast; ring
    have l2 : Real.log (3 / 2) = Real.log 3 - Real.log 2 := Real.log_div (by norm_num) (by norm_num)
    have l3 : Real.log (3 / 4) = Real.log 3 - 2 * Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    rw [l1, l2, l3, hA]
    push_cast
    ring
  rw [hE, hlim, gauss_summation hcA hre,
    show 2 * A + 5 / 6 - A - (A + 1 / 3) = 1 / 2 by ring,
    show 2 * A + 5 / 6 - A = 5 / 6 + a / 3 by rw [hA]; ring,
    show 2 * A + 5 / 6 - (A + 1 / 3) = 1 / 2 + a / 3 by rw [hA]; ring,
    show 2 * A + 5 / 6 = 5 / 6 + 2 * a / 3 by rw [hA]; ring, Gamma_one_half_eq, ← hsq, ← mul_assoc,
    hpow]
  ring

end DLMF.Hypergeometric
end
end
