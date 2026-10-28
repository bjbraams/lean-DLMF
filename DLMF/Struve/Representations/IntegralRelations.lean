/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.Representations.Mellin

/-!
# Further Struve integral relations

Branch-square-root estimates and further integral relations for the Struve functions.

Source references and common attribution are retained in
`DLMF.Struve.Representations`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Struve

open DLMF.Bessel

/-- Principal square roots of slit-plane numbers lie in the open right half-plane. -/
theorem re_cpow_half_pos {x : ℂ} (hx : x ∈ slitPlane) : 0 < (x^(1/2:ℂ)).re := by
  rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by push_cast; ring, cpow_ofReal_re]
  have hx0 := slitPlane_ne_zero hx
  have harg := (mem_slitPlane_iff_arg.1 hx).1
  have h1 : -π < arg x := neg_pi_lt_arg x
  have h2 : arg x < π := lt_of_le_of_ne (arg_le_pi x) harg
  apply mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 hx0) _)
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos]

/-- Identity under the stated parameter and domain assumptions: `(x^(1/2:ℂ))^2 = x`. -/
theorem cpow_half_sq (x : ℂ) : (x^(1/2:ℂ))^2 = x := by
  have := cpow_nat_inv_pow x (n := 2) two_ne_zero
  rwa [show ((2:ℕ):ℂ)⁻¹ = 1/2 by norm_num] at this

/-- Identity under the stated parameter and domain assumptions: `r = a`. -/
theorem eq_of_sq_eq_of_re_pos {r a : ℂ} (hr : 0 < r.re) (ha : 0 < a.re) (h : r^2 = a^2) :
    r = a := by
  have h0 : (r - a)*(r + a) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h0 with h1 | h1
  · linear_combination h1
  · exfalso; have := congrArg Complex.re h1; simp at this; linarith

/-- Formula under the stated hypotheses: `p / r ∈ slitPlane`. -/
theorem div_mem_slitPlane_of_re_pos {p r : ℂ} (hp : 0 < p.re) (hr : 0 < r.re) :
    p / r ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_contra hc
  push Not at hc
  have hr0 : r ≠ 0 := fun h => by rw [h] at hr; simp at hr
  have hpe : p = (p/r)*r := by field_simp
  have : p.re = (p/r).re * r.re := by
    conv_lhs => rw [hpe]
    simp [mul_re, hc.2]
  nlinarith [hc.1]

/-- Formula under the stated hypotheses: `a^2 + u ∈ slitPlane`. -/
theorem sq_add_mem_slitPlane {a : ℂ} (ha : 0 < a.re) {u : ℝ} (hu : 0 ≤ u) :
    a^2 + u ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases him : a.im = 0
  · left
    have : (a^2 + u).re = a.re^2 - a.im^2 + u := by simp [sq, mul_re]
    rw [this, him]; nlinarith
  · right
    have : (a^2 + u).im = 2*a.re*a.im := by simp [sq, mul_im]; ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero two_ne_zero ha.ne') him

/-- `∫₀¹ du/(b²-u²) = log((1+b)/a)/b` with `b = (1+a²)^{1/2}`, `Re a > 0`. -/
theorem integral_recip_one_add_sq_sub_sq {a : ℂ} (ha : 0 < a.re) :
    (∫ u : ℝ in 0..1, 1/((1+a^2) - (u:ℂ)^2)) =
      log ((1+(1+a^2)^(1/2:ℂ))/a) / (1+a^2)^(1/2:ℂ) := by
  set b : ℂ := (1+a^2)^(1/2:ℂ) with hbdef
  have hslit : ∀ u : ℝ, u ∈ uIcc (0:ℝ) 1 → a^2 + ((1-u^2:ℝ):ℂ) ∈ slitPlane := by
    intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    exact sq_add_mem_slitPlane ha (by nlinarith [hu.1, hu.2])
  have hb1 : a^2 + ((1-(0:ℝ)^2:ℝ):ℂ) = 1+a^2 := by push_cast; ring
  have hbre : 0 < b.re := by
    have := re_cpow_half_pos (hslit 0 (by simp))
    rwa [hb1] at this
  have hb2 : b^2 = 1+a^2 := cpow_half_sq _
  set r : ℝ → ℂ := fun u => (a^2 + ((1-u^2:ℝ):ℂ))^(1/2:ℂ) with hrdef
  have hrre : ∀ u ∈ uIcc (0:ℝ) 1, 0 < (r u).re := fun u hu => re_cpow_half_pos (hslit u hu)
  have hr2 : ∀ u : ℝ, (r u)^2 = b^2 - (u:ℂ)^2 := by
    intro u; simp only [r]; rw [cpow_half_sq, hb2]; push_cast; ring
  have hr0 : r 0 = b := by simp only [r]; rw [hb1]
  have hr1 : r 1 = a := by
    apply eq_of_sq_eq_of_re_pos (hrre 1 (by simp)) ha
    rw [hr2, hb2]; push_cast; ring
  set Φ : ℝ → ℂ := fun u => log ((b+u)/r u) / b
  have hbne : b ≠ 0 := fun h => by rw [h] at hbre; simp at hbre
  have hderiv : ∀ u ∈ uIcc (0:ℝ) 1, HasDerivAt Φ (1/((1+a^2) - (u:ℂ)^2)) u := by
    intro u hu
    have hrne : r u ≠ 0 := fun h => by have := hrre u hu; rw [h] at this; simp at this
    have hpre : 0 < (b + u).re := by
      rw [uIcc_of_le zero_le_one] at hu; simp; linarith [hu.1]
    have hpne : b + (u:ℂ) ≠ 0 := fun h => by rw [h] at hpre; simp at hpre
    have hq : HasDerivAt (fun u : ℝ => a^2 + ((1-u^2:ℝ):ℂ)) (-(2*(u:ℂ))) u := by
      have := ((hasDerivAt_pow 2 u).const_sub 1).ofReal_comp.const_add (a^2)
      convert this using 1; push_cast; ring
    have hr : HasDerivAt r (-(u:ℂ) / r u) u := by
      have := (hasStrictDerivAt_cpow_const (c := 1/2) (hslit u hu)).hasDerivAt.comp u hq
      refine this.congr_deriv ?_
      set Q : ℂ := a^2 + ((1-u^2:ℝ):ℂ) with hQdef
      have hQne : Q ≠ 0 := slitPlane_ne_zero (hslit u hu)
      have hru : r u = Q^(1/2:ℂ) := rfl
      have hQ : Q = (r u)^2 := (cpow_half_sq Q).symm
      have : Q^((1/2:ℂ)-1) = (r u)⁻¹ := by
        rw [cpow_sub _ _ hQne, cpow_one, ← hru]
        conv_lhs => rw [hQ]
        field_simp
      rw [this]; field_simp
    have hp : HasDerivAt (fun u : ℝ => b + (u:ℂ)) 1 u := by
      simpa using (hasDerivAt_id (u:ℝ)).ofReal_comp.const_add b
    have hdiv := hp.div hr hrne
    have hlog := hdiv.clog_real (div_mem_slitPlane_of_re_pos hpre (hrre u hu))
    have := hlog.div_const b
    convert this using 1
    have hr2u := hr2 u
    rw [← hb2]
    have hden : b^2 - (u:ℂ)^2 ≠ 0 := by rw [← hr2u]; exact pow_ne_zero 2 hrne
    simp only [Pi.div_apply]
    field_simp
    linear_combination (b*(u:ℂ) + (u:ℂ)^2) * hr2u
  have hcont : ContinuousOn (fun u : ℝ => 1/((1+a^2) - (u:ℂ)^2)) (uIcc 0 1) := by
    refine continuousOn_const.div (by fun_prop) fun u hu => ?_
    have hrne : r u ≠ 0 := fun h => by have := hrre u hu; rw [h] at this; simp at this
    rw [← hb2, ← hr2]; exact pow_ne_zero 2 hrne
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [Φ, hr0, hr1]
  push_cast
  rw [add_zero, div_self hbne, log_one, zero_div, sub_zero, add_comm]

/-- Nonvanishing under the stated hypotheses: `(1+a^2) - (u:ℂ)^2 ≠ 0`. -/
theorem one_add_sq_sub_sq_ne_zero {a : ℂ} (ha : 0 < a.re) {u : ℝ} (hu : u ∈ uIcc (0:ℝ) 1) :
    (1+a^2) - (u:ℂ)^2 ≠ 0 := by
  rw [uIcc_of_le zero_le_one] at hu
  have := slitPlane_ne_zero (sq_add_mem_slitPlane ha (u := 1-u^2) (by nlinarith [hu.1, hu.2]))
  convert this using 1; push_cast; ring

/-- `∫₀¹ (1-s²)^{-1/2} s/(a²+s²) ds = log((1+b)/a)/b`. -/
theorem integral_poissonWeight_mul_div_sq_add {a : ℂ} (ha : 0 < a.re) :
    (∫ s : ℝ in 0..1, (1-(s:ℂ)^2)^(-1/2:ℂ) * ((s:ℂ)/(a^2+(s:ℂ)^2))) =
      log ((1+(1+a^2)^(1/2:ℂ))/a) / (1+a^2)^(1/2:ℂ) := by
  have h := integral_poissonWeight_eq_trig 0 (fun s : ℝ => (s:ℂ)/(a^2+(s:ℂ)^2))
  rw [show (0:ℂ)-1/2 = -1/2 by ring] at h
  rw [h, ← integral_recip_one_add_sq_sub_sq ha]
  simp only [mul_zero, cpow_zero, mul_one]
  set g : ℝ → ℂ := fun u => 1/((1+a^2) - (u:ℂ)^2)
  have hsub := intervalIntegral.integral_deriv_smul_comp' (a := 0) (b := π/2) (f := Real.sin)
    (f' := Real.cos) (g := g) (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn
    (by
      refine ContinuousOn.mono (s := uIcc 0 1) ?_ ?_
      · exact continuousOn_const.div (by fun_prop) fun u hu => one_add_sq_sub_sq_ne_zero ha hu
      · rintro _ ⟨x, hx, rfl⟩
        rw [uIcc_of_le (by positivity)] at hx
        rw [uIcc_of_le zero_le_one]
        exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2, Real.pi_pos]),
          Real.sin_le_one x⟩)
  rw [Real.sin_zero, Real.sin_pi_div_two] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  simp only [g, Function.comp, real_smul]
  have hc : (Real.cos θ : ℂ)^2 = 1 - (Real.sin θ : ℂ)^2 := by
    rw [← ofReal_pow, ← ofReal_pow, Real.cos_sq']; push_cast; ring
  rw [hc]; ring

/-- `H₀` is bounded on the positive real axis. -/
theorem exists_bound_struveH_zero : ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ‖struveH 0 t‖ ≤ C := by
  set w : ℝ → ℂ := fun s => (1-(s:ℂ)^2)^(-1/2:ℂ)
  have hw : IntervalIntegrable w volume 0 1 := by
    have := intervalIntegrable_poissonWeight (ν := 0) (by norm_num)
    convert this using 3; norm_num
  refine ⟨2/π * ∫ s : ℝ in 0..1, ‖w s‖, fun t ht => ?_⟩
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    simp only [ofReal_zero, struveH, zero_div, zero_add, cpow_one, zero_mul, norm_zero]
    exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg zero_le_one fun _ _ =>
      norm_nonneg _)
  rw [struveH_eq_poisson (by norm_num) (ofReal_ne_zero.2 hpos.ne')]
  rw [cpow_zero, zero_add, Complex.Gamma_one_half_eq, show (0:ℂ)-1/2 = -1/2 by ring]
  have hs : (π:ℂ)^(1/2:ℂ) = (Real.sqrt π : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf
  have hp : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  rw [hs, hp, mul_one, norm_mul]
  have h2 : ‖(2:ℂ)/π‖ = 2/π := by
    rw [norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [h2]
  gcongr
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans ?_
  refine intervalIntegral.integral_mono_on zero_le_one ?_ hw.norm fun s _ => ?_
  · exact (hw.mul_continuousOn (by fun_prop)).norm
  · rw [norm_mul]
    have : ‖sin ((t:ℂ)*s)‖ ≤ 1 := by
      rw [← ofReal_mul, ← ofReal_sin, norm_real, Real.norm_eq_abs]
      exact Real.abs_sin_le_one _
    calc ‖w s‖ * ‖sin ((t:ℂ)*s)‖ ≤ ‖w s‖ * 1 := by gcongr
      _ = ‖w s‖ := mul_one _

/-- Formula under the stated hypotheses: `a^2 - 1 + u ∈ slitPlane`. -/
theorem sq_sub_one_add_mem_slitPlane {a : ℂ} (ha : 1 < a.re) {u : ℝ} (hu : 0 ≤ u) :
    a^2 - 1 + u ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases him : a.im = 0
  · left
    have : (a^2 - 1 + u).re = a.re^2 - a.im^2 - 1 + u := by simp [sq, mul_re]
    rw [this, him]; nlinarith
  · right
    have : (a^2 - 1 + u).im = 2*a.re*a.im := by simp [sq, mul_im]; ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (by linarith)) him

/-- Formula under the stated hypotheses: `1 - 1/a^2 ∈ slitPlane`. -/
theorem one_sub_recip_sq_mem_slitPlane {a : ℂ} (ha : 1 < a.re) : 1 - 1/a^2 ∈ slitPlane := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha; linarith
  rw [mem_slitPlane_iff]
  by_cases him : a.im = 0
  · left
    have hae : a = (a.re:ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hae, ← ofReal_pow, ← ofReal_one, ← ofReal_div, ← ofReal_sub, ofReal_re]
    have h1 : 1 < a.re^2 := by nlinarith
    have : 1/a.re^2 < 1 := by rw [div_lt_one (by positivity)]; exact h1
    linarith
  · right
    have h2 : (a^2).im ≠ 0 := by
      rw [sq, mul_im]; intro h; apply him; nlinarith [h]
    rw [sub_im, one_im, one_div, inv_im, zero_sub, neg_ne_zero, neg_div, neg_ne_zero]
    exact div_ne_zero h2 (normSq_pos.2 (pow_ne_zero 2 ha0)).ne'

/-- `√(a²-1) = a √(1-a⁻²)` for `Re a > 1`. -/
theorem cpow_half_sq_sub_one {a : ℂ} (ha : 1 < a.re) :
    (a^2-1)^(1/2:ℂ) = a * (1-1/a^2)^(1/2:ℂ) := by
  set S : Set ℂ := {z | 1 < z.re}
  have hS : IsPreconnected S := (convex_halfSpace_re_gt 1).isPreconnected
  have hslit1 : ∀ z ∈ S, z^2 - 1 ∈ slitPlane := fun z hz => by
    simpa using sq_sub_one_add_mem_slitPlane (u := 0) hz le_rfl
  have hf : ContinuousOn (fun z : ℂ => (z^2-1)^(1/2:ℂ)) S := fun z hz =>
    ((by fun_prop : ContinuousAt (fun z : ℂ => z^2-1) z).cpow continuousAt_const
      (hslit1 z hz)).continuousWithinAt
  have hz0 : ∀ z ∈ S, z ≠ 0 := fun z hz h => by
    simp only [S, mem_ofPred_eq] at hz; rw [h] at hz; simp at hz; linarith
  have hg : ContinuousOn (fun z : ℂ => z * (1-1/z^2)^(1/2:ℂ)) S := fun z hz => by
    have h1 : ContinuousAt (fun z : ℂ => 1 - 1/z^2) z :=
      continuousAt_const.sub (continuousAt_const.div (by fun_prop) (pow_ne_zero 2 (hz0 z hz)))
    exact (continuousAt_id.mul (h1.cpow continuousAt_const
      (one_sub_recip_sq_mem_slitPlane hz))).continuousWithinAt
  have hsq : EqOn ((fun z : ℂ => (z^2-1)^(1/2:ℂ))^2) ((fun z : ℂ => z * (1-1/z^2)^(1/2:ℂ))^2) S := by
    intro z hz
    simp only [Pi.pow_apply, mul_pow, cpow_half_sq]
    field_simp [hz0 z hz]
  have hne : ∀ {z : ℂ}, z ∈ S → z * (1-1/z^2)^(1/2:ℂ) ≠ 0 := by
    intro z hz
    refine mul_ne_zero (hz0 z hz) fun h => ?_
    have := re_cpow_half_pos (one_sub_recip_sq_mem_slitPlane hz)
    rw [h] at this; simp at this
  have h2 : (2:ℂ) ∈ S := by simp [S]
  rcases hS.eq_or_eq_neg_of_sq_eq hf hg hsq hne with h | h
  · exact h ha
  · exfalso
    have h1 := h h2
    have hp1 := re_cpow_half_pos (hslit1 2 h2)
    have hp2 := re_cpow_half_pos (one_sub_recip_sq_mem_slitPlane (a := 2) (by simp))
    simp only [Pi.neg_apply] at h1
    rw [h1] at hp1
    simp only [neg_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero] at hp1
    linarith

/-- For `Re q > 0` and `Re p = Re q`, the quotient `p/q` lies in the slit plane. -/
theorem div_mem_slitPlane_of_re_eq {p q : ℂ} (hq : 0 < q.re) (h : p.re = q.re) :
    p / q ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_contra hc
  push Not at hc
  have hq0 : q ≠ 0 := fun h0 => by rw [h0] at hq; simp at hq
  have hpe : p = (p/q)*q := by field_simp
  have : p.re = (p/q).re * q.re := by
    conv_lhs => rw [hpe]
    simp [mul_re, hc.2]
  nlinarith [hc.1]

/-- Nonvanishing under the stated hypotheses: `(a^2-1) + (u:ℂ)^2 ≠ 0`. -/
theorem sq_sub_one_add_sq_ne_zero {a : ℂ} (ha : 1 < a.re) (u : ℝ) :
    (a^2-1) + (u:ℂ)^2 ≠ 0 := by
  have := slitPlane_ne_zero (sq_sub_one_add_mem_slitPlane ha (u := u^2) (sq_nonneg u))
  convert this using 1; push_cast; ring

/-- Logarithmic form of `∫₀¹ du/(c²+u²)`, `c = (a²-1)^{1/2}`. -/
theorem integral_recip_sq_sub_one_add_sq_log {a : ℂ} (ha : 1 < a.re) :
    (∫ u : ℝ in 0..1, 1/((a^2-1) + (u:ℂ)^2)) =
      -I*log (I/a+(1-1/a^2)^(1/2:ℂ)) / (a^2-1)^(1/2:ℂ) := by
  set c : ℂ := (a^2-1)^(1/2:ℂ) with hcdef
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha; linarith
  have hslit : ∀ u : ℝ, a^2 - 1 + ((u^2:ℝ):ℂ) ∈ slitPlane :=
    fun u => sq_sub_one_add_mem_slitPlane ha (sq_nonneg u)
  have hcre : 0 < c.re := by
    have := re_cpow_half_pos (hslit 0)
    rwa [show a^2-1+(((0:ℝ)^2:ℝ):ℂ) = a^2-1 by push_cast; ring] at this
  have hc2 : c^2 = a^2-1 := cpow_half_sq _
  have hcne : c ≠ 0 := fun h => by rw [h] at hcre; simp at hcre
  set r : ℝ → ℂ := fun u => (a^2 - 1 + ((u^2:ℝ):ℂ))^(1/2:ℂ) with hrdef
  have hrre : ∀ u, 0 < (r u).re := fun u => re_cpow_half_pos (hslit u)
  have hrne : ∀ u, r u ≠ 0 := fun u h => by have := hrre u; rw [h] at this; simp at this
  have hr2 : ∀ u : ℝ, (r u)^2 = c^2 + (u:ℂ)^2 := by
    intro u; simp only [r]; rw [cpow_half_sq, hc2]; push_cast; ring
  have hr0 : r 0 = c := by simp [r, c]
  have hr1 : r 1 = a := by
    have ha' : 0 < a.re := by linarith
    apply eq_of_sq_eq_of_re_pos (hrre 1) ha'
    rw [hr2, hc2]; push_cast; ring
  set Ψ : ℝ → ℂ := fun u => -I*log ((c+I*u)/r u) / c
  have hderiv : ∀ u ∈ uIcc (0:ℝ) 1, HasDerivAt Ψ (1/((a^2-1) + (u:ℂ)^2)) u := by
    intro u _
    have hpre : 0 < (c + I*u).re := by simp; exact hcre
    have hpne : c + I*(u:ℂ) ≠ 0 := fun h => by rw [h] at hpre; simp at hpre
    have hq : HasDerivAt (fun u : ℝ => a^2 - 1 + ((u^2:ℝ):ℂ)) (2*(u:ℂ)) u := by
      have := (hasDerivAt_pow 2 u).ofReal_comp.const_add (a^2-1)
      convert this using 1; push_cast; ring
    have hr : HasDerivAt r ((u:ℂ) / r u) u := by
      have := (hasStrictDerivAt_cpow_const (c := 1/2) (hslit u)).hasDerivAt.comp u hq
      refine this.congr_deriv ?_
      set Q : ℂ := a^2 - 1 + ((u^2:ℝ):ℂ) with hQdef
      have hQne : Q ≠ 0 := slitPlane_ne_zero (hslit u)
      have hru : r u = Q^(1/2:ℂ) := rfl
      have hQ : Q = (r u)^2 := (cpow_half_sq Q).symm
      have : Q^((1/2:ℂ)-1) = (r u)⁻¹ := by
        rw [cpow_sub _ _ hQne, cpow_one, ← hru]
        conv_lhs => rw [hQ]
        field_simp [hrne u]
      rw [this]; field_simp [hrne u]
    have hp : HasDerivAt (fun u : ℝ => c + I*(u:ℂ)) I u := by
      simpa using ((hasDerivAt_id (u:ℝ)).ofReal_comp.const_mul I).const_add c
    have hdiv := hp.div hr (hrne u)
    have hlog := hdiv.clog_real (div_mem_slitPlane_of_re_pos hpre (hrre u))
    have := (hlog.const_mul (-I)).div_const c
    convert this using 1
    have hr2u := hr2 u
    rw [← hc2]
    have hden : c^2 + (u:ℂ)^2 ≠ 0 := by rw [← hr2u]; exact pow_ne_zero 2 (hrne u)
    have hrn := hrne u
    have hpne' : c + (u:ℂ)*I ≠ 0 := by rw [mul_comm]; exact hpne
    simp only [Pi.div_apply]
    field_simp
    linear_combination (c*(u:ℂ)*I - (u:ℂ)^2) * hr2u +
      (c^2*(r u)^2 - c^2*(u:ℂ)^2 + (r u)^2*(u:ℂ)^2 - (u:ℂ)^4) * I_sq
  have hcont : ContinuousOn (fun u : ℝ => 1/((a^2-1) + (u:ℂ)^2)) (uIcc 0 1) :=
    continuousOn_const.div (by fun_prop) fun u _ => sq_sub_one_add_sq_ne_zero ha u
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [Ψ, hr0, hr1]
  push_cast
  rw [mul_zero, add_zero, div_self hcne, log_one, mul_zero, zero_div, sub_zero, mul_one]
  congr 3
  rw [hcdef, cpow_half_sq_sub_one ha]
  field_simp
  ring

/-- Arctangent form of `∫₀¹ du/(c²+u²)`, `c = (a²-1)^{1/2}`. -/
theorem integral_recip_sq_sub_one_add_sq_arctan {a : ℂ} (ha : 1 < a.re) :
    (∫ u : ℝ in 0..1, 1/((a^2-1) + (u:ℂ)^2)) =
      arctan (1/((a^2-1)^(1/2:ℂ))) / (a^2-1)^(1/2:ℂ) := by
  set c : ℂ := (a^2-1)^(1/2:ℂ) with hcdef
  have hcre : 0 < c.re := by
    have := re_cpow_half_pos (sq_sub_one_add_mem_slitPlane ha (u := 0) le_rfl)
    rwa [show a^2-1+((0:ℝ):ℂ) = a^2-1 by push_cast; ring] at this
  have hc2 : c^2 = a^2-1 := cpow_half_sq _
  have hcne : c ≠ 0 := fun h => by rw [h] at hcre; simp at hcre
  set Λ : ℝ → ℂ := fun u => -I/2 * log ((1+(u/c)*I)/(1-(u/c)*I)) / c
  have hderiv : ∀ u ∈ uIcc (0:ℝ) 1, HasDerivAt Λ (1/((a^2-1) + (u:ℂ)^2)) u := by
    intro u _
    have hD : 1-((u:ℂ)/c)*I ≠ 0 := by
      intro h
      have : c - (u:ℂ)*I = c * (1-((u:ℂ)/c)*I) := by field_simp
      rw [h, mul_zero] at this
      have := congrArg Complex.re this; simp at this; linarith
    have hN : 1+((u:ℂ)/c)*I ≠ 0 := by
      intro h
      have : c + (u:ℂ)*I = c * (1+((u:ℂ)/c)*I) := by field_simp
      rw [h, mul_zero] at this
      have := congrArg Complex.re this; simp at this; linarith
    have hslit : (1+((u:ℂ)/c)*I)/(1-((u:ℂ)/c)*I) ∈ slitPlane := by
      have : (1+((u:ℂ)/c)*I)/(1-((u:ℂ)/c)*I) = (c + (u:ℂ)*I)/(c - (u:ℂ)*I) := by
        field_simp
      rw [this]
      exact div_mem_slitPlane_of_re_eq (by simpa using hcre) (by simp)
    have hNd : HasDerivAt (fun u : ℝ => 1+((u:ℂ)/c)*I) (I/c) u := by
      have := (((hasDerivAt_id (u:ℝ)).ofReal_comp.div_const c).mul_const I).const_add 1
      exact this.congr_deriv (by norm_num; ring)
    have hDd : HasDerivAt (fun u : ℝ => 1-((u:ℂ)/c)*I) (-(I/c)) u := by
      have := (((hasDerivAt_id (u:ℝ)).ofReal_comp.div_const c).mul_const I).const_sub 1
      exact this.congr_deriv (by norm_num; ring)
    have hlog := (hNd.div hDd hD).clog_real hslit
    have := (hlog.const_mul (-I/2)).div_const c
    convert this using 1
    rw [← hc2]
    have hden : c^2 + (u:ℂ)^2 ≠ 0 := by rw [hc2]; exact sq_sub_one_add_sq_ne_zero ha u
    have hden' : c^2 - (u:ℂ)^2*I^2 ≠ 0 := by rw [I_sq]; convert hden using 1; ring
    simp only [Pi.div_apply]
    field_simp
    ring_nf
    rw [I_sq]
    ring_nf
    linear_combination (-2*c) * mul_inv_cancel₀ hden
  have hcont : ContinuousOn (fun u : ℝ => 1/((a^2-1) + (u:ℂ)^2)) (uIcc 0 1) :=
    continuousOn_const.div (by fun_prop) fun u _ => sq_sub_one_add_sq_ne_zero ha u
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [Λ, Complex.arctan]
  push_cast
  simp

/-- Poisson form of `L₀` on the positive axis. -/
theorem struveL_zero_eq_poisson {t : ℝ} (ht : 0 < t) :
    struveL 0 t = 2/π * ∫ s : ℝ in 0..1, (1-(s:ℂ)^2)^(-1/2:ℂ) * sinh ((t:ℂ)*s) := by
  rw [struveL_eq_poisson (by norm_num) (ofReal_ne_zero.2 ht.ne')]
  rw [cpow_zero, zero_add, Complex.Gamma_one_half_eq, show (0:ℂ)-1/2 = -1/2 by ring]
  have hs : (π:ℂ)^(1/2:ℂ) = (Real.sqrt π : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf
  have hp : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  rw [hs, hp]; ring

/-- Estimate under the stated parameter and domain assumptions: `‖sinh ((t:ℂ)*s)‖ ≤ Real.exp
(1*t)`. -/
theorem norm_sinh_mul_le {t s : ℝ} (ht : 0 < t) (hs : s ∈ Ioc (0:ℝ) 1) :
    ‖sinh ((t:ℂ)*s)‖ ≤ Real.exp (1*t) := by
  rw [← ofReal_mul, ← ofReal_sinh, norm_real, Real.norm_eq_abs, one_mul,
    abs_of_nonneg (Real.sinh_nonneg_iff.2 (by nlinarith [hs.1])), Real.sinh_eq]
  have h1 : Real.exp (t*s) ≤ Real.exp t := Real.exp_le_exp.2 (by nlinarith [hs.2])
  have h2 : 0 < Real.exp (-(t*s)) := Real.exp_pos _
  have h3 : 0 < Real.exp t := Real.exp_pos _
  linarith

/-- `L₀` grows at most like `e^t` on the positive axis. -/
theorem exists_bound_struveL_zero :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ‖struveL 0 t‖ ≤ C * Real.exp t := by
  set w : ℝ → ℂ := fun s => (1-(s:ℂ)^2)^(-1/2:ℂ)
  have hw : IntervalIntegrable w volume 0 1 := by
    have := intervalIntegrable_poissonWeight (ν := 0) (by norm_num)
    convert this using 3; norm_num
  set C : ℝ := 2/π * ∫ s : ℝ in 0..1, ‖w s‖
  have hC : 0 ≤ C := mul_nonneg (by positivity)
    (intervalIntegral.integral_nonneg zero_le_one fun _ _ => norm_nonneg _)
  refine ⟨C, fun t ht => ?_⟩
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    simp only [ofReal_zero, struveL, zero_div, zero_add, cpow_one, zero_mul, norm_zero]
    positivity
  rw [struveL_zero_eq_poisson hpos, norm_mul]
  have h2 : ‖(2:ℂ)/π‖ = 2/π := by
    rw [norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [h2, show C * Real.exp t = 2/π * ((∫ s : ℝ in 0..1, ‖w s‖) * Real.exp t) by ring]
  gcongr
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans ?_
  rw [← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one ?_ (hw.norm.mul_const _)
    fun s hs => ?_
  · exact (hw.mul_continuousOn (by fun_prop)).norm
  · rw [norm_mul]
    have := norm_sinh_mul_le hpos ⟨hs.1, hs.2.le⟩
    rw [one_mul] at this
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)

/-- Laplace transform of `L₀` in terms of `∫₀¹ du/((a²-1)+u²)`. -/
lemma struveL_zero_laplace_aux {a : ℂ} (ha : 1 < a.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-a*t)*struveL 0 t) 0
      (2/π * ∫ u : ℝ in 0..1, 1/((a^2-1) + (u:ℂ)^2)) := by
  set w : ℝ → ℂ := fun s => (1-(s:ℂ)^2)^(-1/2:ℂ)
  have hk : Continuous (Function.uncurry fun t s : ℝ => sinh ((t:ℂ)*s)) := by
    simp only [Function.uncurry_def]; fun_prop
  obtain ⟨hI, hV⟩ := laplace_poissonWeight (a := a) (β := 1) ha hk
    (fun t s ht hs => norm_sinh_mul_le ht hs)
  have hae : ∀ t ∈ Ioi (0:ℝ), exp (-a*t) * struveL 0 t =
      2/π * (exp (-a*t) * ∫ s : ℝ in 0..1, w s * sinh ((t:ℂ)*s)) := by
    intro t ht; rw [struveL_zero_eq_poisson ht]; ring
  have hI' : IntegrableOn (fun t : ℝ => exp (-a*t)*struveL 0 t) (Ioi 0) :=
    IntegrableOn.congr_fun (Integrable.const_mul hI (2/π:ℂ)) (fun t ht => (hae t ht).symm)
      measurableSet_Ioi
  have hval : (∫ t : ℝ in Ioi 0, exp (-a*t)*struveL 0 t) =
      2/π * ∫ u : ℝ in 0..1, 1/((a^2-1) + (u:ℂ)^2) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hae, integral_const_mul, hV]
    congr 1
    have h1 : (∫ s : ℝ in 0..1, w s * ∫ t : ℝ in Ioi 0, exp (-a*t) * sinh ((t:ℂ)*s)) =
        ∫ s : ℝ in 0..1, w s * ((s:ℂ)/(a^2-(s:ℂ)^2)) := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => ?_)
      rw [uIoc_of_le zero_le_one] at hs
      rw [laplace_sinh_mul ha hs]
    rw [h1]
    have h := integral_poissonWeight_eq_trig 0 (fun s : ℝ => (s:ℂ)/(a^2-(s:ℂ)^2))
    rw [show (0:ℂ)-1/2 = -1/2 by ring] at h
    rw [h]
    simp only [mul_zero, cpow_zero, mul_one]
    set g : ℝ → ℂ := fun u => 1/((a^2-1) + (u:ℂ)^2)
    have hsub := intervalIntegral.integral_deriv_smul_comp' (a := 0) (b := π/2) (f := Real.sin)
      (f' := Real.cos) (g := g) (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn
      (continuousOn_const.div (by fun_prop) fun u _ => sq_sub_one_add_sq_ne_zero ha u)
    rw [Real.sin_zero, Real.sin_pi_div_two] at hsub
    rw [← hsub]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [g, Function.comp, real_smul]
    have hc : (Real.cos θ : ℂ)^2 = 1 - (Real.sin θ : ℂ)^2 := by
      rw [← ofReal_pow, ← ofReal_pow, Real.cos_sq']; push_cast; ring
    rw [hc]; ring
  have := intervalIntegral_tendsto_integral_Ioi 0 hI' tendsto_id
  rw [hval] at this
  exact this

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => exp (-a*t)*struveH 0
t) 0 (2/(π*((1+a^2)^(1/2:ℂ)))*log ((1+((1+a^2)^(1/2:ℂ)))/a))`. -/
@[dlmf 11.7.E13]
theorem struve_laplace_13 {a : ℂ} (ha : 0 < a.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-a*t)*struveH 0 t) 0 (2/(π*((1+a^2)^(1/2:ℂ)))*log ((1+((1+a^2)^(1/2:ℂ)))/a)) := by
  set w : ℝ → ℂ := fun s => (1-(s:ℂ)^2)^(-1/2:ℂ)
  have hH : ∀ t : ℝ, 0 < t → struveH 0 t = 2/π * ∫ s : ℝ in 0..1, w s * sin ((t:ℂ)*s) := by
    intro t ht
    rw [struveH_eq_poisson (by norm_num) (ofReal_ne_zero.2 ht.ne')]
    rw [cpow_zero, zero_add, Complex.Gamma_one_half_eq, show (0:ℂ)-1/2 = -1/2 by ring]
    have hs : (π:ℂ)^(1/2:ℂ) = (Real.sqrt π : ℂ) := by
      rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf
    have hp : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
      rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
    rw [hs, hp]; ring
  have hk : Continuous (Function.uncurry fun t s : ℝ => sin ((t:ℂ)*s)) := by
    simp only [Function.uncurry_def]; fun_prop
  have hkb : ∀ t s : ℝ, 0 < t → s ∈ Ioc (0:ℝ) 1 → ‖sin ((t:ℂ)*s)‖ ≤ Real.exp (0*t) := by
    intro t s _ _
    rw [zero_mul, Real.exp_zero, ← ofReal_mul, ← ofReal_sin, norm_real, Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  obtain ⟨hI, hV⟩ := laplace_poissonWeight (a := a) (β := 0) ha hk hkb
  have hae : ∀ t ∈ Ioi (0:ℝ), exp (-a*t) * struveH 0 t =
      2/π * (exp (-a*t) * ∫ s : ℝ in 0..1, w s * sin ((t:ℂ)*s)) := by
    intro t ht; rw [hH t ht]; ring
  have hI' : IntegrableOn (fun t : ℝ => exp (-a*t)*struveH 0 t) (Ioi 0) :=
    IntegrableOn.congr_fun (Integrable.const_mul hI (2/π:ℂ)) (fun t ht => (hae t ht).symm)
      measurableSet_Ioi
  have hval : (∫ t : ℝ in Ioi 0, exp (-a*t)*struveH 0 t) =
      2/(π*((1+a^2)^(1/2:ℂ)))*log ((1+((1+a^2)^(1/2:ℂ)))/a) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hae, integral_const_mul, hV]
    have : (∫ s : ℝ in 0..1, w s * ∫ t : ℝ in Ioi 0, exp (-a*t) * sin ((t:ℂ)*s)) =
        ∫ s : ℝ in 0..1, w s * ((s:ℂ)/(a^2+(s:ℂ)^2)) :=
      intervalIntegral.integral_congr fun s _ => by rw [laplace_sin_mul ha]
    rw [this, integral_poissonWeight_mul_div_sq_add ha]
    ring
  have := intervalIntegral_tendsto_integral_Ioi 0 hI' tendsto_id
  rw [hval] at this
  exact this

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => exp (-a*t)*struveH 1
t) 0 (2/(π*a)-2*a/(π*((1+a^2)^(1/2:ℂ)))*log ((1+((1+a^2)^(1/2:ℂ)))/a))`. -/
@[dlmf 11.7.E14]
theorem struve_laplace_14 {a : ℂ} (ha : 0 < a.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-a*t)*struveH 1 t) 0 (2/(π*a)-2*a/(π*((1+a^2)^(1/2:ℂ)))*log ((1+((1+a^2)^(1/2:ℂ)))/a)) := by
  set L : ℂ := 2/(π*((1+a^2)^(1/2:ℂ)))*log ((1+((1+a^2)^(1/2:ℂ)))/a)
  have h13 : Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R, exp (-a*t)*struveH 0 t) atTop (𝓝 L) :=
    struve_laplace_13 ha
  have hre : (-a).re < 0 := by simp; linarith
  have hexp : Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R, exp (-a*t)) atTop (𝓝 (1/a)) := by
    have := intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_exp_mul_complex_Ioi hre 0)
      tendsto_id
    rw [integral_exp_mul_complex_Ioi hre 0] at this
    have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
    convert this using 2
    · rfl
    · rw [ofReal_zero, mul_zero, Complex.exp_zero]
      field_simp
  obtain ⟨C, hC⟩ := exists_bound_struveH_zero
  have hbd : Tendsto (fun R : ℝ => exp (-a*R) * struveH 0 R) atTop (𝓝 0) := by
    have hE : Tendsto (fun R : ℝ => ‖exp (-a*R)‖) atTop (𝓝 0) := by
      have : (fun R : ℝ => ‖exp (-a*R)‖) = fun R => Real.exp ((-a).re * R) := by
        funext R; rw [Complex.norm_exp]; simp
      rw [this]
      exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hre)
    have hEC : Tendsto (fun R : ℝ => ‖exp (-a*R)‖ * C) atTop (𝓝 0) := by
      have := hE.mul_const C; rwa [zero_mul] at this
    refine squeeze_zero_norm' ?_ hEC
    filter_upwards [eventually_ge_atTop 0] with R hR
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC R hR) (norm_nonneg _)
  have hH0 : Differentiable ℂ (struveH 0) := by simpa using struveH_nat_entire 0
  have hH1 : Differentiable ℂ (struveH 1) := by simpa using struveH_nat_entire 1
  have hc0 : Continuous fun t : ℝ => struveH 0 t := hH0.continuous.comp continuous_ofReal
  have hc1 : Continuous fun t : ℝ => struveH 1 t := hH1.continuous.comp continuous_ofReal
  have hval : ∀ R : ℝ, (∫ t in (0:ℝ)..R, exp (-a*t)*struveH 1 t) =
      2/π * (∫ t in (0:ℝ)..R, exp (-a*t)) - (exp (-a*R) * struveH 0 R +
        a * ∫ t in (0:ℝ)..R, exp (-a*t)*struveH 0 t) := by
    intro R
    have hu : ∀ x ∈ uIcc (0:ℝ) R, HasDerivAt (fun t : ℝ => exp (-a*t)) (-a * exp (-a*x)) x := by
      intro x _
      have := ((hasDerivAt_id (x:ℝ)).ofReal_comp.const_mul (-a)).cexp
      exact this.congr_deriv (by simp only [id, ofReal_one, mul_one]; ring)
    have hv : ∀ x ∈ uIcc (0:ℝ) R, HasDerivAt (fun t : ℝ => struveH 0 t)
        (2/π - struveH 1 x) x := fun x _ => (struveH_zero_deriv x).comp_ofReal
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
      ((by fun_prop : Continuous fun x : ℝ => -a * exp (-a*x)).intervalIntegrable _ _)
      ((continuous_const.sub hc1).intervalIntegrable _ _)
    have hsplit : (∫ t in (0:ℝ)..R, exp (-a*t)*struveH 1 t) =
        (∫ t in (0:ℝ)..R, 2/π * exp (-a*t)) -
          ∫ t in (0:ℝ)..R, exp (-a*t) * (2/π - struveH 1 t) := by
      rw [← intervalIntegral.integral_sub]
      · congr 1; funext t; ring
      · exact (by fun_prop : Continuous fun t : ℝ => 2/π * exp (-a*t)).intervalIntegrable _ _
      · exact ((by fun_prop : Continuous fun t : ℝ => exp (-a*t)).mul
          (continuous_const.sub hc1)).intervalIntegrable _ _
    rw [hsplit, hibp, intervalIntegral.integral_const_mul]
    have hz : struveH 0 ((0:ℝ):ℂ) = 0 := by
      simp only [ofReal_zero, struveH, zero_div, zero_add, cpow_one, zero_mul]
    have hneg : (∫ x in (0:ℝ)..R, -a * exp (-a*x) * struveH 0 x) =
        -a * ∫ t in (0:ℝ)..R, exp (-a*t)*struveH 0 t := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; ring
    rw [hneg, hz]
    ring
  have : (fun R : ℝ => ∫ t in (0:ℝ)..R, exp (-a*t)*struveH 1 t) = fun R =>
      2/π * (∫ t in (0:ℝ)..R, exp (-a*t)) - (exp (-a*R) * struveH 0 R +
        a * ∫ t in (0:ℝ)..R, exp (-a*t)*struveH 0 t) := funext hval
  unfold HasIntegralAtTop
  rw [this]
  have hlim := (hexp.const_mul (2/π:ℂ)).sub (hbd.add (h13.const_mul a))
  convert hlim using 2
  simp only [L, zero_add]
  ring

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => exp (-a*t)*struveL 0
t) 0 (2/(π*((a^2-1)^(1/2:ℂ)))*(-I*log (I/a+(1-1/a^2)^(1/2:ℂ))))`. -/
@[dlmf 11.7.E15]
theorem struve_laplace_15 {a : ℂ} (ha : 1 < a.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-a*t)*struveL 0 t) 0 (2/(π*((a^2-1)^(1/2:ℂ)))*(-I*log (I/a+(1-1/a^2)^(1/2:ℂ)))) := by
  have h := struveL_zero_laplace_aux ha
  rw [integral_recip_sq_sub_one_add_sq_log ha] at h
  convert h using 1
  ring

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => exp (-a*t)*struveL 1
t) 0 (2*a/(π*((a^2-1)^(1/2:ℂ)))*arctan (1/((a^2-1)^(1/2:ℂ)))-2/(π*a))`. -/
@[dlmf 11.7.E16]
theorem struve_laplace_16 {a : ℂ} (ha : 1 < a.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-a*t)*struveL 1 t) 0 (2*a/(π*((a^2-1)^(1/2:ℂ)))*arctan (1/((a^2-1)^(1/2:ℂ)))-2/(π*a)) := by
  set L : ℂ := 2/π * (arctan (1/((a^2-1)^(1/2:ℂ))) / (a^2-1)^(1/2:ℂ))
  have h15 : Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R, exp (-a*t)*struveL 0 t) atTop (𝓝 L) := by
    have h := struveL_zero_laplace_aux ha
    rwa [integral_recip_sq_sub_one_add_sq_arctan ha] at h
  have ha0' : 0 < a.re := by linarith
  have hre : (-a).re < 0 := by simp; linarith
  have hexp : Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R, exp (-a*t)) atTop (𝓝 (1/a)) := by
    have := intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_exp_mul_complex_Ioi hre 0)
      tendsto_id
    rw [integral_exp_mul_complex_Ioi hre 0] at this
    have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha; linarith
    convert this using 2
    · rfl
    · rw [ofReal_zero, mul_zero, Complex.exp_zero]
      field_simp
  obtain ⟨C, hC⟩ := exists_bound_struveL_zero
  have hbd : Tendsto (fun R : ℝ => exp (-a*R) * struveL 0 R) atTop (𝓝 0) := by
    have hE : Tendsto (fun R : ℝ => Real.exp ((1 - a.re) * R)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
    have hEC : Tendsto (fun R : ℝ => Real.exp ((1 - a.re) * R) * C) atTop (𝓝 0) := by
      have := hE.mul_const C; rwa [zero_mul] at this
    refine squeeze_zero_norm' ?_ hEC
    filter_upwards [eventually_ge_atTop 0] with R hR
    rw [norm_mul, Complex.norm_exp]
    have : (-a*(R:ℂ)).re = -a.re*R := by simp
    rw [this]
    calc Real.exp (-a.re*R) * ‖struveL 0 R‖ ≤ Real.exp (-a.re*R) * (C * Real.exp R) :=
          mul_le_mul_of_nonneg_left (hC R hR) (Real.exp_pos _).le
      _ = Real.exp ((1 - a.re) * R) * C := by
          rw [show (1 - a.re) * R = -a.re*R + R by ring, Real.exp_add]; ring
  have hL0 : Differentiable ℂ (struveL 0) := by simpa using struveL_nat_entire 0
  have hL1 : Differentiable ℂ (struveL 1) := by simpa using struveL_nat_entire 1
  have hc1 : Continuous fun t : ℝ => struveL 1 t := hL1.continuous.comp continuous_ofReal
  have hval : ∀ R : ℝ, (∫ t in (0:ℝ)..R, exp (-a*t)*struveL 1 t) =
      (exp (-a*R) * struveL 0 R + a * ∫ t in (0:ℝ)..R, exp (-a*t)*struveL 0 t) -
        2/π * (∫ t in (0:ℝ)..R, exp (-a*t)) := by
    intro R
    have hu : ∀ x ∈ uIcc (0:ℝ) R, HasDerivAt (fun t : ℝ => exp (-a*t)) (-a * exp (-a*x)) x := by
      intro x _
      have := ((hasDerivAt_id (x:ℝ)).ofReal_comp.const_mul (-a)).cexp
      exact this.congr_deriv (by simp only [id, ofReal_one, mul_one]; ring)
    have hv : ∀ x ∈ uIcc (0:ℝ) R, HasDerivAt (fun t : ℝ => struveL 0 t)
        (2/π + struveL 1 x) x := fun x _ => (struveL_zero_deriv x).comp_ofReal
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
      ((by fun_prop : Continuous fun x : ℝ => -a * exp (-a*x)).intervalIntegrable _ _)
      ((continuous_const.add hc1).intervalIntegrable _ _)
    have hsplit : (∫ t in (0:ℝ)..R, exp (-a*t)*struveL 1 t) =
        (∫ t in (0:ℝ)..R, exp (-a*t) * (2/π + struveL 1 t)) -
          ∫ t in (0:ℝ)..R, 2/π * exp (-a*t) := by
      rw [← intervalIntegral.integral_sub]
      · congr 1; funext t; ring
      · exact ((by fun_prop : Continuous fun t : ℝ => exp (-a*t)).mul
          (continuous_const.add hc1)).intervalIntegrable _ _
      · exact (by fun_prop : Continuous fun t : ℝ => 2/π * exp (-a*t)).intervalIntegrable _ _
    rw [hsplit, hibp, intervalIntegral.integral_const_mul]
    have hz : struveL 0 ((0:ℝ):ℂ) = 0 := by
      simp only [ofReal_zero, struveL, zero_div, zero_add, cpow_one, zero_mul]
    have hneg : (∫ x in (0:ℝ)..R, -a * exp (-a*x) * struveL 0 x) =
        -a * ∫ t in (0:ℝ)..R, exp (-a*t)*struveL 0 t := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; ring
    rw [hneg, hz]
    ring
  unfold HasIntegralAtTop
  rw [funext hval]
  have hlim := (hbd.add (h15.const_mul a)).sub (hexp.const_mul (2/π:ℂ))
  convert hlim using 2
  simp only [L, zero_add]
  ring

end DLMF.Struve

end
