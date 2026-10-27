/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.FurtherTransformations
public import DLMF.Hypergeometric.ParameterHolomorphy

/-!
# Tools for the cubic connection formula (DLMF 15.8.32)

The proof of `cubic_connection` (DLMF 15.8.32) works in the variable `u = 1/ζ`. With
`ω = e^{2πi/3}` and `t = √3 i` (so `ω = (-1+t)/2`, `ω² = (-1-t)/2`):

* `hcub_cubic`: Goursat's cubic transformation near `u = 0`,
  `F(a+1/3, 3a; 2a+2/3; u) = (1+ω²u)^{-3a} F(a, a+1/3; 2a+2/3; 3t u(u-1)/(1+ω²u)³)`, proved by
  the uniqueness of the analytic solution of the Gauss equation at the origin;
* `hcub_conn`: the bracket of 15.8.32 written through `w₁, w₂` at `0` equals
  `√3 Γ(a+1/3)/(2π Γ(2a+2/3)) F(a, a+1/3; 2a+2/3; 1-w)`, from 15.10.17 for generic `a` and
  holomorphy in `a` (all `a` with `2a+2/3, a+1/3 ∉ -ℕ`);
* `hcub_main`: the two combined near `u = 0` (where `w = Z³` with `Z = ω²(1+ωu)/(u+ω)` and the
  principal cube root of `w` is `ω² Z`) and continued by the identity theorem to the convex set
  `{Im u > 0, |u| < 1}`, where `|Z| < 1`;
* `hcub_cpow`: the bookkeeping of principal powers on the image `u = 1/2 + iY`, `0 < Y < √3/2`,
  of the ray `x < -1`, by comparing logarithms whose imaginary parts differ by less than `2π`.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace DLMF.Hypergeometric


/-- Powers of `t` with `t² = -3`. -/
theorem hcub_tpow {t : ℂ} (ht : t ^ 2 = -3) :
    t ^ 3 = -3 * t ∧ t ^ 4 = 9 ∧ t ^ 5 = 9 * t ∧ t ^ 6 = -27 ∧ t ^ 7 = -27 * t ∧ t ^ 8 = 81 ∧
      t ^ 9 = 81 * t ∧ t ^ 10 = -243 ∧ t ^ 11 = -243 * t ∧ t ^ 12 = 729 := by
  have h3 : t ^ 3 = -3 * t := by rw [pow_succ, ht]
  have h4 : t ^ 4 = 9 := by rw [show 4 = 2 + 2 from rfl, pow_add, ht]; norm_num
  have h5 : t ^ 5 = 9 * t := by rw [pow_succ, h4]
  have h6 : t ^ 6 = -27 := by rw [show 6 = 4 + 2 from rfl, pow_add, h4, ht]; norm_num
  have h7 : t ^ 7 = -27 * t := by rw [pow_succ, h6]
  have h8 : t ^ 8 = 81 := by rw [show 8 = 6 + 2 from rfl, pow_add, h6, ht]; norm_num
  have h9 : t ^ 9 = 81 * t := by rw [pow_succ, h8]
  have h10 : t ^ 10 = -243 := by rw [show 10 = 8 + 2 from rfl, pow_add, h8, ht]; norm_num
  have h11 : t ^ 11 = -243 * t := by rw [pow_succ, h10]
  have h12 : t ^ 12 = 729 := by rw [show 12 = 10 + 2 from rfl, pow_add, h10, ht]; norm_num
  exact ⟨h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

set_option maxRecDepth 10000 in
/-- The Gauss-equation algebra of the cubic transformation: the operator of
`(1+ω²u)^{-3a} F(φ(u))` is a multiple of the Gauss operator of `F` at `φ(u)`. -/
theorem hcub_ode_alg {t a u P h0 h1 h2 : ℂ} (ht : t ^ 2 = -3)
    (hq : 1 + (-1 - t) / 2 * u ≠ 0) (hr : 1 + (-1 + t) / 2 * u ≠ 0)
    (hode : 3 * t * u * (u - 1) / (1 + (-1 - t) / 2 * u) ^ 3 *
        (1 - 3 * t * u * (u - 1) / (1 + (-1 - t) / 2 * u) ^ 3) * h2 +
      (2 * a + 2 / 3 - (a + (a + 1 / 3) + 1) * (3 * t * u * (u - 1) / (1 + (-1 - t) / 2 * u) ^ 3))
        * h1 - a * (a + 1 / 3) * h0 = 0) :
    u * (1 - u) * ((-3 * a) * (-3 * a - 1) * ((-1 - t) / 2) ^ 2 * P / (1 + (-1 - t) / 2 * u) ^ 2 * h0 +
        2 * ((-3 * a) * ((-1 - t) / 2) * P / (1 + (-1 - t) / 2 * u)) *
          (h1 * (3 * t * ((2 * u - 1) * (1 + (-1 - t) / 2 * u) - 3 * ((-1 - t) / 2) * u * (u - 1)) /
            (1 + (-1 - t) / 2 * u) ^ 4)) +
        P * (h2 * (3 * t * ((2 * u - 1) * (1 + (-1 - t) / 2 * u) - 3 * ((-1 - t) / 2) * u * (u - 1)) /
            (1 + (-1 - t) / 2 * u) ^ 4) ^ 2 +
          h1 * (3 * t * ((2 * (1 + (-1 - t) / 2 * u) - 2 * ((-1 - t) / 2) * (2 * u - 1)) *
            (1 + (-1 - t) / 2 * u) - 4 * ((-1 - t) / 2) * ((2 * u - 1) * (1 + (-1 - t) / 2 * u) -
              3 * ((-1 - t) / 2) * u * (u - 1))) / (1 + (-1 - t) / 2 * u) ^ 5))) +
      (2 * a + 2 / 3 - (a + 1 / 3 + 3 * a + 1) * u) *
        ((-3 * a) * ((-1 - t) / 2) * P / (1 + (-1 - t) / 2 * u) * h0 +
          P * (h1 * (3 * t * ((2 * u - 1) * (1 + (-1 - t) / 2 * u) - 3 * ((-1 - t) / 2) * u * (u - 1)) /
            (1 + (-1 - t) / 2 * u) ^ 4))) -
      (a + 1 / 3) * (3 * a) * (P * h0) = 0 := by
  obtain ⟨h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hcub_tpow ht
  linear_combination (norm := skip)
    (-P * (3 * t) * ((2 * u - 1) * (1 + (-1 - t) / 2 * u) - 3 * ((-1 - t) / 2) * u * (u - 1)) ^ 2 /
      ((1 + (-1 - t) / 2 * u) ^ 2 * (1 + (-1 + t) / 2 * u) ^ 3)) * hode
  generalize hQ : 1 + (-1 - t) / 2 * u = Q at hq ⊢
  generalize hR : 1 + (-1 + t) / 2 * u = R at hr ⊢
  field_simp
  subst hQ hR
  ring_nf
  simp only [ht, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  ring_nf

/-- The cubic map `φ(u) = K u (u - 1) / (1 + m u)³` and its derivatives. -/
theorem hcub_phi_hasDerivAt {K m u : ℂ} (hq : 1 + m * u ≠ 0) :
    HasDerivAt (fun v => K * v * (v - 1) / (1 + m * v) ^ 3)
      (K * ((2 * u - 1) * (1 + m * u) - 3 * m * u * (u - 1)) / (1 + m * u) ^ 4) u := by
  have h : HasDerivAt (fun v => K * v * (v - 1) / (1 + m * v) ^ 3) _ u :=
    (((hasDerivAt_id' u).const_mul K).mul ((hasDerivAt_id' u).sub_const 1)).div
      ((((hasDerivAt_id' u).const_mul m).const_add 1).pow 3) (pow_ne_zero 3 hq)
  convert h using 1
  simp only [Pi.mul_apply, Nat.cast_ofNat, show (3 : ℕ) - 1 = 2 from rfl]
  field_simp
  ring

/-- Second derivative of the cubic map. -/
theorem hcub_phi_deriv_hasDerivAt {K m u : ℂ} (hq : 1 + m * u ≠ 0) :
    HasDerivAt (fun v => K * ((2 * v - 1) * (1 + m * v) - 3 * m * v * (v - 1)) / (1 + m * v) ^ 4)
      (K * ((2 * (1 + m * u) - 2 * m * (2 * u - 1)) * (1 + m * u) -
        4 * m * ((2 * u - 1) * (1 + m * u) - 3 * m * u * (u - 1))) / (1 + m * u) ^ 5) u := by
  have hN : HasDerivAt (fun v => (2 * v - 1) * (1 + m * v) - 3 * m * v * (v - 1))
      (2 * (1 + m * u) - 2 * m * (2 * u - 1)) u := by
    have h : HasDerivAt (fun v => (2 * v - 1) * (1 + m * v) - 3 * m * v * (v - 1)) _ u :=
      ((((hasDerivAt_id' u).const_mul 2).sub_const 1).mul
        (((hasDerivAt_id' u).const_mul m).const_add 1)).sub
        (((hasDerivAt_id' u).const_mul (3 * m)).mul ((hasDerivAt_id' u).sub_const 1))
    convert h using 1
    ring
  have h : HasDerivAt (fun v => K * ((2 * v - 1) * (1 + m * v) - 3 * m * v * (v - 1)) /
      (1 + m * v) ^ 4) _ u :=
    (hN.const_mul K).div ((((hasDerivAt_id' u).const_mul m).const_add 1).pow 4)
      (pow_ne_zero 4 hq)
  convert h using 1
  simp only [Nat.cast_ofNat, show (4 : ℕ) - 1 = 3 from rfl]
  field_simp


/-- `t = √3 i` satisfies `t² = -3`. -/
theorem hcub_t_sq : ((Real.sqrt 3 : ℂ) * I) ^ 2 = -3 := by
  rw [mul_pow, I_sq, ← ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring

/-- `‖√3 i‖ = √3`. -/
theorem hcub_norm_t : ‖(Real.sqrt 3 : ℂ) * I‖ = Real.sqrt 3 := by
  rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- `|ω| = |ω²| = 1`. -/
theorem hcub_norm_m (ε : ℝ) (hε : ε = 1 ∨ ε = -1) : ‖(-1 + ε * ((Real.sqrt 3 : ℂ) * I)) / 2‖ = 1 := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  rw [show (-1 + ε * ((Real.sqrt 3 : ℂ) * I)) / 2 = ⟨-1 / 2, ε * Real.sqrt 3 / 2⟩ by
    apply Complex.ext <;> simp]
  rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sqrt_eq_one]
  simp only
  nlinarith

/-- A crude bound `√3 < 7/4`. -/
theorem hcub_sqrt3_lt : Real.sqrt 3 < 7 / 4 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `Re(1 + m u) > 0` when `|m| = 1` and `|u| < 1`. -/
theorem hcub_one_add_mul_re_pos {m u : ℂ} (hm : ‖m‖ = 1) (hu : ‖u‖ < 1) : 0 < (1 + m * u).re := by
  have h := abs_re_le_norm (m * u)
  rw [norm_mul, hm, one_mul] at h
  rw [add_re, one_re]
  linarith [neg_abs_le (m * u).re]

/-- `|1 + m u| ≥ 1 - |u|` when `|m| = 1`. -/
theorem hcub_one_add_mul_norm_ge {m u : ℂ} (hm : ‖m‖ = 1) : 1 - ‖u‖ ≤ ‖1 + m * u‖ := by
  have := norm_sub_norm_le (1 : ℂ) (-(m * u))
  rw [norm_one, norm_neg, norm_mul, hm, one_mul, sub_neg_eq_add] at this
  exact this

/-- Goursat's cubic transformation near the origin:
`F(a+1/3, 3a; 2a+2/3; u) = (1+ω²u)^{-3a} F(a, a+1/3; 2a+2/3; 3√3 i u(u-1)/(1+ω²u)³)`. -/
theorem hcub_cubic {a : ℂ} (hc : ∀ k : ℕ, 2 * a + 2 / 3 ≠ -(k : ℂ)) {u : ℂ} (hu : ‖u‖ < 1 / 10) :
    ₂F₁ (a + 1 / 3) (3 * a) (2 * a + 2 / 3) u =
      (1 + (-1 - (Real.sqrt 3 : ℂ) * I) / 2 * u) ^ (-3 * a) *
        ₂F₁ a (a + 1 / 3) (2 * a + 2 / 3) (3 * ((Real.sqrt 3 : ℂ) * I) * u * (u - 1) /
          (1 + (-1 - (Real.sqrt 3 : ℂ) * I) / 2 * u) ^ 3) := by
  set t : ℂ := (Real.sqrt 3 : ℂ) * I with htdef
  have ht : t ^ 2 = -3 := hcub_t_sq
  have hm : ‖(-1 - t) / 2‖ = 1 := by
    have := hcub_norm_m (-1) (Or.inr rfl); rw [← htdef] at this; convert this using 2; push_cast; ring
  have hω : ‖(-1 + t) / 2‖ = 1 := by
    have := hcub_norm_m 1 (Or.inl rfl); rw [← htdef] at this; convert this using 2; push_cast; ring
  set m : ℂ := (-1 - t) / 2 with hmdef
  set H : ℂ → ℂ := ₂F₁ a (a + 1 / 3) (2 * a + 2 / 3) with hH
  set P : ℂ → ℂ := fun w => (1 + m * w) ^ (-3 * a) with hP
  set φ : ℂ → ℂ := fun v => (3 * t) * v * (v - 1) / (1 + m * v) ^ 3 with hφdef
  have hsmall : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 10), ‖w‖ < 1 / 10 := fun w hw => by simpa using hw
  have hq0 : ∀ w : ℂ, ‖w‖ < 1 / 10 → 1 + m * w ≠ 0 := fun w hw h => by
    have := hcub_one_add_mul_re_pos hm (show ‖w‖ < 1 by linarith)
    rw [h, zero_re] at this; exact lt_irrefl _ this
  have hr0 : ∀ w : ℂ, ‖w‖ < 1 / 10 → 1 + (-1 + t) / 2 * w ≠ 0 := fun w hw h => by
    have := hcub_one_add_mul_re_pos hω (show ‖w‖ < 1 by linarith)
    rw [h, zero_re] at this; exact lt_irrefl _ this
  have hslit : ∀ w : ℂ, ‖w‖ < 1 / 10 → 1 + m * w ∈ slitPlane := fun w hw =>
    mem_slitPlane_iff.mpr (Or.inl (hcub_one_add_mul_re_pos hm (by linarith)))
  have hφn : ∀ w : ℂ, ‖w‖ < 1 / 10 → ‖φ w‖ < 1 := by
    intro w hw
    have h1 : 9 / 10 ≤ ‖1 + m * w‖ := by linarith [hcub_one_add_mul_norm_ge (u := w) hm]
    have h2 : ‖w - 1‖ ≤ 11 / 10 := by
      have := norm_sub_le w 1; rw [norm_one] at this; linarith
    have h3 : ‖(3 : ℂ)‖ * ‖t‖ ≤ 21 / 4 := by
      rw [htdef, hcub_norm_t]; norm_num; linarith [hcub_sqrt3_lt]
    simp only [hφdef, norm_div, norm_mul, norm_pow]
    rw [div_lt_one (by positivity)]
    have hw0 := norm_nonneg w
    calc ‖(3 : ℂ)‖ * ‖t‖ * ‖w‖ * ‖w - 1‖ ≤ 21 / 4 * (1 / 10) * (11 / 10) := by
          gcongr
      _ < (9 / 10) ^ 3 := by norm_num
      _ ≤ ‖1 + m * w‖ ^ 3 := by gcongr
  have hPa : ∀ w : ℂ, ‖w‖ < 1 / 10 → AnalyticAt ℂ P w := fun w hw =>
    (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).cpow analyticAt_const (hslit w hw)
  have hφa : ∀ w : ℂ, ‖w‖ < 1 / 10 → AnalyticAt ℂ φ w := fun w hw =>
    ((((analyticAt_const.mul analyticAt_id).mul (analyticAt_id.sub analyticAt_const))).div
      ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).pow 3))
      (pow_ne_zero 3 (hq0 w hw))
  have hballo : IsOpen {w : ℂ | ‖w‖ < 1 / 10} := isOpen_lt continuous_norm continuous_const
  have hφdd : ∀ w : ℂ, ‖w‖ < 1 / 10 → deriv (deriv φ) w =
      3 * t * ((2 * (1 + m * w) - 2 * m * (2 * w - 1)) * (1 + m * w) -
        4 * m * ((2 * w - 1) * (1 + m * w) - 3 * m * w * (w - 1))) / (1 + m * w) ^ 5 := by
    intro w hw
    have hev : deriv φ =ᶠ[𝓝 w] fun v =>
        3 * t * ((2 * v - 1) * (1 + m * v) - 3 * m * v * (v - 1)) / (1 + m * v) ^ 4 := by
      filter_upwards [hballo.mem_nhds hw] with v hv
      exact (hcub_phi_hasDerivAt (hq0 v hv)).deriv
    rw [hev.deriv_eq]
    exact (hcub_phi_deriv_hasDerivAt (hq0 w hw)).deriv
  have hG : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 10), (fun v => P v * H (φ v)) w =
      ₂F₁ (a + 1 / 3) (3 * a) (2 * a + 2 / 3) w := by
    refine eq_ordinaryHypergeometric_of_gaussOperator hc (by norm_num) (by norm_num) ?_ ?_ ?_
    · intro w hw
      have hw1 := hsmall w hw
      exact (hPa w hw1).mul ((analyticAt_ordinaryHypergeometric (hφn w hw1)).comp
        (f := φ) (hφa w hw1))
    · intro w hw
      have hw1 := hsmall w hw
      have hHa : AnalyticAt ℂ H (φ w) := analyticAt_ordinaryHypergeometric (hφn w hw1)
      rw [gaussOperator_mul_comp (hPa w hw1) (hφa w hw1) hHa,
        show deriv P w = _ from deriv_affine_cpow (hslit w hw1),
        show deriv (deriv P) w = _ from deriv_deriv_affine_cpow (hslit w hw1),
        (hcub_phi_hasDerivAt (hq0 w hw1)).deriv, hφdd w hw1]
      have hode := gaussOperator_ordinaryHypergeometric (a := a) (b := a + 1 / 3) hc (hφn w hw1)
      simp only [gaussOperator] at hode
      simp only [hP, hφdef, hH] at hode ⊢
      generalize ₂F₁ a (a + 1 / 3) (2 * a + 2 / 3) (3 * t * w * (w - 1) / (1 + m * w) ^ 3) = h0
        at hode ⊢
      generalize deriv (₂F₁ a (a + 1 / 3) (2 * a + 2 / 3))
        (3 * t * w * (w - 1) / (1 + m * w) ^ 3) = h1 at hode ⊢
      generalize iteratedDeriv 2 (₂F₁ a (a + 1 / 3) (2 * a + 2 / 3))
        (3 * t * w * (w - 1) / (1 + m * w) ^ 3) = h2 at hode ⊢
      generalize (1 + m * w) ^ (-3 * a) = pw
      have := hcub_ode_alg (P := pw) ht (hq0 w hw1) (hr0 w hw1) hode
      linear_combination this
    · simp [hP, hφdef, hH, ordinaryHypergeometric_zero]
  exact (hG u (by simpa using hu)).symm



/-- A number with real part in `(0, 1)` is not an integer. -/
theorem hcub_not_int {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) : ∀ k : ℤ, s ≠ (k : ℂ) := by
  intro k hk
  have hr : s.re = (k : ℝ) := by rw [hk]; simp
  have a0 : (0 : ℝ) < k := hr ▸ h0
  have a1 : (k : ℝ) < 1 := hr ▸ h1
  have b0 : 0 < k := by exact_mod_cast a0
  have b1 : k < 1 := by exact_mod_cast a1
  omega

/-- A number with positive real part is not a nonpositive integer. -/
theorem hcub_not_neg_nat {s : ℂ} (h : 0 < s.re) : ∀ k : ℕ, s ≠ -(k : ℂ) := by
  intro k hk
  have := congrArg re hk; simp at this
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- `Γ(1/3) Γ(2/3) = 2π/√3`. -/
theorem hcub_gamma_third_mul : Gamma (1 / 3) * Gamma (2 / 3) = 2 * π / Real.sqrt 3 := by
  have h := Complex.Gamma_mul_Gamma_one_sub (1 / 3)
  rw [show (1 : ℂ) - 1 / 3 = 2 / 3 by norm_num] at h
  rw [h, show (π : ℂ) * (1 / 3) = ((π / 3 : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin,
    Real.sin_pi_div_three]
  have h3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  push_cast
  field_simp

/-- The connection of the bracket of DLMF 15.8.32 with the solution at `1`, for all `a`. -/
theorem hcub_conn {a w : ℂ} (hc : ∀ k : ℕ, 2 * a + 2 / 3 ≠ -(k : ℂ))
    (ha : ∀ k : ℕ, a + 1 / 3 ≠ -(k : ℂ)) (hw : ‖w‖ < 1) (hw1 : ‖1 - w‖ < 1) :
    ₂F₁ a (a + 1 / 3) (2 / 3) w / (Gamma (a + 2 / 3) * Gamma (2 / 3)) -
        w ^ (1 / 3 : ℂ) * ₂F₁ (a + 1 / 3) (a + 2 / 3) (4 / 3) w / (Gamma a * Gamma (4 / 3)) =
      Real.sqrt 3 * Gamma (a + 1 / 3) / (2 * π * Gamma (2 * a + 2 / 3)) *
        ₂F₁ a (a + 1 / 3) (2 * a + 2 / 3) (1 - w) := by
  have hwc : w ∈ cutPlane := by
    show 1 - w ∈ slitPlane
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    have : (1 - w).re = 1 - w.re := by simp
    linarith [abs_re_le_norm w, le_abs_self w.re]
  have hwc' : 1 - w ∈ cutPlane := by
    show 1 - (1 - w) ∈ slitPlane
    rw [sub_sub_cancel]
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    have : (1 - w).re = 1 - w.re := by simp
    linarith [abs_re_le_norm (1 - w), le_abs_self (1 - w).re]
  set F₁ : ℂ → ℂ := fun a => regularizedGaussHG a (a + 1 / 3) (2 / 3) w with hF₁
  set F₂ : ℂ → ℂ := fun a => regularizedGaussHG (a + 1 / 3) (a + 2 / 3) (4 / 3) w with hF₂
  set F₃ : ℂ → ℂ := fun a => regularizedGaussHG a (a + 1 / 3) (2 * a + 2 / 3) (1 - w) with hF₃
  set f : ℂ → ℂ := fun a => (1 / Gamma (a + 1 / 3)) *
    (F₁ a * (1 / Gamma (a + 2 / 3)) - w ^ (1 / 3 : ℂ) * F₂ a * (1 / Gamma a)) with hf
  set g : ℂ → ℂ := fun a => Real.sqrt 3 / (2 * π) * F₃ a with hg
  have hinvG : ∀ s : ℂ, Differentiable ℂ fun a : ℂ => 1 / Gamma (a + s) := fun s => by
    simpa [one_div, Function.comp_def] using
      Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const s)
  have hfa : AnalyticOnNhd ℂ f Set.univ := by
    have h1 := analyticOnNhd_regularizedGaussHG_comp (A := id) (B := fun a => a + 1 / 3)
      (C := fun _ => 2 / 3) differentiable_id (differentiable_id.add_const _)
      (differentiable_const _) hwc
    have h2 := analyticOnNhd_regularizedGaussHG_comp (A := fun a => a + 1 / 3)
      (B := fun a => a + 2 / 3) (C := fun _ => 4 / 3) (differentiable_id.add_const _)
      (differentiable_id.add_const _) (differentiable_const _) hwc
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
    refine ((hinvG _).differentiableOn).mul ?_
    refine (h1.differentiableOn.mul (hinvG _).differentiableOn).sub ?_
    refine ((differentiableOn_const _).mul h2.differentiableOn).mul ?_
    simpa using (hinvG 0).differentiableOn
  have hga : AnalyticOnNhd ℂ g Set.univ := by
    have h3 := analyticOnNhd_regularizedGaussHG_comp (A := id) (B := fun a => a + 1 / 3)
      (C := fun a => 2 * a + 2 / 3) differentiable_id (differentiable_id.add_const _)
      ((differentiable_id.const_mul _).add_const _) hwc'
    exact analyticOnNhd_const.mul h3
  have hGne : ∀ s : ℂ, 0 < s.re → Gamma s ≠ 0 := fun s hs => Complex.Gamma_ne_zero_of_re_pos hs
  have hc23 : ∀ k : ℤ, (2 / 3 : ℂ) ≠ (k : ℂ) := hcub_not_int (by norm_num) (by norm_num)
  have e1 : ∀ b : ℂ, ₂F₁ b (b + 1 / 3) (2 / 3) w = Gamma (2 / 3) * F₁ b := fun b => by
    simp only [hF₁]
    rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw,
      regularizedGaussHGFun_eq_div_Gamma (not_neg_nat_of_not_int hc23)]
    field_simp [hGne (2 / 3) (by norm_num)]
  have e2 : ∀ b : ℂ, ₂F₁ (b + 1 / 3) (b + 2 / 3) (4 / 3) w = Gamma (4 / 3) * F₂ b := fun b => by
    simp only [hF₂]
    rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw,
      regularizedGaussHGFun_eq_div_Gamma (hcub_not_neg_nat (by norm_num))]
    field_simp [hGne (4 / 3) (by norm_num)]
  have e3 : ∀ b : ℂ, (∀ k : ℕ, 2 * b + 2 / 3 ≠ -(k : ℂ)) →
      ₂F₁ b (b + 1 / 3) (2 * b + 2 / 3) (1 - w) = Gamma (2 * b + 2 / 3) * F₃ b := fun b hb => by
    simp only [hF₃]
    rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw1,
      regularizedGaussHGFun_eq_div_Gamma hb]
    have : Gamma (2 * b + 2 / 3) ≠ 0 := Complex.Gamma_ne_zero hb
    exact (mul_div_cancel₀ _ this).symm
  have hm13 : Gamma (-1 / 3) = -3 * Gamma (2 / 3) := by
    have h1 := Complex.Gamma_add_one (-1 / 3) (by norm_num)
    rw [show (-1 / 3 : ℂ) + 1 = 2 / 3 by norm_num] at h1
    rw [h1]; ring
  have h43 : Gamma (4 / 3) = Gamma (1 / 3) / 3 := by
    have h2 := Complex.Gamma_add_one (1 / 3) (by norm_num)
    rw [show (1 / 3 : ℂ) + 1 = 4 / 3 by norm_num] at h2
    rw [h2]; ring
  -- generic parameters
  have hgen : ∀ b ∈ Metric.ball (1 / 24 : ℂ) (1 / 48), f b = g b := by
    intro b hb
    have hb' : ‖b - 1 / 24‖ < 1 / 48 := by simpa [dist_eq_norm] using hb
    have hre := abs_re_le_norm (b - 1 / 24)
    rw [abs_le] at hre
    simp only [sub_re] at hre
    have hbre : (1 / 24 : ℂ).re = 1 / 24 := by norm_num
    rw [hbre] at hre
    have hcb : ∀ k : ℕ, 2 * b + 2 / 3 ≠ -(k : ℂ) := by
      intro k hk
      have := congrArg re hk; simp at this
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have he : ∀ k : ℤ, 2 / 3 - b - (b + 1 / 3) ≠ (k : ℂ) := hcub_not_int
      (by simp; linarith) (by simp; linarith)
    have hconn := one_first_connection_zero (a := b) (b := b + 1 / 3) hc23 he hw hw1
    simp only [oneFirst, zeroSecond] at hconn
    rw [show b + (b + 1 / 3) - 2 / 3 + 1 = 2 * b + 2 / 3 by ring,
      show (1 : ℂ) - 2 / 3 = 1 / 3 by norm_num, show b - 2 / 3 + 1 = b + 1 / 3 by ring,
      show b + 1 / 3 - 2 / 3 + 1 = b + 2 / 3 by ring, show (2 : ℂ) / 3 - 1 = -1 / 3 by norm_num,
      show (2 : ℂ) - 2 / 3 = 4 / 3 by norm_num, e1, e2, e3 b hcb, hm13, h43] at hconn
    have hG1 := hGne b (by linarith)
    have hG2 := hGne (b + 1 / 3) (by simp; linarith)
    have hG3 := hGne (b + 2 / 3) (by simp; linarith)
    have hG4 := hGne (2 * b + 2 / 3) (by simp; linarith)
    have hF3 : F₃ b = Gamma (1 / 3) * Gamma (2 / 3) *
        (F₁ b / (Gamma (b + 1 / 3) * Gamma (b + 2 / 3)) -
          w ^ (1 / 3 : ℂ) * F₂ b / (Gamma b * Gamma (b + 1 / 3))) := by
      apply mul_left_cancel₀ hG4
      rw [hconn]
      ring
    simp only [hf, hg]
    rw [hF3, hcub_gamma_third_mul]
    have h3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  have hfg : Set.EqOn f g Set.univ := by
    refine hfa.eqOn_of_preconnected_of_eventuallyEq hga isPreconnected_univ
      (Set.mem_univ (1 / 24 : ℂ)) ?_
    filter_upwards [Metric.ball_mem_nhds (1 / 24 : ℂ) (by norm_num : (0 : ℝ) < 1 / 48)] with b hb
    exact hgen b hb
  have hfa' := hfg (Set.mem_univ a)
  simp only [hf, hg] at hfa'
  have hGa : Gamma (a + 1 / 3) ≠ 0 := Complex.Gamma_ne_zero ha
  rw [e1, e2, e3 a hc]
  have hG23 := hGne (2 / 3) (by norm_num)
  have hG43 := hGne (4 / 3) (by norm_num)
  have hGc : Gamma (2 * a + 2 / 3) ≠ 0 := Complex.Gamma_ne_zero hc
  have key : F₁ a * (1 / Gamma (a + 2 / 3)) - w ^ (1 / 3 : ℂ) * F₂ a * (1 / Gamma a) =
      Gamma (a + 1 / 3) * (Real.sqrt 3 / (2 * π) * F₃ a) := by
    rw [← hfa', ← mul_assoc, mul_one_div_cancel hGa, one_mul]
  calc Gamma (2 / 3) * F₁ a / (Gamma (a + 2 / 3) * Gamma (2 / 3)) -
        w ^ (1 / 3 : ℂ) * (Gamma (4 / 3) * F₂ a) / (Gamma a * Gamma (4 / 3))
      = F₁ a * (1 / Gamma (a + 2 / 3)) - w ^ (1 / 3 : ℂ) * F₂ a * (1 / Gamma a) := by
        field_simp
    _ = _ := by
        rw [key]
        generalize Gamma (2 * a + 2 / 3) = G at hGc ⊢
        field_simp



/-- `√3 > 0`. -/
theorem hcub_sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

/-- `(√3)² = 3`. -/
theorem hcub_sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- `|u + ω|² - |1 + ωu|² = 2√3 Im u` for `ω = e^{2πi/3}`. -/
theorem hcub_normSq_diff (u : ℂ) :
    normSq (u + (-1 + (Real.sqrt 3 : ℂ) * I) / 2) =
      normSq (1 + (-1 + (Real.sqrt 3 : ℂ) * I) / 2 * u) + 2 * Real.sqrt 3 * u.im := by
  simp only [normSq_apply, add_re, add_im, mul_re, mul_im, div_re, div_im, ofReal_re, ofReal_im,
    I_re, I_im, one_re, one_im, neg_re, neg_im]
  norm_num
  ring_nf
  rw [hcub_sqrt3_sq]
  ring

/-- Comparison of norms through `normSq`. -/
theorem hcub_norm_lt_of_normSq {z w : ℂ} (h : normSq z < normSq w) : ‖z‖ < ‖w‖ := by
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at h
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h

/-- For `Im u > 0`, `|1 + ωu| < |u + ω|`. -/
theorem hcub_norm_lt_of_im_pos {u : ℂ} (hu : 0 < u.im) :
    ‖1 + (-1 + (Real.sqrt 3 : ℂ) * I) / 2 * u‖ < ‖u + (-1 + (Real.sqrt 3 : ℂ) * I) / 2‖ := by
  apply hcub_norm_lt_of_normSq
  rw [hcub_normSq_diff]
  have := hcub_sqrt3_pos
  nlinarith

/-- Three-way exponentials: `e^{iπ/3}`, `e^{2πi/3}`, `e^{4πi/3}` through `t = √3 i`. -/
theorem hcub_exp_third : exp (Real.pi * I / 3) = (1 + (Real.sqrt 3 : ℂ) * I) / 2 := by
  rw [show (Real.pi : ℂ) * I / 3 = ((π / 3 : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring

theorem hcub_exp_two_third : exp (2 * Real.pi * I / 3) = (-1 + (Real.sqrt 3 : ℂ) * I) / 2 := by
  rw [show 2 * (Real.pi : ℂ) * I / 3 = ((π - π / 3 : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  push_cast; ring

theorem hcub_exp_four_third : exp (4 * Real.pi * I / 3) = (-1 - (Real.sqrt 3 : ℂ) * I) / 2 := by
  rw [show 4 * (Real.pi : ℂ) * I / 3 = ((π / 3 + π : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, Real.cos_add_pi, Real.sin_add_pi, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  push_cast; ring

/-- Principal cube root near `1`: if `‖y - 1‖ < 1/5` then `(y³)^{1/3} = y`. -/
theorem hcub_cube_root {y : ℂ} (hy : ‖y - 1‖ < 1 / 5) : (y ^ 3) ^ (1 / 3 : ℂ) = y := by
  have him : |y.im| < 1 / 5 := by
    have := abs_im_le_norm (y - 1); simp at this; linarith
  have hre : 4 / 5 < y.re := by
    have := abs_re_le_norm (y - 1); simp at this
    linarith [neg_abs_le (y.re - 1)]
  have hn : 4 / 5 < ‖y‖ := lt_of_lt_of_le hre (le_trans (le_abs_self _) (abs_re_le_norm y))
  have hs : |y.im / ‖y‖| ≤ 1 / 2 := by
    rw [abs_div, abs_norm, div_le_iff₀ (by linarith)]; linarith
  have harg := arg_of_re_nonneg (x := y) (by linarith)
  have h6 : Real.arcsin (1 / 2) = π / 6 := by
    rw [← Real.sin_pi_div_six, Real.arcsin_sin] <;> linarith [Real.pi_pos]
  rw [abs_le] at hs
  have hup : arg y ≤ π / 6 := by
    rw [harg, ← h6]; exact Real.arcsin_le_arcsin hs.2
  have hlo : -(π / 6) ≤ arg y := by
    rw [harg, ← h6, ← Real.arcsin_neg]; exact Real.arcsin_le_arcsin (by linarith)
  have := pow_cpow_nat_inv (x := y) (n := 3) (by norm_num) (by push_cast; linarith [Real.pi_pos])
    (by push_cast; linarith [Real.pi_pos])
  simpa using this

/-- The cubic map sends the disk `|u| < 1/10` into the unit disk. -/
theorem hcub_phi_norm {u : ℂ} (hu : ‖u‖ < 1 / 10) :
    ‖3 * ((Real.sqrt 3 : ℂ) * I) * u * (u - 1) / (1 + (-1 - (Real.sqrt 3 : ℂ) * I) / 2 * u) ^ 3‖
      < 1 := by
  have hm : ‖(-1 - (Real.sqrt 3 : ℂ) * I) / 2‖ = 1 := by
    have := hcub_norm_m (-1) (Or.inr rfl); convert this using 2; push_cast; ring
  have h1 : 9 / 10 ≤ ‖1 + (-1 - (Real.sqrt 3 : ℂ) * I) / 2 * u‖ := by
    linarith [hcub_one_add_mul_norm_ge (u := u) hm]
  have h2 : ‖u - 1‖ ≤ 11 / 10 := by
    have := norm_sub_le u 1; rw [norm_one] at this; linarith
  have h3 : ‖(3 : ℂ)‖ * ‖(Real.sqrt 3 : ℂ) * I‖ ≤ 21 / 4 := by
    rw [hcub_norm_t]; norm_num; linarith [hcub_sqrt3_lt]
  simp only [norm_div, norm_mul, norm_pow] at h3 ⊢
  rw [div_lt_one (by positivity)]
  have hu0 := norm_nonneg u
  calc ‖(3 : ℂ)‖ * (‖(Real.sqrt 3 : ℂ)‖ * ‖I‖) * ‖u‖ * ‖u - 1‖ ≤ 21 / 4 * (1 / 10) * (11 / 10) := by
        gcongr
    _ < (9 / 10) ^ 3 := by norm_num
    _ ≤ _ := by gcongr

/-- The algebraic identities behind the cubic change of variables (`t² = -3`). -/
theorem hcub_alg {t u : ℂ} (ht : t ^ 2 = -3) (hq : 1 + (-1 - t) / 2 * u ≠ 0) :
    ((-1 - t) / 2 * ((-1 - t) / 2 * (1 + (-1 + t) / 2 * u) / (u + (-1 + t) / 2))) ^ 3 =
        ((-1 - t) / 2 * (1 + (-1 + t) / 2 * u) / (u + (-1 + t) / 2)) ^ 3 ∧
      (-1 - t) / 2 * ((-1 - t) / 2 * (1 + (-1 + t) / 2 * u) / (u + (-1 + t) / 2)) - 1 =
        u * ((-1 - t) / 2 - 1) / (u + (-1 + t) / 2) ∧
      1 - ((-1 - t) / 2 * (1 + (-1 + t) / 2 * u) / (u + (-1 + t) / 2)) ^ 3 =
        3 * t * u * (u - 1) / (1 + (-1 - t) / 2 * u) ^ 3 := by
  obtain ⟨h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hcub_tpow ht
  have hω : u + (-1 + t) / 2 = (-1 + t) / 2 * (1 + (-1 - t) / 2 * u) := by
    linear_combination (u / 4) * ht
  have hω1 : (-1 + t) / 2 ≠ 0 := by
    intro h
    have : t = 1 := by linear_combination 2 * h
    rw [this] at ht; norm_num at ht
  have hω0 : u + (-1 + t) / 2 ≠ 0 := by rw [hω]; exact mul_ne_zero hω1 hq
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_pow]
    have : ((-1 - t) / 2) ^ 3 = 1 := by linear_combination (-3 / 8) * ht - (1 / 8) * h3
    rw [this, one_mul]
  · generalize hW : u + (-1 + t) / 2 = W at hω0 ⊢
    field_simp
    subst hW
    ring_nf
    simp only [ht, h3]
    ring_nf
  · rw [hω]
    generalize hQ : 1 + (-1 - t) / 2 * u = Q at hq ⊢
    field_simp
    subst hQ
    ring_nf
    simp only [ht, h3, h4, h5, h6]
    ring_nf

/-- **The connection identity in the cubic variable.** For `Im u > 0`, `|u| < 1`, with
`ω = e^{2πi/3}` and `Z = ω²(1+ωu)/(u+ω)` (so that `Z³` lies in the unit disk), the bracket of
DLMF 15.8.32 at `z = 1/Z` equals `√3 Γ(a+1/3)/(2π Γ(2a+2/3)) (1+ω²u)^{3a} F(a+1/3, 3a; 2a+2/3; u)`. -/
theorem hcub_main {a : ℂ} (hc : ∀ k : ℕ, 2 * a + 2 / 3 ≠ -(k : ℂ))
    (ha : ∀ k : ℕ, a + 1 / 3 ≠ -(k : ℂ)) {u : ℂ} (hu0 : 0 < u.im) (hu1 : ‖u‖ < 1) :
    ₂F₁ a (a + 1 / 3) (2 / 3) (((-1 - (Real.sqrt 3 : ℂ) * I) / 2 *
          (1 + (-1 + (Real.sqrt 3 : ℂ) * I) / 2 * u) / (u + (-1 + (Real.sqrt 3 : ℂ) * I) / 2)) ^ 3) /
        (Gamma (a + 2 / 3) * Gamma (2 / 3)) +
      exp (Real.pi * I / 3) * ((-1 - (Real.sqrt 3 : ℂ) * I) / 2 *
          (1 + (-1 + (Real.sqrt 3 : ℂ) * I) / 2 * u) / (u + (-1 + (Real.sqrt 3 : ℂ) * I) / 2)) /
        (Gamma a * Gamma (4 / 3)) *
        ₂F₁ (a + 1 / 3) (a + 2 / 3) (4 / 3) (((-1 - (Real.sqrt 3 : ℂ) * I) / 2 *
          (1 + (-1 + (Real.sqrt 3 : ℂ) * I) / 2 * u) / (u + (-1 + (Real.sqrt 3 : ℂ) * I) / 2)) ^ 3) =
      Real.sqrt 3 * Gamma (a + 1 / 3) / (2 * π * Gamma (2 * a + 2 / 3)) *
        (1 + (-1 - (Real.sqrt 3 : ℂ) * I) / 2 * u) ^ (3 * a) *
        ₂F₁ (a + 1 / 3) (3 * a) (2 * a + 2 / 3) u := by
  set t : ℂ := (Real.sqrt 3 : ℂ) * I with htdef
  have ht : t ^ 2 = -3 := hcub_t_sq
  have hm : ‖(-1 - t) / 2‖ = 1 := by
    have := hcub_norm_m (-1) (Or.inr rfl); rw [← htdef] at this; convert this using 2; push_cast; ring
  have hωn : ‖(-1 + t) / 2‖ = 1 := by
    have := hcub_norm_m 1 (Or.inl rfl); rw [← htdef] at this; convert this using 2; push_cast; ring
  set ω : ℂ := (-1 + t) / 2 with hωdef
  set m : ℂ := (-1 - t) / 2 with hmdef
  set Zf : ℂ → ℂ := fun v => m * (1 + ω * v) / (v + ω) with hZf
  set β : ℂ := Real.sqrt 3 * Gamma (a + 1 / 3) / (2 * π * Gamma (2 * a + 2 / 3)) with hβ
  set Bf : ℂ → ℂ := fun v => ₂F₁ a (a + 1 / 3) (2 / 3) (Zf v ^ 3) / (Gamma (a + 2 / 3) * Gamma (2 / 3)) +
      exp (Real.pi * I / 3) * Zf v / (Gamma a * Gamma (4 / 3)) *
        ₂F₁ (a + 1 / 3) (a + 2 / 3) (4 / 3) (Zf v ^ 3) with hBf
  set Rf : ℂ → ℂ := fun v => β * (1 + m * v) ^ (3 * a) * ₂F₁ (a + 1 / 3) (3 * a) (2 * a + 2 / 3) v
    with hRf
  set Ω : Set ℂ := {v : ℂ | 0 < v.im} ∩ Metric.ball 0 1 with hΩ
  have hΩo : IsOpen Ω := (isOpen_lt continuous_const continuous_im).inter Metric.isOpen_ball
  have hΩc : IsPreconnected Ω := (Convex.inter (convex_halfSpace_im_gt (r := 0)) (convex_ball (0 : ℂ) 1)).isPreconnected
  have hmem : ∀ v ∈ Ω, 0 < v.im ∧ ‖v‖ < 1 := fun v hv => ⟨hv.1, by simpa using hv.2⟩
  have hlt : ∀ v ∈ Ω, ‖1 + ω * v‖ < ‖v + ω‖ := fun v hv => hcub_norm_lt_of_im_pos (hmem v hv).1
  have hden : ∀ v ∈ Ω, v + ω ≠ 0 := fun v hv h => by
    have := hlt v hv; rw [h, norm_zero] at this; exact absurd this (not_lt.mpr (norm_nonneg _))
  have hZn : ∀ v ∈ Ω, ‖Zf v ^ 3‖ < 1 := by
    intro v hv
    have h1 : ‖Zf v‖ < 1 := by
      simp only [hZf, norm_div, norm_mul, hm, one_mul]
      rw [div_lt_one (norm_pos_iff.mpr (hden v hv))]
      exact hlt v hv
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) h1 (by norm_num)
  have hZa : ∀ v ∈ Ω, AnalyticAt ℂ Zf v := fun v hv =>
    ((analyticAt_const.mul (analyticAt_const.add (analyticAt_const.mul analyticAt_id))).div
      (analyticAt_id.add analyticAt_const)) (hden v hv)
  have hBa : AnalyticOnNhd ℂ Bf Ω := by
    intro v hv
    have hZ3 : AnalyticAt ℂ (fun v => Zf v ^ 3) v := (hZa v hv).pow 3
    have hF1 := (analyticAt_ordinaryHypergeometric (a := a) (b := a + 1 / 3) (c := 2 / 3)
      (hZn v hv)).comp (f := fun w => Zf w ^ 3) hZ3
    have hF2 := (analyticAt_ordinaryHypergeometric (a := a + 1 / 3) (b := a + 2 / 3) (c := 4 / 3)
      (hZn v hv)).comp (f := fun w => Zf w ^ 3) hZ3
    exact (hF1.div_const).add (((analyticAt_const.mul (hZa v hv)).div_const).mul hF2)
  have hslit : ∀ v : ℂ, ‖v‖ < 1 → 1 + m * v ∈ slitPlane := fun v hv =>
    mem_slitPlane_iff.mpr (Or.inl (hcub_one_add_mul_re_pos hm hv))
  have hRa : AnalyticOnNhd ℂ Rf Ω := by
    intro v hv
    have hP : AnalyticAt ℂ (fun v => (1 + m * v) ^ (3 * a)) v :=
      (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).cpow analyticAt_const
        (hslit v (hmem v hv).2)
    exact (analyticAt_const.mul hP).mul (analyticAt_ordinaryHypergeometric (hmem v hv).2)
  -- the identity near the origin
  have hloc : ∀ v : ℂ, 0 < v.im → ‖v‖ < 1 / 10 → Bf v = Rf v := by
    intro v hv0 hv1
    have hvΩ : v ∈ Ω := ⟨hv0, by simpa using (show ‖v‖ < 1 by linarith)⟩
    have hq : 1 + m * v ≠ 0 := slitPlane_ne_zero (hslit v (by linarith))
    obtain ⟨A1, A2, A3⟩ := hcub_alg (u := v) ht hq
    have hy : ‖m * Zf v - 1‖ < 1 / 5 := by
      simp only [hZf]
      rw [A2, norm_div, norm_mul]
      have hm1 : ‖m - 1‖ = Real.sqrt 3 := by
        rw [hmdef, htdef, show (-1 - (Real.sqrt 3 : ℂ) * I) / 2 - 1 =
          ⟨-3 / 2, -(Real.sqrt 3 / 2)⟩ by apply Complex.ext <;> simp <;> ring]
        rw [Complex.norm_eq_sqrt_sq_add_sq]
        congr 1
        simp only
        nlinarith [hcub_sqrt3_sq]
      have hω9 : 9 / 10 ≤ ‖v + ω‖ := by
        have := norm_sub_norm_le ω (-v)
        rw [norm_neg, hωn, sub_neg_eq_add, add_comm] at this; linarith
      rw [hm1, div_lt_iff₀ (by linarith)]
      have := hcub_sqrt3_lt
      calc ‖v‖ * Real.sqrt 3 ≤ 1 / 10 * (7 / 4) := by gcongr
        _ < 1 / 5 * (9 / 10) := by norm_num
        _ ≤ _ := by gcongr
    have hroot : (Zf v ^ 3) ^ (1 / 3 : ℂ) = m * Zf v := by
      rw [← hcub_cube_root hy]; congr 1; exact A1.symm
    have hexp : exp (Real.pi * I / 3) = -m := by rw [hcub_exp_third, hmdef, htdef]; ring
    have hw1 : ‖1 - Zf v ^ 3‖ < 1 := by
      simp only [hZf]; rw [A3]; exact hcub_phi_norm hv1
    have hconn := hcub_conn (w := Zf v ^ 3) hc ha (hZn v hvΩ) hw1
    rw [hroot] at hconn
    have hcub := hcub_cubic hc (u := v) hv1
    rw [← htdef, ← hmdef] at hcub
    simp only [hZf] at hconn
    rw [A3, ← hβ] at hconn
    simp only [hBf, hRf]
    rw [hexp, hcub]
    have hP0 : (1 + m * v) ^ (3 * a) * (1 + m * v) ^ (-3 * a) = 1 := by
      rw [show -3 * a = -(3 * a) by ring, cpow_neg, mul_inv_cancel₀]
      exact (cpow_ne_zero_iff.mpr (Or.inl hq))
    linear_combination hconn + (-β * ₂F₁ a (a + 1 / 3) (2 * a + 2 / 3)
      (3 * t * v * (v - 1) / (1 + m * v) ^ 3)) * hP0
  -- continuation to `Ω`
  set u₀ : ℂ := I / 20 with hu₀
  have hu₀Ω : u₀ ∈ Ω := ⟨by simp [hu₀], by simp [hu₀]; norm_num⟩
  have hev : Bf =ᶠ[𝓝 u₀] Rf := by
    have hU : IsOpen ({v : ℂ | 0 < v.im} ∩ Metric.ball 0 (1 / 10)) :=
      (isOpen_lt continuous_const continuous_im).inter Metric.isOpen_ball
    filter_upwards [hU.mem_nhds ⟨by simp [hu₀], by simp [hu₀]; norm_num⟩] with v hv
    exact hloc v hv.1 (by simpa using hv.2)
  have hEq := hBa.eqOn_of_preconnected_of_eventuallyEq hRa hΩc hu₀Ω hev
  have := hEq (show u ∈ Ω from ⟨hu0, by simpa using hu1⟩)
  simpa only [hBf, hRf, hZf, hβ] using this

/-- The point `u = 1/ζ` of DLMF 15.8.32 for real `z = X`, in terms of `t² = -3`. -/
theorem hcub_seg_u {t X : ℂ} (ht : t ^ 2 = -3) (hω : -1 + t ≠ 0) (h1 : 1 - X ≠ 0)
    (hxm : 2 * X + 1 + t ≠ 0) :
    1 / ((-1 + t) / 2 * (1 - X) / (X - (-1 - t) / 2)) = 1 / 2 - t / 2 * (X + 1) / (1 - X) := by
  have hxm' : X - (-1 - t) / 2 ≠ 0 := by
    intro h; apply hxm; linear_combination 2 * h
  rw [one_div_div, div_eq_iff (mul_ne_zero (div_ne_zero hω two_ne_zero) h1)]
  field_simp
  linear_combination (X + 1) * ht

/-- At `u = 1/ζ`, the point `ω²(1+ωu)/(u+ω)` is `1/X`. -/
theorem hcub_seg_Z {t X : ℂ} (ht : t ^ 2 = -3) (h1 : 1 - X ≠ 0) (hX : X ≠ 0) :
    (-1 - t) / 2 * (1 + (-1 + t) / 2 * (1 / 2 - t / 2 * (X + 1) / (1 - X))) /
      ((1 / 2 - t / 2 * (X + 1) / (1 - X)) + (-1 + t) / 2) = X⁻¹ := by
  have hden : (1 / 2 - t / 2 * (X + 1) / (1 - X)) + (-1 + t) / 2 = -t * X / (1 - X) := by
    field_simp; ring
  rw [hden]
  have ht0 : t ≠ 0 := by rintro rfl; norm_num at ht
  rw [div_eq_iff (div_ne_zero (mul_ne_zero (neg_ne_zero.mpr ht0) hX) h1)]
  have h3 : t ^ 3 = -3 * t := by rw [pow_succ, ht]
  field_simp
  ring_nf
  simp only [ht, h3]
  ring_nf

/-- The algebraic form of the power identity on the segment. -/
theorem hcub_seg_rel {t X : ℂ} (ht : t ^ 2 = -3) (h1 : 1 - X ≠ 0) (hX : X ≠ 0)
    (hu : 1 / 2 - t / 2 * (X + 1) / (1 - X) ≠ 0) :
    (1 - X ^ 3) * (1 + (-1 - t) / 2 * (1 / 2 - t / 2 * (X + 1) / (1 - X))) ^ 3 / (-X) ^ 3 =
      3 * t * (1 - 1 / (1 / 2 - t / 2 * (X + 1) / (1 - X))) *
        (1 / 2 - t / 2 * (X + 1) / (1 - X)) ^ 2 := by
  obtain ⟨h3, h4, h5, h6, -⟩ := hcub_tpow ht
  have hu' : (1 - X) - t * (X + 1) ≠ 0 := by
    intro h; apply hu; field_simp; linear_combination h
  have hrw : 1 / 2 - t / 2 * (X + 1) / (1 - X) = ((1 - X) - t * (X + 1)) / (2 * (1 - X)) := by
    field_simp
  rw [hrw]
  field_simp
  ring_nf
  simp only [ht, h3, h4, h5, h6]
  ring_nf

/-- The power bookkeeping of DLMF 15.8.32 on the segment `u = 1/2 + iY`. -/
theorem hcub_cpow {a : ℂ} {x : ℝ} (hx : x < -1) {u : ℂ} (hre : u.re = 1 / 2) (him : 0 < u.im)
    (hn : ‖u‖ < 1)
    (hrel : (1 - (x : ℂ) ^ 3) * (1 + (-1 - (Real.sqrt 3 : ℂ) * I) / 2 * u) ^ 3 / (-(x : ℂ)) ^ 3 =
      3 * ((Real.sqrt 3 : ℂ) * I) * (1 - 1 / u) * u ^ 2) :
    (1 - (x : ℂ) ^ 3) ^ a / (-(x : ℂ)) ^ (3 * a) * Real.sqrt 3 *
        (1 + (-1 - (Real.sqrt 3 : ℂ) * I) / 2 * u) ^ (3 * a) =
      (3 : ℂ) ^ (3 * a / 2 + 1 / 2) * exp (a * Real.pi * I / 2) * (1 - 1 / u) ^ a /
        (-(1 / u)) ^ (2 * a) := by
  set m : ℂ := (-1 - (Real.sqrt 3 : ℂ) * I) / 2 with hmdef
  have hm : ‖m‖ = 1 := by
    have := hcub_norm_m (-1) (Or.inr rfl); convert this using 2; push_cast; ring
  set X : ℂ := (x : ℂ) with hX
  have hu0 : u ≠ 0 := by rintro rfl; simp at him
  have hpos1 : (1 - X ^ 3) = ((1 - x ^ 3 : ℝ) : ℂ) := by push_cast; rfl
  have hpos2 : -X = ((-x : ℝ) : ℂ) := by push_cast; rfl
  have hr2 : (0 : ℝ) < -x := by linarith
  have hr1 : (0 : ℝ) < 1 - x ^ 3 := by
    have := mul_pos hr2 (pow_pos hr2 2); nlinarith
  have hA : 1 - X ^ 3 ≠ 0 := by rw [hpos1]; exact_mod_cast hr1.ne'
  have hB : -X ≠ 0 := by rw [hpos2]; exact_mod_cast hr2.ne'
  have hCre : 0 < (1 + m * u).re := hcub_one_add_mul_re_pos hm hn
  have hC : 1 + m * u ≠ 0 := fun h => by rw [h, zero_re] at hCre; exact lt_irrefl _ hCre
  have hCim : (1 + m * u).im < 0 := by
    simp [hmdef, hre]; nlinarith [hcub_sqrt3_pos]
  have hns : 0 < normSq u := normSq_pos.mpr hu0
  have hζre : 0 < (1 / u).re := by rw [one_div, inv_re, hre]; positivity
  have hζim : (1 / u).im < 0 := by
    rw [one_div, inv_im]; exact div_neg_of_neg_of_pos (neg_lt_zero.mpr him) hns
  have hD : 1 - 1 / u ≠ 0 := fun h => by
    have := congrArg im h; simp only [sub_im, one_im, zero_im] at this; linarith
  have hE : -(1 / u) ≠ 0 := neg_ne_zero.mpr (one_div_ne_zero hu0)
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  -- the logarithmic identity
  set L₀ : ℂ := log (1 - X ^ 3) - 3 * log (-X) + 3 * log (1 + m * u) with hL₀
  set R₀ : ℂ := log 3 * (3 / 2) + Real.pi * I / 2 + log (1 - 1 / u) - 2 * log (-(1 / u)) with hR₀
  have hsq : ((Real.sqrt 3 : ℝ) : ℂ) = exp (log 3 * (1 / 2)) := by
    rw [← cpow_def_of_ne_zero h3, Real.sqrt_eq_rpow, ofReal_cpow (by norm_num)]
    push_cast; ring_nf
  have hexpL : exp L₀ = (1 - X ^ 3) * (1 + m * u) ^ 3 / (-X) ^ 3 := by
    rw [hL₀, exp_add, exp_sub, exp_log hA, show (3 : ℂ) * log (-X) = ((3 : ℕ) : ℂ) * log (-X) by
      norm_num, exp_nat_mul, exp_log hB, show (3 : ℂ) * log (1 + m * u) =
      ((3 : ℕ) : ℂ) * log (1 + m * u) by norm_num, exp_nat_mul, exp_log hC]
    ring
  have hexpR : exp R₀ = 3 * ((Real.sqrt 3 : ℂ) * I) * (1 - 1 / u) * u ^ 2 := by
    rw [hR₀, exp_sub, exp_add, exp_add, exp_log hD, show (2 : ℂ) * log (-(1 / u)) =
      ((2 : ℕ) : ℂ) * log (-(1 / u)) by norm_num, exp_nat_mul, exp_log hE,
      show log 3 * (3 / 2) = log 3 + log 3 * (1 / 2) by ring, exp_add, exp_log h3, ← hsq,
      show (Real.pi : ℂ) * I / 2 = ((Real.pi / 2 : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
      ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
    field_simp
    push_cast
    ring
  have key : L₀ = R₀ := by
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.mp (hexpL.trans (hrel.trans hexpR.symm))
    have him' := congrArg im hn
    have hA0 : arg (1 - X ^ 3) = 0 := by rw [hpos1]; exact arg_ofReal_of_nonneg hr1.le
    have hB0 : arg (-X) = 0 := by rw [hpos2]; exact arg_ofReal_of_nonneg hr2.le
    have h30 : arg (3 : ℂ) = 0 := by
      rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num]; exact arg_ofReal_of_nonneg (by norm_num)
    simp only [hL₀, hR₀, add_im, sub_im, mul_im, log_im, hA0, hB0, h30, re_ofNat, im_ofNat,
      ofReal_re, ofReal_im, I_re, I_im, div_ofNat_im, div_ofNat_re, intCast_re, intCast_im,
      mul_re] at him'
    have hc1 : arg (1 + m * u) < 0 := arg_neg_iff.mpr hCim
    have hc2 : -(π / 2) < arg (1 + m * u) := by
      have := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hCre); rw [abs_lt] at this; exact this.1
    have hd1 : 0 ≤ arg (1 - 1 / u) := arg_nonneg_iff.mpr (by
      simp only [sub_im, one_im]; linarith)
    have hd2 : arg (1 - 1 / u) ≤ π := arg_le_pi _
    have he1 : π / 2 < arg (-(1 / u)) := by
      rw [arg_neg_eq_arg_add_pi_of_im_neg hζim]
      have := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hζre); rw [abs_lt] at this; linarith
    have he2 : arg (-(1 / u)) ≤ π := arg_le_pi _
    have hn1 : (-1 : ℝ) < n := by
      by_contra h; have h := not_lt.mp h
      nlinarith [Real.pi_pos]
    have hn2 : (n : ℝ) < 1 := by
      by_contra h; have h := not_lt.mp h
      nlinarith [Real.pi_pos]
    have hn0 : n = 0 := by
      have a1 : (-1 : ℤ) < n := by exact_mod_cast hn1
      have a2 : n < 1 := by exact_mod_cast hn2
      omega
    rw [hn, hn0]; simp
  have e1 : (1 - X ^ 3) ^ a / (-X) ^ (3 * a) * Real.sqrt 3 * (1 + m * u) ^ (3 * a) =
      exp (log (1 - X ^ 3) * a - log (-X) * (3 * a) + log 3 * (1 / 2) +
        log (1 + m * u) * (3 * a)) := by
    rw [cpow_def_of_ne_zero hA, cpow_def_of_ne_zero hB, cpow_def_of_ne_zero hC, hsq, exp_add,
      exp_add, exp_sub]
  have e2 : (3 : ℂ) ^ (3 * a / 2 + 1 / 2) * exp (a * Real.pi * I / 2) * (1 - 1 / u) ^ a /
        (-(1 / u)) ^ (2 * a) =
      exp (log 3 * (3 * a / 2 + 1 / 2) + a * Real.pi * I / 2 + log (1 - 1 / u) * a -
        log (-(1 / u)) * (2 * a)) := by
    rw [cpow_def_of_ne_zero h3, cpow_def_of_ne_zero hD, cpow_def_of_ne_zero hE, exp_sub,
      exp_add, exp_add]
  rw [e1, e2]
  congr 1
  linear_combination a * key

end DLMF.Hypergeometric
