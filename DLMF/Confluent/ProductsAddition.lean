/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Whittaker
public import DLMF.Confluent.MobiusTaylor

/-!
# Products and addition theorems (DLMF §§13.12, 13.13, 13.25, 13.26)

For U and Whittaker addition formulas, `Re x > 0` keeps the Taylor domain
on the principal branch. Downward shifts of ordinary M exclude integer denominator
parameters: the old formulas at `b = 1` discarded nonzero limiting terms as `0 * 0`.
The product proofs use the Mathlib contributors’ zero-derivative constancy and
complex-power calculus, together with the local Kummer contiguous relations.
First-parameter additions use the unit-disk Taylor expansions in `MobiusTaylor`.
Their four Whittaker adapters check the principal powers with positive-real-part
ratios, retaining the original convergence and exceptional-parameter hypotheses.
-/

@[expose] public section

open Complex
open scoped Real Topology
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- A disk centered in the right half-plane, with radius the distance to zero,
avoids the nonpositive real axis. -/
theorem ball_norm_subset_slitPlane {x : ℂ} (hx : 0 < x.re) :
    Metric.ball x ‖x‖ ⊆ slitPlane := by
  intro w hw
  rw [mem_slitPlane_iff]
  by_contra! h
  have hn : ‖w - x‖ < ‖x‖ := by simpa only [Metric.mem_ball, dist_eq] using hw
  have hs := (sq_lt_sq₀ (norm_nonneg (w - x)) (norm_nonneg x)).mpr hn
  rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq] at hs
  simp only [normSq_apply, sub_re, sub_im, h.2, zero_sub, neg_mul_neg] at hs
  nlinarith [mul_nonpos_of_nonpos_of_nonneg h.1 hx.le, sq_nonneg w.re]

/-- Principal powers multiply without a branch correction when both factors
lie in the right half-plane. -/
theorem cpow_mul_of_re_pos {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (s : ℂ) :
    (u * v) ^ s = u ^ s * v ^ s := by
  have hu0 := slitPlane_ne_zero (Or.inl hu : u ∈ slitPlane)
  have hv0 := slitPlane_ne_zero (Or.inl hv : v ∈ slitPlane)
  have hua := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu))
  have hva := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hv))
  rw [cpow_def_of_ne_zero (mul_ne_zero hu0 hv0), cpow_def_of_ne_zero hu0,
    cpow_def_of_ne_zero hv0, log_mul hu0 hv0 ⟨by linarith, by linarith⟩, ← exp_add]
  congr 1; ring

/-- The power factor in the downward-parameter Taylor formulas. -/
theorem cpow_add_shift_factor {x y : ℂ} (hx : 0 < x.re) (hy : ‖y‖ < ‖x‖)
    (b : ℂ) (n : ℕ) :
    (x + y) ^ (1 - b) * x ^ (b - n - 1) = ((x + y) / x) ^ (1 - b) / x ^ n := by
  have hx0 := slitPlane_ne_zero (Or.inl hx : x ∈ slitPlane)
  have hdiv : ‖y / x‖ < 1 := by
    rw [norm_div]; exact (div_lt_one (norm_pos_iff.mpr hx0)).mpr hy
  have hr : 0 < ((x + y) / x).re := by
    have h := re_le_norm (-(y / x))
    simp only [neg_re, norm_neg] at h
    rw [add_div, div_self hx0]
    simp only [add_re, one_re]
    linarith
  have hp : (x + y) ^ (1 - b) = ((x + y) / x) ^ (1 - b) * x ^ (1 - b) := by
    rw [← cpow_mul_of_re_pos hr hx, div_mul_cancel₀ _ hx0]
  rw [hp, mul_assoc, ← cpow_add _ _ hx0,
    show 1 - b + (b - (n : ℂ) - 1) = -(n : ℂ) by ring, cpow_neg, cpow_natCast]
  rfl

/-- For `‖y‖ < ‖x‖` the ratio `(x + y)/x` lies in the right half-plane. -/
theorem re_add_div_pos {x y : ℂ} (hyx : ‖y‖ < ‖x‖) : 0 < ((x + y) / x).re := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg y) hyx)
  have hdiv : ‖y / x‖ < 1 := by
    rw [norm_div]; exact (div_lt_one (norm_pos_iff.mpr hx0)).mpr hyx
  have h := re_le_norm (-(y / x))
  simp only [neg_re, norm_neg] at h
  rw [add_div, div_self hx0]
  simp only [add_re, one_re]
  linarith

/-- Splitting `(x + y)^s` as `((x + y)/x)^s x^s` on the principal branch. -/
theorem add_cpow_eq_div_cpow_mul {x y : ℂ} (hx : 0 < x.re) (hyx : ‖y‖ < ‖x‖) (s : ℂ) :
    (x + y) ^ s = ((x + y) / x) ^ s * x ^ s := by
  have hx0 := slitPlane_ne_zero (Or.inl hx : x ∈ slitPlane)
  rw [← cpow_mul_of_re_pos (re_add_div_pos hyx) hx, div_mul_cancel₀ _ hx0]

/-- `x^{n/2} = (x^{1/2})^n`. -/
theorem cpow_nat_div_two (x : ℂ) (n : ℕ) : x ^ ((n : ℂ) / 2) = (x ^ (1 / 2 : ℂ)) ^ n := by
  rw [← cpow_nat_mul]; congr 1; ring

/-- `(x^{1/2})^n (x^{1/2})^n = x^n`. -/
theorem cpow_half_pow_mul_self (x : ℂ) (n : ℕ) :
    (x ^ (1 / 2 : ℂ)) ^ n * (x ^ (1 / 2 : ℂ)) ^ n = x ^ n := by
  rw [← mul_pow, ← sq, ← cpow_nat_mul]; norm_num

/-- The principal square root of a nonzero number is nonzero. -/
theorem cpow_half_ne_zero {x : ℂ} (hx : x ≠ 0) : x ^ (1 / 2 : ℂ) ≠ 0 :=
  (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hx

/-- The prefactor of the downward-`μ` Whittaker additions:
`r^{μ+1/2} r^{-2μ} = (r⁻¹)^{μ-1/2}` for `Re r > 0`. -/
theorem cpow_shift_down_prefactor {r : ℂ} (hr : 0 < r.re) (μ : ℂ) :
    r ^ (μ + 1 / 2) * r ^ (-2 * μ) = r⁻¹ ^ (μ - 1 / 2) := by
  have hr0 := slitPlane_ne_zero (Or.inl hr : r ∈ slitPlane)
  have harg : r.arg ≠ π := by
    have := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hr)); linarith [Real.pi_pos]
  rw [← cpow_add _ _ hr0, inv_cpow _ _ harg, ← cpow_neg]
  congr 1; ring

/-- Reflection of a Pochhammer symbol: `(b - n)_n = (-1)^n (1 - b)_n`. -/
theorem poch_sub_nat_self (b : ℂ) (n : ℕ) : poch (b - n) n = (-1 : ℂ) ^ n * poch (1 - b) n := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [poch_succ_left, show b - ((n + 1 : ℕ) : ℂ) + 1 = b - n by push_cast; ring, ih, poch_succ]
    push_cast
    ring

/-- Near a point `x` of the slit plane, `w^s = (w/x)^s x^s`. -/
theorem eventually_cpow_eq_div_cpow_mul {x : ℂ} (hx : x ∈ slitPlane) (s : ℂ) :
    ∀ᶠ w in 𝓝 x, w ^ s = (w / x) ^ s * x ^ s := by
  have hx0 := slitPlane_ne_zero hx
  have hπ : |x.arg| < π := by
    rw [abs_lt]
    exact ⟨neg_pi_lt_arg x, lt_of_le_of_ne (arg_le_pi x) (mem_slitPlane_iff_arg.mp hx).1⟩
  have hc : ContinuousAt (fun w => |(w / x).arg|) x := by
    refine continuous_abs.continuousAt.comp (f := fun w => (w / x).arg) ?_
    refine (continuousAt_arg ?_).comp (continuousAt_id.div_const x)
    simp [div_self hx0]
  have h0 : |(x / x).arg| < π - |x.arg| := by simp [div_self hx0]; linarith
  filter_upwards [hc.eventually (gt_mem_nhds h0), eventually_ne_nhds hx0] with w hw hw0
  have hq : w / x ≠ 0 := div_ne_zero hw0 hx0
  have hb := abs_lt.mp hw
  rw [show w ^ s = (w / x * x) ^ s by rw [div_mul_cancel₀ _ hx0],
    cpow_def_of_ne_zero (mul_ne_zero hq hx0), cpow_def_of_ne_zero hq, cpow_def_of_ne_zero hx0,
    (log_mul_eq_add_log_iff hq hx0).mpr ⟨by linarith [neg_abs_le x.arg],
      by linarith [le_abs_self x.arg]⟩, ← exp_add]
  congr 1; ring

/-- Taylor expansion of `(w/x)^s F(w)` about `x` in the slit plane, on the disk of radius `‖x‖`,
where `w/x` stays in the right half-plane. -/
theorem div_cpow_mul_eq_taylor {F : ℂ → ℂ} (hF : Differentiable ℂ F) {x y : ℂ}
    (hx : x ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) (s : ℂ) :
    ((x + y) / x) ^ s * F (x + y) =
      ∑' n : ℕ, (n.factorial : ℂ)⁻¹ * ((x ^ s)⁻¹ * iteratedDeriv n (fun w => w ^ s * F w) x) *
        y ^ n := by
  have hx0 := slitPlane_ne_zero hx
  set g : ℂ → ℂ := fun w => (w / x) ^ s * F w with hg
  have hd : DifferentiableOn ℂ g (Metric.ball x ‖x‖) := by
    intro w hw
    have hw' : ‖w - x‖ < ‖x‖ := by simpa [Metric.mem_ball, dist_eq] using hw
    have hre := re_add_div_pos hw'
    rw [add_sub_cancel] at hre
    exact (((differentiableAt_id.div_const x).cpow_const (Or.inl hre)).mul
      (hF w)).differentiableWithinAt
  have hz : x + y ∈ Metric.ball x ‖x‖ := by simpa [Metric.mem_ball, dist_eq] using hyx
  have ht := Complex.taylorSeries_eq_on_ball' hz hd
  rw [add_sub_cancel_left] at ht
  rw [show ((x + y) / x) ^ s * F (x + y) = g (x + y) from rfl, ← ht]
  congr 1; funext n
  have heq : g =ᶠ[𝓝 x] fun w => (x ^ s)⁻¹ * (w ^ s * F w) := by
    filter_upwards [eventually_cpow_eq_div_cpow_mul hx s] with w hw
    have hs0 : x ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
    simp only [hg]; rw [hw]; field_simp
  rw [heq.iteratedDeriv_eq, iteratedDeriv_const_mul_field]

/-- Principal powers in the first-parameter addition prefactor. -/
theorem cpow_first_parameter_prefactor {x y : ℂ} (hx : 0 < x.re)
    (hy : -1 / 2 < (y / x).re) (s a : ℂ) :
    (x + y) ^ s * (x / (x + y)) ^ a = ((x + y) / x) ^ (s - a) * x ^ s := by
  have hx0 := slitPlane_ne_zero (Or.inl hx : x ∈ slitPlane)
  have hr : 0 < ((x + y) / x).re := by
    rw [add_div, div_self hx0]; simp only [add_re, one_re]; linarith
  have hr0 := slitPlane_ne_zero (Or.inl hr : (x + y) / x ∈ slitPlane)
  have harg : ((x + y) / x).arg ≠ Real.pi := by
    have := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hr)); linarith [Real.pi_pos]
  have hp : (x + y) ^ s = ((x + y) / x) ^ s * x ^ s := by
    rw [← cpow_mul_of_re_pos hr hx, div_mul_cancel₀ _ hx0]
  rw [hp, show x / (x + y) = ((x + y) / x)⁻¹ from (inv_div _ _).symm,
    inv_cpow _ _ harg, ← cpow_neg, mul_right_comm _ (x ^ s), ← cpow_add _ _ hr0,
    sub_eq_add_neg]

/-- The reverse-ratio form of the same first-parameter prefactor. -/
theorem cpow_first_parameter_prefactor_recip {x y : ℂ} (hx : 0 < x.re)
    (hy : -1 / 2 < (y / x).re) (s a : ℂ) :
    (x + y) ^ s * (x / (x + y)) ^ a = (x / (x + y)) ^ (a - s) * x ^ s := by
  have hx0 := slitPlane_ne_zero (Or.inl hx : x ∈ slitPlane)
  have hr : 0 < ((x + y) / x).re := by
    rw [add_div, div_self hx0]; simp only [add_re, one_re]; linarith
  have harg : ((x + y) / x).arg ≠ Real.pi := by
    have := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hr)); linarith [Real.pi_pos]
  rw [cpow_first_parameter_prefactor hx hy,
    show x / (x + y) = ((x + y) / x)⁻¹ from (inv_div _ _).symm,
    inv_cpow _ _ harg, ← cpow_neg, neg_sub]

@[dlmf 13.12.E1]
theorem kummerM_product {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (hb1 : ∀ k : ℕ, 1 - b ≠ -k)
    (hb0 : b ≠ 0) (hb2 : b ≠ 1) (hb3 : b ≠ -1) :
    kummerM a b z * kummerM (-a) (-b) (-z) +
      a * (a - b) * z ^ 2 / (b ^ 2 * (1 - b ^ 2)) *
        kummerM (1 + a) (2 + b) z * kummerM (1 - a) (2 - b) (-z) = 1 := by
  have hmb : ∀ k : ℕ, -b ≠ -(k : ℂ) := by
    intro k hk
    cases k with
    | zero => exact hb0 (by simpa using hk)
    | succ k =>
      apply hb1 k
      push_cast at hk
      linear_combination hk
  have hbp : ∀ k : ℕ, b + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 1
  have hbpp : ∀ k : ℕ, b + 2 ≠ -(k : ℂ) := not_neg_nat_add_nat hb 2
  have hqb : ∀ k : ℕ, 2 - b ≠ -(k : ℂ) := by
    simpa only [Nat.cast_one, show 1 - b + (1 : ℂ) = 2 - b by ring] using not_neg_nat_add_nat hb1 1
  let U := kummerM a b
  let V : ℂ → ℂ := fun w => kummerM (-a) (-b) (-w)
  let P := kummerM (a + 1) (b + 2)
  let Q : ℂ → ℂ := fun w => kummerM (1 - a) (2 - b) (-w)
  let c := a * (a - b) / (b ^ 2 * (1 - b ^ 2))
  let F : ℂ → ℂ := fun w => U w * V w + c * w ^ 2 * P w * Q w
  have hder (w : ℂ) : HasDerivAt F
      ((a / b * kummerM (a + 1) (b + 1) w) * V w +
        U w * (-(a / b) * kummerM (1 - a) (1 - b) (-w)) +
        c * 2 * w * P w * Q w + c * w ^ 2 * deriv P w * Q w +
        c * w ^ 2 * P w * deriv Q w) w := by
    have hU := hasDerivAt_kummerM_shift (a := a) hb w
    have hV := (hasDerivAt_kummerM_shift (a := -a) hmb (-w)).comp w (hasDerivAt_neg w)
    have hP := (hasDerivAt_kummerM_shift (a := a + 1) hbpp w).differentiableAt.hasDerivAt
    have hQ : HasDerivAt Q (deriv Q w) w :=
      ((hasDerivAt_kummerM_shift (a := 1 - a) hqb (-w)).comp w
        (hasDerivAt_neg w)).differentiableAt.hasDerivAt
    have hV' : HasDerivAt V (-(a / b) * kummerM (1 - a) (1 - b) (-w)) w := by
      convert hV using 1 <;> simp only [V, Function.comp_def,
        show -a + 1 = 1 - a by ring, show -b + 1 = 1 - b by ring] <;> ring
    change HasDerivAt F _ w
    convert (hU.mul hV').add (((((hasDerivAt_id w).pow 2).const_mul c).mul hP).mul hQ) using 1
    · rfl
    · simp only [Pi.mul_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, mul_one]
      dsimp only [P, U]
      ring
  have hzder (w : ℂ) (hw : w ≠ 0) : deriv F w = 0 := by
    have hP := z_mul_deriv_kummerM_eq_shift_b_pred (a := a + 1) (b := b + 2)
      (by simpa only [show b + 2 - 1 = b + 1 by ring] using hbp) w
    have hQ := z_mul_deriv_kummerM_eq_shift_b_pred (a := 1 - a) (b := 2 - b)
      (by simpa only [show 2 - b - 1 = 1 - b by ring] using hb1) (-w)
    have hs := kummerM_contiguous_up_shift_aux (a := a + 1) (b := b + 1)
      (by simpa using hb) (z := w)
    have ht := kummerM_contiguous_up_shift_aux (a := 1 - a) (b := 1 - b)
      (by simpa using hmb) (z := -w)
    have hQd : deriv Q w = -deriv (kummerM (1 - a) (2 - b)) (-w) := by
      exact (((hasDerivAt_kummerM_shift (a := 1 - a) hqb (-w)).comp w
        (hasDerivAt_neg w)).deriv).trans (by
          rw [(hasDerivAt_kummerM_shift (a := 1 - a) hqb (-w)).deriv]; ring)
    rw [(hder w).deriv]
    dsimp [U, V, P, c]
    rw [hQd]
    simp only [show a + 1 - 1 = a by ring, show b + 1 - 1 = b by ring,
      show 1 - a - 1 = -a by ring, show 1 - b - 1 = -b by ring,
      show (b + 2 : ℂ) - 1 = b + 1 by ring,
      show (2 : ℂ) - b - 1 = 1 - b by ring,
      show (b + 1 : ℂ) + 1 = b + 2 by ring,
      show (1 : ℂ) - b + 1 = 2 - b by ring] at hP hQ hs ht
    dsimp [Q]
    have hbpm : 1 - b ^ 2 ≠ 0 := by
      intro hh
      have : (b - 1) * (b + 1) = 0 := by linear_combination -hh
      rcases mul_eq_zero.mp this with he | he
      · exact hb2 (by linear_combination he)
      · exact hb3 (by linear_combination he)
    have hbplus : b + 1 ≠ 0 := by simpa using hbp 0
    have hbminus : b - 1 ≠ 0 := sub_ne_zero.mpr hb2
    have hs' : kummerM (a + 1) (b + 1) w = kummerM a b w +
        (b - a) * w / (b * (b + 1)) * kummerM (a + 1) (b + 2) w := by
      field_simp
      linear_combination -hs
    have ht' : kummerM (1 - a) (1 - b) (-w) = kummerM (-a) (-b) (-w) +
        (b - a) * w / (b * (b - 1)) * kummerM (1 - a) (2 - b) (-w) := by
      field_simp
      linear_combination -ht
    have hP' : deriv (kummerM (a + 1) (b + 2)) w = (b + 1) / w *
        (kummerM (a + 1) (b + 1) w - kummerM (a + 1) (b + 2) w) := by
      field_simp
      linear_combination hP
    have hQ' : deriv (kummerM (1 - a) (2 - b)) (-w) = (b - 1) / w *
        (kummerM (1 - a) (1 - b) (-w) - kummerM (1 - a) (2 - b) (-w)) := by
      field_simp
      linear_combination -hQ
    rw [hP', hQ', hs', ht']
    field_simp [hb0, hbpm, hbplus, hbminus, hw]
    ring
  have hzero : deriv F 0 = 0 := by
    rw [(hder 0).deriv]
    simp [U, V, P, Q]
  have hconst : ∀ w : ℂ, deriv F w = 0 := fun w => by
    by_cases hw : w = 0
    · simpa [hw] using hzero
    · exact hzder w hw
  -- Mathlib’s constancy theorem identifies this entire expression from its value at zero.
  have he := is_const_of_deriv_eq_zero (fun w => (hder w).differentiableAt) hconst z 0
  simpa [F, U, V, P, Q, c, show (1 : ℂ) + a = a + 1 by ring,
    show (2 : ℂ) + b = b + 2 by ring, div_mul_eq_mul_div, mul_assoc] using he

@[dlmf 13.13.E1]
theorem kummerM_addition {a b x y : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    kummerM a b (x + y) =
      ∑' n : ℕ, poch a n * y ^ n / (poch b n * n.factorial) * kummerM (a + n) (b + n) x := by
  have hd : Differentiable ℂ (kummerM a b) := fun w =>
    ((analyticOnNhd_kummerM (a := a) hb) w (Set.mem_univ _)).differentiableAt
  rw [← Complex.taylorSeries_eq_of_entire' (c := x) (z := x + y) hd]
  congr 1
  funext n
  rw [iteratedDeriv_kummerM n hb, add_sub_cancel_left]
  ring

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.13.E2]
theorem kummerM_addition_shift_b {a b x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) (hb : ∀ k : ℤ, b ≠ k) :
    kummerM a b (x + y) =
      ((x + y) / x) ^ (1 - b) *
        ∑' n : ℕ, poch (1 - b) n * (-y / x) ^ n / n.factorial * kummerM a (b - n) x := by
  have hx0 := slitPlane_ne_zero hx
  have hr0 := slitPlane_ne_zero (Or.inl (re_add_div_pos hyx) : (x + y) / x ∈ slitPlane)
  have hbN : ∀ k : ℕ, b ≠ -k := fun k hk => hb (-k) (by push_cast; exact hk)
  have hF : Differentiable ℂ (kummerM a b) := fun w =>
    ((analyticOnNhd_kummerM (a := a) hbN) w (Set.mem_univ _)).differentiableAt
  have hM : kummerM a b (x + y) =
      ((x + y) / x) ^ (1 - b) * (((x + y) / x) ^ (b - 1) * kummerM a b (x + y)) := by
    rw [← mul_assoc, ← cpow_add _ _ hr0, show 1 - b + (b - 1) = 0 by ring, cpow_zero, one_mul]
  rw [hM, div_cpow_mul_eq_taylor hF hx hyx (b - 1)]
  congr 1; congr 1; funext n
  have hbn : ∀ k : ℕ, b - n ≠ -k := fun k hk =>
    hb ((n : ℤ) - k) (by push_cast; linear_combination hk)
  have hs0 : x ^ (b - 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  rw [iteratedDeriv_mul_cpow_kummerM n hbn hx, show b - n - 1 = (b - 1) - n by ring,
    cpow_sub (x := x) (b - 1) (n : ℂ) hx0, cpow_natCast, poch_sub_nat_self, div_pow]
  field_simp
  rw [neg_pow y]; ring

@[dlmf 13.13.E3]
theorem kummerM_addition_shift_a {a b x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hy : -1 / 2 < (y / x).re) (hb : ∀ k : ℕ, b ≠ -k) :
    kummerM a b (x + y) =
      (x / (x + y)) ^ a *
        ∑' n : ℕ, poch a n * y ^ n / (n.factorial * (x + y) ^ n) * kummerM (a + n) b x := by
  have hx0 := slitPlane_ne_zero hx
  have hxy0 := slitPlane_ne_zero hxy
  have ht := kummerM_mobius_taylor (a := a) (x := x) hb (norm_div_add_lt_one hx0 hxy0 hy)
  simpa only [Nat.cast_zero, add_zero] using
    (of_mobius_taylor (F := fun n => kummerM (a + n) b) hx0 hxy0 (by simpa using ht))

@[dlmf 13.13.E4]
theorem kummerM_addition_exp {a b x y : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    kummerM a b (x + y) =
      exp y * ∑' n : ℕ, poch (b - a) n * (-y) ^ n / (poch b n * n.factorial) *
        kummerM a (b + n) x := by
  set f : ℂ → ℂ := fun w => exp (-w) * kummerM a b w with hf
  have hd : Differentiable ℂ f := fun w =>
    (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => exp (-w)) w).mul
      ((analyticOnNhd_kummerM (a := a) hb) w (Set.mem_univ _)).differentiableAt
  have ht := Complex.taylorSeries_eq_of_entire' (c := x) (z := x + y) hd
  have hM : kummerM a b (x + y) = exp (x + y) * f (x + y) := by
    simp only [hf, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
  rw [hM, ← ht, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  funext n
  rw [hf, iteratedDeriv_exp_neg_kummerM n hb, add_sub_cancel_left, exp_add]
  beta_reduce
  rw [exp_neg]
  have hx : exp x ≠ 0 := exp_ne_zero x
  rw [neg_pow y]
  field_simp

@[dlmf 13.13.E5]
theorem kummerM_addition_exp_shift_a {a b x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hy : 1 / 2 < ((y + x) / x).re) (hb : ∀ k : ℕ, b ≠ -k) :
    kummerM a b (x + y) =
      exp y * (x / (x + y)) ^ (b - a) *
        ∑' n : ℕ, poch (b - a) n * y ^ n / (n.factorial * (x + y) ^ n) *
          kummerM (a - n) b x := by
  have hx0 := slitPlane_ne_zero hx
  have hxy0 := slitPlane_ne_zero hxy
  have hy' : -1 / 2 < (y / x).re := by
    rw [add_div, div_self hx0] at hy
    simp only [add_re, one_re] at hy
    linarith
  have ht := kummerM_exp_mobius_taylor (a := a) (x := x) hb (norm_div_add_lt_one hx0 hxy0 hy')
  have he := of_mobius_taylor (s := b - a) (C := poch (b - a))
    (F := fun n z => exp (-z) * kummerM (a - n) b z)
    hx0 hxy0 (by simpa using ht)
  simp only [Nat.cast_zero, sub_zero] at he
  have he' := congrArg (fun z : ℂ => exp (x + y) * z) he
  simp only [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul] at he'
  rw [he']
  simp only [← tsum_mul_left]
  apply tsum_congr
  intro n
  have hex : exp (x + y) * exp (-x) = exp y := by rw [← exp_add]; congr 1; ring
  linear_combination ((x / (x + y)) ^ (b - a) *
    (poch (b - a) n * y ^ n / (n.factorial * (x + y) ^ n)) * kummerM (a - n) b x) * hex

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.13.E6]
theorem kummerM_addition_exp_shift_both {a b x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) (hb : ∀ k : ℤ, b ≠ k) :
    kummerM a b (x + y) =
      exp y * ((x + y) / x) ^ (1 - b) *
        ∑' n : ℕ, poch (1 - b) n * (-y) ^ n / (n.factorial * x ^ n) *
          kummerM (a - n) (b - n) x := by
  have hx0 := slitPlane_ne_zero hx
  have hr0 := slitPlane_ne_zero (Or.inl (re_add_div_pos hyx) : (x + y) / x ∈ slitPlane)
  have hbN : ∀ k : ℕ, b ≠ -k := fun k hk => hb (-k) (by push_cast; exact hk)
  have hF : Differentiable ℂ (fun w => cexp (-w) * kummerM a b w) := fun w =>
    (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => cexp (-w)) w).mul
      ((analyticOnNhd_kummerM (a := a) hbN) w (Set.mem_univ _)).differentiableAt
  have hM : kummerM a b (x + y) = cexp (x + y) *
      (((x + y) / x) ^ (1 - b) *
        (((x + y) / x) ^ (b - 1) * (cexp (-(x + y)) * kummerM a b (x + y)))) := by
    rw [← mul_assoc (((x + y) / x) ^ (1 - b)), ← cpow_add _ _ hr0,
      show 1 - b + (b - 1) = 0 by ring, cpow_zero, one_mul, ← mul_assoc, ← exp_add,
      add_neg_cancel, exp_zero, one_mul]
  rw [hM, div_cpow_mul_eq_taylor hF hx hyx (b - 1), ← tsum_mul_left, ← tsum_mul_left,
    ← tsum_mul_left]
  congr 1; funext n
  have hbn : ∀ k : ℕ, b - n ≠ -k := fun k hk =>
    hb ((n : ℤ) - k) (by push_cast; linear_combination hk)
  have hs0 : x ^ (b - 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  rw [show (fun w => w ^ (b - 1) * (cexp (-w) * kummerM a b w)) =
      fun w => w ^ (b - 1) * cexp (-w) * kummerM a b w by funext w; ring,
    iteratedDeriv_mul_cpow_exp_neg_kummerM n hbn hx, show b - n - 1 = (b - 1) - n by ring,
    cpow_sub (x := x) (b - 1) (n : ℂ) hx0, cpow_natCast, poch_sub_nat_self, exp_add, exp_neg x]
  field_simp
  rw [neg_pow y]; ring

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.13.E7]
theorem kummerU_addition (a b : ℂ) {x y : ℂ} (hx : 0 < x.re) (hxy : x + y ∈ slitPlane)
    (hyx : ‖y‖ < ‖x‖) :
    kummerU a b (x + y) =
      ∑' n : ℕ, poch a n * (-y) ^ n / n.factorial * kummerU (a + n) (b + n) x := by
  have hx' : x ∈ slitPlane := Or.inl hx
  have hd : DifferentiableOn ℂ (kummerU a b) (Metric.ball x ‖x‖) :=
    fun w hw => (differentiableAt_kummerU a b (ball_norm_subset_slitPlane hx hw)).differentiableWithinAt
  rw [← Complex.taylorSeries_eq_on_ball' (c := x) (z := x + y)
    (by simpa [mem_ball_iff_norm] using hyx) hd]
  congr 1
  funext n
  rw [iteratedDeriv_kummerU a b n hx', add_sub_cancel_left, neg_pow]
  ring

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.13.E8]
theorem kummerU_addition_shift_b {a b x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) :
    kummerU a b (x + y) =
      ((x + y) / x) ^ (1 - b) *
        ∑' n : ℕ, poch (1 + a - b) n * (-y / x) ^ n / n.factorial * kummerU a (b - n) x := by
  have hx0 := slitPlane_ne_zero (Or.inl hx : x ∈ slitPlane)
  rw [kummerU_kummer_transform_all a b (slitPlane_ne_zero hxy),
    kummerU_addition (a - b + 1) (2 - b) hx hxy hyx,
    ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  funext n
  rw [kummerU_kummer_transform_all (a - b + 1 + n) (2 - b + n) hx0,
    show (a - b + 1 + n) - (2 - b + n) + 1 = a by ring,
    show 2 - (2 - b + (n : ℂ)) = b - n by ring,
    show 1 - (2 - b + (n : ℂ)) = b - n - 1 by ring]
  have hp := cpow_add_shift_factor hx hyx b n
  rw [div_pow, show (1 : ℂ) + a - b = a - b + 1 by ring]
  linear_combination (poch (a - b + 1) n * (-y) ^ n / n.factorial * kummerU a (b - n) x) * hp

@[dlmf 13.13.E9]
theorem kummerU_addition_shift_a {a b x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hy : -1 / 2 < (y / x).re) :
    kummerU a b (x + y) =
      (x / (x + y)) ^ a *
        ∑' n : ℕ, poch a n * poch (1 + a - b) n * y ^ n / (n.factorial * (x + y) ^ n) *
          kummerU (a + n) b x := by
  have hx0 := slitPlane_ne_zero (Or.inl hx : x ∈ slitPlane)
  have hxy0 := slitPlane_ne_zero hxy
  have ht := kummerU_mobius_taylor a b hx (norm_div_add_lt_one hx0 hxy0 hy)
  simpa only [Nat.cast_zero, add_zero] using
    (of_mobius_taylor (F := fun n => kummerU (a + n) b) hx0 hxy0 (by simpa using ht))

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.13.E10]
theorem kummerU_addition_exp (a b : ℂ) {x y : ℂ} (hx : 0 < x.re) (hxy : x + y ∈ slitPlane)
    (hyx : ‖y‖ < ‖x‖) :
    kummerU a b (x + y) =
      exp y * ∑' n : ℕ, (-y) ^ n / n.factorial * kummerU a (b + n) x := by
  have hx' : x ∈ slitPlane := Or.inl hx
  set f : ℂ → ℂ := fun w => exp (-w) * kummerU a b w with hf
  have hd : DifferentiableOn ℂ f (Metric.ball x ‖x‖) := by
    intro w hw
    exact ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => exp (-w)) w).mul
      (differentiableAt_kummerU a b (ball_norm_subset_slitPlane hx hw))).differentiableWithinAt
  have ht := Complex.taylorSeries_eq_on_ball' (c := x)
    (z := x + y) (by simpa [mem_ball_iff_norm] using hyx) hd
  have hU : kummerU a b (x + y) = exp (x + y) * f (x + y) := by
    simp only [hf, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
  rw [hU, ← ht, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  funext n
  rw [hf, iteratedDeriv_exp_neg_kummerU a b n hx', add_sub_cancel_left, exp_add, exp_neg, neg_pow y]
  field_simp

@[dlmf 13.13.E11]
theorem kummerU_addition_exp_shift_a {a b x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hy : -1 / 2 < (y / x).re) :
    kummerU a b (x + y) =
      exp y * (x / (x + y)) ^ (b - a) *
        ∑' n : ℕ, (-y) ^ n / (n.factorial * (x + y) ^ n) * kummerU (a - n) b x := by
  have hx0 := slitPlane_ne_zero (Or.inl hx : x ∈ slitPlane)
  have hxy0 := slitPlane_ne_zero hxy
  have ht := kummerU_exp_mobius_taylor a b hx (norm_div_add_lt_one hx0 hxy0 hy)
  have he := of_mobius_taylor (s := b - a) (C := fun n => (-1 : ℂ) ^ n)
    (F := fun n z => exp (-z) * kummerU (a - n) b z)
    hx0 hxy0 (by simpa using ht)
  simp only [Nat.cast_zero, sub_zero] at he
  have he' := congrArg (fun z : ℂ => exp (x + y) * z) he
  simp only [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul] at he'
  rw [he']
  simp only [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [neg_pow]
  have hex : exp (x + y) * exp (-x) = exp y := by rw [← exp_add]; congr 1; ring
  linear_combination ((x / (x + y)) ^ (b - a) *
    ((-1 : ℂ) ^ n * y ^ n / (n.factorial * (x + y) ^ n)) * kummerU (a - n) b x) * hex

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.13.E12]
theorem kummerU_addition_exp_shift_both {a b x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) :
    kummerU a b (x + y) =
      exp y * ((x + y) / x) ^ (1 - b) *
        ∑' n : ℕ, (-y) ^ n / (n.factorial * x ^ n) * kummerU (a - n) (b - n) x := by
  have hx0 := slitPlane_ne_zero (Or.inl hx : x ∈ slitPlane)
  rw [kummerU_kummer_transform_all a b (slitPlane_ne_zero hxy),
    kummerU_addition_exp (a - b + 1) (2 - b) hx hxy hyx,
    ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  funext n
  rw [kummerU_kummer_transform_all (a - b + 1) (2 - b + n) hx0,
    show (a - b + 1) - (2 - b + n) + 1 = a - n by ring,
    show 2 - (2 - b + (n : ℂ)) = b - n by ring,
    show 1 - (2 - b + (n : ℂ)) = b - n - 1 by ring]
  have hp := cpow_add_shift_factor hx hyx b n
  linear_combination (exp y * (-y) ^ n / n.factorial * kummerU (a - n) (b - n) x) * hp

/-- Whittaker product formula for `2μ` not an integer, where all four `M` factors are regular. -/
@[dlmf 13.25.E1]
theorem whittakerM_product {κ μ z : ℂ} (hμ : ∀ k : ℕ, 2 * μ ≠ -k)
    (hμ1 : μ ≠ 0) (hμ2 : μ ≠ -1) (hμ3 : 1 + 2 * μ ≠ 0) (hμpos : ∀ k : ℕ, 2 * μ ≠ k + 1)
    (hz : z ∈ slitPlane) :
    whittakerM κ μ z * whittakerM κ (-μ - 1) z +
      (1 / 2 + μ + κ) * (1 / 2 + μ - κ) / (4 * μ * (1 + μ) * (1 + 2 * μ) ^ 2) *
        whittakerM κ (μ + 1) z * whittakerM κ (-μ) z = 1 := by
  have hz0 := slitPlane_ne_zero hz
  let a := μ - κ + 1 / 2
  let b := 1 + 2 * μ
  have hb : ∀ k : ℕ, b ≠ -(k : ℂ) := by
    simpa only [b, Nat.cast_one, add_comm] using not_neg_nat_add_nat hμ 1
  have hmb : ∀ k : ℕ, -b ≠ -(k : ℂ) := by
    intro k hk
    cases k with
    | zero => exact hμ3 (by dsimp [b] at hk; norm_num at hk; linear_combination -hk)
    | succ k =>
      cases k with
      | zero => exact hμ1 (by dsimp [b] at hk; norm_num at hk; exact hk)
      | succ k =>
        apply hμpos k
        dsimp [b] at hk
        push_cast at hk ⊢
        linear_combination -hk
  have h1b : ∀ k : ℕ, 1 - b ≠ -(k : ℂ) := by
    intro k hk
    cases k with
    | zero => exact hμ1 (by dsimp [b] at hk; norm_num at hk; exact hk)
    | succ k =>
      apply hμpos k
      dsimp [b] at hk
      push_cast at hk ⊢
      linear_combination -hk
  have h2b : ∀ k : ℕ, 2 - b ≠ -(k : ℂ) := by
    simpa only [Nat.cast_one, show 1 - b + 1 = 2 - b by ring] using not_neg_nat_add_nat h1b 1
  have hE : exp (-z / 2) * exp (-z / 2) * exp z = 1 := by
    rw [← exp_add, ← exp_add, show -z / 2 + -z / 2 + z = 0 by ring, exp_zero]
  have hpair1 : whittakerM κ μ z * whittakerM κ (-μ - 1) z =
      kummerM a b z * kummerM (-a) (-b) (-z) := by
    unfold whittakerM
    rw [show 1 + 2 * (-μ - 1) = -b by dsimp [b]; ring,
      kummerM_kummer_transform hmb]
    rw [show -b - (-μ - 1 - κ + 1 / 2) = -a by dsimp [a, b]; ring]
    calc
      _ = (exp (-z / 2) * exp (-z / 2) * exp z) *
          (z ^ (μ + 1 / 2) * z ^ (-μ - 1 + 1 / 2)) *
          (kummerM a b z * kummerM (-a) (-b) (-z)) := by dsimp [a, b]; ring
      _ = _ := by rw [hE, ← cpow_add _ _ hz0, show μ + 1 / 2 + (-μ - 1 + 1 / 2) = 0 by ring]; simp
  have hpair2 : whittakerM κ (μ + 1) z * whittakerM κ (-μ) z =
      z ^ 2 * kummerM (1 + a) (2 + b) z * kummerM (1 - a) (2 - b) (-z) := by
    unfold whittakerM
    rw [show 1 + 2 * -μ = 2 - b by dsimp [b]; ring,
      kummerM_kummer_transform h2b]
    rw [show 2 - b - (-μ - κ + 1 / 2) = 1 - a by dsimp [a, b]; ring]
    calc
      _ = (exp (-z / 2) * exp (-z / 2) * exp z) *
          (z ^ (μ + 1 + 1 / 2) * z ^ (-μ + 1 / 2)) *
          (kummerM (1 + a) (2 + b) z * kummerM (1 - a) (2 - b) (-z)) := by dsimp [a, b]; ring
      _ = _ := by
        rw [hE, ← cpow_add _ _ hz0, show μ + 1 + 1 / 2 + (-μ + 1 / 2) = (2 : ℂ) by ring]
        simp [cpow_ofNat, mul_assoc]
  rw [hpair1, mul_assoc _ (whittakerM κ (μ + 1) z), hpair2]
  have hb0 : b ≠ 0 := hμ3
  have hb2 : b ≠ 1 := by dsimp [b]; intro he; apply hμ1; linear_combination he / 2
  have hb3 : b ≠ -1 := by dsimp [b]; intro he; apply hμ2; linear_combination he / 2
  have h := kummerM_product (a := a) (z := z) hb h1b hb0 hb2 hb3
  have hc : (1 / 2 + μ + κ) * (1 / 2 + μ - κ) /
      (4 * μ * (1 + μ) * (1 + 2 * μ) ^ 2) = a * (a - b) / (b ^ 2 * (1 - b ^ 2)) := by
    dsimp [a, b]
    rw [show 1 - (1 + 2 * μ) ^ 2 = -4 * μ * (1 + μ) by ring]
    have hp : 1 + μ ≠ 0 := by intro he; apply hμ2; linear_combination he
    field_simp [hμ1, hp, hμ3]
    ring
  rw [hc]
  convert h using 1 <;> ring

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.26.E1]
theorem whittakerM_addition {κ μ x y : ℂ} (hx : 0 < x.re) (hxy : x + y ∈ slitPlane)
    (hyx : ‖y‖ < ‖x‖)
    (hμ : ∀ k : ℤ, 1 + 2 * μ ≠ k) :
    whittakerM κ μ (x + y) =
      exp (-y / 2) * (x / (x + y)) ^ (μ - 1 / 2) *
        ∑' n : ℕ, poch (-2 * μ) n / n.factorial * (-y / x ^ (1 / 2 : ℂ)) ^ n *
          whittakerM (κ - n / 2) (μ - n / 2) x := by
  have hx' : x ∈ slitPlane := Or.inl hx
  have hx0 := slitPlane_ne_zero hx'
  have hh := cpow_half_ne_zero hx0
  have hr := re_add_div_pos hyx
  simp only [whittakerM]
  rw [kummerM_addition_shift_b hx' hxy hyx hμ, add_cpow_eq_div_cpow_mul hx hyx,
    show x / (x + y) = ((x + y) / x)⁻¹ from (inv_div _ _).symm,
    ← cpow_shift_down_prefactor hr μ, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  congr 1; funext n
  rw [show (1 : ℂ) - (1 + 2 * μ) = -2 * μ by ring,
    show μ - (n : ℂ) / 2 - (κ - n / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show 1 + 2 * (μ - (n : ℂ) / 2) = 1 + 2 * μ - n by ring,
    show μ - (n : ℂ) / 2 + 1 / 2 = μ + 1 / 2 - n / 2 by ring,
    cpow_sub (x := x) (μ + 1 / 2) ((n : ℂ) / 2) hx0, cpow_nat_div_two, div_pow (-y) x,
    ← cpow_half_pow_mul_self x n, div_pow (-y) (x ^ (1 / 2 : ℂ)),
    show -(x + y) / 2 = -y / 2 + -x / 2 by ring, exp_add]
  field_simp

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.26.E2]
theorem whittakerM_addition_shift_mu {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ (x + y) =
      exp (-y / 2) * ((x + y) / x) ^ (μ + 1 / 2) *
        ∑' n : ℕ, poch (1 / 2 + μ - κ) n / (poch (1 + 2 * μ) n * n.factorial) *
          (y / x ^ (1 / 2 : ℂ)) ^ n * whittakerM (κ - n / 2) (μ + n / 2) x := by
  have hx0 := slitPlane_ne_zero (Or.inl hx : x ∈ slitPlane)
  have hh := cpow_half_ne_zero hx0
  simp only [whittakerM]
  rw [kummerM_addition hμ, add_cpow_eq_div_cpow_mul hx hyx, ← tsum_mul_left, ← tsum_mul_left]
  congr 1; funext n
  rw [show μ + (n : ℂ) / 2 - (κ - n / 2) + 1 / 2 = μ - κ + 1 / 2 + n by ring,
    show 1 + 2 * (μ + (n : ℂ) / 2) = 1 + 2 * μ + n by ring,
    show μ + (n : ℂ) / 2 + 1 / 2 = μ + 1 / 2 + n / 2 by ring,
    cpow_add (x := x) (μ + 1 / 2) ((n : ℂ) / 2) hx0, cpow_nat_div_two,
    show (1 : ℂ) / 2 + μ - κ = μ - κ + 1 / 2 by ring, div_pow,
    show -(x + y) / 2 = -y / 2 + -x / 2 by ring, exp_add]
  field_simp

@[dlmf 13.26.E3]
theorem whittakerM_addition_shift_kappa {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hy : -1 / 2 < (y / x).re)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ (x + y) =
      exp (-y / 2) * ((x + y) / x) ^ κ *
        ∑' n : ℕ, poch (1 / 2 + μ - κ) n * y ^ n / (n.factorial * (x + y) ^ n) *
          whittakerM (κ - n) μ x := by
  simp only [whittakerM]
  rw [kummerM_addition_shift_a (Or.inl hx) hxy hy hμ]
  simp only [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [show μ - (κ - n) + 1 / 2 = μ - κ + 1 / 2 + n by ring,
    show 1 / 2 + μ - κ = μ - κ + 1 / 2 by ring]
  have hp := cpow_first_parameter_prefactor hx hy (μ + 1 / 2) (μ - κ + 1 / 2)
  rw [show μ + 1 / 2 - (μ - κ + 1 / 2) = κ by ring] at hp
  have he : exp (-(x + y) / 2) = exp (-y / 2) * exp (-x / 2) := by
    rw [← exp_add]; congr 1; ring
  rw [he]
  linear_combination (exp (-y / 2) * exp (-x / 2) *
    (poch (μ - κ + 1 / 2) n * y ^ n / (n.factorial * (x + y) ^ n)) *
      kummerM (μ - κ + 1 / 2 + n) (1 + 2 * μ) x) * hp

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.26.E4]
theorem whittakerM_addition_exp {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) (hμ : ∀ k : ℤ, 1 + 2 * μ ≠ k) :
    whittakerM κ μ (x + y) =
      exp (y / 2) * (x / (x + y)) ^ (μ - 1 / 2) *
        ∑' n : ℕ, poch (-2 * μ) n / n.factorial * (-y / x ^ (1 / 2 : ℂ)) ^ n *
          whittakerM (κ + n / 2) (μ - n / 2) x := by
  have hx' : x ∈ slitPlane := Or.inl hx
  have hx0 := slitPlane_ne_zero hx'
  have hh := cpow_half_ne_zero hx0
  have hr := re_add_div_pos hyx
  have hey : cexp y = cexp (y / 2) * cexp (y / 2) := by rw [← exp_add]; ring_nf
  simp only [whittakerM]
  rw [kummerM_addition_exp_shift_both hx' hxy hyx hμ, add_cpow_eq_div_cpow_mul hx hyx,
    show x / (x + y) = ((x + y) / x)⁻¹ from (inv_div _ _).symm,
    ← cpow_shift_down_prefactor hr μ, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  congr 1; funext n
  rw [show (1 : ℂ) - (1 + 2 * μ) = -2 * μ by ring,
    show μ - (n : ℂ) / 2 - (κ + n / 2) + 1 / 2 = μ - κ + 1 / 2 - n by ring,
    show 1 + 2 * (μ - (n : ℂ) / 2) = 1 + 2 * μ - n by ring,
    show μ - (n : ℂ) / 2 + 1 / 2 = μ + 1 / 2 - n / 2 by ring,
    cpow_sub (x := x) (μ + 1 / 2) ((n : ℂ) / 2) hx0, cpow_nat_div_two,
    ← cpow_half_pow_mul_self x n, div_pow (-y) (x ^ (1 / 2 : ℂ)),
    show -(x + y) / 2 = -(y / 2) + -x / 2 by ring, exp_add, exp_neg (y / 2), hey]
  field_simp

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.26.E5]
theorem whittakerM_addition_exp_shift_mu {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ (x + y) =
      exp (y / 2) * ((x + y) / x) ^ (μ + 1 / 2) *
        ∑' n : ℕ, poch (1 / 2 + μ + κ) n / (poch (1 + 2 * μ) n * n.factorial) *
          (-y / x ^ (1 / 2 : ℂ)) ^ n * whittakerM (κ + n / 2) (μ + n / 2) x := by
  have hx0 := slitPlane_ne_zero (Or.inl hx : x ∈ slitPlane)
  have hh := cpow_half_ne_zero hx0
  have hey : cexp y = cexp (y / 2) * cexp (y / 2) := by rw [← exp_add]; ring_nf
  simp only [whittakerM]
  rw [kummerM_addition_exp hμ, add_cpow_eq_div_cpow_mul hx hyx, ← tsum_mul_left,
    ← tsum_mul_left, ← tsum_mul_left]
  congr 1; funext n
  rw [show μ + (n : ℂ) / 2 - (κ + n / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show 1 + 2 * (μ + (n : ℂ) / 2) = 1 + 2 * μ + n by ring,
    show μ + (n : ℂ) / 2 + 1 / 2 = μ + 1 / 2 + n / 2 by ring,
    cpow_add (x := x) (μ + 1 / 2) ((n : ℂ) / 2) hx0, cpow_nat_div_two,
    show (1 : ℂ) / 2 + μ + κ = 1 + 2 * μ - (μ - κ + 1 / 2) by ring, div_pow,
    show -(x + y) / 2 = -(y / 2) + -x / 2 by ring, exp_add, exp_neg (y / 2), hey]
  field_simp

@[dlmf 13.26.E6]
theorem whittakerM_addition_exp_shift_kappa {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hy : 1 / 2 < ((y + x) / x).re)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ (x + y) =
      exp (y / 2) * (x / (x + y)) ^ κ *
        ∑' n : ℕ, poch (1 / 2 + μ + κ) n * y ^ n / (n.factorial * (x + y) ^ n) *
          whittakerM (κ + n) μ x := by
  have hx0 := slitPlane_ne_zero (Or.inl hx : x ∈ slitPlane)
  have hy' : -1 / 2 < (y / x).re := by
    rw [add_div, div_self hx0] at hy
    simp only [add_re, one_re] at hy; linarith
  simp only [whittakerM]
  rw [kummerM_addition_exp_shift_a (Or.inl hx) hxy hy hμ]
  simp only [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [show μ - (κ + n) + 1 / 2 = μ - κ + 1 / 2 - n by ring,
    show 1 + 2 * μ - (μ - κ + 1 / 2) = 1 / 2 + μ + κ by ring]
  have hp := cpow_first_parameter_prefactor_recip hx hy' (μ + 1 / 2) (1 / 2 + μ + κ)
  rw [show (1 / 2 + μ + κ) - (μ + 1 / 2) = κ by ring] at hp
  have he : exp (-(x + y) / 2) * exp y = exp (y / 2) * exp (-x / 2) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  linear_combination (exp (-(x + y) / 2) * exp y *
    (poch (1 / 2 + μ + κ) n * y ^ n / (n.factorial * (x + y) ^ n)) *
      kummerM (μ - κ + 1 / 2 - n) (1 + 2 * μ) x) * hp +
    ((x / (x + y)) ^ κ * x ^ (μ + 1 / 2) *
      (poch (1 / 2 + μ + κ) n * y ^ n / (n.factorial * (x + y) ^ n)) *
      kummerM (μ - κ + 1 / 2 - n) (1 + 2 * μ) x) * he

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.26.E7]
theorem whittakerW_addition {κ μ x y : ℂ} (hx : 0 < x.re) (hxy : x + y ∈ slitPlane)
    (hyx : ‖y‖ < ‖x‖) :
    whittakerW κ μ (x + y) =
      exp (-y / 2) * (x / (x + y)) ^ (μ - 1 / 2) *
        ∑' n : ℕ, poch (1 / 2 - μ - κ) n / n.factorial * (-y / x ^ (1 / 2 : ℂ)) ^ n *
          whittakerW (κ - n / 2) (μ - n / 2) x := by
  have hx0 := slitPlane_ne_zero (Or.inl hx : x ∈ slitPlane)
  have hh := cpow_half_ne_zero hx0
  have hr := re_add_div_pos hyx
  simp only [whittakerW]
  rw [kummerU_addition_shift_b hx hxy hyx, add_cpow_eq_div_cpow_mul hx hyx,
    show x / (x + y) = ((x + y) / x)⁻¹ from (inv_div _ _).symm,
    ← cpow_shift_down_prefactor hr μ, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  congr 1; funext n
  rw [show ((x + y) / x) ^ (1 / 2 + μ) = ((x + y) / x) ^ (μ + 1 / 2) by rw [add_comm (1 / 2 : ℂ)],
    show (1 : ℂ) - (1 + 2 * μ) = -2 * μ by ring,
    show 1 + (1 / 2 + μ - κ) - (1 + 2 * μ) = 1 / 2 - μ - κ by ring,
    show (1 : ℂ) / 2 + (μ - n / 2) - (κ - n / 2) = 1 / 2 + μ - κ by ring,
    show 1 + 2 * (μ - (n : ℂ) / 2) = 1 + 2 * μ - n by ring,
    show (1 : ℂ) / 2 + (μ - n / 2) = 1 / 2 + μ - n / 2 by ring,
    cpow_sub (x := x) (1 / 2 + μ) ((n : ℂ) / 2) hx0, cpow_nat_div_two, div_pow (-y) x,
    ← cpow_half_pow_mul_self x n, div_pow (-y) (x ^ (1 / 2 : ℂ)),
    show -(x + y) / 2 = -y / 2 + -x / 2 by ring, exp_add]
  field_simp

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.26.E8]
theorem whittakerW_addition_shift_mu {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) :
    whittakerW κ μ (x + y) =
      exp (-y / 2) * ((x + y) / x) ^ (μ + 1 / 2) *
        ∑' n : ℕ, poch (1 / 2 + μ - κ) n / n.factorial * (-y / x ^ (1 / 2 : ℂ)) ^ n *
          whittakerW (κ - n / 2) (μ + n / 2) x := by
  have hx0 := slitPlane_ne_zero (Or.inl hx : x ∈ slitPlane)
  have hh := cpow_half_ne_zero hx0
  simp only [whittakerW]
  rw [kummerU_addition _ _ hx hxy hyx, add_cpow_eq_div_cpow_mul hx hyx, ← tsum_mul_left,
    ← tsum_mul_left]
  congr 1; funext n
  rw [show (1 : ℂ) / 2 + (μ + n / 2) - (κ - n / 2) = 1 / 2 + μ - κ + n by ring,
    show 1 + 2 * (μ + (n : ℂ) / 2) = 1 + 2 * μ + n by ring,
    show (1 : ℂ) / 2 + (μ + n / 2) = 1 / 2 + μ + n / 2 by ring,
    cpow_add (x := x) (1 / 2 + μ) ((n : ℂ) / 2) hx0, cpow_nat_div_two,
    show (1 : ℂ) / 2 + μ = μ + 1 / 2 by ring, div_pow,
    show -(x + y) / 2 = -y / 2 + -x / 2 by ring, exp_add]
  field_simp

@[dlmf 13.26.E9]
theorem whittakerW_addition_shift_kappa {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hy : -1 / 2 < (y / x).re) :
    whittakerW κ μ (x + y) =
      exp (-y / 2) * ((x + y) / x) ^ κ *
        ∑' n : ℕ, poch (1 / 2 + μ - κ) n * poch (1 / 2 - μ - κ) n / n.factorial *
          (y / (x + y)) ^ n * whittakerW (κ - n) μ x := by
  simp only [whittakerW]
  rw [kummerU_addition_shift_a hx hxy hy]
  simp only [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [show 1 / 2 + μ - (κ - n) = 1 / 2 + μ - κ + n by ring,
    show 1 + (1 / 2 + μ - κ) - (1 + 2 * μ) = 1 / 2 - μ - κ by ring, div_pow]
  have hp := cpow_first_parameter_prefactor hx hy (1 / 2 + μ) (1 / 2 + μ - κ)
  rw [show 1 / 2 + μ - (1 / 2 + μ - κ) = κ by ring] at hp
  have he : exp (-(x + y) / 2) = exp (-y / 2) * exp (-x / 2) := by
    rw [← exp_add]; congr 1; ring
  rw [he]
  linear_combination (exp (-y / 2) * exp (-x / 2) *
    (poch (1 / 2 + μ - κ) n * poch (1 / 2 - μ - κ) n * y ^ n /
      (n.factorial * (x + y) ^ n)) * kummerU (1 / 2 + μ - κ + n) (1 + 2 * μ) x) * hp

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.26.E10]
theorem whittakerW_addition_exp {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) :
    whittakerW κ μ (x + y) =
      exp (y / 2) * (x / (x + y)) ^ (μ - 1 / 2) *
        ∑' n : ℕ, (1 / n.factorial) * (-y / x ^ (1 / 2 : ℂ)) ^ n *
          whittakerW (κ + n / 2) (μ - n / 2) x := by
  have hx0 := slitPlane_ne_zero (Or.inl hx : x ∈ slitPlane)
  have hh := cpow_half_ne_zero hx0
  have hr := re_add_div_pos hyx
  have hey : cexp y = cexp (y / 2) * cexp (y / 2) := by rw [← exp_add]; ring_nf
  simp only [whittakerW]
  rw [kummerU_addition_exp_shift_both hx hxy hyx, add_cpow_eq_div_cpow_mul hx hyx,
    show x / (x + y) = ((x + y) / x)⁻¹ from (inv_div _ _).symm,
    ← cpow_shift_down_prefactor hr μ, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  congr 1; funext n
  rw [show ((x + y) / x) ^ (1 / 2 + μ) = ((x + y) / x) ^ (μ + 1 / 2) by rw [add_comm (1 / 2 : ℂ)],
    show (1 : ℂ) - (1 + 2 * μ) = -2 * μ by ring,
    show (1 : ℂ) / 2 + (μ - n / 2) - (κ + n / 2) = 1 / 2 + μ - κ - n by ring,
    show 1 + 2 * (μ - (n : ℂ) / 2) = 1 + 2 * μ - n by ring,
    show (1 : ℂ) / 2 + (μ - n / 2) = 1 / 2 + μ - n / 2 by ring,
    cpow_sub (x := x) (1 / 2 + μ) ((n : ℂ) / 2) hx0, cpow_nat_div_two,
    ← cpow_half_pow_mul_self x n, div_pow (-y) (x ^ (1 / 2 : ℂ)),
    show -(x + y) / 2 = -(y / 2) + -x / 2 by ring, exp_add, exp_neg (y / 2), hey]
  field_simp

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.26.E11]
theorem whittakerW_addition_exp_shift_mu {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) :
    whittakerW κ μ (x + y) =
      exp (y / 2) * ((x + y) / x) ^ (μ + 1 / 2) *
        ∑' n : ℕ, (1 / n.factorial) * (-y / x ^ (1 / 2 : ℂ)) ^ n *
          whittakerW (κ + n / 2) (μ + n / 2) x := by
  have hx0 := slitPlane_ne_zero (Or.inl hx : x ∈ slitPlane)
  have hh := cpow_half_ne_zero hx0
  have hey : cexp y = cexp (y / 2) * cexp (y / 2) := by rw [← exp_add]; ring_nf
  simp only [whittakerW]
  rw [kummerU_addition_exp _ _ hx hxy hyx, add_cpow_eq_div_cpow_mul hx hyx, ← tsum_mul_left,
    ← tsum_mul_left, ← tsum_mul_left]
  congr 1; funext n
  rw [show (1 : ℂ) / 2 + (μ + n / 2) - (κ + n / 2) = 1 / 2 + μ - κ by ring,
    show 1 + 2 * (μ + (n : ℂ) / 2) = 1 + 2 * μ + n by ring,
    show (1 : ℂ) / 2 + (μ + n / 2) = 1 / 2 + μ + n / 2 by ring,
    cpow_add (x := x) (1 / 2 + μ) ((n : ℂ) / 2) hx0, cpow_nat_div_two,
    show (1 : ℂ) / 2 + μ = μ + 1 / 2 by ring, div_pow,
    show -(x + y) / 2 = -(y / 2) + -x / 2 by ring, exp_add, exp_neg (y / 2), hey]
  field_simp

@[dlmf 13.26.E12]
theorem whittakerW_addition_exp_shift_kappa {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hy : -1 / 2 < (y / x).re) :
    whittakerW κ μ (x + y) =
      exp (y / 2) * (x / (x + y)) ^ κ *
        ∑' n : ℕ, (1 / n.factorial) * (-y / (x + y)) ^ n * whittakerW (κ + n) μ x := by
  simp only [whittakerW]
  rw [kummerU_addition_exp_shift_a hx hxy hy]
  simp only [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [show 1 / 2 + μ - (κ + n) = 1 / 2 + μ - κ - n by ring,
    show 1 + 2 * μ - (1 / 2 + μ - κ) = 1 / 2 + μ + κ by ring, div_pow]
  have hp := cpow_first_parameter_prefactor_recip hx hy (1 / 2 + μ) (1 / 2 + μ + κ)
  rw [show (1 / 2 + μ + κ) - (1 / 2 + μ) = κ by ring] at hp
  have he : exp (-(x + y) / 2) * exp y = exp (y / 2) * exp (-x / 2) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  linear_combination (exp (-(x + y) / 2) * exp y *
    ((-y) ^ n / (n.factorial * (x + y) ^ n)) *
      kummerU (1 / 2 + μ - κ - n) (1 + 2 * μ) x) * hp +
    ((x / (x + y)) ^ κ * x ^ (1 / 2 + μ) *
      ((-y) ^ n / (n.factorial * (x + y) ^ n)) *
      kummerU (1 / 2 + μ - κ - n) (1 + 2 * μ) x) * he

end DLMF.Confluent
