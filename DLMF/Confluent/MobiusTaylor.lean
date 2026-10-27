/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Recurrence
public import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Taylor expansions after a fractional linear change of variable

The map `w ↦ x / (1 - w)` converts first-parameter contiguous relations into
ordinary Taylor derivatives. Mathlib's complex Taylor theorem supplies convergence
on the unit disk, without an exchange of hypergeometric double series.
-/

@[expose] public section

open Complex Filter
open scoped Topology
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- The denominator of the fractional linear map has positive real part on the unit disk. -/
theorem re_one_sub_pos_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : 0 < (1 - w).re := by
  simp only [sub_re, one_re]
  linarith [re_le_norm w]

/-- A right-half-plane center stays on the principal branch under the disk map. -/
theorem div_one_sub_mem_slitPlane {x w : ℂ} (hx : 0 < x.re) (hw : ‖w‖ < 1) :
    x / (1 - w) ∈ slitPlane := by
  have hr := re_one_sub_pos_of_norm_lt_one hw
  have hd : 1 - w ≠ 0 := by intro h; simp [h] at hr
  rw [mem_slitPlane_iff]
  by_contra! h
  have he := congrArg re (div_mul_cancel₀ x hd)
  rw [mul_re, h.2, zero_mul, sub_zero] at he
  have := mul_nonpos_of_nonpos_of_nonneg h.1 hr.le
  linarith

/-- A contiguous differential relation yields a convergent Taylor expansion on the unit disk.
The coefficient recurrence permits zeros, so terminating numerator parameters are retained. -/
theorem mobius_taylor (F : ℕ → ℂ → ℂ) (C : ℕ → ℂ) (s x : ℂ)
    (hC0 : C 0 = 1)
    (hF : ∀ n w, ‖w‖ < 1 → DifferentiableAt ℂ (F n) (x / (1 - w)))
    (hstep : ∀ n w, ‖w‖ < 1 →
      C n * ((s + n) * F n (x / (1 - w)) +
        (x / (1 - w)) * deriv (F n) (x / (1 - w))) =
      C (n + 1) * F (n + 1) (x / (1 - w)))
    {v : ℂ} (hv : ‖v‖ < 1) :
    (1 - v) ^ (-s) * F 0 (x / (1 - v)) =
      ∑' n : ℕ, C n * F n x / n.factorial * v ^ n := by
  let G : ℕ → ℂ → ℂ := fun n w => C n * (1 - w) ^ (-s - n) * F n (x / (1 - w))
  have hG (n : ℕ) (w : ℂ) (hw : ‖w‖ < 1) :
      HasDerivAt (G n) (G (n + 1) w) w := by
    have hr := re_one_sub_pos_of_norm_lt_one hw
    have hd : 1 - w ≠ 0 := by intro h; simp [h] at hr
    have hp := ((hasDerivAt_id w).const_sub 1).cpow_const
      (c := -s - n) (Or.inl hr : 1 - w ∈ slitPlane)
    have hq := (hasDerivAt_const w x).div ((hasDerivAt_id w).const_sub 1) hd
    have hf := (hF n w hw).hasDerivAt.comp w hq
    have hh := (hp.const_mul (C n)).mul hf
    change HasDerivAt (G n) _ w at hh
    convert hh using 1
    dsimp only [G, id_eq, Function.comp_apply, Pi.div_apply]
    push_cast
    simp only [show -s - ((n : ℂ) + 1) = -s - n - 1 by ring,
      cpow_sub (x := 1 - w) (-s - (n : ℂ)) 1 hd, cpow_one]
    have he := hstep n w hw
    field_simp [hd] at he ⊢
    linear_combination -he
  have hi (n : ℕ) : ∀ w : ℂ, ‖w‖ < 1 → iteratedDeriv n (G 0) w = G n w := by
    induction n with
    | zero => intro w hw; rfl
    | succ n ih =>
      intro w hw
      have he : iteratedDeriv n (G 0) =ᶠ[𝓝 w] G n := by
        filter_upwards [Metric.isOpen_ball.mem_nhds (show w ∈ Metric.ball 0 1 by simpa using hw)] with u hu
        exact ih u (by simpa using hu)
      rw [iteratedDeriv_succ, he.deriv_eq, (hG n w hw).deriv]
  have ht := Complex.taylorSeries_eq_on_ball'
    (c := 0) (z := v) (r := 1) (by simpa using hv)
    (fun w hw => (hG 0 w (by simpa using hw)).differentiableAt.differentiableWithinAt)
  have he0 : G 0 = fun w => (1 - w) ^ (-s) * F 0 (x / (1 - w)) := by
    funext w; simp [G, hC0]
  change (fun w => (1 - w) ^ (-s) * F 0 (x / (1 - w))) v = _
  rw [← he0, ← ht]
  apply tsum_congr
  intro n
  rw [hi n 0 (by simp)]
  simp only [G, sub_zero, one_cpow, mul_one, div_one]
  ring

/-- First-parameter Kummer M expansion in the disk coordinate; no cut restriction on `x`. -/
theorem kummerM_mobius_taylor {a b x v : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (hv : ‖v‖ < 1) :
    (1 - v) ^ (-a) * kummerM a b (x / (1 - v)) =
      ∑' n : ℕ, poch a n * kummerM (a + n) b x / n.factorial * v ^ n := by
  simpa only [Nat.cast_zero, add_zero] using
    (mobius_taylor (fun n => kummerM (a + n) b) (poch a) a x (poch_zero a)
      (fun n w _ => ((analyticOnNhd_kummerM (a := a + n) hb) _ (Set.mem_univ _)).differentiableAt) (by
        intro n w hw
        rw [poch_succ]
        have h := z_mul_deriv_kummerM_eq_shift_a (a := a + n) hb (x / (1 - w))
        rw [show a + ((n + 1 : ℕ) : ℂ) = a + n + 1 by push_cast; ring]
        linear_combination (poch a n) * h) hv)

/-- First-parameter Tricomi U expansion in the disk coordinate. -/
theorem kummerU_mobius_taylor (a b : ℂ) {x v : ℂ} (hx : 0 < x.re) (hv : ‖v‖ < 1) :
    (1 - v) ^ (-a) * kummerU a b (x / (1 - v)) =
      ∑' n : ℕ, poch a n * poch (1 + a - b) n * kummerU (a + n) b x /
        n.factorial * v ^ n := by
  simpa only [Nat.cast_zero, add_zero] using
    (mobius_taylor (fun n => kummerU (a + n) b)
      (fun n => poch a n * poch (1 + a - b) n) a x (by simp [poch_zero])
      (fun n w hw => (hasDerivAt_kummerU _ _ (div_one_sub_mem_slitPlane hx hw)).differentiableAt) (by
        intro n w hw
        have hz := div_one_sub_mem_slitPlane hx hw
        rw [deriv_kummerU _ _ hz, poch_succ, poch_succ]
        have h1 := kummerU_contiguous_shift_a (a + n + 1) b _ (slitPlane_ne_zero hz)
        rw [add_sub_cancel_right] at h1
        rw [show a + ((n + 1 : ℕ) : ℂ) = a + n + 1 by push_cast; ring]
        linear_combination (poch a n * poch (1 + a - b) n * (a + n)) * h1) hv)

/-- The addition hypotheses put `y/(x+y)` strictly inside the unit disk. -/
theorem norm_div_add_lt_one {x y : ℂ} (hx : x ≠ 0) (hxy : x + y ≠ 0)
    (hy : -1 / 2 < (y / x).re) : ‖y / (x + y)‖ < 1 := by
  have hu : ‖y / x‖ < ‖1 + y / x‖ := by
    apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
    simp only [normSq_apply, add_re, add_im, one_re, one_im, zero_add]
    nlinarith
  have he : y / (x + y) = (y / x) / (1 + y / x) := by field_simp
  rw [he, norm_div]
  exact (div_lt_one (lt_of_le_of_lt (norm_nonneg _) hu)).mpr hu

/-- Undo the fractional linear coordinate, including its principal power prefactor. -/
theorem of_mobius_taylor {F : ℕ → ℂ → ℂ} {C : ℕ → ℂ} {s x y : ℂ}
    (hx : x ≠ 0) (hxy : x + y ≠ 0)
    (ht : (1 - y / (x + y)) ^ (-s) * F 0 (x / (1 - y / (x + y))) =
      ∑' n : ℕ, C n * F n x / n.factorial * (y / (x + y)) ^ n) :
    F 0 (x + y) = (x / (x + y)) ^ s *
      ∑' n : ℕ, C n * y ^ n / (n.factorial * (x + y) ^ n) * F n x := by
  have he : 1 - y / (x + y) = x / (x + y) := by field_simp; ring
  have hq : x / (x / (x + y)) = x + y := by field_simp
  rw [he, hq, cpow_neg] at ht
  have hp : (x / (x + y)) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (div_ne_zero hx hxy))
  have ht' := congrArg (fun z : ℂ => (x / (x + y)) ^ s * z) ht
  simp only [← mul_assoc, mul_inv_cancel₀ hp, one_mul] at ht'
  rw [ht']
  congr 1
  apply tsum_congr
  intro n
  rw [div_pow]
  ring

/-- Exponentially weighted first-parameter Tricomi expansion in the disk coordinate. -/
theorem kummerU_exp_mobius_taylor (a b : ℂ) {x v : ℂ} (hx : 0 < x.re) (hv : ‖v‖ < 1) :
    (1 - v) ^ (-(b - a)) * (exp (-(x / (1 - v))) * kummerU a b (x / (1 - v))) =
      ∑' n : ℕ, (-1 : ℂ) ^ n * (exp (-x) * kummerU (a - n) b x) / n.factorial * v ^ n := by
  simpa only [Nat.cast_zero, sub_zero] using
    (mobius_taylor (fun n z => exp (-z) * kummerU (a - n) b z)
      (fun n => (-1 : ℂ) ^ n) (b - a) x (by simp)
      (fun n w hw => (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => exp (-z)) _).mul
        (hasDerivAt_kummerU _ _ (div_one_sub_mem_slitPlane hx hw)).differentiableAt) (by
        intro n w hw
        have hz := div_one_sub_mem_slitPlane hx hw
        have hd := ((hasDerivAt_id (x / (1 - w))).neg.cexp).mul
          (hasDerivAt_kummerU (a - n) b hz)
        change HasDerivAt (fun z : ℂ => exp (-z) * kummerU (a - n) b z) _ _ at hd
        rw [hd.deriv, pow_succ]
        dsimp only [Pi.neg_apply, id_eq]
        have h1 := kummerU_contiguous_shift_a (a - n) b _ (slitPlane_ne_zero hz)
        have h2 := kummerU_contiguous_a_b (a - n) (b + 1) _ (slitPlane_ne_zero hz)
        rw [add_sub_cancel_right] at h2
        rw [show a - ((n + 1 : ℕ) : ℂ) = a - n - 1 by push_cast; ring]
        linear_combination ((-1 : ℂ) ^ n * exp (-(x / (1 - w)))) * h1 +
          ((-1 : ℂ) ^ n * exp (-(x / (1 - w))) * (x / (1 - w))) * h2) hv)

/-- Exponentially weighted first-parameter Kummer M expansion in the disk coordinate. -/
theorem kummerM_exp_mobius_taylor {a b x v : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (hv : ‖v‖ < 1) :
    (1 - v) ^ (-(b - a)) * (exp (-(x / (1 - v))) * kummerM a b (x / (1 - v))) =
      ∑' n : ℕ, poch (b - a) n * (exp (-x) * kummerM (a - n) b x) / n.factorial * v ^ n := by
  simpa only [Nat.cast_zero, sub_zero] using
    (mobius_taylor (fun n z => exp (-z) * kummerM (a - n) b z)
      (poch (b - a)) (b - a) x (poch_zero _)
      (fun n w hw => (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => exp (-z)) _).mul
        (((analyticOnNhd_kummerM (a := a - n) hb) _ (Set.mem_univ _)).differentiableAt)) (by
        intro n w hw
        have hd := ((hasDerivAt_id (x / (1 - w))).neg.cexp).mul
          (((analyticOnNhd_kummerM (a := a - n) hb) _ (Set.mem_univ _)).differentiableAt.hasDerivAt)
        change HasDerivAt (fun z : ℂ => exp (-z) * kummerM (a - n) b z) _ _ at hd
        rw [hd.deriv, poch_succ]
        dsimp only [Pi.neg_apply, id_eq]
        have h := z_mul_deriv_kummerM_eq_shift_a_pred (a := a - n) hb (x / (1 - w))
        rw [show a - ((n + 1 : ℕ) : ℂ) = a - n - 1 by push_cast; ring]
        linear_combination (poch (b - a) n * exp (-(x / (1 - w)))) * h) hv)

end DLMF.Confluent
