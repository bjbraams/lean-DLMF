/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Scorer

/-!
# Tools for the Airy integrals of DLMF §9.10

* `airyInt_primitive_ofReal`: the entire primitive on the real axis is an interval integral.
* Elementary bounds for the Scorer function `Hi` and `Hi'` in the left half-plane, from the
  Laplace integral 9.12.20, and for `Gi`, `Gi'` on the positive axis, from the rotation
  formula 9.12.12.
* The oscillatory expansions 9.7.9–9.7.12 restricted to the positive real axis, giving the
  growth `Ai(-s), Bi(-s) = O(s^{-1/4})`, `Ai'(-s), Bi'(-s) = O(s^{1/4})` and the leading
  terms of `Ai'(-s)`, `Bi'(-s)` with an `O(s^{-5/4})` error.
* `airyInt_hasIntegralAtBot_of_cross` and `airyInt_cross_expansion`: the improper integrals
  at `-∞` and their asymptotics, via the Scorer identities 9.10.2–9.10.3.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent
open scoped Real Topology
namespace DLMF.Airy

/-- For an entire integrand, the primitive at a real point is the interval integral. -/
theorem airyInt_primitive_ofReal {f : ℂ → ℂ} (hf : Differentiable ℂ f) (x : ℝ) :
    primitive f x = ∫ t in (0 : ℝ)..x, f t := by
  obtain ⟨g, hg⟩ := hf.isExactOn_univ
  have hg' (w : ℂ) : HasDerivAt g (f w) w := hg w (mem_univ w)
  have h1 : primitive f x = g x - g 0 := by
    have hd (t : ℝ) : HasDerivAt (fun u : ℝ => g (u * (x : ℂ))) ((x : ℂ) * f (t * x)) t := by
      have h := ((hg' (t * x)).comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).mul_const (x : ℂ))).comp_ofReal
      simpa [mul_comm] using h
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((continuous_const.mul (hf.continuous.comp (continuous_ofReal.mul continuous_const))).intervalIntegrable 0 1)
    rw [intervalIntegral.integral_const_mul] at h
    simpa [primitive, segmentIntegral] using h
  rw [h1, intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => g t)
    (fun t _ => (hg' t).comp_ofReal)
    ((hf.continuous.comp continuous_ofReal).intervalIntegrable _ _)]
  simp

/-- `∫₀^∞ t^m e^{-st} dt = m!/s^{m+1}`. -/
theorem airyInt_integral_pow_mul_exp_neg (m : ℕ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => t ^ m * Real.exp (-(s * t))) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), t ^ m * Real.exp (-(s * t)) = (Nat.factorial m : ℝ) / s ^ (m + 1) := by
  have he : (fun t : ℝ => t ^ m * Real.exp (-(s * t))) =ᵐ[volume.restrict (Ioi 0)]
      fun t : ℝ => t ^ ((m + 1 : ℝ) - 1) * Real.exp (-(s * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    rw [add_sub_cancel_right, Real.rpow_natCast]
  constructor
  · have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (m : ℝ)) (p := 1) (b := s)
      (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) one_pos hs
    refine h.congr_fun (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
    simp [Real.rpow_natCast]
  · rw [integral_congr_ae he, Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hs,
      show (m + 1 : ℝ) = ((m + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
      show ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 by push_cast; ring, Real.Gamma_nat_eq_factorial,
      one_div, inv_pow]
    ring

/-- The Laplace integrand of Hi is dominated by `t^m e^{-st}` when `Re w ≤ -s`. -/
theorem airyInt_norm_integral_cubic_le (m : ℕ) {w : ℂ} {s : ℝ} (hs : 0 < s) (hw : w.re ≤ -s) :
    ‖∫ t : ℝ in Ioi 0, (t : ℂ) ^ m * exp (-(t : ℂ) ^ 3 / 3 + w * t)‖ ≤
      (Nat.factorial m : ℝ) / s ^ (m + 1) := by
  obtain ⟨hi, hv⟩ := airyInt_integral_pow_mul_exp_neg m hs
  rw [← hv]
  refine norm_integral_le_of_norm_le hi ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  rw [norm_mul, norm_pow, norm_real, Real.norm_of_nonneg ht.le, norm_exp]
  have hre : (-(t : ℂ) ^ 3 / 3 + w * t).re = -(t ^ 3 / 3) + w.re * t := by
    simp [pow_succ]; ring
  rw [hre]
  gcongr
  nlinarith [pow_pos ht 3]

/-- `‖Hi(w)‖ ≤ 1/(πs)` when `Re w ≤ -s < 0`. -/
theorem airyInt_norm_scorerHi_le {w : ℂ} {s : ℝ} (hs : 0 < s) (hw : w.re ≤ -s) :
    ‖scorerHi w‖ ≤ 1 / (π * s) := by
  rw [(scorerHi_exp_integral w).2, norm_div, norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have h := airyInt_norm_integral_cubic_le 0 hs hw
  simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one] at h
  rw [div_le_iff₀ Real.pi_pos]
  calc _ ≤ 1 / s := h
    _ = 1 / (π * s) * π := by field_simp

/-- `‖Hi'(w)‖ ≤ 1/(πs²)` when `Re w ≤ -s < 0`. -/
theorem airyInt_norm_scorerHiDeriv_le {w : ℂ} {s : ℝ} (hs : 0 < s) (hw : w.re ≤ -s) :
    ‖scorerHiDeriv w‖ ≤ 1 / (π * s ^ 2) := by
  rw [scorerHiDeriv_exp_integral w, norm_div, norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have h := airyInt_norm_integral_cubic_le 1 hs hw
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at h
  rw [div_le_iff₀ Real.pi_pos]
  calc _ ≤ 1 / s ^ 2 := h
    _ = 1 / (π * s ^ 2) * π := by field_simp

/-- `Hi(-s) = 1/(πs) + O(s^{-4})`, with the explicit bound `2/(πs⁴)`. -/
theorem airyInt_norm_scorerHi_neg_sub_le {s : ℝ} (hs : 0 < s) :
    ‖scorerHi (-(s : ℂ)) - 1 / (π * s)‖ ≤ 2 / (π * s ^ 4) := by
  have hpi := Real.pi_pos
  obtain ⟨h0i, h0v⟩ := airyInt_integral_pow_mul_exp_neg 0 hs
  obtain ⟨h3i, h3v⟩ := airyInt_integral_pow_mul_exp_neg 3 hs
  have hJ := integral_pow_mul_exp_cubic_ofReal 0 (-s)
  simp only [pow_zero, one_mul] at hJ h0i h0v
  have hJi : IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 3 / 3) + -s * t)) (Ioi 0) := by
    have := (integrableOn_pow_mul_exp_cubic 0 (-(s : ℂ))).re
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [pow_zero, one_mul]
    rw [RCLike.re_to_complex, show (-(t : ℂ) ^ 3 / 3 + -(s : ℂ) * t) =
      ((-(t ^ 3 / 3) + -s * t : ℝ) : ℂ) by push_cast; ring, ← ofReal_exp, ofReal_re]
  rw [(scorerHi_exp_integral _).2, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring, hJ]
  have hkey : (∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 3 / 3) + -s * t)) - 1 / s =
      ∫ t in Ioi (0 : ℝ), (Real.exp (-(t ^ 3 / 3) + -s * t) - Real.exp (-(s * t))) := by
    rw [integral_sub hJi h0i, h0v]; simp
  have hb : |∫ t in Ioi (0 : ℝ), (Real.exp (-(t ^ 3 / 3) + -s * t) - Real.exp (-(s * t)))| ≤
      2 / s ^ 4 := by
    have hc : ∫ t in Ioi (0 : ℝ), (1 / 3 : ℝ) * (t ^ 3 * Real.exp (-(s * t))) = 2 / s ^ 4 := by
      rw [integral_const_mul, h3v]; norm_num [Nat.factorial]; ring
    rw [← hc, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (h3i.const_mul _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    rw [Real.norm_eq_abs, abs_of_nonpos]
    · have e : Real.exp (-(t ^ 3 / 3) + -s * t) = Real.exp (-(t ^ 3 / 3)) * Real.exp (-(s * t)) := by
        rw [← Real.exp_add]; ring_nf
      rw [e]
      have := Real.add_one_le_exp (-(t ^ 3 / 3))
      have hp := Real.exp_pos (-(s * t))
      nlinarith
    · have : Real.exp (-(t ^ 3 / 3) + -s * t) ≤ Real.exp (-(s * t)) :=
        Real.exp_le_exp.mpr (by nlinarith [pow_pos ht 3])
      linarith
  have e2 : ((∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 3 / 3) + -s * t) : ℝ) : ℂ) / π - 1 / (π * s) =
      (((∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 3 / 3) + -s * t)) - 1 / s) / π : ℝ) := by
    push_cast; field_simp
  rw [e2, norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hpi, hkey]
  calc _ ≤ 2 / s ^ 4 / π := by gcongr
    _ = _ := by rw [div_div, mul_comm]

/-- `Hi(-s) = O(s^{-1})` as `s → ∞`. -/
theorem airyInt_scorerHi_neg_isBigO :
    (fun s : ℝ => scorerHi (-(s : ℂ))) =O[atTop] (fun s : ℝ => s ^ (-1 : ℝ)) := by
  refine IsBigO.of_bound (1 / π) ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg_one]
  calc _ ≤ 1 / (π * s) := airyInt_norm_scorerHi_le hs (by simp)
    _ = _ := by field_simp

/-- `Hi'(-s) = O(s^{-2})` as `s → ∞`. -/
theorem airyInt_scorerHiDeriv_neg_isBigO :
    (fun s : ℝ => scorerHiDeriv (-(s : ℂ))) =O[atTop] (fun s : ℝ => s ^ (-2 : ℝ)) := by
  refine IsBigO.of_bound (1 / π) ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg hs.le,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc _ ≤ 1 / (π * s ^ 2) := airyInt_norm_scorerHiDeriv_le hs (by simp)
    _ = _ := by field_simp

/-- The Scorer cross combination `f Hi' - f' Hi` tends to zero at `-∞` whenever
`f(-s) = O(s^{-1/4})` and `f'(-s) = O(s^{1/4})`. -/
theorem airyInt_tendsto_cross_atBot {f f' : ℂ → ℂ}
    (hf : (fun s : ℝ => f (-(s : ℂ))) =O[atTop] (fun s : ℝ => s ^ (-(1 / 4) : ℝ)))
    (hf' : (fun s : ℝ => f' (-(s : ℂ))) =O[atTop] (fun s : ℝ => s ^ (1 / 4 : ℝ))) :
    Tendsto (fun x : ℝ => f x * scorerHiDeriv x - f' x * scorerHi x) atBot (𝓝 0) := by
  have h1 : Tendsto (fun s : ℝ => f (-(s : ℂ)) * scorerHiDeriv (-(s : ℂ))) atTop (𝓝 0) := by
    refine (hf.mul airyInt_scorerHiDeriv_neg_isBigO).trans_tendsto ?_
    have := (tendsto_rpow_neg_atTop (y := 1 / 4) (by norm_num)).mul
      (tendsto_rpow_neg_atTop (y := 2) (by norm_num))
    simpa using this
  have h2 : Tendsto (fun s : ℝ => f' (-(s : ℂ)) * scorerHi (-(s : ℂ))) atTop (𝓝 0) := by
    refine (hf'.mul airyInt_scorerHi_neg_isBigO).trans_tendsto ?_
    refine (tendsto_rpow_neg_atTop (y := 3 / 4) (by norm_num)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    rw [← Real.rpow_add hs]; norm_num
  have h := (h1.sub h2).comp tendsto_neg_atBot_atTop
  simp only [sub_zero] at h
  refine h.congr fun x => ?_
  simp

/-- An improper integral at `-∞` obtained from a Scorer-type identity
`c + ∫₀ˣ f = π g(x)` with `g → 0` at `-∞`. -/
theorem airyInt_hasIntegralAtBot_of_cross {f g : ℂ → ℂ} (hfd : Differentiable ℂ f) {c : ℂ}
    (hid : ∀ x : ℝ, c + primitive f x = π * g x)
    (hg : Tendsto (fun x : ℝ => g x) atBot (𝓝 0)) (x : ℝ) :
    HasIntegralAtBot (fun t => f t) x (c + primitive f x) := by
  have hc : Continuous fun t : ℝ => f t := hfd.continuous.comp continuous_ofReal
  have he : ∀ R : ℝ, ∫ t in R..x, f t = primitive f x - (π * g R - c) := by
    intro R
    rw [← intervalIntegral.integral_interval_sub_left (a := 0) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _), ← airyInt_primitive_ofReal hfd, ← airyInt_primitive_ofReal hfd,
      ← hid R]
    ring
  unfold HasIntegralAtBot
  simp only [he]
  have := ((hg.const_mul (π : ℂ)).sub_const c).const_sub (primitive f x)
  simpa [add_comm] using this

/-- If `g - c s^{1/4} φ = O(s^{-5/4})` with `|φ| ≤ 1`, then `g = O(s^{1/4})`. -/
theorem airyInt_isBigO_rpow_of_sub {g : ℝ → ℂ} {φ : ℝ → ℝ} (hg : (fun s : ℝ => g s -
      ((s ^ (1 / 4 : ℝ) / Real.sqrt π * φ s : ℝ) : ℂ)) =O[atTop] (fun s : ℝ => s ^ (-(5 / 4) : ℝ)))
    (hφ : ∀ s, |φ s| ≤ 1) : g =O[atTop] (fun s : ℝ => s ^ (1 / 4 : ℝ)) := by
  have h1 : (fun s : ℝ => ((s ^ (1 / 4 : ℝ) / Real.sqrt π * φ s : ℝ) : ℂ)) =O[atTop]
      (fun s : ℝ => s ^ (1 / 4 : ℝ)) := by
    refine IsBigO.of_bound ((Real.sqrt π)⁻¹) ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    rw [norm_real, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity), abs_mul,
      abs_div, abs_of_pos (Real.rpow_pos_of_pos hs _), abs_of_pos (Real.sqrt_pos.2 Real.pi_pos)]
    have := hφ s
    have h0 : 0 ≤ s ^ (1 / 4 : ℝ) / Real.sqrt π := by positivity
    calc s ^ (1 / 4 : ℝ) / Real.sqrt π * |φ s| ≤ s ^ (1 / 4 : ℝ) / Real.sqrt π * 1 := by gcongr
      _ = _ := by ring
  have h2 : (fun s : ℝ => s ^ (-(5 / 4) : ℝ)) =O[atTop] (fun s : ℝ => s ^ (1 / 4 : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with s hs
    have hs0 : 0 < s := by linarith
    rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hs (by norm_num)
  exact ((hg.trans h2).add h1).congr_left fun s => by ring

/-- The Scorer cross combination with its leading oscillatory term removed. -/
theorem airyInt_cross_expansion {f f' : ℂ → ℂ} {φ : ℝ → ℝ} (hφ : ∀ s, |φ s| ≤ 1)
    (hf : (fun s : ℝ => f (-(s : ℂ))) =O[atTop] (fun s : ℝ => s ^ (-(1 / 4) : ℝ)))
    (hf' : (fun s : ℝ => f' (-(s : ℂ)) - ((s ^ (1 / 4 : ℝ) / Real.sqrt π * φ s : ℝ) : ℂ))
      =O[atTop] (fun s : ℝ => s ^ (-(5 / 4) : ℝ))) :
    (fun s : ℝ => π * (f (-(s : ℂ)) * scorerHiDeriv (-(s : ℂ)) -
        f' (-(s : ℂ)) * scorerHi (-(s : ℂ))) +
        ((s ^ (-(3 / 4) : ℝ) / Real.sqrt π * φ s : ℝ) : ℂ))
      =O[atTop] (fun s : ℝ => s ^ (-(9 / 4) : ℝ)) := by
  have hπ := Real.pi_pos
  set D := fun s : ℝ => f' (-(s : ℂ)) - ((s ^ (1 / 4 : ℝ) / Real.sqrt π * φ s : ℝ) : ℂ)
  set E := fun s : ℝ => (π : ℂ) * scorerHi (-(s : ℂ)) - 1 / s
  have hE : E =O[atTop] (fun s : ℝ => s ^ (-4 : ℝ)) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    have h := airyInt_norm_scorerHi_neg_sub_le hs
    have e : E s = π * (scorerHi (-(s : ℂ)) - 1 / (π * s)) := by
      simp only [E]; field_simp
    rw [e, norm_mul, norm_real, Real.norm_of_nonneg hπ.le, Real.norm_of_nonneg (by positivity),
      Real.rpow_neg hs.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc π * ‖scorerHi (-(s : ℂ)) - 1 / (π * s)‖ ≤ π * (2 / (π * s ^ 4)) := by gcongr
      _ = 2 * (s ^ 4)⁻¹ := by field_simp
  have hf'0 := airyInt_isBigO_rpow_of_sub hf' hφ
  -- decomposition
  have key : ∀ s : ℝ, 0 < s → π * (f (-(s : ℂ)) * scorerHiDeriv (-(s : ℂ)) -
      f' (-(s : ℂ)) * scorerHi (-(s : ℂ))) +
      ((s ^ (-(3 / 4) : ℝ) / Real.sqrt π * φ s : ℝ) : ℂ) =
      π * (f (-(s : ℂ)) * scorerHiDeriv (-(s : ℂ))) - D s * (1 / s) - f' (-(s : ℂ)) * E s := by
    intro s hs
    have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
    have hr : (s : ℝ) ^ (-(3 / 4) : ℝ) = s ^ (1 / 4 : ℝ) / s := by
      rw [show (-(3 / 4) : ℝ) = 1 / 4 - 1 by norm_num, Real.rpow_sub hs, Real.rpow_one]
    simp only [D, E]
    rw [hr]; push_cast
    field_simp
    ring
  have t1 : (fun s : ℝ => π * (f (-(s : ℂ)) * scorerHiDeriv (-(s : ℂ)))) =O[atTop]
      (fun s : ℝ => s ^ (-(9 / 4) : ℝ)) := by
    refine ((hf.mul airyInt_scorerHiDeriv_neg_isBigO).const_mul_left (π : ℂ)).congr' ?_ ?_
    · exact Eventually.of_forall fun s => by simp
    · filter_upwards [eventually_gt_atTop 0] with s hs
      rw [← Real.rpow_add hs]; norm_num
  have t2 : (fun s : ℝ => D s * (1 / s)) =O[atTop] (fun s : ℝ => s ^ (-(9 / 4) : ℝ)) := by
    have h1 : (fun s : ℝ => (1 / s : ℂ)) =O[atTop] (fun s : ℝ => s ^ (-1 : ℝ)) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_gt_atTop 0] with s hs
      rw [Real.rpow_neg_one, one_mul, Real.norm_of_nonneg (by positivity)]
      simp [abs_of_pos hs]
    refine (hf'.mul h1).congr' (Eventually.of_forall fun s => rfl) ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    rw [← Real.rpow_add hs]; norm_num
  have t3 : (fun s : ℝ => f' (-(s : ℂ)) * E s) =O[atTop] (fun s : ℝ => s ^ (-(9 / 4) : ℝ)) := by
    refine (hf'0.mul hE).trans ?_
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with s hs
    have hs0 : 0 < s := by linarith
    rw [← Real.rpow_add hs0, one_mul, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hs (by norm_num)
  refine ((t1.sub t2).sub t3).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with s hs
  exact (key s hs).symm

/-- `‖e^{cπi}‖ = 1` for real `c`. -/
theorem airyInt_norm_exp_pi_I_mul (c : ℝ) : ‖exp ((c : ℂ) * π * I)‖ = 1 := by
  rw [show (c : ℂ) * π * I = ((c * π : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I]

/-- Real parts of `x e^{∓2πi/3}`. -/
theorem airyInt_re_mul_omega {x : ℝ} :
    ((x : ℂ) * exp (-2 * π * I / 3)).re = -(x / 2) ∧
      ((x : ℂ) * exp (2 * π * I / 3)).re = -(x / 2) := by
  rw [exp_neg_two_pi_I_div_three', exp_two_pi_I_div_three]
  constructor <;> simp <;> ring

/-- Norms of the rotation factors in the Scorer connection formulas. -/
theorem airyInt_norm_rot :
    ‖exp (π * I / 3) / 2‖ = 1 / 2 ∧ ‖exp (-π * I / 3) / 2‖ = 1 / 2 ∧
      ‖exp (-2 * π * I / 3)‖ = 1 ∧ ‖exp (2 * π * I / 3)‖ = 1 := by
  have e1 : π * I / 3 = ((1 / 3 : ℝ) : ℂ) * π * I := by push_cast; ring
  have e2 : -π * I / 3 = ((-1 / 3 : ℝ) : ℂ) * π * I := by push_cast; ring
  have e3 : -2 * π * I / 3 = ((-2 / 3 : ℝ) : ℂ) * π * I := by push_cast; ring
  have e4 : 2 * π * I / 3 = ((2 / 3 : ℝ) : ℂ) * π * I := by push_cast; ring
  rw [e1, e2, e3, e4, norm_div, norm_div, airyInt_norm_exp_pi_I_mul, airyInt_norm_exp_pi_I_mul,
    airyInt_norm_exp_pi_I_mul, airyInt_norm_exp_pi_I_mul]
  norm_num

/-- `|Gi(x)| ≤ 2/(πx)` for `x > 0`. -/
theorem airyInt_norm_scorerGi_le {x : ℝ} (hx : 0 < x) : ‖scorerGi x‖ ≤ 2 / (π * x) := by
  have hx2 : 0 < x / 2 := by linarith
  obtain ⟨n1, n2, -, -⟩ := airyInt_norm_rot
  obtain ⟨r1, r2⟩ := airyInt_re_mul_omega (x := x)
  have b1 := airyInt_norm_scorerHi_le hx2 r1.le
  have b2 := airyInt_norm_scorerHi_le hx2 r2.le
  rw [scorerGi_rotations]
  calc _ ≤ ‖exp (π * I / 3) / 2 * scorerHi (x * exp (-2 * π * I / 3))‖ +
        ‖exp (-π * I / 3) / 2 * scorerHi (x * exp (2 * π * I / 3))‖ := norm_add_le _ _
    _ ≤ 1 / 2 * (1 / (π * (x / 2))) + 1 / 2 * (1 / (π * (x / 2))) := by
        rw [norm_mul, norm_mul, n1, n2]; gcongr
    _ = _ := by field_simp; ring

/-- `|Gi'(x)| ≤ 4/(πx²)` for `x > 0`. -/
theorem airyInt_norm_scorerGiDeriv_le {x : ℝ} (hx : 0 < x) : ‖scorerGiDeriv x‖ ≤ 4 / (π * x ^ 2) := by
  have hx2 : 0 < x / 2 := by linarith
  obtain ⟨n1, n2, n3, n4⟩ := airyInt_norm_rot
  obtain ⟨r1, r2⟩ := airyInt_re_mul_omega (x := x)
  have b1 := airyInt_norm_scorerHiDeriv_le hx2 r1.le
  have b2 := airyInt_norm_scorerHiDeriv_le hx2 r2.le
  rw [scorerAsym_scorerGiDeriv_rotations]
  calc _ ≤ ‖exp (π * I / 3) / 2 * (scorerHiDeriv (x * exp (-2 * π * I / 3)) *
        exp (-2 * π * I / 3))‖ + ‖exp (-π * I / 3) / 2 * (scorerHiDeriv (x * exp (2 * π * I / 3)) *
        exp (2 * π * I / 3))‖ := norm_add_le _ _
    _ ≤ 1 / 2 * (1 / (π * (x / 2) ^ 2) * 1) + 1 / 2 * (1 / (π * (x / 2) ^ 2) * 1) := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, n1, n2, n3, n4]; gcongr
    _ = _ := by field_simp; ring

/-- `|Ai(x)| ≤ 1` for `x ≥ 1`. -/
theorem airyInt_norm_airyAi_le {x : ℝ} (hx : 1 ≤ x) : ‖airyAi x‖ ≤ 1 := by
  have hx0 : 0 < x := by linarith
  have h := (airy_ai_real_error hx0 (N := 0) le_rfl).1
  simp only [airyRemainder, airyExponentialSum, Finset.range_zero, Finset.sum_empty, sub_zero,
    airyExpansionCoeff, pow_zero, div_one, one_mul, airyReal_airyU_zero, ofReal_one, norm_one,
    airyFunction] at h
  have hp : airyPrefactor .ai x ≠ 0 := airyRot_prefactor_ne_zero .ai (ofReal_ne_zero.mpr hx0.ne')
  have hpn : ‖airyPrefactor .ai x‖ ≤ 1 := by
    rw [airyReal_norm_prefactor_ai hx0]
    have h1 : Real.exp (-airyZeta x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [airyZeta_pos hx0])
    have h2 : 1 ≤ 2 * Real.sqrt π * x ^ (1 / 4 : ℝ) := by
      have := Real.one_le_rpow hx (by norm_num : (0 : ℝ) ≤ 1 / 4)
      have hs : 1 ≤ Real.sqrt π := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
      nlinarith
    rw [div_le_one (by linarith)]; linarith
  calc ‖airyAi x‖ = ‖airyPrefactor .ai x‖ * ‖airyAi x / airyPrefactor .ai x‖ := by
        rw [← norm_mul, mul_div_cancel₀ _ hp]
    _ ≤ 1 * 1 := by gcongr
    _ = 1 := by ring

/-- `|Ai'(x)| ≤ 2 x^{1/4}` for `x ≥ 1`. -/
theorem airyInt_norm_airyAiDeriv_le {x : ℝ} (hx : 1 ≤ x) : ‖airyAiDeriv x‖ ≤ 2 * x ^ (1 / 4 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have h := airy_aiDeriv_bound hx0
  rw [airyAiDeriv_ofReal_eq, norm_real, Real.norm_eq_abs]
  have hz := airyInt_two_thirds_le_airyZeta hx
  have h1 : Real.exp (-airyZeta x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hs : 1 ≤ Real.sqrt π := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have h3 : 7 / (72 * airyZeta x) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hq : 0 ≤ x ^ (1 / 4 : ℝ) := by positivity
  calc _ ≤ _ := h
    _ ≤ x ^ (1 / 4 : ℝ) * 1 / (2 * 1) * (1 + 1) := by gcongr
    _ ≤ 2 * x ^ (1 / 4 : ℝ) := by linarith

/-- `Ai Gi' - Ai' Gi → 0` at `+∞`. -/
theorem airyInt_tendsto_cross_gi_atTop :
    Tendsto (fun x : ℝ => airyAi x * scorerGiDeriv x - airyAiDeriv x * scorerGi x) atTop (𝓝 0) := by
  have hπ := Real.pi_pos
  have hA : (fun x : ℝ => airyAi x) =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    simpa using airyInt_norm_airyAi_le hx
  have hA' : (fun x : ℝ => airyAiDeriv x) =O[atTop] (fun x : ℝ => x ^ (1 / 4 : ℝ)) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact airyInt_norm_airyAiDeriv_le hx
  have hG : (fun x : ℝ => scorerGi x) =O[atTop] (fun x : ℝ => x ^ (-1 : ℝ)) := by
    refine IsBigO.of_bound (2 / π) ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg_one]
    calc _ ≤ 2 / (π * x) := airyInt_norm_scorerGi_le hx
      _ = _ := by field_simp
  have hG' : (fun x : ℝ => scorerGiDeriv x) =O[atTop] (fun x : ℝ => x ^ (-2 : ℝ)) := by
    refine IsBigO.of_bound (4 / π) ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg hx.le,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc _ ≤ 4 / (π * x ^ 2) := airyInt_norm_scorerGiDeriv_le hx
      _ = _ := by field_simp
  have h1 : Tendsto (fun x : ℝ => airyAi x * scorerGiDeriv x) atTop (𝓝 0) := by
    refine (hA.mul hG').trans_tendsto ?_
    simpa using tendsto_rpow_neg_atTop (y := 2) (by norm_num)
  have h2 : Tendsto (fun x : ℝ => airyAiDeriv x * scorerGi x) atTop (𝓝 0) := by
    refine (hA'.mul hG).trans_tendsto ?_
    refine (tendsto_rpow_neg_atTop (y := 3 / 4) (by norm_num)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    rw [← Real.rpow_add hs]; norm_num
  simpa using h1.sub h2

/-- `u - v = O(|v| x^{-c})` with `c > 0` gives `u ~ v`. -/
theorem airyInt_isEquivalent_of_isBigO {u v : ℝ → ℂ} {c : ℝ} (hc : 0 < c)
    (h : (fun x => u x - v x) =O[atTop] (fun x => ‖v x‖ * x ^ (-c))) : u ~[atTop] v := by
  have h1 : (fun x : ℝ => x ^ (-c)) =o[atTop] (fun _ : ℝ => (1 : ℝ)) :=
    isLittleO_one_iff ℝ |>.2 (tendsto_rpow_neg_atTop hc)
  have h2 := h1.mul_isBigO (isBigO_refl (fun x => ‖v x‖) atTop)
  simp only [one_mul] at h2
  have h3 : (fun x => ‖v x‖ * x ^ (-c)) =o[atTop] v :=
    (h2.congr_left fun x => mul_comm _ _).trans_isBigO (isBigO_norm_left.2 (isBigO_refl v atTop))
  exact h.trans_isLittleO h3

/-- On the real axis, `πGi(x) = 1/x + O(x^{-4})`. -/
theorem airyInt_scorerGi_sub_isBigO :
    (fun x : ℝ => scorerGi x - 1 / (π * x)) =O[atTop] (fun x : ℝ => x ^ (-4 : ℝ)) := by
  have hπ := Real.pi_pos
  have h := (scorerGi_asymptotic (δ := π / 6) (by positivity) (by linarith) 1)
  rw [comap_id'] at h
  have h' := h.comp_tendsto (airyInt_tendsto_ofReal_sector (α := π / 3 - π / 6) (by linarith))
  refine (h'.congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl).trans ?_
  · simp
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Function.comp_apply]
    rw [one_mul, Real.norm_of_nonneg (by positivity), show (-(3 * ((1 : ℕ) : ℂ) + 1)) =
      ((-4 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hx.le, norm_real,
      Real.norm_of_nonneg (by positivity)]

/-- Real-axis Poincaré bounds with one term: `w(x) = pref(x) + O(pref(x)/ζ)`. -/
theorem airyInt_poincare_real (kind : AiryKind) :
    (fun x : ℝ => airyFunction kind x - airyPrefactor kind x) =O[atTop]
      (fun x : ℝ => airyPrefactor kind x / airyZetaComplex x) := by
  have hπ := Real.pi_pos
  have hT := airyInt_tendsto_ofReal_sector (α := π / 3 - π / 6) (by linarith)
  have hT' : Tendsto (fun s : ℝ => (s : ℂ)) atTop (airySector (π - π / 6)) :=
    airyInt_tendsto_ofReal_sector (by linarith)
  have hs : ∀ z : ℂ, airyExponentialSum kind 1 z = 1 := fun z => by
    cases kind <;> simp [airyExponentialSum, airyExpansionCoeff, airyReal_airyU_zero,
      airyReal_airyV_zero]
  cases kind
  · have := (airy_ai_poincare (δ := π / 6) (by positivity) (by linarith) 1).comp_tendsto hT'
    simpa [hs, Function.comp_def] using this
  · have := (airy_aiDeriv_poincare (δ := π / 6) (by positivity) (by linarith) 1).comp_tendsto hT'
    simpa [hs, Function.comp_def] using this
  · have := (airy_bi_poincare (δ := π / 6) (by positivity) (by linarith) 1).comp_tendsto hT
    simpa [hs, Function.comp_def] using this
  · have := (airy_biDeriv_poincare (δ := π / 6) (by positivity) (by linarith) 1).comp_tendsto hT
    simpa [hs, Function.comp_def] using this

/-- `Gi(x) = O(x^{-1})` as `x → +∞`. -/
theorem airyInt_scorerGi_isBigO :
    (fun x : ℝ => scorerGi x) =O[atTop] (fun x : ℝ => x ^ (-1 : ℝ)) := by
  have hπ := Real.pi_pos
  refine IsBigO.of_bound (2 / π) ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg_one]
  calc _ ≤ 2 / (π * x) := airyInt_norm_scorerGi_le hx
    _ = _ := by field_simp

/-- `Gi'(x) = O(x^{-2})` as `x → +∞`. -/
theorem airyInt_scorerGiDeriv_isBigO :
    (fun x : ℝ => scorerGiDeriv x) =O[atTop] (fun x : ℝ => x ^ (-2 : ℝ)) := by
  have hπ := Real.pi_pos
  refine IsBigO.of_bound (4 / π) ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg hx.le,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc _ ≤ 4 / (π * x ^ 2) := airyInt_norm_scorerGiDeriv_le hx
    _ = _ := by field_simp

/-- The Scorer cross combination `π(A Gi' - A' Gi)` at `+∞`: if `A = O(x^{1/2}|v|)` and
`A' = -x v + O(x^{-1/2}|v|)`, then it is asymptotic to `v`. -/
theorem airyInt_cross_equiv_atTop {A A' v : ℝ → ℂ}
    (hA : A =O[atTop] (fun x => x ^ (1 / 2 : ℝ) * ‖v x‖))
    (hA' : (fun x => A' x + x * v x) =O[atTop] (fun x => x ^ (-(1 / 2) : ℝ) * ‖v x‖)) :
    (fun x : ℝ => π * (A x * scorerGiDeriv x - A' x * scorerGi x)) ~[atTop] v := by
  have hπ := Real.pi_pos
  refine airyInt_isEquivalent_of_isBigO (c := 3 / 2) (by norm_num) ?_
  have t1 := (hA.mul airyInt_scorerGiDeriv_isBigO).const_mul_left (π : ℂ)
  have t2 := (hA'.mul airyInt_scorerGi_isBigO).const_mul_left (π : ℂ)
  have hE : (fun x : ℝ => (π : ℂ) * scorerGi x - 1 / x) =O[atTop] (fun x : ℝ => x ^ (-4 : ℝ)) := by
    refine (airyInt_scorerGi_sub_isBigO.const_mul_left (π : ℂ)).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
    have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  have hxv : (fun x : ℝ => (x : ℂ) * v x) =O[atTop] (fun x : ℝ => x * ‖v x‖) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [one_mul, norm_mul, norm_real, Real.norm_of_nonneg hx.le, norm_mul,
      Real.norm_of_nonneg hx.le, norm_norm]
  have t3 := hxv.mul hE
  set W : ℝ → ℝ := fun x => ‖v x‖ * x ^ (-(3 / 2) : ℝ) with hW
  have b1 : (fun x : ℝ => x ^ (1 / 2 : ℝ) * ‖v x‖ * x ^ (-2 : ℝ)) =O[atTop] W := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with x hx0
    rw [one_mul, hW]; apply le_of_eq; congr 1
    rw [mul_comm (x ^ (1 / 2 : ℝ)), mul_assoc, ← Real.rpow_add hx0]; norm_num
  have b2 : (fun x : ℝ => x ^ (-(1 / 2) : ℝ) * ‖v x‖ * x ^ (-1 : ℝ)) =O[atTop] W := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with x hx0
    rw [one_mul, hW]; apply le_of_eq; congr 1
    rw [mul_comm (x ^ (-(1 / 2) : ℝ)), mul_assoc, ← Real.rpow_add hx0]; norm_num
  have b3 : (fun x : ℝ => x * ‖v x‖ * x ^ (-4 : ℝ)) =O[atTop] W := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    have hx0 : 0 < x := by linarith
    have : x * x ^ (-4 : ℝ) = x ^ (-3 : ℝ) := by
      rw [show x * x ^ (-4 : ℝ) = x ^ (1 : ℝ) * x ^ (-4 : ℝ) by rw [Real.rpow_one],
        ← Real.rpow_add hx0]; norm_num
    rw [one_mul, Real.norm_of_nonneg (by positivity : 0 ≤ x * ‖v x‖ * x ^ (-4 : ℝ)),
      Real.norm_of_nonneg (show 0 ≤ W x by simp only [hW]; positivity)]
    simp only [hW]
    rw [mul_comm x, mul_assoc, this]
    gcongr
    norm_num
  have hsum := ((t1.trans b1).sub (t2.trans b2)).add (t3.trans b3)
  refine hsum.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  field_simp
  ring

/-- Real-axis Poincaré bound with no terms: `w(x) = O(pref(x))`. -/
theorem airyInt_poincare0_real (kind : AiryKind) :
    (fun x : ℝ => airyFunction kind x) =O[atTop] (fun x : ℝ => airyPrefactor kind x) := by
  have hπ := Real.pi_pos
  have hT := airyInt_tendsto_ofReal_sector (α := π / 3 - π / 6) (by linarith)
  have hT' : Tendsto (fun s : ℝ => (s : ℂ)) atTop (airySector (π - π / 6)) :=
    airyInt_tendsto_ofReal_sector (by linarith)
  cases kind
  · have := (airy_ai_poincare (δ := π / 6) (by positivity) (by linarith) 0).comp_tendsto hT'
    simpa [airyExponentialSum, Function.comp_def] using this
  · have := (airy_aiDeriv_poincare (δ := π / 6) (by positivity) (by linarith) 0).comp_tendsto hT'
    simpa [airyExponentialSum, Function.comp_def] using this
  · have := (airy_bi_poincare (δ := π / 6) (by positivity) (by linarith) 0).comp_tendsto hT
    simpa [airyExponentialSum, Function.comp_def] using this
  · have := (airy_biDeriv_poincare (δ := π / 6) (by positivity) (by linarith) 0).comp_tendsto hT
    simpa [airyExponentialSum, Function.comp_def] using this

/-- `‖pref/ζ‖ = (3/2) x^{-3/2} ‖pref‖` on the positive axis. -/
theorem airyInt_norm_div_zeta (kind : AiryKind) {x : ℝ} (hx : 0 < x) :
    ‖airyPrefactor kind x / airyZetaComplex x‖ =
      3 / 2 * x ^ (-(3 / 2) : ℝ) * ‖airyPrefactor kind x‖ := by
  rw [norm_div, airyReal_zeta_ofReal hx, norm_real, Real.norm_of_nonneg (airyZeta_pos hx).le,
    div_eq_mul_inv, airyInt_airyZeta_recip hx]
  ring

/-- Elementary identities for the powers `x^{1/4}, x^{1/2}, x^{3/4}`. -/
theorem airyInt_quarter_rpow {x : ℝ} (hx : 0 < x) :
    x ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) = x ∧ x ^ (1 / 4 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ (3 / 4 : ℝ) ∧
      x ^ (1 / 4 : ℝ) * x ^ (-(3 / 2) : ℝ) * x ^ (3 / 4 : ℝ) = x ^ (-(1 / 2) : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Real.rpow_add hx]; norm_num
  · rw [← Real.rpow_add hx]; norm_num
  · rw [← Real.rpow_add hx, ← Real.rpow_add hx]; norm_num

/-- Norm of the prefactor of `Bi'(x)` on the positive axis. -/
theorem airyInt_norm_prefactor_biDeriv {x : ℝ} (hx : 0 < x) :
    ‖airyPrefactor .biDeriv x‖ = x ^ (1 / 4 : ℝ) * Real.exp (airyZeta x) / Real.sqrt π := by
  rw [airyPrefactor, norm_div, norm_mul, airyInt_norm_cpow_quarter hx, Complex.norm_exp,
    airyReal_zeta_ofReal hx, ofReal_re, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

end DLMF.Airy
