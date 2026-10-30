/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic.Definitions

public import DLMF.Theta.Identities
public import DLMF.Elliptic.ThetaAGM

/-!
# Theta constants and elliptic quarter periods

Nonvanishing theta constants and positivity of the elliptic quarter-period ratio prepare modulus
inversion.

Source references and common attribution are retained in
`DLMF.JacobiElliptic.Basic`.
-/

@[expose] public section

open Complex DLMF.Elliptic

open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

/-! ### Theta toolkit: nonvanishing of the theta constants and half-period shifts -/

open DLMF.QSeries DLMF.QSeries.TripleProduct in
/-- The triple-product form of `jacobiTheta₂`:
`jacobiTheta₂ a τ = (Q;Q)_∞ (w;Q)_∞ (Q/w;Q)_∞` with `Q = e^{2πiτ}`, `w = -e^{πiτ + 2πia}`. -/
lemma je22a_jacobiTheta₂_eq_prod (a : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta₂ a τ =
      qPochhammerInf (cexp (2 * π * I * τ)) (cexp (2 * π * I * τ)) *
        qPochhammerInf (-cexp (π * I * τ + 2 * π * I * a)) (cexp (2 * π * I * τ)) *
        qPochhammerInf (cexp (2 * π * I * τ) / -cexp (π * I * τ + 2 * π * I * a))
          (cexp (2 * π * I * τ)) := by
  set Q := cexp (2 * π * I * τ) with hQ
  set w := -cexp (π * I * τ + 2 * π * I * a) with hw
  have hQn : ‖Q‖ < 1 := by
    rw [hQ, Complex.norm_exp]
    simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero, I_re,
      mul_im, zero_mul, add_zero, I_im, mul_one, zero_sub]
    simpa using Real.exp_lt_exp.mpr (show -(2 * π * τ.im) < 0 by nlinarith [Real.pi_pos])
  have hwne : w ≠ 0 := neg_ne_zero.mpr (Complex.exp_ne_zero _)
  rw [jacobi_triple_product hQn hwne, jacobiTheta₂]
  refine tsum_congr fun n => ?_
  have ht : ((tri n : ℤ) : ℂ) = (n : ℂ) * ((n : ℂ) - 1) / 2 := by
    rw [eq_div_iff two_ne_zero]; exact_mod_cast tri_mul_two n
  rw [jacobiTheta₂_term, cpow_tri, hw, neg_eq_neg_one_mul (cexp _), mul_zpow, ← mul_assoc,
    mul_assoc ((-1 : ℂ) ^ n), mul_comm (Q ^ tri n), ← mul_assoc, ← mul_zpow,
    show ((-1 : ℂ) * -1) = 1 by norm_num, one_zpow, one_mul, hQ, ← Complex.exp_int_mul,
    ← Complex.exp_int_mul, ← Complex.exp_add, ht]
  congr 1
  ring

/-- `‖e^{iπτ}‖ < 1` for `Im τ > 0`. -/
lemma je22a_norm_exp_pi_I_mul_lt_one {c : ℝ} (hc : 0 < c) {τ : ℂ} (hτ : 0 < τ.im) :
    ‖cexp (c * π * I * τ)‖ < 1 := by
  rw [Complex.norm_exp]
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, I_re, mul_im, zero_mul, add_zero,
    I_im, mul_one, zero_sub]
  simpa using Real.exp_lt_exp.mpr (show -(c * π * τ.im) < 0 by
    have := Real.pi_pos; have : 0 < c * π * τ.im := by positivity
    linarith)

/-- `θ₃(0|τ) ≠ 0` for `Im τ > 0` (Jacobi triple product). -/
theorem je22a_thetaThree_zero_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : jacobiThetaThreeTau 0 τ ≠ 0 := by
  have hQ := je22a_norm_exp_pi_I_mul_lt_one (c := 2) two_pos hτ
  have hE := je22a_norm_exp_pi_I_mul_lt_one (c := 1) one_pos hτ
  simp only [ofReal_one, one_mul] at hE
  have hQ' : ‖cexp (2 * π * I * τ)‖ < 1 := by simpa using hQ
  rw [jacobiThetaThreeTau, zero_div, je22a_jacobiTheta₂_eq_prod 0 hτ]
  have hw : -cexp (π * I * τ + 2 * π * I * 0) = -cexp (π * I * τ) := by simp
  have hQw : cexp (2 * π * I * τ) / -cexp (π * I * τ) = -cexp (π * I * τ) := by
    rw [show (2 : ℂ) * π * I * τ = π * I * τ + π * I * τ by ring, exp_add]
    field_simp [Complex.exp_ne_zero]
  rw [hw, hQw]
  have h1 : ‖-cexp (π * I * τ)‖ < 1 := by rwa [norm_neg]
  exact mul_ne_zero (mul_ne_zero (DLMF.QSeries.qPochhammerInf_ne_zero_of_norm_lt_one hQ' hQ')
    (DLMF.QSeries.qPochhammerInf_ne_zero_of_norm_lt_one h1 hQ'))
    (DLMF.QSeries.qPochhammerInf_ne_zero_of_norm_lt_one h1 hQ')

/-- `θ₄(0|τ) ≠ 0` for `Im τ > 0` (Jacobi triple product). -/
theorem je22a_thetaFour_zero_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : jacobiThetaFourTau 0 τ ≠ 0 := by
  have hE := je22a_norm_exp_pi_I_mul_lt_one (c := 1) one_pos hτ
  simp only [ofReal_one, one_mul] at hE
  have hQ' : ‖cexp (2 * π * I * τ)‖ < 1 := by
    simpa using je22a_norm_exp_pi_I_mul_lt_one (c := 2) two_pos hτ
  rw [jacobiThetaFourTau, jacobiThetaThreeTau, zero_add,
    show (π : ℂ) / 2 / π = 1 / 2 by field_simp [pi_ne_zero'], je22a_jacobiTheta₂_eq_prod _ hτ]
  have hw : -cexp (π * I * τ + 2 * π * I * (1 / 2)) = cexp (π * I * τ) := by
    rw [show π * I * τ + 2 * π * I * (1 / 2) = π * I * τ + π * I by ring, exp_add, exp_pi_mul_I]
    ring
  have hQw : cexp (2 * π * I * τ) / cexp (π * I * τ) = cexp (π * I * τ) := by
    rw [show (2 : ℂ) * π * I * τ = π * I * τ + π * I * τ by ring, exp_add]
    field_simp [Complex.exp_ne_zero]
  rw [hw, hQw]
  exact mul_ne_zero (mul_ne_zero (DLMF.QSeries.qPochhammerInf_ne_zero_of_norm_lt_one hQ' hQ')
    (DLMF.QSeries.qPochhammerInf_ne_zero_of_norm_lt_one hE hQ'))
    (DLMF.QSeries.qPochhammerInf_ne_zero_of_norm_lt_one hE hQ')

/-- `θ₂(0|τ) ≠ 0` for `Im τ > 0` (Jacobi triple product). -/
theorem je22a_thetaTwo_zero_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : jacobiThetaTwoTau 0 τ ≠ 0 := by
  have hQ' : ‖cexp (2 * π * I * τ)‖ < 1 := by
    simpa using je22a_norm_exp_pi_I_mul_lt_one (c := 2) two_pos hτ
  rw [jacobiThetaTwoTau, jacobiThetaThreeTau, zero_add,
    show (π : ℂ) * τ / 2 / π = τ / 2 by field_simp [pi_ne_zero'], je22a_jacobiTheta₂_eq_prod _ hτ]
  have hw : -cexp (π * I * τ + 2 * π * I * (τ / 2)) = -cexp (2 * π * I * τ) := by
    congr 2; ring
  have hQw : cexp (2 * π * I * τ) / -cexp (2 * π * I * τ) = -1 := by
    field_simp [Complex.exp_ne_zero]
  rw [hw, hQw]
  refine mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (mul_ne_zero
    (DLMF.QSeries.qPochhammerInf_ne_zero_of_norm_lt_one hQ' hQ')
    (DLMF.QSeries.qPochhammerInf_ne_zero_of_norm_lt_one (by rwa [norm_neg]) hQ'))
    (DLMF.QSeries.qPochhammerInf_ne_zero hQ' fun n => ?_))
  rcases n with _ | n
  · norm_num
  · rw [neg_one_mul, sub_neg_eq_add]
    intro h
    have h1 : ‖cexp (2 * π * I * τ) ^ (n + 1)‖ = 1 := by
      rw [show cexp (2 * π * I * τ) ^ (n + 1) = -1 by linear_combination h, norm_neg, norm_one]
    rw [norm_pow] at h1
    have : ‖cexp (2 * π * I * τ)‖ ^ (n + 1) < 1 := pow_lt_one₀ (norm_nonneg _) hQ' (by omega)
    linarith

/-- `θ₁(0|τ) = 0`. -/
theorem je22a_thetaOne_zero (τ : ℂ) : jacobiThetaOneTau 0 τ = 0 := by
  have h := jacobiThetaOneTau_neg 0 τ
  rw [neg_zero] at h
  exact CharZero.eq_neg_self_iff.mp h

/-- `θ₁(ζ + π/2) = θ₂(ζ)`. -/
theorem je22a_thetaOne_add_half_pi (ζ τ : ℂ) :
    jacobiThetaOneTau (ζ + π / 2) τ = jacobiThetaTwoTau ζ τ := by
  rw [jacobiThetaOneTau, show ζ + π / 2 + π / 2 = ζ + π by ring, jacobiThetaTwoTau_add_pi, neg_neg]

/-- `θ₂(ζ + π/2) = -θ₁(ζ)`. -/
theorem je22a_thetaTwo_add_half_pi (ζ τ : ℂ) :
    jacobiThetaTwoTau (ζ + π / 2) τ = -jacobiThetaOneTau ζ τ := by
  rw [jacobiThetaOneTau, neg_neg]

/-- `θ₃(ζ + π/2) = θ₄(ζ)`. -/
theorem je22a_thetaThree_add_half_pi (ζ τ : ℂ) :
    jacobiThetaThreeTau (ζ + π / 2) τ = jacobiThetaFourTau ζ τ := rfl

/-- `θ₄(ζ + π/2) = θ₃(ζ)`. -/
theorem je22a_thetaFour_add_half_pi (ζ τ : ℂ) :
    jacobiThetaFourTau (ζ + π / 2) τ = jacobiThetaThreeTau ζ τ := by
  rw [jacobiThetaFourTau, show ζ + π / 2 + π / 2 = ζ + π by ring, jacobiThetaThreeTau_add_pi]

/-- The multiplier `e^{-iπτ/4 - iζ}` of the half-period shift `ζ ↦ ζ + πτ/2`. -/
def je22a_shiftFactor (ζ τ : ℂ) : ℂ := cexp (-(π * I * τ / 4 + I * ζ))

/-- Nonvanishing under the stated hypotheses: `je22a_shiftFactor ζ τ ≠ 0`. -/
theorem je22a_shiftFactor_ne_zero (ζ τ : ℂ) : je22a_shiftFactor ζ τ ≠ 0 := Complex.exp_ne_zero _

/-- `θ₃(ζ + πτ/2) = e^{-iπτ/4-iζ} θ₂(ζ)`. -/
theorem je22a_thetaThree_add_half_tau (ζ τ : ℂ) :
    jacobiThetaThreeTau (ζ + π * τ / 2) τ = je22a_shiftFactor ζ τ * jacobiThetaTwoTau ζ τ := by
  rw [jacobiThetaTwoTau, je22a_shiftFactor, ← mul_assoc, ← exp_add, neg_add_cancel, exp_zero,
    one_mul]

/-- `θ₂(ζ + πτ/2) = e^{-iπτ/4-iζ} θ₃(ζ)`. -/
theorem je22a_thetaTwo_add_half_tau (ζ τ : ℂ) :
    jacobiThetaTwoTau (ζ + π * τ / 2) τ = je22a_shiftFactor ζ τ * jacobiThetaThreeTau ζ τ := by
  rw [jacobiThetaTwoTau, show ζ + π * τ / 2 + π * τ / 2 = ζ + π * τ by ring,
    jacobiThetaThreeTau_add_pi_mul, je22a_shiftFactor, ← mul_assoc, ← exp_add]
  congr 2
  ring

/-- Identity under the stated parameter and domain assumptions: `cexp (-(π / 2 * I)) = -I`. -/
lemma je22a_exp_neg_half_pi_I : cexp (-(π / 2 * I)) = -I := by
  rw [Complex.exp_neg, Complex.exp_pi_div_two_mul_I, inv_I]

/-- `θ₁(ζ + πτ/2) = i e^{-iπτ/4-iζ} θ₄(ζ)`. -/
theorem je22a_thetaOne_add_half_tau (ζ τ : ℂ) :
    jacobiThetaOneTau (ζ + π * τ / 2) τ = I * je22a_shiftFactor ζ τ * jacobiThetaFourTau ζ τ := by
  rw [jacobiThetaOneTau, jacobiThetaTwoTau, show ζ + π * τ / 2 + π / 2 + π * τ / 2 =
    (ζ + π / 2) + π * τ by ring, jacobiThetaThreeTau_add_pi_mul, je22a_shiftFactor,
    ← jacobiThetaFourTau, ← mul_assoc, ← exp_add]
  have h : π * I * τ / 4 + I * (ζ + π * τ / 2 + π / 2) + (-(π * I * τ) - 2 * I * (ζ + π / 2)) =
      -(π * I * τ / 4 + I * ζ) + (-(π / 2 * I)) := by ring
  rw [h, exp_add, je22a_exp_neg_half_pi_I]
  ring

/-- `θ₄(ζ + πτ/2) = i e^{-iπτ/4-iζ} θ₁(ζ)`. -/
theorem je22a_thetaFour_add_half_tau (ζ τ : ℂ) :
    jacobiThetaFourTau (ζ + π * τ / 2) τ = I * je22a_shiftFactor ζ τ * jacobiThetaOneTau ζ τ := by
  rw [jacobiThetaFourTau, show ζ + π * τ / 2 + π / 2 = (ζ + π / 2) + π * τ / 2 by ring,
    je22a_thetaThree_add_half_tau, je22a_thetaTwo_add_half_pi, je22a_shiftFactor,
    je22a_shiftFactor, show -(π * I * τ / 4 + I * (ζ + π / 2)) =
      -(π * I * τ / 4 + I * ζ) + (-(π / 2 * I)) by ring, exp_add, je22a_exp_neg_half_pi_I]
  ring

/-! ### Basic relations between the parametrizations -/

/-- The nome is `q = e^{iπτ}` with `τ = iK'/K` (DLMF 22.2.1 and 22.2.12). -/
@[dlmf 22.2.E1]
theorem jacobiNomek_eq_exp_tau (k : ℂ) : jacobiNomek k = cexp (π * I * jacobiTauk k) := by
  rw [jacobiNomek, jacobiTauk]
  congr 1
  rw [mul_div_assoc', ← mul_assoc, mul_assoc (π : ℂ) I I, I_mul_I]
  ring

/-! ### `Im τ > 0`: positivity of `Re(K' conj K)` -/
/-- Sign facts for the principal square root `w^{1/2}`. -/
theorem p22R1_sqrt_parts (w : ℂ) :
    0 ≤ (w ^ (1 / 2 : ℂ)).re ∧ (0 ≤ w.im → 0 ≤ (w ^ (1 / 2 : ℂ)).im) ∧
      (w.im < 0 → (w ^ (1 / 2 : ℂ)).im ≤ 0) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  rw [cpow_def_of_ne_zero hw]
  have hre : (log w * (1 / 2 : ℂ)).re = Real.log ‖w‖ / 2 := by
    simp [log_re]; ring
  have him : (log w * (1 / 2 : ℂ)).im = arg w / 2 := by
    simp [log_im]; ring
  rw [exp_re, exp_im, hre, him]
  have h1 := neg_pi_lt_arg w
  have h2 := arg_le_pi w
  have hp := Real.exp_pos (Real.log ‖w‖ / 2)
  refine ⟨mul_nonneg hp.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩),
    fun h => mul_nonneg hp.le (Real.sin_nonneg_of_nonneg_of_le_pi
      (by have := arg_nonneg_iff.mpr h; linarith) (by linarith)), fun h => ?_⟩
  have := arg_neg_iff.mpr h
  exact mul_nonpos_of_nonneg_of_nonpos hp.le
    (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith))

/-- `(w^{1/2})^2 = w`. -/
theorem p22R1_sqrt_sq (w : ℂ) : (w ^ (1 / 2 : ℂ)) ^ 2 = w := by
  rw [← cpow_natCast, ← cpow_mul]
  · norm_num
  all_goals simp [log_im]; nlinarith [neg_pi_lt_arg w, arg_le_pi w, Real.pi_pos]

/-- Pointwise positivity: for `Im m > 0` and `s, t ∈ [0, 1]`,
`Re(√(1-(1-m)s) · conj √(1-mt)) > 0`. -/
lemma p22R1_re_sqrt_mul_conj_pos_of_im_pos {m : ℂ} (hm : 0 < m.im) {s t : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < ((1 - (1 - m) * s) ^ (1 / 2 : ℂ) * (starRingEnd ℂ) ((1 - m * t) ^ (1 / 2 : ℂ))).re := by
  set a := (1 - (1 - m) * s) ^ (1 / 2 : ℂ) with ha
  set b := (1 - m * t) ^ (1 / 2 : ℂ) with hb
  have hw1 : (1 - (1 - m) * (s : ℂ)).im = s * m.im := by simp; ring
  have hw2 : (1 - m * (t : ℂ)).im = -(t * m.im) := by simp; ring
  obtain ⟨ha0, ha1, -⟩ := p22R1_sqrt_parts (1 - (1 - m) * s)
  obtain ⟨hb0, -, hb2⟩ := p22R1_sqrt_parts (1 - m * t)
  have hai : 0 ≤ a.im := ha1 (by rw [hw1]; positivity)
  rcases ht0.eq_or_lt with rfl | htp
  · -- `b = 1`
    have : b = 1 := by rw [hb]; simp
    rw [this]
    simp only [map_one, mul_one]
    rcases hs0.eq_or_lt with rfl | hsp
    · rw [ha]; simp
    · -- `Im (a^2) = s Im m > 0`, so `Re a > 0`
      have h2 := p22R1_sqrt_sq (1 - (1 - m) * s)
      rw [← ha] at h2
      have him := congrArg Complex.im h2
      rw [hw1, pow_two, mul_im] at him
      have : 0 < s * m.im := mul_pos hsp hm
      nlinarith
  have hbi : b.im ≤ 0 := hb2 (by rw [hw2]; nlinarith)
  set z := a * (starRingEnd ℂ) b with hz
  have hzi : 0 ≤ z.im := by
    rw [hz, mul_im, conj_re, conj_im]; nlinarith
  have hz2 : z ^ 2 = (1 - (1 - m) * s) * (starRingEnd ℂ) (1 - m * t) := by
    rw [hz, mul_pow, ← map_pow, ha, hb, p22R1_sqrt_sq, p22R1_sqrt_sq]
  have him := congrArg Complex.im hz2
  rw [pow_two, mul_im] at him
  have hrhs : ((1 - (1 - m) * (s : ℂ)) * (starRingEnd ℂ) (1 - m * t)).im =
      m.im * (t * (1 - s) + s) := by
    simp [mul_im]; ring
  rw [hrhs] at him
  have : 0 < m.im * (t * (1 - s) + s) := mul_pos hm (by nlinarith)
  nlinarith

/-- Pointwise positivity of `Re(√(1-(1-m)s) · conj √(1-mt))` for `m ∉ (-∞, 0] ∪ [1, ∞)`. -/
lemma p22R1_re_sqrt_mul_conj_pos {m : ℂ} (hm : m.im ≠ 0 ∨ (m.im = 0 ∧ 0 < m.re ∧ m.re < 1))
    {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < ((1 - (1 - m) * s) ^ (1 / 2 : ℂ) * (starRingEnd ℂ) ((1 - m * t) ^ (1 / 2 : ℂ))).re := by
  rcases hm with hm | ⟨hm0, hm1, hm2⟩
  · rcases hm.lt_or_gt with hm | hm
    · have hc : 0 < ((starRingEnd ℂ) m).im := by simpa using hm
      have h := p22R1_re_sqrt_mul_conj_pos_of_im_pos hc hs0 hs1 ht0 ht1
      have harg1 : (1 - (1 - m) * (s : ℂ)).arg ≠ π := by
        rw [Ne, arg_eq_pi_iff]; intro ⟨h1, h2⟩
        simp at h1 h2
        rcases h2 with h2 | h2 <;> first | exact hm.ne h2 | (subst h2; simp at h1; linarith)
      have harg2 : (1 - m * (t : ℂ)).arg ≠ π := by
        rw [Ne, arg_eq_pi_iff]; intro ⟨h1, h2⟩
        simp at h1 h2
        rcases h2 with h2 | h2 <;> first | exact hm.ne h2 | (subst h2; simp at h1; linarith)
      have e1 := cpow_conj (1 - (1 - m) * (s : ℂ)) (1 / 2) harg1
      have e2 := cpow_conj (1 - m * (t : ℂ)) (1 / 2) harg2
      simp only [map_div₀, map_one, map_ofNat, map_sub, map_mul, conj_ofReal] at e1 e2
      rw [← conj_re, map_mul, Complex.conj_conj, e1, e2, Complex.conj_conj]
      exact h
    · exact p22R1_re_sqrt_mul_conj_pos_of_im_pos hm hs0 hs1 ht0 ht1
  · have hmr : m = (m.re : ℂ) := by apply Complex.ext <;> simp [hm0]
    have hw1 : (1 - (1 - m) * (s : ℂ)) = ((1 - (1 - m.re) * s : ℝ) : ℂ) := by
      rw [hmr]; push_cast; simp
    have hw2 : (1 - m * (t : ℂ)) = ((1 - m.re * t : ℝ) : ℂ) := by
      rw [hmr]; push_cast; simp
    have hp1 : 0 < 1 - (1 - m.re) * s := by nlinarith
    have hp2 : 0 < 1 - m.re * t := by nlinarith
    rw [hw1, hw2, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hp1.le, ← ofReal_cpow hp2.le, conj_ofReal, ← ofReal_mul,
      ofReal_re]
    exact mul_pos (Real.rpow_pos_of_pos hp1 _) (Real.rpow_pos_of_pos hp2 _)

/-- On `jacobiModulusDomain`, `k²` is non-real or lies in `(0, 1)`. -/
theorem p22R1_sq_of_mem_domain {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    (k ^ 2).im ≠ 0 ∨ ((k ^ 2).im = 0 ∧ 0 < (k ^ 2).re ∧ (k ^ 2).re < 1) := by
  obtain ⟨h0, h1⟩ := hk
  by_cases him : k.im = 0
  · right
    have := h1 him
    simp only [pow_two, mul_im, mul_re, him]
    refine ⟨by ring, by nlinarith, by nlinarith⟩
  · left
    simp only [pow_two, mul_im]
    intro h
    have : k.re * k.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact him h'

/-- The integrands of `K` and `K'` stay in the slit plane. -/
lemma p22R1_mem_slitPlane {m : ℂ} (hm : m.im ≠ 0 ∨ (m.im = 0 ∧ 0 < m.re ∧ m.re < 1))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    1 - (1 - m) * (s : ℂ) ∈ slitPlane ∧ 1 - m * (s : ℂ) ∈ slitPlane := by
  rw [mem_slitPlane_iff, mem_slitPlane_iff]
  rcases hs0.eq_or_lt with rfl | hs
  · simp
  rcases hm with hm | ⟨hm0, hm1, hm2⟩
  · exact ⟨Or.inr (by simp; exact ⟨hm, hs.ne'⟩), Or.inr (by simp; exact ⟨hm, hs.ne'⟩)⟩
  · constructor <;> left <;> simp [hm0] <;> nlinarith

/-- For `k ∈ jacobiModulusDomain` the lattice parameter `τ = iK'/K` lies in the
upper half-plane (`|q| < 1`). Proof: `Re(K' conj K) = ∫∫ Re(F(θ) conj G(φ)) > 0` pointwise, where
`F`, `G` are the integrands of `K'`, `K`; the pointwise positivity follows from
`Im(w₁ conj w₂) = Im(k²)(t(1-s)+s)` for `w₁ = 1-(1-k²)s`, `w₂ = 1-k²t`. -/
@[dlmf 22.2.E1 "domain: Re k > 0, k ∉ [1, ∞), so |q| < 1"]
theorem jacobiTauk_im_pos {k : ℂ} (hk : k ∈ jacobiModulusDomain) : 0 < (jacobiTauk k).im := by
  have hm := p22R1_sq_of_mem_domain hk
  set m := k ^ 2 with hmdef
  set F : ℝ → ℂ := fun θ => (1 - (1 - m) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) with hFdef
  set G : ℝ → ℂ := fun θ => (1 - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) with hGdef
  have hsq (θ : ℝ) : (Real.sin θ : ℂ) ^ 2 = ((Real.sin θ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hs0 (θ : ℝ) : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hs1 (θ : ℝ) : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hF : Continuous F := Continuous.cpow (by fun_prop) continuous_const fun θ => by
    rw [hsq]; exact (p22R1_mem_slitPlane hm (hs0 θ) (hs1 θ)).1
  have hG : Continuous G := Continuous.cpow (by fun_prop) continuous_const fun θ => by
    rw [hsq]; exact (p22R1_mem_slitPlane hm (hs0 θ) (hs1 θ)).2
  have hKp : compEllIntKpk k = ∫ θ in (0 : ℝ)..(π / 2), F θ := rfl
  have hK : compEllIntKk k = ∫ θ in (0 : ℝ)..(π / 2), G θ := rfl
  set K := compEllIntKk k
  set K' := compEllIntKpk k
  have hpi : (0 : ℝ) < π / 2 := by positivity
  have hpt (θ φ : ℝ) : 0 < (F θ * (starRingEnd ℂ) (G φ)).re := by
    have h := p22R1_re_sqrt_mul_conj_pos hm (hs0 θ) (hs1 θ) (hs0 φ) (hs1 φ)
    simp only [hFdef, hGdef, hsq]
    rw [cpow_neg, cpow_neg, map_inv₀, ← mul_inv, inv_re]
    exact div_pos h (normSq_pos.mpr fun h0 => by rw [h0] at h; simp at h)
  have key : 0 < (K' * (starRingEnd ℂ) K).re := by
    have e1 : K' * (starRingEnd ℂ) K = ∫ θ in (0 : ℝ)..(π / 2), F θ * (starRingEnd ℂ) K := by
      rw [hKp, intervalIntegral.integral_mul_const]
    have hc1 : Continuous fun θ => F θ * (starRingEnd ℂ) K := hF.mul continuous_const
    have r1 := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (μ := MeasureTheory.volume)
      (hc1.intervalIntegrable 0 (π / 2))
    simp only [RCLike.re_to_complex] at r1
    rw [e1, ← r1]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((Complex.continuous_re.comp hc1).intervalIntegrable _ _) (fun θ _ => ?_) hpi
    have e2 : F θ * (starRingEnd ℂ) K =
        ∫ φ in (0 : ℝ)..(π / 2), F θ * (starRingEnd ℂ) (G φ) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.intervalIntegral_conj, hK]
    have hc2 : Continuous fun φ => F θ * (starRingEnd ℂ) (G φ) :=
      continuous_const.mul (Complex.continuous_conj.comp hG)
    have r2 := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (μ := MeasureTheory.volume)
      (hc2.intervalIntegrable 0 (π / 2))
    simp only [RCLike.re_to_complex] at r2
    show 0 < (F θ * (starRingEnd ℂ) K).re
    rw [e2, ← r2]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      ((Complex.continuous_re.comp hc2).intervalIntegrable _ _) (fun φ _ => hpt θ φ) hpi
  have hK0 : K ≠ 0 := fun h0 => by simp [h0] at key
  have hns : 0 < normSq K := normSq_pos.mpr hK0
  have : (jacobiTauk k).im = (K' * (starRingEnd ℂ) K).re / normSq K := by
    simp only [jacobiTauk, div_eq_mul_inv, inv_def, mul_im, mul_re, I_re, I_im, conj_re, conj_im]
    simp
    ring
  rw [this]
  exact div_pos key hns

/-- For real `k` with `k² < 1` the complex integral `K(k)` is the real `K(m)`, `m = k²`. -/
theorem compEllIntKk_ofReal {k : ℝ} (hk : k ^ 2 < 1) :
    compEllIntKk k = (Real.compEllIntKm (k ^ 2) : ℂ) := by
  rw [compEllIntKk, Real.compEllIntKm, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hpos : 0 ≤ 1 - k ^ 2 * Real.sin θ ^ 2 := (one_sub_mul_sin_sq_pos hk θ).le
  rw [ofReal_cpow hpos]
  push_cast
  ring_nf

/-- For real `k` with `0 < k²` the complex `K'(k)` is the real `K(1 - m)`, `m = k²`. -/
theorem compEllIntKpk_ofReal {k : ℝ} (hk : 0 < k ^ 2) :
    compEllIntKpk k = (Real.compEllIntKm (1 - k ^ 2) : ℂ) := by
  rw [compEllIntKpk, Real.compEllIntKm, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hpos : 0 ≤ 1 - (1 - k ^ 2) * Real.sin θ ^ 2 :=
    (one_sub_mul_sin_sq_pos (by linarith) θ).le
  rw [ofReal_cpow hpos]
  push_cast
  ring_nf

end DLMF.JacobiElliptic
end
end
