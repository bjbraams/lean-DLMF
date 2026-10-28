/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.Representations.PoissonAndBarnesLoop

/-!
# Barnes and Sonine representations of Struve functions

The Barnes integral for H and Sonine-type integral identities, including analytic continuation.

Source references and common attribution are retained in
`DLMF.Struve.Representations`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Struve

open DLMF.Bessel

/-! ### The Barnes integral for `H_ν` (DLMF 11.5.8) -/

/-- `-(ix)²/4 = x²/4`. -/
theorem struveBar_w (x : ℝ) : -(I * x) ^ 2 / 4 = ((x ^ 2 / 4 : ℝ) : ℂ) := by
  push_cast; ring_nf; rw [I_sq]; ring

/-- The modulus of the 11.5.8 integrand `F(s)` at `s = t + iy`. -/
theorem struveBar_norm_F (ν : ℂ) {x : ℝ} (hx : 0 < x) (t y : ℝ) :
    ‖struveLoop_F ν (I * x) (t + y * I)‖ = (x ^ 2 / 4) ^ t * (π / ‖sin (π * ((t : ℂ) + y * I))‖ *
      (‖Gamma (((3 / 2 + t : ℝ) : ℂ) + y * I)‖)⁻¹ *
      (‖Gamma (((3 / 2 + ν.re + t : ℝ) : ℂ) + ((y : ℂ) + ν.im) * I)‖)⁻¹) := by
  have e1 : (3 / 2 : ℂ) + (t + y * I) = ((3 / 2 + t : ℝ) : ℂ) + y * I := by push_cast; ring
  have e2 : (3 / 2 : ℂ) + ν + (t + y * I) =
      ((3 / 2 + ν.re + t : ℝ) : ℂ) + ((y : ℂ) + ν.im) * I := by
    apply Complex.ext <;> simp; ring
  simp only [struveLoop_F]
  rw [struveBar_w, e1, e2, norm_mul, norm_div, norm_div, norm_mul,
    norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp only [norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, add_re, ofReal_re, mul_re,
    I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]
  rw [div_eq_mul_inv _ (_ * _), mul_inv]
  ring

/-- The modulus of the 11.5.8 integrand at `s = t - iy`, by conjugation. -/
theorem struveBar_norm_F_neg (ν : ℂ) {x : ℝ} (hx : 0 < x) (t y : ℝ) :
    ‖struveLoop_F ν (I * x) (t + (-y : ℝ) * I)‖ = (x ^ 2 / 4) ^ t *
      (π / ‖sin (π * ((t : ℂ) + y * I))‖ * (‖Gamma (((3 / 2 + t : ℝ) : ℂ) + y * I)‖)⁻¹ *
      (‖Gamma (((3 / 2 + ν.re + t : ℝ) : ℂ) + ((y : ℂ) + ((-ν.im : ℝ) : ℂ)) * I)‖)⁻¹) := by
  rw [struveBar_norm_F ν hx]
  have h1 : (π : ℂ) * ((t : ℂ) + ((-y : ℝ) : ℂ) * I) = (starRingEnd ℂ) (π * ((t : ℂ) + y * I)) := by
    apply Complex.ext <;> simp
  have h2 : ((3 / 2 + t : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I =
      (starRingEnd ℂ) (((3 / 2 + t : ℝ) : ℂ) + y * I) := by
    rw [map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]; push_cast; ring
  have h3 : ((3 / 2 + ν.re + t : ℝ) : ℂ) + ((((-y : ℝ) : ℂ)) + ν.im) * I =
      (starRingEnd ℂ) (((3 / 2 + ν.re + t : ℝ) : ℂ) + ((y : ℂ) + ((-ν.im : ℝ) : ℂ)) * I) := by
    rw [map_add, map_mul, map_add, conj_ofReal, conj_ofReal, conj_ofReal, conj_I]; push_cast; ring
  rw [h1, h2, h3, sin_conj, Gamma_conj, Gamma_conj, norm_conj, norm_conj, norm_conj]

/-- **The horizontal sides vanish.** If `‖G h t‖` is the modulus of the 11.5.8 integrand at
`t ± ih` (with shift `m = ±Im ν`), then `∫_{(c,∞)} G h → 0` as `h → ∞`: dominated convergence
with the uniform bounds `DLMF.Gamma.shiftB_norm_recip_Gamma_le` and the pointwise Stirling decay
`struveBar_isBigO`. -/
theorem struveBar_tendsto_horizontal (ν : ℂ) {x c : ℝ} (hx : 0 < x) (hc : -1 < c) (hc0 : c < 0)
    (hv : -1 < ν.re + 2 * c) (m : ℝ) (G : ℝ → ℝ → ℂ)
    (hG : ∀ h t : ℝ, ‖G h t‖ = (x ^ 2 / 4) ^ t * (π / ‖sin (π * ((t : ℂ) + h * I))‖ *
      (‖Gamma (((3 / 2 + t : ℝ) : ℂ) + h * I)‖)⁻¹ *
      (‖Gamma (((3 / 2 + ν.re + t : ℝ) : ℂ) + ((h : ℂ) + m) * I)‖)⁻¹))
    (hGc : ∀ h : ℝ, 1 ≤ h → Continuous (G h)) :
    Tendsto (fun h => ∫ t in Ioi c, G h t) atTop (𝓝 0) := by
  have hw : 0 < x ^ 2 / 4 := by positivity
  set D : ℝ → ℝ := fun t => 4 * π * Real.exp (π * |m| / 2) *
    ((x ^ 2 / 4) ^ t / (Real.Gamma (3 / 2 + t) * Real.Gamma (3 / 2 + ν.re + t))) with hD
  have hDi : IntegrableOn D (Ioi c) :=
    (struveBar_integrableOn_rpow_div_Gamma (α := 3 / 2) (β := 3 / 2 + ν.re) (by linarith)
      (by linarith) hw).const_mul _
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi c))
    (F := fun h t => G h t) (f := fun _ => (0 : ℂ)) (l := atTop) D ?_ ?_ hDi ?_
  · simpa using hlim
  · filter_upwards [eventually_ge_atTop 1] with h hh
    exact (hGc h hh).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 1] with h hh
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht' : c < t := ht
    rw [hG]
    have ha : 1 / 2 ≤ 3 / 2 + t := by linarith
    have hb : 1 / 2 ≤ 3 / 2 + ν.re + t := by linarith
    have hGa := Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < 3 / 2 + t)
    have hGb := Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < 3 / 2 + ν.re + t)
    have g1 := DLMF.Gamma.shiftB_norm_recip_Gamma_le ha h
    have g2 := DLMF.Gamma.shiftB_norm_recip_Gamma_le hb (h + m)
    rw [norm_inv] at g1 g2
    have e : ((h : ℂ) + m) = ((h + m : ℝ) : ℂ) := by push_cast; ring
    rw [e]
    have hS := struveBar_pi_div_sin_le t hh
    have hexp : Real.exp (-(π * h)) * Real.exp (π * |h| / 2) * Real.exp (π * |h + m| / 2) ≤
        Real.exp (π * |m| / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : |h| = h := abs_of_nonneg (by linarith)
      have h2 : |h + m| ≤ h + |m| := (abs_add_le h m).trans (by rw [h1])
      rw [h1]; nlinarith [Real.pi_pos]
    calc (x ^ 2 / 4) ^ t * (π / ‖sin (π * ((t : ℂ) + h * I))‖ *
          (‖Gamma (((3 / 2 + t : ℝ) : ℂ) + h * I)‖)⁻¹ *
          (‖Gamma (((3 / 2 + ν.re + t : ℝ) : ℂ) + ((h + m : ℝ) : ℂ) * I)‖)⁻¹)
        ≤ (x ^ 2 / 4) ^ t * (4 * π * Real.exp (-(π * h)) *
          (Real.exp (π * |h| / 2) / Real.Gamma (3 / 2 + t)) *
          (Real.exp (π * |h + m| / 2) / Real.Gamma (3 / 2 + ν.re + t))) := by
          gcongr
      _ = 4 * π * (Real.exp (-(π * h)) * Real.exp (π * |h| / 2) * Real.exp (π * |h + m| / 2)) *
          ((x ^ 2 / 4) ^ t / (Real.Gamma (3 / 2 + t) * Real.Gamma (3 / 2 + ν.re + t))) := by
          field_simp
      _ ≤ D t := by
          simp only [hD]
          gcongr
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht' : c < t := ht
    have hO := struveBar_isBigO t (3 / 2 + t) (3 / 2 + ν.re + t) m
    have hq : 0 < 2 + ν.re + 2 * t := by linarith
    have hO' : (fun h : ℝ => G h t) =O[atTop] fun h : ℝ => h ^ (-(2 + ν.re + 2 * t)) := by
      refine Asymptotics.IsBigO.of_norm_left ?_
      simp_rw [hG]
      have := hO.const_mul_left ((x ^ 2 / 4) ^ t)
      rw [show (1 - (3 / 2 + t) - (3 / 2 + ν.re + t)) = -(2 + ν.re + 2 * t) by ring] at this
      exact this
    exact hO'.trans_tendsto (tendsto_rpow_neg_atTop hq)

/-- `L_ν`'s normalized series at `iz` is `H_ν`'s at `z`. -/
theorem struveBar_LCore_I (ν z : ℂ) : struveLCore ν (I * z) = struveHCore ν z := by
  unfold struveLCore struveHCore
  congr 1; funext n
  have e : (I * z / 2) ^ 2 = -1 * (z / 2) ^ 2 := by ring_nf; rw [I_sq]; ring
  rw [pow_mul, pow_mul, e, mul_pow]
  ring

/-- The 11.5.8 integrand is continuous on the vertical line `Re s = c`, `-1 < c < 0`. -/
theorem struveBar_continuous_vertical (ν : ℂ) {x c : ℝ} (hx : 0 < x) (hc : -1 < c) (hc0 : c < 0) :
    Continuous fun y : ℝ => struveLoop_F ν (I * x) (c + y * I) := by
  have hz : I * (x : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx.ne')
  simp_rw [struveLoop_F_eq]
  refine Continuous.mul (Continuous.div continuous_const (by fun_prop) fun y h0 => ?_)
    ((struveLoop_continuous_G ν hz).comp (by fun_prop))
  obtain ⟨k, hk⟩ := struveLoop_sin_eq_zero h0
  have hre : c = (k : ℝ) := by simpa using congrArg Complex.re hk
  have h1 : (-1 : ℝ) < k := hre ▸ hc
  have h2 : (k : ℝ) < 0 := hre ▸ hc0
  have h1' : (-1 : ℤ) < k := by exact_mod_cast h1
  have h2' : k < 0 := by exact_mod_cast h2
  omega

/-- The 11.5.8 integrand is integrable on the vertical line: it is `O(|y|^{-2-Re ν-2c})`. -/
theorem struveBar_integrable_vertical (ν : ℂ) {x c : ℝ} (hx : 0 < x) (hc : -1 < c) (hc0 : c < 0)
    (hv : -1 < ν.re + 2 * c) :
    Integrable fun y : ℝ => struveLoop_F ν (I * x) (c + y * I) := by
  have hp : -(2 + ν.re + 2 * c) < -1 := by linarith
  have e : (1 - (3 / 2 + c) - (3 / 2 + ν.re + c)) = -(2 + ν.re + 2 * c) := by ring
  refine struveBar_integrable_of_isBigO (struveBar_continuous_vertical ν hx hc hc0) hp ?_ ?_
  · refine Asymptotics.IsBigO.of_norm_left ?_
    simp_rw [struveBar_norm_F ν hx]
    have := (struveBar_isBigO c (3 / 2 + c) (3 / 2 + ν.re + c) ν.im).const_mul_left
      ((x ^ 2 / 4) ^ c)
    rwa [e] at this
  · refine Asymptotics.IsBigO.of_norm_left ?_
    simp_rw [struveBar_norm_F_neg ν hx]
    have := (struveBar_isBigO c (3 / 2 + c) (3 / 2 + ν.re + c) (-ν.im)).const_mul_left
      ((x ^ 2 / 4) ^ c)
    rwa [e] at this

/-- The closed rectangle identity at height `h`, after `R → ∞`: the two horizontal half-line
integrals and the vertical segment give `2πi` times the residue sum `H`-core. -/
theorem struveBar_rect_identity (ν : ℂ) {x c h : ℝ} (hx : 0 < x) (hc : -1 < c) (hc0 : c < 0)
    (hh : 0 < h) :
    (∫ t in Ioi c, struveLoop_F ν (I * x) (t + (-h : ℝ) * I)) -
      (∫ t in Ioi c, struveLoop_F ν (I * x) (t + h * I)) -
      I * ∫ y in (-h)..h, struveLoop_F ν (I * x) (c + y * I) = 2 * π * I * struveHCore ν x := by
  have hz : I * (x : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx.ne')
  set F := struveLoop_F ν (I * x) with hFdef
  have hloop := struveL_barnes_loop ν hz hc hc0 hh
  change Tendsto (fun R => positiveBarnesLoop F c h R) atTop _ at hloop
  have hint : ∀ t : ℝ, t ≠ 0 → IntegrableOn (fun x : ℝ => F (x + t * I)) (Ioi c) :=
    fun t ht => struveLoop_integrableOn ν hz c ht
  have hform : ∀ R : ℝ, positiveBarnesLoop F c h R =
      (∫ x : ℝ in c..R, F (x + (-h : ℝ) * I)) - (∫ x : ℝ in c..R, F (x + h * I)) -
        I * ∫ y : ℝ in (-h)..h, F (c + y * I) := by
    intro R
    rw [struveLoop_loop_eq, struveLoop_rect, smul_eq_mul, smul_eq_mul]
    ring
  have hL : Tendsto (fun R => positiveBarnesLoop F c h R) atTop
      (𝓝 ((∫ t in Ioi c, F (t + (-h : ℝ) * I)) - (∫ t in Ioi c, F (t + h * I)) -
        I * ∫ y in (-h)..h, F (c + y * I))) := by
    simp_rw [hform]
    exact ((intervalIntegral_tendsto_integral_Ioi c (hint _ (by linarith)) tendsto_id).sub
      (intervalIntegral_tendsto_integral_Ioi c (hint _ hh.ne') tendsto_id)).sub
      tendsto_const_nhds
  rw [tendsto_nhds_unique hL hloop, struveL, struveBar_LCore_I]
  have hz2 : I * (x : ℂ) / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  have hpow : (I * (x : ℂ) / 2) ^ (-ν - 1) * (I * (x : ℂ) / 2) ^ (ν + 1) = 1 := by
    rw [← cpow_add _ _ hz2]; simp
  linear_combination (2 * π * I * struveHCore ν x) * hpow

/-- struveH barnes (DLMF 11.5.8). Proof: the residue theorem on the rectangles
`[c, N + 1/2] × [-h, h]` (as for 11.5.9, `struveL_barnes_loop` at `z = ix`) gives the identity
`struveBar_rect_identity` for every height `h`; the horizontal half-line integrals tend to `0` as
`h → ∞` by dominated convergence (`struveBar_tendsto_horizontal`), and the vertical integrand is
`O(|y|^{-2-Re ν-2c})` by Stirling's formula on vertical lines, hence integrable
(`struveBar_integrable_vertical`). A 30-digit numerical check (2026-10-22) is recorded in
REVIEW.md. -/
@[dlmf 11.5.E8]
theorem struveH_barnes {ν : ℂ} (hν : -1 < ν.re) {x c : ℝ} (hx : 0 < x) (hc : -1 < c) (hc0 : c < 0) (hv : -1 < ν.re+2*c) :
    HasIntegralWholeLine (fun y : ℝ => let s : ℂ := c+y*I; π/sin (π*s)/(Gamma (3/2+s)*Gamma (3/2+ν+s))*(x^2/4:ℂ)^s) (-2*π*(x/2:ℂ)^(-ν-1)*struveH ν x) := by
  set f : ℝ → ℂ := fun y => struveLoop_F ν (I * x) (c + y * I) with hfdef
  have hfe : (fun y : ℝ => let s : ℂ := c+y*I; π/sin (π*s)/(Gamma (3/2+s)*Gamma (3/2+ν+s))*(x^2/4:ℂ)^s) = f := by
    funext y
    simp only [hfdef, struveLoop_F]
    congr 2
    ring_nf; rw [I_sq]; ring
  have hval : -2*π*(x/2:ℂ)^(-ν-1)*struveH ν x = -2 * π * struveHCore ν x := by
    have hx2 : (x : ℂ) / 2 ≠ 0 := div_ne_zero (ofReal_ne_zero.mpr hx.ne') two_ne_zero
    have hpow : ((x : ℂ) / 2) ^ (-ν - 1) * ((x : ℂ) / 2) ^ (ν + 1) = 1 := by
      rw [← cpow_add _ _ hx2]; simp
    rw [struveH]
    linear_combination (-2 * π * struveHCore ν x) * hpow
  rw [hfe, hval]
  have hfi : Integrable f := struveBar_integrable_vertical ν hx hc hc0 hv
  -- the symmetric integrals
  have hJ : Tendsto (fun h : ℝ => ∫ y in (-h)..h, f y) atTop (𝓝 (-2 * π * struveHCore ν x)) := by
    have hP := struveBar_tendsto_horizontal ν hx hc hc0 hv ν.im
      (fun h t => struveLoop_F ν (I * x) (t + h * I))
      (fun h t => struveBar_norm_F ν hx t h)
      (fun h hh => struveLoop_continuous_line ν (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx.ne'))
        (by linarith))
    have hM := struveBar_tendsto_horizontal ν hx hc hc0 hv (-ν.im)
      (fun h t => struveLoop_F ν (I * x) (t + (-h : ℝ) * I))
      (fun h t => struveBar_norm_F_neg ν hx t h)
      (fun h hh => struveLoop_continuous_line ν (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx.ne'))
        (by linarith))
    have hlim := ((hM.sub hP).sub (tendsto_const_nhds (x := 2 * π * I * struveHCore ν x))).const_mul (-I)
    have e : -I * ((0 : ℂ) - 0 - 2 * π * I * struveHCore ν x) = -2 * π * struveHCore ν x := by
      ring_nf; rw [I_sq]; ring
    rw [e] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with h hh
    have := struveBar_rect_identity ν hx hc hc0 hh
    simp only [hfdef]
    linear_combination (-I) * this - (I_sq) * (∫ y in (-h)..h, struveLoop_F ν (I * x) (c + y * I))
  have hint := intervalIntegral_tendsto_integral hfi tendsto_neg_atTop_atBot tendsto_id
  have hI : ∫ y, f y = -2 * π * struveHCore ν x := tendsto_nhds_unique hint hJ
  rw [← hI]
  exact ⟨_, _, intervalIntegral_tendsto_integral_Iic 0 hfi.integrableOn tendsto_id,
    intervalIntegral_tendsto_integral_Ioi 0 hfi.integrableOn tendsto_id,
    intervalIntegral.integral_Iic_add_Ioi hfi.integrableOn hfi.integrableOn⟩

/-- The straight-segment primitive based at zero of `t^ν H_ν(t)`, with the principal power used in
the integrand. -/
@[dlmf 11.7.E5]
def struveHPrimitive (ν z : ℂ) : ℂ :=
  primitive (fun t => t^ν*struveH ν t) z

/-- A positive real multiple of a slit-plane point lies in the slit plane. -/
theorem ofReal_mul_mem_slitPlane {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z ∈ slitPlane) :
    (s:ℂ)*z ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  rcases hz with h | h
  · left; simp; positivity
  · right; simp; exact ⟨hs.ne', h⟩

/-- Derivative of the antiderivative used in the primitive recurrence. -/
lemma hasDerivAt_struveHPrimitive_aux {ν : ℂ} (hν1 : ν + 1 ≠ 0) {w : ℂ} (hw : w ∈ slitPlane) :
    HasDerivAt (fun w : ℂ => -(w^(ν+1)*struveH ν w) +
        w^(2*ν+2)/(2^(ν+1)*(ν+1)*Real.sqrt π*Gamma (ν+3/2)))
      (w^(ν+1)*struveH (ν+1) w - (2*ν+1)*(w^ν*struveH ν w)) w := by
  have hw0 := slitPlane_ne_zero hw
  have h28 := struveH_weighted_deriv_28 ν hw
  have hp := (hasStrictDerivAt_cpow_const (c := 2*ν+1) hw).hasDerivAt
  have hprod := hp.mul h28
  have heq : (fun u : ℂ => u^(2*ν+1) * (u^(-1*ν) * struveH ν u)) =ᶠ[𝓝 w]
      fun u => u^(ν+1)*struveH ν u := by
    filter_upwards [isOpen_slitPlane.mem_nhds hw] with u hu
    rw [← mul_assoc, ← cpow_add _ _ (slitPlane_ne_zero hu)]; ring_nf
  have hA := hprod.congr_of_eventuallyEq heq.symm
  have hB := (hasStrictDerivAt_cpow_const (c := 2*ν+2) hw).hasDerivAt.div_const
    (2^(ν+1)*(ν+1)*Real.sqrt π*Gamma (ν+3/2))
  refine (hA.neg.add hB).congr_deriv ?_
  have e1 : w^(2*ν+1-1) * w^(-1*ν) = w^ν := by
    rw [← cpow_add _ _ hw0]; ring_nf
  have e2 : w^(2*ν+1) * w^(-ν) = w^(ν+1) := by
    rw [← cpow_add _ _ hw0]; ring_nf
  have e3 : w^(2*ν+2-1) = w^(2*ν+1) := by ring_nf
  have key : (2*ν+2)/(2^(ν+1)*(ν+1)*Real.sqrt π*Gamma (ν+3/2)) =
      2^(-ν)/(Real.sqrt π*Gamma (ν+3/2)) := by
    rw [cpow_neg, cpow_add _ _ two_ne_zero, cpow_one]
    have h2 : (2:ℂ)^ν ≠ 0 := cpow_ne_zero_iff.2 (Or.inl two_ne_zero)
    by_cases hg : (Real.sqrt π:ℂ)*Gamma (ν+3/2) = 0
    · rw [hg, div_zero, show (2:ℂ)^ν*2*(ν+1)*Real.sqrt π*Gamma (ν+3/2) =
        2^ν*2*(ν+1)*((Real.sqrt π)*Gamma (ν+3/2)) by ring, hg, mul_zero, div_zero]
    · field_simp
  rw [e3]
  have : (2*ν+2) * w^(2*ν+1) / (2^(ν+1)*(ν+1)*Real.sqrt π*Gamma (ν+3/2)) =
      w^(2*ν+1) * (2^(-ν)/(Real.sqrt π*Gamma (ν+3/2))) := by
    rw [← key]; ring
  rw [this]
  linear_combination (-(2*ν+1)*struveH ν w) * e1 + struveH (ν+1) w * e2

/-- The power of z squared carries twice the argument of z, and is expressed using the inherited logarithm. -/
@[dlmf 11.7.E6]
theorem struveHPrimitive_recurrence {ν : ℂ} (hν : -1 < ν.re) {z : ℂ} (hz : z ∈ slitPlane) :
    struveHPrimitive (ν+1) z = (2*ν+1)*struveHPrimitive ν z-z^(ν+1)*struveH ν z+exp ((ν+1)*(2*log z-log 2))/((ν+1)*Real.sqrt π*Gamma (ν+3/2)) := by
  have hν1 : ν+1 ≠ 0 := fun h => by have := congrArg re h; simp at this; linarith
  have hν2 : 2*ν+2 ≠ 0 := fun h => hν1 (by linear_combination h/2)
  have hz0 := slitPlane_ne_zero hz
  set D : ℂ := 2^(ν+1)*(ν+1)*Real.sqrt π*Gamma (ν+3/2) with hD
  set G : ℂ → ℂ := fun w => -(w^(ν+1)*struveH ν w) + w^(2*ν+2)/D with hG
  have hcore : ∀ μ : ℂ, Continuous (struveHCore μ) := fun μ => (entire_struveHCore μ).continuous
  have hf : ∀ μ : ℂ, ∀ s : ℝ, 0 < s → ((s:ℂ)*z)^μ * struveH μ ((s:ℂ)*z) =
      (s:ℂ)^(2*μ+1) * (z^μ*(z/2)^(μ+1)*struveHCore μ ((s:ℂ)*z)) := by
    intro μ s hs
    rw [struveH, show (s:ℂ)*z/2 = (s:ℂ)*(z/2) by ring, DLMF.Confluent.ofReal_mul_cpow' hs hz0,
      DLMF.Confluent.ofReal_mul_cpow' hs (div_ne_zero hz0 two_ne_zero)]
    have : (s:ℂ)^(2*μ+1) = (s:ℂ)^μ * (s:ℂ)^(μ+1) := by
      rw [← cpow_add _ _ (ofReal_ne_zero.2 hs.ne')]; ring_nf
    rw [this]; ring
  have hint : ∀ μ : ℂ, -1 < μ.re →
      IntervalIntegrable (fun s : ℝ => ((s:ℂ)*z)^μ * struveH μ ((s:ℂ)*z)) volume 0 1 := by
    intro μ hμ
    have h1 : IntervalIntegrable (fun s : ℝ => (s:ℂ)^(2*μ+1)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
    have hc : Continuous fun s : ℝ => z^μ*(z/2)^(μ+1)*struveHCore μ ((s:ℂ)*z) :=
      continuous_const.mul ((hcore μ).comp (by fun_prop))
    have h2 := h1.mul_continuousOn hc.continuousOn
    refine h2.congr fun s hs => ?_
    rw [uIoc_of_le zero_le_one] at hs
    exact (hf μ s hs.1).symm
  set ψ : ℝ → ℂ := fun s => -(z^(ν+1)*(z/2)^(ν+1)*struveHCore ν ((s:ℂ)*z)) + z^(2*ν+2)/D
  have hφ : ∀ s : ℝ, 0 ≤ s → G ((s:ℂ)*z) = (s:ℂ)^(2*ν+2) * ψ s := by
    intro s hs
    rcases hs.eq_or_lt with h0 | hpos
    · subst h0
      simp only [G, ψ, ofReal_zero, zero_mul, zero_cpow hν1, zero_cpow hν2]
      ring
    · simp only [G, ψ]
      rw [struveH, show (s:ℂ)*z/2 = (s:ℂ)*(z/2) by ring, DLMF.Confluent.ofReal_mul_cpow' hpos hz0,
        DLMF.Confluent.ofReal_mul_cpow' hpos (div_ne_zero hz0 two_ne_zero),
        DLMF.Confluent.ofReal_mul_cpow' hpos hz0]
      have : (s:ℂ)^(2*ν+2) = (s:ℂ)^(ν+1) * (s:ℂ)^(ν+1) := by
        rw [← cpow_add _ _ (ofReal_ne_zero.2 hpos.ne')]; ring_nf
      rw [this]; ring
  have hcontφ : ContinuousOn (fun s : ℝ => G ((s:ℂ)*z)) (Icc 0 1) := by
    have hψ : Continuous ψ :=
      (continuous_const.mul ((hcore ν).comp (by fun_prop))).neg.add continuous_const
    have : ContinuousOn (fun s : ℝ => (s:ℂ)^(2*ν+2) * ψ s) (Icc 0 1) := fun s _ =>
      ((continuousAt_ofReal_cpow_const s _ (Or.inl (by simp; linarith))).mul
        hψ.continuousAt).continuousWithinAt
    exact this.congr fun s hs => hφ s hs.1
  have hderiv : ∀ s ∈ Ioo (0:ℝ) 1, HasDerivAt (fun s : ℝ => G ((s:ℂ)*z))
      (z * (((s:ℂ)*z)^(ν+1)*struveH (ν+1) ((s:ℂ)*z) -
        (2*ν+1)*(((s:ℂ)*z)^ν*struveH ν ((s:ℂ)*z)))) s := by
    intro s hs
    have h1 := hasDerivAt_struveHPrimitive_aux hν1 (ofReal_mul_mem_slitPlane hs.1 hz)
    have h2 : HasDerivAt (fun s : ℝ => (s:ℂ)*z) z s :=
      ((hasDerivAt_id s).ofReal_comp.mul_const z).congr_deriv (by simp)
    refine (h1.comp s h2).congr_deriv ?_
    ring
  have hII := ((hint (ν+1) (by simp; linarith)).sub ((hint ν hν).const_mul (2*ν+1))).const_mul z
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcontφ hderiv hII
  have hP : ∀ μ, struveHPrimitive μ z =
      z * ∫ s : ℝ in 0..1, ((s:ℂ)*z)^μ*struveH μ ((s:ℂ)*z) := by
    intro μ; simp [struveHPrimitive, primitive, segmentIntegral]
  have hG0 : G (((0:ℝ):ℂ)*z) = 0 := by
    rw [hφ 0 le_rfl, ofReal_zero, zero_cpow hν2, zero_mul]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hint (ν+1)
    (by simp; linarith)) ((hint ν hν).const_mul (2*ν+1)), intervalIntegral.integral_const_mul,
    hG0, ofReal_one, one_mul] at hFTC
  rw [hP, hP]
  have hexp : exp ((ν+1)*(2*log z-log 2)) = z^(2*ν+2)/2^(ν+1) := by
    rw [cpow_def_of_ne_zero hz0, cpow_def_of_ne_zero two_ne_zero, ← Complex.exp_sub]; ring_nf
  rw [hexp]
  simp only [G, hD] at hFTC
  have hsplit : z^(2*ν+2)/(2^(ν+1)*(ν+1)*Real.sqrt π*Gamma (ν+3/2)) =
      z^(2*ν+2)/2^(ν+1)/((ν+1)*Real.sqrt π*Gamma (ν+3/2)) := by
    rw [div_div, ← mul_assoc, ← mul_assoc]
  rw [hsplit] at hFTC
  linear_combination hFTC

/-- `sin²` maps `(0, π/2)` onto `(0, 1)`. -/
theorem sin_sq_image_Ioo : (fun θ : ℝ => Real.sin θ^2) '' Ioo 0 (π/2) = Ioo 0 1 := by
  ext x; constructor
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
    have := Real.sin_sq_add_cos_sq θ
    exact ⟨by positivity, by nlinarith⟩
  · rintro ⟨h0, h1⟩
    refine ⟨Real.arcsin (Real.sqrt x), ⟨Real.arcsin_pos.2 (Real.sqrt_pos.2 h0), ?_⟩, ?_⟩
    · rw [Real.arcsin_lt_pi_div_two, Real.sqrt_lt' one_pos]; simpa using h1
    · show Real.sin (Real.arcsin (Real.sqrt x))^2 = x
      rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg x]) (by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt h1.le), Real.sq_sqrt h0.le]

/-- `sin²` is injective on `(0, π/2)`. -/
theorem sin_sq_injOn : InjOn (fun θ : ℝ => Real.sin θ^2) (Ioo 0 (π/2)) := by
  intro a ha b hb hab
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [ha.2, Real.pi_pos])
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb.1 (by linarith [hb.2, Real.pi_pos])
  have : Real.sin a = Real.sin b := by
    simp only at hab; nlinarith [sq_nonneg (Real.sin a - Real.sin b)]
  exact Real.injOn_sin ⟨by linarith [ha.1, Real.pi_pos], ha.2.le⟩
    ⟨by linarith [hb.1, Real.pi_pos], hb.2.le⟩ this

/-- Derivative of `sin²`. -/
theorem hasDerivWithinAt_sin_sq (θ : ℝ) :
    HasDerivWithinAt (fun θ : ℝ => Real.sin θ^2) (2*Real.sin θ*Real.cos θ) (Ioo 0 (π/2)) θ := by
  have := ((Real.hasDerivAt_sin θ).pow 2).hasDerivWithinAt (s := Ioo 0 (π/2))
  convert this using 1; push_cast; ring

/-- The weight `sin^(2a-1) θ cos^(2b-1) θ` after the substitution `x = sin² θ`. -/
theorem trigBeta_integrand_eq {a b : ℂ} {θ : ℝ} (hθ : θ ∈ Ioo 0 (π/2)) :
    |2*Real.sin θ*Real.cos θ| • (((Real.sin θ^2:ℝ):ℂ)^(a-1)*(1-((Real.sin θ^2:ℝ):ℂ))^(b-1)) =
      2*((Real.sin θ:ℂ)^(2*a-1)*(Real.cos θ:ℂ)^(2*b-1)) := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have h1 : 1-((Real.sin θ^2:ℝ):ℂ) = ((Real.cos θ^2:ℝ):ℂ) := by
    have := Real.sin_sq_add_cos_sq θ
    rw [show Real.cos θ^2 = 1 - Real.sin θ^2 by linarith]; push_cast; ring
  rw [abs_of_pos (by positivity), h1, Complex.real_smul]
  have e1 := ofReal_mul_sq_cpow' hs (a-1)
  have e2 := ofReal_mul_sq_cpow' hc (b-1)
  rw [show 2*(a-1)+1 = 2*a-1 by ring] at e1
  rw [show 2*(b-1)+1 = 2*b-1 by ring] at e2
  rw [← e1, ← e2]; push_cast; ring

/-- **Trigonometric Beta integral**, with integrability. -/
theorem trigBeta {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntervalIntegrable (fun θ : ℝ => (Real.sin θ:ℂ)^(2*a-1)*(Real.cos θ:ℂ)^(2*b-1)) volume 0 (π/2) ∧
    (∫ θ : ℝ in 0..π/2, (Real.sin θ:ℂ)^(2*a-1)*(Real.cos θ:ℂ)^(2*b-1)) =
      Gamma a * Gamma b / (2*Gamma (a+b)) := by
  set g : ℝ → ℂ := fun x => (x:ℂ)^(a-1)*(1-(x:ℂ))^(b-1)
  have hconv := Complex.betaIntegral_convergent ha hb
  have hg : IntegrableOn g (Ioo 0 1) := by
    have := hconv.1
    exact (integrableOn_Ioc_iff_integrableOn_Ioo'
      (by simp)).1 this
  set W : ℝ → ℂ := fun θ => (Real.sin θ:ℂ)^(2*a-1)*(Real.cos θ:ℂ)^(2*b-1)
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun θ _ => hasDerivWithinAt_sin_sq θ) sin_sq_injOn g
  have heq := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun θ _ => hasDerivWithinAt_sin_sq θ) sin_sq_injOn g
  rw [sin_sq_image_Ioo] at hiff heq
  have hcongr : EqOn (fun θ => |2*Real.sin θ*Real.cos θ| • g (Real.sin θ^2))
      (fun θ => 2 * W θ) (Ioo 0 (π/2)) := fun θ hθ => by
    simp only [g, W]; exact trigBeta_integrand_eq hθ
  have hW2 : IntegrableOn (fun θ => 2 * W θ) (Ioo 0 (π/2)) :=
    (hiff.1 hg).congr_fun hcongr measurableSet_Ioo
  have hW : IntegrableOn W (Ioo 0 (π/2)) := by
    exact IntegrableOn.congr_fun (hW2.const_mul (1/2:ℂ)) (fun θ _ => by ring) measurableSet_Ioo
  have hWi : IntervalIntegrable W volume 0 (π/2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by positivity)]
    exact hW
  refine ⟨hWi, ?_⟩
  have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral ha hb
  have hG : Gamma (a+b) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  rw [hB, mul_comm (2:ℂ), ← div_div, mul_div_cancel_left₀ _ hG, Complex.betaIntegral,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  change _ = (∫ t in Ioo 0 1, g t)/2
  rw [heq, setIntegral_congr_fun measurableSet_Ioo hcongr, integral_const_mul,
    intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo]
  ring

/-- Identity under the stated parameter and domain assumptions: `(∫ θ : ℝ in 0..π/2, struveH ν
(z*Real.sin θ)*(Real.sin θ:ℂ)^(ν+1)/(Real.cos θ:ℂ)^(2*ν)) = 2^(-ν)/Real.sqrt π*Gamma
(1/2-ν)*z^(ν-1)*(1-cos z)`. -/
@[dlmf 11.7.E7]
theorem struveH_sonine {ν : ℂ} (hν0 : -3/2 < ν.re) (hν1 : ν.re < 1/2) {z : ℂ} (hz : z ∈ slitPlane) :
    (∫ θ : ℝ in 0..π/2, struveH ν (z*Real.sin θ)*(Real.sin θ:ℂ)^(ν+1)/(Real.cos θ:ℂ)^(2*ν)) = 2^(-ν)/Real.sqrt π*Gamma (1/2-ν)*z^(ν-1)*(1-cos z) := by
  have hz0 := slitPlane_ne_zero hz
  have hz2 : z/2 ≠ 0 := div_ne_zero hz0 two_ne_zero
  have hb : 0 < (1/2-ν).re := by simp; linarith
  have ha : ∀ k : ℕ, 0 < ((k:ℂ)+ν+3/2).re := fun k => by
    simp; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  set W : ℕ → ℝ → ℂ := fun k θ =>
    (Real.sin θ:ℂ)^(2*((k:ℂ)+ν+3/2)-1)*(Real.cos θ:ℂ)^(2*(1/2-ν)-1)
  have hTB := fun k => trigBeta (ha k) hb
  set c : ℕ → ℂ := fun k => (z/2)^(ν+1)*((-1)^k*(z/2)^(2*k)*struveCoeff ν k)
  have hc : Summable fun k => ‖c k‖ := by
    rw [summable_norm_iff]
    exact ((hasSum_struveHCore ν z).mul_left _).summable
  have hWk : ∀ k : ℕ, ∀ θ ∈ Ioo (0:ℝ) (π/2), W k θ = (Real.sin θ:ℂ)^(2*k) * W 0 θ := by
    intro k θ hθ
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hs0 : (Real.sin θ:ℂ) ≠ 0 := ofReal_ne_zero.2 hs.ne'
    simp only [W]
    rw [← cpow_natCast, ← mul_assoc, ← cpow_add _ _ hs0]
    push_cast; ring_nf
  have hpt : ∀ θ ∈ Ioo (0:ℝ) (π/2), HasSum (fun k => c k * W k θ)
      (struveH ν (z*Real.sin θ)*(Real.sin θ:ℂ)^(ν+1)/(Real.cos θ:ℂ)^(2*ν)) := by
    intro θ hθ
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hs0 : (Real.sin θ:ℂ) ≠ 0 := ofReal_ne_zero.2 hs.ne'
    have hzs : z*Real.sin θ/2 = (Real.sin θ:ℂ)*(z/2) := by ring
    rw [struveH, hzs, DLMF.Confluent.ofReal_mul_cpow' hs hz2]
    have hser := (hasSum_struveHCore ν ((Real.sin θ:ℂ)*z)).mul_left
      ((Real.sin θ:ℂ)^(ν+1)*(z/2)^(ν+1)*(Real.sin θ:ℂ)^(ν+1)/(Real.cos θ:ℂ)^(2*ν))
    rw [show (Real.sin θ:ℂ)*z = z*Real.sin θ by ring] at hser
    convert hser using 1
    · funext k
      simp only [c, W]
      rw [show 2*((k:ℂ)+ν+3/2)-1 = (2*k:ℕ) + ((ν+1)+(ν+1)) by push_cast; ring,
        cpow_add _ _ hs0, cpow_add _ _ hs0, cpow_natCast,
        show 2*(1/2-ν)-1 = -(2*ν) by ring, cpow_neg]
      rw [show z*(Real.sin θ:ℂ)/2 = (Real.sin θ:ℂ)*(z/2) by ring, mul_pow]
      field_simp
    · ring
  have hne : ∀ᵐ t ∂(volume:Measure ℝ), t ≠ π/2 := by
    rw [ae_iff]; simp
  have hIoo : ∀ᵐ t ∂(volume:Measure ℝ), t ∈ uIoc (0:ℝ) (π/2) → t ∈ Ioo (0:ℝ) (π/2) := by
    filter_upwards [hne] with t ht h
    rw [uIoc_of_le (by positivity)] at h
    exact ⟨h.1, lt_of_le_of_ne h.2 ht⟩
  have hS := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := fun k θ => c k * W k θ) (μ := volume) (a := 0) (b := π/2)
    (f := fun θ => struveH ν (z*Real.sin θ)*(Real.sin θ:ℂ)^(ν+1)/(Real.cos θ:ℂ)^(2*ν))
    (fun k θ => ‖c k‖ * ‖W 0 θ‖)
    (fun k => (((hTB k).1.const_mul (c k)).def').aestronglyMeasurable)
    (fun k => by
      filter_upwards [hIoo] with θ hθ h
      have h' := hθ h
      show ‖c k * W k θ‖ ≤ ‖c k‖ * ‖W 0 θ‖
      rw [norm_mul (c k), hWk k θ h', norm_mul ((Real.sin θ:ℂ)^(2*k)), norm_pow,
        Complex.norm_real]
      have h1 : ‖Real.sin θ‖^(2*k) ≤ 1 := pow_le_one₀ (norm_nonneg _)
        (by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one θ)
      have := mul_le_mul_of_nonneg_right h1 (norm_nonneg (W 0 θ))
      rw [one_mul] at this
      exact mul_le_mul_of_nonneg_left this (norm_nonneg _))
    (Eventually.of_forall fun θ _ => hc.mul_right _)
    (by simp_rw [tsum_mul_right]; exact (hTB 0).1.norm.const_mul _)
    (by filter_upwards [hIoo] with θ hθ h; exact hpt θ (hθ h))
  simp only [intervalIntegral.integral_const_mul] at hS
  refine hS.unique ?_
  -- the cosine series
  have hcos := Complex.hasSum_cos z
  rw [← hasSum_nat_add_iff' 1] at hcos
  simp only [Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one] at hcos
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h2 : (2:ℂ)^(-ν) * 2^(ν+1) = 2 := by
    rw [← cpow_add _ _ two_ne_zero, show -ν+(ν+1) = 1 by ring, cpow_one]
  have hzp : z^(ν-1) * z^2 = 2^(ν+1) * (z/2)^(ν+1) := by
    rw [← cpow_natCast, ← cpow_add _ _ hz0, show ν-1+((2:ℕ):ℂ) = ν+1 by push_cast; ring]
    conv_lhs => rw [show z = ((2:ℝ):ℂ)*(z/2) by push_cast; ring]
    rw [DLMF.Confluent.ofReal_mul_cpow' (by norm_num : (0:ℝ) < 2) hz2]
    push_cast; ring
  have hTQ : (2:ℂ)^(-ν) * z^(ν-1) * z^2 = 2 * (z/2)^(ν+1) := by
    rw [mul_assoc, hzp, ← mul_assoc, h2]
  convert hcos.neg.mul_left (2^(-ν)/Real.sqrt π*Gamma (1/2-ν)*z^(ν-1)) using 1
  · funext k
    simp only [W]
    rw [(hTB k).2]
    rw [show (2:ℂ)^(-ν)/Real.sqrt π*Gamma (1/2-ν)*z^(ν-1) *
        -((-1)^(k+1)*z^(2*(k+1))/(((2*(k+1))! : ℕ) : ℂ)) =
        ((2:ℂ)^(-ν) * z^(ν-1) * z^2) * (Gamma (1/2-ν)*(-1)^k*z^(2*k)/
          (Real.sqrt π*(((2*(k+1))! : ℕ) : ℂ))) by ring, hTQ]
    have hf : (((2*(k+1))! : ℕ):ℂ) = oddProduct k * 2^(k+1) * (((k+1)! : ℕ) : ℂ) := by
      rw [show 2*(k+1) = (2*k+1)+1 by ring, Nat.factorial_succ, Nat.cast_mul,
        factorial_odd_eq_oddProduct, Nat.factorial_succ]
      push_cast; ring
    have ho : oddProduct k ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      have : (0:ℝ) < 2*j+1 := by positivity
      exact_mod_cast this.ne'
    have hG : Gamma ((k:ℂ)+ν+3/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (ha k)
    have hk : (((k+1)! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    rw [hf, show (k:ℂ)+ν+3/2+(1/2-ν) = ((k+1:ℕ):ℂ)+1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
    simp only [c, struveCoeff, Gamma_oddProduct]
    rw [show (k:ℂ)+ν+3/2 = (k:ℂ)+ν+3/2 from rfl, div_pow z 2 (2*k)]
    generalize (z/2)^(ν+1) = P
    generalize Gamma ((k:ℂ)+ν+3/2) = G at hG ⊢
    field_simp
    ring
  · ring

/-- The sine integral `Si(x) = ∫₀ˣ sinc` is bounded on `[0,∞)`. -/
theorem exists_bound_integral_sinc : ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → |∫ u in (0:ℝ)..x, Real.sinc u| ≤ C := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    ((TauCeti.Contour.tendsto_integral_sinc_atTop).eventually (Metric.ball_mem_nhds (π/2) one_pos))
  refine ⟨max X (π/2 + 1), fun x hx => ?_⟩
  by_cases h : X ≤ x
  · have := hX x h
    rw [Real.dist_eq] at this
    have := abs_sub_abs_le_abs_sub (∫ u in (0:ℝ)..x, Real.sinc u) (π/2)
    rw [abs_of_pos (by positivity : (0:ℝ) < π/2)] at this
    exact (by linarith : _ ≤ π/2+1).trans (le_max_right _ _)
  · push Not at h
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x) (C := 1)
      (f := Real.sinc) (fun u _ => by rw [Real.norm_eq_abs]; exact Real.abs_sinc_le_one u)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hx, one_mul] at hb
    exact hb.trans (by linarith [le_max_left X (π/2+1)])

/-- `∫₀^R c sinc(tc) dt = ∫₀^{Rc} sinc`. -/
theorem integral_mul_sinc_mul (c R : ℝ) :
    ∫ t in (0:ℝ)..R, c * Real.sinc (t * c) = ∫ u in (0:ℝ)..R * c, Real.sinc u := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have := intervalIntegral.integral_comp_mul_right (a := 0) (b := R) Real.sinc hc
    rw [intervalIntegral.integral_const_mul, this, zero_mul, smul_eq_mul]
    field_simp

/-- Dirichlet's integral under a parametric integral: for `g` continuous on `[a,b]` and `c ≥ 0`
continuous, positive on `(a,b)`,
`∫₀^R ∫_a^b g(s) c(s) sinc(t c(s)) ds dt → (π/2) ∫_a^b g`. -/
theorem tendsto_integral_integral_mul_sinc {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℂ} {c : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) (hc : ContinuousOn c (Icc a b))
    (hc0 : ∀ s ∈ Icc a b, 0 ≤ c s) (hc1 : ∀ s ∈ Ioo a b, 0 < c s) :
    Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R, ∫ s in a..b, g s * ((c s * Real.sinc (t * c s) : ℝ) : ℂ))
      atTop (𝓝 (((π/2 : ℝ) : ℂ) * ∫ s in a..b, g s)) := by
  obtain ⟨C, hC⟩ := exists_bound_integral_sinc
  set Si : ℝ → ℝ := fun x => ∫ u in (0:ℝ)..x, Real.sinc u
  have hSi : Continuous Si := by
    have := intervalIntegral.continuous_primitive (μ := volume) (f := Real.sinc)
      (fun x y => Real.continuous_sinc.intervalIntegrable x y) 0
    exact this
  -- Fubini and substitution
  have hswap : ∀ R : ℝ, 0 ≤ R → (∫ t in (0:ℝ)..R, ∫ s in a..b,
      g s * ((c s * Real.sinc (t * c s) : ℝ) : ℂ)) = ∫ s in a..b, g s * (Si (R * c s) : ℂ) := by
    intro R hR
    rw [intervalIntegral_intervalIntegral_swap]
    · refine intervalIntegral.integral_congr fun s _ => ?_
      rw [intervalIntegral.integral_const_mul]
      congr 1
      rw [intervalIntegral.integral_ofReal, integral_mul_sinc_mul]
    · have hK : ContinuousOn (Function.uncurry fun t s => g s * ((c s * Real.sinc (t * c s) : ℝ) : ℂ))
          (Icc 0 R ×ˢ Icc a b) := by
        have hm : MapsTo Prod.snd (Icc 0 R ×ˢ Icc a b) (Icc a b) := fun p hp => hp.2
        refine (hg.comp continuousOn_snd hm).mul ?_
        refine continuous_ofReal.comp_continuousOn ?_
        exact (hc.comp continuousOn_snd hm).mul
          (Real.continuous_sinc.comp_continuousOn (continuousOn_fst.mul
            (hc.comp continuousOn_snd hm)))
      refine (hK.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set ?_
      rw [uIoc_of_le hR, uIoc_of_le hab]
      exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hlim : Tendsto (fun R : ℝ => ∫ s in a..b, g s * (Si (R * c s) : ℂ)) atTop
      (𝓝 (∫ s in a..b, g s * ((π/2 : ℝ) : ℂ))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun s => ‖g s‖ * C) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun R => ?_
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
      refine (hg.mul (continuous_ofReal.comp_continuousOn (hSi.comp_continuousOn
        (continuousOn_const.mul hc)))).mono ?_
      rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
      refine Eventually.of_forall fun s hs => ?_
      rw [uIoc_of_le hab] at hs
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hC _ (mul_nonneg hR (hc0 s (Ioc_subset_Icc_self hs))))
        (norm_nonneg _)
    · refine (ContinuousOn.intervalIntegrable ?_).mul_const C
      rw [uIcc_of_le hab]; exact continuous_norm.comp_continuousOn hg
    · have hb : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ b := by
        rw [ae_iff]; simp [measure_singleton]
      filter_upwards [hb] with s hsb hs
      rw [uIoc_of_le hab] at hs
      have hcs := hc1 s ⟨hs.1, lt_of_le_of_ne hs.2 hsb⟩
      refine Tendsto.const_mul _ ?_
      exact (continuous_ofReal.tendsto _).comp
        ((TauCeti.Contour.tendsto_integral_sinc_atTop).comp
          (tendsto_id.atTop_mul_const hcs))
  rw [intervalIntegral.integral_mul_const, mul_comm] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
  rw [hswap R hR]

/-- `sin(tc)/t = c sinc(tc)` for `t ≠ 0`. -/
theorem sin_mul_div_eq_mul_sinc (t c : ℝ) (ht : t ≠ 0) :
    Real.sin (t * c) / t = c * Real.sinc (t * c) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [Real.sinc_of_ne_zero (mul_ne_zero ht hc)]; field_simp

/-- `c sinc(tc) t = sin(tc)` for `t ≠ 0`. -/
theorem mul_sinc_mul_mul (t c : ℝ) (ht : t ≠ 0) :
    c * Real.sinc (t * c) * t = Real.sin (t * c) := by
  rw [← sin_mul_div_eq_mul_sinc t c ht]; field_simp

/-- `√π √π = π` in `ℂ`. -/
theorem sqrt_pi_mul_sqrt_pi_complex : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
  rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]

/-- `∫₀¹ √(1-s²) ds = π/4`. -/
theorem integral_sqrt_one_sub_sq_unit : ∫ s in (0:ℝ)..1, √(1 - s ^ 2) = π / 4 := by
  have h := integral_sqrt_one_sub_sq
  have hc : Continuous fun s : ℝ => √(1 - s ^ 2) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)] at h
  have hneg : ∫ s in (-1:ℝ)..0, √(1 - s ^ 2) = ∫ s in (0:ℝ)..1, √(1 - s ^ 2) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := 1) (fun s : ℝ => √(1 - s ^ 2))
    simp only [neg_sq, neg_zero] at this
    exact this.symm
  linarith

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => struveH 0 t/t) 0
(π/2)`. -/
@[dlmf 11.7.E8]
theorem struveH_integral_zero_div  :
    HasIntegralAtTop (fun t : ℝ => struveH 0 t/t) 0 (π/2) := by
  -- Poisson's integral, Fubini, and Dirichlet's integral (TauCeti `tendsto_integral_sinc_atTop`)
  have h := tendsto_integral_integral_mul_sinc (a := 0) (b := π/2) (by positivity)
    (g := fun _ => ((2/π : ℝ) : ℂ)) (c := Real.cos) continuousOn_const
    Real.continuous_cos.continuousOn (fun s hs => Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩)
    (fun s hs => Real.cos_pos_of_mem_Ioo ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩)
  rw [intervalIntegral.integral_const, sub_zero, real_smul] at h
  have hv : (((π/2 : ℝ) : ℂ) * (((π/2 : ℝ) : ℂ) * ((2/π : ℝ) : ℂ))) = (π/2 : ℂ) := by
    push_cast; field_simp
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le hR] at ht
  have ht0 : (0:ℝ) < t := ht.1
  have ht' : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  rw [struveH_trig_integral (by norm_num) (ofReal_mem_slitPlane.mpr ht0), eq_div_iff ht',
    ← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hr := mul_sinc_mul_mul t (Real.cos θ) ht0.ne'
  have hr' : ((Real.cos θ * Real.sinc (t * Real.cos θ) : ℝ) : ℂ) * t =
      sin ((t:ℂ) * (Real.cos θ : ℂ)) := by
    rw [← ofReal_mul, hr, ofReal_sin, ofReal_mul]
  simp only [cpow_zero, mul_zero, mul_one, zero_add, DLMF.Confluent.Gamma_one_half_eq_sqrt]
  rw [mul_assoc, hr', sqrt_pi_mul_sqrt_pi_complex]
  push_cast
  ring

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => struveH 1 t/t^2) 0
(π/4)`. -/
@[dlmf 11.7.E8]
theorem struveH_integral_one_div_sq  :
    HasIntegralAtTop (fun t : ℝ => struveH 1 t/t^2) 0 (π/4) := by
  -- Poisson's integral, Fubini, and Dirichlet's integral
  have h := tendsto_integral_integral_mul_sinc (a := 0) (b := 1) zero_le_one
    (g := fun s => ((2/π * √(1 - s ^ 2) : ℝ) : ℂ)) (c := id)
    (continuous_ofReal.comp (by fun_prop)).continuousOn continuous_id.continuousOn
    (fun s hs => hs.1) (fun s hs => hs.1)
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
    integral_sqrt_one_sub_sq_unit] at h
  have hv : (((π/2 : ℝ) : ℂ) * ((2/π * (π/4) : ℝ) : ℂ)) = (π/4 : ℂ) := by
    push_cast; field_simp
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le hR] at ht
  have ht0 : (0:ℝ) < t := ht.1
  have ht' : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  rw [struveH_integral (by norm_num) (ofReal_mem_slitPlane.mpr ht0), eq_div_iff (pow_ne_zero 2 ht'),
    ← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le zero_le_one] at hs
  have hr := mul_sinc_mul_mul t s ht0.ne'
  have hsq : (1 - (s : ℂ) ^ 2) ^ ((1:ℂ) - 1/2) = ((√(1 - s ^ 2) : ℝ) : ℂ) := by
    rw [show (1 - (s : ℂ) ^ 2) = ((1 - s ^ 2 : ℝ) : ℂ) by push_cast; ring,
      show ((1:ℂ) - 1/2) = ((1/2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by nlinarith [hs.1, hs.2]), Real.sqrt_eq_rpow]
  have hG : Gamma (1 + 1/2) = (Real.sqrt π : ℂ) / 2 := by
    rw [show (1:ℂ) + 1/2 = 1/2 + 1 by ring, Complex.Gamma_add_one _ (by norm_num),
      DLMF.Confluent.Gamma_one_half_eq_sqrt]; ring
  have hsin : sin ((t:ℂ) * (s:ℂ)) = ((Real.sin (t * s) : ℝ) : ℂ) := by push_cast; ring_nf
  rw [hsq, hG, cpow_one, hsin, ← hr]
  have hp : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs0 : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  simp only [id]
  push_cast
  rw [← sqrt_pi_mul_sqrt_pi_complex]
  field_simp

end DLMF.Struve
end
