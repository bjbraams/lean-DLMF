/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.FirstKindProperties
public import DLMF.Hypergeometric.Elementary

/-!
# Legendre functions of the second kind (Temme §§8.2, 8.5; DLMF §14.3)

`Q_ν(z) = √π Γ(ν+1) (2z)^{-ν-1} 𝐅((ν+2)/2, (ν+1)/2; ν+3/2; 1/z²)` is analytic on
`ℂ ∖ (-∞, 1]`, where `1/z²` lies in the cut plane of `𝐅`. It satisfies Legendre's equation for
every complex `ν`, and `Q₀(z) = ½ log((z+1)/(z-1))`; the latter is proved near `z = 2` from
DLMF 15.4.2 and extended by the identity principle.
-/

@[expose] public section

open Complex Filter Set DLMF.Hypergeometric
open scoped Topology Real

noncomputable section

namespace DLMF.Legendre

/-- For `z ∉ (-∞, 1]`, `1/z²` lies in the cut plane. -/
theorem recip_sq_mem_cutPlane {z : ℂ} (hz : z - 1 ∈ slitPlane) : 1 / z ^ 2 ∈ cutPlane := by
  rw [mem_cutPlane, mem_slitPlane_iff]
  rw [mem_slitPlane_iff] at hz
  by_contra h
  push Not at h
  obtain ⟨hre, him⟩ := h
  have hz0 : z ≠ 0 := by
    rintro rfl; simp at hz; norm_num at hz
  set u := z ^ 2 with hu
  have hu0 : u ≠ 0 := pow_ne_zero 2 hz0
  have hn : 0 < normSq u := normSq_pos.mpr hu0
  simp only [sub_re, one_re, sub_im, one_im, one_div, inv_re, inv_im] at hre him
  have huim : u.im = 0 := by
    have : -u.im / normSq u = 0 := by linarith
    rw [neg_div, neg_eq_zero, div_eq_zero_iff] at this
    exact this.resolve_right hn.ne'
  have hure : normSq u ≤ u.re := by
    have : 1 ≤ u.re / normSq u := by linarith
    rwa [le_div_iff₀ hn, one_mul] at this
  have hnsq : normSq u = u.re * u.re := by rw [normSq_apply, huim]; ring
  have hx : u.re = z.re ^ 2 - z.im ^ 2 := by rw [hu]; simp [pow_two]
  have hy : u.im = 2 * z.re * z.im := by rw [hu]; simp [pow_two]; ring
  have hpos : 0 < u.re := by nlinarith
  have hle : u.re ≤ 1 := by nlinarith
  have hyz : z.im = 0 := by
    rcases mul_eq_zero.mp (show 2 * z.re * z.im = 0 by linarith) with h | h
    · rcases mul_eq_zero.mp h with h | h
      · norm_num at h
      · rw [h] at hx; nlinarith [sq_nonneg z.im]
    · exact h
  rw [hyz] at hx
  have : z.re ≤ 1 := by nlinarith
  rcases hz with h | h
  · simp at h; linarith
  · simp [hyz] at h

/-- `z ∉ (-∞, 1]` implies `z ∉ (-∞, 0]`. -/
theorem mem_slitPlane_of_sub_one {z : ℂ} (hz : z - 1 ∈ slitPlane) : z ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  rcases hz with h | h
  · left; simp at h; linarith
  · right; simpa using h

/-- The domain `ℂ ∖ (-∞, 1]` of `Q_ν` is open. -/
theorem isOpen_sub_one_mem_slitPlane : IsOpen {z : ℂ | z - 1 ∈ slitPlane} :=
  isOpen_slitPlane.preimage (by fun_prop)

/-- Chain rule for `z ↦ z^p 𝐅(a,b;c;1/z²)`. -/
theorem hasDerivAt_cpow_mul_regularizedGaussHG_recip_sq (a b c p : ℂ) {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    HasDerivAt (fun z => z ^ p * regularizedGaussHG a b c (1 / z ^ 2))
      (p * z ^ (p - 1) * regularizedGaussHG a b c (1 / z ^ 2) -
        2 * z ^ (p - 3) * (a * b * regularizedGaussHG (a + 1) (b + 1) (c + 1) (1 / z ^ 2))) z := by
  have hs := mem_slitPlane_of_sub_one hz
  have hz0 := slitPlane_ne_zero hs
  have hu := recip_sq_mem_cutPlane hz
  have hG := (differentiableAt_regularizedGaussHG a b c hu).hasDerivAt
  rw [deriv_regularizedGaussHG _ _ _ hu] at hG
  have hinv : HasDerivAt (fun z : ℂ => 1 / z ^ 2) (-2 / z ^ 3) z := by
    have h := (hasDerivAt_pow 2 z).inv (pow_ne_zero 2 hz0)
    simp only [one_div]
    convert h using 1
    field_simp
    ring
  have hp : HasDerivAt (fun z : ℂ => z ^ p) (p * z ^ (p - 1)) z :=
    (hasDerivAt_id z).cpow_const hs |>.congr_deriv (by simp)
  have h := hp.mul (hG.comp z hinv)
  refine h.congr_deriv ?_
  have h3 : z ^ (p - 3) = z ^ (p - 1) / z ^ 2 := by
    rw [show p - 3 = (p - 1) - ((2 : ℕ) : ℂ) by push_cast; ring, cpow_sub _ _ hz0, cpow_natCast]
  rw [h3, show p - 1 = p - 1 by rfl]
  simp only [Function.comp]
  rw [cpow_sub _ _ hz0, cpow_one]
  field_simp
  ring

/-- Legendre function of the second kind
`Q_ν(z) = √π Γ(ν+1) (2z)^{-ν-1} 𝐅((ν+2)/2, (ν+1)/2; ν+3/2; 1/z²)`, analytic off `(-∞, 1]`
(DLMF 14.3.7 with `μ = 0`, Temme (8.8)). -/
@[dlmf 14.3.E7]
def legendreQ (ν z : ℂ) : ℂ :=
  (Real.sqrt π * Gamma (ν + 1) * 2 ^ (-(ν + 1))) *
    (z ^ (-(ν + 1)) * regularizedGaussHG ((ν + 2) / 2) ((ν + 1) / 2) (ν + 3 / 2) (1 / z ^ 2))

/-- Legendre's equation for `Q_ν` (DLMF 14.2.2 with `μ = 0`). -/
@[dlmf 14.2.E2]
theorem legendreQ_ode (ν : ℂ) {z : ℂ}
    (hz : z - 1 ∈ slitPlane) :
    (1 - z ^ 2) * iteratedDeriv 2 (legendreQ ν) z - 2 * z * deriv (legendreQ ν) z +
      ν * (ν + 1) * legendreQ ν z = 0 := by
  set K : ℂ := Real.sqrt π * Gamma (ν + 1) * 2 ^ (-(ν + 1))
  set a := (ν + 2) / 2
  set b := (ν + 1) / 2
  set c := ν + 3 / 2
  set p := -(ν + 1)
  have hz0 := slitPlane_ne_zero (mem_slitPlane_of_sub_one hz)
  have hd (w : ℂ) (hw : w - 1 ∈ slitPlane) : HasDerivAt (legendreQ ν)
      (K * (p * w ^ (p - 1) * regularizedGaussHG a b c (1 / w ^ 2) -
        2 * w ^ (p - 3) * (a * b * regularizedGaussHG (a + 1) (b + 1) (c + 1) (1 / w ^ 2)))) w :=
    (hasDerivAt_cpow_mul_regularizedGaussHG_recip_sq a b c p hw).const_mul K
  have hev : deriv (legendreQ ν) =ᶠ[𝓝 z] fun w =>
      K * (p * (w ^ (p - 1) * regularizedGaussHG a b c (1 / w ^ 2)) -
        2 * (a * b) * (w ^ (p - 3) * regularizedGaussHG (a + 1) (b + 1) (c + 1) (1 / w ^ 2))) := by
    filter_upwards [isOpen_sub_one_mem_slitPlane.mem_nhds hz] with w hw
    rw [(hd w hw).deriv]; ring
  have h2 := (((hasDerivAt_cpow_mul_regularizedGaussHG_recip_sq a b c (p - 1) hz).const_mul p).sub
    ((hasDerivAt_cpow_mul_regularizedGaussHG_recip_sq (a + 1) (b + 1) (c + 1) (p - 3) hz).const_mul
      (2 * (a * b)))).const_mul K
  have h2' : HasDerivAt (fun w =>
      K * (p * (w ^ (p - 1) * regularizedGaussHG a b c (1 / w ^ 2)) -
        2 * (a * b) * (w ^ (p - 3) * regularizedGaussHG (a + 1) (b + 1) (c + 1) (1 / w ^ 2)))) _ z
            := h2
  have hQ : legendreQ ν z = K * (z ^ p * regularizedGaussHG a b c (1 / z ^ 2)) := rfl
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq, h2'.deriv, (hd z hz).deriv, hQ]
  have hode := regularizedGaussHG_ode a b c (recip_sq_mem_cutPlane hz)
  have hpow (k : ℕ) : z ^ (p - k) = z ^ p / z ^ k := by
    rw [cpow_sub _ _ hz0, cpow_natCast]
  rw [show p - 1 - 1 = p - (2 : ℕ) by push_cast; ring,
    show p - 1 - 3 = p - (4 : ℕ) by push_cast; ring,
    show p - 3 - 1 = p - (4 : ℕ) by push_cast; ring,
    show p - 3 - 3 = p - (6 : ℕ) by push_cast; ring,
    show p - 1 = p - (1 : ℕ) by push_cast; ring, show p - 3 = p - (3 : ℕ) by push_cast; ring,
    hpow, hpow, hpow, hpow, hpow]
  simp only [poch, ascPochhammer_succ_eval, ascPochhammer_zero, Polynomial.eval_one] at hode
  rw [show a + 1 + 1 = a + 2 by ring, show b + 1 + 1 = b + 2 by ring,
    show c + 1 + 1 = c + 2 by ring]
  generalize regularizedGaussHG a b c (1 / z ^ 2) = G0 at *
  generalize regularizedGaussHG (a + 1) (b + 1) (c + 1) (1 / z ^ 2) = G1 at *
  generalize regularizedGaussHG (a + 2) (b + 2) (c + 2) (1 / z ^ 2) = G2 at *
  generalize z ^ p = Zp at *
  push_cast at hode ⊢
  field_simp at hode ⊢
  simp only [a, b, c, p] at hode ⊢
  linear_combination (-4 * K * Zp) * hode

/-- `w ∈ slitPlane → w⁻¹ ∈ slitPlane`. -/
theorem recip_mem_slitPlane' {w : ℂ} (hw : w ∈ slitPlane) : w⁻¹ ∈ slitPlane := by
  have hn : 0 < normSq w := normSq_pos.mpr (slitPlane_ne_zero hw)
  rw [mem_slitPlane_iff] at hw ⊢
  rcases hw with h | h
  · left; rw [inv_re]; positivity
  · right; rw [inv_im]; exact div_ne_zero (neg_ne_zero.mpr h) hn.ne'

/-- For `z ∉ (-∞, 1]`, `(z+1)/(z-1)` lies in the slit plane. -/
theorem div_mem_slitPlane {z : ℂ} (hz : z - 1 ∈ slitPlane) : (z + 1) / (z - 1) ∈ slitPlane := by
  have hz1 : z - 1 ≠ 0 := slitPlane_ne_zero hz
  have hi := recip_mem_slitPlane' hz
  rw [show (z + 1) / (z - 1) = 1 + 2 * (z - 1)⁻¹ by field_simp; ring]
  rw [mem_slitPlane_iff] at hi ⊢
  rcases hi with h | h
  · left; simp at h ⊢; linarith
  · right; simpa using h

/-- The domain `ℂ ∖ (-∞, 1]` is connected. -/
theorem isPreconnected_sub_one_mem_slitPlane : IsPreconnected {z : ℂ | z - 1 ∈ slitPlane} := by
  have h := ((StarConvex.isPathConnected starConvex_one_slitPlane
    (by simp)).isConnected.isPreconnected).image (fun w : ℂ => w + 1)
    (by fun_prop : Continuous fun w : ℂ => w + 1).continuousOn
  convert h using 1
  ext z
  simp only [mem_ofPred_eq, mem_image]
  exact ⟨fun h => ⟨z - 1, h, by ring⟩, fun ⟨w, hw, hwz⟩ => by rw [← hwz]; simpa using hw⟩

/-- `Q_ν` is analytic on `ℂ ∖ (-∞, 1]`. -/
theorem analyticAt_legendreQ (ν : ℂ) {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    AnalyticAt ℂ (legendreQ ν) z := by
  have hs := mem_slitPlane_of_sub_one hz
  have hz0 := slitPlane_ne_zero hs
  have hu := recip_sq_mem_cutPlane hz
  have hG : AnalyticAt ℂ (fun w : ℂ => regularizedGaussHG ((ν + 2) / 2) ((ν + 1) / 2) (ν + 3 / 2)
      (1 / w ^ 2)) z :=
    (analyticAt_regularizedGaussHG _ _ _ hu).comp_of_eq
      (by fun_prop (disch := exact pow_ne_zero 2 hz0)) rfl
  unfold legendreQ
  exact analyticAt_const.mul ((analyticAt_id.cpow analyticAt_const hs).mul hG)

/-- `Q₀(z) = ½ log((z+1)/(z-1))` (Temme (8.24)). -/
theorem legendreQ_zero {z : ℂ} (hz : z - 1 ∈ slitPlane) :
    legendreQ 0 z = 1 / 2 * log ((z + 1) / (z - 1)) := by
  have hQ : AnalyticOnNhd ℂ (legendreQ 0) {z | z - 1 ∈ slitPlane} :=
    fun w hw => analyticAt_legendreQ 0 hw
  have hL : AnalyticOnNhd ℂ (fun z : ℂ => 1 / 2 * log ((z + 1) / (z - 1)))
      {z | z - 1 ∈ slitPlane} := by
    intro w hw
    have hw1 : w - 1 ≠ 0 := slitPlane_ne_zero hw
    exact analyticAt_const.mul ((analyticAt_clog (div_mem_slitPlane hw)).comp_of_eq
      (by fun_prop (disch := exact hw1)) rfl)
  have h2 : (2 : ℂ) ∈ {z : ℂ | z - 1 ∈ slitPlane} := by
    show (2 : ℂ) - 1 ∈ slitPlane; norm_num
  refine hQ.eqOn_of_preconnected_of_eventuallyEq hL isPreconnected_sub_one_mem_slitPlane h2 ?_ hz
  have hball : Metric.ball (2 : ℂ) (1 / 2) ∈ 𝓝 (2 : ℂ) := Metric.ball_mem_nhds _ (by norm_num)
  filter_upwards [hball] with w hw
  have hw' : w - 1 ∈ slitPlane := by
    rw [Metric.mem_ball, dist_eq_norm] at hw
    left
    have := abs_re_le_norm (w - 2)
    simp at this ⊢
    rw [abs_le] at this
    linarith [this.1]
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have hw1 : 3 / 2 < ‖w‖ := by
    have := norm_sub_norm_le (2 : ℂ) w
    rw [norm_sub_rev] at hw; norm_num at this; linarith
  have hw0 : w ≠ 0 := by rintro rfl; norm_num at hw1
  have hu : ‖w⁻¹‖ < 1 := by
    rw [norm_inv]; exact inv_lt_one_of_one_lt₀ (by linarith)
  have hu2 : ‖w⁻¹ ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg w⁻¹]
  have hc : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hΓ : Gamma (3 / 2) = (Real.sqrt π : ℂ) / 2 := by
    rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Gamma_add_one _ (by norm_num),
      Gamma_one_half_eq, show ((1 / 2 : ℂ)) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow Real.pi_pos.le, ← Real.sqrt_eq_rpow]
    push_cast; ring
  have hsq : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hlog := log_ratio hu
  have hratio : (1 + w⁻¹) / (1 - w⁻¹) = (w + 1) / (w - 1) := by
    have hw1 : w - 1 ≠ 0 := slitPlane_ne_zero hw'
    field_simp
  have hQ0 : legendreQ 0 w = (Real.sqrt π : ℂ) * 2⁻¹ *
      (w⁻¹ * regularizedGaussHG (1 / 2) 1 (3 / 2) (w⁻¹ ^ 2)) := by
    rw [legendreQ, regularizedGaussHG_symm _ _ _ (by
      rw [show 1 / w ^ 2 = w⁻¹ ^ 2 by rw [inv_pow, one_div]]
      exact mem_cutPlane_of_norm_lt_one hu2)]
    norm_num [cpow_neg_one]
  rw [hQ0, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hu2,
      regularizedGaussHGFun_eq_div_Gamma hc, hΓ,
    ← hratio, ← hlog]
  field_simp

end DLMF.Legendre

end
