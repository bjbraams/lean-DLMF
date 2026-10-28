/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Conical
public import DLMFMathlib.Analysis.ODE.PowerSeriesUniqueness
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Tactic.Monotonicity.Lemmas

/-!
# Logarithmic branches of associated Legendre functions

Principal-to-logarithmic-plane identities and the zeta-coordinate representation of the second-
kind solution.

Source references and common attribution are retained in
`DLMF.Legendre.Continuation`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat ComplexConjugate

namespace DLMF.Legendre

/-- Boundary value with convergence asserted separately. -/
def legendreBoundary (F : ℂ → ℂ) (s x : ℝ) : ℂ :=
  limUnder (𝓝[>] (0:ℝ)) (fun ε : ℝ => F (x+s*I*ε))

/-- Boundary values of `associatedP` from either side of the cut `(-1, 1)`. -/
lemma associatedP_boundary_aux (ν μ : ℂ) (s : ℝ) (hs : s = 1 ∨ s = -1) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => associatedP ν μ (x+(s:ℂ)*I*ε)) (𝓝[>] (0:ℝ))
      (𝓝 (exp (-(s:ℂ)*μ*π*I/2)*ferrersP ν μ x)) := by
  have h1 : 0 < 1 + x := by linarith [hx.1]
  have h2 : 0 < 1 - x := by linarith [hx.2]
  have hz : Tendsto (fun ε : ℝ => (x:ℂ)+(s:ℂ)*I*ε) (𝓝[>] (0:ℝ)) (𝓝 (x:ℂ)) := by
    have : Continuous (fun ε : ℝ => (x:ℂ)+(s:ℂ)*I*ε) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  -- the factor log (z - 1)
  have hlogm : Tendsto (fun ε : ℝ => log ((x:ℂ)+(s:ℂ)*I*ε - 1)) (𝓝[>] (0:ℝ))
      (𝓝 ((Real.log (1-x) : ℂ) + s*π*I)) := by
    have hre : ((x:ℂ) - 1).re < 0 := by simp; linarith [hx.2]
    have him : ((x:ℂ) - 1).im = 0 := by simp
    have hnorm : Real.log ‖(x:ℂ) - 1‖ = Real.log (1 - x) := by
      rw [show (x:ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (by linarith [hx.2])]; ring_nf
    have hw : Tendsto (fun ε : ℝ => (x:ℂ)+(s:ℂ)*I*ε - 1) (𝓝[>] (0:ℝ)) (𝓝 ((x:ℂ) - 1)) :=
      hz.sub_const 1
    rcases hs with rfl | rfl
    · have hw' : Tendsto (fun ε : ℝ => (x:ℂ)+((1:ℝ):ℂ)*I*ε - 1) (𝓝[>] (0:ℝ))
          (𝓝[{w : ℂ | 0 ≤ w.im}] ((x:ℂ) - 1)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨hw, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with ε hε
        show 0 ≤ ((x:ℂ)+((1:ℝ):ℂ)*I*ε - 1).im
        simp; exact le_of_lt hε
      have := (tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hre him).comp hw'
      rw [hnorm] at this
      convert this using 2
      · rfl
      · push_cast; ring
    · have hw' : Tendsto (fun ε : ℝ => (x:ℂ)+((-1:ℝ):ℂ)*I*ε - 1) (𝓝[>] (0:ℝ))
          (𝓝[{w : ℂ | w.im < 0}] ((x:ℂ) - 1)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨hw, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with ε hε
        show ((x:ℂ)+((-1:ℝ):ℂ)*I*ε - 1).im < 0
        simp; exact hε
      have := (tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him).comp hw'
      rw [hnorm] at this
      convert this using 2
      · rfl
      · push_cast; ring
  have hlogp : Tendsto (fun ε : ℝ => log ((x:ℂ)+(s:ℂ)*I*ε + 1)) (𝓝[>] (0:ℝ))
      (𝓝 ((Real.log (1+x) : ℂ))) := by
    have hsl : (x:ℂ) + 1 ∈ slitPlane := Or.inl (by simp; linarith)
    have := ((continuousAt_clog hsl).tendsto).comp (hz.add_const 1)
    rw [show (x:ℂ) + 1 = ((1 + x : ℝ) : ℂ) by push_cast; ring, ← ofReal_log h1.le] at this
    exact this
  have hF : Tendsto (fun ε : ℝ => regularizedGaussHG (ν+1) (-ν) (1-μ) ((1-((x:ℂ)+(s:ℂ)*I*ε))/2))
      (𝓝[>] (0:ℝ)) (𝓝 (regularizedGaussHG (ν+1) (-ν) (1-μ) ((1-(x:ℂ))/2))) := by
    have hcut : (1-(x:ℂ))/2 ∈ cutPlane := by
      rw [mem_cutPlane, show (1:ℂ) - (1-(x:ℂ))/2 = (((1+x)/2 : ℝ) : ℂ) by push_cast; ring]
      exact Or.inl (by simp only [ofReal_re]; linarith)
    have hc := ((analyticOnNhd_regularizedGaussHG (ν+1) (-ν) (1-μ)) _ hcut).continuousAt
    exact hc.tendsto.comp ((hz.const_sub 1).div_const 2)
  have hE := ((continuous_exp.tendsto _).comp ((hlogp.sub hlogm).const_mul (μ/2)))
  have := hE.mul hF
  unfold associatedP
  convert this using 2
  · rfl
  rw [ferrersP, ofReal_cpow_eq_exp (div_pos h1 h2), Real.log_div h1.ne' h2.ne', ← mul_assoc,
    ← exp_add]
  congr 2; push_cast; ring

/-- DLMF 14.23.1 (upper side): for `-1 < x < 1`, `P^μ_ν(x + iε) → e^{-μπi/2} 𝖯^μ_ν(x)` as `ε →
0⁺`. -/
@[dlmf 14.23.E1]
theorem associatedP_boundary_upper (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => associatedP ν μ (x+(1:ℂ)*I*ε)) (𝓝[>] (0:ℝ)) (𝓝 (exp (-(1:ℂ)*μ*π*I/2)*ferrersP ν μ x)) := by
  have h := associatedP_boundary_aux ν μ 1 (Or.inl rfl) hx
  simpa only [ofReal_one] using h

/-- Two functions continuous at a point and agreeing near it off a countable set agree there. -/
theorem legendre_eq_of_continuousAt_off_countable {f g : ℂ → ℂ} {μ₀ : ℂ} (hf : ContinuousAt f μ₀)
    (hg : ContinuousAt g μ₀) {S : Set ℂ} (hS : S.Countable) (h : ∀ᶠ μ in 𝓝 μ₀, μ ∉ S → f μ = g μ) :
    f μ₀ = g μ₀ := by
  have : (𝓝[Sᶜ] μ₀).NeBot := mem_closure_iff_nhdsWithin_neBot.mp ((hS.dense_compl ℂ).closure_eq ▸ mem_univ _)
  have hev : f =ᶠ[𝓝[Sᶜ] μ₀] g := by
    filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with μ h1 h2 using h1 h2
  exact tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm)

/-- `𝖯^μ_ν` continued analytically off `(-1,1)` into the unit disk. -/
noncomputable def ferrersPCont (ν μ z : ℂ) : ℂ :=
  exp (μ/2*(log (1+z)-log (1-z)))*regularizedGaussHG (ν+1) (-ν) (1-μ) ((1-z)/2)

/-- `𝖰^μ_ν` continued analytically off `(-1,1)` into the unit disk. -/
noncomputable def ferrersQCont (ν μ z : ℂ) : ℂ :=
  -π/2*sin ((ν+μ)*π/2)*(2^μ*Gamma ((ν+μ+1)/2)/Gamma ((ν-μ+2)/2)*(1-z^2)^(-μ/2)*
    regularizedGaussHG (-(ν+μ)/2) ((ν-μ+1)/2) (1/2) (z^2))+
  π/2*cos ((ν+μ)*π/2)*(2^μ*Gamma ((ν+μ+2)/2)/Gamma ((ν-μ+1)/2)*z*(1-z^2)^(-μ/2)*
    regularizedGaussHG ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) (z^2))

/-- On real arguments, the disk continuation `ferrersQCont ν μ` agrees with the Ferrers function
`𝖰^μ_ν = ferrersQ ν μ` (by definition). -/
theorem ferrersQCont_ofReal (ν μ : ℂ) (x : ℝ) : ferrersQCont ν μ x = ferrersQ ν μ x := rfl

/-- For `-1 < x < 1`, the disk continuation `ferrersPCont ν μ x` equals the Ferrers function
`𝖯^μ_ν(x)`. -/
theorem ferrersPCont_ofReal (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersPCont ν μ x = ferrersP ν μ x := by
  have h1 : 0 < 1 + x := by linarith [hx.1]
  have h2 : 0 < 1 - x := by linarith [hx.2]
  rw [ferrersPCont, ferrersP, ofReal_cpow_eq_exp (div_pos h1 h2), Real.log_div h1.ne' h2.ne',
    show (1:ℂ)+x = ((1+x:ℝ):ℂ) by push_cast; ring, show (1:ℂ)-x = ((1-x:ℝ):ℂ) by push_cast; ring,
    ← ofReal_log h1.le, ← ofReal_log h2.le]
  push_cast; ring_nf

/-- For `|z| < 1`, the points `1 + z`, `1 - z` and `1 - z²` lie in the slit plane and `(1 - z)/2`
and `z²` lie in the cut plane `ℂ \ [1, ∞)`. -/
theorem legendre_disk_facts {z : ℂ} (hz : z ∈ Metric.ball (0:ℂ) 1) :
    1+z ∈ slitPlane ∧ 1-z ∈ slitPlane ∧ (1-z)/2 ∈ cutPlane ∧ 1-z^2 ∈ slitPlane ∧ z^2 ∈ cutPlane := by
  have hn : ‖z‖ < 1 := by simpa using hz
  have hre := abs_re_le_norm z
  have hre' : |z.re| < 1 := lt_of_le_of_lt hre hn
  have hsq : ‖z^2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  have hre2 : |(z^2).re| < 1 := lt_of_le_of_lt (abs_re_le_norm _) hsq
  refine ⟨Or.inl ?_, Or.inl ?_, ?_, Or.inl ?_, mem_cutPlane_of_norm_lt_one hsq⟩
  · simp; linarith [(abs_lt.mp hre').1]
  · simp; linarith [(abs_lt.mp hre').2]
  · rw [mem_cutPlane, show (1:ℂ)-(1-z)/2 = (1+z)/2 by ring]
    exact Or.inl (by simp; linarith [(abs_lt.mp hre').1])
  · have : (1-z^2).re = 1-(z^2).re := by simp
    rw [this]; linarith [(abs_lt.mp hre2).2]

/-- `ferrersPCont ν μ` is analytic on the open unit disk. -/
theorem ferrersPCont_analytic (ν μ : ℂ) : AnalyticOnNhd ℂ (ferrersPCont ν μ) (Metric.ball (0:ℂ) 1) := by
  intro z hz
  obtain ⟨hp, hm, hc, -, -⟩ := legendre_disk_facts hz
  have hG : AnalyticAt ℂ (fun w : ℂ => regularizedGaussHG (ν+1) (-ν) (1-μ) ((1-w)/2)) z :=
    (analyticAt_regularizedGaussHG _ _ _ hc).comp_of_eq (by fun_prop) rfl
  have hE : AnalyticAt ℂ (fun w : ℂ => exp (μ/2*(log (1+w)-log (1-w)))) z := by
    fun_prop (disch := assumption)
  exact hE.mul hG

/-- `ferrersQCont ν μ` is analytic on the open unit disk. -/
theorem ferrersQCont_analytic (ν μ : ℂ) : AnalyticOnNhd ℂ (ferrersQCont ν μ) (Metric.ball (0:ℂ) 1) := by
  intro z hz
  obtain ⟨-, -, -, hs, hc⟩ := legendre_disk_facts hz
  have hW : AnalyticAt ℂ (fun w : ℂ => (1-w^2)^(-μ/2)) z :=
    (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 1-w^2) z).cpow analyticAt_const hs
  have hG1 : AnalyticAt ℂ (fun w : ℂ => regularizedGaussHG (-(ν+μ)/2) ((ν-μ+1)/2) (1/2) (w^2)) z :=
    (analyticAt_regularizedGaussHG _ _ _ hc).comp_of_eq (by fun_prop) rfl
  have hG2 : AnalyticAt ℂ (fun w : ℂ => regularizedGaussHG ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) (w^2)) z :=
    (analyticAt_regularizedGaussHG _ _ _ hc).comp_of_eq (by fun_prop) rfl
  unfold ferrersQCont
  exact (analyticAt_const.mul (analyticAt_const.mul hW |>.mul hG1)).add
    (analyticAt_const.mul (((analyticAt_const.mul analyticAt_id).mul hW).mul hG2))

/-- If `ν + μ₀` is not a negative integer and `|z| < 1`, then `μ ↦ ferrersQCont ν μ z` is continuous
at `μ₀`. -/
theorem continuousAt_ferrersQCont_order {ν μ₀ : ℂ} (h : LegendreQRegular ν μ₀) {z : ℂ}
    (hz : z ∈ Metric.ball (0:ℂ) 1) : ContinuousAt (fun μ => ferrersQCont ν μ z) μ₀ := by
  obtain ⟨-, -, -, hsl, hc⟩ := legendre_disk_facts hz
  have h1 : ∀ m : ℕ, (ν+μ₀+1)/2 ≠ -m := fun m hm => h (2*m) (by push_cast; linear_combination 2*hm)
  have h2 : ∀ m : ℕ, (ν+μ₀+2)/2 ≠ -m := fun m hm => h (2*m+1) (by push_cast; linear_combination 2*hm)
  have c1 : ContinuousAt (fun μ => Gamma ((ν+μ+1)/2)) μ₀ :=
    ContinuousAt.comp (g := Gamma) (differentiableAt_Gamma _ h1).continuousAt (by fun_prop)
  have c2 : ContinuousAt (fun μ => Gamma ((ν+μ+2)/2)) μ₀ :=
    ContinuousAt.comp (g := Gamma) (differentiableAt_Gamma _ h2).continuousAt (by fun_prop)
  have r1 := (continuous_recip_Gamma.comp (by fun_prop : Continuous fun μ : ℂ => (ν-μ+2)/2)).continuousAt (x := μ₀)
  have r2 := (continuous_recip_Gamma.comp (by fun_prop : Continuous fun μ : ℂ => (ν-μ+1)/2)).continuousAt (x := μ₀)
  have hne := slitPlane_ne_zero hsl
  have p2 : Continuous fun μ : ℂ => (2:ℂ)^μ := continuous_const_cpow' (by norm_num)
  have pw : Continuous fun μ : ℂ => (1-z^2)^(-μ/2) := (continuous_const_cpow' hne).comp (by fun_prop)
  have g1 := (differentiable_regularizedGaussHG_comp (A := fun μ : ℂ => -(ν+μ)/2) (B := fun μ : ℂ => (ν-μ+1)/2)
    (C := fun _ : ℂ => 1/2) (by fun_prop) (by fun_prop) (by fun_prop) hc).continuous
  have g2 := (differentiable_regularizedGaussHG_comp (A := fun μ : ℂ => (1-ν-μ)/2) (B := fun μ : ℂ => (ν-μ+2)/2)
    (C := fun _ : ℂ => 3/2) (by fun_prop) (by fun_prop) (by fun_prop) hc).continuous
  have hs : Continuous fun μ : ℂ => sin ((ν+μ)*π/2) := by fun_prop
  have hcs : Continuous fun μ : ℂ => cos ((ν+μ)*π/2) := by fun_prop
  unfold ferrersQCont
  exact ((continuousAt_const.mul hs.continuousAt).mul ((((p2.continuousAt.mul c1).mul r1).mul
    pw.continuousAt).mul g1.continuousAt)).add ((continuousAt_const.mul hcs.continuousAt).mul
    (((((p2.continuousAt.mul c2).mul r2).mul continuousAt_const).mul pw.continuousAt).mul g2.continuousAt))

/-- For `|z| < 1`, `μ ↦ ferrersPCont ν μ z` is continuous. -/
theorem continuous_ferrersPCont_order (ν : ℂ) {z : ℂ} (hz : z ∈ Metric.ball (0:ℂ) 1) :
    Continuous fun μ => ferrersPCont ν μ z := by
  obtain ⟨-, -, hc, -, -⟩ := legendre_disk_facts hz
  unfold ferrersPCont
  exact (by fun_prop : Continuous fun μ : ℂ => exp (μ/2*(log (1+z)-log (1-z)))).mul
    (differentiable_regularizedGaussHG_comp (A := fun _ : ℂ => ν+1) (B := fun _ : ℂ => -ν)
      (C := fun μ : ℂ => 1-μ) (by fun_prop) (by fun_prop) (by fun_prop) hc).continuous

/-- On the side `s Im z > 0`, `log (z-1) = log (1-z) + sπi`. -/
theorem legendre_log_sub_one_side {s : ℝ} (hs : s = 1 ∨ s = -1) {z : ℂ} (hz : 0 < s*z.im) :
    log (z-1) = log (1-z)+s*π*I := by
  have harg : arg (z-1) = arg (1-z)+s*π := by
    rw [show z-1 = -(1-z) by ring]
    rcases hs with rfl | rfl
    · exact (arg_neg_eq_arg_add_pi_of_im_neg (by simp; linarith)).trans (by ring)
    · rw [arg_neg_eq_arg_sub_pi_of_im_pos (by simp; linarith)]; ring
  apply Complex.ext
  · simp [log_re, norm_sub_rev]
  · simp [log_im, harg]

/-- For `s = ±1` and `s · Im z > 0`, `P^μ_ν(z) = e^{-sμπi/2} ferrersPCont ν μ z`, relating the
Legendre function to the continued Ferrers function in the upper or lower half-plane. -/
theorem associatedP_eq_ferrersPCont {s : ℝ} (hs : s = 1 ∨ s = -1) (ν μ : ℂ) {z : ℂ} (hz : 0 < s*z.im) :
    associatedP ν μ z = exp (-(s:ℂ)*μ*π*I/2)*ferrersPCont ν μ z := by
  unfold associatedP ferrersPCont
  rw [legendre_log_sub_one_side hs hz, ← mul_assoc, ← exp_add, add_comm z 1]
  congr 2; ring

/-- The boundary representative: `e^{sμπi/2}/Γ(ν+μ+1) (𝖰 - sπi/2 𝖯)` continued into the disk. -/
noncomputable def olverQSide (s : ℝ) (ν μ z : ℂ) : ℂ :=
  exp ((s:ℂ)*μ*π*I/2)/Gamma (ν+μ+1)*(ferrersQCont ν μ z-(s:ℂ)*π*I/2*ferrersPCont ν μ z)

/-- For `s = ±1`, `e^{sμπi/2} (cos(μπ) - s i sin(μπ)) = e^{-sμπi/2}`. -/
theorem legendre_cos_sub_sin_side {s : ℝ} (hs : s = 1 ∨ s = -1) (μ : ℂ) :
    exp ((s:ℂ)*μ*π*I/2)*(cos (μ*π)-(s:ℂ)*I*sin (μ*π)) = exp (-(s:ℂ)*μ*π*I/2) := by
  have hc : cos (μ*π)-(s:ℂ)*I*sin (μ*π) = exp (-(s:ℂ)*μ*π*I) := by
    rcases hs with rfl | rfl
    · rw [show -((1:ℝ):ℂ)*μ*π*I = (-(μ*π))*I by push_cast; ring, exp_mul_I, cos_neg, sin_neg]
      push_cast; ring
    · rw [show -((-1:ℝ):ℂ)*μ*π*I = (μ*π)*I by push_cast; ring, exp_mul_I]
      push_cast; ring
  rw [hc, ← exp_add]; congr 1; ring

/-- For `s = ±1`, `ν + μ` not a negative integer, `μ` not an integer and `|z| < 1`, `olverQSide s ν
μ z = π/(2 sin(μπ)) (e^{-sμπi/2} 𝖯^μ_ν(z)/Γ(ν+μ+1) - e^{sμπi/2} 𝖯^{-μ}_ν(z)/Γ(ν-μ+1))` with
continued Ferrers functions. -/
theorem olverQSide_eq_nonint {s : ℝ} (hs : s = 1 ∨ s = -1) {ν μ : ℂ} (h : LegendreQRegular ν μ)
    (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z ∈ Metric.ball (0:ℂ) 1) :
    olverQSide s ν μ z = π/(2*sin (μ*π))*(exp (-(s:ℂ)*μ*π*I/2)*ferrersPCont ν μ z*(Gamma (ν+μ+1))⁻¹-
      exp ((s:ℂ)*μ*π*I/2)*ferrersPCont ν (-μ) z*(Gamma (ν-μ+1))⁻¹) := by
  have hR : AnalyticOnNhd ℂ (olverQSide s ν μ) (Metric.ball (0:ℂ) 1) := fun w hw =>
    analyticAt_const.mul ((ferrersQCont_analytic ν μ w hw).sub
      (analyticAt_const.mul (ferrersPCont_analytic ν μ w hw)))
  have hG : AnalyticOnNhd ℂ (fun w => π/(2*sin (μ*π))*(exp (-(s:ℂ)*μ*π*I/2)*ferrersPCont ν μ w*
      (Gamma (ν+μ+1))⁻¹-exp ((s:ℂ)*μ*π*I/2)*ferrersPCont ν (-μ) w*(Gamma (ν-μ+1))⁻¹))
      (Metric.ball (0:ℂ) 1) := fun w hw =>
    analyticAt_const.mul (((analyticAt_const.mul (ferrersPCont_analytic ν μ w hw)).mul analyticAt_const).sub
      ((analyticAt_const.mul (ferrersPCont_analytic ν (-μ) w hw)).mul analyticAt_const))
  have h0 : ((0:ℝ):ℂ) ∈ Metric.ball (0:ℂ) 1 := by simp
  refine hR.eqOn_of_preconnected_of_frequently_eq hG (convex_ball _ _).isPreconnected h0 ?_ hz
  have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (0:ℝ)) (𝓝[≠] ((0:ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_inj] using hr
  apply ht.frequently
  have hI : Ioo (-1:ℝ) 1 ∈ 𝓝 (0:ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  refine Filter.Eventually.frequently (nhdsWithin_le_nhds (Filter.mem_of_superset hI ?_))
  intro y hy
  have hQ := ferrersQ_hypergeometric h hμ hy
  have hG1 : Gamma (ν+μ+1) ≠ 0 := Gamma_ne_zero (fun n he => h n (by linear_combination he))
  have hsn := legendre_sin_ne_zero hμ
  have hsn' : sin (π*μ) ≠ 0 := by rwa [mul_comm]
  have hc := legendre_cos_sub_sin_side hs μ
  show olverQSide s ν μ y = _
  unfold olverQSide
  rw [ferrersQCont_ofReal, ferrersPCont_ofReal ν μ hy, ferrersPCont_ofReal ν (-μ) hy, hQ, ← hc]
  field_simp
  ring

/-- For `s = ±1`, `ν + μ` not a negative integer, `|z| < 1` and `s · Im z > 0`, `𝑸^μ_ν(z) =
olverQSide s ν μ z`. -/
theorem olverQ_eq_olverQSide {s : ℝ} (hs : s = 1 ∨ s = -1) {ν μ : ℂ} (h : LegendreQRegular ν μ)
    {z : ℂ} (hz : z ∈ Metric.ball (0:ℂ) 1) (him : 0 < s*z.im) :
    olverQ ν μ z = olverQSide s ν μ z := by
  have hz1 : z-1 ∈ slitPlane := Or.inr (by
    intro h0; simp at h0; rw [h0] at him; simp at him)
  have hreg : ∀ᶠ μ' in 𝓝 μ, LegendreQRegular ν μ' := by
    have hc : Continuous fun m : ℂ => ν+m+1 := by fun_prop
    have h' : ν+μ+1 ∈ {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)} := fun m hm => h m (by linear_combination hm)
    filter_upwards [(isOpen_not_neg_nat.preimage hc).mem_nhds h'] with μ' hμ' n hn
    exact hμ' n (by linear_combination hn)
  have hcR : ContinuousAt (fun μ => olverQSide s ν μ z) μ := by
    have hG1 : Gamma (ν+μ+1) ≠ 0 := Gamma_ne_zero (fun n he => h n (by linear_combination he))
    have cG : ContinuousAt (fun μ => Gamma (ν+μ+1)) μ :=
      ContinuousAt.comp (g := Gamma) (differentiableAt_Gamma _
        (fun m hm => h m (by linear_combination hm))).continuousAt (by fun_prop)
    unfold olverQSide
    exact (((by fun_prop : Continuous fun μ : ℂ => exp ((s:ℂ)*μ*π*I/2)).continuousAt).div cG hG1).mul
      ((continuousAt_ferrersQCont_order h hz).sub
        (continuousAt_const.mul (continuous_ferrersPCont_order ν hz).continuousAt))
  refine legendre_eq_of_continuousAt_off_countable (f := fun μ => olverQ ν μ z)
    (g := fun μ => olverQSide s ν μ z) (olverQ_entire_order ν z hz1).continuous.continuousAt hcR
    (countable_range (Int.cast : ℤ → ℂ)) ?_
  filter_upwards [hreg] with μ' hμ' hnS
  have hnint : ∀ n : ℤ, μ' ≠ n := fun n hn => hnS ⟨n, hn.symm⟩
  show olverQ ν μ' z = olverQSide s ν μ' z
  rw [olverQSide_eq_nonint hs hμ' hnint hz, olverQ_eq_nonint ν μ' hnint hz1,
    associatedP_eq_ferrersPCont hs ν μ' him, associatedP_eq_ferrersPCont hs ν (-μ') him]
  ring_nf

/-- Boundary values of `𝑸^μ_ν` from either side of the cut (DLMF 14.23.2). -/
theorem olverQ_boundary_aux (ν μ : ℂ) (hr : LegendreQRegular ν μ) (s : ℝ) (hs : s = 1 ∨ s = -1)
    {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => olverQ ν μ (x+(s:ℂ)*I*ε)) (𝓝[>] (0:ℝ))
      (𝓝 (exp ((s:ℂ)*μ*π*I/2)/Gamma (ν+μ+1)*(ferrersQ ν μ x-(s:ℂ)*π*I/2*ferrersP ν μ x))) := by
  have hxD : (x:ℂ) ∈ Metric.ball (0:ℂ) 1 := by
    simp only [Metric.mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs]
    exact abs_lt.mpr ⟨hx.1, hx.2⟩
  have hz : Tendsto (fun ε : ℝ => (x:ℂ)+(s:ℂ)*I*ε) (𝓝[>] (0:ℝ)) (𝓝 (x:ℂ)) := by
    have : Continuous (fun ε : ℝ => (x:ℂ)+(s:ℂ)*I*ε) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hcont : ContinuousAt (olverQSide s ν μ) (x:ℂ) :=
    (analyticAt_const.mul ((ferrersQCont_analytic ν μ _ hxD).sub
      (analyticAt_const.mul (ferrersPCont_analytic ν μ _ hxD)))).continuousAt
  have hlim := hcont.tendsto.comp hz
  have hval : olverQSide s ν μ x = exp ((s:ℂ)*μ*π*I/2)/Gamma (ν+μ+1)*
      (ferrersQ ν μ x-(s:ℂ)*π*I/2*ferrersP ν μ x) := by
    rw [olverQSide, ferrersQCont_ofReal, ferrersPCont_ofReal ν μ hx]
  rw [hval] at hlim
  refine hlim.congr' ?_
  have hD : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), (x:ℂ)+(s:ℂ)*I*ε ∈ Metric.ball (0:ℂ) 1 :=
    hz.eventually (Metric.isOpen_ball.mem_nhds hxD)
  filter_upwards [hD, self_mem_nhdsWithin] with ε hεD hε
  have him : 0 < s*((x:ℂ)+(s:ℂ)*I*ε).im := by
    have : ((x:ℂ)+(s:ℂ)*I*ε).im = s*ε := by simp
    rw [this]
    rcases hs with rfl | rfl <;> simp <;> exact hε
  exact (olverQ_eq_olverQSide hs hr hεD him).symm

/-- For `s = ±1`, `cos θ - s i sin θ = e^{-sθi}`. -/
theorem legendre_cos_sub_sin_exp {s : ℝ} (hs : s = 1 ∨ s = -1) (θ : ℂ) :
    cos θ-(s:ℂ)*I*sin θ = exp (-(s:ℂ)*θ*I) := by
  rcases hs with rfl | rfl
  · rw [show -((1:ℝ):ℂ)*θ*I = (-θ)*I by push_cast; ring, exp_mul_I, cos_neg, sin_neg]
    push_cast; ring
  · rw [show -((-1:ℝ):ℂ)*θ*I = θ*I by push_cast; ring, exp_mul_I]
    push_cast; ring

/-- The right side of DLMF 14.23.3, continued into the unit disk. -/
noncomputable def olverQSideHyp (s : ℝ) (ν μ z : ℂ) : ℂ :=
  exp (-(s:ℂ)*ν*π*I/2)*(π:ℂ)^(3/2:ℂ)*(1-z^2)^(μ/2)*((2:ℂ)^(ν+1))⁻¹*
    (z*regularizedGaussHG ((μ-ν+1)/2) ((ν+μ+2)/2) (3/2) (z^2)*((Gamma ((ν-μ+1)/2))⁻¹*(Gamma ((ν+μ+1)/2))⁻¹)-
      (s:ℂ)*I*regularizedGaussHG ((μ-ν)/2) ((ν+μ+1)/2) (1/2) (z^2)*((Gamma ((ν-μ+2)/2))⁻¹*(Gamma ((ν+μ+2)/2))⁻¹))

/-- `olverQSideHyp s ν μ` is analytic on the open unit disk. -/
theorem olverQSideHyp_analytic (s : ℝ) (ν μ : ℂ) :
    AnalyticOnNhd ℂ (olverQSideHyp s ν μ) (Metric.ball (0:ℂ) 1) := by
  intro z hz
  obtain ⟨-, -, -, hsl, hc⟩ := legendre_disk_facts hz
  have hW : AnalyticAt ℂ (fun w : ℂ => (1-w^2)^(μ/2)) z :=
    (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 1-w^2) z).cpow analyticAt_const hsl
  have hG1 : AnalyticAt ℂ (fun w : ℂ => regularizedGaussHG ((μ-ν+1)/2) ((ν+μ+2)/2) (3/2) (w^2)) z :=
    (analyticAt_regularizedGaussHG _ _ _ hc).comp_of_eq (by fun_prop) rfl
  have hG2 : AnalyticAt ℂ (fun w : ℂ => regularizedGaussHG ((μ-ν)/2) ((ν+μ+1)/2) (1/2) (w^2)) z :=
    (analyticAt_regularizedGaussHG _ _ _ hc).comp_of_eq (by fun_prop) rfl
  unfold olverQSideHyp
  exact ((analyticAt_const.mul hW).mul analyticAt_const).mul
    (((analyticAt_id.mul hG1).mul analyticAt_const).sub ((analyticAt_const.mul hG2).mul analyticAt_const))

/-- For `|z| < 1`, `μ ↦ olverQSideHyp s ν μ z` is continuous. -/
theorem continuous_olverQSideHyp_order (s : ℝ) (ν : ℂ) {z : ℂ} (hz : z ∈ Metric.ball (0:ℂ) 1) :
    Continuous fun μ => olverQSideHyp s ν μ z := by
  obtain ⟨-, -, -, hsl, hc⟩ := legendre_disk_facts hz
  have hne := slitPlane_ne_zero hsl
  have pw : Continuous fun μ : ℂ => (1-z^2)^(μ/2) := (continuous_const_cpow' hne).comp (by fun_prop)
  have g1 := (differentiable_regularizedGaussHG_comp (A := fun μ : ℂ => (μ-ν+1)/2) (B := fun μ : ℂ => (ν+μ+2)/2)
    (C := fun _ : ℂ => 3/2) (by fun_prop) (by fun_prop) (by fun_prop) hc).continuous
  have g2 := (differentiable_regularizedGaussHG_comp (A := fun μ : ℂ => (μ-ν)/2) (B := fun μ : ℂ => (ν+μ+1)/2)
    (C := fun _ : ℂ => 1/2) (by fun_prop) (by fun_prop) (by fun_prop) hc).continuous
  have i1 := continuous_recip_Gamma.comp (by fun_prop : Continuous fun μ : ℂ => (ν-μ+1)/2)
  have i2 := continuous_recip_Gamma.comp (by fun_prop : Continuous fun μ : ℂ => (ν+μ+1)/2)
  have i3 := continuous_recip_Gamma.comp (by fun_prop : Continuous fun μ : ℂ => (ν-μ+2)/2)
  have i4 := continuous_recip_Gamma.comp (by fun_prop : Continuous fun μ : ℂ => (ν+μ+2)/2)
  unfold olverQSideHyp
  exact ((continuous_const.mul pw).mul continuous_const).mul
    (((continuous_const.mul g1).mul (i1.mul i2)).sub ((continuous_const.mul g2).mul (i3.mul i4)))

/-- `π^{3/2} = π √π` (complex power). -/
theorem legendre_pi_three_halves : (π:ℂ)^(3/2:ℂ) = π*Real.sqrt π := by
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (3/2:ℂ) = 1+((1/2:ℝ):ℂ) by push_cast; norm_num, cpow_add _ _ hpi, cpow_one,
    ← ofReal_cpow Real.pi_pos.le, ← Real.sqrt_eq_rpow]

/-- For `s = ±1`, `ν + μ` not a negative integer and `-1 < y < 1`, `olverQSide s ν μ y =
olverQSideHyp s ν μ y`. -/
theorem olverQSide_eq_hyp_real {s : ℝ} (hs : s = 1 ∨ s = -1) {ν μ : ℂ} (h : LegendreQRegular ν μ)
    {y : ℝ} (hy : y ∈ Ioo (-1:ℝ) 1) : olverQSide s ν μ y = olverQSideHyp s ν μ y := by
  obtain ⟨ha, hb⟩ := legendre_Gamma_half_ne_zero h
  have hc := ferrers_sq_mem_cutPlane hy
  have hne := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hy)
  have hE : ferrersEven ν μ y = (1-(y:ℂ)^2)^(μ/2)*regularizedGaussHG ((μ-ν)/2) ((ν+μ+1)/2) (1/2) ((y:ℂ)^2) := by
    unfold ferrersEven
    rw [regularizedGaussHG_euler _ _ _ hc, regularizedGaussHG_symm _ _ _ hc,
      show (1/2:ℂ) - -(ν+μ)/2 - (ν-μ+1)/2 = μ by ring, show (1/2:ℂ) - (ν-μ+1)/2 = (μ-ν)/2 by ring,
      show (1/2:ℂ) - -(ν+μ)/2 = (ν+μ+1)/2 by ring, ← mul_assoc, ← cpow_add _ _ hne]
    ring_nf
  have hO : ferrersOdd ν μ y = y*((1-(y:ℂ)^2)^(μ/2)*regularizedGaussHG ((μ-ν+1)/2) ((ν+μ+2)/2) (3/2) ((y:ℂ)^2)) := by
    unfold ferrersOdd
    rw [regularizedGaussHG_euler _ _ _ hc, regularizedGaussHG_symm _ _ _ hc,
      show (3/2:ℂ) - (1-ν-μ)/2 - (ν-μ+2)/2 = μ by ring, show (3/2:ℂ) - (ν-μ+2)/2 = (μ-ν+1)/2 by ring,
      show (3/2:ℂ) - (1-ν-μ)/2 = (ν+μ+2)/2 by ring, ← mul_assoc ((1-(y:ℂ)^2)^(-μ/2)), ← cpow_add _ _ hne]
    ring_nf
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have e := legendre_reflection_even (ν+μ)
  rw [show (1-(ν+μ))/2 = (1-ν-μ)/2 by ring] at e
  have o := legendre_reflection_odd (ν+μ)
  have r1 : (Gamma ((1-ν-μ)/2))⁻¹ = cos ((ν+μ)*π/2)*Gamma ((ν+μ+1)/2)/π := by
    rw [← e]; field_simp
  have r2 : (Gamma (-(ν+μ)/2))⁻¹ = -sin ((ν+μ)*π/2)*Gamma ((ν+μ+2)/2)/π := by
    rw [show -sin ((ν+μ)*π/2) = π*((Gamma (-(ν+μ)/2))⁻¹*(Gamma ((ν+μ+2)/2))⁻¹) from o.symm]; field_simp
  have hX : exp (-(s:ℂ)*ν*π*I/2) = exp ((s:ℂ)*μ*π*I/2)*(cos ((ν+μ)*π/2)-(s:ℂ)*I*sin ((ν+μ)*π/2)) := by
    rw [legendre_cos_sub_sin_exp hs, ← exp_add]; congr 1; ring
  have hsq : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  unfold olverQSide olverQSideHyp
  rw [ferrersQCont_ofReal, ferrersPCont_ofReal ν μ hy, ferrersQ_even_odd, ferrersP_even_odd ν μ hy, r1, r2,
    hE, hO, legendre_Gamma_plus, hX, legendre_pi_three_halves, cpow_add _ _ two_ne_zero, cpow_one]
  generalize (1-(y:ℂ)^2)^(μ/2) = U
  generalize regularizedGaussHG ((μ-ν)/2) ((ν+μ+1)/2) (1/2) ((y:ℂ)^2) = F1
  generalize regularizedGaussHG ((μ-ν+1)/2) ((ν+μ+2)/2) (3/2) ((y:ℂ)^2) = F3
  generalize (Gamma ((ν-μ+2)/2))⁻¹ = gc
  generalize (Gamma ((ν-μ+1)/2))⁻¹ = gd
  generalize Gamma ((ν+μ+1)/2) = ga at ha
  generalize Gamma ((ν+μ+2)/2) = gb at hb
  generalize exp ((s:ℂ)*μ*π*I/2) = X
  generalize cos ((ν+μ)*π/2) = cb
  generalize sin ((ν+μ)*π/2) = sb
  have h2m : (2:ℂ)^μ ≠ 0 := by simp
  have h2n : (2:ℂ)^ν ≠ 0 := by simp
  generalize (2:ℂ)^μ = T at h2m
  generalize (2:ℂ)^ν = N at h2n
  generalize (Real.sqrt π:ℂ) = S at hsq
  rcases hs with rfl | rfl
  · push_cast
    linear_combination (norm := (field_simp; ring)) (X*π*S/(2*N)*gc*(U*F1)/gb*(-sb))*I_sq
  · push_cast
    linear_combination (norm := (field_simp; ring)) (X*π*S/(2*N)*gc*(U*F1)/gb*(-sb))*I_sq

/-- For `s = ±1`, `ν + μ` not a negative integer and `|z| < 1`, `olverQSide s ν μ z = olverQSideHyp
s ν μ z`, by analytic continuation from `(-1, 1)`. -/
theorem olverQSide_eq_hyp {s : ℝ} (hs : s = 1 ∨ s = -1) {ν μ : ℂ} (h : LegendreQRegular ν μ)
    {z : ℂ} (hz : z ∈ Metric.ball (0:ℂ) 1) : olverQSide s ν μ z = olverQSideHyp s ν μ z := by
  have hR : AnalyticOnNhd ℂ (olverQSide s ν μ) (Metric.ball (0:ℂ) 1) := fun w hw =>
    analyticAt_const.mul ((ferrersQCont_analytic ν μ w hw).sub
      (analyticAt_const.mul (ferrersPCont_analytic ν μ w hw)))
  have h0 : ((0:ℝ):ℂ) ∈ Metric.ball (0:ℂ) 1 := by simp
  refine hR.eqOn_of_preconnected_of_frequently_eq (olverQSideHyp_analytic s ν μ)
    (convex_ball _ _).isPreconnected h0 ?_ hz
  have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (0:ℝ)) (𝓝[≠] ((0:ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_inj] using hr
  apply ht.frequently
  have hI : Ioo (-1:ℝ) 1 ∈ 𝓝 (0:ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  refine Filter.Eventually.frequently (nhdsWithin_le_nhds (Filter.mem_of_superset hI ?_))
  intro y hy
  exact olverQSide_eq_hyp_real hs h hy

/-- For `s = ±1`, `|z| < 1` and `s · Im z > 0`, `𝑸^μ_ν(z) = olverQSideHyp s ν μ z` (the
representation of DLMF 14.23.3), for all `ν, μ`. -/
theorem olverQ_eq_olverQSideHyp {s : ℝ} (hs : s = 1 ∨ s = -1) (ν μ : ℂ)
    {z : ℂ} (hz : z ∈ Metric.ball (0:ℂ) 1) (him : 0 < s*z.im) :
    olverQ ν μ z = olverQSideHyp s ν μ z := by
  have hz1 : z-1 ∈ slitPlane := Or.inr (by
    intro h0; simp at h0; rw [h0] at him; simp at him)
  refine legendre_eq_of_continuous_off_countable (f := fun μ => olverQ ν μ z)
    (g := fun μ => olverQSideHyp s ν μ z) (olverQ_entire_order ν z hz1).continuous
    (continuous_olverQSideHyp_order s ν hz) (S := range fun n : ℕ => -((n:ℂ)+1)-ν)
    (countable_range _) (fun μ' hμ' => ?_) μ
  have hreg : LegendreQRegular ν μ' := fun n hn => hμ' ⟨n, by linear_combination -hn⟩
  show olverQ ν μ' z = olverQSideHyp s ν μ' z
  rw [olverQ_eq_olverQSide hs hreg hz him, olverQSide_eq_hyp hs hreg hz]

/-- Boundary values of `𝑸^μ_ν` in hypergeometric form (DLMF 14.23.3), for all parameters. -/
lemma olverQ_boundary_hyp_aux (ν μ : ℂ) (s : ℝ) (hs : s = 1 ∨ s = -1) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => olverQ ν μ (x+(s:ℂ)*I*ε)) (𝓝[>] (0:ℝ)) (𝓝 (olverQSideHyp s ν μ x)) := by
  have hxD : (x:ℂ) ∈ Metric.ball (0:ℂ) 1 := by
    simp only [Metric.mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs]
    exact abs_lt.mpr ⟨hx.1, hx.2⟩
  have hz : Tendsto (fun ε : ℝ => (x:ℂ)+(s:ℂ)*I*ε) (𝓝[>] (0:ℝ)) (𝓝 (x:ℂ)) := by
    have : Continuous (fun ε : ℝ => (x:ℂ)+(s:ℂ)*I*ε) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim := (olverQSideHyp_analytic s ν μ _ hxD).continuousAt.tendsto.comp hz
  refine hlim.congr' ?_
  have hD : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), (x:ℂ)+(s:ℂ)*I*ε ∈ Metric.ball (0:ℂ) 1 :=
    hz.eventually (Metric.isOpen_ball.mem_nhds hxD)
  filter_upwards [hD, self_mem_nhdsWithin] with ε hεD hε
  have him : 0 < s*((x:ℂ)+(s:ℂ)*I*ε).im := by
    have : ((x:ℂ)+(s:ℂ)*I*ε).im = s*ε := by simp
    rw [this]
    rcases hs with rfl | rfl <;> simp <;> exact hε
  exact (olverQ_eq_olverQSideHyp hs ν μ hεD him).symm

/-- DLMF 14.23.2 (upper side): when `ν + μ` is not a negative integer and `-1 < x < 1`, `𝑸^μ_ν(x +
iε) → e^{μπi/2} (𝖰^μ_ν(x) - (πi/2) 𝖯^μ_ν(x))/Γ(ν+μ+1)` as `ε → 0⁺`. -/
@[dlmf 14.23.E2]
theorem olverQ_boundary_upper (ν μ : ℂ) (hr : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => olverQ ν μ (x+(1:ℂ)*I*ε)) (𝓝[>] (0:ℝ)) (𝓝 (exp ((1:ℂ)*μ*π*I/2)/Gamma (ν+μ+1)*(ferrersQ ν μ x-(1:ℂ)*π*I/2*ferrersP ν μ x))) := by
  simpa only [ofReal_one] using olverQ_boundary_aux ν μ hr 1 (Or.inl rfl) hx

/-- DLMF 14.23.4 (upper side): for `-1 < x < 1`, `𝖯^μ_ν(x) = e^{μπi/2} P^μ_ν(x + i0)`, the boundary
value being taken from above the cut. -/
@[dlmf 14.23.E4]
theorem ferrersP_boundary_inverse_upper (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν μ x=exp ((1:ℂ)*μ*π*I/2)*legendreBoundary (associatedP ν μ) 1 x := by
  rw [legendreBoundary, (associatedP_boundary_aux ν μ 1 (Or.inl rfl) hx).limUnder_eq, ← mul_assoc,
    ← exp_add]
  push_cast; ring_nf; rw [exp_zero, one_mul]

/-- DLMF 14.23.6 (upper side): when `ν + μ` is not a negative integer and `-1 < x < 1`, `𝖰^μ_ν(x) =
e^{-μπi/2} Γ(ν+μ+1) 𝑸^μ_ν(x + i0) + (πi/2) e^{μπi/2} P^μ_ν(x + i0)`. -/
@[dlmf 14.23.E6]
theorem ferrersQ_boundary_inverse_upper {ν μ : ℂ} (hr : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ ν μ x=exp (-(1:ℂ)*μ*π*I/2)*Gamma (ν+μ+1)*legendreBoundary (olverQ ν μ) 1 x+(1:ℂ)*π*I/2*exp ((1:ℂ)*μ*π*I/2)*legendreBoundary (associatedP ν μ) 1 x := by
  have hG1 : Gamma (ν+μ+1) ≠ 0 := Gamma_ne_zero (fun n he => hr n (by linear_combination he))
  have hG : Gamma (ν+μ+1)*(Gamma (ν+μ+1))⁻¹ = 1 := mul_inv_cancel₀ hG1
  have hAB : exp (-(1:ℂ)*μ*π*I/2)*exp ((1:ℂ)*μ*π*I/2) = 1 := by
    rw [← exp_add, show -(1:ℂ)*μ*π*I/2+(1:ℂ)*μ*π*I/2 = 0 by ring, exp_zero]
  rw [legendreBoundary, legendreBoundary, (olverQ_boundary_aux ν μ hr 1 (Or.inl rfl) hx).limUnder_eq,
    (associatedP_boundary_aux ν μ 1 (Or.inl rfl) hx).limUnder_eq]
  simp only [ofReal_one, div_eq_mul_inv]
  simp only [div_eq_mul_inv] at hAB
  linear_combination (-ferrersQ ν μ x)*hAB - (exp (-(1:ℂ)*μ*π*I*2⁻¹)*exp ((1:ℂ)*μ*π*I*2⁻¹)*
    (ferrersQ ν μ x-π*I/2*ferrersP ν μ x))*hG

/-- DLMF 14.23.3 (upper side): for `-1 < x < 1`, `𝑸^μ_ν(x + iε)` tends as `ε → 0⁺` to `e^{-νπi/2}
π^{3/2} (1-x²)^{μ/2}/2^{ν+1} (x 𝐅((μ-ν+1)/2, (ν+μ+2)/2; 3/2; x²)/(Γ((ν-μ+1)/2) Γ((ν+μ+1)/2)) - i
𝐅((μ-ν)/2, (ν+μ+1)/2; 1/2; x²)/(Γ((ν-μ+2)/2) Γ((ν+μ+2)/2)))`. -/
@[dlmf 14.23.E3]
theorem olverQ_boundary_hypergeometric_upper (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => olverQ ν μ (x+(1:ℂ)*I*ε)) (𝓝[>] (0:ℝ)) (𝓝 (exp (-(1:ℂ)*ν*π*I/2)*(π:ℂ)^(3/2:ℂ)*(1-x^2:ℂ)^(μ/2)/2^(ν+1)*(x*regularizedGaussHG ((μ-ν+1)/2) ((ν+μ+2)/2) (3/2) (x^2)/(Gamma ((ν-μ+1)/2)*Gamma ((ν+μ+1)/2))-(1:ℂ)*I*regularizedGaussHG ((μ-ν)/2) ((ν+μ+1)/2) (1/2) (x^2)/(Gamma ((ν-μ+2)/2)*Gamma ((ν+μ+2)/2))))) := by
  have h := olverQ_boundary_hyp_aux ν μ 1 (Or.inl rfl) hx
  simp only [olverQSideHyp, ofReal_one] at h
  simpa only [div_eq_mul_inv, mul_inv] using h

/-- DLMF 14.23.1 (lower side): for `-1 < x < 1`, `P^μ_ν(x - iε) → e^{μπi/2} 𝖯^μ_ν(x)` as `ε →
0⁺`. -/
@[dlmf 14.23.E1]
theorem associatedP_boundary_lower (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => associatedP ν μ (x+(-1:ℂ)*I*ε)) (𝓝[>] (0:ℝ)) (𝓝 (exp (-(-1:ℂ)*μ*π*I/2)*ferrersP ν μ x)) := by
  have h := associatedP_boundary_aux ν μ (-1) (Or.inr rfl) hx
  simpa only [ofReal_neg, ofReal_one] using h

/-- DLMF 14.23.2 (lower side): when `ν + μ` is not a negative integer and `-1 < x < 1`, `𝑸^μ_ν(x -
iε) → e^{-μπi/2} (𝖰^μ_ν(x) + (πi/2) 𝖯^μ_ν(x))/Γ(ν+μ+1)` as `ε → 0⁺`. -/
@[dlmf 14.23.E2]
theorem olverQ_boundary_lower (ν μ : ℂ) (hr : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => olverQ ν μ (x+(-1:ℂ)*I*ε)) (𝓝[>] (0:ℝ)) (𝓝 (exp ((-1:ℂ)*μ*π*I/2)/Gamma (ν+μ+1)*(ferrersQ ν μ x-(-1:ℂ)*π*I/2*ferrersP ν μ x))) := by
  simpa only [ofReal_neg, ofReal_one] using olverQ_boundary_aux ν μ hr (-1) (Or.inr rfl) hx

/-- DLMF 14.23.4 (lower side): for `-1 < x < 1`, `𝖯^μ_ν(x) = e^{-μπi/2} P^μ_ν(x - i0)`, the boundary
value being taken from below the cut. -/
@[dlmf 14.23.E4]
theorem ferrersP_boundary_inverse_lower (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν μ x=exp ((-1:ℂ)*μ*π*I/2)*legendreBoundary (associatedP ν μ) (-1) x := by
  rw [legendreBoundary, (associatedP_boundary_aux ν μ (-1) (Or.inr rfl) hx).limUnder_eq, ← mul_assoc,
    ← exp_add]
  push_cast; ring_nf; rw [exp_zero, one_mul]

/-- DLMF 14.23.6 (lower side): when `ν + μ` is not a negative integer and `-1 < x < 1`, `𝖰^μ_ν(x) =
e^{μπi/2} Γ(ν+μ+1) 𝑸^μ_ν(x - i0) - (πi/2) e^{-μπi/2} P^μ_ν(x - i0)`. -/
@[dlmf 14.23.E6]
theorem ferrersQ_boundary_inverse_lower {ν μ : ℂ} (hr : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ ν μ x=exp (-(-1:ℂ)*μ*π*I/2)*Gamma (ν+μ+1)*legendreBoundary (olverQ ν μ) (-1) x+(-1:ℂ)*π*I/2*exp ((-1:ℂ)*μ*π*I/2)*legendreBoundary (associatedP ν μ) (-1) x := by
  have hG1 : Gamma (ν+μ+1) ≠ 0 := Gamma_ne_zero (fun n he => hr n (by linear_combination he))
  have hG : Gamma (ν+μ+1)*(Gamma (ν+μ+1))⁻¹ = 1 := mul_inv_cancel₀ hG1
  have hAB : exp (-(-1:ℂ)*μ*π*I/2)*exp ((-1:ℂ)*μ*π*I/2) = 1 := by
    rw [← exp_add, show -(-1:ℂ)*μ*π*I/2+(-1:ℂ)*μ*π*I/2 = 0 by ring, exp_zero]
  rw [legendreBoundary, legendreBoundary, (olverQ_boundary_aux ν μ hr (-1) (Or.inr rfl) hx).limUnder_eq,
    (associatedP_boundary_aux ν μ (-1) (Or.inr rfl) hx).limUnder_eq]
  simp only [ofReal_neg, ofReal_one, div_eq_mul_inv]
  simp only [div_eq_mul_inv] at hAB
  linear_combination (-ferrersQ ν μ x)*hAB - (exp (-(-1:ℂ)*μ*π*I*2⁻¹)*exp ((-1:ℂ)*μ*π*I*2⁻¹)*
    (ferrersQ ν μ x+π*I/2*ferrersP ν μ x))*hG

/-- DLMF 14.23.3 (lower side): for `-1 < x < 1`, `𝑸^μ_ν(x - iε)` tends as `ε → 0⁺` to `e^{νπi/2}
π^{3/2} (1-x²)^{μ/2}/2^{ν+1} (x 𝐅((μ-ν+1)/2, (ν+μ+2)/2; 3/2; x²)/(Γ((ν-μ+1)/2) Γ((ν+μ+1)/2)) + i
𝐅((μ-ν)/2, (ν+μ+1)/2; 1/2; x²)/(Γ((ν-μ+2)/2) Γ((ν+μ+2)/2)))`. -/
@[dlmf 14.23.E3]
theorem olverQ_boundary_hypergeometric_lower (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => olverQ ν μ (x+(-1:ℂ)*I*ε)) (𝓝[>] (0:ℝ)) (𝓝 (exp (-(-1:ℂ)*ν*π*I/2)*(π:ℂ)^(3/2:ℂ)*(1-x^2:ℂ)^(μ/2)/2^(ν+1)*(x*regularizedGaussHG ((μ-ν+1)/2) ((ν+μ+2)/2) (3/2) (x^2)/(Gamma ((ν-μ+1)/2)*Gamma ((ν+μ+1)/2))-(-1:ℂ)*I*regularizedGaussHG ((μ-ν)/2) ((ν+μ+1)/2) (1/2) (x^2)/(Gamma ((ν-μ+2)/2)*Gamma ((ν+μ+2)/2))))) := by
  have h := olverQ_boundary_hyp_aux ν μ (-1) (Or.inr rfl) hx
  simp only [olverQSideHyp, ofReal_neg, ofReal_one] at h
  simpa only [div_eq_mul_inv, mul_inv] using h

/-- DLMF 14.23.5: when `ν + μ` is not a negative integer and `-1 < x < 1`, `𝖰^μ_ν(x) = (Γ(ν+μ+1)/2)
(e^{-μπi/2} 𝑸^μ_ν(x + i0) + e^{μπi/2} 𝑸^μ_ν(x - i0))`. -/
@[dlmf 14.23.E5]
theorem ferrersQ_boundary_average {ν μ : ℂ} (hr : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ ν μ x=Gamma (ν+μ+1)/2*(exp (-μ*π*I/2)*legendreBoundary (olverQ ν μ) 1 x+exp (μ*π*I/2)*legendreBoundary (olverQ ν μ) (-1) x) := by
  have hG1 : Gamma (ν+μ+1) ≠ 0 := Gamma_ne_zero (fun n he => hr n (by linear_combination he))
  have hG : Gamma (ν+μ+1)*(Gamma (ν+μ+1))⁻¹ = 1 := mul_inv_cancel₀ hG1
  have hXY : exp (μ*π*I/2)*exp (-μ*π*I/2) = 1 := by
    rw [← exp_add, show μ*π*I/2+(-μ)*π*I/2 = 0 by ring, exp_zero]
  rw [legendreBoundary, legendreBoundary, (olverQ_boundary_aux ν μ hr 1 (Or.inl rfl) hx).limUnder_eq,
    (olverQ_boundary_aux ν μ hr (-1) (Or.inr rfl) hx).limUnder_eq]
  simp only [ofReal_neg, ofReal_one, one_mul, neg_mul]
  rw [show -(μ*π*I)/2 = -μ*π*I/2 by ring]
  simp only [div_eq_mul_inv] at hXY ⊢
  linear_combination (-ferrersQ ν μ x)*hXY - (exp (μ*π*I*2⁻¹)*exp (-μ*π*I*2⁻¹)*ferrersQ ν μ x)*hG

/-- The conical Ferrers function `𝖯^{-μ}_{-1/2+iτ}` is unchanged by `τ ↦ -τ`
(degree reflection `ν ↦ -ν-1`). -/
theorem ferrersP_conical_neg_tau (τ μ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP (-1/2-I*τ) (-μ) x = ferrersP (-1/2+I*τ) (-μ) x := by
  have hz : ‖(1-(x:ℂ))/2‖ < 1 := by
    rw [show (1-(x:ℂ))/2=(((1-x)/2:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hx.1,hx.2]
  unfold ferrersP
  rw [regularizedGaussHG_symm _ _ _ (mem_cutPlane_of_norm_lt_one hz)]
  ring_nf

/-- conicalQHat boundary.

Corrected statement: DLMF 14.23.7 as printed, with second factor `e^{-3μπi/2}`, is false.
With DLMF's own conventions 14.20.2 and 14.23.1–14.23.6 (which `legendreBoundary` and
`associatedQ` follow), the second factor is `e^{μπi/2}`; then the two terms are complex
conjugates and the right side is real, as `Q̂` is. Checked independently with mpmath.
Stronger than DLMF: the standing assumptions `τ ≥ 0`, `μ ≥ 0` of §14.20 are not needed. -/
@[dlmf 14.23.E7]
theorem conicalQHat_boundary {τ μ : ℝ} (hex : τ ≠ 0 ∨ ∀ n : ℕ, μ ≠ n+1/2) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    conicalQHat τ μ x=1/2*exp (3*μ*π*I/2)*legendreBoundary (associatedQ (-1/2+I*τ) (-μ)) (-1) x+1/2*exp (μ*π*I/2)*legendreBoundary (associatedQ (-1/2-I*τ) (-μ)) 1 x := by
  have hreg : ∀ σ : ℂ, (σ = I ∨ σ = -I) → LegendreQRegular (-1/2+σ*τ) (-μ) := by
    intro σ hσ n hn
    rcases hex with h | h
    · have := congrArg Complex.im hn
      rcases hσ with rfl | rfl <;> simp at this <;> exact h this
    · have := congrArg Complex.re hn
      rcases hσ with rfl | rfl <;> simp at this <;> exact h n (by linarith)
  have hr₁ : LegendreQRegular (-1/2+I*τ) (-μ) := hreg I (Or.inl rfl)
  have hr₂ : LegendreQRegular (-1/2-I*τ) (-μ) := by
    simpa [sub_eq_add_neg] using hreg (-I) (Or.inr rfl)
  -- boundary values of `Q^{-μ}_ν` from DLMF 14.23.2
  have hb : ∀ ν : ℂ, LegendreQRegular ν (-μ) → ∀ s : ℝ, (s = 1 ∨ s = -1) →
      legendreBoundary (associatedQ ν (-μ)) s x =
        exp ((-μ:ℂ)*π*I)*exp ((s:ℂ)*(-μ)*π*I/2)*(ferrersQ ν (-μ) x-(s:ℂ)*π*I/2*ferrersP ν (-μ) x) := by
    intro ν hr s hs
    have hG : Gamma (ν+(-μ)+1) ≠ 0 := Gamma_ne_zero (fun n he => hr n (by linear_combination he))
    have h := (olverQ_boundary_aux ν (-μ) hr s hs hx).const_mul (exp ((-μ:ℂ)*π*I)*Gamma (ν+(-μ)+1))
    unfold legendreBoundary associatedQ
    rw [h.limUnder_eq]
    field_simp
  rw [hb _ hr₁ (-1) (Or.inr rfl), hb _ hr₂ 1 (Or.inl rfl), ferrersP_conical_neg_tau τ μ hx]
  have hQ : ferrersQ (-1/2-I*τ) (-μ) x = conj (ferrersQ (-1/2+I*τ) (-μ) x) := by
    rw [ferrersQ_conj _ _ hx]; congr 1 <;> simp [map_div₀, map_ofNat, sub_eq_add_neg]
  rw [hQ]
  unfold conicalQHat conicalP
  set q := ferrersQ (-1/2+I*τ) (-μ) x
  set p := ferrersP (-1/2+I*τ) (-μ) x
  have hre : (((exp (μ*π*I)*q).re : ℝ) : ℂ) = (exp (μ*π*I)*q + conj (exp (μ*π*I)*q))/2 := by
    rw [add_conj]; push_cast; ring
  have hc : conj (exp ((μ:ℂ)*π*I)) = exp (-(μ*π*I)) := by
    rw [← exp_conj]; simp
  rw [hre, map_mul, hc, ofReal_sin, Complex.sin]
  -- express every exponential as a power of `w = e^{μπi/2}`
  have hw : exp ((μ:ℂ)*π*I/2) ≠ 0 := exp_ne_zero _
  have k1 : exp ((μ:ℂ)*π*I) = exp (μ*π*I/2)^2 := by rw [← exp_nat_mul]; ring_nf
  have k2 : exp (-((μ:ℂ)*π*I)) = (exp (μ*π*I/2)^2)⁻¹ := by rw [exp_neg, k1]
  have k3 : exp (3*(μ:ℂ)*π*I/2) = exp (μ*π*I/2)^3 := by rw [← exp_nat_mul]; ring_nf
  have k4 : exp ((-μ:ℂ)*π*I) = (exp (μ*π*I/2)^2)⁻¹ := by rw [← k2]; ring_nf
  have k5 : exp (((-1:ℝ):ℂ)*(-μ)*π*I/2) = exp (μ*π*I/2) := by push_cast; ring_nf
  have k6 : exp (((1:ℝ):ℂ)*(-μ)*π*I/2) = (exp (μ*π*I/2))⁻¹ := by rw [← exp_neg]; push_cast; ring_nf
  rw [k3, k4, k5, k6, show ((μ*π:ℝ):ℂ) = μ*π by push_cast; ring, k1,
    show -((μ:ℂ)*π)*I = -(μ*π*I) by ring, k2]
  push_cast
  field_simp
  ring

/-- Continuation of the value and complex derivative along a path, by its first-order differential system. -/
def IsLegendreTransport (ν μ : ℂ) (γ : ℝ → ℂ) (a b : ℂ) (u v : ℝ → ℂ) : Prop :=
  u 0=a ∧ v 0=b ∧ ContinuousOn u (Icc 0 1) ∧ ContinuousOn v (Icc 0 1) ∧ ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt u (deriv γ t*v t) (Icc 0 1) t ∧ HasDerivWithinAt v (deriv γ t*(2*γ t*v t-(ν*(ν+1)-μ^2/(1-(γ t)^2))*u t)/(1-(γ t)^2)) (Icc 0 1) t

/-- Endpoint value of the continued solution; existence and endpoint uniqueness are not consequences of choice. -/
def legendreTransport (ν μ : ℂ) (γ : ℝ → ℂ) (a b : ℂ) : ℂ :=
  let uv:=Classical.epsilon (fun p : (ℝ → ℂ) × (ℝ → ℂ) => IsLegendreTransport ν μ γ a b p.1 p.2); uv.1 1

/-- Existence on a compact path avoiding both regular singular points. -/
theorem legendreTransport_exists (ν μ a b : ℂ) (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (hreg : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ 1 ∧ γ t ≠ -1) :
    ∃ u v : ℝ → ℂ, IsLegendreTransport ν μ γ a b u v := by
  have hγc : Continuous γ := hγ.continuous
  have hγ'c : Continuous (deriv γ) := hγ.continuous_deriv le_rfl
  have hne : ∀ t ∈ Icc (0:ℝ) 1, 1 - γ t ^ 2 ≠ 0 := fun t ht h0 => by
    have : (1 - γ t) * (1 + γ t) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h | h
    · exact (hreg t ht).1 (by linear_combination -h)
    · exact (hreg t ht).2 (by linear_combination h)
  have hden : ContinuousOn (fun t => 1 - γ t ^ 2) (Icc 0 1) := by fun_prop
  obtain ⟨u, v, hu0, hv0, huv⟩ := ODE.exists_linear_system_Icc (E := ℂ) (𝕜 := ℂ) zero_le_one
    (a₁₁ := fun _ => 0) (a₁₂ := deriv γ)
    (a₂₁ := fun t => -(deriv γ t * (ν*(ν+1) - μ^2/(1 - γ t ^ 2))) / (1 - γ t ^ 2))
    (a₂₂ := fun t => deriv γ t * (2 * γ t) / (1 - γ t ^ 2))
    continuousOn_const hγ'c.continuousOn
    (((hγ'c.continuousOn.mul (continuousOn_const.sub
      (continuousOn_const.div hden hne))).neg).div hden hne)
    ((hγ'c.continuousOn.mul (continuousOn_const.mul hγc.continuousOn)).div hden hne) a b
  refine ⟨u, v, hu0, hv0, fun t ht => (huv t ht).1.continuousWithinAt,
    fun t ht => (huv t ht).2.continuousWithinAt, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := huv t ht
  refine ⟨h1.congr_deriv (by simp), h2.congr_deriv ?_⟩
  have := hne t ht
  simp only [smul_eq_mul]; field_simp; ring

/-- Uniqueness of Legendre transports with given initial data. -/
theorem isLegendreTransport_unique {ν μ a b : ℂ} {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hreg : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ 1 ∧ γ t ≠ -1) {u v u₁ v₁ : ℝ → ℂ}
    (h : IsLegendreTransport ν μ γ a b u v) (h₁ : IsLegendreTransport ν μ γ a b u₁ v₁) :
    EqOn u u₁ (Icc 0 1) ∧ EqOn v v₁ (Icc 0 1) := by
  obtain ⟨hu0, hv0, -, -, hd⟩ := h
  obtain ⟨hu0', hv0', -, -, hd'⟩ := h₁
  have hγc : Continuous γ := hγ.continuous
  have hγ'c : Continuous (deriv γ) := hγ.continuous_deriv le_rfl
  have hne : ∀ t ∈ Icc (0:ℝ) 1, 1 - γ t ^ 2 ≠ 0 := fun t ht h0 => by
    have : (1 - γ t) * (1 + γ t) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h | h
    · exact (hreg t ht).1 (by linear_combination -h)
    · exact (hreg t ht).2 (by linear_combination h)
  have hden : ContinuousOn (fun t => 1 - γ t ^ 2) (Icc 0 1) := by fun_prop
  refine ODE.eqOn_Icc_of_linear_system (𝕜 := ℂ) (t₀ := 0) ⟨le_rfl, zero_le_one⟩
    (a₁₁ := fun _ => 0) (a₁₂ := deriv γ)
    (a₂₁ := fun t => -(deriv γ t * (ν*(ν+1) - μ^2/(1 - γ t ^ 2))) / (1 - γ t ^ 2))
    (a₂₂ := fun t => deriv γ t * (2 * γ t) / (1 - γ t ^ 2))
    continuousOn_const hγ'c.continuousOn ?_ ?_ (fun t ht => ?_) (fun t ht => ?_)
    (by rw [hu0, hu0']) (by rw [hv0, hv0'])
  · refine ContinuousOn.div ?_ hden hne
    refine (hγ'c.continuousOn.mul (continuousOn_const.sub
      (continuousOn_const.div hden hne))).neg
  · exact (hγ'c.continuousOn.mul (continuousOn_const.mul hγc.continuousOn)).div hden hne
  · obtain ⟨h1, h2⟩ := hd t ht
    refine ⟨h1.congr_deriv (by simp), h2.congr_deriv ?_⟩
    have := hne t ht
    simp only [smul_eq_mul]; field_simp; ring
  · obtain ⟨h1, h2⟩ := hd' t ht
    refine ⟨h1.congr_deriv (by simp), h2.congr_deriv ?_⟩
    have := hne t ht
    simp only [smul_eq_mul]; field_simp; ring

/-- Uniqueness identifies the actual analytic continuation, independently of the chosen solution. -/
theorem legendreTransport_unique (ν μ a b : ℂ) (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (hreg : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ 1 ∧ γ t ≠ -1) {u v : ℝ → ℂ} (huv : IsLegendreTransport ν μ γ a b u v) :
    legendreTransport ν μ γ a b=u 1 := by
  have hex : ∃ p : (ℝ → ℂ) × (ℝ → ℂ), IsLegendreTransport ν μ γ a b p.1 p.2 := ⟨(u, v), huv⟩
  have hs := Classical.epsilon_spec hex
  exact (isLegendreTransport_unique hγ hreg hs huv).1 ⟨zero_le_one, le_rfl⟩

/-! ### The `ζ`-form of `𝑸^μ_ν` (used for DLMF 14.24.2 and in `FourierTools`) -/

/-- The right side of the `ζ`-form of `𝑸^μ_ν`:
`√π (1-w²)^μ w^{ν+1} 𝐅(μ+1/2, ν+μ+1; ν+3/2; w²)`. -/
def legFS_G (ν μ w : ℂ) : ℂ :=
  Real.sqrt π * (1 - w^2)^μ * w^(ν+1) * regularizedGaussHG (μ+1/2) (ν+μ+1) (ν+3/2) (w^2)

/-- `legFS_G ν μ` is analytic at `w` when `w ∉ (-∞, 0]` and `1 - w² ∉ (-∞, 0]`. -/
theorem legFS_G_analyticAt (ν μ : ℂ) {w : ℂ} (hw : w ∈ slitPlane) (hw2 : 1 - w^2 ∈ slitPlane) :
    AnalyticAt ℂ (legFS_G ν μ) w := by
  have hF : AnalyticAt ℂ (fun w : ℂ => regularizedGaussHG (μ+1/2) (ν+μ+1) (ν+3/2) (w^2)) w :=
    (analyticAt_regularizedGaussHG _ _ _ (show w^2 ∈ cutPlane from hw2)).comp_of_eq
      (f := fun w : ℂ => w^2) (by fun_prop) rfl
  have h1 : AnalyticAt ℂ (fun w : ℂ => (1 - w^2)^μ) w :=
    (analyticAt_const.sub (analyticAt_id.pow 2)).cpow analyticAt_const hw2
  have h2 : AnalyticAt ℂ (fun w : ℂ => w^(ν+1)) w := analyticAt_id.cpow analyticAt_const hw
  exact ((analyticAt_const.mul h1).mul h2).mul hF

/-- `1 - w² ∈ slitPlane` for `|w| < 1`. -/
theorem legFS_one_sub_sq_mem {w : ℂ} (hw : ‖w‖ < 1) : 1 - w^2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]; left
  have : (w^2).re ≤ ‖w‖^2 := by rw [← norm_pow]; exact re_le_norm _
  simp only [sub_re, one_re]
  nlinarith [norm_nonneg w]

/-- The `ζ`-form of `𝑸^μ_ν` (the complex continuation of DLMF 14.19.3):
`𝑸^μ_ν(z) = √π (1-ζ²)^μ ζ^{ν+1} 𝐅(μ+1/2, ν+μ+1; ν+3/2; ζ²)`, `ζ = z - √(z²-1)`, on `ℂ ∖ (-∞, 1]`. -/
theorem legFS_olverQ_eq_G (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ ν μ z = legFS_G ν μ (legInt_zeta z) := by
  set D : Set ℂ := {w : ℂ | w-1 ∈ slitPlane}
  have hg : AnalyticOnNhd ℂ (fun w => legFS_G ν μ (legInt_zeta w)) D := fun w hw =>
    (legFS_G_analyticAt ν μ (legInt_zeta_mem_slitPlane hw)
      (legFS_one_sub_sq_mem (legInt_norm_zeta_lt_one hw))).comp (legInt_zeta_analyticAt hw)
  have h2 : ((2 : ℝ) : ℂ) ∈ D := by show ((2 : ℝ) : ℂ) - 1 ∈ slitPlane; norm_num
  refine (olverQ_analytic ν μ).eqOn_of_preconnected_of_frequently_eq hg
    isPreconnected_sub_one_mem_slitPlane h2 ?_ hz
  have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (2 : ℝ)) (𝓝[≠] ((2 : ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_inj] using hr
  apply ht.frequently
  apply Eventually.frequently
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (show (1 : ℝ) < 2 by norm_num))] with t ht
  have ht1 : (1:ℝ) < t := ht
  set ξ := Real.arcosh t with hξ
  have hξ0 : 0 < ξ := Real.arcosh_pos ht1
  have hc : Real.cosh ξ = t := Real.cosh_arcosh ht1.le
  have hζ : legInt_zeta t = ((Real.exp (-ξ) : ℝ) : ℂ) := by
    rw [legInt_zeta_real ht1, Real.exp_neg, hξ, Real.exp_arcosh ht1.le,
      Real.add_sqrt_self_sq_sub_one_inv ht1.le]
  have key := toroidalQ_hypergeometric (ν+1/2) μ hξ0
  rw [hc, show ν+1/2-1/2 = ν by ring] at key
  show olverQ ν μ t = legFS_G ν μ (legInt_zeta t)
  rw [key, hζ, legFS_G]
  have he2 : ((Real.exp (-ξ) : ℝ) : ℂ)^2 = ((Real.exp (-2*ξ) : ℝ) : ℂ) := by
    rw [← ofReal_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hpow : ((Real.exp (-ξ) : ℝ) : ℂ)^(ν+1) = (exp ((ν+1/2+1/2)*ξ))⁻¹ := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos _).ne'), ← ofReal_log (Real.exp_pos _).le,
      Real.log_exp, ← exp_neg]
    congr 1; push_cast; ring
  rw [he2, hpow, show ν+1/2+μ+1/2 = ν+μ+1 by ring, show ν+1/2+1 = ν+3/2 by ring]
  ring

/-- Half-circuits of the confocal ellipse, with inherited path orientation. -/
def legendreEllipsePath (z : ℂ) (s : ℤ) (t : ℝ) : ℂ :=
  let q:=z+exp ((log (z-1)+log (z+1))/2); (q*exp (s*π*I*t)+q⁻¹*exp (-s*π*I*t))/2

/-- The value obtained by continuing the solution `F` of the associated Legendre equation (with its
derivative at `z`) along `s` half-circuits of the confocal ellipse through `z`. -/
def legendreEllipseContinued (F : ℂ → ℂ) (ν μ z : ℂ) (s : ℤ) : ℂ :=
  legendreTransport ν μ (legendreEllipsePath z s) (F z) (deriv F z)

end DLMF.Legendre
end
