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
# Legendre boundary values and continuation by ODE transport

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
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

/-- associatedP boundary upper. -/
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

theorem ferrersQCont_ofReal (ν μ : ℂ) (x : ℝ) : ferrersQCont ν μ x = ferrersQ ν μ x := rfl

theorem ferrersPCont_ofReal (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersPCont ν μ x = ferrersP ν μ x := by
  have h1 : 0 < 1 + x := by linarith [hx.1]
  have h2 : 0 < 1 - x := by linarith [hx.2]
  rw [ferrersPCont, ferrersP, ofReal_cpow_eq_exp (div_pos h1 h2), Real.log_div h1.ne' h2.ne',
    show (1:ℂ)+x = ((1+x:ℝ):ℂ) by push_cast; ring, show (1:ℂ)-x = ((1-x:ℝ):ℂ) by push_cast; ring,
    ← ofReal_log h1.le, ← ofReal_log h2.le]
  push_cast; ring_nf

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

theorem ferrersPCont_analytic (ν μ : ℂ) : AnalyticOnNhd ℂ (ferrersPCont ν μ) (Metric.ball (0:ℂ) 1) := by
  intro z hz
  obtain ⟨hp, hm, hc, -, -⟩ := legendre_disk_facts hz
  have hG : AnalyticAt ℂ (fun w : ℂ => regularizedGaussHG (ν+1) (-ν) (1-μ) ((1-w)/2)) z :=
    (analyticAt_regularizedGaussHG _ _ _ hc).comp_of_eq (by fun_prop) rfl
  have hE : AnalyticAt ℂ (fun w : ℂ => exp (μ/2*(log (1+w)-log (1-w)))) z := by
    fun_prop (disch := assumption)
  exact hE.mul hG

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

theorem associatedP_eq_ferrersPCont {s : ℝ} (hs : s = 1 ∨ s = -1) (ν μ : ℂ) {z : ℂ} (hz : 0 < s*z.im) :
    associatedP ν μ z = exp (-(s:ℂ)*μ*π*I/2)*ferrersPCont ν μ z := by
  unfold associatedP ferrersPCont
  rw [legendre_log_sub_one_side hs hz, ← mul_assoc, ← exp_add, add_comm z 1]
  congr 2; ring

/-- The boundary representative: `e^{sμπi/2}/Γ(ν+μ+1) (𝖰 - sπi/2 𝖯)` continued into the disk. -/
noncomputable def olverQSide (s : ℝ) (ν μ z : ℂ) : ℂ :=
  exp ((s:ℂ)*μ*π*I/2)/Gamma (ν+μ+1)*(ferrersQCont ν μ z-(s:ℂ)*π*I/2*ferrersPCont ν μ z)

theorem legendre_cos_sub_sin_side {s : ℝ} (hs : s = 1 ∨ s = -1) (μ : ℂ) :
    exp ((s:ℂ)*μ*π*I/2)*(cos (μ*π)-(s:ℂ)*I*sin (μ*π)) = exp (-(s:ℂ)*μ*π*I/2) := by
  have hc : cos (μ*π)-(s:ℂ)*I*sin (μ*π) = exp (-(s:ℂ)*μ*π*I) := by
    rcases hs with rfl | rfl
    · rw [show -((1:ℝ):ℂ)*μ*π*I = (-(μ*π))*I by push_cast; ring, exp_mul_I, cos_neg, sin_neg]
      push_cast; ring
    · rw [show -((-1:ℝ):ℂ)*μ*π*I = (μ*π)*I by push_cast; ring, exp_mul_I]
      push_cast; ring
  rw [hc, ← exp_add]; congr 1; ring

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

theorem legendre_pi_three_halves : (π:ℂ)^(3/2:ℂ) = π*Real.sqrt π := by
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (3/2:ℂ) = 1+((1/2:ℝ):ℂ) by push_cast; norm_num, cpow_add _ _ hpi, cpow_one,
    ← ofReal_cpow Real.pi_pos.le, ← Real.sqrt_eq_rpow]

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

/-- olverQ boundary upper. -/
@[dlmf 14.23.E2]
theorem olverQ_boundary_upper (ν μ : ℂ) (hr : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => olverQ ν μ (x+(1:ℂ)*I*ε)) (𝓝[>] (0:ℝ)) (𝓝 (exp ((1:ℂ)*μ*π*I/2)/Gamma (ν+μ+1)*(ferrersQ ν μ x-(1:ℂ)*π*I/2*ferrersP ν μ x))) := by
  simpa only [ofReal_one] using olverQ_boundary_aux ν μ hr 1 (Or.inl rfl) hx

/-- ferrersP boundary inverse upper. -/
@[dlmf 14.23.E4]
theorem ferrersP_boundary_inverse_upper (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν μ x=exp ((1:ℂ)*μ*π*I/2)*legendreBoundary (associatedP ν μ) 1 x := by
  rw [legendreBoundary, (associatedP_boundary_aux ν μ 1 (Or.inl rfl) hx).limUnder_eq, ← mul_assoc,
    ← exp_add]
  push_cast; ring_nf; rw [exp_zero, one_mul]

/-- ferrersQ boundary inverse upper. -/
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

/-- olverQ boundary hypergeometric upper. -/
@[dlmf 14.23.E3]
theorem olverQ_boundary_hypergeometric_upper (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => olverQ ν μ (x+(1:ℂ)*I*ε)) (𝓝[>] (0:ℝ)) (𝓝 (exp (-(1:ℂ)*ν*π*I/2)*(π:ℂ)^(3/2:ℂ)*(1-x^2:ℂ)^(μ/2)/2^(ν+1)*(x*regularizedGaussHG ((μ-ν+1)/2) ((ν+μ+2)/2) (3/2) (x^2)/(Gamma ((ν-μ+1)/2)*Gamma ((ν+μ+1)/2))-(1:ℂ)*I*regularizedGaussHG ((μ-ν)/2) ((ν+μ+1)/2) (1/2) (x^2)/(Gamma ((ν-μ+2)/2)*Gamma ((ν+μ+2)/2))))) := by
  have h := olverQ_boundary_hyp_aux ν μ 1 (Or.inl rfl) hx
  simp only [olverQSideHyp, ofReal_one] at h
  simpa only [div_eq_mul_inv, mul_inv] using h

/-- associatedP boundary lower. -/
@[dlmf 14.23.E1]
theorem associatedP_boundary_lower (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => associatedP ν μ (x+(-1:ℂ)*I*ε)) (𝓝[>] (0:ℝ)) (𝓝 (exp (-(-1:ℂ)*μ*π*I/2)*ferrersP ν μ x)) := by
  have h := associatedP_boundary_aux ν μ (-1) (Or.inr rfl) hx
  simpa only [ofReal_neg, ofReal_one] using h

/-- olverQ boundary lower. -/
@[dlmf 14.23.E2]
theorem olverQ_boundary_lower (ν μ : ℂ) (hr : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => olverQ ν μ (x+(-1:ℂ)*I*ε)) (𝓝[>] (0:ℝ)) (𝓝 (exp ((-1:ℂ)*μ*π*I/2)/Gamma (ν+μ+1)*(ferrersQ ν μ x-(-1:ℂ)*π*I/2*ferrersP ν μ x))) := by
  simpa only [ofReal_neg, ofReal_one] using olverQ_boundary_aux ν μ hr (-1) (Or.inr rfl) hx

/-- ferrersP boundary inverse lower. -/
@[dlmf 14.23.E4]
theorem ferrersP_boundary_inverse_lower (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν μ x=exp ((-1:ℂ)*μ*π*I/2)*legendreBoundary (associatedP ν μ) (-1) x := by
  rw [legendreBoundary, (associatedP_boundary_aux ν μ (-1) (Or.inr rfl) hx).limUnder_eq, ← mul_assoc,
    ← exp_add]
  push_cast; ring_nf; rw [exp_zero, one_mul]

/-- ferrersQ boundary inverse lower. -/
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

/-- olverQ boundary hypergeometric lower. -/
@[dlmf 14.23.E3]
theorem olverQ_boundary_hypergeometric_lower (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => olverQ ν μ (x+(-1:ℂ)*I*ε)) (𝓝[>] (0:ℝ)) (𝓝 (exp (-(-1:ℂ)*ν*π*I/2)*(π:ℂ)^(3/2:ℂ)*(1-x^2:ℂ)^(μ/2)/2^(ν+1)*(x*regularizedGaussHG ((μ-ν+1)/2) ((ν+μ+2)/2) (3/2) (x^2)/(Gamma ((ν-μ+1)/2)*Gamma ((ν+μ+1)/2))-(-1:ℂ)*I*regularizedGaussHG ((μ-ν)/2) ((ν+μ+1)/2) (1/2) (x^2)/(Gamma ((ν-μ+2)/2)*Gamma ((ν+μ+2)/2))))) := by
  have h := olverQ_boundary_hyp_aux ν μ (-1) (Or.inr rfl) hx
  simp only [olverQSideHyp, ofReal_neg, ofReal_one] at h
  simpa only [div_eq_mul_inv, mul_inv] using h

/-- ferrersQ boundary average. -/
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

/-- legendreEllipseContinued. -/
def legendreEllipseContinued (F : ℂ → ℂ) (ν μ z : ℂ) (s : ℤ) : ℂ :=
  legendreTransport ν μ (legendreEllipsePath z s) (F z) (deriv F z)

/-! ### Helpers for DLMF 14.24.2: the explicit transport of `𝑸^μ_ν` along the ellipse -/

/-- The Joukowski map `J(w) = (w + w⁻¹)/2` sends `{|w| < 1} ∖ (-∞, 0]` into `ℂ ∖ (-∞, 1]`. -/
theorem legInt_joukowski_mem {w : ℂ} (hw1 : ‖w‖ < 1) (hw : w ∈ slitPlane) :
    (w + w⁻¹)/2 - 1 ∈ slitPlane := by
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  have hn : 0 < normSq w := normSq_pos.mpr hw0
  have hn1 : normSq w < 1 := by
    rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  rw [mem_slitPlane_iff]
  by_cases hb : w.im = 0
  · left
    have ha : 0 < w.re := by
      rcases mem_slitPlane_iff.mp hw with h | h
      · exact h
      · exact absurd hb h
    have hnq : normSq w = w.re^2 := by rw [normSq_apply, hb]; ring
    simp only [sub_re, div_re, add_re, inv_re, one_re, hnq]
    norm_num
    have : w.re < 1 := by nlinarith
    have e : (w.re + w.re / w.re ^ 2) * 2 / 4 - 1 = (w.re - 1)^2/(2*w.re) := by field_simp; ring
    have := div_pos (pow_pos (show (0:ℝ) < 1 - w.re by linarith) 2) (by linarith : (0:ℝ) < 2*w.re)
    rw [show (1 - w.re)^2 = (w.re - 1)^2 by ring] at this
    linarith
  · right
    simp only [sub_im, div_im, add_im, inv_im, one_im]
    norm_num
    intro h
    have : w.im * (1 - 1/normSq w) = 0 := by
      field_simp; field_simp at h; linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hb h1
    · have : 1/normSq w = 1 := by linarith
      rw [div_eq_one_iff_eq hn.ne'] at this; linarith

/-- `ζ(J(w)) = w` for `|w| < 1`, `w ∉ (-∞, 0]`. -/
theorem legInt_zeta_joukowski {w : ℂ} (hw1 : ‖w‖ < 1) (hw : w ∈ slitPlane) :
    legInt_zeta ((w + w⁻¹)/2) = w := by
  have hm := legInt_joukowski_mem hw1 hw
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  have h := legInt_zeta_mul hm
  set y := legInt_zeta ((w + w⁻¹)/2)
  have hy : (y - w) * (y - w⁻¹) = 0 := by
    have : w * w⁻¹ = 1 := mul_inv_cancel₀ hw0
    linear_combination -h + this
  rcases mul_eq_zero.mp hy with h1 | h1
  · linear_combination h1
  · exfalso
    have hy1 : ‖y‖ < 1 := legInt_norm_zeta_lt_one hm
    rw [show y = w⁻¹ by linear_combination h1, norm_inv] at hy1
    have := (one_lt_inv₀ (norm_pos_iff.mpr hw0)).mpr hw1
    linarith

/-- The moving point `w(t) = ζ e^{-sπit}` of DLMF 14.24.2. -/
noncomputable def legInt_ew (ζ : ℂ) (s : ℤ) (t : ℝ) : ℂ := ζ * exp (-(s:ℂ)*π*I*t)

/-- The ellipse path is `J(w(t))`. -/
theorem legInt_path_eq {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) (t : ℝ) :
    legendreEllipsePath z s t = (legInt_ew (legInt_zeta z) s t + (legInt_ew (legInt_zeta z) s t)⁻¹)/2 := by
  have h0 := legInt_zeta_ne_zero hz
  have hq : z + exp ((log (z-1) + log (z+1))/2) = (legInt_zeta z)⁻¹ := by
    have := legInt_zeta_mul hz
    have h2 : z + exp ((log (z-1) + log (z+1))/2) = 2*z - legInt_zeta z := by
      simp only [legInt_zeta, legInt_root]; ring
    rw [h2]; exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact this)
  simp only [legendreEllipsePath, legInt_ew]
  rw [hq, mul_inv, inv_inv, ← exp_neg, show -(-(s:ℂ)*π*I*t) = (s:ℂ)*π*I*t by ring,
    show -(s:ℂ)*π*I*t = -(s:ℂ)*π*I*t from rfl]
  ring

/-- `|w(t)| = |ζ|`. -/
theorem legInt_norm_ew (ζ : ℂ) (s : ℤ) (t : ℝ) : ‖legInt_ew ζ s t‖ = ‖ζ‖ := by
  rw [legInt_ew, norm_mul, norm_exp]
  simp

/-- The derivative of `w(t)`. -/
theorem legInt_hasDerivAt_ew (ζ : ℂ) (s : ℤ) (t : ℝ) :
    HasDerivAt (legInt_ew ζ s) (-(s:ℂ)*π*I * legInt_ew ζ s t) t := by
  have h := ((hasDerivAt_id (t:ℂ)).const_mul (-(s:ℂ)*π*I)).cexp.const_mul ζ
  have h2 := h.comp_ofReal
  simp only [legInt_ew]
  convert h2 using 1
  · ext t; simp only [legInt_ew, id]
  · simp only [id]; ring_nf

/-- The explicit transport of `𝑸^μ_ν` along the ellipse path:
`u(t) = √π (1-w²)^μ ζ^{ν+1} e^{-(ν+1)sπit} 𝐅(μ+1/2, ν+μ+1; ν+3/2; w²)`, `w = ζ e^{-sπit}`. -/
noncomputable def legInt_eu (ν μ ζ : ℂ) (s : ℤ) (t : ℝ) : ℂ :=
  Real.sqrt π * (1 - legInt_ew ζ s t ^ 2)^μ * (ζ^(ν+1) * exp (-(ν+1)*((s:ℂ)*π*I*t))) *
    regularizedGaussHG (μ+1/2) (ν+μ+1) (ν+3/2) (legInt_ew ζ s t ^ 2)

/-- Locally along the path, the transport is a constant multiple of `𝑸^μ_ν(σ z)`, `σ = ±1`. -/
theorem legInt_eu_local (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) {σ : ℂ}
    (hσ : σ = 1 ∨ σ = -1) {t₀ : ℝ} (ht₀ : σ * legInt_ew (legInt_zeta z) s t₀ ∈ slitPlane) :
    ∀ᶠ t in 𝓝 t₀, (σ * legInt_ew (legInt_zeta z) s t ∈ slitPlane) ∧
      legInt_eu ν μ (legInt_zeta z) s t =
      exp ((ν+1)*(log (legInt_zeta z) - (log (σ * legInt_ew (legInt_zeta z) s t₀) + (s:ℂ)*π*I*t₀))) *
        olverQ ν μ (σ * ((legInt_ew (legInt_zeta z) s t + (legInt_ew (legInt_zeta z) s t)⁻¹)/2)) := by
  set ζ := legInt_zeta z with hζ
  have hζ0 : ζ ≠ 0 := legInt_zeta_ne_zero hz
  have hζ1 : ‖ζ‖ < 1 := legInt_norm_zeta_lt_one hz
  set w := legInt_ew ζ s with hw
  have hσ2 : σ^2 = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hσ0 : σ ≠ 0 := by rintro rfl; norm_num at hσ2
  have hwc : Continuous w := by
    rw [hw]; unfold legInt_ew; fun_prop
  have hU : ∀ᶠ t in 𝓝 t₀, σ * w t ∈ slitPlane :=
    ((continuous_const.mul hwc).continuousAt (x := t₀)).preimage_mem_nhds (isOpen_slitPlane.mem_nhds ht₀)
  obtain ⟨l, r, hlr, hsub⟩ := hU.exists_Ioo_subset
  set h : ℝ → ℂ := fun t => log (σ * w t) + (s:ℂ)*π*I*t with hh
  have hdh : ∀ t ∈ Ioo l r, HasDerivAt h 0 t := by
    intro t ht
    have hm : σ * w t ∈ slitPlane := hsub ht
    have h1 := ((legInt_hasDerivAt_ew ζ s t).const_mul σ).clog_real hm
    have h2 : HasDerivAt (fun t : ℝ => (s:ℂ)*π*I*t) ((s:ℂ)*π*I) t := by
      have := ((hasDerivAt_id (t:ℂ)).const_mul ((s:ℂ)*π*I)).comp_ofReal
      simpa using this
    convert h1.add h2 using 1
    have hw0 : w t ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hm; exact slitPlane_ne_zero hm rfl
    have hinv : legInt_ew ζ s t * (legInt_ew ζ s t)⁻¹ = 1 := mul_inv_cancel₀ hw0
    field_simp
    linear_combination ((s:ℂ)*π*I) * hinv
  have hconst : ∀ t ∈ Ioo l r, h t = h t₀ := fun t ht =>
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun x hx => (hdh x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hdh x hx).deriv) ht hlr
  filter_upwards [isOpen_Ioo.mem_nhds hlr] with t ht
  have hm : σ * w t ∈ slitPlane := hsub ht
  refine ⟨hm, ?_⟩
  have hn : ‖σ * w t‖ < 1 := by
    rw [norm_mul, show ‖σ‖ = 1 by rcases hσ with h | h <;> rw [h] <;> simp, one_mul, hw,
      legInt_norm_ew]; exact hζ1
  have hJ := legInt_joukowski_mem hn hm
  have hσJ : σ * ((w t + (w t)⁻¹)/2) = (σ * w t + (σ * w t)⁻¹)/2 := by
    rcases hσ with h | h
    · rw [h]; simp
    · rw [h]; simp; ring
  rw [hσJ, legFS_olverQ_eq_G ν μ hJ, legInt_zeta_joukowski hn hm, legFS_G, legInt_eu]
  have hw0 : σ * w t ≠ 0 := slitPlane_ne_zero hm
  have hsq : (σ * w t)^2 = w t ^ 2 := by rw [mul_pow, hσ2, one_mul]
  have hht := hconst t ht
  simp only [hh] at hht
  have hp : (σ * w t)^(ν+1) = exp ((ν+1)*(log (σ * w t₀) + (s:ℂ)*π*I*t₀ - (s:ℂ)*π*I*t)) := by
    rw [cpow_def_of_ne_zero hw0, ← hht]; congr 1; ring
  have hz' : ζ^(ν+1) = exp ((ν+1) * log ζ) := by rw [cpow_def_of_ne_zero hζ0]; ring_nf
  rw [hsq, hp, hz']
  have e : exp ((ν+1) * log ζ) * exp (-(ν+1)*((s:ℂ)*π*I*t)) =
      exp ((ν+1)*(log ζ - (log (σ * w t₀) + (s:ℂ)*π*I*t₀))) *
        exp ((ν+1)*(log (σ * w t₀) + (s:ℂ)*π*I*t₀ - (s:ℂ)*π*I*t)) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  rw [e]; ring

/-- The derivative of the ellipse path, `γ'(t) = -sπi (w - w⁻¹)/2`. -/
noncomputable def legInt_gd (ζ : ℂ) (s : ℤ) (t : ℝ) : ℂ :=
  -(s:ℂ)*π*I * (legInt_ew ζ s t - (legInt_ew ζ s t)⁻¹)/2

/-- `w(t) ≠ 0`. -/
theorem legInt_ew_ne_zero {ζ : ℂ} (hζ : ζ ≠ 0) (s : ℤ) (t : ℝ) : legInt_ew ζ s t ≠ 0 :=
  mul_ne_zero hζ (exp_ne_zero _)

/-- The ellipse path has derivative `legInt_gd`. -/
theorem legInt_hasDerivAt_path {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) (t : ℝ) :
    HasDerivAt (legendreEllipsePath z s) (legInt_gd (legInt_zeta z) s t) t := by
  have h0 := legInt_ew_ne_zero (legInt_zeta_ne_zero hz) s t
  have hw := legInt_hasDerivAt_ew (legInt_zeta z) s t
  have h := (hw.add (hw.inv h0)).div_const 2
  have he : legendreEllipsePath z s = fun t =>
      (legInt_ew (legInt_zeta z) s t + (legInt_ew (legInt_zeta z) s t)⁻¹)/2 :=
    funext fun t => legInt_path_eq hz s t
  rw [he]
  convert h using 1
  simp only [legInt_gd]
  field_simp
  ring

/-- `γ'(t) ≠ 0` for `s ≠ 0`. -/
theorem legInt_gd_ne_zero {z : ℂ} (hz : z-1 ∈ slitPlane) {s : ℤ} (hs : s ≠ 0) (t : ℝ) :
    legInt_gd (legInt_zeta z) s t ≠ 0 := by
  have h0 := legInt_ew_ne_zero (legInt_zeta_ne_zero hz) s t
  have hn : ‖legInt_ew (legInt_zeta z) s t‖ < 1 := by
    rw [legInt_norm_ew]; exact legInt_norm_zeta_lt_one hz
  simp only [legInt_gd]
  refine div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast hs))
    (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero) ?_) two_ne_zero
  intro h
  have h1 : legInt_ew (legInt_zeta z) s t ^ 2 = 1 := by
    field_simp at h; linear_combination h
  have := congrArg norm h1
  rw [norm_pow, norm_one] at this
  nlinarith [norm_nonneg (legInt_ew (legInt_zeta z) s t)]

/-- A nonzero point outside `ℂ ∖ (-∞, 0]` has its negative inside. -/
theorem legInt_neg_mem_slitPlane {w : ℂ} (hw0 : w ≠ 0) (hw : w ∉ slitPlane) : -w ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hw ⊢
  push Not at hw
  left
  have : w.re ≠ 0 := fun h => hw0 (Complex.ext (by simp [h]) (by simp [hw.2]))
  simp only [neg_re]
  exact neg_pos.mpr (lt_of_le_of_ne hw.1 this)

/-- Local data at each point of the path: `u = c 𝑸(σ γ)` near `t₀`. -/
theorem legInt_eu_local' (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) (t₀ : ℝ) :
    ∃ c σ : ℂ, σ^2 = 1 ∧ ∀ᶠ t in 𝓝 t₀, σ * legendreEllipsePath z s t - 1 ∈ slitPlane ∧
      legInt_eu ν μ (legInt_zeta z) s t = c * olverQ ν μ (σ * legendreEllipsePath z s t) := by
  have h0 := legInt_ew_ne_zero (legInt_zeta_ne_zero hz) s t₀
  have key : ∀ σ : ℂ, (σ = 1 ∨ σ = -1) → σ * legInt_ew (legInt_zeta z) s t₀ ∈ slitPlane →
      ∃ c σ : ℂ, σ^2 = 1 ∧ ∀ᶠ t in 𝓝 t₀, σ * legendreEllipsePath z s t - 1 ∈ slitPlane ∧
      legInt_eu ν μ (legInt_zeta z) s t = c * olverQ ν μ (σ * legendreEllipsePath z s t) := by
    intro σ hσ hm
    refine ⟨exp ((ν+1)*(log (legInt_zeta z) - (log (σ * legInt_ew (legInt_zeta z) s t₀) +
      (s:ℂ)*π*I*t₀))), σ, by rcases hσ with h | h <;> rw [h] <;> norm_num, ?_⟩
    filter_upwards [legInt_eu_local ν μ hz s hσ hm] with t ⟨hmt, he⟩
    have hn : ‖σ * legInt_ew (legInt_zeta z) s t‖ < 1 := by
      rw [norm_mul, show ‖σ‖ = 1 by rcases hσ with h | h <;> rw [h] <;> simp, one_mul,
        legInt_norm_ew]; exact legInt_norm_zeta_lt_one hz
    have hσJ : σ * ((legInt_ew (legInt_zeta z) s t + (legInt_ew (legInt_zeta z) s t)⁻¹)/2) =
        (σ * legInt_ew (legInt_zeta z) s t + (σ * legInt_ew (legInt_zeta z) s t)⁻¹)/2 := by
      rcases hσ with h | h
      · rw [h]; simp
      · rw [h]; simp; ring
    rw [legInt_path_eq hz s t]
    refine ⟨?_, he⟩
    rw [hσJ]; exact legInt_joukowski_mem hn hmt
  by_cases hm : legInt_ew (legInt_zeta z) s t₀ ∈ slitPlane
  · exact key 1 (Or.inl rfl) (by rwa [one_mul])
  · exact key (-1) (Or.inr rfl) (by rw [neg_one_mul]; exact legInt_neg_mem_slitPlane h0 hm)

/-- The transport `u` satisfies the first-order Legendre system along the ellipse path, with
`v = u'/γ'`. -/
theorem legInt_eu_deriv (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) {s : ℤ} (hs : s ≠ 0) (t₀ : ℝ) :
    HasDerivAt (legInt_eu ν μ (legInt_zeta z) s)
      (deriv (legendreEllipsePath z s) t₀ * (deriv (legInt_eu ν μ (legInt_zeta z) s) t₀ /
        legInt_gd (legInt_zeta z) s t₀)) t₀ ∧
    HasDerivAt (fun t => deriv (legInt_eu ν μ (legInt_zeta z) s) t / legInt_gd (legInt_zeta z) s t)
      (deriv (legendreEllipsePath z s) t₀ * (2 * legendreEllipsePath z s t₀ *
        (deriv (legInt_eu ν μ (legInt_zeta z) s) t₀ / legInt_gd (legInt_zeta z) s t₀) -
        (ν*(ν+1) - μ^2/(1 - (legendreEllipsePath z s t₀)^2)) * legInt_eu ν μ (legInt_zeta z) s t₀) /
        (1 - (legendreEllipsePath z s t₀)^2)) t₀ := by
  obtain ⟨c, σ, hσ2, hev⟩ := legInt_eu_local' ν μ hz s t₀
  set γ := legendreEllipsePath z s with hγdef
  set u := legInt_eu ν μ (legInt_zeta z) s with hudef
  set gd := legInt_gd (legInt_zeta z) s with hgd
  set Q := olverQ ν μ with hQdef
  have hγ : ∀ t, HasDerivAt γ (gd t) t := legInt_hasDerivAt_path hz s
  have hdγ : ∀ t, deriv γ t = gd t := fun t => (hγ t).deriv
  have hgd0 : ∀ t, gd t ≠ 0 := legInt_gd_ne_zero hz hs
  have hf : ∀ t, σ * γ t - 1 ∈ slitPlane →
      HasDerivAt (fun t => c * Q (σ * γ t)) (c * (deriv Q (σ * γ t) * (σ * gd t))) t := by
    intro t ht
    have hQ : HasDerivAt Q (deriv Q (σ * γ t)) (σ * γ t) :=
      (olverQ_analytic ν μ _ ht).differentiableAt.hasDerivAt
    exact (hQ.comp t ((hγ t).const_mul σ)).const_mul c
  have hloc : ∀ᶠ t in 𝓝 t₀, σ * γ t - 1 ∈ slitPlane ∧ HasDerivAt u (c * (deriv Q (σ * γ t) * (σ * gd t))) t := by
    filter_upwards [hev.eventually_nhds] with t ht
    have hm := ht.self_of_nhds.1
    refine ⟨hm, (hf t hm).congr_of_eventuallyEq ?_⟩
    filter_upwards [ht] with y hy using hy.2
  have hV : ∀ᶠ t in 𝓝 t₀, deriv u t / gd t = c * σ * deriv Q (σ * γ t) := by
    filter_upwards [hloc] with t ⟨_, ht⟩
    rw [ht.deriv]; field_simp [hgd0 t]
  obtain ⟨hm0, hu0⟩ := hloc.self_of_nhds
  have hV0 := hV.self_of_nhds
  rw [hdγ, hV0]
  have hQ2 : HasDerivAt (deriv Q) (iteratedDeriv 2 Q (σ * γ t₀)) (σ * γ t₀) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (olverQ_analytic ν μ _ hm0).deriv.differentiableAt.hasDerivAt
  have hg := ((hQ2.comp t₀ ((hγ t₀).const_mul σ)).const_mul (c*σ))
  have hode := olverQ_ode ν μ hm0
  have hγ2 : (σ * γ t₀)^2 = γ t₀ ^ 2 := by rw [mul_pow, hσ2, one_mul]
  rw [hγ2] at hode
  have hev0 := hev.self_of_nhds
  refine ⟨?_, ?_⟩
  · convert hu0 using 1; ring
  · refine (hg.congr_of_eventuallyEq hV).congr_deriv ?_
    rw [hev0.2]
    have h1 : 1 - γ t₀ ^ 2 ≠ 0 := by
      rw [← hγ2]
      have ha : σ * γ t₀ - 1 ≠ 0 := slitPlane_ne_zero hm0
      have hb : σ * γ t₀ + 1 ≠ 0 := by
        intro h; rw [show σ * γ t₀ - 1 = -2 by linear_combination h] at hm0
        rw [mem_slitPlane_iff] at hm0; norm_num at hm0
      have : 1 - (σ * γ t₀)^2 = -((σ * γ t₀ - 1) * (σ * γ t₀ + 1)) := by ring
      rw [this]; exact neg_ne_zero.mpr (mul_ne_zero ha hb)
    rw [← hQdef] at hode
    generalize Q (σ * γ t₀) = A at hode ⊢
    generalize deriv Q (σ * γ t₀) = B at hode ⊢
    generalize iteratedDeriv 2 Q (σ * γ t₀) = C at hode ⊢
    have hode' : (1 - γ t₀ ^ 2)^2 * C - 2 * (σ * γ t₀) * B * (1 - γ t₀ ^ 2) +
        (ν * (ν + 1) * (1 - γ t₀ ^ 2) - μ ^ 2) * A = 0 := by
      field_simp at hode; linear_combination hode
    field_simp
    linear_combination (c * gd t₀ * (1 - γ t₀ ^ 2)^2 * C) * hσ2 +
      (c * gd t₀) * hode'

/-- The ellipse path avoids `±1`. -/
theorem legInt_path_ne {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) (t : ℝ) :
    legendreEllipsePath z s t ≠ 1 ∧ legendreEllipsePath z s t ≠ -1 := by
  have h0 := legInt_ew_ne_zero (legInt_zeta_ne_zero hz) s t
  have hn : ‖legInt_ew (legInt_zeta z) s t‖ < 1 := by
    rw [legInt_norm_ew]; exact legInt_norm_zeta_lt_one hz
  rw [legInt_path_eq hz s t]
  set w := legInt_ew (legInt_zeta z) s t
  have key : ∀ σ : ℂ, σ^2 = 1 → (w + w⁻¹)/2 ≠ σ := by
    intro σ hσ h
    have h1 : (w - σ)^2 = 0 := by
      field_simp at h; linear_combination h + hσ
    have h2 : w = σ := by linear_combination pow_eq_zero_iff (n := 2) two_ne_zero |>.mp h1
    have h3 : ‖σ‖ = 1 := by
      have := congrArg norm hσ; rw [norm_pow, norm_one] at this
      nlinarith [norm_nonneg σ]
    rw [h2, h3] at hn; exact lt_irrefl _ hn
  exact ⟨key 1 (by norm_num), key (-1) (by norm_num)⟩

/-- The initial data of the transport: `u(0) = 𝑸^μ_ν(z)`, `u'(0) = γ'(0) 𝑸'(z)`. -/
theorem legInt_eu_zero (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    legInt_eu ν μ (legInt_zeta z) s 0 = olverQ ν μ z ∧
    HasDerivAt (legInt_eu ν μ (legInt_zeta z) s)
      (deriv (olverQ ν μ) z * legInt_gd (legInt_zeta z) s 0) 0 := by
  have hw0 : legInt_ew (legInt_zeta z) s 0 = legInt_zeta z := by simp [legInt_ew]
  have hm : (1:ℂ) * legInt_ew (legInt_zeta z) s 0 ∈ slitPlane := by
    rw [one_mul, hw0]; exact legInt_zeta_mem_slitPlane hz
  have hev := legInt_eu_local ν μ hz s (Or.inl rfl) hm
  rw [one_mul, hw0] at hev
  simp only [ofReal_zero, mul_zero, add_zero, sub_self, exp_zero, one_mul] at hev
  have hγ0 : legendreEllipsePath z s 0 = z := by
    rw [legInt_path_eq hz s 0, hw0, legInt_two_mul_eq hz |>.symm]; ring
  have hev' : legInt_eu ν μ (legInt_zeta z) s =ᶠ[𝓝 0] fun t => olverQ ν μ (legendreEllipsePath z s t) := by
    filter_upwards [hev] with t ht
    rw [ht.2, legInt_path_eq hz s t]
  refine ⟨by rw [hev'.self_of_nhds]; show olverQ ν μ (legendreEllipsePath z s 0) = _; rw [hγ0], ?_⟩
  have hQ : HasDerivAt (olverQ ν μ) (deriv (olverQ ν μ) z) (legendreEllipsePath z s 0) := by
    rw [hγ0]; exact (olverQ_analytic ν μ z hz).differentiableAt.hasDerivAt
  exact (hQ.comp 0 (legInt_hasDerivAt_path hz s 0)).congr_of_eventuallyEq hev'

-- DLMF 14.24.1 `associatedP_ellipse_continuation` is stated below, after 14.24.2 and 14.24.3, which its proof uses.

/-- olverQ ellipse continuation. Along the ellipse `γ(t) = J(w(t))`, `w(t) = ζ e^{-sπit}`, the
transport is `√π (1-w²)^μ ζ^{ν+1} e^{-(ν+1)sπit} 𝐅(μ+1/2, ν+μ+1; ν+3/2; w²)` (`legInt_eu`),
locally a multiple of `𝑸^μ_ν(±γ)` by the `ζ`-form `legFS_olverQ_eq_G`. -/
@[dlmf 14.24.E2]
theorem olverQ_ellipse_continuation (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    legendreEllipseContinued (olverQ ν μ) ν μ z s=(-1:ℂ)^s*exp (-s*ν*π*I)*olverQ ν μ z := by
  have hreg : ∀ t ∈ Icc (0:ℝ) 1, legendreEllipsePath z s t ≠ 1 ∧ legendreEllipsePath z s t ≠ -1 :=
    fun t _ => legInt_path_ne hz s t
  have hγc : ContDiff ℝ 1 (legendreEllipsePath z s) := by
    have he : legendreEllipsePath z s = fun t : ℝ =>
        ((z + exp ((log (z-1) + log (z+1))/2)) * exp ((s:ℂ)*π*I * ofRealCLM t) +
          (z + exp ((log (z-1) + log (z+1))/2))⁻¹ * exp ((-(s:ℂ))*π*I * ofRealCLM t))/2 := by
      funext t; simp only [legendreEllipsePath, ofRealCLM_apply]
    rw [he]
    have h1 : ContDiff ℝ 1 (fun t : ℝ => ofRealCLM t) := ofRealCLM.contDiff
    fun_prop
  obtain ⟨hu0, hd0⟩ := legInt_eu_zero ν μ hz s
  by_cases hs : s = 0
  · subst hs
    have hγ : legendreEllipsePath z 0 = fun _ => z := funext fun t => by
      have hw : legInt_ew (legInt_zeta z) 0 t = legInt_zeta z := by simp [legInt_ew]
      rw [legInt_path_eq hz 0 t, hw, ← legInt_two_mul_eq hz]; ring
    have hd : ∀ t, deriv (legendreEllipsePath z 0) t = 0 := fun t => by rw [hγ]; simp
    have huv : IsLegendreTransport ν μ (legendreEllipsePath z 0) (olverQ ν μ z) (deriv (olverQ ν μ) z)
        (fun _ => olverQ ν μ z) (fun _ => deriv (olverQ ν μ) z) := by
      refine ⟨rfl, rfl, continuousOn_const, continuousOn_const, fun t _ => ⟨?_, ?_⟩⟩
      · rw [hd, zero_mul]; exact hasDerivWithinAt_const _ _ _
      · rw [hd, zero_mul, zero_div]; exact hasDerivWithinAt_const _ _ _
    rw [legendreEllipseContinued, legendreTransport_unique _ _ _ _ _ hγc hreg huv]
    simp
  · set u := legInt_eu ν μ (legInt_zeta z) s with hudef
    set gd := legInt_gd (legInt_zeta z) s with hgd
    have hD := legInt_eu_deriv ν μ hz hs
    have huv : IsLegendreTransport ν μ (legendreEllipsePath z s) (olverQ ν μ z) (deriv (olverQ ν μ) z)
        u (fun t => deriv u t / gd t) := by
      refine ⟨hu0, ?_, fun t _ => (hD t).1.continuousAt.continuousWithinAt,
        fun t _ => (hD t).2.continuousAt.continuousWithinAt,
        fun t _ => ⟨(hD t).1.hasDerivWithinAt, (hD t).2.hasDerivWithinAt⟩⟩
      show deriv u 0 / gd 0 = _
      rw [hd0.deriv, mul_div_assoc, div_self (legInt_gd_ne_zero hz hs 0), mul_one]
    rw [legendreEllipseContinued, legendreTransport_unique _ _ _ _ _ hγc hreg huv, hudef, legInt_eu,
      legFS_olverQ_eq_G ν μ hz, legFS_G]
    have hw1 : legInt_ew (legInt_zeta z) s 1 ^ 2 = legInt_zeta z ^ 2 := by
      rw [legInt_ew, mul_pow, ← exp_nat_mul]
      have : exp (((2:ℕ):ℂ) * (-(s:ℂ)*π*I*((1:ℝ):ℂ))) = 1 := by
        rw [show ((2:ℕ):ℂ) * (-(s:ℂ)*π*I*((1:ℝ):ℂ)) = ((-s:ℤ):ℂ) * (2*π*I) by push_cast; ring]
        exact exp_int_mul_two_pi_mul_I _
      rw [this, mul_one]
    have hexp : exp (-(ν+1)*((s:ℂ)*π*I*((1:ℝ):ℂ))) = (-1:ℂ)^s * exp (-s*ν*π*I) := by
      rw [show -(ν+1)*((s:ℂ)*π*I*((1:ℝ):ℂ)) = (s:ℂ) * (-(π*I)) + -s*ν*π*I by push_cast; ring,
        exp_add, exp_int_mul, exp_neg, exp_pi_mul_I]
      norm_num
    rw [hw1, hexp]; ring

/-- Smooth joining parameter with zero derivatives at both endpoints. -/
def legendreSmoothStep (t : ℝ) : ℝ :=
  3*t^2-2*t^3

/-- A joined path from z to 3/2, s circuits about one of radius 1/2, and back; minus one is not enclosed. -/
def legendreOneLoop (z : ℂ) (s : ℤ) (t : ℝ) : ℂ :=
  if t ≤ 1/3 then z+legendreSmoothStep (3*t)*(3/2-z) else if t ≤ 2/3 then 1+1/2*exp (2*π*I*s*legendreSmoothStep (3*t-1)) else 3/2+legendreSmoothStep (3*t-2)*(z-3/2)

/-- legendreOneContinued. -/
def legendreOneContinued (F : ℂ → ℂ) (ν μ z : ℂ) (s : ℤ) : ℂ :=
  legendreTransport ν μ (legendreOneLoop z s) (F z) (deriv F z)

/-! ### Helpers for DLMF 14.24.3: transport of `P^{-μ}_ν` around `1` (prefix `legTr_`) -/

/-- A pair `(u, v)` is a Legendre transport along `γ` if near each `t₀` it is `(f ∘ γ, f' ∘ γ)`
for a local solution `f` of the Legendre equation at `γ(t₀)`. -/
theorem legTr_isTransport_of_local (ν μ : ℂ) {γ : ℝ → ℂ} (hγ : Differentiable ℝ γ) {u v : ℝ → ℂ}
    (hloc : ∀ t₀ ∈ Icc (0:ℝ) 1, ∃ f f1 : ℂ → ℂ, ∃ f2 : ℂ, HasDerivAt f (f1 (γ t₀)) (γ t₀) ∧
      HasDerivAt f1 f2 (γ t₀) ∧ 1 - γ t₀ ^ 2 ≠ 0 ∧
      (1 - γ t₀ ^ 2) * f2 - 2 * γ t₀ * f1 (γ t₀) + (ν*(ν+1) - μ^2/(1 - γ t₀ ^ 2)) * f (γ t₀) = 0 ∧
      ∀ᶠ t in 𝓝[Icc 0 1] t₀, u t = f (γ t) ∧ v t = f1 (γ t)) :
    IsLegendreTransport ν μ γ (u 0) (v 0) u v := by
  have hd : ∀ t₀ ∈ Icc (0:ℝ) 1, HasDerivWithinAt u (deriv γ t₀ * v t₀) (Icc 0 1) t₀ ∧
      HasDerivWithinAt v (deriv γ t₀ * (2 * γ t₀ * v t₀ - (ν*(ν+1) - μ^2/(1 - γ t₀ ^ 2)) * u t₀) /
        (1 - γ t₀ ^ 2)) (Icc 0 1) t₀ := by
    intro t₀ ht₀
    obtain ⟨f, f1, f2, hf, hf1, hne, hode, hev⟩ := hloc t₀ ht₀
    have hg := (hγ t₀).hasDerivAt
    have hu0 : u t₀ = f (γ t₀) := (hev.self_of_nhdsWithin ht₀).1
    have hv0 : v t₀ = f1 (γ t₀) := (hev.self_of_nhdsWithin ht₀).2
    have hA := (hf.comp t₀ hg).hasDerivWithinAt (s := Icc 0 1)
    have hB := (hf1.comp t₀ hg).hasDerivWithinAt (s := Icc 0 1)
    refine ⟨(hA.congr_of_eventuallyEq (hev.mono fun t h => h.1) hu0).congr_deriv ?_,
      (hB.congr_of_eventuallyEq (hev.mono fun t h => h.2) hv0).congr_deriv ?_⟩
    · rw [hv0]; ring
    · rw [hv0, hu0, eq_div_iff hne]
      linear_combination (deriv γ t₀) * hode
  refine ⟨rfl, rfl, fun t ht => (hd t ht).1.continuousWithinAt,
    fun t ht => (hd t ht).2.continuousWithinAt, hd⟩

/-- A function continuous within `s` at `t₀` with locally constant exponential is locally
constant. -/
theorem legTr_eventually_eq_of_exp {d : ℝ → ℂ} {s : Set ℝ} {t₀ : ℝ}
    (hd : ContinuousWithinAt d s t₀) (he : ∀ᶠ t in 𝓝[s] t₀, exp (d t) = exp (d t₀)) :
    ∀ᶠ t in 𝓝[s] t₀, d t = d t₀ := by
  have hn : ∀ᶠ t in 𝓝[s] t₀, ‖d t - d t₀‖ < 2*π := by
    have := (hd.tendsto.sub_const (d t₀)).norm
    rw [sub_self, norm_zero] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hn, he] with t h1 h2
  have h3 : exp (d t - d t₀) = 1 := by rw [exp_sub, h2, div_self (exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h3
  rw [hn] at h1
  have : ‖(n:ℂ) * (2*π*I)‖ = |(n:ℝ)| * (2*π) := by
    rw [norm_mul, norm_intCast]; simp [abs_of_pos Real.pi_pos]
  rw [this] at h1
  have hn0 : n = 0 := by
    have : |(n:ℝ)| < 1 := by nlinarith [Real.pi_pos]
    have : |n| < 1 := by exact_mod_cast this
    have := abs_lt.mp this
    omega
  rw [hn0] at hn; simp at hn; linear_combination hn

/-- The regular factor `(w+1)^{-μ/2} 𝐅(ν+1, -ν; 1+μ; (1-w)/2)` of `P^{-μ}_ν`. -/
noncomputable def legTr_K (ν μ w : ℂ) : ℂ :=
  exp (-μ/2*log (w+1)) * regularizedGaussHG (ν+1) (-ν) (1+μ) ((1-w)/2)

/-- `P^{-μ}_ν(w) = e^{μ log(w-1)/2} K(w)`. -/
theorem legTr_associatedP_eq (ν μ w : ℂ) :
    associatedP ν (-μ) w = exp (μ/2*log (w-1)) * legTr_K ν μ w := by
  rw [associatedP, legTr_K, show (1:ℂ) - -μ = 1+μ by ring, ← mul_assoc, ← exp_add]
  congr 2; ring

/-- `𝖯^{-μ}_ν(w) = e^{μ log(1-w)/2} K(w)` (continued into the disk). -/
theorem legTr_ferrersPCont_eq (ν μ w : ℂ) :
    ferrersPCont ν (-μ) w = exp (μ/2*log (1-w)) * legTr_K ν μ w := by
  rw [ferrersPCont, legTr_K, show (1:ℂ) - -μ = 1+μ by ring, ← mul_assoc, ← exp_add, add_comm 1 w]
  congr 2; ring

/-- `K` is analytic where `w + 1 ∉ (-∞, 0]` and `(1-w)/2 ∉ [1, ∞)`. -/
theorem legTr_K_analyticAt (ν μ : ℂ) {w : ℂ} (hp : w+1 ∈ slitPlane) (hc : (1-w)/2 ∈ cutPlane) :
    AnalyticAt ℂ (legTr_K ν μ) w := by
  have hG : AnalyticAt ℂ (fun w : ℂ => regularizedGaussHG (ν+1) (-ν) (1+μ) ((1-w)/2)) w :=
    (analyticAt_regularizedGaussHG _ _ _ hc).comp_of_eq (by fun_prop) rfl
  have hE : AnalyticAt ℂ (fun w : ℂ => exp (-μ/2*log (w+1))) w := by
    fun_prop (disch := assumption)
  exact hE.mul hG

/-- Derivative of `e^{μL/2} K` for a branch `L` of `log(w-1)` (up to constants). -/
theorem legTr_hasDerivAt_branch (ν μ : ℂ) {L : ℂ → ℂ} {w : ℂ} (hL : HasDerivAt L (1/(w-1)) w)
    (hK : DifferentiableAt ℂ (legTr_K ν μ) w) :
    HasDerivAt (fun w => exp (μ/2*L w) * legTr_K ν μ w)
      (exp (μ/2*L w) * (μ/2*legTr_K ν μ w/(w-1) + deriv (legTr_K ν μ) w)) w := by
  have h := ((hL.const_mul (μ/2)).cexp).mul hK.hasDerivAt
  convert h using 1; ring

/-- `(log(w-1))' = 1/(w-1)`. -/
theorem legTr_hasDerivAt_log_sub_one {w : ℂ} (hw : w-1 ∈ slitPlane) :
    HasDerivAt (fun w : ℂ => log (w-1)) (1/(w-1)) w := by
  simpa using ((hasDerivAt_id w).sub_const 1).clog hw

/-- `(log(1-w))' = 1/(w-1)`. -/
theorem legTr_hasDerivAt_log_one_sub {w : ℂ} (hw : 1-w ∈ slitPlane) :
    HasDerivAt (fun w : ℂ => log (1-w)) (1/(w-1)) w := by
  have h := ((hasDerivAt_id' w).const_sub 1).clog hw
  have hne : 1 - w ≠ 0 := slitPlane_ne_zero hw
  have hne' : w - 1 ≠ 0 := fun h => hne (by linear_combination -h)
  convert h using 1
  field_simp
  ring

/-- The Legendre equation for `𝖯^μ_ν` continued into the unit disk. -/
theorem legTr_ferrersPCont_ode (ν μ : ℂ) {w : ℂ} (hw : w ∈ Metric.ball (0:ℂ) 1) :
    (1-w^2)*iteratedDeriv 2 (ferrersPCont ν μ) w-2*w*deriv (ferrersPCont ν μ) w+
      (ν*(ν+1)-μ^2/(1-w^2))*ferrersPCont ν μ w=0 := by
  set F := ferrersPCont ν μ
  set B := Metric.ball (0:ℂ) 1
  have hF := ferrersPCont_analytic ν μ
  have hne : ∀ w ∈ B, 1 - w^2 ≠ 0 := fun w hw => slitPlane_ne_zero (legendre_disk_facts hw).2.2.2.1
  have hE : AnalyticOnNhd ℂ (fun w => (1-w^2)*iteratedDeriv 2 F w-2*w*deriv F w+
      (ν*(ν+1)-μ^2/(1-w^2))*F w) B := by
    intro w hw
    have h2 : AnalyticAt ℂ (iteratedDeriv 2 F) w := by
      rw [iteratedDeriv_eq_iterate]; exact hF.iterated_deriv 2 w hw
    have h1 := hF.deriv w hw
    have h0 := hF w hw
    have hd : AnalyticAt ℂ (fun w : ℂ => μ^2/(1-w^2)) w :=
      analyticAt_const.div (by fun_prop) (hne w hw)
    have h1' : AnalyticAt ℂ (deriv F) w := h1
    have h0' : AnalyticAt ℂ F w := h0
    exact (((analyticAt_const.sub (analyticAt_id.pow 2)).fun_mul h2).fun_sub
      ((analyticAt_const.fun_mul analyticAt_id).fun_mul h1')).fun_add ((analyticAt_const.fun_sub hd).fun_mul h0')
  have hI : (I/2 : ℂ) ∈ B := by
    simp only [B, Metric.mem_ball, dist_zero_right, norm_div, norm_I]; norm_num
  have hev : (fun w => (1-w^2)*iteratedDeriv 2 F w-2*w*deriv F w+
      (ν*(ν+1)-μ^2/(1-w^2))*F w) =ᶠ[𝓝 (I/2)] 0 := by
    have hV : IsOpen (B ∩ {w : ℂ | 0 < w.im}) :=
      Metric.isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
    have hI' : (I/2:ℂ) ∈ B ∩ {w : ℂ | 0 < w.im} := ⟨hI, by simp⟩
    filter_upwards [hV.mem_nhds hI'] with w ⟨hwB, hwi⟩
    have hloc : F =ᶠ[𝓝 w] fun w => exp (μ*π*I/2) * associatedP ν μ w := by
      filter_upwards [hV.mem_nhds ⟨hwB, hwi⟩] with y ⟨_, hyi⟩
      have := associatedP_eq_ferrersPCont (s := 1) (Or.inl rfl) ν μ (z := y) (by simpa using hyi)
      have e : exp (μ*π*I/2) * exp (-((1:ℝ):ℂ)*μ*π*I/2) = 1 := by
        rw [← exp_add]; push_cast; ring_nf; exact exp_zero
      rw [this, ← mul_assoc, e, one_mul]
    have hw1 : w - 1 ∈ slitPlane := Or.inr (by simp; exact hwi.ne')
    have hd1 := hloc.deriv_eq
    have hd2 := (hloc.iteratedDeriv 2).self_of_nhds
    rw [iteratedDeriv_const_mul_field] at hd2
    rw [show deriv (fun w => exp (μ*π*I/2) * associatedP ν μ w) w =
      exp (μ*π*I/2) * deriv (associatedP ν μ) w from deriv_const_mul _
        (associatedP_analytic ν μ w hw1).differentiableAt] at hd1
    have hode := associatedP_ode ν μ hw1
    simp only [Pi.zero_apply]
    rw [hd2, hd1, hloc.self_of_nhds]
    linear_combination exp (μ*π*I/2) * hode
  exact hE.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hI hev hw

/-- The transported value `e^{μℓ(t)/2} K(γ(t))`, with `ℓ` a continuous logarithm of `γ - 1`. -/
noncomputable def legTr_u (ν μ : ℂ) (γ ℓ : ℝ → ℂ) (t : ℝ) : ℂ :=
  exp (μ/2*ℓ t) * legTr_K ν μ (γ t)

/-- The transported derivative `e^{μℓ(t)/2} (μ K/(2(γ-1)) + K')(γ(t))`. -/
noncomputable def legTr_v (ν μ : ℂ) (γ ℓ : ℝ → ℂ) (t : ℝ) : ℂ :=
  exp (μ/2*ℓ t) * (μ/2*legTr_K ν μ (γ t)/(γ t - 1) + deriv (legTr_K ν μ) (γ t))

/-- Local data for `legTr_isTransport_of_local` from a local branch `L` of `log(w-1)` (up to a
constant) and a solution `F = e^{μL/2} K` of the Legendre equation near `γ(t₀)`. -/
theorem legTr_local_branch (ν μ : ℂ) {γ : ℝ → ℂ} (hγ : Differentiable ℝ γ) {ℓ : ℝ → ℂ}
    (hℓ : ContinuousOn ℓ (Icc 0 1)) (hexp : ∀ t ∈ Icc (0:ℝ) 1, exp (ℓ t) = γ t - 1)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0:ℝ) 1) {L F : ℂ → ℂ} {U : Set ℂ} {κ : ℂ} (hU : IsOpen U)
    (hw₀ : γ t₀ ∈ U) (hLd : ∀ w ∈ U, HasDerivAt L (1/(w-1)) w)
    (hLexp : ∀ w ∈ U, exp (L w) = κ * (w - 1)) (hκ : κ ≠ 0)
    (hFeq : ∀ w, F w = exp (μ/2*L w) * legTr_K ν μ w)
    (hKd : ∀ w ∈ U, DifferentiableAt ℂ (legTr_K ν μ) w) (hFa : AnalyticOnNhd ℂ F U)
    (hode : ∀ w ∈ U, (1-w^2)*iteratedDeriv 2 F w-2*w*deriv F w+(ν*(ν+1)-μ^2/(1-w^2))*F w=0)
    (hne : ∀ w ∈ U, 1 - w^2 ≠ 0) :
    ∃ f f1 : ℂ → ℂ, ∃ f2 : ℂ, HasDerivAt f (f1 (γ t₀)) (γ t₀) ∧
      HasDerivAt f1 f2 (γ t₀) ∧ 1 - γ t₀ ^ 2 ≠ 0 ∧
      (1 - γ t₀ ^ 2) * f2 - 2 * γ t₀ * f1 (γ t₀) + (ν*(ν+1) - μ^2/(1 - γ t₀ ^ 2)) * f (γ t₀) = 0 ∧
      ∀ᶠ t in 𝓝[Icc 0 1] t₀, legTr_u ν μ γ ℓ t = f (γ t) ∧ legTr_v ν μ γ ℓ t = f1 (γ t) := by
  set w₀ := γ t₀
  have hne1 : ∀ w ∈ U, w - 1 ≠ 0 := fun w hw h => hne w hw (by
    rw [show w = 1 by linear_combination h]; ring)
  have hγU : ∀ᶠ t in 𝓝 t₀, γ t ∈ U := (hγ t₀).continuousAt.preimage_mem_nhds (hU.mem_nhds hw₀)
  set d : ℝ → ℂ := fun t => ℓ t - L (γ t)
  have hdc : ContinuousWithinAt d (Icc 0 1) t₀ :=
    (hℓ t₀ ht₀).sub (((hLd w₀ hw₀).differentiableAt.continuousAt.comp
      (hγ t₀).continuousAt).continuousWithinAt)
  have hdexp : ∀ t ∈ Icc (0:ℝ) 1, γ t ∈ U → exp (d t) = κ⁻¹ := by
    intro t ht hU'
    simp only [d]
    rw [exp_sub, hexp t ht, hLexp _ hU']
    field_simp [hne1 _ hU']
  have hd := legTr_eventually_eq_of_exp hdc (by
    filter_upwards [nhdsWithin_le_nhds hγU, self_mem_nhdsWithin] with t h1 h2
    rw [hdexp t h2 h1, hdexp t₀ ht₀ hw₀])
  set c := exp (μ/2*d t₀)
  have hF' : ∀ w ∈ U, deriv F w = exp (μ/2*L w) * (μ/2*legTr_K ν μ w/(w-1) + deriv (legTr_K ν μ) w) := by
    intro w hw
    have he : F = fun w => exp (μ/2*L w) * legTr_K ν μ w := funext hFeq
    rw [he]; exact (legTr_hasDerivAt_branch ν μ (hLd w hw) (hKd w hw)).deriv
  refine ⟨fun w => c * F w, fun w => c * deriv F w, c * iteratedDeriv 2 F w₀,
    ((hFa w₀ hw₀).differentiableAt.hasDerivAt).const_mul c, ?_, hne w₀ hw₀, ?_, ?_⟩
  · have h := ((hFa.deriv w₀ hw₀).differentiableAt.hasDerivAt).const_mul c
    rwa [iteratedDeriv_succ, iteratedDeriv_one]
  · linear_combination c * hode w₀ hw₀
  · filter_upwards [hd, nhdsWithin_le_nhds hγU] with t hdt hUt
    have hl : ℓ t = L (γ t) + d t₀ := by rw [← hdt]; simp only [d]; ring
    have hE : exp (μ/2*ℓ t) = c * exp (μ/2*L (γ t)) := by
      rw [hl, ← exp_add]; congr 1; ring
    refine ⟨?_, ?_⟩
    · simp only [legTr_u]; rw [hE, hFeq]; ring
    · simp only [legTr_v]; rw [hE, hF' _ hUt]; ring

/-- Transport of `P^{-μ}_ν` along a path that stays in `ℂ ∖ (-∞, 1]` or in the unit disk:
`u = e^{μℓ/2} K(γ)`, `ℓ` a continuous logarithm of `γ - 1`. -/
theorem legTr_isTransport_branch (ν μ : ℂ) {γ : ℝ → ℂ} (hγ : Differentiable ℝ γ) {ℓ : ℝ → ℂ}
    (hℓ : ContinuousOn ℓ (Icc 0 1)) (hexp : ∀ t ∈ Icc (0:ℝ) 1, exp (ℓ t) = γ t - 1)
    (hdom : ∀ t ∈ Icc (0:ℝ) 1, γ t - 1 ∈ slitPlane ∨ γ t ∈ Metric.ball (0:ℂ) 1) :
    IsLegendreTransport ν μ γ (legTr_u ν μ γ ℓ 0) (legTr_v ν μ γ ℓ 0) (legTr_u ν μ γ ℓ)
      (legTr_v ν μ γ ℓ) := by
  refine legTr_isTransport_of_local ν μ hγ fun t₀ ht₀ => ?_
  rcases hdom t₀ ht₀ with hs | hb
  · have hp : ∀ w : ℂ, w - 1 ∈ slitPlane → w + 1 ∈ slitPlane := fun w hw => by
      simpa [add_comm] using one_add_mem_slitPlane_of_sub_one hw
    refine legTr_local_branch ν μ hγ hℓ hexp ht₀ (L := fun w => log (w-1)) (F := associatedP ν (-μ))
      (U := {w | w-1 ∈ slitPlane}) (κ := 1) isOpen_sub_one_mem_slitPlane hs
      (fun w hw => legTr_hasDerivAt_log_sub_one hw)
      (fun w hw => by simp [exp_log (slitPlane_ne_zero hw)]) one_ne_zero (legTr_associatedP_eq ν μ)
      (fun w hw => (legTr_K_analyticAt ν μ (hp w hw)
        (mem_cutPlane_of_one_add (by simpa [add_comm] using hp w hw))).differentiableAt)
      (associatedP_analytic ν (-μ)) (fun w hw => by
        have := associatedP_ode ν (-μ) hw; rwa [neg_sq] at this) (fun w hw => ?_)
    have h1 := slitPlane_ne_zero (show w - 1 ∈ slitPlane from hw)
    have h2 := slitPlane_ne_zero (hp w hw)
    intro h; apply mul_ne_zero h1 h2; linear_combination -h
  · refine legTr_local_branch ν μ hγ hℓ hexp ht₀ (L := fun w => log (1-w)) (F := ferrersPCont ν (-μ))
      (U := Metric.ball (0:ℂ) 1) (κ := -1) Metric.isOpen_ball hb
      (fun w hw => legTr_hasDerivAt_log_one_sub (legendre_disk_facts hw).2.1)
      (fun w hw => by rw [exp_log (slitPlane_ne_zero (legendre_disk_facts hw).2.1)]; ring)
      (by norm_num) (legTr_ferrersPCont_eq ν μ)
      (fun w hw => (legTr_K_analyticAt ν μ (by simpa [add_comm] using (legendre_disk_facts hw).1)
        (legendre_disk_facts hw).2.2.1).differentiableAt)
      (ferrersPCont_analytic ν (-μ)) (fun w hw => by
        have := legTr_ferrersPCont_ode ν (-μ) hw; rwa [neg_sq] at this)
      (fun w hw => slitPlane_ne_zero (legendre_disk_facts hw).2.2.2.1)

/-- Gluing two everywhere-differentiable functions that agree to first order at `a`. -/
theorem legTr_hasDerivAt_piecewise {f g f' g' : ℝ → ℂ} {a : ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hg : ∀ t, HasDerivAt g (g' t) t) (ha : f a = g a) (ha' : f' a = g' a) (t : ℝ) :
    HasDerivAt (fun t => if t ≤ a then f t else g t) (if t ≤ a then f' t else g' t) t := by
  rcases lt_trichotomy t a with h | h | h
  · simp only [h.le, ↓reduceIte]
    refine (hf t).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with x hx
    simp [le_of_lt (show x < a from hx)]
  · rw [h]
    simp only [le_refl, ↓reduceIte]
    have h1 : HasDerivWithinAt (fun x => if x ≤ a then f x else g x) (f' a) (Iic a) a :=
      (hf a).hasDerivWithinAt.congr (fun x hx => by simp [show x ≤ a from hx]) (by simp)
    have h2 : HasDerivWithinAt (fun x => if x ≤ a then f x else g x) (f' a) (Ici a) a := by
      rw [ha']
      refine (hg a).hasDerivWithinAt.congr (fun x hx => ?_) (by simp [ha])
      rcases eq_or_lt_of_le (show a ≤ x from hx) with h | h
      · rw [← h]; simp [ha]
      · simp [not_le.mpr h]
    have := h1.union h2
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · simp only [not_le.mpr h, ↓reduceIte]
    refine (hg t).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds h] with x hx
    simp [not_le.mpr (show a < x from hx)]

/-- Gluing two functions continuous on adjacent closed intervals. -/
theorem legTr_continuousOn_piecewise {f g : ℝ → ℂ} {p a q : ℝ} (hf : ContinuousOn f (Icc p a))
    (hg : ContinuousOn g (Icc a q)) (ha : f a = g a) :
    ContinuousOn (fun t => if t ≤ a then f t else g t) (Icc p q) := by
  have h1 : ContinuousOn (fun t => if t ≤ a then f t else g t) (Icc p a) :=
    hf.congr fun x hx => by simp [hx.2]
  have h2 : ContinuousOn (fun t => if t ≤ a then f t else g t) (Icc a q) := hg.congr fun x hx => by
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]; simp [ha]
    · simp [not_le.mpr h]
  refine (h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc).mono fun x hx => ?_
  rcases le_total x a with h | h
  · exact Or.inl ⟨hx.1, h⟩
  · exact Or.inr ⟨h, hx.2⟩

/-- `ℂ ∖ (-∞, 0]` is star-shaped about `1/2`. -/
theorem legTr_star_mem {w : ℂ} (hw : w ∈ slitPlane) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (1 - r) * w + r * (1/2) ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hw ⊢
  rcases eq_or_lt_of_le hr1 with h | h
  · left; rw [h]; norm_num
  · by_cases hi : w.im = 0
    · left
      have : 0 < w.re := hw.resolve_right (not_not.mpr hi)
      simp; nlinarith
    · right; simp [hi]; exact fun h' => by linarith

/-- The smooth step maps `[0, 1]` into `[0, 1]`. -/
theorem legTr_S_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ legendreSmoothStep x ∧ legendreSmoothStep x ≤ 1 := by
  unfold legendreSmoothStep
  constructor
  · nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) (sub_nonneg.mpr h1)]
  · nlinarith [mul_nonneg (sq_nonneg (1-x)) (by linarith : (0:ℝ) ≤ 1+2*x)]

/-- Derivative of `t ↦ S(3t-c)`. -/
theorem legTr_hasDerivAt_S (c : ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => ((legendreSmoothStep (3*t-c) : ℝ) : ℂ))
      (((6*(3*t-c)-6*(3*t-c)^2)*3 : ℝ) : ℂ) t := by
  have h : HasDerivAt (fun t : ℝ => legendreSmoothStep (3*t-c)) ((6*(3*t-c)-6*(3*t-c)^2)*3) t := by
    unfold legendreSmoothStep
    have h1 : HasDerivAt (fun t : ℝ => 3*t-c) 3 t := by
      simpa using ((hasDerivAt_id t).const_mul 3).sub_const c
    have := ((h1.pow 2).const_mul 3).sub ((h1.pow 3).const_mul 2)
    convert this using 1; push_cast; ring
  exact h.ofReal_comp

/-- The derivative `(6x-6x²)·3` of `t ↦ S(3t-c)`. -/
noncomputable def legTr_Sd (c t : ℝ) : ℂ := (((6*(3*t-c)-6*(3*t-c)^2)*3 : ℝ) : ℂ)

/-- The derivative of `legendreOneLoop`. -/
noncomputable def legTr_loopDeriv (z : ℂ) (s : ℤ) (t : ℝ) : ℂ :=
  if t ≤ 1/3 then legTr_Sd 0 t*(3/2-z) else if t ≤ 2/3 then
    1/2*exp (2*π*I*s*legendreSmoothStep (3*t-1))*(2*π*I*s*legTr_Sd 1 t) else legTr_Sd 2 t*(z-3/2)

/-- `e^{2πis S(1)} = 1`. -/
theorem legTr_exp_two_pi_s (s : ℤ) : exp (2*π*I*s*((legendreSmoothStep (3*(2/3:ℝ)-1) : ℝ) : ℂ)) = 1 := by
  rw [show legendreSmoothStep (3*(2/3:ℝ)-1) = 1 by unfold legendreSmoothStep; norm_num]
  rw [show 2*π*I*(s:ℂ)*((1:ℝ):ℂ) = (s:ℂ)*(2*π*I) by push_cast; ring]
  exact exp_int_mul_two_pi_mul_I s

/-- `legendreOneLoop` is differentiable, with derivative `legTr_loopDeriv`. -/
theorem legTr_hasDerivAt_loop (z : ℂ) (s : ℤ) (t : ℝ) :
    HasDerivAt (legendreOneLoop z s) (legTr_loopDeriv z s t) t := by
  have hA : ∀ t, HasDerivAt (fun t : ℝ => z+legendreSmoothStep (3*t)*(3/2-z)) (legTr_Sd 0 t*(3/2-z)) t := by
    intro t
    have := ((legTr_hasDerivAt_S 0 t).mul_const (3/2-z)).const_add z
    simpa [legTr_Sd] using this
  have hB : ∀ t, HasDerivAt (fun t : ℝ => 1+1/2*exp (2*π*I*s*legendreSmoothStep (3*t-1)))
      (1/2*exp (2*π*I*s*legendreSmoothStep (3*t-1))*(2*π*I*s*legTr_Sd 1 t)) t := by
    intro t
    have := ((((legTr_hasDerivAt_S 1 t).const_mul (2*π*I*s)).cexp).const_mul (1/2)).const_add 1
    convert this using 1
    simp only [legTr_Sd]; ring
  have hC : ∀ t, HasDerivAt (fun t : ℝ => 3/2+legendreSmoothStep (3*t-2)*(z-3/2)) (legTr_Sd 2 t*(z-3/2)) t := by
    intro t
    have := ((legTr_hasDerivAt_S 2 t).mul_const (z-3/2)).const_add (3/2)
    simpa [legTr_Sd] using this
  have hBC := legTr_hasDerivAt_piecewise (a := 2/3) hB hC (by
      rw [legTr_exp_two_pi_s]; unfold legendreSmoothStep; norm_num)
    (by unfold legTr_Sd; norm_num)
  have h := legTr_hasDerivAt_piecewise (a := 1/3) hA hBC (by
      unfold legendreSmoothStep; norm_num) (by unfold legTr_Sd; norm_num) t
  exact h

/-- The derivative of `legendreOneLoop` is continuous. -/
theorem legTr_continuous_loopDeriv (z : ℂ) (s : ℤ) : Continuous (legTr_loopDeriv z s) := by
  have hS : ∀ c, Continuous (legTr_Sd c) := fun c => by unfold legTr_Sd; fun_prop
  have hS' : Continuous fun t : ℝ => ((legendreSmoothStep (3*t-1) : ℝ) : ℂ) := by
    unfold legendreSmoothStep; fun_prop
  unfold legTr_loopDeriv
  refine Continuous.if_le ((hS 0).mul continuous_const)
    (Continuous.if_le (by fun_prop) ((hS 2).mul continuous_const) continuous_id continuous_const ?_)
    continuous_id continuous_const ?_
  · intro x hx; rw [hx]; unfold legTr_Sd; norm_num
  · intro x hx; rw [hx]; unfold legTr_Sd; norm_num

/-- `legendreOneLoop` is `C¹`. -/
theorem legTr_contDiff_loop (z : ℂ) (s : ℤ) : ContDiff ℝ 1 (legendreOneLoop z s) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (legTr_hasDerivAt_loop z s t).differentiableAt, ?_⟩
  have : deriv (legendreOneLoop z s) = legTr_loopDeriv z s :=
    funext fun t => (legTr_hasDerivAt_loop z s t).deriv
  rw [this]; exact legTr_continuous_loopDeriv z s

/-- A continuous logarithm of `γ - 1` along `legendreOneLoop`. -/
noncomputable def legTr_ell (z : ℂ) (s : ℤ) (t : ℝ) : ℂ :=
  if t ≤ 1/3 then log (z+legendreSmoothStep (3*t)*(3/2-z)-1) else if t ≤ 2/3 then
    log (1/2)+2*π*I*s*legendreSmoothStep (3*t-1) else log (3/2+legendreSmoothStep (3*t-2)*(z-3/2)-1)+2*π*I*s

/-- The first leg of `legendreOneLoop` stays in `ℂ ∖ (-∞, 1]`. -/
theorem legTr_mem_first {z : ℂ} (hz : z-1 ∈ slitPlane) {t : ℝ} (ht : t ∈ Icc (0:ℝ) (1/3)) :
    z+legendreSmoothStep (3*t)*(3/2-z)-1 ∈ slitPlane := by
  obtain ⟨h0, h1⟩ := legTr_S_mem (x := 3*t) (by linarith [ht.1]) (by linarith [ht.2])
  have := legTr_star_mem hz h0 h1
  convert this using 1; ring

/-- The last leg of `legendreOneLoop` stays in `ℂ ∖ (-∞, 1]`. -/
theorem legTr_mem_last {z : ℂ} (hz : z-1 ∈ slitPlane) {t : ℝ} (ht : t ∈ Icc (2/3:ℝ) 1) :
    3/2+legendreSmoothStep (3*t-2)*(z-3/2)-1 ∈ slitPlane := by
  obtain ⟨h0, h1⟩ := legTr_S_mem (x := 3*t-2) (by linarith [ht.1]) (by linarith [ht.2])
  have := legTr_star_mem hz (r := 1 - legendreSmoothStep (3*t-2)) (by linarith) (by linarith)
  convert this using 1; push_cast; ring

/-- `e^{ℓ(t)} = γ(t) - 1` along `legendreOneLoop`. -/
theorem legTr_exp_ell {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    exp (legTr_ell z s t) = legendreOneLoop z s t - 1 := by
  unfold legTr_ell legendreOneLoop
  split_ifs with h1 h2
  · exact exp_log (slitPlane_ne_zero (legTr_mem_first hz ⟨ht.1, h1⟩))
  · rw [exp_add, exp_log (by norm_num)]; ring
  · rw [exp_add, exp_log (slitPlane_ne_zero (legTr_mem_last hz ⟨by linarith, ht.2⟩)),
      show 2*π*I*(s:ℂ) = (s:ℂ)*(2*π*I) by ring, exp_int_mul_two_pi_mul_I, mul_one]

/-- `legTr_ell` is continuous on `[0, 1]`. -/
theorem legTr_continuousOn_ell {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    ContinuousOn (legTr_ell z s) (Icc 0 1) := by
  have hS : ∀ c : ℝ, Continuous fun t : ℝ => ((legendreSmoothStep (3*t-c) : ℝ) : ℂ) := fun c => by
    unfold legendreSmoothStep; fun_prop
  have hS0 : Continuous fun t : ℝ => ((legendreSmoothStep (3*t) : ℝ) : ℂ) := by
    unfold legendreSmoothStep; fun_prop
  unfold legTr_ell
  refine legTr_continuousOn_piecewise (p := 0) (a := 1/3) (q := 1) ?_ ?_ ?_
  · intro t ht
    have hc : Continuous (fun t : ℝ => z+(legendreSmoothStep (3*t):ℂ)*(3/2-z)-1) :=
      (continuous_const.add (hS0.mul continuous_const)).sub continuous_const
    exact (hc.continuousAt.clog (legTr_mem_first hz ht)).continuousWithinAt
  · refine legTr_continuousOn_piecewise (p := 1/3) (a := 2/3) (q := 1)
      (continuous_const.add (continuous_const.mul (hS 1))).continuousOn ?_ ?_
    · intro t ht
      have hc : Continuous (fun t : ℝ => 3/2+(legendreSmoothStep (3*t-2):ℂ)*(z-3/2)-1) :=
        (continuous_const.add ((hS 2).mul continuous_const)).sub continuous_const
      exact ((hc.continuousAt.clog (legTr_mem_last hz ht)).add
        continuousAt_const).continuousWithinAt
    · unfold legendreSmoothStep; norm_num
  · simp only [show (1/3:ℝ) ≤ 2/3 by norm_num, ↓reduceIte]
    unfold legendreSmoothStep; norm_num

/-- Each point of `legendreOneLoop` lies in `ℂ ∖ (-∞, 1]` or in the unit disk. -/
theorem legTr_loop_dom {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    legendreOneLoop z s t - 1 ∈ slitPlane ∨ legendreOneLoop z s t ∈ Metric.ball (0:ℂ) 1 := by
  unfold legendreOneLoop
  split_ifs with h1 h2
  · exact Or.inl (legTr_mem_first hz ⟨ht.1, h1⟩)
  · set w : ℂ := 1/2*exp (2*π*I*s*legendreSmoothStep (3*t-1))
    have hw : 1 + w - 1 = w := by ring
    rw [hw]
    by_cases hm : w ∈ slitPlane
    · exact Or.inl hm
    · right
      have hn : ‖w‖ = 1/2 := by
        simp only [w, norm_mul, norm_exp]
        simp
      rw [mem_slitPlane_iff] at hm
      push Not at hm
      have hw' : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [hm.2])
      have habs : |w.re| = 1/2 := by rw [← hn, hw', norm_real, Real.norm_eq_abs]; simp
      have hre : w.re = -1/2 := by
        rcases abs_eq (by norm_num : (0:ℝ) ≤ 1/2) |>.mp habs with h | h
        · linarith [hm.1]
        · linarith
      rw [hw', hre]
      simp only [Metric.mem_ball, dist_zero_right]
      rw [show (1:ℂ) + (((-1/2:ℝ)):ℂ) = ((1/2:ℝ):ℂ) by push_cast; ring, norm_real]
      norm_num
  · exact Or.inl (legTr_mem_last hz ⟨by linarith, ht.2⟩)

/-- associatedP one continuation. The transport is `e^{μℓ(t)/2} K(γ(t))`, `ℓ` a continuous
logarithm of `γ - 1` along the loop (`legTr_isTransport_branch`), so `ℓ(1) = log(z-1) + 2πis`. -/
@[dlmf 14.24.E3]
theorem associatedP_one_continuation (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    legendreOneContinued (associatedP ν (-μ)) ν μ z s=exp (s*μ*π*I)*associatedP ν (-μ) z := by
  have hγd : Differentiable ℝ (legendreOneLoop z s) := fun t => (legTr_hasDerivAt_loop z s t).differentiableAt
  have huv := legTr_isTransport_branch ν μ hγd (legTr_continuousOn_ell hz s)
    (fun t ht => legTr_exp_ell hz s ht) (fun t ht => legTr_loop_dom hz s ht)
  have hreg : ∀ t ∈ Icc (0:ℝ) 1, legendreOneLoop z s t ≠ 1 ∧ legendreOneLoop z s t ≠ -1 := by
    intro t ht
    rcases legTr_loop_dom hz s ht with h | h
    · refine ⟨fun h1 => slitPlane_ne_zero h (by rw [h1]; ring), fun h1 => ?_⟩
      rw [h1] at h; norm_num [mem_slitPlane_iff] at h
    · have hn : ‖legendreOneLoop z s t‖ < 1 := by simpa using h
      refine ⟨fun h1 => by rw [h1] at hn; simp at hn, fun h1 => by rw [h1] at hn; simp at hn⟩
  have key := legendreTransport_unique ν μ _ _ (legendreOneLoop z s) (legTr_contDiff_loop z s) hreg huv
  have hγ0 : legendreOneLoop z s 0 = z := by
    simp only [legendreOneLoop]; unfold legendreSmoothStep; norm_num
  have hγ1 : legendreOneLoop z s 1 = z := by
    simp only [legendreOneLoop]; unfold legendreSmoothStep; norm_num
  have hℓ0 : legTr_ell z s 0 = log (z-1) := by
    simp only [legTr_ell]; unfold legendreSmoothStep; norm_num
  have hℓ1 : legTr_ell z s 1 = log (z-1) + 2*π*I*s := by
    simp only [legTr_ell]; unfold legendreSmoothStep; norm_num
  have hp : z + 1 ∈ slitPlane := by simpa [add_comm] using one_add_mem_slitPlane_of_sub_one hz
  have hKd : DifferentiableAt ℂ (legTr_K ν μ) z := (legTr_K_analyticAt ν μ hp
    (mem_cutPlane_of_one_add (by simpa [add_comm] using hp))).differentiableAt
  have hu0 : legTr_u ν μ (legendreOneLoop z s) (legTr_ell z s) 0 = associatedP ν (-μ) z := by
    rw [legTr_u, hγ0, hℓ0, legTr_associatedP_eq]
  have hv0 : legTr_v ν μ (legendreOneLoop z s) (legTr_ell z s) 0 = deriv (associatedP ν (-μ)) z := by
    have he : associatedP ν (-μ) = fun w => exp (μ/2*log (w-1)) * legTr_K ν μ w :=
      funext (legTr_associatedP_eq ν μ)
    rw [he, (legTr_hasDerivAt_branch ν μ (legTr_hasDerivAt_log_sub_one hz) hKd).deriv, legTr_v,
      hγ0, hℓ0]
  rw [hu0, hv0] at key
  unfold legendreOneContinued
  rw [key, legTr_u, hγ1, hℓ1, legTr_associatedP_eq, ← mul_assoc, ← exp_add]
  congr 2; ring

/-! ### Helpers for DLMF 14.24.1 and 14.24.4: continuity and linearity of the transport (prefix `legTr_`) -/

/-- Gronwall step for `legTr_transport_tendsto`: the second component of the difference system. -/
theorem legTr_diff_bound {g γ q α β α0 β0 ux vx u v : ℂ} {G Γ0 Qi A B U : ℝ}
    (hg : ‖g‖ ≤ G) (hγ : ‖γ‖ ≤ Γ0) (hq : ‖q⁻¹‖ ≤ Qi) (hα : ‖α‖ ≤ A) (hβ : ‖β‖ ≤ B) (hu : ‖u‖ ≤ U)
    (hG : 0 ≤ G) (hQi : 0 ≤ Qi) (hΓ : 0 ≤ Γ0) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ‖g*(2*γ*vx-(α-β/q)*ux)/q - g*(2*γ*v-(α0-β0/q)*u)/q‖ ≤
      G*Qi*(2*Γ0 + A + B*Qi) * max ‖ux-u‖ ‖vx-v‖ + G*Qi*(‖α-α0‖+‖β-β0‖*Qi)*U := by
  have e : g*(2*γ*vx-(α-β/q)*ux)/q - g*(2*γ*v-(α0-β0/q)*u)/q =
      g*q⁻¹*(2*γ*(vx-v) - (α - β*q⁻¹)*(ux-u) - ((α-α0) - (β-β0)*q⁻¹)*u) := by ring
  rw [e, norm_mul, norm_mul]
  set M := max ‖ux-u‖ ‖vx-v‖
  have h1 : ‖ux-u‖ ≤ M := le_max_left _ _
  have h2 : ‖vx-v‖ ≤ M := le_max_right _ _
  have hM : 0 ≤ M := le_trans (norm_nonneg _) h1
  have hin : ‖2*γ*(vx-v) - (α - β*q⁻¹)*(ux-u) - ((α-α0) - (β-β0)*q⁻¹)*u‖ ≤
      (2*Γ0 + A + B*Qi)*M + (‖α-α0‖+‖β-β0‖*Qi)*U := by
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_sub_le _ _) le_rfl).trans ?_
    have t1 : ‖2*γ*(vx-v)‖ ≤ 2*Γ0*M := by
      rw [norm_mul, norm_mul]; simp only [Complex.norm_ofNat]
      exact mul_le_mul (by linarith) h2 (norm_nonneg _) (by linarith)
    have t2 : ‖(α - β*q⁻¹)*(ux-u)‖ ≤ (A + B*Qi)*M := by
      rw [norm_mul]
      refine mul_le_mul ((norm_sub_le _ _).trans ?_) h1 (norm_nonneg _) (by positivity)
      rw [norm_mul]; exact add_le_add hα (mul_le_mul hβ hq (norm_nonneg _) hB)
    have t3 : ‖((α-α0) - (β-β0)*q⁻¹)*u‖ ≤ (‖α-α0‖+‖β-β0‖*Qi)*U := by
      rw [norm_mul]
      refine mul_le_mul ((norm_sub_le _ _).trans ?_) hu (norm_nonneg _) (by positivity)
      rw [norm_mul]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hq (norm_nonneg _))
    nlinarith
  calc ‖g‖ * ‖q⁻¹‖ * ‖2*γ*(vx-v) - (α - β*q⁻¹)*(ux-u) - ((α-α0) - (β-β0)*q⁻¹)*u‖
      ≤ G * Qi * ((2*Γ0 + A + B*Qi)*M + (‖α-α0‖+‖β-β0‖*Qi)*U) := by
        gcongr
    _ = _ := by ring

/-- Continuous dependence of the Legendre transport on the degree, the order and the initial
data (Gronwall). -/
theorem legTr_transport_tendsto {X : Type*} {l : Filter X} {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hreg : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ 1 ∧ γ t ≠ -1) {νf μf af bf : X → ℂ} {ν μ a b : ℂ}
    (hν : Tendsto νf l (𝓝 ν)) (hμ : Tendsto μf l (𝓝 μ)) (ha : Tendsto af l (𝓝 a))
    (hb : Tendsto bf l (𝓝 b)) :
    Tendsto (fun x => legendreTransport (νf x) (μf x) γ (af x) (bf x)) l
      (𝓝 (legendreTransport ν μ γ a b)) := by
  have hne : ∀ t ∈ Icc (0:ℝ) 1, 1 - γ t ^ 2 ≠ 0 := fun t ht h0 => by
    have : (1 - γ t) * (1 + γ t) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h | h
    · exact (hreg t ht).1 (by linear_combination -h)
    · exact (hreg t ht).2 (by linear_combination h)
  have hγc : Continuous γ := hγ.continuous
  have hγ'c : Continuous (deriv γ) := hγ.continuous_deriv le_rfl
  obtain ⟨G, hG⟩ := isCompact_Icc.exists_bound_of_continuousOn (hγ'c.continuousOn (s := Icc (0:ℝ) 1))
  obtain ⟨Γ0, hΓ⟩ := isCompact_Icc.exists_bound_of_continuousOn (hγc.continuousOn (s := Icc (0:ℝ) 1))
  obtain ⟨Qi, hQ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (((continuous_const.sub (hγc.pow 2)).continuousOn (s := Icc (0:ℝ) 1)).inv₀ hne)
  have hQ' : ∀ t ∈ Icc (0:ℝ) 1, ‖(1-(γ t)^2)⁻¹‖ ≤ Qi := fun t ht => hQ t ht
  have hG' : ∀ t ∈ Icc (0:ℝ) 1, ‖deriv γ t‖ ≤ G := fun t ht => hG t ht
  have hΓ' : ∀ t ∈ Icc (0:ℝ) 1, ‖γ t‖ ≤ Γ0 := fun t ht => hΓ t ht
  clear hQ hG hΓ
  obtain ⟨u, v, huv⟩ := legendreTransport_exists ν μ a b γ hγ hreg
  obtain ⟨U, hU⟩ := isCompact_Icc.exists_bound_of_continuousOn huv.2.2.1
  have h0I : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG' 0 h0I)
  have hΓ0 : 0 ≤ Γ0 := (norm_nonneg _).trans (hΓ' 0 h0I)
  have hQ0 : 0 ≤ Qi := (norm_nonneg _).trans (hQ' 0 h0I)
  have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU 0 h0I)
  choose ux vx hx using fun x => legendreTransport_exists (νf x) (μf x) (af x) (bf x) γ hγ hreg
  rw [legendreTransport_unique ν μ a b γ hγ hreg huv]
  have hT : ∀ x, legendreTransport (νf x) (μf x) γ (af x) (bf x) = ux x 1 :=
    fun x => legendreTransport_unique _ _ _ _ γ hγ hreg (hx x)
  simp only [hT]
  have hα : Tendsto (fun x => νf x*(νf x+1)) l (𝓝 (ν*(ν+1))) := hν.mul (hν.add_const 1)
  have hβ : Tendsto (fun x => μf x^2) l (𝓝 (μ^2)) := hμ.pow 2
  obtain ⟨A, hAd⟩ : ∃ A : ℝ, A = ‖ν*(ν+1)‖+1 := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, B = ‖μ^2‖+1 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAd]; positivity
  have hB0 : 0 ≤ B := by rw [hBd]; positivity
  obtain ⟨K, hKd⟩ : ∃ K : ℝ, K = G + G*Qi*(2*Γ0 + A + B*Qi) + 1 := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hKd]; positivity
  have hK1 : G ≤ K := by rw [hKd]; have : 0 ≤ G*Qi*(2*Γ0 + A + B*Qi) := by positivity
                         linarith
  have hK2 : G*Qi*(2*Γ0 + A + B*Qi) ≤ K := by rw [hKd]; linarith
  have hε : Tendsto (fun x => G*Qi*(‖νf x*(νf x+1)-ν*(ν+1)‖+‖μf x^2-μ^2‖*Qi)*U) l (𝓝 0) := by
    have h1 := (hα.sub_const (ν*(ν+1))).norm
    have h2 := (hβ.sub_const (μ^2)).norm
    simp only [sub_self, norm_zero] at h1 h2
    have := ((tendsto_const_nhds (x := G*Qi)).mul (h1.add (h2.mul_const Qi))).mul_const U
    simpa using this
  have hδ : Tendsto (fun x => max ‖af x - a‖ ‖bf x - b‖) l (𝓝 0) := by
    have h := ((ha.sub_const a).prodMk_nhds (hb.sub_const b)).norm
    simpa using h
  have hbound : ∀ᶠ x in l, ‖ux x 1 - u 1‖ ≤ max ‖af x - a‖ ‖bf x - b‖ * Real.exp K +
      G*Qi*(‖νf x*(νf x+1)-ν*(ν+1)‖+‖μf x^2-μ^2‖*Qi)*U / K * (Real.exp K - 1) := by
    have hA : ∀ᶠ x in l, ‖νf x*(νf x+1)‖ ≤ A := by
      filter_upwards [hα.norm.eventually (gt_mem_nhds (lt_add_one ‖ν*(ν+1)‖))] with x hx
      rw [hAd]; exact hx.le
    have hB : ∀ᶠ x in l, ‖μf x^2‖ ≤ B := by
      filter_upwards [hβ.norm.eventually (gt_mem_nhds (lt_add_one ‖μ^2‖))] with x hx
      rw [hBd]; exact hx.le
    filter_upwards [hA, hB] with x hAx hBx
    obtain ⟨hu0', hv0', hcu, hcv, hd⟩ := hx x
    obtain ⟨hu0, hv0, hcu0, hcv0, hd0⟩ := huv
    obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = G*Qi*(‖νf x*(νf x+1)-ν*(ν+1)‖+‖μf x^2-μ^2‖*Qi)*U := ⟨_, rfl⟩
    have hε0 : 0 ≤ ε := by rw [hεd]; positivity
    rw [← hεd]
    have hfc : ContinuousOn (fun t => (ux x t - u t, vx x t - v t)) (Icc 0 1) :=
      (hcu.sub hcu0).prodMk (hcv.sub hcv0)
    have hfd : ∀ t ∈ Ico (0:ℝ) 1, HasDerivWithinAt (fun t => (ux x t - u t, vx x t - v t))
        ((deriv γ t*vx x t - deriv γ t*v t,
          deriv γ t*(2*γ t*vx x t-(νf x*(νf x+1)-μf x^2/(1-(γ t)^2))*ux x t)/(1-(γ t)^2) -
          deriv γ t*(2*γ t*v t-(ν*(ν+1)-μ^2/(1-(γ t)^2))*u t)/(1-(γ t)^2)) : ℂ × ℂ) (Ici t) t := by
      intro t ht
      have htI : t ∈ Icc (0:ℝ) 1 := Ico_subset_Icc_self ht
      have hm := Icc_mem_nhdsGE_of_mem ht
      exact ((((hd t htI).1.sub (hd0 t htI).1)).prodMk ((hd t htI).2.sub (hd0 t htI).2)).mono_of_mem_nhdsWithin hm
    have hf0 : ‖((ux x 0 - u 0, vx x 0 - v 0) : ℂ × ℂ)‖ ≤ max ‖af x - a‖ ‖bf x - b‖ := by
      rw [hu0, hv0, hu0', hv0', Prod.norm_def]
    have hfb : ∀ t ∈ Ico (0:ℝ) 1, ‖((deriv γ t*vx x t - deriv γ t*v t,
          deriv γ t*(2*γ t*vx x t-(νf x*(νf x+1)-μf x^2/(1-(γ t)^2))*ux x t)/(1-(γ t)^2) -
          deriv γ t*(2*γ t*v t-(ν*(ν+1)-μ^2/(1-(γ t)^2))*u t)/(1-(γ t)^2)) : ℂ × ℂ)‖ ≤
        K * ‖((ux x t - u t, vx x t - v t) : ℂ × ℂ)‖ + ε := by
      intro t ht
      have htI : t ∈ Icc (0:ℝ) 1 := Ico_subset_Icc_self ht
      rw [Prod.norm_def, Prod.norm_def]
      simp only
      have hM : 0 ≤ max ‖ux x t - u t‖ ‖vx x t - v t‖ :=
        le_trans (norm_nonneg _) (le_max_left _ _)
      refine max_le ?_ ?_
      · rw [← mul_sub, norm_mul]
        have h2 : ‖vx x t - v t‖ ≤ max ‖ux x t - u t‖ ‖vx x t - v t‖ := le_max_right _ _
        have h3 := hG' t htI
        calc ‖deriv γ t‖ * ‖vx x t - v t‖ ≤ G * max ‖ux x t - u t‖ ‖vx x t - v t‖ :=
              mul_le_mul h3 h2 (norm_nonneg _) hG0
          _ ≤ K * max ‖ux x t - u t‖ ‖vx x t - v t‖ := mul_le_mul_of_nonneg_right hK1 hM
          _ ≤ _ := le_add_of_nonneg_right hε0
      · have h := legTr_diff_bound (g := deriv γ t) (γ := γ t) (q := 1-(γ t)^2)
          (α := νf x*(νf x+1)) (β := μf x^2) (α0 := ν*(ν+1)) (β0 := μ^2)
          (ux := ux x t) (vx := vx x t) (u := u t) (v := v t)
          (hG' t htI) (hΓ' t htI) (hQ' t htI) hAx hBx (hU t htI) hG0 hQ0 hΓ0 hA0 hB0
        rw [← hεd] at h
        refine h.trans (add_le_add_left (mul_le_mul_of_nonneg_right hK2 hM) ε |>.trans_eq' ?_ |>.trans_eq ?_)
        · ring
        · ring
    have hgr := norm_le_gronwallBound_of_norm_deriv_right_le hfc hfd hf0 hfb 1 ⟨zero_le_one, le_rfl⟩
    rw [gronwallBound_of_K_ne_0 hK.ne', sub_zero] at hgr
    simp only [mul_one] at hgr
    have : ‖ux x 1 - u 1‖ ≤ ‖((ux x 1 - u 1, vx x 1 - v 1) : ℂ × ℂ)‖ := by
      rw [Prod.norm_def]; exact le_max_left _ _
    exact this.trans hgr
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hbound ?_
  have := (hδ.mul_const (Real.exp K)).add ((hε.div_const K).mul_const (Real.exp K - 1))
  simpa using this

/-- The transport depends on the order only through `μ²`. -/
theorem legTr_transport_neg_order (ν μ : ℂ) (γ : ℝ → ℂ) (a b : ℂ) :
    legendreTransport ν (-μ) γ a b = legendreTransport ν μ γ a b := by
  simp only [legendreTransport, IsLegendreTransport, neg_sq]

/-- The transport is linear in the initial data. -/
theorem legTr_transport_linear (ν μ : ℂ) {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hreg : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ 1 ∧ γ t ≠ -1) (c₁ c₂ a₁ b₁ a₂ b₂ : ℂ) :
    legendreTransport ν μ γ (c₁*a₁ + c₂*a₂) (c₁*b₁ + c₂*b₂) =
      c₁*legendreTransport ν μ γ a₁ b₁ + c₂*legendreTransport ν μ γ a₂ b₂ := by
  obtain ⟨u₁, v₁, h₁⟩ := legendreTransport_exists ν μ a₁ b₁ γ hγ hreg
  obtain ⟨u₂, v₂, h₂⟩ := legendreTransport_exists ν μ a₂ b₂ γ hγ hreg
  rw [legendreTransport_unique _ _ _ _ γ hγ hreg h₁, legendreTransport_unique _ _ _ _ γ hγ hreg h₂]
  obtain ⟨hu₁, hv₁, hcu₁, hcv₁, hd₁⟩ := h₁
  obtain ⟨hu₂, hv₂, hcu₂, hcv₂, hd₂⟩ := h₂
  have h : IsLegendreTransport ν μ γ (c₁*a₁ + c₂*a₂) (c₁*b₁ + c₂*b₂)
      (fun t => c₁*u₁ t + c₂*u₂ t) (fun t => c₁*v₁ t + c₂*v₂ t) := by
    refine ⟨by simp [hu₁, hu₂], by simp [hv₁, hv₂],
      (continuousOn_const.mul hcu₁).add (continuousOn_const.mul hcu₂),
      (continuousOn_const.mul hcv₁).add (continuousOn_const.mul hcv₂), fun t ht => ⟨?_, ?_⟩⟩
    · exact (((hd₁ t ht).1.const_mul c₁).add ((hd₂ t ht).1.const_mul c₂)).congr_deriv (by ring)
    · exact (((hd₁ t ht).2.const_mul c₁).add ((hd₂ t ht).2.const_mul c₂)).congr_deriv (by ring)
  exact legendreTransport_unique _ _ _ _ γ hγ hreg h

/-- `legendreOneLoop` avoids `±1`. -/
theorem legTr_loop_reg {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    ∀ t ∈ Icc (0:ℝ) 1, legendreOneLoop z s t ≠ 1 ∧ legendreOneLoop z s t ≠ -1 := by
  intro t ht
  rcases legTr_loop_dom hz s ht with h | h
  · refine ⟨fun h1 => slitPlane_ne_zero h (by rw [h1]; ring), fun h1 => ?_⟩
    rw [h1] at h; norm_num [mem_slitPlane_iff] at h
  · have hn : ‖legendreOneLoop z s t‖ < 1 := by simpa using h
    refine ⟨fun h1 => by rw [h1] at hn; simp at hn, fun h1 => by rw [h1] at hn; simp at hn⟩

/-- DLMF 14.24.4 for non-integer order, from 14.24.3 for `P^{±μ}_ν` and the connection formula. -/
theorem legTr_one_olverQ_nonint (ν m : ℂ) (hm : ∀ n : ℤ, m ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    legendreOneContinued (olverQ ν m) ν m z s = exp (-s*m*π*I)*olverQ ν m z-
      π*I*sin (s*m*π)/(sin (m*π)*Gamma (ν-m+1))*associatedP ν (-m) z := by
  have hγ := legTr_contDiff_loop z s
  have hreg := legTr_loop_reg hz s
  have hP : legendreTransport ν m (legendreOneLoop z s) (associatedP ν m z) (deriv (associatedP ν m) z) =
      exp (-s*m*π*I) * associatedP ν m z := by
    have h := associatedP_one_continuation ν (-m) hz s
    rw [neg_neg] at h
    unfold legendreOneContinued at h
    rw [legTr_transport_neg_order] at h
    rw [h]; congr 1; ring_nf
  have hM : legendreTransport ν m (legendreOneLoop z s) (associatedP ν (-m) z)
      (deriv (associatedP ν (-m)) z) = exp (s*m*π*I) * associatedP ν (-m) z :=
    associatedP_one_continuation ν m hz s
  unfold legendreOneContinued
  rw [olverQ_eq_nonint ν m hm hz, deriv_olverQ_nonint ν m hm hz]
  set C := π/(2*sin (m*π))
  set g1 := (Gamma (ν+m+1))⁻¹
  set g2 := (Gamma (ν-m+1))⁻¹ with hg2
  have e1 : C*(associatedP ν m z*g1 - associatedP ν (-m) z*g2) =
      (C*g1)*associatedP ν m z + (-(C*g2))*associatedP ν (-m) z := by ring
  have e2 : C*(deriv (associatedP ν m) z*g1 - deriv (associatedP ν (-m)) z*g2) =
      (C*g1)*deriv (associatedP ν m) z + (-(C*g2))*deriv (associatedP ν (-m)) z := by ring
  rw [e1, e2, legTr_transport_linear ν m hγ hreg, hP, hM]
  have hsin := legendre_sin_ne_zero hm
  have hs : sin (s*m*π) = (exp (-s*m*π*I) - exp (s*m*π*I))*I/2 := by
    rw [Complex.sin]; ring_nf
  rw [hs]
  simp only [C, div_eq_mul_inv, mul_inv]
  rw [← hg2]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- The transport depends on the degree only through `ν(ν+1)`. -/
theorem legTr_transport_degree_eq {ν ν' : ℂ} (h : ν'*(ν'+1) = ν*(ν+1)) (μ : ℂ) (γ : ℝ → ℂ) (a b : ℂ) :
    legendreTransport ν' μ γ a b = legendreTransport ν μ γ a b := by
  simp only [legendreTransport, IsLegendreTransport, h]

/-- The ellipse path is `C¹`. -/
theorem legTr_contDiff_ellipse (z : ℂ) (s : ℤ) : ContDiff ℝ 1 (legendreEllipsePath z s) := by
  have he : legendreEllipsePath z s = fun t : ℝ =>
      ((z + exp ((log (z-1) + log (z+1))/2)) * exp ((s:ℂ)*π*I * ofRealCLM t) +
        (z + exp ((log (z-1) + log (z+1))/2))⁻¹ * exp ((-(s:ℂ))*π*I * ofRealCLM t))/2 := by
    funext t; simp only [legendreEllipsePath, ofRealCLM_apply]
  rw [he]
  have h1 : ContDiff ℝ 1 (fun t : ℝ => ofRealCLM t) := ofRealCLM.contDiff
  fun_prop

/-- `ν ↦ ∂_z P^{-μ}_ν(z)` is continuous. -/
theorem legTr_continuous_deriv_associatedP_degree (μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    Continuous fun ν => deriv (associatedP ν (-μ)) z := by
  have hw := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  have e := funext fun ν => deriv_associatedP ν (-μ) hz
  rw [e]
  have hP := (associatedP_entire_degree (-μ) z hz).continuous
  have hG := (differentiable_regularizedGaussHG_comp (A := fun ν : ℂ => ν+1+1) (B := fun ν : ℂ => -ν+1)
    (C := fun _ : ℂ => 1-(-μ)+1) (by fun_prop) (by fun_prop) (by fun_prop) hw).continuous
  exact (continuous_const.mul hP).sub ((by fun_prop : Continuous fun ν : ℂ => (ν+1)*(-ν)/2).mul
    (continuous_const.mul hG))

/-- DLMF 14.24.1 off the zeros of `cos νπ`, from 14.24.2 for `𝑸^μ_ν`, `𝑸^μ_{-ν-1}` and 14.9.12. -/
theorem legTr_ellipse_associatedP_generic (ν μ : ℂ) (hc : cos (ν*π) ≠ 0) {z : ℂ} (hz : z-1 ∈ slitPlane)
    (s : ℤ) :
    legendreEllipseContinued (associatedP ν (-μ)) ν μ z s = exp (s*ν*π*I)*associatedP ν (-μ) z+
      2*I*sin ((ν+1/2)*s*π)*exp (-s*π*I/2)/(cos (ν*π)*Gamma (μ-ν))*olverQ ν μ z := by
  have hγ := legTr_contDiff_ellipse z s
  have hreg : ∀ t ∈ Icc (0:ℝ) 1, legendreEllipsePath z s t ≠ 1 ∧ legendreEllipsePath z s t ≠ -1 :=
    fun t _ => legInt_path_ne hz s t
  set g1 := (Gamma (μ-ν))⁻¹ with hg1
  set g2 := (Gamma (ν+μ+1))⁻¹ with hg2
  set c := (cos (ν*π))⁻¹ with hcdef
  have hconn : ∀ w : ℂ, w-1 ∈ slitPlane →
      associatedP ν (-μ) w = (-c*g1)*olverQ ν μ w + (c*g2)*olverQ (-ν-1) μ w := by
    intro w hw
    have h := associated_connection_12 ν μ hw
    simp only [div_eq_mul_inv] at h
    rw [hcdef]; field_simp; linear_combination h
  have hev : associatedP ν (-μ) =ᶠ[𝓝 z] fun w => (-c*g1)*olverQ ν μ w + (c*g2)*olverQ (-ν-1) μ w := by
    filter_upwards [isOpen_sub_one_mem_slitPlane.mem_nhds hz] with w hw using hconn w hw
  have hd : deriv (associatedP ν (-μ)) z =
      (-c*g1)*deriv (olverQ ν μ) z + (c*g2)*deriv (olverQ (-ν-1) μ) z := by
    rw [hev.deriv_eq]
    have h1 := (olverQ_analytic ν μ z hz).differentiableAt.hasDerivAt
    have h2 := (olverQ_analytic (-ν-1) μ z hz).differentiableAt.hasDerivAt
    exact ((h1.const_mul (-c*g1)).add (h2.const_mul (c*g2))).deriv
  have hQ1 := olverQ_ellipse_continuation ν μ hz s
  have hQ2 := olverQ_ellipse_continuation (-ν-1) μ hz s
  unfold legendreEllipseContinued at hQ1 hQ2 ⊢
  rw [legTr_transport_degree_eq (ν := ν) (by ring)] at hQ2
  rw [hconn z hz, hd, legTr_transport_linear ν μ hγ hreg, hQ1, hQ2]
  have hs : sin ((ν+1/2)*s*π) = (exp (-((ν+1/2)*s*π)*I) - exp (((ν+1/2)*s*π)*I))*I/2 := by
    rw [Complex.sin]
  have hcos : cos (ν*π) * c = 1 := mul_inv_cancel₀ hc
  have hconnz := associated_connection_12 ν μ hz
  simp only [div_eq_mul_inv] at hconnz
  rw [← hg1, ← hg2] at hconnz
  rw [hs]
  have hE1 : exp (-((ν+1/2)*s*π)*I) * exp (-s*π*I/2) = (-1:ℂ)^s * exp (-s*ν*π*I) := by
    rw [← exp_add, show -((ν+1/2)*s*π)*I + -s*π*I/2 = (s:ℂ)*(-(π*I)) + -s*ν*π*I by ring,
      exp_add, exp_int_mul, exp_neg, exp_pi_mul_I]; norm_num
  have hE2 : exp (((ν+1/2)*s*π)*I) * exp (-s*π*I/2) = exp (s*ν*π*I) := by
    rw [← exp_add]; congr 1; ring
  have hE3 : (-1:ℂ)^s * exp (-s*(-ν-1)*π*I) = exp (s*ν*π*I) := by
    rw [show -s*(-ν-1)*π*I = (s:ℂ)*(π*I) + s*ν*π*I by ring, exp_add, exp_int_mul, exp_pi_mul_I,
      ← mul_assoc, ← mul_zpow]; norm_num
  rw [div_eq_mul_inv _ (cos (ν*π)*Gamma (μ-ν)), mul_inv, ← hcdef, ← hg1]
  linear_combination (c*g1*olverQ ν μ z)*hE1 - (c*g1*olverQ ν μ z)*hE2 +
    (c*g2*olverQ (-ν-1) μ z)*hE3 -
    ((exp (-((ν+1/2)*s*π)*I)*exp (-s*π*I/2) - exp (((ν+1/2)*s*π)*I)*exp (-s*π*I/2))*c*g1*
      olverQ ν μ z)*I_sq

/-- The parameter limit retains odd half-integral degrees.

Moved within this file (round 13) below DLMF 14.24.2–14.24.3: off the zeros of `cos νπ` the
identity follows from 14.24.2 for `𝑸^μ_ν`, `𝑸^μ_{-ν-1}` and 14.9.12
(`legTr_ellipse_associatedP_generic`); the limit uses the continuity of the transport in the
degree (`legTr_transport_tendsto`). -/
@[dlmf 14.24.E1]
theorem associatedP_ellipse_continuation (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    Tendsto (fun v : ℂ => exp (s*v*π*I)*associatedP v (-μ) z+2*I*sin ((v+1/2)*s*π)*exp (-s*π*I/2)/(cos (v*π)*Gamma (μ-v))*olverQ v μ z) (𝓝[≠] ν) (𝓝 (legendreEllipseContinued (associatedP ν (-μ)) ν μ z s)) := by

  have hγ := legTr_contDiff_ellipse z s
  have hreg : ∀ t ∈ Icc (0:ℝ) 1, legendreEllipsePath z s t ≠ 1 ∧ legendreEllipsePath z s t ≠ -1 :=
    fun t _ => legInt_path_ne hz s t
  have hcont : Tendsto (fun v => legendreEllipseContinued (associatedP v (-μ)) v μ z s) (𝓝[≠] ν)
      (𝓝 (legendreEllipseContinued (associatedP ν (-μ)) ν μ z s)) :=
    legTr_transport_tendsto (l := 𝓝[≠] ν) hγ hreg (νf := id) (μf := fun _ => μ)
      (af := fun v => associatedP v (-μ) z) (bf := fun v => deriv (associatedP v (-μ)) z)
      (tendsto_id.mono_left nhdsWithin_le_nhds) tendsto_const_nhds
      (((associatedP_entire_degree (-μ) z hz).continuous.tendsto ν).mono_left nhdsWithin_le_nhds)
      (((legTr_continuous_deriv_associatedP_degree μ hz).tendsto ν).mono_left nhdsWithin_le_nhds)
  refine hcont.congr' ?_
  have hf : AnalyticOnNhd ℂ (fun v : ℂ => cos (v*π)) univ := fun v _ =>
    ((Complex.differentiable_cos.comp (differentiable_id.mul_const _)).analyticAt v)
  have hnz : ∀ᶠ v in 𝓝[≠] ν, cos (v*π) ≠ 0 := by
    rcases (hf ν (mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ ν) h
        (mem_univ 0)
      simp at this
    · exact h
  filter_upwards [hnz] with v hv
  rw [legTr_ellipse_associatedP_generic v μ hv hz s]

/-- Integer orders use the removable parameter limit of the complete expression.

For non-integer order the identity follows from 14.24.3 for `P^{±μ}_ν` and the connection formula
(`legTr_one_olverQ_nonint`); the limit uses the continuity of the transport in the order
(`legTr_transport_tendsto`). -/
@[dlmf 14.24.E4]
theorem olverQ_one_continuation (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    Tendsto (fun m : ℂ => exp (-s*m*π*I)*olverQ ν m z-π*I*sin (s*m*π)/(sin (m*π)*Gamma (ν-m+1))*associatedP ν (-m) z) (𝓝[≠] μ) (𝓝 (legendreOneContinued (olverQ ν μ) ν μ z s)) := by

  have hγ := legTr_contDiff_loop z s
  have hreg := legTr_loop_reg hz s
  have hcont : Tendsto (fun m => legendreOneContinued (olverQ ν m) ν m z s) (𝓝[≠] μ)
      (𝓝 (legendreOneContinued (olverQ ν μ) ν μ z s)) :=
    legTr_transport_tendsto (l := 𝓝[≠] μ) hγ hreg (νf := fun _ => ν) (μf := id)
      (af := fun m => olverQ ν m z) (bf := fun m => deriv (olverQ ν m) z) tendsto_const_nhds
      (tendsto_id.mono_left nhdsWithin_le_nhds)
      (((olverQ_entire_order ν z hz).continuous.tendsto μ).mono_left nhdsWithin_le_nhds)
      (((continuous_deriv_olverQ_order ν hz).tendsto μ).mono_left nhdsWithin_le_nhds)
  refine hcont.congr' ?_
  have hf : AnalyticOnNhd ℂ (fun m : ℂ => sin (m*π)) univ := fun m _ =>
    ((Complex.differentiable_sin.comp (differentiable_id.mul_const _)).analyticAt m)
  have hnint : ∀ᶠ m in 𝓝[≠] μ, ∀ n : ℤ, (m:ℂ) ≠ (n:ℂ) := by
    rcases (hf μ (mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ μ) h
        (mem_univ (1/2))
      simp only [Pi.zero_apply] at this
      rw [show (1/2:ℂ)*π = (π/2:ℝ) by push_cast; ring, ← ofReal_sin, Real.sin_pi_div_two] at this
      norm_num at this
    · filter_upwards [h] with m hm n hn
      apply hm; rw [hn]; exact Complex.sin_int_mul_pi n
  filter_upwards [hnint] with m hm
  exact legTr_one_olverQ_nonint ν m hm hz s

end DLMF.Legendre
