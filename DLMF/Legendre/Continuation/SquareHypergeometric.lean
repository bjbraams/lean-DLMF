/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Continuation.LogarithmicBranches

/-!
# The square-argument hypergeometric form of `P^{-μ}_ν` on `(1, ∞)` (DLMF 14.3.17)

DLMF 14.3.17 expresses `P^{-μ}_ν(x)` for `x > 1` through `𝐅((μ-ν)/2, (ν+μ+1)/2; 1/2; x²)` and
`𝐅((μ-ν+1)/2, (ν+μ+2)/2; 3/2; x²)`, whose argument `x²` lies on the cut `[1, ∞)` of the
hypergeometric functions. It is stated here as a limit of the boundary values from above.

The proof continues the even and odd quadratic Ferrers representation (`ferrersP_even_odd`) from
`(-1, 1)` into the unit disk and then, through `associatedP_eq_ferrersPCont`, to the whole upper
half-plane, where `P^{-μ}_ν(z)` equals the same combination with `z²` in place of `x²`. On the
path `z = (x² + iε)^{1/2}` this reduces the limit to the boundedness of the second
hypergeometric term, which follows from the companion representation of `𝑸^μ_ν` in the upper
half-plane (DLMF 14.23.3 continued), with the reflection formula making the elimination
possible whenever the corresponding coefficient is nonzero.

## Main results

* `associatedP_square_hypergeometric`: DLMF 14.3.17 as a boundary-value limit.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat

namespace DLMF.Legendre

/-- The bracket of DLMF 14.3.17 as a function of `z`, with `z²` the hypergeometric argument. -/
private noncomputable def squareHypBracket (ν μ z : ℂ) : ℂ :=
  regularizedGaussHG ((μ-ν)/2) ((ν+μ+1)/2) (1/2) (z^2)/(Gamma ((μ-ν+1)/2)*Gamma ((ν+μ+2)/2)) -
    z*regularizedGaussHG ((μ-ν+1)/2) ((ν+μ+2)/2) (3/2) (z^2)/(Gamma ((μ-ν)/2)*Gamma ((ν+μ+1)/2))

/-- The bracket is analytic wherever `z²` lies in the cut plane. -/
private lemma squareHypBracket_analyticAt (ν μ : ℂ) {z : ℂ} (hz : z^2 ∈ cutPlane) :
    AnalyticAt ℂ (squareHypBracket ν μ) z := by
  have h1 : AnalyticAt ℂ (fun w : ℂ => regularizedGaussHG ((μ-ν)/2) ((ν+μ+1)/2) (1/2) (w^2)) z :=
    (analyticAt_regularizedGaussHG _ _ _ hz).comp_of_eq (by fun_prop) rfl
  have h2 : AnalyticAt ℂ
      (fun w : ℂ => regularizedGaussHG ((μ-ν+1)/2) ((ν+μ+2)/2) (3/2) (w^2)) z :=
    (analyticAt_regularizedGaussHG _ _ _ hz).comp_of_eq (by fun_prop) rfl
  unfold squareHypBracket
  simp only [div_eq_mul_inv]
  exact (h1.mul analyticAt_const).sub ((analyticAt_id.mul h2).mul analyticAt_const)

/-- The quadratic form of `𝖯^{-μ}_ν(y)` on `(-1, 1)` (DLMF 14.3.11 rewritten by reflection). -/
private lemma ferrersPCont_neg_eq_real (ν μ : ℂ) {y : ℝ} (hy : y ∈ Ioo (-1:ℝ) 1) :
    ferrersPCont ν (-μ) y = π*(1-(y:ℂ)^2)^(μ/2)/2^μ*squareHypBracket ν μ y := by
  rw [ferrersPCont_ofReal ν (-μ) hy, ferrersP_even_odd ν (-μ) hy]
  unfold ferrersEven ferrersOdd squareHypBracket
  rw [show (1-ν-(-μ))/2 = (μ-ν+1)/2 by ring, show (ν-(-μ)+2)/2 = (ν+μ+2)/2 by ring,
    show -(ν+(-μ))/2 = (μ-ν)/2 by ring, show (ν-(-μ)+1)/2 = (ν+μ+1)/2 by ring,
    show -(-μ)/2 = μ/2 by ring, cpow_neg]
  ring

/-- The quadratic form of `𝖯^{-μ}_ν`, continued into the unit disk. -/
private lemma ferrersPCont_neg_eq (ν μ : ℂ) {z : ℂ} (hz : z ∈ Metric.ball (0:ℂ) 1) :
    ferrersPCont ν (-μ) z = π*(1-z^2)^(μ/2)/2^μ*squareHypBracket ν μ z := by
  have hR : AnalyticOnNhd ℂ (fun w => π*(1-w^2)^(μ/2)/2^μ*squareHypBracket ν μ w)
      (Metric.ball (0:ℂ) 1) := by
    intro w hw
    obtain ⟨-, -, -, hsl, hc⟩ := legendre_disk_facts hw
    have hW : AnalyticAt ℂ (fun w : ℂ => (1-w^2)^(μ/2)) w :=
      (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 1-w^2) w).cpow analyticAt_const hsl
    simp only [div_eq_mul_inv]
    exact ((analyticAt_const.mul hW).mul analyticAt_const).mul
      (squareHypBracket_analyticAt ν μ hc)
  have h0 : ((0:ℝ):ℂ) ∈ Metric.ball (0:ℂ) 1 := by simp
  refine (ferrersPCont_analytic ν (-μ)).eqOn_of_preconnected_of_frequently_eq hR
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
  exact ferrersPCont_neg_eq_real ν μ hy

/-- Facts about a point of the upper half-plane. -/
private lemma upper_facts {w : ℂ} (hw : 0 < w.im) :
    w-1 ∈ slitPlane ∧ w+1 ∈ slitPlane ∧ (1-w)/2 ∈ cutPlane ∧ w^2 ∈ cutPlane ∧
      w ∈ slitPlane ∧ 1/w^2 ∈ cutPlane := by
  have h1 : w-1 ∈ slitPlane := Or.inr (by simp; exact hw.ne')
  refine ⟨h1, Or.inr (by simp; exact hw.ne'), ?_, ?_, Or.inr hw.ne',
    one_sub_recip_sq_mem_slitPlane_of_sub_one h1⟩
  · rw [mem_cutPlane, show (1:ℂ)-(1-w)/2 = (1+w)/2 by ring]
    exact Or.inr (by simp; exact hw.ne')
  · rw [mem_cutPlane]
    by_cases hre : w.re = 0
    · left
      simp [pow_two, hre]
      nlinarith
    · right
      simp [pow_two]
      intro h
      have h' : w.re * w.im = 0 := by linarith
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact hre h''
      · linarith

/-- In the upper half-plane, `(z²-1)^{μ/2} = e^{μπi/2} (1-z²)^{μ/2}` with principal branches. -/
private lemma legendreBranchPower_upper (μ : ℂ) {z : ℂ} (hz : 0 < z.im) :
    legendreBranchPower μ z = exp (μ*π*I/2)*(1-z^2)^(μ/2) := by
  have h1 := legendre_log_sub_one_side (s := 1) (Or.inl rfl) (z := z) (by simpa using hz)
  have ha : 1 - z ≠ 0 := fun h => by
    have := congrArg im h; simp at this; linarith
  have hb : z + 1 ≠ 0 := fun h => by
    have := congrArg im h; simp at this; linarith
  have hlog : log (1-z) + log (z+1) = log (1-z^2) := by
    rw [show 1 - z^2 = (1-z)*(z+1) by ring]
    refine ((log_mul_eq_add_log_iff ha hb).mpr ?_).symm
    have e1 : arg (1-z) < 0 := arg_neg_iff.mpr (by simp; linarith)
    have e2 : 0 ≤ arg (z+1) := arg_nonneg_iff.mpr (by simp; linarith)
    have e3 := neg_pi_lt_arg (1-z)
    have e4 := arg_le_pi (z+1)
    constructor <;> linarith
  have hne : 1 - z^2 ≠ 0 := by
    rw [show 1 - z^2 = (1-z)*(z+1) by ring]; exact mul_ne_zero ha hb
  unfold legendreBranchPower
  rw [h1, cpow_def_of_ne_zero hne, ← exp_add, ← hlog]
  congr 1
  push_cast
  ring

/-- In the upper half-plane, `P^{-μ}_ν(z)` is the bracket of DLMF 14.3.17 at `z`. -/
private lemma associatedP_neg_eq_upper (ν μ : ℂ) {z : ℂ} (hz : 0 < z.im) :
    associatedP ν (-μ) z = π*legendreBranchPower μ z/2^μ*squareHypBracket ν μ z := by
  set U : Set ℂ := {w | 0 < w.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hUc : IsPreconnected U := (convex_halfSpace_im_gt 0).isPreconnected
  have hf : AnalyticOnNhd ℂ (fun w => associatedP ν (-μ) w) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    obtain ⟨h2, h1, h4, -, -, -⟩ := upper_facts hw
    unfold associatedP
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := assumption)
  have hg : AnalyticOnNhd ℂ (fun w => π*legendreBranchPower μ w/2^μ*squareHypBracket ν μ w) U := by
    intro w hw
    obtain ⟨h2, h1, -, h4, -, -⟩ := upper_facts hw
    have hB : AnalyticAt ℂ (legendreBranchPower μ) w := by
      unfold legendreBranchPower
      fun_prop (disch := assumption)
    simp only [div_eq_mul_inv]
    exact ((analyticAt_const.mul hB).mul analyticAt_const).mul
      (squareHypBracket_analyticAt ν μ h4)
  have hz0 : I/2 ∈ U := by simp [hU]
  have hball : I/2 ∈ Metric.ball (0:ℂ) 1 := by
    simp; norm_num
  have hev : (fun w => associatedP ν (-μ) w) =ᶠ[𝓝 (I/2)]
      (fun w => π*legendreBranchPower μ w/2^μ*squareHypBracket ν μ w) := by
    filter_upwards [inter_mem (hUo.mem_nhds hz0) (Metric.isOpen_ball.mem_nhds hball)] with w hw
    obtain ⟨hwU, hwB⟩ := hw
    rw [associatedP_eq_ferrersPCont (s := 1) (Or.inl rfl) ν (-μ) (by simpa [hU] using hwU),
      ferrersPCont_neg_eq ν μ hwB, legendreBranchPower_upper μ hwU]
    push_cast
    ring_nf
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUc hz0 hev hz

/-- `olverQSideHyp 1 ν μ` is analytic where `1 - z²` is in the slit plane. -/
private lemma olverQSideHyp_analyticAt (ν μ : ℂ) {z : ℂ} (hsl : 1 - z^2 ∈ slitPlane)
    (hc : z^2 ∈ cutPlane) : AnalyticAt ℂ (olverQSideHyp 1 ν μ) z := by
  have hW : AnalyticAt ℂ (fun w : ℂ => (1-w^2)^(μ/2)) z :=
    (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 1-w^2) z).cpow analyticAt_const hsl
  have hG1 : AnalyticAt ℂ (fun w : ℂ => regularizedGaussHG ((μ-ν+1)/2) ((ν+μ+2)/2) (3/2) (w^2)) z :=
    (analyticAt_regularizedGaussHG _ _ _ hc).comp_of_eq (by fun_prop) rfl
  have hG2 : AnalyticAt ℂ (fun w : ℂ => regularizedGaussHG ((μ-ν)/2) ((ν+μ+1)/2) (1/2) (w^2)) z :=
    (analyticAt_regularizedGaussHG _ _ _ hc).comp_of_eq (by fun_prop) rfl
  unfold olverQSideHyp
  exact ((analyticAt_const.mul hW).mul analyticAt_const).mul
    (((analyticAt_id.mul hG1).mul analyticAt_const).sub
        ((analyticAt_const.mul hG2).mul analyticAt_const))

/-- `𝑸^μ_ν` is analytic off `(-∞, 1]`. -/
private lemma olverQ_analyticAt (ν μ : ℂ) {w : ℂ} (h2 : w-1 ∈ slitPlane) :
    AnalyticAt ℂ (fun z => olverQ ν μ z) w := by
  have h1 : w + 1 ∈ slitPlane := by
    have := one_add_mem_slitPlane_of_sub_one h2; rwa [add_comm] at this
  have h3 : w ∈ slitPlane := by
    rw [mem_slitPlane_iff] at h2 ⊢
    rcases h2 with h | h
    · left; simp at h; linarith
    · right; simpa using h
  have h5 : 1/w^2 ∈ cutPlane := one_sub_recip_sq_mem_slitPlane_of_sub_one h2
  have h0 : w ^ 2 ≠ 0 := pow_ne_zero 2 (slitPlane_ne_zero h3)
  have h6 : w ^ (ν+μ+1) ≠ 0 := by
    rw [cpow_def_of_ne_zero (slitPlane_ne_zero h3)]; exact exp_ne_zero _
  have h7 : (2:ℂ) ^ (ν+1) ≠ 0 := by
    rw [cpow_def_of_ne_zero two_ne_zero]; exact exp_ne_zero _
  have hd : ∀ᶠ z in 𝓝 w, DifferentiableAt ℂ (fun z => olverQ ν μ z) z := by
    have hS : {z : ℂ | z - 1 ∈ slitPlane} ∈ 𝓝 w :=
      (isOpen_slitPlane.preimage (continuous_sub_right 1)).mem_nhds h2
    filter_upwards [hS] with v hv
    have hv1 : v + 1 ∈ slitPlane := by
      have := one_add_mem_slitPlane_of_sub_one hv; rwa [add_comm] at this
    have hv3 : v ∈ slitPlane := by
      rw [mem_slitPlane_iff] at hv ⊢
      rcases hv with h | h
      · left; simp at h; linarith
      · right; simpa using h
    have hv5 : 1/v^2 ∈ cutPlane := one_sub_recip_sq_mem_slitPlane_of_sub_one hv
    have hv0 : v ^ 2 ≠ 0 := pow_ne_zero 2 (slitPlane_ne_zero hv3)
    have hv6 : v ^ (ν+μ+1) ≠ 0 := by
      rw [cpow_def_of_ne_zero (slitPlane_ne_zero hv3)]; exact exp_ne_zero _
    unfold olverQ legendreBranchPower
    simp only [div_eq_mul_inv, mul_inv]
    fun_prop (disch := first | assumption | simpa [div_eq_mul_inv] using hv5)
  exact Complex.analyticAt_iff_eventually_differentiableAt.mpr hd

/-- In the upper half-plane, `𝑸^μ_ν(z) = olverQSideHyp 1 ν μ z` (DLMF 14.23.3 continued). -/
private lemma olverQ_eq_upper (ν μ : ℂ) {z : ℂ} (hz : 0 < z.im) :
    olverQ ν μ z = olverQSideHyp 1 ν μ z := by
  set U : Set ℂ := {w | 0 < w.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hUc : IsPreconnected U := (convex_halfSpace_im_gt 0).isPreconnected
  have hf : AnalyticOnNhd ℂ (fun w => olverQ ν μ w) U := fun w hw =>
    olverQ_analyticAt ν μ (upper_facts hw).1
  have hg : AnalyticOnNhd ℂ (fun w => olverQSideHyp 1 ν μ w) U := fun w hw =>
    olverQSideHyp_analyticAt ν μ (upper_facts hw).2.2.2.1 (upper_facts hw).2.2.2.1
  have hz0 : I/2 ∈ U := by simp [hU]
  have hball : I/2 ∈ Metric.ball (0:ℂ) 1 := by
    simp; norm_num
  have hev : (fun w => olverQ ν μ w) =ᶠ[𝓝 (I/2)] (fun w => olverQSideHyp 1 ν μ w) := by
    filter_upwards [inter_mem (hUo.mem_nhds hz0) (Metric.isOpen_ball.mem_nhds hball)] with w hw
    exact olverQ_eq_olverQSideHyp (s := 1) (Or.inl rfl) ν μ hw.2 (by simpa [hU] using hw.1)
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUc hz0 hev hz

/-- Combined boundary value at the hypergeometric cut; separate totalized values on that cut are not
used. -/
@[dlmf 14.3.E17]
theorem associatedP_square_hypergeometric (ν μ : ℂ) {x : ℝ} (hx : 1 < x) :
    Tendsto (fun ε : ℝ => let u : ℂ := x^2+I*ε;
        π*legendreBranchPower μ
        x/2^μ*(regularizedGaussHG ((μ-ν)/2) ((ν+μ+1)/2) (1/2)
        u/(Gamma ((μ-ν+1)/2)*Gamma ((ν+μ+2)/2))-x*regularizedGaussHG ((μ-ν+1)/2) ((ν+μ+2)/2) (3/2)
        u/(Gamma ((μ-ν)/2)*Gamma ((ν+μ+1)/2)))) (𝓝[>] 0) (𝓝 (associatedP ν (-μ) x)) := by
  have hx0 : (0:ℝ) < x := by linarith
  set u : ℝ → ℂ := fun ε => (x:ℂ)^2+I*ε with hu
  set z : ℝ → ℂ := fun ε => exp (log (u ε)/2) with hz
  have hu_im : ∀ ε : ℝ, (u ε).im = ε := fun ε => by simp [hu, pow_two]
  have hu0 : ∀ ε : ℝ, 0 < ε → u ε ≠ 0 := fun ε hε h => by
    have := hu_im ε; rw [h] at this; simp at this; linarith
  have hzsq : ∀ ε : ℝ, 0 < ε → z ε ^ 2 = u ε := by
    intro ε hε
    simp only [hz]
    rw [← exp_nat_mul]; push_cast
    rw [show 2*(log (u ε)/2) = log (u ε) by ring, exp_log (hu0 ε hε)]
  have hzre : ∀ ε : ℝ, 0 < ε → 0 < (z ε).re := by
    intro ε hε
    have harg1 : arg (u ε) ≠ π := fun h => by
      have := (arg_eq_pi_iff.mp h).2; rw [hu_im] at this; linarith
    have harg2 := neg_pi_lt_arg (u ε)
    have harg3 := arg_le_pi (u ε)
    simp only [hz, exp_re]
    refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    · simp [log_im]; linarith
    · simp [log_im]; have := lt_of_le_of_ne harg3 harg1; linarith
  have hzim : ∀ ε : ℝ, 0 < ε → 0 < (z ε).im := by
    intro ε hε
    have h := congrArg im (hzsq ε hε)
    rw [hu_im] at h
    simp [pow_two] at h
    nlinarith [hzre ε hε]
  have hu_lim : Tendsto u (𝓝[>] 0) (𝓝 ((x:ℂ)^2)) := by
    have : Tendsto u (𝓝 0) (𝓝 ((x:ℂ)^2+I*((0:ℝ):ℂ))) :=
      ((continuous_const.add (continuous_const.mul continuous_ofReal)).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hz_lim : Tendsto z (𝓝[>] 0) (𝓝 (x:ℂ)) := by
    have hsl : (x:ℂ)^2 ∈ slitPlane := Or.inl (by simp [pow_two]; positivity)
    have hc : ContinuousAt (fun w : ℂ => exp (log w/2)) ((x:ℂ)^2) :=
      ((continuousAt_clog hsl).div_const 2).cexp
    have hval : exp (log ((x:ℂ)^2)/2) = x := by
      rw [show (x:ℂ)^2 = ((x^2:ℝ):ℂ) by push_cast; ring, ← ofReal_log (by positivity),
        Real.log_pow, show (((2:ℕ) * Real.log x : ℝ) : ℂ)/2 = ((Real.log x : ℝ) : ℂ) by
          push_cast; ring, ← ofReal_exp, Real.exp_log hx0]
    have := hc.tendsto.comp hu_lim
    rwa [hval] at this
  have hx1 : (x:ℂ) - 1 ∈ slitPlane := Or.inl (by simp; linarith)
  have hxp : (x:ℂ) + 1 ∈ slitPlane := Or.inl (by simp; linarith)
  have hxc : (1-(x:ℂ))/2 ∈ cutPlane := by
    rw [mem_cutPlane]; exact Or.inl (by simp; linarith)
  have hxne : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2μ : (2:ℂ)^μ ≠ 0 := by
    rw [cpow_def_of_ne_zero two_ne_zero]; exact exp_ne_zero _
  set F1 : ℝ → ℂ := fun ε => regularizedGaussHG ((μ-ν)/2) ((ν+μ+1)/2) (1/2) (u ε) with hF1
  set F2 : ℝ → ℂ := fun ε => regularizedGaussHG ((μ-ν+1)/2) ((ν+μ+2)/2) (3/2) (u ε) with hF2
  set A : ℂ := (Gamma ((μ-ν+1)/2)*Gamma ((ν+μ+2)/2))⁻¹ with hA
  set B : ℂ := (Gamma ((μ-ν)/2)*Gamma ((ν+μ+1)/2))⁻¹ with hB
  set BP : ℂ → ℂ := legendreBranchPower μ with hBP
  have hBP0 : ∀ w, BP w ≠ 0 := fun w => exp_ne_zero _
  set P : ℂ → ℂ := fun w => associatedP ν (-μ) w with hPdef
  have hP : ∀ ε : ℝ, 0 < ε → P (z ε) = π*BP (z ε)/2^μ*(F1 ε * A - z ε * (F2 ε * B)) := by
    intro ε hε
    simp only [hPdef, hBP]
    rw [associatedP_neg_eq_upper ν μ (hzim ε hε)]
    unfold squareHypBracket
    rw [hzsq ε hε]
    simp only [div_eq_mul_inv, hF1, hF2, hA, hB]
    ring
  have hPc : ContinuousAt P x := by
    have : DifferentiableAt ℂ P x := by
      simp only [hPdef]; unfold associatedP; fun_prop (disch := assumption)
    exact this.continuousAt
  have hBPc : ContinuousAt BP x := by
    have : DifferentiableAt ℂ BP x := by
      simp only [hBP]; unfold legendreBranchPower; fun_prop (disch := assumption)
    exact this.continuousAt
  -- the bounded factor
  have hb : IsBoundedUnder (· ≤ ·) (𝓝[>] (0:ℝ)) (fun ε => ‖F2 ε * B‖) := by
    -- it suffices to exhibit a convergent function eventually equal to `F2 * B`
    suffices h : ∃ (g : ℝ → ℂ) (c : ℂ), Tendsto g (𝓝[>] (0:ℝ)) (𝓝 c) ∧
        ∀ ε : ℝ, 0 < ε → F2 ε * B = g ε by
      obtain ⟨g, c, hg, hgb⟩ := h
      refine (hg.norm.congr' ?_).isBoundedUnder_le
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [hgb ε hε]
    by_cases hs1 : Gamma ((ν+μ+1)/2) = 0
    · refine ⟨fun _ => 0, 0, tendsto_const_nhds, fun ε _ => ?_⟩
      simp [hB, hs1]
    by_cases hs2 : Gamma ((ν+μ+2)/2) = 0
    · refine ⟨fun ε => -(P (z ε)*2^μ)/(π*BP (z ε)*z ε), -(P x*2^μ)/(π*BP x*x), ?_,
        fun ε hε => ?_⟩
      · exact ((hPc.tendsto.comp hz_lim).mul_const _).neg.div
          ((tendsto_const_nhds.mul (hBPc.tendsto.comp hz_lim)).mul hz_lim)
          (mul_ne_zero (mul_ne_zero hπ (hBP0 x)) hxne)
      · have hA0 : A = 0 := by simp [hA, hs2]
        have hz0 : z ε ≠ 0 := fun h => by have := hzim ε hε; rw [h] at this; simp at this
        have h1 := hBP0 (z ε)
        show _ = -(P (z ε) * 2 ^ μ) / (↑π * BP (z ε) * z ε)
        rw [hP ε hε, hA0]
        field_simp
        ring
    -- generic case: eliminate `F1` with the second solution `𝑸^μ_ν`
    set q1 : ℂ := (Gamma ((ν-μ+2)/2))⁻¹*(Gamma ((ν+μ+2)/2))⁻¹ with hq1
    set q2 : ℂ := (Gamma ((ν-μ+1)/2))⁻¹*(Gamma ((ν+μ+1)/2))⁻¹ with hq2
    set D : ℂ := A*q2 - I*q1*B with hD
    have hD0 : D ≠ 0 := by
      have e := legendre_reflection_even (μ-ν)
      rw [show (1-(μ-ν))/2 = (ν-μ+1)/2 by ring] at e
      have o := legendre_reflection_odd (ν-μ)
      rw [show -(ν-μ)/2 = (μ-ν)/2 by ring, show (ν-μ)*π/2 = -((μ-ν)*π/2) by ring,
        Complex.sin_neg] at o
      have c := legendre_cos_sub_sin_exp (s := 1) (Or.inl rfl) ((μ-ν)*π/2)
      have k : π*D*Gamma ((ν+μ+1)/2)*Gamma ((ν+μ+2)/2) =
          (π*((Gamma ((ν-μ+1)/2))⁻¹*(Gamma ((μ-ν+1)/2))⁻¹) -
            I*(π*((Gamma ((μ-ν)/2))⁻¹*(Gamma ((ν-μ+2)/2))⁻¹)))*
          (Gamma ((ν+μ+1)/2)*(Gamma ((ν+μ+1)/2))⁻¹)*
          (Gamma ((ν+μ+2)/2)*(Gamma ((ν+μ+2)/2))⁻¹) := by
        simp only [hD, hA, hB, hq1, hq2, mul_inv]; ring
      rw [mul_inv_cancel₀ hs1, mul_inv_cancel₀ hs2, e, o] at k
      intro h0
      rw [h0] at k
      apply exp_ne_zero (-((1:ℝ):ℂ)*((μ-ν)*π/2)*I)
      rw [← c]
      simp only [ofReal_one, one_mul]
      linear_combination -k
    set K : ℝ → ℂ := fun ε => exp (-((1:ℝ):ℂ)*ν*π*I/2)*(π:ℂ)^(3/2:ℂ)*(1-u ε)^(μ/2)*
      ((2:ℂ)^(ν+1))⁻¹ with hK
    have hQ : ∀ ε : ℝ, 0 < ε → olverQ ν μ (z ε) = K ε * (z ε * F2 ε * q2 - I * F1 ε * q1) := by
      intro ε hε
      rw [olverQ_eq_upper ν μ (hzim ε hε)]
      unfold olverQSideHyp
      rw [hzsq ε hε]
      simp only [hK, hF1, hF2, hq1, hq2]
      push_cast
      ring
    have hune : ∀ ε : ℝ, 0 < ε → 1 - u ε ≠ 0 := fun ε hε h => by
      have := congrArg im h; simp [hu_im] at this; linarith
    have hL : Tendsto (fun ε => log (1 - u ε)) (𝓝[>] (0:ℝ))
        (𝓝 (Real.log ‖1-(x:ℂ)^2‖ - π*I)) := by
      have hre : (1-(x:ℂ)^2).re < 0 := by simp [pow_two]; nlinarith
      have him : (1-(x:ℂ)^2).im = 0 := by simp [pow_two]
      refine (tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him).comp ?_
      refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.sub hu_lim, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε hε
      show (1 - u ε).im < 0
      have hε' : (0:ℝ) < ε := hε
      simp [hu_im]; exact hε'
    have hcp : Tendsto (fun ε => (1-u ε)^(μ/2)) (𝓝[>] (0:ℝ))
        (𝓝 (exp ((Real.log ‖1-(x:ℂ)^2‖ - π*I)*(μ/2)))) := by
      refine ((continuous_exp.tendsto _).comp (hL.mul_const (μ/2))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      simp only [Function.comp]
      rw [cpow_def_of_ne_zero (hune ε hε)]
    have hπ32 : (π:ℂ)^(3/2:ℂ) ≠ 0 := by
      rw [cpow_def_of_ne_zero hπ]; exact exp_ne_zero _
    have h2ν : (2:ℂ)^(ν+1) ≠ 0 := by
      rw [cpow_def_of_ne_zero two_ne_zero]; exact exp_ne_zero _
    have hK_lim := ((tendsto_const_nhds (x := exp (-((1:ℝ):ℂ)*ν*π*I/2)*(π:ℂ)^(3/2:ℂ))).mul
      hcp).mul (tendsto_const_nhds (x := ((2:ℂ)^(ν+1))⁻¹))
    have hKl0 : exp (-((1:ℝ):ℂ)*ν*π*I/2)*(π:ℂ)^(3/2:ℂ)*
        exp ((Real.log ‖1-(x:ℂ)^2‖ - π*I)*(μ/2))*((2:ℂ)^(ν+1))⁻¹ ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (exp_ne_zero _) hπ32) (exp_ne_zero _))
        (inv_ne_zero h2ν)
    have hp := ((hPc.tendsto.comp hz_lim).mul_const ((2:ℂ)^μ)).div
      (tendsto_const_nhds.mul (hBPc.tendsto.comp hz_lim)) (mul_ne_zero hπ (hBP0 x))
    have hq := ((olverQ_analyticAt ν μ hx1).continuousAt.tendsto.comp hz_lim).div hK_lim hKl0
    refine ⟨_, _, (tendsto_const_nhds (x := B)).mul ((tendsto_const_nhds (x := I*q1)).mul hp
      |>.add ((tendsto_const_nhds (x := A)).mul hq)) |>.div (hz_lim.mul_const D)
        (mul_ne_zero hxne hD0), fun ε hε => ?_⟩
    have hz0 : z ε ≠ 0 := fun h => by have := hzim ε hε; rw [h] at this; simp at this
    have hKε : K ε ≠ 0 := by
      simp only [hK]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (exp_ne_zero _) hπ32) ?_) (inv_ne_zero h2ν)
      rw [cpow_def_of_ne_zero (hune ε hε)]; exact exp_ne_zero _
    have h1 := hBP0 (z ε)
    show F2 ε * B = B * (I*q1*(P (z ε)*2^μ/(π*BP (z ε))) + A*(olverQ ν μ (z ε)/K ε))/
      (z ε * D)
    rw [eq_div_iff (mul_ne_zero hz0 hD0), hP ε hε, hQ ε hε]
    field_simp
    simp only [hD]
    ring
  have hlim1 : Tendsto (fun ε => BP x / BP (z ε) * P (z ε)) (𝓝[>] (0:ℝ)) (𝓝 (P x)) := by
    have := (tendsto_const_nhds (x := BP x)).div (hBPc.tendsto.comp hz_lim) (hBP0 x)
      |>.mul (hPc.tendsto.comp hz_lim)
    rwa [div_self (hBP0 x), one_mul] at this
  have hlim2 : Tendsto (fun ε => π*BP x/2^μ*((z ε - x) * (F2 ε * B))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun ε => z ε - (x:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have := hz_lim.sub (tendsto_const_nhds (x := (x:ℂ)))
      rwa [sub_self] at this
    have := (tendsto_const_nhds (x := π*BP x/2^μ)).mul (h0.zero_mul_isBoundedUnder_le hb)
    rwa [mul_zero] at this
  refine ((hlim1.add hlim2).congr' ?_).trans (by rw [add_zero])
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0:ℝ) < ε := hε
  rw [hP ε hε']
  simp only [hF1, hF2, hA, hB, hu, hBP]
  have h1 := hBP0 (z ε)
  simp only [hBP] at h1
  field_simp
  ring

end DLMF.Legendre
