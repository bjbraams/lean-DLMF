/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.LogExpBasic
public import Mathlib.Analysis.Analytic.Binomial
public import DLMFMathlib.Analysis.SpecialFunctions.Complex.LogBoundary
public import DLMF.Core.Framework
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Logarithms, exponentials and powers: DLMF §§4.4–4.8

Exact special values, complex-parameter limits, inequalities, boundary-convergent
series, differential equations, and multivalued identities. Binomial series use Mathlib's
`Complex.one_add_cpow_hasFPowerSeriesOnBall_zero`; the coefficient adapter uses
Mathlib's descending Pochhammer polynomial and generalized binomial APIs. Decimal approximations
are omitted. The strict bounds in 4.5.3 and 4.5.14 require a strict endpoint; their
exact positive cutoffs are defined below and equality is retained there.
The additive constant printed in 4.7.13 is corrected to a multiplicative constant.
The independent-set interpretation of 4.8.5 is corrected by retaining all integer
logarithm shifts rather than only multiples of the exponent.
-/

@[expose] public section
open Complex Filter Set Finset Polynomial
open scoped Topology Real
noncomputable section
namespace DLMF.Elementary

/-- Both exact logarithm values at `-1`. -/
@[dlmf 4.4.E2]
theorem closedLogValues_neg_one  : closedLogValues (-1) = {Real.pi * I, -Real.pi * I} := by
  simpa using (closedLogValues_neg (x := -1) (by norm_num))

/-- The two exact sixth-root exponential values. -/
@[dlmf 4.4.E8]
theorem exp_pi_div_three (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Complex.exp (ε * Real.pi / 3 * I) = 1 / 2 + ε * I * (Real.sqrt 3 / 2) := by
  have he : (ε:ℂ)*Real.pi/3*I=((ε*Real.pi/3:ℝ):ℂ)*I := by push_cast; ring
  rw [he,Complex.exp_ofReal_mul_I]
  rcases hε with rfl|rfl <;>
    simp only [one_mul,neg_one_mul,neg_div,Real.cos_neg,Real.sin_neg,
      Real.cos_pi_div_three,Real.sin_pi_div_three] <;> push_cast <;> ring

/-- The two exact third-root exponential values. -/
@[dlmf 4.4.E9]
theorem exp_two_pi_div_three (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Complex.exp (ε * 2 * Real.pi / 3 * I) = -1 / 2 + ε * I * (Real.sqrt 3 / 2) := by
  have he : (ε:ℂ)*2*Real.pi/3*I=((ε*(Real.pi-Real.pi/3):ℝ):ℂ)*I := by push_cast; ring
  rw [he,Complex.exp_ofReal_mul_I]
  rcases hε with rfl|rfl <;>
    simp [Real.cos_sub,Real.sin_sub,Real.cos_pi_div_three,Real.sin_pi_div_three] <;> ring

/-- The two exact eighth-root exponential values. -/
@[dlmf 4.4.E10]
theorem exp_pi_div_four (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Complex.exp (ε * Real.pi / 4 * I) = 1 / (Real.sqrt 2 : ℂ) + ε * I / Real.sqrt 2 := by
  have hs : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hn : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)).ne'
  have hi : (1:ℂ)/(Real.sqrt 2:ℂ)=(Real.sqrt 2:ℂ)/2 := by
    field_simp
    linear_combination -hs
  have he : (ε:ℂ)*Real.pi/4*I=((ε*Real.pi/4:ℝ):ℂ)*I := by push_cast; ring
  rw [he,Complex.exp_ofReal_mul_I]
  rcases hε with rfl|rfl <;>
    simp only [one_mul,neg_one_mul,neg_div,Real.cos_neg,Real.sin_neg,
      Real.cos_pi_div_four,Real.sin_pi_div_four] <;> push_cast <;>
    simp only [div_eq_mul_inv,show (Real.sqrt 2:ℂ)⁻¹=(Real.sqrt 2:ℂ)/2 by simpa only [one_div] using hi] <;> ring

/-- The two exact remaining eighth-root exponential values. -/
@[dlmf 4.4.E11]
theorem exp_three_pi_div_four (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Complex.exp (ε * 3 * Real.pi / 4 * I) = -1 / (Real.sqrt 2 : ℂ) + ε * I / Real.sqrt 2 := by
  have hs : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hn : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)).ne'
  have hi : (1:ℂ)/(Real.sqrt 2:ℂ)=(Real.sqrt 2:ℂ)/2 := by
    field_simp
    linear_combination -hs
  have he : (ε:ℂ)*3*Real.pi/4*I=((ε*(Real.pi-Real.pi/4):ℝ):ℂ)*I := by push_cast; ring
  rw [he,Complex.exp_ofReal_mul_I]
  rcases hε with rfl|rfl <;>
    simp only [one_mul,neg_one_mul,Real.cos_neg,Real.sin_neg,Real.cos_sub,Real.sin_sub,
      Real.cos_pi,Real.sin_pi,mul_zero,mul_one,zero_mul,one_mul,zero_sub,sub_zero,
      Real.cos_pi_div_four,Real.sin_pi_div_four] <;> push_cast <;>
    simp only [div_eq_mul_inv,show (Real.sqrt 2:ℂ)⁻¹=(Real.sqrt 2:ℂ)/2 by simpa only [one_div] using hi] <;> ring

/-- The principal imaginary powers of `I`. -/
@[dlmf 4.4.E12]
theorem I_cpow_I (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    I ^ (ε * I) = (Real.exp (-ε * Real.pi / 2) : ℂ) := by
  rw [Complex.cpow_def_of_ne_zero Complex.I_ne_zero,Complex.log_I]
  have he : (Real.pi/2*I)*(ε*I)=((-ε*Real.pi/2:ℝ):ℂ) := by
    push_cast
    linear_combination (Real.pi/2*ε:ℂ)*Complex.I_mul_I
  rw [he,Complex.ofReal_exp]

/-- Logarithmic growth is smaller than every power with positive real part. -/
@[dlmf 4.4.E13]
theorem tendsto_cpow_neg_mul_log {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ (-a) * Real.log x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := ((isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero).norm
  simp only [norm_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  simp only [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx,Complex.neg_re,
    Real.rpow_neg hx.le,abs_of_pos (Real.rpow_pos_of_pos hx _)]
  ring

/-- Complex positive-real-part powers suppress the logarithm at zero. -/
@[dlmf 4.4.E14]
theorem tendsto_cpow_mul_log_zero {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ a * Real.log x) (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (tendsto_log_mul_rpow_nhdsGT_zero ha).norm
  simp only [norm_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx,abs_of_pos (Real.rpow_pos_of_pos hx _)]
  ring

/-- Real-axis exponential decay for every complex power. -/
@[dlmf 4.4.E15]
theorem tendsto_cpow_mul_exp_neg (a : ℂ) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ a * Complex.exp (-x)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a.re 1 (by norm_num)
  simp only [neg_mul,one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx,Complex.norm_exp]
  simp

/-- Uniform exponential decay in each closed proper right half-sector. -/
@[dlmf 4.4.E16]
theorem tendsto_cpow_mul_exp_neg_sector (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ Real.pi / 2) :
    Tendsto (fun z : ℂ => z ^ a * Complex.exp (-z))
      (DLMF.sector (Real.pi / 2 - δ)) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsd : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  set K := Real.exp (Real.pi * |a.im|) with hK
  have hg : Tendsto (fun r : ℝ => K * (r ^ a.re * Real.exp (-Real.sin δ * r))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a.re (Real.sin δ) hsd).const_mul K
  have hg' : Tendsto (fun z : ℂ => K * (‖z‖ ^ a.re * Real.exp (-Real.sin δ * ‖z‖)))
      (DLMF.sector (Real.pi / 2 - δ)) (𝓝 0) :=
    (hg.comp (tendsto_comap (f := fun z : ℂ => ‖z‖))).mono_left inf_le_left
  apply squeeze_zero' (Eventually.of_forall fun z => norm_nonneg _) _ hg'
  have hmem : {z : ℂ | z ≠ 0 ∧ |arg z| ≤ Real.pi / 2 - δ} ∈ DLMF.sector (Real.pi / 2 - δ) :=
    mem_inf_of_right (mem_principal_self _)
  filter_upwards [hmem] with z ⟨hz0, harg⟩
  rw [norm_mul, Complex.norm_cpow_of_ne_zero hz0, Complex.norm_exp, Complex.neg_re]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have h1 : (Real.exp (arg z * a.im))⁻¹ ≤ K := by
    rw [← Real.exp_neg, hK, Real.exp_le_exp]
    have : |arg z * a.im| ≤ Real.pi * |a.im| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right ((Complex.abs_arg_le_pi z)) (abs_nonneg _)
    linarith [neg_abs_le (arg z * a.im)]
  have h2 : Real.exp (-z.re) ≤ Real.exp (-Real.sin δ * ‖z‖) := by
    rw [Real.exp_le_exp]
    have hc : Real.sin δ ≤ Real.cos (arg z) := by
      rw [← Real.cos_pi_div_two_sub, ← Real.cos_abs (arg z)]
      apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) harg
    rw [Complex.cos_arg hz0, le_div_iff₀ hn] at hc
    linarith
  rw [div_eq_mul_inv]
  calc ‖z‖ ^ a.re * (Real.exp (arg z * a.im))⁻¹ * Real.exp (-z.re)
      ≤ ‖z‖ ^ a.re * K * Real.exp (-Real.sin δ * ‖z‖) := by
        gcongr
    _ = K * (‖z‖ ^ a.re * Real.exp (-Real.sin δ * ‖z‖)) := by ring

/-- Exact positive cutoff for the logarithm inequality, without a decimal approximation. -/
def logInequalityCutoff : ℝ := sSup {x : ℝ | 0 < x ∧ x < 1 ∧ -Real.log (1 - x) ≤ 3 * x / 2}

/-- Members of the logarithm cutoff set lie below `9/10`. -/
lemma logR4_mem_le {x : ℝ} (hx : x ∈ {x : ℝ | 0 < x ∧ x < 1 ∧ -Real.log (1 - x) ≤ 3 * x / 2}) :
    x ≤ 9/10 := by
  obtain ⟨h0, h1, h2⟩ := hx
  by_contra h
  push Not at h
  have hl : Real.log (1 - x) < Real.log (1/10) := Real.log_lt_log (by linarith) (by linarith)
  have h10 : Real.log (1/10) = - Real.log 10 := by rw [one_div, Real.log_inv]
  have h8 : 3 * Real.log 2 < Real.log 10 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  have := Real.log_two_gt_d9
  linarith

/-- The logarithm cutoff set is bounded above. -/
lemma logR4_bdd : BddAbove {x : ℝ | 0 < x ∧ x < 1 ∧ -Real.log (1 - x) ≤ 3 * x / 2} :=
  ⟨9/10, fun _ hx => logR4_mem_le hx⟩

/-- One half belongs to the logarithm cutoff set. -/
lemma logR4_half_mem : (1/2:ℝ) ∈ {x : ℝ | 0 < x ∧ x < 1 ∧ -Real.log (1 - x) ≤ 3 * x / 2} := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [show (1:ℝ) - 1/2 = (2:ℝ)⁻¹ by norm_num, Real.log_inv, neg_neg]
  have := Real.log_two_lt_d9
  linarith

/-- Convexity bound: below a member of the cutoff set the strict inequality holds. -/
lemma logR4_strict {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hy : y ∈ {x : ℝ | 0 < x ∧ x < 1 ∧ -Real.log (1 - x) ≤ 3 * x / 2}) :
    -Real.log (1 - x) < 3 * x / 2 := by
  obtain ⟨hy0, hy1, hy2⟩ := hy
  set t := x / y with ht
  have ht0 : 0 < t := div_pos hx hy0
  have ht1 : t < 1 := (div_lt_one hy0).mpr hxy
  have hc := strictConcaveOn_log_Ioi.2 (show 1 - y ∈ Ioi (0:ℝ) by simp; linarith)
    (show (1:ℝ) ∈ Ioi (0:ℝ) by simp) (by linarith) ht0 (show 0 < 1 - t by linarith) (by ring)
  have he : t • (1 - y) + (1 - t) • (1:ℝ) = 1 - x := by
    simp only [smul_eq_mul, ht]; field_simp; ring
  rw [he] at hc
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hc
  have : t * (3 * y / 2) = 3 * x / 2 := by rw [ht]; field_simp
  nlinarith

/-- The logarithm cutoff is at least one half. -/
lemma logR4_cutoff_pos : 1/2 ≤ logInequalityCutoff := le_csSup logR4_bdd logR4_half_mem

/-- The cutoff is the nonzero root of the equality case. -/
theorem logInequalityCutoff_spec  :
    0 < logInequalityCutoff ∧ logInequalityCutoff < 1 ∧
    -Real.log (1 - logInequalityCutoff) = 3 * logInequalityCutoff / 2 := by
  have hc0 := logR4_cutoff_pos
  have hc9 : logInequalityCutoff ≤ 9/10 := csSup_le ⟨_, logR4_half_mem⟩ (fun _ hx => logR4_mem_le hx)
  set c := logInequalityCutoff with hcdef
  have hcont : ContinuousOn (fun x : ℝ => -Real.log (1 - x) - 3 * x / 2) (Icc 0 (9/10)) := by
    apply ContinuousOn.sub _ (by fun_prop)
    apply ContinuousOn.neg
    apply ContinuousOn.log (by fun_prop)
    intro x hx; simp at hx; linarith [hx.2]
  refine ⟨by linarith, by linarith, ?_⟩
  apply le_antisymm
  · -- closure: c is a limit of members
    have hT : IsClosed {x ∈ Icc (0:ℝ) (9/10) | -Real.log (1 - x) - 3 * x / 2 ≤ 0} :=
      hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hsub : {x : ℝ | 0 < x ∧ x < 1 ∧ -Real.log (1 - x) ≤ 3 * x / 2} ⊆
        {x ∈ Icc (0:ℝ) (9/10) | -Real.log (1 - x) - 3 * x / 2 ≤ 0} := by
      intro x hx
      exact ⟨⟨hx.1.le, logR4_mem_le hx⟩, by linarith [hx.2.2]⟩
    have hcl : c ∈ closure {x : ℝ | 0 < x ∧ x < 1 ∧ -Real.log (1 - x) ≤ 3 * x / 2} :=
      csSup_mem_closure ⟨_, logR4_half_mem⟩ logR4_bdd
    have hmem := hT.closure_subset_iff.mpr hsub hcl
    have := hmem.2
    linarith
  · by_contra hlt
    push Not at hlt
    -- f(c) < 0, so slightly larger points are members
    have hca : ContinuousAt (fun x : ℝ => -Real.log (1 - x) - 3 * x / 2) c := by
      apply ContinuousAt.sub _ (by fun_prop)
      apply ContinuousAt.neg
      apply ContinuousAt.log (by fun_prop)
      linarith
    have hev : ∀ᶠ x in 𝓝 c, -Real.log (1 - x) - 3 * x / 2 < 0 ∧ x < 1 :=
      (hca.eventually (gt_mem_nhds (show -Real.log (1 - c) - 3 * c / 2 < 0 by linarith))).and (gt_mem_nhds (show c < 1 by linarith))
    obtain ⟨x, ⟨hx1, hx2⟩, hcx⟩ :=
      ((hev.filter_mono (nhdsWithin_le_nhds (s := Ioi c))).and self_mem_nhdsWithin).exists
    have hxS : x ∈ {x : ℝ | 0 < x ∧ x < 1 ∧ -Real.log (1 - x) ≤ 3 * x / 2} :=
      ⟨by linarith [hcx], hx2, by linarith⟩
    have : x ≤ c := le_csSup logR4_bdd hxS
    linarith [hcx]

/-- Both sharp first-order logarithmic inequalities. -/
@[dlmf 4.5.E1]
theorem log_one_add_bounds {x : ℝ} (hx : -1 < x) (hne : x ≠ 0) :
    x / (1 + x) < Real.log (1 + x) ∧ Real.log (1 + x) < x := by
  have hp : 0 < 1+x := by linarith
  have hn : 1+x ≠ 1 := by intro h; apply hne; linarith
  have hu := Real.log_lt_sub_one_of_pos hp hn
  have hl := Real.log_lt_sub_one_of_pos (inv_pos.mpr hp) (inv_ne_one.mpr hn)
  rw [Real.log_inv] at hl
  have he : x/(1+x) = 1-(1+x)⁻¹ := by field_simp; ring
  constructor
  · rw [he]; linarith
  · linarith

/-- The equivalent logarithmic inequalities below one. -/
@[dlmf 4.5.E2]
theorem neg_log_one_sub_bounds {x : ℝ} (hx : x < 1) (hne : x ≠ 0) :
    x < -Real.log (1 - x) ∧ -Real.log (1 - x) < x / (1 - x) := by
  have h := log_one_add_bounds (x := -x) (by linarith) (neg_ne_zero.mpr hne)
  have he : (-x)/(1-x) = -(x/(1-x)) := by ring
  rw [show 1+-x=1-x by ring] at h
  rw [he] at h
  constructor <;> linarith

/-- Strict form inside the exact cutoff; the printed closed endpoint has equality. -/
@[dlmf 4.5.E3]
theorem abs_log_one_sub_lt {x : ℝ} (hx : 0 < x) (hr : x < logInequalityCutoff) :
    |Real.log (1 - x)| < 3 * x / 2 := by
  obtain ⟨y, hy, hxy⟩ := exists_lt_of_lt_csSup ⟨_, logR4_half_mem⟩ hr
  have h := logR4_strict hx hxy hy
  have hx1 : x < 1 := lt_trans hxy hy.2.1
  have hl : Real.log (1 - x) < 0 := Real.log_neg (by linarith) (by linarith)
  rw [abs_of_neg hl]
  exact h

/-- Weak form through the exact cutoff. -/
@[dlmf 4.5.E3]
theorem abs_log_one_sub_le {x : ℝ} (hx : 0 < x) (hr : x ≤ logInequalityCutoff) :
    |Real.log (1 - x)| ≤ 3 * x / 2 := by
  rcases hr.lt_or_eq with hr | rfl
  · obtain ⟨y, hy, hxy⟩ := exists_lt_of_lt_csSup ⟨_, logR4_half_mem⟩ hr
    have h := logR4_strict hx hxy hy
    have hx1 : x < 1 := lt_trans hxy hy.2.1
    have hl : Real.log (1 - x) < 0 := Real.log_neg (by linarith) (by linarith)
    rw [abs_of_neg hl]
    exact h.le
  · obtain ⟨h0, h1, h2⟩ := logInequalityCutoff_spec
    have hl : Real.log (1 - logInequalityCutoff) < 0 := Real.log_neg (by linarith) (by linarith)
    rw [abs_of_neg hl]
    linarith

/-- The positive-parameter power bound for the logarithm. -/
@[dlmf 4.5.E5]
theorem log_le_rpow_sub_one {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    Real.log x ≤ a * (x ^ (1 / a) - 1) := by
  have hy : 0 < x^(1/a) := Real.rpow_pos_of_pos hx _
  have h := Real.log_le_sub_one_of_pos hy
  rw [Real.log_rpow hx] at h
  have ha0 : a≠0 := ne_of_gt ha
  have hm := mul_le_mul_of_nonneg_left h ha.le
  convert hm using 1 <;> field_simp

/-- The complex logarithm bound with full unit-disk range. -/
@[dlmf 4.5.E6]
theorem norm_log_one_add_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖Complex.log (1 + z)‖ ≤ -Real.log (1 - ‖z‖) := by
  have hr : ‖(‖z‖:ℂ)‖<1 := by simpa using hz
  have hs := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hr)
  have hn : HasSum (fun n : ℕ => ‖(-1:ℂ)^(n+1)*z^n/n‖) (-Real.log (1-‖z‖)) := by
    convert hs using 1
    · ext n
      simp only [norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_natCast]
      rw [← Complex.ofReal_pow,← Complex.ofReal_natCast,← Complex.ofReal_div,Complex.ofReal_re]
    · simp only [Complex.neg_re,Complex.log_re]
      rw [show (1:ℂ)-(‖z‖:ℂ)=((1-‖z‖:ℝ):ℂ) by push_cast; rfl,
        Complex.norm_of_nonneg (sub_pos.mpr hz).le]
  rw [← (Complex.hasSum_taylorSeries_log hz).tsum_eq]
  exact (norm_tsum_le_tsum_norm hn.summable).trans_eq hn.tsum_eq

/-- Exponential bounds for `1-x`. -/
@[dlmf 4.5.E7]
theorem exp_one_sub_bounds {x : ℝ} (hx : x < 1) (hne : x ≠ 0) :
    Real.exp (-x / (1 - x)) < 1 - x ∧ 1 - x < Real.exp (-x) := by
  have hp : 0 < 1-x := by linarith
  have h := neg_log_one_sub_bounds hx hne
  constructor
  · apply (Real.lt_log_iff_exp_lt hp).mp
    simpa only [neg_neg,neg_div] using neg_lt_neg h.2
  · apply (Real.log_lt_iff_lt_exp hp).mp
    linarith [h.1]

/-- The exponential upper bound below one. -/
@[dlmf 4.5.E9]
theorem exp_lt_one_div {x : ℝ} (hx : x < 1) (hne : x ≠ 0) : Real.exp x < 1 / (1 - x) := by
  have hp : 0 < 1-x := by linarith
  have hh := (log_one_add_bounds (x := -x) (by linarith) (neg_ne_zero.mpr hne)).2
  have hlog : x < Real.log ((1-x)⁻¹) := by rw [Real.log_inv]; simp only [sub_eq_add_neg] at *; linarith [hh]
  simpa only [one_div] using (Real.exp_lt_exp.mpr hlog).trans_eq (Real.exp_log (inv_pos.mpr hp))

/-- Bounds for `1-exp(-x)`. -/
@[dlmf 4.5.E10]
theorem one_sub_exp_neg_bounds {x : ℝ} (hx : -1 < x) (hne : x ≠ 0) :
    x / (1 + x) < 1 - Real.exp (-x) ∧ 1 - Real.exp (-x) < x := by
  have h := exp_lt_one_div (x := -x) (by linarith) (neg_ne_zero.mpr hne)
  have hp : 1+x≠0 := by linarith
  have he : x/(1+x)=1-1/(1+x) := by field_simp; ring
  constructor
  · rw [he]; simpa only [show 1- -x=1+x by ring] using (sub_lt_sub_left h 1)
  · linarith [Real.add_one_lt_exp (neg_ne_zero.mpr hne)]

/-- Bounds for `exp x-1`. -/
@[dlmf 4.5.E11]
theorem exp_sub_one_bounds {x : ℝ} (hx : x < 1) (hne : x ≠ 0) :
    x < Real.exp x - 1 ∧ Real.exp x - 1 < x / (1 - x) := by
  have he : 1/(1-x)-1=x/(1-x) := by field_simp; ring
  constructor
  · linarith [Real.add_one_lt_exp hne]
  · rw [← he]; exact sub_lt_sub_right (exp_lt_one_div hx hne) 1

/-- Exponential lower approximation to `1+x`. -/
@[dlmf 4.5.E12]
theorem exp_div_one_add_lt {x : ℝ} (hx : -1 < x) (hne : x ≠ 0) : Real.exp (x / (1 + x)) < 1 + x := by
  exact (Real.lt_log_iff_exp_lt (by linarith : 0<1+x)).mp
    (log_one_add_bounds hx hne).1

/-- Two-parameter exponential bounds, with both parameters positive. -/
@[dlmf 4.5.E13]
theorem rpow_one_add_bounds {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.exp (x * y / (x + y)) < (1 + x / y) ^ y ∧
    (1 + x / y) ^ y < Real.exp x := by
  have hu : 0 < x/y := div_pos hx hy
  have h := log_one_add_bounds (x := x/y) (by linarith) (ne_of_gt hu)
  have he : y*(x/y/(1+x/y))=x*y/(x+y) := by
    field_simp
    <;> ring
  have hleft : x*y/(x+y)<y*Real.log (1+x/y) := by
    rw [← he]; exact mul_lt_mul_of_pos_left h.1 hy
  have hright : y*Real.log (1+x/y)<x := by
    convert mul_lt_mul_of_pos_left h.2 hy using 1 <;> field_simp
  rw [Real.rpow_def_of_pos (by linarith : 0<1+x/y)]
  constructor <;> apply Real.exp_lt_exp.mpr <;> nlinarith

/-- Exact nonzero cutoff for the linear exponential upper bound. -/
def expInequalityCutoff : ℝ := sSup {x : ℝ | 0 < x ∧ Real.exp (-x) ≤ 1 - x / 2}

/-- Members of the exponential cutoff set lie below two. -/
lemma logR4_exp_mem_lt {x : ℝ} (hx : x ∈ {x : ℝ | 0 < x ∧ Real.exp (-x) ≤ 1 - x / 2}) :
    x < 2 := by
  have := Real.exp_pos (-x)
  linarith [hx.2]

/-- The exponential cutoff set is bounded above. -/
lemma logR4_exp_bdd : BddAbove {x : ℝ | 0 < x ∧ Real.exp (-x) ≤ 1 - x / 2} :=
  ⟨2, fun _ hx => (logR4_exp_mem_lt hx).le⟩

/-- One belongs to the exponential cutoff set. -/
lemma logR4_exp_one_mem : (1:ℝ) ∈ {x : ℝ | 0 < x ∧ Real.exp (-x) ≤ 1 - x / 2} := by
  refine ⟨by norm_num, ?_⟩
  rw [Real.exp_neg]
  have := Real.exp_one_gt_d9
  rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
  linarith

/-- Convexity bound below a member of the exponential cutoff set. -/
lemma logR4_exp_strict {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hy : y ∈ {x : ℝ | 0 < x ∧ Real.exp (-x) ≤ 1 - x / 2}) :
    Real.exp (-x) < 1 - x / 2 := by
  obtain ⟨hy0, hy2⟩ := hy
  set t := x / y with ht
  have ht0 : 0 < t := div_pos hx hy0
  have ht1 : t < 1 := (div_lt_one hy0).mpr hxy
  have hc := strictConvexOn_exp.2 (mem_univ (-y)) (mem_univ (0:ℝ)) (by linarith) ht0
    (show 0 < 1 - t by linarith) (by ring)
  have he : t • (-y) + (1 - t) • (0:ℝ) = -x := by
    simp only [smul_eq_mul, ht, mul_zero, add_zero]; field_simp
  rw [he] at hc
  simp only [smul_eq_mul, Real.exp_zero, mul_one] at hc
  have : t * (1 - y / 2) + (1 - t) = 1 - x / 2 := by rw [ht]; field_simp; ring
  nlinarith

/-- The exponential cutoff and its exact equality case. -/
theorem expInequalityCutoff_spec  :
    0 < expInequalityCutoff ∧ expInequalityCutoff < 2 ∧
    Real.exp (-expInequalityCutoff) = 1 - expInequalityCutoff / 2 := by
  have hc1 : 1 ≤ expInequalityCutoff := le_csSup logR4_exp_bdd logR4_exp_one_mem
  have hc2 : expInequalityCutoff ≤ 2 :=
    csSup_le ⟨_, logR4_exp_one_mem⟩ (fun _ hx => (logR4_exp_mem_lt hx).le)
  set c := expInequalityCutoff with hcdef
  have hle : Real.exp (-c) - 1 + c / 2 ≤ 0 := by
    have hT : IsClosed {x : ℝ | x ∈ Icc (0:ℝ) 2 ∧ Real.exp (-x) - 1 + x / 2 ≤ 0} :=
      (by fun_prop : Continuous fun x : ℝ => Real.exp (-x) - 1 + x / 2).continuousOn.preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_Iic
    have hsub : {x : ℝ | 0 < x ∧ Real.exp (-x) ≤ 1 - x / 2} ⊆
        {x : ℝ | x ∈ Icc (0:ℝ) 2 ∧ Real.exp (-x) - 1 + x / 2 ≤ 0} := by
      intro x hx
      exact ⟨⟨hx.1.le, (logR4_exp_mem_lt hx).le⟩, by linarith [hx.2]⟩
    have hcl : c ∈ closure {x : ℝ | 0 < x ∧ Real.exp (-x) ≤ 1 - x / 2} :=
      csSup_mem_closure ⟨_, logR4_exp_one_mem⟩ logR4_exp_bdd
    exact (hT.closure_subset_iff.mpr hsub hcl).2
  have hlt2 : c < 2 := by
    rcases hc2.lt_or_eq with h | h
    · exact h
    · rw [h] at hle; have := Real.exp_pos (-2); linarith
  refine ⟨by linarith, hlt2, ?_⟩
  apply le_antisymm (by linarith)
  by_contra hlt
  push Not at hlt
  have hca : ContinuousAt (fun x : ℝ => Real.exp (-x) - 1 + x / 2) c := by fun_prop
  have hev : ∀ᶠ x in 𝓝 c, Real.exp (-x) - 1 + x / 2 < 0 :=
    hca.eventually (gt_mem_nhds (show Real.exp (-c) - 1 + c / 2 < 0 by linarith))
  obtain ⟨x, hx1, hcx⟩ :=
    ((hev.filter_mono (nhdsWithin_le_nhds (s := Ioi c))).and self_mem_nhdsWithin).exists
  have hxS : x ∈ {x : ℝ | 0 < x ∧ Real.exp (-x) ≤ 1 - x / 2} :=
    ⟨by linarith [show c < x from hcx], by linarith⟩
  have : x ≤ c := le_csSup logR4_exp_bdd hxS
  linarith [show c < x from hcx]

/-- Strict form inside the exact cutoff. -/
@[dlmf 4.5.E14]
theorem exp_neg_lt_linear {x : ℝ} (hx : 0 < x) (hr : x < expInequalityCutoff) :
    Real.exp (-x) < 1 - x / 2 := by
  obtain ⟨y, hy, hxy⟩ := exists_lt_of_lt_csSup ⟨_, logR4_exp_one_mem⟩ hr
  exact logR4_exp_strict hx hxy hy

/-- Weak form through the exact cutoff. -/
@[dlmf 4.5.E14]
theorem exp_neg_le_linear {x : ℝ} (hx : 0 < x) (hr : x ≤ expInequalityCutoff) :
    Real.exp (-x) ≤ 1 - x / 2 := by
  rcases hr.lt_or_eq with hr | rfl
  · obtain ⟨y, hy, hxy⟩ := exists_lt_of_lt_csSup ⟨_, logR4_exp_one_mem⟩ hr
    exact (logR4_exp_strict hx hxy hy).le
  · exact expInequalityCutoff_spec.2.2.le

/-- Two-sided complex exponential estimate on the punctured unit disk. -/
@[dlmf 4.5.E15]
theorem norm_exp_sub_one_bounds {z : ℂ} (hz : 0 < ‖z‖) (hz1 : ‖z‖ < 1) :
    ‖z‖ / 4 < ‖Complex.exp z - 1‖ ∧ ‖Complex.exp z - 1‖ < 7 * ‖z‖ / 4 := by
  have he := Complex.exp_bound hz1.le (n := 3) (by norm_num)
  have hsum : (∑ m∈range 3,z^m/(m.factorial:ℂ))=1+z+z^2/2 := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at he
  have hR : ‖Complex.exp z-1-z-z^2/2‖≤‖z‖^3*(2/9) := by
    convert he using 1
    · congr 1; ring
    · norm_num
  have h3 : ‖z‖^3<‖z‖ := by nlinarith [sq_nonneg ‖z‖,mul_pos hz (sub_pos.mpr hz1)]
  have h2 : ‖z‖^2<‖z‖ := by nlinarith
  have hs := norm_add_le (Complex.exp z-1-z-z^2/2) (z^2/2)
  rw [show (Complex.exp z-1-z-z^2/2)+(z^2/2)=Complex.exp z-1-z by ring] at hs
  have hn : ‖z^2/2‖=‖z‖^2/2 := by norm_num [norm_div,norm_pow]
  rw [hn] at hs
  have hsmall : ‖Complex.exp z-1-z‖<3*‖z‖/4 := by nlinarith
  have hu : ‖Complex.exp z-1‖≤‖Complex.exp z-1-z‖+‖z‖ := by
    simpa using norm_add_le (Complex.exp z-1-z) z
  have hl := norm_sub_norm_le z (Complex.exp z-1)
  rw [show ‖z-(Complex.exp z-1)‖=‖Complex.exp z-1-z‖ from norm_sub_rev _ _] at hl
  constructor <;> nlinarith

/-- Global complex exponential estimate. -/
@[dlmf 4.5.E16]
theorem norm_exp_sub_one_le (z : ℂ) :
    ‖Complex.exp z - 1‖ ≤ Real.exp ‖z‖ - 1 ∧
    Real.exp ‖z‖ - 1 ≤ ‖z‖ * Real.exp ‖z‖ := by
  constructor
  · simpa using Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z 1
  · have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-‖z‖)) (Real.exp_pos ‖z‖).le
    rw [← Real.exp_add] at h
    simp only [neg_add_cancel,Real.exp_zero] at h
    nlinarith

/-- Logarithm Taylor series with all convergent boundary points. -/
@[dlmf 4.6.E1]
theorem log_one_add_hasSum_closed {z : ℂ} (hz : ‖z‖ ≤ 1) (hne : z ≠ -1) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, (-1 : ℂ) ^ n * z ^ (n + 1) / (n + 1))
      atTop (𝓝 (Complex.log (1 + z))) := by
  convert Complex.tendsto_logTaylor_closed hz hne using 1
  funext N
  unfold Complex.logTaylor
  rw [Finset.sum_range_succ']
  simp [pow_add]

/-- Natural-order positive logarithm series on the closed disk, excluding its pole. -/
theorem logBoundary_one_sub {w : ℂ} (hw : ‖w‖ ≤ 1) (hne : w ≠ 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, w ^ (n + 1) / (n + 1))
      atTop (𝓝 (-Complex.log (1 - w))) := by
  have hn : -w ≠ (-1 : ℂ) := by simpa using hne
  have h := (log_one_add_hasSum_closed (z := -w) (by simpa using hw) hn).neg
  convert h using 1
  · funext N
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [neg_pow, pow_succ]
    have hs : ((-1 : ℂ) ^ n) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul, neg_one_sq, one_pow]
    have hd : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp
    linear_combination -(w ^ (n + 1)) * hs

/-- The real part of a translated closed-disk point is positive off its endpoint. -/
theorem logBoundary_one_add_re_pos {w : ℂ} (hw : ‖w‖ ≤ 1) (hne : w ≠ -1) :
    0 < (1 + w).re := by
  have hs := Complex.sq_norm w
  rw [Complex.normSq_apply] at hs
  have hr := (abs_le.mp (Complex.abs_re_le_norm w)).1
  by_contra hbad
  have he : w.re = -1 := by simp only [Complex.add_re, Complex.one_re] at hbad; linarith
  have hi : w.im = 0 := by nlinarith [sq_nonneg w.im, norm_nonneg w]
  apply hne
  exact Complex.ext (by simpa using he) (by simpa using hi)

/-- The principal logarithm quotient law for two points with positive real part. -/
theorem logBoundary_log_div {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    Complex.log (u / v) = Complex.log u - Complex.log v := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hua := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu))
  have hva := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hv))
  have he : Complex.exp (Complex.log u - Complex.log v) = u / v := by
    rw [Complex.exp_sub, Complex.exp_log hu0, Complex.exp_log hv0]
  rw [← he]
  apply Complex.log_exp
  · simp only [Complex.sub_im, Complex.log_im]
    linarith
  · simp only [Complex.sub_im, Complex.log_im]
    linarith

/-- Odd logarithm series on the whole closed disk except the two divergent endpoints.
The finite identity groups adjacent natural-order terms before taking an even subsequence. -/
theorem logBoundary_odd {w : ℂ} (hw : ‖w‖ ≤ 1) (hp : w ≠ 1) (hm : w ≠ -1) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, 2 * w ^ (2 * n + 1) / (2 * n + 1))
      atTop (𝓝 (Complex.log ((1 + w) / (1 - w)))) := by
  have hplus := log_one_add_hasSum_closed hw hm
  have hminus := logBoundary_one_sub hw hp
  let F : ℕ → ℂ := fun n => w ^ (n + 1) / (n + 1) +
    (-1 : ℂ) ^ n * w ^ (n + 1) / (n + 1)
  have hfinite (N : ℕ) : (∑ n ∈ range N, 2 * w ^ (2 * n + 1) / (2 * n + 1)) =
      ∑ n ∈ range (2 * N), F n := by
    induction N with
    | zero => simp
    | succ N ih =>
      have hidx : 2 * (N + 1) = 2 * N + 1 + 1 := by omega
      rw [Finset.sum_range_succ, ih, hidx, Finset.sum_range_succ, Finset.sum_range_succ]
      simp [F, pow_add, pow_mul]
      ring
  have hsub : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (fun N => by dsimp only [id]; omega) tendsto_id
  have h := (hminus.add hplus).comp hsub
  simp only [← Finset.sum_add_distrib] at h
  have he : -Complex.log (1 - w) + Complex.log (1 + w) =
      Complex.log ((1 + w) / (1 - w)) := by
    rw [logBoundary_log_div (logBoundary_one_add_re_pos hw hm)
      (by simpa only [sub_eq_add_neg] using
        logBoundary_one_add_re_pos (w := -w) (by simpa using hw) (by simpa using hp))]
    ring
  rw [he] at h
  exact h.congr (fun N => (hfinite N).symm)

/-- The reciprocal-transformed logarithm series, including the boundary line. -/
@[dlmf 4.6.E2]
theorem log_hasSum_halfplane {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, ((z - 1) / z) ^ (n + 1) / (n + 1))
      atTop (𝓝 (Complex.log z)) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz; linarith
  have hn : ‖(z - 1) / z‖ ≤ 1 := by
    rw [norm_div, div_le_one₀ (norm_pos_iff.mpr hz0)]
    have h₁ := Complex.sq_norm (z - 1)
    have h₂ := Complex.sq_norm z
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, sub_zero] at h₁ h₂
    nlinarith [norm_nonneg (z - 1), norm_nonneg z]
  have hne : (z - 1) / z ≠ 1 := by
    intro h
    have h' := (div_eq_iff hz0).mp h
    apply (one_ne_zero : (1 : ℂ) ≠ 0)
    linear_combination -h'
  have h := logBoundary_one_sub hn hne
  have he : 1 - (z - 1) / z = z⁻¹ := by field_simp; ring
  have harg : z.arg ≠ Real.pi := Complex.slitPlane_arg_ne_pi (by
    change 0 < z.re ∨ z.im ≠ 0
    left
    linarith)
  rw [he, Complex.log_inv z harg, neg_neg] at h
  exact h

/-- The logarithm Taylor series about one with its full boundary. -/
@[dlmf 4.6.E3]
theorem log_hasSum_center_one {z : ℂ} (hz : ‖z - 1‖ ≤ 1) (hne : z ≠ 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, (-1 : ℂ) ^ n * (z - 1) ^ (n + 1) / (n + 1))
      atTop (𝓝 (Complex.log z)) := by
  have hn : z - 1 ≠ (-1 : ℂ) := by
    intro h
    apply hne
    linear_combination h
  have h := log_one_add_hasSum_closed hz hn
  rwa [show 1 + (z - 1) = z by ring] at h

/-- The odd Cayley-transform series, including the imaginary-axis boundary. -/
@[dlmf 4.6.E4]
theorem log_hasSum_odd {z : ℂ} (hz : 0 ≤ z.re) (hne : z ≠ 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, 2 * ((z - 1) / (z + 1)) ^ (2 * n + 1) / (2 * n + 1))
      atTop (𝓝 (Complex.log z)) := by
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hr
    linarith
  have hn : ‖(z - 1) / (z + 1)‖ ≤ 1 := by
    rw [norm_div, div_le_one₀ (norm_pos_iff.mpr hz1)]
    have h₁ := Complex.sq_norm (z - 1)
    have h₂ := Complex.sq_norm (z + 1)
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, sub_zero, add_zero] at h₁ h₂
    nlinarith [norm_nonneg (z - 1), norm_nonneg (z + 1)]
  have hp : (z - 1) / (z + 1) ≠ 1 := by
    intro h
    have he := (div_eq_iff hz1).mp h
    apply (one_ne_zero : (1 : ℂ) ≠ 0)
    linear_combination -he / 2
  have hm : (z - 1) / (z + 1) ≠ -1 := by
    intro h
    have he := (div_eq_iff hz1).mp h
    apply hne
    linear_combination he / 2
  have h := logBoundary_odd hn hp hm
  have he : (1 + (z - 1) / (z + 1)) / (1 - (z - 1) / (z + 1)) = z := by
    field_simp
    ring
  rwa [he] at h

/-- The reciprocal odd series, including all admissible unit-circle points. -/
@[dlmf 4.6.E5]
theorem log_ratio_hasSum_odd {z : ℂ} (hz : 1 ≤ ‖z‖) (hp : z ≠ 1) (hm : z ≠ -1) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, 2 / ((2 * n + 1 : ℂ) * z ^ (2 * n + 1)))
      atTop (𝓝 (Complex.log ((z + 1) / (z - 1)))) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz; linarith
  have hn : ‖z⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (norm_pos_iff.mpr hz0)).2 hz
  have hp' : z⁻¹ ≠ 1 := by
    intro h
    apply hp
    simpa using congrArg (fun w : ℂ => w⁻¹) h
  have hm' : z⁻¹ ≠ -1 := by
    intro h
    apply hm
    simpa using congrArg (fun w : ℂ => w⁻¹) h
  have h := logBoundary_odd hn hp' hm'
  have he : (1 + z⁻¹) / (1 - z⁻¹) = (z + 1) / (z - 1) := by
    field_simp
  rw [he] at h
  convert h using 1
  funext N
  apply Finset.sum_congr rfl
  intro n hn
  simp only [div_eq_mul_inv, mul_inv, inv_pow]
  ring

/-- The shifted odd logarithm series with a positive real shift. -/
@[dlmf 4.6.E6]
theorem log_add_hasSum_odd {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : -a ≤ z.re) (hne : z ≠ -a) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, 2 * (z / (2 * a + z)) ^ (2 * n + 1) / (2 * n + 1))
      atTop (𝓝 (Complex.log (z + a) - Complex.log a)) := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hza : z + a ≠ 0 := by
    intro h
    apply hne
    linear_combination h
  have hn : 0 ≤ ((z + a) / a).re := by
    have hsum : 0 ≤ z.re + a := by linarith
    simp only [Complex.div_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, Complex.normSq_ofReal]
    positivity
  have hne' : (z + a) / a ≠ 0 := div_ne_zero hza ha0
  have h := log_hasSum_odd hn hne'
  have hratio : (((z + a) / a) - 1) / (((z + a) / a) + 1) = z / (2 * a + z) := by
    field_simp
    ring
  have hlog : Complex.log ((z + a) / a) = Complex.log (z + a) - Complex.log a := by
    rw [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.log_mul_ofReal a⁻¹ (inv_pos.mpr ha) (z + a) hza,
      Real.log_inv, ← Complex.ofReal_log ha.le]
    push_cast
    ring
  simpa only [hratio, hlog] using h

/-- The complex falling factorial, including its empty product. -/
def fallingPower (a : ℂ) (n : ℕ) : ℂ := ∏ j ∈ range n, (a - j)

/-- Falling-factorial coefficients agree with Mathlib's generalized binomial coefficients. -/
theorem fallingPower_choose (a : ℂ) (n : ℕ) :
    fallingPower a n/(n.factorial:ℂ)=Ring.choose a n := by
  have he : fallingPower a n=(descPochhammer ℂ n).eval a := by
    rw [descPochhammer_eval_eq_prod_range]
    rfl
  rw [he,Ring.choose_eq_smul,Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_cast,Polynomial.ascPochhammer_smeval_eq_eval,
    descPochhammer_eval_eq_ascPochhammer]
  simp [smul_eq_mul,div_eq_mul_inv,mul_comm]

/-- The complex binomial series on its full open disk. -/
@[dlmf 4.6.E7]
theorem binomial_hasSum (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => fallingPower a n / n.factorial * z ^ n) ((1 + z) ^ a) := by
  have hs := Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := a) |>.hasSum
    (show z∈Metric.eball (0:ℂ) 1 by
      rw [← ENNReal.ofReal_one,Metric.eball_ofReal]
      simpa using hz)
  simpa [binomialSeries,FormalMultilinearSeries.ofScalars_apply_eq,fallingPower_choose,
    mul_comm] using hs

/-- Nonnegative integer exponents terminate and allow unrestricted arguments. -/
@[dlmf 4.6.E7]
theorem binomial_nat_hasSum (m : ℕ) (z : ℂ) :
    HasSum (fun n : ℕ => fallingPower (m : ℂ) n / n.factorial * z ^ n) ((1 + z) ^ m) := by
  have hc (n : ℕ) : fallingPower (m:ℂ) n/(n.factorial:ℂ)=(m.choose n:ℂ) := by
    simpa only [descPochhammer_eval_eq_prod_range,fallingPower] using
      (Nat.cast_choose_eq_descPochhammer_div (K := ℂ) m n).symm
  simp_rw [hc]
  have hs : (∑ n∈range (m+1),(m.choose n:ℂ)*z^n)=(1+z)^m := by
    simpa [mul_comm,mul_left_comm,one_pow,add_comm] using (add_pow z (1:ℂ) m).symm
  rw [← hs]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  have hm : m<n := by simpa using hn
  simp [Nat.choose_eq_zero_of_lt hm]

/-- Every logarithm sheet has the same derivative on the slit plane. -/
@[dlmf 4.7.E2]
theorem logSheet_hasDerivAt (k : ℤ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (logSheet k) z⁻¹ z := by
  change HasDerivAt (fun z => Complex.log z + k * (2 * Real.pi * I)) z⁻¹ z
  exact (Complex.hasDerivAt_log hz).add_const _

/-- Every logarithm sheet has the displayed derivatives of all positive orders. -/
@[dlmf 4.7.E4]
theorem iteratedDeriv_logSheet (k : ℤ) (n : ℕ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    iteratedDeriv (n + 1) (logSheet k) z =
      (-1 : ℂ) ^ n * n.factorial * z ^ (-(n : ℤ) - 1) := by
  have he : logSheet k = fun z => k*(2*Real.pi*I)+Complex.log z := by
    ext z; simp [logSheet,add_comm]
  rw [he,iteratedDeriv_const_add (Nat.succ_pos _) _]
  exact iteratedDeriv_succ_log hz

/-- General logarithmic ODE solution on a connected open domain with a selected analytic logarithm. -/
@[dlmf 4.7.E5, dlmf 4.7.E6]
theorem logarithmic_ode_solution {s : Set ℂ} (hs : IsOpen s) (hc : IsPreconnected s)
    (f f' L w : ℂ → ℂ)
    (hf : ∀ z ∈ s, HasDerivAt f (f' z) z)
    (hn : ∀ z ∈ s, f z ≠ 0)
    (hL : ∀ z ∈ s, Complex.exp (L z) = f z)
    (hLd : DifferentiableOn ℂ L s) :
    (∀ z ∈ s, HasDerivAt w (f' z / f z) z) ↔
      ∃ C : ℂ, ∀ z ∈ s, w z = L z + C := by
  have hLD (z : ℂ) (hz : z∈s) : HasDerivAt L (f' z/f z) z := by
    have hd := hLd.differentiableAt (hs.mem_nhds hz)
    have hloc : (fun z => Complex.exp (L z)) =ᶠ[𝓝 z] f := by
      filter_upwards [hs.mem_nhds hz] with z hz using hL z hz
    have heq := hd.hasDerivAt.cexp.unique ((hf z hz).congr_of_eventuallyEq hloc)
    have hmul : deriv L z=f' z/f z := by
      rw [hL z hz] at heq
      apply (eq_div_iff (hn z hz)).mpr
      simpa only [mul_comm] using heq
    simpa only [hmul] using hd.hasDerivAt
  constructor
  · intro hw
    exact hs.exists_eq_add_of_deriv_eq hc
      (fun z hz => (hw z hz).differentiableAt.differentiableWithinAt) hLd
      (fun z hz => by rw [(hw z hz).deriv,(hLD z hz).deriv])
  · rintro ⟨C,hC⟩ z hz
    have hloc : w =ᶠ[𝓝 z] (fun z => L z+C) := by
      filter_upwards [hs.mem_nhds hz] with z hz using hC z hz
    exact ((hLD z hz).add_const C).congr_of_eventuallyEq hloc


/-- Derivative of an exponential with an arbitrary complex slope. -/
@[dlmf 4.7.E8]
theorem exp_mul_hasDerivAt (a z : ℂ) : HasDerivAt (fun z : ℂ => Complex.exp (a * z))
    (a * Complex.exp (a * z)) z := by
  simpa only [Function.comp_def, id_eq, mul_one, one_mul, mul_comm] using
    (Complex.hasDerivAt_exp (a * z)).comp z ((hasDerivAt_id z).const_mul a)

/-- A general power uses the logarithm sheet from its definition. -/
@[dlmf 4.7.E9]
theorem powerSheet_hasDerivAt (a : ℂ) (k : ℤ) (z : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (z * logSheet k a))
      (Complex.exp (z * logSheet k a) * logSheet k a) z := by
  simpa only [Function.comp_def, id_eq, mul_one, one_mul, mul_comm] using
    (Complex.hasDerivAt_exp (z * logSheet k a)).comp z
      ((hasDerivAt_id z).mul_const (logSheet k a))

/-- All higher power derivatives retain the full complex exponent. -/
@[dlmf 4.7.E11]
theorem iteratedDeriv_cpow (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    iteratedDeriv n (fun z : ℂ => z ^ a) z = fallingPower a n * z ^ (a - n) := by
  induction n generalizing z with
  | zero => simp [fallingPower]
  | succ n ih =>
    have hloc : iteratedDeriv n (fun z : ℂ => z^a) =ᶠ[𝓝 z]
        (fun z => fallingPower a n*z^(a-n)) := by
      filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz] with w hw using ih hw
    rw [iteratedDeriv_succ,hloc.deriv_eq]
    have hd := ((Complex.hasStrictDerivAt_cpow_const (c := a-n) hz).hasDerivAt.const_mul (fallingPower a n)).deriv
    rw [hd]
    have hp : fallingPower a (n+1)=fallingPower a n*(a-n) := by
      simp [fallingPower,Finset.prod_range_succ]
    rw [hp,show a-(n:ℂ)-1=a-((n+1:ℕ):ℂ) by push_cast; ring]
    ring

/-- Corrected general linear ODE solution: the arbitrary constant multiplies the exponential. -/
@[dlmf 4.7.E12, dlmf 4.7.E13]
theorem linear_ode_solution {s : Set ℂ} (hs : IsOpen s) (hc : IsPreconnected s)
    (f F w : ℂ → ℂ) (hF : ∀ z ∈ s, HasDerivAt F (f z) z) :
    (∀ z ∈ s, HasDerivAt w (f z * w z) z) ↔
      ∃ C : ℂ, ∀ z ∈ s, w z = C * Complex.exp (F z) := by
  constructor
  · intro hw
    have hV (z : ℂ) (hz : z∈s) :
        HasDerivAt (fun t => w t * Complex.exp (-F t)) 0 z := by
      convert (hw z hz).mul ((hF z hz).neg.cexp) using 1
      ring
    obtain ⟨C,hC⟩ := hs.exists_is_const_of_deriv_eq_zero hc
      (fun z hz => (hV z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hV z hz).deriv)
    refine ⟨C,fun z hz => ?_⟩
    have h := congrArg (fun t => t*Complex.exp (F z)) (hC z hz)
    simpa only [mul_assoc,← Complex.exp_add,neg_add_cancel,Complex.exp_zero,mul_one] using h
  · rintro ⟨C,hC⟩ z hz
    have hloc : w =ᶠ[𝓝 z] (fun z => C*Complex.exp (F z)) := by
      filter_upwards [hs.mem_nhds hz] with z hz using hC z hz
    convert ((hF z hz).cexp.const_mul C).congr_of_eventuallyEq hloc using 1
    rw [hC z hz]
    ring

/-- General second-order constant-coefficient ODE solution, including both arbitrary constants. -/
@[dlmf 4.7.E14, dlmf 4.7.E15]
theorem second_order_ode_solution {s : Set ℂ} (hs : IsOpen s) (hc : IsPreconnected s)
    {a : ℂ} (ha : a ≠ 0) (w : ℂ → ℂ) :
    (∀ z ∈ s, HasDerivAt w (deriv w z) z ∧ HasDerivAt (deriv w) (a * w z) z) ↔
      ∃ A B : ℂ, ∀ z ∈ s,
        w z = A * Complex.exp ((a ^ (1 / 2 : ℂ)) * z) + B * Complex.exp (-(a ^ (1 / 2 : ℂ)) * z) := by
  let r := a^(1/2:ℂ)
  have hr : r≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl ha)
  have hr2 : r^2=a := by
    dsimp only [r]
    rw [← Complex.cpow_nat_mul]
    norm_num
  have hFp : ∀ z∈s, HasDerivAt (fun z : ℂ => r*z) r z := by
    intro z _
    simpa using (hasDerivAt_id z).const_mul r
  have hFm : ∀ z∈s, HasDerivAt (fun z : ℂ => -r*z) (-r) z := by
    intro z _
    simpa using (hasDerivAt_id z).const_mul (-r)
  constructor
  · intro hw
    have hp : ∀ z∈s, HasDerivAt (fun z => deriv w z+r*w z)
        (r*(deriv w z+r*w z)) z := by
      intro z hz
      convert (hw z hz).2.add ((hw z hz).1.const_mul r) using 1
      rw [← hr2]
      ring
    have hm : ∀ z∈s, HasDerivAt (fun z => deriv w z-r*w z)
        (-r*(deriv w z-r*w z)) z := by
      intro z hz
      convert (hw z hz).2.sub ((hw z hz).1.const_mul r) using 1
      rw [← hr2]
      ring
    obtain ⟨A,hA⟩ := (linear_ode_solution hs hc (fun _ => r) (fun z => r*z)
      (fun z => deriv w z+r*w z) hFp).mp hp
    obtain ⟨B,hB⟩ := (linear_ode_solution hs hc (fun _ => -r) (fun z => -r*z)
      (fun z => deriv w z-r*w z) hFm).mp hm
    refine ⟨A/(2*r),-B/(2*r),fun z hz => ?_⟩
    change w z=A/(2*r)*Complex.exp (r*z)+ -B/(2*r)*Complex.exp (-r*z)
    have he : (2*r)*w z=A*Complex.exp (r*z)-B*Complex.exp (-r*z) := by
      linear_combination hA z hz-hB z hz
    simp only [neg_mul] at he ⊢
    field_simp
    linear_combination he
  · rintro ⟨A,B,hAB⟩ z hz
    let g := fun z => A*Complex.exp (r*z)+B*Complex.exp (-r*z)
    have hg (z : ℂ) (hz : z∈s) : HasDerivAt g
        (A*(Complex.exp (r*z)*r)+B*(Complex.exp (-r*z)*(-r))) z :=
      ((hFp z hz).cexp.const_mul A).add ((hFm z hz).cexp.const_mul B)
    have hloc : w =ᶠ[𝓝 z] g := by
      filter_upwards [hs.mem_nhds hz] with t ht using hAB t ht
    have hder (t : ℂ) (ht : t∈s) :
        deriv w t=A*(Complex.exp (r*t)*r)+B*(Complex.exp (-r*t)*(-r)) := by
      have heq : w =ᶠ[𝓝 t] g := by
        filter_upwards [hs.mem_nhds ht] with v hv using hAB v hv
      exact ((hg t ht).congr_of_eventuallyEq heq).deriv
    have hlocald : deriv w =ᶠ[𝓝 z]
        (fun t => A*(Complex.exp (r*t)*r)+B*(Complex.exp (-r*t)*(-r))) := by
      filter_upwards [hs.mem_nhds hz] with t ht using hder t ht
    constructor
    · simpa only [hder z hz] using (hg z hz).congr_of_eventuallyEq hloc
    · have hd := ((((hFp z hz).cexp.mul_const r).const_mul A).add
        (((hFm z hz).cexp.mul_const (-r)).const_mul B)).congr_of_eventuallyEq hlocald
      convert hd using 1
      rw [show a*w z=r^2*w z by rw [hr2],hAB z hz]
      change r^2*(A*Complex.exp (r*z)+B*Complex.exp (-r*z)) =
        A*(Complex.exp (r*z)*r*r)+B*(Complex.exp (-r*z)*(-r)*(-r))
      simp only [neg_mul]
      ring

/-- Product identity as equality of full multivalued logarithm sets. -/
@[dlmf 4.8.E1]
theorem generalLogValues_mul {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    generalLogValues (x * y) = {w | ∃ u ∈ generalLogValues x, ∃ v ∈ generalLogValues y, w = u + v} := by
  ext w
  change Complex.exp w=x*y ↔ _
  constructor
  · intro hw
    refine ⟨Complex.log x, Complex.exp_log hx, w-Complex.log x, ?_, by ring⟩
    change Complex.exp (w-Complex.log x)=y
    rw [Complex.exp_sub, hw, Complex.exp_log hx]
    field_simp
  · rintro ⟨u,hu,v,hv,rfl⟩
    rw [Complex.exp_add, show Complex.exp u=x from hu, show Complex.exp v=y from hv]

/-- Quotient identity as equality of full multivalued logarithm sets. -/
@[dlmf 4.8.E3]
theorem generalLogValues_div {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    generalLogValues (x / y) = {w | ∃ u ∈ generalLogValues x, ∃ v ∈ generalLogValues y, w = u - v} := by
  ext w
  change Complex.exp w=x/y ↔ _
  constructor
  · intro hw
    refine ⟨w+Complex.log y, ?_, Complex.log y, Complex.exp_log hy, by ring⟩
    change Complex.exp (w+Complex.log y)=x
    rw [Complex.exp_add, hw, Complex.exp_log hy]
    field_simp
  · rintro ⟨u,hu,v,hv,rfl⟩
    rw [Complex.exp_sub, show Complex.exp u=x from hu, show Complex.exp v=y from hv]

/-- All branches of the integer-power logarithm; shifts remain arbitrary, including at exponent zero. -/
@[dlmf 4.8.E5]
theorem generalLogValues_zpow {z : ℂ} (hz : z ≠ 0) (n : ℤ) :
    generalLogValues (z ^ n) = {w | ∃ k : ℤ, w = n * Complex.log z + k * (2 * Real.pi * I)} := by
  have he : Complex.exp ((n:ℂ)*Complex.log z)=z^n := by
    rw [Complex.exp_int_mul, Complex.exp_log hz]
  ext w
  change Complex.exp w=z^n ↔ _
  rw [← he]
  exact Complex.exp_eq_exp_iff_exists_int

/-- Principal integer-power identity with the half-open Mathlib strip. -/
@[dlmf 4.8.E6]
theorem log_zpow_strip {z : ℂ} (hz : z ≠ 0) (n : ℤ)
    (hlo : -Real.pi < n * z.arg) (hhi : n * z.arg ≤ Real.pi) :
    Complex.log (z ^ n) = n * Complex.log z := by
  have he : Complex.exp ((n:ℂ)*Complex.log z)=z^n := by
    rw [Complex.exp_int_mul, Complex.exp_log hz]
  rw [← he]
  apply Complex.log_exp <;> simpa [Complex.mul_im,Complex.log_im]

/-- Every logarithm of an exponential differs by an integer period. -/
@[dlmf 4.8.E8]
theorem generalLogValues_exp (z : ℂ) : generalLogValues (Complex.exp z) =
    {w | ∃ k : ℤ, w = z + k * (2 * Real.pi * I)} := by
  ext w
  exact Complex.exp_eq_exp_iff_exists_int

/-- Logarithms of a selected general power acquire an independent integer shift. -/
@[dlmf 4.8.E11]
theorem generalLogValues_power {a : ℂ} (ha : a ≠ 0) (z : ℂ) (j : ℤ) :
    generalLogValues (Complex.exp (z * logSheet j a)) =
      {w | ∃ k : ℤ, w = z * logSheet j a + k * (2 * Real.pi * I)} := by
  exact generalLogValues_exp (z*logSheet j a)

/-- Principal logarithm of a principal power with the unique half-open strip correction. -/
@[dlmf 4.8.E12]
theorem log_cpow_sheet {a : ℂ} (ha : a ≠ 0) (z : ℂ) :
    ∃ k : ℤ, Complex.log (a ^ z) = z * Complex.log a + k * (2 * Real.pi * I) ∧
      -Real.pi < (z * Complex.log a + k * (2 * Real.pi * I)).im ∧
      (z * Complex.log a + k * (2 * Real.pi * I)).im ≤ Real.pi := by
  obtain ⟨k,hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp
    (Complex.exp_log ((Complex.cpow_ne_zero_iff.mpr (Or.inl ha))) |>.trans (Complex.cpow_def_of_ne_zero ha z))
  refine ⟨k, ?_, ?_, ?_⟩
  · simpa only [mul_comm] using hk
  · rw [← show Complex.log (a^z)=z*Complex.log a+k*(2*Real.pi*I) by simpa only [mul_comm] using hk]
    simpa only [Complex.log_im] using Complex.neg_pi_lt_arg (a^z)
  · rw [← show Complex.log (a^z)=z*Complex.log a+k*(2*Real.pi*I) by simpa only [mul_comm] using hk]
    simpa only [Complex.log_im] using Complex.arg_le_pi (a^z)

/-- Exponentiating twice uses the principal strip, with the lower edge excluded. -/
@[dlmf 4.8.E17]
theorem exp_cpow_strip {z : ℂ} (hlo : -Real.pi < z.im) (hhi : z.im ≤ Real.pi) (a : ℂ) :
    (Complex.exp z) ^ a = Complex.exp (z * a) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero z),Complex.log_exp hlo hhi]

/-- Integer outer exponents remove the strip restriction entirely. -/
@[dlmf 4.8.E17]
theorem exp_cpow_int (z : ℂ) (n : ℤ) : (Complex.exp z) ^ n = Complex.exp (z * n) := by
  simpa only [mul_comm] using (Complex.exp_int_mul z n).symm

/-- The closed principal product identity retains both valid strip edges (4.8.2). -/
@[dlmf 4.8.E2]
theorem closedLog_mul {x y u v : ℂ} (hu : u ∈ closedLogValues x)
    (hv : v ∈ closedLogValues y) (hstrip : |(u + v).im| ≤ Real.pi) :
    u + v ∈ closedLogValues (x * y) := by
  simp only [closedLogValues, mem_setOf_eq] at *
  exact ⟨by rw [Complex.exp_add, hu.1, hv.1], hstrip⟩

/-- The closed principal quotient identity retains both valid strip edges (4.8.4). -/
@[dlmf 4.8.E4]
theorem closedLog_div {x y u v : ℂ} (hu : u ∈ closedLogValues x)
    (hv : v ∈ closedLogValues y) (hstrip : |(u - v).im| ≤ Real.pi) :
    u - v ∈ closedLogValues (x / y) := by
  simp only [closedLogValues, mem_setOf_eq] at *
  exact ⟨by rw [Complex.exp_sub, hu.1, hv.1], hstrip⟩

/-- The closed integer-power identity retains both strip edges (4.8.6). -/
@[dlmf 4.8.E6]
theorem closedLog_zpow {z l : ℂ} (hl : l ∈ closedLogValues z) (n : ℤ)
    (hstrip : |(n * l).im| ≤ Real.pi) :
    n * l ∈ closedLogValues (z ^ n) := by
  refine ⟨?_,hstrip⟩
  change Complex.exp ((n:ℂ)*l)=z^n
  rw [Complex.exp_int_mul,show Complex.exp l=z from hl.1]

/-- Inversion exchanges the two sides of the cut (4.8.7). -/
@[dlmf 4.8.E7]
theorem closedLog_inv {z l : ℂ} (hl : l ∈ closedLogValues z) :
    -l ∈ closedLogValues z⁻¹ := by
  simp only [closedLogValues, mem_setOf_eq] at *
  exact ⟨by rw [Complex.exp_neg, hl.1], by simpa using hl.2⟩

/-- The closed logarithm of an exponential includes both edges (4.8.9). -/
@[dlmf 4.8.E9]
theorem closedLog_exp {z : ℂ} (hstrip : |z.im| ≤ Real.pi) :
    z ∈ closedLogValues (Complex.exp z) := ⟨rfl, hstrip⟩

/-- Compatible principal logarithms give compatible principal products of powers (4.8.15). -/
@[dlmf 4.8.E15]
theorem closedPower_mul {a b u v : ℂ} (hu : u ∈ closedLogValues a)
    (hv : v ∈ closedLogValues b) (hstrip : |(u + v).im| ≤ Real.pi) (z : ℂ) :
    Complex.exp (z * u) * Complex.exp (z * v) ∈ closedPowerValues (a * b) z := by
  refine ⟨u + v, closedLog_mul hu hv hstrip, ?_⟩
  rw [← Complex.exp_add]; congr 1; ring

/-- The zero-limit holds even on every complex approach, including both cut sides. -/
@[dlmf 4.4.E14]
theorem tendsto_cpow_mul_log_complex_zero {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun z : ℂ => z ^ a * Complex.log z) (𝓝[≠] 0) (𝓝 0) := by
  let C := Real.exp (Real.pi*|a.im|)
  have hC : 0≤C := (Real.exp_pos _).le
  have hp : Tendsto (fun r : ℝ => r^a.re) (𝓝[>] 0) (𝓝 0) := by
    simpa [Real.zero_rpow ha.ne'] using
      (Real.continuousAt_rpow_const 0 a.re (Or.inr ha.le)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have hl := (tendsto_log_mul_rpow_nhdsGT_zero ha).norm
  have hg : Tendsto (fun r : ℝ => C*(‖Real.log r*r^a.re‖+Real.pi*r^a.re))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (hl.add (hp.const_mul Real.pi)).const_mul C
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ (hg.comp tendsto_norm_nhdsNE_zero)
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z≠0 := hz
  have harg : -z.arg*a.im≤Real.pi*|a.im| := by
    calc
      -z.arg*a.im = -(z.arg*a.im) := by ring
      _≤|z.arg*a.im| := neg_le_abs _
      _=|z.arg| * |a.im| := abs_mul _ _
      _≤Real.pi*|a.im| := mul_le_mul_of_nonneg_right (Complex.abs_arg_le_pi z) (abs_nonneg _)
  have hpow : ‖z^a‖≤C*‖z‖^a.re := by
    rw [Complex.norm_cpow_of_ne_zero hz0,div_eq_mul_inv,← Real.exp_neg]
    have hh : Real.exp (-(z.arg*a.im))≤C := by
      apply Real.exp_le_exp.mpr
      simpa only [neg_mul] using harg
    exact (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (norm_nonneg z) a.re)).trans_eq (mul_comm _ _)
  have hlog : ‖Complex.log z‖≤|Real.log ‖z‖|+Real.pi := by
    have h := Complex.norm_le_abs_re_add_abs_im (Complex.log z)
    rw [Complex.log_re,Complex.log_im] at h
    linarith [Complex.abs_arg_le_pi z]
  calc
    ‖z^a*Complex.log z‖ ≤ (C*‖z‖^a.re)*(|Real.log ‖z‖|+Real.pi) := by
      rw [norm_mul]
      exact mul_le_mul hpow hlog (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg z) a.re))
    _=C*(‖Real.log ‖z‖*‖z‖^a.re‖+Real.pi*‖z‖^a.re) := by
      rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) a.re)]
      ring

end DLMF.Elementary
