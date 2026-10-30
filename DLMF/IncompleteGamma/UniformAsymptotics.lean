/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.AnalyticProperties
public import DLMF.IncompleteGamma.ContinuedProperties
public import DLMFMathlib.Analysis.Complex.StarPrimitive
public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.Topology.Covering.Proper

/-!
# Uniform incomplete-Gamma expansions and inversion, DLMF §8.12

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
The inverse continues to the full Maclaurin disk through Mathlib's covering-space
lifting theorem and the Tau Ceti contributors' proper local-homeomorphism criterion
(`TauCeti.Topology.Covering.Proper`). Compact sublevel estimates keep its preimages
inside the zero-free strip. The local inverse uses Mathlib's analytic inverse-function
theorem, and its series uses `Complex.hasSum_taylorSeries_on_ball`.
Uniform remainder estimates and further coefficient statements remain admitted.
-/

@[expose] public noncomputable section
open Topology Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat ENNReal
namespace DLMF.Confluent

open DLMF.Statistical

/-- Scaled Gamma Γ*, as in DLMF 5.11.3; the retired 8.18.13 points there. -/
def gammaScaled (z : ℂ) : ℂ :=
  Gamma z/((2*π : ℂ)^(1/2 : ℂ)*exp ((z-1/2)*log z-z))

/-- The Stirling coefficients g_k from the actual scaled Gamma expansion. -/
def gammaStirlingCoeff (k : ℕ) : ℂ :=
  asymptoticCoeff (fun t : ℝ => gammaScaled t) k

/-- Nonvanishing analytic factor used to choose the continuous square root. -/
def gammaEtaFactor (w : ℂ) : ℂ :=
  if w=0 then 1 else 2*(exp w-1-w)/w^2

/-- η on the logarithmic λ-plane, normalized by η~log λ~λ-1 at λ=1. -/
@[dlmf 8.12.E1]
def gammaUniformEtaOnLog (w : ℂ) : ℂ :=
  w*exp (primitive (fun t => deriv gammaEtaFactor t/gammaEtaFactor t) w/2)

/-- Real core of the zero-free strip: `e^x sin u = u`, `e^x cos u = 1+x` has no solution with
`0 < u < 2π`. -/
lemma incG_no_root_aux {x u : ℝ} (hu0 : 0 < u) (hu : u < 2*π)
    (hs : Real.exp x * Real.sin u = u) (hc : Real.exp x * Real.cos u = 1+x) : False := by
  have hex := Real.exp_pos x
  by_cases hπ : π ≤ u
  · have h1 := Real.sin_nonneg_of_nonneg_of_le_pi (x := u - π) (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at h1
    nlinarith
  push Not at hπ
  have hsin : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu0 hπ
  have hlt : Real.sin u < u := Real.sin_lt hu0
  have hx : 0 < x := by
    by_contra hx; push Not at hx
    have : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx
    nlinarith
  have hkey : u * Real.cos u < Real.sin u := by
    by_cases hc0 : Real.cos u ≤ 0
    · nlinarith
    push Not at hc0
    have hu2 : u < π/2 := by
      by_contra h; push Not at h
      have := Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith); linarith
    have := Real.lt_tan hu0 hu2
    rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hc0] at this
    linarith
  have : (1+x)*Real.sin u = u*Real.cos u := by
    linear_combination (-Real.sin u)*hc + Real.cos u*hs
  nlinarith

/-- `e^w = 1 + w` has no nonzero root in the strip `|Im w| < 2π`. -/
theorem incG_exp_sub_one_sub_ne_zero {w : ℂ} (hw : |w.im| < 2*π) (hw0 : w ≠ 0) :
    exp w - 1 - w ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sub_re, sub_im, Complex.exp_re, Complex.exp_im, one_re, one_im, zero_re, zero_im] at hre him
  rcases lt_trichotomy w.im 0 with hy | hy | hy
  · refine incG_no_root_aux (x := w.re) (u := -w.im) (by linarith) (by rw [abs_lt] at hw; linarith)
      ?_ ?_
    · rw [Real.sin_neg]; linarith
    · rw [Real.cos_neg]; linarith
  · have hx : w.re ≠ 0 := fun hx => hw0 (Complex.ext hx hy)
    rw [hy, Real.cos_zero, mul_one] at hre
    have := Real.add_one_lt_exp hx
    linarith
  · exact incG_no_root_aux (x := w.re) (u := w.im) hy (by rw [abs_lt] at hw; linarith)
      (by linarith) (by linarith)

/-- `(e^w-1-w)/w² → 1/2` as `w → 0`. -/
theorem incG_tendsto_etaQuot :
    Tendsto (fun w : ℂ => (exp w - 1 - w)/w^2) (𝓝[≠] 0) (𝓝 (1/2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    ((continuous_norm.tendsto (0:ℂ)).mono_left nhdsWithin_le_nhds |>.trans (by simp))
  have hb : ∀ᶠ w in 𝓝[≠] (0:ℂ), ‖w‖ ≤ 1 ∧ w ≠ 0 := by
    filter_upwards [nhdsWithin_le_nhds (Metric.closedBall_mem_nhds (0:ℂ) one_pos),
      self_mem_nhdsWithin] with w hw hw0
    exact ⟨by simpa using hw, hw0⟩
  filter_upwards [hb] with w ⟨hw, hw0⟩
  have h := Complex.exp_bound hw (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial] at h
  norm_num at h
  have hw2 : (0:ℝ) < ‖w‖^2 := by positivity
  have e : (exp w - 1 - w)/w^2 - 1/2 = (exp w - (1 + w + w^2/2))/w^2 := by
    field_simp; ring
  rw [e, norm_div, norm_pow, div_le_iff₀ hw2]
  calc ‖exp w - (1 + w + w^2/2)‖ ≤ ‖w‖^3 * (2/9) := by convert h using 2
    _ ≤ ‖w‖ * ‖w‖^2 := by nlinarith [norm_nonneg w]

/-- The factor `2(e^w-1-w)/w²`, filled in by `1` at the origin, is entire. -/
theorem incG_gammaEtaFactor_differentiable : Differentiable ℂ gammaEtaFactor := by
  have hne : ∀ w : ℂ, w ≠ 0 → gammaEtaFactor =ᶠ[𝓝 w] fun v => 2*(exp v-1-v)/v^2 := by
    intro w hw
    filter_upwards [isOpen_compl_singleton.mem_nhds hw] with v hv
    simp [gammaEtaFactor, show v ≠ 0 from hv]
  have hd : ∀ w : ℂ, w ≠ 0 → DifferentiableAt ℂ gammaEtaFactor w := by
    intro w hw
    refine DifferentiableAt.congr_of_eventuallyEq ?_ (hne w hw)
    exact ((by fun_prop : Differentiable ℂ fun v : ℂ => 2*(exp v-1-v)) w).div
      (by fun_prop) (pow_ne_zero 2 hw)
  intro w
  by_cases hw : w = 0
  · subst hw
    have hc : ContinuousAt gammaEtaFactor 0 := by
      rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
      have h := incG_tendsto_etaQuot.const_mul (2:ℂ)
      rw [show (2:ℂ)*(1/2) = gammaEtaFactor 0 by simp [gammaEtaFactor]] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with v hv
      simp [gammaEtaFactor, show v ≠ 0 from hv]; ring
    exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (by filter_upwards [self_mem_nhdsWithin] with v hv using hd v hv) hc).differentiableAt
  · exact hd w hw

/-- The strip `|Im w| < 2π`. -/
def incG_strip : Set ℂ := {w : ℂ | |w.im| < 2*π}

/-- The indicated domain is open: `IsOpen incG_strip`. -/
theorem incG_strip_isOpen : IsOpen incG_strip :=
  isOpen_lt (continuous_abs.comp continuous_im) continuous_const

/-- The stated relation follows from the given hypotheses: `Convex ℝ incG_strip`. -/
theorem incG_strip_convex : Convex ℝ incG_strip := by
  intro u hu v hv a b ha hb hab
  simp only [incG_strip, Set.mem_ofPred_eq] at *
  have : (a • u + b • v).im = a*u.im + b*v.im := by simp
  rw [this]
  calc |a*u.im + b*v.im| ≤ a*|u.im| + b*|v.im| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ < 2*π := by
        rcases ha.eq_or_lt with h | h
        · subst h; simp at hab; subst hab; simpa using hv
        · have hb' : b*|v.im| ≤ b*(2*π) := mul_le_mul_of_nonneg_left hv.le hb
          have ha' : a*|u.im| < a*(2*π) := mul_lt_mul_of_pos_left hu h
          have hs : a*(2*π)+b*(2*π) = 2*π := by rw [← add_mul, hab, one_mul]
          linarith

/-- Formula under the stated hypotheses: `(0:ℂ) ∈ incG_strip`. -/
theorem incG_zero_mem_strip : (0:ℂ) ∈ incG_strip := by simp [incG_strip, Real.pi_pos]

/-- Nonvanishing under the stated hypotheses: `gammaEtaFactor w ≠ 0`. -/
theorem incG_gammaEtaFactor_ne_zero {w : ℂ} (hw : w ∈ incG_strip) : gammaEtaFactor w ≠ 0 := by
  by_cases h0 : w = 0
  · simp [gammaEtaFactor, h0]
  · simp only [gammaEtaFactor, h0, ↓reduceIte]
    exact div_ne_zero (mul_ne_zero two_ne_zero (incG_exp_sub_one_sub_ne_zero hw h0))
      (pow_ne_zero 2 h0)

/-- The logarithmic derivative of the factor is holomorphic on the strip. -/
theorem incG_logDeriv_differentiableOn :
    DifferentiableOn ℂ (fun t => deriv gammaEtaFactor t/gammaEtaFactor t) incG_strip := by
  have hd := incG_gammaEtaFactor_differentiable
  have hdd : Differentiable ℂ (deriv gammaEtaFactor) := fun w =>
    ((hd.differentiableOn.analyticOnNhd isOpen_univ).deriv w (mem_univ w)).differentiableAt
  exact (hdd.differentiableOn).div hd.differentiableOn fun w hw => incG_gammaEtaFactor_ne_zero hw

/-- The primitive in the definition of η has the expected derivative on the strip. -/
theorem incG_hasDerivAt_etaPrimitive {w : ℂ} (hw : w ∈ incG_strip) :
    HasDerivAt (primitive (fun t => deriv gammaEtaFactor t/gammaEtaFactor t))
      (deriv gammaEtaFactor w/gammaEtaFactor w) w := by
  have he : primitive (fun t => deriv gammaEtaFactor t/gammaEtaFactor t) =
      fun v => v * ∫ t in (0:ℝ)..1, (fun t => deriv gammaEtaFactor t/gammaEtaFactor t) (t*v) := by
    funext v; simp [primitive, segmentIntegral]
  rw [he]
  exact Complex.starPrim_hasDerivAt incG_strip_isOpen (incG_strip_convex.starConvex incG_zero_mem_strip)
    incG_logDeriv_differentiableOn hw

/-- `exp` of the primitive of the logarithmic derivative recovers the factor on the strip. -/
theorem incG_exp_etaPrimitive {w : ℂ} (hw : w ∈ incG_strip) :
    exp (primitive (fun t => deriv gammaEtaFactor t/gammaEtaFactor t) w) = gammaEtaFactor w := by
  set P := primitive (fun t => deriv gammaEtaFactor t/gammaEtaFactor t)
  set f := gammaEtaFactor
  have hf := incG_gammaEtaFactor_differentiable
  have hD : ∀ v ∈ incG_strip, HasDerivAt (fun v => f v * exp (-P v)) 0 v := by
    intro v hv
    have h1 := (hf v).hasDerivAt
    have h2 := ((incG_hasDerivAt_etaPrimitive hv).neg).cexp
    have := h1.mul h2
    convert this using 1
    have := incG_gammaEtaFactor_ne_zero hv
    field_simp; ring
  have hc := incG_strip_isOpen.is_const_of_deriv_eq_zero (incG_strip_convex.isPreconnected)
    (fun v hv => (hD v hv).differentiableAt.differentiableWithinAt)
    (fun v hv => (hD v hv).deriv) hw incG_zero_mem_strip
  simp only [P, primitive_zero, neg_zero, Complex.exp_zero, mul_one] at hc
  have h0 : f 0 = 1 := by simp [f, gammaEtaFactor]
  rw [h0] at hc
  have : exp (P w) * exp (-P w) = 1 := by rw [← Complex.exp_add]; simp
  calc exp (P w) = exp (P w) * (f w * exp (-P w)) := by rw [hc, mul_one]
    _ = f w * (exp (P w) * exp (-P w)) := by ring
    _ = f w := by rw [this, mul_one]

/-- Identity under the stated parameter and domain assumptions: `gammaUniformEtaOnLog w^2/2=exp
w-1-w`. -/
theorem incG_gammaUniformEta_sq {w : ℂ} (hw : |w.im| < 2*π) :
    gammaUniformEtaOnLog w^2/2=exp w-1-w := by
  have he := incG_exp_etaPrimitive (w := w) hw
  unfold gammaUniformEtaOnLog
  rw [mul_pow, ← Complex.exp_nat_mul, show ((2:ℕ):ℂ) * (primitive (fun t => deriv gammaEtaFactor t / gammaEtaFactor t) w / 2) = primitive (fun t => deriv gammaEtaFactor t / gammaEtaFactor t) w by push_cast; ring, he]
  by_cases h0 : w = 0
  · subst h0; simp
  · simp only [gammaEtaFactor, h0, ↓reduceIte]
    field_simp

/-- Derivative formula at the specified argument: `HasDerivAt gammaUniformEtaOnLog 1 0 ∧
gammaUniformEtaOnLog 0=0`. -/
theorem incG_gammaUniformEta_normalization :
    HasDerivAt gammaUniformEtaOnLog 1 0 ∧ gammaUniformEtaOnLog 0=0 := by
  refine ⟨?_, by simp [gammaUniformEtaOnLog]⟩
  have hP := incG_hasDerivAt_etaPrimitive incG_zero_mem_strip
  have h := (hasDerivAt_id (0:ℂ)).mul ((hP.div_const 2).cexp)
  have e : gammaUniformEtaOnLog = fun w => id w * exp (primitive (fun t => deriv gammaEtaFactor t/gammaEtaFactor t) w/2) := rfl
  rw [e]
  convert h using 1
  simp

/-- At `w`, the function `gammaUniformEtaOnLog` has derivative `((exp w-1)/gammaUniformEtaOnLog
w)`. -/
theorem incG_gammaUniformEta_derivative {w : ℂ} (hw : |w.im| < 2*π) (hw0 : w ≠ 0) :
    HasDerivAt gammaUniformEtaOnLog ((exp w-1)/gammaUniformEtaOnLog w) w := by
  have hws : w ∈ incG_strip := hw
  have hP := incG_hasDerivAt_etaPrimitive hws
  have h := (hasDerivAt_id w).mul ((hP.div_const 2).cexp)
  have e : gammaUniformEtaOnLog = fun w => id w * exp (primitive (fun t => deriv gammaEtaFactor t/gammaEtaFactor t) w/2) := rfl
  set d := 1 * exp (primitive (fun t => deriv gammaEtaFactor t/gammaEtaFactor t) w/2) + id w * (exp (primitive (fun t => deriv gammaEtaFactor t/gammaEtaFactor t) w/2) * (deriv gammaEtaFactor w/gammaEtaFactor w/2))
  have hη : HasDerivAt gammaUniformEtaOnLog d w := by rw [e]; exact h
  -- differentiate η² = 2(e^w-1-w) near w
  have hsq : HasDerivAt (fun v => gammaUniformEtaOnLog v^2) (2*gammaUniformEtaOnLog w*d) w := by
    have := hη.fun_pow 2; simpa [mul_comm, mul_assoc, mul_left_comm] using this
  have hsq' : HasDerivAt (fun v => gammaUniformEtaOnLog v^2) (2*(exp w-1)) w := by
    have h2 : HasDerivAt (fun v : ℂ => 2*(exp v-1-v)) (2*(exp w-1)) w := by
      have := (((Complex.hasDerivAt_exp w).sub_const 1).sub (hasDerivAt_id w)).const_mul (2:ℂ)
      simpa using this
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [incG_strip_isOpen.mem_nhds hws] with v hv
    have := incG_gammaUniformEta_sq (w := v) hv
    linear_combination 2*this
  have huniq := hsq.unique hsq'
  have hη0 : gammaUniformEtaOnLog w ≠ 0 := by
    intro h0
    have := incG_gammaUniformEta_sq hw
    rw [h0] at this
    exact incG_exp_sub_one_sub_ne_zero hw hw0 (by rw [← this]; ring)
  have : d = (exp w-1)/gammaUniformEtaOnLog w := by
    field_simp
    linear_combination huniq/2
  rw [← this]; exact hη

/-- Identity under the stated parameter and domain assumptions: `gammaUniformEtaOnLog w^2/2=exp
w-1-w`. -/
@[dlmf 8.12.E2]
theorem gammaUniformEta_equation {w : ℂ} (hw : |w.im| < 2*π) :
    gammaUniformEtaOnLog w^2/2=exp w-1-w :=
  incG_gammaUniformEta_sq hw

/-- At `w`, the function `gammaUniformEtaOnLog` has derivative `((exp w-1)/gammaUniformEtaOnLog
w)`. -/
@[dlmf 8.12.E2]
theorem gammaUniformEta_derivative {w : ℂ} (hw : |w.im| < 2*π) (hw0 : w ≠ 0) :
    HasDerivAt gammaUniformEtaOnLog ((exp w-1)/gammaUniformEtaOnLog w) w :=
  incG_gammaUniformEta_derivative hw hw0

/-- Derivative formula at the specified argument: `HasDerivAt gammaUniformEtaOnLog 1 0 ∧
gammaUniformEtaOnLog 0=0`. -/
@[dlmf 8.12.E1]
theorem gammaUniformEta_normalization  :
    HasDerivAt gammaUniformEtaOnLog 1 0 ∧ gammaUniformEtaOnLog 0=0 :=
  incG_gammaUniformEta_normalization

/-- The exact S remainder, with w the logarithm of λ. -/
@[dlmf 8.12.E4]
def gammaUniformS (a w : ℂ) : ℂ :=
  normIncGammaQOnLog a (log a+w)-erfc (gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ))/2

/-- The exact T remainder with the removable integer-parameter quotient cancelled. -/
def gammaUniformT (a w : ℂ) : ℂ :=
  I*(-exp (π*I*a)*Gamma (a+1)/(2*π*I)*upperIncGammaOnLog (-a) (log a+w+π*I)-erfc (I*gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ))/2)

/-- Identity under the stated parameter and domain assumptions: `normIncGammaPOnLog a (log
a+w)=erfc (-gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ))/2-gammaUniformS a w`. -/
@[dlmf 8.12.E3]
theorem gammaUniformP_identity (a w : ℂ) :
    normIncGammaPOnLog a (log a+w)=erfc (-gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ))/2-gammaUniformS a w := by
  have h : ∀ u : ℂ, erfc (-u) + erfc u = 2 := by
    intro u; simp only [erfc, erf, neg_sq]; ring
  have := h (gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ))
  rw [gammaUniformS, normIncGammaQOnLog, neg_mul]
  linear_combination -this/2

/-- Points of the slit plane are not poles of `Γ(a+1)`. -/
theorem slitPlane_add_one_ne_neg_nat {a : ℂ} (ha : a ∈ slitPlane) : ∀ n : ℕ, a+1 ≠ -n := by
  intro n h
  have : a = ((-((n:ℝ)+1) : ℝ) : ℂ) := by push_cast; linear_combination h
  rw [this, ofReal_mem_slitPlane] at ha
  linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]

/-- The reflection formula cancels the source quotient by sin(πa), including integral a. -/
@[dlmf 8.12.E5]
theorem gammaUniformQ_negative_identity {a : ℂ} (ha : a ∈ slitPlane) {w : ℂ} {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    -exp (ε*π*I*a)*Gamma (a+1)/(2*π*I)*upperIncGammaOnLog (-a) (log a+w+ε*π*I)=ε/2*erfc (ε*I*gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ))-I*gammaUniformT a w := by
  have hG := Gamma_ne_zero (slitPlane_add_one_ne_neg_nat ha)
  rcases hε with rfl | rfl
  · simp only [gammaUniformT]
    push_cast
    ring_nf; rw [I_sq]; ring
  · have hj := upperIncGammaOnLog_jump (-a) (log a+w)
    rw [show 1-(-a)=a+1 by ring] at hj
    have he : ∀ u : ℂ, erfc (-u) + erfc u = 2 := by
      intro u; simp only [erfc, erf, neg_sq]; ring
    have h2 := he (I*gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ))
    simp only [gammaUniformT]
    push_cast
    rw [show log a+w+-1*π*I=log a+w-π*I by ring]
    have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp at hj
    field_simp
    ring_nf
    ring_nf at hj h2
    have hI3 : I^3 = -I := by rw [pow_succ, I_sq]; ring
    rw [hI3]
    linear_combination hj + π*I*h2
      - Gamma (1+a)*exp (π*I*a)*upperIncGammaOnLog (-a) (π*I+log a+w)*I_sq

/-- Identity under the stated parameter and domain assumptions: `exp (-a*(log a+w))*scIncGamma
(-a) (-a*exp w)=cos (π*a)-2*sin (π*a)*(exp (a*gammaUniformEtaOnLog w^2/2)/Real.sqrt π*dawsonF
(gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ))+gammaUniformT a w)`. -/
@[dlmf 8.12.E6]
theorem gammaUniform_scIncGamma_identity {a : ℂ} (ha : a ∈ slitPlane) {w : ℂ} :
    exp (-a*(log a+w))*scIncGamma (-a) (-a*exp w)=cos (π*a)-2*sin (π*a)*(exp (a*gammaUniformEtaOnLog w^2/2)/Real.sqrt π*dawsonF (gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ))+gammaUniformT a w) := by
  have ha0 : a ≠ 0 := slitPlane_ne_zero ha
  have hev : exp (log a+w)=a*exp w := by rw [Complex.exp_add, Complex.exp_log ha0]
  by_cases hint : ∃ n : ℕ, a = n
  · obtain ⟨n, rfl⟩ := hint
    have hs : Complex.sin (π*n)=0 := by
      rw [Complex.sin_eq_zero_iff]; exact ⟨n, by push_cast; ring⟩
    have hc : Complex.cos (π*n)=(-1)^n := by
      rw [show (π:ℂ)*n=((n*π:ℝ):ℂ) by push_cast; ring, ← ofReal_cos, Real.cos_nat_mul_pi]; push_cast; rfl
    rw [hs, hc, scIncGamma_neg_nat, mul_pow, neg_pow, show -(n:ℂ)*(log n+w)=-(n*(log n+w)) by ring,
      Complex.exp_neg, show (n:ℂ)*(log n+w)=(n:ℕ)*(log n+w) by rfl, Complex.exp_nat_mul, hev]
    have : (n:ℂ)*exp w ≠ 0 := mul_ne_zero ha0 (Complex.exp_ne_zero w)
    field_simp
    ring
  push Not at hint
  have hreg : ∀ n : ℕ, -a ≠ -n := fun n h => hint n (neg_inj.mp h)
  have hreg1 := slitPlane_add_one_ne_neg_nat ha
  have hs : Complex.sin (π*a) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    have hk' : a = k := mul_left_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) (by rw [hk]; ring)
    rcases Int.eq_nat_or_neg k with ⟨j, rfl | rfl⟩
    · exact hint j (by simpa using hk')
    · have : a = ((-(j:ℝ)) : ℝ) := by rw [hk']; push_cast; ring
      rw [this, ofReal_mem_slitPlane] at ha
      linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  have hU := upperIncGammaOnLog_halfTurn (log a+w) hreg (ε := 1) (Or.inl rfl)
  rw [hev] at hU
  have hr := Complex.Gamma_mul_Gamma_one_sub (-a)
  rw [show 1-(-a)=a+1 by ring, show (π:ℂ)*(-a)=-(π*a) by ring, Complex.sin_neg] at hr
  have herf : erf (I*(gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ)))
      =2/Real.sqrt π*I*exp (a*gammaUniformEtaOnLog w^2/2)*dawsonF (gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ)) := by
    set u := gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ)
    have hu2 : u^2=a*gammaUniformEtaOnLog w^2/2 := by
      simp only [u, mul_pow]
      rw [show (1/2:ℂ)=(2:ℂ)⁻¹ by norm_num]
      have := Complex.cpow_ofNat_inv_pow (a/2) 2
      rw [this]; ring
    have he : erf (I*u)=2/Real.sqrt π*I*primitive (fun t => exp (t^2)) u := by
      rw [erf_complex_segment_integral]
      simp only [primitive, segmentIntegral, sub_zero, zero_add]
      have harg (t : ℝ) : -((t:ℂ)*(I*u))^2=((t:ℂ)*u)^2 := by simp [mul_pow, I_sq]
      simp_rw [harg]
      ring
    have hx : exp (u^2)*exp (-u^2)=1 := by rw [← Complex.exp_add]; simp
    rw [he, dawsonF, ← hu2]
    linear_combination (-(2/Real.sqrt π*I*primitive (fun t => exp (t^2)) u))*hx
  simp only [gammaUniformT, erfc]
  rw [show I*gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ)=I*(gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ)) by ring,
    herf, show log a+w+π*I=log a+w+((1:ℝ):ℂ)*π*I by push_cast; ring, hU]
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsq : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hcs : Complex.cos (π*a)+I*Complex.sin (π*a)=exp (π*I*a) := by
    rw [show (π:ℂ)*I*a=(π*a)*I by ring, Complex.exp_mul_I]; ring
  have hee : exp (-a*(log a+w)+(1:ℝ)*π*I*(-a))=exp (-a*(log a+w))*exp (-(π*I*a)) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  have hpm : exp (π*I*a)*exp (-(π*I*a))=1 := by rw [← Complex.exp_add]; simp
  have hG1 := Gamma_ne_zero hreg1
  have hGm : Gamma (-a)=-π/(Complex.sin (π*a)*Gamma (a+1)) := by
    rw [eq_div_iff (mul_ne_zero hs hG1)]; rw [eq_div_iff (neg_ne_zero.mpr hs)] at hr
    linear_combination -hr
  rw [hee, hGm, neg_mul a (exp w), ← hcs]
  rw [← hcs] at hpm
  have hs' : Complex.sin (a*π) ≠ 0 := by rwa [mul_comm]
  have hpm' : (Complex.cos (a*π)+Complex.sin (a*π)*I)*exp (-(a*π*I))=1 := by
    rw [← hpm]; ring_nf
  field_simp
  linear_combination (-(Real.sqrt π:ℂ)*exp (-(a*(log a+w)))*scIncGamma (-a) (-(a*exp w)))*hpm'
    + Complex.sin (a*π)*(2*exp (a*gammaUniformEtaOnLog w^2/2)*dawsonF (gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ)))*I_sq

/-- Uniform coefficients, with removable singularities filled by limits at w=0. -/
@[dlmf 8.12.E9, dlmf 8.12.E10]
def gammaUniformC : ℕ → ℂ → ℂ
  | 0, w => if w=0 then -1/3 else 1/(exp w-1)-1/gammaUniformEtaOnLog w
  | k+1, w => if w=0 then limUnder (𝓝[≠] (0 : ℂ))
      (fun t => deriv (gammaUniformC k) t/(exp t-1)+(-1 : ℂ)^(k+1)*gammaStirlingCoeff (k+1)/(exp t-1))
    else deriv (gammaUniformC k) w/(exp w-1)+(-1 : ℂ)^(k+1)*gammaStirlingCoeff (k+1)/(exp w-1)

/-- On the positive axis the scaled Gamma function is `exp` of Binet's integral. -/
theorem incG_gammaScaled_ofReal {t : ℝ} (ht : 0 < t) :
    gammaScaled t = ((Real.exp (DLMF.Gamma.binetIntegral t) : ℝ) : ℂ) := by
  have hG : Real.Gamma t = (2*π)^(1/2:ℝ) * Real.exp ((t-1/2)*Real.log t - t) *
      Real.exp (DLMF.Gamma.binetIntegral t) := by
    rw [← Real.exp_log (Real.Gamma_pos_of_pos ht), DLMF.Gamma.log_Gamma_eq_add_binetIntegral ht,
      Real.rpow_def_of_pos (by positivity), ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  have hpos : (0:ℝ) < (2*π)^(1/2:ℝ) * Real.exp ((t-1/2)*Real.log t - t) := by positivity
  have e1 : ((2*π : ℂ))^(1/2 : ℂ) = (((2*π)^(1/2:ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow (by positivity)]; push_cast; rfl
  have e2 : exp (((t:ℂ)-1/2)*log t - t) = ((Real.exp ((t-1/2)*Real.log t - t) : ℝ) : ℂ) := by
    rw [ofReal_exp, ← ofReal_log ht.le]; push_cast; rfl
  rw [gammaScaled, Complex.Gamma_ofReal, e1, e2, hG]
  push_cast
  have : (((2*π)^(1/2:ℝ) : ℝ) : ℂ) * ((Real.exp ((t-1/2)*Real.log t - t) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  field_simp

/-- The map `DLMF.Gamma.binetIntegral` tends to `(𝓝 0)` along `atTop`. -/
theorem incG_tendsto_binetIntegral :
    Tendsto DLMF.Gamma.binetIntegral atTop (𝓝 0) := by
  have hu : Tendsto (fun t : ℝ => 1/(12*t)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 12))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with t ht using (DLMF.Gamma.binetIntegral_mem ht).1
  · filter_upwards [eventually_gt_atTop 0] with t ht using (DLMF.Gamma.binetIntegral_mem ht).2

/-- The map `(fun t : ℝ => t * DLMF.Gamma.binetIntegral t)` tends to `(𝓝 (1/12))` along `atTop`. -/
theorem incG_tendsto_mul_binetIntegral :
    Tendsto (fun t : ℝ => t * DLMF.Gamma.binetIntegral t) atTop (𝓝 (1/12)) := by
  have h := DLMF.Gamma.hasAsymptoticExpansion_binetIntegral 1
  simp only [Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero, zero_add, smul_eq_mul,
    Nat.cast_one] at h
  have hb : (bernoulli 2 : ℝ) / ((0+1)*(0+2)) = 1/12 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_two]; norm_num
  have hb' : (bernoulli 2 : ℝ) / (1*2) = 1/12 := by simpa using hb
  -- t * (Φ t - t⁻¹/12) = O(t⁻¹)
  have h2 : (fun t : ℝ => t * (DLMF.Gamma.binetIntegral t - t ^ (-(1:ℝ)) * (1/12))) =O[atTop]
      fun t : ℝ => t * t ^ (-((1:ℝ)+1)) := by
    rw [hb'] at h
    exact (isBigO_refl (fun t : ℝ => t) atTop).mul h
  have h3 : Tendsto (fun t : ℝ => t * t ^ (-((1:ℝ)+1))) atTop (𝓝 0) := by
    refine (tendsto_inv_atTop_zero).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [show -((1:ℝ)+1) = -2 by norm_num, Real.rpow_neg ht.le, Real.rpow_two]; field_simp
  have h4 := h2.trans_tendsto h3
  have h5 := h4.add (tendsto_const_nhds (x := (1/12 : ℝ)))
  rw [zero_add] at h5
  refine h5.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [Real.rpow_neg_one]; field_simp; ring

/-- The map `(fun t : ℝ => t * (Real.exp (DLMF.Gamma.binetIntegral t) - 1))` tends to `(𝓝 (1/12))`
along `atTop`. -/
theorem incG_tendsto_mul_exp_binet_sub_one :
    Tendsto (fun t : ℝ => t * (Real.exp (DLMF.Gamma.binetIntegral t) - 1)) atTop (𝓝 (1/12)) := by
  have hr : Tendsto (fun t : ℝ => t * (Real.exp (DLMF.Gamma.binetIntegral t) - 1 -
      DLMF.Gamma.binetIntegral t)) atTop (𝓝 0) := by
    have hu : Tendsto (fun t : ℝ => 1/(144*t)) atTop (𝓝 0) := by
      exact tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 144))
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
      (Eventually.of_forall fun _ => abs_nonneg _) ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    have ht0 : 0 < t := by linarith
    obtain ⟨h0, h1⟩ := DLMF.Gamma.binetIntegral_mem ht0
    have hle : |DLMF.Gamma.binetIntegral t| ≤ 1 := by
      rw [abs_of_nonneg h0]; refine h1.trans ?_; rw [div_le_one (by positivity)]; linarith
    have hq := Real.abs_exp_sub_one_sub_id_le hle
    simp only [Function.comp_apply]
    rw [abs_mul, abs_of_pos ht0]
    have hsq : DLMF.Gamma.binetIntegral t ^ 2 ≤ (1/(12*t))^2 := pow_le_pow_left₀ h0 h1 2
    calc t * |Real.exp (DLMF.Gamma.binetIntegral t) - 1 - DLMF.Gamma.binetIntegral t|
        ≤ t * (1/(12*t))^2 := mul_le_mul_of_nonneg_left (hq.trans hsq) ht0.le
      _ = 1/(144*t) := by field_simp; ring
  have := hr.add incG_tendsto_mul_binetIntegral
  rw [zero_add] at this
  exact this.congr fun t => by ring

/-- `g₀ = 1`. -/
theorem incG_gammaStirlingCoeff_zero : gammaStirlingCoeff 0 = 1 := by
  rw [gammaStirlingCoeff, asymptoticCoeff]
  refine Tendsto.limUnder_eq ?_
  have h1 : Tendsto (fun t => Real.exp (DLMF.Gamma.binetIntegral t)) atTop (𝓝 1) := by
    have := (Real.continuous_exp.tendsto 0).comp incG_tendsto_binetIntegral
    rwa [Real.exp_zero] at this
  have h := (continuous_ofReal.tendsto 1).comp h1
  simp only [ofReal_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [incG_gammaScaled_ofReal ht]

/-- `g₁ = 1/12`. -/
theorem incG_gammaStirlingCoeff_one : gammaStirlingCoeff 1 = 1/12 := by
  have h0 := incG_gammaStirlingCoeff_zero
  rw [gammaStirlingCoeff] at h0 ⊢
  rw [asymptoticCoeff]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.sub_zero, h0, CharP.cast_eq_zero,
    neg_zero, zpow_zero, mul_one, zero_add, pow_one]
  refine Tendsto.limUnder_eq ?_
  have h := (continuous_ofReal.tendsto _).comp incG_tendsto_mul_exp_binet_sub_one
  refine (by simpa using h : Tendsto _ _ (𝓝 ((1:ℂ)/12))).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [incG_gammaScaled_ofReal ht]

/-- `e^w ≠ 1` on the punctured strip `0 < |Im w| < 2π` or real `w ≠ 0`. -/
theorem incG_exp_sub_one_ne_zero {w : ℂ} (hw : |w.im| < 2*π) (hw0 : w ≠ 0) : exp w - 1 ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (sub_eq_zero.mp h)
  have him : w.im = n*(2*π) := by rw [hn]; simp
  have hn0 : n = 0 := by
    rw [him, abs_mul, abs_of_pos Real.two_pi_pos] at hw
    have : |(n:ℝ)| < 1 := by nlinarith [Real.pi_pos]
    have : |n| < 1 := by exact_mod_cast this
    exact Int.abs_lt_one_iff.mp this
  exact hw0 (by rw [hn, hn0]; simp)

/-- η does not vanish on the punctured strip. -/
theorem incG_gammaUniformEta_ne_zero {w : ℂ} (hw : |w.im| < 2*π) (hw0 : w ≠ 0) :
    gammaUniformEtaOnLog w ≠ 0 := by
  intro h0
  have := gammaUniformEta_equation hw
  rw [h0] at this
  exact incG_exp_sub_one_sub_ne_zero hw hw0 (by rw [← this]; ring)

/-- Identity under the stated parameter and domain assumptions: `gammaUniformC 0 w=1/(exp
w-1)-1/gammaUniformEtaOnLog w ∧ gammaUniformC 1 w=1/gammaUniformEtaOnLog w^3-1/(exp
w-1)^3-1/(exp w-1)^2-1/(12*(exp w-1))`. -/
theorem incG_gammaUniformC_first {w : ℂ} (hw : |w.im| < 2*π) (hw0 : w ≠ 0) :
    gammaUniformC 0 w=1/(exp w-1)-1/gammaUniformEtaOnLog w ∧ gammaUniformC 1 w=1/gammaUniformEtaOnLog w^3-1/(exp w-1)^3-1/(exp w-1)^2-1/(12*(exp w-1)) := by
  have h0 : ∀ v : ℂ, v ≠ 0 → gammaUniformC 0 v = 1/(exp v-1)-1/gammaUniformEtaOnLog v := by
    intro v hv; simp [gammaUniformC, hv]
  refine ⟨h0 w hw0, ?_⟩
  have hE := incG_exp_sub_one_ne_zero hw hw0
  have hη := incG_gammaUniformEta_ne_zero hw hw0
  have hD : HasDerivAt (gammaUniformC 0)
      (-exp w/(exp w-1)^2 + ((exp w-1)/gammaUniformEtaOnLog w)/gammaUniformEtaOnLog w^2) w := by
    have h1 : HasDerivAt (fun v => 1/(exp v-1)) (-exp w/(exp w-1)^2) w := by
      have := ((Complex.hasDerivAt_exp w).sub_const 1).fun_inv hE
      simpa [one_div, neg_div] using this
    have h2 : HasDerivAt (fun v => 1/gammaUniformEtaOnLog v)
        (-((exp w-1)/gammaUniformEtaOnLog w)/gammaUniformEtaOnLog w^2) w := by
      have := (gammaUniformEta_derivative hw hw0).fun_inv hη
      simpa [one_div, neg_div] using this
    have := h1.sub h2
    refine (this.congr_of_eventuallyEq ?_).congr_deriv (by ring)
    filter_upwards [isOpen_compl_singleton.mem_nhds hw0] with v hv
    exact h0 v hv
  rw [show (1:ℕ) = 0+1 from rfl, gammaUniformC]
  simp only [hw0, ↓reduceIte]
  rw [hD.deriv, incG_gammaStirlingCoeff_one]
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `gammaUniformC 0 w=1/(exp
w-1)-1/gammaUniformEtaOnLog w ∧ gammaUniformC 1 w=1/gammaUniformEtaOnLog w^3-1/(exp
w-1)^3-1/(exp w-1)^2-1/(12*(exp w-1))`. -/
@[dlmf 8.12.E9]
theorem gammaUniformC_first {w : ℂ} (hw : |w.im| < 2*π) (hw0 : w ≠ 0) :
    gammaUniformC 0 w=1/(exp w-1)-1/gammaUniformEtaOnLog w ∧ gammaUniformC 1 w=1/gammaUniformEtaOnLog w^3-1/(exp w-1)^3-1/(exp w-1)^2-1/(12*(exp w-1)) :=
  incG_gammaUniformC_first hw hw0

/-- The normalized η coordinate is holomorphic throughout the zero-free strip. -/
theorem incG_gammaUniformEta_analyticOnNhd :
    AnalyticOnNhd ℂ gammaUniformEtaOnLog incG_strip := by
  refine (show DifferentiableOn ℂ gammaUniformEtaOnLog incG_strip from ?_).analyticOnNhd
    incG_strip_isOpen
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    exact gammaUniformEta_normalization.1.differentiableAt.differentiableWithinAt
  · exact (gammaUniformEta_derivative hw hw0).differentiableAt.differentiableWithinAt

/-- The derivative of η has no zeros in the strip. -/
theorem incG_gammaUniformEta_deriv_ne_zero {w : ℂ} (hw : w ∈ incG_strip) :
    deriv gammaUniformEtaOnLog w ≠ 0 := by
  by_cases hw0 : w = 0
  · subst w
    rw [gammaUniformEta_normalization.1.deriv]
    exact one_ne_zero
  · rw [(gammaUniformEta_derivative hw hw0).deriv]
    exact div_ne_zero (incG_exp_sub_one_ne_zero hw hw0)
      (incG_gammaUniformEta_ne_zero hw hw0)

/-- η has a normalized analytic inverse in some neighborhood of zero. -/
theorem incG_gammaUniformEta_exists_local_inverse :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ HasDerivAt f 1 0 ∧ f 0 = 0 ∧
      (∀ᶠ w in 𝓝 (0 : ℂ), f (gammaUniformEtaOnLog w) = w) ∧
      ∀ᶠ η in 𝓝 (0 : ℂ), gammaUniformEtaOnLog (f η) = η := by
  have ha := incG_gammaUniformEta_analyticOnNhd 0 incG_zero_mem_strip
  have hd := incG_gammaUniformEta_deriv_ne_zero incG_zero_mem_strip
  have hs := ha.hasStrictDerivAt
  have hl := hs.eventually_left_inverse hd
  refine ⟨hs.localInverse _ _ _ hd, ?_, ?_, ?_, hl, ?_⟩
  · simpa only [gammaUniformEta_normalization.2] using ha.analyticAt_localInverse hd
  · simpa only [gammaUniformEta_normalization.1.deriv,
      gammaUniformEta_normalization.2, inv_one] using (hs.to_localInverse hd).hasDerivAt
  · simpa only [gammaUniformEta_normalization.2] using hl.self_of_nhds
  · simpa only [gammaUniformEta_normalization.2] using hs.eventually_right_inverse hd

/-- Uniform large-a filter with independently bounded log arguments of a and λ. -/
def gammaUniformFilter (α β : ℝ) : Filter (ℂ × ℂ) :=
  comap (fun p : ℂ × ℂ => Real.exp p.1.re) atTop ⊓ 𝓟 {p : ℂ × ℂ | |p.1.im| ≤ α ∧ |p.2.im| ≤ β}

/-- Formula under the stated hypotheses: `IsBigO (gammaUniformFilter (π-δ) (2*π-ε)) (fun p =>
Real.sqrt (2*π)*exp (p.1/2)*exp (exp p.1*gammaUniformEtaOnLog p.2^2/2)*gammaUniformS (exp p.1)
p.2-∑ k ∈ Finset.range N, gammaUniformC k p.2*exp (-(k : ℂ)*p.1)) (fun p => exp (-(N :
ℂ)*p.1))`. -/
@[dlmf 8.12.E7]
theorem gammaUniformS_uniform_expansion {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) (hε : 0 < ε) (hε1 : ε < 2*π) (N : ℕ) :
    IsBigO (gammaUniformFilter (π-δ) (2*π-ε)) (fun p => Real.sqrt (2*π)*exp (p.1/2)*exp (exp p.1*gammaUniformEtaOnLog p.2^2/2)*gammaUniformS (exp p.1) p.2-∑ k ∈ Finset.range N, gammaUniformC k p.2*exp (-(k : ℂ)*p.1)) (fun p => exp (-(N : ℂ)*p.1)) := by
  sorry

/-- Formula under the stated hypotheses: `IsBigO (gammaUniformFilter (π-δ) (2*π-ε)) (fun p =>
Real.sqrt (2*π)*exp (p.1/2)*exp (-exp p.1*gammaUniformEtaOnLog p.2^2/2)*gammaUniformT (exp
p.1) p.2-∑ k ∈ Finset.range N, (-1 : ℂ)^k*gammaUniformC k p.2*exp (-(k : ℂ)*p.1)) (fun p =>
exp (-(N : ℂ)*p.1))`. -/
@[dlmf 8.12.E8]
theorem gammaUniformT_uniform_expansion {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) (hε : 0 < ε) (hε1 : ε < 2*π) (N : ℕ) :
    IsBigO (gammaUniformFilter (π-δ) (2*π-ε)) (fun p => Real.sqrt (2*π)*exp (p.1/2)*exp (-exp p.1*gammaUniformEtaOnLog p.2^2/2)*gammaUniformT (exp p.1) p.2-∑ k ∈ Finset.range N, (-1 : ℂ)^k*gammaUniformC k p.2*exp (-(k : ℂ)*p.1)) (fun p => exp (-(N : ℂ)*p.1)) := by
  sorry

/-- The normalized analytic inverse of η on its Maclaurin disk. -/
def gammaUniformInverseLog  : ℂ → ℂ :=
  Classical.epsilon (fun f : ℂ → ℂ => f 0=0 ∧ deriv f 0=1 ∧ ∀ η : ℂ, ‖η‖ < 2*Real.sqrt π → DifferentiableAt ℂ f η ∧ |(f η).im| < 2*π ∧ gammaUniformEtaOnLog (f η)=η)

/-- Inverse λ-series coefficients α_n. -/
def gammaUniformAlpha (n : ℕ) : ℂ :=
  iteratedDeriv n (fun η => exp (gammaUniformInverseLog η)) 0/(n.factorial : ℂ)

/-- Maclaurin coefficients d_{k,n}. -/
def gammaUniformD (k n : ℕ) : ℂ :=
  iteratedDeriv n (fun η => gammaUniformC k (gammaUniformInverseLog η)) 0/(n.factorial : ℂ)

/-- A bounded image of the saddle coordinate in the closed strip has bounded preimage. -/
theorem gammaInv_norm_bound {w : ℂ} {M : ℝ} (hw : |w.im| ≤ 2*π) (hF : ‖exp w-1-w‖ ≤ M) :
    ‖w‖ ≤ M+4*π+2 := by
  have hnorm := norm_le_abs_re_add_abs_im w
  have hexp : Real.exp w.re ≤ M+1+‖w‖ := by
    rw [← norm_exp]
    calc ‖exp w‖ = ‖(exp w-1-w)+(1+w)‖ := by ring_nf
      _ ≤ ‖exp w-1-w‖+‖1+w‖ := norm_add_le _ _
      _ ≤ M+(1+‖w‖) := add_le_add hF (by simpa using norm_add_le (1:ℂ) w)
      _ = _ := by ring
  rcases le_or_gt w.re 0 with hx | hx
  · have h0 : ‖w‖ ≤ Real.exp w.re+1+M := by
      calc ‖w‖ = ‖exp w-1-(exp w-1-w)‖ := by ring_nf
        _ ≤ ‖exp w-1‖+‖exp w-1-w‖ := norm_sub_le _ _
        _ ≤ (‖exp w‖+‖(1:ℂ)‖)+M := add_le_add (norm_sub_le _ _) hF
        _ = _ := by rw [norm_exp, norm_one]
    have he : Real.exp w.re ≤ 1 := Real.exp_le_one_iff.mpr hx
    linarith [Real.pi_pos]
  · have hn : ‖w‖ ≤ w.re+2*π := by
      calc ‖w‖ ≤ |w.re|+|w.im| := hnorm
        _ ≤ w.re+2*π := by rw [abs_of_pos hx]; linarith
    have hq := Real.quadratic_le_exp_of_nonneg hx.le
    have hxB : w.re ≤ M+2*π+1 := by nlinarith [sq_nonneg (M+2*π)]
    linarith

/-- Points on the strip boundary map outside the Maclaurin disk. -/
theorem gammaInv_boundary_norm {w : ℂ} (hw : |w.im|=2*π) :
    2*π ≤ ‖exp w-1-w‖ := by
  have hsin : Real.sin w.im = 0 := by
    rcases abs_eq (by positivity : (0:ℝ) ≤ 2*π) |>.mp hw with h | h
    · rw [h, Real.sin_two_pi]
    · rw [h, Real.sin_neg, Real.sin_two_pi, neg_zero]
  have hi := abs_im_le_norm (exp w-1-w)
  simpa [Complex.exp_im, hsin, hw] using hi

/-- A sublevel set below the first critical image stays compactly inside the strip. -/
theorem gammaInv_compact_sublevel {M : ℝ} (_hM : 0 ≤ M) (hMπ : M < 2*π) :
    IsCompact {w : ℂ | |w.im| ≤ 2*π ∧ ‖exp w-1-w‖ ≤ M} ∧
      {w : ℂ | |w.im| ≤ 2*π ∧ ‖exp w-1-w‖ ≤ M} ⊆ incG_strip := by
  have hc : IsClosed {w : ℂ | |w.im| ≤ 2*π ∧ ‖exp w-1-w‖ ≤ M} :=
    (isClosed_le (f := fun w : ℂ => |w.im|) (g := fun _ => 2*π)
      (by fun_prop) continuous_const).inter
      (isClosed_le (f := fun w : ℂ => ‖exp w-1-w‖) (g := fun _ => M)
        (by fun_prop) continuous_const)
  constructor
  · refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨hc, ?_⟩
    refine (Metric.isBounded_closedBall (x := (0:ℂ)) (r := M+4*π+2)).subset ?_
    intro w hw
    simpa using gammaInv_norm_bound hw.1 hw.2
  · intro w hw
    change |w.im| < 2*π
    exact lt_of_le_of_ne hw.1 (fun he => not_le.mpr hMπ ((gammaInv_boundary_norm he).trans hw.2))

/-- Compact subsets of the inverse disk have compact preimage in the strip. -/
theorem gammaInv_compact_preimage {K : Set ℂ}
    (hKsub : K ⊆ Metric.ball (0:ℂ) (2*Real.sqrt π)) (hK : IsCompact K) :
    IsCompact (incG_strip ∩ gammaUniformEtaOnLog ⁻¹' K) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨η₀, hη₀, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
  have hB : ‖η₀‖ < 2*Real.sqrt π := by simpa using hKsub hη₀
  let M : ℝ := ‖η₀‖^2/2
  have hM : 0 ≤ M := by positivity
  have hMπ : M < 2*π := by
    have hsq := Real.sq_sqrt Real.pi_pos.le
    have hs := Real.sqrt_nonneg π
    have hn := norm_nonneg η₀
    dsimp [M]; nlinarith
  let C : Set ℂ := {w : ℂ | |w.im| ≤ 2*π ∧ ‖exp w-1-w‖ ≤ M}
  obtain ⟨hCc, hCs⟩ := gammaInv_compact_sublevel hM hMπ
  let S : Set ℂ := incG_strip ∩ gammaUniformEtaOnLog ⁻¹' K
  have hSC : S ⊆ C := by
    intro w hw
    refine ⟨hw.1.le, ?_⟩
    rw [← incG_gammaUniformEta_sq hw.1, norm_div, norm_pow, Complex.norm_two]
    dsimp [M]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hmax hw.2) 2) (by norm_num)
  have hclosed : IsClosed S := by
    refine isClosed_of_closure_subset fun w hw => ?_
    have hwC : w ∈ C := hCc.isClosed.closure_subset_iff.mpr hSC hw
    have hws : w ∈ incG_strip := hCs hwC
    refine ⟨hws, ?_⟩
    have hcont := (incG_gammaUniformEta_analyticOnNhd w hws).continuousAt
    have hi := mem_closure_image hcont hw
    have hmap : gammaUniformEtaOnLog '' S ⊆ K := by
      rintro _ ⟨v, hv, rfl⟩
      exact hv.2
    change gammaUniformEtaOnLog w ∈ K
    simpa only [hK.isClosed.closure_eq] using closure_mono hmap hi
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hCc.isBounded.subset hSC⟩

/-- The saddle coordinate is locally a homeomorphism on its zero-free strip. -/
theorem gammaInv_isLocalHomeomorphOn : IsLocalHomeomorphOn gammaUniformEtaOnLog incG_strip := by
  refine IsLocalHomeomorphOn.mk _ _ fun w hw => ?_
  have hs := (incG_gammaUniformEta_analyticOnNhd w hw).hasStrictDerivAt
  have hd := incG_gammaUniformEta_deriv_ne_zero hw
  have he := hs.hasStrictFDerivAt_equiv hd
  exact ⟨he.toOpenPartialHomeomorph _, he.mem_toOpenPartialHomeomorph_source,
    fun v _ => by rw [he.toOpenPartialHomeomorph_coe]⟩

/-- The saddle coordinate is a covering over the entire Maclaurin disk, using the
Tau Ceti contributors' proper local-homeomorphism criterion. -/
theorem gammaInv_isCoveringMapOn :
    IsCoveringMapOn (fun w : incG_strip => gammaUniformEtaOnLog w)
      (Metric.ball (0:ℂ) (2*Real.sqrt π)) := by
  have hl : IsLocalHomeomorph (fun w : incG_strip => gammaUniformEtaOnLog w) :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr <|
      gammaInv_isLocalHomeomorphOn.comp
        incG_strip_isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
        (fun w _ => w.property)
  refine IsCoveringMapOn.of_isLocalHomeomorph_of_isCompact_preimage Metric.isOpen_ball
    (hl.isLocalHomeomorphOn.mono (subset_univ _)) fun K hKs hK => ?_
  rw [IsEmbedding.subtypeVal.isCompact_iff]
  have heq : Subtype.val '' ((fun w : incG_strip => gammaUniformEtaOnLog w) ⁻¹' K) =
      incG_strip ∩ gammaUniformEtaOnLog ⁻¹' K := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨v.property, hv⟩
    · rintro ⟨hw, hη⟩; exact ⟨⟨w, hw⟩, hη, rfl⟩
  rw [heq]
  exact gammaInv_compact_preimage hKs hK

/-- The local inverse continues single-valuedly over its full Maclaurin disk. -/
theorem gammaInv_exists_global : ∃ f : ℂ → ℂ,
    f 0=0 ∧ deriv f 0=1 ∧ ∀ η : ℂ, ‖η‖ < 2*Real.sqrt π →
      DifferentiableAt ℂ f η ∧ |(f η).im| < 2*π ∧ gammaUniformEtaOnLog (f η)=η := by
  classical
  let D : Set ℂ := Metric.ball 0 (2*Real.sqrt π)
  have hR : (0:ℝ) < 2*Real.sqrt π := by positivity
  have h0 : (0:ℂ) ∈ D := by simpa [D] using hR
  have : ContractibleSpace D := (convex_ball (0:ℂ) (2*Real.sqrt π)).contractibleSpace ⟨0,h0⟩
  have : LocallyPathConnectedSpace D := Metric.isOpen_ball.locallyPathConnectedSpace
  let g : C(D,ℂ) := ⟨Subtype.val,continuous_subtype_val⟩
  let d₀ : D := ⟨0,h0⟩
  let e₀ : incG_strip := ⟨0,incG_zero_mem_strip⟩
  have he : gammaUniformEtaOnLog e₀ = g d₀ := gammaUniformEta_normalization.2
  obtain ⟨G,⟨hG0,hG⟩,_⟩ := gammaInv_isCoveringMapOn.existsUnique_continuousMap_lifts g he
    (fun η => η.property)
  let f : ℂ → ℂ := fun η => if hη : η ∈ D then (G ⟨η,hη⟩ : ℂ) else 0
  have hf (η : ℂ) (hη : η ∈ D) : f η = (G ⟨η,hη⟩ : ℂ) := by simp only [f, dite_eq_left hη]
  have hfc : ContinuousOn f D := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert continuous_subtype_val.comp G.continuous using 1
    funext η
    exact hf η η.property
  have hf0 : f 0 = 0 := by
    rw [hf 0 h0]
    exact congrArg Subtype.val hG0
  have hspec (η : ℂ) (hη : η ∈ D) :
      |(f η).im| < 2*π ∧ gammaUniformEtaOnLog (f η)=η := by
    rw [hf η hη]
    refine ⟨(G ⟨η,hη⟩).property, ?_⟩
    exact congrFun hG ⟨η,hη⟩
  have hderiv (η : ℂ) (hη : η ∈ D) :
      HasStrictDerivAt f (deriv gammaUniformEtaOnLog (f η))⁻¹ η := by
    have hws : f η ∈ incG_strip := (hspec η hη).1
    have hs := (incG_gammaUniformEta_analyticOnNhd (f η) hws).hasStrictDerivAt
    refine HasStrictDerivAt.of_local_left_inverse
      (hfc.continuousAt (Metric.isOpen_ball.mem_nhds hη)) hs
      (incG_gammaUniformEta_deriv_ne_zero hws) ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hη] with v hv
    exact (hspec v hv).2
  refine ⟨f,hf0,?_,?_⟩
  · rw [(hderiv 0 h0).hasDerivAt.deriv, hf0, gammaUniformEta_normalization.1.deriv, inv_one]
  · intro η hη
    have hη' : η ∈ D := by simpa [D] using hη
    exact ⟨(hderiv η hη').hasDerivAt.differentiableAt, hspec η hη'⟩

/-- Estimate under the stated parameter and domain assumptions: `gammaUniformInverseLog 0=0 ∧
deriv gammaUniformInverseLog 0=1 ∧ ∀ η : ℂ, ‖η‖ < 2*Real.sqrt π → DifferentiableAt ℂ
gammaUniformInverseLog η ∧ |(gammaUniformInverseLog η).im| < 2*π ∧ gammaUniformEtaOnLog
(gammaUniformInverseLog η)=η`. -/
@[dlmf 8.12.E13]
theorem gammaUniformInverseLog_spec  :
    gammaUniformInverseLog 0=0 ∧ deriv gammaUniformInverseLog 0=1 ∧ ∀ η : ℂ, ‖η‖ < 2*Real.sqrt π → DifferentiableAt ℂ gammaUniformInverseLog η ∧ |(gammaUniformInverseLog η).im| < 2*π ∧ gammaUniformEtaOnLog (gammaUniformInverseLog η)=η := by
  exact Classical.epsilon_spec gammaInv_exists_global

/-- The series with terms `(fun n : ℕ => gammaUniformD k n*η^n)` converges to `(gammaUniformC k
(gammaUniformInverseLog η))`. -/
@[dlmf 8.12.E11]
theorem gammaUniformC_maclaurin (k : ℕ) {η : ℂ} (hη : ‖η‖ < 2*Real.sqrt π) :
    HasSum (fun n : ℕ => gammaUniformD k n*η^n) (gammaUniformC k (gammaUniformInverseLog η)) := by
  sorry

/-- Estimate under the stated parameter and domain assumptions: `gammaUniformD 0 0 = -1/3 ∧ (1 ≤ n
→ gammaUniformD 0 n=(n+2)*gammaUniformAlpha (n+2)) ∧ gammaUniformD (k+1) n=(-1 :
ℂ)^(k+1)*gammaStirlingCoeff (k+1)*gammaUniformD 0 n+(n+2)*gammaUniformD k (n+2)`. -/
@[dlmf 8.12.E12]
theorem gammaUniformD_recurrence (k n : ℕ) :
    gammaUniformD 0 0 = -1/3 ∧ (1 ≤ n → gammaUniformD 0 n=(n+2)*gammaUniformAlpha (n+2)) ∧ gammaUniformD (k+1) n=(-1 : ℂ)^(k+1)*gammaStirlingCoeff (k+1)*gammaUniformD 0 n+(n+2)*gammaUniformD k (n+2) := by
  sorry

/-- The series with terms `(fun n : ℕ => gammaUniformAlpha n*η^n)` converges to `(exp
(gammaUniformInverseLog η))`. -/
@[dlmf 8.12.E13]
theorem gammaUniformAlpha_hasSum {η : ℂ} (hη : ‖η‖ < 2*Real.sqrt π) :
    HasSum (fun n : ℕ => gammaUniformAlpha n*η^n) (exp (gammaUniformInverseLog η)) := by
  have hd : DifferentiableOn ℂ (fun η => exp (gammaUniformInverseLog η))
      (Metric.ball 0 (2*Real.sqrt π)) := by
    intro z hz
    have hz' : ‖z‖ < 2*Real.sqrt π := by simpa using hz
    exact ((gammaUniformInverseLog_spec.2.2 z hz').1.cexp).differentiableWithinAt
  have h := Complex.hasSum_taylorSeries_on_ball hd (by simpa using hη)
  convert h using 1
  funext n
  simp only [gammaUniformAlpha, sub_zero, smul_eq_mul, div_eq_mul_inv]
  ring

/-- Estimate under the stated parameter and domain assumptions: `∀ n < 6, gammaUniformAlpha
(n+3)=([1/36,-1/270,1/4320,1/17010,-139/5443200,1/204120] : List ℂ)[n]!`. -/
@[dlmf 8.12.E14]
theorem gammaUniformAlpha_printed  :
    ∀ n < 6, gammaUniformAlpha (n+3)=([1/36,-1/270,1/4320,1/17010,-139/5443200,1/204120] : List ℂ)[n]! := by
  have hode {η : ℂ} (hη : ‖η‖ < 2*Real.sqrt π) :
      deriv (fun η => exp (gammaUniformInverseLog η)) η *
        (exp (gammaUniformInverseLog η)-1) = η*exp (gammaUniformInverseLog η) := by
    have hf := (gammaUniformInverseLog_spec.2.2 η hη).1.hasDerivAt
    have h1 := ((hf.cexp.sub_const 1).sub hf)
    have he : (fun z => exp (gammaUniformInverseLog z)-1-gammaUniformInverseLog z) =ᶠ[𝓝 η]
        fun z => z^2/2 := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (show η ∈ Metric.ball 0 (2*Real.sqrt π) by simpa using hη)] with z hz
      obtain ⟨_, hs, he⟩ := gammaUniformInverseLog_spec.2.2 z (by simpa using hz)
      simpa only [he] using (gammaUniformEta_equation hs).symm
    have h2 : HasDerivAt (fun z : ℂ => z^2/2) η η := by
      convert ((hasDerivAt_id η).fun_pow 2).div_const 2 using 1 <;> simp
    have h := h1.unique (h2.congr_of_eventuallyEq he)
    rw [hf.cexp.deriv]
    linear_combination exp (gammaUniformInverseLog η)*h
  let f : ℂ → ℂ := fun η => exp (gammaUniformInverseLog η)
  have hd : DifferentiableOn ℂ f (Metric.ball 0 (2*Real.sqrt π)) := by
    intro z hz
    exact ((gammaUniformInverseLog_spec.2.2 z (by simpa using hz)).1.cexp).differentiableWithinAt
  have ha : AnalyticAt ℂ f 0 := hd.analyticOnNhd Metric.isOpen_ball 0 (by
    simpa using (show (0:ℝ) < 2*Real.sqrt π by positivity))
  have hzero : f 0 = 1 := by simp [f, gammaUniformInverseLog_spec.1]
  have hone : deriv f 0 = 1 := by
    have h := (gammaUniformInverseLog_spec.2.2 0 (by simp; positivity)).1.hasDerivAt.cexp
    simpa only [gammaUniformInverseLog_spec.1, gammaUniformInverseLog_spec.2.1,
      Complex.exp_zero, mul_one] using h.deriv
  have he : (fun z => deriv f z * (f z - 1)) =ᶠ[𝓝 0] fun z => z*f z := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) (show (0:ℝ) < 2*Real.sqrt π by positivity)] with z hz
    exact hode (by simpa using hz)
  have hrec (n : ℕ) :
      (∑ i ∈ Finset.range (n+1), (n.choose i : ℂ)*iteratedDeriv (i+1) f 0 *
        (iteratedDeriv (n-i) f 0 - if n-i=0 then 1 else 0)) =
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℂ)*(if i=1 then 1 else 0)*
        iteratedDeriv (n-i) f 0 := by
    have h := he.iteratedDeriv_eq n
    rw [iteratedDeriv_fun_mul (f := deriv f) (g := fun z => f z - 1)
      ha.deriv.contDiffAt (ha.sub analyticAt_const).contDiffAt,
      iteratedDeriv_fun_mul (f := fun z => z) (g := f) contDiffAt_id ha.contDiffAt] at h
    simpa only [← iteratedDeriv_succ', iteratedDeriv_fun_sub ha.contDiffAt contDiffAt_const,
      iteratedDeriv_const, iteratedDeriv_fun_id_zero] using h
  have h0 : iteratedDeriv 0 f 0 = 1 := hzero
  have h1 : iteratedDeriv 1 f 0 = 1 := by simpa only [iteratedDeriv_one] using hone
  have h2 : iteratedDeriv 2 f 0 = 2/3 := by
    have h := hrec 2
    norm_num [Finset.sum_range_succ, Nat.choose, h0, h1] at h
    linear_combination h/3
  have h3 : iteratedDeriv 3 f 0 = 1/6 := by
    have h := hrec 3
    norm_num [Finset.sum_range_succ, Nat.choose, h0, h1, h2] at h
    linear_combination h/4
  have h4 : iteratedDeriv 4 f 0 = -4/45 := by
    have h := hrec 4
    norm_num [Finset.sum_range_succ, Nat.choose, h0, h1, h2, h3] at h
    linear_combination h/5
  have h5 : iteratedDeriv 5 f 0 = 1/36 := by
    have h := hrec 5
    norm_num [Finset.sum_range_succ, Nat.choose, h0, h1, h2, h3, h4] at h
    linear_combination h/6
  have h6 : iteratedDeriv 6 f 0 = 8/189 := by
    have h := hrec 6
    norm_num [Finset.sum_range_succ, Nat.choose, h0, h1, h2, h3, h4, h5] at h
    linear_combination h/7
  have h7 : iteratedDeriv 7 f 0 = -139/1080 := by
    have h := hrec 7
    norm_num [Finset.sum_range_succ, Nat.choose, h0, h1, h2, h3, h4, h5, h6] at h
    linear_combination h/8
  have h8 : iteratedDeriv 8 f 0 = 16/81 := by
    have h := hrec 8
    norm_num [Finset.sum_range_succ, Nat.choose, h0, h1, h2, h3, h4, h5, h6, h7] at h
    linear_combination h/9
  dsimp only [f] at h3 h4 h5 h6 h7 h8
  intro n hn
  interval_cases n <;> norm_num [gammaUniformAlpha, h3, h4, h5, h6, h7, h8, Nat.factorial]

/-- Estimate under the stated parameter and domain assumptions: `∀ n < 6, gammaUniformC n
0=([-1/3,-1/540,25/6048,101/155520,-3184811/3695155200,-2745493/8151736320] : List ℂ)[n]!`. -/
@[dlmf 8.12.E17]
theorem gammaUniformC_at_zero_printed  :
    ∀ n < 6, gammaUniformC n 0=([-1/3,-1/540,25/6048,101/155520,-3184811/3695155200,-2745493/8151736320] : List ℂ)[n]! := by
  sorry

/-- Identity under the stated parameter and domain assumptions: `HasAsymptoticExpansion (logSector
(π-δ)) (fun k w => exp (-((k : ℂ)+1/2)*w)/Real.sqrt (2*π)) (fun k => gammaUniformC k 0) (fun w
=> normIncGammaQOnLog (exp w) w-1/2)`. -/
@[dlmf 8.12.E15]
theorem normIncGammaQ_diagonal_uniform_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) :
    HasAsymptoticExpansion (logSector (π-δ)) (fun k w => exp (-((k : ℂ)+1/2)*w)/Real.sqrt (2*π)) (fun k => gammaUniformC k 0) (fun w => normIncGammaQOnLog (exp w) w-1/2) := by
  sorry

/-- Identity under the stated parameter and domain assumptions: `HasAsymptoticExpansion (logSector
(π-δ)) (fun k w => exp (-((k : ℂ)+1/2)*w)/Real.sqrt (2*π)) (fun k => -I*(-1 :
ℂ)^k*gammaUniformC k 0) (fun w => -exp (ε*π*I*exp w)*Gamma (exp
w+1)/(2*π*I)*upperIncGammaOnLog (-exp w) (w+ε*π*I)-ε/2)`. -/
@[dlmf 8.12.E16]
theorem normIncGammaQ_negative_diagonal_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    HasAsymptoticExpansion (logSector (π-δ)) (fun k w => exp (-((k : ℂ)+1/2)*w)/Real.sqrt (2*π)) (fun k => -I*(-1 : ℂ)^k*gammaUniformC k 0) (fun w => -exp (ε*π*I*exp w)*Gamma (exp w+1)/(2*π*I)*upperIncGammaOnLog (-exp w) (w+ε*π*I)-ε/2) := by
  sorry

/-- The parabolic transition function d(χ). -/
@[dlmf 8.12.E19]
def gammaParisD (χ : ℂ) : ℂ :=
  Real.sqrt (π/2)*exp (χ^2/2)*erfc (χ/Real.sqrt 2)

/-- Transition coefficients extracted in the positive square-root variable. -/
def gammaParisRawCoeff (upper : Bool) (χ : ℂ) (k : ℕ) : ℂ :=
  asymptoticCoeff (fun t : ℝ => let z : ℂ := t^2; let a := z-χ*t; Gamma a*z^(1/2-a)*exp z*(if upper then normIncGammaQContinued a z else normIncGammaPContinued a z)) k

/-- The coefficients A_k(χ) fixed by the two complementary transitions. -/
def gammaParisA (k : ℕ) (χ : ℂ) : ℂ :=
  (gammaParisRawCoeff true χ k+gammaParisRawCoeff false χ k)/(gammaParisD χ+gammaParisD (-χ))

/-- The coefficients B_k(χ). -/
def gammaParisB (k : ℕ) (χ : ℂ) : ℂ :=
  gammaParisD χ*gammaParisA k χ-gammaParisRawCoeff true χ k

/-- Identity under the stated parameter and domain assumptions: `gammaParisA 0 χ=1 ∧ gammaParisB 0
χ=0 ∧ gammaParisA 1 χ=χ/2+χ^3/6 ∧ gammaParisB 1 χ=1/3+χ^2/6`. -/
@[dlmf 8.12.E20]
theorem gammaParis_printed (χ : ℂ) :
    gammaParisA 0 χ=1 ∧ gammaParisB 0 χ=0 ∧ gammaParisA 1 χ=χ/2+χ^3/6 ∧ gammaParisB 1 χ=1/3+χ^2/6 := by
  sorry

/-- Uniformity is specified for bounded transition variable χ and closed right-half-plane sectors. -/
@[dlmf 8.12.E18]
theorem gammaParis_uniform_expansion (upper : Bool) {δ B : ℝ} (hδ : 0 < δ) (hδ1 : δ < π/2) (hB : 0 < B) (N : ℕ) :
    IsBigO (comap (fun p : ℂ × ℂ => Real.exp p.1.re) atTop ⊓ 𝓟 {p : ℂ × ℂ | |p.1.im| ≤ π/2-δ ∧ ‖p.2‖ ≤ B ∧ (if upper then 0 ≤ (p.2*exp (p.1/2)).re else (p.2*exp (p.1/2)).re ≤ 0)}) (fun p => let a := exp p.1-p.2*exp (p.1/2); let ε : ℂ := if upper then 1 else -1; Gamma a*exp ((1/2-a)*p.1+exp p.1)*(if upper then normIncGammaQContinued a (exp p.1) else normIncGammaPContinued a (exp p.1))-gammaParisD (ε*p.2)*(∑ k ∈ Finset.range N, gammaParisA k p.2*exp (-(k : ℂ)*p.1/2))+ε*(∑ k ∈ Finset.range N, gammaParisB k p.2*exp (-(k : ℂ)*p.1/2))) (fun p => exp (-(N : ℂ)*p.1/2)) := by
  sorry

/-- The inverse Q, including x=∞ at q=0. -/
@[dlmf 8.12.E21]
def gammaQInverse (a q : ℝ) : ℝ≥0∞ :=
  if q=0 then ∞ else if q=1 then 0 else ENNReal.ofReal (Classical.epsilon (fun x : ℝ => 0 ≤ x ∧ (normIncGammaQContinued a x).re=q))

/-- The continued `P(a,x)` for real `a > 0`, `x ≥ 0` is TauCeti's regularized lower Gamma. -/
theorem incG_normIncGammaPContinued_ofReal {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x) :
    normIncGammaPContinued a x = ((TauCeti.lowerIncompleteGamma a x / Real.Gamma a : ℝ) : ℂ) := by
  rcases hx.eq_or_lt with h0 | h0
  · subst h0
    rw [TauCeti.lowerIncompleteGamma_eq_zero_of_nonpos_right a le_rfl, normIncGammaPContinued,
      ofReal_zero, zero_cpow (ofReal_ne_zero.mpr ha.ne')]
    simp
  · have ha' : ∀ n : ℕ, (a:ℂ) ≠ -n := fun n h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    rw [normIncGammaPContinued_eq ha', normIncGammaP, lowerIncGamma_ofReal ha h0,
      Complex.Gamma_ofReal]
    push_cast; rfl

/-- Existence of a real point `x ≥ 0` with `Q(a,x) = q` for `0 < q < 1`. -/
theorem incG_exists_normIncGammaQ_eq {a : ℝ} (ha : 0 < a) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ∃ x : ℝ, 0 ≤ x ∧ (normIncGammaQContinued a x).re = q := by
  set f : ℝ → ℝ := fun x => TauCeti.lowerIncompleteGamma a x / Real.Gamma a
  have hf : Continuous f := (TauCeti.continuous_lowerIncompleteGamma a).div_const _
  have hG := Real.Gamma_pos_of_pos ha
  have hlim : Tendsto f atTop (𝓝 1) := by
    have := (TauCeti.tendsto_lowerIncompleteGamma_atTop ha).div_const (Real.Gamma a)
    rwa [div_self hG.ne'] at this
  obtain ⟨R, hR⟩ := (hlim.eventually (lt_mem_nhds (show 1-q < 1 by linarith))).exists_forall_of_atTop
  set R' := max R 0
  have hR' := hR R' (le_max_left _ _)
  have h0 : f 0 = 0 := by
    simp [f]
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc (le_max_right R 0) hf.continuousOn
    ⟨by rw [h0]; linarith, hR'.le⟩
  refine ⟨x, hx.1, ?_⟩
  rw [normIncGammaQContinued, incG_normIncGammaPContinued_ofReal ha hx.1, sub_re, one_re, ofReal_re]
  change 1 - f x = q
  rw [hfx]; ring

/-- Identity under the stated parameter and domain assumptions: `(if gammaQInverse a q=∞ then 0
else (normIncGammaQContinued a (gammaQInverse a q).toReal).re)=q ∧ (q ≠ 0 → gammaQInverse a q
≠ ∞)`. -/
@[dlmf 8.12.E21]
theorem gammaQInverse_spec {a q : ℝ} (ha : 0 < a) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (if gammaQInverse a q=∞ then 0 else (normIncGammaQContinued a (gammaQInverse a q).toReal).re)=q ∧ (q ≠ 0 → gammaQInverse a q ≠ ∞) := by
  rcases hq.eq_or_lt with h0 | h0
  · subst h0; simp [gammaQInverse]
  rcases hq1.eq_or_lt with h1 | h1
  · subst h1
    have : gammaQInverse a 1 = 0 := by simp [gammaQInverse]
    simp only [this, ENNReal.zero_ne_top, ite_false, ENNReal.toReal_zero, ofReal_zero,
      normIncGammaQContinued, normIncGammaPContinued, zero_cpow (ofReal_ne_zero.mpr ha.ne')]
    simp
  have hex := incG_exists_normIncGammaQ_eq ha h0 h1
  have hs := Classical.epsilon_spec (p := fun x : ℝ => 0 ≤ x ∧ (normIncGammaQContinued a x).re = q) hex
  have hg : gammaQInverse a q = ENNReal.ofReal (Classical.epsilon (fun x : ℝ => 0 ≤ x ∧ (normIncGammaQContinued a x).re=q)) := by
    simp [gammaQInverse, h0.ne', h1.ne]
  rw [hg]
  simp only [ENNReal.ofReal_ne_top, ite_false, ENNReal.toReal_ofReal hs.1]
  exact ⟨hs.2, fun _ => ENNReal.ofReal_ne_top⟩

/-- Estimate under the stated parameter and domain assumptions: `∃ c : ℕ → ℝ, (∀ n < 5, c
n=([1,-1/3,8/405,184/25515,2248/3444525] : List ℝ)[n]!) ∧ HasAsymptoticExpansion atTop (fun n
(a : ℝ) => a^((1 : ℤ)-n)) c (fun a => (gammaQInverse a (1/2)).toReal)`. -/
@[dlmf 8.12.E22]
theorem gammaQInverse_median_asymptotic  :
    ∃ c : ℕ → ℝ, (∀ n < 5, c n=([1,-1/3,8/405,184/25515,2248/3444525] : List ℝ)[n]!) ∧ HasAsymptoticExpansion atTop (fun n (a : ℝ) => a^((1 : ℤ)-n)) c (fun a => (gammaQInverse a (1/2)).toReal) := by
  sorry

end DLMF.Confluent
