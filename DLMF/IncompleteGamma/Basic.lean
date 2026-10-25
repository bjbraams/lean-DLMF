/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.Basic
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy

/-!
# Incomplete Gamma continuation, definitions and differential equations, DLMF §8.2

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

open DLMF.Statistical

/-- Upper incomplete Gamma on the logarithmic plane, also at integral a. -/
def upperIncGammaOnLog (a w : ℂ) : ℂ :=
  upperIncGamma a (exp w) - segmentIntegral (fun u => exp (a*u-exp u)) (log (exp w)) w

/-- Lower incomplete Gamma on the logarithmic plane away from its parameter poles. -/
def lowerIncGammaOnLog (a w : ℂ) : ℂ :=
  Gamma a*exp (a*w)*scIncGamma a (exp w)

/-- Analytically continued P; at nonpositive integral a it differs from the old totalized quotient. -/
@[dlmf 8.2.E4]
def normIncGammaPContinued (a z : ℂ) : ℂ :=
  z^a*scIncGamma a z

/-- Analytically continued Q. -/
@[dlmf 8.2.E4]
def normIncGammaQContinued (a z : ℂ) : ℂ :=
  1-normIncGammaPContinued a z

/-- Continued P on the logarithmic plane. -/
def normIncGammaPOnLog (a w : ℂ) : ℂ :=
  exp (a*w)*scIncGamma a (exp w)

/-- Continued Q on the logarithmic plane. -/
def normIncGammaQOnLog (a w : ℂ) : ℂ :=
  1-normIncGammaPOnLog a w

/-- normIncGammaPContinued eq. -/
@[dlmf 8.2.E4]
theorem normIncGammaPContinued_eq {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (z : ℂ) :
    normIncGammaPContinued a z=normIncGammaP a z := by
  have h := regularizedConfluent_kummer_transform a (a+1) (-z)
  rw [show a+1-a=1 by ring] at h
  rw [normIncGammaPContinued, normIncGammaP, lowerIncGamma_eq_regularized ha, h, scIncGamma]
  field_simp [Gamma_ne_zero ha]

/-- normIncGammaQContinued eq. -/
@[dlmf 8.2.E4]
theorem normIncGammaQContinued_eq {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ≠ 0) :
    normIncGammaQContinued a z=normIncGammaQ a z := by
  have h := normIncGammaP_add_normIncGammaQ ha hz
  rw [normIncGammaQContinued, normIncGammaPContinued_eq ha]
  linear_combination -h

/-- scIncGamma hasSum exponential. -/
@[dlmf 8.7.E1]
theorem scIncGamma_hasSum_exponential (a z : ℂ) :
    HasSum (fun k : ℕ => exp (-z)*z^k/Gamma (a+k+1)) (scIncGamma a z) := by
  have hs := ((hasFPowerSeriesOnBall_regularizedConfluent 1 (a+1)).hasSum_mul_pow
    (by simp : z ∈ Metric.eball (0:ℂ) ⊤)).mul_left (exp (-z))
  change HasSum _ (exp (-z)*regularizedHGFun {1} {a+1} z)
  refine hs.congr_fun fun k => ?_
  rw [regularizedHGFunCoeff_singleton, poch_nat_one, div_mul_eq_div_div,
    div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))]
  rw [show a+1+k=a+k+1 by ring]
  ring

/-- scIncGamma recurrence. -/
@[dlmf 8.8.E4]
theorem scIncGamma_recurrence (a z : ℂ) :
    z*scIncGamma (a+1) z=scIncGamma a z-exp (-z)/Gamma (a+1) := by
  have hs := scIncGamma_hasSum_exponential a z
  have ht := (scIncGamma_hasSum_exponential (a+1) z).mul_left z
  have hg (k : ℕ) : exp (-z)*z^(k+1)/Gamma (a+((k+1:ℕ):ℂ)+1)=
      z*(exp (-z)*z^k/Gamma (a+1+k+1)) := by
    rw [show a+((k+1:ℕ):ℂ)+1=a+1+k+1 by push_cast; ring, pow_succ]
    ring
  have htail := (hasSum_nat_add_iff' 1).mpr hs
  simp only [Finset.sum_range_one, pow_zero, mul_one, Nat.cast_zero, add_zero] at htail
  have ht' : HasSum (fun k : ℕ => exp (-z)*z^(k+1)/Gamma (a+((k+1:ℕ):ℂ)+1)) (z*scIncGamma (a+1) z) :=
    ht.congr_fun fun k => hg k
  exact ht'.unique htail

/-- normIncGammaPContinued shift up. -/
@[dlmf 8.8.E11]
theorem normIncGammaPContinued_shift_up (n : ℕ) (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    normIncGammaPContinued (a+n) z=normIncGammaPContinued a z - z^a*exp (-z)*(∑ k ∈ Finset.range n, z^k/Gamma (a+k+1)) := by
  have hstep (b : ℂ) : normIncGammaPContinued (b+1) z =
      normIncGammaPContinued b z-z^b*exp (-z)/Gamma (b+1) := by
    unfold normIncGammaPContinued
    rw [cpow_add _ _ hz, cpow_one, mul_assoc, scIncGamma_recurrence]
    ring
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, hstep, ih, Finset.sum_range_succ]
    rw [cpow_add _ _ hz, cpow_natCast]
    ring

/-- normIncGammaQContinued shift up. -/
@[dlmf 8.8.E12]
theorem normIncGammaQContinued_shift_up (n : ℕ) (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    normIncGammaQContinued (a+n) z=normIncGammaQContinued a z + z^a*exp (-z)*(∑ k ∈ Finset.range n, z^k/Gamma (a+k+1)) := by
  rw [normIncGammaQContinued, normIncGammaQContinued, normIncGammaPContinued_shift_up n a hz]
  ring

/-- scIncGamma integral. -/
@[dlmf 8.2.E7]
theorem scIncGamma_integral {a : ℂ} (ha : 0 < a.re) (z : ℂ) :
    scIncGamma a z=1/Gamma a*(∫ t : ℝ in 0..1, (t : ℂ)^(a-1)*exp (-z*t)) := by
  have h := regularizedConfluent_kummer_transform 1 (a+1) z
  rw [show a+1-1=a by ring] at h
  rw [scIncGamma, h, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul,
    regularized_euler_integral ha (by simp), show a+1-a-1=0 by ring, show a+1-a=1 by ring,
    Complex.Gamma_one, mul_one]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [cpow_zero, mul_one]
  ring_nf

/-- lowerIncGamma segment integral. -/
@[dlmf 8.2.E1]
theorem lowerIncGamma_segment_integral {a : ℂ} (ha : 0 < a.re) {z : ℂ} (hz : z ∈ slitPlane) :
    lowerIncGamma a z=primitive (fun t => t^(a-1)*exp (-t)) z := by
  have ha' : ∀ k : ℕ, a ≠ -k := fun k hk => by
    have := congrArg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hz0 := slitPlane_ne_zero hz
  have hk := regularizedConfluent_kummer_transform a (a+1) (-z)
  rw [show a+1-a=1 by ring, neg_neg] at hk
  have hsc : regularizedHGFun {a} {a+1} (-z) = scIncGamma a z := by
    rw [hk, scIncGamma]
  rw [lowerIncGamma_eq_regularized ha', hsc, scIncGamma_integral ha, primitive, segmentIntegral,
    sub_zero]
  have hint : (∫ t : ℝ in 0..1, (0 + (t:ℂ) * z) ^ (a - 1) * exp (-(0 + (t:ℂ) * z))) =
      z ^ (a-1) * ∫ t : ℝ in 0..1, (t : ℂ)^(a-1)*exp (-z*t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    refine Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    have htp : 0 < t := ht.1
    rw [zero_add, ofReal_mul_cpow_of_pos htp hz0]
    ring_nf
  rw [hint]
  have hza : z ^ a = z * z ^ (a-1) := by
    conv_lhs => rw [show a = 1 + (a - 1) by ring]
    rw [Complex.cpow_add _ _ hz0, Complex.cpow_one]
  rw [hza]
  field_simp [Complex.Gamma_ne_zero ha']

/-- normIncGammaContinued complement. -/
@[dlmf 8.2.E5]
theorem normIncGammaContinued_complement (a z : ℂ) :
    normIncGammaPContinued a z+normIncGammaQContinued a z=1 := by
  simp [normIncGammaQContinued]

/-- Joint entire differentiability asserted in DLMF §8.2(ii). -/
theorem scIncGamma_joint_entire  :
    Differentiable ℂ (fun p : ℂ × ℂ => scIncGamma p.1 p.2) := by
  have hc : Continuous fun p : ℂ × ℂ => scIncGamma p.1 p.2 := by
    unfold scIncGamma
    exact (by fun_prop : Continuous fun p : ℂ × ℂ => exp (-p.2)).mul
      (continuous_regularizedConfluent.comp (f := fun p : ℂ × ℂ => ((1:ℂ), p.1+1, p.2)) (by fun_prop))
  have h1 : ∀ p ∈ (univ : Set (ℂ × ℂ)), DifferentiableAt ℂ (fun a => scIncGamma a p.2) p.1 := by
    intro p _
    unfold scIncGamma
    exact (differentiableAt_const _).mul (analyticAt_regularizedConfluent_comp
      (A := fun _ => (1:ℂ)) (B := fun b => b+1) (differentiable_const _) (by fun_prop) p.2 p.1).differentiableAt
  have h2 : ∀ p ∈ (univ : Set (ℂ × ℂ)), DifferentiableAt ℂ (fun z => scIncGamma p.1 z) p.2 := by
    intro p _
    unfold scIncGamma
    exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => exp (-z)) p.2).mul
      (differentiableAt_regularizedConfluent 1 (p.1+1) p.2)
  intro p
  exact ((Complex.differentiableOn_prod_of_continuousOn_of_separately isOpen_univ hc.continuousOn h1 h2)
    p trivial).differentiableAt univ_mem

/-- Meromorphic parameter dependence away from the listed poles. -/
theorem lowerIncGamma_parameter_analytic {a z : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (hz : z ≠ 0) :
    AnalyticAt ℂ (fun b => lowerIncGamma b z) a := by
  have hG : AnalyticAt ℂ Gamma a := by
    apply ((differentiable_one_div_Gamma.analyticAt a).inv
      (inv_ne_zero (Gamma_ne_zero ha))).congr
    exact Eventually.of_forall fun b=>inv_inv (Gamma b)
  have hpow : Differentiable ℂ (fun b : ℂ=>z^b) :=
    fun b=>differentiableAt_id.const_cpow (Or.inl hz)
  have hM := analyticAt_regularizedConfluent_comp differentiable_id
    (show Differentiable ℂ (fun b : ℂ=>b+1) by fun_prop) (-z) a
  have hev : ∀ᶠ b : ℂ in 𝓝 a, ∀ n : ℕ, b≠-n := by
    filter_upwards [(differentiable_one_div_Gamma a).continuousAt.eventually_ne
      (inv_ne_zero (Gamma_ne_zero ha))] with b hb n hn
    apply hb
    rw [hn, Gamma_neg_nat_eq_zero, inv_zero]
  apply ((hG.mul (hpow.analyticAt a)).mul hM).congr
  filter_upwards [hev] with b hb
  exact (lowerIncGamma_eq_regularized hb z).symm

/-- Near a nonpositive integer, all other points avoid the nonpositive integers. -/
lemma eventually_nhdsNE_neg_nat_ne (n : ℕ) :
    ∀ᶠ a : ℂ in 𝓝[≠] (-(n : ℂ)), ∀ m : ℕ, a ≠ -m := by
  have hb : Metric.ball (-(n : ℂ)) 1 ∈ 𝓝 (-(n : ℂ)) := Metric.ball_mem_nhds _ one_pos
  filter_upwards [nhdsWithin_le_nhds hb, self_mem_nhdsWithin] with a ha hne m hm
  subst hm
  rw [Metric.mem_ball, dist_eq_norm, show -(m:ℂ) - -n = ((n:ℝ) - m : ℝ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs] at ha
  have hmn : m ≠ n := fun h => hne (by rw [h]; rfl)
  rcases Nat.lt_or_gt_of_ne hmn with h | h
  · have : (m:ℝ) + 1 ≤ n := by exact_mod_cast h
    rw [abs_lt] at ha; linarith
  · have : (n:ℝ) + 1 ≤ m := by exact_mod_cast h
    rw [abs_lt] at ha; linarith

/-- The residue of Gamma at a nonpositive integer. -/
lemma tendsto_add_nat_mul_Gamma (n : ℕ) :
    Tendsto (fun a : ℂ => (a+n)*Gamma a) (𝓝[≠] (-(n : ℂ))) (𝓝 ((-1 : ℂ)^n/n.factorial)) := by
  induction n with
  | zero => simpa using tendsto_self_mul_Gamma_nhds_zero
  | succ n ih =>
    have hshift : Tendsto (fun a : ℂ => a+1) (𝓝[≠] (-((n+1:ℕ) : ℂ))) (𝓝[≠] (-(n : ℂ))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h : Tendsto (fun a : ℂ => a+1) (𝓝 (-((n+1:ℕ) : ℂ))) (𝓝 (-((n+1:ℕ) : ℂ)+1)) :=
          (continuous_id.add continuous_const).tendsto _
        convert h.mono_left nhdsWithin_le_nhds using 2; push_cast; ring
      · filter_upwards [self_mem_nhdsWithin] with a ha
        simp only [mem_compl_iff, mem_singleton_iff] at ha ⊢
        intro h
        apply ha
        push_cast
        linear_combination h
    have hinv : Tendsto (fun a : ℂ => a⁻¹) (𝓝[≠] (-((n+1:ℕ) : ℂ))) (𝓝 (-((n+1:ℕ) : ℂ))⁻¹) :=
      ((continuousAt_inv₀ (by push_cast; exact neg_ne_zero.mpr (by exact_mod_cast n.succ_ne_zero))).tendsto).mono_left
        nhdsWithin_le_nhds
    have h := (ih.comp hshift).mul hinv
    have hne0 : ∀ᶠ a in 𝓝[≠] (-((n+1:ℕ) : ℂ)), a ≠ 0 :=
      (hinv.eventually_ne (by
        exact inv_ne_zero (by push_cast; exact neg_ne_zero.mpr (by exact_mod_cast n.succ_ne_zero)))).mono
        fun a ha h0 => ha (by rw [h0, inv_zero])
    have hlim : (-1 : ℂ)^n/n.factorial * (-((n+1:ℕ) : ℂ))⁻¹ =
        (-1 : ℂ)^(n+1)/(n+1).factorial := by
      rw [Nat.factorial_succ]; push_cast
      have : (n:ℂ)+1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
      field_simp
      ring
    rw [← hlim]
    refine h.congr' ?_
    filter_upwards [hne0] with a ha
    simp only [Function.comp_apply]
    rw [Complex.Gamma_add_one a ha]
    push_cast
    field_simp
    ring

/-- `𝐌(a,a+1,-z)` is the scaled incomplete Gamma function. -/
lemma regularizedConfluent_self_succ_neg (a z : ℂ) :
    regularizedHGFun {a} {a+1} (-z) = scIncGamma a z := by
  rw [regularizedConfluent_kummer_transform a (a+1) (-z), show a+1-a=1 by ring, neg_neg,
    scIncGamma]

lemma continuous_scIncGamma_param (z : ℂ) : Continuous fun a => scIncGamma a z := by
  have h : Continuous fun c : ℂ => regularizedHGFun {1} {c+1} z :=
    continuous_regularizedConfluent.comp (f := fun c : ℂ => ((1:ℂ), c + 1, z)) (by fun_prop)
  exact continuous_const.mul h

/-- Entire parameter dependence in DLMF §8.2(ii). -/
theorem upperIncGamma_parameter_entire {z : ℂ} (hz : z ≠ 0) :
    Differentiable ℂ (fun a => upperIncGamma a z) := by
  have hA : ∀ b : ℂ, (∀ m : ℕ, b ≠ -m) → DifferentiableAt ℂ (fun a => upperIncGamma a z) b := by
    intro b hb
    have hev : ∀ᶠ c : ℂ in 𝓝 b, ∀ m : ℕ, c≠-m := by
      filter_upwards [(differentiable_one_div_Gamma b).continuousAt.eventually_ne
        (inv_ne_zero (Gamma_ne_zero hb))] with c hc m hm
      apply hc
      rw [hm, Gamma_neg_nat_eq_zero, inv_zero]
    refine ((differentiableAt_Gamma b hb).sub
      (lowerIncGamma_parameter_analytic hb hz).differentiableAt).congr_of_eventuallyEq ?_
    filter_upwards [hev] with c hc
    simp only [Pi.sub_apply]
    linear_combination lowerIncGamma_add_upperIncGamma hc hz
  have hcont : Continuous fun a => upperIncGamma a z := by
    have hU : Continuous fun c : ℂ => kummerU (1 - c) (1 - c) z :=
      continuous_iff_continuousAt.mpr fun c =>
        (continuousAt_kummerU_param (1 - c) (1 - c) hz).comp_of_eq
          (g := fun p : ℂ × ℂ => kummerU p.1 p.2 z)
          (by fun_prop : Continuous fun c : ℂ => (1 - c, 1 - c)).continuousAt rfl
    exact continuous_const.mul hU
  intro a
  by_cases ha : ∀ m : ℕ, a ≠ -m
  · exact hA a ha
  push Not at ha
  obtain ⟨n, rfl⟩ := ha
  have hs : {b : ℂ | b = -n ∨ ∀ m : ℕ, b ≠ -m} ∈ 𝓝 (-(n:ℂ)) := by
    have h := eventually_nhdsWithin_iff.mp (eventually_nhdsNE_neg_nat_ne n)
    filter_upwards [h] with b hb
    by_cases hbn : b = -n
    · exact Or.inl hbn
    · exact Or.inr (hb hbn)
  refine (((differentiableOn_compl_singleton_and_continuousAt_iff hs).mp
    ⟨fun b hb => ?_, hcont.continuousAt⟩).differentiableAt hs)
  obtain ⟨hb1, hb2⟩ := hb
  rcases hb1 with h | h
  · exact absurd h hb2
  · exact (hA b h).differentiableWithinAt

/-- Simple parameter poles and their residues in DLMF §8.2(ii). -/
theorem lowerIncGamma_parameter_residue (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun a : ℂ => (a+n)*lowerIncGamma a z) (𝓝[≠] (-(n : ℂ))) (𝓝 ((-1 : ℂ)^n/n.factorial)) := by
  have hc : Tendsto (fun a : ℂ => z^a*scIncGamma a z) (𝓝[≠] (-(n : ℂ)))
      (𝓝 (z^(-(n:ℂ))*scIncGamma (-n) z)) :=
    (((continuous_const_cpow' hz).mul (continuous_scIncGamma_param z)).tendsto _).mono_left
      nhdsWithin_le_nhds
  have h := (tendsto_add_nat_mul_Gamma n).mul hc
  rw [scIncGamma_neg_nat, cpow_neg, cpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hz),
    mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_nhdsNE_neg_nat_ne n] with a ha
  rw [lowerIncGamma_eq_regularized ha, regularizedConfluent_self_succ_neg]
  ring

/-- Derivative of `𝐌(p,q,-u)`. -/
lemma hasDerivAt_regularizedConfluent_neg (p q w : ℂ) :
    HasDerivAt (fun u => regularizedHGFun {p} {q} (-u))
      (-(p*regularizedHGFun {p+1} {q+1} (-w))) w := by
  have h := (differentiableAt_regularizedConfluent p q (-w)).hasDerivAt
  rw [deriv_regularizedConfluent] at h
  have h2 := h.comp w (hasDerivAt_neg w)
  simpa [Function.comp_def] using h2

/-- On the logarithmic plane the lower Gamma function has derivative `exp (a w - e^w)`. -/
theorem hasDerivAt_lowerIncGammaOnLog {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (w : ℂ) :
    HasDerivAt (lowerIncGammaOnLog a) (exp (a*w-exp w)) w := by
  have ha0 : a ≠ 0 := by simpa using ha 0
  have hsc : HasDerivAt (fun u => scIncGamma a (exp u))
      (-(a*scIncGamma (a+1) (exp w))*exp w) w := by
    have h := (hasDerivAt_regularizedConfluent_neg a (a+1) (exp w)).comp w (Complex.hasDerivAt_exp w)
    rw [show a+1+1=(a+1)+1 by ring, regularizedConfluent_self_succ_neg] at h
    simpa only [Function.comp_def, regularizedConfluent_self_succ_neg] using h
  have h := ((((hasDerivAt_id w).const_mul a).cexp).mul hsc).const_mul (Gamma a)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)).congr_deriv ?_
  · simp [lowerIncGammaOnLog]; ring
  have hr := scIncGamma_recurrence a (exp w)
  have hG := Complex.Gamma_add_one a ha0
  have hG0 : Gamma a ≠ 0 := Gamma_ne_zero ha
  simp only [id, mul_one]
  rw [show a*w-exp w=a*w+(-exp w) by ring, Complex.exp_add]
  have hr' : exp w*scIncGamma (a+1) (exp w)*(a*Gamma a)=scIncGamma a (exp w)*(a*Gamma a)-exp (-exp w) := by
    rw [hr, hG]; field_simp
  linear_combination (-exp (a*w))*hr'

/-- At a regular parameter the upper Gamma continuation is `Γ(a)` minus the lower one. -/
theorem upperIncGammaOnLog_eq_Gamma_sub {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (w : ℂ) :
    upperIncGammaOnLog a w=Gamma a-lowerIncGammaOnLog a w := by
  have hi := segmentIntegral_eq_sub (by fun_prop : Continuous (fun u : ℂ => exp (a*u-exp u)))
    (hasDerivAt_lowerIncGammaOnLog ha) (log (exp w)) w
  have hz : exp w ≠ 0 := Complex.exp_ne_zero w
  have hl : lowerIncGammaOnLog a (log (exp w))=lowerIncGamma a (exp w) := by
    rw [lowerIncGammaOnLog, Complex.exp_log hz,
      show exp (a*log (exp w))=(exp w)^a by
        rw [cpow_def_of_ne_zero hz]; congr 1; ring,
      lowerIncGamma_eq_regularized ha, regularizedConfluent_self_succ_neg]
  have hc := lowerIncGamma_add_upperIncGamma ha hz
  rw [upperIncGammaOnLog, hi]
  linear_combination hc+hl

/-- The upper Gamma continuation is continuous in its parameter. -/
theorem continuous_upperIncGammaOnLog_param (w : ℂ) :
    Continuous fun a => upperIncGammaOnLog a w := by
  have h1 := (upperIncGamma_parameter_entire (Complex.exp_ne_zero w)).continuous
  have h2 : Continuous fun a : ℂ => ∫ t : ℝ in 0..1,
      exp (a*(log (exp w)+t*(w-log (exp w)))-exp (log (exp w)+t*(w-log (exp w)))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (by fun_prop) 0 1
  unfold upperIncGammaOnLog segmentIntegral
  exact h1.sub (continuous_const.mul h2)

/-- The upper Gamma continuation is entire in its parameter. -/
theorem upperIncGammaOnLog_parameter_entire (w : ℂ) :
    Differentiable ℂ (fun a => upperIncGammaOnLog a w) := by
  have hA : ∀ b : ℂ, (∀ m : ℕ, b ≠ -m) → DifferentiableAt ℂ (fun a => upperIncGammaOnLog a w) b := by
    intro b hb
    have hev : ∀ᶠ c : ℂ in 𝓝 b, ∀ m : ℕ, c≠-m := by
      filter_upwards [(differentiable_one_div_Gamma b).continuousAt.eventually_ne
        (inv_ne_zero (Gamma_ne_zero hb))] with c hc m hm
      apply hc
      rw [hm, Gamma_neg_nat_eq_zero, inv_zero]
    have hM := analyticAt_regularizedConfluent_comp differentiable_id
      (show Differentiable ℂ (fun b : ℂ=>b+1) by fun_prop) (-exp w) b
    have hd : DifferentiableAt ℂ (fun c => Gamma c-Gamma c*(exp (c*w)*scIncGamma c (exp w))) b := by
      refine (differentiableAt_Gamma b hb).sub ((differentiableAt_Gamma b hb).mul
        (((differentiable_id.mul_const w).cexp b).mul ?_))
      refine hM.differentiableAt.congr_of_eventuallyEq (Eventually.of_forall fun c => ?_)
      simp [regularizedConfluent_self_succ_neg]
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hev] with c hc
    rw [upperIncGammaOnLog_eq_Gamma_sub hc, lowerIncGammaOnLog]
    ring
  intro a
  by_cases ha : ∀ m : ℕ, a ≠ -m
  · exact hA a ha
  push Not at ha
  obtain ⟨n, rfl⟩ := ha
  have hs : {b : ℂ | b = -n ∨ ∀ m : ℕ, b ≠ -m} ∈ 𝓝 (-(n:ℂ)) := by
    have h := eventually_nhdsWithin_iff.mp (eventually_nhdsNE_neg_nat_ne n)
    filter_upwards [h] with b hb
    by_cases hbn : b = -n
    · exact Or.inl hbn
    · exact Or.inr (hb hbn)
  refine (((differentiableOn_compl_singleton_and_continuousAt_iff hs).mp
    ⟨fun b hb => ?_, (continuous_upperIncGammaOnLog_param w).continuousAt⟩).differentiableAt hs)
  obtain ⟨hb1, hb2⟩ := hb
  rcases hb1 with h | h
  · exact absurd h hb2
  · exact (hA b h).differentiableWithinAt

/-- The regular parameters are dense. -/
lemma dense_regular_param : Dense {a : ℂ | ∀ n : ℕ, a ≠ -n} := by
  have hc : (Set.range fun n : ℕ => -(n:ℂ)).Countable := Set.countable_range _
  convert hc.dense_compl ℂ using 1
  ext a; simp [eq_comm]

/-- The logarithmic-plane recurrence `U(a+1,w)=a U(a,w)+e^{aw-e^w}`, at every parameter. -/
theorem upperIncGammaOnLog_add_one (a w : ℂ) :
    upperIncGammaOnLog (a+1) w=a*upperIncGammaOnLog a w+exp (a*w-exp w) := by
  have hz : exp w ≠ 0 := Complex.exp_ne_zero w
  have hf : Differentiable ℂ (fun s : ℂ => exp (a*s-exp s)) := by fun_prop
  have hP := hasDerivAt_primitive hf
  have hd (u : ℂ) : HasDerivAt (fun v => a*primitive (fun s => exp (a*s-exp s)) v
      - exp (a*v-exp v)) (exp ((a+1)*u-exp u)) u := by
    have he : HasDerivAt (fun v => exp (a*v-exp v)) (exp (a*u-exp u)*(a-exp u)) u := by
      have := (((hasDerivAt_id u).const_mul a).sub (Complex.hasDerivAt_exp u)).cexp
      simpa using this
    refine (((hP u).const_mul a).sub he).congr_deriv ?_
    rw [show (a+1)*u-exp u=(a*u-exp u)+u by ring, Complex.exp_add (a*u-exp u)]
    ring
  have h1 := segmentIntegral_eq_sub (by fun_prop : Continuous (fun u : ℂ => exp ((a+1)*u-exp u)))
    hd (log (exp w)) w
  have h0 := segmentIntegral_eq_sub hf.continuous hP (log (exp w)) w
  have hr := upperIncGamma_add_one a hz
  have hp : (exp w)^a=exp (a*log (exp w)) := by rw [cpow_def_of_ne_zero hz]; ring_nf
  rw [upperIncGammaOnLog, upperIncGammaOnLog, h1, h0, hr, hp, Complex.exp_log hz,
    show a*log (exp w)-exp w=a*log (exp w)+(-exp w) by ring, Complex.exp_add (a*log (exp w))]
  ring

/-- Non-integral parameters are dense. -/
lemma dense_nonint_param : Dense {a : ℂ | ∀ n : ℤ, a ≠ n} := by
  have hc : (Set.range fun n : ℤ => (n:ℂ)).Countable := Set.countable_range _
  convert hc.dense_compl ℂ using 1
  ext a; simp [eq_comm]

/-- `exp (ε π i) = -1` for `ε = ±1`. -/
lemma exp_eps_pi_I {ε : ℝ} (hε : ε=1 ∨ ε = -1) : exp (ε*π*I) = -1 := by
  rcases hε with rfl | rfl
  · simp
  · simp [neg_mul]

/-- lowerIncGammaOnLog monodromy. -/
@[dlmf 8.2.E8]
theorem lowerIncGammaOnLog_monodromy (w : ℂ) (m : ℤ) {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) :
    lowerIncGammaOnLog a (w+2*π*m*I)=exp (2*π*m*I*a)*lowerIncGammaOnLog a w := by
  have he : exp (2*π*m*I)=1 := by
    rw [show (2:ℂ)*π*m*I=m*(2*π*I) by ring, exp_int_mul_two_pi_mul_I]
  simp only [lowerIncGammaOnLog, exp_add, he, mul_one]
  rw [show a*(w+2*π*m*I)=2*π*m*I*a+a*w by ring, exp_add]
  ring

/-- upperIncGammaOnLog monodromy. -/
@[dlmf 8.2.E9]
theorem upperIncGammaOnLog_monodromy (w : ℂ) (m : ℤ) {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) :
    upperIncGammaOnLog a (w+2*π*m*I)=exp (2*π*m*I*a)*upperIncGammaOnLog a w+(1-exp (2*π*m*I*a))*Gamma a := by
  have he : exp (2*π*m*I)=1 := by
    rw [show (2:ℂ)*π*m*I=m*(2*π*I) by ring, exp_int_mul_two_pi_mul_I]
  rw [upperIncGammaOnLog_eq_Gamma_sub ha, upperIncGammaOnLog_eq_Gamma_sub ha, lowerIncGammaOnLog,
    lowerIncGammaOnLog, Complex.exp_add w, he, mul_one,
    show a*(w+2*π*m*I)=2*π*m*I*a+a*w by ring, Complex.exp_add]
  ring

/-- upperIncGammaOnLog monodromy limit. -/
@[dlmf 8.2.E9]
theorem upperIncGammaOnLog_monodromy_limit (w : ℂ) (m : ℤ) (n : ℕ) :
    Tendsto (fun a : ℂ => exp (2*π*m*I*a)*upperIncGammaOnLog a w+(1-exp (2*π*m*I*a))*Gamma a) (𝓝[≠] (-(n : ℂ))) (𝓝 (upperIncGammaOnLog (-n) (w+2*π*m*I))) := by
  refine (((continuous_upperIncGammaOnLog_param _).tendsto _).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_nhdsNE_neg_nat_ne n] with a ha
  exact upperIncGammaOnLog_monodromy w m ha

/-- upperIncGammaOnLog halfTurn. -/
@[dlmf 8.2.E11]
theorem upperIncGammaOnLog_halfTurn (w : ℂ) {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    upperIncGammaOnLog a (w+ε*π*I)=Gamma a*(1-exp (a*w+ε*π*I*a)*scIncGamma a (-exp w)) := by
  rw [upperIncGammaOnLog_eq_Gamma_sub ha, lowerIncGammaOnLog, Complex.exp_add w, exp_eps_pi_I hε]
  ring_nf

/-- upperIncGammaOnLog jump. -/
@[dlmf 8.2.E10]
theorem upperIncGammaOnLog_jump (a w : ℂ) :
    exp (-π*I*a)*upperIncGammaOnLog a (w+π*I)-exp (π*I*a)*upperIncGammaOnLog a (w-π*I) = -2*π*I/Gamma (1-a) := by
  have hc1 : Continuous fun a : ℂ => exp (-π*I*a)*upperIncGammaOnLog a (w+π*I)-exp (π*I*a)*upperIncGammaOnLog a (w-π*I) :=
    ((by fun_prop : Continuous fun a : ℂ => exp (-π*I*a)).mul (continuous_upperIncGammaOnLog_param _)).sub
      ((by fun_prop : Continuous fun a : ℂ => exp (π*I*a)).mul (continuous_upperIncGammaOnLog_param _))
  have hc2 : Continuous fun a : ℂ => -2*π*I/Gamma (1-a) := by
    have h := differentiable_one_div_Gamma.continuous.comp
      (continuous_const.sub continuous_id : Continuous fun a : ℂ => 1 - a)
    simp_rw [div_eq_mul_inv]
    exact continuous_const.mul (by simpa [Function.comp_def] using h)
  refine congrFun (hc1.ext_on dense_nonint_param hc2 ?_) a
  intro b hb
  have hb' : ∀ n : ℕ, b ≠ -n := fun n h => hb (-n) (by rw [h]; push_cast; ring)
  have hb1 : ∀ n : ℕ, 1-b ≠ -n := fun n h => hb (n+1) (by push_cast; linear_combination -h)
  have hs : Complex.sin (π*b) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    exact hb k (mul_left_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) (by rw [hk]; ring))
  have hr := Complex.Gamma_mul_Gamma_one_sub b
  have h1 := upperIncGammaOnLog_halfTurn w hb' (ε := 1) (Or.inl rfl)
  have h2 := upperIncGammaOnLog_halfTurn w hb' (ε := -1) (Or.inr rfl)
  push_cast at h1 h2
  simp only [one_mul, neg_mul, ← sub_eq_add_neg] at h1 h2
  simp only
  rw [h1, h2]
  have hG1 := Gamma_ne_zero hb1
  rw [Complex.sin] at hs hr
  have e1 : exp (-π*I*b)*exp (b*w+π*I*b)=exp (b*w) := by rw [← Complex.exp_add]; ring_nf
  have e2 : exp (π*I*b)*exp (b*w-π*I*b)=exp (b*w) := by rw [← Complex.exp_add]; ring_nf
  have e3 : exp (-(π*b)*I)=exp (-π*I*b) := by ring_nf
  have e4 : exp (π*b*I)=exp (π*I*b) := by ring_nf
  rw [e3, e4] at hr
  have hs' : exp (-π*I*b) - exp (π*I*b) ≠ 0 := by
    rw [e3, e4] at hs; intro h; apply hs; rw [h]; ring
  have hr' : Gamma b*Gamma (1-b)*((exp (-π*I*b)-exp (π*I*b))*I)=2*π := by
    rw [hr, div_mul_eq_mul_div, div_eq_iff (div_ne_zero (mul_ne_zero hs' I_ne_zero) two_ne_zero)]; ring
  rw [eq_div_iff hG1]
  linear_combination (Gamma (1-b))*scIncGamma b (-exp w)*Gamma b*(e2-e1) + (-I)*hr'
    + (exp (-π*I*b)-exp (π*I*b))*Gamma b*Gamma (1-b)*I_sq

/-- Differentiating the Tricomi representation gives the upper-Gamma derivative at every order. -/
theorem hasDerivAt_upperIncGamma_complex (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (upperIncGamma a) (-z^(a-1)*exp (-z)) z := by
  have hz0 := slitPlane_ne_zero hz
  have hr := kummerU_contiguous_a_b (1-a) (2-a) z hz0
  rw [show (1:ℂ)-a+1=2-a by ring, show (2:ℂ)-a-1=1-a by ring,
    kummerU_kummer_transform_all (1-a) (2-a) hz0,
    show 1-(2-a)=a-1 by ring, show (1:ℂ)-a-(2-a)+1=0 by ring,
    kummerU_zero, mul_one] at hr
  change HasDerivAt (fun w => exp (-w)*kummerU (1-a) (1-a) w) _ z
  refine (((hasDerivAt_neg z).cexp).mul (hasDerivAt_kummerU (1-a) (1-a) hz)).congr_deriv ?_
  simp only [show (1:ℂ)-a+1=2-a by ring]
  linear_combination exp (-z)*hr

/-- upperIncGamma horizontal integral. -/
@[dlmf 8.2.E2]
theorem upperIncGamma_horizontal_integral (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => (z+t)^(a-1)*exp (-(z+t))) 0 (upperIncGamma a z) := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => -upperIncGamma a (z+t))
      ((z+t)^(a-1)*exp (-(z+t))) t := by
    intro t ht
    refine (hasDerivAt_comp_add_ofReal (g := fun w => -upperIncGamma a w)
      (hasDerivAt_upperIncGamma_complex a (add_ofReal_mem_slitPlane hz ht)).neg).congr_deriv ?_
    ring
  have hc : ContinuousOn (fun t : ℝ => (z+t)^(a-1)*exp (-(z+t))) (Ici 0) := by
    refine ContinuousOn.mul (fun t ht => ?_) (by fun_prop)
    exact ((continuousAt_const.add continuous_ofReal.continuousAt).cpow continuousAt_const
      (add_ofReal_mem_slitPlane hz ht)).continuousWithinAt
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc (tendsto_upperIncGamma_add_ofReal a z).neg
  simpa using h

/-- hasDerivAt incompleteGamma. -/
@[dlmf 8.8.E13]
theorem hasDerivAt_incompleteGamma {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (lowerIncGamma a) (z^(a-1)*exp (-z)) z ∧ HasDerivAt (upperIncGamma a) (-z^(a-1)*exp (-z)) z := by
  have hu := hasDerivAt_upperIncGamma_complex a hz
  refine ⟨?_,hu⟩
  have he : lowerIncGamma a =ᶠ[𝓝 z] fun w => Gamma a-upperIncGamma a w := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    linear_combination lowerIncGamma_add_upperIncGamma ha (slitPlane_ne_zero hw)
  simpa only [neg_mul, neg_neg] using (hu.const_sub (Gamma a)).congr_of_eventuallyEq he

/-- lower upperIncGamma ode. -/
@[dlmf 8.2.E12]
theorem lower_upperIncGamma_ode {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ∈ slitPlane) :
    (∀ f ∈ ({lowerIncGamma a,upperIncGamma a} : Set (ℂ → ℂ)), deriv (deriv f) z+(1+(1-a)/z)*deriv f z=0) := by
  have hz0 := slitPlane_ne_zero hz
  have hg : HasDerivAt (fun w : ℂ => w^(a-1)*exp (-w))
      ((a-1)*z^(a-1-1)*exp (-z) - z^(a-1)*exp (-z)) z := by
    have h1 := (hasDerivAt_id z).cpow_const (c := a-1) hz
    have h2 := (hasDerivAt_neg z).cexp
    have h3 := h1.mul h2
    simp only [id] at h3
    convert h3 using 1
    ring
  have hpow : z^(a-1-1) = z^(a-1)/z := by
    rw [cpow_sub _ _ hz0, cpow_one]
  have hnb := isOpen_slitPlane.mem_nhds hz
  intro f hf
  rcases hf with rfl | hf
  · have hd : deriv (lowerIncGamma a) =ᶠ[𝓝 z] fun w => w^(a-1)*exp (-w) := by
      filter_upwards [hnb] with w hw
      exact (hasDerivAt_incompleteGamma ha hw).1.deriv
    rw [hd.deriv_eq, hg.deriv, (hasDerivAt_incompleteGamma ha hz).1.deriv, hpow]
    field_simp
    ring
  · rw [Set.mem_singleton_iff] at hf
    subst hf
    have hd : deriv (upperIncGamma a) =ᶠ[𝓝 z] fun w => -(w^(a-1)*exp (-w)) := by
      filter_upwards [hnb] with w hw
      rw [(hasDerivAt_upperIncGamma_complex a hw).deriv]; ring
    have hgn : HasDerivAt (fun w : ℂ => -(w^(a-1)*exp (-w))) _ z := hg.neg
    rw [hd.deriv_eq, hgn.deriv, (hasDerivAt_upperIncGamma_complex a hz).deriv, hpow]
    field_simp
    ring

/-- upperIncGamma scaled ode. -/
@[dlmf 8.2.E13]
theorem upperIncGamma_scaled_ode (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    let w := fun t => exp t*t^(1-a)*upperIncGamma a t; deriv (deriv w) z-(1+(1-a)/z)*deriv w z+(1-a)/z^2*w z=0 := by
  intro w
  have hw : ∀ t ∈ slitPlane, HasDerivAt w ((1+(1-a)/t)*w t - 1) t := by
    intro t ht
    have ht0 := slitPlane_ne_zero ht
    have h1 := (hasDerivAt_id t).cpow_const (c := 1-a) ht
    have h : HasDerivAt w _ t :=
      ((Complex.hasDerivAt_exp t).mul h1).mul (hasDerivAt_upperIncGamma_complex a ht)
    refine h.congr_deriv ?_
    have hp : t^(1-a-1) = t^(1-a)/t := by rw [cpow_sub _ _ ht0, cpow_one]
    have hq : t^(1-a)*t^(a-1) = 1 := by rw [← cpow_add _ _ ht0]; simp
    have he : exp t*exp (-t) = 1 := by rw [← Complex.exp_add]; simp
    simp only [w, id, Pi.mul_apply, hp, mul_one]
    field_simp
    linear_combination (-t) * (exp t * exp (-t)) * hq - t * he
  have hnb := isOpen_slitPlane.mem_nhds hz
  have hd : deriv w =ᶠ[𝓝 z] fun t => (1+(1-a)/t)*w t - 1 := by
    filter_upwards [hnb] with t ht
    exact (hw t ht).deriv
  have hz0 := slitPlane_ne_zero hz
  have h2 : HasDerivAt (fun t => (1+(1-a)/t)*w t - 1)
      ((-(1-a)/z^2)*w z + (1+(1-a)/z)*((1+(1-a)/z)*w z - 1)) z := by
    have hi := ((hasDerivAt_inv hz0).const_mul (1-a)).const_add 1
    convert (hi.mul (hw z hz)).sub_const 1 using 1
    · funext t; simp [div_eq_mul_inv]
    · simp [div_eq_mul_inv]; ring
  rw [hd.deriv_eq, h2.deriv, (hw z hz).deriv]
  field_simp
  ring

/-- scIncGamma ode. -/
@[dlmf 8.2.E14]
theorem scIncGamma_ode (a z : ℂ) :
    z*deriv (deriv (scIncGamma a)) z+(a+1+z)*deriv (scIncGamma a) z+a*scIncGamma a z=0 := by
  have he : scIncGamma a = fun w => regularizedHGFun {a} {a+1} (-w) := by
    funext w
    rw [regularizedConfluent_kummer_transform a (a+1) (-w)]
    simp only [show a+1-a=1 by ring, neg_neg, scIncGamma]
  have hd1 : deriv (scIncGamma a) = fun w => -(a*regularizedHGFun {a+1} {a+1+1} (-w)) := by
    funext w
    rw [he]
    exact (hasDerivAt_regularizedConfluent_neg _ _ w).deriv
  have hd2 : deriv (deriv (scIncGamma a)) z = a*((a+1)*regularizedHGFun {a+1+1} {a+1+1+1} (-z)) := by
    rw [hd1]
    have := (((hasDerivAt_regularizedConfluent_neg (a+1) (a+1+1) z).const_mul a).neg)
    rw [show (fun w => -(a*regularizedHGFun {a+1} {a+1+1} (-w))) =
      -(fun w => a*regularizedHGFun {a+1} {a+1+1} (-w)) from rfl, this.deriv]; ring
  rw [hd2, hd1, he]
  have h := regularizedConfluent_ode_contiguous a (a+1) (-z)
  rw [show a+2=a+1+1 by ring, show a+1+2=a+1+1+1 by ring] at h
  simp only
  linear_combination (-a) * h

end DLMF.Confluent
