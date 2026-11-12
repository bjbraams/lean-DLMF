/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.QAdditionTools
public import DLMF.Legendre.Continuation.LogarithmicBranches

/-!
# Exterior Legendre Q addition theorem

The Fourier coefficients of the principal Legendre Q angular kernel are continued from
Ferrers addition formulas to ordered positive hyperbolic angles (DLMF 14.18.5).
Fixing the ratio `κ` of the two angles gives a connected first-quadrant strip. The combined
argument is a convex combination of `cos ((1-κ)w)` and `cos ((1+κ)w)`, and hence stays in
the lower half-plane throughout that strip. The lower Ferrers boundary combination
`𝖰 + (πi/2)𝖯` gives the coefficient identity near a real angle. Holomorphic uniqueness and
continuity at imaginary angles then give the exterior identity. Fourier reconstruction
uses the twice continuously differentiable periodic kernel.

## Main results

* `ExteriorAddition.coefficient_associatedQ_hyperbolicArg`: the Fourier coefficients.
* `ExteriorAddition.hasSum_addition`: the convergent cosine expansion of DLMF 14.18.5.
-/

open Complex Filter Set MeasureTheory
open scoped Real Topology Nat
@[expose] public noncomputable section
namespace DLMF.Legendre.ExteriorAddition

/-- The complex angular argument with first angle `κw` and second angle `w`. -/
def argument (κ : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  cos (κ*w)*cos w + sin (κ*w)*sin w*Real.cos t

/-- The first-quadrant strip on which all angular arguments lie in the lower half-plane. -/
def domain (κ : ℝ) : Set ℂ :=
  {w | 0 < w.re ∧ (1+κ)*w.re < π ∧ 0 < w.im}

/-- The angular argument is a convex combination of the two cosine endpoints. -/
lemma argument_eq_cos_sub_add (κ : ℝ) (w : ℂ) (t : ℝ) :
    argument κ w t = (1+(Real.cos t:ℂ))/2*cos ((1-κ)*w) +
      (1-(Real.cos t:ℂ))/2*cos ((1+κ)*w) := by
  rw [show ((1:ℂ)-κ)*w = w-κ*w by ring,
    show ((1:ℂ)+κ)*w = w+κ*w by ring, cos_sub, cos_add]
  simp only [argument]
  ring

/-- The cosine has negative imaginary part in the angular strip. -/
lemma im_cos_mul_neg {κ r : ℝ} (_hκ0 : 0 < κ) (_hκ1 : κ < 1)
    (hr0 : 0 < r) (hrκ : r ≤ 1+κ) {w : ℂ} (hw : w ∈ domain κ) :
    (cos (r*w)).im < 0 := by
  have hrπ : r*w.re < π := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hrκ hw.1.le) hw.2.1
  have him : (cos (r*w)).im = -Real.sin (r*w.re)*Real.sinh (r*w.im) := by
    rw [cos_eq]
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, mul_im, zero_add,
      sub_im, cos_ofReal_im, cosh_ofReal_im, sin_ofReal_re, sinh_ofReal_re,
      sin_ofReal_im, sinh_ofReal_im, cos_ofReal_re, cosh_ofReal_re, I_im, I_re, mul_zero,
      add_zero, sub_zero]
    ring
  rw [him]
  have hs : 0 < Real.sin (r*w.re) := Real.sin_pos_of_pos_of_lt_pi (mul_pos hr0 hw.1) hrπ
  have hh : 0 < Real.sinh (r*w.im) := Real.sinh_pos_iff.mpr (mul_pos hr0 hw.2.2)
  nlinarith

/-- The combined angular argument has negative imaginary part for every real angle. -/
lemma im_argument_neg {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    {w : ℂ} (hw : w ∈ domain κ) (t : ℝ) : (argument κ w t).im < 0 := by
  have hm := im_cos_mul_neg hκ0 hκ1 (by linarith : 0 < 1-κ) (by linarith : 1-κ ≤ 1+κ) hw
  have hp := im_cos_mul_neg hκ0 hκ1 (by linarith : 0 < 1+κ) le_rfl hw
  push_cast at hm hp
  rw [argument_eq_cos_sub_add]
  simp only [add_im, mul_im, div_ofNat_re, div_ofNat_im, add_re, one_re, ofReal_re,
    add_im, one_im, ofReal_im, add_zero, zero_add, zero_div, zero_mul, sub_re, sub_im,
    sub_zero]
  have hc0 := Real.neg_one_le_cos t
  have hc1 := Real.cos_le_one t
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1+Real.cos t) hm.le,
    mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1-Real.cos t) hp.le]

/-- The angular continuation strip is open. -/
lemma isOpen_domain (κ : ℝ) : IsOpen (domain κ) := by
  change IsOpen ({w : ℂ | 0 < w.re} ∩
    ({w : ℂ | (1+κ)*w.re < π} ∩ {w : ℂ | 0 < w.im}))
  exact (isOpen_lt continuous_const continuous_re).inter
    ((isOpen_lt (by fun_prop) continuous_const).inter
      (isOpen_lt continuous_const continuous_im))

/-- The angular continuation strip is convex. -/
lemma convex_domain {κ : ℝ} (hκ : 0 < κ) : Convex ℝ (domain κ) := by
  have he : domain κ = {w : ℂ | 0 < w.re} ∩
      ({w : ℂ | w.re < π/(1+κ)} ∩ {w : ℂ | 0 < w.im}) := by
    ext w
    simp only [domain,mem_ofPred_eq,mem_inter_iff]
    rw [lt_div_iff₀ (by linarith : 0 < 1+κ)]
    ring_nf
  rw [he]
  exact (convex_halfSpace_re_gt 0).inter
    ((convex_halfSpace_re_lt (π/(1+κ))).inter (convex_halfSpace_im_gt 0))

/-- The cosine arguments avoid the associated Legendre cut. -/
lemma cos_mul_sub_one_mem_slitPlane {κ r : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hr0 : 0 < r) (hrκ : r ≤ 1+κ) {w : ℂ} (hw : w ∈ domain κ) :
    cos (r*w)-1 ∈ slitPlane := Or.inr (by
  have him := im_cos_mul_neg hκ0 hκ1 hr0 hrκ hw
  simpa only [sub_im,one_im,sub_zero] using him.ne)

/-- Every combined argument avoids the associated Legendre cut. -/
lemma argument_sub_one_mem_slitPlane {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    {w : ℂ} (hw : w ∈ domain κ) (t : ℝ) : argument κ w t-1 ∈ slitPlane := Or.inr (by
  have him := im_argument_neg hκ0 hκ1 hw t
  simpa only [sub_im,one_im,sub_zero] using him.ne)

/-- The combined argument is jointly continuous in the complex angle and real phase. -/
lemma continuous_argument (κ : ℝ) : Continuous (fun p : ℂ × ℝ => argument κ p.1 p.2) := by
  dsimp [argument]
  fun_prop

/-- The combined argument is entire in the complex angle. -/
lemma differentiable_argument (κ : ℝ) (t : ℝ) : Differentiable ℂ (fun w => argument κ w t) := by
  dsimp [argument]
  fun_prop

/-- Angular Fourier coefficients preserve holomorphy of a composed function. -/
lemma differentiableOn_coefficient {κ : ℝ} {G : ℂ → ℂ} {U S : Set ℂ}
    (hU : IsOpen U) (hG : DifferentiableOn ℂ G S)
    (hmap : ∀ w ∈ U, ∀ t, argument κ w t ∈ S) (m : ℤ) :
    DifferentiableOn ℂ (fun w => AdditionTheorem.coeff (fun t => G (argument κ w t)) m) U := by
  have hj : ContinuousOn (fun p : ℂ × ℝ => G (argument κ p.1 p.2)) (U ×ˢ univ) :=
    hG.continuousOn.comp (continuous_argument κ).continuousOn (fun p hp => hmap p.1 hp.1 p.2)
  have hkernel : Continuous (fun p : ℂ × ℝ => exp (-((m:ℂ)*p.2*I))) := by fun_prop
  have hc := hkernel.continuousOn.mul hj
  have hd (t : ℝ) : DifferentiableOn ℂ
      (fun w => exp (-((m:ℂ)*t*I))*G (argument κ w t)) U :=
    (differentiableOn_const _).mul
      (hG.comp (differentiable_argument κ t).differentiableOn (fun w hw => hmap w hw t))
  exact (Complex.differentiableOn_intervalIntegral_of_continuousOn hU (-π) π hc hd).const_mul _

/-- The exterior Q coefficients are holomorphic on the angular continuation strip. -/
lemma differentiableOn_coefficient_associatedQ {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (ν : ℂ) (m : ℤ) :
    DifferentiableOn ℂ (fun w => AdditionTheorem.coeff
      (fun t => associatedQ ν 0 (argument κ w t)) m) (domain κ) := by
  apply differentiableOn_coefficient (isOpen_domain κ)
    (S := {z : ℂ | z-1 ∈ slitPlane})
  · intro z hz
    exact ((analyticAt_const.mul (olverQ_analytic ν 0 z hz)).differentiableAt)
      |>.differentiableWithinAt
  · intro w hw t
    exact argument_sub_one_mem_slitPlane hκ0 hκ1 hw t

/-- The neighborhood where the two individual arguments and every combined argument lie
in the unit disk. -/
def localDomain (κ : ℝ) : Set ℂ :=
  {w | ‖cos (κ*w)*cos w‖+‖sin (κ*w)*sin w‖ < 1 ∧
    ‖cos (κ*w)‖ < 1 ∧ ‖cos w‖ < 1}

/-- The disk neighborhood of angular parameters is open. -/
lemma isOpen_localDomain (κ : ℝ) : IsOpen (localDomain κ) := by
  change IsOpen ({w : ℂ | ‖cos (κ*w)*cos w‖+‖sin (κ*w)*sin w‖ < 1} ∩
    ({w : ℂ | ‖cos (κ*w)‖ < 1} ∩ {w : ℂ | ‖cos w‖ < 1}))
  exact (isOpen_lt (by fun_prop) continuous_const).inter
    ((isOpen_lt (by fun_prop) continuous_const).inter
      (isOpen_lt (by fun_prop) continuous_const))

/-- The norm bound defining the disk neighborhood controls every real phase. -/
lemma argument_mem_ball {κ : ℝ} {w : ℂ} (hw : w ∈ localDomain κ) (t : ℝ) :
    argument κ w t ∈ Metric.ball (0:ℂ) 1 := by
  rw [Metric.mem_ball,dist_zero_right]
  have hcos : ‖(Real.cos t:ℂ)‖ ≤ 1 := by
    rw [norm_real,Real.norm_eq_abs]
    exact Real.abs_cos_le_one t
  calc
    ‖argument κ w t‖ ≤ ‖cos (κ*w)*cos w‖+‖sin (κ*w)*sin w*Real.cos t‖ := norm_add_le _ _
    _ ≤ ‖cos (κ*w)*cos w‖+‖sin (κ*w)*sin w‖ := by
      rw [norm_mul (sin (κ*w)*sin w) (Real.cos t)]
      nlinarith [norm_nonneg (sin (κ*w)*sin w)]
    _ < 1 := hw.1

/-- Sufficiently small positive real angles belong to the disk neighborhood. -/
lemma ofReal_mem_localDomain {κ r : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hr0 : 0 < r) (hrsum : (1+κ)*r < π/2) : (r:ℂ) ∈ localDomain κ := by
  have hrπ : r < π/2 := by nlinarith
  have hκr0 : 0 < κ*r := mul_pos hκ0 hr0
  have hκrπ : κ*r < π/2 := by nlinarith
  have hc1 : 0 < Real.cos (κ*r) := Real.cos_pos_of_mem_Ioo ⟨by linarith,hκrπ⟩
  have hc2 : 0 < Real.cos r := Real.cos_pos_of_mem_Ioo ⟨by linarith,hrπ⟩
  have hs1 : 0 < Real.sin (κ*r) := Real.sin_pos_of_pos_of_lt_pi hκr0 (by linarith)
  have hs2 : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr0 (by linarith)
  have hc1lt : Real.cos (κ*r) < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) hκr0
  have hc2lt : Real.cos r < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) hr0
  have hdiff0 : 0 < r-κ*r := by nlinarith
  have hdiffπ : r-κ*r < π := by nlinarith [Real.pi_pos]
  have hsum : Real.cos (κ*r)*Real.cos r + Real.sin (κ*r)*Real.sin r < 1 := by
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hdiffπ.le hdiff0
    rw [Real.cos_zero,Real.cos_sub] at hc
    simpa only [mul_comm] using hc
  simp only [localDomain,mem_ofPred_eq]
  rw [← ofReal_mul,← ofReal_cos,← ofReal_cos,← ofReal_sin,← ofReal_sin]
  simp only [mem_ofPred_eq,norm_mul,norm_real,Real.norm_eq_abs,abs_of_pos hc1,
    abs_of_pos hc2,abs_of_pos hs1,abs_of_pos hs2]
  exact ⟨hsum,hc1lt,hc2lt⟩


/-- The continued Ferrers combination `𝖰 + (πi/2)𝖯` giving the lower Q boundary. -/
def localCombination (ν μ z : ℂ) : ℂ := ferrersQCont ν μ z + π*I/2*ferrersPCont ν μ z

/-- Real complex angles recover the Ferrers addition argument. -/
lemma argument_ofReal (κ r t : ℝ) : argument κ r t = AdditionTheorem.ferrersArg (κ*r) r t := by
  dsimp [argument,AdditionTheorem.ferrersArg]
  push_cast
  rfl

/-- The real-angle Fourier coefficients follow from the Ferrers P and Q addition formulas. -/
lemma coeff_localCombination_real {κ r : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hr0 : 0 < r) (hrsum : (1+κ)*r < π) {ν : ℂ} (hr : LegendreQRegular ν 0) (m : ℕ) :
    AdditionTheorem.coeff (fun t => localCombination ν 0 (argument κ r t)) m =
      (-1:ℂ)^m*ferrersPCont ν (-m) (cos (κ*r)) *
        localCombination ν m (cos r) := by
  have hθ1 : 0 ≤ κ*r := (mul_pos hκ0 hr0).le
  have hθ12 : κ*r < r := by nlinarith
  have hθ2 : 0 ≤ r := hr0.le
  have hsum : κ*r+r < π := by nlinarith
  have hrπ : r < π := by nlinarith
  have hκrπ : κ*r < π := by nlinarith
  have hI1 : Real.cos (κ*r) ∈ Ioo (-1:ℝ) 1 :=
    ⟨AdditionTheorem.neg_one_lt_cos hθ1 hκrπ, by
      rw [← Real.cos_zero]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hκrπ.le (mul_pos hκ0 hr0)⟩
  have hI2 : Real.cos r ∈ Ioo (-1:ℝ) 1 :=
    ⟨AdditionTheorem.neg_one_lt_cos hθ2 hrπ, by
      rw [← Real.cos_zero]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hrπ.le hr0⟩
  have hArg (t : ℝ) : AdditionTheorem.ferrersArg (κ*r) r t ∈ Ioo (-1:ℝ) 1 := by
    have hm := SecondKindAddition.ferrersArg_mem hθ1 hθ12 hsum t
    exact ⟨lt_of_lt_of_le (AdditionTheorem.neg_one_lt_cos (by positivity) hsum) hm.1,
      lt_of_le_of_lt hm.2 (SecondKindAddition.ferrersArg_lt_one hθ1 hθ12 hrπ t).2⟩
  have hqc : Continuous (fun t => ferrersQ ν 0 (AdditionTheorem.ferrersArg (κ*r) r t)) :=
    (SecondKindAddition.contDiff_ferrersQ ν (SecondKindAddition.ferrersArg_contDiff _ _)
      (fun t => by have ht := hArg t; nlinarith [ht.1,ht.2])).continuous
  have hpc : Continuous (fun t => ferrersP ν 0 (AdditionTheorem.ferrersArg (κ*r) r t)) :=
    (AdditionTheorem.ferrersArg_contDiff ν hθ1 hθ2 hsum).continuous
  have hf : (fun t => localCombination ν 0 (argument κ r t)) =
      (fun t => ferrersQ ν 0 (AdditionTheorem.ferrersArg (κ*r) r t) +
        (π*I/2)*ferrersP ν 0 (AdditionTheorem.ferrersArg (κ*r) r t)) := by
    funext t
    rw [argument_ofReal,localCombination,ferrersQCont_ofReal,
      ferrersPCont_ofReal ν 0 (hArg t)]
  have hp := AdditionTheorem.ferrers_coeff_eq hθ1 hθ2 hsum m
    (fun n => AdditionTheorem.ferrers_nat hθ1 hθ2 hsum m n) ν
  have hq := SecondKindAddition.coeff_eq hθ1 hθ12 hsum m hr
  have hpc' : Continuous (fun t : ℝ => π*I/2*
      ferrersP ν 0 (AdditionTheorem.ferrersArg (κ*r) r t)) := by fun_prop
  rw [hf,AdditionTheorem.coeff_add hqc hpc',
    AdditionTheorem.coeff_const_mul,hp,hq,localCombination]
  rw [← ofReal_mul,← ofReal_cos,← ofReal_cos,ferrersPCont_ofReal ν (-m) hI1,
    ferrersQCont_ofReal,ferrersPCont_ofReal ν m hI2]
  ring

/-- The lower-half-plane Q branch agrees with the continued Ferrers combination in the disk. -/
lemma associatedQ_eq_localCombination {ν μ z : ℂ} (hr : LegendreQRegular ν μ)
    (hz : z ∈ Metric.ball (0:ℂ) 1) (him : z.im < 0) :
    associatedQ ν μ z = exp (μ*π*I/2)*localCombination ν μ z := by
  have hG : Gamma (ν+μ+1) ≠ 0 := Gamma_ne_zero (fun n hn => hr n (by linear_combination hn))
  have he : exp (μ*π*I)*exp (-(μ*π*I)/2) = exp (μ*π*I/2) := by
    rw [← exp_add]
    congr 1
    ring
  rw [associatedQ,olverQ_eq_olverQSide (s := -1) (Or.inr rfl) hr hz (by simpa using him)]
  simp only [olverQSide,ofReal_neg,ofReal_one,neg_mul,one_mul,localCombination]
  rw [show -(μ*π*I)/2 = -μ*π*I/2 by ring] at he
  field_simp
  rw [show -(μ*π*I/2) = -μ*π*I/2 by ring,he]
  ring


/-- The Fourier coefficient difference for the continued Ferrers combination. -/
def localDifference (κ : ℝ) (ν : ℂ) (m : ℕ) (w : ℂ) : ℂ :=
  AdditionTheorem.coeff (fun t => localCombination ν 0 (argument κ w t)) m -
    (-1:ℂ)^m*ferrersPCont ν (-m) (cos (κ*w))*localCombination ν m (cos w)

/-- The Fourier coefficient difference for the principal exterior Legendre Q function. -/
def difference (κ : ℝ) (ν : ℂ) (m : ℕ) (w : ℂ) : ℂ :=
  AdditionTheorem.coeff (fun t => associatedQ ν 0 (argument κ w t)) m -
    (-1:ℂ)^m*associatedP ν (-m) (cos (κ*w))*associatedQ ν m (cos w)

/-- The continued Ferrers combination is analytic in the unit disk. -/
lemma analyticOnNhd_localCombination (ν μ : ℂ) :
    AnalyticOnNhd ℂ (localCombination ν μ) (Metric.ball (0:ℂ) 1) := by
  intro z hz
  exact (ferrersQCont_analytic ν μ z hz).add
    (analyticAt_const.mul (ferrersPCont_analytic ν μ z hz))

/-- The Ferrers coefficient difference is holomorphic in the disk neighborhood. -/
lemma differentiableOn_localDifference (κ : ℝ) (ν : ℂ) (m : ℕ) :
    DifferentiableOn ℂ (localDifference κ ν m) (localDomain κ) := by
  have hC := (analyticOnNhd_localCombination ν m).differentiableOn
  have hP := (ferrersPCont_analytic ν (-m)).differentiableOn
  have hcoef := differentiableOn_coefficient (isOpen_localDomain κ)
    (analyticOnNhd_localCombination ν 0).differentiableOn
    (fun w hw t => argument_mem_ball hw t) (m:ℤ)
  have hp : DifferentiableOn ℂ (fun w => ferrersPCont ν (-m) (cos (κ*w))) (localDomain κ) :=
    hP.comp (by fun_prop : Differentiable ℂ (fun w : ℂ => cos (κ*w))).differentiableOn
      (fun w hw => by simpa only [Metric.mem_ball,dist_zero_right] using hw.2.1)
  have hc : DifferentiableOn ℂ (fun w => localCombination ν m (cos w)) (localDomain κ) :=
    hC.comp Complex.differentiable_cos.differentiableOn
      (fun w hw => by simpa only [Metric.mem_ball,dist_zero_right] using hw.2.2)
  exact hcoef.sub ((hp.const_mul _).mul hc)

/-- The exterior Q coefficient difference is holomorphic on the angular continuation strip. -/
lemma differentiableOn_difference {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (ν : ℂ) (m : ℕ) :
    DifferentiableOn ℂ (difference κ ν m) (domain κ) := by
  have hp : DifferentiableOn ℂ (fun w => associatedP ν (-m) (cos (κ*w))) (domain κ) := by
    intro w hw
    exact ((associatedP_analytic ν (-m) _
      (cos_mul_sub_one_mem_slitPlane hκ0 hκ1 hκ0 (by linarith) hw)).differentiableAt.comp w
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => cos (κ*w)) w)).differentiableWithinAt
  have hq : DifferentiableOn ℂ (fun w => associatedQ ν m (cos w)) (domain κ) := by
    intro w hw
    have hz : cos w-1 ∈ slitPlane := by
      simpa only [ofReal_one,one_mul] using
        cos_mul_sub_one_mem_slitPlane hκ0 hκ1 (by norm_num : (0:ℝ) < 1) (by linarith) hw
    exact ((analyticAt_const.mul (olverQ_analytic ν m _ hz)).differentiableAt.comp w
      (Complex.differentiable_cos w)).differentiableWithinAt
  exact (differentiableOn_coefficient_associatedQ hκ0 hκ1 ν m).sub ((hp.const_mul _).mul hq)

/-- Regularity at order zero implies regularity at every nonnegative integer order. -/
lemma legendreQRegular_nat_order {ν : ℂ} (hr : LegendreQRegular ν 0) (m : ℕ) :
    LegendreQRegular ν m := by
  intro n hn
  apply hr (n+m)
  push_cast
  linear_combination hn

/-- The lower-half-plane branch phases cancel in the coefficient product. -/
lemma difference_eq_localDifference {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    {ν : ℂ} (hr : LegendreQRegular ν 0) (m : ℕ) {w : ℂ}
    (hwD : w ∈ domain κ) (hwL : w ∈ localDomain κ) :
    difference κ ν m w = localDifference κ ν m w := by
  have hQ : (fun t => associatedQ ν 0 (argument κ w t)) =
      (fun t => localCombination ν 0 (argument κ w t)) := by
    funext t
    simpa only [zero_mul,zero_div,exp_zero,one_mul] using
      associatedQ_eq_localCombination hr (argument_mem_ball hwL t)
        (im_argument_neg hκ0 hκ1 hwD t)
  have hP := associatedP_eq_ferrersPCont (s := -1) (Or.inr rfl) ν (-m)
    (show 0 < (-1:ℝ)*(cos (κ*w)).im by
      have h := im_cos_mul_neg hκ0 hκ1 hκ0 (by linarith) hwD
      linarith)
  have hQ2 := associatedQ_eq_localCombination (legendreQRegular_nat_order hr m)
    (show cos w ∈ Metric.ball (0:ℂ) 1 by simpa only [Metric.mem_ball,dist_zero_right] using hwL.2.2)
    (show (cos w).im < 0 by
      simpa using im_cos_mul_neg hκ0 hκ1 (by norm_num : (0:ℝ) < 1) (by linarith) hwD)
  dsimp only [difference,localDifference]
  rw [hQ,hP,hQ2]
  simp only [ofReal_neg,ofReal_one,neg_mul,one_mul,neg_neg]
  have he : exp (-(m:ℂ)*π*I/2)*exp ((m:ℂ)*π*I/2) = 1 := by
    rw [← exp_add]
    convert exp_zero using 1 <;> ring
  rw [show -((m:ℂ)*π*I)/2 = -(m:ℂ)*π*I/2 by ring]
  linear_combination (-(-1:ℂ)^m*ferrersPCont ν (-m) (cos (κ*w))*
    localCombination ν m (cos w))*he


/-- The identity theorem extends the real Ferrers coefficient identity to a complex ball. -/
lemma exists_ball_localDifference_zero {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    {ν : ℂ} (hr : LegendreQRegular ν 0) (m : ℕ) :
    ∃ r : ℝ, 0 < r ∧ (1+κ)*r < π ∧ ∃ ε : ℝ, 0 < ε ∧
      Metric.ball (r:ℂ) ε ⊆ localDomain κ ∧
      ∀ w ∈ Metric.ball (r:ℂ) ε, localDifference κ ν m w = 0 := by
  let r : ℝ := π/(4*(1+κ))
  have hden : 0 < 1+κ := by linarith
  have hr0 : 0 < r := div_pos Real.pi_pos (by positivity)
  have hrval : (1+κ)*r = π/4 := by dsimp [r]; field_simp
  have hπ4 : (1+κ)*r < π/2 := by rw [hrval]; linarith [Real.pi_pos]
  have hπ : (1+κ)*r < π := by linarith [Real.pi_pos]
  have hrL := ofReal_mem_localDomain hκ0 hκ1 hr0 hπ4
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (isOpen_localDomain κ) (r:ℂ) hrL
  have han : AnalyticOnNhd ℂ (localDifference κ ν m) (Metric.ball (r:ℂ) ε) :=
    ((differentiableOn_localDifference κ ν m).mono hball).analyticOnNhd Metric.isOpen_ball
  have ht : Tendsto (fun t : ℝ => (t:ℂ)) (𝓝[≠] r) (𝓝[≠] (r:ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (continuous_ofReal.tendsto r).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa only [Set.mem_compl_iff,Set.mem_singleton_iff,ofReal_inj] using ht
  have hri : Ioo 0 (π/(1+κ)) ∈ 𝓝 r := Ioo_mem_nhds hr0 (by
    rw [lt_div_iff₀ hden]
    simpa only [mul_comm] using hπ)
  have he : ∀ᶠ t : ℝ in 𝓝[≠] r, localDifference κ ν m (t:ℂ) = 0 := by
    filter_upwards [nhdsWithin_le_nhds hri] with t htI
    apply sub_eq_zero.mpr
    exact coeff_localCombination_real hκ0 hκ1 htI.1 (by
      have ht := (lt_div_iff₀ hden).mp htI.2
      simpa only [mul_comm] using ht) hr m
  have hz := han.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
    (convex_ball _ _).isPreconnected (Metric.mem_ball_self hε) (ht.frequently he.frequently)
  exact ⟨r,hr0,hπ,ε,hε,hball,fun w hw => hz hw⟩

/-- The coefficient identity extends throughout the connected angular continuation strip. -/
lemma difference_eq_zero {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    {ν : ℂ} (hr : LegendreQRegular ν 0) (m : ℕ) :
    ∀ w ∈ domain κ, difference κ ν m w = 0 := by
  obtain ⟨r,hr0,hrπ,ε,hε,hball,hzero⟩ := exists_ball_localDifference_zero hκ0 hκ1 hr m
  let w0 : ℂ := r+(ε/2:ℝ)*I
  have hw0D : w0 ∈ domain κ := by
    dsimp [domain,w0]
    simpa only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_zero,
      add_zero,add_im,mul_im,zero_add,mul_one] using And.intro hr0 (And.intro hrπ (half_pos hε))
  have hw0B : w0 ∈ Metric.ball (r:ℂ) ε := by
    rw [Metric.mem_ball,dist_eq_norm]
    rw [show w0-(r:ℂ) = (ε/2:ℝ)*I by dsimp [w0];ring,norm_mul,norm_I,mul_one,
      norm_real,Real.norm_eq_abs,abs_of_pos (half_pos hε)]
    linarith
  have he : difference κ ν m =ᶠ[𝓝 w0] 0 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hw0B,(isOpen_domain κ).mem_nhds hw0D] with w hwB hwD
    rw [difference_eq_localDifference hκ0 hκ1 hr m hwD (hball hwB)]
    exact hzero w hwB
  exact ((differentiableOn_difference hκ0 hκ1 ν m).analyticOnNhd (isOpen_domain κ))
    |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_domain hκ0).isPreconnected hw0D he


/-- The neighborhood where both cosine endpoints and individual arguments have real part
greater than one. -/
def exteriorDomain (κ : ℝ) : Set ℂ :=
  {w | 1 < (cos ((1-κ)*w)).re ∧ 1 < (cos ((1+κ)*w)).re ∧
    1 < (cos (κ*w)).re ∧ 1 < (cos w).re}

/-- The exterior neighborhood of angular parameters is open. -/
lemma isOpen_exteriorDomain (κ : ℝ) : IsOpen (exteriorDomain κ) := by
  change IsOpen ({w : ℂ | 1 < (cos ((1-κ)*w)).re} ∩
    ({w : ℂ | 1 < (cos ((1+κ)*w)).re} ∩
    ({w : ℂ | 1 < (cos (κ*w)).re} ∩ {w : ℂ | 1 < (cos w).re})))
  exact (isOpen_lt continuous_const (by fun_prop)).inter
    ((isOpen_lt continuous_const (by fun_prop)).inter
    ((isOpen_lt continuous_const (by fun_prop)).inter
      (isOpen_lt continuous_const (by fun_prop))))

/-- The combined argument has real part greater than one in the exterior neighborhood. -/
lemma argument_re_gt_one {κ : ℝ} {w : ℂ} (hw : w ∈ exteriorDomain κ) (t : ℝ) :
    1 < (argument κ w t).re := by
  have hm := hw.1
  have hp := hw.2.1
  push_cast at hm hp
  rw [argument_eq_cos_sub_add]
  simp only [add_re,mul_re,div_ofNat_re,div_ofNat_im,one_re,one_im,ofReal_re,ofReal_im,
    add_zero,sub_zero,zero_mul,mul_zero,zero_div,sub_re,sub_im,add_im]
  let a := (cos ((1-(κ:ℂ))*w)).re
  let b := (cos ((1+(κ:ℂ))*w)).re
  have hmin : 1 < min a b := lt_min hm hp
  have hm0 : 0 ≤ a-min a b := sub_nonneg.mpr (min_le_left _ _)
  have hp0 : 0 ≤ b-min a b := sub_nonneg.mpr (min_le_right _ _)
  have hc0 : 0 ≤ 1+Real.cos t := by linarith [Real.neg_one_le_cos t]
  have hc1 : 0 ≤ 1-Real.cos t := by linarith [Real.cos_le_one t]
  dsimp [a,b] at hm0 hp0 hmin
  nlinarith [mul_nonneg hc0 hm0,mul_nonneg hc1 hp0]

/-- The coefficient difference is holomorphic in the exterior neighborhood. -/
lemma differentiableOn_difference_exterior (κ : ℝ) (ν : ℂ) (m : ℕ) :
    DifferentiableOn ℂ (difference κ ν m) (exteriorDomain κ) := by
  have hmem {z : ℂ} (hz : 1 < z.re) : z-1 ∈ slitPlane := Or.inl (by simp;linarith)
  have hp : DifferentiableOn ℂ (fun w => associatedP ν (-m) (cos (κ*w))) (exteriorDomain κ) := by
    intro w hw
    exact ((associatedP_analytic ν (-m) _ (hmem hw.2.2.1)).differentiableAt.comp w
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => cos (κ*w)) w)).differentiableWithinAt
  have hq : DifferentiableOn ℂ (fun w => associatedQ ν m (cos w)) (exteriorDomain κ) := by
    intro w hw
    exact ((analyticAt_const.mul (olverQ_analytic ν m _ (hmem hw.2.2.2))).differentiableAt.comp w
      (Complex.differentiable_cos w)).differentiableWithinAt
  have hcoef : DifferentiableOn ℂ (fun w => AdditionTheorem.coeff
      (fun t => associatedQ ν 0 (argument κ w t)) m) (exteriorDomain κ) := by
    apply differentiableOn_coefficient (isOpen_exteriorDomain κ) (S := {z : ℂ | z-1 ∈ slitPlane})
    · intro z hz
      exact ((analyticAt_const.mul (olverQ_analytic ν 0 z hz)).differentiableAt)
      |>.differentiableWithinAt
    · intro w hw t
      exact hmem (argument_re_gt_one hw t)
  exact hcoef.sub ((hp.const_mul _).mul hq)

/-- Continuity extends the coefficient identity to positive imaginary angles. -/
lemma difference_mul_I_eq_zero {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    {ν : ℂ} (hr : LegendreQRegular ν 0) (m : ℕ) {u : ℝ} (hu : 0 < u) :
    difference κ ν m ((u:ℂ)*I) = 0 := by
  have hcos {r : ℝ} (hr : 0 < r) : 1 < (cos ((r:ℂ)*((u:ℂ)*I))).re := by
    rw [show (r:ℂ)*((u:ℂ)*I) = ((r*u:ℝ):ℂ)*I by push_cast;ring,cos_mul_I,cosh_ofReal_re]
    exact Real.one_lt_cosh.mpr (mul_pos hr hu).ne'
  have hwE : (u:ℂ)*I ∈ exteriorDomain κ := by
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [ofReal_sub,ofReal_one] using hcos (by linarith : 0 < 1-κ)
    · simpa only [ofReal_add,ofReal_one] using hcos (by linarith : 0 < 1+κ)
    · exact hcos hκ0
    · simpa only [ofReal_one,one_mul] using hcos (by norm_num : (0:ℝ) < 1)
  have hc : ContinuousAt (difference κ ν m) ((u:ℂ)*I) :=
    ((differentiableOn_difference_exterior κ ν m _ hwE).differentiableAt
      ((isOpen_exteriorDomain κ).mem_nhds hwE)).continuousAt
  have ht : Tendsto (fun ε : ℝ => (ε:ℂ)+(u:ℂ)*I) (𝓝[>] 0) (𝓝 ((u:ℂ)*I)) := by
    simpa using ((continuous_ofReal.tendsto 0).add_const ((u:ℂ)*I)).mono_left nhdsWithin_le_nhds
  have hden : 0 < 1+κ := by linarith
  have he : (fun ε : ℝ => difference κ ν m ((ε:ℂ)+(u:ℂ)*I)) =ᶠ[𝓝[>] 0] 0 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (div_pos Real.pi_pos hden))] with ε he0 he1
    apply difference_eq_zero hκ0 hκ1 hr m
    dsimp [domain]
    simp only [add_re,add_im,ofReal_re,ofReal_im,mul_re,mul_im,I_re,I_im,mul_zero,
      zero_mul,sub_zero,zero_add,add_zero,mul_one]
    exact ⟨he0,by simpa only [mul_comm] using (lt_div_iff₀ hden).mp he1,hu⟩
  exact tendsto_nhds_unique (hc.tendsto.comp ht) (tendsto_const_nhds.congr' he.symm)


/-- The hyperbolic Q Fourier coefficients are `(-1)^m P_ν^{-m}(cosh ξ₁) Q_ν^m(cosh ξ₂)`. -/
lemma coefficient_associatedQ_hyperbolicArg {ν : ℂ} (hr : LegendreQRegular ν 0)
    {ξ₁ ξ₂ : ℝ} (h1 : 0 < ξ₁) (h2 : 0 < ξ₂) (h12 : ξ₁ < ξ₂) (m : ℕ) :
    AdditionTheorem.coeff (fun t => associatedQ ν 0 (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t)) m =
      (-1:ℂ)^m*associatedP ν (-m) (Real.cosh ξ₁)*associatedQ ν m (Real.cosh ξ₂) := by
  let κ := ξ₁/ξ₂
  have hκ0 : 0 < κ := div_pos h1 h2
  have hκ1 : κ < 1 := (div_lt_one h2).mpr h12
  have hκu : (κ:ℂ)*(ξ₂:ℂ) = ξ₁ := by dsimp [κ];push_cast;field_simp [ofReal_ne_zero.mpr h2.ne']
  have he := sub_eq_zero.mp (difference_mul_I_eq_zero hκ0 hκ1 hr m h2)
  have hcos1 : cos ((κ:ℂ)*((ξ₂:ℂ)*I)) = Real.cosh ξ₁ := by
    rw [← mul_assoc,hκu,cos_mul_I,← ofReal_cosh]
  have hcos2 : cos ((ξ₂:ℂ)*I) = Real.cosh ξ₂ := by rw [cos_mul_I,← ofReal_cosh]
  have harg (t : ℝ) : argument κ ((ξ₂:ℂ)*I) t = AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t := by
    dsimp [argument,AdditionTheorem.hyperbolicArg]
    rw [hcos1,hcos2,← mul_assoc (κ:ℂ),hκu,sin_mul_I,sin_mul_I]
    push_cast
    rw [← ofReal_cosh,← ofReal_cosh,← ofReal_sinh,← ofReal_sinh]
    ring_nf
    simp only [I_sq]
    ring
  simpa only [hcos1,hcos2,harg] using he

/-- Ordered positive hyperbolic angles keep the combined argument strictly greater than one. -/
lemma hyperbolicArg_gt_one {ξ₁ ξ₂ : ℝ} (h1 : 0 < ξ₁) (h2 : 0 < ξ₂) (h12 : ξ₁ < ξ₂)
    (t : ℝ) : 1 < AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t := by
  have hs1 := Real.sinh_pos_iff.mpr h1
  have hs2 := Real.sinh_pos_iff.mpr h2
  have hcosh : 1 < Real.cosh (ξ₂-ξ₁) := Real.one_lt_cosh.mpr (sub_pos.mpr h12).ne'
  have hbound : Real.cosh (ξ₂-ξ₁) ≤ AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t := by
    rw [Real.cosh_sub]
    dsimp [AdditionTheorem.hyperbolicArg]
    nlinarith [mul_nonneg hs1.le hs2.le,Real.cos_le_one t]
  exact hcosh.trans_le hbound

/-- The exterior Q angular kernel is twice continuously differentiable. -/
lemma contDiff_associatedQ_hyperbolicArg {ν : ℂ} {ξ₁ ξ₂ : ℝ} (h1 : 0 < ξ₁) (h2 : 0 < ξ₂)
    (h12 : ξ₁ < ξ₂) :
    ContDiff ℝ 2 (fun t => associatedQ ν 0 (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t)) := by
  let S : Set ℂ := {z | z-1 ∈ slitPlane}
  have hSo : IsOpen S := isOpen_slitPlane.preimage (by fun_prop)
  have hQ : DifferentiableOn ℂ (associatedQ ν 0) S := by
    intro z hz
    exact (analyticAt_const.mul (olverQ_analytic ν 0 z hz)).differentiableAt.differentiableWithinAt
  have hQ2 : ContDiffOn ℝ 2 (associatedQ ν 0) S := (hQ.contDiffOn hSo).restrict_scalars ℝ
  have hgR : ContDiff ℝ 2 (AdditionTheorem.hyperbolicArg ξ₁ ξ₂) := by
    change ContDiff ℝ 2 (fun t : ℝ =>
      Real.cosh ξ₁*Real.cosh ξ₂-Real.sinh ξ₁*Real.sinh ξ₂*Real.cos t)
    fun_prop
  have hg : ContDiff ℝ 2 (fun t : ℝ => (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t:ℂ)) :=
    ofRealCLM.contDiff.comp hgR
  exact hQ2.comp_contDiff hg (fun t => by
    left
    simp only [sub_re,one_re,ofReal_re]
    have ht := hyperbolicArg_gt_one h1 h2 h12 t
    linarith)

/-- The exterior Legendre Q addition theorem, with its principal branch and ordered radii
(DLMF 14.18.5). -/
lemma hasSum_addition {ν : ℂ} (hr : LegendreQRegular ν 0)
    {ξ₁ ξ₂ : ℝ} (h1 : 0 < ξ₁) (h2 : 0 < ξ₂) (h12 : ξ₁ < ξ₂) (phi : ℝ) :
    HasSum (fun j : ℕ => let m:=j+1;
        2*(-1)^m*associatedP ν (-m) (Real.cosh ξ₁)*associatedQ ν m (Real.cosh ξ₂)*Real.cos (m*phi))
        (associatedQ ν 0 (Real.cosh ξ₁*Real.cosh ξ₂-Real.sinh ξ₁*Real.sinh ξ₂*Real.cos
        phi)-associatedP ν 0 (Real.cosh ξ₁)*associatedQ ν 0 (Real.cosh ξ₂)) := by
  have hp : Function.Periodic (fun t => associatedQ ν 0
      (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t)) (2*π) := by
    intro t
    simp only [AdditionTheorem.hyperbolicArg,Real.cos_add_two_pi]
  have he : ∀ t, (fun t => associatedQ ν 0 (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t)) (-t) =
      (fun t => associatedQ ν 0 (AdditionTheorem.hyperbolicArg ξ₁ ξ₂ t)) t := by
    intro t
    simp only [AdditionTheorem.hyperbolicArg,Real.cos_neg]
  have hs := AdditionTheorem.hasSum_cos (contDiff_associatedQ_hyperbolicArg h1 h2 h12) hp he phi
  have h0 := coefficient_associatedQ_hyperbolicArg hr h1 h2 h12 0
  simp only [Nat.cast_zero,neg_zero,pow_zero,one_mul] at h0
  convert hs using 1
  · funext j
    rw [coefficient_associatedQ_hyperbolicArg hr h1 h2 h12 (j+1)]
    push_cast
    ring
  · rw [h0]
    simp only [AdditionTheorem.hyperbolicArg]
    push_cast
    rfl

end DLMF.Legendre.ExteriorAddition
