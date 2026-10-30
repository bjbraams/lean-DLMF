/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Associated.QuadraticFerrers

/-!
# Conjugation and special associated Legendre values

Conjugation symmetry and special-parameter relations for associated Legendre functions.

Source references and common attribution are retained in
`DLMF.Legendre.Associated`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat ComplexConjugate

namespace DLMF.Legendre

/-! ### Conjugation symmetry -/

/-- Rising factorials commute with complex conjugation. -/
theorem ascPochhammer_eval_conj (n : ℕ) (a : ℂ) :
    (ascPochhammer ℂ n).eval (conj a) = conj ((ascPochhammer ℂ n).eval a) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ascPochhammer_succ_eval, ih]

/-- Conjugation symmetry of the regularized Gauss function on the unit disk. -/
theorem regularizedGaussHG_conj {a b c z : ℂ} (hz : ‖z‖ < 1) :
    conj (regularizedGaussHG a b c z) =
      regularizedGaussHG (conj a) (conj b) (conj c) (conj z) := by
  have hz' : ‖conj z‖ < 1 := by rwa [RCLike.norm_conj]
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz', regularizedGaussHGFun_eq_tsum,
    regularizedGaussHGFun_eq_tsum, Complex.conj_tsum]
  congr 1
  funext n
  simp [ascPochhammer_eval_conj, ← Gamma_conj, map_div₀]

/-- Real parameters and a real argument in the unit disk give a real Gauss value. -/
theorem regularizedGaussHG_real_im {a b c z : ℝ} (hz : |z| < 1) :
    (regularizedGaussHG a b c z).im = 0 := by
  rw [← conj_eq_iff_im, regularizedGaussHG_conj (by simpa using hz)]
  simp

/-- `conj (r^w) = r^(conj w)` for positive real `r`. -/
theorem conj_ofReal_cpow {r : ℝ} (hr : 0 < r) (w : ℂ) : conj ((r:ℂ)^w) = (r:ℂ)^(conj w) := by
  rw [cpow_conj _ _ (by rw [arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm), conj_ofReal]

/-- Conjugation symmetry of the Ferrers function of the first kind. -/
theorem ferrersP_conj (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    conj (ferrersP ν μ x) = ferrersP (conj ν) (conj μ) x := by
  have h1 : (0:ℝ) < 1+x := by linarith [hx.1]
  have h2 : (0:ℝ) < 1-x := by linarith [hx.2]
  have hz : ‖(1-(x:ℂ))/2‖ < 1 := by
    rw [show (1-(x:ℂ))/2=(((1-x)/2:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hx.1,hx.2]
  unfold ferrersP
  rw [map_mul, conj_ofReal_cpow (div_pos h1 h2), regularizedGaussHG_conj hz]
  simp [map_div₀, map_ofNat]

/-- `conj (2^w) = 2^(conj w)`. -/
theorem conj_two_cpow (w : ℂ) : conj ((2:ℂ)^w) = 2^(conj w) := by
  simpa using conj_ofReal_cpow two_pos w

/-- `x² ` lies in the unit disk for `x ∈ (-1,1)`. -/
theorem ferrers_norm_sq_lt_one {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) : ‖(x:ℂ)^2‖ < 1 := by
  rw [norm_pow, norm_real, Real.norm_eq_abs, sq_abs]; nlinarith [hx.1, hx.2]

/-- `conj ((1-x²)^w) = (1-x²)^(conj w)` on `(-1,1)`. -/
theorem conj_one_sub_sq_cpow {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) (w : ℂ) :
    conj ((1-(x:ℂ)^2)^w) = (1-(x:ℂ)^2)^(conj w) := by
  have h := conj_ofReal_cpow (r := 1-x^2) (by nlinarith [hx.1, hx.2]) w
  push_cast at h
  exact h

/-- Conjugation symmetry of the even quadratic solution. -/
theorem ferrersEven_conj (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    conj (ferrersEven ν μ x) = ferrersEven (conj ν) (conj μ) x := by
  unfold ferrersEven
  rw [map_mul, conj_one_sub_sq_cpow hx, regularizedGaussHG_conj (ferrers_norm_sq_lt_one hx)]
  simp [map_div₀, map_ofNat]

/-- Conjugation symmetry of the odd quadratic solution. -/
theorem ferrersOdd_conj (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    conj (ferrersOdd ν μ x) = ferrersOdd (conj ν) (conj μ) x := by
  unfold ferrersOdd
  rw [map_mul, map_mul, conj_one_sub_sq_cpow hx, regularizedGaussHG_conj (ferrers_norm_sq_lt_one hx)]
  simp [map_div₀, map_ofNat]

/-- Conjugation symmetry of the Ferrers function of the second kind. -/
theorem ferrersQ_conj (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    conj (ferrersQ ν μ x) = ferrersQ (conj ν) (conj μ) x := by
  rw [ferrersQ_even_odd, ferrersQ_even_odd]
  simp [map_div₀, map_ofNat, ← sin_conj, ← cos_conj, ← Gamma_conj, ferrersEven_conj _ _ hx,
    ferrersOdd_conj _ _ hx, conj_two_cpow]

/-- DLMF 14.3.10: when `ν+μ ∉ {-1,-2,…}`, Olver's function satisfies `𝑸^μ_ν(z) = e^{-μπi}
Q^μ_ν(z)/Γ(ν+μ+1)` for every `z`. -/
@[dlmf 14.3.E10]
theorem olverQ_normalization {ν μ : ℂ} (h : LegendreQRegular ν μ) (z : ℂ) :
    olverQ ν μ z = exp (-μ*π*I)*associatedQ ν μ z/Gamma (ν+μ+1) := by
  have hG : Gamma (ν+μ+1) ≠ 0 := Gamma_ne_zero (fun n he => h n (by linear_combination he))
  simp only [associatedQ, neg_mul, Complex.exp_neg]
  field_simp

/-- Compatibility with the existing degree-only Legendre function. -/
theorem associatedP_zero_order (ν : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν 0 z=legendreP ν z := by
  have hz' : 1+z ∈ slitPlane := by
    rw [mem_slitPlane_iff] at hz ⊢
    rcases hz with h | h
    · left; simp at h ⊢; linarith
    · right; simpa using h
  simpa [associatedP,legendreP] using
    regularizedGaussHG_symm (ν+1) (-ν) 1 (mem_cutPlane_of_one_add hz')

/-- Compatibility of the totalized degree-only APIs; classical Q additionally requires regular degree. -/
theorem associatedQ_zero_order (ν : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedQ ν 0 z=legendreQ ν z := by
  simp only [associatedQ, olverQ, legendreQ, legendreBranchPower, zero_mul, zero_div,
    Complex.exp_zero, mul_one, one_mul, add_zero, cpow_neg]
  ring

/-- At order zero and natural degree, `𝑸_n = Q_n/n!`. -/
theorem legInt_olverQ_nat_zero_order (n : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ n 0 z = legendreQ n z / n.factorial := by
  have hreg : LegendreQRegular (n:ℂ) 0 := fun k hk => by
    have := congrArg re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  rw [olverQ_normalization hreg, associatedQ_zero_order _ hz, add_zero, Gamma_nat_eq_factorial]
  simp

/-- `P^μ_ν(z)` is analytic in `z` for `z-1` in the slit plane (`z ∉ (-∞, 1]`), for all complex `ν,
μ`. -/
theorem associatedP_analytic (ν μ : ℂ) :
    AnalyticOnNhd ℂ (associatedP ν μ) {z : ℂ | z-1 ∈ slitPlane} := by
  intro z hz
  have hp : z+1 ∈ slitPlane := by simpa [add_comm] using one_add_mem_slitPlane_of_sub_one hz
  have hG : AnalyticAt ℂ (fun w : ℂ =>
      regularizedGaussHG (ν+1) (-ν) (1-μ) ((1-w)/2)) z :=
    (analyticAt_regularizedGaussHG _ _ _ (mem_cutPlane_of_one_add (by simpa [add_comm] using hp))).comp_of_eq
      (by fun_prop) rfl
  unfold associatedP
  have hP : AnalyticAt ℂ (fun w : ℂ => exp (μ/2*(log (w+1)-log (w-1)))) z := by
    fun_prop (disch := assumption)
  exact hP.mul hG

/-- Entire parameter dependence on the principal sheet. -/
theorem associatedP_entire_degree (μ : ℂ) :
    ∀ z : ℂ, z-1 ∈ slitPlane → Differentiable ℂ (fun ν => associatedP ν μ z) := by
  intro z hz
  have hw := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  unfold associatedP
  exact (differentiable_const _).mul
    (differentiable_regularizedGaussHG_comp (by fun_prop) (by fun_prop) (by fun_prop) hw)

/-- Entire parameter dependence on the principal sheet. -/
theorem associatedP_entire_order (ν : ℂ) :
    ∀ z : ℂ, z-1 ∈ slitPlane → Differentiable ℂ (fun μ => associatedP ν μ z) := by
  intro z hz
  have hw := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  unfold associatedP
  exact (by fun_prop : Differentiable ℂ fun μ : ℂ => exp (μ/2*(log (z+1)-log (z-1)))).mul
    (differentiable_regularizedGaussHG_comp (by fun_prop) (by fun_prop) (by fun_prop) hw)

/-- The logarithmic gauge derivative for associated P, before imposing its degree parameters. -/
theorem hasDerivAt_associatedP_aux (a b c μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    HasDerivAt (fun w : ℂ => exp (μ/2*(log (w+1)-log (w-1)))*regularizedGaussHG a b c ((1-w)/2))
      (μ/(1-z^2)*(exp (μ/2*(log (z+1)-log (z-1)))*regularizedGaussHG a b c ((1-z)/2))-
        a*b/2*(exp (μ/2*(log (z+1)-log (z-1)))*regularizedGaussHG (a+1) (b+1) (c+1) ((1-z)/2))) z := by
  have hp : z+1 ∈ slitPlane := by simpa [add_comm] using one_add_mem_slitPlane_of_sub_one hz
  have hm0 := slitPlane_ne_zero hz
  have hp0 := slitPlane_ne_zero hp
  have he := (((hasDerivAt_id z).add_const 1).clog hp).sub
    (((hasDerivAt_id z).sub_const 1).clog hz)
  have hE := (he.const_mul (μ/2)).cexp
  have hG := hasDerivAt_regularizedGaussHG_half a b c (one_add_mem_slitPlane_of_sub_one hz)
  refine (hE.mul hG).congr_deriv ?_
  simp only [id_eq, Pi.sub_apply]
  have hne : 1-z^2 ≠ 0 := by
    intro h
    have hfac : (z-1)*(z+1)=0 := by linear_combination -h
    exact (mul_ne_zero hm0 hp0) hfac
  field_simp
  ring

/-- DLMF 14.2.2 / 14.21.1: for `z-1` in the slit plane (`z ∉ (-∞, 1]`), `w = P^μ_ν(z)` satisfies the
associated Legendre equation `(1-z²) w'' - 2z w' + (ν(ν+1) - μ²/(1-z²)) w = 0`. -/
@[dlmf 14.2.E2, dlmf 14.21.E1]
theorem associatedP_ode (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (1-z^2)*iteratedDeriv 2 (associatedP ν μ) z-2*z*deriv (associatedP ν μ) z+(ν*(ν+1)-μ^2/(1-z^2))*associatedP ν μ z=0 := by
  have hd (w : ℂ) (hw : w-1 ∈ slitPlane) := hasDerivAt_associatedP_aux (ν+1) (-ν) (1-μ) μ hw
  have hev : deriv (associatedP ν μ) =ᶠ[𝓝 z] fun w =>
      μ/(1-w^2)*(exp (μ/2*(log (w+1)-log (w-1)))*regularizedGaussHG (ν+1) (-ν) (1-μ) ((1-w)/2))-
        (ν+1)*(-ν)/2*(exp (μ/2*(log (w+1)-log (w-1)))*regularizedGaussHG (ν+1+1) (-ν+1) (1-μ+1) ((1-w)/2)) := by
    filter_upwards [isOpen_sub_one_mem_slitPlane.mem_nhds hz] with w hw
    exact (hd w hw).deriv
  have hm0 := slitPlane_ne_zero hz
  have hp0 := slitPlane_ne_zero (one_add_mem_slitPlane_of_sub_one hz)
  have hne : 1-z^2 ≠ 0 := by
    intro h
    have hfac : (z-1)*(1+z)=0 := by linear_combination -h
    exact (mul_ne_zero hm0 hp0) hfac
  have hq : HasDerivAt (fun w : ℂ => μ/(1-w^2)) (μ*(2*z/(1-z^2)^2)) z := by
    convert ((((hasDerivAt_pow 2 z).const_sub 1).inv hne).const_mul μ) using 1
    · funext w
      simp [div_eq_mul_inv]
    · field_simp
      ring
  have h2 := (hq.mul (hd z hz)).sub
    ((hasDerivAt_associatedP_aux (ν+1+1) (-ν+1) (1-μ+1) μ hz).const_mul ((ν+1)*(-ν)/2))
  have h2' : HasDerivAt (fun w : ℂ =>
      μ/(1-w^2)*(exp (μ/2*(log (w+1)-log (w-1)))*regularizedGaussHG (ν+1) (-ν) (1-μ) ((1-w)/2))-
        (ν+1)*(-ν)/2*(exp (μ/2*(log (w+1)-log (w-1)))*regularizedGaussHG (ν+1+1) (-ν+1) (1-μ+1) ((1-w)/2))) _ z :=
    h2.congr_of_eventuallyEq (Eventually.of_forall fun w => rfl)
  have hd0 : HasDerivAt (associatedP ν μ) _ z := hd z hz
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq, h2'.deriv, hd0.deriv]
  have hode := regularizedGaussHG_ode (ν+1) (-ν) (1-μ)
    (mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz))
  simp only [poch, ascPochhammer_succ_eval, ascPochhammer_zero, Polynomial.eval_one] at hode
  simp only [associatedP]
  rw [show ν+1+1=ν+2 by ring, show -ν+1+1=-ν+2 by ring,
    show 1-μ+1+1=1-μ+2 by ring]
  generalize exp (μ/2*(log (z+1)-log (z-1)))=A
  field_simp
  ring_nf at hode ⊢
  linear_combination (4*(1-z^2)*A)*hode

/-- For real `ν, μ` and real `x > 1`, `P^μ_ν(x)` is real. -/
theorem associatedP_real (ν μ : ℝ) {x : ℝ} (hx : 1 < x) :
    (associatedP ν μ x).im=0 := by
  have hw : (1-(x:ℂ))/2 ∈ cutPlane := by
    show 1-(1-(x:ℂ))/2 ∈ slitPlane
    left; simp; linarith
  have hz : ‖((1-(x:ℂ))/2)/((1-(x:ℂ))/2-1)‖ < 1 := by
    rw [show ((1-(x:ℂ))/2)/((1-(x:ℂ))/2-1) = (((x-1)/(x+1):ℝ):ℂ) by
      have h1 : (x:ℂ)+1 ≠ 0 := by exact_mod_cast (by linarith : x+1 ≠ 0)
      have h2 : (1-(x:ℂ))/2-1 ≠ 0 := by
        rw [show (1-(x:ℂ))/2-1 = -((x:ℂ)+1)/2 by ring]
        exact div_ne_zero (neg_ne_zero.mpr h1) two_ne_zero
      push_cast; rw [div_eq_div_iff h2 h1]; ring, norm_real, Real.norm_eq_abs, abs_lt]
    constructor
    · have : 0 < (x-1)/(x+1) := div_pos (by linarith) (by linarith)
      linarith
    · rw [div_lt_one (by linarith)]; linarith
  have hb : 1-(1-(x:ℂ))/2 = (((1+x)/2:ℝ):ℂ) := by push_cast; ring
  have hl1 : log ((x:ℂ)-1) = (Real.log (x-1):ℂ) := by
    rw [show (x:ℂ)-1 = ((x-1:ℝ):ℂ) by push_cast; ring, ofReal_log (by linarith)]
  have hl2 : log ((x:ℂ)+1) = (Real.log (x+1):ℂ) := by
    rw [show (x:ℂ)+1 = ((x+1:ℝ):ℂ) by push_cast; ring, ofReal_log (by linarith)]
  rw [← conj_eq_iff_im]
  unfold associatedP
  rw [regularizedGaussHG_pfaff _ _ _ hw, hb, hl1, hl2, map_mul, map_mul, regularizedGaussHG_conj hz,
    ← exp_conj, conj_ofReal_cpow (by linarith)]
  simp [map_div₀, map_ofNat]

/-- `𝑸^μ_ν(z)` is analytic in `z` for `z-1` in the slit plane (`z ∉ (-∞, 1]`), for all complex `ν,
μ`. -/
theorem olverQ_analytic (ν μ : ℂ) :
    AnalyticOnNhd ℂ (olverQ ν μ) {z : ℂ | z-1 ∈ slitPlane} := by
  intro z hz
  have hs := mem_slitPlane_of_sub_one hz
  have hz0 := slitPlane_ne_zero hs
  have hp : z+1 ∈ slitPlane := by simpa [add_comm] using one_add_mem_slitPlane_of_sub_one hz
  have hG : AnalyticAt ℂ (fun w : ℂ => regularizedGaussHG ((ν+μ+2)/2)
      ((ν+μ+1)/2) (ν+3/2) (1/w^2)) z :=
    (analyticAt_regularizedGaussHG _ _ _ (recip_sq_mem_cutPlane hz)).comp_of_eq
      (by fun_prop (disch := exact pow_ne_zero 2 hz0)) rfl
  have hB : AnalyticAt ℂ (legendreBranchPower μ) z := by
    unfold legendreBranchPower
    fun_prop (disch := assumption)
  have hP : AnalyticAt ℂ (fun w : ℂ => w^(ν+μ+1)) z :=
    analyticAt_id.cpow analyticAt_const hs
  have hD : (2:ℂ)^(ν+1)*z^(ν+μ+1) ≠ 0 :=
    mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl (by norm_num))) (cpow_ne_zero_iff.mpr (Or.inl hz0))
  unfold olverQ
  exact ((analyticAt_const.mul hB).div (analyticAt_const.mul hP) hD).mul hG

/-- Entire parameter dependence on the principal sheet. -/
theorem olverQ_entire_degree (μ : ℂ) :
    ∀ z : ℂ, z-1 ∈ slitPlane → Differentiable ℂ (fun ν => olverQ ν μ z) := by
  intro z hz
  have hz0 := slitPlane_ne_zero (mem_slitPlane_of_sub_one hz)
  have : NeZero z := ⟨hz0⟩
  unfold olverQ
  refine (((differentiable_const _).div ((differentiable_const_cpow_of_neZero (2:ℂ) |>.comp
    (by fun_prop : Differentiable ℂ fun ν : ℂ => ν+1)).mul ?_) ?_)).mul
    (differentiable_regularizedGaussHG_comp (by fun_prop) (by fun_prop) (by fun_prop) (recip_sq_mem_cutPlane hz))
  · exact (differentiable_const_cpow_of_neZero z |>.comp (by fun_prop : Differentiable ℂ fun ν : ℂ => ν+μ+1))
  · intro ν
    exact mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)) (cpow_ne_zero_iff.mpr (Or.inl hz0))

/-- Entire parameter dependence on the principal sheet. -/
theorem olverQ_entire_order (ν : ℂ) :
    ∀ z : ℂ, z-1 ∈ slitPlane → Differentiable ℂ (fun μ => olverQ ν μ z) := by
  intro z hz
  have hz0 := slitPlane_ne_zero (mem_slitPlane_of_sub_one hz)
  have : NeZero z := ⟨hz0⟩
  unfold olverQ legendreBranchPower
  refine (((differentiable_const _).mul (by fun_prop)).div ((differentiable_const _).mul ?_) ?_).mul
    (differentiable_regularizedGaussHG_comp (by fun_prop) (by fun_prop) (by fun_prop) (recip_sq_mem_cutPlane hz))
  · exact (differentiable_const_cpow_of_neZero z |>.comp (by fun_prop : Differentiable ℂ fun μ : ℂ => ν+μ+1))
  · intro μ
    exact mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)) (cpow_ne_zero_iff.mpr (Or.inl hz0))

/-- DLMF 14.2.2 / 14.21.1: for `z-1` in the slit plane (`z ∉ (-∞, 1]`), `w = 𝑸^μ_ν(z)` satisfies the
associated Legendre equation `(1-z²) w'' - 2z w' + (ν(ν+1) - μ²/(1-z²)) w = 0`. -/
@[dlmf 14.2.E2, dlmf 14.21.E1]
theorem olverQ_ode (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (1-z^2)*iteratedDeriv 2 (olverQ ν μ) z-2*z*deriv (olverQ ν μ) z+(ν*(ν+1)-μ^2/(1-z^2))*olverQ ν μ z=0 := by
  let a : ℂ := (ν+μ+2)/2
  let b : ℂ := (ν+μ+1)/2
  let c : ℂ := ν+3/2
  let r : ℂ := ν+μ+1
  let F := regularizedGaussHG a b c
  let u : ℂ → ℂ := fun w => 1/w^2
  let v : ℂ → ℂ := fun w => -2/w^3
  let g : ℂ → ℂ := fun w => (Real.sqrt π:ℂ)/2^(ν+1)*
    exp (μ/2*(log (w-1)+log (w+1)))*w^(-r)
  let q : ℂ → ℂ := fun w => μ*w/(w^2-1)-r/w
  have hne (w : ℂ) (hw : w-1∈slitPlane) : w≠0 ∧ w-1≠0 ∧ w+1≠0 ∧ w^2-1≠0 := by
    have hm := slitPlane_ne_zero hw
    have hp : w+1≠0 := by simpa [add_comm] using slitPlane_ne_zero (one_add_mem_slitPlane_of_sub_one hw)
    refine ⟨slitPlane_ne_zero (mem_slitPlane_of_sub_one hw),hm,hp,?_⟩
    intro he; apply mul_ne_zero hm hp; linear_combination he
  have hg (w : ℂ) (hw : w-1∈slitPlane) : HasDerivAt g (g w*q w) w := by
    have hp : w+1∈slitPlane := by simpa [add_comm] using one_add_mem_slitPlane_of_sub_one hw
    have he := ((((hasDerivAt_id w).sub_const 1).clog hw).add
      (((hasDerivAt_id w).add_const 1).clog hp)).const_mul (μ/2)
    have hE := he.cexp.const_mul ((Real.sqrt π:ℂ)/2^(ν+1))
    have hP := (hasDerivAt_id w).cpow_const (c:= -r) (mem_slitPlane_of_sub_one hw)
    have hd : HasDerivAt g _ w := (hE.mul hP).congr_of_eventuallyEq (Eventually.of_forall fun t=>rfl)
    refine hd.congr_deriv ?_
    simp only [g,q,id_eq]
    rw [cpow_sub (-r) 1 (hne w hw).1,cpow_one]
    generalize exp (μ/2*(log (w-1)+log (w+1)))=E
    field_simp [(hne w hw).1,(hne w hw).2.1,(hne w hw).2.2.1,(hne w hw).2.2.2]
    ring
  have hu (w : ℂ) (hw : w-1∈slitPlane) : HasDerivAt u (v w) w := by
    convert! (hasDerivAt_pow 2 w).inv (pow_ne_zero 2 (hne w hw).1) using 1
    · ext t; simp [u]
    · simp only [v]
      field_simp [(hne w hw).1]
      ring
  have hF (w : ℂ) (hw : w-1∈slitPlane) : AnalyticAt ℂ F (u w) :=
    analyticAt_regularizedGaussHG a b c (recip_sq_mem_cutPlane hw)
  have hf : olverQ ν μ=fun w => g w*F (u w) := by
    funext w
    simp only [olverQ,g,F,u,a,b,c,r,legendreBranchPower,cpow_neg]
    ring
  have hfirst (w : ℂ) (hw : w-1∈slitPlane) :
      deriv (olverQ ν μ) w=g w*(q w*F (u w)+v w*deriv F (u w)) := by
    rw [hf]
    have hd := (hg w hw).mul ((hF w hw).differentiableAt.hasDerivAt.comp w (hu w hw))
    have hd' : HasDerivAt (fun t=>g t*F (u t)) _ w :=
      hd.congr_of_eventuallyEq (Eventually.of_forall fun t=>rfl)
    rw [hd'.deriv]
    simp only [Function.comp_apply]
    ring
  have heq : deriv (olverQ ν μ)=ᶠ[𝓝 z] fun w=>g w*(q w*F (u w)+v w*deriv F (u w)) :=
    Filter.eventually_of_mem (isOpen_sub_one_mem_slitPlane.mem_nhds hz) hfirst
  have hq : HasDerivAt q (-μ*(z^2+1)/(z^2-1)^2+r/z^2) z := by
    have hd := (((hasDerivAt_id z).const_mul μ).div
      (((hasDerivAt_id z).pow 2).sub_const 1) (hne z hz).2.2.2).sub
      ((hasDerivAt_const z r).div (hasDerivAt_id z) (hne z hz).1)
    convert! hd using 1
    simp only [id_eq,mul_one,Pi.pow_apply]
    field_simp
    ring
  have hv : HasDerivAt v (6/z^4) z := by
    convert! (hasDerivAt_const z (-2:ℂ)).div ((hasDerivAt_id z).pow 3) (pow_ne_zero 3 (hne z hz).1) using 1
    simp only [id_eq,Pi.pow_apply]
    field_simp [(hne z hz).1]
    ring
  have hsecond := (hg z hz).mul
    ((hq.mul ((hF z hz).differentiableAt.hasDerivAt.comp z (hu z hz))).add
      (hv.mul ((hF z hz).deriv.differentiableAt.hasDerivAt.comp z (hu z hz))))
  have hsecond' : HasDerivAt (fun w=>g w*(q w*F (u w)+v w*deriv F (u w))) _ z :=
    hsecond.congr_of_eventuallyEq (Eventually.of_forall fun w=>rfl)
  rw [iteratedDeriv_succ,iteratedDeriv_one,heq.deriv_eq,hsecond'.deriv,hfirst z hz,hf]
  have hode : u z*(1-u z)*deriv (deriv F) (u z)+
      (c-(a+b+1)*u z)*deriv F (u z)-a*b*F (u z)=0 := by
    dsimp only [F]
    rw [← show iteratedDeriv 2 (regularizedGaussHG a b c)=deriv (deriv (regularizedGaussHG a b c)) by
      rw [iteratedDeriv_succ,iteratedDeriv_one],iteratedDeriv_regularizedGaussHG a b c 2 (recip_sq_mem_cutPlane hz),
      deriv_regularizedGaussHG a b c (recip_sq_mem_cutPlane hz)]
    exact regularizedGaussHG_ode a b c (recip_sq_mem_cutPlane hz)
  simp only [Function.comp_apply,Pi.mul_apply,Pi.add_apply]
  generalize g z=G at *
  generalize F (u z)=F0 at *
  generalize deriv F (u z)=F1 at *
  generalize deriv (deriv F) (u z)=F2 at *
  simp only [q,u,v] at hode ⊢
  have hz0 := (hne z hz).1
  have hz1 := (hne z hz).2.2.2
  have hz2 : 1-z^2≠0 := by intro h; apply hz1; linear_combination -h
  simp only [a,b,c,r] at hode ⊢
  field_simp [hz0,hz1,hz2] at hode ⊢
  linear_combination (G*(z^2-1)^3)*hode

/-- For real `ν, μ` and real `x > 1`, `𝑸^μ_ν(x)` is real. -/
theorem olverQ_real (ν μ : ℝ) {x : ℝ} (hx : 1 < x) :
    (olverQ ν μ x).im=0 := by
  have hx0 : (0:ℝ) < x := by linarith
  have hz : ‖1/(x:ℂ)^2‖ < 1 := by
    rw [norm_div, norm_one, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    rw [div_lt_one (by positivity)]; nlinarith
  have hl1 : log ((x:ℂ)-1) = (Real.log (x-1):ℂ) := by
    rw [show (x:ℂ)-1 = ((x-1:ℝ):ℂ) by push_cast; ring, ofReal_log (by linarith)]
  have hl2 : log ((x:ℂ)+1) = (Real.log (x+1):ℂ) := by
    rw [show (x:ℂ)+1 = ((x+1:ℝ):ℂ) by push_cast; ring, ofReal_log (by linarith)]
  rw [← conj_eq_iff_im]
  unfold olverQ legendreBranchPower
  rw [hl1, hl2, map_mul, map_div₀, map_mul, map_mul, regularizedGaussHG_conj hz, ← exp_conj,
    conj_two_cpow, conj_ofReal_cpow hx0]
  simp [map_div₀, map_ofNat]

/-- First two jets of the quadratic Gauss pullback with its Ferrers gauge.
The complex jets also give real derivatives on the Ferrers interval. -/
theorem quadratic_gauss_gauge_jets (a b c μ : ℂ) {z : ℂ}
    (hz : 1-z^2∈slitPlane) :
    let F := regularizedGaussHG a b c
    let g : ℂ→ℂ := fun w=>(1-w^2)^(-μ/2)
    let q : ℂ→ℂ := fun w=>μ*w/(1-w^2)
    let d : ℂ→ℂ := fun w=>g w*(q w*F (w^2)+2*w*deriv F (w^2))
    HasDerivAt (fun w=>g w*F (w^2)) (d z) z ∧
    HasDerivAt d (g z*((q z^2+μ*(1+z^2)/(1-z^2)^2)*F (z^2)+
      (4*z*q z+2)*deriv F (z^2)+4*z^2*deriv (deriv F) (z^2))) z := by
  dsimp only
  let F := regularizedGaussHG a b c
  let g : ℂ→ℂ := fun w=>(1-w^2)^(-μ/2)
  let q : ℂ→ℂ := fun w=>μ*w/(1-w^2)
  have hne : 1-z^2≠0 := slitPlane_ne_zero hz
  have hg : HasDerivAt g (g z*q z) z := by
    have hd := (hasStrictDerivAt_cpow_const (c:= -μ/2) hz).hasDerivAt.comp z
      ((hasDerivAt_pow 2 z).const_sub 1)
    refine hd.congr_deriv ?_
    simp only [g,q]
    rw [cpow_sub (-μ/2) 1 hne,cpow_one]
    field_simp
    ring
  have hq : HasDerivAt q (μ*(1+z^2)/(1-z^2)^2) z := by
    have hd := ((hasDerivAt_id z).const_mul μ).div ((hasDerivAt_pow 2 z).const_sub 1) hne
    convert! hd using 1
    simp only [id_eq]
    field_simp
    ring
  have hF : AnalyticAt ℂ F (z^2) := analyticAt_regularizedGaussHG a b c hz
  have hC := hF.differentiableAt.hasDerivAt.comp z (h:=fun w : ℂ=>w^2) (hasDerivAt_pow 2 z)
  have hC' := hF.deriv.differentiableAt.hasDerivAt.comp z (h:=fun w : ℂ=>w^2) (hasDerivAt_pow 2 z)
  constructor
  · have hd := hg.mul hC
    refine (hd.congr_of_eventuallyEq (Eventually.of_forall fun w=>rfl)).congr_deriv ?_
    simp only [F,g,q,Function.comp_apply,Nat.cast_ofNat]
    ring
  · have hd := hg.mul ((hq.mul hC).add
      (((hasDerivAt_id z).const_mul 2).mul hC'))
    refine (hd.congr_of_eventuallyEq (Eventually.of_forall fun w=>rfl)).congr_deriv ?_
    simp only [F,g,q,Function.comp_apply,Pi.add_apply,Pi.mul_apply,id_eq,Nat.cast_ofNat]
    ring

/-- DLMF 14.2.2: when `ν+μ ∉ {-1,-2,…}` and for `-1 < x < 1`, `w = 𝖰^μ_ν(x)` satisfies `(1-x²) w'' -
2x w' + (ν(ν+1) - μ²/(1-x²)) w = 0`. -/
@[dlmf 14.2.E2]
theorem ferrersQ_ode {ν μ : ℂ} {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)*iteratedDeriv 2 (ferrersQ ν μ) x-2*x*deriv (ferrersQ ν μ) x+(ν*(ν+1)-μ^2/(1-x^2:ℂ))*ferrersQ ν μ x=0 := by
  let a : ℂ := -(ν+μ)/2
  let b : ℂ := (ν-μ+1)/2
  let A : ℂ := (1-ν-μ)/2
  let B : ℂ := (ν-μ+2)/2
  let F := regularizedGaussHG a b (1/2)
  let G := regularizedGaussHG A B (3/2)
  let g : ℂ→ℂ := fun z=>(1-z^2)^(-μ/2)
  let q : ℂ→ℂ := fun z=>μ*z/(1-z^2)
  let E : ℝ→ℂ := fun y=>g y*F ((y:ℂ)^2)
  let O : ℝ→ℂ := fun y=>g y*G ((y:ℂ)^2)
  let E1 : ℝ→ℂ := fun y=>g y*(q y*F ((y:ℂ)^2)+2*y*deriv F ((y:ℂ)^2))
  let O1 : ℝ→ℂ := fun y=>g y*(q y*G ((y:ℂ)^2)+2*y*deriv G ((y:ℂ)^2))
  let k : ℂ := -π/2*sin ((ν+μ)*π/2)*2^μ*Gamma ((ν+μ+1)/2)/Gamma ((ν-μ+2)/2)
  let l : ℂ := π/2*cos ((ν+μ)*π/2)*2^μ*Gamma ((ν+μ+2)/2)/Gamma ((ν-μ+1)/2)
  have hs (y : ℝ) (hy : y∈Ioo (-1:ℝ) 1) : 1-(y:ℂ)^2∈slitPlane := by
    left
    simp only [sub_re,one_re,pow_two,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
    nlinarith [hy.1,hy.2]
  have hE (y : ℝ) (hy : y∈Ioo (-1:ℝ) 1) : HasDerivAt E (E1 y) y :=
    (quadratic_gauss_gauge_jets a b (1/2) μ (hs y hy)).1.comp_ofReal
  have hO (y : ℝ) (hy : y∈Ioo (-1:ℝ) 1) : HasDerivAt O (O1 y) y :=
    (quadratic_gauss_gauge_jets A B (3/2) μ (hs y hy)).1.comp_ofReal
  have hf : ferrersQ ν μ=fun y : ℝ=>k*E y+l*y*O y := by
    funext y
    simp only [ferrersQ,ferrersW1,ferrersW2,k,l,E,O,g,F,G,a,b,A,B]
    ring
  have hd (y : ℝ) (hy : y∈Ioo (-1:ℝ) 1) :
      HasDerivAt (ferrersQ ν μ) (k*E1 y+l*(O y+y*O1 y)) y := by
    rw [hf]
    have hh := ((hE y hy).const_mul k).add
      (((hasDerivAt_id y).ofReal_comp.mul (hO y hy)).const_mul l)
    have hh' : HasDerivAt (fun t : ℝ=>k*E t+l*t*O t) _ y :=
      hh.congr_of_eventuallyEq (Eventually.of_forall fun t=>by
        simp only [Pi.add_apply,Pi.mul_apply,id_eq]
        ring)
    refine hh'.congr_deriv ?_
    simp only [id_eq,ofReal_one]
    ring
  have heq : deriv (ferrersQ ν μ)=ᶠ[𝓝 x] fun y=>k*E1 y+l*(O y+y*O1 y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact (hd y hy).deriv
  have hE2 := (quadratic_gauss_gauge_jets a b (1/2) μ (hs x hx)).2.comp_ofReal
  have hO2 := (quadratic_gauss_gauge_jets A B (3/2) μ (hs x hx)).2.comp_ofReal
  have hsecond := (hE2.const_mul k).add
    (((hO x hx).add ((hasDerivAt_id x).ofReal_comp.mul hO2)).const_mul l)
  have hsecond' : HasDerivAt (fun y : ℝ=>k*E1 y+l*(O y+y*O1 y)) _ x :=
    hsecond.congr_of_eventuallyEq (Eventually.of_forall fun y=>by
      simp only [E1,O1,F,G,g,q,Pi.add_apply,Pi.mul_apply,id_eq])
  have hode (α β γ : ℂ) :
      (x:ℂ)^2*(1-(x:ℂ)^2)*deriv (deriv (regularizedGaussHG α β γ)) ((x:ℂ)^2)+
      (γ-(α+β+1)*(x:ℂ)^2)*deriv (regularizedGaussHG α β γ) ((x:ℂ)^2)-
      α*β*regularizedGaussHG α β γ ((x:ℂ)^2)=0 := by
    rw [←show iteratedDeriv 2 (regularizedGaussHG α β γ)=deriv (deriv (regularizedGaussHG α β γ)) by
      rw [iteratedDeriv_succ,iteratedDeriv_one],iteratedDeriv_regularizedGaussHG α β γ 2 (hs x hx),
      deriv_regularizedGaussHG α β γ (hs x hx)]
    exact regularizedGaussHG_ode α β γ (hs x hx)
  have he := hode a b (1/2)
  have ho := hode A B (3/2)
  rw [iteratedDeriv_succ,iteratedDeriv_one,heq.deriv_eq,hsecond'.deriv,(hd x hx).deriv,hf]
  simp only [id_eq,ofReal_one]
  dsimp only [E1,O1,E,O,g,q,F,G,a,b,A,B] at he ho ⊢
  have hne : 1-(x:ℂ)^2≠0 := slitPlane_ne_zero (hs x hx)
  linear_combination (norm := (field_simp [hne]; ring))
    (4*k*(1-(x:ℂ)^2)^(-μ/2))*he+(4*l*x*(1-(x:ℂ)^2)^(-μ/2))*ho

end DLMF.Legendre
end
