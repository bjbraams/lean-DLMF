/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Ferrers
public import DLMF.Legendre.Integer

/-!
# Quadratic bases for associated Legendre and Ferrers functions

Even and odd quadratic hypergeometric bases give the initial associated Legendre identities.

Source references and common attribution are retained in
`DLMF.Legendre.Associated`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat ComplexConjugate

namespace DLMF.Legendre

/-- The inherited power of z squared minus one, continued from z greater than one. -/
def legendreBranchPower (μ z : ℂ) : ℂ :=
  exp (μ/2*(log (z-1)+log (z+1)))

/-- DLMF 14.3.6: the associated Legendre function of the first kind, `P^μ_ν(z) =
((z+1)/(z-1))^{μ/2} 𝐅(ν+1, -ν; 1-μ; (1-z)/2)` with principal branches and the regularized
hypergeometric function `𝐅`. -/
@[dlmf 14.3.E6]
def associatedP (ν μ z : ℂ) : ℂ :=
  exp (μ/2*(log (z+1)-log (z-1)))*regularizedGaussHG (ν+1) (-ν) (1-μ) ((1-z)/2)

/-- Olver Q is regularized before multiplying by Gamma, so exceptional parameters are retained. -/
@[dlmf 14.3.E10]
def olverQ (ν μ z : ℂ) : ℂ :=
  Real.sqrt π*legendreBranchPower μ z/(2^(ν+1)*z^(ν+μ+1))*regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/z^2)

/-- Classical associated Q, defined mathematically when degree plus order is not a negative integer. -/
@[dlmf 14.3.E7]
def associatedQ (ν μ z : ℂ) : ℂ :=
  exp (μ*π*I)*Gamma (ν+μ+1)*olverQ ν μ z

/-- The parameter condition `ν + μ ∉ {-1, -2, -3, …}` under which the classical `Q^μ_ν` and Ferrers
`𝖰^μ_ν` are defined. -/
def LegendreQRegular (ν μ : ℂ) : Prop :=
  ∀ n : ℕ, ν+μ ≠ -(n+1)

/-- DLMF 14.3.13: the even Ferrers auxiliary function `w₁(ν, μ, x) = 2^μ Γ((ν+μ+1)/2)/Γ((ν-μ+2)/2)
(1-x²)^{-μ/2} 𝐅(-(ν+μ)/2, (ν-μ+1)/2; 1/2; x²)`. -/
@[dlmf 14.3.E13]
def ferrersW1 (ν μ : ℂ) (x : ℝ) : ℂ :=
  2^μ*Gamma ((ν+μ+1)/2)/Gamma ((ν-μ+2)/2)*(1-x^2:ℂ)^(-μ/2)*regularizedGaussHG (-(ν+μ)/2) ((ν-μ+1)/2) (1/2) (x^2)

/-- DLMF 14.3.14: the odd Ferrers auxiliary function `w₂(ν, μ, x) = 2^μ Γ((ν+μ+2)/2)/Γ((ν-μ+1)/2) x
(1-x²)^{-μ/2} 𝐅((1-ν-μ)/2, (ν-μ+2)/2; 3/2; x²)`. -/
@[dlmf 14.3.E14]
def ferrersW2 (ν μ : ℂ) (x : ℝ) : ℂ :=
  2^μ*Gamma ((ν+μ+2)/2)/Gamma ((ν-μ+1)/2)*x*(1-x^2:ℂ)^(-μ/2)*regularizedGaussHG ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) (x^2)

/-- This representation supplies integer-order limiting values without division by sin of the order. -/
@[dlmf 14.3.E12]
def ferrersQ (ν μ : ℂ) (x : ℝ) : ℂ :=
  -π/2*sin ((ν+μ)*π/2)*ferrersW1 ν μ x+π/2*cos ((ν+μ)*π/2)*ferrersW2 ν μ x

/-- `Γ(1/2) = √π` in the complex Gamma function. -/
theorem legendre_Gamma_one_half : Gamma (1 / 2 : ℂ) = (Real.sqrt π : ℂ) := by
  rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
  norm_num

/-- `𝐅(a,b;c;0) = 1/Γ(c)` for regular `c`. -/
theorem regularizedGaussHGFun_zero_of_regular {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    regularizedGaussHGFun a b c 0 = 1/Gamma c := by
  rw [regularizedGaussHGFun_eq_div_Gamma hc, ordinaryHypergeometric_zero]

/-- `𝐅(a,b;c;0) = 1/Γ(c)` for regular `c`, on the cut plane. -/
theorem regularizedGaussHG_zero_of_regular {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    regularizedGaussHG a b c 0 = 1/Gamma c := by
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by simp),
    regularizedGaussHGFun_zero_of_regular hc]

/-- `1/2` is not a pole of `Γ`. -/
theorem half_ne_neg_nat : ∀ k : ℕ, (1/2:ℂ) ≠ -(k:ℂ) := fun k h => by
  have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]

/-- `Γ(3/2) = √π/2`. -/
theorem legendre_Gamma_three_halves : Gamma (3 / 2 : ℂ) = (Real.sqrt π : ℂ)/2 := by
  rw [show (3/2:ℂ) = 1/2+1 by norm_num, Gamma_add_one _ (by norm_num), legendre_Gamma_one_half]
  ring

/-- Positive real bases align the quadratic Ferrers gauge with the original ratio gauge. -/
theorem ferrers_quadratic_gauge (μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (((1+x)/(1-x):ℝ):ℂ)^(μ/2)*((1+(x:ℂ))/2)^(-μ)=
      (2:ℂ)^μ*(1-(x:ℂ)^2)^(-μ/2) := by
  have hp : 0<1+x := by linarith [hx.1]
  have hm : 0<1-x := by linarith [hx.2]
  have hs : 0<1-x^2 := by nlinarith [hx.1,hx.2]
  have hr : 0<(1+x)/(1-x) := div_pos hp hm
  have hb : 0<(1+x)/2 := by positivity
  have hl (y : ℝ) (hy : 0<y) : log (y:ℂ)=(Real.log y:ℂ) := (ofReal_log hy.le).symm
  have hlr : log (((1+x)/(1-x):ℝ):ℂ)=(Real.log (1+x):ℂ)-(Real.log (1-x):ℂ) := by
    rw [hl _ hr,Real.log_div hp.ne' hm.ne',ofReal_sub]
  have hlb : log ((1+(x:ℂ))/2)=(Real.log (1+x):ℂ)-(Real.log 2:ℂ) := by
    rw [show (1+(x:ℂ))/2=(((1+x)/2:ℝ):ℂ) by push_cast; ring,
      hl _ hb,Real.log_div hp.ne' (by norm_num),ofReal_sub]
  have hls : log (1-(x:ℂ)^2)=(Real.log (1+x):ℂ)+(Real.log (1-x):ℂ) := by
    rw [show 1-(x:ℂ)^2=((1-x^2:ℝ):ℂ) by push_cast; ring,hl _ hs,
      show 1-x^2=(1+x)*(1-x) by ring,Real.log_mul hp.ne' hm.ne',ofReal_add]
  have hr0 : (((1+x)/(1-x):ℝ):ℂ)≠0 := ofReal_ne_zero.mpr hr.ne'
  have hb0 : (1+(x:ℂ))/2≠0 := by exact_mod_cast hb.ne'
  have hs0 : 1-(x:ℂ)^2≠0 := by exact_mod_cast hs.ne'
  have hl2 : log (2:ℂ)=(Real.log 2:ℂ) := by simp
  rw [cpow_def_of_ne_zero hr0,cpow_def_of_ne_zero hb0,cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    cpow_def_of_ne_zero hs0,hlr,hlb,hls,hl2,←exp_add,←exp_add]
  congr 1
  ring

/-- Reflection after cancelling only the regular Gamma factor. -/
theorem ferrers_Gamma_reflection {s : ℂ} (hs : ∀ n : ℕ, s≠-n) :
    (π:ℂ)/Gamma (1-s)=Gamma s*sin (π*s) := by
  have hπ : (π:ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hR : (π:ℂ)*((Gamma s)⁻¹*(Gamma (1-s))⁻¹)=sin (π*s) := by
    rw [←mul_inv,Gamma_mul_Gamma_one_sub,inv_div]
    field_simp
  rw [←hR]
  field_simp [Gamma_ne_zero hs]

/-- DLMF 14.3.11: for `-1 < x < 1` and `ν+μ ∉ {-1,-2,…}`, `𝖯^μ_ν(x) = cos((ν+μ)π/2) w₁(ν,μ,x) +
sin((ν+μ)π/2) w₂(ν,μ,x)`. -/
@[dlmf 14.3.E11]
theorem ferrersP_w1_w2 {ν μ : ℂ} (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν μ x=cos ((ν+μ)*π/2)*ferrersW1 ν μ x+sin ((ν+μ)*π/2)*ferrersW2 ν μ x := by
  have hz : ‖((1-(x:ℂ))/2)‖<1 := by
    rw [show (1-(x:ℂ))/2=(((1-x)/2:ℝ):ℂ) by push_cast; ring,
      Complex.norm_real,Real.norm_eq_abs,abs_lt]
    constructor <;> linarith [hx.1,hx.2]
  have hw : ‖(x:ℂ)^2‖<1 := by
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    nlinarith [hx.1,hx.2]
  have hq := regularized_quadratic_connection_complementary (ν+1) (1-μ) hz
    (by rw [show 1-2*((1-(x:ℂ))/2)=(x:ℂ) by ring]; exact hw)
  rw [show 1-(ν+1) = -ν by ring,
    show 1-2*((1-(x:ℂ))/2)=(x:ℂ) by ring,
    show 1-(1-(x:ℂ))/2=(1+(x:ℂ))/2 by ring,
    show 1-μ-1 = -μ by ring,
    show (1-μ-(ν+1)+1)/2=(1-ν-μ)/2 by ring,
    show (1-μ+(ν+1))/2=(ν-μ+2)/2 by ring,
    show (1-μ-(ν+1))/2=-(ν+μ)/2 by ring,
    show (1-μ+(ν+1)-1)/2=(ν-μ+1)/2 by ring] at hq
  simp only [←regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz,
    ←regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw] at hq
  have hGe : ∀ n : ℕ, (ν+μ+1)/2≠-n := by
    intro n he
    exact h (2*n) (by push_cast; linear_combination 2*he)
  have hGo : ∀ n : ℕ, (ν+μ+2)/2≠-n := by
    intro n he
    exact h (2*n+1) (by push_cast; linear_combination 2*he)
  have hre := ferrers_Gamma_reflection hGe
  have hro := ferrers_Gamma_reflection hGo
  rw [show 1-(ν+μ+1)/2=(1-ν-μ)/2 by ring,
    show (π:ℂ)*((ν+μ+1)/2)=(ν+μ)*π/2+π/2 by ring, sin_add_pi_div_two] at hre
  rw [show 1-(ν+μ+2)/2=-(ν+μ)/2 by ring,
    show (π:ℂ)*((ν+μ+2)/2)=(ν+μ)*π/2+π by ring,sin_add_pi] at hro
  have hhalf : Gamma (1/2:ℂ)^2=(π:ℂ) := by
    have hh := Gamma_mul_Gamma_one_sub (1/2:ℂ)
    rw [show (1:ℂ)-1/2=1/2 by ring,show (π:ℂ)*(1/2)=π/2 by ring,
      sin_pi_div_two,div_one] at hh
    simpa only [pow_two] using hh
  have hm : Gamma (-1/2:ℂ)= -2*Gamma (1/2:ℂ) := by
    have hh := Gamma_add_one (-1/2:ℂ) (by norm_num)
    rw [show (-1/2:ℂ)+1=1/2 by ring] at hh
    linear_combination 2*hh
  have ht : Gamma (3/2:ℂ)=Gamma (1/2:ℂ)/2 := by
    rw [show (3/2:ℂ)=1/2+1 by ring,Gamma_add_one _ (by norm_num)]
    ring
  have hodd : Gamma (-1/2:ℂ)*Gamma (3/2:ℂ)= -(π:ℂ) := by
    rw [hm,ht]
    linear_combination -hhalf
  rw [hhalf,hodd] at hq
  unfold ferrersP ferrersW1 ferrersW2
  rw [hq]
  calc
    _ = ((((1+x)/(1-x):ℝ):ℂ)^(μ/2)*((1+(x:ℂ))/2)^(-μ))*
        ((π/Gamma ((1-ν-μ)/2))/Gamma ((ν-μ+2)/2)*
          regularizedGaussHG (-(ν+μ)/2) ((ν-μ+1)/2) (1/2) (x^2)+
        x*(-(π/Gamma (-(ν+μ)/2)))/Gamma ((ν-μ+1)/2)*
          regularizedGaussHG ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) (x^2)) := by ring
    _ = _ := by rw [ferrers_quadratic_gauge μ hx,hre,hro]; ring

/-! ### The even/odd quadratic basis of Ferrers solutions

All Ferrers functions of degree `ν` and orders `±μ` are combinations of the two quadratic
solutions `ferrersEven` and `ferrersOdd`. Coefficients use reciprocal Gamma values, so no
regularity hypothesis is needed for `𝖯`. -/

/-- The even quadratic Ferrers solution `(1-x²)^{-μ/2} 𝐅(-(ν+μ)/2, (ν-μ+1)/2; 1/2; x²)`. -/
def ferrersEven (ν μ : ℂ) (x : ℝ) : ℂ :=
  (1-(x:ℂ)^2)^(-μ/2)*regularizedGaussHG (-(ν+μ)/2) ((ν-μ+1)/2) (1/2) ((x:ℂ)^2)

/-- The odd quadratic Ferrers solution `x (1-x²)^{-μ/2} 𝐅((1-ν-μ)/2, (ν-μ+2)/2; 3/2; x²)`. -/
def ferrersOdd (ν μ : ℂ) (x : ℝ) : ℂ :=
  (x:ℂ)*((1-(x:ℂ)^2)^(-μ/2)*regularizedGaussHG ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) ((x:ℂ)^2))

/-- `1-x²` lies in the slit plane for `x ∈ (-1,1)`. -/
theorem ferrers_one_sub_sq_mem_slitPlane {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) : 1-(x:ℂ)^2 ∈ slitPlane := by
  left
  simp only [sub_re,one_re,pow_two,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
  nlinarith [hx.1,hx.2]

/-- `x²` lies in the cut plane for `x ∈ (-1,1)`. -/
theorem ferrers_sq_mem_cutPlane {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) : (x:ℂ)^2 ∈ cutPlane :=
  ferrers_one_sub_sq_mem_slitPlane hx

/-- `(-1,1)` is symmetric. -/
theorem ferrers_neg_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) : -x ∈ Ioo (-1:ℝ) 1 :=
  ⟨by linarith [hx.2], by linarith [hx.1]⟩

/-- Euler's transformation: the even solution is invariant under `μ ↦ -μ`. -/
theorem ferrersEven_neg_order (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersEven ν (-μ) x = ferrersEven ν μ x := by
  have hw := ferrers_sq_mem_cutPlane hx
  have hne := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  unfold ferrersEven
  rw [regularizedGaussHG_euler _ _ _ hw, regularizedGaussHG_symm _ _ _ hw, ← mul_assoc,
    ← cpow_add _ _ hne]
  congr 2 <;> ring

/-- Euler's transformation: the odd solution is invariant under `μ ↦ -μ`. -/
theorem ferrersOdd_neg_order (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersOdd ν (-μ) x = ferrersOdd ν μ x := by
  have hw := ferrers_sq_mem_cutPlane hx
  have hne := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  unfold ferrersOdd
  rw [regularizedGaussHG_euler _ _ _ hw, regularizedGaussHG_symm _ _ _ hw]
  have e : -μ/2 = -(-μ)/2 + (3/2 - (1-ν-(-μ))/2 - (ν-(-μ)+2)/2) := by ring
  rw [e, cpow_add _ _ hne]
  ring_nf

/-- The even solution is invariant under `ν ↦ -ν-1`. -/
theorem ferrersEven_neg_degree (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersEven (-ν-1) μ x = ferrersEven ν μ x := by
  unfold ferrersEven
  rw [regularizedGaussHG_symm _ _ _ (ferrers_sq_mem_cutPlane hx)]
  congr 3 <;> ring

/-- The odd solution is invariant under `ν ↦ -ν-1`. -/
theorem ferrersOdd_neg_degree (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersOdd (-ν-1) μ x = ferrersOdd ν μ x := by
  unfold ferrersOdd
  rw [regularizedGaussHG_symm _ _ _ (ferrers_sq_mem_cutPlane hx)]
  congr 4 <;> ring

/-- The even solution is even in `x`. -/
theorem ferrersEven_neg (ν μ : ℂ) (x : ℝ) : ferrersEven ν μ (-x) = ferrersEven ν μ x := by
  simp [ferrersEven]

/-- The odd solution is odd in `x`. -/
theorem ferrersOdd_neg (ν μ : ℂ) (x : ℝ) : ferrersOdd ν μ (-x) = -ferrersOdd ν μ x := by
  simp [ferrersOdd]

/-- The reflection formula for reciprocal Gamma values, valid at every `s`. -/
theorem legendre_recip_Gamma_reflection (s : ℂ) : π*((Gamma s)⁻¹*(Gamma (1-s))⁻¹) = sin (π*s) := by
  rw [← mul_inv, Gamma_mul_Gamma_one_sub, inv_div]
  by_cases h : sin (π*s) = 0
  · simp [h]
  · field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- Reflection for the even Ferrers coefficients: `π/(Γ((1-t)/2)Γ((t+1)/2)) = cos(tπ/2)`. -/
theorem legendre_reflection_even (t : ℂ) :
    π*((Gamma ((1-t)/2))⁻¹*(Gamma ((t+1)/2))⁻¹) = cos (t*π/2) := by
  have h := legendre_recip_Gamma_reflection ((t+1)/2)
  rw [show 1-(t+1)/2 = (1-t)/2 by ring, show (π:ℂ)*((t+1)/2) = t*π/2+π/2 by ring,
    sin_add_pi_div_two] at h
  rw [← h]; ring

/-- Reflection for the odd Ferrers coefficients: `π/(Γ(-t/2)Γ((t+2)/2)) = -sin(tπ/2)`. -/
theorem legendre_reflection_odd (t : ℂ) :
    π*((Gamma (-t/2))⁻¹*(Gamma ((t+2)/2))⁻¹) = -sin (t*π/2) := by
  have h := legendre_recip_Gamma_reflection ((t+2)/2)
  rw [show 1-(t+2)/2 = -t/2 by ring, show (π:ℂ)*((t+2)/2) = t*π/2+π by ring,
    sin_add_pi] at h
  rw [← h]; ring

/-- Legendre duplication `Γ(t+1) = Γ((t+1)/2)Γ((t+2)/2)2^t/√π`, valid for all `t`. -/
theorem legendre_duplication (t : ℂ) :
    Gamma (t+1) = Gamma ((t+1)/2)*Gamma ((t+2)/2)*2^t/(Real.sqrt π:ℂ) := by
  have h := Gamma_mul_Gamma_add_half ((t+1)/2)
  rw [show (t+1)/2+1/2 = (t+2)/2 by ring, show 2*((t+1)/2) = t+1 by ring,
    show 1-(t+1) = -t by ring] at h
  have hs : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h2 : (2:ℂ)^t*2^(-t) = 1 := by rw [← cpow_add _ _ two_ne_zero]; simp
  rw [h]; field_simp; linear_combination (-Gamma (t+1))*h2

/-- Reciprocal Legendre duplication, valid for all `t`. -/
theorem legendre_recip_duplication (t : ℂ) :
    (Gamma (t+1))⁻¹ = (Gamma ((t+1)/2))⁻¹*(Gamma ((t+2)/2))⁻¹*2^(-t)*(Real.sqrt π:ℂ) := by
  rw [legendre_duplication t, cpow_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]

/-- `Γ(ν+μ+1)/Γ(ν-μ+1)` through half-argument Gamma values; totalized at poles. -/
theorem legendre_Gamma_ratio (ν μ : ℂ) :
    Gamma (ν+μ+1)/Gamma (ν-μ+1) = Gamma ((ν+μ+1)/2)*Gamma ((ν+μ+2)/2)*
      (Gamma ((ν-μ+1)/2))⁻¹*(Gamma ((ν-μ+2)/2))⁻¹*((2:ℂ)^μ)^2 := by
  have hs : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h2 : (2:ℂ)^(ν+μ)*2^(-(ν-μ)) = ((2:ℂ)^μ)^2 := by
    rw [← cpow_add _ _ two_ne_zero, sq, ← cpow_add _ _ two_ne_zero]; ring_nf
  rw [div_eq_mul_inv, legendre_duplication (ν+μ), legendre_recip_duplication (ν-μ), ← h2]
  ring_nf
  field_simp

/-- Duplication for `Γ(ν+μ+1)` with separated powers of two. -/
theorem legendre_Gamma_plus (ν μ : ℂ) :
    Gamma (ν+μ+1) = Gamma ((ν+μ+1)/2)*Gamma ((ν+μ+2)/2)*(2^ν*2^μ)/(Real.sqrt π:ℂ) := by
  rw [legendre_duplication, cpow_add _ _ two_ne_zero]

/-- Duplication for `Γ(ν-μ+1)` with separated powers of two. -/
theorem legendre_Gamma_minus (ν μ : ℂ) :
    Gamma (ν-μ+1) = Gamma ((ν-μ+1)/2)*Gamma ((ν-μ+2)/2)*(2^ν*((2:ℂ)^μ)⁻¹)/(Real.sqrt π:ℂ) := by
  rw [legendre_duplication, cpow_sub _ _ two_ne_zero, div_eq_mul_inv (2^ν)]

/-- Reciprocal duplication for `Γ(μ-ν)`. -/
theorem legendre_recip_Gamma_sub (ν μ : ℂ) :
    (Gamma (μ-ν))⁻¹ = (Gamma ((μ-ν)/2))⁻¹*(Gamma ((1-ν+μ)/2))⁻¹*(2*2^ν*((2:ℂ)^μ)⁻¹)*(Real.sqrt π:ℂ) := by
  have h := legendre_recip_duplication (μ-ν-1)
  rw [show μ-ν-1+1 = μ-ν by ring,
    show (μ-ν-1+2)/2 = (1-ν+μ)/2 by ring] at h
  rw [h, show -(μ-ν-1) = 1+ν-μ by ring, cpow_sub _ _ two_ne_zero, cpow_add _ _ two_ne_zero, cpow_one]
  ring

/-- Regularity of `ν+μ` makes both half-argument Gamma factors finite. -/
theorem legendre_Gamma_half_ne_zero {ν μ : ℂ} (h : LegendreQRegular ν μ) :
    Gamma ((ν+μ+1)/2) ≠ 0 ∧ Gamma ((ν+μ+2)/2) ≠ 0 :=
  ⟨Gamma_ne_zero fun n he => h (2*n) (by push_cast; linear_combination 2*he),
    Gamma_ne_zero fun n he => h (2*n+1) (by push_cast; linear_combination 2*he)⟩

/-- Regularity of `ν-μ` makes both half-argument Gamma factors finite. -/
theorem legendre_Gamma_half_ne_zero_neg {ν μ : ℂ} (h : LegendreQRegular ν (-μ)) :
    Gamma ((ν-μ+1)/2) ≠ 0 ∧ Gamma ((ν-μ+2)/2) ≠ 0 := by
  simpa only [← sub_eq_add_neg] using legendre_Gamma_half_ne_zero h

/-- Shared reflection data for the even and odd Ferrers coefficients. -/
theorem legendre_reflections (ν μ : ℂ) :
    π*((Gamma ((1-ν-μ)/2))⁻¹*(Gamma ((ν+μ+1)/2))⁻¹) = cos ((ν+μ)*π/2) ∧
    π*((Gamma (-(ν+μ)/2))⁻¹*(Gamma ((ν+μ+2)/2))⁻¹) = -sin ((ν+μ)*π/2) ∧
    π*((Gamma ((1-ν+μ)/2))⁻¹*(Gamma ((ν-μ+1)/2))⁻¹) = cos ((ν-μ)*π/2) ∧
    π*((Gamma ((μ-ν)/2))⁻¹*(Gamma ((ν-μ+2)/2))⁻¹) = -sin ((ν-μ)*π/2) := by
  have e1 := legendre_reflection_even (ν+μ)
  have o1 := legendre_reflection_odd (ν+μ)
  have e2 := legendre_reflection_even (ν-μ)
  have o2 := legendre_reflection_odd (ν-μ)
  rw [show (1-(ν+μ))/2 = (1-ν-μ)/2 by ring] at e1
  rw [show (1-(ν-μ))/2 = (1-ν+μ)/2 by ring] at e2
  rw [show -(ν-μ)/2 = (μ-ν)/2 by ring] at o2
  exact ⟨e1, o1, e2, o2⟩

/-- Under regular `ν+μ`, the reflected reciprocal Gamma values of the order-`μ` coefficients. -/
theorem legendre_reflection_recip {ν μ : ℂ} (h : LegendreQRegular ν μ) :
    (Gamma ((1-ν-μ)/2))⁻¹ = cos ((ν+μ)*π/2)*Gamma ((ν+μ+1)/2)/π ∧
    (Gamma (-(ν+μ)/2))⁻¹ = -sin ((ν+μ)*π/2)*Gamma ((ν+μ+2)/2)/π := by
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero h
  obtain ⟨e1, o1, -, -⟩ := legendre_reflections ν μ
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  constructor
  · rw [← e1]; field_simp
  · rw [← o1]; field_simp

/-- Under regular `ν-μ`, the reflected reciprocal Gamma values of the order-`-μ` coefficients. -/
theorem legendre_reflection_recip_neg {ν μ : ℂ} (h : LegendreQRegular ν (-μ)) :
    (Gamma ((1-ν+μ)/2))⁻¹ = cos ((ν-μ)*π/2)*Gamma ((ν-μ+1)/2)/π ∧
    (Gamma ((μ-ν)/2))⁻¹ = -sin ((ν-μ)*π/2)*Gamma ((ν-μ+2)/2)/π := by
  obtain ⟨hh1, hh2⟩ := legendre_Gamma_half_ne_zero_neg h
  obtain ⟨-, -, e2, o2⟩ := legendre_reflections ν μ
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  constructor
  · rw [← e2]; field_simp
  · rw [← o2]; field_simp

/-- `sin(zπ) = 2 sin(zπ/2) cos(zπ/2)`. -/
theorem legendre_sin_two_mul_half (z : ℂ) : sin (z*π) = 2*sin (z*π/2)*cos (z*π/2) := by
  rw [← sin_two_mul]; ring_nf

/-- `cos(zπ) = 2 cos²(zπ/2) - 1`. -/
theorem legendre_cos_two_mul_half (z : ℂ) : cos (z*π) = 2*cos (z*π/2)^2-1 := by
  rw [← cos_two_mul]; ring_nf

/-- `sin(z-mπ) = (-1)^m sin z` for complex `z`. -/
theorem legendre_sin_sub_nat_mul_pi (z : ℂ) (m : ℕ) : sin (z-m*π) = (-1)^m*sin z := by
  have hs : sin ((m:ℂ)*π) = 0 := by
    rw [show (m:ℂ)*π = ((m*π:ℝ):ℂ) by push_cast; ring, ← ofReal_sin, Real.sin_nat_mul_pi]; simp
  have hc : cos ((m:ℂ)*π) = (-1)^m := by
    rw [show (m:ℂ)*π = ((m*π:ℝ):ℂ) by push_cast; ring, ← ofReal_cos, Real.cos_nat_mul_pi]; push_cast; rfl
  rw [sin_sub, hs, hc]; ring

/-- `cos(z-mπ) = (-1)^m cos z` for complex `z`. -/
theorem legendre_cos_sub_nat_mul_pi (z : ℂ) (m : ℕ) : cos (z-m*π) = (-1)^m*cos z := by
  have hs : sin ((m:ℂ)*π) = 0 := by
    rw [show (m:ℂ)*π = ((m*π:ℝ):ℂ) by push_cast; ring, ← ofReal_sin, Real.sin_nat_mul_pi]; simp
  have hc : cos ((m:ℂ)*π) = (-1)^m := by
    rw [show (m:ℂ)*π = ((m*π:ℝ):ℂ) by push_cast; ring, ← ofReal_cos, Real.cos_nat_mul_pi]; push_cast; rfl
  rw [cos_sub, hs, hc]; ring

/-- `(1/2)^(-μ) = 2^μ`. -/
theorem half_cpow_neg (μ : ℂ) : (1/2:ℂ)^(-μ) = 2^μ := by
  rw [show (1/2:ℂ) = ((2:ℝ):ℂ)⁻¹ by norm_num, inv_cpow_ofReal_nonneg (by norm_num), cpow_neg, inv_inv]
  norm_num

/-- The even quadratic Gauss pullback `(1-w²)^(-μ/2) 𝐅(a,b;c;w²)` is stationary at `0`. -/
theorem hasDerivAt_quadratic_even (a b c μ : ℂ) :
    HasDerivAt (fun w : ℂ => (1-w^2)^(-μ/2) * regularizedGaussHG a b c (w^2)) 0 0 := by
  have h1 : (1:ℂ)-0^2 ∈ slitPlane := by norm_num
  have hg := (hasStrictDerivAt_cpow_const (c := -μ/2) h1).hasDerivAt.comp (0:ℂ)
    ((hasDerivAt_pow 2 (0:ℂ)).const_sub 1)
  have h0 : (0:ℂ)^2 ∈ cutPlane := by rw [zero_pow two_ne_zero]; exact zero_mem_cutPlane
  have hF := (differentiableAt_regularizedGaussHG a b c h0).hasDerivAt.comp (0:ℂ) (h := fun w : ℂ => w^2)
    (hasDerivAt_pow 2 (0:ℂ))
  refine (hg.mul hF).congr_deriv ?_
  simp

/-- The odd quadratic Gauss pullback `w (1-w²)^(-μ/2) 𝐅(a,b;c;w²)` has slope `𝐅(a,b;c;0)` at `0`. -/
theorem hasDerivAt_quadratic_odd (a b c μ : ℂ) :
    HasDerivAt (fun w : ℂ => w * ((1-w^2)^(-μ/2) * regularizedGaussHG a b c (w^2)))
      (regularizedGaussHG a b c 0) 0 := by
  refine ((hasDerivAt_id (0:ℂ)).mul (hasDerivAt_quadratic_even a b c μ)).congr_deriv ?_
  simp

/-- The regularized quadratic form of `𝖯^μ_ν` on `(-1,1)`, valid for all parameters. -/
theorem ferrersP_eq_quadratic (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν μ x = 2^μ*(π/(Gamma ((1-ν-μ)/2)*Gamma ((ν-μ+2)/2))*
        ((1-(x:ℂ)^2)^(-μ/2)*regularizedGaussHG (-(ν+μ)/2) ((ν-μ+1)/2) (1/2) ((x:ℂ)^2)) -
      π/(Gamma (-(ν+μ)/2)*Gamma ((ν-μ+1)/2))*
        ((x:ℂ)*((1-(x:ℂ)^2)^(-μ/2)*regularizedGaussHG ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) ((x:ℂ)^2)))) := by
  have hz : ‖((1-(x:ℂ))/2)‖<1 := by
    rw [show (1-(x:ℂ))/2=(((1-x)/2:ℝ):ℂ) by push_cast; ring,
      Complex.norm_real,Real.norm_eq_abs,abs_lt]
    constructor <;> linarith [hx.1,hx.2]
  have hw : ‖(x:ℂ)^2‖<1 := by
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    nlinarith [hx.1,hx.2]
  have hq := regularized_quadratic_connection_complementary (ν+1) (1-μ) hz
    (by rw [show 1-2*((1-(x:ℂ))/2)=(x:ℂ) by ring]; exact hw)
  rw [show 1-(ν+1) = -ν by ring,
    show 1-2*((1-(x:ℂ))/2)=(x:ℂ) by ring,
    show 1-(1-(x:ℂ))/2=(1+(x:ℂ))/2 by ring,
    show 1-μ-1 = -μ by ring,
    show (1-μ-(ν+1)+1)/2=(1-ν-μ)/2 by ring,
    show (1-μ+(ν+1))/2=(ν-μ+2)/2 by ring,
    show (1-μ-(ν+1))/2=-(ν+μ)/2 by ring,
    show (1-μ+(ν+1)-1)/2=(ν-μ+1)/2 by ring] at hq
  simp only [←regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz,
    ←regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw] at hq
  have hhalf : Gamma (1/2:ℂ)^2=(π:ℂ) := by
    rw [legendre_Gamma_one_half, ← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hodd : Gamma (-1/2:ℂ)*Gamma (3/2:ℂ)= -(π:ℂ) := by
    have hh := Gamma_add_one (-1/2:ℂ) (by norm_num)
    rw [show (-1/2:ℂ)+1=1/2 by ring] at hh
    have hm : Gamma (-1/2:ℂ) = -2*Gamma (1/2:ℂ) := by linear_combination 2*hh
    rw [hm, legendre_Gamma_three_halves, legendre_Gamma_one_half]
    have hs2 : (Real.sqrt π:ℂ)^2 = π := by rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
    linear_combination -hs2
  rw [hhalf,hodd] at hq
  unfold ferrersP
  rw [hq]
  calc
    _ = ((((1+x)/(1-x):ℝ):ℂ)^(μ/2)*((1+(x:ℂ))/2)^(-μ))*
        (π/(Gamma ((1-ν-μ)/2)*Gamma ((ν-μ+2)/2))*
          regularizedGaussHG (-(ν+μ)/2) ((ν-μ+1)/2) (1/2) (x^2)-
        π/(Gamma (-(ν+μ)/2)*Gamma ((ν-μ+1)/2))*(x*
          regularizedGaussHG ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) (x^2))) := by ring
    _ = _ := by rw [ferrers_quadratic_gauge μ hx]; ring

/-- `𝖯^μ_ν` in the even/odd basis, with reciprocal Gamma coefficients valid for all parameters. -/
theorem ferrersP_even_odd (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν μ x = 2^μ*π*((Gamma ((1-ν-μ)/2))⁻¹*(Gamma ((ν-μ+2)/2))⁻¹*ferrersEven ν μ x -
      (Gamma (-(ν+μ)/2))⁻¹*(Gamma ((ν-μ+1)/2))⁻¹*ferrersOdd ν μ x) := by
  rw [ferrersP_eq_quadratic ν μ hx, ferrersEven, ferrersOdd]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- `𝖯^{-μ}_ν` in the even/odd basis of order `μ`, valid for all parameters. -/
theorem ferrersP_neg_even_odd (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν (-μ) x = 2^(-μ)*π*((Gamma ((1-ν+μ)/2))⁻¹*(Gamma ((ν+μ+2)/2))⁻¹*ferrersEven ν μ x -
      (Gamma ((μ-ν)/2))⁻¹*(Gamma ((ν+μ+1)/2))⁻¹*ferrersOdd ν μ x) := by
  rw [ferrersP_even_odd ν (-μ) hx, ferrersEven_neg_order ν μ hx, ferrersOdd_neg_order ν μ hx]
  ring_nf

/-- `𝖰^μ_ν` in the even/odd basis; this is its definition (DLMF 14.3.12). -/
theorem ferrersQ_even_odd (ν μ : ℂ) (x : ℝ) :
    ferrersQ ν μ x = 2^μ*π/2*(-sin ((ν+μ)*π/2)*Gamma ((ν+μ+1)/2)*(Gamma ((ν-μ+2)/2))⁻¹*ferrersEven ν μ x +
      cos ((ν+μ)*π/2)*Gamma ((ν+μ+2)/2)*(Gamma ((ν-μ+1)/2))⁻¹*ferrersOdd ν μ x) := by
  simp only [ferrersQ, ferrersW1, ferrersW2, ferrersEven, ferrersOdd]
  ring

/-- `𝖰^{-μ}_ν` in the even/odd basis of order `μ`. -/
theorem ferrersQ_neg_even_odd (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ ν (-μ) x = 2^(-μ)*π/2*(-sin ((ν-μ)*π/2)*Gamma ((ν-μ+1)/2)*(Gamma ((ν+μ+2)/2))⁻¹*ferrersEven ν μ x +
      cos ((ν-μ)*π/2)*Gamma ((ν-μ+2)/2)*(Gamma ((ν+μ+1)/2))⁻¹*ferrersOdd ν μ x) := by
  rw [ferrersQ_even_odd ν (-μ) x, ferrersEven_neg_order ν μ hx, ferrersOdd_neg_order ν μ hx]
  ring_nf

/-- `𝖰^μ_{-ν-1}` in the even/odd basis of degree `ν`. -/
theorem ferrersQ_neg_degree_even_odd (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ (-ν-1) μ x = 2^μ*π/2*(cos ((ν-μ)*π/2)*Gamma ((μ-ν)/2)*(Gamma ((1-ν-μ)/2))⁻¹*ferrersEven ν μ x -
      sin ((ν-μ)*π/2)*Gamma ((1-ν+μ)/2)*(Gamma (-(ν+μ)/2))⁻¹*ferrersOdd ν μ x) := by
  have hs : sin ((-ν-1+μ)*π/2) = -cos ((ν-μ)*π/2) := by
    rw [show (-ν-1+μ)*π/2 = -((ν-μ)*π/2+π/2) by ring, sin_neg, sin_add_pi_div_two]
  have hc : cos ((-ν-1+μ)*π/2) = -sin ((ν-μ)*π/2) := by
    rw [show (-ν-1+μ)*π/2 = -((ν-μ)*π/2+π/2) by ring, cos_neg, cos_add_pi_div_two]
  rw [ferrersQ_even_odd, ferrersEven_neg_degree ν μ hx, ferrersOdd_neg_degree ν μ hx, hs, hc,
    show (-ν-1+μ+1)/2 = (μ-ν)/2 by ring, show (-ν-1-μ+2)/2 = (1-ν-μ)/2 by ring,
    show (-ν-1+μ+2)/2 = (1-ν+μ)/2 by ring, show (-ν-1-μ+1)/2 = -(ν+μ)/2 by ring]
  ring

/-- `𝖯^μ_ν` in the even/odd basis with regular-parameter Gamma coefficients (DLMF 14.3.11). -/
theorem ferrersP_regular {ν μ : ℂ} (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν μ x = 2^μ*(cos ((ν+μ)*π/2)*Gamma ((ν+μ+1)/2)/Gamma ((ν-μ+2)/2)*ferrersEven ν μ x +
      sin ((ν+μ)*π/2)*Gamma ((ν+μ+2)/2)/Gamma ((ν-μ+1)/2)*ferrersOdd ν μ x) := by
  rw [ferrersP_w1_w2 h hx, ferrersW1, ferrersW2, ferrersEven, ferrersOdd]
  ring

/-- `𝖯^{-μ}_ν` in the even/odd basis of order `μ` when `ν-μ` is regular. -/
theorem ferrersP_neg_regular {ν μ : ℂ} (h : LegendreQRegular ν (-μ)) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν (-μ) x = 2^(-μ)*(cos ((ν-μ)*π/2)*Gamma ((ν-μ+1)/2)/Gamma ((ν+μ+2)/2)*ferrersEven ν μ x +
      sin ((ν-μ)*π/2)*Gamma ((ν-μ+2)/2)/Gamma ((ν+μ+1)/2)*ferrersOdd ν μ x) := by
  rw [ferrersP_regular h hx, ferrersEven_neg_order ν μ hx, ferrersOdd_neg_order ν μ hx]
  ring_nf

/-- DLMF 14.3.2: for non-integer `μ`, `ν+μ ∉ {-1,-2,…}` and for `-1 < x < 1`, `𝖰^μ_ν(x) = π/(2
sin(μπ)) (cos(μπ) 𝖯^μ_ν(x) - Γ(ν+μ+1)/Γ(ν-μ+1) 𝖯^{-μ}_ν(x))`. -/
@[dlmf 14.3.E2]
theorem ferrersQ_hypergeometric {ν μ : ℂ} (h : LegendreQRegular ν μ) (hμ : ∀ n : ℤ, μ ≠ n) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ ν μ x = π/(2*sin (μ*π))*(cos (μ*π)*ferrersP ν μ x-Gamma (ν+μ+1)/Gamma (ν-μ+1)*ferrersP ν (-μ) x) := by
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero h
  have hs : sin (μ*π) ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h0
    exact hμ k (mul_right_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) hk)
  obtain ⟨e1, o1, e2, o2⟩ := legendre_reflections ν μ
  have kT : (2:ℂ)^μ*((2:ℂ)^μ)⁻¹ = 1 := mul_inv_cancel₀ (by simp)
  have k1 : Gamma ((ν+μ+1)/2)*(Gamma ((ν+μ+1)/2))⁻¹ = 1 := mul_inv_cancel₀ hg1
  have k2 : Gamma ((ν+μ+2)/2)*(Gamma ((ν+μ+2)/2))⁻¹ = 1 := mul_inv_cancel₀ hg2
  have pyth := sin_sq_add_cos_sq ((ν+μ)*π/2)
  rw [ferrersQ_even_odd, ferrersP_even_odd ν μ hx, ferrersP_neg_even_odd ν μ hx, legendre_Gamma_ratio,
    cpow_neg, div_mul_eq_mul_div (π:ℂ) (2*sin (μ*π)), eq_div_iff (mul_ne_zero two_ne_zero hs)]
  have hμπ : μ*π = (ν+μ)*π/2 - (ν-μ)*π/2 := by ring
  rw [hμπ, sin_sub, cos_sub]
  generalize ferrersEven ν μ x = E
  generalize ferrersOdd ν μ x = O
  generalize (Gamma ((1-ν-μ)/2))⁻¹ = A1 at e1
  generalize (Gamma (-(ν+μ)/2))⁻¹ = B1 at o1
  generalize (Gamma ((1-ν+μ)/2))⁻¹ = A2 at e2
  generalize (Gamma ((μ-ν)/2))⁻¹ = B2 at o2
  generalize (Gamma ((ν-μ+1)/2))⁻¹ = r1 at e2
  generalize (Gamma ((ν-μ+2)/2))⁻¹ = r2 at o2
  generalize Gamma ((ν+μ+1)/2) = g1 at k1 e1
  generalize Gamma ((ν+μ+2)/2) = g2 at k2 o1
  generalize (g1)⁻¹ = i1 at e1 k1
  generalize (g2)⁻¹ = i2 at o1 k2
  generalize (2:ℂ)^μ = T at kT
  generalize (T)⁻¹ = Ti at kT
  generalize sin ((ν+μ)*π/2) = sb at o1 pyth
  generalize cos ((ν+μ)*π/2) = cb at e1 pyth
  generalize sin ((ν-μ)*π/2) = sa at o2
  generalize cos ((ν-μ)*π/2) = ca at e2
  generalize (π:ℂ) = P at e1 o1 e2 o2
  linear_combination
    -(T*P*g1*r2*E*ca + T*P*g2*r1*O*sa) * pyth - ((cb*ca+sb*sa)*T*P*r2*E*g1)*e1
    + ((cb*ca+sb*sa)*T*P^2*A1*r2*E)*k1 + ((cb*ca+sb*sa)*T*P*r1*O*g2)*o1
    - ((cb*ca+sb*sa)*T*P^2*B1*r1*O)*k2 + (g1*r2*T*E*P)*e2 + (g1*r2*T*E*P)*(P*A2*r1)*k2
    + (g1*r2*T*E*P)*(P*A2*r1)*(g2*i2)*kT - (g2*r1*T*O*P)*o2 - (g2*r1*T*O*P)*(P*B2*r2)*k1
    - (g2*r1*T*O*P)*(P*B2*r2)*(g1*i1)*kT

/-- Gauss values at `x²` depend continuously on affine parameters. -/
theorem continuous_regularizedGaussHG_sq {A B C : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (hC : Differentiable ℂ C) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Continuous fun ν => regularizedGaussHG (A ν) (B ν) (C ν) ((x:ℂ)^2) :=
  (differentiable_regularizedGaussHG_comp hA hB hC (ferrers_sq_mem_cutPlane hx)).continuous

/-- The reciprocal Gamma function is continuous. -/
theorem continuous_recip_Gamma : Continuous fun s : ℂ => (Gamma s)⁻¹ := by
  simpa [one_div] using Complex.differentiable_one_div_Gamma.continuous

/-- `𝖰^μ_ν(x)` is continuous in the order at a regular parameter. -/
theorem continuousAt_ferrersQ_order {ν μ₀ : ℂ} (h : LegendreQRegular ν μ₀) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ContinuousAt (fun μ => ferrersQ ν μ x) μ₀ := by
  have h1 : ∀ m : ℕ, (ν+μ₀+1)/2 ≠ -m := fun m hm => h (2*m) (by push_cast; linear_combination 2*hm)
  have h2 : ∀ m : ℕ, (ν+μ₀+2)/2 ≠ -m := fun m hm => h (2*m+1) (by push_cast; linear_combination 2*hm)
  have c1 : ContinuousAt (fun μ => Gamma ((ν+μ+1)/2)) μ₀ :=
    ContinuousAt.comp (g := Gamma) (differentiableAt_Gamma _ h1).continuousAt (by fun_prop)
  have c2 : ContinuousAt (fun μ => Gamma ((ν+μ+2)/2)) μ₀ :=
    ContinuousAt.comp (g := Gamma) (differentiableAt_Gamma _ h2).continuousAt (by fun_prop)
  have r1 := (continuous_recip_Gamma.comp (by fun_prop : Continuous fun μ : ℂ => (ν-μ+2)/2)).continuousAt (x := μ₀)
  have r2 := (continuous_recip_Gamma.comp (by fun_prop : Continuous fun μ : ℂ => (ν-μ+1)/2)).continuousAt (x := μ₀)
  have hne := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  have p2 : Continuous fun μ : ℂ => (2:ℂ)^μ := continuous_const_cpow' (by norm_num)
  have pw : Continuous fun μ : ℂ => (1-(x:ℂ)^2)^(-μ/2) :=
    (continuous_const_cpow' hne).comp (by fun_prop)
  have g1 := continuous_regularizedGaussHG_sq (A := fun μ => -(ν+μ)/2) (B := fun μ => (ν-μ+1)/2)
    (C := fun _ => 1/2) (by fun_prop) (by fun_prop) (by fun_prop) hx
  have g2 := continuous_regularizedGaussHG_sq (A := fun μ => (1-ν-μ)/2) (B := fun μ => (ν-μ+2)/2)
    (C := fun _ => 3/2) (by fun_prop) (by fun_prop) (by fun_prop) hx
  have hs : Continuous fun μ : ℂ => sin ((ν+μ)*π/2) := by fun_prop
  have hc : Continuous fun μ : ℂ => cos ((ν+μ)*π/2) := by fun_prop
  unfold ferrersQ ferrersW1 ferrersW2
  exact ((continuousAt_const.mul hs.continuousAt).mul ((((p2.continuousAt.mul c1).mul r1).mul
    pw.continuousAt).mul g1.continuousAt)).add ((continuousAt_const.mul hc.continuousAt).mul
    (((((p2.continuousAt.mul c2).mul r2).mul continuousAt_const).mul pw.continuousAt).mul g2.continuousAt))

/-- An affine image of a punctured neighbourhood eventually avoids the poles of `Γ`. -/
theorem eventually_affine_ne_neg_nat {a : ℂ} (ha : a ≠ 0) (b μ : ℂ) :
    ∀ᶠ m in 𝓝[≠] μ, ∀ k : ℕ, a*m+b ≠ -(k:ℂ) := by
  have hc : Continuous fun m : ℂ => a*m+b := by fun_prop
  by_cases h : ∀ k : ℕ, a*μ+b ≠ -(k:ℂ)
  · exact nhdsWithin_le_nhds ((isOpen_not_neg_nat.preimage hc).mem_nhds h)
  · push Not at h
    obtain ⟨n, hn⟩ := h
    have ht : Tendsto (fun m : ℂ => a*m+b) (𝓝[≠] μ) (𝓝[≠] (-(n:ℂ))) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · rw [← hn]; exact (hc.tendsto μ).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with m hm
        intro he
        apply hm
        have : a*(m-μ) = 0 := by
          have he' : a*m+b = a*μ+b := by rw [hn]; exact he
          linear_combination he'
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha)
    exact ht.eventually (eventually_nhdsWithin_ne_neg_nat n)

/-- DLMF 14.3.2 at integer order: for an integer `m` with `ν+m ∉ {-1,-2,…}` and for `-1 < x < 1`,
the right-hand side `π/(2 sin(μπ)) (cos(μπ) 𝖯^μ_ν(x) - Γ(ν+μ+1)/Γ(ν-μ+1) 𝖯^{-μ}_ν(x))` tends to
`𝖰^m_ν(x)` as `μ → m`, `μ ≠ m`. -/
@[dlmf 14.3.E2]
theorem ferrersQ_order_limit {ν : ℂ} (m : ℤ) (h : LegendreQRegular ν m) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun μ : ℂ => π/(2*sin (μ*π))*(cos (μ*π)*ferrersP ν μ x-Gamma (ν+μ+1)/Gamma (ν-μ+1)*ferrersP ν (-μ) x)) (𝓝[≠] (m:ℂ)) (𝓝 (ferrersQ ν m x)) := by
  have hc := (continuousAt_ferrersQ_order h hx).tendsto.mono_left (nhdsWithin_le_nhds (s := {(m:ℂ)}ᶜ))
  refine hc.congr' ?_
  have hG0 : (Gamma (ν+m+1))⁻¹ ≠ 0 := inv_ne_zero (Complex.Gamma_ne_zero fun k hk =>
    h k (by linear_combination hk))
  have hev1 : ∀ᶠ μ in 𝓝 (m:ℂ), (Gamma (ν+μ+1))⁻¹ ≠ 0 :=
    ((continuous_recip_Gamma.comp (by fun_prop : Continuous fun μ : ℂ => ν+μ+1)).continuousAt
      (x := (m:ℂ))).eventually_ne hG0
  have hev2 : ∀ᶠ μ in 𝓝 (m:ℂ), μ ∈ Metric.ball (m:ℂ) 1 := Metric.ball_mem_nhds _ one_pos
  filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, self_mem_nhdsWithin] with μ hμ1 hμ2 hμ3
  have hreg : LegendreQRegular ν μ := fun k hk => hμ1 (by
    rw [show ν+μ+1 = -(k:ℂ) by linear_combination hk, Complex.Gamma_neg_nat_eq_zero, inv_zero])
  have hnot : ∀ n : ℤ, μ ≠ n := by
    intro n hn
    subst hn
    have hlt : ‖((n:ℂ)-m)‖ < 1 := by simpa [dist_eq_norm] using hμ2
    rw [← Int.cast_sub, Complex.norm_intCast] at hlt
    have : n - m = 0 := by
      have : |((n-m:ℤ):ℝ)| < 1 := by simpa using hlt
      rw [← Int.cast_abs] at this
      have : |n-m| < 1 := by exact_mod_cast this
      exact Int.abs_lt_one_iff.mp this
    exact hμ3 (by simp [show n = m by omega])
  exact ferrersQ_hypergeometric hreg hnot hx

end DLMF.Legendre
end
