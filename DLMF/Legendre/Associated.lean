/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Ferrers
public import DLMF.Legendre.Integer

/-!
# Associated Legendre functions and Olver normalization

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
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
theorem ferrersQ_ode {ν μ : ℂ} (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
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


/-! ### Ferrers solutions and Abel's identity -/

/-- `f` solves the associated Legendre equation with degree `ν` and order `μ` on `(-1,1)`,
with a second derivative of `f` in the strong sense. -/
def IsFerrersSolution (ν μ : ℂ) (f : ℝ → ℂ) : Prop :=
  ∀ y ∈ Ioo (-1:ℝ) 1, DifferentiableAt ℝ f y ∧ ∃ f2, HasDerivAt (deriv f) f2 y ∧
    (1-(y:ℂ)^2)*f2-2*y*deriv f y+(ν*(ν+1)-μ^2/(1-(y:ℂ)^2))*f y = 0

/-- Abel's identity: `(1-x²)` times the Wronskian of two Ferrers solutions is constant. -/
theorem IsFerrersSolution.wronskian_const {ν μ : ℂ} {f g : ℝ → ℂ} (hf : IsFerrersSolution ν μ f)
    (hg : IsFerrersSolution ν μ g) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-(x:ℂ)^2)*(f x*deriv g x-g x*deriv f x) = f 0*deriv g 0-g 0*deriv f 0 := by
  set F : ℝ → ℂ := fun y => (1-(y:ℂ)^2)*(f y*deriv g y-g y*deriv f y) with hFdef
  have hF : ∀ y ∈ Ioo (-1:ℝ) 1, HasDerivAt F 0 y := by
    intro y hy
    obtain ⟨hf1, f2, hf2, ef⟩ := hf y hy
    obtain ⟨hg1, g2, hg2, eg⟩ := hg y hy
    have hsq : HasDerivAt (fun y : ℝ => 1-(y:ℂ)^2) (-(2*(y:ℂ))) y := by
      have := ((hasDerivAt_id y).ofReal_comp.pow 2).const_sub 1
      simpa using this
    refine (hsq.mul ((hf1.hasDerivAt.mul hg2).sub (hg1.hasDerivAt.mul hf2))).congr_deriv ?_
    simp only [Pi.mul_apply, Pi.sub_apply]
    linear_combination (f y)*eg-(g y)*ef
  have h0 : (0:ℝ) ∈ Ioo (-1:ℝ) 1 := by norm_num
  have := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun y hy => (hF y hy).differentiableAt.differentiableWithinAt) (fun y hy => (hF y hy).deriv) hx h0
  simpa [F] using this

/-- Linear combinations of Ferrers solutions are Ferrers solutions. -/
theorem IsFerrersSolution.add_smul {ν μ : ℂ} {f g : ℝ → ℂ} (hf : IsFerrersSolution ν μ f)
    (hg : IsFerrersSolution ν μ g) (a b : ℂ) :
    IsFerrersSolution ν μ (fun y => a*f y+b*g y) := by
  intro y hy
  obtain ⟨hf1, f2, hf2, ef⟩ := hf y hy
  obtain ⟨hg1, g2, hg2, eg⟩ := hg y hy
  have hd : ∀ z ∈ Ioo (-1:ℝ) 1, deriv (fun y => a*f y+b*g y) z = a*deriv f z+b*deriv g z := by
    intro z hz
    exact (((hf z hz).1.hasDerivAt.const_mul a).add ((hg z hz).1.hasDerivAt.const_mul b)).deriv
  refine ⟨((hf1.const_mul a).add (hg1.const_mul b)), a*f2+b*g2, ?_, ?_⟩
  · refine ((hf2.const_mul a).add (hg2.const_mul b)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz using hd z hz
  · rw [hd y hy]
    linear_combination a*ef+b*eg

/-- Ferrers solutions are determined on `(-1,1)`. -/
theorem IsFerrersSolution.congr {ν μ : ℂ} {f g : ℝ → ℂ} (hf : IsFerrersSolution ν μ f)
    (h : EqOn f g (Ioo (-1:ℝ) 1)) : IsFerrersSolution ν μ g := by
  intro y hy
  have hev : ∀ z ∈ Ioo (-1:ℝ) 1, f =ᶠ[𝓝 z] g := fun z hz => by
    filter_upwards [isOpen_Ioo.mem_nhds hz] with w hw using h hw
  obtain ⟨hf1, f2, hf2, ef⟩ := hf y hy
  have hd : deriv f =ᶠ[𝓝 y] deriv g := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with w hw using (hev w hw).deriv_eq
  refine ⟨hf1.congr_of_eventuallyEq (hev y hy).symm, f2, hf2.congr_of_eventuallyEq hd.symm, ?_⟩
  rw [← hd.eq_of_nhds, ← h hy]
  exact ef

/-- Reflection `x ↦ -x` preserves Ferrers solutions. -/
theorem IsFerrersSolution.comp_neg {ν μ : ℂ} {f : ℝ → ℂ} (hf : IsFerrersSolution ν μ f) :
    IsFerrersSolution ν μ (fun y => f (-y)) := by
  have hm : ∀ y ∈ Ioo (-1:ℝ) 1, -y ∈ Ioo (-1:ℝ) 1 := fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hd : ∀ y ∈ Ioo (-1:ℝ) 1, HasDerivAt (fun y => f (-y)) (-deriv f (-y)) y := fun y hy => by
    exact ((hf (-y) (hm y hy)).1.hasDerivAt.scomp y (hasDerivAt_neg y)).congr_deriv (by simp)
  intro y hy
  obtain ⟨hf1, f2, hf2, ef⟩ := hf (-y) (hm y hy)
  refine ⟨(hd y hy).differentiableAt, f2, ?_, ?_⟩
  · have := (hf2.scomp y (hasDerivAt_neg y)).neg
    refine this.congr_of_eventuallyEq ?_ |>.congr_deriv (by simp)
    filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
    simp [(hd z hz).deriv]
  · rw [(hd y hy).deriv]
    push_cast at ef ⊢
    linear_combination ef

/-- The Gauss equation for `𝐅(α,β;γ;·)` at `x²`, `x ∈ (-1,1)`. -/
theorem regularizedGaussHG_ode_sq (α β γ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (x:ℂ)^2*(1-(x:ℂ)^2)*deriv (deriv (regularizedGaussHG α β γ)) ((x:ℂ)^2)+
      (γ-(α+β+1)*(x:ℂ)^2)*deriv (regularizedGaussHG α β γ) ((x:ℂ)^2)-
      α*β*regularizedGaussHG α β γ ((x:ℂ)^2)=0 := by
  have hs := ferrers_one_sub_sq_mem_slitPlane hx
  rw [←show iteratedDeriv 2 (regularizedGaussHG α β γ)=deriv (deriv (regularizedGaussHG α β γ)) by
    rw [iteratedDeriv_succ,iteratedDeriv_one],iteratedDeriv_regularizedGaussHG α β γ 2 hs,
    deriv_regularizedGaussHG α β γ hs]
  exact regularizedGaussHG_ode α β γ hs

/-- The even quadratic solution solves the associated Legendre equation. -/
theorem ferrersEven_isFerrersSolution (ν μ : ℂ) : IsFerrersSolution ν μ (ferrersEven ν μ) := by
  let a : ℂ := -(ν+μ)/2
  let b : ℂ := (ν-μ+1)/2
  let F := regularizedGaussHG a b (1/2)
  let g : ℂ→ℂ := fun z=>(1-z^2)^(-μ/2)
  let q : ℂ→ℂ := fun z=>μ*z/(1-z^2)
  let E1 : ℝ→ℂ := fun y=>g y*(q y*F ((y:ℂ)^2)+2*y*deriv F ((y:ℂ)^2))
  have hE (y : ℝ) (hy : y∈Ioo (-1:ℝ) 1) : HasDerivAt (ferrersEven ν μ) (E1 y) y :=
    (quadratic_gauss_gauge_jets a b (1/2) μ (ferrers_one_sub_sq_mem_slitPlane hy)).1.comp_ofReal
  intro x hx
  have heq : deriv (ferrersEven ν μ)=ᶠ[𝓝 x] E1 := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact (hE y hy).deriv
  have hE2 := (quadratic_gauss_gauge_jets a b (1/2) μ (ferrers_one_sub_sq_mem_slitPlane hx)).2.comp_ofReal
  refine ⟨(hE x hx).differentiableAt, _, hE2.congr_of_eventuallyEq heq, ?_⟩
  have he := regularizedGaussHG_ode_sq a b (1/2) hx
  rw [(hE x hx).deriv]
  simp only [ferrersEven]
  dsimp only [E1,g,q,F,a,b] at he ⊢
  have hne : 1-(x:ℂ)^2≠0 := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  linear_combination (norm := (field_simp [hne]; ring)) (4*(1-(x:ℂ)^2)^(-μ/2))*he

/-- The odd quadratic solution solves the associated Legendre equation. -/
theorem ferrersOdd_isFerrersSolution (ν μ : ℂ) : IsFerrersSolution ν μ (ferrersOdd ν μ) := by
  let A : ℂ := (1-ν-μ)/2
  let B : ℂ := (ν-μ+2)/2
  let G := regularizedGaussHG A B (3/2)
  let g : ℂ→ℂ := fun z=>(1-z^2)^(-μ/2)
  let q : ℂ→ℂ := fun z=>μ*z/(1-z^2)
  let O : ℝ→ℂ := fun y=>g y*G ((y:ℂ)^2)
  let O1 : ℝ→ℂ := fun y=>g y*(q y*G ((y:ℂ)^2)+2*y*deriv G ((y:ℂ)^2))
  have hO (y : ℝ) (hy : y∈Ioo (-1:ℝ) 1) : HasDerivAt O (O1 y) y :=
    (quadratic_gauss_gauge_jets A B (3/2) μ (ferrers_one_sub_sq_mem_slitPlane hy)).1.comp_ofReal
  have hd (y : ℝ) (hy : y∈Ioo (-1:ℝ) 1) :
      HasDerivAt (ferrersOdd ν μ) (O y+y*O1 y) y := by
    have hh := (hasDerivAt_id y).ofReal_comp.mul (hO y hy)
    exact hh.congr_deriv (by simp)
  intro x hx
  have heq : deriv (ferrersOdd ν μ)=ᶠ[𝓝 x] fun y=>O y+y*O1 y := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact (hd y hy).deriv
  have hO2 := (quadratic_gauss_gauge_jets A B (3/2) μ (ferrers_one_sub_sq_mem_slitPlane hx)).2.comp_ofReal
  have hsecond := (hO x hx).add ((hasDerivAt_id x).ofReal_comp.mul hO2)
  refine ⟨(hd x hx).differentiableAt, _, hsecond.congr_of_eventuallyEq heq, ?_⟩
  have ho := regularizedGaussHG_ode_sq A B (3/2) hx
  rw [(hd x hx).deriv]
  simp only [ferrersOdd, id_eq, ofReal_one]
  dsimp only [O1,O,g,q,G,A,B] at ho ⊢
  have hne : 1-(x:ℂ)^2≠0 := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  linear_combination (norm := (field_simp [hne]; ring)) (4*x*(1-(x:ℂ)^2)^(-μ/2))*ho

/-- The Wronskian of the even and odd quadratic solutions, `𝒲{E,O} = 2/(π(1-x²))`. -/
theorem ferrers_even_odd_wronskian (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersEven ν μ x*deriv (ferrersOdd ν μ) x-ferrersOdd ν μ x*deriv (ferrersEven ν μ) x =
      2/(π*(1-(x:ℂ)^2)) := by
  have hw := (ferrersEven_isFerrersSolution ν μ).wronskian_const (ferrersOdd_isFerrersSolution ν μ) hx
  have hE0 : ferrersEven ν μ 0 = 1/(Real.sqrt π:ℂ) := by
    unfold ferrersEven
    rw [ofReal_zero, show (0:ℂ)^2 = 0 by norm_num, regularizedGaussHG_zero_of_regular half_ne_neg_nat,
      legendre_Gamma_one_half]
    simp
  have hO0 : ferrersOdd ν μ 0 = 0 := by simp [ferrersOdd]
  have hO1 : deriv (ferrersOdd ν μ) 0 = 2/(Real.sqrt π:ℂ) := by
    have h := (hasDerivAt_quadratic_odd ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) μ).comp_ofReal (z := 0)
    rw [show ferrersOdd ν μ = fun y:ℝ => (y:ℂ)*((1-(y:ℂ)^2)^(-μ/2)*
      regularizedGaussHG ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) ((y:ℂ)^2)) from rfl, h.deriv,
      regularizedGaussHG_zero_of_regular DLMF.Hypergeometric.three_halves_not_neg_nat,
          legendre_Gamma_three_halves]
    field_simp
  rw [hE0, hO0, hO1] at hw
  have hne : 1-(x:ℂ)^2≠0 := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  have hs2 : (Real.sqrt π:ℂ)^2 = π := by rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hs : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [eq_div_iff (mul_ne_zero hP hne)]
  rw [← hs2]
  field_simp at hw ⊢
  linear_combination hw


/-- For real `ν, μ` and `-1 < x < 1`, `𝖯^μ_ν(x)` is real. -/
theorem ferrersP_real (ν μ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (ferrersP ν μ x).im=0 := by
  rw [← conj_eq_iff_im, ferrersP_conj _ _ hx]; simp

/-- For real `ν, μ` with `ν+μ ∉ {-1,-2,…}` and `-1 < x < 1`, `𝖰^μ_ν(x)` is real. -/
theorem ferrersQ_real (ν μ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) (h : LegendreQRegular ν μ) :
    (ferrersQ ν μ x).im=0 := by
  rw [← conj_eq_iff_im, ferrersQ_conj _ _ hx]; simp

/-- For real `τ, μ` and `-1 < x < 1`, the conical Ferrers function `𝖯^μ_{-1/2+iτ}(x)` is real (DLMF
§14.20). -/
theorem ferrersP_conical_real (τ μ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (ferrersP (-1/2+I*τ) μ x).im=0 := by
  have hp : 1+(x:ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  rw [← conj_eq_iff_im, ferrersP_conj _ _ hx, conj_ofReal,
    show conj (-1/2+I*(τ:ℂ)) = -(-1/2+I*τ)-1 by simp [map_div₀, map_ofNat]; ring]
  unfold ferrersP
  rw [show -(-(-1/2+I*(τ:ℂ))-1) = (-1/2+I*τ)+1 by ring, show -(-1/2+I*(τ:ℂ))-1+1 = -(-1/2+I*τ) by ring,
    regularizedGaussHG_symm _ _ _ (mem_cutPlane_of_one_add hp)]

/-- Complex Wronskian. -/
def LegendreWronskian (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z*deriv g z-g z*deriv f z

/-- The Wronskian `f(x) g'(x) - g(x) f'(x)` of two functions `ℝ → ℂ`. -/
def ferrersWronskian (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  f x*deriv g x-g x*deriv f x

/-- The Wronskian of two combinations of the even and odd solutions. -/
theorem ferrersWronskian_of_even_odd {ν μ a b c d : ℂ} {f g : ℝ → ℂ}
    (hf : EqOn f (fun y => a*ferrersEven ν μ y+b*ferrersOdd ν μ y) (Ioo (-1:ℝ) 1))
    (hg : EqOn g (fun y => c*ferrersEven ν μ y+d*ferrersOdd ν μ y) (Ioo (-1:ℝ) 1))
    {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersWronskian f g x = (a*d-b*c)*(2/(π*(1-(x:ℂ)^2))) := by
  have hE := ((ferrersEven_isFerrersSolution ν μ) x hx).1.hasDerivAt
  have hO := ((ferrersOdd_isFerrersSolution ν μ) x hx).1.hasDerivAt
  have hev : ∀ {h : ℝ → ℂ} {p q : ℂ},
      EqOn h (fun y => p*ferrersEven ν μ y+q*ferrersOdd ν μ y) (Ioo (-1:ℝ) 1) →
      deriv h x = p*deriv (ferrersEven ν μ) x+q*deriv (ferrersOdd ν μ) x := by
    intro h p q hh
    have : h =ᶠ[𝓝 x] fun y => p*ferrersEven ν μ y+q*ferrersOdd ν μ y := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using hh hy
    rw [this.deriv_eq]
    exact ((hE.const_mul p).add (hO.const_mul q)).deriv
  unfold ferrersWronskian
  rw [hev hf, hev hg, hf hx, hg hx, ← ferrers_even_odd_wronskian ν μ hx]
  ring

/-- `𝖯^μ_ν` as a combination of the even and odd solutions on `(-1,1)`. -/
theorem ferrersP_eqOn_even_odd (ν μ : ℂ) : EqOn (ferrersP ν μ) (fun y =>
    2^μ*π*((Gamma ((1-ν-μ)/2))⁻¹*(Gamma ((ν-μ+2)/2))⁻¹)*ferrersEven ν μ y+
      -(2^μ*π*((Gamma (-(ν+μ)/2))⁻¹*(Gamma ((ν-μ+1)/2))⁻¹))*ferrersOdd ν μ y) (Ioo (-1:ℝ) 1) :=
  fun y hy => by rw [ferrersP_even_odd ν μ hy]; ring

/-- `𝖯^{-μ}_ν` as a combination of the even and odd solutions on `(-1,1)`. -/
theorem ferrersP_neg_eqOn_even_odd (ν μ : ℂ) : EqOn (ferrersP ν (-μ)) (fun y =>
    2^(-μ)*π*((Gamma ((1-ν+μ)/2))⁻¹*(Gamma ((ν+μ+2)/2))⁻¹)*ferrersEven ν μ y+
      -(2^(-μ)*π*((Gamma ((μ-ν)/2))⁻¹*(Gamma ((ν+μ+1)/2))⁻¹))*ferrersOdd ν μ y) (Ioo (-1:ℝ) 1) :=
  fun y hy => by rw [ferrersP_neg_even_odd ν μ hy]; ring

/-- `𝖯^{-μ}_ν(-x)` as a combination of the even and odd solutions on `(-1,1)`. -/
theorem ferrersP_neg_reflect_eqOn_even_odd (ν μ : ℂ) : EqOn (fun x => ferrersP ν (-μ) (-x)) (fun y =>
    2^(-μ)*π*((Gamma ((1-ν+μ)/2))⁻¹*(Gamma ((ν+μ+2)/2))⁻¹)*ferrersEven ν μ y+
      2^(-μ)*π*((Gamma ((μ-ν)/2))⁻¹*(Gamma ((ν+μ+1)/2))⁻¹)*ferrersOdd ν μ y) (Ioo (-1:ℝ) 1) :=
  fun y hy => by
    simp only
    rw [ferrersP_neg_even_odd ν μ (ferrers_neg_mem_Ioo hy), ferrersEven_neg, ferrersOdd_neg]; ring

/-- `𝖰^μ_ν` as a combination of the even and odd solutions on `(-1,1)`. -/
theorem ferrersQ_eqOn_even_odd (ν μ : ℂ) : EqOn (ferrersQ ν μ) (fun y =>
    2^μ*π/2*(-sin ((ν+μ)*π/2)*Gamma ((ν+μ+1)/2)*(Gamma ((ν-μ+2)/2))⁻¹)*ferrersEven ν μ y+
      2^μ*π/2*(cos ((ν+μ)*π/2)*Gamma ((ν+μ+2)/2)*(Gamma ((ν-μ+1)/2))⁻¹)*ferrersOdd ν μ y)
    (Ioo (-1:ℝ) 1) :=
  fun y _ => by rw [ferrersQ_even_odd]; ring

/-- `𝖯^μ_ν` solves the associated Legendre equation on `(-1,1)`, for all complex `ν, μ`. -/
theorem ferrersP_isFerrersSolution (ν μ : ℂ) : IsFerrersSolution ν μ (ferrersP ν μ) :=
  ((ferrersEven_isFerrersSolution ν μ).add_smul (ferrersOdd_isFerrersSolution ν μ) _ _).congr
    (ferrersP_eqOn_even_odd ν μ).symm

/-- `𝖰^μ_ν` solves the associated Legendre equation on `(-1,1)`, for all complex `ν, μ`. -/
theorem ferrersQ_isFerrersSolution (ν μ : ℂ) : IsFerrersSolution ν μ (ferrersQ ν μ) :=
  ((ferrersEven_isFerrersSolution ν μ).add_smul (ferrersOdd_isFerrersSolution ν μ) _ _).congr
    (ferrersQ_eqOn_even_odd ν μ).symm

/-- `𝖯^μ_ν` with regular-parameter coefficients, on `(-1,1)`. -/
theorem ferrersP_regular_eqOn {ν μ : ℂ} (h : LegendreQRegular ν μ) : EqOn (ferrersP ν μ) (fun y =>
    2^μ*(cos ((ν+μ)*π/2)*Gamma ((ν+μ+1)/2)*(Gamma ((ν-μ+2)/2))⁻¹)*ferrersEven ν μ y+
      2^μ*(sin ((ν+μ)*π/2)*Gamma ((ν+μ+2)/2)*(Gamma ((ν-μ+1)/2))⁻¹)*ferrersOdd ν μ y)
    (Ioo (-1:ℝ) 1) :=
  fun y hy => by rw [ferrersP_regular h hy]; simp only [div_eq_mul_inv]; ring

/-- DLMF 14.2.3: for `-1 < x < 1`, `𝒲{𝖯^{-μ}_ν(x), 𝖯^{-μ}_ν(-x)} = 2/(Γ(μ-ν) Γ(ν+μ+1) (1-x²))`, with
`𝒲{f,g} = f g' - g f'`. -/
@[dlmf 14.2.E3]
theorem ferrers_wronskian_3 (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersWronskian (ferrersP ν (-μ)) (fun x => ferrersP ν (-μ) (-x)) x=2/(Gamma (μ-ν)*Gamma (ν+μ+1)*(1-x^2:ℂ)) := by
  rw [ferrersWronskian_of_even_odd (ferrersP_neg_eqOn_even_odd ν μ)
    (ferrersP_neg_reflect_eqOn_even_odd ν μ) hx,
    show (2:ℂ)/(Gamma (μ-ν)*Gamma (ν+μ+1)*(1-x^2:ℂ)) =
      (Gamma (μ-ν))⁻¹*(Gamma (ν+μ+1))⁻¹*(2/(1-x^2:ℂ)) by rw [div_eq_mul_inv, mul_inv, mul_inv]; ring,
    legendre_recip_Gamma_sub, legendre_recip_duplication (ν+μ), cpow_neg, cpow_neg, cpow_add _ _ two_ne_zero]
  have hne : 1-(x:ℂ)^2≠0 := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  have hs2 : (Real.sqrt π:ℂ)^2 = π := by rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hT : (2:ℂ)^μ ≠ 0 := by simp
  have hN : (2:ℂ)^ν ≠ 0 := by simp
  rw [← hs2]
  field_simp
  ring

/-- DLMF 14.2.4: when `ν+μ ∉ {-1,-2,…}` and for `-1 < x < 1`, `𝒲{𝖯^μ_ν(x), 𝖰^μ_ν(x)} =
Γ(ν+μ+1)/(Γ(ν-μ+1) (1-x²))`. -/
@[dlmf 14.2.E4]
theorem ferrers_wronskian_4 (ν μ : ℂ) (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersWronskian (ferrersP ν μ) (ferrersQ ν μ) x=Gamma (ν+μ+1)/(Gamma (ν-μ+1)*(1-x^2:ℂ)) := by
  rw [ferrersWronskian_of_even_odd (ferrersP_regular_eqOn h) (ferrersQ_eqOn_even_odd ν μ) hx,
    show Gamma (ν+μ+1)/(Gamma (ν-μ+1)*(1-x^2:ℂ)) = Gamma (ν+μ+1)/Gamma (ν-μ+1)/(1-x^2:ℂ) from
      (div_div _ _ _).symm, legendre_Gamma_ratio]
  have hne : 1-(x:ℂ)^2≠0 := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have pyth := sin_sq_add_cos_sq ((ν+μ)*π/2)
  field_simp
  linear_combination (Gamma ((ν+μ+1)/2)*Gamma ((ν+μ+2)/2)*(Gamma ((ν-μ+2)/2))⁻¹*
    (Gamma ((ν-μ+1)/2))⁻¹)*pyth

/-- DLMF 14.2.6: when `ν+μ ∉ {-1,-2,…}` and for `-1 < x < 1`, `𝒲{𝖯^{-μ}_ν(x), 𝖰^μ_ν(x)} =
cos(μπ)/(1-x²)`. -/
@[dlmf 14.2.E6]
theorem ferrers_wronskian_6 (ν μ : ℂ) (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersWronskian (ferrersP ν (-μ)) (ferrersQ ν μ) x=cos (μ*π)/(1-x^2:ℂ) := by
  have hne : 1-(x:ℂ)^2≠0 := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ferrersWronskian_of_even_odd (ferrersP_neg_eqOn_even_odd ν μ) (ferrersQ_eqOn_even_odd ν μ) hx,
    show cos (μ*π)/(1-x^2:ℂ) = (π/2*cos (μ*π))*(2/(π*(1-x^2:ℂ))) by field_simp]
  congr 1
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero h
  obtain ⟨-, -, e2, o2⟩ := legendre_reflections ν μ
  have kT : (2:ℂ)^μ*((2:ℂ)^μ)⁻¹ = 1 := mul_inv_cancel₀ (by simp)
  have k1 : Gamma ((ν+μ+1)/2)*(Gamma ((ν+μ+1)/2))⁻¹ = 1 := mul_inv_cancel₀ hg1
  have k2 : Gamma ((ν+μ+2)/2)*(Gamma ((ν+μ+2)/2))⁻¹ = 1 := mul_inv_cancel₀ hg2
  have hne : 1-(x:ℂ)^2≠0 := slitPlane_ne_zero (ferrers_one_sub_sq_mem_slitPlane hx)
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [cpow_neg, show μ*π = (ν+μ)*π/2 - (ν-μ)*π/2 by ring, cos_sub]
  generalize (Gamma ((1-ν+μ)/2))⁻¹ = A2 at e2
  generalize (Gamma ((μ-ν)/2))⁻¹ = B2 at o2
  generalize (Gamma ((ν-μ+1)/2))⁻¹ = r1 at e2
  generalize (Gamma ((ν-μ+2)/2))⁻¹ = r2 at o2
  generalize (Gamma ((ν+μ+1)/2))⁻¹ = R1 at k1
  generalize (Gamma ((ν+μ+2)/2))⁻¹ = R2 at k2
  generalize Gamma ((ν+μ+1)/2) = g1 at k1
  generalize Gamma ((ν+μ+2)/2) = g2 at k2
  generalize ((2:ℂ)^μ)⁻¹ = Ti at kT
  generalize (2:ℂ)^μ = T at kT
  generalize sin ((ν+μ)*π/2) = sb
  generalize cos ((ν+μ)*π/2) = cb
  generalize sin ((ν-μ)*π/2) = sa at o2
  generalize cos ((ν-μ)*π/2) = ca at e2
  linear_combination (π/2:ℂ)*((Ti*T*R2*g2*cb)*e2 - (Ti*T*R1*g1*sb)*o2 + cb*ca*(R2*g2*kT + k2) +
    sb*sa*(R1*g1*kT + k1))

/-- DLMF 14.2.7 (Ferrers form): for `-1 < x < 1`, `𝒲{𝖯^{-μ}_ν(x), 𝖯^μ_ν(x)} = 2 sin(μπ)/(π
(1-x²))`. -/
@[dlmf 14.2.E7]
theorem ferrers_wronskian_7 (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersWronskian (ferrersP ν (-μ)) (ferrersP ν μ) x=2*sin (μ*π)/(π*(1-x^2:ℂ)) := by
  rw [ferrersWronskian_of_even_odd (ferrersP_neg_eqOn_even_odd ν μ) (ferrersP_eqOn_even_odd ν μ) hx,
    show 2*sin (μ*π)/(π*(1-x^2:ℂ)) = sin (μ*π)*(2/(π*(1-x^2:ℂ))) by ring]
  congr 1
  obtain ⟨e1, o1, e2, o2⟩ := legendre_reflections ν μ
  have kT : (2:ℂ)^μ*((2:ℂ)^μ)⁻¹ = 1 := mul_inv_cancel₀ (by simp)
  rw [cpow_neg, show μ*π = (ν+μ)*π/2 - (ν-μ)*π/2 by ring, sin_sub]
  generalize (Gamma ((1-ν-μ)/2))⁻¹ = A1 at e1
  generalize (Gamma (-(ν+μ)/2))⁻¹ = B1 at o1
  generalize (Gamma ((1-ν+μ)/2))⁻¹ = A2 at e2
  generalize (Gamma ((μ-ν)/2))⁻¹ = B2 at o2
  generalize (Gamma ((ν-μ+1)/2))⁻¹ = r1 at e2
  generalize (Gamma ((ν-μ+2)/2))⁻¹ = r2 at o2
  generalize (Gamma ((ν+μ+1)/2))⁻¹ = R1 at e1
  generalize (Gamma ((ν+μ+2)/2))⁻¹ = R2 at o1
  generalize ((2:ℂ)^μ)⁻¹ = Ti at kT
  generalize (2:ℂ)^μ = T at kT
  generalize sin ((ν+μ)*π/2) = sb at o1
  generalize cos ((ν+μ)*π/2) = cb at e1
  generalize sin ((ν-μ)*π/2) = sa at o2
  generalize cos ((ν-μ)*π/2) = ca at e2
  generalize (π:ℂ) = P at e1 o1 e2 o2
  linear_combination (sb*ca-cb*sa)*kT + T*Ti*(-(P*B1*R2)*e2 - ca*o1 + (P*A1*R1)*o2 - sa*e1)

/-- Norm bounds on `(1,√2)` for the Legendre hypergeometric arguments. -/
theorem legendre_near_one_bounds {x : ℝ} (h1 : 1 < x) (h2 : x^2 < 2) :
    ‖((1:ℂ)-x)/2‖ < 1 ∧ (((1:ℂ)-x)/2).re < 1/2 ∧ ‖1-1/(x:ℂ)^2‖ < 1 ∧ ‖1/(x:ℂ)^2‖ < 1 := by
  have hx0 : (0:ℝ) < x := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show ((1:ℂ)-x)/2 = (((1-x)/2:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> nlinarith
  · simp; linarith
  · rw [show 1-1/(x:ℂ)^2 = ((1-1/x^2:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs, abs_lt]
    have : 0 < 1/x^2 := by positivity
    have : 1/x^2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
    constructor <;> linarith
  · rw [show 1/(x:ℂ)^2 = ((1/x^2:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs, abs_lt]
    have : 0 < 1/x^2 := by positivity
    have : 1/x^2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
    constructor <;> linarith

/-- DLMF 14.3.18-type quadratic representation near `x = 1⁺`. -/
theorem regularizedGaussHG_legendre_quadratic (ν c : ℂ) (hc : ∀ k : ℕ, c ≠ -(k:ℂ)) {x : ℝ} (h1 : 1 < x)
    (h2 : x^2 < 2) :
    regularizedGaussHG (ν+1) (-ν) c ((1-x)/2) =
      (x:ℂ)^(1+ν-c)*((1+x)/2:ℂ)^(c-1)*regularizedGaussHG ((c-ν)/2) ((c-ν-1)/2) c (1-1/(x:ℂ)^2) := by
  obtain ⟨hw, hr, hy, -⟩ := legendre_near_one_bounds h1 h2
  have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < x).ne'
  have harg : 4*(((1:ℂ)-x)/2)*(((1:ℂ)-x)/2-1)/(1-2*(((1:ℂ)-x)/2))^2 = 1-1/(x:ℂ)^2 := by
    rw [show (1:ℂ)-2*((1-x)/2) = x by ring]; field_simp; ring
  have hq := quadratic_complementary (a := -ν) (c := c) hc hw hr (by rwa [harg])
  rw [harg, show (1:ℂ)-2*((1-x)/2) = x by ring, show (1:ℂ)-((1-x)/2) = (1+x)/2 by ring,
    show (1:ℂ)-(-ν) = ν+1 by ring, show ν+1-c = 1+ν-c by ring,
    show (-ν+c)/2 = (c-ν)/2 by ring, show (-ν+c-1)/2 = (c-ν-1)/2 by ring] at hq
  rw [congrFun (ordinaryHypergeometric_symm (-ν) (ν+1) c), ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHG hc hw,
    ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHG hc hy] at hq
  have hG := Complex.Gamma_ne_zero hc
  apply mul_left_cancel₀ hG
  rw [hq]; ring

/-- The `u ↔ 1-u` connection for the Olver Gauss function at `u = 1/x²`. -/
theorem regularizedGaussHG_olver_connection (ν μ : ℂ) {x : ℝ} (h1 : 1 < x) (h2 : x^2 < 2) :
    sin (π*(-μ))/π*regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/(x:ℂ)^2) =
      (1/(x:ℂ)^2)^(-ν-1/2)*regularizedGaussHG ((1+μ-ν)/2) ((1+μ-ν-1)/2) (1+μ) (1-1/(x:ℂ)^2)/
        (Gamma ((ν-μ+1)/2)*Gamma ((ν-μ+2)/2)) -
      (1-1/(x:ℂ)^2)^(-μ)*(1/(x:ℂ)^2)^(-ν-1/2)/(Gamma ((ν+μ+2)/2)*Gamma ((ν+μ+1)/2))*
        regularizedGaussHG ((1-μ-ν)/2) ((1-μ-ν-1)/2) (1-μ) (1-1/(x:ℂ)^2) := by
  obtain ⟨-, -, hy, hu⟩ := legendre_near_one_bounds h1 h2
  have h1u : ‖1-1/(x:ℂ)^2‖ < 1 := hy
  have h := regularized_connection_one_sub ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) hu h1u
  rw [← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hu,
    ← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ h1u,
    ← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ h1u] at h
  have hyc := mem_cutPlane_of_norm_lt_one h1u
  rw [regularizedGaussHG_euler _ _ _ hyc, regularizedGaussHG_euler (ν+3/2-(ν+μ+2)/2) _ _ hyc] at h
  rw [show ν+3/2-(ν+μ+2)/2-(ν+μ+1)/2 = -μ by ring,
    show (ν+μ+2)/2+(ν+μ+1)/2-(ν+3/2)+1 = 1+μ by ring,
    show ν+3/2-(ν+μ+2)/2 = (ν-μ+1)/2 by ring, show ν+3/2-(ν+μ+1)/2 = (ν-μ+2)/2 by ring,
    show -μ+1 = 1-μ by ring, show (1:ℂ)-(1-1/(x:ℂ)^2) = 1/(x:ℂ)^2 by ring,
    show 1+μ-(ν+μ+2)/2-(ν+μ+1)/2 = -ν-1/2 by ring,
    show 1-μ-(ν-μ+1)/2-(ν-μ+2)/2 = -ν-1/2 by ring,
    show 1+μ-(ν+μ+2)/2 = (1+μ-ν-1)/2 by ring, show 1+μ-(ν+μ+1)/2 = (1+μ-ν)/2 by ring,
    show 1-μ-(ν-μ+1)/2 = (1-μ-ν)/2 by ring, show 1-μ-(ν-μ+2)/2 = (1-μ-ν-1)/2 by ring,
    regularizedGaussHG_symm ((1+μ-ν-1)/2) ((1+μ-ν)/2) (1+μ) hyc] at h
  rw [h]; ring

/-- Complex powers of positive reals as exponentials of real logarithms. -/
theorem legendre_ofReal_cpow_exp {r : ℝ} (hr : 0 < r) (s : ℂ) : ((r:ℂ))^s = exp ((Real.log r:ℂ)*s) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), ofReal_log hr.le]

/-- Powers of two as exponentials. -/
theorem legendre_two_cpow_exp (s : ℂ) : (2:ℂ)^s = exp ((Real.log 2:ℂ)*s) := by
  rw [cpow_def_of_ne_zero two_ne_zero, show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, ← ofReal_log (by norm_num)]

/-- `2 = exp (log 2)`. -/
theorem legendre_two_eq_exp : (2:ℂ) = exp (Real.log 2:ℂ) := by
  rw [← ofReal_exp, Real.exp_log (by norm_num)]; norm_num

/-- Scalar identity behind the `P^{-μ}` coefficient in DLMF 14.9.15. -/
theorem legendre_connection_scalar_minus (ν μ : ℂ) {x : ℝ} (h1 : 1 < x) :
    2*(1/(x:ℂ)^2)^(-ν-1/2)*(legendreBranchPower μ x/(2^(ν+1)*(x:ℂ)^(ν+μ+1))) =
      exp (-μ/2*(log ((x:ℂ)+1)-log ((x:ℂ)-1)))*((x:ℂ)^(1+ν-(1+μ))*((1+x)/2:ℂ)^(1+μ-1))*2^(-(ν-μ)) := by
  have hx : (0:ℝ) < x := by linarith
  have hp : (0:ℝ) < x+1 := by linarith
  have hm : (0:ℝ) < x-1 := by linarith
  have e1 : (1/(x:ℂ)^2) = ((1/x^2:ℝ):ℂ) := by push_cast; ring
  have e2 : ((1+x)/2:ℂ) = (((x+1)/2:ℝ):ℂ) := by push_cast; ring
  have e4 : (x:ℂ)+1 = ((x+1:ℝ):ℂ) := by push_cast; ring
  have e5 : (x:ℂ)-1 = ((x-1:ℝ):ℂ) := by push_cast; ring
  unfold legendreBranchPower
  rw [e1, e2, e4, e5, legendre_ofReal_cpow_exp (by positivity : (0:ℝ) < 1/x^2),
    legendre_ofReal_cpow_exp (by positivity : (0:ℝ) < (x+1)/2), legendre_ofReal_cpow_exp hx, legendre_ofReal_cpow_exp hx,
    legendre_two_cpow_exp, legendre_two_cpow_exp, ← ofReal_log hp.le, ← ofReal_log hm.le,
    Real.log_div (by positivity : x+1 ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
    Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by positivity : x^2 ≠ 0), Real.log_one, Real.log_pow]
  nth_rw 1 [legendre_two_eq_exp]
  simp only [← exp_add, ← exp_sub]
  congr 1
  push_cast
  ring

/-- Scalar identity behind the `P^{μ}` coefficient in DLMF 14.9.15. -/
theorem legendre_connection_scalar_plus (ν μ : ℂ) {x : ℝ} (h1 : 1 < x) :
    2*(1-1/(x:ℂ)^2)^(-μ)*(1/(x:ℂ)^2)^(-ν-1/2)*(legendreBranchPower μ x/(2^(ν+1)*(x:ℂ)^(ν+μ+1))) =
      exp (μ/2*(log ((x:ℂ)+1)-log ((x:ℂ)-1)))*((x:ℂ)^(1+ν-(1-μ))*((1+x)/2:ℂ)^(1-μ-1))*2^(-(ν+μ)) := by
  have hx : (0:ℝ) < x := by linarith
  have hp : (0:ℝ) < x+1 := by linarith
  have hm : (0:ℝ) < x-1 := by linarith
  have e1 : (1/(x:ℂ)^2) = ((1/x^2:ℝ):ℂ) := by push_cast; ring
  have e0 : (1-1/(x:ℂ)^2) = (((x-1)*(x+1)/x^2:ℝ):ℂ) := by
    have : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    push_cast; field_simp; ring
  have e2 : ((1+x)/2:ℂ) = (((x+1)/2:ℝ):ℂ) := by push_cast; ring
  have e4 : (x:ℂ)+1 = ((x+1:ℝ):ℂ) := by push_cast; ring
  have e5 : (x:ℂ)-1 = ((x-1:ℝ):ℂ) := by push_cast; ring
  unfold legendreBranchPower
  rw [e0, e1, e2, e4, e5, legendre_ofReal_cpow_exp (by positivity : (0:ℝ) < (x-1)*(x+1)/x^2),
    legendre_ofReal_cpow_exp (by positivity : (0:ℝ) < 1/x^2),
    legendre_ofReal_cpow_exp (by positivity : (0:ℝ) < (x+1)/2), legendre_ofReal_cpow_exp hx, legendre_ofReal_cpow_exp hx,
    legendre_two_cpow_exp, legendre_two_cpow_exp, ← ofReal_log hp.le, ← ofReal_log hm.le,
    Real.log_div (by positivity : x+1 ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
    Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by positivity : x^2 ≠ 0), Real.log_one, Real.log_pow,
    Real.log_div (by positivity : (x-1)*(x+1) ≠ 0) (by positivity : x^2 ≠ 0),
    Real.log_mul hm.ne' hp.ne', Real.log_pow]
  nth_rw 1 [legendre_two_eq_exp]
  simp only [← exp_add, ← exp_sub]
  congr 1
  push_cast
  ring

/-- DLMF 14.9.15 on `(1,√2)` for non-integer order. -/
theorem associated_connection_15_real (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {x : ℝ} (h1 : 1 < x) (h2 : x^2 < 2) :
    2*sin (μ*π)/π*olverQ ν μ x=associatedP ν μ x/Gamma (ν+μ+1)-associatedP ν (-μ) x/Gamma (ν-μ+1) := by
  have hc1 : ∀ k : ℕ, 1-μ ≠ -(k:ℂ) := fun k hk => hμ (k+1) (by push_cast; linear_combination -hk)
  have hc2 : ∀ k : ℕ, 1+μ ≠ -(k:ℂ) := fun k hk => hμ (-(k+1)) (by push_cast; linear_combination hk)
  have hT := regularizedGaussHG_olver_connection ν μ h1 h2
  have I1 := legendre_connection_scalar_minus ν μ h1
  have I2 := legendre_connection_scalar_plus ν μ h1
  have hd1 := legendre_recip_duplication (ν+μ)
  have hd2 := legendre_recip_duplication (ν-μ)
  have hs : sin (μ*π) = -sin (π*(-μ)) := by rw [mul_neg, sin_neg, neg_neg, mul_comm]
  unfold olverQ associatedP
  rw [show 1-(-μ) = 1+μ by ring, regularizedGaussHG_legendre_quadratic ν (1-μ) hc1 h1 h2,
    regularizedGaussHG_legendre_quadratic ν (1+μ) hc2 h1 h2,
    show (1-μ-ν)/2 = ((1-μ)-ν)/2 by ring] at *
  rw [div_eq_mul_inv _ (Gamma (ν+μ+1)), div_eq_mul_inv _ (Gamma (ν-μ+1)), hd1, hd2, hs]
  linear_combination (-2*(Real.sqrt π:ℂ)*(legendreBranchPower μ x/(2^(ν+1)*(x:ℂ)^(ν+μ+1))))*hT
    + (-(Real.sqrt π:ℂ)*regularizedGaussHG ((1+μ-ν)/2) ((1+μ-ν-1)/2) (1+μ) (1-1/(x:ℂ)^2)*
        (Gamma ((ν-μ+1)/2))⁻¹*(Gamma ((ν-μ+2)/2))⁻¹)*I1
    + ((Real.sqrt π:ℂ)*regularizedGaussHG ((1-μ-ν)/2) ((1-μ-ν-1)/2) (1-μ) (1-1/(x:ℂ)^2)*
        (Gamma ((ν+μ+1)/2))⁻¹*(Gamma ((ν+μ+2)/2))⁻¹)*I2

/-- DLMF 14.9.15 on the cut plane for non-integer order. -/
theorem associated_connection_15_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    2*sin (μ*π)/π*olverQ ν μ z=associatedP ν μ z/Gamma (ν+μ+1)-associatedP ν (-μ) z/Gamma (ν-μ+1) := by
  have hf : AnalyticOnNhd ℂ (fun w => 2*sin (μ*π)/π*olverQ ν μ w) {z : ℂ | z-1 ∈ slitPlane} :=
    fun w hw => analyticAt_const.mul (olverQ_analytic ν μ w hw)
  have hg : AnalyticOnNhd ℂ (fun w => associatedP ν μ w/Gamma (ν+μ+1)-associatedP ν (-μ) w/Gamma (ν-μ+1))
      {z : ℂ | z-1 ∈ slitPlane} :=
    fun w hw => ((associatedP_analytic ν μ w hw).div_const).sub ((associatedP_analytic ν (-μ) w hw).div_const)
  set x₀ : ℝ := 6/5
  have h2 : ((x₀:ℝ):ℂ) ∈ {z : ℂ | z-1 ∈ slitPlane} := by
    show ((x₀:ℝ):ℂ) - 1 ∈ slitPlane
    rw [show ((x₀:ℝ):ℂ) - 1 = ((x₀-1:ℝ):ℂ) by push_cast; ring]
    exact Or.inl (by simp [x₀]; norm_num)
  refine hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_sub_one_mem_slitPlane h2 ?_ hz
  have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] x₀) (𝓝[≠] ((x₀ : ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_inj] using hr
  apply ht.frequently
  have hI : Ioo (1:ℝ) (7/5) ∈ 𝓝 x₀ := Ioo_mem_nhds (by norm_num [x₀]) (by norm_num [x₀])
  refine (Filter.Eventually.frequently (nhdsWithin_le_nhds (Filter.mem_of_superset hI ?_)))
  intro r hr
  exact associated_connection_15_real ν μ hμ hr.1 (by nlinarith [hr.1, hr.2])

/-- DLMF 14.9.15: `2 sin(μπ)/π · 𝑸^μ_ν = P^μ_ν/Γ(ν+μ+1) - P^{-μ}_ν/Γ(ν-μ+1)` on the cut plane. -/
theorem olverQ_connection (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    2*sin (μ*π)/π*olverQ ν μ z=associatedP ν μ z/Gamma (ν+μ+1)-associatedP ν (-μ) z/Gamma (ν-μ+1) := by
  by_cases hμ : ∀ n : ℤ, μ ≠ n
  · exact associated_connection_15_nonint ν μ hμ hz
  push Not at hμ
  obtain ⟨m, rfl⟩ := hμ
  set G : ℂ → ℂ := fun μ => 2*sin (μ*π)/π*olverQ ν μ z -
    (associatedP ν μ z*(Gamma (ν+μ+1))⁻¹-associatedP ν (-μ) z*(Gamma (ν-μ+1))⁻¹)
  have hGc : Continuous G := by
    have hQ := (olverQ_entire_order ν z hz).continuous
    have hP := (associatedP_entire_order ν z hz).continuous
    have hPm : Continuous fun μ : ℂ => associatedP ν (-μ) z := hP.comp continuous_neg
    have g1 := continuous_recip_Gamma.comp (by fun_prop : Continuous fun μ : ℂ => ν+μ+1)
    have g2 := continuous_recip_Gamma.comp (by fun_prop : Continuous fun μ : ℂ => ν-μ+1)
    exact ((by fun_prop : Continuous fun μ : ℂ => 2*sin (μ*π)/π).mul hQ).sub
      ((hP.mul g1).sub (hPm.mul g2))
  have hev : G =ᶠ[𝓝[≠] (m:ℂ)] fun _ => 0 := by
    have hb : ∀ᶠ μ in 𝓝 (m:ℂ), μ ∈ Metric.ball (m:ℂ) 1 := Metric.ball_mem_nhds _ one_pos
    filter_upwards [nhdsWithin_le_nhds hb, self_mem_nhdsWithin] with μ hμ2 hμ3
    have hnot : ∀ n : ℤ, μ ≠ n := by
      intro n hn
      subst hn
      have hlt : ‖((n:ℂ)-m)‖ < 1 := by simpa [dist_eq_norm] using hμ2
      rw [← Int.cast_sub, Complex.norm_intCast] at hlt
      have : |((n-m:ℤ):ℝ)| < 1 := by simpa using hlt
      rw [← Int.cast_abs] at this
      have : |n-m| < 1 := by exact_mod_cast this
      have := Int.abs_lt_one_iff.mp this
      exact hμ3 (by simp [show n = m by omega])
    simp only [G]
    rw [associated_connection_15_nonint ν μ hnot hz, div_eq_mul_inv, div_eq_mul_inv, sub_self]
  have h0 : G m = 0 := tendsto_nhds_unique (hGc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' hev.symm)
  simp only [G] at h0
  rw [div_eq_mul_inv, div_eq_mul_inv]
  linear_combination h0

/-- The regularized Gauss function at the origin is `1/Γ(c)`, also at poles of `Γ`. -/
theorem regularizedGaussHG_at_zero (a b c : ℂ) : regularizedGaussHG a b c 0 = (Gamma c)⁻¹ := by
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by simp), regularizedGaussHGFun_eq_tsum,
    tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  simp

/-- Abel's identity for two solutions of the associated Legendre equation of orders `±μ`. -/
theorem associatedP_wronskian_const (ν μ : ℂ) {z w : ℂ} (hz : z-1 ∈ slitPlane) (hw : w-1 ∈ slitPlane) :
    (1-z^2)*LegendreWronskian (associatedP ν (-μ)) (associatedP ν μ) z =
      (1-w^2)*LegendreWronskian (associatedP ν (-μ)) (associatedP ν μ) w := by
  set G : ℂ → ℂ := fun y => (1-y^2)*LegendreWronskian (associatedP ν (-μ)) (associatedP ν μ) y
  have hd : ∀ y ∈ {z : ℂ | z-1 ∈ slitPlane}, HasDerivAt G 0 y := by
    intro y hy
    have hfa := associatedP_analytic ν (-μ) y hy
    have hga := associatedP_analytic ν μ y hy
    have hf2 : HasDerivAt (deriv (associatedP ν (-μ))) (iteratedDeriv 2 (associatedP ν (-μ)) y) y := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      exact ((associatedP_analytic ν (-μ)).deriv y hy).differentiableAt.hasDerivAt
    have hg2 : HasDerivAt (deriv (associatedP ν μ)) (iteratedDeriv 2 (associatedP ν μ) y) y := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      exact ((associatedP_analytic ν μ).deriv y hy).differentiableAt.hasDerivAt
    have ef := associatedP_ode ν (-μ) hy
    have eg := associatedP_ode ν μ hy
    rw [neg_sq] at ef
    have hsq : HasDerivAt (fun y : ℂ => 1-y^2) (-(2*y)) y := by
      simpa using ((hasDerivAt_id y).pow 2).const_sub 1
    refine (hsq.mul ((hfa.differentiableAt.hasDerivAt.mul hg2).sub
      (hga.differentiableAt.hasDerivAt.mul hf2))).congr_deriv ?_
    simp only [Pi.mul_apply, Pi.sub_apply]
    linear_combination (associatedP ν (-μ) y)*eg-(associatedP ν μ y)*ef
  have := isOpen_sub_one_mem_slitPlane.is_const_of_deriv_eq_zero isPreconnected_sub_one_mem_slitPlane
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt) (fun y hy => (hd y hy).deriv) hz hw
  simpa [G] using this

/-- DLMF 14.2.7: for `z-1` in the slit plane (`z ∉ (-∞, 1]`), `𝒲{P^{-μ}_ν(z), P^μ_ν(z)} = 2
sin(μπ)/(π (1-z²))`, with `𝒲{f,g} = f g' - g f'`. -/
@[dlmf 14.2.E7]
theorem associated_wronskian_7 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    LegendreWronskian (associatedP ν (-μ)) (associatedP ν μ) z=2*sin (μ*π)/(π*(1-z^2)) := by
  set H : ℂ → ℂ := fun y => 2*μ*regularizedGaussHG (ν+1) (-ν) (1-(-μ)) ((1-y)/2)*
      regularizedGaussHG (ν+1) (-ν) (1-μ) ((1-y)/2) + (1-y^2)*(ν*(ν+1)/2)*
      (regularizedGaussHG (ν+1) (-ν) (1-(-μ)) ((1-y)/2)*regularizedGaussHG (ν+1+1) (-ν+1) (1-μ+1) ((1-y)/2)
       - regularizedGaussHG (ν+1) (-ν) (1-μ) ((1-y)/2)*regularizedGaussHG (ν+1+1) (-ν+1) (1-(-μ)+1) ((1-y)/2))
  have hne : ∀ y : ℂ, y-1 ∈ slitPlane → 1-y^2 ≠ 0 := by
    intro y hy h
    have hp := slitPlane_ne_zero (one_add_mem_slitPlane_of_sub_one hy)
    have hfac : (y-1)*(1+y)=0 := by linear_combination -h
    exact (mul_ne_zero (slitPlane_ne_zero hy) hp) hfac
  have hGH : ∀ y : ℂ, y-1 ∈ slitPlane →
      (1-y^2)*LegendreWronskian (associatedP ν (-μ)) (associatedP ν μ) y = H y := by
    intro y hy
    have hf : HasDerivAt (associatedP ν (-μ)) _ y := hasDerivAt_associatedP_aux (ν+1) (-ν) (1-(-μ)) (-μ) hy
    have hg : HasDerivAt (associatedP ν μ) _ y := hasDerivAt_associatedP_aux (ν+1) (-ν) (1-μ) μ hy
    have hE : exp (-μ/2*(log (y+1)-log (y-1)))*exp (μ/2*(log (y+1)-log (y-1))) = 1 := by
      rw [← exp_add]; ring_nf; exact exp_zero
    have hB : exp (μ/2*(log (y+1)-log (y-1))) ≠ 0 := exp_ne_zero _
    have h1 := hne y hy
    unfold LegendreWronskian
    rw [hf.deriv, hg.deriv]
    simp only [associatedP, H]
    rw [eq_inv_of_mul_eq_one_left hE]
    generalize exp (μ/2*(log (y+1)-log (y-1))) = B at hB ⊢
    field_simp
    ring
  have hF : ∀ a b c : ℂ, ContinuousAt (fun y : ℂ => regularizedGaussHG a b c ((1-y)/2)) 1 := by
    intro a b c
    have h0 : ((1:ℂ)-1)/2 ∈ cutPlane := by simpa using zero_mem_cutPlane
    have hg : ContinuousAt (fun y : ℂ => (1-y)/2) 1 := by fun_prop
    exact ContinuousAt.comp (g := regularizedGaussHG a b c) (f := fun y : ℂ => (1-y)/2) (x := 1)
      (analyticAt_regularizedGaussHG a b c h0).continuousAt hg
  have hcont : ContinuousAt H 1 := by
    simp only [H]
    exact ((continuousAt_const.mul (hF _ _ _)).mul (hF _ _ _)).add
      ((by fun_prop : ContinuousAt (fun y : ℂ => (1-y^2)*(ν*(ν+1)/2)) 1).mul
        (((hF _ _ _).mul (hF _ _ _)).sub ((hF _ _ _).mul (hF _ _ _))))
  have hH1 : H 1 = 2*μ*(Gamma (1-(-μ)))⁻¹*(Gamma (1-μ))⁻¹ := by
    simp only [H, sub_self, zero_div, regularizedGaussHG_at_zero]; ring
  have hlim : Tendsto (fun ε : ℝ => H (1+ε)) (𝓝[>] (0:ℝ)) (𝓝 (H 1)) := by
    have : Tendsto (fun ε : ℝ => (1:ℂ)+ε) (𝓝[>] (0:ℝ)) (𝓝 1) := by
      have hc : Continuous (fun ε : ℝ => (1:ℂ)+ε) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    exact hcont.tendsto.comp this
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), H (1+ε) =
      (1-z^2)*LegendreWronskian (associatedP ν (-μ)) (associatedP ν μ) z := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hm : (1+(ε:ℂ))-1 ∈ slitPlane := by
      rw [add_sub_cancel_left]; exact Or.inl (by simpa using hε)
    rw [← hGH _ hm, associatedP_wronskian_const ν μ hm hz]
  have hval := tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds
  rw [hH1] at hval
  have hm : μ*(Gamma (1-(-μ)))⁻¹ = (Gamma μ)⁻¹ := by
    rw [show 1-(-μ) = μ+1 by ring]
    by_cases h0 : μ = 0
    · simp [h0]
    · rw [Gamma_add_one _ h0, mul_inv, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]
  have hrefl := legendre_recip_Gamma_reflection μ
  have hz1 := hne z hz
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [eq_div_iff (mul_ne_zero hpi hz1)]
  rw [show 2*μ*(Gamma (1-(-μ)))⁻¹*(Gamma (1-μ))⁻¹ = 2*((Gamma μ)⁻¹*(Gamma (1-μ))⁻¹) by
    rw [← hm]; ring] at hval
  rw [mul_comm μ π]
  linear_combination -π*hval + 2*hrefl

/-- Explicit derivative of `𝑸^μ_ν`. -/
theorem hasDerivAt_olverQ (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    HasDerivAt (olverQ ν μ) ((Real.sqrt π:ℂ)*legendreBranchPower μ z/(2^(ν+1)*z^(ν+μ+1))*
      ((μ*z/(z^2-1)-(ν+μ+1)/z)*regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/z^2) +
        (ν+μ+2)/2*((ν+μ+1)/2)*regularizedGaussHG ((ν+μ+2)/2+1) ((ν+μ+1)/2+1) (ν+3/2+1) (1/z^2)*(-2/z^3))) z := by
  have hz0 := slitPlane_ne_zero (mem_slitPlane_of_sub_one hz)
  have hm := slitPlane_ne_zero hz
  have hp' : z+1 ∈ slitPlane := by simpa [add_comm] using one_add_mem_slitPlane_of_sub_one hz
  have hp := slitPlane_ne_zero hp'
  have hB : HasDerivAt (legendreBranchPower μ) _ z :=
    ((((hasDerivAt_id z).sub_const 1).clog hz).add (((hasDerivAt_id z).add_const 1).clog hp')).const_mul (μ/2)
      |>.cexp
  have hP := (hasDerivAt_id z).cpow_const (c := ν+μ+1) (mem_slitPlane_of_sub_one hz)
  have hcut := recip_sq_mem_cutPlane hz
  have hFd := (analyticAt_regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) hcut).differentiableAt.hasDerivAt
  rw [deriv_regularizedGaussHG _ _ _ hcut] at hFd
  have hu : HasDerivAt (fun w : ℂ => 1/w^2) (-2/z^3) z := by
    have := (hasDerivAt_pow 2 z).inv (pow_ne_zero 2 hz0)
    convert this using 1
    · ext t; simp
    · field_simp; ring
  have hF := hFd.comp z hu
  have hD : HasDerivAt (fun w : ℂ => 2^(ν+1)*w^(ν+μ+1)) (2^(ν+1)*((ν+μ+1)*z^(ν+μ+1-1))) z := by
    simpa using hP.const_mul ((2:ℂ)^(ν+1))
  have hne : (2:ℂ)^(ν+1)*z^(ν+μ+1) ≠ 0 :=
    mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)) (cpow_ne_zero_iff.mpr (Or.inl hz0))
  have h := ((hB.const_mul (Real.sqrt π:ℂ)).div hD hne).mul hF
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_) |>.congr_deriv ?_
  · simp [olverQ, legendreBranchPower, Function.comp_def, mul_div_assoc]
  · simp only [id_eq, Function.comp_def]
    rw [cpow_sub _ _ hz0, cpow_one]
    unfold legendreBranchPower
    simp only [Pi.add_apply, Pi.div_apply]
    generalize exp (μ/2*(log (z-1)+log (z+1))) = E
    have hz2 : z^2-1 ≠ 0 := by intro h; apply mul_ne_zero hm hp; linear_combination h
    have hr : z^(ν+μ+1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    have h2 : (2:ℂ)^(ν+1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
    field_simp
    ring

/-- Two continuous functions that agree off a countable set agree everywhere. -/
theorem legendre_eq_of_continuous_off_countable {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    {S : Set ℂ} (hS : S.Countable) (h : ∀ μ ∉ S, f μ = g μ) (μ : ℂ) : f μ = g μ :=
  congrFun (Continuous.ext_on (hS.dense_compl ℂ) hf hg h) μ

/-- Two continuous functions that agree at non-integers agree everywhere. -/
theorem legendre_eq_of_continuous_nonint {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ μ : ℂ, (∀ n : ℤ, μ ≠ n) → f μ = g μ) (μ : ℂ) : f μ = g μ :=
  legendre_eq_of_continuous_off_countable hf hg (countable_range (Int.cast : ℤ → ℂ))
    (fun μ hμ => h μ (fun n hn => hμ ⟨n, hn.symm⟩)) μ

/-- If `μ` is not an integer, then `sin (μπ) ≠ 0`. -/
theorem legendre_sin_ne_zero {μ : ℂ} (hμ : ∀ n : ℤ, μ ≠ n) : sin (μ*π) ≠ 0 := by
  rw [Ne, Complex.sin_eq_zero_iff]
  rintro ⟨k, hk⟩
  exact hμ k (mul_right_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) hk)

/-- DLMF 14.9.11 on the principal sheet. -/
theorem associatedP_reflect_degree (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP (-ν-1) μ z=associatedP ν μ z := by
  unfold associatedP
  rw [show -(-ν-1)=ν+1 by ring, show -ν-1+1 = -ν by ring,
    regularizedGaussHG_symm _ _ _ (mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz))]

/-- For non-integer order, `𝑸^μ_ν` is locally the combination of `P^{±μ}_ν` from DLMF 14.9.15. -/
theorem olverQ_eventuallyEq_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ ν μ =ᶠ[𝓝 z] fun w => π/(2*sin (μ*π))*(associatedP ν μ w*(Gamma (ν+μ+1))⁻¹-
      associatedP ν (-μ) w*(Gamma (ν-μ+1))⁻¹) := by
  filter_upwards [isOpen_sub_one_mem_slitPlane.mem_nhds hz] with w hw
  have hc := olverQ_connection ν μ hw
  rw [div_eq_mul_inv (associatedP ν μ w), div_eq_mul_inv (associatedP ν (-μ) w)] at hc
  generalize (Gamma (ν+μ+1))⁻¹ = g1 at hc ⊢
  generalize (Gamma (ν-μ+1))⁻¹ = g2 at hc ⊢
  have hs := legendre_sin_ne_zero hμ
  have hs' : sin (π*μ) ≠ 0 := by rwa [mul_comm]
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← hc]; field_simp

/-- For non-integer `μ` and `z - 1` in the slit plane, the `z`-derivative of `𝑸^μ_ν` is `π/(2
sin(μπ))` times `(P^μ_ν)'(z)/Γ(ν+μ+1) - (P^{-μ}_ν)'(z)/Γ(ν-μ+1)`. -/
theorem deriv_olverQ_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    deriv (olverQ ν μ) z = π/(2*sin (μ*π))*(deriv (associatedP ν μ) z*(Gamma (ν+μ+1))⁻¹-
      deriv (associatedP ν (-μ)) z*(Gamma (ν-μ+1))⁻¹) := by
  rw [(olverQ_eventuallyEq_nonint ν μ hμ hz).deriv_eq]
  have h1 := (associatedP_analytic ν μ z hz).differentiableAt.hasDerivAt
  have h2 := (associatedP_analytic ν (-μ) z hz).differentiableAt.hasDerivAt
  exact (((h1.mul_const _).sub (h2.mul_const _)).const_mul _).deriv

/-- For `z - 1` in the slit plane, the derivative of `P^μ_ν` is `μ/(1-z²) P^μ_ν(z) - ((ν+1)(-ν)/2)
((z+1)/(z-1))^{μ/2} 𝐅(ν+2, 1-ν; 2-μ; (1-z)/2)`. -/
theorem deriv_associatedP (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    deriv (associatedP ν μ) z = μ/(1-z^2)*associatedP ν μ z-
      (ν+1)*(-ν)/2*(exp (μ/2*(log (z+1)-log (z-1)))*regularizedGaussHG (ν+1+1) (-ν+1) (1-μ+1) ((1-z)/2)) :=
  (hasDerivAt_associatedP_aux (ν+1) (-ν) (1-μ) μ hz).deriv

/-- For `z - 1` in the slit plane, the derivative `(P^μ_ν)'(z)` is continuous in the order `μ`. -/
theorem continuous_deriv_associatedP_order (ν : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    Continuous fun μ => deriv (associatedP ν μ) z := by
  have hw := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  have e := funext fun μ => deriv_associatedP ν μ hz
  rw [e]
  have hP := (associatedP_entire_order ν z hz).continuous
  have hG := (differentiable_regularizedGaussHG_comp (A := fun _ : ℂ => ν+1+1) (B := fun _ : ℂ => -ν+1)
    (C := fun μ : ℂ => 1-μ+1) (by fun_prop) (by fun_prop) (by fun_prop) hw).continuous
  exact ((continuous_id.div_const _).mul hP).sub (continuous_const.mul
    ((by fun_prop : Continuous fun μ : ℂ => exp (μ/2*(log (z+1)-log (z-1)))).mul hG))

/-- For `z - 1` in the slit plane, the derivative `(𝑸^μ_ν)'(z)` is continuous in the order `μ`. -/
theorem continuous_deriv_olverQ_order (ν : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    Continuous fun μ => deriv (olverQ ν μ) z := by
  have hz0 := slitPlane_ne_zero (mem_slitPlane_of_sub_one hz)
  have : NeZero z := ⟨hz0⟩
  have hc := recip_sq_mem_cutPlane hz
  have e := funext fun μ => (hasDerivAt_olverQ ν μ hz).deriv
  rw [e]
  have hB : Continuous fun μ : ℂ => legendreBranchPower μ z := by
    unfold legendreBranchPower; fun_prop
  have hP : Continuous fun μ : ℂ => z^(ν+μ+1) := (differentiable_const_cpow_of_neZero z |>.comp
    (by fun_prop : Differentiable ℂ fun μ : ℂ => ν+μ+1)).continuous
  have hG1 := (differentiable_regularizedGaussHG_comp (A := fun μ : ℂ => (ν+μ+2)/2)
    (B := fun μ : ℂ => (ν+μ+1)/2) (C := fun _ : ℂ => ν+3/2) (by fun_prop) (by fun_prop) (by fun_prop) hc).continuous
  have hG2 := (differentiable_regularizedGaussHG_comp (A := fun μ : ℂ => (ν+μ+2)/2+1)
    (B := fun μ : ℂ => (ν+μ+1)/2+1) (C := fun _ : ℂ => ν+3/2+1) (by fun_prop) (by fun_prop) (by fun_prop) hc).continuous
  have hD : ∀ μ : ℂ, (2:ℂ)^(ν+1)*z^(ν+μ+1) ≠ 0 := fun μ =>
    mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)) (cpow_ne_zero_iff.mpr (Or.inl hz0))
  exact ((continuous_const.mul hB).div (continuous_const.mul hP) hD).mul
    (((by fun_prop : Continuous fun μ : ℂ => μ*z/(z^2-1)-(ν+μ+1)/z).mul hG1).add
      (((by fun_prop : Continuous fun μ : ℂ => (ν+μ+2)/2*((ν+μ+1)/2)).mul hG2).mul continuous_const))

/-- If `z - 1` lies in the slit plane, then `z² - 1 ≠ 0`. -/
theorem legendre_sq_sub_one_ne_zero {z : ℂ} (hz : z-1 ∈ slitPlane) : z^2-1 ≠ 0 := by
  have hm := slitPlane_ne_zero hz
  have hp := slitPlane_ne_zero (one_add_mem_slitPlane_of_sub_one hz)
  intro h; apply mul_ne_zero hm hp; linear_combination h

/-- Continuity in the order of a Wronskian at a fixed point. -/
theorem continuous_legendreWronskian_order {f g : ℂ → ℂ → ℂ} {z : ℂ}
    (hf : Continuous fun μ => f μ z) (hf' : Continuous fun μ => deriv (f μ) z)
    (hg : Continuous fun μ => g μ z) (hg' : Continuous fun μ => deriv (g μ) z) :
    Continuous fun μ => LegendreWronskian (f μ) (g μ) z :=
  (hf.mul hg').sub (hg.mul hf')

/-- For non-integer `μ` and `z - 1` in the slit plane, the Wronskian `W{P^{-μ}_ν, 𝑸^μ_ν}(z) =
-1/(Γ(ν+μ+1) (z²-1))`; the non-integer case of DLMF 14.2.8. -/
theorem associated_wronskian_8_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    LegendreWronskian (associatedP ν (-μ)) (olverQ ν μ) z = -(Gamma (ν+μ+1))⁻¹*(z^2-1)⁻¹ := by
  have h7 := associated_wronskian_7 ν μ hz
  unfold LegendreWronskian at h7 ⊢
  rw [deriv_olverQ_nonint ν μ hμ hz, (olverQ_eventuallyEq_nonint ν μ hμ hz).eq_of_nhds]
  generalize (Gamma (ν+μ+1))⁻¹ = g1
  generalize (Gamma (ν-μ+1))⁻¹ = g2
  have hs := legendre_sin_ne_zero hμ
  have hs' : sin (π*μ) ≠ 0 := by rwa [mul_comm]
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz2 := legendre_sq_sub_one_ne_zero hz
  have hz2' : 1-z^2 ≠ 0 := fun h => hz2 (by linear_combination -h)
  linear_combination (norm := skip) (π/(2*sin (μ*π))*g1)*h7
  field_simp
  ring

/-- For non-integer `μ` and `z - 1` in the slit plane, the Wronskian `W{P^μ_ν, 𝑸^μ_ν}(z) =
-1/(Γ(ν-μ+1) (z²-1))`. -/
theorem olverQ_wronskian_pos_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    LegendreWronskian (associatedP ν μ) (olverQ ν μ) z = -(Gamma (ν-μ+1))⁻¹*(z^2-1)⁻¹ := by
  have h7 := associated_wronskian_7 ν μ hz
  unfold LegendreWronskian at h7 ⊢
  rw [deriv_olverQ_nonint ν μ hμ hz, (olverQ_eventuallyEq_nonint ν μ hμ hz).eq_of_nhds]
  generalize (Gamma (ν+μ+1))⁻¹ = g1
  generalize (Gamma (ν-μ+1))⁻¹ = g2
  have hs := legendre_sin_ne_zero hμ
  have hs' : sin (π*μ) ≠ 0 := by rwa [mul_comm]
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz2 := legendre_sq_sub_one_ne_zero hz
  have hz2' : 1-z^2 ≠ 0 := fun h => hz2 (by linear_combination -h)
  linear_combination (norm := skip) (π/(2*sin (μ*π))*g2)*h7
  field_simp
  ring

/-- For `z - 1` in the slit plane, `μ ↦ P^{-μ}_ν(z)` is continuous. -/
theorem continuous_associatedP_neg_order (ν : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    Continuous fun μ => associatedP ν (-μ) z :=
  (associatedP_entire_order ν z hz).continuous.comp continuous_neg

/-- For `z - 1` in the slit plane, `μ ↦ (P^{-μ}_ν)'(z)` is continuous. -/
theorem continuous_deriv_associatedP_neg_order (ν : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    Continuous fun μ => deriv (associatedP ν (-μ)) z :=
  (continuous_deriv_associatedP_order ν hz).comp continuous_neg

/-- DLMF 14.2.8: for `z-1` in the slit plane (`z ∉ (-∞, 1]`), `𝒲{P^{-μ}_ν(z), 𝑸^μ_ν(z)} =
-1/(Γ(ν+μ+1) (z²-1))`. -/
@[dlmf 14.2.E8]
theorem associated_wronskian_8 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    LegendreWronskian (associatedP ν (-μ)) (olverQ ν μ) z=-1/(Gamma (ν+μ+1)*(z^2-1)) := by
  have key := legendre_eq_of_continuous_nonint
    (f := fun μ => LegendreWronskian (associatedP ν (-μ)) (olverQ ν μ) z)
    (g := fun μ => -(Gamma (ν+μ+1))⁻¹*(z^2-1)⁻¹)
    (continuous_legendreWronskian_order (continuous_associatedP_neg_order ν hz)
      (continuous_deriv_associatedP_neg_order ν hz) (olverQ_entire_order ν z hz).continuous
      (continuous_deriv_olverQ_order ν hz))
    ((continuous_recip_Gamma.comp (by fun_prop)).neg.mul continuous_const)
    (fun μ hμ => associated_wronskian_8_nonint ν μ hμ hz) μ
  rw [key, div_eq_mul_inv, mul_inv]; ring

/-- For all complex `ν, μ` and `z - 1` in the slit plane, the Wronskian `W{P^μ_ν, 𝑸^μ_ν}(z) =
-1/(Γ(ν-μ+1) (z²-1))`, extended from non-integer `μ` by continuity in the order. -/
theorem olverQ_wronskian_pos (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    LegendreWronskian (associatedP ν μ) (olverQ ν μ) z = -(Gamma (ν-μ+1))⁻¹*(z^2-1)⁻¹ :=
  legendre_eq_of_continuous_nonint
    (f := fun μ => LegendreWronskian (associatedP ν μ) (olverQ ν μ) z)
    (g := fun μ => -(Gamma (ν-μ+1))⁻¹*(z^2-1)⁻¹)
    (continuous_legendreWronskian_order (associatedP_entire_order ν z hz).continuous
      (continuous_deriv_associatedP_order ν hz) (olverQ_entire_order ν z hz).continuous
      (continuous_deriv_olverQ_order ν hz))
    ((continuous_recip_Gamma.comp (by fun_prop)).neg.mul continuous_const)
    (fun μ hμ => olverQ_wronskian_pos_nonint ν μ hμ hz) μ

/-- DLMF 14.2.10: when `ν+μ ∉ {-1,-2,…}` and for `z-1` in the slit plane (`z ∉ (-∞, 1]`),
`𝒲{P^μ_ν(z), Q^μ_ν(z)} = -e^{μπi} Γ(ν+μ+1)/(Γ(ν-μ+1) (z²-1))`. -/
@[dlmf 14.2.E10]
theorem associated_wronskian_10 (ν μ : ℂ) (h : LegendreQRegular ν μ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    LegendreWronskian (associatedP ν μ) (associatedQ ν μ) z=-exp (μ*π*I)*Gamma (ν+μ+1)/(Gamma (ν-μ+1)*(z^2-1)) := by
  have hW := olverQ_wronskian_pos ν μ hz
  have hd : deriv (associatedQ ν μ) z = exp (μ*π*I)*Gamma (ν+μ+1)*deriv (olverQ ν μ) z :=
    deriv_const_mul _ (olverQ_analytic ν μ z hz).differentiableAt
  unfold LegendreWronskian at hW ⊢
  rw [hd]
  simp only [associatedQ]
  rw [div_eq_mul_inv, mul_inv]
  linear_combination (exp (μ*π*I)*Gamma (ν+μ+1))*hW

/-- For non-integer `μ` and `z - 1` in the slit plane, near `z` the function `𝑸^μ_{-ν-1}` equals
`π/(2 sin(μπ)) (P^μ_ν/Γ(μ-ν) - P^{-μ}_ν/Γ(-ν-μ))`, using `P^{±μ}_{-ν-1} = P^{±μ}_ν`. -/
theorem olverQ_reflect_eventuallyEq_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ (-ν-1) μ =ᶠ[𝓝 z] fun w => π/(2*sin (μ*π))*(associatedP ν μ w*(Gamma (-ν-1+μ+1))⁻¹-
      associatedP ν (-μ) w*(Gamma (-ν-1-μ+1))⁻¹) := by
  filter_upwards [olverQ_eventuallyEq_nonint (-ν-1) μ hμ hz,
    isOpen_sub_one_mem_slitPlane.mem_nhds hz] with w hw hw'
  rw [hw, associatedP_reflect_degree ν μ hw', associatedP_reflect_degree ν (-μ) hw']

/-- For non-integer `μ` and `z - 1` in the slit plane, the Wronskian `W{𝑸^μ_ν, 𝑸^μ_{-ν-1}}(z) =
cos(νπ)/(z²-1)`; the non-integer case of DLMF 14.2.9. -/
theorem associated_wronskian_9_nonint (ν μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    LegendreWronskian (olverQ ν μ) (olverQ (-ν-1) μ) z=cos (ν*π)*(z^2-1)⁻¹ := by
  have h7 := associated_wronskian_7 ν μ hz
  have he := olverQ_reflect_eventuallyEq_nonint ν μ hμ hz
  have hd2 : deriv (olverQ (-ν-1) μ) z = π/(2*sin (μ*π))*(deriv (associatedP ν μ) z*(Gamma (-ν-1+μ+1))⁻¹-
      deriv (associatedP ν (-μ)) z*(Gamma (-ν-1-μ+1))⁻¹) := by
    rw [he.deriv_eq]
    have h1 := (associatedP_analytic ν μ z hz).differentiableAt.hasDerivAt
    have h2 := (associatedP_analytic ν (-μ) z hz).differentiableAt.hasDerivAt
    exact (((h1.mul_const _).sub (h2.mul_const _)).const_mul _).deriv
  have r1 := legendre_recip_Gamma_reflection (ν+μ+1)
  have r2 := legendre_recip_Gamma_reflection (ν-μ+1)
  rw [show 1-(ν+μ+1) = -ν-1-μ+1 by ring] at r1
  rw [show 1-(ν-μ+1) = -ν-1+μ+1 by ring] at r2
  have t1 : sin (π*(ν+μ+1)) = -(sin (ν*π)*cos (μ*π)+cos (ν*π)*sin (μ*π)) := by
    rw [show (π:ℂ)*(ν+μ+1) = ν*π+μ*π+π by ring, sin_add_pi, sin_add]
  have t2 : sin (π*(ν-μ+1)) = -(sin (ν*π)*cos (μ*π)-cos (ν*π)*sin (μ*π)) := by
    rw [show (π:ℂ)*(ν-μ+1) = ν*π-μ*π+π by ring, sin_add_pi, sin_sub]
  unfold LegendreWronskian at h7 ⊢
  rw [hd2, he.eq_of_nhds, deriv_olverQ_nonint ν μ hμ hz, (olverQ_eventuallyEq_nonint ν μ hμ hz).eq_of_nhds]
  generalize (Gamma (ν+μ+1))⁻¹ = g1 at r1 ⊢
  generalize (Gamma (ν-μ+1))⁻¹ = g2 at r2 ⊢
  generalize (Gamma (-ν-1+μ+1))⁻¹ = h1 at r2 ⊢
  generalize (Gamma (-ν-1-μ+1))⁻¹ = h2 at r1 ⊢
  have hs := legendre_sin_ne_zero hμ
  have hs' : sin (π*μ) ≠ 0 := by rwa [mul_comm]
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hE : g1*h2-g2*h1 = -2*cos (ν*π)*sin (μ*π)/π := by
    rw [eq_div_iff hpi]; linear_combination r1 - r2 + t1 - t2
  have hz2 := legendre_sq_sub_one_ne_zero hz
  have hz2' : 1-z^2 ≠ 0 := fun h => hz2 (by linear_combination -h)
  linear_combination (norm := skip) ((π/(2*sin (μ*π)))^2*(g1*h2-g2*h1))*h7 +
    ((π/(2*sin (μ*π)))^2*(2*sin (μ*π)/(π*(1-z^2))))*hE
  field_simp
  ring

/-- DLMF 14.2.9: for `z-1` in the slit plane (`z ∉ (-∞, 1]`), `𝒲{𝑸^μ_ν(z), 𝑸^μ_{-ν-1}(z)} =
cos(νπ)/(z²-1)`. -/
@[dlmf 14.2.E9]
theorem associated_wronskian_9 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    LegendreWronskian (olverQ ν μ) (olverQ (-ν-1) μ) z=cos (ν*π)/(z^2-1) := by
  have key := legendre_eq_of_continuous_nonint
    (f := fun μ => LegendreWronskian (olverQ ν μ) (olverQ (-ν-1) μ) z)
    (g := fun _ => cos (ν*π)*(z^2-1)⁻¹)
    (continuous_legendreWronskian_order (olverQ_entire_order ν z hz).continuous
      (continuous_deriv_olverQ_order ν hz) (olverQ_entire_order (-ν-1) z hz).continuous
      (continuous_deriv_olverQ_order (-ν-1) hz))
    continuous_const
    (fun μ hμ => associated_wronskian_9_nonint ν μ hμ hz) μ
  rw [key, div_eq_mul_inv]





/-- DLMF 14.29.1: `f` satisfies the generalized Legendre equation at `z`, `(1-z²) f'' - 2z f' +
(ν(ν+1) - μ₁²/(2(1-z)) - μ₂²/(2(1+z))) f = 0`. -/
@[dlmf 14.29.E1]
def IsGeneralizedLegendreSolution (ν μ₁ μ₂ : ℂ) (f : ℂ → ℂ) (z : ℂ) : Prop :=
  (1-z^2)*iteratedDeriv 2 f z-2*z*deriv f z+(ν*(ν+1)-μ₁^2/(2*(1-z))-μ₂^2/(2*(1+z)))*f z=0

/-- DLMF 14.29.1 with `μ₁ = μ₂ = μ`: for `z ≠ ±1` the generalized Legendre equation reduces to the
associated Legendre equation `(1-z²) f'' - 2z f' + (ν(ν+1) - μ²/(1-z²)) f = 0`. -/
@[dlmf 14.29.E1]
theorem generalizedLegendre_equal_orders (ν μ : ℂ) (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 1) (hzm : z ≠ -1) :
    IsGeneralizedLegendreSolution ν μ μ f z ↔ (1-z^2)*iteratedDeriv 2 f z-2*z*deriv f z+(ν*(ν+1)-μ^2/(1-z^2))*f z=0 := by
  unfold IsGeneralizedLegendreSolution
  have h1 : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have h2 : 1+z ≠ 0 := by intro h; apply hzm; linear_combination h
  have he : μ^2/(2*(1-z))+μ^2/(2*(1+z))=μ^2/(1-z^2) := by
    have h3 : 1-z^2=(1-z)*(1+z) := by ring
    rw [h3]
    field_simp
    ring
  have heq : ν*(ν+1)-μ^2/(2*(1-z))-μ^2/(2*(1+z))=ν*(ν+1)-μ^2/(1-z^2) := by
    linear_combination -he
  rw [heq]

/-- The gauge factor behind the negative-integer-order formula on the cut plane. -/
theorem associated_gauge_neg_nat (m : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    exp ((m:ℂ)/2*(log (z+1)-log (z-1))) * ((1-z)/2)^m * ((1-(1-z)/2)^m)⁻¹ =
      (-1)^m * exp (-(m:ℂ)/2*(log (z+1)-log (z-1))) := by
  have h0 : z-1 ≠ 0 := slitPlane_ne_zero hz
  have h1 : z+1 ≠ 0 := by
    simpa [add_comm] using slitPlane_ne_zero (one_add_mem_slitPlane_of_sub_one hz)
  have key : exp ((m:ℂ)/2*(log (z+1)-log (z-1))) * (z-1)^m =
      exp (-(m:ℂ)/2*(log (z+1)-log (z-1))) * (z+1)^m := by
    have ha : (z-1)^m = exp (m*log (z-1)) := by rw [exp_nat_mul, exp_log h0]
    have hb : (z+1)^m = exp (m*log (z+1)) := by rw [exp_nat_mul, exp_log h1]
    rw [ha, hb, ← exp_add, ← exp_add]
    congr 1; ring
  rw [show 1-(1-z)/2 = (z+1)/2 by ring, show (1-z)/2 = (-1)*(z-1)/2 by ring, div_pow, div_pow,
    mul_pow]
  have h1m : (z+1)^m ≠ 0 := pow_ne_zero _ h1
  generalize exp ((m:ℂ)/2*(log (z+1)-log (z-1))) = E1 at key ⊢
  generalize exp (-(m:ℂ)/2*(log (z+1)-log (z-1))) = E2 at key ⊢
  field_simp
  linear_combination key

/-- The Pochhammer product behind the negative-integer-order formulas. -/
theorem poch_mul_poch_neg_mul_Gamma (ν : ℂ) (m : ℕ) (h : ∀ n : ℕ, ν-m+1 ≠ -n) :
    poch (ν+1) m * poch (-ν) m * Gamma (ν-m+1) = (-1)^m * Gamma (ν+m+1) := by
  have h1 := poch_one_sub_sub (ν-m+1) m
  rw [show 1-(ν-m+1)-(m:ℂ) = -ν by ring] at h1
  have h2 := poch_add (ν-m+1) m m
  rw [show ν-m+1+(m:ℂ) = ν+1 by ring] at h2
  have h3 := Gamma_add_nat_div_Gamma_eq (n := m+m) (ν-m+1) h
  rw [show ν-m+1+((m+m:ℕ):ℂ) = ν+m+1 by push_cast; ring] at h3
  rw [div_eq_iff (Gamma_ne_zero h)] at h3
  rw [h1, h3, ← poch, h2]
  ring

/-- Under the hypothesis of DLMF 14.9.3, `Γ(ν+m+1)` is regular and nonzero. -/
theorem Gamma_add_nat_ne_zero (ν : ℂ) (m : ℕ) (h : ∀ n : ℕ, ν-m+1 ≠ -n) : Gamma (ν+m+1) ≠ 0 :=
  Gamma_ne_zero fun n hn => h (n+2*m) (by push_cast; linear_combination hn)

/-- DLMF 15.2.3_5 followed by Euler's transformation for the Legendre parameters `ν+1, -ν`. -/
theorem regularizedGaussHG_legendre_neg_nat (ν : ℂ) (m : ℕ) {w : ℂ} (hw : w ∈ cutPlane) :
    regularizedGaussHG (ν+1) (-ν) (1-((m+1:ℕ):ℂ)) w = poch (ν+1) (m+1) * poch (-ν) (m+1) *
      w^(m+1) * ((1-w)^(m+1))⁻¹ * regularizedGaussHG (ν+1) (-ν) ((m+1:ℕ)+1) w := by
  rw [show 1-((m+1:ℕ):ℂ) = -(m:ℂ) by push_cast; ring, regularizedGaussHG_neg_nat _ _ _ hw,
    regularizedGaussHG_euler _ _ _ hw,
    show (m:ℂ)+2-(ν+1+m+1)-(-ν+m+1) = -((m+1:ℕ):ℂ) by push_cast; ring,
    show (m:ℂ)+2-(ν+1+m+1) = -ν by ring, show (m:ℂ)+2-(-ν+m+1) = ν+1 by ring,
    regularizedGaussHG_symm _ _ _ hw, cpow_neg, cpow_natCast,
    show (m:ℂ)+2 = ((m+1:ℕ):ℂ)+1 by push_cast; ring]
  ring

/-- The Ferrers gauge factor behind DLMF 14.9.3. -/
theorem ferrers_gauge_neg_nat (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (((1+x)/(1-x):ℝ):ℂ)^((m:ℂ)/2) * ((1-(x:ℂ))/2)^m * ((1-(1-(x:ℂ))/2)^m)⁻¹ =
      (((1+x)/(1-x):ℝ):ℂ)^(-(m:ℂ)/2) := by
  have h1 : (0:ℝ) < 1+x := by linarith [hx.1]
  have h2 : (0:ℝ) < 1-x := by linarith [hx.2]
  have hr : (((1+x)/(1-x):ℝ):ℂ) ≠ 0 := ofReal_ne_zero.mpr (div_pos h1 h2).ne'
  have h1' : (1+(x:ℂ)) ≠ 0 := by exact_mod_cast h1.ne'
  have h2' : (1-(x:ℂ)) ≠ 0 := by exact_mod_cast h2.ne'
  have hsq : (((1+x)/(1-x):ℝ):ℂ)^((m:ℂ)/2) * (((1+x)/(1-x):ℝ):ℂ)^((m:ℂ)/2) =
      ((1+(x:ℂ))/(1-x))^m := by
    rw [← cpow_add _ _ hr, add_halves, cpow_natCast]; push_cast; rfl
  have hc : (((1+x)/(1-x):ℝ):ℂ)^((m:ℂ)/2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hr)
  rw [show -(m:ℂ)/2 = -((m:ℂ)/2) by ring, cpow_neg, show 1-(1-(x:ℂ))/2 = (1+x)/2 by ring]
  generalize (((1+x)/(1-x):ℝ):ℂ)^((m:ℂ)/2) = R at hsq hc ⊢
  rw [div_pow] at hsq
  have h1m : (1+(x:ℂ))^m ≠ 0 := pow_ne_zero _ h1'
  have h2m : (1-(x:ℂ))^m ≠ 0 := pow_ne_zero _ h2'
  rw [div_pow, div_pow]
  field_simp
  field_simp at hsq
  linear_combination hsq
/-- The Legendre Pochhammer product `(ν+1)ₘ(-ν)ₘ = (-1)ᵐ (ν-m+1)₂ₘ`. -/
theorem poch_mul_poch_neg (ν : ℂ) (m : ℕ) :
    poch (ν+1) m * poch (-ν) m = (-1)^m * poch (ν-m+1) (2*m) := by
  have h1 := poch_one_sub_sub (ν-m+1) m
  rw [show 1-(ν-m+1)-(m:ℂ) = -ν by ring] at h1
  have h2 := poch_add (ν-m+1) m m
  rw [show ν-m+1+(m:ℂ) = ν+1 by ring] at h2
  rw [h1, two_mul, h2]
  ring

/-- The Ferrers gauge factor at nonnegative integer order. -/
theorem ferrers_gauge_nat (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (((1+x)/(1-x):ℝ):ℂ)^((m:ℂ)/2) * ((1-(x:ℂ))/2)^m = (1-(x:ℂ)^2)^((m:ℂ)/2)/2^m := by
  have ha : (0:ℝ) ≤ 1+x := by linarith [hx.1]
  have hb : (0:ℝ) < 1-x := by linarith [hx.2]
  have hb0 : ((1-x:ℝ):ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have e1 : (((1+x)/(1-x):ℝ):ℂ) = ((1+x:ℝ):ℂ)/((1-x:ℝ):ℂ) := by push_cast; ring
  have e2 : 1-(x:ℂ)^2 = ((1+x:ℝ):ℂ)*((1-x:ℝ):ℂ) := by push_cast; ring
  have e3 : (1-(x:ℂ))^m = ((1-x:ℝ):ℂ)^((m:ℂ)/2) * ((1-x:ℝ):ℂ)^((m:ℂ)/2) := by
    rw [← cpow_add _ _ hb0, add_halves, cpow_natCast]; push_cast; rfl
  have hc : ((1-x:ℝ):ℂ)^((m:ℂ)/2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hb0)
  rw [e1, e2, div_cpow_ofReal_nonneg ha hb.le, mul_cpow_ofReal_nonneg ha hb.le, div_pow, e3]
  field_simp

/-- The gauge factor of the associated Legendre function at nonnegative integer order. -/
theorem associated_gauge_nat (m : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    exp ((m:ℂ)/2*(log (z+1)-log (z-1))) * ((-1)^m * ((1-z)/2)^m) =
      legendreBranchPower m z / 2^m := by
  have h0 : z-1 ≠ 0 := slitPlane_ne_zero hz
  have ha : (z-1)^m = exp ((m:ℂ)*log (z-1)) := by rw [exp_nat_mul, exp_log h0]
  rw [← mul_pow, show (-1)*((1-z)/2) = (z-1)/2 by ring, div_pow, ha, legendreBranchPower,
    mul_div_assoc', ← exp_add]
  congr 2; ring

end DLMF.Legendre
