/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Associated
public import DLMF.Elliptic.Complete
public import DLMF.Legendre.Neumann
public import DLMF.Hypergeometric.Clausen
public import DLMF.Legendre.Connections
public import DLMF.Elliptic.AGM

/-!
# Associated Legendre and Ferrers special values

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

/-- DLMF 14.5.1: for all complex `ν, μ`, `𝖯^μ_ν(0) = 2^μ π^{1/2}/(Γ((ν-μ)/2+1) Γ((1-ν-μ)/2))`. -/
@[dlmf 14.5.E1]
theorem ferrersP_zero_1 (ν μ : ℂ) :
    ferrersP ν μ 0=2^μ*Real.sqrt π/(Gamma ((ν-μ)/2+1)*Gamma ((1-ν-μ)/2)) := by
  have hz : ‖(1/2:ℂ)‖ < 1 := by norm_num
  have hw : ‖(1-2*(1/2:ℂ))^2‖ < 1 := by norm_num
  have hq := regularized_quadratic_connection_complementary (ν+1) (1-μ) hz hw
  have hh : ∀ k : ℕ, (1/2:ℂ) ≠ -(k:ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  unfold ferrersP
  simp only [ofReal_zero, add_zero, sub_zero, div_one, ofReal_one, one_cpow, one_mul]
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz, show -ν = 1-(ν+1) by ring, hq,
    show (1:ℂ)-2*(1/2) = 0 by norm_num, zero_pow two_ne_zero, regularizedGaussHGFun_zero_of_regular hh,
    show (1:ℂ)-1/2 = 1/2 by norm_num, show 1-μ-1 = -μ by ring, half_cpow_neg,
    show (1-μ-(ν+1)+1)/2 = (1-ν-μ)/2 by ring, show (1-μ+(ν+1))/2 = (ν-μ)/2+1 by ring,
    legendre_Gamma_one_half]
  have hs : (Real.sqrt π : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp
  ring

/-- DLMF 14.5.2: for all complex `ν, μ`, `𝖯^μ_ν` has derivative `-2^{μ+1} π^{1/2}/(Γ((ν-μ+1)/2)
Γ(-(ν+μ)/2))` at `x = 0`. -/
@[dlmf 14.5.E2]
theorem ferrersP_zero_2 (ν μ : ℂ) :
    HasDerivAt (ferrersP ν μ) (-2^(μ+1)*Real.sqrt π/(Gamma ((ν-μ+1)/2)*Gamma (-(ν+μ)/2))) 0 := by
  have h1 := (hasDerivAt_quadratic_even (-(ν+μ)/2) ((ν-μ+1)/2) (1/2) μ).comp_ofReal (z := 0)
  have h2 := (hasDerivAt_quadratic_odd ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) μ).comp_ofReal (z := 0)
  have hd := ((h1.const_mul (π/(Gamma ((1-ν-μ)/2)*Gamma ((ν-μ+2)/2)))).sub
    (h2.const_mul (π/(Gamma (-(ν+μ)/2)*Gamma ((ν-μ+1)/2))))).const_mul ((2:ℂ)^μ)
  have hev : ferrersP ν μ =ᶠ[𝓝 0] fun x : ℝ => 2^μ*(π/(Gamma ((1-ν-μ)/2)*Gamma ((ν-μ+2)/2))*
        ((1-(x:ℂ)^2)^(-μ/2)*regularizedGaussHG (-(ν+μ)/2) ((ν-μ+1)/2) (1/2) ((x:ℂ)^2)) -
      π/(Gamma (-(ν+μ)/2)*Gamma ((ν-μ+1)/2))*
        ((x:ℂ)*((1-(x:ℂ)^2)^(-μ/2)*regularizedGaussHG ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) ((x:ℂ)^2)))) := by
    filter_upwards [Ioo_mem_nhds (show (-1:ℝ) < 0 by norm_num) (show (0:ℝ) < 1 by norm_num)]
      with x hx using ferrersP_eq_quadratic ν μ hx
  refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [regularizedGaussHG_zero_of_regular DLMF.Hypergeometric.three_halves_not_neg_nat,
      legendre_Gamma_three_halves,
    cpow_add _ _ (by norm_num : (2:ℂ) ≠ 0), cpow_one]
  have hs : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpi : (π:ℂ) = (Real.sqrt π : ℂ)^2 := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  rw [hpi]
  field_simp
  ring

/-- DLMF 14.5.3: when `ν+μ ∉ {-1,-2,…}`, `𝖰^μ_ν(0) = -2^{μ-1} π^{1/2} sin((ν+μ)π/2)
Γ((ν+μ+1)/2)/Γ((ν-μ)/2+1)`. -/
@[dlmf 14.5.E3]
theorem ferrersQ_zero_3 (ν μ : ℂ) (h : LegendreQRegular ν μ) :
    ferrersQ ν μ 0=-2^(μ-1)*Real.sqrt π*sin ((ν+μ)*π/2)*Gamma ((ν+μ+1)/2)/Gamma ((ν-μ)/2+1) := by
  unfold ferrersQ ferrersW1 ferrersW2
  simp only [ofReal_zero, zero_mul, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, sub_zero, one_cpow, mul_one]
  rw [regularizedGaussHG_zero_of_regular half_ne_neg_nat, legendre_Gamma_one_half,
    cpow_sub _ _ (by norm_num : (2:ℂ) ≠ 0), cpow_one, show (ν-μ+2)/2 = (ν-μ)/2+1 by ring]
  have hs : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpi : (π:ℂ) = (Real.sqrt π : ℂ)^2 := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  rw [hpi]
  field_simp

/-- DLMF 14.5.4: when `ν+μ ∉ {-1,-2,…}`, `𝖰^μ_ν` has derivative `2^μ π^{1/2} cos((ν+μ)π/2)
Γ((ν+μ)/2+1)/Γ((ν-μ+1)/2)` at `x = 0`. -/
@[dlmf 14.5.E4]
theorem ferrersQ_zero_4 (ν μ : ℂ) (h : LegendreQRegular ν μ) :
    HasDerivAt (ferrersQ ν μ) (2^μ*Real.sqrt π*cos ((ν+μ)*π/2)*Gamma ((ν+μ)/2+1)/Gamma ((ν-μ+1)/2)) 0 := by
  have h1 := (hasDerivAt_quadratic_even (-(ν+μ)/2) ((ν-μ+1)/2) (1/2) μ).comp_ofReal (z := 0)
  have h2 := (hasDerivAt_quadratic_odd ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) μ).comp_ofReal (z := 0)
  have hd := ((h1.const_mul (-π/2*sin ((ν+μ)*π/2)*(2^μ*Gamma ((ν+μ+1)/2)/Gamma ((ν-μ+2)/2))))).add
    (h2.const_mul (π/2*cos ((ν+μ)*π/2)*(2^μ*Gamma ((ν+μ+2)/2)/Gamma ((ν-μ+1)/2))))
  have he : ferrersQ ν μ = fun x : ℝ =>
      -π/2*sin ((ν+μ)*π/2)*(2^μ*Gamma ((ν+μ+1)/2)/Gamma ((ν-μ+2)/2))*
        ((1-(x:ℂ)^2)^(-μ/2)*regularizedGaussHG (-(ν+μ)/2) ((ν-μ+1)/2) (1/2) ((x:ℂ)^2)) +
      π/2*cos ((ν+μ)*π/2)*(2^μ*Gamma ((ν+μ+2)/2)/Gamma ((ν-μ+1)/2))*
        ((x:ℂ)*((1-(x:ℂ)^2)^(-μ/2)*regularizedGaussHG ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) ((x:ℂ)^2))) := by
    funext x
    unfold ferrersQ ferrersW1 ferrersW2
    ring
  rw [he]
  refine hd.congr_deriv ?_
  rw [regularizedGaussHG_zero_of_regular DLMF.Hypergeometric.three_halves_not_neg_nat,
      legendre_Gamma_three_halves,
    show (ν+μ+2)/2 = (ν+μ)/2+1 by ring]
  have hs : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpi : (π:ℂ) = (Real.sqrt π : ℂ)^2 := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  rw [hpi]
  field_simp
  ring

/-- DLMF 14.5.5: `𝖯_0(x) = 1` for `-1 < x < 1`. -/
@[dlmf 14.5.E5]
theorem ferrersP_degree_0 {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP 0 0 x=1 := by
  have hz : 1+(x:ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  rw [ferrersP_zero _ hx.1]
  have hN := legendreP_nat 0 hz
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at hN
  rw [hN]
  exact DLMF.OrthogonalPolynomials.legendrePolyP_zero _

/-- DLMF 14.5.6: `𝖯_1(x) = x` for `-1 < x < 1`. -/
@[dlmf 14.5.E6]
theorem ferrersP_degree_1 {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP 1 0 x=x := by
  have hz : 1+(x:ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  rw [ferrersP_zero _ hx.1]
  have hN := legendreP_nat 1 hz
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at hN
  rw [hN]
  exact DLMF.OrthogonalPolynomials.legendrePolyP_one _

/-- DLMF 14.5.28: `𝖯_2(x) = (3x²-1)/2` for `-1 < x < 1`. -/
@[dlmf 14.5.E28]
theorem ferrersP_degree_2 {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP 2 0 x=(3*x^2-1)/2 := by
  have hz : 1+(x:ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  rw [ferrersP_zero _ hx.1]
  have hN := legendreP_nat 2 hz
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at hN
  rw [hN]
  have h := DLMF.OrthogonalPolynomials.legendrePolyP_recurrence 0 (x:ℂ)
  norm_num [DLMF.OrthogonalPolynomials.legendrePolyP_zero,
    DLMF.OrthogonalPolynomials.legendrePolyP_one] at h
  linear_combination h/2

/-- DLMF 14.5.5: `P_0(z) = 1` for `z-1` in the slit plane (`z ∉ (-∞, 1]`). -/
@[dlmf 14.5.E5]
theorem associatedP_degree_0 {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP 0 0 z=1 := by
  have hz' := one_add_mem_slitPlane_of_sub_one hz
  rw [associatedP_zero_order _ hz]
  have hN := legendreP_nat 0 hz'
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at hN
  rw [hN]
  exact DLMF.OrthogonalPolynomials.legendrePolyP_zero _

/-- DLMF 14.5.6: `P_1(z) = z` for `z-1` in the slit plane (`z ∉ (-∞, 1]`). -/
@[dlmf 14.5.E6]
theorem associatedP_degree_1 {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP 1 0 z=z := by
  have hz' := one_add_mem_slitPlane_of_sub_one hz
  rw [associatedP_zero_order _ hz]
  have hN := legendreP_nat 1 hz'
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at hN
  rw [hN]
  exact DLMF.OrthogonalPolynomials.legendrePolyP_one _

/-- DLMF 14.5.28: `P_2(z) = (3z²-1)/2` for `z-1` in the slit plane (`z ∉ (-∞, 1]`). -/
@[dlmf 14.5.E28]
theorem associatedP_degree_2 {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP 2 0 z=(3*z^2-1)/2 := by
  have hz' := one_add_mem_slitPlane_of_sub_one hz
  rw [associatedP_zero_order _ hz]
  have hN := legendreP_nat 2 hz'
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at hN
  rw [hN]
  have h := DLMF.OrthogonalPolynomials.legendrePolyP_recurrence 0 z
  norm_num [DLMF.OrthogonalPolynomials.legendrePolyP_zero,
    DLMF.OrthogonalPolynomials.legendrePolyP_one] at h
  linear_combination h/2

/-- `𝐅(1/2,1;1/2;w) = (1-w)⁻¹/Γ(1/2)` on the cut plane. -/
theorem regularizedGaussHG_half_one_half {w : ℂ} (hw : w ∈ cutPlane) :
    regularizedGaussHG (1/2) 1 (1/2) w = (1-w)⁻¹/Real.sqrt π := by
  rw [regularizedGaussHG_euler _ _ _ hw, show (1/2:ℂ)-1/2-1 = -1 by norm_num,
    show (1/2:ℂ)-1/2 = 0 by norm_num, regularizedGaussHG_zero_left _ _ hw, legendre_Gamma_one_half,
    cpow_neg_one]
  ring

/-- Values of `𝐅(·,·;·;x²)` behind `𝖰₀, 𝖰₁, 𝖰₂`, in terms of `A = 𝐅(1/2,1;3/2;x²)`. -/
lemma regularizedGaussHG_ferrersQ_aux {w : ℂ} (hw : w ∈ cutPlane) :
    regularizedGaussHG (-(1/2)) 1 (1/2) w = 1/Real.sqrt π - w/2*regularizedGaussHG (1/2) 1 (3/2) w ∧
    w*regularizedGaussHG (-(1/2)) 2 (3/2) w =
      w*(3/(2*Real.sqrt π) + (1-3*w)/4*regularizedGaussHG (1/2) 1 (3/2) w) := by
  have h1 := regularizedGaussHG_contiguous_a_pred_c_succ (1/2) 1 (1/2) hw
  have h2 := regularizedGaussHG_contiguous_a_c_succ (-1/2) 1 (1/2) hw
  have h3 := regularizedGaussHG_contiguous_ab (-1/2) 1 (3/2) hw
  have hh := regularizedGaussHG_half_one_half hw
  have hw1 : 1-w ≠ 0 := one_sub_ne_zero_of_mem_cutPlane hw
  have hs : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  norm_num at h1 h2 h3
  rw [hh] at h1 h2
  have e : (1-w)*((1-w)⁻¹/(Real.sqrt π:ℂ)) = 1/Real.sqrt π := by field_simp
  rw [e] at h1
  exact ⟨by linear_combination -h1, by linear_combination (-w)*h3 - 3*h2 - (3/2)*(w-1)*h1 + (3/2)*e⟩

/-- `x 𝐅(1/2,1;3/2;x²) = log((1+x)/(1-x))/√π` on `(-1,1)`. -/
theorem ofReal_mul_regularizedGaussHG_log_ratio {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (x:ℂ)*regularizedGaussHG (1/2) 1 (3/2) ((x:ℂ)^2) = log ((1+x)/(1-x):ℂ)/Real.sqrt π := by
  have hx1 : ‖(x:ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]; exact ⟨hx.1, hx.2⟩
  have hw : ‖(x:ℂ)^2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg (x:ℂ)]
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw,
    regularizedGaussHGFun_eq_div_Gamma DLMF.Hypergeometric.three_halves_not_neg_nat,
        legendre_Gamma_three_halves,
    ← log_ratio hx1]
  have hs : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp

/-- DLMF 14.5.7: `𝖰_0(x) = (1/2) ln((1+x)/(1-x))` for `-1 < x < 1`. -/
@[dlmf 14.5.E7]
theorem ferrersQ_degree_0 {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ 0 0 x=1/2*log ((1+x)/(1-x):ℂ) := by
  have hA := ofReal_mul_regularizedGaussHG_log_ratio hx
  unfold ferrersQ ferrersW1 ferrersW2
  norm_num
  have hs : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpi : (π:ℂ) = (Real.sqrt π : ℂ)^2 := by rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  rw [legendre_Gamma_one_half, mul_assoc, hA, hpi]
  field_simp

/-- DLMF 14.5.8: `𝖰_1(x) = (x/2) ln((1+x)/(1-x)) - 1` for `-1 < x < 1`. -/
@[dlmf 14.5.E8]
theorem ferrersQ_degree_1 {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ 1 0 x=x/2*log ((1+x)/(1-x):ℂ)-1 := by
  have hA := ofReal_mul_regularizedGaussHG_log_ratio hx
  unfold ferrersQ ferrersW1 ferrersW2
  norm_num
  have hs : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpi : (π:ℂ) = (Real.sqrt π : ℂ)^2 := by rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hw : (x:ℂ)^2 ∈ cutPlane := mem_cutPlane_of_norm_lt_one (by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]; nlinarith [hx.1, hx.2])
  obtain ⟨h1, h2⟩ := regularizedGaussHG_ferrersQ_aux hw
  rw [h1, legendre_Gamma_three_halves, hpi]
  field_simp at hA ⊢
  linear_combination (x:ℂ) * hA

/-- DLMF 14.5.29: `𝖰_2(x) = ((3x²-1)/4) ln((1+x)/(1-x)) - 3x/2` for `-1 < x < 1`. -/
@[dlmf 14.5.E29]
theorem ferrersQ_degree_2 {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ 2 0 x=(3*x^2-1:ℂ)/4*log ((1+x)/(1-x):ℂ)-3*x/2 := by
  have hA := ofReal_mul_regularizedGaussHG_log_ratio hx
  unfold ferrersQ ferrersW1 ferrersW2
  norm_num
  have hs : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpi : (π:ℂ) = (Real.sqrt π : ℂ)^2 := by rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hw : (x:ℂ)^2 ∈ cutPlane := mem_cutPlane_of_norm_lt_one (by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]; nlinarith [hx.1, hx.2])
  obtain ⟨h1, h2⟩ := regularizedGaussHG_ferrersQ_aux hw
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hx0' : (x:ℂ)^2 ≠ 0 := pow_ne_zero 2 (ofReal_ne_zero.mpr hx0)
  have h2' := mul_left_cancel₀ hx0' h2
  rw [h2', legendre_Gamma_three_halves, hpi]
  field_simp at hA ⊢
  linear_combination (6*(x:ℂ)^2-2) * hA

/-- DLMF 14.5.9: `𝑸_0(z) = (1/2)(ln(z+1) - ln(z-1))` for `z-1` in the slit plane (`z ∉ (-∞, 1]`),
principal logarithms. -/
@[dlmf 14.5.E9]
theorem olverQ_degree_0 {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ 0 0 z=1/2*(log (z+1)-log (z-1)) := by
  have h := legInt_olverQ_nat_zero_order 0 hz
  norm_num at h
  rw [h, legendreQ_zero hz, log_add_one_sub_log_sub_one hz]

/-- DLMF 14.5.10: `𝑸_1(z) = (z/2)(ln(z+1) - ln(z-1)) - 1` for `z-1` in the slit plane (`z ∉ (-∞,
1]`), principal logarithms. -/
@[dlmf 14.5.E10]
theorem olverQ_degree_1 {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ 1 0 z=z/2*(log (z+1)-log (z-1))-1 := by
  have h := legInt_olverQ_nat_zero_order 1 hz
  norm_num at h
  rw [h, legendreQ_one hz, legendreQ_zero hz, log_add_one_sub_log_sub_one hz]
  ring

/-- DLMF 14.5.30: `𝑸_2(z) = ((3z²-1)/8)(ln(z+1) - ln(z-1)) - 3z/4` for `z-1` in the slit plane (`z ∉
(-∞, 1]`), principal logarithms. -/
@[dlmf 14.5.E30]
theorem olverQ_degree_2 {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ 2 0 z=(3*z^2-1)/8*(log (z+1)-log (z-1))-3*z/4 := by
  have h := legInt_olverQ_nat_zero_order 2 hz
  norm_num at h
  have hr := legendreQ_recurrence (ν := 1) one_ne_zero hz
  norm_num at hr
  rw [h, log_add_one_sub_log_sub_one hz]
  rw [legendreQ_one hz, legendreQ_zero hz] at hr
  linear_combination hr/4

/-- DLMF 14.5.11: for `0 < θ < π`, `𝖯^{1/2}_ν(cos θ) = (2/(π sin θ))^{1/2} cos((ν+1/2)θ)`. -/
@[dlmf 14.5.E11]
theorem ferrersP_half_order_11 (ν : ℂ) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersP ν (1/2) (Real.cos θ)=(2/(π*Real.sin θ):ℂ)^(1/2:ℂ)*cos ((ν+1/2)*θ)/(1) := by
  set t := θ/2 with ht
  have ht0 : 0 < t := by positivity
  have htπ : t < π/2 := by linarith
  have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith)
  have hct : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith, htπ⟩
  have hθ : θ = 2*t := by rw [ht]; ring
  have hcos : Real.cos θ = 1 - 2*Real.sin t^2 := by rw [hθ, Real.cos_two_mul, Real.cos_sq']; ring
  have hsin : Real.sin θ = 2*Real.sin t*Real.cos t := by rw [hθ, Real.sin_two_mul]
  have habs : |t| < π/2 := by rw [abs_of_pos ht0]; exact htπ
  have hsq1 : Real.sin t^2 < 1 := by
    have := Real.sin_sq_add_cos_sq t; nlinarith
  have hz : ‖((1:ℂ) - (Real.cos θ:ℝ))/2‖ < 1 := by
    rw [hcos, show ((1:ℂ) - ((1 - 2*Real.sin t^2 : ℝ) : ℂ))/2 = ((Real.sin t^2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hsq1
  have hc : ∀ k : ℕ, (1 - 1/2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [ferrersP, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz, regularizedGaussHGFun_eq_div_Gamma hc,
    show (1 - 1/2 : ℂ) = 1/2 by norm_num, show -ν = 1 - (ν+1) by ring,
    show ((1:ℂ) - (Real.cos θ:ℝ))/2 = (Real.sin t:ℂ)^2 by rw [hcos]; push_cast; ring,
    sin_sq_cos_quotient (ν+1) habs, legendre_Gamma_one_half]
  have hr : (1+Real.cos θ)/(1-Real.cos θ) = (Real.cos t/Real.sin t)^2 := by
    rw [hcos, div_pow, Real.cos_sq']; field_simp; ring
  have hR : (2:ℂ)/(π*Real.sin θ) = ((1/(π*Real.sin t*Real.cos t) : ℝ) : ℂ) := by
    rw [hsin]; push_cast; field_simp
  have hpi : ((Real.sqrt π : ℝ) : ℂ) = exp ((Real.log π : ℂ)/2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos Real.pi_pos, ofReal_exp]; push_cast; ring_nf
  have hC : ((Real.cos t : ℝ) : ℂ) = exp (Real.log (Real.cos t) : ℂ) := by
    rw [← ofReal_exp, Real.exp_log hct]
  rw [hr, hR, ofReal_cpow_eq_exp (by positivity), ofReal_cpow_eq_exp (by positivity), hpi, hC,
    Real.log_pow, Real.log_div hct.ne' hst.ne', one_div (π * Real.sin t * Real.cos t), Real.log_inv,
    Real.log_mul (by positivity) hct.ne', Real.log_mul Real.pi_pos.ne' hst.ne',
    show ((ν+1/2)*(θ:ℂ)) = (2*(ν+1)-1)*(t:ℂ) by rw [hθ]; push_cast; ring]
  have e : ∀ (A B C D : ℂ), exp A * (D / exp B / exp C) = exp (A - B - C) * D := by
    intros; rw [exp_sub, exp_sub]; field_simp
  rw [e, div_one]
  congr 2
  push_cast; ring

/-- DLMF 14.5.12: for `0 < θ < π`, `𝖯^{-1/2}_ν(cos θ) = (2/(π sin θ))^{1/2} sin((ν+1/2)θ)/(ν+1/2)`,
with the limiting value `(2/(π sin θ))^{1/2} θ` at `ν = -1/2`. -/
@[dlmf 14.5.E12]
theorem ferrersP_half_order_12 (ν : ℂ) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersP ν (-1/2) (Real.cos θ)=if ν=-1/2 then (2/(π*Real.sin θ):ℂ)^(1/2:ℂ)*θ else (2/(π*Real.sin θ):ℂ)^(1/2:ℂ)*sin ((ν+1/2)*θ)/(ν+1/2) := by
  set t := θ/2 with ht
  have ht0 : 0 < t := by positivity
  have htπ : t < π/2 := by linarith
  have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith)
  have hct : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith, htπ⟩
  have hθ : θ = 2*t := by rw [ht]; ring
  have hcos : Real.cos θ = 1 - 2*Real.sin t^2 := by rw [hθ, Real.cos_two_mul, Real.cos_sq']; ring
  have hsin : Real.sin θ = 2*Real.sin t*Real.cos t := by rw [hθ, Real.sin_two_mul]
  have habs : |t| < π/2 := by rw [abs_of_pos ht0]; exact htπ
  have hsq1 : Real.sin t^2 < 1 := by
    have := Real.sin_sq_add_cos_sq t; nlinarith
  have hz : ‖((1:ℂ) - (Real.cos θ:ℝ))/2‖ < 1 := by
    rw [hcos, show ((1:ℂ) - ((1 - 2*Real.sin t^2 : ℝ) : ℂ))/2 = ((Real.sin t^2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hsq1
  have hc : ∀ k : ℕ, (1 - -1/2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [ferrersP, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz, regularizedGaussHGFun_eq_div_Gamma hc,
    show (1 - -1/2 : ℂ) = 3/2 by norm_num, show -ν = 1 - (ν+1) by ring,
    show ((1:ℂ) - (Real.cos θ:ℝ))/2 = (Real.sin t:ℂ)^2 by rw [hcos]; push_cast; ring,
    legendre_Gamma_three_halves]
  -- the common prefactor
  have hK : (((1+Real.cos θ)/(1-Real.cos θ) : ℝ) : ℂ)^((-1/2:ℂ)/2) / ((Real.sqrt π : ℂ)/2) =
      2 * Real.sin t * (2/(π*Real.sin θ):ℂ)^(1/2:ℂ) := by
    have hr : (1+Real.cos θ)/(1-Real.cos θ) = (Real.cos t/Real.sin t)^2 := by
      rw [hcos, div_pow, Real.cos_sq']; field_simp; ring
    have hR : (2:ℂ)/(π*Real.sin θ) = ((1/(π*Real.sin t*Real.cos t) : ℝ) : ℂ) := by
      rw [hsin]; push_cast; field_simp
    have hpi : ((Real.sqrt π : ℝ) : ℂ) = exp ((Real.log π : ℂ)/2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos Real.pi_pos, ofReal_exp]; push_cast; ring_nf
    have hS : ((Real.sin t : ℝ) : ℂ) = exp (Real.log (Real.sin t) : ℂ) := by
      rw [← ofReal_exp, Real.exp_log hst]
    rw [hr, hR, ofReal_cpow_eq_exp (by positivity), ofReal_cpow_eq_exp (by positivity), hpi, hS,
      Real.log_pow, Real.log_div hct.ne' hst.ne', one_div (π * Real.sin t * Real.cos t), Real.log_inv,
      Real.log_mul (by positivity) hct.ne', Real.log_mul Real.pi_pos.ne' hst.ne']
    rw [div_div_eq_mul_div, mul_comm (exp _) 2, mul_div_assoc, mul_assoc, ← exp_sub, ← exp_add]
    congr 2
    push_cast; ring
  rw [mul_div_assoc', mul_comm _ (₂F₁ _ _ _ _), mul_div_assoc, hK]
  have hRne : (2/(π*Real.sin θ):ℂ)^(1/2:ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; push Not; intro h; exfalso
    have : (π:ℂ)*Real.sin θ ≠ 0 := by
      have := Real.sin_pos_of_pos_of_lt_pi h0 hπ
      exact mul_ne_zero (by exact_mod_cast Real.pi_pos.ne') (by exact_mod_cast this.ne')
    exact absurd h (div_ne_zero two_ne_zero this)
  split_ifs with hν
  · subst hν
    have hA := arcsin_eq_ordinaryHypergeometric (x := Real.sin t) (by rw [abs_of_pos hst]; nlinarith)
    have hI := ordinaryHypergeometric_half_im (x := Real.sin t) (by rw [abs_of_pos hst]; nlinarith)
    rw [Real.arcsin_sin (by linarith) htπ.le] at hA
    have hF : ₂F₁ (1/2:ℂ) (1/2) (3/2) ((Real.sin t:ℂ)^2) = (t:ℂ) / Real.sin t := by
      have hre : ₂F₁ (1/2:ℂ) (1/2) (3/2) ((Real.sin t:ℂ)^2) =
          ((₂F₁ (1/2:ℂ) (1/2) (3/2) ((Real.sin t:ℂ)^2)).re : ℂ) := by
        apply Complex.ext
        · rw [ofReal_re]
        · rw [ofReal_im]; exact hI
      have hA' : (t:ℂ) = Real.sin t * ((₂F₁ (1/2:ℂ) (1/2) (3/2) ((Real.sin t:ℂ)^2)).re : ℂ) := by
        exact_mod_cast hA
      rw [eq_div_iff (by exact_mod_cast hst.ne'), hre]
      linear_combination -hA'
    rw [show (-1/2:ℂ) + 1 = 1/2 by norm_num, show (1:ℂ) - 1/2 = 1/2 by norm_num, hF, hθ]
    have : (Real.sin t : ℂ) ≠ 0 := by exact_mod_cast hst.ne'
    field_simp
    push_cast; ring
  · have hS := sin_sq_sin (ν+1) habs
    have h2 : (2*(ν+1)-1) ≠ 0 := by
      intro h; apply hν; linear_combination h/2
    have : (Real.sin t : ℂ) ≠ 0 := by exact_mod_cast hst.ne'
    have hF : ₂F₁ (ν+1) (1-(ν+1)) (3/2) ((Real.sin t:ℂ)^2) =
        sin ((2*(ν+1)-1)*t) / ((2*(ν+1)-1) * Real.sin t) := by
      rw [eq_div_iff (mul_ne_zero h2 this)]; linear_combination hS
    have h3 : ν + 1/2 ≠ 0 := by intro h; apply h2; linear_combination 2*h
    rw [hF, show (2*(ν+1)-1)*(t:ℂ) = (ν+1/2)*θ by rw [hθ]; push_cast; ring,
      show (2*(ν+1)-1) = 2*(ν+1/2) by ring]
    field_simp

/-- DLMF 14.5.13: for `ν+1/2 ∉ {-1,-2,…}` and `0 < θ < π`, `𝖰^{1/2}_ν(cos θ) = -(π/(2 sin θ))^{1/2}
sin((ν+1/2)θ)`. -/
@[dlmf 14.5.E13]
theorem ferrersQ_half_order_13 (ν : ℂ) (h : LegendreQRegular ν (1/2)) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersQ ν (1/2) (Real.cos θ)=-(π/(2*Real.sin θ):ℂ)^(1/2:ℂ)*sin ((ν+1/2)*θ)/(1) := by
  set ph := π/2 - θ with hph
  have hphabs : |ph| < π/2 := by rw [abs_lt]; constructor <;> linarith
  have hx : Real.cos θ = Real.sin ph := by rw [hph, Real.sin_pi_div_two_sub]
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hx2 : ‖((Real.cos θ : ℝ) : ℂ)^2‖ < 1 := by
    rw [← ofReal_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := Real.sin_sq_add_cos_sq θ; nlinarith
  have hc1 : ∀ k : ℕ, (1/2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hc3 : ∀ k : ℕ, (3/2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [ferrersQ, ferrersW1, ferrersW2,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hx2, regularizedGaussHGFun_eq_div_Gamma hc1,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hx2, regularizedGaussHGFun_eq_div_Gamma hc3,
    legendre_Gamma_one_half, legendre_Gamma_three_halves]
  set b := (ν + 1/2)/2 with hb
  -- Gamma ratios
  have hG1 : Gamma ((ν + 1/2 + 1)/2) / Gamma ((ν - 1/2 + 2)/2) = 1 := by
    rw [show (ν - 1/2 + 2)/2 = (ν + 1/2 + 1)/2 by ring]
    apply div_self
    apply Complex.Gamma_ne_zero
    intro k hk
    apply h (2*k)
    push_cast; linear_combination 2*hk
  have hG2 : Gamma ((ν + 1/2 + 2)/2) / Gamma ((ν - 1/2 + 1)/2) = b := by
    rw [show (ν + 1/2 + 2)/2 = b + 1 by rw [hb]; ring, show (ν - 1/2 + 1)/2 = b by rw [hb]; ring]
    by_cases hb0 : b = 0
    · rw [hb0, zero_add, Complex.Gamma_zero, div_zero]
    · have hGb : Gamma b ≠ 0 := by
        apply Complex.Gamma_ne_zero
        intro k hk
        rcases k with _ | k
        · exact hb0 (by simpa using hk)
        · apply h (2*k+1)
          rw [hb] at hk
          push_cast at hk ⊢; linear_combination 2*hk
      rw [Complex.Gamma_add_one _ hb0]; field_simp
  have hF1 : ₂F₁ (-(ν + 1/2)/2) ((ν - 1/2 + 1)/2) (1/2) (((Real.cos θ : ℝ) : ℂ)^2) =
      cos ((ν + 1/2) * ph) := by
    rw [hx, show -(ν + 1/2)/2 = -b by rw [hb]; ring, show (ν - 1/2 + 1)/2 = b by rw [hb]; ring,
      sin_sq_cos b hphabs]; congr 1; rw [hb]; ring
  have hF2 : 2 * b * ((Real.cos θ : ℝ) : ℂ) *
      ₂F₁ ((1 - ν - 1/2)/2) ((ν - 1/2 + 2)/2) (3/2) (((Real.cos θ : ℝ) : ℂ)^2) = sin ((ν + 1/2) * ph) := by
    have hS := sin_sq_sin ((ν - 1/2 + 2)/2) hphabs
    rw [show (1:ℂ) - (ν - 1/2 + 2)/2 = (1 - ν - 1/2)/2 by ring, ordinaryHypergeometric_symm,
      show 2 * ((ν - 1/2 + 2)/2) - 1 = ν + 1/2 by ring] at hS
    rw [hx, ← hS, hb]; ring
  rw [mul_div_assoc (2 ^ (1/2:ℂ)) (Gamma ((ν + 1/2 + 1)/2)), hG1,
    mul_div_assoc (2 ^ (1/2:ℂ)) (Gamma ((ν + 1/2 + 2)/2)), hG2, hF1]
  have hsp : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hpi2 : (Real.sqrt π : ℂ)^2 = π := by rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have htrig : -(sin ((ν + 1/2) * π/2) * cos ((ν + 1/2) * ph)) + cos ((ν + 1/2) * π/2) * sin ((ν + 1/2) * ph)
      = -sin ((ν + 1/2) * θ) := by
    rw [← neg_neg (sin ((ν + 1/2) * (θ:ℂ))), ← Complex.sin_neg,
      show -((ν + 1/2) * (θ:ℂ)) = (ν + 1/2) * ph - (ν + 1/2) * π/2 by rw [hph]; push_cast; ring,
      Complex.sin_sub]; ring
  have hT : (2:ℂ)^(1/2:ℂ) * (1 - ((Real.cos θ : ℝ) : ℂ)^2)^(-(1/2:ℂ)/2) * (Real.sqrt π : ℂ) =
      2 * ((π:ℂ)/(2*Real.sin θ))^(1/2:ℂ) := by
    have h2 : (2:ℂ) = exp (Real.log 2 : ℂ) := by rw [← ofReal_exp, Real.exp_log two_pos]; norm_num
    have hpi : ((Real.sqrt π : ℝ) : ℂ) = exp ((Real.log π : ℂ)/2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos Real.pi_pos, ofReal_exp]; push_cast; ring_nf
    rw [show (1:ℂ) - ((Real.cos θ : ℝ) : ℂ)^2 = ((Real.sin θ ^ 2 : ℝ) : ℂ) by
        rw [Real.sin_sq]; push_cast; ring,
      show (π:ℂ)/(2*Real.sin θ) = ((π/(2*Real.sin θ) : ℝ) : ℂ) by push_cast; ring,
      show (2:ℂ)^(1/2:ℂ) = ((2:ℝ):ℂ)^(1/2:ℂ) by norm_num,
      ofReal_cpow_eq_exp two_pos, ofReal_cpow_eq_exp (by positivity), ofReal_cpow_eq_exp (by positivity),
      hpi, Real.log_pow, Real.log_div Real.pi_pos.ne' (by positivity), Real.log_mul two_ne_zero hs.ne']
    conv_rhs => arg 1; rw [h2]
    simp only [← exp_add]; congr 1; push_cast; ring
  set Q := (2:ℂ)^(1/2:ℂ)
  set R := (1 - ((Real.cos θ : ℝ) : ℂ)^2)^(-(1/2:ℂ)/2)
  set T := ((π:ℂ)/(2*Real.sin θ))^(1/2:ℂ)
  set F2 := ₂F₁ ((1 - ν - 1/2)/2) ((ν - 1/2 + 2)/2) (3/2) (((Real.cos θ : ℝ) : ℂ)^2)
  set sp := (Real.sqrt π : ℂ)
  have hpi' : (π:ℂ) * sp⁻¹ = sp := by rw [← hpi2]; field_simp
  linear_combination (π * Q * R * sp⁻¹ / 2) * htrig + (π * cos ((ν + 1/2) * π/2) * Q * R * sp⁻¹ / 2) * hF2
    - (sin ((ν + 1/2) * θ) / 2) * hT - (sin ((ν + 1/2) * θ) * Q * R / 2) * hpi'

/-- DLMF 14.5.14: for `ν-1/2 ∉ {-1,-2,…}` and `0 < θ < π`, `𝖰^{-1/2}_ν(cos θ) = (π/(2 sin θ))^{1/2}
cos((ν+1/2)θ)/(ν+1/2)`. -/
@[dlmf 14.5.E14]
theorem ferrersQ_half_order_14 (ν : ℂ) (h : LegendreQRegular ν (-1/2)) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersQ ν (-1/2) (Real.cos θ)=(π/(2*Real.sin θ):ℂ)^(1/2:ℂ)*cos ((ν+1/2)*θ)/(ν+1/2) := by
  set ph := π/2 - θ with hph
  have hphabs : |ph| < π/2 := by rw [abs_lt]; constructor <;> linarith
  have hx : Real.cos θ = Real.sin ph := by rw [hph, Real.sin_pi_div_two_sub]
  have hcph : Real.cos ph = Real.sin θ := by rw [hph, Real.cos_pi_div_two_sub]
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hx2 : ‖((Real.cos θ : ℝ) : ℂ)^2‖ < 1 := by
    rw [← ofReal_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := Real.sin_sq_add_cos_sq θ; nlinarith
  have hc1 : ∀ k : ℕ, (1/2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hc3 : ∀ k : ℕ, (3/2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hn : ν + 1/2 ≠ 0 := by
    intro h'; apply h 0; push_cast; linear_combination h'
  rw [ferrersQ, ferrersW1, ferrersW2,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hx2, regularizedGaussHGFun_eq_div_Gamma hc1,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hx2, regularizedGaussHGFun_eq_div_Gamma hc3,
    legendre_Gamma_one_half, legendre_Gamma_three_halves]
  set b := (ν + 1/2)/2 with hb
  have hb0 : b ≠ 0 := by rw [hb]; exact div_ne_zero hn two_ne_zero
  have hG1 : Gamma ((ν + -1/2 + 1)/2) / Gamma ((ν - -1/2 + 2)/2) = 1/b := by
    rw [show (ν + -1/2 + 1)/2 = b by rw [hb]; ring, show (ν - -1/2 + 2)/2 = b + 1 by rw [hb]; ring]
    have hGb : Gamma b ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro k hk
      apply h (2*k)
      rw [hb] at hk
      push_cast at hk ⊢; linear_combination 2*hk
    rw [Complex.Gamma_add_one _ hb0]; field_simp
  have hG2 : Gamma ((ν + -1/2 + 2)/2) / Gamma ((ν - -1/2 + 1)/2) = 1 := by
    rw [show (ν + -1/2 + 2)/2 = (ν - -1/2 + 1)/2 by ring]
    apply div_self
    apply Complex.Gamma_ne_zero
    intro k hk
    apply h (2*k+1)
    push_cast at hk ⊢; linear_combination 2*hk
  have hF1 : ₂F₁ (-(ν + -1/2)/2) ((ν - -1/2 + 1)/2) (1/2) (((Real.cos θ : ℝ) : ℂ)^2) =
      cos ((ν + 1/2) * ph) / (Real.sin θ : ℂ) := by
    have hq := sin_sq_cos_quotient ((ν - -1/2 + 1)/2) hphabs
    rw [show (1:ℂ) - (ν - -1/2 + 1)/2 = -(ν + -1/2)/2 by ring, ordinaryHypergeometric_symm,
      show 2 * ((ν - -1/2 + 1)/2) - 1 = ν + 1/2 by ring, hcph] at hq
    rw [hx, hq]
  have hF2 : (ν + 1/2) * ((Real.cos θ : ℝ) : ℂ) * (Real.sin θ : ℂ) *
      ₂F₁ ((1 - ν - -1/2)/2) ((ν - -1/2 + 2)/2) (3/2) (((Real.cos θ : ℝ) : ℂ)^2) = sin ((ν + 1/2) * ph) := by
    rw [euler_transformation_of_ne_neg_nat hc3 hx2,
      show (3/2:ℂ) - (1 - ν - -1/2)/2 - (ν - -1/2 + 2)/2 = -(1/2) by ring,
      show (3/2:ℂ) - (1 - ν - -1/2)/2 = (ν - -1/2 + 1)/2 by ring,
      show (3/2:ℂ) - (ν - -1/2 + 2)/2 = 1 - (ν - -1/2 + 1)/2 by ring]
    have hS := sin_sq_sin ((ν - -1/2 + 1)/2) hphabs
    rw [show 2 * ((ν - -1/2 + 1)/2) - 1 = ν + 1/2 by ring] at hS
    have hE : (1 - ((Real.cos θ : ℝ) : ℂ)^2)^(-(1/2):ℂ) * (Real.sin θ : ℂ) = 1 := by
      rw [show (1:ℂ) - ((Real.cos θ : ℝ) : ℂ)^2 = ((Real.sin θ ^ 2 : ℝ) : ℂ) by
        rw [Real.sin_sq]; push_cast; ring, ofReal_cpow_eq_exp (by positivity), Real.log_pow,
        show (Real.sin θ : ℂ) = exp (Real.log (Real.sin θ) : ℂ) by rw [← ofReal_exp, Real.exp_log hs],
        ← exp_add]
      push_cast; ring_nf; exact exp_zero
    rw [← hS, hx]
    rw [hx] at hE
    linear_combination ((ν + 1/2) * (Real.sin ph : ℂ) *
      ₂F₁ ((ν - -1/2 + 1)/2) (1 - (ν - -1/2 + 1)/2) (3/2) ((Real.sin ph : ℂ)^2)) * hE
  rw [mul_div_assoc ((2:ℂ) ^ (-1/2:ℂ)) (Gamma ((ν + -1/2 + 1)/2)), hG1,
    mul_div_assoc ((2:ℂ) ^ (-1/2:ℂ)) (Gamma ((ν + -1/2 + 2)/2)), hG2, hF1]
  have hsp : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hpi2 : (π:ℂ) = (Real.sqrt π : ℂ)^2 := by rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hsC : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have htrig : -(sin ((ν + -1/2) * π/2) * cos ((ν + 1/2) * ph)) + cos ((ν + -1/2) * π/2) * sin ((ν + 1/2) * ph)
      = cos ((ν + 1/2) * θ) := by
    rw [show (ν + 1/2) * (θ:ℂ) = π/2 - ((ν + 1/2) * ph - (ν + -1/2) * π/2) by rw [hph]; push_cast; ring,
      Complex.cos_pi_div_two_sub, Complex.sin_sub]; ring
  have hT : (2:ℂ)^(-1/2:ℂ) * (1 - ((Real.cos θ : ℝ) : ℂ)^2)^(-(-1/2:ℂ)/2) * (Real.sqrt π : ℂ) =
      ((π:ℂ)/(2*Real.sin θ))^(1/2:ℂ) * (Real.sin θ : ℂ) := by
    have hpi : ((Real.sqrt π : ℝ) : ℂ) = exp ((Real.log π : ℂ)/2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos Real.pi_pos, ofReal_exp]; push_cast; ring_nf
    have hS : ((Real.sin θ : ℝ) : ℂ) = exp (Real.log (Real.sin θ) : ℂ) := by
      rw [← ofReal_exp, Real.exp_log hs]
    rw [show (1:ℂ) - ((Real.cos θ : ℝ) : ℂ)^2 = ((Real.sin θ ^ 2 : ℝ) : ℂ) by
        rw [Real.sin_sq]; push_cast; ring,
      show (π:ℂ)/(2*Real.sin θ) = ((π/(2*Real.sin θ) : ℝ) : ℂ) by push_cast; ring,
      show (2:ℂ)^(-1/2:ℂ) = ((2:ℝ):ℂ)^(-1/2:ℂ) by norm_num,
      ofReal_cpow_eq_exp two_pos, ofReal_cpow_eq_exp (by positivity), ofReal_cpow_eq_exp (by positivity),
      hpi, hS, Real.log_pow, Real.log_div Real.pi_pos.ne' (by positivity), Real.log_mul two_ne_zero hs.ne']
    simp only [← exp_add]; congr 1; push_cast; ring
  have alg : ∀ (pi Q R s sp T n x F2 cB sB sA cA C : ℂ), s ≠ 0 → sp ≠ 0 → n ≠ 0 →
      n * x * s * F2 = sB → -(sA * cB) + cA * sB = C → Q * R * sp = T * s → pi = sp^2 →
      -pi/2 * sA * (Q * (2/n) * R * (cB / s / sp)) + pi/2 * cA * (Q * 1 * x * R * (F2 / (sp/2))) = T * C / n := by
    intro pi Q R s sp T n x F2 cB sB sA cA C hs hsp hn h1 h2 h3 h4
    subst h4
    field_simp
    linear_combination (sp * Q * R) * h2 + (cA * sp * Q * R) * h1 + (C) * h3
  rw [show (1:ℂ)/b = 2/(ν + 1/2) by rw [hb]; field_simp]
  exact alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsC hsp hn hF2 htrig hT hpi2

/-- DLMF 14.5.15: for `ξ > 0`, `P^{1/2}_ν(cosh ξ) = (2/(π sinh ξ))^{1/2} cosh((ν+1/2)ξ)`. -/
@[dlmf 14.5.E15]
theorem associatedP_half_order_15 (ν : ℂ) {ξ : ℝ} (hξ : 0 < ξ) :
    associatedP ν (1/2) (Real.cosh ξ)=(2/(π*Real.sinh ξ):ℂ)^(1/2:ℂ)*cosh ((ν+1/2)*ξ) := by
  set s := ξ/2 with hsdef
  set S := Real.sinh s
  set C := Real.cosh s
  have hs0 : 0 < s := by positivity
  have hS0 : 0 < S := Real.sinh_pos_iff.2 hs0
  have hC0 : 0 < C := Real.cosh_pos _
  have hcs : C^2 = 1 + S^2 := by rw [Real.cosh_sq]; ring
  have hξ2 : ξ = 2*s := by rw [hsdef]; ring
  have hcosh : Real.cosh ξ = 1 + 2*S^2 := by
    rw [hξ2, Real.cosh_two_mul, Real.cosh_sq]; ring
  have hsinh : Real.sinh ξ = 2*S*C := by rw [hξ2, Real.sinh_two_mul]
  have htanh : Real.tanh s = S / C := Real.tanh_eq_sinh_div_cosh _
  have hTlt : S / C < 1 := by
    rw [div_lt_one hC0]; nlinarith
  have hm : ‖((S/C : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; exact hTlt
  have hz : ((1:ℂ) - (Real.cosh ξ:ℝ))/2 = ((-S^2 : ℝ) : ℂ) := by rw [hcosh]; push_cast; ring
  have hcut : (((-S^2 : ℝ) : ℂ)) ∈ cutPlane := by
    rw [mem_cutPlane]; exact Or.inl (by simp only [sub_re, one_re, ofReal_re]; nlinarith)
  have hq : (((-S^2 : ℝ) : ℂ)) / ((((-S^2 : ℝ) : ℂ)) - 1) = ((S/C : ℝ) : ℂ)^2 := by
    have h1 : (1 + (S:ℂ)^2) ≠ 0 := by exact_mod_cast (by positivity : (0:ℝ) < 1 + S^2).ne'
    have h2 : (-(S:ℂ)^2 - 1) ≠ 0 := by
      intro h; apply h1; linear_combination -h
    have hC2 : (C:ℂ)^2 = 1 + (S:ℂ)^2 := by exact_mod_cast hcs
    have hCne : (C:ℂ) ≠ 0 := by exact_mod_cast hC0.ne'
    push_cast; rw [div_pow, hC2]; field_simp; ring
  have hnorm : ‖((S/C : ℝ) : ℂ)^2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hm two_ne_zero
  have hc : ∀ k : ℕ, (1 - 1/2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [associatedP, hz, regularizedGaussHG_pfaff _ _ _ hcut, hq,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hnorm, regularizedGaussHGFun_eq_div_Gamma hc,
    ordinaryHypergeometric_symm, show (1 - 1/2 : ℂ) - -ν = ν + 1/2 by ring,
    show ν + 1 = (ν + 1/2) + 1/2 by ring, show (1 - 1/2 : ℂ) = 1/2 by norm_num, even_binomial _ hm,
    legendre_Gamma_one_half]
  have hp : (Real.cosh ξ : ℂ) + 1 = ((2*C^2 : ℝ) : ℂ) := by rw [hcosh, hcs]; push_cast; ring
  have hm1 : (Real.cosh ξ : ℂ) - 1 = ((2*S^2 : ℝ) : ℂ) := by rw [hcosh]; push_cast; ring
  have h1 : (1:ℂ) - ((-S^2:ℝ):ℂ) = ((C^2:ℝ):ℂ) := by rw [hcs]; push_cast; ring
  have hTp : (1:ℂ) + ((S/C:ℝ):ℂ) = ((Real.exp s / C : ℝ) : ℂ) := by
    have hCne : (C:ℂ) ≠ 0 := by exact_mod_cast hC0.ne'
    rw [← Real.cosh_add_sinh]; change _ = (((C + S)/C : ℝ):ℂ); push_cast; field_simp
  have hTm : (1:ℂ) - ((S/C:ℝ):ℂ) = ((Real.exp (-s) / C : ℝ) : ℂ) := by
    have hCne : (C:ℂ) ≠ 0 := by exact_mod_cast hC0.ne'
    rw [← Real.cosh_sub_sinh]; change _ = (((C - S)/C : ℝ):ℂ); push_cast; field_simp
  have hR : (2:ℂ)/(π*Real.sinh ξ) = ((1/(π*S*C) : ℝ) : ℂ) := by
    rw [hsinh]; push_cast; field_simp
  have hpi : ((Real.sqrt π : ℝ) : ℂ) = exp ((Real.log π : ℂ)/2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos Real.pi_pos, ofReal_exp]; push_cast; ring_nf
  rw [hp, hm1, h1, hTp, hTm, hR, hpi, ← ofReal_log (by positivity), ← ofReal_log (by positivity),
    ofReal_cpow_eq_exp (by positivity), ofReal_cpow_eq_exp (by positivity),
    ofReal_cpow_eq_exp (by positivity), ofReal_cpow_eq_exp (by positivity),
    Real.log_mul two_ne_zero (by positivity), Real.log_mul two_ne_zero (by positivity),
    Real.log_pow, Real.log_pow, Real.log_div (Real.exp_pos _).ne' hC0.ne', Real.log_div (Real.exp_pos _).ne' hC0.ne',
    Real.log_exp, Real.log_exp, one_div (π*S*C), Real.log_inv,
    Real.log_mul (by positivity) hC0.ne', Real.log_mul Real.pi_pos.ne' hS0.ne', Complex.cosh, hξ2]
  have key : ∀ x y z u v w : ℂ, x + y + z = u + v + w →
      exp x * exp y * exp z = exp u * exp v * exp w := by
    intro x y z u v w h; rw [← exp_add, ← exp_add, ← exp_add, ← exp_add, h]
  set Ea := cexp (1 / 2 / 2 * (((Real.log 2 + ((2:ℕ):ℝ) * Real.log C : ℝ) : ℂ) - ((Real.log 2 + ((2:ℕ):ℝ) * Real.log S : ℝ) : ℂ)))
  set Eb := cexp (((((2:ℕ):ℝ) * Real.log C : ℝ) : ℂ) * -(ν + 1 / 2 + 1 / 2))
  set Ec := cexp (((s - Real.log C : ℝ) : ℂ) * (-2 * (ν + 1 / 2)))
  set Ed := cexp (((-s - Real.log C : ℝ) : ℂ) * (-2 * (ν + 1 / 2)))
  set Ee := cexp ((Real.log π : ℂ) / 2)
  set Ef := cexp (((-(Real.log π + Real.log S + Real.log C)) : ℝ) * (1 / 2 : ℂ))
  set Eg := cexp ((ν + 1 / 2) * ((2 * s : ℝ) : ℂ))
  set Eh := cexp (-((ν + 1 / 2) * ((2 * s : ℝ) : ℂ)))
  have k1 : Ea * Eb * Ec = Ef * Eh * Ee := key _ _ _ _ _ _ (by push_cast; ring)
  have k2 : Ea * Eb * Ed = Ef * Eg * Ee := key _ _ _ _ _ _ (by push_cast; ring)
  have hEe : Ee ≠ 0 := exp_ne_zero _
  rw [show Ea * (Eb * ((Ec + Ed)/2/Ee)) = (Ea*Eb*Ec + Ea*Eb*Ed)/(2*Ee) by ring, k1, k2,
    div_eq_iff (mul_ne_zero two_ne_zero hEe)]
  ring

/-- DLMF 14.5.16: for `ξ > 0`, `P^{-1/2}_ν(cosh ξ) = (2/(π sinh ξ))^{1/2} sinh((ν+1/2)ξ)/(ν+1/2)`,
with the limiting value `(2/(π sinh ξ))^{1/2} ξ` at `ν = -1/2`. -/
@[dlmf 14.5.E16]
theorem associatedP_half_order_16 (ν : ℂ) {ξ : ℝ} (hξ : 0 < ξ) :
    associatedP ν (-1/2) (Real.cosh ξ)=if ν=-1/2 then (2/(π*Real.sinh ξ):ℂ)^(1/2:ℂ)*ξ else (2/(π*Real.sinh ξ):ℂ)^(1/2:ℂ)*sinh ((ν+1/2)*ξ)/(ν+1/2) := by
  set s := ξ/2 with hsdef
  set S := Real.sinh s
  set C := Real.cosh s
  have hs0 : 0 < s := by positivity
  have hS0 : 0 < S := Real.sinh_pos_iff.2 hs0
  have hC0 : 0 < C := Real.cosh_pos _
  have hcs : C^2 = 1 + S^2 := by rw [Real.cosh_sq]; ring
  have hξ2 : ξ = 2*s := by rw [hsdef]; ring
  have hcosh : Real.cosh ξ = 1 + 2*S^2 := by
    rw [hξ2, Real.cosh_two_mul, Real.cosh_sq]; ring
  have hsinh : Real.sinh ξ = 2*S*C := by rw [hξ2, Real.sinh_two_mul]
  have htanh : Real.tanh s = S / C := Real.tanh_eq_sinh_div_cosh _
  have hTlt : S / C < 1 := by
    rw [div_lt_one hC0]; nlinarith
  have hm : ‖((S/C : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; exact hTlt
  have hz : ((1:ℂ) - (Real.cosh ξ:ℝ))/2 = ((-S^2 : ℝ) : ℂ) := by rw [hcosh]; push_cast; ring
  have hcut : (((-S^2 : ℝ) : ℂ)) ∈ cutPlane := by
    rw [mem_cutPlane]; exact Or.inl (by simp only [sub_re, one_re, ofReal_re]; nlinarith)
  have hq : (((-S^2 : ℝ) : ℂ)) / ((((-S^2 : ℝ) : ℂ)) - 1) = ((S/C : ℝ) : ℂ)^2 := by
    have h1 : (1 + (S:ℂ)^2) ≠ 0 := by exact_mod_cast (by positivity : (0:ℝ) < 1 + S^2).ne'
    have h2 : (-(S:ℂ)^2 - 1) ≠ 0 := by
      intro h; apply h1; linear_combination -h
    have hC2 : (C:ℂ)^2 = 1 + (S:ℂ)^2 := by exact_mod_cast hcs
    have hCne : (C:ℂ) ≠ 0 := by exact_mod_cast hC0.ne'
    push_cast; rw [div_pow, hC2]; field_simp; ring
  have hnorm : ‖((S/C : ℝ) : ℂ)^2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hm two_ne_zero
  have hc : ∀ k : ℕ, (1 - -1/2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [associatedP, hz, regularizedGaussHG_pfaff _ _ _ hcut, hq,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hnorm, regularizedGaussHGFun_eq_div_Gamma hc,
    show (1 - -1/2 : ℂ) - -ν = (ν + 1) + 1/2 by ring, show (1 - -1/2 : ℂ) = 3/2 by norm_num,
    legendre_Gamma_three_halves]
  have hp : (Real.cosh ξ : ℂ) + 1 = ((2*C^2 : ℝ) : ℂ) := by rw [hcosh, hcs]; push_cast; ring
  have hm1 : (Real.cosh ξ : ℂ) - 1 = ((2*S^2 : ℝ) : ℂ) := by rw [hcosh]; push_cast; ring
  have h1 : (1:ℂ) - ((-S^2:ℝ):ℂ) = ((C^2:ℝ):ℂ) := by rw [hcs]; push_cast; ring
  have hCne : (C:ℂ) ≠ 0 := by exact_mod_cast hC0.ne'
  have hTp : (1:ℂ) + ((S/C:ℝ):ℂ) = ((Real.exp s / C : ℝ) : ℂ) := by
    rw [← Real.cosh_add_sinh]; change _ = (((C + S)/C : ℝ):ℂ); push_cast; field_simp
  have hTm : (1:ℂ) - ((S/C:ℝ):ℂ) = ((Real.exp (-s) / C : ℝ) : ℂ) := by
    rw [← Real.cosh_sub_sinh]; change _ = (((C - S)/C : ℝ):ℂ); push_cast; field_simp
  have hR : (2:ℂ)/(π*Real.sinh ξ) = ((1/(π*S*C) : ℝ) : ℂ) := by
    rw [hsinh]; push_cast; field_simp
  have hpi : ((Real.sqrt π : ℝ) : ℂ) = exp ((Real.log π : ℂ)/2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos Real.pi_pos, ofReal_exp]; push_cast; ring_nf
  have hT : ((S/C:ℝ):ℂ) = exp ((Real.log S - Real.log C : ℝ) : ℂ) := by
    rw [← ofReal_exp, ← Real.log_div hS0.ne' hC0.ne', Real.exp_log (by positivity)]
  have key : ∀ x y z t u v w : ℂ, x + y + z - t = u + v + w →
      exp x * exp y * exp z / exp t = exp u * exp v * exp w := by
    intro x y z t u v w h; rw [← exp_add, ← exp_add, ← exp_sub, ← exp_add, ← exp_add, h]
  rw [hp, hm1, h1, hR, hpi, ← ofReal_log (by positivity), ← ofReal_log (by positivity),
    ofReal_cpow_eq_exp (by positivity), ofReal_cpow_eq_exp (by positivity),
    Real.log_mul two_ne_zero (by positivity), Real.log_mul two_ne_zero (by positivity),
    Real.log_pow, Real.log_pow, one_div (π*S*C), Real.log_inv,
    Real.log_mul (by positivity) hC0.ne', Real.log_mul Real.pi_pos.ne' hS0.ne']
  have hEe : cexp ((Real.log π : ℂ)/2) ≠ 0 := exp_ne_zero _
  split_ifs with hν
  · subst hν
    have hL := log_ratio hm
    rw [hTp, hTm, ← ofReal_div, div_div_div_cancel_right₀ hC0.ne', ← Real.exp_sub,
      ← ofReal_log (Real.exp_pos _).le, Real.log_exp] at hL
    rw [show (-1/2:ℂ) + 1 = 1/2 by norm_num, show (1/2:ℂ) + 1/2 = 1 by norm_num]
    have hF : ₂F₁ (1/2:ℂ) 1 (3/2) (((S/C:ℝ):ℂ)^2) = (s:ℂ) / ((S/C:ℝ):ℂ) := by
      have hTne : ((S/C:ℝ):ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0:ℝ) < S/C).ne'
      rw [eq_div_iff hTne]; push_cast at hL ⊢; linear_combination hL/2
    rw [hF, hT, hξ2, show ((2*s:ℝ):ℂ) = 2*(s:ℂ) by push_cast; ring]
    have alg : ∀ a b t e f s : ℂ, t ≠ 0 → e ≠ 0 → a*b = f*t*e → a*(b*(s/t/(e/2))) = f*(2*s) := by
      intro a b t e f s ht he h; field_simp; linear_combination s*h
    refine alg _ _ _ _ _ _ (exp_ne_zero _) (exp_ne_zero _) ?_
    rw [← exp_add, ← exp_add, ← exp_add]; congr 1; push_cast; ring
  · have hn : ν + 1/2 ≠ 0 := by intro h; apply hν; linear_combination h
    have hO := odd_binomial (ν+1) hm
    rw [hTp, hTm, ofReal_cpow_eq_exp (by positivity), ofReal_cpow_eq_exp (by positivity),
      Real.log_div (Real.exp_pos _).ne' hC0.ne', Real.log_div (Real.exp_pos _).ne' hC0.ne',
      Real.log_exp, Real.log_exp] at hO
    have alg : ∀ a b e f F P M g h k T n : ℂ, n ≠ 0 → e ≠ 0 → T ≠ 0 → k = -4*n → k*T*F = P - M →
        a*b*P = f*h*T*e → a*b*M = f*g*T*e → a*(b*(F/(e/2))) = f*((g - h)/2)/n := by
      intro a b e f F P M g h k T n hn he hT hk hF h1 h2
      subst hk
      have hF' : F = (P - M)/(-4*n*T) := by
        rw [eq_div_iff (by simp [hn, hT])]; linear_combination hF
      rw [hF']
      field_simp
      linear_combination (-4) * h1 + 4 * h2
    rw [Complex.sinh]
    refine alg _ _ _ _ _ _ _ _ _ _ _ _ hn hEe (by rw [hT]; exact exp_ne_zero _) (by ring) hO ?_ ?_
    · rw [hT, hξ2]; simp only [← exp_add]; congr 1; push_cast; ring
    · rw [hT, hξ2]; simp only [← exp_add]; congr 1; push_cast; ring

/-- DLMF 14.5.17 (order `+1/2`): for `ξ > 0`, `𝑸^{1/2}_ν(cosh ξ) = (π/(2 sinh ξ))^{1/2}
e^{-(ν+1/2)ξ}/Γ(ν+3/2)`. -/
@[dlmf 14.5.E17]
theorem olverQ_half_order_1 (ν : ℂ) {ξ : ℝ} (hξ : 0 < ξ) :
    olverQ ν (1/2) (Real.cosh ξ)=(π/(2*Real.sinh ξ):ℂ)^(1/2:ℂ)*exp (-(ν+1/2)*ξ)/Gamma (ν+3/2) := by
  set Z := Real.cosh ξ
  set Sh := Real.sinh ξ
  have hZ1 : 1 < Z := Real.one_lt_cosh.2 hξ.ne'
  have hZ0 : 0 < Z := by linarith
  have hS0 : 0 < Sh := Real.sinh_pos_iff.2 hξ
  have hZS : Z^2 = 1 + Sh^2 := by rw [Real.cosh_sq]; ring
  have hSZ : Sh < Z := by nlinarith
  have hw : ‖(1:ℂ)/(Z:ℂ)^2‖ < 1 := by
    rw [show (1:ℂ)/(Z:ℂ)^2 = ((1/Z^2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity), div_lt_one (by positivity)]; nlinarith
  rw [olverQ, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw,
    show (ν + 1/2 + 2)/2 = (ν+3/2)/2 + 1/2 by ring, show (ν + 1/2 + 1)/2 = (ν+3/2)/2 by ring]
  by_cases hc : ∀ k : ℕ, ν + 3/2 ≠ -(k:ℂ)
  · have hq := quadratic_binomial_derivative (a := (ν+3/2)/2)
      (by rw [show 2*((ν+3/2)/2) = ν+3/2 by ring]; exact hc) hw
    rw [show 2*((ν+3/2)/2) = ν+3/2 by ring] at hq
    rw [regularizedGaussHGFun_eq_div_Gamma hc, ordinaryHypergeometric_symm, hq]
    have hZne : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ0.ne'
    have h1w : (1:ℂ) - 1/(Z:ℂ)^2 = (((Sh/Z)^2 : ℝ) : ℂ) := by
      have : ((Z:ℂ))^2 = 1 + (Sh:ℂ)^2 := by exact_mod_cast hZS
      push_cast; field_simp; linear_combination this
    have hSZ0 : 0 < Sh/Z := by positivity
    have hsq : (1 - 1/(Z:ℂ)^2)^(1/2:ℂ) = ((Sh/Z : ℝ) : ℂ) := by
      rw [h1w, ofReal_cpow_eq_exp (by positivity), Real.log_pow,
        show (((2:ℕ) * Real.log (Sh/Z) : ℝ) : ℂ) * (1/2) = (Real.log (Sh/Z) : ℂ) by push_cast; ring,
        ← ofReal_exp, Real.exp_log hSZ0]
    have hsqm : (1 - 1/(Z:ℂ)^2)^(-(1/2):ℂ) = exp (-((Real.log Sh - Real.log Z : ℝ) : ℂ)) := by
      rw [h1w, ofReal_cpow_eq_exp (by positivity), Real.log_pow, Real.log_div hS0.ne' hZ0.ne']
      congr 1; push_cast; ring
    have hhalf : (1 + ((Sh/Z : ℝ) : ℂ))/2 = ((Real.exp ξ / (2*Z) : ℝ) : ℂ) := by
      rw [← Real.cosh_add_sinh]; change _ = (((Z + Sh)/(2*Z) : ℝ):ℂ); push_cast; field_simp
    have hBP : legendreBranchPower (1/2) (Z:ℂ) = exp ((1/2)/2 * (2 * (Real.log Sh : ℂ))) := by
      rw [legendreBranchPower, show (Z:ℂ) - 1 = ((Z - 1 : ℝ) : ℂ) by push_cast; ring,
        show (Z:ℂ) + 1 = ((Z + 1 : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_log (by linarith), ← ofReal_log (by linarith), ← ofReal_add,
        ← Real.log_mul (by linarith) (by linarith),
        show (Z - 1)*(Z + 1) = Sh^2 by nlinarith [hZS], Real.log_pow]
      push_cast; ring_nf
    have hpi : ((Real.sqrt π : ℝ) : ℂ) = exp ((Real.log π : ℂ)/2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos Real.pi_pos, ofReal_exp]; push_cast; ring_nf
    rw [hsq, hsqm, hhalf, hBP, hpi, ofReal_cpow_eq_exp (r := Real.exp ξ / (2*Z)) (by positivity),
      show (2:ℂ)^(ν+1) = ((2:ℝ):ℂ)^(ν+1) by norm_num, ofReal_cpow_eq_exp two_pos, ofReal_cpow_eq_exp hZ0,
      show ((π:ℝ):ℂ) / (2 * (Sh:ℂ)) = ((π / (2*Sh) : ℝ) : ℂ) by push_cast; ring,
      ofReal_cpow_eq_exp (r := π / (2*Sh)) (by positivity),
      Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_mul two_ne_zero hZ0.ne', Real.log_exp,
      Real.log_div Real.pi_pos.ne' (by positivity), Real.log_mul two_ne_zero hS0.ne']
    have alg : ∀ e1 e2 e3 e4 e5 e6 e7 e8 G : ℂ, e3 ≠ 0 → e4 ≠ 0 →
        e1*e2*e5*e6 = e7*e8*e3*e4 → e1*e2/(e3*e4)*(e5*e6/G) = e7*e8/G := by
      intro e1 e2 e3 e4 e5 e6 e7 e8 G h3 h4 h
      by_cases hG : G = 0
      · simp [hG]
      field_simp; linear_combination h
    refine alg _ _ _ _ _ _ _ _ _ (exp_ne_zero _) (exp_ne_zero _) ?_
    simp only [← exp_add]; congr 1; push_cast; ring
  · push Not at hc
    obtain ⟨n, hn⟩ := hc
    have hG : Gamma (ν + 3/2) = 0 := by rw [hn]; exact Complex.Gamma_neg_nat_eq_zero n
    rw [hG, div_zero, ← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw, hn,
      regularizedGaussHG_neg_nat _ _ _ (mem_cutPlane_of_norm_lt_one hw)]
    have hν : ν = -(n:ℂ) - 3/2 := by linear_combination hn
    rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
    · have : -(n:ℂ)/2 = -(j:ℂ) := by rw [hj]; push_cast; ring
      rw [this, poch_neg_nat_eq_zero (by omega : j < n + 1)]; simp
    · have : -(n:ℂ)/2 + 1/2 = -(j:ℂ) := by rw [hj]; push_cast; ring
      rw [this, poch_neg_nat_eq_zero (by omega : j < n + 1)]; simp

/-- DLMF 14.5.17 (order `-1/2`): for `ξ > 0`, `𝑸^{-1/2}_ν(cosh ξ) = (π/(2 sinh ξ))^{1/2}
e^{-(ν+1/2)ξ}/Γ(ν+3/2)`. -/
@[dlmf 14.5.E17]
theorem olverQ_half_order_2 (ν : ℂ) {ξ : ℝ} (hξ : 0 < ξ) :
    olverQ ν (-1/2) (Real.cosh ξ)=(π/(2*Real.sinh ξ):ℂ)^(1/2:ℂ)*exp (-(ν+1/2)*ξ)/Gamma (ν+3/2) := by
  set Z := Real.cosh ξ
  set Sh := Real.sinh ξ
  have hZ1 : 1 < Z := Real.one_lt_cosh.2 hξ.ne'
  have hZ0 : 0 < Z := by linarith
  have hS0 : 0 < Sh := Real.sinh_pos_iff.2 hξ
  have hZS : Z^2 = 1 + Sh^2 := by rw [Real.cosh_sq]; ring
  have hSZ : Sh < Z := by nlinarith
  have hw : ‖(1:ℂ)/(Z:ℂ)^2‖ < 1 := by
    rw [show (1:ℂ)/(Z:ℂ)^2 = ((1/Z^2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity), div_lt_one (by positivity)]; nlinarith
  rw [olverQ, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw,
    show (ν + -1/2 + 2)/2 = (ν+1/2)/2 + 1/2 by ring, show (ν + -1/2 + 1)/2 = (ν+1/2)/2 by ring]
  by_cases hc : ∀ k : ℕ, ν + 3/2 ≠ -(k:ℂ)
  · have hq := quadratic_binomial (a := (ν+1/2)/2)
      (by rw [show 1 + 2*((ν+1/2)/2) = ν+3/2 by ring]; exact hc) hw
    rw [show 1 + 2*((ν+1/2)/2) = ν+3/2 by ring] at hq
    rw [regularizedGaussHGFun_eq_div_Gamma hc, ordinaryHypergeometric_symm, hq]
    have hZne : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ0.ne'
    have h1w : (1:ℂ) - 1/(Z:ℂ)^2 = (((Sh/Z)^2 : ℝ) : ℂ) := by
      have : ((Z:ℂ))^2 = 1 + (Sh:ℂ)^2 := by exact_mod_cast hZS
      push_cast; field_simp; linear_combination this
    have hSZ0 : 0 < Sh/Z := by positivity
    have hsq : (1 - 1/(Z:ℂ)^2)^(1/2:ℂ) = ((Sh/Z : ℝ) : ℂ) := by
      rw [h1w, ofReal_cpow_eq_exp (by positivity), Real.log_pow,
        show (((2:ℕ) * Real.log (Sh/Z) : ℝ) : ℂ) * (1/2) = (Real.log (Sh/Z) : ℂ) by push_cast; ring,
        ← ofReal_exp, Real.exp_log hSZ0]
    have hsqm : (1 - 1/(Z:ℂ)^2)^(-(1/2):ℂ) = exp (-((Real.log Sh - Real.log Z : ℝ) : ℂ)) := by
      rw [h1w, ofReal_cpow_eq_exp (by positivity), Real.log_pow, Real.log_div hS0.ne' hZ0.ne']
      congr 1; push_cast; ring
    have hhalf : (1 + ((Sh/Z : ℝ) : ℂ))/2 = ((Real.exp ξ / (2*Z) : ℝ) : ℂ) := by
      rw [← Real.cosh_add_sinh]; change _ = (((Z + Sh)/(2*Z) : ℝ):ℂ); push_cast; field_simp
    have hBP : legendreBranchPower (-1/2) (Z:ℂ) = exp ((-1/2)/2 * (2 * (Real.log Sh : ℂ))) := by
      rw [legendreBranchPower, show (Z:ℂ) - 1 = ((Z - 1 : ℝ) : ℂ) by push_cast; ring,
        show (Z:ℂ) + 1 = ((Z + 1 : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_log (by linarith), ← ofReal_log (by linarith), ← ofReal_add,
        ← Real.log_mul (by linarith) (by linarith),
        show (Z - 1)*(Z + 1) = Sh^2 by nlinarith [hZS], Real.log_pow]
      push_cast; ring_nf
    have hpi : ((Real.sqrt π : ℝ) : ℂ) = exp ((Real.log π : ℂ)/2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos Real.pi_pos, ofReal_exp]; push_cast; ring_nf
    rw [hsq, hhalf, hBP, hpi, ofReal_cpow_eq_exp (r := Real.exp ξ / (2*Z)) (by positivity),
      show (2:ℂ)^(ν+1) = ((2:ℝ):ℂ)^(ν+1) by norm_num, ofReal_cpow_eq_exp two_pos, ofReal_cpow_eq_exp hZ0,
      show ((π:ℝ):ℂ) / (2 * (Sh:ℂ)) = ((π / (2*Sh) : ℝ) : ℂ) by push_cast; ring,
      ofReal_cpow_eq_exp (r := π / (2*Sh)) (by positivity),
      Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_mul two_ne_zero hZ0.ne', Real.log_exp,
      Real.log_div Real.pi_pos.ne' (by positivity), Real.log_mul two_ne_zero hS0.ne']
    have alg : ∀ e1 e2 e3 e4 e6 e7 e8 G : ℂ, e3 ≠ 0 → e4 ≠ 0 →
        e1*e2*e6 = e7*e8*e3*e4 → e1*e2/(e3*e4)*(e6/G) = e7*e8/G := by
      intro e1 e2 e3 e4 e6 e7 e8 G h3 h4 h
      by_cases hG : G = 0
      · simp [hG]
      field_simp; linear_combination h
    refine alg _ _ _ _ _ _ _ _ (exp_ne_zero _) (exp_ne_zero _) ?_
    simp only [← exp_add]; congr 1; push_cast; ring
  · push Not at hc
    obtain ⟨n, hn⟩ := hc
    have hG : Gamma (ν + 3/2) = 0 := by rw [hn]; exact Complex.Gamma_neg_nat_eq_zero n
    rw [hG, div_zero, ← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw, hn,
      regularizedGaussHG_neg_nat _ _ _ (mem_cutPlane_of_norm_lt_one hw)]
    have hν : ν = -(n:ℂ) - 3/2 := by linear_combination hn
    rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
    · have : (ν + 1/2)/2 + 1/2 = -(j:ℂ) := by rw [hν, hj]; push_cast; ring
      rw [this, poch_neg_nat_eq_zero (by omega : j < n + 1)]; simp
    · have : (ν + 1/2)/2 = -((j+1:ℕ):ℂ) := by rw [hν, hj]; push_cast; ring
      rw [this, poch_neg_nat_eq_zero (by omega : j + 1 < n + 1)]; simp

/-- DLMF 14.5.18: for `0 < θ < π`, `𝖯^{-ν}_ν(cos θ) = (sin θ)^ν/(2^ν Γ(ν+1))`. -/
@[dlmf 14.5.E18]
theorem ferrersP_negative_degree_order (ν : ℂ) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersP ν (-ν) (Real.cos θ)=(Real.sin θ:ℂ)^ν/(2^ν*Gamma (ν+1)) := by
  set x := Real.cos θ with hxdef
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hx1 : -1 < x := by rw [← Real.cos_pi]; exact Real.cos_lt_cos_of_nonneg_of_le_pi h0.le le_rfl hπ
  have hx2 : x < 1 := by rw [← Real.cos_zero]; exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hπ.le h0
  have hz : ‖((1:ℂ) - x)/2‖ < 1 := by
    rw [show ((1:ℂ) - x)/2 = (((1-x)/2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  rw [ferrersP, show 1 - -ν = ν + 1 by ring, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
  by_cases hc : ∀ k : ℕ, ν + 1 ≠ -(k:ℂ)
  · rw [regularizedGaussHGFun_eq_div_Gamma hc, ordinaryHypergeometric_symm,
      ordinaryHypergeometric_eq_one_sub_neg_cpow (fun k h => hc k (by rw [h, neg_neg])) hz,
      neg_neg]
    have h1 : 0 < 1 + x := by linarith
    have h2 : 0 < 1 - x := by linarith
    rw [show (1:ℂ) - (1 - x)/2 = (((1+x)/2 : ℝ) : ℂ) by push_cast; ring,
      ofReal_cpow_eq_exp (div_pos h1 h2), ofReal_cpow_eq_exp (by positivity),
      show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, ofReal_cpow_eq_exp hs, ofReal_cpow_eq_exp two_pos,
      Real.log_div h1.ne' h2.ne', Real.log_div h1.ne' two_ne_zero]
    have hsin : Real.log (Real.sin θ) = (Real.log (1+x) + Real.log (1-x))/2 := by
      rw [← Real.log_mul h1.ne' h2.ne', show (1+x)*(1-x) = Real.sin θ^2 by
        rw [hxdef, Real.sin_sq]; ring, Real.log_pow]; push_cast; ring
    rw [hsin]
    have hG : Gamma (ν+1) ≠ 0 := Complex.Gamma_ne_zero (fun m h => hc m (by rw [h]))
    field_simp
    rw [← exp_add, ← exp_add]; congr 1; push_cast; ring
  · push Not at hc
    obtain ⟨k, hk⟩ := hc
    have hG : Gamma (ν+1) = 0 := by rw [hk]; exact Complex.Gamma_neg_nat_eq_zero k
    rw [hG, mul_zero, div_zero, ← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz, hk,
      regularizedGaussHG_neg_nat]
    · rw [poch_neg_nat_eq_zero (Nat.lt_succ_self k)]; simp
    · exact mem_cutPlane_of_norm_lt_one hz

/-- The degree-order balanced regularized function `𝐅(ν+1,-ν;ν+1;w) = (1-w)^ν/Γ(ν+1)`
on the cut plane, including the exceptional parameters. -/
theorem regularizedGaussHG_legendre_neg_degree (ν : ℂ) {w : ℂ} (hw : w ∈ cutPlane) :
    regularizedGaussHG (ν+1) (-ν) (ν+1) w = (1-w)^ν / Gamma (ν+1) := by
  refine eqOn_cutPlane_of_eqOn_disk (f := regularizedGaussHG (ν+1) (-ν) (ν+1))
    (g := fun w => (1-w)^ν / Gamma (ν+1)) (analyticOnNhd_regularizedGaussHG _ _ _)
    (fun w hw => ?_) (fun w hz => ?_) hw
  · exact ((analyticAt_const.sub analyticAt_id).cpow analyticAt_const hw).div_const
  · rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
    by_cases hc : ∀ k : ℕ, ν + 1 ≠ -(k:ℂ)
    · rw [regularizedGaussHGFun_eq_div_Gamma hc, ordinaryHypergeometric_symm,
        ordinaryHypergeometric_eq_one_sub_neg_cpow (fun k h => hc k (by rw [h, neg_neg])) hz, neg_neg]
    · push Not at hc
      obtain ⟨k, hk⟩ := hc
      have hG : Gamma (ν+1) = 0 := by rw [hk]; exact Complex.Gamma_neg_nat_eq_zero k
      rw [hG, div_zero, ← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz, hk,
        regularizedGaussHG_neg_nat _ _ _ (mem_cutPlane_of_norm_lt_one hz),
        poch_neg_nat_eq_zero (Nat.lt_succ_self k)]
      simp

/-- DLMF 14.5.19: for `ξ > 0`, `P^{-ν}_ν(cosh ξ) = (sinh ξ)^ν/(2^ν Γ(ν+1))`. -/
@[dlmf 14.5.E19]
theorem associatedP_negative_degree_order (ν : ℂ) {θ : ℝ} (h0 : 0 < θ) :
    associatedP ν (-ν) (Real.cosh θ)=(Real.sinh θ:ℂ)^ν/(2^ν*Gamma (ν+1)) := by
  set z := Real.cosh θ with hzdef
  have hz1 : 1 < z := Real.one_lt_cosh.2 h0.ne'
  have hs : 0 < Real.sinh θ := Real.sinh_pos_iff.2 h0
  have h1 : 0 < z + 1 := by linarith
  have h2 : 0 < z - 1 := by linarith
  have hw : ((1:ℂ) - z)/2 ∈ cutPlane := by
    rw [mem_cutPlane, show (1:ℂ) - (1 - z)/2 = (((1+z)/2 : ℝ) : ℂ) by push_cast; ring]
    exact Or.inl (by simp only [ofReal_re]; linarith)
  rw [associatedP, show 1 - -ν = ν + 1 by ring, regularizedGaussHG_legendre_neg_degree ν hw,
    show (1:ℂ) - (1 - z)/2 = (((z+1)/2 : ℝ) : ℂ) by push_cast; ring,
    show (z:ℂ) + 1 = ((z+1:ℝ):ℂ) by push_cast; ring, show (z:ℂ) - 1 = ((z-1:ℝ):ℂ) by push_cast; ring,
    ← ofReal_log h1.le, ← ofReal_log h2.le,
    ofReal_cpow_eq_exp (by positivity), show (2:ℂ) = ((2:ℝ):ℂ) by norm_num,
    ofReal_cpow_eq_exp hs, ofReal_cpow_eq_exp two_pos, Real.log_div h1.ne' two_ne_zero]
  have hsinh : Real.log (Real.sinh θ) = (Real.log (z+1) + Real.log (z-1))/2 := by
    rw [← Real.log_mul h1.ne' h2.ne', show (z+1)*(z-1) = Real.sinh θ^2 by
      rw [hzdef, Real.sinh_sq]; ring, Real.log_pow]; push_cast; ring
  rw [hsinh]
  by_cases hG : Gamma (ν+1) = 0
  · simp [hG]
  field_simp
  rw [← exp_add, ← exp_add]; congr 1; push_cast; ring

/-- The Ferrers order-zero function as a Gauss function of `sin²(θ/2)`. -/
theorem ferrersP_zero_order_sin_sq (ν : ℂ) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersP ν 0 (Real.cos θ) = ₂F₁ (ν+1) (-ν) 1 (((Real.sin (θ/2))^2 : ℝ) : ℂ) ∧
      |(Real.sin (θ/2))^2| < 1 := by
  have ht0 : 0 < θ/2 := by positivity
  have hst : 0 < Real.sin (θ/2) := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith)
  have hct : 0 < Real.cos (θ/2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcos : Real.cos θ = 1 - 2*Real.sin (θ/2)^2 := by
    rw [show θ = 2*(θ/2) by ring, Real.cos_two_mul, Real.cos_sq']; ring_nf
  have hsq1 : |(Real.sin (θ/2))^2| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    have := Real.sin_sq_add_cos_sq (θ/2); nlinarith
  refine ⟨?_, hsq1⟩
  have hz : ‖((1:ℂ) - (Real.cos θ:ℝ))/2‖ < 1 := by
    rw [hcos, show ((1:ℂ) - ((1 - 2*Real.sin (θ/2)^2 : ℝ) : ℂ))/2 = ((Real.sin (θ/2)^2 : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    exact hsq1
  have hc : ∀ k : ℕ, (1 - 0 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [ferrersP, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz, regularizedGaussHGFun_eq_div_Gamma hc,
    zero_div, cpow_zero, one_mul, sub_zero, Complex.Gamma_one, div_one,
    show ((1:ℂ) - (Real.cos θ:ℝ))/2 = ((Real.sin (θ/2)^2 : ℝ) : ℂ) by rw [hcos]; push_cast; ring]

/-- Complete elliptic integrals use parameter equal to the square of DLMF modulus. -/
@[dlmf 14.5.E20]
theorem legendre_elliptic_20 {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersP (1/2) 0 (Real.cos θ)=2/π*(2*(DLMF.Elliptic.Real.compEllIntEm ((Real.sin (θ/2))^2):ℂ)-(DLMF.Elliptic.Real.compEllIntKm ((Real.sin (θ/2))^2):ℂ)) := by
  obtain ⟨h, hm⟩ := ferrersP_zero_order_sin_sq (1/2) h0 hπ
  rw [h, DLMF.Elliptic.Real.compEllIntKm_eq_ordinaryHypergeometric hm,
    DLMF.Elliptic.Real.compEllIntEm_eq_ordinaryHypergeometric hm]
  have hz : ‖(((Real.sin (θ/2))^2 : ℝ) : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hm
  have hc : ∀ k : ℕ, (1:ℂ) ≠ -(k:ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hcon := contiguous_ab (a := (1/2:ℂ)) (b := -(1/2)) (c := 1) hc hz
  have hπ0 : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  rw [ordinaryHypergeometric_symm (-(1/2)) (1/2)]
  norm_num at hcon ⊢
  field_simp
  linear_combination 2 * hcon

/-- Complete elliptic integrals use parameter equal to the square of DLMF modulus. -/
@[dlmf 14.5.E21]
theorem legendre_elliptic_21 {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersP (-1/2) 0 (Real.cos θ)=2/π*(DLMF.Elliptic.Real.compEllIntKm ((Real.sin (θ/2))^2):ℂ) := by
  obtain ⟨h, hm⟩ := ferrersP_zero_order_sin_sq (-1/2) h0 hπ
  rw [h, DLMF.Elliptic.Real.compEllIntKm_eq_ordinaryHypergeometric hm]
  have hπ0 : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  field_simp
  norm_num

/-- `cos θ` lies in `(-1, 1)` for `0 < θ < π`. -/
private lemma cos_mem_Ioo_of_pos_of_lt_pi {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    Real.cos θ ∈ Ioo (-1:ℝ) 1 := by
  constructor
  · rw [← Real.cos_pi]; exact Real.cos_lt_cos_of_nonneg_of_le_pi h0.le le_rfl hπ
  · rw [← Real.cos_zero]; exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) h0

/-- DLMF 14.9.10 at order zero, written with the reflected angle `π - θ`. -/
private lemma ferrersQ_zero_order_connection {ν : ℂ} (hν : LegendreQRegular ν 0) {θ : ℝ}
    (h0 : 0 < θ) (hπ : θ < π) :
    2/π*sin (ν*π)*ferrersQ ν 0 (Real.cos θ) =
      cos (ν*π)*ferrersP ν 0 (Real.cos θ) - ferrersP ν 0 (Real.cos (π-θ)) := by
  have h := ferrers_connection_10 ν 0 hν (by simpa using hν) (cos_mem_Ioo_of_pos_of_lt_pi h0 hπ)
  simp only [sub_zero, neg_zero] at h
  rw [Real.cos_pi_sub]; exact h

/-- `sin((π - θ)/2) = cos(θ/2)`. -/
private lemma sin_half_pi_sub (θ : ℝ) : Real.sin ((π-θ)/2) = Real.cos (θ/2) := by
  rw [show (π-θ)/2 = π/2 - θ/2 by ring, Real.sin_pi_div_two_sub]

/-- Complete elliptic integrals use parameter equal to the square of DLMF modulus. -/
@[dlmf 14.5.E22]
theorem legendre_elliptic_22 {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersQ (1/2) 0 (Real.cos θ)=(DLMF.Elliptic.Real.compEllIntKm ((Real.cos (θ/2))^2):ℂ)-2*(DLMF.Elliptic.Real.compEllIntEm ((Real.cos (θ/2))^2):ℂ) := by
  have hr : LegendreQRegular (1/2) 0 := by
    intro n h; have := congrArg Complex.re h; simp at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  have h := ferrersQ_zero_order_connection hr h0 hπ
  rw [legendre_elliptic_20 (θ := π-θ) (by linarith) (by linarith), sin_half_pi_sub] at h
  have hs : sin ((1/2:ℂ)*π) = 1 := by
    rw [show (1/2:ℂ)*π = π/2 by ring, Complex.sin_pi_div_two]
  have hc : cos ((1/2:ℂ)*π) = 0 := by
    rw [show (1/2:ℂ)*π = π/2 by ring, Complex.cos_pi_div_two]
  rw [hs, hc] at h
  have hπ0 : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  generalize ferrersQ (1/2) 0 (Real.cos θ) = Q at h ⊢
  generalize ferrersP (1/2) 0 (Real.cos θ) = P at h
  field_simp at h
  linear_combination h/2

/-- Complete elliptic integrals use parameter equal to the square of DLMF modulus. -/
@[dlmf 14.5.E23]
theorem legendre_elliptic_23 {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersQ (-1/2) 0 (Real.cos θ)=(DLMF.Elliptic.Real.compEllIntKm ((Real.cos (θ/2))^2):ℂ) := by
  have hr : LegendreQRegular (-1/2) 0 := by
    intro n h; have := congrArg Complex.re h; simp at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  have h := ferrersQ_zero_order_connection hr h0 hπ
  rw [legendre_elliptic_21 (θ := π-θ) (by linarith) (by linarith), sin_half_pi_sub] at h
  have hs : sin ((-1/2:ℂ)*π) = -1 := by
    rw [show (-1/2:ℂ)*π = -(π/2) by ring, Complex.sin_neg, Complex.sin_pi_div_two]
  have hc : cos ((-1/2:ℂ)*π) = 0 := by
    rw [show (-1/2:ℂ)*π = -(π/2) by ring, Complex.cos_neg, Complex.cos_pi_div_two]
  rw [hs, hc] at h
  have hπ0 : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  generalize ferrersQ (-1/2) 0 (Real.cos θ) = Q at h ⊢
  generalize ferrersP (-1/2) 0 (Real.cos θ) = P at h
  field_simp at h
  linear_combination -h/2

/-- Complete elliptic integrals use parameter equal to the square of DLMF modulus. -/
@[dlmf 14.5.E24]
theorem legendre_elliptic_24 {θ : ℝ} (h0 : 0 < θ) :
    associatedP (1/2) 0 (Real.cosh θ)=2/π*Real.exp (θ/2)*(DLMF.Elliptic.Real.compEllIntEm ((Real.sqrt (1-Real.exp (-2*θ)))^2):ℂ) := by
  have hc1 : 1 < Real.cosh θ := Real.one_lt_cosh.mpr h0.ne'
  have hsl : (Real.cosh θ : ℂ) - 1 ∈ slitPlane := Or.inl (by simp; linarith)
  set m : ℝ := 1 - Real.exp (-2*θ) with hm
  have he : Real.exp (-2*θ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hm0 : 0 ≤ m := by rw [hm]; linarith
  have hm1 : m < 1 := by rw [hm]; linarith [Real.exp_pos (-2*θ)]
  rw [Real.sq_sqrt hm0, associatedP_zero_order _ hsl, legendreP_laplace _ hc1.le]
  have hsq : Real.sqrt (Real.cosh θ ^ 2 - 1) = Real.sinh θ := by
    rw [Real.cosh_sq, show Real.sinh θ ^ 2 + 1 - 1 = Real.sinh θ ^ 2 by ring,
      Real.sqrt_sq (Real.sinh_nonneg_iff.mpr h0.le)]
  have hpt : ∀ phi : ℝ, (((Real.cosh θ + Real.sqrt (Real.cosh θ ^ 2 - 1) * Real.cos phi : ℝ)) : ℂ) ^ (1/2:ℂ) =
      ((Real.exp (θ/2) * (1 - m * Real.sin (phi/2) ^ 2) ^ (1/2:ℝ) : ℝ) : ℂ) := by
    intro phi
    have hs2 : Real.sin (phi/2) ^ 2 ≤ 1 := Real.sin_sq_le_one _
    have hb : 0 ≤ 1 - m * Real.sin (phi/2) ^ 2 := by nlinarith [sq_nonneg (Real.sin (phi/2))]
    have ha : Real.cosh θ + Real.sqrt (Real.cosh θ ^ 2 - 1) * Real.cos phi =
        Real.exp θ * (1 - m * Real.sin (phi/2) ^ 2) := by
      rw [hsq, hm, Real.cosh_eq, Real.sinh_eq,
        show Real.cos phi = 1 - 2 * Real.sin (phi/2) ^ 2 by
          rw [show phi = 2*(phi/2) by ring, Real.cos_two_mul, Real.cos_sq']; ring_nf,
        show -2*θ = -θ + -θ by ring, Real.exp_add, Real.exp_neg]
      have := Real.exp_pos θ
      field_simp; ring
    rw [ha, show (1/2:ℂ) = ((1/2:ℝ):ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (mul_nonneg (Real.exp_pos θ).le hb),
      Real.mul_rpow (Real.exp_pos θ).le hb, ← Real.exp_mul, show θ * (1/2) = θ/2 by ring]
  simp_rw [hpt]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun t => (1 - m * Real.sin t ^ 2) ^ (1/2:ℝ)) two_ne_zero,
    zero_div]
  simp only [DLMF.Elliptic.Real.compEllIntEm, smul_eq_mul]
  push_cast; ring

/-- Complete elliptic integrals use parameter equal to the square of DLMF modulus. -/
@[dlmf 14.5.E25]
theorem legendre_elliptic_25 {θ : ℝ} (h0 : 0 < θ) :
    associatedP (-1/2) 0 (Real.cosh θ)=2/(π*Real.cosh (θ/2))*(DLMF.Elliptic.Real.compEllIntKm ((Real.tanh (θ/2))^2):ℂ) := by
  set s := Real.sinh (θ/2)
  set c := Real.cosh (θ/2)
  have hc0 : 0 < c := Real.cosh_pos _
  have hcs : c^2 = 1 + s^2 := by rw [Real.cosh_sq]; ring
  have hcosh : Real.cosh θ = 1 + 2*s^2 := by
    rw [show θ = 2*(θ/2) by ring, Real.cosh_two_mul, Real.cosh_sq]; ring
  have htanh : Real.tanh (θ/2) = s / c := Real.tanh_eq_sinh_div_cosh _
  have hm : |(Real.tanh (θ/2))^2| < 1 := by
    rw [abs_of_nonneg (by positivity), htanh, div_pow, div_lt_one (by positivity), hcs]; linarith
  have hz : ((1:ℂ) - (Real.cosh θ:ℝ))/2 = ((-s^2 : ℝ) : ℂ) := by rw [hcosh]; push_cast; ring
  have hcut : (((-s^2 : ℝ) : ℂ)) ∈ cutPlane := by
    rw [mem_cutPlane]; exact Or.inl (by simp only [sub_re, one_re, ofReal_re]; nlinarith)
  have hq : (((-s^2 : ℝ) : ℂ)) / ((((-s^2 : ℝ) : ℂ)) - 1) = (((Real.tanh (θ/2))^2 : ℝ) : ℂ) := by
    rw [htanh, div_pow, hcs]
    have h1 : (1 + (s:ℂ)^2) ≠ 0 := by exact_mod_cast (by positivity : (0:ℝ) < 1 + s^2).ne'
    have h2 : (-(s:ℂ)^2 - 1) ≠ 0 := by
      intro h; apply h1; linear_combination -h
    push_cast; field_simp; ring
  have hnorm : ‖(((Real.tanh (θ/2))^2 : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hm
  have hc1 : ∀ k : ℕ, (1 - 0 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [associatedP, zero_div, zero_mul, exp_zero, one_mul, hz, regularizedGaussHG_pfaff _ _ _ hcut, hq,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hnorm, regularizedGaussHGFun_eq_div_Gamma hc1,
    DLMF.Elliptic.Real.compEllIntKm_eq_ordinaryHypergeometric hm]
  have h1 : (1:ℂ) - ((-s^2:ℝ):ℂ) = ((c^2:ℝ):ℂ) := by rw [hcs]; push_cast; ring
  have hcC : (c:ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hπ0 : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hE : ((c^2:ℝ):ℂ)^(-((-1/2:ℂ)+1)) = 1/c := by
    rw [ofReal_cpow_eq_exp (by positivity), Real.log_pow, eq_div_iff hcC]
    conv_lhs => rhs; rw [show (c:ℂ) = exp (Real.log c : ℂ) by rw [← ofReal_exp, Real.exp_log hc0]]
    rw [← exp_add]; push_cast; ring_nf; exact exp_zero
  rw [h1, hE, show (1:ℂ) - 0 - -(-1/2) = 1/2 by norm_num, show (-1/2:ℂ)+1 = 1/2 by norm_num,
    sub_zero, Complex.Gamma_one]
  field_simp

/-- `₂F₁(1/2, 3/2; 2; q) = 4(K(q) - E(q))/(πq)`, from `dE/dm = (E-K)/(2m)` and DLMF 15.5.1. -/
private lemma hyp_half_three_halves_two {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ₂F₁ (1/2:ℂ) (3/2) 2 (q:ℂ) = 4/π * ((DLMF.Elliptic.Real.compEllIntKm q:ℂ) - DLMF.Elliptic.Real.compEllIntEm q)/q := by
  have hqn : ‖(q:ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have hc : ∀ k : ℕ, (1:ℂ) ≠ -k := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hd1 := (hasDerivAt_ordinaryHypergeometric (a := -(1/2)) (b := 1/2) hc hqn).comp_ofReal
  have hd2 := (DLMF.Elliptic.Real.hasDerivAt_compEllIntEm hq1 hq0.ne').ofReal_comp
  have heq : (fun m : ℝ => (DLMF.Elliptic.Real.compEllIntEm m : ℂ)) =ᶠ[𝓝 q]
      fun m : ℝ => (π/2:ℂ) * ₂F₁ (-(1/2):ℂ) (1/2) 1 (m:ℂ) := by
    have : ∀ᶠ m in 𝓝 q, |m| < 1 := by
      have : |q| < 1 := by rw [abs_of_pos hq0]; exact hq1
      exact (continuous_abs.tendsto q).eventually (gt_mem_nhds this)
    filter_upwards [this] with m hm
    exact DLMF.Elliptic.Real.compEllIntEm_eq_ordinaryHypergeometric hm
  have hd3 := (hd1.const_mul (π/2:ℂ)).congr_of_eventuallyEq heq
  have hu := hd2.unique hd3
  rw [show -(1/2:ℂ)+1 = 1/2 by norm_num, show (1/2:ℂ)+1 = 3/2 by norm_num,
    show (1:ℂ)+1 = 2 by norm_num] at hu
  have hπ : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hq : (q:ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  push_cast at hu
  field_simp at hu ⊢
  linear_combination hu

/-- Complete elliptic integrals use parameter equal to the square of DLMF modulus. -/
@[dlmf 14.5.E26]
theorem legendre_elliptic_26 {θ : ℝ} (h0 : 0 < θ) :
    olverQ (1/2) 0 (Real.cosh θ)=2/Real.sqrt π*Real.cosh θ/Real.cosh (θ/2)*(DLMF.Elliptic.Real.compEllIntKm ((1/Real.cosh (θ/2))^2):ℂ)-4/Real.sqrt π*Real.cosh (θ/2)*(DLMF.Elliptic.Real.compEllIntEm ((1/Real.cosh (θ/2))^2):ℂ) := by
  set Z := Real.cosh θ
  set k := Real.exp (-θ) with hkdef
  set q := k^2 with hqdef
  have hZ0 : 0 < Z := Real.cosh_pos _
  have hk0 : 0 < k := Real.exp_pos _
  have hk1 : k < 1 := by rw [hkdef, ← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := pow_lt_one₀ hk0.le hk1 two_ne_zero
  have hZq : Z = Real.exp θ * (1 + q) / 2 := by
    show Real.cosh θ = _
    rw [Real.cosh_eq, hqdef, hkdef, ← Real.exp_nat_mul, mul_add, mul_one, ← Real.exp_add]; push_cast; ring_nf
  have hqn : ‖(q:ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have h4 : 4 * (q:ℂ) / (1 + q)^2 = 1/(Z:ℂ)^2 := by
    have hq' : (q:ℂ) * (Real.exp θ : ℂ)^2 = 1 := by
      rw [hqdef, hkdef, ofReal_pow, ← mul_pow, ← ofReal_mul, ← Real.exp_add]; simp
    have h1q : (1 + (q:ℂ)) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < 1 + q).ne'
    have hE : (Real.exp θ : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos θ).ne'
    rw [hZq, ofReal_div, ofReal_mul, ofReal_add, ofReal_one, ofReal_ofNat]
    field_simp; linear_combination 4 * hq'
  have hw : ‖1/(Z:ℂ)^2‖ < 1 := by
    rw [show (1:ℂ)/(Z:ℂ)^2 = ((1/Z^2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity), div_lt_one (by positivity)]
    have := Real.one_lt_cosh.2 h0.ne'; nlinarith
  have hc : ∀ k : ℕ, (3/2:ℂ) - 1/2 + 1 ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hwp := quadratic_well_poised_plus hc hqn (by rw [h4]; exact hw)
  rw [h4, show (3/2:ℂ) - 1/2 + 1 = 2 by norm_num, show (3/2:ℂ)/2 = 3/4 by norm_num,
    show ((3/2:ℂ)+1)/2 = 5/4 by norm_num, ordinaryHypergeometric_symm (3/2), hyp_half_three_halves_two hq0 hq1] at hwp
  have hc1 : ∀ k : ℕ, (1/2 : ℂ) + 3/2 ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hG2 : Gamma (2:ℂ) = 1 := by simp
  rw [olverQ, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw, regularizedGaussHGFun_eq_div_Gamma hc1,
    show (1/2:ℂ) + 0 + 2 = 5/2 by norm_num, show (1/2:ℂ) + 0 + 1 = 3/2 by norm_num,
    show (5/2:ℂ)/2 = 5/4 by norm_num, show (3/2:ℂ)/2 = 3/4 by norm_num,
    show (1/2:ℂ) + 3/2 = 2 by norm_num, hG2, div_one,
    ordinaryHypergeometric_symm (5/4), legendreBranchPower, zero_div, zero_mul, exp_zero, mul_one]
  have h1q : 0 < 1 + q := by linarith
  have hpre : (1:ℂ) / ((2:ℂ)^((1/2:ℂ)+1) * (Z:ℂ)^(3/2:ℂ)) =
      (Real.exp (-3*θ/2) : ℂ) * (((1 + q : ℝ) : ℂ))^(-(3/2:ℂ)) := by
    rw [show (2:ℂ)^((1/2:ℂ)+1) = ((2:ℝ):ℂ)^(3/2:ℂ) by norm_num, ofReal_cpow_eq_exp two_pos,
      ofReal_cpow_eq_exp hZ0, ofReal_cpow_eq_exp h1q, ofReal_exp, ← exp_add, ← exp_add, one_div, ← exp_neg,
      hZq, Real.log_div (by positivity) two_ne_zero, Real.log_mul (Real.exp_pos _).ne' h1q.ne', Real.log_exp]
    congr 1; push_cast; ring
  rw [ofReal_add, ofReal_one] at hpre
  rw [div_eq_mul_one_div (Real.sqrt π : ℂ), hpre, mul_assoc, mul_assoc, ← hwp]
  -- Landen
  set u := Real.exp (θ/2) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have hku : k = (u⁻¹)^2 := by
    rw [hkdef, hu, ← Real.exp_neg, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hsq : Real.sqrt q = k := by rw [hqdef, Real.sqrt_sq hk0.le]
  have hsk : Real.sqrt k = u⁻¹ := by rw [hku, Real.sqrt_sq (by positivity)]
  have hcu : Real.cosh (θ/2) = (u + u⁻¹)/2 := by rw [Real.cosh_eq, hu, Real.exp_neg]
  have hM : (2 * Real.sqrt (Real.sqrt q) / (1 + Real.sqrt q))^2 = (1/Real.cosh (θ/2))^2 := by
    rw [hsq, hsk, hcu, hku]; field_simp
  have hKa := DLMF.Elliptic.Real.compEllIntKm_landen_ascending hq0.le hq1
  have hEa := DLMF.Elliptic.Real.compEllIntEm_landen_ascending hq0.le hq1
  rw [hM, hsq] at hKa hEa
  have hZu : Z = (u^2 + (u⁻¹)^2)/2 := by
    show Real.cosh θ = _
    rw [Real.cosh_eq, hu, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_nat_mul]; push_cast; ring_nf
  have he3 : Real.exp (-3*θ/2) = (u⁻¹)^3 := by
    rw [hu, ← Real.exp_neg, ← Real.exp_nat_mul]; push_cast; ring_nf
  set A := DLMF.Elliptic.Real.compEllIntKm ((1/Real.cosh (θ/2))^2)
  set B := DLMF.Elliptic.Real.compEllIntEm ((1/Real.cosh (θ/2))^2)
  set Kq := DLMF.Elliptic.Real.compEllIntKm q
  set Eq := DLMF.Elliptic.Real.compEllIntEm q
  have hK' : Kq = A / (1 + k) := hKa
  have hE' : Eq = (1 + k)/2 * B + (1 - q)/2 * Kq := hEa
  rw [hE', hK', he3, hcu, hZu, hqdef, hku]
  have hpi : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hpi2 : (Real.sqrt π : ℂ)^2 = π := by rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have huC : (u:ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
  have h1 : (u:ℂ)^2 + 1 ≠ 0 := by exact_mod_cast (by positivity : (0:ℝ) < u^2+1).ne'
  have hπ : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  push_cast
  rw [← hpi2]
  field_simp
  ring


/-- Complete elliptic integrals use parameter equal to the square of DLMF modulus. -/
@[dlmf 14.5.E27]
theorem legendre_elliptic_27 {θ : ℝ} (h0 : 0 < θ) :
    olverQ (-1/2) 0 (Real.cosh θ)=2/Real.sqrt π*Real.exp (-θ/2)*(DLMF.Elliptic.Real.compEllIntKm ((Real.exp (-θ))^2):ℂ) := by
  set Z := Real.cosh θ
  set q := (Real.exp (-θ))^2 with hqdef
  have hZ0 : 0 < Z := Real.cosh_pos _
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by
    have : Real.exp (-θ) < 1 := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
    exact pow_lt_one₀ (Real.exp_pos _).le this two_ne_zero
  have hZq : Z = Real.exp θ * (1 + q) / 2 := by
    show Real.cosh θ = _
    rw [Real.cosh_eq, hqdef, ← Real.exp_nat_mul, mul_add, mul_one, ← Real.exp_add]; push_cast; ring_nf
  have hm : |q| < 1 := by rw [abs_of_pos hq0]; exact hq1
  have hqn : ‖(q:ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hm
  have h4 : 4 * (q:ℂ) / (1 + q)^2 = 1/(Z:ℂ)^2 := by
    have hq' : (q:ℂ) * (Real.exp θ : ℂ)^2 = 1 := by
      rw [hqdef, ofReal_pow, ← mul_pow, ← ofReal_mul, ← Real.exp_add]; simp
    have h1q : (1 + (q:ℂ)) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < 1 + q).ne'
    have hE : (Real.exp θ : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos θ).ne'
    rw [hZq, ofReal_div, ofReal_mul, ofReal_add, ofReal_one, ofReal_ofNat]
    field_simp; linear_combination 4 * hq'
  have hw : ‖1/(Z:ℂ)^2‖ < 1 := by
    rw [show (1:ℂ)/(Z:ℂ)^2 = ((1/Z^2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity), div_lt_one (by positivity)]
    have := Real.one_lt_cosh.2 h0.ne'; nlinarith
  have hc : ∀ k : ℕ, (1/2:ℂ) - 1/2 + 1 ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hwp := quadratic_well_poised_plus hc hqn (by rw [h4]; exact hw)
  rw [h4, show (1/2:ℂ) - 1/2 + 1 = 1 by norm_num, show (1/2:ℂ)/2 = 1/4 by norm_num,
    show ((1/2:ℂ)+1)/2 = 3/4 by norm_num] at hwp
  have hc1 : ∀ k : ℕ, (-1/2 : ℂ) + 3/2 ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [olverQ, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw, regularizedGaussHGFun_eq_div_Gamma hc1,
    show (-1/2:ℂ) + 0 + 2 = 2*(3/4) by norm_num, show (-1/2:ℂ) + 0 + 1 = 1/2 by norm_num,
    show (2*(3/4:ℂ))/2 = 3/4 by norm_num, show (1/2:ℂ)/2 = 1/4 by norm_num,
    show (-1/2:ℂ) + 3/2 = 1 by norm_num, Complex.Gamma_one, div_one,
    ordinaryHypergeometric_symm (3/4), DLMF.Elliptic.Real.compEllIntKm_eq_ordinaryHypergeometric hm]
  rw [hwp, legendreBranchPower, zero_div, zero_mul, exp_zero, mul_one]
  have h1q : 0 < 1 + q := by linarith
  have hpi : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hpi2 : (Real.sqrt π : ℂ)^2 = π := by rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hpre : (1:ℂ) / ((2:ℂ)^((-1/2:ℂ)+1) * (Z:ℂ)^(1/2:ℂ)) =
      (Real.exp (-θ/2) : ℂ) * (((1 + q : ℝ) : ℂ))^(-(1/2:ℂ)) := by
    rw [show (2:ℂ)^((-1/2:ℂ)+1) = ((2:ℝ):ℂ)^(1/2:ℂ) by norm_num, ofReal_cpow_eq_exp two_pos,
      ofReal_cpow_eq_exp hZ0, ofReal_cpow_eq_exp h1q, ofReal_exp, ← exp_add, ← exp_add, one_div, ← exp_neg,
      hZq, Real.log_div (by positivity) two_ne_zero, Real.log_mul (Real.exp_pos _).ne' h1q.ne', Real.log_exp]
    congr 1; push_cast; ring
  rw [ofReal_add, ofReal_one] at hpre
  rw [div_eq_mul_one_div (Real.sqrt π : ℂ), hpre]
  field_simp
  linear_combination (((1:ℂ) + q)^(-(1/2:ℂ)) * ₂F₁ (1/4:ℂ) (3/4) 1 (1/(Z:ℂ)^2)) * hpi2

end DLMF.Legendre
