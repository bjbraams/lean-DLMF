/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.IntegralRepresentations

/-!
# Toroidal functions, coordinates and representations

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

/-- DLMF 14.19.1: the toroidal coordinates map `(η, θ, φ) ↦ (x, y, z) = (c sinh η cos φ, c sinh η
sin φ, c sin θ)/(cosh η - cos θ)`. -/
@[dlmf 14.19.E1]
def toroidalCoordinates (c η θ phi : ℝ) : ℝ × ℝ × ℝ :=
  (c*Real.sinh η*Real.cos phi/(Real.cosh η-Real.cos θ),c*Real.sinh η*Real.sin phi/(Real.cosh η-Real.cos θ),c*Real.sin θ/(Real.cosh η-Real.cos θ))

/-- Toroidal function of the first kind. -/
def toroidalP (n : ℕ) (μ : ℂ) (x : ℝ) : ℂ :=
  associatedP (n-1/2) μ x

/-- Regularized toroidal function of the second kind. -/
def toroidalQ (n : ℕ) (μ : ℂ) (x : ℝ) : ℂ :=
  olverQ (n-1/2) μ x

/-! ### Helpers for Whipple's formulas (prefix `legTor_`) -/

/-- For real `t > 1` with `t² - 1 = u²`, `u > 0`: the Whipple point of `t` is `t/u` and
`(t²-1)^{-1/4} = exp(-(log u)/2)`. -/
theorem legTor_point {t u : ℝ} (ht : 1 < t) (hu : 0 < u) (htu : t^2 - 1 = u^2) :
    (t:ℂ)/exp ((log ((t:ℂ)-1)+log ((t:ℂ)+1))/2) = ((t/u:ℝ):ℂ) ∧
      legendreBranchPower (-1/2) t = exp (-(Real.log u:ℂ)/2) := by
  have hl : log ((t:ℂ)-1)+log ((t:ℂ)+1) = 2*(Real.log u:ℂ) := by
    rw [show (t:ℂ)-1 = ((t-1:ℝ):ℂ) by push_cast; ring, show (t:ℂ)+1 = ((t+1:ℝ):ℂ) by push_cast; ring,
      ← ofReal_log (by linarith), ← ofReal_log (by linarith), ← ofReal_add,
      ← Real.log_mul (by linarith) (by linarith), show (t-1)*(t+1) = u^2 by linear_combination htu,
      Real.log_pow]
    push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [hl, show 2*(Real.log u:ℂ)/2 = (Real.log u:ℂ) by ring, ← ofReal_exp, Real.exp_log hu]
    push_cast; ring
  · unfold legendreBranchPower
    rw [hl]; congr 1; ring

/-- `P^μ_{-ν-1} = P^μ_ν` (DLMF 14.9.11 for `P`) on `(1,∞)`. -/
theorem legTor_P_neg_degree (ν μ : ℂ) {y : ℝ} (hy : 1 < y) :
    associatedP (-ν-1) μ y = associatedP ν μ y := by
  have hz : 1 + (y:ℂ) ∈ slitPlane := Or.inl (by simp; linarith)
  unfold associatedP
  rw [regularizedGaussHG_symm _ _ _ (mem_cutPlane_of_one_add hz)]
  congr 2 <;> ring

/-- `(c/(s))^{1/2}` for positive reals as an exponential of logarithms. -/
theorem legTor_cpow_half {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    ((c/s:ℝ):ℂ)^(1/2:ℂ) = (c:ℂ)^(1/2:ℂ) * exp (-(Real.log s:ℂ)/2) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (div_pos hc hs).ne'),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hc.ne'), ← ofReal_log (div_pos hc hs).le,
    ← ofReal_log hc.le, Real.log_div hc.ne' hs.ne', ← exp_add]
  congr 1; push_cast; ring

/-- `Γ(k + 1/2) ≠ 0` for integer `k`. -/
theorem legTor_Gamma_half_ne (k : ℤ) : Gamma ((k:ℂ) + 1/2) ≠ 0 := by
  refine Gamma_ne_zero fun j hj => ?_
  have := congrArg Complex.re hj
  simp at this
  have h' : ((2*k + 1 + 2*j : ℤ):ℝ) = ((0:ℤ):ℝ) := by push_cast; linarith
  have := Int.cast_inj.mp h'
  omega

/-! ### Quadratic transformations for DLMF 14.19.2–3 -/

/-- Complex powers of a positive real as exponentials. -/
theorem legTor_cpow_real {x : ℝ} (hx : 0 < x) (s : ℂ) : (x:ℂ)^s = exp ((Real.log x:ℂ) * s) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ofReal_log hx.le]

/-- Composite quadratic transformation (DLMF 15.8.21 then 15.8.13) behind DLMF 14.19.3:
for `0 < q < 1` and `x = (1+q²)/(2q)`,
`F(μ+½, ν+μ+½; ν+1; q²) = (1+q²)^{-(ν+μ+½)} F(a/2, (a+1)/2; ν+1; x^{-2})`, `a = ν+μ+½`. -/
theorem legTor_quad (ν μ : ℂ) (hc : ∀ k : ℕ, ν + 1 ≠ -(k:ℂ)) (ht : ∀ k : ℕ, 2*ν + 1 ≠ -(k:ℂ))
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ₂F₁ (μ+1/2) (ν+μ+1/2) (ν+1) ((q^2:ℝ):ℂ) =
      exp (-(Real.log (1+q^2):ℂ)*(ν+μ+1/2)) *
        ₂F₁ ((ν+μ+1/2)/2) ((ν+μ+1/2+1)/2) (ν+1) (((2*q/(1+q^2))^2:ℝ):ℂ) := by
  have hz : ‖((q^2:ℝ):ℂ)‖ < 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; nlinarith
  have hs : ((q^2:ℝ):ℂ) ∈ slitPlane := Or.inl (by simp only [ofReal_re]; positivity)
  have hsq : ((q^2:ℝ):ℂ)^(1/2:ℂ) = (q:ℂ) := by
    rw [legTor_cpow_real (by positivity), Real.log_pow]; push_cast
    rw [show (2*(Real.log q:ℂ))*(1/2) = Real.log q by ring, ← ofReal_exp, Real.exp_log hq0]
  set w : ℝ := 4*q/(1+q)^2 with hwdef
  have hw0 : 0 < w := by positivity
  have hw1 : w < 1 := by rw [hwdef, div_lt_one (by positivity)]; nlinarith [sq_nonneg (1-q)]
  have hwC : 4*((q^2:ℝ):ℂ)^(1/2:ℂ)/(1+((q^2:ℝ):ℂ)^(1/2:ℂ))^2 = (w:ℂ) := by
    rw [hsq, hwdef]; push_cast; ring
  have hwn : ‖(w:ℂ)‖ < 1 := by rw [norm_real, Real.norm_eq_abs, abs_of_pos hw0]; exact hw1
  have s1 := quadratic_sqrt (a := ν+μ+1/2) (b := μ+1/2) (z := ((q^2:ℝ):ℂ))
    (by intro k; rw [show ν+μ+1/2-(μ+1/2)+1 = ν+1 by ring]; exact hc k)
    (by intro k; rw [show 2*(ν+μ+1/2)-2*(μ+1/2)+1 = 2*ν+1 by ring]; exact ht k) hz hs
    (by rw [hwC]; exact hwn)
  rw [hwC, hsq, show ν+μ+1/2-(μ+1/2)+1 = ν+1 by ring, show ν+μ+1/2-(μ+1/2)+1/2 = ν+1/2 by ring,
    show 2*(ν+μ+1/2)-2*(μ+1/2)+1 = 2*(ν+1/2) by ring] at s1
  have s2 := quadratic_double_denominator (a := ν+μ+1/2) (b := ν+1/2) (z := (w:ℂ))
    (by intro k; rw [show 2*(ν+1/2) = 2*ν+1 by ring]; exact ht k)
    (by intro k; rw [show ν+1/2+1/2 = ν+1 by ring]; exact hc k) hwn
  rw [show ν+1/2+1/2 = ν+1 by ring] at s2
  rw [ordinaryHypergeometric_symm, s1, s2]
  have h2w : (2:ℝ) - w ≠ 0 := by linarith
  have harg : ((w:ℂ)/(2-w))^2 = (((2*q/(1+q^2))^2:ℝ):ℂ) := by
    rw [show ((w:ℂ)/(2-w)) = ((w/(2-w):ℝ):ℂ) by push_cast; ring]
    have : w/(2-w) = 2*q/(1+q^2) := by
      rw [div_eq_div_iff h2w (by positivity), hwdef]; field_simp; ring
    rw [this]; push_cast; ring
  rw [harg]
  have hw2 : (1:ℂ) - (w:ℂ)/2 = ((1-w/2:ℝ):ℂ) := by push_cast; ring
  have h1q : (1:ℂ) + q = ((1+q:ℝ):ℂ) := by push_cast; ring
  rw [hw2, h1q, legTor_cpow_real (by positivity), legTor_cpow_real (by linarith), ← mul_assoc,
    ← exp_add]
  congr 2
  have hl : Real.log (1+q^2) = 2*Real.log (1+q) + Real.log (1-w/2) := by
    rw [show (2:ℝ)*Real.log (1+q) = Real.log ((1+q)^2) by rw [Real.log_pow]; push_cast; ring,
      ← Real.log_mul (by positivity) (by linarith)]
    congr 1; rw [hwdef]; field_simp; ring
  rw [hl]; push_cast; ring

/-- DLMF 14.19.3 off the half-integer degrees `2ν ∈ ℤ`. -/
theorem legTor_Q_hyp_generic (ν μ : ℂ) (hc : ∀ k : ℕ, ν + 1 ≠ -(k:ℂ)) (ht : ∀ k : ℕ, 2*ν + 1 ≠ -(k:ℂ))
    {ξ : ℝ} (hξ : 0 < ξ) :
    olverQ (ν-1/2) μ (Real.cosh ξ)=Real.sqrt π*(1-Real.exp (-2*ξ):ℂ)^μ/exp ((ν+1/2)*ξ)*regularizedGaussHG (μ+1/2) (ν+μ+1/2) (ν+1) (Real.exp (-2*ξ)) := by
  set q := Real.exp (-ξ) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by rw [hqdef]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hq2 : Real.exp (-2*ξ) = q^2 := by
    rw [hqdef, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hx : Real.cosh ξ = (1+q^2)/(2*q) := by
    rw [Real.cosh_eq, hqdef, show Real.exp ξ = (Real.exp (-ξ))⁻¹ by rw [Real.exp_neg, inv_inv]]
    field_simp
  have hsh : Real.sinh ξ = (1-q^2)/(2*q) := by
    rw [Real.sinh_eq, hqdef, show Real.exp ξ = (Real.exp (-ξ))⁻¹ by rw [Real.exp_neg, inv_inv]]
    field_simp
  have hs : 0 < Real.sinh ξ := Real.sinh_pos_iff.mpr hξ
  have ht1 : 1 < Real.cosh ξ := Real.one_lt_cosh.mpr hξ.ne'
  have hx0 : 0 < Real.cosh ξ := by linarith
  -- the hypergeometric factors
  have hn1 : ‖((q^2:ℝ):ℂ)‖ < 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; nlinarith
  have harg : 1/((Real.cosh ξ:ℝ):ℂ)^2 = (((2*q/(1+q^2))^2:ℝ):ℂ) := by
    rw [hx]; push_cast; field_simp
  have hn2 : ‖(((2*q/(1+q^2))^2:ℝ):ℂ)‖ < 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [div_pow, div_lt_one (by positivity)]; nlinarith [pow_pos (show 0 < 1-q^2 by nlinarith) 2]
  have hc' : ∀ k : ℕ, ν - 1/2 + 3/2 ≠ -(k:ℂ) := by
    intro k; rw [show ν-1/2+3/2 = ν+1 by ring]; exact hc k
  unfold olverQ
  rw [hq2, harg, show ((q^2:ℝ):ℂ) = ((q^2:ℝ):ℂ) from rfl,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hn1,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hn2,
    regularizedGaussHGFun_eq_div_Gamma hc, regularizedGaussHGFun_eq_div_Gamma hc',
    legTor_quad ν μ hc ht hq0 hq1, ordinaryHypergeometric_symm,
    show (ν-1/2+μ+2)/2 = (ν+μ+1/2+1)/2 by ring, show (ν-1/2+μ+1)/2 = (ν+μ+1/2)/2 by ring,
    show ν-1/2+3/2 = ν+1 by ring]
  set G := ₂F₁ ((ν+μ+1/2)/2) ((ν+μ+1/2+1)/2) (ν+1) (((2*q/(1+q^2))^2:ℝ):ℂ) / Gamma (ν+1)
  -- logarithmic bookkeeping
  have hl : log (((Real.cosh ξ:ℝ):ℂ)-1)+log (((Real.cosh ξ:ℝ):ℂ)+1) = 2*(Real.log (Real.sinh ξ):ℂ) := by
    rw [show ((Real.cosh ξ:ℝ):ℂ)-1 = ((Real.cosh ξ-1:ℝ):ℂ) by push_cast; ring,
      show ((Real.cosh ξ:ℝ):ℂ)+1 = ((Real.cosh ξ+1:ℝ):ℂ) by push_cast; ring,
      ← ofReal_log (by linarith), ← ofReal_log (by linarith), ← ofReal_add,
      ← Real.log_mul (by linarith) (by linarith),
      show (Real.cosh ξ-1)*(Real.cosh ξ+1) = Real.sinh ξ^2 by linear_combination Real.cosh_sq ξ,
      Real.log_pow]
    push_cast; ring
  have hlq : Real.log q = -ξ := by rw [hqdef, Real.log_exp]
  have hl1 : Real.log (1-q^2) = Real.log 2 + Real.log q + Real.log (Real.sinh ξ) := by
    rw [← Real.log_mul (by norm_num) hq0.ne', ← Real.log_mul (by positivity) hs.ne', hsh]
    congr 1; field_simp
  have hl2 : Real.log (1+q^2) = Real.log 2 + Real.log q + Real.log (Real.cosh ξ) := by
    rw [← Real.log_mul (by norm_num) hq0.ne', ← Real.log_mul (by positivity) hx0.ne', hx]
    congr 1; field_simp
  have e1 : (1:ℂ) - ((q^2:ℝ):ℂ) = ((1-q^2:ℝ):ℂ) := by push_cast; ring
  have q21 : q^2 < 1 := by nlinarith
  unfold legendreBranchPower
  rw [hl, e1, legTor_cpow_real (by linarith) μ, show (2:ℂ)^(ν-1/2+1) = ((2:ℝ):ℂ)^(ν-1/2+1) by norm_num,
    legTor_cpow_real (by norm_num : (0:ℝ) < 2),
    legTor_cpow_real hx0]
  have L : ∀ A B C : ℂ, (Real.sqrt π:ℂ) * exp A / (exp B * exp C) * G =
      (Real.sqrt π:ℂ) * G * exp (A + -B + -C) := by
    intro A B C; rw [exp_add, exp_add, exp_neg, exp_neg]; ring
  have R : ∀ A B C : ℂ, (Real.sqrt π:ℂ) * exp A / exp B * (exp C * ₂F₁ ((ν+μ+1/2)/2)
      ((ν+μ+1/2+1)/2) (ν+1) (((2*q/(1+q^2))^2:ℝ):ℂ) / Gamma (ν+1)) =
      (Real.sqrt π:ℂ) * G * exp (A + -B + C) := by
    intro A B C; rw [exp_add, exp_add, exp_neg]; simp only [G]; ring
  rw [L, R]
  congr 2
  rw [hl1, hl2, hlq]; push_cast; ring

/-- DLMF 14.19.2 off the half-integer orders `2μ ∈ ℤ`. -/
theorem legTor_P_hyp_generic (ν μ : ℂ) (hc1 : ∀ k : ℕ, 1 - 2*μ ≠ -(k:ℂ)) (hc2 : ∀ k : ℕ, 1 - μ ≠ -(k:ℂ))
    {ξ : ℝ} (hξ : 0 < ξ) :
    associatedP (ν-1/2) μ (Real.cosh ξ)=Gamma (1/2-μ)/(Real.sqrt π*(1-Real.exp (-2*ξ):ℂ)^μ*exp ((ν+1/2)*ξ))*regularizedGaussHG (1/2-μ) (1/2+ν-μ) (1-2*μ) (1-Real.exp (-2*ξ)) := by
  set q := Real.exp (-ξ) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by rw [hqdef]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hq2 : Real.exp (-2*ξ) = q^2 := by
    rw [hqdef, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hx : Real.cosh ξ = (1+q^2)/(2*q) := by
    rw [Real.cosh_eq, hqdef, show Real.exp ξ = (Real.exp (-ξ))⁻¹ by rw [Real.exp_neg, inv_inv]]
    field_simp
  have hsh : Real.sinh ξ = (1-q^2)/(2*q) := by
    rw [Real.sinh_eq, hqdef, show Real.exp ξ = (Real.exp (-ξ))⁻¹ by rw [Real.exp_neg, inv_inv]]
    field_simp
  have hs : 0 < Real.sinh ξ := Real.sinh_pos_iff.mpr hξ
  have ht1 : 1 < Real.cosh ξ := Real.one_lt_cosh.mpr hξ.ne'
  have hx0 : 0 < Real.cosh ξ := by linarith
  have q21 : q^2 < 1 := by nlinarith
  have hz : ((Real.cosh ξ:ℝ):ℂ) - 1 ∈ slitPlane := Or.inl (by simp only [sub_re, ofReal_re, one_re]; linarith)
  -- step 1: degree reflection and DLMF 14.3.18
  have hrefl := legTor_P_neg_degree (-ν-1/2) μ ht1
  rw [show -(-ν-1/2)-1 = ν-1/2 by ring] at hrefl
  rw [hrefl]
  rw [show associatedP (-ν-1/2) μ (Real.cosh ξ) = associatedP (-ν-1/2) (-(-μ)) (Real.cosh ξ) by
    rw [neg_neg], associatedP_neg_eq_quadratic (-ν-1/2) (-μ) hz (by simp only [ofReal_re]; linarith)]
  simp only [neg_neg]
  -- step 2: hypergeometric factors
  have hw1 : ‖(1:ℂ) - 1/((Real.cosh ξ:ℝ):ℂ)^2‖ < 1 := by
    rw [show (1:ℂ) - 1/((Real.cosh ξ:ℝ):ℂ)^2 = ((1 - 1/Real.cosh ξ^2:ℝ):ℂ) by push_cast; ring,
      norm_real, Real.norm_eq_abs, abs_lt]
    have : 0 < 1/Real.cosh ξ^2 := by positivity
    have : 1/Real.cosh ξ^2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
    constructor <;> linarith
  have hw2 : ‖((1-q^2:ℝ):ℂ)‖ < 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; nlinarith
  have hc2' : ∀ k : ℕ, -μ + 1 ≠ -(k:ℂ) := fun k => by rw [show -μ+1 = 1-μ by ring]; exact hc2 k
  rw [hq2, show (1:ℂ) - ((q^2:ℝ):ℂ) = ((1-q^2:ℝ):ℂ) by push_cast; ring,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw1,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw2,
    regularizedGaussHGFun_eq_div_Gamma hc2', regularizedGaussHGFun_eq_div_Gamma hc1,
    ordinaryHypergeometric_symm (1/2-μ), show 1-2*μ = 2*(1/2-μ) by ring,
    quadratic_double_denominator (by intro k; rw [show 2*(1/2-μ) = 1-2*μ by ring]; exact hc1 k)
      (by intro k; rw [show 1/2-μ+1/2 = 1-μ by ring]; exact hc2 k) hw2,
    show 1/2-μ+1/2 = -μ+1 by ring,
    show (-μ-(-ν-1/2))/2 = (1/2+ν-μ)/2 by ring, show (-μ-(-ν-1/2)+1)/2 = (1/2+ν-μ+1)/2 by ring]
  have hr : ((1-q^2)/(2-(1-q^2)))^2 = 1 - 1/Real.cosh ξ^2 := by
    rw [hx, show (2:ℝ)-(1-q^2) = 1+q^2 by ring, div_pow, div_pow, one_div_div]
    have : (1+q^2)^2 ≠ 0 := by positivity
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq this]; ring
  have harg : (((1-q^2:ℝ):ℂ)/(2-((1-q^2:ℝ):ℂ)))^2 = (1:ℂ) - 1/((Real.cosh ξ:ℝ):ℂ)^2 := by
    rw [show (((1-q^2:ℝ):ℂ)/(2-((1-q^2:ℝ):ℂ)))^2 = ((((1-q^2)/(2-(1-q^2)))^2:ℝ):ℂ) by push_cast; ring,
      hr]; push_cast; ring
  rw [harg]
  set F := ₂F₁ ((1/2+ν-μ)/2) ((1/2+ν-μ+1)/2) (-μ+1) ((1:ℂ) - 1/((Real.cosh ξ:ℝ):ℂ)^2)
  -- step 3: duplication
  have hG1 : Gamma (-μ+1) ≠ 0 := Gamma_ne_zero hc2'
  have hG2 : Gamma (2*(1/2-μ)) ≠ 0 := Gamma_ne_zero (by
    intro k; rw [show 2*(1/2-μ) = 1-2*μ by ring]; exact hc1 k)
  have hdup := Complex.Gamma_mul_Gamma_add_half (1/2-μ)
  rw [show 1/2-μ+1/2 = -μ+1 by ring, show 1-2*(1/2-μ) = 2*μ by ring] at hdup
  have hGam : Gamma (1/2-μ) = Gamma (2*(1/2-μ)) * (2:ℂ)^(2*μ) * Real.sqrt π / Gamma (-μ+1) := by
    rw [eq_div_iff hG1, hdup]
  rw [hGam]
  -- step 4: logarithms
  have hl : log (((Real.cosh ξ:ℝ):ℂ)-1)+log (((Real.cosh ξ:ℝ):ℂ)+1) = 2*(Real.log (Real.sinh ξ):ℂ) := by
    rw [show ((Real.cosh ξ:ℝ):ℂ)-1 = ((Real.cosh ξ-1:ℝ):ℂ) by push_cast; ring,
      show ((Real.cosh ξ:ℝ):ℂ)+1 = ((Real.cosh ξ+1:ℝ):ℂ) by push_cast; ring,
      ← ofReal_log (by linarith), ← ofReal_log (by linarith), ← ofReal_add,
      ← Real.log_mul (by linarith) (by linarith),
      show (Real.cosh ξ-1)*(Real.cosh ξ+1) = Real.sinh ξ^2 by linear_combination Real.cosh_sq ξ,
      Real.log_pow]
    push_cast; ring
  have hlq : Real.log q = -ξ := by rw [hqdef, Real.log_exp]
  have hl1 : Real.log (1-q^2) = Real.log 2 + Real.log q + Real.log (Real.sinh ξ) := by
    rw [← Real.log_mul (by norm_num) hq0.ne', ← Real.log_mul (by positivity) hs.ne', hsh]
    congr 1; field_simp
  have hl2 : Real.log (1-(1-q^2)/2) = Real.log q + Real.log (Real.cosh ξ) := by
    rw [← Real.log_mul hq0.ne' hx0.ne', hx]
    congr 1; field_simp; ring
  have e2 : (1:ℂ) - ((1-q^2:ℝ):ℂ)/2 = ((1-(1-q^2)/2:ℝ):ℂ) := by push_cast; ring
  unfold legendreBranchPower
  have h2 : ∀ s : ℂ, (2:ℂ)^s = exp ((Real.log 2:ℂ)*s) := fun s => by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num]; exact legTor_cpow_real (by norm_num) s
  rw [hl, e2, h2, h2, legTor_cpow_real hx0, legTor_cpow_real (by linarith) μ,
    legTor_cpow_real (by nlinarith)]
  have hpi : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have L : ∀ A B C : ℂ, exp A * exp B * exp C * (F / Gamma (-μ+1)) = F / Gamma (-μ+1) * exp (A+B+C) := by
    intro A B C; rw [exp_add, exp_add]; ring
  have R : ∀ D E G H : ℂ, Gamma (2*(1/2-μ)) * exp D * (Real.sqrt π:ℂ) / Gamma (-μ+1) /
      ((Real.sqrt π:ℂ) * exp E * exp G) * (exp H * F / Gamma (2*(1/2-μ))) =
      F / Gamma (-μ+1) * exp (D + -E + -G + H) := by
    intro D E G H; rw [exp_add, exp_add, exp_add, exp_neg, exp_neg]
    have h2' := hG2; rw [show 2*(1/2-μ) = 1-2*μ by ring] at h2' ⊢; field_simp
  rw [L, R]
  congr 2
  rw [hl1, hl2, hlq]; push_cast; ring

/-- DLMF 14.19.2: for `μ` not a positive half-odd integer and `ξ > 0`, `P^μ_{ν-1/2}(cosh ξ) =
Γ(1/2-μ)/(π^{1/2} (1-e^{-2ξ})^μ e^{(ν+1/2)ξ}) 𝐅(1/2-μ, 1/2+ν-μ; 1-2μ; 1-e^{-2ξ})`. -/
@[dlmf 14.19.E2]
theorem toroidalP_hypergeometric (ν μ : ℂ) (hμ : ∀ n : ℕ, μ ≠ n+1/2) {ξ : ℝ} (hξ : 0 < ξ) :
    associatedP (ν-1/2) μ (Real.cosh ξ)=Gamma (1/2-μ)/(Real.sqrt π*(1-Real.exp (-2*ξ):ℂ)^μ*exp ((ν+1/2)*ξ))*regularizedGaussHG (1/2-μ) (1/2+ν-μ) (1-2*μ) (1-Real.exp (-2*ξ)) := by
  have ht1 : 1 < Real.cosh ξ := Real.one_lt_cosh.mpr hξ.ne'
  have hz : ((Real.cosh ξ:ℝ):ℂ) - 1 ∈ slitPlane := Or.inl (by simp only [sub_re, ofReal_re, one_re]; linarith)
  have he0 : 0 < Real.exp (-2*ξ) := Real.exp_pos _
  have he1 : Real.exp (-2*ξ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hcut : (1:ℂ) - ((Real.exp (-2*ξ):ℝ):ℂ) ∈ cutPlane := by
    refine mem_cutPlane_of_norm_lt_one ?_
    rw [show (1:ℂ) - ((Real.exp (-2*ξ):ℝ):ℂ) = ((1 - Real.exp (-2*ξ):ℝ):ℂ) by push_cast; ring,
      norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hb : (1:ℂ) - ((Real.exp (-2*ξ):ℝ):ℂ) ≠ 0 := by
    rw [show (1:ℂ) - ((Real.exp (-2*ξ):ℝ):ℂ) = ((1 - Real.exp (-2*ξ):ℝ):ℂ) by push_cast; ring]
    exact ofReal_ne_zero.mpr (by linarith)
  have hpi : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hD : ∀ μ : ℂ, (Real.sqrt π:ℂ)*(1-Real.exp (-2*ξ):ℂ)^μ*exp ((ν+1/2)*ξ) ≠ 0 := fun μ =>
    mul_ne_zero (mul_ne_zero hpi (cpow_ne_zero_iff.mpr (Or.inl hb))) (exp_ne_zero _)
  have key := legendre_eq_of_continuous_off_countable
    (f := fun μ : ℂ => (Gamma (1/2-μ))⁻¹ * associatedP (ν-1/2) μ (Real.cosh ξ))
    (g := fun μ : ℂ => ((Real.sqrt π:ℂ)*(1-Real.exp (-2*ξ):ℂ)^μ*exp ((ν+1/2)*ξ))⁻¹ *
      regularizedGaussHG (1/2-μ) (1/2+ν-μ) (1-2*μ) (1-Real.exp (-2*ξ)))
    ((differentiable_one_div_Gamma.continuous.comp (continuous_const.sub continuous_id)).mul
      (associatedP_entire_order (ν-1/2) _ hz).continuous)
    (((continuous_const.mul (continuous_const_cpow' hb)).mul (Continuous.cexp (by fun_prop))).inv₀ hD
      |>.mul (differentiable_regularizedGaussHG_comp (A := fun μ : ℂ => 1/2-μ)
      (B := fun μ : ℂ => 1/2+ν-μ) (C := fun μ : ℂ => 1-2*μ) (by fun_prop) (by fun_prop) (by fun_prop)
      hcut).continuous)
    (countable_range (fun n : ℤ => (n:ℂ)/2)) (fun μ hμ' => ?_) μ
  · have hG : Gamma (1/2-μ) ≠ 0 := Gamma_ne_zero fun m hm => hμ m (by linear_combination -hm)
    have key' : (Gamma (1/2-μ))⁻¹ * associatedP (ν-1/2) μ (Real.cosh ξ) =
        ((Real.sqrt π:ℂ)*(1-Real.exp (-2*ξ):ℂ)^μ*exp ((ν+1/2)*ξ))⁻¹ *
          regularizedGaussHG (1/2-μ) (1/2+ν-μ) (1-2*μ) (1-Real.exp (-2*ξ)) := key
    calc associatedP (ν-1/2) μ (Real.cosh ξ)
        = Gamma (1/2-μ) * ((Gamma (1/2-μ))⁻¹ * associatedP (ν-1/2) μ (Real.cosh ξ)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hG, one_mul]
      _ = _ := by rw [key']; ring
  · have hG : Gamma (1/2-μ) ≠ 0 := Gamma_ne_zero fun m hm => hμ' ⟨2*(m:ℤ)+1, by
      push_cast; linear_combination hm⟩
    show (Gamma (1/2-μ))⁻¹ * associatedP (ν-1/2) μ (Real.cosh ξ) = _
    rw [legTor_P_hyp_generic ν μ (fun k hk => hμ' ⟨(k:ℤ)+1, by push_cast; linear_combination hk/2⟩)
      (fun k hk => hμ' ⟨2*(k:ℤ)+2, by push_cast; linear_combination hk⟩) hξ]
    rw [← mul_assoc, ← mul_div_assoc, inv_mul_cancel₀ hG, one_div]

/-- DLMF 14.19.3: for `ξ > 0`, `𝑸^μ_{ν-1/2}(cosh ξ) = π^{1/2} (1-e^{-2ξ})^μ e^{-(ν+1/2)ξ} 𝐅(μ+1/2,
ν+μ+1/2; ν+1; e^{-2ξ})`. -/
@[dlmf 14.19.E3]
theorem toroidalQ_hypergeometric (ν μ : ℂ) {ξ : ℝ} (hξ : 0 < ξ) :
    olverQ (ν-1/2) μ (Real.cosh ξ)=Real.sqrt π*(1-Real.exp (-2*ξ):ℂ)^μ/exp ((ν+1/2)*ξ)*regularizedGaussHG (μ+1/2) (ν+μ+1/2) (ν+1) (Real.exp (-2*ξ)) := by
  have ht1 : 1 < Real.cosh ξ := Real.one_lt_cosh.mpr hξ.ne'
  have hz : ((Real.cosh ξ:ℝ):ℂ) - 1 ∈ slitPlane := Or.inl (by simp only [sub_re, ofReal_re, one_re]; linarith)
  have hcut : ((Real.exp (-2*ξ):ℝ):ℂ) ∈ cutPlane := by
    refine mem_cutPlane_of_norm_lt_one ?_
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  refine legendre_eq_of_continuous_off_countable (f := fun ν : ℂ => olverQ (ν-1/2) μ (Real.cosh ξ))
    (g := fun ν : ℂ => Real.sqrt π*(1-Real.exp (-2*ξ):ℂ)^μ/exp ((ν+1/2)*ξ)*regularizedGaussHG (μ+1/2)
      (ν+μ+1/2) (ν+1) (Real.exp (-2*ξ)))
    ((olverQ_entire_degree μ _ hz).continuous.comp (continuous_id.sub continuous_const)) ?_
    (countable_range (fun n : ℤ => (n:ℂ)/2)) (fun ν hν => ?_) ν
  · refine (continuous_const.div (Continuous.cexp (by fun_prop)) (fun _ => exp_ne_zero _)).mul ?_
    exact (differentiable_regularizedGaussHG_comp (A := fun _ : ℂ => μ+1/2)
      (B := fun ν : ℂ => ν+μ+1/2) (C := fun ν : ℂ => ν+1) (by fun_prop) (by fun_prop) (by fun_prop)
      hcut).continuous
  · refine legTor_Q_hyp_generic ν μ (fun k hk => hν ⟨-2*(k:ℤ)-2, ?_⟩) (fun k hk => hν ⟨-(k:ℤ)-1, ?_⟩) hξ
    · push_cast; linear_combination -hk
    · push_cast; linear_combination -hk/2

/-! ### Helpers for DLMF 14.19.4 -/

/-- The half-angle substitution `u = tan²(θ/2) = (1 - cos θ)/(1 + cos θ)`. -/
noncomputable def legInt_ht (θ : ℝ) : ℝ := (1 - Real.cos θ) / (1 + Real.cos θ)

/-- Its derivative `2 sin θ/(1 + cos θ)²`. -/
noncomputable def legInt_ht' (θ : ℝ) : ℝ := 2 * Real.sin θ / (1 + Real.cos θ) ^ 2

/-- `-1 < cos θ < 1` and `0 < sin θ` on `(0, π)`. -/
theorem legInt_cos_bounds {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    -1 < Real.cos θ ∧ Real.cos θ < 1 ∧ 0 < Real.sin θ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have h := Real.sin_sq_add_cos_sq θ
  refine ⟨?_, ?_, hs⟩ <;> nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ]

/-- Change of variables `u = tan²(θ/2)` from `(0, ∞)` to `(0, π)`. -/
theorem legInt_ht_cov {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0)) :
    IntegrableOn (fun θ => |legInt_ht' θ| • g (legInt_ht θ)) (Ioo 0 π) ∧
      ∫ θ in Ioo 0 π, |legInt_ht' θ| • g (legInt_ht θ) = ∫ u in Ioi 0, g u := by
  have hd : ∀ θ ∈ Ioo (0:ℝ) π, HasDerivWithinAt legInt_ht (legInt_ht' θ) (Ioo 0 π) θ := by
    intro θ hθ
    have hc : 0 < 1 + Real.cos θ := by linarith [(legInt_cos_bounds hθ).1]
    have h := ((Real.hasDerivAt_cos θ).const_sub 1).div ((Real.hasDerivAt_cos θ).const_add 1) hc.ne'
    unfold legInt_ht legInt_ht'
    convert h.hasDerivWithinAt using 1
    field_simp; ring
  have hinj : InjOn legInt_ht (Ioo 0 π) := by
    intro a ha b hb he
    have ha1 : 0 < 1 + Real.cos a := by linarith [(legInt_cos_bounds ha).1]
    have hb1 : 0 < 1 + Real.cos b := by linarith [(legInt_cos_bounds hb).1]
    simp only [legInt_ht] at he
    rw [div_eq_div_iff ha1.ne' hb1.ne'] at he
    exact Real.injOn_cos ⟨ha.1.le, ha.2.le⟩ ⟨hb.1.le, hb.2.le⟩ (by linarith)
  have him : legInt_ht '' Ioo 0 π = Ioi 0 := by
    ext u; constructor
    · rintro ⟨θ, hθ, rfl⟩
      obtain ⟨h1, h2, -⟩ := legInt_cos_bounds hθ
      show 0 < (1 - Real.cos θ)/(1 + Real.cos θ)
      exact div_pos (by linarith) (by linarith)
    · intro hu
      have hu0 : 0 < u := hu
      have hy1 : -1 < (1-u)/(1+u) := by rw [lt_div_iff₀ (by linarith)]; linarith
      have hy2 : (1-u)/(1+u) < 1 := by rw [div_lt_one (by linarith)]; linarith
      refine ⟨Real.arccos ((1-u)/(1+u)), ⟨Real.arccos_pos.mpr hy2, Real.arccos_lt_pi.mpr hy1⟩, ?_⟩
      rw [legInt_ht, Real.cos_arccos hy1.le hy2.le]
      field_simp; ring
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj g
  have hcovI := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hd hinj g
  rw [him] at hcov hcovI
  exact ⟨hcovI.mp hg, hcov.symm⟩

/-- The Euler half-line kernel of DLMF 14.19.4 at `u = tan²(θ/2)`, with `2qx = 1+q²`,
`2qs = 1-q²`. -/
theorem legInt_toroidal_point (a : ℂ) (m : ℕ) {q x s θ : ℝ} (hq : 0 < q) (hqx : 1 + q^2 = 2*q*x)
    (hqs : 1 - q^2 = 2*q*s) (hq1 : q < 1) (hθ : θ ∈ Ioo (0:ℝ) π) :
    |legInt_ht' θ| • eulerHalfLineKernel a (m+1/2) (m+1/2) (((q^2)⁻¹:ℝ):ℂ) (legInt_ht θ) =
      (2:ℂ)^(-(2*m:ℂ)) * (q:ℂ)^a * ((Real.sin θ:ℂ)^(2*m) / ((x + Real.cos θ * s : ℝ):ℂ)^a) := by
  obtain ⟨h1, h2, hS⟩ := legInt_cos_bounds hθ
  set C := Real.cos θ
  set S := Real.sin θ
  have hht : legInt_ht θ = (1-C)/(1+C) := rfl
  have hht' : legInt_ht' θ = 2*S/(1+C)^2 := rfl
  have hp : 0 < 1 + C := by linarith
  have hm : 0 < 1 - C := by linarith
  have hs0 : 0 < s := by nlinarith
  have hx0 : 0 < x := by nlinarith
  have hW : 0 < x + C * s := by
    have : 2*q*(x + C*s) = (1+C) + q^2*(1-C) := by nlinarith
    have : 0 < 2*q*(x + C*s) := by rw [this]; positivity
    exact pos_of_mul_pos_right this (by positivity)
  have hSC : S^2 = (1-C)*(1+C) := by have := Real.sin_sq_add_cos_sq θ; nlinarith
  have hu : 0 < legInt_ht θ := by rw [hht]; exact div_pos hm hp
  have hd : 0 < |legInt_ht' θ| := abs_pos.mpr (by rw [hht']; positivity)
  have l0 : 2 * Real.log S = Real.log (1-C) + Real.log (1+C) := by
    rw [← Real.log_mul hm.ne' hp.ne', ← hSC, Real.log_pow]; push_cast; ring
  have l1 : Real.log (legInt_ht θ) = Real.log (1-C) - Real.log (1+C) := by
    rw [hht]; exact Real.log_div hm.ne' hp.ne'
  have l2 : Real.log (1 + legInt_ht θ) = Real.log 2 - Real.log (1+C) := by
    rw [← Real.log_div two_ne_zero hp.ne']; congr 1; rw [hht]; field_simp; ring
  have l3 : Real.log ((q^2)⁻¹ + legInt_ht θ) =
      Real.log 2 + Real.log (x + C*s) - Real.log q - Real.log (1+C) := by
    rw [← Real.log_mul two_ne_zero hW.ne', ← Real.log_div (by positivity) hq.ne',
      ← Real.log_div (by positivity) hp.ne']
    congr 1; rw [hht]; field_simp; nlinarith
  have l4 : Real.log |legInt_ht' θ| = Real.log 2 + Real.log S - 2 * Real.log (1+C) := by
    rw [hht', abs_of_pos (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_mul two_ne_zero hS.ne', Real.log_pow]; push_cast; ring
  unfold eulerHalfLineKernel
  rw [show (1:ℂ) + ((legInt_ht θ:ℝ):ℂ) = ((1 + legInt_ht θ : ℝ):ℂ) by push_cast; ring,
    show (((q^2)⁻¹:ℝ):ℂ) + ((legInt_ht θ:ℝ):ℂ) = (((q^2)⁻¹ + legInt_ht θ : ℝ):ℂ) by push_cast; ring,
    show (2:ℂ)^(-(2*m:ℂ)) = ((2:ℝ):ℂ)^(-(2*m:ℂ)) by norm_num,
    show (S:ℂ)^(2*m) = (S:ℂ)^(((2*m:ℕ):ℂ)) by rw [cpow_natCast],
    legInt_cpow_ofReal hu, legInt_cpow_ofReal (by positivity : (0:ℝ) < 1 + legInt_ht θ),
    legInt_cpow_ofReal (by positivity : (0:ℝ) < (q^2)⁻¹ + legInt_ht θ), legInt_cpow_ofReal hq,
    legInt_cpow_ofReal two_pos, legInt_cpow_ofReal hS, legInt_cpow_ofReal hW, real_smul,
    show ((|legInt_ht' θ|:ℝ):ℂ) = exp (Real.log |legInt_ht' θ| : ℂ) by
      rw [← ofReal_exp, Real.exp_log hd]]
  rw [← Complex.exp_sub]
  simp only [← exp_add]
  congr 1
  rw [l1, l2, l3, l4]
  have l0' : (2:ℂ) * Real.log S = Real.log (1-C) + Real.log (1+C) := by exact_mod_cast l0
  push_cast
  linear_combination (-(m:ℂ)+1/2) * l0'

/-- The constant in DLMF 14.19.4, by the duplication formula. -/
theorem legInt_toroidal_value (n m : ℕ) (F : ℂ) {q c s : ℝ} (hq0 : 0 < q) (hc0 : 0 < c) (hs0 : 0 < s) :
    Gamma (n+m+1/2)*(s:ℂ)^m/(2^m*Real.sqrt π*Gamma (n-m+1/2)*Gamma (m+1/2)) *
      ((2:ℂ)^(2*m:ℂ) * (q:ℂ)^(-((n:ℂ)+m+1/2)) * (Gamma (m+1/2) * Gamma (m+1/2) *
        (exp (Real.log q * (2*((m:ℂ)-(-n-1/2)))) * exp ((Real.log q + Real.log c) * ((-n-1/2:ℂ)-m)) *
          (Gamma ((m:ℂ)+1) / Gamma (2*(m:ℂ)+1)) * F))) =
      Gamma (n+m+1/2) / Gamma (n-m+1/2) *
        ((2:ℂ)^(-(m:ℂ)) * (c:ℂ)^((-n-1/2:ℂ)-m) * exp (Real.log s * m) * F) := by
  have hdup := Complex.Gamma_mul_Gamma_add_half ((m:ℂ)+1/2)
  rw [show (m:ℂ)+1/2+1/2 = m+1 by ring, show 2*((m:ℂ)+1/2) = 2*m+1 by ring] at hdup
  have hc : ∀ k : ℕ, 2*(m:ℂ)+1 ≠ -(k:ℂ) := fun k hk => by
    have := congrArg re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k), (m.cast_nonneg : (0:ℝ) ≤ m)]
  have hGa : Gamma ((m:ℂ)+1/2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; positivity)
  have hG2 : Gamma (2*(m:ℂ)+1) ≠ 0 := Gamma_ne_zero hc
  have hGb : Gamma ((n:ℂ)-m+1/2) ≠ 0 := by
    have := legTor_Gamma_half_ne ((n:ℤ)-m); push_cast at this; exact this
  have hpi : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hG1 : Gamma ((m:ℂ)+1) / Gamma (2*(m:ℂ)+1) = 2^(1-(2*(m:ℂ)+1)) * Real.sqrt π / Gamma ((m:ℂ)+1/2) := by
    rw [eq_div_iff hGa, div_mul_eq_mul_div, div_eq_iff hG2, mul_comm (Gamma ((m:ℂ)+1)), hdup]; ring
  rw [hG1]
  have h2 : ∀ w : ℂ, (2:ℂ)^w = exp (Real.log 2 * w) := fun w => by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, legInt_cpow_ofReal two_pos]
  have h2n : (2:ℂ)^m = exp (Real.log 2 * (m:ℂ)) := by rw [← h2, cpow_natCast]
  have hsn : (s:ℂ)^m = exp (Real.log s * (m:ℂ)) := by rw [← cpow_natCast, legInt_cpow_ofReal hs0]
  rw [h2n, hsn, h2, h2, h2, legInt_cpow_ofReal hq0, legInt_cpow_ofReal hc0]
  have e : exp (Real.log s * (m:ℂ)) * exp (Real.log 2 * (2*m:ℂ)) *
      exp (Real.log q * (-((n:ℂ)+m+1/2))) * exp (Real.log q * (2*((m:ℂ)-(-n-1/2)))) *
      exp ((Real.log q + Real.log c) * ((-n-1/2:ℂ)-m)) * exp (Real.log 2 * (1-(2*(m:ℂ)+1))) =
      exp (Real.log 2 * (m:ℂ)) *
        (exp (Real.log 2 * (-(m:ℂ))) * exp (Real.log c * ((-n-1/2:ℂ)-m)) * exp (Real.log s * m)) := by
    simp only [← exp_add]; congr 1; ring
  have hne : exp (Real.log 2 * (m:ℂ)) ≠ 0 := exp_ne_zero _
  calc _ = (exp (Real.log s * (m:ℂ)) * exp (Real.log 2 * (2*m:ℂ)) *
      exp (Real.log q * (-((n:ℂ)+m+1/2))) * exp (Real.log q * (2*((m:ℂ)-(-n-1/2)))) *
      exp ((Real.log q + Real.log c) * ((-n-1/2:ℂ)-m)) * exp (Real.log 2 * (1-(2*(m:ℂ)+1)))) /
      exp (Real.log 2 * (m:ℂ)) * (Gamma (n+m+1/2) / Gamma (n-m+1/2) * F) *
      ((Gamma ((m:ℂ)+1/2) * (Gamma ((m:ℂ)+1/2))⁻¹) * (Gamma ((m:ℂ)+1/2) * (Gamma ((m:ℂ)+1/2))⁻¹) *
        ((Real.sqrt π:ℂ) * (Real.sqrt π:ℂ)⁻¹)) := by ring
    _ = _ := by
      rw [mul_inv_cancel₀ hGa, mul_inv_cancel₀ hpi, e, mul_div_cancel_left₀ _ hne]
      ring

/-- toroidalP integral, from the Euler half-line integral of `₂F₁` (via the substitution
`u = tan²(θ/2)`) and the hypergeometric form of `P^{-m}_{-n-1/2}`. -/
@[dlmf 14.19.E4]
theorem toroidalP_integral (n m : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    toroidalP n m (Real.cosh ξ)=Gamma (n+m+1/2)*(Real.sinh ξ:ℂ)^m/(2^m*Real.sqrt π*Gamma (n-m+1/2)*Gamma (m+1/2))*∫ θ : ℝ in 0..π, (Real.sin θ:ℂ)^(2*m)/(Real.cosh ξ+Real.cos θ*Real.sinh ξ:ℂ)^(n+m+1/2:ℂ) := by
  set c := Real.cosh ξ with hcdef
  set s := Real.sinh ξ with hsdef
  set q := Real.exp (-ξ) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hc1 : 1 < c := Real.one_lt_cosh.mpr hξ.ne'
  have hs0 : 0 < s := Real.sinh_pos_iff.mpr hξ
  have hqi : Real.exp ξ = q⁻¹ := by rw [hqdef, Real.exp_neg, inv_inv]
  have hqx : 1 + q^2 = 2*q*c := by
    rw [hcdef, Real.cosh_eq, hqi, ← hqdef]; field_simp
  have hqs : 1 - q^2 = 2*q*s := by
    rw [hsdef, Real.sinh_eq, hqi, ← hqdef]; field_simp
  set a : ℂ := (n:ℂ)+m+1/2 with hadef
  have hha : 0 < ((m:ℂ)+1/2).re := by simp; positivity
  have hz : 0 < ((((q^2)⁻¹:ℝ)):ℂ).re := by simp only [ofReal_re]; positivity
  obtain ⟨hKI, hKv⟩ := eulerHalfLine_integrable_integral (p := a) hha hha hz
  obtain ⟨hI, hE⟩ := legInt_ht_cov hKI
  have hw : 1 - (((q^2)⁻¹:ℝ):ℂ) ∈ cutPlane := by
    rw [mem_cutPlane, sub_sub_cancel]; exact Or.inl (by simp only [ofReal_re]; positivity)
  have hF : regularizedGaussHG a ((m:ℂ)+1/2) (2*(m:ℂ)+1) (1 - (((q^2)⁻¹:ℝ):ℂ)) =
      exp (Real.log q * (2*((m:ℂ)-(-n-1/2)))) * exp ((Real.log q + Real.log c) * ((-n-1/2:ℂ)-m)) *
        (Gamma ((m:ℂ)+1) / Gamma (2*(m:ℂ)+1)) *
        regularizedGaussHG (((m:ℂ)-(-n-1/2))/2) (((m:ℂ)-(-n-1/2)+1)/2) ((m:ℂ)+1) (1 - 1/(c:ℂ)^2) := by
    rw [regularizedGaussHG_symm _ _ _ hw, show a = (m:ℂ) - (-n-1/2) by rw [hadef]; ring,
      legInt_cosh_hyp (-n-1/2) m (by simp only [natCast_re]; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)])
        hq0 hq1 hqx]
  rw [show (m:ℂ)+1/2+((m:ℂ)+1/2) = 2*(m:ℂ)+1 by ring, hF] at hKv
  -- the integral over `(0, π)`
  have hf : ∀ θ ∈ Ioo (0:ℝ) π, (2:ℂ)^(2*m:ℂ) * (q:ℂ)^(-a) *
      (|legInt_ht' θ| • eulerHalfLineKernel a (m+1/2) (m+1/2) (((q^2)⁻¹:ℝ):ℂ) (legInt_ht θ)) =
      (Real.sin θ:ℂ)^(2*m)/(Real.cosh ξ+Real.cos θ*Real.sinh ξ:ℂ)^(n+m+1/2:ℂ) := by
    intro θ hθ
    have h1 : (2:ℂ)^(2*m:ℂ) * (2:ℂ)^(-(2*m:ℂ)) = 1 := by
      rw [← cpow_add _ _ two_ne_zero, add_neg_cancel, cpow_zero]
    have h2 : (q:ℂ)^(-a) * (q:ℂ)^a = 1 := by
      rw [← cpow_add _ _ (ofReal_ne_zero.mpr hq0.ne'), neg_add_cancel, cpow_zero]
    have key : ∀ X : ℂ, (2:ℂ)^(2*m:ℂ) * (q:ℂ)^(-a) * ((2:ℂ)^(-(2*m:ℂ)) * (q:ℂ)^a * X) = X := fun X => by
      linear_combination X * ((2:ℂ)^(2*m:ℂ) * (2:ℂ)^(-(2*m:ℂ)) * h2 + h1)
    rw [legInt_toroidal_point a m hq0 hqx hqs hq1 hθ, key,
      show ((c + Real.cos θ * s : ℝ):ℂ) = (Real.cosh ξ:ℂ) + (Real.cos θ:ℂ) * (Real.sinh ξ:ℂ) by
        rw [ofReal_add, ofReal_mul]]
  have hint : ∫ θ : ℝ in 0..π, (Real.sin θ:ℂ)^(2*m)/(Real.cosh ξ+Real.cos θ*Real.sinh ξ:ℂ)^(n+m+1/2:ℂ) =
      (2:ℂ)^(2*m:ℂ) * (q:ℂ)^(-a) * (Gamma ((m:ℂ)+1/2) * Gamma ((m:ℂ)+1/2) *
        (exp (Real.log q * (2*((m:ℂ)-(-n-1/2)))) * exp ((Real.log q + Real.log c) * ((-n-1/2:ℂ)-m)) *
          (Gamma ((m:ℂ)+1) / Gamma (2*(m:ℂ)+1)) *
          regularizedGaussHG (((m:ℂ)-(-n-1/2))/2) (((m:ℂ)-(-n-1/2)+1)/2) ((m:ℂ)+1) (1 - 1/(c:ℂ)^2))) := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo,
      ← setIntegral_congr_fun measurableSet_Ioo hf, integral_const_mul, hE, hKv]
  rw [hint]
  have hnon : ∀ k : ℕ, (n:ℂ)-1/2-m+1 ≠ -(k:ℂ) := fun k hk => by
    have := congrArg re hk; simp at this
    have h' : ((2*n+1+2*k : ℤ):ℝ) = ((2*m:ℤ):ℝ) := by push_cast; linarith
    have := Int.cast_inj.mp h'; omega
  have hP := associatedP_negative_integer_order ((n:ℂ)-1/2) m hnon (legInt_one_lt_mem hc1)
  have hGb : Gamma ((n:ℂ)-1/2-m+1) ≠ 0 := by
    have := legTor_Gamma_half_ne ((n:ℤ)-m); push_cast at this
    rwa [show (n:ℂ)-1/2-m+1 = (n:ℂ)-m+1/2 by ring]
  have hPm : associatedP ((n:ℂ)-1/2) m c = Gamma ((n:ℂ)-1/2+m+1)/Gamma ((n:ℂ)-1/2-m+1) *
      associatedP ((n:ℂ)-1/2) (-(m:ℂ)) c := by
    have hGa : Gamma ((n:ℂ)-1/2+m+1) ≠ 0 := by
      have := legTor_Gamma_half_ne ((n:ℤ)+m); push_cast at this
      rwa [show (n:ℂ)-1/2+m+1 = (n:ℂ)+m+1/2 by ring]
    rw [hP, ← mul_assoc, div_mul_div_comm, mul_comm (Gamma ((n:ℂ)-1/2+m+1)),
      div_self (mul_ne_zero hGb hGa), one_mul]
  unfold toroidalP
  rw [hPm, ← legTor_P_neg_degree _ _ hc1, show -((n:ℂ)-1/2)-1 = -n-1/2 by ring,
    associated_hypergeometric_18 _ _ (legInt_one_lt_mem hc1) (by simp; linarith),
    legInt_legendreBranchPower_real _ hc1,
    show ((c:ℂ))^2 - 1 = ((s^2:ℝ):ℂ) by
      rw [hcdef, hsdef]; push_cast; linear_combination (Complex.cosh_sq_sub_sinh_sq (ξ:ℂ)),
    legInt_cpow_ofReal (r := s^2) (by positivity), Real.log_pow,
    show (Real.sinh ξ:ℂ) = (s:ℂ) from rfl, show (Real.cosh ξ:ℂ) = (c:ℂ) from rfl,
    show (n:ℂ)-1/2+m+1 = n+m+1/2 by ring, show (n:ℂ)-1/2-m+1 = n-m+1/2 by ring,
    legInt_toroidal_value n m _ hq0 (by linarith) hs0,
    show (-(m:ℂ)) = -(m:ℂ) from rfl]
  congr 2
  push_cast; ring_nf

/-- toroidalQ integral, from Whipple's formula 14.9.16 and DLMF 14.12.4. -/
@[dlmf 14.19.E5]
theorem toroidalQ_integral (n m : ℕ) (hmn : m ≤ n) {ξ : ℝ} (hξ : 0 < ξ) :
    HasIntegralAtTop (fun t : ℝ => Gamma (n+1/2)/(Gamma (n+m+1/2)*Gamma (n-m+1/2))*Real.cosh (m*t)/(Real.cosh ξ+Real.cosh t*Real.sinh ξ:ℂ)^(n+1/2:ℂ)) 0 (toroidalQ n m (Real.cosh ξ)) := by
  have hc1 : 1 < Real.cosh ξ := Real.one_lt_cosh.mpr hξ.ne'
  have hs : 0 < Real.sinh ξ := Real.sinh_pos_iff.mpr hξ
  set c := Real.cosh ξ with hcdef
  set s := Real.sinh ξ with hsdef
  have hcs : c^2 - 1 = s^2 := by rw [hcdef, hsdef]; nlinarith [Real.cosh_sq_sub_sinh_sq ξ]
  obtain ⟨hpt, hbp⟩ := legTor_point hc1 hs hcs
  have hy : 1 < c/s := by
    rw [one_lt_div hs]; nlinarith [Real.cosh_sq_sub_sinh_sq ξ, Real.sinh_lt_cosh ξ]
  have hW := olverQ_whipple_real ((n:ℂ)-1/2) (m:ℂ) c hc1
  rw [hpt, hbp, show -((n:ℂ)-1/2)-1/2 = -(n:ℂ) by ring] at hW
  have hI := legInt_associatedP_cosh_integral (ν := -(m:ℂ)-1/2) (μ := (n:ℂ))
    (by simp; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)])
    (by simp; have : (m:ℝ) ≤ n := by exact_mod_cast hmn
        linarith) hy
  unfold toroidalQ
  rw [hW]
  have hK := hI.const_mul ((π/2:ℂ)^(1/2:ℂ) * exp (-(Real.log s:ℂ)/2))
  unfold HasIntegralAtTop at hK ⊢
  refine hK.congr fun R => ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hcm : (c^2/s^2 - 1) = 1/s^2 := by field_simp; linarith
  have hY : 0 < c + Real.cosh t * s := by positivity
  rw [show -(m:ℂ)-1/2+n+1 = n-m+1/2 by ring, show (n:ℂ)-(-m-1/2) = n+m+1/2 by ring,
    show (-(m:ℂ)-1/2+1/2)*t = -(m*t) by ring, Complex.cosh_neg,
    show ((c/s:ℝ):ℂ)^2-1 = ((1/s^2:ℝ):ℂ) by rw [← hcm]; push_cast; ring,
    show ((c/s:ℝ):ℂ) + ((Real.cosh t:ℝ):ℂ) = (((c + Real.cosh t * s)/s:ℝ):ℂ) by
      have hs0 : (s:ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
      push_cast; field_simp,
    show (c:ℂ) + ((Real.cosh t:ℝ):ℂ)*(s:ℂ) = ((c + Real.cosh t * s:ℝ):ℂ) by push_cast; ring,
    show ((Real.cosh (m*t):ℝ):ℂ) = cosh ((m:ℂ)*t) by push_cast; ring_nf,
    show (π/2:ℂ) = ((π/2:ℝ):ℂ) by push_cast; ring,
    legInt_cpow_ofReal (by positivity), legInt_cpow_ofReal (by positivity),
    legInt_cpow_ofReal (by positivity), legInt_cpow_ofReal hY,
    Real.log_div hY.ne' hs.ne', Real.log_div Real.pi_pos.ne' two_ne_zero,
    show Real.log (1/s^2) = -(2*Real.log s) by
      rw [one_div, Real.log_inv, Real.log_pow]; push_cast; ring]
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) = exp (Real.log 2 / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos two_pos, ofReal_exp]; push_cast; ring_nf
  have hsp : ((Real.sqrt π : ℝ) : ℂ) = exp (Real.log π / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos Real.pi_pos, ofReal_exp]; push_cast; ring_nf
  rw [hs2, hsp]
  have e1 : exp ((Real.log (c + Real.cosh t * s) - Real.log s : ℝ) * ((n:ℂ)+1/2)) =
      exp (Real.log (c + Real.cosh t * s) * ((n:ℂ)+1/2)) * exp (-(Real.log s) * ((n:ℂ)+1/2)) := by
    rw [← exp_add]; congr 1; push_cast; ring
  rw [e1]
  have e : exp ((Real.log π - Real.log 2 : ℝ) * (1/2:ℂ)) * exp (-(Real.log s:ℂ)/2) *
      exp (Real.log 2 / 2) * exp ((-(2 * Real.log s) : ℝ) * ((n:ℂ)/2)) =
      exp (Real.log π / 2) * exp (-(Real.log s) * ((n:ℂ)+1/2)) := by
    simp only [← exp_add]; congr 1; push_cast; ring
  have hne : exp (Real.log π / 2) * exp (-(Real.log s) * ((n:ℂ)+1/2)) ≠ 0 :=
    mul_ne_zero (exp_ne_zero _) (exp_ne_zero _)
  calc _ = (exp ((Real.log π - Real.log 2 : ℝ) * (1/2:ℂ)) * exp (-(Real.log s:ℂ)/2) *
      exp (Real.log 2 / 2) * exp ((-(2 * Real.log s) : ℝ) * ((n:ℂ)/2))) /
      (exp (Real.log π / 2) * exp (-(Real.log s) * ((n:ℂ)+1/2))) *
      (Gamma (↑n + 1 / 2) / (Gamma (↑n + ↑m + 1 / 2) * Gamma (↑n - ↑m + 1 / 2)) * cosh ((m:ℂ)*t) /
        exp (Real.log (c + Real.cosh t * s) * ((n:ℂ)+1/2))) := by ring
    _ = _ := by rw [e, div_self hne, one_mul]

/-! ### Helpers for the Fourier series 14.19.6 (prefix `legFS_`) -/

/-- Regrouping a summable double series on `ℕ × ℕ` along the diagonals `j - k = n ≥ 0` and
`k - j = n + 1`. -/
theorem legFS_diag_split {F : ℕ × ℕ → ℂ} {P : ℂ} {gp gm : ℕ → ℂ} (hF : HasSum F P)
    (hp : ∀ n, HasSum (fun k => F (k+n, k)) (gp n))
    (hm : ∀ n, HasSum (fun k => F (k, k+n+1)) (gm n)) :
    ∃ a b, HasSum gp a ∧ HasSum gm b ∧ a + b = P := by
  set ep : ℕ × ℕ → ℕ × ℕ := fun p => (p.2 + p.1, p.2) with hep
  set em : ℕ × ℕ → ℕ × ℕ := fun p => (p.2, p.2 + p.1 + 1) with hem
  have ip : Function.Injective ep := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [hep, Prod.mk.injEq] at h; ext <;> simp <;> omega
  have im : Function.Injective em := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [hem, Prod.mk.injEq] at h; ext <;> simp <;> omega
  have hbij : Function.Bijective (Sum.elim ep em) := by
    refine ⟨?_, ?_⟩
    · rintro (⟨a, b⟩ | ⟨a, b⟩) (⟨c, d⟩ | ⟨c, d⟩) h <;>
        simp only [Sum.elim_inl, Sum.elim_inr, hep, hem, Prod.mk.injEq] at h
      · congr 1; ext <;> simp <;> omega
      · omega
      · omega
      · congr 1; ext <;> simp <;> omega
    · rintro ⟨j, k⟩
      by_cases hk : k ≤ j
      · exact ⟨Sum.inl (j - k, k), by simp [hep]; omega⟩
      · exact ⟨Sum.inr (k - j - 1, j), by simp [hem]; omega⟩
  set e := Equiv.ofBijective _ hbij
  have hFe : HasSum (F ∘ e) P := e.hasSum_iff.mpr hF
  have sp : Summable (F ∘ ep) := hF.summable.comp_injective ip
  have sm : Summable (F ∘ em) := hF.summable.comp_injective im
  have hsum : HasSum (F ∘ e) (∑' p, (F ∘ ep) p + ∑' p, (F ∘ em) p) :=
    HasSum.sum (f := F ∘ e) sp.hasSum sm.hasSum
  have hP := hFe.unique hsum
  refine ⟨_, _, ?_, ?_, hP.symm⟩
  · exact sp.hasSum.prod_fiberwise fun n => by simpa [hep, add_comm] using hp n
  · exact sm.hasSum.prod_fiberwise fun n => by simpa [hem, add_comm, add_assoc] using hm n

/-- Absolute convergence of the binomial series `∑ (α)_j z^j/j!` for `|z| < 1`. -/
theorem legFS_binom_norm_summable (α : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun j : ℕ => ‖poch α j / (j ! : ℂ) * z^j‖) := by
  set t := ‖z‖
  set r := (1 + t)/2
  have hr : r < 1 := by simp only [r]; linarith
  have hrt : 0 < r - t := by simp only [r]; linarith
  refine summable_of_ratio_norm_eventually_le hr ?_
  filter_upwards [eventually_ge_atTop ⌈‖α‖/(r - t)⌉₊] with j hj
  have hj' : ‖α‖/(r - t) ≤ j := Nat.ceil_le.mp hj
  rw [norm_norm, norm_norm, poch_succ, Nat.factorial_succ, pow_succ]
  push_cast
  have hj1 : (0:ℝ) < (j:ℝ) + 1 := by positivity
  have e : poch α j * (α + j) / (((j:ℂ)+1) * (j ! : ℂ)) * (z^j * z) =
      (poch α j / (j ! : ℂ) * z^j) * ((α + j) * z / ((j:ℂ)+1)) := by
    have : ((j:ℂ)+1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero j)
    have : (j ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
    field_simp
  rw [e, norm_mul, mul_comm r]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [norm_div, norm_mul, show ((j:ℂ)+1) = (((j:ℝ)+1 : ℝ) : ℂ) by push_cast; ring, norm_real,
    Real.norm_eq_abs, abs_of_pos hj1, div_le_iff₀ hj1]
  have h1 : ‖α + j‖ ≤ ‖α‖ + j := by
    refine (norm_add_le _ _).trans ?_; rw [Complex.norm_natCast]
  have h2 : ‖α‖ ≤ (r - t) * j := by rwa [div_le_iff₀ hrt, mul_comm] at hj'
  have ht0 : 0 ≤ t := norm_nonneg _
  have ht1 : t ≤ 1 := hz.le
  calc ‖α + j‖ * t ≤ (‖α‖ + j) * t := by gcongr
    _ ≤ ‖α‖ + j * t := by nlinarith [norm_nonneg α]
    _ ≤ (r - t) * j + j * t := by linarith
    _ ≤ r * ((j:ℝ) + 1) := by nlinarith [show (0:ℝ) ≤ j from j.cast_nonneg, hr, hrt]

/-- The diagonal `j = k + m` of the product of the binomial series in `tE` and `tE⁻¹`:
`∑_k (α)_{k+m}(α)_k t^{2k+m} E^m/((k+m)! k!) = E^m t^m (α)_m 𝐅(α, α+m; m+1; t²)`. -/
theorem legFS_fiber (α : ℂ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {E : ℂ} (hE : E ≠ 0) (m : ℕ) :
    HasSum (fun k : ℕ => (poch α (k+m) / ((k+m) ! : ℂ) * ((t:ℂ)*E)^(k+m)) *
        (poch α k / (k ! : ℂ) * ((t:ℂ)*E⁻¹)^k))
      (E^m * (t:ℂ)^m * poch α m * regularizedGaussHGFun α (α+m) (m+1) ((t:ℂ)^2)) := by
  have hz : ‖((t:ℂ)^2)‖ < 1 := by
    rw [norm_pow, norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]; nlinarith
  have hs := (summable_regularizedGaussHGFun_term α (α+m) (m+1) hz).hasSum.mul_left
    (E^m * (t:ℂ)^m * poch α m)
  rw [regularizedGaussHGFun_eq_tsum]
  convert hs using 1
  funext k
  have hG : Gamma ((m:ℂ)+1+k) = ((m+k) ! : ℂ) := by
    rw [show (m:ℂ)+1+k = ((m+k:ℕ):ℂ)+1 by push_cast; ring, Gamma_nat_eq_factorial]
  rw [hG, show k + m = m + k by ring, poch_add]
  simp only [poch]
  have h1 : ((m+k) ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h2 : (k ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h3 : E^k * E⁻¹^k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hE, one_pow]
  field_simp
  linear_combination (Polynomial.eval α (ascPochhammer ℂ m) * Polynomial.eval (α + ↑m)
    (ascPochhammer ℂ k) * ↑t ^ m * ↑t ^ (k * 2) * E ^ m * Polynomial.eval α (ascPochhammer ℂ k)) * h3

/-- The Fourier modes of `(1 - tE)^{-α} (1 - t/E)^{-α}`, `0 ≤ t < 1`, `|E| = 1`: with
`c_n = t^n (α)_n 𝐅(α, α+n; n+1; t²)`, `∑_{n ≥ 1} (Eⁿ + E⁻ⁿ) c_n = (1-tE)^{-α}(1-t/E)^{-α} - c_0`. -/
theorem legFS_binom_product (α : ℂ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {E : ℂ} (hE : ‖E‖ = 1) :
    HasSum (fun j : ℕ => (E^(j+1) + E⁻¹^(j+1)) * ((t:ℂ)^(j+1) * poch α (j+1) *
        regularizedGaussHGFun α (α+(j+1:ℕ)) ((j+1:ℕ)+1) ((t:ℂ)^2)))
      ((1 - (t:ℂ)*E)^(-α) * (1 - (t:ℂ)*E⁻¹)^(-α) -
        regularizedGaussHGFun α α 1 ((t:ℂ)^2)) := by
  have hE0 : E ≠ 0 := fun h => by rw [h, norm_zero] at hE; exact zero_ne_one hE
  have hn1 : ‖(t:ℂ)*E‖ < 1 := by
    rw [norm_mul, hE, mul_one, norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1
  have hn2 : ‖(t:ℂ)*E⁻¹‖ < 1 := by
    rw [norm_mul, norm_inv, hE, inv_one, mul_one, norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact ht1
  have hs1 := hasSum_one_sub_cpow_neg α hn1
  have hs2 := hasSum_one_sub_cpow_neg α hn2
  have hsm : Summable (fun x : ℕ × ℕ => (poch α x.1 / (x.1 ! : ℂ) * ((t:ℂ)*E)^x.1) *
      (poch α x.2 / (x.2 ! : ℂ) * ((t:ℂ)*E⁻¹)^x.2)) :=
    summable_mul_of_summable_norm (f := fun j : ℕ => poch α j / (j ! : ℂ) * ((t:ℂ)*E)^j)
      (g := fun j : ℕ => poch α j / (j ! : ℂ) * ((t:ℂ)*E⁻¹)^j)
      (legFS_binom_norm_summable α hn1) (legFS_binom_norm_summable α hn2)
  have hF := HasSum.mul hs1 hs2 hsm
  obtain ⟨a, b, ha, hb, hab⟩ := legFS_diag_split hF
    (gp := fun n => E^n * (t:ℂ)^n * poch α n * regularizedGaussHGFun α (α+n) (n+1) ((t:ℂ)^2))
    (gm := fun n => E⁻¹^(n+1) * (t:ℂ)^(n+1) * poch α (n+1) *
      regularizedGaussHGFun α (α+(n+1:ℕ)) ((n+1:ℕ)+1) ((t:ℂ)^2))
    (fun n => by
      have h := legFS_fiber α ht0 ht1 hE0 n
      exact h)
    (fun n => by
      have h := legFS_fiber α ht0 ht1 (inv_ne_zero hE0) (n+1)
      rw [inv_inv] at h
      convert h using 1
      funext k
      rw [show k + (n+1) = k + n + 1 by ring, mul_comm])
  have ha' := (hasSum_nat_add_iff' 1).mpr ha
  simp only [Finset.range_one, Finset.sum_singleton] at ha'
  have hsum := ha'.add hb
  rw [show a - (E^0 * (t:ℂ)^0 * poch α 0 * regularizedGaussHGFun α (α+(0:ℕ)) ((0:ℕ)+1) ((t:ℂ)^2)) + b
    = a + b - regularizedGaussHGFun α α 1 ((t:ℂ)^2) by simp [poch]; ring, hab] at hsum
  convert hsum using 1
  funext j
  ring

/-- `w^s (w̄)^s = (|w|²)^s` for `w ∉ (-∞, 0]`. -/
theorem legFS_cpow_mul_conj {w : ℂ} (hw : w ∈ slitPlane) (s : ℂ) :
    w^s * (starRingEnd ℂ w)^s = exp (((2 * Real.log ‖w‖ : ℝ) : ℂ) * s) := by
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  have hc0 : starRingEnd ℂ w ≠ 0 := (map_ne_zero _).mpr hw0
  have harg : w.arg ≠ π := by
    intro h
    rw [mem_slitPlane_iff_arg] at hw
    exact hw.1 h
  rw [cpow_def_of_ne_zero hw0, cpow_def_of_ne_zero hc0, ← exp_add, log_conj w harg, ← add_mul,
    add_conj, log_re]

/-- Positive real powers through the real logarithm. -/
theorem legFS_ofReal_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x:ℂ)^s = exp (((Real.log x : ℝ) : ℂ) * s) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ← ofReal_log hx.le]

/-- The closed form behind DLMF 14.19.6: with `t = e^{-ξ}`, `E = e^{iphi}`,
`√π (1-t²)^μ e^{-ξ/2} (1-tE)^{-μ-1/2} (1-t/E)^{-μ-1/2} = (π/2)^{1/2} sinh^μ ξ (cosh ξ - cos phi)^{-μ-1/2}`. -/
theorem legFS_toroidal_rhs (μ : ℂ) {ξ : ℝ} (hξ : 0 < ξ) (phi : ℝ) :
    Real.sqrt π * (1 - (Real.exp (-2*ξ):ℂ))^μ / exp (ξ/2) *
      ((1 - (Real.exp (-ξ):ℂ)*exp (phi*I))^(-(μ+1/2)) * (1 - (Real.exp (-ξ):ℂ)*(exp (phi*I))⁻¹)^(-(μ+1/2))) =
    (π/2:ℂ)^(1/2:ℂ)*(Real.sinh ξ:ℂ)^μ/(Real.cosh ξ-Real.cos phi:ℂ)^(μ+1/2) := by
  set t := Real.exp (-ξ) with htdef
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  set w : ℂ := 1 - (t:ℂ)*exp (phi*I) with hwdef
  have hEinv : (exp (phi*I))⁻¹ = starRingEnd ℂ (exp (phi*I)) := by
    rw [← exp_conj, ← exp_neg]; congr 1; simp [map_mul, conj_ofReal]
  have hconj : 1 - (t:ℂ)*(exp (phi*I))⁻¹ = starRingEnd ℂ w := by
    rw [hwdef, hEinv]; simp [map_sub, map_mul, conj_ofReal]
  have hwre : 0 < w.re := by
    rw [hwdef, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, add_re, I_re, I_im, mul_zero,
      zero_mul, sub_zero, mul_one, add_im, mul_im, zero_add]
    nlinarith [Real.cos_le_one phi]
  have hw : w ∈ slitPlane := Or.inl hwre
  set m : ℝ := 1 - 2*t*Real.cos phi + t^2 with hm
  have hnorm : ‖w‖^2 = m := by
    rw [← normSq_eq_norm_sq, hwdef, exp_mul_I, ← ofReal_cos, ← ofReal_sin, normSq_apply]
    simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, add_re, I_re, I_im, mul_zero,
      zero_mul, sub_zero, mul_one, add_im, mul_im, zero_add, sub_im, one_im, zero_sub]
    rw [hm]; nlinarith [Real.sin_sq_add_cos_sq phi]
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr (slitPlane_ne_zero hw)
  have hm0 : 0 < m := by rw [← hnorm]; positivity
  have hlogm : 2 * Real.log ‖w‖ = Real.log m := by
    rw [← hnorm, Real.log_pow]; push_cast; ring
  rw [hconj, legFS_cpow_mul_conj hw, hlogm]
  -- real logarithms
  have h2t : Real.exp (-2*ξ) = t^2 := by rw [htdef, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hsinh : Real.sinh ξ = (1 - t^2) / (2*t) := by
    rw [Real.sinh_eq, htdef, Real.exp_neg]; field_simp
  have hcc : Real.cosh ξ - Real.cos phi = m / (2*t) := by
    rw [hm, Real.cosh_eq, htdef, Real.exp_neg]; field_simp; ring
  have ht2 : 0 < 1 - t^2 := by nlinarith
  have hlt : Real.log t = -ξ := by rw [htdef, Real.log_exp]
  have hL1 : Real.log (Real.sinh ξ) = Real.log (1 - t^2) - Real.log 2 + ξ := by
    rw [hsinh, Real.log_div ht2.ne' (by positivity), Real.log_mul two_ne_zero ht0.ne', hlt]; ring
  have hL2 : Real.log (Real.cosh ξ - Real.cos phi) = Real.log m - Real.log 2 + ξ := by
    rw [hcc, Real.log_div hm0.ne' (by positivity), Real.log_mul two_ne_zero ht0.ne', hlt]; ring
  have hL3 : Real.log (π/2) = Real.log π - Real.log 2 := Real.log_div Real.pi_pos.ne' two_ne_zero
  have hsq : (Real.sqrt π : ℂ) = exp (((Real.log π : ℝ) : ℂ) * (1/2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos Real.pi_pos, ofReal_exp]; push_cast; ring_nf
  have hsinh0 : 0 < Real.sinh ξ := Real.sinh_pos_iff.mpr hξ
  have hcc0 : 0 < Real.cosh ξ - Real.cos phi := by
    have := Real.one_lt_cosh.mpr hξ.ne'; linarith [Real.cos_le_one phi]
  rw [show (1 - (Real.exp (-2*ξ):ℂ)) = ((1 - t^2 : ℝ) : ℂ) by rw [h2t]; push_cast; ring,
    legFS_ofReal_cpow ht2, hsq, show (π/2:ℂ) = ((π/2 : ℝ) : ℂ) by push_cast; ring,
    legFS_ofReal_cpow (by positivity), legFS_ofReal_cpow hsinh0,
    show (Real.cosh ξ - Real.cos phi : ℂ) = ((Real.cosh ξ - Real.cos phi : ℝ) : ℂ) by push_cast; ring,
    legFS_ofReal_cpow hcc0, hL1, hL2, hL3]
  simp only [← exp_add, ← exp_sub]
  congr 1
  push_cast
  ring

/-- The hypergeometric form of `𝑸^μ_{n-1/2}(cosh ξ)` in terms of `t = e^{-ξ}` (DLMF 14.19.3). -/
theorem legFS_toroidal_coef (μ : ℂ) {ξ : ℝ} (hξ : 0 < ξ) (n : ℕ) :
    olverQ ((n:ℂ)-1/2) μ (Real.cosh ξ) = Real.sqrt π * (1 - (Real.exp (-2*ξ):ℂ))^μ / exp (ξ/2) *
      ((Real.exp (-ξ):ℂ)^n * regularizedGaussHGFun (μ+1/2) (μ+1/2+n) (n+1) ((Real.exp (-ξ):ℂ)^2)) := by
  have ht : ‖((Real.exp (-ξ):ℂ))^2‖ < 1 := by
    rw [norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have : Real.exp (-ξ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    nlinarith [Real.exp_pos (-ξ)]
  have h2 : ((Real.exp (-ξ):ℂ))^2 = (Real.exp (-2*ξ):ℂ) := by
    rw [← ofReal_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  rw [toroidalQ_hypergeometric (n:ℂ) μ hξ, ← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ ht, h2,
    show (n:ℂ)+μ+1/2 = μ+1/2+n by ring]
  have he : exp (((n:ℂ)+1/2)*ξ) = exp (ξ/2) * (((Real.exp (-ξ):ℂ))^n)⁻¹ := by
    rw [← ofReal_pow, ← Real.exp_nat_mul, ofReal_exp, ← exp_neg, ← exp_add]; congr 1; push_cast; ring
  rw [he]
  have : exp ((ξ:ℂ)/2) ≠ 0 := exp_ne_zero _
  have : ((Real.exp (-ξ):ℂ))^n ≠ 0 := pow_ne_zero _ (ofReal_ne_zero.mpr (Real.exp_pos _).ne')
  field_simp

/-- DLMF 14.19.6: for `Re μ > -1/2`, `ξ > 0` and real `φ`, `(π/2)^{1/2} sinh^μ ξ/(cosh ξ - cos
φ)^{μ+1/2} = 𝑸^μ_{-1/2}(cosh ξ) + 2 Σ_{n≥1} Γ(μ+n+1/2)/Γ(μ+1/2) 𝑸^μ_{n-1/2}(cosh ξ) cos(nφ)`, as a
convergent series. -/
@[dlmf 14.19.E6]
theorem toroidalQ_fourier {μ : ℂ} (hμ : -1/2 < μ.re) {ξ : ℝ} (hξ : 0 < ξ) (phi : ℝ) :
    HasSum (fun j : ℕ => let n:=j+1; 2*Gamma (μ+n+1/2)/Gamma (μ+1/2)*olverQ (n-1/2) μ (Real.cosh ξ)*Real.cos (n*phi)) ((π/2:ℂ)^(1/2:ℂ)*(Real.sinh ξ:ℂ)^μ/(Real.cosh ξ-Real.cos phi:ℂ)^(μ+1/2)-olverQ (-1/2) μ (Real.cosh ξ)) := by
  have ht0 : 0 ≤ Real.exp (-ξ) := (Real.exp_pos _).le
  have ht1 : Real.exp (-ξ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hE : ‖exp ((phi:ℂ)*I)‖ = 1 := norm_exp_ofReal_mul_I phi
  have h := (legFS_binom_product (μ+1/2) ht0 ht1 hE).mul_left
    (Real.sqrt π * (1 - (Real.exp (-2*ξ):ℂ))^μ / exp (ξ/2))
  have hα : ∀ k : ℕ, μ+1/2 ≠ -(k:ℂ) := fun k hk => by
    have := congrArg re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have h0 := legFS_toroidal_coef μ hξ 0
  simp only [Nat.cast_zero, pow_zero, one_mul, add_zero, zero_add, zero_sub] at h0
  rw [mul_sub, legFS_toroidal_rhs μ hξ phi] at h
  rw [show (-1/2:ℂ) = -(1/2) by ring, h0]
  convert h using 1
  funext j
  simp only
  rw [legFS_toroidal_coef μ hξ (j+1)]
  have hG := Gamma_add_nat_div_Gamma_eq (n := j+1) (μ+1/2) hα
  rw [show μ+((j+1:ℕ):ℂ)+1/2 = μ+1/2+((j+1:ℕ):ℂ) by ring, mul_div_assoc, hG]
  have hc : ((Real.cos (((j+1:ℕ):ℝ)*phi) : ℝ) : ℂ) =
      (exp ((phi:ℂ)*I)^(j+1) + (exp ((phi:ℂ)*I))⁻¹^(j+1))/2 := by
    rw [ofReal_cos, Complex.cos, ← exp_nat_mul, inv_pow, ← exp_nat_mul, ← exp_neg]
    congr 2 <;> push_cast <;> ring_nf
  rw [hc]
  simp only [poch]
  ring

/-- DLMF 14.19.7 (Whipple): for natural `n, m` and `ξ > 0`, `P^m_{n-1/2}(cosh ξ) =
Γ(n+m+1/2)/Γ(n-m+1/2) (2/(π sinh ξ))^{1/2} 𝑸^n_{m-1/2}(coth ξ)`. -/
@[dlmf 14.19.E7]
theorem toroidal_whipple_P (n m : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    toroidalP n m (Real.cosh ξ)=Gamma (n+m+1/2)/Gamma (n-m+1/2)*(2/(π*Real.sinh ξ):ℂ)^(1/2:ℂ)*toroidalQ m n (Real.cosh ξ/Real.sinh ξ) := by
  have hs : 0 < Real.sinh ξ := Real.sinh_pos_iff.mpr hξ
  have ht : 1 < Real.cosh ξ := Real.one_lt_cosh.mpr hξ.ne'
  have hcs : Real.cosh ξ^2 - 1 = Real.sinh ξ^2 := by rw [Real.cosh_sq]; ring
  have hy : 1 < Real.cosh ξ / Real.sinh ξ := by
    rw [lt_div_iff₀ hs]; linarith [Real.sinh_lt_cosh ξ]
  have hys : (Real.cosh ξ / Real.sinh ξ)^2 - 1 = (1/Real.sinh ξ)^2 := by
    field_simp; linarith
  obtain ⟨h1, h2⟩ := legTor_point hy (by positivity) hys
  rw [show Real.cosh ξ / Real.sinh ξ / (1 / Real.sinh ξ) = Real.cosh ξ by field_simp] at h1
  have hG1 : Gamma ((n:ℂ)+m+1/2) ≠ 0 := by
    have := legTor_Gamma_half_ne ((n:ℤ)+m); push_cast at this; exact this
  have hG2 : Gamma ((n:ℂ)-m+1/2) ≠ 0 := by
    have := legTor_Gamma_half_ne ((n:ℤ)-m); push_cast at this; exact this
  unfold toroidalQ toroidalP
  rw [olverQ_whipple_real _ _ _ hy, h1, h2, show -((m:ℂ)-1/2)-1/2 = -(m:ℂ) by ring,
    show -(n:ℂ)-1/2 = -((n:ℂ)-1/2)-1 by ring, legTor_P_neg_degree _ _ ht,
    associatedP_negative_integer_order _ m ?_ (Or.inl (by simp; linarith))]
  · rw [show (2/(π*Real.sinh ξ):ℂ) = ((2/π/Real.sinh ξ:ℝ):ℂ) by push_cast; ring,
      legTor_cpow_half (by positivity) hs,
      show (n:ℂ)-1/2-m+1 = n-m+1/2 by ring, show (n:ℂ)-1/2+m+1 = n+m+1/2 by ring,
      Real.log_div one_ne_zero hs.ne', Real.log_one]
    have hpi : ((2/π:ℝ):ℂ)^(1/2:ℂ) * (π/2:ℂ)^(1/2:ℂ) = 1 := by
      rw [show (π/2:ℂ) = ((π/2:ℝ):ℂ) by push_cast; ring,
        ← mul_cpow_ofReal_nonneg (by positivity) (by positivity),
        ← ofReal_mul, show 2/π*(π/2) = (1:ℝ) by field_simp, ofReal_one, one_cpow]
    have he : exp (-(Real.log (Real.sinh ξ):ℂ)/2) * exp (-((0 - Real.log (Real.sinh ξ):ℝ):ℂ)/2) = 1 := by
      rw [← exp_add]; push_cast; ring_nf; exact exp_zero
    have h3 := mul_inv_cancel₀ hG1
    have h4 := mul_inv_cancel₀ hG2
    set P := associatedP ((n:ℂ)-1/2) m (Real.cosh ξ)
    set X := Gamma ((n:ℂ)+m+1/2) * (Gamma ((n:ℂ)+m+1/2))⁻¹
    set Y := Gamma ((n:ℂ)-m+1/2) * (Gamma ((n:ℂ)-m+1/2))⁻¹
    set Z := ((2/π:ℝ):ℂ)^(1/2:ℂ) * (π/2:ℂ)^(1/2:ℂ)
    set W := exp (-(Real.log (Real.sinh ξ):ℂ)/2) * exp (-((0 - Real.log (Real.sinh ξ):ℝ):ℂ)/2)
    linear_combination (-P)*((Y*Z*W)*h3 + (Z*W)*h4 + W*hpi + he)
  · intro k hk
    have := congrArg Complex.re hk
    simp at this
    have h' : ((2*n + 1 + 2*k : ℤ):ℝ) = ((2*m:ℤ):ℝ) := by push_cast; linarith
    have := Int.cast_inj.mp h'
    omega

/-- DLMF 14.19.8 (Whipple): for natural `n, m` and `ξ > 0`, `𝑸^m_{n-1/2}(cosh ξ) =
Γ(m-n+1/2)/Γ(m+n+1/2) (π/(2 sinh ξ))^{1/2} P^n_{m-1/2}(coth ξ)`. -/
@[dlmf 14.19.E8]
theorem toroidal_whipple_Q (n m : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    toroidalQ n m (Real.cosh ξ)=Gamma (m-n+1/2)/Gamma (m+n+1/2)*(π/(2*Real.sinh ξ):ℂ)^(1/2:ℂ)*toroidalP m n (Real.cosh ξ/Real.sinh ξ) := by
  have hs : 0 < Real.sinh ξ := Real.sinh_pos_iff.mpr hξ
  have ht : 1 < Real.cosh ξ := Real.one_lt_cosh.mpr hξ.ne'
  have hcs : Real.cosh ξ^2 - 1 = Real.sinh ξ^2 := by rw [Real.cosh_sq]; ring
  have hy : 1 < Real.cosh ξ / Real.sinh ξ := by
    rw [lt_div_iff₀ hs]; linarith [Real.sinh_lt_cosh ξ]
  obtain ⟨h1, h2⟩ := legTor_point ht hs hcs
  unfold toroidalQ toroidalP
  rw [olverQ_whipple_real _ _ _ ht, h1, h2, show -((n:ℂ)-1/2)-1/2 = -(n:ℂ) by ring,
    show -(m:ℂ)-1/2 = -((m:ℂ)-1/2)-1 by ring, legTor_P_neg_degree _ _ hy,
    associatedP_negative_integer_order _ n ?_ (Or.inl (by
      rw [show ((Real.cosh ξ / Real.sinh ξ : ℝ):ℂ) - 1 = ((Real.cosh ξ / Real.sinh ξ - 1 : ℝ):ℂ) by
        push_cast; ring, ofReal_re]; linarith))]
  · rw [show (π/(2*Real.sinh ξ):ℂ) = ((π/2/Real.sinh ξ:ℝ):ℂ) by push_cast; ring,
      legTor_cpow_half (by positivity) hs,
      show ((π/2:ℝ):ℂ) = (π/2:ℂ) by push_cast; ring,
      show (m:ℂ)-1/2-n+1 = m-n+1/2 by ring, show (m:ℂ)-1/2+n+1 = m+n+1/2 by ring]
    ring
  · intro k hk
    have := congrArg Complex.re hk
    simp at this
    have h' : ((2*m + 1 + 2*k : ℤ):ℝ) = ((2*n:ℤ):ℝ) := by push_cast; linarith
    have := Int.cast_inj.mp h'
    omega

end DLMF.Legendre
