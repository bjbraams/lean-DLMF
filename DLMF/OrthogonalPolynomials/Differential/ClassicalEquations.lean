/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import DLMF.OrthogonalPolynomials.Topics
public import DLMF.OrthogonalPolynomials.Explicit

/-!
# Differential equations and derivatives of classical polynomials

Polynomial continuation of differential identities and the classical orthogonal-polynomial
equations.

Source references and common attribution are retained in
`DLMF.OrthogonalPolynomials.Differential`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter

open scoped Real Nat Topology

open DLMF.Hypergeometric

open DLMF.Confluent

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-- Identity under the stated parameter and domain assumptions: `derivative (hermite (n + 1)) = C
(n + 1 : ℤ) * hermite n`. -/
@[dlmf 18.9.E27]
theorem hermite_derivative (n : ℕ) :
    derivative (hermite (n + 1)) = C (n + 1 : ℤ) * hermite n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hermite_succ (n + 1)]
    simp only [derivative_sub, derivative_mul, derivative_X, one_mul]
    rw [ih]
    simp only [derivative_mul, derivative_C, zero_mul, zero_add]
    rw [hermite_succ n]
    push_cast
    simp only [map_add, map_natCast, map_one]
    ring

/-- The terminating Gauss series has infinite radius, including singular lower parameters. -/
theorem hasFPowerSeriesOnBall_gauss_neg_nat (n : ℕ) (b c : ℂ) :
    HasFPowerSeriesOnBall (₂F₁ (-(n : ℂ)) b c)
      (FormalMultilinearSeries.ofScalars ℂ (gaussHGCoeff (-(n : ℂ)) b c)) 0 ⊤ := by
  have hz (k : ℕ) (hk : n < k) : gaussHGCoeff (-(n : ℂ)) b c k = 0 := by
    simp [gaussHGCoeff, poch_neg_nat_eq_zero hk]
  refine ⟨?_, by simp, ?_⟩
  · rw [FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero _ (n + 1)]
    intro k
    simp [FormalMultilinearSeries.ofScalars, hz (k + (n + 1)) (by omega)]
  · intro z _
    simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add]
    rw [ordinaryHypergeometric_eq_sum_neg_nat]
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hnk : n < k := by simpa using hk
    simp [hz k hnk]

/-- The Gauss equation for a terminating series holds at every complex point. -/
theorem gauss_neg_nat_ode (n : ℕ) (b : ℂ) {c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (z : ℂ) :
    z * (1 - z) * deriv (deriv (₂F₁ (-(n : ℂ)) b c)) z +
      (c - (-(n : ℂ) + b + 1) * z) * deriv (₂F₁ (-(n : ℂ)) b c) z +
      n * b * ₂F₁ (-(n : ℂ)) b c z = 0 := by
  have h := (hasFPowerSeriesOnBall_gauss_neg_nat n b c).ode_of_recurrence
    (A := 1) (B := -(n : ℂ) + b + 1) (C := -(n : ℂ) * b) (D := c)
    (fun k => by rw [gaussHGCoeff_recurrence hc]; ring) (z := z) (by simp)
  linear_combination h

/-- The affine substitution used in the Jacobi and Gegenbauer definitions. -/
theorem deriv_half_shift (f : ℂ → ℂ) :
    deriv (fun z => f ((1 - z) / 2)) = fun z => (-1 / 2 : ℂ) * deriv f ((1 - z) / 2) := by
  funext z
  change deriv (fun w => (fun t => f (t / 2)) (1 - w)) z = _
  rw [deriv_comp_const_sub (fun t : ℂ => f (t / 2)) 1 z]
  have he : (fun t : ℂ => f (t / 2)) = fun t => f ((1 / 2) * t) := by
    funext t
    congr 1
    ring
  rw [he, deriv_comp_mul_left]
  simp only [smul_eq_mul, show (1 / 2 : ℂ) * (1 - z) = (1 - z) / 2 by ring]
  ring

/-- Identity under the stated parameter and domain assumptions: `(1 - x ^ 2) * deriv (deriv
(jacobiPolyP α β n)) x + (β - α - (α + β + 2) * x) * deriv (jacobiPolyP α β n) x + n * (n + α
+ β + 1) * jacobiPolyP α β n x = 0`. -/
@[dlmf 18.8.T1]
theorem jacobi_differential_equation {α β : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    (1 - x ^ 2) * deriv (deriv (jacobiPolyP α β n)) x +
      (β - α - (α + β + 2) * x) * deriv (jacobiPolyP α β n) x +
      n * (n + α + β + 1) * jacobiPolyP α β n x = 0 := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have ho := gauss_neg_nat_ode n (n + α + β + 1) hc ((1 - x) / 2)
  have he : jacobiPolyP α β n = fun z => poch (α + 1) n / (n.factorial : ℂ) *
      ₂F₁ (-(n : ℂ)) (n + α + β + 1) (α + 1) ((1 - z) / 2) := rfl
  rw [he]
  simp only [deriv_const_mul_field', deriv_half_shift]
  linear_combination (poch (α + 1) n / (n.factorial : ℂ)) * ho

/-- Identity under the stated parameter and domain assumptions: `(1 - x ^ 2) * deriv (deriv
(ultrasphPoly lam n)) x - (2 * lam + 1) * x * deriv (ultrasphPoly lam n) x + n * (n + 2 * lam)
* ultrasphPoly lam n x = 0`. -/
@[dlmf 18.8.T1]
theorem ultrasphPoly_differential_equation {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) (x : ℂ) :
    (1 - x ^ 2) * deriv (deriv (ultrasphPoly lam n)) x -
      (2 * lam + 1) * x * deriv (ultrasphPoly lam n) x + n * (n + 2 * lam) * ultrasphPoly lam n x
          = 0 := by
  have hc : ∀ k : ℕ, lam + 1 / 2 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith)
  have ho := gauss_neg_nat_ode n (n + 2 * lam) hc ((1 - x) / 2)
  have he : ultrasphPoly lam n = fun z => poch (2 * lam) n / (n.factorial : ℂ) *
      ₂F₁ (-(n : ℂ)) (n + 2 * lam) (lam + 1 / 2) ((1 - z) / 2) := rfl
  rw [he]
  simp only [deriv_const_mul_field', deriv_half_shift]
  linear_combination (poch (2 * lam) n / (n.factorial : ℂ)) * ho

/-- Identity under the stated parameter and domain assumptions: `(1 - x ^ 2) * deriv (deriv
(legendrePolyP n)) x - 2 * x * deriv (legendrePolyP n) x + n * (n + 1) * legendrePolyP n x =
0`. -/
@[dlmf 18.8.T1]
theorem legendre_differential_equation (n : ℕ) (x : ℂ) :
    (1 - x ^ 2) * deriv (deriv (legendrePolyP n)) x -
      2 * x * deriv (legendrePolyP n) x + n * (n + 1) * legendrePolyP n x = 0 := by
  have h := jacobi_differential_equation (α := 0) (β := 0) (by norm_num) n x
  change (1 - x ^ 2) * deriv (deriv (jacobiPolyP 0 0 n)) x -
    2 * x * deriv (jacobiPolyP 0 0 n) x + n * (n + 1) * jacobiPolyP 0 0 n x = 0
  linear_combination h

/-- Identity under the stated parameter and domain assumptions: `x * deriv (deriv (laguerrePolyL α
n)) x + (α + 1 - x) * deriv (laguerrePolyL α n) x + n * laguerrePolyL α n x = 0`. -/
@[dlmf 18.8.T1]
theorem laguerrePolyL_differential_equation {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    x * deriv (deriv (laguerrePolyL α n)) x + (α + 1 - x) * deriv (laguerrePolyL α n) x + n
        * laguerrePolyL α n x = 0 := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have ho := (hasFPowerSeriesOnBall_kummerM (a := -(n : ℂ)) hc).ode_of_recurrence
    (A := 0) (B := 1) (C := -(n : ℂ)) (D := α + 1)
    (fun k => by rw [kummerMCoeff_recurrence hc]; ring) (z := x) (by simp)
  have he : laguerrePolyL α n = fun z => poch (α + 1) n / (n.factorial : ℂ) *
      kummerM (-(n : ℂ)) (α + 1) z := rfl
  rw [he]
  simp only [deriv_const_mul_field']
  linear_combination (poch (α + 1) n / (n.factorial : ℂ)) * ho

/-- Identity under the stated parameter and domain assumptions: `derivative (derivative
(hermitePolyH n)) - 2 * X * derivative (hermitePolyH n) + C (2 * n : ℤ) * hermitePolyH n = 0`. -/
@[dlmf 18.8.T1]
theorem hermitePolyH_differential_equation (n : ℕ) :
    derivative (derivative (hermitePolyH n)) - 2 * X * derivative (hermitePolyH n) +
      C (2 * n : ℤ) * hermitePolyH n = 0 := by
  have hd := congrArg derivative (hermitePolyH_succ n)
  rw [hermitePolyH_derivative] at hd
  simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_X,
    zero_mul, zero_add, mul_one] at hd
  simp only [map_add, map_mul, map_natCast, map_ofNat, map_one] at hd ⊢
  linear_combination hd

/-- Identity under the stated parameter and domain assumptions: `derivative (derivative (hermite
n)) - X * derivative (hermite n) + C (n : ℤ) * hermite n = 0`. -/
@[dlmf 18.8.T1]
theorem hermite_differential_equation (n : ℕ) :
    derivative (derivative (hermite n)) - X * derivative (hermite n) + C (n : ℤ) * hermite n = 0 := by
  have hd := congrArg derivative (hermite_succ n)
  rw [hermite_derivative] at hd
  simp only [derivative_sub, derivative_mul, derivative_X, one_mul] at hd
  simp only [map_add, map_natCast, map_one] at hd ⊢
  linear_combination hd

/-! ### Extension of polynomial identities from the disk `‖(1-x)/2‖ < 1`

The Gauss contiguous relations are available for `‖z‖ < 1`. The classical polynomials are
entire in `x`, so an identity between them proved for `‖(1-x)/2‖ < 1` holds everywhere. -/

/-- The set `‖(1-x)/2‖ < 1` is open. -/
theorem isOpen_half_shift_disk : IsOpen {x : ℂ | ‖(1 - x) / 2‖ < 1} :=
  isOpen_lt (by fun_prop) continuous_const

/-- Jacobi polynomials are entire in `x`. -/
theorem analyticOnNhd_jacobiPolyP (α β : ℂ) (n : ℕ) :
    AnalyticOnNhd ℂ (fun x => jacobiPolyP α β n x) Set.univ := by
  intro x _
  unfold jacobiPolyP
  have hf : AnalyticAt ℂ (fun w : ℂ => (1 - w) / 2) x := by fun_prop (disch := norm_num)
  exact analyticAt_const.mul
    (AnalyticAt.comp (f := fun w : ℂ => (1 - w) / 2) (analyticAt_gauss_neg_nat n _ _ _) hf)

/-- Gegenbauer polynomials are entire in `x`. -/
theorem analyticOnNhd_ultrasphPoly (lam : ℂ) (n : ℕ) :
    AnalyticOnNhd ℂ (fun x => ultrasphPoly lam n x) Set.univ := by
  intro x _
  unfold ultrasphPoly
  have hf : AnalyticAt ℂ (fun w : ℂ => (1 - w) / 2) x := by fun_prop (disch := norm_num)
  exact analyticAt_const.mul
    (AnalyticAt.comp (f := fun w : ℂ => (1 - w) / 2) (analyticAt_gauss_neg_nat n _ _ _) hf)

/-- Gegenbauer polynomials are analytic in the parameter on the half-plane `-1/2 < Re λ`. -/
theorem analyticOnNhd_ultrasphPoly_param (n : ℕ) (x : ℂ) :
    AnalyticOnNhd ℂ (fun lam => ultrasphPoly lam n x) {lam : ℂ | -1 / 2 < lam.re} := by
  intro lam hlam
  have hc : ∀ k : ℕ, lam + 1 / 2 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    have := hlam
    simp only [Set.mem_ofPred_eq] at this
    linarith)
  have heq : (fun lam => ultrasphPoly lam n x) = fun lam => poch (2 * lam) n / n.factorial *
      ∑ k ∈ Finset.range (n + 1),
        gaussHGCoeff (-(n : ℂ)) (n + 2 * lam) (lam + 1 / 2) k * ((1 - x) / 2) ^ k := by
    funext lam
    unfold ultrasphPoly
    rw [ordinaryHypergeometric_eq_sum_neg_nat]
  rw [heq]
  simp only [gaussHGCoeff]
  have hpoch : ∀ (m : ℕ) (f : ℂ → ℂ), Differentiable ℂ f →
      AnalyticAt ℂ (fun lam => poch (f lam) m) lam := fun m f hf =>
    ((Polynomial.differentiable (ascPochhammer ℂ m)).comp hf).analyticAt lam
  refine (hpoch n (fun lam => 2 * lam) (by fun_prop)).div_const.mul ?_
  refine Finset.analyticAt_fun_sum (Finset.range (n + 1)) fun k _ => ?_
  have hne : poch (lam + 1 / 2) k * k.factorial ≠ 0 :=
    mul_ne_zero (poch_ne_zero_of_not_neg_nat hc k) (Nat.cast_ne_zero.mpr k.factorial_ne_zero)
  exact AnalyticAt.mul (AnalyticAt.fun_div (f := fun lam => poch (-(n : ℂ)) k * poch (n + 2 * lam) k)
    (g := fun lam => poch (lam + 1 / 2) k * k.factorial) (x := lam)
    (analyticAt_const.mul (hpoch k (fun lam => n + 2 * lam) (by fun_prop)))
    ((hpoch k (fun lam => lam + 1 / 2) (by fun_prop)).mul analyticAt_const) hne) analyticAt_const

/-- Gegenbauer polynomials are analytic at every point, in `fun_prop` form. -/
@[fun_prop]
theorem analyticAt_ultrasphPoly (lam : ℂ) (n : ℕ) (x : ℂ) :
    AnalyticAt ℂ (fun x => ultrasphPoly lam n x) x :=
  analyticOnNhd_ultrasphPoly lam n x (Set.mem_univ x)

/-- Jacobi polynomials are analytic at every point, in `fun_prop` form. -/
@[fun_prop]
theorem analyticAt_jacobiPolyP (α β : ℂ) (n : ℕ) (x : ℂ) :
    AnalyticAt ℂ (fun x => jacobiPolyP α β n x) x :=
  analyticOnNhd_jacobiPolyP α β n x (Set.mem_univ x)

/-- An identity between entire functions of `x` holds everywhere once it holds for
`‖(1-x)/2‖ < 1`. -/
theorem eq_of_eqOn_half_shift_disk {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ) (h : ∀ x : ℂ, ‖(1 - x) / 2‖ < 1 → f x = g x) : f = g :=
  DLMF.Hypergeometric.eq_of_analyticOnNhd_univ_of_eqOn hf hg isOpen_half_shift_disk
    ⟨1, by simp⟩ h

/-- Identity under the stated parameter and domain assumptions: `2 * (n + 2) * (n + α + β + 2) *
(2 * n + α + β + 2) * jacobiPolyP α β (n + 2) x = (2 * n + α + β + 3) * ((2 * n + α + β + 2) *
(2 * n + α + β + 4) * x + α ^ 2 - β ^ 2) * jacobiPolyP α β (n + 1) x - 2 * (n + α + 1) * (n +
β + 1) * (2 * n + α + β + 4) * jacobiPolyP α β n x`. -/
@[dlmf 18.9.E2]
theorem jacobi_recurrence {α β : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    2 * (n + 2) * (n + α + β + 2) * (2 * n + α + β + 2) * jacobiPolyP α β (n + 2) x =
      (2 * n + α + β + 3) * ((2 * n + α + β + 2) * (2 * n + α + β + 4) * x + α ^ 2 - β ^ 2)
          * jacobiPolyP α β (n + 1) x -
      2 * (n + α + 1) * (n + β + 1) * (2 * n + α + β + 4) * jacobiPolyP α β n x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have key : (fun x : ℂ => 2 * (n + 2) * (n + α + β + 2) * (2 * n + α + β + 2) *
      jacobiPolyP α β (n + 2) x) = fun x =>
      (2 * n + α + β + 3) * ((2 * n + α + β + 2) * (2 * n + α + β + 4) * x + α ^ 2 - β ^ 2) *
        jacobiPolyP α β (n + 1) x -
      2 * (n + α + 1) * (n + β + 1) * (2 * n + α + β + 4) * jacobiPolyP α β n x := by
    refine eq_of_eqOn_half_shift_disk (by intro x _; fun_prop) (by intro x _; fun_prop) ?_
    intro x hx
    have hrel := DLMF.Hypergeometric.contiguous_antidiagonal (a := -((n : ℂ) + 2))
      (b := (n : ℂ) + 2 + α + β + 1) (c := α + 1) hc hx
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hn2 : ((n : ℂ) + 2) ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
    have hp2 : poch (α + 1) (n + 2) = poch (α + 1) n * (α + 1 + n) * (α + 1 + (n + 1)) := by
      rw [show n + 2 = n + 1 + 1 from rfl, poch_succ, poch_succ]
      push_cast
      ring
    have hf2 : ((n + 2).factorial : ℂ) = (n + 2) * (n + 1) * n.factorial := by
      rw [show n + 2 = n + 1 + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have hP2 : jacobiPolyP α β (n + 2) x * ((n + 2) * (n + 1) * n.factorial) =
        poch (α + 1) n * (α + 1 + n) * (α + 1 + (n + 1)) *
          ₂F₁ (-((n : ℂ) + 2)) ((n : ℂ) + 2 + α + β + 1) (α + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [hp2, hf2]
      push_cast
      field_simp
    have hP1 : jacobiPolyP α β (n + 1) x * ((n + 2) * (n + 1) * n.factorial) =
        poch (α + 1) n * (α + 1 + n) * (n + 2) *
          ₂F₁ (-((n : ℂ) + 1)) ((n : ℂ) + 1 + α + β + 1) (α + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [poch_succ, Nat.factorial_succ]
      push_cast
      field_simp
    have hP0 : jacobiPolyP α β n x * ((n + 2) * (n + 1) * n.factorial) =
        poch (α + 1) n * ((n + 2) * (n + 1)) *
          ₂F₁ (-(n : ℂ)) ((n : ℂ) + α + β + 1) (α + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      field_simp
    have hM : ((n : ℂ) + 2) * (n + 1) * n.factorial ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero hn2 hn1) hf
    apply mul_right_cancel₀ hM
    rw [show -((n : ℂ) + 2) + 1 = -((n : ℂ) + 1) by ring,
      show (n : ℂ) + 2 + α + β + 1 - 1 = (n : ℂ) + 1 + α + β + 1 by ring,
      show -((n : ℂ) + 2) + 2 = -(n : ℂ) by ring,
      show (n : ℂ) + 2 + α + β + 1 - 2 = (n : ℂ) + α + β + 1 by ring] at hrel
    linear_combination (2 * (n + 2) * (n + α + β + 2) * (2 * n + α + β + 2)) * hP2 -
      ((2 * n + α + β + 3) * ((2 * n + α + β + 2) * (2 * n + α + β + 4) * x + α ^ 2 - β ^ 2)) *
        hP1 +
      (2 * (n + α + 1) * (n + β + 1) * (2 * n + α + β + 4)) * hP0 + (poch (α + 1) n) * hrel
  exact congrFun key x

/-- Identity under the stated parameter and domain assumptions: `(n + 2 : ℂ) * ultrasphPoly lam (n
+ 2) x = 2 * (n + lam + 1) * x * ultrasphPoly lam (n + 1) x - (n + 2 * lam) * ultrasphPoly lam
n x`. -/
@[dlmf 18.9.T1]
theorem ultrasphPoly_recurrence {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) (x : ℂ) :
    (n + 2 : ℂ) * ultrasphPoly lam (n + 2) x =
      2 * (n + lam + 1) * x * ultrasphPoly lam (n + 1) x - (n + 2 * lam)
          * ultrasphPoly lam n x := by
  -- the case `0 < Re λ`, from the normalized recurrence
  have hpos : ∀ μ : ℂ, 0 < μ.re → (n + 2 : ℂ) * ultrasphPoly μ (n + 2) x =
      2 * (n + μ + 1) * x * ultrasphPoly μ (n + 1) x - (n + 2 * μ) * ultrasphPoly μ n x := by
    intro μ hμ
    have h := ultrasphPoly_normalized_recurrence hμ n x
    have h1 : ∀ m : ℕ, ultrasphPoly μ m 1 = poch (2 * μ) m / m.factorial := by
      intro m
      unfold ultrasphPoly
      simp
    have h2μ : ∀ k : ℕ, 2 * μ ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
      simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
      linarith)
    have hA : poch (2 * μ) n ≠ 0 := poch_ne_zero_of_not_neg_nat h2μ n
    have hB : 2 * μ + n ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using h2μ n
    have hC : 2 * μ + (n + 1 : ℕ) ≠ 0 := by
      simpa only [ne_eq, eq_neg_iff_add_eq_zero] using h2μ (n + 1)
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hn2 : (n : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast (n + 1).succ_ne_zero
    rw [h1, h1, h1, poch_succ (2 * μ) (n + 1), poch_succ (2 * μ) n, Nat.factorial_succ,
      Nat.factorial_succ] at h
    push_cast at h hC ⊢
    field_simp at h
    apply mul_left_cancel₀ hC
    linear_combination h
  -- continuation in the parameter over the half-plane `-1/2 < Re λ`
  have hU : IsOpen {μ : ℂ | -1 / 2 < μ.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected {μ : ℂ | -1 / 2 < μ.re} :=
    (convex_halfSpace_re_gt (-1 / 2)).isPreconnected
  have hf : AnalyticOnNhd ℂ (fun μ => (n + 2 : ℂ) * ultrasphPoly μ (n + 2) x)
      {μ : ℂ | -1 / 2 < μ.re} :=
    analyticOnNhd_const.mul (analyticOnNhd_ultrasphPoly_param (n + 2) x)
  have hg : AnalyticOnNhd ℂ (fun μ => 2 * (n + μ + 1) * x * ultrasphPoly μ (n + 1) x -
      (n + 2 * μ) * ultrasphPoly μ n x) {μ : ℂ | -1 / 2 < μ.re} :=
    (((analyticOnNhd_const.mul ((analyticOnNhd_const.add analyticOnNhd_id).add
      analyticOnNhd_const)).mul analyticOnNhd_const).mul
        (analyticOnNhd_ultrasphPoly_param (n + 1) x)).sub
      ((analyticOnNhd_const.add (analyticOnNhd_const.mul analyticOnNhd_id)).mul
        (analyticOnNhd_ultrasphPoly_param n x))
  have hev : (fun μ => (n + 2 : ℂ) * ultrasphPoly μ (n + 2) x) =ᶠ[𝓝 (1 : ℂ)]
      fun μ => 2 * (n + μ + 1) * x * ultrasphPoly μ (n + 1) x - (n + 2 * μ)
          * ultrasphPoly μ n x := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0 : ℝ) < (1 : ℂ).re by simp)] with μ hμ
    exact hpos μ hμ
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf hg hconn
    (show (1 : ℂ) ∈ {μ : ℂ | -1 / 2 < μ.re} by simp; norm_num) hev hlam

/-- Identity under the stated parameter and domain assumptions: `(n + 2 : ℂ) * laguerrePolyL α (n
+ 2) x = (2 * n + α + 3 - x) * laguerrePolyL α (n + 1) x - (n + α + 1) * laguerrePolyL α n x`. -/
@[dlmf 18.9.T1]
theorem laguerrePolyL_recurrence {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    (n + 2 : ℂ) * laguerrePolyL α (n + 2) x =
      (2 * n + α + 3 - x) * laguerrePolyL α (n + 1) x - (n + α + 1) * laguerrePolyL α n x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hM := DLMF.Confluent.kummerM_contiguous_a (a := -((n + 1 : ℕ) : ℂ)) hc (z := x)
  rw [show -((n + 1 : ℕ) : ℂ) - 1 = -((n + 2 : ℕ) : ℂ) by push_cast; ring,
    show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring] at hM
  have hQ : poch (α + 1) n ≠ 0 := poch_ne_zero_of_not_neg_nat hc n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hn2 : (n : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
  simp only [laguerrePolyL]
  rw [poch_succ (α + 1) (n + 1), poch_succ (α + 1) n, Nat.factorial_succ (n + 1),
    Nat.factorial_succ n]
  push_cast at hM ⊢
  field_simp
  linear_combination ((n : ℂ) + 2) * (α + 1 + n) * hM

/-- Identity under the stated parameter and domain assumptions: `hermitePolyH (n + 2) = 2 * X *
hermitePolyH (n + 1) - C (2 * (n + 1) : ℤ) * hermitePolyH n`. -/
@[dlmf 18.9.T1]
theorem hermitePolyH_recurrence (n : ℕ) :
    hermitePolyH (n + 2) = 2 * X * hermitePolyH (n + 1) - C (2 * (n + 1) : ℤ) * hermitePolyH n := by
  rw [hermitePolyH_succ (n + 1), hermitePolyH_derivative]

/-- Identity under the stated parameter and domain assumptions: `hermite (n + 2) = X * hermite (n
+ 1) - C (n + 1 : ℤ) * hermite n`. -/
@[dlmf 18.9.T1]
theorem hermite_recurrence (n : ℕ) :
    hermite (n + 2) = X * hermite (n + 1) - C (n + 1 : ℤ) * hermite n := by
  rw [hermite_succ (n + 1), hermite_derivative]

/-- Identity under the stated parameter and domain assumptions: `jacobiPolyP α (β - 1) (n + 1) x -
jacobiPolyP (α - 1) β (n + 1) x = jacobiPolyP α β n x`. -/
@[dlmf 18.9.E3]
theorem jacobi_contiguous_sub {α β : ℂ} (hα : 0 < α.re) (n : ℕ) (x : ℂ) :
    jacobiPolyP α (β - 1) (n + 1) x - jacobiPolyP (α - 1) β (n + 1) x = jacobiPolyP α β n x := by
  have hcα : ∀ k : ℕ, α ≠ -(k : ℂ) := not_neg_nat_of_re_pos hα
  have key : (fun x : ℂ => jacobiPolyP α (β - 1) (n + 1) x - jacobiPolyP (α - 1) β (n + 1) x) =
      fun x => jacobiPolyP α β n x := by
    refine eq_of_eqOn_half_shift_disk ?_ ?_ ?_
    · exact (analyticOnNhd_jacobiPolyP _ _ _).sub (analyticOnNhd_jacobiPolyP _ _ _)
    · exact analyticOnNhd_jacobiPolyP _ _ _
    intro x hx
    have hcc := contiguous_c (a := -((n + 1 : ℕ) : ℂ)) (b := n + α + β + 1) (c := α) hcα hx
    rw [show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring] at hcc
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    unfold jacobiPolyP
    rw [show ((n + 1 : ℕ) : ℂ) + α + (β - 1) + 1 = n + α + β + 1 by push_cast; ring,
      show ((n + 1 : ℕ) : ℂ) + (α - 1) + β + 1 = n + α + β + 1 by push_cast; ring,
      show α - 1 + 1 = α by ring, poch_succ_left α n, poch_succ (α + 1) n, Nat.factorial_succ]
    push_cast at hcc ⊢
    field_simp
    linear_combination (-(poch (α + 1) n)) * hcc
  exact congrFun key x

/-- Identity under the stated parameter and domain assumptions: `(1 - x) * jacobiPolyP (α + 1) β n
x + (1 + x) * jacobiPolyP α (β + 1) n x = 2 * jacobiPolyP α β n x`. -/
@[dlmf 18.9.E4]
theorem jacobi_contiguous_add {α β : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    (1 - x) * jacobiPolyP (α + 1) β n x + (1 + x) * jacobiPolyP α (β + 1) n x = 2
        * jacobiPolyP α β n x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hc0 : α + 1 ≠ 0 := by simpa using hc 0
  have key : (fun x : ℂ => (1 - x) * jacobiPolyP (α + 1) β n x + (1 + x)
      * jacobiPolyP α (β + 1) n x) =
      fun x => 2 * jacobiPolyP α β n x := by
    refine eq_of_eqOn_half_shift_disk ?_ ?_ ?_
    · exact ((analyticOnNhd_const.sub analyticOnNhd_id).mul (analyticOnNhd_jacobiPolyP _ _ _)).add
        ((analyticOnNhd_const.add analyticOnNhd_id).mul (analyticOnNhd_jacobiPolyP _ _ _))
    · exact analyticOnNhd_const.mul (analyticOnNhd_jacobiPolyP _ _ _)
    intro x hx
    have hsb := contiguous_shift_b (a := -(n : ℂ)) (b := n + α + β + 1) (c := α + 1) hc hx
    have hcc := contiguous_c (a := -(n : ℂ)) (b := n + α + β + 1 + 1) (c := α + 1) hc hx
    have hp : (α + 1) * poch (α + 1 + 1) n = poch (α + 1) n * (α + 1 + n) := by
      rw [← poch_succ_left, poch_succ]
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    unfold jacobiPolyP
    rw [show (n : ℂ) + (α + 1) + β + 1 = n + α + β + 1 + 1 by ring,
      show (n : ℂ) + α + (β + 1) + 1 = n + α + β + 1 + 1 by ring]
    field_simp
    apply mul_left_cancel₀ hc0
    linear_combination (-2 * poch (α + 1) n * ((1 - x) / 2)) * hcc - (2 * poch (α + 1) n) * hsb +
      ((1 - x) * ₂F₁ (-(n : ℂ)) (n + α + β + 1 + 1) (α + 1 + 1) ((1 - x) / 2)) * hp
  exact congrFun key x

/-- Identity under the stated parameter and domain assumptions: `(2 * n + α + β + 3) * jacobiPolyP
α β (n + 1) x = (n + α + β + 2) * jacobiPolyP α (β + 1) (n + 1) x + (n + α + 1) * jacobiPolyP
α (β + 1) n x`. -/
@[dlmf 18.9.E5]
theorem jacobi_raise_beta {α β : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    (2 * n + α + β + 3) * jacobiPolyP α β (n + 1) x =
      (n + α + β + 2) * jacobiPolyP α (β + 1) (n + 1) x + (n + α + 1)
          * jacobiPolyP α (β + 1) n x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have key : (fun x : ℂ => (2 * n + α + β + 3) * jacobiPolyP α β (n + 1) x) =
      fun x => (n + α + β + 2) * jacobiPolyP α (β + 1) (n + 1) x +
        (n + α + 1) * jacobiPolyP α (β + 1) n x := by
    refine eq_of_eqOn_half_shift_disk ?_ ?_ ?_
    · exact analyticOnNhd_const.mul (analyticOnNhd_jacobiPolyP _ _ _)
    · exact (analyticOnNhd_const.mul (analyticOnNhd_jacobiPolyP _ _ _)).add
        (analyticOnNhd_const.mul (analyticOnNhd_jacobiPolyP _ _ _))
    intro x hx
    have hab := DLMF.Hypergeometric.contiguous_ab (a := -((n + 1 : ℕ) : ℂ)) (b := (n + 1 : ℕ) + α + β + 1)
      (c := α + 1) hc hx
    rw [show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring] at hab
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    unfold jacobiPolyP
    rw [show ((n + 1 : ℕ) : ℂ) + α + (β + 1) + 1 = (n + 1 : ℕ) + α + β + 1 + 1 by ring,
      show (n : ℂ) + α + (β + 1) + 1 = (n + 1 : ℕ) + α + β + 1 by push_cast; ring,
      poch_succ (α + 1) n, Nat.factorial_succ]
    push_cast at hab ⊢
    field_simp
    linear_combination (poch (α + 1) n * (α + 1 + n)) * hab
  exact congrFun key x

/-- Identity under the stated parameter and domain assumptions: `(n + α / 2 + β / 2 + 1) * (1 + x)
* jacobiPolyP α (β + 1) n x = (n + 1) * jacobiPolyP α β (n + 1) x + (n + β + 1) * jacobiPolyP
α β n x`. -/
@[dlmf 18.9.E6]
theorem jacobi_raise_degree_beta {α β : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    (n + α / 2 + β / 2 + 1) * (1 + x) * jacobiPolyP α (β + 1) n x =
      (n + 1) * jacobiPolyP α β (n + 1) x + (n + β + 1) * jacobiPolyP α β n x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have key : (fun x : ℂ => (n + α / 2 + β / 2 + 1) * (1 + x) * jacobiPolyP α (β + 1) n x) =
      fun x => (n + 1) * jacobiPolyP α β (n + 1) x + (n + β + 1) * jacobiPolyP α β n x := by
    refine eq_of_eqOn_half_shift_disk (by intro x _; fun_prop) (by intro x _; fun_prop) ?_
    intro x hx
    have hrel := DLMF.Hypergeometric.contiguous_a_pred_b_pred (a := -(n : ℂ))
      (b := (n : ℂ) + α + (β + 1) + 1) (c := α + 1) hc hx
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hQ : jacobiPolyP α (β + 1) n x * ((n + 1) * n.factorial) =
        poch (α + 1) n * (n + 1) *
          ₂F₁ (-(n : ℂ)) ((n : ℂ) + α + (β + 1) + 1) (α + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      field_simp
    have hP1 : jacobiPolyP α β (n + 1) x * ((n + 1) * n.factorial) =
        poch (α + 1) n * (α + 1 + n) *
          ₂F₁ (-(n : ℂ) - 1) ((n : ℂ) + α + (β + 1) + 1) (α + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [poch_succ, Nat.factorial_succ]
      push_cast
      rw [show -((n : ℂ) + 1) = -(n : ℂ) - 1 by ring,
        show (n : ℂ) + 1 + α + β + 1 = (n : ℂ) + α + (β + 1) + 1 by ring]
      field_simp
    have hP0 : jacobiPolyP α β n x * ((n + 1) * n.factorial) =
        poch (α + 1) n * (n + 1) *
          ₂F₁ (-(n : ℂ)) ((n : ℂ) + α + (β + 1) + 1 - 1) (α + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [show (n : ℂ) + α + (β + 1) + 1 - 1 = (n : ℂ) + α + β + 1 by ring]
      field_simp
    have hM : ((n : ℂ) + 1) * n.factorial ≠ 0 := mul_ne_zero hn1 hf
    apply mul_right_cancel₀ hM
    linear_combination ((n + α / 2 + β / 2 + 1) * (1 + x)) * hQ - (n + 1) * hP1 -
      (n + β + 1) * hP0 + (poch (α + 1) n * (n + 1)) * hrel
  exact congrFun key x

/-- Identity under the stated parameter and domain assumptions: `(n + lam + 2) * ultrasphPoly lam
(n + 2) x = lam * (ultrasphPoly (lam + 1) (n + 2) x - ultrasphPoly (lam + 1) n x)`. -/
@[dlmf 18.9.E7]
theorem ultrasphPoly_raise_parameter {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) (x : ℂ) :
    (n + lam + 2) * ultrasphPoly lam (n + 2) x =
      lam * (ultrasphPoly (lam + 1) (n + 2) x - ultrasphPoly (lam + 1) n x) := by
  have hc : ∀ k : ℕ, lam + 1 / 2 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith)
  have key : (fun x : ℂ => (n + lam + 2) * ultrasphPoly lam (n + 2) x) =
      fun x => lam * (ultrasphPoly (lam + 1) (n + 2) x - ultrasphPoly (lam + 1) n x) := by
    refine DLMF.Hypergeometric.eq_of_analyticOnNhd_univ_of_eqOn (by intro x _; fun_prop)
      (by intro x _; fun_prop)
      (isOpen_half_shift_disk.inter isOpen_ne :
        IsOpen ({x : ℂ | ‖(1 - x) / 2‖ < 1} ∩ {x : ℂ | x ≠ 1}))
      ⟨0, by rw [Set.mem_ofPred_eq, sub_zero, norm_div, norm_one]; norm_num, by simp⟩ ?_
    rintro x ⟨hx, hx1⟩
    have hy : (1 - x) / 2 ≠ 0 := by
      intro h
      apply hx1
      linear_combination -2 * h
    have hrel := DLMF.Hypergeometric.contiguous_ultrasphPoly_raise (a := -((n : ℂ) + 2))
      (c := lam + 1 / 2) hc hx
    have hD : 2 * ((1 - x) / 2) * (-((n : ℂ) + 2) - 2 * (lam + 1 / 2) + 2) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero two_ne_zero hy) ?_
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hrel' := (mul_eq_zero.mp hrel).resolve_left hD
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hn2 : ((n : ℂ) + 2) ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
    have hpoch : poch (2 * lam) (n + 2) = 2 * lam * (2 * lam + 1) * poch (2 * (lam + 1)) n := by
      rw [show n + 2 = n + 1 + 1 from rfl, poch_succ_left, poch_succ_left,
        show 2 * lam + 1 + 1 = 2 * (lam + 1) by ring]
      ring
    have hpoch' : poch (2 * (lam + 1)) (n + 2) =
        poch (2 * (lam + 1)) n * (2 * (lam + 1) + n) * (2 * (lam + 1) + (n + 1)) := by
      rw [show n + 2 = n + 1 + 1 from rfl, poch_succ, poch_succ]
      push_cast
      ring
    have hf2 : ((n + 2).factorial : ℂ) = (n + 2) * (n + 1) * n.factorial := by
      rw [show n + 2 = n + 1 + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have hP0 : ultrasphPoly lam (n + 2) x * ((n + 2) * (n + 1) * n.factorial) =
        2 * lam * (2 * lam + 1) * poch (2 * (lam + 1)) n *
          ₂F₁ (-((n : ℂ) + 2)) ((n : ℂ) + 2 + 2 * lam) (lam + 1 / 2) ((1 - x) / 2) := by
      unfold ultrasphPoly
      rw [hpoch, hf2]
      push_cast
      field_simp
    have hP1 : ultrasphPoly (lam + 1) (n + 2) x * ((n + 2) * (n + 1) * n.factorial) =
        poch (2 * (lam + 1)) n * (2 * (lam + 1) + n) * (2 * (lam + 1) + (n + 1)) *
          ₂F₁ (-((n : ℂ) + 2)) ((n : ℂ) + 2 + 2 * (lam + 1)) (lam + 1 + 1 / 2) ((1 - x) / 2) := by
      unfold ultrasphPoly
      rw [hpoch', hf2]
      push_cast
      field_simp
    have hP2 : ultrasphPoly (lam + 1) n x * ((n + 2) * (n + 1) * n.factorial) =
        poch (2 * (lam + 1)) n * ((n + 2) * (n + 1)) *
          ₂F₁ (-(n : ℂ)) ((n : ℂ) + 2 * (lam + 1)) (lam + 1 + 1 / 2) ((1 - x) / 2) := by
      unfold ultrasphPoly
      field_simp
    have hM : ((n : ℂ) + 2) * (n + 1) * n.factorial ≠ 0 :=
      mul_ne_zero (mul_ne_zero hn2 hn1) hf
    apply mul_right_cancel₀ hM
    set q := poch (2 * (lam + 1)) n with hq
    ring_nf at hrel' hP0 hP1 hP2 ⊢
    linear_combination (n + lam + 2) * hP0 - lam * hP1 + lam * hP2 + q * hrel'
  exact congrFun key x

/-- Identity under the stated parameter and domain assumptions: `4 * lam * (n + lam + 1) * (1 - x
^ 2) * ultrasphPoly (lam + 1) n x = -(n + 1) * (n + 2) * ultrasphPoly lam (n + 2) x + (n + 2 *
lam) * (n + 2 * lam + 1) * ultrasphPoly lam n x`. -/
@[dlmf 18.9.E8]
theorem ultrasphPoly_raise_parameter_sq {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) (x : ℂ) :
    4 * lam * (n + lam + 1) * (1 - x ^ 2) * ultrasphPoly (lam + 1) n x =
      -(n + 1) * (n + 2) * ultrasphPoly lam (n + 2) x +
      (n + 2 * lam) * (n + 2 * lam + 1) * ultrasphPoly lam n x := by
  -- the degenerate case `n = 0`, `λ = 0`
  by_cases hN : 2 * lam + n = 0
  · have hn0 : n = 0 := by
      have := congrArg Complex.re hN
      simp at this
      have h1 : (n : ℝ) < 1 := by linarith
      have h2 : n < 1 := by exact_mod_cast h1
      omega
    subst hn0
    have hl0 : lam = 0 := by simpa using hN
    subst hl0
    simp [ultrasphPoly]
  have hc : ∀ k : ℕ, lam + 1 / 2 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith)
  have key : (fun x : ℂ => 4 * lam * (n + lam + 1) * (1 - x ^ 2) * ultrasphPoly (lam + 1) n x) =
      fun x => -(n + 1) * (n + 2) * ultrasphPoly lam (n + 2) x +
        (n + 2 * lam) * (n + 2 * lam + 1) * ultrasphPoly lam n x := by
    refine eq_of_eqOn_half_shift_disk (by intro x _; fun_prop) (by intro x _; fun_prop) ?_
    intro x hx
    have hrel := DLMF.Hypergeometric.contiguous_ultrasphPoly_raise_sq (a := -((n : ℂ) + 2))
      (c := lam + 1 / 2) hc hx
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hn2 : ((n : ℂ) + 2) ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
    have hD : -((n : ℂ) + 2) * (-((n : ℂ) + 2) + 1) ≠ 0 := by
      refine mul_ne_zero (neg_ne_zero.mpr hn2) ?_
      intro h
      apply hn1
      linear_combination -h
    have hrel' := (mul_eq_zero.mp hrel).resolve_left hD
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hN1 : (2 * lam + ((n : ℂ) + 1)) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hpoch : poch (2 * lam) (n + 2) = 2 * lam * (2 * lam + 1) * poch (2 * (lam + 1)) n := by
      rw [show n + 2 = n + 1 + 1 from rfl, poch_succ_left, poch_succ_left,
        show 2 * lam + 1 + 1 = 2 * (lam + 1) by ring]
      ring
    have hpq : poch (2 * lam) n * (2 * lam + n) * (2 * lam + (n + 1)) =
        2 * lam * (2 * lam + 1) * poch (2 * (lam + 1)) n := by
      rw [← hpoch, show n + 2 = n + 1 + 1 from rfl, poch_succ, poch_succ]
      push_cast
      ring
    have hf2 : ((n + 2).factorial : ℂ) = (n + 2) * (n + 1) * n.factorial := by
      rw [show n + 2 = n + 1 + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have hP0 : ultrasphPoly lam (n + 2) x * ((n + 2) * (n + 1) * n.factorial) =
        2 * lam * (2 * lam + 1) * poch (2 * (lam + 1)) n *
          ₂F₁ (-((n : ℂ) + 2)) ((n : ℂ) + 2 + 2 * lam) (lam + 1 / 2) ((1 - x) / 2) := by
      unfold ultrasphPoly
      rw [hpoch, hf2]
      push_cast
      field_simp
    have hP1 : ultrasphPoly (lam + 1) n x * ((n + 2) * (n + 1) * n.factorial) =
        poch (2 * (lam + 1)) n * ((n + 2) * (n + 1)) *
          ₂F₁ (-(n : ℂ)) ((n : ℂ) + 2 * (lam + 1)) (lam + 1 + 1 / 2) ((1 - x) / 2) := by
      unfold ultrasphPoly
      field_simp
    have hP2a : ultrasphPoly lam n x * ((n + 2) * (n + 1) * n.factorial) =
        poch (2 * lam) n * ((n + 2) * (n + 1)) *
          ₂F₁ (-(n : ℂ)) ((n : ℂ) + 2 * lam) (lam + 1 / 2) ((1 - x) / 2) := by
      unfold ultrasphPoly
      field_simp
    have hP2 : ultrasphPoly lam n x * ((n + 2) * (n + 1) * n.factorial) *
        ((2 * lam + n) * (2 * lam + (n + 1))) =
        2 * lam * (2 * lam + 1) * poch (2 * (lam + 1)) n * ((n + 2) * (n + 1)) *
          ₂F₁ (-(n : ℂ)) ((n : ℂ) + 2 * lam) (lam + 1 / 2) ((1 - x) / 2) := by
      linear_combination ((2 * lam + n) * (2 * lam + (n + 1))) * hP2a +
        ((n + 2) * (n + 1) * ₂F₁ (-(n : ℂ)) ((n : ℂ) + 2 * lam) (lam + 1 / 2) ((1 - x) / 2)) * hpq
    have hM : ((n : ℂ) + 2) * (n + 1) * n.factorial * ((2 * lam + n) * (2 * lam + (n + 1))) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero hn2 hn1) hf) (mul_ne_zero hN hN1)
    apply mul_right_cancel₀ hM
    set q := poch (2 * (lam + 1)) n with hq
    ring_nf at hrel' hP0 hP1 hP2 ⊢
    linear_combination ((2 * lam + n) * (2 * lam + (n + 1)) * 4 * lam * (n + lam + 1) * (1 - x ^ 2)) *
        hP1 + ((2 * lam + n) * (2 * lam + (n + 1)) * (n + 1) * (n + 2)) * hP0 -
      ((2 * lam + n) * (2 * lam + (n + 1))) * hP2 +
      ((2 * lam + n) * (2 * lam + (n + 1)) * (n + 1) * (n + 2) * q * 2 * lam) * hrel'
  exact congrFun key x

/-- The Jacobi polynomial of degree one. -/
theorem jacobiPolyP_one_eq {α : ℂ} (hα : -1 < α.re) (β x : ℂ) :
    jacobiPolyP α β 1 x = (α + 1) - (α + β + 2) * ((1 - x) / 2) := by
  have h : α + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  unfold jacobiPolyP
  rw [ordinaryHypergeometric_eq_sum_neg_nat]
  simp [Finset.sum_range_succ, gaussHGCoeff, poch_zero, poch_one]
  field_simp
  ring

/-- The Gegenbauer polynomial of degree one. -/
theorem ultrasphPoly_one_eq {lam : ℂ} (hlam : -1 / 2 < lam.re) (x : ℂ) :
    ultrasphPoly lam 1 x = 2 * lam * x := by
  have h : lam + 1 / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h2 : (1 : ℂ) + lam * 2 ≠ 0 := by
    intro h'
    apply h
    linear_combination h' / 2
  have h3 : (2 : ℂ) * lam + 1 ≠ 0 := by
    intro h'
    apply h
    linear_combination h' / 2
  unfold ultrasphPoly
  rw [ordinaryHypergeometric_eq_sum_neg_nat]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, gaussHGCoeff, poch_zero, poch_one,
    Nat.cast_one, Nat.factorial_one, pow_zero, pow_one, zero_add, mul_one, div_one]
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `jacobiPolyP α β n (-x) = (-1 : ℂ)
^ n * jacobiPolyP β α n x`. -/
@[dlmf 18.6.T1]
theorem jacobi_reflection {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re) (n : ℕ) (x : ℂ) :
    jacobiPolyP α β n (-x) = (-1 : ℂ) ^ n * jacobiPolyP β α n x := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    rw [jacobiPolyP_one_eq hα, jacobiPolyP_one_eq hβ]
    ring
  | more n ih0 ih1 =>
    have h1 := jacobi_recurrence (β := β) hα n (-x)
    have h2 := jacobi_recurrence (α := β) (β := α) hβ n x
    have hA : (2 * ((n : ℂ) + 2) * (n + α + β + 2) * (2 * n + α + β + 2)) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) ?_
      all_goals
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    apply mul_left_cancel₀ hA
    rw [ih0, ih1] at h1
    linear_combination h1 - (-1 : ℂ) ^ n * h2

/-- Identity under the stated parameter and domain assumptions: `ultrasphPoly lam n (-x) = (-1 :
ℂ) ^ n * ultrasphPoly lam n x`. -/
@[dlmf 18.6.T1]
theorem ultrasphPoly_reflection {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) (x : ℂ) :
    ultrasphPoly lam n (-x) = (-1 : ℂ) ^ n * ultrasphPoly lam n x := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    rw [ultrasphPoly_one_eq hlam, ultrasphPoly_one_eq hlam]
    ring
  | more n ih0 ih1 =>
    have h1 := ultrasphPoly_recurrence hlam n (-x)
    have h2 := ultrasphPoly_recurrence hlam n x
    have hA : ((n : ℂ) + 2) ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
    apply mul_left_cancel₀ hA
    rw [ih0, ih1] at h1
    linear_combination h1 - (-1 : ℂ) ^ n * h2

/-- `(a+1)_{n+1} · a = (a)_n (a+n)(a+n+1)`. -/
theorem poch_succ_succ_mul (a : ℂ) (n : ℕ) :
    poch (a + 1) (n + 1) * a = poch a n * (a + n) * (a + n + 1) := by
  have h1 := poch_succ_left a (n + 1)
  have h2 := poch_succ a (n + 1)
  have h3 := poch_succ a n
  push_cast at h1 h2 h3
  linear_combination -h1 + h2 + (a + n + 1) * h3

/-- Identity under the stated parameter and domain assumptions: `ultrasphPoly lam (2 * n) 0 = (-1
: ℂ) ^ n * poch lam n / n.factorial`. -/
@[dlmf 18.6.T1]
theorem ultrasphPoly_even_at_zero {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) :
    ultrasphPoly lam (2 * n) 0 = (-1 : ℂ) ^ n * poch lam n / n.factorial := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    have hrec := ultrasphPoly_recurrence hlam (2 * n) 0
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have ih' : ultrasphPoly lam (2 * n) 0 * n.factorial = (-1 : ℂ) ^ n * poch lam n := by
      rw [ih]
      field_simp
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, poch_succ, Nat.factorial_succ, eq_div_iff (by
      push_cast
      exact mul_ne_zero hn1 hf)]
    push_cast at hrec ⊢
    linear_combination ((n.factorial : ℂ) / 2) * hrec - ((n : ℂ) + lam) * ih'

/-- Identity under the stated parameter and domain assumptions: `jacobiPolyP α α (2 * n) 0 = (-1 /
4 : ℂ) ^ n * poch (n + α + 1) n / n.factorial`. -/
@[dlmf 18.6.T1]
theorem jacobi_symmetric_even_at_zero {α : ℂ} (hα : -1 < α.re) (n : ℕ) :
    jacobiPolyP α α (2 * n) 0 = (-1 / 4 : ℂ) ^ n * poch (n + α + 1) n / n.factorial := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    have hrec := jacobi_recurrence (β := α) hα (2 * n) 0
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hna : ((n : ℂ) + α + 1) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hna2 : (2 * (n : ℂ) + α + 1) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have ih' : jacobiPolyP α α (2 * n) 0 * n.factorial = (-1 / 4 : ℂ) ^ n * poch (n + α + 1) n := by
      rw [ih]
      field_simp
    have hpoch : poch ((n : ℂ) + 1 + α + 1) (n + 1) * ((n : ℂ) + α + 1) =
        poch ((n : ℂ) + α + 1) n * (2 * n + α + 1) * (2 * n + α + 2) := by
      have h := poch_succ_succ_mul ((n : ℂ) + α + 1) n
      rw [show (n : ℂ) + α + 1 + 1 = (n : ℂ) + 1 + α + 1 by ring] at h
      rw [h]
      ring
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, Nat.factorial_succ, eq_div_iff (by
      push_cast
      exact mul_ne_zero hn1 hf)]
    push_cast at hrec ⊢
    have hM : (16 * ((n : ℂ) + α + 1) * (2 * n + α + 1)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hna) hna2
    apply mul_right_cancel₀ hM
    linear_combination (n.factorial : ℂ) * hrec -
      (4 * (2 * (n : ℂ) + α + 1) ^ 2 * (2 * n + α + 2)) * ih' -
      ((-1 / 4 : ℂ) ^ (n + 1) * 16 * (2 * n + α + 1)) * hpoch

/-- Jacobi polynomials with `α = β = -1/2` in hypergeometric form. -/
theorem jacobiPolyP_half_half (n : ℕ) (x : ℂ) :
    jacobiPolyP (-1 / 2) (-1 / 2) n x =
      poch (1 / 2) n / n.factorial * ₂F₁ (-(n : ℂ)) (n : ℂ) (1 / 2) ((1 - x) / 2) := by
  unfold jacobiPolyP
  rw [show (n : ℂ) + -1 / 2 + -1 / 2 + 1 = n by ring, show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num]

/-- `(1/2)_n ≠ 0`. -/
theorem poch_half_ne_zero (n : ℕ) : poch (1 / 2 : ℂ) n ≠ 0 :=
  poch_ne_zero_of_not_neg_nat (fun k hk => by
    have := congrArg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) n

/-- The three-term recurrence of `₂F₁(-n, n; 1/2; (1-x)/2)` in `n`, from the Jacobi recurrence
with `α = β = -1/2`. -/
theorem gauss_chebyshev_recurrence (n : ℕ) (x : ℂ) :
    ₂F₁ (-((n : ℂ) + 2)) ((n : ℂ) + 2) (1 / 2) ((1 - x) / 2) =
      2 * x * ₂F₁ (-((n : ℂ) + 1)) ((n : ℂ) + 1) (1 / 2) ((1 - x) / 2) -
        ₂F₁ (-(n : ℂ)) (n : ℂ) (1 / 2) ((1 - x) / 2) := by
  have jr := jacobi_recurrence (α := -1 / 2) (β := -1 / 2) (by norm_num) n x
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hn2 : ((n : ℂ) + 2) ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
  have hp : poch (1 / 2 : ℂ) n ≠ 0 := poch_half_ne_zero n
  have hp2 : poch (1 / 2 : ℂ) (n + 2) = poch (1 / 2) n * (1 / 2 + n) * (1 / 2 + (n + 1)) := by
    rw [show n + 2 = n + 1 + 1 from rfl, poch_succ, poch_succ]
    push_cast
    ring
  have hf2 : ((n + 2).factorial : ℂ) = (n + 2) * (n + 1) * n.factorial := by
    rw [show n + 2 = n + 1 + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hP2 : jacobiPolyP (-1 / 2) (-1 / 2) (n + 2) x * ((n + 2) * (n + 1) * n.factorial) =
      poch (1 / 2) n * (1 / 2 + n) * (1 / 2 + (n + 1)) *
        ₂F₁ (-((n : ℂ) + 2)) ((n : ℂ) + 2) (1 / 2) ((1 - x) / 2) := by
    rw [jacobiPolyP_half_half, hp2, hf2]
    push_cast
    field_simp
  have hP1 : jacobiPolyP (-1 / 2) (-1 / 2) (n + 1) x * ((n + 2) * (n + 1) * n.factorial) =
      poch (1 / 2) n * (1 / 2 + n) * (n + 2) *
        ₂F₁ (-((n : ℂ) + 1)) ((n : ℂ) + 1) (1 / 2) ((1 - x) / 2) := by
    rw [jacobiPolyP_half_half, poch_succ, Nat.factorial_succ]
    push_cast
    field_simp
  have hP0 : jacobiPolyP (-1 / 2) (-1 / 2) n x * ((n + 2) * (n + 1) * n.factorial) =
      poch (1 / 2) n * ((n + 2) * (n + 1)) *
        ₂F₁ (-(n : ℂ)) (n : ℂ) (1 / 2) ((1 - x) / 2) := by
    rw [jacobiPolyP_half_half]
    field_simp
  have hK : (2 * ((n : ℂ) + 2) * (n + 1) * (2 * n + 1) * (n + 1 / 2) * (n + 3 / 2) *
      poch (1 / 2) n) ≠ 0 := by
    have h1 : (2 * (n : ℂ) + 1) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h2 : ((n : ℂ) + 1 / 2) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h3 : ((n : ℂ) + 3 / 2) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simp only [ne_eq, mul_eq_zero, hp, h1, h2, h3, hn1, hn2, or_self, not_false_eq_true,
      OfNat.ofNat_ne_zero]
  have h : (2 * ((n : ℂ) + 2) * (n + 1) * (2 * n + 1) * (n + 1 / 2) * (n + 3 / 2) *
      poch (1 / 2) n) * ₂F₁ (-((n : ℂ) + 2)) ((n : ℂ) + 2) (1 / 2) ((1 - x) / 2) =
      (2 * ((n : ℂ) + 2) * (n + 1) * (2 * n + 1) * (n + 1 / 2) * (n + 3 / 2) *
      poch (1 / 2) n) * (2 * x * ₂F₁ (-((n : ℂ) + 1)) ((n : ℂ) + 1) (1 / 2) ((1 - x) / 2) -
        ₂F₁ (-(n : ℂ)) (n : ℂ) (1 / 2) ((1 - x) / 2)) := by
    linear_combination (((n : ℂ) + 2) * (n + 1) * n.factorial) * jr -
      (2 * ((n : ℂ) + 2) * (n + 1) * (2 * n + 1)) * hP2 +
      ((2 * (n : ℂ) + 2) * (2 * n + 1) * (2 * n + 3) * x) * hP1 -
      (2 * ((n : ℂ) + 1 / 2) ^ 2 * (2 * n + 3)) * hP0
  exact mul_left_cancel₀ hK h

/-- Identity under the stated parameter and domain assumptions: `(Chebyshev.T ℂ n).eval x = ₂F₁
(-(n : ℂ)) (n : ℂ) (1 / 2) ((1 - x) / 2)`. -/
@[dlmf 18.5.E11_2]
theorem chebyshevT_hypergeometric (n : ℕ) (x : ℂ) :
    (Chebyshev.T ℂ n).eval x = ₂F₁ (-(n : ℂ)) (n : ℂ) (1 / 2) ((1 - x) / 2) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [ordinaryHypergeometric_eq_sum_neg_nat]
    simp [gaussHGCoeff, poch_zero]
  | one =>
    rw [ordinaryHypergeometric_eq_sum_neg_nat]
    simp [Finset.sum_range_succ, gaussHGCoeff, poch_zero, poch_one]
    ring
  | more n ih0 ih1 =>
    push_cast at ih1 ⊢
    rw [Chebyshev.T_add_two]
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
    rw [ih1, ih0, gauss_chebyshev_recurrence]

/-- Identity under the stated parameter and domain assumptions: `(Chebyshev.T ℂ n).eval x =
jacobiPolyP (-1 / 2) (-1 / 2) n x / jacobiPolyP (-1 / 2) (-1 / 2) n 1`. -/
@[dlmf 18.7.E3]
theorem chebyshevT_eq_jacobi (n : ℕ) (x : ℂ) :
    (Chebyshev.T ℂ n).eval x = jacobiPolyP (-1 / 2) (-1 / 2) n x
        / jacobiPolyP (-1 / 2) (-1 / 2) n 1 := by
  rw [chebyshevT_hypergeometric, jacobiPolyP_half_half, jacobi_at_one (by norm_num),
    show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num]
  have hp : poch (1 / 2 : ℂ) n ≠ 0 := poch_half_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp

end DLMF.OrthogonalPolynomials
end
end
