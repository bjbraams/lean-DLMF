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
# Differential equations and recurrences (DLMF §§18.8–18.9)

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology
open DLMF.Hypergeometric
open DLMF.Confluent

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

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

@[dlmf 18.8.T1]
theorem legendre_differential_equation (n : ℕ) (x : ℂ) :
    (1 - x ^ 2) * deriv (deriv (legendrePolyP n)) x -
      2 * x * deriv (legendrePolyP n) x + n * (n + 1) * legendrePolyP n x = 0 := by
  have h := jacobi_differential_equation (α := 0) (β := 0) (by norm_num) n x
  change (1 - x ^ 2) * deriv (deriv (jacobiPolyP 0 0 n)) x -
    2 * x * deriv (jacobiPolyP 0 0 n) x + n * (n + 1) * jacobiPolyP 0 0 n x = 0
  linear_combination h

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

@[dlmf 18.9.T1]
theorem hermitePolyH_recurrence (n : ℕ) :
    hermitePolyH (n + 2) = 2 * X * hermitePolyH (n + 1) - C (2 * (n + 1) : ℤ) * hermitePolyH n := by
  rw [hermitePolyH_succ (n + 1), hermitePolyH_derivative]

@[dlmf 18.9.T1]
theorem hermite_recurrence (n : ℕ) :
    hermite (n + 2) = X * hermite (n + 1) - C (n + 1 : ℤ) * hermite n := by
  rw [hermite_succ (n + 1), hermite_derivative]

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

@[dlmf 18.7.E3]
theorem chebyshevT_eq_jacobi (n : ℕ) (x : ℂ) :
    (Chebyshev.T ℂ n).eval x = jacobiPolyP (-1 / 2) (-1 / 2) n x
        / jacobiPolyP (-1 / 2) (-1 / 2) n 1 := by
  rw [chebyshevT_hypergeometric, jacobiPolyP_half_half, jacobi_at_one (by norm_num),
    show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num]
  have hp : poch (1 / 2 : ℂ) n ≠ 0 := poch_half_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp

@[dlmf 18.9.E11]
theorem chebyshevV_contiguous (n : ℕ) (x : ℂ) :
    chebyshevV (n + 1) x + chebyshevV n x = 2 * (Chebyshev.T ℂ (n + 1)).eval x := by
  have hraise := jacobi_raise_beta (α := -1 / 2) (β := -1 / 2) (by norm_num) n x
  rw [show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num] at hraise
  unfold chebyshevV
  have hT := chebyshevT_eq_jacobi (n + 1) x
  push_cast at hT
  rw [hT, jacobi_at_one (by norm_num), jacobi_at_one (by norm_num),
    jacobi_at_one (by norm_num), show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num, poch_succ,
    Nat.factorial_succ]
  have hp : poch (1 / 2 : ℂ) n ≠ 0 := poch_half_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hh : ((1 / 2 : ℂ) + n) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h12 : (1 + 2 * (n : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  push_cast
  field_simp
  simp only [neg_div] at hraise
  linear_combination (-2 : ℂ) * hraise

@[dlmf 18.9.E12]
theorem chebyshevV_mul_one_add (n : ℕ) (x : ℂ) :
    (Chebyshev.T ℂ (n + 1)).eval x + (Chebyshev.T ℂ n).eval x = (1 + x) * chebyshevV n x := by
  have hraise := jacobi_raise_degree_beta (α := -1 / 2) (β := -1 / 2) (by norm_num) n x
  rw [show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num] at hraise
  unfold chebyshevV
  have hT := chebyshevT_eq_jacobi (n + 1) x
  push_cast at hT
  rw [hT, chebyshevT_eq_jacobi, jacobi_at_one (by norm_num),
    jacobi_at_one (by norm_num), jacobi_at_one (by norm_num),
    show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num, poch_succ, Nat.factorial_succ]
  have hp : poch (1 / 2 : ℂ) n ≠ 0 := poch_half_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hh : ((1 / 2 : ℂ) + n) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h12 : (1 + 2 * (n : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  push_cast
  field_simp
  simp only [neg_div] at hraise
  linear_combination (-2 : ℂ) * hraise

@[dlmf 18.5.E3]
theorem chebyshevV_cos (n : ℕ) (θ : ℂ) :
    chebyshevV n (cos θ) * cos (θ / 2) = cos ((n + 1 / 2) * θ) := by
  induction n with
  | zero =>
    simp only [chebyshevV, jacobiPolyP_zero, div_one, Nat.cast_zero, zero_add, one_mul]
    ring_nf
  | succ n ih =>
    have hV : chebyshevV (n + 1) (cos θ) =
        2 * (Chebyshev.T ℂ (n + 1)).eval (cos θ) - chebyshevV n (cos θ) := by
      linear_combination chebyshevV_contiguous n (cos θ)
    have hT : (Chebyshev.T ℂ (n + 1)).eval (cos θ) = cos (((n : ℂ) + 1) * θ) := by
      have := Polynomial.Chebyshev.T_complex_cos θ ((n + 1 : ℕ) : ℤ)
      push_cast at this ⊢
      exact this
    have hsum := Complex.cos_add_cos (((n : ℂ) + 1 + 1 / 2) * θ) (((n : ℂ) + 1 / 2) * θ)
    rw [show (((n : ℂ) + 1 + 1 / 2) * θ + ((n : ℂ) + 1 / 2) * θ) / 2 = ((n : ℂ) + 1) * θ by ring,
      show (((n : ℂ) + 1 + 1 / 2) * θ - ((n : ℂ) + 1 / 2) * θ) / 2 = θ / 2 by ring] at hsum
    push_cast
    rw [hV, hT]
    linear_combination -hsum - ih

/-- The companion of 18.9.5 raising `α`:
`(2n+α+β+3) P^{(α,β)}_{n+1} = (n+α+β+2) P^{(α+1,β)}_{n+1} - (n+β+1) P^{(α+1,β)}_n`. -/
theorem jacobi_raise_alpha {α β : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    (2 * n + α + β + 3) * jacobiPolyP α β (n + 1) x =
      (n + α + β + 2) * jacobiPolyP (α + 1) β (n + 1) x - (n + β + 1)
          * jacobiPolyP (α + 1) β n x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have key : (fun x : ℂ => (2 * n + α + β + 3) * jacobiPolyP α β (n + 1) x) =
      fun x => (n + α + β + 2) * jacobiPolyP (α + 1) β (n + 1) x -
        (n + β + 1) * jacobiPolyP (α + 1) β n x := by
    refine eq_of_eqOn_half_shift_disk (by intro x _; fun_prop) (by intro x _; fun_prop) ?_
    intro x hx
    have hrel := DLMF.Hypergeometric.contiguous_c_pair (a := -((n : ℂ) + 1))
      (b := (n : ℂ) + 1 + α + β + 1) (c := α + 1) hc hx
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hP0 : jacobiPolyP α β (n + 1) x * ((n + 1) * n.factorial) =
        (α + 1) * poch (α + 1 + 1) n *
          ₂F₁ (-((n : ℂ) + 1)) ((n : ℂ) + 1 + α + β + 1) (α + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [poch_succ_left, Nat.factorial_succ]
      push_cast
      field_simp
    have hP1 : jacobiPolyP (α + 1) β (n + 1) x * ((n + 1) * n.factorial) =
        poch (α + 1 + 1) n * (α + 1 + 1 + n) *
          ₂F₁ (-((n : ℂ) + 1)) ((n : ℂ) + 1 + α + β + 1 + 1) (α + 1 + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [poch_succ, Nat.factorial_succ]
      push_cast
      rw [show (n : ℂ) + 1 + (α + 1) + β + 1 = (n : ℂ) + 1 + α + β + 1 + 1 by ring]
      field_simp
    have hP2 : jacobiPolyP (α + 1) β n x * ((n + 1) * n.factorial) =
        poch (α + 1 + 1) n * (n + 1) *
          ₂F₁ (-((n : ℂ) + 1) + 1) ((n : ℂ) + 1 + α + β + 1) (α + 1 + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [show (n : ℂ) + (α + 1) + β + 1 = (n : ℂ) + 1 + α + β + 1 by ring,
        show -(n : ℂ) = -((n : ℂ) + 1) + 1 by ring]
      field_simp
    have hM : ((n : ℂ) + 1) * n.factorial ≠ 0 := mul_ne_zero hn1 hf
    apply mul_right_cancel₀ hM
    linear_combination (2 * n + α + β + 3) * hP0 - (n + α + β + 2) * hP1 + (n + β + 1) * hP2 +
      (poch (α + 1 + 1) n) * hrel
  exact congrFun key x

/-- `(3/2)_n ≠ 0`. -/
theorem poch_three_half_ne_zero (n : ℕ) : poch (3 / 2 : ℂ) n ≠ 0 :=
  poch_ne_zero_of_not_neg_nat (fun k hk => by
    have := congrArg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) n

/-- `W_{n+1} - W_n = 2 T_{n+1}`, the fourth-kind companion of 18.9.11. -/
theorem chebyshevW_contiguous (n : ℕ) (x : ℂ) :
    chebyshevW (n + 1) x - chebyshevW n x = 2 * (Chebyshev.T ℂ (n + 1)).eval x := by
  have hraise := jacobi_raise_alpha (α := -1 / 2) (β := -1 / 2) (by norm_num) n x
  rw [show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num] at hraise
  unfold chebyshevW
  have hT := chebyshevT_eq_jacobi (n + 1) x
  push_cast at hT
  rw [hT, jacobi_at_one (by norm_num), jacobi_at_one (by norm_num), jacobi_at_one (by norm_num),
    show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num, show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num,
    poch_succ (3 / 2 : ℂ) n, poch_succ_left (1 / 2 : ℂ) n,
    show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, Nat.factorial_succ]
  have hp : poch (3 / 2 : ℂ) n ≠ 0 := poch_three_half_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hh : ((3 / 2 : ℂ) + n) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h32 : (3 + 2 * (n : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  push_cast
  field_simp
  simp only [neg_div] at hraise
  linear_combination (-2 * (3 + 2 * (n : ℂ))) * hraise

@[dlmf 18.5.E4]
theorem chebyshevW_cos (n : ℕ) (θ : ℂ) :
    chebyshevW n (cos θ) * sin (θ / 2) = sin ((n + 1 / 2) * θ) := by
  induction n with
  | zero =>
    simp only [chebyshevW, jacobiPolyP_zero, div_one, Nat.cast_zero, mul_zero, zero_add, one_mul]
    ring_nf
  | succ n ih =>
    have hW : chebyshevW (n + 1) (cos θ) =
        2 * (Chebyshev.T ℂ (n + 1)).eval (cos θ) + chebyshevW n (cos θ) := by
      linear_combination chebyshevW_contiguous n (cos θ)
    have hT : (Chebyshev.T ℂ (n + 1)).eval (cos θ) = cos (((n : ℂ) + 1) * θ) := by
      have := Polynomial.Chebyshev.T_complex_cos θ ((n + 1 : ℕ) : ℤ)
      push_cast at this ⊢
      exact this
    have hdiff := Complex.sin_sub_sin (((n : ℂ) + 1 + 1 / 2) * θ) (((n : ℂ) + 1 / 2) * θ)
    rw [show (((n : ℂ) + 1 + 1 / 2) * θ + ((n : ℂ) + 1 / 2) * θ) / 2 = ((n : ℂ) + 1) * θ by ring,
      show (((n : ℂ) + 1 + 1 / 2) * θ - ((n : ℂ) + 1 / 2) * θ) / 2 = θ / 2 by ring] at hdiff
    push_cast
    rw [hW, hT]
    linear_combination ih - hdiff

@[dlmf 18.7.E18]
theorem chebyshevT_quadratic (n : ℕ) (x : ℂ) :
    (Chebyshev.T ℂ (2 * n + 1)).eval x = x * chebyshevV n (2 * x ^ 2 - 1) := by
  obtain ⟨θ, rfl⟩ := Complex.cos_surjective x
  have hT : (Chebyshev.T ℂ (2 * n + 1)).eval (cos θ) = cos ((2 * (n : ℂ) + 1) * θ) := by
    have := Polynomial.Chebyshev.T_complex_cos θ ((2 * n + 1 : ℕ) : ℤ)
    push_cast at this ⊢
    exact this
  have hV := chebyshevV_cos n (2 * θ)
  rw [Complex.cos_two_mul, show 2 * θ / 2 = θ by ring] at hV
  rw [hT, show (2 * (n : ℂ) + 1) * θ = ((n : ℂ) + 1 / 2) * (2 * θ) by ring, ← hV]
  ring

/-- `sin θ ≠ 0` when `cos θ ≠ ±1`. -/
theorem sin_ne_zero_of_cos_ne {θ : ℂ} (h1 : cos θ ≠ 1) (h2 : cos θ ≠ -1) : sin θ ≠ 0 := by
  intro h
  have hsc := Complex.sin_sq_add_cos_sq θ
  rw [h] at hsc
  have : (cos θ - 1) * (cos θ + 1) = 0 := by linear_combination hsc
  rcases mul_eq_zero.mp this with h3 | h3
  · exact h1 (by linear_combination h3)
  · exact h2 (by linear_combination h3)

/-- `sin (θ/2) ≠ 0` when `cos θ ≠ 1`. -/
theorem sin_half_ne_zero_of_cos_ne_one {θ : ℂ} (h1 : cos θ ≠ 1) : sin (θ / 2) ≠ 0 := by
  intro h
  apply h1
  have hsc := Complex.sin_sq_add_cos_sq (θ / 2)
  rw [h] at hsc
  rw [show θ = 2 * (θ / 2) by ring, Complex.cos_two_mul]
  linear_combination 2 * hsc

@[dlmf 18.7.E17]
theorem chebyshevU_quadratic (n : ℕ) (x : ℂ) :
    (Chebyshev.U ℂ (2 * n)).eval x = chebyshevW n (2 * x ^ 2 - 1) := by
  have hne : jacobiPolyP (1 / 2) (-1 / 2) n 1 ≠ 0 := jacobiPolyP_one_ne_zero (by norm_num) n
  have key : (fun x : ℂ => (Chebyshev.U ℂ (2 * n)).eval x) =
      fun x => chebyshevW n (2 * x ^ 2 - 1) := by
    refine DLMF.Hypergeometric.eq_of_analyticOnNhd_univ_of_eqOn ?_ ?_
      (isOpen_ne.inter isOpen_ne : IsOpen {x : ℂ | x ≠ 1 ∧ x ≠ -1})
      ⟨0, by norm_num, by exact (by norm_num : (0 : ℂ) ≠ -1)⟩ ?_
    · exact (Polynomial.differentiable _).differentiableOn.analyticOnNhd isOpen_univ
    · intro x _
      unfold chebyshevW
      have h1 : AnalyticAt ℂ (fun x : ℂ => jacobiPolyP (1 / 2) (-1 / 2) n (2 * x ^ 2 - 1)) x :=
        (analyticAt_jacobiPolyP _ _ n _).comp (f := fun x : ℂ => 2 * x ^ 2 - 1) (by fun_prop)
      exact AnalyticAt.fun_div (f := fun x : ℂ => (2 * (n : ℂ) + 1) *
        jacobiPolyP (1 / 2) (-1 / 2) n (2 * x ^ 2 - 1))
            (g := fun _ => jacobiPolyP (1 / 2) (-1 / 2) n 1)
        (x := x) (analyticAt_const.mul h1) analyticAt_const hne
    intro x hx
    obtain ⟨θ, rfl⟩ := Complex.cos_surjective x
    have hs : sin θ ≠ 0 := sin_ne_zero_of_cos_ne hx.1 hx.2
    have hU : (Chebyshev.U ℂ (2 * n)).eval (cos θ) * sin θ = sin ((2 * (n : ℂ) + 1) * θ) := by
      have := Polynomial.Chebyshev.U_complex_cos θ ((2 * n : ℕ) : ℤ)
      push_cast at this ⊢
      exact this
    have hW := chebyshevW_cos n (2 * θ)
    rw [Complex.cos_two_mul, show 2 * θ / 2 = θ by ring,
      show ((n : ℂ) + 1 / 2) * (2 * θ) = (2 * (n : ℂ) + 1) * θ by ring] at hW
    exact mul_right_cancel₀ hs (hU.trans hW.symm)
  exact congrFun key x

@[dlmf 18.6.T1]
theorem chebyshevV_reflection (n : ℕ) (x : ℂ) :
    chebyshevV n (-x) = (-1 : ℂ) ^ n * chebyshevW n x := by
  have hneV : jacobiPolyP (-1 / 2) (1 / 2) n 1 ≠ 0 := jacobiPolyP_one_ne_zero (by norm_num) n
  have hneW : jacobiPolyP (1 / 2) (-1 / 2) n 1 ≠ 0 := jacobiPolyP_one_ne_zero (by norm_num) n
  have key : (fun x : ℂ => chebyshevV n (-x)) = fun x => (-1 : ℂ) ^ n * chebyshevW n x := by
    refine DLMF.Hypergeometric.eq_of_analyticOnNhd_univ_of_eqOn ?_ ?_
      (isOpen_ne : IsOpen {x : ℂ | x ≠ 1}) ⟨0, by norm_num⟩ ?_
    · intro x _
      unfold chebyshevV
      have h1 : AnalyticAt ℂ (fun x : ℂ => jacobiPolyP (-1 / 2) (1 / 2) n (-x)) x :=
        (analyticAt_jacobiPolyP _ _ n _).comp (f := fun x : ℂ => -x) (by fun_prop)
      exact AnalyticAt.fun_div (f := fun x : ℂ => jacobiPolyP (-1 / 2) (1 / 2) n (-x))
        (g := fun _ => jacobiPolyP (-1 / 2) (1 / 2) n 1) (x := x) h1 analyticAt_const hneV
    · intro x _
      unfold chebyshevW
      exact analyticAt_const.mul (AnalyticAt.fun_div (f := fun x : ℂ => (2 * (n : ℂ) + 1) *
        jacobiPolyP (1 / 2) (-1 / 2) n x) (g := fun _ => jacobiPolyP (1 / 2) (-1 / 2) n 1) (x := x)
        (analyticAt_const.mul (analyticAt_jacobiPolyP _ _ n x)) analyticAt_const hneW)
    intro x hx
    obtain ⟨θ, rfl⟩ := Complex.cos_surjective x
    have hs : sin (θ / 2) ≠ 0 := sin_half_ne_zero_of_cos_ne_one hx
    have hV := chebyshevV_cos n ((Real.pi : ℂ) - θ)
    rw [Complex.cos_pi_sub] at hV
    have h1 : cos (((Real.pi : ℂ) - θ) / 2) = sin (θ / 2) := by
      rw [show ((Real.pi : ℂ) - θ) / 2 = (Real.pi : ℂ) / 2 - θ / 2 by ring,
        Complex.cos_pi_div_two_sub]
    have hcos : cos ((n : ℂ) * (Real.pi : ℂ)) = (-1 : ℂ) ^ n := by
      rw [show (n : ℂ) * (Real.pi : ℂ) = ((n * Real.pi : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cos, Real.cos_nat_mul_pi]
      push_cast
      ring
    have hsin : sin ((n : ℂ) * (Real.pi : ℂ)) = 0 := by
      rw [show (n : ℂ) * (Real.pi : ℂ) = ((n * Real.pi : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_sin, Real.sin_nat_mul_pi]
      push_cast
      ring
    have h2 : cos (((n : ℂ) + 1 / 2) * ((Real.pi : ℂ) - θ)) =
        (-1 : ℂ) ^ n * sin (((n : ℂ) + 1 / 2) * θ) := by
      rw [show ((n : ℂ) + 1 / 2) * ((Real.pi : ℂ) - θ) =
          ((n : ℂ) * Real.pi + (Real.pi : ℂ) / 2) - ((n : ℂ) + 1 / 2) * θ by ring,
        Complex.cos_sub, Complex.cos_add_pi_div_two, Complex.sin_add_pi_div_two, hcos, hsin]
      ring
    have hW := chebyshevW_cos n θ
    rw [h1, h2, ← hW, ← mul_assoc] at hV
    exact mul_right_cancel₀ hs hV
  exact congrFun key x

@[dlmf 18.6.T1]
theorem chebyshevW_reflection (n : ℕ) (x : ℂ) :
    chebyshevW n (-x) = (-1 : ℂ) ^ n * chebyshevV n x := by
  have h := chebyshevV_reflection n (-x)
  rw [neg_neg] at h
  have hsq : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by
    rw [← mul_pow]
    simp
  rw [h, ← mul_assoc, hsq, one_mul]

@[dlmf 18.9.E13]
theorem laguerrePolyL_raise_parameter {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    laguerrePolyL α (n + 1) x = laguerrePolyL (α + 1) (n + 1) x - laguerrePolyL (α + 1) n x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hb : ∀ k : ℕ, α + 1 + 1 - 1 ≠ -(k : ℂ) := by simpa using hc
  have hc1 : ∀ k : ℕ, α + 1 + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hc 1
  have hM := DLMF.Confluent.kummerM_contiguous_a_b (a := -((n + 1 : ℕ) : ℂ)) hb (z := x)
  rw [show α + 1 + 1 - 1 = α + 1 by ring,
    show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring] at hM
  have hP : poch (α + 1 + 1) n ≠ 0 := poch_ne_zero_of_not_neg_nat hc1 n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [laguerrePolyL]
  rw [poch_succ_left (α + 1) n, poch_succ (α + 1 + 1) n, Nat.factorial_succ n]
  push_cast at hM ⊢
  field_simp
  linear_combination hM

@[dlmf 18.9.E14]
theorem laguerrePolyL_mul_argument {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    x * laguerrePolyL (α + 1) n x = -(n + 1) * laguerrePolyL α (n + 1) x + (n + α + 1)
        * laguerrePolyL α n x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hc0 : α + 1 ≠ 0 := by simpa using hc 0
  have hM := DLMF.Confluent.kummerM_contiguous_shift_a (a := -(n : ℂ)) hc (z := x)
  rw [show -(n : ℂ) - 1 = -((n + 1 : ℕ) : ℂ) by push_cast; ring] at hM
  have hQ : poch (α + 1) n ≠ 0 := poch_ne_zero_of_not_neg_nat hc n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hrel : (α + 1) * poch (α + 1 + 1) n = poch (α + 1) n * (α + 1 + n) := by
    rw [← poch_succ_left, poch_succ]
  have hX : poch (α + 1 + 1) n = poch (α + 1) n * (α + 1 + n) / (α + 1) := by
    rw [eq_div_iff hc0]; linear_combination hrel
  simp only [laguerrePolyL]
  rw [poch_succ (α + 1) n, Nat.factorial_succ n, hX]
  push_cast at hM ⊢
  field_simp
  linear_combination (-(α + 1 + (n : ℂ))) * hM

/-- Differentiating a terminating Gauss series is valid throughout the complex plane. -/
theorem deriv_gauss_neg_nat_succ (n : ℕ) (b : ℂ) {c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    deriv (₂F₁ (-((n + 1 : ℕ) : ℂ)) b c) = fun z =>
      (-((n + 1 : ℕ) : ℂ) * b / c) * ₂F₁ (-(n : ℂ)) (b + 1) (c + 1) z := by
  funext z
  have hd := (hasFPowerSeriesOnBall_gauss_neg_nat (n + 1) b c).deriv_ofScalars.hasSum_mul_pow
    (z := z) (by simp)
  have hs := ((hasFPowerSeriesOnBall_gauss_neg_nat n (b + 1) (c + 1)).hasSum_mul_pow
    (z := z) (by simp)).mul_left (-((n + 1 : ℕ) : ℂ) * b / c)
  simp_rw [gaussHGCoeff_shift hc] at hd
  rw [show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring] at hd
  simp only [mul_assoc] at hd hs
  exact hd.unique hs

@[dlmf 18.9.E15]
theorem jacobi_derivative {α β : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    deriv (jacobiPolyP α β (n + 1)) x = (n + α + β + 2) / 2 * jacobiPolyP (α + 1) (β + 1) n x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hc0 : α + 1 ≠ 0 := by simpa using hc 0
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have he : jacobiPolyP α β (n + 1) = fun z => poch (α + 1) (n + 1) / ((n + 1).factorial : ℂ) *
      ₂F₁ (-((n + 1 : ℕ) : ℂ)) ((n + 1 : ℕ) + α + β + 1) (α + 1) ((1 - z) / 2) := rfl
  rw [he]
  simp only [deriv_const_mul_field', deriv_half_shift, deriv_gauss_neg_nat_succ n _ hc]
  rw [jacobiPolyP, poch_succ_left, Nat.factorial_succ]
  push_cast
  rw [show (n : ℂ) + 1 + α + β + 1 + 1 = n + (α + 1) + (β + 1) + 1 by ring]
  field_simp
  <;> ring

/-- The derivative of a Jacobi polynomial on the disk `‖(1-x)/2‖ < 1`, from 15.5.1 and the
chain rule. -/
theorem hasDerivAt_jacobiPolyP {α β : ℂ} (hα : -1 < α.re) (n : ℕ) {x : ℂ} (hx : ‖(1 - x) / 2‖ < 1) :
    HasDerivAt (jacobiPolyP α β n)
      (poch (α + 1) n / n.factorial * (-(n : ℂ) * ((n : ℂ) + α + β + 1) / (α + 1) *
        ₂F₁ (-(n : ℂ) + 1) ((n : ℂ) + α + β + 1 + 1) (α + 1 + 1) ((1 - x) / 2) * (-1 / 2))) x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hF := hasDerivAt_ordinaryHypergeometric (a := -(n : ℂ)) (b := (n : ℂ) + α + β + 1) hc hx
  have hin : HasDerivAt (fun x : ℂ => (1 - x) / 2) (-1 / 2) x :=
    ((hasDerivAt_id' x).const_sub 1).div_const 2
  exact (hF.comp x hin).const_mul (poch (α + 1) n / n.factorial)

@[dlmf 18.9.E17]
theorem jacobi_lowering_derivative {α β : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    (2 * n + α + β + 2) * (1 - x ^ 2) * deriv (jacobiPolyP α β (n + 1)) x =
      (n + 1) * (α - β - (2 * n + α + β + 2) * x) * jacobiPolyP α β (n + 1) x +
      2 * (n + α + 1) * (n + β + 1) * jacobiPolyP α β n x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have key : (fun x : ℂ => (2 * n + α + β + 2) * (1 - x ^ 2) * deriv (jacobiPolyP α β (n + 1)) x) =
      fun x => (n + 1) * (α - β - (2 * n + α + β + 2) * x) * jacobiPolyP α β (n + 1) x +
        2 * (n + α + 1) * (n + β + 1) * jacobiPolyP α β n x := by
    refine eq_of_eqOn_half_shift_disk ?_ (by intro x _; fun_prop) ?_
    · intro x _
      have hd : AnalyticAt ℂ (deriv (jacobiPolyP α β (n + 1))) x :=
        (analyticOnNhd_jacobiPolyP α β (n + 1)).deriv x (Set.mem_univ x)
      fun_prop
    intro x hx
    have hrel := DLMF.Hypergeometric.contiguous_jacobi_lowering (a := -((n : ℂ) + 1))
      (b := (n : ℂ) + 1 + α + β + 1) (c := α + 1) hc hx
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hD : (-((n : ℂ) + 1) - 1) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hrel' := (mul_eq_zero.mp hrel).resolve_left hD
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hc0 : (α + 1) ≠ 0 := by simpa using hc 0
    have hP1 : jacobiPolyP α β (n + 1) x * ((n + 1) * n.factorial * (α + 1)) =
        poch (α + 1) n * (α + 1 + n) * (α + 1) *
          ₂F₁ (-((n : ℂ) + 1)) ((n : ℂ) + 1 + α + β + 1) (α + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [poch_succ, Nat.factorial_succ]
      push_cast
      field_simp
    have hP0 : jacobiPolyP α β n x * ((n + 1) * n.factorial * (α + 1)) =
        poch (α + 1) n * ((n + 1) * (α + 1)) *
          ₂F₁ (-((n : ℂ) + 1) + 1) ((n : ℂ) + 1 + α + β + 1 - 1) (α + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [show (n : ℂ) + 1 + α + β + 1 - 1 = (n : ℂ) + α + β + 1 by ring,
        show -((n : ℂ) + 1) + 1 = -(n : ℂ) by ring]
      field_simp
    have hDd : deriv (jacobiPolyP α β (n + 1)) x * ((n + 1) * n.factorial * (α + 1)) =
        poch (α + 1) n * (α + 1 + n) * (-((n : ℂ) + 1) * ((n : ℂ) + 1 + α + β + 1)) * (-1 / 2) *
          ₂F₁ (-((n : ℂ) + 1) + 1) ((n : ℂ) + 1 + α + β + 1 + 1) (α + 1 + 1) ((1 - x) / 2) := by
      rw [(hasDerivAt_jacobiPolyP hα (n + 1) hx).deriv, poch_succ, Nat.factorial_succ]
      push_cast
      field_simp
    have hM : ((n : ℂ) + 1) * n.factorial * (α + 1) ≠ 0 := mul_ne_zero (mul_ne_zero hn1 hf) hc0
    apply mul_right_cancel₀ hM
    linear_combination ((2 * n + α + β + 2) * (1 - x ^ 2)) * hDd -
      ((n + 1) * (α - β - (2 * n + α + β + 2) * x)) * hP1 -
      (2 * (n + α + 1) * (n + β + 1)) * hP0 + (poch (α + 1) n) * hrel'
  exact congrFun key x

@[dlmf 18.9.E18]
theorem jacobi_raising_derivative {α β : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    (2 * n + α + β + 2) * (1 - x ^ 2) * deriv (jacobiPolyP α β n) x =
      (n + α + β + 1) * (α - β + (2 * n + α + β + 2) * x) * jacobiPolyP α β n x -
      2 * (n + 1) * (n + α + β + 1) * jacobiPolyP α β (n + 1) x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have key : (fun x : ℂ => (2 * n + α + β + 2) * (1 - x ^ 2) * deriv (jacobiPolyP α β n) x) =
      fun x => (n + α + β + 1) * (α - β + (2 * n + α + β + 2) * x) * jacobiPolyP α β n x -
        2 * (n + 1) * (n + α + β + 1) * jacobiPolyP α β (n + 1) x := by
    refine eq_of_eqOn_half_shift_disk ?_ (by intro x _; fun_prop) ?_
    · intro x _
      have hd : AnalyticAt ℂ (deriv (jacobiPolyP α β n)) x :=
        (analyticOnNhd_jacobiPolyP α β n).deriv x (Set.mem_univ x)
      fun_prop
    intro x hx
    have hrel := DLMF.Hypergeometric.contiguous_jacobi_raising (a := -(n : ℂ))
      (b := (n : ℂ) + α + β + 1) (c := α + 1) hc hx
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hD : (-(n : ℂ) - 2) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hrel' := (mul_eq_zero.mp hrel).resolve_left hD
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hc0 : (α + 1) ≠ 0 := by simpa using hc 0
    have hP0 : jacobiPolyP α β n x * ((n + 1) * n.factorial * (α + 1)) =
        poch (α + 1) n * ((n + 1) * (α + 1)) *
          ₂F₁ (-(n : ℂ)) ((n : ℂ) + α + β + 1) (α + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      field_simp
    have hP1 : jacobiPolyP α β (n + 1) x * ((n + 1) * n.factorial * (α + 1)) =
        poch (α + 1) n * (α + 1 + n) * (α + 1) *
          ₂F₁ (-(n : ℂ) - 1) ((n : ℂ) + α + β + 1 + 1) (α + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [poch_succ, Nat.factorial_succ]
      push_cast
      rw [show -((n : ℂ) + 1) = -(n : ℂ) - 1 by ring,
        show (n : ℂ) + 1 + α + β + 1 = (n : ℂ) + α + β + 1 + 1 by ring]
      field_simp
    have hDd : deriv (jacobiPolyP α β n) x * ((n + 1) * n.factorial * (α + 1)) =
        poch (α + 1) n * (n + 1) * (-(n : ℂ) * ((n : ℂ) + α + β + 1)) * (-1 / 2) *
          ₂F₁ (-(n : ℂ) + 1) ((n : ℂ) + α + β + 1 + 1) (α + 1 + 1) ((1 - x) / 2) := by
      rw [(hasDerivAt_jacobiPolyP hα n hx).deriv]
      field_simp
    have hM : ((n : ℂ) + 1) * n.factorial * (α + 1) ≠ 0 := mul_ne_zero (mul_ne_zero hn1 hf) hc0
    apply mul_right_cancel₀ hM
    linear_combination ((2 * n + α + β + 2) * (1 - x ^ 2)) * hDd -
      ((n + α + β + 1) * (α - β + (2 * n + α + β + 2) * x)) * hP0 +
      (2 * (n + 1) * (n + α + β + 1)) * hP1 + (poch (α + 1) n) * hrel'
  exact congrFun key x

@[dlmf 18.9.E19]
theorem ultrasphPoly_derivative {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) (x : ℂ) :
    deriv (ultrasphPoly lam (n + 1)) x = 2 * lam * ultrasphPoly (lam + 1) n x := by
  have hc : ∀ k : ℕ, lam + 1 / 2 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith)
  have hc0 : lam + 1 / 2 ≠ 0 := by simpa using hc 0
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hp : poch (2 * lam) (n + 1) * (n + 1 + 2 * lam) =
      2 * lam * (2 * lam + 1) * poch (2 * lam + 2) n := by
    rw [poch_succ_left]
    have h := poch_succ (2 * lam + 1) n
    rw [poch_succ_left] at h
    rw [show 2 * lam + 1 + 1 = 2 * lam + 2 by ring] at h
    linear_combination -(2 * lam) * h
  have hf : poch (2 * lam) (n + 1) / ((n + 1).factorial : ℂ) * (-1 / 2) *
      (-(n + 1 : ℂ) * (n + 1 + 2 * lam) / (lam + 1 / 2)) =
      2 * lam * (poch (2 * (lam + 1)) n / (n.factorial : ℂ)) := by
    calc
      _ = (poch (2 * lam) (n + 1) * (n + 1 + 2 * lam)) /
          (2 * (lam + 1 / 2) * (n.factorial : ℂ)) := by
        rw [Nat.factorial_succ]
        push_cast
        field_simp
      _ = _ := by
        have h2 : 2 * lam + 1 ≠ 0 := by
          intro hz
          apply hc0
          linear_combination hz / 2
        rw [hp, show 2 * (lam + 1) = 2 * lam + 2 by ring,
          show 2 * (lam + 1 / 2) * (n.factorial : ℂ) = (2 * lam + 1) * n.factorial by ring,
          show 2 * lam * (2 * lam + 1) * poch (2 * lam + 2) n =
            (2 * lam + 1) * (2 * lam * poch (2 * lam + 2) n) by ring,
          mul_div_mul_left _ _ h2]
        ring
  have he : ultrasphPoly lam (n + 1) = fun z => poch (2 * lam) (n + 1) / ((n + 1).factorial : ℂ) *
      ₂F₁ (-((n + 1 : ℕ) : ℂ)) ((n + 1 : ℕ) + 2 * lam) (lam + 1 / 2) ((1 - z) / 2) := rfl
  rw [he]
  simp only [deriv_const_mul_field', deriv_half_shift, deriv_gauss_neg_nat_succ n _ hc]
  rw [ultrasphPoly]
  push_cast
  rw [show (n : ℂ) + 1 + 2 * lam + 1 = n + 2 * (lam + 1) by ring,
    show lam + 1 / 2 + 1 = (lam + 1) + 1 / 2 by ring]
  linear_combination (₂F₁ (-(n : ℂ)) (n + 2 * (lam + 1)) ((lam + 1) + 1 / 2) ((1 - x) / 2)) * hf

/-- The derivative formula for Kummer's entire series at regular lower parameters. -/
@[dlmf 13.3.E15]
theorem deriv_kummerM_regular {a c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    deriv (kummerM a c) = fun z => a / c * kummerM (a + 1) (c + 1) z :=
  funext fun z => DLMF.Confluent.deriv_kummerM hc (by simpa using hc 0)

@[dlmf 18.9.E23]
theorem laguerrePolyL_derivative {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    deriv (laguerrePolyL α (n + 1)) x = -laguerrePolyL (α + 1) n x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hc0 : α + 1 ≠ 0 := by simpa using hc 0
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have he : laguerrePolyL α (n + 1) = fun z => poch (α + 1) (n + 1) / ((n + 1).factorial : ℂ) *
      kummerM (-((n + 1 : ℕ) : ℂ)) (α + 1) z := rfl
  rw [he]
  simp only [deriv_const_mul_field', deriv_kummerM_regular hc]
  rw [laguerrePolyL, poch_succ_left, Nat.factorial_succ]
  push_cast
  rw [show -((n : ℂ) + 1) + 1 = -(n : ℂ) by ring]
  field_simp

@[dlmf 18.9.E26]
theorem hermitePolyH_weighted_derivative (n : ℕ) (x : ℝ) :
    deriv (fun t : ℝ => Real.exp (-(t ^ 2)) * aeval t (hermitePolyH n)) x =
      -Real.exp (-(x ^ 2)) * aeval x (hermitePolyH (n + 1)) := by
  have hd := (((hasDerivAt_id x).pow 2).neg.exp).fun_mul ((hermitePolyH n).hasDerivAt_aeval x)
  simp only [Pi.pow_apply, Pi.neg_apply, id_eq] at hd
  rw [hd.deriv]
  simp only [hermitePolyH_succ, map_sub, map_mul, map_ofNat, aeval_X, mul_one]
  ring

@[dlmf 18.9.E28]
theorem hermite_weighted_derivative (n : ℕ) (x : ℝ) :
    deriv (fun t : ℝ => Real.exp (-(t ^ 2) / 2) * aeval t (hermite n)) x =
      -Real.exp (-(x ^ 2) / 2) * aeval x (hermite (n + 1)) := by
  have hd := ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp).fun_mul ((hermite n).hasDerivAt_aeval x)
  simp only [Pi.pow_apply, Pi.neg_apply, id_eq] at hd
  rw [hd.deriv]
  simp only [hermite_succ, map_sub, map_mul, aeval_X, mul_one]
  ring


/-- The derivative of a Gegenbauer polynomial on the disk `‖(1-x)/2‖ < 1`. -/
theorem hasDerivAt_ultrasphPoly {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) {x : ℂ}
    (hx : ‖(1 - x) / 2‖ < 1) :
    HasDerivAt (ultrasphPoly lam n)
      (poch (2 * lam) n / n.factorial * (-(n : ℂ) * ((n : ℂ) + 2 * lam) / (lam + 1 / 2) *
        ₂F₁ (-(n : ℂ) + 1) ((n : ℂ) + 2 * lam + 1) (lam + 1 / 2 + 1) ((1 - x) / 2) * (-1 / 2))) x := by
  have hc : ∀ k : ℕ, lam + 1 / 2 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith)
  have hF := hasDerivAt_ordinaryHypergeometric (a := -(n : ℂ)) (b := (n : ℂ) + 2 * lam) hc hx
  have hin : HasDerivAt (fun x : ℂ => (1 - x) / 2) (-1 / 2) x :=
    ((hasDerivAt_id' x).const_sub 1).div_const 2
  exact (hF.comp x hin).const_mul (poch (2 * lam) n / n.factorial)

/-- The polynomial identity behind 18.9.16:
`(1-x²) P' + (β(1-x) - α(1+x)) P = -2(n+1) P^{(α-1,β-1)}_{n+1}`. -/
theorem jacobi_weighted_identity {α β : ℂ} (hα : 0 < α.re) (n : ℕ) (x : ℂ) :
    (1 - x ^ 2) * deriv (jacobiPolyP α β n) x + (β * (1 - x) - α * (1 + x)) * jacobiPolyP α β n x +
      2 * (n + 1) * jacobiPolyP (α - 1) (β - 1) (n + 1) x = 0 := by
  have hα' : -1 < α.re := by linarith
  have hc : ∀ k : ℕ, α ≠ -(k : ℂ) := not_neg_nat_of_re_pos hα
  have hc1 : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have key : (fun x : ℂ => (1 - x ^ 2) * deriv (jacobiPolyP α β n) x +
      (β * (1 - x) - α * (1 + x)) * jacobiPolyP α β n x +
      2 * (n + 1) * jacobiPolyP (α - 1) (β - 1) (n + 1) x) = fun _ => 0 := by
    refine eq_of_eqOn_half_shift_disk ?_ analyticOnNhd_const ?_
    · intro x _
      have hd : AnalyticAt ℂ (deriv (jacobiPolyP α β n)) x :=
        (analyticOnNhd_jacobiPolyP α β n).deriv x (Set.mem_univ x)
      fun_prop
    intro x hx
    have hdiag := DLMF.Hypergeometric.contiguous_diagonal (a := -((n : ℂ) + 1))
      (b := (n : ℂ) + α + β) (c := α) hc hx
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hc0 : (α + 1) ≠ 0 := by simpa using hc1 0
    have hP : jacobiPolyP α β n x * (n.factorial * (n + 1) * (α + 1)) =
        poch (α + 1) n * (n + 1) * (α + 1) *
          ₂F₁ (-((n : ℂ) + 1) + 1) ((n : ℂ) + α + β + 1) (α + 1) ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [show -((n : ℂ) + 1) + 1 = -(n : ℂ) by ring]
      field_simp
    have hD : deriv (jacobiPolyP α β n) x * (n.factorial * (n + 1) * (α + 1)) =
        poch (α + 1) n * (n + 1) * (-(n : ℂ) * ((n : ℂ) + α + β + 1)) * (-1 / 2) *
          ₂F₁ (-((n : ℂ) + 1) + 2) ((n : ℂ) + α + β + 2) (α + 2) ((1 - x) / 2) := by
      rw [(hasDerivAt_jacobiPolyP hα' n hx).deriv, show -((n : ℂ) + 1) + 2 = -(n : ℂ) + 1 by ring,
        show (n : ℂ) + α + β + 2 = (n : ℂ) + α + β + 1 + 1 by ring, show α + 2 = α + 1 + 1 by ring]
      field_simp
    have hQ : jacobiPolyP (α - 1) (β - 1) (n + 1) x * (n.factorial * (n + 1) * (α + 1)) =
        α * poch (α + 1) n * (α + 1) *
          ₂F₁ (-((n : ℂ) + 1)) ((n : ℂ) + α + β) α ((1 - x) / 2) := by
      unfold jacobiPolyP
      rw [show α - 1 + 1 = α by ring, poch_succ_left, Nat.factorial_succ]
      push_cast
      rw [show (n : ℂ) + 1 + (α - 1) + (β - 1) + 1 = (n : ℂ) + α + β by ring]
      field_simp
    have hM : (n.factorial : ℂ) * (n + 1) * (α + 1) ≠ 0 := mul_ne_zero (mul_ne_zero hf hn1) hc0
    have : ((1 - x ^ 2) * deriv (jacobiPolyP α β n) x + (β * (1 - x) - α * (1 + x))
        * jacobiPolyP α β n x +
        2 * (n + 1) * jacobiPolyP (α - 1) (β - 1) (n + 1) x) * (n.factorial * (n + 1) * (α + 1))
            = 0 := by
      linear_combination (1 - x ^ 2) * hD + (β * (1 - x) - α * (1 + x)) * hP + (2 * (n + 1)) * hQ +
        (-2 * poch (α + 1) n * (n + 1)) * hdiag
    exact (mul_eq_zero.mp this).resolve_right hM
  exact congrFun key x

/-- The polynomial identity behind 18.9.20, multiplied by `2(λ-1)`:
`2(λ-1)((1-x²) C' - (2λ-1) x C) + (n+1)(n+2λ-1) C^{λ-1}_{n+1} = 0`. -/
theorem ultrasphPoly_weighted_identity {lam : ℂ} (hlam : 1 / 2 < lam.re) (n : ℕ) (x : ℂ) :
    2 * (lam - 1)
        * ((1 - x ^ 2) * deriv (ultrasphPoly lam n) x - (2 * lam - 1) * x * ultrasphPoly lam n x) +
      (n + 1) * (n + 2 * lam - 1) * ultrasphPoly (lam - 1) (n + 1) x = 0 := by
  have hlam' : -1 / 2 < lam.re := by linarith
  have hc : ∀ k : ℕ, lam - 1 / 2 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith)
  have hc1 : ∀ k : ℕ, lam + 1 / 2 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith)
  have key : (fun x : ℂ => 2 * (lam - 1) * ((1 - x ^ 2) * deriv (ultrasphPoly lam n) x -
      (2 * lam - 1) * x * ultrasphPoly lam n x) +
      (n + 1) * (n + 2 * lam - 1) * ultrasphPoly (lam - 1) (n + 1) x) = fun _ => 0 := by
    refine eq_of_eqOn_half_shift_disk ?_ analyticOnNhd_const ?_
    · intro x _
      have hd : AnalyticAt ℂ (deriv (ultrasphPoly lam n)) x :=
        (analyticOnNhd_ultrasphPoly lam n).deriv x (Set.mem_univ x)
      fun_prop
    intro x hx
    have hdiag := DLMF.Hypergeometric.contiguous_diagonal (a := -((n : ℂ) + 1))
      (b := (n : ℂ) + 2 * lam - 1) (c := lam - 1 / 2) hc hx
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hc0 : (lam + 1 / 2) ≠ 0 := by simpa using hc1 0
    have hN : (2 * lam - 1 + (n : ℂ)) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h2 : (2 * lam + 1) ≠ 0 := by
      intro h
      apply hc0
      linear_combination h / 2
    have hpq : poch (2 * (lam - 1)) (n + 1) * (2 * lam - 1 + n) =
        2 * (lam - 1) * (2 * lam - 1) * poch (2 * lam) n := by
      rw [poch_succ_left, show 2 * (lam - 1) + 1 = 2 * lam - 1 by ring, mul_assoc, ← poch_succ,
        poch_succ_left, show 2 * lam - 1 + 1 = 2 * lam by ring]
      ring
    have hM : (n.factorial : ℂ) * (n + 1) * (lam + 1 / 2) * (2 * lam - 1 + n) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero hf hn1) hc0) hN
    have hP : ultrasphPoly lam n x * (n.factorial * (n + 1) * (lam + 1 / 2) * (2 * lam - 1 + n)) =
        poch (2 * lam) n * (n + 1) * (lam + 1 / 2) * (2 * lam - 1 + n) *
          ₂F₁ (-((n : ℂ) + 1) + 1) ((n : ℂ) + 2 * lam - 1 + 1) (lam - 1 / 2 + 1) ((1 - x) / 2) := by
      unfold ultrasphPoly
      rw [show -((n : ℂ) + 1) + 1 = -(n : ℂ) by ring,
        show (n : ℂ) + 2 * lam - 1 + 1 = (n : ℂ) + 2 * lam by ring,
        show lam - 1 / 2 + 1 = lam + 1 / 2 by ring]
      field_simp
    have hD : deriv (ultrasphPoly lam n) x
        * (n.factorial * (n + 1) * (lam + 1 / 2) * (2 * lam - 1 + n)) =
        poch (2 * lam) n * (n + 1) * (-(n : ℂ) * ((n : ℂ) + 2 * lam)) * (-1 / 2) * (2 * lam - 1 + n) *
          ₂F₁ (-((n : ℂ) + 1) + 2) ((n : ℂ) + 2 * lam - 1 + 2) (lam - 1 / 2 + 2) ((1 - x) / 2) := by
      rw [(hasDerivAt_ultrasphPoly hlam' n hx).deriv,
        show -((n : ℂ) + 1) + 2 = -(n : ℂ) + 1 by ring,
        show (n : ℂ) + 2 * lam - 1 + 2 = (n : ℂ) + 2 * lam + 1 by ring,
        show lam - 1 / 2 + 2 = lam + 1 / 2 + 1 by ring]
      field_simp
    have hQ' : ultrasphPoly (lam - 1) (n + 1) x * ((n + 1) * n.factorial) =
        poch (2 * (lam - 1)) (n + 1) *
          ₂F₁ (-((n : ℂ) + 1)) ((n : ℂ) + 2 * lam - 1) (lam - 1 / 2) ((1 - x) / 2) := by
      unfold ultrasphPoly
      rw [Nat.factorial_succ]
      push_cast
      rw [show (n : ℂ) + 1 + 2 * (lam - 1) = (n : ℂ) + 2 * lam - 1 by ring,
        show lam - 1 + 1 / 2 = lam - 1 / 2 by ring]
      field_simp
    have hQ : ultrasphPoly (lam - 1) (n + 1) x
        * (n.factorial * (n + 1) * (lam + 1 / 2) * (2 * lam - 1 + n)) =
        2 * (lam - 1) * (2 * lam - 1) * poch (2 * lam) n * (lam + 1 / 2) *
          ₂F₁ (-((n : ℂ) + 1)) ((n : ℂ) + 2 * lam - 1) (lam - 1 / 2) ((1 - x) / 2) := by
      linear_combination ((lam + 1 / 2) * (2 * lam - 1 + n)) * hQ' + ((lam + 1 / 2) *
        ₂F₁ (-((n : ℂ) + 1)) ((n : ℂ) + 2 * lam - 1) (lam - 1 / 2) ((1 - x) / 2)) * hpq
    have : (2 * (lam - 1) * ((1 - x ^ 2) * deriv (ultrasphPoly lam n) x -
        (2 * lam - 1) * x * ultrasphPoly lam n x) +
        (n + 1) * (n + 2 * lam - 1) * ultrasphPoly (lam - 1) (n + 1) x) *
        (n.factorial * (n + 1) * (lam + 1 / 2) * (2 * lam - 1 + n)) = 0 := by
      linear_combination (2 * (lam - 1) * (1 - x ^ 2)) * hD - (2 * (lam - 1) * (2 * lam - 1) * x) * hP +
        ((n + 1) * (n + 2 * lam - 1)) * hQ +
        (-4 * (lam - 1) * poch (2 * lam) n * (n + 1) * (2 * lam - 1 + n)) * hdiag
    exact (mul_eq_zero.mp this).resolve_right hM
  exact congrFun key x

@[dlmf 18.9.E16]
theorem jacobi_weighted_derivative {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    deriv (fun t : ℝ => (1 - (t : ℂ)) ^ (α : ℂ) * (1 + (t : ℂ)) ^ (β : ℂ) * jacobiPolyP α β n t) x =
      -2 * (n + 1) * (1 - (x : ℂ)) ^ ((α : ℂ) - 1) * (1 + (x : ℂ)) ^ ((β : ℂ) - 1) *
        jacobiPolyP (α - 1) (β - 1) (n + 1) x := by
  obtain ⟨hx1, hx2⟩ := hx
  have h1 : (1 - (x : ℂ)) ∈ slitPlane := by
    rw [show (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_mem_slitPlane.mpr (by linarith)
  have h2 : (1 + (x : ℂ)) ∈ slitPlane := by
    rw [show (1 + (x : ℂ)) = ((1 + x : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_mem_slitPlane.mpr (by linarith)
  have hne1 : (1 - (x : ℂ)) ≠ 0 := slitPlane_ne_zero h1
  have hne2 : (1 + (x : ℂ)) ≠ 0 := slitPlane_ne_zero h2
  have hA : HasDerivAt (fun t : ℝ => (1 - (t : ℂ)) ^ (α : ℂ))
      ((α : ℂ) * (1 - (x : ℂ)) ^ ((α : ℂ) - 1) * (-1)) x :=
    ((((hasDerivAt_id' (x : ℂ)).const_sub 1).cpow_const (c := (α : ℂ)) h1)).comp_ofReal
  have hB : HasDerivAt (fun t : ℝ => (1 + (t : ℂ)) ^ (β : ℂ))
      ((β : ℂ) * (1 + (x : ℂ)) ^ ((β : ℂ) - 1) * 1) x :=
    ((((hasDerivAt_id' (x : ℂ)).const_add 1).cpow_const (c := (β : ℂ)) h2)).comp_ofReal
  have hP : HasDerivAt (fun t : ℝ => jacobiPolyP α β n t) (deriv (jacobiPolyP α β n) x) x :=
    ((analyticOnNhd_jacobiPolyP α β n) x (Set.mem_univ _)).differentiableAt.hasDerivAt.comp_ofReal
  have hprod := (hA.mul hB).mul hP
  change deriv (((fun t : ℝ => (1 - (t : ℂ)) ^ (α : ℂ)) * fun t : ℝ => (1 + (t : ℂ)) ^ (β : ℂ)) *
    fun t : ℝ => jacobiPolyP α β n t) x = _
  rw [hprod.deriv]
  simp only [Pi.mul_apply]
  have hid := jacobi_weighted_identity (α := α) (β := β) (by simpa using hα) n x
  have hpowA : (1 - (x : ℂ)) ^ (α : ℂ) = (1 - (x : ℂ)) ^ ((α : ℂ) - 1) * (1 - x) := by
    rw [Complex.cpow_sub _ _ hne1, Complex.cpow_one]
    field_simp
  have hpowB : (1 + (x : ℂ)) ^ (β : ℂ) = (1 + (x : ℂ)) ^ ((β : ℂ) - 1) * (1 + x) := by
    rw [Complex.cpow_sub _ _ hne2, Complex.cpow_one]
    field_simp
  rw [hpowA, hpowB]
  linear_combination ((1 - (x : ℂ)) ^ ((α : ℂ) - 1) * (1 + (x : ℂ)) ^ ((β : ℂ) - 1)) * hid

@[dlmf 18.9.E20]
theorem ultrasphPoly_weighted_derivative {lam : ℝ} (hlam : 1 / 2 < lam) (hlam1 : lam ≠ 1)
    (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    deriv (fun t : ℝ => (1 - (t : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2) * ultrasphPoly lam n t) x =
      -(n + 1) * (n + 2 * (lam : ℂ) - 1) / (2 * (lam - 1)) *
        (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 3 / 2) * ultrasphPoly (lam - 1) (n + 1) x := by
  obtain ⟨hx1, hx2⟩ := hx
  have h1 : (1 - (x : ℂ) ^ 2) ∈ slitPlane := by
    rw [show (1 - (x : ℂ) ^ 2) = ((1 - x ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_mem_slitPlane.mpr (by nlinarith)
  have hne1 : (1 - (x : ℂ) ^ 2) ≠ 0 := slitPlane_ne_zero h1
  have hsq : HasDerivAt (fun w : ℂ => 1 - w ^ 2) (-(2 * (x : ℂ))) x := by
    simpa using (hasDerivAt_pow 2 (x : ℂ)).const_sub 1
  have hA : HasDerivAt (fun t : ℝ => (1 - (t : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2))
      (((lam : ℂ) - 1 / 2) * (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2 - 1) * -(2 * (x : ℂ))) x :=
    (hsq.cpow_const (c := (lam : ℂ) - 1 / 2) h1).comp_ofReal
  have hC : HasDerivAt (fun t : ℝ => ultrasphPoly lam n t) (deriv (ultrasphPoly lam n) x) x :=
    ((analyticOnNhd_ultrasphPoly lam n) x (Set.mem_univ _)).differentiableAt.hasDerivAt.comp_ofReal
  have hprod := hA.mul hC
  change deriv ((fun t : ℝ => (1 - (t : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2)) *
    fun t : ℝ => ultrasphPoly lam n t) x = _
  rw [hprod.deriv]
  have hid := ultrasphPoly_weighted_identity (lam := lam) (by simpa using hlam) n x
  have h2 : (2 * ((lam : ℂ) - 1)) ≠ 0 := by
    have : (lam : ℂ) - 1 ≠ 0 := by
      intro h
      apply hlam1
      exact_mod_cast (sub_eq_zero.mp h)
    exact mul_ne_zero two_ne_zero this
  have hpow : (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2) =
      (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 3 / 2) * (1 - (x : ℂ) ^ 2) := by
    rw [show (lam : ℂ) - 3 / 2 = (lam : ℂ) - 1 / 2 - 1 by ring,
      Complex.cpow_sub ((lam : ℂ) - 1 / 2) 1 hne1, Complex.cpow_one]
    field_simp
  rw [hpow, show (lam : ℂ) - 1 / 2 - 1 = (lam : ℂ) - 3 / 2 by ring, div_mul_eq_mul_div,
    div_mul_eq_mul_div, eq_div_iff h2]
  linear_combination ((1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 3 / 2)) * hid

@[dlmf 18.9.E22]
theorem chebyshevU_weighted_derivative (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    deriv (fun t : ℝ => Real.sqrt (1 - t ^ 2) * (Chebyshev.U ℝ n).eval t) x =
      -(n + 1) / Real.sqrt (1 - x ^ 2) * (Chebyshev.T ℝ (n + 1)).eval x := by
  obtain ⟨hx1, hx2⟩ := hx
  have hpos : 0 < 1 - x ^ 2 := by nlinarith
  have hs : Real.sqrt (1 - x ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hsq : Real.sqrt (1 - x ^ 2) * Real.sqrt (1 - x ^ 2) = 1 - x ^ 2 := Real.mul_self_sqrt hpos.le
  have hin : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_sub 1
  have hS : HasDerivAt (fun t : ℝ => Real.sqrt (1 - t ^ 2))
      (-(2 * x) / (2 * Real.sqrt (1 - x ^ 2))) x :=
    hin.sqrt hpos.ne'
  have hU : HasDerivAt (fun t : ℝ => (Chebyshev.U ℝ n).eval t)
      ((Chebyshev.U ℝ n).derivative.eval x) x :=
    Polynomial.hasDerivAt _ x
  have hprod := hS.mul hU
  change deriv ((fun t : ℝ => Real.sqrt (1 - t ^ 2)) * fun t : ℝ => (Chebyshev.U ℝ n).eval t) x = _
  rw [hprod.deriv]
  have hid := congrArg (Polynomial.eval x) (Polynomial.Chebyshev.add_one_mul_T_eq_poly_in_U (R := ℝ) n)
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_intCast] at hid
  push_cast at hid ⊢
  field_simp
  linear_combination hid + ((Chebyshev.U ℝ n).derivative.eval x) * hsq

/-- The polynomial identity behind 18.9.24: `x L' + (α - x) L = (n+1) L^{(α-1)}_{n+1}`, from the
Kummer relation 13.3.13. -/
theorem laguerrePolyL_weighted_identity {α : ℂ} (hα : 0 < α.re) (n : ℕ) (x : ℂ) :
    x * deriv (laguerrePolyL α n) x + (α - x) * laguerrePolyL α n x = (n + 1)
        * laguerrePolyL (α - 1) (n + 1) x := by
  have hb : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hb' : ∀ k : ℕ, α ≠ -(k : ℂ) := not_neg_nat_of_re_pos hα
  have hb0 : α + 1 ≠ 0 := by simpa using hb 0
  have hMd : DifferentiableAt ℂ (kummerM (-(n : ℂ)) (α + 1)) x :=
    ((hasFPowerSeriesOnBall_kummerM (a := -(n : ℂ)) hb).analyticAt_of_mem
      (by simp : x ∈ Metric.eball (0 : ℂ) ⊤)).differentiableAt
  have hderiv : deriv (laguerrePolyL α n) x =
      poch (α + 1) n / n.factorial
          * (-(n : ℂ) / (α + 1) * kummerM (-(n : ℂ) + 1) (α + 1 + 1) x) := by
    show deriv (fun x => poch (α + 1) n / n.factorial * kummerM (-(n : ℂ)) (α + 1) x) x = _
    rw [deriv_const_mul _ hMd, DLMF.Confluent.deriv_kummerM hb hb0]
  have hode := DLMF.Confluent.kummerM_ode_contiguous (a := -((n : ℂ) + 1)) (b := α) (z := x) hb'
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hM : (n.factorial : ℂ) * (n + 1) * (α + 1) ≠ 0 := mul_ne_zero (mul_ne_zero hf hn1) hb0
  have hL : laguerrePolyL α n x * (n.factorial * (n + 1) * (α + 1)) =
      poch (α + 1) n * (n + 1) * (α + 1) * kummerM (-((n : ℂ) + 1) + 1) (α + 1) x := by
    unfold laguerrePolyL
    rw [show -((n : ℂ) + 1) + 1 = -(n : ℂ) by ring]
    field_simp
  have hD : deriv (laguerrePolyL α n) x * (n.factorial * (n + 1) * (α + 1)) =
      poch (α + 1) n * (n + 1) * (-(n : ℂ)) * kummerM (-((n : ℂ) + 1) + 2) (α + 2) x := by
    rw [hderiv, show -((n : ℂ) + 1) + 2 = -(n : ℂ) + 1 by ring, show α + 2 = α + 1 + 1 by ring]
    field_simp
  have hQ : laguerrePolyL (α - 1) (n + 1) x * (n.factorial * (n + 1) * (α + 1)) =
      α * poch (α + 1) n * (α + 1) * kummerM (-((n : ℂ) + 1)) α x := by
    unfold laguerrePolyL
    rw [show α - 1 + 1 = α by ring, poch_succ_left, Nat.factorial_succ]
    push_cast
    field_simp
  apply mul_right_cancel₀ hM
  linear_combination x * hD + (α - x) * hL - (n + 1) * hQ + (poch (α + 1) n * (n + 1)) * hode

@[dlmf 18.9.E24]
theorem laguerrePolyL_weighted_derivative {α : ℝ} (hα : 0 < α) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    deriv (fun t : ℝ => exp (-t) * (t : ℂ) ^ (α : ℂ) * laguerrePolyL α n t) x =
      (n + 1) * exp (-x) * (x : ℂ) ^ ((α : ℂ) - 1) * laguerrePolyL (α - 1) (n + 1) x := by
  have hxs : (x : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hx
  have hx0 : (x : ℂ) ≠ 0 := slitPlane_ne_zero hxs
  have hb : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith)
  have hMd : DifferentiableAt ℂ (kummerM (-(n : ℂ)) ((α : ℂ) + 1)) x :=
    ((hasFPowerSeriesOnBall_kummerM (a := -(n : ℂ)) hb).analyticAt_of_mem
      (by simp : (x : ℂ) ∈ Metric.eball (0 : ℂ) ⊤)).differentiableAt
  have hLd : DifferentiableAt ℂ (laguerrePolyL α n) x := by
    show DifferentiableAt ℂ (fun x => poch ((α : ℂ) + 1) n / n.factorial *
      kummerM (-(n : ℂ)) ((α : ℂ) + 1) x) x
    exact hMd.const_mul _
  have hE : HasDerivAt (fun t : ℝ => exp (-(t : ℂ))) (exp (-(x : ℂ)) * -1) x :=
    ((hasDerivAt_id' (x : ℂ)).neg.cexp).comp_ofReal
  have hT : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (α : ℂ)) ((α : ℂ) * (x : ℂ) ^ ((α : ℂ) - 1) * 1) x :=
    ((hasDerivAt_id' (x : ℂ)).cpow_const (c := (α : ℂ)) hxs).comp_ofReal
  have hL : HasDerivAt (fun t : ℝ => laguerrePolyL α n t) (deriv (laguerrePolyL α n) x) x :=
    hLd.hasDerivAt.comp_ofReal
  have hprod := (hE.mul hT).mul hL
  change deriv (((fun t : ℝ => exp (-(t : ℂ))) * fun t : ℝ => (t : ℂ) ^ (α : ℂ)) *
    fun t : ℝ => laguerrePolyL α n t) x = _
  rw [hprod.deriv]
  simp only [Pi.mul_apply]
  have hid := laguerrePolyL_weighted_identity (α := α) (by simpa using hα) n x
  have hpow : (x : ℂ) ^ (α : ℂ) = (x : ℂ) ^ ((α : ℂ) - 1) * x := by
    rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one]
    field_simp
  rw [hpow]
  linear_combination (exp (-(x : ℂ)) * (x : ℂ) ^ ((α : ℂ) - 1)) * hid


end DLMF.OrthogonalPolynomials
