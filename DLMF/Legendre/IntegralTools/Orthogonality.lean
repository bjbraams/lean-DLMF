/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework
public import DLMF.Legendre.AssociatedRecurrences
public import DLMF.Legendre.Laplace

/-!
# Orthogonality tools for Legendre integrals

Weighted orthogonality and integration-by-parts estimates for associated Legendre and Ferrers
functions.

Source references and common attribution are retained in
`DLMF.Legendre.IntegralTools`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Legendre

open DLMF.OrthogonalPolynomials

/-- `m`-th derivative of the Legendre polynomial `P_n`, as an entire function. -/
abbrev legInt_D (n m : ℕ) : ℂ → ℂ := iteratedDeriv m (legendrePolyP n)

/-- `P_n^{(m)}` is entire. -/
theorem legInt_analytic_D (n m : ℕ) : AnalyticOnNhd ℂ (legInt_D n m) univ := by
  rw [legInt_D, iteratedDeriv_eq_iterate]
  exact (show AnalyticOnNhd ℂ (legendrePolyP n) univ from analyticOnNhd_jacobiPolyP 0 0 n).iterated_deriv m

/-- Complex derivative of `P_n^{(m)}`. -/
theorem legInt_hasDerivAt_D (n m : ℕ) (z : ℂ) :
    HasDerivAt (legInt_D n m) (legInt_D n (m+1) z) z := by
  show HasDerivAt (iteratedDeriv m _) (iteratedDeriv (m+1) _ z) z
  rw [iteratedDeriv_succ]
  exact ((legInt_analytic_D n m z (mem_univ _)).differentiableAt).hasDerivAt

/-- Real-variable derivative of `P_n^{(m)}`. -/
theorem legInt_hasDerivAt_D_real (n m : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => legInt_D n m x) (legInt_D n (m+1) x) x :=
  (legInt_hasDerivAt_D n m x).comp_ofReal

/-- The Legendre equation differentiated `m` times. -/
theorem legInt_ode (n m : ℕ) (z : ℂ) :
    (1 - z^2) * legInt_D n (m+2) z - 2*(m+1)*z*legInt_D n (m+1) z
      + ((n:ℂ)*(n+1) - m*(m+1)) * legInt_D n m z = 0 := by
  induction m generalizing z with
  | zero =>
    have h := legendre_differential_equation n z
    simp only [legInt_D, iteratedDeriv_succ, iteratedDeriv_zero] at h ⊢
    push_cast
    linear_combination h
  | succ m ih =>
    have h := ((((hasDerivAt_pow 2 z).const_sub 1).mul (legInt_hasDerivAt_D n (m+2) z)).sub
      (((hasDerivAt_id' z).const_mul (2*((m:ℂ)+1))).mul (legInt_hasDerivAt_D n (m+1) z))).add
      ((legInt_hasDerivAt_D n m z).const_mul ((n:ℂ)*(n+1) - m*(m+1)))
    have h0 : HasDerivAt (fun z => (1 - z^2) * legInt_D n (m+2) z - 2*(m+1)*z*legInt_D n (m+1) z
      + ((n:ℂ)*(n+1) - m*(m+1)) * legInt_D n m z) 0 z := by
      rw [show (fun z => (1 - z^2) * legInt_D n (m+2) z - 2*(m+1)*z*legInt_D n (m+1) z
        + ((n:ℂ)*(n+1) - m*(m+1)) * legInt_D n m z) = fun _ => 0 from funext ih]
      exact hasDerivAt_const _ _
    have hu := h.unique h0
    push_cast
    linear_combination hu

/-- The weighted moment `∫ (1-x²)^m P_l^{(m)} P_n^{(m)}`. -/
abbrev legInt_I (m l n : ℕ) : ℂ :=
  ∫ x : ℝ in (-1:ℝ)..1, (1-(x:ℂ)^2)^m * legInt_D l m x * legInt_D n m x

/-- `x ↦ P_n^{(m)}(x)` is continuous on `ℝ`. -/
theorem legInt_cont_D (n m : ℕ) : Continuous fun x : ℝ => legInt_D n m x :=
  continuous_iff_continuousAt.mpr fun x => (legInt_hasDerivAt_D_real n m x).continuousAt

/-- Moment recursion by integration by parts and the differentiated Legendre equation. -/
theorem legInt_I_succ (m l n : ℕ) :
    legInt_I (m+1) l n = ((n:ℂ)-m)*(n+m+1) * legInt_I m l n := by
  have hv : ∀ x ∈ uIcc (-1:ℝ) 1, HasDerivAt (fun x : ℝ => (1-(x:ℂ)^2)^(m+1) * legInt_D n (m+1) x)
      (-(((n:ℂ)-m)*(n+m+1)) * ((1-(x:ℂ)^2)^m * legInt_D n m x)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => (1-(x:ℂ)^2)) (-(2*(x:ℂ))) x := by
      have := ((hasDerivAt_id (x:ℂ)).pow 2).const_sub 1 |>.comp_ofReal
      simpa using this
    have h := (h1.pow (m+1)).mul (legInt_hasDerivAt_D_real n (m+1) x)
    refine h.congr_deriv ?_
    have hode := legInt_ode n m x
    simp only [Pi.pow_apply, Nat.add_sub_cancel]
    push_cast
    linear_combination (1-(x:ℂ)^2)^m * hode
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => legInt_hasDerivAt_D_real l m x) hv
    ((legInt_cont_D l (m+1)).intervalIntegrable _ _)
    (by apply Continuous.intervalIntegrable; have := legInt_cont_D n m; fun_prop)
  simp only [ofReal_one, ofReal_neg, one_pow, sub_self, even_two, Even.neg_pow,
    zero_pow (Nat.succ_ne_zero m), zero_mul, mul_zero] at hibp
  have e1 : (∫ x : ℝ in (-1:ℝ)..1, legInt_D l m x * (-(((n:ℂ)-m)*(n+m+1)) *
      ((1-(x:ℂ)^2)^m * legInt_D n m x))) = -(((n:ℂ)-m)*(n+m+1)) * legInt_I m l n := by
    rw [legInt_I, ← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  have e2 : (∫ x : ℝ in (-1:ℝ)..1, legInt_D l (m+1) x * ((1-(x:ℂ)^2)^(m+1) *
      legInt_D n (m+1) x)) = legInt_I (m+1) l n := by
    rw [legInt_I]; congr 1; funext x; ring
  rw [e1, e2] at hibp
  linear_combination hibp

/-- Closed form of the weighted moments from Legendre orthogonality. -/
theorem legInt_I_eq (m l n : ℕ) :
    legInt_I m l n = (∏ k ∈ Finset.range m, (((n:ℂ)-k)*(n+k+1))) *
      (if l = n then 2/(2*(n:ℂ)+1) else 0) := by
  induction m with
  | zero =>
    simp only [legInt_I, pow_zero, one_mul, Finset.range_zero, Finset.prod_empty, legInt_D,
      iteratedDeriv_zero]
    exact legendre_orthogonality l n
  | succ m ih => rw [legInt_I_succ, ih, Finset.prod_range_succ]; ring

/-- `∏_{k<m} (n-k)(n+k+1) · (n-m)! = (n+m)!` for `m ≤ n`. -/
theorem legInt_prod_factorial {m n : ℕ} (h : m ≤ n) :
    (∏ k ∈ Finset.range m, (((n:ℂ)-k)*(n+k+1))) * ((n-m).factorial : ℂ) = ((n+m).factorial : ℂ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ih := ih (by omega)
    rw [Finset.prod_range_succ]
    have e : n - m = (n-(m+1)) + 1 := by omega
    rw [e, Nat.factorial_succ] at ih
    rw [show n + (m+1) = (n+m) + 1 by omega, Nat.factorial_succ]
    have hc : ((n-(m+1)+1 : ℕ) : ℂ) = (n:ℂ) - m := by
      rw [Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring
    push_cast at ih ⊢
    rw [← ih]
    rw [show ((n - (m+1) : ℕ) : ℂ) + 1 = ((n-(m+1)+1 : ℕ) : ℂ) by push_cast; ring, hc]
    ring

/-- Ferrers functions of integer degree and order via derivatives of the Legendre polynomial. -/
theorem legInt_ferrersP_nat_nat (n m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP n m x = (-1)^m * (((1-x^2)^((m:ℝ)/2) : ℝ) : ℂ) * legInt_D n m x := by
  have hs : 1+(x:ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  have hev : legendreP (n:ℂ) =ᶠ[𝓝 (x:ℂ)] legendrePolyP n := by
    filter_upwards [isOpen_one_add_mem_slitPlane.mem_nhds hs] with w hw
    rw [legendreP_nat n hw]
  rw [ferrersP_nat n m hx, hev.iteratedDeriv_eq]

/-- Product of two Ferrers functions of integer degree and equal integer order. -/
theorem legInt_ferrersP_mul (l n m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP l m x * ferrersP n m x = (1-(x:ℂ)^2)^m * legInt_D l m x * legInt_D n m x := by
  rw [legInt_ferrersP_nat_nat l m hx, legInt_ferrersP_nat_nat n m hx]
  have h0 : (0:ℝ) ≤ 1 - x^2 := by nlinarith [hx.1, hx.2]
  have hr : ((1-x^2)^((m:ℝ)/2)) * ((1-x^2)^((m:ℝ)/2)) = (1-x^2)^m := by
    rw [← sq, ← Real.rpow_natCast ((1-x^2)^((m:ℝ)/2)) 2, ← Real.rpow_mul h0,
      ← Real.rpow_natCast (1-x^2) m]
    congr 1; push_cast; ring
  have hr' := congrArg (fun r : ℝ => (r:ℂ)) hr
  push_cast at hr'
  have hsq : (-1:ℂ)^m*(-1)^m = 1 := by rw [← mul_pow]; norm_num
  linear_combination (legInt_D l m x * legInt_D n m x) * hr' +
    (((1-x^2)^((m:ℝ)/2) : ℝ) : ℂ)^2 * legInt_D l m x * legInt_D n m x * hsq

/-- `𝐅(a,b;c;z) = c 𝐅(a,b;c+1;z) + a b z 𝐅(a+1,b+1;c+2;z)` on the cut plane. -/
theorem legInt_contiguous (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    regularizedGaussHG a b c z = c * regularizedGaussHG a b (c+1) z +
      a * b * z * regularizedGaussHG (a+1) (b+1) (c+2) z := by
  have h1 := regularizedGaussHG_contiguous_c a b c hz
  have h2 := regularizedGaussHG_contiguous_shift_b b a (c+1) hz
  rw [regularizedGaussHG_symm b a _ hz, regularizedGaussHG_symm b (a+1) _ hz,
    regularizedGaussHG_symm (b+1) (a+1) _ hz, show c+1+1 = c+2 by ring] at h2
  linear_combination h1 - a * h2

/-- `d/dw [w^{k+1} 𝐅(a,b;k+2;w)] = w^k 𝐅(a,b;k+1;w)` on the cut plane. -/
theorem legInt_hasDerivAt_G (a b : ℂ) (k : ℕ) {w : ℂ} (hw : w ∈ cutPlane) :
    HasDerivAt (fun w => w^(k+1) * regularizedGaussHG a b ((k:ℂ)+2) w)
      (w^k * regularizedGaussHG a b ((k:ℂ)+1) w) w := by
  have hF := (differentiableAt_regularizedGaussHG a b ((k:ℂ)+2) hw).hasDerivAt
  rw [deriv_regularizedGaussHG _ _ _ hw] at hF
  have hc := legInt_contiguous a b ((k:ℂ)+1) hw
  rw [show (k:ℂ)+1+1 = k+2 by ring, show (k:ℂ)+1+2 = k+2+1 by ring] at hc
  refine ((hasDerivAt_pow (k+1) w).mul hF).congr_deriv ?_
  rw [hc]; push_cast; ring

/-- `H_k(x) = (1-x)^k 𝐅(a,b;k+1;(1-x)/2)`. -/
def legInt_H (a b : ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  (1-(x:ℂ))^k * regularizedGaussHG a b ((k:ℂ)+1) ((1-x)/2)

/-- `(1-x)/2` lies in the cut plane for `x > -1`. -/
theorem legInt_half_mem_cutPlane {x : ℝ} (hx : -1 < x) : (1-(x:ℂ))/2 ∈ cutPlane := by
  rw [mem_cutPlane]; left; simp; linarith

/-- `H_{k+1}' = -H_k` on `(-1,∞)`. -/
theorem legInt_hasDerivAt_H (a b : ℂ) (k : ℕ) {x : ℝ} (hx : -1 < x) :
    HasDerivAt (legInt_H a b (k+1)) (-legInt_H a b k x) x := by
  have hw := legInt_half_mem_cutPlane hx
  have hψ : HasDerivAt (fun z : ℂ => (1-z)/2) (-1/2) (x:ℂ) := by
    simpa using ((hasDerivAt_id' (x:ℂ)).const_sub 1).div_const 2
  have h := (((legInt_hasDerivAt_G a b k hw).comp (x:ℂ) hψ).comp_ofReal).const_mul (2^(k+1):ℂ)
  have e : legInt_H a b (k+1) = fun x : ℝ => (2^(k+1):ℂ) *
      ((fun w => w^(k+1) * regularizedGaussHG a b ((k:ℂ)+2) w) ∘ fun z : ℂ => (1-z)/2) x := by
    funext y
    simp only [legInt_H, Function.comp, div_pow]
    push_cast
    rw [show (k:ℂ)+1+1 = k+2 by ring]
    field_simp
  rw [e]
  refine h.congr_deriv ?_
  simp only [legInt_H, div_pow, pow_succ]
  field_simp

/-- `H_k` is continuous on `(-1,∞)`. -/
theorem legInt_continuousAt_H (a b : ℂ) (k : ℕ) {x : ℝ} (hx : -1 < x) :
    ContinuousAt (legInt_H a b k) x := by
  have hw := legInt_half_mem_cutPlane hx
  unfold legInt_H
  refine ContinuousAt.mul (by fun_prop) ?_
  exact ContinuousAt.comp (g := regularizedGaussHG a b ((k:ℂ)+1))
    (differentiableAt_regularizedGaussHG a b _ hw).continuousAt (by fun_prop)

/-- `H_{k+1}(1) = 0`. -/
theorem legInt_H_one (a b : ℂ) (k : ℕ) : legInt_H a b (k+1) 1 = 0 := by
  simp [legInt_H]

/-- `∫_x^1 H_k = H_{k+1}(x)` for `x > -1`. -/
theorem legInt_integral_H (a b : ℂ) (k : ℕ) {x : ℝ} (hx : -1 < x) :
    ∫ t in x..1, legInt_H a b k t = legInt_H a b (k+1) x := by
  have hsub : ∀ t ∈ uIcc x 1, -1 < t := fun t ht => by
    rcases le_total x 1 with h | h
    · rw [uIcc_of_le h] at ht; linarith [ht.1]
    · rw [uIcc_of_ge h] at ht; linarith [ht.1]
  have hint : IntervalIntegrable (fun t => -legInt_H a b k t) volume x 1 :=
    (ContinuousOn.neg fun t ht => (legInt_continuousAt_H a b k (hsub t ht)).continuousWithinAt
      ).intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => legInt_hasDerivAt_H a b k (hsub t ht)) hint
  rw [intervalIntegral.integral_neg, legInt_H_one] at h
  linear_combination -h

/-- Iterated integrals of `𝖯_ν` from the endpoint `1`. -/
theorem legInt_iterate_ferrers (ν : ℂ) (k : ℕ) {x : ℝ} (hx : x ∈ Ioc (-1:ℝ) 1) :
    ((fun f : ℝ → ℂ => fun x => ∫ t : ℝ in x..1, f t)^[k]) (ferrersP ν 0) x =
      legInt_H (ν+1) (-ν) k x := by
  induction k generalizing x with
  | zero => simp [legInt_H, ferrersP]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rw [← legInt_integral_H _ _ k hx.1]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hx.2] at ht
    exact ih ⟨by linarith [hx.1, ht.1], ht.2⟩

/-- `K_k(w) = (w-1)^k 𝐅(a,b;k+1;(1-w)/2)`. -/
def legInt_K (a b : ℂ) (k : ℕ) (w : ℂ) : ℂ :=
  (w-1)^k * regularizedGaussHG a b ((k:ℂ)+1) ((1-w)/2)

/-- `K_{k+1}' = K_k` where `1+w` lies in the slit plane. -/
theorem legInt_hasDerivAt_K (a b : ℂ) (k : ℕ) {w : ℂ} (hw : 1+w ∈ slitPlane) :
    HasDerivAt (legInt_K a b (k+1)) (legInt_K a b k w) w := by
  have hc := mem_cutPlane_of_one_add hw
  have hψ : HasDerivAt (fun z : ℂ => (1-z)/2) (-1/2) w := by
    simpa using ((hasDerivAt_id' w).const_sub 1).div_const 2
  have h := ((legInt_hasDerivAt_G a b k hc).comp w hψ).const_mul ((-2)^(k+1):ℂ)
  have e : legInt_K a b (k+1) = fun w : ℂ => ((-2)^(k+1):ℂ) *
      ((fun w => w^(k+1) * regularizedGaussHG a b ((k:ℂ)+2) w) ∘ fun z : ℂ => (1-z)/2) w := by
    funext y
    simp only [legInt_K, Function.comp]
    push_cast
    rw [show (k:ℂ)+1+1 = k+2 by ring, ← mul_assoc, ← mul_pow]
    congr 2; ring
  rw [e]
  refine h.congr_deriv ?_
  simp only [legInt_K]
  rw [show w - 1 = (-2) * ((1-w)/2) by ring, mul_pow, pow_succ]
  ring

/-- `K_k` is continuous where `1+w` lies in the slit plane. -/
theorem legInt_continuousAt_K (a b : ℂ) (k : ℕ) {w : ℂ} (hw : 1+w ∈ slitPlane) :
    ContinuousAt (legInt_K a b k) w := by
  have hc := mem_cutPlane_of_one_add hw
  unfold legInt_K
  refine ContinuousAt.mul (by fun_prop) ?_
  exact ContinuousAt.comp (g := regularizedGaussHG a b ((k:ℂ)+1))
    (differentiableAt_regularizedGaussHG a b _ hc).continuousAt (by fun_prop)

/-- `1+t` lies in the slit plane for real `t ≥ 1`. -/
theorem legInt_one_add_ofReal_mem {t : ℝ} (ht : 1 ≤ t) : 1 + (t:ℂ) ∈ slitPlane :=
  Or.inl (by simp; linarith)

/-- `∫_1^x K_k = K_{k+1}(x)` for `x ≥ 1`. -/
theorem legInt_integral_K (a b : ℂ) (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in (1:ℝ)..x, legInt_K a b k t = legInt_K a b (k+1) x := by
  have hsub : ∀ t ∈ uIcc 1 x, 1 ≤ t := fun t ht => by rw [uIcc_of_le hx] at ht; exact ht.1
  have hco : ContinuousOn (fun t : ℝ => legInt_K a b k t) (uIcc 1 x) := fun t ht =>
    ((legInt_continuousAt_K a b k (legInt_one_add_ofReal_mem (hsub t ht))).comp
      continuous_ofReal.continuousAt).continuousWithinAt
  have hint := hco.intervalIntegrable (μ := volume)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => legInt_K a b (k+1) t)
    (fun t ht => (legInt_hasDerivAt_K a b k (legInt_one_add_ofReal_mem (hsub t ht))).comp_ofReal) hint
  rw [h]; simp [legInt_K]

/-- Iterated integrals of `P_ν` from `1` on the real half-line. -/
theorem legInt_iterate_associated (ν : ℂ) (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ((fun f : ℝ → ℂ => fun x => ∫ t : ℝ in (1:ℝ)..x, f t)^[k]) (fun x : ℝ => associatedP ν 0 x) x =
      legInt_K (ν+1) (-ν) k x := by
  induction k generalizing x with
  | zero => simp [legInt_K, associatedP]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← legInt_integral_K _ _ k hx]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hx] at ht
    exact ih ht.1

/-- `𝐏^{-m}_ν(z) = (z²-1)^{-m/2} K_m(z)` on the principal sheet. -/
theorem legInt_associatedP_neg_nat (ν : ℂ) (m : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν (-m) z = legendreBranchPower (-m) z * legInt_K (ν+1) (-ν) m z := by
  have hne : z - 1 ≠ 0 := slitPlane_ne_zero hz
  unfold associatedP legendreBranchPower legInt_K
  have e : (z-1)^m = exp (log (z-1) * m) := by rw [← cpow_natCast, cpow_def_of_ne_zero hne]
  rw [show (1:ℂ) - -(m:ℂ) = m+1 by ring, e, ← mul_assoc, ← exp_add]
  congr 2; ring

/-- On `(1,∞)` the principal branch power is `(x²-1)^{μ/2}`. -/
theorem legInt_legendreBranchPower_real (μ : ℂ) {x : ℝ} (hx : 1 < x) :
    legendreBranchPower μ x = ((x:ℂ)^2-1)^(μ/2) := by
  have h1 : (0:ℝ) < x-1 := by linarith
  have h2 : (0:ℝ) < x+1 := by linarith
  have l1 : log ((x:ℂ)-1) = (Real.log (x-1):ℂ) := by
    rw [show (x:ℂ)-1 = ((x-1:ℝ):ℂ) by push_cast; ring, ofReal_log h1.le]
  have l2 : log ((x:ℂ)+1) = (Real.log (x+1):ℂ) := by
    rw [show (x:ℂ)+1 = ((x+1:ℝ):ℂ) by push_cast; ring, ofReal_log h2.le]
  have hne : ((x:ℂ)^2-1) ≠ 0 := by
    rw [show (x:ℂ)^2-1 = ((x^2-1:ℝ):ℂ) by push_cast; ring]
    exact_mod_cast (by nlinarith : (x^2-1:ℝ) ≠ 0)
  have l3 : log ((x:ℂ)^2-1) = (Real.log (x-1):ℂ) + Real.log (x+1) := by
    rw [show (x:ℂ)^2-1 = (((x-1)*(x+1):ℝ):ℂ) by push_cast; ring,
      ← ofReal_log (by positivity : (0:ℝ) ≤ (x-1)*(x+1)), Real.log_mul h1.ne' h2.ne']
    push_cast; ring
  rw [legendreBranchPower, cpow_def_of_ne_zero hne, l1, l2, l3]
  congr 1; ring

/-- The slit plane is invariant under multiplication by positive reals. -/
theorem legInt_ofReal_mul_mem {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ∈ slitPlane) :
    (t:ℂ)*z ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  rw [re_ofReal_mul, im_ofReal_mul]
  rcases hz with h | h
  · exact Or.inl (mul_pos ht h)
  · exact Or.inr (mul_ne_zero ht.ne' h)

/-- Adding a positive real keeps `0` or a slit-plane point in the slit plane. -/
theorem legInt_ofReal_add_mem {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z = 0 ∨ z ∈ slitPlane) :
    (r:ℂ)+z ∈ slitPlane := by
  rcases hz with rfl | hz
  · simpa using hr
  rw [mem_slitPlane_iff] at hz ⊢
  rw [add_re, add_im, ofReal_re, ofReal_im, zero_add]
  by_cases h : z.im = 0
  · rcases hz with h' | h'
    · exact Or.inl (by linarith)
    · exact absurd h h'
  · exact Or.inr h

/-- Points of the segment `[1,w]` are `1` or lie in `1 + slitPlane`. -/
theorem legInt_seg_mem {w : ℂ} (hw : w = 1 ∨ w-1 ∈ slitPlane) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (1 + (t:ℂ)*(w-1)) = 1 ∨ (1 + (t:ℂ)*(w-1)) - 1 ∈ slitPlane := by
  rcases hw with rfl | hw
  · left; simp
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · left; rw [← h0]; simp
  right
  rw [add_sub_cancel_left]
  exact legInt_ofReal_mul_mem h0 hw

/-- For `p` on the segment `[1,w]`, `1+p` lies in the slit plane. -/
theorem legInt_two_add_mem {w : ℂ} (hw : w = 1 ∨ w-1 ∈ slitPlane) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    1 + (1 + (t:ℂ)*(w-1)) ∈ slitPlane := by
  rw [show 1 + (1 + (t:ℂ)*(w-1)) = ((2:ℝ):ℂ) + (1 + (t:ℂ)*(w-1) - 1) by push_cast; ring]
  refine legInt_ofReal_add_mem two_pos ?_
  rcases legInt_seg_mem hw ht with h | h
  · left; rw [h]; ring
  · exact Or.inr h

/-- Iterated segment integrals of `P_ν` from `1`. -/
theorem legInt_iterate_segment (ν : ℂ) (k : ℕ) {w : ℂ} (hw : w = 1 ∨ w-1 ∈ slitPlane) :
    ((fun f : ℂ → ℂ => fun z => segmentIntegral f 1 z)^[k]) (associatedP ν 0) w =
      legInt_K (ν+1) (-ν) k w := by
  induction k generalizing w with
  | zero => simp [legInt_K, associatedP]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    show segmentIntegral _ 1 w = _
    rw [segmentIntegral]
    have hc : (∫ t : ℝ in (0:ℝ)..1, ((fun f : ℂ → ℂ => fun z => segmentIntegral f 1 z)^[k])
        (associatedP ν 0) (1 + t*(w-1))) =
        ∫ t : ℝ in (0:ℝ)..1, legInt_K (ν+1) (-ν) k (1 + t*(w-1)) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le zero_le_one] at ht
      exact ih (legInt_seg_mem hw ht)
    rw [hc, mul_comm, ← intervalIntegral.integral_mul_const]
    have hd : ∀ t ∈ uIcc (0:ℝ) 1, HasDerivAt (fun t : ℝ => legInt_K (ν+1) (-ν) (k+1) (1 + t*(w-1)))
        (legInt_K (ν+1) (-ν) k (1 + t*(w-1)) * (w-1)) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hl : HasDerivAt (fun t : ℝ => 1 + (t:ℂ)*(w-1)) (1*(w-1)) t :=
        ((hasDerivAt_id t).ofReal_comp.mul_const (w-1)).const_add 1
      rw [one_mul] at hl
      exact (legInt_hasDerivAt_K _ _ k (legInt_two_add_mem hw ht)).comp t hl
    have hco : ContinuousOn (fun t : ℝ => legInt_K (ν+1) (-ν) k (1 + t*(w-1)) * (w-1))
        (uIcc 0 1) := fun t ht => by
      have ht' := ht; rw [uIcc_of_le zero_le_one] at ht'
      refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ continuousAt_const)
      exact ContinuousAt.comp (g := legInt_K (ν+1) (-ν) k)
        (legInt_continuousAt_K _ _ k (legInt_two_add_mem hw ht')) (by fun_prop)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hco.intervalIntegrable)]
    simp [legInt_K]

/-! ### Orthogonality with weight `1/(1-x²)` -/

/-- `J_k = ∫ (1-x²)^k (P_n^{(k+1)})²`. -/
abbrev legInt_J (k n : ℕ) : ℂ :=
  ∫ x : ℝ in (-1:ℝ)..1, (1-(x:ℂ)^2)^k * (legInt_D n (k+1) x)^2

/-- Derivative of `1-x²` as a complex-valued function of a real variable. -/
theorem legInt_hasDerivAt_one_sub_sq (x : ℝ) :
    HasDerivAt (fun x : ℝ => 1-(x:ℂ)^2) (-(2*(x:ℂ))) x := by
  have := ((hasDerivAt_id (x:ℂ)).pow 2).const_sub 1 |>.comp_ofReal
  simpa using this

/-- `∫ (P_n')² = n(n+1)`. -/
theorem legInt_J_zero (n : ℕ) : legInt_J 0 n = n*(n+1) := by
  set c : ℂ := (n:ℂ)*(n+1)
  have hd : ∀ x ∈ uIcc (-1:ℝ) 1, HasDerivAt (fun x : ℝ => (x:ℂ)*(1-(x:ℂ)^2)*(legInt_D n 1 x)^2
      + c*x*(legInt_D n 0 x)^2 + (1-(x:ℂ)^2)*legInt_D n 1 x*legInt_D n 0 x)
      (2*(legInt_D n 1 x)^2) x := by
    intro x _
    have hx := (hasDerivAt_id x).ofReal_comp
    have h1 := legInt_hasDerivAt_one_sub_sq x
    have p0 := legInt_hasDerivAt_D_real n 0 x
    have p1 := legInt_hasDerivAt_D_real n 1 x
    have h := (((hx.mul h1).mul (p1.pow 2)).add (((hx.const_mul c).mul (p0.pow 2)))).add
      ((h1.mul p1).mul p0)
    refine h.congr_deriv ?_
    have hode := legInt_ode n 0 x
    simp only [Nat.cast_zero, zero_add] at hode
    simp only [Pi.mul_apply, Pi.pow_apply, id, ofReal_one, Nat.cast_ofNat, zero_add, Nat.reduceAdd]
    linear_combination (2*(x:ℂ)*legInt_D n 1 x + legInt_D n 0 x) * hode
  have hco : Continuous fun x : ℝ => 2*(legInt_D n 1 x)^2 := by
    have := legInt_cont_D n 1; fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hco.intervalIntegrable _ _)
  have e1 := (LegendreSingular.endpoints n).1
  have e2 := (LegendreSingular.endpoints n).2
  simp only [legInt_D, iteratedDeriv_zero, ofReal_one, ofReal_neg, one_pow, sub_self, mul_zero,
    zero_mul, add_zero, zero_add, even_two, Even.neg_pow, e1, e2] at h
  rw [intervalIntegral.integral_const_mul] at h
  have hsq : ((-1:ℂ)^n)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [hsq] at h
  simp only [legInt_J, pow_zero, one_mul]
  linear_combination h/2

/-- Recursion `(j+2) J_{j+1} = (j+1)(n-j-1)(n+j+2) J_j`. -/
theorem legInt_J_succ (j n : ℕ) :
    ((j:ℂ)+2) * legInt_J (j+1) n = ((j:ℂ)+1)*(((n:ℂ)-(j+1))*(n+(j+1)+1)) * legInt_J j n := by
  set c : ℂ := ((n:ℂ)-(j+1))*(n+(j+1)+1)
  have hd : ∀ x ∈ uIcc (-1:ℝ) 1, HasDerivAt (fun x : ℝ =>
      (x:ℂ)*(1-(x:ℂ)^2)^(j+2)*(legInt_D n (j+2) x)^2
      + c*x*(1-(x:ℂ)^2)^(j+1)*(legInt_D n (j+1) x)^2
      + (2*(j:ℂ)+3)*(1-(x:ℂ)^2)^(j+2)*legInt_D n (j+2) x*legInt_D n (j+1) x)
      (2*((j:ℂ)+2)*((1-(x:ℂ)^2)^(j+1)*(legInt_D n (j+2) x)^2)
        - 2*((j:ℂ)+1)*c*((1-(x:ℂ)^2)^j*(legInt_D n (j+1) x)^2)) x := by
    intro x _
    have hx := (hasDerivAt_id x).ofReal_comp
    have h1 := legInt_hasDerivAt_one_sub_sq x
    have p1 := legInt_hasDerivAt_D_real n (j+1) x
    have p2 := legInt_hasDerivAt_D_real n (j+2) x
    have h := (((hx.mul (h1.pow (j+2))).mul (p2.pow 2)).add
      ((((hx.const_mul c).mul (h1.pow (j+1))).mul (p1.pow 2)))).add
      (((h1.pow (j+2)).const_mul (2*(j:ℂ)+3)).mul p2 |>.mul p1)
    refine h.congr_deriv ?_
    have hode := legInt_ode n (j+1) x
    simp only [Pi.mul_apply, Pi.pow_apply, id, ofReal_one, Nat.cast_ofNat, Nat.cast_add,
      Nat.cast_one, Nat.add_sub_cancel] at hode ⊢
    rw [show j+1+2 = j+3 by ring, show j+2+1 = j+3 by ring, show j+1+1 = j+2 by ring,
      show j+2-1 = j+1 by omega] at *
    simp only [c]
    linear_combination (2*(x:ℂ)*(1-(x:ℂ)^2)^(j+1)*legInt_D n (j+2) x
      + (2*(j:ℂ)+3)*(1-(x:ℂ)^2)^(j+1)*legInt_D n (j+1) x) * hode
  have hco1 : Continuous fun x : ℝ => (1-(x:ℂ)^2)^(j+1)*(legInt_D n (j+2) x)^2 := by
    have := legInt_cont_D n (j+2); fun_prop
  have hco0 : Continuous fun x : ℝ => (1-(x:ℂ)^2)^j*(legInt_D n (j+1) x)^2 := by
    have := legInt_cont_D n (j+1); fun_prop
  have hint : IntervalIntegrable (fun x : ℝ =>
      2*((j:ℂ)+2)*((1-(x:ℂ)^2)^(j+1)*(legInt_D n (j+2) x)^2)
        - 2*((j:ℂ)+1)*c*((1-(x:ℂ)^2)^j*(legInt_D n (j+1) x)^2)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_sub ((hco1.intervalIntegrable _ _).const_mul _)
    ((hco0.intervalIntegrable _ _).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h
  simp only [ofReal_one, ofReal_neg, one_pow, sub_self, even_two, Even.neg_pow,
    zero_pow (Nat.succ_ne_zero _), mul_zero, zero_mul, add_zero] at h
  simp only [legInt_J, show j+1+1 = j+2 by ring]
  linear_combination h/2

/-- Closed form `(k+1) J_k (n-k-1)! = (n+k+1)!` for `k+1 ≤ n`. -/
theorem legInt_J_eq {k n : ℕ} (h : k+1 ≤ n) :
    ((k:ℂ)+1) * legInt_J k n * ((n-(k+1)).factorial : ℂ) = ((n+(k+1)).factorial : ℂ) := by
  induction k with
  | zero =>
    rw [legInt_J_zero]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n-1, by omega⟩
    simp only [Nat.add_sub_cancel, show n'+1+(0+1) = n'+1+1 by ring, Nat.factorial_succ]
    push_cast; ring
  | succ k ih =>
    have ih := ih (by omega)
    have e1 : n - (k+1) = (n-(k+1+1)) + 1 := by omega
    rw [e1, Nat.factorial_succ] at ih
    have hc : ((n-(k+1+1)+1 : ℕ) : ℂ) = (n:ℂ) - (k+1) := by
      rw [Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring
    push_cast at ih hc
    rw [show n+(k+1+1) = (n+(k+1))+1 by ring, Nat.factorial_succ]
    push_cast
    rw [← ih]
    have hs := legInt_J_succ k n
    rw [show (k:ℂ)+1+1 = k+2 by ring, hs]
    rw [hc] at *
    ring

/-- `(1-x²)^r` is integrable on `[-1,1]` for `r = -1/2` or `r ≥ 0`. -/
theorem legInt_intervalIntegrable_rpow {r : ℝ} (hr : r = -1/2 ∨ 0 ≤ r) :
    IntervalIntegrable (fun x : ℝ => (1-x^2)^r) volume (-1) 1 := by
  rcases hr with rfl | hr
  · have hd : ∀ x ∈ Ioo (min (-1:ℝ) 1) (max (-1) 1), HasDerivAt Real.arcsin ((1-x^2)^(-1/2:ℝ)) x := by
      intro x hx
      simp only [min_eq_left (by norm_num : (-1:ℝ) ≤ 1), max_eq_right (by norm_num : (-1:ℝ) ≤ 1)] at hx
      have h := Real.hasDerivAt_arcsin (by linarith [hx.1] : x ≠ -1) (by linarith [hx.2] : x ≠ 1)
      have h0 : (0:ℝ) ≤ 1 - x^2 := by nlinarith [hx.1, hx.2]
      convert h using 1
      rw [show (-1/2:ℝ) = -(1/2) by ring, Real.rpow_neg h0, Real.sqrt_eq_rpow, one_div, one_div]
    refine intervalIntegral.intervalIntegrable_deriv_of_nonneg Real.continuous_arcsin.continuousOn hd ?_
    intro x hx
    simp only [min_eq_left (by norm_num : (-1:ℝ) ≤ 1), max_eq_right (by norm_num : (-1:ℝ) ≤ 1)] at hx
    exact Real.rpow_nonneg (by nlinarith [hx.1, hx.2]) _
  · exact ((continuous_const.sub (continuous_pow 2)).rpow_const (fun _ => Or.inr hr)
      ).intervalIntegrable _ _

/-- Green's identity in the order: `∫ (1-x²)^{(l+m)/2-1} P_n^{(l)} P_n^{(m)} = 0` for `l ≠ m`. -/
theorem legInt_offdiag (n l m : ℕ) (hlm : l ≠ m) (hpos : 0 < l+m) :
    ∫ x : ℝ in (-1:ℝ)..1, (((1-x^2)^(((l+m:ℕ):ℝ)/2-1) : ℝ) : ℂ) *
      (legInt_D n l x * legInt_D n m x) = 0 := by
  set a : ℝ := ((l+m:ℕ):ℝ)/2 with ha_def
  have ha : 0 < a := by
    rw [ha_def]; have : (0:ℝ) < ((l+m:ℕ):ℝ) := by exact_mod_cast hpos
    positivity
  set B : ℝ → ℂ := fun x => (1-(x:ℂ)^2)*(legInt_D n l x * legInt_D n (m+1) x -
      legInt_D n m x * legInt_D n (l+1) x) + ((l:ℂ)-m)*x*legInt_D n l x*legInt_D n m x with hB
  set Φ : ℝ → ℂ := fun x => (((1-x^2)^a : ℝ) : ℂ) * B x with hΦ
  set f' : ℝ → ℂ := fun x => ((m:ℂ)^2-l^2) * ((((1-x^2)^(a-1) : ℝ) : ℂ) *
      (legInt_D n l x * legInt_D n m x)) with hf'
  have hderiv : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt Φ (f' x) x := by
    intro x hx
    have hpos' : (0:ℝ) < 1 - x^2 := by nlinarith [hx.1, hx.2]
    have hq : HasDerivAt (fun x : ℝ => 1 - x^2) (-(2*x)) x := by
      simpa using ((hasDerivAt_id x).pow 2).const_sub 1
    have hR := (hq.rpow_const (p := a) (Or.inl hpos'.ne')).ofReal_comp
    have hx' := (hasDerivAt_id x).ofReal_comp
    have h1 := legInt_hasDerivAt_one_sub_sq x
    have pl := legInt_hasDerivAt_D_real n l x
    have pl1 := legInt_hasDerivAt_D_real n (l+1) x
    have pm := legInt_hasDerivAt_D_real n m x
    have pm1 := legInt_hasDerivAt_D_real n (m+1) x
    have hBd := (h1.mul ((pl.mul pm1).sub (pm.mul pl1))).add
      ((((hx'.const_mul ((l:ℂ)-m))).mul pl).mul pm)
    refine (hR.mul hBd).congr_deriv ?_
    have hsplit : (1-x^2)^a = (1-x^2)^(a-1) * (1-x^2) := by
      rw [Real.rpow_sub_one hpos'.ne']; field_simp
    have odl := legInt_ode n l x
    have odm := legInt_ode n m x
    simp only [hf', Pi.mul_apply, Pi.sub_apply, Pi.add_apply, id, ofReal_one]
    rw [hsplit]
    have hac : ((a:ℝ):ℂ) = ((l:ℂ)+m)/2 := by rw [ha_def]; push_cast; ring
    push_cast
    rw [hac]
    rw [show l+1+1 = l+2 by ring, show m+1+1 = m+2 by ring]
    set T : ℂ := (((1-x^2)^(a-1) : ℝ) : ℂ)
    linear_combination T*(1-(x:ℂ)^2)*(legInt_D n l x * odm - legInt_D n m x * odl)
  have hcΦ : Continuous Φ := by
    have hr : Continuous fun x : ℝ => (1-x^2)^a :=
      (continuous_const.sub (continuous_pow 2)).rpow_const (fun _ => Or.inr ha.le)
    have := legInt_cont_D n l; have := legInt_cont_D n m
    have := legInt_cont_D n (l+1); have := legInt_cont_D n (m+1)
    simp only [hΦ, hB]
    fun_prop
  have hT : IntervalIntegrable (fun x : ℝ => (((1-x^2)^(a-1) : ℝ) : ℂ)) volume (-1) 1 := by
    have hr : a - 1 = -1/2 ∨ 0 ≤ a - 1 := by
      rcases Nat.lt_or_ge (l+m) 2 with h | h
      · left; rw [ha_def, show l+m = 1 by omega]; norm_num
      · right; rw [ha_def]; have : (2:ℝ) ≤ ((l+m:ℕ):ℝ) := by exact_mod_cast h
        linarith
    have h := legInt_intervalIntegrable_rpow hr
    exact ⟨h.1.ofReal, h.2.ofReal⟩
  have hint : IntervalIntegrable f' volume (-1) 1 := by
    have := legInt_cont_D n l; have := legInt_cont_D n m
    exact (hT.mul_continuousOn (by fun_prop : Continuous fun x : ℝ =>
      legInt_D n l x * legInt_D n m x).continuousOn).const_mul _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
    hcΦ.continuousOn hderiv hint
  have h0 : Φ 1 = 0 ∧ Φ (-1) = 0 := by
    simp only [hΦ]; norm_num [Real.zero_rpow ha.ne']
  rw [h0.1, h0.2, sub_zero, hf', intervalIntegral.integral_const_mul] at h
  have hne : ((m:ℂ)^2-l^2) ≠ 0 := by
    intro he
    have : ((m:ℝ)^2 - l^2) = 0 := by exact_mod_cast he
    have : (m:ℝ) = l := by nlinarith [(m.cast_nonneg : (0:ℝ) ≤ m), (l.cast_nonneg : (0:ℝ) ≤ l)]
    exact hlm (by exact_mod_cast this.symm)
  exact (mul_eq_zero.mp h).resolve_left hne

/-- `𝖯^l_n 𝖯^m_n/(1-x²) = (-1)^{l+m} (1-x²)^{(l+m)/2-1} P_n^{(l)} P_n^{(m)}` on `(-1,1)`. -/
theorem legInt_ferrers_div_mul (n l m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    1/(1-x^2:ℂ)*ferrersP n l x*ferrersP n m x = (-1)^(l+m) *
      ((((1-x^2)^(((l+m:ℕ):ℝ)/2-1)) : ℝ) : ℂ) * (legInt_D n l x * legInt_D n m x) := by
  have hpos : (0:ℝ) < 1 - x^2 := by nlinarith [hx.1, hx.2]
  rw [legInt_ferrersP_nat_nat n l hx, legInt_ferrersP_nat_nat n m hx]
  have hr : (1-x^2)^((l:ℝ)/2) * (1-x^2)^((m:ℝ)/2) =
      (1-x^2)^(((l+m:ℕ):ℝ)/2-1) * (1-x^2) := by
    rw [← Real.rpow_add hpos, Real.rpow_sub_one hpos.ne', div_mul_cancel₀ _ hpos.ne']
    push_cast; ring_nf
  have hr' := congrArg (fun r : ℝ => (r:ℂ)) hr
  push_cast at hr'
  have hne : (1-(x:ℂ)^2) ≠ 0 := by
    rw [show (1-(x:ℂ)^2) = ((1-x^2:ℝ):ℂ) by push_cast; ring]; exact_mod_cast hpos.ne'
  push_cast
  generalize ((((1-x^2)^(((l:ℝ)+m)/2-1)) : ℝ) : ℂ) = T at hr' ⊢
  generalize ((((1-x^2)^((l:ℝ)/2)) : ℝ) : ℂ) = A at hr' ⊢
  generalize ((((1-x^2)^((m:ℝ)/2)) : ℝ) : ℂ) = B at hr' ⊢
  field_simp
  rw [pow_add]
  linear_combination ((-1:ℂ)^l*(-1)^m*legInt_D n l x * legInt_D n m x) * hr'

/-- Off-diagonal orthogonality of `𝖯^l_n` and `𝖯^m_n` with weight `1/(1-x²)`. -/
theorem legInt_ferrers_offdiag (n l m : ℕ) (hlm : l ≠ m) (hpos : 0 < l+m) :
    ∫ x : ℝ in -1..1, 1/(1-x^2:ℂ)*ferrersP n l x*ferrersP n m x = 0 := by
  have hI : (∫ x : ℝ in -1..1, 1/(1-x^2:ℂ)*ferrersP n l x*ferrersP n m x) =
      (-1)^(l+m) * ∫ x : ℝ in (-1:ℝ)..1, (((1-x^2)^(((l+m:ℕ):ℝ)/2-1) : ℝ) : ℂ) *
        (legInt_D n l x * legInt_D n m x) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    have : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by simp [ae_iff]
    filter_upwards [this] with t ht htm
    rw [uIoc_of_le (by norm_num)] at htm
    rw [legInt_ferrers_div_mul n l m ⟨htm.1, lt_of_le_of_ne htm.2 ht⟩, mul_assoc]
  rw [hI, legInt_offdiag n l m hlm hpos, mul_zero]

/-- The diagonal: `∫ (𝖯^{k+1}_n)²/(1-x²) = ∫ (1-x²)^k (P_n^{(k+1)})²`. -/
theorem legInt_ferrers_diag (n k : ℕ) :
    ∫ x : ℝ in -1..1, 1/(1-x^2:ℂ)*ferrersP n (k+1:ℕ) x*ferrersP n (k+1:ℕ) x = legInt_J k n := by
  refine intervalIntegral.integral_congr_ae ?_
  have : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by simp [ae_iff]
  filter_upwards [this] with t ht htm
  rw [uIoc_of_le (by norm_num)] at htm
  have hx : t ∈ Ioo (-1:ℝ) 1 := ⟨htm.1, lt_of_le_of_ne htm.2 ht⟩
  have hpos : (0:ℝ) ≤ 1 - t^2 := by nlinarith [hx.1, hx.2]
  rw [legInt_ferrers_div_mul n (k+1) (k+1) hx,
    show (((k+1+(k+1):ℕ):ℝ)/2-1) = ((k:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast,
    show k+1+(k+1) = 2*(k+1) by ring, pow_mul]
  push_cast; ring

end DLMF.Legendre
end
