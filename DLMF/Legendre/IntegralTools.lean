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
# Tools for Legendre integrals

Helper results (prefix `legInt_`) for `DLMF.Legendre.Integrals` and
`DLMF.Legendre.IntegralRepresentations`:

* the `m`-times differentiated Legendre equation for `P_n^{(m)}` and the moment recursion
  `∫ (1-x²)^{m+1} (P_l^{(m+1)})(P_n^{(m+1)}) = (n-m)(n+m+1) ∫ (1-x²)^m P_l^{(m)} P_n^{(m)}`,
  which yields the orthogonality of Ferrers functions of integer degree and order (DLMF 14.17.6);
* Green's identity in the order and the moment recursion behind the weight `1/(1-x²)`
  orthogonality (DLMF 14.17.8);
* the contiguous relation `𝐅(a,b;c) = c 𝐅(a,b;c+1) + a b z 𝐅(a+1,b+1;c+2)` on the cut plane and
  the resulting primitive `d/dw [w^{k+1} 𝐅(a,b;k+2;w)] = w^k 𝐅(a,b;k+1;w)`, which identifies
  iterated integrals of `P_ν` from the endpoint `1` with Ferrers and associated Legendre functions
  of negative integer order (DLMF 14.6.6, 14.6.7);
* analyticity of `z ↦ ∫_0^1 w(s) F(zs) ds` on the cut plane and the resulting cut-plane form of
  the fractional integral DLMF 15.6.8 with `d = 1`, used for DLMF 14.12.5;
* elementary facts on complex powers of positive reals and on the principal slit plane;
* the primitives `g_k = (z²-1)^{k/2} Q^{-k}_ν` with `g_{k+1}' = g_k` and `g_{k+1} → 0` at infinity,
  giving the iterated tail integrals of DLMF 14.6.8 on `(1,∞)` and on the principal sheet;
* integration-by-parts recurrences in the order for the Laplace-type moments
  `∫_0^π w^ν cos(mθ)` and `∫_0^π w^p sin^{2q}θ`, `w = x + √(x²-1) cos θ` (DLMF 14.12.7, 14.12.8);
* Heine's integral `∫_0^∞ dt/(x+√(x²-1) cosh t)^{n+1}` (DLMF 14.12.14) via an explicit primitive
  and a degree recurrence;
* recurrences in degree and order for `∫_0^u (x-√(x²-1) cosh t)^n cosh(mt)`, `u = arcoth x`
  (DLMF 14.12.9), and for `∫_{-1}^1 (1-t²)^n (x-t)^{-p}` (DLMF 14.12.11).
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

/-! ### A fractional integral on the cut plane -/

/-- `z s` lies in the cut plane for `z` in the cut plane and `s ∈ [0,1]`. -/
theorem legInt_mul_mem_cutPlane {z : ℂ} (hz : z ∈ cutPlane) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    z * s ∈ cutPlane := by
  have h := starConvex_zero_cutPlane hz (by linarith [hs.2] : (0:ℝ) ≤ 1 - s) hs.1 (by ring)
  simpa [Complex.real_smul, mul_comm] using h

/-- `z ↦ ∫_0^1 w(s) F(z s) ds` is analytic on the cut plane when `F` is and `w` is integrable. -/
theorem legInt_analyticOnNhd_integral {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F cutPlane) {w : ℝ → ℂ}
    (hw : IntervalIntegrable w volume 0 1) :
    AnalyticOnNhd ℂ (fun z => ∫ s : ℝ in (0:ℝ)..1, w s * F (z * s)) cutPlane := by
  refine DifferentiableOn.analyticOnNhd (fun z0 hz0 => ?_) isOpen_cutPlane
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_cutPlane z0 hz0
  set ε := r/2 with hε
  have hεpos : 0 < ε := by positivity
  have hcb : Metric.closedBall z0 ε ⊆ cutPlane := fun z hz =>
    hball (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)))
  set K := (fun p : ℂ × ℝ => p.1 * p.2) '' (Metric.closedBall z0 ε ×ˢ Icc (0:ℝ) 1)
  have hK : IsCompact K := ((isCompact_closedBall z0 ε).prod isCompact_Icc).image (by fun_prop)
  have hKsub : K ⊆ cutPlane := by
    rintro _ ⟨⟨z, s⟩, ⟨hz, hs⟩, rfl⟩
    exact legInt_mul_mem_cutPlane (hcb hz) hs
  have hdF : ContinuousOn (deriv F) cutPlane := (hF.deriv).continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hdF.mono hKsub)
  have hIcc : ∀ s ∈ uIoc (0:ℝ) 1, s ∈ Icc (0:ℝ) 1 := fun s hs => by
    rw [uIoc_of_le zero_le_one] at hs; exact ⟨hs.1.le, hs.2⟩
  have hcont : ∀ z ∈ cutPlane, ContinuousOn (fun s : ℝ => F (z * s)) (uIcc 0 1) := by
    intro z hz s hs
    rw [uIcc_of_le zero_le_one] at hs
    exact (ContinuousAt.comp (g := F) (f := fun s : ℝ => z * (s:ℂ))
      (hF _ (legInt_mul_mem_cutPlane hz hs)).continuousAt (by fun_prop)).continuousWithinAt
  have hcont' : ContinuousOn (fun s : ℝ => deriv F (z0 * s) * s) (uIcc 0 1) := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    exact ((ContinuousAt.comp (g := deriv F) (f := fun s : ℝ => z0 * (s:ℂ))
      (hF.deriv _ (legInt_mul_mem_cutPlane hz0 hs)).continuousAt (by fun_prop)).mul
      (continuous_ofReal.continuousAt)).continuousWithinAt
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z s => w s * F (z * s)) (F' := fun z s => w s * (deriv F (z * s) * s))
    (x₀ := z0) (bound := fun s => ‖w s‖ * C) (μ := volume) (a := 0) (b := 1) (Metric.ball_mem_nhds z0 hεpos)
    (by
      filter_upwards [isOpen_cutPlane.mem_nhds hz0] with z hz
      exact (hw.mul_continuousOn (hcont z hz)).def'.aestronglyMeasurable)
    (hw.mul_continuousOn (hcont z0 hz0))
    ((hw.mul_continuousOn hcont').def'.aestronglyMeasurable)
    (Eventually.of_forall fun s hs z hz => by
      have hs' := hIcc s hs
      have hzK : z * s ∈ K := ⟨⟨z, s⟩, ⟨Metric.ball_subset_closedBall hz, hs'⟩, rfl⟩
      rw [norm_mul, norm_mul]
      gcongr
      calc ‖deriv F (z * s)‖ * ‖(s:ℂ)‖ ≤ C * 1 := by
            gcongr
            · exact le_trans (norm_nonneg _) (hC _ hzK)
            · exact hC _ hzK
            · rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hs'.1]; exact hs'.2
        _ = C := mul_one C)
    (hw.norm.mul_const C)
    (Eventually.of_forall fun s hs z hz => by
      have hs' := hIcc s hs
      have hzc : z * s ∈ cutPlane := legInt_mul_mem_cutPlane (hcb (Metric.ball_subset_closedBall hz)) hs'
      have hd := ((hF _ hzc).differentiableAt.hasDerivAt).comp z (hasDerivAt_mul_const (s:ℂ))
      exact hd.const_mul (w s))
  exact h.2.differentiableAt

/-- DLMF 15.6.8 with `d = 1` on the cut plane:
`Γ(μ) 𝐅(a,b;1+μ;z) = ∫_0^1 (1-s)^{μ-1} 𝐅(a,b;1;zs) ds`. -/
theorem legInt_fractional_cutPlane (a b : ℂ) {μ : ℂ} (hμ : 0 < μ.re) {z : ℂ} (hz : z ∈ cutPlane) :
    Gamma μ * regularizedGaussHG a b (1+μ) z =
      ∫ s : ℝ in (0:ℝ)..1, (1-(s:ℂ))^(μ-1) * regularizedGaussHG a b 1 (z * s) := by
  have hw : IntervalIntegrable (fun s : ℝ => (1-(s:ℂ))^(μ-1)) volume 0 1 := by
    simpa using betaIntegral_convergent (u := 1) (by norm_num) hμ
  refine eqOn_cutPlane_of_eqOn_disk (f := fun z => Gamma μ * regularizedGaussHG a b (1+μ) z)
    (fun z hz => analyticAt_const.mul (analyticOnNhd_regularizedGaussHG a b _ z hz))
    (legInt_analyticOnNhd_integral (analyticOnNhd_regularizedGaussHG a b 1) hw) (fun z hz => ?_) hz
  have hfr := fractional_integral (a := a) (b := b) (c := 1+μ) (d := 1) (by norm_num)
    (by simpa using hμ) hz
  rw [show 1+μ-1 = μ by ring] at hfr
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz, hfr, ← mul_assoc,
    mul_one_div_cancel (Gamma_ne_zero_of_re_pos hμ), one_mul]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le zero_le_one] at hs
  have hzs : ‖z*s‖ < 1 := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc ‖z‖*s ≤ ‖z‖*1 := by gcongr; exact hs.2
      _ < 1 := by rw [mul_one]; exact hz
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hzs, sub_self, cpow_zero, mul_one, mul_comm]

/-- Complex powers of a positive real as exponentials of the real logarithm. -/
theorem legInt_cpow_ofReal {r : ℝ} (hr : 0 < r) (c : ℂ) :
    ((r:ℝ):ℂ)^c = exp (Real.log r * c) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.2 hr.ne'), ofReal_log hr.le]

/-- Order-derivative relation `(1-z²) 𝑸' + μ z 𝑸^μ_ν = (ν+μ+1) (z²-1)^{1/2} 𝑸^{μ+1}_ν`. -/
theorem legInt_olverQ_order_deriv (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (1-z^2)*deriv (olverQ ν μ) z + μ*z*olverQ ν μ z =
      (ν+μ+1)*legendreBranchPower 1 z*olverQ ν (μ+1) z := by
  have h7 := olverQ_recurrence_7 ν μ hz
  have h4 := olverQ_recurrence_4 ν μ hz
  linear_combination h4 + (ν+μ+1)*h7

/-- `g_k(z) = (z²-1)^{k/2} Q^{-k}_ν(z)`. -/
noncomputable def legInt_g (ν : ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  legendreBranchPower k z * associatedQ ν (-k) z

/-- `g_0 = Q_ν`. -/
theorem legInt_g_zero (ν z : ℂ) : legInt_g ν 0 z = associatedQ ν 0 z := by
  simp [legInt_g, legendreBranchPower]

/-- `g_{k+1}' = g_k` on the principal sheet, for `ν ≠ k`. -/
theorem legInt_hasDerivAt_g (ν : ℂ) (k : ℕ) (hk : ν ≠ k) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    HasDerivAt (legInt_g ν (k+1)) (legInt_g ν k z) z := by
  set C : ℂ := exp (-((k+1:ℕ):ℂ)*π*I)*Gamma (ν+-((k+1:ℕ):ℂ)+1)
  have hQ := ((olverQ_analytic ν (-((k+1:ℕ):ℂ)) z hz).differentiableAt.hasDerivAt).const_mul C
  have h := (hasDerivAt_legendreBranchPower ((k+1:ℕ):ℂ) hz).mul hQ
  have e : legInt_g ν (k+1) = fun w => legendreBranchPower ((k+1:ℕ):ℂ) w *
      (C * olverQ ν (-((k+1:ℕ):ℂ)) w) := by
    funext w; simp only [legInt_g, associatedQ, C]
  rw [e]
  refine h.congr_deriv ?_
  have L := legInt_olverQ_order_deriv ν (-((k+1:ℕ):ℂ)) hz
  rw [show -((k+1:ℕ):ℂ)+1 = -(k:ℂ) by push_cast; ring] at L
  have hz2 := legendre_sq_sub_one_ne_zero hz
  have hb : legendreBranchPower ((k+1:ℕ):ℂ) z = legendreBranchPower k z * legendreBranchPower 1 z := by
    rw [legendreBranchPower_mul]; push_cast; ring_nf
  have hb2 : legendreBranchPower 1 z * legendreBranchPower 1 z = z^2-1 := by
    rw [legendreBranchPower_mul, show (1:ℂ)+1 = 2 by norm_num, legendreBranchPower_two hz]
  have hνk : ν - k ≠ 0 := sub_ne_zero.mpr hk
  have hG : Gamma (ν + -(k:ℂ) + 1) = (ν-k) * Gamma (ν-(k+1)+1) := by
    rw [show ν-(k+1)+1 = ν-k by ring, show ν + -(k:ℂ) + 1 = (ν-k)+1 by ring, Gamma_add_one _ hνk]
  have hE : exp (-((k+1:ℕ):ℂ)*π*I) = -exp (-(k:ℂ)*π*I) := by
    rw [show -((k+1:ℕ):ℂ)*π*I = -(k:ℂ)*π*I + (-(π*I)) by push_cast; ring, exp_add, exp_neg,
      exp_pi_mul_I]; ring
  simp only [legInt_g, associatedQ, C, hE, hb]
  push_cast at hG L ⊢
  have hD : deriv (olverQ ν (-((k:ℂ)+1))) z = -((ν-k)*legendreBranchPower 1 z*olverQ ν (-k) z
      + ((k:ℂ)+1)*z*olverQ ν (-((k:ℂ)+1)) z)/(z^2-1) := by
    field_simp; linear_combination -L
  rw [hG, hD]
  field_simp
  rw [show ν + -((k:ℂ)+1) + 1 = ν - (k+1) + 1 by ring]
  linear_combination (legendreBranchPower k z * (ν-k) * olverQ ν (-k) z * Gamma (ν-(k+1)+1)) * hb2

/-- Continuity of `g_k` on the principal sheet. -/
theorem legInt_continuousAt_g (ν : ℂ) (k : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    ContinuousAt (legInt_g ν k) z := by
  have h1 := (hasDerivAt_legendreBranchPower (k:ℂ) hz).continuousAt
  have h2 := ((olverQ_analytic ν (-(k:ℂ)) z hz).continuousAt).const_mul
    (exp (-(k:ℂ)*π*I)*Gamma (ν+-(k:ℂ)+1))
  have e : legInt_g ν k = fun w => legendreBranchPower (k:ℂ) w *
      (exp (-(k:ℂ)*π*I)*Gamma (ν+-(k:ℂ)+1) * olverQ ν (-(k:ℂ)) w) := by
    funext w; simp only [legInt_g, associatedQ]
  rw [e]; exact h1.mul h2

/-- `g_{k+1}(R) → 0` as `R → ∞` when `k < Re ν`. -/
theorem legInt_tendsto_g (ν : ℂ) (k : ℕ) (hk : (k:ℝ) < ν.re) :
    Tendsto (fun R : ℝ => legInt_g ν (k+1) R) atTop (𝓝 0) := by
  set w : ℂ := ν + -((k+1:ℕ):ℂ) + 1 with hw
  have hwre : 0 < w.re := by rw [hw]; simp; linarith
  set K : ℂ := exp (-((k+1:ℕ):ℂ)*π*I)*Gamma w*(Real.sqrt π/(2^(ν+1)))
  set A := (ν+-((k+1:ℕ):ℂ)+2)/2
  set B := (ν+-((k+1:ℕ):ℂ)+1)/2
  have e : ∀ R : ℝ, legInt_g ν (k+1) R =
      K * ((R:ℂ)^w)⁻¹ * regularizedGaussHG A B (ν+3/2) (1/(R:ℂ)^2) := by
    intro R
    have hb : legendreBranchPower ((k+1:ℕ):ℂ) R * legendreBranchPower (-((k+1:ℕ):ℂ)) R = 1 := by
      rw [legendreBranchPower_mul, add_neg_cancel]; simp [legendreBranchPower]
    simp only [legInt_g, associatedQ, olverQ, K, A, B, hw]
    rw [div_eq_mul_inv (Real.sqrt π * legendreBranchPower _ _), mul_inv]
    linear_combination (exp (-((k+1:ℕ):ℂ)*π*I)*Gamma (ν+-((k+1:ℕ):ℂ)+1)*Real.sqrt π *
      (2^(ν+1))⁻¹ * ((R:ℂ)^(ν+-((k+1:ℕ):ℂ)+1))⁻¹ *
      regularizedGaussHG ((ν+-((k+1:ℕ):ℂ)+2)/2) ((ν+-((k+1:ℕ):ℂ)+1)/2) (ν+3/2) (1/(R:ℂ)^2)) * hb
  simp_rw [e]
  have h1 : Tendsto (fun R : ℝ => ((R:ℂ)^w)⁻¹) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := (tendsto_rpow_atTop hwre).inv_tendsto_atTop
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    rw [norm_inv, norm_cpow_eq_rpow_re_of_pos hR]; rfl
  have h2 : Tendsto (fun R : ℝ => regularizedGaussHG A B (ν+3/2) (1/(R:ℂ)^2)) atTop
      (𝓝 (regularizedGaussHG A B (ν+3/2) 0)) := by
    have hc := (analyticAt_regularizedGaussHG A B (ν+3/2) zero_mem_cutPlane).continuousAt
    have ht : Tendsto (fun R : ℝ => 1/(R:ℂ)^2) atTop (𝓝 0) := by
      have := ((continuous_ofReal.tendsto 0).comp
        (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (two_ne_zero (α := ℕ)))))
      simp only [ofReal_zero] at this
      refine this.congr fun R => ?_
      simp [Function.comp]
    exact hc.tendsto.comp ht
  simpa using (tendsto_const_nhds (x := K)).mul h1 |>.mul h2

/-- Real points `t > 1` give `t - 1` in the slit plane. -/
theorem legInt_one_lt_mem {t : ℝ} (ht : 1 < t) : (t:ℂ)-1 ∈ slitPlane :=
  Or.inl (by simp; linarith)

/-- `∫_x^∞ g_j = -g_{j+1}(x)` for `x > 1` and `j < Re ν`. -/
theorem legInt_hasIntegralAtTop_g (ν : ℂ) (j : ℕ) (hj : (j:ℝ) < ν.re) {x : ℝ} (hx : 1 < x) :
    HasIntegralAtTop (fun t : ℝ => legInt_g ν j t) x (-legInt_g ν (j+1) x) := by
  have hne : ν ≠ j := fun h => by rw [h] at hj; simp at hj
  have hFTC : ∀ R, x ≤ R → ∫ t in x..R, legInt_g ν j t = legInt_g ν (j+1) R - legInt_g ν (j+1) x := by
    intro R hR
    have hsub : ∀ t ∈ uIcc x R, 1 < t := fun t ht => by
      rw [uIcc_of_le hR] at ht; linarith [ht.1]
    have hco : ContinuousOn (fun t : ℝ => legInt_g ν j t) (uIcc x R) := fun t ht =>
      ((legInt_continuousAt_g ν j (legInt_one_lt_mem (hsub t ht))).comp
        continuous_ofReal.continuousAt).continuousWithinAt
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => legInt_g ν (j+1) t)
      (fun t ht => (legInt_hasDerivAt_g ν j hne (legInt_one_lt_mem (hsub t ht))).comp_ofReal)
      (hco.intervalIntegrable)
  have h := (legInt_tendsto_g ν j hj).sub_const (legInt_g ν (j+1) x)
  rw [zero_sub] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop x] with R hR
  exact (hFTC R hR).symm

/-- Iterated tails of `Q_ν`. -/
theorem legInt_iterate_Q (ν : ℂ) (k : ℕ) (hk : (k:ℝ)-1 < ν.re) {x : ℝ} (hx : 1 < x) :
    ((fun f : ℝ → ℂ => fun x => improperAtTop f x)^[k]) (fun x : ℝ => associatedQ ν 0 x) x =
      (-1)^k * legInt_g ν k x := by
  induction k generalizing x with
  | zero => simp [legInt_g_zero]
  | succ k ih =>
    have hk' : (k:ℝ) < ν.re := by push_cast at hk; linarith
    rw [Function.iterate_succ_apply']
    show improperAtTop _ x = _
    have h := (legInt_hasIntegralAtTop_g ν k hk' hx).const_mul ((-1:ℂ)^k)
    have h' : HasIntegralAtTop (((fun f : ℝ → ℂ => fun x => improperAtTop f x)^[k])
        (fun x : ℝ => associatedQ ν 0 x)) x ((-1)^k * -legInt_g ν (k+1) x) := by
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop x] with R hR
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hR] at ht
      exact (ih (by linarith) (by linarith [ht.1])).symm
    rw [improperAtTop, h'.limUnder_eq]
    ring


/-- Points of the segment from `z` to `2` stay on the principal sheet. -/
theorem legInt_seg_two_mem {z : ℂ} (hz : z-1 ∈ slitPlane) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (z + t*(2-z)) - 1 ∈ slitPlane := by
  have h := starConvex_one_slitPlane hz ht.1 (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) (by ring)
  convert h using 1
  simp only [Complex.real_smul, mul_one, ofReal_sub, ofReal_one]
  ring

/-- Iterated segment-plus-tail integrals of `Q_ν`. -/
theorem legInt_iterate_Qc (ν : ℂ) (k : ℕ) (hk : (k:ℝ)-1 < ν.re) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    ((fun f : ℂ → ℂ => fun z => segmentIntegral f z 2+improperAtTop (fun t : ℝ => f t) 2)^[k])
      (associatedQ ν 0) z = (-1)^k * legInt_g ν k z := by
  induction k generalizing z with
  | zero => simp [legInt_g_zero]
  | succ k ih =>
    have hk' : (k:ℝ) < ν.re := by push_cast at hk; linarith
    have hne : ν ≠ k := fun h => by rw [h] at hk'; simp at hk'
    have ih' := fun {w : ℂ} (hw : w-1 ∈ slitPlane) => ih (by linarith) (z := w) hw
    rw [Function.iterate_succ_apply']
    show segmentIntegral _ z 2 + improperAtTop _ 2 = _
    -- the tail
    have htail : improperAtTop (fun t : ℝ => ((fun f : ℂ → ℂ => fun z =>
        segmentIntegral f z 2+improperAtTop (fun t : ℝ => f t) 2)^[k]) (associatedQ ν 0) t) 2 =
        (-1)^k * -legInt_g ν (k+1) 2 := by
      have h := (legInt_hasIntegralAtTop_g ν k hk' (by norm_num : (1:ℝ) < 2)).const_mul ((-1:ℂ)^k)
      refine (h.congr' ?_).limUnder_eq
      · filter_upwards [eventually_ge_atTop 2] with R hR
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hR] at ht
        exact (ih' (legInt_one_lt_mem (by linarith [ht.1]))).symm
    -- the segment
    have hseg : segmentIntegral (((fun f : ℂ → ℂ => fun z =>
        segmentIntegral f z 2+improperAtTop (fun t : ℝ => f t) 2)^[k]) (associatedQ ν 0)) z 2 =
        (-1)^k * (legInt_g ν (k+1) 2 - legInt_g ν (k+1) z) := by
      rw [segmentIntegral]
      have hc : (∫ t : ℝ in (0:ℝ)..1, ((fun f : ℂ → ℂ => fun z =>
          segmentIntegral f z 2+improperAtTop (fun t : ℝ => f t) 2)^[k]) (associatedQ ν 0)
            (z + t*(2-z))) = ∫ t : ℝ in (0:ℝ)..1, (-1)^k * legInt_g ν k (z + t*(2-z)) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le zero_le_one] at ht
        exact ih' (legInt_seg_two_mem hz ht)
      rw [hc, intervalIntegral.integral_const_mul, mul_left_comm]
      congr 1
      rw [← intervalIntegral.integral_const_mul]
      have hd : ∀ t ∈ uIcc (0:ℝ) 1, HasDerivAt (fun t : ℝ => legInt_g ν (k+1) (z + t*(2-z)))
          ((2-z) * legInt_g ν k (z + t*(2-z))) t := by
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        have hl : HasDerivAt (fun t : ℝ => z + (t:ℂ)*(2-z)) (1*(2-z)) t :=
          ((hasDerivAt_id t).ofReal_comp.mul_const (2-z)).const_add z
        rw [one_mul] at hl
        exact ((legInt_hasDerivAt_g ν k hne (legInt_seg_two_mem hz ht)).comp t hl).congr_deriv
          (mul_comm _ _)
      have hco : ContinuousOn (fun t : ℝ => (2-z) * legInt_g ν k (z + t*(2-z))) (uIcc 0 1) :=
        fun t ht => by
          have ht' := ht; rw [uIcc_of_le zero_le_one] at ht'
          refine ContinuousAt.continuousWithinAt (ContinuousAt.mul continuousAt_const ?_)
          exact ContinuousAt.comp (g := legInt_g ν k)
            (legInt_continuousAt_g ν k (legInt_seg_two_mem hz ht')) (by fun_prop)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hco.intervalIntegrable]
      simp only [ofReal_one, one_mul, ofReal_zero, zero_mul, add_zero, add_sub_cancel]
    rw [htail, hseg]
    ring


/-- The Laplace kernel `w(θ) = x + √(x²-1) cos θ`, positive for `x > 1`. -/
theorem legInt_laplace_pos {x : ℝ} (hx : 1 < x) (θ : ℝ) :
    0 < x + Real.sqrt (x^2-1) * Real.cos θ := by
  have hs : Real.sqrt (x^2-1) < x := by
    rw [Real.sqrt_lt' (by linarith)]; linarith
  have hs0 := Real.sqrt_nonneg (x^2-1)
  nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]

/-- Fourier moments of powers of the Laplace kernel. -/
noncomputable def legInt_L (ν : ℂ) (x : ℝ) (m : ℕ) : ℂ :=
  ∫ θ : ℝ in (0:ℝ)..π, (((x + Real.sqrt (x^2-1) * Real.cos θ : ℝ)) : ℂ)^ν * Real.cos (m*θ)

/-- Continuity of the integrand of `legInt_L`. -/
theorem legInt_cont_L (ν : ℂ) {x : ℝ} (hx : 1 < x) (c : ℝ) :
    Continuous fun θ : ℝ => (((x + Real.sqrt (x^2-1) * Real.cos θ : ℝ)) : ℂ)^ν * Real.cos (c*θ) := by
  refine Continuous.mul ?_ (by fun_prop)
  refine continuous_iff_continuousAt.2 fun θ => ?_
  refine ContinuousAt.cpow (by fun_prop) continuousAt_const ( ?_)
  exact ofReal_mem_slitPlane.2 (legInt_laplace_pos hx θ)

/-- The integration-by-parts recurrence
`(ν+m+2) s L_{m+2} + 2(m+1) x L_{m+1} + (m-ν) s L_m = 0`, `s = √(x²-1)`. -/
theorem legInt_L_rec (ν : ℂ) {x : ℝ} (hx : 1 < x) (m : ℕ) :
    (ν+m+2) * Real.sqrt (x^2-1) * legInt_L ν x (m+2) + 2*(m+1)*x*legInt_L ν x (m+1) +
      (m-ν) * Real.sqrt (x^2-1) * legInt_L ν x m = 0 := by
  set s := Real.sqrt (x^2-1)
  set w : ℝ → ℝ := fun θ => x + s * Real.cos θ with hw
  have hwpos : ∀ θ, 0 < w θ := legInt_laplace_pos hx
  -- derivative of `w^{ν+1} sin((m+1)θ)`
  have hd : ∀ θ ∈ uIcc (0:ℝ) π, HasDerivAt (fun θ : ℝ => ((w θ : ℝ):ℂ)^(ν+1) * Real.sin ((m+1)*θ))
      ((ν+1) * ((w θ:ℝ):ℂ)^ν * (-(s * Real.sin θ)) * Real.sin ((m+1)*θ) +
        ((w θ:ℝ):ℂ)^(ν+1) * (((m:ℝ)+1) * Real.cos ((m+1)*θ))) θ := by
    intro θ _
    have h1 : HasDerivAt (fun θ : ℝ => ((w θ:ℝ):ℂ)) (((-(s * Real.sin θ)):ℝ):ℂ) θ := by
      have := ((Real.hasDerivAt_cos θ).const_mul s).const_add x
      simpa [hw] using this.ofReal_comp
    have h2 := (hasStrictDerivAt_cpow_const (c := ν+1)
      (ofReal_mem_slitPlane.2 (hwpos θ))).hasDerivAt.comp θ h1
    have h3 : HasDerivAt (fun θ : ℝ => ((Real.sin ((m+1)*θ) : ℝ):ℂ))
        ((((m:ℝ)+1) * Real.cos ((m+1)*θ) : ℝ):ℂ) θ := by
      have := (Real.hasDerivAt_sin ((m+1)*θ)).comp θ ((hasDerivAt_id θ).const_mul ((m:ℝ)+1))
      simpa [mul_comm] using this.ofReal_comp
    rw [add_sub_cancel_right] at h2
    exact (h2.mul h3).congr_deriv (by simp only [Function.comp_apply]; push_cast; ring)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    refine (Continuous.intervalIntegrable ?_ _ _)
    refine Continuous.add (Continuous.mul (Continuous.mul (Continuous.mul continuous_const ?_)
      (by fun_prop)) (by fun_prop)) (Continuous.mul ?_ (by fun_prop))
    · refine continuous_iff_continuousAt.2 fun θ => ?_
      exact ContinuousAt.cpow (by fun_prop) continuousAt_const ( (ofReal_mem_slitPlane.2 (hwpos θ)))
    · refine continuous_iff_continuousAt.2 fun θ => ?_
      exact ContinuousAt.cpow (by fun_prop) continuousAt_const ( (ofReal_mem_slitPlane.2 (hwpos θ))))
  have hsin0 : Real.sin ((m+1)*π) = 0 := by
    rw [show ((m:ℝ)+1)*π = ((m+1:ℕ):ℝ)*π by push_cast; ring]; exact Real.sin_nat_mul_pi _
  simp only [mul_zero, Real.sin_zero, ofReal_zero, hsin0, mul_zero, sub_zero] at hint
  -- pointwise identity
  have hpt : ∀ θ : ℝ, (ν+1) * ((w θ:ℝ):ℂ)^ν * (-(s * Real.sin θ)) * Real.sin ((m+1)*θ) +
        ((w θ:ℝ):ℂ)^(ν+1) * (((m:ℝ)+1) * Real.cos ((m+1)*θ)) =
      (1/2:ℂ) * ((ν+m+2) * s * (((w θ:ℝ):ℂ)^ν * Real.cos (((m+2:ℕ):ℝ)*θ)) +
        2*(m+1)*x*(((w θ:ℝ):ℂ)^ν * Real.cos (((m+1:ℕ):ℝ)*θ)) +
        (m-ν) * s * (((w θ:ℝ):ℂ)^ν * Real.cos (((m:ℕ):ℝ)*θ))) := by
    intro θ
    have hp : ((w θ:ℝ):ℂ)^(ν+1) = ((w θ:ℝ):ℂ)^ν * (x + s * Real.cos θ) := by
      rw [cpow_add _ _ (ofReal_ne_zero.2 (hwpos θ).ne'), cpow_one]; simp [hw]
    have e1 : Real.cos (((m+2:ℕ):ℝ)*θ) = Real.cos ((m+1)*θ) * Real.cos θ -
        Real.sin ((m+1)*θ) * Real.sin θ := by
      rw [← Real.cos_add]; push_cast; ring_nf
    have e2 : Real.cos (((m:ℕ):ℝ)*θ) = Real.cos ((m+1)*θ) * Real.cos θ +
        Real.sin ((m+1)*θ) * Real.sin θ := by
      rw [← Real.cos_sub]; ring_nf
    rw [hp, e1, e2]; push_cast; ring
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ), intervalIntegral.integral_const_mul] at hint
  have hc := fun k : ℕ => (legInt_cont_L ν hx (k:ℝ)).intervalIntegrable (μ := volume) 0 π
  rw [intervalIntegral.integral_add ((((hc _).const_mul _)).add ((hc _).const_mul _))
    ((hc _).const_mul _), intervalIntegral.integral_add ((hc _).const_mul _) ((hc _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hint
  simp only [legInt_L] at hint ⊢
  push_cast at hint ⊢
  linear_combination 2 * hint

/-- The Heine kernel `W(t) = x + √(x²-1) cosh t`. -/
noncomputable def legInt_W (x t : ℝ) : ℝ := x + Real.sqrt (x^2-1) * Real.cosh t

/-- Positivity of the Heine kernel. -/
theorem legInt_W_pos {x : ℝ} (hx : 1 < x) (t : ℝ) : 0 < legInt_W x t := by
  unfold legInt_W
  have := Real.sqrt_nonneg (x^2-1); have := Real.one_le_cosh t
  nlinarith

/-- Continuity of `1/W^n`. -/
theorem legInt_cont_W_pow {x : ℝ} (hx : 1 < x) (n : ℕ) :
    Continuous fun t => 1 / legInt_W x t ^ n := by
  unfold legInt_W
  exact Continuous.div continuous_const (by fun_prop)
    (fun t => pow_ne_zero _ (legInt_W_pos hx t).ne')

/-- `W(t) → ∞` as `t → ∞`. -/
theorem legInt_W_tendsto {x : ℝ} (hx : 1 < x) : Tendsto (legInt_W x) atTop atTop := by
  have hs : 0 < Real.sqrt (x^2-1) := Real.sqrt_pos.2 (by nlinarith)
  refine tendsto_atTop_mono (fun t => ?_)
    ((Real.tendsto_exp_atTop.const_mul_atTop (by positivity : 0 < Real.sqrt (x^2-1)/2)))
  unfold legInt_W
  rw [Real.cosh_eq]
  have := Real.exp_pos (-t)
  nlinarith

/-- The `n = 0` Heine integral: `∫_0^∞ dt/W = ½ log((x+1)/(x-1))`. -/
theorem legInt_heine_zero {x : ℝ} (hx : 1 < x) :
    Tendsto (fun R => ∫ t in (0:ℝ)..R, 1 / legInt_W x t ^ 1) atTop
      (𝓝 (Real.log ((x+1)/(x-1)) / 2)) := by
  set s := Real.sqrt (x^2-1) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 (by nlinarith)
  have hss : s^2 = x^2-1 := Real.sq_sqrt (by nlinarith)
  set F : ℝ → ℝ := fun t => Real.log (s * Real.exp t + x - 1) - Real.log (s * Real.exp t + x + 1)
  have hA : ∀ t, 0 < s * Real.exp t + x - 1 := fun t => by
    have := Real.exp_pos t; nlinarith
  have hB : ∀ t, 0 < s * Real.exp t + x + 1 := fun t => by linarith [hA t]
  have hd : ∀ t, HasDerivAt F (1 / legInt_W x t ^ 1) t := by
    intro t
    have he := Real.hasDerivAt_exp t
    have h1 := ((((he.const_mul s).add_const x).sub_const 1).log (hA t).ne')
    have h2 := ((((he.const_mul s).add_const x).add_const 1).log (hB t).ne')
    refine (h1.sub h2).congr_deriv ?_
    have hW := legInt_W_pos hx t
    have hAt := hA t; have hBt := hB t
    unfold legInt_W at hW ⊢
    rw [Real.cosh_eq] at hW ⊢
    have hee : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    field_simp
    nlinarith [hee, hss]
  have hint : ∀ R, ∫ t in (0:ℝ)..R, 1 / legInt_W x t ^ 1 = F R - F 0 := fun R =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((legInt_cont_W_pow hx 1).intervalIntegrable _ _)
  simp_rw [hint]
  have hF0 : -F 0 = Real.log ((x+1)/(x-1)) / 2 := by
    simp only [F, Real.exp_zero, mul_one]
    have hq : ((s+x+1)/(s+x-1))^2 = (x+1)/(x-1) := by
      have h1 : s + x - 1 ≠ 0 := by linarith [hA 0, Real.exp_zero]
      have h2 : x - 1 ≠ 0 := by linarith
      field_simp
      nlinarith [hss]
    rw [← hq, Real.log_pow, Real.log_div (by linarith [hB 0, Real.exp_zero])
      (by linarith [hA 0, Real.exp_zero])]
    push_cast; ring
  rw [← hF0, show -F 0 = 0 - F 0 by ring]
  refine Tendsto.sub_const ?_ _
  have hBt : Tendsto (fun R => s * Real.exp R + x + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _
      (Real.tendsto_exp_atTop.const_mul_atTop hs))
  have h2 : Tendsto (fun R => 1 - 2 / (s * Real.exp R + x + 1)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub (hBt.const_div_atTop (2:ℝ))
  have h3 := ((Real.continuousAt_log one_ne_zero).tendsto).comp h2
  rw [Real.log_one] at h3
  refine h3.congr fun R => ?_
  simp only [Function.comp_apply, F]
  rw [← Real.log_div (hA R).ne' (hB R).ne']
  congr 1
  field_simp
  ring

/-- Integration by parts for the Heine integrals:
`∫_0^R (-n/W^n + (2n+1)x/W^{n+1} - (n+1)/W^{n+2}) = s sinh R / W(R)^{n+1}`. -/
theorem legInt_heine_ibp {x : ℝ} (hx : 1 < x) (n : ℕ) (R : ℝ) :
    ∫ t in (0:ℝ)..R, (-(n:ℝ) * (1 / legInt_W x t ^ n) + (2*n+1)*x * (1 / legInt_W x t ^ (n+1)) -
      (n+1) * (1 / legInt_W x t ^ (n+2))) =
      Real.sqrt (x^2-1) * Real.sinh R / legInt_W x R ^ (n+1) := by
  set s := Real.sqrt (x^2-1) with hs_def
  have hss : s^2 = x^2-1 := Real.sq_sqrt (by nlinarith)
  have hd : ∀ t, HasDerivAt (fun t => s * Real.sinh t / legInt_W x t ^ (n+1))
      (-(n:ℝ) * (1 / legInt_W x t ^ n) + (2*n+1)*x * (1 / legInt_W x t ^ (n+1)) -
        (n+1) * (1 / legInt_W x t ^ (n+2))) t := by
    intro t
    have hW := legInt_W_pos hx t
    have hWd : HasDerivAt (legInt_W x) (s * Real.sinh t) t := by
      unfold legInt_W
      simpa using ((Real.hasDerivAt_cosh t).const_mul s).const_add x
    have h := ((Real.hasDerivAt_sinh t).const_mul s).div (hWd.pow (n+1)) (pow_ne_zero _ hW.ne')
    refine h.congr_deriv ?_
    have hc : Real.cosh t ^ 2 - Real.sinh t ^ 2 = 1 := by
      rw [Real.cosh_sq, Real.sinh_sq]; ring
    have hWe : legInt_W x t = x + s * Real.cosh t := rfl
    simp only [Pi.pow_apply, Nat.add_sub_cancel]
    generalize legInt_W x t = w at hW hWe ⊢
    have hw : w ≠ 0 := hW.ne'
    rw [show s * Real.cosh t * w^(n+1) - s * Real.sinh t * (((n+1:ℕ):ℝ) * w^n * (s * Real.sinh t)) =
        w^n * (s * Real.cosh t * w - (n+1) * s^2 * Real.sinh t^2) by push_cast; ring,
      show (w^(n+1))^2 = w^n * w^(n+2) by ring, mul_div_mul_left _ _ (pow_ne_zero _ hw)]
    rw [show -(n:ℝ) * (1 / w ^ n) + (2*n+1)*x * (1 / w ^ (n+1)) - (n+1) * (1 / w ^ (n+2)) =
        (-(n:ℝ) * w^2 + (2*n+1)*x*w - (n+1)) / w^(n+2) by field_simp; ring]
    congr 1
    rw [hWe]
    linear_combination (↑n + 1) * s ^ 2 * hc + (↑n + 1) * hss
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)]
  · simp
  · refine Continuous.intervalIntegrable ?_ _ _
    exact ((continuous_const.mul (legInt_cont_W_pow hx n)).add
      (continuous_const.mul (legInt_cont_W_pow hx (n+1)))).sub
      (continuous_const.mul (legInt_cont_W_pow hx (n+2)))

/-- The Heine recurrence for truncated integrals. -/
theorem legInt_heine_rec {x : ℝ} (hx : 1 < x) (n : ℕ) (R : ℝ) :
    (n+1) * (∫ t in (0:ℝ)..R, 1 / legInt_W x t ^ (n+2)) =
      -(n:ℝ) * (∫ t in (0:ℝ)..R, 1 / legInt_W x t ^ n) +
        (2*n+1)*x * (∫ t in (0:ℝ)..R, 1 / legInt_W x t ^ (n+1)) -
        Real.sqrt (x^2-1) * Real.sinh R / legInt_W x R ^ (n+1) := by
  rw [← legInt_heine_ibp hx n R]
  have hc := fun k : ℕ => (legInt_cont_W_pow hx k).intervalIntegrable (μ := volume) 0 R
  rw [intervalIntegral.integral_sub (((hc n).const_mul _).add ((hc _).const_mul _))
    ((hc _).const_mul _), intervalIntegral.integral_add ((hc n).const_mul _) ((hc _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  ring

/-- `s sinh R / W(R) → 1`. -/
theorem legInt_heine_bdry_one {x : ℝ} (hx : 1 < x) :
    Tendsto (fun R => Real.sqrt (x^2-1) * Real.sinh R / legInt_W x R ^ (0+1)) atTop (𝓝 1) := by
  set s := Real.sqrt (x^2-1)
  have h1 : Tendsto (fun R => x + s * Real.exp (-R)) atTop (𝓝 (x + s*0)) :=
    tendsto_const_nhds.add (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul s)
  have h2 := (h1.div_atTop (legInt_W_tendsto hx))
  have h3 := (tendsto_const_nhds (x := (1:ℝ))).sub h2
  rw [sub_zero] at h3
  refine h3.congr fun R => ?_
  have hW := (legInt_W_pos hx R).ne'
  simp only [zero_add, pow_one]
  field_simp
  unfold legInt_W
  rw [Real.cosh_eq, Real.sinh_eq]; ring

/-- `s sinh R / W(R)^{n+2} → 0`. -/
theorem legInt_heine_bdry {x : ℝ} (hx : 1 < x) (n : ℕ) :
    Tendsto (fun R => Real.sqrt (x^2-1) * Real.sinh R / legInt_W x R ^ (n+2)) atTop (𝓝 0) := by
  have h1 := legInt_heine_bdry_one hx
  have h2 : Tendsto (fun R => (legInt_W x R)⁻¹ ^ (n+1)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp (legInt_W_tendsto hx)).pow (n+1)
  have h3 := h1.mul h2
  rw [mul_zero] at h3
  refine h3.congr fun R => ?_
  rw [inv_pow, zero_add, pow_one, ← div_eq_mul_inv, div_div, ← pow_succ']

/-- Heine's integral for `Q_n` on `(1,∞)`, unnormalized. -/
theorem legInt_heine (x : ℝ) (hx : 1 < x) (n : ℕ) :
    Tendsto (fun R => ((∫ t in (0:ℝ)..R, 1 / legInt_W x t ^ (n+1) : ℝ) : ℂ)) atTop
      (𝓝 (legendreQ n x)) := by
  have hx1 : (x:ℂ)-1 ∈ slitPlane := legInt_one_lt_mem hx
  have hc : Continuous (fun r : ℝ => (r:ℂ)) := continuous_ofReal
  have h0 : Tendsto (fun R => ((∫ t in (0:ℝ)..R, 1 / legInt_W x t ^ (0+1) : ℝ) : ℂ)) atTop
      (𝓝 (legendreQ (0:ℕ) x)) := by
    have h := (hc.tendsto _).comp (legInt_heine_zero hx)
    have hv : legendreQ (0:ℕ) x = ((Real.log ((x+1)/(x-1)) / 2 : ℝ) : ℂ) := by
      rw [Nat.cast_zero, legendreQ_zero hx1, ofReal_div,
        ofReal_log (div_pos (by linarith) (by linarith)).le]
      push_cast; ring
    rw [hv]; exact h
  have key : ∀ n : ℕ, Tendsto (fun R => ((∫ t in (0:ℝ)..R, 1 / legInt_W x t ^ (n+1) : ℝ) : ℂ))
      atTop (𝓝 (legendreQ n x)) ∧
      Tendsto (fun R => ((∫ t in (0:ℝ)..R, 1 / legInt_W x t ^ (n+1+1) : ℝ) : ℂ))
      atTop (𝓝 (legendreQ (n+1:ℕ) x)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨h0, ?_⟩
      have hr := fun R => legInt_heine_rec hx 0 R
      have hb := (hc.tendsto _).comp (legInt_heine_bdry_one hx)
      have h := (h0.const_mul (x:ℂ)).sub hb
      have hQ1 : legendreQ ((0+1:ℕ):ℂ) x = x * legendreQ (0:ℕ) x - 1 := by
        rw [legendreQ_nat _ hx1]
        have := legendreP_nat 1 (one_add_mem_slitPlane_of_sub_one hx1)
        simp only [Nat.cast_zero, zero_add, Nat.cast_one] at this ⊢
        rw [this]
        simp [legendreQPoly, DLMF.OrthogonalPolynomials.legendrePolyP_one]
      rw [hQ1]
      convert h using 2 with R
      simp only [Function.comp_apply]
      have := hr R
      simp only [CharP.cast_eq_zero, zero_add, one_mul, neg_zero, zero_mul, mul_zero,
        pow_zero] at this ⊢
      rw [this]; push_cast; ring
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hr := fun R => legInt_heine_rec hx (k+1) R
      have hb := (hc.tendsto _).comp (legInt_heine_bdry hx k)
      have h := ((((ih.1.const_mul (-((k:ℂ)+1))).add (ih.2.const_mul ((2*((k:ℂ)+1)+1)*x))).sub
        hb).div_const ((k:ℂ)+2))
      have hrec := olverQ_recurrence_3 (k:ℂ) 0 hx1
      rw [show (k:ℂ)+2 = ((k+1+1:ℕ):ℂ) by push_cast; ring,
        show (k:ℂ)+1 = ((k+1:ℕ):ℂ) by push_cast; ring, legInt_olverQ_nat_zero_order _ hx1,
        legInt_olverQ_nat_zero_order _ hx1, legInt_olverQ_nat_zero_order _ hx1] at hrec
      have hQ : legendreQ ((k+1+1:ℕ):ℂ) x = (-((k:ℂ)+1) * legendreQ k x +
          (2*((k:ℂ)+1)+1)*x * legendreQ ((k+1:ℕ):ℂ) x - 0) / ((k:ℂ)+2) := by
        have hf : (k.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
        simp only [Nat.factorial_succ] at hrec
        push_cast at hrec ⊢
        have hk2 : (k:ℂ)+2 ≠ 0 := by norm_cast
        have hk1 : (k:ℂ)+1 ≠ 0 := by norm_cast
        field_simp at hrec
        rw [show (k:ℂ)+1+1 = k+2 by ring] at hrec ⊢
        have e : ((k:ℂ)+0+2)*((k:ℂ)-0+2)*legendreQ ((k:ℂ)+2) x/((k:ℂ)+2) =
            ((k:ℂ)+2)*legendreQ ((k:ℂ)+2) x := by field_simp; ring
        rw [eq_div_iff hk2]
        linear_combination hrec - e
      rw [hQ]
      convert h using 2 with R
      simp only [Function.comp_apply]
      have := hr R
      have hk2 : (k:ℝ)+1+1 ≠ 0 := by positivity
      push_cast at this ⊢
      rw [eq_div_iff (by norm_cast)]
      rw [show k+1+1+1 = k+1+2 by ring]
      apply_fun ((↑) : ℝ → ℂ) at this
      push_cast at this
      linear_combination this
  exact (key n).1

/-- The endpoint `u = ½ log((x+1)/(x-1)) = arcoth x`. -/
noncomputable def legInt_u (x : ℝ) : ℝ := 1/2*Real.log ((x+1)/(x-1))

/-- `√(x²-1) e^u = x+1` at `u = arcoth x`. -/
theorem legInt_s_exp_u {x : ℝ} (hx : 1 < x) :
    Real.sqrt (x^2-1) * Real.exp (legInt_u x) = x+1 := by
  have hq : 0 < (x+1)/(x-1) := div_pos (by linarith) (by linarith)
  have hs := Real.sqrt_nonneg (x^2-1)
  have hss : Real.sqrt (x^2-1)^2 = x^2-1 := Real.sq_sqrt (by nlinarith)
  have he : Real.exp (legInt_u x)^2 = (x+1)/(x-1) := by
    rw [← Real.exp_nat_mul, legInt_u]; push_cast
    rw [show (2:ℝ) * (1/2*Real.log ((x+1)/(x-1))) = Real.log ((x+1)/(x-1)) by ring,
      Real.exp_log hq]
  have h2 : (Real.sqrt (x^2-1) * Real.exp (legInt_u x))^2 = (x+1)^2 := by
    rw [mul_pow, hss, he]; field_simp; ring
  exact (sq_eq_sq₀ (by positivity) (by linarith)).1 h2

/-- `√(x²-1) cosh u = x` and `√(x²-1) sinh u = 1` at `u = arcoth x`. -/
theorem legInt_s_cosh_sinh_u {x : ℝ} (hx : 1 < x) :
    Real.sqrt (x^2-1) * Real.cosh (legInt_u x) = x ∧
      Real.sqrt (x^2-1) * Real.sinh (legInt_u x) = 1 := by
  have h1 := legInt_s_exp_u hx
  have hss : Real.sqrt (x^2-1)^2 = x^2-1 := Real.sq_sqrt (by nlinarith)
  have hee : Real.exp (legInt_u x) * Real.exp (-legInt_u x) = 1 := by
    rw [← Real.exp_add]; simp
  have h2 : Real.sqrt (x^2-1) * Real.exp (-legInt_u x) = x-1 := by
    have hx1 : x+1 ≠ 0 := by linarith
    have : (Real.sqrt (x^2-1) * Real.exp (-legInt_u x)) * (x+1) = (x-1)*(x+1) := by
      linear_combination (-(Real.sqrt (x^2-1) * Real.exp (-legInt_u x))) * h1 +
        (Real.sqrt (x^2-1))^2 * hee + hss
    exact mul_right_cancel₀ hx1 this
  rw [Real.cosh_eq, Real.sinh_eq]
  constructor
  · linear_combination h1/2 + h2/2
  · linear_combination h1/2 - h2/2

/-- The kernel `V(t) = x - √(x²-1) cosh t` of DLMF 14.12.9. -/
noncomputable def legInt_V (x t : ℝ) : ℝ := x - Real.sqrt (x^2-1) * Real.cosh t

/-- The integrand `V^n cosh(m t)`. -/
noncomputable def legInt_f (x : ℝ) (n m : ℕ) (t : ℝ) : ℝ := legInt_V x t ^ n * Real.cosh (m*t)

/-- The integrals `M(n,m) = ∫_0^u V^n cosh(m t)`. -/
noncomputable def legInt_M (x : ℝ) (n m : ℕ) : ℝ := ∫ t in (0:ℝ)..legInt_u x, legInt_f x n m t

/-- Continuity of `V^n cosh(m t)`. -/
theorem legInt_cont_f (x : ℝ) (n m : ℕ) : Continuous (legInt_f x n m) := by
  unfold legInt_f legInt_V; fun_prop

/-- `V(u) = 0`. -/
theorem legInt_V_u {x : ℝ} (hx : 1 < x) : legInt_V x (legInt_u x) = 0 := by
  rw [legInt_V, (legInt_s_cosh_sinh_u hx).1, sub_self]

/-- The degree recurrence `(n+2) M(n+2,0) = (2n+3) x M(n+1,0) - (n+1) M(n,0)`. -/
theorem legInt_M_deg {x : ℝ} (hx : 1 < x) (n : ℕ) :
    (n+2) * legInt_M x (n+2) 0 = (2*n+3)*x*legInt_M x (n+1) 0 - (n+1) * legInt_M x n 0 := by
  set s := Real.sqrt (x^2-1) with hs_def
  have hss : s^2 = x^2-1 := Real.sq_sqrt (by nlinarith)
  have hd : ∀ t, HasDerivAt (fun t => s * (legInt_V x t ^ (n+1) * Real.sinh t))
      (-(n+2) * legInt_f x (n+2) 0 t + (2*n+3)*x*legInt_f x (n+1) 0 t - (n+1) * legInt_f x n 0 t)
      t := by
    intro t
    have hV : HasDerivAt (legInt_V x) (-(s * Real.sinh t)) t := by
      unfold legInt_V
      simpa using ((Real.hasDerivAt_cosh t).const_mul s).const_sub x
    have h := ((hV.pow (n+1)).mul (Real.hasDerivAt_sinh t)).const_mul s
    refine h.congr_deriv ?_
    have hc : Real.cosh t ^ 2 - Real.sinh t ^ 2 = 1 := by
      rw [Real.cosh_sq, Real.sinh_sq]; ring
    have hv : legInt_V x t = x - s * Real.cosh t := rfl
    simp only [legInt_f, CharP.cast_eq_zero, zero_mul, Real.cosh_zero, mul_one, Nat.add_sub_cancel,
      Pi.pow_apply]
    generalize legInt_V x t = v at hv ⊢
    push_cast
    linear_combination v^n*((v - (n+1)*(2*(x-v) + (v - x + s*Real.cosh t)))*hv + (n+1)*hss +
      (n+1)*s^2*hc)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := legInt_u x)
    (fun t _ => hd t) (by
      refine Continuous.intervalIntegrable ?_ _ _
      exact ((continuous_const.mul (legInt_cont_f x _ _)).add
        (continuous_const.mul (legInt_cont_f x _ _))).sub
        (continuous_const.mul (legInt_cont_f x _ _)))
  have hc := fun k : ℕ => (legInt_cont_f x k 0).intervalIntegrable (μ := volume) 0 (legInt_u x)
  rw [intervalIntegral.integral_sub (((hc _).const_mul _).add ((hc _).const_mul _))
    ((hc _).const_mul _), intervalIntegral.integral_add ((hc _).const_mul _) ((hc _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, legInt_V_u hx] at hint
  simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
    zero_mul, mul_zero, Real.sinh_zero, sub_zero] at hint
  simp only [legInt_M]
  linarith

/-- The order recurrence
`(n+m+2) s M(n,m+2) = 2(m+1) x M(n,m+1) + (n-m) s M(n,m)`. -/
theorem legInt_M_ord {x : ℝ} (hx : 1 < x) (n m : ℕ) :
    (n+m+2) * Real.sqrt (x^2-1) * legInt_M x n (m+2) =
      2*(m+1)*x*legInt_M x n (m+1) + ((n:ℝ)-m) * Real.sqrt (x^2-1) * legInt_M x n m := by
  set s := Real.sqrt (x^2-1) with hs_def
  have hd : ∀ t, HasDerivAt (fun t => legInt_V x t ^ (n+1) * Real.sinh ((m+1)*t))
      ((1/2:ℝ) * (-(n+m+2) * s * legInt_f x n (m+2) t + 2*(m+1)*x*legInt_f x n (m+1) t +
        ((n:ℝ)-m) * s * legInt_f x n m t)) t := by
    intro t
    have hV : HasDerivAt (legInt_V x) (-(s * Real.sinh t)) t := by
      unfold legInt_V
      simpa using ((Real.hasDerivAt_cosh t).const_mul s).const_sub x
    have h3 : HasDerivAt (fun t : ℝ => Real.sinh ((m+1)*t)) (((m:ℝ)+1) * Real.cosh ((m+1)*t)) t := by
      have := (Real.hasDerivAt_sinh ((m+1)*t)).comp t ((hasDerivAt_id t).const_mul ((m:ℝ)+1))
      simpa [mul_comm, Function.comp_def] using this
    have h := (hV.pow (n+1)).mul h3
    refine h.congr_deriv ?_
    have hv : legInt_V x t = x - s * Real.cosh t := rfl
    have e1 : Real.cosh (((m+2:ℕ):ℝ)*t) = Real.cosh ((m+1)*t) * Real.cosh t +
        Real.sinh ((m+1)*t) * Real.sinh t := by
      rw [← Real.cosh_add]; push_cast; ring_nf
    have e2 : Real.cosh (((m:ℕ):ℝ)*t) = Real.cosh ((m+1)*t) * Real.cosh t -
        Real.sinh ((m+1)*t) * Real.sinh t := by
      rw [← Real.cosh_sub]; ring_nf
    simp only [legInt_f, e1, e2, Nat.add_sub_cancel, Pi.pow_apply]
    generalize legInt_V x t = v at hv ⊢
    push_cast
    linear_combination v^n*(m+1)*Real.cosh ((m+1)*t)*hv
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := legInt_u x)
    (fun t _ => hd t) (by
      refine Continuous.intervalIntegrable ?_ _ _
      exact continuous_const.mul (((continuous_const.mul (legInt_cont_f x _ _)).add
        (continuous_const.mul (legInt_cont_f x _ _))).add
        (continuous_const.mul (legInt_cont_f x _ _))))
  have hc := fun k : ℕ => (legInt_cont_f x n k).intervalIntegrable (μ := volume) 0 (legInt_u x)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (((hc _).const_mul _).add ((hc _).const_mul _)) ((hc _).const_mul _),
    intervalIntegral.integral_add ((hc _).const_mul _) ((hc _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, legInt_V_u hx] at hint
  simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
    zero_mul, mul_zero, Real.sinh_zero, sub_zero] at hint
  simp only [legInt_M]
  linarith

/-- `M(0,0) = u` and `M(1,0) = x u - 1`. -/
theorem legInt_M_base {x : ℝ} (hx : 1 < x) :
    legInt_M x 0 0 = legInt_u x ∧ legInt_M x 1 0 = x * legInt_u x - 1 := by
  constructor
  · simp [legInt_M, legInt_f]
  · have hd : ∀ t, HasDerivAt (fun t => x*t - Real.sqrt (x^2-1) * Real.sinh t) (legInt_f x 1 0 t) t :=
      fun t => by
        have := ((hasDerivAt_id t).const_mul x).sub ((Real.hasDerivAt_sinh t).const_mul
          (Real.sqrt (x^2-1)))
        exact this.congr_deriv (by simp [legInt_f, legInt_V])
    rw [legInt_M, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((legInt_cont_f x 1 0).intervalIntegrable _ _), (legInt_s_cosh_sinh_u hx).2]
    simp

/-- `s M(n,1) = x M(n,0) - M(n+1,0)`. -/
theorem legInt_M_one (x : ℝ) (n : ℕ) :
    Real.sqrt (x^2-1) * legInt_M x n 1 = x * legInt_M x n 0 - legInt_M x (n+1) 0 := by
  have hc := fun k : ℕ => (legInt_cont_f x k 0).intervalIntegrable (μ := volume) 0 (legInt_u x)
  simp only [legInt_M]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub ((hc _).const_mul _) (hc _)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [legInt_f, legInt_V, Nat.cast_one, one_mul, Nat.cast_zero, zero_mul, Real.cosh_zero]
  ring

/-- The Legendre recurrence `(k+2) Q_{k+2} = (2k+3) x Q_{k+1} - (k+1) Q_k` on the principal sheet. -/
theorem legInt_legendreQ_rec (k : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    ((k:ℂ)+2) * legendreQ ((k+2:ℕ):ℂ) z =
      (2*k+3)*z*legendreQ ((k+1:ℕ):ℂ) z - ((k:ℂ)+1) * legendreQ k z := by
  have hrec := olverQ_recurrence_3 (k:ℂ) 0 hz
  rw [show (k:ℂ)+2 = ((k+1+1:ℕ):ℂ) by push_cast; ring,
    show (k:ℂ)+1 = ((k+1:ℕ):ℂ) by push_cast; ring, legInt_olverQ_nat_zero_order _ hz,
    legInt_olverQ_nat_zero_order _ hz, legInt_olverQ_nat_zero_order _ hz] at hrec
  have hf : (k.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  simp only [Nat.factorial_succ] at hrec
  push_cast at hrec ⊢
  have hk2 : (k:ℂ)+2 ≠ 0 := by norm_cast
  have hk1 : (k:ℂ)+1 ≠ 0 := by norm_cast
  field_simp at hrec
  rw [show (k:ℂ)+1+1 = k+2 by ring] at hrec
  have e : ((k:ℂ)+0+2)*((k:ℂ)-0+2)*legendreQ ((k:ℂ)+2) z/((k:ℂ)+2) =
      ((k:ℂ)+2)*legendreQ ((k:ℂ)+2) z := by field_simp; ring
  linear_combination hrec - e

/-- `Q_n(x) = M(n,0)` for `x > 1`. -/
theorem legInt_legendreQ_M {x : ℝ} (hx : 1 < x) (n : ℕ) : legendreQ n x = legInt_M x n 0 := by
  have hx1 : (x:ℂ)-1 ∈ slitPlane := legInt_one_lt_mem hx
  have key : ∀ n : ℕ, legendreQ n x = legInt_M x n 0 ∧ legendreQ (n+1:ℕ) x = legInt_M x (n+1) 0 := by
    intro n
    induction n with
    | zero =>
      have h0 : legendreQ (0:ℕ) x = legInt_M x 0 0 := by
        rw [(legInt_M_base hx).1, Nat.cast_zero, legendreQ_zero hx1, legInt_u, ofReal_mul,
          ofReal_log (div_pos (by linarith) (by linarith)).le]
        push_cast; ring
      refine ⟨h0, ?_⟩
      have hQ0 : legendreQ 0 x = legInt_u x := by
        rw [← (legInt_M_base hx).1, ← h0, Nat.cast_zero]
      rw [zero_add, (legInt_M_base hx).2, legendreQ_nat _ hx1]
      have := legendreP_nat 1 (one_add_mem_slitPlane_of_sub_one hx1)
      simp only [Nat.cast_one] at this ⊢
      rw [this, hQ0]
      simp [legendreQPoly, DLMF.OrthogonalPolynomials.legendrePolyP_one]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h := legInt_legendreQ_rec k hx1
      have hM := legInt_M_deg hx k
      have hk2 : (k:ℂ)+2 ≠ 0 := by norm_cast
      rw [ih.1, ih.2] at h
      apply mul_left_cancel₀ hk2
      rw [show k+1+1 = k+2 by ring, h]
      apply_fun ((↑) : ℝ → ℂ) at hM
      push_cast at hM
      linear_combination -hM
  exact (key n).1

/-- The integrals `A(n,p) = ∫_{-1}^1 (1-t²)^n/(x-t)^p`. -/
noncomputable def legInt_A (x : ℝ) (n p : ℕ) : ℝ := ∫ t in (-1:ℝ)..1, (1-t^2)^n / (x-t)^p

/-- Continuity of the integrand of `legInt_A` on `[-1,1]`. -/
theorem legInt_contOn_A {x : ℝ} (hx : 1 < x) (n p : ℕ) :
    ContinuousOn (fun t : ℝ => (1-t^2)^n / (x-t)^p) (uIcc (-1) 1) := by
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => ?_
  rw [uIcc_of_le (by norm_num)] at ht
  exact pow_ne_zero _ (by linarith [ht.2])

/-- Interval integrability of the integrand of `legInt_A`. -/
theorem legInt_intInt_A {x : ℝ} (hx : 1 < x) (n p : ℕ) :
    IntervalIntegrable (fun t : ℝ => (1-t^2)^n / (x-t)^p) volume (-1) 1 :=
  (legInt_contOn_A hx n p).intervalIntegrable

/-- The algebraic relation `A(n+1,p+2) = (1-x²) A(n,p+2) + 2x A(n,p+1) - A(n,p)`. -/
theorem legInt_A_R1 {x : ℝ} (hx : 1 < x) (n p : ℕ) :
    legInt_A x (n+1) (p+2) = (1-x^2) * legInt_A x n (p+2) + 2*x * legInt_A x n (p+1) -
      legInt_A x n p := by
  have hi := legInt_intInt_A hx
  simp only [legInt_A]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((hi _ _).const_mul _) ((hi _ _).const_mul _),
    ← intervalIntegral.integral_sub (((hi _ _).const_mul _).add ((hi _ _).const_mul _)) (hi _ _)]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le (by norm_num)] at ht
  have hw : x - t ≠ 0 := by linarith [ht.2]
  field_simp
  ring

/-- Integration by parts: `2(n+1)(x A(n,p+1) - A(n,p)) = (p+1) A(n+1,p+2)`. -/
theorem legInt_A_R2 {x : ℝ} (hx : 1 < x) (n p : ℕ) :
    2*(n+1)*(x * legInt_A x n (p+1) - legInt_A x n p) = (p+1) * legInt_A x (n+1) (p+2) := by
  have hi := legInt_intInt_A hx
  have hd : ∀ t ∈ uIcc (-1:ℝ) 1, HasDerivAt (fun t : ℝ => (1-t^2)^(n+1) / (x-t)^(p+1))
      ((p+1) * ((1-t^2)^(n+1) / (x-t)^(p+2)) -
        2*(n+1)*(x * ((1-t^2)^n / (x-t)^(p+1)) - (1-t^2)^n / (x-t)^p)) t := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have hw : x - t ≠ 0 := by linarith [ht.2]
    have h1 : HasDerivAt (fun t : ℝ => (1-t^2)^(n+1)) ((n+1:ℕ) * (1-t^2)^n * (-(2*t))) t := by
      have := ((hasDerivAt_pow 2 t).const_sub 1).pow (n+1)
      exact this.congr_deriv (by push_cast; ring)
    have h2 : HasDerivAt (fun t : ℝ => (x-t)^(p+1)) ((p+1:ℕ) * (x-t)^p * (-1)) t := by
      have := ((hasDerivAt_id t).const_sub x).pow (p+1)
      exact this.congr_deriv (by simp)
    refine (h1.div h2 (pow_ne_zero _ hw)).congr_deriv ?_
    field_simp
    push_cast
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    refine ((((hi _ _).const_mul _)).sub ((((hi _ _).const_mul _).sub (hi _ _)).const_mul _)))
  rw [intervalIntegral.integral_sub ((hi _ _).const_mul _)
    ((((hi _ _).const_mul _).sub (hi _ _)).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub ((hi _ _).const_mul _) (hi _ _),
    intervalIntegral.integral_const_mul] at hint
  norm_num at hint
  simp only [legInt_A]
  linarith

/-- The order relation
`(p+1)(1-x²) A(n,p+2) + 2(p-n) x A(n,p+1) + (2n+1-p) A(n,p) = 0`. -/
theorem legInt_A_ord {x : ℝ} (hx : 1 < x) (n p : ℕ) :
    (p+1)*(1-x^2)*legInt_A x n (p+2) + 2*((p:ℝ)-n)*x*legInt_A x n (p+1) +
      (2*n+1-(p:ℝ))*legInt_A x n p = 0 := by
  linear_combination (-((p:ℝ)+1))*legInt_A_R1 hx n p - legInt_A_R2 hx n p

/-- `A(n+1,n+2) = 2x A(n,n+1) - 2(x²-1) A(n,n+2)`. -/
theorem legInt_A_b {x : ℝ} (hx : 1 < x) (n : ℕ) :
    legInt_A x (n+1) (n+2) = 2*x*legInt_A x n (n+1) - 2*(x^2-1)*legInt_A x n (n+2) := by
  have h1 := legInt_A_R1 hx n n
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  have h2 := mul_left_cancel₀ hn (by linear_combination legInt_A_R2 hx n n :
    ((n:ℝ)+1) * (2*(x*legInt_A x n (n+1) - legInt_A x n n)) = ((n:ℝ)+1) * legInt_A x (n+1) (n+2))
  linear_combination 2*h1 + h2

/-- The degree recurrence `(n+2) A(n+2,n+3) = 2(2n+3) x A(n+1,n+2) - 4(n+1) A(n,n+1)`. -/
theorem legInt_A_deg {x : ℝ} (hx : 1 < x) (n : ℕ) :
    (n+2)*legInt_A x (n+2) (n+3) = 2*(2*n+3)*x*legInt_A x (n+1) (n+2) -
      4*(n+1)*legInt_A x n (n+1) := by
  have B0 := legInt_A_b hx n
  have B1 := legInt_A_b hx (n+1)
  have R := legInt_A_R1 hx n (n+1)
  have O := legInt_A_ord hx n (n+1)
  simp only [show n+1+1 = n+2 by ring, show n+1+2 = n+3 by ring] at B1 R O
  push_cast at B1 R O ⊢
  linear_combination ((n:ℝ)+2)*B1 - 2*(x^2-1)*((n:ℝ)+2)*R - 2*(x^2-1)*O - 2*((n:ℝ)+1)*x*B0

/-- `A(0,1) = log((x+1)/(x-1))` and `A(0,2) = 2/(x²-1)`. -/
theorem legInt_A_base {x : ℝ} (hx : 1 < x) :
    legInt_A x 0 1 = Real.log ((x+1)/(x-1)) ∧ legInt_A x 0 2 = 2/(x^2-1) := by
  have hi := legInt_intInt_A hx
  constructor
  · have hd : ∀ t ∈ uIcc (-1:ℝ) 1, HasDerivAt (fun t => -Real.log (x-t)) ((1-t^2)^0/(x-t)^1) t := by
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht
      have hw : x - t ≠ 0 := by linarith [ht.2]
      have := (((hasDerivAt_id t).const_sub x).log hw).neg
      exact this.congr_deriv (by simp [neg_div])
    rw [legInt_A, intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hi 0 1),
      Real.log_div (by linarith) (by linarith)]
    ring_nf
  · have hd : ∀ t ∈ uIcc (-1:ℝ) 1, HasDerivAt (fun t => 1/(x-t)) ((1-t^2)^0/(x-t)^2) t := by
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht
      have hw : x - t ≠ 0 := by linarith [ht.2]
      have := (((hasDerivAt_id t).const_sub x)).inv hw
      exact (this.congr_deriv (by simp)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => by simp)
    rw [legInt_A, intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hi 0 2)]
    have h1 : x - 1 ≠ 0 := by linarith
    have h2 : x + 1 ≠ 0 := by linarith
    have h3 : x^2 - 1 ≠ 0 := by nlinarith
    have h4 : 1 + x ≠ 0 := by linarith
    norm_num
    field_simp
    ring

/-- `Q_n(x) = A(n,n+1)/2^{n+1}` for `x > 1`. -/
theorem legInt_legendreQ_A {x : ℝ} (hx : 1 < x) (n : ℕ) :
    legendreQ n x = legInt_A x n (n+1) / 2^(n+1) := by
  have hx1 : (x:ℂ)-1 ∈ slitPlane := legInt_one_lt_mem hx
  have key : ∀ n : ℕ, legendreQ n x = legInt_A x n (n+1) / 2^(n+1) ∧
      legendreQ (n+1:ℕ) x = legInt_A x (n+1) (n+1+1) / 2^(n+1+1) := by
    intro n
    induction n with
    | zero =>
      have hQ0 : legendreQ 0 x = Real.log ((x+1)/(x-1)) / 2 := by
        rw [legendreQ_zero hx1, ofReal_log (div_pos (by linarith) (by linarith)).le]
        push_cast; ring
      refine ⟨by rw [Nat.cast_zero, hQ0, (legInt_A_base hx).1]; push_cast; ring, ?_⟩
      rw [zero_add, legendreQ_nat _ hx1]
      have := legendreP_nat 1 (one_add_mem_slitPlane_of_sub_one hx1)
      simp only [Nat.cast_one] at this ⊢
      rw [this, hQ0, legInt_A_b hx 0, (legInt_A_base hx).1, (legInt_A_base hx).2]
      have h3 : (x:ℂ)^2 - 1 ≠ 0 := by
        rw [show (x:ℂ)^2-1 = ((x^2-1:ℝ):ℂ) by push_cast; ring]
        exact ofReal_ne_zero.2 (by nlinarith)
      simp [legendreQPoly, DLMF.OrthogonalPolynomials.legendrePolyP_one]
      field_simp
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h := legInt_legendreQ_rec k hx1
      have hA := legInt_A_deg hx k
      have hk2 : (k:ℂ)+2 ≠ 0 := by norm_cast
      rw [ih.1, ih.2] at h
      apply mul_left_cancel₀ hk2
      rw [show k+1+1 = k+2 by ring, h]
      apply_fun ((↑) : ℝ → ℂ) at hA
      push_cast at hA ⊢
      rw [show k+1+1 = k+2 by ring, show k+2+1 = k+3 by ring]
      linear_combination -hA / (2:ℂ)^(k+3)
  exact (key n).1

/-- The real Laplace kernel `w(θ) = x + √(x²-1) cos θ`. -/
noncomputable def legInt_w (x θ : ℝ) : ℝ := x + Real.sqrt (x^2-1) * Real.cos θ

/-- The moments `K(p,q) = ∫_0^π w^p sin^{2q}θ`. -/
noncomputable def legInt_Ks (x : ℝ) (p q : ℕ) : ℝ :=
  ∫ θ in (0:ℝ)..π, legInt_w x θ ^ p * Real.sin θ ^ (2*q)

/-- Continuity of the integrand of `legInt_Ks`. -/
theorem legInt_cont_Ks (x : ℝ) (p q : ℕ) :
    Continuous fun θ => legInt_w x θ ^ p * Real.sin θ ^ (2*q) := by
  unfold legInt_w; fun_prop

/-- Derivative of the real Laplace kernel. -/
theorem legInt_hasDerivAt_w (x θ : ℝ) :
    HasDerivAt (legInt_w x) (-(Real.sqrt (x^2-1) * Real.sin θ)) θ := by
  unfold legInt_w
  simpa using ((Real.hasDerivAt_cos θ).const_mul (Real.sqrt (x^2-1))).const_add x

/-- Integration by parts:
`(r+2q+3) K(r+1,q+1) = (r+1) x K(r,q+1) + (2q+1) K(r+1,q)`. -/
theorem legInt_Ks_star (x : ℝ) (r q : ℕ) :
    (r+2*q+3) * legInt_Ks x (r+1) (q+1) = (r+1)*x*legInt_Ks x r (q+1) +
      (2*q+1) * legInt_Ks x (r+1) q := by
  have hd : ∀ θ, HasDerivAt (fun θ => legInt_w x θ ^ (r+1) * (Real.sin θ ^ (2*q+1) * Real.cos θ))
      (-(r+2*q+3) * (legInt_w x θ ^ (r+1) * Real.sin θ ^ (2*(q+1))) +
        (r+1)*x*(legInt_w x θ ^ r * Real.sin θ ^ (2*(q+1))) +
        (2*q+1) * (legInt_w x θ ^ (r+1) * Real.sin θ ^ (2*q))) θ := by
    intro θ
    have h1 := (legInt_hasDerivAt_w x θ).pow (r+1)
    have h2 := ((Real.hasDerivAt_sin θ).pow (2*q+1)).mul (Real.hasDerivAt_cos θ)
    refine (h1.mul h2).congr_deriv ?_
    have hv : legInt_w x θ = x + Real.sqrt (x^2-1) * Real.cos θ := rfl
    have hsc := Real.sin_sq_add_cos_sq θ
    simp only [Pi.pow_apply, Pi.mul_apply, Nat.add_sub_cancel]
    generalize legInt_w x θ = v at hv ⊢
    push_cast
    linear_combination ((r:ℝ)+1)*v^r*Real.sin θ^(2*q+2)*hv +
      (2*(q:ℝ)+1)*v^(r+1)*Real.sin θ^(2*q)*hsc
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := π)
    (fun θ _ => hd θ) (by
      refine Continuous.intervalIntegrable ?_ _ _
      exact ((continuous_const.mul (legInt_cont_Ks x _ _)).add
        (continuous_const.mul (legInt_cont_Ks x _ _))).add
        (continuous_const.mul (legInt_cont_Ks x _ _)))
  have hc := fun p k : ℕ => (legInt_cont_Ks x p k).intervalIntegrable (μ := volume) 0 π
  rw [intervalIntegral.integral_add (((hc _ _).const_mul _).add ((hc _ _).const_mul _))
    ((hc _ _).const_mul _), intervalIntegral.integral_add ((hc _ _).const_mul _)
    ((hc _ _).const_mul _), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hint
  simp only [Real.sin_pi, Real.sin_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, zero_mul, mul_zero, sub_zero] at hint
  simp only [legInt_Ks]
  linarith

/-- Integration by parts:
`(p+1) s² K(p,q+1) = (2q+1) (K(p+2,q) - x K(p+1,q))`, `s = √(x²-1)`. -/
theorem legInt_Ks_ibp (x : ℝ) (p q : ℕ) :
    ((p:ℝ)+1) * Real.sqrt (x^2-1)^2 * legInt_Ks x p (q+1) =
      (2*q+1) * (legInt_Ks x (p+2) q - x * legInt_Ks x (p+1) q) := by
  have hd : ∀ θ, HasDerivAt (fun θ => Real.sqrt (x^2-1) * (legInt_w x θ ^ (p+1) * Real.sin θ ^ (2*q+1)))
      (-(((p:ℝ)+1) * Real.sqrt (x^2-1)^2) * (legInt_w x θ ^ p * Real.sin θ ^ (2*(q+1))) +
        (2*q+1) * (legInt_w x θ ^ (p+2) * Real.sin θ ^ (2*q)) -
        (2*q+1) * x * (legInt_w x θ ^ (p+1) * Real.sin θ ^ (2*q))) θ := by
    intro θ
    have h1 := (legInt_hasDerivAt_w x θ).pow (p+1)
    have h2 := (Real.hasDerivAt_sin θ).pow (2*q+1)
    refine ((h1.mul h2).const_mul (Real.sqrt (x^2-1))).congr_deriv ?_
    have hv : legInt_w x θ = x + Real.sqrt (x^2-1) * Real.cos θ := rfl
    simp only [Pi.pow_apply, Nat.add_sub_cancel]
    generalize legInt_w x θ = v at hv ⊢
    push_cast
    linear_combination (-(2*(q:ℝ)+1))*v^(p+1)*Real.sin θ^(2*q)*hv
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := π)
    (fun θ _ => hd θ) (by
      refine Continuous.intervalIntegrable ?_ _ _
      exact ((continuous_const.mul (legInt_cont_Ks x _ _)).add
        (continuous_const.mul (legInt_cont_Ks x _ _))).sub
        (continuous_const.mul (legInt_cont_Ks x _ _)))
  have hc := fun p k : ℕ => (legInt_cont_Ks x p k).intervalIntegrable (μ := volume) 0 π
  rw [intervalIntegral.integral_sub (((hc _ _).const_mul _).add ((hc _ _).const_mul _))
    ((hc _ _).const_mul _), intervalIntegral.integral_add ((hc _ _).const_mul _)
    ((hc _ _).const_mul _), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hint
  simp only [Real.sin_pi, Real.sin_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, mul_zero, sub_zero] at hint
  simp only [legInt_Ks]
  linarith

/-- `K(r+2,0) - x K(r+1,0) = (r+1) s² K(r,1)`. -/
theorem legInt_Ks_one (x : ℝ) (r : ℕ) :
    legInt_Ks x (r+2) 0 - x * legInt_Ks x (r+1) 0 = (r+1) * Real.sqrt (x^2-1)^2 * legInt_Ks x r 1 := by
  have := legInt_Ks_ibp x r 0
  simp only [CharP.cast_eq_zero, mul_zero, zero_add, one_mul] at this
  linarith

/-- The constant `2^m m! (2m+p)! / ((2m)! p! π)` of DLMF 14.12.8 with `n = m+p`. -/
noncomputable def legInt_cK (m p : ℕ) : ℂ :=
  2^m*(m.factorial:ℂ)*(2*m+p).factorial/(((2*m).factorial:ℂ)*p.factorial*π)

/-- Ratio of consecutive constants `legInt_cK`. -/
theorem legInt_cK_succ (m p : ℕ) :
    legInt_cK (m+1) (p+1) * (2*m+1) = legInt_cK m (p+2) * (2*m+p+3) * (p+2) := by
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  simp only [legInt_cK]
  rw [show 2*(m+1)+(p+1) = 2*m+p+2+1 by ring, show 2*(m+1) = 2*m+1+1 by ring,
    show 2*m+(p+2) = 2*m+p+2 by ring, show p+2 = p+1+1 by ring]
  simp only [Nat.factorial_succ]
  push_cast
  have n1 : (2*(m:ℂ)+1) ≠ 0 := by norm_cast
  have n2 : (2*(m:ℂ)+1+1) ≠ 0 := by norm_cast
  have n3 : (2*(m:ℂ)+1+1+1) ≠ 0 := by norm_cast
  have n4 : (2*(m:ℂ)+1+1+1+1) ≠ 0 := by norm_cast
  have n5 : ((p:ℂ)+1) ≠ 0 := by norm_cast
  have n6 : ((p:ℂ)+1+1) ≠ 0 := by norm_cast
  have n7 : ((m:ℂ)+1) ≠ 0 := by norm_cast
  have n8 : ((m:ℂ)+1+1) ≠ 0 := by norm_cast
  have f1 : ((2*m).factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have f2 : (p.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have f3 : ((m.factorial:ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  simp only [div_mul_eq_mul_div]
  rw [div_eq_div_iff (by apply_rules [mul_ne_zero]) (by apply_rules [mul_ne_zero])]
  ring

/-- Ratio of consecutive constants `legInt_cK`. -/
theorem legInt_cK_succ' (m p : ℕ) :
    legInt_cK (m+2) p * (2*m+3) = legInt_cK (m+1) (p+1) * (2*m+p+4) * (p+1) := by
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  simp only [legInt_cK]
  rw [show 2*(m+2)+p = 2*m+p+3+1 by ring, show 2*(m+1)+(p+1) = 2*m+p+3 by ring,
    show 2*(m+2) = 2*m+1+1+1+1 by ring, show 2*(m+1) = 2*m+1+1 by ring, show m+2 = m+1+1 by ring]
  simp only [Nat.factorial_succ]
  push_cast
  have n1 : (2*(m:ℂ)+1) ≠ 0 := by norm_cast
  have n2 : (2*(m:ℂ)+1+1) ≠ 0 := by norm_cast
  have n3 : (2*(m:ℂ)+1+1+1) ≠ 0 := by norm_cast
  have n4 : (2*(m:ℂ)+1+1+1+1) ≠ 0 := by norm_cast
  have n5 : ((p:ℂ)+1) ≠ 0 := by norm_cast
  have n6 : ((p:ℂ)+1+1) ≠ 0 := by norm_cast
  have n7 : ((m:ℂ)+1) ≠ 0 := by norm_cast
  have n8 : ((m:ℂ)+1+1) ≠ 0 := by norm_cast
  have f1 : ((2*m).factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have f2 : (p.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have f3 : ((m.factorial:ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  simp only [div_mul_eq_mul_div]
  rw [div_eq_div_iff (by apply_rules [mul_ne_zero] <;> norm_cast)
    (by apply_rules [mul_ne_zero])]
  ring

/-- DLMF 14.12.8 in the form `P^m_{m+p}(x) = c s^m K(p,m)`. -/
theorem legInt_associatedP_Ks {x : ℝ} (hx : 1 < x) (m p : ℕ) :
    associatedP ((m+p:ℕ):ℂ) m x = legInt_cK m p * (Real.sqrt (x^2-1):ℂ)^m * legInt_Ks x p m := by
  have hx1 : ((x:ℂ)-1) ∈ slitPlane := legInt_one_lt_mem hx
  set s := Real.sqrt (x^2-1) with hs_def
  have hs : (s:ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 (by nlinarith)).ne'
  have hb1 : legendreBranchPower 1 x = s := by
    rw [legInt_legendreBranchPower_real _ hx, show (x:ℂ)^2-1 = ((x^2-1:ℝ):ℂ) by push_cast; ring,
      hs_def, Real.sqrt_eq_rpow, ofReal_cpow (by nlinarith)]
    push_cast; ring_nf
  have hbm : legendreBranchPower (-1) x * s = 1 := by
    rw [← hb1, legendreBranchPower_mul, neg_add_cancel]; simp [legendreBranchPower]
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have h0 : ∀ k : ℕ, associatedP (k:ℂ) 0 x = legInt_Ks x k 0 / π := fun k => by
    rw [associatedP_zero_order _ hx1, legendreP_laplace _ hx.le, legInt_Ks,
      ← intervalIntegral.integral_ofReal]
    simp only [mul_zero, pow_zero, mul_one]
    rw [one_div_mul_eq_div]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [legInt_w]
    rw [cpow_natCast, ofReal_pow]
  have hc0 : ∀ p : ℕ, legInt_cK 0 p = 1/π := fun p => by
    have := Nat.factorial_ne_zero p
    simp [legInt_cK]; field_simp
  have key : ∀ m : ℕ, (∀ p : ℕ, associatedP ((m+p:ℕ):ℂ) m x =
      legInt_cK m p * (s:ℂ)^m * legInt_Ks x p m) ∧ (∀ p : ℕ, associatedP ((m+1+p:ℕ):ℂ) (m+1:ℕ) x =
      legInt_cK (m+1) p * (s:ℂ)^(m+1) * legInt_Ks x p (m+1)) := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun p => by rw [Nat.cast_zero, zero_add, h0, hc0]; simp; ring, fun p => ?_⟩
      have h7 := associatedP_recurrence_7 ((p+1:ℕ):ℂ) 0 hx1
      have hK := legInt_Ks_one x p
      rw [hb1, zero_add, show ((p+1:ℕ):ℂ)+1 = ((p+2:ℕ):ℂ) by push_cast; ring, h0, h0] at h7
      apply mul_left_cancel₀ hs
      apply_fun ((↑) : ℝ → ℂ) at hK
      have hc1 : legInt_cK 1 p = ((p:ℂ)+1)*((p:ℂ)+2)/π := by
        simp only [legInt_cK]
        rw [show 2*1+p = p+1+1 by ring]
        simp only [Nat.factorial_succ]
        push_cast
        have := Nat.factorial_ne_zero p
        field_simp
        ring
      rw [show 0+1+p = p+1 by ring, hc1]
      have hss : (s:ℂ)^2 = (x:ℂ)^2-1 := by
        rw [← ofReal_pow, hs_def, Real.sq_sqrt (by nlinarith)]; push_cast; ring
      push_cast at hK h7 ⊢
      rw [← hs_def] at hK
      linear_combination h7 + ((p:ℂ)+2)/π * hK
    | succ k ih =>
      refine ⟨ih.2, fun p => ?_⟩
      have h6 := associatedP_recurrence_6 ((k+1+1+p:ℕ):ℂ) (k:ℂ) hx1
      have e1 := ih.1 (p+2)
      have e2 := ih.2 (p+1)
      rw [show k+(p+2) = k+1+1+p by ring] at e1
      rw [show k+1+(p+1) = k+1+1+p by ring] at e2
      rw [show (k:ℂ)+1 = ((k+1:ℕ):ℂ) by push_cast; ring, e2,
        show (k:ℂ)+2 = ((k+1+1:ℕ):ℂ) by push_cast; ring, e1] at h6
      have hst := legInt_Ks_star x (p+1) k
      have hib := legInt_Ks_ibp x p (k+1)
      have hr1 := legInt_cK_succ k p
      have hr2 := legInt_cK_succ' k p
      have h23 : (2*(k:ℂ)+3) ≠ 0 := by norm_cast
      apply mul_left_cancel₀ (mul_ne_zero h23 hs)
      apply_fun ((↑) : ℝ → ℂ) at hst hib
      push_cast at hst hib h6 hr1 hr2 ⊢
      rw [← hs_def] at hib
      simp only [show k+1+1 = k+2 by ring] at h6 hib hst ⊢
      linear_combination (2*(k:ℂ)+3)*(s:ℂ)*h6
        - 2*((k:ℂ)+1)*(2*k+3)*x*legInt_cK (k+1) (p+1)*(s:ℂ)^(k+1)*(legInt_Ks x (p+1) (k+1):ℂ)*hbm
        - (2*(k:ℂ)+3)*(s:ℂ)^(k+1)*(legInt_Ks x (p+2) k:ℂ)*hr1
        - (s:ℂ)^(k+3)*(legInt_Ks x p (k+2):ℂ)*hr2
        - (2*(k:ℂ)+3)*legInt_cK (k+1) (p+1)*(s:ℂ)^(k+1)*hst
        - legInt_cK (k+1) (p+1)*(s:ℂ)^(k+1)*((p:ℂ)+2*k+4)*hib
  exact (key m).1 p

end DLMF.Legendre
