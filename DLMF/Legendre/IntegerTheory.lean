/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.AssociatedRecurrences
public import DLMF.OrthogonalPolynomials.Integrals

/-!
# Integer degrees and orders and Rodrigues formulas

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

/- DLMF 14.7.13: Mathlib `Polynomial.factorial_mul_shiftedLegendre_eq`
is Rodrigues’ formula for P_n(1-2x). The affine normalization is already
proved locally by `DLMF.OrthogonalPolynomials.aeval_shiftedLegendre_eq_legendrePolyP`.
The upstream Rodrigues proof is not duplicated here. -/

/-- ferrersP nat polynomial. -/
@[dlmf 14.7.E1]
theorem ferrersP_nat_polynomial (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP n 0 x=DLMF.OrthogonalPolynomials.legendrePolyP n x := by
  rw [ferrersP_zero _ hx.1,legendreP_nat]
  left
  simp
  linarith [hx.1]

section RodriguesHelpers

open DLMF.OrthogonalPolynomials

/-- Iterated derivatives of a polynomial function are the iterated polynomial derivatives. -/
theorem iteratedDeriv_eval_polynomial {𝕜 : Type*} [NontriviallyNormedField 𝕜] (p : Polynomial 𝕜)
    (k : ℕ) : iteratedDeriv k (fun z => p.eval z) = fun z => (Polynomial.derivative^[k] p).eval z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    rw [Polynomial.deriv, Function.iterate_succ_apply']

/-- Real-variable iterated derivatives of the complexification of a real polynomial. -/
theorem iteratedDeriv_ofReal_eval_polynomial (p : Polynomial ℝ) (k : ℕ) :
    iteratedDeriv k (fun x : ℝ => ((p.eval x : ℝ) : ℂ)) =
      fun x => (((Polynomial.derivative^[k] p).eval x : ℝ) : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [((Polynomial.hasDerivAt _ x).ofReal_comp).deriv, Function.iterate_succ_apply']

/-- A real polynomial representing the Legendre polynomial `P_n`. -/
noncomputable def legendrePolyR (n : ℕ) : Polynomial ℝ :=
  ((Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)).comp
    (Polynomial.C (1/2) * (1 - Polynomial.X))

/-- `P_n(z)` is the evaluation of the complexified real polynomial `legendrePolyR n`. -/
theorem legendrePolyP_eq_eval (n : ℕ) (z : ℂ) :
    legendrePolyP n z = ((legendrePolyR n).map ofRealHom).eval z := by
  have h := aeval_shiftedLegendre_eq_legendrePolyP n ((1-z)/2)
  rw [show 1 - 2*((1-z)/2) = z by ring] at h
  rw [← h, legendrePolyR, Polynomial.map_comp, Polynomial.eval_comp, Polynomial.map_map]
  simp [Polynomial.aeval_def, Polynomial.eval_map]
  rw [show ofRealHom.comp (Int.castRingHom ℝ) = Int.castRingHom ℂ from RingHom.ext_int _ _]
  congr 1; ring

/-- Evaluating a complexified real polynomial at a real point. -/
theorem eval_ofReal_map_ofRealHom (p : Polynomial ℝ) (x : ℝ) :
    (p.map ofRealHom).eval (x:ℂ) = ((p.eval x : ℝ) : ℂ) := by
  rw [Polynomial.eval_map]; exact Polynomial.eval₂_at_apply ofRealHom x

/-- Complex Rodrigues formula `P_n(z) = (2ⁿ n!)⁻¹ dⁿ/dzⁿ (z²-1)ⁿ` (DLMF 18.5.5). -/
theorem legendrePolyP_rodrigues_complex (n : ℕ) (z : ℂ) :
    legendrePolyP n z = (2^n*(n.factorial:ℂ))⁻¹ * iteratedDeriv n (fun z : ℂ => (z^2-1)^n) z := by
  set R : Polynomial ℝ := (Polynomial.X^2 - 1)^n
  set B : Polynomial ℝ := Polynomial.C ((2^n*(n.factorial:ℝ))⁻¹) * Polynomial.derivative^[n] R
  have hAB : legendrePolyR n = B := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ((Set.Ioo_infinite (show (-1:ℝ) < 1 by norm_num)).mono ?_)
    intro x hx
    have h := legendre_rodrigues n hx
    rw [legendrePolyP_eq_eval, eval_ofReal_map_ofRealHom, ← iteratedDeriv_eq_iterate] at h
    have hR : (fun t : ℝ => (t^2-1)^n) = fun t => R.eval t := by
      funext t; simp [R]
    rw [hR, iteratedDeriv_eval_polynomial] at h
    simp only [Set.mem_ofPred_eq, B, Polynomial.eval_mul, Polynomial.eval_C]
    exact_mod_cast h
  have hRC : (fun z : ℂ => (z^2-1)^n) = fun z => (R.map ofRealHom).eval z := by
    funext w; simp [R]
  rw [legendrePolyP_eq_eval, hAB, hRC, iteratedDeriv_eval_polynomial, Polynomial.iterate_derivative_map]
  simp [B, Polynomial.map_mul]

/-- `dᵐ P_n(z)/dzᵐ = (2ⁿ n!)⁻¹ dᵐ⁺ⁿ/dzᵐ⁺ⁿ (z²-1)ⁿ`. -/
theorem iteratedDeriv_legendrePolyP_rodrigues (n m : ℕ) (z : ℂ) :
    iteratedDeriv m (legendrePolyP n) z =
      (2^n*(n.factorial:ℂ))⁻¹ * iteratedDeriv (m+n) (fun z : ℂ => (z^2-1)^n) z := by
  set Rc : Polynomial ℂ := (Polynomial.X^2 - 1)^n
  have hRc : (fun z : ℂ => (z^2-1)^n) = fun z => Rc.eval z := by funext w; simp [Rc]
  have hP : legendrePolyP n = fun w =>
      (Polynomial.C ((2^n*(n.factorial:ℂ))⁻¹) * Polynomial.derivative^[n] Rc).eval w := by
    funext w
    rw [legendrePolyP_rodrigues_complex, hRc, iteratedDeriv_eval_polynomial, Polynomial.eval_mul,
      Polynomial.eval_C]
  rw [hP, hRc, iteratedDeriv_eval_polynomial, iteratedDeriv_eval_polynomial]
  dsimp only
  rw [Polynomial.iterate_derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C,
    ← Function.iterate_add_apply]

end RodriguesHelpers

/-- ferrersP nat order rodrigues. -/
@[dlmf 14.7.E8, dlmf 14.7.E10]
theorem ferrersP_nat_order_rodrigues (n m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP n m x=(-1)^(m+n)*(1-x^2:ℂ)^((m:ℂ)/2)/(2^n*(n.factorial:ℂ))*iteratedDeriv (m+n) (fun x : ℝ => (1-x^2:ℂ)^n) x := by
  have hs : 1+(x:ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  have hev : legendreP (n:ℂ) =ᶠ[𝓝 (x:ℂ)] DLMF.OrthogonalPolynomials.legendrePolyP n := by
    filter_upwards [isOpen_one_add_mem_slitPlane.mem_nhds hs] with w hw
    rw [legendreP_nat n hw]
  set R : Polynomial ℝ := (Polynomial.X^2 - 1)^n
  set p : Polynomial ℝ := (1 - Polynomial.X^2)^n
  have hp : p = Polynomial.C ((-1:ℝ)^n) * R := by
    simp only [p, R, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_1, ← mul_pow]; ring_nf
  have hf : (fun x : ℝ => (1-(x:ℂ)^2)^n) = fun x : ℝ => ((p.eval x : ℝ) : ℂ) := by
    funext t; simp [p]
  have hRc : (fun z : ℂ => (z^2-1)^n) = fun z => (R.map ofRealHom).eval z := by
    funext w; simp [R]
  have hc : ((((1-x^2)^((m:ℝ)/2)) : ℝ) : ℂ) = (1-(x:ℂ)^2)^((m:ℂ)/2) := by
    rw [ofReal_cpow (by nlinarith [hx.1, hx.2])]; push_cast; ring_nf
  have hsq : (-1:ℂ)^n*(-1)^n = 1 := by rw [← mul_pow]; norm_num
  rw [ferrersP_nat n m hx, hev.iteratedDeriv_eq, iteratedDeriv_legendrePolyP_rodrigues, hRc,
    iteratedDeriv_eval_polynomial]
  dsimp only
  rw [Polynomial.iterate_derivative_map, eval_ofReal_map_ofRealHom, hf,
    iteratedDeriv_ofReal_eval_polynomial]
  dsimp only
  rw [hp, Polynomial.iterate_derivative_C_mul,
    Polynomial.eval_mul, Polynomial.eval_C, hc]
  push_cast
  rw [pow_add]
  linear_combination -((-1:ℂ)^m * (1-(x:ℂ)^2)^((m:ℂ)/2) * (2^n*(n.factorial:ℂ))⁻¹ *
    (((Polynomial.derivative^[m+n] R).eval x : ℝ) : ℂ)) * hsq

/-- associatedP nat order rodrigues. -/
@[dlmf 14.7.E14]
theorem associatedP_nat_order_rodrigues (n m : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP n m z=legendreBranchPower m z/(2^n*(n.factorial:ℂ))*iteratedDeriv (m+n) (fun z : ℂ => (z^2-1)^n) z := by
  have hev : associatedP (n:ℂ) 0 =ᶠ[𝓝 z] DLMF.OrthogonalPolynomials.legendrePolyP n := by
    filter_upwards [(isOpen_slitPlane.preimage (by fun_prop : Continuous fun w : ℂ => w-1)).mem_nhds hz]
      with w hw
    rw [associatedP_zero_order _ hw, legendreP_nat n (one_add_mem_slitPlane_of_sub_one hw)]
  rw [associatedP_nat_order_derivative n m hz, hev.iteratedDeriv_eq,
    iteratedDeriv_legendrePolyP_rodrigues]
  ring

/-- associatedP equal nat order. -/
@[dlmf 14.7.E15]
theorem associatedP_equal_nat_order (m : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP m m z=((2*m).factorial:ℂ)/(2^m*(m.factorial:ℂ))*legendreBranchPower m z := by
  have hz' := one_add_mem_slitPlane_of_sub_one hz
  have hw := mem_cutPlane_of_one_add hz'
  have hev : associatedP (m:ℂ) 0 =ᶠ[𝓝 z] legendreP m := by
    filter_upwards [(isOpen_slitPlane.preimage (by fun_prop : Continuous fun w : ℂ => w-1)).mem_nhds hz]
      with w hw using associatedP_zero_order _ hw
  have hc : ((2*m).factorial : ℂ) = ((2*m).choose m) * m.factorial * m.factorial := by
    have h := congrArg (Nat.cast : ℕ → ℂ)
      (Nat.choose_mul_factorial_mul_factorial (show m ≤ 2*m by omega))
    rw [show 2*m-m = m by omega] at h
    push_cast at h ⊢; rw [h]
  have hsq : (-1:ℂ)^m*(-1)^m = 1 := by rw [← mul_pow]; norm_num
  have hf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  rw [associatedP_nat_order_derivative m m hz, hev.iteratedDeriv_eq, iteratedDeriv_legendreP _ _ hz',
    show -(m:ℂ)+m = 0 by ring, regularizedGaussHG_zero_left _ _ hw, poch_neg_coe_nat,
    Nat.descFactorial_self, DLMF.OrthogonalPolynomials.poch_nat_succ_eq_choose_mul_factorial,
    show (1:ℂ)+m = (m:ℂ)+1 by ring, Gamma_nat_eq_factorial, hc, div_pow, show m+m = 2*m by ring]
  field_simp
  linear_combination ((2*m).choose m) * legendreBranchPower m z * hsq

/-- ferrersP order gt degree. -/
@[dlmf 14.7.E16]
theorem ferrersP_order_gt_degree (n m : ℕ) (h : n < m) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP n m x=0 := by
  have hm : 1 ≤ m := by omega
  have hc : 1-(m:ℂ)=-((m-1:ℕ):ℂ) := by rw [Nat.cast_sub hm]; push_cast; ring
  have hp : 1+(x:ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  unfold ferrersP
  rw [hc, regularizedGaussHG_neg_nat _ _ (m-1) (mem_cutPlane_of_one_add hp)]
  rw [Nat.sub_add_cancel hm, poch_neg_nat_eq_zero h]
  simp

/-- associatedP order gt degree. -/
@[dlmf 14.7.E16]
theorem associatedP_order_gt_degree (n m : ℕ) (h : n < m) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP n m z=0 := by
  have hm : 1 ≤ m := by omega
  have hc : 1-(m:ℂ)=-((m-1:ℕ):ℂ) := by rw [Nat.cast_sub hm]; push_cast; ring
  have hp := one_add_mem_slitPlane_of_sub_one hz
  unfold associatedP
  rw [hc, regularizedGaussHG_neg_nat _ _ (m-1) (mem_cutPlane_of_one_add hp)]
  rw [Nat.sub_add_cancel hm, poch_neg_nat_eq_zero h]
  simp

/-- `𝖶₁` is even in `x`. -/
lemma ferrersW1_neg (ν μ : ℂ) (x : ℝ) : ferrersW1 ν μ (-x) = ferrersW1 ν μ x := by
  simp [ferrersW1]

/-- `𝖶₂` is odd in `x`. -/
lemma ferrersW2_neg (ν μ : ℂ) (x : ℝ) : ferrersW2 ν μ (-x) = -ferrersW2 ν μ x := by
  simp [ferrersW2]

/-- Parity identities for the trigonometric coefficients at integer `ν+μ`. -/
theorem cos_sin_nat_half_pi (N : ℕ) :
    cos (N*π/2)*(1-(-1)^N) = 0 ∧ sin (N*π/2)*(1+(-1)^N) = 0 := by
  rcases Nat.even_or_odd' N with ⟨k, rfl | rfl⟩
  · have hs : sin (((2*k:ℕ):ℂ)*π/2) = 0 := by
      rw [show ((2*k:ℕ):ℂ)*π/2 = (k:ℂ)*π by push_cast; ring]; exact sin_nat_mul_pi k
    exact ⟨by simp [pow_mul], by rw [hs, zero_mul]⟩
  · have hc : cos (((2*k+1:ℕ):ℂ)*π/2) = 0 := by
      rw [show ((2*k+1:ℕ):ℂ)*π/2 = (k:ℂ)*π+π/2 by push_cast; ring, cos_add_pi_div_two,
        sin_nat_mul_pi, neg_zero]
    exact ⟨by rw [hc, zero_mul], by simp [pow_succ, pow_mul]⟩

/-- Reflection of `𝖯^μ_ν` when `ν+μ` is a nonnegative integer. -/
theorem ferrersP_neg_of_add_eq_nat {ν μ : ℂ} {N : ℕ} (hN : ν+μ = N) {x : ℝ}
    (hx : x ∈ Ioo (-1:ℝ) 1) : ferrersP ν μ (-x) = (-1)^N*ferrersP ν μ x := by
  have hreg : LegendreQRegular ν μ := fun k hk => by
    rw [hN] at hk
    have := congrArg re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hx' : -x ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  obtain ⟨h1, h2⟩ := cos_sin_nat_half_pi N
  rw [ferrersP_w1_w2 hreg hx', ferrersP_w1_w2 hreg hx, ferrersW1_neg, ferrersW2_neg, hN]
  linear_combination ferrersW1 ν μ x * h1 - ferrersW2 ν μ x * h2

/-- Reflection of `𝖰^μ_ν` when `ν+μ` is a nonnegative integer. -/
theorem ferrersQ_neg_of_add_eq_nat {ν μ : ℂ} {N : ℕ} (hN : ν+μ = N) (x : ℝ) :
    ferrersQ ν μ (-x) = (-1)^(N+1)*ferrersQ ν μ x := by
  obtain ⟨h1, h2⟩ := cos_sin_nat_half_pi N
  unfold ferrersQ
  rw [ferrersW1_neg, ferrersW2_neg, hN, pow_succ]
  linear_combination (-π/2*ferrersW1 ν μ x) * h2 - (π/2*ferrersW2 ν μ x) * h1

/-- ferrersP nat reflection. -/
@[dlmf 14.7.E17]
theorem ferrersP_nat_reflection (n m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP n m (-x)=(-1)^(n+m)*ferrersP n m x := by
  exact ferrersP_neg_of_add_eq_nat (by push_cast; ring) hx

/-- ferrersQ nat reflection 1. -/
@[dlmf 14.7.E18]
theorem ferrersQ_nat_reflection_1 (n m : ℕ) (h : m ≤ n) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ n (1*m) (-x)=(-1)^(n+m+1)*ferrersQ n (1*m) x := by
  exact ferrersQ_neg_of_add_eq_nat (by push_cast; ring) x

/-- ferrersQ nat reflection 2. -/
@[dlmf 14.7.E18]
theorem ferrersQ_nat_reflection_2 (n m : ℕ) (h : m ≤ n) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ n (-1*m) (-x)=(-1)^(n+m+1)*ferrersQ n (-1*m) x := by
  rw [ferrersQ_neg_of_add_eq_nat (N := n-m) (by push_cast [h]; ring) x]
  congr 1
  rw [show n+m+1 = (n-m+1)+2*m by omega, pow_add _ (n-m+1), pow_mul]
  norm_num

end DLMF.Legendre
