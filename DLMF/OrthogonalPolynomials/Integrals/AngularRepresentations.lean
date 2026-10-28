/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Series
public import DLMF.OrthogonalPolynomials.LegendreSingular
public import DLMF.OrthogonalPolynomials.Associated
public import DLMF.Confluent.IntegralRepresentations
public import Mathlib.MeasureTheory.Integral.Gamma
public import TauCeti.Analysis.SpecialFunctions.Hermite.Orthogonality
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Fourier.Basic
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

/-!
# Angular integral representations of classical polynomials

Classical norms, Rodrigues integration and the Dirichlet-Mehler angular representations.

Source references and common attribution are retained in
`DLMF.OrthogonalPolynomials.Integrals`.
This module uses results of the Tau Ceti contributors; see also `CREDITS.md`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter

open scoped Real Nat Topology

open DLMF.Hypergeometric

open DLMF.Confluent

open DLMF.Bessel

open DLMF.Gamma (Gamma_add_nat_eq_poch_mul_Gamma)

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-- `x^k e^{-x²}` is integrable. -/
theorem integrable_pow_mul_exp_neg_sq (k : ℕ) :
    Integrable fun x : ℝ => x ^ k * Real.exp (-(x ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos
    (s := (k : ℝ)) (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp [Real.rpow_natCast]

/-- Physicists' Hermite polynomials as real polynomials. -/
abbrev hermitePolyHR (n : ℕ) : ℝ[X] := (hermitePolyH n).map (Int.castRingHom ℝ)

/-- Evaluating the integer Hermite polynomial at a real point agrees with its real form. -/
theorem aeval_hermitePolyH_eq_eval (n : ℕ) (x : ℝ) :
    (aeval x (hermitePolyH n) : ℝ) = (hermitePolyHR n).eval x := by
  rw [aeval_def, hermitePolyHR, eval_map]
  congr 1

/-- The recursion `H_{n+1} = 2X H_n - H_n'` for the real Hermite polynomials. -/
theorem hermitePolyHR_succ (n : ℕ) :
    hermitePolyHR (n + 1) = 2 * X * hermitePolyHR n - derivative (hermitePolyHR n) := by
  simp [hermitePolyHR, Polynomial.map_sub, Polynomial.map_mul, derivative_map]

/-- Rodrigues step: the derivative of `H_n(x) e^{-x²}` is `-H_{n+1}(x) e^{-x²}`. -/
theorem hasDerivAt_hermite_gauss (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => (hermitePolyHR n).eval y * Real.exp (-(y ^ 2)))
      (-((hermitePolyHR (n + 1)).eval x * Real.exp (-(x ^ 2)))) x := by
  have hg : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2))) (Real.exp (-(x ^ 2)) * (-(2 * x))) x := by
    have := ((hasDerivAt_pow 2 x).neg).exp
    simpa using this
  have h := ((hermitePolyHR n).hasDerivAt x).mul hg
  convert h using 1
  rw [hermitePolyHR_succ, eval_sub, eval_mul, eval_mul, eval_X]
  simp
  ring

/-- Repeated integration by parts against the Hermite–Gaussian. -/
theorem integral_eval_mul_hermite_gauss (n : ℕ) :
    ∀ q : ℝ[X], ∫ x : ℝ, q.eval x * ((hermitePolyHR n).eval x * Real.exp (-(x ^ 2))) =
      ∫ x : ℝ, (derivative^[n] q).eval x * Real.exp (-(x ^ 2)) := by
  induction n with
  | zero => intro q; simp [hermitePolyHR]
  | succ n ih =>
    intro q
    have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := fun x => q.eval x) (u' := fun x => (derivative q).eval x)
      (v := fun x => (hermitePolyHR n).eval x * Real.exp (-(x ^ 2)))
      (v' := fun x => -((hermitePolyHR (n + 1)).eval x * Real.exp (-(x ^ 2))))
      (fun x _ => q.hasDerivAt x) (fun x _ => hasDerivAt_hermite_gauss n x)
      (by
        have := (TauCeti.integrable_eval_mul_exp_neg_sq (q * hermitePolyHR (n + 1))).neg
        refine this.congr (Eventually.of_forall fun x => ?_)
        simp only [Pi.mul_apply, eval_mul, Pi.neg_apply]; ring)
      (by
        have := TauCeti.integrable_eval_mul_exp_neg_sq (derivative q * hermitePolyHR n)
        refine this.congr (Eventually.of_forall fun x => ?_)
        simp only [Pi.mul_apply, eval_mul]; ring)
      (by
        have := TauCeti.integrable_eval_mul_exp_neg_sq (q * hermitePolyHR n)
        refine this.congr (Eventually.of_forall fun x => ?_)
        simp only [Pi.mul_apply, eval_mul]; ring)
    have h1 : ∫ x : ℝ, q.eval x * ((hermitePolyHR (n + 1)).eval x * Real.exp (-(x ^ 2))) =
        -∫ x : ℝ, q.eval x * -((hermitePolyHR (n + 1)).eval x * Real.exp (-(x ^ 2))) := by
      rw [← integral_neg]; congr 1; funext x; ring
    rw [h1, hibp, neg_neg, ih, Function.iterate_succ_apply]

/-- `H_n` has degree at most `n` and leading coefficient `2ⁿ`. -/
theorem hermitePolyHR_natDegree_coeff (n : ℕ) :
    (hermitePolyHR n).natDegree ≤ n ∧ (hermitePolyHR n).coeff n = 2 ^ n := by
  induction n with
  | zero => simp [hermitePolyHR]
  | succ n ih =>
    obtain ⟨hd, hc⟩ := ih
    rw [hermitePolyHR_succ]
    constructor
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_mul_le).trans ?_
        have : (2 * X : ℝ[X]).natDegree ≤ 1 := by
          rw [show (2 * X : ℝ[X]) = C 2 * X by rw [← map_ofNat C 2]]
          exact (natDegree_C_mul_le 2 X).trans natDegree_X_le
        omega
      · exact (natDegree_derivative_le _).trans (by omega)
    · rw [coeff_sub, show (2 * X : ℝ[X]) = C 2 * X by rw [← map_ofNat C 2], mul_assoc, coeff_C_mul, coeff_X_mul,
        hc, coeff_derivative, coeff_eq_zero_of_natDegree_lt (by omega)]
      ring

/-- Scaling Mathlib's Beta integral gives the power moments used in Laguerre
convolutions, including singular but integrable endpoints. -/
theorem integral_cpow_mul_sub_cpow {a b : ℂ} {x : ℝ}
    (ha : -1 < a.re) (hb : -1 < b.re) (hx : 0 < x) :
    (∫ t : ℝ in (0 : ℝ)..x, (t : ℂ) ^ a * ((x : ℂ) - t) ^ b) =
      (x : ℂ) ^ (a + b + 1) * (Gamma (a + 1) * Gamma (b + 1) / Gamma (a + b + 2)) := by
  let f : ℝ → ℂ := fun t => (t : ℂ) ^ a * ((x : ℂ) - t) ^ b
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hs := intervalIntegral.smul_integral_comp_mul_left f x (a := (0 : ℝ)) (b := 1)
  simp only [mul_zero, mul_one, Complex.real_smul] at hs
  have hpow : (x : ℂ) * (x : ℂ) ^ a * (x : ℂ) ^ b = (x : ℂ) ^ (a + b + 1) := by
    calc
      _ = (x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ a * (x : ℂ) ^ b := by rw [cpow_one]
      _ = _ := by
        rw [← cpow_add _ _ hx0, ← cpow_add _ _ hx0]
        congr 1
        ring
  have hi : (∫ t : ℝ in (0 : ℝ)..x, f t) =
      (x : ℂ) ^ (a + b + 1) * betaIntegral (a + 1) (b + 1) := by
    rw [← hs, betaIntegral, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    have hp : ((x : ℂ) * (1 - (t : ℂ))) ^ b = (x : ℂ) ^ b * (1 - (t : ℂ)) ^ b := by
      simpa only [ofReal_sub, ofReal_one] using
        mul_cpow_ofReal_nonneg hx.le (sub_nonneg.mpr ht.2.le) b
    dsimp [f]
    simp only [ofReal_mul, add_sub_cancel_right]
    rw [show (x : ℂ) - (x : ℂ) * t = (x : ℂ) * (1 - (t : ℂ)) by ring,
      mul_cpow_ofReal_nonneg hx.le ht.1.le, hp]
    linear_combination (t : ℂ) ^ a * (1 - (t : ℂ)) ^ b * hpow
  rw [betaIntegral_eq_Gamma_mul_div (a + 1) (b + 1) (by simp; linarith) (by simp; linarith)] at hi
  simpa only [show a + 1 + (b + 1) = a + b + 2 by ring] using hi

/-- Integrability of scaled Beta kernels, including integrable endpoint singularities. -/
theorem intervalIntegrable_cpow_mul_sub_cpow {a b : ℂ} {x : ℝ}
    (ha : -1 < a.re) (hb : -1 < b.re) (hx : 0 < x) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ a * ((x : ℂ) - t) ^ b) volume 0 x := by
  have hi := (betaIntegral_convergent (u := a + 1) (v := b + 1)
    (by simp; linarith) (by simp; linarith)).comp_mul_left (c := x⁻¹)
  simp only [add_sub_cancel_right, zero_div, one_div, inv_inv] at hi
  apply (hi.const_mul ((x : ℂ) ^ a * (x : ℂ) ^ b)).congr_ae
  apply (ae_restrict_mem measurableSet_Ioc).mono
  intro t ht
  simp only [min_eq_left hx.le, max_eq_right hx.le, Set.mem_Ioc] at ht
  dsimp only
  have ht0 : 0 ≤ t := ht.1.le
  have ht1 : 0 ≤ 1 - x⁻¹ * t := by
    rw [inv_mul_eq_div]; exact sub_nonneg.mpr ((div_le_one hx).mpr ht.2)
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have he : (x : ℂ) * ((x⁻¹ * t : ℝ) : ℂ) = t := by
    push_cast; field_simp
  have he' : (x : ℂ) * ((1 - x⁻¹ * t : ℝ) : ℂ) = (x : ℂ) - t := by
    push_cast; field_simp
  have hp := mul_cpow_ofReal_nonneg hx.le
    (mul_nonneg (inv_nonneg.mpr hx.le) ht0) a
  have hp' := mul_cpow_ofReal_nonneg hx.le ht1 b
  rw [he] at hp
  rw [he'] at hp'
  simp only [ofReal_sub, ofReal_one] at hp'
  rw [hp, hp']
  ring

/-- Integrability of the Jacobi weight on its orthogonality interval. -/
theorem intervalIntegrable_jacobi_weight {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    IntervalIntegrable (fun t : ℝ => (1 - (t : ℂ)) ^ (α : ℂ) *
      (1 + (t : ℂ)) ^ (β : ℂ)) volume (-1) 1 := by
  have hi := (intervalIntegrable_cpow_mul_sub_cpow (a := (β : ℂ)) (b := (α : ℂ))
    hβ hα (show (0 : ℝ) < 2 by norm_num)).comp_add_right 1
  norm_num only [zero_sub, sub_self, sub_add_cancel] at hi
  convert hi using 1
  · ext t
    push_cast
    rw [show (2 : ℂ) - ((t : ℂ) + 1) = 1 - t by ring]
    rw [add_comm (t : ℂ) 1]
    ring

/-- Integrability of Jacobi polynomial products against their weight. -/
theorem intervalIntegrable_jacobi_product {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (m n : ℕ) :
    IntervalIntegrable (fun t : ℝ => jacobiPolyP α β m t * jacobiPolyP α β n t *
      (1 - (t : ℂ)) ^ (α : ℂ) * (1 + (t : ℂ)) ^ (β : ℂ)) volume (-1) 1 := by
  have hP (k : ℕ) : Continuous (fun t : ℝ => jacobiPolyP α β k t) :=
    (continuous_iff_continuousAt.mpr fun z => (analyticAt_jacobiPolyP α β k z).continuousAt).comp
      continuous_ofReal
  convert (intervalIntegrable_jacobi_weight hα hβ).continuousOn_mul
    ((hP m).mul (hP n)).continuousOn using 1
  ext t
  simp only [Pi.mul_apply]
  ring

/-- Integration by parts reduces a Jacobi squared norm to a shifted norm. -/
theorem jacobi_norm_shift {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    4 * (n + 1 : ℂ) * (∫ t : ℝ in (-1 : ℝ)..1, jacobiPolyP α β (n + 1) t ^ 2 *
      (1 - (t : ℂ)) ^ (α : ℂ) * (1 + (t : ℂ)) ^ (β : ℂ)) =
    (n + α + β + 2 : ℂ) * (∫ t : ℝ in (-1 : ℝ)..1, jacobiPolyP (α + 1) (β + 1) n t ^ 2 *
      (1 - (t : ℂ)) ^ (α + 1 : ℂ) * (1 + (t : ℂ)) ^ (β + 1 : ℂ)) := by
  let w (a b : ℝ) (t : ℝ) : ℂ := (1 - (t : ℂ)) ^ (a : ℂ) * (1 + (t : ℂ)) ^ (b : ℂ)
  let g (t : ℝ) : ℂ := w (α + 1) (β + 1) t * jacobiPolyP (α + 1) (β + 1) n t
  let H (t : ℝ) : ℂ := g t * jacobiPolyP α β (n + 1) t
  let f (a b : ℝ) (k : ℕ) (t : ℝ) : ℂ := jacobiPolyP a b k t ^ 2 * w a b t
  have hP (a b : ℝ) (k : ℕ) : Continuous (fun t : ℝ => jacobiPolyP a b k t) :=
    (continuous_iff_continuousAt.mpr fun z => (analyticAt_jacobiPolyP a b k z).continuousAt).comp
      continuous_ofReal
  have hw : ContinuousOn (w (α + 1) (β + 1)) (Set.Icc (-1) 1) := by
    intro t ht
    dsimp only [w]
    apply ContinuousWithinAt.mul
    · exact ((continuousAt_cpow_const_of_re_pos (z := 1 - (t : ℂ))
        (Or.inl (by simp; linarith [ht.2]))
        (show 0 < ((α + 1 : ℝ) : ℂ).re by simp; linarith)).comp (x := t)
        (show ContinuousAt (fun u : ℝ => 1 - (u : ℂ)) t by fun_prop)).continuousWithinAt
    · exact ((continuousAt_cpow_const_of_re_pos (z := 1 + (t : ℂ))
        (Or.inl (by simp; linarith [ht.1]))
        (show 0 < ((β + 1 : ℝ) : ℂ).re by simp; linarith)).comp (x := t)
        (show ContinuousAt (fun u : ℝ => 1 + (u : ℂ)) t by fun_prop)).continuousWithinAt
  have hHcont : ContinuousOn H (Set.Icc (-1) 1) := by
    simpa only [H, g, ofReal_add, ofReal_one, Pi.mul_def] using
      (hw.mul (hP (α + 1) (β + 1) n).continuousOn).mul (hP α β (n + 1)).continuousOn
  have hd (t : ℝ) (ht : t ∈ Set.Ioo (-1) 1) : HasDerivAt H
      (-2 * (n + 1 : ℂ) * f α β (n + 1) t +
        (n + α + β + 2 : ℂ) / 2 * f (α + 1) (β + 1) n t) t := by
    have h1 : 1 - (t : ℂ) ∈ slitPlane := Or.inl (by simp; linarith [ht.2])
    have h2 : 1 + (t : ℂ) ∈ slitPlane := Or.inl (by simp; linarith [ht.1])
    have hA := ((((hasDerivAt_id' (t : ℂ)).const_sub 1).cpow_const
      (c := ((α + 1 : ℝ) : ℂ)) h1).comp_ofReal)
    have hB := ((((hasDerivAt_id' (t : ℂ)).const_add 1).cpow_const
      (c := ((β + 1 : ℝ) : ℂ)) h2).comp_ofReal)
    have hJ := (analyticAt_jacobiPolyP ((α + 1 : ℝ) : ℂ) ((β + 1 : ℝ) : ℂ) n
        (t : ℂ)).differentiableAt.hasDerivAt.comp_ofReal
    have hg : DifferentiableAt ℝ g t := by
      simpa only [g, w, ofReal_add, ofReal_one, Function.comp_apply, Pi.mul_def] using
        ((hA.mul hB).mul hJ).differentiableAt
    have he := jacobi_weighted_derivative (α := α + 1) (β := β + 1)
      (by linarith) (by linarith) n ht
    simp only [ofReal_add, ofReal_one, add_sub_cancel_right, add_sub_cancel_right] at he
    have he' : deriv g t = -2 * (n + 1 : ℂ) * w α β t * jacobiPolyP α β (n + 1) t := by
      simpa only [g, w, ofReal_add, ofReal_one, mul_assoc] using he
    have hJ' :=
        (analyticAt_jacobiPolyP (α : ℂ) β (n + 1) (t : ℂ)).differentiableAt.hasDerivAt.comp_ofReal
    rw [jacobi_derivative hα] at hJ'
    have h := hg.hasDerivAt.mul hJ'
    rw [he'] at h
    convert h using 1
    dsimp [H, g, f, w]
    push_cast
    ring
  have hf (a b : ℝ) (ha : -1 < a) (hb : -1 < b) (k : ℕ) :
      IntervalIntegrable (f a b k) volume (-1) 1 := by
    simpa only [f, w, pow_two, mul_assoc] using intervalIntegrable_jacobi_product ha hb k k
  have hi := ((hf α β hα hβ (n + 1)).const_mul (-2 * (n + 1 : ℂ))).add
    ((hf (α + 1) (β + 1) (by linarith) (by linarith) n).const_mul ((n + α + β + 2 : ℂ) / 2))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (-1 : ℝ) ≤ 1)
    hHcont hd hi
  have ha0 : ((α + 1 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have hb0 : ((β + 1 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  simp only [H, g, w, ofReal_one, ofReal_neg, sub_self, add_neg_cancel,
    zero_cpow ha0, zero_cpow hb0, zero_mul, mul_zero] at he
  rw [intervalIntegral.integral_add (f := fun t => -2 * (n + 1 : ℂ) * f α β (n + 1) t)
    (g := fun t => (n + α + β + 2 : ℂ) / 2 * f (α + 1) (β + 1) n t)
    ((hf α β hα hβ (n + 1)).const_mul _) ((hf (α + 1) (β + 1) (by linarith) (by linarith) n).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at he
  dsimp [f, w] at he
  push_cast at he ⊢
  simp only [mul_assoc] at he ⊢
  linear_combination -2 * he

/-- The Jacobi weight integral in a form regular throughout the orthogonality range. -/
theorem integral_jacobi_weight {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    (∫ t : ℝ in (-1 : ℝ)..1, (1 - (t : ℂ)) ^ (α : ℂ) * (1 + (t : ℂ)) ^ (β : ℂ)) =
      (2 : ℂ) ^ ((α : ℂ) + β + 1) * (Gamma ((α : ℂ) + 1) * Gamma ((β : ℂ) + 1) /
        Gamma ((α : ℂ) + β + 2)) := by
  have he := intervalIntegral.integral_comp_add_right
    (fun t : ℝ => (t : ℂ) ^ (β : ℂ) * ((2 : ℂ) - t) ^ (α : ℂ)) 1
    (a := (-1 : ℝ)) (b := 1)
  norm_num only [neg_add_cancel, one_add_one_eq_two] at he
  have hm := integral_cpow_mul_sub_cpow (a := (β : ℂ)) (b := (α : ℂ)) hβ hα
    (by norm_num : (0 : ℝ) < 2)
  norm_num only [ofReal_ofNat] at hm
  rw [hm] at he
  calc
    _ = ∫ t : ℝ in (-1 : ℝ)..1, ((t + 1 : ℝ) : ℂ) ^ (β : ℂ) *
        ((2 : ℂ) - ((t + 1 : ℝ) : ℂ)) ^ (α : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      push_cast
      rw [show (2 : ℂ) - ((t : ℂ) + 1) = 1 - t by ring, add_comm (t : ℂ) 1]
      ring
    _ = _ := by rw [he, add_comm (β : ℂ) α, mul_comm (Gamma ((β : ℂ) + 1))]

/-- Jacobi squared norms at all degrees, with a denominator regular at degree zero. -/
theorem jacobi_norm_all {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    (∫ t : ℝ in (-1 : ℝ)..1, jacobiPolyP α β n t ^ 2 *
      (1 - (t : ℂ)) ^ (α : ℂ) * (1 + (t : ℂ)) ^ (β : ℂ)) =
      (2 : ℂ) ^ ((α : ℂ) + β + 1) * Gamma ((α : ℂ) + n + 1) * Gamma ((β : ℂ) + n + 1) *
        poch ((α : ℂ) + β + n + 1) n /
          (n.factorial * Gamma ((α : ℂ) + β + 2 * n + 2)) := by
  induction n generalizing α β with
  | zero => simpa only [jacobiPolyP_zero, one_pow, one_mul, Nat.cast_zero, add_zero, mul_zero,
      poch_zero, mul_one, Nat.factorial_zero, Nat.cast_one, mul_div_assoc, mul_assoc] using integral_jacobi_weight hα hβ
  | succ n ih =>
    have h := jacobi_norm_shift hα hβ n
    have hih := ih (by linarith : -1 < α + 1) (by linarith : -1 < β + 1)
    push_cast at hih
    rw [hih] at h
    have hn : (4 : ℂ) * (n + 1 : ℂ) ≠ 0 :=
      mul_ne_zero (by norm_num) (by exact_mod_cast Nat.succ_ne_zero n)
    apply mul_left_cancel₀ hn
    rw [h]
    push_cast
    rw [poch_succ_left, Nat.factorial_succ]
    push_cast
    have hp : (2 : ℂ) ^ (((α : ℂ) + 1) + ((β : ℂ) + 1) + 1) =
        4 * (2 : ℂ) ^ ((α : ℂ) + β + 1) := by
      rw [show ((α : ℂ) + 1) + ((β : ℂ) + 1) + 1 = ((α : ℂ) + β + 1) + 2 by ring,
        cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
      norm_num
      ring
    rw [hp]
    have hG : Gamma ((α : ℂ) + β + 2 * n + 4) ≠ 0 := Gamma_ne_zero_of_re_pos (by
      simp; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    rw [show ((α : ℂ) + 1) + n + 1 = (α : ℂ) + (n + 1) + 1 by ring,
      show ((β : ℂ) + 1) + n + 1 = (β : ℂ) + (n + 1) + 1 by ring,
      show ((α : ℂ) + 1) + ((β : ℂ) + 1) + n + 1 = ((α : ℂ) + β + (n + 1) + 1) + 1 by ring,
      show ((α : ℂ) + 1) + ((β : ℂ) + 1) + 2 * n + 2 = (α : ℂ) + β + 2 * n + 4 by ring,
      show (α : ℂ) + β + 2 * (n + 1) + 2 = (α : ℂ) + β + 2 * n + 4 by ring]
    field_simp
    ring

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in (-1 : ℝ)..1,
jacobiPolyP α β (n + 1) x ^ 2 * (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) = (2 : ℂ) ^
((α : ℂ) + β + 1) * Gamma (n + (α : ℂ) + 2) * Gamma (n + (β : ℂ) + 2) / ((2 * n + α + β + 3) *
(n + 1).factorial * Gamma (n + (α : ℂ) + β + 2))`. -/
@[dlmf 18.3.T1]
theorem jacobi_norm {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1, jacobiPolyP α β (n + 1) x ^ 2 *
      (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) =
      (2 : ℂ) ^ ((α : ℂ) + β + 1) * Gamma (n + (α : ℂ) + 2) * Gamma (n + (β : ℂ) + 2) /
      ((2 * n + α + β + 3) * (n + 1).factorial * Gamma (n + (α : ℂ) + β + 2)) := by
  rw [jacobi_norm_all hα hβ]
  have hz : 0 < ((α : ℂ) + β + n + 2).re := by
    simp; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  have hg := Gamma_add_nat_div_Gamma_eq (n := n + 1) ((α : ℂ) + β + n + 2)
    (not_neg_nat_of_re_pos hz)
  change _ = poch ((α : ℂ) + β + n + 2) (n + 1) at hg
  push_cast at hg ⊢
  rw [show (α : ℂ) + β + (n + 1) + 1 = (α : ℂ) + β + n + 2 by ring, ← hg,
    show (α : ℂ) + β + n + 2 + (n + 1) = (α : ℂ) + β + 2 * n + 3 by ring,
    show (α : ℂ) + β + 2 * (n + 1) + 2 = ((α : ℂ) + β + 2 * n + 3) + 1 by ring,
    Gamma_add_one ((α : ℂ) + β + 2 * n + 3) (by
      have hp : 0 < ((α : ℂ) + β + 2 * n + 3).re := by
        simp; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
      intro he; rw [he] at hp; simp at hp)]
  have hG : Gamma ((α : ℂ) + β + 2 * n + 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
  rw [show (α : ℂ) + (n + 1) + 1 = n + (α : ℂ) + 2 by ring,
    show (β : ℂ) + (n + 1) + 1 = n + (β : ℂ) + 2 by ring,
    show (α : ℂ) + β + n + 2 = n + (α : ℂ) + β + 2 by ring,
    show (α : ℂ) + β + 2 * n + 3 = 2 * n + (α : ℂ) + β + 3 by ring] at *
  have hG' : Gamma ((n : ℂ) * 2 + α + β + 3) ≠ 0 := by
    convert hG using 1
    congr 1
    ring
  field_simp [hG']

/-- The squared Laguerre norm for the weight `x^α exp (-x)` on the positive ray. -/
@[dlmf 18.3.T1]
theorem laguerrePolyL_norm {α : ℝ} (hα : -1 < α) (n : ℕ) :
    ∫ x : ℝ in Set.Ioi 0, laguerrePolyL α n x ^ 2 * exp (-x) * (x : ℂ) ^ (α : ℂ) =
      Gamma (n + (α : ℂ) + 1) / n.factorial := by
  have heq : (fun x : ℝ => laguerrePolyL α n x ^ 2 * exp (-x) * (x : ℂ) ^ (α : ℂ)) =
      fun x : ℝ => ∑ k ∈ Finset.range (n + 1),
        (poch ((α : ℂ) + 1) n / n.factorial * kummerMCoeff (-(n : ℂ)) (α + 1) k) *
          (laguerrePolyL α n x * (x : ℂ) ^ k * (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ))) := by
    funext x
    rw [pow_two]
    conv_lhs => arg 1; arg 1; arg 1; rw [laguerrePolyL_eq_sum_coeff (α : ℂ) n]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq, integral_finsetSum _ (fun k _ =>
    (integrable_laguerrePolyL_mul_monomial hα n k).const_mul _)]
  simp_rw [MeasureTheory.integral_const_mul, integral_laguerrePolyL_mul_monomial hα]
  rw [Finset.sum_eq_single n]
  · have hc : ∀ j : ℕ, (α : ℂ) + 1 ≠ -j := not_neg_nat_of_re_pos (by
      simp only [add_re, ofReal_re, one_re]; linarith)
    have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hp := poch_ne_zero_of_not_neg_nat hc n
    change (poch ((α : ℂ) + 1) n / n.factorial *
      (poch (-(n : ℂ)) n / (poch ((α : ℂ) + 1) n * n.factorial))) *
      (Gamma ((α : ℂ) + n + 1) * poch (-(n : ℂ)) n / n.factorial) = _
    rw [poch_neg_coe_nat, Nat.descFactorial_self]
    have hs : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; simp
    rw [show (α : ℂ) + n + 1 = n + (α : ℂ) + 1 by ring]
    field_simp [hn, hp]
    linear_combination (Gamma (n + (α : ℂ) + 1)) * hs
  · intro k hk hkn
    have hlt : k < n := by have := Finset.mem_range.mp hk; omega
    rw [poch_neg_nat_eq_zero hlt]
    simp
  · simp

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ, (aeval x (hermitePolyH
m) : ℝ) * aeval x (hermitePolyH n) * Real.exp (-(x ^ 2)) = if m = n then Real.sqrt Real.pi * 2
^ n * n.factorial else 0`. -/
@[dlmf 18.3.T1]
theorem hermitePolyH_orthogonality (m n : ℕ) :
    ∫ x : ℝ, (aeval x (hermitePolyH m) : ℝ) * aeval x (hermitePolyH n) * Real.exp (-(x ^ 2)) =
      if m = n then Real.sqrt Real.pi * 2 ^ n * n.factorial else 0 := by
  have key : ∀ a b : ℕ, ∫ x : ℝ, (aeval x (hermitePolyH a) : ℝ) * aeval x (hermitePolyH b) *
      Real.exp (-(x ^ 2)) = ∫ x : ℝ, (derivative^[b] (hermitePolyHR a)).eval x *
        Real.exp (-(x ^ 2)) := fun a b => by
    rw [← integral_eval_mul_hermite_gauss b]
    congr 1; funext x
    rw [aeval_hermitePolyH_eq_eval, aeval_hermitePolyH_eq_eval]; ring
  have hzero : ∀ a b : ℕ, a < b → ∫ x : ℝ,
      (aeval x (hermitePolyH a) : ℝ) * aeval x (hermitePolyH b) *
      Real.exp (-(x ^ 2)) = 0 := fun a b hab => by
    rw [key, iterate_derivative_eq_zero ((hermitePolyHR_natDegree_coeff a).1.trans_lt hab)]
    simp
  split_ifs with hmn
  · subst hmn
    rw [key]
    obtain ⟨hd, hc⟩ := hermitePolyHR_natDegree_coeff m
    have hconst : derivative^[m] (hermitePolyHR m) = C ((m ! : ℝ) * 2 ^ m) := by
      rw [eq_C_of_natDegree_le_zero ((natDegree_iterate_derivative _ _).trans (by omega)),
        coeff_iterate_derivative, zero_add, Nat.descFactorial_self, hc, nsmul_eq_mul]
    simp only [hconst, eval_C]
    rw [integral_const_mul, show (fun x : ℝ => Real.exp (-(x ^ 2))) =
      fun x => Real.exp (-1 * x ^ 2) by funext x; ring_nf, integral_gaussian, div_one]
    ring
  · rcases Nat.lt_or_gt_of_ne hmn with h | h
    · exact hzero m n h
    · rw [← hzero n m h]
      congr 1; funext x; ring

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ, (aeval x (hermite m) :
ℝ) * aeval x (hermite n) * Real.exp (-(x ^ 2) / 2) = if m = n then Real.sqrt (2 * Real.pi) *
n.factorial else 0`. -/
@[dlmf 18.3.T1]
theorem hermite_orthogonality (m n : ℕ) :
    ∫ x : ℝ, (aeval x (hermite m) : ℝ) * aeval x (hermite n) * Real.exp (-(x ^ 2) / 2) =
      if m = n then Real.sqrt (2 * Real.pi) * n.factorial else 0 := by
  simpa only [neg_div, mul_comm] using
    TauCeti.integral_hermite_mul_hermite_mul_gaussian m n

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in (-1 : ℝ)..1,
legendrePolyP m x * legendrePolyP n x = if m = n then 2 / (2 * (n : ℂ) + 1) else 0`. -/
@[dlmf 18.3.T1]
theorem legendre_orthogonality (m n : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1, legendrePolyP m x * legendrePolyP n x =
      if m = n then 2 / (2 * (n : ℂ) + 1) else 0 := by
  let K : ℕ → ℕ → ℂ := fun i j => ∫ x : ℝ in (-1 : ℝ)..1, legendrePolyP i x * legendrePolyP j x
  let J : ℕ → ℕ → ℂ := fun i j => ∫ x : ℝ in (-1 : ℝ)..1,
    (x : ℂ) * legendrePolyP i x * legendrePolyP j x
  have hL (i : ℕ) : Continuous (fun x : ℝ => legendrePolyP i x) :=
    (continuous_iff_continuousAt.mpr fun z =>
      ((analyticOnNhd_jacobiPolyP 0 0 i) z (Set.mem_univ z)).continuousAt).comp continuous_ofReal
  have hK (i j : ℕ) : IntervalIntegrable
      (fun x : ℝ => legendrePolyP i x * legendrePolyP j x) volume (-1) 1 :=
    ((hL i).mul (hL j)).intervalIntegrable _ _
  have hJ (i j : ℕ) : IntervalIntegrable
      (fun x : ℝ => (x : ℂ) * legendrePolyP i x * legendrePolyP j x) volume (-1) 1 :=
    ((continuous_ofReal.mul (hL i)).mul (hL j)).intervalIntegrable _ _
  have hzero (i j : ℕ) (hij : i ≠ j) : K i j = 0 := by
    simpa only [K, legendrePolyP, ofReal_zero, cpow_zero, mul_one] using
      jacobiPolyP_orthogonal (α := 0) (β := 0) (by norm_num) (by norm_num) hij
  have hR (i j : ℕ) : (i + 2 : ℂ) * K (i + 2) j =
      (2 * i + 3 : ℂ) * J (i + 1) j - (i + 1 : ℂ) * K i j := by
    dsimp [K, J]
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ((hJ (i + 1) j).const_mul _) ((hK i j).const_mul _)]
    apply intervalIntegral.integral_congr
    intro x _
    linear_combination legendrePolyP j x * legendrePolyP_recurrence i x
  have hJsym (i j : ℕ) : J i j = J j i :=
    intervalIntegral.integral_congr fun x _ => by ring
  have hnorm : ∀ i : ℕ, K i i = 2 / (2 * (i : ℂ) + 1) := by
    intro i
    induction i using Nat.twoStepInduction with
    | zero => norm_num [K, legendrePolyP_zero]
    | one =>
      have h := hR 0 0
      rw [hzero 2 0 (by omega)] at h
      have h00 : K 0 0 = 2 := by norm_num [K, legendrePolyP_zero]
      have h10 : J 1 0 = K 1 1 := by simp [J, K, legendrePolyP_zero]
      rw [h00, h10] at h
      norm_num at h ⊢
      linear_combination -h / 3
    | more i _hi hi1 =>
      have h₁ := hR i (i + 2)
      have h₂ := hR (i + 1) (i + 1)
      rw [hzero i (i + 2) (by omega), mul_zero, sub_zero] at h₁
      rw [hzero (i + 1 + 2) (i + 1) (by omega), mul_zero, hi1] at h₂
      have hsym : J (i + 1 + 1) (i + 1) = J (i + 1) (i + 2) := by
        simpa only [Nat.add_assoc] using hJsym (i + 2) (i + 1)
      rw [hsym] at h₂
      have hd : (2 * (i + 2 : ℂ) + 1) ≠ 0 := by
        have hp : 0 < (2 * (i + 2 : ℂ) + 1).re := by simp; positivity
        intro h; rw [h] at hp; simpa using hp
      have hd1 : (2 * (i + 1 : ℂ) + 1) ≠ 0 := by
        have hp : 0 < (2 * (i + 1 : ℂ) + 1).re := by simp; positivity
        intro h; rw [h] at hp; simpa using hp
      have hn : (i + 2 : ℂ) ≠ 0 := by
        have hp : 0 < (i + 2 : ℂ).re := by simp; positivity
        intro h; rw [h] at hp; simpa using hp
      push_cast at h₁ h₂ ⊢
      apply (eq_div_iff hd).mpr
      have h₂' : (2 * (i : ℂ) + 5) * J (i + 1) (i + 2) *
          (2 * (i : ℂ) + 3) = 2 * ((i : ℂ) + 2) := by
        have he : (2 * (i : ℂ) + 5) * J (i + 1) (i + 2) =
            (2 * ((i : ℂ) + 2)) / (2 * (i : ℂ) + 3) := by
          linear_combination -h₂
        exact (eq_div_iff (by convert hd1 using 1; ring)).mp he
      apply mul_left_cancel₀ hn
      linear_combination (2 * (i : ℂ) + 5) * h₁ + h₂'
  split_ifs with hmn
  · subst m
    exact hnorm n
  · exact hzero m n hmn

/-- Duplication converts the symmetric Jacobi normalization to the Gegenbauer one. -/
private lemma ultrasphPoly_norm_constant {lam : ℝ} (hlam : 0 < lam) :
    (2 : ℂ) ^ (2 * (lam : ℂ)) * Gamma ((lam : ℂ) + 1 / 2) ^ 2 / Gamma (2 * (lam : ℂ)) ^ 2 =
      2 * (2 : ℂ) ^ (1 - 2 * (lam : ℂ)) * Real.pi / Gamma (lam : ℂ) ^ 2 := by
  have hG : Gamma (lam : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos hlam
  have hG2 : Gamma (2 * (lam : ℂ)) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hd := Gamma_mul_Gamma_add_half (lam : ℂ)
  have hh : Gamma ((lam : ℂ) + 1 / 2) =
      Gamma (2 * (lam : ℂ)) * (2 : ℂ) ^ (1 - 2 * (lam : ℂ)) * Real.sqrt Real.pi / Gamma (lam : ℂ) := by
    apply (eq_div_iff hG).mpr
    linear_combination hd
  have hs : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hp' : (2 : ℂ) ^ (2 * (lam : ℂ)) * (2 : ℂ) ^ (1 - 2 * (lam : ℂ)) = 2 := by
    rw [← cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0),
      show 2 * (lam : ℂ) + (1 - 2 * (lam : ℂ)) = 1 by ring, cpow_one]
  rw [hh, div_pow, mul_pow, mul_pow, hs]
  field_simp
  exact hp'

/-- Gegenbauer squared norms, including degree zero. -/
theorem ultrasphPoly_norm {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    (∫ t : ℝ in (-1 : ℝ)..1, ultrasphPoly lam n t ^ 2 *
      (1 - (t : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2)) =
      (2 : ℂ) ^ (1 - 2 * (lam : ℂ)) * Real.pi * Gamma (n + 2 * (lam : ℂ)) /
        ((n + lam) * Gamma (lam : ℂ) ^ 2 * n.factorial) := by
  have ha : -1 < lam - 1 / 2 := by linarith
  have hpoch (k : ℕ) : poch ((lam : ℂ) + 1 / 2) k ≠ 0 :=
    poch_ne_zero_of_re_pos (by simp; linarith) k
  have he : (∫ t : ℝ in (-1 : ℝ)..1, ultrasphPoly lam n t ^ 2 *
      (1 - (t : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2)) =
      (poch (2 * (lam : ℂ)) n / poch ((lam : ℂ) + 1 / 2) n) ^ 2 *
        (∫ t : ℝ in (-1 : ℝ)..1,
            jacobiPolyP ((lam - 1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) n t ^ 2 *
          (1 - (t : ℂ)) ^ ((lam - 1 / 2 : ℝ) : ℂ) * (1 + (t : ℂ)) ^ ((lam - 1 / 2 : ℝ) : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    dsimp only
    rw [ultrasphPoly_eq_jacobiPolyP n _ (hpoch n), mul_pow]
    have hp := mul_cpow_ofReal_nonneg (show 0 ≤ 1 - t by linarith [ht.2])
      (show 0 ≤ 1 + t by linarith [ht.1]) ((lam : ℂ) - 1 / 2)
    push_cast at hp ⊢
    rw [show (1 - (t : ℂ)) * (1 + t) = 1 - (t : ℂ) ^ 2 by ring] at hp
    rw [hp]
    ring
  rw [he, jacobi_norm_all ha ha]
  push_cast
  have h1 := Gamma_add_nat_div_Gamma_eq (n := n) ((lam : ℂ) + 1 / 2)
    (not_neg_nat_of_re_pos (by simp; linarith))
  change _ = poch ((lam : ℂ) + 1 / 2) n at h1
  have h2 := Gamma_add_nat_div_Gamma_eq (n := n) (2 * (lam : ℂ))
    (not_neg_nat_of_re_pos (by simp; linarith))
  change _ = poch (2 * (lam : ℂ)) n at h2
  have h3 := Gamma_add_nat_div_Gamma_eq (n := n) (2 * (lam : ℂ) + n)
    (not_neg_nat_of_re_pos (by simp; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith))
  change _ = poch (2 * (lam : ℂ) + n) n at h3
  have hG (k : ℕ) : Gamma (2 * (lam : ℂ) + k) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp; have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
  have hGh : Gamma ((lam : ℂ) + 1 / 2 + n) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
  have hGh0 : Gamma ((lam : ℂ) + 1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hG0 : Gamma (2 * (lam : ℂ)) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  rw [show ((lam : ℂ) - 1 / 2) + ((lam : ℂ) - 1 / 2) + 1 = 2 * (lam : ℂ) by ring,
    show ((lam : ℂ) - 1 / 2) + n + 1 = (lam : ℂ) + 1 / 2 + n by ring,
    show ((lam : ℂ) - 1 / 2) + ((lam : ℂ) - 1 / 2) + n + 1 = 2 * (lam : ℂ) + n by ring,
    show ((lam : ℂ) - 1 / 2) + ((lam : ℂ) - 1 / 2) + 2 * n + 2 =
      (2 * (lam : ℂ) + (2 * n : ℕ)) + 1 by push_cast; ring,
    ← h1, ← h2, ← h3,
    show 2 * (lam : ℂ) + n + n = 2 * (lam : ℂ) + (2 * n : ℕ) by push_cast; ring,
    Gamma_add_one (2 * (lam : ℂ) + (2 * n : ℕ)) (by
      have hp : 0 < (2 * (lam : ℂ) + (2 * n : ℕ)).re := by
        simp; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
      intro h; rw [h] at hp; simp at hp)]
  have hconst := ultrasphPoly_norm_constant hlam
  have halgebra : (Gamma (2 * (lam : ℂ) + n) / Gamma (2 * (lam : ℂ)) /
      (Gamma ((lam : ℂ) + 1 / 2 + n) / Gamma ((lam : ℂ) + 1 / 2))) ^ 2 *
        ((2 : ℂ) ^ (2 * (lam : ℂ)) * Gamma ((lam : ℂ) + 1 / 2 + n) *
          Gamma ((lam : ℂ) + 1 / 2 + n) *
          (Gamma (2 * (lam : ℂ) + (2 * n : ℕ)) / Gamma (2 * (lam : ℂ) + n)) /
          (n.factorial * ((2 * (lam : ℂ) + (2 * n : ℕ)) * Gamma (2 * (lam : ℂ) + (2 * n : ℕ))))) =
      ((2 : ℂ) ^ (2 * (lam : ℂ)) * Gamma ((lam : ℂ) + 1 / 2) ^ 2 / Gamma (2 * (lam : ℂ)) ^ 2) *
        Gamma (2 * (lam : ℂ) + n) / ((2 * (lam : ℂ) + (2 * n : ℕ)) * n.factorial) := by
    have hfield (A B C D E P q r : ℂ) (hA : A ≠ 0) (hB : B ≠ 0)
        (hC : C ≠ 0) (hD : D ≠ 0) (hE : E ≠ 0) :
        (A / B / (C / D)) ^ 2 * (P * C * C * (E / A) / (r * (q * E))) =
          (P * D ^ 2 / B ^ 2) * A / (q * r) := by
      field_simp
    exact hfield _ _ _ _ _ _ _ _ (hG n) hG0 hGh hGh0 (hG (2 * n))
  rw [halgebra, hconst]
  rw [show (2 * (lam : ℂ) + (2 * n : ℕ)) = 2 * ((n : ℂ) + lam) by push_cast; ring,
    add_comm (2 * (lam : ℂ)) (n : ℂ)]
  field_simp

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ in (-1 : ℝ)..1,
ultrasphPoly lam m x * ultrasphPoly lam n x * (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2) = if m =
n then (2 : ℂ) ^ (1 - 2 * (lam : ℂ)) * Real.pi * Gamma (n + 2 * (lam : ℂ)) / ((n + lam) *
Gamma (lam : ℂ) ^ 2 * n.factorial) else 0`. -/
@[dlmf 18.3.T1]
theorem ultrasphPoly_orthogonality {lam : ℝ} (hlam : 0 < lam) (m n : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1, ultrasphPoly lam m x * ultrasphPoly lam n x *
      (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2) =
      if m = n then (2 : ℂ) ^ (1 - 2 * (lam : ℂ)) * Real.pi * Gamma (n + 2 * (lam : ℂ)) /
        ((n + lam) * Gamma (lam : ℂ) ^ 2 * n.factorial) else 0 := by
  split_ifs with hmn
  · subst m
    simpa only [pow_two] using ultrasphPoly_norm hlam n
  · have ha : -1 < lam - 1 / 2 := by linarith
    have hpoch (k : ℕ) : poch ((lam : ℂ) + 1 / 2) k ≠ 0 :=
      poch_ne_zero_of_re_pos (by simp; linarith) k
    have he : (∫ x : ℝ in (-1 : ℝ)..1, ultrasphPoly lam m x * ultrasphPoly lam n x *
        (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2)) =
        (poch (2 * (lam : ℂ)) m / poch ((lam : ℂ) + 1 / 2) m *
          (poch (2 * (lam : ℂ)) n / poch ((lam : ℂ) + 1 / 2) n)) *
          (∫ t : ℝ in (-1 : ℝ)..1, jacobiPolyP ((lam - 1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) m t *
            jacobiPolyP ((lam - 1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) n t *
            (1 - (t : ℂ)) ^ ((lam - 1 / 2 : ℝ) : ℂ) * (1 + (t : ℂ)) ^ ((lam - 1 / 2 : ℝ) : ℂ)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      dsimp only
      rw [ultrasphPoly_eq_jacobiPolyP m _ (hpoch m), ultrasphPoly_eq_jacobiPolyP n _ (hpoch n)]
      have hp := mul_cpow_ofReal_nonneg (show 0 ≤ 1 - t by linarith [ht.2])
        (show 0 ≤ 1 + t by linarith [ht.1]) ((lam : ℂ) - 1 / 2)
      push_cast at hp ⊢
      rw [show (1 - (t : ℂ)) * (1 + t) = 1 - (t : ℂ) ^ 2 by ring] at hp
      rw [hp]
      ring
    rw [he, jacobiPolyP_orthogonal ha ha hmn, mul_zero]

/-- Repeated differentiation of the Jacobi weight, using the proved weighted
derivative identity on the open interval. -/
theorem iteratedDeriv_jacobi_weight {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    iteratedDeriv n (fun t : ℝ => (1 - (t : ℂ)) ^ (α + n : ℂ) *
      (1 + (t : ℂ)) ^ (β + n : ℂ)) x =
        (-2 : ℂ) ^ n * n.factorial * (1 - (x : ℂ)) ^ (α : ℂ) *
          (1 + (x : ℂ)) ^ (β : ℂ) * jacobiPolyP α β n x := by
  induction n generalizing α β x with
  | zero => simp
  | succ n ih =>
    have heq : iteratedDeriv n (fun t : ℝ => (1 - (t : ℂ)) ^ ((α : ℂ) + ((n + 1 : ℕ) : ℂ)) *
        (1 + (t : ℂ)) ^ ((β : ℂ) + ((n + 1 : ℕ) : ℂ))) =ᶠ[𝓝 x]
        (fun t : ℝ => ((-2 : ℂ) ^ n * n.factorial) *
          ((1 - (t : ℂ)) ^ (α + 1 : ℂ) * (1 + (t : ℂ)) ^ (β + 1 : ℂ) *
            jacobiPolyP (α + 1) (β + 1) n t)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
      have h := ih (α := α + 1) (β := β + 1) (by linarith) (by linarith) ht
      push_cast at h
      simp only [Nat.cast_add, Nat.cast_one]
      rw [show (α : ℂ) + ((n : ℂ) + 1) = (α : ℂ) + 1 + n by ring,
        show (β : ℂ) + ((n : ℂ) + 1) = (β : ℂ) + 1 + n by ring]
      simpa only [mul_assoc] using h
    rw [iteratedDeriv_succ, heq.deriv_eq, deriv_const_mul_field]
    have hD := jacobi_weighted_derivative (by linarith : 0 < α + 1)
      (by linarith : 0 < β + 1) n hx
    push_cast at hD
    rw [hD]
    simp only [Nat.factorial_succ, pow_succ, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
      add_sub_cancel_right]
    ring

/-- Repeated differentiation of the Laguerre weight on the positive half-line. -/
theorem iteratedDeriv_laguerrePolyL_weight {α : ℝ} (hα : -1 < α) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (fun t : ℝ => exp (-(t : ℂ)) * (t : ℂ) ^ (α + n : ℂ)) x =
      (n.factorial : ℂ) * exp (-(x : ℂ)) * (x : ℂ) ^ (α : ℂ) * laguerrePolyL α n x := by
  induction n generalizing α x with
  | zero => simp
  | succ n ih =>
    have heq : iteratedDeriv n (fun t : ℝ => exp (-(t : ℂ)) * (t : ℂ) ^ ((α : ℂ) + ((n + 1 : ℕ) : ℂ)))
        =ᶠ[𝓝 x] (fun t : ℝ => (n.factorial : ℂ) *
          (exp (-(t : ℂ)) * (t : ℂ) ^ (α + 1 : ℂ) * laguerrePolyL (α + 1) n t)) := by
      filter_upwards [Ioi_mem_nhds hx] with t ht
      have h := ih (α := α + 1) (by linarith) ht
      push_cast at h
      simp only [Nat.cast_add, Nat.cast_one]
      rw [show (α : ℂ) + ((n : ℂ) + 1) = (α : ℂ) + 1 + n by ring]
      simpa only [mul_assoc] using h
    rw [iteratedDeriv_succ, heq.deriv_eq, deriv_const_mul_field]
    have hD := laguerrePolyL_weighted_derivative (by linarith : 0 < α + 1) n hx
    push_cast at hD
    rw [hD]
    simp only [Nat.factorial_succ, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
      add_sub_cancel_right]
    ring

/-- Identity under the stated parameter and domain assumptions: `jacobiPolyP α β n x = (deriv^[n]
(fun t : ℝ => (1 - t) ^ (α + n) * (1 + t) ^ (β + n)) x : ℝ) / ((-2 : ℂ) ^ n * n.factorial * (1
- x : ℂ) ^ (α : ℂ) * (1 + x : ℂ) ^ (β : ℂ))`. -/
@[dlmf 18.5.E5]
theorem jacobi_rodrigues {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    jacobiPolyP α β n x = (deriv^[n] (fun t : ℝ => (1 - t) ^ (α + n) * (1 + t) ^ (β + n)) x : ℝ) /
      ((-2 : ℂ) ^ n * n.factorial * (1 - x : ℂ) ^ (α : ℂ) * (1 + x : ℂ) ^ (β : ℂ)) := by
  let f : ℝ → ℝ := fun t => (1 - t) ^ (α + n) * (1 + t) ^ (β + n)
  have hf : ContDiffAt ℝ n f x := by
    exact ((contDiffAt_const.sub contDiffAt_id).rpow_const_of_ne (by dsimp; linarith [hx.2])).mul
      ((contDiffAt_const.add contDiffAt_id).rpow_const_of_ne (by dsimp; linarith [hx.1]))
  have heq : (fun t : ℝ => f t • (1 : ℂ)) =ᶠ[𝓝 x]
      (fun t : ℝ => (1 - (t : ℂ)) ^ (α + n : ℂ) * (1 + (t : ℂ)) ^ (β + n : ℂ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    simp only [f, Complex.real_smul, mul_one, ofReal_mul]
    rw [ofReal_cpow (by linarith [ht.2]), ofReal_cpow (by linarith [ht.1])]
    push_cast
    rfl
  have hd := heq.iteratedDeriv_eq n
  rw [iteratedDeriv_smul_const hf, iteratedDeriv_jacobi_weight hα hβ n hx,
    Complex.real_smul, mul_one, iteratedDeriv_eq_iterate] at hd
  rw [hd]
  have h1 : 1 - (x : ℂ) ≠ 0 := by exact_mod_cast (show 1 - x ≠ 0 by linarith [hx.2])
  have h2 : 1 + (x : ℂ) ≠ 0 := by exact_mod_cast (show 1 + x ≠ 0 by linarith [hx.1])
  field_simp [cpow_ne_zero_iff.mpr (Or.inl h1), cpow_ne_zero_iff.mpr (Or.inl h2),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]

/-- Identity under the stated parameter and domain assumptions: `laguerrePolyL α n x = (Real.exp x
* x ^ (-α) * deriv^[n] (fun t : ℝ => Real.exp (-t) * t ^ (n + α)) x / n.factorial : ℝ)`. -/
@[dlmf 18.5.E5]
theorem laguerrePolyL_rodrigues {α : ℝ} (hα : -1 < α) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    laguerrePolyL α n x = (Real.exp x * x ^ (-α) *
      deriv^[n] (fun t : ℝ => Real.exp (-t) * t ^ (n + α)) x / n.factorial : ℝ) := by
  let f : ℝ → ℝ := fun t => Real.exp (-t) * t ^ (n + α)
  have hf : ContDiffAt ℝ n f x :=
    (by fun_prop : ContDiffAt ℝ n (fun t : ℝ => Real.exp (-t)) x).mul
      (Real.contDiffAt_rpow_const_of_ne hx.ne')
  have heq : (fun t : ℝ => f t • (1 : ℂ)) =ᶠ[𝓝 x]
      (fun t : ℝ => exp (-(t : ℂ)) * (t : ℂ) ^ (α + n : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    simp only [f, Complex.real_smul, mul_one, ofReal_mul, ofReal_exp, ofReal_neg]
    rw [ofReal_cpow ht.le]
    push_cast
    congr 2
    ring
  have hd := heq.iteratedDeriv_eq n
  rw [iteratedDeriv_smul_const hf, iteratedDeriv_laguerrePolyL_weight hα n hx,
    Complex.real_smul, mul_one, iteratedDeriv_eq_iterate] at hd
  push_cast
  rw [hd, ofReal_cpow hx.le, ofReal_neg, exp_neg, cpow_neg]
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  field_simp [cpow_ne_zero_iff.mpr (Or.inl hx0), Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]

/-- **Rodrigues' formula for Gegenbauer polynomials** (DLMF 18.5.5, Temme §6.3): for `λ > -1/2`
and `-1 < x < 1`,
`C_n^λ(x) = (2λ)_n / ((-2)ⁿ n! (λ+1/2)_n) · (1-x²)^{1/2-λ} dⁿ/dxⁿ (1-x²)^{n+λ-1/2}`. -/
theorem ultrasphPoly_rodrigues {lam : ℝ} (hlam : -1 / 2 < lam) (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1) 1) :
    ultrasphPoly lam n x = poch (2 * lam) n / ((-2 : ℂ) ^ n * n.factorial * poch (lam + 1 / 2) n) *
      ((1 - x ^ 2) ^ (1 / 2 - lam) *
        deriv^[n] (fun t : ℝ => (1 - t ^ 2) ^ (n + lam - 1 / 2)) x : ℝ) := by
  have hα : -1 < lam - 1 / 2 := by linarith
  have hp : poch ((lam : ℂ) + 1 / 2) n ≠ 0 := poch_ne_zero_of_not_neg_nat
    (not_neg_nat_of_re_pos (by simp; linarith)) n
  have hJ := jacobi_rodrigues hα hα n hx
  rw [ultrasphPoly_eq_jacobiPolyP n x hp]
  push_cast at hJ ⊢
  rw [hJ]
  -- the two weights agree near `x`
  have hev : (fun t : ℝ => (1 - t) ^ (lam - 1 / 2 + n) * (1 + t) ^ (lam - 1 / 2 + n)) =ᶠ[𝓝 x]
      fun t : ℝ => (1 - t ^ 2) ^ (n + lam - 1 / 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    rw [← Real.mul_rpow (by linarith [ht.2]) (by linarith [ht.1])]
    congr 1 <;> ring
  rw [← iteratedDeriv_eq_iterate, ← iteratedDeriv_eq_iterate, hev.iteratedDeriv_eq n]
  have h1 : 0 < 1 - x := by linarith [hx.2]
  have h2 : 0 < 1 + x := by linarith [hx.1]
  have hw : ((1 - x : ℂ) ^ ((lam : ℂ) - 1 / 2)) * ((1 + x : ℂ) ^ ((lam : ℂ) - 1 / 2)) =
      (((1 - x ^ 2) ^ (lam - 1 / 2) : ℝ) : ℂ) := by
    rw [show (1 - x ^ 2) = (1 - x) * (1 + x) by ring, Real.mul_rpow h1.le h2.le]
    push_cast
    rw [Complex.ofReal_cpow h1.le, Complex.ofReal_cpow h2.le]
    push_cast; ring
  have hw' : ((1 - x ^ 2) ^ (1 / 2 - lam) : ℝ) * (1 - x ^ 2) ^ (lam - 1 / 2) = 1 := by
    rw [← Real.rpow_add (by nlinarith)]; norm_num
  have hw0 : (((1 - x ^ 2) ^ (lam - 1 / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by nlinarith) _).ne'
  have hwC : (((1 - x ^ 2) ^ (1 / 2 - lam) : ℝ) : ℂ) = ((((1 - x ^ 2) ^ (lam - 1 / 2) : ℝ) : ℂ))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← Complex.ofReal_mul, hw']; simp
  rw [mul_assoc ((-2 : ℂ) ^ n * n.factorial), hw, hwC]
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp

/-- **Rodrigues' formula for Legendre polynomials** (DLMF 18.5.5, Temme (6.20)):
`P_n(x) = (2ⁿ n!)⁻¹ dⁿ/dxⁿ (x² - 1)ⁿ` for `-1 < x < 1`. -/
theorem legendre_rodrigues (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    legendrePolyP n x = ((2 ^ n * n.factorial : ℝ)⁻¹ *
      deriv^[n] (fun t : ℝ => (t ^ 2 - 1) ^ n) x : ℝ) := by
  have h := ultrasphPoly_rodrigues (lam := 1 / 2) (by norm_num) n hx
  rw [show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by norm_num, ← legendre_eq_ultrasphPoly] at h
  rw [h]
  have hfun : (fun t : ℝ => (1 - t ^ 2) ^ ((n : ℝ) + 1 / 2 - 1 / 2)) =
      fun t : ℝ => (-1) ^ n * (t ^ 2 - 1) ^ n := by
    funext t
    rw [show (n : ℝ) + 1 / 2 - 1 / 2 = (n : ℕ) by ring, Real.rpow_natCast, ← mul_pow]
    ring_nf
  rw [hfun, ← iteratedDeriv_eq_iterate, ← iteratedDeriv_eq_iterate,
    iteratedDeriv_const_mul_field]
  simp only [show (1 / 2 : ℝ) - 1 / 2 = 0 by norm_num, Real.rpow_zero, one_mul]
  have hp1 : poch (2 * (1 / 2 : ℂ)) n = n.factorial := by
    rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num, poch_nat_one]
  have hp2 : poch ((1 / 2 : ℂ) + 1 / 2) n = n.factorial := by
    rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, poch_nat_one]
  rw [hp1, hp2]
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  push_cast
  rw [show (-2 : ℂ) ^ n = (-1) ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
  have h1 : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  field_simp

/-- The substitution `ψ = 2 arcsin(k √t)`, `k = sin(θ/2)`, maps `(0, 1)` onto `(0, θ)`. -/
private lemma dirM_subst {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) (F : ℝ → ℂ) :
    (∫ ψ : ℝ in (0 : ℝ)..θ, F ψ) = ∫ t : ℝ in (0 : ℝ)..1,
      ((Real.sin (θ / 2) / (Real.sqrt t * Real.sqrt (1 - Real.sin (θ / 2) ^ 2 * t)) : ℝ) : ℂ) *
        F (2 * Real.arcsin (Real.sin (θ / 2) * Real.sqrt t)) := by
  set k := Real.sin (θ / 2) with hk
  have hk0 : 0 < k := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hk1 : k < 1 := by
    rw [hk, ← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) le_rfl (by linarith)
  set g : ℝ → ℝ := fun t => 2 * Real.arcsin (k * Real.sqrt t) with hg
  set g' : ℝ → ℝ := fun t => k / (Real.sqrt t * Real.sqrt (1 - k ^ 2 * t)) with hg'
  have hs : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 < k * Real.sqrt t ∧ k * Real.sqrt t < k := by
    intro t ht
    have h1 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht.1
    have h2 : Real.sqrt t < 1 := by rw [Real.sqrt_lt' one_pos]; simpa using ht.2
    exact ⟨mul_pos hk0 h1, by nlinarith⟩
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivWithinAt g (g' t) (Set.Ioo 0 1) t := by
    intro t ht
    obtain ⟨h1, h2⟩ := hs t ht
    have hsq := (Real.hasDerivAt_sqrt ht.1.ne').const_mul k
    have ha := (Real.hasDerivAt_arcsin (x := k * Real.sqrt t) (by linarith)
      (by linarith)).comp t hsq
    have := (ha.const_mul 2).hasDerivWithinAt (s := Set.Ioo 0 1)
    convert this using 1
    · rfl
    have hst : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.1.le
    have : (k * Real.sqrt t) ^ 2 = k ^ 2 * t := by rw [mul_pow, hst]
    rw [this]
    have hp : 0 < Real.sqrt (1 - k ^ 2 * t) := Real.sqrt_pos.mpr (by nlinarith [ht.2])
    have hq : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht.1
    simp only [hg']
    field_simp
  have hinj : Set.InjOn g (Set.Ioo 0 1) := by
    intro t1 ht1 t2 ht2 h
    simp only [hg] at h
    have h' : Real.arcsin (k * Real.sqrt t1) = Real.arcsin (k * Real.sqrt t2) := by linarith
    obtain ⟨a1, a2⟩ := hs t1 ht1
    obtain ⟨b1, b2⟩ := hs t2 ht2
    have := (Real.arcsin_inj (by linarith) (by linarith) (by linarith) (by linarith)).mp h'
    have hsq : Real.sqrt t1 = Real.sqrt t2 := mul_left_cancel₀ hk0.ne' this
    exact (Real.sqrt_inj ht1.1.le ht2.1.le).mp hsq
  have himg : g '' Set.Ioo 0 1 = Set.Ioo 0 θ := by
    ext ψ
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨h1, h2⟩ := hs t ht
      have hA : Real.arcsin k = θ / 2 := by
        rw [hk]; exact Real.arcsin_sin (by linarith) (by linarith)
      constructor
      · simp only [hg]; have := Real.arcsin_pos.mpr h1; linarith
      · simp only [hg]
        have := Real.arcsin_lt_arcsin (by linarith) h2 hk1.le
        linarith
    · rintro ⟨h1, h2⟩
      have hs0 : 0 < Real.sin (ψ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have hsk : Real.sin (ψ / 2) < k :=
        Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
      refine ⟨(Real.sin (ψ / 2) / k) ^ 2, ⟨by positivity, ?_⟩, ?_⟩
      · rw [div_pow]; rw [div_lt_one (by positivity)]
        exact pow_lt_pow_left₀ hsk hs0.le two_ne_zero
      · simp only [hg]
        rw [Real.sqrt_sq (by positivity), mul_div_cancel₀ _ hk0.ne',
          Real.arcsin_sin (by linarith) (by linarith)]
        ring
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj F
  rw [himg] at he
  rw [intervalIntegral.integral_of_le hθ.le, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, he]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have hq : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht.1
  have hp : 0 < Real.sqrt (1 - k ^ 2 * t) := Real.sqrt_pos.mpr (by nlinarith [ht.2, hk1])
  rw [abs_of_pos (by simp only [hg']; positivity), Complex.real_smul]

/-- The integrand of 18.10.1 after the substitution `ψ = 2 arcsin(k √t)`. -/
private lemma dirM_pointwise {θ lam : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ((Real.sin (θ / 2) / (Real.sqrt t * Real.sqrt (1 - Real.sin (θ / 2) ^ 2 * t)) : ℝ) : ℂ) *
      ((Real.cos ((n + lam) * (2 * Real.arcsin (Real.sin (θ / 2) * Real.sqrt t))) : ℂ) *
        (Real.cos (2 * Real.arcsin (Real.sin (θ / 2) * Real.sqrt t)) - Real.cos θ : ℂ) ^
          (lam - 1 : ℂ)) =
    (Real.sin (θ / 2) : ℂ) * ((2 * Real.sin (θ / 2) ^ 2 : ℝ) : ℂ) ^ (lam - 1 : ℂ) *
      Gamma (1 / 2) * (regularizedGaussHGFun ((n : ℂ) + lam + 1 / 2) (1 - ((n : ℂ) + lam + 1 / 2))
        (1 / 2) (((Real.sin (θ / 2) ^ 2 : ℝ) : ℂ) * t) * (t : ℂ) ^ ((1 / 2 : ℂ) - 1) *
          (1 - (t : ℂ)) ^ ((lam : ℂ) + 1 / 2 - 1 / 2 - 1)) := by
  set k := Real.sin (θ / 2) with hk
  have hk0 : 0 < k := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hk1 : k < 1 := by
    rw [hk, ← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) le_rfl (by linarith)
  have hq : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht.1
  have hst : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.1.le
  have hs1 : k * Real.sqrt t < 1 := by
    have : Real.sqrt t < 1 := by rw [Real.sqrt_lt' one_pos]; simpa using ht.2
    nlinarith
  have hs0 : 0 < k * Real.sqrt t := mul_pos hk0 hq
  set x := Real.arcsin (k * Real.sqrt t) with hx
  have hsinx : Real.sin x = k * Real.sqrt t := Real.sin_arcsin (by linarith) hs1.le
  have hcosx : Real.cos x = Real.sqrt (1 - k ^ 2 * t) := by
    rw [hx, Real.cos_arcsin, mul_pow, hst]
  have hp : 0 < Real.sqrt (1 - k ^ 2 * t) := Real.sqrt_pos.mpr (by nlinarith [ht.2, hk1])
  have hxlt : |x| < Real.pi / 2 := by
    rw [abs_lt]; constructor
    · have := Real.arcsin_pos.mpr hs0; linarith [Real.pi_pos]
    · exact Real.arcsin_lt_pi_div_two.mpr hs1
  -- the hypergeometric form of `cos(2(n+λ)x)`
  have hF := sin_sq_cos_quotient ((n : ℂ) + lam + 1 / 2) hxlt
  have hc : ∀ j : ℕ, (1 / 2 : ℂ) ≠ -(j : ℂ) := fun j h => by
    have := congrArg Complex.re h; simp at this; linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]
  have hR := regularizedGaussHGFun_eq_div_Gamma hc (a := (n : ℂ) + lam + 1 / 2)
    (b := 1 - ((n : ℂ) + lam + 1 / 2)) (((k ^ 2 : ℝ) : ℂ) * t)
  have hz : ((Real.sin x : ℂ)) ^ 2 = ((k ^ 2 : ℝ) : ℂ) * t := by
    rw [hsinx, ← ofReal_pow, mul_pow, hst]; push_cast; ring
  rw [hz] at hF
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hcx : (Real.cos x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by rw [hcosx]; exact hp.ne')
  have hcos : (Real.cos ((n + lam) * (2 * x)) : ℂ) = (Real.cos x : ℂ) *
      (Gamma (1 / 2) * regularizedGaussHGFun ((n : ℂ) + lam + 1 / 2) (1 - ((n : ℂ) + lam + 1 / 2))
        (1 / 2) (((k ^ 2 : ℝ) : ℂ) * t)) := by
    rw [hR, hF, ofReal_cos]
    field_simp
    congr 1; push_cast; ring
  have hcos2 : Real.cos (2 * x) = 1 - 2 * k ^ 2 * t := by
    rw [Real.cos_two_mul', hsinx]; nlinarith [Real.sin_sq_add_cos_sq x, hsinx, hst]
  have hcosθ : Real.cos θ = 1 - 2 * k ^ 2 := by
    rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul', ← hk]
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have hdiff : (Real.cos (2 * x) : ℂ) - Real.cos θ = ((2 * k ^ 2 : ℝ) : ℂ) * ((1 - t : ℝ) : ℂ) := by
    rw [hcos2, hcosθ]; push_cast; ring
  have ht1 : (0 : ℝ) ≤ 1 - t := by linarith [ht.2]
  rw [hcos, hdiff, mul_cpow_ofReal_nonneg (by positivity) ht1]
  have htp : (t : ℂ) ^ ((1 / 2 : ℂ) - 1) = ((Real.sqrt t)⁻¹ : ℝ) := by
    rw [show (1 / 2 : ℂ) - 1 = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow ht.1.le,
      Real.rpow_neg ht.1.le, Real.sqrt_eq_rpow]
  rw [htp, show (lam : ℂ) + 1 / 2 - 1 / 2 - 1 = lam - 1 by ring,
    show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring, hcosx]
  have hpc : ((Real.sqrt (1 - k ^ 2 * t) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  push_cast
  field_simp

/-- The real normalization `2^λ sin^{1-2λ} θ · k (2k²)^{λ-1} (1-k²)^{λ-1/2} = 1`, `k = sin(θ/2)`. -/
private lemma dirM_const_real {θ lam : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    (2 : ℝ) ^ lam * Real.sin θ ^ (1 - 2 * lam) * (Real.sin (θ / 2) *
      ((2 * Real.sin (θ / 2) ^ 2) ^ (lam - 1) *
        (1 - Real.sin (θ / 2) ^ 2) ^ (lam - 1 / 2))) = 1 := by
  set k := Real.sin (θ / 2) with hk
  set c := Real.cos (θ / 2) with hc
  have hk0 : 0 < k := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hc0 : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : Real.sin θ = 2 * k * c := by
    rw [show θ = 2 * (θ / 2) by ring, Real.sin_two_mul]
  have h1 : 1 - k ^ 2 = c ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  rw [hs, h1, Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos (by positivity),
    Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity),
    Real.log_mul (by positivity) hc0.ne', Real.log_mul (by norm_num) hk0.ne',
    Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow,
    show k = Real.exp (Real.log k) from (Real.exp_log hk0).symm]
  rw [Real.log_exp, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  rw [Real.exp_eq_one_iff]; ring

/-- Dirichlet–Mehler integral for Gegenbauer polynomials (DLMF 18.10.1), via the substitution
`ψ = 2 arcsin(sin(θ/2) √t)`, the quotient formula 15.4.14, the fractional integral 15.6.8 and
Euler's transformation 15.8.1. -/
@[dlmf 18.10.E1]
theorem ultrasphPoly_dirichlet_integral {lam : ℝ} (hlam : 0 < lam) (n : ℕ)
    {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    ultrasphPoly lam n (Real.cos θ) / ultrasphPoly lam n 1 =
      (2 : ℂ) ^ (lam : ℂ) * Gamma (lam + 1 / 2 : ℂ) /
        (Real.sqrt Real.pi * Gamma (lam : ℂ)) * (Real.sin θ : ℂ) ^ (1 - 2 * lam : ℂ) *
      ∫ phi : ℝ in (0 : ℝ)..θ, (Real.cos ((n + lam) * phi) : ℂ) *
        (Real.cos phi - Real.cos θ : ℂ) ^ (lam - 1 : ℂ) := by
  set k := Real.sin (θ / 2) with hk
  have hk0 : 0 < k := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hk1 : k < 1 := by
    rw [hk, ← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) le_rfl (by linarith)
  set a : ℂ := (n : ℂ) + lam + 1 / 2 with ha
  set c : ℂ := (lam : ℂ) + 1 / 2 with hc
  set z : ℂ := ((k ^ 2 : ℝ) : ℂ) with hz
  have hz1 : ‖z‖ < 1 := by
    rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith
  -- the substitution and the fractional integral
  have hI : (∫ phi : ℝ in (0 : ℝ)..θ, (Real.cos ((n + lam) * phi) : ℂ) *
        (Real.cos phi - Real.cos θ : ℂ) ^ (lam - 1 : ℂ)) =
      (k : ℂ) * ((2 * k ^ 2 : ℝ) : ℂ) ^ (lam - 1 : ℂ) * Gamma (1 / 2) *
        (Gamma (c - 1 / 2) * regularizedGaussHGFun a (1 - a) c z) := by
    rw [dirM_subst hθ hθπ]
    rw [intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      (fun t ht => dirM_pointwise hθ hθπ n ht), intervalIntegral.integral_const_mul]
    congr 1
    have hfr := fractional_integral (a := a) (b := 1 - a) (c := c) (d := 1 / 2)
      (by norm_num) (by rw [hc]; simp [hlam]) hz1
    have hG : Gamma (c - 1 / 2) ≠ 0 := by
      rw [hc, show (lam : ℂ) + 1 / 2 - 1 / 2 = lam by ring]
      exact Complex.Gamma_ne_zero_of_re_pos (by simpa using hlam)
    rw [hfr, ← mul_assoc, mul_one_div_cancel hG, one_mul]
  rw [hI, regularizedGaussHGFun_euler a (1 - a) c hz1,
    show c - a - (1 - a) = (lam : ℂ) - 1 / 2 by rw [hc]; ring,
    show c - a = -(n : ℂ) by rw [hc, ha]; ring,
    show c - (1 - a) = (n : ℂ) + 2 * lam by rw [hc, ha]; ring,
    show c - 1 / 2 = (lam : ℂ) by rw [hc]; ring]
  have hcc : ∀ j : ℕ, c ≠ -(j : ℂ) := fun j h => by
    have := congrArg Complex.re h; rw [hc] at this; simp at this
    linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]
  rw [regularizedGaussHGFun_eq_div_Gamma hcc]
  have hcosθ : Real.cos θ = 1 - 2 * k ^ 2 := by
    rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul', ← hk]
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have hlre : -1 / 2 < (lam : ℂ).re := by simp; linarith
  have hP : poch (2 * (lam : ℂ)) n ≠ 0 := poch_ne_zero_of_re_pos (by simp; linarith) n
  have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [ultrasphPoly_at_one hlre, ultrasphPoly,
    show (1 - ((Real.cos θ : ℝ) : ℂ)) / 2 = z by rw [hz, hcosθ]; push_cast; ring, ← hc]
  -- the constant
  have hR := dirM_const_real (lam := lam) hθ hθπ
  rw [← hk] at hR
  have hpi : Gamma (1 / 2 : ℂ) = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]
    push_cast; ring_nf
  have hC : (2 : ℂ) ^ (lam : ℂ) * (Real.sin θ : ℂ) ^ (1 - 2 * lam : ℂ) * ((k : ℂ) *
      (((2 * k ^ 2 : ℝ) : ℂ) ^ (lam - 1 : ℂ) * (1 - z) ^ ((lam : ℂ) - 1 / 2))) = 1 := by
    have e1 : (2 : ℂ) ^ (lam : ℂ) = (((2 : ℝ) ^ lam : ℝ) : ℂ) := by
      rw [ofReal_cpow (by norm_num)]; norm_num
    have e2 : (Real.sin θ : ℂ) ^ (1 - 2 * lam : ℂ) = ((Real.sin θ ^ (1 - 2 * lam) : ℝ) : ℂ) := by
      rw [ofReal_cpow (Real.sin_nonneg_of_nonneg_of_le_pi hθ.le hθπ.le)]; push_cast; ring_nf
    have e3 : ((2 * k ^ 2 : ℝ) : ℂ) ^ (lam - 1 : ℂ) = (((2 * k ^ 2) ^ (lam - 1) : ℝ) : ℂ) := by
      rw [ofReal_cpow (by positivity)]; push_cast; ring_nf
    have e4 : (1 - z) ^ ((lam : ℂ) - 1 / 2) = (((1 - k ^ 2) ^ (lam - 1 / 2) : ℝ) : ℂ) := by
      rw [ofReal_cpow (by nlinarith), hz]; push_cast; ring_nf
    rw [e1, e2, e3, e4]
    exact_mod_cast hR
  have hg1 : Gamma (lam : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hlam)
  have hg2 : Gamma c ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hc]; simp; linarith)
  have hsq : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [hpi]
  field_simp
  rw [show ((2 * (lam : ℂ) - 1) / 2) = (lam : ℂ) - 1 / 2 by ring]
  linear_combination (-(₂F₁ (-(n : ℂ)) (n + 2 * lam) c z)) * hC

/-- Identity under the stated parameter and domain assumptions: `legendrePolyP n (Real.cos θ) =
(Real.sqrt 2 / Real.pi * ∫ phi : ℝ in (0 : ℝ)..θ, Real.cos ((n + 1 / 2) * phi) / Real.sqrt
(Real.cos phi - Real.cos θ) : ℝ)`. -/
@[dlmf 18.10.E2]
theorem legendre_dirichlet_mehler (n : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    legendrePolyP n (Real.cos θ) = (Real.sqrt 2 / Real.pi *
      ∫ phi : ℝ in (0 : ℝ)..θ, Real.cos ((n + 1 / 2) * phi) / Real.sqrt (Real.cos phi - Real.cos θ) : ℝ) := by
  have h := ultrasphPoly_dirichlet_integral (lam := 1 / 2) (by norm_num) n hθ hθπ
  have h1 : ultrasphPoly ((1 / 2 : ℝ) : ℂ) n 1 = 1 := by
    rw [ultrasphPoly_at_one (by norm_num)]
    rw [show 2 * ((1 / 2 : ℝ) : ℂ) = 1 by push_cast; ring, poch_nat_one]
    exact div_self (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  rw [h1, div_one, show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by push_cast; ring,
    ← legendre_eq_ultrasphPoly] at h
  rw [h]
  have hint : (∫ phi : ℝ in (0 : ℝ)..θ, (Real.cos ((n + 1 / 2) * phi) : ℂ) *
      (Real.cos phi - Real.cos θ : ℂ) ^ ((1 / 2 : ℂ) - 1)) =
      ((∫ phi : ℝ in (0 : ℝ)..θ, Real.cos ((n + 1 / 2) * phi) /
        Real.sqrt (Real.cos phi - Real.cos θ) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun phi hphi => ?_
    rw [Set.uIcc_of_le hθ.le] at hphi
    have hd : 0 ≤ Real.cos phi - Real.cos θ := sub_nonneg.mpr
      (Real.cos_le_cos_of_nonneg_of_le_pi hphi.1 hθπ.le hphi.2)
    rw [show (Real.cos phi : ℂ) - Real.cos θ = ((Real.cos phi - Real.cos θ : ℝ) : ℂ) by
        push_cast; ring,
      show (1 / 2 : ℂ) - 1 = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hd,
      Real.rpow_neg hd, ← Real.sqrt_eq_rpow]
    push_cast; ring
  rw [hint]
  have hpi : Gamma (1 / 2 : ℂ) = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]
    push_cast; ring_nf
  have h2 : (2 : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow (by norm_num)]; push_cast; ring_nf
  have hs : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Complex.Gamma_one, hpi, h2,
    show (1 : ℂ) - 2 * (1 / 2) = 0 by norm_num, cpow_zero]
  have hsq : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hs2 : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by
    rw [sq]; exact_mod_cast hs
  push_cast
  field_simp
  rw [hs2, mul_comm]

end DLMF.OrthogonalPolynomials
end
end
