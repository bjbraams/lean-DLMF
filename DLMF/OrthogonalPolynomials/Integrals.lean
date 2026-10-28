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
# Classical orthogonality, Rodrigues formulas, and integral identities

The product Laguerre Laplace transform uses finite changes of scale and local
orthogonality; Mathlib’s polynomial induction and Gamma moments justify complex
Laplace rates. The two double Laplace integrals use the proved Gegenbauer angular
representation, finite Jacobi binomial coefficients, and Mathlib’s square-substitution,
Gaussian-moment and Beta-integrability APIs, retaining singular integrable endpoints.

Integral identities from NIST DLMF Chapter 18. The Hermite and weighted Jacobi antiderivatives
are proved by the fundamental theorem of calculus. The Laguerre squared norm
is obtained from the already proved monomial moments;
other declarations below still include admitted results.
Probabilists’ Hermite orthogonality and polynomial Gaussian integrability use
the corresponding results of the Tau Ceti contributors. The two Hermite Fourier
eigenfunction identities adapt their normalized Hermite Fourier theorem to the
positive phase and scales used in DLMF.
The Hermite cosine and sine transforms 18.17.23 and 18.17.27 integrate by parts
against `He_n(x) e^{-x²/2}`; they use the Tau Ceti contributors' Gaussian
integrability `integrable_aeval_mul_gaussian` and Hermite parity `hermite_aeval_neg`.
The product cosine and sine transforms use finite Hermite linearization followed
by the single-polynomial transforms. The Gaussian convolution transfers derivatives
by integration by parts and evaluates its base case with Hermite addition.
The Laguerre fractional integrals reuse the regularized Kummer parameter integral
and the Laguerre addition and moment formulas. Gamma normalization uses Mathlib's
Gamma/Pochhammer identity; the tail substitution uses its measure-preserving translation API.
The Jacobi fractional integral reuses the regularized Gauss fractional integral.
Both Rodrigues formulas iterate the proved weighted derivative identities, with
Mathlib's iterated-derivative and real-scalar APIs handling the real restrictions.
Jacobi norms reduce by weighted integration by parts to shifted parameters and
terminate at the Beta integral, using Mathlib's endpoint-continuity and FTC APIs.
Gegenbauer orthogonality reuses symmetric Jacobi orthogonality and these norms;
Mathlib's Gamma duplication formula fixes its normalization, including degree zero.
Legendre norms follow from the three-term recurrence and proved Jacobi orthogonality.
The unweighted Laguerre convolution uses Mathlib's interval integration by parts
and the project's Laguerre derivative recurrence, and retains arbitrary real endpoints.
The weighted Laguerre convolution expands the normalized polynomials into finite
Gamma-normalized sums and scales Mathlib's Beta integral. Its Vandermonde step
uses an additive functional on Mathlib polynomials and their binomial coefficients.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
Gegenbauer's product formula 18.17.5 is proved by induction on the degree for all `λ > 0` at
once: one integration by parts in the angle (Mathlib's FTC API) lowers `cos φ` times the integrand
to the derivative at parameter `λ + 1`, and the three-term recurrence together with the identity
`(1 - x²) C_{n}^{λ+1}` (DLMF 18.9.8) closes the induction.
The Legendre–Bessel integral 18.17.21 integrates the sine series termwise against `P_n(1 - 2x²)`,
evaluates the moments by the substitution `s = 1 - 2x²` and the Jacobi moments, and matches the
result with the product series of `J_{n+1/2}²` (DLMF 10.8.3, `besselJ_mul_besselJ`).
The Dirichlet–Mehler integrals 18.10.1–18.10.2 substitute `ψ = 2 arcsin(sin(θ/2) √t)` (Mathlib's
change-of-variables formula `integral_image_eq_integral_abs_deriv_smul`), write `cos(2(n+λ)x)/cos x`
as a Gauss function (DLMF 15.4.14), and close with the fractional integral 15.6.8 and Euler's
transformation 15.8.1, which turns `𝐅(n+λ+1/2, 1/2-n-λ; λ+1/2; sin²(θ/2))` into the Gegenbauer
polynomial.
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

@[dlmf 18.3.T1]
theorem hermite_orthogonality (m n : ℕ) :
    ∫ x : ℝ, (aeval x (hermite m) : ℝ) * aeval x (hermite n) * Real.exp (-(x ^ 2) / 2) =
      if m = n then Real.sqrt (2 * Real.pi) * n.factorial else 0 := by
  simpa only [neg_div, mul_comm] using
    TauCeti.integral_hermite_mul_hermite_mul_gaussian m n

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

section GegenbauerLaplace

open Set

/-- `∫₀^π sin^{2λ-1} = √π Γ(λ)/Γ(λ+1/2)` for `λ > 0`, from the trigonometric Beta integral,
together with the integrability of `sin^{2λ-1}` on `[0, π]`. -/
theorem integral_sin_rpow_aux {lam : ℝ} (hlam : 0 < lam) :
    IntervalIntegrable (fun t : ℝ => Real.sin t ^ (2 * lam - 1)) volume 0 π ∧
    ∫ t in (0 : ℝ)..π, Real.sin t ^ (2 * lam - 1) =
      Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) := by
  have hB := DLMF.Gamma.beta_sin_cos (a := lam) (b := 1 / 2) hlam (by norm_num)
  simp only [show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero, mul_one,
    Real.Gamma_one_half_eq] at hB
  set f : ℝ → ℝ := fun t => Real.sin t ^ (2 * lam - 1) with hf
  have hpos : 0 < (1 / 2) * (Real.Gamma lam * Real.sqrt π / Real.Gamma (lam + 1 / 2)) := by
    have := Real.Gamma_pos_of_pos hlam
    have := Real.Gamma_pos_of_pos (show 0 < lam + 1 / 2 by linarith)
    have := Real.sqrt_pos.mpr Real.pi_pos
    positivity
  have hI1 : IntervalIntegrable f volume 0 (π / 2) := by
    by_contra h
    rw [intervalIntegral.integral_undef h] at hB
    linarith
  have hsymm : ∀ t, f (π - t) = f t := fun t => by simp [hf, Real.sin_pi_sub]
  have hI2 : IntervalIntegrable f volume (π / 2) π := by
    have := hI1.comp_sub_left π
    simp only [hsymm, sub_zero, show π - π / 2 = π / 2 by ring] at this
    exact this.symm
  refine ⟨hI1.trans hI2, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
  have h2 := intervalIntegral.integral_comp_sub_left f (a := 0) (b := π / 2) π
  rw [show π - π / 2 = π / 2 by ring, sub_zero] at h2
  simp only [hsymm] at h2
  rw [← h2, hB]
  ring

/-- The weighted Laplace integral `∫₀^π (cos θ + i sin θ cos φ)ⁿ sin^{2λ-1} φ dφ`. -/
def gegenbauerLaplace (lam θ : ℝ) (n : ℕ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..π, ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) ^ n *
    ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)

/-- The weighted Laplace integrals satisfy the normalized Gegenbauer recurrence. -/
theorem gegenbauerLaplace_recurrence {lam : ℝ} (hlam : 0 < lam) (θ : ℝ) (n : ℕ) :
    (n + 1 + 2 * lam : ℂ) * gegenbauerLaplace lam θ (n + 2) =
      2 * (n + 1 + lam) * Real.cos θ * gegenbauerLaplace lam θ (n + 1) -
        (n + 1) * gegenbauerLaplace lam θ n := by
  set c : ℂ := (Real.cos θ : ℂ) with hc
  set s : ℂ := (Real.sin θ : ℂ) with hs
  set w : ℝ → ℂ := fun t => c + I * s * Real.cos t with hw
  set ρ : ℝ → ℂ := fun t => ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) with hρ
  have hρi : IntervalIntegrable ρ volume 0 π := by
    have := (integral_sin_rpow_aux hlam).1
    exact ⟨this.1.ofReal, this.2.ofReal⟩
  have hU : uIcc (0 : ℝ) π = Icc 0 π := uIcc_of_le Real.pi_pos.le
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    rw [hc, hs, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Real.cos_sq_add_sin_sq]; simp
  have hsplit : ∀ x : ℝ, 0 ≤ x → x ^ (2 * lam) = x * x ^ (2 * lam - 1) := by
    intro x hx
    rcases hx.eq_or_lt with h | h
    · subst h; rw [Real.zero_rpow (by positivity), zero_mul]
    · rw [← Real.rpow_one_add' h.le (by linarith)]; ring_nf
  -- `F' = ρ g` is the derivative of `F = w^{n+1} sin^{2λ}` on `(0, π)`
  set g : ℝ → ℂ := fun t => (n + 1 : ℂ) * w t ^ n * (-(I * s) * Real.sin t) * Real.sin t +
    w t ^ (n + 1) * (2 * lam * Real.cos t) with hg
  have hgc : Continuous g := by fun_prop
  have hD : ∀ t ∈ Ioo (0 : ℝ) π, HasDerivAt (fun t : ℝ => w t ^ (n + 1) *
      ((Real.sin t ^ (2 * lam) : ℝ) : ℂ)) (ρ t * g t) t := by
    intro t ht
    have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
    have hwd : HasDerivAt w (-(I * s) * Real.sin t) t := by
      have := ((Real.hasDerivAt_cos t).ofReal_comp).const_mul (I * s)
      exact (this.const_add c).congr_deriv (by push_cast; ring)
    have hr := ((Real.hasDerivAt_sin t).rpow_const (p := 2 * lam) (Or.inl hst.ne')).ofReal_comp
    have := (hwd.pow (n + 1)).mul hr
    refine this.congr_deriv ?_
    simp only [hρ, hg, Nat.add_sub_cancel, Pi.pow_apply]
    rw [hsplit _ hst.le]
    push_cast
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.pi_pos.le
    ((by fun_prop : Continuous fun t : ℝ => w t ^ (n + 1)).continuousOn.mul
      (Complex.continuous_ofReal.comp ((Real.continuous_rpow_const (by positivity)).comp
        Real.continuous_sin)).continuousOn) hD (hρi.mul_continuousOn (hU ▸ hgc.continuousOn))
  simp only [Pi.mul_apply, Function.comp_apply, Real.sin_pi, Real.sin_zero,
    Real.zero_rpow (by positivity : 2 * lam ≠ 0), Complex.ofReal_zero, mul_zero, sub_zero] at hFTC
  -- multiply by `i s`
  have hpt : ∀ t : ℝ, I * s * (ρ t * g t) = ρ t * ((n + 1) * w t ^ n -
      2 * (n + 1 + lam) * c * w t ^ (n + 1) + (n + 1 + 2 * lam) * w t ^ (n + 2)) := by
    intro t
    have htrig : (Real.sin t : ℂ) ^ 2 + (Real.cos t : ℂ) ^ 2 = 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
        Real.sin_sq_add_cos_sq]; simp
    simp only [hg, hw]
    linear_combination (ρ t * (n + 1 : ℂ) * (c + I * s * Real.cos t) ^ n * (-I ^ 2 * s ^ 2)) *
      htrig - (ρ t * (n + 1 : ℂ) * (c + I * s * Real.cos t) ^ n * s ^ 2) * Complex.I_sq +
      (ρ t * (n + 1 : ℂ) * (c + I * s * Real.cos t) ^ n) * hcs
  have h0 : ∫ t : ℝ in (0 : ℝ)..π, I * s * (ρ t * g t) = 0 := by
    rw [intervalIntegral.integral_const_mul, hFTC]; simp
  rw [intervalIntegral.integral_congr (fun t _ => hpt t)] at h0
  have hk : ∀ k : ℕ, IntervalIntegrable (fun t => w t ^ k * ρ t) volume 0 π :=
    fun k => hρi.continuousOn_mul (hU ▸ (by fun_prop : Continuous fun t : ℝ => w t ^ k).continuousOn)
  have hsplit3 : ∀ t : ℝ, ρ t * ((n + 1) * w t ^ n - 2 * (n + 1 + lam) * c * w t ^ (n + 1) +
      (n + 1 + 2 * lam) * w t ^ (n + 2)) = (n + 1) * (w t ^ n * ρ t) -
      2 * (n + 1 + lam) * c * (w t ^ (n + 1) * ρ t) + (n + 1 + 2 * lam) * (w t ^ (n + 2) * ρ t) :=
    fun t => by ring
  rw [intervalIntegral.integral_congr (fun t _ => hsplit3 t),
    intervalIntegral.integral_add (((hk n).const_mul _).sub ((hk (n + 1)).const_mul _))
      ((hk (n + 2)).const_mul _),
    intervalIntegral.integral_sub ((hk n).const_mul _) ((hk (n + 1)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h0
  simp only [gegenbauerLaplace]
  linear_combination h0

@[dlmf 18.10.E4]
theorem ultrasphPoly_laplace_integral {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (θ : ℝ) :
    ultrasphPoly lam n (Real.cos θ) / ultrasphPoly lam n 1 =
      Gamma (lam + 1 / 2 : ℂ) / (Real.sqrt Real.pi * Gamma (lam : ℂ)) *
        ∫ phi : ℝ in (0 : ℝ)..Real.pi, (Real.cos θ + I * Real.sin θ * Real.cos phi) ^ n *
          (Real.rpow (Real.sin phi) (2 * lam - 1) : ℂ) := by
  obtain ⟨hρi', hρint⟩ := integral_sin_rpow_aux hlam
  set K : ℂ := ((Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) : ℝ) : ℂ) with hK
  have hG1 : 0 < Real.Gamma (lam + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hG2 : 0 < Real.Gamma lam := Real.Gamma_pos_of_pos hlam
  have hsq : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hK0 : K ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hlamC : 0 < (lam : ℂ).re := by simpa using hlam
  -- the normalized polynomials
  set R : ℕ → ℂ := fun n => ultrasphPoly lam n (Real.cos θ) / ultrasphPoly lam n 1 with hR
  have hbase0 : gegenbauerLaplace lam θ 0 = K := by
    simp only [gegenbauerLaplace, pow_zero, one_mul, hK]
    rw [intervalIntegral.integral_ofReal, hρint]
  have hcos0 : ∫ t : ℝ in (0 : ℝ)..π, (Real.cos t * Real.sin t ^ (2 * lam - 1) : ℝ) = 0 := by
    have hD : ∀ t ∈ Ioo (0 : ℝ) π, HasDerivAt (fun t : ℝ => Real.sin t ^ (2 * lam) / (2 * lam))
        (Real.cos t * Real.sin t ^ (2 * lam - 1)) t := by
      intro t ht
      have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
      have := ((Real.hasDerivAt_sin t).rpow_const (p := 2 * lam) (Or.inl hst.ne')).div_const
        (2 * lam)
      refine this.congr_deriv ?_
      field_simp
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.pi_pos.le
      (((Real.continuous_rpow_const (by positivity)).comp Real.continuous_sin).div_const
        (2 * lam)).continuousOn hD (hρi'.continuousOn_mul Real.continuous_cos.continuousOn)
    rw [h]
    simp [Real.zero_rpow (by positivity : 2 * lam ≠ 0)]
  have hbase1 : gegenbauerLaplace lam θ 1 = Real.cos θ * K := by
    simp only [gegenbauerLaplace, pow_one]
    have hsplit : ∀ t : ℝ, ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) *
        ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) = Real.cos θ * ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) +
          I * Real.sin θ * ((Real.cos t * Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) := by
      intro t; push_cast; ring
    have hρC : IntervalIntegrable (fun t : ℝ => ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)) volume 0 π :=
      ⟨hρi'.1.ofReal, hρi'.2.ofReal⟩
    have hψ := hρi'.continuousOn_mul Real.continuous_cos.continuousOn
    have hψC : IntervalIntegrable (fun t : ℝ => ((Real.cos t * Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ))
        volume 0 π := ⟨hψ.1.ofReal, hψ.2.ofReal⟩
    rw [intervalIntegral.integral_congr (fun t _ => hsplit t),
      intervalIntegral.integral_add (hρC.const_mul _) (hψC.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, hρint, hcos0, hK]
    simp
  -- induction
  have hind : ∀ n : ℕ, gegenbauerLaplace lam θ n = K * R n ∧
      gegenbauerLaplace lam θ (n + 1) = K * R (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [hbase0]; simp [hR, ultrasphPoly_zero]
      · rw [hbase1]; simp only [hR, zero_add, ultrasphPoly_normalized_one hlamC]; ring
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hr := gegenbauerLaplace_recurrence hlam θ n
      have hP := ultrasphPoly_normalized_recurrence hlamC n (Real.cos θ)
      rw [ih.1, ih.2] at hr
      have hn : (n + 1 + 2 * lam : ℂ) ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      apply mul_left_cancel₀ hn
      rw [show n + 1 + 1 = n + 2 by ring, hr]
      simp only [hR]
      linear_combination (-K) * hP
  have hmain := (hind n).1
  have hGam : Gamma (lam + 1 / 2 : ℂ) / (Real.sqrt Real.pi * Gamma (lam : ℂ)) = K⁻¹ := by
    rw [hK, show (lam + 1 / 2 : ℂ) = ((lam + 1 / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal, Complex.Gamma_ofReal]
    push_cast
    field_simp
  rw [hGam, show (∫ phi : ℝ in (0 : ℝ)..Real.pi, ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos phi) ^ n *
      (Real.rpow (Real.sin phi) (2 * lam - 1) : ℂ)) = gegenbauerLaplace lam θ n from rfl, hmain]
  field_simp
  rfl

end GegenbauerLaplace

/-- The Laplace integral `∫₀^π (cos θ + i sin θ cos t)^n dt`. -/
def legendreLaplace (θ : ℝ) (n : ℕ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..π, ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) ^ n

/-- The Laplace integrals satisfy the Legendre recurrence. -/
theorem legendreLaplace_recurrence (θ : ℝ) (n : ℕ) :
    (n + 2 : ℂ) * legendreLaplace θ (n + 2) =
      (2 * n + 3) * Real.cos θ * legendreLaplace θ (n + 1) - (n + 1) * legendreLaplace θ n := by
  set c : ℂ := (Real.cos θ : ℂ) with hc
  set s : ℂ := (Real.sin θ : ℂ) with hs
  set w : ℝ → ℂ := fun t => c + I * s * Real.cos t with hw
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    rw [hc, hs, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Real.cos_sq_add_sin_sq]; simp
  -- the exact derivative `d/dt [w^{n+1} sin t]`
  have hD : ∀ t : ℝ, HasDerivAt (fun t : ℝ => w t ^ (n + 1) * (Real.sin t : ℂ))
      ((n + 1 : ℂ) * w t ^ n * (-(I * s) * Real.sin t) * Real.sin t +
        w t ^ (n + 1) * Real.cos t) t := by
    intro t
    have hwd : HasDerivAt w (-(I * s) * Real.sin t) t := by
      have := ((Real.hasDerivAt_cos t).ofReal_comp).const_mul (I * s)
      exact (this.const_add c).congr_deriv (by push_cast; ring)
    have := (hwd.pow (n + 1)).mul (Real.hasDerivAt_sin t).ofReal_comp
    exact this.congr_deriv (by simp only [Pi.pow_apply, Nat.add_sub_cancel]; push_cast; ring)
  have hcont : Continuous fun t : ℝ => (n + 1 : ℂ) * w t ^ n * (-(I * s) * Real.sin t) *
      Real.sin t + w t ^ (n + 1) * Real.cos t := by fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hD t)
    (hcont.intervalIntegrable 0 π)
  simp only [Real.sin_pi, Real.sin_zero, Complex.ofReal_zero, mul_zero, sub_zero] at hint
  -- multiply by `i s` and use the pointwise identity
  have hpt : ∀ t : ℝ, I * s * ((n + 1 : ℂ) * w t ^ n * (-(I * s) * Real.sin t) * Real.sin t +
      w t ^ (n + 1) * Real.cos t) = (n + 1) * w t ^ n - (2 * n + 3) * c * w t ^ (n + 1) +
        (n + 2) * w t ^ (n + 2) := by
    intro t
    have htrig : (Real.sin t : ℂ) ^ 2 + (Real.cos t : ℂ) ^ 2 = 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
        Real.sin_sq_add_cos_sq]; simp
    simp only [hw]
    linear_combination ((n + 1 : ℂ) * (c + I * s * Real.cos t) ^ n * (-I ^ 2 * s ^ 2)) * htrig -
      ((n + 1 : ℂ) * (c + I * s * Real.cos t) ^ n * s ^ 2) * Complex.I_sq +
      ((n + 1 : ℂ) * (c + I * s * Real.cos t) ^ n) * hcs
  have h0 : ∫ t : ℝ in (0 : ℝ)..π, I * s * ((n + 1 : ℂ) * w t ^ n * (-(I * s) * Real.sin t) *
      Real.sin t + w t ^ (n + 1) * Real.cos t) = 0 := by
    rw [intervalIntegral.integral_const_mul, hint]; simp
  rw [intervalIntegral.integral_congr (fun t _ => hpt t)] at h0
  have hc' : ∀ k : ℕ, IntervalIntegrable (fun t : ℝ => w t ^ k) volume 0 π :=
    fun k => (by fun_prop : Continuous fun t : ℝ => w t ^ k).intervalIntegrable 0 π
  rw [intervalIntegral.integral_add (((hc' n).const_mul _).sub ((hc' (n + 1)).const_mul _))
    ((hc' (n + 2)).const_mul _), intervalIntegral.integral_sub ((hc' n).const_mul _)
    ((hc' (n + 1)).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h0
  simp only [legendreLaplace]
  linear_combination h0

@[dlmf 18.10.E5]
theorem legendre_laplace_integral (n : ℕ) (θ : ℝ) :
    legendrePolyP n (Real.cos θ) = (Real.pi : ℂ)⁻¹ *
      ∫ phi : ℝ in (0 : ℝ)..Real.pi, (Real.cos θ + I * Real.sin θ * Real.cos phi) ^ n := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  suffices h : ∀ n : ℕ, legendreLaplace θ n = π * legendrePolyP n (Real.cos θ) ∧
      legendreLaplace θ (n + 1) = π * legendrePolyP (n + 1) (Real.cos θ) by
    rw [show (∫ t : ℝ in (0 : ℝ)..Real.pi, ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) ^ n)
      = legendreLaplace θ n from rfl, (h n).1]
    field_simp
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [legendreLaplace, legendrePolyP_zero]
    · simp only [legendreLaplace, zero_add, pow_one, legendrePolyP_one]
      rw [intervalIntegral.integral_add intervalIntegrable_const
        ((by fun_prop : Continuous fun t : ℝ => I * (Real.sin θ : ℂ) * Real.cos t
          ).intervalIntegrable 0 π), intervalIntegral.integral_const_mul,
        show ∫ x in (0 : ℝ)..π, ((Real.cos x : ℝ) : ℂ) = ((∫ x in (0 : ℝ)..π, Real.cos x : ℝ) : ℂ)
          from intervalIntegral.integral_ofReal, integral_cos]
      simp
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hr := legendreLaplace_recurrence θ n
    have hP := legendrePolyP_recurrence n (Real.cos θ)
    rw [ih.1, ih.2] at hr
    have hn : (n + 2 : ℂ) ≠ 0 := by norm_cast
    apply mul_left_cancel₀ hn
    rw [hr]
    linear_combination (-(π : ℂ)) * hP

/-- `x^k e^{-xz} e^{-x²}` is integrable for every complex `z`. -/
theorem integrable_pow_mul_cexp_gauss (k : ℕ) (z : ℂ) :
    Integrable fun x : ℝ => (x : ℂ) ^ k * (cexp (-x * z) * cexp (-(x : ℂ) ^ 2)) := by
  have hreal : Integrable fun x : ℝ => x ^ k * Real.exp (-(1 / 2) * x ^ 2) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
      (s := (k : ℝ)) (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
    refine h.congr (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [Real.rpow_natCast]
  have hg : Integrable fun x : ℝ => (x : ℂ) ^ k * cexp (-(x : ℂ) ^ 2 / 2) := by
    refine hreal.norm.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp, norm_pow,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    apply le_of_eq
    congr 2
    simp [sq]; ring
  set a := z.re
  have hbd : ∀ x : ℝ, ‖cexp (-x * z - (x : ℂ) ^ 2 / 2)‖ ≤ Real.exp (a ^ 2 / 2) := by
    intro x
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have : (-x * z - (x : ℂ) ^ 2 / 2).re = -x * a - x ^ 2 / 2 := by
      simp [a, sq]
    rw [this]
    nlinarith [sq_nonneg (x + a)]
  have hm : AEStronglyMeasurable (fun x : ℝ => cexp (-x * z - (x : ℂ) ^ 2 / 2)) volume :=
    (by fun_prop : Continuous fun x : ℝ => cexp (-x * z - (x : ℂ) ^ 2 / 2)).aestronglyMeasurable
  refine (hg.bdd_mul hm (Eventually.of_forall hbd)).congr (Eventually.of_forall fun x => ?_)
  beta_reduce
  have e : cexp (-↑x * z - (x : ℂ) ^ 2 / 2) * cexp (-(x : ℂ) ^ 2 / 2) =
      cexp (-↑x * z) * cexp (-(x : ℂ) ^ 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
  linear_combination (x : ℂ) ^ k * e

/-- A polynomial times `e^{-xz} e^{-x²}` is integrable. -/
theorem integrable_eval_mul_cexp_gauss (q : ℝ[X]) (z : ℂ) :
    Integrable fun x : ℝ => cexp (-x * z) * ((q.eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) := by
  have hq : ∀ x : ℝ, cexp (-x * z) * ((q.eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) =
      ∑ i ∈ Finset.range (q.natDegree + 1),
        (q.coeff i : ℂ) * ((x : ℂ) ^ i * (cexp (-x * z) * cexp (-(x : ℂ) ^ 2))) := fun x => by
    rw [eval_eq_sum_range, Finset.sum_mul]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hq]
  exact integrable_finsetSum _ fun i _ => (integrable_pow_mul_cexp_gauss i z).const_mul _

/-- Repeated integration by parts against `e^{-xz}`. -/
theorem integral_cexp_mul_hermite_gauss (z : ℂ) (n : ℕ) :
    ∫ x : ℝ, cexp (-x * z) * (((hermitePolyHR n).eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) =
      (-z) ^ n * ∫ x : ℝ, cexp (-x * z) * ((Real.exp (-(x ^ 2)) : ℝ) : ℂ) := by
  induction n with
  | zero => simp [hermitePolyHR]
  | succ n ih =>
    have hu : ∀ x : ℝ, HasDerivAt (fun y : ℝ => cexp (-y * z)) (cexp (-x * z) * (-z)) x := by
      intro x
      have := ((hasDerivAt_id (x : ℂ)).neg.mul_const z).cexp.comp_ofReal (z := x)
      simpa using this
    have hv : ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => (((hermitePolyHR n).eval y * Real.exp (-(y ^ 2)) : ℝ) : ℂ))
        (-((((hermitePolyHR (n + 1)).eval x * Real.exp (-(x ^ 2))) : ℝ) : ℂ)) x := by
      intro x
      have := (hasDerivAt_hermite_gauss n x).ofReal_comp
      simpa using this
    have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => hu x) (fun x _ => hv x)
      ((integrable_eval_mul_cexp_gauss (hermitePolyHR (n + 1)) z).neg.congr
        (Eventually.of_forall fun x => by simp only [Pi.mul_apply, Pi.neg_apply]; ring))
      (((integrable_eval_mul_cexp_gauss (hermitePolyHR n) z).const_mul (-z)).congr
        (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring))
      (integrable_eval_mul_cexp_gauss (hermitePolyHR n) z)
    have h1 : ∫ x : ℝ,
        cexp (-x * z) * (((hermitePolyHR (n + 1)).eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) =
        -∫ x : ℝ, cexp (-x * z)
            * -((((hermitePolyHR (n + 1)).eval x * Real.exp (-(x ^ 2))) : ℝ) : ℂ) := by
      rw [← integral_neg]; congr 1; funext x; ring
    rw [h1, hibp, neg_neg]
    have h2 : ∫ x : ℝ,
        cexp (-x * z) * (-z) * (((hermitePolyHR n).eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) =
        -z * ∫ x : ℝ,
            cexp (-x * z) * (((hermitePolyHR n).eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) := by
      rw [← integral_const_mul]; congr 1; funext x; ring
    rw [h2, ih, pow_succ]
    ring

/-- `∫ e^{-xz} e^{-x²} dx = √π e^{z²/4}`. -/
theorem integral_cexp_gauss (z : ℂ) :
    ∫ x : ℝ, cexp (-x * z) * ((Real.exp (-(x ^ 2)) : ℝ) : ℂ) =
      (Real.sqrt Real.pi : ℂ) * cexp (z ^ 2 / 4) := by
  have h := integral_cexp_quadratic (b := -1) (by simp) (-z) 0
  have heq : ∀ x : ℝ, cexp (-x * z) * ((Real.exp (-(x ^ 2)) : ℝ) : ℂ) =
      cexp (-1 * (x : ℂ) ^ 2 + -z * x + 0) := fun x => by
    rw [ofReal_exp, ← Complex.exp_add]; push_cast; ring_nf
  simp_rw [heq, h]
  rw [neg_neg, div_one, show (0 : ℂ) - (-z) ^ 2 / (4 * -1) = z ^ 2 / 4 by ring]
  congr 1
  rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]
  norm_num

/-- The Laplace transform of `Hₙ(x) e^{-x²}` over `ℝ` is `√π (-z)ⁿ e^{z²/4}`
(DLMF 18.17.35). -/
@[dlmf 18.17.E35]
theorem hermitePolyH_laplace_transform (n : ℕ) (z : ℂ) :
    ∫ x : ℝ, exp (-x * z) * (aeval (x : ℂ) (hermitePolyH n) : ℂ) * exp (-(x : ℂ) ^ 2) =
      Real.sqrt Real.pi * (-z) ^ n * exp (z ^ 2 / 4) := by
  have heq : ∀ x : ℝ, exp (-x * z) * (aeval (x : ℂ) (hermitePolyH n) : ℂ) * exp (-(x : ℂ) ^ 2) =
      cexp (-x * z) * (((hermitePolyHR n).eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) := fun x => by
    have : (aeval (x : ℂ) (hermitePolyH n) : ℂ) = (((hermitePolyHR n).eval x : ℝ) : ℂ) := by
      rw [← aeval_hermitePolyH_eq_eval]
      exact aeval_algebraMap_apply ℂ x (hermitePolyH n)
    rw [this, ofReal_mul, ofReal_exp]; push_cast; ring
  simp_rw [heq]
  rw [integral_cexp_mul_hermite_gauss, integral_cexp_gauss]
  ring

/-- `(x+it)^n t^j e^{-t²}` is integrable. -/
theorem integrable_add_I_pow_mul_pow_gauss (x : ℂ) (n j : ℕ) :
    Integrable fun t : ℝ => (x + I * t) ^ n * ((t : ℂ) ^ j * ((Real.exp (-(t ^ 2)) : ℝ) : ℂ)) := by
  have hq : ∀ t : ℝ, (x + I * t) ^ n * ((t : ℂ) ^ j * ((Real.exp (-(t ^ 2)) : ℝ) : ℂ)) =
      ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℂ) * x ^ (n - k) * I ^ k) *
        ((t : ℂ) ^ (k + j) * (cexp (-t * 0) * cexp (-(t : ℂ) ^ 2))) := fun t => by
    rw [add_comm, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ofReal_exp]; push_cast; simp; ring
  simp_rw [hq]
  exact integrable_finsetSum _ fun k _ => (integrable_pow_mul_cexp_gauss (k + j) 0).const_mul _

/-- `(x+it)^n e^{-t²}` is integrable. -/
theorem integrable_add_I_pow_gauss (x : ℂ) (n : ℕ) :
    Integrable fun t : ℝ => (x + I * t) ^ n * ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) := by
  simpa using integrable_add_I_pow_mul_pow_gauss x n 0

/-- One integration by parts: `∫ t (x+it)^n e^{-t²} = (i n / 2) ∫ (x+it)^{n-1} e^{-t²}`. -/
theorem integral_t_mul_add_I_pow (x : ℂ) (n : ℕ) :
    ∫ t : ℝ, (x + I * t) ^ (n + 1) * ((t * Real.exp (-(t ^ 2)) : ℝ) : ℂ) =
      I * (n + 1) / 2 * ∫ t : ℝ, (x + I * t) ^ n * ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) := by
  have hu : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (x + I * s) ^ (n + 1))
      ((n + 1 : ℂ) * (x + I * t) ^ n * I) t := by
    intro t
    have := (((hasDerivAt_id (t : ℂ)).const_mul I).const_add x).pow (n + 1) |>.comp_ofReal (z := t)
    simpa using this
  have hv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ((-(Real.exp (-(s ^ 2))) / 2 : ℝ) : ℂ))
      (((t * Real.exp (-(t ^ 2))) : ℝ) : ℂ) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -(Real.exp (-(s ^ 2))) / 2) (t * Real.exp (-(t ^ 2))) t := by
      have := (((hasDerivAt_pow 2 t).neg).exp.neg).div_const 2
      convert this using 1; simp; ring
    exact h1.ofReal_comp
  have hI := integrable_add_I_pow_gauss x n
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hu t) (fun t _ => hv t)
    ?_ ?_ ?_
  · rw [hibp]
    rw [show (fun t : ℝ => (n + 1 : ℂ) * (x + I * t) ^ n * I * ((-(Real.exp (-(t ^ 2))) / 2 : ℝ) : ℂ))
      = fun t => -(I * (n + 1) / 2) * ((x + I * t) ^ n * ((Real.exp (-(t ^ 2)) : ℝ) : ℂ)) by
        funext t; push_cast; ring, integral_const_mul]
    ring
  · refine (integrable_add_I_pow_mul_pow_gauss x (n + 1) 1).congr
      (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply]; push_cast; ring
  · refine ((integrable_add_I_pow_gauss x n).const_mul (-(I * (n + 1) / 2))).congr
      (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply]; push_cast; ring
  · refine ((integrable_add_I_pow_gauss x (n + 1)).const_mul (-(1 / 2))).congr
      (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply]; push_cast; ring

@[dlmf 18.10.E7]
theorem hermitePolyH_laplace_integral (n : ℕ) (x : ℂ) :
    aeval x (hermitePolyH n) = (2 : ℂ) ^ n / Real.sqrt Real.pi *
      ∫ t : ℝ, (x + I * t) ^ n * Real.exp (-(t ^ 2)) := by
  set F : ℕ → ℂ := fun n => ∫ t : ℝ, (x + I * t) ^ n * ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) with hF
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hF0 : F 0 = Real.sqrt Real.pi := by
    simp only [hF, pow_zero, one_mul]
    rw [integral_complex_ofReal, show (fun t : ℝ => Real.exp (-(t ^ 2))) =
      fun t => Real.exp (-1 * t ^ 2) by funext t; ring_nf, integral_gaussian, div_one]
  have hodd : ∫ t : ℝ, ((t * Real.exp (-(t ^ 2)) : ℝ) : ℂ) = 0 := by
    have h := integral_neg_eq_self (fun t : ℝ => ((t * Real.exp (-(t ^ 2)) : ℝ) : ℂ)) volume
    simp only [neg_mul, neg_sq, ofReal_neg, integral_neg] at h
    linear_combination (-1 / 2 : ℂ) * h
  have hF1 : F 1 = x * Real.sqrt Real.pi := by
    have : F 1 = x * F 0 + I * ∫ t : ℝ, ((t * Real.exp (-(t ^ 2)) : ℝ) : ℂ) := by
      simp only [hF, pow_one, pow_zero, one_mul]
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
      · congr 1; funext t; push_cast; try ring
      · exact (integrable_add_I_pow_gauss x 0).const_mul x |>.congr
          (Eventually.of_forall fun t => by simp)
      · exact ((integrable_add_I_pow_mul_pow_gauss 0 0 1).const_mul I).congr
          (Eventually.of_forall fun t => by simp)
    rw [this, hodd, hF0]; ring
  have hrec : ∀ n : ℕ, F (n + 2) = x * F (n + 1) - (n + 1) / 2 * F n := by
    intro n
    have hsplit : F (n + 2) = x * F (n + 1) +
        I * ∫ t : ℝ, (x + I * t) ^ (n + 1) * ((t * Real.exp (-(t ^ 2)) : ℝ) : ℂ) := by
      simp only [hF]
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add
        ((integrable_add_I_pow_gauss x (n + 1)).const_mul x)
        (((integrable_add_I_pow_mul_pow_gauss x (n + 1) 1).const_mul I).congr
          (Eventually.of_forall fun t => by simp only; push_cast; ring))]
      congr 1; funext t; push_cast; ring
    rw [hsplit, integral_t_mul_add_I_pow]
    simp only [hF]
    rw [show I * (I * ((n : ℂ) + 1) / 2 * ∫ t : ℝ, (x + I * t) ^ n *
      ((Real.exp (-(t ^ 2)) : ℝ) : ℂ)) = I ^ 2 * (((n : ℂ) + 1) / 2) * ∫ t : ℝ, (x + I * t) ^ n *
      ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) by ring, I_sq]
    ring
  have key : ∀ n : ℕ, (2 : ℂ) ^ n * F n = Real.sqrt Real.pi * aeval x (hermitePolyH n) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simp [hF0]
    | one => rw [hF1, hermitePolyH_one, map_mul, aeval_X, map_ofNat]; ring
    | more n ih0 ih1 =>
      rw [hrec, aeval_hermitePolyH_succ_succ]
      linear_combination 2 * x * ih1 - 2 * ((n : ℂ) + 1) * ih0
  have hn := key n
  simp only [hF] at hn
  field_simp
  linear_combination -hn

/-- `e^{-t²} tⁿ e^{2ixt}` is integrable. -/
theorem integrable_gauss_pow_cexp (x : ℝ) (n : ℕ) :
    Integrable fun t : ℝ => ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ n * cexp (2 * I * x * t) := by
  refine (integrable_pow_mul_cexp_gauss n (-2 * I * x)).congr (Eventually.of_forall fun t => ?_)
  simp only [ofReal_exp]
  push_cast
  rw [show -(t : ℂ) * (-2 * I * x) = 2 * I * x * t by ring]
  ring

/-- The moment recurrence for `∫ e^{-t²} tⁿ e^{2ixt} dt`. -/
theorem integral_K_succ_succ (x : ℝ) (n : ℕ) :
    ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ (n + 2) * cexp (2 * I * x * t) =
      I * x * (∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ (n + 1) * cexp (2 * I * x * t)) +
      (n + 1) / 2 * ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ n * cexp (2 * I * x * t) := by
  have hu : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ) ^ (n + 1) * cexp (2 * I * x * s))
      (((n + 1 : ℂ) * (t : ℂ) ^ n) * cexp (2 * I * x * t) +
        (t : ℂ) ^ (n + 1) * (cexp (2 * I * x * t) * (2 * I * x))) t := by
    intro t
    have h1 := (hasDerivAt_pow (n + 1) (t : ℂ)).comp_ofReal
    have h2 := ((hasDerivAt_id (t : ℂ)).const_mul (2 * I * x)).cexp.comp_ofReal (z := t)
    simp only [id, mul_one] at h2
    refine (h1.mul h2).congr_deriv ?_
    push_cast; ring
  have hv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ((-(Real.exp (-(s ^ 2))) / 2 : ℝ) : ℂ))
      (((t * Real.exp (-(t ^ 2))) : ℝ) : ℂ) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -(Real.exp (-(s ^ 2))) / 2) (t * Real.exp (-(t ^ 2))) t := by
      have := (((hasDerivAt_pow 2 t).neg).exp.neg).div_const 2
      convert this using 1; simp; ring
    exact h1.ofReal_comp
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hu t) (fun t _ => hv t)
    ((integrable_gauss_pow_cexp x (n + 2)).congr (Eventually.of_forall fun t => by
      simp only [Pi.mul_apply]; push_cast; ring))
    ((((integrable_gauss_pow_cexp x n).const_mul (-((n : ℂ) + 1) / 2)).add
      ((integrable_gauss_pow_cexp x (n + 1)).const_mul (-(I * x)))).congr
      (Eventually.of_forall fun t => by simp only [Pi.mul_apply, Pi.add_apply]; push_cast; ring))
    (((integrable_gauss_pow_cexp x (n + 1)).const_mul (-(1 / 2))).congr
      (Eventually.of_forall fun t => by simp only [Pi.mul_apply]; push_cast; ring))
  have e1 : ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ (n + 2) * cexp (2 * I * x * t) =
      ∫ t : ℝ, (t : ℂ) ^ (n + 1) * cexp (2 * I * x * t) * (((t * Real.exp (-(t ^ 2))) : ℝ) : ℂ) := by
    congr 1; funext t; push_cast; ring
  rw [e1, hibp]
  rw [show (fun t : ℝ => (((n + 1 : ℂ) * (t : ℂ) ^ n) * cexp (2 * I * x * t) +
      (t : ℂ) ^ (n + 1) * (cexp (2 * I * x * t) * (2 * I * x))) * ((-(Real.exp (-(t ^ 2))) / 2 : ℝ) : ℂ))
      = fun t => (-((n : ℂ) + 1) / 2) * (((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ n *
          cexp (2 * I * x * t)) + (-(I * x)) * (((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ (n + 1) *
          cexp (2 * I * x * t)) by funext t; push_cast; ring]
  rw [integral_add ((integrable_gauss_pow_cexp x n).const_mul _)
    ((integrable_gauss_pow_cexp x (n + 1)).const_mul _), integral_const_mul, integral_const_mul]
  ring

/-- The Fourier transform of the Gaussian. -/
theorem integral_K_zero (x : ℝ) :
    ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ 0 * cexp (2 * I * x * t) =
      Real.sqrt Real.pi * cexp (-(x : ℂ) ^ 2) := by
  have h := integral_cexp_gauss (-2 * I * x)
  rw [show (-2 * I * (x : ℂ)) ^ 2 / 4 = -(x : ℂ) ^ 2 by ring_nf; rw [I_sq]; ring] at h
  rw [← h]
  congr 1; funext t
  rw [show -(t : ℂ) * (-2 * I * x) = 2 * I * x * t by ring]
  ring

/-- The first moment of the Gaussian Fourier kernel. -/
theorem integral_K_one (x : ℝ) :
    ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ 1 * cexp (2 * I * x * t) =
      I * x * ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ 0 * cexp (2 * I * x * t) := by
  have hu : ∀ t : ℝ, HasDerivAt (fun s : ℝ => cexp (2 * I * x * s))
      (cexp (2 * I * x * t) * (2 * I * x)) t := by
    intro t
    have h2 := ((hasDerivAt_id (t : ℂ)).const_mul (2 * I * x)).cexp.comp_ofReal (z := t)
    simpa using h2
  have hv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ((-(Real.exp (-(s ^ 2))) / 2 : ℝ) : ℂ))
      (((t * Real.exp (-(t ^ 2))) : ℝ) : ℂ) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -(Real.exp (-(s ^ 2))) / 2) (t * Real.exp (-(t ^ 2))) t := by
      have := (((hasDerivAt_pow 2 t).neg).exp.neg).div_const 2
      convert this using 1; simp; ring
    exact h1.ofReal_comp
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hu t) (fun t _ => hv t)
    ((integrable_gauss_pow_cexp x 1).congr (Eventually.of_forall fun t => by
      simp only [Pi.mul_apply]; push_cast; ring))
    (((integrable_gauss_pow_cexp x 0).const_mul (-(I * x))).congr
      (Eventually.of_forall fun t => by simp only [Pi.mul_apply]; push_cast; ring))
    (((integrable_gauss_pow_cexp x 0).const_mul (-(1 / 2))).congr
      (Eventually.of_forall fun t => by simp only [Pi.mul_apply]; push_cast; ring))
  have e1 : ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ 1 * cexp (2 * I * x * t) =
      ∫ t : ℝ, cexp (2 * I * x * t) * (((t * Real.exp (-(t ^ 2))) : ℝ) : ℂ) := by
    congr 1; funext t; push_cast; ring
  rw [e1, hibp, show (fun t : ℝ => cexp (2 * I * x * t) * (2 * I * x) *
      ((-(Real.exp (-(t ^ 2))) / 2 : ℝ) : ℂ)) = fun t => (-(I * x)) *
      (((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ 0 * cexp (2 * I * x * t)) by
      funext t; push_cast; ring, integral_const_mul]
  ring

@[dlmf 18.10.E10]
theorem hermitePolyH_fourier_integral (n : ℕ) (x : ℝ) :
    (aeval (x : ℂ) (hermitePolyH n) : ℂ) = (-2 * I) ^ n * exp ((x : ℂ) ^ 2) / Real.sqrt Real.pi *
      ∫ t : ℝ, Real.exp (-(t ^ 2)) * (t : ℂ) ^ n * exp (2 * I * x * t) := by
  set K : ℕ → ℂ := fun n => ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ n *
    cexp (2 * I * x * t) with hK
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hE : cexp ((x : ℂ) ^ 2) * cexp (-(x : ℂ) ^ 2) = 1 := by rw [← Complex.exp_add]; simp
  have key : ∀ n : ℕ, (-2 * I) ^ n * cexp ((x : ℂ) ^ 2) / Real.sqrt Real.pi * K n =
      aeval (x : ℂ) (hermitePolyH n) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero =>
      simp only [hK]
      rw [integral_K_zero]
      field_simp
      simp [hE]
    | one =>
      simp only [hK]
      rw [integral_K_one, integral_K_zero, hermitePolyH_one, map_mul, aeval_X, map_ofNat]
      generalize (Real.sqrt Real.pi : ℂ) = sp at hπ ⊢
      field_simp
      linear_combination (-(x : ℂ) * I ^ 2) * hE + (-(x : ℂ)) * I_sq
    | more n ih0 ih1 =>
      simp only [hK] at ih0 ih1 ⊢
      rw [integral_K_succ_succ, aeval_hermitePolyH_succ_succ, ← ih0, ← ih1]
      generalize (∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ (n + 1) *
        cexp (2 * I * x * t)) = A
      generalize (∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ n *
        cexp (2 * I * x * t)) = B
      set P := (-2 * I) ^ n * cexp ((x : ℂ) ^ 2) / Real.sqrt Real.pi
      rw [show (-2 * I) ^ (n + 2) * cexp ((x : ℂ) ^ 2) / Real.sqrt Real.pi = P * (-2 * I) ^ 2 by
        simp only [P]; ring,
        show (-2 * I) ^ (n + 1) * cexp ((x : ℂ) ^ 2) / Real.sqrt Real.pi = P * (-2 * I) by
        simp only [P]; ring]
      linear_combination (4 * P * I * x * A + 2 * P * ((n : ℂ) + 1) * B) * I_sq
  rw [← key n]

/-- An interval antiderivative of the physicists’ Hermite polynomial. -/
@[dlmf 18.17.E3]
theorem hermitePolyH_integral (n : ℕ) (x : ℝ) :
    ∫ y : ℝ in (0 : ℝ)..x, (aeval y (hermitePolyH n) : ℝ) =
      (aeval x (hermitePolyH (n + 1)) - aeval (0 : ℝ) (hermitePolyH (n + 1))) / (2 * (n + 1)) := by
  have hd (t : ℝ) : HasDerivAt (fun y : ℝ => aeval y (hermitePolyH (n + 1)))
      (2 * (n + 1) * aeval t (hermitePolyH n)) t := by
    have h := (hermitePolyH (n + 1)).hasDerivAt_aeval t
    rw [hermitePolyH_derivative] at h
    simpa only [map_mul, aeval_C, map_ofNat, map_add, map_natCast, map_one] using h
  have hi : IntervalIntegrable (fun t : ℝ => 2 * (n + 1) * aeval t (hermitePolyH n))
      volume 0 x := (by fun_prop : Continuous _).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  rw [intervalIntegral.integral_const_mul] at h
  apply (eq_div_iff (by positivity : (2 * (n + 1) : ℝ) ≠ 0)).mpr
  nlinarith [h]

/-- An interval antiderivative of a Gaussian-weighted physicists’ Hermite polynomial. -/
@[dlmf 18.17.E4]
theorem hermitePolyH_weighted_integral (n : ℕ) (x : ℝ) :
    ∫ y : ℝ in (0 : ℝ)..x, Real.exp (-(y ^ 2)) * (aeval y (hermitePolyH (n + 1)) : ℝ) =
      aeval (0 : ℝ) (hermitePolyH n) - Real.exp (-(x ^ 2)) * aeval x (hermitePolyH n) := by
  let g : ℝ → ℝ := fun t => Real.exp (-(t ^ 2)) * aeval t (hermitePolyH n)
  have hd (t : ℝ) : HasDerivAt (fun y => -g y)
      (Real.exp (-(t ^ 2)) * aeval t (hermitePolyH (n + 1))) t := by
    have hg : DifferentiableAt ℝ g t :=
      (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => Real.exp (-(t ^ 2))) t).mul
        ((hermitePolyH n).hasDerivAt_aeval t).differentiableAt
    have ht := hg.hasDerivAt.neg
    change HasDerivAt (fun y => -g y) (-deriv g t) t at ht
    simpa only [g, DLMF.OrthogonalPolynomials.hermitePolyH_weighted_derivative, neg_mul, neg_neg]
      using ht
  have hi : IntervalIntegrable
      (fun y : ℝ => Real.exp (-(y ^ 2)) * (aeval y (hermitePolyH (n + 1)) : ℝ)) volume 0 x :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simpa only [g, zero_pow (by decide : 2 ≠ 0), neg_zero, Real.exp_zero, one_mul,
    neg_sub_neg] using h

/-- Positive integer cosine frequencies integrate to zero on the half-circle. -/
theorem integral_cos_nat_pi {k : ℕ} (hk : 0 < k) :
    (∫ phi : ℝ in (0 : ℝ)..π, (Real.cos (k*phi) : ℂ)) = 0 := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hh := integral_cos_mul_complex hk0 0 π
  have he : (fun phi : ℝ => Complex.cos ((k : ℂ)*phi)) = fun phi : ℝ => (Real.cos (k*phi) : ℂ) := by
    funext phi
    push_cast
    rfl
  rw [he] at hh
  simpa only [mul_zero, sin_zero, zero_div, sub_zero, ← ofReal_natCast, ← ofReal_mul,
    ← ofReal_sin, Real.sin_nat_mul_pi, ofReal_zero, zero_div] using hh


@[dlmf 18.17.E6]
theorem legendre_product_integral (n : ℕ) (θ ψ : ℝ) :
    legendrePolyP n (Real.cos θ) * legendrePolyP n (Real.cos ψ) = (Real.pi : ℂ)⁻¹ *
      ∫ phi : ℝ in (0 : ℝ)..Real.pi, legendrePolyP n
        (Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi) := by
  let c (k : ℕ) : ℂ := ((n-k)! : ℂ) * (n+k)! / (2^(2*k)*(n ! : ℂ)^2) *
    (Real.sin θ : ℂ)^k * jacobiPolyP k k (n-k) (Real.cos θ) *
    (Real.sin ψ : ℂ)^k * jacobiPolyP k k (n-k) (Real.cos ψ)
  have he : (fun phi : ℝ => legendrePolyP n
      (Real.cos θ*Real.cos ψ + Real.sin θ*Real.sin ψ*Real.cos phi)) =
      fun phi => legendrePolyP n (Real.cos θ)*legendrePolyP n (Real.cos ψ) +
        2*∑ k ∈ Finset.Icc 1 n, c k*(Real.cos (k*phi) : ℂ) := by
    funext phi
    exact legendre_addition n θ ψ phi
  have hsum : (∫ phi : ℝ in (0 : ℝ)..π, 2*∑ k ∈ Finset.Icc 1 n, c k*(Real.cos (k*phi) : ℂ)) =
      2*∑ k ∈ Finset.Icc 1 n, ∫ phi : ℝ in (0 : ℝ)..π, c k*(Real.cos (k*phi) : ℂ) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun k _ =>
        (show Continuous (fun phi : ℝ => c k*(Real.cos (k*phi) : ℂ)) by fun_prop).intervalIntegrable _ _)]
  rw [he, intervalIntegral.integral_add intervalIntegrable_const
    ((show Continuous (fun phi : ℝ => ∑ k ∈ Finset.Icc 1 n, c k*(Real.cos (k*phi) : ℂ)) by fun_prop).intervalIntegrable _ _ |>.const_mul _), hsum]
  have hz : ∑ k ∈ Finset.Icc 1 n, ∫ phi : ℝ in (0 : ℝ)..π, c k*(Real.cos (k*phi) : ℂ) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [intervalIntegral.integral_const_mul, integral_cos_nat_pi (by simp at hk; omega), mul_zero]
  rw [hz, mul_zero, add_zero, intervalIntegral.integral_const]
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  rw [real_smul]
  push_cast
  field_simp
  ring

/-- Gamma normalization converts Laguerre polynomials into the regularized Kummer
function. This uses Mathlib's Gamma/Pochhammer relation at regular parameters. -/
theorem laguerrePolyL_div_Gamma_eq_regularized {α : ℝ} (hα : -1 < α) (n : ℕ) (y : ℂ) :
    laguerrePolyL α n y / Gamma ((α : ℂ) + n + 1) =
      regularizedHGFun {(-(n : ℂ))} {(α : ℂ) + 1} y / (n.factorial : ℂ) := by
  have hp : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) :=
    not_neg_nat_of_re_pos (by simp; linarith)
  have hG : Gamma ((α : ℂ) + n + 1) = poch ((α : ℂ) + 1) n * Gamma ((α : ℂ) + 1) := by
    have h := Gamma_add_nat_div_Gamma_eq (n := n) ((α : ℂ) + 1) hp
    rw [show (α : ℂ) + n + 1 = (α : ℂ) + 1 + n by ring]
    exact (div_eq_iff (Gamma_ne_zero hp)).mp h
  rw [laguerrePolyL, kummerM_eq_mul_regularizedHGFun hp, hG]
  field [Gamma_ne_zero hp, poch_ne_zero_of_not_neg_nat hp n]

@[dlmf 18.17.E14]
theorem laguerrePolyL_fractional_integral {α μ x : ℝ} (hα : -1 < α) (hμ : 0 < μ) (hx : 0 < x)
    (n : ℕ) :
    (x : ℂ) ^ ((α : ℂ) + μ) * laguerrePolyL (α + μ) n x / Gamma (α + μ + n + 1 : ℂ) =
      ∫ y : ℝ in (0 : ℝ)..x, (y : ℂ) ^ (α : ℂ) * laguerrePolyL α n y / Gamma (α + n + 1 : ℂ) *
        (x - y : ℂ) ^ ((μ : ℂ) - 1) / Gamma (μ : ℂ) := by
  let f : ℝ → ℂ := fun y => (y : ℂ) ^ (α : ℂ) *
    regularizedHGFun {(-(n : ℂ))} {(α : ℂ) + 1} y *
      ((x : ℂ) - y) ^ ((μ : ℂ) - 1)
  let g : ℝ → ℂ := fun t =>
    regularizedHGFun {(-(n : ℂ))} {(α : ℂ) + 1} ((x : ℂ) * t) *
      (t : ℂ) ^ (α : ℂ) * (1 - (t : ℂ)) ^ ((μ : ℂ) - 1)
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hscale : (∫ y : ℝ in (0 : ℝ)..x, f y) =
      (x : ℂ) ^ ((α : ℂ) + μ) * ∫ t : ℝ in (0 : ℝ)..1, g t := by
    have hs := intervalIntegral.smul_integral_comp_mul_left f x (a := (0 : ℝ)) (b := 1)
    simp only [mul_zero, mul_one, Complex.real_smul] at hs
    rw [← hs, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    have hxp : (x : ℂ) * (x : ℂ) ^ (α : ℂ) * (x : ℂ) ^ ((μ : ℂ) - 1) =
        (x : ℂ) ^ ((α : ℂ) + μ) := by
      calc
        _ = (x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ (α : ℂ) *
            (x : ℂ) ^ ((μ : ℂ) - 1) := by rw [cpow_one]
        _ = _ := by
          rw [← cpow_add _ _ hx0, ← cpow_add _ _ hx0]
          congr 1
          ring
    have hptail : ((x : ℂ) * (1 - (t : ℂ))) ^ ((μ : ℂ) - 1) =
        (x : ℂ) ^ ((μ : ℂ) - 1) * (1 - (t : ℂ)) ^ ((μ : ℂ) - 1) := by
      simpa only [ofReal_sub, ofReal_one] using
        mul_cpow_ofReal_nonneg hx.le (sub_nonneg.mpr ht.2.le) ((μ : ℂ) - 1)
    dsimp [f, g]
    simp only [ofReal_mul]
    rw [show (x : ℂ) - (x : ℂ) * t = (x : ℂ) * (1 - (t : ℂ)) by ring,
      mul_cpow_ofReal_nonneg hx.le ht.1.le, hptail]
    linear_combination (t : ℂ) ^ (α : ℂ) *
      regularizedHGFun {(-(n : ℂ))} {(α : ℂ) + 1} ((x : ℂ) * t) *
      (1 - (t : ℂ)) ^ ((μ : ℂ) - 1) * hxp
  have hR := DLMF.Confluent.regularized_parameter_integral (a := -(n : ℂ))
    (b := (α : ℂ) + μ + 1) (c := (α : ℂ) + 1) (z := x)
    (by simp; linarith) (by simp; linarith)
  rw [show (α : ℂ) + 1 - 1 = (α : ℂ) by ring,
    show (α : ℂ) + μ + 1 - ((α : ℂ) + 1) = (μ : ℂ) by ring] at hR
  change regularizedHGFun {(-(n : ℂ))} {(α : ℂ) + μ + 1} x =
    1 / Gamma (μ : ℂ) * ∫ t : ℝ in (0 : ℝ)..1, g t at hR
  have hrhs : (∫ y : ℝ in (0 : ℝ)..x,
      (y : ℂ) ^ (α : ℂ) * laguerrePolyL α n y / Gamma (α + n + 1 : ℂ) *
        (x - y : ℂ) ^ ((μ : ℂ) - 1) / Gamma (μ : ℂ)) =
      (∫ y : ℝ in (0 : ℝ)..x, f y) / ((n.factorial : ℂ) * Gamma (μ : ℂ)) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro y _
    dsimp only
    rw [show (y : ℂ) ^ (α : ℂ) * laguerrePolyL α n y / Gamma (α + n + 1 : ℂ) =
      (y : ℂ) ^ (α : ℂ) * (laguerrePolyL α n y / Gamma (α + n + 1 : ℂ)) by ring,
      laguerrePolyL_div_Gamma_eq_regularized hα]
    dsimp [f]
    push_cast
    ring
  have hL := laguerrePolyL_div_Gamma_eq_regularized (by linarith : -1 < α + μ) n (x : ℂ)
  push_cast at hL
  rw [hrhs, hscale, show (x : ℂ) ^ ((α : ℂ) + μ) * laguerrePolyL (α + μ) n x /
      Gamma (α + μ + n + 1 : ℂ) = (x : ℂ) ^ ((α : ℂ) + μ) *
      (laguerrePolyL (α + μ) n x / Gamma (α + μ + n + 1 : ℂ)) by ring,
    hL]
  push_cast
  rw [hR]
  ring

@[dlmf 18.17.E15]
theorem laguerrePolyL_fractional_tail_integral {α μ x : ℝ} (hα : -1 < α) (hμ : 0 < μ) (hx : 0 ≤ x)
    (n : ℕ) :
    exp (-x) * laguerrePolyL α n x = ∫ y : ℝ in Set.Ioi x,
      exp (-y) * laguerrePolyL (α + μ) n y * (y - x : ℂ) ^ ((μ : ℂ) - 1) / Gamma (μ : ℂ) := by
  have hβ : -1 < μ - 1 := by linarith
  have hp (a : ℝ) (ha : -1 < a) : ∀ k : ℕ, (a : ℂ) + 1 ≠ -(k : ℂ) :=
    not_neg_nat_of_re_pos (by simp; linarith)
  have hΓ : Gamma (μ : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using hμ)
  have hadd (y : ℝ) : laguerrePolyL (α + μ) n ((x : ℂ) + y) =
      ∑ k ∈ Finset.range (n + 1), laguerrePolyL α k x * laguerrePolyL (μ - 1) (n - k) y := by
    have h := laguerrePolyL_addition (α : ℂ) ((μ - 1 : ℝ) : ℂ) x y n
    have hparam : (α : ℂ) + ((μ - 1 : ℝ) : ℂ) + 1 = ((α + μ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hparam, laguerreExtended_eq (hp (α + μ) (by linarith))] at h
    simp only [laguerreExtended_eq (hp α hα), laguerreExtended_eq (hp (μ - 1) hβ)] at h
    simpa only [ofReal_add, ofReal_sub, ofReal_one] using h
  let f : ℕ → ℝ → ℂ := fun k y => laguerrePolyL (μ - 1) k y *
    (y : ℂ) ^ ((μ : ℂ) - 1) * exp (-(y : ℂ))
  have hint (k : ℕ) : IntegrableOn (f k) (Set.Ioi 0) := by
    have h := integrable_laguerrePolyL_mul_monomial hβ k 0
    simpa only [IntegrableOn, f, pow_zero, mul_one, ofReal_sub, ofReal_one] using h
  have hmoment (k : ℕ) : (∫ y : ℝ in Set.Ioi 0, f k y) =
      if k = 0 then Gamma (μ : ℂ) else 0 := by
    have h := integral_laguerrePolyL_mul_monomial hβ k 0
    simp only [pow_zero, mul_one, ofReal_sub, ofReal_one, Nat.cast_zero, neg_zero,
      add_zero, sub_add_cancel] at h
    change (∫ y : ℝ in Set.Ioi 0, f k y) = _ at h
    rw [h]
    cases k with
    | zero => simp [poch_zero]
    | succ k => simp
  let F : ℝ → ℂ := fun y => exp (-(y : ℂ)) * laguerrePolyL (α + μ) n y *
    ((y : ℂ) - x) ^ ((μ : ℂ) - 1) / Gamma (μ : ℂ)
  have hshift := (measurePreserving_add_left (volume : Measure ℝ) x).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft x).measurableEmbedding F (Set.Ioi x)
  have hpre : (fun y : ℝ => x + y) ⁻¹' Set.Ioi x = Set.Ioi 0 := by
    ext y
    simp
  rw [hpre] at hshift
  change exp (-x) * laguerrePolyL α n x = ∫ y : ℝ in Set.Ioi x, F y
  rw [← hshift]
  have heq (y : ℝ) : F (x + y) = exp (-x) / Gamma (μ : ℂ) *
      ∑ k ∈ Finset.range (n + 1), laguerrePolyL α k x * f (n - k) y := by
    dsimp [F, f]
    rw [ofReal_add, add_sub_cancel_left, neg_add, exp_add, hadd]
    simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => heq y), integral_const_mul,
    integral_finsetSum _ (fun k _ => (hint (n - k)).const_mul (laguerrePolyL α k x))]
  simp only [integral_const_mul, hmoment]
  rw [Finset.sum_eq_single n]
  · simp only [Nat.sub_self, ↓reduceIte]
    field [hΓ]
  · intro k hk hkn
    have hk' : k < n := by have := Finset.mem_range.mp hk; omega
    simp [Nat.sub_ne_zero_of_lt hk']
  · simp

@[dlmf 18.17.E21_2]
theorem hermitePolyH_fourier_transform (n : ℕ) (y : ℝ) :
    (∫ x : ℝ, exp (-(x : ℂ) ^ 2) * (aeval (x : ℂ) (hermitePolyH n) : ℂ) * exp (I * x * y)) /
      Real.sqrt Real.pi = I ^ n * exp (-(y : ℂ) ^ 2 / 4) * (y : ℂ) ^ n := by
  have h := hermitePolyH_laplace_transform n (-I * y)
  have heq : ∀ x : ℝ, exp (-(x : ℂ) ^ 2) * (aeval (x : ℂ) (hermitePolyH n) : ℂ) * exp (I * x * y) =
      exp (-x * (-I * y)) * (aeval (x : ℂ) (hermitePolyH n) : ℂ) * exp (-(x : ℂ) ^ 2) := fun x => by
    rw [show -(x : ℂ) * (-I * y) = I * x * y by ring]; ring
  simp_rw [heq]
  rw [h]
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [show -(-I * (y : ℂ)) = I * y by ring, mul_pow,
    show (-I * (y : ℂ)) ^ 2 / 4 = -(y : ℂ) ^ 2 / 4 by ring_nf; rw [I_sq]; ring]
  field_simp

/-- TauCeti's Hermite functions with the positive, unit-frequency Fourier convention. -/
theorem hermiteFunction_integral (n : ℕ) (y : ℝ) :
    (∫ x : ℝ, Complex.exp (I * x * y) * (TauCeti.hermiteFunction n x : ℂ)) =
      (Real.sqrt (2 * Real.pi) : ℂ) * I ^ n * (TauCeti.hermiteFunction n y : ℂ) := by
  let s := Real.sqrt (2 * Real.pi)
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos)
  have hs0 : s ≠ 0 := hs.ne'
  have hs2 : s ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have ha : (Real.sqrt s : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hs).ne'
  have he := congrFun (TauCeti.fourier_twoPiHermiteFunction n) (-y / s)
  rw [Real.fourier_real_eq_integral_exp_smul] at he
  have hphase (x : ℝ) : (↑(-2 * Real.pi * x * (-y / s)) : ℂ) * I = I * (s * x) * y := by
    rw [show -2 * Real.pi * x * (-y / s) = s * x * y by
      calc
        _ = (2 * Real.pi) * x * y / s := by ring
        _ = _ := by rw [← hs2]; field_simp]
    push_cast
    ring
  simp_rw [hphase, smul_eq_mul, TauCeti.twoPiHermiteFunction_def, ofReal_mul] at he
  have harg : s * (-y / s) = -y := by field_simp
  change (∫ x : ℝ, exp (I * (s * x) * y) * ((Real.sqrt s : ℂ) * ↑(TauCeti.hermiteFunction n (s * x)))) =
    (-I) ^ n * ((Real.sqrt s : ℂ) * ↑(TauCeti.hermiteFunction n (s * (-y / s)))) at he
  rw [harg, TauCeti.hermiteFunction_neg, ofReal_mul, ofReal_pow, ofReal_neg, ofReal_one] at he
  have hmul : (-I) ^ n * ((Real.sqrt s : ℂ) * ((-1) ^ n * ↑(TauCeti.hermiteFunction n y))) =
      (Real.sqrt s : ℂ) * (I ^ n * ↑(TauCeti.hermiteFunction n y)) := by
    rw [show (-I) ^ n = (-1 : ℂ) ^ n * I ^ n by rw [← mul_pow]; congr 1; ring]
    have hn : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; simp
    calc
      _ = (Real.sqrt s : ℂ) * (I ^ n * ↑(TauCeti.hermiteFunction n y)) * ((-1) ^ n * (-1) ^ n) := by ring
      _ = _ := by rw [hn, mul_one]
  rw [hmul] at he
  have hleft : (∫ x : ℝ, exp (I * (s * x) * y) * ((Real.sqrt s : ℂ) * ↑(TauCeti.hermiteFunction n (s * x)))) =
      (Real.sqrt s : ℂ) * (s : ℂ)⁻¹ * ∫ x : ℝ, exp (I * x * y) * ↑(TauCeti.hermiteFunction n x) := by
    simp_rw [mul_left_comm (exp _)]
    simp_rw [← ofReal_mul s]
    rw [integral_const_mul, Measure.integral_comp_mul_left
      (fun x : ℝ => exp (I * x * y) * ↑(TauCeti.hermiteFunction n x)) s]
    simp [abs_of_pos (inv_pos.mpr hs), Complex.real_smul, mul_assoc]
  rw [hleft] at he
  have hsc0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs0
  field_simp [hsc0] at he
  exact he
/-- Evaluation of integer polynomials commutes with the real-to-complex inclusion. -/
private lemma ofReal_aeval_int (p : ℤ[X]) (x : ℝ) :
    ((aeval x p : ℝ) : ℂ) = aeval (x : ℂ) p := by
  exact (aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) x p).symm

/-- The physicists' Hermite envelope differs from TauCeti's function by a constant. -/
theorem hermitePolyH_envelope (n : ℕ) (x : ℝ) :
    exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermitePolyH n) : ℂ) =
      ((2 : ℝ) ^ (n / 2 : ℝ) * Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) : ℝ) *
        (TauCeti.hermiteFunction n x : ℂ) := by
  rw [← ofReal_aeval_int, aeval_hermitePolyH_eq_hermite, TauCeti.hermiteFunction_def]
  have hc : Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) ≠ 0 :=
    TauCeti.sqrt_factorial_mul_sqrt_pi_ne_zero n
  have he : exp (-(x : ℂ) ^ 2 / 2) = (Real.exp (-(x ^ 2 / 2)) : ℂ) := by
    rw [ofReal_exp]; congr 1; push_cast; ring
  rw [he]
  push_cast
  rw [mul_comm x (Real.sqrt 2)]
  field_simp [ofReal_ne_zero.mpr hc]
  rw [mul_div_cancel_right₀ _ (ofReal_ne_zero.mpr hc)]

/-- The probabilists' Hermite envelope is a dilation of TauCeti's Hermite function. -/
theorem hermite_envelope (n : ℕ) (x : ℝ) :
    exp (-(x : ℂ) ^ 2 / 4) * (aeval (x : ℂ) (hermite n) : ℂ) =
      (Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) : ℂ) *
        (TauCeti.hermiteFunction n (x / Real.sqrt 2) : ℂ) := by
  rw [← ofReal_aeval_int, TauCeti.hermiteFunction_def]
  have hc := TauCeti.sqrt_factorial_mul_sqrt_pi_ne_zero n
  have hr : Real.sqrt 2 ≠ 0 := by positivity
  rw [div_mul_cancel₀ x hr]
  rw [show -((x / Real.sqrt 2) ^ 2 / 2) = -(x ^ 2 / 4) by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring]
  have he : exp (-(x : ℂ) ^ 2 / 4) = (Real.exp (-(x ^ 2 / 4)) : ℂ) := by
    rw [ofReal_exp]; congr 1; push_cast; ring
  rw [he]
  push_cast
  field_simp [ofReal_ne_zero.mpr hc]
  rw [mul_div_cancel_right₀ _ (ofReal_ne_zero.mpr hc)]

@[dlmf 18.17.E21_3]
theorem hermitePolyH_fourier_eigenfunction (n : ℕ) (y : ℝ) :
    (∫ x : ℝ, exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermitePolyH n) : ℂ) * exp (I * x * y)) /
      Real.sqrt (2 * Real.pi) = I ^ n * exp (-(y : ℂ) ^ 2 / 2)
          * aeval (y : ℂ) (hermitePolyH n) := by
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  rw [show I ^ n * exp (-(y : ℂ) ^ 2 / 2) * aeval (y : ℂ) (hermitePolyH n) =
    I ^ n * (exp (-(y : ℂ) ^ 2 / 2) * aeval (y : ℂ) (hermitePolyH n)) by ring]
  simp_rw [hermitePolyH_envelope]
  simp_rw [mul_assoc, mul_comm (↑(TauCeti.hermiteFunction n _) : ℂ) (exp _)]
  rw [integral_const_mul]
  simp_rw [← mul_assoc I]
  rw [hermiteFunction_integral]
  field_simp

/-- `u^{s-1} e^{-wu}` is integrable on `(0,∞)` for `Re s, Re w > 0`. -/
theorem integrableOn_cpow_mul_cexp_neg {s w : ℂ} (hs : 0 < s.re) (hw : 0 < w.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) * cexp (-(w * u))) (Set.Ioi 0) := by
  have hb := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re - 1) (b := w.re)
    (by linarith) one_pos hw
  refine Integrable.mono' hb (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu' : 0 < u := hu
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hu', Complex.norm_exp, Real.rpow_one]
  simp

/-- Termwise Mellin–Laplace integration of a finite polynomial sum. -/
theorem integral_finite_sum_mellin_laplace {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : 0 < z.re) (s : Finset ℕ) (c : ℕ → ℂ) (d : ℕ → ℕ) :
    (∫ x : ℝ in Set.Ioi 0, exp (-a * x) *
      (∑ k ∈ s, c k * (x : ℂ) ^ d k) * (x : ℂ) ^ (z - 1)) =
      ∑ k ∈ s, c k * Gamma (z + d k) / (a : ℂ) ^ (z + d k) := by
  have hs (k : ℕ) : 0 < (z + d k).re := by
    simp only [add_re, natCast_re]; positivity
  have hterm (x : ℝ) (hx : 0 < x) :
      exp (-a * x) * (∑ k ∈ s, c k * (x : ℂ) ^ d k) * (x : ℂ) ^ (z - 1) =
      ∑ k ∈ s, c k * ((x : ℂ) ^ (z + d k - 1) * exp (-((a : ℂ) * x))) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [show z + (d k : ℂ) - 1 = (z - 1) + d k by ring,
      cpow_add _ _ (ofReal_ne_zero.mpr hx.ne'), cpow_natCast]
    rw [neg_mul]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => hterm x hx),
    integral_finsetSum _ (fun k _ =>
      (integrableOn_cpow_mul_cexp_neg (hs k) (by simpa using ha)).const_mul _)]
  simp_rw [integral_const_mul,
    DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi (z := (a : ℂ)) (hs _) (by simpa using ha), cpow_neg,
    div_eq_mul_inv, mul_assoc]

/-- The Laplace transform of `e^{-x} x^α L_n^{(α)}(x)` on `(0, ∞)` (DLMF 18.17.34). -/
@[dlmf 18.17.E34]
theorem laguerrePolyL_laplace_transform {α : ℝ} (hα : -1 < α) (n : ℕ) {z : ℂ} (hz : -1 < z.re) :
    ∫ x : ℝ in Set.Ioi 0, exp (-x * z) * laguerrePolyL α n x * exp (-x) * (x : ℂ) ^ (α : ℂ) =
      Gamma (α + n + 1 : ℂ) * z ^ n / (n.factorial * (z + 1) ^ (α + n + 1 : ℂ)) := by
  have hα' : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hw : 0 < (z + 1).re := by simp; linarith
  have hw0 : z + 1 ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have hs : ∀ k : ℕ, 0 < ((α : ℂ) + k + 1).re := fun k => by
    simp; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  -- termwise form of the integrand
  have hterm : ∀ x : ℝ, 0 < x → exp (-x * z) * laguerrePolyL α n x * exp (-x) * (x : ℂ) ^ (α : ℂ) =
      ∑ k ∈ Finset.range (n + 1), poch (α + 1 + k) (n - k) / ((n - k).factorial * k.factorial : ℂ) *
        (-1) ^ k * ((x : ℂ) ^ (((α : ℂ) + k + 1) - 1) * cexp (-((z + 1) * x))) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
    rw [laguerrePolyL_eq_sum hα', Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc : (x : ℂ) ^ (((α : ℂ) + k + 1) - 1) = (x : ℂ) ^ (α : ℂ) * (x : ℂ) ^ k := by
      rw [show ((α : ℂ) + k + 1) - 1 = (α : ℂ) + k by ring, cpow_add _ _ hx0, cpow_natCast]
    have he : cexp (-((z + 1) * x)) = cexp (-x * z) * cexp (-x) := by
      rw [← Complex.exp_add]; ring_nf
    rw [hc, he, neg_pow]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => hterm x hx)]
  rw [integral_finsetSum _ fun k _ =>
    ((integrableOn_cpow_mul_cexp_neg (hs k) hw).const_mul _)]
  simp_rw [integral_const_mul]
  rw [Finset.sum_congr rfl fun k _ => by rw [DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi (hs k) hw]]
  -- resum with the binomial theorem
  have hz1 : z = (z + 1) - 1 := by ring
  have hpowz : z ^ n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (-1) ^ k * (z + 1) ^ (n - k) := by
    conv_lhs => rw [hz1]
    rw [sub_eq_add_neg, add_comm, add_pow]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hS : ∀ k ∈ Finset.range (n + 1), poch (α + 1 + k) (n - k) / ((n - k).factorial * k.factorial : ℂ) *
      (-1) ^ k * (Gamma ((α : ℂ) + k + 1) * (z + 1) ^ (-((α : ℂ) + k + 1))) =
      Gamma ((α : ℂ) + n + 1) / (n ! * (z + 1) ^ ((α : ℂ) + n + 1)) *
        ((n.choose k : ℂ) * (-1) ^ k * (z + 1) ^ (n - k)) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hG := Gamma_add_nat_eq_poch_mul_Gamma (hs k) (n - k)
    rw [show (α : ℂ) + k + 1 + ((n - k : ℕ) : ℂ) = α + n + 1 by push_cast [Nat.cast_sub hkn]; ring,
      show (α : ℂ) + k + 1 = α + 1 + k by ring] at hG
    rw [show (α : ℂ) + k + 1 = α + 1 + k by ring, hG,
      show (α : ℂ) + n + 1 = α + 1 + k + (n - k : ℕ) by push_cast [Nat.cast_sub hkn]; ring,
      cpow_add _ _ hw0, cpow_neg, cpow_natCast, Nat.cast_choose ℂ hkn]
    have hf1 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hf2 : ((n - k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
    have hp1 : (z + 1) ^ ((α : ℂ) + 1 + k) ≠ 0 := by
      rw [cpow_def_of_ne_zero hw0]; exact exp_ne_zero _
    have hp2 : (z + 1) ^ (n - k) ≠ 0 := pow_ne_zero _ hw0
    have hfn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    field_simp
  rw [Finset.sum_congr rfl hS, ← Finset.mul_sum, ← hpowz]
  ring

@[dlmf 18.17.E28_5]
theorem laguerrePolyL_fourier_transform {α : ℝ} (hα : -1 < α) (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-x) * (x : ℂ) ^ (α : ℂ) * laguerrePolyL α n x * exp (I * x * y) =
      Gamma (α + n + 1 : ℂ) * (-I * y) ^ n / (n.factorial * (1 - I * y) ^ (α + n + 1 : ℂ)) := by
  have h := laguerrePolyL_laplace_transform hα n (z := -I * y) (by simp)
  rw [show -I * (y : ℂ) + 1 = 1 - I * y by ring] at h
  rw [← h]
  congr 1; funext x
  rw [show -(x : ℂ) * (-I * y) = I * x * y by ring]
  ring

/-- Complex-exponent version of `integral_jacobi_weight`. -/
theorem integral_jacobi_weight_cpow {a b : ℂ} (ha : -1 < a.re) (hb : -1 < b.re) :
    (∫ t : ℝ in (-1 : ℝ)..1, (1 - (t : ℂ)) ^ a * (1 + (t : ℂ)) ^ b) =
      (2 : ℂ) ^ (a + b + 1) * (Gamma (a + 1) * Gamma (b + 1) / Gamma (a + b + 2)) := by
  have he := intervalIntegral.integral_comp_add_right
    (fun t : ℝ => (t : ℂ) ^ b * ((2 : ℂ) - t) ^ a) 1
    (a := (-1 : ℝ)) (b := 1)
  norm_num only [neg_add_cancel, one_add_one_eq_two] at he
  have hm := integral_cpow_mul_sub_cpow (a := b) (b := a) hb ha
    (by norm_num : (0 : ℝ) < 2)
  norm_num only [ofReal_ofNat] at hm
  rw [hm] at he
  calc
    _ = ∫ t : ℝ in (-1 : ℝ)..1, ((t + 1 : ℝ) : ℂ) ^ b *
        ((2 : ℂ) - ((t + 1 : ℝ) : ℂ)) ^ a := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      push_cast
      rw [show (2 : ℂ) - ((t : ℂ) + 1) = 1 - t by ring, add_comm (t : ℂ) 1]
      ring
    _ = _ := by rw [he, add_comm b a, mul_comm (Gamma (b + 1))]

/-- Complex-exponent version of `intervalIntegrable_jacobi_weight`. -/
theorem intervalIntegrable_jacobi_weight_cpow {a b : ℂ} (ha : -1 < a.re) (hb : -1 < b.re) :
    IntervalIntegrable (fun t : ℝ => (1 - (t : ℂ)) ^ a * (1 + (t : ℂ)) ^ b) volume (-1) 1 := by
  have hi := (intervalIntegrable_cpow_mul_sub_cpow (a := b) (b := a)
    hb ha (show (0 : ℝ) < 2 by norm_num)).comp_add_right 1
  norm_num only [zero_sub, sub_self, sub_add_cancel] at hi
  convert hi using 1
  · ext t
    push_cast
    rw [show (2 : ℂ) - ((t : ℂ) + 1) = 1 - t by ring]
    rw [add_comm (t : ℂ) 1]
    ring


@[dlmf 18.17.E36]
theorem jacobi_mellin_transform {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1,
        (1 - (x : ℂ)) ^ (z - 1) * (1 + (x : ℂ)) ^ (β : ℂ) * jacobiPolyP α β n x =
      (2 : ℂ) ^ ((β : ℂ) + z) * Gamma z * Gamma (1 + (β : ℂ) + n) * poch (1 + α - z) n /
      (n.factorial * Gamma (1 + β + z + n)) := by
  set a : ℂ := (n : ℂ) + α + β + 1 with ha
  set c : ℂ := (α : ℂ) + 1 with hc
  set C : ℕ → ℂ := fun k => poch c n / n ! * gaussHGCoeff (-(n : ℂ)) a c k / 2 ^ k with hC
  have hexp : Set.EqOn
      (fun x : ℝ => (1 - (x : ℂ)) ^ (z - 1) * (1 + (x : ℂ)) ^ (β : ℂ) * jacobiPolyP α β n x)
      (fun x : ℝ => ∑ k ∈ Finset.range (n + 1),
        C k * ((1 - (x : ℂ)) ^ (z - 1 + k) * (1 + (x : ℂ)) ^ (β : ℂ))) (Set.Ioo (-1) 1) := by
    intro x hx
    have h1 : (1 - (x : ℂ)) ≠ 0 := by
      rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (by linarith [hx.2])
    simp only [jacobiPolyP, ordinaryHypergeometric_eq_sum_neg_nat, Finset.mul_sum, hC]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cpow_add _ _ h1, cpow_natCast, div_pow, ← hc, ← ha]
    have h2 : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
    field_simp
  have hint (k : ℕ) : IntervalIntegrable
      (fun x : ℝ => C k * ((1 - (x : ℂ)) ^ (z - 1 + k) * (1 + (x : ℂ)) ^ (β : ℂ)))
      volume (-1) 1 :=
    (intervalIntegrable_jacobi_weight_cpow (a := z - 1 + k) (b := (β : ℂ))
      (by simp; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (by simpa using hβ)).const_mul _
  rw [intervalIntegral.integral_congr_Ioo_of_le (by norm_num) hexp,
    intervalIntegral.integral_finsetSum fun k _ => hint k]
  simp only [intervalIntegral.integral_const_mul]
  have hzb : 0 < (z + β + 1).re := by simp; linarith
  have hc0 : 0 < c.re := by simp [hc]; linarith
  have hb1 : 0 < ((β : ℂ) + 1).re := by simp; linarith
  have hsum : 1 + a + z - c - n = z + β + 1 := by simp only [ha, hc]; ring
  set K : ℂ := poch c n / n ! * (2 : ℂ) ^ (z + β) * Gamma z * Gamma ((β : ℂ) + 1) /
    Gamma (z + β + 1) with hK
  have hterm : ∀ k ∈ Finset.range (n + 1),
      C k * ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ)) ^ (z - 1 + k) * (1 + (x : ℂ)) ^ (β : ℂ) =
      K * (poch (-(n : ℂ)) k * poch a k * poch z k /
        (poch c k * poch (1 + a + z - c - n) k * k !)) := by
    intro k _
    rw [integral_jacobi_weight_cpow (by simp; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
      (by simpa using hβ)]
    rw [show z - 1 + k + 1 = z + k by ring, show z - 1 + k + β + 2 = (z + β + 1) + k by ring,
      Gamma_add_nat_eq_poch_mul_Gamma hz, Gamma_add_nat_eq_poch_mul_Gamma hzb,
      show z - 1 + k + β + 1 = (z + β) + k by ring, cpow_add _ _ two_ne_zero, cpow_natCast,
      hsum]
    have h1 : poch (z + β + 1) k ≠ 0 := poch_ne_zero_of_re_pos hzb k
    have h2 : poch c k ≠ 0 := poch_ne_zero_of_re_pos hc0 k
    have h3 : Gamma (z + β + 1) ≠ 0 := Gamma_ne_zero_of_re_pos hzb
    have h4 : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
    have h5 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    simp only [hC, hK, gaussHGCoeff]
    field_simp
  have hcn : ∀ k : ℕ, c ≠ -k := fun k h => by
    have := congrArg re h; simp [hc] at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hd : poch (1 + a + z - c - n) n ≠ 0 := by rw [hsum]; exact poch_ne_zero_of_re_pos hzb n
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, pfaff_saalschutz n hcn hd]
  rw [show c - a - z = -((n : ℂ) + β + z) by simp only [ha, hc]; ring,
    show c - a = -((n : ℂ) + β) by simp only [ha, hc]; ring,
    DLMF.Gamma.poch_neg_eq, DLMF.Gamma.poch_neg_eq,
    show (n : ℂ) + β - n + 1 = β + 1 by ring, show (n : ℂ) + β + z - n + 1 = z + β + 1 by ring,
    show c - z = 1 + α - z by simp only [hc]; ring,
    show (1 : ℂ) + β + n = (β + 1) + n by ring, show (1 : ℂ) + β + z + n = (z + β + 1) + n by ring,
    Gamma_add_nat_eq_poch_mul_Gamma hb1, Gamma_add_nat_eq_poch_mul_Gamma hzb]
  have h1 : poch (z + β + 1) n ≠ 0 := poch_ne_zero_of_re_pos hzb n
  have h2 : poch c n ≠ 0 := poch_ne_zero_of_re_pos hc0 n
  have h3 : Gamma (z + β + 1) ≠ 0 := Gamma_ne_zero_of_re_pos hzb
  have h5 : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have h6 : ((-1 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [hK]
  rw [add_comm (β : ℂ) z]
  field_simp

/-- The substitution `s = 1 - 2x²` on `(0, 1)`, with no regularity assumption on `F`. -/
theorem integral_mul_comp_one_sub_two_sq (F : ℝ → ℂ) :
    (∫ x : ℝ in (0 : ℝ)..1, (x : ℂ) * F (1 - 2 * x ^ 2)) =
      (1 / 4 : ℂ) * ∫ s : ℝ in (-1 : ℝ)..1, F s := by
  have himg : (fun x : ℝ => 1 - 2 * x ^ 2) '' Set.Ioo 0 1 = Set.Ioo (-1) 1 := by
    ext s
    constructor
    · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
      constructor <;> nlinarith
    · rintro ⟨hs0, hs1⟩
      refine ⟨Real.sqrt ((1 - s) / 2), ⟨Real.sqrt_pos.mpr (by linarith), ?_⟩, ?_⟩
      · rw [Real.sqrt_lt' one_pos]; linarith
      · show 1 - 2 * Real.sqrt ((1 - s) / 2) ^ 2 = s
        rw [Real.sq_sqrt (by linarith)]; ring
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun x : ℝ => 1 - 2 * x ^ 2) (-(4 * x)) (Set.Ioo 0 1) x := by
    intro x _
    have := ((hasDerivAt_pow 2 x).const_mul 2).const_sub 1
    convert this.hasDerivWithinAt using 1
    push_cast; ring
  have hinj : Set.InjOn (fun x : ℝ => 1 - 2 * x ^ 2) (Set.Ioo 0 1) := by
    intro x hx y hy hxy
    have h2 : x ^ 2 = y ^ 2 := by simp only at hxy; linarith
    exact (pow_left_inj₀ hx.1.le hy.1.le two_ne_zero).mp h2
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj F
  rw [himg] at he
  rw [intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, he, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  rw [abs_neg, abs_of_pos (by linarith [hx.1]), Complex.real_smul]
  push_cast
  ring


/-- The substitution `s = 1 - 2x²` turns `(1-x²)^μ x^v` on `(0, 1)` into a Jacobi weight. -/
theorem integral_one_sub_sq_cpow_mul_cpow (μ v : ℂ) (G : ℝ → ℂ) :
    (∫ x : ℝ in (0 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ μ * (x : ℂ) ^ v * G (1 - 2 * x ^ 2)) =
      (1 / 4 : ℂ) * (2 : ℂ) ^ (-(μ + (v - 1) / 2)) * ∫ s : ℝ in (-1 : ℝ)..1,
        (1 - (s : ℂ)) ^ ((v - 1) / 2) * (1 + (s : ℂ)) ^ μ * G s := by
  set w : ℂ := (v - 1) / 2 with hw
  rw [mul_assoc, ← intervalIntegral.integral_const_mul, ← integral_mul_comp_one_sub_two_sq]
  refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun x hx => ?_
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.1.ne'
  have hA : ((2 : ℂ) * (1 - (x : ℂ) ^ 2)) ^ μ = (2 : ℂ) ^ μ * (1 - (x : ℂ) ^ 2) ^ μ := by
    have := mul_cpow_ofReal_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
      (show (0 : ℝ) ≤ 1 - x ^ 2 by nlinarith [hx.1, hx.2]) μ
    push_cast at this; exact this
  have hB : ((2 : ℂ) * (x : ℂ) ^ 2) ^ w = (2 : ℂ) ^ w * ((x : ℂ) ^ 2) ^ w := by
    have := mul_cpow_ofReal_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (sq_nonneg x) w
    push_cast at this; exact this
  have hC : ((x : ℂ) ^ 2) ^ w = (x : ℂ) ^ (2 * w) := by
    rw [cpow_mul _ (by rw [← ofReal_log hx.1.le]; simp; positivity)
      (by rw [← ofReal_log hx.1.le]; simp; positivity), cpow_two]
  have hD : (x : ℂ) ^ v = (x : ℂ) * (x : ℂ) ^ (2 * w) := by
    rw [hw, show 2 * ((v - 1) / 2) = v - 1 by ring, cpow_sub _ _ hx0, cpow_one]
    field_simp
  have h2 : (2 : ℂ) ^ (-(μ + w)) * (2 : ℂ) ^ w * (2 : ℂ) ^ μ = 1 := by
    rw [cpow_neg, cpow_add _ _ two_ne_zero]
    have : (2 : ℂ) ^ μ * (2 : ℂ) ^ w ≠ 0 := mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl two_ne_zero))
      (cpow_ne_zero_iff.mpr (Or.inl two_ne_zero))
    field_simp
  push_cast
  rw [show (1 : ℂ) - (1 - 2 * (x : ℂ) ^ 2) = 2 * (x : ℂ) ^ 2 by ring,
    show (1 : ℂ) + (1 - 2 * (x : ℂ) ^ 2) = 2 * (1 - (x : ℂ) ^ 2) by ring, hA, hB, hC, hD]
  linear_combination -(x : ℂ) * (x : ℂ) ^ (2 * w) * (1 - (x : ℂ) ^ 2) ^ μ *
    G (1 - 2 * x ^ 2) * h2


@[dlmf 18.17.E38]
theorem legendre_even_mellin_transform {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, legendrePolyP (2 * n) x * (x : ℂ) ^ (z - 1) =
      (-1 : ℂ) ^ n * poch (1 / 2 - z / 2) n / (2 * poch (z / 2) (n + 1)) := by
  have hrw : ∀ x : ℝ, legendrePolyP (2 * n) x * (x : ℂ) ^ (z - 1) =
      (1 - (x : ℂ) ^ 2) ^ (0 : ℂ) * (x : ℂ) ^ (z - 1) *
        ((-1 : ℂ) ^ n *
          jacobiPolyP ((-1 / 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) n ((1 - 2 * x ^ 2 : ℝ) : ℂ)) := by
    intro x
    have hp : poch (1 / 2 : ℂ) n ≠ 0 := poch_ne_zero_of_re_pos (by norm_num) n
    rw [cpow_zero, one_mul, legendre_eq_ultrasphPoly,
      ultrasphPoly_quadratic_even (by norm_num : -1 / 2 < (1 / 2 : ℂ).re),
      show 2 * (x : ℂ) ^ 2 - 1 = -((1 - 2 * x ^ 2 : ℝ) : ℂ) by push_cast; ring,
      jacobi_reflection (by norm_num) (by norm_num), div_self hp]
    push_cast
    ring_nf
  rw [intervalIntegral.integral_congr (fun x _ => hrw x),
    integral_one_sub_sq_cpow_mul_cpow 0 (z - 1)
      (fun s => (-1 : ℂ) ^ n * jacobiPolyP ((-1 / 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) n s)]
  have hz2 : 0 < (z / 2).re := by simp; linarith
  have hJ := jacobi_mellin_transform (α := -1 / 2) (β := 0) (by norm_num) (by norm_num) hz2 n
  have hint : (∫ s : ℝ in (-1 : ℝ)..1, (1 - (s : ℂ)) ^ ((z - 1 - 1) / 2) * (1 + (s : ℂ)) ^ (0 : ℂ) *
      ((-1 : ℂ) ^ n * jacobiPolyP ((-1 / 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) n s)) =
      (-1 : ℂ) ^ n * ∫ s : ℝ in (-1 : ℝ)..1, (1 - (s : ℂ)) ^ (z / 2 - 1) *
        (1 + (s : ℂ)) ^ ((0 : ℝ) : ℂ) * jacobiPolyP ((-1 / 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) n s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [ofReal_zero]
    rw [show (z - 1 - 1) / 2 = z / 2 - 1 by ring]
    ring
  rw [hint, hJ]
  have hG : Gamma (1 + ((0 : ℝ) : ℂ) + z / 2 + n) = poch (z / 2) (n + 1) * Gamma (z / 2) := by
    rw [← Gamma_add_nat_eq_poch_mul_Gamma hz2]; push_cast; ring_nf
  have hG1 : Gamma (1 + ((0 : ℝ) : ℂ) + n) = n ! := by
    rw [show 1 + ((0 : ℝ) : ℂ) + n = (n : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
  have h2 : (2 : ℂ) ^ (-((0 : ℂ) + (z - 1 - 1) / 2)) * (2 : ℂ) ^ (((0 : ℝ) : ℂ) + z / 2) = 2 := by
    rw [← cpow_add _ _ two_ne_zero, show -((0 : ℂ) + (z - 1 - 1) / 2) + (((0 : ℝ) : ℂ) + z / 2) = 1
      by push_cast; ring, cpow_one]
  rw [hG, hG1]
  have hp : poch (z / 2) (n + 1) ≠ 0 := poch_ne_zero_of_re_pos hz2 _
  have hg : Gamma (z / 2) ≠ 0 := Gamma_ne_zero_of_re_pos hz2
  have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [show (1 : ℂ) + ((-1 / 2 : ℝ) : ℂ) - z / 2 = 1 / 2 - z / 2 by push_cast; ring]
  generalize (2 : ℂ) ^ (-((0 : ℂ) + (z - 1 - 1) / 2)) = P at h2 ⊢
  generalize (2 : ℂ) ^ (((0 : ℝ) : ℂ) + z / 2) = Q at h2 ⊢
  generalize poch (1 / 2 - z / 2) n = R
  field_simp
  linear_combination 2 * R * h2

@[dlmf 18.17.E39]
theorem legendre_odd_mellin_transform {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, legendrePolyP (2 * n + 1) x * (x : ℂ) ^ (z - 1) =
      (-1 : ℂ) ^ n * poch (1 - z / 2) n / (2 * poch (1 / 2 + z / 2) (n + 1)) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hrw : Set.EqOn (fun x : ℝ => legendrePolyP (2 * n + 1) x * (x : ℂ) ^ (z - 1))
      (fun x : ℝ => (1 - (x : ℂ) ^ 2) ^ (0 : ℂ) * (x : ℂ) ^ z *
        ((-1 : ℂ) ^ n * jacobiPolyP ((1 / 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) n ((1 - 2 * x ^ 2 : ℝ) : ℂ)))
      (Set.Ioo 0 1) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.1.ne'
    have hp : poch (1 / 2 : ℂ) (n + 1) ≠ 0 := poch_ne_zero_of_re_pos (by norm_num) _
    simp only
    rw [cpow_zero, one_mul, legendre_eq_ultrasphPoly,
      ultrasphPoly_quadratic_odd (by norm_num : -1 / 2 < (1 / 2 : ℂ).re),
      show 2 * (x : ℂ) ^ 2 - 1 = -((1 - 2 * x ^ 2 : ℝ) : ℂ) by push_cast; ring,
      jacobi_reflection (by norm_num) (by norm_num), div_self hp,
      show z = (z - 1) + 1 by ring, cpow_add _ _ hx0, cpow_one, show z - 1 + 1 - 1 = z - 1 by ring]
    push_cast
    ring_nf
  rw [intervalIntegral.integral_congr_Ioo_of_le (by norm_num) hrw,
    integral_one_sub_sq_cpow_mul_cpow 0 z
      (fun s => (-1 : ℂ) ^ n * jacobiPolyP ((1 / 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) n s)]
  have hw : 0 < (1 / 2 + z / 2).re := by simp; linarith
  have hJ := jacobi_mellin_transform (α := 1 / 2) (β := 0) (by norm_num) (by norm_num) hw n
  have hint : (∫ s : ℝ in (-1 : ℝ)..1, (1 - (s : ℂ)) ^ ((z - 1) / 2) * (1 + (s : ℂ)) ^ (0 : ℂ) *
      ((-1 : ℂ) ^ n * jacobiPolyP ((1 / 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) n s)) =
      (-1 : ℂ) ^ n * ∫ s : ℝ in (-1 : ℝ)..1, (1 - (s : ℂ)) ^ (1 / 2 + z / 2 - 1) *
        (1 + (s : ℂ)) ^ ((0 : ℝ) : ℂ) * jacobiPolyP ((1 / 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) n s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [ofReal_zero]
    rw [show (z - 1) / 2 = 1 / 2 + z / 2 - 1 by ring]
    ring
  rw [hint, hJ]
  have hG : Gamma (1 + ((0 : ℝ) : ℂ) + (1 / 2 + z / 2) + n) =
      poch (1 / 2 + z / 2) (n + 1) * Gamma (1 / 2 + z / 2) := by
    rw [← Gamma_add_nat_eq_poch_mul_Gamma hw]; push_cast; ring_nf
  have hG1 : Gamma (1 + ((0 : ℝ) : ℂ) + n) = n ! := by
    rw [show 1 + ((0 : ℝ) : ℂ) + n = (n : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
  have h2 : (2 : ℂ) ^ (-((0 : ℂ) + (z - 1) / 2)) * (2 : ℂ) ^ (((0 : ℝ) : ℂ) + (1 / 2 + z / 2)) =
      2 := by
    rw [← cpow_add _ _ two_ne_zero, show -((0 : ℂ) + (z - 1) / 2) +
      (((0 : ℝ) : ℂ) + (1 / 2 + z / 2)) = 1 by push_cast; ring, cpow_one]
  rw [hG, hG1]
  have hp : poch (1 / 2 + z / 2) (n + 1) ≠ 0 := poch_ne_zero_of_re_pos hw _
  have hg : Gamma (1 / 2 + z / 2) ≠ 0 := Gamma_ne_zero_of_re_pos hw
  have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [show (1 : ℂ) + ((1 / 2 : ℝ) : ℂ) - (1 / 2 + z / 2) = 1 - z / 2 by push_cast; ring]
  generalize (2 : ℂ) ^ (-((0 : ℂ) + (z - 1) / 2)) = P at h2 ⊢
  generalize (2 : ℂ) ^ (((0 : ℝ) : ℂ) + (1 / 2 + z / 2)) = Q at h2 ⊢
  generalize poch (1 - z / 2) n = R
  generalize Gamma (1 / 2 + z / 2) = A at hg ⊢
  generalize poch (1 / 2 + z / 2) (n + 1) = B at hp ⊢
  field_simp
  linear_combination 2 * R * h2

@[dlmf 18.17.E44]
theorem legendre_singular_integral (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    ∫ t : ℝ in (-1 : ℝ)..1, (legendrePolyP n x - legendrePolyP n t) / (|x - t| : ℝ) =
      2 * (∑ k ∈ Finset.range n, ((k + 1 : ℂ)⁻¹)) * legendrePolyP n x := by
  simpa only [LegendreSingular.dq, LegendreSingular.harmonicSum] using
    LegendreSingular.singular_integral n hx

/-- Vandermonde convolution applied to an arbitrary finite coefficient sequence. -/
private lemma binomial_double_sum (m n : ℕ) (f : ℕ → ℂ) :
    (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      (m.choose i : ℂ) * (n.choose j : ℂ) * f (i + j)) =
    ∑ k ∈ Finset.range (m + n + 1), ((m + n).choose k : ℂ) * f k := by
  let ell : ℂ[X] →+ ℂ := {
    toFun := fun p => p.sum (fun k c => c * f k)
    map_zero' := sum_zero_index _
    map_add' := fun p q => sum_add_index p q _ (by simp) (by intros; ring) }
  have hs (k : ℕ) : (X + 1 : ℂ[X]) ^ k =
      ∑ i ∈ Finset.range (k + 1), monomial i (k.choose i : ℂ) := by
    have h := as_sum_range' ((X + 1 : ℂ[X]) ^ k) (k + 1)
      (by simpa only [← C_1, natDegree_pow_X_add_C] using Nat.lt_succ_self k)
    simpa only [coeff_X_add_one_pow] using h
  have h := congrArg ell (pow_add (X + 1 : ℂ[X]) m n).symm
  rw [hs m, hs n, hs (m + n), Finset.sum_mul] at h
  simp only [Finset.mul_sum, map_sum, monomial_mul_monomial] at h
  change (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
    (monomial (i + j) ((m.choose i : ℂ) * (n.choose j : ℂ))).sum (fun k c => c * f k)) =
    (∑ k ∈ Finset.range (m + n + 1),
      (monomial k ((m + n).choose k : ℂ)).sum (fun k c => c * f k)) at h
  simpa only [sum_monomial_index, zero_mul] using h

/-- Finite Gamma-normalized expansion of the Laguerre polynomial divided by its value at zero. -/
theorem laguerrePolyL_normalized_sum {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    laguerrePolyL α n x / laguerrePolyL α n 0 =
      Gamma (α + 1) * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * (-x) ^ i / Gamma (α + 1 + i) := by
  have ha : 0 < (α + 1).re := by simp; linarith
  have hc := not_neg_nat_of_re_pos ha
  have hp : poch (α + 1) n / (n.factorial : ℂ) ≠ 0 :=
    div_ne_zero (poch_ne_zero_of_not_neg_nat hc n) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  rw [laguerrePolyL_at_zero, laguerrePolyL, mul_div_cancel_left₀ _ hp,
    kummerM_eq_sum_neg_nat, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpi := poch_ne_zero_of_not_neg_nat hc i
  have hgi := Gamma_ne_zero_of_re_pos (show 0 < (α + 1 + i).re by
    simp; have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i); linarith)
  have hga := Gamma_ne_zero_of_re_pos ha
  have hg := Gamma_add_nat_div_Gamma_eq (n := i) (α + 1) hc
  change Gamma (α + 1 + i) / Gamma (α + 1) = poch (α + 1) i at hg
  have hfi : (i.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr i.factorial_ne_zero
  rw [poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  rw [← hg, neg_pow]
  field_simp
  ring

/-- Power expansion of a normalized Laguerre polynomial with its endpoint weight. -/
theorem laguerrePolyL_normalized_weight_sum {α : ℂ} (hα : -1 < α.re)
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ α * laguerrePolyL α n t / laguerrePolyL α n 0 =
      Gamma (α + 1) * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * (-1) ^ i / Gamma (α + 1 + i) * (t : ℂ) ^ (α + i) := by
  rw [mul_div_assoc, laguerrePolyL_normalized_sum hα, ← mul_assoc, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_natCast, neg_pow]
  ring

@[dlmf 18.17.E47]
theorem laguerrePolyL_convolution {α β x : ℝ} (hα : -1 < α) (hβ : -1 < β) (hx : 0 < x) (m n : ℕ) :
    ∫ t : ℝ in (0 : ℝ)..x, (t : ℂ) ^ (α : ℂ) * laguerrePolyL α m t / laguerrePolyL α m 0 *
      (x - t : ℂ) ^ (β : ℂ) * laguerrePolyL β n (x - t) / laguerrePolyL β n 0 =
      Gamma (α + 1 : ℂ) * Gamma (β + 1 : ℂ) / Gamma (α + β + 2 : ℂ) *
      (x : ℂ) ^ (α + β + 1 : ℂ) * laguerrePolyL (α + β + 1) (m + n) x
          / laguerrePolyL (α + β + 1) (m + n) 0 := by
  have ha : -1 < (α : ℂ).re := hα
  have hb : -1 < (β : ℂ).re := hβ
  have hc : -1 < ((α + β + 1 : ℝ) : ℂ).re := by simp; linarith
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  let F (i j : ℕ) (t : ℝ) : ℂ :=
    (m.choose i : ℂ) * (n.choose j : ℂ) * (-1) ^ (i + j) /
      (Gamma ((α : ℂ) + 1 + i) * Gamma ((β : ℂ) + 1 + j)) *
      ((t : ℂ) ^ ((α : ℂ) + i) * ((x : ℂ) - t) ^ ((β : ℂ) + j))
  have hai (i : ℕ) : -1 < ((α : ℂ) + i).re := by
    simp; have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i); linarith
  have hbj (j : ℕ) : -1 < ((β : ℂ) + j).re := by
    simp; have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
  have hi (i j : ℕ) : IntervalIntegrable (F i j) volume 0 x :=
    (intervalIntegrable_cpow_mul_sub_cpow (hai i) (hbj j) hx).const_mul _
  have hmoment (i j : ℕ) : (∫ t : ℝ in (0 : ℝ)..x, F i j t) =
      (x : ℂ) ^ ((α : ℂ) + β + 1) *
        ((m.choose i : ℂ) * (n.choose j : ℂ) * (- (x : ℂ)) ^ (i + j) /
          Gamma ((α : ℂ) + β + 2 + (i + j : ℕ))) := by
    dsimp only [F]
    rw [intervalIntegral.integral_const_mul, integral_cpow_mul_sub_cpow (hai i) (hbj j) hx]
    have hga : Gamma ((α : ℂ) + 1 + i) ≠ 0 :=
      Gamma_ne_zero_of_re_pos (by simp; have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i); linarith)
    have hgb : Gamma ((β : ℂ) + 1 + j) ≠ 0 :=
      Gamma_ne_zero_of_re_pos (by simp; have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith)
    rw [show (α : ℂ) + i + ((β : ℂ) + j) + 1 =
        ((α : ℂ) + β + 1) + (i + j : ℕ) by push_cast; ring,
      cpow_add _ _ hx0, cpow_natCast,
      show (α : ℂ) + i + 1 = (α : ℂ) + 1 + i by ring,
      show (β : ℂ) + j + 1 = (β : ℂ) + 1 + j by ring,
      show (α : ℂ) + i + ((β : ℂ) + j) + 2 =
        (α : ℂ) + β + 2 + (i + j : ℕ) by push_cast; ring]
    rw [neg_pow (x : ℂ)]
    field_simp
  have he : (∫ t : ℝ in (0 : ℝ)..x, (t : ℂ) ^ (α : ℂ) * laguerrePolyL α m t / laguerrePolyL α m 0 *
      (x - t : ℂ) ^ (β : ℂ) * laguerrePolyL β n (x - t) / laguerrePolyL β n 0) =
      Gamma ((α : ℂ) + 1) * Gamma ((β : ℂ) + 1) *
        ∫ t : ℝ in (0 : ℝ)..x, ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1), F i j t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le hx.le
    intro t ht
    dsimp only
    rw [← ofReal_sub x t]
    have ht' : 0 < x - t := sub_pos.mpr ht.2
    rw [show (t : ℂ) ^ (α : ℂ) * laguerrePolyL α m t / laguerrePolyL α m 0 *
        ((x - t : ℝ) : ℂ) ^ (β : ℂ) * laguerrePolyL β n ((x - t : ℝ) : ℂ) / laguerrePolyL β n 0 =
        ((t : ℂ) ^ (α : ℂ) * laguerrePolyL α m t / laguerrePolyL α m 0) *
        (((x - t : ℝ) : ℂ) ^ (β : ℂ) * laguerrePolyL β n ((x - t : ℝ) : ℂ) / laguerrePolyL β n 0) by
            ring,
      laguerrePolyL_normalized_weight_sum ha m ht.1, laguerrePolyL_normalized_weight_sum hb n ht']
    simp only [Finset.mul_sum, Finset.sum_mul, F, ofReal_sub, pow_add]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, intervalIntegral.integral_finsetSum
    (f := fun i t => ∑ j ∈ Finset.range (n + 1), F i j t)
    (fun i _ => by
      convert IntervalIntegrable.sum (Finset.range (n + 1)) (fun j _ => hi i j) using 1
      ext t
      simp)]
  have hs (i : ℕ) : (∫ t : ℝ in (0 : ℝ)..x, ∑ j ∈ Finset.range (n + 1), F i j t) =
      ∑ j ∈ Finset.range (n + 1), ∫ t : ℝ in (0 : ℝ)..x, F i j t :=
    intervalIntegral.integral_finsetSum (fun j _ => hi i j)
  simp_rw [hs, hmoment]
  simp only [← Finset.mul_sum, div_eq_mul_inv, mul_assoc]
  have hbin := binomial_double_sum m n (fun k => (- (x : ℂ)) ^ k *
    (Gamma ((α : ℂ) + β + 2 + k))⁻¹)
  simp only [mul_assoc, ← Finset.mul_sum] at hbin
  rw [hbin]
  have hgc : Gamma ((α : ℂ) + β + 2) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hn := laguerrePolyL_normalized_sum hc (m + n) (x : ℂ)
  push_cast at hn
  rw [show (α : ℂ) + β + 1 + 1 = (α : ℂ) + β + 2 by ring] at hn
  simp only [div_eq_mul_inv, mul_assoc] at hn
  rw [hn]
  field_simp

@[dlmf 18.17.E48]
theorem hermitePolyH_convolution (m n : ℕ) (x : ℝ) :
    ∫ y : ℝ, (aeval y (hermitePolyH m) : ℝ) * Real.exp (-(y ^ 2)) *
      aeval (x - y) (hermitePolyH n) * Real.exp (-((x - y) ^ 2)) =
      Real.sqrt Real.pi * (2 : ℝ) ^ (-((m : ℝ) + n + 1) / 2) *
      aeval (x / Real.sqrt 2) (hermitePolyH (m + n)) * Real.exp (-(x ^ 2) / 2) := by
  let g (j : ℕ) (t : ℝ) := (aeval t (hermitePolyH j) : ℝ) * Real.exp (-(t ^ 2))
  have hg (j : ℕ) (t : ℝ) : HasDerivAt (g j) (-g (j + 1) t) t := by
    simpa only [g, aeval_hermitePolyH_eq_eval] using hasDerivAt_hermite_gauss j t
  have hi (j k : ℕ) : Integrable (fun t => g j t * g k (x - t)) := by
    let q := hermitePolyHR j * (hermitePolyHR k).comp (C x - X)
    have he := (TauCeti.integrable_eval_mul_exp_neg_sq q).mul_bdd
      (by fun_prop : Continuous (fun t : ℝ => Real.exp (-((x - t) ^ 2)))).aestronglyMeasurable
      (Eventually.of_forall fun t => show ‖Real.exp (-((x - t) ^ 2))‖ ≤ (1 : ℝ) by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
        exact neg_nonpos.mpr (sq_nonneg _))
    apply he.congr
    filter_upwards [] with t
    simp only [q, g, eval_mul, eval_comp, eval_sub, eval_C, eval_X,
      aeval_hermitePolyH_eq_eval]
    ring
  have htransfer (j k : ℕ) : (∫ t, g (j + 1) t * g k (x - t)) =
      ∫ t, g j t * g (k + 1) (x - t) := by
    have hv (t : ℝ) : HasDerivAt (fun t => g k (x - t)) (g (k + 1) (x - t)) t := by
      convert (hg k (x - t)).comp t ((hasDerivAt_id t).const_sub x) using 1 <;> first | rfl | ring
    have he := integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun t _ => hg j t) (fun t _ => hv t) (hi j (k + 1))
      ((hi (j + 1) k).neg.congr (Eventually.of_forall fun t => by simp)) (hi j k)
    rw [← integral_neg] at he
    simpa only [neg_mul, neg_neg] using he.symm
  have hreduce (j k : ℕ) : (∫ t, g j t * g k (x - t)) = ∫ t, g 0 t * g (j + k) (x - t) := by
    induction j generalizing k with
    | zero => simp
    | succ j ih => rw [htransfer, ih]; congr 1; funext t; congr 2; omega
  let s := Real.sqrt 2
  let r := s⁻¹
  let v := x / s
  have hs : 0 < s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = 2 := by simp [s]
  have hr : 0 < r := inv_pos.mpr hs
  have hab : r ^ 2 + (-r) ^ 2 = 1 := by dsimp [r]; field_simp; nlinarith
  have hmoment (k : ℕ) : (∫ u : ℝ, (aeval (r * v - r * u) (hermitePolyH k) : ℝ) *
      Real.exp (-(u ^ 2))) = r ^ k * aeval v (hermitePolyH k) * Real.sqrt π := by
    have hfun (u : ℝ) : (aeval (r * v - r * u) (hermitePolyH k) : ℝ) * Real.exp (-(u ^ 2)) =
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * r ^ i * (-r) ^ (k - i) *
          aeval v (hermitePolyH i) * (aeval u (hermitePolyH (k - i)) * Real.exp (-(u ^ 2))) := by
      rw [show r * v - r * u = r * v + (-r) * u by ring,
        hermitePolyH_addition r (-r) v u hab, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [hfun]
    rw [integral_finsetSum _ (fun i _ => by
      simpa only [aeval_hermitePolyH_eq_eval] using
        ((TauCeti.integrable_eval_mul_exp_neg_sq (hermitePolyHR (k - i))).const_mul
          ((k.choose i : ℝ) * r ^ i * (-r) ^ (k - i) * aeval v (hermitePolyH i))))]
    simp_rw [integral_const_mul]
    have hm (i : ℕ) : (∫ u : ℝ, (aeval u (hermitePolyH i) : ℝ) * Real.exp (-(u ^ 2))) =
        if i = 0 then Real.sqrt π else 0 := by
      by_cases hi : i = 0
      · subst i; simpa using hermitePolyH_orthogonality 0 0
      · simpa [hi, Ne.symm hi] using hermitePolyH_orthogonality 0 i
    simp_rw [hm]
    rw [Finset.sum_eq_single k]
    · simp
    · intro i hi hik
      have hiz : k - i ≠ 0 := by have := Finset.mem_range.mp hi; omega
      simp [hiz]
    · simp
  have hbase (k : ℕ) : (∫ t, g 0 t * g k (x - t)) =
      Real.sqrt π * (2 : ℝ) ^ (-((k : ℝ) + 1) / 2) *
        aeval v (hermitePolyH k) * Real.exp (-(x ^ 2) / 2) := by
    let F : ℝ → ℝ := fun t => g 0 t * g k (x - t)
    have hchange : (∫ u : ℝ, F (r * u + x / 2)) = s * ∫ t : ℝ, F t := by
      have he := Measure.integral_comp_mul_left (fun t => F (t + x / 2)) r
      simpa only [integral_add_right_eq_self, r, inv_inv, abs_of_pos hs, smul_eq_mul] using he
    have hfun (u : ℝ) : F (r * u + x / 2) = Real.exp (-(x ^ 2) / 2) *
        ((aeval (r * v - r * u) (hermitePolyH k) : ℝ) * Real.exp (-(u ^ 2))) := by
      have hx : x - (r * u + x / 2) = r * v - r * u := by
        dsimp [r, v]
        field_simp [hs.ne']
        ring_nf
        simp [hs2]
        ring
      dsimp only [F, g]
      simp only [hermitePolyH_zero, map_one, one_mul]
      rw [hx]
      have he : Real.exp (-((r * u + x / 2) ^ 2)) * Real.exp (-((r * v - r * u) ^ 2)) =
          Real.exp (-(x ^ 2) / 2) * Real.exp (-(u ^ 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [r, v]
        field_simp [hs.ne']
        ring_nf
        simp [hs2, show s ^ 3 = 2 * s by rw [pow_succ, hs2],
          show s ^ 4 = 4 by rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2]; norm_num]
        ring
      linear_combination (aeval (r * v - r * u) (hermitePolyH k) : ℝ) * he
    simp_rw [hfun] at hchange
    rw [integral_const_mul, hmoment] at hchange
    have hpow : r ^ k / s = (2 : ℝ) ^ (-((k : ℝ) + 1) / 2) := by
      dsimp [r, s]
      rw [inv_pow, div_eq_mul_inv, ← mul_inv, ← pow_succ, Real.sqrt_eq_rpow,
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      push_cast
      ring
    apply (mul_left_cancel₀ hs.ne')
    change (s * ∫ t, F t) = _
    rw [← hchange, ← hpow]
    field_simp
  have he := (hreduce m n).trans (hbase (m + n))
  simpa only [g, v, s, Nat.cast_add, mul_assoc] using he

@[dlmf 18.17.E49]
theorem hermitePolyH_triple_integral (a b c : ℕ) :
    ∫ x : ℝ, (aeval x (hermitePolyH (a + b)) : ℝ) * aeval x (hermitePolyH (b + c)) *
      aeval x (hermitePolyH (c + a)) * Real.exp (-(x ^ 2)) =
      2 ^ (a + b + c) * (a + b).factorial * (b + c).factorial * (c + a).factorial *
      Real.sqrt Real.pi / ((a.factorial : ℝ) * b.factorial * c.factorial) := by
  have hl (m n : ℕ) (x : ℝ) :
      (aeval x (hermitePolyH m) : ℝ) * aeval x (hermitePolyH n) =
        ∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℝ) * n.choose k * 2 ^ k * k.factorial *
          aeval x (hermitePolyH (m + n - 2 * k)) := by
    have h := hermitePolyH_linearization m n (x : ℂ)
    have castH (j : ℕ) : (aeval (x : ℂ) (hermitePolyH j) : ℂ) =
        ((aeval x (hermitePolyH j) : ℝ) : ℂ) :=
      aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) x (hermitePolyH j)
    simp_rw [castH] at h
    exact_mod_cast h
  have hi (k : ℕ) : Integrable (fun x : ℝ =>
      (aeval x (hermitePolyH (a + b + (b + c) - 2 * k)) : ℝ) *
        aeval x (hermitePolyH (c + a)) * Real.exp (-(x ^ 2))) := by
    simp_rw [aeval_hermitePolyH_eq_eval, ← eval_mul]
    exact TauCeti.integrable_eval_mul_exp_neg_sq _
  have heq : (fun x : ℝ => (aeval x (hermitePolyH (a + b)) : ℝ) *
      aeval x (hermitePolyH (b + c)) * aeval x (hermitePolyH (c + a)) * Real.exp (-(x ^ 2))) =
      fun x => ∑ k ∈ Finset.range (min (a + b) (b + c) + 1),
        ((a + b).choose k : ℝ) * (b + c).choose k * 2 ^ k * k.factorial *
          ((aeval x (hermitePolyH (a + b + (b + c) - 2 * k)) : ℝ) *
            aeval x (hermitePolyH (c + a)) * Real.exp (-(x ^ 2))) := by
    funext x
    rw [hl, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _; ring
  rw [heq, integral_finsetSum _ (fun k _ => (hi k).const_mul _)]
  simp_rw [integral_const_mul, hermitePolyH_orthogonality]
  rw [Finset.sum_eq_single b]
  · rw [if_pos (by omega : a + b + (b + c) - 2 * b = c + a),
      Nat.cast_choose ℝ (by omega : b ≤ a + b), Nat.cast_choose ℝ (by omega : b ≤ b + c)]
    rw [show a + b - b = a by omega, show b + c - b = c by omega]
    have hp : (2 : ℝ) ^ b * 2 ^ (c + a) = 2 ^ (a + b + c) := by
      rw [← pow_add]; congr 1; omega
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero c)]
    linear_combination ((a + b).factorial : ℝ) * (b + c).factorial * (c + a).factorial *
      Real.sqrt Real.pi * hp
  · intro k hk hkb
    have hneq : a + b + (b + c) - 2 * k ≠ c + a := by
      have := Finset.mem_range.mp hk; omega
    simp [hneq]
  · simp only [Finset.mem_range]
    omega


/-- The weighted Jacobi antiderivative on an interval contained in `(-1,1)`. -/
@[dlmf 18.17.E1]
theorem jacobi_weighted_integral {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    2 * (n + 1 : ℂ) * (∫ y : ℝ in (0 : ℝ)..x, (1 - (y : ℂ)) ^ (α : ℂ) *
      (1 + (y : ℂ)) ^ (β : ℂ) * jacobiPolyP α β (n + 1) y) =
      jacobiPolyP (α + 1) (β + 1) n 0 - (1 - (x : ℂ)) ^ (α + 1 : ℂ) *
        (1 + (x : ℂ)) ^ (β + 1 : ℂ) * jacobiPolyP (α + 1) (β + 1) n x := by
  have hreg (a b : ℝ) (m : ℕ) (t : ℝ) (ht : t ∈ Set.Ioo (-1) 1) :
      DifferentiableAt ℝ (fun y : ℝ => (1 - (y : ℂ)) ^ (a : ℂ) *
        (1 + (y : ℂ)) ^ (b : ℂ) * jacobiPolyP a b m y) t := by
    have h1 : (1 - (t : ℂ)) ∈ slitPlane := by
      rw [show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_mem_slitPlane.mpr (by linarith [ht.2])
    have h2 : (1 + (t : ℂ)) ∈ slitPlane := by
      rw [show (1 + (t : ℂ)) = ((1 + t : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_mem_slitPlane.mpr (by linarith [ht.1])
    exact (((((hasDerivAt_id' (t : ℂ)).const_sub 1).cpow_const h1).comp_ofReal).mul
      ((((hasDerivAt_id' (t : ℂ)).const_add 1).cpow_const h2).comp_ofReal)).differentiableAt.mul
      (((analyticOnNhd_jacobiPolyP a b m) t
          (Set.mem_univ _)).differentiableAt.hasDerivAt.comp_ofReal).differentiableAt
  have hmem (t : ℝ) (ht : t ∈ Set.uIcc 0 x) : t ∈ Set.Ioo (-1) 1 := by
    rcases Set.mem_uIcc.mp ht with ht | ht <;> constructor <;>
      linarith [ht.1, ht.2, hx.1, hx.2]
  let g : ℝ → ℂ := fun y => (1 - (y : ℂ)) ^ (α + 1 : ℂ) *
    (1 + (y : ℂ)) ^ (β + 1 : ℂ) * jacobiPolyP (α + 1) (β + 1) n y
  have hd (t : ℝ) (ht : t ∈ Set.uIcc 0 x) : HasDerivAt (fun y => -g y)
      (2 * (n + 1 : ℂ) * ((1 - (t : ℂ)) ^ (α : ℂ) *
        (1 + (t : ℂ)) ^ (β : ℂ) * jacobiPolyP α β (n + 1) t)) t := by
    have hg : DifferentiableAt ℝ g t := by
      simpa only [g, ofReal_add, ofReal_one] using hreg (α + 1) (β + 1) n t (hmem t ht)
    have hh := hg.hasDerivAt.neg
    have he := jacobi_weighted_derivative (α := α + 1) (β := β + 1)
      (by linarith) (by linarith) n (hmem t ht)
    simp only [ofReal_add, ofReal_one, add_sub_cancel_right] at he
    change deriv g t = _ at he
    rw [he] at hh
    convert hh using 1; ring
  have hi : IntervalIntegrable (fun y : ℝ => 2 * (n + 1 : ℂ) *
      ((1 - (y : ℂ)) ^ (α : ℂ) * (1 + (y : ℂ)) ^ (β : ℂ) *
        jacobiPolyP α β (n + 1) y)) volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact (continuousAt_const.mul (hreg α β (n + 1) t (hmem t ht)).continuousAt).continuousWithinAt
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_const_mul] at hh
  simpa [g, sub_eq_add_neg, add_comm] using hh

@[dlmf 18.17.E2]
theorem laguerrePolyL_unweighted_convolution (m n : ℕ) (x : ℝ) :
    ∫ y : ℝ in (0 : ℝ)..x, laguerrePolyL 0 m y * laguerrePolyL 0 n (x - y) =
      laguerrePolyL 0 (m + n) x - laguerrePolyL 0 (m + n + 1) x := by
  let A : ℕ → ℝ → ℂ := fun j y => laguerrePolyL 0 j y - laguerrePolyL 0 (j + 1) y
  let D : ℕ → ℝ → ℂ := fun j y => -deriv (laguerrePolyL 0 j) ((x : ℂ) - y)
  let C : ℕ → ℕ → ℂ := fun i j => ∫ y : ℝ in (0 : ℝ)..x,
    laguerrePolyL 0 i y * laguerrePolyL 0 j ((x : ℂ) - y)
  have hL (a : ℂ) (ha : -1 < a.re) (j : ℕ) : Continuous (laguerrePolyL a j) :=
    continuous_iff_continuousAt.mpr fun y => (analyticAt_laguerrePolyL ha j y).continuousAt
  have hdL (j : ℕ) (y : ℝ) : HasDerivAt (fun t : ℝ => laguerrePolyL 0 j t)
      (deriv (laguerrePolyL 0 j) y) y :=
    ((analyticAt_laguerrePolyL (by norm_num) j (y : ℂ)).differentiableAt.hasDerivAt).comp_ofReal
  have hA (j : ℕ) (y : ℝ) : HasDerivAt (A j) (laguerrePolyL 0 j y) y := by
    have h := (hdL j y).sub (hdL (j + 1) y)
    convert h using 1
    linear_combination (laguerrePolyL_deriv_succ_sub (α := 0) (by norm_num) j y)
  have hAcont (j : ℕ) : Continuous (A j) :=
    ((hL 0 (by norm_num) j).comp continuous_ofReal).sub
      ((hL 0 (by norm_num) (j + 1)).comp continuous_ofReal)
  have hDcont (j : ℕ) : Continuous (D j) := by
    cases j with
    | zero =>
      have h0 : laguerrePolyL 0 0 = fun _ => 1 := funext fun y => laguerrePolyL_zero 0 y
      simp only [D, h0, deriv_const, neg_zero]
      exact continuous_const
    | succ j =>
      have hder : deriv (laguerrePolyL 0 (j + 1)) = fun y => -laguerrePolyL 1 j y :=
        funext fun y => by simpa using laguerrePolyL_derivative (α := 0) (by norm_num) j y
      simp only [D, hder, neg_neg]
      exact (hL 1 (by norm_num) j).comp (continuous_const.sub continuous_ofReal)
  have hzero (j : ℕ) : laguerrePolyL 0 j 0 = 1 := by
    simp [laguerrePolyL_at_zero, poch, ascPochhammer_eval_one, Nat.factorial_ne_zero]
  have hIBP (i j : ℕ) : C i j = A i x - ∫ y : ℝ in (0 : ℝ)..x, D j y * A i y := by
    have hu (y : ℝ) : HasDerivAt (fun t : ℝ => laguerrePolyL 0 j ((x : ℂ) - t)) (D j y) y := by
      have h := (analyticAt_laguerrePolyL (α := 0) (by norm_num) j
          ((x : ℂ) - y)).differentiableAt.hasDerivAt
      have hc := (h.comp (y : ℂ) ((hasDerivAt_id (y : ℂ)).const_sub (x : ℂ))).comp_ofReal
      simpa only [D, Function.comp_apply, mul_neg, mul_one] using hc
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ)) (b := x) (fun y _ => hu y) (fun y _ => hA i y)
      ((hDcont j).intervalIntegrable _ _)
      (((hL 0 (by norm_num) i).comp continuous_ofReal).intervalIntegrable _ _)
    have hleft : (∫ y : ℝ in (0 : ℝ)..x, laguerrePolyL 0 j ((x : ℂ) - y) * laguerrePolyL 0 i y)
        = C i j := by
      apply intervalIntegral.integral_congr
      intro y _
      dsimp [C]
      ring
    rw [hleft] at h
    simpa [A, hzero] using h
  have hstep (i j : ℕ) : C i (j + 1) = C (i + 1) j := by
    have hD (y : ℝ) : D (j + 1) y = D j y + laguerrePolyL 0 j ((x : ℂ) - y) := by
      dsimp [D]
      linear_combination -(laguerrePolyL_deriv_succ_sub (α := 0) (by norm_num) j ((x : ℂ) - y))
    have hsplit : (∫ y : ℝ in (0 : ℝ)..x, D (j + 1) y * A i y) =
        (∫ y : ℝ in (0 : ℝ)..x, D j y * A i y) + C i j - C (i + 1) j := by
      have heq : (fun y => D (j + 1) y * A i y) = fun y => D j y * A i y +
          laguerrePolyL 0 i y * laguerrePolyL 0 j ((x : ℂ) - y) -
          laguerrePolyL 0 (i + 1) y * laguerrePolyL 0 j ((x : ℂ) - y) := by
        funext y
        rw [hD]
        dsimp [A]
        ring
      have hprod (k : ℕ) : Continuous (fun y : ℝ =>
          laguerrePolyL 0 k y * laguerrePolyL 0 j ((x : ℂ) - y)) :=
        ((hL 0 (by norm_num) k).comp continuous_ofReal).mul
          ((hL 0 (by norm_num) j).comp (continuous_const.sub continuous_ofReal))
      have hDA : Continuous (fun y => D j y * A i y) := (hDcont j).mul (hAcont i)
      rw [heq, intervalIntegral.integral_sub
        (f := fun y => D j y * A i y + laguerrePolyL 0 i y * laguerrePolyL 0 j ((x : ℂ) - y))
        (g := fun y => laguerrePolyL 0 (i + 1) y * laguerrePolyL 0 j ((x : ℂ) - y))
        ((hDA.add (hprod i)).intervalIntegrable _ _)
        ((hprod (i + 1)).intervalIntegrable _ _),
        intervalIntegral.integral_add
          (f := fun y => D j y * A i y)
          (g := fun y => laguerrePolyL 0 i y * laguerrePolyL 0 j ((x : ℂ) - y))
          (hDA.intervalIntegrable _ _)
          ((hprod i).intervalIntegrable _ _)]
    rw [hIBP, hsplit, hIBP i j]
    ring
  have hbase (i : ℕ) : C i 0 = A i x := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := x)
      (fun y _ => hA i y) (((hL 0 (by norm_num) i).comp continuous_ofReal).intervalIntegrable _ _)
    simpa [C, A, hzero] using h
  have hconv : ∀ i j : ℕ, C i j = A (i + j) x := by
    intro i j
    induction j generalizing i with
    | zero => simpa using hbase i
    | succ j ih => rw [hstep, ih]; congr 1; omega
  exact hconv m n

open Set in
/-- Integration by parts against the Gegenbauer angular weight. -/
private lemma gegProd_ibp {lam : ℝ} (hlam : 0 < lam) (a v : ℝ) {f f' : ℂ → ℂ}
    (hf : ∀ z, HasDerivAt f (f' z) z) (hf' : Continuous f') :
    ∫ t : ℝ in (0 : ℝ)..π, (Real.cos t : ℂ) * f ((a + v * Real.cos t : ℝ)) *
        ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) =
      (v : ℂ) / (2 * lam) * ∫ t : ℝ in (0 : ℝ)..π, f' ((a + v * Real.cos t : ℝ)) *
        ((Real.sin t ^ (2 * (lam + 1) - 1) : ℝ) : ℂ) := by
  set ρ : ℝ → ℂ := fun t => ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) with hρ
  set w : ℝ → ℂ := fun t => ((a + v * Real.cos t : ℝ) : ℂ) with hw
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun z => (hf z).continuousAt
  have hρi : IntervalIntegrable ρ volume 0 π := by
    have := (integral_sin_rpow_aux hlam).1
    exact ⟨this.1.ofReal, this.2.ofReal⟩
  have hU : uIcc (0 : ℝ) π = Icc 0 π := uIcc_of_le Real.pi_pos.le
  have hsplit : ∀ x : ℝ, 0 ≤ x → x ^ (2 * lam) = x * x ^ (2 * lam - 1) := by
    intro x hx
    rcases hx.eq_or_lt with h | h
    · subst h; rw [Real.zero_rpow (by positivity), zero_mul]
    · rw [← Real.rpow_one_add' h.le (by linarith)]; ring_nf
  have hsplit2 : ∀ x : ℝ, 0 ≤ x → x ^ (2 * (lam + 1) - 1) = x ^ 2 * x ^ (2 * lam - 1) := by
    intro x hx
    rcases hx.eq_or_lt with h | h
    · subst h; rw [Real.zero_rpow (by linarith)]; simp
    · rw [show 2 * (lam + 1) - 1 = 2 + (2 * lam - 1) by ring, Real.rpow_add h]
      norm_cast
  have hwc : Continuous w := by fun_prop
  set g : ℝ → ℂ := fun t => f' (w t) * (-(v : ℂ) * Real.sin t) * Real.sin t +
    f (w t) * (2 * lam * Real.cos t) with hg
  have hgc : Continuous g := by
    simp only [hg]
    have : Continuous fun t => f' (w t) := hf'.comp hwc
    have : Continuous fun t => f (w t) := hfc.comp hwc
    fun_prop
  have hD : ∀ t ∈ Ioo (0 : ℝ) π, HasDerivAt (fun t : ℝ => f (w t) *
      ((Real.sin t ^ (2 * lam) : ℝ) : ℂ)) (ρ t * g t) t := by
    intro t ht
    have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
    have hwd : HasDerivAt w (-(v : ℂ) * Real.sin t) t := by
      have := (((Real.hasDerivAt_cos t).const_mul v).const_add a).ofReal_comp
      exact this.congr_deriv (by push_cast; ring)
    have hfw : HasDerivAt (fun t => f (w t)) (f' (w t) * (-(v : ℂ) * Real.sin t)) t :=
      (hf (w t)).comp t hwd
    have hr := ((Real.hasDerivAt_sin t).rpow_const (p := 2 * lam) (Or.inl hst.ne')).ofReal_comp
    have := hfw.mul hr
    refine this.congr_deriv ?_
    simp only [hρ, hg]
    rw [hsplit _ hst.le]
    push_cast
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.pi_pos.le
    ((hfc.comp hwc).continuousOn.mul
      (Complex.continuous_ofReal.comp ((Real.continuous_rpow_const (by positivity)).comp
        Real.continuous_sin)).continuousOn) hD (hρi.mul_continuousOn (hU ▸ hgc.continuousOn))
  simp only [Pi.mul_apply, Function.comp_apply, Real.sin_pi, Real.sin_zero,
    Real.zero_rpow (by positivity : 2 * lam ≠ 0), Complex.ofReal_zero, mul_zero, sub_zero] at hFTC
  have h1 : IntervalIntegrable (fun t => ρ t * (f' (w t) * (-(v : ℂ) * Real.sin t) * Real.sin t))
      volume 0 π := hρi.mul_continuousOn (hU ▸ (by
        have : Continuous fun t => f' (w t) := hf'.comp hwc
        fun_prop : Continuous fun t => f' (w t) * (-(v : ℂ) * Real.sin t) * Real.sin t).continuousOn)
  have h2 : IntervalIntegrable (fun t => ρ t * (f (w t) * (2 * lam * Real.cos t)))
      volume 0 π := hρi.mul_continuousOn (hU ▸ (by
        have : Continuous fun t => f (w t) := hfc.comp hwc
        fun_prop : Continuous fun t => f (w t) * (2 * lam * Real.cos t)).continuousOn)
  have hsum : ∫ t in (0 : ℝ)..π, ρ t * g t =
      (∫ t in (0 : ℝ)..π, ρ t * (f' (w t) * (-(v : ℂ) * Real.sin t) * Real.sin t)) +
      ∫ t in (0 : ℝ)..π, ρ t * (f (w t) * (2 * lam * Real.cos t)) := by
    rw [← intervalIntegral.integral_add h1 h2]
    exact intervalIntegral.integral_congr fun t _ => by simp only [hg]; ring
  have hA : (∫ t in (0 : ℝ)..π, ρ t * (f' (w t) * (-(v : ℂ) * Real.sin t) * Real.sin t)) =
      -(v : ℂ) * ∫ t : ℝ in (0 : ℝ)..π, f' (w t) *
        ((Real.sin t ^ (2 * (lam + 1) - 1) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [hU] at ht
    have hs0 : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2
    simp only [hρ]
    rw [hsplit2 _ hs0]
    push_cast
    ring
  have hB : (∫ t in (0 : ℝ)..π, ρ t * (f (w t) * (2 * lam * Real.cos t))) =
      2 * lam * ∫ t : ℝ in (0 : ℝ)..π, (Real.cos t : ℂ) * f (w t) * ρ t := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [hsum, hA, hB] at hFTC
  have hlam' : (2 * lam : ℂ) ≠ 0 := by
    have : (2 * lam : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  show (∫ t in (0 : ℝ)..π, (Real.cos t : ℂ) * f (w t) * ρ t) = (v : ℂ) / (2 * lam) *
    ∫ t in (0 : ℝ)..π, f' (w t) * ((Real.sin t ^ (2 * (lam + 1) - 1) : ℝ) : ℂ)
  rw [div_mul_eq_mul_div, eq_div_iff hlam']
  linear_combination hFTC
/-- Gegenbauer polynomials are continuous. -/
private lemma gegProd_continuous (lam : ℂ) (n : ℕ) : Continuous (ultrasphPoly lam n) :=
  continuousOn_univ.1 (analyticOnNhd_ultrasphPoly lam n).continuousOn

/-- Continuous functions are integrable against the angular weight `sin^{2λ-1}` on `[0, π]`. -/
private lemma gegProd_intble {lam : ℝ} (hlam : 0 < lam) {h : ℝ → ℂ} (hh : Continuous h) :
    IntervalIntegrable (fun t => h t * ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)) volume 0 π := by
  have := (integral_sin_rpow_aux hlam).1
  have hρi : IntervalIntegrable (fun t => ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)) volume 0 π :=
    ⟨this.1.ofReal, this.2.ofReal⟩
  exact hρi.continuousOn_mul hh.continuousOn

/-- The three-term recurrence of the Gegenbauer polynomials, integrated against the angular
weight along `t ↦ a + v cos t`; the middle term is integrated by parts, which raises `λ` by one. -/
private lemma gegProd_step {lam : ℝ} (hlam : 0 < lam) (a v : ℝ) (k : ℕ) :
    (k + 2 : ℂ) * (∫ t : ℝ in (0 : ℝ)..π, ultrasphPoly lam (k + 2) ((a + v * Real.cos t : ℝ) : ℂ) *
      ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)) =
      2 * (k + lam + 1) * a * (∫ t : ℝ in (0 : ℝ)..π,
        ultrasphPoly lam (k + 1) ((a + v * Real.cos t : ℝ) : ℂ) *
          ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)) +
      2 * (k + lam + 1) * v * (v * ∫ t : ℝ in (0 : ℝ)..π,
        ultrasphPoly ((lam : ℂ) + 1) k ((a + v * Real.cos t : ℝ) : ℂ) *
          ((Real.sin t ^ (2 * (lam + 1) - 1) : ℝ) : ℂ)) -
      (k + 2 * lam) * (∫ t : ℝ in (0 : ℝ)..π, ultrasphPoly lam k ((a + v * Real.cos t : ℝ) : ℂ) *
        ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)) := by
  have hlre : -1 / 2 < (lam : ℂ).re := by simp; linarith
  set ρ : ℝ → ℂ := fun t => ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) with hρ
  set ρ' : ℝ → ℂ := fun t => ((Real.sin t ^ (2 * (lam + 1) - 1) : ℝ) : ℂ) with hρ'
  set z : ℝ → ℂ := fun t => ((a + v * Real.cos t : ℝ) : ℂ) with hz
  have hzc : Continuous z := by fun_prop
  set I : ℕ → ℂ := fun j => ∫ t : ℝ in (0 : ℝ)..π, ultrasphPoly lam j (z t) * ρ t with hI
  set J : ℂ := ∫ t : ℝ in (0 : ℝ)..π, ultrasphPoly ((lam : ℂ) + 1) k (z t) * ρ' t with hJ
  change (k + 2 : ℂ) * I (k + 2) = 2 * (k + lam + 1) * a * I (k + 1) +
    2 * (k + lam + 1) * v * (v * J) - (k + 2 * lam) * I k
  -- integration by parts
  have hK : (∫ t : ℝ in (0 : ℝ)..π, (Real.cos t : ℂ) * ultrasphPoly lam (k + 1) (z t) * ρ t) =
      v * J := by
    have hd : ∀ w : ℂ, HasDerivAt (ultrasphPoly lam (k + 1))
        (2 * lam * ultrasphPoly ((lam : ℂ) + 1) k w) w := by
      intro w
      rw [← ultrasphPoly_derivative hlre k w]
      exact (analyticAt_ultrasphPoly _ _ w).differentiableAt.hasDerivAt
    have := gegProd_ibp hlam a v hd
      ((gegProd_continuous _ k).const_mul (2 * (lam : ℂ)))
    rw [this, intervalIntegral.integral_congr (g := fun t => (2 * (lam : ℂ)) *
      (ultrasphPoly ((lam : ℂ) + 1) k (z t) * ρ' t)) (fun t _ => by simp only [hz, hρ']; ring),
      intervalIntegral.integral_const_mul]
    have hl : (2 * lam : ℂ) ≠ 0 := by
      have : (2 * lam : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    rw [← mul_assoc, div_mul_eq_mul_div, mul_div_assoc, div_self hl, mul_one]
  -- the three-term recurrence under the integral
  have hcj : ∀ j : ℕ, Continuous fun t => ultrasphPoly lam j (z t) :=
    fun j => (gegProd_continuous _ j).comp hzc
  have iA : IntervalIntegrable (fun t => ultrasphPoly lam (k + 1) (z t) * ρ t) volume 0 π :=
    gegProd_intble hlam (hcj _)
  have iB : IntervalIntegrable (fun t => (Real.cos t : ℂ) * ultrasphPoly lam (k + 1) (z t) * ρ t)
      volume 0 π :=
    gegProd_intble hlam ((Complex.continuous_ofReal.comp Real.continuous_cos).mul (hcj (k + 1)))
  have iC : IntervalIntegrable (fun t => ultrasphPoly lam k (z t) * ρ t) volume 0 π :=
    gegProd_intble hlam (hcj _)
  have e : ∀ t : ℝ, (k + 2 : ℂ) * (ultrasphPoly lam (k + 2) (z t) * ρ t) =
      2 * (k + lam + 1) * a * (ultrasphPoly lam (k + 1) (z t) * ρ t) +
      2 * (k + lam + 1) * v * ((Real.cos t : ℂ) * ultrasphPoly lam (k + 1) (z t) * ρ t) -
      (k + 2 * lam) * (ultrasphPoly lam k (z t) * ρ t) := by
    intro t
    have hr := ultrasphPoly_recurrence hlre k (z t)
    have hzt : z t = a + v * Real.cos t := by simp only [hz]; push_cast; ring
    rw [hzt] at hr ⊢
    push_cast at hr ⊢
    linear_combination ρ t * hr
  rw [← hK]
  simp only [hI]
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_congr (fun t _ => e t),
    intervalIntegral.integral_sub ((iA.const_mul _).add (iB.const_mul _)) (iC.const_mul _),
    intervalIntegral.integral_add (iA.const_mul _) (iB.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

/-- The normalizing constant `√π Γ(λ)/Γ(λ+1/2)` of the angular weight, at `λ + 1`. -/
private lemma gegProd_const_succ {lam : ℝ} (hlam : 0 < lam) :
    Real.sqrt π * Real.Gamma (lam + 1) / Real.Gamma (lam + 1 + 1 / 2) =
      2 * lam * (Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2)) / (2 * lam + 1) := by
  rw [Real.Gamma_add_one hlam.ne', show lam + 1 + 1 / 2 = (lam + 1 / 2) + 1 by ring,
    Real.Gamma_add_one (by linarith : lam + 1 / 2 ≠ 0)]
  have : Real.Gamma (lam + 1 / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  field_simp

/-- Unnormalized form of Gegenbauer's product formula, by induction on the degree. -/
private lemma gegProd_main (n : ℕ) : ∀ lam : ℝ, 0 < lam → ∀ θ ψ : ℝ,
    ultrasphPoly lam n 1 * (∫ u : ℝ in (0 : ℝ)..π, ultrasphPoly lam n
      ((Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos u : ℝ)) *
        ((Real.sin u ^ (2 * lam - 1) : ℝ) : ℂ)) =
      ((Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) : ℝ) : ℂ) *
        ultrasphPoly lam n (Real.cos θ) * ultrasphPoly lam n (Real.cos ψ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro lam hlam θ ψ
  set a : ℝ := Real.cos θ * Real.cos ψ with ha
  set v : ℝ := Real.sin θ * Real.sin ψ with hv
  have hm := (integral_sin_rpow_aux hlam).2
  have hlre : -1 / 2 < (lam : ℂ).re := by simp; linarith
  -- `∫ cos u ρ = 0`
  have hcos0 : ∫ t : ℝ in (0 : ℝ)..π, (Real.cos t : ℂ) * ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)
      = 0 := by
    have := gegProd_ibp hlam a v (f := fun _ => (1 : ℂ)) (f' := fun _ => 0)
      (fun z => hasDerivAt_const z 1) continuous_const
    simpa using this
  have hI0 : ∫ t : ℝ in (0 : ℝ)..π, ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) =
      ((Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_ofReal, hm]
  rcases n with _ | _ | k
  · -- degree zero
    simp only [ultrasphPoly_zero, one_mul, mul_one]
    exact hI0
  · -- degree one
    simp only [ultrasphPoly_one_eq hlre]
    have hsplit : ∀ t : ℝ, 2 * (lam : ℂ) * ((a + v * Real.cos t : ℝ) : ℂ) *
        ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) = 2 * lam * a * ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)
        + 2 * lam * v * ((Real.cos t : ℂ) * ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)) := by
      intro t; push_cast; ring
    have i1 : IntervalIntegrable (fun t : ℝ => 2 * (lam : ℂ) * a *
        ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)) volume 0 π := by
      have := (gegProd_intble hlam (h := fun _ => 2 * (lam : ℂ) * a) continuous_const)
      simpa using this
    have i2 : IntervalIntegrable (fun t : ℝ => 2 * (lam : ℂ) * v * ((Real.cos t : ℂ) *
        ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ))) volume 0 π :=
      (gegProd_intble hlam (Complex.continuous_ofReal.comp Real.continuous_cos)).const_mul _
    rw [intervalIntegral.integral_congr (fun t _ => hsplit t),
      intervalIntegral.integral_add i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hcos0, hI0]
    simp only [ha]
    push_cast
    ring
  · -- degree  from degrees ,  and the raised parameter
    set x : ℂ := (Real.cos θ : ℂ) with hx
    set y : ℂ := (Real.cos ψ : ℂ) with hy
    set mR : ℝ := Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) with hmR
    set m'R : ℝ := Real.sqrt π * Real.Gamma (lam + 1) / Real.Gamma (lam + 1 + 1 / 2) with hm'R
    set ρ : ℝ → ℂ := fun t => ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) with hρ
    set ρ' : ℝ → ℂ := fun t => ((Real.sin t ^ (2 * (lam + 1) - 1) : ℝ) : ℂ) with hρ'
    set z : ℝ → ℂ := fun t => ((a + v * Real.cos t : ℝ) : ℂ) with hz
    have hzc : Continuous z := by fun_prop
    set I : ℕ → ℂ := fun j => ∫ t : ℝ in (0 : ℝ)..π, ultrasphPoly lam j (z t) * ρ t with hI
    set J : ℂ := ∫ t : ℝ in (0 : ℝ)..π, ultrasphPoly ((lam : ℂ) + 1) k (z t) * ρ' t with hJ
    have ih0 : ultrasphPoly lam k 1 * I k = mR * ultrasphPoly lam k x * ultrasphPoly lam k y :=
      ih k (by omega) lam hlam θ ψ
    have ih1 : ultrasphPoly lam (k + 1) 1 * I (k + 1) =
        mR * ultrasphPoly lam (k + 1) x * ultrasphPoly lam (k + 1) y :=
      ih (k + 1) (by omega) lam hlam θ ψ
    have ihJ : ultrasphPoly ((lam : ℂ) + 1) k 1 * J =
        m'R * ultrasphPoly ((lam : ℂ) + 1) k x * ultrasphPoly ((lam : ℂ) + 1) k y := by
      have := ih k (by omega) (lam + 1) (by linarith) θ ψ
      rw [show ((lam + 1 : ℝ) : ℂ) = (lam : ℂ) + 1 by push_cast; ring] at this
      exact this
    have hstep : (k + 2 : ℂ) * I (k + 2) = 2 * (k + lam + 1) * a * I (k + 1) +
        2 * (k + lam + 1) * v * (v * J) - (k + 2 * lam) * I k :=
      gegProd_step hlam a v k
    -- normalizing constants
    have hlre' : -1 / 2 < ((lam : ℂ) + 1).re := by simp; linarith
    have hl0 : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
    have hl1 : (2 * lam + 1 : ℂ) ≠ 0 := by
      have : (2 * lam + 1 : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    have hlk : (2 * lam + k : ℂ) ≠ 0 := by
      have : (2 * lam + k : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    have hlk1 : (2 * lam + k + 1 : ℂ) ≠ 0 := by
      have : (2 * lam + k + 1 : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    have hkl : (k + lam + 1 : ℂ) ≠ 0 := by
      have : (k + lam + 1 : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    have hk1 : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hk2 : (k + 2 : ℂ) ≠ 0 := by exact_mod_cast (show k + 2 ≠ 0 by omega)
    set P : ℂ := poch (2 * (lam : ℂ)) k with hP
    set F : ℂ := (k.factorial : ℂ) with hF
    have hP0 : P ≠ 0 := poch_ne_zero_of_re_pos (by simp; linarith) k
    have hF0 : F ≠ 0 := by simp [hF, Nat.factorial_ne_zero]
    have hv0 : ultrasphPoly lam k 1 = P / F := ultrasphPoly_at_one hlre k
    have hv1 : ultrasphPoly lam (k + 1) 1 = P * (2 * lam + k) / ((k + 1) * F) := by
      rw [ultrasphPoly_at_one hlre, poch_succ, Nat.factorial_succ]; push_cast; ring
    have hv2 : ultrasphPoly lam (k + 2) 1 =
        P * (2 * lam + k) * (2 * lam + k + 1) / ((k + 2) * (k + 1) * F) := by
      rw [ultrasphPoly_at_one hlre, poch_succ, poch_succ, Nat.factorial_succ,
        Nat.factorial_succ]; push_cast; ring
    have hvb : ultrasphPoly ((lam : ℂ) + 1) k 1 =
        P * (2 * lam + k) * (2 * lam + k + 1) / (2 * lam * (2 * lam + 1) * F) := by
      have h1 := poch_add (2 * (lam : ℂ)) 2 k
      rw [show 2 + k = (k + 1) + 1 by omega, poch_succ, poch_succ,
        show (2 : ℕ) = 0 + 1 + 1 from rfl, poch_succ, poch_succ, poch_zero] at h1
      push_cast at h1
      rw [ultrasphPoly_at_one hlre', show 2 * ((lam : ℂ) + 1) = 2 * lam + 2 by ring,
        div_eq_div_iff hF0 (by simp [hl0, hl1, hF0])]
      linear_combination (-F) * h1
    have hmm : ((m'R : ℝ) : ℂ) = 2 * lam * mR / (2 * lam + 1) := by
      rw [show m'R = 2 * lam * mR / (2 * lam + 1) from gegProd_const_succ hlam]; push_cast; ring
    -- the polynomial identities at `x` and `y`
    have recx := ultrasphPoly_recurrence hlre k x
    have recy := ultrasphPoly_recurrence hlre k y
    have sqx := ultrasphPoly_raise_parameter_sq hlre k x
    have sqy := ultrasphPoly_raise_parameter_sq hlre k y
    have hxy : (a : ℂ) = x * y := by simp only [ha, hx, hy]; push_cast; ring
    have hvv : (v : ℂ) ^ 2 = (1 - x ^ 2) * (1 - y ^ 2) := by
      have hr : v ^ 2 = (1 - Real.cos θ ^ 2) * (1 - Real.cos ψ ^ 2) := by
        rw [hv, mul_pow, Real.sin_sq, Real.sin_sq]
      simp only [hx, hy]
      exact_mod_cast hr
    set X0 := ultrasphPoly lam k x
    set X1 := ultrasphPoly lam (k + 1) x
    set X2 := ultrasphPoly lam (k + 2) x
    set Y0 := ultrasphPoly lam k y
    set Y1 := ultrasphPoly lam (k + 1) y
    set Y2 := ultrasphPoly lam (k + 2) y
    set Qx := ultrasphPoly ((lam : ℂ) + 1) k x
    set Qy := ultrasphPoly ((lam : ℂ) + 1) k y
    have hEx : (1 - x ^ 2) * Qx = (-(k + 1) * (2 * (k + lam + 1) * x * X1 - (k + 2 * lam) * X0) +
        (k + 2 * lam) * (k + 2 * lam + 1) * X0) / (4 * lam * (k + lam + 1)) := by
      rw [eq_div_iff (by simp [hl0, hkl])]
      linear_combination sqx - (k + 1) * recx
    have hEy : (1 - y ^ 2) * Qy = (-(k + 1) * (2 * (k + lam + 1) * y * Y1 - (k + 2 * lam) * Y0) +
        (k + 2 * lam) * (k + 2 * lam + 1) * Y0) / (4 * lam * (k + lam + 1)) := by
      rw [eq_div_iff (by simp [hl0, hkl])]
      linear_combination sqy - (k + 1) * recy
    have hX2 : X2 = (2 * (k + lam + 1) * x * X1 - (k + 2 * lam) * X0) / (k + 2) := by
      rw [eq_div_iff hk2]; linear_combination recx
    have hY2 : Y2 = (2 * (k + lam + 1) * y * Y1 - (k + 2 * lam) * Y0) / (k + 2) := by
      rw [eq_div_iff hk2]; linear_combination recy
    have eI0 : I k = mR * X0 * Y0 / (P / F) := by
      rw [eq_div_iff (div_ne_zero hP0 hF0), ← hv0]; linear_combination ih0
    have eI1 : I (k + 1) = mR * X1 * Y1 / (P * (2 * lam + k) / ((k + 1) * F)) := by
      rw [eq_div_iff (by simp [hP0, hF0, hk1, hlk, -one_div]), ← hv1]; linear_combination ih1
    have eJ : J = m'R * Qx * Qy / (P * (2 * lam + k) * (2 * lam + k + 1) /
        (2 * lam * (2 * lam + 1) * F)) := by
      rw [eq_div_iff (by simp [hP0, hF0, hl0, hl1, hlk, hlk1, -one_div]), ← hvb]
      linear_combination ihJ
    have hvJ : (v : ℂ) * ((v : ℂ) * J) = m'R * ((1 - x ^ 2) * Qx) * ((1 - y ^ 2) * Qy) /
        (P * (2 * lam + k) * (2 * lam + k + 1) / (2 * lam * (2 * lam + 1) * F)) := by
      rw [eJ]; linear_combination (m'R * Qx * Qy / (P * (2 * lam + k) * (2 * lam + k + 1) /
        (2 * lam * (2 * lam + 1) * F))) * hvv
    rw [hEx, hEy, hmm] at hvJ
    have eI2 : I (k + 2) = (2 * (k + lam + 1) * a * I (k + 1) +
        2 * (k + lam + 1) * (v * (v * J)) - (k + 2 * lam) * I k) / (k + 2) := by
      rw [eq_div_iff hk2]; linear_combination hstep
    show ultrasphPoly lam (k + 2) 1 * I (k + 2) = mR * X2 * Y2
    rw [eI2, hvJ, eI1, eI0, hxy, hv2, hX2, hY2]
    field_simp
    ring

@[dlmf 18.17.E5]
theorem ultrasphPoly_product_integral {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (θ ψ : ℝ) :
    ultrasphPoly lam n (Real.cos θ) / ultrasphPoly lam n 1 *
      (ultrasphPoly lam n (Real.cos ψ) / ultrasphPoly lam n 1) =
      Gamma (lam + 1 / 2 : ℂ) / (Real.sqrt Real.pi * Gamma (lam : ℂ)) *
      ∫ phi : ℝ in (0 : ℝ)..Real.pi, ultrasphPoly lam n
        (Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi) / ultrasphPoly lam n 1 *
          (Real.rpow (Real.sin phi) (2 * lam - 1) : ℂ) := by
  have hmain := gegProd_main n lam hlam θ ψ
  have hlre : -1 / 2 < (lam : ℂ).re := by simp; linarith
  have h1 : ultrasphPoly lam n 1 ≠ 0 := by
    rw [ultrasphPoly_at_one hlre]
    exact div_ne_zero (poch_ne_zero_of_re_pos (by simp; linarith) n)
      (by exact_mod_cast n.factorial_ne_zero)
  have hG1 : 0 < Real.Gamma (lam + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hG2 : 0 < Real.Gamma lam := Real.Gamma_pos_of_pos hlam
  have hsq : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hGG : Gamma (lam + 1 / 2 : ℂ) / (Real.sqrt Real.pi * Gamma (lam : ℂ)) =
      ((Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) : ℝ) : ℂ)⁻¹ := by
    rw [show (lam + 1 / 2 : ℂ) = ((lam + 1 / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal, Complex.Gamma_ofReal]
    push_cast
    field_simp
  have hint : (∫ phi : ℝ in (0 : ℝ)..Real.pi, ultrasphPoly lam n
        (Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi) / ultrasphPoly lam n 1 *
          (Real.rpow (Real.sin phi) (2 * lam - 1) : ℂ)) =
      (ultrasphPoly lam n 1)⁻¹ * ∫ phi : ℝ in (0 : ℝ)..π, ultrasphPoly lam n
        ((Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi : ℝ)) *
          ((Real.sin phi ^ (2 * lam - 1) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Real.rpow_eq_pow]
    push_cast
    ring
  have hm0 : ((Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) ≠ 0)
  have hI : (∫ phi : ℝ in (0 : ℝ)..π, ultrasphPoly lam n
        ((Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi : ℝ)) *
          ((Real.sin phi ^ (2 * lam - 1) : ℝ) : ℂ)) =
      ((Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) : ℝ) : ℂ) *
        ultrasphPoly lam n (Real.cos θ) * ultrasphPoly lam n (Real.cos ψ) / ultrasphPoly lam n 1 := by
    rw [eq_div_iff h1, mul_comm]; exact hmain
  rw [hGG, hint, hI]
  generalize ((Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) : ℝ) : ℂ) = M at hm0 ⊢
  field_simp

@[dlmf 18.17.E9]
theorem jacobi_fractional_integral {α β μ : ℝ} (hα : -1 < α) (hβ : -1 < β) (hμ : 0 < μ)
    (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    (1 - (x : ℂ)) ^ (α + μ : ℂ) * jacobiPolyP (α + μ) (β - μ) n x / Gamma (α + μ + n + 1 : ℂ) =
      ∫ y : ℝ in x..1, (1 - (y : ℂ)) ^ (α : ℂ) * jacobiPolyP α β n y / Gamma (α + n + 1 : ℂ) *
        ((y - x : ℂ) ^ (μ - 1 : ℂ) / Gamma (μ : ℂ)) := by
  have hnorm (a b : ℝ) (ha : -1 < a) (y : ℂ) :
      jacobiPolyP a b n y / Gamma ((a : ℂ) + n + 1) =
        regularizedGaussHGFun (-(n : ℂ))
          (n + (a : ℂ) + b + 1) ((a : ℂ) + 1) ((1 - y) / 2) / n.factorial := by
    have hp : ∀ k : ℕ, (a : ℂ) + 1 ≠ -(k : ℂ) :=
      not_neg_nat_of_re_pos (by simp; linarith)
    have hG : Gamma ((a : ℂ) + n + 1) = poch ((a : ℂ) + 1) n * Gamma ((a : ℂ) + 1) := by
      rw [show (a : ℂ) + n + 1 = (a : ℂ) + 1 + n by ring]
      exact (div_eq_iff (Gamma_ne_zero hp)).mp
        (Gamma_add_nat_div_Gamma_eq (n := n) ((a : ℂ) + 1) hp)
    rw [jacobiPolyP, DLMF.Hypergeometric.regularizedGaussHGFun_eq_div_Gamma hp, hG]
    field [Gamma_ne_zero hp, poch_ne_zero_of_not_neg_nat hp n]
  let R : ℂ → ℂ := regularizedGaussHGFun (-(n : ℂ))
    (n + (α : ℂ) + β + 1) ((α : ℂ) + 1)
  let f : ℝ → ℂ := fun y => (1 - (y : ℂ)) ^ (α : ℂ) * R ((1 - y) / 2) *
    ((y : ℂ) - x) ^ ((μ : ℂ) - 1)
  let g : ℝ → ℂ := fun t => R (((1 - (x : ℂ)) / 2) * t) *
    (t : ℂ) ^ (α : ℂ) * (1 - (t : ℂ)) ^ ((μ : ℂ) - 1)
  have hxpos : 0 < 1 - x := by linarith [hx.2]
  have hx0 : 1 - (x : ℂ) ≠ 0 := by
    exact_mod_cast hxpos.ne'
  have hscale : (∫ y : ℝ in x..1, f y) =
      (1 - (x : ℂ)) ^ ((α : ℂ) + μ) * ∫ t : ℝ in (0 : ℝ)..1, g t := by
    have hs := intervalIntegral.smul_integral_comp_sub_mul f (1 - x) 1
      (a := (0 : ℝ)) (b := 1)
    simp only [mul_one, sub_sub_cancel, mul_zero, sub_zero, Complex.real_smul,
      ofReal_sub, ofReal_one] at hs
    rw [← hs, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    have hxp : (1 - (x : ℂ)) * (1 - (x : ℂ)) ^ (α : ℂ) *
        (1 - (x : ℂ)) ^ ((μ : ℂ) - 1) = (1 - (x : ℂ)) ^ ((α : ℂ) + μ) := by
      calc
        _ = (1 - (x : ℂ)) ^ (1 : ℂ) * (1 - (x : ℂ)) ^ (α : ℂ) *
            (1 - (x : ℂ)) ^ ((μ : ℂ) - 1) := by rw [cpow_one]
        _ = _ := by rw [← cpow_add _ _ hx0, ← cpow_add _ _ hx0]; congr 1; ring
    have hp (s : ℝ) (hs : 0 ≤ s) (a : ℂ) :
        ((1 - (x : ℂ)) * s) ^ a = (1 - (x : ℂ)) ^ a * (s : ℂ) ^ a := by
      simpa only [ofReal_sub, ofReal_one] using mul_cpow_ofReal_nonneg hxpos.le hs a
    dsimp [f, g]
    push_cast
    rw [show 1 - (1 - (1 - (x : ℂ)) * t) = (1 - (x : ℂ)) * t by ring,
      show 1 - (1 - (x : ℂ)) * t - x = (1 - (x : ℂ)) * (1 - t) by ring,
      hp t ht.1.le, show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; rfl,
      hp (1 - t) (by linarith [ht.2])]
    push_cast
    rw [show (1 - (x : ℂ)) * t / 2 = ((1 - (x : ℂ)) / 2) * t by ring]
    linear_combination (t : ℂ) ^ (α : ℂ) * R (((1 - (x : ℂ)) / 2) * t) *
      (1 - (t : ℂ)) ^ ((μ : ℂ) - 1) * hxp
  have hz : ‖(1 - (x : ℂ)) / 2‖ < 1 := by
    rw [show (1 - (x : ℂ)) / 2 = (((1 - x) / 2 : ℝ) : ℂ) by push_cast; rfl,
      norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith [hx.1]
  have hR := DLMF.Hypergeometric.fractional_integral (a := -(n : ℂ))
    (b := n + (α : ℂ) + β + 1) (c := (α : ℂ) + μ + 1) (d := (α : ℂ) + 1)
    (by simp; linarith) (by simp; linarith) hz
  rw [show (α : ℂ) + 1 - 1 = (α : ℂ) by ring,
    show (α : ℂ) + μ + 1 - ((α : ℂ) + 1) = (μ : ℂ) by ring] at hR
  change regularizedGaussHGFun (-(n : ℂ))
    (n + (α : ℂ) + β + 1) ((α : ℂ) + μ + 1) ((1 - x) / 2) =
      1 / Gamma (μ : ℂ) * ∫ t : ℝ in (0 : ℝ)..1, g t at hR
  have hrhs : (∫ y : ℝ in x..1, (1 - (y : ℂ)) ^ (α : ℂ) * jacobiPolyP α β n y /
      Gamma (α + n + 1 : ℂ) * ((y - x : ℂ) ^ (μ - 1 : ℂ) / Gamma (μ : ℂ))) =
      (∫ y : ℝ in x..1, f y) / ((n.factorial : ℂ) * Gamma (μ : ℂ)) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro y _
    dsimp only
    rw [show (1 - (y : ℂ)) ^ (α : ℂ) * jacobiPolyP α β n y / Gamma (α + n + 1 : ℂ) =
      (1 - (y : ℂ)) ^ (α : ℂ) * (jacobiPolyP α β n y / Gamma (α + n + 1 : ℂ)) by ring,
      hnorm α β hα]
    dsimp [f, R]
    push_cast
    ring
  have hL := hnorm (α + μ) (β - μ) (by linarith) x
  push_cast at hL
  rw [show (n : ℂ) + ((α : ℂ) + μ) + ((β : ℂ) - μ) + 1 = n + (α : ℂ) + β + 1 by ring] at hL
  rw [hrhs, hscale, show (1 - (x : ℂ)) ^ (α + μ : ℂ) * jacobiPolyP (α + μ) (β - μ) n x /
      Gamma (α + μ + n + 1 : ℂ) = (1 - (x : ℂ)) ^ (α + μ : ℂ) *
      (jacobiPolyP (α + μ) (β - μ) n x / Gamma (α + μ + n + 1 : ℂ)) by ring, hL, hR]
  push_cast
  ring

/-- The moments `∫ (1 + x)^m (1 - x)^α (1 + x)^β P_n^{(α,β)}(x) dx`, from the Mellin transform
and the reflection `x ↦ -x`. -/
theorem jacobi_moment {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n m : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) + 1) ^ m *
        (jacobiPolyP α β n x * (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ)) =
      (-1 : ℂ) ^ n * ((2 : ℂ) ^ ((α : ℂ) + (β + m + 1)) * Gamma (β + m + 1) *
        Gamma (1 + (α : ℂ) + n) * poch (-(m : ℂ)) n /
        (n.factorial * Gamma (1 + α + (β + m + 1) + n))) := by
  have hz : 0 < ((β : ℂ) + m + 1).re := by
    simp; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hM := jacobi_mellin_transform hβ hα hz n
  rw [show (1 : ℂ) + β - (β + m + 1) = -(m : ℂ) by ring] at hM
  have hneg := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
    (fun x : ℝ => ((x : ℂ) + 1) ^ m *
      (jacobiPolyP α β n x * (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ)))
  norm_num only [neg_neg] at hneg
  rw [← hM, ← hneg, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun t ht => ?_
  have h1 : (1 - (t : ℂ)) ≠ 0 := by
    rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.mpr (by linarith [ht.2])
  have hr := jacobi_reflection (α := (α : ℂ)) (β := (β : ℂ)) (by simpa using hα)
    (by simpa using hβ) n (t : ℂ)
  push_cast
  rw [hr, show (β : ℂ) + m + 1 - 1 = β + m by ring, cpow_add _ _ h1, cpow_natCast,
    show -(t : ℂ) + 1 = 1 - t by ring, show (1 : ℂ) - -t = 1 + t by ring]
  rw [show (1 : ℂ) + -t = 1 - t by ring]
  ring


/-- Termwise integration of `e^{-(x+1)z}` against an integrable function on `[-1, 1]`. -/
theorem hasSum_integral_exp_neg_add_one_mul {w : ℝ → ℂ}
    (hw : IntervalIntegrable w volume (-1) 1) (z : ℂ) :
    HasSum (fun m : ℕ => ∫ x : ℝ in (-1 : ℝ)..1, (-z) ^ m / m ! * (((x : ℂ) + 1) ^ m * w x))
      (∫ x : ℝ in (-1 : ℝ)..1, exp (-((x : ℂ) + 1) * z) * w x) := by
  have hwm : AEStronglyMeasurable w (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    rw [Set.uIoc_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]; exact hw.1.aestronglyMeasurable
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun m x => (2 * ‖z‖) ^ m / m ! * ‖w x‖)
    (fun m => (((by fun_prop : Continuous fun x : ℝ => (-z) ^ m / (m ! : ℂ) *
      ((x : ℂ) + 1) ^ m)).aestronglyMeasurable.mul hwm).congr
      (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring))
    (fun m => ?_)
    (Eventually.of_forall fun x _ => (Real.summable_pow_div_factorial (2 * ‖z‖)).mul_right _)
    ?_
    (Eventually.of_forall fun x _ => ?_)
  · refine Eventually.of_forall fun x hx => ?_
    rw [Set.uIoc_of_le (show (-1 : ℝ) ≤ 1 by norm_num)] at hx
    have hx1 : ‖(x : ℂ) + 1‖ ≤ 2 := by
      rw [← ofReal_one, ← ofReal_add, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.2]
    rw [norm_mul, norm_mul, norm_div, norm_pow, norm_pow, norm_neg, Complex.norm_natCast,
      mul_pow]
    have hw0 : 0 ≤ ‖w x‖ := norm_nonneg _
    have hp : ‖(x : ℂ) + 1‖ ^ m ≤ 2 ^ m := pow_le_pow_left₀ (norm_nonneg _) hx1 m
    have hf : (0 : ℝ) < m ! := by exact_mod_cast m.factorial_pos
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hf.le
    calc ‖z‖ ^ m * (‖(x : ℂ) + 1‖ ^ m * ‖w x‖) ≤ ‖z‖ ^ m * (2 ^ m * ‖w x‖) := by gcongr
      _ = 2 ^ m * ‖z‖ ^ m * ‖w x‖ := by ring
  · have h : (fun x => ∑' m : ℕ, (2 * ‖z‖) ^ m / m ! * ‖w x‖) =
        fun x => Real.exp (2 * ‖z‖) * ‖w x‖ := by
      funext x
      rw [tsum_mul_right, Real.exp_eq_exp_ℝ,
        ← (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (2 * ‖z‖)).tsum_eq]
    rw [h]
    exact hw.norm.const_mul _
  · have h := (NormedSpace.expSeries_div_hasSum_exp (-((x : ℂ) + 1) * z)).mul_right (w x)
    rw [← Complex.exp_eq_exp_ℂ] at h
    convert h using 1
    funext m
    rw [show -((x : ℂ) + 1) * z = -z * ((x : ℂ) + 1) by ring, mul_pow]
    ring


/-- DLMF 18.17.33 in the form used by the Fourier transforms below. -/
lemma jacobi_laplace_aux {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) (z : ℂ) :
    ∫ x : ℝ in (-1 : ℝ)..1, exp (-((x : ℂ) + 1) * z) *
        (jacobiPolyP α β n x * (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ)) =
      (-1 : ℂ) ^ n * (2 : ℂ) ^ ((α : ℂ) + β + n + 1) * Gamma ((α : ℂ) + n + 1) *
      Gamma ((β : ℂ) + n + 1) / (Gamma ((α : ℂ) + β + 2 * n + 2) * n.factorial) *
      z ^ n * kummerM ((β : ℂ) + n + 1) ((α : ℂ) + β + 2 * n + 2) (-2 * z) := by
  set w : ℝ → ℂ := fun x =>
    jacobiPolyP α β n x * (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) with hwdef
  have hP : Continuous fun x : ℝ => jacobiPolyP α β n (x : ℂ) :=
    ((analyticOnNhd_jacobiPolyP (α : ℂ) β n).continuousOn.comp_continuous
      continuous_ofReal (fun _ => Set.mem_univ _))
  have hw : IntervalIntegrable w volume (-1) 1 := by
    have h := (intervalIntegrable_jacobi_weight_cpow (a := (α : ℂ)) (b := (β : ℂ))
      (by simpa using hα) (by simpa using hβ)).continuousOn_mul hP.continuousOn
    exact h.congr fun x _ => by simp only [hwdef]; ring
  have hS := hasSum_integral_exp_neg_add_one_mul hw z
  set s : ℕ → ℂ := fun m =>
    ∫ x : ℝ in (-1 : ℝ)..1, (-z) ^ m / m ! * (((x : ℂ) + 1) ^ m * w x) with hsdef
  have hs (m : ℕ) : s m = (-z) ^ m / m ! * ((-1 : ℂ) ^ n *
      ((2 : ℂ) ^ ((α : ℂ) + (β + m + 1)) * Gamma (β + m + 1) *
        Gamma (1 + (α : ℂ) + n) * poch (-(m : ℂ)) n /
        (n.factorial * Gamma (1 + α + (β + m + 1) + n)))) := by
    simp only [hsdef, hwdef, intervalIntegral.integral_const_mul]
    rw [jacobi_moment hα hβ n m]
  have hzero : ∑ i ∈ Finset.range n, s i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [hs, poch_neg_nat_eq_zero (Finset.mem_range.mp hi)]; simp
  have hshift := (hasSum_nat_add_iff' n).mpr hS
  rw [hzero, sub_zero] at hshift
  set c : ℂ := (α : ℂ) + β + 2 * n + 2 with hcdef
  have hc0 : 0 < c.re := by
    simp [hcdef]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hcn : ∀ k : ℕ, c ≠ -k := fun k h => by
    have := congrArg re h; simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), hc0]
  have hb0 : 0 < ((β : ℂ) + n + 1).re := by
    simp; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hK := ((hasFPowerSeriesOnBall_kummerM (a := (β : ℂ) + n + 1) hcn).hasSum_mul_pow
    (z := -2 * z) (by simp)).mul_left
    ((-1 : ℂ) ^ n * (2 : ℂ) ^ ((α : ℂ) + β + n + 1) * Gamma ((α : ℂ) + n + 1) *
      Gamma ((β : ℂ) + n + 1) / (Gamma c * n.factorial) * z ^ n)
  have hK' : HasSum (fun k => s (k + n))
      ((-1 : ℂ) ^ n * (2 : ℂ) ^ ((α : ℂ) + β + n + 1) * Gamma ((α : ℂ) + n + 1) *
        Gamma ((β : ℂ) + n + 1) / (Gamma c * n.factorial) * z ^ n *
        kummerM ((β : ℂ) + n + 1) c (-2 * z)) := by
    convert hK using 1
    funext k
    rw [hs, DLMF.Gamma.poch_neg_nat_eq (k + n) n]
    simp only [show n ≤ k + n by omega, ↓reduceIte, Nat.add_sub_cancel]
    rw [show (β : ℂ) + ((k + n : ℕ) : ℂ) + 1 = ((β : ℂ) + n + 1) + k by push_cast; ring,
      show (1 : ℂ) + α + (((β : ℂ) + n + 1) + k) + n = c + k by simp only [hcdef]; ring,
      show (α : ℂ) + (((β : ℂ) + n + 1) + k) = ((α : ℂ) + β + n + 1) + k by ring,
      show (1 : ℂ) + α + n = (α : ℂ) + n + 1 by ring,
      Gamma_add_nat_eq_poch_mul_Gamma hb0, Gamma_add_nat_eq_poch_mul_Gamma hc0,
      cpow_add _ _ two_ne_zero, cpow_natCast, pow_add, neg_pow z, neg_pow z, mul_pow,
      neg_pow (2 : ℂ)]
    have h1 : poch ((β : ℂ) + n + 1) k ≠ 0 := poch_ne_zero_of_re_pos hb0 k
    have h2 : poch c k ≠ 0 := poch_ne_zero_of_re_pos hc0 k
    have h3 : Gamma c ≠ 0 := Gamma_ne_zero_of_re_pos hc0
    have h4 : ((k + n).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h5 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have h6 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have he : ((-1 : ℂ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    simp only [kummerMCoeff]
    field_simp
    rw [he]
    ring
  rw [hshift.unique hK', hcdef]

/-- DLMF 18.17.16, stated here so that the Gegenbauer transforms below can use it. -/
@[dlmf 18.17.E16]
theorem jacobi_fourier_transform {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) *
      jacobiPolyP α β n x * exp (I * x * y) =
      (I * y) ^ n * exp (I * y) / n.factorial * (2 : ℂ) ^ (n + α + β + 1 : ℂ) *
        Gamma (n + α + 1 : ℂ) * Gamma (n + β + 1 : ℂ) / Gamma (2 * n + α + β + 2 : ℂ) *
        kummerM (n + α + 1) (2 * n + α + β + 2) (-2 * I * y) := by
  have h := jacobi_laplace_aux hα hβ n (-I * y)
  have hint : ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) *
      jacobiPolyP α β n x * exp (I * x * y) =
      exp (-(I * y)) * ∫ x : ℝ in (-1 : ℝ)..1, exp (-((x : ℂ) + 1) * (-I * y)) *
        (jacobiPolyP α β n x * (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    have he : exp (-((x : ℂ) + 1) * (-I * y)) = exp (I * y) * exp (I * x * y) := by
      rw [← Complex.exp_add]; ring_nf
    simp only [he]
    have h1 : exp (-(I * y)) * exp (I * y) = 1 := by rw [← Complex.exp_add]; simp
    linear_combination (-(1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) *
      jacobiPolyP α β n x * exp (I * x * y)) * h1
  set c : ℂ := (α : ℂ) + β + 2 * n + 2 with hcdef
  have hc0 : 0 < c.re := by
    simp [hcdef]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hcn : ∀ k : ℕ, c ≠ -k := fun k h => by
    have := congrArg re h; simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), hc0]
  rw [hint, h, kummerM_kummer_transform hcn,
    show c - ((β : ℂ) + n + 1) = n + α + 1 by simp only [hcdef]; ring,
    show -(-2 * (-I * (y : ℂ))) = -2 * I * y by ring,
    show c = 2 * n + α + β + 2 by simp only [hcdef]; ring,
    show (α : ℂ) + β + n + 1 = n + α + β + 1 by ring,
    show (α : ℂ) + n + 1 = n + α + 1 by ring, show (β : ℂ) + n + 1 = n + β + 1 by ring]
  have he : exp (-(I * y)) * exp (-2 * (-I * y)) = exp (I * y) := by
    rw [← Complex.exp_add]; ring_nf
  have hn : (-1 : ℂ) ^ n * (-I * y) ^ n = (I * y) ^ n := by
    rw [← mul_pow]; ring_nf
  linear_combination (exp (-(I * y)) * (2 : ℂ) ^ ((n : ℂ) + α + β + 1) *
    Gamma ((n : ℂ) + α + 1) * Gamma ((n : ℂ) + β + 1) / (Gamma (2 * n + α + β + 2) * n !) *
    kummerM ((n : ℂ) + α + 1) (2 * n + α + β + 2) (-2 * I * y) * exp (-2 * (-I * y))) * hn +
    ((2 : ℂ) ^ ((n : ℂ) + α + β + 1) * Gamma ((n : ℂ) + α + 1) * Gamma ((n : ℂ) + β + 1) /
      (Gamma (2 * n + α + β + 2) * n !) * (I * y) ^ n *
      kummerM ((n : ℂ) + α + 1) (2 * n + α + β + 2) (-2 * I * y)) * he

@[dlmf 18.17.E16_5]
theorem ultrasphPoly_fourier_transform {lam : ℝ} (hlam : 0 < lam) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam n x * exp (I * x * y) =
      2 * Real.pi * I ^ n * Gamma (n + 2 * (lam : ℂ)) * besselJ (n + (lam : ℂ)) y /
        (n.factorial * Gamma (lam : ℂ) * (2 * y : ℂ) ^ (lam : ℂ)) := by
  have ha : -1 < lam - 1 / 2 := by linarith
  have hJ := jacobi_fourier_transform ha ha n y
  have hpoch : poch ((lam : ℂ) + 1 / 2) n ≠ 0 :=
    poch_ne_zero_of_re_pos (by simp; linarith) n
  have hint : ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam n x * exp (I * x * y) =
      poch (2 * (lam : ℂ)) n / poch ((lam : ℂ) + 1 / 2) n *
        ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ)) ^ ((lam - 1 / 2 : ℝ) : ℂ) *
          (1 + (x : ℂ)) ^ ((lam - 1 / 2 : ℝ) : ℂ) *
          jacobiPolyP ((lam - 1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) n x * exp (I * x * y) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun x hx => ?_
    have h1 : (1 - (x : ℂ) ^ 2) = ((1 - x : ℝ) : ℂ) * ((1 + x : ℝ) : ℂ) := by push_cast; ring
    rw [h1, mul_cpow_ofReal_nonneg (by linarith [hx.2]) (by linarith [hx.1]),
      ultrasphPoly_eq_jacobiPolyP n _ hpoch]
    push_cast
    ring
  rw [hint, hJ]
  push_cast
  set ν : ℂ := (n : ℂ) + lam with hν
  have hl0 : 0 < ((lam : ℂ) + 1 / 2).re := by simp; linarith
  have hν1 : 0 < (ν + 1).re := by simp [hν]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hνk : ∀ k : ℕ, ν + 1 ≠ -k := fun k h => by
    have := congrArg re h; simp [hν] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2ν : ∀ k : ℕ, 2 * ν + 1 ≠ -k := fun k h => by
    have := congrArg re h; simp [hν] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [show (n : ℂ) + ((lam : ℂ) - 1 / 2) + 1 = ν + 1 / 2 by simp only [hν]; ring,
    show 2 * (n : ℂ) + ((lam : ℂ) - 1 / 2) + ((lam : ℂ) - 1 / 2) + 2 = 2 * ν + 1 by
      simp only [hν]; ring,
    kummerM_kummer_transform h2ν,
    show 2 * ν + 1 - (ν + 1 / 2) = ν + 1 / 2 by ring, show -(-2 * I * (y : ℂ)) = 2 * I * y by ring,
    besselJ_eq_kummerM hνk h2ν]
  -- Gamma functions
  set T : ℂ := (2 : ℂ) ^ (lam : ℂ) with hT
  set Y : ℂ := (y : ℂ) ^ (lam : ℂ) with hY
  have hT0 : T ≠ 0 := by simp [hT]
  have hY0 : Y ≠ 0 := by
    simp [hY, cpow_eq_zero_iff, ofReal_ne_zero.mpr hy.ne']
  have hsq : ((√π : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have hpi : ((π : ℝ) : ℂ) = ((√π : ℝ) : ℂ) ^ 2 := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hnu : ν + 1 / 2 = ((lam : ℂ) + 1 / 2) + n := by simp only [hν]; ring
  have hG1 : Gamma (ν + 1 / 2) = poch ((lam : ℂ) + 1 / 2) n * Gamma ((lam : ℂ) + 1 / 2) := by
    rw [hnu, Gamma_add_nat_eq_poch_mul_Gamma hl0]
  have hl2 : 0 < (2 * (lam : ℂ)).re := by simp; linarith
  have hG2 : Gamma ((n : ℂ) + 2 * lam) = poch (2 * (lam : ℂ)) n * Gamma (2 * (lam : ℂ)) := by
    rw [add_comm, Gamma_add_nat_eq_poch_mul_Gamma hl2]
  have hd1 := Complex.Gamma_mul_Gamma_add_half (lam : ℂ)
  have hd2 := Complex.Gamma_mul_Gamma_add_half (ν + 1 / 2)
  rw [show ν + 1 / 2 + 1 / 2 = ν + 1 by ring, show 2 * (ν + 1 / 2) = 2 * ν + 1 by ring,
    hG1] at hd2
  have hc1 : (2 : ℂ) ^ (1 - 2 * (lam : ℂ)) * T ^ 2 = 2 := by
    rw [hT, sq, ← mul_assoc, ← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero,
      show 1 - 2 * (lam : ℂ) + lam + lam = 1 by ring, cpow_one]
  have hc2 : (2 : ℂ) ^ (1 - (2 * ν + 1)) * ((2 : ℂ) ^ n) ^ 2 * T ^ 2 = 1 := by
    rw [hT, sq, sq, ← cpow_natCast, ← mul_assoc, ← mul_assoc,
      ← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero,
      ← cpow_add _ _ two_ne_zero, show 1 - (2 * ν + 1) + n + n + lam + lam = 0 by
        simp only [hν]; ring, cpow_zero]
  have hc3 : (2 : ℂ) ^ ((n : ℂ) + ((lam : ℂ) - 1 / 2) + ((lam : ℂ) - 1 / 2) + 1) =
      (2 : ℂ) ^ n * T ^ 2 := by
    rw [hT, sq, ← cpow_natCast, ← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero]
    ring_nf
  have hy2 : ((y : ℂ) / 2) ^ ν = ((y : ℂ) / 2) ^ n * (((y : ℂ) / 2) ^ (lam : ℂ)) := by
    rw [hν, cpow_add _ _ (by simp [hy.ne']), cpow_natCast]
  have hyT : ((y : ℂ) / 2) ^ (lam : ℂ) * T = Y := by
    have h := mul_cpow_ofReal_nonneg (a := y / 2) (b := 2) (by positivity) (by norm_num)
      (lam : ℂ)
    rw [show ((y / 2 : ℝ) : ℂ) * ((2 : ℝ) : ℂ) = (y : ℂ) by push_cast; ring] at h
    rw [hT, hY, h]
    push_cast; ring
  have h2y : (2 * (y : ℂ)) ^ (lam : ℂ) = T * Y := by
    rw [hT, hY, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      mul_cpow_ofReal_nonneg (by norm_num) hy.le]
  have hT2 : T ^ 2 ≠ 0 := pow_ne_zero 2 hT0
  have hA : (2 : ℂ) ^ (1 - 2 * (lam : ℂ)) = 2 / T ^ 2 := eq_div_of_mul_eq hT2 hc1
  have hn2 : ((2 : ℂ) ^ n) ^ 2 * T ^ 2 ≠ 0 := mul_ne_zero (by simp) hT2
  have hB : (2 : ℂ) ^ (1 - (2 * ν + 1)) = 1 / (((2 : ℂ) ^ n) ^ 2 * T ^ 2) :=
    eq_div_of_mul_eq hn2 (by rw [← mul_assoc]; exact hc2)
  have hG3 : Gamma (2 * (lam : ℂ)) =
      Gamma (lam : ℂ) * Gamma ((lam : ℂ) + 1 / 2) * T ^ 2 / (2 * ((√π : ℝ) : ℂ)) := by
    rw [hd1, hA]; field_simp
  have hG5 : Gamma (2 * ν + 1) = poch ((lam : ℂ) + 1 / 2) n * Gamma ((lam : ℂ) + 1 / 2) *
      Gamma (ν + 1) * (((2 : ℂ) ^ n) ^ 2 * T ^ 2) / ((√π : ℝ) : ℂ) := by
    rw [hd2, hB]; field_simp
  have hyT' : ((y : ℂ) / 2) ^ (lam : ℂ) = Y / T := eq_div_of_mul_eq hT0 hyT
  have hE0 : exp (I * y) ≠ 0 := Complex.exp_ne_zero _
  have hE1 : exp (-2 * I * y) = ((exp (I * y)) ^ 2)⁻¹ := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_neg]; ring_nf
  have hE2 : exp (-I * y) = (exp (I * y))⁻¹ := by
    rw [← Complex.exp_neg]; ring_nf
  have hg1 : Gamma (lam : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using hlam)
  have hg2 : Gamma ((lam : ℂ) + 1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos hl0
  have hg4 : Gamma (ν + 1) ≠ 0 := Gamma_ne_zero_of_re_pos hν1
  have hfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  rw [hG5, hG2, hG3, hG1, hc3, hy2, h2y, hyT', hE1, hE2, hpi, mul_pow, div_pow]
  set Hp := poch ((lam : ℂ) + 1 / 2) n with hHp
  set Gp := poch (2 * (lam : ℂ)) n with hGp
  field_simp

/-- Moments of `P_n(1 - 2x²)` on `[0, 1]`, from the substitution `s = 1 - 2x²` and the
Jacobi moments: `∫₀¹ x^{2k+1} P_n(1-2x²) dx = k! (-k)_n / (2 (k+n+1)!)`. -/
private lemma lbsq_moment (n k : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, (x : ℂ) ^ (2 * k + 1) * legendrePolyP n (1 - 2 * (x : ℂ) ^ 2) =
      (1 / 2 : ℂ) * k ! * poch (-(k : ℂ)) n / ((k + n + 1) ! : ℂ) := by
  set F : ℝ → ℂ := fun s => legendrePolyP n (s : ℂ) * ((1 - (s : ℂ)) / 2) ^ k with hF
  have h1 : (∫ x : ℝ in (0 : ℝ)..1, (x : ℂ) ^ (2 * k + 1) *
      legendrePolyP n (1 - 2 * (x : ℂ) ^ 2)) =
        ∫ x : ℝ in (0 : ℝ)..1, (x : ℂ) * F (1 - 2 * x ^ 2) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hF]; push_cast
    rw [show ((1 : ℂ) - (1 - 2 * (x : ℂ) ^ 2)) / 2 = (x : ℂ) ^ 2 by ring, ← pow_mul]
    ring
  have hJ := jacobi_moment (α := 0) (β := 0) (by norm_num) (by norm_num) n k
  have hneg := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1) F
  norm_num only [neg_neg] at hneg
  have h2 : (∫ s : ℝ in (-1 : ℝ)..1, F s) = (2 : ℂ)⁻¹ ^ k * (-1 : ℂ) ^ n *
      ∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) + 1) ^ k *
        (jacobiPolyP ((0:ℝ):ℂ) ((0:ℝ):ℂ) n x * (1 - (x : ℂ)) ^ ((0:ℝ) : ℂ) *
          (1 + (x : ℂ)) ^ ((0:ℝ) : ℂ)) := by
    rw [← hneg, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hF, ofReal_zero, cpow_zero, mul_one]
    push_cast
    rw [legendrePolyP, jacobi_reflection (by norm_num) (by norm_num)]
    rw [show ((1 : ℂ) - -(s : ℂ)) / 2 = 2⁻¹ * ((s : ℂ) + 1) by ring, mul_pow]
    ring
  rw [h1, integral_mul_comp_one_sub_two_sq, h2, hJ]
  have hG1 : Gamma ((0:ℝ) + k + 1 : ℂ) = k ! := by
    rw [show ((0:ℝ) : ℂ) + k + 1 = (k : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
  have hG2 : Gamma (1 + ((0:ℝ):ℂ) + n) = n ! := by
    rw [show 1 + ((0:ℝ) : ℂ) + n = (n : ℂ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
  have hG3 : Gamma (1 + ((0:ℝ):ℂ) + (((0:ℝ):ℂ) + k + 1) + n) = (k + n + 1) ! := by
    rw [show 1 + ((0:ℝ) : ℂ) + (((0:ℝ):ℂ) + k + 1) + n = ((k + n + 1 : ℕ) : ℂ) + 1 by
      push_cast; ring, Gamma_nat_eq_factorial]
  have hP : (2 : ℂ) ^ (((0:ℝ):ℂ) + (((0:ℝ):ℂ) + k + 1)) = 2 ^ (k + 1) := by
    rw [show ((0:ℝ) : ℂ) + (((0:ℝ):ℂ) + k + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; ring,
      cpow_natCast]
  rw [hG1, hG2, hG3, hP]
  have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hkn : ((k + n + 1) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hs : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  rw [inv_pow, pow_succ]
  field_simp
  ring_nf
  rw [pow_mul]
  norm_num
  rw [sq, hs, mul_one]

/-- `x ↦ P_n(1 - 2x²)` is continuous. -/
private lemma lbsq_continuous (n : ℕ) :
    Continuous fun x : ℝ => legendrePolyP n (1 - 2 * (x : ℂ) ^ 2) := by
  simp_rw [legendre_eq_ultrasphPoly]
  exact (continuousOn_univ.1 (analyticOnNhd_ultrasphPoly _ n).continuousOn).comp (by fun_prop)

/-- Termwise integration of the sine series against `P_n(1 - 2x²)` on `[0, 1]`. -/
private lemma lbsq_hasSum_integral (n : ℕ) (y : ℝ) :
    HasSum (fun k : ℕ => (-1 : ℂ) ^ k * (y : ℂ) ^ (2 * k + 1) / ((2 * k + 1) ! : ℂ) *
        ∫ x : ℝ in (0 : ℝ)..1, (x : ℂ) ^ (2 * k + 1) * legendrePolyP n (1 - 2 * (x : ℂ) ^ 2))
      (∫ x : ℝ in (0 : ℝ)..1, legendrePolyP n (1 - 2 * (x : ℂ) ^ 2) * Real.sin (x * y)) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (lbsq_continuous n).continuousOn (s := Set.Icc (0 : ℝ) 1)
  set F : ℕ → ℝ → ℂ := fun k x => (-1 : ℂ) ^ k * (y : ℂ) ^ (2 * k + 1) / ((2 * k + 1) ! : ℂ) *
    ((x : ℂ) ^ (2 * k + 1) * legendrePolyP n (1 - 2 * (x : ℂ) ^ 2)) with hF
  have hc : ∀ k, Continuous (F k) := fun k => by
    simp only [hF]; exact continuous_const.mul ((by fun_prop : Continuous fun x : ℝ =>
      (x : ℂ) ^ (2 * k + 1)).mul (lbsq_continuous n))
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := F) (a := 0) (b := 1) (μ := volume)
    (f := fun x => legendrePolyP n (1 - 2 * (x : ℂ) ^ 2) * Real.sin (x * y))
    (fun k _ => |y| ^ (2 * k + 1) / ((2 * k + 1) ! : ℝ) * B)
    (fun k => (hc k).aestronglyMeasurable)
    (fun k => ae_of_all _ fun x hx => by
      rw [Set.uIoc_of_le zero_le_one] at hx
      have hx1 : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
      simp only [hF, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
      have hxa : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx1.1, hx1.2]
      have h1 : |x| ^ (2 * k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg x) hxa
      have h2 := hB x hx1
      have hf : (0 : ℝ) < ((2 * k + 1) ! : ℝ) := by positivity
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hf]
      calc |y| ^ (2 * k + 1) * (|x| ^ (2 * k + 1) * ‖legendrePolyP n (1 - 2 * (x : ℂ) ^ 2)‖)
          ≤ |y| ^ (2 * k + 1) * (1 * B) := by
            gcongr
      _ = _ := by ring)
    (ae_of_all _ fun x _ => ((Real.hasSum_sinh |y|).summable.mul_right B))
    intervalIntegrable_const
    (ae_of_all _ fun x _ => by
      have hs := (Complex.hasSum_ofReal.mpr (Real.hasSum_sin (x * y))).mul_left
        (legendrePolyP n (1 - 2 * (x : ℂ) ^ 2))
      refine hs.congr_fun fun k => ?_
      simp only [hF]; push_cast; ring)
  refine h.congr_fun fun k => ?_
  simp only [hF]
  rw [intervalIntegral.integral_const_mul]

/-- Coefficient identity matching the moment series with the series of `J_{n+1/2}²`
(DLMF 10.8.3). -/
private lemma lbsq_coeff (n m : ℕ) (y : ℝ) :
    (-1 : ℂ) ^ (m + n) * (y : ℂ) ^ (2 * (m + n) + 1) / ((2 * (m + n) + 1) ! : ℂ) *
      ((1 / 2 : ℂ) * (m + n) ! * poch (-((m + n : ℕ) : ℂ)) n / ((m + n + n + 1) ! : ℂ)) =
    (Real.pi : ℂ) / 2 * ((y : ℂ) / 2 / 2) ^ ((n + 1 / 2 : ℂ) + (n + 1 / 2 : ℂ)) *
      (poch ((n + 1 / 2 : ℂ) + (n + 1 / 2 : ℂ) + m + 1) m * (-(((y : ℂ) / 2) ^ 2 / 4)) ^ m /
        (m ! : ℂ) * (Gamma ((n + 1 / 2 : ℂ) + m + 1))⁻¹ * (Gamma ((n + 1 / 2 : ℂ) + m + 1))⁻¹) := by
  set k := m + n with hk
  have hexp : (n + 1 / 2 : ℂ) + (n + 1 / 2 : ℂ) = ((2 * n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [hexp, cpow_natCast]
  have hP : poch (-((k : ℕ) : ℂ)) n * (m ! : ℂ) = (-1) ^ n * (k ! : ℂ) := by
    rw [poch_neg_coe_nat]
    have h := Nat.factorial_mul_descFactorial (show n ≤ k by omega)
    rw [show k - n = m by omega] at h
    have h' : (m ! : ℂ) * (k.descFactorial n : ℂ) = k ! := by exact_mod_cast h
    linear_combination (-1 : ℂ) ^ n * h'
  have hQ : poch (((2 * n + 1 : ℕ) : ℂ) + m + 1) m * ((2 * n + m + 1) ! : ℂ) = (2 * k + 1) ! := by
    have h := poch_nat_succ_eq_choose_mul_factorial (2 * n + m + 1) m
    push_cast at h ⊢
    rw [show (2 * (n : ℂ) + 1 + m + 1) = 2 * n + m + 1 + 1 by ring, h]
    have hc := Nat.choose_mul_factorial_mul_factorial
      (show 2 * n + m + 1 ≤ 2 * n + m + 1 + m by omega)
    rw [show 2 * n + m + 1 + m - (2 * n + m + 1) = m by omega,
      show 2 * n + m + 1 + m = 2 * k + 1 by omega] at hc
    rw [show 2 * n + m + 1 + m = 2 * k + 1 by omega]
    have hc' : ((2 * k + 1).choose (2 * n + m + 1) : ℂ) * ((2 * n + m + 1) ! : ℂ) * (m ! : ℂ) =
      ((2 * k + 1) ! : ℂ) := by exact_mod_cast hc
    linear_combination hc'
  have hG : Gamma ((n + 1 / 2 : ℂ) + m + 1) =
      ((2 * k + 2) * (2 * k + 1) ! : ℂ) / (4 ^ (k + 1) * ((k + 1) * k ! : ℂ)) * Gamma (1 / 2) := by
    rw [show (n + 1 / 2 : ℂ) + m + 1 = 1 / 2 + ((k + 1 : ℕ) : ℂ) by rw [hk]; push_cast; ring,
      Gamma_nat_add_half, show 2 * (k + 1) = (2 * k + 1) + 1 by ring,
      Nat.factorial_succ (2 * k + 1),
      Nat.factorial_succ k]
    push_cast; ring
  have hpi : Gamma (1 / 2 : ℂ) ^ 2 = Real.pi := by
    rw [Complex.Gamma_one_half_eq, ← cpow_nat_mul]; norm_num
  have hk' : m + n + n + 1 = 2 * n + m + 1 := by omega
  rw [hk', hG]
  have hg : Gamma (1 / 2 : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hf1 : ((2 * k + 1) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf2 : ((k) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf3 : ((m) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf4 : ((2 * n + m + 1) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hk2 : (2 * (k : ℂ) + 2) ≠ 0 := by
    have h : ((2 * k + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast at h; exact h
  rw [← hpi]
  have hs : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  rw [eq_div_of_mul_eq hf3 hP, eq_div_of_mul_eq hf4 hQ]
  field_simp
  ring_nf
  rw [hk, show (-1 / 16 : ℂ) = -1 * 4⁻¹ ^ 2 by norm_num, mul_pow, ← pow_mul, one_div, inv_pow,
    inv_pow]
  field_simp
  ring_nf
  rw [show ((-1 : ℂ)) ^ (n * 2) = 1 by rw [mul_comm, pow_mul]; simp, mul_one]

/-- DLMF 18.17.21 for `y > 0`. -/
private lemma lbsq_pos (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ in (0 : ℝ)..1, legendrePolyP n (1 - 2 * (x : ℂ) ^ 2) * Real.sin (x * y) =
      Real.pi / 2 * besselJ (n + 1 / 2 : ℂ) ((y : ℂ) / 2) ^ 2 := by
  have hL := lbsq_hasSum_integral n y
  simp_rw [lbsq_moment] at hL
  rw [← hasSum_nat_add_iff' n] at hL
  rw [Finset.sum_eq_zero (fun k hk => by
    rw [poch_neg_nat_eq_zero (Finset.mem_range.mp hk)]; simp), sub_zero] at hL
  have hz : ((y : ℂ) / 2) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left; simp; linarith
  rw [sq, besselJ_mul_besselJ _ _ hz]
  have hR := hL.congr_fun (fun m => (lbsq_coeff n m y).symm)
  rw [← hR.tsum_eq, tsum_mul_left, mul_assoc]

/-- `J_{n+1/2}(w)² = (w/2)^{2n+1} 𝐅(;n+3/2;-w²/4)²` for all `w`, without a branch condition. -/
private lemma lbsq_bessel_sq (n : ℕ) (w : ℂ) :
    besselJ (n + 1 / 2 : ℂ) w ^ 2 = (w / 2) ^ (2 * n + 1) *
      regularizedHGFun (∅ : Multiset ℂ) {(n + 1 / 2 : ℂ) + 1} (-(w ^ 2 / 4)) ^ 2 := by
  rw [besselJ_eq_regularized, mul_pow, ← cpow_nat_mul,
    show ((2 : ℕ) : ℂ) * (n + 1 / 2 : ℂ) = ((2 * n + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast]

@[dlmf 18.17.E21]
theorem legendre_bessel_square_integral (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in (0 : ℝ)..1, legendrePolyP n (1 - 2 * (x : ℂ) ^ 2) * Real.sin (x * y) =
      Real.pi / 2 * besselJ (n + 1 / 2 : ℂ) ((y : ℂ) / 2) ^ 2 := by
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · have h := lbsq_pos n (neg_pos.mpr hy)
    rw [lbsq_bessel_sq] at h ⊢
    have hl : (∫ x : ℝ in (0 : ℝ)..1, legendrePolyP n (1 - 2 * (x : ℂ) ^ 2) * Real.sin (x * y)) =
        -∫ x : ℝ in (0 : ℝ)..1, legendrePolyP n (1 - 2 * (x : ℂ) ^ 2) * Real.sin (x * -y) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [mul_neg, Real.sin_neg]; push_cast; ring
    rw [hl, h]
    push_cast
    rw [show -(y : ℂ) / 2 / 2 = -((y : ℂ) / 2 / 2) by ring, Odd.neg_pow (by exact ⟨n, rfl⟩),
      neg_div, neg_sq]
    ring
  · simp only [mul_zero, Real.sin_zero, ofReal_zero, zero_div, intervalIntegral.integral_zero]
    rw [lbsq_bessel_sq]; simp
  · exact lbsq_pos n hy

@[dlmf 18.17.E22]
theorem hermite_fourier_eigenfunction (n : ℕ) (y : ℝ) :
    (∫ x : ℝ, exp (-(x : ℂ) ^ 2 / 4) * (aeval (x : ℂ) (hermite n) : ℂ) * exp (I * x * y / 2)) /
      (2 * Real.sqrt Real.pi) = I ^ n * exp (-(y : ℂ) ^ 2 / 4) * aeval (y : ℂ) (hermite n) := by
  let r := Real.sqrt 2
  have hr : 0 < r := Real.sqrt_pos.mpr two_pos
  have hr0 : r ≠ 0 := hr.ne'
  have hr2 : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  let c := Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi)
  let F : ℝ → ℂ := fun x => exp (-(x : ℂ) ^ 2 / 4) * aeval (x : ℂ) (hermite n) * exp (I * x * y / 2)
  have hscale := Measure.integral_comp_mul_left F r
  have hx (x : ℝ) : F (r * x) = (c : ℂ) *
      (exp (I * x * ↑(y / r)) * (TauCeti.hermiteFunction n x : ℂ)) := by
    dsimp [F]
    rw [hermite_envelope]
    change (c : ℂ) * (TauCeti.hermiteFunction n (r * x / r) : ℂ) * exp (I * ↑(r * x) * y / 2) = _
    rw [mul_div_cancel_left₀ x hr0]
    have he : I * ↑(r * x) * y / 2 = I * x * ↑(y / r) := by
      push_cast
      have hrc : (r : ℂ) ^ 2 = 2 := by exact_mod_cast hr2
      have hr0c : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0
      field_simp
      linear_combination (x : ℂ) * y * hrc
    rw [he]
    ring
  simp_rw [hx] at hscale
  rw [integral_const_mul, hermiteFunction_integral, abs_of_pos (inv_pos.mpr hr), Complex.real_smul] at hscale
  have hrs : (r : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ) = 2 * (Real.sqrt Real.pi : ℂ) := by
    norm_cast
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    change r * (r * Real.sqrt Real.pi) = _
    rw [← mul_assoc, ← pow_two, hr2]
  rw [show I ^ n * exp (-(y : ℂ) ^ 2 / 4) * aeval (y : ℂ) (hermite n) =
    I ^ n * (exp (-(y : ℂ) ^ 2 / 4) * aeval (y : ℂ) (hermite n)) by ring, hermite_envelope]
  change (∫ x, F x) / (2 * ↑(Real.sqrt Real.pi)) = I ^ n * ((c : ℂ) * ↑(TauCeti.hermiteFunction n (y / r)))
  have hr0c : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0
  have hp0 : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  rw [ofReal_inv] at hscale
  field_simp [hr0c] at hscale
  apply (div_eq_iff (mul_ne_zero two_ne_zero hp0)).mpr
  calc
    _ = (c : ℂ) * (r * ↑(Real.sqrt (2 * Real.pi))) * I ^ n * ↑(TauCeti.hermiteFunction n (y / r)) := by
      linear_combination -hscale
    _ = _ := by rw [hrs]; ring

/-! ### Fourier transforms of `He_n(x) e^{-x²/2}` -/

/-- The Hermite–Gaussian function `He_n(x) e^{-x²/2}`. -/
def hermiteGauss (n : ℕ) (x : ℝ) : ℝ := aeval x (hermite n) * Real.exp (-(x ^ 2 / 2))

/-- `He_n(x) e^{-x²/2} = (-1)^n dⁿ/dxⁿ e^{-x²/2}`. -/
theorem hermiteGauss_eq_iterate (n : ℕ) (x : ℝ) :
    hermiteGauss n x = (-1) ^ n * deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x := by
  rw [deriv_gaussian_eq_hermite_mul_gaussian, hermiteGauss, ← mul_assoc, ← mul_assoc,
    ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- `(He_n e^{-x²/2})' = -He_{n+1} e^{-x²/2}`. -/
theorem hasDerivAt_hermiteGauss (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteGauss n) (-hermiteGauss (n + 1) x) x := by
  have hg : ContDiff ℝ ⊤ fun y : ℝ => Real.exp (-(y ^ 2 / 2)) := by fun_prop
  have hd : Differentiable ℝ (deriv^[n] fun y : ℝ => Real.exp (-(y ^ 2 / 2))) := by
    rw [← iteratedDeriv_eq_iterate]
    exact hg.differentiable_iteratedDeriv n (by exact_mod_cast WithTop.coe_lt_top _)
  have hfun : hermiteGauss n = fun x =>
      (-1) ^ n * deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x :=
    funext (hermiteGauss_eq_iterate n)
  rw [hfun, hermiteGauss_eq_iterate, Function.iterate_succ_apply', pow_succ]
  convert ((hd x).hasDerivAt.const_mul ((-1 : ℝ) ^ n)) using 1
  ring

/-- `He_n(x) e^{-x²/2}` is integrable (Tau Ceti `integrable_aeval_mul_gaussian`). -/
theorem integrable_hermiteGauss (n : ℕ) : Integrable (hermiteGauss n) :=
  TauCeti.integrable_aeval_mul_gaussian (hermite n)

/-- The positive-phase Fourier transform of `He_n(x) e^{-x²/2}`. -/
theorem integral_exp_mul_hermiteGauss (n : ℕ) (y : ℝ) :
    ∫ x : ℝ, cexp (I * y * x) * (hermiteGauss n x : ℂ) =
      (I * y) ^ n * (Real.sqrt (2 * π) * Real.exp (-(y ^ 2 / 2)) : ℝ) := by
  induction n with
  | zero =>
    have h := fourierIntegral_gaussian (b := 1 / 2) (by norm_num) (y : ℂ)
    simp only [hermiteGauss, hermite_zero, map_one, one_mul, pow_zero]
    convert h using 1
    · congr 1; funext x; congr 1; push_cast; congr 1; ring
    · rw [show (π : ℂ) / (1 / 2) = 2 * π by ring, Complex.ofReal_mul, Real.sqrt_eq_rpow,
        Complex.ofReal_cpow (by positivity), Complex.ofReal_exp]
      push_cast
      congr 2
      ring
  | succ n ih =>
    have hu : ∀ x : ℝ, HasDerivAt (fun x : ℝ => cexp (I * y * x)) (I * y * cexp (I * y * x)) x :=
      fun x => by
        have := ((hasDerivAt_id (x : ℂ)).const_mul (I * y)).cexp.comp_ofReal
        simpa [mul_comm] using this
    have hv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (hermiteGauss n x : ℂ))
        ((-hermiteGauss (n + 1) x : ℝ) : ℂ) x :=
      fun x => (hasDerivAt_hermiteGauss n x).ofReal_comp
    have hint : ∀ m, Integrable fun x : ℝ => cexp (I * y * x) * (hermiteGauss m x : ℂ) := by
      intro m
      refine (integrable_hermiteGauss m).ofReal.bdd_mul (c := 1) ?_ ?_
      · exact (by fun_prop : Continuous fun x : ℝ => cexp (I * y * x)).aestronglyMeasurable
      · refine Eventually.of_forall fun x => le_of_eq ?_
        rw [Complex.norm_exp]
        simp
    have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hu x)
      (fun x _ => hv x)
      ((hint (n + 1)).neg.congr (Eventually.of_forall fun x => by simp))
      (((hint n).const_mul (I * y)).congr (Eventually.of_forall fun x => by simp; ring))
      (hint n)
    simp only [ofReal_neg, mul_neg, integral_neg, neg_inj] at hibp
    rw [hibp, show (fun x : ℝ => I * y * cexp (I * y * x) * (hermiteGauss n x : ℂ)) =
      fun x : ℝ => I * y * (cexp (I * y * x) * (hermiteGauss n x : ℂ)) by funext x; ring,
      integral_const_mul, ih, pow_succ]
    ring


/-- `e^{iyx} He_n(x) e^{-x²/2}` is integrable. -/
theorem integrable_exp_mul_hermiteGauss (n : ℕ) (y : ℝ) :
    Integrable fun x : ℝ => cexp (I * y * x) * (hermiteGauss n x : ℂ) := by
  refine (integrable_hermiteGauss n).ofReal.bdd_mul (c := 1) ?_ ?_
  · exact (by fun_prop : Continuous fun x : ℝ => cexp (I * y * x)).aestronglyMeasurable
  · refine Eventually.of_forall fun x => le_of_eq ?_
    rw [Complex.norm_exp]
    simp

/-- Rewriting `e^{iyx}` as `e^{(yx) i}`. -/
theorem exp_I_mul_eq (y x : ℝ) : cexp (I * y * x) = cexp (((y * x : ℝ) : ℂ) * I) := by
  push_cast; ring_nf

/-- The cosine transform of `He_n(x) e^{-x²/2}` over `ℝ`. -/
theorem integral_cos_mul_hermiteGauss (n : ℕ) (y : ℝ) :
    ∫ x : ℝ, Real.cos (y * x) * hermiteGauss n x =
      ((I * y) ^ n).re * (Real.sqrt (2 * π) * Real.exp (-(y ^ 2 / 2))) := by
  have h := congrArg Complex.re (integral_exp_mul_hermiteGauss n y)
  have hr := integral_re (integrable_exp_mul_hermiteGauss n y)
  simp only [RCLike.re_to_complex] at hr
  rw [← hr, Complex.re_mul_ofReal] at h
  rw [← h]
  congr 1; funext x
  rw [exp_I_mul_eq, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]

/-- The sine transform of `He_n(x) e^{-x²/2}` over `ℝ`. -/
theorem integral_sin_mul_hermiteGauss (n : ℕ) (y : ℝ) :
    ∫ x : ℝ, Real.sin (y * x) * hermiteGauss n x =
      ((I * y) ^ n).im * (Real.sqrt (2 * π) * Real.exp (-(y ^ 2 / 2))) := by
  have h := congrArg Complex.im (integral_exp_mul_hermiteGauss n y)
  have hi := integral_im (integrable_exp_mul_hermiteGauss n y)
  simp only [RCLike.im_to_complex] at hi
  rw [← hi, Complex.im_mul_ofReal] at h
  rw [← h]
  congr 1; funext x
  rw [exp_I_mul_eq, Complex.im_mul_ofReal, Complex.exp_ofReal_mul_I_im]

/-- `√(2π)/2 = √(π/2)`. -/
theorem sqrt_two_pi_div_two : Real.sqrt (2 * π) / 2 = Real.sqrt (π / 2) := by
  rw [show π / 2 = (2 * π) / 2 ^ 2 by ring, Real.sqrt_div' _ (by positivity),
    Real.sqrt_sq (by norm_num)]

@[dlmf 18.17.E23]
theorem hermite_even_cosine_transform (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-(x ^ 2) / 2) * (aeval x (hermite (2 * n)) : ℝ) * Real.cos (x * y) =
      (-1 : ℝ) ^ n * Real.sqrt (Real.pi / 2) * y ^ (2 * n) * Real.exp (-(y ^ 2) / 2) := by
  set f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2) / 2) * (aeval x (hermite (2 * n)) : ℝ) *
    Real.cos (x * y) with hf
  have heven : ∀ x, f |x| = f x := by
    intro x
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, hf]
      simp only [hermite_aeval_neg, pow_mul, one_pow, one_mul, neg_mul, Real.cos_neg,
        even_two, Even.neg_pow]
  have habs := integral_comp_abs (f := f)
  simp_rw [heven] at habs
  have hfull : ∫ x, f x = ∫ x : ℝ, Real.cos (y * x) * hermiteGauss (2 * n) x := by
    congr 1; funext x
    simp only [hf, hermiteGauss, neg_div, mul_comm x y]
    ring
  rw [hfull, integral_cos_mul_hermiteGauss, mul_pow, pow_mul, I_sq] at habs
  have hre : (((-1 : ℂ) ^ n) * (y : ℂ) ^ (2 * n)).re = (-1 : ℝ) ^ n * y ^ (2 * n) := by
    rw [← Complex.ofReal_pow, Complex.re_mul_ofReal]
    norm_cast
  rw [hre] at habs
  rw [← sqrt_two_pi_div_two, neg_div]
  linarith

@[dlmf 18.17.E27]
theorem hermite_odd_sine_transform (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-(x ^ 2) / 2) * (aeval x (hermite (2 * n + 1)) : ℝ) * Real.sin (x * y) =
      (-1 : ℝ) ^ n * Real.sqrt (Real.pi / 2) * y ^ (2 * n + 1) * Real.exp (-(y ^ 2) / 2) := by
  set f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2) / 2) * (aeval x (hermite (2 * n + 1)) : ℝ) *
    Real.sin (x * y) with hf
  have heven : ∀ x, f |x| = f x := by
    intro x
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, hf]
      simp only [hermite_aeval_neg, neg_mul, Real.sin_neg, neg_sq]
      rw [pow_succ (-1 : ℝ), pow_mul (-1 : ℝ), neg_one_sq, one_pow]
      ring
  have habs := integral_comp_abs (f := f)
  simp_rw [heven] at habs
  have hfull : ∫ x, f x = ∫ x : ℝ, Real.sin (y * x) * hermiteGauss (2 * n + 1) x := by
    congr 1; funext x
    simp only [hf, hermiteGauss, neg_div, mul_comm x y]
    ring
  rw [hfull, integral_sin_mul_hermiteGauss, mul_pow, pow_succ, pow_mul, I_sq] at habs
  have him : ((-1 : ℂ) ^ n * I * (y : ℂ) ^ (2 * n + 1)).im =
      (-1 : ℝ) ^ n * y ^ (2 * n + 1) := by
    rw [show (-1 : ℂ) ^ n * I * (y : ℂ) ^ (2 * n + 1) =
      (((-1 : ℝ) ^ n * y ^ (2 * n + 1) : ℝ) : ℂ) * I by push_cast; ring, Complex.mul_I_im,
      Complex.ofReal_re]
  rw [him] at habs
  rw [← sqrt_two_pi_div_two, neg_div]
  linarith

/-- The product formula for Mathlib's probabilists' Hermite normalization. -/
theorem hermite_linearization (m n : ℕ) (x : ℝ) :
    (aeval x (hermite m) : ℝ) * aeval x (hermite n) =
      ∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℝ) * n.choose k * k.factorial *
        aeval x (hermite (m + n - 2 * k)) := by
  let s := Real.sqrt 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = 2 := by simp [s]
  have hscale (j : ℕ) : (aeval (x / s) (hermitePolyH j) : ℝ) =
      s ^ j * aeval x (hermite j) := by
    rw [aeval_hermitePolyH_eq_hermite]
    have hpow : (2 : ℝ) ^ (j / 2 : ℝ) = s ^ j := by
      rw [show s = (2 : ℝ) ^ (1 / 2 : ℝ) by dsimp [s]; rw [Real.sqrt_eq_rpow],
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    rw [hpow, show Real.sqrt 2 * (x / s) = x by dsimp [s]; field_simp]
  have hcast (j : ℕ) : (aeval ((x / s : ℝ) : ℂ) (hermitePolyH j) : ℂ) =
      ((aeval (x / s) (hermitePolyH j) : ℝ) : ℂ) :=
    aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) (x / s) (hermitePolyH j)
  have hc := hermitePolyH_linearization m n ((x / s : ℝ) : ℂ)
  simp_rw [hcast] at hc
  have hr : (aeval (x / s) (hermitePolyH m) : ℝ) * aeval (x / s) (hermitePolyH n) =
      ∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℝ) * n.choose k * 2 ^ k * k.factorial *
        aeval (x / s) (hermitePolyH (m + n - 2 * k)) := by exact_mod_cast hc
  simp_rw [hscale] at hr
  have hpow (k : ℕ) (hk : k ∈ Finset.range (min m n + 1)) :
      (2 : ℝ) ^ k * s ^ (m + n - 2 * k) = s ^ (m + n) := by
    have hle : 2 * k ≤ m + n := by have := Finset.mem_range.mp hk; omega
    rw [← hs2, ← pow_mul, ← pow_add, Nat.add_sub_of_le hle]
  apply mul_left_cancel₀ (pow_ne_zero (m + n) hs.ne')
  calc
    _ = (s ^ m * (aeval x (hermite m) : ℝ)) * (s ^ n * aeval x (hermite n)) := by
      rw [pow_add]; ring
    _ = _ := hr
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have := hpow k hk
      linear_combination (m.choose k : ℝ) * n.choose k * k.factorial *
        (aeval x (hermite (m + n - 2 * k)) : ℝ) * this

/-- The finite contraction sum in a Hermite transform is a Laguerre polynomial. -/
theorem hermite_laguerrePolyL_sum (n l : ℕ) (u : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + l).choose k * k.factorial *
      (-1 : ℂ) ^ (n - k) * u ^ (2 * (n - k) + l) =
      n.factorial * u ^ l * laguerrePolyL l n (u ^ 2) := by
  have hl : ∀ k : ℕ, (l : ℂ) + 1 ≠ -k :=
    not_neg_nat_of_re_pos (by simp; positivity)
  rw [laguerrePolyL_eq_sum hl, Finset.mul_sum, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
  rw [show n + 1 - 1 - j = n - j by omega, Nat.sub_sub_self hjn]
  have hN : (n.choose (n - j) : ℂ) * (n - j).factorial * j.factorial = n.factorial := by
    exact_mod_cast (by simpa [Nat.sub_sub_self hjn] using
      Nat.choose_mul_factorial_mul_factorial (Nat.sub_le n j))
  have hL : ((n + l).choose (n - j) : ℂ) * (n - j).factorial * (l + j).factorial =
      (n + l).factorial := by
    exact_mod_cast (by simpa [show n + l - (n - j) = l + j by omega] using
      Nat.choose_mul_factorial_mul_factorial (show n - j ≤ n + l by omega))
  have hP : ((l + j).factorial : ℂ) * poch ((l : ℂ) + 1 + j) (n - j) = (n + l).factorial := by
    have he := factorial_mul_ascPochhammer ℂ (l + j) (n - j)
    simpa only [poch, Nat.add_sub_of_le (show j ≤ n + l by omega),
      show l + j + (n - j) = n + l by omega, Nat.cast_add,
      show (l : ℂ) + j + 1 = l + 1 + j by ring] using he
  have hcoeff : (n.choose (n - j) : ℂ) * (n + l).choose (n - j) * (n - j).factorial =
      n.factorial * (poch ((l : ℂ) + 1 + j) (n - j) /
        ((n - j).factorial * j.factorial : ℂ)) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff (mul_ne_zero (Nat.cast_ne_zero.mpr (n - j).factorial_ne_zero)
      (Nat.cast_ne_zero.mpr j.factorial_ne_zero))).mpr
    calc
      _ = ((n.choose (n - j) : ℂ) * (n - j).factorial * j.factorial) *
          (((n + l).choose (n - j) : ℂ) * (n - j).factorial) := by ring
      _ = n.factorial * poch ((l : ℂ) + 1 + j) (n - j) := by
        rw [hN]
        congr 1
        apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr (l + j).factorial_ne_zero)
        rw [hL]
        simpa [mul_comm] using hP.symm
  rw [hcoeff, neg_pow (u ^ 2), pow_add, pow_mul]
  ring

@[dlmf 18.17.E25]
theorem hermite_product_cosine_transform (m n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermite n) : ℂ) *
      aeval (x : ℂ) (hermite (n + 2 * m)) * Real.cos (x * y) =
      (-1 : ℂ) ^ m * Real.sqrt (Real.pi / 2) * n.factorial * (y : ℂ) ^ (2 * m) *
        exp (-(y : ℂ) ^ 2 / 2) * laguerrePolyL (2 * m) n ((y : ℂ) ^ 2) := by
  have hcast (j : ℕ) (x : ℝ) : (aeval (x : ℂ) (hermite j) : ℂ) =
      ((aeval x (hermite j) : ℝ) : ℂ) :=
    aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) x (hermite j)
  have hexp (x : ℝ) : exp (-(x : ℂ) ^ 2 / 2) = (Real.exp (-(x ^ 2) / 2) : ℂ) := by
    rw [ofReal_exp]
    congr 1
    push_cast
    ring
  let G (j : ℕ) (x : ℝ) : ℂ := exp (-(x : ℂ) ^ 2 / 2) *
    aeval (x : ℂ) (hermite j) * Real.cos (x * y)
  have hi (j : ℕ) : Integrable (G j) := by
    have ht := (integrable_hermiteGauss j).mul_bdd
      (by fun_prop : Continuous (fun x : ℝ => Real.cos (x * y))).aestronglyMeasurable
      (Eventually.of_forall fun x => show ‖Real.cos (x * y)‖ ≤ (1 : ℝ) by
        simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (x * y))
    apply ht.ofReal.congr
    filter_upwards [] with x
    dsimp only [G]
    rw [hexp, hcast]
    simp only [hermiteGauss, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_mul, neg_div]
    ring_nf
  have hlin (x : ℝ) : (aeval (x : ℂ) (hermite n) : ℂ) *
      aeval (x : ℂ) (hermite (n + 2 * m)) =
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + 2 * m).choose k * k.factorial *
          aeval (x : ℂ) (hermite (n + (n + 2 * m) - 2 * k)) := by
    simp_rw [hcast]
    have hr := hermite_linearization n (n + 2 * m) x
    rw [min_eq_left (by omega)] at hr
    exact_mod_cast hr
  have he : (∫ x : ℝ in Set.Ioi 0, exp (-(x : ℂ) ^ 2 / 2) *
      (aeval (x : ℂ) (hermite n) : ℂ) * aeval (x : ℂ) (hermite (n + 2 * m)) *
        Real.cos (x * y)) = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℂ) * (n + 2 * m).choose k * k.factorial *
        ∫ x : ℝ in Set.Ioi 0, G (n + (n + 2 * m) - 2 * k) x := by
    have he (x : ℝ) : exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermite n) : ℂ) *
        aeval (x : ℂ) (hermite (n + 2 * m)) * Real.cos (x * y) =
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + 2 * m).choose k * k.factorial *
          G (n + (n + 2 * m) - 2 * k) x := by
      rw [mul_assoc (exp _) _ _, hlin]
      simp only [Finset.mul_sum, Finset.sum_mul, G]
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp_rw [he]
    rw [integral_finsetSum _ (fun k _ => (hi _).integrableOn.const_mul _)]
    simp_rw [integral_const_mul]
  have htrans (j : ℕ) : (∫ x : ℝ in Set.Ioi 0, G (2 * j) x) =
      (-1 : ℂ) ^ j * Real.sqrt (Real.pi / 2) * (y : ℂ) ^ (2 * j) *
        exp (-(y : ℂ) ^ 2 / 2) := by
    simp only [G, hexp, hcast, ← ofReal_mul, _root_.integral_complex_ofReal]
    rw [hermite_even_cosine_transform j y]
    push_cast
    ring
  rw [he]
  have hsum := hermite_laguerrePolyL_sum n (2 * m) (y : ℂ)
  calc
    _ = ((-1 : ℂ) ^ m * Real.sqrt (Real.pi / 2) * exp (-(y : ℂ) ^ 2 / 2)) *
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + 2 * m).choose k * k.factorial *
          (-1 : ℂ) ^ (n - k) * (y : ℂ) ^ (2 * (n - k) + 2 * m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
      rw [show n + (n + 2 * m) - 2 * k = 2 * (n - k + m) by omega,
        htrans, pow_add, show 2 * (n - k + m) = 2 * (n - k) + 2 * m by omega]
      ring
    _ = _ := by
      try simp only [← Nat.add_assoc] at hsum
      rw [hsum]
      push_cast
      ring

@[dlmf 18.17.E26]
theorem hermite_product_sine_transform (m n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermite n) : ℂ) *
      aeval (x : ℂ) (hermite (n + 2 * m + 1)) * Real.sin (x * y) =
      (-1 : ℂ) ^ m * Real.sqrt (Real.pi / 2) * n.factorial * (y : ℂ) ^ (2 * m + 1) *
        exp (-(y : ℂ) ^ 2 / 2) * laguerrePolyL (2 * m + 1) n ((y : ℂ) ^ 2) := by
  have hcast (j : ℕ) (x : ℝ) : (aeval (x : ℂ) (hermite j) : ℂ) =
      ((aeval x (hermite j) : ℝ) : ℂ) :=
    aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) x (hermite j)
  have hexp (x : ℝ) : exp (-(x : ℂ) ^ 2 / 2) = (Real.exp (-(x ^ 2) / 2) : ℂ) := by
    rw [ofReal_exp]
    congr 1
    push_cast
    ring
  let G (j : ℕ) (x : ℝ) : ℂ := exp (-(x : ℂ) ^ 2 / 2) *
    aeval (x : ℂ) (hermite j) * Real.sin (x * y)
  have hi (j : ℕ) : Integrable (G j) := by
    have ht := (integrable_hermiteGauss j).mul_bdd
      (by fun_prop : Continuous (fun x : ℝ => Real.sin (x * y))).aestronglyMeasurable
      (Eventually.of_forall fun x => show ‖Real.sin (x * y)‖ ≤ (1 : ℝ) by
        simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (x * y))
    apply ht.ofReal.congr
    filter_upwards [] with x
    dsimp only [G]
    rw [hexp, hcast]
    simp only [hermiteGauss, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_mul, neg_div]
    ring_nf
  have hlin (x : ℝ) : (aeval (x : ℂ) (hermite n) : ℂ) *
      aeval (x : ℂ) (hermite (n + 2 * m + 1)) =
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + 2 * m + 1).choose k * k.factorial *
          aeval (x : ℂ) (hermite (n + (n + 2 * m + 1) - 2 * k)) := by
    simp_rw [hcast]
    have hr := hermite_linearization n (n + 2 * m + 1) x
    rw [min_eq_left (by omega)] at hr
    exact_mod_cast hr
  have he : (∫ x : ℝ in Set.Ioi 0, exp (-(x : ℂ) ^ 2 / 2) *
      (aeval (x : ℂ) (hermite n) : ℂ) * aeval (x : ℂ) (hermite (n + 2 * m + 1)) *
        Real.sin (x * y)) = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℂ) * (n + 2 * m + 1).choose k * k.factorial *
        ∫ x : ℝ in Set.Ioi 0, G (n + (n + 2 * m + 1) - 2 * k) x := by
    have he (x : ℝ) : exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermite n) : ℂ) *
        aeval (x : ℂ) (hermite (n + 2 * m + 1)) * Real.sin (x * y) =
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + 2 * m + 1).choose k * k.factorial *
          G (n + (n + 2 * m + 1) - 2 * k) x := by
      rw [mul_assoc (exp _) _ _, hlin]
      simp only [Finset.mul_sum, Finset.sum_mul, G]
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp_rw [he]
    rw [integral_finsetSum _ (fun k _ => (hi _).integrableOn.const_mul _)]
    simp_rw [integral_const_mul]
  have htrans (j : ℕ) : (∫ x : ℝ in Set.Ioi 0, G (2 * j + 1) x) =
      (-1 : ℂ) ^ j * Real.sqrt (Real.pi / 2) * (y : ℂ) ^ (2 * j + 1) *
        exp (-(y : ℂ) ^ 2 / 2) := by
    simp only [G, hexp, hcast, ← ofReal_mul, _root_.integral_complex_ofReal]
    rw [hermite_odd_sine_transform j y]
    push_cast
    ring
  rw [he]
  have hsum := hermite_laguerrePolyL_sum n (2 * m + 1) (y : ℂ)
  calc
    _ = ((-1 : ℂ) ^ m * Real.sqrt (Real.pi / 2) * exp (-(y : ℂ) ^ 2 / 2)) *
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + 2 * m + 1).choose k * k.factorial *
          (-1 : ℂ) ^ (n - k) * (y : ℂ) ^ (2 * (n - k) + 2 * m + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
      rw [show n + (n + 2 * m + 1) - 2 * k = 2 * (n - k + m) + 1 by omega,
        htrans, pow_add, show 2 * (n - k + m) + 1 = 2 * (n - k) + 2 * m + 1 by omega]
      ring
    _ = _ := by
      try simp only [← Nat.add_assoc] at hsum
      rw [hsum]
      push_cast
      ring

@[dlmf 18.17.E33]
theorem jacobi_laplace_transform {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) (z : ℂ) :
    ∫ x : ℝ in (-1 : ℝ)..1, exp (-((x : ℂ) + 1) * z) * jacobiPolyP α β n x *
      (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) =
      (-1 : ℂ) ^ n * (2 : ℂ) ^ (α + β + n + 1 : ℂ) * Gamma (α + n + 1 : ℂ) *
      Gamma (β + n + 1 : ℂ) / (Gamma (α + β + 2 * n + 2 : ℂ) * n.factorial) *
      z ^ n * kummerM (β + n + 1 : ℂ) (α + β + 2 * n + 2 : ℂ) (-2 * z) := by
  convert jacobi_laplace_aux hα hβ n z using 1
  exact intervalIntegral.integral_congr fun x _ => by ring

section LaguerreProductLaplace

set_option maxHeartbeats 1000000

/-- Complex scaling of a finite Gamma moment. -/
theorem scaled_monomial_moment {α : ℝ} (hα : -1 < α) {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    IntegrableOn (fun x : ℝ => (w * x) ^ n * (x : ℂ) ^ (α : ℂ) * exp (-(w * x))) (Set.Ioi 0) ∧
    (∫ x : ℝ in Set.Ioi 0, (w * x) ^ n * (x : ℂ) ^ (α : ℂ) * exp (-(w * x))) =
      w ^ (-((α : ℂ) + 1)) * Gamma ((α : ℂ) + n + 1) := by
  have hs : 0 < ((α : ℂ) + n + 1).re := by simp; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hw0 : w ≠ 0 := ne_zero_of_re_pos hw
  have he : ∀ x : ℝ, 0 < x → (w * x) ^ n * (x : ℂ) ^ (α : ℂ) * exp (-(w * x)) =
      w ^ n * ((x : ℂ) ^ (((α : ℂ) + n + 1) - 1) * exp (-(w * x))) := by
    intro x hx
    rw [mul_pow, add_sub_cancel_right, cpow_add _ _ (ofReal_ne_zero.mpr hx.ne'), cpow_natCast]
    ring
  have hi := (integrableOn_cpow_mul_cexp_neg hs hw).const_mul (w ^ n)
  refine ⟨hi.congr (ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => (he x hx).symm)), ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul,
    DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi hs hw]
  have hp : w ^ n * w ^ (-((α : ℂ) + n + 1)) = w ^ (-((α : ℂ) + 1)) := by
    rw [← cpow_natCast, ← cpow_add _ _ hw0]
    congr 1
    ring
  linear_combination Gamma ((α : ℂ) + n + 1) * hp

/-- A polynomial's scaled Laplace integral differs from its Gamma integral by one power. -/
theorem scaled_polynomial_moment {α : ℝ} (hα : -1 < α) {w : ℂ} (hw : 0 < w.re) (p : ℂ[X]) :
    IntegrableOn (fun x : ℝ => p.eval (w * x) * (x : ℂ) ^ (α : ℂ) * exp (-(w * x))) (Set.Ioi 0) ∧
    (∫ x : ℝ in Set.Ioi 0, p.eval (w * x) * (x : ℂ) ^ (α : ℂ) * exp (-(w * x))) =
      w ^ (-((α : ℂ) + 1)) *
      ∫ x : ℝ in Set.Ioi 0, p.eval (x : ℂ) * (x : ℂ) ^ (α : ℂ) * exp (-x) := by
  have hi1 : ∀ q : ℂ[X], IntegrableOn
      (fun x : ℝ => q.eval (x : ℂ) * (x : ℂ) ^ (α : ℂ) * exp (-x)) (Set.Ioi 0) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq =>
      convert hp.add hq using 1
      ext x
      simp only [Pi.add_apply, eval_add]
      ring
    | monomial n c =>
      simpa only [IntegrableOn, eval_monomial, mul_assoc] using ((laguerrePolyL_weight_moment hα n).1.const_mul c)
  -- Mathlib's monomial induction reduces complex scaling to the Gamma moments.
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    refine ⟨?_, ?_⟩
    · convert hp.1.add hq.1 using 1
      ext x
      simp only [Pi.add_apply, eval_add]
      ring
    · simp only [eval_add, add_mul]
      rw [integral_add hp.1 hq.1, integral_add (hi1 p) (hi1 q), hp.2, hq.2]
      ring
  | monomial n c =>
    refine ⟨by simpa only [IntegrableOn, eval_monomial, mul_assoc] using (scaled_monomial_moment hα hw n).1.const_mul c, ?_⟩
    simp only [eval_monomial, mul_assoc]
    rw [integral_const_mul, integral_const_mul]
    have h1 := (scaled_monomial_moment hα hw n).2
    have h2 := (laguerrePolyL_weight_moment hα n).2
    simp only [mul_assoc] at h1 h2
    rw [h1, h2]
    ring

/-- The finite Laguerre expansion is a complex polynomial. -/
theorem laguerre_exists_poly (α : ℂ) (n : ℕ) :
    ∃ p : ℂ[X], ∀ x, p.eval x = laguerrePolyL α n x := by
  refine ⟨∑ j ∈ Finset.range (n + 1), monomial j
    (poch (α + 1) n / n.factorial * kummerMCoeff (-(n : ℂ)) (α + 1) j), ?_⟩
  intro x
  simp [eval_finsetSum, laguerrePolyL_eq_sum_coeff]

/-- Scaled Laguerre orthogonality for a complex Laplace rate. -/
theorem scaled_laguerre_inner {α : ℝ} (hα : -1 < α) {w : ℂ} (hw : 0 < w.re) (m n : ℕ) :
    IntegrableOn (fun x : ℝ => laguerrePolyL α m (w * x) * laguerrePolyL α n (w * x) *
      (x : ℂ) ^ (α : ℂ) * exp (-(w * x))) (Set.Ioi 0) ∧
    (∫ x : ℝ in Set.Ioi 0, laguerrePolyL α m (w * x) * laguerrePolyL α n (w * x) *
      (x : ℂ) ^ (α : ℂ) * exp (-(w * x))) =
      if m = n then w ^ (-((α : ℂ) + 1)) * Gamma (n + (α : ℂ) + 1) / n ! else 0 := by
  obtain ⟨p, hp⟩ := laguerre_exists_poly α m
  obtain ⟨q, hq⟩ := laguerre_exists_poly α n
  have h := scaled_polynomial_moment hα hw (p * q)
  simp only [eval_mul, hp, hq] at h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  split_ifs with he
  · subst m
    have hn := laguerrePolyL_norm hα n
    have heq : (∫ x : ℝ in Set.Ioi 0, laguerrePolyL α n x * laguerrePolyL α n x *
        (x : ℂ) ^ (α : ℂ) * exp (-x)) = Gamma (n + (α : ℂ) + 1) / n ! := by
      convert hn using 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring
    rw [heq]; ring
  · rw [laguerrePolyL_orthogonal hα he, mul_zero]

/-- Finite change-of-scale coefficient for the Laguerre basis. -/
def laguerreScaleCoeff (α w : ℂ) (n k : ℕ) : ℂ :=
  laguerrePolyL α n 0 * (n.choose k : ℂ) * (w⁻¹) ^ k * (1 - w⁻¹) ^ (n - k) /
    laguerrePolyL α k 0

/-- Expansion in the Laguerre basis evaluated at a scaled argument. -/
theorem laguerre_scale_sum {α w : ℂ} (hα : -1 < α.re) (hw : w ≠ 0) (n : ℕ) (x : ℂ) :
    laguerrePolyL α n x = ∑ k ∈ Finset.range (n + 1),
      laguerreScaleCoeff α w n k * laguerrePolyL α k (w * x) := by
  have he : laguerrePolyL α n 0 ≠ 0 := by
    rw [laguerrePolyL_at_zero]
    exact div_ne_zero (poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) n)
      (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  have h := laguerrePolyL_multiplication hα w⁻¹ (w * x) n
  rw [inv_mul_cancel_left₀ hw] at h
  rw [div_eq_iff he] at h
  rw [h, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  simp only [laguerreScaleCoeff]
  ring

/-- Orthogonality contracts the two finite change-of-scale expansions. -/
theorem laguerre_product_contraction {α : ℝ} (hα : -1 < α) {w : ℂ} (hw : 0 < w.re) (m n : ℕ) :
    (∫ x : ℝ in Set.Ioi 0, laguerrePolyL α m x * laguerrePolyL α n x *
      (x : ℂ) ^ (α : ℂ) * exp (-(w * x))) =
      ∑ k ∈ Finset.range (m + 1), laguerreScaleCoeff α w m k * laguerreScaleCoeff α w n k *
        (w ^ (-((α : ℂ) + 1)) * Gamma (k + (α : ℂ) + 1) / k !) := by
  have hw0 := ne_zero_of_re_pos hw
  have heq : (fun x : ℝ => laguerrePolyL α m x * laguerrePolyL α n x *
      (x : ℂ) ^ (α : ℂ) * exp (-(w * x))) = fun x : ℝ =>
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        (laguerreScaleCoeff α w m i * laguerreScaleCoeff α w n j) *
        (laguerrePolyL α i (w * x) * laguerrePolyL α j (w * x) *
          (x : ℂ) ^ (α : ℂ) * exp (-(w * x))) := by
    funext x
    conv_lhs => arg 1; arg 1; arg 1; rw [laguerre_scale_sum (by simpa using hα) hw0 m]
    conv_lhs => arg 1; arg 1; arg 2; rw [laguerre_scale_sum (by simpa using hα) hw0 n]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (scaled_laguerre_inner hα hw i j).1.const_mul _]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ fun j _ => (scaled_laguerre_inner hα hw i j).1.const_mul _]
  simp only [integral_const_mul]
  simp_rw [(scaled_laguerre_inner hα hw i _).2]
  by_cases hi : i ∈ Finset.range (n + 1)
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      rw [ite_eq_right (Ne.symm hji), mul_zero]
    · exact fun h => (h hi).elim
  · have hn : n < i := by simpa using hi
    have hc : laguerreScaleCoeff α w n i = 0 := by
      simp [laguerreScaleCoeff, Nat.choose_eq_zero_of_lt hn]
    rw [hc, mul_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro j hj
    rw [ite_eq_right (by intro h; subst j; exact hi hj), mul_zero]

/-- Terminating Gauss coefficients in binomial form. -/
theorem gauss_neg_nat_choose (m n k : ℕ) (a : ℂ) :
    gaussHGCoeff (-(m : ℂ)) (-(n : ℂ)) a k =
      (m.choose k : ℂ) * (n.choose k : ℂ) * k ! / poch a k := by
  simp only [gaussHGCoeff, poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul]
  have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hs : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  by_cases hp : poch a k = 0
  · simp [hp]
  · field_simp
    ring_nf at hs ⊢
    rw [hs]
    ring

/-- The elementary power cancellation in a Laguerre change of scale. -/
theorem laguerre_scale_power {z : ℂ} (hz : z ≠ 0) (hw : z + 1 ≠ 0) {n k : ℕ} (hk : k ≤ n) :
    ((z + 1)⁻¹) ^ k * (1 - (z + 1)⁻¹) ^ (n - k) =
      z ^ n / (z + 1) ^ n / z ^ k := by
  have he : 1 - (z + 1)⁻¹ = z / (z + 1) := by field_simp; ring
  rw [he, div_pow, pow_sub₀ z hz hk, pow_sub₀ (z + 1) hw hk, inv_pow]
  field_simp

/-- The diagonal contraction has exactly the terminating Gauss coefficients. -/
theorem laguerre_product_contraction_term {α : ℝ} (hα : -1 < α) {z : ℂ}
    (hz : z ≠ 0) (hw : z + 1 ≠ 0) {m n k : ℕ} (hk : k ≤ m) :
    laguerreScaleCoeff α (z + 1) m k * laguerreScaleCoeff α (z + 1) n k *
      ((z + 1) ^ (-((α : ℂ) + 1)) * Gamma (k + (α : ℂ) + 1) / k !) =
    (Gamma (α + m + 1 : ℂ) * Gamma (α + n + 1 : ℂ) /
      (Gamma (α + 1 : ℂ) * m ! * n !) * z ^ (m + n) /
      (z + 1) ^ (α + m + n + 1 : ℂ)) *
      (gaussHGCoeff (-(m : ℂ)) (-(n : ℂ)) (α + 1) k * (z⁻¹ ^ 2) ^ k) := by
  by_cases hkn : k ≤ n
  · have hA : 0 < ((α : ℂ) + 1).re := by simp; linarith
    have hP (j : ℕ) : poch ((α : ℂ) + 1) j ≠ 0 :=
      poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos hA) j
    have hG := Gamma_ne_zero_of_re_pos hA
    have hF (j : ℕ) : (j ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
    have hgamma (j : ℕ) : Gamma ((α : ℂ) + j + 1) = poch ((α : ℂ) + 1) j * Gamma ((α : ℂ) + 1) := by
      rw [show (α : ℂ) + j + 1 = ((α : ℂ) + 1) + j by ring]
      exact Gamma_add_nat_eq_poch_mul_Gamma hA j
    have hgk : Gamma (k + (α : ℂ) + 1) = poch ((α : ℂ) + 1) k * Gamma ((α : ℂ) + 1) := by
      rw [add_comm (k : ℂ) (α : ℂ)]; exact hgamma k
    have hwP : (z + 1) ^ ((α : ℂ) + 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hw)
    have he : (z + 1) ^ (α + m + n + 1 : ℂ) =
        (z + 1) ^ ((α : ℂ) + 1) * (z + 1) ^ m * (z + 1) ^ n := by
      rw [show (α : ℂ) + m + n + 1 = (((α : ℂ) + 1) + m) + n by ring,
        cpow_add _ _ hw, cpow_add _ _ hw, cpow_natCast, cpow_natCast]
    have hd (j : ℕ) (hkj : k ≤ j) : laguerreScaleCoeff α (z + 1) j k =
        (poch ((α : ℂ) + 1) j / j !) * (j.choose k : ℂ) *
          (z ^ j / (z + 1) ^ j / z ^ k) / (poch ((α : ℂ) + 1) k / k !) := by
      unfold laguerreScaleCoeff
      rw [laguerrePolyL_at_zero, laguerrePolyL_at_zero]
      rw [show (poch ((α : ℂ) + 1) j / j ! * (j.choose k : ℂ) * ((z + 1)⁻¹) ^ k *
          (1 - (z + 1)⁻¹) ^ (j - k)) =
          (poch ((α : ℂ) + 1) j / j ! * (j.choose k : ℂ)) *
          (((z + 1)⁻¹) ^ k * (1 - (z + 1)⁻¹) ^ (j - k)) by ring,
        laguerre_scale_power hz hw hkj]
    rw [hd m hk, hd n hkn, hgk, hgamma m, hgamma n, he, gauss_neg_nat_choose,
      cpow_neg, pow_add, ← pow_mul, mul_comm 2 k, pow_mul, inv_pow]
    field_simp

  · have hnk : n < k := by omega
    rw [gauss_neg_nat_choose, Nat.choose_eq_zero_of_lt hnk]
    simp [laguerreScaleCoeff, Nat.choose_eq_zero_of_lt hnk]

@[dlmf 18.17.E34_5]
theorem laguerrePolyL_product_laplace_transform {α : ℝ} (hα : -1 < α) (m n : ℕ) {z : ℂ}
    (hz : -1 < z.re) (hz0 : z ≠ 0) :
    ∫ x : ℝ in Set.Ioi 0,
        exp (-x * z) * laguerrePolyL α m x * laguerrePolyL α n x * exp (-x) * (x : ℂ) ^ (α : ℂ) =
      Gamma (α + m + 1 : ℂ) * Gamma (α + n + 1 : ℂ) /
      (Gamma (α + 1 : ℂ) * m.factorial * n.factorial) * z ^ (m + n) /
      (z + 1) ^ (α + m + n + 1 : ℂ) * ₂F₁ (-(m : ℂ)) (-(n : ℂ)) (α + 1 : ℂ) (z⁻¹ ^ 2) := by
  have hw : 0 < (z + 1).re := by simp; linarith
  have heq : (∫ x : ℝ in Set.Ioi 0,
        exp (-x * z) * laguerrePolyL α m x * laguerrePolyL α n x * exp (-x) * (x : ℂ) ^ (α : ℂ)) =
      ∫ x : ℝ in Set.Ioi 0, laguerrePolyL α m x * laguerrePolyL α n x *
        (x : ℂ) ^ (α : ℂ) * exp (-((z + 1) * x)) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [show -((z + 1) * (x : ℂ)) = -x * z + -x by ring, exp_add]
      ring
  rw [heq, laguerre_product_contraction hα hw,
    ordinaryHypergeometric_eq_sum_neg_nat, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact laguerre_product_contraction_term hα hz0 (ne_zero_of_re_pos hw)
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

end LaguerreProductLaplace

/-- Corrected finite-sum form of DLMF 18.17.41 (checked 2026-09-16).
The displayed DLMF formula is incorrect: at `n = 0` its power `a^(-n-2)`
would give `Γ(z)/a²`, whereas the integral is `Γ(z)/a^z`.
The terminating ₂F₂ denominator parameters also require a shift: they should be
`(1-z-n)/2` and `(2-z-n)/2`. This sum avoids their removable singularities. -/
@[dlmf 18.17.E41]
theorem hermite_mellin_laplace_transform {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-a * x) * (aeval (x : ℂ) (hermite n) : ℂ) * (x : ℂ) ^ (z - 1) =
      ∑ k ∈ Finset.range (n / 2 + 1), (-1 : ℂ) ^ k * n.factorial /
        (2 ^ k * (k.factorial : ℂ) * (n - 2 * k).factorial) *
        Gamma (z + (n - 2 * k : ℕ)) / (a : ℂ) ^ (z + (n - 2 * k : ℕ)) := by
  simp_rw [hermite_finite_sum]
  exact integral_finite_sum_mellin_laplace ha hz _ _ (fun k => n - 2 * k)



section DoubleLaplaceIntegrals

open Set

set_option maxHeartbeats 1000000

/-- Homogenized symmetric Jacobi coefficients from the binomial formula. -/
def angularJacobiSum (β : ℂ) (n : ℕ) (x y : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), poch (β + n - k + 1) k / k ! *
    (poch (β + k + 1) (n - k) / (n - k) !) * (-y ^ 2) ^ (n - k) * (x ^ 2) ^ k

/-- A normalized Gegenbauer polynomial is the corresponding normalized symmetric Jacobi polynomial. -/
theorem gegenbauer_normalized_jacobi {β : ℝ} (hβ : -1 / 2 < β) (n : ℕ) (z : ℂ) :
    ultrasphPoly (β + 1 / 2) n z / ultrasphPoly (β + 1 / 2) n 1 =
      jacobiPolyP β β n z / jacobiPolyP β β n 1 := by
  have hb : -1 < (β : ℂ).re := by simp; linarith
  have hp : poch ((β : ℂ) + 1) n ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) n
  have hq : poch (2 * ((β : ℂ) + 1 / 2)) n ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) n
  rw [ultrasphPoly_eq_jacobiPolyP n z (by convert hp using 1 ; congr 1 ; ring),
    ultrasphPoly_eq_jacobiPolyP n 1 (by convert hp using 1 ; congr 1 ; ring)]
  simp only [show (β : ℂ) + 1 / 2 - 1 / 2 = β by ring]
  have hp' : poch ((β : ℂ) + 1 / 2 + 1 / 2) n ≠ 0 := by convert hp using 1 ; congr 1 ; ring
  exact mul_div_mul_left _ _ (div_ne_zero hq hp')

/-- Homogenization of the finite Jacobi binomial sum. -/
theorem angularJacobiSum_eq {β : ℝ} (hβ : -1 / 2 < β) (n : ℕ) {x y : ℝ}
    (hs : 0 < x ^ 2 + y ^ 2) :
    (x ^ 2 + y ^ 2 : ℂ) ^ n * jacobiPolyP β β n ((x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) : ℂ) =
      angularJacobiSum β n x y := by
  have hs0 : (x ^ 2 + y ^ 2 : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [jacobi_binomial_sum (by simp; linarith), angularJacobiSum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have h1 : (x ^ 2 - y ^ 2 : ℂ) / (x ^ 2 + y ^ 2) - 1 = 2 * (-((y : ℂ) ^ 2)) / (x ^ 2 + y ^ 2) := by
    field_simp; ring
  have h2 : (x ^ 2 - y ^ 2 : ℂ) / (x ^ 2 + y ^ 2) + 1 = 2 * (x : ℂ) ^ 2 / (x ^ 2 + y ^ 2) := by
    field_simp; ring
  rw [h1, h2, div_pow, div_pow, mul_pow, mul_pow]
  have hpow : (2 : ℂ) ^ (n - k) * 2 ^ k = 2 ^ n := by rw [← pow_add, Nat.sub_add_cancel hk']
  have hspow : (x ^ 2 + y ^ 2 : ℂ) ^ (n - k) * (x ^ 2 + y ^ 2) ^ k = (x ^ 2 + y ^ 2 : ℂ) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))]
  linear_combination (poch ((β : ℂ) + n - k + 1) k * poch ((β : ℂ) + k + 1) (n - k) *
    (-((y : ℂ) ^ 2)) ^ (n - k) * ((x : ℂ) ^ 2) ^ k) *
    ((x ^ 2 + y ^ 2 : ℂ) ^ n * hpow - (2 : ℂ) ^ n * hspow)

/-- The angular weight is integrable, including the allowed singular endpoint exponents. -/
theorem angular_weight_integrable {β : ℝ} (hβ : -1 / 2 < β) :
    IntervalIntegrable (fun phi : ℝ => (Real.sin phi : ℂ) ^ (2 * β : ℂ)) volume 0 Real.pi := by
  have h := (integral_sin_rpow_aux (lam := β + 1 / 2) (by linarith)).1
  have hc : IntervalIntegrable (fun phi : ℝ => ((Real.sin phi ^ (2 * β) : ℝ) : ℂ)) volume 0 Real.pi := by
    have hh : IntervalIntegrable (fun phi : ℝ => Real.sin phi ^ (2 * β)) volume 0 Real.pi := by
      convert h using 1  ; ring
    exact ⟨hh.1.ofReal, hh.2.ofReal⟩
  apply hc.congr_uIoo
  intro phi hphi
  dsimp only
  rw [Set.uIoo_of_lt Real.pi_pos] at hphi
  rw [show (2 * (β : ℂ)) = ((2 * β : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_cpow (Real.sin_pos_of_pos_of_lt_pi hphi.1 hphi.2).le]

/-- Homogeneous angular Laplace integral, reduced to a finite symmetric Jacobi sum. -/
theorem angular_homogeneous {β : ℝ} (hβ : -1 / 2 < β) (n : ℕ) {x y : ℝ}
    (hs : 0 < x ^ 2 + y ^ 2) :
    (∫ phi : ℝ in (0 : ℝ)..Real.pi,
      ((x : ℂ) ^ 2 - y ^ 2 + 2 * I * x * y * Real.cos phi) ^ n *
        (Real.sin phi : ℂ) ^ (2 * β : ℂ)) =
      (Real.sqrt Real.pi * Gamma (β + 1 / 2 : ℂ) * n ! / Gamma (β + n + 1 : ℂ)) *
        angularJacobiSum β n x y := by
  let q : ℂ := (x + y * I) ^ 2
  have hqnorm : ‖q‖ = x ^ 2 + y ^ 2 := by
    simp only [q, norm_pow, Complex.sq_norm, Complex.normSq_add_mul_I]
  have hq : q ≠ 0 := norm_ne_zero_iff.mp (by rw [hqnorm]; exact hs.ne')
  have hc : Real.cos q.arg = (x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) := by
    rw [Complex.cos_arg hq, hqnorm]
    simp [q, pow_two]
  have hsin : Real.sin q.arg = 2 * x * y / (x ^ 2 + y ^ 2) := by
    rw [Complex.sin_arg, hqnorm]
    simp [q, pow_two] ; ring
  have hs0 : (x ^ 2 + y ^ 2 : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hβC : -1 < (β : ℂ).re := by simp; linarith
  have hG0 : Gamma (β + 1 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hG1 : Gamma (β + 1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hP : poch ((β : ℂ) + 1) n ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) n
  have hF : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hG : Gamma (β + n + 1 : ℂ) = poch ((β : ℂ) + 1) n * Gamma (β + 1 : ℂ) := by
    rw [show (β : ℂ) + n + 1 = ((β : ℂ) + 1) + n by ring]
    exact Gamma_add_nat_eq_poch_mul_Gamma (by simp; linarith) n
  have hL := ultrasphPoly_laplace_integral (lam := β + 1 / 2) (by linarith) n q.arg
  rw [show ((β + 1 / 2 : ℝ) : ℂ) = (β : ℂ) + 1 / 2 by push_cast; ring,
    gegenbauer_normalized_jacobi hβ] at hL
  have hpow : ∀ phi : ℝ,
      ((x : ℂ) ^ 2 - y ^ 2 + 2 * I * x * y * Real.cos phi) ^ n =
      (x ^ 2 + y ^ 2 : ℂ) ^ n *
        (Real.cos q.arg + I * Real.sin q.arg * Real.cos phi : ℂ) ^ n := by
    intro phi
    rw [← mul_pow, hc, hsin]
    push_cast
    congr 1
    field_simp
  have hW : ∀ phi ∈ Set.uIcc (0 : ℝ) Real.pi,
      (Real.sin phi : ℂ) ^ (2 * β : ℂ) =
        ((Real.sin phi ^ (2 * (β + 1 / 2) - 1) : ℝ) : ℂ) := by
    intro phi hphi
    rw [Set.uIcc_of_le Real.pi_pos.le] at hphi
    rw [show (2 * (β : ℂ)) = ((2 * β : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow (Real.sin_nonneg_of_mem_Icc hphi)]
    congr 2
    ring
  have hI : (∫ phi : ℝ in (0 : ℝ)..Real.pi,
      ((x : ℂ) ^ 2 - y ^ 2 + 2 * I * x * y * Real.cos phi) ^ n *
        (Real.sin phi : ℂ) ^ (2 * β : ℂ)) =
      (x ^ 2 + y ^ 2 : ℂ) ^ n * ∫ phi : ℝ in (0 : ℝ)..Real.pi,
      (Real.cos q.arg + I * Real.sin q.arg * Real.cos phi : ℂ) ^ n *
        ((Real.sin phi ^ (2 * (β + 1 / 2) - 1) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro phi hphi
    dsimp only
    rw [hpow, hW phi hphi]
    ring
  rw [hI]
  have hscaled := angularJacobiSum_eq hβ n hs
  have harg : ((Real.cos q.arg : ℝ) : ℂ) = (x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) := by rw [hc]; push_cast; rfl
  conv_lhs at hL => rw [harg, jacobi_at_one hβC]
  have hGammaArgs : (β + 1 / 2 + 1 / 2 : ℂ) = β + 1 := by ring
  rw [show (β : ℂ) + 1 / 2 + 1 / 2 = β + 1 by ring] at hL
  rw [hG]
  let J : ℂ := ∫ phi : ℝ in (0 : ℝ)..Real.pi,
    (Real.cos q.arg + I * Real.sin q.arg * Real.cos phi : ℂ) ^ n *
      ((Real.sin phi ^ (2 * (β + 1 / 2) - 1) : ℝ) : ℂ)
  change _ = _ * J at hL
  change (x ^ 2 + y ^ 2 : ℂ) ^ n * J = _
  rw [div_div_eq_mul_div, div_mul_eq_mul_div] at hL
  have hLcross := (div_eq_div_iff hP (mul_ne_zero hπ hG1)).mp hL
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (mul_ne_zero hP hG0)).mpr
  linear_combination (Real.sqrt Real.pi * Gamma (β + 1 / 2 : ℂ) * (n ! : ℂ)) * hscaled -
    ((x ^ 2 + y ^ 2 : ℂ) ^ n) * hLcross

/-- Gaussian radial moments, including integrability at zero. -/
theorem gaussian_radial_moment {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun r : ℝ => exp (-(r : ℂ) ^ 2) * (r : ℂ) ^ (2 * s - 1 : ℂ)) (Ioi 0) ∧
    (∫ r : ℝ in Ioi 0, exp (-(r : ℂ) ^ 2) * (r : ℂ) ^ (2 * s - 1 : ℂ)) =
      (1 / 2) * Gamma (s : ℂ) := by
  have hi : IntegrableOn (fun r : ℝ => r ^ (2 * s - 1) * Real.exp (-r ^ 2)) (Ioi 0) := by
    simpa only [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, neg_mul, one_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 2) (s := 2 * s - 1) (b := 1)
        (by linarith) (by norm_num) (by norm_num))
  have he : ∀ r : ℝ, 0 < r → exp (-(r : ℂ) ^ 2) * (r : ℂ) ^ (2 * s - 1 : ℂ) =
      ((r ^ (2 * s - 1) * Real.exp (-r ^ 2) : ℝ) : ℂ) := by
    intro r hr
    rw [show (2 * (s : ℂ) - 1) = ((2 * s - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hr.le]
    push_cast
    ring
  refine ⟨(hi.ofReal).congr (ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => (he r hr).symm)), ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_complex_ofReal]
  -- Mathlib's real Gaussian moment theorem fixes the radial Gamma normalization.
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2 * s - 1) (b := 1)
    (by norm_num) (by linarith) (by norm_num)
  simp only [neg_mul, one_mul, Real.one_rpow,
    show (2 * s - 1 + 1) / 2 = s by ring] at h
  have hr : (∫ x : ℝ in Ioi 0, x ^ (2 * s - 1) * Real.exp (-x ^ 2)) = (1 / 2) * Real.Gamma s := by
    convert h using 1
    congr 1
    funext x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hr, Complex.Gamma_ofReal]
  push_cast
  ring

/-- The square map takes the open unit interval bijectively to itself. -/
theorem square_image_Ioo : (fun r : ℝ => r ^ 2) '' Ioo 0 1 = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨sq_pos_of_pos hr.1, by nlinarith [hr.1, hr.2]⟩
  · intro hx
    exact ⟨Real.sqrt x, ⟨Real.sqrt_pos.mpr hx.1, (Real.sqrt_lt' zero_lt_one).mpr (by simpa using hx.2)⟩,
      Real.sq_sqrt hx.1.le⟩

/-- Beta radial moments after the square substitution; endpoint singularities are retained. -/
theorem beta_radial_moment {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun r : ℝ => (r : ℂ) ^ (2 * a - 1 : ℂ) * (1 - (r : ℂ) ^ 2) ^ (b - 1 : ℂ)) volume 0 1 ∧
    (∫ r : ℝ in (0 : ℝ)..1, (r : ℂ) ^ (2 * a - 1 : ℂ) * (1 - (r : ℂ) ^ 2) ^ (b - 1 : ℂ)) =
      (1 / 2) * (Gamma (a : ℂ) * Gamma (b : ℂ) / Gamma (a + b : ℂ)) := by
  let f : ℝ → ℂ := fun u => (u : ℂ) ^ (a - 1 : ℂ) * (1 - (u : ℂ)) ^ (b - 1 : ℂ)
  have hf : IntegrableOn f (Ioo 0 1) := by
    exact ((betaIntegral_convergent (by simpa using ha) (by simpa using hb)).1).mono_set Ioo_subset_Ioc_self
  have hd : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (fun r : ℝ => r ^ 2) (2 * r) (Ioo 0 1) r := by
    intro r _
    simpa only [Nat.reduceSub, pow_one, mul_one, Nat.cast_ofNat] using
      (hasDerivAt_pow 2 r).hasDerivWithinAt (s := Ioo 0 1)
  have hinj : InjOn (fun r : ℝ => r ^ 2) (Ioo 0 1) := by
    intro r hr t ht hrt
    nlinarith [hr.1, ht.1]
  have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hd hinj f)
  rw [square_image_Ioo] at hi
  have ht : ∀ r ∈ Ioo (0 : ℝ) 1, |2 * r| • f (r ^ 2) =
      2 * ((r : ℂ) ^ (2 * a - 1 : ℂ) * (1 - (r : ℂ) ^ 2) ^ (b - 1 : ℂ)) := by
    intro r hr
    rw [abs_of_pos (by linarith [hr.1]), Complex.real_smul]
    dsimp only [f]
    push_cast
    have hsq : ((r : ℂ) ^ 2) ^ ((a : ℂ) - 1) = (r : ℂ) ^ (2 * ((a : ℂ) - 1)) := by
      rw [← Complex.ofReal_pow, ← Real.rpow_natCast]
      exact (Complex.cpow_mul_ofReal_nonneg hr.1.le 2 ((a : ℂ) - 1)).symm
    rw [hsq]
    rw [show (2 : ℂ) * ((a : ℂ) - 1) = (2 * (a : ℂ) - 1) - 1 by ring,
      cpow_sub _ _ (ofReal_ne_zero.mpr hr.1.ne'), cpow_one]
    field_simp [ofReal_ne_zero.mpr hr.1.ne']
  have hif : IntegrableOn (fun r : ℝ => (r : ℂ) ^ (2 * a - 1 : ℂ) *
      (1 - (r : ℂ) ^ 2) ^ (b - 1 : ℂ)) (Ioo 0 1) := by
    have htwo := (hi.mp hf).congr_fun ht measurableSet_Ioo
    have hh := htwo.const_mul (1 / 2 : ℂ)
    exact hh.congr (Filter.Eventually.of_forall fun r => by dsimp only; ring)
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hif, ?_⟩
  -- Mathlib's Jacobian formula also applies to these integrable endpoint singularities.
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj f
  rw [square_image_Ioo, setIntegral_congr_fun measurableSet_Ioo ht, integral_const_mul] at hchange
  have hbval : (∫ u : ℝ in Ioo 0 1, f u) = Gamma (a : ℂ) * Gamma (b : ℂ) / Gamma (a + b : ℂ) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    have hgab : Gamma (a + b : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    apply (eq_div_iff hgab).mpr
    change betaIntegral (a : ℂ) (b : ℂ) * Gamma (a + b : ℂ) = _
    rw [mul_comm]
    exact (Gamma_mul_Gamma_eq_betaIntegral (s := (a : ℂ)) (t := (b : ℂ)) (by simpa using ha) (by simpa using hb)).symm
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rw [hbval] at hchange
  linear_combination -(1 / 2 : ℂ) * hchange


/-- Gamma-normalized finite Jacobi expansion at a real angle. -/
theorem jacobi_half_angle_normalized {α β : ℝ} (hα : -1 < α) (n : ℕ) (θ : ℝ) :
    jacobiPolyP α β n (Real.cos θ) / jacobiPolyP α β n 1 =
      Gamma (α + 1 : ℂ) * n ! * ∑ k ∈ Finset.range (n + 1),
        poch ((β : ℂ) + k + 1) (n - k) /
          ((k ! : ℂ) * (n - k) ! * Gamma (α + (n - k : ℕ) + 1 : ℂ)) *
        (-((Real.sin (θ / 2) : ℂ) ^ 2)) ^ (n - k) * ((Real.cos (θ / 2) : ℂ) ^ 2) ^ k := by
  have hm : (Real.cos θ : ℂ) - 1 = 2 * (-((Real.sin (θ / 2) : ℂ) ^ 2)) := by
    have h := Real.cos_two_mul (θ / 2)
    have hcs := Real.cos_sq_add_sin_sq (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    exact_mod_cast (by nlinarith : Real.cos θ - 1 = 2 * (-(Real.sin (θ / 2) ^ 2)))
  have hp : (Real.cos θ : ℂ) + 1 = 2 * ((Real.cos (θ / 2) : ℂ) ^ 2) := by
    have h := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    exact_mod_cast (by linarith : Real.cos θ + 1 = 2 * Real.cos (θ / 2) ^ 2)
  have hP : poch ((α : ℂ) + 1) n ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; linarith)) n
  rw [jacobi_binomial_sum (by simpa using hα), jacobi_at_one (by simpa using hα)]
  simp only [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hA : 0 < ((α : ℂ) + (n - k : ℕ) + 1).re := by
    simp; linarith [Nat.cast_nonneg (α := ℝ) (n - k)]
  have hG : Gamma (α + (n - k : ℕ) + 1 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos hA
  have h0 : Gamma (α + n + 1 : ℂ) = poch ((α : ℂ) + 1) n * Gamma (α + 1 : ℂ) := by
    rw [show (α : ℂ) + n + 1 = ((α : ℂ) + 1) + n by ring]
    exact Gamma_add_nat_eq_poch_mul_Gamma (by simp; linarith) n
  have h1 : Gamma (α + n + 1 : ℂ) =
      poch ((α : ℂ) + n - k + 1) k * Gamma (α + (n - k : ℕ) + 1 : ℂ) := by
    have h := Gamma_add_nat_eq_poch_mul_Gamma hA k
    convert h using 1 <;> push_cast [Nat.cast_sub hk'] <;> congr 1 <;> ring
  have hratio : poch ((α : ℂ) + n - k + 1) k / poch ((α : ℂ) + 1) n =
      Gamma (α + 1 : ℂ) / Gamma (α + (n - k : ℕ) + 1 : ℂ) := by
    apply (div_eq_div_iff hP hG).mpr
    linear_combination h0 - h1
  have htwo : (2 : ℂ) ^ n = 2 ^ (n - k) * 2 ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  rw [hm, hp, mul_pow, mul_pow, htwo]
  calc
    _ = (poch ((β : ℂ) + k + 1) (n - k) / ((k ! : ℂ) * (n - k) !) * n ! *
        (-((Real.sin (θ / 2) : ℂ) ^ 2)) ^ (n - k) * ((Real.cos (θ / 2) : ℂ) ^ 2) ^ k) *
        (poch ((α : ℂ) + n - k + 1) k / poch ((α : ℂ) + 1) n) := by
      field_simp
    _ = _ := by rw [hratio]; ring

@[dlmf 18.10.E3]
theorem jacobi_double_laplace_integral {α β : ℝ} (hαβ : β < α) (hβ : -1 / 2 < β)
    (n : ℕ) (θ : ℝ) :
    jacobiPolyP α β n (Real.cos θ) / jacobiPolyP α β n 1 =
      2 * Gamma (α + 1 : ℂ) / (Real.sqrt Real.pi * Gamma (α - β : ℂ) * Gamma (β + 1 / 2 : ℂ)) *
      ∫ r : ℝ in (0 : ℝ)..1, ∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((Real.cos (θ / 2) : ℂ) ^ 2 - r ^ 2 * (Real.sin (θ / 2) : ℂ) ^ 2 +
          I * r * Real.sin θ * Real.cos phi) ^ n *
        (1 - r ^ 2 : ℂ) ^ (α - β - 1 : ℂ) * (r : ℂ) ^ (2 * β + 1 : ℂ) *
        (Real.sin phi : ℂ) ^ (2 * β : ℂ) := by
  let c : ℝ := Real.cos (θ / 2)
  let s : ℝ := Real.sin (θ / 2)
  let K : ℂ := Real.sqrt Real.pi * Gamma (β + 1 / 2 : ℂ) * n ! / Gamma (β + n + 1 : ℂ)
  let D : ℕ → ℂ := fun k => poch ((β : ℂ) + n - k + 1) k / k ! *
    (poch ((β : ℂ) + k + 1) (n - k) / (n - k) !) * (-((s : ℂ) ^ 2)) ^ (n - k) * ((c : ℂ) ^ 2) ^ k
  let F : ℕ → ℝ → ℂ := fun k r => (r : ℂ) ^ (2 * ((β : ℂ) + (n - k : ℕ) + 1) - 1) *
    (1 - (r : ℂ) ^ 2) ^ (α - β - 1 : ℂ)
  have hpos (k : ℕ) : 0 < β + (n - k : ℕ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) (n - k)
    linarith
  have hF (k : ℕ) : IntervalIntegrable (F k) volume 0 1 ∧
      (∫ r : ℝ in (0 : ℝ)..1, F k r) = (1 / 2) *
        (Gamma (β + (n - k : ℕ) + 1 : ℂ) * Gamma (α - β : ℂ) /
          Gamma (α + (n - k : ℕ) + 1 : ℂ)) := by
    have h := beta_radial_moment (hpos k) (sub_pos.mpr hαβ)
    dsimp only [F]
    convert h using 1 <;> push_cast <;> ring
  have hcs : c ^ 2 + s ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have hsin : Real.sin θ = 2 * s * c := by
    have h := Real.sin_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    exact h
  have hin (r : ℝ) (hr : r ∈ Set.Ioo 0 1) :
      (∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((c : ℂ) ^ 2 - r ^ 2 * (s : ℂ) ^ 2 + I * r * Real.sin θ * Real.cos phi) ^ n *
        (1 - r ^ 2 : ℂ) ^ (α - β - 1 : ℂ) * (r : ℂ) ^ (2 * β + 1 : ℂ) *
        (Real.sin phi : ℂ) ^ (2 * β : ℂ)) = K * ∑ k ∈ Finset.range (n + 1), D k * F k r := by
    have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.1.ne'
    have hnorm : 0 < c ^ 2 + (r * s) ^ 2 := by
      by_cases hc : c = 0
      · have hs : s ≠ 0 := by intro h; simp [hc, h] at hcs
        rw [hc, zero_pow (by norm_num), zero_add]
        exact sq_pos_of_ne_zero (mul_ne_zero hr.1.ne' hs)
      · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hc) (sq_nonneg _)
    have h := angular_homogeneous hβ n (x := c) (y := r * s) hnorm
    have heq : (∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((c : ℂ) ^ 2 - r ^ 2 * (s : ℂ) ^ 2 + I * r * Real.sin θ * Real.cos phi) ^ n *
        (1 - r ^ 2 : ℂ) ^ (α - β - 1 : ℂ) * (r : ℂ) ^ (2 * β + 1 : ℂ) *
        (Real.sin phi : ℂ) ^ (2 * β : ℂ)) =
      ((1 - r ^ 2 : ℂ) ^ (α - β - 1 : ℂ) * (r : ℂ) ^ (2 * β + 1 : ℂ)) *
      ∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((c : ℂ) ^ 2 - (r * s : ℝ) ^ 2 + 2 * I * c * ((r * s : ℝ) : ℂ) * Real.cos phi) ^ n *
          (Real.sin phi : ℂ) ^ (2 * β : ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro phi _
      dsimp only
      rw [hsin]
      push_cast
      have he : (c : ℂ) ^ 2 - r ^ 2 * (s : ℂ) ^ 2 + I * r * ((2 * s * c : ℝ) : ℂ) * Real.cos phi =
          (c : ℂ) ^ 2 - ((r * s : ℝ) : ℂ) ^ 2 + 2 * I * c * ((r * s : ℝ) : ℂ) * Real.cos phi := by
        push_cast
        ring
      push_cast at he
      rw [he]
      ring
    rw [heq, h]
    simp only [angularJacobiSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hp : (r : ℂ) ^ (2 * β + 1 : ℂ) * (r : ℂ) ^ (2 * (n - k)) =
        (r : ℂ) ^ (2 * ((β : ℂ) + (n - k : ℕ) + 1) - 1) := by
      rw [← cpow_natCast, ← cpow_add _ _ hr0]
      congr 1
      push_cast
      ring
    dsimp only [K, D, F]
    push_cast
    rw [mul_pow, neg_pow, mul_pow, ← pow_mul]
    linear_combination
      (Real.sqrt Real.pi * Gamma (β + 1 / 2 : ℂ) * n ! / Gamma (β + n + 1 : ℂ) *
        (poch ((β : ℂ) + n - k + 1) k / k !) *
        (poch ((β : ℂ) + k + 1) (n - k) / (n - k) !) * (-1) ^ (n - k) *
        ((s : ℂ) ^ 2) ^ (n - k) * ((c : ℂ) ^ 2) ^ k * (1 - (r : ℂ) ^ 2) ^ (α - β - 1 : ℂ)) * hp
  have houter : (∫ r : ℝ in (0 : ℝ)..1, ∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((c : ℂ) ^ 2 - r ^ 2 * (s : ℂ) ^ 2 + I * r * Real.sin θ * Real.cos phi) ^ n *
        (1 - r ^ 2 : ℂ) ^ (α - β - 1 : ℂ) * (r : ℂ) ^ (2 * β + 1 : ℂ) *
        (Real.sin phi : ℂ) ^ (2 * β : ℂ)) =
      K * ∑ k ∈ Finset.range (n + 1), D k *
        ((1 / 2) * (Gamma (β + (n - k : ℕ) + 1 : ℂ) * Gamma (α - β : ℂ) /
          Gamma (α + (n - k : ℕ) + 1 : ℂ))) := by
    have hfi (k : ℕ) : IntegrableOn (F k) (Set.Ioo 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp (hF k).1
    have hval (k : ℕ) : (∫ r : ℝ in Set.Ioo 0 1, F k r) = (1 / 2) *
        (Gamma (β + (n - k : ℕ) + 1 : ℂ) * Gamma (α - β : ℂ) /
          Gamma (α + (n - k : ℕ) + 1 : ℂ)) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
      exact (hF k).2
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo hin, integral_const_mul,
      integral_finsetSum _ fun k _ => (hfi k).const_mul _]
    simp only [integral_const_mul]
    simp_rw [hval]
  rw [show (Real.cos (θ / 2) : ℂ) = (c : ℂ) from rfl,
    show (Real.sin (θ / 2) : ℂ) = (s : ℂ) from rfl, houter,
    jacobi_half_angle_normalized (by linarith : -1 < α)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hA : 0 < ((β : ℂ) + (n - k : ℕ) + 1).re := by simpa using hpos k
  have hg : Gamma (β + n + 1 : ℂ) =
      poch ((β : ℂ) + n - k + 1) k * Gamma (β + (n - k : ℕ) + 1 : ℂ) := by
    have h := Gamma_add_nat_eq_poch_mul_Gamma hA k
    convert h using 1 <;> push_cast [Nat.cast_sub hk'] <;> congr 1 <;> ring
  have hG : Gamma (β + n + 1 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp; linarith [Nat.cast_nonneg (α := ℝ) n])
  have hGr : Gamma (α + (n - k : ℕ) + 1 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp; linarith [Nat.cast_nonneg (α := ℝ) (n - k)])
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hΓ : Gamma (β + 1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hΓ' : Gamma (((β : ℂ) * 2 + 1) / 2) ≠ 0 := by
    convert hΓ using 1 ; congr 1 ; ring
  have hΓab : Gamma (α - β : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hf (j : ℕ) : (j ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  dsimp only [K, D, c, s]
  field_simp [hf k, hf (n - k), hf n, hΓ, hΓ', hG, hGr, hΓab, hπ]
  linear_combination (Gamma (α + 1 : ℂ) * poch ((β : ℂ) + k + 1) (n - k) *
    (-((Real.sin (θ / 2) : ℂ) ^ 2)) ^ (n - k) * ((Real.cos (θ / 2) : ℂ) ^ 2) ^ k) * hg

@[dlmf 18.10.E6]
theorem laguerrePolyL_double_laplace_integral {α : ℝ} (hα : -1 / 2 < α) (n : ℕ) (x : ℝ) :
    laguerrePolyL α n ((x : ℂ) ^ 2) =
      2 * (-1 : ℂ) ^ n / (Real.sqrt Real.pi * Gamma (α + 1 / 2 : ℂ) * n.factorial) *
      ∫ r : ℝ in Set.Ioi 0, ∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((x : ℂ) ^ 2 - r ^ 2 + 2 * I * x * r * Real.cos phi) ^ n * exp (-(r : ℂ) ^ 2) *
        (r : ℂ) ^ (2 * α + 1 : ℂ) * (Real.sin phi : ℂ) ^ (2 * α : ℂ) := by
  let K : ℂ := Real.sqrt Real.pi * Gamma (α + 1 / 2 : ℂ) * n ! / Gamma (α + n + 1 : ℂ)
  let D : ℕ → ℂ := fun k => poch ((α : ℂ) + n - k + 1) k / k ! *
    (poch ((α : ℂ) + k + 1) (n - k) / (n - k) !) * (-1) ^ (n - k) * ((x : ℂ) ^ 2) ^ k
  let F : ℕ → ℝ → ℂ := fun k r => exp (-(r : ℂ) ^ 2) *
    (r : ℂ) ^ (2 * ((α : ℂ) + (n - k : ℕ) + 1) - 1)
  have hpos (k : ℕ) : 0 < α + (n - k : ℕ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) (n - k)
    linarith
  have hF (k : ℕ) : IntegrableOn (F k) (Set.Ioi 0) ∧
      (∫ r : ℝ in Set.Ioi 0, F k r) = (1 / 2) * Gamma (α + (n - k : ℕ) + 1 : ℂ) := by
    dsimp only [F]
    have h := gaussian_radial_moment (hpos k)
    push_cast at h
    exact h
  have hin (r : ℝ) (hr : 0 < r) :
      (∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((x : ℂ) ^ 2 - r ^ 2 + 2 * I * x * r * Real.cos phi) ^ n * exp (-(r : ℂ) ^ 2) *
        (r : ℂ) ^ (2 * α + 1 : ℂ) * (Real.sin phi : ℂ) ^ (2 * α : ℂ)) =
      K * ∑ k ∈ Finset.range (n + 1), D k * F k r := by
    have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
    have h := angular_homogeneous hα n (x := x) (y := r) (by nlinarith [sq_nonneg x])
    have heq : (∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((x : ℂ) ^ 2 - r ^ 2 + 2 * I * x * r * Real.cos phi) ^ n * exp (-(r : ℂ) ^ 2) *
        (r : ℂ) ^ (2 * α + 1 : ℂ) * (Real.sin phi : ℂ) ^ (2 * α : ℂ)) =
      (exp (-(r : ℂ) ^ 2) * (r : ℂ) ^ (2 * α + 1 : ℂ)) *
      ∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((x : ℂ) ^ 2 - r ^ 2 + 2 * I * x * r * Real.cos phi) ^ n *
          (Real.sin phi : ℂ) ^ (2 * α : ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro phi _
      dsimp only
      ring
    rw [heq, h]
    simp only [angularJacobiSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hp : (r : ℂ) ^ (2 * α + 1 : ℂ) * (r : ℂ) ^ (2 * (n - k)) =
        (r : ℂ) ^ (2 * ((α : ℂ) + (n - k : ℕ) + 1) - 1) := by
      rw [← cpow_natCast, ← cpow_add _ _ hr0]
      congr 1
      push_cast
      ring
    dsimp only [K, D, F]
    rw [neg_pow, ← pow_mul]
    linear_combination
      (Real.sqrt Real.pi * Gamma (α + 1 / 2 : ℂ) * n ! / Gamma (α + n + 1 : ℂ) *
        (poch ((α : ℂ) + n - k + 1) k / k !) *
        (poch ((α : ℂ) + k + 1) (n - k) / (n - k) !) * (-1) ^ (n - k) *
        ((x : ℂ) ^ 2) ^ k * exp (-(r : ℂ) ^ 2)) * hp
  rw [setIntegral_congr_fun measurableSet_Ioi hin, integral_const_mul,
    integral_finsetSum _ fun k _ => (hF k).1.const_mul _]
  simp only [integral_const_mul]
  simp_rw [(hF _).2]
  rw [laguerrePolyL_eq_sum (not_neg_nat_of_re_pos (by simp; linarith)), Finset.mul_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hA : 0 < ((α : ℂ) + (n - k : ℕ) + 1).re := by simpa using hpos k
  have hg : Gamma (α + n + 1 : ℂ) =
      poch ((α : ℂ) + n - k + 1) k * Gamma (α + (n - k : ℕ) + 1 : ℂ) := by
    have h := Gamma_add_nat_eq_poch_mul_Gamma hA k
    convert h using 1 <;> push_cast [Nat.cast_sub hk'] <;> congr 1 <;> ring
  have hG : Gamma (α + n + 1 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp; linarith [Nat.cast_nonneg (α := ℝ) n])
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hΓ : Gamma (α + 1 / 2 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hf (j : ℕ) : (j ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hsign : (-1 : ℂ) ^ n * (-1) ^ (n - k) = (-1) ^ k := by
    conv_lhs => arg 1; rw [show n = k + (n - k) by omega, pow_add]
    rw [mul_assoc, ← mul_pow]
    simp
  dsimp only [K, D]
  rw [neg_pow]
  rw [show (α : ℂ) + 1 + k = α + k + 1 by ring]
  have hΓ' : Gamma (((α : ℂ) * 2 + 1) / 2) ≠ 0 := by
    convert hΓ using 1 ; congr 1 ; ring
  field_simp [hf k, hf (n - k), hf n, hΓ, hΓ', hG, hπ]
  linear_combination (poch ((α : ℂ) + k + 1) (n - k) * ((x : ℂ) ^ 2) ^ k) *
    ((-1 : ℂ) ^ n * (-1) ^ (n - k) * hg - Gamma (α + n + 1 : ℂ) * hsign)

end DoubleLaplaceIntegrals

@[dlmf 18.10.E9]
theorem laguerrePolyL_bessel_integral {α : ℝ} (hα : -1 < α) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    laguerrePolyL α n x = exp (x : ℂ) * (x : ℂ) ^ (-α / 2 : ℂ) / n.factorial *
      ∫ t : ℝ in Set.Ioi 0, exp (-t : ℂ) * (t : ℂ) ^ (n + α / 2 : ℂ) *
        besselJ α (2 * Real.sqrt (x * t)) := by
  have hc : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := by
    intro k hk
    have h := congrArg Complex.re hk
    simp at h
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have ha : 0 < ((n : ℂ) + α + 1).re := by
    simp only [add_re, natCast_re, ofReal_re, one_re]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have h := regularized_bessel_integral (a := (n : ℂ) + α + 1) (b := (α : ℂ) + 1)
    (z := (x : ℂ)) ha (by simpa using hx)
  rw [regularizedConfluent_kummer_transform] at h
  rw [show ((α : ℂ) + 1) - ((n : ℂ) + α + 1) = -(n : ℂ) by ring,
    neg_neg, show (1 - ((α : ℂ) + 1)) / 2 = -(α : ℂ) / 2 by ring] at h
  have hi : (∫ t : ℝ in Set.Ioi 0,
      exp (-(t : ℂ)) * (t : ℂ) ^ ((n : ℂ) + α + 1 - ((α : ℂ) + 1) / 2 - 1 / 2) *
        besselJ ((α : ℂ) + 1 - 1) (2 * ((x : ℂ) * t) ^ (1 / 2 : ℂ))) =
      ∫ t : ℝ in Set.Ioi 0, exp (-t : ℂ) * (t : ℂ) ^ (n + α / 2 : ℂ) *
        besselJ α (2 * Real.sqrt (x * t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    have ht0 : 0 < t := ht
    have hs : (((x * t : ℝ) : ℂ) ^ (1 / 2 : ℂ)) = (Real.sqrt (x * t) : ℂ) := by
      rw [Real.sqrt_eq_rpow, ofReal_cpow (mul_nonneg hx.le ht0.le)]
      norm_num
    rw [show ((n : ℂ) + α + 1 - ((α : ℂ) + 1) / 2 - 1 / 2) = n + α / 2 by ring,
      show (α : ℂ) + 1 - 1 = α by ring, ← ofReal_mul, hs]
  rw [hi] at h
  rw [laguerrePolyL_eq_Gamma_mul_regularized hc]
  have hg : Gamma ((n : ℂ) + α + 1) ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have he : exp (x : ℂ) * exp (-(x : ℂ)) = 1 := by rw [← exp_add]; simp
  field_simp at h ⊢
  linear_combination (exp (x : ℂ)) * h -
    Gamma ((n : ℂ) + α + 1) * regularizedHGFun {-(n : ℂ)} {(α : ℂ) + 1} x * he

/-- For `g` even, the Fourier integral over `[-1, 1]` is twice the cosine integral over `[0, 1]`. -/
theorem integral_mul_exp_of_even {g : ℝ → ℂ} (hg : IntervalIntegrable g volume (-1) 1)
    (hev : ∀ x, g (-x) = g x) (y : ℝ) :
    ∫ x : ℝ in (-1 : ℝ)..1, g x * exp (I * x * y) =
      2 * ∫ x : ℝ in (0 : ℝ)..1, g x * Real.cos (x * y) := by
  have hs1 : Set.uIcc (-1 : ℝ) 0 ⊆ Set.uIcc (-1) 1 := by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc le_rfl (by norm_num)
  have hs2 : Set.uIcc (0 : ℝ) 1 ⊆ Set.uIcc (-1) 1 := by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc (by norm_num) le_rfl
  have h1 : IntervalIntegrable g volume (-1) 0 := hg.mono_set hs1
  have h2 : IntervalIntegrable g volume 0 1 := hg.mono_set hs2
  have hc {a b : ℝ} {f : ℝ → ℂ} (h : IntervalIntegrable g volume a b) (hf : Continuous f) :
      IntervalIntegrable (fun x => g x * f x) volume a b := h.mul_continuousOn hf.continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc h1 (by fun_prop)) (hc h2 (by fun_prop))]
  have hneg := intervalIntegral.integral_comp_neg (a := 0) (b := 1)
    (fun x : ℝ => g x * exp (I * x * y))
  norm_num only [neg_zero] at hneg
  simp only [hev, ofReal_neg] at hneg
  rw [← hneg, ← intervalIntegral.integral_add
    (hc (f := fun x : ℝ => exp (I * -(x : ℂ) * y)) h2 (by fun_prop))
    (hc (f := fun x : ℝ => exp (I * (x : ℂ) * y)) h2 (by fun_prop)),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  push_cast
  rw [show I * (-(x : ℂ)) * y = -(x * y) * I by ring, show I * (x : ℂ) * y = (x * y) * I by ring]
  linear_combination (-g x) * Complex.two_cos ((x : ℂ) * y)

/-- For `g` odd, the Fourier integral over `[-1, 1]` is `2i` times the sine integral over
`[0, 1]`. -/
theorem integral_mul_exp_of_odd {g : ℝ → ℂ} (hg : IntervalIntegrable g volume (-1) 1)
    (hodd : ∀ x, g (-x) = -g x) (y : ℝ) :
    ∫ x : ℝ in (-1 : ℝ)..1, g x * exp (I * x * y) =
      2 * I * ∫ x : ℝ in (0 : ℝ)..1, g x * Real.sin (x * y) := by
  have hs1 : Set.uIcc (-1 : ℝ) 0 ⊆ Set.uIcc (-1) 1 := by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc le_rfl (by norm_num)
  have hs2 : Set.uIcc (0 : ℝ) 1 ⊆ Set.uIcc (-1) 1 := by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc (by norm_num) le_rfl
  have h1 : IntervalIntegrable g volume (-1) 0 := hg.mono_set hs1
  have h2 : IntervalIntegrable g volume 0 1 := hg.mono_set hs2
  have hc {a b : ℝ} {f : ℝ → ℂ} (h : IntervalIntegrable g volume a b) (hf : Continuous f) :
      IntervalIntegrable (fun x => g x * f x) volume a b := h.mul_continuousOn hf.continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc h1 (by fun_prop)) (hc h2 (by fun_prop))]
  have hneg := intervalIntegral.integral_comp_neg (a := 0) (b := 1)
    (fun x : ℝ => g x * exp (I * x * y))
  norm_num only [neg_zero] at hneg
  simp only [hodd, ofReal_neg, neg_mul, ← mul_neg] at hneg
  rw [← hneg, ← intervalIntegral.integral_add
    (hc (f := fun x : ℝ => -exp (I * -(x : ℂ) * y)) h2 (by fun_prop))
    (hc (f := fun x : ℝ => exp (I * (x : ℂ) * y)) h2 (by fun_prop)),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  push_cast
  rw [show I * (-(x : ℂ)) * y = -(x * y) * I by ring, show I * (x : ℂ) * y = (x * y) * I by ring]
  linear_combination (-(g x * I)) * Complex.two_sin ((x : ℂ) * y) +
    (-(g x) * (exp (-(x * y) * I) - exp ((x * y) * I))) * I_sq

/-- The Gegenbauer weight times a continuous function is integrable on `[-1, 1]`. -/
theorem intervalIntegrable_ultrasph_weight_mul {lam : ℝ} (hlam : 0 < lam) (N : ℕ) :
    IntervalIntegrable (fun x : ℝ => (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam N x) volume (-1) 1 := by
  have hw := intervalIntegrable_jacobi_weight_cpow (a := (lam : ℂ) - 1 / 2)
    (b := (lam : ℂ) - 1 / 2) (by simp; linarith) (by simp; linarith)
  have hC : Continuous fun x : ℝ => ultrasphPoly lam N (x : ℂ) :=
    ((analyticOnNhd_ultrasphPoly (lam : ℂ) N).continuousOn.comp_continuous
      continuous_ofReal (fun _ => Set.mem_univ _))
  refine (hw.mul_continuousOn hC.continuousOn).congr fun x hx => ?_
  rw [Set.uIoc_of_le (by norm_num)] at hx
  have h1 : (1 - (x : ℂ) ^ 2) = ((1 - x : ℝ) : ℂ) * ((1 + x : ℝ) : ℂ) := by push_cast; ring
  rw [h1, mul_cpow_ofReal_nonneg (by linarith [hx.2]) (by linarith [hx.1])]
  push_cast; ring

@[dlmf 18.17.E17]
theorem ultrasphPoly_even_cosine_transform {lam : ℝ} (hlam : 0 < lam) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ in (0 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam (2 * n) x * Real.cos (x * y) =
      (-1 : ℂ) ^ n * Real.pi * Gamma (2 * n + 2 * lam : ℂ) * besselJ (lam + 2 * n) y /
        ((2 * n).factorial * Gamma (lam : ℂ) * (2 * y : ℂ) ^ (lam : ℂ)) := by
  have hev : ∀ x : ℝ, (1 - ((-x : ℝ) : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam (2 * n) ((-x : ℝ) : ℂ) =
      (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) * ultrasphPoly lam (2 * n) x := by
    intro x
    rw [ofReal_neg, ultrasphPoly_reflection (by simp; linarith), pow_mul]
    norm_num
  have h := integral_mul_exp_of_even (intervalIntegrable_ultrasph_weight_mul hlam (2 * n))
    hev y
  rw [ultrasphPoly_fourier_transform hlam (2 * n) hy] at h
  apply mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0)
  rw [← h, pow_mul, I_sq]
  push_cast
  rw [add_comm (lam : ℂ) (2 * n)]
  ring

@[dlmf 18.17.E18]
theorem ultrasphPoly_odd_sine_transform {lam : ℝ} (hlam : 0 < lam) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ in (0 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam (2 * n + 1) x * Real.sin (x * y) =
      (-1 : ℂ) ^ n * Real.pi * Gamma (2 * n + 2 * lam + 1 : ℂ) * besselJ (2 * n + lam + 1) y /
        ((2 * n + 1).factorial * Gamma (lam : ℂ) * (2 * y : ℂ) ^ (lam : ℂ)) := by
  have hodd : ∀ x : ℝ, (1 - ((-x : ℝ) : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam (2 * n + 1) ((-x : ℝ) : ℂ) =
      -((1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) * ultrasphPoly lam (2 * n + 1) x) := by
    intro x
    rw [ofReal_neg, ultrasphPoly_reflection (by simp; linarith),
      show ((-1 : ℂ)) ^ (2 * n + 1) = -1 by rw [pow_succ, pow_mul]; norm_num, neg_sq]
    ring
  have h := integral_mul_exp_of_odd (intervalIntegrable_ultrasph_weight_mul hlam (2 * n + 1))
    hodd y
  rw [ultrasphPoly_fourier_transform hlam (2 * n + 1) hy] at h
  apply mul_left_cancel₀ (mul_ne_zero two_ne_zero I_ne_zero : (2 : ℂ) * I ≠ 0)
  rw [← h, pow_succ, pow_mul, I_sq]
  push_cast
  rw [show (2 * n + 1 : ℂ) + lam = 2 * n + lam + 1 by ring,
    show (2 * n + 1 : ℂ) + 2 * lam = 2 * n + 2 * lam + 1 by ring]
  ring

@[dlmf 18.17.E19]
theorem legendre_fourier_transform (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ in (-1 : ℝ)..1, legendrePolyP n x * exp (I * x * y) =
      I ^ n * Real.sqrt (2 * Real.pi / y) * besselJ (n + 1 / 2 : ℂ) y := by
  have h := ultrasphPoly_fourier_transform (lam := 1 / 2) (by norm_num) n hy
  push_cast at h
  norm_num only [sub_self, cpow_zero, one_mul, mul_one] at h
  simp only [legendre_eq_ultrasphPoly]
  rw [h, Complex.Gamma_nat_eq_factorial, Complex.Gamma_one_half_eq]
  have hs : ((π : ℂ)) ^ (1 / 2 : ℂ) = ((√π : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; norm_num
  have hr : (2 * (y : ℂ)) ^ (1 / 2 : ℂ) = ((√(2 * y) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow (by positivity)]; norm_num
  have key : √(2 * π / y) * (√π * √(2 * y)) = 2 * π := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity),
      show 2 * π / y * (π * (2 * y)) = (2 * π) ^ 2 by field_simp,
      Real.sqrt_sq (by positivity)]
  have keyC := congrArg (fun r : ℝ => (r : ℂ)) key
  push_cast at keyC
  have h1 : ((√π : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have h2 : ((√(2 * y) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
  have h3 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [hs, hr]
  set J := besselJ ((n : ℂ) + 1 / 2) (y : ℂ) with hJ
  field_simp
  linear_combination (-J) * keyC

/-- `1/Γ(y) = (y)_m/Γ(y+m)` for every `y` and every `m`, including poles. -/
theorem recip_Gamma_eq_poch_mul_recip_Gamma_add (m : ℕ) (y : ℂ) :
    (Gamma y)⁻¹ = poch y m * (Gamma (y + m))⁻¹ := by
  cases m with
  | zero => simp [poch_zero]
  | succ p => exact recip_Gamma_eq_poch_mul p y

/-- The Mellin transform `∫₀¹ (1-x²)^{λ-1/2} C_{2m}^{(λ)}(x) x^{z-1} dx` in closed form, for
`λ > 0` and `Re z > 0`. -/
theorem ultrasphPoly_mellin_transform_even {lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 0 < z.re)
    (m : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam (2 * m) x * (x : ℂ) ^ (z - 1) =
      Real.pi * (2 : ℂ) ^ (1 - 2 * lam - z) * Gamma (((2 * m : ℕ) : ℂ) + 2 * lam : ℂ) * Gamma z /
        ((2 * m).factorial * Gamma (lam : ℂ) *
          Gamma (1 / 2 + ((2 * m : ℕ) : ℂ) / 2 + lam + z / 2) *
          Gamma (1 / 2 + z / 2 - ((2 * m : ℕ) : ℂ) / 2)) := by
  set K0 : ℂ := poch (lam : ℂ) m / poch (1 / 2) m * (-1 : ℂ) ^ m with hK0
  have hrw : ∀ x : ℝ, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) * ultrasphPoly lam (2 * m) x *
      (x : ℂ) ^ (z - 1) = (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2) * (x : ℂ) ^ (z - 1) *
        (K0 * jacobiPolyP ((-1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) m
          ((1 - 2 * x ^ 2 : ℝ) : ℂ)) := by
    intro x
    rw [ultrasphPoly_quadratic_even (by simp; linarith),
      show 2 * (x : ℂ) ^ 2 - 1 = -((1 - 2 * x ^ 2 : ℝ) : ℂ) by push_cast; ring,
      jacobi_reflection (by simp; linarith) (by norm_num), hK0]
    push_cast
    ring_nf
  rw [intervalIntegral.integral_congr (fun x _ => hrw x),
    integral_one_sub_sq_cpow_mul_cpow ((lam : ℂ) - 1 / 2) (z - 1)
      (fun s => K0 * jacobiPolyP ((-1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) m s)]
  have hz2 : 0 < (z / 2).re := by simp; linarith
  have hJ := jacobi_mellin_transform (α := -1 / 2) (β := lam - 1 / 2) (by norm_num)
    (by linarith) hz2 m
  have hint : (∫ s : ℝ in (-1 : ℝ)..1, (1 - (s : ℂ)) ^ ((z - 1 - 1) / 2) *
      (1 + (s : ℂ)) ^ ((lam : ℂ) - 1 / 2) *
      (K0 * jacobiPolyP ((-1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) m s)) =
      K0 * ∫ s : ℝ in (-1 : ℝ)..1, (1 - (s : ℂ)) ^ (z / 2 - 1) *
        (1 + (s : ℂ)) ^ ((lam - 1 / 2 : ℝ) : ℂ) *
        jacobiPolyP ((-1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) m s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [show (z - 1 - 1) / 2 = z / 2 - 1 by ring]
    push_cast
    ring
  rw [hint, hJ]
  have hl : (0 : ℝ) < (lam : ℂ).re := by simpa using hlam
  rw [show (1 : ℂ) + ((lam - 1 / 2 : ℝ) : ℂ) + z / 2 + m = lam + 1 / 2 + z / 2 + m by
      push_cast; ring,
    show (1 / 2 : ℂ) + ((2 * m : ℕ) : ℂ) / 2 + lam + z / 2 = lam + 1 / 2 + z / 2 + m by
      push_cast; ring,
    show (1 : ℂ) + ((lam - 1 / 2 : ℝ) : ℂ) + m = (m + lam) + 1 / 2 by push_cast; ring,
    show ((2 * m : ℕ) : ℂ) + 2 * lam = 2 * (m + lam) by push_cast; ring,
    show (1 / 2 : ℂ) + z / 2 - ((2 * m : ℕ) : ℂ) / 2 = 1 / 2 + z / 2 - m by push_cast; ring,
    show (1 : ℂ) + ((-1 / 2 : ℝ) : ℂ) - z / 2 = 1 / 2 - z / 2 by push_cast; ring]
  -- the reciprocal of `Γ(1/2 + z/2 - m)`, valid also at poles
  have hE : (Gamma (1 / 2 + z / 2 - m))⁻¹ =
      (-1 : ℂ) ^ m * poch (1 / 2 - z / 2) m * (Gamma (1 / 2 + z / 2))⁻¹ := by
    have h := DLMF.Gamma.poch_neg_eq ((m : ℂ) - 1 / 2 - z / 2) m
    rw [show -((m : ℂ) - 1 / 2 - z / 2) = 1 / 2 + z / 2 - m by ring,
      show (m : ℂ) - 1 / 2 - z / 2 - m + 1 = 1 / 2 - z / 2 by ring] at h
    rw [recip_Gamma_eq_poch_mul_recip_Gamma_add m, h, show 1 / 2 + z / 2 - (m : ℂ) + m = 1 / 2 + z / 2
      by ring]
  have F1 := Complex.Gamma_mul_Gamma_add_half (z / 2)
  rw [show 2 * (z / 2) = z by ring, show z / 2 + 1 / 2 = 1 / 2 + z / 2 by ring] at F1
  have F2 := Complex.Gamma_mul_Gamma_add_half ((m : ℂ) + lam)
  have F3 : Gamma ((m : ℂ) + lam) = poch (lam : ℂ) m * Gamma lam := by
    rw [add_comm, Gamma_add_nat_eq_poch_mul_Gamma hl]
  have F4 := two_pow_mul_poch_half m
  have hpi : (Real.pi : ℂ) = (Real.sqrt Real.pi : ℂ) * (Real.sqrt Real.pi : ℂ) := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hV : (2 : ℂ) ^ (1 - 2 * (lam : ℂ) - z) * 2 =
      (2 : ℂ) ^ (1 - 2 * ((m : ℂ) + lam)) * (2 : ℂ) ^ (1 - z) * (2 : ℂ) ^ (2 * m) := by
    rw [← cpow_natCast, ← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero,
      show 1 - 2 * ((m : ℂ) + lam) + (1 - z) + ((2 * m : ℕ) : ℂ) = (1 - 2 * lam - z) + 1 by
        push_cast; ring, cpow_add _ _ two_ne_zero, cpow_one]
  have hPQ : (2 : ℂ) ^ (-((lam : ℂ) - 1 / 2 + (z - 1 - 1) / 2)) *
      (2 : ℂ) ^ (((lam - 1 / 2 : ℝ) : ℂ) + z / 2) = 2 := by
    rw [← cpow_add _ _ two_ne_zero, show -((lam : ℂ) - 1 / 2 + (z - 1 - 1) / 2) +
      (((lam - 1 / 2 : ℝ) : ℂ) + z / 2) = 1 by push_cast; ring, cpow_one]
  have hW : Gamma (1 / 2 + z / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hD : Gamma (lam + 1 / 2 + z / 2 + m) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have hGl : Gamma (lam : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos hl
  have hph : poch (1 / 2 : ℂ) m ≠ 0 := poch_ne_zero_of_re_pos (by norm_num) m
  have hfm : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have hS : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2 : ℂ) ^ (1 - 2 * ((m : ℂ) + lam)) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hU : (2 : ℂ) ^ (1 - z) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hF : (2 : ℂ) ^ (2 * m) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [hpi, div_mul_eq_div_div _ _ (Gamma (1 / 2 + z / 2 - (m : ℂ))),
    div_eq_mul_inv _ (Gamma (1 / 2 + z / 2 - (m : ℂ))), hE, ← F4]
  simp only [hK0]
  generalize (2 : ℂ) ^ (-((lam : ℂ) - 1 / 2 + (z - 1 - 1) / 2)) = P at hPQ ⊢
  generalize (2 : ℂ) ^ (((lam - 1 / 2 : ℝ) : ℂ) + z / 2) = Q at hPQ ⊢
  generalize (2 : ℂ) ^ (1 - 2 * (lam : ℂ) - z) = V at hV ⊢
  generalize (2 : ℂ) ^ (1 - 2 * ((m : ℂ) + lam)) = T at hV hT F2 ⊢
  generalize (2 : ℂ) ^ (1 - z) = U at hV hU F1 ⊢
  generalize (2 : ℂ) ^ (2 * m) = F at hV hF ⊢
  generalize (Real.sqrt Real.pi : ℂ) = S at hS F1 F2 ⊢
  generalize Gamma (1 / 2 + z / 2) = W at hW F1 ⊢
  generalize Gamma (z / 2) = Gz2 at F1 ⊢
  generalize Gamma z = Gz at F1 ⊢
  generalize Gamma (2 * ((m : ℂ) + lam)) = G2 at F2 ⊢
  generalize Gamma ((m : ℂ) + lam) = Gml at F2 F3 ⊢
  generalize Gamma ((m : ℂ) + lam + 1 / 2) = Gmlh at F2 ⊢
  generalize Gamma (lam + 1 / 2 + z / 2 + m) = D at hD ⊢
  generalize Gamma (lam : ℂ) = Gl at hGl F3 ⊢
  generalize poch (1 / 2 : ℂ) m = ph at hph ⊢
  generalize poch (lam : ℂ) m = pl at F3 ⊢
  generalize poch (1 / 2 - z / 2) m = R
  generalize (m ! : ℂ) = fm at hfm ⊢
  have hG2 : G2 = Gml * Gmlh / (T * S) := by field_simp; linear_combination -F2
  have hGz : Gz = Gz2 * W / (U * S) := by field_simp; linear_combination -F1
  have hV' : V = T * U * F / 2 := by field_simp; linear_combination hV
  rw [hG2, hGz, hV', F3]
  field_simp
  linear_combination 2 * pl * Gz2 * Gmlh * R * hPQ


/-- The Mellin transform `∫₀¹ (1-x²)^{λ-1/2} C_{2m+1}^{(λ)}(x) x^{z-1} dx` in closed form, for
`λ > 0` and `Re z > 0`. -/
theorem ultrasphPoly_mellin_transform_odd {lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 0 < z.re)
    (m : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam (2 * m + 1) x * (x : ℂ) ^ (z - 1) =
      Real.pi * (2 : ℂ) ^ (1 - 2 * lam - z) * Gamma (((2 * m + 1 : ℕ) : ℂ) + 2 * lam : ℂ) *
        Gamma z / ((2 * m + 1).factorial * Gamma (lam : ℂ) *
          Gamma (1 / 2 + ((2 * m + 1 : ℕ) : ℂ) / 2 + lam + z / 2) *
          Gamma (1 / 2 + z / 2 - ((2 * m + 1 : ℕ) : ℂ) / 2)) := by
  set K1 : ℂ := poch (lam : ℂ) (m + 1) / poch (1 / 2) (m + 1) * (-1 : ℂ) ^ m with hK1
  have hrw : Set.EqOn (fun x : ℝ => (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam (2 * m + 1) x * (x : ℂ) ^ (z - 1))
      (fun x : ℝ => (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2) * (x : ℂ) ^ z *
        (K1 * jacobiPolyP ((1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) m
          ((1 - 2 * x ^ 2 : ℝ) : ℂ))) (Set.Ioo 0 1) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.1.ne'
    simp only
    rw [ultrasphPoly_quadratic_odd (by simp; linarith),
      show 2 * (x : ℂ) ^ 2 - 1 = -((1 - 2 * x ^ 2 : ℝ) : ℂ) by push_cast; ring,
      jacobi_reflection (by simp; linarith) (by norm_num), hK1,
      show z = (z - 1) + 1 by ring, cpow_add _ _ hx0, cpow_one,
      show z - 1 + 1 - 1 = z - 1 by ring]
    push_cast
    ring_nf
  rw [intervalIntegral.integral_congr_Ioo_of_le (by norm_num) hrw,
    integral_one_sub_sq_cpow_mul_cpow ((lam : ℂ) - 1 / 2) z
      (fun s => K1 * jacobiPolyP ((1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) m s)]
  have hw : 0 < (1 / 2 + z / 2).re := by simp; linarith
  have hJ := jacobi_mellin_transform (α := 1 / 2) (β := lam - 1 / 2) (by norm_num)
    (by linarith) hw m
  have hint : (∫ s : ℝ in (-1 : ℝ)..1, (1 - (s : ℂ)) ^ ((z - 1) / 2) *
      (1 + (s : ℂ)) ^ ((lam : ℂ) - 1 / 2) *
      (K1 * jacobiPolyP ((1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) m s)) =
      K1 * ∫ s : ℝ in (-1 : ℝ)..1, (1 - (s : ℂ)) ^ (1 / 2 + z / 2 - 1) *
        (1 + (s : ℂ)) ^ ((lam - 1 / 2 : ℝ) : ℂ) *
        jacobiPolyP ((1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) m s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [show (z - 1) / 2 = 1 / 2 + z / 2 - 1 by ring]
    push_cast
    ring
  rw [hint, hJ]
  have hl : (0 : ℝ) < (lam : ℂ).re := by simpa using hlam
  rw [show (1 : ℂ) + ((lam - 1 / 2 : ℝ) : ℂ) + (1 / 2 + z / 2) + m = lam + 1 + z / 2 + m by
      push_cast; ring,
    show (1 / 2 : ℂ) + ((2 * m + 1 : ℕ) : ℂ) / 2 + lam + z / 2 = lam + 1 + z / 2 + m by
      push_cast; ring,
    show (1 : ℂ) + ((lam - 1 / 2 : ℝ) : ℂ) + m = (m + lam) + 1 / 2 by push_cast; ring,
    show ((2 * m + 1 : ℕ) : ℂ) + 2 * lam = 2 * ((m + lam) + 1 / 2) by push_cast; ring,
    show (1 / 2 : ℂ) + z / 2 - ((2 * m + 1 : ℕ) : ℂ) / 2 = z / 2 - m by push_cast; ring,
    show (1 : ℂ) + ((1 / 2 : ℝ) : ℂ) - (1 / 2 + z / 2) = 1 - z / 2 by push_cast; ring]
  have hE : (Gamma (z / 2 - m))⁻¹ =
      (-1 : ℂ) ^ m * poch (1 - z / 2) m * (Gamma (z / 2))⁻¹ := by
    have h := DLMF.Gamma.poch_neg_eq ((m : ℂ) - z / 2) m
    rw [show -((m : ℂ) - z / 2) = z / 2 - m by ring,
      show (m : ℂ) - z / 2 - m + 1 = 1 - z / 2 by ring] at h
    rw [recip_Gamma_eq_poch_mul_recip_Gamma_add m, h, show z / 2 - (m : ℂ) + m = z / 2 by ring]
  have F1 := Complex.Gamma_mul_Gamma_add_half (z / 2)
  rw [show 2 * (z / 2) = z by ring, show z / 2 + 1 / 2 = 1 / 2 + z / 2 by ring] at F1
  have F2 := Complex.Gamma_mul_Gamma_add_half ((m : ℂ) + lam + 1 / 2)
  rw [show (m : ℂ) + lam + 1 / 2 + 1 / 2 = lam + (m + 1 : ℕ) by push_cast; ring] at F2
  have F3 : Gamma ((lam : ℂ) + (m + 1 : ℕ)) = poch (lam : ℂ) (m + 1) * Gamma lam :=
    Gamma_add_nat_eq_poch_mul_Gamma hl (m + 1)
  have F4 : (2 : ℂ) ^ (2 * m + 1) * poch (1 / 2) (m + 1) * m ! = (2 * m + 1).factorial := by
    rw [Nat.factorial_succ, Nat.cast_mul, ← two_pow_mul_poch_half m, poch_succ, pow_succ]
    push_cast
    ring
  have hpi : (Real.pi : ℂ) = (Real.sqrt Real.pi : ℂ) * (Real.sqrt Real.pi : ℂ) := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hV : (2 : ℂ) ^ (1 - 2 * (lam : ℂ) - z) * 2 =
      (2 : ℂ) ^ (1 - 2 * ((m : ℂ) + lam + 1 / 2)) * (2 : ℂ) ^ (1 - z) * (2 : ℂ) ^ (2 * m + 1) := by
    rw [← cpow_natCast, ← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero,
      show 1 - 2 * ((m : ℂ) + lam + 1 / 2) + (1 - z) + ((2 * m + 1 : ℕ) : ℂ) =
        (1 - 2 * lam - z) + 1 by push_cast; ring, cpow_add _ _ two_ne_zero, cpow_one]
  have hPQ : (2 : ℂ) ^ (-((lam : ℂ) - 1 / 2 + (z - 1) / 2)) *
      (2 : ℂ) ^ (((lam - 1 / 2 : ℝ) : ℂ) + (1 / 2 + z / 2)) = 2 := by
    rw [← cpow_add _ _ two_ne_zero, show -((lam : ℂ) - 1 / 2 + (z - 1) / 2) +
      (((lam - 1 / 2 : ℝ) : ℂ) + (1 / 2 + z / 2)) = 1 by push_cast; ring, cpow_one]
  have hz2 : Gamma (z / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hD : Gamma (lam + 1 + z / 2 + m) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have hGl : Gamma (lam : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos hl
  have hph : poch (1 / 2 : ℂ) (m + 1) ≠ 0 := poch_ne_zero_of_re_pos (by norm_num) _
  have hfm : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have hS : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2 : ℂ) ^ (1 - 2 * ((m : ℂ) + lam + 1 / 2)) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hU : (2 : ℂ) ^ (1 - z) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hF : (2 : ℂ) ^ (2 * m + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [hpi, div_mul_eq_div_div _ _ (Gamma (z / 2 - (m : ℂ))),
    div_eq_mul_inv _ (Gamma (z / 2 - (m : ℂ))), hE, ← F4]
  simp only [hK1]
  generalize (2 : ℂ) ^ (-((lam : ℂ) - 1 / 2 + (z - 1) / 2)) = P at hPQ ⊢
  generalize (2 : ℂ) ^ (((lam - 1 / 2 : ℝ) : ℂ) + (1 / 2 + z / 2)) = Q at hPQ ⊢
  generalize (2 : ℂ) ^ (1 - 2 * (lam : ℂ) - z) = V at hV ⊢
  generalize (2 : ℂ) ^ (1 - 2 * ((m : ℂ) + lam + 1 / 2)) = T at hV hT F2 ⊢
  generalize (2 : ℂ) ^ (1 - z) = U at hV hU F1 ⊢
  generalize (2 : ℂ) ^ (2 * m + 1) = F at hV hF ⊢
  generalize (Real.sqrt Real.pi : ℂ) = S at hS F1 F2 ⊢
  generalize Gamma (1 / 2 + z / 2) = W at F1 ⊢
  generalize Gamma (z / 2) = Gz2 at hz2 F1 ⊢
  generalize Gamma z = Gz at F1 ⊢
  generalize Gamma (2 * ((m : ℂ) + lam + 1 / 2)) = G2 at F2 ⊢
  generalize Gamma ((lam : ℂ) + (m + 1 : ℕ)) = Gml1 at F2 F3 ⊢
  generalize Gamma ((m : ℂ) + lam + 1 / 2) = Gmlh at F2 ⊢
  generalize Gamma (lam + 1 + z / 2 + m) = D at hD ⊢
  generalize Gamma (lam : ℂ) = Gl at hGl F3 ⊢
  generalize poch (1 / 2 : ℂ) (m + 1) = ph at hph ⊢
  generalize poch (lam : ℂ) (m + 1) = pl at F3 ⊢
  generalize poch (1 - z / 2) m = R
  generalize (m ! : ℂ) = fm at hfm ⊢
  have hG2 : G2 = Gmlh * Gml1 / (T * S) := by field_simp; linear_combination -F2
  have hGz : Gz = Gz2 * W / (U * S) := by field_simp; linear_combination -F1
  have hV' : V = T * U * F / 2 := by field_simp; linear_combination hV
  rw [hG2, hGz, hV', F3]
  field_simp
  linear_combination 2 * pl * W * Gmlh * R * hPQ


@[dlmf 18.17.E37]
theorem ultrasphPoly_mellin_transform {lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      ultrasphPoly lam n x * (x : ℂ) ^ (z - 1) =
      Real.pi * (2 : ℂ) ^ (1 - 2 * lam - z) * Gamma (n + 2 * lam : ℂ) * Gamma z /
        (n.factorial * Gamma (lam : ℂ) * Gamma (1 / 2 + n / 2 + lam + z / 2) *
          Gamma (1 / 2 + z / 2 - n / 2)) := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · exact ultrasphPoly_mellin_transform_even hlam hz m
  · exact ultrasphPoly_mellin_transform_odd hlam hz m

/-- Finite-sum version, including parameters where the displayed hypergeometric quotient
has removable singularities. -/
@[dlmf 18.17.E40]
theorem laguerrePolyL_mellin_laplace_transform {a : ℝ} (ha : 0 < a) {α : ℂ} (hα : -1 < α.re)
    (b : ℂ) {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-a * x) * laguerrePolyL α n (b * x) * (x : ℂ) ^ (z - 1) =
      ∑ k ∈ Finset.range (n + 1), poch (α + k + 1) (n - k) * (-b) ^ k /
        ((n - k).factorial * (k.factorial : ℂ)) * Gamma (z + k) / (a : ℂ) ^ (z + k) := by
  have hα' : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) :=
    not_neg_nat_of_re_pos (by simp only [add_re, one_re]; linarith)
  have heq (x : ℝ) : laguerrePolyL α n (b * x) =
      ∑ k ∈ Finset.range (n + 1),
        (poch (α + k + 1) (n - k) * (-b) ^ k / ((n - k).factorial * (k.factorial : ℂ))) *
          (x : ℂ) ^ k := by
    rw [laguerrePolyL_eq_sum hα']
    apply Finset.sum_congr rfl
    intro k _
    rw [show -(b * (x : ℂ)) = -b * x by ring, mul_pow]
    rw [show α + 1 + (k : ℂ) = α + k + 1 by ring]
    ring
  simp_rw [heq]
  exact integral_finite_sum_mellin_laplace ha hz _ _ id

end DLMF.OrthogonalPolynomials
