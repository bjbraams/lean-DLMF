/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic
public import DLMF.Heun.LocalSolutions
public import DLMF.Hypergeometric.Riemann
public import Carlson.TwoVariable.RPolynomial.Hypergeometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Heun functions and the Gauss hypergeometric function (DLMF §31.7(i), §31.11)

`₂F₁` is Mathlib's `ordinaryHypergeometric` (the series; junk outside `|z| < 1`).

* §31.7(i): the reductions 31.7.1 are proved for every `z` (the Maclaurin coefficients of `Hl`
  are the hypergeometric coefficients, so the two series agree term by term). DLMF's
  `Hl(0, 0; α, β, γ, α + β + 1 - γ; z)` (31.7.1, middle member) is degenerate (the recurrence
  divides by `a`); it is acquired in two readings: as the limit `a → 0` along `q = aαβ`
  (proved) and as the exponent-`0` solution of Heun's equation with `a = q = 0` (admitted). The
  quadratic and cubic reductions 31.7.2–31.7.4 are stated where both series converge;
  31.7.2 and 31.7.3 are proved (the domain is star-shaped about `0`; the composed `₂F₁` solves
  Heun's equation and the characterization of `Hl` applies). 31.7.4 is admitted: its domain
  has three components (the preimage of the disk under the cube) and the identity holds only on
  the one containing `0`. The classification remark (other reductions exist only for finitely
  many `(a, p)`, `q = αβp`; Maier 2005) and the reference to Joyce (1994) are not acquired.
* §31.11: the coefficients `K_j, L_j, M_j` (31.11.6–31.11.8, as corrected in DLMF 1.1.7) and
  the Fuchs–Frobenius solutions `P_j^5, P_j^6` at `∞` (31.11.3_1, 31.11.3_2) are definitions
  in Basic. Here: the P-symbol property 31.11.2 of `P_j^5, P_j^6` (Riemann's equation with
  singularities `0, 1, ∞`, the project's `riemannNormalOperator`), the parameter conditions
  31.11.3, 31.11.9–31.11.11, 31.11.14–31.11.17, the Type I expansion 31.11.12 of the solution
  31.3.10, the continued fraction 31.11.13 and the Type II expansion of `(0,1)`-Heun functions
  for the pair 31.11.14.

Numerical checks (mpmath): 31.7.1–31.7.4 to `10⁻³⁰`; the Type I series 31.11.1 with 31.11.10
and with 31.11.11 reproduces 31.3.10 and 31.3.11 at `z = 7 + 2i` to 15 digits
(`a = 2.3 + 0.7i`, complex `α, …, δ, q`); for `a = 3, α = 0.4, β = 1.2, γ = 0.7, δ = 0.6` and the
eigenvalue `q ≈ 0.25992` the minimal solution of 31.11.5 (backward recursion) satisfies 31.11.4
to `10⁻³¹`, and the Type II series with 31.11.14 is a constant multiple (`≈ 0.92528`) of the
Heun function at three points. With the pairs 31.11.15–31.11.17 the same series with the
principal branch of `P_j^6` is *not* a constant multiple of that Heun function (the ratio varies
from point to point); DLMF does not say which branches or which of the four Heun functions with
exponents `{0, 1-γ} × {0, 1-δ}` are meant, so for those pairs only the conditions 31.11.3 are
acquired. The remarks of §31.11(iii) on convergence of Type I series for Heun functions in cut
planes and inside the ellipse `𝓔` for other branches, the statement that Type II series diverge
for Fuchs–Frobenius solutions, and §31.11(v) (Schmidt's doubly-infinite series) are not
acquired.
-/

@[expose] public section

open Complex Filter Set
open scoped Topology Real Nat

noncomputable section

namespace DLMF.Heun

variable {a q α β γ δ ε : ℂ}

/-! ### Reductions to `₂F₁` (§31.7(i)) -/

/-- Helper for 31.7.1: no Pochhammer value `(γ)_n` vanishes when `γ ∉ {0, -1, -2, …}`. -/
theorem h31_ascPochhammer_ne_zero (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ)) (n : ℕ) :
    (ascPochhammer ℂ n).eval γ ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval]
    refine mul_ne_zero ih fun h => hγ n ?_
    linear_combination h

/-- Helper for 31.7.1: `F_{n+1}(n+1)(n+γ) = (n+α)(n+β)F_n` for the hypergeometric coefficients. -/
theorem h31_hgCoeff_succ (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ)) (n : ℕ) :
    ordinaryHypergeometricCoefficient α β γ (n + 1) * (((n : ℂ) + 1) * ((n : ℂ) + γ)) =
      ((n : ℂ) + α) * ((n : ℂ) + β) * ordinaryHypergeometricCoefficient α β γ n := by
  have h1 := h31_ascPochhammer_ne_zero hγ n
  have h2 : γ + n ≠ 0 := fun h => hγ n (by linear_combination h)
  have h3 : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h4 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  simp only [ordinaryHypergeometricCoefficient, ascPochhammer_succ_eval, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- Helper for 31.7.1: if `q = aαβ` and `Q_{j+1} + q - (j+1)(j+γ) = a(j+1+α)(j+1+β)` for all
`j`, the Maclaurin coefficients of `Hl` are the hypergeometric coefficients. -/
theorem h31_heunLocalCoeff_eq_hg (ha : a ≠ 0) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ)) (hq : q = a * α * β)
    (hQ : ∀ j : ℕ, heunRecQ a α β γ δ (j + 1) + q - ((j : ℂ) + 1) * ((j : ℂ) + γ) =
      a * ((j : ℂ) + 1 + α) * ((j : ℂ) + 1 + β)) (j : ℕ) :
    heunLocalCoeff a q α β γ δ j = ordinaryHypergeometricCoefficient α β γ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => show (1 : ℂ) = _; simp [ordinaryHypergeometricCoefficient]
    | 1, _ =>
      have hγ0 : γ ≠ 0 := by simpa using hγ 0
      show q / (a * γ) = _
      simp only [ordinaryHypergeometricCoefficient, ascPochhammer_one,
        Polynomial.eval_X, Nat.factorial_one, Nat.cast_one, inv_one, one_mul, hq]
      field_simp
    | k + 2, ih =>
      rw [heunLocalCoeff, ih (k + 1) (by omega), ih k (by omega)]
      have hR : heunRecR a γ (k + 1) ≠ 0 := by
        unfold heunRecR
        refine mul_ne_zero (mul_ne_zero ha (by exact_mod_cast (k + 1).succ_ne_zero)) ?_
        intro h
        push_cast at h
        exact hγ (k + 1) (by push_cast; linear_combination h)
      rw [div_eq_iff hR]
      have e1 := h31_hgCoeff_succ (α := α) (β := β) hγ k
      have e2 := h31_hgCoeff_succ (α := α) (β := β) hγ (k + 1)
      have hk := hQ k
      generalize ordinaryHypergeometricCoefficient α β γ (k + 1 + 1) = F2 at e2 ⊢
      generalize ordinaryHypergeometricCoefficient α β γ (k + 1) = F1 at e1 e2 ⊢
      generalize ordinaryHypergeometricCoefficient α β γ k = F0 at e1 ⊢
      generalize heunRecQ a α β γ δ (k + 1) = Q at hk ⊢
      unfold heunRecP heunRecR
      push_cast at e2 ⊢
      linear_combination F1 * hk + e1 - a * e2

/-- DLMF 31.7.1 (first equality): `₂F₁(α, β; γ; z) = Hl(1, αβ; α, β, γ, δ; z)` for
`γ ∉ {0, -1, …}`. Stronger than DLMF: for every `z`, as an identity of the two series. -/
@[dlmf 31.7.E1]
theorem heunLocal_one_eq_hypergeometric (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ)) (z : ℂ) :
    heunLocal 1 (α * β) α β γ δ z = ordinaryHypergeometric α β γ z := by
  rw [heunLocal, ordinaryHypergeometric_eq_tsum]
  refine tsum_congr fun j => ?_
  rw [h31_heunLocalCoeff_eq_hg one_ne_zero hγ (by ring) (fun j => by
    unfold heunRecQ heunEps; push_cast; ring) j, smul_eq_mul]

/-- DLMF 31.7.1 (third equality): `₂F₁(α, β; γ; z) = Hl(a, aαβ; α, β, γ, α + β + 1 - γ; z)` for
`a ≠ 0`, `γ ∉ {0, -1, …}` (then `ε = 0` and the singularity at `a` disappears). Stronger than
DLMF: for every `z`, as an identity of the two series. -/
@[dlmf 31.7.E1]
theorem heunLocal_eps_zero_eq_hypergeometric (ha : a ≠ 0) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ))
    (z : ℂ) :
    heunLocal a (a * α * β) α β γ (α + β + 1 - γ) z = ordinaryHypergeometric α β γ z := by
  rw [heunLocal, ordinaryHypergeometric_eq_tsum]
  refine tsum_congr fun j => ?_
  rw [h31_heunLocalCoeff_eq_hg ha hγ rfl (fun j => by
    unfold heunRecQ heunEps; push_cast; ring) j, smul_eq_mul]

/-- DLMF 31.7.1 (second equality, first reading): `Hl(0, 0; α, β, γ, α + β + 1 - γ; z)` as the
limit `a → 0` of `Hl(a, aαβ; α, β, γ, α + β + 1 - γ; z)` is `₂F₁(α, β; γ; z)`. -/
@[dlmf 31.7.E1]
theorem tendsto_heunLocal_zero_eq_hypergeometric (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ)) (z : ℂ) :
    Tendsto (fun a => heunLocal a (a * α * β) α β γ (α + β + 1 - γ) z) (𝓝[≠] 0)
      (𝓝 (ordinaryHypergeometric α β γ z)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (heunLocal_eps_zero_eq_hypergeometric ha hγ z).symm

/-- DLMF 31.7.1 (second equality, second reading): for `a = q = 0` and
`δ = α + β + 1 - γ`, `ε = 0`, Heun's equation is Gauss's hypergeometric equation and
`₂F₁(α, β; γ; ·)` is its solution on the punctured unit disk. -/
@[dlmf 31.7.E1]
theorem hypergeometric_isHeunSolOn_zero (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ)) :
    IsHeunSolOn 0 0 α β γ (α + β + 1 - γ) 0 (ordinaryHypergeometric α β γ)
      (Metric.ball 0 1 \ {0}) := by
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · exact (DLMF.Hypergeometric.analyticAt_ordinaryHypergeometric
      (mem_ball_zero_iff.1 hz.1)).differentiableAt
  · obtain ⟨hz1, hz0⟩ := hz
    have hz0' : z ≠ 0 := hz0
    rw [mem_ball_zero_iff] at hz1
    have hzne1 : z - 1 ≠ 0 := fun h => by
      rw [sub_eq_zero] at h; rw [h, norm_one] at hz1; exact lt_irrefl _ hz1
    have hA := DLMF.Hypergeometric.analyticAt_ordinaryHypergeometric (a := α) (b := β) (c := γ) hz1
    have hd := hA.deriv.differentiableAt.hasDerivAt
    have hode := DLMF.Hypergeometric.ordinaryHypergeometric_ode (a := α) (b := β) (c := γ)
      (fun k => by simpa using hγ k) hz1 hz0' (fun h => hzne1 (by rw [h, sub_self]))
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hode
    convert hd using 1
    simp only [heunCoeffP, heunCoeffR]
    have h1z : 1 - z ≠ 0 := fun h => hzne1 (by linear_combination -h)
    field_simp
    linear_combination z * hode

/-- `‖t z (2 - t z)‖ ≤ ‖z (2 - z)‖` for `0 ≤ t ≤ 1` and `‖z‖ ≤ 1`. -/
theorem p2h_norm_quad_le {z : ℂ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hz : ‖z‖ ≤ 1) :
    ‖(t : ℂ) * z * (2 - (t : ℂ) * z)‖ ≤ ‖z * (2 - z)‖ := by
  set r := ‖z‖ with hr
  set x := z.re with hxdef
  have hx : x ≤ r := Complex.re_le_norm z
  have hr0 : 0 ≤ r := norm_nonneg z
  have hsq : ∀ u : ℂ, ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := fun u => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hz2 : r ^ 2 = x ^ 2 + z.im ^ 2 := hsq z
  have e1 : ‖2 - (t : ℂ) * z‖ ^ 2 = 4 - 4 * t * x + t ^ 2 * r ^ 2 := by
    rw [hsq, hz2]; simp [hxdef]; ring
  have e2 : ‖2 - z‖ ^ 2 = 4 - 4 * x + r ^ 2 := by
    rw [hsq, hz2]; simp [hxdef]; ring
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
  suffices h : t * ‖2 - (t : ℂ) * z‖ ≤ ‖2 - z‖ by
    calc t * r * ‖2 - (t : ℂ) * z‖ = r * (t * ‖2 - (t : ℂ) * z‖) := by ring
      _ ≤ r * ‖2 - z‖ := mul_le_mul_of_nonneg_left h hr0
  rw [← pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero, mul_pow, e1, e2]
  have hB1 : 0 ≤ (r - x) * (4 * (1 + t + t ^ 2)) := mul_nonneg (by linarith) (by positivity)
  have hB2 : 0 ≤ 2 + 2 * t + 2 * t ^ 2 - 2 * t ^ 3 := by nlinarith
  have hB3 : 0 ≤ (1 - r) * (4 * (1 + t + t ^ 2) - (1 + r) * (1 + t) * (1 + t ^ 2)) := by
    refine mul_nonneg (by linarith) ?_
    nlinarith [mul_nonneg (sub_nonneg.2 hz) (mul_nonneg (by linarith : (0:ℝ) ≤ 1 + t)
      (by positivity : (0:ℝ) ≤ 1 + t ^ 2))]
  have hC1 : 0 ≤ (1 - t) * (1 + 2 * t - t ^ 2) := mul_nonneg (by linarith) (by nlinarith)
  have hB : 0 ≤ 4 * (1 + t) - 4 * x * (1 + t + t ^ 2) + r ^ 2 * (1 + t) * (1 + t ^ 2) := by
    nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 ht1) hB]

/-- `‖t z (3 - t z)²‖ ≤ ‖z (3 - z)²‖` for `0 ≤ t ≤ 1` and `‖z‖ ≤ 1`. -/
theorem p2h_norm_cubic_le {z : ℂ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hz : ‖z‖ ≤ 1) :
    ‖(t : ℂ) * z * (3 - (t : ℂ) * z) ^ 2‖ ≤ ‖z * (3 - z) ^ 2‖ := by
  set r := ‖z‖ with hr
  set x := z.re with hxdef
  have hx : x ≤ r := Complex.re_le_norm z
  have hr0 : 0 ≤ r := norm_nonneg z
  have hsq : ∀ u : ℂ, ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := fun u => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hz2 : r ^ 2 = x ^ 2 + z.im ^ 2 := hsq z
  have e1 : ‖3 - (t : ℂ) * z‖ ^ 2 = 9 - 6 * t * x + t ^ 2 * r ^ 2 := by
    rw [hsq, hz2]; simp [hxdef]; ring
  have e2 : ‖3 - z‖ ^ 2 = 9 - 6 * x + r ^ 2 := by
    rw [hsq, hz2]; simp [hxdef]; ring
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg ht0, e1, e2]
  have hB3 : 0 ≤ (1 - r) * (6 * (1 + t) - (1 + r) * (1 + t + t ^ 2)) := by
    refine mul_nonneg (by linarith) ?_
    nlinarith [mul_nonneg (sub_nonneg.2 hz) (by positivity : (0:ℝ) ≤ 1 + t + t ^ 2)]
  have hB1 : 0 ≤ (r - x) * (6 * (1 + t)) := mul_nonneg (by linarith) (by positivity)
  have hC1 : 0 ≤ (1 - t) * (4 - t) := mul_nonneg (by linarith) (by linarith)
  have hB : 0 ≤ 9 - 6 * x * (1 + t) + r ^ 2 * (1 + t + t ^ 2) := by nlinarith
  have key : t * (9 - 6 * t * x + t ^ 2 * r ^ 2) ≤ 9 - 6 * x + r ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 ht1) hB]
  calc t * r * (9 - 6 * t * x + t ^ 2 * r ^ 2) = r * (t * (9 - 6 * t * x + t ^ 2 * r ^ 2)) := by
        ring
    _ ≤ r * (9 - 6 * x + r ^ 2) := mul_le_mul_of_nonneg_left key hr0

/-- DLMF 31.7.2: `Hl(2, αβ; α, β, γ, α + β - 2γ + 1; z) = ₂F₁(α/2, β/2; γ; 1 - (1-z)²)` where
both series converge. -/
@[dlmf 31.7.E2]
theorem heunLocal_two_eq_hypergeometric (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ)) {z : ℂ} (hz : ‖z‖ < 1)
    (hz' : ‖1 - (1 - z) ^ 2‖ < 1) :
    heunLocal 2 (α * β) α β γ (α + β - 2 * γ + 1) z =
      ordinaryHypergeometric (α / 2) (β / 2) γ (1 - (1 - z) ^ 2) := by
  set δ := α + β - 2 * γ + 1 with hδ
  set F : ℂ → ℂ := ordinaryHypergeometric (α / 2) (β / 2) γ with hF
  set ψ : ℂ → ℂ := fun u => 1 - (1 - u) ^ 2 with hψ
  set G : ℂ → ℂ := fun u => F (ψ u) with hG
  set D : Set ℂ := {u | ‖u‖ < 1 ∧ ‖ψ u‖ < 1} with hD
  have hψeq : ∀ u, ψ u = u * (2 - u) := fun u => by simp only [hψ]; ring
  have hrad : heunLocalRadius 2 = 1 := by simp [heunLocalRadius]
  have hDopen : IsOpen D :=
    (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt
      (continuous_norm.comp (show Continuous ψ by rw [hψ]; fun_prop)) continuous_const)
  have h0D : (0 : ℂ) ∈ D := ⟨by simp, by simp [hψ]⟩
  have hDconn : IsPreconnected D := by
    have hstar : StarConvex ℝ (0 : ℂ) D := fun y hy s t hs ht hst => by
      have e : s • (0 : ℂ) + t • y = (t : ℂ) * y := by simp [Complex.real_smul]
      rw [e]
      have ht1 : t ≤ 1 := by linarith
      refine ⟨?_, ?_⟩
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht]
        exact (mul_le_of_le_one_left (norm_nonneg _) ht1).trans_lt hy.1
      · show ‖ψ ((t : ℂ) * y)‖ < 1
        rw [hψeq]
        refine (p2h_norm_quad_le ht ht1 hy.1.le).trans_lt ?_
        rw [← hψeq]; exact hy.2
    exact (hstar.isPathConnected h0D).isConnected.isPreconnected
  have hHH := heunLocal_isHeunSolOn (a := 2) (q := α * β) (α := α) (β := β) (δ := δ)
    two_ne_zero hγ
  rw [hrad] at hHH
  have hHl : AnalyticOnNhd ℂ (heunLocal 2 (α * β) α β γ δ) D := fun u hu =>
    hHH.1 u (mem_ball_zero_iff.2 hu.1)
  have hGa : AnalyticOnNhd ℂ G D := fun u hu => by
    have h1 : AnalyticAt ℂ ψ u := by simp only [hψ]; fun_prop
    have h2 : AnalyticAt ℂ F (ψ u) :=
      DLMF.Hypergeometric.analyticAt_ordinaryHypergeometric hu.2
    exact AnalyticAt.comp (g := F) (f := ψ) h2 h1
  have hFsol := hypergeometric_isHeunSolOn_zero (α := α / 2) (β := β / 2) hγ
  have hε : heunEps α β γ δ = γ := by simp only [heunEps, hδ]; ring
  have hfacts : ∀ u ∈ D \ {0}, u ≠ 0 ∧ u - 1 ≠ 0 ∧ u - 2 ≠ 0 ∧ 2 - u ≠ 0 ∧ 1 - u ≠ 0 := by
    rintro u ⟨hu, hu0⟩
    have h1 : ‖u‖ < 1 := hu.1
    have hne : ∀ c : ℂ, 1 ≤ ‖c‖ → u - c ≠ 0 := fun c hc h => by
      rw [sub_eq_zero] at h; rw [h] at h1; linarith
    refine ⟨hu0, hne 1 (by simp), hne 2 (by norm_num), fun h => hne 2 (by norm_num) ?_,
      fun h => hne 1 (by simp) ?_⟩
    · linear_combination -h
    · linear_combination -h
  have hsol : IsHeunSolOn 2 (α * β) α β γ δ (heunEps α β γ δ) G (D \ {0}) := by
    rw [hε]
    refine p1h_isLinearODE2On_comp («φ» := ψ) (φ₁ := fun u => 2 * (1 - u)) (φ₂ := fun _ => -2)
      (hDopen.sdiff isClosed_singleton) (fun u _ => ?_) (fun u _ => ?_) (fun u hu => ?_)
      (fun u hu => ?_) (fun u hu => ?_) hFsol
    · show HasDerivAt (fun x : ℂ => 1 - (1 - x) ^ 2) (2 * (1 - u)) u
      have h := (((hasDerivAt_id u).const_sub (1 : ℂ)).pow 2).const_sub (1 : ℂ)
      exact h.congr_deriv (by simp)
    · show HasDerivAt (fun x : ℂ => 2 * (1 - x)) (-2) u
      exact (((hasDerivAt_id u).const_sub (1 : ℂ)).const_mul (2 : ℂ)).congr_deriv (by simp)
    · obtain ⟨hu, hu0⟩ := hu
      refine ⟨mem_ball_zero_iff.2 hu.2, ?_⟩
      simp only [mem_singleton_iff]
      rw [hψeq]
      refine mul_ne_zero hu0 fun h => ?_
      have : u = 2 := by linear_combination -h
      have h1 := hu.1
      rw [this] at h1; norm_num at h1
    · obtain ⟨h0, h1, h2, h2', h1'⟩ := hfacts u hu
      simp only [heunCoeffP, hψ, hδ]
      have hA : 1 - (1 - u) ^ 2 ≠ 0 := by
        rw [show 1 - (1 - u) ^ 2 = u * (2 - u) by ring]; exact mul_ne_zero h0 h2'
      have hB : 1 - (1 - u) ^ 2 - 1 ≠ 0 := by
        rw [show 1 - (1 - u) ^ 2 - 1 = -((1 - u) ^ 2) by ring]
        exact neg_ne_zero.2 (pow_ne_zero _ h1')
      rw [sub_zero]
      field_simp
      ring
    · obtain ⟨h0, h1, h2, h2', h1'⟩ := hfacts u hu
      simp only [heunCoeffR, hψ]
      have hA : 1 - (1 - u) ^ 2 ≠ 0 := by
        rw [show 1 - (1 - u) ^ 2 = u * (2 - u) by ring]; exact mul_ne_zero h0 h2'
      have hB : 1 - (1 - u) ^ 2 - 1 ≠ 0 := by
        rw [show 1 - (1 - u) ^ 2 - 1 = -((1 - u) ^ 2) by ring]
        exact neg_ne_zero.2 (pow_ne_zero _ h1')
      rw [sub_zero]
      field_simp
      ring
  have hev := eventuallyEq_heunLocal_of_analyticAt two_ne_zero hγ (hDopen.mem_nhds h0D)
    (hGa 0 h0D) hsol
  have hG0 : G 0 = 1 := by simp [hG, hψ, hF, ordinaryHypergeometric_zero]
  rw [hG0] at hev
  have hev' : heunLocal 2 (α * β) α β γ δ =ᶠ[𝓝 0] G := by
    filter_upwards [hev] with u hu
    rw [hu, one_mul]
  exact hHl.eqOn_of_preconnected_of_eventuallyEq hGa hDconn h0D hev' ⟨hz, hz'⟩

/-- DLMF 31.7.3: `Hl(4, αβ; α, β, 1/2, 2(α+β)/3; z) = ₂F₁(α/3, β/3; 1/2; 1 - (1-z)²(1 - z/4))`
where both series converge. -/
@[dlmf 31.7.E3]
theorem heunLocal_four_eq_hypergeometric {z : ℂ} (hz : ‖z‖ < 1)
    (hz' : ‖1 - (1 - z) ^ 2 * (1 - z / 4)‖ < 1) :
    heunLocal 4 (α * β) α β (1 / 2) (2 / 3 * (α + β)) z =
      ordinaryHypergeometric (α / 3) (β / 3) (1 / 2) (1 - (1 - z) ^ 2 * (1 - z / 4)) := by
  have hγ : ∀ n : ℕ, (1 / 2 : ℂ) ≠ -(n : ℂ) := fun n h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h4c : (4 : ℂ) ≠ 0 := by norm_num
  set δ := 2 / 3 * (α + β) with hδ
  set F : ℂ → ℂ := ordinaryHypergeometric (α / 3) (β / 3) (1 / 2) with hF
  set ψ : ℂ → ℂ := fun u => 1 - (1 - u) ^ 2 * (1 - u / 4) with hψ
  set G : ℂ → ℂ := fun u => F (ψ u) with hG
  set D : Set ℂ := {u | ‖u‖ < 1 ∧ ‖ψ u‖ < 1} with hD
  have hψeq : ∀ u, ψ u = u * (3 - u) ^ 2 / 4 := fun u => by simp only [hψ]; ring
  have hrad : heunLocalRadius 4 = 1 := by simp [heunLocalRadius]
  have hDopen : IsOpen D :=
    (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt
      (continuous_norm.comp (show Continuous ψ by rw [hψ]; fun_prop)) continuous_const)
  have h0D : (0 : ℂ) ∈ D := ⟨by simp, by simp [hψ]⟩
  have hDconn : IsPreconnected D := by
    have hstar : StarConvex ℝ (0 : ℂ) D := fun y hy s t hs ht hst => by
      have e : s • (0 : ℂ) + t • y = (t : ℂ) * y := by simp [Complex.real_smul]
      rw [e]
      have ht1 : t ≤ 1 := by linarith
      refine ⟨?_, ?_⟩
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht]
        exact (mul_le_of_le_one_left (norm_nonneg _) ht1).trans_lt hy.1
      · show ‖ψ ((t : ℂ) * y)‖ < 1
        have h2 := hy.2
        rw [hψeq] at h2 ⊢
        rw [norm_div] at h2 ⊢
        exact (div_le_div_of_nonneg_right (p2h_norm_cubic_le ht ht1 hy.1.le)
          (norm_nonneg _)).trans_lt h2
    exact (hstar.isPathConnected h0D).isConnected.isPreconnected
  have hHH := heunLocal_isHeunSolOn (a := 4) (q := α * β) (α := α) (β := β) (δ := δ)
    h4c hγ
  rw [hrad] at hHH
  have hHl : AnalyticOnNhd ℂ (heunLocal 4 (α * β) α β (1 / 2) δ) D := fun u hu =>
    hHH.1 u (mem_ball_zero_iff.2 hu.1)
  have hGa : AnalyticOnNhd ℂ G D := fun u hu => by
    have h1 : AnalyticAt ℂ ψ u := by simp only [hψ]; fun_prop
    have h2 : AnalyticAt ℂ F (ψ u) :=
      DLMF.Hypergeometric.analyticAt_ordinaryHypergeometric hu.2
    exact AnalyticAt.comp (g := F) (f := ψ) h2 h1
  have hFsol := hypergeometric_isHeunSolOn_zero (α := α / 3) (β := β / 3) hγ
  have hε : heunEps α β (1 / 2) δ = (α + β) / 3 + 1 / 2 := by simp only [heunEps, hδ]; ring
  have hfacts : ∀ u ∈ D \ {0}, u ≠ 0 ∧ 1 - u ≠ 0 ∧ 3 - u ≠ 0 ∧ 4 - u ≠ 0 ∧ u - 1 ≠ 0 ∧
      u - 4 ≠ 0 := by
    rintro u ⟨hu, hu0⟩
    have h1 : ‖u‖ < 1 := hu.1
    have hne : ∀ c : ℂ, 1 ≤ ‖c‖ → u - c ≠ 0 := fun c hc h => by
      rw [sub_eq_zero] at h; rw [h] at h1; linarith
    refine ⟨hu0, fun h => hne 1 (by simp) ?_, fun h => hne 3 (by norm_num) ?_,
      fun h => hne 4 (by norm_num) ?_, hne 1 (by simp), hne 4 (by norm_num)⟩
    · linear_combination -h
    · linear_combination -h
    · linear_combination -h
  have hsol : IsHeunSolOn 4 (α * β) α β (1 / 2) δ (heunEps α β (1 / 2) δ) G (D \ {0}) := by
    rw [hε]
    refine p1h_isLinearODE2On_comp («φ» := ψ) (φ₁ := fun u => 3 / 4 * (1 - u) * (3 - u))
      (φ₂ := fun u => -3 + 3 / 2 * u)
      (hDopen.sdiff isClosed_singleton) (fun u _ => ?_) (fun u _ => ?_) (fun u hu => ?_)
      (fun u hu => ?_) (fun u hu => ?_) hFsol
    · show HasDerivAt (fun x : ℂ => 1 - (1 - x) ^ 2 * (1 - x / 4)) (3 / 4 * (1 - u) * (3 - u)) u
      have h := ((((hasDerivAt_id u).const_sub (1 : ℂ)).pow 2).mul
        (((hasDerivAt_id u).div_const (4 : ℂ)).const_sub (1 : ℂ))).const_sub (1 : ℂ)
      exact h.congr_deriv (by simp; ring)
    · show HasDerivAt (fun x : ℂ => 3 / 4 * (1 - x) * (3 - x)) (-3 + 3 / 2 * u) u
      have h := ((((hasDerivAt_id u).const_sub (1 : ℂ)).const_mul (3 / 4 : ℂ)).mul
        ((hasDerivAt_id u).const_sub (3 : ℂ)))
      exact h.congr_deriv (by simp; ring)
    · obtain ⟨hu, hu0⟩ := hu
      obtain ⟨h0, h1, h3, h4, -, -⟩ := hfacts u ⟨hu, hu0⟩
      refine ⟨mem_ball_zero_iff.2 hu.2, ?_⟩
      simp only [mem_singleton_iff]
      rw [hψeq]
      exact div_ne_zero (mul_ne_zero h0 (pow_ne_zero _ h3)) h4c
    · obtain ⟨h0, h1, h3, h4, h1', h4'⟩ := hfacts u hu
      simp only [heunCoeffP, hψ, hδ]
      rw [show 1 - (1 - u) ^ 2 * (1 - u / 4) = u * (3 - u) ^ 2 / 4 by ring, sub_zero,
        show u * (3 - u) ^ 2 / 4 - 1 = -((1 - u) ^ 2 * (4 - u) / 4) by ring]
      field_simp
      ring
    · obtain ⟨h0, h1, h3, h4, h1', h4'⟩ := hfacts u hu
      simp only [heunCoeffR, hψ]
      rw [show 1 - (1 - u) ^ 2 * (1 - u / 4) = u * (3 - u) ^ 2 / 4 by ring, sub_zero,
        show u * (3 - u) ^ 2 / 4 - 1 = -((1 - u) ^ 2 * (4 - u) / 4) by ring]
      field_simp
      ring
  have hev := eventuallyEq_heunLocal_of_analyticAt h4c hγ (hDopen.mem_nhds h0D)
    (hGa 0 h0D) hsol
  have hG0 : G 0 = 1 := by simp [hG, hψ, hF, ordinaryHypergeometric_zero]
  rw [hG0] at hev
  have hev' : heunLocal 4 (α * β) α β (1 / 2) δ =ᶠ[𝓝 0] G := by
    filter_upwards [hev] with u hu
    rw [hu, one_mul]
  exact hHl.eqOn_of_preconnected_of_eventuallyEq hGa hDconn h0D hev' ⟨hz, hz'⟩

/-- DLMF 31.7.4: with `a = 1/2 + i√3/2`,
`Hl(a, αβ(1/2 + i√3/6); α, β, (α+β+1)/3, (α+β+1)/3; z)
= ₂F₁(α/3, β/3; (α+β+1)/3; 1 - (1 - (3/2 - i√3/2) z)³)` where both series converge and
`(α + β + 1)/3 ∉ {0, -1, …}`. -/
@[dlmf 31.7.E4]
theorem heunLocal_cubic_eq_hypergeometric
    (hγ : ∀ n : ℕ, (α + β + 1) / 3 ≠ -(n : ℂ)) {z : ℂ} (hz : ‖z‖ < 1)
    (hz' : ‖1 - (1 - (3 / 2 - I * Real.sqrt 3 / 2) * z) ^ 3‖ < 1) :
    heunLocal (1 / 2 + I * Real.sqrt 3 / 2) (α * β * (1 / 2 + I * Real.sqrt 3 / 6)) α β
        ((α + β + 1) / 3) ((α + β + 1) / 3) z =
      ordinaryHypergeometric (α / 3) (β / 3) ((α + β + 1) / 3)
        (1 - (1 - (3 / 2 - I * Real.sqrt 3 / 2) * z) ^ 3) := by
  sorry

/-! ### Expansions in series of hypergeometric functions (§31.11) -/

/-- DLMF 31.11.3 with the Type I choices 31.11.10 (`λ = α, μ = β - ε`) and 31.11.11
(`λ = β, μ = α - ε`): under Fuchs's relation `λ + μ = γ + δ - 1 = α + β - ε`. -/
@[dlmf 31.11.E3, dlmf 31.11.E10, dlmf 31.11.E11]
theorem heunHyp_typeI_add (hF : α + β + 1 = γ + δ + ε) :
    (α + (β - ε) = γ + δ - 1 ∧ α + (β - ε) = α + β - ε) ∧
      (β + (α - ε) = γ + δ - 1 ∧ β + (α - ε) = α + β - ε) := by
  refine ⟨⟨?_, by ring⟩, ⟨?_, by ring⟩⟩ <;> linear_combination hF

/-- DLMF 31.11.3 with the Type II choices 31.11.14–31.11.17: each pair satisfies
`λ + μ = γ + δ - 1`. -/
@[dlmf 31.11.E3, dlmf 31.11.E14, dlmf 31.11.E15, dlmf 31.11.E16, dlmf 31.11.E17]
theorem heunHyp_typeII_add :
    (γ + δ - 1) + 0 = γ + δ - 1 ∧ γ + (δ - 1) = γ + δ - 1 ∧ δ + (γ - 1) = γ + δ - 1 ∧
      1 + (γ + δ - 2) = γ + δ - 1 := by
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- DLMF 31.11.9 for Type I (§31.11(iii)): with `λ = α` or `λ = β` the coefficient `M_{-1}`
vanishes, so `M_{-1}P_{-1} = 0`. -/
@[dlmf 31.11.E9, dlmf 31.11.iii]
theorem heunHypM_neg_one_eq_zero (μ : ℂ) :
    heunHypM α β γ α μ (-1) = 0 ∧ heunHypM α β γ β μ (-1) = 0 := by
  constructor <;> simp [heunHypM]

/-- `₂F₁(a, b; 0; x) = 1` with Mathlib's junk convention: every term past the constant one
divides by `(0)_n = 0`, which is taken to be `0`. -/
theorem p2h_ordinaryHypergeometric_c_zero (a b x : ℂ) : ₂F₁ a b (0 : ℂ) x = 1 := by
  rw [ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul]
  have h : (fun n : ℕ =>
      (n !⁻¹ : ℂ) * (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b *
        ((ascPochhammer ℂ n).eval 0)⁻¹ * x ^ n) =
      fun n => if n = 0 then 1 else 0 := by
    ext n
    cases n with
    | zero => simp
    | succ n => simp
  rw [h, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

/-- The normalized Riemann operator depends on the exponents at `∞` only through their
product. -/
theorem p2h_riemannNormalOperator_swap (a₁ a₂ b₁ b₂ c₁ c₂ : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    DLMF.Hypergeometric.riemannNormalOperator a₁ a₂ b₁ b₂ c₁ c₂ f z =
      DLMF.Hypergeometric.riemannNormalOperator a₁ a₂ b₁ b₂ c₂ c₁ f z := by
  simp only [DLMF.Hypergeometric.riemannNormalOperator, mul_comm c₁ c₂]

/-- The normalized Riemann operator is homogeneous: `R(C f) = C R(f)`. -/
theorem p2h_riemannNormalOperator_const_mul (a₁ a₂ b₁ b₂ c₁ c₂ C : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    DLMF.Hypergeometric.riemannNormalOperator a₁ a₂ b₁ b₂ c₁ c₂ (fun w => C * f w) z =
      C * DLMF.Hypergeometric.riemannNormalOperator a₁ a₂ b₁ b₂ c₁ c₂ f z := by
  simp only [DLMF.Hypergeometric.riemannNormalOperator, iteratedDeriv_const_mul_field,
    deriv_const_mul_field']
  ring

/-- A Gauss solution `infinityFirst a b c` at `∞` solves the normalized Riemann equation with
exponents `0, 1 - c; 0, c - a - b; a, b`, when `a - b + 1 ∉ {0, -1, …}`. -/
theorem p2h_riemann_infinityFirst {a b c z : ℂ} (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (hz : 1 < ‖z‖) (hs : z ∈ slitPlane) :
    DLMF.Hypergeometric.riemannNormalOperator 0 (1 - c) 0 (c - a - b) a b
      (DLMF.Hypergeometric.infinityFirst a b c) z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hs
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz
  have hg := DLMF.Hypergeometric.riemannNormalOperator_gauss a b c
    (DLMF.Hypergeometric.infinityFirst a b c) hz0 hz1
  rw [DLMF.Hypergeometric.infinity_first_ode hc hz hs] at hg
  have h1 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz1)
  rcases mul_eq_zero.1 hg with h | h
  · exact absurd h (mul_ne_zero hz0 h1)
  · exact h

/-- DLMF 31.11.2 with 31.11.3_1 and 31.11.3_2: for `λ + μ = γ + δ - 1`, `P_j^5` and `P_j^6`
belong to the P-symbol `P{0, 1, ∞; 0, 0, λ+j; 1-γ, 1-δ, μ-j; z}`, i.e. solve Riemann's equation
with these exponents (`riemannNormalOperator`), for `|z| > 1` off the branch cuts.

Correction (2026-10-26): the hypotheses `h5`, `h6` that the third Gauss parameters
`1 + λ - μ + 2j` and `1 - λ + μ - 2j` of `P_j^5`, `P_j^6` are not in `{0, -1, -2, …}` were
added. Without them Mathlib's `₂F₁` takes its junk value there and the statement fails:
`p2h_not_heunHypP5_P6_riemann_degenerate` (`γ = 1, δ = -1, λ = -1, μ = 0, j = 0, z = 2`, where
`P_0^5(z) = z`). -/
@[dlmf 31.11.E2, dlmf 31.11.E3_1, dlmf 31.11.E3_2]
theorem heunHypP5_P6_riemann {lam μ : ℂ} (h : lam + μ = γ + δ - 1) (j : ℕ)
    (h5 : ∀ k : ℕ, 1 + lam - μ + 2 * j ≠ -(k : ℂ))
    (h6 : ∀ k : ℕ, 1 - lam + μ - 2 * j ≠ -(k : ℂ)) {z : ℂ}
    (hz : 1 < ‖z‖) (hz' : z ∈ slitPlane) :
    DLMF.Hypergeometric.riemannNormalOperator 0 (1 - γ) 0 (1 - δ) (lam + j) (μ - j)
        (heunHypP5 γ lam μ j) z = 0 ∧
      DLMF.Hypergeometric.riemannNormalOperator 0 (1 - γ) 0 (1 - δ) (lam + j) (μ - j)
        (heunHypP6 γ lam μ j) z = 0 := by
  constructor
  · have hP : heunHypP5 γ lam μ j = fun w =>
        ((ascPochhammer ℂ j).eval lam * (ascPochhammer ℂ j).eval (1 - γ + lam) /
          (ascPochhammer ℂ (2 * j)).eval (1 + lam - μ)) *
        DLMF.Hypergeometric.infinityFirst (lam + j) (μ - j) γ w := by
      funext w
      simp only [heunHypP5, DLMF.Hypergeometric.infinityFirst]
      rw [show -lam - (j : ℂ) = -(lam + j) by ring,
        show 1 - γ + lam + (j : ℂ) = lam + j - γ + 1 by ring,
        show 1 + lam - μ + 2 * (j : ℂ) = lam + j - (μ - j) + 1 by ring]
      ring
    have hδ : 1 - δ = γ - (lam + j) - (μ - j) := by linear_combination h
    rw [hP, p2h_riemannNormalOperator_const_mul, hδ,
      p2h_riemann_infinityFirst (fun k => by
        rw [show lam + (j : ℂ) - (μ - j) + 1 = 1 + lam - μ + 2 * j by ring]; exact h5 k)
        hz hz', mul_zero]
  · have hP : heunHypP6 γ lam μ j = fun w =>
        ((ascPochhammer ℂ (2 * j)).eval (lam - μ) /
          ((ascPochhammer ℂ j).eval (1 - μ) * (ascPochhammer ℂ j).eval (γ - μ))) *
        DLMF.Hypergeometric.infinityFirst (μ - j) (lam + j) γ w := by
      funext w
      simp only [heunHypP6, DLMF.Hypergeometric.infinityFirst]
      rw [show -μ + (j : ℂ) = -(μ - j) by ring,
        show 1 - γ + μ - (j : ℂ) = μ - j - γ + 1 by ring,
        show 1 - lam + μ - 2 * (j : ℂ) = μ - j - (lam + j) + 1 by ring]
      ring
    have hδ : 1 - δ = γ - (μ - j) - (lam + j) := by linear_combination h
    rw [hP, p2h_riemannNormalOperator_const_mul, p2h_riemannNormalOperator_swap, hδ,
      p2h_riemann_infinityFirst (fun k => by
        rw [show μ - (j : ℂ) - (lam + j) + 1 = 1 - lam + μ - 2 * j by ring]; exact h6 k)
        hz hz', mul_zero]

/-- Without `h5`, `h6` the statement of DLMF 31.11.2 (`heunHypP5_P6_riemann`) fails in the
degenerate case `γ = 1, δ = -1, λ = -1, μ = 0, j = 0`: the third Gauss parameter of `P_0^5` is
`0`, Mathlib's `₂F₁(-1, -1; 0; 1/z)` is the junk value `1`, so `P_0^5(z) = z`, and the Riemann
operator at `z = 2` is `-1/2 ≠ 0`. -/
theorem p2h_not_heunHypP5_P6_riemann_degenerate :
    ¬ ∀ (γ δ lam μ : ℂ) (j : ℕ) (z : ℂ), lam + μ = γ + δ - 1 → 1 < ‖z‖ → z ∈ slitPlane →
      DLMF.Hypergeometric.riemannNormalOperator 0 (1 - γ) 0 (1 - δ) (lam + j) (μ - j)
          (heunHypP5 γ lam μ j) z = 0 ∧
        DLMF.Hypergeometric.riemannNormalOperator 0 (1 - γ) 0 (1 - δ) (lam + j) (μ - j)
          (heunHypP6 γ lam μ j) z = 0 := by
  intro H
  have hP : heunHypP5 1 (-1) 0 0 = fun w => w := by
    funext w
    simp [heunHypP5, p2h_ordinaryHypergeometric_c_zero]
  have h2 := (H 1 (-1) (-1) 0 0 2 (by norm_num) (by simp) (by simp)).1
  rw [hP] at h2
  simp only [DLMF.Hypergeometric.riemannNormalOperator, iteratedDeriv_succ, iteratedDeriv_zero,
    deriv_id'', deriv_const] at h2
  norm_num at h2

/-- DLMF 31.11.1, 31.11.4–31.11.5, 31.11.10 and 31.11.12 (Type I): the Fuchs–Frobenius solution
31.3.10 at `∞` with exponent `α` is `∑_j c_j P_j^5(z)` with `λ = α`, `μ = β - ε`, `c₀ = 1` and
the recurrence 31.11.4–31.11.5, for `z` outside the ellipse `𝓔` with foci `0, 1` through `a`
(`|z| + |z - 1| > |a| + |a - 1|`), here also with `|z| > max(1, |a|)` so that 31.3.10 is given
by its series. -/
@[dlmf 31.11.E1, dlmf 31.11.E4, dlmf 31.11.E5, dlmf 31.11.E10, dlmf 31.11.E12, dlmf 31.11.iii]
theorem hasSum_heunHyp_typeI (ha : a ≠ 0) (hF : α + β + 1 = γ + δ + ε) {z : ℂ}
    (hz : ‖1 / z‖ < heunLocalRadius (1 / a)) (hz' : z ∈ slitPlane)
    (hE : ‖a‖ + ‖a - 1‖ < ‖z‖ + ‖z - 1‖) :
    HasSum (fun j => heunHypCoeff a q α β γ α (β - ε) j * heunHypP5 γ α (β - ε) j z)
      (z ^ (-α) * heunLocal (1 / a) (q / a - α * (β - ε) - α / a * (β - δ)) α (α - γ + 1)
        (α - β + 1) δ (1 / z)) := by
  sorry

/-- DLMF 31.11.1 with 31.11.11 (Type I, second choice): the solution 31.3.11 with exponent `β`
at `∞` is `∑_j c_j P_j^5(z)` with `λ = β`, `μ = α - ε`. -/
@[dlmf 31.11.E1, dlmf 31.11.E11]
theorem hasSum_heunHyp_typeI' (ha : a ≠ 0) (hF : α + β + 1 = γ + δ + ε) {z : ℂ}
    (hz : ‖1 / z‖ < heunLocalRadius (1 / a)) (hz' : z ∈ slitPlane)
    (hE : ‖a‖ + ‖a - 1‖ < ‖z‖ + ‖z - 1‖) :
    HasSum (fun j => heunHypCoeff a q α β γ β (α - ε) j * heunHypP5 γ β (α - ε) j z)
      (z ^ (-β) * heunLocal (1 / a) (q / a - β * (α - ε) - β / a * (α - δ)) β (β - γ + 1)
        (β - α + 1) δ (1 / z)) := by
  sorry

/-- DLMF 31.11.13: if the Fuchs–Frobenius solution 31.3.10 (exponent `α` at `∞`) continues
analytically to a neighbourhood of `z = a` (a Heun function for the pair `(a, ∞)`), then the
accessory parameter `q` is a root of the continued fraction
`L₀/M₀ - (K₁/M₁)/(L₁/M₁ - (K₂/M₂)/(L₂/M₂ - ⋯)) = 0` (with `λ = α`, `μ = β - ε`): the
approximants tend to `0`. Hypotheses: no `K_j`, `M_j` and no coefficient `c_j` vanishes. -/
@[dlmf 31.11.E13, dlmf 31.11.iii]
theorem tendsto_heunHypCFApprox (ha : a ≠ 0) (hF : α + β + 1 = γ + δ + ε)
    (hK : ∀ j : ℕ, heunHypK α β γ α (β - ε) j ≠ 0) (hM : ∀ j : ℕ, heunHypM α β γ α (β - ε) j ≠ 0)
    (hc : ∀ j, heunHypCoeff a q α β γ α (β - ε) j ≠ 0)
    (hq : ∃ (U : Set ℂ) (f : ℂ → ℂ) (R : ℝ), IsOpen U ∧ IsPreconnected U ∧ a ∈ U ∧
      {z | R < ‖z‖ ∧ z ∈ slitPlane} ⊆ U ∧ AnalyticOnNhd ℂ f U ∧
      ∀ z, R < ‖z‖ → z ∈ slitPlane → f z = z ^ (-α) *
        heunLocal (1 / a) (q / a - α * (β - ε) - α / a * (β - δ)) α (α - γ + 1) (α - β + 1) δ
          (1 / z)) :
    Tendsto (heunHypCFApprox a q α β γ α (β - ε)) atTop (𝓝 0) := by
  sorry

/-- DLMF §31.11(iv) with 31.11.14 (Type II): for `λ = γ + δ - 1`, `μ = 0` each `P_j^6` is a
polynomial of degree at most `j` (a multiple of the Jacobi polynomial
`P_j^{(γ-1, δ-1)}(1 - 2z)`). -/
@[dlmf 31.11.iv, dlmf 31.11.E14]
theorem heunHypP6_typeII_polynomial (j : ℕ) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ j ∧
      ∀ z : ℂ, z ≠ 0 → heunHypP6 γ (γ + δ - 1) 0 j z = p.eval z := by
  set K : ℂ := (ascPochhammer ℂ (2 * j)).eval (γ + δ - 1 - 0) /
      ((ascPochhammer ℂ j).eval (1 - 0) * (ascPochhammer ℂ j).eval (γ - 0)) with hK
  set b : ℂ := 1 - γ + 0 - j
  set c : ℂ := 1 - (γ + δ - 1) + 0 - 2 * j
  let t : ℕ → ℂ := fun m => (m.factorial : ℂ)⁻¹ * (ascPochhammer ℂ m).eval (-(j : ℂ)) *
    (ascPochhammer ℂ m).eval b * ((ascPochhammer ℂ m).eval c)⁻¹
  refine ⟨∑ m ∈ Finset.range (j + 1), Polynomial.C (K * t m) * Polynomial.X ^ (j - m), ?_,
    fun z hz => ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m _ => ?_
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [Polynomial.natDegree_X_pow]
    omega
  · unfold heunHypP6
    rw [show (0 : ℂ) - j = -(j : ℂ) by ring,
      Carlson.TwoVariable.ordinaryHypergeometric_neg_natCast, neg_zero, zero_add,
      Complex.cpow_natCast, Polynomial.eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : m ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [pow_sub₀ _ hz hm', one_div, inv_pow]
    simp only [t, b, c, hK]
    ring

/-- DLMF §31.11(iv) with 31.11.14 (Type II): every `(0,1)`-Heun function has an expansion
`∑_j c_j P_j^6(z)` (`λ = γ + δ - 1`, `μ = 0`), convergent inside the ellipse `𝓔` with foci
`0, 1` through `a`; the coefficients are the solution of 31.11.4–31.11.5 with `c₀ = 1`, and the
sum is a constant multiple of the Heun function. Stated where `(0,1)Hf` is defined
(`|z| < |a|`). -/
@[dlmf 31.11.iv, dlmf 31.11.E14]
theorem hasSum_heunHyp_typeII (ha : 1 < ‖a‖) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ))
    (hδ : ∀ n : ℤ, δ ≠ n) (hq : IsHeunEigenvalue01 a q α β γ δ) :
    ∃ C : ℂ, ∀ z : ℂ, ‖z‖ + ‖z - 1‖ < ‖a‖ + ‖a - 1‖ → ‖z‖ < ‖a‖ →
      HasSum (fun j => heunHypCoeff a q α β γ (γ + δ - 1) 0 j * heunHypP6 γ (γ + δ - 1) 0 j z)
        (C * heunFunction01 a q α β γ δ z) := by
  sorry

end DLMF.Heun
