/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic
public import DLMF.Hypergeometric.Riemann
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
  quadratic and cubic reductions 31.7.2–31.7.4 are admitted on the disks where both series
  converge. The classification remark (other reductions exist only for finitely many `(a, p)`,
  `q = αβp`; Maier 2005) and the reference to Joyce (1994) are not acquired.
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
  sorry

/-- DLMF 31.7.2: `Hl(2, αβ; α, β, γ, α + β - 2γ + 1; z) = ₂F₁(α/2, β/2; γ; 1 - (1-z)²)` where
both series converge. -/
@[dlmf 31.7.E2]
theorem heunLocal_two_eq_hypergeometric (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ)) {z : ℂ} (hz : ‖z‖ < 1)
    (hz' : ‖1 - (1 - z) ^ 2‖ < 1) :
    heunLocal 2 (α * β) α β γ (α + β - 2 * γ + 1) z =
      ordinaryHypergeometric (α / 2) (β / 2) γ (1 - (1 - z) ^ 2) := by
  sorry

/-- DLMF 31.7.3: `Hl(4, αβ; α, β, 1/2, 2(α+β)/3; z) = ₂F₁(α/3, β/3; 1/2; 1 - (1-z)²(1 - z/4))`
where both series converge. -/
@[dlmf 31.7.E3]
theorem heunLocal_four_eq_hypergeometric {z : ℂ} (hz : ‖z‖ < 1)
    (hz' : ‖1 - (1 - z) ^ 2 * (1 - z / 4)‖ < 1) :
    heunLocal 4 (α * β) α β (1 / 2) (2 / 3 * (α + β)) z =
      ordinaryHypergeometric (α / 3) (β / 3) (1 / 2) (1 - (1 - z) ^ 2 * (1 - z / 4)) := by
  sorry

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

/-- DLMF 31.11.2 with 31.11.3_1 and 31.11.3_2: for `λ + μ = γ + δ - 1`, `P_j^5` and `P_j^6`
belong to the P-symbol `P{0, 1, ∞; 0, 0, λ+j; 1-γ, 1-δ, μ-j; z}`, i.e. solve Riemann's equation
with these exponents (`riemannNormalOperator`), for `|z| > 1` off the branch cuts. -/
@[dlmf 31.11.E2, dlmf 31.11.E3_1, dlmf 31.11.E3_2]
theorem heunHypP5_P6_riemann {lam μ : ℂ} (h : lam + μ = γ + δ - 1) (j : ℕ) {z : ℂ}
    (hz : 1 < ‖z‖) (hz' : z ∈ slitPlane) :
    DLMF.Hypergeometric.riemannNormalOperator 0 (1 - γ) 0 (1 - δ) (lam + j) (μ - j)
        (heunHypP5 γ lam μ j) z = 0 ∧
      DLMF.Hypergeometric.riemannNormalOperator 0 (1 - γ) 0 (1 - δ) (lam + j) (μ - j)
        (heunHypP6 γ lam μ j) z = 0 := by
  sorry

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
  sorry

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
