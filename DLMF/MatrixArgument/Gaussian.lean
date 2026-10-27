/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.MatrixArgument.Basic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Gaussian hypergeometric function of matrix argument (DLMF §35.7)

`hyp2F1 a b c T` (35.7.1), the Jacobi form `jacobiP γ δ ν T` (35.7.2) and the operators
`gaussPDEOperator` of 35.7.9 are defined in `DLMF.MatrixArgument.Basic`. This file proves the
series form 35.7.1 and states 35.7.3, 35.7.5–35.7.9 and the uniqueness theorem of §35.7(iii)
(admitted). The function `₂F₁` of matrix argument is the series 35.7.1, defined for `‖T‖ < 1`
(and at `T = I` where it converges); formulas whose argument leaves that region are stated on
the part of their domain where all arguments stay in it:

* 35.7.3 (`m = 2`) is stated for `0 ≤ t₁, t₂ < 1`, where `t₁ + t₂ - t₁t₂ ∈ [0, 1)`;
* the last two forms of 35.7.6 (argument `-T(I - T)⁻¹`) are stated for `0 < T < I/2`;
* 35.7.4 (argument `I - cT⁻¹`, `c → ∞`) is not formalized: it needs the analytic continuation of
  `₂F₁` of matrix argument outside `‖T‖ < 1`, which is not defined here.

**Correction of 35.7.8.** DLMF requires `½(j+1) - a ∈ ℕ` for some `j = 1, …, m`. The formula
holds for `j = 1`, i.e. `a ∈ {0, -1, -2, …}` (the terminating case), and fails otherwise
(for `m = 2`, `a = 1/2` or `a = -1/2`, `b = 0.4`, `c = 2.7`, `T = diag(0.3, 0.65)`:
`1.0896…` against `-3.7418…`, and `0.9236…` against `0.2471…`).
§35.7(iv) cites references only.
-/

@[expose] public noncomputable section

open MeasureTheory Matrix Finset Filter
open scoped Nat MatrixOrder Topology

namespace DLMF.MatrixArgument

/-- DLMF 35.7.1: `₂F₁(a, b; c; T) = ∑_{k=0}^∞ (1/k!) ∑_{|κ|=k} [a]_κ [b]_κ / [c]_κ Z_κ(T)`. -/
@[dlmf 35.7.E1]
theorem hyp2F1_eq_tsum {m : ℕ} (a b c : ℂ) (T : Matrix (Fin m) (Fin m) ℝ) :
    hyp2F1 a b c T = ∑' k : ℕ, (1 / (k ! : ℂ)) * ∑ κ ∈ partitions m k,
      partitionalShiftedFactorial a κ * partitionalShiftedFactorial b κ /
        partitionalShiftedFactorial c κ * (zonalPolynomial κ T : ℂ) := by
  simp [hyp2F1, hypergeometricPFQ, Fin.prod_univ_two]

/-- DLMF 35.7.3 (case `m = 2`):
`₂F₁(a, b; c; diag(t₁, t₂)) = ∑_k (a)_k (c-a)_k (b)_k (c-b)_k / (k! (c)_{2k} (c - ½)_k)
  (t₁t₂)^k ₂F₁(a + k, b + k; c + 2k; t₁ + t₂ - t₁t₂)`,
with the classical `₂F₁` (Mathlib's `ordinaryHypergeometric`), for `0 ≤ t₁, t₂ < 1` and
`Γ₂(c) ≠ 0`. -/
@[dlmf 35.7.E3]
theorem hyp2F1_diagonal_two (a b c : ℂ) (hc : multivariateGamma 2 c ≠ 0) {t₁ t₂ : ℝ}
    (h₁ : 0 ≤ t₁) (h₁' : t₁ < 1) (h₂ : 0 ≤ t₂) (h₂' : t₂ < 1) :
    hyp2F1 a b c (Matrix.diagonal ![t₁, t₂]) = ∑' k : ℕ,
      (ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval (c - a) *
        (ascPochhammer ℂ k).eval b * (ascPochhammer ℂ k).eval (c - b) /
        ((k ! : ℂ) * (ascPochhammer ℂ (2 * k)).eval c * (ascPochhammer ℂ k).eval (c - 1 / 2)) *
        ((t₁ * t₂ : ℝ) : ℂ) ^ k *
        ordinaryHypergeometric (a + k) (b + k) (c + 2 * k) ((t₁ + t₂ - t₁ * t₂ : ℝ) : ℂ) := by
  sorry

/-- DLMF 35.7.5: for `ℜa, ℜ(c - a) > (m-1)/2` and `0 < T < I`,
`₂F₁(a, b; c; T) = B_m(a, c - a)⁻¹ ∫_{0<X<I} |X|^{a-(m+1)/2} |I - X|^{c-a-(m+1)/2}
  |I - TX|^{-b} dX`, stated as: the integral converges and equals `B_m(a, c - a) ₂F₁(a, b; c; T)`.
-/
@[dlmf 35.7.E5]
theorem hasIntegralOn_hyp2F1 {m : ℕ} {a c : ℂ} (b : ℂ) (ha : ((m : ℝ) - 1) / 2 < a.re)
    (hca : ((m : ℝ) - 1) / 2 < (c - a).re) {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.PosDef)
    (hT1 : (1 - T).PosDef) :
    HasIntegralOn (m := m) (matrixInterval 0 1)
      (fun X => ((X.det : ℂ) ^ (a - ((m : ℂ) + 1) / 2)) *
        (((1 - X).det : ℂ) ^ (c - a - ((m : ℂ) + 1) / 2)) * (((1 - T * X).det : ℂ) ^ (-b)))
      (multivariateBeta m a (c - a) * hyp2F1 a b c T) := by
  sorry

/-- DLMF 35.7.6 (Euler transformation, first equality):
`₂F₁(a, b; c; T) = |I - T|^{c-a-b} ₂F₁(c - a, c - b; c; T)` for `0 < T < I`, `Γ_m(c) ≠ 0`. -/
@[dlmf 35.7.E6]
theorem hyp2F1_euler {m : ℕ} (a b : ℂ) {c : ℂ} (hc : multivariateGamma m c ≠ 0)
    {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.PosDef) (hT1 : (1 - T).PosDef) :
    hyp2F1 a b c T = (((1 - T).det : ℝ) : ℂ) ^ (c - a - b) * hyp2F1 (c - a) (c - b) c T := by
  sorry

/-- DLMF 35.7.6 (Pfaff transformations, second and third equalities):
`₂F₁(a, b; c; T) = |I - T|^{-a} ₂F₁(a, c - b; c; -T(I - T)⁻¹)
  = |I - T|^{-b} ₂F₁(c - a, b; c; -T(I - T)⁻¹)`, stated for `0 < T < I/2`, where
`‖T(I - T)⁻¹‖ < 1`, and `Γ_m(c) ≠ 0`. -/
@[dlmf 35.7.E6]
theorem hyp2F1_pfaff {m : ℕ} (a b : ℂ) {c : ℂ} (hc : multivariateGamma m c ≠ 0)
    {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.PosDef) (hT1 : (1 - (2 : ℝ) • T).PosDef) :
    hyp2F1 a b c T = (((1 - T).det : ℝ) : ℂ) ^ (-a) * hyp2F1 a (c - b) c (-(T * (1 - T)⁻¹)) ∧
      hyp2F1 a b c T = (((1 - T).det : ℝ) : ℂ) ^ (-b) * hyp2F1 (c - a) b c (-(T * (1 - T)⁻¹)) := by
  sorry

/-- DLMF 35.7.7 (Gauss formula): `₂F₁(a, b; c; I) = Γ_m(c) Γ_m(c - a - b) / (Γ_m(c - a) Γ_m(c - b))`
for `ℜc, ℜ(c - a - b) > (m-1)/2`. -/
@[dlmf 35.7.E7]
theorem hyp2F1_one {m : ℕ} {a b c : ℂ} (hc : ((m : ℝ) - 1) / 2 < c.re)
    (hcab : ((m : ℝ) - 1) / 2 < (c - a - b).re) :
    hyp2F1 a b c (1 : Matrix (Fin m) (Fin m) ℝ) =
      multivariateGamma m c * multivariateGamma m (c - a - b) /
        (multivariateGamma m (c - a) * multivariateGamma m (c - b)) := by
  sorry

/-- DLMF 35.7.8 (reflection formula, **corrected**): for `0 < T < I`, `a ∈ {0, -1, -2, …}`
(DLMF: `½(j+1) - a ∈ ℕ` for some `j`; only `j = 1` is correct), and `c`, `a + b - c + (m+1)/2`
regular (DLMF: `½(j+1) - c ∉ ℕ` and `c - a - b - ½(m-j) ∉ ℕ` for all `j`),
`₂F₁(a, b; c; T) = Γ_m(c) Γ_m(c - a - b) / (Γ_m(c - a) Γ_m(c - b))
  ₂F₁(a, b; a + b - c + (m+1)/2; I - T)`. -/
@[dlmf 35.7.E8 "corrected: a must be a nonpositive integer (j = 1)"]
theorem hyp2F1_reflection {m : ℕ} {a : ℂ} (b : ℂ) {c : ℂ} {n : ℕ} (ha : a = -n)
    (hc : multivariateGamma m c ≠ 0)
    (hc' : multivariateGamma m (a + b - c + ((m : ℂ) + 1) / 2) ≠ 0)
    {T : Matrix (Fin m) (Fin m) ℝ} (hT : T.PosDef) (hT1 : (1 - T).PosDef) :
    hyp2F1 a b c T = multivariateGamma m c * multivariateGamma m (c - a - b) /
        (multivariateGamma m (c - a) * multivariateGamma m (c - b)) *
      hyp2F1 a b (a + b - c + ((m : ℂ) + 1) / 2) (1 - T) := by
  sorry

/-- DLMF 35.7.9: the function `F(t) = ₂F₁(a, b; c; diag(t₁, …, t_m))` of the eigenvalues is
real-analytic on `|t_k| < 1` and satisfies each partial differential equation 35.7.9
(`gaussPDEOperator a b c F j t = 0`) at every such `t` with pairwise distinct entries, when
`Γ_m(c) ≠ 0`. -/
@[dlmf 35.7.E9]
theorem hyp2F1_gaussPDE {m : ℕ} (a b : ℂ) {c : ℂ} (hc : multivariateGamma m c ≠ 0) :
    AnalyticOnNhd ℝ (fun t : Fin m → ℝ => hyp2F1 a b c (Matrix.diagonal t))
        {t | ∀ k, |t k| < 1} ∧
      ∀ t : Fin m → ℝ, (∀ k, |t k| < 1) → Function.Injective t → ∀ j,
        gaussPDEOperator a b c (fun t : Fin m → ℝ => hyp2F1 a b c (Matrix.diagonal t)) j t = 0 := by
  sorry

/-- DLMF §35.7(iii) (uniqueness): a function `f` of the eigenvalues that is (a) symmetric,
(b) analytic in a neighborhood `|t_k| < ε` of `0` (`0 < ε ≤ 1`) and (c) satisfies `f(0) = 1`,
and solves each equation 35.7.9 at the points `0 < t_k < ε` with distinct entries, is
`₂F₁(a, b; c; diag(t))` there. Regularity `Γ_m(c) ≠ 0` is made explicit. -/
@[dlmf 35.7.iii]
theorem eq_hyp2F1_of_gaussPDE {m : ℕ} (a b : ℂ) {c : ℂ} (hc : multivariateGamma m c ≠ 0)
    (f : (Fin m → ℝ) → ℂ) (hsymm : ∀ (σ : Equiv.Perm (Fin m)) (t : Fin m → ℝ), f (t ∘ σ) = f t)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hf : AnalyticOnNhd ℝ f {t | ∀ k, |t k| < ε})
    (h0 : f 0 = 1)
    (hpde : ∀ t : Fin m → ℝ, (∀ k, 0 < t k ∧ t k < ε) → Function.Injective t →
      ∀ j, gaussPDEOperator a b c f j t = 0) :
    ∀ t : Fin m → ℝ, (∀ k, |t k| < ε) → f t = hyp2F1 a b c (Matrix.diagonal t) := by
  sorry

end DLMF.MatrixArgument
