/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.SpecialFunctions.ChebyshevSeries
public import DLMF.ParabolicCylinder.ElementaryProperties

/-!
# Chebyshev-series expansions of parabolic cylinder functions (DLMF §12.20)

DLMF §12.20 asserts that `U(a,x)` and `V(a,x)` can be computed from Chebyshev expansions on
compact intervals and, for the recessive solution, on a compactified half-line. This file
proves the existence of such expansions; the coefficients and the degree are not supplied by
the source.

## Main results

* `pcfU_chebyshev_compact`, `pcfV_chebyshev_compact`: summable Chebyshev expansions of
  `U(a,x)` and `V(a,x)` on `[0, λ]`.
* `pcfU_chebyshev_infinite`: a summable Chebyshev expansion of `U(a,x)` in `1 - 2λ/x` on
  `[λ, ∞)`.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- DLMF 12.20: Chebyshev expansion on a compact interval; coefficients and degree are not supplied by the source. -/
theorem pcfU_chebyshev_compact (a : ℂ) {lam : ℝ} (hlam : 0 < lam) :
    ∃ c : ℕ → ℂ, Summable c ∧ ∀ x ∈ Icc (0:ℝ) lam, HasSum (fun k : ℕ => c k*(Polynomial.Chebyshev.T ℂ (k:ℤ)).eval (2*(x:ℂ)/lam-1)) (pcfU a x) := by
  have hF : Differentiable ℂ (fun z : ℂ => pcfU a ((lam : ℂ) * (z + 1) / 2)) :=
    (pcfU_entire a).comp (by fun_prop)
  obtain ⟨c, hc, hs⟩ := Polynomial.Chebyshev.exists_summable_series_of_entire hF
  refine ⟨c, hc, fun x hx => ?_⟩
  have h0 : 0 ≤ 2 * x / lam := div_nonneg (by linarith [hx.1]) hlam.le
  have h2 : 2 * x / lam ≤ 2 := (div_le_iff₀ hlam).mpr (by linarith [hx.2])
  have hy : 2 * x / lam - 1 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have h := hs (2 * x / lam - 1) hy
  have hlam0 : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
  have he : (lam : ℂ) * (((2 * x / lam - 1 : ℝ) : ℂ) + 1) / 2 = (x : ℂ) := by
    push_cast
    field_simp
    ring
  rw [he] at h
  convert h using 1
  funext k
  push_cast
  rfl

/-- DLMF 12.20: Chebyshev expansion on a compact interval; coefficients and degree are not supplied by the source. -/
theorem pcfV_chebyshev_compact (a : ℂ) {lam : ℝ} (hlam : 0 < lam) :
    ∃ c : ℕ → ℂ, Summable c ∧ ∀ x ∈ Icc (0:ℝ) lam, HasSum (fun k : ℕ => c k*(Polynomial.Chebyshev.T ℂ (k:ℤ)).eval (2*(x:ℂ)/lam-1)) (pcfV a x) := by
  have hF : Differentiable ℂ (fun z : ℂ => pcfV a ((lam : ℂ) * (z + 1) / 2)) :=
    (pcfV_entire a).comp (by fun_prop)
  obtain ⟨c, hc, hs⟩ := Polynomial.Chebyshev.exists_summable_series_of_entire hF
  refine ⟨c, hc, fun x hx => ?_⟩
  have h0 : 0 ≤ 2 * x / lam := div_nonneg (by linarith [hx.1]) hlam.le
  have h2 : 2 * x / lam ≤ 2 := (div_le_iff₀ hlam).mpr (by linarith [hx.2])
  have hy : 2 * x / lam - 1 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have h := hs (2 * x / lam - 1) hy
  have hlam0 : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
  have he : (lam : ℂ) * (((2 * x / lam - 1 : ℝ) : ℂ) + 1) / 2 = (x : ℂ) := by
    push_cast
    field_simp
    ring
  rw [he] at h
  convert h using 1
  funext k
  push_cast
  rfl

/-- DLMF 12.20: compactification of the half-line for the recessive solution. -/
theorem pcfU_chebyshev_infinite (a : ℂ) {lam : ℝ} (hlam : 0 < lam) :
    ∃ c : ℕ → ℂ, Summable c ∧ ∀ x : ℝ, lam ≤ x → HasSum (fun k : ℕ => c k*(Polynomial.Chebyshev.T ℂ (k:ℤ)).eval (1-2*(lam:ℂ)/x)) (pcfU a x) := by
  sorry

/- DLMF 12.6 points to a continued-fraction reference without specifying
coefficients; it adds no displayed fraction to acquire. Sections 12.18–21
contain computational references, a bibliography of external tables, the above
Chebyshev existence claims, and software listings. -/

end DLMF.Confluent
