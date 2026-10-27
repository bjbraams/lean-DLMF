/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.SpecialFunctions.ChebyshevSeries
public import DLMF.ParabolicCylinder.Basic

/-!
# Cylinder Chebyshev-series existence claims

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
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
