/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic
public import DLMF.Bessel.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Hardy's and Roosenraad's Hermite uncertainty theorems

The named results in Andrews, Askey and Roy, *Special Functions*, Chapter 6,
Exercises 51–52. The generalized transform is defined by its actual spectral
series in `L²`, with the positive Fourier phase `i^j`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology Real ContDiff Classical

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- Roosenraad's even and odd generalized Hermite functions, with the normalization
of Andrews–Askey–Roy, *Special Functions*, Chapter 6, Exercise 52, p. 354
(synopsis AAR-6-exercises-51–52). The parameter range is `α > -1`. -/
def generalizedHermiteFunction (α : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  if j % 2 = 0 then
    Real.sqrt ((j / 2).factorial / Real.Gamma (((j / 2 : ℕ) : ℝ) + α + 1)) *
      |x| ^ (α + 1 / 2) * Real.exp (-x ^ 2 / 2) *
      (laguerreExtended α (j / 2) (x ^ 2)).re
  else
    Real.sqrt ((j / 2).factorial / Real.Gamma (((j / 2 : ℕ) : ℝ) + α + 2)) *
      |x| ^ (α + 1 / 2) * x * Real.exp (-x ^ 2 / 2) *
      (laguerreExtended (α + 1) (j / 2) (x ^ 2)).re

/-- The explicit even and odd Laguerre formulas. -/
theorem generalizedHermiteFunction_def (α : ℝ) (j : ℕ) (x : ℝ) :
    generalizedHermiteFunction α j x =
      if j % 2 = 0 then
        Real.sqrt ((j / 2).factorial / Real.Gamma (((j / 2 : ℕ) : ℝ) + α + 1)) *
          |x| ^ (α + 1 / 2) * Real.exp (-x ^ 2 / 2) *
          (laguerreExtended α (j / 2) (x ^ 2)).re
      else
        Real.sqrt ((j / 2).factorial / Real.Gamma (((j / 2 : ℕ) : ℝ) + α + 2)) *
          |x| ^ (α + 1 / 2) * x * Real.exp (-x ^ 2 / 2) *
          (laguerreExtended (α + 1) (j / 2) (x ^ 2)).re := rfl

/-- The canonical `L²` lift of a generalized Hermite function, totalized by zero if
it is not square integrable. Andrews–Askey–Roy, Chapter 6, Exercise 52.
The square-integrability theorem identifies the lift throughout `α > -1`. -/
def generalizedHermiteLp (α : ℝ) (j : ℕ) : Lp ℂ 2 (volume : Measure ℝ) :=
  if h : MemLp (fun x : ℝ => (generalizedHermiteFunction α j x : ℂ)) 2 volume then
    h.toLp (fun x : ℝ => (generalizedHermiteFunction α j x : ℂ))
  else 0

/-- The `L²` lift agrees with `MemLp.toLp` whenever the function is square integrable. -/
theorem generalizedHermiteLp_eq_toLp (α : ℝ) (j : ℕ)
    (h : MemLp (fun x : ℝ => (generalizedHermiteFunction α j x : ℂ)) 2 volume) :
    generalizedHermiteLp α j = h.toLp
      (fun x : ℝ => (generalizedHermiteFunction α j x : ℂ)) := by
  simp [generalizedHermiteLp, h]

/-- The generalized Hermite functions are square integrable.
Andrews–Askey–Roy, *Special Functions*, Chapter 6, Exercise 52
(synopsis AAR-6-exercises-51–52). -/
theorem memLp_generalizedHermiteFunction {α : ℝ} (hα : -1 < α) (j : ℕ) :
    MemLp (fun x : ℝ => (generalizedHermiteFunction α j x : ℂ)) 2 volume := by
  sorry

/-- The generalized Hermite functions form an orthonormal basis of `L²(ℝ)`.
Andrews–Askey–Roy, *Special Functions*, Chapter 6, Exercise 52
(synopsis AAR-6-exercises-51–52). Completeness is stated as dense linear span. -/
theorem orthonormal_generalizedHermiteLp {α : ℝ} (hα : -1 < α) :
    Orthonormal ℂ (generalizedHermiteLp α) ∧
      Dense (Submodule.span ℂ (Set.range (generalizedHermiteLp α)) :
        Set (Lp ℂ 2 (volume : Measure ℝ))) := by
  sorry

/-- Roosenraad's generalized Fourier transform as the spectral series in `L²`.
Andrews–Askey–Roy, *Special Functions*, Chapter 6, Exercise 52
(synopsis AAR-6-exercises-51–52). -/
def roosenraadTransform (α : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  ∑' j : ℕ, (Complex.I ^ j * inner ℂ (generalizedHermiteLp α j) f) •
    generalizedHermiteLp α j

/-- The spectral-series formula defining the transform. -/
theorem roosenraadTransform_def (α : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    roosenraadTransform α f =
      ∑' j : ℕ, (Complex.I ^ j * inner ℂ (generalizedHermiteLp α j) f) •
        generalizedHermiteLp α j := rfl

/-- The spectral series converges and defines the unique unitary basis action.
Andrews–Askey–Roy, *Special Functions*, Chapter 6, Exercise 52
(synopsis AAR-6-exercises-51–52). -/
theorem exists_unitary_roosenraadTransform {α : ℝ} (hα : -1 < α) :
    ∃ R : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      (∀ f, R f = roosenraadTransform α f ∧
        HasSum (fun j : ℕ =>
          (Complex.I ^ j * inner ℂ (generalizedHermiteLp α j) f) •
            generalizedHermiteLp α j) (R f)) ∧
      ∀ j : ℕ, R (generalizedHermiteLp α j) = Complex.I ^ j •
        generalizedHermiteLp α j := by
  sorry

/-- The Bessel-kernel representation of the generalized Fourier transform.
Andrews–Askey–Roy, *Special Functions*, Chapter 6, Exercise 52
(synopsis AAR-6-exercises-51–52). Equality of `L²` representatives holds almost everywhere. -/
theorem roosenraadTransform_eq_integral {α : ℝ} (hα : -1 < α) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    (hzero : (0 : ℝ) ∉ tsupport f) (hf₂ : MemLp f 2 volume) :
    ∀ᵐ t : ℝ, t ≠ 0 →
      roosenraadTransform α (hf₂.toLp f) t =
        (1 / 2 : ℂ) * ∫ x : ℝ, f x * (Real.sqrt |x * t| : ℂ) *
          (Complex.besselJ α ((|x * t| : ℝ) : ℂ) + Complex.I * ((SignType.sign (x * t) : ℝ) : ℂ) *
            Complex.besselJ (α + 1) ((|x * t| : ℝ) : ℂ)) := by
  sorry

/-- Hardy's polynomial-Gaussian uncertainty theorem. Andrews–Askey–Roy,
*Special Functions*, Chapter 6, Exercise 51 (synopsis AAR-6-exercises-51–52).
The transform uses `exp(ixt)/sqrt(2π)`. -/
theorem exists_finite_hermite_expansion_of_gaussian_bounds (f : ℝ → ℂ)
    (hf₂ : MemLp f 2 volume) {m : ℝ} (hm : 0 ≤ m)
    (hbound : f =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ m * Real.exp (-x ^ 2 / 2)))
    (hfourier : (fun t : ℝ =>
      FourierTransform.fourierInv f (t / (2 * Real.pi)) / Real.sqrt (2 * Real.pi))
      =O[cocompact ℝ] (fun t : ℝ => |t| ^ m * Real.exp (-t ^ 2 / 2))) :
    ∃ N : ℕ, ∃ c : Fin N → ℂ, ∀ᵐ x : ℝ,
      f x = ∑ j : Fin N, c j * (Real.exp (-x ^ 2 / 2) : ℂ) *
        DLMF.Confluent.hermitePolynomialHEval j x := by
  sorry

/-- Roosenraad's polynomial-Gaussian uncertainty theorem. Andrews–Askey–Roy,
*Special Functions*, Chapter 6, Exercise 52, p. 354
(synopsis AAR-6-exercises-51–52). -/
theorem exists_finite_generalizedHermite_expansion_of_gaussian_bounds
    {α : ℝ} (hα : -1 < α) (f : Lp ℂ 2 (volume : Measure ℝ))
    {m : ℝ} (hm : 0 < m)
    (hbound : (fun x : ℝ => f x) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (m + α + 1 / 2) * Real.exp (-x ^ 2 / 2)))
    (htransform : (fun x : ℝ => roosenraadTransform α f x) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (m + α + 1 / 2) * Real.exp (-x ^ 2 / 2))) :
    ∃ N : ℕ, ∃ c : Fin N → ℂ, f = ∑ j : Fin N, c j • generalizedHermiteLp α j := by
  sorry

end DLMF.OrthogonalPolynomials
