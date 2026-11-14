/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Multidimensional.SelbergLimits
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Weighted Dirichlet and Liouville integrals

Scaled positive power coordinates in Andrews, Askey and Roy, *Special Functions*,
§1.8, Corollaries 1.8.2–1.8.4 and Theorem 1.8.5. The simplex identities themselves
are supplied by `dirichlet_simplex` and `dirichlet_simplex_full`.
-/

@[expose] public section

open Finset MeasureTheory Set
open scoped Real

noncomputable section

namespace DLMF.Gamma

/-- The weighted power-coordinate Dirichlet integral. Andrews–Askey–Roy,
*Special Functions*, Corollaries 1.8.2–1.8.4 (synopsis AAR-1.8.1–1.8.6).
All powers of positive real coordinates use the principal complex power. -/
theorem integral_power_simplex {n : ℕ} (a p : Fin n → ℝ) (α : Fin n → ℂ)
    (ha : ∀ i, 0 < a i) (hp : ∀ i, 0 < p i) (hα : ∀ i, 0 < (α i).re)
    {h : ℝ} (hh : 0 < h) :
    IntegrableOn (fun x : Fin n → ℝ => ∏ i, (x i : ℂ) ^ (α i - 1))
      {x | (∀ i, 0 < x i) ∧ ∑ i, (x i / a i) ^ p i < h} ∧
    (∫ x : Fin n → ℝ in {x | (∀ i, 0 < x i) ∧ ∑ i, (x i / a i) ^ p i < h},
      ∏ i, (x i : ℂ) ^ (α i - 1)) =
      (h : ℂ) ^ (∑ i, α i / p i) *
        (∏ i, (a i : ℂ) ^ α i * Complex.Gamma (α i / p i) / p i) /
        Complex.Gamma (1 + ∑ i, α i / p i) := by
  sorry

/-- Liouville's reduction of a continuous radial-shell integral to one dimension.
Andrews–Askey–Roy, *Special Functions*, Theorem 1.8.5
(synopsis AAR-1.8.1–1.8.6). The number of coordinates is positive. -/
theorem integral_liouville {n : ℕ} (hn : 0 < n) (a p : Fin n → ℝ)
    (α : Fin n → ℂ) (ha : ∀ i, 0 < a i) (hp : ∀ i, 0 < p i)
    (hα : ∀ i, 0 < (α i).re) {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht : t₁ < t₂)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Icc t₁ t₂)) :
    IntegrableOn
      (fun x : Fin n → ℝ => (∏ i, (x i : ℂ) ^ (α i - 1)) *
        f (∑ i, (x i / a i) ^ p i))
      {x | (∀ i, 0 < x i) ∧ t₁ < ∑ i, (x i / a i) ^ p i ∧
        ∑ i, (x i / a i) ^ p i < t₂} ∧
    (∫ x : Fin n → ℝ in {x | (∀ i, 0 < x i) ∧
        t₁ < ∑ i, (x i / a i) ^ p i ∧ ∑ i, (x i / a i) ^ p i < t₂},
      (∏ i, (x i : ℂ) ^ (α i - 1)) * f (∑ i, (x i / a i) ^ p i)) =
      (∏ i, (a i : ℂ) ^ α i * Complex.Gamma (α i / p i) / p i) /
        Complex.Gamma (∑ i, α i / p i) *
        ∫ u in Set.Ioo t₁ t₂, (u : ℂ) ^ ((∑ i, α i / p i) - 1) * f u := by
  sorry

/-- The measurable, absolutely integrable extension of Liouville's formula.
Andrews–Askey–Roy, *Special Functions*, Theorem 1.8.5
(synopsis AAR-1.8.1–1.8.6). -/
theorem integral_liouville_of_integrable {n : ℕ} (hn : 0 < n)
    (a p : Fin n → ℝ) (α : Fin n → ℂ) (ha : ∀ i, 0 < a i)
    (hp : ∀ i, 0 < p i) (hα : ∀ i, 0 < (α i).re)
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht : t₁ < t₂)
    (f : ℝ → ℂ) (hf : Measurable f)
    (hint : IntegrableOn
      (fun u : ℝ => (u : ℂ) ^ ((∑ i, α i / p i) - 1) * f u) (Set.Ioo t₁ t₂)) :
    IntegrableOn
      (fun x : Fin n → ℝ => (∏ i, (x i : ℂ) ^ (α i - 1)) *
        f (∑ i, (x i / a i) ^ p i))
      {x | (∀ i, 0 < x i) ∧ t₁ < ∑ i, (x i / a i) ^ p i ∧
        ∑ i, (x i / a i) ^ p i < t₂} ∧
    (∫ x : Fin n → ℝ in {x | (∀ i, 0 < x i) ∧
        t₁ < ∑ i, (x i / a i) ^ p i ∧ ∑ i, (x i / a i) ^ p i < t₂},
      (∏ i, (x i : ℂ) ^ (α i - 1)) * f (∑ i, (x i / a i) ^ p i)) =
      (∏ i, (a i : ℂ) ^ α i * Complex.Gamma (α i / p i) / p i) /
        Complex.Gamma (∑ i, α i / p i) *
        ∫ u in Set.Ioo t₁ t₂, (u : ℂ) ^ ((∑ i, α i / p i) - 1) * f u := by
  sorry

/-- The volume of a coordinate ellipsoid. Andrews–Askey–Roy, *Special Functions*,
Corollary 1.8.4 (synopsis AAR-1.8.1–1.8.6). -/
theorem volume_ellipsoid {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    volume {x : Fin n → ℝ | ∑ i, (x i / a i) ^ 2 < 1} =
      ENNReal.ofReal (Real.pi ^ ((n : ℝ) / 2) * (∏ i, a i) /
        Real.Gamma (1 + (n : ℝ) / 2)) := by
  sorry

end DLMF.Gamma
