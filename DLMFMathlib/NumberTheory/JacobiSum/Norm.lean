/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.JacobiSum.Basic
public import TauCeti.NumberTheory.GaussSum.Basic

/-!
# The absolute value of a nondegenerate complex Jacobi sum

Andrews, Askey and Roy, *Special Functions*, §1.10, pp. 39–42,
synopsis AAR-1.10.1–1.10.11. The proof uses Mathlib's Jacobi/Gauss quotient
and the proved TauCeti Gauss-sum absolute value.
-/

@[expose] public section

/-- Nontrivial characters with nontrivial product have Jacobi sum of magnitude sqrt(card F).
Andrews–Askey–Roy, §1.10, synopsis AAR-1.10.1–1.10.11. A primitive additive character only
supplies the Gauss-quotient proof; the Jacobi sum itself is independent of it. -/
theorem norm_jacobiSum {F : Type*} [Field F] [Fintype F] {χ φ : MulChar F ℂ}
    (hχ : χ ≠ 1) (hφ : φ ≠ 1) (hχφ : χ * φ ≠ 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖jacobiSum χ φ‖ = Real.sqrt (Fintype.card F) := by
  have hc : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum hc hχφ hψ, norm_div, norm_mul,
    TauCeti.norm_gaussSum hχ hψ, TauCeti.norm_gaussSum hφ hψ,
    TauCeti.norm_gaussSum hχφ hψ]
  have hs : Real.sqrt (Fintype.card F) ≠ 0 :=
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)).ne'
  exact mul_div_cancel_right₀ _ hs
