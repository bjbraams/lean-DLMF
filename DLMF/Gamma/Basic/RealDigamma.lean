/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.Basic.Digamma

/-!
# Real digamma at all regular parameters

The real and complex logarithmic derivatives of Gamma agree off the nonpositive integers.
This includes negative real parameters, as required by Duverney, *An Introduction to
Hypergeometric Functions*, Chapter 2, equations (2.1)–(2.2).
-/

@[expose] public noncomputable section

namespace DLMF.Gamma

/-- Complex digamma restricts to real digamma at every regular real parameter.
Duverney (2.1), synopsis DU-2.01. -/
theorem digamma_ofReal_of_not_neg_nat {x : ℝ} (hx : ∀ n : ℕ, x ≠ -(n : ℝ)) :
    Complex.digamma x = Real.digamma x := by
  have hxc : ∀ n : ℕ, (x : ℂ) ≠ -(n : ℂ) := by
    intro n h
    exact hx n (by exact_mod_cast h)
  have hG := Complex.differentiableAt_Gamma _ hxc
  have hGr := _root_.Real.differentiableAt_Gamma hx
  have h₁ : HasDerivAt (fun y : ℝ => Complex.Gamma y) (deriv Complex.Gamma x) x :=
    hG.hasDerivAt.comp_ofReal
  have h₂ : HasDerivAt (fun y : ℝ => (_root_.Real.Gamma y : ℂ))
      ((deriv _root_.Real.Gamma x : ℝ) : ℂ) x := hGr.hasDerivAt.ofReal_comp
  simp_rw [← Complex.Gamma_ofReal] at h₂
  rw [Complex.digamma_def, logDeriv_apply, h₁.unique h₂, Complex.Gamma_ofReal, Real.digamma]
  push_cast
  rfl

/-- The logarithm of the absolute Gamma value has derivative equal to digamma,
including on the negative regular intervals. Duverney (2.1), synopsis DU-2.01. -/
theorem Real.hasDerivAt_log_abs_Gamma {x : ℝ} (hx : ∀ n : ℕ, x ≠ -(n : ℝ)) :
    HasDerivAt (fun t : ℝ => _root_.Real.log |(_root_.Real.Gamma t)|) (Real.digamma x) x := by
  simpa only [_root_.Real.log_abs, Real.digamma] using
    (_root_.Real.differentiableAt_Gamma hx).hasDerivAt.log
      (_root_.Real.Gamma_ne_zero hx)

/-- The real digamma recurrence holds at every regular real parameter.
Duverney (2.2), synopsis DU-2.01. -/
theorem Real.digamma_add_one_of_not_neg_nat {x : ℝ}
    (hx : ∀ n : ℕ, x ≠ -(n : ℝ)) :
    Real.digamma (x + 1) = Real.digamma x + x⁻¹ := by
  have hnext : ∀ n : ℕ, x + 1 ≠ -(n : ℝ) := by
    intro n hn
    exact hx (n + 1) (by push_cast; linarith)
  have hxc : ∀ n : ℕ, (x : ℂ) ≠ -(n : ℂ) := by
    intro n h
    exact hx n (by exact_mod_cast h)
  have h := Complex.digamma_apply_add_one (x : ℂ) hxc
  have hcast : ((x + 1 : ℝ) : ℂ) = (x : ℂ) + 1 := by push_cast; rfl
  rw [← hcast, digamma_ofReal_of_not_neg_nat hnext,
    digamma_ofReal_of_not_neg_nat hx] at h
  exact_mod_cast h

end DLMF.Gamma
