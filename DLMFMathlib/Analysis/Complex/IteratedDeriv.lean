/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Iterated derivatives of restrictions of holomorphic functions

Restricting a holomorphic function to the real axis commutes with iterated differentiation.
Taking its real part gives the corresponding real-valued derivative identity.
-/

@[expose] public noncomputable section
open Filter Set
open scoped Topology
namespace Complex

/-- Real iterated derivatives of the restriction of a holomorphic function to `ℝ`. -/
theorem iteratedDeriv_comp_ofReal_of_differentiableOn {Ψ : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hΨ : DifferentiableOn ℂ Ψ U) (k : ℕ) {t : ℝ} (ht : (t : ℂ) ∈ U) :
    iteratedDeriv k (fun x : ℝ => Ψ x) t = iteratedDeriv k Ψ t := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hev : iteratedDeriv k (fun x : ℝ => Ψ x) =ᶠ[𝓝 t] fun x : ℝ => iteratedDeriv k Ψ x := by
      filter_upwards [(hU.preimage Complex.continuous_ofReal).mem_nhds ht] with x hx using ih hx
    rw [hev.deriv_eq]
    have hd : DifferentiableAt ℂ (iteratedDeriv k Ψ) t := by
      rw [iteratedDeriv_eq_iterate]
      exact ((hΨ.analyticOnNhd hU).iterated_deriv k t ht).differentiableAt
    exact hd.hasDerivAt.comp_ofReal.deriv

/-- The real iterated derivatives of the real part of a holomorphic function are the
real parts of its complex iterated derivatives. -/
theorem iteratedDeriv_re_comp_ofReal_of_differentiableOn {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (k : ℕ) {t : ℝ} (ht : (t:ℂ) ∈ U) :
    iteratedDeriv k (fun x : ℝ => (f x).re) t = (iteratedDeriv k f t).re := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have he : iteratedDeriv k (fun x : ℝ => (f x).re) =ᶠ[𝓝 t]
        fun x : ℝ => (iteratedDeriv k f x).re := by
      filter_upwards [(hU.preimage continuous_ofReal).mem_nhds ht] with x hx using ih hx
    rw [he.deriv_eq]
    have hd : DifferentiableAt ℂ (iteratedDeriv k f) t := by
      rw [iteratedDeriv_eq_iterate]
      exact ((hf.analyticOnNhd hU).iterated_deriv k t ht).differentiableAt
    exact hd.hasDerivAt.real_of_complex.deriv

end Complex
