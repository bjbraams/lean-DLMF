/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Noether's first integral for a configuration symmetry

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018), Chapter 2,
pp. 2-3–2-5, synopsis RL-2.14. Invariance and the Euler–Lagrange equation
are explicit analytic hypotheses. The theorem also applies to normed configuration
spaces, since only Fréchet derivatives and scalar conservation are used.
-/

@[expose] public noncomputable section
open Set
namespace Lagrangian

/-- Conservation of the momentum paired with the infinitesimal configuration
symmetry, Rao–Lakshminarayanan Chapter 2, pp. 2-3–2-5, synopsis RL-2.14. -/
theorem momentum_generator_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ → E → E → ℝ) (Φ : ℝ → E → E) (q : ℝ → E) {I : Set ℝ}
    (hI : IsOpen I) (hIc : IsPreconnected I)
    (hL : ContDiff ℝ 2 (fun p : ℝ × E × E => L p.1 p.2.1 p.2.2))
    (hΦ : ContDiff ℝ 2 (fun p : ℝ × E => Φ p.1 p.2))
    (hΦ₀ : ∀ x, Φ 0 x = x)
    (hinvariant : ∀ s t x v, L t (Φ s x) (fderiv ℝ (Φ s) x v) = L t x v)
    (hq : ContDiffOn ℝ 2 q I)
    (hEL : ∀ t ∈ I,
      HasDerivAt (fun t => fderiv ℝ (fun v => L t (q t) v) (deriv q t))
        (fderiv ℝ (fun x => L t x (deriv q t)) (q t)) t) :
    ∀ s ∈ I, ∀ t ∈ I,
      fderiv ℝ (fun v => L s (q s) v) (deriv q s)
          (deriv (fun r => Φ r (q s)) 0) =
        fderiv ℝ (fun v => L t (q t) v) (deriv q t)
          (deriv (fun r => Φ r (q t)) 0) := by
  sorry

end Lagrangian
