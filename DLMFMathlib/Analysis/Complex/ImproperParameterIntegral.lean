/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Locally uniform improper integrals with a holomorphic parameter

Temme, *Special Functions* (1996), Chapter 2, Theorem 2.3, pp. 30–31,
synopsis TEM-02-03. Finite cutoffs may approach finite or infinite endpoints.
The conclusion uses their locally uniform limits and retains conditional convergence.
The underlying finite-interval and locally uniform limit APIs are
`Complex.differentiableOn_intervalIntegral_of_locally_dominated` and Mathlib's
`TendstoLocallyUniformlyOn.deriv`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace Complex

/-- Holomorphy and differentiation to every order of a locally uniform improper
parameter integral. Temme Theorem 2.3, synopsis TEM-02-03. Every cutoff interval
lies in the interval of joint continuity; local uniform convergence replaces any
absolute-integrability hypothesis at the limiting endpoints. -/
theorem differentiableOn_and_tendstoLocallyUniformlyOn_integral_iteratedDeriv
    {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {l : Filter ι} [l.NeBot] {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {J : Set ℝ} {f : ℂ → ℝ → F} {lower upper : ι → ℝ} {G : ℂ → F}
    (hc : ContinuousOn (fun p : ℂ × ℝ => f p.1 p.2) (Ω ×ˢ J))
    (hd : ∀ t ∈ J, DifferentiableOn ℂ (f · t) Ω)
    (hcut : ∀ i, uIcc (lower i) (upper i) ⊆ J)
    (hlim : TendstoLocallyUniformlyOn
      (fun i z => ∫ t in lower i..upper i, f z t) G l Ω) :
    DifferentiableOn ℂ G Ω ∧ ∀ j : ℕ,
      TendstoLocallyUniformlyOn
        (fun i z => ∫ t in lower i..upper i, iteratedDeriv j (f · t) z)
        (iteratedDeriv j G) l Ω := by
  sorry

end Complex
