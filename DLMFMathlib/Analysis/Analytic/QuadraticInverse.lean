/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Inverse
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Normalized analytic coordinates at a nondegenerate saddle

Analytic phases with nonzero second derivative admit quadratic coordinates. Specifying
the first derivative fixes the inverse germ. Temme, *Special Functions* (1996),
Chapter 11, equations (11.45)–(11.58) and (11.81)–(11.83), uses these germs to define
the coefficients of uniform beta and Marcum expansions.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace Complex

/-- An analytic saddle-coordinate map with a specified value and first derivative.
The phase equality is an equality of germs at the source saddle. -/
structure IsAnalyticSaddleMap (F G : ℂ → ℂ) (s₀ t₀ d : ℂ) (g : ℂ → ℂ) : Prop where
  analyticAt : AnalyticAt ℂ g s₀
  value : g s₀ = t₀
  derivative : deriv g s₀ = d
  phase : ∀ᶠ s in 𝓝 s₀, F (g s) - F t₀ = G s - G s₀

/-- The defining conditions on a normalized analytic saddle map. -/
theorem isAnalyticSaddleMap_iff (F G : ℂ → ℂ) (s₀ t₀ d : ℂ) (g : ℂ → ℂ) :
    IsAnalyticSaddleMap F G s₀ t₀ d g ↔
      AnalyticAt ℂ g s₀ ∧ g s₀ = t₀ ∧ deriv g s₀ = d ∧
        ∀ᶠ s in 𝓝 s₀, F (g s) - F t₀ = G s - G s₀ := by
  constructor
  · intro h
    exact ⟨h.analyticAt, h.value, h.derivative, h.phase⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨h₁, h₂, h₃, h₄⟩

/-- The analytic Morse coordinate with its prescribed branch exists.
Temme Chapter 11, (11.45)–(11.58), synopsis TEM-11-14 and TEM-11-15. -/
theorem exists_isAnalyticSaddleMap {F G : ℂ → ℂ} {s₀ t₀ d : ℂ}
    (hF : AnalyticAt ℂ F t₀) (hG : AnalyticAt ℂ G s₀)
    (hF' : deriv F t₀ = 0) (hG' : deriv G s₀ = 0)
    (hF'' : iteratedDeriv 2 F t₀ ≠ 0) (hd : d ≠ 0)
    (hsecond : iteratedDeriv 2 F t₀ * d ^ 2 = iteratedDeriv 2 G s₀) :
    ∃ g : ℂ → ℂ, IsAnalyticSaddleMap F G s₀ t₀ d g := by
  sorry

/-- A canonical representative of the analytic saddle-map germ. Values outside its
neighborhood of analyticity are unspecified; all uses are through its defining germ. -/
def analyticSaddleMap (F G : ℂ → ℂ) (s₀ t₀ d : ℂ) : ℂ → ℂ :=
  Classical.epsilon (IsAnalyticSaddleMap F G s₀ t₀ d)

/-- The defining choice of the normalized analytic saddle-map representative. -/
theorem analyticSaddleMap_def (F G : ℂ → ℂ) (s₀ t₀ d : ℂ) :
    analyticSaddleMap F G s₀ t₀ d =
      Classical.epsilon (IsAnalyticSaddleMap F G s₀ t₀ d) := rfl

/-- The canonical saddle germ has the stated phase and branch normalization.
Temme (11.45)–(11.58), synopsis TEM-11-14 and TEM-11-15. -/
theorem analyticSaddleMap_spec {F G : ℂ → ℂ} {s₀ t₀ d : ℂ}
    (hF : AnalyticAt ℂ F t₀) (hG : AnalyticAt ℂ G s₀)
    (hF' : deriv F t₀ = 0) (hG' : deriv G s₀ = 0)
    (hF'' : iteratedDeriv 2 F t₀ ≠ 0) (hd : d ≠ 0)
    (hsecond : iteratedDeriv 2 F t₀ * d ^ 2 = iteratedDeriv 2 G s₀) :
    IsAnalyticSaddleMap F G s₀ t₀ d (analyticSaddleMap F G s₀ t₀ d) := by
  exact Classical.epsilon_spec (exists_isAnalyticSaddleMap hF hG hF' hG' hF'' hd hsecond)

/-- A prescribed first derivative fixes the analytic saddle-map germ uniquely.
Temme Chapter 11 saddle substitutions, synopsis TEM-11-14, TEM-11-15 and TEM-11-19. -/
theorem IsAnalyticSaddleMap.eventuallyEq {F G : ℂ → ℂ} {s₀ t₀ d : ℂ}
    {g h : ℂ → ℂ} (hg : IsAnalyticSaddleMap F G s₀ t₀ d g)
    (hh : IsAnalyticSaddleMap F G s₀ t₀ d h)
    (hF : AnalyticAt ℂ F t₀) (hF' : deriv F t₀ = 0)
    (hF'' : iteratedDeriv 2 F t₀ ≠ 0) (hd : d ≠ 0) : g =ᶠ[𝓝 s₀] h := by
  sorry

/-- The normalized inverse quadratic germ `F(t(u))=F(t₀)-u²/2`.
The specified nonzero derivative selects one of the two branches. -/
def quadraticInverse (F : ℂ → ℂ) (t₀ d : ℂ) : ℂ → ℂ :=
  analyticSaddleMap F (fun u => -u ^ 2 / 2) 0 t₀ d

/-- The quadratic inverse is the corresponding analytic saddle map. -/
theorem quadraticInverse_def (F : ℂ → ℂ) (t₀ d : ℂ) :
    quadraticInverse F t₀ d = analyticSaddleMap F (fun u => -u ^ 2 / 2) 0 t₀ d := rfl

end Complex
