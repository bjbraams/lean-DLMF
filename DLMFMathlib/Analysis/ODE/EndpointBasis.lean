/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Filter-relative recessive solutions and satisfactory endpoint bases

Olver, *Asymptotics and Special Functions*, Chapter 5, §§6–7, pp. 153–155,
synopsis O-5.10. The solution space is explicit. Independent dominant denominators
must be eventually nonzero; `IsLittleO` then agrees with the ordinary ratio limit
without introducing artifacts from totalized division at zeros.
-/

@[expose] public noncomputable section

open Filter Asymptotics
open scoped Topology

namespace ODE

/-- A nonzero solution is recessive along a specified approach if it is negligible
relative to every independent solution; those dominant denominators are eventually
nonzero. Olver, Chapter 5, §§6–7, synopsis O-5.10. -/
def IsRecessiveAt {α 𝕜 : Type*} [RCLike 𝕜] (V : Submodule 𝕜 (α → 𝕜))
    (l : Filter α) (f : α → 𝕜) : Prop :=
  f ∈ V ∧ f ≠ 0 ∧ ∀ g ∈ V, LinearIndependent 𝕜 ![f, g] →
    (∀ᶠ x in l, g x ≠ 0) ∧ IsLittleO l f g

/-- The solution-space, nontriviality and dominant-ratio conditions defining recessiveness. -/
theorem isRecessiveAt_iff {α 𝕜 : Type*} [RCLike 𝕜] (V : Submodule 𝕜 (α → 𝕜))
    (l : Filter α) (f : α → 𝕜) : IsRecessiveAt V l f ↔
    f ∈ V ∧ f ≠ 0 ∧ ∀ g ∈ V, LinearIndependent 𝕜 ![f, g] →
      (∀ᶠ x in l, g x ≠ 0) ∧ IsLittleO l f g := Iff.rfl

/-- Recessive solutions for the same approach differ only by a nonzero constant.
Olver, Chapter 5, §7, pp. 154–155, synopsis O-5.10. -/
theorem IsRecessiveAt.exists_smul_eq {α 𝕜 : Type*} [RCLike 𝕜]
    {V : Submodule 𝕜 (α → 𝕜)} {l : Filter α} [l.NeBot] {f g : α → 𝕜}
    (hf : IsRecessiveAt V l f) (hg : IsRecessiveAt V l g) :
    ∃ c : 𝕜, c ≠ 0 ∧ g = c • f := by
  sorry

/-- A fundamental pair includes a recessive member at every specified endpoint where
one exists. The approaches can describe distinct ends or different Stokes sectors.
Olver, Chapter 5, §7, synopsis O-5.10. -/
def IsNumericallySatisfactoryPair {α 𝕜 ι : Type*} [RCLike 𝕜]
    (V : Submodule 𝕜 (α → 𝕜)) (approach : ι → Filter α) (f g : α → 𝕜) : Prop :=
  LinearIndependent 𝕜 ![f, g] ∧ Submodule.span 𝕜 ({f, g} : Set (α → 𝕜)) = V ∧
    ∀ i, (∃ h, IsRecessiveAt V (approach i) h) →
      IsRecessiveAt V (approach i) f ∨ IsRecessiveAt V (approach i) g

/-- The basis and endpoint-recessiveness conditions of numerical satisfactory pairing. -/
theorem isNumericallySatisfactoryPair_iff {α 𝕜 ι : Type*} [RCLike 𝕜]
    (V : Submodule 𝕜 (α → 𝕜)) (approach : ι → Filter α) (f g : α → 𝕜) :
    IsNumericallySatisfactoryPair V approach f g ↔
      LinearIndependent 𝕜 ![f, g] ∧ Submodule.span 𝕜 ({f, g} : Set (α → 𝕜)) = V ∧
        ∀ i, (∃ h, IsRecessiveAt V (approach i) h) →
          IsRecessiveAt V (approach i) f ∨ IsRecessiveAt V (approach i) g := Iff.rfl

end ODE
