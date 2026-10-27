/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset

/-!
# Truncated expansions of inverse and algebraic functions

Tools for verifying explicit Taylor polynomials of functions defined implicitly, without
computing iterated derivatives. They reduce an expansion `F = P + O(φ)` to a residual estimate
for a polynomial identity satisfied by `F`.

* `invSer_isBigO_sub_of_pow_sub`: if `A → a ≠ 0`, `B → a` and `A^n - B^n = O(φ)`, then
  `A - B = O(φ)` (roots of algebraic relations, e.g. square and cube roots).
* `invSer_isBigO_sub_of_leftInverse`: if `g` is a left inverse of `f` near `x₀` with a strict
  derivative at `f x₀`, then for any approximant `P → x₀` of `g ∘ h`,
  `P - g ∘ h = O(f ∘ P - h)`: a candidate expansion of an inverse function is verified by
  substituting it into `f`.
* `invSer_isBigO_pow_of_eq_mul`: a function of the form `y^n · q(y)` with `q` bounded near the
  point is `O(y^n)`.
-/

@[expose] public noncomputable section

open Filter Topology Asymptotics

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {α : Type*} {l : Filter α}

/-- Roots of algebraic relations: if `A → a ≠ 0`, `B → a` and `A^n - B^n = O(φ)` (with
`n ≠ 0` in characteristic zero), then `A - B = O(φ)`. -/
theorem invSer_isBigO_sub_of_pow_sub [CharZero 𝕜] {A B : α → 𝕜} {a : 𝕜}
    {φ : α → 𝕜} {n : ℕ} (hn : n ≠ 0) (ha : a ≠ 0) (hA : Tendsto A l (𝓝 a))
    (hB : Tendsto B l (𝓝 a)) (h : (fun z => A z ^ n - B z ^ n) =O[l] φ) :
    (fun z => A z - B z) =O[l] φ := by
  set S : α → 𝕜 := fun z => ∑ i ∈ Finset.range n, A z ^ i * B z ^ (n - 1 - i) with hS
  have hSl : Tendsto S l (𝓝 ((n : 𝕜) * a ^ (n - 1))) := by
    have : Tendsto S l (𝓝 (∑ i ∈ Finset.range n, a ^ i * a ^ (n - 1 - i))) :=
      tendsto_finsetSum _ fun i _ => (hA.pow i).mul (hB.pow (n - 1 - i))
    convert this using 2
    rw [Finset.sum_congr rfl fun i hi => by
      rw [← pow_add, show i + (n - 1 - i) = n - 1 by
        have := Finset.mem_range.1 hi; omega]]
    simp
  have hne : (n : 𝕜) * a ^ (n - 1) ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 hn) (pow_ne_zero _ ha)
  have hinv : (fun z => (S z)⁻¹) =O[l] (fun _ => (1 : 𝕜)) := (hSl.inv₀ hne).isBigO_one 𝕜
  refine (hinv.mul h).congr' ?_ (Eventually.of_forall fun _ => by simp)
  filter_upwards [hSl.eventually_ne hne] with z hz
  have := (Commute.all (A z) (B z)).geom_sum₂_mul n
  rw [← this]
  field_simp
  rfl

/-- A function of the form `y^n · q(y)` with `q` bounded is `O(y^n)`. -/
theorem invSer_isBigO_pow_of_eq_mul {f q : α → 𝕜} {y : α → 𝕜} (n : ℕ)
    (hq : q =O[l] (fun _ => (1 : 𝕜))) (hf : ∀ᶠ z in l, f z = y z ^ n * q z) :
    f =O[l] (fun z => y z ^ n) := by
  refine (((isBigO_refl (fun z => y z ^ n) l).mul hq).congr' (hf.mono fun z hz => hz.symm)
    (Eventually.of_forall fun _ => rfl)).trans ?_
  simpa using isBigO_refl (fun z => y z ^ n) l

/-- Verifying an expansion of an inverse function by substitution. If `g` is a left inverse of
`f` near `x₀`, strictly differentiable at `y₀ = f x₀`, `f` is continuous at `x₀`, and `P → x₀`,
`h → y₀`, then `P - g ∘ h = O(f ∘ P - h)`. -/
theorem invSer_isBigO_sub_of_leftInverse {f g : 𝕜 → 𝕜} {x₀ g' : 𝕜}
    (hg : HasStrictDerivAt g g' (f x₀)) (hgf : ∀ᶠ x in 𝓝 x₀, g (f x) = x)
    (hf : ContinuousAt f x₀) {P h : α → 𝕜} (hP : Tendsto P l (𝓝 x₀))
    (hh : Tendsto h l (𝓝 (f x₀))) :
    (fun z => P z - g (h z)) =O[l] (fun z => f (P z) - h z) := by
  have h1 := hg.hasStrictFDerivAt.isBigO_sub
  have h2 : Tendsto (fun z => (f (P z), h z)) l (𝓝 (f x₀, f x₀)) :=
    (hf.tendsto.comp hP).prodMk_nhds hh
  refine (h1.comp_tendsto h2).congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [hP.eventually hgf] with z hz
  simp [Function.comp, hz]

end
