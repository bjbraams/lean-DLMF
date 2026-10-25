/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Products of solutions of a second-order equation

If `f'' = q f` and `g'' = q g`, their product satisfies
`(fg)''' = 4 q (fg)' + 2 q' fg`. This common calculation applies to both
Airy and parabolic-cylinder functions, without assumptions specific to either family.

Over `ℝ` and `ℂ`, the third-order Wronskian and Cramer formulas give decomposition
in a fundamental system and uniqueness from an initial value and two derivatives.
-/

@[expose] public noncomputable section

namespace ODE

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {f f' g g' q q' : 𝕜 → 𝕜}


/-- First derivative of the product of two functions with specified derivatives. -/
theorem product_deriv (hf : ∀ z, HasDerivAt f (f' z) z)
    (hg : ∀ z, HasDerivAt g (g' z) z) :
    deriv (fun z => f z * g z) = fun z => f' z * g z + f z * g' z :=
  funext fun z => ((hf z).mul (hg z)).deriv


/-- Second derivative of a product of solutions of `f'' = q f`. -/
theorem product_second_deriv
    (hf : ∀ z, HasDerivAt f (f' z) z ∧ HasDerivAt f' (q z * f z) z)
    (hg : ∀ z, HasDerivAt g (g' z) z ∧ HasDerivAt g' (q z * g z) z) :
    deriv (deriv (fun z => f z * g z)) =
      fun z => 2 * q z * f z * g z + 2 * f' z * g' z := by
  rw [product_deriv (fun z => (hf z).1) (fun z => (hg z).1)]
  funext z
  have h := ((hf z).2.mul (hg z).1).add ((hf z).1.mul (hg z).2)
  exact h.deriv.trans (by ring)


/-- The symmetric-square equation for products of solutions of `f'' = q f`. -/
theorem product_third_deriv
    (hf : ∀ z, HasDerivAt f (f' z) z ∧ HasDerivAt f' (q z * f z) z)
    (hg : ∀ z, HasDerivAt g (g' z) z ∧ HasDerivAt g' (q z * g z) z)
    (hq : ∀ z, HasDerivAt q (q' z) z) (z : 𝕜) :
    iteratedDeriv 3 (fun t => f t * g t) z =
      4 * q z * deriv (fun t => f t * g t) z + 2 * q' z * f z * g z := by
  have he := product_second_deriv hf hg
  have h := ((((hq z).const_mul 2).mul (hf z).1).mul (hg z).1).add
    (((hf z).2.mul (hg z).2).const_mul 2)
  have hd : deriv (fun t => 2 * q t * f t * g t + 2 * f' t * g' t) z =
      2 * q' z * f z * g z + 4 * q z * (f' z * g z + f z * g' z) := by
    have h0 : HasDerivAt (fun t => 2 * q t * f t * g t + 2 * f' t * g' t) _ z :=
      h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
        simp only [Pi.mul_apply, Pi.add_apply]; ring)
    rw [h0.deriv]
    simp only [Pi.mul_apply]
    ring
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [he, hd, product_deriv (fun z => (hf z).1) (fun z => (hg z).1)]
  ring

section ThirdOrder

variable {𝕝 : Type*} [RCLike 𝕝]


/-- A solution together with its first two derivatives for `y''' = p y' + q y`. -/
def IsThirdOrderSolution (p q y y1 y2 : 𝕝 → 𝕝) : Prop :=
  ∀ x, HasDerivAt y (y1 x) x ∧ HasDerivAt y1 (y2 x) x ∧
    HasDerivAt y2 (p x*y1 x+q x*y x) x

/-- Constant multiples preserve the homogeneous third-order equation. -/
theorem IsThirdOrderSolution.const_mul {p q y y1 y2 : 𝕝 → 𝕝}
    (hy : IsThirdOrderSolution p q y y1 y2) (c : 𝕝) :
    IsThirdOrderSolution p q (fun x => c*y x) (fun x => c*y1 x) (fun x => c*y2 x) := by
  intro x
  refine ⟨(hy x).1.const_mul c, (hy x).2.1.const_mul c, ?_⟩
  exact ((hy x).2.2.const_mul c).congr_deriv (by ring)

/-- Sums preserve the homogeneous third-order equation. -/
theorem IsThirdOrderSolution.add {p q y y1 y2 z z1 z2 : 𝕝 → 𝕝}
    (hy : IsThirdOrderSolution p q y y1 y2) (hz : IsThirdOrderSolution p q z z1 z2) :
    IsThirdOrderSolution p q (fun x => y x+z x) (fun x => y1 x+z1 x)
      (fun x => y2 x+z2 x) := by
  intro x
  refine ⟨(hy x).1.add (hz x).1, (hy x).2.1.add (hz x).2.1, ?_⟩
  exact ((hy x).2.2.add (hz x).2.2).congr_deriv (by ring)

/-- Products of second-order solutions give a solution triple of the symmetric-square equation. -/
theorem product_isThirdOrderSolution {f f' g g' q q' : 𝕝 → 𝕝}
    (hf : ∀ x, HasDerivAt f (f' x) x ∧ HasDerivAt f' (q x*f x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x ∧ HasDerivAt g' (q x*g x) x)
    (hq : ∀ x, HasDerivAt q (q' x) x) :
    IsThirdOrderSolution (fun x => 4*q x) (fun x => 2*q' x)
      (fun x => f x*g x) (fun x => f' x*g x+f x*g' x)
      (fun x => 2*q x*f x*g x+2*f' x*g' x) := by
  intro x
  refine ⟨(hf x).1.mul (hg x).1, ?_, ?_⟩
  · exact (((hf x).2.mul (hg x).1).add ((hf x).1.mul (hg x).2)).congr_deriv (by ring)
  · have h := ((((hq x).const_mul 2).mul (hf x).1).mul (hg x).1).add
      (((hf x).2.mul (hg x).2).const_mul 2)
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
    · simp only [Pi.mul_apply, Pi.add_apply]
      ring
    · simp only [Pi.mul_apply]
      ring

/-- The Wronskian of three solution triples of a third-order equation. -/
def thirdOrderWronskian (y y1 y2 u u1 u2 v v1 v2 : 𝕝 → 𝕝) (x : 𝕝) : 𝕝 :=
  y x*(u1 x*v2 x-v1 x*u2 x)-u x*(y1 x*v2 x-v1 x*y2 x)+
    v x*(y1 x*u2 x-u1 x*y2 x)

/-- A third-order equation with no second-derivative term has constant Wronskians. -/
theorem thirdOrderWronskian_const {p q y y1 y2 u u1 u2 v v1 v2 : 𝕝 → 𝕝}
    (hy : IsThirdOrderSolution p q y y1 y2) (hu : IsThirdOrderSolution p q u u1 u2)
    (hv : IsThirdOrderSolution p q v v1 v2) (x x₀ : 𝕝) :
    thirdOrderWronskian y y1 y2 u u1 u2 v v1 v2 x =
      thirdOrderWronskian y y1 y2 u u1 u2 v v1 v2 x₀ := by
  have hd : ∀ x, HasDerivAt (thirdOrderWronskian y y1 y2 u u1 u2 v v1 v2) 0 x := fun x => by
    obtain ⟨y0, y1', y2'⟩ := hy x
    obtain ⟨u0, u1', u2'⟩ := hu x
    obtain ⟨v0, v1', v2'⟩ := hv x
    have h := ((y0.mul ((u1'.mul v2').sub (v1'.mul u2'))).sub
      (u0.mul ((y1'.mul v2').sub (v1'.mul y2')))).add
      (v0.mul ((y1'.mul u2').sub (u1'.mul y2')))
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.sub_apply]
    ring
  exact is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) x x₀

/-- Cramer's rule for the first component of a triple. -/
theorem thirdOrder_cramer (y y1 y2 u u1 u2 v v1 v2 w w1 w2 : 𝕝 → 𝕝) (x : 𝕝) :
    thirdOrderWronskian u u1 u2 v v1 v2 w w1 w2 x * y x =
      thirdOrderWronskian y y1 y2 v v1 v2 w w1 w2 x * u x +
      thirdOrderWronskian u u1 u2 y y1 y2 w w1 w2 x * v x +
      thirdOrderWronskian u u1 u2 v v1 v2 y y1 y2 x * w x := by
  unfold thirdOrderWronskian
  ring

/-- Decomposition in a fundamental system with constant nonzero Wronskian. -/
theorem thirdOrder_decomp {p q y y1 y2 u u1 u2 v v1 v2 w w1 w2 : 𝕝 → 𝕝}
    (hy : IsThirdOrderSolution p q y y1 y2) (hu : IsThirdOrderSolution p q u u1 u2)
    (hv : IsThirdOrderSolution p q v v1 v2) (hw : IsThirdOrderSolution p q w w1 w2)
    {D : 𝕝} (hW : ∀ x, thirdOrderWronskian u u1 u2 v v1 v2 w w1 w2 x = D)
    (hD : D ≠ 0) (x x₀ : 𝕝) :
    y x = thirdOrderWronskian y y1 y2 v v1 v2 w w1 w2 x₀ / D * u x +
      thirdOrderWronskian u u1 u2 y y1 y2 w w1 w2 x₀ / D * v x +
      thirdOrderWronskian u u1 u2 v v1 v2 y y1 y2 x₀ / D * w x := by
  have h := thirdOrder_cramer y y1 y2 u u1 u2 v v1 v2 w w1 w2 x
  rw [hW x, thirdOrderWronskian_const hy hv hw x x₀,
    thirdOrderWronskian_const hu hy hw x x₀, thirdOrderWronskian_const hu hv hy x x₀] at h
  field_simp
  linear_combination h

/-- Equal initial triples determine the same solution once a fundamental system is known. -/
theorem thirdOrder_eq_of_initial {p q y y1 y2 z z1 z2 u u1 u2 v v1 v2 w w1 w2 : 𝕝 → 𝕝}
    (hy : IsThirdOrderSolution p q y y1 y2) (hz : IsThirdOrderSolution p q z z1 z2)
    (hu : IsThirdOrderSolution p q u u1 u2) (hv : IsThirdOrderSolution p q v v1 v2)
    (hw : IsThirdOrderSolution p q w w1 w2) {x₀ : 𝕝}
    (hW : thirdOrderWronskian u u1 u2 v v1 v2 w w1 w2 x₀ ≠ 0)
    (h0 : y x₀ = z x₀) (h1 : y1 x₀ = z1 x₀) (h2 : y2 x₀ = z2 x₀) : y = z := by
  funext x
  have hconst := fun t => thirdOrderWronskian_const hu hv hw t x₀
  rw [thirdOrder_decomp hy hu hv hw hconst hW x x₀,
    thirdOrder_decomp hz hu hv hw hconst hW x x₀]
  simp only [thirdOrderWronskian, h0, h1, h2]

end ThirdOrder

end ODE
