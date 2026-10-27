/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.ODE.Defs
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Changes of variables and products of solutions (DLMF §§1.13(iv)–1.13(v))

For `w'' + f(z) w' + g(z) w = 0` on an open set `D ⊆ ℂ` (`IsLinODE2SolOn f g 0 w D`):

* the inversion `ξ = 1/z` (1.13.11–1.13.12);
* elimination of the first derivative by a change of the dependent variable (1.13.13–1.13.15)
  and of the independent variable (1.13.16–1.13.17); the integrals `∫ f dz` of DLMF are
  primitives `F` of `f` on `D` (hypotheses `HasDerivAt F (f z) z`), so the statements are
  branch-free;
* the Liouville transformation 1.13.18–1.13.19, stated in the variable `z` with a chosen square
  root `σ` of `ζ'` (admitted), the Schwarzian derivative 1.13.20 (definition `schwarzian`; the
  first form is admitted), Cayley's identity 1.13.21 (admitted) and the inversion formula
  1.13.22 (proved from 1.13.21);
* the third-order equation 1.13.23 for products of solutions, and 1.13.25 (admitted).
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DLMF.AlgebraicAnalytic

variable {f g : ℂ → ℂ} {D : Set ℂ}

/-! ## The point at infinity (1.13.11–1.13.12) -/

/-- DLMF 1.13.11–1.13.12: if `w` solves 1.13.1 on the open set `D` with `0 ∉ D`, then
`W(ξ) = w(1/ξ)` solves `W'' + F(ξ) W' + G(ξ) W = 0` with `F(ξ) = 2/ξ - ξ⁻² f(1/ξ)`,
`G(ξ) = ξ⁻⁴ g(1/ξ)`, on `{ξ : 1/ξ ∈ D}`. -/
@[dlmf 1.13.E11, dlmf 1.13.E12]
theorem isLinODE2SolOn_inv (hD : IsOpen D) (h0 : (0 : ℂ) ∉ D) {w : ℂ → ℂ}
    (hw : IsLinODE2SolOn f g 0 w D) :
    IsLinODE2SolOn (fun ξ => 2 / ξ - f ξ⁻¹ / ξ ^ 2) (fun ξ => g ξ⁻¹ / ξ ^ 4) 0
      (fun ξ => w ξ⁻¹) ((fun ξ => ξ⁻¹) ⁻¹' D) := by
  have hne : ∀ ξ ∈ (fun ξ : ℂ => ξ⁻¹) ⁻¹' D, ξ ≠ 0 := by
    rintro ξ hξ rfl
    exact h0 (by simpa using hξ)
  have hW : ∀ ξ ∈ (fun ξ : ℂ => ξ⁻¹) ⁻¹' D,
      HasDerivAt (fun ξ => w ξ⁻¹) (deriv w ξ⁻¹ * -(ξ ^ 2)⁻¹) ξ := fun ξ hξ =>
    (hw _ hξ).1.hasDerivAt.comp ξ (hasDerivAt_inv (hne ξ hξ))
  intro ξ hξ
  have hξ0 := hne ξ hξ
  have hnhds : (fun ξ : ℂ => ξ⁻¹) ⁻¹' D ∈ 𝓝 ξ :=
    (continuousAt_inv₀ hξ0).preimage_mem_nhds (hD.mem_nhds hξ)
  have hev : deriv (fun ξ => w ξ⁻¹) =ᶠ[𝓝 ξ] fun η => deriv w η⁻¹ * -(η ^ 2)⁻¹ := by
    filter_upwards [hnhds] with η hη
    exact (hW η hη).deriv
  have hd2 : HasDerivAt (fun η => -(η ^ 2)⁻¹) (-(-(↑2 * ξ ^ (2 - 1) * 1) / (ξ ^ 2) ^ 2)) ξ :=
    (((hasDerivAt_id ξ).pow 2).inv (pow_ne_zero 2 hξ0)).neg
  refine ⟨(hW ξ hξ).differentiableAt, ?_⟩
  refine ((((hw _ hξ).2.comp ξ (hasDerivAt_inv hξ0)).mul hd2).congr_of_eventuallyEq
    hev).congr_deriv ?_
  rw [(hW ξ hξ).deriv]
  simp only [Pi.zero_apply, Function.comp_apply]
  field_simp
  ring

/-! ## Elimination of the first derivative (1.13.13–1.13.17) -/

/-- DLMF 1.13.13–1.13.15: if `w` solves 1.13.1 on the open set `D` and `F` is a primitive of `f`
on `D` (`∫ f dz`), then `W = w e^{F/2}` (so `w = W exp(-½∫ f dz)`) solves `W'' - H W = 0` with
`H = ¼ f² + ½ f' - g`. -/
@[dlmf 1.13.E13, dlmf 1.13.E14, dlmf 1.13.E15]
theorem isLinODE2SolOn_elim_first (hD : IsOpen D) {F : ℂ → ℂ}
    (hF : ∀ z ∈ D, HasDerivAt F (f z) z) (hf : DifferentiableOn ℂ f D) {w : ℂ → ℂ}
    (hw : IsLinODE2SolOn f g 0 w D) :
    IsLinODE2SolOn 0 (fun z => -(f z ^ 2 / 4 + deriv f z / 2 - g z)) 0
      (fun z => w z * Complex.exp (F z / 2)) D := by
  have he : ∀ z ∈ D, HasDerivAt (fun y => Complex.exp (F y / 2))
      (Complex.exp (F z / 2) * (f z / 2)) z := fun z hz => ((hF z hz).div_const 2).cexp
  have hW : ∀ z ∈ D, HasDerivAt (fun y => w y * Complex.exp (F y / 2))
      (deriv w z * Complex.exp (F z / 2) + w z * (Complex.exp (F z / 2) * (f z / 2))) z :=
    fun z hz => (hw z hz).1.hasDerivAt.mul (he z hz)
  intro z hz
  have hev : deriv (fun y => w y * Complex.exp (F y / 2)) =ᶠ[𝓝 z]
      fun y => deriv w y * Complex.exp (F y / 2) + w y * (Complex.exp (F y / 2) * (f y / 2)) := by
    filter_upwards [hD.mem_nhds hz] with y hy
    exact (hW y hy).deriv
  have hfd : HasDerivAt f (deriv f z) z :=
    (hf.differentiableAt (hD.mem_nhds hz)).hasDerivAt
  refine ⟨(hW z hz).differentiableAt, ?_⟩
  refine ((((hw z hz).2.mul (he z hz)).add ((hw z hz).1.hasDerivAt.mul
    ((he z hz).mul (hfd.div_const 2)))).congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [Pi.zero_apply, Pi.mul_apply]
  ring

/-- The first derivative of `v ∘ η` with `η' = e^{-F}`. -/
lemma g1d_hasDerivAt_comp_eta {F η v : ℂ → ℂ} {z : ℂ}
    (hη : HasDerivAt η (Complex.exp (-F z)) z) (hv : DifferentiableAt ℂ v (η z)) :
    HasDerivAt (v ∘ η) (deriv v (η z) * Complex.exp (-F z)) z :=
  hv.hasDerivAt.comp z hη

/-- DLMF 1.13.16–1.13.17: if `F` is a primitive of `f` on the open set `D` and
`η' = exp(-F)` (1.13.16), then for `w = v ∘ η`
`w'' + f w' + g w = e^{-2F} (d²v/dη² + g e^{2F} v)`. -/
@[dlmf 1.13.E16, dlmf 1.13.E17]
theorem hasDerivAt_deriv_comp_eta (hD : IsOpen D) {F η v : ℂ → ℂ}
    (hF : ∀ z ∈ D, HasDerivAt F (f z) z) (hη : ∀ z ∈ D, HasDerivAt η (Complex.exp (-F z)) z)
    (hv : ∀ z ∈ D, DifferentiableAt ℂ v (η z) ∧ DifferentiableAt ℂ (deriv v) (η z)) {z : ℂ}
    (hz : z ∈ D) :
    DifferentiableAt ℂ (v ∘ η) z ∧
      HasDerivAt (deriv (v ∘ η)) (-f z * deriv (v ∘ η) z - g z * (v ∘ η) z +
        Complex.exp (-2 * F z) * (deriv (deriv v) (η z) + g z * Complex.exp (2 * F z) *
          v (η z))) z := by
  have h1 := g1d_hasDerivAt_comp_eta (hη z hz) (hv z hz).1
  have hev : deriv (v ∘ η) =ᶠ[𝓝 z] fun y => deriv v (η y) * Complex.exp (-F y) := by
    filter_upwards [hD.mem_nhds hz] with y hy
    exact (g1d_hasDerivAt_comp_eta (hη y hy) (hv y hy).1).deriv
  refine ⟨h1.differentiableAt, ?_⟩
  refine ((((hv z hz).2.hasDerivAt.comp z (hη z hz)).mul (hF z hz).neg.cexp).congr_of_eventuallyEq
    hev).congr_deriv ?_
  rw [h1.deriv]
  have e1 : Complex.exp (-2 * F z) * Complex.exp (2 * F z) = 1 := by
    rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
  have e2 : Complex.exp (-2 * F z) = Complex.exp (-F z) * Complex.exp (-F z) := by
    rw [← Complex.exp_add]; ring_nf
  simp only [Function.comp_apply]
  linear_combination (-(g z * v (η z))) * e1 -
    deriv (deriv v) (η z) * e2

/-- DLMF 1.13.17: with `η` as in 1.13.16, `w = v ∘ η` solves 1.13.1 on `D` iff
`d²v/dη² + g e^{2∫f} v = 0` at `η(z)` for every `z ∈ D`. -/
@[dlmf 1.13.E17]
theorem isLinODE2SolOn_comp_eta_iff (hD : IsOpen D) {F η v : ℂ → ℂ}
    (hF : ∀ z ∈ D, HasDerivAt F (f z) z) (hη : ∀ z ∈ D, HasDerivAt η (Complex.exp (-F z)) z)
    (hv : ∀ z ∈ D, DifferentiableAt ℂ v (η z) ∧ DifferentiableAt ℂ (deriv v) (η z)) :
    IsLinODE2SolOn f g 0 (v ∘ η) D ↔
      ∀ z ∈ D, deriv (deriv v) (η z) + g z * Complex.exp (2 * F z) * v (η z) = 0 := by
  constructor
  · intro hw z hz
    have h := (hasDerivAt_deriv_comp_eta (g := g) hD hF hη hv hz).2
    have h' := (hw z hz).2
    have := h.unique h'
    simp only [Pi.zero_apply] at this
    have hx : Complex.exp (-2 * F z) * (deriv (deriv v) (η z) +
        g z * Complex.exp (2 * F z) * v (η z)) = 0 := by linear_combination this
    exact (mul_eq_zero.mp hx).resolve_left (Complex.exp_ne_zero _)
  · intro h z hz
    obtain ⟨hd, h2⟩ := hasDerivAt_deriv_comp_eta (g := g) hD hF hη hv hz
    refine ⟨hd, h2.congr_deriv ?_⟩
    rw [h z hz, Pi.zero_apply]
    ring

/-! ## Liouville transformation and Schwarzian derivatives (1.13.18–1.13.22) -/

/-- DLMF 1.13.18–1.13.19 (Liouville transformation), stated in the variable `z`: let `W` solve
`W'' = H W` (1.13.14) on the open set `D`, let `ζ` be three times differentiable with `ζ' ≠ 0`,
and let `σ` be a differentiable square root of `ζ'` (`σ² = ζ'`, the branch of `(ζ')^{1/2}`).
Then `U = σ W` satisfies `d²U/dζ² = (ż² H - ½{z, ζ}) U`, where `d/dζ = (1/ζ') d/dz`,
`ż = 1/ζ'` and, by 1.13.22, `-½{z, ζ} = {ζ, z}/(2ζ'²)`. -/
@[dlmf 1.13.E18, dlmf 1.13.E19]
theorem liouville_transformation (hD : IsOpen D) {H W ζ σ : ℂ → ℂ}
    (hW : IsLinODE2SolOn 0 (fun z => -H z) 0 W D) (hζ : ContDiffOn ℂ 3 ζ D)
    (hζ' : ∀ z ∈ D, deriv ζ z ≠ 0) (hσ : ∀ z ∈ D, DifferentiableAt ℂ σ z)
    (hσ2 : ∀ z ∈ D, σ z ^ 2 = deriv ζ z) (z : ℂ) (hz : z ∈ D) :
    deriv (fun y => deriv (fun x => σ x * W x) y / deriv ζ y) z / deriv ζ z =
      (H z / deriv ζ z ^ 2 + schwarzian ζ z / (2 * deriv ζ z ^ 2)) * (σ z * W z) := by
  sorry

/-- DLMF 1.13.20, first form: `{z, ζ} = -2 ż^{1/2} d²(ż^{-1/2})/dζ²`, with `τ` a branch of
`ż^{-1/2}` near `ζ₀` (`τ² ż = 1`), so that `ż^{1/2} = 1/τ`. -/
@[dlmf 1.13.E20]
theorem schwarzian_eq_sqrt {z τ : ℂ → ℂ} {ζ₀ : ℂ} (hz : ContDiffAt ℂ 3 z ζ₀)
    (hτ : ContDiffAt ℂ 2 τ ζ₀) (hτz : ∀ᶠ ζ in 𝓝 ζ₀, τ ζ ^ 2 * deriv z ζ = 1) :
    schwarzian z ζ₀ = -2 * (τ ζ₀)⁻¹ * iteratedDeriv 2 τ ζ₀ := by
  sorry

/-- DLMF 1.13.21 (Cayley's identity): for `z = Z(ξ(ζ))`,
`{z, ζ} = (dξ/dζ)² {z, ξ} + {ξ, ζ}`, when `ξ` and `Z` are three times differentiable with
nonvanishing first derivatives. -/
@[dlmf 1.13.E21]
theorem schwarzian_comp {Z ξ : ℂ → ℂ} {ζ : ℂ} (hξ : ContDiffAt ℂ 3 ξ ζ)
    (hZ : ContDiffAt ℂ 3 Z (ξ ζ)) (hξ' : deriv ξ ζ ≠ 0) (hZ' : deriv Z (ξ ζ) ≠ 0) :
    schwarzian (Z ∘ ξ) ζ = deriv ξ ζ ^ 2 * schwarzian Z (ξ ζ) + schwarzian ξ ζ := by
  sorry

/-- The Schwarzian derivative of a function equal to the identity near `ζ₀` vanishes. -/
lemma g1d_schwarzian_of_eventuallyEq_id {u : ℂ → ℂ} {ζ₀ : ℂ} (hu : u =ᶠ[𝓝 ζ₀] id) :
    schwarzian u ζ₀ = 0 := by
  have h3 := hu.iteratedDeriv_eq 3
  have h2 := hu.iteratedDeriv_eq 2
  have h1 := hu.deriv_eq
  simp only [schwarzian, h3, h2, h1, iteratedDeriv_succ, iteratedDeriv_zero, deriv_id',
    deriv_const']
  norm_num

/-- DLMF 1.13.22: if `ζ(z)` is the inverse of `z(ζ)` near `ζ₀` (both three times
differentiable), then `{z, ζ} = -(dz/dζ)² {ζ, z}`. -/
@[dlmf 1.13.E22]
theorem schwarzian_inverse {z ζf : ℂ → ℂ} {ζ₀ : ℂ} (hz : ContDiffAt ℂ 3 z ζ₀)
    (hζf : ContDiffAt ℂ 3 ζf (z ζ₀)) (hinv : ζf ∘ z =ᶠ[𝓝 ζ₀] id) (hz' : deriv z ζ₀ ≠ 0) :
    schwarzian z ζ₀ = -(deriv z ζ₀ ^ 2 * schwarzian ζf (z ζ₀)) := by
  have hd : deriv ζf (z ζ₀) * deriv z ζ₀ = 1 := by
    rw [← deriv_comp ζ₀ (hζf.differentiableAt (by norm_num)) (hz.differentiableAt
      (by norm_num)), hinv.deriv_eq, deriv_id]
  have hζf' : deriv ζf (z ζ₀) ≠ 0 := left_ne_zero_of_mul_eq_one hd
  have := schwarzian_comp hz hζf hz' hζf'
  rw [g1d_schwarzian_of_eventuallyEq_id hinv] at this
  linear_combination -this

/-! ## Products of solutions (§1.13(v)) -/

/-- DLMF 1.13.23: the product `w = w₁ w₂` of two solutions of 1.13.1 on the open set `D`
(with `f`, `g` analytic in `D`) satisfies
`w''' + 3f w'' + (2f² + f' + 4g) w' + (4fg + 2g') w = 0`. -/
@[dlmf 1.13.E23]
theorem product_solution_ode3 (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (hg : DifferentiableOn ℂ g D) {w₁ w₂ : ℂ → ℂ} (h₁ : IsLinODE2SolOn f g 0 w₁ D)
    (h₂ : IsLinODE2SolOn f g 0 w₂ D) {z : ℂ} (hz : z ∈ D) :
    iteratedDeriv 3 (fun y => w₁ y * w₂ y) z + 3 * f z * iteratedDeriv 2 (fun y => w₁ y * w₂ y) z +
        (2 * f z ^ 2 + deriv f z + 4 * g z) * deriv (fun y => w₁ y * w₂ y) z +
        (4 * f z * g z + 2 * deriv g z) * (w₁ z * w₂ z) = 0 := by
  set E1 : ℂ → ℂ := fun y => deriv w₁ y * w₂ y + w₁ y * deriv w₂ y
  set E2 : ℂ → ℂ := fun y => (-f y * deriv w₁ y - g y * w₁ y) * w₂ y +
    2 * (deriv w₁ y * deriv w₂ y) + w₁ y * (-f y * deriv w₂ y - g y * w₂ y)
  have hP1 : ∀ y ∈ D, HasDerivAt (fun y => w₁ y * w₂ y) (E1 y) y := fun y hy =>
    (h₁ y hy).1.hasDerivAt.mul (h₂ y hy).1.hasDerivAt
  have hP2 : ∀ y ∈ D, HasDerivAt E1 (E2 y) y := by
    intro y hy
    refine (((h₁ y hy).2.mul (h₂ y hy).1.hasDerivAt).add
      ((h₁ y hy).1.hasDerivAt.mul (h₂ y hy).2)).congr_deriv ?_
    simp only [E2, Pi.zero_apply]
    ring
  have hfd : HasDerivAt f (deriv f z) z := (hf.differentiableAt (hD.mem_nhds hz)).hasDerivAt
  have hgd : HasDerivAt g (deriv g z) z := (hg.differentiableAt (hD.mem_nhds hz)).hasDerivAt
  have a1 := (h₁ z hz).1.hasDerivAt
  have a2 := (h₂ z hz).1.hasDerivAt
  have b1 := (h₁ z hz).2
  have b2 := (h₂ z hz).2
  have hP3 : HasDerivAt E2 _ z :=
    ((((hfd.neg.mul b1).sub (hgd.mul a1)).mul a2).add ((b1.mul b2).const_mul 2)).add
      (a1.mul ((hfd.neg.mul b2).sub (hgd.mul a2)))
  have hev1 : deriv (fun y => w₁ y * w₂ y) =ᶠ[𝓝 z] E1 := by
    filter_upwards [hD.mem_nhds hz] with y hy
    exact (hP1 y hy).deriv
  have hev2 : deriv (deriv (fun y => w₁ y * w₂ y)) =ᶠ[𝓝 z] E2 := by
    filter_upwards [hD.mem_nhds hz] with y hy
    have hev1y : deriv (fun y => w₁ y * w₂ y) =ᶠ[𝓝 y] E1 := by
      filter_upwards [hD.mem_nhds hy] with x hx
      exact (hP1 x hx).deriv
    rw [hev1y.deriv_eq, (hP2 y hy).deriv]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hev2.deriv_eq, hev2.eq_of_nhds, hev1.eq_of_nhds, hP3.deriv]
  simp only [E1, E2, Pi.zero_apply, Pi.neg_apply, Pi.mul_apply, Pi.sub_apply]
  ring

/-- DLMF 1.13.24–1.13.25: if `U'' + I U = 0` and `V'' + J V = 0` on the open set `D` (with `I`,
`J` analytic in `D` and `I ≠ J` there), then `W = U V` satisfies
`d/dz ((W''' + 2(I + J) W' + (I' + J') W)/(I - J)) = -(I - J) W`. -/
@[dlmf 1.13.E24, dlmf 1.13.E25]
theorem product_solution_IJ (hD : IsOpen D) {I J U V : ℂ → ℂ} (hI : DifferentiableOn ℂ I D)
    (hJ : DifferentiableOn ℂ J D) (hIJ : ∀ z ∈ D, I z ≠ J z) (hU : IsLinODE2SolOn 0 I 0 U D)
    (hV : IsLinODE2SolOn 0 J 0 V D) {z : ℂ} (hz : z ∈ D) :
    deriv (fun y => (iteratedDeriv 3 (fun x => U x * V x) y +
        2 * (I y + J y) * deriv (fun x => U x * V x) y +
        (deriv I y + deriv J y) * (U y * V y)) / (I y - J y)) z =
      -(I z - J z) * (U z * V z) := by
  sorry

end DLMF.AlgebraicAnalytic
