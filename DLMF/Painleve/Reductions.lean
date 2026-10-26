/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.SolutionsDefs
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Reductions of partial differential equations (DLMF §32.13)

The PDE predicates `IsMKdVOn`, `IsKdVOn`, `IsSineGordonOn`, `IsBoussinesqOn` are in
`DLMF.Painleve.SolutionsDefs`. The scaling reductions of mKdV and KdV to `PII` (32.13.2,
32.13.4; verified symbolically for every `α`), the similarity reduction of KdV (32.13.5), the
scaling reduction of sine-Gordon (32.13.7) and the travelling-wave reduction of Boussinesq
(32.13.9–32.13.10) are admitted as PDE statements, with the principal branch of `(3t)^{-1/3}`
(`3t` in the slit plane).

The ODE parts are proved: the sine-Gordon reduction `zv'' + v' = sin v` gives `PIII` with
`α = -β = 1/2`, `γ = δ = 0` for `w = exp(-iv)` (§32.13(ii)); the similarity reduction of KdV,
`W'' = -3W² + λz + C`, is solved by `W(z) = -2μ²w(μz - C/(2μ⁴))` with `w` a solution of `PI`
and `μ⁵ = -λ/2` (the "expressible in terms of `PI`" of §32.13(i), for `λ ≠ 0`); and the
Boussinesq travelling-wave equation 32.13.10 with `A ≠ 0` is solved by
`v(z) = λ²w(λz + μ) - (c² - 1)/12` with `w` a solution of `PI`, `λ⁵ = A` (§32.13(iii)). The
case `A = 0` (Weierstrass function) is not formalized.
-/

@[expose] public noncomputable section

open Set Complex

namespace DLMF.Painleve

/-- DLMF 32.13.2: if `w` solves `PII` with parameter `α` on `U`, then
`v(x, t) = (3t)^{-1/3}w(x(3t)^{-1/3})` solves the mKdV equation 32.13.1 wherever `3t` is in the
slit plane and `x(3t)^{-1/3} ∈ U` (principal branch). -/
@[dlmf 32.13.E2]
theorem mKdV_scalingReduction {α : ℂ} {w : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hw : IsPainleveIIOn α w U) :
    IsMKdVOn (fun x t => (3 * t) ^ (-1 / 3 : ℂ) * w (x * (3 * t) ^ (-1 / 3 : ℂ)))
      {p | 3 * p.2 ∈ slitPlane ∧ p.1 * (3 * p.2) ^ (-1 / 3 : ℂ) ∈ U} := by
  sorry

/-- DLMF 32.13.4: if `w` solves `PII` (any `α`) on `U`, then
`u(x, t) = -(3t)^{-2/3}(w'(z) + w(z)²)`, `z = x(3t)^{-1/3}`, solves the KdV equation 32.13.3
wherever `3t` is in the slit plane and `z ∈ U` (principal branch). -/
@[dlmf 32.13.E4]
theorem kdV_scalingReduction {α : ℂ} {w : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hw : IsPainleveIIOn α w U) :
    IsKdVOn (fun x t => -(3 * t) ^ (-2 / 3 : ℂ) *
        (deriv w (x * (3 * t) ^ (-1 / 3 : ℂ)) + w (x * (3 * t) ^ (-1 / 3 : ℂ)) ^ 2))
      {p | 3 * p.2 ∈ slitPlane ∧ p.1 * (3 * p.2) ^ (-1 / 3 : ℂ) ∈ U} := by
  sorry

/-- DLMF 32.13.5: if `W'' = -3W² + λz + C` on `U` (the twice-integrated form of the reduced
equation `W''' + 6WW' = λ`), then `u(x, t) = W(x + 3λt²) - λt` solves the KdV equation
32.13.3 wherever `x + 3λt² ∈ U`. -/
@[dlmf 32.13.E5]
theorem kdV_similarityReduction {lam C : ℂ} {W : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hW : IsODE2SolutionOn (fun z W _ => -3 * W ^ 2 + lam * z + C) W U) :
    IsKdVOn (fun x t => W (x + 3 * lam * t ^ 2) - lam * t)
      {p | p.1 + 3 * lam * p.2 ^ 2 ∈ U} := by
  sorry

/-- §32.13(i): the function `W` of 32.13.5 is expressible in terms of solutions of `PI`: if
`w` solves `PI` on `V` and `μ⁵ = -λ/2`, `μ ≠ 0`, then `W(z) = -2μ²w(μz - C/(2μ⁴))` solves
`W'' = -3W² + λz + C`. -/
@[dlmf 32.13.i]
theorem kdV_similarity_painleveI {lam C μ : ℂ} (hμ0 : μ ≠ 0) (hμ : μ ^ 5 = -lam / 2)
    {w : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V) (hw : IsPainleveIOn w V) :
    IsODE2SolutionOn (fun z W _ => -3 * W ^ 2 + lam * z + C)
      (fun z => -2 * μ ^ 2 * w (μ * z - C / (2 * μ ^ 4))) {z | μ * z - C / (2 * μ ^ 4) ∈ V} := by
  have hlin : ∀ z : ℂ, HasDerivAt (fun z => μ * z - C / (2 * μ ^ 4)) μ z := fun z =>
    (((hasDerivAt_id z).const_mul μ).sub_const _).congr_deriv (by simp)
  have hU : IsOpen {z | μ * z - C / (2 * μ ^ 4) ∈ V} :=
    hV.preimage ((continuous_const.mul continuous_id).sub continuous_const)
  refine isODE2SolutionOn_of_hasDerivAt hU
    (v := fun z => -2 * μ ^ 2 * (deriv w (μ * z - C / (2 * μ ^ 4)) * μ))
    (fun z hz => ((hw.hasDerivAt hz).comp z (hlin z)).const_mul _) (fun z hz => ?_)
  refine ((((hw.hasDerivAt_deriv _ hz).comp z (hlin z)).mul_const μ).const_mul
    (-2 * μ ^ 2)).congr_deriv ?_
  simp only [painleveIRhs]
  have hX : μ ^ 4 * (C / (2 * μ ^ 4)) = C / 2 := by field_simp
  linear_combination (-2 * z) * hμ + 2 * hX

/-- DLMF 32.13.7, §32.13(ii): if `v(z)` satisfies the reduced equation `zv'' + v' = sin v`, then
`u(x, t) = v(xt)` solves the sine-Gordon equation 32.13.6 wherever `xt ∈ U`. -/
@[dlmf 32.13.E7]
theorem sineGordon_scalingReduction {v : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hv : ∀ z ∈ U, DifferentiableAt ℂ v z) (hv1 : ∀ z ∈ U, DifferentiableAt ℂ (deriv v) z)
    (hode : ∀ z ∈ U, z * deriv (deriv v) z + deriv v z = Complex.sin (v z)) :
    IsSineGordonOn (fun x t => v (x * t)) {p | p.1 * p.2 ∈ U} := by
  sorry

/-- §32.13(ii): if `zv'' + v' = sin v` on an open set avoiding `0` (the reduced sine-Gordon
equation of 32.13.7), with `v' = v₁`, then `w = exp(-iv)` solves `PIII` with
`α = -β = 1/2` and `γ = δ = 0`. -/
@[dlmf 32.13.ii]
theorem painleveIII_of_sineGordon {v v₁ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h0 : ∀ z ∈ U, z ≠ 0) (hv : ∀ z ∈ U, HasDerivAt v (v₁ z) z)
    (hv₁ : ∀ z ∈ U, HasDerivAt v₁ ((Complex.sin (v z) - v₁ z) / z) z) :
    IsPainleveIIIOn (1 / 2) (-1 / 2) 0 0 (fun z => exp (-I * v z)) U := by
  refine ⟨isODE2SolutionOn_of_hasDerivAt hU
    (v := fun z => exp (-I * v z) * (-I * v₁ z))
    (fun z hz => ((hv z hz).const_mul (-I)).cexp) (fun z hz => ?_), h0,
    fun z _ => exp_ne_zero _⟩
  have hz0 := h0 z hz
  refine ((((hv z hz).const_mul (-I)).cexp).mul ((hv₁ z hz).const_mul (-I))).congr_deriv ?_
  simp only [painleveIIIRhs]
  have he : exp (-I * v z) ≠ 0 := exp_ne_zero _
  have h1 : exp (v z * I) * exp (-I * v z) = 1 := by
    rw [← Complex.exp_add]
    convert exp_zero using 2
    ring
  have hsin : Complex.sin (v z) * exp (-I * v z) * (2 * I) = 1 - exp (-I * v z) ^ 2 := by
    have h2 : exp (-(v z) * I) = exp (-I * v z) := by ring_nf
    rw [Complex.sin, h2]
    linear_combination (exp (-I * v z) - exp (v z * I)) * exp (-I * v z) * I_sq + h1
  field_simp
  simp only [neg_mul] at hsin ⊢
  linear_combination (-exp (-(I * v z))) * hsin

/-- DLMF 32.13.9–32.13.10: if `v'' = 6v² + (c² - 1)v + Az + B` on `U`, then the travelling wave
`u(x, t) = v(x - ct)` solves the Boussinesq equation 32.13.8 wherever `x - ct ∈ U`. -/
@[dlmf 32.13.E9, dlmf 32.13.E10]
theorem boussinesq_travellingWave {c A B : ℂ} {v : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hv : IsODE2SolutionOn (fun z v _ => 6 * v ^ 2 + (c ^ 2 - 1) * v + A * z + B) v U) :
    IsBoussinesqOn (fun x t => v (x - c * t)) {p | p.1 - c * p.2 ∈ U} := by
  sorry

/-- §32.13(iii): for `A ≠ 0` the travelling-wave equation 32.13.10 is solved in terms of `PI`:
if `w` solves `PI` on `V` and `λ⁵ = A`, then
`v(z) = λ²w(λz + (B - 6e²)/λ⁴) - e`, `e = (c² - 1)/12`, solves
`v'' = 6v² + (c² - 1)v + Az + B`. -/
@[dlmf 32.13.iii]
theorem boussinesq_painleveI {c A B lam : ℂ} (hl0 : lam ≠ 0) (hl : lam ^ 5 = A)
    {w : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V) (hw : IsPainleveIOn w V) :
    IsODE2SolutionOn (fun z v _ => 6 * v ^ 2 + (c ^ 2 - 1) * v + A * z + B)
      (fun z => lam ^ 2 * w (lam * z + (B - 6 * ((c ^ 2 - 1) / 12) ^ 2) / lam ^ 4) -
        (c ^ 2 - 1) / 12)
      {z | lam * z + (B - 6 * ((c ^ 2 - 1) / 12) ^ 2) / lam ^ 4 ∈ V} := by
  have hlin : ∀ z : ℂ, HasDerivAt (fun z => lam * z + (B - 6 * ((c ^ 2 - 1) / 12) ^ 2) / lam ^ 4)
      lam z := fun z => (((hasDerivAt_id z).const_mul lam).add_const _).congr_deriv (by simp)
  have hU : IsOpen {z | lam * z + (B - 6 * ((c ^ 2 - 1) / 12) ^ 2) / lam ^ 4 ∈ V} :=
    hV.preimage ((continuous_const.mul continuous_id).add continuous_const)
  refine isODE2SolutionOn_of_hasDerivAt hU
    (v := fun z => lam ^ 2 * (deriv w (lam * z + (B - 6 * ((c ^ 2 - 1) / 12) ^ 2) / lam ^ 4) *
      lam))
    (fun z hz => (((hw.hasDerivAt hz).comp z (hlin z)).const_mul _).sub_const _)
    (fun z hz => ?_)
  refine ((((hw.hasDerivAt_deriv _ hz).comp z (hlin z)).mul_const lam).const_mul
    (lam ^ 2)).congr_deriv ?_
  simp only [painleveIRhs]
  have hX : lam ^ 4 * ((B - 6 * ((c ^ 2 - 1) / 12) ^ 2) / lam ^ 4) =
      B - 6 * ((c ^ 2 - 1) / 12) ^ 2 := by field_simp
  linear_combination z * hl + hX

end DLMF.Painleve
