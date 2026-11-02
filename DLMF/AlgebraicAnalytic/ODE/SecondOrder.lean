/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.ODE.Basic
public import DLMFMathlib.Analysis.ODE.EntireLinear
public import DLMFMathlib.Analysis.ODE.BallLinear
public import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Normalization
public import Mathlib.Analysis.Complex.HasPrimitives
public import TauCeti.Analysis.Complex.Conformal.Inverse.Function
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Linear second-order differential equations (DLMF §§1.13(i)–1.13(iii))

Existence, uniqueness, fundamental pairs, Wronskians, parameter dependence and the
inhomogeneous equation for `w'' + f(z) w' + g(z) w = r(z)` on an open set `D ⊆ ℂ` with analytic
coefficients (`IsLinearODE2SolutionOn f g r w D`).

## Main results

* `exists_isLinearODE2SolutionOn`, `exists_isLinearODE2SolutionOn_univ`: solutions with prescribed
  `w(z₀)`, `w'(z₀)` on a simply connected domain, and for entire coefficients (from
  `ODE.exists_entire_solution_linear_ode'`).
* `isLinearODE2SolutionOn_unique`: uniqueness on a connected open set (from `ODE.eqOn_of_ode`).
* `IsLinearODE2SolutionOn.linear_combination`: linear combinations of solutions.
* `isFundamentalPair_of_initial`, `exists_isFundamentalPair`,
  `isFundamentalPair_of_wronskian_ne_zero`: fundamental pairs (DLMF 1.13.2–1.13.3).
* `wronskianN_two`: the two-argument Wronskian as a determinant (DLMF 1.13.4).
* `wronskian_eq_mul_exp`, `wronskian_const_of_f_eq_zero`: Abel's identity (DLMF 1.13.5).
* `isFundamentalPair_tfae`: the equivalences 1.13.6.
* `isLinearODE2SolutionOn_param_analytic`: parameter dependence (DLMF 1.13.7, §1.13(ii)).
* `exists_isLinearODE2SolutionOn_inhom`, `isLinearODE2SolutionOn_inhom_eq`,
  `isLinearODE2SolutionOn_varParam`: the inhomogeneous equation, its general solution 1.13.9 and
  variation of parameters 1.13.10.

## Implementation notes

Existence on a simply connected proper domain transports the equation to the unit disc by a
normalized Riemann map (Tau Ceti's `TauCeti.riemannMapping_normalized`) and solves it there by
`ODE.exists_ball_solution_linear_ode`; the same transport gives primitives, which feed
variation of parameters for the inhomogeneous equation.

Abel's identity is stated given a primitive `F` of `f`, so that `e^{-∫ f} = e^{-F}`; variation
of parameters is stated given primitives of `w₁ r/𝒲` and `w₂ r/𝒲`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DLMF.AlgebraicAnalytic

variable {f g r : ℂ → ℂ} {D : Set ℂ}

/-! ## Basic facts about solutions -/

/-- A solution satisfies the differential equation with `deriv (deriv w)`. -/
theorem IsLinearODE2SolutionOn.deriv_deriv {w : ℂ → ℂ}
    (hw : IsLinearODE2SolutionOn f g r w D) {z : ℂ}
    (hz : z ∈ D) : deriv (deriv w) z = r z - f z * deriv w z - g z * w z :=
  (hw z hz).2.deriv

/-- A solution is complex differentiable on `D`. -/
theorem IsLinearODE2SolutionOn.differentiableOn {w : ℂ → ℂ}
    (hw : IsLinearODE2SolutionOn f g r w D) :
    DifferentiableOn ℂ w D := fun z hz => (hw z hz).1.differentiableWithinAt

/-- A solution on an open set is analytic there. -/
theorem IsLinearODE2SolutionOn.analyticOnNhd {w : ℂ → ℂ} (hD : IsOpen D)
    (hw : IsLinearODE2SolutionOn f g r w D) :
    AnalyticOnNhd ℂ w D := hw.differentiableOn.analyticOnNhd hD

/-- Linear combinations: if `w` solves the equation with right side `r₁` and `v` with `r₂`, then
`A w + B v` solves it with right side `A r₁ + B r₂`. -/
theorem IsLinearODE2SolutionOn.linear_combination {r₁ r₂ w v : ℂ → ℂ} (hD : IsOpen D)
    (hw : IsLinearODE2SolutionOn f g r₁ w D)
    (hv : IsLinearODE2SolutionOn f g r₂ v D) (A B : ℂ) (hr : ∀ z ∈ D, r z = A * r₁ z + B * r₂ z) :
    IsLinearODE2SolutionOn f g r (fun z => A * w z + B * v z) D := by
  intro z hz
  have hev : deriv (fun y => A * w y + B * v y) =ᶠ[𝓝 z]
      fun y => A * deriv w y + B * deriv v y := by
    filter_upwards [hD.mem_nhds hz] with y hy
    have h1 := (hw y hy).1.hasDerivAt.const_mul A
    have h2 := (hv y hy).1.hasDerivAt.const_mul B
    exact (h1.add h2).deriv
  refine ⟨((hw z hz).1.const_mul A).add ((hv z hz).1.const_mul B), ?_⟩
  refine ((((hw z hz).2.const_mul A).add ((hv z hz).2.const_mul B)).congr_of_eventuallyEq
    hev).congr_deriv ?_
  rw [hev.eq_of_nhds, hr z hz]
  ring

/-- The zero function solves the homogeneous equation. -/
lemma isLinearODE2SolutionOn_zero : IsLinearODE2SolutionOn f g 0 (fun _ => 0) D := fun z _ => by
  refine ⟨differentiableAt_const _, ?_⟩
  simp only [deriv_const', Pi.zero_apply, mul_zero, sub_zero]
  exact hasDerivAt_const z 0

/-- The derivative of a linear combination of solutions, at a point of the open set `D`. -/
private lemma deriv_const_mul_add_const_mul_of_isLinearODE2SolutionOn {w v : ℂ → ℂ} {r₁ r₂ : ℂ → ℂ}
    (hw : IsLinearODE2SolutionOn f g r₁ w D)
    (hv : IsLinearODE2SolutionOn f g r₂ v D) (A B : ℂ) {z : ℂ} (hz : z ∈ D) :
    deriv (fun y => A * w y + B * v y) z = A * deriv w z + B * deriv v z :=
  (((hw z hz).1.hasDerivAt.const_mul A).add ((hv z hz).1.hasDerivAt.const_mul B)).deriv

/-! ## Existence and uniqueness (§1.13(i)) -/

/-- DLMF §1.13(i) for entire coefficients: `w'' + f w' + g w = 0` has an entire solution with
prescribed `w(z₀)`, `w'(z₀)`. -/
@[dlmf 1.13.i]
theorem exists_isLinearODE2SolutionOn_univ (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (z₀ w₀ w₁ : ℂ) : ∃ w, IsLinearODE2SolutionOn f g 0 w univ ∧ w z₀ = w₀ ∧ deriv w z₀ = w₁ := by
  obtain ⟨w, hw, hode, h0, h1⟩ := ODE.exists_entire_solution_linear_ode' (p := fun z => -f z)
    (q := fun z => -g z) hf.neg hg.neg z₀ w₀ w₁
  refine ⟨w, fun z _ => ⟨hw z, (hode z).congr_deriv ?_⟩, h0, h1⟩
  simp only [Pi.zero_apply]
  ring

/-- A Riemann map of a simply connected proper domain `D` onto the unit disc, normalized by
`φ(z₀) = 0`, together with its holomorphic inverse `ψ` and the chain rule `ψ'(φ z) φ'(z) = 1`. -/
private lemma exists_riemannMap_data (hD : IsOpen D) (hsc : IsSimplyConnected D) (hne : D ≠ univ)
    {z₀ : ℂ} (hz₀ : z₀ ∈ D) :
    ∃ φ ψ : ℂ → ℂ, φ z₀ = 0 ∧ AnalyticOnNhd ℂ φ D ∧ DifferentiableOn ℂ ψ (Metric.ball 0 1) ∧
      MapsTo φ D (Metric.ball 0 1) ∧ MapsTo ψ (Metric.ball 0 1) D ∧ LeftInvOn ψ φ D ∧
      ∀ z ∈ D, deriv ψ (φ z) * deriv φ z = 1 := by
  obtain ⟨φ, hφ, -⟩ := TauCeti.riemannMapping_normalized hD hsc hne hz₀
  set ψ := Function.invFunOn φ D
  have hbij := hφ.bijOn
  have hψd : DifferentiableOn ℂ ψ (Metric.ball 0 1) := by
    have := _root_.DifferentiableOn.invFunOn hφ.differentiableOn hD hbij.injOn
    rwa [hbij.image_eq] at this
  have hleft : LeftInvOn ψ φ D := hbij.injOn.leftInvOn_invFunOn
  have hψD : MapsTo ψ (Metric.ball 0 1) D := fun ζ hζ => Function.invFunOn_mem (hbij.surjOn hζ)
  have hφa : AnalyticOnNhd ℂ φ D := hφ.differentiableOn.analyticOnNhd hD
  refine ⟨φ, ψ, hφ.map_base, hφa, hψd, hbij.mapsTo, hψD, hleft, fun z hz => ?_⟩
  have hev : ψ ∘ φ =ᶠ[𝓝 z] id := by
    filter_upwards [hD.mem_nhds hz] with y hy using hleft hy
  have h1 : HasDerivAt (ψ ∘ φ) (deriv ψ (φ z) * deriv φ z) z :=
    ((hψd.differentiableAt (Metric.isOpen_ball.mem_nhds (hbij.mapsTo hz))).hasDerivAt).comp z
      (hφa z hz).differentiableAt.hasDerivAt
  exact h1.unique ((hasDerivAt_id z).congr_of_eventuallyEq hev)

/-- A holomorphic function on a simply connected open set has a primitive vanishing at a given
point (via the Riemann mapping theorem and Morera's theorem on the disc). -/
private lemma exists_primitive_of_isSimplyConnected (hD : IsOpen D) (hsc : IsSimplyConnected D)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F D) {z₀ : ℂ} (hz₀ : z₀ ∈ D) :
    ∃ G : ℂ → ℂ, (∀ z ∈ D, HasDerivAt G (F z) z) ∧ G z₀ = 0 := by
  suffices h : ∃ G : ℂ → ℂ, ∀ z ∈ D, HasDerivAt G (F z) z by
    obtain ⟨G, hG⟩ := h
    exact ⟨fun z => G z - G z₀, fun z hz => (hG z hz).sub_const _, sub_self _⟩
  by_cases hne : D = univ
  · subst hne
    exact (differentiableOn_univ.mp hF).isExactOn_univ
  obtain ⟨φ, ψ, -, hφa, hψd, hφD, hψD, hleft, hchain⟩ := exists_riemannMap_data hD hsc hne hz₀
  have hψa : AnalyticOnNhd ℂ ψ (Metric.ball 0 1) := hψd.analyticOnNhd Metric.isOpen_ball
  obtain ⟨H, hH⟩ := ((hF.comp hψd hψD).mul hψa.deriv.differentiableOn).isExactOn_ball
  refine ⟨H ∘ φ, fun z hz => ?_⟩
  have h := (hH (φ z) (hφD hz)).comp z (hφa z hz).differentiableAt.hasDerivAt
  convert h using 1
  change F z = F (ψ (φ z)) * deriv ψ (φ z) * deriv φ z
  rw [hleft hz, mul_assoc, hchain z hz, mul_one]

/-- DLMF §1.13(i): on a simply connected domain `D`, with `f`, `g` analytic in `D`, the equation
1.13.1 has a solution with prescribed `w(z₀)` and `w'(z₀)` at any `z₀ ∈ D` (so infinitely many
analytic solutions). -/
@[dlmf 1.13.i]
theorem exists_isLinearODE2SolutionOn (hD : IsOpen D) (hsc : IsSimplyConnected D)
    (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D) {z₀ : ℂ} (hz₀ : z₀ ∈ D)
    (w₀ w₁ : ℂ) : ∃ w, IsLinearODE2SolutionOn f g 0 w D ∧ w z₀ = w₀ ∧ deriv w z₀ = w₁ := by
  by_cases hne : D = univ
  · subst hne
    obtain ⟨w, hw, h0, h1⟩ := exists_isLinearODE2SolutionOn_univ (differentiableOn_univ.mp hf)
      (differentiableOn_univ.mp hg) z₀ w₀ w₁
    exact ⟨w, hw, h0, h1⟩
  obtain ⟨φ, ψ, hφ0, hφa, hψd, hφD, hψD, hleft, hchain⟩ := exists_riemannMap_data hD hsc hne hz₀
  have hφ'ne : ∀ z ∈ D, deriv φ z ≠ 0 := fun z hz h => by simpa [h] using hchain z hz
  have hd1 : DifferentiableOn ℂ (deriv φ) D := hφa.deriv.differentiableOn
  have hd2 : DifferentiableOn ℂ (deriv (deriv φ)) D := hφa.deriv.deriv.differentiableOn
  set P : ℂ → ℂ := fun ζ =>
    -((deriv (deriv φ) (ψ ζ) + f (ψ ζ) * deriv φ (ψ ζ)) / deriv φ (ψ ζ) ^ 2)
  set Q : ℂ → ℂ := fun ζ => -(g (ψ ζ) / deriv φ (ψ ζ) ^ 2)
  have hne2 : ∀ ζ ∈ Metric.ball (0 : ℂ) 1, deriv φ (ψ ζ) ^ 2 ≠ 0 := fun ζ hζ =>
    pow_ne_zero _ (hφ'ne _ (hψD hζ))
  have hPd : DifferentiableOn ℂ P (Metric.ball 0 1) :=
    (((hd2.comp hψd hψD).add ((hf.comp hψd hψD).mul (hd1.comp hψd hψD))).div
      ((hd1.comp hψd hψD).pow 2) hne2).neg
  have hQd : DifferentiableOn ℂ Q (Metric.ball 0 1) :=
    ((hg.comp hψd hψD).div ((hd1.comp hψd hψD).pow 2) hne2).neg
  obtain ⟨v, hvd, hvode, hv0, hv1⟩ :=
    ODE.exists_ball_solution_linear_ode hPd hQd w₀ (w₁ / deriv φ z₀)
  have hvda : ∀ z ∈ D, HasDerivAt v (deriv v (φ z)) (φ z) := fun z hz =>
    (hvd.differentiableAt (Metric.isOpen_ball.mem_nhds (hφD hz))).hasDerivAt
  have hderiv : ∀ z ∈ D, HasDerivAt (v ∘ φ) (deriv v (φ z) * deriv φ z) z := fun z hz =>
    (hvda z hz).comp z (hφa z hz).differentiableAt.hasDerivAt
  refine ⟨v ∘ φ, fun z hz => ⟨(hderiv z hz).differentiableAt, ?_⟩, ?_, ?_⟩
  · have hev : deriv (v ∘ φ) =ᶠ[𝓝 z] fun y => deriv v (φ y) * deriv φ y := by
      filter_upwards [hD.mem_nhds hz] with y hy using (hderiv y hy).deriv
    have h2 := ((hvode (φ z) (hφD hz)).comp z
      (hφa z hz).differentiableAt.hasDerivAt).mul
      (hd1.differentiableAt (hD.mem_nhds hz)).hasDerivAt
    refine (h2.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [(hderiv z hz).deriv]
    have hψφ : ψ (φ z) = z := hleft hz
    have hnz := hφ'ne z hz
    simp only [P, Q, hψφ, Function.comp_apply, Pi.zero_apply]
    field_simp
    ring
  · simp [hφ0, hv0]
  · rw [(hderiv z₀ hz₀).deriv, hφ0, hv1]
    field_simp [hφ'ne z₀ hz₀]

/-- DLMF §1.13(i): a solution of 1.13.1 on a connected open set `D` (with `f`, `g` analytic in
`D`) is uniquely determined by `w(z₀)` and `w'(z₀)`. -/
@[dlmf 1.13.i]
theorem isLinearODE2SolutionOn_unique (hD : IsOpen D) (hD' : IsPreconnected D)
    (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D) {w v : ℂ → ℂ}
    (hw : IsLinearODE2SolutionOn f g 0 w D) (hv : IsLinearODE2SolutionOn f g 0 v D)
        {z₀ : ℂ} (hz₀ : z₀ ∈ D)
    (h₀ : w z₀ = v z₀) (h₁ : deriv w z₀ = deriv v z₀) : EqOn w v D := by
  have hp : ContDiffAt ℂ ∞ (fun z => -f z) z₀ :=
    ((hf.analyticOnNhd hD z₀ hz₀).neg).contDiffAt
  have hq : ContDiffAt ℂ ∞ (fun z => -g z) z₀ :=
    ((hg.analyticOnNhd hD z₀ hz₀).neg).contDiffAt
  refine ODE.eqOn_of_ode hD hD' (hw.analyticOnNhd hD) (hv.analyticOnNhd hD) hz₀ hp hq
    (fun x hx => ?_) (fun x hx => ?_) h₀ h₁
  · rw [hw.deriv_deriv hx, Pi.zero_apply]; ring
  · rw [hv.deriv_deriv hx, Pi.zero_apply]; ring

/-! ## Wronskian and fundamental pairs -/

/-- DLMF 1.13.4: the two-argument Wronskian is the determinant `det [[w₁, w₂], [w₁', w₂']]`. -/
@[dlmf 1.13.E4]
theorem wronskianN_two (w₁ w₂ : ℂ → ℂ) (z : ℂ) :
    wronskianN ![w₁, w₂] z = ODE.wronskian w₁ w₂ z := by
  simp [wronskianN, ODE.wronskian, Matrix.det_fin_two]

/-- DLMF §1.13(i): if the Wronskian of two solutions does not vanish at one point `z₀` of the
connected open set `D`, they are a fundamental pair in `D`. -/
@[dlmf 1.13.E2]
theorem isFundamentalPair_of_wronskian_ne_zero (hD : IsOpen D) (hD' : IsPreconnected D)
    (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D) {w₁ w₂ : ℂ → ℂ}
    (h₁ : IsLinearODE2SolutionOn f g 0 w₁ D) (h₂ : IsLinearODE2SolutionOn f g 0 w₂ D)
        {z₀ : ℂ} (hz₀ : z₀ ∈ D)
    (hW : ODE.wronskian w₁ w₂ z₀ ≠ 0) : IsFundamentalPair f g w₁ w₂ D := by
  refine ⟨h₁, h₂, fun w hw => ?_⟩
  set W := ODE.wronskian w₁ w₂ z₀
  set A := (w z₀ * deriv w₂ z₀ - w₂ z₀ * deriv w z₀) / W
  set B := (w₁ z₀ * deriv w z₀ - w z₀ * deriv w₁ z₀) / W
  have hsol := h₁.linear_combination hD h₂ A B (r := 0) (fun z _ => by simp)
  refine ⟨A, B, fun z hz => isLinearODE2SolutionOn_unique hD hD' hf hg hw hsol hz₀ ?_ ?_ hz⟩
  · simp only [A, B]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hW]
    simp only [W, ODE.wronskian]
    ring
  · rw [deriv_const_mul_add_const_mul_of_isLinearODE2SolutionOn h₁ h₂ A B hz₀]
    simp only [A, B]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hW]
    simp only [W, ODE.wronskian]
    ring

/-- DLMF 1.13.3: solutions with `w₁(z₀) = 1`, `w₁'(z₀) = 0`, `w₂(z₀) = 0`, `w₂'(z₀) = 1` are a
fundamental pair in the connected open set `D`. -/
@[dlmf 1.13.E3]
theorem isFundamentalPair_of_initial (hD : IsOpen D) (hD' : IsPreconnected D)
    (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D) {w₁ w₂ : ℂ → ℂ}
    (h₁ : IsLinearODE2SolutionOn f g 0 w₁ D) (h₂ : IsLinearODE2SolutionOn f g 0 w₂ D)
        {z₀ : ℂ} (hz₀ : z₀ ∈ D)
    (h10 : w₁ z₀ = 1) (h11 : deriv w₁ z₀ = 0) (h20 : w₂ z₀ = 0) (h21 : deriv w₂ z₀ = 1) :
    IsFundamentalPair f g w₁ w₂ D :=
  isFundamentalPair_of_wronskian_ne_zero hD hD' hf hg h₁ h₂ hz₀ (by simp [ODE.wronskian, *])

/-- DLMF 1.13.3: on a simply connected domain, a fundamental pair exists. -/
@[dlmf 1.13.E3]
theorem exists_isFundamentalPair (hD : IsOpen D) (hsc : IsSimplyConnected D)
    (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D) :
    ∃ w₁ w₂, IsFundamentalPair f g w₁ w₂ D := by
  obtain ⟨z₀, hz₀⟩ := hsc.nonempty
  obtain ⟨w₁, h₁, h10, h11⟩ := exists_isLinearODE2SolutionOn hD hsc hf hg hz₀ 1 0
  obtain ⟨w₂, h₂, h20, h21⟩ := exists_isLinearODE2SolutionOn hD hsc hf hg hz₀ 0 1
  exact ⟨w₁, w₂, isFundamentalPair_of_initial hD hsc.isPathConnected.isConnected.isPreconnected
    hf hg h₁ h₂ hz₀ h10 h11 h20 h21⟩

/-- The derivative of the Wronskian of two solutions of 1.13.1: `𝒲' = -f 𝒲`. -/
private lemma hasDerivAt_wronskian_of_isLinearODE2SolutionOn {w₁ w₂ : ℂ → ℂ}
    (h₁ : IsLinearODE2SolutionOn f g 0 w₁ D)
    (h₂ : IsLinearODE2SolutionOn f g 0 w₂ D) {z : ℂ} (hz : z ∈ D) :
    HasDerivAt (ODE.wronskian w₁ w₂) (-f z * ODE.wronskian w₁ w₂ z) z := by
  have := (((h₁ z hz).1.hasDerivAt.mul (h₂ z hz).2)).sub
    ((h₂ z hz).1.hasDerivAt.mul (h₁ z hz).2)
  refine this.congr_deriv ?_
  simp only [ODE.wronskian, Pi.zero_apply]
  ring

/-- DLMF 1.13.5 (Abel's identity): if `F` is a primitive of `f` on the connected open set `D`
(so that `e^{-∫ f dz} = e^{-F}`), the Wronskian of two solutions of 1.13.1 is `c e^{-F(z)}`
with `c` independent of `z`. -/
@[dlmf 1.13.E5]
theorem wronskian_eq_mul_exp (hD : IsOpen D) (hD' : IsPreconnected D) {F : ℂ → ℂ}
    (hF : ∀ z ∈ D, HasDerivAt F (f z) z) {w₁ w₂ : ℂ → ℂ} (h₁ : IsLinearODE2SolutionOn f g 0 w₁ D)
    (h₂ : IsLinearODE2SolutionOn f g 0 w₂ D) :
    ∃ c : ℂ, ∀ z ∈ D, ODE.wronskian w₁ w₂ z = c * Complex.exp (-F z) := by
  have hd : ∀ z ∈ D, HasDerivAt (fun z => ODE.wronskian w₁ w₂ z * Complex.exp (F z)) 0 z := by
    intro z hz
    refine ((hasDerivAt_wronskian_of_isLinearODE2SolutionOn h₁ h₂ hz).mul
        ((hF z hz).cexp)).congr_deriv ?_
    ring
  obtain ⟨c, hc⟩ := hD.exists_is_const_of_deriv_eq_zero hD'
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv)
  refine ⟨c, fun z hz => ?_⟩
  rw [← hc z hz, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

/-- DLMF §1.13(i): if `f = 0`, the Wronskian of two solutions is constant on a connected open
set. -/
@[dlmf 1.13.E5]
theorem wronskian_const_of_f_eq_zero (hD : IsOpen D) (hD' : IsPreconnected D)
    {w₁ w₂ : ℂ → ℂ} (h₁ : IsLinearODE2SolutionOn 0 g 0 w₁ D)
        (h₂ : IsLinearODE2SolutionOn 0 g 0 w₂ D)
    {z z' : ℂ} (hz : z ∈ D) (hz' : z' ∈ D) : ODE.wronskian w₁ w₂ z = ODE.wronskian w₁ w₂ z' := by
  obtain ⟨c, hc⟩ := wronskian_eq_mul_exp hD hD' (F := fun _ => 0)
    (fun z _ => by simpa using hasDerivAt_const z (0 : ℂ)) h₁ h₂
  rw [hc z hz, hc z' hz']

/-- The data of a linear combination of solutions at a point vanish only trivially if the
Wronskian there does not vanish. -/
private lemma eq_zero_of_wronskian_ne_zero {w₁ w₂ : ℂ → ℂ} {A B z : ℂ}
    (hW : ODE.wronskian w₁ w₂ z ≠ 0)
    (h0 : A * w₁ z + B * w₂ z = 0) (h1 : A * deriv w₁ z + B * deriv w₂ z = 0) :
    A = 0 ∧ B = 0 := by
  unfold ODE.wronskian at hW
  constructor
  · have : A * (w₁ z * deriv w₂ z - w₂ z * deriv w₁ z) = 0 := by
      linear_combination deriv w₂ z * h0 - w₂ z * h1
    exact (mul_eq_zero.mp this).resolve_right hW
  · have : B * (w₁ z * deriv w₂ z - w₂ z * deriv w₁ z) = 0 := by
      linear_combination w₁ z * h1 - deriv w₁ z * h0
    exact (mul_eq_zero.mp this).resolve_right hW

/-- DLMF 1.13.6: on a simply connected domain `D` (with `f`, `g` analytic in `D`), for two
solutions `w₁`, `w₂` of 1.13.1 the following are equivalent: they are a fundamental pair; their
Wronskian does not vanish in `D`; they are linearly independent on `D`. -/
@[dlmf 1.13.E6]
theorem isFundamentalPair_tfae (hD : IsOpen D) (hsc : IsSimplyConnected D)
    (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D) {w₁ w₂ : ℂ → ℂ}
    (h₁ : IsLinearODE2SolutionOn f g 0 w₁ D) (h₂ : IsLinearODE2SolutionOn f g 0 w₂ D) :
    List.TFAE [IsFundamentalPair f g w₁ w₂ D, ∀ z ∈ D, ODE.wronskian w₁ w₂ z ≠ 0,
      ∀ A B : ℂ, (∀ z ∈ D, A * w₁ z + B * w₂ z = 0) → A = 0 ∧ B = 0] := by
  have hD' : IsPreconnected D := hsc.isPathConnected.isConnected.isPreconnected
  obtain ⟨z₀, hz₀⟩ := hsc.nonempty
  tfae_have 1 → 2 := by
    rintro ⟨-, -, hall⟩ z hz
    obtain ⟨u₁, hu₁, hu10, hu11⟩ := exists_isLinearODE2SolutionOn hD hsc hf hg hz 1 0
    obtain ⟨u₂, hu₂, hu20, hu21⟩ := exists_isLinearODE2SolutionOn hD hsc hf hg hz 0 1
    obtain ⟨A₁, B₁, hAB₁⟩ := hall u₁ hu₁
    obtain ⟨A₂, B₂, hAB₂⟩ := hall u₂ hu₂
    have e1 : w₁ z * A₁ + w₂ z * B₁ = 1 := by rw [← hu10, hAB₁ z hz]; ring
    have e2 : deriv w₁ z * A₁ + deriv w₂ z * B₁ = 0 := by
      rw [← hu11, (eventuallyEq_of_mem (hD.mem_nhds hz) hAB₁).deriv_eq,
        deriv_const_mul_add_const_mul_of_isLinearODE2SolutionOn h₁ h₂ A₁ B₁ hz]; ring
    have e3 : w₁ z * A₂ + w₂ z * B₂ = 0 := by rw [← hu20, hAB₂ z hz]; ring
    have e4 : deriv w₁ z * A₂ + deriv w₂ z * B₂ = 1 := by
      rw [← hu21, (eventuallyEq_of_mem (hD.mem_nhds hz) hAB₂).deriv_eq,
        deriv_const_mul_add_const_mul_of_isLinearODE2SolutionOn h₁ h₂ A₂ B₂ hz]; ring
    have : ODE.wronskian w₁ w₂ z * (A₁ * B₂ - A₂ * B₁) = 1 := by
      unfold ODE.wronskian
      linear_combination (deriv w₁ z * A₂ + deriv w₂ z * B₂) * e1 + e4 -
        (deriv w₁ z * A₁ + deriv w₂ z * B₁) * e3
    exact left_ne_zero_of_mul_eq_one this
  tfae_have 2 → 3 := by
    intro hW A B hAB
    have h0 := hAB z₀ hz₀
    have h1 : A * deriv w₁ z₀ + B * deriv w₂ z₀ = 0 := by
      rw [← deriv_const_mul_add_const_mul_of_isLinearODE2SolutionOn h₁ h₂ A B hz₀,
        (eventuallyEq_of_mem (hD.mem_nhds hz₀) hAB).deriv_eq]
      simp
    exact eq_zero_of_wronskian_ne_zero (hW z₀ hz₀) h0 h1
  tfae_have 3 → 1 := by
    intro hind
    by_cases hW : ODE.wronskian w₁ w₂ z₀ = 0
    · exfalso
      have key : ∀ A B : ℂ, A * w₁ z₀ + B * w₂ z₀ = 0 → A * deriv w₁ z₀ + B * deriv w₂ z₀ = 0 →
          A = 0 ∧ B = 0 := by
        intro A B h0 h1
        have hsol := h₁.linear_combination hD h₂ A B (r := 0) (fun z _ => by simp)
        refine hind A B fun z hz =>
            isLinearODE2SolutionOn_unique hD hD' hf hg hsol isLinearODE2SolutionOn_zero
          hz₀ h0 ?_ hz
        rw [deriv_const_mul_add_const_mul_of_isLinearODE2SolutionOn h₁ h₂ A B hz₀, h1, deriv_const']
      unfold ODE.wronskian at hW
      by_cases ha : w₂ z₀ = 0 ∧ w₁ z₀ = 0
      · by_cases hb : deriv w₂ z₀ = 0 ∧ deriv w₁ z₀ = 0
        · have := key 1 0 (by simp [ha.2]) (by simp [hb.2])
          simp at this
        · have := key (deriv w₂ z₀) (-deriv w₁ z₀) (by linear_combination hW) (by ring)
          exact hb ⟨this.1, neg_eq_zero.mp this.2⟩
      · have := key (w₂ z₀) (-w₁ z₀) (by ring) (by linear_combination -hW)
        exact ha ⟨this.1, neg_eq_zero.mp this.2⟩
    · exact isFundamentalPair_of_wronskian_ne_zero hD hD' hf hg h₁ h₂ hz₀ hW
  tfae_finish

/-! ## Equations with a parameter (§1.13(ii)) -/

/-- DLMF 1.13.7 and §1.13(ii): let `f(u, z)`, `g(u, z)` be continuous on `U × D`, analytic in
`z` for fixed `u` and in `u` for fixed `z`, and let `w(u, ·)` solve
`w'' + f(u, z) w' + g(u, z) w = 0` on `D` for each `u ∈ U`. If `w` and `∂w/∂z` are analytic in
`u` at a fixed `z₀ ∈ D`, then at each `z ∈ D` the functions `w`, `∂w/∂z` and `∂²w/∂z²` are
analytic in `u`. The domain `D` must be connected: initial data at `z₀` impose no
constraint on solutions on a different component. Its nonemptiness follows from `z₀ ∈ D`. -/
@[dlmf 1.13.E7, dlmf 1.13.ii]
theorem isLinearODE2SolutionOn_param_analytic {U : Set ℂ} (hU : IsOpen U) (hD : IsOpen D)
    (hDc : IsPreconnected D)
    {F G w : ℂ → ℂ → ℂ} (hF : ContinuousOn (Function.uncurry F) (U ×ˢ D))
    (hG : ContinuousOn (Function.uncurry G) (U ×ˢ D))
    (hFz : ∀ u ∈ U, DifferentiableOn ℂ (F u) D) (hGz : ∀ u ∈ U, DifferentiableOn ℂ (G u) D)
    (hFu : ∀ z ∈ D, DifferentiableOn ℂ (fun u => F u z) U)
    (hGu : ∀ z ∈ D, DifferentiableOn ℂ (fun u => G u z) U)
    (hw : ∀ u ∈ U, IsLinearODE2SolutionOn (F u) (G u) 0 (w u) D) {z₀ : ℂ} (hz₀ : z₀ ∈ D)
    (h₀ : DifferentiableOn ℂ (fun u => w u z₀) U)
    (h₁ : DifferentiableOn ℂ (fun u => deriv (w u) z₀) U) (z : ℂ) (hz : z ∈ D) :
    DifferentiableOn ℂ (fun u => w u z) U ∧ DifferentiableOn ℂ (fun u => deriv (w u) z) U ∧
      DifferentiableOn ℂ (fun u => deriv (deriv (w u)) z) U := by
  sorry

/-! ## Inhomogeneous equations (§1.13(iii)) -/

/-- DLMF 1.13.9: if `w₀` solves the inhomogeneous equation 1.13.8 and `w₁`, `w₂` are a
fundamental pair of 1.13.1 in the open set `D`, every solution of 1.13.8 is
`w₀ + A w₁ + B w₂`. -/
@[dlmf 1.13.E9]
theorem isLinearODE2SolutionOn_inhom_eq (hD : IsOpen D) {w₀ w₁ w₂ w : ℂ → ℂ}
    (h₀ : IsLinearODE2SolutionOn f g r w₀ D) (hfp : IsFundamentalPair f g w₁ w₂ D)
    (hw : IsLinearODE2SolutionOn f g r w D) :
    ∃ A B : ℂ, ∀ z ∈ D, w z = w₀ z + A * w₁ z + B * w₂ z := by
  have hd := hw.linear_combination hD h₀ 1 (-1) (r := 0) (fun z _ => by simp)
  obtain ⟨A, B, hAB⟩ := hfp.2.2 _ hd
  exact ⟨A, B, fun z hz => by linear_combination hAB z hz⟩

/-- The variation-of-parameters solution `w₂ P - w₁ Q` (with `P' = w₁ r/𝒲`, `Q' = w₂ r/𝒲`)
has derivative `w₂' P - w₁' Q`. -/
private lemma hasDerivAt_variationOfParameters {w₁ w₂ P Q : ℂ → ℂ} {z : ℂ}
    (h₁ : DifferentiableAt ℂ w₁ z)
    (h₂ : DifferentiableAt ℂ w₂ z) (hP : HasDerivAt P (w₁ z * r z / ODE.wronskian w₁ w₂ z) z)
    (hQ : HasDerivAt Q (w₂ z * r z / ODE.wronskian w₁ w₂ z) z) :
    HasDerivAt (fun y => w₂ y * P y - w₁ y * Q y) (deriv w₂ z * P z - deriv w₁ z * Q z) z := by
  refine ((h₂.hasDerivAt.mul hP).sub (h₁.hasDerivAt.mul hQ)).congr_deriv ?_
  ring

/-- DLMF 1.13.10 (variation of parameters): if `w₁`, `w₂` solve 1.13.1 on the open set `D` with
nonvanishing Wronskian `𝒲`, and `P`, `Q` are primitives of `w₁ r/𝒲` and `w₂ r/𝒲` on `D`
(the integrals of 1.13.10), then `w₀ = w₂ P - w₁ Q` solves the inhomogeneous equation 1.13.8. -/
@[dlmf 1.13.E10]
theorem isLinearODE2SolutionOn_varParam (hD : IsOpen D) {w₁ w₂ P Q : ℂ → ℂ}
    (h₁ : IsLinearODE2SolutionOn f g 0 w₁ D) (h₂ : IsLinearODE2SolutionOn f g 0 w₂ D)
    (hW : ∀ z ∈ D, ODE.wronskian w₁ w₂ z ≠ 0)
    (hP : ∀ z ∈ D, HasDerivAt P (w₁ z * r z / ODE.wronskian w₁ w₂ z) z)
    (hQ : ∀ z ∈ D, HasDerivAt Q (w₂ z * r z / ODE.wronskian w₁ w₂ z) z) :
    IsLinearODE2SolutionOn f g r (fun z => w₂ z * P z - w₁ z * Q z) D := by
  intro z hz
  have hd := hasDerivAt_variationOfParameters (h₁ z hz).1 (h₂ z hz).1 (hP z hz) (hQ z hz)
  have hev : deriv (fun y => w₂ y * P y - w₁ y * Q y) =ᶠ[𝓝 z]
      fun y => deriv w₂ y * P y - deriv w₁ y * Q y := by
    filter_upwards [hD.mem_nhds hz] with y hy
    exact (hasDerivAt_variationOfParameters (h₁ y hy).1 (h₂ y hy).1 (hP y hy) (hQ y hy)).deriv
  refine ⟨hd.differentiableAt, ((((h₂ z hz).2.mul (hP z hz))).sub
    (((h₁ z hz).2.mul (hQ z hz)))).congr_of_eventuallyEq hev |>.congr_deriv ?_⟩
  rw [hd.deriv]
  have hWz := hW z hz
  have key : deriv w₂ z * (w₁ z * r z / ODE.wronskian w₁ w₂ z) -
      deriv w₁ z * (w₂ z * r z / ODE.wronskian w₁ w₂ z) = r z := by
    rw [mul_div_assoc', mul_div_assoc', ← sub_div, div_eq_iff hWz]
    unfold ODE.wronskian
    ring
  simp only [Pi.zero_apply]
  linear_combination key

/-- DLMF §1.13(iii): on a simply connected domain `D`, with `f`, `g`, `r` analytic in `D`, the
inhomogeneous equation 1.13.8 has a solution with prescribed `w(z₀)`, `w'(z₀)` (so infinitely
many analytic solutions). -/
@[dlmf 1.13.E8, dlmf 1.13.iii]
theorem exists_isLinearODE2SolutionOn_inhom (hD : IsOpen D) (hsc : IsSimplyConnected D)
    (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D) (hr : DifferentiableOn ℂ r D)
    {z₀ : ℂ} (hz₀ : z₀ ∈ D) (w₀ w₁ : ℂ) :
    ∃ w, IsLinearODE2SolutionOn f g r w D ∧ w z₀ = w₀ ∧ deriv w z₀ = w₁ := by
  obtain ⟨u₁, h₁, h10, h11⟩ := exists_isLinearODE2SolutionOn hD hsc hf hg hz₀ 1 0
  obtain ⟨u₂, h₂, h20, h21⟩ := exists_isLinearODE2SolutionOn hD hsc hf hg hz₀ 0 1
  have hDc : IsPreconnected D := hsc.isPathConnected.isConnected.isPreconnected
  obtain ⟨F, hF, -⟩ := exists_primitive_of_isSimplyConnected hD hsc hf hz₀
  obtain ⟨c, hc⟩ := wronskian_eq_mul_exp hD hDc hF h₁ h₂
  have hc0 : c ≠ 0 := by
    intro h
    have := hc z₀ hz₀
    simp [h, ODE.wronskian, h10, h11, h20, h21] at this
  have hW : ∀ z ∈ D, ODE.wronskian u₁ u₂ z ≠ 0 := fun z hz => by
    rw [hc z hz]; exact mul_ne_zero hc0 (Complex.exp_ne_zero _)
  have ha₁ := h₁.analyticOnNhd hD
  have ha₂ := h₂.analyticOnNhd hD
  have hWd : DifferentiableOn ℂ (ODE.wronskian u₁ u₂) D := by
    unfold ODE.wronskian
    exact (ha₁.differentiableOn.mul ha₂.deriv.differentiableOn).sub
      (ha₂.differentiableOn.mul ha₁.deriv.differentiableOn)
  obtain ⟨P, hP, hP0⟩ := exists_primitive_of_isSimplyConnected hD hsc
    ((ha₁.differentiableOn.mul hr).div hWd hW) hz₀
  obtain ⟨Q, hQ, hQ0⟩ := exists_primitive_of_isSimplyConnected hD hsc
    ((ha₂.differentiableOn.mul hr).div hWd hW) hz₀
  have hp := isLinearODE2SolutionOn_varParam hD h₁ h₂ hW hP hQ
  have hhom := h₁.linear_combination hD h₂ w₀ w₁ (r := 0) (fun z _ => by simp)
  have htot := hp.linear_combination hD hhom 1 1 (r := r) (fun z _ => by simp)
  refine ⟨_, htot, by simp [hP0, hQ0, h10, h20], ?_⟩
  rw [deriv_const_mul_add_const_mul_of_isLinearODE2SolutionOn hp hhom 1 1 hz₀,
    deriv_const_mul_add_const_mul_of_isLinearODE2SolutionOn h₁ h₂ w₀ w₁ hz₀,
    (hasDerivAt_variationOfParameters (h₁ z₀ hz₀).1 (h₂ z₀ hz₀).1 (hP z₀ hz₀)
      (hQ z₀ hz₀)).deriv, hP0, hQ0, h11, h21]
  ring

end DLMF.AlgebraicAnalytic
