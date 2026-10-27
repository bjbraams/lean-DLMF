/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.ODE.Defs
public import DLMFMathlib.Analysis.ODE.P1oEntireLinear
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Linear second-order differential equations (DLMF §§1.13(i)–1.13(iii))

For `w'' + f(z) w' + g(z) w = r(z)` on an open set `D ⊆ ℂ` with analytic coefficients
(`IsLinODE2SolOn f g r w D`):

* existence of solutions with prescribed `w(z₀)`, `w'(z₀)` on a simply connected domain
  (admitted; proved for entire coefficients from `ODE.exists_entire_solution_linear_ode'`), and
  uniqueness on a connected open set (from `ODE.eqOn_of_ode`);
* linear combinations of solutions, fundamental pairs from initial data 1.13.3 or from a
  nonvanishing Wronskian at one point;
* the two-argument Wronskian as a determinant (1.13.4), Abel's identity 1.13.5 (given a
  primitive `F` of `f`, so that `e^{-∫ f} = e^{-F}`), and the equivalences 1.13.6;
* parameter dependence 1.13.7 (admitted);
* the inhomogeneous equation: existence (admitted), the general solution 1.13.9 and variation
  of parameters 1.13.10 (given primitives of `w₁ r/𝒲` and `w₂ r/𝒲`).
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DLMF.AlgebraicAnalytic

variable {f g r : ℂ → ℂ} {D : Set ℂ}

/-! ## Basic facts about solutions -/

/-- A solution satisfies the differential equation with `deriv (deriv w)`. -/
theorem IsLinODE2SolOn.deriv_deriv {w : ℂ → ℂ} (hw : IsLinODE2SolOn f g r w D) {z : ℂ}
    (hz : z ∈ D) : deriv (deriv w) z = r z - f z * deriv w z - g z * w z :=
  (hw z hz).2.deriv

/-- A solution is complex differentiable on `D`. -/
theorem IsLinODE2SolOn.differentiableOn {w : ℂ → ℂ} (hw : IsLinODE2SolOn f g r w D) :
    DifferentiableOn ℂ w D := fun z hz => (hw z hz).1.differentiableWithinAt

/-- A solution on an open set is analytic there. -/
theorem IsLinODE2SolOn.analyticOnNhd {w : ℂ → ℂ} (hD : IsOpen D) (hw : IsLinODE2SolOn f g r w D) :
    AnalyticOnNhd ℂ w D := hw.differentiableOn.analyticOnNhd hD

/-- Linear combinations: if `w` solves the equation with right side `r₁` and `v` with `r₂`, then
`A w + B v` solves it with right side `A r₁ + B r₂`. -/
theorem IsLinODE2SolOn.linComb {r₁ r₂ w v : ℂ → ℂ} (hD : IsOpen D) (hw : IsLinODE2SolOn f g r₁ w D)
    (hv : IsLinODE2SolOn f g r₂ v D) (A B : ℂ) (hr : ∀ z ∈ D, r z = A * r₁ z + B * r₂ z) :
    IsLinODE2SolOn f g r (fun z => A * w z + B * v z) D := by
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
lemma isLinODE2SolOn_zero : IsLinODE2SolOn f g 0 (fun _ => 0) D := fun z _ => by
  refine ⟨differentiableAt_const _, ?_⟩
  simp only [deriv_const', Pi.zero_apply, mul_zero, sub_zero]
  exact hasDerivAt_const z 0

/-- The derivative of a linear combination of solutions, at a point of the open set `D`. -/
lemma g1d_deriv_linComb {w v : ℂ → ℂ} {r₁ r₂ : ℂ → ℂ} (hw : IsLinODE2SolOn f g r₁ w D)
    (hv : IsLinODE2SolOn f g r₂ v D) (A B : ℂ) {z : ℂ} (hz : z ∈ D) :
    deriv (fun y => A * w y + B * v y) z = A * deriv w z + B * deriv v z :=
  (((hw z hz).1.hasDerivAt.const_mul A).add ((hv z hz).1.hasDerivAt.const_mul B)).deriv

/-! ## Existence and uniqueness (§1.13(i)) -/

/-- DLMF §1.13(i): on a simply connected domain `D`, with `f`, `g` analytic in `D`, the equation
1.13.1 has a solution with prescribed `w(z₀)` and `w'(z₀)` at any `z₀ ∈ D` (so infinitely many
analytic solutions). -/
@[dlmf 1.13.i]
theorem exists_isLinODE2SolOn (hD : IsOpen D) (hsc : IsSimplyConnected D)
    (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D) {z₀ : ℂ} (hz₀ : z₀ ∈ D)
    (w₀ w₁ : ℂ) : ∃ w, IsLinODE2SolOn f g 0 w D ∧ w z₀ = w₀ ∧ deriv w z₀ = w₁ := by
  sorry

/-- DLMF §1.13(i) for entire coefficients: `w'' + f w' + g w = 0` has an entire solution with
prescribed `w(z₀)`, `w'(z₀)`. -/
@[dlmf 1.13.i]
theorem exists_isLinODE2SolOn_univ (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (z₀ w₀ w₁ : ℂ) : ∃ w, IsLinODE2SolOn f g 0 w univ ∧ w z₀ = w₀ ∧ deriv w z₀ = w₁ := by
  obtain ⟨w, hw, hode, h0, h1⟩ := ODE.exists_entire_solution_linear_ode' (p := fun z => -f z)
    (q := fun z => -g z) hf.neg hg.neg z₀ w₀ w₁
  refine ⟨w, fun z _ => ⟨hw z, (hode z).congr_deriv ?_⟩, h0, h1⟩
  simp only [Pi.zero_apply]
  ring

/-- DLMF §1.13(i): a solution of 1.13.1 on a connected open set `D` (with `f`, `g` analytic in
`D`) is uniquely determined by `w(z₀)` and `w'(z₀)`. -/
@[dlmf 1.13.i]
theorem isLinODE2SolOn_unique (hD : IsOpen D) (hD' : IsPreconnected D)
    (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D) {w v : ℂ → ℂ}
    (hw : IsLinODE2SolOn f g 0 w D) (hv : IsLinODE2SolOn f g 0 v D) {z₀ : ℂ} (hz₀ : z₀ ∈ D)
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
    wronskianN ![w₁, w₂] z = wronskian w₁ w₂ z := by
  simp [wronskianN, wronskian, Matrix.det_fin_two]

/-- DLMF §1.13(i): if the Wronskian of two solutions does not vanish at one point `z₀` of the
connected open set `D`, they are a fundamental pair in `D`. -/
@[dlmf 1.13.E2]
theorem isFundamentalPair_of_wronskian_ne_zero (hD : IsOpen D) (hD' : IsPreconnected D)
    (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D) {w₁ w₂ : ℂ → ℂ}
    (h₁ : IsLinODE2SolOn f g 0 w₁ D) (h₂ : IsLinODE2SolOn f g 0 w₂ D) {z₀ : ℂ} (hz₀ : z₀ ∈ D)
    (hW : wronskian w₁ w₂ z₀ ≠ 0) : IsFundamentalPair f g w₁ w₂ D := by
  refine ⟨h₁, h₂, fun w hw => ?_⟩
  set W := wronskian w₁ w₂ z₀
  set A := (w z₀ * deriv w₂ z₀ - w₂ z₀ * deriv w z₀) / W
  set B := (w₁ z₀ * deriv w z₀ - w z₀ * deriv w₁ z₀) / W
  have hsol := h₁.linComb hD h₂ A B (r := 0) (fun z _ => by simp)
  refine ⟨A, B, fun z hz => isLinODE2SolOn_unique hD hD' hf hg hw hsol hz₀ ?_ ?_ hz⟩
  · simp only [A, B]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hW]
    simp only [W, wronskian]
    ring
  · rw [g1d_deriv_linComb h₁ h₂ A B hz₀]
    simp only [A, B]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hW]
    simp only [W, wronskian]
    ring

/-- DLMF 1.13.3: solutions with `w₁(z₀) = 1`, `w₁'(z₀) = 0`, `w₂(z₀) = 0`, `w₂'(z₀) = 1` are a
fundamental pair in the connected open set `D`. -/
@[dlmf 1.13.E3]
theorem isFundamentalPair_of_initial (hD : IsOpen D) (hD' : IsPreconnected D)
    (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D) {w₁ w₂ : ℂ → ℂ}
    (h₁ : IsLinODE2SolOn f g 0 w₁ D) (h₂ : IsLinODE2SolOn f g 0 w₂ D) {z₀ : ℂ} (hz₀ : z₀ ∈ D)
    (h10 : w₁ z₀ = 1) (h11 : deriv w₁ z₀ = 0) (h20 : w₂ z₀ = 0) (h21 : deriv w₂ z₀ = 1) :
    IsFundamentalPair f g w₁ w₂ D :=
  isFundamentalPair_of_wronskian_ne_zero hD hD' hf hg h₁ h₂ hz₀ (by simp [wronskian, *])

/-- DLMF 1.13.3: on a simply connected domain, a fundamental pair exists. -/
@[dlmf 1.13.E3]
theorem exists_isFundamentalPair (hD : IsOpen D) (hsc : IsSimplyConnected D)
    (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D) :
    ∃ w₁ w₂, IsFundamentalPair f g w₁ w₂ D := by
  obtain ⟨z₀, hz₀⟩ := hsc.nonempty
  obtain ⟨w₁, h₁, h10, h11⟩ := exists_isLinODE2SolOn hD hsc hf hg hz₀ 1 0
  obtain ⟨w₂, h₂, h20, h21⟩ := exists_isLinODE2SolOn hD hsc hf hg hz₀ 0 1
  exact ⟨w₁, w₂, isFundamentalPair_of_initial hD hsc.isPathConnected.isConnected.isPreconnected
    hf hg h₁ h₂ hz₀ h10 h11 h20 h21⟩

/-- The derivative of the Wronskian of two solutions of 1.13.1: `𝒲' = -f 𝒲`. -/
lemma g1d_hasDerivAt_wronskian {w₁ w₂ : ℂ → ℂ} (h₁ : IsLinODE2SolOn f g 0 w₁ D)
    (h₂ : IsLinODE2SolOn f g 0 w₂ D) {z : ℂ} (hz : z ∈ D) :
    HasDerivAt (wronskian w₁ w₂) (-f z * wronskian w₁ w₂ z) z := by
  have := (((h₁ z hz).1.hasDerivAt.mul (h₂ z hz).2)).sub
    ((h₂ z hz).1.hasDerivAt.mul (h₁ z hz).2)
  refine this.congr_deriv ?_
  simp only [wronskian, Pi.zero_apply]
  ring

/-- DLMF 1.13.5 (Abel's identity): if `F` is a primitive of `f` on the connected open set `D`
(so that `e^{-∫ f dz} = e^{-F}`), the Wronskian of two solutions of 1.13.1 is `c e^{-F(z)}`
with `c` independent of `z`. -/
@[dlmf 1.13.E5]
theorem wronskian_eq_mul_exp (hD : IsOpen D) (hD' : IsPreconnected D) {F : ℂ → ℂ}
    (hF : ∀ z ∈ D, HasDerivAt F (f z) z) {w₁ w₂ : ℂ → ℂ} (h₁ : IsLinODE2SolOn f g 0 w₁ D)
    (h₂ : IsLinODE2SolOn f g 0 w₂ D) :
    ∃ c : ℂ, ∀ z ∈ D, wronskian w₁ w₂ z = c * Complex.exp (-F z) := by
  have hd : ∀ z ∈ D, HasDerivAt (fun z => wronskian w₁ w₂ z * Complex.exp (F z)) 0 z := by
    intro z hz
    refine ((g1d_hasDerivAt_wronskian h₁ h₂ hz).mul ((hF z hz).cexp)).congr_deriv ?_
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
    {w₁ w₂ : ℂ → ℂ} (h₁ : IsLinODE2SolOn 0 g 0 w₁ D) (h₂ : IsLinODE2SolOn 0 g 0 w₂ D)
    {z z' : ℂ} (hz : z ∈ D) (hz' : z' ∈ D) : wronskian w₁ w₂ z = wronskian w₁ w₂ z' := by
  obtain ⟨c, hc⟩ := wronskian_eq_mul_exp hD hD' (F := fun _ => 0)
    (fun z _ => by simpa using hasDerivAt_const z (0 : ℂ)) h₁ h₂
  rw [hc z hz, hc z' hz']

/-- The data of a linear combination of solutions at a point vanish only trivially if the
Wronskian there does not vanish. -/
lemma g1d_eq_zero_of_wronskian {w₁ w₂ : ℂ → ℂ} {A B z : ℂ} (hW : wronskian w₁ w₂ z ≠ 0)
    (h0 : A * w₁ z + B * w₂ z = 0) (h1 : A * deriv w₁ z + B * deriv w₂ z = 0) :
    A = 0 ∧ B = 0 := by
  unfold wronskian at hW
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
    (h₁ : IsLinODE2SolOn f g 0 w₁ D) (h₂ : IsLinODE2SolOn f g 0 w₂ D) :
    List.TFAE [IsFundamentalPair f g w₁ w₂ D, ∀ z ∈ D, wronskian w₁ w₂ z ≠ 0,
      ∀ A B : ℂ, (∀ z ∈ D, A * w₁ z + B * w₂ z = 0) → A = 0 ∧ B = 0] := by
  have hD' : IsPreconnected D := hsc.isPathConnected.isConnected.isPreconnected
  obtain ⟨z₀, hz₀⟩ := hsc.nonempty
  tfae_have 1 → 2 := by
    rintro ⟨-, -, hall⟩ z hz
    obtain ⟨u₁, hu₁, hu10, hu11⟩ := exists_isLinODE2SolOn hD hsc hf hg hz 1 0
    obtain ⟨u₂, hu₂, hu20, hu21⟩ := exists_isLinODE2SolOn hD hsc hf hg hz 0 1
    obtain ⟨A₁, B₁, hAB₁⟩ := hall u₁ hu₁
    obtain ⟨A₂, B₂, hAB₂⟩ := hall u₂ hu₂
    have e1 : w₁ z * A₁ + w₂ z * B₁ = 1 := by rw [← hu10, hAB₁ z hz]; ring
    have e2 : deriv w₁ z * A₁ + deriv w₂ z * B₁ = 0 := by
      rw [← hu11, (eventuallyEq_of_mem (hD.mem_nhds hz) hAB₁).deriv_eq,
        g1d_deriv_linComb h₁ h₂ A₁ B₁ hz]; ring
    have e3 : w₁ z * A₂ + w₂ z * B₂ = 0 := by rw [← hu20, hAB₂ z hz]; ring
    have e4 : deriv w₁ z * A₂ + deriv w₂ z * B₂ = 1 := by
      rw [← hu21, (eventuallyEq_of_mem (hD.mem_nhds hz) hAB₂).deriv_eq,
        g1d_deriv_linComb h₁ h₂ A₂ B₂ hz]; ring
    have : wronskian w₁ w₂ z * (A₁ * B₂ - A₂ * B₁) = 1 := by
      unfold wronskian
      linear_combination (deriv w₁ z * A₂ + deriv w₂ z * B₂) * e1 + e4 -
        (deriv w₁ z * A₁ + deriv w₂ z * B₁) * e3
    exact left_ne_zero_of_mul_eq_one this
  tfae_have 2 → 3 := by
    intro hW A B hAB
    have h0 := hAB z₀ hz₀
    have h1 : A * deriv w₁ z₀ + B * deriv w₂ z₀ = 0 := by
      rw [← g1d_deriv_linComb h₁ h₂ A B hz₀,
        (eventuallyEq_of_mem (hD.mem_nhds hz₀) hAB).deriv_eq]
      simp
    exact g1d_eq_zero_of_wronskian (hW z₀ hz₀) h0 h1
  tfae_have 3 → 1 := by
    intro hind
    by_cases hW : wronskian w₁ w₂ z₀ = 0
    · exfalso
      have key : ∀ A B : ℂ, A * w₁ z₀ + B * w₂ z₀ = 0 → A * deriv w₁ z₀ + B * deriv w₂ z₀ = 0 →
          A = 0 ∧ B = 0 := by
        intro A B h0 h1
        have hsol := h₁.linComb hD h₂ A B (r := 0) (fun z _ => by simp)
        refine hind A B fun z hz => isLinODE2SolOn_unique hD hD' hf hg hsol isLinODE2SolOn_zero
          hz₀ h0 ?_ hz
        rw [g1d_deriv_linComb h₁ h₂ A B hz₀, h1, deriv_const']
      unfold wronskian at hW
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
analytic in `u`. -/
@[dlmf 1.13.E7, dlmf 1.13.ii]
theorem isLinODE2SolOn_param_analytic {U : Set ℂ} (hU : IsOpen U) (hD : IsOpen D)
    {F G w : ℂ → ℂ → ℂ} (hF : ContinuousOn (Function.uncurry F) (U ×ˢ D))
    (hG : ContinuousOn (Function.uncurry G) (U ×ˢ D))
    (hFz : ∀ u ∈ U, DifferentiableOn ℂ (F u) D) (hGz : ∀ u ∈ U, DifferentiableOn ℂ (G u) D)
    (hFu : ∀ z ∈ D, DifferentiableOn ℂ (fun u => F u z) U)
    (hGu : ∀ z ∈ D, DifferentiableOn ℂ (fun u => G u z) U)
    (hw : ∀ u ∈ U, IsLinODE2SolOn (F u) (G u) 0 (w u) D) {z₀ : ℂ} (hz₀ : z₀ ∈ D)
    (h₀ : DifferentiableOn ℂ (fun u => w u z₀) U)
    (h₁ : DifferentiableOn ℂ (fun u => deriv (w u) z₀) U) (z : ℂ) (hz : z ∈ D) :
    DifferentiableOn ℂ (fun u => w u z) U ∧ DifferentiableOn ℂ (fun u => deriv (w u) z) U ∧
      DifferentiableOn ℂ (fun u => deriv (deriv (w u)) z) U := by
  sorry

/-! ## Inhomogeneous equations (§1.13(iii)) -/

/-- DLMF §1.13(iii): on a simply connected domain `D`, with `f`, `g`, `r` analytic in `D`, the
inhomogeneous equation 1.13.8 has a solution with prescribed `w(z₀)`, `w'(z₀)` (so infinitely
many analytic solutions). -/
@[dlmf 1.13.E8, dlmf 1.13.iii]
theorem exists_isLinODE2SolOn_inhom (hD : IsOpen D) (hsc : IsSimplyConnected D)
    (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D) (hr : DifferentiableOn ℂ r D)
    {z₀ : ℂ} (hz₀ : z₀ ∈ D) (w₀ w₁ : ℂ) :
    ∃ w, IsLinODE2SolOn f g r w D ∧ w z₀ = w₀ ∧ deriv w z₀ = w₁ := by
  sorry

/-- DLMF 1.13.9: if `w₀` solves the inhomogeneous equation 1.13.8 and `w₁`, `w₂` are a
fundamental pair of 1.13.1 in the open set `D`, every solution of 1.13.8 is
`w₀ + A w₁ + B w₂`. -/
@[dlmf 1.13.E9]
theorem isLinODE2SolOn_inhom_eq (hD : IsOpen D) {w₀ w₁ w₂ w : ℂ → ℂ}
    (h₀ : IsLinODE2SolOn f g r w₀ D) (hfp : IsFundamentalPair f g w₁ w₂ D)
    (hw : IsLinODE2SolOn f g r w D) :
    ∃ A B : ℂ, ∀ z ∈ D, w z = w₀ z + A * w₁ z + B * w₂ z := by
  have hd := hw.linComb hD h₀ 1 (-1) (r := 0) (fun z _ => by simp)
  obtain ⟨A, B, hAB⟩ := hfp.2.2 _ hd
  exact ⟨A, B, fun z hz => by linear_combination hAB z hz⟩

/-- The variation-of-parameters solution `w₂ P - w₁ Q` (with `P' = w₁ r/𝒲`, `Q' = w₂ r/𝒲`)
has derivative `w₂' P - w₁' Q`. -/
lemma g1d_hasDerivAt_varParam {w₁ w₂ P Q : ℂ → ℂ} {z : ℂ} (h₁ : DifferentiableAt ℂ w₁ z)
    (h₂ : DifferentiableAt ℂ w₂ z) (hP : HasDerivAt P (w₁ z * r z / wronskian w₁ w₂ z) z)
    (hQ : HasDerivAt Q (w₂ z * r z / wronskian w₁ w₂ z) z) :
    HasDerivAt (fun y => w₂ y * P y - w₁ y * Q y) (deriv w₂ z * P z - deriv w₁ z * Q z) z := by
  refine ((h₂.hasDerivAt.mul hP).sub (h₁.hasDerivAt.mul hQ)).congr_deriv ?_
  ring

/-- DLMF 1.13.10 (variation of parameters): if `w₁`, `w₂` solve 1.13.1 on the open set `D` with
nonvanishing Wronskian `𝒲`, and `P`, `Q` are primitives of `w₁ r/𝒲` and `w₂ r/𝒲` on `D`
(the integrals of 1.13.10), then `w₀ = w₂ P - w₁ Q` solves the inhomogeneous equation 1.13.8. -/
@[dlmf 1.13.E10]
theorem isLinODE2SolOn_varParam (hD : IsOpen D) {w₁ w₂ P Q : ℂ → ℂ}
    (h₁ : IsLinODE2SolOn f g 0 w₁ D) (h₂ : IsLinODE2SolOn f g 0 w₂ D)
    (hW : ∀ z ∈ D, wronskian w₁ w₂ z ≠ 0)
    (hP : ∀ z ∈ D, HasDerivAt P (w₁ z * r z / wronskian w₁ w₂ z) z)
    (hQ : ∀ z ∈ D, HasDerivAt Q (w₂ z * r z / wronskian w₁ w₂ z) z) :
    IsLinODE2SolOn f g r (fun z => w₂ z * P z - w₁ z * Q z) D := by
  intro z hz
  have hd := g1d_hasDerivAt_varParam (h₁ z hz).1 (h₂ z hz).1 (hP z hz) (hQ z hz)
  have hev : deriv (fun y => w₂ y * P y - w₁ y * Q y) =ᶠ[𝓝 z]
      fun y => deriv w₂ y * P y - deriv w₁ y * Q y := by
    filter_upwards [hD.mem_nhds hz] with y hy
    exact (g1d_hasDerivAt_varParam (h₁ y hy).1 (h₂ y hy).1 (hP y hy) (hQ y hy)).deriv
  refine ⟨hd.differentiableAt, ((((h₂ z hz).2.mul (hP z hz))).sub
    (((h₁ z hz).2.mul (hQ z hz)))).congr_of_eventuallyEq hev |>.congr_deriv ?_⟩
  rw [hd.deriv]
  have hWz := hW z hz
  have key : deriv w₂ z * (w₁ z * r z / wronskian w₁ w₂ z) -
      deriv w₁ z * (w₂ z * r z / wronskian w₁ w₂ z) = r z := by
    rw [mul_div_assoc', mul_div_assoc', ← sub_div, div_eq_iff hWz]
    unfold wronskian
    ring
  simp only [Pi.zero_apply]
  linear_combination key

end DLMF.AlgebraicAnalytic
