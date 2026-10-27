/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.SolutionsDefs
public import DLMF.Painleve.Defs
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

/-!
# Reductions of partial differential equations (DLMF §32.13)

The PDE predicates `IsMKdVOn`, `IsKdVOn`, `IsSineGordonOn`, `IsBoussinesqOn` are in
`DLMF.Painleve.SolutionsDefs`. The scaling reductions of mKdV and KdV to `PII` (32.13.2,
32.13.4; verified symbolically for every `α`), the similarity reduction of KdV (32.13.5), the
scaling reduction of sine-Gordon (32.13.7) and the travelling-wave reduction of Boussinesq
(32.13.9–32.13.10) are proved as PDE statements, with the principal branch of `(3t)^{-1/3}`
(`3t` in the slit plane), from the chain rule and `d/dt (3t)^{-1/3} = -((3t)^{-1/3})⁴`.

The ODE parts are proved: the sine-Gordon reduction `zv'' + v' = sin v` gives `PIII` with
`α = -β = 1/2`, `γ = δ = 0` for `w = exp(-iv)` (§32.13(ii)); the similarity reduction of KdV,
`W'' = -3W² + λz + C`, is solved by `W(z) = -2μ²w(μz - C/(2μ⁴))` with `w` a solution of `PI`
and `μ⁵ = -λ/2` (the "expressible in terms of `PI`" of §32.13(i), for `λ ≠ 0`); and the
Boussinesq travelling-wave equation 32.13.10 with `A ≠ 0` is solved by
`v(z) = λ²w(λz + μ) - (c² - 1)/12` with `w` a solution of `PI`, `λ⁵ = A` (§32.13(iii)). The
case `A = 0` (Weierstrass function) is not formalized.
-/

@[expose] public noncomputable section

open Set Complex Filter
open scoped Topology

namespace DLMF.Painleve

/-- The third derivative of a solution of a second-order equation, from the derivative of
the right-hand side along the solution. -/
private lemma p3b_deriv3 {F : ℂ → ℂ → ℂ → ℂ} {W : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h : IsODE2SolutionOn F W U) {y G : ℂ} (hy : y ∈ U)
    (hG : HasDerivAt (fun y => F y (W y) (deriv W y)) G y) :
    deriv (deriv (deriv W)) y = G := by
  have he : deriv (deriv W) =ᶠ[𝓝 y] fun y => F y (W y) (deriv W y) := by
    filter_upwards [hU.mem_nhds hy] with x hx using h.ode hx
  rw [he.deriv_eq, hG.deriv]

/-- Solutions of a second-order equation on an open set are smooth there. -/
private lemma p3b_contDiffAt {F : ℂ → ℂ → ℂ → ℂ} {W : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h : IsODE2SolutionOn F W U) {y : ℂ} (hy : y ∈ U) (n : ℕ) : ContDiffAt ℂ n W y :=
  (DifferentiableOn.contDiffOn (fun x hx => (h.differentiableAt x hx).differentiableWithinAt)
    hU).contDiffAt (hU.mem_nhds hy)

/-- Three successive explicit derivatives on an open set give the third iterated derivative. -/
private lemma p3b_iteratedDeriv_three {f0 f1 f2 f3 : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (h1 : ∀ y ∈ V, HasDerivAt f0 (f1 y) y) (h2 : ∀ y ∈ V, HasDerivAt f1 (f2 y) y)
    (h3 : ∀ y ∈ V, HasDerivAt f2 (f3 y) y) {y : ℂ} (hy : y ∈ V) :
    iteratedDeriv 3 f0 y = f3 y := by
  have E1 : ∀ x ∈ V, deriv f0 =ᶠ[𝓝 x] f1 := fun x hx => by
    filter_upwards [hV.mem_nhds hx] with z hz using (h1 z hz).deriv
  have E2 : ∀ x ∈ V, deriv (deriv f0) =ᶠ[𝓝 x] f2 := fun x hx => by
    filter_upwards [hV.mem_nhds hx] with z hz
    rw [(E1 z hz).deriv_eq, (h2 z hz).deriv]
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, (E2 y hy).deriv_eq,
    (h3 y hy).deriv]

/-- The derivative of the principal power `(3t)^{-1/3}` is `-((3t)^{-1/3})⁴`. -/
private lemma p3b_hasDerivAt_r {t : ℂ} (ht : 3 * t ∈ slitPlane) :
    HasDerivAt (fun t : ℂ => (3 * t) ^ (-1 / 3 : ℂ)) (-((3 * t) ^ (-1 / 3 : ℂ)) ^ 4) t := by
  have h3 : HasDerivAt (fun t : ℂ => 3 * t) 3 t := by
    simpa using (hasDerivAt_id t).const_mul (3 : ℂ)
  refine (HasDerivAt.cpow_const (c := (-1 / 3 : ℂ)) h3 ht).congr_deriv ?_
  rw [show (-1 / 3 : ℂ) - 1 = ((4 : ℕ) : ℂ) * (-1 / 3) by push_cast; ring, cpow_nat_mul]
  ring
/-- Scaling the variable of a function with a derivative. -/
private lemma p3b_scale {A A' : ℂ → ℂ} {R K x : ℂ} (h : HasDerivAt A (A' (x * R)) (x * R)) :
    HasDerivAt (fun x => K * A (x * R)) (K * R * A' (x * R)) x := by
  have := (h.comp x (hasDerivAt_mul_const R)).const_mul K
  exact this.congr_deriv (by ring)


/-- DLMF 32.13.2: if `w` solves `PII` with parameter `α` on `U`, then
`v(x, t) = (3t)^{-1/3}w(x(3t)^{-1/3})` solves the mKdV equation 32.13.1 wherever `3t` is in the
slit plane and `x(3t)^{-1/3} ∈ U` (principal branch). -/
@[dlmf 32.13.E2]
theorem mKdV_scalingReduction {α : ℂ} {w : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hw : IsPainleveIIOn α w U) :
    IsMKdVOn (fun x t => (3 * t) ^ (-1 / 3 : ℂ) * w (x * (3 * t) ^ (-1 / 3 : ℂ)))
      {p | 3 * p.2 ∈ slitPlane ∧ p.1 * (3 * p.2) ^ (-1 / 3 : ℂ) ∈ U} := by
  have hd : DifferentiableOn ℂ w U := fun y hy => (hw.differentiableAt y hy).differentiableWithinAt
  have hw2 : ∀ y ∈ U, HasDerivAt (fun y => 2 * w y ^ 3 + y * w y + α)
      (6 * w y ^ 2 * deriv w y + w y + y * deriv w y) y := fun y hy => by
    have := ((((hw.hasDerivAt hy).pow 3).const_mul 2).add ((hasDerivAt_id y).mul
      (hw.hasDerivAt hy))).add_const α
    exact this.congr_deriv (by simp; ring)
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · exact contDiffAt_const.mul (((hd.contDiffOn hU).contDiffAt (hU.mem_nhds hp.2)).comp p.1
      (contDiffAt_id.mul contDiffAt_const))
  · exact (p3b_hasDerivAt_r hp.1).differentiableAt.mul ((hw.differentiableAt _ hp.2).comp p.2
      (((p3b_hasDerivAt_r hp.1).const_mul p.1).differentiableAt))
  · obtain ⟨hp1, hp2⟩ := hp
    set R := (3 * p.2) ^ (-1 / 3 : ℂ) with hR
    have hin : HasDerivAt (fun t : ℂ => p.1 * (3 * t) ^ (-1 / 3 : ℂ)) (p.1 * -R ^ 4) p.2 :=
      (p3b_hasDerivAt_r hp1).const_mul p.1
    have hc : HasDerivAt (fun t : ℂ => w (p.1 * (3 * t) ^ (-1 / 3 : ℂ)))
        (deriv w (p.1 * R) * (p.1 * -R ^ 4)) p.2 := (hw.hasDerivAt hp2).comp p.2 hin
    have ht : HasDerivAt (fun t : ℂ => (3 * t) ^ (-1 / 3 : ℂ) * w (p.1 * (3 * t) ^ (-1 / 3 : ℂ)))
        (-R ^ 4 * w (p.1 * R) + R * (deriv w (p.1 * R) * (p.1 * -R ^ 4))) p.2 :=
      (p3b_hasDerivAt_r hp1).mul hc
    have hV : IsOpen {x : ℂ | x * R ∈ U} := hU.preimage (continuous_id.mul continuous_const)
    have hlin : ∀ x : ℂ, HasDerivAt (fun x => x * R) R x := fun x => hasDerivAt_mul_const R
    have h1 : ∀ x ∈ {x : ℂ | x * R ∈ U}, HasDerivAt (fun x => R * w (x * R))
        (R * (deriv w (x * R) * R)) x := fun x hx =>
      ((hw.hasDerivAt hx).comp x (hlin x)).const_mul R
    have h2 : ∀ x ∈ {x : ℂ | x * R ∈ U}, HasDerivAt (fun x => R * (deriv w (x * R) * R))
        (R * ((2 * w (x * R) ^ 3 + x * R * w (x * R) + α) * R * R)) x := fun x hx => by
      have hd2 : HasDerivAt (deriv w) (2 * w (x * R) ^ 3 + x * R * w (x * R) + α) (x * R) :=
        hw.hasDerivAt_deriv _ hx
      exact ((hd2.comp x (hlin x)).mul_const R).const_mul R
    have h3 : ∀ x ∈ {x : ℂ | x * R ∈ U},
        HasDerivAt (fun x => R * ((2 * w (x * R) ^ 3 + x * R * w (x * R) + α) * R * R))
        (R * ((6 * w (x * R) ^ 2 * deriv w (x * R) + w (x * R) + x * R * deriv w (x * R)) * R *
          R * R)) x := fun x hx => by
      have hd3 := hw2 _ hx
      have := (((hd3.comp x (hlin x)).mul_const R).mul_const R).const_mul R
      exact this
    rw [ht.deriv, (h1 p.1 hp2).deriv, p3b_iteratedDeriv_three hV h1 h2 h3 hp2]
    ring


/-- DLMF 32.13.4: if `w` solves `PII` (any `α`) on `U`, then
`u(x, t) = -(3t)^{-2/3}(w'(z) + w(z)²)`, `z = x(3t)^{-1/3}`, solves the KdV equation 32.13.3
wherever `3t` is in the slit plane and `z ∈ U` (principal branch). -/
@[dlmf 32.13.E4]
theorem kdV_scalingReduction {α : ℂ} {w : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hw : IsPainleveIIOn α w U) :
    IsKdVOn (fun x t => -(3 * t) ^ (-2 / 3 : ℂ) *
        (deriv w (x * (3 * t) ^ (-1 / 3 : ℂ)) + w (x * (3 * t) ^ (-1 / 3 : ℂ)) ^ 2))
      {p | 3 * p.2 ∈ slitPlane ∧ p.1 * (3 * p.2) ^ (-1 / 3 : ℂ) ∈ U} := by
  have e23 : ∀ t : ℂ, (3 * t) ^ (-2 / 3 : ℂ) = ((3 * t) ^ (-1 / 3 : ℂ)) ^ 2 := fun t => by
    rw [← cpow_nat_mul]; norm_num
  simp only [e23]
  have hd : DifferentiableOn ℂ w U := fun y hy => (hw.differentiableAt y hy).differentiableWithinAt
  have hd1 : DifferentiableOn ℂ (deriv w) U := hd.deriv hU
  set A : ℂ → ℂ := fun y => deriv w y + w y ^ 2 with hA
  set B : ℂ → ℂ := fun y => (2 * w y ^ 3 + y * w y + α) + 2 * w y * deriv w y with hB
  set C' : ℂ → ℂ := fun y => 6 * w y ^ 2 * deriv w y + w y + y * deriv w y +
    2 * deriv w y ^ 2 + 2 * w y * (2 * w y ^ 3 + y * w y + α) with hC
  set D : ℂ → ℂ := fun y => 12 * w y ^ 5 + 24 * w y ^ 3 * deriv w y + 8 * w y ^ 3 * y +
    6 * w y ^ 2 * α + 2 * w y ^ 2 + 12 * w y * deriv w y ^ 2 + 8 * w y * deriv w y * y +
    w y * y ^ 2 + 6 * deriv w y * α + 2 * deriv w y + α * y with hD
  have hw1 : ∀ y ∈ U, HasDerivAt (deriv w) (2 * w y ^ 3 + y * w y + α) y := fun y hy =>
    hw.hasDerivAt_deriv y hy
  have hW : ∀ y ∈ U, HasDerivAt w (deriv w y) y := fun y hy => hw.hasDerivAt hy
  have hAd : ∀ y ∈ U, HasDerivAt A (B y) y := fun y hy => by
    have := (hw1 y hy).add ((hW y hy).pow 2)
    exact this.congr_deriv (by simp only [hB]; push_cast; ring)
  have hBd : ∀ y ∈ U, HasDerivAt B (C' y) y := fun y hy => by
    have := (((((hW y hy).pow 3).const_mul 2).add ((hasDerivAt_id y).mul (hW y hy))).add_const
      α).add (((hW y hy).const_mul 2).mul (hw1 y hy))
    exact this.congr_deriv (by simp only [hC, id]; push_cast; ring)
  have hCd : ∀ y ∈ U, HasDerivAt C' (D y) y := fun y hy => by
    have hW2 := ((((hW y hy).pow 3).const_mul 2).add ((hasDerivAt_id y).mul (hW y hy))).add_const α
    have := ((((((hW y hy).pow 2).const_mul 6).mul (hw1 y hy)).add (hW y hy)).add
      ((hasDerivAt_id y).mul (hw1 y hy))).add (((hw1 y hy).pow 2).const_mul 2) |>.add
      (((hW y hy).const_mul 2).mul hW2)
    exact this.congr_deriv (by
      simp only [hD, id, Pi.pow_apply, Pi.add_apply, Pi.mul_apply]; push_cast; ring)
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · have hc : ContDiffAt ℂ 3 A (p.1 * (3 * p.2) ^ (-1 / 3 : ℂ)) :=
      ((hd1.contDiffOn hU).contDiffAt (hU.mem_nhds hp.2)).add
        (((hd.contDiffOn hU).contDiffAt (hU.mem_nhds hp.2)).pow 2)
    exact contDiffAt_const.mul (hc.comp p.1 (contDiffAt_id.mul contDiffAt_const))
  · have hin := (p3b_hasDerivAt_r hp.1).const_mul p.1
    exact ((p3b_hasDerivAt_r hp.1).differentiableAt.pow 2).neg.mul
      ((hAd _ hp.2).differentiableAt.comp p.2 hin.differentiableAt)
  · obtain ⟨hp1, hp2⟩ := hp
    set R := (3 * p.2) ^ (-1 / 3 : ℂ) with hR
    have hin : HasDerivAt (fun t : ℂ => p.1 * (3 * t) ^ (-1 / 3 : ℂ)) (p.1 * -R ^ 4) p.2 :=
      (p3b_hasDerivAt_r hp1).const_mul p.1
    have ht : HasDerivAt (fun t : ℂ => -((3 * t) ^ (-1 / 3 : ℂ)) ^ 2 *
        A (p.1 * (3 * t) ^ (-1 / 3 : ℂ)))
        (-(2 * R * -R ^ 4) * A (p.1 * R) + -R ^ 2 * (B (p.1 * R) * (p.1 * -R ^ 4))) p.2 := by
      have := (((p3b_hasDerivAt_r hp1).pow 2).neg).mul ((hAd _ hp2).comp p.2 hin)
      refine this.congr_deriv ?_
      simp only [Function.comp_apply, Pi.neg_apply, Pi.pow_apply, ← hR]
      push_cast; ring
    have hV : IsOpen {x : ℂ | x * R ∈ U} := hU.preimage (continuous_id.mul continuous_const)
    have h1 : ∀ x ∈ {x : ℂ | x * R ∈ U}, HasDerivAt (fun x => -R ^ 2 * A (x * R))
        (-R ^ 2 * R * B (x * R)) x := fun x hx => p3b_scale (hAd _ hx)
    have h2 : ∀ x ∈ {x : ℂ | x * R ∈ U}, HasDerivAt (fun x => -R ^ 2 * R * B (x * R))
        (-R ^ 2 * R * R * C' (x * R)) x := fun x hx => p3b_scale (hBd _ hx)
    have h3 : ∀ x ∈ {x : ℂ | x * R ∈ U}, HasDerivAt (fun x => -R ^ 2 * R * R * C' (x * R))
        (-R ^ 2 * R * R * R * D (x * R)) x := fun x hx => p3b_scale (hCd _ hx)
    have hu : (fun x => -R ^ 2 * (deriv w (x * R) + w (x * R) ^ 2)) =
        fun x => -R ^ 2 * A (x * R) := rfl
    have hut : (fun t : ℂ => -((3 * t) ^ (-1 / 3 : ℂ)) ^ 2 *
        (deriv w (p.1 * (3 * t) ^ (-1 / 3 : ℂ)) + w (p.1 * (3 * t) ^ (-1 / 3 : ℂ)) ^ 2)) =
        fun t : ℂ => -((3 * t) ^ (-1 / 3 : ℂ)) ^ 2 * A (p.1 * (3 * t) ^ (-1 / 3 : ℂ)) := rfl
    rw [hut, hu, ht.deriv, (h1 p.1 hp2).deriv, p3b_iteratedDeriv_three hV h1 h2 h3 hp2]
    simp only [hA, hB, hD]
    ring


/-- DLMF 32.13.5: if `W'' = -3W² + λz + C` on `U` (the twice-integrated form of the reduced
equation `W''' + 6WW' = λ`), then `u(x, t) = W(x + 3λt²) - λt` solves the KdV equation
32.13.3 wherever `x + 3λt² ∈ U`. -/
@[dlmf 32.13.E5]
theorem kdV_similarityReduction {lam C : ℂ} {W : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hW : IsODE2SolutionOn (fun z W _ => -3 * W ^ 2 + lam * z + C) W U) :
    IsKdVOn (fun x t => W (x + 3 * lam * t ^ 2) - lam * t)
      {p | p.1 + 3 * lam * p.2 ^ 2 ∈ U} := by
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · exact ((p3b_contDiffAt hU hW hp 3).comp p.1 (contDiffAt_id.add contDiffAt_const)).sub
      contDiffAt_const
  · exact ((hW.differentiableAt _ hp).comp p.2 (by fun_prop)).sub (by fun_prop)
  · have hin : HasDerivAt (fun t => p.1 + 3 * lam * t ^ 2) (6 * lam * p.2) p.2 := by
      have := ((hasDerivAt_pow 2 p.2).const_mul (3 * lam)).const_add p.1
      exact this.congr_deriv (by push_cast; ring)
    have ht : deriv (fun t => W (p.1 + 3 * lam * t ^ 2) - lam * t) p.2 =
        deriv W (p.1 + 3 * lam * p.2 ^ 2) * (6 * lam * p.2) - lam :=
      (((hW.hasDerivAt hp).comp p.2 hin).sub ((hasDerivAt_id p.2).const_mul lam)).deriv.trans
        (by simp)
    have hdx : deriv (fun x => W (x + 3 * lam * p.2 ^ 2) - lam * p.2) =
        fun x => deriv W (x + 3 * lam * p.2 ^ 2) := by
      funext x; rw [deriv_sub_const, deriv_comp_add_const]
    have hx3 : iteratedDeriv 3 (fun x => W (x + 3 * lam * p.2 ^ 2) - lam * p.2) p.1 =
        -6 * W (p.1 + 3 * lam * p.2 ^ 2) * deriv W (p.1 + 3 * lam * p.2 ^ 2) + lam := by
      rw [iteratedDeriv_succ', hdx, iteratedDeriv_comp_add_const, iteratedDeriv_succ,
        iteratedDeriv_one]
      refine p3b_deriv3 hU hW hp ?_
      have := ((((hW.hasDerivAt hp).pow 2).const_mul (-3)).add ((hasDerivAt_id _).const_mul lam)
        ).add_const C
      exact this.congr_deriv (by simp; ring)
    rw [ht, hdx, hx3]
    ring


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
  have key : ∀ p : ℂ × ℂ, p.1 * p.2 ∈ U →
      (fun t => deriv (fun x => v (x * t)) p.1) =ᶠ[𝓝 p.2] fun t => deriv v (p.1 * t) * t := by
    intro p hp
    have ho : IsOpen {t : ℂ | p.1 * t ∈ U} := hU.preimage (continuous_const.mul continuous_id)
    filter_upwards [ho.mem_nhds hp] with t ht
    exact ((hv _ ht).hasDerivAt.comp p.1 (hasDerivAt_mul_const t)).deriv
  have hg : ∀ p : ℂ × ℂ, p.1 * p.2 ∈ U → HasDerivAt (fun t => deriv v (p.1 * t) * t)
      (deriv (deriv v) (p.1 * p.2) * p.1 * p.2 + deriv v (p.1 * p.2)) p.2 := by
    intro p hp
    have h1 : HasDerivAt (fun t => deriv v (p.1 * t)) (deriv (deriv v) (p.1 * p.2) * p.1) p.2 :=
      (hv1 _ hp).hasDerivAt.comp p.2 (hasDerivAt_const_mul p.1 |>.congr_deriv (by simp))
    exact (h1.mul (hasDerivAt_id p.2)).congr_deriv (by simp)
  refine ⟨fun p hp => (hv _ hp).comp p.1 (differentiableAt_id.mul_const _), fun p hp => ?_,
    fun p hp => ?_⟩
  · exact ((hg p hp).differentiableAt).congr_of_eventuallyEq (key p hp)
  · rw [(key p hp).deriv_eq, (hg p hp).deriv, ← hode _ hp]
    ring


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
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · exact (p3b_contDiffAt hU hv hp 4).comp p.1 (contDiffAt_id.sub contDiffAt_const)
  · exact (p3b_contDiffAt hU hv hp 2).comp p.2 (contDiffAt_const.sub
      (contDiffAt_const.mul contDiffAt_id))
  set y0 := p.1 - c * p.2 with hy0
  change y0 ∈ U at hp
  have hF : ∀ y ∈ U, HasDerivAt (fun y => 6 * v y ^ 2 + (c ^ 2 - 1) * v y + A * y + B)
      ((12 * v y + (c ^ 2 - 1)) * deriv v y + A) y := by
    intro y hy
    have := ((((hv.hasDerivAt hy).pow 2).const_mul 6).add ((hv.hasDerivAt hy).const_mul
      (c ^ 2 - 1))).add ((hasDerivAt_id y).const_mul A) |>.add_const B
    exact this.congr_deriv (by simp; ring)
  have h3 : deriv (deriv (deriv v)) =ᶠ[𝓝 y0] fun y => (12 * v y + (c ^ 2 - 1)) * deriv v y + A := by
    filter_upwards [hU.mem_nhds hp] with y hy using p3b_deriv3 hU hv hy (hF y hy)
  have hv2 : deriv (deriv v) y0 = 6 * v y0 ^ 2 + (c ^ 2 - 1) * v y0 + A * y0 + B := hv.ode hp
  have hdd := hv.hasDerivAt_deriv y0 hp
  rw [← hv2] at hdd
  -- the fourth derivative
  have h4 : iteratedDeriv 4 (fun x => v (x - c * p.2)) p.1 =
      12 * deriv v y0 ^ 2 + (12 * v y0 + (c ^ 2 - 1)) * deriv (deriv v) y0 := by
    rw [iteratedDeriv_comp_sub_const]
    change iteratedDeriv 4 v y0 = _
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
      h3.deriv_eq]
    have : HasDerivAt (fun y => (12 * v y + (c ^ 2 - 1)) * deriv v y + A)
        ((12 * deriv v y0) * deriv v y0 + (12 * v y0 + (c ^ 2 - 1)) * deriv (deriv v) y0) y0 := by
      have := ((((hv.hasDerivAt hp).const_mul 12).add_const (c ^ 2 - 1)).mul hdd).add_const A
      exact this.congr_deriv (by ring)
    rw [this.deriv]; ring
  have h2 : iteratedDeriv 2 (fun x => v (x - c * p.2)) p.1 = deriv (deriv v) y0 := by
    rw [iteratedDeriv_comp_sub_const, iteratedDeriv_succ, iteratedDeriv_one]
  have h2sq : iteratedDeriv 2 (fun x => v (x - c * p.2) ^ 2) p.1 =
      2 * deriv v y0 ^ 2 + 2 * v y0 * deriv (deriv v) y0 := by
    rw [congrFun (iteratedDeriv_comp_sub_const 2 (fun y => v y ^ 2) (c * p.2)) p.1,
      iteratedDeriv_succ, iteratedDeriv_one, ← hy0]
    have hsq : deriv (fun y => v y ^ 2) =ᶠ[𝓝 y0] fun y => 2 * v y * deriv v y := by
      filter_upwards [hU.mem_nhds hp] with y hy
      exact ((hv.hasDerivAt hy).pow 2).deriv.trans (by simp)
    rw [hsq.deriv_eq]
    have : HasDerivAt (fun y => 2 * v y * deriv v y)
        (2 * deriv v y0 * deriv v y0 + 2 * v y0 * deriv (deriv v) y0) y0 :=
      ((hv.hasDerivAt hp).const_mul 2).mul hdd
    rw [this.deriv]
    ring
  have ht2 : iteratedDeriv 2 (fun t => v (p.1 - c * t)) p.2 = c ^ 2 * deriv (deriv v) y0 := by
    have hin : ∀ t, HasDerivAt (fun t => p.1 - c * t) (-c) t := fun t =>
      ((hasDerivAt_id t).const_mul c).const_sub p.1 |>.congr_deriv (by simp)
    have ho : IsOpen {t : ℂ | p.1 - c * t ∈ U} :=
      hU.preimage (continuous_const.sub (continuous_const.mul continuous_id))
    have he : deriv (fun t => v (p.1 - c * t)) =ᶠ[𝓝 p.2] fun t => deriv v (p.1 - c * t) * (-c) := by
      filter_upwards [ho.mem_nhds hp] with t ht
      exact ((hv.hasDerivAt ht).comp t (hin t)).deriv
    rw [iteratedDeriv_succ, iteratedDeriv_one, he.deriv_eq]
    have : HasDerivAt (fun t => deriv v (p.1 - c * t) * (-c))
        (deriv (deriv v) y0 * (-c) * (-c)) p.2 := (hdd.comp p.2 (hin p.2)).mul_const (-c)
    rw [this.deriv]
    ring
  rw [ht2, h2, h2sq, h4, hv2]
  ring


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
