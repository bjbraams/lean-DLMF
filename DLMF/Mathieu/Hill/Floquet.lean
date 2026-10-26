/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Hill.Defs
public import DLMFMathlib.Analysis.ODE.PowerSeriesUniqueness
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Hill's equation: Floquet theory and the discriminant (DLMF §28.29)

Statements of DLMF §28.29 for Hill's equation `w'' + (λ + Q(x)) w = 0` (definitions in
`DLMF.Mathieu.Hill.Defs`):

* §28.29(i): Mathieu's equation is the case `Q(x) = -2q cos 2x` (`isHillPotential_mathieu`).
* §28.29(ii): existence (flagged, `hill_exists_solution`) and uniqueness
  (`IsHillSolution.eq_of_initial`, proved) of solutions with given initial data, the basic
  solutions, the shift relations 28.29.4–28.29.5 (proved from the existence theorem), the
  characteristic equation 28.29.8–28.29.9, Floquet solutions 28.29.10, the exceptional cases
  `ν = 0, 1` (28.29.11–28.29.12), 28.29.13 and the symmetric case 28.29.14.
* §28.29(iii) (real `Q`): the discriminant, the periodic and antiperiodic eigenvalues
  28.29.16–28.29.18 and their asymptotics 28.29.19–28.29.22.

The basic solutions are definitions by choice (`hillWI`, `hillWII`); the only admitted
ingredient of the proved shift relations is the existence theorem `hill_exists_solution`
for continuous `Q` (a global existence theorem for linear ODEs; DLMFMathlib has existence on
compact intervals, `ODE.exists_linear_system_Icc`).
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics MeasureTheory intervalIntegral
open scoped Topology Classical

namespace DLMF.Mathieu

variable {Q : ℝ → ℂ} {lam : ℂ}

/-! ### Mathieu's equation as a Hill equation -/

/-- Mathieu's equation 28.2.1 is Hill's equation (DLMF §28.29(i), "a generalization of
Mathieu's equation") with `λ = a` and `Q(x) = -2q cos 2x`; this potential satisfies
28.29.2 and 28.29.3. -/
@[dlmf 28.29.i]
theorem isHillPotential_mathieu (q : ℂ) :
    IsHillPotential (fun x => -2 * q * Complex.cos (2 * x)) := by
  refine ⟨by fun_prop, fun x => ?_, ?_⟩
  · push_cast
    rw [show (2 : ℂ) * ((x : ℂ) + Real.pi) = 2 * x + 2 * Real.pi by ring, Complex.cos_add_two_pi]
  · have h : ∫ x in (0 : ℝ)..Real.pi, Complex.cos (2 * (x : ℂ)) = 0 := by
      have e : (fun x : ℝ => Complex.cos (2 * (x : ℂ))) =
          fun x : ℝ => ((Real.cos (2 * x) : ℝ) : ℂ) := by
        funext x; push_cast; rfl
      have hr : ∫ x in (0 : ℝ)..Real.pi, Real.cos (2 * x) = 0 := by
        rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) two_ne_zero]
        simp [integral_cos, Real.sin_two_pi]
      rw [e, intervalIntegral.integral_ofReal, hr]; simp
    simp [intervalIntegral.integral_const_mul, h]

/-! ### Existence and uniqueness -/

/-- **Existence of solutions** of Hill's equation with prescribed initial data at `0`, for a
continuous potential (the basis of DLMF §28.29(ii)). Flagged existence theorem (admitted):
global existence for a linear second-order ODE with continuous coefficients. -/
@[dlmf 28.29.ii]
theorem hill_exists_solution (hQ : Continuous Q) (lam w₀ w₁ : ℂ) :
    ∃ w : ℝ → ℂ, IsHillSolution Q lam w ∧ w 0 = w₀ ∧ deriv w 0 = w₁ := by
  sorry

/-- A solution of Hill's equation has derivative `deriv w`. -/
theorem IsHillSolution.hasDerivAt {w : ℝ → ℂ} (h : IsHillSolution Q lam w) (x : ℝ) :
    HasDerivAt w (deriv w x) x :=
  (h.differentiable x).hasDerivAt

/-- **Uniqueness of solutions** of Hill's equation with continuous potential: two solutions
with the same value and derivative at one point coincide. -/
theorem IsHillSolution.eq_of_initial (hQ : Continuous Q) {u v : ℝ → ℂ}
    (hu : IsHillSolution Q lam u) (hv : IsHillSolution Q lam v) {x₀ : ℝ} (h₀ : u x₀ = v x₀)
    (h₁ : deriv u x₀ = deriv v x₀) : u = v := by
  have hq : Continuous (fun x => -(lam + Q x)) := by fun_prop
  refine (ODE.eq_of_linear_ode (p := fun _ => (0 : ℂ)) (q := fun x => -(lam + Q x))
    (f' := deriv u) (g' := deriv v) continuous_const hq (fun t => ⟨hu.hasDerivAt t, ?_⟩)
    (fun t => ⟨hv.hasDerivAt t, ?_⟩) h₀ h₁).1
  · simpa using hu.hasDerivAt_deriv t
  · simpa using hv.hasDerivAt_deriv t

/-- The defining property of the basic solution `w_I` (DLMF §28.29(ii)). -/
@[dlmf 28.29.ii]
theorem hillWI_spec (hQ : Continuous Q) (lam : ℂ) :
    IsHillSolution Q lam (fun x => hillWI Q x lam) ∧ hillWI Q 0 lam = 1 ∧
      deriv (fun x => hillWI Q x lam) 0 = 0 := by
  have h := hill_exists_solution hQ lam 1 0
  have he : (fun x => hillWI Q x lam) = h.choose := by
    funext x; simp only [hillWI, h, dite_true]
  have h0 : hillWI Q 0 lam = h.choose 0 := congrFun he 0
  rw [he, h0]; exact h.choose_spec

/-- The defining property of the basic solution `w_II` (DLMF §28.29(ii)). -/
@[dlmf 28.29.ii]
theorem hillWII_spec (hQ : Continuous Q) (lam : ℂ) :
    IsHillSolution Q lam (fun x => hillWII Q x lam) ∧ hillWII Q 0 lam = 0 ∧
      deriv (fun x => hillWII Q x lam) 0 = 1 := by
  have h := hill_exists_solution hQ lam 0 1
  have he : (fun x => hillWII Q x lam) = h.choose := by
    funext x; simp only [hillWII, h, dite_true]
  have h0 : hillWII Q 0 lam = h.choose 0 := congrFun he 0
  rw [he, h0]; exact h.choose_spec

/-- Every solution is the combination `w(0) w_I + w'(0) w_II` of the basic solutions. -/
theorem IsHillSolution.eq_combination (hQ : Continuous Q) {w : ℝ → ℂ}
    (h : IsHillSolution Q lam w) :
    w = fun x => w 0 * hillWI Q x lam + deriv w 0 * hillWII Q x lam := by
  obtain ⟨h1, h1a, h1b⟩ := hillWI_spec hQ lam
  obtain ⟨h2, h2a, h2b⟩ := hillWII_spec hQ lam
  have hc : IsHillSolution Q lam
      ((w 0) • (fun x => hillWI Q x lam) + (deriv w 0) • (fun x => hillWII Q x lam)) :=
    (h1.const_smul _).add (h2.const_smul _)
  have hd : deriv ((w 0) • (fun x => hillWI Q x lam) + (deriv w 0) • (fun x => hillWII Q x lam))
      0 = deriv w 0 := by
    rw [deriv_add ((h1.differentiable 0).const_smul _) ((h2.differentiable 0).const_smul _),
      deriv_const_smul _ (h1.differentiable 0), deriv_const_smul _ (h2.differentiable 0), h1b,
      h2b]
    simp
  have := h.eq_of_initial hQ hc (x₀ := 0) (by simp [h1a, h2a]) hd.symm
  exact funext fun x => by simpa using congrFun this x

/-- The shift `x ↦ w(x + π)` of a solution is a solution (the potential has period `π`). -/
theorem IsHillSolution.comp_add_pi (hQ : Function.Periodic Q Real.pi) {w : ℝ → ℂ}
    (h : IsHillSolution Q lam w) : IsHillSolution Q lam (fun x => w (x + Real.pi)) := by
  have hd : deriv (fun x => w (x + Real.pi)) = fun x => deriv w (x + Real.pi) := by
    funext x; exact deriv_comp_add_const w Real.pi x
  refine ⟨h.differentiable.comp (differentiable_id.add_const _), fun x => ?_⟩
  rw [hd]
  have := (h.hasDerivAt_deriv (x + Real.pi)).comp_add_const x Real.pi
  rwa [hQ x] at this

/-- **Shift relation** for `w_I` (DLMF 28.29.4):
`w_I(z + π, λ) = w_I(π, λ) w_I(z, λ) + w_I'(π, λ) w_II(z, λ)`. Proved from the existence
theorem `hill_exists_solution`. -/
@[dlmf 28.29.E4]
theorem hillWI_add_pi (hQ : IsHillPotential Q) (lam : ℂ) (z : ℝ) :
    hillWI Q (z + Real.pi) lam = hillWI Q Real.pi lam * hillWI Q z lam +
      deriv (fun x => hillWI Q x lam) Real.pi * hillWII Q z lam := by
  have h := ((hillWI_spec hQ.continuous lam).1.comp_add_pi hQ.periodic).eq_combination
    hQ.continuous
  have h' := congrFun h z
  simp only [zero_add] at h'
  have hd := deriv_comp_add_const (f := fun y => hillWI Q y lam) (a := Real.pi) (x := 0)
  rw [h', hd, zero_add]

/-- **Shift relation** for `w_II` (DLMF 28.29.5):
`w_II(z + π, λ) = w_II(π, λ) w_I(z, λ) + w_II'(π, λ) w_II(z, λ)`. Proved from the existence
theorem `hill_exists_solution`. -/
@[dlmf 28.29.E5]
theorem hillWII_add_pi (hQ : IsHillPotential Q) (lam : ℂ) (z : ℝ) :
    hillWII Q (z + Real.pi) lam = hillWII Q Real.pi lam * hillWI Q z lam +
      deriv (fun x => hillWII Q x lam) Real.pi * hillWII Q z lam := by
  have h := ((hillWII_spec hQ.continuous lam).1.comp_add_pi hQ.periodic).eq_combination
    hQ.continuous
  have h' := congrFun h z
  simp only [zero_add] at h'
  have hd := deriv_comp_add_const (f := fun y => hillWII Q y lam) (a := Real.pi) (x := 0)
  rw [h', hd, zero_add]

/-! ### Characteristic exponents and Floquet solutions -/

/-- **Characteristic exponents exist** in the strip 28.29.6: for every `λ` there is `ν` with
`-1 < ℜν ≤ 1` and `2 cos(πν) = Δ(λ)` (DLMF 28.29.6, 28.29.9); the characteristic exponents
are `±ν`. -/
@[dlmf 28.29.E6]
theorem exists_hillCharExp (Q : ℝ → ℂ) (lam : ℂ) :
    ∃ ν : ℂ, -1 < ν.re ∧ ν.re ≤ 1 ∧ 2 * Complex.cos (Real.pi * ν) = hillDiscriminant Q lam := by
  obtain ⟨x, hx⟩ := Complex.cos_surjective (hillDiscriminant Q lam / 2)
  set ν₀ : ℂ := x / Real.pi
  set k : ℤ := ⌈(ν₀.re - 1) / 2⌉
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine ⟨ν₀ - 2 * k, ?_, ?_, ?_⟩
  · have := Int.ceil_lt_add_one ((ν₀.re - 1) / 2)
    simp only [sub_re, mul_re, re_ofNat, intCast_re, im_ofNat, intCast_im, mul_zero, sub_zero]
    linarith
  · have := Int.le_ceil ((ν₀.re - 1) / 2)
    simp only [sub_re, mul_re, re_ofNat, intCast_re, im_ofNat, intCast_im, mul_zero, sub_zero]
    linarith
  · have : (Real.pi : ℂ) * (ν₀ - 2 * k) = x - k * (2 * Real.pi) := by
      simp only [ν₀]; field_simp
    rw [this, Complex.cos_sub_int_mul_two_pi, hx]; ring

/-- **Floquet's theorem** (DLMF 28.29.7–28.29.8): Hill's equation has a nontrivial solution
with `w(z + π) = e^{πiν} w(z)` iff `e^{πiν}` is an eigenvalue of the monodromy matrix 28.29.8.
(DLMF normalizes `-1 < ℜν ≤ 1`, 28.29.6; the statement holds for every `ν`.) -/
@[dlmf 28.29.E7, dlmf 28.29.E8]
theorem exists_hillFloquet_iff_det (hQ : IsHillPotential Q) (lam ν : ℂ) :
    (∃ w, IsHillFloquetSolution Q lam ν w) ↔
      (hillMonodromy Q lam - Complex.exp (Real.pi * I * ν) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det
        = 0 := by
  sorry

/-- **Characteristic equation** of Hill's equation (DLMF 28.29.9): a Floquet solution with
respect to `ν` exists iff `2 cos(πν) = w_I(π, λ) + w_II'(π, λ)`. -/
@[dlmf 28.29.E9]
theorem exists_hillFloquet_iff_discriminant (hQ : IsHillPotential Q) (lam ν : ℂ) :
    (∃ w, IsHillFloquetSolution Q lam ν w) ↔
      2 * Complex.cos (Real.pi * ν) = hillDiscriminant Q lam := by
  sorry

/-- `cos(πν) = Δ(λ)/2` is an **entire function of `λ`** (DLMF §28.29(ii), after 28.29.9; also
§28.29(iii): the discriminant is entire). -/
@[dlmf 28.29.ii, dlmf 28.29.iii]
theorem differentiable_hillDiscriminant (hQ : IsHillPotential Q) :
    Differentiable ℂ (hillDiscriminant Q) := by
  sorry

/-- A Floquet solution has the form `F_ν(z) = e^{iνz} P_ν(z)` with `P_ν` `π`-periodic
(DLMF 28.29.10). -/
@[dlmf 28.29.E10]
theorem IsHillFloquetSolution.exists_periodic {ν : ℂ} {w : ℝ → ℂ}
    (h : IsHillFloquetSolution Q lam ν w) :
    ∃ P : ℝ → ℂ, Function.Periodic P Real.pi ∧ ∀ x : ℝ, w x = Complex.exp (I * ν * x) * P x := by
  refine ⟨fun x => Complex.exp (-(I * ν * x)) * w x, fun x => ?_, fun x => ?_⟩
  · simp only
    rw [h.2.2 x, ← mul_assoc, ← Complex.exp_add]
    congr 2; push_cast; ring
  · rw [← mul_assoc, ← Complex.exp_add]; simp

/-- **Fundamental pair of Floquet solutions** (DLMF §28.29(ii)): if `ν ≠ 0, 1` with
`-1 < ℜν ≤ 1` solves 28.29.9, then there are Floquet solutions `F_ν`, `F_{-ν}`, and they
form a fundamental pair: every solution is a combination of them. -/
@[dlmf 28.29.ii]
theorem exists_hillFloquet_fundamental_pair (hQ : IsHillPotential Q) {ν : ℂ}
    (hν : -1 < ν.re ∧ ν.re ≤ 1) (hν0 : ν ≠ 0) (hν1 : ν ≠ 1)
    (hc : 2 * Complex.cos (Real.pi * ν) = hillDiscriminant Q lam) :
    ∃ w₁ w₂ : ℝ → ℂ, IsHillFloquetSolution Q lam ν w₁ ∧ IsHillFloquetSolution Q lam (-ν) w₂ ∧
      ∀ w, IsHillSolution Q lam w → ∃ c₁ c₂ : ℂ, w = c₁ • w₁ + c₂ • w₂ := by
  sorry

/-- **The exceptional exponents `ν = 0, 1`** (DLMF §28.29(ii), 28.29.11): if `Δ(λ) = 2s`
with `s = (-1)^ν = ±1`, there is a nontrivial solution `P` with `P(z + π) = s P(z)` (period
`π` or `2π`), and every solution satisfies `w(z + π) = s w(z) + c P(z)` for a constant `c`.
(DLMF states this for `w` linearly independent of `P`; for multiples of `P` it holds with
`c = 0`.) -/
@[dlmf 28.29.E11]
theorem exists_hill_periodic_of_discriminant (hQ : IsHillPotential Q) {s : ℂ}
    (hs : s = 1 ∨ s = -1) (hΔ : hillDiscriminant Q lam = 2 * s) :
    ∃ P ∈ hillMultiplierSolutions Q lam s, P ≠ 0 ∧
      ∀ w, IsHillSolution Q lam w → ∃ c : ℂ, ∀ z, w (z + Real.pi) = s * w z + c * P z := by
  sorry

/-- **Coexistence** (DLMF 28.29.12): with `Δ(λ) = 2s`, `s = (-1)^ν = ±1`, the constant `c` of
28.29.11 vanishes for all solutions (all solutions have multiplier `s`) iff the monodromy
matrix is `s` times the identity. -/
@[dlmf 28.29.E12]
theorem hill_coexistence_iff (hQ : IsHillPotential Q) {s : ℂ} (hs : s = 1 ∨ s = -1)
    (hΔ : hillDiscriminant Q lam = 2 * s) :
    (∀ w, IsHillSolution Q lam w → w ∈ hillMultiplierSolutions Q lam s) ↔
      hillMonodromy Q lam = s • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  sorry

/-- **Periodic solutions of period `nπ`, `n ≥ 3`** (DLMF §28.29(ii)): if Hill's equation has
a periodic solution with minimum period `nπ`, `n = 3, 4, …`, then all its solutions have
period `nπ`. -/
@[dlmf 28.29.ii]
theorem hill_all_periodic_of_minimal_period (hQ : IsHillPotential Q) {n : ℕ} (hn : 3 ≤ n)
    {w : ℝ → ℂ} (hw : IsHillSolution Q lam w) (hper : Function.Periodic w (n * Real.pi))
    (hmin : ∀ T : ℝ, 0 < T → T < n * Real.pi → ¬ Function.Periodic w T) :
    ∀ v, IsHillSolution Q lam v → Function.Periodic v (n * Real.pi) := by
  sorry

/-- DLMF 28.29.13: every solution satisfies `w(z + π) + w(z - π) = 2 cos(πν) w(z)`, where
`2 cos(πν) = Δ(λ)`. -/
@[dlmf 28.29.E13]
theorem IsHillSolution.add_pi_add_sub_pi (hQ : IsHillPotential Q) {ν : ℂ}
    (hc : 2 * Complex.cos (Real.pi * ν) = hillDiscriminant Q lam) {w : ℝ → ℂ}
    (hw : IsHillSolution Q lam w) (z : ℝ) :
    w (z + Real.pi) + w (z - Real.pi) = 2 * Complex.cos (Real.pi * ν) * w z := by
  sorry

/-- DLMF §28.29(ii), after 28.29.13: with `2 cos(πν) = Δ(λ)`, a nontrivial solution `w` is
either a Floquet solution with respect to `ν`, or `w(z + π) - e^{iνπ} w(z)` is a Floquet
solution with respect to `-ν`. -/
@[dlmf 28.29.ii]
theorem IsHillSolution.floquet_or (hQ : IsHillPotential Q) {ν : ℂ}
    (hc : 2 * Complex.cos (Real.pi * ν) = hillDiscriminant Q lam) {w : ℝ → ℂ}
    (hw : IsHillSolution Q lam w) (hw0 : w ≠ 0) :
    IsHillFloquetSolution Q lam ν w ∨
      IsHillFloquetSolution Q lam (-ν)
        (fun z => w (z + Real.pi) - Complex.exp (I * ν * Real.pi) * w z) := by
  sorry

/-- **Symmetric case** (DLMF §28.29(ii)): for an even potential `Q(z) = Q(-z)`, `w_I` is
even. Proved from the existence theorem. -/
@[dlmf 28.29.ii]
theorem hillWI_neg_of_even (hQ : Continuous Q) (heven : ∀ x, Q (-x) = Q x) (lam : ℂ) (z : ℝ) :
    hillWI Q (-z) lam = hillWI Q z lam := by
  obtain ⟨h1, h1a, h1b⟩ := hillWI_spec hQ lam
  set w := fun x => hillWI Q x lam
  have hd : deriv (fun x => w (-x)) = fun x => -deriv w (-x) := by
    funext x; exact deriv_comp_neg w x
  have hs : IsHillSolution Q lam (fun x => w (-x)) := by
    refine ⟨h1.differentiable.comp differentiable_neg, fun x => ?_⟩
    rw [hd]
    have := (HasDerivAt.scomp (h := fun y : ℝ => -y) x (h1.hasDerivAt_deriv (-x))
      (hasDerivAt_neg x)).neg
    exact this.congr_deriv (by rw [heven]; simp)
  have := hs.eq_of_initial hQ h1 (x₀ := 0) (by simp) (by rw [hd]; simp [w, h1b])
  exact congrFun this z

/-- **Symmetric case** (DLMF §28.29(ii)): for an even potential `w_II` is odd. Proved from
the existence theorem. -/
@[dlmf 28.29.ii]
theorem hillWII_neg_of_even (hQ : Continuous Q) (heven : ∀ x, Q (-x) = Q x) (lam : ℂ)
    (z : ℝ) : hillWII Q (-z) lam = -hillWII Q z lam := by
  obtain ⟨h1, h1a, h1b⟩ := hillWII_spec hQ lam
  set w := fun x => hillWII Q x lam
  have hd : deriv (fun x => -w (-x)) = fun x => deriv w (-x) := by
    funext x
    rw [show (fun x => -w (-x)) = -(fun x => w (-x)) from rfl, deriv.neg, deriv_comp_neg w x,
      neg_neg]
  have hs : IsHillSolution Q lam (fun x => -w (-x)) := by
    refine ⟨(h1.differentiable.comp differentiable_neg).neg, fun x => ?_⟩
    rw [hd]
    have := HasDerivAt.scomp (h := fun y : ℝ => -y) x (h1.hasDerivAt_deriv (-x))
      (hasDerivAt_neg x)
    exact this.congr_deriv (by rw [heven]; simp)
  have := hs.eq_of_initial hQ h1 (x₀ := 0) (by simp [w, h1a]) (by rw [hd]; simp [w, h1b])
  have := congrFun this z
  simp only [w] at this
  rw [← this, neg_neg]

/-- **Symmetric case** (DLMF 28.29.14): for an even potential `w_I(π, λ) = w_II'(π, λ)`, so the
characteristic equation becomes `cos(πν) = w_I(π, λ)`, i.e. `Δ(λ) = 2 w_I(π, λ)`. -/
@[dlmf 28.29.E14]
theorem hillDiscriminant_of_even (hQ : IsHillPotential Q) (heven : ∀ x, Q (-x) = Q x)
    (lam : ℂ) : hillDiscriminant Q lam = 2 * hillWI Q Real.pi lam := by
  sorry

/-! ### §28.29(iii) The discriminant and the eigenvalues (real `Q`) -/

/-- The discriminant of a real Hill equation has **order of growth exactly `½`** as
`|λ| → ∞` (DLMF §28.29(iii)): for every `ε > 0`,
`Δ(λ) = O(exp(|λ|^{1/2+ε}))`, and `Δ(λ)` is not `O(exp(|λ|^{1/2-ε}))`. -/
@[dlmf 28.29.iii]
theorem hillDiscriminant_order_half {Q : ℝ → ℝ} (hQ : IsHillPotential (fun x => (Q x : ℂ)))
    {ε : ℝ} (hε : 0 < ε) :
    (hillDiscriminant (fun x => (Q x : ℂ)) =O[cocompact ℂ]
        fun lam => Real.exp (‖lam‖ ^ ((1 : ℝ) / 2 + ε))) ∧
      ¬ (hillDiscriminant (fun x => (Q x : ℂ)) =O[cocompact ℂ]
        fun lam => Real.exp (‖lam‖ ^ ((1 : ℝ) / 2 - ε))) := by
  sorry

/-- For given `ν` the characteristic equation `Δ(λ) - 2 cos(πν) = 0` has **infinitely many
roots** `λ` (DLMF §28.29(iii)), for real `Q`. -/
@[dlmf 28.29.iii]
theorem infinite_hillDiscriminant_eq {Q : ℝ → ℝ} (hQ : IsHillPotential (fun x => (Q x : ℂ)))
    (ν : ℂ) :
    {lam : ℂ | hillDiscriminant (fun x => (Q x : ℂ)) lam = 2 * Complex.cos (Real.pi * ν)}.Infinite
    := by
  sorry

/-- **Periodic eigenvalues** (DLMF 28.29.16 and §28.29(iii)) for real `Q`: every `λ_n`
satisfies `Δ(λ_n) = 2`; Hill's equation (with complex `λ`) has a nontrivial solution of period
`π` iff `λ = λ_n` for some `n`; the counting function is finite; and `λ_n → ∞`. -/
@[dlmf 28.29.E16, dlmf 28.29.iii]
theorem hillPeriodicEigenvalue_spec {Q : ℝ → ℝ} (hQ : IsHillPotential (fun x => (Q x : ℂ))) :
    (∀ t : ℝ, {lam : ℝ | lam ≤ t ∧
        hillMultiplierSolutions (fun x => (Q x : ℂ)) lam 1 ≠ ⊥}.Finite) ∧
      (∀ n, hillDiscriminant (fun x => (Q x : ℂ)) (hillPeriodicEigenvalue Q n) = 2) ∧
      (∀ lam : ℂ, hillMultiplierSolutions (fun x => (Q x : ℂ)) lam 1 ≠ ⊥ ↔
        ∃ n, lam = hillPeriodicEigenvalue Q n) ∧
      Tendsto (hillPeriodicEigenvalue Q) atTop atTop := by
  sorry

/-- **Antiperiodic eigenvalues** (DLMF 28.29.17 and §28.29(iii)) for real `Q`: every `μ_n`,
`n ≥ 1`, satisfies `Δ(μ_n) = -2`; Hill's equation has a nontrivial solution with
`w(z + π) = -w(z)` (DLMF: "a solution of period `2π`", meaning antiperiodic) iff `λ = μ_n` for
some `n ≥ 1`; and `μ_n → ∞`. -/
@[dlmf 28.29.E17, dlmf 28.29.iii]
theorem hillAntiperiodicEigenvalue_spec {Q : ℝ → ℝ}
    (hQ : IsHillPotential (fun x => (Q x : ℂ))) :
    (∀ t : ℝ, {lam : ℝ | lam ≤ t ∧
        hillMultiplierSolutions (fun x => (Q x : ℂ)) lam (-1) ≠ ⊥}.Finite) ∧
      (∀ n, 1 ≤ n → hillDiscriminant (fun x => (Q x : ℂ)) (hillAntiperiodicEigenvalue Q n) = -2) ∧
      (∀ lam : ℂ, hillMultiplierSolutions (fun x => (Q x : ℂ)) lam (-1) ≠ ⊥ ↔
        ∃ n, 1 ≤ n ∧ lam = hillAntiperiodicEigenvalue Q n) ∧
      Tendsto (hillAntiperiodicEigenvalue Q) atTop atTop := by
  sorry

/-- **Interlacing** of the periodic and antiperiodic eigenvalues (DLMF 28.29.18):
`λ₀ < μ₁ ≤ μ₂ < λ₁ ≤ λ₂ < μ₃ ≤ μ₄ < λ₃ ≤ λ₄ < ⋯`. -/
@[dlmf 28.29.E18]
theorem hill_eigenvalue_interlacing {Q : ℝ → ℝ} (hQ : IsHillPotential (fun x => (Q x : ℂ)))
    (k : ℕ) :
    hillPeriodicEigenvalue Q (2 * k) < hillAntiperiodicEigenvalue Q (2 * k + 1) ∧
      hillAntiperiodicEigenvalue Q (2 * k + 1) ≤ hillAntiperiodicEigenvalue Q (2 * k + 2) ∧
      hillAntiperiodicEigenvalue Q (2 * k + 2) < hillPeriodicEigenvalue Q (2 * k + 1) ∧
      hillPeriodicEigenvalue Q (2 * k + 1) ≤ hillPeriodicEigenvalue Q (2 * k + 2) := by
  sorry

/-- **Asymptotics of the antiperiodic eigenvalues** (DLMF 28.29.19–28.29.20): if `Q` has a
continuous second derivative, then with `N = π⁻¹ ∫₀^π Q²`, as `m → ∞`,
`μ_{2m-1} - (2m-1)² - N/(4m)² = o(m⁻²)` and `μ_{2m} - (2m-1)² - N/(4m)² = o(m⁻²)`. -/
@[dlmf 28.29.E19, dlmf 28.29.E20]
theorem hillAntiperiodicEigenvalue_asymptotic {Q : ℝ → ℝ}
    (hQ : IsHillPotential (fun x => (Q x : ℂ))) (hQ2 : ContDiff ℝ 2 Q) :
    (fun m : ℕ => hillAntiperiodicEigenvalue Q (2 * m - 1) - (2 * m - 1 : ℝ) ^ 2 -
        hillMeanSquare Q / (4 * m) ^ 2) =o[atTop] (fun m : ℕ => ((m : ℝ) ^ 2)⁻¹) ∧
      (fun m : ℕ => hillAntiperiodicEigenvalue Q (2 * m) - (2 * m - 1 : ℝ) ^ 2 -
        hillMeanSquare Q / (4 * m) ^ 2) =o[atTop] (fun m : ℕ => ((m : ℝ) ^ 2)⁻¹) := by
  sorry

/-- **Asymptotics of the periodic eigenvalues** (DLMF 28.29.21): if `Q` has a continuous
second derivative, then as `m → ∞`, `λ_{2m-1} - (2m)² - N/(4m)² = o(m⁻²)` and
`λ_{2m} - (2m)² - N/(4m)² = o(m⁻²)`. -/
@[dlmf 28.29.E21]
theorem hillPeriodicEigenvalue_asymptotic {Q : ℝ → ℝ}
    (hQ : IsHillPotential (fun x => (Q x : ℂ))) (hQ2 : ContDiff ℝ 2 Q) :
    (fun m : ℕ => hillPeriodicEigenvalue Q (2 * m - 1) - (2 * m : ℝ) ^ 2 -
        hillMeanSquare Q / (4 * m) ^ 2) =o[atTop] (fun m : ℕ => ((m : ℝ) ^ 2)⁻¹) ∧
      (fun m : ℕ => hillPeriodicEigenvalue Q (2 * m) - (2 * m : ℝ) ^ 2 -
        hillMeanSquare Q / (4 * m) ^ 2) =o[atTop] (fun m : ℕ => ((m : ℝ) ^ 2)⁻¹) := by
  sorry

/-- **Instability intervals** (DLMF 28.29.22, Hochstadt): if `Q` has `k` continuous
derivatives, then `λ_{2m} - λ_{2m-1} = o(m^{-k})` and `μ_{2m} - μ_{2m-1} = o(m^{-k})` as
`m → ∞`. -/
@[dlmf 28.29.E22]
theorem hill_gap_asymptotic {Q : ℝ → ℝ} (hQ : IsHillPotential (fun x => (Q x : ℂ))) {k : ℕ}
    (hQk : ContDiff ℝ k Q) :
    (fun m : ℕ => hillPeriodicEigenvalue Q (2 * m) - hillPeriodicEigenvalue Q (2 * m - 1))
        =o[atTop] (fun m : ℕ => ((m : ℝ) ^ k)⁻¹) ∧
      (fun m : ℕ => hillAntiperiodicEigenvalue Q (2 * m) -
        hillAntiperiodicEigenvalue Q (2 * m - 1)) =o[atTop] (fun m : ℕ => ((m : ℝ) ^ k)⁻¹) := by
  sorry

end DLMF.Mathieu
