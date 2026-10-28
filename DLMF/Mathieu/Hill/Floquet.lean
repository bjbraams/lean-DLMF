/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Hill.Defs
public import DLMFMathlib.Analysis.ODE.P1oLinearGlobal
public import DLMFMathlib.Analysis.ODE.P1oParamHolomorphic
public import DLMFMathlib.Analysis.ODE.P2sGrowth
public import DLMFMathlib.Analysis.ODE.P2sSturmSpectrum
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Hill's equation: Floquet theory and the discriminant (DLMF §28.29)

Statements of DLMF §28.29 for Hill's equation `w'' + (λ + Q(x)) w = 0` (definitions in
`DLMF.Mathieu.Hill.Defs`):

* §28.29(i): Mathieu's equation is the case `Q(x) = -2q cos 2x` (`isHillPotential_mathieu`).
* §28.29(ii): existence (`hill_exists_solution`, from `ODE.exists_linear_ode`) and uniqueness
  (`IsHillSolution.eq_of_initial`) of solutions with given initial data, the basic
  solutions, the shift relations 28.29.4–28.29.5, the
  characteristic equation 28.29.8–28.29.9, Floquet solutions 28.29.10, the exceptional cases
  `ν = 0, 1` (28.29.11–28.29.12), 28.29.13 and the symmetric case 28.29.14.
* §28.29(iii) (real `Q`): the discriminant, the periodic and antiperiodic eigenvalues
  28.29.16–28.29.18 and their asymptotics 28.29.19–28.29.22.

The basic solutions are definitions by choice (`hillWI`, `hillWII`); the existence theorem
`hill_exists_solution` for continuous `Q` is proved from the global existence theorem
`ODE.exists_linear_ode` (`DLMFMathlib.Analysis.ODE.P1oLinearGlobal`). The Floquet theory of
§28.29(ii) is proved in coordinates: the Wronskian of `w_I`, `w_II` is `1`
(`p1o_hill_wronskian`), a solution is determined by its data at `0`, and the shift by `π` acts
on the data by the monodromy matrix (`p1o_hill_data_pi`, `p1o_hill_multiplier_iff`), whose
characteristic polynomial is `ρ² - Δ(λ) ρ + 1` (`p1o_hill_two_step`).
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
  obtain ⟨f, f', h0, h1, h⟩ := ODE.exists_linear_ode (𝕜 := ℂ) (E := ℂ) (p := fun _ => 0)
    (q := fun x => -(lam + Q x)) continuous_const (by fun_prop) 0 w₀ w₁
  have hd : deriv f = f' := funext fun t => (h t).1.deriv
  refine ⟨f, ⟨fun t => (h t).1.differentiableAt, fun t => ?_⟩, h0, by rw [hd, h1]⟩
  rw [hd]
  simpa using (h t).2

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

/-! ### Floquet theory in coordinates (helpers) -/

/-- A solution shifted by `π`, in terms of the basic solutions. -/
lemma p1o_hill_shift (hQ : IsHillPotential Q) {u : ℝ → ℂ} (hu : IsHillSolution Q lam u)
    (z : ℝ) : u (z + Real.pi) = u Real.pi * hillWI Q z lam + deriv u Real.pi * hillWII Q z lam := by
  have h := (hu.comp_add_pi hQ.periodic).eq_combination hQ.continuous
  have h' := congrFun h z
  simp only [zero_add] at h'
  have hd := deriv_comp_add_const (f := u) (a := Real.pi) (x := 0)
  rw [h', hd, zero_add]

/-- The Wronskian of the basic solutions is identically `1` (no first-derivative term). -/
lemma p1o_hill_wronskian (hQ : Continuous Q) (x : ℝ) :
    hillWI Q x lam * deriv (fun x => hillWII Q x lam) x -
      deriv (fun x => hillWI Q x lam) x * hillWII Q x lam = 1 := by
  obtain ⟨h1, h1a, h1b⟩ := hillWI_spec hQ lam
  obtain ⟨h2, h2a, h2b⟩ := hillWII_spec hQ lam
  set W : ℝ → ℂ := fun x => hillWI Q x lam * deriv (fun x => hillWII Q x lam) x -
      deriv (fun x => hillWI Q x lam) x * hillWII Q x lam
  have hW : ∀ x, HasDerivAt W 0 x := fun x => by
    have := ((h1.hasDerivAt x).mul (h2.hasDerivAt_deriv x)).sub
      ((h1.hasDerivAt_deriv x).mul (h2.hasDerivAt x))
    convert this using 1; ring
  have hc := is_const_of_deriv_eq_zero (fun x => (hW x).differentiableAt) (fun x => (hW x).deriv)
    x 0
  change W x = 1
  rw [hc]; simp [W, h1a, h1b, h2a, h2b]

/-- The value and derivative at `π` of a solution, through the monodromy entries. -/
lemma p1o_hill_data_pi (hQ : Continuous Q) {w : ℝ → ℂ} (hw : IsHillSolution Q lam w) :
    w Real.pi = w 0 * hillWI Q Real.pi lam + deriv w 0 * hillWII Q Real.pi lam ∧
      deriv w Real.pi = w 0 * deriv (fun x => hillWI Q x lam) Real.pi +
        deriv w 0 * deriv (fun x => hillWII Q x lam) Real.pi := by
  have h1 := (hillWI_spec hQ lam).1
  have h2 := (hillWII_spec hQ lam).1
  have he := hw.eq_combination hQ
  refine ⟨congrFun he Real.pi, ?_⟩
  conv_lhs => rw [he]
  exact (((h1.differentiable _).hasDerivAt.const_mul _).add
    ((h2.differentiable _).hasDerivAt.const_mul _)).deriv

/-- A solution has multiplier `ρ` iff its data at `π` are `ρ` times its data at `0`. -/
lemma p1o_hill_multiplier_iff (hQ : IsHillPotential Q) {w : ℝ → ℂ}
    (hw : IsHillSolution Q lam w) (ρ : ℂ) :
    (∀ x, w (x + Real.pi) = ρ * w x) ↔
      (w Real.pi = ρ * w 0 ∧ deriv w Real.pi = ρ * deriv w 0) := by
  constructor
  · intro h
    refine ⟨by simpa using h 0, ?_⟩
    have hf : (fun x => w (x + Real.pi)) = fun x => ρ * w x := funext h
    have := congrArg (fun f => deriv f 0) hf
    rw [deriv_comp_add_const, zero_add] at this
    rw [this]
    exact ((hw.differentiable 0).hasDerivAt.const_mul ρ).deriv
  · rintro ⟨h0, h1⟩ x
    rw [p1o_hill_shift hQ hw x, h0, h1, congrFun (hw.eq_combination hQ.continuous) x]
    ring

/-- A solution with vanishing data at `0` vanishes. -/
lemma p1o_hill_eq_zero (hQ : Continuous Q) {w : ℝ → ℂ} (hw : IsHillSolution Q lam w)
    (h0 : w 0 = 0) (h1 : deriv w 0 = 0) (x : ℝ) : w x = 0 := by
  have := congrFun (hw.eq_combination hQ) x
  simpa [h0, h1] using this

/-- The solution `X w_I + Y w_II`. -/
lemma p1o_hill_comb (hQ : Continuous Q) (X Y : ℂ) :
    IsHillSolution Q lam (fun x => X * hillWI Q x lam + Y * hillWII Q x lam) ∧
      X * hillWI Q 0 lam + Y * hillWII Q 0 lam = X ∧
      deriv (fun x => X * hillWI Q x lam + Y * hillWII Q x lam) 0 = Y := by
  obtain ⟨h1, h1a, h1b⟩ := hillWI_spec hQ lam
  obtain ⟨h2, h2a, h2b⟩ := hillWII_spec hQ lam
  refine ⟨(h1.const_smul X).add (h2.const_smul Y), by simp [h1a, h2a], ?_⟩
  rw [show deriv (fun x => X * hillWI Q x lam + Y * hillWII Q x lam) 0 =
      X * deriv (fun x => hillWI Q x lam) 0 + Y * deriv (fun x => hillWII Q x lam) 0 from
    (((h1.differentiable 0).hasDerivAt.const_mul X).add
      ((h2.differentiable 0).hasDerivAt.const_mul Y)).deriv, h1b, h2b]
  ring

/-- A nontrivial solution with multiplier `ρ` exists iff `(a - ρ)(d - ρ) - bc = 0`, where
`[[a, b], [c, d]]` is the monodromy matrix. -/
lemma p1o_hill_exists_multiplier_iff (hQ : IsHillPotential Q) (ρ : ℂ) :
    (∃ w, IsHillSolution Q lam w ∧ (∃ x, w x ≠ 0) ∧ ∀ x, w (x + Real.pi) = ρ * w x) ↔
      (hillWI Q Real.pi lam - ρ) * (deriv (fun x => hillWII Q x lam) Real.pi - ρ) -
        hillWII Q Real.pi lam * deriv (fun x => hillWI Q x lam) Real.pi = 0 := by
  set a := hillWI Q Real.pi lam
  set b := hillWII Q Real.pi lam
  set c := deriv (fun x => hillWI Q x lam) Real.pi
  set d := deriv (fun x => hillWII Q x lam) Real.pi
  constructor
  · rintro ⟨w, hw, ⟨x₀, hx₀⟩, hm⟩
    obtain ⟨e1, e2⟩ := (p1o_hill_multiplier_iff hQ hw ρ).1 hm
    obtain ⟨f1, f2⟩ := p1o_hill_data_pi hQ.continuous hw
    rw [f1] at e1; rw [f2] at e2
    have hX : w 0 * ((a - ρ) * (d - ρ) - b * c) = 0 := by linear_combination (d - ρ) * e1 - b * e2
    have hY : deriv w 0 * ((a - ρ) * (d - ρ) - b * c) = 0 := by
      linear_combination (a - ρ) * e2 - c * e1
    by_contra hne
    exact hx₀ (p1o_hill_eq_zero hQ.continuous hw ((mul_eq_zero.mp hX).resolve_right hne)
      ((mul_eq_zero.mp hY).resolve_right hne) x₀)
  · intro hdet
    obtain ⟨X, Y, hXY, e1, e2⟩ : ∃ X Y : ℂ, (X ≠ 0 ∨ Y ≠ 0) ∧ X * a + Y * b = ρ * X ∧
        X * c + Y * d = ρ * Y := by
      by_cases hb : b ≠ 0 ∨ ρ - a ≠ 0
      · exact ⟨b, ρ - a, hb, by ring, by linear_combination -hdet⟩
      push Not at hb
      obtain ⟨hb, ha⟩ := hb
      have ha' : a = ρ := by linear_combination -ha
      by_cases hd : ρ - d ≠ 0 ∨ c ≠ 0
      · exact ⟨ρ - d, c, hd, by rw [hb, ha']; ring, by ring⟩
      push Not at hd
      obtain ⟨hd, hc⟩ := hd
      exact ⟨1, 0, Or.inl one_ne_zero, by rw [ha']; ring, by rw [hc]; ring⟩
    obtain ⟨hs, hs0, hs1⟩ := p1o_hill_comb (lam := lam) hQ.continuous X Y
    refine ⟨_, hs, ?_, (p1o_hill_multiplier_iff hQ hs ρ).2 ?_⟩
    · by_contra hall
      push Not at hall
      rcases hXY with hX | hY
      · exact hX (by rw [← hs0]; exact hall 0)
      · apply hY
        rw [← hs1, show (fun x => X * hillWI Q x lam + Y * hillWII Q x lam) = fun _ => 0 from
          funext hall]
        simp
    · obtain ⟨f1, f2⟩ := p1o_hill_data_pi hQ.continuous hs
      rw [f1, f2, hs0, hs1]
      exact ⟨e1, e2⟩

/-- The two-step relation `u(z + 2π) = Δ(λ) u(z + π) - u(z)` (Cayley–Hamilton for the
monodromy matrix, whose determinant is the Wronskian `1`). -/
lemma p1o_hill_two_step (hQ : IsHillPotential Q) {u : ℝ → ℂ} (hu : IsHillSolution Q lam u)
    (z : ℝ) : u (z + Real.pi + Real.pi) = hillDiscriminant Q lam * u (z + Real.pi) - u z := by
  have hv := hu.comp_add_pi hQ.periodic
  have hW := p1o_hill_wronskian (lam := lam) hQ.continuous Real.pi
  have s1 := p1o_hill_shift hQ hv z
  have s2 := p1o_hill_shift hQ hu z
  have d1 := p1o_hill_data_pi hQ.continuous hv
  have d0 := p1o_hill_data_pi hQ.continuous hu
  have e := congrFun (hu.eq_combination hQ.continuous) z
  rw [deriv_comp_add_const, zero_add] at d1
  rw [s1, s2, d1.1, d1.2, d0.1, d0.2, hillDiscriminant]
  conv_rhs => rw [e]
  linear_combination (-(u 0 * hillWI Q z lam) - deriv u 0 * hillWII Q z lam) * hW

/-- The data of a solution with multiplier `ρ` form an eigenvector of the monodromy matrix. -/
lemma p1o_hill_multiplier_data (hQ : IsHillPotential Q) {u : ℝ → ℂ}
    (hu : IsHillSolution Q lam u) {ρ : ℂ} (hm : ∀ x, u (x + Real.pi) = ρ * u x) :
    u 0 * hillWI Q Real.pi lam + deriv u 0 * hillWII Q Real.pi lam = ρ * u 0 ∧
      u 0 * deriv (fun x => hillWI Q x lam) Real.pi +
        deriv u 0 * deriv (fun x => hillWII Q x lam) Real.pi = ρ * deriv u 0 := by
  obtain ⟨e1, e2⟩ := (p1o_hill_multiplier_iff hQ hu ρ).1 hm
  obtain ⟨f1, f2⟩ := p1o_hill_data_pi hQ.continuous hu
  exact ⟨f1 ▸ e1, f2 ▸ e2⟩

/-- `exp(-πiν) = exp(πiν)⁻¹` and `2 cos πν = exp(πiν) + exp(πiν)⁻¹`. -/
lemma p1o_two_cos_eq (ν : ℂ) :
    2 * Complex.cos (Real.pi * ν) = Complex.exp (Real.pi * I * ν) +
      (Complex.exp (Real.pi * I * ν))⁻¹ := by
  rw [Complex.two_cos, ← Complex.exp_neg]; ring_nf

/-- Two eigenvectors of a `2 × 2` matrix `≠ ρ • 1` for the same eigenvalue `ρ` are parallel. -/
lemma p1o_cross_eq_zero_of_kernel {a b c d x1 y1 x2 y2 ρ : ℂ}
    (h : ¬(a - ρ = 0 ∧ b = 0 ∧ c = 0 ∧ d - ρ = 0)) (e1 : x1 * a + y1 * b = ρ * x1)
    (e2 : x1 * c + y1 * d = ρ * y1) (f1 : x2 * a + y2 * b = ρ * x2)
    (f2 : x2 * c + y2 * d = ρ * y2) : x1 * y2 - y1 * x2 = 0 := by
  have k1 : (a - ρ) * (x1 * y2 - y1 * x2) = 0 := by linear_combination y2 * e1 - y1 * f1
  have k2 : b * (x1 * y2 - y1 * x2) = 0 := by linear_combination x1 * f1 - x2 * e1
  have k3 : c * (x1 * y2 - y1 * x2) = 0 := by linear_combination y2 * e2 - y1 * f2
  have k4 : (d - ρ) * (x1 * y2 - y1 * x2) = 0 := by linear_combination x1 * f2 - x2 * e2
  by_contra hne
  exact h ⟨(mul_eq_zero.mp k1).resolve_right hne, (mul_eq_zero.mp k2).resolve_right hne,
    (mul_eq_zero.mp k3).resolve_right hne, (mul_eq_zero.mp k4).resolve_right hne⟩

/-- A vector with vanishing cross product with a nonzero vector is a multiple of it. -/
lemma p1o_exists_smul_of_cross {x1 y1 x2 y2 : ℂ} (hne : x1 ≠ 0 ∨ y1 ≠ 0)
    (h : x1 * y2 - y1 * x2 = 0) : ∃ k, x2 = k * x1 ∧ y2 = k * y1 := by
  by_cases hx : x1 ≠ 0
  · refine ⟨x2 / x1, by field_simp, ?_⟩
    field_simp; linear_combination h
  · push Not at hx
    have hy := hne.resolve_left (not_not.mpr hx)
    subst hx
    refine ⟨y2 / y1, ?_, by field_simp⟩
    have : y1 * x2 = 0 := by linear_combination -h
    simp [(mul_eq_zero.mp this).resolve_left hy]

/-- Derivative at `0` of a combination of solutions. -/
lemma p1o_deriv_comb {u v : ℝ → ℂ} (hu : IsHillSolution Q lam u) (hv : IsHillSolution Q lam v)
    (c₁ c₂ : ℂ) (x : ℝ) : deriv (c₁ • u + c₂ • v) x = c₁ * deriv u x + c₂ * deriv v x := by
  rw [deriv_add ((hu.differentiable x).const_smul _) ((hv.differentiable x).const_smul _),
    deriv_const_smul _ (hu.differentiable x), deriv_const_smul _ (hv.differentiable x)]
  rfl

/-- Two solutions whose data at `0` are proportional are proportional. -/
lemma p1o_hill_eq_smul (hQ : Continuous Q) {u v : ℝ → ℂ} (hu : IsHillSolution Q lam u)
    (hv : IsHillSolution Q lam v) {k : ℂ} (h0 : v 0 = k * u 0)
    (h1 : deriv v 0 = k * deriv u 0) (x : ℝ) : v x = k * u x := by
  have := hv.eq_of_initial hQ (hu.const_smul k) (x₀ := 0) (by simp [h0])
    (by rw [deriv_const_smul _ (hu.differentiable 0), h1]; rfl)
  simpa using congrFun this x

/-- Iterating a multiplier: `u(x + kπ) = ρᵏ u(x)`. -/
lemma p1o_iter_mult {u : ℝ → ℂ} {ρ : ℂ} (hm : ∀ x, u (x + Real.pi) = ρ * u x) (k : ℕ)
    (x : ℝ) : u (x + k * Real.pi) = ρ ^ k * u x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show x + ((k + 1 : ℕ) : ℝ) * Real.pi = x + k * Real.pi + Real.pi by push_cast; ring, hm,
      ih, pow_succ]
    ring

/-- Iterating `w(z + π) = s w(z) + c P(z)` with `P(z + π) = s P(z)`. -/
lemma p1o_iter_jordan {w P : ℝ → ℂ} {s c : ℂ} (hP : ∀ x, P (x + Real.pi) = s * P x)
    (hw : ∀ x, w (x + Real.pi) = s * w x + c * P x) (k : ℕ) (x : ℝ) :
    w (x + (k + 1 : ℕ) * Real.pi) = s ^ (k + 1) * w x + (k + 1 : ℕ) * s ^ k * c * P x := by
  induction k with
  | zero => simpa using hw x
  | succ k ih =>
    rw [show x + ((k + 1 + 1 : ℕ) : ℝ) * Real.pi = x + ((k + 1 : ℕ) : ℝ) * Real.pi + Real.pi by
      push_cast; ring, hw, ih, p1o_iter_mult hP]
    push_cast; ring

/-- For `ν ∉ {0, 1}` with `-1 < ℜν ≤ 1`, the multipliers `e^{±πiν}` are distinct. -/
lemma p1o_exp_ne {ν : ℂ} (hν : -1 < ν.re ∧ ν.re ≤ 1) (hν0 : ν ≠ 0) (hν1 : ν ≠ 1) :
    Complex.exp (Real.pi * I * ν) ≠ Complex.exp (Real.pi * I * -ν) := by
  intro h
  have h2 : Complex.exp (ν * (2 * Real.pi * I)) = 1 := by
    have : Complex.exp (ν * (2 * Real.pi * I)) =
        Complex.exp (Real.pi * I * ν) / Complex.exp (Real.pi * I * -ν) := by
      rw [← Complex.exp_sub]; ring_nf
    rw [this, h, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h2
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hνn : ν = n := mul_right_cancel₀ hpi hn
  rw [hνn] at hν hν0 hν1
  simp only [intCast_re] at hν
  have : n = 0 ∨ n = 1 := by
    obtain ⟨l, r⟩ := hν
    have l' : -1 < n := by exact_mod_cast l
    have r' : n ≤ 1 := by exact_mod_cast r
    omega
  rcases this with rfl | rfl
  · exact hν0 (by simp)
  · exact hν1 (by simp)

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
  rw [Matrix.det_fin_two]
  simp only [hillMonodromy, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul, mul_one]
  simp only [Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_zero, sub_zero]
  rw [← p1o_hill_exists_multiplier_iff hQ]
  rfl

/-- **Characteristic equation** of Hill's equation (DLMF 28.29.9): a Floquet solution with
respect to `ν` exists iff `2 cos(πν) = w_I(π, λ) + w_II'(π, λ)`. -/
@[dlmf 28.29.E9]
theorem exists_hillFloquet_iff_discriminant (hQ : IsHillPotential Q) (lam ν : ℂ) :
    (∃ w, IsHillFloquetSolution Q lam ν w) ↔
      2 * Complex.cos (Real.pi * ν) = hillDiscriminant Q lam := by
  have hW := p1o_hill_wronskian (lam := lam) hQ.continuous Real.pi
  change (∃ w, IsHillSolution Q lam w ∧ (∃ x, w x ≠ 0) ∧ ∀ x, w (x + Real.pi) = _ * w x) ↔ _
  rw [p1o_hill_exists_multiplier_iff hQ, Complex.two_cos, hillDiscriminant]
  set ρ := Complex.exp (Real.pi * I * ν)
  have hρ : ρ ≠ 0 := Complex.exp_ne_zero _
  have e1 : Complex.exp (↑Real.pi * ν * I) = ρ := by simp only [ρ]; ring_nf
  have e2 : Complex.exp (-(↑Real.pi * ν) * I) = ρ⁻¹ := by
    simp only [ρ]; rw [← Complex.exp_neg]; ring_nf
  rw [e1, e2]
  constructor
  · intro h
    field_simp
    linear_combination h - hW
  · intro h
    field_simp at h
    linear_combination h + hW

/-- `cos(πν) = Δ(λ)/2` is an **entire function of `λ`** (DLMF §28.29(ii), after 28.29.9; also
§28.29(iii): the discriminant is entire). -/
@[dlmf 28.29.ii, dlmf 28.29.iii]
theorem differentiable_hillDiscriminant (hQ : IsHillPotential Q) :
    Differentiable ℂ (hillDiscriminant Q) := by
  have hI := ODE.differentiable_param_of_linear_ode (p₀ := fun _ => 0) (p₁ := fun _ => 0)
    (q₀ := fun x => -Q x) (q₁ := fun _ => -1) continuous_const continuous_const
    hQ.continuous.neg continuous_const (t₀ := 0) (y₀ := 1) (y₁ := 0)
    (F := fun x μ => hillWI Q x μ) (F' := fun x μ => deriv (fun x => hillWI Q x μ) x)
    (fun μ t => ⟨(hillWI_spec hQ.continuous μ).1.hasDerivAt t,
      ((hillWI_spec hQ.continuous μ).1.hasDerivAt_deriv t).congr_deriv (by ring)⟩)
    (fun μ => (hillWI_spec hQ.continuous μ).2.1) (fun μ => (hillWI_spec hQ.continuous μ).2.2)
    Real.pi
  have hII := ODE.differentiable_param_of_linear_ode (p₀ := fun _ => 0) (p₁ := fun _ => 0)
    (q₀ := fun x => -Q x) (q₁ := fun _ => -1) continuous_const continuous_const
    hQ.continuous.neg continuous_const (t₀ := 0) (y₀ := 0) (y₁ := 1)
    (F := fun x μ => hillWII Q x μ) (F' := fun x μ => deriv (fun x => hillWII Q x μ) x)
    (fun μ t => ⟨(hillWII_spec hQ.continuous μ).1.hasDerivAt t,
      ((hillWII_spec hQ.continuous μ).1.hasDerivAt_deriv t).congr_deriv (by ring)⟩)
    (fun μ => (hillWII_spec hQ.continuous μ).2.1) (fun μ => (hillWII_spec hQ.continuous μ).2.2)
    Real.pi
  exact hI.1.add hII.2

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
  obtain ⟨w₁, hw₁⟩ := (exists_hillFloquet_iff_discriminant hQ lam ν).2 hc
  obtain ⟨w₂, hw₂⟩ := (exists_hillFloquet_iff_discriminant hQ lam (-ν)).2
    (by rw [mul_neg, Complex.cos_neg]; exact hc)
  refine ⟨w₁, w₂, hw₁, hw₂, fun w hw => ?_⟩
  obtain ⟨s₁, ⟨z₁, hz₁⟩, m₁⟩ := hw₁
  obtain ⟨s₂, ⟨z₂, hz₂⟩, m₂⟩ := hw₂
  set ρ := Complex.exp (Real.pi * I * ν)
  set σ := Complex.exp (Real.pi * I * -ν)
  have hρσ : ρ ≠ σ := by
    intro h
    have h2 : Complex.exp (ν * (2 * Real.pi * I)) = 1 := by
      have : Complex.exp (ν * (2 * Real.pi * I)) = ρ / σ := by
        simp only [ρ, σ]; rw [← Complex.exp_sub]; ring_nf
      rw [this, h, div_self (Complex.exp_ne_zero _)]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h2
    have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, I_ne_zero]
    have hνn : ν = n := mul_right_cancel₀ hpi hn
    rw [hνn] at hν hν0 hν1
    simp only [intCast_re] at hν
    have : n = 0 ∨ n = 1 := by
      obtain ⟨l, r⟩ := hν
      have l' : -1 < n := by exact_mod_cast l
      have r' : n ≤ 1 := by exact_mod_cast r
      omega
    rcases this with rfl | rfl
    · exact hν0 (by simp)
    · exact hν1 (by simp)
  have hne1 : (w₁ 0) ≠ 0 ∨ (deriv w₁ 0) ≠ 0 := by
    by_contra hc'
    push Not at hc'
    exact hz₁ (p1o_hill_eq_zero hQ.continuous s₁ hc'.1 hc'.2 z₁)
  have hD : (w₁ 0) * (deriv w₂ 0) - (deriv w₁ 0) * (w₂ 0) ≠ 0 := by
    intro hD
    obtain ⟨k, hk0, hk1⟩ := p1o_exists_smul_of_cross hne1 hD
    have hk := p1o_hill_eq_smul hQ.continuous s₁ s₂ hk0 hk1
    apply hρσ
    have e := m₂ z₂
    have e' : w₂ (z₂ + Real.pi) = ρ * w₂ z₂ := by rw [hk, m₁, hk]; ring
    have : (ρ - σ) * w₂ z₂ = 0 := by linear_combination e - e'
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hz₂)
  refine ⟨(w 0 * deriv w₂ 0 - deriv w 0 * w₂ 0) / (w₁ 0 * deriv w₂ 0 - deriv w₁ 0 * w₂ 0),
    (w₁ 0 * deriv w 0 - deriv w₁ 0 * w 0) / (w₁ 0 * deriv w₂ 0 - deriv w₁ 0 * w₂ 0), ?_⟩
  refine hw.eq_of_initial hQ.continuous ((s₁.const_smul _).add (s₂.const_smul _)) (x₀ := 0)
    ?_ ?_
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD]
    ring
  · rw [p1o_deriv_comb s₁ s₂]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD]
    ring

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
  have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hW := p1o_hill_wronskian (lam := lam) hQ.continuous Real.pi
  have hΔ' := hΔ
  rw [hillDiscriminant] at hΔ'
  obtain ⟨P, hP, ⟨x₀, hx₀⟩, hPm⟩ := (p1o_hill_exists_multiplier_iff (lam := lam) hQ s).2
    (by linear_combination hW - s * hΔ' - hs2)
  refine ⟨P, ⟨hP, hPm⟩, fun h => hx₀ (by rw [h]; rfl), fun w hw => ?_⟩
  set v : ℝ → ℂ := fun z => w (z + Real.pi) - s * w z
  have hv : IsHillSolution Q lam v := by
    have := (hw.comp_add_pi hQ.periodic).add (hw.const_smul (-s))
    convert this using 1
    funext z; simp only [v, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hvm : ∀ z, v (z + Real.pi) = s * v z := fun z => by
    simp only [v]
    rw [p1o_hill_two_step hQ hw z, hΔ]
    linear_combination (w z) * hs2
  obtain ⟨e1, e2⟩ := p1o_hill_multiplier_data hQ hP hPm
  obtain ⟨f1, f2⟩ := p1o_hill_multiplier_data hQ hv hvm
  by_cases hN : hillWI Q Real.pi lam - s = 0 ∧ hillWII Q Real.pi lam = 0 ∧
      deriv (fun x => hillWI Q x lam) Real.pi = 0 ∧
      deriv (fun x => hillWII Q x lam) Real.pi - s = 0
  · refine ⟨0, fun z => ?_⟩
    obtain ⟨g1, g2⟩ := p1o_hill_data_pi hQ.continuous hw
    have := (p1o_hill_multiplier_iff hQ hw s).2 ⟨by rw [g1, hN.2.1,
      show hillWI Q Real.pi lam = s by linear_combination hN.1]; ring,
      by rw [g2, hN.2.2.1, show deriv (fun x => hillWII Q x lam) Real.pi = s by
        linear_combination hN.2.2.2]; ring⟩ z
    rw [this]; ring
  · have hcross := p1o_cross_eq_zero_of_kernel hN e1 e2 f1 f2
    have hPne : P 0 ≠ 0 ∨ deriv P 0 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hx₀ (p1o_hill_eq_zero hQ.continuous hP hc.1 hc.2 x₀)
    obtain ⟨k, hk0, hk1⟩ := p1o_exists_smul_of_cross hPne hcross
    refine ⟨k, fun z => ?_⟩
    have := p1o_hill_eq_smul hQ.continuous hP hv hk0 hk1 z
    simp only [v] at this
    linear_combination this

/-- **Coexistence** (DLMF 28.29.12): with `Δ(λ) = 2s`, `s = (-1)^ν = ±1`, the constant `c` of
28.29.11 vanishes for all solutions (all solutions have multiplier `s`) iff the monodromy
matrix is `s` times the identity. -/
@[dlmf 28.29.E12]
theorem hill_coexistence_iff (hQ : IsHillPotential Q) {s : ℂ} (hs : s = 1 ∨ s = -1)
    (hΔ : hillDiscriminant Q lam = 2 * s) :
    (∀ w, IsHillSolution Q lam w → w ∈ hillMultiplierSolutions Q lam s) ↔
      hillMonodromy Q lam = s • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨h1, h1a, h1b⟩ := hillWI_spec hQ.continuous lam
  obtain ⟨h2, h2a, h2b⟩ := hillWII_spec hQ.continuous lam
  constructor
  · intro h
    obtain ⟨e1, e2⟩ := (p1o_hill_multiplier_iff hQ h1 s).1 (h _ h1).2
    obtain ⟨f1, f2⟩ := (p1o_hill_multiplier_iff hQ h2 s).1 (h _ h2).2
    rw [h1a] at e1; rw [h1b] at e2; rw [h2a] at f1; rw [h2b] at f2
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hillMonodromy, e1, e2, f1, f2]
  · intro hM w hw
    have m00 := congrFun (congrFun hM 0) 0
    have m01 := congrFun (congrFun hM 0) 1
    have m10 := congrFun (congrFun hM 1) 0
    have m11 := congrFun (congrFun hM 1) 1
    simp [hillMonodromy] at m00 m01 m10 m11
    obtain ⟨f1, f2⟩ := p1o_hill_data_pi hQ.continuous hw
    refine ⟨hw, (p1o_hill_multiplier_iff hQ hw s).2 ⟨?_, ?_⟩⟩
    · rw [f1, m00, m01]; ring
    · rw [f2, m10, m11]; ring

/-- **Periodic solutions of period `nπ`, `n ≥ 3`** (DLMF §28.29(ii)): if Hill's equation has
a periodic solution with minimum period `nπ`, `n = 3, 4, …`, then all its solutions have
period `nπ`. -/
@[dlmf 28.29.ii]
theorem hill_all_periodic_of_minimal_period (hQ : IsHillPotential Q) {n : ℕ} (hn : 3 ≤ n)
    {w : ℝ → ℂ} (hw : IsHillSolution Q lam w) (hper : Function.Periodic w (n * Real.pi))
    (hmin : ∀ T : ℝ, 0 < T → T < n * Real.pi → ¬ Function.Periodic w T) :
    ∀ v, IsHillSolution Q lam v → Function.Periodic v (n * Real.pi) := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi := Real.pi_pos
  -- a solution with a multiplier `±1` has period `2π`, which is excluded
  have hno : ∀ s : ℂ, s = 1 ∨ s = -1 → ¬ ∀ x, w (x + Real.pi) = s * w x := by
    intro s hs hm
    refine hmin (2 * Real.pi) (by positivity) (by nlinarith) fun x => ?_
    have := p1o_iter_mult hm 2 x
    push_cast at this
    rw [this]; rcases hs with rfl | rfl <;> norm_num
  obtain ⟨ν, hν1, hν2, hc⟩ := exists_hillCharExp Q lam
  by_cases hν : ν = 0 ∨ ν = 1
  · exfalso
    obtain ⟨s, hs, hΔ⟩ : ∃ s : ℂ, (s = 1 ∨ s = -1) ∧ hillDiscriminant Q lam = 2 * s := by
      rcases hν with rfl | rfl
      · exact ⟨1, Or.inl rfl, by rw [← hc]; simp⟩
      · exact ⟨-1, Or.inr rfl, by rw [← hc]; simp⟩
    obtain ⟨P, ⟨hP, hPm⟩, hP0, hall⟩ := exists_hill_periodic_of_discriminant hQ hs hΔ
    obtain ⟨c, hcw⟩ := hall w hw
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
    by_cases hc0 : c = 0
    · exact hno s hs fun x => by rw [hcw, hc0]; ring
    have hit := fun x => p1o_iter_jordan hPm hcw m x
    by_cases hsn : s ^ (m + 1) = 1
    · apply hP0
      funext x
      have h := hit x
      rw [hper x, hsn] at h
      have : ((m + 1 : ℕ) : ℂ) * s ^ m * c * P x = 0 := by linear_combination -h
      have hm1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
      exact (mul_eq_zero.mp this).resolve_left
        (mul_ne_zero (mul_ne_zero hm1 (pow_ne_zero m hs0)) hc0)
    · apply hno s hs
      have hκ : ∀ x, w x = ((m + 1 : ℕ) * s ^ m * c / (1 - s ^ (m + 1))) * P x := by
        intro x
        have h := hit x
        rw [hper x] at h
        have h1 : 1 - s ^ (m + 1) ≠ 0 := sub_ne_zero.mpr (Ne.symm hsn)
        field_simp
        linear_combination h
      intro x
      rw [hκ, hκ, hPm]; ring
  · push Not at hν
    obtain ⟨w₁, w₂, ⟨s₁, ⟨z₁, hz₁⟩, m₁⟩, ⟨s₂, ⟨z₂, hz₂⟩, m₂⟩, hall⟩ :=
      exists_hillFloquet_fundamental_pair hQ ⟨hν1, hν2⟩ hν.1 hν.2 hc
    set ρ := Complex.exp (Real.pi * I * ν)
    set σ := Complex.exp (Real.pi * I * -ν)
    have hρσ : ρ ≠ σ := p1o_exp_ne ⟨hν1, hν2⟩ hν.1 hν.2
    have hprod : ρ * σ = 1 := by
      simp only [ρ, σ]; rw [← Complex.exp_add]; ring_nf; simp
    obtain ⟨c₁, c₂, hwc⟩ := hall w hw
    have E : ∀ x, c₁ * (ρ ^ n - 1) * w₁ x + c₂ * (σ ^ n - 1) * w₂ x = 0 := by
      intro x
      have h := hper x
      rw [hwc] at h
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, p1o_iter_mult m₁,
        p1o_iter_mult m₂] at h
      linear_combination h
    have E2 : ∀ x, c₂ * (σ ^ n - 1) * (ρ - σ) * w₂ x = 0 := by
      intro x
      have h1 := E x
      have h2 := E (x + Real.pi)
      rw [m₁, m₂] at h2
      linear_combination ρ * h1 - h2
    have E1 : ∀ x, c₁ * (ρ ^ n - 1) * (σ - ρ) * w₁ x = 0 := by
      intro x
      have h1 := E x
      have h2 := E (x + Real.pi)
      rw [m₁, m₂] at h2
      linear_combination σ * h1 - h2
    have k2 : c₂ * (σ ^ n - 1) = 0 := by
      have := E2 z₂
      simpa [hz₂, sub_ne_zero.mpr hρσ] using this
    have k1 : c₁ * (ρ ^ n - 1) = 0 := by
      have := E1 z₁
      simpa [hz₁, sub_ne_zero.mpr (Ne.symm hρσ)] using this
    have hboth : ρ ^ n = 1 ∧ σ ^ n = 1 := by
      have hpn : ρ ^ n * σ ^ n = 1 := by rw [← mul_pow, hprod, one_pow]
      by_cases h1 : c₁ = 0
      · by_cases h2 : c₂ = 0
        · exfalso
          refine hno 1 (Or.inl rfl) fun x => ?_
          rw [hwc, h1, h2]; simp
        · have : σ ^ n = 1 := sub_eq_zero.mp ((mul_eq_zero.mp k2).resolve_left h2)
          exact ⟨by rw [this, mul_one] at hpn; exact hpn, this⟩
      · have : ρ ^ n = 1 := sub_eq_zero.mp ((mul_eq_zero.mp k1).resolve_left h1)
        exact ⟨this, by rw [this, one_mul] at hpn; exact hpn⟩
    intro v hv x
    obtain ⟨d₁, d₂, hvd⟩ := hall v hv
    rw [hvd]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, p1o_iter_mult m₁, p1o_iter_mult m₂,
      hboth.1, hboth.2, one_mul]

/-- DLMF 28.29.13: every solution satisfies `w(z + π) + w(z - π) = 2 cos(πν) w(z)`, where
`2 cos(πν) = Δ(λ)`. -/
@[dlmf 28.29.E13]
theorem IsHillSolution.add_pi_add_sub_pi (hQ : IsHillPotential Q) {ν : ℂ}
    (hc : 2 * Complex.cos (Real.pi * ν) = hillDiscriminant Q lam) {w : ℝ → ℂ}
    (hw : IsHillSolution Q lam w) (z : ℝ) :
    w (z + Real.pi) + w (z - Real.pi) = 2 * Complex.cos (Real.pi * ν) * w z := by
  have h := p1o_hill_two_step hQ hw (z - Real.pi)
  rw [sub_add_cancel] at h
  rw [h, hc]; ring

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
  set ρ := Complex.exp (Real.pi * I * ν)
  have hρ : ρ ≠ 0 := Complex.exp_ne_zero _
  have hρ' : Complex.exp (I * ν * Real.pi) = ρ := by simp only [ρ]; ring_nf
  have hρ'' : Complex.exp (Real.pi * I * -ν) = ρ⁻¹ := by
    simp only [ρ]; rw [← Complex.exp_neg]; ring_nf
  unfold IsHillFloquetSolution
  rw [hρ', hρ'']
  rw [p1o_two_cos_eq] at hc
  by_cases hv : ∀ z, w (z + Real.pi) - ρ * w z = 0
  · left
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hw0
    exact ⟨hw, ⟨x, hx⟩, fun z => sub_eq_zero.mp (hv z)⟩
  · right
    push Not at hv
    refine ⟨?_, hv, fun z => ?_⟩
    · have := (hw.comp_add_pi hQ.periodic).add (hw.const_smul (-ρ))
      convert this using 1
      funext z; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    · have h := p1o_hill_two_step hQ hw z
      beta_reduce
      rw [h, ← hc]
      field_simp
      ring

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
  have hW := p1o_hill_wronskian (lam := lam) hQ.continuous Real.pi
  have h1 := hillWI_add_pi hQ lam (-Real.pi)
  have h2 := hillWII_add_pi hQ lam (-Real.pi)
  rw [neg_add_cancel, hillWI_neg_of_even hQ.continuous heven,
    hillWII_neg_of_even hQ.continuous heven, (hillWI_spec hQ.continuous lam).2.1] at h1
  rw [neg_add_cancel, hillWI_neg_of_even hQ.continuous heven,
    hillWII_neg_of_even hQ.continuous heven, (hillWII_spec hQ.continuous lam).2.1] at h2
  rw [hillDiscriminant]
  set a := hillWI Q Real.pi lam
  set b := hillWII Q Real.pi lam
  set c := deriv (fun x => hillWI Q x lam) Real.pi
  set d := deriv (fun x => hillWII Q x lam) Real.pi
  have ha : a * (a - d) = 0 := by linear_combination -h1 - hW
  have hb : b * (a - d) = 0 := by linear_combination -h2
  by_cases had : a - d = 0
  · linear_combination -had
  · have ha0 := (mul_eq_zero.mp ha).resolve_right had
    have hb0 := (mul_eq_zero.mp hb).resolve_right had
    rw [ha0, hb0] at hW
    simp at hW

/-! ### §28.29(iii) The discriminant and the eigenvalues (real `Q`) -/

/-- Upper growth bound for the discriminant: for `‖λ‖ ≥ 1`,
`‖Δ(λ)‖ ≤ 2 e^{Mπ/2} e^{π ‖λ‖^{1/2}}`, where `‖Q‖ ≤ M` on `[0, π]`. -/
lemma p2s_hillDiscriminant_le {Q : ℝ → ℂ} (hQc : Continuous Q) {M : ℝ} (hM : 0 ≤ M)
    (hQM : ∀ x ∈ Icc 0 Real.pi, ‖Q x‖ ≤ M) {lam : ℂ} (hlam : 1 ≤ ‖lam‖) :
    ‖hillDiscriminant Q lam‖ ≤
      2 * Real.exp (M * Real.pi / 2) * Real.exp (Real.pi * Real.sqrt ‖lam‖) := by
  set k := Real.sqrt ‖lam‖
  have hk : 1 ≤ k := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hlam
  have hk2 : k ^ 2 = ‖lam‖ := Real.sq_sqrt (by linarith)
  have hP : ∀ x ∈ Icc 0 Real.pi, ‖-(lam + Q x)‖ ≤ M + k ^ 2 := fun x hx => by
    rw [norm_neg, hk2]; linarith [norm_add_le lam (Q x), hQM x hx]
  have hπ : Real.pi ∈ Icc 0 Real.pi := ⟨Real.pi_pos.le, le_rfl⟩
  obtain ⟨sI, sI0, sI1⟩ := hillWI_spec hQc lam
  obtain ⟨sII, sII0, sII1⟩ := hillWII_spec hQc lam
  have eI := ODE.p2s_energy_complex_le hM hk hP sI.hasDerivAt sI.hasDerivAt_deriv hπ
  have eII := ODE.p2s_energy_complex_le hM hk hP sII.hasDerivAt sII.hasDerivAt_deriv hπ
  rw [sI0, sI1] at eI
  rw [sII0, sII1] at eII
  simp only [norm_zero, norm_one] at eI eII
  simp only [zero_pow two_ne_zero, one_pow, mul_one, zero_add, mul_zero, add_zero,
    one_mul] at eI eII
  set B := Real.exp ((M + 2 * k) * Real.pi)
  have hB : B =
      (Real.exp (M * Real.pi / 2) * Real.exp (Real.pi * k)) ^ 2 := by
    rw [← Real.exp_add, sq, ← Real.exp_add]; simp only [B]; ring_nf
  have hsq : ∀ {u : ℝ}, 0 ≤ u → u ^ 2 ≤ B → u ≤ Real.exp (M * Real.pi / 2) *
      Real.exp (Real.pi * k) := fun {u} hu h => by
    rw [hB] at h
    exact (pow_le_pow_iff_left₀ hu (by positivity) two_ne_zero).mp h
  have h1 : ‖hillWI Q Real.pi lam‖ ≤ Real.exp (M * Real.pi / 2) * Real.exp (Real.pi * k) := by
    refine hsq (norm_nonneg _) ?_
    have hk2' : 0 < k ^ 2 := by positivity
    have : k ^ 2 * ‖hillWI Q Real.pi lam‖ ^ 2 ≤ k ^ 2 * B := by
      nlinarith [sq_nonneg ‖deriv (fun x => hillWI Q x lam) Real.pi‖]
    exact le_of_mul_le_mul_left this hk2'
  have h2 : ‖deriv (fun x => hillWII Q x lam) Real.pi‖ ≤
      Real.exp (M * Real.pi / 2) * Real.exp (Real.pi * k) := by
    refine hsq (norm_nonneg _) ?_
    nlinarith [mul_nonneg (sq_nonneg k) (sq_nonneg ‖hillWII Q Real.pi lam‖)]
  calc ‖hillDiscriminant Q lam‖ ≤ ‖hillWI Q Real.pi lam‖ +
        ‖deriv (fun x => hillWII Q x lam) Real.pi‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- A solution of Hill's equation with real potential, real `λ = -t` and real data at `0` is
real, and its real part solves `y'' = (t - Q) y`. -/
lemma p2s_hill_real {Q : ℝ → ℝ} (hQc : Continuous Q) {t : ℝ} {w : ℝ → ℂ}
    (hw : IsHillSolution (fun x => (Q x : ℂ)) (-(t : ℂ)) w)
    (h0 : (starRingEnd ℂ) (w 0) = w 0) (h1 : (starRingEnd ℂ) (deriv w 0) = deriv w 0) :
    (∀ x, w x = ((w x).re : ℂ) ∧ deriv w x = ((deriv w x).re : ℂ)) ∧
      (∀ x, HasDerivAt (fun x => (w x).re) (deriv w x).re x) ∧
      (∀ x, HasDerivAt (fun x => (deriv w x).re) ((t - Q x) * (w x).re) x) := by
  have hd : ∀ x, HasDerivAt w (deriv w x) x ∧
      HasDerivAt (deriv w) (((t - Q x : ℝ) : ℂ) * w x) x := fun x =>
    ⟨hw.hasDerivAt x, (hw.hasDerivAt_deriv x).congr_deriv (by push_cast; ring)⟩
  have hP : Continuous fun x => t - Q x := by fun_prop
  have hr := ODE.p2s_conj_eq_of_linear_ode hP hd h0 h1
  refine ⟨fun x => ⟨(Complex.conj_eq_iff_re.mp (hr x).1).symm,
    (Complex.conj_eq_iff_re.mp (hr x).2).symm⟩, fun x => ?_, fun x => ?_⟩
  · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hd x).1
  · have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hd x).2
    simp only [Complex.reCLM_apply, Complex.re_ofReal_mul] at this
    exact this

/-- Lower growth bound for the discriminant of a real potential on the negative axis:
`Δ(-t) ≥ e^{π √(t - M)} / 2` when `|Q| ≤ M ≤ t` on `[0, π]`. -/
lemma p2s_hillDiscriminant_ge {Q : ℝ → ℝ} (hQc : Continuous Q) {M : ℝ}
    (hQM : ∀ x ∈ Icc 0 Real.pi, |Q x| ≤ M) {t : ℝ} (ht : M ≤ t) :
    Real.exp (Real.pi * Real.sqrt (t - M)) / 2 ≤
      ‖hillDiscriminant (fun x => (Q x : ℂ)) (-(t : ℂ))‖ := by
  have hQc' : Continuous fun x => (Q x : ℂ) := by fun_prop
  obtain ⟨sI, sI0, sI1⟩ := hillWI_spec hQc' (-(t : ℂ))
  obtain ⟨sII, sII0, sII1⟩ := hillWII_spec hQc' (-(t : ℂ))
  obtain ⟨rI, dI, dI'⟩ := p2s_hill_real hQc sI (by simp [sI0]) (by simp [sI1])
  obtain ⟨rII, dII, dII'⟩ := p2s_hill_real hQc sII (by simp [sII0]) (by simp [sII1])
  set s := Real.sqrt (t - M)
  have hs2 : s ^ 2 = t - M := Real.sq_sqrt (by linarith)
  have hp : ∀ x ∈ Icc 0 Real.pi, s ^ 2 ≤ t - Q x := fun x hx => by
    rw [hs2]; linarith [(abs_le.mp (hQM x hx)).2]
  have lI := ODE.p2s_real_lower_I Real.pi_pos.le hp dI dI' (by simp [sI0]) (by simp [sI1])
  have lII := ODE.p2s_real_lower_II Real.pi_pos.le hp dII dII' (by simp [sII0])
    (by simp [sII1])
  have hre : (hillDiscriminant (fun x => (Q x : ℂ)) (-(t : ℂ))).re =
      (hillWI (fun x => (Q x : ℂ)) Real.pi (-(t : ℂ))).re +
        (deriv (fun x => hillWII (fun x => (Q x : ℂ)) x (-(t : ℂ))) Real.pi).re := by
    simp [hillDiscriminant]
  calc Real.exp (Real.pi * s) / 2 ≤ (hillDiscriminant (fun x => (Q x : ℂ)) (-(t : ℂ))).re := by
        rw [hre, mul_comm]; linarith
    _ ≤ _ := Complex.re_le_norm _

/-- The discriminant of a real Hill equation has **order of growth exactly `½`** as
`|λ| → ∞` (DLMF §28.29(iii)): for every `ε > 0`,
`Δ(λ) = O(exp(|λ|^{1/2+ε}))`, and `Δ(λ)` is not `O(exp(|λ|^{1/2-ε}))`. Proved
from the energy bound `‖Δ(λ)‖ ≤ 2 e^{Mπ/2} e^{π |λ|^{1/2}}` and the lower bound
`Δ(-t) ≥ e^{π √(t - M)} / 2` on the negative axis. -/
@[dlmf 28.29.iii]
theorem hillDiscriminant_order_half {Q : ℝ → ℝ} (hQ : IsHillPotential (fun x => (Q x : ℂ)))
    {ε : ℝ} (hε : 0 < ε) :
    (hillDiscriminant (fun x => (Q x : ℂ)) =O[cocompact ℂ]
        fun lam => Real.exp (‖lam‖ ^ ((1 : ℝ) / 2 + ε))) ∧
      ¬ (hillDiscriminant (fun x => (Q x : ℂ)) =O[cocompact ℂ]
        fun lam => Real.exp (‖lam‖ ^ ((1 : ℝ) / 2 - ε))) := by
  have hQc : Continuous Q :=
    (Complex.continuous_re.comp hQ.continuous).congr fun x => by simp
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hQc.continuousOn (s := Icc 0 Real.pi))
  set M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hQM : ∀ x ∈ Icc 0 Real.pi, |Q x| ≤ M := fun x hx =>
    (Real.norm_eq_abs (Q x) ▸ hM₀ x hx).trans (le_max_left _ _)
  have hQM' : ∀ x ∈ Icc 0 Real.pi, ‖(Q x : ℂ)‖ ≤ M := fun x hx => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hQM x hx
  constructor
  · refine IsBigO.of_bound (2 * Real.exp (M * Real.pi / 2)) ?_
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop
      (max 1 (Real.pi ^ (1 / ε)))] with lam hlam
    have h1 : 1 ≤ ‖lam‖ := (le_max_left _ _).trans hlam
    have hr : 0 < ‖lam‖ := by linarith
    refine (p2s_hillDiscriminant_le (by fun_prop) hM hQM' h1).trans ?_
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    gcongr
    have hpi : Real.pi ≤ ‖lam‖ ^ ε := by
      calc Real.pi = (Real.pi ^ (1 / ε)) ^ ε := by
            rw [← Real.rpow_mul Real.pi_pos.le, one_div_mul_cancel hε.ne', Real.rpow_one]
        _ ≤ ‖lam‖ ^ ε := Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hlam)
            hε.le
    rw [Real.rpow_add hr, Real.sqrt_eq_rpow, mul_comm (‖lam‖ ^ ((1 : ℝ) / 2))]
    exact mul_le_mul_of_nonneg_right hpi (by positivity)
  · intro h
    obtain ⟨C, hC⟩ := h.bound
    have htend : Tendsto (fun t : ℝ => -(t : ℂ)) atTop (cocompact ℂ) := by
      rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
      refine tendsto_id.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with t ht
      simp [Complex.norm_real, abs_of_nonneg ht]
    set C' := max C 1
    have hev := (htend.eventually hC).and ((eventually_ge_atTop (max 1 (2 * M))).and
      (((tendsto_rpow_neg_atTop hε).eventually (gt_mem_nhds (by positivity :
        (0 : ℝ) < Real.pi / 4))).and ((Real.tendsto_sqrt_atTop.const_mul_atTop
          (by positivity : (0 : ℝ) < Real.pi / 4)).eventually_gt_atTop (Real.log (2 * C')))))
    obtain ⟨t, hCt, ht1, htε, hta⟩ := hev.exists
    have ht0 : 0 < t := by linarith [le_max_left 1 (2 * M)]
    have htM : 2 * M ≤ t := (le_max_right _ _).trans ht1
    have hnorm : ‖-(t : ℂ)‖ = t := by simp [Complex.norm_real, abs_of_pos ht0]
    rw [hnorm, Real.norm_of_nonneg (Real.exp_pos _).le] at hCt
    have hlow := p2s_hillDiscriminant_ge hQc hQM (show M ≤ t by linarith)
    set a := Real.pi / 4 * Real.sqrt t
    -- `π √(t - M) ≥ 2a`
    have h2a : 2 * a ≤ Real.pi * Real.sqrt (t - M) := by
      have : Real.sqrt t / 2 ≤ Real.sqrt (t - M) := by
        rw [show Real.sqrt t / 2 = Real.sqrt (t / 4) by
          rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by linarith)
      simp only [a]; nlinarith [Real.pi_pos]
    -- `t^{1/2-ε} ≤ a`
    have hexp : t ^ ((1 : ℝ) / 2 - ε) ≤ a := by
      rw [sub_eq_add_neg, Real.rpow_add ht0, ← Real.sqrt_eq_rpow, mul_comm]
      exact mul_le_mul_of_nonneg_right htε.le (Real.sqrt_nonneg _)
    have hea := Real.exp_pos a
    have hC0 : 0 ≤ C := by
      by_contra hc; push Not at hc
      have := mul_neg_of_neg_of_pos hc (Real.exp_pos (t ^ ((1 : ℝ) / 2 - ε)))
      linarith [norm_nonneg (hillDiscriminant (fun x => (Q x : ℂ)) (-(t : ℂ)))]
    have k1 : Real.exp (2 * a) / 2 ≤ C * Real.exp a := by
      have e1 : Real.exp (2 * a) ≤ Real.exp (Real.pi * Real.sqrt (t - M)) :=
        Real.exp_le_exp.mpr h2a
      have e2 : C * Real.exp (t ^ ((1 : ℝ) / 2 - ε)) ≤ C * Real.exp a :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC0
      linarith
    rw [show 2 * a = a + a by ring, Real.exp_add] at k1
    have k2 : Real.exp a ≤ 2 * C' := by
      have : Real.exp a * Real.exp a ≤ Real.exp a * (2 * C) := by linarith
      have := le_of_mul_le_mul_left this hea
      linarith [le_max_left C 1]
    have k3 := Real.exp_lt_exp.mpr hta
    rw [Real.exp_log (by positivity)] at k3
    linarith


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
