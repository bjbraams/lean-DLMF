/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Calculus.Defs
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Calculus of two or more variables (DLMF §1.5)

Partial derivatives are derivatives of sections, as in DLMF 1.5.3–1.5.4: for `f : ℝ × ℝ → ℝ`
we write `deriv (fun t => f (t, y)) x` for `∂f/∂x` at `(x, y)`, and on `Fin n → ℝ` we use
`partialDeriv` (`DLMF.AlgebraicAnalytic.Calculus.Defs`). The first part of the file connects
them with Fréchet derivatives (`partialDeriv_eq_fderiv`, `partialDeriv_partialDeriv`), which
gives the symmetry of mixed partials 1.5.6 and the chain rules 1.5.7–1.5.9.

The other items: the implicit function theorem (§1.5(i)), polar, cylindrical and spherical
coordinates and their Laplacians (1.5.10–1.5.17), Taylor's theorem and the second derivative
test (1.5.18–1.5.21), Leibniz's rule (1.5.22–1.5.24), double integrals over normal domains
and the change of order of integration (1.5.30–1.5.37), Jacobians (1.5.39, 1.5.41) and the
change of variables 1.5.42–1.5.43 with an exceptional null set. Riemann double integrals
(1.5.25–1.5.27), the extension by zero 1.5.28–1.5.29 and Fubini's theorem are Mathlib's
(`DLMF.AlgebraicAnalytic.Calculus.MathlibCoverage`).
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace DLMF.AlgebraicAnalytic

/-! ### Partial derivatives and Fréchet derivatives -/

/-- DLMF 1.5.3: at a point of differentiability the partial derivative `∂f/∂xᵢ` (derivative of
the section) is the Fréchet derivative applied to the `i`-th unit vector. -/
@[dlmf 1.5.E3]
theorem hasDerivAt_partialDeriv {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (Fin n → ℝ) → E} {x : Fin n → ℝ} (i : Fin n) (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun t => f (Function.update x i t)) (fderiv ℝ f x (Pi.single i 1)) (x i) := by
  have hu := hasDerivAt_update x i (x i)
  have hf' : DifferentiableAt ℝ f (Function.update x i (x i)) := by
    rwa [Function.update_eq_self]
  have := hf'.hasFDerivAt.comp_hasDerivAt (x i) hu
  simpa [Function.comp_def] using this

/-- DLMF 1.5.3: `∂f/∂xᵢ = Df(x) eᵢ` at a point of differentiability. -/
@[dlmf 1.5.E3]
theorem partialDeriv_eq_fderiv {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (Fin n → ℝ) → E} {x : Fin n → ℝ} (i : Fin n) (hf : DifferentiableAt ℝ f x) :
    partialDeriv i f x = fderiv ℝ f x (Pi.single i 1) :=
  (hasDerivAt_partialDeriv i hf).deriv

/-- If `f` is differentiable near `x`, then near `x` the function `partialDeriv j f` is
`y ↦ Df(y) eⱼ`. -/
theorem g1b_partialDeriv_eventuallyEq {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : (Fin n → ℝ) → E} {x : Fin n → ℝ} (j : Fin n)
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) :
    (fun y => partialDeriv j f y) =ᶠ[𝓝 x] fun y => fderiv ℝ f y (Pi.single j 1) := by
  filter_upwards [hf] with y hy using partialDeriv_eq_fderiv j hy

/-- Second partial derivatives of a `C²` function are second Fréchet derivatives:
`∂²f/∂xᵢ∂xⱼ = D²f(x) eᵢ eⱼ`. -/
theorem partialDeriv_partialDeriv {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : (Fin n → ℝ) → E} {x : Fin n → ℝ} (i j : Fin n)
    (hf : ContDiffAt ℝ 2 f x) :
    partialDeriv i (fun y => partialDeriv j f y) x =
      fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) := by
  have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hg : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x :=
    hd.clm_apply (differentiableAt_const _)
  have hsec : (fun t => partialDeriv j f (Function.update x i t)) =ᶠ[𝓝 (x i)]
      fun t => fderiv ℝ f (Function.update x i t) (Pi.single j 1) := by
    have hc : ContinuousAt (Function.update x i) (x i) :=
      (hasDerivAt_update x i (x i)).continuousAt
    have := (g1b_partialDeriv_eventuallyEq j hev)
    rw [← Function.update_eq_self i x] at this
    exact hc.eventually this
  change deriv (fun t => partialDeriv j f (Function.update x i t)) (x i) = _
  rw [hsec.deriv_eq]
  have := (hasDerivAt_partialDeriv (f := fun y => fderiv ℝ f y (Pi.single j 1)) i hg).deriv
  rw [this, fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- DLMF 1.5.6 (for `n` variables): for `f` of class `C²` at `x` the mixed partial derivatives
agree, `∂²f/∂xᵢ∂xⱼ = ∂²f/∂xⱼ∂xᵢ`. -/
@[dlmf 1.5.E6]
theorem partialDeriv_comm {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (Fin n → ℝ) → E} {x : Fin n → ℝ} (i j : Fin n) (hf : ContDiffAt ℝ 2 f x) :
    partialDeriv i (fun y => partialDeriv j f y) x =
      partialDeriv j (fun y => partialDeriv i f y) x := by
  rw [partialDeriv_partialDeriv i j hf, partialDeriv_partialDeriv j i hf]
  exact hf.isSymmSndFDerivAt (by simp) _ _

/-! ### §1.5(i) Continuity and partial derivatives in two variables -/

/-- DLMF 1.5.1–1.5.2: `f(x, y)` is continuous at `(a, b)` iff for every `ε > 0` there is
`δ > 0` with `|f(a + α, b + β) - f(a, b)| < ε` whenever `|α|, |β| < δ`. -/
@[dlmf 1.5.E1, dlmf 1.5.E2]
theorem continuousAt_prod_iff_eps_delta {f : ℝ × ℝ → ℝ} {a b : ℝ} :
    ContinuousAt f (a, b) ↔ ∀ ε > 0, ∃ δ > 0, ∀ α β : ℝ, |α| < δ → |β| < δ →
      |f (a + α, b + β) - f (a, b)| < ε := by
  rw [Metric.continuousAt_iff]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    refine ⟨δ, hδ, fun α β hα hβ => ?_⟩
    have := h (x := (a + α, b + β)) (by simp [Prod.dist_eq, hα, hβ])
    simpa [Real.dist_eq] using this
  · intro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    refine ⟨δ, hδ, fun {q} hq => ?_⟩
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hq
    have := h (q.1 - a) (q.2 - b) hq.1 hq.2
    simpa [Real.dist_eq] using this

/-- DLMF 1.5.3: at a point of differentiability of `f(x, y)` the section `t ↦ f(t, y)` has
derivative `∂f/∂x = Df(x, y)(1, 0)`. -/
@[dlmf 1.5.E3]
theorem hasDerivAt_section_fst {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p) :
    HasDerivAt (fun t => f (t, p.2)) (fderiv ℝ f p (1, 0)) p.1 := by
  have h := (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have := hf.hasFDerivAt.comp_hasDerivAt (x := p.1) (by simpa using h)
  simpa [Function.comp_def] using this

/-- DLMF 1.5.4: at a point of differentiability of `f(x, y)` the section `t ↦ f(x, t)` has
derivative `∂f/∂y = Df(x, y)(0, 1)`. -/
@[dlmf 1.5.E4]
theorem hasDerivAt_section_snd {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p) :
    HasDerivAt (fun t => f (p.1, t)) (fderiv ℝ f p (0, 1)) p.2 := by
  have h := (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have := hf.hasFDerivAt.comp_hasDerivAt (x := p.2) (by simpa using h)
  simpa [Function.comp_def] using this

/-- DLMF 1.5.5–1.5.6: for `f(x, y)` of class `C²` at `p` the mixed partial derivatives agree,
`∂/∂y (∂f/∂x) = ∂/∂x (∂f/∂y)`. -/
@[dlmf 1.5.E5, dlmf 1.5.E6]
theorem deriv_section_comm {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : ContDiffAt ℝ 2 f p) :
    deriv (fun s => deriv (fun t => f (t, s)) p.1) p.2 =
      deriv (fun t => deriv (fun s => f (t, s)) p.2) p.1 := by
  have hev : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ f q :=
    (hf.eventually (by simp)).mono fun q hq => hq.differentiableAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have h1 : (fun s => deriv (fun t => f (t, s)) p.1) =ᶠ[𝓝 p.2]
      fun s => fderiv ℝ f (p.1, s) (1, 0) := by
    have hc : ContinuousAt (fun s : ℝ => (p.1, s)) p.2 := by fun_prop
    have := hc.eventually (by simpa using hev)
    filter_upwards [this] with s hs using (hasDerivAt_section_fst (p := (p.1, s)) hs).deriv
  have h2 : (fun t => deriv (fun s => f (t, s)) p.2) =ᶠ[𝓝 p.1]
      fun t => fderiv ℝ f (t, p.2) (0, 1) := by
    have hc : ContinuousAt (fun t : ℝ => (t, p.2)) p.1 := by fun_prop
    have := hc.eventually (by simpa using hev)
    filter_upwards [this] with t ht using (hasDerivAt_section_snd (p := (t, p.2)) ht).deriv
  rw [h1.deriv_eq, h2.deriv_eq]
  have g1 := hasDerivAt_section_snd (f := fun q => fderiv ℝ f q (1, 0)) (p := p)
    (hd.clm_apply (differentiableAt_const _))
  have g2 := hasDerivAt_section_fst (f := fun q => fderiv ℝ f q (0, 1)) (p := p)
    (hd.clm_apply (differentiableAt_const _))
  rw [g1.deriv, g2.deriv, fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using hf.isSymmSndFDerivAt (by simp) (0, 1) (1, 0)

/-- DLMF 1.5.7 (chain rule): `d/dt f(x(t), y(t)) = f_x x'(t) + f_y y'(t)`, the partial
derivatives taken at `(x(t), y(t))`. -/
@[dlmf 1.5.E7]
theorem hasDerivAt_comp_prod {f : ℝ × ℝ → ℝ} {x y : ℝ → ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f (x t, y t)) (hx : DifferentiableAt ℝ x t)
    (hy : DifferentiableAt ℝ y t) :
    HasDerivAt (fun s => f (x s, y s))
      (deriv (fun u => f (u, y t)) (x t) * deriv x t +
        deriv (fun v => f (x t, v)) (y t) * deriv y t) t := by
  have h := hf.hasFDerivAt.comp_hasDerivAt t (hx.hasDerivAt.prodMk hy.hasDerivAt)
  rw [(hasDerivAt_section_fst (p := (x t, y t)) hf).deriv,
    (hasDerivAt_section_snd (p := (x t, y t)) hf).deriv]
  have : (deriv x t, deriv y t) =
      deriv x t • ((1 : ℝ), (0 : ℝ)) + deriv y t • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
  exact h.congr_deriv (by ring)

/-- DLMF 1.5.8 (chain rule): `∂/∂u f(x(u, v), y(u, v)) = f_x ∂x/∂u + f_y ∂y/∂u`. -/
@[dlmf 1.5.E8]
theorem deriv_comp_prod_section {f : ℝ × ℝ → ℝ} {x y : ℝ × ℝ → ℝ} {u v : ℝ}
    (hf : DifferentiableAt ℝ f (x (u, v), y (u, v)))
    (hx : DifferentiableAt ℝ (fun u => x (u, v)) u)
    (hy : DifferentiableAt ℝ (fun u => y (u, v)) u) :
    deriv (fun u => f (x (u, v), y (u, v))) u =
      deriv (fun s => f (s, y (u, v))) (x (u, v)) * deriv (fun u => x (u, v)) u +
        deriv (fun s => f (x (u, v), s)) (y (u, v)) * deriv (fun u => y (u, v)) u :=
  (hasDerivAt_comp_prod (x := fun u => x (u, v)) (y := fun u => y (u, v)) hf hx hy).deriv

/-- DLMF 1.5.9 (chain rule in `n` variables, stated for paths): for `f` differentiable at
`c(t)`, `d/dt f(c(t)) = ∑ᵢ ∂f/∂xᵢ (c(t)) cᵢ'(t)`; for `n = 3` and `c(v) = (x, y, z)(u, v)` this
is 1.5.9. -/
@[dlmf 1.5.E9]
theorem hasDerivAt_comp_pi {n : ℕ} {f : (Fin n → ℝ) → ℝ} {c : ℝ → Fin n → ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f (c t)) (hc : DifferentiableAt ℝ c t) :
    HasDerivAt (fun s => f (c s))
      (∑ i, partialDeriv i f (c t) * deriv (fun s => c s i) t) t := by
  have h := hf.hasFDerivAt.comp_hasDerivAt t hc.hasDerivAt
  have hsum : deriv c t = ∑ i, deriv (fun s => c s i) t • (Pi.single i 1 : Fin n → ℝ) := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact ((hasDerivAt_pi.mp hc.hasDerivAt) j).deriv.symm
  rw [hsum, map_sum] at h
  refine h.congr_deriv (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_smul, smul_eq_mul, partialDeriv_eq_fderiv i hf, mul_comm]

/-- DLMF §1.5(i) (implicit function theorem): if `F(x, y)` is continuously differentiable near
`(a, b)`, `F(a, b) = 0` and `∂F/∂y ≠ 0` at `(a, b)`, then near `(a, b)` the equation `F = 0`
defines a continuously differentiable `y = g(x)` with `F(x, g(x)) = 0`, `g(a) = b` and
`g'(x) = -F_x/F_y` at `(x, g(x))`; every zero of `F` near `(a, b)` lies on the graph of `g`. -/
@[dlmf 1.5.i]
theorem exists_implicitFunction {F : ℝ × ℝ → ℝ} {a b : ℝ} (hF : ContDiffAt ℝ 1 F (a, b))
    (h0 : F (a, b) = 0) (hy : deriv (fun t => F (a, t)) b ≠ 0) :
    ∃ g : ℝ → ℝ, g a = b ∧ ContDiffAt ℝ 1 g a ∧ (∀ᶠ x in 𝓝 a, F (x, g x) = 0) ∧
      (∀ᶠ x in 𝓝 a, HasDerivAt g
        (-(deriv (fun t => F (t, g x)) x) / deriv (fun t => F (x, t)) (g x)) x) ∧
      ∀ᶠ q in 𝓝 (a, b), F q = 0 → q.2 = g q.1 := by
  sorry

/-! ### §1.5(ii) Coordinate systems -/

/-- DLMF 1.5.11–1.5.12: in polar coordinates `x = r cos φ`, `y = r sin φ` (1.5.10), with
`F(r, φ) = f(r cos φ, r sin φ)` and `r ≠ 0`,
`∂f/∂x = cos φ ∂F/∂r - (sin φ / r) ∂F/∂φ` and `∂f/∂y = sin φ ∂F/∂r + (cos φ / r) ∂F/∂φ`. -/
@[dlmf 1.5.E11, dlmf 1.5.E12]
theorem partialDeriv_polar {f : ℝ × ℝ → ℝ} {r φ : ℝ} (hr : r ≠ 0)
    (hf : DifferentiableAt ℝ f (r * Real.cos φ, r * Real.sin φ)) :
    let F : ℝ × ℝ → ℝ := fun q => f (q.1 * Real.cos q.2, q.1 * Real.sin q.2)
    deriv (fun t => f (t, r * Real.sin φ)) (r * Real.cos φ) =
        Real.cos φ * deriv (fun t => F (t, φ)) r -
          Real.sin φ / r * deriv (fun t => F (r, t)) φ ∧
      deriv (fun t => f (r * Real.cos φ, t)) (r * Real.sin φ) =
        Real.sin φ * deriv (fun t => F (t, φ)) r +
          Real.cos φ / r * deriv (fun t => F (r, t)) φ := by
  intro F
  have hr' : deriv (fun t => F (t, φ)) r =
      deriv (fun u => f (u, r * Real.sin φ)) (r * Real.cos φ) * Real.cos φ +
        deriv (fun v => f (r * Real.cos φ, v)) (r * Real.sin φ) * Real.sin φ := by
    have := hasDerivAt_comp_prod (x := fun t => t * Real.cos φ) (y := fun t => t * Real.sin φ)
      (t := r) hf (by fun_prop) (by fun_prop)
    simp only [F]
    rw [this.deriv]
    simp
  have hφ : deriv (fun t => F (r, t)) φ =
      deriv (fun u => f (u, r * Real.sin φ)) (r * Real.cos φ) * (-(r * Real.sin φ)) +
        deriv (fun v => f (r * Real.cos φ, v)) (r * Real.sin φ) * (r * Real.cos φ) := by
    have := hasDerivAt_comp_prod (x := fun t => r * Real.cos t) (y := fun t => r * Real.sin t)
      (t := φ) hf (by fun_prop) (by fun_prop)
    simp only [F]
    rw [this.deriv]
    simp [mul_comm]
  rw [hr', hφ]
  have hcs := Real.sin_sq_add_cos_sq φ
  set A := deriv (fun u => f (u, r * Real.sin φ)) (r * Real.cos φ)
  set B := deriv (fun v => f (r * Real.cos φ, v)) (r * Real.sin φ)
  have e1 : Real.sin φ / r * (A * -(r * Real.sin φ) + B * (r * Real.cos φ)) =
      -A * Real.sin φ ^ 2 + B * Real.sin φ * Real.cos φ := by
    field_simp
  have e2 : Real.cos φ / r * (A * -(r * Real.sin φ) + B * (r * Real.cos φ)) =
      -A * Real.sin φ * Real.cos φ + B * Real.cos φ ^ 2 := by
    field_simp
  constructor
  · rw [e1]
    linear_combination (-A) * hcs
  · rw [e2]
    linear_combination (-B) * hcs

/-- DLMF 1.5.13: the Laplacian in polar coordinates. For `f` of class `C²` at
`(r cos φ, r sin φ)`, `r ≠ 0`, and `F(r, φ) = f(r cos φ, r sin φ)`:
`f_xx + f_yy = F_rr + F_r / r + F_φφ / r²`. -/
@[dlmf 1.5.E13]
theorem laplacian_polar {f : ℝ × ℝ → ℝ} {r φ : ℝ} (hr : r ≠ 0)
    (hf : ContDiffAt ℝ 2 f (r * Real.cos φ, r * Real.sin φ)) :
    let F : ℝ × ℝ → ℝ := fun q => f (q.1 * Real.cos q.2, q.1 * Real.sin q.2)
    deriv (fun t => deriv (fun s => f (s, r * Real.sin φ)) t) (r * Real.cos φ) +
        deriv (fun t => deriv (fun s => f (r * Real.cos φ, s)) t) (r * Real.sin φ) =
      deriv (fun t => deriv (fun s => F (s, φ)) t) r +
        deriv (fun t => F (t, φ)) r / r +
        deriv (fun t => deriv (fun s => F (r, s)) t) φ / r ^ 2 := by
  sorry

/-- DLMF 1.5.15: the Laplacian in cylindrical coordinates (1.5.14). For `f` of class `C²` at
`x = (r cos φ, r sin φ, z)` with `r ≠ 0` and `F = f ∘ cylindricalCoord`:
`∇²f = F_rr + F_r / r + F_φφ / r² + F_zz`. -/
@[dlmf 1.5.E15]
theorem laplacian_cylindrical {f : (Fin 3 → ℝ) → ℝ} {q : Fin 3 → ℝ} (hr : q 0 ≠ 0)
    (hf : ContDiffAt ℝ 2 f (cylindricalCoord q)) :
    laplacian f (cylindricalCoord q) =
      partialDeriv 0 (fun y => partialDeriv 0 (f ∘ cylindricalCoord) y) q +
        partialDeriv 0 (f ∘ cylindricalCoord) q / q 0 +
        partialDeriv 1 (fun y => partialDeriv 1 (f ∘ cylindricalCoord) y) q / q 0 ^ 2 +
        partialDeriv 2 (fun y => partialDeriv 2 (f ∘ cylindricalCoord) y) q := by
  sorry

/-- DLMF 1.5.17: the Laplacian in spherical coordinates (1.5.16). For `f` of class `C²` at
`x = sphericalCoord (ρ, θ, φ)` with `ρ ≠ 0`, `sin θ ≠ 0` and `F = f ∘ sphericalCoord`:
`∇²f = ρ⁻² ∂_ρ(ρ² F_ρ) + (ρ² sin² θ)⁻¹ F_φφ + (ρ² sin θ)⁻¹ ∂_θ(sin θ F_θ)`. -/
@[dlmf 1.5.E17]
theorem laplacian_spherical {f : (Fin 3 → ℝ) → ℝ} {q : Fin 3 → ℝ} (hρ : q 0 ≠ 0)
    (hθ : Real.sin (q 1) ≠ 0) (hf : ContDiffAt ℝ 2 f (sphericalCoord q)) :
    laplacian f (sphericalCoord q) =
      partialDeriv 0 (fun y => y 0 ^ 2 * partialDeriv 0 (f ∘ sphericalCoord) y) q / q 0 ^ 2 +
        partialDeriv 2 (fun y => partialDeriv 2 (f ∘ sphericalCoord) y) q /
          (q 0 ^ 2 * Real.sin (q 1) ^ 2) +
        partialDeriv 1 (fun y => Real.sin (y 1) * partialDeriv 1 (f ∘ sphericalCoord) y) q /
          (q 0 ^ 2 * Real.sin (q 1)) := by
  sorry

/-! ### §1.5(iii) Taylor's theorem; maxima and minima -/

/-- DLMF 1.5.18 (Taylor's theorem in two variables, Peano remainder): for `f` of class `Cⁿ⁺¹`
at `(a, b)`, `f(a + λ, b + μ) = ∑_{k ≤ n} (1/k!) (λ ∂_x + μ ∂_y)ᵏ f(a, b) + Rₙ` with
`Rₙ / (λ² + μ²)^{n/2} → 0`. The operator power `(λ∂_x + μ∂_y)ᵏ f` is the `k`-th Fréchet
derivative applied to `(λ, μ)` in each slot. -/
@[dlmf 1.5.E18]
theorem taylor_isLittleO_prod {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (n : ℕ)
    (hf : ContDiffAt ℝ (n + 1) f p) :
    (fun h : ℝ × ℝ => f (p + h) -
        ∑ k ∈ Finset.range (n + 1),
          (1 / (Nat.factorial k : ℝ)) * iteratedFDeriv ℝ k f p (fun _ => h))
      =o[𝓝 0] fun h => Real.sqrt (h.1 ^ 2 + h.2 ^ 2) ^ n := by
  sorry

/-- DLMF 1.5.19–1.5.21 (second derivative test, minimum): if `f` is `C²` at `(a, b)`,
`f_x = f_y = 0`, `f_xx > 0` and `f_xx f_yy - f_xy² > 0` at `(a, b)`, then `f` has a local
minimum at `(a, b)`. -/
@[dlmf 1.5.E19, dlmf 1.5.E20, dlmf 1.5.E21]
theorem isLocalMin_of_hessian_posDef {f : ℝ × ℝ → ℝ} {a b : ℝ} (hf : ContDiffAt ℝ 2 f (a, b))
    (hx : deriv (fun t => f (t, b)) a = 0) (hy : deriv (fun t => f (a, t)) b = 0)
    (hxx : 0 < deriv (fun s => deriv (fun t => f (t, b)) s) a)
    (hdet : 0 < deriv (fun s => deriv (fun t => f (t, b)) s) a *
        deriv (fun s => deriv (fun t => f (a, t)) s) b -
          deriv (fun s => deriv (fun t => f (t, s)) a) b ^ 2) :
    IsLocalMin f (a, b) := by
  sorry

/-- DLMF 1.5.19–1.5.21 (second derivative test, maximum): as
`isLocalMin_of_hessian_posDef` with `f_xx < 0`; then `f` has a local maximum at `(a, b)`. -/
@[dlmf 1.5.E19, dlmf 1.5.E20, dlmf 1.5.E21]
theorem isLocalMax_of_hessian_negDef {f : ℝ × ℝ → ℝ} {a b : ℝ} (hf : ContDiffAt ℝ 2 f (a, b))
    (hx : deriv (fun t => f (t, b)) a = 0) (hy : deriv (fun t => f (a, t)) b = 0)
    (hxx : deriv (fun s => deriv (fun t => f (t, b)) s) a < 0)
    (hdet : 0 < deriv (fun s => deriv (fun t => f (t, b)) s) a *
        deriv (fun s => deriv (fun t => f (a, t)) s) b -
          deriv (fun s => deriv (fun t => f (t, s)) a) b ^ 2) :
    IsLocalMax f (a, b) := by
  sorry

/-! ### §1.5(iv) Leibniz's theorem for differentiation of integrals -/

/-- DLMF 1.5.22 (Leibniz's rule with variable limits): if `f` and `∂f/∂x` are continuous on
`[a, b] × [c, d]` and `α`, `β` are continuously differentiable on `[a, b]` with values in
`[c, d]`, then for `x ∈ (a, b)`
`d/dx ∫_{α(x)}^{β(x)} f(x, y) dy = f(x, β(x)) β'(x) - f(x, α(x)) α'(x) + ∫_{α(x)}^{β(x)} f_x dy`.
-/
@[dlmf 1.5.E22]
theorem hasDerivAt_integral_variable_limits {f : ℝ × ℝ → ℝ} {α β : ℝ → ℝ} {a b c d : ℝ}
    (hf : ContinuousOn f (Icc a b ×ˢ Icc c d))
    (hfx : ContinuousOn (fun q => deriv (fun t => f (t, q.2)) q.1) (Icc a b ×ˢ Icc c d))
    (hα : ContDiffOn ℝ 1 α (Icc a b)) (hβ : ContDiffOn ℝ 1 β (Icc a b))
    (hαI : ∀ x ∈ Icc a b, α x ∈ Icc c d) (hβI : ∀ x ∈ Icc a b, β x ∈ Icc c d)
    {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (fun x => ∫ y in α x..β x, f (x, y))
      (f (x, β x) * deriv β x - f (x, α x) * deriv α x +
        ∫ y in α x..β x, deriv (fun t => f (t, y)) x) x := by
  sorry

/-- DLMF 1.5.23–1.5.24 (Leibniz's rule for infinite integrals, `d = +∞`): suppose `f` and
`∂f/∂x` are continuous on `[a, b] × [c, ∞)`, `∫_c^∞ f(x, y) dy` converges to `I(x)` for
`x ∈ [a, b]`, and `∫_c^∞ ∂f/∂x dy` converges to `J(x)` uniformly on `[a, b]` (1.5.23, stated
as uniform convergence of `∫_c^R` as `R → ∞`, which is equivalent to the uniform smallness of
the tails). Then `I' = J` on `(a, b)`. -/
@[dlmf 1.5.E23, dlmf 1.5.E24]
theorem hasDerivAt_improper_integral_of_tendstoUniformlyOn {f : ℝ × ℝ → ℝ} {I J : ℝ → ℝ}
    {a b c : ℝ} (hf : ContinuousOn f (Icc a b ×ˢ Ici c))
    (hfx : ContinuousOn (fun q => deriv (fun t => f (t, q.2)) q.1) (Icc a b ×ˢ Ici c))
    (hI : ∀ x ∈ Icc a b, Tendsto (fun R => ∫ y in c..R, f (x, y)) atTop (𝓝 (I x)))
    (hJ : TendstoUniformlyOn (fun R x => ∫ y in c..R, deriv (fun t => f (t, y)) x) J atTop
      (Icc a b))
    {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt I (J x) x := by
  sorry

/-! ### §1.5(v) Multiple integrals -/

/-- DLMF 1.5.30–1.5.32: for `f` continuous on `D = {a ≤ x ≤ b, φ₁(x) ≤ y ≤ φ₂(x)}` with
`φ₁ ≤ φ₂` continuous, `∬_D f dA = ∫ₐᵇ (∫_{φ₁(x)}^{φ₂(x)} f(x, y) dy) dx`. -/
@[dlmf 1.5.E30, dlmf 1.5.E31, dlmf 1.5.E32]
theorem setIntegral_normalDomain_fst {f : ℝ × ℝ → ℝ} {φ₁ φ₂ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hφ₁ : ContinuousOn φ₁ (Icc a b)) (hφ₂ : ContinuousOn φ₂ (Icc a b))
    (hφ : ∀ x ∈ Icc a b, φ₁ x ≤ φ₂ x)
    (hf : ContinuousOn f {q | q.1 ∈ Icc a b ∧ q.2 ∈ Icc (φ₁ q.1) (φ₂ q.1)}) :
    ∫ q in {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ q.2 ∈ Icc (φ₁ q.1) (φ₂ q.1)}, f q =
      ∫ x in a..b, ∫ y in φ₁ x..φ₂ x, f (x, y) := by
  sorry

/-- DLMF 1.5.33–1.5.34: for `f` continuous on `D = {c ≤ y ≤ d, ψ₁(y) ≤ x ≤ ψ₂(y)}` with
`ψ₁ ≤ ψ₂` continuous, `∬_D f dA = ∫_c^d (∫_{ψ₁(y)}^{ψ₂(y)} f(x, y) dx) dy`. -/
@[dlmf 1.5.E33, dlmf 1.5.E34]
theorem setIntegral_normalDomain_snd {f : ℝ × ℝ → ℝ} {ψ₁ ψ₂ : ℝ → ℝ} {c d : ℝ} (hcd : c ≤ d)
    (hψ₁ : ContinuousOn ψ₁ (Icc c d)) (hψ₂ : ContinuousOn ψ₂ (Icc c d))
    (hψ : ∀ y ∈ Icc c d, ψ₁ y ≤ ψ₂ y)
    (hf : ContinuousOn f {q | q.2 ∈ Icc c d ∧ q.1 ∈ Icc (ψ₁ q.2) (ψ₂ q.2)}) :
    ∫ q in {q : ℝ × ℝ | q.2 ∈ Icc c d ∧ q.1 ∈ Icc (ψ₁ q.2) (ψ₂ q.2)}, f q =
      ∫ y in c..d, ∫ x in ψ₁ y..ψ₂ y, f (x, y) := by
  sorry

/-- DLMF 1.5.35 (change of order of integration): if the domain `D` has both forms 1.5.30 and
1.5.33 and `f` is continuous on `D`, the two repeated integrals agree. -/
@[dlmf 1.5.E35]
theorem integral_normalDomain_swap {f : ℝ × ℝ → ℝ} {φ₁ φ₂ ψ₁ ψ₂ : ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hφ₁ : ContinuousOn φ₁ (Icc a b)) (hφ₂ : ContinuousOn φ₂ (Icc a b))
    (hφ : ∀ x ∈ Icc a b, φ₁ x ≤ φ₂ x)
    (hψ₁ : ContinuousOn ψ₁ (Icc c d)) (hψ₂ : ContinuousOn ψ₂ (Icc c d))
    (hψ : ∀ y ∈ Icc c d, ψ₁ y ≤ ψ₂ y)
    (hD : {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ q.2 ∈ Icc (φ₁ q.1) (φ₂ q.1)} =
      {q | q.2 ∈ Icc c d ∧ q.1 ∈ Icc (ψ₁ q.2) (ψ₂ q.2)})
    (hf : ContinuousOn f {q | q.1 ∈ Icc a b ∧ q.2 ∈ Icc (φ₁ q.1) (φ₂ q.1)}) :
    ∫ x in a..b, ∫ y in φ₁ x..φ₂ x, f (x, y) = ∫ y in c..d, ∫ x in ψ₁ y..ψ₂ y, f (x, y) := by
  rw [← setIntegral_normalDomain_fst hab hφ₁ hφ₂ hφ hf, hD]
  rw [hD] at hf
  exact setIntegral_normalDomain_snd hcd hψ₁ hψ₂ hψ hf

/-- DLMF 1.5.36 (infinite double integrals): if `f` is (almost everywhere strongly)
measurable on `s × t` (for example piecewise continuous on `(a, b) × (c, d)`), its repeated
integral `∫_s (∫_t |f|)` is absolutely convergent and the inner integrals `∫_t f(x, ·)` exist
for almost every `x ∈ s`, then the two repeated integrals agree. The sets `s`, `t` may be
unbounded intervals. -/
@[dlmf 1.5.E36]
theorem integral_integral_swap_of_abs {f : ℝ × ℝ → ℝ} {s t : Set ℝ}
    (hm : AEStronglyMeasurable f ((volume.restrict s).prod (volume.restrict t)))
    (hin : ∀ᵐ x ∂(volume.restrict s), IntegrableOn (fun y => f (x, y)) t)
    (habs : IntegrableOn (fun x => ∫ y in t, |f (x, y)|) s) :
    ∫ x in s, ∫ y in t, f (x, y) = ∫ y in t, ∫ x in s, f (x, y) := by
  have hI : Integrable f ((volume.restrict s).prod (volume.restrict t)) := by
    rw [integrable_prod_iff hm]
    refine ⟨hin, ?_⟩
    simp only [Real.norm_eq_abs]
    exact habs
  exact integral_integral_swap (f := Function.curry f) (by rwa [Function.uncurry_curry])

/-- DLMF 1.5.37: triple integrals over `{a ≤ x ≤ b, φ₁(x) ≤ y ≤ φ₂(x), ψ₁(x, y) ≤ z ≤ ψ₂(x, y)}`
are repeated integrals, for `f` continuous on the region and continuous bounds. -/
@[dlmf 1.5.E37]
theorem setIntegral_normalDomain_three {f : ℝ × ℝ × ℝ → ℝ} {φ₁ φ₂ : ℝ → ℝ}
    {ψ₁ ψ₂ : ℝ × ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hφ₁ : ContinuousOn φ₁ (Icc a b)) (hφ₂ : ContinuousOn φ₂ (Icc a b))
    (hφ : ∀ x ∈ Icc a b, φ₁ x ≤ φ₂ x)
    (hψ₁ : ContinuousOn ψ₁ {p | p.1 ∈ Icc a b ∧ p.2 ∈ Icc (φ₁ p.1) (φ₂ p.1)})
    (hψ₂ : ContinuousOn ψ₂ {p | p.1 ∈ Icc a b ∧ p.2 ∈ Icc (φ₁ p.1) (φ₂ p.1)})
    (hψ : ∀ p ∈ {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc (φ₁ p.1) (φ₂ p.1)}, ψ₁ p ≤ ψ₂ p)
    (hf : ContinuousOn f {q | q.1 ∈ Icc a b ∧ q.2.1 ∈ Icc (φ₁ q.1) (φ₂ q.1) ∧
      q.2.2 ∈ Icc (ψ₁ (q.1, q.2.1)) (ψ₂ (q.1, q.2.1))}) :
    ∫ q in {q : ℝ × ℝ × ℝ | q.1 ∈ Icc a b ∧ q.2.1 ∈ Icc (φ₁ q.1) (φ₂ q.1) ∧
        q.2.2 ∈ Icc (ψ₁ (q.1, q.2.1)) (ψ₂ (q.1, q.2.1))}, f q =
      ∫ x in a..b, ∫ y in φ₁ x..φ₂ x, ∫ z in ψ₁ (x, y)..ψ₂ (x, y), f (x, y, z) := by
  sorry

/-! ### §1.5(vi) Jacobians and change of variables -/

/-- DLMF 1.5.39: the Jacobian of polar coordinates is `∂(x, y)/∂(r, φ) = r`. -/
@[dlmf 1.5.E39]
theorem jacobianDet2_polar (r φ : ℝ) :
    jacobianDet2 (fun q => q.1 * Real.cos q.2) (fun q => q.1 * Real.sin q.2) (r, φ) = r := by
  simp [jacobianDet2, Matrix.det_fin_two]
  linear_combination r * Real.sin_sq_add_cos_sq φ

/-- DLMF 1.5.41: the Jacobian of spherical coordinates is
`∂(x, y, z)/∂(ρ, θ, φ) = ρ² sin θ`. -/
@[dlmf 1.5.E41]
theorem jacobianDet3_spherical (q : Fin 3 → ℝ) :
    jacobianDet3 (fun y => sphericalCoord y 0) (fun y => sphericalCoord y 1)
      (fun y => sphericalCoord y 2) q = q 0 ^ 2 * Real.sin (q 1) := by
  simp [jacobianDet3, sphericalCoord, partialDeriv, Matrix.det_fin_three, Function.update_apply]
  linear_combination q 0 ^ 2 * Real.sin (q 1) *
    ((Real.sin (q 2) ^ 2 + Real.cos (q 2) ^ 2) * Real.sin_sq_add_cos_sq (q 1) +
      Real.sin_sq_add_cos_sq (q 2))

/-- DLMF 1.5.42–1.5.43 (change of variables): if `Φ` is differentiable on the measurable set
`D*` with derivative `Φ'` and one-to-one on `D*` except on a null set `N`, then
`∫_{Φ(D*)} g = ∫_{D*} g(Φ(u)) |det Φ'(u)| du`. Stated for any finite-dimensional real space
with an additive Haar measure (`ℝ²`, `ℝ³`); `det Φ'` is the Jacobian of 1.5.38 and 1.5.40. -/
@[dlmf 1.5.E42, dlmf 1.5.E43]
theorem integral_image_eq_integral_abs_det_of_injOn_diff_null {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {Φ : E → E} {Φ' : E → E →L[ℝ] E}
    {D N : Set E} (hD : MeasurableSet D) (hN : μ N = 0)
    (hΦ' : ∀ x ∈ D, HasFDerivWithinAt Φ (Φ' x) D x) (hinj : InjOn Φ (D \ N)) (g : E → ℝ) :
    ∫ x in Φ '' D, g x ∂μ = ∫ x in D, |(Φ' x).det| * g (Φ x) ∂μ := by
  obtain ⟨T, hNT, hTm, hT0⟩ := exists_measurable_superset_of_null hN
  have hDT : MeasurableSet (D \ T) := hD.diff hTm
  have hinj' : InjOn Φ (D \ T) := hinj.mono (sdiff_subset_sdiff_right hNT)
  have hΦ'' : ∀ x ∈ D \ T, HasFDerivWithinAt Φ (Φ' x) (D \ T) x :=
    fun x hx => (hΦ' x hx.1).mono sdiff_subset
  have h1 := integral_image_eq_integral_abs_det_fderiv_smul μ hDT hΦ'' hinj' g
  have himg0 : μ (Φ '' (D ∩ T)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ
      (fun x hx => (hΦ' x hx.1).differentiableWithinAt.mono inter_subset_left)
      (measure_mono_null inter_subset_right hT0)
  have hset : Φ '' D = Φ '' (D \ T) ∪ Φ '' (D ∩ T) := by rw [← image_union, sdiff_union_inter]
  rw [hset, setIntegral_congr_set (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr himg0)), h1,
    setIntegral_congr_set (sdiff_null_ae_eq_self hT0)]
  simp [smul_eq_mul]

end DLMF.AlgebraicAnalytic
