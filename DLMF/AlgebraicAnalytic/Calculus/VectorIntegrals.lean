/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Calculus.Vectors
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Path, line and surface integrals; Gauss's theorem (DLMF §1.6(iv)–(v))

Paths are `c : ℝ → ℝ³`, surfaces are parametrized by `Φ : ℝ × ℝ → ℝ³` on a parameter set
`D ⊆ ℝ²` (definitions in `DLMF.AlgebraicAnalytic.Calculus.Defs`). This file has:

* reparametrization invariance of line and path integrals (1.6.39–1.6.41) and the gradient
  theorem 1.6.42;
* the normal `T_u × T_v`, the area element 1.6.49 in terms of Jacobians, the sphere 1.6.50,
  graphs 1.6.51 and surfaces of revolution 1.6.52–1.6.53;
* invariance of surface area and flux under reparametrization (§1.6(v), 1.6.56);
* Gauss's divergence theorem 1.6.58 for a compact `V` whose boundary is covered by finitely
  many smooth parametrized patches with outward normals, and Green's identities 1.6.59–1.6.60
  derived from it.

Green's theorem in the plane (1.6.43–1.6.44) and Stokes's theorem (1.6.57) are in
`DLMF.AlgebraicAnalytic.Calculus.GreenStokes`, which uses TauCeti's winding-number form of
Green's theorem.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology Matrix

namespace DLMF.AlgebraicAnalytic

/-! ### §1.6(iv) Path and line integrals -/

/-- `vecNorm (r • v) = |r| vecNorm v`. -/
lemma g1b_vecNorm_smul (r : ℝ) (v : Fin 3 → ℝ) : vecNorm (r • v) = |r| * vecNorm v := by
  rw [vecNorm, vecNorm, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    Real.sqrt_mul (mul_self_nonneg r), Real.sqrt_mul_self_eq_abs]

/-- The derivative of a reparametrized `C¹` path: `(c ∘ h)' = h' c' ∘ h`. -/
lemma g1b_deriv_comp_path {c : ℝ → Fin 3 → ℝ} {h : ℝ → ℝ} (hc : ContDiff ℝ 1 c)
    (hh : ContDiff ℝ 1 h) (t : ℝ) : deriv (c ∘ h) t = deriv h t • deriv c (h t) :=
  ((hc.differentiable one_ne_zero (h t)).hasDerivAt.scomp t
    (hh.differentiable one_ne_zero t).hasDerivAt).deriv

lemma g1b_continuous_dot {F : (Fin 3 → ℝ) → Fin 3 → ℝ} {c : ℝ → Fin 3 → ℝ}
    (hF : Continuous F) (hc : ContDiff ℝ 1 c) :
    Continuous fun s => F (c s) ⬝ᵥ deriv c s := by
  have h1 : Continuous fun s => F (c s) := hF.comp hc.continuous
  have h2 : Continuous (deriv c) := hc.continuous_deriv le_rfl
  simp only [dotProduct]
  fun_prop

/-- DLMF 1.6.39: line integrals are invariant under a `C¹` reparametrization
`t' = h(t)` with `h(a) = a'`, `h(b) = b'`; monotonicity of `h` is not needed. -/
@[dlmf 1.6.E39]
theorem lineIntegral_comp {F : (Fin 3 → ℝ) → Fin 3 → ℝ} {c : ℝ → Fin 3 → ℝ} {h : ℝ → ℝ}
    (hF : Continuous F) (hc : ContDiff ℝ 1 c) (hh : ContDiff ℝ 1 h) (a b : ℝ) :
    lineIntegral F (c ∘ h) a b = lineIntegral F c (h a) (h b) := by
  unfold lineIntegral
  simp_rw [g1b_deriv_comp_path hc hh, dotProduct_smul, smul_eq_mul]
  have := intervalIntegral.integral_comp_mul_deriv (a := a) (b := b) (f := h) (f' := deriv h)
    (g := fun s => F (c s) ⬝ᵥ deriv c s)
    (fun x _ => (hh.differentiable one_ne_zero x).hasDerivAt)
    (hh.continuous_deriv le_rfl).continuousOn (g1b_continuous_dot hF hc)
  rw [← this]
  exact intervalIntegral.integral_congr fun t _ => by simp [Function.comp, mul_comm]

/-- DLMF 1.6.40: for an orientation-reversing `C¹` reparametrization (`h(a) = b'`,
`h(b) = a'`) the line integral changes sign. -/
@[dlmf 1.6.E40]
theorem lineIntegral_comp_reverse {F : (Fin 3 → ℝ) → Fin 3 → ℝ} {c : ℝ → Fin 3 → ℝ}
    {h : ℝ → ℝ} (hF : Continuous F) (hc : ContDiff ℝ 1 c) (hh : ContDiff ℝ 1 h)
    {a b a' b' : ℝ} (ha : h a = b') (hb : h b = a') :
    lineIntegral F (c ∘ h) a b = -lineIntegral F c a' b' := by
  rw [lineIntegral_comp hF hc hh, ha, hb, lineIntegral, lineIntegral,
    intervalIntegral.integral_symm]

/-- DLMF 1.6.41: path integrals of a continuous `f` are invariant under monotone `C¹`
reparametrizations, orientation preserving (`h` nondecreasing) or reversing
(`h` nonincreasing). -/
@[dlmf 1.6.E41]
theorem pathIntegral_comp {f : (Fin 3 → ℝ) → ℝ} {c : ℝ → Fin 3 → ℝ} {h : ℝ → ℝ}
    (hf : Continuous f) (hc : ContDiff ℝ 1 c) (hh : ContDiff ℝ 1 h) (a b : ℝ) :
    (Monotone h → pathIntegral f (c ∘ h) a b = pathIntegral f c (h a) (h b)) ∧
      (Antitone h → pathIntegral f (c ∘ h) a b = pathIntegral f c (h b) (h a)) := by
  have hg : Continuous fun s => f (c s) * vecNorm (deriv c s) := by
    have h1 : Continuous fun s => f (c s) := hf.comp hc.continuous
    have h2 : Continuous (deriv c) := hc.continuous_deriv le_rfl
    simp only [vecNorm, dotProduct]
    fun_prop
  have key := intervalIntegral.integral_comp_mul_deriv (a := a) (b := b) (f := h)
    (f' := deriv h) (g := fun s => f (c s) * vecNorm (deriv c s))
    (fun x _ => (hh.differentiable one_ne_zero x).hasDerivAt)
    (hh.continuous_deriv le_rfl).continuousOn hg
  unfold pathIntegral
  simp_rw [g1b_deriv_comp_path hc hh, g1b_vecNorm_smul]
  constructor
  · intro hm
    rw [← key]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Function.comp, abs_of_nonneg (hm.deriv_nonneg (x := t))]
    ring
  · intro ha
    rw [intervalIntegral.integral_symm (h a) (h b), ← key, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have : deriv h t ≤ 0 := by
      have := (ha.neg).deriv_nonneg (x := t)
      rwa [deriv.fun_neg, neg_nonneg] at this
    simp only [Function.comp, abs_of_nonpos this]
    ring

/-- DLMF 1.6.42 (gradient theorem): for `f` and the path `c` continuously differentiable,
`∫_c ∇f · ds = f(c(b)) - f(c(a))`. -/
@[dlmf 1.6.E42]
theorem lineIntegral_grad {f : (Fin 3 → ℝ) → ℝ} {c : ℝ → Fin 3 → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : ContDiff ℝ 1 c) (a b : ℝ) :
    lineIntegral (grad f) c a b = f (c b) - f (c a) := by
  have hfd : ∀ y, DifferentiableAt ℝ f y := fun y => hf.differentiable one_ne_zero y
  have hgrad : grad f = fun y i => fderiv ℝ f y (Pi.single i 1) := by
    funext y i
    exact partialDeriv_eq_fderiv i (hfd y)
  have hderiv : ∀ t, HasDerivAt (fun s => f (c s)) (grad f (c t) ⬝ᵥ deriv c t) t := by
    intro t
    have := hasDerivAt_comp_pi (hfd (c t)) (hc.differentiable one_ne_zero t)
    refine this.congr_deriv (Finset.sum_congr rfl fun i _ => ?_)
    rw [((hasDerivAt_pi.mp (hc.differentiable one_ne_zero t).hasDerivAt) i).deriv]
    rfl
  have hcont : Continuous fun t => grad f (c t) ⬝ᵥ deriv c t := by
    refine g1b_continuous_dot (F := grad f) ?_ hc
    rw [hgrad]
    have := hf.continuous_fderiv one_ne_zero
    exact continuous_pi fun i => this.clm_apply continuous_const
  unfold lineIntegral
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    (hcont.intervalIntegrable a b)

/-! ### §1.6(v) Surfaces -/

/-- DLMF §1.6(v): the vector `T_u × T_v` is normal to the surface, i.e. orthogonal to both
tangent vectors. -/
@[dlmf 1.6.v]
theorem tangent_dotProduct_cross (Φ : ℝ × ℝ → Fin 3 → ℝ) (p : ℝ × ℝ) :
    tangentU Φ p ⬝ᵥ (tangentU Φ p ⨯₃ tangentV Φ p) = 0 ∧
      tangentV Φ p ⬝ᵥ (tangentU Φ p ⨯₃ tangentV Φ p) = 0 := by
  exact ⟨dot_self_cross _ _, dot_cross_self _ _⟩

lemma g1b_tangentU_apply {Φ : ℝ × ℝ → Fin 3 → ℝ} {p : ℝ × ℝ}
    (hu : DifferentiableAt ℝ (fun u => Φ (u, p.2)) p.1) (i : Fin 3) :
    tangentU Φ p i = deriv (fun u => Φ (u, p.2) i) p.1 :=
  ((hasDerivAt_pi.mp hu.hasDerivAt) i).deriv.symm

lemma g1b_tangentV_apply {Φ : ℝ × ℝ → Fin 3 → ℝ} {p : ℝ × ℝ}
    (hv : DifferentiableAt ℝ (fun v => Φ (p.1, v)) p.2) (i : Fin 3) :
    tangentV Φ p i = deriv (fun v => Φ (p.1, v) i) p.2 :=
  ((hasDerivAt_pi.mp hv.hasDerivAt) i).deriv.symm

/-- DLMF 1.6.49: `‖T_u × T_v‖² = (∂(x,y)/∂(u,v))² + (∂(y,z)/∂(u,v))² + (∂(x,z)/∂(u,v))²`,
at a point where both sections of `Φ = (x, y, z)` are differentiable. -/
@[dlmf 1.6.E49]
theorem vecNorm_tangent_cross {Φ : ℝ × ℝ → Fin 3 → ℝ} {p : ℝ × ℝ}
    (hu : DifferentiableAt ℝ (fun u => Φ (u, p.2)) p.1)
    (hv : DifferentiableAt ℝ (fun v => Φ (p.1, v)) p.2) :
    vecNorm (tangentU Φ p ⨯₃ tangentV Φ p) =
      Real.sqrt (jacobianDet2 (fun q => Φ q 0) (fun q => Φ q 1) p ^ 2 +
        jacobianDet2 (fun q => Φ q 1) (fun q => Φ q 2) p ^ 2 +
        jacobianDet2 (fun q => Φ q 0) (fun q => Φ q 2) p ^ 2) := by
  rw [vecNorm]
  congr 1
  simp only [dotProduct_fin_three, cross_apply, jacobianDet2, Matrix.det_fin_two_of,
    g1b_tangentU_apply hu, g1b_tangentV_apply hv]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- `HasDerivAt` for a vector `![u₀, u₁, u₂]` of scalar functions. -/
lemma g1b_hasDerivAt_vec3 {u₀ u₁ u₂ : ℝ → ℝ} {d₀ d₁ d₂ t : ℝ} (h₀ : HasDerivAt u₀ d₀ t)
    (h₁ : HasDerivAt u₁ d₁ t) (h₂ : HasDerivAt u₂ d₂ t) :
    HasDerivAt (fun s => ![u₀ s, u₁ s, u₂ s]) ![d₀, d₁, d₂] t := by
  refine hasDerivAt_pi.mpr fun i => ?_
  fin_cases i <;> simpa

/-- DLMF 1.6.50: for the sphere `Φ(θ, φ) = ρ (sin θ cos φ, sin θ sin φ, cos θ)`,
`‖T_θ × T_φ‖ = ρ² |sin θ|`. -/
@[dlmf 1.6.E50]
theorem vecNorm_tangent_cross_sphere (ρ θ φ : ℝ) :
    let Φ : ℝ × ℝ → Fin 3 → ℝ := fun q =>
      ![ρ * Real.sin q.1 * Real.cos q.2, ρ * Real.sin q.1 * Real.sin q.2, ρ * Real.cos q.1]
    vecNorm (tangentU Φ (θ, φ) ⨯₃ tangentV Φ (θ, φ)) = ρ ^ 2 * |Real.sin θ| := by
  intro Φ
  have hu : tangentU Φ (θ, φ) = ![ρ * Real.cos θ * Real.cos φ, ρ * Real.cos θ * Real.sin φ,
      -(ρ * Real.sin θ)] := by
    refine HasDerivAt.deriv ?_
    refine g1b_hasDerivAt_vec3 ?_ ?_ ?_
    · simpa using ((Real.hasDerivAt_sin θ).const_mul ρ).mul_const (Real.cos φ)
    · simpa using ((Real.hasDerivAt_sin θ).const_mul ρ).mul_const (Real.sin φ)
    · simpa using (Real.hasDerivAt_cos θ).const_mul ρ
  have hv : tangentV Φ (θ, φ) = ![-(ρ * Real.sin θ * Real.sin φ), ρ * Real.sin θ * Real.cos φ,
      0] := by
    refine HasDerivAt.deriv ?_
    refine g1b_hasDerivAt_vec3 ?_ ?_ ?_
    · simpa using (Real.hasDerivAt_cos φ).const_mul (ρ * Real.sin θ)
    · simpa using (Real.hasDerivAt_sin φ).const_mul (ρ * Real.sin θ)
    · exact hasDerivAt_const φ (ρ * Real.cos θ)
  rw [hu, hv, vecNorm]
  have e : ![ρ * Real.cos θ * Real.cos φ, ρ * Real.cos θ * Real.sin φ, -(ρ * Real.sin θ)] ⨯₃
      ![-(ρ * Real.sin θ * Real.sin φ), ρ * Real.sin θ * Real.cos φ, 0] ⬝ᵥ
      (![ρ * Real.cos θ * Real.cos φ, ρ * Real.cos θ * Real.sin φ, -(ρ * Real.sin θ)] ⨯₃
        ![-(ρ * Real.sin θ * Real.sin φ), ρ * Real.sin θ * Real.cos φ, 0]) =
      (ρ ^ 2 * Real.sin θ) ^ 2 := by
    simp only [cross_apply, dotProduct_fin_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination ρ ^ 4 * Real.sin θ ^ 2 *
      ((Real.sin θ ^ 2 + Real.cos θ ^ 2 * (Real.sin φ ^ 2 + Real.cos φ ^ 2 + 1)) *
          Real.sin_sq_add_cos_sq φ + Real.sin_sq_add_cos_sq θ)
  rw [e, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ρ)]

/-- DLMF 1.6.51 (pointwise): for the graph `Φ(x, y) = (x, y, f(x, y))`,
`‖T_x × T_y‖ = √(1 + f_x² + f_y²)` where both sections of `f` are differentiable. -/
@[dlmf 1.6.E51]
theorem vecNorm_tangent_cross_graph {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hx : DifferentiableAt ℝ (fun t => f (t, p.2)) p.1)
    (hy : DifferentiableAt ℝ (fun t => f (p.1, t)) p.2) :
    vecNorm (tangentU (fun q => ![q.1, q.2, f q]) p ⨯₃ tangentV (fun q => ![q.1, q.2, f q]) p) =
      Real.sqrt (1 + deriv (fun t => f (t, p.2)) p.1 ^ 2 +
        deriv (fun t => f (p.1, t)) p.2 ^ 2) := by
  have hu : tangentU (fun q => ![q.1, q.2, f q]) p =
      ![1, 0, deriv (fun t => f (t, p.2)) p.1] :=
    (g1b_hasDerivAt_vec3 (hasDerivAt_id' p.1) (hasDerivAt_const p.1 p.2) hx.hasDerivAt).deriv
  have hv : tangentV (fun q => ![q.1, q.2, f q]) p =
      ![0, 1, deriv (fun t => f (p.1, t)) p.2] :=
    (g1b_hasDerivAt_vec3 (hasDerivAt_const p.2 p.1) (hasDerivAt_id' p.2) hy.hasDerivAt).deriv
  rw [hu, hv, vecNorm]
  congr 1
  simp only [cross_apply, dotProduct_fin_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- DLMF 1.6.51: the area of the graph `z = f(x, y)` over `D` is
`∬_D √(1 + f_x² + f_y²) dA`, for `f` with differentiable sections. -/
@[dlmf 1.6.E51]
theorem surfaceArea_graph {f : ℝ × ℝ → ℝ} {D : Set (ℝ × ℝ)}
    (hx : ∀ p ∈ D, DifferentiableAt ℝ (fun t => f (t, p.2)) p.1)
    (hy : ∀ p ∈ D, DifferentiableAt ℝ (fun t => f (p.1, t)) p.2) (hD : MeasurableSet D) :
    surfaceArea (fun q => ![q.1, q.2, f q]) D =
      ∫ p in D, Real.sqrt (1 + deriv (fun t => f (t, p.2)) p.1 ^ 2 +
        deriv (fun t => f (p.1, t)) p.2 ^ 2) :=
  setIntegral_congr_fun hD fun p hp => vecNorm_tangent_cross_graph (hx p hp) (hy p hp)

/-- An integral over `(a, b) × (0, c)` of a function of the first coordinate. -/
lemma g1b_setIntegral_Ioo_prod (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) {c : ℝ} (hc : 0 ≤ c) :
    ∫ p in Ioo a b ×ˢ Ioo 0 c, g p.1 = c * ∫ x in a..b, g x := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have := integral_prod_mul (μ := volume.restrict (Ioo a b)) (ν := volume.restrict (Ioo 0 c))
    g (fun _ => (1 : ℝ))
  simp only [mul_one] at this
  rw [this, intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  simp [hc, mul_comm]

/-- DLMF 1.6.52 (pointwise): for the surface of revolution of `y = f(x)` about the `x`-axis,
`Φ(x, t) = (x, f(x) cos t, f(x) sin t)`, `‖T_x × T_t‖ = |f(x)| √(1 + f'(x)²)`. -/
@[dlmf 1.6.E52]
theorem vecNorm_tangent_cross_revolution_x {f : ℝ → ℝ} {x t : ℝ}
    (hf : DifferentiableAt ℝ f x) :
    vecNorm (tangentU (fun q => ![q.1, f q.1 * Real.cos q.2, f q.1 * Real.sin q.2]) (x, t) ⨯₃
      tangentV (fun q => ![q.1, f q.1 * Real.cos q.2, f q.1 * Real.sin q.2]) (x, t)) =
      |f x| * Real.sqrt (1 + deriv f x ^ 2) := by
  have hu : tangentU (fun q => ![q.1, f q.1 * Real.cos q.2, f q.1 * Real.sin q.2]) (x, t) =
      ![1, deriv f x * Real.cos t, deriv f x * Real.sin t] :=
    (g1b_hasDerivAt_vec3 (hasDerivAt_id' x) (hf.hasDerivAt.mul_const (Real.cos t))
      (hf.hasDerivAt.mul_const (Real.sin t))).deriv
  have hv : tangentV (fun q => ![q.1, f q.1 * Real.cos q.2, f q.1 * Real.sin q.2]) (x, t) =
      ![0, -(f x * Real.sin t), f x * Real.cos t] := by
    refine (g1b_hasDerivAt_vec3 (hasDerivAt_const t x) ?_
      ((Real.hasDerivAt_sin t).const_mul (f x))).deriv
    simpa using (Real.hasDerivAt_cos t).const_mul (f x)
  rw [hu, hv, vecNorm, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  simp only [cross_apply, dotProduct_fin_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination (f x ^ 2 * deriv f x ^ 2 * (Real.sin t ^ 2 + Real.cos t ^ 2 + 1) +
    f x ^ 2) * Real.sin_sq_add_cos_sq t

/-- DLMF 1.6.52: the area of the surface of revolution of `y = f(x)`, `x ∈ [a, b]`, about the
`x`-axis is `2π ∫ₐᵇ |f(x)| √(1 + f'(x)²) dx`, for `f` differentiable (both sides vanish
together when the integrand is not integrable). -/
@[dlmf 1.6.E52]
theorem surfaceArea_revolution_x {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x, DifferentiableAt ℝ f x) :
    surfaceArea (fun q => ![q.1, f q.1 * Real.cos q.2, f q.1 * Real.sin q.2])
        (Ioo a b ×ˢ Ioo 0 (2 * Real.pi)) =
      2 * Real.pi * ∫ x in a..b, |f x| * Real.sqrt (1 + deriv f x ^ 2) := by
  rw [surfaceArea, ← g1b_setIntegral_Ioo_prod _ hab (by positivity)]
  refine setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) fun p _ => ?_
  obtain ⟨x, t⟩ := p
  exact vecNorm_tangent_cross_revolution_x (hf x)

/-- DLMF 1.6.53 (pointwise): for the surface of revolution of `y = f(x)` about the `y`-axis,
`Φ(x, t) = (x cos t, f(x), x sin t)`, `‖T_x × T_t‖ = |x| √(1 + f'(x)²)`. -/
@[dlmf 1.6.E53]
theorem vecNorm_tangent_cross_revolution_y {f : ℝ → ℝ} {x t : ℝ}
    (hf : DifferentiableAt ℝ f x) :
    vecNorm (tangentU (fun q => ![q.1 * Real.cos q.2, f q.1, q.1 * Real.sin q.2]) (x, t) ⨯₃
      tangentV (fun q => ![q.1 * Real.cos q.2, f q.1, q.1 * Real.sin q.2]) (x, t)) =
      |x| * Real.sqrt (1 + deriv f x ^ 2) := by
  have hu : tangentU (fun q => ![q.1 * Real.cos q.2, f q.1, q.1 * Real.sin q.2]) (x, t) =
      ![Real.cos t, deriv f x, Real.sin t] := by
    refine (g1b_hasDerivAt_vec3 ?_ hf.hasDerivAt ?_).deriv
    · simpa using (hasDerivAt_id x).mul_const (Real.cos t)
    · simpa using (hasDerivAt_id x).mul_const (Real.sin t)
  have hv : tangentV (fun q => ![q.1 * Real.cos q.2, f q.1, q.1 * Real.sin q.2]) (x, t) =
      ![-(x * Real.sin t), 0, x * Real.cos t] := by
    refine (g1b_hasDerivAt_vec3 ?_ (hasDerivAt_const t (f x))
      ((Real.hasDerivAt_sin t).const_mul x)).deriv
    simpa using (Real.hasDerivAt_cos t).const_mul x
  rw [hu, hv, vecNorm, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  simp only [cross_apply, dotProduct_fin_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination (x ^ 2 * deriv f x ^ 2 +
    x ^ 2 * (Real.sin t ^ 2 + Real.cos t ^ 2 + 1)) * Real.sin_sq_add_cos_sq t

/-- DLMF 1.6.53: the area of the surface of revolution of `y = f(x)`, `x ∈ [a, b]`, about the
`y`-axis is `2π ∫ₐᵇ |x| √(1 + f'(x)²) dx`, for `f` differentiable (both sides vanish together
when the integrand is not integrable). -/
@[dlmf 1.6.E53]
theorem surfaceArea_revolution_y {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x, DifferentiableAt ℝ f x) :
    surfaceArea (fun q => ![q.1 * Real.cos q.2, f q.1, q.1 * Real.sin q.2])
        (Ioo a b ×ˢ Ioo 0 (2 * Real.pi)) =
      2 * Real.pi * ∫ x in a..b, |x| * Real.sqrt (1 + deriv f x ^ 2) := by
  rw [surfaceArea, ← g1b_setIntegral_Ioo_prod _ hab (by positivity)]
  refine setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) fun p _ => ?_
  obtain ⟨x, t⟩ := p
  exact vecNorm_tangent_cross_revolution_y (hf x)

/-- DLMF §1.6(v): the area is independent of the parametrization: if `Φ₁ = Φ₂ ∘ ψ` with
`ψ : D₁ → D₂` a `C¹` diffeomorphism of open sets and `Φ₂` of class `C¹`, then
`A(Φ₁(D₁)) = A(Φ₂(D₂))`. -/
@[dlmf 1.6.v]
theorem surfaceArea_comp_diffeomorph {Φ : ℝ × ℝ → Fin 3 → ℝ} {ψ : ℝ × ℝ → ℝ × ℝ}
    {D₁ D₂ : Set (ℝ × ℝ)} (hD₁ : IsOpen D₁) (hΦ : ContDiff ℝ 1 Φ) (hψ : ContDiffOn ℝ 1 ψ D₁)
    (hbij : BijOn ψ D₁ D₂) (hdet : ∀ p ∈ D₁, (fderiv ℝ ψ p).det ≠ 0) :
    surfaceArea (Φ ∘ ψ) D₁ = surfaceArea Φ D₂ := by
  sorry

/-- DLMF 1.6.56: the flux is invariant under orientation-preserving reparametrizations and
changes sign under orientation-reversing ones: for `Φ₁ = Φ₂ ∘ ψ` with `ψ : D₁ → D₂` a `C¹`
diffeomorphism of open sets and `F` continuous, the fluxes agree if `det Dψ > 0` on `D₁`
(then `T_u × T_v` has the same direction for both) and are opposite if `det Dψ < 0`. -/
@[dlmf 1.6.E56]
theorem fluxIntegral_comp_diffeomorph {F : (Fin 3 → ℝ) → Fin 3 → ℝ} {Φ : ℝ × ℝ → Fin 3 → ℝ}
    {ψ : ℝ × ℝ → ℝ × ℝ} {D₁ D₂ : Set (ℝ × ℝ)} (hF : Continuous F) (hD₁ : IsOpen D₁)
    (hΦ : ContDiff ℝ 1 Φ) (hψ : ContDiffOn ℝ 1 ψ D₁) (hbij : BijOn ψ D₁ D₂) :
    ((∀ p ∈ D₁, 0 < (fderiv ℝ ψ p).det) → fluxIntegral F (Φ ∘ ψ) D₁ = fluxIntegral F Φ D₂) ∧
      ((∀ p ∈ D₁, (fderiv ℝ ψ p).det < 0) →
        fluxIntegral F (Φ ∘ ψ) D₁ = -fluxIntegral F Φ D₂) := by
  sorry

/-! ### Gauss's theorem and Green's identities -/

/-- DLMF 1.6.58 (Gauss's or divergence theorem): if the piecewise smooth surface
`S = ⋃ Φ i (D i)` is the complete boundary of the compact set `V`, oriented by outward
normals, and `F` is continuously differentiable on an open set containing `V`, then
`∭_V ∇ · F dV = ∬_S F · dS`. -/
@[dlmf 1.6.E58]
theorem integral_divergence_eq_sum_fluxIntegral {V : Set (Fin 3 → ℝ)} {ι : Type*} [Fintype ι]
    {Φ : ι → ℝ × ℝ → Fin 3 → ℝ} {D : ι → Set (ℝ × ℝ)}
    (hV : HasPiecewiseSmoothBoundary V ι Φ D) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hVU : V ⊆ U) {F : (Fin 3 → ℝ) → Fin 3 → ℝ} (hF : ContDiffOn ℝ 1 F U) :
    ∫ x in V, divergence F x = ∑ i, fluxIntegral F (Φ i) (D i) := by
  sorry

/-- The gradient of a `C²` function on an open set is `C¹` there. -/
lemma g1b_contDiffOn_grad {g : (Fin 3 → ℝ) → ℝ} {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hg : ContDiffOn ℝ 2 g U) : ContDiffOn ℝ 1 (grad g) U := by
  have hfd := hg.fderiv_of_isOpen hU (m := 1) (by norm_num)
  refine contDiffOn_pi.mpr fun i => ?_
  refine (hfd.clm_apply (contDiffOn_const (c := (Pi.single i 1 : Fin 3 → ℝ)))).congr
    fun y hy => ?_
  exact partialDeriv_eq_fderiv i
    ((hg.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))

/-- DLMF 1.6.59 (Green's first identity): under the hypotheses of Gauss's theorem, for `f`, `g`
twice continuously differentiable on an open set containing `V`,
`∭_V (f ∇²g + ∇f · ∇g) dV = ∬_S f ∂g/∂n dA`; the right side is the flux of `f ∇g`, since
`n dA = (T_u × T_v) du dv`. -/
@[dlmf 1.6.E59]
theorem integral_green_first_identity {V : Set (Fin 3 → ℝ)} {ι : Type*} [Fintype ι]
    {Φ : ι → ℝ × ℝ → Fin 3 → ℝ} {D : ι → Set (ℝ × ℝ)}
    (hV : HasPiecewiseSmoothBoundary V ι Φ D) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hVU : V ⊆ U) {f g : (Fin 3 → ℝ) → ℝ} (hf : ContDiffOn ℝ 2 f U)
    (hg : ContDiffOn ℝ 2 g U) :
    ∫ x in V, (f x * laplacian g x + grad f x ⬝ᵥ grad g x) =
      ∑ i, fluxIntegral (fun y => f y • grad g y) (Φ i) (D i) := by
  have hF : ContDiffOn ℝ 1 (fun y => f y • grad g y) U :=
    (hf.of_le (by norm_num)).smul (g1b_contDiffOn_grad hU hg)
  rw [← integral_divergence_eq_sum_fluxIntegral hV hU hVU hF]
  refine setIntegral_congr_fun hV.compact.isClosed.measurableSet fun x hx => ?_
  have hfx := hf.contDiffAt (hU.mem_nhds (hVU hx))
  have hgx := hg.contDiffAt (hU.mem_nhds (hVU hx))
  have hdg : DifferentiableAt ℝ (grad g) x :=
    differentiableAt_pi.mpr fun j => g1b_differentiableAt_partialDeriv j hgx
  rw [divergence_smul (hfx.differentiableAt (by simp)) hdg, laplacian_eq_divergence_grad,
    dotProduct_comm]

/-- DLMF 1.6.60 (Green's second identity): under the hypotheses of Gauss's theorem, for `f`,
`g` twice continuously differentiable on an open set containing `V`,
`∭_V (f ∇²g - g ∇²f) dV = ∬_S (f ∂g/∂n - g ∂f/∂n) dA`. -/
@[dlmf 1.6.E60]
theorem integral_green_second_identity {V : Set (Fin 3 → ℝ)} {ι : Type*} [Fintype ι]
    {Φ : ι → ℝ × ℝ → Fin 3 → ℝ} {D : ι → Set (ℝ × ℝ)}
    (hV : HasPiecewiseSmoothBoundary V ι Φ D) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hVU : V ⊆ U) {f g : (Fin 3 → ℝ) → ℝ} (hf : ContDiffOn ℝ 2 f U)
    (hg : ContDiffOn ℝ 2 g U) :
    ∫ x in V, (f x * laplacian g x - g x * laplacian f x) =
      ∑ i, fluxIntegral (fun y => f y • grad g y - g y • grad f y) (Φ i) (D i) := by
  have hF : ContDiffOn ℝ 1 (fun y => f y • grad g y - g y • grad f y) U :=
    ((hf.of_le (by norm_num)).smul (g1b_contDiffOn_grad hU hg)).sub
      ((hg.of_le (by norm_num)).smul (g1b_contDiffOn_grad hU hf))
  rw [← integral_divergence_eq_sum_fluxIntegral hV hU hVU hF]
  refine setIntegral_congr_fun hV.compact.isClosed.measurableSet fun x hx => ?_
  exact (divergence_smul_grad_sub (hf.contDiffAt (hU.mem_nhds (hVU hx)))
    (hg.contDiffAt (hU.mem_nhds (hVU hx)))).symm

end DLMF.AlgebraicAnalytic
