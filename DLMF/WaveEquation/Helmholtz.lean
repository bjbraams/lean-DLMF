/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.RegularizedSeries

/-!
# Separating the Helmholtz equation (Temme Chapter 10)

Temme separates `Δu + k²u = 0` in cylindrical and spherical coordinates. The radial factors are
Bessel functions, and for integer azimuthal order the separated solutions are, in Cartesian form,
`(x+iy)ⁿ ₀F̃₁(n + d/2; -k²r²/4)` with `d = 2` or `3`. These expressions are entire in the
Cartesian coordinates, so the Helmholtz equation can be checked at every point, including the
axis and the origin. This file proves:
* `helmholtz_cylinderWave`: the cylinder wave solves `Δu + k²u = 0` on `ℝ²`, and
  `cylinderWave_polar` identifies it with `(2/k)ⁿ J_n(kr) e^{inφ}` (Temme §10.2.1).
* `helmholtz_cylinderWave_exp`: with the axial factor `e^{iβz}` it solves
  `Δu + (κ² + β²)u = 0` on `ℝ³`.
* `helmholtz_sphericalWave`: the spherical wave solves `Δu + k²u = 0` on `ℝ³`, and
  `sphericalWave_spherical` identifies it with `(r sin θ)ⁿ e^{inφ} (kr/2)^{-(n+1/2)} J_{n+1/2}(kr)`,
  a multiple of `j_n(kr) Pⁿₙ(cos θ) e^{inφ}` (Temme §10.2.2).
* `heatMode_pde`, `heatMode_boundary`: Temme's cooled-cylinder modes `J₀(jr) e^{-j²t}` (§10.3.1).

The Laplacians `laplacian2`, `laplacian3` are written with iterated one-variable derivatives.
In each case the computation reduces to the contiguous relation
`₀F̃₁(c; w) = c ₀F̃₁(c+1; w) + w ₀F̃₁(c+2; w)`.
-/

@[expose] public section

open Complex
open scoped Real
open DLMF.Bessel

noncomputable section

namespace DLMF.WaveEquation

/-- Shorthand for the regularized `₀F₁(;c;w)`. -/
abbrev F01 (c w : ℂ) : ℂ := regularizedHGFun (∅ : Multiset ℂ) {c} w

/-- Chain rule for `t ↦ ₀F̃₁(c; a t² + b)`. -/
theorem hasDerivAt_F01_quad (c a b : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => F01 c (a * (t : ℂ) ^ 2 + b))
      (F01 (c + 1) (a * (t : ℂ) ^ 2 + b) * (2 * a * t)) t := by
  have hq : HasDerivAt (fun t : ℝ => a * (t : ℂ) ^ 2 + b) (2 * a * t) t := by
    have := (((hasDerivAt_id (t : ℂ)).pow 2).const_mul a).add_const b
    have h := this.comp_ofReal
    refine h.congr_deriv ?_
    simp; ring
  exact (hasDerivAt_regularized0F1 c _).comp t hq

/-- Second derivative of `t ↦ h(t) ₀F₁(c; a t² + b)`. -/
theorem iteratedDeriv_two_mul_F01 {h h1 h2 : ℝ → ℂ} (hh : ∀ t, HasDerivAt h (h1 t) t)
    (hh1 : ∀ t, HasDerivAt h1 (h2 t) t) (c a b : ℂ) (t : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => h t * F01 c (a * (t : ℂ) ^ 2 + b)) t =
      h2 t * F01 c (a * (t : ℂ) ^ 2 + b) +
        2 * h1 t * (2 * a * t) * F01 (c + 1) (a * (t : ℂ) ^ 2 + b) +
        h t * ((2 * a * t) ^ 2 * F01 (c + 1 + 1) (a * (t : ℂ) ^ 2 + b) +
          2 * a * F01 (c + 1) (a * (t : ℂ) ^ 2 + b)) := by
  have hd : deriv (fun t : ℝ => h t * F01 c (a * (t : ℂ) ^ 2 + b)) = fun t =>
      h1 t * F01 c (a * (t : ℂ) ^ 2 + b) +
        h t * (F01 (c + 1) (a * (t : ℂ) ^ 2 + b) * (2 * a * t)) := by
    funext s
    exact ((hh s).mul (hasDerivAt_F01_quad c a b s)).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd]
  have hlin : HasDerivAt (fun t : ℝ => 2 * a * (t : ℂ)) (2 * a) t := by
    simpa using ((hasDerivAt_id (t : ℂ)).const_mul (2 * a)).comp_ofReal
  have h' := ((hh1 t).mul (hasDerivAt_F01_quad c a b t)).add
    ((hh t).mul ((hasDerivAt_F01_quad (c + 1) a b t).mul hlin))
  have h'' : HasDerivAt (fun t : ℝ => h1 t * F01 c (a * (t : ℂ) ^ 2 + b) +
      h t * (F01 (c + 1) (a * (t : ℂ) ^ 2 + b) * (2 * a * t))) _ t := h'
  rw [h''.deriv]
  simp only [Pi.mul_apply]
  ring


/-- Derivative of `t ↦ (p + q t)ᵐ`. -/
theorem hasDerivAt_pow_affine (p q : ℂ) (m : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (p + q * t) ^ m) (m * (p + q * t) ^ (m - 1) * q) t := by
  have h := (((hasDerivAt_id (t : ℂ)).const_mul q).const_add p).pow m
  exact h.comp_ofReal.congr_deriv (by simp)

/-- Derivative of `t ↦ m (p + q t)^{m-1} q`. -/
theorem hasDerivAt_pow_affine' (p q : ℂ) (m : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (m : ℂ) * (p + q * t) ^ (m - 1) * q)
      ((m : ℂ) * ((m - 1 : ℕ) * (p + q * t) ^ (m - 1 - 1) * q) * q) t :=
  ((hasDerivAt_pow_affine p q (m - 1) t).const_mul (m : ℂ)).mul_const q

/-- The two-dimensional Laplacian in Cartesian coordinates, through second partial derivatives. -/
def laplacian2 (u : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  iteratedDeriv 2 (fun t => u t y) x + iteratedDeriv 2 (fun t => u x t) y

/-- The cylinder wave `(x+iy)ⁿ ₀F̃₁(n+1; -k²(x²+y²)/4)`, which equals `(2/k)ⁿ J_n(kr) e^{inφ}`
in polar coordinates. -/
def cylinderWave (n : ℕ) (k : ℂ) (x y : ℝ) : ℂ :=
  ((x : ℂ) + I * y) ^ n * F01 (n + 1) (-(k ^ 2) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2) / 4)

/-- `n Z^{n-1} Z = n Zⁿ`, including `n = 0`. -/
theorem natCast_mul_pow_pred_mul (n : ℕ) (Z : ℂ) : (n : ℂ) * (Z ^ (n - 1) * Z) = n * Z ^ n := by
  rcases n with _ | n
  · simp
  · simp [pow_succ]

/-- **Separation in cylindrical coordinates** (Temme §10.2.1): the cylinder wave solves the
Helmholtz equation `Δu + k²u = 0` on all of `ℝ²`. -/
theorem helmholtz_cylinderWave (n : ℕ) (k : ℂ) (x y : ℝ) :
    laplacian2 (cylinderWave n k) x y + k ^ 2 * cylinderWave n k x y = 0 := by
  set c : ℂ := n + 1
  set a : ℂ := -(k ^ 2) / 4
  have hx : (fun t => cylinderWave n k t y) = fun t : ℝ =>
      (I * y + 1 * t) ^ n * F01 c (a * (t : ℂ) ^ 2 + a * (y : ℂ) ^ 2) := by
    funext t; simp only [cylinderWave, c, a]; ring_nf
  have hy : (fun t => cylinderWave n k x t) = fun t : ℝ =>
      ((x : ℂ) + I * t) ^ n * F01 c (a * (t : ℂ) ^ 2 + a * (x : ℂ) ^ 2) := by
    funext t; simp only [cylinderWave, c, a]; ring_nf
  have Dx := iteratedDeriv_two_mul_F01 (hasDerivAt_pow_affine (I * y) 1 n)
    (hasDerivAt_pow_affine' (I * y) 1 n) c a (a * (y : ℂ) ^ 2) x
  have Dy := iteratedDeriv_two_mul_F01 (hasDerivAt_pow_affine (x : ℂ) I n)
    (hasDerivAt_pow_affine' (x : ℂ) I n) c a (a * (x : ℂ) ^ 2) y
  have hcont : F01 c (a * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2)) =
      c * F01 (c + 1) (a * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2)) + a * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2) *
        F01 (c + 1 + 1) (a * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2)) := regularized0F1_contiguous _ _
  have hk : k ^ 2 = -4 * a := by simp only [a]; ring
  have hZ := natCast_mul_pow_pred_mul n ((x : ℂ) + I * y)
  rw [laplacian2, hx, hy, Dx, Dy]
  simp only [cylinderWave]
  rw [show -(k ^ 2) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2) / 4 = a * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2) by ring,
    show a * (x : ℂ) ^ 2 + a * (y : ℂ) ^ 2 = a * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2) by ring,
    show a * (y : ℂ) ^ 2 + a * (x : ℂ) ^ 2 = a * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2) by ring,
    show I * (y : ℂ) + 1 * x = x + I * y by ring]
  generalize F01 c (a * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2)) = G0 at *
  generalize F01 (c + 1) (a * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2)) = G1 at *
  generalize F01 (c + 1 + 1) (a * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2)) = G2 at *
  linear_combination (k ^ 2 * ((x : ℂ) + I * y) ^ n) * hcont +
    (((x : ℂ) + I * y) ^ n * (c * G1 + a * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2) * G2)) * hk +
    (4 * a * G1) * hZ +
    ((n : ℂ) * ((n - 1 : ℕ) : ℂ) * ((x : ℂ) + I * y) ^ (n - 1 - 1) * G0) * I_sq

/-- The three-dimensional Laplacian in Cartesian coordinates. -/
def laplacian3 (u : ℝ → ℝ → ℝ → ℂ) (x y z : ℝ) : ℂ :=
  iteratedDeriv 2 (fun t => u t y z) x + iteratedDeriv 2 (fun t => u x t z) y +
    iteratedDeriv 2 (fun t => u x y t) z

/-- The spherical wave `(x+iy)ⁿ ₀F̃₁(n+3/2; -k²r²/4)`, proportional to
`j_n(kr) Pⁿₙ(cos θ) e^{inφ}` in spherical coordinates. -/
def sphericalWave (n : ℕ) (k : ℂ) (x y z : ℝ) : ℂ :=
  ((x : ℂ) + I * y) ^ n *
    F01 (n + 3 / 2) (-(k ^ 2) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2 + (z : ℂ) ^ 2) / 4)

/-- **Separation in spherical coordinates** (Temme §10.2.2): the spherical wave solves the
Helmholtz equation `Δu + k²u = 0` on all of `ℝ³`. -/
theorem helmholtz_sphericalWave (n : ℕ) (k : ℂ) (x y z : ℝ) :
    laplacian3 (sphericalWave n k) x y z + k ^ 2 * sphericalWave n k x y z = 0 := by
  set c : ℂ := n + 3 / 2
  set a : ℂ := -(k ^ 2) / 4
  set R : ℂ := (x : ℂ) ^ 2 + (y : ℂ) ^ 2 + (z : ℂ) ^ 2
  have hx : (fun t => sphericalWave n k t y z) = fun t : ℝ =>
      (I * y + 1 * t) ^ n * F01 c (a * (t : ℂ) ^ 2 + a * ((y : ℂ) ^ 2 + (z : ℂ) ^ 2)) := by
    funext t; simp only [sphericalWave, c, a]; ring_nf
  have hy : (fun t => sphericalWave n k x t z) = fun t : ℝ =>
      ((x : ℂ) + I * t) ^ n * F01 c (a * (t : ℂ) ^ 2 + a * ((x : ℂ) ^ 2 + (z : ℂ) ^ 2)) := by
    funext t; simp only [sphericalWave, c, a]; ring_nf
  have hz : (fun t => sphericalWave n k x y t) = fun t : ℝ =>
      (fun _ : ℝ => ((x : ℂ) + I * y) ^ n) t *
        F01 c (a * (t : ℂ) ^ 2 + a * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2)) := by
    funext t; simp only [sphericalWave, c, a]; ring_nf
  have Dx := iteratedDeriv_two_mul_F01 (hasDerivAt_pow_affine (I * y) 1 n)
    (hasDerivAt_pow_affine' (I * y) 1 n) c a (a * ((y : ℂ) ^ 2 + (z : ℂ) ^ 2)) x
  have Dy := iteratedDeriv_two_mul_F01 (hasDerivAt_pow_affine (x : ℂ) I n)
    (hasDerivAt_pow_affine' (x : ℂ) I n) c a (a * ((x : ℂ) ^ 2 + (z : ℂ) ^ 2)) y
  have Dz := iteratedDeriv_two_mul_F01 (h := fun _ : ℝ => ((x : ℂ) + I * y) ^ n)
    (h1 := fun _ => 0) (h2 := fun _ => 0) (fun t => hasDerivAt_const t _)
    (fun t => hasDerivAt_const t _) c a (a * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2)) z
  have hcont : F01 c (a * R) = c * F01 (c + 1) (a * R) + a * R * F01 (c + 1 + 1) (a * R) :=
    regularized0F1_contiguous _ _
  have hk : k ^ 2 = -4 * a := by simp only [a]; ring
  have hZ := natCast_mul_pow_pred_mul n ((x : ℂ) + I * y)
  rw [laplacian3, hx, hy, hz, Dx, Dy, Dz]
  simp only [sphericalWave]
  rw [show -(k ^ 2) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2 + (z : ℂ) ^ 2) / 4 = a * R by
      simp only [a, R]; ring,
    show a * (x : ℂ) ^ 2 + a * ((y : ℂ) ^ 2 + (z : ℂ) ^ 2) = a * R by simp only [R]; ring,
    show a * (y : ℂ) ^ 2 + a * ((x : ℂ) ^ 2 + (z : ℂ) ^ 2) = a * R by simp only [R]; ring,
    show a * (z : ℂ) ^ 2 + a * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2) = a * R by simp only [R]; ring,
    show I * (y : ℂ) + 1 * x = x + I * y by ring]
  generalize F01 c (a * R) = G0 at *
  generalize F01 (c + 1) (a * R) = G1 at *
  generalize F01 (c + 1 + 1) (a * R) = G2 at *
  simp only [R, c] at hcont ⊢
  linear_combination (k ^ 2 * ((x : ℂ) + I * y) ^ n) * hcont +
    (((x : ℂ) + I * y) ^ n * (((n : ℂ) + 3 / 2) * G1 +
      a * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2 + (z : ℂ) ^ 2) * G2)) * hk +
    (4 * a * G1) * hZ +
    ((n : ℂ) * ((n - 1 : ℕ) : ℂ) * ((x : ℂ) + I * y) ^ (n - 1 - 1) * G0) * I_sq

/-- Cylinder waves with axial dependence: `(x+iy)ⁿ ₀F̃₁(n+1; -κ²(x²+y²)/4) e^{iβz}` solves
`Δu + (κ² + β²) u = 0` on `ℝ³` (Temme §10.2.1). -/
theorem helmholtz_cylinderWave_exp (n : ℕ) (κ β : ℂ) (x y z : ℝ) :
    laplacian3 (fun x y z => cylinderWave n κ x y * exp (I * β * z)) x y z +
      (κ ^ 2 + β ^ 2) * (cylinderWave n κ x y * exp (I * β * z)) = 0 := by
  have h2 := helmholtz_cylinderWave n κ x y
  rw [laplacian2] at h2
  have hz : iteratedDeriv 2 (fun t : ℝ => cylinderWave n κ x y * exp (I * β * t)) z =
      cylinderWave n κ x y * ((I * β) ^ 2 * exp (I * β * z)) := by
    have he (t : ℝ) : HasDerivAt (fun t : ℝ => exp (I * β * t)) (I * β * exp (I * β * t)) t := by
      have := (((hasDerivAt_id (t : ℂ)).const_mul (I * β)).cexp).comp_ofReal
      exact this.congr_deriv (by simp; ring)
    have hd : deriv (fun t : ℝ => cylinderWave n κ x y * exp (I * β * t)) =
        fun t : ℝ => cylinderWave n κ x y * (I * β * exp (I * β * t)) := by
      funext t; exact ((he t).const_mul _).deriv
    rw [iteratedDeriv_succ, iteratedDeriv_one, hd, (((he z).const_mul (I * β)).const_mul _).deriv]
    ring
  have hx : iteratedDeriv 2 (fun t => cylinderWave n κ t y * exp (I * β * z)) x =
      iteratedDeriv 2 (fun t => cylinderWave n κ t y) x * exp (I * β * z) := by
    rw [show (fun t => cylinderWave n κ t y * exp (I * β * z)) =
      fun t => exp (I * β * z) * cylinderWave n κ t y by funext t; ring,
      iteratedDeriv_const_mul_field]; ring
  have hy : iteratedDeriv 2 (fun t => cylinderWave n κ x t * exp (I * β * z)) y =
      iteratedDeriv 2 (fun t => cylinderWave n κ x t) y * exp (I * β * z) := by
    rw [show (fun t => cylinderWave n κ x t * exp (I * β * z)) =
      fun t => exp (I * β * z) * cylinderWave n κ x t by funext t; ring,
      iteratedDeriv_const_mul_field]; ring
  rw [laplacian3, hx, hy, hz]
  linear_combination exp (I * β * z) * h2 + (β ^ 2 * cylinderWave n κ x y * exp (I * β * z)) * I_sq

/-- In polar coordinates the cylinder wave is `(2/k)ⁿ J_n(kr) e^{inφ}`. -/
theorem cylinderWave_polar (n : ℕ) {k : ℂ} (hk : k ≠ 0) (r φ : ℝ) :
    cylinderWave n k (r * Real.cos φ) (r * Real.sin φ) =
      (2 / k) ^ n * besselJ n (k * r) * exp (I * n * φ) := by
  have hpol : ((r * Real.cos φ : ℝ) : ℂ) + I * ((r * Real.sin φ : ℝ) : ℂ) = r * exp (φ * I) := by
    rw [exp_mul_I]; push_cast; ring
  have hsq : ((r * Real.cos φ : ℝ) : ℂ) ^ 2 + ((r * Real.sin φ : ℝ) : ℂ) ^ 2 = (r : ℂ) ^ 2 := by
    have := Real.cos_sq_add_sin_sq φ
    have h' : ((Real.cos φ : ℝ) : ℂ) ^ 2 + ((Real.sin φ : ℝ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast this
    push_cast at h' ⊢
    linear_combination (r : ℂ) ^ 2 * h'
  rw [cylinderWave, hpol, hsq, besselJ_eq_regularized, cpow_natCast,
    show (I * n * φ : ℂ) = n * (φ * I) by ring, exp_nat_mul]
  rw [show -(k ^ 2) * (r : ℂ) ^ 2 / 4 = -((k * r) ^ 2 / 4) by ring]
  have h2 : (2 / k) ^ n * ((k * r) / 2) ^ n = (r : ℂ) ^ n := by
    rw [← mul_pow]; congr 1; field_simp
  linear_combination (-(exp (φ * I) ^ n * F01 (n + 1) (-((k * r) ^ 2 / 4)))) * h2

/-- In spherical coordinates the spherical wave is
`(r sin θ)ⁿ e^{inφ} (kr/2)^{-(n+1/2)} J_{n+1/2}(kr)`, a multiple of `j_n(kr) Pⁿₙ(cos θ) e^{inφ}`. -/
theorem sphericalWave_spherical (n : ℕ) {k : ℂ} {r : ℝ} (hkr : k * r ≠ 0) (θ φ : ℝ) :
    sphericalWave n k (r * Real.sin θ * Real.cos φ) (r * Real.sin θ * Real.sin φ)
        (r * Real.cos θ) =
      (r * Real.sin θ : ℂ) ^ n * exp (I * n * φ) * ((k * r) / 2) ^ (-((n : ℂ) + 1 / 2)) *
        besselJ (n + 1 / 2) (k * r) := by
  have hpol : ((r * Real.sin θ * Real.cos φ : ℝ) : ℂ) +
      I * ((r * Real.sin θ * Real.sin φ : ℝ) : ℂ) = (r * Real.sin θ : ℂ) * exp (φ * I) := by
    rw [exp_mul_I]; push_cast; ring
  have hsq : ((r * Real.sin θ * Real.cos φ : ℝ) : ℂ) ^ 2 +
      ((r * Real.sin θ * Real.sin φ : ℝ) : ℂ) ^ 2 + ((r * Real.cos θ : ℝ) : ℂ) ^ 2 =
        (r : ℂ) ^ 2 := by
    have h1 : ((Real.cos φ : ℝ) : ℂ) ^ 2 + ((Real.sin φ : ℝ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq φ
    have h2 : ((Real.cos θ : ℝ) : ℂ) ^ 2 + ((Real.sin θ : ℝ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq θ
    push_cast at h1 h2 ⊢
    linear_combination ((r : ℂ) ^ 2 * (Complex.sin θ) ^ 2) * h1 + (r : ℂ) ^ 2 * h2
  have hw : (k * r) / 2 ≠ 0 := div_ne_zero hkr two_ne_zero
  have hinv : ((k * r) / 2) ^ (-((n : ℂ) + 1 / 2)) * ((k * r) / 2) ^ ((n : ℂ) + 1 / 2) = 1 := by
    rw [cpow_neg, inv_mul_cancel₀ (cpow_ne_zero_iff.mpr (Or.inl hw))]
  rw [sphericalWave, hpol, hsq, besselJ_eq_regularized,
    show (I * n * φ : ℂ) = n * (φ * I) by ring, exp_nat_mul,
    show (n : ℂ) + 1 / 2 + 1 = n + 3 / 2 by ring,
    show -(k ^ 2) * (r : ℂ) ^ 2 / 4 = -((k * r) ^ 2 / 4) by ring]
  rw [mul_pow]
  linear_combination (-((r * Real.sin θ : ℂ) ^ n * exp (φ * I) ^ n *
    F01 (n + 3 / 2) (-((k * r) ^ 2 / 4)))) * hinv

/-- Temme's heat-conduction mode in a cylinder (§10.3.1): `J₀(jr) e^{-j²t}`. -/
def heatMode (j r t : ℝ) : ℂ := besselJ 0 (j * r) * exp (-(j ^ 2) * t)

/-- The mode solves the radially symmetric heat equation `u_rr + u_r/r = u_t` for `r ≠ 0`. -/
theorem heatMode_pde (j t : ℝ) {r : ℝ} (hr : r ≠ 0) :
    iteratedDeriv 2 (fun r => heatMode j r t) r + 1 / r * deriv (fun r => heatMode j r t) r =
      deriv (fun t => heatMode j r t) t := by
  set a : ℂ := -((j : ℂ) ^ 2) / 4
  have hJ : (fun r : ℝ => heatMode j r t) = fun r : ℝ =>
      (fun _ : ℝ => exp (-(j ^ 2 : ℂ) * t)) r * F01 1 (a * (r : ℂ) ^ 2 + 0) := by
    funext s; simp only [heatMode, besselJ_eq_regularized, a]; rw [cpow_zero]; ring_nf
  have D2 := iteratedDeriv_two_mul_F01 (h := fun _ : ℝ => exp (-(j ^ 2 : ℂ) * t))
    (h1 := fun _ => 0) (h2 := fun _ => 0) (fun s => hasDerivAt_const s _)
    (fun s => hasDerivAt_const s _) 1 a 0 r
  have D1 : deriv (fun r : ℝ => (fun _ : ℝ => exp (-(j ^ 2 : ℂ) * t)) r *
      F01 1 (a * (r : ℂ) ^ 2 + 0)) r =
      exp (-(j ^ 2 : ℂ) * t) * (F01 (1 + 1) (a * (r : ℂ) ^ 2 + 0) * (2 * a * r)) :=
    ((hasDerivAt_F01_quad 1 a 0 r).const_mul _).deriv
  have Dt : deriv (fun t : ℝ => heatMode j r t) t =
      besselJ 0 (j * r) * (-(j ^ 2 : ℂ) * exp (-(j ^ 2 : ℂ) * t)) := by
    have he : HasDerivAt (fun t : ℝ => exp (-(j ^ 2 : ℂ) * t))
        (-(j ^ 2 : ℂ) * exp (-(j ^ 2 : ℂ) * t)) t := by
      have := (((hasDerivAt_id (t : ℂ)).const_mul (-(j ^ 2 : ℂ))).cexp).comp_ofReal
      exact this.congr_deriv (by simp; ring)
    simp only [heatMode]
    exact (he.const_mul _).deriv
  have hcont : F01 1 (a * (r : ℂ) ^ 2 + 0) = 1 * F01 (1 + 1) (a * (r : ℂ) ^ 2 + 0) +
      (a * (r : ℂ) ^ 2 + 0) * F01 (1 + 1 + 1) (a * (r : ℂ) ^ 2 + 0) :=
    regularized0F1_contiguous _ _
  have hJ0 : besselJ 0 (j * r) = F01 1 (a * (r : ℂ) ^ 2 + 0) := by
    simp only [besselJ_eq_regularized, a]; rw [cpow_zero]; ring_nf
  rw [hJ, D2, D1, Dt, hJ0]
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  generalize exp (-(j ^ 2 : ℂ) * t) = E
  generalize F01 1 (a * (r : ℂ) ^ 2 + 0) = G0 at *
  generalize F01 (1 + 1) (a * (r : ℂ) ^ 2 + 0) = G1 at *
  generalize F01 (1 + 1 + 1) (a * (r : ℂ) ^ 2 + 0) = G2 at *
  field_simp
  simp only [a] at hcont ⊢
  linear_combination ((j : ℂ) ^ 2 * E) * hcont

/-- Boundary condition on the unit cylinder: if `J₀(j) = 0` the mode vanishes at `r = 1`. -/
theorem heatMode_boundary {j : ℝ} (hj : besselJ 0 j = 0) (t : ℝ) : heatMode j 1 t = 0 := by
  simp [heatMode, hj]

end DLMF.WaveEquation

end
