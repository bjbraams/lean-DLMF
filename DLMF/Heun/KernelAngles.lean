/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic
public import DLMFMathlib.Analysis.Calculus.Deriv.CompCurve
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The Type I kernel equation in angular variables (DLMF 31.10.7–31.10.8)

With `cos²θ = zt/a`, `sin²θ cos²φ = -(z-a)(t-a)/(a(1-a))`, `sin²θ sin²φ = (z-1)(t-1)/(1-a)`
(31.10.7 squared), a kernel `𝒦(z, t)` with `(𝒟_z - 𝒟_t)𝒦 = 0` satisfies the partial differential
equation 31.10.8 (with the sign of the `∂𝒦/∂φ` term corrected) in the variables `(θ, φ)`.

The proof differentiates the relations 31.10.7 implicitly along the coordinate lines, solves for
the first and second partial derivatives of `z` and `t`, and combines the second-order chain
rule for `𝒦(z(θ, φ), t(θ, φ))` with the kernel equation. In fact the left side of 31.10.8 equals
`4 sin²θ/(t - z)` times `(𝒟_z - 𝒟_t)𝒦`.

## Main results

* `DLMF.Heun.heun_kernel_typeI_angles'`: DLMF 31.10.7–31.10.8 without Fuchs's relation and
  without `a ∉ {0, 1}`.
-/

@[expose] public section

open Complex Filter Set
open scoped Topology

namespace DLMF.Heun

namespace KernelAngles

/-- The algebraic core of 31.10.8. The quantities `zt, tt` (resp. `zp, tp`) are the first
partial derivatives of `z, t` in `θ` divided by `cos θ sin θ` (resp. in `φ` divided by
`cos φ sin φ`), `Ztt, Ttt, Zpp, Tpp` the second partial derivatives, `u = sin²θ`, `C = cos²θ`,
`v = sin²φ`, `CP = cos²φ`. The hypotheses are the relations 31.10.7 and their first and second
derivatives along the coordinate lines; the conclusions are the coefficient identities of the
change of variables, with factor `4u/(t - z)`. -/
private theorem coefficient_identities {a γ δ ε Z T C u CP v zt tt zp tp Ztt Ttt Zpp Tpp : ℂ}
    (hTZ : T - Z ≠ 0) (hC : C = 1 - u) (hCP : CP = 1 - v)
    (r1 : Z * T = a * C) (r2 : (Z - 1) * (T - 1) = (1 - a) * u * v)
    (a1 : zt * T + Z * tt = -2 * a) (b1 : zt * (T - 1) + (Z - 1) * tt = 2 * (1 - a) * v)
    (a2 : Ztt * T + 2 * (C * u * zt * tt) + Z * Ttt = -2 * a * (C - u))
    (b2 : Ztt * (T - 1) + 2 * (C * u * zt * tt) + (Z - 1) * Ttt = 2 * (1 - a) * (C - u) * v)
    (c1 : zp * T + Z * tp = 0) (d1 : zp * (T - 1) + (Z - 1) * tp = 2 * (1 - a) * u)
    (c2 : Zpp * T + 2 * (CP * v * zp * tp) + Z * Tpp = 0)
    (d2 : Zpp * (T - 1) + 2 * (CP * v * zp * tp) + (Z - 1) * Tpp = 2 * (1 - a) * u * (CP - v)) :
    u * (C * u * zt ^ 2) + CP * v * zp ^ 2 = 4 * u / (T - Z) * (Z * (Z - 1) * (Z - a)) ∧
    u * (C * u * tt ^ 2) + CP * v * tp ^ 2 = -4 * u / (T - Z) * (T * (T - 1) * (T - a)) ∧
    u * (C * u * zt * tt) + CP * v * zp * tp = 0 ∧
    u * (Ztt + ((1 - 2 * γ) * u + (2 * δ + 2 * ε - 1) * C) * zt) + Zpp +
        ((2 * δ - 1) * CP - (2 * ε - 1) * v) * zp =
      4 * u / (T - Z) * (γ * (Z - 1) * (Z - a) + δ * Z * (Z - a) + ε * Z * (Z - 1)) ∧
    u * (Ttt + ((1 - 2 * γ) * u + (2 * δ + 2 * ε - 1) * C) * tt) + Tpp +
        ((2 * δ - 1) * CP - (2 * ε - 1) * v) * tp =
      -4 * u / (T - Z) * (γ * (T - 1) * (T - a) + δ * T * (T - a) + ε * T * (T - 1)) := by
  have hT : T = 1 + a * C - (1 - a) * u * v - Z := by linear_combination r1 - r2
  have hz2 : Z ^ 2 = (1 + a * C - (1 - a) * u * v) * Z - a * C := by
    linear_combination -r1 + Z * hT
  have hzt : zt = (-2 * a - Z * (-2 * a - 2 * (1 - a) * v)) / (T - Z) := by
    rw [eq_div_iff hTZ]; linear_combination a1 - Z * (a1 - b1)
  have htt : tt = -2 * a - 2 * (1 - a) * v - zt := by linear_combination a1 - b1
  have hzp : zp = -Z * (-2 * (1 - a) * u) / (T - Z) := by
    rw [eq_div_iff hTZ]; linear_combination c1 - Z * (c1 - d1)
  have htp : tp = -2 * (1 - a) * u - zp := by linear_combination c1 - d1
  have hZtt : Ztt = (-2 * a * (C - u) - 2 * (C * u * zt * tt) -
      Z * (-2 * a * (C - u) - 2 * (1 - a) * (C - u) * v)) / (T - Z) := by
    rw [eq_div_iff hTZ]; linear_combination a2 - Z * (a2 - b2)
  have hTtt : Ttt = -2 * a * (C - u) - 2 * (1 - a) * (C - u) * v - Ztt := by
    linear_combination a2 - b2
  have hZpp : Zpp = (-2 * (CP * v * zp * tp) - Z * (-2 * (1 - a) * u * (CP - v))) /
      (T - Z) := by
    rw [eq_div_iff hTZ]; linear_combination c2 - Z * (c2 - d2)
  have hTpp : Tpp = -2 * (1 - a) * u * (CP - v) - Zpp := by linear_combination c2 - d2
  clear a1 b1 a2 b2 c1 d1 c2 d2 r1 r2
  subst hTtt hTpp
  subst hZtt hZpp
  subst htt htp
  subst hzt hzp
  subst hC hCP
  obtain ⟨D, rfl⟩ : ∃ D, T = Z + D := ⟨T - Z, by ring⟩
  have hD : D ≠ 0 := by simpa using hTZ
  have hDr : D = 1 + a * (1 - u) - (1 - a) * u * v - 2 * Z := by linear_combination hT
  clear hT hTZ
  rw [show Z + D - Z = D by ring]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · field_simp
    linear_combination (4 * Z * u * (-Z + a) * (Z - 1)) * hDr + (4 * u * (2 * Z ^ 2 + Z * a * u * v
      - Z * a * u - Z * a - Z * u * v - Z + a * u)) * hz2
  · field_simp
    linear_combination (-4 * u * (-D ^ 3 - D ^ 2 * Z - D ^ 2 * a * u * v + D ^ 2 * a * u + D ^ 2 * u
      * v - D * Z ^ 2 + D * Z * a * u * v - D * Z * a * u + D * Z * a - D * Z * u * v + D * Z + D *
      a * u - D * a + Z ^ 3 - 3 * Z ^ 2 * a * u * v + 3 * Z ^ 2 * a * u - 2 * Z ^ 2 * a + 3 * Z ^ 2
      * u * v - 2 * Z ^ 2 + 3 * Z * a ^ 2 * u ^ 2 * v ^ 2 - 6 * Z * a ^ 2 * u ^ 2 * v + 3 * Z * a ^
      2 * u ^ 2 + 4 * Z * a ^ 2 * u * v - 4 * Z * a ^ 2 * u + Z * a ^ 2 - 6 * Z * a * u ^ 2 * v ^ 2
      + 6 * Z * a * u ^ 2 * v - 4 * Z * a * u + 3 * Z * a + 3 * Z * u ^ 2 * v ^ 2 - 4 * Z * u * v +
      Z + 3 * a ^ 2 * u ^ 2 * v - 3 * a ^ 2 * u ^ 2 - 3 * a ^ 2 * u * v + 4 * a ^ 2 * u - a ^ 2 - 3
      * a * u ^ 2 * v + 3 * a * u * v + a * u - a)) * hDr + (4 * u * (2 * Z ^ 2 - 5 * Z * a * u * v
      + 5 * Z * a * u - 3 * Z * a + 5 * Z * u * v - 3 * Z + 3 * a ^ 2 * u ^ 2 * v ^ 2 - 6 * a ^ 2 *
      u ^ 2 * v + 3 * a ^ 2 * u ^ 2 + 4 * a ^ 2 * u * v - 4 * a ^ 2 * u + a ^ 2 - 6 * a * u ^ 2 * v
      ^ 2 + 6 * a * u ^ 2 * v - 3 * a * u + 2 * a + 3 * u ^ 2 * v ^ 2 - 4 * u * v + 1)) * hz2
  · field_simp
    linear_combination (4 * u ^ 2 * (Z * a ^ 2 * u * v ^ 2 - 2 * Z * a ^ 2 * u * v + Z * a ^ 2 * u +
      Z * a ^ 2 * v - Z * a ^ 2 - 2 * Z * a * u * v ^ 2 + 2 * Z * a * u * v + Z * u * v ^ 2 - Z * v
      + a ^ 2 * u * v - a ^ 2 * u - a ^ 2 * v + a ^ 2 - a * u * v + a * v)) * hDr + (-4 * u ^ 2 * (a
      ^ 2 * u * v ^ 2 - 2 * a ^ 2 * u * v + a ^ 2 * u + a ^ 2 * v - a ^ 2 - 2 * a * u * v ^ 2 + 2 *
      a * u * v + u * v ^ 2 - v)) * hz2
  · field_simp
    linear_combination (4 * u * (-D * Z ^ 2 * δ - D * Z ^ 2 * ε - D * Z ^ 2 * γ + D * Z * a * δ * u
      * v - D * Z * a * δ * u + D * Z * a * δ + D * Z * a * ε * u * v - D * Z * a * ε * u + D * Z *
      a * ε + D * Z * a * γ * u * v - D * Z * a * γ * u + D * Z * a * γ - D * Z * δ * u * v + D * Z
      * δ - D * Z * ε * u * v + D * Z * ε - D * Z * γ * u * v + D * Z * γ + D * a * δ * u - D * a *
      δ + D * a * ε * u - D * a * ε + D * a * γ * u - D * a * γ + 2 * Z ^ 3 * δ + 2 * Z ^ 3 * ε + 2
      * Z ^ 3 * γ - 3 * Z ^ 2 * a * δ * u * v + 3 * Z ^ 2 * a * δ * u - 3 * Z ^ 2 * a * δ - 3 * Z ^
      2 * a * ε * u * v + 3 * Z ^ 2 * a * ε * u - 3 * Z ^ 2 * a * ε - 3 * Z ^ 2 * a * γ * u * v + 3
      * Z ^ 2 * a * γ * u - 3 * Z ^ 2 * a * γ + 3 * Z ^ 2 * δ * u * v - 3 * Z ^ 2 * δ + 3 * Z ^ 2 *
      ε * u * v - 3 * Z ^ 2 * ε + 3 * Z ^ 2 * γ * u * v - 3 * Z ^ 2 * γ + Z * a ^ 2 * δ * u ^ 2 * v
      ^ 2 - 2 * Z * a ^ 2 * δ * u ^ 2 * v + Z * a ^ 2 * δ * u ^ 2 + 2 * Z * a ^ 2 * δ * u * v - 2 *
      Z * a ^ 2 * δ * u + Z * a ^ 2 * δ + Z * a ^ 2 * ε * u ^ 2 * v ^ 2 - 2 * Z * a ^ 2 * ε * u ^ 2
      * v + Z * a ^ 2 * ε * u ^ 2 + 2 * Z * a ^ 2 * ε * u * v - 2 * Z * a ^ 2 * ε * u + Z * a ^ 2 *
      ε + Z * a ^ 2 * γ * u ^ 2 * v ^ 2 - 2 * Z * a ^ 2 * γ * u ^ 2 * v + Z * a ^ 2 * γ * u ^ 2 + 2
      * Z * a ^ 2 * γ * u * v - 2 * Z * a ^ 2 * γ * u + Z * a ^ 2 * γ - 2 * Z * a ^ 2 * u ^ 2 * v ^
      2 + 4 * Z * a ^ 2 * u ^ 2 * v - 2 * Z * a ^ 2 * u ^ 2 - 2 * Z * a ^ 2 * u * v + 2 * Z * a ^ 2
      * u - 2 * Z * a * δ * u ^ 2 * v ^ 2 + 2 * Z * a * δ * u ^ 2 * v - 4 * Z * a * δ * u + 4 * Z *
      a * δ - 2 * Z * a * ε * u ^ 2 * v ^ 2 + 2 * Z * a * ε * u ^ 2 * v - 4 * Z * a * ε * u + 4 * Z
      * a * ε - 2 * Z * a * γ * u ^ 2 * v ^ 2 + 2 * Z * a * γ * u ^ 2 * v - 4 * Z * a * γ * u + 4 *
      Z * a * γ + 4 * Z * a * u ^ 2 * v ^ 2 - 4 * Z * a * u ^ 2 * v + Z * δ * u ^ 2 * v ^ 2 - 2 * Z
      * δ * u * v + Z * δ + Z * ε * u ^ 2 * v ^ 2 - 2 * Z * ε * u * v + Z * ε + Z * γ * u ^ 2 * v ^
      2 - 2 * Z * γ * u * v + Z * γ - 2 * Z * u ^ 2 * v ^ 2 + 2 * Z * u * v + a ^ 2 * δ * u ^ 2 * v
      - a ^ 2 * δ * u ^ 2 - a ^ 2 * δ * u * v + 2 * a ^ 2 * δ * u - a ^ 2 * δ + a ^ 2 * ε * u ^ 2 *
      v - a ^ 2 * ε * u ^ 2 - a ^ 2 * ε * u * v + 2 * a ^ 2 * ε * u - a ^ 2 * ε + a ^ 2 * γ * u ^ 2
      * v - a ^ 2 * γ * u ^ 2 - a ^ 2 * γ * u * v + 2 * a ^ 2 * γ * u - a ^ 2 * γ - 2 * a ^ 2 * u ^
      2 * v + 2 * a ^ 2 * u ^ 2 + 2 * a ^ 2 * u * v - 2 * a ^ 2 * u - a * δ * u ^ 2 * v + a * δ * u
      * v + a * δ * u - a * δ - a * ε * u ^ 2 * v + a * ε * u * v + a * ε * u - a * ε - a * γ * u ^
      2 * v + a * γ * u * v + a * γ * u - a * γ + 2 * a * u ^ 2 * v - 2 * a * u * v)) * hDr + (-4 *
      u * (4 * Z ^ 2 * δ + 4 * Z ^ 2 * ε + 4 * Z ^ 2 * γ - 4 * Z * a * δ * u * v + 4 * Z * a * δ * u
      - 4 * Z * a * δ - 4 * Z * a * ε * u * v + 4 * Z * a * ε * u - 4 * Z * a * ε - 4 * Z * a * γ *
      u * v + 4 * Z * a * γ * u - 4 * Z * a * γ + 4 * Z * δ * u * v - 4 * Z * δ + 4 * Z * ε * u * v
      - 4 * Z * ε + 4 * Z * γ * u * v - 4 * Z * γ + a ^ 2 * δ * u ^ 2 * v ^ 2 - 2 * a ^ 2 * δ * u ^
      2 * v + a ^ 2 * δ * u ^ 2 + 2 * a ^ 2 * δ * u * v - 2 * a ^ 2 * δ * u + a ^ 2 * δ + a ^ 2 * ε
      * u ^ 2 * v ^ 2 - 2 * a ^ 2 * ε * u ^ 2 * v + a ^ 2 * ε * u ^ 2 + 2 * a ^ 2 * ε * u * v - 2 *
      a ^ 2 * ε * u + a ^ 2 * ε + a ^ 2 * γ * u ^ 2 * v ^ 2 - 2 * a ^ 2 * γ * u ^ 2 * v + a ^ 2 * γ
      * u ^ 2 + 2 * a ^ 2 * γ * u * v - 2 * a ^ 2 * γ * u + a ^ 2 * γ - 2 * a ^ 2 * u ^ 2 * v ^ 2 +
      4 * a ^ 2 * u ^ 2 * v - 2 * a ^ 2 * u ^ 2 - 2 * a ^ 2 * u * v + 2 * a ^ 2 * u - 2 * a * δ * u
      ^ 2 * v ^ 2 + 2 * a * δ * u ^ 2 * v - 2 * a * δ * u + 2 * a * δ - 2 * a * ε * u ^ 2 * v ^ 2 +
      2 * a * ε * u ^ 2 * v - 2 * a * ε * u + 2 * a * ε - 2 * a * γ * u ^ 2 * v ^ 2 + 2 * a * γ * u
      ^ 2 * v - 2 * a * γ * u + 2 * a * γ + 4 * a * u ^ 2 * v ^ 2 - 4 * a * u ^ 2 * v + δ * u ^ 2 *
      v ^ 2 - 2 * δ * u * v + δ + ε * u ^ 2 * v ^ 2 - 2 * ε * u * v + ε + γ * u ^ 2 * v ^ 2 - 2 * γ
      * u * v + γ - 2 * u ^ 2 * v ^ 2 + 2 * u * v)) * hz2
  · field_simp
    linear_combination (-4 * u * (-D ^ 3 * δ - D ^ 3 * ε - D ^ 3 * γ - D * Z ^ 2 * δ - D * Z ^ 2 * ε
      - D * Z ^ 2 * γ + D * Z * a * δ * u * v - D * Z * a * δ * u + D * Z * a * δ + D * Z * a * ε *
      u * v - D * Z * a * ε * u + D * Z * a * ε + D * Z * a * γ * u * v - D * Z * a * γ * u + D * Z
      * a * γ - D * Z * δ * u * v + D * Z * δ - D * Z * ε * u * v + D * Z * ε - D * Z * γ * u * v +
      D * Z * γ + D * a * δ * u - D * a * δ + D * a * ε * u - D * a * ε + D * a * γ * u - D * a * γ
      + 2 * Z ^ 3 * δ + 2 * Z ^ 3 * ε + 2 * Z ^ 3 * γ - 3 * Z ^ 2 * a * δ * u * v + 3 * Z ^ 2 * a *
      δ * u - 3 * Z ^ 2 * a * δ - 3 * Z ^ 2 * a * ε * u * v + 3 * Z ^ 2 * a * ε * u - 3 * Z ^ 2 * a
      * ε - 3 * Z ^ 2 * a * γ * u * v + 3 * Z ^ 2 * a * γ * u - 3 * Z ^ 2 * a * γ + 3 * Z ^ 2 * δ *
      u * v - 3 * Z ^ 2 * δ + 3 * Z ^ 2 * ε * u * v - 3 * Z ^ 2 * ε + 3 * Z ^ 2 * γ * u * v - 3 * Z
      ^ 2 * γ + Z * a ^ 2 * δ * u ^ 2 * v ^ 2 - 2 * Z * a ^ 2 * δ * u ^ 2 * v + Z * a ^ 2 * δ * u ^
      2 + 2 * Z * a ^ 2 * δ * u * v - 2 * Z * a ^ 2 * δ * u + Z * a ^ 2 * δ + Z * a ^ 2 * ε * u ^ 2
      * v ^ 2 - 2 * Z * a ^ 2 * ε * u ^ 2 * v + Z * a ^ 2 * ε * u ^ 2 + 2 * Z * a ^ 2 * ε * u * v -
      2 * Z * a ^ 2 * ε * u + Z * a ^ 2 * ε + Z * a ^ 2 * γ * u ^ 2 * v ^ 2 - 2 * Z * a ^ 2 * γ * u
      ^ 2 * v + Z * a ^ 2 * γ * u ^ 2 + 2 * Z * a ^ 2 * γ * u * v - 2 * Z * a ^ 2 * γ * u + Z * a ^
      2 * γ - 2 * Z * a ^ 2 * u ^ 2 * v ^ 2 + 4 * Z * a ^ 2 * u ^ 2 * v - 2 * Z * a ^ 2 * u ^ 2 - 2
      * Z * a ^ 2 * u * v + 2 * Z * a ^ 2 * u - 2 * Z * a * δ * u ^ 2 * v ^ 2 + 2 * Z * a * δ * u ^
      2 * v - 4 * Z * a * δ * u + 4 * Z * a * δ - 2 * Z * a * ε * u ^ 2 * v ^ 2 + 2 * Z * a * ε * u
      ^ 2 * v - 4 * Z * a * ε * u + 4 * Z * a * ε - 2 * Z * a * γ * u ^ 2 * v ^ 2 + 2 * Z * a * γ *
      u ^ 2 * v - 4 * Z * a * γ * u + 4 * Z * a * γ + 4 * Z * a * u ^ 2 * v ^ 2 - 4 * Z * a * u ^ 2
      * v + Z * δ * u ^ 2 * v ^ 2 - 2 * Z * δ * u * v + Z * δ + Z * ε * u ^ 2 * v ^ 2 - 2 * Z * ε *
      u * v + Z * ε + Z * γ * u ^ 2 * v ^ 2 - 2 * Z * γ * u * v + Z * γ - 2 * Z * u ^ 2 * v ^ 2 + 2
      * Z * u * v + a ^ 2 * δ * u ^ 2 * v - a ^ 2 * δ * u ^ 2 - a ^ 2 * δ * u * v + 2 * a ^ 2 * δ *
      u - a ^ 2 * δ + a ^ 2 * ε * u ^ 2 * v - a ^ 2 * ε * u ^ 2 - a ^ 2 * ε * u * v + 2 * a ^ 2 * ε
      * u - a ^ 2 * ε + a ^ 2 * γ * u ^ 2 * v - a ^ 2 * γ * u ^ 2 - a ^ 2 * γ * u * v + 2 * a ^ 2 *
      γ * u - a ^ 2 * γ - 2 * a ^ 2 * u ^ 2 * v + 2 * a ^ 2 * u ^ 2 + 2 * a ^ 2 * u * v - 2 * a ^ 2
      * u - a * δ * u ^ 2 * v + a * δ * u * v + a * δ * u - a * δ - a * ε * u ^ 2 * v + a * ε * u *
      v + a * ε * u - a * ε - a * γ * u ^ 2 * v + a * γ * u * v + a * γ * u - a * γ + 2 * a * u ^ 2
      * v - 2 * a * u * v)) * hDr + (4 * u * (4 * Z ^ 2 * δ + 4 * Z ^ 2 * ε + 4 * Z ^ 2 * γ - 4 * Z
      * a * δ * u * v + 4 * Z * a * δ * u - 4 * Z * a * δ - 4 * Z * a * ε * u * v + 4 * Z * a * ε *
      u - 4 * Z * a * ε - 4 * Z * a * γ * u * v + 4 * Z * a * γ * u - 4 * Z * a * γ + 4 * Z * δ * u
      * v - 4 * Z * δ + 4 * Z * ε * u * v - 4 * Z * ε + 4 * Z * γ * u * v - 4 * Z * γ + a ^ 2 * δ *
      u ^ 2 * v ^ 2 - 2 * a ^ 2 * δ * u ^ 2 * v + a ^ 2 * δ * u ^ 2 + 2 * a ^ 2 * δ * u * v - 2 * a
      ^ 2 * δ * u + a ^ 2 * δ + a ^ 2 * ε * u ^ 2 * v ^ 2 - 2 * a ^ 2 * ε * u ^ 2 * v + a ^ 2 * ε *
      u ^ 2 + 2 * a ^ 2 * ε * u * v - 2 * a ^ 2 * ε * u + a ^ 2 * ε + a ^ 2 * γ * u ^ 2 * v ^ 2 - 2
      * a ^ 2 * γ * u ^ 2 * v + a ^ 2 * γ * u ^ 2 + 2 * a ^ 2 * γ * u * v - 2 * a ^ 2 * γ * u + a ^
      2 * γ - 2 * a ^ 2 * u ^ 2 * v ^ 2 + 4 * a ^ 2 * u ^ 2 * v - 2 * a ^ 2 * u ^ 2 - 2 * a ^ 2 * u
      * v + 2 * a ^ 2 * u - 2 * a * δ * u ^ 2 * v ^ 2 + 2 * a * δ * u ^ 2 * v - 2 * a * δ * u + 2 *
      a * δ - 2 * a * ε * u ^ 2 * v ^ 2 + 2 * a * ε * u ^ 2 * v - 2 * a * ε * u + 2 * a * ε - 2 * a
      * γ * u ^ 2 * v ^ 2 + 2 * a * γ * u ^ 2 * v - 2 * a * γ * u + 2 * a * γ + 4 * a * u ^ 2 * v ^
      2 - 4 * a * u ^ 2 * v + δ * u ^ 2 * v ^ 2 - 2 * δ * u * v + δ + ε * u ^ 2 * v ^ 2 - 2 * ε * u
      * v + ε + γ * u ^ 2 * v ^ 2 - 2 * γ * u * v + γ - 2 * u ^ 2 * v ^ 2 + 2 * u * v)) * hz2

/-- Implicit differentiation of a product relation `f g = p` holding near `x`, to first and
second order. -/
private theorem deriv_mul_relation {f g p : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x)
    (hg : AnalyticAt ℂ g x) (h : ∀ᶠ y in 𝓝 x, f y * g y = p y) :
    deriv f x * g x + f x * deriv g x = deriv p x ∧
      deriv (deriv f) x * g x + 2 * (deriv f x * deriv g x) + f x * deriv (deriv g) x =
        deriv (deriv p) x := by
  have e1 : ∀ᶠ y in 𝓝 x, deriv (fun y => f y * g y) y =
      deriv f y * g y + f y * deriv g y := by
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with y hfy hgy
    exact deriv_mul hfy.differentiableAt hgy.differentiableAt
  have hfg : (fun y => f y * g y) =ᶠ[𝓝 x] p := h
  have d1 : deriv p =ᶠ[𝓝 x] fun y => deriv f y * g y + f y * deriv g y :=
    hfg.deriv.symm.trans e1
  refine ⟨d1.self_of_nhds.symm, ?_⟩
  rw [d1.deriv_eq]
  have hd := ((hf.deriv.differentiableAt.hasDerivAt.mul hg.differentiableAt.hasDerivAt).add
    (hf.differentiableAt.hasDerivAt.mul hg.deriv.differentiableAt.hasDerivAt))
  refine Eq.trans ?_ hd.deriv.symm
  ring

/-- First and second derivatives of `σ ↦ A sin²σ`. -/
private theorem deriv_const_mul_sin_sq (A x : ℂ) :
    deriv (fun σ => A * Complex.sin σ ^ 2) x = A * (2 * Complex.sin x * Complex.cos x) ∧
      deriv (deriv fun σ => A * Complex.sin σ ^ 2) x =
        A * (2 * (Complex.cos x ^ 2 - Complex.sin x ^ 2)) := by
  have h1 : ∀ y, HasDerivAt (fun σ => A * Complex.sin σ ^ 2)
      (A * (2 * Complex.sin y * Complex.cos y)) y := fun y => by
    convert ((Complex.hasDerivAt_sin y).pow 2).const_mul A using 1
    simp only [Nat.cast_ofNat]; ring
  have e : deriv (fun σ => A * Complex.sin σ ^ 2) =
      fun y => A * (2 * Complex.sin y * Complex.cos y) := funext fun y => (h1 y).deriv
  refine ⟨(h1 x).deriv, ?_⟩
  rw [e]
  have h2 := (((Complex.hasDerivAt_sin x).const_mul 2).mul
    (Complex.hasDerivAt_cos x)).const_mul A
  refine h2.deriv.trans ?_
  ring

/-- First and second derivatives of `σ ↦ A cos²σ`. -/
private theorem deriv_const_mul_cos_sq (A x : ℂ) :
    deriv (fun σ => A * Complex.cos σ ^ 2) x = A * (-2 * Complex.cos x * Complex.sin x) ∧
      deriv (deriv fun σ => A * Complex.cos σ ^ 2) x =
        A * (-2 * (Complex.cos x ^ 2 - Complex.sin x ^ 2)) := by
  have h1 : ∀ y, HasDerivAt (fun σ => A * Complex.cos σ ^ 2)
      (A * (-2 * Complex.cos y * Complex.sin y)) y := fun y => by
    convert ((Complex.hasDerivAt_cos y).pow 2).const_mul A using 1
    simp only [Nat.cast_ofNat]; ring
  have e : deriv (fun σ => A * Complex.cos σ ^ 2) =
      fun y => A * (-2 * Complex.cos y * Complex.sin y) := funext fun y => (h1 y).deriv
  refine ⟨(h1 x).deriv, ?_⟩
  rw [e]
  have h2 := (((Complex.hasDerivAt_cos x).const_mul (-2)).mul
    (Complex.hasDerivAt_sin x)).const_mul A
  refine h2.deriv.trans ?_
  ring

end KernelAngles

open KernelAngles in
/-- DLMF 31.10.7–31.10.8 (**31.10.8 sign corrected**): with
`cos²θ = zt/a`, `sin²θ cos²φ = -(z-a)(t-a)/(a(1-a))`, `sin²θ sin²φ = (z-1)(t-1)/(1-a)`
(31.10.7 squared), a kernel `𝒦(z, t)` with `(𝒟_z - 𝒟_t)𝒦 = 0` satisfies, as a function of
`(θ, φ)`, `sin²θ(𝒦_θθ + ((1-2γ)tan θ + 2(δ+ε-1/2)cot θ)𝒦_θ - 4αβ𝒦) + 𝒦_φφ
+ ((2δ-1)cot φ - (2ε-1)tan φ)𝒦_φ = 0`. Stronger than DLMF, which assumes Fuchs's relation
`α + β + 1 = γ + δ + ε` and `a ∉ {0, 1}`; only the first two relations 31.10.7 are used. -/
@[dlmf 31.10.E7, dlmf 31.10.E8]
theorem heun_kernel_typeI_angles' {a α β γ δ ε : ℂ}
    {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω) {Z T : ℂ → ℂ → ℂ} {K : ℂ → ℂ → ℂ}
    (hZT : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => (Z x.1 x.2, T x.1 x.2)) Ω)
    (hrel : ∀ x ∈ Ω, Z x.1 x.2 * T x.1 x.2 = a * Complex.cos x.1 ^ 2 ∧
      (Z x.1 x.2 - 1) * (T x.1 x.2 - 1) = (1 - a) * Complex.sin x.1 ^ 2 * Complex.sin x.2 ^ 2)
    (hreg : ∀ x ∈ Ω, Z x.1 x.2 ≠ T x.1 x.2 ∧ Complex.sin x.1 ≠ 0 ∧ Complex.cos x.1 ≠ 0 ∧
      Complex.sin x.2 ≠ 0 ∧ Complex.cos x.2 ≠ 0)
    (hK : AnalyticOnNhd ℂ (fun y : ℂ × ℂ => K y.1 y.2)
      ((fun x : ℂ × ℂ => (Z x.1 x.2, T x.1 x.2)) '' Ω))
    (hKpde : ∀ x ∈ Ω, heunOperator a α β γ δ ε (fun z' => K z' (T x.1 x.2)) (Z x.1 x.2) =
      heunOperator a α β γ δ ε (K (Z x.1 x.2)) (T x.1 x.2)) :
    ∀ x ∈ Ω, let 𝒦 : ℂ → ℂ → ℂ := fun θ φ => K (Z θ φ) (T θ φ)
      Complex.sin x.1 ^ 2 * (deriv (deriv fun θ => 𝒦 θ x.2) x.1 +
          ((1 - 2 * γ) * Complex.tan x.1 + 2 * (δ + ε - 1 / 2) * Complex.cot x.1) *
            deriv (fun θ => 𝒦 θ x.2) x.1 - 4 * α * β * 𝒦 x.1 x.2) +
        deriv (deriv (𝒦 x.1)) x.2 +
        ((2 * δ - 1) * Complex.cot x.2 - (2 * ε - 1) * Complex.tan x.2) * deriv (𝒦 x.1) x.2 =
        0 := by
  rintro ⟨θ, φ⟩ hx 𝒦
  simp only [𝒦]
  obtain ⟨hZT0, hs, hc, hsp, hcp⟩ := hreg _ hx
  obtain ⟨r1, r2⟩ := hrel _ hx
  have hP := hKpde _ hx
  dsimp only at hZT0 hs hc hsp hcp r1 r2 hP ⊢
  -- analyticity along the coordinate lines
  have hA := hZT _ hx
  have hZa : AnalyticAt ℂ (fun x : ℂ × ℂ => Z x.1 x.2) (θ, φ) := analyticAt_fst.comp hA
  have hTa : AnalyticAt ℂ (fun x : ℂ × ℂ => T x.1 x.2) (θ, φ) := analyticAt_snd.comp hA
  have hθc : AnalyticAt ℂ (fun σ : ℂ => (σ, φ)) θ := analyticAt_id.prod analyticAt_const
  have hφc : AnalyticAt ℂ (fun σ : ℂ => (θ, σ)) φ := analyticAt_const.prod analyticAt_id
  have hZθ : AnalyticAt ℂ (fun σ => Z σ φ) θ :=
    AnalyticAt.comp (f := fun σ => (σ, φ)) hZa hθc
  have hTθ : AnalyticAt ℂ (fun σ => T σ φ) θ :=
    AnalyticAt.comp (f := fun σ => (σ, φ)) hTa hθc
  have hZφ : AnalyticAt ℂ (fun σ => Z θ σ) φ :=
    AnalyticAt.comp (f := fun σ => (θ, σ)) hZa hφc
  have hTφ : AnalyticAt ℂ (fun σ => T θ σ) φ :=
    AnalyticAt.comp (f := fun σ => (θ, σ)) hTa hφc
  have hΩθ : ∀ᶠ σ in 𝓝 θ, (σ, φ) ∈ Ω := hθc.continuousAt.preimage_mem_nhds (hΩ.mem_nhds hx)
  have hΩφ : ∀ᶠ σ in 𝓝 φ, (θ, σ) ∈ Ω := hφc.continuousAt.preimage_mem_nhds (hΩ.mem_nhds hx)
  -- implicit differentiation of the relations 31.10.7
  obtain ⟨A1, A2⟩ := deriv_mul_relation hZθ hTθ (p := fun σ => a * Complex.cos σ ^ 2)
    (hΩθ.mono fun σ h => (hrel _ h).1)
  obtain ⟨B1, B2⟩ := deriv_mul_relation (f := fun σ => Z σ φ - 1) (g := fun σ => T σ φ - 1)
    (hZθ.sub analyticAt_const) (hTθ.sub analyticAt_const)
    (p := fun σ => ((1 - a) * Complex.sin φ ^ 2) * Complex.sin σ ^ 2)
    (hΩθ.mono fun σ h => (hrel _ h).2.trans (by ring))
  obtain ⟨C1, C2⟩ := deriv_mul_relation hZφ hTφ (p := fun _ => a * Complex.cos θ ^ 2)
    (hΩφ.mono fun σ h => (hrel _ h).1)
  obtain ⟨D1, D2⟩ := deriv_mul_relation (f := fun σ => Z θ σ - 1) (g := fun σ => T θ σ - 1)
    (hZφ.sub analyticAt_const) (hTφ.sub analyticAt_const)
    (p := fun σ => ((1 - a) * Complex.sin θ ^ 2) * Complex.sin σ ^ 2)
    (hΩφ.mono fun σ h => (hrel _ h).2.trans (by ring))
  have hc0 : deriv (fun _ : ℂ => a * Complex.cos θ ^ 2) = fun _ => 0 :=
    funext fun _ => deriv_const _ _
  rw [hc0, deriv_const] at C2
  rw [hc0] at C1
  rw [(deriv_const_mul_cos_sq a θ).1] at A1
  rw [(deriv_const_mul_cos_sq a θ).2] at A2
  rw [(deriv_const_mul_sin_sq _ θ).1] at B1
  rw [(deriv_const_mul_sin_sq _ θ).2] at B2
  rw [(deriv_const_mul_sin_sq _ φ).1] at D1
  rw [(deriv_const_mul_sin_sq _ φ).2] at D2
  simp only [deriv_sub_const_fun, deriv_sub_const] at B1 B2 D1 D2
  -- the second-order chain rule
  have hKa : AnalyticAt ℂ (fun y : ℂ × ℂ => K y.1 y.2) (Z θ φ, T θ φ) := hK _ ⟨(θ, φ), hx, rfl⟩
  have hF : ContDiffAt ℂ 2 (fun x : ℂ × ℂ × ℂ => K x.1 x.2.1) (Z θ φ, T θ φ, 0) := by
    have h := AnalyticAt.comp (g := fun y : ℂ × ℂ => K y.1 y.2)
      (f := fun x : ℂ × ℂ × ℂ => (x.1, x.2.1)) (x := (Z θ φ, T θ φ, 0)) hKa
      (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd))
    exact h.contDiffAt
  have hev : ∀ {f : ℂ → ℂ} {y : ℂ}, AnalyticAt ℂ f y →
      ∀ᶠ σ in 𝓝 y, HasDerivAt f (deriv f σ) σ := fun h =>
    h.eventually_analyticAt.mono fun σ h' => h'.differentiableAt.hasDerivAt
  have h0 : ∀ y : ℂ, ∀ᶠ σ in 𝓝 y, HasDerivAt (fun _ : ℂ => (0 : ℂ)) ((fun _ => (0 : ℂ)) σ) σ :=
    fun y => Eventually.of_forall fun σ => hasDerivAt_const σ 0
  have Dθ := Complex.deriv_comp_three (𝒦 := fun u v _ => K u v) (X := fun σ => Z σ φ)
    (Y := fun σ => T σ φ) (Z := fun _ => 0) (s := θ) hF (hev hZθ) (hev hTθ) (h0 θ)
    hZθ.deriv.differentiableAt.hasDerivAt hTθ.deriv.differentiableAt.hasDerivAt
    (hasDerivAt_const θ (0 : ℂ))
  have Dφ := Complex.deriv_comp_three (𝒦 := fun u v _ => K u v) (X := fun σ => Z θ σ)
    (Y := fun σ => T θ σ) (Z := fun _ => 0) (s := φ) hF (hev hZφ) (hev hTφ) (h0 φ)
    hZφ.deriv.differentiableAt.hasDerivAt hTφ.deriv.differentiableAt.hasDerivAt
    (hasDerivAt_const φ (0 : ℂ))
  have Dc := Complex.deriv_coord_three (𝒦 := fun u v _ => K u v) hF
  beta_reduce at Dθ Dφ Dc
  simp only [heunOperator] at hP
  have e1 : deriv (fun z' => K z' (T θ φ)) (Z θ φ) = _ := Dc.1
  have e2 : deriv (deriv fun z' => K z' (T θ φ)) (Z θ φ) = _ := Dc.2.1
  have e3 : deriv (K (Z θ φ)) (T θ φ) = _ := Dc.2.2.1
  have e4 : deriv (deriv (K (Z θ φ))) (T θ φ) = _ := Dc.2.2.2.1
  rw [e1, e2, e3, e4] at hP
  rw [Dθ.1, Dθ.2, Dφ.1, Dφ.2]
  simp only [Complex.tan_eq_sin_div_cos, Complex.cot_eq_cos_div_sin]
  set F3 := fun x : ℂ × ℂ × ℂ => K x.1 x.2.1
  set p3 : ℂ × ℂ × ℂ := (Z θ φ, T θ φ, 0)
  set Zt := deriv (fun σ => Z σ φ) θ
  set Tt := deriv (fun σ => T σ φ) θ
  set Zp := deriv (fun σ => Z θ σ) φ
  set Tp := deriv (fun σ => T θ σ) φ
  set s := Complex.sin θ
  set c := Complex.cos θ
  set s' := Complex.sin φ
  set c' := Complex.cos φ
  set Z0 := Z θ φ
  set T0 := T θ φ
  obtain ⟨zt, hzt⟩ : ∃ w, Zt = c * s * w := ⟨Zt / (c * s), by field_simp⟩
  obtain ⟨tt, htt⟩ : ∃ w, Tt = c * s * w := ⟨Tt / (c * s), by field_simp⟩
  obtain ⟨zp, hzp⟩ : ∃ w, Zp = c' * s' * w := ⟨Zp / (c' * s'), by field_simp⟩
  obtain ⟨tp, htp⟩ : ∃ w, Tp = c' * s' * w := ⟨Tp / (c' * s'), by field_simp⟩
  rw [hzt, htt] at A1 B1 A2 B2
  rw [hzp, htp] at C1 D1 C2 D2
  rw [hzt, htt, hzp, htp]
  have hcs := mul_ne_zero hc hs
  have hcs' := mul_ne_zero hcp hsp
  have a1 : zt * T0 + Z0 * tt = -2 * a :=
    mul_left_cancel₀ hcs (by linear_combination A1)
  have b1 : zt * (T0 - 1) + (Z0 - 1) * tt = 2 * (1 - a) * s' ^ 2 :=
    mul_left_cancel₀ hcs (by linear_combination B1)
  have a2 : deriv (deriv fun σ => Z σ φ) θ * T0 + 2 * (c ^ 2 * s ^ 2 * zt * tt) +
      Z0 * deriv (deriv fun σ => T σ φ) θ = -2 * a * (c ^ 2 - s ^ 2) := by
    linear_combination A2
  have b2 : deriv (deriv fun σ => Z σ φ) θ * (T0 - 1) + 2 * (c ^ 2 * s ^ 2 * zt * tt) +
      (Z0 - 1) * deriv (deriv fun σ => T σ φ) θ =
        2 * (1 - a) * (c ^ 2 - s ^ 2) * s' ^ 2 := by
    linear_combination B2
  have c1 : zp * T0 + Z0 * tp = 0 := mul_left_cancel₀ hcs' (by linear_combination C1)
  have d1 : zp * (T0 - 1) + (Z0 - 1) * tp = 2 * (1 - a) * s ^ 2 :=
    mul_left_cancel₀ hcs' (by linear_combination D1)
  have c2 : deriv (deriv fun σ => Z θ σ) φ * T0 + 2 * (c' ^ 2 * s' ^ 2 * zp * tp) +
      Z0 * deriv (deriv fun σ => T θ σ) φ = 0 := by
    linear_combination C2
  have d2 : deriv (deriv fun σ => Z θ σ) φ * (T0 - 1) + 2 * (c' ^ 2 * s' ^ 2 * zp * tp) +
      (Z0 - 1) * deriv (deriv fun σ => T θ σ) φ = 2 * (1 - a) * s ^ 2 * (c' ^ 2 - s' ^ 2) := by
    linear_combination D2
  have hC : c ^ 2 = 1 - s ^ 2 := by linear_combination Complex.sin_sq_add_cos_sq θ
  have hCP : c' ^ 2 = 1 - s' ^ 2 := by linear_combination Complex.sin_sq_add_cos_sq φ
  have hTZ : T0 - Z0 ≠ 0 := sub_ne_zero.2 (Ne.symm hZT0)
  obtain ⟨Ezz, Ett, Ezt, Ez, Et⟩ := coefficient_identities (γ := γ) (δ := δ) (ε := ε) hTZ hC
    hCP r1 (by linear_combination r2) a1 b1 a2 b2 c1 d1 c2 d2
  have key1 : ∀ w, ((1 - 2 * γ) * (s / c) + 2 * (δ + ε - 1 / 2) * (c / s)) * (c * s * w) =
      ((1 - 2 * γ) * s ^ 2 + (2 * δ + 2 * ε - 1) * c ^ 2) * w := fun w => by
    field_simp
  have key2 : ∀ w, ((2 * δ - 1) * (c' / s') - (2 * ε - 1) * (s' / c')) * (c' * s' * w) =
      ((2 * δ - 1) * c' ^ 2 - (2 * ε - 1) * s' ^ 2) * w := fun w => by
    field_simp
  have eK : 4 * s ^ 2 / (T0 - Z0) * (T0 - Z0) = 4 * s ^ 2 := by field_simp
  set H11 := fderiv ℂ (fderiv ℂ F3) p3 (1, 0, 0) (1, 0, 0)
  set H22 := fderiv ℂ (fderiv ℂ F3) p3 (0, 1, 0) (0, 1, 0)
  set H12 := fderiv ℂ (fderiv ℂ F3) p3 (1, 0, 0) (0, 1, 0)
  set g1 := fderiv ℂ F3 p3 (1, 0, 0)
  set g2 := fderiv ℂ F3 p3 (0, 1, 0)
  linear_combination H11 * Ezz + H22 * Ett + 2 * H12 * Ezt + g1 * Ez + g2 * Et +
    s ^ 2 * key1 (zt * g1 + tt * g2) + key2 (zp * g1 + tp * g2) +
    4 * s ^ 2 / (T0 - Z0) * hP + α * β * K Z0 T0 * eK

end DLMF.Heun
