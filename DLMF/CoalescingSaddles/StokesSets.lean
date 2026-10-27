/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.CoalescingSaddles.Basic
public import Mathlib.Basic.Real.Sign
public import DLMF.CoalescingSaddles.BifurcationSets

/-!
# Stokes sets (DLMF §36.5)

Statements acquired from the NIST DLMF (version 1.2.8), checked 2026-10-26.

The Stokes sets are defined in `DLMF.CoalescingSaddles.Basic` (`cuspoidStokesSet`,
`umbilicStokesSet` and their complex–complex variants) by the exponential dominance condition
36.5.1 together with a connecting path of constant `Re Φ`. This file proves the fold case
(§36.5(ii), `K = 1`, in the form of the dominance condition for complex `x`) and states the
parametrizations 36.5.2–36.5.21 of the cusp, swallowtail, elliptic umbilic and hyperbolic umbilic
Stokes sets. The cusp case 36.5.2 is proved (necessity by elimination from the critical-point
equations; sufficiency by an explicit level curve of `Re Φ₂` joining the real saddle to a complex
one); the others are admitted. All of them were checked numerically at sample points (the real
parts of `Φ` at the real and the complex critical point agree to working precision).

Notation: the swallowtail coordinates `(x, y, z)` are `(x 0, x 1, x 2)`; `σ = Real.sign z`.
The decimal values 36.5.5 (`B_±`) and `X₁, Y₁, X₂, Y₂` are excluded as numerical; where DLMF
uses `Y₁` or `X₂` as a threshold the statement asserts the existence of the threshold.
-/

@[expose] public noncomputable section

open Complex Set
open scoped Real

namespace DLMF.CoalescingSaddles

/-! ### Fold (`K = 1`) -/

lemma s36a_re_eq_zero_iff_sq {w : ℂ} : w.re = 0 ↔ (w ^ 2).im = 0 ∧ (w ^ 2).re ≤ 0 := by
  rw [sq, Complex.mul_im, Complex.mul_re]
  constructor
  · intro h; rw [h]; constructor
    · ring
    · nlinarith [sq_nonneg w.im]
  · rintro ⟨h1, h2⟩
    have : w.re * w.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · rw [h] at h2; nlinarith [sq_nonneg w.re]

/-- The fold Stokes set (DLMF §36.5(ii), `K = 1`). For complex `x ≠ 0` the two critical points of
`Φ₁(t; x) = t³ + xt` are `±t` with `3t² = -x`, and the exponential dominance condition 36.5.1,
`Re(Φ₁(t) - Φ₁(-t)) = 0`, holds exactly when `x³` is real and nonnegative, that is on the three
rays `ph x ∈ {0, ±2π/3}`. DLMF's Stokes set consists of the rays `ph x = ±2π/3`; on the
positive real axis (where `Ψ₁` is a multiple of `Ai` of positive argument) only the subdominant
saddle contributes, so no Stokes switching occurs there. -/
@[dlmf 36.5.ii]
theorem fold_dominance_iff {x t : ℂ} (ht : 3 * t ^ 2 + x = 0) :
    ((t ^ 3 + x * t) - ((-t) ^ 3 + x * (-t))).re = 0 ↔ (x ^ 3).im = 0 ∧ 0 ≤ (x ^ 3).re := by
  have hx : x = -3 * t ^ 2 := by linear_combination ht
  have hdiff : (t ^ 3 + x * t) - ((-t) ^ 3 + x * (-t)) = (4 / 3 : ℝ) * (x * t) := by
    rw [hx]; push_cast; ring
  have hsq : (x * t) ^ 2 = ((-1 / 3 : ℝ) : ℂ) * x ^ 3 := by
    rw [hx]; push_cast; ring
  rw [hdiff, Complex.re_ofReal_mul, mul_eq_zero, s36a_re_eq_zero_iff_sq, hsq,
    Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · norm_num at h
    · constructor
      · simpa using h1
      · linarith
  · rintro ⟨h1, h2⟩
    right; constructor
    · rw [h1, mul_zero]
    · nlinarith

/-! ### Cusp (`K = 2`) -/

/-- The cusp potential `Φ₂(w; x) = w⁴ + x₂w² + x₁w`. -/
lemma q2s_cusp_pot (x : Fin 2 → ℝ) (w : ℂ) :
    cuspoidPotential 2 w x = w ^ 4 + x 1 * w ^ 2 + x 0 * w := by
  simp [cuspoidPotential, Fin.sum_univ_two]; ring

/-- `√27 = 3√3`. -/
lemma q2s_sqrt27 : Real.sqrt 27 = 3 * Real.sqrt 3 := by
  rw [show (27 : ℝ) = 3 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]

/-- The necessity half of 36.5.2: a saddle connection between a real and a nonreal critical point
of the cusp potential forces `y³ = (27/4)(√27 - 5)x²`. -/
lemma q2s_cusp_stokes_mp {x : Fin 2 → ℝ} (hx : x ∈ cuspoidStokesSet 2) :
    x 1 ^ 3 = 27 / 4 * (Real.sqrt 27 - 5) * x 0 ^ 2 := by
  obtain ⟨t, μ, hμ, hd1, hd2, -, γ, -, hγ0, hγ1, hγ⟩ := hx
  have hre := hγ 1 ⟨zero_le_one, le_rfl⟩
  rw [hγ1] at hre
  rw [(s36a_cusp_derivs x _).1] at hd1 hd2
  simp only [q2s_cusp_pot] at hre
  set a := μ.re
  set b := μ.im
  set y := x 1
  set x0 := x 0
  have hμe : μ = a + b * I := (re_add_im μ).symm
  have E1 : 4 * t ^ 3 + 2 * y * t + x0 = 0 := by
    have := congrArg Complex.re hd1
    simpa [pow_succ] using this
  have R : 4 * (a ^ 3 - 3 * a * b ^ 2) + 2 * y * a + x0 = 0 := by
    have := congrArg Complex.re hd2
    rw [hμe] at this
    simp [pow_succ, mul_re, mul_im] at this
    linear_combination this
  have Im0 : b * (12 * a ^ 2 - 4 * b ^ 2 + 2 * y) = 0 := by
    have := congrArg Complex.im hd2
    rw [hμe] at this
    simp [pow_succ, mul_re, mul_im] at this
    linear_combination this
  have M : 12 * a ^ 2 - 4 * b ^ 2 + 2 * y = 0 := (mul_eq_zero.mp Im0).resolve_left hμ
  have hP : (2 * a + t) * ((a - t) ^ 2 + b ^ 2) = 0 := by
    linear_combination (-1 / 4 : ℝ) * R + (1 / 4 : ℝ) * E1 + ((a - t) / 4) * M
  have hb2 : 0 < b ^ 2 := by positivity
  have ha : 2 * a + t = 0 := by
    rcases mul_eq_zero.mp hP with h | h
    · exact h
    · nlinarith [sq_nonneg (a - t)]
  have hRe : (a ^ 2 - b ^ 2) ^ 2 - 4 * a ^ 2 * b ^ 2 + y * (a ^ 2 - b ^ 2) + x0 * a =
      t ^ 4 + y * t ^ 2 + x0 * t := by
    rw [hμe] at hre
    simp [pow_succ, mul_re, mul_im] at hre
    linear_combination hre
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs32 : 3 / 2 < Real.sqrt 3 := by
    rw [show (3 / 2 : ℝ) = Real.sqrt (9 / 4) by
      rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hQ : (y - (3 + 3 * Real.sqrt 3) * t ^ 2) * (y - (3 - 3 * Real.sqrt 3) * t ^ 2) = 0 := by
    have ha' : a = -t / 2 := by linarith
    have hb' : b ^ 2 = 3 * a ^ 2 + y / 2 := by linarith
    have hx0 : x0 = -4 * t ^ 3 - 2 * y * t := by linarith
    rw [ha'] at hb' hRe
    rw [hb', hx0] at hRe
    linear_combination (-4 : ℝ) * hRe + (-9 * t ^ 4) * hs
  rcases mul_eq_zero.mp hQ with h | h
  · have hy : y = (3 + 3 * Real.sqrt 3) * t ^ 2 := by linarith
    have hx0 : x0 = -(10 + 6 * Real.sqrt 3) * t ^ 3 := by rw [hy] at E1; linarith
    rw [q2s_sqrt27, hy, hx0]
    linear_combination (-54 * t ^ 6 * (13 * Real.sqrt 3 + 21)) * hs
  · exfalso
    have hy : y = (3 - 3 * Real.sqrt 3) * t ^ 2 := by linarith
    have ha' : a = -t / 2 := by linarith
    have hb' : b ^ 2 = t ^ 2 * (9 / 4 - 3 / 2 * Real.sqrt 3) := by
      rw [hy, ha'] at M; linarith
    nlinarith [sq_nonneg t]


/-- The sufficiency half of 36.5.2: on the curve `y³ = (27/4)(√27 - 5)x²`, `x ≠ 0`, an explicit
path of constant `Re Φ₂` joins the real critical point to a nonreal one. -/
lemma q2s_cusp_stokes_mpr {x : Fin 2 → ℝ} (hx : x 0 ≠ 0)
    (h : x 1 ^ 3 = 27 / 4 * (Real.sqrt 27 - 5) * x 0 ^ 2) : x ∈ cuspoidStokesSet 2 := by
  rw [q2s_sqrt27] at h
  set y := x 1 with hydef
  set x0 := x 0 with hx0def
  set s := Real.sqrt 3 with hsdef
  have hs : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hs53 : 5 / 3 < s := by nlinarith
  set k : ℝ := 3 + 3 * s with hk
  set m : ℝ := 10 + 6 * s with hm
  have hk0 : 0 < k := by positivity
  have hm0 : 0 < m := by positivity
  have hy0 : 0 < y := by
    by_contra hneg
    push Not at hneg
    have h1 : y ^ 3 ≤ 0 := by nlinarith [sq_nonneg y]
    have h2 : 0 < 27 / 4 * (3 * s - 5) * x0 ^ 2 := by
      have : 0 < x0 ^ 2 := by positivity
      have : 0 < 3 * s - 5 := by linarith
      positivity
    linarith
  set t : ℝ := -(k * x0) / (m * y) with ht
  have hyt : y = k * t ^ 2 := by
    rw [ht, div_pow, neg_sq, mul_pow, mul_pow]
    field_simp
    linear_combination (m ^ 2) * h + (x0 ^ 2 * (702 * s + 1134)) * hs
  have hxt : x0 = -m * t ^ 3 := by
    have e : t ^ 3 = t * (y / k) := by rw [hyt]; field_simp
    rw [e, ht]; field_simp
  have ht0 : t ≠ 0 := by
    rintro h0; apply hx; rw [hxt, h0]; ring
  -- the nonreal critical point `μ = t(-1/2 + iβ)`
  set β : ℝ := Real.sqrt ((9 + 6 * s) / 4) with hβ
  have hβ2 : β ^ 2 = (9 + 6 * s) / 4 := Real.sq_sqrt (by positivity)
  have hβ0 : 0 < β := Real.sqrt_pos.mpr (by positivity)
  set μ : ℂ := (t : ℂ) * (-1 / 2 + β * I) with hμ
  have hμim : μ.im = t * β := by simp [hμ]
  -- the path
  set B : ℝ → ℝ := fun u => 6 * u ^ 2 + k with hB
  set D : ℝ → ℝ := fun u => 32 * u ^ 4 + 8 * k * u ^ 2 + 4 * m * u + k ^ 2 + 4 * (1 + k - m)
    with hD
  set W : ℝ → ℝ := fun u => (B u - Real.sqrt (D u)) / 2 with hW
  have hDfac : ∀ u, D u = (2 * u + 1) ^ 2 * (8 * u ^ 2 - 8 * u + 12 + 6 * s) := by
    intro u; simp only [hD, hk, hm]; linear_combination (9 : ℝ) * hs
  have hD0 : ∀ u, 0 ≤ D u := by
    intro u; rw [hDfac]
    exact mul_nonneg (sq_nonneg _) (by nlinarith [sq_nonneg (2 * u - 1)])
  have hBD : ∀ u, B u ^ 2 - D u = 4 * ((u - 1) ^ 2 * (u ^ 2 + 2 * u + 6 + 3 * s)) := by
    intro u; simp only [hB, hD, hk, hm]; ring_nf
  have hW0 : ∀ u, 0 ≤ W u := by
    intro u
    have hB0 : 0 ≤ B u := by simp only [hB]; positivity
    have h1 : Real.sqrt (D u) ≤ B u := by
      rw [Real.sqrt_le_left hB0]
      have := hBD u
      nlinarith [sq_nonneg (u - 1), sq_nonneg (u + 1)]
    simp only [hW]; linarith
  have hWq : ∀ u, W u ^ 2 - B u * W u + (B u ^ 2 - D u) / 4 = 0 := by
    intro u
    have := Real.sq_sqrt (hD0 u)
    simp only [hW]; linear_combination (1 / 4 : ℝ) * this
  set γ : ℝ → ℂ := fun r => (t : ℂ) * ((1 - 3 / 2 * r : ℝ) + I * (Real.sqrt (W (1 - 3 / 2 * r))))
    with hγ
  refine ⟨t, μ, by rw [hμim]; exact mul_ne_zero ht0 hβ0.ne', ?_, ?_, ?_, γ, ?_, ?_, ?_, ?_⟩
  · rw [(s36a_cusp_derivs x _).1, ← hydef, ← hx0def, hyt, hxt]
    push_cast; simp only [hk, hm]; push_cast; ring
  · rw [(s36a_cusp_derivs x _).1, ← hydef, ← hx0def, hyt, hxt, hμ]
    have hβc : (β : ℂ) ^ 2 = (9 + 6 * s) / 4 := by exact_mod_cast hβ2
    push_cast; simp only [hk, hm]; push_cast
    linear_combination (6 * (t : ℂ) ^ 3 - 4 * (t : ℂ) ^ 3 * I * β) * hβc +
      (t : ℂ) ^ 3 * (-6 * (β : ℂ) ^ 2 + 4 * (β : ℂ) ^ 3 * I) * I_sq
  · intro he
    have := congrArg Complex.im he
    rw [hμim] at this
    simp at this
    rcases this with h1 | h1
    · exact ht0 h1
    · exact hβ0.ne' h1
  · refine Continuous.continuousOn ?_
    simp only [hγ, hW, hB, hD]
    fun_prop
  · have hB1 : 0 ≤ B 1 := by simp only [hB]; positivity
    have hD1 : D 1 = B 1 ^ 2 := by have := hBD 1; norm_num at this; linarith
    have hW1 : W 1 = 0 := by simp only [hW]; rw [hD1, Real.sqrt_sq hB1]; ring
    simp only [hγ]
    norm_num [hW1]
  · have hDm : D (-1 / 2) = 0 := by rw [hDfac]; norm_num
    have hWm : W (-1 / 2) = (9 + 6 * s) / 4 := by
      simp only [hW]; rw [hDm, Real.sqrt_zero]; simp only [hB, hk]; ring
    simp only [hγ, hμ]
    rw [show (1 - 3 / 2 * 1 : ℝ) = -1 / 2 by norm_num, hWm, ← hβ]
    push_cast; ring
  · intro r _
    set u : ℝ := 1 - 3 / 2 * r with hu
    set w : ℝ := Real.sqrt (W u) with hw
    have hw2 : w ^ 2 = W u := Real.sq_sqrt (hW0 u)
    have hC : (B u ^ 2 - D u) / 4 = u ^ 4 + k * u ^ 2 - m * u - (1 + k - m) := by
      simp only [hB, hD]; ring
    have hq : W u ^ 2 - (6 * u ^ 2 + k) * W u + (u ^ 4 + k * u ^ 2 - m * u - (1 + k - m)) = 0 := by
      have := hWq u; rw [hC] at this; simpa only [hB] using this
    simp only [hγ, q2s_cusp_pot]
    rw [← hydef, ← hx0def, ← hu, ← hw]
    simp [pow_succ, mul_re, mul_im]
    rw [hyt, hxt]
    linear_combination (t ^ 4) * hq +
      t ^ 4 * ((w ^ 2 + W u) - 6 * u ^ 2 - k) * hw2

/-- The cusp Stokes set (DLMF 36.5.2): away from the cusp point, `x ∈ S` exactly when
`y³ = (27/4)(√27 - 5) x²` (with `x = x 0`, `y = x 1`). The decimal value `1.32403` of the
coefficient is not acquired. -/
@[dlmf 36.5.E2]
theorem cuspoidStokesSet_two {x : Fin 2 → ℝ} (hx : x 0 ≠ 0) :
    x ∈ cuspoidStokesSet 2 ↔ x 1 ^ 3 = 27 / 4 * (Real.sqrt 27 - 5) * x 0 ^ 2 :=
  ⟨q2s_cusp_stokes_mp, q2s_cusp_stokes_mpr hx⟩

/-! ### Swallowtail (`K = 3`) -/

/-- The swallowtail Stokes set in the plane `z = 0` (DLMF 36.5.3, 36.5.4): for `y ≠ 0` the point
`(x, y, 0)` lies on the Stokes set exactly when `x = B_± |y|^{4/3}`, where
`B_± = swallowtailStokesB x_±` and `x_±` are the two smallest positive roots of the quintic
36.5.4 (a positive root `ξ` with at most one smaller positive root). -/
@[dlmf 36.5.E3, dlmf 36.5.E4]
theorem cuspoidStokesSet_three_z_zero {x y : ℝ} (hy : y ≠ 0) :
    ![x, y, 0] ∈ cuspoidStokesSet 3 ↔
      ∃ ξ : ℝ, 0 < ξ ∧ swallowtailStokesQuintic ξ = 0 ∧
        {ξ' : ℝ | 0 < ξ' ∧ ξ' < ξ ∧ swallowtailStokesQuintic ξ' = 0}.ncard ≤ 1 ∧
        x = swallowtailStokesB ξ * |y| ^ ((4 : ℝ) / 3) := by
  sorry

/-- The swallowtail Stokes set for `z ≠ 0` (DLMF 36.5.6–36.5.9): in the scaled coordinates
`X = x/z²`, `Y = y/|z|^{3/2}` (36.5.6) the Stokes set is generated by `X = X(u)` (36.5.7) where
`u > 0` solves 36.5.8 with `t` given by 36.5.9 (its radicand nonnegative). For `z < 0` the
solutions generate the Stokes set provided `|Y| > (2/5)^{1/2}`, as DLMF states; for smaller `|Y|`
36.5.8 has spurious roots (checked numerically). For `z > 0` the solutions generate the first
sheet and, for `|Y| > Y₁`, the second sheet. -/
@[dlmf 36.5.E6, dlmf 36.5.E7, dlmf 36.5.E8, dlmf 36.5.E9]
theorem cuspoidStokesSet_three_param {y z u : ℝ} (hz : z ≠ 0) (hu : 0 < u)
    (hrad : 0 ≤ |y / |z| ^ ((3 : ℝ) / 2)| / (10 * u) - u ^ 2 - 3 / 10 * Real.sign z)
    (heq : swallowtailStokesEq u (y / |z| ^ ((3 : ℝ) / 2)) (Real.sign z) = 0)
    (hneg : z < 0 → Real.sqrt (2 / 5) < |y / |z| ^ ((3 : ℝ) / 2)|) :
    ![swallowtailStokesX u (y / |z| ^ ((3 : ℝ) / 2)) (Real.sign z) * z ^ 2, y, z] ∈
      cuspoidStokesSet 3 := by
  sorry

/-- The second sheet of the swallowtail Stokes set for `z > 0` and small `|Y|` (DLMF 36.5.10):
there is a threshold `Y₁ > 0` (DLMF: `|Y₁| = 6.81337`) such that for `|Y| < Y₁` the sheet is
generated by 36.5.7 with `u > 0` a root of `160u⁶ + 40u⁴ = Y²`. This part of the Stokes set
connects two complex critical points (it lies inside the bifurcation set). -/
@[dlmf 36.5.E10]
theorem cuspoidComplexStokesSet_three_param :
    ∃ Y₁ : ℝ, 0 < Y₁ ∧ ∀ y z u : ℝ, 0 < z → 0 < u → |y / z ^ ((3 : ℝ) / 2)| < Y₁ →
      160 * u ^ 6 + 40 * u ^ 4 = (y / z ^ ((3 : ℝ) / 2)) ^ 2 →
      ![swallowtailStokesX u (y / z ^ ((3 : ℝ) / 2)) 1 * z ^ 2, y, z] ∈
        cuspoidComplexStokesSet 3 := by
  sorry

/-! ### Elliptic umbilic -/

/-- The elliptic umbilic Stokes set (DLMF 36.5.11–36.5.14): the sheet symmetric under `y ↦ -y`
is given, for `z ≠ 0`, by
`x/z² = -1 - 12u² + 8u - |y/z²|(1/3 - u)/(u(2/3 - u))^{1/2}` (36.5.11), where `0 < u < 1/6`
(36.5.14) is a root of
`8u³ - 4u² - |y/(3z²)|(u/(2/3 - u))^{1/2} = y²/(6wz⁴) - 2w³ - 2w²` (36.5.12) with `w` from
36.5.13 (`ellipticStokesW`). The other two sheets are its rotations by `±2π/3`
(36.2.26). -/
@[dlmf 36.5.E11, dlmf 36.5.E12, dlmf 36.5.E14, dlmf 36.5.iii]
theorem umbilicStokesSet_elliptic_param {y z u : ℝ} (hz : z ≠ 0) (hu : 0 < u)
    (hu' : u < 1 / 6)
    (heq : 8 * u ^ 3 - 4 * u ^ 2 - |y / (3 * z ^ 2)| * Real.sqrt (u / (2 / 3 - u)) =
      y ^ 2 / (6 * ellipticStokesW u (y / z ^ 2) * z ^ 4) -
        2 * ellipticStokesW u (y / z ^ 2) ^ 3 - 2 * ellipticStokesW u (y / z ^ 2) ^ 2) :
    (z ^ 2 * (-1 - 12 * u ^ 2 + 8 * u -
        |y / z ^ 2| * (1 / 3 - u) / Real.sqrt (u * (2 / 3 - u))), y, z) ∈
      umbilicStokesSet ellipticUmbilicPotential := by
  sorry

/-! ### Hyperbolic umbilic -/

/-- The hyperbolic umbilic Stokes set (DLMF 36.5.15–36.5.21), in the coordinates
`X = (x - y)/z²`, `Y = 1/2 + (x + y)/z²` (36.5.15), with `Y(u, X)` and `f(u, X)` from 36.5.16.
There is a threshold `X₂ > 0` (DLMF: `X₂ = 0.45148`) such that

* for `|X| > X₂` the Stokes set is `Y = Y(u, |X|)` (36.5.17), with `u > 1/3` a root of
  `f(u, X) = f(1/3 - u, X)` (36.5.18); this part connects two complex saddles;
* for `|X| < X₂` it is `Y = Y(-u, -|X|)` (36.5.19), with `u > 0` a root of
  `f(-u, X) = X²/(12w) + 4w³ - 2w²` (36.5.20), `w` from 36.5.21 (`hyperbolicStokesW`). -/
@[dlmf 36.5.E15, dlmf 36.5.E17, dlmf 36.5.E18, dlmf 36.5.E19, dlmf 36.5.E20,
  dlmf 36.5.iii]
theorem umbilicStokesSet_hyperbolic_param :
    ∃ X₂ : ℝ, 0 < X₂ ∧
      (∀ x y z u : ℝ, z ≠ 0 → X₂ < |(x - y) / z ^ 2| → 1 / 3 < u →
        hyperbolicStokesF u ((x - y) / z ^ 2) =
          hyperbolicStokesF (1 / 3 - u) ((x - y) / z ^ 2) →
        1 / 2 + (x + y) / z ^ 2 = hyperbolicStokesY u |(x - y) / z ^ 2| →
        (x, y, z) ∈ umbilicComplexStokesSet hyperbolicUmbilicPotential) ∧
      (∀ x y z u : ℝ, z ≠ 0 → |(x - y) / z ^ 2| < X₂ → 0 < u →
        hyperbolicStokesF (-u) ((x - y) / z ^ 2) =
          ((x - y) / z ^ 2) ^ 2 / (12 * hyperbolicStokesW u ((x - y) / z ^ 2)) +
            4 * hyperbolicStokesW u ((x - y) / z ^ 2) ^ 3 -
            2 * hyperbolicStokesW u ((x - y) / z ^ 2) ^ 2 →
        1 / 2 + (x + y) / z ^ 2 = hyperbolicStokesY (-u) (-|(x - y) / z ^ 2|) →
        (x, y, z) ∈ umbilicStokesSet hyperbolicUmbilicPotential) := by
  sorry

end DLMF.CoalescingSaddles
