/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Coulomb.Energy.Basic
public import DLMF.Confluent.Coulomb
public import DLMF.Bessel.RegularizedSeries
public import DLMFMathlib.Analysis.ODE.PowerSeriesUniqueness
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Algebra.Order.Ring.Star

/-!
# The regular Coulomb function `f(ε,ℓ;r)` as an entire function (DLMF 33.14.1, 33.19.1)

For every real `ε` the function `f(ε,ℓ;·)` is the restriction to `ℝ` of the real part of an
entire function `q2e_Phi ε ℓ` (the Kummer form 33.14.5 with `κ = coulombKappa ε 1` for `ε ≠ 0`,
the confluent form `(2z)^{ℓ+1} ₀F̃₁(;2ℓ+2;-2z)` for `ε = 0`). This entire function satisfies
the Coulomb equation 33.14.1 (from the Coulomb wave equation 33.2.1 by the substitution
`ρ = -iz/κ`, `η = -iκ`, resp. from the `₀F₁` equation), and its Taylor coefficients satisfy the
recurrence 33.19.2, which gives the power series 33.19.1.

## Main results

* `q2e_coulombf_eq_re`: `f(ε,ℓ;r) = Re q2e_Phi ε ℓ r`.
* `q2e_Phi_ode`: the equation 33.14.1 for `q2e_Phi ε ℓ` at `z ≠ 0`.
* `q2e_hasSum_of_ode`: an entire solution `z^{ℓ+1} ψ(z)` of 33.14.1 with `ψ(0) = α₀` has the
  power series `∑ α_k z^{k+ℓ+1}`.
* `q2e_Phi_hasSum`: the complex power series 33.19.1.
* `q2e_alpha_raise`, `q2e_alpha_lower`: ladder relations between the coefficients `α_k` for
  consecutive `ℓ`; `q2e_Phi_raise`, `q2e_Phi_three_term`: the recurrences 33.17.3 and 33.17.1
  for `q2e_Phi`, proved by comparing Taylor coefficients.
-/

@[expose] public section

open Complex Filter
open scoped Real Nat Topology

noncomputable section

namespace DLMF.Coulomb

open DLMF.Confluent

/-! ### `κ` -/

/-- For `x > 0`, `x^{-1/2} > 0`. -/
lemma c33b_rpow_neg_half_pos {x : ℝ} (hx : 0 < x) : 0 < x ^ (-(1 / 2 : ℝ)) :=
  Real.rpow_pos_of_pos hx _

/-- `κ ≠ 0` for `ε ≠ 0`. -/
theorem coulombKappa_ne_zero {ε : ℝ} (hε : ε ≠ 0) (r : ℝ) : coulombKappa ε r ≠ 0 := by
  unfold coulombKappa
  rcases lt_or_gt_of_ne hε with h | h
  · have hp := c33b_rpow_neg_half_pos (neg_pos.mpr h)
    simp only [h, ite_true]
    split_ifs
    · exact_mod_cast hp.ne'
    · exact_mod_cast (neg_neg_of_pos hp).ne
  · have hp := c33b_rpow_neg_half_pos h
    simp only [not_lt.mpr h.le, ite_false]
    exact mul_ne_zero I_ne_zero (by exact_mod_cast hp.ne')

/-- `κ² = -1/ε` for `ε ≠ 0` (DLMF 33.14.6). -/
theorem coulombKappa_sq {ε : ℝ} (hε : ε ≠ 0) (r : ℝ) : coulombKappa ε r ^ 2 = -(1 / ε : ℂ) := by
  have key : ∀ x : ℝ, 0 < x → (x ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / x := by
    intro x hx
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num [Real.rpow_neg_one]
  unfold coulombKappa
  rcases lt_or_gt_of_ne hε with h | h
  · have hk := key (-ε) (neg_pos.mpr h)
    simp only [h, ite_true]
    split_ifs
    · rw [← Complex.ofReal_pow, hk]; push_cast; field_simp
    · rw [← Complex.ofReal_pow, neg_sq, hk]; push_cast; field_simp
  · have hk := key ε h
    simp only [not_lt.mpr h.le, ite_false]
    rw [mul_pow, I_sq, ← Complex.ofReal_pow, hk]; push_cast; ring

/-- `κ(ε,r) = ±κ(ε,1)`. -/
theorem q2e_coulombKappa_eq_or (ε r : ℝ) :
    coulombKappa ε r = coulombKappa ε 1 ∨ coulombKappa ε r = -coulombKappa ε 1 := by
  unfold coulombKappa
  split_ifs <;> simp_all

/-! ### The entire functions -/

/-- **The sign of `κ` is immaterial** in 33.14.5 (DLMF §33.14(ii)), by Kummer's transformation
`M(a,b,z) = e^z M(b-a,b,-z)`. -/
@[dlmf 33.14.ii]
theorem coulombfKummer_neg (κ : ℂ) (ℓ : ℕ) (r : ℝ) :
    coulombfKummer (-κ) ℓ r = coulombfKummer κ ℓ r := by
  unfold coulombfKummer
  rw [kummerM_kummer_transform (two_mul_nat_add_two_ne_neg_nat ℓ) (a := (ℓ : ℂ) + 1 - κ),
    show 2 * (ℓ : ℂ) + 2 - (ℓ + 1 - κ) = ℓ + 1 - -κ by ring,
    show -(2 * (r : ℂ) / κ) = 2 * r / -κ by ring]
  have he : exp (-(r : ℂ) / κ) * exp (2 * r / κ) = exp (-(r : ℂ) / -κ) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [← he]
  ring

/-- The complex extension of the Kummer form 33.14.5, as a function of complex `z`. -/
def q2e_PhiK (κ : ℂ) (ℓ : ℕ) (z : ℂ) : ℂ :=
  (2 * z) ^ (ℓ + 1) * exp (-z / κ) * kummerM (ℓ + 1 - κ) (2 * ℓ + 2) (2 * z / κ) / (2 * ℓ + 1)!

/-- The Kummer form of `f(ε,ℓ;r)` is the restriction of its complex extension `q2e_PhiK`. -/
lemma q2e_coulombfKummer_eq (κ : ℂ) (ℓ : ℕ) (r : ℝ) : coulombfKummer κ ℓ r = q2e_PhiK κ ℓ r :=
  rfl

/-- `M(a, 2ℓ+2, ·)` is entire. -/
lemma q2e_kummerM_differentiable (a : ℂ) (ℓ : ℕ) :
    Differentiable ℂ (kummerM a (2 * ℓ + 2)) := fun z =>
  ((hasFPowerSeriesOnBall_kummerM (a := a) (two_mul_nat_add_two_ne_neg_nat ℓ)).analyticAt_of_mem
    (by simp)).differentiableAt

/-- For `κ ≠ 0`, the complex Kummer form is `(2iκ)^{ℓ+1}/(2ℓ+1)!` times the Coulomb wave at `η =
-iκ`, `ρ = -iz/κ`. -/
lemma q2e_PhiK_eq_coulombWave {κ : ℂ} (hκ : κ ≠ 0) (ℓ : ℕ) (z : ℂ) :
    q2e_PhiK κ ℓ z = (2 * I * κ) ^ (ℓ + 1) / (2 * ℓ + 1)! *
      coulombWave ℓ (-I * κ) (-I / κ * z) := by
  unfold q2e_PhiK coulombWave
  have h1 : -I * (-I / κ * z) = -z / κ := by
    field_simp; ring_nf; rw [I_sq]; ring
  have h2 : 2 * I * (-I / κ * z) = 2 * z / κ := by
    field_simp; ring_nf; rw [I_sq]; ring
  have h3 : (ℓ : ℂ) + 1 - I * (-I * κ) = ℓ + 1 - κ := by
    ring_nf; rw [I_sq]; ring
  have h4 : (2 * I * κ) ^ (ℓ + 1) * (-I / κ * z) ^ (ℓ + 1) = (2 * z) ^ (ℓ + 1) := by
    rw [← mul_pow]; congr 1; field_simp; ring_nf; rw [I_sq]; ring
  rw [h1, h2, h3]
  linear_combination (exp (-z / κ) * kummerM (ℓ + 1 - κ) (2 * ℓ + 2) (2 * z / κ) /
    (2 * ℓ + 1)!) * h4.symm


/-- Function form of `q2e_PhiK_eq_coulombWave`. -/
lemma q2e_PhiK_fun {κ : ℂ} (hκ : κ ≠ 0) (ℓ : ℕ) :
    q2e_PhiK κ ℓ = fun z => (2 * I * κ) ^ (ℓ + 1) / (2 * ℓ + 1)! *
      coulombWave ℓ (-I * κ) (-I / κ * z) := funext (q2e_PhiK_eq_coulombWave hκ ℓ)

/-- Derivative of the complex Kummer form, through the Coulomb wave derivative. -/
lemma q2e_hasDerivAt_PhiK {κ : ℂ} (hκ : κ ≠ 0) (ℓ : ℕ) (z : ℂ) :
    HasDerivAt (q2e_PhiK κ ℓ) ((2 * I * κ) ^ (ℓ + 1) / (2 * ℓ + 1)! *
      (-I / κ * coulombWaveDeriv ℓ (-I * κ) (-I / κ * z))) z := by
  rw [q2e_PhiK_fun hκ]
  have h := (hasDerivAt_coulombWave ℓ (-I * κ) (-I / κ * z)).comp z
    ((hasDerivAt_id z).const_mul (-I / κ))
  simp only [mul_one] at h
  exact (h.const_mul _).congr_deriv (by ring)

/-- Function form of the derivative of the complex Kummer form. -/
lemma q2e_deriv_PhiK {κ : ℂ} (hκ : κ ≠ 0) (ℓ : ℕ) :
    deriv (q2e_PhiK κ ℓ) = fun z => (2 * I * κ) ^ (ℓ + 1) / (2 * ℓ + 1)! *
      (-I / κ * coulombWaveDeriv ℓ (-I * κ) (-I / κ * z)) :=
  funext fun z => (q2e_hasDerivAt_PhiK hκ ℓ z).deriv

/-- For `κ ≠ 0`, `ε = -1/κ²` and `z ≠ 0`, the complex Kummer form solves `Φ'' + (ε + 2/z -
ℓ(ℓ+1)/z²) Φ = 0` (DLMF 33.14.1). -/
lemma q2e_PhiK_ode {κ : ℂ} (hκ : κ ≠ 0) (ℓ : ℕ) {ε : ℂ} (hε : ε = -1 / κ ^ 2) {z : ℂ}
    (hz : z ≠ 0) :
    HasDerivAt (deriv (q2e_PhiK κ ℓ))
      (-(ε + 2 / z - ℓ * (ℓ + 1) / z ^ 2) * q2e_PhiK κ ℓ z) z := by
  have hcz : -I / κ * z ≠ 0 := mul_ne_zero (div_ne_zero (neg_ne_zero.mpr I_ne_zero) hκ) hz
  rw [q2e_deriv_PhiK hκ]
  have h := (hasDerivAt_coulombWaveDeriv ℓ (-I * κ) hcz).comp z
    ((hasDerivAt_id z).const_mul (-I / κ))
  simp only [mul_one] at h
  refine ((h.const_mul (-I / κ)).const_mul _).congr_deriv ?_
  rw [q2e_PhiK_eq_coulombWave hκ, hε]
  field_simp
  ring_nf
  simp only [I_sq]
  ring


/-- The confluent (`ε = 0`) form `(2z)^{ℓ+1} ₀F̃₁(;2ℓ+2;-2z)` of 33.14.5. -/
def q2e_Phi0 (ℓ : ℕ) (z : ℂ) : ℂ :=
  (2 * z) ^ (ℓ + 1) * regularizedHGFun 0 {(2 * ℓ + 2 : ℂ)} (-(2 * z))

/-- `d/dz (2z)ⁿ = 2n (2z)^{n-1}`. -/
lemma q2e_hasDerivAt_pow2 (n : ℕ) (z : ℂ) :
    HasDerivAt (fun z : ℂ => (2 * z) ^ n) (2 * n * (2 * z) ^ (n - 1)) z := by
  have h := (hasDerivAt_pow n (2 * z)).comp z ((hasDerivAt_id z).const_mul 2)
  simp only [mul_one] at h
  exact h.congr_deriv (by ring)

/-- `d/dz ₀F̃₁(;c;-2z) = -2 ₀F̃₁(;c+1;-2z)`. -/
lemma q2e_hasDerivAt_F (c : ℂ) (z : ℂ) :
    HasDerivAt (fun z : ℂ => regularizedHGFun 0 {c} (-(2 * z)))
      (-2 * regularizedHGFun 0 {c + 1} (-(2 * z))) z := by
  have h := (DLMF.Bessel.hasDerivAt_regularized0F1 c (-(2 * z))).comp z
    (((hasDerivAt_id z).const_mul 2).neg)
  simp only [mul_one, id, Multiset.empty_eq_zero] at h
  exact h.congr_deriv (by ring)

/-- Derivative of the confluent form `(2z)^{ℓ+1} ₀F̃₁(;2ℓ+2;-2z)`. -/
lemma q2e_hasDerivAt_Phi0 (ℓ : ℕ) (z : ℂ) :
    HasDerivAt (q2e_Phi0 ℓ) (2 * (ℓ + 1) * (2 * z) ^ ℓ *
      regularizedHGFun 0 {(2 * ℓ + 2 : ℂ)} (-(2 * z)) -
      2 * (2 * z) ^ (ℓ + 1) * regularizedHGFun 0 {(2 * ℓ + 2 : ℂ) + 1} (-(2 * z))) z := by
  have h := (q2e_hasDerivAt_pow2 (ℓ + 1) z).mul (q2e_hasDerivAt_F (2 * ℓ + 2) z)
  refine h.congr_deriv ?_
  simp only [Nat.add_sub_cancel]; push_cast; ring

/-- Function form of the derivative of the confluent form. -/
lemma q2e_deriv_Phi0 (ℓ : ℕ) :
    deriv (q2e_Phi0 ℓ) = fun z => 2 * (ℓ + 1) * (2 * z) ^ ℓ *
      regularizedHGFun 0 {(2 * ℓ + 2 : ℂ)} (-(2 * z)) -
      2 * (2 * z) ^ (ℓ + 1) * regularizedHGFun 0 {(2 * ℓ + 2 : ℂ) + 1} (-(2 * z)) :=
  funext fun z => (q2e_hasDerivAt_Phi0 ℓ z).deriv

/-- For `z ≠ 0`, the confluent form solves the `ε = 0` Coulomb equation `Φ'' + (2/z - ℓ(ℓ+1)/z²) Φ =
0`. -/
lemma q2e_Phi0_ode (ℓ : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (deriv (q2e_Phi0 ℓ))
      (-((0 : ℂ) + 2 / z - ℓ * (ℓ + 1) / z ^ 2) * q2e_Phi0 ℓ z) z := by
  rw [q2e_deriv_Phi0]
  have h : HasDerivAt (fun w : ℂ => 2 * ((ℓ : ℂ) + 1) * ((2 * w) ^ ℓ *
      regularizedHGFun 0 {(2 * ℓ + 2 : ℂ)} (-(2 * w))) - 2 * ((2 * w) ^ (ℓ + 1) *
      regularizedHGFun 0 {(2 * ℓ + 2 : ℂ) + 1} (-(2 * w)))) _ z :=
    (((q2e_hasDerivAt_pow2 ℓ z).mul (q2e_hasDerivAt_F (2 * ℓ + 2) z)).const_mul
      (2 * ((ℓ : ℂ) + 1))).sub
      (((q2e_hasDerivAt_pow2 (ℓ + 1) z).mul (q2e_hasDerivAt_F (2 * ℓ + 2 + 1) z)).const_mul 2)
  convert h using 1
  · funext w; ring
  symm
  have hc := DLMF.Bessel.regularized0F1_contiguous (2 * ℓ + 2 : ℂ) (-(2 * z))
  simp only [Multiset.empty_eq_zero] at hc
  unfold q2e_Phi0
  generalize regularizedHGFun 0 {(2 * ℓ + 2 : ℂ)} (-(2 * z)) = F0 at hc ⊢
  generalize regularizedHGFun 0 {(2 * ℓ + 2 : ℂ) + 1} (-(2 * z)) = F1 at hc ⊢
  generalize regularizedHGFun 0 {(2 * ℓ + 2 : ℂ) + 1 + 1} (-(2 * z)) = F2 at hc ⊢
  rcases ℓ with _ | m
  · simp only [Nat.cast_zero, Nat.zero_sub, pow_zero] at hc ⊢
    field_simp
    linear_combination (4 * z ^ 2) * hc
  · simp only [Nat.add_sub_cancel] at hc ⊢
    push_cast at hc ⊢
    field_simp
    linear_combination (8 * z ^ 3 * z ^ m * 2 ^ m) * hc


/-- The second derivative of an entire function is smooth. -/
lemma q2e_contDiffAt_deriv2 {Φ : ℂ → ℂ} (hΦd : Differentiable ℂ Φ) (n : ℕ) (x : ℂ) :
    ContDiffAt ℂ n (deriv (deriv Φ)) x :=
  ((hΦd.contDiff (n := ((n : ℕ) : WithTop ℕ∞) + 1 + 1)).deriv'.deriv').contDiffAt

/-- The Taylor coefficients of a solution `z^{ℓ+1} ψ(z)` of 33.14.1 that is entire satisfy the
recurrence 33.19.2: `Φ⁽ⁿ⁾(0) = 0` for `n ≤ ℓ` and `Φ⁽ℓ⁺¹⁺ʲ⁾(0) = (ℓ+1+j)! α_j`. -/
lemma q2e_iteratedDeriv_of_ode {ε : ℝ} {ℓ : ℕ} {Φ ψ : ℂ → ℂ} (hψ : Differentiable ℂ ψ)
    (hΦ : Φ = fun z => z ^ (ℓ + 1) * ψ z)
    (hode : ∀ z : ℂ, z ≠ 0 → HasDerivAt (deriv Φ)
      (-((ε : ℂ) + 2 / z - ℓ * (ℓ + 1) / z ^ 2) * Φ z) z)
    (h0 : ψ 0 = coulombAlpha ε ℓ 0) :
    (∀ n, n < ℓ + 1 → iteratedDeriv n Φ 0 = 0) ∧
      ∀ j, iteratedDeriv (ℓ + 1 + j) Φ 0 = (ℓ + 1 + j)! * coulombAlpha ε ℓ j := by
  have hΦd : Differentiable ℂ Φ := by
    rw [hΦ]; exact (differentiable_id.pow _).mul hψ
  have hc : ∀ (f : ℂ → ℂ), Differentiable ℂ f → ∀ n : ℕ, ContDiffAt ℂ n f 0 :=
    fun f hf n => (hf.contDiff).contDiffAt
  set L : ℂ := (ℓ : ℂ) * (ℓ + 1)
  -- the polynomial form of the equation
  have hH : (fun z : ℂ => z ^ 2 * deriv (deriv Φ) z + z ^ 2 * ((ε : ℂ) * Φ z) +
      z ^ 1 * (2 * Φ z) - z ^ 0 * (L * Φ z)) = fun _ => 0 := by
    funext w
    by_cases hw : w = 0
    · have : Φ 0 = 0 := by rw [hΦ]; simp
      rw [hw, this]; simp
    · rw [(hode w hw).deriv]
      field_simp
      ring
  set D : ℕ → ℂ := fun n => iteratedDeriv n Φ 0 with hD
  have hrec : ∀ k : ℕ, ((k : ℂ) + 2) * (k + 1) * D (k + 2) + (k + 2) * (k + 1) * ε * D k +
      2 * (k + 2) * D (k + 1) - L * D (k + 2) = 0 := by
    intro k
    have h := congrArg (fun f => iteratedDeriv (k + 2) f 0) hH
    simp only [iteratedDeriv_const, add_eq_zero] at h
    have hΦ'' : Differentiable ℂ (deriv (deriv Φ)) := fun x =>
      (q2e_contDiffAt_deriv2 hΦd 1 x).differentiableAt (by norm_num)
    rw [iteratedDeriv_fun_sub (hc _ (by fun_prop) _) (hc _ (by fun_prop) _),
      iteratedDeriv_fun_add (hc _ (by fun_prop) _) (hc _ (by fun_prop) _),
      iteratedDeriv_fun_add (hc _ (by fun_prop) _) (hc _ (by fun_prop) _),
      ODE.iteratedDeriv_pow_mul_zero (hc _ hΦ'' _),
      ODE.iteratedDeriv_pow_mul_zero (hc _ (by fun_prop) _),
      ODE.iteratedDeriv_pow_mul_zero (hc _ (by fun_prop) _),
      ODE.iteratedDeriv_pow_mul_zero (hc _ (by fun_prop) _),
      iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
      iteratedDeriv_const_mul_field] at h
    simp only [Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega, Nat.sub_zero,
      ← iteratedDeriv_succ'] at h
    simp only [Nat.descFactorial, hD] at h ⊢
    push_cast at h ⊢
    simp only [and_false, ↓reduceIte] at h
    linear_combination h
  have hDψ : ∀ n, D n = n.descFactorial (ℓ + 1) * iteratedDeriv (n - (ℓ + 1)) ψ 0 := by
    intro n; simp only [hD]; rw [hΦ]; exact ODE.iteratedDeriv_pow_mul_zero (hc _ hψ _) _
  have hlow : ∀ n, n < ℓ + 1 → D n = 0 := by
    intro n hn; rw [hDψ, Nat.descFactorial_eq_zero_iff_lt.mpr hn]; simp
  have hmain : ∀ j, D (ℓ + 1 + j) = (ℓ + 1 + j)! * coulombAlpha ε ℓ j ∧
      D (ℓ + 1 + (j + 1)) = (ℓ + 1 + (j + 1))! * coulombAlpha ε ℓ (j + 1) := by
    intro j
    induction j with
    | zero =>
      have h1 : D (ℓ + 1) = (ℓ + 1)! * coulombAlpha ε ℓ 0 := by
        rw [hDψ, Nat.descFactorial_self, Nat.sub_self, iteratedDeriv_zero, h0]
      refine ⟨by simpa using h1, ?_⟩
      have hr := hrec ℓ
      rw [hlow ℓ (by omega), show ℓ + 1 = ℓ + 1 from rfl] at hr
      rw [show ℓ + 1 + (0 + 1) = ℓ + 2 by ring]
      rw [h1] at hr
      have hl : ((ℓ : ℂ) + 1) ≠ 0 := by norm_cast
      rw [show coulombAlpha ε ℓ 1 = -coulombAlpha ε ℓ 0 / (ℓ + 1) from rfl,
        Nat.factorial_succ (ℓ + 1)]
      simp only [L] at hr
      push_cast at hr ⊢
      rw [mul_div_assoc', eq_div_iff hl]
      linear_combination hr / 2
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      have hr := hrec (ℓ + 1 + j)
      rw [show ℓ + 1 + j + 1 = ℓ + 1 + (j + 1) by ring, ih.1, ih.2] at hr
      rw [show ℓ + 1 + j + 2 = ℓ + 1 + (j + 1 + 1) by ring] at hr
      have hne : ((j : ℂ) + 2) * ((j : ℂ) + 2 + 2 * ℓ + 1) ≠ 0 := by norm_cast
      rw [coulombAlpha, show ℓ + 1 + (j + 1 + 1) = (ℓ + 1 + j + 1) + 1 by ring,
        Nat.factorial_succ (ℓ + 1 + j + 1), Nat.factorial_succ (ℓ + 1 + j)]
      rw [show ℓ + 1 + (j + 1) = ℓ + 1 + j + 1 by ring, Nat.factorial_succ (ℓ + 1 + j)] at hr
      rw [show ℓ + 1 + (j + 1 + 1) = ℓ + 1 + j + 1 + 1 by ring] at hr
      simp only [L] at hr
      push_cast at hr ⊢
      rw [mul_div_assoc', eq_div_iff hne]
      linear_combination hr
  exact ⟨hlow, fun j => (hmain j).1⟩

/-- The power series 33.19.1 in `ℂ` for an entire solution `z^{ℓ+1} ψ(z)` of 33.14.1 with
`ψ(0) = α₀`. -/
lemma q2e_hasSum_of_ode {ε : ℝ} {ℓ : ℕ} {Φ ψ : ℂ → ℂ} (hψ : Differentiable ℂ ψ)
    (hΦ : Φ = fun z => z ^ (ℓ + 1) * ψ z)
    (hode : ∀ z : ℂ, z ≠ 0 → HasDerivAt (deriv Φ)
      (-((ε : ℂ) + 2 / z - ℓ * (ℓ + 1) / z ^ 2) * Φ z) z)
    (h0 : ψ 0 = coulombAlpha ε ℓ 0) (z : ℂ) :
    HasSum (fun k => (coulombAlpha ε ℓ k : ℂ) * z ^ (k + ℓ + 1)) (Φ z) := by
  have hΦd : Differentiable ℂ Φ := by
    rw [hΦ]; exact (differentiable_id.pow _).mul hψ
  obtain ⟨hlow, hmain⟩ := q2e_iteratedDeriv_of_ode hψ hΦ hode h0
  have hT := Complex.hasSum_taylorSeries_of_entire hΦd 0 z
  have hS := (hasSum_nat_add_iff' (ℓ + 1)).mpr hT
  rw [Finset.sum_eq_zero (fun i hi => by
    rw [hlow i (Finset.mem_range.mp hi), smul_zero,
      smul_zero]),
    sub_zero] at hS
  convert hS using 1
  swap
  · simp
  funext k
  rw [show k + (ℓ + 1) = ℓ + 1 + k by ring, hmain k,
    smul_eq_mul, smul_eq_mul, show k + ℓ + 1 = ℓ + 1 + k by ring]
  have : ((ℓ + 1 + k)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp


/-! ### The unified entire function -/

/-- The entire function whose restriction to `ℝ` has real part `f(ε,ℓ;·)`. -/
def q2e_Phi (ε : ℝ) (ℓ : ℕ) (z : ℂ) : ℂ :=
  if ε = 0 then q2e_Phi0 ℓ z else q2e_PhiK (coulombKappa ε 1) ℓ z

/-- `q2e_Phi ε ℓ z = z^{ℓ+1} q2e_Psi ε ℓ z`. -/
def q2e_Psi (ε : ℝ) (ℓ : ℕ) (z : ℂ) : ℂ :=
  if ε = 0 then 2 ^ (ℓ + 1) * regularizedHGFun 0 {(2 * ℓ + 2 : ℂ)} (-(2 * z))
  else 2 ^ (ℓ + 1) * exp (-z / coulombKappa ε 1) *
    kummerM (ℓ + 1 - coulombKappa ε 1) (2 * ℓ + 2) (2 * z / coulombKappa ε 1) / (2 * ℓ + 1)!

/-- `Φ(ε,ℓ;z) = z^{ℓ+1} Ψ(ε,ℓ;z)`. -/
lemma q2e_Phi_eq (ε : ℝ) (ℓ : ℕ) : q2e_Phi ε ℓ = fun z => z ^ (ℓ + 1) * q2e_Psi ε ℓ z := by
  funext z
  unfold q2e_Phi q2e_Psi q2e_Phi0 q2e_PhiK
  split_ifs <;> ring

/-- The reduced function `Ψ(ε,ℓ;·)` is entire. -/
lemma q2e_Psi_differentiable (ε : ℝ) (ℓ : ℕ) : Differentiable ℂ (q2e_Psi ε ℓ) := by
  unfold q2e_Psi
  split_ifs with hε
  · have h : Differentiable ℂ (regularizedHGFun (∅ : Multiset ℂ) {(2 * ℓ + 2 : ℂ)}) :=
      fun w => (DLMF.Bessel.analyticAt_regularized0F1 _ w).differentiableAt
    simp only [Multiset.empty_eq_zero] at h
    exact (h.comp ((differentiable_id.const_mul 2).neg)).const_mul _
  · have hk := q2e_kummerM_differentiable (ℓ + 1 - coulombKappa ε 1) ℓ
    have h1 : Differentiable ℂ fun z : ℂ => kummerM (ℓ + 1 - coulombKappa ε 1) (2 * ℓ + 2)
        (2 * z / coulombKappa ε 1) :=
      hk.comp ((differentiable_id.const_mul 2).div_const _)
    exact ((((differentiable_id.neg.div_const _).cexp).const_mul _).mul h1).div_const _

/-- `Ψ(ε,ℓ;0) = α₀(ε,ℓ)`, the leading power-series coefficient. -/
lemma q2e_Psi_zero (ε : ℝ) (ℓ : ℕ) : q2e_Psi ε ℓ 0 = coulombAlpha ε ℓ 0 := by
  have hG : Gamma (2 * ℓ + 2 : ℂ) = (2 * ℓ + 1)! := by
    rw [show (2 * ℓ + 2 : ℂ) = ((2 * ℓ + 1 : ℕ) : ℂ) + 1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
  unfold q2e_Psi
  simp only [coulombAlpha]
  split_ifs
  · rw [mul_zero, neg_zero, Complex.regularizedHGFun_zero, ← Multiset.empty_eq_zero,
      DLMF.Bessel.regularizedHGFunCoeff_empty]
    simp [hG, div_eq_mul_inv]
  · simp

/-- For `z ≠ 0`, `Φ(ε,ℓ;·)` solves `Φ'' + (ε + 2/z - ℓ(ℓ+1)/z²) Φ = 0` (DLMF 33.14.1). -/
theorem q2e_Phi_ode (ε : ℝ) (ℓ : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (deriv (q2e_Phi ε ℓ))
      (-((ε : ℂ) + 2 / z - ℓ * (ℓ + 1) / z ^ 2) * q2e_Phi ε ℓ z) z := by
  by_cases hε : ε = 0
  · have h : q2e_Phi ε ℓ = q2e_Phi0 ℓ := funext fun w => by simp [q2e_Phi, hε]
    rw [h, hε]
    simpa using q2e_Phi0_ode ℓ hz
  · have h : q2e_Phi ε ℓ = q2e_PhiK (coulombKappa ε 1) ℓ := funext fun w => by
      simp [q2e_Phi, hε]
    rw [h]
    refine q2e_PhiK_ode (coulombKappa_ne_zero hε 1) ℓ ?_ hz
    rw [coulombKappa_sq hε]
    field_simp

/-- **The power series 33.19.1 in `ℂ`.** -/
theorem q2e_Phi_hasSum (ε : ℝ) (ℓ : ℕ) (z : ℂ) :
    HasSum (fun k => (coulombAlpha ε ℓ k : ℂ) * z ^ (k + ℓ + 1)) (q2e_Phi ε ℓ z) :=
  q2e_hasSum_of_ode (q2e_Psi_differentiable ε ℓ) (q2e_Phi_eq ε ℓ)
    (fun _ hz => q2e_Phi_ode ε ℓ hz) (q2e_Psi_zero ε ℓ) z

/-- `Φ(ε,ℓ;·)` is entire. -/
theorem q2e_Phi_differentiable (ε : ℝ) (ℓ : ℕ) : Differentiable ℂ (q2e_Phi ε ℓ) := by
  rw [q2e_Phi_eq]; exact (differentiable_id.pow _).mul (q2e_Psi_differentiable ε ℓ)

/-- `f(ε,ℓ;r) = Re q2e_Phi ε ℓ r`. -/
theorem q2e_coulombf_eq_re (ε : ℝ) (ℓ : ℕ) (r : ℝ) :
    coulombf ε ℓ r = (q2e_Phi ε ℓ r).re := by
  unfold coulombf q2e_Phi
  split_ifs with hε
  · rfl
  · rw [q2e_coulombfKummer_eq]
    rcases q2e_coulombKappa_eq_or ε r with h | h
    · rw [h]
    · rw [h, ← q2e_coulombfKummer_eq, coulombfKummer_neg, q2e_coulombfKummer_eq]

/-- The derivative of `f(ε,ℓ;·)` is the real part of the derivative of `q2e_Phi ε ℓ`. -/
theorem q2e_hasDerivAt_coulombf (ε : ℝ) (ℓ : ℕ) (x : ℝ) :
    HasDerivAt (coulombf ε ℓ) (deriv (q2e_Phi ε ℓ) x).re x := by
  rw [show coulombf ε ℓ = fun x : ℝ => (q2e_Phi ε ℓ x).re from funext (q2e_coulombf_eq_re ε ℓ)]
  exact ((q2e_Phi_differentiable ε ℓ x).hasDerivAt).real_of_complex

/-! ### Taylor coefficients, ladder relations -/

/-- The Taylor coefficients of `Φ(ε,ℓ;·)` at `0`: `Φ⁽ⁿ⁾(0) = 0` for `n ≤ ℓ` and `n! α_{n-ℓ-1}(ε,ℓ)`
otherwise. -/
lemma q2e_iteratedDeriv_Phi (ε : ℝ) (ℓ n : ℕ) :
    iteratedDeriv n (q2e_Phi ε ℓ) 0 =
      if n < ℓ + 1 then 0 else (n ! : ℂ) * coulombAlpha ε ℓ (n - (ℓ + 1)) := by
  obtain ⟨hlow, hmain⟩ := q2e_iteratedDeriv_of_ode (q2e_Psi_differentiable ε ℓ) (q2e_Phi_eq ε ℓ)
    (fun _ hz => q2e_Phi_ode ε ℓ hz) (q2e_Psi_zero ε ℓ)
  split_ifs with h
  · exact hlow n h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp h)
    rw [hmain j, Nat.add_sub_cancel_left]

/-- An entire function all of whose derivatives vanish at `0` is zero. -/
lemma q2e_eq_zero_of_iteratedDeriv {Q : ℂ → ℂ} (hQ : Differentiable ℂ Q)
    (h : ∀ n, iteratedDeriv n Q 0 = 0) (z : ℂ) : Q z = 0 := by
  have hT := Complex.hasSum_taylorSeries_of_entire hQ 0 z
  simp only [h, smul_zero] at hT
  exact hT.unique hasSum_zero

/-- `(z^m Φ)⁽ⁿ⁾(0) = n^{(m)} Φ^{(n-m)}(0)` with the falling factorial `n^{(m)}`. -/
lemma q2e_iD_pow_mul {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) (m n : ℕ) :
    iteratedDeriv n (fun z => z ^ m * Φ z) 0 = n.descFactorial m * iteratedDeriv (n - m) Φ 0 :=
  ODE.iteratedDeriv_pow_mul_zero (hΦ.contDiff).contDiffAt m

/-- The three-term recurrence `(k+2)(k+2ℓ+3) α_{k+2} + 2 α_{k+1} + ε α_k = 0` of the power-series
coefficients. -/
lemma q2e_alpha_rec (ε : ℝ) (ℓ k : ℕ) :
    ((k : ℝ) + 2) * ((k : ℝ) + 2 + 2 * ℓ + 1) * coulombAlpha ε ℓ (k + 2) +
      2 * coulombAlpha ε ℓ (k + 1) + ε * coulombAlpha ε ℓ k = 0 := by
  rw [coulombAlpha]
  have h : ((k : ℝ) + 2) * ((k : ℝ) + 2 + 2 * ℓ + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- `α₁(ε,ℓ) = -α₀(ε,ℓ)/(ℓ+1)`. -/
lemma q2e_alpha_one (ε : ℝ) (ℓ : ℕ) :
    coulombAlpha ε ℓ 1 = -coulombAlpha ε ℓ 0 / (ℓ + 1) := rfl

/-- `α₀(ε,ℓ+1) = α₀(ε,ℓ)/((ℓ+1)(2ℓ+3))`. -/
lemma q2e_alpha_zero_succ (ε : ℝ) (ℓ : ℕ) :
    coulombAlpha ε (ℓ + 1) 0 = coulombAlpha ε ℓ 0 / ((ℓ + 1) * (2 * ℓ + 3)) := by
  simp only [coulombAlpha]
  rw [show 2 * (ℓ + 1) + 1 = 2 * ℓ + 1 + 1 + 1 by ring, Nat.factorial_succ,
    Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- The raising relation of the coefficients 33.19.2 behind 33.17.3:
`(1 + (ℓ+1)²ε) α^{(ℓ+1)}_j = -(ℓ+1)(j+2) α^{(ℓ)}_{j+2} - α^{(ℓ)}_{j+1}`. -/
lemma q2e_alpha_raise (ε : ℝ) (ℓ j : ℕ) :
    (1 + ((ℓ : ℝ) + 1) ^ 2 * ε) * coulombAlpha ε (ℓ + 1) j =
      -((ℓ : ℝ) + 1) * ((j : ℝ) + 2) * coulombAlpha ε ℓ (j + 2) - coulombAlpha ε ℓ (j + 1) := by
  have hl : ((ℓ : ℝ) + 1) ≠ 0 := by positivity
  have hl3 : (2 * (ℓ : ℝ) + 3) ≠ 0 := by positivity
  have hl2 : ((ℓ : ℝ) + 2) ≠ 0 := by positivity
  suffices H : ∀ j, (1 + ((ℓ : ℝ) + 1) ^ 2 * ε) * coulombAlpha ε (ℓ + 1) j =
      -((ℓ : ℝ) + 1) * ((j : ℝ) + 2) * coulombAlpha ε ℓ (j + 2) - coulombAlpha ε ℓ (j + 1) ∧
      (1 + ((ℓ : ℝ) + 1) ^ 2 * ε) * coulombAlpha ε (ℓ + 1) (j + 1) =
      -((ℓ : ℝ) + 1) * ((j + 1 : ℕ) + 2) * coulombAlpha ε ℓ (j + 1 + 2) -
        coulombAlpha ε ℓ (j + 1 + 1) from (H j).1
  intro j
  induction j with
  | zero =>
    have R0 := q2e_alpha_rec ε ℓ 0
    have R1 := q2e_alpha_rec ε ℓ 1
    have h1 := q2e_alpha_one ε ℓ
    have h1' := q2e_alpha_one ε (ℓ + 1)
    have h0' := q2e_alpha_zero_succ ε ℓ
    push_cast at R0 R1 h1' ⊢
    set a0 := coulombAlpha ε ℓ 0
    set a1 := coulombAlpha ε ℓ 1
    set a2 := coulombAlpha ε ℓ 2
    set a3 := coulombAlpha ε ℓ 3
    rw [h1', h0']
    rw [h1] at R0 R1
    rw [h1]
    field_simp at R0 R1 ⊢
    constructor
    · linear_combination (1 + (ℓ : ℝ)) * R0
    · linear_combination (1 / 2 : ℝ) * R0 +
        ((3 / 2 : ℝ) + 5 / 2 * ℓ + ℓ ^ 2) * R1
  | succ j ih =>
    refine ⟨ih.2, ?_⟩
    obtain ⟨P0, P1⟩ := ih
    have R3 := q2e_alpha_rec ε ℓ (j + 1)
    have R4 := q2e_alpha_rec ε ℓ (j + 2)
    have hN : ((j : ℝ) + 2) * ((j : ℝ) + 2 + 2 * ((ℓ + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    rw [show j + 1 + 1 = j + 2 by ring, coulombAlpha]
    rw [show j + 1 + 1 = j + 2 by ring] at P1
    push_cast at P0 P1 R3 R4 hN ⊢
    rw [show j + 1 + 2 = j + 3 by ring] at P1 R3 ⊢
    rw [show j + 2 + 2 = j + 4 by ring, show j + 2 + 1 = j + 3 by ring] at R4
    rw [show j + 2 + 2 = j + 4 by ring, show j + 2 + 1 = j + 3 by ring]
    rw [mul_div_assoc', div_eq_iff hN]
    linear_combination (-2) * P1 - ε * P0 + (ℓ + 1) * (j + 2) * R4 + R3

/-- The lowering relation of the coefficients 33.19.2 behind 33.17.1:
`α^{(m)}_{j+1} = (m+1)(j+2m+4) α^{(m+1)}_{j+1} - α^{(m+1)}_j`. -/
lemma q2e_alpha_lower (ε : ℝ) (m j : ℕ) :
    coulombAlpha ε m (j + 1) = ((m : ℝ) + 1) * ((j : ℝ) + 2 * m + 4) *
      coulombAlpha ε (m + 1) (j + 1) - coulombAlpha ε (m + 1) j := by
  have hl : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hl3 : (2 * (m : ℝ) + 3) ≠ 0 := by positivity
  have hl2 : ((m : ℝ) + 2) ≠ 0 := by positivity
  have h00 : coulombAlpha ε m 0 = ((m : ℝ) + 1) * (2 * m + 3) * coulombAlpha ε (m + 1) 0 := by
    rw [q2e_alpha_zero_succ]; field_simp
  suffices H : ∀ j, (coulombAlpha ε m (j + 1) = ((m : ℝ) + 1) * ((j : ℝ) + 2 * m + 4) *
      coulombAlpha ε (m + 1) (j + 1) - coulombAlpha ε (m + 1) j) ∧
      (coulombAlpha ε m (j + 1 + 1) = ((m : ℝ) + 1) * (((j + 1 : ℕ) : ℝ) + 2 * m + 4) *
      coulombAlpha ε (m + 1) (j + 1 + 1) - coulombAlpha ε (m + 1) (j + 1)) from (H j).1
  have Q0 : coulombAlpha ε m 1 = ((m : ℝ) + 1) * (2 * m + 4) * coulombAlpha ε (m + 1) 1 -
      coulombAlpha ε (m + 1) 0 := by
    rw [q2e_alpha_one, q2e_alpha_one, h00]
    push_cast
    field_simp
    ring
  intro j
  induction j with
  | zero =>
    refine ⟨by simpa using Q0, ?_⟩
    have C0 := q2e_alpha_rec ε m 0
    have A0 := q2e_alpha_rec ε (m + 1) 0
    rw [h00, Q0] at C0
    push_cast at C0 A0 ⊢
    have hN : (2 : ℝ) * (2 + 2 * m + 1) ≠ 0 := by positivity
    have : coulombAlpha ε m 2 = -(2 * (((m : ℝ) + 1) * (2 * m + 4) *
        coulombAlpha ε (m + 1) 1 - coulombAlpha ε (m + 1) 0) +
        ε * (((m : ℝ) + 1) * (2 * m + 3) * coulombAlpha ε (m + 1) 0)) /
        ((0 + 2) * (0 + 2 + 2 * m + 1)) := by
      rw [eq_div_iff (by simpa using hN)]; linear_combination C0
    have hA1 : ((m : ℝ) + 2) * coulombAlpha ε (m + 1) 1 + coulombAlpha ε (m + 1) 0 = 0 := by
      rw [q2e_alpha_one]; push_cast; field_simp; ring
    rw [this, div_eq_iff (by simpa using hN)]
    linear_combination (-((m : ℝ) + 1) * (2 + 2 * m + 1)) * A0 + 2 * hA1
  | succ j ih =>
    refine ⟨ih.2, ?_⟩
    obtain ⟨P0, P1⟩ := ih
    have C := q2e_alpha_rec ε m (j + 1)
    have A1 := q2e_alpha_rec ε (m + 1) (j + 1)
    have A0 := q2e_alpha_rec ε (m + 1) j
    have hN : ((j + 1 : ℕ) + 2 : ℝ) * ((j + 1 : ℕ) + 2 + 2 * (m : ℝ) + 1) ≠ 0 := by positivity
    rw [show j + 1 + 1 = j + 2 by ring] at P1 C
    rw [show j + 1 + 2 = j + 3 by ring] at C A1
    rw [show j + 2 = j + 2 from rfl] at A0
    rw [show j + 1 + 1 + 1 = j + 3 by ring, show j + 1 + 1 = j + 2 by ring]
    rw [P1, P0] at C
    have : coulombAlpha ε m (j + 3) = -(2 * (((m : ℝ) + 1) * (((j + 1 : ℕ) : ℝ) + 2 * m + 4) *
        coulombAlpha ε (m + 1) (j + 2) - coulombAlpha ε (m + 1) (j + 1)) +
        ε * (((m : ℝ) + 1) * ((j : ℝ) + 2 * m + 4) * coulombAlpha ε (m + 1) (j + 1) -
          coulombAlpha ε (m + 1) j)) /
        (((j + 1 : ℕ) + 2 : ℝ) * ((j + 1 : ℕ) + 2 + 2 * (m : ℝ) + 1)) := by
      rw [eq_div_iff hN]; linear_combination C
    rw [this, div_eq_iff hN]
    push_cast at A1 A0 ⊢
    linear_combination (-((m : ℝ) + 1) * ((j : ℝ) + 3 + 2 * m + 1)) * A1 + A0

/-- **The raising relation 33.17.3 for the entire function** `q2e_Phi`:
`(ℓ+1) z Φ_ℓ'(z) = ((ℓ+1)² - z) Φ_ℓ(z) - (1 + (ℓ+1)²ε) z Φ_{ℓ+1}(z)`. -/
theorem q2e_Phi_raise (ε : ℝ) (ℓ : ℕ) (z : ℂ) :
    ((ℓ : ℂ) + 1) * (z * deriv (q2e_Phi ε ℓ) z) =
      (((ℓ : ℂ) + 1) ^ 2 - z) * q2e_Phi ε ℓ z -
        (1 + ((ℓ : ℂ) + 1) ^ 2 * ε) * z * q2e_Phi ε (ℓ + 1) z := by
  have hΦ := q2e_Phi_differentiable ε ℓ
  have hΦ1 := q2e_Phi_differentiable ε (ℓ + 1)
  have hΦ' : Differentiable ℂ (deriv (q2e_Phi ε ℓ)) := fun x =>
    ((hΦ.contDiff (n := 2)).deriv' (n := 1)).differentiable (by norm_num) x
  set Dc : ℂ := 1 + ((ℓ : ℂ) + 1) ^ 2 * ε
  have hQ : ∀ w : ℂ, (fun z : ℂ => ((ℓ : ℂ) + 1) * (z ^ 1 * deriv (q2e_Phi ε ℓ) z) -
      ((ℓ : ℂ) + 1) ^ 2 * (z ^ 0 * q2e_Phi ε ℓ z) + z ^ 1 * q2e_Phi ε ℓ z +
      Dc * (z ^ 1 * q2e_Phi ε (ℓ + 1) z)) w = 0 := by
    refine q2e_eq_zero_of_iteratedDeriv (by fun_prop) fun n => ?_
    have hc : ∀ f : ℂ → ℂ, Differentiable ℂ f → ContDiffAt ℂ n f 0 :=
      fun f hf => (hf.contDiff).contDiffAt
    rw [iteratedDeriv_fun_add (hc _ (by fun_prop)) (hc _ (by fun_prop)),
      iteratedDeriv_fun_add (hc _ (by fun_prop)) (hc _ (by fun_prop)),
      iteratedDeriv_fun_sub (hc _ (by fun_prop)) (hc _ (by fun_prop)),
      iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
      iteratedDeriv_const_mul_field, q2e_iD_pow_mul hΦ', q2e_iD_pow_mul hΦ,
      q2e_iD_pow_mul hΦ, q2e_iD_pow_mul hΦ1]
    rcases n with _ | n
    · simp [q2e_iteratedDeriv_Phi]
    rw [Nat.add_sub_cancel, ← iteratedDeriv_succ', Nat.descFactorial_one, Nat.descFactorial_zero,
      Nat.sub_zero]
    simp only [q2e_iteratedDeriv_Phi]
    rcases Nat.lt_or_ge n ℓ with hn | hn
    · simp [show n + 1 < ℓ + 1 by omega, show n < ℓ + 1 by omega, show n < ℓ + 1 + 1 by omega]
    obtain ⟨j, rfl⟩ : ∃ j, n = ℓ + j := ⟨n - ℓ, by omega⟩
    rcases j with _ | _ | k
    · simp only [add_zero, lt_self_iff_false, ↓reduceIte, Nat.sub_self, lt_add_iff_pos_right,
        Nat.lt_one_iff, show ℓ < ℓ + 1 + 1 by omega]
      push_cast; ring
    · simp only [show ¬ (ℓ + (0 + 1) + 1 < ℓ + 1) by omega, show ¬ (ℓ + (0 + 1) < ℓ + 1) by omega,
        show ℓ + (0 + 1) < ℓ + 1 + 1 by omega, ↓reduceIte,
        show ℓ + (0 + 1) + 1 - (ℓ + 1) = 1 by omega, show ℓ + (0 + 1) - (ℓ + 1) = 0 by omega]
      rw [q2e_alpha_one, show ℓ + (0 + 1) + 1 = (ℓ + 1) + 1 by omega, Nat.factorial_succ (ℓ + 1)]
      have : ((ℓ : ℂ) + 1) ≠ 0 := by norm_cast
      push_cast
      field_simp
      ring
    · have hr := q2e_alpha_raise ε ℓ k
      simp only [show ¬ (ℓ + (k + 1 + 1) + 1 < ℓ + 1) by omega,
        show ¬ (ℓ + (k + 1 + 1) < ℓ + 1) by omega,
        show ¬ (ℓ + (k + 1 + 1) < ℓ + 1 + 1) by omega, ↓reduceIte,
        show ℓ + (k + 1 + 1) + 1 - (ℓ + 1) = k + 2 by omega,
        show ℓ + (k + 1 + 1) - (ℓ + 1) = k + 1 by omega,
        show ℓ + (k + 1 + 1) - (ℓ + 1 + 1) = k by omega]
      rw [Nat.factorial_succ (ℓ + (k + 1 + 1))]
      generalize (ℓ + (k + 1 + 1))! = F
      simp only [Dc]
      have hc : (((1 + ((ℓ : ℝ) + 1) ^ 2 * ε) * coulombAlpha ε (ℓ + 1) k : ℝ) : ℂ) =
          ((-((ℓ : ℝ) + 1) * ((k : ℝ) + 2) * coulombAlpha ε ℓ (k + 2) -
            coulombAlpha ε ℓ (k + 1) : ℝ) : ℂ) := by rw [hr]
      push_cast at hc ⊢
      linear_combination ((ℓ : ℂ) + k + 3) * (F : ℂ) * hc
  have h := hQ z
  simp only [pow_one, pow_zero, one_mul] at h
  linear_combination h

/-- **The three-term recurrence 33.17.1 for the entire functions** `q2e_Phi` (with `ℓ = m+1`). -/
theorem q2e_Phi_three_term (ε : ℝ) (m : ℕ) (z : ℂ) :
    ((m : ℂ) + 2) * z * q2e_Phi ε m z -
      (2 * m + 3) * ((m + 1) * (m + 2) - z) * q2e_Phi ε (m + 1) z +
      (m + 1) * (1 + ((m : ℂ) + 2) ^ 2 * ε) * z * q2e_Phi ε (m + 2) z = 0 := by
  have hΦ := q2e_Phi_differentiable ε m
  have hΦ1 := q2e_Phi_differentiable ε (m + 1)
  have hΦ2 := q2e_Phi_differentiable ε (m + 2)
  set Dc : ℂ := 1 + ((m : ℂ) + 2) ^ 2 * ε
  have hQ : ∀ w : ℂ, (fun z : ℂ => ((m : ℂ) + 2) * (z ^ 1 * q2e_Phi ε m z) -
      (2 * m + 3) * (m + 1) * (m + 2) * (z ^ 0 * q2e_Phi ε (m + 1) z) +
      (2 * m + 3) * (z ^ 1 * q2e_Phi ε (m + 1) z) +
      (m + 1) * Dc * (z ^ 1 * q2e_Phi ε (m + 2) z)) w = 0 := by
    refine q2e_eq_zero_of_iteratedDeriv (by fun_prop) fun n => ?_
    have hc : ∀ f : ℂ → ℂ, Differentiable ℂ f → ContDiffAt ℂ n f 0 :=
      fun f hf => (hf.contDiff).contDiffAt
    rw [iteratedDeriv_fun_add (hc _ (by fun_prop)) (hc _ (by fun_prop)),
      iteratedDeriv_fun_add (hc _ (by fun_prop)) (hc _ (by fun_prop)),
      iteratedDeriv_fun_sub (hc _ (by fun_prop)) (hc _ (by fun_prop)),
      iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
      iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field, q2e_iD_pow_mul hΦ,
      q2e_iD_pow_mul hΦ1, q2e_iD_pow_mul hΦ1, q2e_iD_pow_mul hΦ2]
    rcases n with _ | n
    · simp [q2e_iteratedDeriv_Phi]
    rw [Nat.add_sub_cancel, Nat.descFactorial_one, Nat.descFactorial_zero, Nat.sub_zero]
    simp only [q2e_iteratedDeriv_Phi]
    rcases Nat.lt_or_ge n (m + 1) with hn | hn
    · simp [show n + 1 < m + 1 + 1 by omega, show n < m + 1 by omega,
        show n < m + 1 + 1 by omega, show n < m + 2 + 1 by omega]
    obtain ⟨k, rfl⟩ : ∃ k, n = m + 1 + k := ⟨n - (m + 1), by omega⟩
    have h00 : coulombAlpha ε m 0 = ((m : ℝ) + 1) * (2 * m + 3) * coulombAlpha ε (m + 1) 0 := by
      rw [q2e_alpha_zero_succ]; field_simp
    rw [Nat.factorial_succ (m + 1 + k)]
    generalize (m + 1 + k)! = F
    rcases k with _ | _ | j
    · simp only [add_zero, show ¬ (m + 1 + 1 < m + 1 + 1) by omega,
        show ¬ (m + 1 < m + 1) by omega, show m + 1 < m + 1 + 1 by omega,
        show m + 1 < m + 2 + 1 by omega, ↓reduceIte, Nat.sub_self,
        show m + 1 + 1 - (m + 1 + 1) = 0 by omega]
      have h := congrArg (fun x : ℝ => (x : ℂ)) h00
      push_cast at h ⊢
      rw [h]; ring
    · simp only [show ¬ (m + 1 + (0 + 1) + 1 < m + 1 + 1) by omega,
        show ¬ (m + 1 + (0 + 1) < m + 1) by omega, show ¬ (m + 1 + (0 + 1) < m + 1 + 1) by omega,
        show m + 1 + (0 + 1) < m + 2 + 1 by omega, ↓reduceIte,
        show m + 1 + (0 + 1) + 1 - (m + 1 + 1) = 1 by omega,
        show m + 1 + (0 + 1) - (m + 1) = 1 by omega,
        show m + 1 + (0 + 1) - (m + 1 + 1) = 0 by omega]
      have hl := congrArg (fun x : ℝ => (x : ℂ)) (q2e_alpha_lower ε m 0)
      have hA1 : ((m : ℝ) + 2) * coulombAlpha ε (m + 1) 1 + coulombAlpha ε (m + 1) 0 = 0 := by
        rw [q2e_alpha_one]; push_cast; field_simp; ring
      have hA := congrArg (fun x : ℝ => (x : ℂ)) hA1
      push_cast at hl hA ⊢
      rw [hl]
      linear_combination ((m : ℂ) + 1) * ((m : ℂ) + 1 + 1 + 1) * F * hA
    · have hl := congrArg (fun x : ℝ => (x : ℂ)) (q2e_alpha_lower ε m (j + 1))
      have hr := congrArg (fun x : ℝ => (x : ℂ)) (q2e_alpha_raise ε (m + 1) j)
      simp only [show ¬ (m + 1 + (j + 1 + 1) + 1 < m + 1 + 1) by omega,
        show ¬ (m + 1 + (j + 1 + 1) < m + 1) by omega,
        show ¬ (m + 1 + (j + 1 + 1) < m + 1 + 1) by omega,
        show ¬ (m + 1 + (j + 1 + 1) < m + 2 + 1) by omega, ↓reduceIte,
        show m + 1 + (j + 1 + 1) + 1 - (m + 1 + 1) = j + 2 by omega,
        show m + 1 + (j + 1 + 1) - (m + 1) = j + 1 + 1 by omega,
        show m + 1 + (j + 1 + 1) - (m + 1 + 1) = j + 1 by omega,
        show m + 1 + (j + 1 + 1) - (m + 2 + 1) = j by omega]
      simp only [Dc]
      push_cast at hl hr ⊢
      rw [hl]
      linear_combination ((m : ℂ) + 1) * ((m : ℂ) + 1 + j + 2 + 1) * F * hr
  have h := hQ z
  simp only [pow_one, pow_zero, one_mul] at h
  linear_combination h

end DLMF.Coulomb
