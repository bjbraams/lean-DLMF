/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Coulomb.RhoEtaProperties
public import DLMF.Core.Framework
public import DLMF.IncompleteGamma.FractionTools

/-!
# Coulomb functions: integral representations and continued fractions (DLMF §§33.7–33.8)

* §33.7: the integral representations 33.7.1–33.7.4. Noninteger powers and the arctangent take
  their principal values (DLMF §33.7). Each statement asserts the integrability of the integrand
  together with the formula, so the Lean convention for nonintegrable functions never enters.
  The contour of 33.7.4, from `-1` to `-i∞`, is the ray `t = -1 - is`, `s ≥ 0`
  (`dt = -i ds`).
* §33.8: the continued fractions 33.8.1–33.8.2 (with `HasContinuedFraction a b v`, meaning
  `v = a₀/(b₀ + a₁/(b₁ + ⋯))`, from `DLMF.Core.Framework`) and Barnett's formulas 33.8.4–33.8.5
  recovering `F_ℓ`, `F_ℓ'`, `G_ℓ`, `G_ℓ'` from `u = F_ℓ'/F_ℓ` and `p + iq = H^+_ℓ'/H^+_ℓ`. The
  latter are proved from the Wronskian 33.2.12.
-/

@[expose] public section

open Complex Filter Set MeasureTheory
open scoped Real Topology Nat ComplexConjugate

noncomputable section

namespace DLMF.Coulomb

open DLMF.Confluent

/-! ### §33.7 Integral representations -/

/-- **DLMF 33.7.1**: `F_ℓ(η,ρ) = ρ^{ℓ+1} 2^ℓ e^{iρ - πη/2}/|Γ(ℓ+1+iη)|
∫_0^1 e^{-2iρt} t^{ℓ+iη} (1-t)^{ℓ-iη} dt` for real `ρ`. -/
@[dlmf 33.7.E1]
theorem coulombF_eq_integral (ℓ : ℕ) (η ρ : ℝ) :
    IntervalIntegrable (fun t : ℝ => exp (-2 * I * ρ * t) * (t : ℂ) ^ ((ℓ : ℂ) + I * η) *
        ((1 - t : ℝ) : ℂ) ^ ((ℓ : ℂ) - I * η)) volume 0 1 ∧
    (coulombF ℓ η ρ : ℂ) = (ρ : ℂ) ^ (ℓ + 1) * 2 ^ ℓ * exp (I * ρ - π * η / 2) /
        ‖Gamma ((ℓ : ℂ) + 1 + I * η)‖ *
      ∫ t in (0 : ℝ)..1, exp (-2 * I * ρ * t) * (t : ℂ) ^ ((ℓ : ℂ) + I * η) *
        ((1 - t : ℝ) : ℂ) ^ ((ℓ : ℂ) - I * η) := by
  set a : ℂ := (ℓ : ℂ) + 1 + I * η with ha
  have hare : 0 < a.re := by simp [ha]; positivity
  have hcare : 0 < (2 * (ℓ : ℂ) + 2 - a).re := by
    simp [ha]; linarith [(Nat.cast_nonneg ℓ : (0:ℝ) ≤ ℓ)]
  have hfun : (fun t : ℝ => exp (-2 * I * ρ * t) * (t : ℂ) ^ ((ℓ : ℂ) + I * η) *
        ((1 - t : ℝ) : ℂ) ^ ((ℓ : ℂ) - I * η)) = fun t : ℝ =>
      (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (2 * (ℓ : ℂ) + 2 - a - 1) * exp (-(2 * I * ρ) * t) := by
    funext t
    rw [show a - 1 = (ℓ : ℂ) + I * η by rw [ha]; ring,
      show 2 * (ℓ : ℂ) + 2 - a - 1 = (ℓ : ℂ) - I * η by rw [ha]; ring, ofReal_sub, ofReal_one]
    ring_nf
  rw [hfun]
  refine ⟨(betaIntegral_convergent hare hcare).mul_continuousOn (by fun_prop), ?_⟩
  have hM := kummerM_eq_euler_integral (z := -(2 * I * ρ)) hare hcare
  rw [ofReal_coulombF, coulombWave_eq_conj_form, ← ha, hM]
  have hconj : Gamma (2 * (ℓ : ℂ) + 2 - a) = conj (Gamma a) := by
    rw [← Complex.Gamma_conj]; congr 1; rw [ha]
    simp [map_add, map_mul, Complex.conj_ofReal]; ring
  have hfac : Gamma (2 * (ℓ : ℂ) + 2) = ((2 * ℓ + 1)! : ℂ) := by
    rw [show 2 * (ℓ : ℂ) + 2 = ((2 * ℓ + 1 : ℕ) : ℂ) + 1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
  have hg : Gamma a ≠ 0 := c33a_Gamma_ne_zero ℓ η
  have hn : (‖Gamma a‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hg).ne'
  have hsq : Gamma a * conj (Gamma a) = (‖Gamma a‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [hconj, hfac, coulombC, ← ha, sub_eq_add_neg (I * (ρ : ℂ)), exp_add]
  generalize (∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (2 * (ℓ : ℂ) + 2 - a - 1) *
      exp (-(2 * I * ρ) * t)) = J
  have hf : ((2 * ℓ + 1)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hcg : conj (Gamma a) ≠ 0 := (map_ne_zero _).mpr hg
  push_cast
  rw [show -(π : ℂ) * η / 2 = -(π * η / 2) by ring]
  field_simp
  linear_combination (-((ρ : ℂ) ^ (ℓ + 1) * J)) * hsq

section q2aRot

open scoped Interval

/-- Tricomi's kernel is differentiable at `t ≠ 0` with `re t ≥ 0`. -/
lemma q2a_differentiableAt_kernel (a b z : ℂ) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    DifferentiableAt ℂ (tricomiKernel a b z) t := by
  have h1 : t ∈ slitPlane := by
    rcases ht.lt_or_eq with h | h
    · exact Or.inl h
    · refine Or.inr fun him => ht0 (Complex.ext ?_ ?_) <;> simp [← h, him]
  have h2 : 1 + t ∈ slitPlane := Or.inl (by simp; linarith)
  unfold tricomiKernel
  exact ((by fun_prop : DifferentiableAt ℂ (fun t : ℂ => exp (-z * t)) t).mul
    (differentiableAt_id.cpow (differentiableAt_const _) h1)).mul
    ((differentiableAt_const _ |>.add differentiableAt_id).cpow (differentiableAt_const _) h2)

/-- `re (2iρ · r e^{iθ}) = -2ρ r sin θ`. -/
lemma q2a_re_two_I_mul (ρ r θ : ℝ) :
    (2 * I * ρ * ((r : ℂ) * exp (θ * I))).re = -(2 * ρ * r * Real.sin θ) := by
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  ring

/-- `re (r e^{iθ}) = r cos θ`. -/
lemma q2a_re_ray (r θ : ℝ) : ((r : ℂ) * exp (θ * I)).re = r * Real.cos θ := by
  rw [re_ofReal_mul, exp_ofReal_mul_I_re]

/-- Bounds for Tricomi's kernel at `z = 2iρ` along rays of angle `θ ∈ [-π/2, -π/4]`. -/
lemma q2a_kernel_bounds (a b : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, ∀ θ : ℝ, -(π / 2) ≤ θ → θ ≤ -(π / 4) →
      (∀ r : ℝ, 0 < r → r ≤ 1 →
        ‖tricomiKernel a b (2 * I * ρ) (r * exp (θ * I))‖ ≤ C * r ^ (a.re - 1)) ∧
      (∀ r : ℝ, 1 ≤ r →
        ‖tricomiKernel a b (2 * I * ρ) (r * exp (θ * I))‖ ≤ C * Real.exp (-(ρ / 2) * r)) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |(b - a - 1).re| ≤ N := ⟨⌈|(b - a - 1).re|⌉₊, Nat.le_ceil _⟩
  set E := Real.exp (π * |a.im|) * Real.exp (π * |(b - a - 1).im|) with hE
  have hE0 : 0 < E := by positivity
  obtain ⟨M, hM⟩ := exists_rpow_mul_exp_neg_le (a.re - 1 + N) (b := ρ / 2) (by positivity)
  have hM0 : 0 ≤ M := (by positivity : (0 : ℝ) ≤ 1 ^ (a.re - 1 + N) * Real.exp (-(ρ / 2) * 1)).trans
    (hM 1 le_rfl)
  refine ⟨2 ^ N * E * (M + 1), fun θ h1 h2 => ?_⟩
  have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨h1, by linarith [Real.pi_pos]⟩
  have hsin : Real.sin θ ≤ -(1 / 2) := by
    have := Real.sin_le_sin_of_le_of_le_pi_div_two h1 (by linarith [Real.pi_pos]) h2
    rw [Real.sin_neg, Real.sin_pi_div_four] at this
    have : (1 : ℝ) < Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have key : ∀ r : ℝ, 0 < r → ‖tricomiKernel a b (2 * I * ρ) (r * exp (θ * I))‖ ≤
      Real.exp (-(ρ * r)) * r ^ (a.re - 1) * (1 + r) ^ N * E := by
    intro r hr
    have hre : 0 ≤ ((r : ℂ) * exp (θ * I)).re := by
      rw [q2a_re_ray]; positivity
    have h := norm_tricomiKernel_le a b (2 * I * ρ) _ hre hN
    rw [norm_mul_exp_I_eq r hr.le, q2a_re_two_I_mul] at h
    refine h.trans ?_
    have : 0 < ρ * r := mul_pos hρ hr
    gcongr
    nlinarith
  refine ⟨fun r hr hr1 => (key r hr).trans ?_, fun r hr => (key r (by linarith)).trans ?_⟩
  · have e1 : Real.exp (-(ρ * r)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have e2 : (1 + r) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    have hrp : 0 ≤ r ^ (a.re - 1) := Real.rpow_nonneg hr.le _
    calc Real.exp (-(ρ * r)) * r ^ (a.re - 1) * (1 + r) ^ N * E
        ≤ 1 * r ^ (a.re - 1) * 2 ^ N * E := by gcongr
      _ ≤ 2 ^ N * E * (M + 1) * r ^ (a.re - 1) := by
        have : (0 : ℝ) ≤ 2 ^ N * E * r ^ (a.re - 1) := by positivity
        nlinarith
  · have hr0 : (0 : ℝ) < r := by linarith
    have e2 : (1 + r) ^ N ≤ 2 ^ N * r ^ N := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) N
    have hpow : r ^ (a.re - 1) * r ^ N = r ^ (a.re - 1 + N) :=
      (Real.rpow_add_natCast hr0.ne' _ _).symm
    have hexp : Real.exp (-(ρ * r)) = Real.exp (-(ρ / 2) * r) * Real.exp (-(ρ / 2) * r) := by
      rw [← Real.exp_add]; ring_nf
    have hMr := hM r hr
    have hrp : 0 ≤ r ^ (a.re - 1) := Real.rpow_nonneg hr0.le _
    calc Real.exp (-(ρ * r)) * r ^ (a.re - 1) * (1 + r) ^ N * E
        ≤ Real.exp (-(ρ * r)) * r ^ (a.re - 1) * (2 ^ N * r ^ N) * E := by gcongr
      _ = 2 ^ N * E * (r ^ (a.re - 1 + N) * Real.exp (-(ρ / 2) * r)) *
            Real.exp (-(ρ / 2) * r) := by rw [← hpow, hexp]; ring
      _ ≤ 2 ^ N * E * M * Real.exp (-(ρ / 2) * r) := by gcongr
      _ ≤ 2 ^ N * E * (M + 1) * Real.exp (-(ρ / 2) * r) := by gcongr; linarith

/-- **Tricomi's integral on the imaginary axis**: for `re a > 0`, `ρ > 0`,
`Γ(a) U(a,b,2iρ) = e^{-iπ/2} ∫₀^∞ K(r e^{-iπ/2}) dr` with `K` Tricomi's kernel at `z = 2iρ`,
and the integrand is integrable. -/
lemma q2a_kummerU_two_I (a b : ℂ) (ha : 0 < a.re) {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun r : ℝ => tricomiKernel a b (2 * I * ρ) (r * exp (-(π / 2) * I))) (Ioi 0) ∧
    Gamma a * kummerU a b (2 * I * ρ) = exp (-(π / 2) * I) *
      ∫ r in Ioi (0 : ℝ), tricomiKernel a b (2 * I * ρ) (r * exp (-(π / 2) * I)) := by
  obtain ⟨C, hC⟩ := q2a_kernel_bounds a b hρ
  have hρ2 : 0 < ρ / 2 := by positivity
  have hcont : ∀ θ : ℝ, -(π / 2) ≤ θ → θ ≤ -(π / 4) → ∀ r : ℝ, 0 < r →
      ContinuousAt (fun r : ℝ => tricomiKernel a b (2 * I * ρ) (r * exp (θ * I))) r := by
    intro θ h1 h2 r hr
    have hre : 0 ≤ ((r : ℂ) * exp (θ * I)).re := by
      rw [q2a_re_ray]
      exact mul_nonneg hr.le (Real.cos_nonneg_of_mem_Icc ⟨h1, by linarith [Real.pi_pos]⟩)
    have hne : ((r : ℂ) * exp (θ * I)) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hr.ne') (exp_ne_zero _)
    exact ContinuousAt.comp (g := tricomiKernel a b (2 * I * ρ))
      (q2a_differentiableAt_kernel a b _ hre hne).continuousAt (by fun_prop)
  have hpi := Real.pi_pos
  refine ⟨by
    have := integrableOn_ray_of_bounds ha hρ2 (hcont _ le_rfl (by linarith))
      (hC _ le_rfl (by linarith)).1 (hC _ le_rfl (by linarith)).2
    simpa only [ofReal_neg, ofReal_div, ofReal_ofNat] using this, ?_⟩
  -- the representation on the ray of angle `-π/4`
  have hz : 0 < (2 * I * (ρ : ℂ) * exp ((-(π / 4) : ℝ) * I)).re := by
    have := q2a_re_two_I_mul ρ 1 (-(π / 4))
    simp only [ofReal_one, one_mul, mul_one] at this
    rw [this, Real.sin_neg, Real.sin_pi_div_four]
    have : 0 < Real.sqrt 2 := by positivity
    nlinarith
  have hU := kummerU_eq_tricomiRotated (b := b) ha (α := -(π / 4))
    (by rw [abs_neg, abs_of_pos (by positivity)]; linarith) hz
  rw [hU, tricomiRotated]
  set ω := exp (((-(π / 4) : ℝ) : ℂ) * I) with hω
  -- rotate further by `-π/4`
  have hshift : ∀ r y : ℝ, (r : ℂ) * exp (y * I) * ω = r * exp (((y + -(π / 4) : ℝ) : ℂ) * I) := by
    intro r y
    rw [hω, mul_assoc, ← exp_add]; push_cast; ring_nf
  have hy : ∀ y ∈ [[(0 : ℝ), -(π / 4)]], -(π / 2) ≤ y + -(π / 4) ∧ y + -(π / 4) ≤ -(π / 4) := by
    intro y hy
    rw [uIcc_of_ge (by linarith)] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hrot := integral_Ioi_eq_exp_mul_integral_Ioi_rotate (f := fun w =>
      tricomiKernel a b (2 * I * ρ) (w * ω)) (α := -(π / 4)) (C := C) ha hρ2
    (fun r hr y hy' => ?_) (fun r hr hr1 y hy' => ?_) (fun r hr y hy' => ?_)
  rotate_left
  · obtain ⟨h1, h2⟩ := hy y hy'
    have hre : 0 ≤ ((r : ℂ) * exp (((y + -(π / 4) : ℝ) : ℂ) * I)).re := by
      rw [q2a_re_ray]
      exact mul_nonneg hr.le (Real.cos_nonneg_of_mem_Icc ⟨h1, by linarith⟩)
    have hne : ((r : ℂ) * exp (((y + -(π / 4) : ℝ) : ℂ) * I)) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hr.ne') (exp_ne_zero _)
    have hd := q2a_differentiableAt_kernel a b (2 * I * ρ) hre hne
    rw [← hshift] at hd
    exact hd.comp (f := fun w : ℂ => w * ω) _ (differentiableAt_id.mul_const ω)
  · obtain ⟨h1, h2⟩ := hy y hy'
    rw [hshift]; exact (hC _ h1 h2).1 r hr hr1
  · obtain ⟨h1, h2⟩ := hy y hy'
    rw [hshift]; exact (hC _ h1 h2).2 r hr
  have hω2 : ∀ r : ℝ, (r : ℂ) * exp (((-(π / 4) : ℝ) : ℂ) * I) * ω =
      r * exp (-(π / 2) * I) := by
    intro r; rw [hshift]; push_cast; ring_nf
  simp only [hω2] at hrot
  have hΓ : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  rw [hrot, hω]
  have he : exp (((-(π / 4) : ℝ) : ℂ) * I) * exp (((-(π / 4) : ℝ) : ℂ) * I) =
      exp (-(π / 2) * I) := by rw [← exp_add]; push_cast; ring_nf
  generalize ∫ (r : ℝ) in Ioi 0, tricomiKernel a b (2 * I * ↑ρ) (↑r * cexp (-(↑π / 2) * I)) = J
  rw [← he]
  field_simp

/-- `(x u)^w = x^w u^w` for real `x > 0` and `u ≠ 0`. -/
lemma q2a_ofReal_mul_cpow {x : ℝ} (hx : 0 < x) {u : ℂ} (hu : u ≠ 0) (w : ℂ) :
    ((x : ℂ) * u) ^ w = (x : ℂ) ^ w * u ^ w := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hx0 hu), cpow_def_of_ne_zero hx0, cpow_def_of_ne_zero hu,
    log_ofReal_mul hx hu, ← exp_add, ← ofReal_log hx.le]
  ring_nf

/-- The kernel of `q2a_kummerU_two_I` at `a = ℓ+1-iη`, `b = 2ℓ+2` in terms of the integrand
of DLMF 33.7.2: `(2ρ)^{2ℓ} K(r e^{-iπ/2}) = (-1)^ℓ e^{-t} t^{ℓ-iη} (t+2iρ)^{ℓ+iη}`, `t = 2ρr`. -/
lemma q2a_kernel_eq (ℓ : ℕ) (η : ℝ) {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) :
    tricomiKernel ((ℓ : ℂ) + 1 - I * η) (2 * ℓ + 2) (2 * I * ρ) (r * exp (-(π / 2) * I)) *
      (2 * (ρ : ℂ)) ^ (2 * ℓ) = (-1) ^ ℓ * (exp (-((2 * ρ * r : ℝ) : ℂ)) *
        ((2 * ρ * r : ℝ) : ℂ) ^ ((ℓ : ℂ) - I * η) *
        (((2 * ρ * r : ℝ) : ℂ) + 2 * I * ρ) ^ ((ℓ : ℂ) + I * η)) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h2ρ : (0 : ℝ) < 2 * ρ := by positivity
  have hθ : (-(π / 2 : ℂ)) = ((-(π / 2) : ℝ) : ℂ) := by push_cast; ring
  have hmI : exp (((-(π / 2) : ℝ) : ℂ) * I) = -I := by
    rw [show (((-(π / 2) : ℝ) : ℂ) * I) = -(π / 2 * I) by push_cast; ring, exp_neg,
      exp_pi_div_two_mul_I, inv_I]
  have hri : (r : ℂ) + I ≠ 0 := fun h => by simpa using congrArg im h
  have harg0 : 0 ≤ arg ((r : ℂ) + I) := arg_nonneg_iff.mpr (by simp)
  have harg1 : arg ((r : ℂ) + I) ≤ π / 2 :=
    (abs_arg_le_pi_div_two_iff.mpr (by simp; linarith)).trans' (le_abs_self _)
  unfold tricomiKernel
  rw [hθ]
  have e1 : 1 + (r : ℂ) * exp (((-(π / 2) : ℝ) : ℂ) * I) =
      ((r : ℂ) + I) * exp (((-(π / 2) : ℝ) : ℂ) * I) := by
    rw [hmI]; linear_combination I_sq
  rw [e1, cpow_mul_exp_mul_I hr0 (by rw [arg_ofReal_of_nonneg hr.le]; linarith [Real.pi_pos])
      (by rw [arg_ofReal_of_nonneg hr.le]; linarith [Real.pi_pos]),
    cpow_mul_exp_mul_I hri (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  have e2 : ((2 * ρ * r : ℝ) : ℂ) = ((2 * ρ : ℝ) : ℂ) * r := by push_cast; ring
  have e3 : ((2 * ρ * r : ℝ) : ℂ) + 2 * I * ρ = ((2 * ρ : ℝ) : ℂ) * ((r : ℂ) + I) := by
    push_cast; ring
  rw [e3, e2, q2a_ofReal_mul_cpow h2ρ hr0, q2a_ofReal_mul_cpow h2ρ hri]
  have hP : ((2 * ρ : ℝ) : ℂ) ^ ((ℓ : ℂ) - I * η) * ((2 * ρ : ℝ) : ℂ) ^ ((ℓ : ℂ) + I * η) =
      (2 * (ρ : ℂ)) ^ (2 * ℓ) := by
    rw [← cpow_add _ _ (by exact_mod_cast h2ρ.ne'), show (ℓ : ℂ) - I * η + (ℓ + I * η) =
      ((2 * ℓ : ℕ) : ℂ) by push_cast; ring, cpow_natCast]
    push_cast; ring
  have hQ : exp (((-(π / 2) : ℝ) : ℂ) * I * ((ℓ : ℂ) + 1 - I * η - 1)) *
      exp (((-(π / 2) : ℝ) : ℂ) * I * (2 * ℓ + 2 - (ℓ + 1 - I * η) - 1)) = (-1) ^ ℓ := by
    rw [← exp_add, show ((-(π / 2) : ℝ) : ℂ) * I * ((ℓ : ℂ) + 1 - I * η - 1) +
      ((-(π / 2) : ℝ) : ℂ) * I * (2 * ℓ + 2 - (ℓ + 1 - I * η) - 1) = ℓ * (-(π * I)) by
      push_cast; ring, exp_nat_mul, exp_neg, exp_pi_mul_I]
    simp
  have hexp : exp (-(2 * I * (ρ : ℂ)) * ((r : ℂ) * exp (((-(π / 2) : ℝ) : ℂ) * I))) =
      exp (-(((2 * ρ : ℝ) : ℂ) * r)) := by
    rw [hmI]; congr 1; push_cast; linear_combination (2 * (ρ : ℂ) * r) * I_sq
  rw [show (ℓ : ℂ) - I * η = (ℓ : ℂ) + 1 - I * η - 1 by ring,
    show (ℓ : ℂ) + I * η = 2 * ℓ + 2 - (ℓ + 1 - I * η) - 1 by ring] at hP ⊢
  rw [hexp, ← hP, ← hQ]
  ring

/-- `conj (A⁺_ℓ) = e^{-iσ} e^{πη/2} 2^{ℓ+1} (-1)^ℓ i`. -/
lemma q2a_conj_APlus (ℓ : ℕ) (η : ℝ) :
    conj (coulombAPlus ℓ η) = exp (-(coulombSigma ℓ η * I)) * Real.exp (π * η / 2) *
      2 ^ (ℓ + 1) * (-1) ^ ℓ * I := by
  rw [coulombAPlus, map_mul, map_mul, map_mul, map_mul, ← exp_conj]
  simp only [map_mul, map_neg, map_ofNat, conj_ofReal, conj_I, map_pow, map_one, neg_neg]
  ring_nf

/-- `Γ(ℓ+1-iη) = |Γ(ℓ+1+iη)| e^{-iσ_ℓ}`. -/
lemma q2a_Gamma_conj_polar (ℓ : ℕ) (η : ℝ) :
    Gamma ((ℓ : ℂ) + 1 - I * η) =
      (‖Gamma ((ℓ : ℂ) + 1 + I * η)‖ : ℂ) * exp (-(coulombSigma ℓ η * I)) := by
  set g := Gamma ((ℓ : ℂ) + 1 + I * η) with hg
  have hgN : g = (‖g‖ : ℂ) * exp (arg g * I) := (norm_mul_exp_arg_mul_I g).symm
  have hc : (ℓ : ℂ) + 1 - I * η = conj ((ℓ : ℂ) + 1 + I * η) := by
    simp [map_add, conj_ofReal]; ring
  rw [hc, Gamma_conj, ← hg, show coulombSigma ℓ η = arg g from rfl]
  conv_lhs => rw [hgN]
  rw [map_mul, ← exp_conj, conj_ofReal]
  simp [map_mul, conj_ofReal, conj_I]

/-- `C_ℓ(η) (2ℓ+1)! = 2^ℓ e^{-πη/2} |Γ(ℓ+1+iη)|`. -/
lemma q2a_C_mul_factorial (ℓ : ℕ) (η : ℝ) :
    ((2 * ℓ + 1)! : ℂ) * coulombC ℓ η =
      2 ^ ℓ * ((Real.exp (π * η / 2) : ℝ) : ℂ)⁻¹ * ‖Gamma ((ℓ : ℂ) + 1 + I * η)‖ := by
  rw [coulombC]
  have hF : ((2 * ℓ + 1)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [show Real.exp (-π * η / 2) = (Real.exp (π * η / 2))⁻¹ by rw [← Real.exp_neg]; ring_nf]
  push_cast
  field_simp

/-- `conj (z^w) = (conj z)^(conj w)` for `arg z ≠ π`. -/
lemma q2a_conj_cpow {z : ℂ} (hz : z.arg ≠ π) (w : ℂ) : conj (z ^ w) = conj z ^ conj w := by
  rw [conj_cpow _ _ hz, conj_conj]

/-- The integrand of DLMF 33.7.4 on the ray `t = -1 - is` in terms of the conjugate of the
integrand of 33.7.2 at `t = ρs`. -/
lemma q2a_integrand_33_7_4 (ℓ : ℕ) (η : ℝ) {ρ s : ℝ} (hρ : 0 < ρ) (hs : 0 < s) :
    exp (-(I * ρ * (-1 - I * s))) * (2 + I * s) ^ ((ℓ : ℂ) - I * η) *
        (-(I * s)) ^ ((ℓ : ℂ) + I * η) * (-I) * (ρ : ℂ) ^ (2 * ℓ) =
      exp (I * ρ) * (-I) * exp (π * η) * (exp (-((ρ * s : ℝ) : ℂ)) *
        ((ρ * s : ℝ) : ℂ) ^ ((ℓ : ℂ) + I * η) *
        (((ρ * s : ℝ) : ℂ) - 2 * I * ρ) ^ ((ℓ : ℂ) - I * η)) := by
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hsi : (s : ℂ) - 2 * I ≠ 0 := fun h => by simpa using congrArg im h
  have hm : exp (((-(π / 2) : ℝ) : ℂ) * I) = -I := by
    rw [show (((-(π / 2) : ℝ) : ℂ) * I) = -(π / 2 * I) by push_cast; ring, exp_neg,
      exp_pi_div_two_mul_I, inv_I]
  have hp : exp (((π / 2 : ℝ) : ℂ) * I) = I := by
    rw [show (((π / 2 : ℝ) : ℂ) * I) = π / 2 * I by push_cast; ring, exp_pi_div_two_mul_I]
  have e1 : -(I * (s : ℂ)) = s * exp (((-(π / 2) : ℝ) : ℂ) * I) := by rw [hm]; ring
  have e2 : 2 + I * (s : ℂ) = ((s : ℂ) - 2 * I) * exp (((π / 2 : ℝ) : ℂ) * I) := by
    rw [hp]; linear_combination (2 : ℂ) * I_sq
  have harg0 : arg ((s : ℂ) - 2 * I) ≤ 0 := (arg_neg_iff.mpr (by simp)).le
  have harg1 : -(π / 2) ≤ arg ((s : ℂ) - 2 * I) := by
    have := (abs_arg_le_pi_div_two_iff.mpr (by simp; linarith : 0 ≤ ((s : ℂ) - 2 * I).re))
    linarith [neg_abs_le (arg ((s : ℂ) - 2 * I))]
  have hpi := Real.pi_pos
  rw [e1, e2, cpow_mul_exp_mul_I hs0 (by rw [arg_ofReal_of_nonneg hs.le]; linarith)
      (by rw [arg_ofReal_of_nonneg hs.le]; linarith),
    cpow_mul_exp_mul_I hsi (by linarith) (by linarith)]
  have e3 : ((ρ * s : ℝ) : ℂ) = (ρ : ℂ) * s := by push_cast; ring
  have e4 : ((ρ * s : ℝ) : ℂ) - 2 * I * ρ = (ρ : ℂ) * ((s : ℂ) - 2 * I) := by push_cast; ring
  rw [e4, e3, q2a_ofReal_mul_cpow hρ hs0, q2a_ofReal_mul_cpow hρ hsi]
  have hP : (ρ : ℂ) ^ ((ℓ : ℂ) + I * η) * (ρ : ℂ) ^ ((ℓ : ℂ) - I * η) = (ρ : ℂ) ^ (2 * ℓ) := by
    rw [← cpow_add _ _ (by exact_mod_cast hρ.ne'), show (ℓ : ℂ) + I * η + (ℓ - I * η) =
      ((2 * ℓ : ℕ) : ℂ) by push_cast; ring, cpow_natCast]
  have hQ : exp (((-(π / 2) : ℝ) : ℂ) * I * ((ℓ : ℂ) + I * η)) *
      exp (((π / 2 : ℝ) : ℂ) * I * ((ℓ : ℂ) - I * η)) = exp (π * η) := by
    rw [← exp_add]; congr 1; push_cast; linear_combination (-(π : ℂ) * η) * I_sq
  have hE : exp (-(I * ρ * (-1 - I * s))) = exp (I * ρ) * exp (-((ρ : ℂ) * s)) := by
    rw [← exp_add]; congr 1; linear_combination ((ρ : ℂ) * s) * I_sq
  rw [hE, ← hP, ← hQ]
  ring

end q2aRot

/-- **DLMF 33.7.2**: `H^-_ℓ(η,ρ) = e^{-iρ} ρ^{-ℓ}/((2ℓ+1)! C_ℓ(η))
∫_0^∞ e^{-t} t^{ℓ-iη} (t+2iρ)^{ℓ+iη} dt`, `ρ > 0`. -/
@[dlmf 33.7.E2]
theorem coulombHMinus_eq_integral (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun t : ℝ => exp (-(t : ℂ)) * (t : ℂ) ^ ((ℓ : ℂ) - I * η) *
        ((t : ℂ) + 2 * I * ρ) ^ ((ℓ : ℂ) + I * η)) (Ioi 0) ∧
    coulombHMinus ℓ η ρ = exp (-(I * ρ)) * ((ρ : ℂ) ^ ℓ)⁻¹ / ((2 * ℓ + 1)! * coulombC ℓ η) *
      ∫ t in Ioi (0 : ℝ), exp (-(t : ℂ)) * (t : ℂ) ^ ((ℓ : ℂ) - I * η) *
        ((t : ℂ) + 2 * I * ρ) ^ ((ℓ : ℂ) + I * η) := by
  set F : ℝ → ℂ := fun t => exp (-(t : ℂ)) * (t : ℂ) ^ ((ℓ : ℂ) - I * η) *
        ((t : ℂ) + 2 * I * ρ) ^ ((ℓ : ℂ) + I * η) with hF
  set a : ℂ := (ℓ : ℂ) + 1 - I * η with ha
  have hare : 0 < a.re := by simp [ha]; positivity
  obtain ⟨hint, hU⟩ := q2a_kummerU_two_I a (2 * ℓ + 2) hare hρ
  have h2ρ : (0 : ℝ) < 2 * ρ := by positivity
  have hP : (2 * (ρ : ℂ)) ^ (2 * ℓ) ≠ 0 := pow_ne_zero _ (by exact_mod_cast h2ρ.ne')
  set c : ℂ := (-1) ^ ℓ / (2 * (ρ : ℂ)) ^ (2 * ℓ) with hc
  have hk : ∀ r ∈ Ioi (0 : ℝ),
      tricomiKernel a (2 * ℓ + 2) (2 * I * ρ) (r * exp (-(π / 2) * I)) = c * F (2 * ρ * r) := by
    intro r hr
    have := q2a_kernel_eq ℓ η hρ hr
    rw [hc, div_mul_eq_mul_div, eq_div_iff hP]
    simpa only [hF] using this
  have hFint : IntegrableOn (fun r : ℝ => F (2 * ρ * r)) (Ioi 0) := by
    have hc0 : c ≠ 0 := div_ne_zero (pow_ne_zero _ (by norm_num)) hP
    have h1 : IntegrableOn (fun r : ℝ => c⁻¹ *
        tricomiKernel a (2 * ℓ + 2) (2 * I * ρ) (r * exp (-(π / 2) * I))) (Ioi 0) :=
      hint.const_mul c⁻¹
    refine h1.congr_fun (fun r hr => ?_) measurableSet_Ioi
    simp only
    rw [hk r hr, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hFint' := (integrableOn_Ioi_comp_mul_left_iff F 0 h2ρ).mp hFint
  rw [mul_zero] at hFint'
  refine ⟨hFint', ?_⟩
  have hI : ∫ r in Ioi (0 : ℝ), tricomiKernel a (2 * ℓ + 2) (2 * I * ρ) (r * exp (-(π / 2) * I))
      = c * ((2 * ρ : ℝ)⁻¹ : ℂ) * ∫ t in Ioi (0 : ℝ), F t := by
    rw [setIntegral_congr_fun measurableSet_Ioi hk, integral_const_mul,
      integral_comp_mul_left_Ioi F 0 h2ρ, mul_zero, Complex.real_smul, mul_assoc, ofReal_inv]
  rw [hI] at hU
  have hΓ : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos hare
  have hU' : kummerU a (2 * ℓ + 2) (2 * I * ρ) =
      (Gamma a)⁻¹ * (exp (-(π / 2) * I) * (c * ((2 * ρ : ℝ)⁻¹ : ℂ) * ∫ t in Ioi (0 : ℝ), F t)) := by
    rw [← hU]; field_simp
  rw [coulombHMinus_eq ℓ η hρ, ← ha, hU', q2a_Gamma_conj_polar, q2a_conj_APlus,
    q2a_C_mul_factorial]
  have hmI : exp (-(π / 2 : ℂ) * I) = -I := by
    rw [show (-(π / 2 : ℂ) * I) = -(π / 2 * I) by ring, exp_neg, exp_pi_div_two_mul_I, inv_I]
  rw [hmI, hc]
  set g := Gamma ((ℓ : ℂ) + 1 + I * η)
  have hgne : (‖g‖ : ℂ) ≠ 0 := by
    have : g ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; positivity)
    exact_mod_cast norm_ne_zero_iff.mpr this
  have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hr : ((Real.exp (π * η / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  have hsq : ((-1 : ℂ) ^ ℓ) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hEne := exp_ne_zero (-(coulombSigma ℓ η * I))
  generalize exp (-(coulombSigma ℓ η * I)) = E at *
  generalize ((Real.exp (π * η / 2) : ℝ) : ℂ) = R at *
  generalize (‖g‖ : ℂ) = N at *
  generalize ∫ t in Ioi (0 : ℝ), F t = J
  rw [neg_mul]
  generalize exp (-(I * ρ)) = X
  push_cast
  field_simp
  rw [hsq, I_sq, mul_pow, pow_mul, pow_mul]
  norm_num
  ring_nf
  rw [show (2 : ℂ) ^ (ℓ * 2) = 4 ^ ℓ by rw [mul_comm, pow_mul]; norm_num]

/-- **DLMF 33.7.3**: `H^-_ℓ(η,ρ) = -i e^{-πη} ρ^{ℓ+1}/((2ℓ+1)! C_ℓ(η))
∫_0^∞ (exp(-i(ρ tanh t - 2ηt))/(cosh t)^{2ℓ+2} + i (1+t²)^ℓ exp(-ρt + 2η arctan t)) dt`,
`ρ > 0`. -/
@[dlmf 33.7.E3]
theorem coulombHMinus_eq_integral_tanh (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun t : ℝ => exp (-(I * (ρ * Real.tanh t - 2 * η * t))) /
        (Real.cosh t : ℂ) ^ (2 * ℓ + 2) +
        I * ((1 + t ^ 2) ^ ℓ * Real.exp (-(ρ * t) + 2 * η * Real.arctan t) : ℝ)) (Ioi 0) ∧
    coulombHMinus ℓ η ρ = -I * Real.exp (-π * η) * (ρ : ℂ) ^ (ℓ + 1) /
        ((2 * ℓ + 1)! * coulombC ℓ η) *
      ∫ t in Ioi (0 : ℝ), (exp (-(I * (ρ * Real.tanh t - 2 * η * t))) /
        (Real.cosh t : ℂ) ^ (2 * ℓ + 2) +
        I * ((1 + t ^ 2) ^ ℓ * Real.exp (-(ρ * t) + 2 * η * Real.arctan t) : ℝ)) := by
  sorry

/-- **DLMF 33.7.4**: `H^+_ℓ(η,ρ) = i e^{-πη} ρ^{ℓ+1}/((2ℓ+1)! C_ℓ(η))
∫_{-1}^{-i∞} e^{-iρt} (1-t)^{ℓ-iη} (1+t)^{ℓ+iη} dt`, `ρ > 0`, along the ray `t = -1 - is`. -/
@[dlmf 33.7.E4]
theorem coulombHPlus_eq_integral (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun s : ℝ => exp (-(I * ρ * (-1 - I * s))) *
        (2 + I * s) ^ ((ℓ : ℂ) - I * η) * (-(I * s)) ^ ((ℓ : ℂ) + I * η) * (-I)) (Ioi 0) ∧
    coulombHPlus ℓ η ρ = I * Real.exp (-π * η) * (ρ : ℂ) ^ (ℓ + 1) /
        ((2 * ℓ + 1)! * coulombC ℓ η) *
      ∫ s in Ioi (0 : ℝ), exp (-(I * ρ * (-1 - I * s))) *
        (2 + I * s) ^ ((ℓ : ℂ) - I * η) * (-(I * s)) ^ ((ℓ : ℂ) + I * η) * (-I) := by
  obtain ⟨hFint, hEq⟩ := coulombHMinus_eq_integral ℓ η hρ
  set F : ℝ → ℂ := fun t => exp (-(t : ℂ)) * (t : ℂ) ^ ((ℓ : ℂ) - I * η) *
        ((t : ℂ) + 2 * I * ρ) ^ ((ℓ : ℂ) + I * η) with hF
  set G : ℝ → ℂ := fun t => exp (-(t : ℂ)) * (t : ℂ) ^ ((ℓ : ℂ) + I * η) *
        ((t : ℂ) - 2 * I * ρ) ^ ((ℓ : ℂ) - I * η) with hG
  have hGF : ∀ t ∈ Ioi (0 : ℝ), conj (F t) = G t := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h1 : ((t : ℂ)).arg ≠ π := by
      rw [arg_ofReal_of_nonneg ht'.le]; exact Real.pi_pos.ne
    have h2 : ((t : ℂ) + 2 * I * ρ).arg ≠ π := by
      refine slitPlane_arg_ne_pi (Or.inl ?_)
      simp; exact ht'
    simp only [hF, hG, map_mul, q2a_conj_cpow h1, q2a_conj_cpow h2, ← exp_conj]
    simp [map_sub, map_add, conj_ofReal, conj_I, map_natCast, map_ofNat]
    ring_nf
    simp
  have hGint : IntegrableOn G (Ioi 0) := by
    have h := (conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp hFint
    refine IntegrableOn.congr_fun (f := fun t => conj (F t)) h (fun t ht => hGF t ht)
      measurableSet_Ioi
  have hGI : ∫ t in Ioi (0 : ℝ), G t = conj (∫ t in Ioi (0 : ℝ), F t) := by
    rw [← integral_conj]; exact (setIntegral_congr_fun measurableSet_Ioi hGF).symm
  set c : ℂ := exp (I * ρ) * (-I) * exp (π * η) / (ρ : ℂ) ^ (2 * ℓ) with hc
  have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hT : ∀ s ∈ Ioi (0 : ℝ), exp (-(I * ρ * (-1 - I * s))) *
      (2 + I * s) ^ ((ℓ : ℂ) - I * η) * (-(I * s)) ^ ((ℓ : ℂ) + I * η) * (-I) =
      c * G (ρ * s) := by
    intro s hs
    have := q2a_integrand_33_7_4 ℓ η hρ hs
    rw [hc, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero _ hρ0)]
    simpa only [hG] using this
  have hGs : IntegrableOn (fun s : ℝ => G (ρ * s)) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff G 0 hρ).mpr (by rwa [mul_zero])
    exact this
  have hGc : IntegrableOn (fun s : ℝ => c * G (ρ * s)) (Ioi 0) := hGs.const_mul c
  refine ⟨hGc.congr_fun (fun s hs => (hT s hs).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hT, integral_const_mul,
    integral_comp_mul_left_Ioi G 0 hρ, mul_zero, Complex.real_smul, ofReal_inv, hGI]
  have hHP : coulombHPlus ℓ η ρ = conj (coulombHMinus ℓ η ρ) := by
    rw [coulombHMinus_eq_conj ℓ η hρ, conj_conj]
  rw [hHP, hEq]
  simp only [map_mul, map_div₀, map_inv₀, map_pow, conj_ofReal, map_natCast, ← exp_conj,
    map_neg, conj_I]
  have hF0 : ((2 * ℓ + 1)! : ℂ) * coulombC ℓ η ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _)
      (by exact_mod_cast (coulombC_pos ℓ η).ne')
  have hex : ((Real.exp (-π * η) : ℝ) : ℂ) * exp (π * η) = 1 := by
    rw [ofReal_exp, ← exp_add]; push_cast; ring_nf; exact exp_zero
  rw [hc]
  generalize conj (∫ t in Ioi (0 : ℝ), F t) = J
  field_simp
  rw [show -(π * η) = -π * η by ring]
  set B := (ρ : ℂ) ^ ℓ * J * (ρ : ℂ) ^ (ℓ + 1) / (((2 * ℓ + 1)! : ℕ) * (coulombC ℓ η : ℂ))
  linear_combination (((Real.exp (-π * η) : ℝ) : ℂ) * exp (π * η) * B) * I_sq - B * hex

/-! ### §33.8 Continued fractions -/

section q2aCF

open DLMF.Hypergeometric

/-- The factor `(m+1-iη+n)/(2m+2+n)` tends to `1/2`. -/
lemma q2a_factor_tendsto (η : ℝ) (n : ℕ) :
    Tendsto (fun m : ℕ => ((m : ℂ) + 1 - I * η + n) / (2 * (m : ℂ) + 2 + n)) atTop
      (𝓝 (1 / 2)) := by
  have h1 : Tendsto (fun m : ℕ => 2 * (m : ℝ) + 2 + n) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _
      (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos))
  have h2 := (continuous_ofReal.tendsto 0).comp h1.inv_tendsto_atTop
  rw [ofReal_zero] at h2
  have hinv : Tendsto (fun m : ℕ => (2 * (m : ℂ) + 2 + n)⁻¹) atTop (𝓝 0) := by
    refine h2.congr fun m => ?_
    simp
  have h := (hinv.const_mul ((n : ℂ) / 2 - I * η)).const_add (1 / 2 : ℂ)
  rw [mul_zero, add_zero] at h
  refine h.congr fun m => ?_
  have hne : (2 * (m : ℂ) + 2 + n) ≠ 0 := by
    have : (0 : ℝ) < 2 * (m : ℝ) + 2 + n := by positivity
    exact_mod_cast this.ne'
  have hD : (2 * (m : ℂ) + 2 + n) * (2 * (m : ℂ) + 2 + n)⁻¹ = 1 := mul_inv_cancel₀ hne
  rw [div_eq_mul_inv]
  linear_combination (-(1 / 2 : ℂ)) * hD

/-- The factor `(m+1-iη+n)/(2m+2+n)` has modulus at most `1` when `|η| ≤ m`. -/
lemma q2a_factor_norm_le (η : ℝ) (n : ℕ) {m : ℕ} (hm : |η| ≤ m) :
    ‖((m : ℂ) + 1 - I * η + n) / (2 * (m : ℂ) + 2 + n)‖ ≤ 1 := by
  have hpos : (0 : ℝ) < 2 * (m : ℝ) + 2 + n := by positivity
  rw [norm_div, show (2 * (m : ℂ) + 2 + n) = ((2 * (m : ℝ) + 2 + n : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_of_nonneg hpos.le, div_le_one hpos,
    show (m : ℂ) + 1 - I * η + n = ⟨(m : ℝ) + 1 + n, -η⟩ by
      apply Complex.ext <;> simp,
    Complex.norm_eq_sqrt_sq_add_sq]
  apply Real.sqrt_le_iff.mpr
  refine ⟨hpos.le, ?_⟩
  have h1 : η ^ 2 ≤ (m : ℝ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg η) hm 2
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- `(m+1-iη)_n/(2m+2)_n → 2^{-n}` as `m → ∞`. -/
lemma q2a_poch_ratio_tendsto (η : ℝ) (n : ℕ) :
    Tendsto (fun m : ℕ => poch ((m : ℂ) + 1 - I * η) n / poch (2 * (m : ℂ) + 2) n) atTop
      (𝓝 ((1 / 2) ^ n)) := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [pow_succ]
    refine (ih.mul (q2a_factor_tendsto η n)).congr fun m => ?_
    rw [poch_succ, poch_succ, mul_div_mul_comm]

/-- `|(m+1-iη)_n/(2m+2)_n| ≤ 1` when `|η| ≤ m`. -/
lemma q2a_poch_ratio_norm_le (η : ℝ) (n : ℕ) {m : ℕ} (hm : |η| ≤ m) :
    ‖poch ((m : ℂ) + 1 - I * η) n / poch (2 * (m : ℂ) + 2) n‖ ≤ 1 := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [poch_succ, poch_succ, mul_div_mul_comm, norm_mul]
    have := q2a_factor_norm_le η n hm
    nlinarith [norm_nonneg (poch ((m : ℂ) + 1 - I * η) n / poch (2 * (m : ℂ) + 2) n)]

/-- `M(m+1-iη, 2m+2, z) → e^{z/2}` as `m → ∞`. -/
lemma q2a_tendsto_kummerM_large (η : ℝ) (z : ℂ) :
    Tendsto (fun m : ℕ => kummerM ((m : ℂ) + 1 - I * η) (2 * m + 2) z) atTop
      (𝓝 (exp (z / 2))) := by
  have hexp : exp (z / 2) = ∑' n : ℕ, (z / 2) ^ n / (n ! : ℂ) :=
    (by simpa only [exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (z / 2) :
        HasSum (fun n : ℕ => (z / 2) ^ n / n !) (exp (z / 2))).tsum_eq.symm
  rw [hexp]
  unfold kummerM
  refine tendsto_tsum_of_dominated_convergence (bound := fun n => ‖z‖ ^ n / n !)
    (Real.summable_pow_div_factorial ‖z‖) (fun n => ?_) ?_
  · have := ((q2a_poch_ratio_tendsto η n).div_const (n ! : ℂ)).mul_const (z ^ n)
    have he : (1 / 2 : ℂ) ^ n / (n ! : ℂ) * z ^ n = (z / 2) ^ n / (n ! : ℂ) := by
      rw [div_pow, div_pow, one_pow]; ring
    rw [he] at this
    refine this.congr fun m => ?_
    field_simp
  · filter_upwards [eventually_ge_atTop (Nat.ceil |η|)] with m hm n
    have hm' : |η| ≤ m := (Nat.le_ceil _).trans (by exact_mod_cast hm)
    have hb := q2a_poch_ratio_norm_le η n hm'
    rw [show poch ((m : ℂ) + 1 - I * η) n / (poch (2 * (m : ℂ) + 2) n * n !) * z ^ n =
      poch ((m : ℂ) + 1 - I * η) n / poch (2 * (m : ℂ) + 2) n * (z ^ n / n !) by ring,
      norm_mul]
    have : ‖z ^ n / (n ! : ℂ)‖ = ‖z‖ ^ n / n ! := by
      rw [norm_div, norm_pow, Complex.norm_natCast]
    rw [this]
    exact mul_le_of_le_one_left (by positivity) hb

/-- The normalized Kummer factor `u_m = e^{-iρ} M(m+1-iη, 2m+2, 2iρ)` of `F_m`. -/
def q2a_u (η ρ : ℝ) (m : ℕ) : ℂ :=
  exp (-I * ρ) * kummerM ((m : ℂ) + 1 - I * η) (2 * m + 2) (2 * I * ρ)

/-- `|F_m(η,ρ)| = C_m ρ^{m+1} ‖u_m‖` for `ρ > 0`. -/
lemma q2a_abs_coulombF (m : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    |coulombF m η ρ| = coulombC m η * ρ ^ (m + 1) * ‖q2a_u η ρ m‖ := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real, ofReal_coulombF, coulombWave, q2a_u]
  rw [show ((ρ : ℂ) ^ (m + 1) * exp (-I * ρ) *
      kummerM ((m : ℂ) + 1 - I * η) (2 * m + 2) (2 * I * ρ)) =
      (ρ : ℂ) ^ (m + 1) * (exp (-I * ρ) *
        kummerM ((m : ℂ) + 1 - I * η) (2 * m + 2) (2 * I * ρ)) by ring,
    norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (coulombC_pos m η).le, Real.norm_of_nonneg hρ.le]
  ring

/-- `u_m → 1` as `m → ∞`. -/
lemma q2a_tendsto_u (η ρ : ℝ) : Tendsto (q2a_u η ρ) atTop (𝓝 1) := by
  have h := (q2a_tendsto_kummerM_large η (2 * I * ρ)).const_mul (exp (-I * ρ))
  rwa [← Complex.exp_add, show -I * (ρ : ℂ) + 2 * I * ρ / 2 = 0 by ring, Complex.exp_zero] at h

/-- `R_m² ≤ 1 + η²` for every `m`. -/
lemma q2a_recurrenceR_sq_le (m : ℕ) (η : ℝ) : recurrenceR m η ^ 2 ≤ 1 + η ^ 2 := by
  rw [recurrenceR, Real.sq_sqrt (by positivity)]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp; positivity
  · have : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hm)
    have : η ^ 2 / (m : ℝ) ^ 2 ≤ η ^ 2 := div_le_self (sq_nonneg η) this
    linarith

/-- `R_m > 0`. -/
lemma q2a_recurrenceR_pos (m : ℕ) (η : ℝ) : 0 < recurrenceR m η := by
  rw [recurrenceR]; exact Real.sqrt_pos.mpr (by positivity)

/-- `C_{m+2} = C_m R_{m+1} R_{m+2} / ((2m+3)(2m+5))`. -/
lemma q2a_coulombC_add_two (m : ℕ) (η : ℝ) :
    coulombC (m + 2) η = coulombC m η * recurrenceR (m + 1) η * recurrenceR (m + 2) η /
      ((2 * m + 3) * (2 * m + 5)) := by
  have h1 := recurrenceR_eq_coulombC_div m η
  have h2 := recurrenceR_eq_coulombC_div (m + 1) η
  have c0 := (coulombC_pos m η).ne'
  have c1 := (coulombC_pos (m + 1) η).ne'
  rw [h1, h2]
  push_cast
  field_simp
  ring

/-- The scaled backward solution `w_k = F_{ℓ+k} / ∏_{j<k} R_{ℓ+1+j}` of the Coulomb
recurrence in continued-fraction form. -/
def q2a_w (ℓ : ℕ) (η ρ : ℝ) (k : ℕ) : ℝ :=
  coulombF (ℓ + k) η ρ / ∏ j ∈ Finset.range k, recurrenceR (ℓ + 1 + j) η

/-- The products `∏_{j<k} R_{ℓ+1+j}` are positive. -/
lemma q2a_prod_pos (ℓ : ℕ) (η : ℝ) (k : ℕ) :
    0 < ∏ j ∈ Finset.range k, recurrenceR (ℓ + 1 + j) η :=
  Finset.prod_pos fun _ _ => q2a_recurrenceR_pos _ η

/-- The backward solution satisfies `w_k = T_{ℓ+1+k} w_{k+1} - R_{ℓ+2+k}² w_{k+2}`. -/
lemma q2a_w_rec (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    q2a_w ℓ η ρ k = recurrenceT (ℓ + 1 + k) η ρ * q2a_w ℓ η ρ (k + 1) +
      -(recurrenceR (ℓ + 1 + (k + 1)) η ^ 2) * q2a_w ℓ η ρ (k + 2) := by
  have hr := coulombF_recurrence (ℓ + k) η hρ
  have p0 := (q2a_prod_pos ℓ η k).ne'
  simp only [q2a_w, Finset.prod_range_succ]
  generalize ∏ j ∈ Finset.range k, recurrenceR (ℓ + 1 + j) η = p at p0 ⊢
  rw [show ℓ + 1 + (k + 1) = ℓ + k + 2 by ring, show ℓ + 1 + k = ℓ + k + 1 by ring,
    show ℓ + (k + 1) = ℓ + k + 1 by ring, show ℓ + (k + 2) = ℓ + k + 2 by ring]
  have r1 := (q2a_recurrenceR_pos (ℓ + k + 1) η).ne'
  have r2 := (q2a_recurrenceR_pos (ℓ + k + 2) η).ne'
  have key : coulombF (ℓ + k) η ρ / p - (recurrenceT (ℓ + k + 1) η ρ *
      (coulombF (ℓ + k + 1) η ρ / (p * recurrenceR (ℓ + k + 1) η)) +
      -recurrenceR (ℓ + k + 2) η ^ 2 * (coulombF (ℓ + k + 2) η ρ /
        (p * recurrenceR (ℓ + k + 1) η * recurrenceR (ℓ + k + 2) η))) =
      (recurrenceR (ℓ + k + 1) η * coulombF (ℓ + k) η ρ -
        recurrenceT (ℓ + k + 1) η ρ * coulombF (ℓ + k + 1) η ρ +
        recurrenceR (ℓ + k + 2) η * coulombF (ℓ + k + 2) η ρ) /
        (p * recurrenceR (ℓ + k + 1) η) := by
    field_simp
    ring
  rw [hr, zero_div, sub_eq_zero] at key
  exact key

/-- **DLMF 33.8.1** via the ratio criterion, as a real convergence statement. -/
lemma q2a_contFrac_real (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hF : coulombF ℓ η ρ ≠ 0) :
    Tendsto (GenContFract.cfConv_ofFun 0 (fun k => -(recurrenceR (ℓ + 1 + k) η ^ 2))
      (fun k => recurrenceT (ℓ + 1 + k) η ρ)).convs atTop
      (𝓝 (deriv (coulombF ℓ η) ρ / coulombF ℓ η ρ - recurrenceS (ℓ + 1) η ρ)) := by
  obtain ⟨M0, hM0⟩ := eventually_atTop.mp
    ((q2a_tendsto_u η ρ).eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0:ℝ) < 1/2)))
  have hu_lo : ∀ m ≥ M0, 1 / 2 ≤ ‖q2a_u η ρ m‖ := by
    intro m hm
    have h := hM0 m hm
    rw [dist_eq_norm] at h
    have := norm_sub_norm_le (1 : ℂ) (q2a_u η ρ m)
    rw [norm_one, norm_sub_rev] at this
    linarith
  have hu_hi : ∀ m ≥ M0, ‖q2a_u η ρ m‖ ≤ 2 := by
    intro m hm
    have h := hM0 m hm
    rw [dist_eq_norm] at h
    have := norm_le_norm_add_norm_sub' (q2a_u η ρ m) 1
    rw [norm_one] at this
    linarith
  have habs := fun m => q2a_abs_coulombF m η hρ
  set N := max M0 (Nat.ceil (12 * (1 + η ^ 2) * ρ ^ 2)) with hN
  have hw0 : q2a_w ℓ η ρ 0 ≠ 0 := by simpa [q2a_w] using hF
  have ha : ∀ k, -(recurrenceR (ℓ + 1 + k) η ^ 2) ≠ 0 := fun k =>
    neg_ne_zero.mpr (pow_ne_zero _ (q2a_recurrenceR_pos _ η).ne')
  have hwN : ∀ k ≥ N, q2a_w ℓ η ρ k ≠ 0 := by
    intro k hk
    have hm : ℓ + k ≥ M0 := le_trans (le_max_left _ _) (hk.trans (Nat.le_add_left _ _))
    simp only [q2a_w]
    refine div_ne_zero ?_ (q2a_prod_pos ℓ η k).ne'
    rw [← abs_pos, habs]
    have := hu_lo _ hm
    have := coulombC_pos (ℓ + k) η
    positivity
  have hrat : ∀ k ≥ N, 3 * ‖-(recurrenceR (ℓ + 1 + (k + 1)) η ^ 2) * q2a_w ℓ η ρ (k + 2)‖ ≤
      ‖q2a_w ℓ η ρ k‖ := by
    intro k hk
    have hmM : ℓ + k ≥ M0 := le_trans (le_max_left _ _) (hk.trans (Nat.le_add_left _ _))
    have hmC : 12 * (1 + η ^ 2) * ρ ^ 2 ≤ ((ℓ + k : ℕ) : ℝ) := by
      have := Nat.le_ceil (12 * (1 + η ^ 2) * ρ ^ 2)
      have h2 : Nat.ceil (12 * (1 + η ^ 2) * ρ ^ 2) ≤ ℓ + k :=
        le_trans (le_max_right _ _) (hk.trans (Nat.le_add_left _ _))
      exact this.trans (by exact_mod_cast h2)
    have p0 := q2a_prod_pos ℓ η k
    simp only [q2a_w, Finset.prod_range_succ]
    generalize ∏ j ∈ Finset.range k, recurrenceR (ℓ + 1 + j) η = p at p0 ⊢
    rw [show ℓ + 1 + (k + 1) = ℓ + k + 2 by ring, show ℓ + 1 + k = ℓ + k + 1 by ring,
      show ℓ + (k + 2) = ℓ + k + 2 by ring]
    generalize ℓ + k = m at hmM hmC ⊢
    simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_neg]
    rw [habs, habs, q2a_coulombC_add_two]
    have r1 := q2a_recurrenceR_pos (m + 1) η
    have r2 := q2a_recurrenceR_pos (m + 2) η
    have c0 := coulombC_pos m η
    rw [abs_of_pos p0, abs_of_pos r1, abs_of_pos r2, abs_of_pos (by positivity : (0:ℝ) <
      recurrenceR (m + 2) η ^ 2)]
    have hlo := hu_lo m hmM
    have hhi := hu_hi (m + 2) (by omega)
    have hR := q2a_recurrenceR_sq_le (m + 2) η
    generalize ‖q2a_u η ρ m‖ = U0 at hlo ⊢
    have hU2 := norm_nonneg (q2a_u η ρ (m + 2))
    generalize ‖q2a_u η ρ (m + 2)‖ = U2 at hhi hU2 ⊢
    have hmpos : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hD : (0 : ℝ) < (2 * m + 3) * (2 * m + 5) := by positivity
    have key : 3 * recurrenceR (m + 2) η ^ 2 * ρ ^ 2 * U2 / ((2 * m + 3) * (2 * m + 5)) ≤ U0 := by
      rw [div_le_iff₀ hD]
      have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
      calc 3 * recurrenceR (m + 2) η ^ 2 * ρ ^ 2 * U2
          ≤ 3 * (1 + η ^ 2) * ρ ^ 2 * 2 := by gcongr
        _ ≤ (1 / 2 : ℝ) * ((2 * (m : ℝ) + 3) * (2 * m + 5)) := by nlinarith
        _ ≤ U0 * ((2 * (m : ℝ) + 3) * (2 * m + 5)) := by gcongr
    have hcp : 0 ≤ coulombC m η * ρ ^ (m + 1) / p := by positivity
    calc 3 * (recurrenceR (m + 2) η ^ 2 * (coulombC m η * recurrenceR (m + 1) η *
            recurrenceR (m + 2) η / ((2 * m + 3) * (2 * m + 5)) * ρ ^ (m + 2 + 1) * U2 /
            (p * recurrenceR (m + 1) η * recurrenceR (m + 2) η)))
        = 3 * recurrenceR (m + 2) η ^ 2 * ρ ^ 2 * U2 / ((2 * m + 3) * (2 * m + 5)) *
            (coulombC m η * ρ ^ (m + 1) / p) := by
          field_simp
          ring
      _ ≤ U0 * (coulombC m η * ρ ^ (m + 1) / p) := mul_le_mul_of_nonneg_right key hcp
      _ = coulombC m η * ρ ^ (m + 1) * U0 / p := by ring
  have := GenContFract.cfConv_tendsto_of_ratio (h := (0 : ℝ)) (q2a_w_rec ℓ η hρ) hw0 ha hwN
    (by norm_num : (2:ℝ) < 3) hrat
  convert this using 2
  simp only [q2a_w, Finset.range_zero, Finset.prod_empty, div_one, zero_add,
    Finset.prod_range_one, add_zero]
  rw [deriv_coulombF_upper ℓ η hρ]
  have r1 := (q2a_recurrenceR_pos (ℓ + 1) η).ne'
  field_simp
  ring

end q2aCF

/-- **DLMF 33.8.1**: `F_ℓ'/F_ℓ = S_{ℓ+1} - R_{ℓ+1}²/(T_{ℓ+1} - R_{ℓ+2}²/(T_{ℓ+2} - ⋯))`,
for `ρ > 0` with `F_ℓ(η,ρ) ≠ 0`; the continued fraction converges for all finite `ρ`
(DLMF §33.8). -/
@[dlmf 33.8.E1]
theorem coulombF_logDeriv_contFrac (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hF : coulombF ℓ η ρ ≠ 0) :
    DLMF.HasContinuedFraction (fun k => (-(recurrenceR (ℓ + 1 + k) η ^ 2) : ℝ))
      (fun k => (recurrenceT (ℓ + 1 + k) η ρ : ℝ))
      ((deriv (coulombF ℓ η) ρ / coulombF ℓ η ρ - recurrenceS (ℓ + 1) η ρ : ℝ)) := by
  have ha : ∀ k, 1 ≤ k → -(recurrenceR (ℓ + 1 + k) η ^ 2) ≠ 0 := fun k _ =>
    neg_ne_zero.mpr (pow_ne_zero _ (q2a_recurrenceR_pos _ η).ne')
  unfold DLMF.HasContinuedFraction
  rw [funext (incGF_cfTail_ofReal (fun _ => rfl) (fun _ => rfl) ha)]
  exact (continuous_ofReal.tendsto _).comp (q2a_contFrac_real ℓ η hρ hF)

/-- **DLMF 33.8.2–33.8.3**, upper sign: `H^+_ℓ'/H^+_ℓ = c + (i/ρ) ab/(2(ρ-η+i) +
(a+1)(b+1)/(2(ρ-η+2i) + ⋯))` with `a = 1+ℓ+iη`, `b = -ℓ+iη`, `c = i(1-η/ρ)`, `ρ > 0`. -/
@[dlmf 33.8.E2, dlmf 33.8.E3]
theorem coulombHPlus_logDeriv_contFrac (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    DLMF.HasContinuedFraction
      (fun k : ℕ => ((1 : ℂ) + ℓ + I * η + k) * (-(ℓ : ℂ) + I * η + k))
      (fun k : ℕ => 2 * ((ρ : ℂ) - η + I * (k + 1)))
      ((deriv (fun x : ℝ => coulombHPlus ℓ η x) ρ / coulombHPlus ℓ η ρ -
        I * (1 - η / ρ)) / (I / ρ)) := by
  sorry

/-- **DLMF 33.8.2–33.8.3**, lower sign: `H^-_ℓ'/H^-_ℓ = c - (i/ρ) ab/(2(ρ-η-i) +
(a+1)(b+1)/(2(ρ-η-2i) + ⋯))` with `a = 1+ℓ-iη`, `b = -ℓ-iη`, `c = -i(1-η/ρ)`, `ρ > 0`. -/
@[dlmf 33.8.E2, dlmf 33.8.E3]
theorem coulombHMinus_logDeriv_contFrac (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    DLMF.HasContinuedFraction
      (fun k : ℕ => ((1 : ℂ) + ℓ - I * η + k) * (-(ℓ : ℂ) - I * η + k))
      (fun k : ℕ => 2 * ((ρ : ℂ) - η - I * (k + 1)))
      ((deriv (fun x : ℝ => coulombHMinus ℓ η x) ρ / coulombHMinus ℓ η ρ +
        I * (1 - η / ρ)) / (-I / ρ)) := by
  sorry

/-- **Barnett's formulas** (DLMF 33.8.4–33.8.5): with `u = F_ℓ'/F_ℓ` and
`p + iq = H^+_ℓ'/H^+_ℓ` (`ρ > 0`, `F_ℓ(η,ρ) ≠ 0`),
`F_ℓ = ±(q⁻¹(u-p)² + q)^{-1/2}` (stated as `F_ℓ² (q⁻¹(u-p)² + q) = 1`), `F_ℓ' = u F_ℓ`,
`G_ℓ = q⁻¹(u-p) F_ℓ`, `G_ℓ' = q⁻¹(up - p² - q²) F_ℓ`. -/
@[dlmf 33.8.E4, dlmf 33.8.E5]
theorem coulomb_barnett (ℓ : ℕ) (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (hF : coulombF ℓ η ρ ≠ 0)
    {u p q : ℝ} (hu : u = deriv (coulombF ℓ η) ρ / coulombF ℓ η ρ)
    (hpq : deriv (fun x : ℝ => coulombHPlus ℓ η x) ρ / coulombHPlus ℓ η ρ = p + q * I) :
    coulombF ℓ η ρ ^ 2 * (q⁻¹ * (u - p) ^ 2 + q) = 1 ∧
      deriv (coulombF ℓ η) ρ = u * coulombF ℓ η ρ ∧
      coulombG ℓ η ρ = q⁻¹ * (u - p) * coulombF ℓ η ρ ∧
      deriv (coulombG ℓ η) ρ = q⁻¹ * (u * p - p ^ 2 - q ^ 2) * coulombF ℓ η ρ := by
  set F := coulombF ℓ η ρ
  set G := coulombG ℓ η ρ
  set F' := deriv (coulombF ℓ η) ρ
  set G' := deriv (coulombG ℓ η) ρ
  have hW : G * F' - G' * F = 1 := coulomb_wronskian ℓ η hρ
  have hH : coulombHPlus ℓ η ρ = G + I * F := (coulombH_eq_G_add_I_mul_F ℓ η hρ).1
  have hH' : deriv (fun x : ℝ => coulombHPlus ℓ η x) ρ = G' + I * F' :=
    (c33a_hasDerivAt_coulombHPlus ℓ η hρ).deriv
  have hN : 0 < F ^ 2 + G ^ 2 := by positivity
  have hHne : (G : ℂ) + I * F ≠ 0 := by
    intro h
    have h1 := congrArg Complex.im h
    simp at h1
    exact hF h1
  rw [hH, hH'] at hpq
  have hmul : (G' : ℂ) + I * F' = (p + q * I) * (G + I * F) := by
    rw [← hpq, div_mul_cancel₀ _ hHne]
  have hre := congrArg Complex.re hmul
  have him := congrArg Complex.im hmul
  simp at hre him
  have hF' : F' = p * F + q * G := by linarith
  have hG' : G' = p * G - q * F := by linarith
  have hq : q * (F ^ 2 + G ^ 2) = 1 := by rw [hF', hG'] at hW; linear_combination hW
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hu2 : u = p + q * G / F := by rw [hu, hF']; field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : F ^ 2 * (q⁻¹ * (u - p) ^ 2 + q) = q * (F ^ 2 + G ^ 2) := by
      rw [hu2]; field_simp; ring
    rw [this, hq]
  · rw [hu2, hF']; field_simp
  · rw [hu2]; field_simp; ring
  · rw [hG', hu2]; field_simp; ring

end DLMF.Coulomb
