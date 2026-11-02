/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The perturbed harmonic oscillator

For `y'' = -(k² + Q(x)) y` with a bounded complex perturbation `Q` and large real `k`, the
solution stays within `O(1/k)` of the solution `a cos kx + b sin kx / k` of the unperturbed
equation with the same data, and its derivative within `O(1/k)` of `-ak sin kx + b cos kx`
(relative to the size `‖b‖ + k ‖a‖` of the data). This gives, for example, the asymptotic form
`Δ(k²) = 2 cos kπ + O(1/k)` of the discriminant of Hill's equation.

## Main results

* `ODE.energy_sub_harmonic_le`: the energy `‖d'‖² + k² ‖d‖²` of the deviation `d` from the
  unperturbed solution is at most `M² (‖b‖² + k² ‖a‖²) e^{(M+1)L} / k²` on `[0, L]`, where
  `‖Q‖ ≤ M`.
-/

@[expose] public section

open Set Filter Real

namespace ODE

/-- Energy identity for `f'' = -k² f - R`: `(‖f'‖² + k² ‖f‖²)' = -2 ⟪f', R⟫`. -/
private lemma hasDerivAt_energy {f f' R : ℝ → ℂ} {k : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (-((k : ℂ) ^ 2) * f x - R x) x) (x : ℝ) :
    HasDerivAt (fun x => ‖f' x‖ ^ 2 + k ^ 2 * ‖f x‖ ^ 2)
      (-2 * inner ℝ (f' x) (R x)) x := by
  have h := ((hf' x).norm_sq).add (((hf x).norm_sq).const_mul (k ^ 2))
  convert h using 1
  have e : -((k : ℂ) ^ 2) * f x = (-(k ^ 2) : ℝ) • f x := by
    rw [Complex.real_smul]; push_cast; ring
  rw [inner_sub_right, e, real_inner_smul_right, real_inner_comm (f x) (f' x)]
  ring

/-- An energy that grows at most like `E' ≤ K E + ε` from `E(0) ≤ δ`. -/
private lemma energy_le_gronwall {E E' : ℝ → ℝ} {δ K ε L : ℝ}
    (hE : ∀ x, HasDerivAt E (E' x) x) (h0 : E 0 ≤ δ)
    (hb : ∀ x ∈ Ico 0 L, E' x ≤ K * E x + ε) {x : ℝ} (hx : x ∈ Icc 0 L) :
    E x ≤ gronwallBound δ K ε x := by
  have := le_gronwallBound_of_liminf_deriv_right_le (f := E) (f' := E') (a := 0) (b := L)
    (fun x _ => (hE x).continuousAt.continuousWithinAt)
    (fun x _ r hr => (hE x).hasDerivWithinAt.liminf_right_slope_le hr) h0 hb x hx
  simpa using this

/-- **Perturbed harmonic oscillator.** Let `y'' = -(k² + Q) y` on `ℝ` (complex values), with
`‖Q‖ ≤ M` on `[0, L]` and `k ≥ 1`, and let `y(0) = a`, `y'(0) = b`. Then the deviation
`d = y - (a cos kx + b sin kx / k)` from the unperturbed solution satisfies
`‖d'(x)‖² + k² ‖d(x)‖² ≤ M² (‖b‖² + k² ‖a‖²) e^{(M+1)L} / k²` on `[0, L]`. -/
theorem energy_sub_harmonic_le {Q y y' : ℝ → ℂ} {M L k : ℝ} {a b : ℂ} (hM : 0 ≤ M)
    (hk : 1 ≤ k) (hQ : ∀ x ∈ Icc 0 L, ‖Q x‖ ≤ M)
    (hy : ∀ x, HasDerivAt y (y' x) x)
    (hy' : ∀ x, HasDerivAt y' (-((k : ℂ) ^ 2 + Q x) * y x) x) (h0 : y 0 = a) (h1 : y' 0 = b)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    ‖y' x - (-(a * k * Real.sin (k * x)) + b * Real.cos (k * x))‖ ^ 2 +
        k ^ 2 * ‖y x - (a * Real.cos (k * x) + b * Real.sin (k * x) / k)‖ ^ 2 ≤
      M ^ 2 * (‖b‖ ^ 2 + k ^ 2 * ‖a‖ ^ 2) * Real.exp ((M + 1) * L) / k ^ 2 := by
  have hk0 : 0 < k := by linarith
  set E0 := ‖b‖ ^ 2 + k ^ 2 * ‖a‖ ^ 2
  -- step 1: energy of `y`
  have hEy : ∀ x ∈ Icc 0 L, ‖y' x‖ ^ 2 + k ^ 2 * ‖y x‖ ^ 2 ≤ E0 * Real.exp (M * x) := by
    intro x hx
    have hy'' : ∀ x, HasDerivAt y' (-((k : ℂ) ^ 2) * y x - Q x * y x) x := fun x =>
      (hy' x).congr_deriv (by ring)
    have := energy_le_gronwall (hasDerivAt_energy hy hy'') (δ := E0) (K := M) (ε := 0)
      (by rw [h0, h1]) (fun x hx => ?_) hx
    · rwa [gronwallBound_ε0] at this
    · have hQx := hQ x (Ico_subset_Icc_self hx)
      have i1 : -inner ℝ (y' x) (Q x * y x) ≤ ‖y' x‖ * (M * ‖y x‖) := by
        rw [← inner_neg_right]
        refine (real_inner_le_norm _ _).trans ?_
        rw [norm_neg, norm_mul]
        gcongr
      have i3 : 2 * k * ‖y x‖ * ‖y' x‖ ≤ ‖y' x‖ ^ 2 + k ^ 2 * ‖y x‖ ^ 2 := by
        nlinarith [sq_nonneg (‖y' x‖ - k * ‖y x‖)]
      have i4 : 0 ≤ M * ‖y x‖ * ‖y' x‖ := by positivity
      nlinarith
  have hy2 : ∀ x ∈ Icc 0 L, ‖y x‖ ^ 2 ≤ E0 * Real.exp (M * L) / k ^ 2 := by
    intro x hx
    rw [le_div_iff₀ (by positivity)]
    have h1 := hEy x hx
    have h2 : Real.exp (M * x) ≤ Real.exp (M * L) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.2 hM)
    have hE0 : 0 ≤ E0 := by positivity
    nlinarith [sq_nonneg ‖y' x‖, mul_le_mul_of_nonneg_left h2 hE0]
  -- step 2: energy of the deviation
  set c : ℝ → ℂ := fun x => a * Real.cos (k * x) + b * Real.sin (k * x) / k
  set c' : ℝ → ℂ := fun x => -(a * k * Real.sin (k * x)) + b * Real.cos (k * x)
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hcos : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (Real.cos (k * x) : ℂ))
      ((-(k * Real.sin (k * x)) : ℝ) : ℂ) x := fun x => by
    have := ((hasDerivAt_id x).const_mul k).cos.ofReal_comp
    simpa [mul_comm] using this
  have hsin : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (Real.sin (k * x) : ℂ))
      ((k * Real.cos (k * x) : ℝ) : ℂ) x := fun x => by
    have := ((hasDerivAt_id x).const_mul k).sin.ofReal_comp
    simpa [mul_comm] using this
  have hc : ∀ x, HasDerivAt c (c' x) x := fun x =>
    (((hcos x).const_mul a).add (((hsin x).const_mul b).div_const (k : ℂ))).congr_deriv (by
      simp only [c']; push_cast; field_simp)
  have hc' : ∀ x, HasDerivAt c' (-((k : ℂ) ^ 2) * c x) x := fun x =>
    ((((hsin x).const_mul (a * k)).neg).add ((hcos x).const_mul b)).congr_deriv (by
      simp only [c]; push_cast; field_simp; ring)
  set R : ℝ → ℂ := fun x => Q x * y x
  have hd : ∀ x, HasDerivAt (fun x => y x - c x) (y' x - c' x) x := fun x =>
    (hy x).sub (hc x)
  have hd' : ∀ x, HasDerivAt (fun x => y' x - c' x)
      (-((k : ℂ) ^ 2) * (y x - c x) - R x) x := fun x =>
    ((hy' x).sub (hc' x)).congr_deriv (by simp only [R]; ring)
  set ε := M ^ 2 * (E0 * Real.exp (M * L) / k ^ 2)
  have hε : 0 ≤ ε := by positivity
  have hG := energy_le_gronwall (hasDerivAt_energy hd hd') (δ := 0) (K := 1) (ε := ε)
    (by simp [h0, h1, c, c']) (fun x hx => ?_) hx
  · rw [gronwallBound_of_K_ne_0 one_ne_zero] at hG
    simp only [zero_mul, zero_add, div_one, one_mul] at hG
    refine hG.trans ?_
    have h1 : Real.exp x - 1 ≤ Real.exp L := by
      linarith [Real.exp_le_exp.mpr hx.2]
    calc ε * (Real.exp x - 1) ≤ ε * Real.exp L := mul_le_mul_of_nonneg_left h1 hε
      _ = _ := by
        simp only [ε]
        rw [show (M + 1) * L = M * L + L by ring, Real.exp_add]
        ring
  · have hQx := hQ x (Ico_subset_Icc_self hx)
    have hyx := hy2 x (Ico_subset_Icc_self hx)
    set u := ‖y' x - c' x‖
    have i1 : -inner ℝ (y' x - c' x) (R x) ≤ u * (M * ‖y x‖) := by
      rw [← inner_neg_right]
      refine (real_inner_le_norm _ _).trans ?_
      rw [norm_neg]
      simp only [R, norm_mul]
      gcongr
    have i2 : 2 * (u * (M * ‖y x‖)) ≤ u ^ 2 + M ^ 2 * ‖y x‖ ^ 2 := by
      nlinarith [sq_nonneg (u - M * ‖y x‖)]
    have i3 : M ^ 2 * ‖y x‖ ^ 2 ≤ ε := mul_le_mul_of_nonneg_left hyx (sq_nonneg M)
    have i4 : 0 ≤ k ^ 2 * ‖y x - c x‖ ^ 2 := by positivity
    nlinarith

end ODE
