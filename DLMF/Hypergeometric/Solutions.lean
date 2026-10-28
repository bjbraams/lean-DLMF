/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

public import DLMF.Hypergeometric.Continuation
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Local solutions and Wronskians (DLMF §15.10)

The ordinary solution and its ODE are already in `DiffEq`. The functions here
are local solutions, not globally continued functions. Swapping `a,b` supplies
the second solution at infinity. Wronskians plus the ODE give fundamental pairs
when the Wronskians are nonzero. The integral-parameter logarithmic pairs are
stated with explicit nonvanishing Wronskians, including empty finite sums.
The four zero/one connection formulas hold on the overlap of their series disks.
See `Kummer` for the other Kummer representations.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace DLMF.Hypergeometric

/-- `(1-x-m)_{m-j} = (-1)^{m-j} (x)_m / (x)_j` in multiplied-out form. -/
theorem poch_one_sub_sub_mul {x : ℂ} {m j : ℕ} (hj : j ≤ m) :
    poch x j * poch (1 - x - m) (m - j) = (-1 : ℂ) ^ (m - j) * poch x m := by
  have h := poch_reflect (x + j) (m - j)
  rw [show 1 - (x + j) - ((m - j : ℕ) : ℂ) = 1 - x - m by push_cast [hj]; ring] at h
  rw [h, show poch x m = poch x (j + (m - j)) by rw [Nat.add_sub_cancel' hj], poch_add]
  ring

/-- A principal power computed from any logarithm in the principal strip. -/
theorem cpow_eq_exp_of_exp_eq {x L : ℂ} (hx : exp L = x) (h1 : -Real.pi < L.im)
    (h2 : L.im ≤ Real.pi) (y : ℂ) : x ^ y = exp (L * y) := by
  have hx0 : x ≠ 0 := by rw [← hx]; exact exp_ne_zero L
  rw [cpow_def_of_ne_zero hx0, ← hx, log_exp h1 h2]

/-- The Gauss differential operator, without division at its singular points. -/
@[dlmf 15.10.E1]
def gaussOperator (a b c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * (1 - z) * iteratedDeriv 2 f z + (c - (a + b + 1) * z) * deriv f z - a * b * f z

/-- Wronskian of two scalar functions, with the order used in DLMF. -/
def solutionWronskian (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z * deriv g z - deriv f z * g z

/-- The second solution at zero. The first is Mathlib's `ordinaryHypergeometric`. -/
@[dlmf 15.10.E2]
def zeroSecond (a b c z : ℂ) : ℂ := z ^ (1 - c) * ₂F₁ (a - c + 1) (b - c + 1) (2 - c) z

@[dlmf 15.10.E4]
def oneFirst (a b c z : ℂ) : ℂ := ₂F₁ a b (a + b - c + 1) (1 - z)

@[dlmf 15.10.E4]
def oneSecond (a b c z : ℂ) : ℂ :=
  (1 - z) ^ (c - a - b) * ₂F₁ (c - a) (c - b) (c - a - b + 1) (1 - z)

/-- Interchanging `a,b` gives the second solution at infinity. -/
@[dlmf 15.10.E6]
def infinityFirst (a b c z : ℂ) : ℂ := z ^ (-a) * ₂F₁ a (a - c + 1) (a - b + 1) (1 / z)

/-- Second derivative of `w ↦ w^s G(w)` for `G` analytic near a point of the slit plane. -/
theorem iteratedDeriv_two_cpow_mul {G : ℂ → ℂ} {s z : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hzU : z ∈ U) (hG : AnalyticOnNhd ℂ G U) (hUs : U ⊆ slitPlane) :
    deriv (fun w => w ^ s * G w) z = s * z ^ (s - 1) * G z + z ^ s * deriv G z ∧
    iteratedDeriv 2 (fun w => w ^ s * G w) z =
      s * (s - 1) * z ^ (s - 2) * G z + 2 * s * z ^ (s - 1) * deriv G z +
        z ^ s * iteratedDeriv 2 G z := by
  have hd : ∀ w ∈ U, HasDerivAt (fun w => w ^ s * G w)
      (s * w ^ (s - 1) * G w + w ^ s * deriv G w) w := by
    intro w hw
    have h1 := (hasDerivAt_id' w).cpow_const (c := s) (hUs hw)
    have h2 := (hG w hw).differentiableAt.hasDerivAt
    convert h1.mul h2 using 1
    ring
  refine ⟨(hd z hzU).deriv, ?_⟩
  have hev : deriv (fun w => w ^ s * G w) =ᶠ[𝓝 z]
      fun w => s * w ^ (s - 1) * G w + w ^ s * deriv G w :=
    Filter.eventually_of_mem (hU.mem_nhds hzU) fun w hw => (hd w hw).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq, iteratedDeriv_succ, iteratedDeriv_one]
  have hz0 := hUs hzU
  have hG1 := (hG z hzU).differentiableAt.hasDerivAt
  have hG2 := (hG z hzU).deriv.differentiableAt.hasDerivAt
  have hp1 := (hasDerivAt_id' z).cpow_const (c := s - 1) hz0
  have hp0 := (hasDerivAt_id' z).cpow_const (c := s) hz0
  have := ((hp1.const_mul s).mul hG1).add (hp0.mul hG2)
  refine this.deriv.trans ?_
  rw [show s - 1 - 1 = s - 2 by ring]
  ring

@[dlmf 15.10.E2]
theorem zero_second_ode
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, 2 - c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane) :
    gaussOperator a b c (zeroSecond a b c) z = 0 := by
  set G : ℂ → ℂ := ₂F₁ (a - c + 1) (b - c + 1) (2 - c)
  have hU : IsOpen (Metric.ball (0 : ℂ) 1 ∩ slitPlane) := Metric.isOpen_ball.inter isOpen_slitPlane
  have hzU : z ∈ Metric.ball (0 : ℂ) 1 ∩ slitPlane := ⟨by simpa using hz, hs⟩
  have hG : AnalyticOnNhd ℂ G (Metric.ball (0 : ℂ) 1 ∩ slitPlane) := fun w hw =>
    (hasFPowerSeriesOnBall_ordinaryHypergeometric _ _ _).analyticAt_of_mem
      (mem_eball_one_of_norm_lt_one (by simpa using hw.1))
  obtain ⟨h1, h2⟩ := iteratedDeriv_two_cpow_mul (s := 1 - c) hU hzU hG Set.inter_subset_right
  have hz0 : z ≠ 0 := slitPlane_ne_zero hs
  have hz1 : z ≠ 1 := by rintro rfl; simp at hz
  have hode := ordinaryHypergeometric_ode (a := a - c + 1) (b := b - c + 1) hc hz hz0 hz1
  have he : zeroSecond a b c = fun w => w ^ (1 - c) * G w := by funext w; rfl
  have e1 : z ^ (1 - c - 1) = z ^ (1 - c) / z := by rw [cpow_sub _ _ hz0, cpow_one]
  have e2 : z ^ (1 - c - 2) = z ^ (1 - c) / z ^ 2 := by
    rw [cpow_sub _ _ hz0, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]
  rw [gaussOperator, he, h1, h2, e1, e2]
  set P := z ^ (1 - c)
  field_simp
  linear_combination (z * P) * hode

/-- The Gauss operator annihilates `₂F₁` on the whole unit disk, including the origin; the
coefficient recurrence also gives the equation at the regular point zero. -/
theorem gaussOperator_ordinaryHypergeometric {a b c w : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hw : ‖w‖ < 1) : gaussOperator a b c (₂F₁ a b c) w = 0 := by
  have h := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).ode_of_recurrence
    (A := 1) (B := a + b + 1) (C := a * b) (D := c) (fun n => ?_)
    (mem_eball_one_of_norm_lt_one hw)
  · simpa [gaussOperator, iteratedDeriv_succ, iteratedDeriv_zero] using h
  · rw [gaussHGCoeff_recurrence hc]
    ring

@[dlmf 15.10.E4]
theorem one_first_ode {a b c z : ℂ} (hc : ∀ k : ℕ, a + b - c + 1 ≠ -(k : ℂ)) (hz : ‖1 - z‖ < 1) :
    gaussOperator a b c (oneFirst a b c) z = 0 := by
  have he : oneFirst a b c = (fun w => ₂F₁ a b (a + b - c + 1) (1 - w)) := by
    funext w
    rw [oneFirst]
  have hd : deriv (oneFirst a b c) z = -deriv (₂F₁ a b (a + b - c + 1)) (1 - z) := by
    have h := congrFun (iteratedDeriv_comp_const_sub (n := 1)
      (f := (₂F₁ a b (a + b - c + 1) : ℂ → ℂ)) (s := 1)) z
    rw [he]
    simpa [iteratedDeriv_one] using h
  have hdd : iteratedDeriv 2 (oneFirst a b c) z =
      iteratedDeriv 2 (₂F₁ a b (a + b - c + 1)) (1 - z) := by
    have h := congrFun (iteratedDeriv_comp_const_sub (n := 2)
      (f := (₂F₁ a b (a + b - c + 1) : ℂ → ℂ)) (s := 1)) z
    rw [he]
    simpa using h
  have h := gaussOperator_ordinaryHypergeometric (a := a) (b := b) hc hz
  rw [gaussOperator, hd, hdd, oneFirst]
  unfold gaussOperator at h
  linear_combination h

/-- The Gauss operator under the reflection `z ↦ 1 - z`. -/
theorem gaussOperator_comp_one_sub (a b c : ℂ) (g : ℂ → ℂ) (z : ℂ) :
    gaussOperator a b c (fun w => g (1 - w)) z = gaussOperator a b (a + b - c + 1) g (1 - z) := by
  have hd : deriv (fun w => g (1 - w)) z = -deriv g (1 - z) := by
    simpa [iteratedDeriv_one] using
      congrFun (iteratedDeriv_comp_const_sub (n := 1) (f := g) (s := 1)) z
  have hdd : iteratedDeriv 2 (fun w => g (1 - w)) z = iteratedDeriv 2 g (1 - z) := by
    simpa using congrFun (iteratedDeriv_comp_const_sub (n := 2) (f := g) (s := 1)) z
  rw [gaussOperator, gaussOperator, hd, hdd]
  ring

@[dlmf 15.10.E4]
theorem one_second_ode
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, c - a - b + 1 ≠ -(k : ℂ))
    (hz : ‖1 - z‖ < 1)
    (hs : 1 - z ∈ slitPlane) :
    gaussOperator a b c (oneSecond a b c) z = 0 := by
  have he : oneSecond a b c = fun w => zeroSecond a b (a + b - c + 1) (1 - w) := by
    funext w
    rw [oneSecond, zeroSecond, ordinaryHypergeometric_symm]
    congr 1 <;> ring_nf
  rw [he, gaussOperator_comp_one_sub]
  exact zero_second_ode (by simpa [show (2 : ℂ) - (a + b - c + 1) = c - a - b + 1 by ring]
    using hc) hz hs

/-- Derivatives of `w ↦ w^s H(1/w)`. -/
theorem iteratedDeriv_two_cpow_mul_recip {H : ℂ → ℂ} {s z : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hzU : z ∈ U) (hH : ∀ w ∈ U, AnalyticAt ℂ H w⁻¹) (hUs : U ⊆ slitPlane) :
    deriv (fun w => w ^ s * H w⁻¹) z =
      s * z ^ (s - 1) * H z⁻¹ - z ^ s * deriv H z⁻¹ / z ^ 2 ∧
    iteratedDeriv 2 (fun w => w ^ s * H w⁻¹) z =
      s * (s - 1) * z ^ (s - 1 - 1) * H z⁻¹ - s * z ^ (s - 1) * deriv H z⁻¹ / z ^ 2
        - (s * z ^ (s - 1) * deriv H z⁻¹ / z ^ 2
          - z ^ s * (2 * deriv H z⁻¹ / z ^ 3 + iteratedDeriv 2 H z⁻¹ / z ^ 4)) := by
  have hne : ∀ w ∈ U, w ≠ 0 := fun w hw => slitPlane_ne_zero (hUs hw)
  have hinv : ∀ w ∈ U, HasDerivAt (fun y : ℂ => y⁻¹) (-(w ^ 2)⁻¹) w := fun w hw =>
    hasDerivAt_inv (hne w hw)
  have hd : ∀ w ∈ U, HasDerivAt (fun w => w ^ s * H w⁻¹)
      (s * w ^ (s - 1) * H w⁻¹ - w ^ s * deriv H w⁻¹ / w ^ 2) w := by
    intro w hw
    have h1 := (hasDerivAt_id' w).cpow_const (c := s) (hUs hw)
    have h2 := (hH w hw).differentiableAt.hasDerivAt.comp w (hinv w hw)
    convert h1.mul h2 using 1
    · rfl
    · simp only [Function.comp_apply]
      field_simp [hne w hw]
      ring
  refine ⟨(hd z hzU).deriv, ?_⟩
  have hev : deriv (fun w => w ^ s * H w⁻¹) =ᶠ[𝓝 z]
      fun w => s * w ^ (s - 1) * H w⁻¹ - w ^ s * deriv H w⁻¹ / w ^ 2 :=
    Filter.eventually_of_mem (hU.mem_nhds hzU) fun w hw => (hd w hw).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq, iteratedDeriv_succ, iteratedDeriv_one]
  have hz0 := hUs hzU
  have hz0' := hne z hzU
  have hH1 := (hH z hzU).differentiableAt.hasDerivAt.comp z (hinv z hzU)
  have hH2 := (hH z hzU).deriv.differentiableAt.hasDerivAt.comp z (hinv z hzU)
  have hp1 := (hasDerivAt_id' z).cpow_const (c := s - 1) hz0
  have hp0 := (hasDerivAt_id' z).cpow_const (c := s) hz0
  have hq := (hasDerivAt_id' z).pow 2
  have := ((hp1.const_mul s).mul hH1).sub ((hp0.mul hH2).div hq (pow_ne_zero 2 hz0'))
  refine this.deriv.trans ?_
  simp only [Function.comp_apply, Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat,
    show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  field_simp
  ring

@[dlmf 15.10.E6]
theorem infinity_first_ode
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (hz : 1 < ‖z‖)
    (hs : z ∈ slitPlane) :
    gaussOperator a b c (infinityFirst a b c) z = 0 := by
  set H : ℂ → ℂ := ₂F₁ a (a - c + 1) (a - b + 1)
  set U : Set ℂ := {w | 1 < ‖w‖} ∩ slitPlane
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_norm).inter isOpen_slitPlane
  have hzU : z ∈ U := ⟨hz, hs⟩
  have hinvlt : ∀ w : ℂ, 1 < ‖w‖ → ‖w⁻¹‖ < 1 := fun w hw => by
    rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hw
  have hH : ∀ w ∈ U, AnalyticAt ℂ H w⁻¹ := fun w hw =>
    (hasFPowerSeriesOnBall_ordinaryHypergeometric _ _ _).analyticAt_of_mem
      (mem_eball_one_of_norm_lt_one (hinvlt w hw.1))
  obtain ⟨h1, h2⟩ := iteratedDeriv_two_cpow_mul_recip (s := -a) hU hzU hH Set.inter_subset_right
  have hz0 : z ≠ 0 := slitPlane_ne_zero hs
  have hu := hinvlt z hz
  have hu0 : z⁻¹ ≠ 0 := inv_ne_zero hz0
  have hu1 : z⁻¹ ≠ 1 := by intro h; rw [h, norm_one] at hu; exact lt_irrefl _ hu
  have hode := ordinaryHypergeometric_ode (a := a) (b := a - c + 1) hc hu hu0 hu1
  have he : infinityFirst a b c = fun w => w ^ (-a) * H w⁻¹ := by
    funext w; rw [infinityFirst, one_div]
  have e1 : z ^ (-a - 1) = z ^ (-a) / z := by rw [cpow_sub _ _ hz0, cpow_one]
  have e2 : z ^ (-a - 1 - 1) = z ^ (-a) / z ^ 2 := by
    rw [sub_sub, cpow_sub _ _ hz0, show (1 + 1 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]
  rw [gaussOperator, he, h1, h2, e1, e2]
  beta_reduce
  set P := z ^ (-a)
  set u := z⁻¹ with hu_def
  have hz' : z = u⁻¹ := (inv_inv z).symm
  rw [hz']
  field_simp
  linear_combination (-(P * u)) * hode

@[dlmf 15.10.E3]
theorem zero_wronskian
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hd : ∀ k : ℕ, 2 - c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane) :
    solutionWronskian (₂F₁ a b c) (zeroSecond a b c) z = (1 - c) * z ^ (-c) * (1 - z) ^ (c - a - b - 1) := by
  set F : ℂ → ℂ := ₂F₁ a b c with hF
  set G : ℂ → ℂ := ₂F₁ (a - c + 1) (b - c + 1) (2 - c) with hG
  set k := a + b + 1 - c with hk
  set B : ℂ → ℂ := fun w => (1 - c) * F w * G w + w * (F w * deriv G w - deriv F w * G w) with hB
  have hFa : ∀ w : ℂ, ‖w‖ < 1 → AnalyticAt ℂ F w := fun w hw =>
    (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).analyticAt_of_mem
      (mem_eball_one_of_norm_lt_one hw)
  have hGa : ∀ w : ℂ, ‖w‖ < 1 → AnalyticAt ℂ G w := fun w hw =>
    (hasFPowerSeriesOnBall_ordinaryHypergeometric _ _ _).analyticAt_of_mem
      (mem_eball_one_of_norm_lt_one hw)
  have hBd : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt B ((1 - c) * (deriv F w * G w + F w * deriv G w) +
      (F w * deriv G w - deriv F w * G w) +
      w * (F w * iteratedDeriv 2 G w - iteratedDeriv 2 F w * G w)) w := by
    intro w hw
    have hF1 := (hFa w hw).differentiableAt.hasDerivAt
    have hG1 := (hGa w hw).differentiableAt.hasDerivAt
    have hF2 := (hFa w hw).deriv.differentiableAt.hasDerivAt
    have hG2 := (hGa w hw).deriv.differentiableAt.hasDerivAt
    have h := ((hF1.const_mul (1 - c)).mul hG1).add ((hasDerivAt_id w).mul
      ((hF1.mul hG2).sub (hF2.mul hG1)))
    refine h.congr_deriv ?_
    simp only [id, iteratedDeriv_succ, iteratedDeriv_zero, Pi.mul_apply, Pi.sub_apply]
    ring
  have hrel : ∀ w : ℂ, ‖w‖ < 1 → (1 - w) * ((1 - c) * (deriv F w * G w + F w * deriv G w) +
      (F w * deriv G w - deriv F w * G w) +
      w * (F w * iteratedDeriv 2 G w - iteratedDeriv 2 F w * G w)) = k * B w := by
    intro w hw
    have hoF := gaussOperator_ordinaryHypergeometric (a := a) (b := b) hc hw
    have hoG := gaussOperator_ordinaryHypergeometric (a := a - c + 1) (b := b - c + 1) hd hw
    simp only [gaussOperator] at hoF hoG
    simp only [hB, hk]
    linear_combination F w * hoG - G w * hoF
  set H : ℂ → ℂ := fun w => B w * (1 - w) ^ k with hH
  have hball : ∀ w ∈ Metric.ball (0 : ℂ) 1, ‖w‖ < 1 := fun w hw => by simpa using hw
  have hHd : ∀ w ∈ Metric.ball (0 : ℂ) 1, HasDerivAt H 0 w := by
    intro w hw
    have hw1 := hball w hw
    have h1w : 1 - w ≠ 0 := by
      intro h
      have : w = 1 := by linear_combination -h
      rw [this] at hw1
      simp at hw1
    have hslit : 1 - w ∈ slitPlane := by
      refine mem_slitPlane_iff.mpr (Or.inl ?_)
      have := (re_le_norm w).trans_lt hw1
      simp only [sub_re, one_re]; linarith
    have hp := ((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w)).cpow_const (c := k) hslit
    refine ((hBd w hw1).mul hp).congr_deriv ?_
    simp only [Pi.sub_apply, id]
    rw [show (1 - w) ^ (k - 1) = (1 - w) ^ k / (1 - w) by rw [cpow_sub _ _ h1w, cpow_one]]
    have := hrel w hw1
    field_simp
    linear_combination (1 - w) ^ k * this
  have hHc := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
    (fun w hw => (hHd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hHd w hw).deriv) (x := z) (y := 0) (by simpa using hz) (by simp)
  have hH0 : H 0 = 1 - c := by
    simp [hH, hB, hF, hG, ordinaryHypergeometric_zero]
  rw [hH0] at hHc
  -- The Wronskian in terms of `B`.
  have hz0 : z ≠ 0 := slitPlane_ne_zero hs
  have h1z : 1 - z ≠ 0 := by
    intro h; have : z = 1 := by linear_combination -h
    rw [this] at hz; simp at hz
  have hS : HasDerivAt (zeroSecond a b c)
      ((1 - c) * z ^ (1 - c - 1) * 1 * G z + z ^ (1 - c) * deriv G z) z :=
    ((hasDerivAt_id z).cpow_const (c := 1 - c) hs).mul (hGa z hz).differentiableAt.hasDerivAt
  have hzc : z ^ (1 - c) = z * z ^ (-c) := by
    rw [show 1 - c = 1 + -c by ring, cpow_add _ _ hz0, cpow_one]
  have hzc' : z ^ (1 - c - 1) = z ^ (-c) := by congr 1; ring
  have hkne : (1 - z) ^ k ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl h1z)
  have hk' : (1 - z) ^ (c - a - b - 1) = ((1 - z) ^ k)⁻¹ := by
    rw [show c - a - b - 1 = -k by rw [hk]; ring, cpow_neg]
  have hBz : B z = (1 - c) * ((1 - z) ^ k)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hkne]; exact hHc
  unfold solutionWronskian
  rw [hS.deriv]
  calc F z * ((1 - c) * z ^ (1 - c - 1) * 1 * G z + z ^ (1 - c) * deriv G z) -
        deriv F z * zeroSecond a b c z = z ^ (-c) * B z := by
        rw [show zeroSecond a b c z = z ^ (1 - c) * G z from rfl, hzc, hzc']
        simp only [hB]
        ring
    _ = (1 - c) * z ^ (-c) * (1 - z) ^ (c - a - b - 1) := by
        rw [hBz, hk']
        ring

@[dlmf 15.10.E5]
theorem one_wronskian
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, a + b - c + 1 ≠ -(k : ℂ))
    (hd : ∀ k : ℕ, c - a - b + 1 ≠ -(k : ℂ))
    (hz : ‖1 - z‖ < 1)
    (hs : 1 - z ∈ slitPlane) :
    solutionWronskian (oneFirst a b c) (oneSecond a b c) z = (a + b - c) * z ^ (-c) * (1 - z) ^ (c - a - b -
      1) := by
  set C := a + b - c + 1 with hCdef
  have hd' : ∀ k : ℕ, 2 - C ≠ -(k : ℂ) := by
    rw [show 2 - C = c - a - b + 1 by rw [hCdef]; ring]; exact hd
  have h0 := zero_wronskian (a := a) (b := b) (c := C) (z := 1 - z) hc hd' hz hs
  have hF : DifferentiableAt ℂ (₂F₁ a b C) (1 - z) :=
    ((hasFPowerSeriesOnBall_ordinaryHypergeometric a b C).analyticAt_of_mem
      (mem_eball_one_of_norm_lt_one hz)).differentiableAt
  have hS : DifferentiableAt ℂ (zeroSecond a b C) (1 - z) :=
    ((hasDerivAt_id (1 - z)).cpow_const (c := 1 - C) hs).differentiableAt.mul
      ((hasFPowerSeriesOnBall_ordinaryHypergeometric _ _ _).analyticAt_of_mem
        (mem_eball_one_of_norm_lt_one hz)).differentiableAt
  have hr : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub 1
  have he1 : oneFirst a b c = fun w => ₂F₁ a b C (1 - w) := rfl
  have he2 : oneSecond a b c = fun w => zeroSecond a b C (1 - w) := by
    funext w
    rw [oneSecond, zeroSecond, ordinaryHypergeometric_symm]
    simp only [hCdef]
    congr 1 <;> ring_nf
  have hd1 : deriv (oneFirst a b c) z = -deriv (₂F₁ a b C) (1 - z) := by
    have h' : HasDerivAt (fun w => ₂F₁ a b C (1 - w)) _ z := hF.hasDerivAt.comp z hr
    rw [he1, h'.deriv]; ring
  have hd2 : deriv (oneSecond a b c) z = -deriv (zeroSecond a b C) (1 - z) := by
    have h' : HasDerivAt (fun w => zeroSecond a b C (1 - w)) _ z := hS.hasDerivAt.comp z hr
    rw [he2, h'.deriv]; ring
  unfold solutionWronskian at h0 ⊢
  rw [hd1, hd2, he1, he2]
  simp only
  rw [sub_sub_cancel, show 1 - C = c - a - b by rw [hCdef]; ring,
    show C - a - b - 1 = -c by rw [hCdef]; ring, show -C = c - a - b - 1 by rw [hCdef]; ring]
    at h0
  linear_combination -h0

/-- Wronskian of a common factor times two functions. -/
theorem solutionWronskian_mul_left {p f g : ℂ → ℂ} {z : ℂ} (hp : DifferentiableAt ℂ p z)
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) :
    solutionWronskian (fun w => p w * f w) (fun w => p w * g w) z =
      p z ^ 2 * solutionWronskian f g z := by
  unfold solutionWronskian
  have h1 : HasDerivAt (fun w => p w * f w) _ z := hp.hasDerivAt.mul hf.hasDerivAt
  have h2 : HasDerivAt (fun w => p w * g w) _ z := hp.hasDerivAt.mul hg.hasDerivAt
  rw [h1.deriv, h2.deriv]
  ring

/-- Wronskian after the inversion `w ↦ w⁻¹`. -/
theorem solutionWronskian_comp_recip {f g : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hf : DifferentiableAt ℂ f z⁻¹) (hg : DifferentiableAt ℂ g z⁻¹) :
    solutionWronskian (fun w => f w⁻¹) (fun w => g w⁻¹) z =
      -(z ^ 2)⁻¹ * solutionWronskian f g z⁻¹ := by
  unfold solutionWronskian
  have hi := hasDerivAt_inv hz
  have h1 : HasDerivAt (fun w => f w⁻¹) _ z := hf.hasDerivAt.comp z hi
  have h2 : HasDerivAt (fun w => g w⁻¹) _ z := hg.hasDerivAt.comp z hi
  rw [h1.deriv, h2.deriv]
  ring

@[dlmf 15.10.E7]
theorem infinity_wronskian
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (hd : ∀ k : ℕ, b - a + 1 ≠ -(k : ℂ))
    (hz : 1 < z.re) :
    solutionWronskian (infinityFirst a b c) (infinityFirst b a c) z = (a - b) * z ^ (-c) * (z - 1) ^ (c - a
      - b - 1) := by
  set B := a - c + 1
  set C := a - b + 1 with hCdef
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz; linarith
  have hre : ∀ w : ℂ, 0 < w.re → w⁻¹ ∈ slitPlane ∧ ‖w⁻¹‖ ≤ 1 / w.re := by
    intro w hw
    have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
    refine ⟨mem_slitPlane_iff.mpr (Or.inl ?_), ?_⟩
    · rw [inv_re]; exact div_pos hw (normSq_pos.mpr hw0)
    · rw [norm_inv]
      exact inv_anti₀ hw (re_le_norm w) |>.trans_eq (one_div _).symm
  have hu := hre z (by linarith)
  have hun : ‖z⁻¹‖ < 1 := hu.2.trans_lt (by rw [div_lt_one (by linarith)]; exact hz)
  have hd' : ∀ k : ℕ, 2 - C ≠ -(k : ℂ) := by
    rw [show 2 - C = b - a + 1 by rw [hCdef]; ring]; exact hd
  have h0 := zero_wronskian (a := a) (b := B) (c := C) hc hd' hun hu.1
  -- local rewriting of the two solutions
  have hU : ∀ᶠ w in 𝓝 z, 0 < w.re := (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
    (show z ∈ re ⁻¹' Set.Ioi 0 by simp only [Set.mem_preimage, Set.mem_Ioi]; linarith)
  have e1 : infinityFirst a b c = fun w => w ^ (-a) * ₂F₁ a B C w⁻¹ := by
    funext w; rw [infinityFirst, one_div]
  have e2 : infinityFirst b a c =ᶠ[𝓝 z] fun w => w ^ (-a) * zeroSecond a B C w⁻¹ := by
    filter_upwards [hU] with w hw
    have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
    have harg : w.arg ≠ π := (mem_slitPlane_iff_arg.mp (mem_slitPlane_iff.mpr (Or.inl hw))).1
    simp only [infinityFirst, zeroSecond, one_div]
    rw [inv_cpow _ _ harg, ← cpow_neg, ← mul_assoc, ← cpow_add _ _ hw0]
    congr 2 <;> simp only [B, C] <;> ring
  have hW : solutionWronskian (infinityFirst a b c) (infinityFirst b a c) z =
      solutionWronskian (fun w => w ^ (-a) * ₂F₁ a B C w⁻¹)
        (fun w => w ^ (-a) * zeroSecond a B C w⁻¹) z := by
    unfold solutionWronskian
    rw [e1, e2.deriv_eq, e2.eq_of_nhds]
  have hzs : z ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by linarith))
  have hFa : DifferentiableAt ℂ (₂F₁ a B C) z⁻¹ :=
    ((hasFPowerSeriesOnBall_ordinaryHypergeometric a B C).analyticAt_of_mem
      (mem_eball_one_of_norm_lt_one hun)).differentiableAt
  have hSa : DifferentiableAt ℂ (zeroSecond a B C) z⁻¹ :=
    ((hasDerivAt_id z⁻¹).cpow_const (c := 1 - C) hu.1).differentiableAt.mul
      ((hasFPowerSeriesOnBall_ordinaryHypergeometric _ _ _).analyticAt_of_mem
        (mem_eball_one_of_norm_lt_one hun)).differentiableAt
  have hp : DifferentiableAt ℂ (fun w : ℂ => w ^ (-a)) z :=
    ((hasDerivAt_id z).cpow_const (c := -a) hzs).differentiableAt
  have hFi : DifferentiableAt ℂ (fun w => ₂F₁ a B C w⁻¹) z := hFa.comp z (differentiableAt_inv hz0)
  have hSi : DifferentiableAt ℂ (fun w => zeroSecond a B C w⁻¹) z :=
    hSa.comp z (differentiableAt_inv hz0)
  rw [hW, solutionWronskian_mul_left hp hFi hSi, solutionWronskian_comp_recip hz0 hFa hSa, h0]
  -- power bookkeeping
  have hz1 : z - 1 ≠ 0 := by intro h; rw [sub_eq_zero] at h; rw [h] at hz; simp at hz
  have hargz : z.arg ≠ π := (mem_slitPlane_iff_arg.mp hzs).1
  have habs : ∀ w : ℂ, 0 < w.re → |w.arg| < π / 2 := fun w hw =>
    abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  have hzi : 0 < z⁻¹.re := by rw [inv_re]; exact div_pos (by linarith) (normSq_pos.mpr hz0)
  have hlog : log (1 - z⁻¹) = log (z - 1) + log z⁻¹ := by
    rw [show 1 - z⁻¹ = (z - 1) * z⁻¹ by field_simp]
    refine log_mul hz1 (inv_ne_zero hz0) ?_
    have h1 := habs (z - 1) (by simp; linarith)
    have h2 := habs z⁻¹ hzi
    rw [abs_lt] at h1 h2
    constructor <;> linarith [Real.pi_pos]
  set p := C - a - B - 1 with hpdef
  have hpow : (1 - z⁻¹) ^ p = (z - 1) ^ p * (z ^ p)⁻¹ := by
    have h1z : 1 - z⁻¹ ≠ 0 := by
      rw [show 1 - z⁻¹ = (z - 1) * z⁻¹ by field_simp]; exact mul_ne_zero hz1 (inv_ne_zero hz0)
    rw [cpow_def_of_ne_zero h1z, hlog, add_mul, exp_add, ← cpow_def_of_ne_zero hz1,
      ← cpow_def_of_ne_zero (inv_ne_zero hz0), inv_cpow _ _ hargz]
  have hC : z⁻¹ ^ (-C) = z ^ C := by rw [inv_cpow _ _ hargz, cpow_neg, inv_inv]
  have hp' : p = c - a - b - 1 := by rw [hpdef]; simp only [B, C]; ring
  have key : z ^ (-a) * z ^ (-a) * z ^ C = z ^ (-c) * z ^ p * z ^ (2 : ℂ) := by
    rw [← cpow_add _ _ hz0, ← cpow_add _ _ hz0, ← cpow_add _ _ hz0, ← cpow_add _ _ hz0]
    congr 1; rw [hp']; simp only [C]; ring
  have hz2 : z ^ (2 : ℂ) = z ^ 2 := by exact_mod_cast cpow_natCast z 2
  rw [hz2] at key
  rw [hpow, hC, ← hp']
  have hzp : z ^ p ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  have h1C : 1 - C = -(a - b) := by simp only [C]; ring
  rw [h1C]
  field_simp
  linear_combination (a - b) * (z - 1) ^ p * key

/-- The logarithmic second solution for a positive integral denominator (generic numerators). -/
@[dlmf 15.10.E8]
def logarithmicSecond (a b : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ₂F₁ a b (n : ℂ) z * log z -
    (∑ j ∈ Finset.range (n - 1),
      ((n - 1).factorial : ℂ) * (j.factorial : ℂ) /
        (((n - j - 2).factorial : ℂ) * poch (1 - a) (j + 1) * poch (1 - b) (j + 1)) * ((-z)⁻¹) ^ (j + 1)) +
    ∑' k : ℕ, gaussHGCoeff a b n k * z ^ k *
      (digamma (a + k) + digamma (b + k) - digamma (1 + k) - digamma (n + k))

/-- The logarithmic second solution with one terminating numerator. -/
@[dlmf 15.10.E9]
def logarithmicSecondTerminating (b : ℂ) (m n : ℕ) (z : ℂ) : ℂ :=
  ₂F₁ (-m : ℂ) b (n : ℂ) z * log z -
    (∑ j ∈ Finset.range (n - 1),
      ((n - 1).factorial : ℂ) * (j.factorial : ℂ) /
        (((n - j - 2).factorial : ℂ) * poch (m + 1) (j + 1) * poch (1 - b) (j + 1)) * ((-z)⁻¹) ^ (j + 1)) +
    (∑ k ∈ Finset.range (m + 1), gaussHGCoeff (-m) b n k * z ^ k *
      (digamma (1 + m - k) + digamma (b + k) - digamma (1 + k) - digamma (n + k))) +
    (-1 : ℂ) ^ m * (m.factorial : ℂ) * ∑' j : ℕ,
      (j.factorial : ℂ) * poch b (m + 1 + j) /
        (poch n (m + 1 + j) * ((m + 1 + j).factorial : ℂ)) * z ^ (m + 1 + j)

/-- The logarithmic second solution with two terminating numerators. -/
@[dlmf 15.10.E10]
def logarithmicSecondBothTerminating (m l n : ℕ) (z : ℂ) : ℂ :=
  ₂F₁ (-m : ℂ) (-l) (n : ℂ) z * log z -
    (∑ j ∈ Finset.range (n - 1),
      ((n - 1).factorial : ℂ) * (j.factorial : ℂ) /
        (((n - j - 2).factorial : ℂ) * poch (m + 1) (j + 1) * poch (l + 1) (j + 1)) * ((-z)⁻¹) ^ (j + 1)) +
    (∑ k ∈ Finset.range (l + 1), gaussHGCoeff (-m) (-l) n k * z ^ k *
      (digamma (1 + m - k) + digamma (1 + l - k) - digamma (1 + k) - digamma (n + k))) +
    (-1 : ℂ) ^ l * (l.factorial : ℂ) * ∑ j ∈ Finset.range (m - l),
      (j.factorial : ℂ) * poch (-m) (l + 1 + j) /
        (poch n (l + 1 + j) * ((l + 1 + j).factorial : ℂ)) * z ^ (l + 1 + j)

/-! ### Uniqueness for the Gauss equation on an open set -/

/-- Differentiating the Gauss equation `n` times on an open set. -/
theorem gaussOperator_iteratedDeriv {a b c : ℂ} {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (hode : ∀ w ∈ U, gaussOperator a b c f w = 0) (n : ℕ) :
    ∀ w ∈ U, w * (1 - w) * iteratedDeriv (n + 2) f w +
      ((n : ℂ) * (1 - 2 * w) + (c - (a + b + 1) * w)) * iteratedDeriv (n + 1) f w +
      (-((n : ℂ) * (n - 1)) - n * (a + b + 1) - a * b) * iteratedDeriv n f w = 0 := by
  have ha (k : ℕ) : AnalyticOnNhd ℂ (iteratedDeriv k f) U := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hf
    | succ k ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hd (k : ℕ) (w : ℂ) (hw : w ∈ U) :
      HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f w) w := by
    simpa only [iteratedDeriv_succ] using (ha k w hw).differentiableAt.hasDerivAt
  induction n with
  | zero =>
    intro w hw
    have h := hode w hw
    simp only [gaussOperator] at h
    simp only [Nat.cast_zero, zero_mul, zero_add, zero_sub, neg_zero, iteratedDeriv_one,
      iteratedDeriv_zero]
    linear_combination h
  | succ n ih =>
    intro w hw
    set E : ℂ → ℂ := fun w' => w' * (1 - w') * iteratedDeriv (n + 2) f w' +
      ((n : ℂ) * (1 - 2 * w') + (c - (a + b + 1) * w')) * iteratedDeriv (n + 1) f w' +
      (-((n : ℂ) * (n - 1)) - n * (a + b + 1) - a * b) * iteratedDeriv n f w' with hE
    have h1 := ((hasDerivAt_id w).mul ((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w))).mul
      (hd (n + 2) w hw)
    have h2 := (((hasDerivAt_const w (n : ℂ)).mul ((hasDerivAt_const w (1 : ℂ)).sub
      ((hasDerivAt_id w).const_mul 2))).add ((hasDerivAt_const w c).sub
      ((hasDerivAt_id w).const_mul (a + b + 1)))).mul (hd (n + 1) w hw)
    have h3 := (hd n w hw).const_mul (-((n : ℂ) * (n - 1)) - n * (a + b + 1) - a * b)
    have ht : HasDerivAt E _ w := (h1.add h2).add h3
    have he : E =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [hU.mem_nhds hw] with w' hw'
      exact ih w' hw'
    have hD := ht.deriv
    rw [he.deriv_eq, deriv_const] at hD
    simp only [id, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, mul_one, zero_sub, zero_add,
      one_mul, zero_mul] at hD
    simp only [show n + 2 + 1 = n + 3 by ring, show n + 1 + 1 = n + 2 by ring] at hD ⊢
    push_cast
    linear_combination -hD

/-- A solution of the Gauss equation on a connected open set vanishing to second order at a
regular point vanishes identically. -/
theorem gaussOperator_eq_zero_of_deriv_eq_zero {a b c : ℂ} {g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hg : AnalyticOnNhd ℂ g U)
    (hode : ∀ w ∈ U, gaussOperator a b c g w = 0) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (h0 : z₀ ≠ 0)
    (h1 : z₀ ≠ 1) (hv : g z₀ = 0) (hdv : deriv g z₀ = 0) : ∀ w ∈ U, g w = 0 := by
  have hP : z₀ * (1 - z₀) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.mpr (Ne.symm h1))
  have hall (n : ℕ) : iteratedDeriv n g z₀ = 0 ∧ iteratedDeriv (n + 1) g z₀ = 0 := by
    induction n with
    | zero => exact ⟨by simpa using hv, by simpa using hdv⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h := gaussOperator_iteratedDeriv hU hg hode n z₀ hz₀
      rw [ih.1, ih.2] at h
      have h' : z₀ * (1 - z₀) * iteratedDeriv (n + 2) g z₀ = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_left hP
  have hp := (hg z₀ hz₀).hasFPowerSeriesAt
  simp_rw [fun n => (hall n).1, zero_div] at hp
  have hev : g =ᶠ[𝓝 z₀] fun _ => (0 : ℂ) := by
    filter_upwards [hp.eventually_hasSum_sub] with w hw
    have h0' : HasSum (fun n => FormalMultilinearSeries.ofScalars ℂ (fun _ : ℕ => (0 : ℂ)) n
        (fun _ => w - z₀)) 0 := by
      simp
    exact hw.unique h0'
  intro w hw
  exact hg.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hUc hz₀ hev hw

/-- The Gauss operator is linear on functions analytic near the point. -/
theorem gaussOperator_sub_smul {a b c : ℂ} {f₁ f₂ f₃ : ℂ → ℂ} {α β z : ℂ}
    (h₁ : AnalyticAt ℂ f₁ z) (h₂ : AnalyticAt ℂ f₂ z) (h₃ : AnalyticAt ℂ f₃ z) :
    gaussOperator a b c (fun w => f₁ w - α * f₂ w - β * f₃ w) z =
      gaussOperator a b c f₁ z - α * gaussOperator a b c f₂ z -
        β * gaussOperator a b c f₃ z := by
  have hd : deriv (fun w => f₁ w - α * f₂ w - β * f₃ w) =ᶠ[𝓝 z]
      fun w => deriv f₁ w - α * deriv f₂ w - β * deriv f₃ w := by
    filter_upwards [h₁.eventually_analyticAt, h₂.eventually_analyticAt,
      h₃.eventually_analyticAt] with w hw₁ hw₂ hw₃
    exact ((hw₁.differentiableAt.hasDerivAt.sub
      (hw₂.differentiableAt.hasDerivAt.const_mul α)).sub
      (hw₃.differentiableAt.hasDerivAt.const_mul β)).deriv
  have hdd : deriv (deriv (fun w => f₁ w - α * f₂ w - β * f₃ w)) z =
      deriv (deriv f₁) z - α * deriv (deriv f₂) z - β * deriv (deriv f₃) z := by
    rw [hd.deriv_eq]
    exact ((h₁.deriv.differentiableAt.hasDerivAt.sub
      (h₂.deriv.differentiableAt.hasDerivAt.const_mul α)).sub
      (h₃.deriv.differentiableAt.hasDerivAt.const_mul β)).deriv
  simp only [gaussOperator, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hdd, hd.eq_of_nhds]
  ring

/-! ### Logarithmic solutions for integral `c` (DLMF 15.10.8–10) -/

section LogSolutions

open FormalMultilinearSeries
open scoped ENNReal

/-- The Gauss operator applied to a power series, coefficientwise. -/
theorem _root_.HasFPowerSeriesOnBall.hasSum_gaussOperator {f : ℂ → ℂ} {c : ℕ → ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f (ofScalars ℂ c) 0 r) (a b d : ℂ) {z : ℂ}
    (hz : z ∈ Metric.eball (0 : ℂ) r) :
    HasSum (fun n : ℕ => ((n + 1) * (d + n) * c (n + 1) - (n + a) * (n + b) * c n) * z ^ n)
      (gaussOperator a b d f z) := by
  have h0 := h.hasSum_mul_pow hz
  have h1 := h.deriv_ofScalars.hasSum_mul_pow hz
  have hz1 := h.hasSum_z_mul_deriv hz
  have hz2 := h.deriv_ofScalars.hasSum_z_mul_deriv hz
  have hzz2 : HasSum (fun n : ℕ => (n : ℂ) * (n - 1) * c n * z ^ n)
      (z ^ 2 * deriv (deriv f) z) := by
    have hs : HasSum (fun n : ℕ =>
        (n + 1 : ℂ) * ((n + 1 : ℂ) - 1) * c (n + 1) * z ^ n)
        (z * deriv (deriv f) z) := by
      convert hz2 using 1
      funext n
      ring
    have ht := HasSum.mul_pow_shift (c := fun n => (n : ℂ) * (n - 1) * c n)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hs) (by simp)
    convert ht using 1
    ring
  have hall := ((hz2.add (h1.mul_left d)).sub (hzz2.add (hz1.mul_left (a + b + 1)))).sub
    (h0.mul_left (a * b))
  convert hall using 1
  · funext n; ring
  · simp only [gaussOperator, iteratedDeriv_succ, iteratedDeriv_zero]; ring

/-- The Gauss operator on `F · log`. -/
theorem gaussOperator_mul_log {a b c : ℂ} {F : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z)
    (hz : z ∈ slitPlane) :
    gaussOperator a b c (fun v => F v * log v) z =
      log z * gaussOperator a b c F z + (2 * (1 - z) * deriv F z + (c - 1) * F z / z -
        (a + b) * F z) := by
  have hz0 := slitPlane_ne_zero hz
  have hd : deriv (fun v => F v * log v) =ᶠ[𝓝 z] fun v => deriv F v * log v + F v * v⁻¹ := by
    filter_upwards [hF.eventually_analyticAt, isOpen_slitPlane.mem_nhds hz] with v hv hvs
    exact (hv.differentiableAt.hasDerivAt.mul (hasDerivAt_log hvs)).deriv
  have hdd : deriv (deriv (fun v => F v * log v)) z =
      deriv (deriv F) z * log z + deriv F z * z⁻¹ + (deriv F z * z⁻¹ + F z * (-(z ^ 2)⁻¹)) := by
    rw [hd.deriv_eq]
    have h := (hF.deriv.differentiableAt.hasDerivAt.mul (hasDerivAt_log hz)).add
      (hF.differentiableAt.hasDerivAt.mul (hasDerivAt_inv hz0))
    exact h.deriv
  simp only [gaussOperator, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hdd, hd.eq_of_nhds]
  field_simp
  ring

/-- For `v ≠ 0`, the derivative of `w ↦ w⁻ᵖ` at `v` is `-p v^{-(p+1)}`. -/
theorem hasDerivAt_recip_pow (p : ℕ) {v : ℂ} (hv : v ≠ 0) :
    HasDerivAt (fun w : ℂ => w⁻¹ ^ p) (-(p : ℂ) * v⁻¹ ^ (p + 1)) v := by
  have h := (hasDerivAt_inv hv).pow p
  refine h.congr_deriv ?_
  rcases p with _ | p
  · simp
  · simp only [Nat.add_sub_cancel]
    rw [show v⁻¹ ^ (p + 1 + 1) = v⁻¹ ^ p * (v ^ 2)⁻¹ by rw [← inv_pow v 2, ← pow_add]]
    push_cast
    ring

/-- The pole part of the logarithmic solutions (DLMF 15.10.8–10). -/
def logSing (a b : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n - 1),
    ((n - 1).factorial : ℂ) * (j.factorial : ℂ) /
      (((n - j - 2).factorial : ℂ) * poch (1 - a) (j + 1) * poch (1 - b) (j + 1)) * ((-z)⁻¹) ^ (j + 1)

/-- If `(x)_N ≠ 0` then `(x)_k ≠ 0` for every `k ≤ N`. -/
theorem poch_ne_zero_of_le {x : ℂ} {N k : ℕ} (hk : k ≤ N) (h : poch x N ≠ 0) : poch x k ≠ 0 := by
  intro h0
  apply h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [poch_add, h0, zero_mul]

/-- For `c = n ≥ 1`, the Gauss operator maps the pole part `logSing` to `(n - 1)/z`. -/
theorem gaussOperator_logSing {a b : ℂ} {n : ℕ} (hn : 0 < n)
    (ha : poch (1 - a) (n - 1) ≠ 0) (hb : poch (1 - b) (n - 1) ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    gaussOperator a b n (logSing a b n) z = (n - 1) / z := by
  set e : ℕ → ℂ := fun j => ((n - 1).factorial : ℂ) * (j.factorial : ℂ) /
      (((n - j - 2).factorial : ℂ) * poch (1 - a) (j + 1) * poch (1 - b) (j + 1)) with he
  set σ : ℕ → ℂ := fun j => e j * (-1) ^ (j + 1) with hσ
  have hS : logSing a b n = fun v => ∑ j ∈ Finset.range (n - 1), σ j * v⁻¹ ^ (j + 1) := by
    funext v
    simp only [logSing, hσ, he]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inv_neg, neg_eq_neg_one_mul, mul_pow, inv_pow]
    ring
  have hS1 : ∀ v : ℂ, v ≠ 0 → HasDerivAt (logSing a b n)
      (∑ j ∈ Finset.range (n - 1), σ j * (-((j + 1 : ℕ) : ℂ) * v⁻¹ ^ (j + 2))) v := by
    intro v hv
    rw [hS]
    exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_recip_pow (j + 1) hv).const_mul (σ j)
  have hS2 : HasDerivAt (fun v => ∑ j ∈ Finset.range (n - 1), σ j * (-((j + 1 : ℕ) : ℂ) * v⁻¹ ^ (j + 2)))
      (∑ j ∈ Finset.range (n - 1), σ j * (-((j + 1 : ℕ) : ℂ) * (-((j + 2 : ℕ) : ℂ) * z⁻¹ ^ (j + 3))))
      z :=
    HasDerivAt.fun_sum fun j _ => ((hasDerivAt_recip_pow (j + 2) hz).const_mul _).const_mul (σ j)
  have hev : deriv (logSing a b n) =ᶠ[𝓝 z]
      fun v => ∑ j ∈ Finset.range (n - 1), σ j * (-((j + 1 : ℕ) : ℂ) * v⁻¹ ^ (j + 2)) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with v hv
    exact (hS1 v hv).deriv
  simp only [gaussOperator, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hev.deriv_eq, hS2.deriv, (hS1 z hz).deriv, hS]
  set u := z⁻¹ with hu
  have hzu : z * u = 1 := mul_inv_cancel₀ hz
  set t : ℕ → ℂ := fun j => if j < n - 1 then σ j * (j + 1 - a) * (j + 1 - b) * u ^ (j + 1) else 0
    with ht
  have hterm : ∀ j ∈ Finset.range (n - 1),
      z * (1 - z) * (σ j * (-((j + 1 : ℕ) : ℂ) * (-((j + 2 : ℕ) : ℂ) * u ^ (j + 3)))) +
        (n - (a + b + 1) * z) * (σ j * (-((j + 1 : ℕ) : ℂ) * u ^ (j + 2))) -
        a * b * (σ j * u ^ (j + 1)) = t (j + 1) - t j := by
    intro j hj
    rw [Finset.mem_range] at hj
    have htj : t j = σ j * (j + 1 - a) * (j + 1 - b) * u ^ (j + 1) := by simp [ht, hj]
    have key : t (j + 1) = σ j * (j + 1) * (j + 2 - n) * u ^ (j + 2) := by
      by_cases hj1 : j + 1 < n - 1
      · obtain ⟨N, hN⟩ : ∃ N, n = N + j + 3 := ⟨n - j - 3, by omega⟩
        have hpa := poch_ne_zero_of_le (show j + 2 ≤ n - 1 by omega) ha
        have hpb := poch_ne_zero_of_le (show j + 2 ≤ n - 1 by omega) hb
        have hpa1 := poch_ne_zero_of_le (show j + 1 ≤ j + 2 by omega) hpa
        have hpb1 := poch_ne_zero_of_le (show j + 1 ≤ j + 2 by omega) hpb
        rw [poch_succ] at hpa hpb
        have h1 : n - j - 2 = N + 1 := by omega
        have h2 : n - (j + 1) - 2 = N := by omega
        simp only [ht, ite_eq_left_iff.mpr (fun h => absurd hj1 h), hσ, he, h1, h2]
        rw [poch_succ (1 - a) (j + 1), poch_succ (1 - b) (j + 1), Nat.factorial_succ j,
          Nat.factorial_succ N]
        have hn' : (n : ℂ) = N + j + 3 := by rw [hN]; push_cast; ring
        rw [hn']
        generalize poch (1 - a) (j + 1) = Pa at *
        generalize poch (1 - b) (j + 1) = Pb at *
        generalize ((n - 1).factorial : ℂ) = M
        have hF : (N.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr N.factorial_ne_zero
        have hJ : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
        have hN1 : ((N + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast at hpa hpb hN1 ⊢
        have hA := right_ne_zero_of_mul hpa
        have hB := right_ne_zero_of_mul hpb
        have hPa := left_ne_zero_of_mul hpa
        have hPb := left_ne_zero_of_mul hpb
        field_simp
        ring
      · have hjn : j + 2 = n := by omega
        simp only [ht, ite_eq_right_iff.mpr (fun h => absurd h hj1)]
        rw [← hjn]; push_cast; ring
    rw [key, htj]
    have e3 : u ^ (j + 3) = u ^ (j + 1) * u * u := by ring
    have e2 : u ^ (j + 2) = u ^ (j + 1) * u := by ring
    rw [e3, e2]
    generalize σ j = sj
    generalize u ^ (j + 1) = U
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    linear_combination (sj * U * (j + 1) * (j + 2) * (u - z * u - 1) +
      sj * U * (a + b + 1) * (j + 1)) * hzu
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hterm,
    Finset.sum_range_sub]
  have htn : t (n - 1) = 0 := by simp [ht]
  rw [htn, zero_sub]
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have : n = 1 := by omega
    subst this
    simp [ht]
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
    have h0 : (0 : ℕ) < N + 2 - 1 := by omega
    have hpa := poch_ne_zero_of_le (show 1 ≤ N + 2 - 1 by omega) ha
    have hpb := poch_ne_zero_of_le (show 1 ≤ N + 2 - 1 by omega) hb
    rw [poch_one] at hpa hpb
    have ht0 : t 0 = σ 0 * (1 - a) * (1 - b) * u := by
      simp only [ht]
      rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]
      simp
    have he0 : e 0 = ((N + 1 : ℕ) : ℂ) / ((1 - a) * (1 - b)) := by
      simp only [he]
      rw [show N + 2 - 1 = N + 1 by omega, show N + 2 - 0 - 2 = N by omega, Nat.factorial_succ N,
        Nat.factorial_zero, zero_add, poch_one, poch_one]
      have hF : (N.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr N.factorial_ne_zero
      push_cast
      field_simp
    rw [ht0, hσ]
    simp only
    rw [he0, hu]
    push_cast
    field_simp
    ring

/-- The pole part `logSing` is analytic away from `0`. -/
theorem analyticAt_logSing (a b : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0) : AnalyticAt ℂ (logSing a b n) z := by
  unfold logSing
  have h : ∀ j ∈ Finset.range (n - 1), AnalyticAt ℂ (fun v : ℂ => ((n - 1).factorial : ℂ) *
      (j.factorial : ℂ) / (((n - j - 2).factorial : ℂ) * poch (1 - a) (j + 1) *
        poch (1 - b) (j + 1)) * ((-v)⁻¹) ^ (j + 1)) z := fun j _ =>
    analyticAt_const.mul ((analyticAt_id.neg.inv (neg_ne_zero.mpr hz)).pow _)
  exact (Finset.analyticAt_fun_sum _ h)

/-- A logarithmic solution of the Gauss equation with integral denominator `n`, given the
recurrence for the coefficients of its power-series part. -/
theorem gaussOperator_logSolution {a b : ℂ} {n : ℕ} (hn : 0 < n)
    (ha : poch (1 - a) (n - 1) ≠ 0) (hb : poch (1 - b) (n - 1) ≠ 0) {h : ℕ → ℂ} {H : ℂ → ℂ}
    (hH : HasFPowerSeriesOnBall H (ofScalars ℂ h) 0 1)
    (hrec : ∀ k : ℕ, (k + 1) * (n + k) * h (k + 1) - (k + a) * (k + b) * h k +
      2 * (k + 1) * gaussHGCoeff a b n (k + 1) - (2 * k + a + b) * gaussHGCoeff a b n k +
      (n - 1) * gaussHGCoeff a b n (k + 1) = 0)
    {z : ℂ} (hz : ‖z‖ < 1) (hs : z ∈ slitPlane) :
    gaussOperator a b n (fun v => ₂F₁ a b (n : ℂ) v * log v - logSing a b n v + H v) z = 0 := by
  have hz0 := slitPlane_ne_zero hs
  have hz1 : z ≠ 1 := by rintro rfl; simp at hz
  set F : ℂ → ℂ := ₂F₁ a b (n : ℂ) with hFdef
  have hFs := hasFPowerSeriesOnBall_ordinaryHypergeometric a b (n : ℂ)
  have hzb : z ∈ Metric.eball (0 : ℂ) 1 := mem_eball_one_of_norm_lt_one hz
  have hFa : AnalyticAt ℂ F z := hFs.analyticAt_of_mem hzb
  have hFlog : AnalyticAt ℂ (fun v => F v * log v) z := hFa.mul (analyticAt_clog hs)
  have hHa : AnalyticAt ℂ H z := hH.analyticAt_of_mem hzb
  have hfun : (fun v => F v * log v - logSing a b n v + H v) =
      fun v => F v * log v - 1 * logSing a b n v - (-1) * H v := by funext v; ring
  rw [hfun, gaussOperator_sub_smul hFlog (analyticAt_logSing a b n hz0) hHa,
    gaussOperator_mul_log hFa hs, gaussOperator_logSing hn ha hb hz0]
  have hnc : ∀ k : ℕ, (n : ℂ) ≠ -(k : ℂ) := by
    intro k hk
    have := congrArg re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]
  have hLF : gaussOperator a b n F z = 0 := by
    have := ordinaryHypergeometric_ode (a := a) (b := b) hnc hz hz0 hz1
    simpa [gaussOperator, iteratedDeriv_succ, iteratedDeriv_zero] using this
  rw [hLF]
  -- the series parts
  set f := gaussHGCoeff a b (n : ℂ) with hf
  have h0 := hFs.hasSum_mul_pow hzb
  have h1 := hFs.deriv_ofScalars.hasSum_mul_pow hzb
  have hz1' := hFs.hasSum_z_mul_deriv hzb
  have hsh : HasSum (fun k : ℕ => f (k + 1) * z ^ k) ((F z - 1) / z) := by
    have h0' := (hasSum_nat_add_iff' 1).mpr h0
    have hf0 : f 0 = 1 := by simp [hf, gaussHGCoeff, poch_zero]
    simp only [Finset.sum_range_one, pow_zero, mul_one, hf0] at h0'
    have h2 := h0'.mul_left z⁻¹
    convert h2 using 1
    · funext k; rw [pow_succ]; field_simp
    · field_simp; rfl
  have hLH := hH.hasSum_gaussOperator a b (n : ℂ) hzb
  have hall := ((((h1.mul_left 2).sub (hz1'.mul_left 2)).add (hsh.mul_left ((n : ℂ) - 1))).sub
    (h0.mul_left (a + b))).add hLH
  have hzero : (fun k : ℕ => 2 * ((k + 1) * f (k + 1) * z ^ k) - 2 * ((k : ℂ) * f k * z ^ k) +
      ((n : ℂ) - 1) * (f (k + 1) * z ^ k) - (a + b) * (f k * z ^ k) +
      ((k + 1) * ((n : ℂ) + k) * h (k + 1) - (k + a) * (k + b) * h k) * z ^ k) = fun _ => 0 := by
    funext k
    linear_combination z ^ k * hrec k
  rw [hzero] at hall
  have hval := hall.unique hasSum_zero
  rw [← hFdef] at hval
  field_simp at hval ⊢
  linear_combination hval

/-- Signed coefficients of the pole part `logSing`. -/
def logSingCoeff (a b : ℂ) (n j : ℕ) : ℂ :=
  ((n - 1).factorial : ℂ) * (j.factorial : ℂ) /
    (((n - j - 2).factorial : ℂ) * poch (1 - a) (j + 1) * poch (1 - b) (j + 1)) * (-1) ^ (j + 1)

/-- The pole part `logSing` written with the signed coefficients `logSingCoeff`. -/
theorem logSing_eq (a b : ℂ) (n : ℕ) (v : ℂ) :
    logSing a b n v = ∑ j ∈ Finset.range (n - 1), logSingCoeff a b n j * v⁻¹ ^ (j + 1) := by
  simp only [logSing, logSingCoeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inv_neg, neg_eq_neg_one_mul, mul_pow, inv_pow]
  ring

/-- Termwise derivative of the pole part `logSing` away from `0`. -/
theorem hasDerivAt_logSing (a b : ℂ) (n : ℕ) {v : ℂ} (hv : v ≠ 0) :
    HasDerivAt (logSing a b n)
      (∑ j ∈ Finset.range (n - 1), logSingCoeff a b n j * (-((j + 1 : ℕ) : ℂ) * v⁻¹ ^ (j + 2))) v := by
  have h : logSing a b n = fun v => ∑ j ∈ Finset.range (n - 1), logSingCoeff a b n j * v⁻¹ ^ (j + 1) :=
    funext (logSing_eq a b n)
  rw [h]
  exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_recip_pow (j + 1) hv).const_mul _

/-- `z^n` times the pole part, a polynomial. -/
def logSingPoly0 (a b : ℂ) (n : ℕ) (v : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n - 1), logSingCoeff a b n j * v ^ (n - j - 1)

/-- `z^n` times the derivative of the pole part, a polynomial. -/
def logSingPoly1 (a b : ℂ) (n : ℕ) (v : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n - 1), logSingCoeff a b n j * (-((j + 1 : ℕ) : ℂ) * v ^ (n - j - 2))

/-- For `v ≠ 0` and `k ≤ n`, `vⁿ v⁻ᵏ = v^{n-k}`. -/
theorem pow_mul_recip_pow {v : ℂ} (hv : v ≠ 0) {n k : ℕ} (hk : k ≤ n) :
    v ^ n * v⁻¹ ^ k = v ^ (n - k) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left, pow_add, inv_pow]
  field_simp

/-- `zⁿ` times the pole part is the polynomial `logSingPoly0`. -/
theorem pow_mul_logSing (a b : ℂ) (n : ℕ) {v : ℂ} (hv : v ≠ 0) :
    v ^ n * logSing a b n v = logSingPoly0 a b n v := by
  rw [logSing_eq, logSingPoly0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [mul_left_comm, pow_mul_recip_pow hv (by omega), show n - (j + 1) = n - j - 1 by omega]

/-- `zⁿ` times the derivative of the pole part is the polynomial `logSingPoly1`. -/
theorem pow_mul_deriv_logSing (a b : ℂ) (n : ℕ) {v : ℂ} (hv : v ≠ 0) :
    v ^ n * deriv (logSing a b n) v = logSingPoly1 a b n v := by
  rw [(hasDerivAt_logSing a b n hv).deriv, logSingPoly1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [show v ^ n * (logSingCoeff a b n j * (-((j + 1 : ℕ) : ℂ) * v⁻¹ ^ (j + 2))) =
      logSingCoeff a b n j * (-((j + 1 : ℕ) : ℂ) * (v ^ n * v⁻¹ ^ (j + 2))) by ring,
    pow_mul_recip_pow hv (by omega), show n - (j + 2) = n - j - 2 by omega]

/-- The polynomial `logSingPoly0` is entire. -/
theorem differentiable_logSingPoly0 (a b : ℂ) (n : ℕ) : Differentiable ℂ (logSingPoly0 a b n) := by
  unfold logSingPoly0
  fun_prop

/-- The polynomial `logSingPoly1` is entire. -/
theorem differentiable_logSingPoly1 (a b : ℂ) (n : ℕ) : Differentiable ℂ (logSingPoly1 a b n) := by
  unfold logSingPoly1
  fun_prop

/-- The leading coefficient of the pole part is nonzero when `n ≥ 2` and the Pochhammer factors do
  not vanish. -/
theorem logSingCoeff_ne_zero {a b : ℂ} {n : ℕ} (hn : 2 ≤ n)
    (ha : poch (1 - a) (n - 1) ≠ 0) (hb : poch (1 - b) (n - 1) ≠ 0) :
    logSingCoeff a b n (n - 2) ≠ 0 := by
  unfold logSingCoeff
  rw [show n - 2 + 1 = n - 1 by omega]
  have h1 : ((n - 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : ((n - 2).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : ((n - (n - 2) - 2).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  exact mul_ne_zero (div_ne_zero (mul_ne_zero h1 h2) (mul_ne_zero (mul_ne_zero h3 ha) hb))
    (pow_ne_zero _ (by norm_num))

/-- The Wronskian of `₂F₁(a,b;n;z)` and a logarithmic solution does not vanish. -/
theorem wronskian_logSolution_ne_zero {a b : ℂ} {n : ℕ} (hn : 0 < n)
    (ha : poch (1 - a) (n - 1) ≠ 0) (hb : poch (1 - b) (n - 1) ≠ 0) {h : ℕ → ℂ} {H : ℂ → ℂ}
    (hH : HasFPowerSeriesOnBall H (ofScalars ℂ h) 0 1)
    (hrec : ∀ k : ℕ, (k + 1) * (n + k) * h (k + 1) - (k + a) * (k + b) * h k +
      2 * (k + 1) * gaussHGCoeff a b n (k + 1) - (2 * k + a + b) * gaussHGCoeff a b n k +
      (n - 1) * gaussHGCoeff a b n (k + 1) = 0)
    {z : ℂ} (hz : ‖z‖ < 1) (hs : z ∈ slitPlane) :
    solutionWronskian (₂F₁ a b (n : ℂ))
      (fun v => ₂F₁ a b (n : ℂ) v * log v - logSing a b n v + H v) z ≠ 0 := by
  set F : ℂ → ℂ := ₂F₁ a b (n : ℂ) with hFdef
  set w : ℂ → ℂ := fun v => F v * log v - logSing a b n v + H v with hw
  set U : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ slitPlane with hU
  have hUo : IsOpen U := Metric.isOpen_ball.inter isOpen_slitPlane
  have hFs := hasFPowerSeriesOnBall_ordinaryHypergeometric a b (n : ℂ)
  have hball : ∀ v ∈ Metric.ball (0 : ℂ) 1, ‖v‖ < 1 := fun v hv => by simpa using hv
  have hFa : ∀ v ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ F v := fun v hv =>
    hFs.analyticAt_of_mem (mem_eball_one_of_norm_lt_one (hball v hv))
  have hHa : ∀ v ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ H v := fun v hv =>
    hH.analyticAt_of_mem (mem_eball_one_of_norm_lt_one (hball v hv))
  have hwa : ∀ v ∈ U, AnalyticAt ℂ w v := fun v hv =>
    (((hFa v hv.1).mul (analyticAt_clog hv.2)).sub
      (analyticAt_logSing a b n (slitPlane_ne_zero hv.2))).add (hHa v hv.1)
  have hnc : ∀ k : ℕ, (n : ℂ) ≠ -(k : ℂ) := by
    intro k hk
    have := congrArg re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]
  have hodeF : ∀ v ∈ U, gaussOperator a b n F v = 0 := by
    intro v hv
    have hv1 : v ≠ 1 := by rintro rfl; simpa using hball _ hv.1
    have := ordinaryHypergeometric_ode (a := a) (b := b) hnc (hball v hv.1)
      (slitPlane_ne_zero hv.2) hv1
    simpa [gaussOperator, iteratedDeriv_succ, iteratedDeriv_zero] using this
  have hodew : ∀ v ∈ U, gaussOperator a b n w v = 0 := fun v hv =>
    gaussOperator_logSolution hn ha hb hH hrec (hball v hv.1) hv.2
  -- Abel's identity
  set W : ℂ → ℂ := solutionWronskian F w with hWdef
  have hWd : ∀ v ∈ U, HasDerivAt W (F v * deriv (deriv w) v - deriv (deriv F) v * w v) v := by
    intro v hv
    have h1 := (hFa v hv.1).differentiableAt.hasDerivAt
    have h2 := (hFa v hv.1).deriv.differentiableAt.hasDerivAt
    have h3 := (hwa v hv).differentiableAt.hasDerivAt
    have h4 := (hwa v hv).deriv.differentiableAt.hasDerivAt
    exact ((h1.mul h4).sub (h2.mul h3)).congr_deriv (by ring)
  have hAbel : ∀ v ∈ U, v * (1 - v) * (F v * deriv (deriv w) v - deriv (deriv F) v * w v) =
      -((n : ℂ) - (a + b + 1) * v) * W v := by
    intro v hv
    have e1 := hodeF v hv
    have e2 := hodew v hv
    simp only [gaussOperator, iteratedDeriv_succ, iteratedDeriv_zero] at e1 e2
    simp only [hWdef, solutionWronskian]
    linear_combination F v * e2 - w v * e1
  -- the analytic factor
  set G : ℂ → ℂ := fun v => v ^ (n - 1) * F v ^ 2 +
    F v * (v ^ n * deriv H v - logSingPoly1 a b n v) -
    deriv F v * (v ^ n * H v - logSingPoly0 a b n v) with hG
  have hGW : ∀ v ∈ U, G v = v ^ n * W v := by
    intro v hv
    have hv0 := slitPlane_ne_zero hv.2
    have hdw : deriv w v = deriv F v * log v + F v * v⁻¹ - deriv (logSing a b n) v + deriv H v := by
      have := ((((hFa v hv.1).differentiableAt.hasDerivAt.mul (hasDerivAt_log hv.2)).sub
        (hasDerivAt_logSing a b n hv0)).add (hHa v hv.1).differentiableAt.hasDerivAt)
      rw [← (hasDerivAt_logSing a b n hv0).deriv] at this
      exact this.deriv
    have hP0 := pow_mul_logSing a b n hv0
    have hP1 := pow_mul_deriv_logSing a b n hv0
    have hvn : v ^ n * v⁻¹ = v ^ (n - 1) := by
      rw [← pow_mul_recip_pow hv0 (show 1 ≤ n by omega), pow_one]
    simp only [hG, hWdef, solutionWronskian]
    rw [hdw]
    simp only [hw]
    rw [← hP0, ← hP1]
    linear_combination (-(F v) ^ 2) * hvn
  -- `G (1 - v)^s` is constant on the disk
  set s : ℂ := a + b + 1 - n with hsdef
  clear_value s
  set K : ℂ → ℂ := fun v => G v * (1 - v) ^ s with hK
  have hslit1 : ∀ v ∈ Metric.ball (0 : ℂ) 1, 1 - v ∈ slitPlane := by
    intro v hv
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    have := (re_le_norm v).trans_lt (hball v hv)
    simp only [sub_re, one_re]; linarith
  have hGa : ∀ v ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ G v := by
    intro v hv
    have hP0 : AnalyticAt ℂ (logSingPoly0 a b n) v :=
      (differentiable_logSingPoly0 a b n).analyticAt v
    have hP1 : AnalyticAt ℂ (logSingPoly1 a b n) v :=
      (differentiable_logSingPoly1 a b n).analyticAt v
    exact ((analyticAt_id.pow _).mul ((hFa v hv).pow 2)).add
      ((hFa v hv).mul (((analyticAt_id.pow _).mul (hHa v hv).deriv).sub hP1)) |>.sub
      ((hFa v hv).deriv.mul (((analyticAt_id.pow _).mul (hHa v hv)).sub hP0))
  have hKa : AnalyticOnNhd ℂ K (Metric.ball (0 : ℂ) 1) := fun v hv =>
    (hGa v hv).mul ((analyticAt_const.sub analyticAt_id).cpow analyticAt_const (hslit1 v hv))
  have hKd0 : ∀ v ∈ U, deriv K v = 0 := by
    intro v hv
    have hv0 := slitPlane_ne_zero hv.2
    have hv1 : 1 - v ≠ 0 := slitPlane_ne_zero (hslit1 v hv.1)
    have hGev : G =ᶠ[𝓝 v] fun u => u ^ n * W u := by
      filter_upwards [hUo.mem_nhds hv] with u hu
      exact hGW u hu
    have hGd : HasDerivAt G ((n : ℂ) * v ^ (n - 1) * W v +
        v ^ n * (F v * deriv (deriv w) v - deriv (deriv F) v * w v)) v := by
      have := (hasDerivAt_pow n v).mul (hWd v hv)
      exact (this.congr_of_eventuallyEq hGev).congr_deriv (by ring)
    have hp := ((hasDerivAt_const v (1 : ℂ)).sub (hasDerivAt_id v)).cpow_const (c := s)
      (hslit1 v hv.1)
    have hKd : HasDerivAt K _ v := hGd.mul hp
    rw [hKd.deriv]
    simp only [_root_.id, Pi.sub_apply]
    rw [cpow_sub _ _ hv1, cpow_one]
    have hA := hAbel v hv
    have hGv := hGW v hv
    have hvn : v ^ n = v ^ (n - 1) * v := by
      rw [← pow_succ, show n - 1 + 1 = n by omega]
    rw [hvn] at hGv ⊢
    have hdi : (1 - v) * (1 - v)⁻¹ = 1 := mul_inv_cancel₀ hv1
    rw [div_eq_mul_inv]
    apply mul_left_cancel₀ hv1
    linear_combination (1 - v) ^ s * v ^ (n - 1) * hA - s * (1 - v) ^ s * hGv -
      (1 - v) ^ s * v ^ (n - 1) * v * W v * hsdef - G v * s * (1 - v) ^ s * hdi
  have hhalf : (1 / 2 : ℂ) ∈ U := ⟨by simp; norm_num, by
    refine mem_slitPlane_iff.mpr (Or.inl ?_); norm_num⟩
  have hev : deriv K =ᶠ[𝓝 (1 / 2 : ℂ)] 0 := by
    filter_upwards [hUo.mem_nhds hhalf] with v hv
    exact hKd0 v hv
  have hzero := hKa.deriv.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : ℂ) 1).isPreconnected hhalf.1 hev
  have hzb : z ∈ Metric.ball (0 : ℂ) 1 := by simpa using hz
  have hKc := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
    (fun v hv => (hKa v hv).differentiableAt.differentiableWithinAt)
    (fun v hv => hzero hv) (x := z) (y := 0) hzb (by simp)
  have hK0 : K 0 = G 0 := by simp [hK]
  have hF0 : F 0 = 1 := by simp [hFdef, ordinaryHypergeometric_zero]
  have hP0 : logSingPoly0 a b n 0 = 0 := by
    unfold logSingPoly0
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [zero_pow (by omega), mul_zero]
  have h0n : (0 : ℂ) ^ n = 0 := zero_pow (by omega)
  have hG0 : G 0 ≠ 0 := by
    simp only [hG, hF0, h0n, hP0, zero_mul, zero_sub, sub_zero, mul_zero, one_pow, mul_one]
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have : n = 1 := by omega
      subst this
      simp [logSingPoly1]
    · have hP1 : logSingPoly1 a b n 0 = logSingCoeff a b n (n - 2) * (-((n - 1 : ℕ) : ℂ)) := by
        unfold logSingPoly1
        rw [Finset.sum_eq_single (n - 2)]
        · rw [show n - 2 + 1 = n - 1 by omega, show n - (n - 2) - 2 = 0 by omega, pow_zero, mul_one]
        · intro j hj hjn
          rw [Finset.mem_range] at hj
          rw [zero_pow (by omega), mul_zero, mul_zero]
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      rw [hP1]
      have hc := logSingCoeff_ne_zero hn2 ha hb
      have hn1 : ((n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [zero_pow (by omega)]
      simp only [zero_add, one_mul, mul_neg, neg_neg]
      exact mul_ne_zero hc hn1
  intro hW0
  have hGz : G z = 0 := by rw [hGW z ⟨hzb, hs⟩, hW0, mul_zero]
  have : K z = 0 := by simp [hK, hGz]
  rw [hKc, hK0] at this
  exact hG0 this

/-- The Gauss operator at `z` depends only on the germ of the function at `z`. -/
theorem gaussOperator_congr {a b c : ℂ} {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    gaussOperator a b c f z = gaussOperator a b c g z := by
  simp only [gaussOperator, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [h.deriv.deriv_eq, h.deriv_eq, h.eq_of_nhds]

/-- The Wronskian at `z` depends only on the germ of the second function at `z`. -/
theorem solutionWronskian_congr {f g₁ g₂ : ℂ → ℂ} {z : ℂ} (h : g₁ =ᶠ[𝓝 z] g₂) :
    solutionWronskian f g₁ z = solutionWronskian f g₂ z := by
  simp only [solutionWronskian]
  rw [h.deriv_eq, h.eq_of_nhds]

/-- A coefficient sequence with `∑ ‖h k‖ r^k < ∞` for all `r < 1` has radius at least one. -/
theorem one_le_radius_ofScalars {h : ℕ → ℂ}
    (hs : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable fun k => ‖h k‖ * r ^ k) :
    1 ≤ (ofScalars ℂ h).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  refine (ofScalars ℂ h).le_radius_of_summable ?_
  have hr' : (r : ℝ) < 1 := by exact_mod_cast hr
  refine (hs r r.2 hr').congr fun k => ?_
  rw [ofScalars_norm]

/-- Coefficients eventually of polynomial growth relative to a Gauss series give radius at
least one. -/
theorem one_le_radius_of_le_gaussHGCoeff {h : ℕ → ℂ} (a b c : ℂ) {C : ℝ} (N : ℕ)
    (hC : ∀ k, N ≤ k → ‖h k‖ ≤ C * (k + 1) * ‖gaussHGCoeff a b c k‖) :
    1 ≤ (ofScalars ℂ h).radius := by
  refine one_le_radius_ofScalars fun r hr0 hr1 => ?_
  set r' : ℝ := (1 + r) / 2 with hr'
  have hr'0 : 0 < r' := by rw [hr']; linarith
  have hr'1 : r' < 1 := by rw [hr']; linarith
  have hsum := summable_norm_gaussHGCoeff_mul_pow a b c (z := (r' : ℂ))
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr'0]; exact hr'1)
  set M := ∑' k, ‖gaussHGCoeff a b c k * (r' : ℂ) ^ k‖
  have hM : ∀ k, ‖gaussHGCoeff a b c k‖ * r' ^ k ≤ M := by
    intro k
    have := hsum.le_tsum k (fun j _ => norm_nonneg _)
    rwa [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr'0] at this
  set q := r / r' with hq
  have hq0 : 0 ≤ q := div_nonneg hr0 hr'0.le
  have hq1 : q < 1 := by rw [hq, div_lt_one hr'0, hr']; linarith
  have hgeom : Summable fun k : ℕ => ((k : ℝ) + 1) * q ^ k := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)
    have h2 := summable_geometric_of_lt_one hq0 hq1
    refine (h1.add h2).congr fun k => ?_
    simp
    ring
  have hgeom' := (summable_nat_add_iff N).mpr hgeom
  refine (summable_nat_add_iff N).mp ?_
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((hgeom'.mul_left (|C| * M)))
  have hk := hC (k + N) (by omega)
  have hrk : r ^ (k + N) = q ^ (k + N) * r' ^ (k + N) := by
    rw [hq, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hr'0.ne')]
  rw [hrk]
  push_cast at hk ⊢
  calc ‖h (k + N)‖ * (q ^ (k + N) * r' ^ (k + N))
      ≤ C * ((k : ℝ) + N + 1) * ‖gaussHGCoeff a b c (k + N)‖ * (q ^ (k + N) * r' ^ (k + N)) := by
        gcongr
    _ = C * ((k : ℝ) + N + 1) * q ^ (k + N) * (‖gaussHGCoeff a b c (k + N)‖ * r' ^ (k + N)) := by
        ring
    _ ≤ |C| * ((k : ℝ) + N + 1) * q ^ (k + N) * M := by
        calc C * ((k : ℝ) + N + 1) * q ^ (k + N) * (‖gaussHGCoeff a b c (k + N)‖ * r' ^ (k + N))
            ≤ |C| * ((k : ℝ) + N + 1) * q ^ (k + N) *
                (‖gaussHGCoeff a b c (k + N)‖ * r' ^ (k + N)) := by
              gcongr; exact le_abs_self C
          _ ≤ |C| * ((k : ℝ) + N + 1) * q ^ (k + N) * M := by gcongr; exact hM _
    _ = |C| * M * (((k : ℝ) + N + 1) * q ^ (k + N)) := by ring

/-- Linear growth of `ψ(x + k)`. -/
theorem exists_norm_digamma_add_nat_le {x : ℂ} (hx : ∀ m : ℕ, x ≠ -(m : ℂ)) :
    ∃ C : ℝ, ∀ k : ℕ, ‖digamma (x + k)‖ ≤ C * (k + 1) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖x‖ + 1 ≤ N := exists_nat_ge _
  set M : ℝ := 1 + ∑ j ∈ Finset.range N, ‖(x + j)⁻¹‖ with hM
  have hM0 : 0 ≤ M := by positivity
  have hb : ∀ j : ℕ, ‖(x + j)⁻¹‖ ≤ M := by
    intro j
    rcases Nat.lt_or_ge j N with hj | hj
    · have := Finset.single_le_sum (f := fun j : ℕ => ‖(x + j)⁻¹‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr hj)
      linarith
    · have hj' : (N : ℝ) ≤ j := by exact_mod_cast hj
      have h1 : 1 ≤ ‖x + j‖ := by
        have := norm_sub_norm_le ((j : ℂ)) (-x)
        rw [Complex.norm_natCast, norm_neg, sub_neg_eq_add, add_comm] at this
        linarith
      rw [norm_inv]
      have := inv_le_one_of_one_le₀ h1
      have : 0 ≤ ∑ j ∈ Finset.range N, ‖(x + j)⁻¹‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      linarith
  refine ⟨‖digamma x‖ + M, fun k => ?_⟩
  rw [digamma_apply_add_nat hx k]
  calc ‖digamma x + ∑ j ∈ Finset.range k, (x + j)⁻¹‖
      ≤ ‖digamma x‖ + ∑ j ∈ Finset.range k, ‖(x + j)⁻¹‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_sum_le _ _)
    _ ≤ ‖digamma x‖ + k * M := by
        gcongr
        calc ∑ j ∈ Finset.range k, ‖(x + j)⁻¹‖ ≤ ∑ _j ∈ Finset.range k, M :=
              Finset.sum_le_sum fun j _ => hb j
          _ = k * M := by simp
    _ ≤ (‖digamma x‖ + M) * (k + 1) := by
        have : 0 ≤ ‖digamma x‖ := norm_nonneg _
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith

/-- A complex number that is not an integer is not a nonpositive integer. -/
theorem not_neg_nat_of_not_int {c : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ)) : ∀ k : ℕ, c ≠ -(k : ℂ) := by
  intro k h
  exact hc (-(k : ℤ)) (by rw [h]; push_cast; ring)

/-- A positive natural number is not a nonpositive integer. -/
theorem natCast_not_neg_nat {n : ℕ} (hn : 0 < n) : ∀ k : ℕ, (n : ℂ) ≠ -(k : ℂ) := by
  intro k hk
  have := congrArg re hk
  simp at this
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]

/-- The power series part is analytic on the unit disk, given a radius bound. -/
theorem hasFPowerSeriesOnBall_ofScalars_sum {h : ℕ → ℂ} (hr : 1 ≤ (ofScalars ℂ h).radius) :
    HasFPowerSeriesOnBall (ofScalars ℂ h).sum (ofScalars ℂ h) 0 1 :=
  ((ofScalars ℂ h).hasFPowerSeriesOnBall (lt_of_lt_of_le one_pos hr)).mono one_pos hr

@[dlmf 15.10.E8]
theorem logarithmic_second_fundamental
    {a b : ℂ}
    (n : ℕ)
    (hn : 0 < n)
    (ha : ∀ k : ℤ, a ≠
    (k : ℂ))
    (hb : ∀ k : ℤ, b ≠
    (k : ℂ))
    {z : ℂ}
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane) :
    gaussOperator a b n (logarithmicSecond a b n) z = 0 ∧
      solutionWronskian (₂F₁ a b (n : ℂ)) (logarithmicSecond a b n) z ≠ 0 := by
  have ha' := not_neg_nat_of_not_int ha
  have hb' := not_neg_nat_of_not_int hb
  have hnc := natCast_not_neg_nat hn
  have h1c : ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := fun m => by
    simpa using natCast_not_neg_nat (n := 1) one_pos m
  set δ : ℕ → ℂ := fun k => digamma (a + k) + digamma (b + k) - digamma (1 + k) - digamma (n + k)
    with hδ
  set h : ℕ → ℂ := fun k => gaussHGCoeff a b n k * δ k with hh
  obtain ⟨Ca, hCa⟩ := exists_norm_digamma_add_nat_le ha'
  obtain ⟨Cb, hCb⟩ := exists_norm_digamma_add_nat_le hb'
  obtain ⟨C1, hC1⟩ := exists_norm_digamma_add_nat_le h1c
  obtain ⟨Cn, hCn⟩ := exists_norm_digamma_add_nat_le hnc
  have hr : 1 ≤ (ofScalars ℂ h).radius := by
    refine one_le_radius_of_le_gaussHGCoeff a b n (C := Ca + Cb + C1 + Cn) 0 fun k _ => ?_
    simp only [hh, hδ, norm_mul]
    have : ‖digamma (a + k) + digamma (b + k) - digamma (1 + k) - digamma (n + k)‖ ≤
        (Ca + Cb + C1 + Cn) * (k + 1) := by
      calc ‖digamma (a + k) + digamma (b + k) - digamma (1 + k) - digamma (n + k)‖
          ≤ ‖digamma (a + k) + digamma (b + k) - digamma (1 + k)‖ + ‖digamma (n + k)‖ :=
            norm_sub_le _ _
        _ ≤ ‖digamma (a + k) + digamma (b + k)‖ + ‖digamma (1 + k)‖ + ‖digamma (n + k)‖ := by
            gcongr; exact norm_sub_le _ _
        _ ≤ ‖digamma (a + k)‖ + ‖digamma (b + k)‖ + ‖digamma (1 + k)‖ + ‖digamma (n + k)‖ := by
            gcongr; exact norm_add_le _ _
        _ ≤ Ca * (k + 1) + Cb * (k + 1) + C1 * (k + 1) + Cn * (k + 1) := by
            gcongr
            · exact hCa k
            · exact hCb k
            · exact hC1 k
            · exact hCn k
        _ = _ := by ring
    calc ‖gaussHGCoeff a b n k‖ * ‖digamma (a + k) + digamma (b + k) - digamma (1 + k) -
          digamma (n + k)‖ ≤ ‖gaussHGCoeff a b n k‖ * ((Ca + Cb + C1 + Cn) * (k + 1)) := by
          gcongr
      _ = _ := by ring
  have hH := hasFPowerSeriesOnBall_ofScalars_sum hr
  set H := (ofScalars ℂ h).sum with hHdef
  have hrec : ∀ k : ℕ, (k + 1) * (n + k) * h (k + 1) - (k + a) * (k + b) * h k +
      2 * (k + 1) * gaussHGCoeff a b n (k + 1) - (2 * k + a + b) * gaussHGCoeff a b n k +
      (n - 1) * gaussHGCoeff a b n (k + 1) = 0 := by
    intro k
    have hrec0 := gaussHGCoeff_recurrence (a := a) (b := b) hnc k
    have hk : ∀ x : ℂ, (∀ m : ℕ, x ≠ -(m : ℂ)) →
        digamma (x + ((k + 1 : ℕ) : ℂ)) = digamma (x + k) + (x + k)⁻¹ := by
      intro x hx
      rw [show x + ((k + 1 : ℕ) : ℂ) = (x + k) + 1 by push_cast; ring]
      exact digamma_apply_add_one _ (not_neg_nat_add_nat hx k)
    have hne : ∀ x : ℂ, (∀ m : ℕ, x ≠ -(m : ℂ)) → (x + k) * (x + k)⁻¹ = 1 := fun x hx =>
      mul_inv_cancel₀ (by simpa using not_neg_nat_add_nat hx k 0)
    simp only [hh, hδ]
    rw [hk a ha', hk b hb', hk 1 h1c, hk n hnc]
    linear_combination (digamma (a + k) + digamma (b + k) - digamma (1 + k) - digamma (n + k) +
        (a + k)⁻¹ + (b + k)⁻¹) * hrec0 +
      (b + k) * gaussHGCoeff a b n k * hne a ha' + (a + k) * gaussHGCoeff a b n k * hne b hb' -
      (n + k) * gaussHGCoeff a b n (k + 1) * hne 1 h1c -
      (k + 1) * gaussHGCoeff a b n (k + 1) * hne n hnc
  have hpa : poch (1 - a) (n - 1) ≠ 0 := poch_ne_zero_of_not_neg_nat
    (fun k hk => ha (k + 1) (by push_cast; linear_combination -hk)) _
  have hpb : poch (1 - b) (n - 1) ≠ 0 := poch_ne_zero_of_not_neg_nat
    (fun k hk => hb (k + 1) (by push_cast; linear_combination -hk)) _
  have hev : logarithmicSecond a b n =ᶠ[𝓝 z]
      fun v => ₂F₁ a b (n : ℂ) v * log v - logSing a b n v + H v := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show z ∈ Metric.ball (0 : ℂ) 1 by simpa using hz)]
      with v hv
    have hv' : v ∈ Metric.eball (0 : ℂ) 1 := mem_eball_one_of_norm_lt_one (by simpa using hv)
    rw [logarithmicSecond, ← (hH.hasSum_mul_pow hv').tsum_eq]
    congr 1
    refine tsum_congr fun k => ?_
    simp only [hh, hδ]
    ring
  refine ⟨?_, ?_⟩
  · rw [gaussOperator_congr hev]
    exact gaussOperator_logSolution hn hpa hpb hH hrec hz hs
  · rw [solutionWronskian_congr hev]
    exact wronskian_logSolution_ne_zero hn hpa hpb hH hrec hz hs

/-- For a positive integer `n`, `k! ≤ ‖(n)ₖ‖`. -/
theorem factorial_le_norm_poch_natCast {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (k.factorial : ℝ) ≤ ‖poch (n : ℂ) k‖ :=
  factorial_le_norm_ascPochhammer_eval (by simp; exact_mod_cast hn) k

@[dlmf 15.10.E9]
theorem logarithmic_second_terminating_fundamental
    {b : ℂ}
    (m n : ℕ)
    (hn : 0 < n)
    (hb : ∀ k : ℤ, b ≠
    (k : ℂ))
    {z : ℂ}
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane) :
    gaussOperator (-m) b n (logarithmicSecondTerminating b m n) z = 0 ∧
      solutionWronskian (₂F₁ (-m : ℂ) b (n : ℂ)) (logarithmicSecondTerminating b m n) z ≠ 0 := by
  have hb' := not_neg_nat_of_not_int hb
  have hnc := natCast_not_neg_nat hn
  have h1c : ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := fun m => by
    simpa using natCast_not_neg_nat (n := 1) one_pos m
  set f : ℕ → ℂ := gaussHGCoeff (-(m : ℂ)) b n with hf
  set δ : ℕ → ℂ := fun k => digamma (1 + m - k) + digamma (b + k) - digamma (1 + k) -
    digamma (n + k) with hδ
  set h : ℕ → ℂ := fun k => if k ≤ m then f k * δ k else
    (-1) ^ m * (m.factorial : ℂ) * ((k - m - 1).factorial : ℂ) * poch b k /
      (poch n k * (k.factorial : ℂ)) with hh
  have hf0 : ∀ k, m < k → f k = 0 := fun k hk => by
    simp only [hf, gaussHGCoeff, poch_neg_nat_eq_zero hk, zero_mul, zero_div]
  have hr : 1 ≤ (ofScalars ℂ h).radius := by
    refine one_le_radius_of_le_gaussHGCoeff b 1 1 (C := m.factorial) (m + 1) fun k hk => ?_
    have hkm : ¬ k ≤ m := by omega
    simp only [hh, ite_eq_right_iff.mpr (fun h => absurd h hkm)]
    have hfk : (0 : ℝ) < k.factorial := by positivity
    have hpn := factorial_le_norm_poch_natCast hn k
    have hkf : (((k - m - 1).factorial : ℕ) : ℝ) ≤ k.factorial :=
      by exact_mod_cast Nat.factorial_le (by omega)
    rw [gaussHGCoeff_self_right]
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast]
    have hQ : (0 : ℝ) < ‖poch (n : ℂ) k‖ := lt_of_lt_of_le hfk hpn
    rw [div_le_iff₀ (mul_pos hQ hfk)]
    have e : (m.factorial : ℝ) * (k + 1) * (‖poch b k‖ / k.factorial) * (‖poch (n : ℂ) k‖ * k.factorial)
        = m.factorial * ‖poch b k‖ * ((k + 1) * ‖poch (n : ℂ) k‖) := by
      field_simp
    rw [e]
    have h1 : (k.factorial : ℝ) ≤ (k + 1) * ‖poch (n : ℂ) k‖ := by
      nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h2 : (0 : ℝ) ≤ m.factorial * ‖poch b k‖ := by positivity
    calc (m.factorial : ℝ) * ((k - m - 1).factorial : ℝ) * ‖poch b k‖
        ≤ m.factorial * k.factorial * ‖poch b k‖ := by gcongr
      _ = m.factorial * ‖poch b k‖ * k.factorial := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2
  have hH := hasFPowerSeriesOnBall_ofScalars_sum hr
  set H := (ofScalars ℂ h).sum with hHdef
  have hrec : ∀ k : ℕ, (k + 1) * (n + k) * h (k + 1) - (k + -(m : ℂ)) * (k + b) * h k +
      2 * (k + 1) * f (k + 1) - (2 * k + -(m : ℂ) + b) * f k + (n - 1) * f (k + 1) = 0 := by
    intro k
    have hrec0 := gaussHGCoeff_recurrence (a := -(m : ℂ)) (b := b) hnc k
    rw [← hf] at hrec0
    rcases Nat.lt_trichotomy k m with hkm | rfl | hkm
    · -- both coefficients come from the finite part
      have hk1 : k + 1 ≤ m := hkm
      simp only [hh, ite_eq_left_iff.mpr (fun h => absurd hk1 h),
        ite_eq_left_iff.mpr (fun h => absurd hkm.le h), hδ]
      have hshift : ∀ x : ℂ, (∀ j : ℕ, x ≠ -(j : ℂ)) →
          digamma (x + ((k + 1 : ℕ) : ℂ)) = digamma (x + k) + (x + k)⁻¹ := by
        intro x hx
        rw [show x + ((k + 1 : ℕ) : ℂ) = (x + k) + 1 by push_cast; ring]
        exact digamma_apply_add_one _ (not_neg_nat_add_nat hx k)
      have hne : ∀ x : ℂ, (∀ j : ℕ, x ≠ -(j : ℂ)) → (x + k) * (x + k)⁻¹ = 1 := fun x hx =>
        mul_inv_cancel₀ (by simpa using not_neg_nat_add_nat hx k 0)
      have hxpos : ∀ j : ℕ, ((m - k - 1 : ℕ) : ℂ) + 1 ≠ -(j : ℂ) := by
        intro j hj
        have := congrArg re hj
        simp at this
        linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg (m - k - 1) : (0 : ℝ) ≤ _)]
      have hmk : ((m - k - 1 : ℕ) : ℂ) + 1 = (m : ℂ) - k := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      have hdm : digamma (1 + m - k) = digamma (1 + m - ((k + 1 : ℕ) : ℂ)) + ((m : ℂ) - k)⁻¹ := by
        rw [show (1 : ℂ) + m - ((k + 1 : ℕ) : ℂ) = ((m - k - 1 : ℕ) : ℂ) + 1 by rw [hmk]; push_cast; ring,
          show (1 : ℂ) + m - k = ((m - k - 1 : ℕ) : ℂ) + 1 + 1 by rw [hmk]; ring,
          digamma_apply_add_one _ hxpos, hmk]
      have hx : ((m : ℂ) - k) * ((m : ℂ) - k)⁻¹ = 1 :=
        mul_inv_cancel₀ (by rw [← hmk]; simpa using hxpos 0)
      rw [hshift b hb', hshift 1 h1c, hshift n hnc,
        show digamma (1 + m - ((k + 1 : ℕ) : ℂ)) = digamma (1 + m - k) - ((m : ℂ) - k)⁻¹ by
          rw [hdm]; ring]
      linear_combination (digamma (1 + m - k) + digamma (b + k) - digamma (1 + k) - digamma (n + k) -
          ((m : ℂ) - k)⁻¹ + (b + k)⁻¹) * hrec0 +
        (b + k) * f k * hx + (-(m : ℂ) + k) * f k * hne b hb' -
        (n + k) * f (k + 1) * hne 1 h1c - (k + 1) * f (k + 1) * hne n hnc
    · -- the transition `k = m`
      simp only [hh, ite_eq_left_iff.mpr (fun h => absurd le_rfl h), ite_eq_right_iff.mpr (fun h => absurd h (by omega : ¬ k + 1 ≤ k)),
        hf0 (k + 1) (by omega), show k + 1 - k - 1 = 0 by omega, Nat.factorial_zero]
      have hfm : f k = (-1) ^ k * poch b k / poch (n : ℂ) k := by
        rw [hf, gaussHGCoeff_neg_nat, Nat.choose_self]; simp
      rw [hfm, poch_succ b k, poch_succ (n : ℂ) k, Nat.factorial_succ]
      have hpn : poch (n : ℂ) k ≠ 0 := poch_ne_zero_of_not_neg_nat hnc k
      have hnk : (n : ℂ) + k ≠ 0 := by simpa using not_neg_nat_add_nat hnc k 0
      have hkf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
      push_cast
      field_simp
      ring
    · -- both coefficients come from the series part
      have hk1 : ¬ k + 1 ≤ m := by omega
      have hk : ¬ k ≤ m := by omega
      simp only [hh, ite_eq_right_iff.mpr (fun h => absurd h hk1),
        ite_eq_right_iff.mpr (fun h => absurd h hk), hf0 k hkm, hf0 (k + 1) (by omega)]
      obtain ⟨j, rfl⟩ : ∃ j, k = m + 1 + j := ⟨k - m - 1, by omega⟩
      rw [show m + 1 + j + 1 - m - 1 = j + 1 by omega, show m + 1 + j - m - 1 = j by omega,
        poch_succ b, poch_succ (n : ℂ), Nat.factorial_succ (m + 1 + j), Nat.factorial_succ j]
      have hpn : poch (n : ℂ) (m + 1 + j) ≠ 0 := poch_ne_zero_of_not_neg_nat hnc _
      have hnk : (n : ℂ) + ((m + 1 + j : ℕ) : ℂ) ≠ 0 := by
        simpa using not_neg_nat_add_nat hnc (m + 1 + j) 0
      have hkf : ((m + 1 + j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have h2 : ((m + 1 + j + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast at hnk h2 ⊢
      field_simp
      ring
  have hpa : poch (1 - -(m : ℂ)) (n - 1) ≠ 0 := by
    refine poch_ne_zero_of_not_neg_nat (fun k hk => ?_) _
    have := congrArg re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hpb : poch (1 - b) (n - 1) ≠ 0 := poch_ne_zero_of_not_neg_nat
    (fun k hk => hb (k + 1) (by push_cast; linear_combination -hk)) _
  have hev : logarithmicSecondTerminating b m n =ᶠ[𝓝 z]
      fun v => ₂F₁ (-(m : ℂ)) b (n : ℂ) v * log v - logSing (-(m : ℂ)) b n v + H v := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show z ∈ Metric.ball (0 : ℂ) 1 by simpa using hz)]
      with v hv
    have hv' : v ∈ Metric.eball (0 : ℂ) 1 := mem_eball_one_of_norm_lt_one (by simpa using hv)
    have hsum := hH.hasSum_mul_pow hv'
    rw [← hsum.tsum_eq, ← hsum.summable.sum_add_tsum_nat_add (m + 1)]
    have hS : logSing (-(m : ℂ)) b n v = ∑ j ∈ Finset.range (n - 1),
        ((n - 1).factorial : ℂ) * (j.factorial : ℂ) /
          (((n - j - 2).factorial : ℂ) * poch (m + 1) (j + 1) * poch (1 - b) (j + 1)) *
            ((-v)⁻¹) ^ (j + 1) := by
      simp only [logSing, show (1 : ℂ) - -(m : ℂ) = m + 1 by ring]
    have hP : ∑ k ∈ Finset.range (m + 1), h k * v ^ k =
        ∑ k ∈ Finset.range (m + 1), gaussHGCoeff (-m) b n k * v ^ k *
          (digamma (1 + m - k) + digamma (b + k) - digamma (1 + k) - digamma (n + k)) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      simp only [hh, ite_eq_left_iff.mpr (fun h => absurd (Nat.lt_succ_iff.mp hk) h), hδ, hf]
      ring
    have hT : ∑' j : ℕ, h (j + (m + 1)) * v ^ (j + (m + 1)) =
        (-1 : ℂ) ^ m * (m.factorial : ℂ) * ∑' j : ℕ,
          (j.factorial : ℂ) * poch b (m + 1 + j) /
            (poch n (m + 1 + j) * ((m + 1 + j).factorial : ℂ)) * v ^ (m + 1 + j) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun j => ?_
      rw [show j + (m + 1) = m + 1 + j by omega]
      simp only [hh, ite_eq_right_iff.mpr (fun h => absurd h (by omega : ¬ m + 1 + j ≤ m)),
        show m + 1 + j - m - 1 = j by omega]
      ring
    rw [logarithmicSecondTerminating, hS, hP, hT]
    ring
  refine ⟨?_, ?_⟩
  · rw [gaussOperator_congr hev]
    exact gaussOperator_logSolution hn hpa hpb hH hrec hz hs
  · rw [solutionWronskian_congr hev]
    exact wronskian_logSolution_ne_zero hn hpa hpb hH hrec hz hs

/-- `ψ(1 + p - (k+1)) = ψ(1 + p - k) - (p - k)⁻¹` for `k < p`. -/
theorem digamma_one_add_sub_succ {p k : ℕ} (hk : k < p) :
    digamma (1 + p - ((k + 1 : ℕ) : ℂ)) = digamma (1 + p - k) - ((p : ℂ) - k)⁻¹ ∧
      ((p : ℂ) - k) * ((p : ℂ) - k)⁻¹ = 1 := by
  have hxpos : ∀ j : ℕ, ((p - k - 1 : ℕ) : ℂ) + 1 ≠ -(j : ℂ) := by
    intro j hj
    have := congrArg re hj
    simp at this
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg (p - k - 1) : (0 : ℝ) ≤ _)]
  have hmk : ((p - k - 1 : ℕ) : ℂ) + 1 = (p : ℂ) - k := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  refine ⟨?_, mul_inv_cancel₀ (by rw [← hmk]; simpa using hxpos 0)⟩
  rw [show (1 : ℂ) + p - ((k + 1 : ℕ) : ℂ) = ((p - k - 1 : ℕ) : ℂ) + 1 by rw [hmk]; push_cast; ring,
    show (1 : ℂ) + p - k = ((p - k - 1 : ℕ) : ℂ) + 1 + 1 by rw [hmk]; ring,
    digamma_apply_add_one _ hxpos, hmk]
  ring

@[dlmf 15.10.E10]
theorem logarithmic_second_both_terminating_fundamental
    (m l n : ℕ)
    (hn : 0 < n)
    (hl : l ≤ m)
    {z : ℂ}
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane) :
    gaussOperator (-m) (-l) n (logarithmicSecondBothTerminating m l n) z = 0 ∧
      solutionWronskian (₂F₁ (-m : ℂ) (-l : ℂ) (n : ℂ)) (logarithmicSecondBothTerminating m l n) z ≠ 0 := by
  have hnc := natCast_not_neg_nat hn
  have h1c : ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := fun m => by
    simpa using natCast_not_neg_nat (n := 1) one_pos m
  set f : ℕ → ℂ := gaussHGCoeff (-(m : ℂ)) (-(l : ℂ)) n with hf
  set δ : ℕ → ℂ := fun k => digamma (1 + m - k) + digamma (1 + l - k) - digamma (1 + k) -
    digamma (n + k) with hδ
  set h : ℕ → ℂ := fun k => if k ≤ l then f k * δ k else
    (-1) ^ l * (l.factorial : ℂ) * ((k - l - 1).factorial : ℂ) * poch (-(m : ℂ)) k /
      (poch n k * (k.factorial : ℂ)) with hh
  have hf0 : ∀ k, l < k → f k = 0 := fun k hk => by
    simp only [hf, gaussHGCoeff, poch_neg_nat_eq_zero hk, mul_zero, zero_div]
  have hh0 : ∀ k, m < k → h k = 0 := fun k hk => by
    simp only [hh, ite_eq_right_iff.mpr (fun h => absurd h (by omega : ¬ k ≤ l)),
      poch_neg_nat_eq_zero hk, mul_zero, zero_div]
  have hr : 1 ≤ (ofScalars ℂ h).radius :=
    one_le_radius_of_le_gaussHGCoeff 1 1 1 (C := 0) (m + 1) fun k hk => by
      rw [hh0 k (by omega)]; simp
  have hH := hasFPowerSeriesOnBall_ofScalars_sum hr
  set H := (ofScalars ℂ h).sum with hHdef
  have hrec : ∀ k : ℕ, (k + 1) * (n + k) * h (k + 1) - (k + -(m : ℂ)) * (k + -(l : ℂ)) * h k +
      2 * (k + 1) * f (k + 1) - (2 * k + -(m : ℂ) + -(l : ℂ)) * f k + (n - 1) * f (k + 1) = 0 := by
    intro k
    have hrec0 := gaussHGCoeff_recurrence (a := -(m : ℂ)) (b := -(l : ℂ)) hnc k
    rw [← hf] at hrec0
    rcases Nat.lt_trichotomy k l with hkl | rfl | hkl
    · have hk1 : k + 1 ≤ l := hkl
      simp only [hh, ite_eq_left_iff.mpr (fun h => absurd hk1 h),
        ite_eq_left_iff.mpr (fun h => absurd hkl.le h), hδ]
      have hshift : ∀ x : ℂ, (∀ j : ℕ, x ≠ -(j : ℂ)) →
          digamma (x + ((k + 1 : ℕ) : ℂ)) = digamma (x + k) + (x + k)⁻¹ := by
        intro x hx
        rw [show x + ((k + 1 : ℕ) : ℂ) = (x + k) + 1 by push_cast; ring]
        exact digamma_apply_add_one _ (not_neg_nat_add_nat hx k)
      have hne : ∀ x : ℂ, (∀ j : ℕ, x ≠ -(j : ℂ)) → (x + k) * (x + k)⁻¹ = 1 := fun x hx =>
        mul_inv_cancel₀ (by simpa using not_neg_nat_add_nat hx k 0)
      obtain ⟨hdm, hxm⟩ := digamma_one_add_sub_succ (show k < m by omega)
      obtain ⟨hdl, hxl⟩ := digamma_one_add_sub_succ hkl
      rw [hshift 1 h1c, hshift n hnc, hdm, hdl]
      linear_combination (digamma (1 + m - k) + digamma (1 + l - k) - digamma (1 + k) -
          digamma (n + k) - ((m : ℂ) - k)⁻¹ - ((l : ℂ) - k)⁻¹) * hrec0 +
        (-(l : ℂ) + k) * f k * hxm + (-(m : ℂ) + k) * f k * hxl -
        (n + k) * f (k + 1) * hne 1 h1c - (k + 1) * f (k + 1) * hne n hnc
    · simp only [hh, ite_eq_left_iff.mpr (fun h => absurd le_rfl h),
        ite_eq_right_iff.mpr (fun h => absurd h (by omega : ¬ k + 1 ≤ k)),
        hf0 (k + 1) (by omega), show k + 1 - k - 1 = 0 by omega, Nat.factorial_zero]
      have hfm : f k = (-1) ^ k * poch (-(m : ℂ)) k / poch (n : ℂ) k := by
        have : f k = gaussHGCoeff (-(k : ℂ)) (-(m : ℂ)) n k := by
          simp only [hf, gaussHGCoeff]; ring
        rw [this, gaussHGCoeff_neg_nat, Nat.choose_self]; simp
      rw [hfm, poch_succ (-(m : ℂ)) k, poch_succ (n : ℂ) k, Nat.factorial_succ]
      have hpn : poch (n : ℂ) k ≠ 0 := poch_ne_zero_of_not_neg_nat hnc k
      have hnk : (n : ℂ) + k ≠ 0 := by simpa using not_neg_nat_add_nat hnc k 0
      have hkf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
      push_cast
      field_simp
      ring
    · have hk1 : ¬ k + 1 ≤ l := by omega
      have hk : ¬ k ≤ l := by omega
      simp only [hh, ite_eq_right_iff.mpr (fun h => absurd h hk1),
        ite_eq_right_iff.mpr (fun h => absurd h hk), hf0 k hkl, hf0 (k + 1) (by omega)]
      obtain ⟨j, rfl⟩ : ∃ j, k = l + 1 + j := ⟨k - l - 1, by omega⟩
      rw [show l + 1 + j + 1 - l - 1 = j + 1 by omega, show l + 1 + j - l - 1 = j by omega,
        poch_succ (-(m : ℂ)), poch_succ (n : ℂ), Nat.factorial_succ (l + 1 + j), Nat.factorial_succ j]
      have hpn : poch (n : ℂ) (l + 1 + j) ≠ 0 := poch_ne_zero_of_not_neg_nat hnc _
      have hnk : (n : ℂ) + ((l + 1 + j : ℕ) : ℂ) ≠ 0 := by
        simpa using not_neg_nat_add_nat hnc (l + 1 + j) 0
      have hkf : ((l + 1 + j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have h2 : ((l + 1 + j + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast at hnk h2 ⊢
      field_simp
      ring
  have hpos : ∀ p : ℕ, poch (1 - -(p : ℂ)) (n - 1) ≠ 0 := by
    intro p
    refine poch_ne_zero_of_not_neg_nat (fun k hk => ?_) _
    have := congrArg re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  have hev : logarithmicSecondBothTerminating m l n =ᶠ[𝓝 z]
      fun v => ₂F₁ (-(m : ℂ)) (-(l : ℂ)) (n : ℂ) v * log v - logSing (-(m : ℂ)) (-(l : ℂ)) n v +
        H v := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show z ∈ Metric.ball (0 : ℂ) 1 by simpa using hz)]
      with v hv
    have hv' : v ∈ Metric.eball (0 : ℂ) 1 := mem_eball_one_of_norm_lt_one (by simpa using hv)
    have hsum := hH.hasSum_mul_pow hv'
    rw [← hsum.tsum_eq, ← hsum.summable.sum_add_tsum_nat_add (l + 1)]
    have hS : logSing (-(m : ℂ)) (-(l : ℂ)) n v = ∑ j ∈ Finset.range (n - 1),
        ((n - 1).factorial : ℂ) * (j.factorial : ℂ) /
          (((n - j - 2).factorial : ℂ) * poch (m + 1) (j + 1) * poch (l + 1) (j + 1)) *
            ((-v)⁻¹) ^ (j + 1) := by
      simp only [logSing, show (1 : ℂ) - -(m : ℂ) = m + 1 by ring,
        show (1 : ℂ) - -(l : ℂ) = l + 1 by ring]
    have hP : ∑ k ∈ Finset.range (l + 1), h k * v ^ k =
        ∑ k ∈ Finset.range (l + 1), gaussHGCoeff (-m) (-l) n k * v ^ k *
          (digamma (1 + m - k) + digamma (1 + l - k) - digamma (1 + k) - digamma (n + k)) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      simp only [hh, ite_eq_left_iff.mpr (fun h => absurd (Nat.lt_succ_iff.mp hk) h), hδ, hf]
      ring
    have hT : ∑' j : ℕ, h (j + (l + 1)) * v ^ (j + (l + 1)) =
        (-1 : ℂ) ^ l * (l.factorial : ℂ) * ∑ j ∈ Finset.range (m - l),
          (j.factorial : ℂ) * poch (-m) (l + 1 + j) /
            (poch n (l + 1 + j) * ((l + 1 + j).factorial : ℂ)) * v ^ (l + 1 + j) := by
      rw [tsum_eq_sum (s := Finset.range (m - l)), Finset.mul_sum]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [show j + (l + 1) = l + 1 + j by omega]
        simp only [hh, ite_eq_right_iff.mpr (fun h => absurd h (by omega : ¬ l + 1 + j ≤ l)),
          show l + 1 + j - l - 1 = j by omega]
        ring
      · intro j hj
        rw [Finset.mem_range] at hj
        rw [hh0 _ (by omega), zero_mul]
    rw [logarithmicSecondBothTerminating, hS, hP, hT]
    ring
  refine ⟨?_, ?_⟩
  · rw [gaussOperator_congr hev]
    exact gaussOperator_logSolution hn (hpos m) (hpos l) hH hrec hz hs
  · rw [solutionWronskian_congr hev]
    exact wronskian_logSolution_ne_zero hn (hpos m) (hpos l) hH hrec hz hs

end LogSolutions

/-! ### The lens `‖z‖ < 1`, `‖1 - z‖ < 1` and the connection at `z = 1` -/

/-- The overlap of the series disks at `0` and at `1`. -/
def connLens : Set ℂ := {z | ‖z‖ < 1 ∧ ‖1 - z‖ < 1}

/-- The lens is the intersection of the unit disks about `0` and `1`. -/
theorem connLens_eq : connLens = Metric.ball 0 1 ∩ Metric.ball 1 1 := by
  ext z
  simp only [connLens, Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_ball, dist_eq_norm,
    sub_zero, norm_sub_rev z 1]

/-- The lens is open. -/
theorem isOpen_connLens : IsOpen connLens := by
  rw [connLens_eq]
  exact Metric.isOpen_ball.inter Metric.isOpen_ball

/-- The lens is preconnected (it is convex). -/
theorem isPreconnected_connLens : IsPreconnected connLens := by
  rw [connLens_eq]
  exact ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected

/-- On the lens, `1 - z` lies in the slit plane. -/
theorem one_sub_mem_slitPlane_of_mem_connLens {z : ℂ} (hz : z ∈ connLens) : 1 - z ∈ slitPlane := by
  refine mem_slitPlane_iff.mpr (Or.inl ?_)
  have := (re_le_norm z).trans_lt hz.1
  simp only [sub_re, one_re]
  linarith

/-- The lens does not contain `0`. -/
theorem ne_zero_of_mem_connLens {z : ℂ} (hz : z ∈ connLens) : z ≠ 0 := by
  rintro rfl
  simp [connLens] at hz

/-- The lens does not contain `1`. -/
theorem ne_one_of_mem_connLens {z : ℂ} (hz : z ∈ connLens) : z ≠ 1 := by
  rintro rfl
  simp [connLens] at hz

/-- `₂F₁(a, b; c; ·)` is analytic on the open unit disk. -/
theorem analyticAt_ordinaryHypergeometric {a b c z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (₂F₁ a b c) z :=
  (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).analyticAt_of_mem
    (mem_eball_one_of_norm_lt_one hz)

/-- The first local solution at `1` is analytic on the disk `‖1 - z‖ < 1`. -/
theorem analyticAt_oneFirst {a b c z : ℂ} (hz : ‖1 - z‖ < 1) : AnalyticAt ℂ (oneFirst a b c) z :=
  (analyticAt_ordinaryHypergeometric hz).comp (analyticAt_const.sub analyticAt_id)

/-- The second local solution at `1` is analytic on the disk `‖1 - z‖ < 1` inside the slit-plane
  condition. -/
theorem analyticAt_oneSecond {a b c z : ℂ} (hz : ‖1 - z‖ < 1) (hs : 1 - z ∈ slitPlane) :
    AnalyticAt ℂ (oneSecond a b c) z :=
  ((analyticAt_const.sub analyticAt_id).cpow analyticAt_const hs).mul
    ((analyticAt_ordinaryHypergeometric hz).comp (analyticAt_const.sub analyticAt_id))

/-- On the lens, `₂F₁(a,b;c;z)` is a combination of the two local solutions at `z = 1`. -/
theorem exists_connection_one {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hC : ∀ k : ℕ, a + b - c + 1 ≠ -(k : ℂ)) (hS : ∀ k : ℕ, c - a - b + 1 ≠ -(k : ℂ))
    (hs0 : c - a - b ≠ 0) :
    ∃ α β : ℂ, ∀ z ∈ connLens,
      ₂F₁ a b c z = α * oneFirst a b c z + β * oneSecond a b c z := by
  set s := c - a - b with hsdef
  set H : ℂ → ℂ := ₂F₁ a b (a + b - c + 1) with hH
  set G : ℂ → ℂ := ₂F₁ (c - a) (c - b) (c - a - b + 1) with hG
  set B : ℂ → ℂ := fun w => -s * H w * G w - w * H w * deriv G w + w * deriv H w * G w with hB
  have hH0 : AnalyticAt ℂ H 0 := analyticAt_ordinaryHypergeometric (by simp)
  have hG0 : AnalyticAt ℂ G 0 := analyticAt_ordinaryHypergeometric (by simp)
  have hBc : ContinuousAt B 0 := by
    simp only [hB]
    exact (((continuousAt_const.mul hH0.continuousAt).mul hG0.continuousAt).sub
      ((continuousAt_id.mul hH0.continuousAt).mul hG0.deriv.continuousAt)).add
      ((continuousAt_id.mul hH0.deriv.continuousAt).mul hG0.continuousAt)
  have hB0 : B 0 ≠ 0 := by
    simp only [hB, hH, hG, ordinaryHypergeometric_zero]
    simpa using hs0
  have hev : ∀ᶠ w in 𝓝 (0 : ℂ), B w ≠ 0 := hBc.eventually_ne hB0
  have hreal : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have := (continuous_ofReal.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    rwa [ofReal_zero] at this
  obtain ⟨t, hBt, ht⟩ := ((hreal.eventually hev).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num))).exists
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
  set z₀ : ℂ := 1 - t with hz₀
  have h1z₀ : 1 - z₀ = t := by rw [hz₀]; ring
  have hz₀L : z₀ ∈ connLens := by
    refine ⟨?_, ?_⟩
    · rw [hz₀, ← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith [ht.2])]
      linarith [ht.1]
    · rw [h1z₀, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      linarith [ht.2]
  have htn : ‖(t : ℂ)‖ < 1 := by rw [← h1z₀]; exact hz₀L.2
  have htslit : (t : ℂ) ∈ slitPlane := by rw [← h1z₀]; exact one_sub_mem_slitPlane_of_mem_connLens hz₀L
  -- Derivatives at `z₀`.
  have hHt : AnalyticAt ℂ H t := analyticAt_ordinaryHypergeometric htn
  have hGt : AnalyticAt ℂ G t := analyticAt_ordinaryHypergeometric htn
  have hsub : HasDerivAt (fun w : ℂ => 1 - w) (-1) z₀ := by
    simpa using (hasDerivAt_id z₀).const_sub 1
  have hHt' : HasDerivAt H (deriv H (1 - z₀)) (1 - z₀) := by
    rw [h1z₀]; exact hHt.differentiableAt.hasDerivAt
  have hGt' : HasDerivAt G (deriv G (1 - z₀)) (1 - z₀) := by
    rw [h1z₀]; exact hGt.differentiableAt.hasDerivAt
  have dF1 : HasDerivAt (oneFirst a b c) (-deriv H t) z₀ := by
    show HasDerivAt (fun w => H (1 - w)) _ z₀
    exact (hHt'.comp z₀ hsub).congr_deriv (by rw [h1z₀]; ring)
  have dF2 : HasDerivAt (oneSecond a b c)
      (s * (t : ℂ) ^ (s - 1) * (-1) * G t + (t : ℂ) ^ s * (-deriv G t)) z₀ := by
    have hp := hsub.cpow_const (c := s) (by rw [h1z₀]; exact htslit)
    show HasDerivAt (fun w => (1 - w) ^ s * G (1 - w)) _ z₀
    exact (hp.mul (hGt'.comp z₀ hsub)).congr_deriv
      (by simp only [Function.comp_apply, h1z₀]; ring)
  have hf₀ : AnalyticAt ℂ (₂F₁ a b c) z₀ := analyticAt_ordinaryHypergeometric hz₀L.1
  have hF1v : oneFirst a b c z₀ = H t := by simp [oneFirst, hH, h1z₀]
  have hF2v : oneSecond a b c z₀ = (t : ℂ) ^ s * G t := by simp [oneSecond, hG, hsdef, h1z₀]
  set W : ℂ := oneFirst a b c z₀ * (s * (t : ℂ) ^ (s - 1) * (-1) * G t + (t : ℂ) ^ s *
    (-deriv G t)) - (-deriv H t) * oneSecond a b c z₀ with hW
  have hpow : (t : ℂ) ^ s = (t : ℂ) ^ (s - 1) * t := by
    conv_lhs => rw [show s = s - 1 + 1 by ring, cpow_add _ _ ht0, cpow_one]
  have hWt : (t : ℂ) * W = (t : ℂ) ^ s * B t := by
    rw [hW, hF1v, hF2v, hpow]
    simp only [hB]
    ring
  have hW0 : W ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hWt
    exact (mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl ht0)) hBt) hWt.symm
  -- The combination with vanishing value and derivative at `z₀`.
  set f₀ := ₂F₁ a b c z₀
  set f₁ := deriv (₂F₁ a b c) z₀
  set p₀ := oneFirst a b c z₀
  set p₁ := -deriv H t
  set q₀ := oneSecond a b c z₀
  set q₁ := s * (t : ℂ) ^ (s - 1) * (-1) * G t + (t : ℂ) ^ s * (-deriv G t)
  refine ⟨(f₀ * q₁ - f₁ * q₀) / W, (p₀ * f₁ - p₁ * f₀) / W, fun z hz => ?_⟩
  set α := (f₀ * q₁ - f₁ * q₀) / W
  set β := (p₀ * f₁ - p₁ * f₀) / W
  let g : ℂ → ℂ := fun w => ₂F₁ a b c w - α * oneFirst a b c w - β * oneSecond a b c w
  have hgan : AnalyticOnNhd ℂ g connLens := fun w hw =>
    ((analyticAt_ordinaryHypergeometric hw.1).sub
      (analyticAt_const.mul (analyticAt_oneFirst hw.2))).sub
      (analyticAt_const.mul (analyticAt_oneSecond hw.2
        (one_sub_mem_slitPlane_of_mem_connLens hw)))
  have hgode : ∀ w ∈ connLens, gaussOperator a b c g w = 0 := by
    intro w hw
    rw [gaussOperator_sub_smul (analyticAt_ordinaryHypergeometric hw.1)
      (analyticAt_oneFirst hw.2)
      (analyticAt_oneSecond hw.2 (one_sub_mem_slitPlane_of_mem_connLens hw))]
    have h1 : gaussOperator a b c (₂F₁ a b c) w = 0 := by
      have := ordinaryHypergeometric_ode (a := a) (b := b) hc hw.1
        (ne_zero_of_mem_connLens hw) (ne_one_of_mem_connLens hw)
      simpa [gaussOperator] using this
    rw [h1, one_first_ode hC hw.2,
      one_second_ode hS hw.2 (one_sub_mem_slitPlane_of_mem_connLens hw)]
    ring
  have hgv : g z₀ = 0 := by
    change f₀ - α * p₀ - β * q₀ = 0
    simp only [α, β]
    field_simp
    simp only [hW]
    ring
  have hgd : deriv g z₀ = 0 := by
    have h : HasDerivAt g (f₁ - α * p₁ - β * q₁) z₀ :=
      ((hf₀.differentiableAt.hasDerivAt.sub (dF1.const_mul α)).sub (dF2.const_mul β))
    rw [h.deriv]
    change f₁ - α * p₁ - β * q₁ = 0
    simp only [α, β]
    field_simp
    simp only [hW]
    ring
  have hg0 := gaussOperator_eq_zero_of_deriv_eq_zero isOpen_connLens isPreconnected_connLens
    hgan hgode hz₀L (ne_zero_of_mem_connLens hz₀L) (ne_one_of_mem_connLens hz₀L) hgv hgd z hz
  simp only [g] at hg0
  linear_combination hg0

/-- Abel's theorem for `₂F₁` at `z = 1` when `Re(c-a-b) > 0`. -/
theorem tendsto_ordinaryHypergeometric_left_one {a b c : ℂ} (h : 0 < (c - a - b).re) :
    Tendsto (fun x : ℝ => ₂F₁ a b c (x : ℂ)) (𝓝[<] 1) (𝓝 (₂F₁ a b c 1)) := by
  have hs : Summable (gaussHGCoeff a b c) := by
    simpa using ordinaryHypergeometric_summable_of_mem_sphere (z := 1) (by simp) h
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hs.hasSum.tendsto_sum_nat
  rw [tendsto_map'_iff, ← ordinaryHypergeometric_one_eq_tsum] at habel
  refine habel.congr fun x => ?_
  simp only [Function.comp_apply]
  rw [ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul]
  congr 1
  funext n
  simp [gaussHGCoeff, poch, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- `sin(πx) ≠ 0` when `x` is not an integer. -/
theorem sin_pi_mul_ne_zero_of_not_int {x : ℂ} (hx : ∀ k : ℤ, x ≠ (k : ℂ)) :
    Complex.sin (π * x) ≠ 0 := by
  rw [Ne, Complex.sin_eq_zero_iff]
  rintro ⟨k, hk⟩
  apply hx k
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have := hk
  field_simp at this
  linear_combination this

/-- The connection formula 15.10.21 in a parameter region where every limit is available. -/
theorem zero_first_connection_one_base {a b c : ℂ} (ha : ∀ k : ℤ, a ≠ (k : ℂ))
    (hb : ∀ k : ℤ, b ≠ (k : ℂ)) (hc : ∀ k : ℤ, c ≠ (k : ℂ)) (hca : ∀ k : ℤ, c - a ≠ (k : ℂ))
    (hcb : ∀ k : ℤ, c - b ≠ (k : ℂ)) (hs : ∀ k : ℤ, c - a - b ≠ (k : ℂ))
    (hre : 0 < (c - a - b).re) (hre1 : c.re < 1) {z : ℂ} (hz : z ∈ connLens) :
    ₂F₁ a b c z =
      Gamma c * Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)) * oneFirst a b c z +
        Gamma c * Gamma (a + b - c) / (Gamma a * Gamma b) * oneSecond a b c z := by
  have hc' := not_neg_nat_of_not_int hc
  have hC : ∀ k : ℕ, a + b - c + 1 ≠ -(k : ℂ) := by
    refine not_neg_nat_of_not_int fun k h => hs (1 - k) ?_
    push_cast
    linear_combination -h
  have hS : ∀ k : ℕ, c - a - b + 1 ≠ -(k : ℂ) := by
    refine not_neg_nat_of_not_int fun k h => hs (k - 1) ?_
    push_cast
    linear_combination h
  have hs0 : c - a - b ≠ 0 := by simpa using hs 0
  obtain ⟨α, β, hαβ⟩ := exists_connection_one hc' hC hS hs0
  set H : ℂ → ℂ := ₂F₁ a b (a + b - c + 1) with hH
  set G : ℂ → ℂ := ₂F₁ (c - a) (c - b) (c - a - b + 1) with hG
  have hH0 : AnalyticAt ℂ H 0 := analyticAt_ordinaryHypergeometric (by simp)
  have hG0 : AnalyticAt ℂ G 0 := analyticAt_ordinaryHypergeometric (by simp)
  have hf0 : AnalyticAt ℂ (₂F₁ a b c : ℂ → ℂ) (0 : ℂ) :=
    analyticAt_ordinaryHypergeometric (by simp)
  have hmem : ∀ x : ℝ, 0 < x → x < 1 → (x : ℂ) ∈ connLens := by
    intro x hx0 hx1
    refine ⟨?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      exact hx1
    · rw [← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
  have hid : ∀ x : ℝ, 0 < x → x < 1 → ₂F₁ a b c (x : ℂ) =
      α * H (1 - x) + β * ((1 - (x : ℂ)) ^ (c - a - b) * G (1 - x)) := by
    intro x hx0 hx1
    exact hαβ _ (hmem x hx0 hx1)
  have hsub1 : Tendsto (fun x : ℝ => (1 : ℂ) - x) (𝓝[<] 1) (𝓝 0) := by
    have := ((show Continuous (fun x : ℝ => (1 : ℂ) - (x : ℂ)) by fun_prop).tendsto (1 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    simpa using this
  have hsub0 : Tendsto (fun x : ℝ => 1 - x) (𝓝[>] 0) (𝓝[<] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := ((show Continuous (fun x : ℝ => (1 : ℝ) - x) by fun_prop).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_Iio]
      linarith [Set.mem_Ioi.mp hx]
  -- The limit `x → 1⁻`.
  have hα : α = ₂F₁ a b c 1 := by
    have hF := tendsto_ordinaryHypergeometric_left_one hre
    have hF1 : Tendsto (fun x : ℝ => H (1 - x)) (𝓝[<] 1) (𝓝 1) := by
      have := hH0.continuousAt.tendsto.comp hsub1
      simpa [hH, Function.comp_def] using this
    have hpow : Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (c - a - b)) (𝓝[<] 1) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hr : Tendsto (fun x : ℝ => (1 - x) ^ (c - a - b).re) (𝓝[<] 1) (𝓝 0) := by
        have hc0 := (Real.continuousAt_rpow_const 0 (c - a - b).re (Or.inr hre.le)).tendsto
        rw [Real.zero_rpow hre.ne'] at hc0
        refine hc0.comp ?_
        have := ((show Continuous (fun x : ℝ => (1 : ℝ) - x) by fun_prop).tendsto (1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
        simpa using this
      refine hr.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [← ofReal_one, ← ofReal_sub, norm_cpow_eq_rpow_re_of_pos (by linarith [Set.mem_Iio.mp hx])]
    have hF2 : Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (c - a - b) * G (1 - x)) (𝓝[<] 1)
        (𝓝 (0 * 1)) := by
      refine hpow.mul ?_
      have := hG0.continuousAt.tendsto.comp hsub1
      simpa [hG, Function.comp_def] using this
    have hR := (hF1.const_mul α).add (hF2.const_mul β)
    rw [mul_one, zero_mul, mul_zero, add_zero] at hR
    refine tendsto_nhds_unique (hR.congr' ?_) hF
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact (hid x hx.1 hx.2).symm
  -- The limit `x → 0⁺`.
  have hre' : 0 < ((a + b - c + 1) - a - b).re := by
    simp only [sub_re, add_re, one_re] at hre1 ⊢
    linarith
  have hre'' : 0 < ((c - a - b + 1) - (c - a) - (c - b)).re := by
    simp only [sub_re, add_re, one_re] at hre1 ⊢
    linarith
  have h0 : 1 = α * H 1 + β * G 1 := by
    have hF : Tendsto (fun x : ℝ => ₂F₁ a b c (x : ℂ)) (𝓝[>] 0) (𝓝 1) := by
      have := hf0.continuousAt.tendsto.comp ((continuous_ofReal.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ))))
      simpa [Function.comp_def] using this
    have hF1 : Tendsto (fun x : ℝ => H (1 - x)) (𝓝[>] 0) (𝓝 (H 1)) := by
      have := (tendsto_ordinaryHypergeometric_left_one hre').comp hsub0
      simpa [hH, Function.comp_def] using this
    have hF2 : Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (c - a - b) * G (1 - x)) (𝓝[>] 0)
        (𝓝 (1 * G 1)) := by
      refine Tendsto.mul ?_ ?_
      · have h1 := (continuousAt_cpow_const (b := c - a - b) one_mem_slitPlane).tendsto
        rw [one_cpow] at h1
        refine h1.comp ?_
        have := ((show Continuous (fun x : ℝ => (1 : ℂ) - (x : ℂ)) by fun_prop).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
        simpa using this
      · have := (tendsto_ordinaryHypergeometric_left_one hre'').comp hsub0
        simpa [hG, Function.comp_def] using this
    have hR := (hF1.const_mul α).add (hF2.const_mul β)
    rw [one_mul] at hR
    refine tendsto_nhds_unique hF (hR.congr' ?_)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact (hid x hx.1 hx.2).symm
  -- Gauss's sums and the reflection formula.
  have hg1 := gauss_summation (a := a) (b := b) hc' hre
  have hH1 : H 1 = Gamma (a + b - c + 1) * Gamma (1 - c) /
      (Gamma (b - c + 1) * Gamma (a - c + 1)) := by
    have := gauss_summation (a := a) (b := b) hC hre'
    rw [show a + b - c + 1 - a - b = 1 - c by ring, show a + b - c + 1 - a = b - c + 1 by ring,
      show a + b - c + 1 - b = a - c + 1 by ring] at this
    exact this
  have hG1 : G 1 = Gamma (c - a - b + 1) * Gamma (1 - c) / (Gamma (1 - b) * Gamma (1 - a)) := by
    have := gauss_summation (a := c - a) (b := c - b) hS hre''
    rw [show c - a - b + 1 - (c - a) - (c - b) = 1 - c by ring,
      show c - a - b + 1 - (c - a) = 1 - b by ring,
      show c - a - b + 1 - (c - b) = 1 - a by ring] at this
    exact this
  have refl (x y : ℂ) (hxy : 1 - x = y) : Gamma x * Gamma y = π / Complex.sin (π * x) := by
    rw [← hxy]
    exact Complex.Gamma_mul_Gamma_one_sub x
  have hnz (x : ℂ) (hx : ∀ k : ℤ, x ≠ (k : ℂ)) : Gamma x ≠ 0 :=
    Complex.Gamma_ne_zero (not_neg_nat_of_not_int hx)
  have hshift (x : ℂ) (hx : ∀ k : ℤ, x ≠ (k : ℂ)) (m : ℤ) : ∀ k : ℤ, x + m ≠ (k : ℂ) := by
    intro k h
    exact hx (k - m) (by push_cast; linear_combination h)
  have hneg (x : ℂ) (hx : ∀ k : ℤ, x ≠ (k : ℂ)) : ∀ k : ℤ, -x ≠ (k : ℂ) := by
    intro k h
    exact hx (-k) (by push_cast; linear_combination -h)
  have hab : ∀ k : ℤ, a + b - c ≠ (k : ℂ) := by
    simpa [show -(c - a - b) = a + b - c by ring] using hneg _ hs
  have hsa := sin_pi_mul_ne_zero_of_not_int ha
  have hsb := sin_pi_mul_ne_zero_of_not_int hb
  have hsc := sin_pi_mul_ne_zero_of_not_int hc
  have hsca := sin_pi_mul_ne_zero_of_not_int hca
  have hscb := sin_pi_mul_ne_zero_of_not_int hcb
  have hss := sin_pi_mul_ne_zero_of_not_int hs
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have r1 := refl c (1 - c) rfl
  have r2 := refl (c - a - b) (a + b - c + 1) (by ring)
  have r3 := refl (c - a) (a - c + 1) (by ring)
  have r4 := refl (c - b) (b - c + 1) (by ring)
  have r5 := refl (a + b - c) (c - a - b + 1) (by ring)
  have r6 := refl a (1 - a) rfl
  have r7 := refl b (1 - b) rfl
  have hsin5 : Complex.sin (π * (a + b - c)) = -Complex.sin (π * (c - a - b)) := by
    rw [← Complex.sin_neg]
    ring_nf
  set β₀ := Gamma c * Gamma (a + b - c) / (Gamma a * Gamma b) with hβ₀
  have hG1ne : G 1 ≠ 0 := by
    rw [hG1]
    have h1 : ∀ k : ℤ, c - a - b + 1 ≠ (k : ℂ) := by simpa using hshift _ hs 1
    have h2 : ∀ k : ℤ, 1 - c ≠ (k : ℂ) := by
      simpa [show -c + 1 = 1 - c by ring] using hshift _ (hneg _ hc) 1
    have h3 : ∀ k : ℤ, 1 - b ≠ (k : ℂ) := by
      simpa [show -b + 1 = 1 - b by ring] using hshift _ (hneg _ hb) 1
    have h4 : ∀ k : ℤ, 1 - a ≠ (k : ℂ) := by
      simpa [show -a + 1 = 1 - a by ring] using hshift _ (hneg _ ha) 1
    exact div_ne_zero (mul_ne_zero (hnz _ h1) (hnz _ h2)) (mul_ne_zero (hnz _ h3) (hnz _ h4))
  have k1 : α * H 1 = (π / Complex.sin (π * c)) * (π / Complex.sin (π * (c - a - b))) /
      ((π / Complex.sin (π * (c - a))) * (π / Complex.sin (π * (c - b)))) := by
    rw [hα, hg1, hH1, ← r1, ← r2, ← r3, ← r4]
    ring
  have k2 : β₀ * G 1 = (π / Complex.sin (π * c)) * (π / Complex.sin (π * (a + b - c))) /
      ((π / Complex.sin (π * a)) * (π / Complex.sin (π * b))) := by
    rw [hβ₀, hG1, ← r1, ← r5, ← r6, ← r7]
    ring
  have htrig : 1 = α * H 1 + β₀ * G 1 := by
    rw [k1, k2, hsin5]
    field_simp
    simp only [mul_sub, Complex.sin_sub, Complex.cos_sub]
    linear_combination (-(Complex.sin (π * a) * Complex.sin (π * b))) *
      Complex.sin_sq_add_cos_sq (π * c)
  have hβ : β = β₀ := by
    have : (β - β₀) * G 1 = 0 := by linear_combination htrig - h0
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hG1ne)
  rw [hαβ z hz, hα, hg1, hβ]

/-- Left side of the regularized form of 15.10.21, entire in each parameter. -/
def connLhs (a b c z : ℂ) : ℂ :=
  Complex.sin (π * (c - a - b)) * regularizedGaussHGFun a b c z

/-- Right side of the regularized form of 15.10.21, entire in each parameter. -/
def connRhs (a b c z : ℂ) : ℂ :=
  π * (regularizedGaussHGFun a b (a + b - c + 1) (1 - z) * (Gamma (c - a))⁻¹ * (Gamma (c - b))⁻¹ -
    (1 - z) ^ (c - a - b) * regularizedGaussHGFun (c - a) (c - b) (c - a - b + 1) (1 - z) *
      (Gamma a)⁻¹ * (Gamma b)⁻¹)

/-- For parameters depending holomorphically on `w`, both sides of the connection formula are entire
  in `w` at each point of the lens. -/
theorem differentiable_connLhs_connRhs {A B C : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (hC : Differentiable ℂ C) {z : ℂ} (hz : z ∈ connLens) :
    Differentiable ℂ (fun w => connLhs (A w) (B w) (C w) z) ∧
      Differentiable ℂ (fun w => connRhs (A w) (B w) (C w) z) := by
  have hz1 : ‖1 - z‖ < 1 := hz.2
  have hz0 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_one_of_mem_connLens hz))
  have hR (A' B' C' : ℂ → ℂ) (hA' : Differentiable ℂ A') (hB' : Differentiable ℂ B')
      (hC' : Differentiable ℂ C') {x : ℂ} (hx : ‖x‖ < 1) :
      Differentiable ℂ (fun w => regularizedGaussHGFun (A' w) (B' w) (C' w) x) := fun w =>
    (analyticOnNhd_regularizedGaussHGFun_comp hA' hB' hC' hx w trivial).differentiableAt
  have hiG (U : ℂ → ℂ) (hU : Differentiable ℂ U) : Differentiable ℂ (fun w => (Gamma (U w))⁻¹) :=
    differentiable_one_div_Gamma.comp hU
  have hs : Differentiable ℂ (fun w => C w - A w - B w) := (hC.sub hA).sub hB
  refine ⟨?_, ?_⟩
  · exact (differentiable_sin.comp ((differentiable_const _).mul hs)).mul
      (hR A B C hA hB hC hz.1)
  · have h1 := hR A B (fun w => A w + B w - C w + 1) hA hB (((hA.add hB).sub hC).add_const 1) hz1
    have h2 := hR (fun w => C w - A w) (fun w => C w - B w) (fun w => C w - A w - B w + 1)
      (hC.sub hA) (hC.sub hB) (hs.add_const 1) hz1
    have hp : Differentiable ℂ (fun w => (1 - z) ^ (C w - A w - B w)) := fun w =>
      (hs w).const_cpow (Or.inl hz0)
    exact (differentiable_const _).mul
      (((h1.mul (hiG _ (hC.sub hA))).mul (hiG _ (hC.sub hB))).sub
        (((hp.mul h2).mul (hiG _ hA)).mul (hiG _ hB)))

/-- The regularized form of 15.10.21 in the base parameter region. -/
theorem connLhs_eq_connRhs_base {a b c : ℂ} (ha : ∀ k : ℤ, a ≠ (k : ℂ))
    (hb : ∀ k : ℤ, b ≠ (k : ℂ)) (hc : ∀ k : ℤ, c ≠ (k : ℂ)) (hca : ∀ k : ℤ, c - a ≠ (k : ℂ))
    (hcb : ∀ k : ℤ, c - b ≠ (k : ℂ)) (hs : ∀ k : ℤ, c - a - b ≠ (k : ℂ))
    (hre : 0 < (c - a - b).re) (hre1 : c.re < 1) {z : ℂ} (hz : z ∈ connLens) :
    connLhs a b c z = connRhs a b c z := by
  have h := zero_first_connection_one_base ha hb hc hca hcb hs hre hre1 hz
  have hc' := not_neg_nat_of_not_int hc
  have hC : ∀ k : ℕ, a + b - c + 1 ≠ -(k : ℂ) := by
    refine not_neg_nat_of_not_int fun k h => hs (1 - k) ?_
    push_cast
    linear_combination -h
  have hS : ∀ k : ℕ, c - a - b + 1 ≠ -(k : ℂ) := by
    refine not_neg_nat_of_not_int fun k h => hs (k - 1) ?_
    push_cast
    linear_combination h
  have hΓc := Complex.Gamma_ne_zero hc'
  have hΓC := Complex.Gamma_ne_zero hC
  have hΓS := Complex.Gamma_ne_zero hS
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hss := sin_pi_mul_ne_zero_of_not_int hs
  have e1 : Gamma (c - a - b) * Gamma (a + b - c + 1) = π / Complex.sin (π * (c - a - b)) := by
    rw [show a + b - c + 1 = 1 - (c - a - b) by ring]
    exact Complex.Gamma_mul_Gamma_one_sub _
  have e2 : Gamma (a + b - c) * Gamma (c - a - b + 1) = -(π / Complex.sin (π * (c - a - b))) := by
    rw [show c - a - b + 1 = 1 - (a + b - c) by ring, Complex.Gamma_mul_Gamma_one_sub,
      show (π : ℂ) * (a + b - c) = -(π * (c - a - b)) by ring, Complex.sin_neg, div_neg]
  have hG1 : Gamma (c - a - b) = π / Complex.sin (π * (c - a - b)) / Gamma (a + b - c + 1) := by
    rw [eq_div_iff hΓC, e1]
  have hG2 : Gamma (a + b - c) =
      -(π / Complex.sin (π * (c - a - b))) / Gamma (c - a - b + 1) := by
    rw [eq_div_iff hΓS, e2]
  rw [hG1, hG2] at h
  simp only [oneFirst, oneSecond] at h
  simp only [connLhs, connRhs, regularizedGaussHGFun_eq_div_Gamma hc',
    regularizedGaussHGFun_eq_div_Gamma hC, regularizedGaussHGFun_eq_div_Gamma hS]
  rw [h]
  field_simp
  ring

/-- A complex number with positive imaginary part is not an integer. -/
theorem not_int_of_im_pos {x : ℂ} (h : 0 < x.im) : ∀ k : ℤ, x ≠ (k : ℂ) := by
  intro k hk
  rw [hk] at h
  simp at h

/-- The regularized form of 15.10.21 for all parameters, by analytic continuation in `c`,
then `a`, then `b`. -/
theorem connLhs_eq_connRhs (a b c : ℂ) {z : ℂ} (hz : z ∈ connLens) :
    connLhs a b c z = connRhs a b c z := by
  have hVo : IsOpen ({w : ℂ | w.re < 0} ∩ {w : ℂ | 0 < w.im}) :=
    (isOpen_lt continuous_re continuous_const).inter (isOpen_lt continuous_const continuous_im)
  have hVne : ({w : ℂ | w.re < 0} ∩ {w : ℂ | 0 < w.im}).Nonempty :=
    ⟨⟨-1, 1⟩, by simp, by simp⟩
  have st1 : ∀ a b : ℂ, a.re < 0 → b.re < 0 → 0 < a.im → 0 < b.im →
      ∀ c, connLhs a b c z = connRhs a b c z := by
    intro a b ha hb ha' hb'
    have hd := differentiable_connLhs_connRhs (A := fun _ => a) (B := fun _ => b)
      (C := fun w => w) (differentiable_const _) (differentiable_const _) differentiable_id hz
    set V : Set ℂ := {w : ℂ | (a + b).re < w.re} ∩ {w : ℂ | w.re < 1} ∩
      {w : ℂ | a.im + b.im < w.im} with hV
    have hVo' : IsOpen V := ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_re continuous_const)).inter (isOpen_lt continuous_const continuous_im)
    have hVne' : V.Nonempty := by
      refine ⟨⟨(a + b).re / 2, a.im + b.im + 1⟩, ⟨?_, ?_⟩, ?_⟩ <;>
        simp only [Set.mem_ofPred_eq, add_re] at * <;> linarith
    have hEq : Set.EqOn (fun w => connLhs a b w z) (fun w => connRhs a b w z) V := by
      intro w hw
      obtain ⟨⟨h1, h2⟩, h3⟩ := hw
      simp only [Set.mem_ofPred_eq, add_re] at h1 h2 h3
      exact connLhs_eq_connRhs_base (not_int_of_im_pos ha') (not_int_of_im_pos hb')
        (not_int_of_im_pos (by linarith)) (not_int_of_im_pos (by simp; linarith))
        (not_int_of_im_pos (by simp; linarith)) (not_int_of_im_pos (by simp; linarith))
        (by simp; linarith) h2 hz
    have := eq_of_analyticOnNhd_univ_of_eqOn (fun w _ => hd.1.analyticAt w)
      (fun w _ => hd.2.analyticAt w) hVo' hVne' hEq
    exact fun c => congrFun this c
  have st2 : ∀ b : ℂ, b.re < 0 → 0 < b.im → ∀ a c, connLhs a b c z = connRhs a b c z := by
    intro b hb hb' a c
    have hd := differentiable_connLhs_connRhs (A := fun w => w) (B := fun _ => b)
      (C := fun _ => c) differentiable_id (differentiable_const _) (differentiable_const _) hz
    have := eq_of_analyticOnNhd_univ_of_eqOn (fun w _ => hd.1.analyticAt w)
      (fun w _ => hd.2.analyticAt w) hVo hVne (fun w hw => st1 w b hw.1 hb hw.2 hb' c)
    exact congrFun this a
  have hd := differentiable_connLhs_connRhs (A := fun _ => a) (B := fun w => w)
    (C := fun _ => c) (differentiable_const _) differentiable_id (differentiable_const _) hz
  have := eq_of_analyticOnNhd_univ_of_eqOn (fun w _ => hd.1.analyticAt w)
    (fun w _ => hd.2.analyticAt w) hVo hVne (fun w hw => st2 w hw.1 hw.2 a c)
  exact congrFun this b

/-- 15.10.21 with `c` only required to avoid the nonpositive integers. -/
theorem zero_first_connection_one_of_not_neg_nat {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hz : ‖z‖ < 1) (hw : ‖1 - z‖ < 1) :
    ₂F₁ a b c z =
      Gamma c * Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)) * oneFirst a b c z + Gamma c * Gamma (a
        + b - c) / (Gamma a * Gamma b) * oneSecond a b c z := by
  have hP := connLhs_eq_connRhs a b c (z := z) ⟨hz, hw⟩
  have hc' := hc
  have hC : ∀ k : ℕ, a + b - c + 1 ≠ -(k : ℂ) := by
    refine not_neg_nat_of_not_int fun k h => he (1 - k) ?_
    push_cast
    linear_combination -h
  have hS : ∀ k : ℕ, c - a - b + 1 ≠ -(k : ℂ) := by
    refine not_neg_nat_of_not_int fun k h => he (k - 1) ?_
    push_cast
    linear_combination h
  have hΓc := Complex.Gamma_ne_zero hc'
  have hΓC := Complex.Gamma_ne_zero hC
  have hΓS := Complex.Gamma_ne_zero hS
  have hss := sin_pi_mul_ne_zero_of_not_int he
  have e1 : Gamma (c - a - b) * Gamma (a + b - c + 1) = π / Complex.sin (π * (c - a - b)) := by
    rw [show a + b - c + 1 = 1 - (c - a - b) by ring]
    exact Complex.Gamma_mul_Gamma_one_sub _
  have e2 : Gamma (a + b - c) * Gamma (c - a - b + 1) = -(π / Complex.sin (π * (c - a - b))) := by
    rw [show c - a - b + 1 = 1 - (a + b - c) by ring, Complex.Gamma_mul_Gamma_one_sub,
      show (π : ℂ) * (a + b - c) = -(π * (c - a - b)) by ring, Complex.sin_neg, div_neg]
  have hG1 : Gamma (c - a - b) = π / Complex.sin (π * (c - a - b)) / Gamma (a + b - c + 1) := by
    rw [eq_div_iff hΓC, e1]
  have hG2 : Gamma (a + b - c) =
      -(π / Complex.sin (π * (c - a - b))) / Gamma (c - a - b + 1) := by
    rw [eq_div_iff hΓS, e2]
  simp only [connLhs, connRhs, regularizedGaussHGFun_eq_div_Gamma hc',
    regularizedGaussHGFun_eq_div_Gamma hC, regularizedGaussHGFun_eq_div_Gamma hS] at hP
  have hF : ₂F₁ a b c z = Gamma c * (π * (₂F₁ a b (a + b - c + 1) (1 - z) /
      Gamma (a + b - c + 1) * (Gamma (c - a))⁻¹ * (Gamma (c - b))⁻¹ -
      (1 - z) ^ (c - a - b) * (₂F₁ (c - a) (c - b) (c - a - b + 1) (1 - z) /
        Gamma (c - a - b + 1)) * (Gamma a)⁻¹ * (Gamma b)⁻¹)) /
      Complex.sin (π * (c - a - b)) := by
    rw [eq_div_iff hss, ← hP]
    field_simp
  rw [hF, hG1, hG2, oneFirst, oneSecond]
  ring

@[dlmf 15.10.E21]
theorem zero_first_connection_one {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hz : ‖z‖ < 1) (hw : ‖1 - z‖ < 1) :
    ₂F₁ a b c z =
      Gamma c * Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)) * oneFirst a b c z + Gamma c * Gamma (a
        + b - c) / (Gamma a * Gamma b) * oneSecond a b c z := by
  exact zero_first_connection_one_of_not_neg_nat (not_neg_nat_of_not_int hc) he hz hw

@[dlmf 15.10.E22]
theorem zero_second_connection_one {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hz : ‖z‖ < 1) (hw : ‖1 - z‖ < 1) :
    zeroSecond a b c z =
      Gamma (2 - c) * Gamma (c - a - b) / (Gamma (1 - a) * Gamma (1 - b)) * oneFirst a b c z + Gamma (2 - c)
        * Gamma (a + b - c) / (Gamma (a - c + 1) * Gamma (b - c + 1)) * oneSecond a b c z := by
  have hz0 : z ≠ 0 := ne_zero_of_mem_connLens ⟨hz, hw⟩
  have hc' : ∀ k : ℤ, 2 - c ≠ (k : ℂ) := fun k h => hc (2 - k) (by
    push_cast; linear_combination -h)
  have he' : ∀ k : ℤ, 2 - c - (a - c + 1) - (b - c + 1) ≠ (k : ℂ) := fun k h => he k (by
    linear_combination h)
  have hC : ∀ k : ℕ, a + b - c + 1 ≠ -(k : ℂ) := by
    refine not_neg_nat_of_not_int fun k h => he (1 - k) ?_
    push_cast
    linear_combination -h
  have hS : ∀ k : ℕ, c - a - b + 1 ≠ -(k : ℂ) := by
    refine not_neg_nat_of_not_int fun k h => he (k - 1) ?_
    push_cast
    linear_combination h
  have key := zero_first_connection_one (a := a - c + 1) (b := b - c + 1) hc' he' hz hw
  rw [show 2 - c - (a - c + 1) - (b - c + 1) = c - a - b by ring,
    show 2 - c - (a - c + 1) = 1 - a by ring, show 2 - c - (b - c + 1) = 1 - b by ring,
    show a - c + 1 + (b - c + 1) - (2 - c) = a + b - c by ring] at key
  have hcancel (X : ℂ) : z ^ (1 - c) * (z ^ (c - 1) * X) = X := by
    rw [← mul_assoc, ← cpow_add _ _ hz0, show 1 - c + (c - 1) = 0 by ring, cpow_zero, one_mul]
  have h1 : z ^ (1 - c) * oneFirst (a - c + 1) (b - c + 1) (2 - c) z = oneFirst a b c z := by
    rw [oneFirst, oneFirst, show a - c + 1 + (b - c + 1) - (2 - c) + 1 = a + b - c + 1 by ring,
      euler_transformation_of_ne_neg_nat hC hw, sub_sub_cancel,
      show a + b - c + 1 - (a - c + 1) - (b - c + 1) = c - 1 by ring,
      show a + b - c + 1 - (a - c + 1) = b by ring, show a + b - c + 1 - (b - c + 1) = a by ring,
      ordinaryHypergeometric_symm b a, hcancel]
  have h2 : z ^ (1 - c) * oneSecond (a - c + 1) (b - c + 1) (2 - c) z = oneSecond a b c z := by
    rw [oneSecond, oneSecond, show 2 - c - (a - c + 1) - (b - c + 1) = c - a - b by ring,
      show 2 - c - (a - c + 1) = 1 - a by ring, show 2 - c - (b - c + 1) = 1 - b by ring,
      euler_transformation_of_ne_neg_nat hS hw, sub_sub_cancel,
      show c - a - b + 1 - (1 - a) - (1 - b) = c - 1 by ring,
      show c - a - b + 1 - (1 - a) = c - b by ring, show c - a - b + 1 - (1 - b) = c - a by ring,
      ordinaryHypergeometric_symm (c - b) (c - a), mul_left_comm, hcancel]
  rw [zeroSecond, key, ← h1, ← h2]
  ring

@[dlmf 15.10.E17]
theorem one_first_connection_zero {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hz : ‖z‖ < 1) (hw : ‖1 - z‖ < 1) :
    oneFirst a b c z =
      Gamma (1 - c) * Gamma (a + b - c + 1) / (Gamma (a - c + 1) * Gamma (b - c + 1)) * ₂F₁ a b c z + Gamma
        (c - 1) * Gamma (a + b - c + 1) / (Gamma a * Gamma b) * zeroSecond a b c z := by
  have hc' : ∀ k : ℤ, a + b - c + 1 ≠ (k : ℂ) := fun k h => he (1 - k) (by
    push_cast; linear_combination -h)
  have he' : ∀ k : ℤ, a + b - c + 1 - a - b ≠ (k : ℂ) := fun k h => hc (1 - k) (by
    push_cast; linear_combination -h)
  have key := zero_first_connection_one (a := a) (b := b) hc' he' hw (by simpa using hz)
  rw [show a + b - c + 1 - a - b = 1 - c by ring, show a + b - c + 1 - a = b - c + 1 by ring,
    show a + b - c + 1 - b = a - c + 1 by ring, show a + b - (a + b - c + 1) = c - 1 by ring]
    at key
  have h1 : oneFirst a b (a + b - c + 1) (1 - z) = ₂F₁ a b c z := by
    rw [oneFirst, show a + b - (a + b - c + 1) + 1 = c by ring, sub_sub_cancel]
  have h2 : oneSecond a b (a + b - c + 1) (1 - z) = zeroSecond a b c z := by
    rw [oneSecond, zeroSecond, sub_sub_cancel, show a + b - c + 1 - a - b = 1 - c by ring,
      show a + b - c + 1 - a = b - c + 1 by ring, show a + b - c + 1 - b = a - c + 1 by ring,
      show 1 - c + 1 = 2 - c by ring, ordinaryHypergeometric_symm]
  rw [oneFirst, key, h1, h2]
  ring

@[dlmf 15.10.E18]
theorem one_second_connection_zero {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hz : ‖z‖ < 1) (hw : ‖1 - z‖ < 1) :
    oneSecond a b c z =
      Gamma (1 - c) * Gamma (c - a - b + 1) / (Gamma (1 - a) * Gamma (1 - b)) * ₂F₁ a b c z + Gamma (c - 1)
        * Gamma (c - a - b + 1) / (Gamma (c - a) * Gamma (c - b)) * zeroSecond a b c z := by
  have hc' : ∀ k : ℤ, a + b - c + 1 ≠ (k : ℂ) := fun k h => he (1 - k) (by
    push_cast; linear_combination -h)
  have he' : ∀ k : ℤ, a + b - c + 1 - a - b ≠ (k : ℂ) := fun k h => hc (1 - k) (by
    push_cast; linear_combination -h)
  have key := zero_second_connection_one (a := a) (b := b) hc' he' hw (by simpa using hz)
  rw [show a + b - c + 1 - a - b = 1 - c by ring, show 2 - (a + b - c + 1) = c - a - b + 1 by ring,
    show a + b - (a + b - c + 1) = c - 1 by ring, show a - (a + b - c + 1) + 1 = c - b by ring,
    show b - (a + b - c + 1) + 1 = c - a by ring] at key
  have h1 : oneFirst a b (a + b - c + 1) (1 - z) = ₂F₁ a b c z := by
    rw [oneFirst, show a + b - (a + b - c + 1) + 1 = c by ring, sub_sub_cancel]
  have h2 : oneSecond a b (a + b - c + 1) (1 - z) = zeroSecond a b c z := by
    rw [oneSecond, zeroSecond, sub_sub_cancel, show a + b - c + 1 - a - b = 1 - c by ring,
      show a + b - c + 1 - a = b - c + 1 by ring, show a + b - c + 1 - b = a - c + 1 by ring,
      show 1 - c + 1 = 2 - c by ring, ordinaryHypergeometric_symm]
  have h3 : zeroSecond a b (a + b - c + 1) (1 - z) = oneSecond a b c z := by
    rw [zeroSecond, oneSecond, show 1 - (a + b - c + 1) = c - a - b by ring,
      show a - (a + b - c + 1) + 1 = c - b by ring, show b - (a + b - c + 1) + 1 = c - a by ring,
      show 2 - (a + b - c + 1) = c - a - b + 1 by ring, ordinaryHypergeometric_symm]
  rw [← h3, key, h1, h2]
  ring


end DLMF.Hypergeometric
