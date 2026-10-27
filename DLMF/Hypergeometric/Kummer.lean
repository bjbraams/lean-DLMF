/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Solutions

/-!
# Kummer's representations and connections (DLMF §15.10(ii))

E11 is already the Euler/Pfaff family in `Transformations` and
`FurtherTransformations`. E12–E16 give the remaining representations, on
overlaps of series disks. Explicit upper-half-plane hypotheses fix the phases
in E15–E16 and in connections involving infinity. Separate charts avoid
assigning analytic-continuation values to divergent Mathlib series.
E17–E18/E21–E22 are in `Solutions`. E19–E20/E25–E26 use the left chart;
E23–E24/E27–E28 use the chart at infinity. E29–E36 mix all three centers;
their series charts have no common open domain and need global continuation.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace DLMF.Hypergeometric

/-- Kummer's fifth solution on the local chart at infinity. -/
@[dlmf 15.10.E15]
def kummerFive (a b c z : ℂ) : ℂ := exp (a * Real.pi * I) * infinityFirst a b c z

/-- Kummer's sixth solution on the local chart at infinity. -/
@[dlmf 15.10.E16]
def kummerSix (a b c z : ℂ) : ℂ := exp (b * Real.pi * I) * infinityFirst b a c z

/-- A second chart for Kummer's fifth solution, overlapping the disk at zero. -/
@[dlmf 15.10.E15]
def kummerFiveLeft (a b c z : ℂ) : ℂ :=
  (1 - z) ^ (-a) * ₂F₁ a (c - b) (a - b + 1) (1 / (1 - z))

/-- A second chart for Kummer's sixth solution. -/
@[dlmf 15.10.E16]
def kummerSixLeft (a b c z : ℂ) : ℂ :=
  (1 - z) ^ (-b) * ₂F₁ b (c - a) (b - a + 1) (1 / (1 - z))

/-! ### Phase identities for principal powers -/

/-- A principal power computed from any logarithm in the principal strip. -/
theorem cpow_eq_exp_of_exp_eq {x L : ℂ} (hx : exp L = x) (h1 : -Real.pi < L.im)
    (h2 : L.im ≤ Real.pi) (y : ℂ) : x ^ y = exp (L * y) := by
  have hx0 : x ≠ 0 := by rw [← hx]; exact exp_ne_zero L
  rw [cpow_def_of_ne_zero hx0, ← hx, log_exp h1 h2]

theorem cpow_eq_exp_log {x : ℂ} (hx : x ≠ 0) (y : ℂ) : x ^ y = exp (log x * y) :=
  cpow_def_of_ne_zero hx y

/-- `z/(z-1) = exp(log z - log(1-z) + φ)` with `φ = -πi` in the upper and `φ = πi` in the
lower half-plane. -/
theorem exp_log_div_sub_one {z φ : ℂ} (hz0 : z ≠ 0) (hz1 : 1 - z ≠ 0)
    (hφ : exp φ = -1) : exp (log z - log (1 - z) + φ) = z / (z - 1) := by
  rw [exp_add, exp_sub, exp_log hz0, exp_log hz1, hφ]
  have : z - 1 = -(1 - z) := by ring
  rw [this]
  field_simp

theorem exp_neg_pi_mul_I : exp (-(Real.pi * I)) = -1 := by
  rw [exp_neg, exp_pi_mul_I]
  norm_num

theorem im_log_div_sub_one_upper {z : ℂ} (hi : 0 < z.im) :
    -Real.pi < (log z - log (1 - z) + -(Real.pi * I)).im ∧
      (log z - log (1 - z) + -(Real.pi * I)).im ≤ Real.pi := by
  have h1 : 0 ≤ z.arg := arg_nonneg_iff.mpr hi.le
  have h2 : (1 - z).arg < 0 := arg_neg_iff.mpr (by simp; linarith)
  have h3 := arg_le_pi z
  have h4 := neg_pi_lt_arg (1 - z)
  simp only [add_im, sub_im, log_im, neg_im, mul_im, ofReal_re, I_im, ofReal_im, I_re,
    mul_zero, mul_one, add_zero]
  constructor <;> linarith

theorem im_log_div_sub_one_lower {z : ℂ} (hi : z.im < 0) :
    -Real.pi < (log z - log (1 - z) + Real.pi * I).im ∧
      (log z - log (1 - z) + Real.pi * I).im ≤ Real.pi := by
  have h1 : z.arg < 0 := arg_neg_iff.mpr hi
  have h2 : 0 ≤ (1 - z).arg := arg_nonneg_iff.mpr (by simp; linarith)
  have h3 := neg_pi_lt_arg z
  have h4 := arg_le_pi (1 - z)
  simp only [add_im, sub_im, log_im, mul_im, ofReal_re, I_im, ofReal_im, I_re,
    mul_zero, mul_one, add_zero]
  constructor <;> linarith

/-- `(z/(z-1))^y` in the upper half-plane. -/
theorem div_sub_one_cpow_upper {z : ℂ} (hi : 0 < z.im) (y : ℂ) :
    (z / (z - 1)) ^ y = exp ((log z - log (1 - z) + -(Real.pi * I)) * y) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hi
  have hz1 : 1 - z ≠ 0 := by intro h; have := congrArg im h; simp at this; linarith
  exact cpow_eq_exp_of_exp_eq (exp_log_div_sub_one hz0 hz1 exp_neg_pi_mul_I)
    (im_log_div_sub_one_upper hi).1 (im_log_div_sub_one_upper hi).2 y

/-- `(z/(z-1))^y` in the lower half-plane. -/
theorem div_sub_one_cpow_lower {z : ℂ} (hi : z.im < 0) (y : ℂ) :
    (z / (z - 1)) ^ y = exp ((log z - log (1 - z) + Real.pi * I) * y) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hi
  have hz1 : 1 - z ≠ 0 := by intro h; have := congrArg im h; simp at this; linarith
  exact cpow_eq_exp_of_exp_eq (exp_log_div_sub_one hz0 hz1 exp_pi_mul_I)
    (im_log_div_sub_one_lower hi).1 (im_log_div_sub_one_lower hi).2 y

/-- `(1 - 1/z)^y` in the upper half-plane. -/
theorem one_sub_recip_cpow_upper {z : ℂ} (hi : 0 < z.im) (y : ℂ) :
    (1 - 1 / z) ^ y = exp ((log (1 - z) - log z + Real.pi * I) * y) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hi
  have hz1 : 1 - z ≠ 0 := by intro h; have := congrArg im h; simp at this; linarith
  refine cpow_eq_exp_of_exp_eq ?_ ?_ ?_ y
  · rw [exp_add, exp_sub, exp_log hz0, exp_log hz1, exp_pi_mul_I]
    field_simp
    ring
  · have h1 := arg_le_pi z
    have h2 := neg_pi_lt_arg (1 - z)
    simp only [add_im, sub_im, log_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero,
      mul_one, add_zero]
    linarith
  · have h1 : 0 ≤ z.arg := arg_nonneg_iff.mpr hi.le
    have h2 : (1 - z).arg < 0 := arg_neg_iff.mpr (by simp; linarith)
    simp only [add_im, sub_im, log_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero,
      mul_one, add_zero]
    linarith

/-- `(1/w)^y = w^(-y)` away from the negative real axis. -/
theorem one_div_cpow_of_mem_slitPlane {w : ℂ} (hw : w ∈ slitPlane) (y : ℂ) :
    (1 / w) ^ y = exp (-log w * y) := by
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  refine cpow_eq_exp_of_exp_eq ?_ ?_ ?_ y
  · rw [exp_neg, exp_log hw0, one_div]
  · have := arg_lt_pi_iff.mpr (by
      rcases mem_slitPlane_iff.mp hw with h | h
      · exact Or.inl h.le
      · exact Or.inr h)
    simp only [neg_im, log_im]
    linarith
  · have := neg_pi_lt_arg w
    simp only [neg_im, log_im]
    linarith

theorem one_sub_mem_slitPlane_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ∈ slitPlane := by
  refine mem_slitPlane_iff.mpr (Or.inl ?_)
  have := (re_le_norm z).trans_lt hz
  simp only [sub_re, one_re]
  linarith

/-! ### Connections between zero and the charts at infinity -/

/-- 15.10.25 without the phase hypotheses (none is needed). -/
theorem zero_first_connection_left_gen {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (hab : ∀ k : ℤ, a - b ≠ (k : ℂ)) (hz : ‖z‖ < 1) (hw : 1 < ‖1 - z‖) :
    ₂F₁ a b c z =
      Gamma c * Gamma (b - a) / (Gamma b * Gamma (c - a)) * kummerFiveLeft a b c z + Gamma c *
        Gamma (a - b) / (Gamma a * Gamma (c - b)) * kummerSixLeft a b c z := by
  have h1z : 1 - z ≠ 0 := by intro h; rw [h] at hw; norm_num at hw
  have hz1 : z - 1 ≠ 0 := by intro h; apply h1z; linear_combination -h
  have hn : ‖z - 1‖ = ‖1 - z‖ := norm_sub_rev z 1
  have hu : ‖z / (z - 1)‖ < 1 := by
    rw [norm_div, hn, div_lt_one (by linarith)]
    linarith
  have h1u : 1 - z / (z - 1) = 1 / (1 - z) := by
    field_simp
    ring
  have hu1 : ‖1 - z / (z - 1)‖ < 1 := by
    rw [h1u, norm_div, norm_one, div_lt_one (by linarith)]
    exact hw
  have hslit := one_sub_mem_slitPlane_of_norm_lt_one hz
  have he' : ∀ k : ℤ, c - a - (c - b) ≠ (k : ℂ) := fun k h => hab (-k) (by
    push_cast; linear_combination -h)
  have key := zero_first_connection_one (a := a) (b := c - b) hc he' hu hu1
  rw [show c - a - (c - b) = b - a by ring, show c - (c - b) = b by ring,
    show a + (c - b) - c = a - b by ring] at key
  rw [pfaff_transformation_of_ne_neg_nat (not_neg_nat_of_not_int hc) hz hu, key]
  simp only [oneFirst, oneSecond, kummerFiveLeft, kummerSixLeft]
  rw [show a + (c - b) - c + 1 = a - b + 1 by ring, h1u, show c - a - (c - b) = b - a by ring,
    show c - (c - b) = b by ring, show b - a + 1 = b - a + 1 by ring,
    ordinaryHypergeometric_symm (c - a) b, one_div_cpow_of_mem_slitPlane hslit,
    cpow_eq_exp_log h1z (-a), cpow_eq_exp_log h1z (-b)]
  have hexp : exp (log (1 - z) * -a) * (exp (-log (1 - z) * (b - a))) =
      exp (log (1 - z) * -b) := by
    rw [← exp_add]
    ring_nf
  linear_combination (Gamma c * Gamma (a - b) / (Gamma a * Gamma (c - b)) *
    ₂F₁ b (c - a) (b - a + 1) (1 / (1 - z))) * hexp

/-- 15.10.26 with a phase `φ = ∓πi` recording the half-plane of `z`. -/
theorem zero_second_connection_left_gen {a b c z φ : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (hab : ∀ k : ℤ, a - b ≠ (k : ℂ)) (hz : ‖z‖ < 1) (hw : 1 < ‖1 - z‖)
    (hphase : ∀ y : ℂ, (z / (z - 1)) ^ y = exp ((log z - log (1 - z) + φ) * y)) :
    zeroSecond a b c z =
      exp (φ * (c - 1)) * Gamma (2 - c) * Gamma (b - a) / (Gamma (1 - a) * Gamma (b - c + 1)) *
        kummerFiveLeft a b c z + exp (φ * (c - 1)) * Gamma (2 - c) * Gamma (a - b) /
        (Gamma (1 - b) * Gamma (a - c + 1)) * kummerSixLeft a b c z := by
  have h1z : 1 - z ≠ 0 := by intro h; rw [h] at hw; norm_num at hw
  have hz0 : z ≠ 0 := by rintro rfl; simp at hw
  have hy : ‖1 / (1 - z)‖ < 1 := by
    rw [norm_div, norm_one, div_lt_one (by linarith)]
    exact hw
  have h1y : 1 - 1 / (1 - z) = z / (z - 1) := by
    have : z - 1 ≠ 0 := by intro h; apply h1z; linear_combination -h
    field_simp
    ring
  have hc' : ∀ k : ℤ, 2 - c ≠ (k : ℂ) := fun k h => hc (2 - k) (by
    push_cast; linear_combination -h)
  have hab' : ∀ k : ℤ, a - c + 1 - (b - c + 1) ≠ (k : ℂ) := fun k h => hab k (by
    linear_combination h)
  have hC : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ) := not_neg_nat_of_not_int fun k h => hab (k - 1) (by
    push_cast; linear_combination h)
  have hC' : ∀ k : ℕ, b - a + 1 ≠ -(k : ℂ) := not_neg_nat_of_not_int fun k h => hab (1 - k) (by
    push_cast; linear_combination -h)
  have key := zero_first_connection_left_gen (a := a - c + 1) (b := b - c + 1) hc' hab' hz hw
  simp only [kummerFiveLeft, kummerSixLeft] at key ⊢
  rw [show b - c + 1 - (a - c + 1) = b - a by ring, show 2 - c - (a - c + 1) = 1 - a by ring,
    show a - c + 1 - (b - c + 1) = a - b by ring, show 2 - c - (b - c + 1) = 1 - b by ring] at key
  rw [euler_transformation_of_ne_neg_nat hC hy, euler_transformation_of_ne_neg_nat hC' hy, h1y,
    show a - b + 1 - (a - c + 1) - (1 - b) = c - 1 by ring,
    show a - b + 1 - (a - c + 1) = c - b by ring, show a - b + 1 - (1 - b) = a by ring,
    show b - a + 1 - (b - c + 1) - (1 - a) = c - 1 by ring,
    show b - a + 1 - (b - c + 1) = c - a by ring, show b - a + 1 - (1 - a) = b by ring,
    ordinaryHypergeometric_symm (c - b) a, ordinaryHypergeometric_symm (c - a) b] at key
  rw [zeroSecond, key]
  simp only [hphase, cpow_eq_exp_log h1z, cpow_eq_exp_log hz0]
  have e1 : exp (log z * (1 - c)) * (exp (log (1 - z) * -(a - c + 1)) *
      exp ((log z - log (1 - z) + φ) * (c - 1))) = exp (φ * (c - 1)) * exp (log (1 - z) * -a) := by
    simp only [← exp_add]
    ring_nf
  have e2 : exp (log z * (1 - c)) * (exp (log (1 - z) * -(b - c + 1)) *
      exp ((log z - log (1 - z) + φ) * (c - 1))) = exp (φ * (c - 1)) * exp (log (1 - z) * -b) := by
    simp only [← exp_add]
    ring_nf
  linear_combination (Gamma (2 - c) * Gamma (b - a) / (Gamma (b - c + 1) * Gamma (1 - a)) *
      ₂F₁ a (c - b) (a - b + 1) (1 / (1 - z))) * e1 +
    (Gamma (2 - c) * Gamma (a - b) / (Gamma (a - c + 1) * Gamma (1 - b)) *
      ₂F₁ b (c - a) (b - a + 1) (1 / (1 - z))) * e2

@[dlmf 15.10.E12]
theorem zero_second_representations
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, 2 - c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane)
    (hw : ‖z /
    (z - 1)‖ < 1) :
    zeroSecond a b c z = z ^ (1 - c) * (1 - z) ^ (c - a - b) * ₂F₁ (1 - a) (1 - b) (2 - c) z ∧
      zeroSecond a b c z = z ^ (1 - c) * (1 - z) ^ (c - a - 1) * ₂F₁ (a - c + 1) (1 - b) (2 - c) (z / (z - 1)) ∧
      zeroSecond a b c z = z ^ (1 - c) * (1 - z) ^ (c - b - 1) * ₂F₁ (1 - a) (b - c + 1) (2 - c) (z / (z -
        1)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold zeroSecond
    rw [euler_transformation_of_ne_neg_nat hc hz,
      show 2 - c - (a - c + 1) - (b - c + 1) = c - a - b by ring,
      show 2 - c - (a - c + 1) = 1 - a by ring, show 2 - c - (b - c + 1) = 1 - b by ring]
    ring
  · unfold zeroSecond
    rw [pfaff_transformation_of_ne_neg_nat hc hz hw, show -(a - c + 1) = c - a - 1 by ring,
      show 2 - c - (b - c + 1) = 1 - b by ring]
    ring
  · unfold zeroSecond
    rw [show (₂F₁ (a - c + 1) (b - c + 1) (2 - c) : ℂ → ℂ) = ₂F₁ (b - c + 1) (a - c + 1) (2 - c) from
      ordinaryHypergeometric_symm _ _ _, pfaff_transformation_of_ne_neg_nat hc hz hw,
      show -(b - c + 1) = c - b - 1 by ring, show 2 - c - (a - c + 1) = 1 - a by ring,
      show (₂F₁ (b - c + 1) (1 - a) (2 - c) : ℂ → ℂ) = ₂F₁ (1 - a) (b - c + 1) (2 - c) from
      ordinaryHypergeometric_symm _ _ _]
    ring

@[dlmf 15.10.E13]
theorem one_first_representations
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, a + b - c + 1 ≠ -(k : ℂ))
    (hz : ‖1 - z‖ < 1)
    (hw : ‖1 - 1 / z‖ < 1) :
    oneFirst a b c z = z ^ (1 - c) * ₂F₁ (a - c + 1) (b - c + 1) (a + b - c + 1) (1 - z) ∧
      oneFirst a b c z = z ^ (-a) * ₂F₁ a (a - c + 1) (a + b - c + 1) (1 - 1 / z) ∧
      oneFirst a b c z = z ^ (-b) * ₂F₁ b (b - c + 1) (a + b - c + 1) (1 - 1 / z) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hw
  have hmap : (1 - z) / (1 - z - 1) = 1 - 1 / z := by
    rw [show (1 : ℂ) - z - 1 = -z by ring]
    field_simp
    try ring
  have hw' : ‖(1 - z) / (1 - z - 1)‖ < 1 := by rwa [hmap]
  refine ⟨?_, ?_, ?_⟩
  · unfold oneFirst
    rw [euler_transformation_of_ne_neg_nat hc hz, sub_sub_cancel,
      show a + b - c + 1 - a - b = 1 - c by ring, show a + b - c + 1 - a = b - c + 1 by ring,
      show a + b - c + 1 - b = a - c + 1 by ring,
      show (₂F₁ (b - c + 1) (a - c + 1) (a + b - c + 1) : ℂ → ℂ) =
        ₂F₁ (a - c + 1) (b - c + 1) (a + b - c + 1) from ordinaryHypergeometric_symm _ _ _]
  · unfold oneFirst
    rw [pfaff_transformation_of_ne_neg_nat hc hz hw', sub_sub_cancel, hmap,
      show a + b - c + 1 - b = a - c + 1 by ring]
  · unfold oneFirst
    rw [show (₂F₁ a b (a + b - c + 1) : ℂ → ℂ) = ₂F₁ b a (a + b - c + 1) from
      ordinaryHypergeometric_symm _ _ _, pfaff_transformation_of_ne_neg_nat hc hz hw',
      sub_sub_cancel, hmap, show a + b - c + 1 - a = b - c + 1 by ring]

@[dlmf 15.10.E14]
theorem one_second_representations
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, c - a - b + 1 ≠ -(k : ℂ))
    (hz : ‖1 - z‖ < 1)
    (hs : 1 - z ∈ slitPlane)
    (hw : ‖1 - 1 / z‖ < 1) :
    oneSecond a b c z = z ^ (1 - c) * (1 - z) ^ (c - a - b) * ₂F₁ (1 - a) (1 - b) (c - a - b + 1) (1 - z) ∧
      oneSecond a b c z = z ^ (a - c) * (1 - z) ^ (c - a - b) * ₂F₁ (1 - a) (c - a) (c - a - b + 1) (1 - 1 /
        z) ∧
      oneSecond a b c z = z ^ (b - c) * (1 - z) ^ (c - a - b) * ₂F₁ (1 - b) (c - b) (c - a - b + 1) (1 - 1 /
        z) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hw
  have hmap : (1 - z) / (1 - z - 1) = 1 - 1 / z := by
    rw [show (1 : ℂ) - z - 1 = -z by ring]
    field_simp
    try ring
  have hw' : ‖(1 - z) / (1 - z - 1)‖ < 1 := by rwa [hmap]
  refine ⟨?_, ?_, ?_⟩
  · unfold oneSecond
    rw [euler_transformation_of_ne_neg_nat hc hz, sub_sub_cancel,
      show c - a - b + 1 - (c - a) - (c - b) = 1 - c by ring,
      show c - a - b + 1 - (c - a) = 1 - b by ring, show c - a - b + 1 - (c - b) = 1 - a by ring,
      show (₂F₁ (1 - b) (1 - a) (c - a - b + 1) : ℂ → ℂ) = ₂F₁ (1 - a) (1 - b) (c - a - b + 1) from
        ordinaryHypergeometric_symm _ _ _]
    ring
  · unfold oneSecond
    rw [pfaff_transformation_of_ne_neg_nat hc hz hw', sub_sub_cancel, hmap,
      show -(c - a) = a - c by ring, show c - a - b + 1 - (c - b) = 1 - a by ring,
      show (₂F₁ (c - a) (1 - a) (c - a - b + 1) : ℂ → ℂ) = ₂F₁ (1 - a) (c - a) (c - a - b + 1) from
        ordinaryHypergeometric_symm _ _ _]
    ring
  · unfold oneSecond
    rw [show (₂F₁ (c - a) (c - b) (c - a - b + 1) : ℂ → ℂ) = ₂F₁ (c - b) (c - a) (c - a - b + 1) from
      ordinaryHypergeometric_symm _ _ _, pfaff_transformation_of_ne_neg_nat hc hz hw',
      sub_sub_cancel, hmap, show -(c - b) = b - c by ring,
      show c - a - b + 1 - (c - a) = 1 - b by ring,
      show (₂F₁ (c - b) (1 - b) (c - a - b + 1) : ℂ → ℂ) = ₂F₁ (1 - b) (c - b) (c - a - b + 1) from
        ordinaryHypergeometric_symm _ _ _]
    ring

@[dlmf 15.10.E15]
theorem kummer_five_representations
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (hz : 1 < ‖z‖)
    (hw : 1 < ‖1 - z‖)
    (hi : 0 < z.im) :
    kummerFive a b c z = exp ((c - b) * Real.pi * I) * z ^ (b - c) * (1 - z) ^ (c - a - b) * ₂F₁ (1 - b) (c
      - b) (a - b + 1) (1 / z) ∧
      kummerFive a b c z = kummerFiveLeft a b c z ∧
      kummerFive a b c z = exp ((c - 1) * Real.pi * I) * z ^ (1 - c) * (1 - z) ^ (c - a - 1) * ₂F₁ (1 - b)
        (a - c + 1) (a - b + 1) (1 / (1 - z)) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hi
  have h1z : 1 - z ≠ 0 := by intro h; rw [h] at hw; norm_num at hw
  have hz1 : z - 1 ≠ 0 := by intro h; apply h1z; linear_combination -h
  have hwn : ‖1 / z‖ < 1 := by
    rw [norm_div, norm_one, div_lt_one (by linarith)]
    exact hz
  have hy : ‖1 / (1 - z)‖ < 1 := by
    rw [norm_div, norm_one, div_lt_one (by linarith)]
    exact hw
  have hww : 1 / z / (1 / z - 1) = 1 / (1 - z) := by
    field_simp
  have h1y : 1 - 1 / (1 - z) = z / (z - 1) := by
    field_simp
    ring
  have hwn' : ‖1 / z / (1 / z - 1)‖ < 1 := by rwa [hww]
  have hleft : kummerFive a b c z = kummerFiveLeft a b c z := by
    simp only [kummerFive, infinityFirst, kummerFiveLeft]
    rw [pfaff_transformation_of_ne_neg_nat hc hwn hwn', hww,
      show a - b + 1 - (a - c + 1) = c - b by ring, one_sub_recip_cpow_upper hi,
      cpow_eq_exp_log hz0, cpow_eq_exp_log h1z]
    have e : exp (↑a * ↑Real.pi * I) * (exp (log z * -a) *
        exp ((log (1 - z) - log z + ↑Real.pi * I) * -a)) = exp (log (1 - z) * -a) := by
      simp only [← exp_add]
      ring_nf
    linear_combination (₂F₁ a (c - b) (a - b + 1) (1 / (1 - z))) * e
  refine ⟨?_, hleft, ?_⟩
  · simp only [kummerFive, infinityFirst]
    rw [euler_transformation_of_ne_neg_nat hc hwn, show a - b + 1 - a - (a - c + 1) = c - a - b by
      ring, show a - b + 1 - a = 1 - b by ring, show a - b + 1 - (a - c + 1) = c - b by ring,
      one_sub_recip_cpow_upper hi, cpow_eq_exp_log hz0, cpow_eq_exp_log hz0, cpow_eq_exp_log h1z]
    have e : exp (↑a * ↑Real.pi * I) * (exp (log z * -a) *
        exp ((log (1 - z) - log z + ↑Real.pi * I) * (c - a - b))) =
        exp ((c - b) * ↑Real.pi * I) * exp (log z * (b - c)) * exp (log (1 - z) * (c - a - b)) := by
      simp only [← exp_add]
      ring_nf
    linear_combination (₂F₁ (1 - b) (c - b) (a - b + 1) (1 / z)) * e
  · rw [hleft, kummerFiveLeft, euler_transformation_of_ne_neg_nat hc hy, h1y,
      show a - b + 1 - a - (c - b) = 1 - c by ring, show a - b + 1 - a = 1 - b by ring,
      show a - b + 1 - (c - b) = a - c + 1 by ring, div_sub_one_cpow_upper hi,
      cpow_eq_exp_log hz0, cpow_eq_exp_log h1z, cpow_eq_exp_log h1z]
    have e : exp (log (1 - z) * -a) * exp ((log z - log (1 - z) + -(↑Real.pi * I)) * (1 - c)) =
        exp ((c - 1) * ↑Real.pi * I) * exp (log z * (1 - c)) * exp (log (1 - z) * (c - a - 1)) := by
      simp only [← exp_add]
      ring_nf
    linear_combination (₂F₁ (1 - b) (a - c + 1) (a - b + 1) (1 / (1 - z))) * e

@[dlmf 15.10.E16]
theorem kummer_six_representations
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, b - a + 1 ≠ -(k : ℂ))
    (hz : 1 < ‖z‖)
    (hw : 1 < ‖1 - z‖)
    (hi : 0 < z.im) :
    kummerSix a b c z = exp ((c - a) * Real.pi * I) * z ^ (a - c) * (1 - z) ^ (c - a - b) * ₂F₁ (1 - a) (c -
      a) (b - a + 1) (1 / z) ∧
      kummerSix a b c z = kummerSixLeft a b c z ∧
      kummerSix a b c z = exp ((c - 1) * Real.pi * I) * z ^ (1 - c) * (1 - z) ^ (c - b - 1) * ₂F₁ (1 - a) (b
        - c + 1) (b - a + 1) (1 / (1 - z)) := by
  obtain ⟨h1, h2, h3⟩ := kummer_five_representations (a := b) (b := a) (c := c) hc hz hw hi
  refine ⟨?_, h2, h3⟩
  rw [show c - a - b = c - b - a by ring]
  exact h1

@[dlmf 15.10.E19]
theorem kummer_five_left_connection_zero {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (_he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hab : ∀ k : ℤ, a - b ≠ (k : ℂ))
    (hz : ‖z‖ < 1) (hw : 1 < ‖1 - z‖) (hi : 0 < z.im) :
    kummerFiveLeft a b c z =
      Gamma (1 - c) * Gamma (a - b + 1) / (Gamma (a - c + 1) * Gamma (1 - b)) * ₂F₁ a b c z + exp ((c - 1) *
        Real.pi * I) * Gamma (c - 1) * Gamma (a - b + 1) / (Gamma a * Gamma (c - b)) * zeroSecond a b c z :=
        by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hi
  have h1z : 1 - z ≠ 0 := by intro h; rw [h] at hw; norm_num at hw
  have hz1 : z - 1 ≠ 0 := by intro h; apply h1z; linear_combination -h
  have hn : ‖z - 1‖ = ‖1 - z‖ := norm_sub_rev z 1
  have hu : ‖z / (z - 1)‖ < 1 := by
    rw [norm_div, hn, div_lt_one (by linarith)]
    linarith
  have h1u : 1 - z / (z - 1) = 1 / (1 - z) := by
    field_simp
    ring
  have hu1 : ‖1 - z / (z - 1)‖ < 1 := by
    rw [h1u, norm_div, norm_one, div_lt_one (by linarith)]
    exact hw
  have he' : ∀ k : ℤ, c - a - (c - b) ≠ (k : ℂ) := fun k h => hab (-k) (by
    push_cast; linear_combination -h)
  have hc2 : ∀ k : ℕ, 2 - c ≠ -(k : ℂ) := not_neg_nat_of_not_int fun k h => hc (2 - k) (by
    push_cast; linear_combination -h)
  have key := one_first_connection_zero (a := a) (b := c - b) hc he' hu hu1
  rw [show a + (c - b) - c + 1 = a - b + 1 by ring, show c - b - c + 1 = 1 - b by ring] at key
  have hk : kummerFiveLeft a b c z = (1 - z) ^ (-a) * oneFirst a (c - b) c (z / (z - 1)) := by
    simp only [kummerFiveLeft, oneFirst]
    rw [show a + (c - b) - c + 1 = a - b + 1 by ring, h1u]
  rw [hk, key, pfaff_transformation_of_ne_neg_nat (not_neg_nat_of_not_int hc) hz hu, zeroSecond,
    zeroSecond, pfaff_transformation_of_ne_neg_nat hc2 hz hu,
    show 2 - c - (b - c + 1) = 1 - b by ring, show c - b - c + 1 = 1 - b by ring,
    div_sub_one_cpow_upper hi, cpow_eq_exp_log hz0, cpow_eq_exp_log h1z, cpow_eq_exp_log h1z]
  have e : exp (log (1 - z) * -a) * exp ((log z - log (1 - z) + -(↑Real.pi * I)) * (1 - c)) =
      exp ((c - 1) * ↑Real.pi * I) * (exp (log z * (1 - c)) *
        exp (log (1 - z) * -(a - c + 1))) := by
    simp only [← exp_add]
    ring_nf
  linear_combination (Gamma (c - 1) * Gamma (a - b + 1) / (Gamma a * Gamma (c - b)) *
    ₂F₁ (a - c + 1) (1 - b) (2 - c) (z / (z - 1))) * e

@[dlmf 15.10.E20]
theorem kummer_six_left_connection_zero {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (_he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hab : ∀ k : ℤ, a - b ≠ (k : ℂ))
    (hz : ‖z‖ < 1) (hw : 1 < ‖1 - z‖) (hi : 0 < z.im) :
    kummerSixLeft a b c z =
      Gamma (1 - c) * Gamma (b - a + 1) / (Gamma (b - c + 1) * Gamma (1 - a)) * ₂F₁ a b c z + exp ((c - 1) *
        Real.pi * I) * Gamma (c - 1) * Gamma (b - a + 1) / (Gamma b * Gamma (c - a)) * zeroSecond a b c z :=
        by
  have hab' : ∀ k : ℤ, b - a ≠ (k : ℂ) := fun k h => hab (-k) (by
    push_cast; linear_combination -h)
  have h := kummer_five_left_connection_zero (a := b) (b := a) (c := c) hc
    (fun k h => _he k (by linear_combination h)) hab' hz hw hi
  have hz2 : zeroSecond b a c z = zeroSecond a b c z := by
    simp only [zeroSecond]
    rw [ordinaryHypergeometric_symm]
  rw [kummerSixLeft, ← kummerFiveLeft, h, ordinaryHypergeometric_symm b a, hz2]

@[dlmf 15.10.E25]
theorem zero_first_connection_left {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (_he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hab : ∀ k : ℤ, a - b ≠ (k : ℂ))
    (hz : ‖z‖ < 1) (hw : 1 < ‖1 - z‖) (_hi : 0 < z.im) :
    ₂F₁ a b c z =
      Gamma c * Gamma (b - a) / (Gamma b * Gamma (c - a)) * kummerFiveLeft a b c z + Gamma c * Gamma (a - b)
        / (Gamma a * Gamma (c - b)) * kummerSixLeft a b c z := by
  exact zero_first_connection_left_gen hc hab hz hw

@[dlmf 15.10.E26]
theorem zero_second_connection_left {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (_he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hab : ∀ k : ℤ, a - b ≠ (k : ℂ))
    (hz : ‖z‖ < 1) (hw : 1 < ‖1 - z‖) (hi : 0 < z.im) :
    zeroSecond a b c z =
      exp ((1 - c) * Real.pi * I) * Gamma (2 - c) * Gamma (b - a) / (Gamma (1 - a) * Gamma (b - c + 1)) *
        kummerFiveLeft a b c z + exp ((1 - c) * Real.pi * I) * Gamma (2 - c) * Gamma (a - b) / (Gamma (1 -
        b) * Gamma (a - c + 1)) * kummerSixLeft a b c z := by
  have h := zero_second_connection_left_gen (φ := -(↑Real.pi * I)) hc hab hz hw
    (div_sub_one_cpow_upper hi)
  rw [show -(↑Real.pi * I) * (c - 1) = (1 - c) * ↑Real.pi * I by ring] at h
  exact h

@[dlmf 15.10.E23]
theorem kummer_five_connection_one {a b c z : ℂ} (_hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hab : ∀ k : ℤ, a - b ≠ (k : ℂ))
    (hz : 1 < ‖z‖) (hw : ‖1 - z‖ < 1) (hi : 0 < z.im) :
    kummerFive a b c z =
      exp (a * Real.pi * I) * Gamma (a - b + 1) * Gamma (c - a - b) / (Gamma (1 - b) * Gamma (c - b)) *
        oneFirst a b c z + exp ((c - b) * Real.pi * I) * Gamma (a - b + 1) * Gamma (a + b - c) / (Gamma a *
        Gamma (a - c + 1)) * oneSecond a b c z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hi
  have h1z : 1 - z ≠ 0 := by intro h; have := congrArg im h; simp at this; linarith
  have hv : ‖1 / z‖ < 1 := by
    rw [norm_div, norm_one, div_lt_one (by linarith)]
    exact hz
  have h1v : ‖1 - 1 / z‖ < 1 := by
    rw [show 1 - 1 / z = (z - 1) / z by field_simp, norm_div, norm_sub_rev,
      div_lt_one (by linarith)]
    linarith
  have hs : 1 - z ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr (by simp; linarith))
  have hc' : ∀ k : ℤ, a - b + 1 ≠ (k : ℂ) := fun k h => hab (k - 1) (by
    push_cast; linear_combination h)
  have he' : ∀ k : ℤ, a - b + 1 - a - (a - c + 1) ≠ (k : ℂ) := fun k h => he k (by
    linear_combination h)
  have hC : ∀ k : ℕ, a + b - c + 1 ≠ -(k : ℂ) := not_neg_nat_of_not_int fun k h => he (1 - k) (by
    push_cast; linear_combination -h)
  have hS : ∀ k : ℕ, c - a - b + 1 ≠ -(k : ℂ) := not_neg_nat_of_not_int fun k h => he (k - 1) (by
    push_cast; linear_combination h)
  have key := zero_first_connection_one (a := a) (b := a - c + 1) (c := a - b + 1) hc' he' hv h1v
  rw [show a - b + 1 - a - (a - c + 1) = c - a - b by ring, show a - b + 1 - a = 1 - b by ring,
    show a - b + 1 - (a - c + 1) = c - b by ring,
    show a + (a - c + 1) - (a - b + 1) = a + b - c by ring] at key
  rw [(one_first_representations hC hw h1v).2.1, (one_second_representations hS hw hs h1v).2.2]
  simp only [kummerFive, infinityFirst]
  rw [key]
  simp only [oneFirst, oneSecond]
  rw [show a + (a - c + 1) - (a - b + 1) + 1 = a + b - c + 1 by ring,
    show a - b + 1 - a - (a - c + 1) = c - a - b by ring, show a - b + 1 - a = 1 - b by ring,
    show a - b + 1 - (a - c + 1) = c - b by ring, one_sub_recip_cpow_upper hi,
    cpow_eq_exp_log hz0 (-a), cpow_eq_exp_log hz0 (b - c), cpow_eq_exp_log h1z (c - a - b)]
  have e : exp (↑a * ↑Real.pi * I) * (exp (log z * -a) *
      exp ((log (1 - z) - log z + ↑Real.pi * I) * (c - a - b))) =
      exp ((c - b) * ↑Real.pi * I) * (exp (log z * (b - c)) * exp (log (1 - z) * (c - a - b))) := by
    simp only [← exp_add]
    ring_nf
  linear_combination (Gamma (a - b + 1) * Gamma (a + b - c) / (Gamma a * Gamma (a - c + 1)) *
    ₂F₁ (1 - b) (c - b) (c - a - b + 1) (1 - 1 / z)) * e

@[dlmf 15.10.E24]
theorem kummer_six_connection_one {a b c z : ℂ} (_hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hab : ∀ k : ℤ, a - b ≠ (k : ℂ))
    (hz : 1 < ‖z‖) (hw : ‖1 - z‖ < 1) (hi : 0 < z.im) :
    kummerSix a b c z =
      exp (b * Real.pi * I) * Gamma (b - a + 1) * Gamma (c - a - b) / (Gamma (1 - a) * Gamma (c - a)) *
        oneFirst a b c z + exp ((c - a) * Real.pi * I) * Gamma (b - a + 1) * Gamma (a + b - c) / (Gamma b *
        Gamma (b - c + 1)) * oneSecond a b c z := by
  have hab' : ∀ k : ℤ, b - a ≠ (k : ℂ) := fun k h => hab (-k) (by
    push_cast; linear_combination -h)
  have h := kummer_five_connection_one (a := b) (b := a) (c := c) _hc
    (fun k h => he k (by linear_combination h)) hab' hz hw hi
  have h1 : oneFirst b a c z = oneFirst a b c z := by
    simp only [oneFirst]
    rw [show b + a - c + 1 = a + b - c + 1 by ring, ordinaryHypergeometric_symm]
  have h2 : oneSecond b a c z = oneSecond a b c z := by
    simp only [oneSecond]
    rw [show c - b - a = c - a - b by ring, ordinaryHypergeometric_symm]
  rw [kummerSix, ← kummerFive, h, h1, h2, show c - b - a = c - a - b by ring,
    show b + a - c = a + b - c by ring]

@[dlmf 15.10.E27]
theorem one_first_connection_infinity {a b c z : ℂ} (_hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hab : ∀ k : ℤ, a - b ≠ (k : ℂ))
    (hz : 1 < ‖z‖) (hw : ‖1 - z‖ < 1) (_hi : 0 < z.im) :
    oneFirst a b c z =
      exp (-a * Real.pi * I) * Gamma (a + b - c + 1) * Gamma (b - a) / (Gamma b * Gamma (b - c + 1)) *
        kummerFive a b c z + exp (-b * Real.pi * I) * Gamma (a + b - c + 1) * Gamma (a - b) / (Gamma a *
        Gamma (a - c + 1)) * kummerSix a b c z := by
  have hC : ∀ k : ℤ, a + b - c + 1 ≠ (k : ℂ) := fun k h => he (1 - k) (by
    push_cast; linear_combination -h)
  have key := zero_first_connection_left_gen (a := a) (b := b) (c := a + b - c + 1) hC hab hw
    (by rwa [sub_sub_cancel])
  have hF : kummerFiveLeft a b (a + b - c + 1) (1 - z) =
      exp (-a * ↑Real.pi * I) * kummerFive a b c z := by
    simp only [kummerFiveLeft, kummerFive, infinityFirst]
    rw [sub_sub_cancel, show a + b - c + 1 - b = a - c + 1 by ring, ← mul_assoc, ← exp_add,
      show -a * ↑Real.pi * I + a * ↑Real.pi * I = 0 by ring, exp_zero, one_mul]
  have hS : kummerSixLeft a b (a + b - c + 1) (1 - z) =
      exp (-b * ↑Real.pi * I) * kummerSix a b c z := by
    simp only [kummerSixLeft, kummerSix, infinityFirst]
    rw [sub_sub_cancel, show a + b - c + 1 - a = b - c + 1 by ring, ← mul_assoc, ← exp_add,
      show -b * ↑Real.pi * I + b * ↑Real.pi * I = 0 by ring, exp_zero, one_mul]
  rw [oneFirst, key, hF, hS, show a + b - c + 1 - a = b - c + 1 by ring,
    show a + b - c + 1 - b = a - c + 1 by ring]
  ring

@[dlmf 15.10.E28]
theorem one_second_connection_infinity {a b c z : ℂ} (_hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hab : ∀ k : ℤ, a - b ≠ (k : ℂ))
    (hz : 1 < ‖z‖) (hw : ‖1 - z‖ < 1) (hi : 0 < z.im) :
    oneSecond a b c z =
      exp ((b - c) * Real.pi * I) * Gamma (c - a - b + 1) * Gamma (b - a) / (Gamma (1 - a) * Gamma (c - a))
        * kummerFive a b c z + exp ((a - c) * Real.pi * I) * Gamma (c - a - b + 1) * Gamma (a - b) / (Gamma
        (1 - b) * Gamma (c - b)) * kummerSix a b c z := by
  have hC : ∀ k : ℤ, a + b - c + 1 ≠ (k : ℂ) := fun k h => he (1 - k) (by
    push_cast; linear_combination -h)
  have him : (1 - z).im < 0 := by simp; linarith
  have key := zero_second_connection_left_gen (φ := ↑Real.pi * I) (a := a) (b := b)
    (c := a + b - c + 1) hC hab hw (by rwa [sub_sub_cancel]) (div_sub_one_cpow_lower him)
  have hZ : zeroSecond a b (a + b - c + 1) (1 - z) = oneSecond a b c z := by
    simp only [zeroSecond, oneSecond]
    rw [show 1 - (a + b - c + 1) = c - a - b by ring, show a - (a + b - c + 1) + 1 = c - b by ring,
      show b - (a + b - c + 1) + 1 = c - a by ring,
      show 2 - (a + b - c + 1) = c - a - b + 1 by ring, ordinaryHypergeometric_symm]
  have hF : kummerFiveLeft a b (a + b - c + 1) (1 - z) =
      exp (-a * ↑Real.pi * I) * kummerFive a b c z := by
    simp only [kummerFiveLeft, kummerFive, infinityFirst]
    rw [sub_sub_cancel, show a + b - c + 1 - b = a - c + 1 by ring, ← mul_assoc, ← exp_add,
      show -a * ↑Real.pi * I + a * ↑Real.pi * I = 0 by ring, exp_zero, one_mul]
  have hS : kummerSixLeft a b (a + b - c + 1) (1 - z) =
      exp (-b * ↑Real.pi * I) * kummerSix a b c z := by
    simp only [kummerSixLeft, kummerSix, infinityFirst]
    rw [sub_sub_cancel, show a + b - c + 1 - a = b - c + 1 by ring, ← mul_assoc, ← exp_add,
      show -b * ↑Real.pi * I + b * ↑Real.pi * I = 0 by ring, exp_zero, one_mul]
  rw [← hZ, key, hF, hS, show 2 - (a + b - c + 1) = c - a - b + 1 by ring,
    show b - (a + b - c + 1) + 1 = c - a by ring, show a - (a + b - c + 1) + 1 = c - b by ring]
  have e1 : exp (↑Real.pi * I * (a + b - c + 1 - 1)) * exp (-a * ↑Real.pi * I) =
      exp ((b - c) * ↑Real.pi * I) := by rw [← exp_add]; ring_nf
  have e2 : exp (↑Real.pi * I * (a + b - c + 1 - 1)) * exp (-b * ↑Real.pi * I) =
      exp ((a - c) * ↑Real.pi * I) := by rw [← exp_add]; ring_nf
  linear_combination (Gamma (c - a - b + 1) * Gamma (b - a) / (Gamma (1 - a) * Gamma (c - a)) *
      kummerFive a b c z) * e1 +
    (Gamma (c - a - b + 1) * Gamma (a - b) / (Gamma (1 - b) * Gamma (c - b)) *
      kummerSix a b c z) * e2

end DLMF.Hypergeometric
