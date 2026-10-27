/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Relations
public import DLMF.Confluent.TricomiRotated

/-!
# Large-argument asymptotics of Bessel functions (DLMF 10.40, 10.17)

Kummer's relation `K_ν(z) = √π e^{-z} (2z)^ν U(ν+½, 2ν+1, 2z)` (DLMF 13.6.10) and Tricomi's
expansion of `U` in rotated sectors give Hankel's expansion

`e^z K_ν(z) ~ √π ∑ₖ (-1)^k (ν+½)ₖ (½-ν)ₖ / k! · (2z)^{-k-½}` (DLMF 10.40.2)

as `z → ∞` in every closed sector `|arg z| ≤ π - ε`.
-/

@[expose] public section

open Complex Filter Asymptotics Set DLMF.Confluent
open scoped Real Topology
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Bessel

/-- Doubling preserves the closed sector filter. -/
theorem tendsto_two_mul_sectorAtTop (δ : ℝ) :
    Tendsto (fun z : ℂ => 2 * z) (sectorAtTop δ) (sectorAtTop δ) := by
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
  · have h := (tendsto_norm_sectorAtTop δ).const_mul_atTop (two_pos : (0 : ℝ) < 2)
    refine h.congr fun z => ?_
    simp
  · rw [sectorAtTop]
    refine mem_inf_of_right (mem_principal.mpr fun z hz => ?_)
    have hz' : δ * ‖z‖ ≤ z.re := hz
    show δ * ‖2 * z‖ ≤ (2 * z).re
    have h1 : (2 * z).re = 2 * z.re := by simp
    have h2 : ‖2 * z‖ = 2 * ‖z‖ := by simp
    rw [h1, h2]
    linarith

/-- Doubling preserves the rotated sector filter. -/
theorem tendsto_two_mul_rotSectorAtTop (δ α : ℝ) :
    Tendsto (fun z : ℂ => 2 * z) (rotSectorAtTop δ α) (rotSectorAtTop δ α) := by
  refine tendsto_comap_iff.mpr ?_
  have h := (tendsto_two_mul_sectorAtTop δ).comp (tendsto_rotSectorAtTop δ α)
  refine h.congr fun z => ?_
  simp only [Function.comp]
  ring

/-- Eventually in a rotated sector, `z` lies in the slit plane. -/
theorem eventually_mem_slitPlane_rotSectorAtTop {δ α : ℝ} (hδ : 0 < δ) (hα : |α| < π / 2) :
    ∀ᶠ z in rotSectorAtTop δ α, z ∈ slitPlane := by
  filter_upwards [eventually_rotSectorAtTop hδ hα] with z hz
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith [hz.1]
  refine mem_slitPlane_iff_arg.mpr ⟨fun h => ?_, hz0⟩
  have h3 := hz.2.2
  rw [h] at h3
  linarith [(abs_lt.mp h3).2, (abs_lt.mp hα).1]

/-- **Hankel's expansion of `K_ν`** (DLMF 10.40.2): in every rotated sector,
`e^z K_ν(z) ~ √π ∑ₖ (-1)^k (ν+½)ₖ (½-ν)ₖ / k! · (2z)^{-k-½}`. -/
@[dlmf 10.40.E2]
theorem hasAsymptoticExpansion_besselK (ν : ℂ) {δ α : ℝ} (hδ : 0 < δ) (hα : |α| < π / 2) :
    HasAsymptoticExpansion (rotSectorAtTop δ α)
      (fun (n : ℕ) (z : ℂ) => (2 * z) ^ (-((n : ℂ) + 1 / 2)))
      (fun n => (Real.sqrt π : ℂ) * tricomiCoeff (ν + 1 / 2) (2 * ν + 1) n)
      (fun z => exp z * besselK ν z) := by
  have hU := (hasAsymptoticExpansion_kummerU_rotSector (ν + 1 / 2) (2 * ν + 1) hδ
    hα).comp_tendsto
    (tendsto_two_mul_rotSectorAtTop δ α)
  have h1 := hU.mul_left (fun z => (Real.sqrt π : ℂ) * (2 * z) ^ ν)
  have hslit := eventually_mem_slitPlane_rotSectorAtTop hδ hα
  have h2 := h1.smul_scale (κ := fun _ => (Real.sqrt π : ℂ))
    (ψ := fun (n : ℕ) (z : ℂ) => (2 * z) ^ (-((n : ℂ) + 1 / 2))) fun n => by
      filter_upwards [hslit] with z hz
      have h2z : 2 * z ≠ 0 := mul_ne_zero two_ne_zero (slitPlane_ne_zero hz)
      rw [mul_assoc, ← cpow_add _ _ h2z]
      congr 2
      ring
  refine h2.congr' ?_
  filter_upwards [hslit] with z hz
  have h2z : 2 * z ≠ 0 := mul_ne_zero two_ne_zero (slitPlane_ne_zero hz)
  have hsq : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpow : (2 * z) ^ ν * (2 * z) ^ (-ν) = 1 := by
    rw [cpow_neg, mul_inv_cancel₀ (cpow_ne_zero_iff.mpr (Or.inl h2z))]
  simp only [Function.comp, smul_eq_mul]
  rw [kummerU_besselK ν z hz]
  field_simp
  linear_combination besselK ν z * hpow
/-- Halving does not change the argument. -/
theorem arg_div_two (z : ℂ) : arg (z / 2) = arg z := by
  rw [div_eq_mul_inv, show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    arg_mul_real (by norm_num)]

/-- `e^{-iπ/2} = -i`. -/
theorem exp_neg_pi_div_two_mul_I' : exp ((-(π / 2) : ℝ) * I) = -I := by
  rw [exp_mul_I]
  push_cast
  rw [cos_neg, sin_neg, cos_pi_div_two, sin_pi_div_two]
  ring

/-- `I_ν(-iz) = e^{-iνπ/2} J_ν(z)` for `-π/2 < arg z` (DLMF 10.27.6). -/
theorem besselI_neg_I_mul {z : ℂ} (hz : z ≠ 0) (harg : -(π / 2) < arg z) (ν : ℂ) :
    besselI ν (-I * z) = exp (-(I * ν * π / 2)) * besselJ ν z := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  have hc := cpow_mul_exp_mul_I hz2 (α := -(π / 2)) (by rw [arg_div_two]; linarith)
    (by rw [arg_div_two]; linarith [arg_le_pi z, Real.pi_pos]) ν
  rw [exp_neg_pi_div_two_mul_I'] at hc
  rw [besselI, besselJ_eq_regularized, show -I * z / 2 = z / 2 * -I by ring, hc,
    show (-I * z) ^ 2 / 4 = -(z ^ 2 / 4) by ring_nf; rw [I_sq]; ring]
  push_cast
  ring_nf

/-- The Hankel–Macdonald connection at noninteger order. -/
lemma hankelH1_eq_besselK_of_not_int {ν z : ℂ} (hν : ∀ k : ℤ, ν ≠ k) (hz : z ≠ 0)
    (harg : -(π / 2) < arg z) :
    hankelH1 ν z = 2 / (π * I) * exp (-(I * ν * π / 2)) * besselK ν (-I * z) := by
  have hν' : ∀ k : ℤ, -ν ≠ k := fun k h => hν (-k) (by push_cast; linear_combination -h)
  rw [hankelH1, besselY_eq_of_not_int hν, besselK_eq_of_not_int hν, besselE, besselD,
    besselI_neg_I_mul hz harg, besselI_neg_I_mul hz harg]
  have hs := sin_mul_pi_ne_zero hν
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hep : exp (-(I * ν * π / 2)) * exp (-(I * -ν * π / 2)) = 1 := by
    rw [← exp_add]; ring_nf; exact exp_zero
  have hem : exp (-(I * ν * π / 2)) ^ 2 = cos (ν * π) - I * sin (ν * π) := by
    rw [← exp_nat_mul, show ((2 : ℕ) : ℂ) * -(I * ν * π / 2) = -(ν * π) * I by push_cast; ring,
      exp_mul_I, cos_neg, sin_neg]
    ring
  set ep := exp (-(I * -ν * π / 2))
  set em := exp (-(I * ν * π / 2))
  set S := sin (ν * π)
  set C := cos (ν * π)
  field_simp
  ring_nf
  rw [I_sq]
  linear_combination besselJ ν z * hem - besselJ (-ν) z * hep

/-- `e^{iπ/2} = i`. -/
theorem exp_pi_div_two_mul_I' : exp (((π / 2) : ℝ) * I) = I := by
  rw [exp_mul_I]
  push_cast
  rw [cos_pi_div_two, sin_pi_div_two]
  ring

/-- `I_ν(iz) = e^{iνπ/2} J_ν(z)` for `arg z ≤ π/2` (DLMF 10.27.6). -/
theorem besselI_I_mul {z : ℂ} (hz : z ≠ 0) (harg : arg z ≤ π / 2) (ν : ℂ) :
    besselI ν (I * z) = exp (I * ν * π / 2) * besselJ ν z := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  have hc := cpow_mul_exp_mul_I hz2 (α := π / 2)
    (by rw [arg_div_two]; linarith [neg_pi_lt_arg z, Real.pi_pos]) (by rw [arg_div_two]; linarith) ν
  rw [exp_pi_div_two_mul_I'] at hc
  rw [besselI, besselJ_eq_regularized, show I * z / 2 = z / 2 * I by ring, hc,
    show (I * z) ^ 2 / 4 = -(z ^ 2 / 4) by ring_nf; rw [I_sq]; ring]
  push_cast
  ring_nf

/-- `J_ν` through `K_ν(∓iz)` at noninteger order. -/
theorem besselJ_eq_besselK_of_not_int {ν z : ℂ} (hν : ∀ k : ℤ, ν ≠ k) (hz : z ≠ 0)
    (harg : |arg z| < π / 2) :
    besselJ ν z = 1 / (π * I) * (exp (-(I * ν * π / 2)) * besselK ν (-I * z) -
      exp (I * ν * π / 2) * besselK ν (I * z)) := by
  have h1 := (abs_lt.mp harg).1
  have h2 := (abs_lt.mp harg).2
  rw [besselK_eq_of_not_int hν, besselK_eq_of_not_int hν, besselE, besselE,
    besselI_neg_I_mul hz h1, besselI_neg_I_mul hz h1, besselI_I_mul hz h2.le,
    besselI_I_mul hz h2.le]
  have hs := sin_mul_pi_ne_zero hν
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hep : exp (-(I * ν * π / 2)) * exp (-(I * -ν * π / 2)) = 1 := by
    rw [← exp_add]; ring_nf; exact exp_zero
  have hep' : exp (I * ν * π / 2) * exp (I * -ν * π / 2) = 1 := by
    rw [← exp_add]; ring_nf; exact exp_zero
  have hem : exp (-(I * ν * π / 2)) ^ 2 = cos (ν * π) - I * sin (ν * π) := by
    rw [← exp_nat_mul, show ((2 : ℕ) : ℂ) * -(I * ν * π / 2) = -(ν * π) * I by push_cast; ring,
      exp_mul_I, cos_neg, sin_neg]
    ring
  have hem' : exp (I * ν * π / 2) ^ 2 = cos (ν * π) + I * sin (ν * π) := by
    rw [← exp_nat_mul, show ((2 : ℕ) : ℂ) * (I * ν * π / 2) = (ν * π) * I by push_cast; ring,
      exp_mul_I]
    ring
  generalize exp (-(I * ν * π / 2)) = a at *
  generalize exp (-(I * -ν * π / 2)) = b at *
  generalize exp (I * ν * π / 2) = c at *
  generalize exp (I * -ν * π / 2) = d at *
  generalize sin (ν * π) = S at *
  generalize cos (ν * π) = C at *
  generalize besselJ ν z = J at *
  generalize besselJ (-ν) z = J' at *
  field_simp
  ring_nf
  linear_combination J * hem - J * hem' - J' * hep + J' * hep'

/-- For `re z > 0`, `iz` lies in the slit plane. -/
theorem mem_slitPlane_I_mul {z : ℂ} (hz : 0 < z.re) : I * z ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inr (by simp; exact hz.ne'))

/-- For `re z > 0`, `-iz` lies in the slit plane. -/
theorem mem_slitPlane_neg_I_mul {z : ℂ} (hz : 0 < z.re) : -I * z ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inr (by simp; exact hz.ne'))

/-- For `re z > 0`, `J_ν(z) = (πi)⁻¹ (e^{-iνπ/2} K_ν(-iz) - e^{iνπ/2} K_ν(iz))`;
this is the sum of the two Hankel–Macdonald relations (DLMF 10.4.4 with 10.27.8). -/
theorem besselJ_eq_besselK (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    besselJ ν z = 1 / (π * I) * (exp (-(I * ν * π / 2)) * besselK ν (-I * z) -
      exp (I * ν * π / 2) * besselK ν (I * z)) := by
  have hzs : z ∈ slitPlane := Or.inl hz
  have harg : |arg z| < π / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  refine eq_of_continuousAt_of_integerComplement (f := fun μ => besselJ μ z)
    (g := fun μ => 1 / (π * I) * (exp (-(I * μ * π / 2)) * besselK μ (-I * z) -
      exp (I * μ * π / 2) * besselK μ (I * z)))
    (continuousAt_besselJ_order (fun μ => μ) continuous_id ν hzs) ?_
    (fun c hc => besselJ_eq_besselK_of_not_int (forall_of_mem_integerComplement hc)
      (slitPlane_ne_zero hzs) harg)
  refine continuousAt_const.mul (ContinuousAt.sub ?_ ?_)
  · exact (by fun_prop : Continuous fun μ : ℂ => exp (-(I * μ * π / 2))).continuousAt.mul
      (continuousAt_besselK_order (fun μ => μ) continuous_id ν (mem_slitPlane_neg_I_mul hz))
  · exact (by fun_prop : Continuous fun μ : ℂ => exp (I * μ * π / 2)).continuousAt.mul
      (continuousAt_besselK_order (fun μ => μ) continuous_id ν (mem_slitPlane_I_mul hz))

/-- For `z` in the slit plane with `arg z > -π/2`, `-iz` lies in the slit plane. -/
theorem mem_slitPlane_neg_I_mul_of_arg {z : ℂ} (hz : z ∈ slitPlane) (harg : -(π / 2) < arg z) :
    -I * z ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases hre : z.re = 0
  · left
    have him : z.im ≠ 0 := by
      intro h; exact slitPlane_ne_zero hz (Complex.ext hre h)
    have : ¬ z.im < 0 := fun h => by
      rw [arg_eq_neg_pi_div_two_iff.mpr ⟨hre, h⟩] at harg; exact lt_irrefl _ harg
    simp
    exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm him)
  · right; simpa using hre

/-- `H_ν^{(1)}(z) = (2/(πi)) e^{-iνπ/2} K_ν(-iz)` (DLMF 10.27.8) for `-π/2 < arg z < π`;
the boundary ray `arg z = π` is excluded by the principal branches. -/
@[dlmf 10.27.E8]
theorem hankelH1_eq_besselK (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) (harg : -(π / 2) < arg z) :
    hankelH1 ν z = 2 / (π * I) * exp (-(I * ν * π / 2)) * besselK ν (-I * z) := by
  refine eq_of_continuousAt_of_integerComplement (f := fun μ => hankelH1 μ z)
    (g := fun μ => 2 / (π * I) * exp (-(I * μ * π / 2)) * besselK μ (-I * z)) ?_ ?_
    (fun c hc => hankelH1_eq_besselK_of_not_int (forall_of_mem_integerComplement hc)
      (slitPlane_ne_zero hz) harg)
  · exact (continuousAt_besselJ_order (fun μ => μ) continuous_id ν hz).add
      (continuousAt_const.mul (continuousAt_besselY_order (fun μ => μ) continuous_id ν hz))
  · exact (continuousAt_const.mul
      (by fun_prop : Continuous fun μ : ℂ => exp (-(I * μ * π / 2))).continuousAt).mul
      (continuousAt_besselK_order (fun μ => μ) continuous_id ν
        (mem_slitPlane_neg_I_mul_of_arg hz harg))

/-- A unit ray `x ↦ cx` enters the rotated sector filter. -/
theorem tendsto_mul_ofReal_rotSectorAtTop {c : ℂ} (hc : ‖c‖ = 1) {α : ℝ}
    (hre : 1 / 2 ≤ (c * exp (α * I)).re) :
    Tendsto (fun x : ℝ => c * x) atTop (rotSectorAtTop (1 / 2) α) := by
  refine tendsto_comap_iff.mpr
    (tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩)
  · refine tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards [eventually_ge_atTop 0] with x hx
    simp [hc, abs_of_nonneg hx]
  · filter_upwards [eventually_ge_atTop 0] with x hx
    show 1 / 2 * ‖c * (x : ℂ) * exp (α * I)‖ ≤ (c * (x : ℂ) * exp (α * I)).re
    rw [norm_mul, norm_mul, hc, norm_exp_ofReal_mul_I, norm_real, Real.norm_of_nonneg hx,
      show c * (x : ℂ) * exp (α * I) = (x : ℂ) * (c * exp (α * I)) by ring, re_ofReal_mul]
    nlinarith

/-- Leading term of Hankel's expansion of `K_ν` along a ray `w = c x`, `x → +∞`. -/
theorem besselK_ray_isBigO (ν : ℂ) {c : ℂ} (hc : ‖c‖ = 1) {α : ℝ} (hα : |α| < π / 2)
    (hre : 1 / 2 ≤ (c * exp (α * I)).re) :
    (fun x : ℝ => exp (c * x) * besselK ν (c * x) -
      (2 * (c * x)) ^ (-(1 / 2 : ℂ)) * (Real.sqrt π : ℂ)) =O[atTop]
      (fun x : ℝ => x ^ (-(3 / 2) : ℝ)) := by
  have h := (hasAsymptoticExpansion_besselK ν (by norm_num : (0 : ℝ) < 1 / 2) hα
    1).comp_tendsto
    (tendsto_mul_ofReal_rotSectorAtTop hc hre)
  simp only [Finset.sum_range_one, tricomiCoeff, pow_zero, poch_zero, Nat.factorial_zero,
    Nat.cast_one, Nat.cast_zero, zero_add, smul_eq_mul, mul_one, div_one] at h
  refine h.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_gt_atTop 0] with x hx
  have h2 : 2 * (c * (x : ℂ)) ≠ 0 := by
    refine mul_ne_zero two_ne_zero (mul_ne_zero ?_ (ofReal_ne_zero.mpr hx.ne'))
    intro h0; rw [h0, norm_zero] at hc; exact zero_ne_one hc
  rw [Function.comp, norm_cpow_of_ne_zero h2]
  norm_num
  rw [hc, abs_of_pos hx, abs_of_pos (Real.rpow_pos_of_pos hx _), one_mul]
  exact Real.rpow_le_rpow_of_nonpos hx (by linarith) (by norm_num)

/-- The ray `-i x` lies in the sector rotated by `π/4`. -/
theorem half_le_re_neg_I_mul_exp : 1 / 2 ≤ (-I * exp ((π / 4 : ℝ) * I)).re := by
  have h : (-I * exp ((π / 4 : ℝ) * I)).re = Real.sin (π / 4) := by
    simp only [mul_re, neg_re, neg_im, I_re, I_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
    ring
  rw [h, Real.sin_pi_div_four]
  have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num)
  rw [Real.sqrt_one] at this
  linarith

/-- The ray `i x` lies in the sector rotated by `-π/4`. -/
theorem half_le_re_I_mul_exp : 1 / 2 ≤ (I * exp ((-(π / 4) : ℝ) * I)).re := by
  have h : (I * exp ((-(π / 4) : ℝ) * I)).re = Real.sin (π / 4) := by
    simp only [mul_re, I_re, I_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, Real.sin_neg]
    ring
  rw [h, Real.sin_pi_div_four]
  have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num)
  rw [Real.sqrt_one] at this
  linarith

/-- **Hankel's expansion of `H_ν^{(1)}`** on the positive axis (DLMF 10.17.5): with `w = -ix`,
`e^{-ix} H_ν^{(1)}(x) ~ (2/(πi)) e^{-iνπ/2} √π ∑ₖ (-1)^k (ν+½)ₖ (½-ν)ₖ / k! · (2w)^{-k-½}`. -/
@[dlmf 10.17.E5]
theorem hasAsymptoticExpansion_hankelH1 (ν : ℂ) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => (2 * (-I * x)) ^ (-((n : ℂ) + 1 / 2)))
      (fun n => 2 / (π * I) * exp (-(I * ν * π / 2)) *
        ((Real.sqrt π : ℂ) * tricomiCoeff (ν + 1 / 2) (2 * ν + 1) n))
      (fun x : ℝ => exp (-I * x) * hankelH1 ν x) := by
  have hpi := Real.pi_pos
  have h := ((hasAsymptoticExpansion_besselK ν (by norm_num : (0 : ℝ) < 1 / 2) (α := π / 4)
    (by rw [abs_of_pos (by positivity)]; linarith)).comp_tendsto
    (tendsto_mul_ofReal_rotSectorAtTop (c := -I) (by simp) half_le_re_neg_I_mul_exp)).const_smul
    (2 / (π * I) * exp (-(I * ν * π / 2)))
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hs : (x : ℂ) ∈ slitPlane := Or.inl (by simpa using hx)
  have harg : -(π / 2) < arg (x : ℂ) := by
    rw [arg_ofReal_of_nonneg hx.le]; linarith
  simp only [Pi.smul_apply, Function.comp, smul_eq_mul]
  rw [hankelH1_eq_besselK ν hs harg]
  ring

/-- `(2 x e^{iα})^{-1/2} = (2x)^{-1/2} e^{-iα/2}` for `x > 0`, `|α| ≤ π/2`. -/
theorem two_mul_ray_cpow {x : ℝ} (hx : 0 < x) {α : ℝ} (hα : |α| ≤ π / 2) :
    (2 * (exp (α * I) * x)) ^ (-(1 / 2 : ℂ)) =
      ((2 * x : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * exp (-(α * I / 2)) := by
  have h2x : ((2 * x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have harg : arg ((2 * x : ℝ) : ℂ) = 0 := arg_ofReal_of_nonneg (by positivity)
  have hc := cpow_mul_exp_mul_I h2x (α := α)
    (by rw [harg]; linarith [(abs_le.mp hα).1, Real.pi_pos])
    (by rw [harg]; linarith [(abs_le.mp hα).2, Real.pi_pos]) (-(1 / 2 : ℂ))
  rw [show 2 * (exp (α * I) * x) = ((2 * x : ℝ) : ℂ) * exp (α * I) by push_cast; ring, hc]
  congr 2
  ring

/-- `√(2/(πx)) = 2√π/π · (2x)^{-1/2}`. -/
theorem sqrt_two_div_pi_mul {x : ℝ} (hx : 0 < x) :
    (Real.sqrt (2 / (π * x)) : ℂ) =
      2 * (Real.sqrt π : ℂ) / π * ((2 * x : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) := by
  rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (by positivity), Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  have hpi := Real.pi_pos
  have h1 : Real.sqrt (2 / (π * x)) = 2 * Real.sqrt π / π * (Real.sqrt (2 * x))⁻¹ := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    have hs1 := Real.mul_self_sqrt hpi.le
    have hs2 := Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ 2 * x)
    have hs3 : Real.sqrt (2 * x) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp
    nlinarith [hs1, hs2]
  rw [h1]
  push_cast
  ring

/-- **Large-argument behaviour of `J_ν`** (DLMF 10.7.8, leading term of 10.17.3): for every
complex `ν`, `J_ν(x) = √(2/(πx)) cos(x - νπ/2 - π/4) + O(x^{-3/2})` as `x → +∞`. -/
@[dlmf 10.7.E8]
theorem besselJ_sub_cos_isBigO (ν : ℂ) :
    (fun x : ℝ => besselJ ν x -
      (Real.sqrt (2 / (π * x)) : ℂ) * cos (x - ν * π / 2 - π / 4)) =O[atTop]
      (fun x : ℝ => x ^ (-(3 / 2) : ℝ)) := by
  have hpi := Real.pi_pos
  have hm := besselK_ray_isBigO ν (c := -I) (by simp) (α := π / 4)
    (by rw [abs_of_pos (by positivity)]; linarith) half_le_re_neg_I_mul_exp
  have hp := besselK_ray_isBigO ν (c := I) (by simp) (α := -(π / 4))
    (by rw [abs_neg, abs_of_pos (by positivity)]; linarith) half_le_re_I_mul_exp
  have hb (a : ℂ) (s : ℝ) : (fun x : ℝ => a * exp ((s * x : ℝ) * I)) =O[atTop]
      (fun _ => (1 : ℝ)) :=
    IsBigO.of_bound ‖a‖ (Eventually.of_forall fun x => by
      rw [norm_mul, norm_exp_ofReal_mul_I]; simp)
  have hcomb := (((hb (exp (-(I * ν * π / 2))) 1).mul hm).sub
    ((hb (exp (I * ν * π / 2)) (-1)).mul hp)).const_mul_left (1 / (π * I))
  refine hcomb.congr' ?_ (Eventually.of_forall fun x => one_mul _)
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hre : 0 < (x : ℂ).re := by simpa using hx
  rw [besselJ_eq_besselK ν hre]
  have hPm := two_mul_ray_cpow hx (α := -(π / 2)) (by rw [abs_neg, abs_of_pos (by positivity)])
  have hPp := two_mul_ray_cpow hx (α := π / 2) (by rw [abs_of_pos (by positivity)])
  rw [exp_neg_pi_div_two_mul_I'] at hPm
  rw [exp_pi_div_two_mul_I'] at hPp
  rw [hPm, hPp, sqrt_two_div_pi_mul hx]
  have hEE : exp (((1 * x : ℝ) : ℂ) * I) * exp (-I * x) = 1 := by
    rw [← exp_add]; push_cast; ring_nf; exact exp_zero
  have hEE' : exp (((-1 * x : ℝ) : ℂ) * I) * exp (I * x) = 1 := by
    rw [← exp_add]; push_cast; ring_nf; exact exp_zero
  have hI : exp ((π / 2 : ℝ) * I) = I := exp_pi_div_two_mul_I'
  have hA : exp (-(I * ν * π / 2)) * exp (((1 * x : ℝ) : ℂ) * I) *
      exp (-((-(π / 2) : ℝ) * I / 2)) =
      exp ((π / 2 : ℝ) * I) * exp ((x - ν * π / 2 - π / 4) * I) := by
    rw [← exp_add, ← exp_add, ← exp_add]; congr 1; push_cast; ring
  rw [hI] at hA
  have hB : exp (I * ν * π / 2) * exp (((-1 * x : ℝ) : ℂ) * I) *
      exp (-((π / 2 : ℝ) * I / 2)) =
      exp ((-(π / 2) : ℝ) * I) * exp (-(x - ν * π / 2 - π / 4) * I) := by
    rw [← exp_add, ← exp_add, ← exp_add]; congr 1; push_cast; ring
  rw [exp_neg_pi_div_two_mul_I'] at hB
  simp only [cos]
  have hinv : 1 / ((π : ℂ) * I) = -I / π := by
    have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpi.ne'
    field_simp
    rw [I_sq]
    ring
  rw [hinv]
  generalize ((2 * x : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = s at *
  generalize exp (-(I * ν * π / 2)) = a at *
  generalize exp (I * ν * π / 2) = b at *
  generalize exp (((1 * x : ℝ) : ℂ) * I) = E at *
  generalize exp (-I * x) = E2 at *
  generalize exp (((-1 * x : ℝ) : ℂ) * I) = F at *
  generalize exp (I * x) = F2 at *
  generalize exp (-((-(π / 2) : ℝ) * I / 2)) = p at *
  generalize exp (-((π / 2 : ℝ) * I / 2)) = q at *
  generalize besselK ν (-I * x) = Km at *
  generalize besselK ν (I * x) = Kp at *
  generalize exp ((x - ν * π / 2 - π / 4) * I) = T1 at *
  generalize exp (-(x - ν * π / 2 - π / 4) * I) = T2 at *
  have hpi' : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpi.ne'
  field_simp
  linear_combination (-I * a * Km) * hEE - (-I * b * Kp) * hEE' -
    (-I * s * (Real.sqrt π : ℂ)) * hA + (-I * s * (Real.sqrt π : ℂ)) * hB +
    (s * (Real.sqrt π : ℂ) * (T1 + T2)) * I_sq

/-- For real order and positive argument, `J_ν(x)` is real. -/
theorem besselJ_ofReal_eq_re (ν x : ℝ) (hx : 0 < x) :
    besselJ ν x = ((besselJ ν x).re : ℂ) := by
  have h : besselJ ν x = (((x / 2) ^ ν * ∑' n : ℕ, (-(x ^ 2 / 4)) ^ n / n.factorial *
      (Real.Gamma (ν + 1 + n))⁻¹ : ℝ) : ℂ) := by
    rw [besselJ_eq_regularized, regularized0F1_eq_tsum, ofReal_mul, ofReal_cpow (by positivity),
      ofReal_tsum]
    push_cast
    congr 1
    refine tsum_congr fun n => ?_
    rw [← Gamma_ofReal]
    push_cast
    ring_nf
  rw [h, ofReal_re]

/-- The real part of `J_ν` on the positive axis is continuous there. -/
theorem continuousOn_re_besselJ (ν : ℂ) :
    ContinuousOn (fun x : ℝ => (besselJ ν x).re) (Set.Ioi 0) := by
  intro x hx
  have hs : (x : ℂ) ∈ slitPlane := Or.inl (by simpa using hx)
  exact (continuous_re.continuousAt.comp ((hasDerivAt_besselJ (ν := ν) hs).continuousAt.comp
    continuous_ofReal.continuousAt)).continuousWithinAt

/-- Eventually `J_ν` has the sign of `cos(x - νπ/2 - π/4)` wherever that cosine is `±1`. -/
theorem exists_besselJ_sign (ν : ℝ) : ∃ X : ℝ, 0 < X ∧ ∀ x, X ≤ x →
    (Real.cos (x - ν * π / 2 - π / 4) = 1 → 0 < (besselJ ν x).re) ∧
    (Real.cos (x - ν * π / 2 - π / 4) = -1 → (besselJ ν x).re < 0) := by
  obtain ⟨C, hC⟩ := (besselJ_sub_cos_isBigO (ν : ℂ)).bound
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp hC
  have hpi := Real.pi_pos
  have hk : 0 < Real.sqrt (2 / π) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨max (max X0 1) (|C| / Real.sqrt (2 / π) + 1), by positivity, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx0 : 0 < x := by linarith
  have hxC : |C| / Real.sqrt (2 / π) < x := by
    linarith [le_max_right (max X0 1) (|C| / Real.sqrt (2 / π) + 1)]
  have hb := hX0 x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx)
  have hcos : cos ((x : ℂ) - (ν : ℂ) * π / 2 - π / 4) =
      ((Real.cos (x - ν * π / 2 - π / 4) : ℝ) : ℂ) := by push_cast; ring_nf
  rw [besselJ_ofReal_eq_re ν x hx0, hcos, ← ofReal_mul, ← ofReal_sub, norm_real,
    Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hb
  -- the error bound is smaller than the amplitude
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hamp : Real.sqrt (2 / (π * x)) = Real.sqrt (2 / π) / Real.sqrt x := by
    rw [← Real.sqrt_div' _ hx0.le, div_div]
  have hrpow : x ^ (-(3 / 2) : ℝ) = 1 / (x * Real.sqrt x) := by
    rw [Real.rpow_neg hx0.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx0,
      Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]
  have hlt : C * x ^ (-(3 / 2) : ℝ) < Real.sqrt (2 / (π * x)) := by
    rw [hamp, hrpow]
    have h1 : |C| < Real.sqrt (2 / π) * x := by
      rwa [div_lt_iff₀ hk, mul_comm] at hxC
    rw [mul_one_div, div_lt_div_iff₀ (by positivity) hsx]
    have := le_abs_self C
    nlinarith
  constructor
  · intro h1
    rw [h1, mul_one] at hb
    linarith [abs_lt.mp (lt_of_le_of_lt hb hlt)]
  · intro h1
    rw [h1, mul_neg_one, sub_neg_eq_add] at hb
    linarith [abs_lt.mp (lt_of_le_of_lt hb hlt)]

/-- For every real `ν`, `J_ν` has infinitely many positive zeros: by the large-argument
asymptotics it changes sign on each interval `[x_k, x_k + π]` with `x_k = νπ/2 + π/4 + 2kπ`. -/
theorem besselJ_infinite_zeros_of_real (ν : ℝ) :
    Set.Infinite {x : ℝ | 0 < x ∧ besselJ ν x = 0} := by
  obtain ⟨X, hX0, hX⟩ := exists_besselJ_sign ν
  have hpi := Real.pi_pos
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt ((max a X - ν * π / 2 - π / 4) / (2 * π))
  set x := ν * π / 2 + π / 4 + n * (2 * π) with hxdef
  have hxa : max a X < x := by
    rw [div_lt_iff₀ (by positivity)] at hn; linarith
  have hxX : X ≤ x := le_trans (le_max_right _ _) hxa.le
  have hc1 : Real.cos (x - ν * π / 2 - π / 4) = 1 := by
    rw [show x - ν * π / 2 - π / 4 = n * (2 * π) by rw [hxdef]; ring, Real.cos_nat_mul_two_pi]
  have hc2 : Real.cos (x + π - ν * π / 2 - π / 4) = -1 := by
    rw [show x + π - ν * π / 2 - π / 4 = n * (2 * π) + π by rw [hxdef]; ring, Real.cos_add_pi,
      Real.cos_nat_mul_two_pi]
  have hpos := (hX x hxX).1 hc1
  have hneg := (hX (x + π) (by linarith)).2 hc2
  have hx0 : 0 < x := by linarith
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc' (by linarith : x ≤ x + π)
    ((continuousOn_re_besselJ ν).mono fun t ht => show (0 : ℝ) < t by linarith [ht.1])
    ⟨hneg.le, hpos.le⟩
  have hy0' : 0 < y := by linarith [hy.1]
  refine ⟨y, ⟨hy0', ?_⟩, by linarith [hy.1, le_max_left a X]⟩
  rw [besselJ_ofReal_eq_re ν y hy0']
  simp only at hy0
  rw [hy0, ofReal_zero]


/-- `(z^{-ν} J_ν(z))' = -z^{-ν} J_{ν+1}(z)` (DLMF 10.6.6). -/
theorem hasDerivAt_cpow_neg_mul_besselJ (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun w : ℂ => w ^ (-ν) * besselJ ν w) (-((x : ℂ) ^ (-ν) * besselJ (ν + 1) x)) x := by
  have hs : (x : ℂ) ∈ slitPlane := Or.inl (by simpa using hx)
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have h := ((hasDerivAt_id (x : ℂ)).cpow_const (c := -ν) hs).mul (hasDerivAt_besselJ (ν := ν) hs)
  convert h using 1
  · rfl
  simp only [id]
  rw [cpow_sub _ _ hx0, cpow_one]
  field_simp
  ring

/-- `(z^{ν+1} J_{ν+1}(z))' = z^{ν+1} J_ν(z)` (DLMF 10.6.6). -/
theorem hasDerivAt_cpow_mul_besselJ_succ (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun w : ℂ => w ^ (ν + 1) * besselJ (ν + 1) w)
      ((x : ℂ) ^ (ν + 1) * besselJ ν x) x := by
  have hs : (x : ℂ) ∈ slitPlane := Or.inl (by simpa using hx)
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have h := ((hasDerivAt_id (x : ℂ)).cpow_const (c := ν + 1) hs).mul
    (hasDerivAt_besselJ' (ν := ν + 1) hs)
  rw [add_sub_cancel_right] at h
  convert h using 1
  · rfl
  simp only [id]
  rw [cpow_add _ _ hx0, cpow_one]
  field_simp
  ring

/-- Between two positive zeros of `J_ν` lies a zero of `J_{ν+1}` (DLMF 10.21.3). -/
theorem exists_besselJ_succ_zero_between {ν a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hJa : besselJ ν a = 0) (hJb : besselJ ν b = 0) :
    ∃ c ∈ Ioo a b, besselJ ((ν : ℂ) + 1) c = 0 := by
  have hd (x : ℝ) (hx : 0 < x) := (hasDerivAt_cpow_neg_mul_besselJ (ν : ℂ) hx).real_of_complex
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hab
    (fun x hx => (hd x (by linarith [hx.1])).continuousAt.continuousWithinAt)
    (by simp [hJa, hJb]) (fun x hx => hd x (by linarith [hx.1]))
  refine ⟨c, hc, ?_⟩
  have hc' : 0 < c := by linarith [hc.1]
  have hreal := besselJ_ofReal_eq_re (ν + 1) c hc'
  push_cast at hreal
  rw [← ofReal_neg, ← ofReal_cpow hc'.le, neg_re, re_ofReal_mul, neg_eq_zero] at hc0
  rw [hreal, (mul_eq_zero.mp hc0).resolve_left (Real.rpow_pos_of_pos hc' _).ne', ofReal_zero]

/-- Between two positive zeros of `J_{ν+1}` lies a zero of `J_ν` (DLMF 10.21.3). -/
theorem exists_besselJ_zero_between {ν a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hJa : besselJ ((ν : ℂ) + 1) a = 0) (hJb : besselJ ((ν : ℂ) + 1) b = 0) :
    ∃ c ∈ Ioo a b, besselJ ν c = 0 := by
  have hd (x : ℝ) (hx : 0 < x) := (hasDerivAt_cpow_mul_besselJ_succ (ν : ℂ) hx).real_of_complex
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hab
    (fun x hx => (hd x (by linarith [hx.1])).continuousAt.continuousWithinAt)
    (by simp [hJa, hJb]) (fun x hx => hd x (by linarith [hx.1]))
  refine ⟨c, hc, ?_⟩
  have hc' : 0 < c := by linarith [hc.1]
  have hreal := besselJ_ofReal_eq_re ν c hc'
  rw [show (ν : ℂ) + 1 = ((ν + 1 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hc'.le,
    re_ofReal_mul] at hc0
  rw [hreal, (mul_eq_zero.mp hc0).resolve_left (Real.rpow_pos_of_pos hc' _).ne', ofReal_zero]

/-- For real `ν > -1` and `x > 0`, `J_ν(x)` has infinitely many positive zeros (AAR §4.14).
The restriction `ν > -1` is not needed; see `DLMF.Bessel.besselJ_infinite_zeros_of_real`. -/
theorem besselJ_infinite_zeros {ν : ℝ} (_hν : -1 < ν) :
    Set.Infinite {x : ℝ | 0 < x ∧ besselJ ν x = 0} :=
  besselJ_infinite_zeros_of_real ν

end DLMF.Bessel
