/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Struve.Asymptotics.BinomialAndAnger

/-!
# Oscillatory Anger-Weber asymptotic kernels

Trigonometric exponential integrals and their bounds establish the Anger-Weber expansions.

Source references and common attribution are retained in
`DLMF.Struve.Asymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Struve

open DLMF.Bessel DLMF.Airy

/-- `‖sin w‖ ≤ e^{|Im w|}`. -/
theorem struveAs_norm_sin_le (w : ℂ) : ‖sin w‖ ≤ Real.exp |w.im| := by
  have e1 : ‖exp (-w * I)‖ ≤ Real.exp |w.im| := by
    rw [norm_exp]; exact Real.exp_le_exp.2 (by simp [le_abs_self])
  have e2 : ‖exp (w * I)‖ ≤ Real.exp |w.im| := by
    rw [norm_exp]; exact Real.exp_le_exp.2 (by simp [neg_le_abs])
  rw [Complex.sin, norm_div, norm_mul, norm_I, mul_one, Complex.norm_two]
  have := norm_sub_le (exp (-w * I)) (exp (w * I))
  linarith

/-- `‖cos w‖ ≤ e^{|Im w|}`. -/
theorem struveAs_norm_cos_le (w : ℂ) : ‖cos w‖ ≤ Real.exp |w.im| := by
  have e1 : ‖exp (-w * I)‖ ≤ Real.exp |w.im| := by
    rw [norm_exp]; exact Real.exp_le_exp.2 (by simp [le_abs_self])
  have e2 : ‖exp (w * I)‖ ≤ Real.exp |w.im| := by
    rw [norm_exp]; exact Real.exp_le_exp.2 (by simp [neg_le_abs])
  rw [Complex.cos, norm_div, Complex.norm_two]
  have := norm_add_le (exp (w * I)) (exp (-w * I))
  linarith

/-- The two tail bounds behind DLMF 11.11.5 and 11.11.6: for `|ν| ≥ 4` at distance `≥ ε`
from the integers, the normalized series `πν/(2 sin(πν/2)) 𝐒₁` and `π/cos(πν/2) 𝐒₂` agree
with their leading terms up to `K/|ν/2|²`. -/
theorem struveAs_S_tail_bound (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, ∀ ν : ℂ, (∀ n : ℤ, ε ≤ ‖ν - n‖) → 2 ≤ ‖ν / 2‖ →
      ‖π * (ν / 2) / sin (π * (ν / 2)) * angerS1 ν z - 1‖ ≤ K / ‖ν / 2‖ ^ 2 ∧
      ‖ν / 2 * (π / cos (π * (ν / 2)) * angerS2 ν z - (z / 2) ^ (0 + 1) /
          ((1 / 2 : ℂ) ^ 2 - (ν / 2) ^ 2))‖ ≤ K / ‖ν / 2‖ ^ 2 := by
  set c := ‖z / 2‖ ^ 2 * (2 / ε)
  have hE := (Real.summable_pow_div_factorial c).hasSum
  set E := ∑' k : ℕ, c ^ k / (k ! : ℝ)
  have hE0 : 0 ≤ E := tsum_nonneg fun k => by positivity
  refine ⟨4 * ‖z / 2‖ ^ 2 * E + 16 * ‖z / 2‖ ^ 3 * E, fun ν hν hx => ?_⟩
  have hν' : ∀ n : ℤ, ν ≠ n := fun n h => by
    have := hν n; rw [h, sub_self, norm_zero] at this; linarith
  have hx0 : 0 < ‖ν / 2‖ := by linarith
  have hε0 : ε ≠ 0 := hε.ne'
  have h1 := struveAs_hasSum_S1 hν' z
  have h2 := struveAs_hasSum_S2 hν' z
  rw [← hasSum_nat_add_iff' 1] at h1 h2
  have e1 : struveAs_P1 ν 0 = 1 := by simp [struveAs_P1]
  have e2 : struveAs_P2 ν 0 = (1 / 2 : ℂ) ^ 2 - (ν / 2) ^ 2 := by simp [struveAs_P2]
  simp only [Finset.range_one, Finset.sum_singleton, e1, e2, pow_zero, mul_zero, div_one,
    one_mul] at h1 h2
  have hb1 : ∀ k : ℕ, ‖(-1) ^ (k + 1) * (z / 2) ^ (2 * (k + 1)) / struveAs_P1 ν (k + 1)‖ ≤
      4 * ‖z / 2‖ ^ 2 / ‖ν / 2‖ ^ 2 * (c ^ k / k !) := by
    intro k
    have hP := struveAs_P1_tail_ge hε hν hx k
    have hpos : 0 < ‖ν / 2‖ ^ 2 / 4 * ((ε / 2) ^ k * k !) := by positivity
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
    calc ‖z / 2‖ ^ (2 * (k + 1)) / ‖struveAs_P1 ν (k + 1)‖
        ≤ ‖z / 2‖ ^ (2 * (k + 1)) / (‖ν / 2‖ ^ 2 / 4 * ((ε / 2) ^ k * k !)) :=
          div_le_div_of_nonneg_left (by positivity) hpos hP
      _ = _ := by
          simp only [c]
          rw [mul_pow, div_pow, div_pow]
          field_simp
          ring
  have hb2 : ∀ k : ℕ, ‖ν / 2 * ((-1) ^ (k + 1) * (z / 2) ^ (2 * (k + 1) + 1) /
      struveAs_P2 ν (k + 1))‖ ≤ 16 * ‖z / 2‖ ^ 3 / ‖ν / 2‖ ^ 2 * (c ^ k / k !) := by
    intro k
    have hP := struveAs_P2_tail_ge hε hν hx k
    have hpos : 0 < (‖ν / 2‖ ^ 2 / 4) ^ 2 * ((ε / 2) ^ k * k !) := by positivity
    rw [norm_mul (ν / 2), norm_div ((-1 : ℂ) ^ (k + 1) * (z / 2) ^ (2 * (k + 1) + 1)),
      norm_mul ((-1 : ℂ) ^ (k + 1)), norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
    calc ‖ν / 2‖ * (‖z / 2‖ ^ (2 * (k + 1) + 1) / ‖struveAs_P2 ν (k + 1)‖)
        ≤ ‖ν / 2‖ * (‖z / 2‖ ^ (2 * (k + 1) + 1) /
            ((‖ν / 2‖ ^ 2 / 4) ^ 2 * ((ε / 2) ^ k * k !))) := by
          gcongr
      _ = 16 * ‖z / 2‖ ^ 3 / ‖ν / 2‖ ^ 3 * (c ^ k / k !) := by
          have hεk : ε ^ k * ε⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hε0, one_pow]
          simp only [c]
          rw [mul_pow, div_pow, div_pow]
          field_simp
          linear_combination (-(‖z / 2‖ ^ 3 * ‖z / 2‖ ^ (k * 2) * 2 ^ k * 16)) * hεk
      _ ≤ _ := by
          have : ‖ν / 2‖ ^ 2 ≤ ‖ν / 2‖ ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
          exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity)
            (by positivity) this) (by positivity)
  have n1 := h1.norm_le_of_bounded (hE.mul_left (4 * ‖z / 2‖ ^ 2 / ‖ν / 2‖ ^ 2)) hb1
  have n2 := (h2.mul_left (ν / 2)).norm_le_of_bounded
    (hE.mul_left (16 * ‖z / 2‖ ^ 3 / ‖ν / 2‖ ^ 2)) hb2
  have hA : 0 ≤ 4 * ‖z / 2‖ ^ 2 * E := by positivity
  have hB : 0 ≤ 16 * ‖z / 2‖ ^ 3 * E := by positivity
  constructor
  · refine n1.trans ?_
    rw [div_mul_eq_mul_div]
    gcongr
    linarith
  · rw [mul_sub] at n2 ⊢
    refine n2.trans ?_
    rw [div_mul_eq_mul_div]
    gcongr
    linarith

/-- weberE large order, DLMF 11.11.6 with the error term corrected for complex `ν`.

DLMF prints the error as `O(ν⁻²)`, but the remainder inherits the size of `sin²(πν/2)` and
`cos²(πν/2)`, which grow like `e^{π|Im ν|}`: at `z = 1`, `|error|·|ν|²` is about `0.5` for real
`ν` but about `10⁵⁴` at `ν = 1/2 + 40i`. The bound here is `e^{π|Im ν|} ν⁻²`, which is DLMF's
form on the real axis. -/
@[dlmf 11.11.E6 "different convention: error term e^{π|Im ν|} ν⁻², DLMF erratum"]
theorem weberE_large_order (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (fun ν : ℂ => π*ν/2*weberE ν z-(sin (π*ν/2))^2-ν*z/(ν^2-1)*(cos (π*ν/2))^2) =O[nonintegerOrderSector ε] (fun ν : ℂ => (Real.exp (π*|ν.im|) : ℂ)*ν^(-2:ℤ)) := by
  obtain ⟨K, hK⟩ := struveAs_S_tail_bound z hε
  have hev : ∀ᶠ ν : ℂ in nonintegerOrderSector ε, 4 ≤ ‖ν‖ ∧ ∀ n : ℤ, ε ≤ ‖ν - n‖ := by
    rw [nonintegerOrderSector, sector, eventually_inf_principal, eventually_inf_principal]
    exact (tendsto_comap.eventually (eventually_ge_atTop 4)).mono fun ν h4 _ hn => ⟨h4, hn⟩
  refine IsBigO.of_bound (8 * K) ?_
  filter_upwards [hev] with ν hν
  have hx : 2 ≤ ‖ν / 2‖ := by rw [norm_div, Complex.norm_two]; linarith [hν.1]
  have hν0 : 0 < ‖ν‖ := by linarith [hν.1]
  have hν' : ∀ n : ℤ, ν ≠ n := fun n h => by
    have := hν.2 n; rw [h, sub_self, norm_zero] at this; linarith
  obtain ⟨b1, b2⟩ := hK ν hν.2 hx
  have hs : sin (π * ν) ≠ 0 := sin_pi_mul_ne_zero_of_not_int hν'
  have h2 : sin (π * ν) = 2 * sin (π * (ν / 2)) * cos (π * (ν / 2)) := by
    rw [show (π : ℂ) * ν = 2 * (π * (ν / 2)) by ring, Complex.sin_two_mul]
  have hs2 : sin (π * (ν / 2)) ≠ 0 := fun h => hs (by rw [h2, h]; ring)
  have hc2 : cos (π * (ν / 2)) ≠ 0 := fun h => hs (by rw [h2, h]; ring)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hP20 : ((1 / 2 : ℂ)) ^ 2 - (ν / 2) ^ 2 ≠ 0 := by
    have := struveAs_P2_ne_zero hν' 0
    simpa [struveAs_P2] using this
  have hν2 : ν ^ 2 - 1 ≠ 0 := fun h => hP20 (by linear_combination (-1 / 4 : ℂ) * h)
  have hν0' : ν ≠ 0 := fun h => by rw [h] at hν0; simp at hν0
  set s := sin (π * (ν / 2)) with hsd
  set c := cos (π * (ν / 2)) with hcd
  set R1 := π * (ν / 2) / s * angerS1 ν z - 1
  set R2 := ν / 2 * (π / c * angerS2 ν z - (z / 2) ^ (0 + 1) / ((1 / 2 : ℂ) ^ 2 - (ν / 2) ^ 2))
  have hid : π*ν/2*weberE ν z-(sin (π*ν/2))^2-ν*z/(ν^2-1)*(cos (π*ν/2))^2 =
      s ^ 2 * R1 - c ^ 2 * R2 := by
    rw [weberE_series, show (π : ℂ) * ν / 2 = π * (ν / 2) by ring]
    rw [← hsd, ← hcd]
    simp only [R1, R2]
    have h1ν : 1 - ν ^ 2 ≠ 0 := fun h => hν2 (by linear_combination -h)
    clear_value s c
    field_simp
    ring
  rw [hid]
  have hsn : ‖s‖ ^ 2 ≤ Real.exp (π * |ν.im|) := by
    have := struveAs_norm_sin_le (π * (ν / 2))
    have him : |(π * (ν / 2) : ℂ).im| = π * |ν.im| / 2 := by
      simp [abs_mul, abs_of_pos Real.pi_pos, abs_div]; ring
    rw [him] at this
    calc ‖s‖ ^ 2 ≤ Real.exp (π * |ν.im| / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := by rw [← Real.exp_nat_mul]; ring_nf
  have hcn : ‖c‖ ^ 2 ≤ Real.exp (π * |ν.im|) := by
    have := struveAs_norm_cos_le (π * (ν / 2))
    have him : |(π * (ν / 2) : ℂ).im| = π * |ν.im| / 2 := by
      simp [abs_mul, abs_of_pos Real.pi_pos, abs_div]; ring
    rw [him] at this
    calc ‖c‖ ^ 2 ≤ Real.exp (π * |ν.im| / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := by rw [← Real.exp_nat_mul]; ring_nf
  have hK0 : 0 ≤ K := by
    have : 0 ≤ K / ‖ν / 2‖ ^ 2 := (norm_nonneg _).trans b1
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) fun h => by
      nlinarith [h.2, sq_nonneg ‖ν / 2‖]
  have hexp := Real.exp_pos (π * |ν.im|)
  calc ‖s ^ 2 * R1 - c ^ 2 * R2‖ ≤ ‖s‖ ^ 2 * ‖R1‖ + ‖c‖ ^ 2 * ‖R2‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul, norm_pow, norm_pow]
    _ ≤ Real.exp (π * |ν.im|) * (K / ‖ν / 2‖ ^ 2) + Real.exp (π * |ν.im|) * (K / ‖ν / 2‖ ^ 2) := by
        gcongr
    _ = 8 * K * ‖((Real.exp (π*|ν.im|) : ℝ) : ℂ) * ν ^ (-2:ℤ)‖ := by
        rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hexp, norm_zpow, norm_div,
          Complex.norm_two, zpow_neg, zpow_two]
        field_simp
        ring

/-- One integration by parts against `e^{ωθ}` on `[0, π]`. -/
theorem integral_exp_mul_ibp {ω : ℂ} (hω : ω ≠ 0) {H H' : ℝ → ℂ}
    (hd : ∀ θ, HasDerivAt H (H' θ) θ) (hc : Continuous H') :
    (∫ θ : ℝ in 0..π, exp (ω*θ) * H θ) =
      (exp (ω*π) * H π - H 0)/ω - (1/ω) * ∫ θ : ℝ in 0..π, exp (ω*θ) * H' θ := by
  have hv : ∀ θ ∈ uIcc (0:ℝ) π, HasDerivAt (fun θ : ℝ => exp (ω*θ)/ω) (exp (ω*θ)) θ := by
    intro θ _
    have := (((hasDerivAt_id (θ:ℝ)).ofReal_comp.const_mul ω).cexp).div_const ω
    refine this.congr_deriv ?_
    simp only [id, ofReal_one, mul_one]; field_simp
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun θ _ => hd θ) hv
    (hc.intervalIntegrable _ _) ((by fun_prop : Continuous fun θ : ℝ => exp (ω*θ)).intervalIntegrable _ _)
  have e1 : (∫ θ : ℝ in 0..π, exp (ω*θ) * H θ) = ∫ θ : ℝ in 0..π, H θ * exp (ω*θ) :=
    intervalIntegral.integral_congr fun θ _ => by ring
  have e2 : (∫ θ : ℝ in 0..π, H' θ * (exp (ω*θ)/ω)) =
      (1/ω) * ∫ θ : ℝ in 0..π, exp (ω*θ) * H' θ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun θ _ => by ring
  rw [e1, hibp, e2]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  ring

/-- `|∫₀^π e^{itθ} k| ≤ ∫₀^π |k|`. -/
theorem norm_integral_exp_I_mul_le (t : ℝ) (k : ℝ → ℂ) :
    ‖∫ θ : ℝ in 0..π, exp ((I*t)*θ) * k θ‖ ≤ ∫ θ : ℝ in 0..π, ‖k θ‖ := by
  refine (intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le).trans ?_
  refine le_of_eq (intervalIntegral.integral_congr fun θ _ => ?_)
  simp only [norm_mul]
  rw [show (I*t)*(θ:ℂ) = ((t*θ:ℝ):ℂ)*I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Derivatives of `θ ↦ exp (a sin θ)`. -/
theorem hasDerivAt_exp_mul_sin (a : ℂ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => exp (a*Real.sin θ)) (a*Real.cos θ*exp (a*Real.sin θ)) θ := by
  have := ((Real.hasDerivAt_sin θ).ofReal_comp.const_mul a).cexp
  convert this using 1; ring

/-- At `θ`, the function `(fun θ : ℝ => a*Real.cos θ*exp (a*Real.sin θ))` has derivative
`((a^2*(Real.cos θ)^2 - a*Real.sin θ)*exp (a*Real.sin θ))`. -/
theorem hasDerivAt_exp_mul_sin_one (a : ℂ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => a*Real.cos θ*exp (a*Real.sin θ))
      ((a^2*(Real.cos θ)^2 - a*Real.sin θ)*exp (a*Real.sin θ)) θ := by
  have h1 := ((Real.hasDerivAt_cos θ).ofReal_comp.const_mul a).mul (hasDerivAt_exp_mul_sin a θ)
  convert h1 using 1; push_cast; ring

/-- At `θ`, the function `(fun θ : ℝ => (a^2*(Real.cos θ)^2 - a*Real.sin θ)*exp (a*Real.sin θ))`
has derivative `((a^3*(Real.cos θ)^3 - 3*a^2*Real.sin θ*Real.cos θ - a*Real.cos θ)*exp
(a*Real.sin θ))`. -/
theorem hasDerivAt_exp_mul_sin_two (a : ℂ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => (a^2*(Real.cos θ)^2 - a*Real.sin θ)*exp (a*Real.sin θ))
      ((a^3*(Real.cos θ)^3 - 3*a^2*Real.sin θ*Real.cos θ - a*Real.cos θ)*exp (a*Real.sin θ)) θ := by
  have hc := (Real.hasDerivAt_cos θ).ofReal_comp
  have hs := (Real.hasDerivAt_sin θ).ofReal_comp
  have h1 := (((hc.pow 2).const_mul (a^2)).sub (hs.const_mul a)).mul (hasDerivAt_exp_mul_sin a θ)
  convert h1 using 1
  simp only [Pi.sub_apply, Pi.pow_apply]; push_cast; ring

/-- Identity under the stated parameter and domain assumptions: `(∫ θ : ℝ in 0..π, exp (ω*θ) * exp
(a*Real.sin θ)) = -2/ω + (1/ω^2) * ∫ θ : ℝ in 0..π, exp (ω*θ) * ((a^2*(Real.cos θ)^2 -
a*Real.sin θ)*exp (a*Real.sin θ))`. -/
theorem integral_exp_mul_exp_sin_odd {ω : ℂ} (hω : ω ≠ 0) (he : exp (ω*π) = -1) (a : ℂ) :
    (∫ θ : ℝ in 0..π, exp (ω*θ) * exp (a*Real.sin θ)) = -2/ω + (1/ω^2) *
      ∫ θ : ℝ in 0..π, exp (ω*θ) * ((a^2*(Real.cos θ)^2 - a*Real.sin θ)*exp (a*Real.sin θ)) := by
  rw [integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin a) (by fun_prop),
    integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin_one a) (by fun_prop), he]
  simp only [Real.sin_pi, Real.cos_pi, Real.sin_zero, Real.cos_zero, ofReal_zero, ofReal_one,
    ofReal_neg, mul_zero, Complex.exp_zero, mul_one]
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `(∫ θ : ℝ in 0..π, exp (ω*θ) * exp
(a*Real.sin θ)) = 2*a/ω^2 - (1/ω^3) * ∫ θ : ℝ in 0..π, exp (ω*θ) * ((a^3*(Real.cos θ)^3 -
3*a^2*Real.sin θ*Real.cos θ - a*Real.cos θ)*exp (a*Real.sin θ))`. -/
theorem integral_exp_mul_exp_sin_even {ω : ℂ} (hω : ω ≠ 0) (he : exp (ω*π) = 1) (a : ℂ) :
    (∫ θ : ℝ in 0..π, exp (ω*θ) * exp (a*Real.sin θ)) = 2*a/ω^2 - (1/ω^3) *
      ∫ θ : ℝ in 0..π, exp (ω*θ) * ((a^3*(Real.cos θ)^3 - 3*a^2*Real.sin θ*Real.cos θ -
        a*Real.cos θ)*exp (a*Real.sin θ)) := by
  rw [integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin a) (by fun_prop),
    integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin_one a) (by fun_prop),
    integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin_two a) (by fun_prop), he]
  simp only [Real.sin_pi, Real.cos_pi, Real.sin_zero, Real.cos_zero, ofReal_zero, ofReal_one,
    ofReal_neg, mul_zero, Complex.exp_zero, mul_one]
  field_simp
  ring

/-- The Weber function as a combination of two exponential integrals. -/
theorem weberE_eq_exp_integrals (ν z : ℂ) :
    weberE ν z = 1/π * (I/2 * ((∫ θ : ℝ in 0..π, exp ((-I*ν)*θ) * exp ((I*z)*Real.sin θ)) -
      ∫ θ : ℝ in 0..π, exp ((I*ν)*θ) * exp ((-I*z)*Real.sin θ))) := by
  unfold weberE
  congr 1
  rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [Complex.sin, ← Complex.exp_add, ← Complex.exp_add]
  ring_nf

/-- A uniform bound for an integral against `e^{itθ}`. -/
theorem norm_integral_exp_I_mul_le_const (t : ℝ) {k : ℝ → ℂ} {C : ℝ}
    (hk : ∀ θ, ‖k θ‖ ≤ C) :
    ‖∫ θ : ℝ in 0..π, exp ((I*t)*θ) * k θ‖ ≤ C * π := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π)
    (f := fun θ : ℝ => exp ((I*t)*θ) * k θ) (C := C) (fun θ _ => by
      rw [norm_mul, show (I*t)*(θ:ℂ) = ((t*θ:ℝ):ℂ)*I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, one_mul]; exact hk θ)
  rwa [sub_zero, abs_of_pos Real.pi_pos] at this

/-- Identity under the stated parameter and domain assumptions: `exp ((I*(2*n+1:ℂ))*π) = -1`. -/
theorem exp_I_mul_odd_mul_pi (n : ℤ) : exp ((I*(2*n+1:ℂ))*π) = -1 := by
  rw [show (I*(2*n+1:ℂ))*π = n*(2*π*I) + π*I by ring, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]

/-- Identity under the stated parameter and domain assumptions: `exp ((I*(2*n:ℂ))*π) = 1`. -/
theorem exp_I_mul_even_mul_pi (n : ℤ) : exp ((I*(2*n:ℂ))*π) = 1 := by
  rw [show (I*(2*n:ℂ))*π = n*(2*π*I) by ring, Complex.exp_int_mul_two_pi_mul_I]

/-- Identity under the stated parameter and domain assumptions: `exp ((-I*(2*n+1:ℂ))*π) = -1`. -/
theorem exp_neg_I_mul_odd_mul_pi (n : ℤ) : exp ((-I*(2*n+1:ℂ))*π) = -1 := by
  have := exp_I_mul_odd_mul_pi (-n-1)
  rw [← this]; congr 1; push_cast; ring

/-- Identity under the stated parameter and domain assumptions: `exp ((-I*(2*n:ℂ))*π) = 1`. -/
theorem exp_neg_I_mul_even_mul_pi (n : ℤ) : exp ((-I*(2*n:ℂ))*π) = 1 := by
  have := exp_I_mul_even_mul_pi (-n)
  rw [← this]; congr 1; push_cast; ring

/-- `E_{2n+1}(z) = 2/((2n+1)π) + O((2n+1)^{-2})`, uniformly in `n`. -/
theorem weberE_odd_bound (z : ℂ) : ∃ M : ℝ, ∀ n : ℤ,
    ‖weberE (2*n+1) z - 2/((2*n+1:ℂ)*π)‖ ≤ M / ((2*n+1:ℝ))^2 := by
  set K : ℝ := (‖z‖^2 + ‖z‖) * Real.exp ‖z‖
  have hH2 : ∀ a : ℂ, ‖a‖ = ‖z‖ → ∀ θ : ℝ,
      ‖(a^2*(Real.cos θ)^2 - a*Real.sin θ)*exp (a*Real.sin θ)‖ ≤ K := by
    intro a ha θ
    rw [norm_mul, Complex.norm_exp]
    have hc := Real.abs_cos_le_one θ
    have hs := Real.abs_sin_le_one θ
    have h1 : ‖a^2*(Real.cos θ:ℂ)^2 - a*Real.sin θ‖ ≤ ‖z‖^2 + ‖z‖ := by
      refine (norm_sub_le _ _).trans ?_
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, ha]
      have : |Real.cos θ|^2 ≤ 1 := by nlinarith [abs_nonneg (Real.cos θ)]
      have hz := norm_nonneg z
      nlinarith [abs_nonneg (Real.sin θ)]
    have h2 : Real.exp (a*Real.sin θ).re ≤ Real.exp ‖z‖ := by
      apply Real.exp_le_exp.2
      calc (a*Real.sin θ).re ≤ ‖a*Real.sin θ‖ := re_le_norm _
        _ = ‖a‖ * |Real.sin θ| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ‖z‖ := by rw [ha]; nlinarith [norm_nonneg z, abs_nonneg (Real.sin θ)]
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
  refine ⟨K * π / π, fun n => ?_⟩
  set t : ℝ := 2*n+1
  have ht : (2*n+1:ℂ) = t := by simp [t]
  have ht0 : t ≠ 0 := by
    intro h
    have h' : ((2*n+1 : ℤ) : ℝ) = 0 := by push_cast; exact h
    have : (2*n+1 : ℤ) = 0 := by exact_mod_cast h'
    omega
  have htc : (t:ℂ) ≠ 0 := ofReal_ne_zero.2 ht0
  have hω1 : -I*(2*n+1:ℂ) ≠ 0 := by rw [ht]; simp [htc]
  have hω2 : I*(2*n+1:ℂ) ≠ 0 := by rw [ht]; simp [htc]
  rw [weberE_eq_exp_integrals,
    integral_exp_mul_exp_sin_odd hω1 (exp_neg_I_mul_odd_mul_pi n),
    integral_exp_mul_exp_sin_odd hω2 (exp_I_mul_odd_mul_pi n)]
  set R1 := ∫ θ : ℝ in 0..π, exp ((-I*(2*n+1:ℂ))*θ) *
    (((I*z)^2*(Real.cos θ)^2 - (I*z)*Real.sin θ)*exp ((I*z)*Real.sin θ))
  set R2 := ∫ θ : ℝ in 0..π, exp ((I*(2*n+1:ℂ))*θ) *
    (((-I*z)^2*(Real.cos θ)^2 - (-I*z)*Real.sin θ)*exp ((-I*z)*Real.sin θ))
  have hR1 : ‖R1‖ ≤ K * π := by
    have h := norm_integral_exp_I_mul_le_const (-t) (hH2 (I*z) (by simp))
    simp only [R1]; convert h using 4; push_cast [ht]; ring_nf
  have hR2 : ‖R2‖ ≤ K * π := by
    have h := norm_integral_exp_I_mul_le_const t (hH2 (-I*z) (by simp))
    simp only [R2]; convert h using 4; push_cast [ht]; ring_nf
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have key : 1/π * (I/2 * ((-2/(-I*(2*n+1:ℂ)) + 1/(-I*(2*n+1:ℂ))^2 * R1) -
      (-2/(I*(2*n+1:ℂ)) + 1/(I*(2*n+1:ℂ))^2 * R2))) - 2/((2*n+1:ℂ)*π) =
      (I/(2*π)) * (R2 - R1) / (t:ℂ)^2 := by
    rw [ht]
    field_simp
    ring_nf
    rw [I_sq]
    ring_nf
  rw [key, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hI : ‖I/(2*(π:ℂ))‖ = 1/(2*π) := by
    rw [norm_div, Complex.norm_I, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [hI]
  have hsum : ‖R2 - R1‖ ≤ 2*(K*π) := (norm_sub_le _ _).trans (by linarith)
  have ht2 : 0 < t^2 := by positivity
  rw [div_le_div_iff_of_pos_right ht2]
  calc 1/(2*π) * ‖R2 - R1‖ ≤ 1/(2*π) * (2*(K*π)) := by gcongr
    _ = K * π / π := by field_simp

/-- `|2n+1| ≥ |n|` and `|2n| ≥ |n|` in real form. -/
theorem abs_two_mul_add_ge (n : ℤ) (e : ℝ) (he : e = 0 ∨ e = 1) :
    (|n| : ℝ) ≤ |2*(n:ℝ)+e| ∨ n = 0 := by
  rcases eq_or_ne n 0 with h | h
  · exact Or.inr h
  left
  have h1 : (1:ℝ) ≤ |(n:ℝ)| := by
    have : (1:ℤ) ≤ |n| := Int.one_le_abs h
    exact_mod_cast this
  rcases he with rfl | rfl
  · rw [add_zero, abs_mul]; norm_num; linarith [abs_nonneg (n:ℝ)]
  · have := abs_sub_abs_le_abs_sub (2*(n:ℝ)) (-1)
    rw [abs_mul, abs_two, abs_neg, abs_one, sub_neg_eq_add] at this
    linarith

/-- Estimate under the stated parameter and domain assumptions: `‖A - B - C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖`. -/
theorem norm_sub_sub_le_add_add (A B C : ℂ) : ‖A - B - C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ :=
  (norm_sub_le _ _).trans (by linarith [norm_sub_le A B])

/-- `E_{2n}(z) = 2z/(π(2n)²) + O(|z| (2n)^{-3})`, uniformly in `n ≠ 0`. -/
theorem weberE_even_bound (z : ℂ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℤ, n ≠ 0 →
    ‖weberE (2*n) z - 2*z/(π*(2*n:ℂ)^2)‖ ≤ ‖z‖ * K / |(2*n:ℝ)|^3 := by
  set K0 : ℝ := (‖z‖^2 + 3*‖z‖ + 1) * Real.exp ‖z‖
  have hK0 : 0 ≤ K0 := by positivity
  have hH3 : ∀ a : ℂ, ‖a‖ = ‖z‖ → ∀ θ : ℝ,
      ‖(a^3*(Real.cos θ)^3 - 3*a^2*Real.sin θ*Real.cos θ - a*Real.cos θ)*exp (a*Real.sin θ)‖ ≤
        ‖z‖ * K0 := by
    intro a ha θ
    rw [norm_mul, Complex.norm_exp]
    have hc := Real.abs_cos_le_one θ
    have hs := Real.abs_sin_le_one θ
    have hz := norm_nonneg z
    have h1 : ‖a^3*(Real.cos θ:ℂ)^3 - 3*a^2*Real.sin θ*Real.cos θ - a*Real.cos θ‖ ≤
        ‖z‖^3 + 3*‖z‖^2 + ‖z‖ := by
      refine (norm_sub_sub_le_add_add _ _ _).trans ?_
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, ha, Complex.norm_ofNat]
      have hc3 : |Real.cos θ|^3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hc
      have hsc : |Real.sin θ| * |Real.cos θ| ≤ 1 := by
        nlinarith [abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ)]
      have e1 : ‖z‖^3 * |Real.cos θ|^3 ≤ ‖z‖^3 := by
        calc _ ≤ ‖z‖^3 * 1 := by gcongr
          _ = _ := mul_one _
      have e2 : 3 * ‖z‖^2 * |Real.sin θ| * |Real.cos θ| ≤ 3*‖z‖^2 := by
        calc _ = 3 * ‖z‖^2 * (|Real.sin θ| * |Real.cos θ|) := by ring
          _ ≤ 3 * ‖z‖^2 * 1 := by gcongr
          _ = _ := mul_one _
      have e3 : ‖z‖ * |Real.cos θ| ≤ ‖z‖ := by
        calc _ ≤ ‖z‖ * 1 := by gcongr
          _ = _ := mul_one _
      linarith
    have h2 : Real.exp (a*Real.sin θ).re ≤ Real.exp ‖z‖ := by
      apply Real.exp_le_exp.2
      calc (a*Real.sin θ).re ≤ ‖a*Real.sin θ‖ := re_le_norm _
        _ = ‖a‖ * |Real.sin θ| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ‖z‖ := by rw [ha]; nlinarith [norm_nonneg z, abs_nonneg (Real.sin θ)]
    calc _ ≤ (‖z‖^3 + 3*‖z‖^2 + ‖z‖) * Real.exp ‖z‖ :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ = ‖z‖ * K0 := by simp only [K0]; ring
  refine ⟨K0, hK0, fun n hn => ?_⟩
  set t : ℝ := 2*n
  have ht : (2*n:ℂ) = t := by simp [t]
  have ht0 : t ≠ 0 := by
    intro h
    have h' : ((2*n : ℤ) : ℝ) = 0 := by push_cast; exact h
    have : (2*n : ℤ) = 0 := by exact_mod_cast h'
    omega
  have htc : (t:ℂ) ≠ 0 := ofReal_ne_zero.2 ht0
  have hω1 : -I*(2*n:ℂ) ≠ 0 := by rw [ht]; simp [htc]
  have hω2 : I*(2*n:ℂ) ≠ 0 := by rw [ht]; simp [htc]
  rw [weberE_eq_exp_integrals,
    integral_exp_mul_exp_sin_even hω1 (exp_neg_I_mul_even_mul_pi n),
    integral_exp_mul_exp_sin_even hω2 (exp_I_mul_even_mul_pi n)]
  set R1 := ∫ θ : ℝ in 0..π, exp ((-I*(2*n:ℂ))*θ) *
    (((I*z)^3*(Real.cos θ)^3 - 3*(I*z)^2*Real.sin θ*Real.cos θ - (I*z)*Real.cos θ)*
      exp ((I*z)*Real.sin θ))
  set R2 := ∫ θ : ℝ in 0..π, exp ((I*(2*n:ℂ))*θ) *
    (((-I*z)^3*(Real.cos θ)^3 - 3*(-I*z)^2*Real.sin θ*Real.cos θ - (-I*z)*Real.cos θ)*
      exp ((-I*z)*Real.sin θ))
  have hR1 : ‖R1‖ ≤ ‖z‖ * K0 * π := by
    have h := norm_integral_exp_I_mul_le_const (-t) (hH3 (I*z) (by simp))
    simp only [R1]; convert h using 4; push_cast [ht]; ring_nf
  have hR2 : ‖R2‖ ≤ ‖z‖ * K0 * π := by
    have h := norm_integral_exp_I_mul_le_const t (hH3 (-I*z) (by simp))
    simp only [R2]; convert h using 4; push_cast [ht]; ring_nf
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have key : 1/π * (I/2 * ((2*(I*z)/(-I*(2*n:ℂ))^2 - 1/(-I*(2*n:ℂ))^3 * R1) -
      (2*(-I*z)/(I*(2*n:ℂ))^2 - 1/(I*(2*n:ℂ))^3 * R2))) - 2*z/(π*(2*n:ℂ)^2) =
      -(R1 + R2) / (2*π*(t:ℂ)^3) := by
    rw [ht]
    have e1 : (-I*(t:ℂ))^2 = -(t:ℂ)^2 := by linear_combination (t:ℂ)^2 * I_sq
    have e2 : (I*(t:ℂ))^2 = -(t:ℂ)^2 := by linear_combination (t:ℂ)^2 * I_sq
    have e3 : (-I*(t:ℂ))^3 = I*(t:ℂ)^3 := by linear_combination (-I*(t:ℂ)^3) * I_sq
    have e4 : (I*(t:ℂ))^3 = -(I*(t:ℂ)^3) := by linear_combination (I*(t:ℂ)^3) * I_sq
    rw [e1, e2, e3, e4]
    field_simp
    ring_nf
    simp only [I_sq]
    ring_nf
  rw [key]
  simp only [norm_div, norm_neg, norm_mul, norm_pow, Complex.norm_real, Complex.norm_ofNat,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hsum : ‖R1 + R2‖ ≤ 2*(‖z‖ * K0 * π) := (norm_add_le _ _).trans (by linarith)
  have ht3 : 0 < |t|^3 := by positivity
  rw [div_le_div_iff₀ (by positivity) ht3]
  nlinarith [Real.pi_pos]

/-- Identity under the stated parameter and domain assumptions: `(fun n : ℤ => weberE (2*n+0) z)
~[comap (fun n : ℤ => |n|) atTop] (fun n => 2*z/((4*(n:ℂ)^2-1)*π))`. -/
@[dlmf 11.11.E7]
theorem weberE_large_integer_0 (z : ℂ) :
    (fun n : ℤ => weberE (2*n+0) z) ~[comap (fun n : ℤ => |n|) atTop] (fun n => 2*z/((4*(n:ℂ)^2-1)*π)) := by
  obtain ⟨K, hK, hb⟩ := weberE_even_bound z
  unfold IsEquivalent
  rw [isLittleO_iff]
  intro c hc
  obtain ⟨N, hN⟩ := exists_nat_ge (2/c + K*π/c + 1)
  have hev : ∀ᶠ n : ℤ in comap (fun n : ℤ => |n|) atTop, (N:ℤ) ≤ |n| :=
    tendsto_comap.eventually (eventually_ge_atTop (N:ℤ))
  filter_upwards [hev] with n hn
  have hnR : (N:ℝ) ≤ |(n:ℝ)| := by
    have : ((N:ℤ):ℝ) ≤ ((|n|:ℤ):ℝ) := by exact_mod_cast hn
    simpa [Int.cast_abs] using this
  have h2c : 0 ≤ 2/c := by positivity
  have hKc : 0 ≤ K*π/c := by positivity
  have hn1 : (1:ℝ) ≤ |(n:ℝ)| := by linarith
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn1; linarith
  set t : ℝ := 2*n
  set x : ℝ := |t|
  have hx : x = 2*|(n:ℝ)| := by simp only [x, t, abs_mul, abs_two]
  have hx2 : 2 ≤ x := by linarith
  have hxN : (N:ℝ) ≤ x := by linarith
  have hxc : 2/c ≤ x := by linarith
  have hxK : K*π/c ≤ x := by linarith
  have ht : (2*n:ℂ) = t := by simp [t]
  have htx : t^2 = x^2 := (sq_abs t).symm
  have hx0 : 0 < x := by linarith
  have hx21 : 0 < x^2 - 1 := by nlinarith
  rw [Pi.sub_apply, add_zero]
  set u := weberE (2*n) z
  set w : ℂ := 2*z/(π*(2*n:ℂ)^2)
  set v : ℂ := 2*z/((4*(n:ℂ)^2-1)*π)
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have htc : (t:ℂ) ≠ 0 := ofReal_ne_zero.2 fun h => by
    have : x = 0 := by simp only [x, h, abs_zero]
    linarith
  have hn4 : (4*(n:ℂ)^2-1) = ((x^2-1:ℝ):ℂ) := by
    rw [← htx]; push_cast [t]; ring
  have hn4ne : (4*(n:ℂ)^2-1) ≠ 0 := by rw [hn4]; exact ofReal_ne_zero.2 hx21.ne'
  have hwv : w - v = -(2*z) / (π*(t:ℂ)^2*((x^2-1:ℝ):ℂ)) := by
    simp only [w, v]
    rw [ht, hn4]
    have : ((x^2-1:ℝ):ℂ) = (t:ℂ)^2 - 1 := by push_cast [← htx]; ring
    have h1 : ((x^2-1:ℝ):ℂ) ≠ 0 := ofReal_ne_zero.2 hx21.ne'
    rw [this] at h1 ⊢
    field_simp
    ring
  have hnv : ‖v‖ = 2*‖z‖/((x^2-1)*π) := by
    simp only [v]
    rw [hn4, norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg hx21.le, Real.norm_of_nonneg Real.pi_pos.le]
  have hnwv : ‖w - v‖ = 2*‖z‖/(π*x^2*(x^2-1)) := by
    rw [hwv, norm_div, norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Complex.norm_real, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hx21.le, Real.norm_of_nonneg Real.pi_pos.le, Real.norm_eq_abs]
  have huw : ‖u - w‖ ≤ ‖z‖ * K / x^3 := hb n hn0
  have htri : ‖u - v‖ ≤ ‖u - w‖ + ‖w - v‖ := by
    have := norm_add_le (u - w) (w - v); rwa [sub_add_sub_cancel] at this
  rw [hnv]
  refine htri.trans ?_
  rw [hnwv]
  have hzn := norm_nonneg z
  have e1 : K / x^3 ≤ c/((x^2-1)*π) := by
    have ha : K / x^3 ≤ c/(x^2*π) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : K*π ≤ c*x := by rwa [div_le_iff₀ hc, mul_comm x] at hxK
      nlinarith [sq_nonneg x]
    refine ha.trans (div_le_div_of_nonneg_left hc.le (by positivity) ?_)
    nlinarith [Real.pi_pos]
  have e2 : 2/(π*x^2*(x^2-1)) ≤ c/((x^2-1)*π) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 2 ≤ c*x := by rwa [div_le_iff₀ hc, mul_comm x] at hxc
    have : 2 ≤ c*x^2 := by nlinarith
    have hp : 0 < (x^2-1)*π := by positivity
    nlinarith
  refine (add_le_add huw le_rfl).trans ?_
  calc ‖z‖ * K / x^3 + 2*‖z‖/(π*x^2*(x^2-1)) = ‖z‖ * (K/x^3 + 2/(π*x^2*(x^2-1))) := by ring
    _ ≤ ‖z‖ * (c/((x^2-1)*π) + c/((x^2-1)*π)) := by gcongr
    _ = c * (2*‖z‖/((x^2-1)*π)) := by ring

/-- Identity under the stated parameter and domain assumptions: `(fun n : ℤ => weberE (2*n+1) z)
~[comap (fun n : ℤ => |n|) atTop] (fun n => 2/((2*n+1:ℂ)*π))`. -/
@[dlmf 11.11.E7]
theorem weberE_large_integer_1 (z : ℂ) :
    (fun n : ℤ => weberE (2*n+1) z) ~[comap (fun n : ℤ => |n|) atTop] (fun n => 2/((2*n+1:ℂ)*π)) := by
  obtain ⟨M, hM⟩ := weberE_odd_bound z
  unfold IsEquivalent
  rw [isLittleO_iff]
  intro c hc
  obtain ⟨N, hN⟩ := exists_nat_ge (M * π / (2*c) + 1)
  have hev : ∀ᶠ n : ℤ in comap (fun n : ℤ => |n|) atTop, (N:ℤ) ≤ |n| :=
    tendsto_comap.eventually (eventually_ge_atTop (N:ℤ))
  filter_upwards [hev] with n hn
  have hnR : (N:ℝ) ≤ |(n:ℝ)| := by
    have : ((N:ℤ):ℝ) ≤ ((|n|:ℤ):ℝ) := by exact_mod_cast hn
    simpa [Int.cast_abs] using this
  set t : ℝ := 2*n+1
  have ht : (2*n+1:ℂ) = t := by simp [t]
  have ht0 : t ≠ 0 := by
    intro h
    have h' : ((2*n+1 : ℤ) : ℝ) = 0 := by push_cast; exact h
    have : (2*n+1 : ℤ) = 0 := by exact_mod_cast h'
    omega
  have htabs : M * π / (2*c) ≤ |t| := by
    rcases abs_two_mul_add_ge n 1 (Or.inr rfl) with h | h
    · linarith
    · subst h
      simp only [Int.cast_zero, abs_zero, mul_zero, zero_add, abs_one, t] at hnR ⊢
      have : (N:ℝ) ≤ 0 := hnR
      linarith
  have htpos : 0 < |t| := abs_pos.2 ht0
  have hv : ‖(2:ℂ)/((2*n+1:ℂ)*π)‖ = 2/(|t| * π) := by
    rw [ht, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_ofNat,
      Real.norm_eq_abs, Real.norm_of_nonneg Real.pi_pos.le]
  rw [hv, Pi.sub_apply]
  refine (hM n).trans ?_
  have hMle : M * π ≤ 2*c*|t| := by
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 2*c)).1 htabs
    linarith
  rw [← sq_abs t, div_le_iff₀ (by positivity)]
  have : c * (2 / (|t| * π)) * |t|^2 = 2*c*|t|/π := by field_simp
  rw [this, le_div_iff₀ Real.pi_pos]
  linarith

/-- Coefficients in the scaled Anger–Weber expansion. -/
def angerScaledA : ℕ → ℂ → ℂ
  | 0 => fun lam => 1/(1+lam)
  | k+1 => fun lam => limUnder (𝓝[≠] lam) (fun l : ℂ => l/(1-l^2)*(l*iteratedDeriv 2 (angerScaledA k) l+deriv (angerScaledA k) l)/((2*k+1:ℂ)*(2*k+2)))

/-- Derivative of a quadratic divided by a power of `1 + l`. -/
theorem hasDerivAt_quadratic_div_pow (a b c : ℂ) (n : ℕ) {l : ℂ} (hl : 1+l ≠ 0) :
    HasDerivAt (fun l => (a*l^2+b*l+c)/(1+l)^(n+1))
      (((2*a*l+b)*(1+l)-(n+1)*(a*l^2+b*l+c))/(1+l)^(n+2)) l := by
  have hp : HasDerivAt (fun l : ℂ => a*l^2+b*l+c) (2*a*l+b) l := by
    convert (((hasDerivAt_pow 2 l).const_mul a).add ((hasDerivAt_id' l).const_mul b)).add_const c
      using 1
    simp; ring
  have hq : HasDerivAt (fun l : ℂ => (1+l)^(n+1)) ((n+1)*(1+l)^n) l := by
    convert ((hasDerivAt_id' l).const_add 1).pow (n+1) using 1
    simp
  convert hp.div hq (pow_ne_zero _ hl) using 1
  field_simp
  ring

/-- One step of the recursion for `angerScaledA`: if the `k`-th coefficient agrees with `g`
off `l = -1`, with derivatives `d`, `e`, then the removable limit defining the next
coefficient is the continuous closed form `G`. -/
theorem angerScaledA_succ_eq (k : ℕ) {g d e G : ℂ → ℂ}
    (hA : ∀ l, 1+l ≠ 0 → angerScaledA k l = g l)
    (hd : ∀ l, 1+l ≠ 0 → HasDerivAt g (d l) l)
    (he : ∀ l, 1+l ≠ 0 → HasDerivAt d (e l) l)
    (halg : ∀ l, 1+l ≠ 0 → l ≠ 1 → l/(1-l^2)*(l*e l+d l)/((2*k+1:ℂ)*(2*k+2)) = G l)
    (hG : ∀ l, 1+l ≠ 0 → ContinuousAt G l) {lam : ℂ} (hlam : 1+lam ≠ 0) :
    angerScaledA (k+1) lam = G lam := by
  have hU : IsOpen {l : ℂ | 1+l ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
  have hAd : ∀ l, 1+l ≠ 0 → HasDerivAt (angerScaledA k) (d l) l := fun l hl =>
    (hd l hl).congr_of_eventuallyEq (by
      filter_upwards [hU.mem_nhds hl] with x hx using hA x hx)
  have hAe : ∀ l, 1+l ≠ 0 → iteratedDeriv 2 (angerScaledA k) l = e l := by
    intro l hl
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    refine ((he l hl).congr_of_eventuallyEq ?_).deriv
    filter_upwards [hU.mem_nhds hl] with x hx using (hAd x hx).deriv
  have hev : ∀ᶠ l in 𝓝[≠] lam, 1+l ≠ 0 ∧ l ≠ 1 := by
    refine Filter.Eventually.and (nhdsWithin_le_nhds (hU.mem_nhds hlam) :
      ∀ᶠ l in 𝓝[≠] lam, 1+l ≠ 0) ?_
    by_cases h1 : lam = 1
    · subst h1; exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (eventually_ne_nhds h1)
  show limUnder _ _ = _
  refine (((hG lam hlam).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_).limUnder_eq
  filter_upwards [hev] with l hl
  rw [hAe l hl.1, (hAd l hl.1).deriv, halg l hl.1 hl.2]

/-- Identity under the stated parameter and domain assumptions: `angerScaledA 1 lam =
-lam/(2*(1+lam)^4) ∧ angerScaledA 2 lam = (9*lam^2-lam)/(24*(1+lam)^7) ∧ angerScaledA 3 lam =
-(225*lam^3-54*lam^2+lam)/(720*(1+lam)^10)`. -/
@[dlmf 11.11.E9]
theorem angerScaledA_initial (lam : ℂ) (h : lam ≠ -1) :
    angerScaledA 1 lam = -lam/(2*(1+lam)^4) ∧ angerScaledA 2 lam = (9*lam^2-lam)/(24*(1+lam)^7) ∧ angerScaledA 3 lam = -(225*lam^3-54*lam^2+lam)/(720*(1+lam)^10) := by
  have hlam : 1+lam ≠ 0 := fun h0 => h (by linear_combination h0)
  have hc : ∀ (a b c : ℂ) (n : ℕ) l, 1+l ≠ 0 → ContinuousAt (fun l => (a*l^2+b*l+c)/(1+l)^(n+1)) l :=
    fun a b c n l hl => (hasDerivAt_quadratic_div_pow a b c n hl).continuousAt
  have h1m : ∀ l : ℂ, 1+l ≠ 0 → l ≠ 1 → 1-l^2 ≠ 0 := fun l hl h1 => by
    have : 1-l ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    rw [show 1-l^2 = (1-l)*(1+l) by ring]; exact mul_ne_zero this hl
  have s1 : ∀ l, 1+l ≠ 0 → angerScaledA 1 l = (0*l^2+(-1/2)*l+0)/(1+l)^(3+1) := by
    intro l hl
    refine angerScaledA_succ_eq 0 (g := fun l => (0*l^2+0*l+1)/(1+l)^(0+1))
      (d := fun l => (0*l^2+0*l+(-1))/(1+l)^(1+1)) (e := fun l => (0*l^2+0*l+2)/(1+l)^(2+1))
      (fun l hl => by simp [angerScaledA]) (fun l hl => ?_) (fun l hl => ?_) (fun l hl h1 => ?_)
      (fun l hl => hc _ _ _ _ l hl) hl
    · convert hasDerivAt_quadratic_div_pow 0 0 1 0 hl using 1; field_simp; ring
    · convert hasDerivAt_quadratic_div_pow 0 0 (-1) 1 hl using 1; field_simp; ring
    · have := h1m l hl h1; field_simp; ring
  have s2 : ∀ l, 1+l ≠ 0 → angerScaledA 2 l = ((9/24)*l^2+(-1/24)*l+0)/(1+l)^(6+1) := by
    intro l hl
    refine angerScaledA_succ_eq 1 (g := fun l => (0*l^2+(-1/2)*l+0)/(1+l)^(3+1))
      (d := fun l => (0*l^2+(3/2)*l+(-1/2))/(1+l)^(4+1))
      (e := fun l => (0*l^2+(-6)*l+4)/(1+l)^(5+1))
      s1 (fun l hl => ?_) (fun l hl => ?_) (fun l hl h1 => ?_)
      (fun l hl => hc _ _ _ _ l hl) hl
    · convert hasDerivAt_quadratic_div_pow 0 (-1/2) 0 3 hl using 1; field_simp; ring
    · convert hasDerivAt_quadratic_div_pow 0 (3/2) (-1/2) 4 hl using 1; field_simp; ring
    · have := h1m l hl h1; push_cast; field_simp; ring
  have s3 : angerScaledA 3 lam = -(225*lam^3-54*lam^2+lam)/(720*(1+lam)^10) := by
    refine angerScaledA_succ_eq 2 (g := fun l => ((9/24)*l^2+(-1/24)*l+0)/(1+l)^(6+1))
      (d := fun l => ((-45/24)*l^2+1*l+(-1/24))/(1+l)^(7+1))
      (e := fun l => ((270/24)*l^2+(-258/24)*l+(32/24))/(1+l)^(8+1))
      (G := fun l => -(225*l^3-54*l^2+l)/(720*(1+l)^10))
      s2 (fun l hl => ?_) (fun l hl => ?_) (fun l hl h1 => ?_)
      (fun l hl => ?_) hlam
    · convert hasDerivAt_quadratic_div_pow (9/24) (-1/24) 0 6 hl using 1; field_simp; ring
    · convert hasDerivAt_quadratic_div_pow (-45/24) 1 (-1/24) 7 hl using 1; field_simp; ring
    · have := h1m l hl h1; push_cast; field_simp; ring
    · exact ((by fun_prop : Continuous fun l : ℂ => -(225*l^3-54*l^2+l)).continuousAt).div
        (by fun_prop) (mul_ne_zero (by norm_num) (pow_ne_zero _ hl))
  refine ⟨?_, ?_, s3⟩
  · rw [s1 lam hlam]; field_simp; ring
  · rw [s2 lam hlam]; field_simp; ring

/-- Asymptotic bound with the indicated comparison function: `(fun ν : ℂ => angerA (1*ν)
(lam*ν)-(1:ℂ)/π*∑ k ∈ Finset.range N, ((2*k).factorial:ℂ)*angerScaledA k (1*lam)/ν^(2*k+1))
=O[sector (π-δ)] (fun ν : ℂ => ν^(-(2*N+1:ℤ)))`. -/
@[dlmf 11.11.E8]
theorem angerA_scaled_8 {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => angerA (1*ν) (lam*ν)-(1:ℂ)/π*∑ k ∈ Finset.range N, ((2*k).factorial:ℂ)*angerScaledA k (1*lam)/ν^(2*k+1)) =O[sector (π-δ)] (fun ν : ℂ => ν^(-(2*N+1:ℤ))) := by
  sorry

/-- Asymptotic bound with the indicated comparison function: `(fun ν : ℂ => angerA (-1*ν)
(lam*ν)-(-1:ℂ)/π*∑ k ∈ Finset.range N, ((2*k).factorial:ℂ)*angerScaledA k (-1*lam)/ν^(2*k+1))
=O[sector (π-δ)] (fun ν : ℂ => ν^(-(2*N+1:ℤ)))`. -/
@[dlmf 11.11.E10]
theorem angerA_scaled_10 {lam : ℝ} (hlam : 1 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => angerA (-1*ν) (lam*ν)-(-1:ℂ)/π*∑ k ∈ Finset.range N, ((2*k).factorial:ℂ)*angerScaledA k (-1*lam)/ν^(2*k+1)) =O[sector (π-δ)] (fun ν : ℂ => ν^(-(2*N+1:ℤ))) := by
  sorry

/-- The principal-branch phase `√(1-lam²) - log ((1+√(1-lam²))/lam)` of the scaled Anger
expansion. -/
@[dlmf 11.11.E12]
def angerMu (lam : ℂ) : ℂ :=
  (1-lam^2)^(1/2:ℂ)-log ((1+(1-lam^2)^(1/2:ℂ))/lam)

/-- Coefficients of the saddle expansion, with existence provided by the expansion theorem. -/
def angerScaledB (lam : ℝ) (k : ℕ) : ℂ :=
  asymptoticCoeff (fun v : ℝ => ((π*v/2:ℂ)^(1/2:ℂ))*exp (v*angerMu lam)*angerA (-v) (lam*v)) k / poch (1/2) k

/-- Asymptotic bound with the indicated comparison function: `(fun ν : ℂ => (π*ν/2)^(1/2:ℂ)*exp
(ν*angerMu lam)*angerA (-ν) (lam*ν)-∑ k ∈ Finset.range N, poch (1/2) k*angerScaledB lam k/ν^k)
=O[sector (π/2-δ)] (fun ν : ℂ => ν^(-(N:ℤ)))`. -/
@[dlmf 11.11.E11]
theorem angerA_scaled_saddle {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun ν : ℂ => (π*ν/2)^(1/2:ℂ)*exp (ν*angerMu lam)*angerA (-ν) (lam*ν)-∑ k ∈ Finset.range N, poch (1/2) k*angerScaledB lam k/ν^k) =O[sector (π/2-δ)] (fun ν : ℂ => ν^(-(N:ℤ))) := by
  sorry

/-- Identity under the stated parameter and domain assumptions: `angerScaledB lam 0 =
(1-lam^2:ℂ)^(-1/4:ℂ) ∧ angerScaledB lam 1 = (2+3*lam^2:ℂ)/(12*(1-lam^2:ℂ)^(7/4:ℂ)) ∧
angerScaledB lam 2 = (4+300*lam^2+81*lam^4:ℂ)/(864*(1-lam^2:ℂ)^(13/4:ℂ))`. -/
@[dlmf 11.11.E13]
theorem angerScaledB_initial {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    angerScaledB lam 0 = (1-lam^2:ℂ)^(-1/4:ℂ) ∧ angerScaledB lam 1 = (2+3*lam^2:ℂ)/(12*(1-lam^2:ℂ)^(7/4:ℂ)) ∧ angerScaledB lam 2 = (4+300*lam^2+81*lam^4:ℂ)/(864*(1-lam^2:ℂ)^(13/4:ℂ)) := by
  sorry

end DLMF.Struve
end
