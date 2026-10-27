/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Stirling's formula for the Gamma function (AAR §1.4)

Mathlib has Stirling's formula for `n!` (`Stirling.factorial_isEquivalent_stirling`). AAR
Theorem 1.4.1 is `Γ(x) ∼ √(2π) x^{x-1/2} e^{-x}` as `Re x → ∞`. Along the positive integers this
is `Γ(n+1) = n! ∼ √(2π n) (n/e)^n`. The real-variable form along rays `n ↦ n + t` is deduced from
the integer case by log-convexity of `Γ` on `(0,∞)`.
-/

@[expose] public section

open Filter Real Asymptotics Set

open scoped Topology

noncomputable section

namespace Real

/-- The leading Stirling approximation to `Γ(x)` for `x > 0`: `√(2π/x) (x/e)^x`. -/
def stirlingGamma (x : ℝ) : ℝ :=
  sqrt (2 * π / x) * (x / exp 1) ^ x

theorem stirlingGamma_pos {x : ℝ} (hx : 0 < x) : 0 < stirlingGamma x :=
  mul_pos (sqrt_pos_of_pos (div_pos (mul_pos two_pos pi_pos) hx))
    (rpow_pos_of_pos (div_pos hx (exp_pos _)) _)

theorem stirlingGamma_ne_zero {x : ℝ} (hx : 0 < x) : stirlingGamma x ≠ 0 :=
  (stirlingGamma_pos hx).ne'

theorem log_stirlingGamma {x : ℝ} (hx : 0 < x) :
    log (stirlingGamma x) =
      (1 / 2) * log (2 * π) - (1 / 2) * log x + x * log x - x := by
  have h2π : 0 < 2 * π := mul_pos two_pos pi_pos
  have hxee : 0 < x / exp 1 := div_pos hx (exp_pos _)
  unfold stirlingGamma
  rw [log_mul (sqrt_pos_of_pos (div_pos h2π hx)).ne' (rpow_pos_of_pos hxee _).ne',
    log_sqrt (div_nonneg h2π.le hx.le), log_div h2π.ne' hx.ne',
    log_rpow hxee, log_div hx.ne' (exp_pos _).ne', log_exp]
  ring

/-- AAR Theorem 1.4.1 along the positive integers: `Γ(n+1) ∼ √(2π n) (n/e)^n`. -/
theorem Gamma_nat_succ_isEquivalent_stirling :
    (fun n : ℕ => Gamma (n + 1 : ℝ)) ~[atTop]
      fun n => sqrt (2 * π * n) * (n / exp 1) ^ n := by
  convert! Stirling.factorial_isEquivalent_stirling using 3 with n
  · exact Gamma_nat_eq_factorial n
  · ring

theorem tendsto_n_div_succ_pow :
    Tendsto (fun n : ℕ => ((n : ℝ) / (n + 1)) ^ n) atTop (𝓝 (exp (-1))) := by
  have h : Tendsto (fun n : ℕ => (1 + (1 : ℝ) / n) ^ n) atTop (𝓝 (exp 1)) :=
    tendsto_one_add_div_pow_exp 1
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) / (n + 1)) ^ n) atTop (𝓝 (exp 1)⁻¹) := by
    refine (h.inv₀ (exp_ne_zero 1)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hpos : 0 < (1 : ℝ) + 1 / n := by positivity
    rw [← inv_pow]
    have : ((1 : ℝ) + 1 / n)⁻¹ = n / (n + 1) := by field
    rw [this]
  simpa [exp_neg] using hinv

theorem sqrt_two_pi_n_div_stirlingGamma_succ (n : ℕ) (hn : 0 < n) :
    sqrt (2 * π * n) * (n / exp 1) ^ n / stirlingGamma (n + 1 : ℝ) =
      exp 1 * sqrt ((n : ℝ) / (n + 1)) * ((n : ℝ) / (n + 1)) ^ n := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (0 : ℝ) < n + 1 := add_pos hn0 one_pos
  have h2π : 0 < 2 * π := mul_pos two_pos pi_pos
  have hS : 0 < stirlingGamma (n + 1 : ℝ) := stirlingGamma_pos hn1
  have hnum : 0 < sqrt (2 * π * n) * (n / exp 1) ^ n := by positivity
  have hsqrt : 0 < sqrt ((n : ℝ) / (n + 1)) := sqrt_pos_of_pos (div_pos hn0 hn1)
  have hpow : 0 < ((n : ℝ) / (n + 1)) ^ n := pow_pos (div_pos hn0 hn1) n
  have hR : 0 < exp 1 * sqrt ((n : ℝ) / (n + 1)) * ((n : ℝ) / (n + 1)) ^ n :=
    mul_pos (mul_pos (exp_pos _) hsqrt) hpow
  refine log_injOn_pos (mem_Ioi.mpr (div_pos hnum hS)) (mem_Ioi.mpr hR) ?_
  have hlog := log_stirlingGamma hn1
  have hlogN :
      log (sqrt (2 * π * n) * (n / exp 1) ^ n) =
        (1 / 2) * log (2 * π) + (1 / 2) * log n + n * log n - n := by
    rw [log_mul (sqrt_pos_of_pos (mul_pos h2π hn0)).ne' (by positivity),
      log_sqrt (mul_nonneg h2π.le hn0.le), log_mul h2π.ne' hn0.ne',
      log_pow, log_div hn0.ne' (exp_pos _).ne', log_exp]
    ring
  rw [log_div hnum.ne' hS.ne', hlogN, hlog,
    log_mul (mul_pos (exp_pos _) hsqrt).ne' hpow.ne',
    log_mul (exp_pos _).ne' hsqrt.ne', log_exp,
    log_sqrt (div_nonneg hn0.le hn1.le), log_div hn0.ne' hn1.ne', log_pow,
    log_div hn0.ne' hn1.ne']
  ring

theorem tendsto_stirling_n_div_stirlingGamma_succ :
    Tendsto (fun n : ℕ =>
      (sqrt (2 * π * n) * (n / exp 1) ^ n) / stirlingGamma (n + 1 : ℝ)) atTop (𝓝 1) := by
  have hsqrt : Tendsto (fun n : ℕ => sqrt ((n : ℝ) / (n + 1))) atTop (𝓝 1) := by
    simpa using (tendsto_natCast_div_add_atTop (1 : ℝ)).sqrt
  have hmain : Tendsto (fun n : ℕ =>
      exp 1 * sqrt ((n : ℝ) / (n + 1)) * ((n : ℝ) / (n + 1)) ^ n) atTop (𝓝 1) := by
    have := tendsto_const_nhds (x := exp 1) |>.mul hsqrt |>.mul tendsto_n_div_succ_pow
    simpa [exp_neg, mul_assoc] using this
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (sqrt_two_pi_n_div_stirlingGamma_succ n hn).symm

/-- Stirling's formula in the form `Γ(n+1) ∼ √(2π/(n+1)) ((n+1)/e)^{n+1}`. -/
@[dlmf 5.11.E3]
theorem Gamma_nat_succ_isEquivalent_stirlingGamma :
    (fun n : ℕ => Gamma (n + 1 : ℝ)) ~[atTop] fun n => stirlingGamma (n + 1 : ℝ) :=
  Gamma_nat_succ_isEquivalent_stirling.trans <|
    isEquivalent_of_tendsto_one tendsto_stirling_n_div_stirlingGamma_succ

theorem tendsto_Gamma_nat_succ_div_stirlingGamma :
    Tendsto (fun n : ℕ => Gamma (n + 1 : ℝ) / stirlingGamma (n + 1 : ℝ)) atTop (𝓝 1) := by
  have hne : ∀ᶠ n : ℕ in atTop, stirlingGamma (n + 1 : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 0] with n _
    exact stirlingGamma_ne_zero (by positivity : (0 : ℝ) < n + 1)
  exact (isEquivalent_iff_tendsto_one hne).mp Gamma_nat_succ_isEquivalent_stirlingGamma

theorem tendsto_Gamma_nat_div_stirlingGamma :
    Tendsto (fun n : ℕ => Gamma (n : ℝ) / stirlingGamma n) atTop (𝓝 1) :=
  (tendsto_add_atTop_iff_nat (f := fun n : ℕ => Gamma (n : ℝ) / stirlingGamma n) 1).mp <| by
    convert tendsto_Gamma_nat_succ_div_stirlingGamma using 1
    ext n
    simp [Nat.cast_succ]

theorem log_Gamma_add_one {y : ℝ} (hy : 0 < y) :
    (log ∘ Gamma) (y + 1) = (log ∘ Gamma) y + log y := by
  simp [Function.comp_apply, Gamma_add_one hy.ne',
    log_mul hy.ne' (Gamma_pos_of_pos hy).ne', add_comm]

theorem Gamma_add_le_mul_rpow {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    Gamma (n + t) ≤ Gamma n * (n : ℝ) ^ t := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hlog := BohrMollerup.f_add_nat_le convexOn_log_Gamma
    (fun {y} hy => log_Gamma_add_one hy) hn ht0 ht1
  have hpos : 0 < Gamma n * (n : ℝ) ^ t :=
    mul_pos (Gamma_pos_of_pos hn0) (rpow_pos_of_pos hn0 _)
  have : log (Gamma (n + t)) ≤ log (Gamma n * (n : ℝ) ^ t) := by
    simpa [Function.comp_apply, log_mul (Gamma_pos_of_pos hn0).ne' (rpow_pos_of_pos hn0 t).ne',
      log_rpow hn0] using hlog
  exact (log_le_log_iff (Gamma_pos_of_pos (add_pos hn0 ht0)) hpos).mp this

theorem mul_rpow_le_Gamma_add {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht0 : 0 < t) :
    Gamma n * ((n : ℝ) - 1) ^ t ≤ Gamma (n + t) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_of_lt_of_le zero_lt_two hn)
  have hn1 : (0 : ℝ) < n - 1 := by
    have : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn
    linarith
  have hlog := BohrMollerup.f_add_nat_ge convexOn_log_Gamma
    (fun {y} hy => log_Gamma_add_one hy) hn ht0
  have hpos : 0 < Gamma n * ((n : ℝ) - 1) ^ t :=
    mul_pos (Gamma_pos_of_pos hn0) (rpow_pos_of_pos hn1 _)
  have : log (Gamma n * ((n : ℝ) - 1) ^ t) ≤ log (Gamma (n + t)) := by
    simpa [Function.comp_apply, log_mul (Gamma_pos_of_pos hn0).ne' (rpow_pos_of_pos hn1 t).ne',
      log_rpow hn1] using hlog
  exact (log_le_log_iff hpos (Gamma_pos_of_pos (add_pos hn0 ht0))).mp this

theorem log_stirlingGamma_mul_rpow_div {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : (n : ℝ) ≤ x) :
    log (stirlingGamma n * (n : ℝ) ^ (x - n) / stirlingGamma x) =
      (x - n) + (1 / 2 - x) * log (x / n) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hx0 : 0 < x := lt_of_lt_of_le hn0 hx
  have hSn := stirlingGamma_pos hn0
  have hSx := stirlingGamma_pos hx0
  have hpow : 0 < (n : ℝ) ^ (x - n) := rpow_pos_of_pos hn0 _
  rw [log_div (mul_pos hSn hpow).ne' hSx.ne', log_mul hSn.ne' hpow.ne',
    log_stirlingGamma hn0, log_stirlingGamma hx0, log_rpow hn0, log_div hx0.ne' hn0.ne']
  ring

theorem tendsto_nat_mul_log_one_add_div (t : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * log (1 + t / n)) atTop (𝓝 t) :=
  tendsto_nat_mul_log_one_add_of_tendsto (g := fun n : ℕ => t / n) <| by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact (mul_div_cancel₀ t (Nat.cast_ne_zero.mpr hn)).symm

theorem tendsto_one_add_div (t : ℝ) :
    Tendsto (fun n : ℕ => (1 : ℝ) + t / n) atTop (𝓝 1) := by
  simpa using tendsto_const_nhds (x := (1 : ℝ)) |>.add
    ((tendsto_const_nhds (x := t)).div_atTop tendsto_natCast_atTop_atTop)

theorem tendsto_stirlingGamma_mul_rpow_div {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ =>
      stirlingGamma n * (n : ℝ) ^ t / stirlingGamma (n + t)) atTop (𝓝 1) := by
  have hmain := tendsto_nat_mul_log_one_add_div t
  have h1 := tendsto_one_add_div t
  have hhalf : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * log (1 + t / n)) atTop (𝓝 0) := by
    simpa using (h1.log one_ne_zero).const_mul (1 / 2 : ℝ)
  have htlog : Tendsto (fun n : ℕ => t * log (1 + t / n)) atTop (𝓝 0) := by
    simpa using (h1.log one_ne_zero).const_mul t
  have hlog : Tendsto (fun n : ℕ =>
      log (stirlingGamma n * (n : ℝ) ^ t / stirlingGamma (n + t))) atTop (𝓝 0) := by
    have hcomb : Tendsto (fun n : ℕ =>
        t - ((n : ℝ) * log (1 + t / n) + t * log (1 + t / n) -
          (1 / 2) * log (1 + t / n))) atTop (𝓝 (t - (t + 0 - 0))) :=
      tendsto_const_nhds.sub (hmain.add htlog |>.sub hhalf)
    refine (hcomb.congr' ?_).trans_eq (by ring)
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hx : (n : ℝ) ≤ n + t := le_add_of_nonneg_right ht
    have hform := log_stirlingGamma_mul_rpow_div hn hx
    simp only [add_sub_cancel_left] at hform
    have hdiv : ((n : ℝ) + t) / n = 1 + t / n := by field
    rw [hform, hdiv]
    ring
  have hpos : ∀ᶠ n : ℕ in atTop,
      0 < stirlingGamma n * (n : ℝ) ^ t / stirlingGamma (n + t) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    exact div_pos (mul_pos (stirlingGamma_pos hn0) (rpow_pos_of_pos hn0 _))
      (stirlingGamma_pos (add_pos_of_pos_of_nonneg hn0 ht))
  refine (((continuous_exp.tendsto (0 : ℝ)).comp hlog).congr' ?_).trans_eq (by simp)
  filter_upwards [hpos] with n hn
  exact Real.exp_log hn

theorem tendsto_stirlingGamma_mul_pred_rpow_div {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ =>
      stirlingGamma n * ((n : ℝ) - 1) ^ t / stirlingGamma (n + t)) atTop (𝓝 1) := by
  have hmain := tendsto_stirlingGamma_mul_rpow_div ht
  have hratio : Tendsto (fun n : ℕ => ((n : ℝ) - 1) ^ t / (n : ℝ) ^ t) atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => ((n : ℝ) - 1) / n) atTop (𝓝 1) := by
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / n) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds (x := (1 : ℝ)) |>.sub
          (tendsto_const_nhds (x := (1 : ℝ)) |>.div_atTop tendsto_natCast_atTop_atTop)
      refine h1.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      field
    have hrpow := h.rpow_const (p := t) (Or.inl (one_ne_zero : (1 : ℝ) ≠ 0))
    have hrpow1 : Tendsto (fun n : ℕ => (((n : ℝ) - 1) / n) ^ t) atTop (𝓝 1) := by
      simpa [one_rpow] using hrpow
    refine hrpow1.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_trans zero_lt_one hn)
    have hlt : (1 : ℝ) < n := (Nat.one_lt_cast (α := ℝ)).mpr hn
    have hn1 : (0 : ℝ) < n - 1 := sub_pos.mpr hlt
    rw [div_rpow hn1.le hn0.le]
  have hmul := hmain.mul hratio
  refine (hmul.congr' ?_).trans_eq (by simp)
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_trans zero_lt_one hn)
  have hlt : (1 : ℝ) < n := (Nat.one_lt_cast (α := ℝ)).mpr hn
  have hn1 : (0 : ℝ) < n - 1 := sub_pos.mpr hlt
  have hnt : 0 < n + t := add_pos_of_pos_of_nonneg hn0 ht
  field [(stirlingGamma_pos hn0).ne', (stirlingGamma_pos hnt).ne',
    (rpow_pos_of_pos hn0 t).ne', (rpow_pos_of_pos hn1 t).ne']

/-- Stirling along the ray `n + t` for fixed `t ∈ (0, 1]`. -/
theorem tendsto_Gamma_add_nat_div_stirlingGamma {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    Tendsto (fun n : ℕ => Gamma (n + t) / stirlingGamma (n + t)) atTop (𝓝 1) := by
  have hnat := tendsto_Gamma_nat_div_stirlingGamma
  have hupper : Tendsto (fun n : ℕ =>
      Gamma (n : ℝ) / stirlingGamma n *
        (stirlingGamma n * (n : ℝ) ^ t / stirlingGamma (n + t))) atTop (𝓝 1) := by
    simpa using hnat.mul (tendsto_stirlingGamma_mul_rpow_div ht.le)
  have hlower : Tendsto (fun n : ℕ =>
      Gamma (n : ℝ) / stirlingGamma n *
        (stirlingGamma n * ((n : ℝ) - 1) ^ t / stirlingGamma (n + t))) atTop (𝓝 1) := by
    simpa using hnat.mul (tendsto_stirlingGamma_mul_pred_rpow_div ht.le)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_of_lt_of_le zero_lt_two hn)
    have hpos : 0 < stirlingGamma (n + t) :=
      stirlingGamma_pos (add_pos_of_pos_of_nonneg hn0 ht.le)
    have hSn : 0 < stirlingGamma n := stirlingGamma_pos hn0
    have hineq := mul_rpow_le_Gamma_add hn ht
    have heq : Gamma n / stirlingGamma n *
        (stirlingGamma n * ((n : ℝ) - 1) ^ t / stirlingGamma (n + t)) =
        Gamma n * ((n : ℝ) - 1) ^ t / stirlingGamma (n + t) := by
      field [hSn.ne', hpos.ne']
    rw [heq]
    exact div_le_div_of_nonneg_right hineq hpos.le
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hpos : 0 < stirlingGamma (n + t) :=
      stirlingGamma_pos (add_pos_of_pos_of_nonneg hn0 ht.le)
    have hSn : 0 < stirlingGamma n := stirlingGamma_pos hn0
    have hineq := Gamma_add_le_mul_rpow hn.ne' ht ht1
    have heq : Gamma n / stirlingGamma n *
        (stirlingGamma n * (n : ℝ) ^ t / stirlingGamma (n + t)) =
        Gamma n * (n : ℝ) ^ t / stirlingGamma (n + t) := by
      field [hSn.ne', hpos.ne']
    rw [heq]
    exact div_le_div_of_nonneg_right hineq hpos.le

end Real
