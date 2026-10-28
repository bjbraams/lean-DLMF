/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial

public import DLMF.Gamma.ComplexBinet
public import DLMF.Gamma.MellinBarnes
public import DLMF.Hypergeometric.Basic
public import Mathlib.NumberTheory.BernoulliPolynomials

/-!
# Asymptotic expansions (DLMF §5.11)

Stirling's formula for `Γ(n+1)` is already `Gamma_nat_succ_isEquivalent_stirlingGamma`
in `Stirling.lean`. Poincaré expansions below are stated along the positive real
axis. Remainder estimates 5.11.10–5.11.11 with `sec(ph z)` are deferred except
for the real-axis form of 5.11.3.
-/

@[expose] public section

open Complex Filter MeasureTheory
open scoped Real Topology
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Gamma

/-- Scaled Gamma `Γ*(z)` in DLMF 5.11.3. -/
@[dlmf 5.11.E3]
def scaledGamma (z : ℂ) : ℂ :=
  Complex.Gamma z / (Complex.exp (-z) * z ^ z * (2 * π / z) ^ (1 / 2 : ℂ))

section StirlingSeries

/-! ### Stirling's series from Binet's formula (Temme §3.6)

The partial fractions `β(t)/t = ∑ₘ 2/(t² + aₘ²)`, `aₘ = 2π(m+1)`, expanded with an exact
geometric remainder, give `β(t)/t = ∑_{k ≤ n} B₂ₖ t^{2k-2}/(2k)! + Rₙ(t)` with
`|Rₙ(t)| ≤ 2 Sₙ t^{2n}`, where `Sₙ = ∑ₘ aₘ^{-(2n+2)}`. Integrating against `e^{-zt}` gives
the series for `log Γ` (from `log_Gamma_binet_exp`) and for `ψ` (from `digamma_coth`'s
companion `digamma_eq_log_sub_binetBeta`). -/

open Set

/-- `∑ₘ (2π(m+1))^{-2k} = (-1)^{k+1} B₂ₖ/(2 (2k)!)` for `k ≥ 1`. -/
theorem hasSum_recip_two_pi_pow {k : ℕ} (hk : k ≠ 0) :
    HasSum (fun m : ℕ => 1 / (2 * π * (m + 1)) ^ (2 * k))
      ((-1 : ℝ) ^ (k + 1) * bernoulli (2 * k) / (2 * (2 * k).factorial)) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_zeta_nat hk)
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero,
    zero_pow (by omega : 2 * k ≠ 0), div_zero, sub_zero] at h
  have h2 := h.mul_left (1 / (2 * π) ^ (2 * k))
  convert h2 using 1
  · funext m
    push_cast
    rw [mul_pow, one_div_mul_one_div]
  · have hπ : (2 * π) ^ (2 * k) = 2 ^ (2 * k) * π ^ (2 * k) := mul_pow _ _ _
    have h2k : (2 : ℝ) ^ (2 * k) = 2 * 2 ^ (2 * k - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hπ, h2k]
    have := Real.pi_pos
    field_simp

/-- `∫₀^∞ e^{-zt} tʲ dt = j!/z^{j+1}`. -/
theorem integral_exp_mul_pow {z : ℝ} (hz : 0 < z) (j : ℕ) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-z * t) * t ^ j = j.factorial / z ^ (j + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (j : ℝ) + 1) (r := z) (by positivity) hz
  rw [Real.Gamma_nat_eq_factorial, add_sub_cancel_right] at h
  calc ∫ t in Ioi (0 : ℝ), Real.exp (-z * t) * t ^ j
      = ∫ t in Ioi (0 : ℝ), t ^ (j : ℝ) * Real.exp (-(z * t)) :=
        setIntegral_congr_fun measurableSet_Ioi fun t _ => by rw [Real.rpow_natCast, neg_mul]; ring
    _ = (1 / z) ^ ((j : ℝ) + 1) * j.factorial := h
    _ = j.factorial / z ^ (j + 1) := by
        rw [show (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
          one_div_pow]
        field_simp

/-- `e^(-zt) t^j` is integrable on `(0, ∞)` for `z > 0`. -/
theorem integrableOn_exp_mul_pow {z : ℝ} (hz : 0 < z) (j : ℕ) :
    IntegrableOn (fun t => Real.exp (-z * t) * t ^ j) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := j) (b := z) (by
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) one_pos hz
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one, Real.rpow_natCast, mul_comm]

/-- The Bernoulli polynomial part of `β(t)/t`. -/
def binetPoly (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (bernoulli (2 * k) : ℝ) / (2 * k).factorial * t ^ (2 * k - 2)

/-- `Sₙ = ∑ₘ (2π(m+1))^{-(2n+2)}`. -/
def binetRemConst (n : ℕ) : ℝ := ∑' m : ℕ, 1 / (2 * π * (m + 1)) ^ (2 * n + 2)

/-- `binetPoly n t = ∑_{j<n} B_{2j+2}/(2j+2)! t^(2j)`. -/
theorem binetPoly_eq_range (n : ℕ) (t : ℝ) : binetPoly n t =
    ∑ j ∈ Finset.range n,
      (bernoulli (2 * (j + 1)) : ℝ) / (2 * (j + 1)).factorial * t ^ (2 * j) := by
  induction n with
  | zero => simp [binetPoly]
  | succ n ih =>
    simp only [binetPoly] at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ,
      show 2 * (n + 1) - 2 = 2 * n by omega]

/-- `|β(t)/t - Pₙ(t)| ≤ 2 Sₙ t^{2n}` (Temme (3.26)). -/
theorem abs_binetBeta_div_sub_binetPoly_le (n : ℕ) {t : ℝ} (ht : 0 < t) :
    |binetBeta t / t - binetPoly n t| ≤ 2 * binetRemConst n * t ^ (2 * n) := by
  have ha : ∀ m : ℕ, 0 < 2 * π * (m + 1) := fun m => by positivity
  -- termwise: `2/(t² + a²) = ∑_{j<n} 2(-1)ʲ t^{2j}/a^{2j+2} + 2(-1)ⁿ t^{2n}/(a^{2n}(t²+a²))`
  have hterm : ∀ a : ℝ, 0 < a → 2 / (t ^ 2 + a ^ 2) =
      ∑ j ∈ Finset.range n, 2 * (-1 : ℝ) ^ j * t ^ (2 * j) / a ^ (2 * j + 2) +
        2 * (-1 : ℝ) ^ n * t ^ (2 * n) / (a ^ (2 * n) * (t ^ 2 + a ^ 2)) := by
    intro a ha
    have h1 : t ^ 2 + a ^ 2 ≠ 0 := by positivity
    have h2 : a ≠ 0 := ha.ne'
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ih, Finset.sum_range_succ, add_assoc]
      congr 1
      field_simp
      ring
  -- the zeta sums
  have hS : ∀ j : ℕ, HasSum (fun m : ℕ => 2 * (-1 : ℝ) ^ j * t ^ (2 * j) /
      (2 * π * (m + 1)) ^ (2 * j + 2))
      ((bernoulli (2 * (j + 1)) : ℝ) / (2 * (j + 1)).factorial * t ^ (2 * j)) := by
    intro j
    have h := (hasSum_recip_two_pi_pow (k := j + 1) (by omega)).mul_left (2 * (-1 : ℝ) ^ j *
      t ^ (2 * j))
    convert h using 1
    · funext m
      rw [show 2 * (j + 1) = 2 * j + 2 by ring]
      ring
    · rw [show (-1 : ℝ) ^ (j + 1 + 1) = (-1) ^ j by ring]
      have hsq : (-1 : ℝ) ^ j * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
      have e : 2 * (-1 : ℝ) ^ j * t ^ (2 * j) * ((-1) ^ j * (bernoulli (2 * (j + 1)) : ℝ) /
          (2 * ((2 * (j + 1)).factorial : ℝ))) = ((-1) ^ j * (-1) ^ j) *
          ((bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)).factorial : ℝ) * t ^ (2 * j)) := by
        ring
      rw [e, hsq, one_mul]
  have hRem : HasSum (fun m : ℕ => 2 * (-1 : ℝ) ^ n * t ^ (2 * n) /
      ((2 * π * (m + 1)) ^ (2 * n) * (t ^ 2 + (2 * π * (m + 1)) ^ 2)))
      (binetBeta t / t - binetPoly n t) := by
    have hfin := hasSum_sum (s := Finset.range n) fun j _ => hS j
    have hβ := hasSum_binetBeta_div ht
    have := hβ.sub hfin
    convert this using 1
    · funext m
      rw [hterm _ (ha m)]
      ring
    · rw [binetPoly_eq_range]
  -- bound the remainder
  have hbound : ∀ m : ℕ, ‖2 * (-1 : ℝ) ^ n * t ^ (2 * n) /
      ((2 * π * (m + 1)) ^ (2 * n) * (t ^ 2 + (2 * π * (m + 1)) ^ 2))‖ ≤
        2 * t ^ (2 * n) * (1 / (2 * π * (m + 1)) ^ (2 * n + 2)) := by
    intro m
    have hm := ha m
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      mul_one, abs_two, abs_of_nonneg (by positivity : 0 ≤ t ^ (2 * n)),
      abs_of_pos (by positivity)]
    have : (2 * π * (m + 1)) ^ (2 * n + 2) ≤
        (2 * π * (m + 1)) ^ (2 * n) * (t ^ 2 + (2 * π * (m + 1)) ^ 2) := by
      rw [pow_add]; gcongr; nlinarith [sq_nonneg t]
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) this
  have hsumS : Summable fun m : ℕ => 1 / (2 * π * (m + 1)) ^ (2 * n + 2) :=
    (hasSum_recip_two_pi_pow (k := n + 1) (by omega)).summable.congr fun m => by
      rw [show 2 * (n + 1) = 2 * n + 2 by ring]
  have hnorm : Summable fun m : ℕ => ‖2 * (-1 : ℝ) ^ n * t ^ (2 * n) /
      ((2 * π * (m + 1)) ^ (2 * n) * (t ^ 2 + (2 * π * (m + 1)) ^ 2))‖ :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hbound (hsumS.mul_left _)
  rw [← Real.norm_eq_abs, ← hRem.tsum_eq]
  calc ‖∑' m : ℕ, 2 * (-1 : ℝ) ^ n * t ^ (2 * n) /
        ((2 * π * (m + 1)) ^ (2 * n) * (t ^ 2 + (2 * π * (m + 1)) ^ 2))‖
      ≤ ∑' m : ℕ, ‖2 * (-1 : ℝ) ^ n * t ^ (2 * n) /
        ((2 * π * (m + 1)) ^ (2 * n) * (t ^ 2 + (2 * π * (m + 1)) ^ 2))‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' m : ℕ, 2 * t ^ (2 * n) * (1 / (2 * π * (m + 1)) ^ (2 * n + 2)) :=
        hnorm.tsum_le_tsum hbound (hsumS.mul_left _)
    _ = 2 * binetRemConst n * t ^ (2 * n) := by
        rw [tsum_mul_left, binetRemConst]; ring

/-- `e^(-zs) s^j binetPoly n s` is integrable on `(0, ∞)` for `z > 0`. -/
theorem integrableOn_exp_mul_pow_mul_binetPoly {z : ℝ} (hz : 0 < z) (n j : ℕ) :
    IntegrableOn (fun s => Real.exp (-z * s) * (s ^ j * binetPoly n s)) (Ioi 0) := by
  simp only [binetPoly, Finset.mul_sum]
  refine integrable_finsetSum _ fun k _ => ?_
  refine IntegrableOn.congr_fun ((integrableOn_exp_mul_pow hz (j + (2 * k - 2))).const_mul
    ((bernoulli (2 * k) : ℝ) / (2 * k).factorial)) (fun s _ => ?_) measurableSet_Ioi
  rw [pow_add]
  ring

/-- `∫₀^∞ e^{-zs} sʲ Pₙ(s) ds = ∑ₖ B₂ₖ (2k-2+j)!/((2k)! z^{2k-1+j})`. -/
theorem integral_exp_mul_pow_mul_binetPoly {z : ℝ} (hz : 0 < z) (n j : ℕ) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-z * s) * (s ^ j * binetPoly n s) =
      ∑ k ∈ Finset.Icc 1 n, (bernoulli (2 * k) : ℝ) / (2 * k).factorial *
        ((2 * k - 2 + j).factorial / z ^ (2 * k - 2 + j + 1)) := by
  simp only [binetPoly, Finset.mul_sum]
  rw [integral_finsetSum _ fun k _ => ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_exp_mul_pow hz, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [pow_add]
    ring
  · refine IntegrableOn.congr_fun ((integrableOn_exp_mul_pow hz (2 * k - 2 + j)).const_mul
      ((bernoulli (2 * k) : ℝ) / (2 * k).factorial)) (fun s _ => ?_) measurableSet_Ioi
    rw [pow_add]
    ring

/-- `|∫₀^∞ e^{-zs} sʲ (β(s)/s - Pₙ(s)) ds| ≤ 2 Sₙ (2n+j)!/z^{2n+j+1}`. -/
theorem abs_integral_exp_mul_pow_mul_rem_le {z : ℝ} (hz : 0 < z) (n j : ℕ) :
    |∫ s in Ioi (0 : ℝ), Real.exp (-z * s) * (s ^ j * (binetBeta s / s - binetPoly n s))| ≤
      2 * binetRemConst n * ((2 * n + j).factorial / z ^ (2 * n + j + 1)) := by
  have hS : 0 ≤ binetRemConst n :=
    tsum_nonneg fun m => by positivity
  rw [← Real.norm_eq_abs]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  have hle : ∫ s in Ioi (0 : ℝ), ‖Real.exp (-z * s) * (s ^ j * (binetBeta s / s -
      binetPoly n s))‖ ≤ ∫ s in Ioi (0 : ℝ), 2 * binetRemConst n *
        (Real.exp (-z * s) * s ^ (2 * n + j)) := by
    refine setIntegral_mono_on ?_ ((integrableOn_exp_mul_pow hz _).const_mul _)
      measurableSet_Ioi fun s hs => ?_
    · refine Integrable.mono' ((integrableOn_exp_mul_pow hz (2 * n + j)).const_mul
        (2 * binetRemConst n)) ?_ ?_
      · refine (ContinuousOn.aestronglyMeasurable (fun s hs => ?_) measurableSet_Ioi).norm
        have hs' : (0 : ℝ) < s := hs
        have h1 := (exp_sub_one_pos hs').ne'
        exact ContinuousAt.continuousWithinAt (by
          unfold binetBeta binetPoly
          fun_prop (disch := first | exact h1 | exact hs'.ne'))
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
        have hs' : (0 : ℝ) < s := hs
        rw [norm_norm, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp,
          abs_of_pos (pow_pos hs' j), pow_add]
        have := abs_binetBeta_div_sub_binetPoly_le n hs'
        have he := Real.exp_pos (-z * s)
        calc Real.exp (-z * s) * (s ^ j * |binetBeta s / s - binetPoly n s|)
            ≤ Real.exp (-z * s) * (s ^ j * (2 * binetRemConst n * s ^ (2 * n))) := by gcongr
          _ = _ := by ring
    · have hs' : (0 : ℝ) < s := hs
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp,
        abs_of_pos (pow_pos hs' j), pow_add]
      have := abs_binetBeta_div_sub_binetPoly_le n hs'
      calc Real.exp (-z * s) * (s ^ j * ‖binetBeta s / s - binetPoly n s‖)
          ≤ Real.exp (-z * s) * (s ^ j * (2 * binetRemConst n * s ^ (2 * n))) := by
            rw [Real.norm_eq_abs]; gcongr
        _ = _ := by ring
  refine hle.trans_eq ?_
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_pow hz]

/-- `(2k-2)!/(2k)! = 1/((2k)(2k-1))` and `(2k-1)!/(2k)! = 1/(2k)` for `k ≥ 1`. -/
theorem factorial_two_mul_sub (k : ℕ) (hk : 1 ≤ k) :
    ((2 * k).factorial : ℝ) = 2 * k * (2 * k - 1) * (2 * k - 2).factorial ∧
      ((2 * k).factorial : ℝ) = 2 * k * (2 * k - 1).factorial := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have e1 : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
  have e2 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  have e3 : 2 * (j + 1) - 2 = 2 * j := by omega
  rw [e2, e3, e1, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  constructor <;> ring

end StirlingSeries

open Set in
/-- DLMF 5.11.1, Stirling's series: `ln Γ(z) = (z - 1/2) ln z - z + (1/2) ln(2π) + ∑_{k=1}^n
B₂ₖ/(2k(2k-1) z^(2k-1)) + O(z^(-2n-1))` along `z = t + x`, `t → ∞`. -/
@[dlmf 5.11.E1]
theorem log_Gamma_stirling (n : ℕ) {x : ℝ} (hx : 1 < x) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Real.log (Real.Gamma (t + x)) -
        ((t + x - 1 / 2) * Real.log (t + x) - (t + x) + (1 / 2) * Real.log (2 * π) +
          ∑ k ∈ Finset.Icc 1 n,
            bernoulli (2 * k) / ((2 * k) * (2 * k - 1) * (t + x) ^ (2 * k - 1))))
      (fun t : ℝ => (t : ℝ) ^ (-(2 * n : ℝ) - 1)) := by
  refine Asymptotics.IsBigO.of_bound (2 * binetRemConst n * (2 * n).factorial) ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  set z := t + x with hz
  have hz0 : 0 < z := by linarith
  have hsum : ∑ k ∈ Finset.Icc 1 n,
      (bernoulli (2 * k) : ℝ) / ((2 * k) * (2 * k - 1) * z ^ (2 * k - 1)) =
      ∫ s in Ioi (0 : ℝ), Real.exp (-z * s) * (s ^ 0 * binetPoly n s) := by
    rw [integral_exp_mul_pow_mul_binetPoly hz0]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [(factorial_two_mul_sub k hk1).1, add_zero,
      show 2 * k - 2 + 1 = 2 * k - 1 by omega]
    have : ((2 * k - 2).factorial : ℝ) ≠ 0 := by positivity
    have h2k : (2 * (k : ℝ) - 1) ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      linarith
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    field_simp
  have hdiff : Real.log (Real.Gamma z) - ((z - 1 / 2) * Real.log z - z + 1 / 2 * Real.log (2 * π) +
      ∑ k ∈ Finset.Icc 1 n,
        (bernoulli (2 * k) : ℝ) / ((2 * k) * (2 * k - 1) * z ^ (2 * k - 1))) =
      ∫ s in Ioi (0 : ℝ), Real.exp (-z * s) * (s ^ 0 * (binetBeta s / s - binetPoly n s)) := by
    have hI : ∫ s in Ioi (0 : ℝ), Real.exp (-z * s) * (s ^ 0 * (binetBeta s / s -
        binetPoly n s)) = binetIntegral z -
          ∫ s in Ioi (0 : ℝ), Real.exp (-z * s) * (s ^ 0 * binetPoly n s) := by
      rw [binetIntegral, ← integral_sub (integrableOn_exp_mul_binetBeta_div hz0)
        (integrableOn_exp_mul_pow_mul_binetPoly hz0 n 0)]
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      ring
    rw [log_Gamma_eq_add_binetIntegral hz0, hsum, hI]
    ring
  have hb := abs_integral_exp_mul_pow_mul_rem_le hz0 n 0
  rw [← hdiff, add_zero] at hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht _)]
  refine hb.trans ?_
  have hS : 0 ≤ binetRemConst n := tsum_nonneg fun m => by positivity
  have hpow : t ^ (-(2 * n : ℝ) - 1) = 1 / t ^ (2 * n + 1) := by
    rw [show -(2 * n : ℝ) - 1 = -((2 * n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg ht.le,
      Real.rpow_natCast, one_div]
  rw [hpow, mul_one_div, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_left₀ ht.le (by linarith) _)) (by positivity)

open Set in
/-- DLMF 5.11.2: `ψ(z) = ln z - 1/(2z) - ∑_{k=1}^n B₂ₖ/(2k z^(2k)) + O(z^(-2n-2))` along `z = t +
x`, `t → ∞`. -/
@[dlmf 5.11.E2]
theorem digamma_stirling (n : ℕ) {x : ℝ} (hx : 1 < x) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Real.digamma (t + x) -
        (Real.log (t + x) - 1 / (2 * (t + x)) -
          ∑ k ∈ Finset.Icc 1 n, bernoulli (2 * k) / ((2 * k) * (t + x) ^ (2 * k))))
      (fun t : ℝ => (t : ℝ) ^ (-(2 * n : ℝ) - 2)) := by
  refine Asymptotics.IsBigO.of_bound (2 * binetRemConst n * (2 * n + 1).factorial) ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  set z := t + x with hz
  have hz0 : 0 < z := by linarith
  have hsum : ∑ k ∈ Finset.Icc 1 n, (bernoulli (2 * k) : ℝ) / ((2 * k) * z ^ (2 * k)) =
      ∫ s in Ioi (0 : ℝ), Real.exp (-z * s) * (s ^ 1 * binetPoly n s) := by
    rw [integral_exp_mul_pow_mul_binetPoly hz0]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [(factorial_two_mul_sub k hk1).2, show 2 * k - 2 + 1 = 2 * k - 1 by omega,
      show 2 * k - 1 + 1 = 2 * k by omega]
    have : ((2 * k - 1).factorial : ℝ) ≠ 0 := by positivity
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    field_simp
  have hdiff : Real.digamma z - (Real.log z - 1 / (2 * z) -
      ∑ k ∈ Finset.Icc 1 n, (bernoulli (2 * k) : ℝ) / ((2 * k) * z ^ (2 * k))) =
      -∫ s in Ioi (0 : ℝ), Real.exp (-z * s) * (s ^ 1 * (binetBeta s / s - binetPoly n s)) := by
    have hI : ∫ s in Ioi (0 : ℝ), Real.exp (-z * s) * (s ^ 1 * (binetBeta s / s -
        binetPoly n s)) = (∫ s in Ioi (0 : ℝ), Real.exp (-z * s) * binetBeta s) -
          ∫ s in Ioi (0 : ℝ), Real.exp (-z * s) * (s ^ 1 * binetPoly n s) := by
      rw [← integral_sub (integrableOn_exp_mul_binetBeta hz0)
        (integrableOn_exp_mul_pow_mul_binetPoly hz0 n 1)]
      refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
      field_simp
    rw [digamma_eq_log_sub_binetBeta hz0, hsum, hI]
    ring
  have hb := abs_integral_exp_mul_pow_mul_rem_le hz0 n 1
  rw [← abs_neg, ← hdiff] at hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht _)]
  refine hb.trans ?_
  have hS : 0 ≤ binetRemConst n := tsum_nonneg fun m => by positivity
  have hpow : t ^ (-(2 * n : ℝ) - 2) = 1 / t ^ (2 * n + 1 + 1) := by
    rw [show -(2 * n : ℝ) - 2 = -((2 * n + 1 + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg ht.le, Real.rpow_natCast, one_div]
  rw [hpow, mul_one_div, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_left₀ ht.le (by linarith) _)) (by positivity)

section StirlingExpansion

/-! ### Stirling's series as an asymptotic expansion, via Watson's lemma

Binet's integral `Φ(z) = ∫₀^∞ e^{-zt} β(t)/t dt` is a Laplace transform whose kernel has the
expansion `β(t)/t ~ ∑ₙ B_{n+2}/(n+2)! tⁿ` at `0`. Watson's lemma
(`hasAsymptoticExpansion_integral_exp_smul`) then gives
`Φ(z) ~ ∑ₙ B_{n+2}/((n+1)(n+2)) z^{-(n+1)}`, and Binet's formula turns this into Stirling's
series for `log Γ`. -/

open Set Asymptotics

/-- The Taylor coefficients of `β(t)/t`: `B_{n+2}/(n+2)!`. -/
def binetCoeff (n : ℕ) : ℝ := (bernoulli (n + 2) : ℝ) / (n + 2).factorial

/-- `Pₘ(t) = ∑_{n<2m} B_{n+2}/(n+2)! tⁿ`; the odd terms vanish. -/
theorem binetPoly_eq_sum_binetCoeff (m : ℕ) (t : ℝ) :
    binetPoly m t = ∑ n ∈ Finset.range (2 * m), binetCoeff n * t ^ n := by
  induction m with
  | zero => simp [binetPoly]
  | succ m ih =>
    rw [binetPoly, Finset.sum_Icc_succ_top (by omega), ← binetPoly, ih,
      show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ]
    have hodd : binetCoeff (2 * m + 1) = 0 := by
      rw [binetCoeff, bernoulli_eq_zero_of_odd ⟨m + 1, by ring⟩ (by omega)]; simp
    rw [hodd, zero_mul, add_zero, binetCoeff, show 2 * m + 1 + 1 - 2 = 2 * m by omega,
      show 2 * m + 1 + 1 = 2 * m + 2 by ring]

/-- Watson's lemma for Binet's integral. -/
theorem hasAsymptoticExpansion_binetIntegral :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (z : ℝ) => z ^ (-((n : ℝ) + 1)))
      (fun n => (bernoulli (n + 2) : ℝ) / ((n + 1) * (n + 2))) binetIntegral := by
  have hW := hasAsymptoticExpansion_integral_exp_smul (F := fun t => binetBeta t / t)
    (a := binetCoeff) (μ := 1) (c := 1) one_pos ?_ ?_
  · refine (hW.congr' (Eventually.of_forall fun z => ?_)).congr_coeff ?_
    · simp only [binetIntegral, smul_eq_mul]
      exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
    · funext n
      rw [smul_eq_mul, show ((n : ℝ) + 1) = ((n : ℕ) : ℝ) + 1 from rfl,
        Real.Gamma_nat_eq_factorial, binetCoeff,
        show n + 2 = (n + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      have : (n.factorial : ℝ) ≠ 0 := by positivity
      field_simp
      ring
  · refine IntegrableOn.congr_fun (integrableOn_exp_mul_binetBeta_div one_pos)
      (fun t _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul]; ring
  · intro N
    -- `β(t)/t - ∑_{n<N} aₙ tⁿ = (β(t)/t - P_N(t)) + ∑_{N ≤ n < 2N} aₙ tⁿ`
    set C := ∑ n ∈ Finset.Ico N (2 * N), |binetCoeff n| with hC
    refine Asymptotics.IsBigO.of_bound (2 * binetRemConst N + C) ?_
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)]
      with t ht ht1
    have ht0 : (0 : ℝ) < t := ht
    have hpow : ∀ n : ℕ, t ^ ((n : ℝ) + 1 - 1) = t ^ n := fun n => by
      rw [add_sub_cancel_right, Real.rpow_natCast]
    simp only [hpow, smul_eq_mul]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos ht0 N)]
    have hsplit : binetBeta t / t - ∑ n ∈ Finset.range N, t ^ n * binetCoeff n =
        (binetBeta t / t - binetPoly N t) +
          ∑ n ∈ Finset.Ico N (2 * N), binetCoeff n * t ^ n := by
      rw [binetPoly_eq_sum_binetCoeff, ← Finset.sum_range_add_sum_Ico _ (by omega : N ≤ 2 * N)]
      simp only [mul_comm (t ^ _)]
      ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    have h1 : |binetBeta t / t - binetPoly N t| ≤ 2 * binetRemConst N * t ^ N := by
      refine (abs_binetBeta_div_sub_binetPoly_le N ht0).trans ?_
      have hS : 0 ≤ binetRemConst N := tsum_nonneg fun j => by positivity
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht0.le ht1.2.le (by omega))
        (by positivity)
    have h2 : |∑ n ∈ Finset.Ico N (2 * N), binetCoeff n * t ^ n| ≤ C * t ^ N := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [hC, Finset.sum_mul]
      refine Finset.sum_le_sum fun n hn => ?_
      rw [abs_mul, abs_of_pos (pow_pos ht0 n)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht0.le ht1.2.le
        (Finset.mem_Ico.mp hn).1) (abs_nonneg _)
    linarith

/-- Stirling's series for `log Γ` as an asymptotic expansion:
`log Γ(z) - ((z - 1/2) log z - z + ½ log 2π) ~ ∑ₙ B_{n+2}/((n+1)(n+2)) z^{-(n+1)}`. -/
theorem hasAsymptoticExpansion_log_Gamma :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (z : ℝ) => z ^ (-((n : ℝ) + 1)))
      (fun n => (bernoulli (n + 2) : ℝ) / ((n + 1) * (n + 2)))
      (fun z => Real.log (Real.Gamma z) -
        ((z - 1 / 2) * Real.log z - z + (1 / 2) * Real.log (2 * π))) := by
  refine hasAsymptoticExpansion_binetIntegral.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with z hz
  linarith [log_Gamma_eq_add_binetIntegral hz]

end StirlingExpansion

/-- Stirling coefficients, obtained by exponentiating the Bernoulli expansion
of the logarithm of the scaled Gamma function. This recurrence specifies every order. -/
@[dlmf 5.11.E4]
def stirlingG : ℕ → ℂ
  | 0 => 1
  | n + 1 => (∑ k : Fin (n + 1),
      (bernoulli (k.val + 2) : ℂ) / (k.val + 2) * stirlingG (n - k.val)) / (n + 1)
termination_by n => n

/-- DLMF 5.11.9: `|Γ(x + iy)| ~ √(2π) |y|^(x-1/2) e^(-π|y|/2)` as `y → ∞`. -/
@[dlmf 5.11.E9]
theorem norm_Gamma_imag_large {x : ℝ} :
    Asymptotics.IsEquivalent atTop
      (fun y : ℝ => ‖Complex.Gamma (x + I * y)‖)
      (fun y : ℝ => Real.sqrt (2 * π) * |y| ^ (x - 1 / 2) * Real.exp (-π * |y| / 2)) :=
  Asymptotics.isEquivalent_of_tendsto_one (tendsto_norm_Gamma_vertical_div x)

/-- Helper lemma for `Gamma_ratio_power`: the substitution `u = x / t` in the Beta integral
`B(a, t+1)`. -/
theorem cpow_mul_betaIntegral_add_one_eq {a : ℂ} {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ a * betaIntegral a (t + 1) =
      ∫ x : ℝ in 0..t, (((1 - x / t) ^ t : ℝ) : ℂ) * (x : ℂ) ^ (a - 1) := by
  have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hcomp := intervalIntegral.integral_comp_div (a := 0) (b := t)
    (fun u : ℝ => (((1 - u) ^ t : ℝ) : ℂ) * ((u * t : ℝ) : ℂ) ^ (a - 1)) ht.ne'
  simp only [zero_div, div_self ht.ne', div_mul_cancel₀ _ ht.ne'] at hcomp
  rw [hcomp, betaIntegral, real_smul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  have h1 : (1 - (u : ℂ)) ^ ((t : ℂ) + 1 - 1) = (((1 - u) ^ t : ℝ) : ℂ) := by
    rw [add_sub_cancel_right, ofReal_cpow (by linarith [hu.2])]
    push_cast
    rfl
  have h2 : ((u * t : ℝ) : ℂ) ^ (a - 1) = (u : ℂ) ^ (a - 1) * (t : ℂ) ^ (a - 1) := by
    push_cast
    exact mul_cpow_ofReal_nonneg hu.1.le ht.le _
  have h3 : (t : ℂ) ^ a = (t : ℂ) ^ (a - 1) * t := by
    conv_lhs => rw [show a = a - 1 + 1 by ring, cpow_add _ _ htC, cpow_one]
  rw [h1, h2, h3]
  ring

/-- Helper lemma for `Gamma_ratio_power`: `t^a B(a, t+1) → Γ(a)` along real `t → ∞`,
by dominated convergence against the Gamma integrand. -/
theorem tendsto_approx_Gamma_integral_rpow {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun t : ℝ => ∫ x : ℝ in 0..t, (((1 - x / t) ^ t : ℝ) : ℂ) * (x : ℂ) ^ (a - 1))
      atTop (𝓝 (Complex.Gamma a)) := by
  rw [Gamma_eq_integral ha, GammaIntegral]
  let f : ℝ → ℝ → ℂ := fun t =>
    Set.indicator (Set.Ioc 0 t) fun x : ℝ => (((1 - x / t) ^ t : ℝ) : ℂ) * (x : ℂ) ^ (a - 1)
  have hcont (t : ℝ) (ht : 0 < t) :
      Continuous fun x : ℝ => (((1 - x / t) ^ t : ℝ) : ℂ) := by
    have : Continuous fun x : ℝ => (1 - x / t) ^ t :=
      (Real.continuous_rpow_const ht.le).comp (by fun_prop)
    exact continuous_ofReal.comp this
  have f_ible (t : ℝ) (ht : 0 < t) :
      MeasureTheory.Integrable (f t) (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioc, MeasureTheory.IntegrableOn,
      MeasureTheory.Measure.restrict_restrict_of_subset Set.Ioc_subset_Ioi_self,
      ← MeasureTheory.IntegrableOn,
      ← intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
    apply IntervalIntegrable.continuousOn_mul
    · refine intervalIntegral.intervalIntegrable_cpow' ?_
      rwa [sub_re, one_re, ← zero_sub, sub_lt_sub_iff_right]
    · exact (hcont t ht).continuousOn
  have f_tends : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) →
      Tendsto (fun t : ℝ => f t x) atTop
        (𝓝 <| ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (a - 1)) := by
    intro x hx
    apply Tendsto.congr'
    · change ∀ᶠ t : ℝ in atTop, (((1 - x / t) ^ t : ℝ) : ℂ) * (x : ℂ) ^ (a - 1) = f t x
      filter_upwards [eventually_ge_atTop x] with t hxt
      simp only [f]
      rw [Set.indicator_of_mem]
      exact ⟨hx, hxt⟩
    · refine (Tendsto.comp (continuous_ofReal.tendsto _) ?_).mul_const _
      convert Real.tendsto_one_add_div_rpow_exp (-x) using 2 with t
      rw [neg_div, ← sub_eq_add_neg]
  have hbound : ∀ᶠ t : ℝ in atTop, ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ‖f t x‖ ≤ Real.exp (-x) * x ^ (a.re - 1) := by
    filter_upwards [Ioi_mem_atTop 0] with t ht
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    simp only [Set.mem_Ioi, f] at hx ⊢
    rcases lt_or_ge t x with hxt | hxt
    · rw [Set.indicator_of_notMem (Set.notMem_Ioc_of_gt hxt), norm_zero]
      positivity
    · have h0 : 0 ≤ 1 - x / t := sub_nonneg.mpr (div_le_one_of_le₀ hxt ht.le)
      rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hx, hxt⟩), norm_mul,
        Complex.norm_of_nonneg (Real.rpow_nonneg h0 _),
        norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re]
      gcongr
      calc (1 - x / t) ^ t ≤ Real.exp (-x / t) ^ t := by
            have hle : 1 - x / t ≤ Real.exp (-x / t) := by
              rw [neg_div]
              linarith [Real.add_one_le_exp (-(x / t))]
            exact Real.rpow_le_rpow h0 hle (le_of_lt ht)
        _ = Real.exp (-x) := by
            rw [← Real.exp_mul, div_mul_cancel₀ _ ht.ne']
  refine (MeasureTheory.tendsto_integral_filter_of_dominated_convergence _
    (Filter.eventually_of_mem (Ioi_mem_atTop 0) fun t ht => (f_ible t ht).1)
    hbound (Real.GammaIntegral_convergent ha)
    ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (MeasureTheory.ae_of_all _ f_tends))).congr' ?_
  filter_upwards [Ioi_mem_atTop 0] with t ht
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le (le_of_lt ht),
    MeasureTheory.Measure.restrict_restrict_of_subset Set.Ioc_subset_Ioi_self]

/-- Helper lemma for `Gamma_ratio_power`: `Γ(t+a)/(Γ(t) t^a) → 1` for `Re a > 1`. -/
theorem tendsto_Gamma_add_div_Gamma_mul_cpow_of_one_lt_re {a : ℂ} (ha : 1 < a.re) :
    Tendsto (fun t : ℝ => Complex.Gamma (t + a) / (Complex.Gamma t * (t : ℂ) ^ a))
      atTop (𝓝 1) := by
  have ha' : 0 < (a - 1).re := by simp; linarith
  have hG : Complex.Gamma (a - 1) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha'
  have hlim := (tendsto_approx_Gamma_integral_rpow ha').inv₀ hG |>.const_mul (Complex.Gamma (a - 1))
  rw [mul_inv_cancel₀ hG] at hlim
  apply hlim.congr'
  filter_upwards [Ioi_mem_atTop 0] with t ht
  have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
  have ht1 : 0 < ((t : ℂ) + 1).re := by simp; linarith [Set.mem_Ioi.mp ht]
  have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral ha' ht1
  have hGt : Complex.Gamma t ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using ht)
  have hGt1 : Complex.Gamma ((t : ℂ) + 1) = t * Complex.Gamma t := Complex.Gamma_add_one _ htC
  rw [← cpow_mul_betaIntegral_add_one_eq ht]
  have hsum : a - 1 + ((t : ℂ) + 1) = t + a := by ring
  rw [hsum, hGt1] at hB
  have hpow : (t : ℂ) ^ a = (t : ℂ) ^ (a - 1) * t := by
    conv_lhs => rw [show a = a - 1 + 1 by ring, cpow_add _ _ htC, cpow_one]
  have hpow0 : (t : ℂ) ^ (a - 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl htC)
  have hBne : betaIntegral (a - 1) ((t : ℂ) + 1) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hB
    exact mul_ne_zero hG (mul_ne_zero htC hGt) hB
  rw [hpow]
  field_simp
  linear_combination hB

/-- Helper lemma for `Gamma_ratio_power`: `Γ(t+a)/(Γ(t) t^a) → 1` along real `t → ∞`. -/
theorem tendsto_Gamma_add_div_Gamma_mul_cpow (a : ℂ) :
    Tendsto (fun t : ℝ => Complex.Gamma (t + a) / (Complex.Gamma t * (t : ℂ) ^ a))
      atTop (𝓝 1) := by
  suffices h : ∀ n : ℕ, ∀ a : ℂ, 1 < a.re + n →
      Tendsto (fun t : ℝ => Complex.Gamma (t + a) / (Complex.Gamma t * (t : ℂ) ^ a))
        atTop (𝓝 1) by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 - a.re)
    exact h n a (by linarith)
  intro n
  induction n with
  | zero =>
    intro a ha
    exact tendsto_Gamma_add_div_Gamma_mul_cpow_of_one_lt_re (by simpa using ha)
  | succ n ih =>
    intro a ha
    have h1 := ih (a + 1) (by simp; push_cast at ha; linarith)
    have h2 : Tendsto (fun t : ℝ => (1 + a / (t : ℂ))⁻¹) atTop (𝓝 1) := by
      have : Tendsto (fun t : ℝ => a / (t : ℂ)) atTop (𝓝 0) := by
        have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).ofReal.const_mul a
        simpa [div_eq_mul_inv] using this
      simpa using (this.const_add 1).inv₀ (by norm_num)
    have := h1.mul h2
    rw [one_mul] at this
    apply this.congr'
    filter_upwards [Ioi_mem_atTop (max 0 (-a.re))] with t ht
    have ht0 : 0 < t := lt_of_le_of_lt (le_max_left _ _) ht
    have hta : 0 < t + a.re := by linarith [lt_of_le_of_lt (le_max_right _ _) (Set.mem_Ioi.mp ht)]
    have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    have htaC : (t : ℂ) + a ≠ 0 := by
      intro h0
      have := congrArg re h0
      simp at this
      linarith
    have hGt : Complex.Gamma t ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using ht0)
    have hpow0 : (t : ℂ) ^ a ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl htC)
    rw [show (t : ℂ) + (a + 1) = (t + a) + 1 by ring, Complex.Gamma_add_one _ htaC,
      cpow_add _ _ htC, cpow_one]
    field_simp

/-- DLMF 5.11.12: `Γ(t + a)/Γ(t + b) ~ t^(a-b)` as real `t → ∞`. -/
@[dlmf 5.11.E12]
theorem Gamma_ratio_power {a b : ℂ} :
    Tendsto (fun t : ℝ => Complex.Gamma (t + a) / Complex.Gamma (t + b) /
      ((t : ℂ) ^ (a - b))) atTop (𝓝 1) := by
  have h := (tendsto_Gamma_add_div_Gamma_mul_cpow a).div
    (tendsto_Gamma_add_div_Gamma_mul_cpow b) one_ne_zero
  rw [div_one] at h
  apply h.congr'
  filter_upwards [Ioi_mem_atTop 0] with t ht
  have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
  have hGt : Complex.Gamma t ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using ht)
  have hpa : (t : ℂ) ^ a ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl htC)
  have hpb : (t : ℂ) ^ b ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl htC)
  simp only [Pi.div_apply]
  rw [cpow_sub _ _ htC]
  field_simp

/-- Real Stirling: `Γ(x) / (√(2π) e^{-x} x^{x-1/2}) → 1` as `x → ∞`. -/
theorem tendsto_Gamma_div_stirling :
    Tendsto (fun x : ℝ => Real.Gamma x /
      (Real.sqrt (2 * π) * Real.exp (-x) * x ^ (x - 1 / 2))) atTop (𝓝 1) := by
  have h0 := hasAsymptoticExpansion_log_Gamma 0
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero, CharP.cast_eq_zero, zero_add] at h0
  have hlim : Tendsto (fun z : ℝ => Real.log (Real.Gamma z) -
      ((z - 1 / 2) * Real.log z - z + (1 / 2) * Real.log (2 * π))) atTop (𝓝 0) := by
    refine h0.trans_tendsto ?_
    simpa using tendsto_rpow_neg_atTop (zero_lt_one : (0 : ℝ) < 1)
  have he := (Real.continuous_exp.tendsto 0).comp hlim
  rw [Real.exp_zero] at he
  refine he.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hd : Real.sqrt (2 * π) * Real.exp (-x) * x ^ (x - 1 / 2) =
      Real.exp ((x - 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * π)) := by
    rw [Real.exp_add, Real.exp_sub, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx,
      Real.rpow_def_of_pos (by positivity), Real.exp_neg]
    field_simp
  simp only [Function.comp_apply]
  rw [Real.exp_sub, Real.exp_log hG, hd]

/-- DLMF 5.11.7: `Γ(at + b) = O(√(2π) e^(-at) (at)^(at+b-1/2))` as `t → ∞`, for `a > 0`. -/
@[dlmf 5.11.E7]
theorem Gamma_linear_argument {a : ℝ} (ha : 0 < a) {b : ℂ} :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Complex.Gamma (a * t + b) /
        (Real.sqrt (2 * π) * Complex.exp (-(a : ℂ) * t) *
          (a * t : ℂ) ^ (a * t + b - 1 / 2)))
      (fun _ : ℝ => (1 : ℂ)) := by
  have hat : Tendsto (fun t : ℝ => a * t) atTop atTop := tendsto_id.const_mul_atTop ha
  have h1 := (Gamma_ratio_power (a := b) (b := 0)).comp hat
  have h2 := (Complex.continuous_ofReal.tendsto 1).comp (tendsto_Gamma_div_stirling.comp hat)
  have h := h1.mul h2
  rw [one_mul, Complex.ofReal_one] at h
  refine (h.congr' ?_).isBigO_one ℂ
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hs : 0 < a * t := mul_pos ha ht
  have hsC : ((a * t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hG : Complex.Gamma ((a * t : ℝ) : ℂ) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa using hs)
  have hsq : (Real.sqrt (2 * π) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne'
  simp only [Function.comp_apply]
  push_cast [Complex.ofReal_cpow hs.le]
  rw [← Complex.Gamma_ofReal]
  push_cast
  rw [add_zero, sub_zero, show (a : ℂ) * t + b - 1 / 2 = b + ((a : ℂ) * t - 1 / 2) by ring,
    cpow_add _ _ (by exact_mod_cast hsC)]
  have hpa : ((a : ℂ) * t) ^ b ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hsC))
  have hpb : ((a : ℂ) * t) ^ ((a : ℂ) * t - 1 / 2) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hsC))
  have hG' : Complex.Gamma ((a : ℂ) * t) ≠ 0 := by exact_mod_cast hG
  field_simp

/-- Gamma-ratio coefficients, obtained by exponentiating the difference of
Bernoulli-polynomial expansions of `log Γ(z+a)` and `log Γ(z+b)`.
The recurrence defines all orders, including the higher coefficients needed in remainders. -/
@[dlmf 5.11.E15]
def stirlingRatioG (a b : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => (∑ k : Fin (n + 1),
      (-1 : ℂ) ^ k.val *
        (Polynomial.aeval a (Polynomial.bernoulli (k.val + 2)) -
          Polynomial.aeval b (Polynomial.bernoulli (k.val + 2))) / (k.val + 2) *
        stirlingRatioG a b (n - k.val)) / (n + 1)
termination_by n => n

section ShiftedStirling

/-! ### The shifted Stirling expansion and the Gamma-ratio expansion

DLMF 5.11.8 is proved for complex shifts `a` along the positive real axis. Binet's function
is written in Laplace form `μ(t + a) = ∫₀^∞ e^{-ts} e^{-as} β(s)/s ds`, and Watson's lemma
applies to the kernel `e^{-as} β(s)/s`, whose Taylor coefficients at `0⁺` are a Cauchy
product of exponential and Bernoulli coefficients. The elementary part
`(t + a - 1/2) log(1 + a/t) - a` is expanded with `logTaylor`. Collecting coefficients gives
the Bernoulli polynomials. Exponentiating the difference of two such expansions gives
5.11.13 with the coefficients of `stirlingRatioG`. -/

open Set Asymptotics
open scoped Nat

/-! ### Expansions at `0⁺` -/

/-- `f(s) = ∑_{n<N} cₙ sⁿ + O(s^N)` as `s → 0⁺`, for every `N`. -/
def HasSeriesAtZero (f : ℝ → ℂ) (c : ℕ → ℂ) : Prop :=
  ∀ N : ℕ, (fun s : ℝ => f s - ∑ n ∈ Finset.range N, c n * (s : ℂ) ^ n) =O[𝓝[>] 0]
    fun s => s ^ N

/-- `sᴺ` (as a complex number) is `O(sᴺ)` as `s → 0⁺`. -/
theorem isBigO_ofReal_pow (N : ℕ) :
    (fun s : ℝ => (s : ℂ) ^ N) =O[𝓝[>] (0 : ℝ)] fun s => s ^ N :=
  IsBigO.of_bound 1 (Eventually.of_forall fun s => by simp)

/-- A complex polynomial evaluated at real `s` is bounded as `s → 0⁺`. -/
theorem isBigO_polynomial_eval_one (q : Polynomial ℂ) :
    (fun s : ℝ => q.eval (s : ℂ)) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
  have hc : Continuous fun s : ℝ => q.eval (s : ℂ) :=
    q.continuous.comp continuous_ofReal
  exact (hc.continuousAt (x := 0)).tendsto.isBigO_one ℝ |>.mono nhdsWithin_le_nhds

/-- A complex polynomial whose coefficients below degree `N` vanish is `O(sᴺ)` as `s → 0⁺`. -/
theorem isBigO_polynomial_eval_of_coeff (q : Polynomial ℂ) (N : ℕ)
    (h : ∀ m < N, q.coeff m = 0) :
    (fun s : ℝ => q.eval (s : ℂ)) =O[𝓝[>] (0 : ℝ)] fun s => s ^ N := by
  obtain ⟨r, hr⟩ := Polynomial.X_pow_dvd_iff.2 h
  have h1 := (isBigO_ofReal_pow N).mul (isBigO_polynomial_eval_one r)
  refine (h1.congr_left fun s => ?_).congr_right fun s => mul_one _
  rw [hr, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-- A finite power sum `∑_{n<N} cₙ zⁿ` is the evaluation of the truncated power series. -/
theorem sum_range_eq_eval_trunc (c : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    ∑ n ∈ Finset.range N, c n * z ^ n = (PowerSeries.trunc N (PowerSeries.mk c)).eval z := by
  rw [Polynomial.eval, PowerSeries.eval₂_trunc_eq_sum_range]
  simp

/-- A function with an expansion at `0⁺` is bounded near `0⁺`. -/
theorem HasSeriesAtZero.isBigO_one {f : ℝ → ℂ} {c : ℕ → ℂ} (hf : HasSeriesAtZero f c) :
    f =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
  have h := hf 0
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero] at h
  exact h

/-- Expansions at `0⁺` multiply: the coefficients of `f g` are those of the product power series. -/
theorem HasSeriesAtZero.mul {f g : ℝ → ℂ} {c d : ℕ → ℂ} (hf : HasSeriesAtZero f c)
    (hg : HasSeriesAtZero g d) :
    HasSeriesAtZero (fun s => f s * g s)
      (fun n => PowerSeries.coeff n (PowerSeries.mk c * PowerSeries.mk d)) := by
  intro N
  set F := PowerSeries.trunc N (PowerSeries.mk c) with hF
  set G := PowerSeries.trunc N (PowerSeries.mk d) with hG
  have hsum : ∀ s : ℝ, ∑ n ∈ Finset.range N,
      PowerSeries.coeff n (PowerSeries.mk c * PowerSeries.mk d) * (s : ℂ) ^ n =
      (PowerSeries.trunc N ((F * G : Polynomial ℂ) : PowerSeries ℂ)).eval (s : ℂ) := by
    intro s
    rw [Polynomial.coe_mul, hF, hG, PowerSeries.trunc_trunc_mul_trunc, Polynomial.eval,
      PowerSeries.eval₂_trunc_eq_sum_range]
    simp
  have hfF : ∀ s : ℝ, ∑ n ∈ Finset.range N, c n * (s : ℂ) ^ n = F.eval (s : ℂ) := fun s =>
    sum_range_eq_eval_trunc c N s
  have hgG : ∀ s : ℝ, ∑ n ∈ Finset.range N, d n * (s : ℂ) ^ n = G.eval (s : ℂ) := fun s =>
    sum_range_eq_eval_trunc d N s
  have h1 : (fun s : ℝ => (f s - F.eval (s : ℂ)) * g s) =O[𝓝[>] 0] fun s => s ^ N :=
    (((hf N).congr_left fun s => by rw [hfF]).mul hg.isBigO_one).congr_right fun s => mul_one _
  have h2 : (fun s : ℝ => F.eval (s : ℂ) * (g s - G.eval (s : ℂ))) =O[𝓝[>] 0]
      fun s => s ^ N :=
    ((isBigO_polynomial_eval_one F).mul ((hg N).congr_left fun s => by rw [hgG])).congr_right
      fun s => one_mul _
  have h3 : (fun s : ℝ => (F * G - PowerSeries.trunc N ((F * G : Polynomial ℂ) :
      PowerSeries ℂ)).eval (s : ℂ)) =O[𝓝[>] 0] fun s => s ^ N := by
    refine isBigO_polynomial_eval_of_coeff _ N fun m hm => ?_
    simp [Polynomial.coeff_sub, PowerSeries.coeff_trunc, hm, -Polynomial.coe_mul]
  refine ((h1.add h2).add h3).congr_left fun s => ?_
  rw [hsum, Polynomial.eval_sub, Polynomial.eval_mul, ← hfF, ← hgG]
  ring

/-- `A |s| ≤ 1` for all `s` near `0⁺`. -/
theorem eventually_mul_abs_le_one (A : ℝ) : ∀ᶠ s in 𝓝[>] (0 : ℝ), A * |s| ≤ 1 := by
  have h : Tendsto (fun s : ℝ => A * |s|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_const.mul continuous_abs).tendsto (0 : ℝ) (f := fun s : ℝ => A * |s|)
  exact nhdsWithin_le_nhds (h.eventually (Iic_mem_nhds zero_lt_one))

/-- `e^(-as) = ∑ (-a)ⁿ sⁿ/n!` as an expansion at `0⁺`. -/
theorem hasSeriesAtZero_exp (a : ℂ) :
    HasSeriesAtZero (fun s => cexp (-a * s)) (fun n => (-a) ^ n / (n ! : ℂ)) := by
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero]
    have hc : Continuous fun s : ℝ => cexp (-a * s) := by fun_prop
    exact (hc.continuousAt (x := 0)).tendsto.isBigO_one ℝ |>.mono nhdsWithin_le_nhds
  refine IsBigO.of_bound (‖a‖ ^ N * ((N.succ : ℝ) * (N ! * N : ℝ)⁻¹)) ?_
  filter_upwards [eventually_mul_abs_le_one ‖a‖] with s hs
  have hx : ‖-a * (s : ℂ)‖ ≤ 1 := by simpa [norm_mul] using hs
  have hb := Complex.exp_bound hx hN
  have hsum : ∑ m ∈ Finset.range N, (-a * (s : ℂ)) ^ m / (m ! : ℂ) =
      ∑ n ∈ Finset.range N, (-a) ^ n / (n ! : ℂ) * (s : ℂ) ^ n :=
    Finset.sum_congr rfl fun n _ => by rw [mul_pow]; ring
  rw [hsum] at hb
  refine hb.trans (le_of_eq ?_)
  simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, mul_pow, norm_pow]
  ring

/-- `binetPoly N s = ∑_{n<2N} B_{n+2}/(n+2)! sⁿ` (odd Bernoulli numbers beyond `B₁` vanish). -/
theorem binetPoly_eq_sum_range_two_mul (N : ℕ) (s : ℝ) :
    binetPoly N s = ∑ n ∈ Finset.range (2 * N),
      (bernoulli (n + 2) : ℝ) / ((n + 2)! : ℝ) * s ^ n := by
  induction N with
  | zero => simp [binetPoly]
  | succ N ih =>
    rw [binetPoly_eq_range] at ih ⊢
    rw [Finset.sum_range_succ, ih, show 2 * (N + 1) = 2 * N + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ,
      bernoulli_eq_zero_of_odd (n := 2 * N + 1 + 2) ⟨N + 1, by ring⟩ (by omega)]
    simp only [Rat.cast_zero, zero_div, zero_mul, add_zero]

/-- `β(s)/s` has the expansion `∑ B_{n+2}/(n+2)! sⁿ` at `0⁺`. -/
theorem hasSeriesAtZero_binetBeta_div :
    HasSeriesAtZero (fun s => ((binetBeta s / s : ℝ) : ℂ))
      (fun n => ((bernoulli (n + 2) : ℚ) : ℂ) / ((n + 2)! : ℂ)) := by
  intro N
  set c : ℕ → ℂ := fun n => ((bernoulli (n + 2) : ℚ) : ℂ) / ((n + 2)! : ℂ) with hc
  have hP : ∀ s : ℝ, ((binetPoly N s : ℝ) : ℂ) = ∑ n ∈ Finset.range (2 * N), c n * (s : ℂ) ^ n :=
    fun s => by rw [binetPoly_eq_sum_range_two_mul]; push_cast; rfl
  -- the Bernoulli remainder
  have h1 : (fun s : ℝ => ((binetBeta s / s - binetPoly N s : ℝ) : ℂ)) =O[𝓝[>] 0]
      fun s => s ^ N := by
    refine IsBigO.of_bound (2 * binetRemConst N) ?_
    filter_upwards [self_mem_nhdsWithin, eventually_mul_abs_le_one 1] with s hs hs1
    have hs' : (0 : ℝ) < s := hs
    have hs1' : s ≤ 1 := by simpa [abs_of_pos hs'] using hs1
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hs' N)]
    refine (abs_binetBeta_div_sub_binetPoly_le N hs').trans ?_
    have hS : 0 ≤ binetRemConst N := tsum_nonneg fun m => by positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs'.le hs1' (by omega))
      (by positivity)
  -- the tail of the polynomial
  have h2 : (fun s : ℝ => ∑ n ∈ Finset.range (2 * N), c n * (s : ℂ) ^ n -
      ∑ n ∈ Finset.range N, c n * (s : ℂ) ^ n) =O[𝓝[>] 0] fun s => s ^ N := by
    simp_rw [sum_range_eq_eval_trunc, ← Polynomial.eval_sub]
    refine isBigO_polynomial_eval_of_coeff _ N fun m hm => ?_
    simp [Polynomial.coeff_sub, PowerSeries.coeff_trunc, hm, show m < 2 * N by omega]
  refine (h1.add h2).congr_left fun s => ?_
  rw [← hP]
  push_cast
  ring

/-! ### The Laplace form of `μ` for complex arguments -/

/-- The Laplace integrand `e^{-ws} β(s)/s`. -/
theorem integrableOn_cexp_mul_binetBeta_div {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun s : ℝ => cexp (-w * s) * ((binetBeta s / s : ℝ) : ℂ)) (Ioi 0) := by
  refine (integrableOn_exp_mul_binetBeta_div hw).norm.mono' ?_ ?_
  · refine ((by fun_prop : Continuous fun s : ℝ => cexp (-w * s)).continuousOn.mul
      (continuous_ofReal.comp_continuousOn (continuousOn_binetBeta.div continuousOn_id
        fun t ht => ne_of_gt ht))).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
    have hs' : (0 : ℝ) < s := hs
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (mul_nonneg (Real.exp_pos _).le (binetBeta_nonneg hs'))
        hs'.le), abs_of_nonneg (div_nonneg (binetBeta_nonneg hs') hs'.le)]
    simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    rw [mul_div_assoc]

/-- `|β(s)/s| ≤ 1/12` for `s > 0`. -/
theorem norm_binetBeta_div_le {s : ℝ} (hs : 0 < s) : ‖((binetBeta s / s : ℝ) : ℂ)‖ ≤ 1 / 12 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (binetBeta_nonneg hs)
    hs.le), div_le_iff₀ hs]
  linarith [binetBeta_le hs]

/-- The Laplace transform `w ↦ ∫₀^∞ e^(-ws) β(s)/s ds` is differentiable in `w` for `Re w > 0`, with
derivative under the integral sign. -/
theorem hasDerivAt_laplace_binetMu {w₀ : ℂ} (hw₀ : 0 < w₀.re) :
    HasDerivAt (fun w : ℂ => ∫ s in Ioi (0 : ℝ), cexp (-w * s) * ((binetBeta s / s : ℝ) : ℂ))
      (∫ s in Ioi (0 : ℝ), -(s : ℂ) * cexp (-w₀ * s) * ((binetBeta s / s : ℝ) : ℂ)) w₀ := by
  set σ := w₀.re / 2 with hσ
  have hσ0 : 0 < σ := by positivity
  have hball : ∀ w ∈ Metric.ball w₀ σ, σ < w.re := fun w hw => by
    have h1 : |w.re - w₀.re| < σ := by
      have := abs_re_le_norm (w - w₀)
      rw [sub_re] at this
      exact lt_of_le_of_lt this (by simpa [dist_eq_norm] using hw)
    have := neg_abs_le (w.re - w₀.re)
    linarith
  have hk : Measurable fun s : ℝ => ((binetBeta s / s : ℝ) : ℂ) := by
    refine continuous_ofReal.measurable.comp ?_
    unfold binetBeta
    fun_prop
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds w₀ hσ0)
    (μ := volume.restrict (Ioi 0))
    (F := fun w s => cexp (-w * s) * ((binetBeta s / s : ℝ) : ℂ))
    (F' := fun w s => -(s : ℂ) * cexp (-w * s) * ((binetBeta s / s : ℝ) : ℂ))
    (bound := fun s => (1 / 12) * (Real.exp (-σ * s) * s ^ 1)) ?_
    (integrableOn_cexp_mul_binetBeta_div hw₀) ?_ ?_
    ((integrableOn_exp_mul_pow hσ0 1).const_mul _) ?_).2
  · exact Eventually.of_forall fun w =>
      ((by fun_prop : Continuous fun s : ℝ => cexp (-w * s)).measurable.mul
        hk).aestronglyMeasurable
  · exact (((by fun_prop : Continuous fun s : ℝ => -(s : ℂ) * cexp (-w₀ * s)).measurable.mul
      hk)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs w hw
    have hs' : (0 : ℝ) < s := hs
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs',
      Complex.norm_exp]
    have he : Real.exp (-w * s : ℂ).re ≤ Real.exp (-σ * s) := by
      apply Real.exp_le_exp.2
      simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      nlinarith [hball w hw]
    have hb := norm_binetBeta_div_le hs'
    calc s * Real.exp (-w * s : ℂ).re * ‖((binetBeta s / s : ℝ) : ℂ)‖
        ≤ s * Real.exp (-σ * s) * (1 / 12) := by gcongr
      _ = (1 / 12) * (Real.exp (-σ * s) * s ^ 1) := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs w hw
    have h := (((hasDerivAt_id w).neg.mul_const (s : ℂ)).cexp).mul_const
      ((binetBeta s / s : ℝ) : ℂ)
    convert h using 1
    · ext v; simp
    · simp only [Pi.neg_apply, id]; ring

/-- The Laplace form `μ(w) = ∫₀^∞ e^{-ws} β(s)/s ds` for `Re w > 0` (Temme (3.27)). -/
theorem binetMu_eq_laplace {w : ℂ} (hw : 0 < w.re) :
    binetMu w = ∫ s in Ioi (0 : ℝ), cexp (-w * s) * ((binetBeta s / s : ℝ) : ℂ) := by
  set U : Set ℂ := {w | 0 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUs : U ⊆ slitPlane := fun w hw => mem_slitPlane_iff.2 (Or.inl hw)
  have h1 : AnalyticOnNhd ℂ binetMu U :=
    (differentiableOn_binetMu.mono hUs).analyticOnNhd hUo
  have h2 : AnalyticOnNhd ℂ (fun w : ℂ =>
      ∫ s in Ioi (0 : ℝ), cexp (-w * s) * ((binetBeta s / s : ℝ) : ℂ)) U :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      (hasDerivAt_laplace_binetMu hw).differentiableAt.differentiableWithinAt) hUo
  refine h1.eqOn_of_preconnected_of_frequently_eq h2
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 1) (by simp [hU]) ?_ hw
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] 1, binetMu x =
      ∫ s in Ioi (0 : ℝ), cexp (-(x : ℂ) * s) * ((binetBeta s / s : ℝ) : ℂ) := by
    filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds one_pos)] with x hx
    rw [binetMu_ofReal, binetMuReal_eq_binetIntegral hx, binetIntegral, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    push_cast
    ring_nf
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 1) (𝓝[≠] 1) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun x hx => by
      simpa using hx
  exact ht.frequently hev.frequently

/-- Watson's lemma for `μ(t + a)`, `t → +∞`. -/
theorem hasAsymptoticExpansion_binetMu_add (a : ℂ) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (t : ℝ) => t ^ (-((n : ℝ) + 1)))
      (fun n => Real.Gamma ((n : ℝ) + 1) • PowerSeries.coeff n
        (PowerSeries.mk (fun n => (-a) ^ n / (n ! : ℂ)) *
          PowerSeries.mk (fun n => ((bernoulli (n + 2) : ℚ) : ℂ) / ((n + 2)! : ℂ))))
      (fun t => binetMu (t + a)) := by
  set F : ℝ → ℂ := fun s => cexp (-a * s) * ((binetBeta s / s : ℝ) : ℂ) with hF
  have hser := (hasSeriesAtZero_exp a).mul hasSeriesAtZero_binetBeta_div
  have hint : IntegrableOn (fun s => Real.exp (-(‖a‖ + 1) * s) • F s) (Ioi 0) := by
    have hre : 0 < (((‖a‖ + 1 : ℝ) : ℂ) + a).re := by
      simp only [add_re, ofReal_re]
      linarith [neg_abs_le a.re, abs_re_le_norm a]
    refine (integrableOn_cexp_mul_binetBeta_div hre).congr_fun (fun s _ => ?_)
      measurableSet_Ioi
    simp only [hF, real_smul, ofReal_exp]
    rw [← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  have hW := hasAsymptoticExpansion_integral_exp_smul (μ := 1) one_pos hint (fun N => by
    refine ((hser N).congr_left fun s => ?_).congr_right fun s => ?_
    · simp only [hF, add_sub_cancel_right, Real.rpow_natCast, real_smul]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      push_cast
      ring
    · simp [Real.rpow_natCast])
  refine hW.congr' ?_
  filter_upwards [eventually_gt_atTop ‖a‖] with t ht
  have hre : 0 < ((t : ℂ) + a).re := by
    simp only [add_re, ofReal_re]
    linarith [neg_abs_le a.re, abs_re_le_norm a]
  rw [binetMu_eq_laplace hre]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [hF, real_smul, ofReal_exp]
  rw [← mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf

/-! ### The elementary part of the shifted Stirling expansion -/

/-- `(t + a - 1/2)(log(t + a) - log t) - a`. -/
def stirlingLogPart (a : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) + a - 1 / 2) * (log ((t : ℂ) + a) - log t) - a

/-- Coefficients of `stirlingLogPart`. -/
def stirlingLogCoeff (a : ℂ) (n : ℕ) : ℂ :=
  (-1) ^ n * (a ^ (n + 2) / ((n + 1) * (n + 2)) - a ^ (n + 1) / (2 * (n + 1)))

/-- The `m`-th coefficient of the truncation to degree `< M` of `mk f` is `f m` if `m < M` and `0`
otherwise. -/
theorem coeff_trunc_mk (f : ℕ → ℂ) (M m : ℕ) :
    (PowerSeries.trunc M (PowerSeries.mk f)).coeff m = if m < M then f m else 0 := by
  simp [PowerSeries.coeff_trunc]

/-- `t (t⁻¹)^(N+2) = t^(-(N+1))` eventually as `t → ∞`. -/
theorem isBigO_rpow_neg_of_recip_pow (N : ℕ) :
    (fun t : ℝ => t * (t⁻¹) ^ (N + 2)) =ᶠ[atTop] fun t => t ^ (-((N : ℝ) + 1)) := by
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [Real.rpow_neg ht.le, show (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, inv_pow, pow_succ _ (N + 1)]
  field_simp

/-- The elementary part `(t + a - 1/2)(log(t + a) - log t) - a` has an asymptotic expansion in
powers `t^(-(n+1))` with coefficients `stirlingLogCoeff a`. -/
theorem hasAsymptoticExpansion_stirlingLogPart (a : ℂ) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (t : ℝ) => t ^ (-((n : ℝ) + 1)))
      (stirlingLogCoeff a) (stirlingLogPart a) := by
  intro N
  set lc : ℕ → ℂ := fun j => (-1) ^ (j + 1) * a ^ j / j with hlc
  set Q : Polynomial ℂ := (1 + Polynomial.C (a - 1 / 2) * Polynomial.X) *
      PowerSeries.trunc (N + 2) (PowerSeries.mk lc) - Polynomial.C a * Polynomial.X -
      Polynomial.X ^ 2 * PowerSeries.trunc N (PowerSeries.mk (stirlingLogCoeff a)) with hQ
  have hQc : ∀ m < N + 2, Q.coeff m = 0 := by
    intro m hm
    have hmul : ∀ P : Polynomial ℂ, ((1 + Polynomial.C (a - 1 / 2) * Polynomial.X) * P) =
        P + Polynomial.C (a - 1 / 2) * (Polynomial.X * P) := fun P => by ring
    rw [hQ, Polynomial.coeff_sub, Polynomial.coeff_sub, hmul, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, Polynomial.coeff_C_mul_X, Polynomial.coeff_X_pow_mul']
    rcases m with _ | _ | k
    · simp [hlc, coeff_trunc_mk]
    · simp [hlc, coeff_trunc_mk]
    · rw [Polynomial.coeff_X_mul, coeff_trunc_mk, coeff_trunc_mk, coeff_trunc_mk]
      simp only [show k + 1 + 1 < N + 2 from hm, show k + 1 < N + 2 by omega,
        show k + 1 + 1 ≠ 1 by omega, show 2 ≤ k + 1 + 1 by omega,
        show k + 1 + 1 - 2 = k by omega, show k < N by omega, ite_true, ite_false]
      simp only [hlc, stirlingLogCoeff]
      push_cast
      have h1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      have h2 : (k : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k + 1)
      have h2' : (k : ℂ) + 2 ≠ 0 := by
        rw [show (k : ℂ) + 2 = k + 1 + 1 by ring]; exact h2
      field_simp
      ring
  -- the polynomial part
  have hQO : (fun t : ℝ => (t : ℂ) * Q.eval ((t⁻¹ : ℝ) : ℂ)) =O[atTop]
      fun t => t ^ (-((N : ℝ) + 1)) := by
    have h1 := (isBigO_polynomial_eval_of_coeff Q (N + 2) hQc).comp_tendsto
      tendsto_inv_atTop_nhdsGT_zero
    have h2 : (fun t : ℝ => (t : ℂ)) =O[atTop] fun t => t :=
      IsBigO.of_bound 1 (Eventually.of_forall fun t => by simp)
    exact ((h2.mul h1).trans_eventuallyEq (isBigO_rpow_neg_of_recip_pow N))
  -- the logarithm remainder
  have hz : Tendsto (fun t : ℝ => a / (t : ℂ)) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
      have h := (continuous_ofReal.tendsto 0).comp (tendsto_inv_atTop_zero (𝕜 := ℝ))
      simpa only [Function.comp_def, ofReal_zero] using h
    simpa [div_eq_mul_inv] using this.const_mul a
  have hlogO : (fun t : ℝ => ((t : ℂ) + a - 1 / 2) *
      (log (1 + a / t) - logTaylor (N + 2) (a / t))) =O[atTop]
      fun t => t ^ (-((N : ℝ) + 1)) := by
    have h1 := (log_sub_logTaylor_isBigO (N + 1)).comp_tendsto hz
    have h1' : (fun t : ℝ => log (1 + a / t) - logTaylor (N + 2) (a / t)) =O[atTop]
        fun t : ℝ => (t⁻¹) ^ (N + 2) := by
      refine h1.trans (IsBigO.of_bound (‖a‖ ^ (N + 2)) ?_)
      filter_upwards [eventually_gt_atTop 0] with t ht
      simp only [Function.comp, norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht, inv_pow, abs_inv, abs_pow]
      exact le_of_eq (by rw [div_pow]; ring)
    have h2 : (fun t : ℝ => (t : ℂ) + a - 1 / 2) =O[atTop] fun t => t := by
      refine IsBigO.of_bound (2 + ‖a‖) ?_
      filter_upwards [eventually_ge_atTop 1] with t ht
      have : ‖(t : ℂ) + a - 1 / 2‖ ≤ t + ‖a‖ + 1 / 2 := by
        refine (norm_sub_le _ _).trans ?_
        have := norm_add_le (t : ℂ) a
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < t)]
          at this
        norm_num
        linarith
      rw [Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < t)]
      nlinarith [norm_nonneg a]
    exact (h2.mul h1').trans_eventuallyEq (isBigO_rpow_neg_of_recip_pow N)
  refine (hlogO.add hQO).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_gt_atTop (2 * ‖a‖)] with t ht
  have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have hlt : ‖a / (t : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, div_lt_one ht0]
    linarith [norm_nonneg a]
  have h1 : (1 : ℂ) + a / t ≠ 0 := fun h => by
    have : a / (t : ℂ) = -1 := by linear_combination h
    rw [this] at hlt; simp at hlt
  have hlog : log ((t : ℂ) + a) - log t = log (1 + a / t) := by
    rw [show (t : ℂ) + a = (t : ℂ) * (1 + a / t) by field_simp, log_ofReal_mul ht0 h1,
      ← ofReal_log ht0.le]
    ring
  simp only [stirlingLogPart, hlog, hQ, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow, ← sum_range_eq_eval_trunc, logTaylor, hlc, real_smul]
  have e1 : ∑ j ∈ Finset.range (N + 2), (-1) ^ (j + 1) * (a / (t : ℂ)) ^ j / (j : ℂ) =
      ∑ n ∈ Finset.range (N + 2), (-1) ^ (n + 1) * a ^ n / (n : ℂ) * ((t⁻¹ : ℝ) : ℂ) ^ n :=
    Finset.sum_congr rfl fun n _ => by rw [div_pow]; push_cast; ring
  have e2 : ∑ x ∈ Finset.range N, ((t ^ (-((x : ℝ) + 1)) : ℝ) : ℂ) * stirlingLogCoeff a x =
      (t : ℂ) * (((t⁻¹ : ℝ) : ℂ) ^ 2 *
        ∑ n ∈ Finset.range N, stirlingLogCoeff a n * ((t⁻¹ : ℝ) : ℂ) ^ n) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Real.rpow_neg ht0.le, show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
    push_cast
    simp only [inv_pow]
    field_simp
    ring
  rw [e1, e2]
  generalize ∑ n ∈ Finset.range (N + 2), (-1) ^ (n + 1) * a ^ n / (n : ℂ) *
    ((t⁻¹ : ℝ) : ℂ) ^ n = S1
  generalize ∑ n ∈ Finset.range N, stirlingLogCoeff a n * ((t⁻¹ : ℝ) : ℂ) ^ n = S2
  push_cast
  field_simp
  ring

/-! ### The shifted Stirling expansion (DLMF 5.11.8) -/

/-- The coefficients `(-1)ⁿ B_{n+2}(a)/((n+1)(n+2))` of DLMF 5.11.8. -/
def stirlingShiftCoeff (a : ℂ) (n : ℕ) : ℂ :=
  (-1) ^ n * Polynomial.aeval a (Polynomial.bernoulli (n + 2)) / ((n + 1) * (n + 2))

/-- `Bₙ(a) = ∑_{i≤n} Bᵢ C(n, i) a^(n-i)`. -/
theorem aeval_bernoulli_eq_sum (a : ℂ) (n : ℕ) :
    Polynomial.aeval a (Polynomial.bernoulli n) =
      ∑ i ∈ Finset.range (n + 1), ((bernoulli i : ℚ) : ℂ) * (n.choose i : ℂ) * a ^ (n - i) := by
  simp [Polynomial.bernoulli, map_sum, Polynomial.aeval_monomial]

/-- `(-1)^k B_{k+2} = B_{k+2}` (odd Bernoulli numbers beyond `B₁` vanish). -/
theorem neg_one_pow_mul_bernoulli_add_two (k : ℕ) :
    (-1 : ℂ) ^ k * ((bernoulli (k + 2) : ℚ) : ℂ) = ((bernoulli (k + 2) : ℚ) : ℂ) := by
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_one_pow, one_mul]
  · rw [bernoulli_eq_zero_of_odd (hk.add_even even_two) (by omega)]
    simp

/-- The coefficients of the elementary and the Laplace parts add up to the coefficients `(-1)ⁿ
B_{n+2}(a)/((n+1)(n+2))` of DLMF 5.11.8. -/
theorem stirlingLogCoeff_add_coeff (a : ℂ) (n : ℕ) :
    stirlingLogCoeff a n + Real.Gamma ((n : ℝ) + 1) • PowerSeries.coeff n
        (PowerSeries.mk (fun n => (-a) ^ n / (n ! : ℂ)) *
          PowerSeries.mk (fun n => ((bernoulli (n + 2) : ℚ) : ℂ) / ((n + 2)! : ℂ))) =
      stirlingShiftCoeff a n := by
  rw [PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap, PowerSeries.coeff_mk]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
    (-a) ^ j / (j ! : ℂ) * (((bernoulli (i + 2) : ℚ) : ℂ) / ((i + 2)! : ℂ))),
    Real.Gamma_nat_eq_factorial, stirlingShiftCoeff, aeval_bernoulli_eq_sum, real_smul,
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hn2 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
  have hterm : ∀ k ∈ Finset.range n.succ, (((n ! : ℝ)) : ℂ) * ((-a) ^ (n - k) /
      ((n - k) ! : ℂ) * (((bernoulli (k + 2) : ℚ) : ℂ) / ((k + 2)! : ℂ))) =
      (-1) ^ n / ((n + 1) * (n + 2)) * (((bernoulli (k + 1 + 1) : ℚ) : ℂ) *
        ((n + 2).choose (k + 1 + 1) : ℂ) * a ^ (n + 2 - (k + 1 + 1))) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hch := Nat.choose_mul_factorial_mul_factorial (show k + 2 ≤ n + 2 by omega)
    rw [show n + 2 - (k + 2) = n - k by omega] at hch
    have hchC : ((n + 2).choose (k + 2) : ℂ) * ((k + 2)! : ℂ) * ((n - k)! : ℂ) =
        ((n + 2)! : ℂ) := by exact_mod_cast hch
    have hfac : ((n + 2)! : ℂ) = ((n : ℂ) + 2) * ((n : ℂ) + 1) * (n ! : ℂ) := by
      push_cast [Nat.factorial_succ]; ring
    have hk1 : ((k + 2)! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hk2 : ((n - k)! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hchoose : ((n + 2).choose (k + 2) : ℂ) =
        ((n : ℂ) + 2) * ((n : ℂ) + 1) * (n ! : ℂ) / (((k + 2)! : ℂ) * ((n - k)! : ℂ)) := by
      rw [eq_div_iff (mul_ne_zero hk1 hk2), ← hfac, ← hchC]
      ring
    have hpow : (-1 : ℂ) ^ (n - k) * ((bernoulli (k + 2) : ℚ) : ℂ) =
        (-1) ^ n * ((bernoulli (k + 2) : ℚ) : ℂ) := by
      calc (-1 : ℂ) ^ (n - k) * ((bernoulli (k + 2) : ℚ) : ℂ)
          = (-1) ^ (n - k) * ((-1) ^ k * ((bernoulli (k + 2) : ℚ) : ℂ)) := by
            rw [neg_one_pow_mul_bernoulli_add_two]
        _ = (-1) ^ n * ((bernoulli (k + 2) : ℚ) : ℂ) := by
            rw [← mul_assoc, ← pow_add, show n - k + k = n by omega]
    rw [show n + 2 - (k + 1 + 1) = n - k by omega, show k + 1 + 1 = k + 2 by ring, hchoose,
      neg_pow, Complex.ofReal_natCast]
    rw [show (n ! : ℂ) * ((-1) ^ (n - k) * a ^ (n - k) / ((n - k)! : ℂ) *
        (((bernoulli (k + 2) : ℚ) : ℂ) / ((k + 2)! : ℂ))) =
        (n ! : ℂ) * a ^ (n - k) / (((n - k)! : ℂ) * ((k + 2)! : ℂ)) *
          ((-1) ^ (n - k) * ((bernoulli (k + 2) : ℚ) : ℂ)) by ring, hpow]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  generalize ∑ k ∈ Finset.range n.succ, ((bernoulli (k + 1 + 1) : ℚ) : ℂ) *
    ((n + 2).choose (k + 1 + 1) : ℂ) * a ^ (n + 2 - (k + 1 + 1)) = S
  simp only [stirlingLogCoeff, bernoulli_zero, bernoulli_one, Nat.choose_zero_right,
    Nat.choose_one_right, zero_add, Nat.sub_zero]
  rw [show n + 2 - 1 = n + 1 by omega]
  push_cast
  field_simp
  ring

/-- `B(t + a) - ((t + a - 1/2) log t - t + (1/2) log 2π)`, with `B` the Binet exponent. -/
def stirlingShiftRem (a : ℂ) (t : ℝ) : ℂ :=
  binetExponent (t + a) - (((t : ℂ) + a - 1 / 2) * log t - t + (1 / 2) * log (2 * π))

/-- The shifted Stirling remainder is the elementary part plus `μ(t + a)`. -/
theorem stirlingShiftRem_eq (a : ℂ) :
    stirlingShiftRem a = stirlingLogPart a + fun t : ℝ => binetMu ((t : ℂ) + a) := by
  funext t
  simp only [stirlingShiftRem, stirlingLogPart, binetExponent, Pi.add_apply]
  ring

/-- DLMF 5.11.8: `log Γ(t + a) ~ (t + a - 1/2) log t - t + (1/2) log 2π
  + ∑ (-1)ⁿ B_{n+2}(a)/((n+1)(n+2)) t^{-(n+1)}`, with `log Γ` the Binet exponent. -/
theorem hasAsymptoticExpansion_stirlingShiftRem (a : ℂ) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (t : ℝ) => t ^ (-((n : ℝ) + 1)))
      (stirlingShiftCoeff a) (stirlingShiftRem a) := by
  rw [stirlingShiftRem_eq]
  refine ((hasAsymptoticExpansion_stirlingLogPart a).add
    (hasAsymptoticExpansion_binetMu_add a)).congr_coeff ?_
  funext n
  exact stirlingLogCoeff_add_coeff a n

/-! ### Exponentiating an asymptotic expansion -/

/-- If `(n+1) Gₙ₊₁ = ∑_{k ≤ n} (k+1) dₖ G_{n-k}` and `G₀ = 1`, then
`exp(∑_{k<N} dₖ x^{k+1}) = ∑_{k ≤ N} Gₖ xᵏ + O(x^{N+1})` as `x → 0⁺`. -/
theorem cexp_poly_sub_isBigO (d G : ℕ → ℂ) (hG0 : G 0 = 1)
    (hG : ∀ n : ℕ, ((n : ℂ) + 1) * G (n + 1) =
      ∑ k ∈ Finset.range (n + 1), ((k : ℂ) + 1) * d k * G (n - k)) (N : ℕ) :
    (fun x : ℝ => cexp (∑ k ∈ Finset.range N, d k * (x : ℂ) ^ (k + 1)) -
      ∑ k ∈ Finset.range (N + 1), G k * (x : ℂ) ^ k) =O[𝓝[>] 0] fun x => x ^ (N + 1) := by
  set P : Polynomial ℂ := Polynomial.X * PowerSeries.trunc N (PowerSeries.mk d) with hP
  set E : Polynomial ℂ := PowerSeries.trunc (N + 1) (PowerSeries.mk G) with hE
  have hPe : ∀ z : ℂ, P.eval z = ∑ k ∈ Finset.range N, d k * z ^ (k + 1) := fun z => by
    rw [hP, Polynomial.eval_mul, Polynomial.eval_X, ← sum_range_eq_eval_trunc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hEe : ∀ z : ℂ, E.eval z = ∑ k ∈ Finset.range (N + 1), G k * z ^ k := fun z =>
    (sum_range_eq_eval_trunc G (N + 1) z).symm
  set D : Polynomial ℂ := Polynomial.derivative E - Polynomial.derivative P * E with hD
  have hDc : ∀ m < N, D.coeff m = 0 := by
    intro m hm
    rw [hD, Polynomial.coeff_sub, Polynomial.coeff_derivative, Polynomial.coeff_mul, hE,
      coeff_trunc_mk]
    simp only [show m + 1 < N + 1 by omega, ↓reduceIte]
    have hsum : ∑ x ∈ Finset.antidiagonal m, (Polynomial.derivative P).coeff x.1 *
        (PowerSeries.trunc (N + 1) (PowerSeries.mk G)).coeff x.2 =
        ∑ x ∈ Finset.antidiagonal m, ((x.1 : ℂ) + 1) * d x.1 * G x.2 := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := Finset.mem_antidiagonal.1 hx
      rw [Polynomial.coeff_derivative, hP, Polynomial.coeff_X_mul, coeff_trunc_mk,
        coeff_trunc_mk]
      simp only [show x.1 < N by omega, show x.2 < N + 1 by omega, ↓reduceIte]
      ring
    rw [hsum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => ((i : ℂ) + 1) * d i * G j), ← hG m]
    ring
  obtain ⟨R, hR⟩ := Polynomial.X_pow_dvd_iff.2 hDc
  have hDe : ∀ z : ℂ, D.eval z = z ^ N * R.eval z := fun z => by
    rw [hR, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  set h : ℝ → ℂ := fun x => cexp (-P.eval (x : ℂ)) * E.eval (x : ℂ) with hh
  have hderiv : ∀ x : ℝ, HasDerivAt h (cexp (-P.eval (x : ℂ)) * D.eval (x : ℂ)) x := by
    intro x
    have hP' : HasDerivAt (fun y : ℝ => P.eval (y : ℂ)) ((Polynomial.derivative P).eval x) x :=
      (P.hasDerivAt (x : ℂ)).comp_ofReal
    have hE' : HasDerivAt (fun y : ℝ => E.eval (y : ℂ)) ((Polynomial.derivative E).eval x) x :=
      (E.hasDerivAt (x : ℂ)).comp_ofReal
    convert (hP'.neg.cexp).mul hE' using 1
    have : D.eval (x : ℂ) = (Polynomial.derivative E).eval (x : ℂ) -
        (Polynomial.derivative P).eval (x : ℂ) * E.eval (x : ℂ) := by
      rw [hD, Polynomial.eval_sub, Polynomial.eval_mul]
    rw [this]
    simp only [Pi.neg_apply]
    ring
  -- bounds on `[0, 1]`
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    (f := fun y : ℝ => cexp (-P.eval (y : ℂ)) * R.eval (y : ℂ))
    (by fun_prop)
  obtain ⟨K, hK⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    (f := fun y : ℝ => cexp (P.eval (y : ℂ))) (by fun_prop)
  have hh0 : h 0 = 1 := by
    simp only [hh, ofReal_zero, ← Polynomial.coeff_zero_eq_eval_zero, hP, hE,
      Polynomial.coeff_X_mul_zero, neg_zero, Complex.exp_zero, one_mul, coeff_trunc_mk]
    simp [hG0]
  refine IsBigO.of_bound (K * M) ?_
  filter_upwards [self_mem_nhdsWithin, eventually_mul_abs_le_one 1] with x hx hx1
  have hx0 : (0 : ℝ) < x := hx
  have hx1' : x ≤ 1 := by simpa [abs_of_pos hx0] using hx1
  have hMV := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := x) (f := h)
    (C := M * x ^ N) (fun y _ => (hderiv y).hasDerivWithinAt) (fun y hy => by
      rw [hDe, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hy.1]
      have h1 := hM y ⟨hy.1, by linarith [hy.2, hx1']⟩
      rw [norm_mul] at h1
      have h2 : y ^ N ≤ x ^ N := pow_le_pow_left₀ hy.1 hy.2.le N
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
      calc ‖cexp (-P.eval (y : ℂ))‖ * (y ^ N * ‖R.eval (y : ℂ)‖)
          = y ^ N * (‖cexp (-P.eval (y : ℂ))‖ * ‖R.eval (y : ℂ)‖) := by ring
        _ ≤ x ^ N * M := mul_le_mul h2 h1 (by positivity) (by positivity)
        _ = M * x ^ N := by ring) x ⟨hx0.le, le_rfl⟩
  rw [hh0, sub_zero] at hMV
  have hKx := hK x ⟨hx0.le, hx1'⟩
  have heq : cexp (∑ k ∈ Finset.range N, d k * (x : ℂ) ^ (k + 1)) -
      ∑ k ∈ Finset.range (N + 1), G k * (x : ℂ) ^ k =
      cexp (P.eval (x : ℂ)) * (1 - h x) := by
    have hhx : h x = cexp (-P.eval (x : ℂ)) * E.eval (x : ℂ) := rfl
    rw [hhx, ← hPe, ← hEe, mul_sub, mul_one, ← mul_assoc, ← Complex.exp_add]
    simp
  rw [heq, norm_mul, Real.norm_eq_abs, abs_of_pos (pow_pos hx0 _), norm_sub_rev]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  calc ‖cexp (P.eval (x : ℂ))‖ * ‖h x - 1‖ ≤ K * (M * x ^ N * x) :=
        mul_le_mul hKx hMV (norm_nonneg _) ((norm_nonneg _).trans hKx)
    _ = K * M * x ^ (N + 1) := by ring

/-- `t^(-(n+1)) = (t⁻¹)^(n+1)` for `t > 0`. -/
theorem rpow_neg_add_one_eq_recip_pow {t : ℝ} (ht : 0 < t) (n : ℕ) :
    t ^ (-((n : ℝ) + 1)) = (t⁻¹) ^ (n + 1) := by
  rw [Real.rpow_neg ht.le, show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, inv_pow]

/-- Exponentiation of an asymptotic expansion in powers of `1/t` without constant term. -/
theorem isBigO_cexp_sub_of_hasAsymptoticExpansion {L : ℝ → ℂ} {d G : ℕ → ℂ}
    (hL : HasAsymptoticExpansion atTop (fun (n : ℕ) (t : ℝ) => t ^ (-((n : ℝ) + 1))) d L)
    (hG0 : G 0 = 1)
    (hG : ∀ n : ℕ, ((n : ℂ) + 1) * G (n + 1) =
      ∑ k ∈ Finset.range (n + 1), ((k : ℂ) + 1) * d k * G (n - k)) (N : ℕ) :
    (fun t => cexp (L t) - ∑ k ∈ Finset.range (N + 1), G k * ((t⁻¹ : ℝ) : ℂ) ^ k) =O[atTop]
      fun t => t ^ (-((N : ℝ) + 1)) := by
  set Pd : ℝ → ℂ := fun x => ∑ k ∈ Finset.range N, d k * (x : ℂ) ^ (k + 1) with hPd
  set r : ℝ → ℂ := fun t => L t - Pd t⁻¹ with hr
  have hrO : r =O[atTop] fun t => t ^ (-((N : ℝ) + 1)) := by
    refine (hL N).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [hr, hPd, real_smul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rpow_neg_add_one_eq_recip_pow ht]
    push_cast
    ring
  have hr0 : Tendsto r atTop (𝓝 0) := by
    refine hrO.trans_tendsto ?_
    have h := (tendsto_rpow_neg_atTop (y := (N : ℝ) + 1) (by positivity))
    simpa using h
  -- `exp r - 1 = O(r)`
  have hexp : (fun t => cexp (r t) - 1) =O[atTop] r := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [hr0.eventually (Metric.closedBall_mem_nhds 0 zero_lt_one)] with t ht
    exact Complex.norm_exp_sub_one_le (by simpa using ht)
  -- `exp(Pd(1/t))` is bounded
  have hPdb : (fun t : ℝ => cexp (Pd t⁻¹)) =O[atTop] fun _ => (1 : ℝ) := by
    have hc : Continuous fun x : ℝ => cexp (Pd x) := by simp only [hPd]; fun_prop
    exact ((hc.tendsto 0).comp tendsto_inv_atTop_zero).isBigO_one ℝ
  have h1 := (hPdb.mul (hexp.trans hrO)).congr_right fun t => one_mul _
  have hev : (fun t : ℝ => (t⁻¹) ^ (N + 1)) =ᶠ[atTop] fun t => t ^ (-((N : ℝ) + 1)) := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact (rpow_neg_add_one_eq_recip_pow ht N).symm
  have h2 := ((cexp_poly_sub_isBigO d G hG0 hG N).comp_tendsto
    tendsto_inv_atTop_nhdsGT_zero).trans_eventuallyEq hev
  refine (h1.add h2).congr_left fun t => ?_
  simp only [Function.comp_apply, hr]
  rw [mul_sub, mul_one, ← Complex.exp_add, add_sub_cancel]
  simp only [hPd]
  ring

/-- `G₀(a, b) = 1` for the coefficients of DLMF 5.11.15. -/
theorem stirlingRatioG_zero (a b : ℂ) : stirlingRatioG a b 0 = 1 := by
  rw [stirlingRatioG]

/-- The coefficients `Gₙ(a, b)` of DLMF 5.11.15 satisfy `(n + 1) G_{n+1} = ∑_{k≤n} (k + 1)(cₖ(a) -
cₖ(b)) G_{n-k}`, with `cₖ` the coefficients of 5.11.8. -/
theorem stirlingRatioG_recurrence (a b : ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * stirlingRatioG a b (n + 1) = ∑ k ∈ Finset.range (n + 1),
      ((k : ℂ) + 1) * (stirlingShiftCoeff a k - stirlingShiftCoeff b k) *
        stirlingRatioG a b (n - k) := by
  rw [stirlingRatioG]
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [mul_div_cancel₀ _ hn, Fin.sum_univ_eq_sum_range (fun k => (-1 : ℂ) ^ k *
    (Polynomial.aeval a (Polynomial.bernoulli (k + 2)) -
      Polynomial.aeval b (Polynomial.bernoulli (k + 2))) / (k + 2) *
    stirlingRatioG a b (n - k)) (n + 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have h2 : (k : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k + 1)
  simp only [stirlingShiftCoeff]
  field_simp

end ShiftedStirling

/-- The all-order positive-ray Gamma-ratio expansion with its order-dependent remainder. -/
@[dlmf 5.11.E13]
theorem Gamma_ratio_expansion (a b : ℂ) (n : ℕ) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Complex.Gamma (t + a) / Complex.Gamma (t + b) -
        (t : ℂ) ^ (a - b) * ∑ k ∈ Finset.range n, stirlingRatioG a b k / (t : ℂ) ^ k)
      (fun t : ℝ => (t : ℂ) ^ (a - b - n)) := by
  set G := stirlingRatioG a b with hGdef
  have hL := (hasAsymptoticExpansion_stirlingShiftRem a).sub
    (hasAsymptoticExpansion_stirlingShiftRem b)
  have hE := isBigO_cexp_sub_of_hasAsymptoticExpansion hL (stirlingRatioG_zero a b)
    (fun m => by simpa using stirlingRatioG_recurrence a b m) n
  -- drop the last term
  have hlast : (fun t : ℝ => G n * ((t⁻¹ : ℝ) : ℂ) ^ n) =O[atTop] fun t => t ^ (-(n : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound ‖G n‖ ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 ht), abs_of_pos (Real.rpow_pos_of_pos ht _), Real.rpow_neg ht.le,
      Real.rpow_natCast, inv_pow]
  have hstep : (fun t : ℝ => t ^ (-((n : ℝ) + 1))) =O[atTop] fun t => t ^ (-(n : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _),
      abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), one_mul]
    exact Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  have hX : (fun t : ℝ => cexp ((stirlingShiftRem a - stirlingShiftRem b) t) -
      ∑ k ∈ Finset.range n, G k * ((t⁻¹ : ℝ) : ℂ) ^ k) =O[atTop]
      fun t => ((t ^ (-(n : ℝ)) : ℝ) : ℂ) := by
    refine (((hE.trans hstep).add hlast).congr_left fun t => ?_).trans
      (Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t => by simp))
    rw [Finset.sum_range_succ]
    ring
  have hmain := (Asymptotics.isBigO_refl (fun t : ℝ => (t : ℂ) ^ (a - b)) atTop).mul hX
  refine (hmain.congr' ?_ ?_)
  · filter_upwards [eventually_gt_atTop (max ‖a‖ ‖b‖)] with t ht
    have hta : (t : ℂ) + a ∈ slitPlane := mem_slitPlane_iff.2 (Or.inl (by
      simp only [add_re, ofReal_re]
      linarith [neg_abs_le a.re, abs_re_le_norm a, le_max_left ‖a‖ ‖b‖]))
    have htb : (t : ℂ) + b ∈ slitPlane := mem_slitPlane_iff.2 (Or.inl (by
      simp only [add_re, ofReal_re]
      linarith [neg_abs_le b.re, abs_re_le_norm b, le_max_right ‖a‖ ‖b‖]))
    have ht0 : (t : ℂ) ≠ 0 := by
      have : 0 < t := lt_of_le_of_lt (le_max_of_le_left (norm_nonneg a)) ht
      exact_mod_cast this.ne'
    rw [Gamma_eq_exp_binetExponent hta, Gamma_eq_exp_binetExponent htb, ← Complex.exp_sub,
      cpow_def_of_ne_zero ht0, mul_sub, ← Complex.exp_add]
    simp only [Pi.sub_apply, stirlingShiftRem]
    congr 1
    · congr 1; ring
    · congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      rw [div_eq_mul_inv, inv_pow]
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    rw [Complex.ofReal_cpow ht.le, ← cpow_add _ _ ht0]
    push_cast
    ring_nf

/-! ### The reciprocal-factorial expansion 5.11.19

For `Re (c - a) > 0` the remainder after `n` terms has the exact Beta-integral form
`Γ(t+b)/Γ(c-a) ∫₀^∞ s^{c-a-1} (1+s)^{-t-b} R_n(s) ds`, where `R_n` is the remainder of the
binomial series of `(1+s)^{b-c}` (`ratioThree_rem_eq`). The Taylor bound
`|R_n(s)| ≤ K sⁿ (1+s)^M` and the real Beta integral then give the `O`-bound. The restriction
on `a` is removed by the exact shift identity `ratioThreeSum_shift`, which lowers `a` by one
at the cost of a factor `t` and one extra reciprocal-factorial term.
-/

section RatioThree

open Set

/-- The binomial coefficient `β(β-1)⋯(β-k+1)/k!`, written with a Pochhammer symbol. -/
def recipFacBinom (β : ℂ) (k : ℕ) : ℂ := (-1) ^ k * poch (-β) k / k.factorial

/-- The remainder of the binomial series of `(1+s)^β` after `n` terms. -/
def recipFacRem (β : ℂ) (n : ℕ) (s : ℝ) : ℂ :=
  (1 + (s : ℂ)) ^ β - ∑ k ∈ Finset.range n, recipFacBinom β k * (s : ℂ) ^ k

/-- The zeroth binomial coefficient `C(β, 0) = 1`. -/
theorem recipFacBinom_zero (β : ℂ) : recipFacBinom β 0 = 1 := by simp [recipFacBinom, poch_zero]

/-- `(a)_{n+1} = a (a + 1)_n`. -/
theorem poch_succ_left' (a : ℂ) (n : ℕ) : poch a (n + 1) = a * poch (a + 1) n := by
  simp [poch, ascPochhammer_succ_left, Polynomial.eval_comp, add_comm]

/-- `C(β, k + 1)(k + 1) = β C(β - 1, k)`. -/
theorem recipFacBinom_succ (β : ℂ) (k : ℕ) :
    recipFacBinom β (k + 1) * (k + 1) = β * recipFacBinom (β - 1) k := by
  simp only [recipFacBinom, poch_succ_left', Nat.factorial_succ]
  rw [show -β + 1 = -(β - 1) by ring]
  push_cast
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
  field_simp
  ring

/-- `1 + s` lies in the slit plane for real `s > -1`. -/
theorem one_add_ofReal_mem_slitPlane {s : ℝ} (hs : -1 < s) : 1 + (s : ℂ) ∈ slitPlane := by
  rw [show 1 + (s : ℂ) = ((1 + s : ℝ) : ℂ) by push_cast; ring]
  exact ofReal_mem_slitPlane.mpr (by linarith)

/-- `u ↦ (1 + u)^β` has derivative `β (1 + s)^(β-1)` at real `s > -1`. -/
theorem hasDerivAt_one_add_cpow (β : ℂ) {s : ℝ} (hs : -1 < s) :
    HasDerivAt (fun u : ℝ => (1 + (u : ℂ)) ^ β) (β * (1 + (s : ℂ)) ^ (β - 1)) s := by
  have h := ((hasDerivAt_id (s : ℂ)).const_add 1).cpow_const (c := β)
    (one_add_ofReal_mem_slitPlane hs)
  simpa using h.comp_ofReal

/-- The remainder of the binomial series of `(1 + s)^β` after `n + 1` terms has derivative `β` times
the remainder of `(1 + s)^(β-1)` after `n` terms. -/
theorem hasDerivAt_recipFacRem (β : ℂ) (n : ℕ) {s : ℝ} (hs : -1 < s) :
    HasDerivAt (recipFacRem β (n + 1)) (β * recipFacRem (β - 1) n s) s := by
  have hp : ∀ k ∈ Finset.range (n + 1), HasDerivAt
      (fun u : ℝ => recipFacBinom β k * (u : ℂ) ^ k)
      (recipFacBinom β k * ((k : ℂ) * (s : ℂ) ^ (k - 1))) s := fun k _ =>
    ((hasDerivAt_pow k (s : ℂ)).comp_ofReal).const_mul _
  have h := (hasDerivAt_one_add_cpow β hs).sub (HasDerivAt.fun_sum hp)
  convert h using 1
  · funext u; rfl
  rw [recipFacRem, Finset.sum_range_succ', mul_sub, Finset.mul_sum]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ← recipFacBinom_succ]
  push_cast
  ring

/-- The binomial remainder after `n + 1` terms vanishes at `s = 0`. -/
theorem recipFacRem_zero_right (β : ℂ) (n : ℕ) : recipFacRem β (n + 1) 0 = 0 := by
  rw [recipFacRem, Finset.sum_range_succ']
  simp [recipFacBinom_zero]

/-- The binomial remainder is continuous on `(-1, ∞)`. -/
theorem continuousOn_recipFacRem (β : ℂ) (n : ℕ) : ContinuousOn (recipFacRem β n) (Ioi (-1)) := by
  intro s hs
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.sub ?_ (by fun_prop)
  exact ContinuousAt.cpow (by fun_prop) continuousAt_const (one_add_ofReal_mem_slitPlane hs)

/-- The binomial remainder after `n` terms is bounded by `K sⁿ (1 + s)^max(Re β, 0)` for `s ≥ 0`. -/
theorem exists_norm_recipFacRem_le (n : ℕ) : ∀ β : ℂ, ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, 0 ≤ s →
    ‖recipFacRem β n s‖ ≤ K * s ^ n * (1 + s) ^ max β.re 0 := by
  induction n with
  | zero =>
    intro β
    refine ⟨1, zero_le_one, fun s hs => ?_⟩
    have h1 : (1 + (s : ℂ)) = ((1 + s : ℝ) : ℂ) := by push_cast; ring
    simp only [recipFacRem, Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, one_mul]
    rw [h1, norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  | succ n ih =>
    intro β
    obtain ⟨K, hK, hb⟩ := ih (β - 1)
    refine ⟨‖β‖ * K, by positivity, fun s hs => ?_⟩
    have hderiv : ∀ u ∈ uIcc 0 s, HasDerivAt (recipFacRem β (n + 1))
        (β * recipFacRem (β - 1) n u) u := by
      intro u hu
      rw [uIcc_of_le hs] at hu
      exact hasDerivAt_recipFacRem β n (by linarith [hu.1])
    have hcont : ContinuousOn (fun u => β * recipFacRem (β - 1) n u) (uIcc 0 s) := by
      refine continuousOn_const.mul ((continuousOn_recipFacRem _ n).mono fun u hu => ?_)
      rw [uIcc_of_le hs] at hu
      exact show -1 < u by linarith [hu.1]
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable)
    rw [recipFacRem_zero_right, sub_zero] at hftc
    rw [← hftc]
    have hle : ∀ u ∈ Set.uIoc (0 : ℝ) s, ‖β * recipFacRem (β - 1) n u‖ ≤
        ‖β‖ * K * s ^ n * (1 + s) ^ max β.re 0 := by
      intro u hu
      rw [uIoc_of_le hs] at hu
      have hu0 : 0 ≤ u := hu.1.le
      rw [norm_mul, mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (hb u hu0).trans ?_
      rw [← mul_assoc]
      have hre : max (β - 1).re 0 ≤ max β.re 0 := by
        simp only [sub_re, one_re]; exact max_le_max (by linarith) le_rfl
      have hpow : (1 + u) ^ max (β - 1).re 0 ≤ (1 + s) ^ max β.re 0 :=
        (Real.rpow_le_rpow (by linarith) (by linarith [hu.2]) (le_max_right _ _)).trans
          (Real.rpow_le_rpow_of_exponent_le (by linarith) hre)
      have hun : u ^ n ≤ s ^ n := pow_le_pow_left₀ hu0 hu.2 n
      gcongr
    calc ‖∫ u in (0 : ℝ)..s, β * recipFacRem (β - 1) n u‖
        ≤ ‖β‖ * K * s ^ n * (1 + s) ^ max β.re 0 * |s - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hle
      _ = ‖β‖ * K * s ^ (n + 1) * (1 + s) ^ max β.re 0 := by
          rw [sub_zero, abs_of_nonneg hs]; ring


/-- `s^(p-1) (1 + s)^(-A)` is integrable on `(0, ∞)` when `0 < Re p < Re A`. -/
theorem integrableOn_cpow_mul_one_add_cpow {p A : ℂ} (hp : 0 < p.re) (hpA : p.re < A.re) :
    IntegrableOn (fun s : ℝ => (s : ℂ) ^ (p - 1) * ((1 + s : ℝ) : ℂ) ^ (-A)) (Ioi 0) := by
  have hg := integrableOn_rpow_mul_one_add_rpow hp hpA
  have hcont : ContinuousOn (fun s : ℝ => (s : ℂ) ^ (p - 1) * ((1 + s : ℝ) : ℂ) ^ (-A))
      (Ioi 0) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
    · exact ContinuousAt.cpow continuous_ofReal.continuousAt continuousAt_const
        (ofReal_mem_slitPlane.mpr hs0)
    · exact ContinuousAt.cpow (continuous_ofReal.continuousAt.comp
        (continuousAt_const.add continuousAt_id)) continuousAt_const
        (ofReal_mem_slitPlane.mpr (by linarith))
  refine hg.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
  have hs0 : (0 : ℝ) < s := hs
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hs0, norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simp

/-- `Γ(α + k) = (α)ₖ Γ(α)` for `Re α > 0`. -/
theorem Gamma_add_nat_eq_poch_mul_Gamma {α : ℂ} (hα : 0 < α.re) (k : ℕ) :
    Complex.Gamma (α + k) = poch α k * Complex.Gamma α := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    have hne : α + k ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hne, ih, poch_succ]
    ring

/-- The Beta-integral representation of the remainder of the reciprocal-factorial expansion. -/
theorem ratioThree_rem_eq {a b c : ℂ} (n : ℕ) (hα : 0 < (c - a).re) {t : ℝ}
    (hta : 0 < (t + a).re) (htb : (c - a).re + n < (t + b).re) :
    Complex.Gamma (t + a) * Complex.Gamma (t + b) / Complex.Gamma (t + c) -
        ∑ k ∈ Finset.range n,
          (-1 : ℂ) ^ k * poch (c - a) k * poch (c - b) k / k.factorial *
            Complex.Gamma (a + b - c + t - k) =
      Complex.Gamma (t + b) / Complex.Gamma (c - a) *
        ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (c - a - 1) * ((1 + s : ℝ) : ℂ) ^ (-(t + b)) *
          recipFacRem (b - c) n s := by
  set α := c - a with hαdef
  have htb0 : 0 < (t + b).re := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hΓα : Complex.Gamma α ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hα
  have hΓb : Complex.Gamma (t + b) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos htb0
  have hαc : α.re < (t + c).re := by
    have : (t + c).re = (t + a).re + α.re := by
      simp only [hαdef, add_re, sub_re]; ring
    linarith
  have hk : ∀ k ∈ Finset.range n, (α + k).re < (t + b).re := by
    intro k hk
    have : (k : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hk
    have h2 := htb
    simp only [add_re, natCast_re, ofReal_re] at h2 ⊢
    linarith
  have hkpos : ∀ k : ℕ, 0 < (α + k).re := by
    intro k; simp only [add_re, natCast_re]; positivity
  -- the integrals
  have hF := mellin_one_add_cpow_neg (a := t + c) (s := α) hα hαc
  have hK : ∀ k ∈ Finset.range n,
      ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (α + k - 1) * ((1 + s : ℝ) : ℂ) ^ (-(t + b)) =
        Complex.Gamma (α + k) * Complex.Gamma (t + b - (α + k)) / Complex.Gamma (t + b) := by
    intro k hk'
    have := mellin_one_add_cpow_neg (a := t + b) (s := α + k) (hkpos k) (hk k hk')
    rw [mellin] at this
    simpa only [smul_eq_mul] using this
  rw [mellin] at hF
  simp only [smul_eq_mul] at hF
  -- pointwise identity of integrands
  have hpt : ∀ s ∈ Ioi (0 : ℝ),
      (s : ℂ) ^ (α - 1) * ((1 + s : ℝ) : ℂ) ^ (-(t + b)) * recipFacRem (b - c) n s =
        (s : ℂ) ^ (α - 1) * ((1 + s : ℝ) : ℂ) ^ (-(t + c)) -
          ∑ k ∈ Finset.range n, recipFacBinom (b - c) k *
            ((s : ℂ) ^ (α + k - 1) * ((1 + s : ℝ) : ℂ) ^ (-(t + b))) := by
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs'.ne'
    have h1 : ((1 + s : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (1 + s : ℝ) ≠ 0 by linarith)
    have hc1 : (1 + (s : ℂ)) = ((1 + s : ℝ) : ℂ) := by push_cast; ring
    have hpow : ((1 + s : ℝ) : ℂ) ^ (-(t + c)) =
        ((1 + s : ℝ) : ℂ) ^ (-(t + b)) * ((1 + s : ℝ) : ℂ) ^ (b - c) := by
      rw [← cpow_add _ _ h1]; congr 1; ring
    have hspow : ∀ k : ℕ, (s : ℂ) ^ (α + k - 1) = (s : ℂ) ^ (α - 1) * (s : ℂ) ^ k := by
      intro k
      rw [← cpow_natCast, ← cpow_add _ _ hs0]; congr 1; ring
    rw [recipFacRem, hc1, hpow, mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [hspow]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hintF := integrableOn_cpow_mul_one_add_cpow (p := α) (A := t + c) hα hαc
  have hintK : ∀ k ∈ Finset.range n, Integrable (fun s : ℝ => recipFacBinom (b - c) k *
      ((s : ℂ) ^ (α + k - 1) * ((1 + s : ℝ) : ℂ) ^ (-(t + b)))) (volume.restrict (Ioi 0)) :=
    fun k hk' => (integrableOn_cpow_mul_one_add_cpow (hkpos k) (hk k hk')).const_mul _
  rw [integral_sub hintF (integrable_finsetSum _ hintK), integral_finsetSum _ hintK, hF]
  simp_rw [integral_const_mul]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · rw [show t + c - α = t + a by rw [hαdef]; ring]
    field_simp
  · refine Finset.sum_congr rfl fun k hk' => ?_
    rw [hK k hk', Gamma_add_nat_eq_poch_mul_Gamma hα, recipFacBinom,
      show -(b - c) = c - b by ring, show t + b - (α + k) = a + b - c + t - k by
        simp [hαdef]; ring]
    field_simp

/-- The norm bound on the Beta-integral remainder. -/
theorem norm_integral_recipFacRem_le {α β B : ℂ} {n : ℕ} {K M : ℝ}
    (hb : ∀ s : ℝ, 0 ≤ s → ‖recipFacRem β n s‖ ≤ K * s ^ n * (1 + s) ^ M)
    (hα : 0 < α.re) (hB : α.re + n + M < B.re) :
    ‖∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (α - 1) * ((1 + s : ℝ) : ℂ) ^ (-B) * recipFacRem β n s‖ ≤
      K * (Real.Gamma (α.re + n) * Real.Gamma (B.re - M - (α.re + n)) /
        Real.Gamma (B.re - M)) := by
  set p : ℝ := α.re + n with hp
  set q : ℝ := B.re - M - p with hq
  have hp0 : 0 < p := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hq0 : 0 < q := by linarith
  obtain ⟨hint, hval⟩ := real_beta_on_Ioi hp0 hq0
  have hpq : p + q = B.re - M := by ring
  rw [hpq] at hint hval
  rw [← hval, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hint.const_mul K) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
  have hs0 : (0 : ℝ) < s := hs
  have h1 : (0 : ℝ) < 1 + s := by linarith
  rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hs0, norm_cpow_eq_rpow_re_of_pos h1]
  have hr := hb s hs0.le
  calc s ^ (α - 1).re * (1 + s) ^ (-B).re * ‖recipFacRem β n s‖
      ≤ s ^ (α - 1).re * (1 + s) ^ (-B).re * (K * s ^ n * (1 + s) ^ M) := by gcongr
    _ = K * (s ^ (p - 1) / (1 + s) ^ (B.re - M)) := by
      have e1 : s ^ (p - 1) = s ^ (α - 1).re * s ^ n := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hs0]; congr 1; simp [hp]; ring
      have e2 : (1 + s) ^ (-B).re * (1 + s) ^ M = ((1 + s) ^ (B.re - M))⁻¹ := by
        rw [← Real.rpow_add h1, ← Real.rpow_neg h1.le]; congr 1; simp; ring
      rw [e1, div_eq_mul_inv, ← e2]; ring


/-- The partial sum of the reciprocal-factorial expansion 5.11.19. -/
def ratioThreeSum (a b c : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range n, (-1 : ℂ) ^ k * poch (c - a) k * poch (c - b) k / k.factorial *
    Complex.Gamma (a + b - c + t - k)

/-- The boundary coefficient in the shift identity `ratioThreeSum_shift`. -/
def ratioThreeShiftCoeff (a b c : ℂ) : ℕ → ℂ
  | 0 => 0
  | j + 1 => (-1 : ℂ) ^ j * poch (c - a + 1) j * poch (c - b) (j + 1) / j.factorial

/-- Shift identity for the partial sums of 5.11.19 in the parameter `a`. -/
theorem ratioThreeSum_shift (a b c : ℂ) (t : ℝ) (n : ℕ)
    (hne : ∀ k < n, a + b - c + t - 1 - k ≠ 0) :
    ((t : ℂ) + a - 1) * ratioThreeSum (a - 1) b c n t =
      ratioThreeSum a b c n t + ratioThreeShiftCoeff a b c n *
        Complex.Gamma (a + b - c + t - n) := by
  induction n with
  | zero => simp [ratioThreeSum, ratioThreeShiftCoeff]
  | succ n ih =>
    have ih' := ih fun k hk => hne k (by omega)
    simp only [ratioThreeSum, Finset.sum_range_succ] at ih' ⊢
    set Y : ℂ := a + b - c + t - 1 - n with hY
    have hYne : Y ≠ 0 := hne n (by omega)
    have hX1 : a - 1 + b - c + t - n = Y := by rw [hY]; ring
    have hX2 : a + b - c + t - ((n + 1 : ℕ) : ℂ) = Y := by rw [hY]; push_cast; ring
    have hX3 : a + b - c + t - n = Y + 1 := by rw [hY]; ring
    have hG : Complex.Gamma (Y + 1) = Y * Complex.Gamma Y := Complex.Gamma_add_one Y hYne
    rw [mul_add, ih', hX1, hX2, hX3, hG]
    have hc : c - (a - 1) = c - a + 1 := by ring
    rw [hc]
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    rcases n with _ | j
    · simp only [ratioThreeShiftCoeff, poch_zero, poch_one, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, one_mul, zero_mul, add_zero, Finset.range_zero,
        Finset.sum_empty, zero_add, Nat.cast_zero] at hY ⊢
      rw [hY]; ring
    · simp only [ratioThreeShiftCoeff]
      rw [poch_succ_left' (c - a) j, poch_succ (c - a + 1) j,
        poch_succ (c - b) (j + 1), Nat.factorial_succ]
      rw [hY]
      have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
      push_cast
      field_simp
      ring


/-- The leading-order consequence of 5.11.13: `Γ(t+u)/Γ(t+v) = O(t^{u-v})`. -/
theorem isBigO_Gamma_add_div_Gamma_add (u v : ℂ) :
    (fun t : ℝ => Complex.Gamma (t + u) / Complex.Gamma (t + v)) =O[atTop]
      fun t : ℝ => (t : ℂ) ^ (u - v) := by
  have h := Gamma_ratio_expansion u v 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, div_one, Nat.cast_one,
    stirlingRatioG_zero, mul_one] at h
  have h1 : (fun t : ℝ => (t : ℂ) ^ (u - v - 1)) =O[atTop] fun t : ℝ => (t : ℂ) ^ (u - v) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [one_mul, norm_cpow_eq_rpow_re_of_pos (by linarith),
      norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le ht (by simp)
  exact ((h.trans h1).add (Asymptotics.isBigO_refl (fun t : ℝ => (t : ℂ) ^ (u - v)) atTop))
    |>.congr_left fun t => by ring

/-- 5.11.19 when `Re (c - a) > 0`, via the Beta-integral remainder. -/
theorem ratioThree_isBigO_of_re_pos {a b c : ℂ} (n : ℕ) (hα : 0 < (c - a).re) :
    (fun t : ℝ => Complex.Gamma (t + a) * Complex.Gamma (t + b) / Complex.Gamma (t + c) -
        ratioThreeSum a b c n t) =O[atTop]
      fun t : ℝ => Complex.Gamma t * (t : ℂ) ^ (a + b - c - n) := by
  obtain ⟨K, hK0, hb⟩ := exists_norm_recipFacRem_le n (b - c)
  set M : ℝ := max (b - c).re 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  set p : ℝ := (c - a).re + n with hpdef
  have hp0 : 0 < p := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  set u1 : ℝ := b.re - M - p with hu1
  set v1 : ℝ := b.re - M with hv1
  set C : ℝ := K * Real.Gamma p / ‖Complex.Gamma (c - a)‖ with hC
  have hΓα : Complex.Gamma (c - a) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hα
  -- the pointwise bound
  have hbound : ∀ᶠ t : ℝ in atTop, ‖Complex.Gamma (t + a) * Complex.Gamma (t + b) /
      Complex.Gamma (t + c) - ratioThreeSum a b c n t‖ ≤
      C * ‖Complex.Gamma (t + b) / Complex.Gamma (t + 0) * Complex.Gamma t *
        (Complex.Gamma ((t : ℂ) + (u1 : ℂ)) / Complex.Gamma ((t : ℂ) + (v1 : ℂ)))‖ := by
    filter_upwards [eventually_gt_atTop (max (max 0 (-a.re)) (max (p + M - b.re) (-u1)))]
      with t ht
    simp only [max_lt_iff] at ht
    obtain ⟨⟨ht0, hta⟩, htb, htu⟩ := ht
    have hta' : 0 < ((t : ℂ) + a).re := by simp; linarith
    have htbre : ((t : ℂ) + b).re = t + b.re := by simp
    have htb' : (c - a).re + n < ((t : ℂ) + b).re := by rw [htbre]; linarith
    have hB : (c - a).re + n + M < ((t : ℂ) + b).re := by rw [htbre]; linarith
    have hrem := ratioThree_rem_eq (a := a) (b := b) (c := c) n hα hta' htb'
    have hJ := norm_integral_recipFacRem_le (α := c - a) (β := b - c) (B := t + b) (n := n)
      (K := K) (M := M) hb hα hB
    rw [htbre] at hJ
    have e1 : t + b.re - M - ((c - a).re + n) = t + u1 := by rw [hu1, hpdef]; ring
    have e2 : t + b.re - M = t + v1 := by rw [hv1]; ring
    rw [e1, e2] at hJ
    have htu1 : 0 < t + u1 := by linarith
    have htv1 : 0 < t + v1 := by linarith
    have hΓt : Complex.Gamma t ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using ht0)
    have hcast : ∀ x : ℝ, Complex.Gamma ((t : ℂ) + (x : ℂ)) = (Real.Gamma (t + x) : ℂ) := by
      intro x; rw [← Complex.ofReal_add, Complex.Gamma_ofReal]
    rw [hcast, hcast, ← Complex.ofReal_div, add_zero, div_mul_cancel₀ _ hΓt, norm_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos (Real.Gamma_pos_of_pos htu1) (Real.Gamma_pos_of_pos htv1))]
    unfold ratioThreeSum
    rw [hrem, norm_mul, norm_div, hC]
    calc ‖Complex.Gamma (t + b)‖ / ‖Complex.Gamma (c - a)‖ * ‖∫ s in Ioi (0 : ℝ),
          (s : ℂ) ^ (c - a - 1) * ((1 + s : ℝ) : ℂ) ^ (-((t : ℂ) + b)) *
            recipFacRem (b - c) n s‖
        ≤ ‖Complex.Gamma (t + b)‖ / ‖Complex.Gamma (c - a)‖ *
          (K * (Real.Gamma p * Real.Gamma (t + u1) / Real.Gamma (t + v1))) := by
          gcongr
      _ = K * Real.Gamma p / ‖Complex.Gamma (c - a)‖ * (‖Complex.Gamma (t + b)‖ *
          (Real.Gamma (t + u1) / Real.Gamma (t + v1))) := by ring
  have h1 := Asymptotics.IsBigO.of_bound C hbound
  have h2 := ((isBigO_Gamma_add_div_Gamma_add b 0).mul
    (Asymptotics.isBigO_refl (fun t : ℝ => Complex.Gamma t) atTop)).mul
      (isBigO_Gamma_add_div_Gamma_add u1 v1)
  refine h1.trans (h2.trans (Asymptotics.IsBigO.of_bound 1 ?_))
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [one_mul, norm_mul, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht,
    norm_cpow_eq_rpow_re_of_pos ht, norm_cpow_eq_rpow_re_of_pos ht]
  have he : (b - 0).re + ((u1 : ℂ) - (v1 : ℂ)).re = (a + b - c - n).re := by
    simp only [sub_re, ofReal_re, add_re, natCast_re, zero_re, hu1, hv1, hpdef]
    ring
  rw [← he, Real.rpow_add ht]
  apply le_of_eq
  ring


/-- Lowering `a` by one in 5.11.19 costs one factor `t` and adds one reciprocal-factorial term. -/
theorem ratioThree_isBigO_shift {a b c : ℂ} (n : ℕ)
    (h : (fun t : ℝ => Complex.Gamma (t + (a - 1)) * Complex.Gamma (t + b) /
        Complex.Gamma (t + c) - ratioThreeSum (a - 1) b c n t) =O[atTop]
      fun t : ℝ => Complex.Gamma t * (t : ℂ) ^ (a - 1 + b - c - n)) :
    (fun t : ℝ => Complex.Gamma (t + a) * Complex.Gamma (t + b) / Complex.Gamma (t + c) -
        ratioThreeSum a b c n t) =O[atTop]
      fun t : ℝ => Complex.Gamma t * (t : ℂ) ^ (a + b - c - n) := by
  set w : ℂ := a + b - c - n with hw
  set e : ℂ := ratioThreeShiftCoeff a b c n
  have heq : (fun t : ℝ => ((t : ℂ) + a - 1) * (Complex.Gamma (t + (a - 1)) *
      Complex.Gamma (t + b) / Complex.Gamma (t + c) - ratioThreeSum (a - 1) b c n t) +
        e * Complex.Gamma (a + b - c + t - n)) =ᶠ[atTop]
      fun t : ℝ => Complex.Gamma (t + a) * Complex.Gamma (t + b) / Complex.Gamma (t + c) -
        ratioThreeSum a b c n t := by
    filter_upwards [eventually_gt_atTop (max (1 - a.re) (n + 1 - (a + b - c).re))]
      with t ht
    simp only [max_lt_iff] at ht
    have hne1 : (t : ℂ) + (a - 1) ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    have hne : ∀ k < n, a + b - c + t - 1 - k ≠ 0 := by
      intro k hk h0
      have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
      have := congrArg Complex.re h0
      have h2 := ht.2
      simp only [sub_re, add_re] at h2
      simp at this
      linarith
    have hG : Complex.Gamma (t + a) = ((t : ℂ) + (a - 1)) * Complex.Gamma (t + (a - 1)) := by
      rw [← Complex.Gamma_add_one _ hne1]; congr 1; ring
    rw [mul_sub, ratioThreeSum_shift a b c t n hne, hG]
    ring
  have hlin : (fun t : ℝ => (t : ℂ) + a - 1) =O[atTop] fun t : ℝ => (t : ℂ) := by
    refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop ‖a - 1‖, eventually_ge_atTop 0] with t ht ht0
    rw [show (t : ℂ) + a - 1 = t + (a - 1) by ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht0]
    calc ‖(t : ℂ) + (a - 1)‖ ≤ ‖(t : ℂ)‖ + ‖a - 1‖ := norm_add_le _ _
      _ ≤ 2 * t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]; linarith
  have hA := hlin.mul h
  have hA' : (fun t : ℝ => (t : ℂ) * (Complex.Gamma t * (t : ℂ) ^ (a - 1 + b - c - n)))
      =ᶠ[atTop] fun t : ℝ => Complex.Gamma t * (t : ℂ) ^ w := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    rw [show w = (a - 1 + b - c - n) + 1 by rw [hw]; ring, cpow_add _ _ ht0, cpow_one]
    ring
  have hB : (fun t : ℝ => e * Complex.Gamma (a + b - c + t - n)) =O[atTop]
      fun t : ℝ => Complex.Gamma t * (t : ℂ) ^ w := by
    have h3 := (((isBigO_Gamma_add_div_Gamma_add w 0).mul
      (Asymptotics.isBigO_refl (fun t : ℝ => Complex.Gamma t) atTop)).const_mul_left e)
    refine (h3.congr' ?_ ?_)
    · filter_upwards [eventually_gt_atTop 0] with t ht
      have hΓt : Complex.Gamma t ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using ht)
      rw [add_zero, div_mul_cancel₀ _ hΓt, show (t : ℂ) + w = a + b - c + t - n by
        rw [hw]; ring]
    · filter_upwards with t
      rw [sub_zero, mul_comm]
  exact ((hA.trans_eventuallyEq hA').add hB).congr' heq EventuallyEq.rfl

/-- Inductive core of the remainder bound for 5.11.19: the error of the `n`-term
reciprocal-factorial expansion of `Γ(t + a)Γ(t + b)/Γ(t + c)` is `O(Γ(t) t^(a+b-c-n))`, by induction
on `m` with `Re(c - a) + m > 0`. -/
lemma ratioThree_isBigO_aux {b c : ℂ} (n : ℕ) (m : ℕ) : ∀ a : ℂ, 0 < (c - a).re + m →
    (fun t : ℝ => Complex.Gamma (t + a) * Complex.Gamma (t + b) / Complex.Gamma (t + c) -
        ratioThreeSum a b c n t) =O[atTop]
      fun t : ℝ => Complex.Gamma t * (t : ℂ) ^ (a + b - c - n) := by
  induction m with
  | zero => intro a ha; exact ratioThree_isBigO_of_re_pos n (by simpa using ha)
  | succ m ih =>
    intro a ha
    refine ratioThree_isBigO_shift n (ih (a - 1) ?_)
    simp only [sub_re, one_re] at ha ⊢
    push_cast at ha
    linarith

end RatioThree

/-- The reciprocal-factorial Gamma-ratio expansion. The remainder retains the
parameter-dependent leading power `a + b - c`, which cannot be omitted. -/
@[dlmf 5.11.E19]
theorem Gamma_ratio_three {a b c : ℂ} (n : ℕ) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Complex.Gamma (t + a) * Complex.Gamma (t + b) / Complex.Gamma (t + c) -
        ∑ k ∈ Finset.range n,
          (-1 : ℂ) ^ k * poch (c - a) k * poch (c - b) k / k.factorial *
            Complex.Gamma (a + b - c + t - k))
      (fun t : ℝ => Complex.Gamma t * (t : ℂ) ^ (a + b - c - n)) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (-(c - a).re)
  exact ratioThree_isBigO_aux n m a (by linarith)

end DLMF.Gamma
