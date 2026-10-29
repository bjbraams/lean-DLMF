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
# Stirling expansions from Binet integrals

Real Stirling coefficients and Poincare expansions obtained from the Binet integral and Watson
lemma.

Source references and common attribution are retained in
`DLMF.Gamma.Asymptotics`.
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

/-- The remainder of the Bernoulli expansion of Binet's kernel is an absolutely
convergent partial-fraction series with alternating sign. -/
theorem hasSum_binetBeta_div_sub_binetPoly (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun m : ℕ => 2 * (-1 : ℝ) ^ n * t ^ (2 * n) /
      ((2 * π * (m + 1)) ^ (2 * n) * (t ^ 2 + (2 * π * (m + 1)) ^ 2)))
      (binetBeta t / t - binetPoly n t) := by
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
  exact hRem

/-- `|β(t)/t - Pₙ(t)| ≤ 2 Sₙ t^{2n}` (Temme (3.26)). -/
theorem abs_binetBeta_div_sub_binetPoly_le (n : ℕ) {t : ℝ} (ht : 0 < t) :
    |binetBeta t / t - binetPoly n t| ≤ 2 * binetRemConst n * t ^ (2 * n) := by
  have ha : ∀ m : ℕ, 0 < 2 * π * (m + 1) := fun m => by positivity
  have hRem := hasSum_binetBeta_div_sub_binetPoly n ht
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

/-- The Bernoulli remainder of Binet's kernel has sign `(-1)^n` on the positive axis. -/
theorem binetBeta_div_sub_binetPoly_sign (n : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ (-1 : ℝ) ^ n * (binetBeta t / t - binetPoly n t) := by
  rw [← (hasSum_binetBeta_div_sub_binetPoly n ht).tsum_eq, ← tsum_mul_left]
  apply tsum_nonneg
  intro m
  have hp : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [show (-1 : ℝ) ^ n * (2 * (-1) ^ n * t ^ (2 * n) /
      ((2 * π * (m + 1)) ^ (2 * n) * (t ^ 2 + (2 * π * (m + 1)) ^ 2))) =
      2 * ((-1) ^ n * (-1) ^ n) * t ^ (2 * n) /
        ((2 * π * (m + 1)) ^ (2 * n) * (t ^ 2 + (2 * π * (m + 1)) ^ 2)) by ring,
    hp]
  positivity

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
/-- The remainder in the digamma expansion is the negative Laplace integral of
Binet's Bernoulli remainder; this identity holds at every positive real argument. -/
theorem digamma_sub_stirling_eq_integral (n : ℕ) {z : ℝ} (hz0 : 0 < z) :
    Real.digamma z - (Real.log z - 1 / (2 * z) -
      ∑ k ∈ Finset.Icc 1 n, (bernoulli (2 * k) : ℝ) / ((2 * k) * z ^ (2 * k))) =
      -∫ s in Ioi (0 : ℝ), Real.exp (-z * s) *
        (s ^ 1 * (binetBeta s / s - binetPoly n s)) := by
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
  exact hdiff

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
  have hdiff := digamma_sub_stirling_eq_integral n hz0
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

end DLMF.Gamma
end
end
