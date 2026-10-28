/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.SpecialFunctions.Erf
public import Mathlib.Analysis.Complex.IntegerCompl
public import DLMF.Hypergeometric.EulerIntegral
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Analysis.Complex.AbsMax

/-!
# Kummer's function `M(a,c,z) = ₁F₁(a;c;z)` (AAR §4.1)

The series is entire in `z` (AAR: the confluent limit of `₂F₁`). Mathlib's
`regularizedHGFun {a} {c}` is the regularized form `M(a,c,z)/Γ(c)`.
Tricomi's `U` uses the connection formula off the integers and parameter limits
at integers; `kummerU_zero` verifies the continuation at zero first parameter.
`kummerUOnLog` retains the logarithmic argument needed for monodromy.
The real restrictions of `erf` and `erfc` are identified with the Tau Ceti
contributors’ real error functions, so their real-variable API can be reused.
-/

@[expose] public section

open Complex Filter intervalIntegral
open scoped Real Nat Topology ENNReal
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- The coefficient of `z^n` in Kummer's confluent series. -/
abbrev kummerMCoeff (a c : ℂ) (n : ℕ) : ℂ :=
  poch a n / (poch c n * n !)

/-- Kummer's function `M(a,c,z) = ₁F₁(a;c;z)`. -/
@[dlmf 13.2.E2]
def kummerM (a c z : ℂ) : ℂ :=
  ∑' n : ℕ, poch a n / (poch c n * n !) * z ^ n

/-- `M(a,c,0) = 1`. -/
@[simp]
theorem kummerM_zero (a c : ℂ) : kummerM a c 0 = 1 := by
  unfold kummerM
  have h0 : (fun n : ℕ => poch a n / (poch c n * n !) * (0 : ℂ) ^ n) =
      fun n => if n = 0 then 1 else 0 := by
    ext n
    cases n with
    | zero => simp [poch_zero]
    | succ n => simp [pow_succ]
  rw [h0, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

/-- `₁F₁(a;a;z) = e^z` when `a` is not a nonpositive integer. -/
@[dlmf 13.6.E1]
theorem kummerM_self {a z : ℂ} (ha : ∀ k : ℕ, a ≠ -k) :
    kummerM a a z = exp z := by
  unfold kummerM
  have hcoeff : ∀ n : ℕ, poch a n / (poch a n * n !) * z ^ n = z ^ n / n ! := by
    intro n
    have hne := poch_ne_zero_of_not_neg_nat ha n
    field [hne]
  simp_rw [hcoeff]
  simpa [exp_eq_exp_ℂ] using (congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℂ)) z).symm

/-- A terminating `₁F₁(-n;c;z)` is a polynomial of degree at most `n`. -/
theorem kummerM_eq_sum_neg_nat (n : ℕ) (c z : ℂ) :
    kummerM (-(n : ℂ)) c z =
      ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k / (poch c k * k.factorial) * z ^ k := by
  unfold kummerM
  refine tsum_eq_sum fun k hk => ?_
  have hkn : n < k := by
    rw [Finset.mem_range] at hk
    omega
  simp [poch_neg_nat_eq_zero hkn]

/-- `₁F₁(0;c;z) = 1`. -/
@[dlmf 13.6.E3]
theorem kummerM_of_zero_param (c z : ℂ) : kummerM 0 c z = 1 := by
  unfold kummerM
  have h0 : (fun n : ℕ => poch 0 n / (poch c n * n !) * z ^ n) =
      fun n => if n = 0 then 1 else 0 := by
    ext n
    cases n with
    | zero => simp [poch_zero]
    | succ n => simp
  rw [h0, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

/-- The coefficients of the regularized `₁F₁` are `(a)_n / (n! Γ(c+n))`. -/
theorem regularizedHGFunCoeff_singleton (a c : ℂ) (n : ℕ) :
    regularizedHGFunCoeff {a} {c} n = poch a n / (n ! * Gamma (c + n)) := by
  simp [regularizedHGFunCoeff, poch]

/-- The regularized generalized hypergeometric function is the sum of its coefficient series. -/
theorem regularizedHGFun_eq_tsum (a b : Multiset ℂ) (z : ℂ) :
    regularizedHGFun a b z = ∑' n : ℕ, regularizedHGFunCoeff a b n * z ^ n := by
  unfold regularizedHGFun regularizedHGFunSeries
  rw [FormalMultilinearSeries.sum]
  simp_rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- The regularized generalized hypergeometric function at `0` is its zeroth coefficient. -/
theorem regularizedHGFun_zero (a b : Multiset ℂ) :
    regularizedHGFun a b 0 = regularizedHGFunCoeff a b 0 :=
  Complex.regularizedHGFun_zero

/-- The coefficient comparison with Mathlib's regularized confluent series. -/
theorem kummerMCoeff_eq_mul_regularizedHGFunCoeff {a c : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    kummerMCoeff a c n = Gamma c * regularizedHGFunCoeff {a} {c} n := by
  have hp : poch c n = Gamma (c + n) / Gamma c :=
    (Gamma_add_nat_div_Gamma_eq (n := n) c hc).symm
  have hc0 : Gamma c ≠ 0 := Gamma_ne_zero hc
  have hcn : Gamma (c + n) ≠ 0 := Gamma_ne_zero (not_neg_nat_add_nat hc n)
  rw [kummerMCoeff, hp, regularizedHGFunCoeff_singleton]
  field [hc0, hcn, Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- Recover Kummer's `M` from Mathlib's regularized `₁F₁`. -/
@[dlmf 13.2.E4]
theorem kummerM_eq_mul_regularizedHGFun {a c z : ℂ} (hc : ∀ k : ℕ, c ≠ -k) :
    kummerM a c z = Gamma c * regularizedHGFun {a} {c} z := by
  unfold kummerM
  simp_rw [show ∀ n : ℕ, poch a n / (poch c n * n !) =
    Gamma c * regularizedHGFunCoeff {a} {c} n from
      kummerMCoeff_eq_mul_regularizedHGFunCoeff hc]
  rw [regularizedHGFun_eq_tsum, ← tsum_mul_left]
  exact tsum_congr fun n => by ring

/-- Kummer's series has infinite radius, by Mathlib's convergence theorem for the
regularized hypergeometric series. -/
theorem hasFPowerSeriesOnBall_kummerM {a c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) :
    HasFPowerSeriesOnBall (kummerM a c)
      (FormalMultilinearSeries.ofScalars ℂ (kummerMCoeff a c)) 0 ⊤ := by
  have hr : (regularizedHGFunSeries {a} {c}).radius = ⊤ :=
    radius_regularizedHGFunSeries_eq_top (by simp)
  have hs : HasFPowerSeriesOnBall (regularizedHGFun {a} {c})
      (regularizedHGFunSeries {a} {c}) 0 ⊤ := by
    change HasFPowerSeriesOnBall (regularizedHGFunSeries {a} {c}).sum
      (regularizedHGFunSeries {a} {c}) 0 ⊤
    simpa only [hr] using (regularizedHGFunSeries {a} {c}).hasFPowerSeriesOnBall
      (by rw [hr]; simp)
  have ht := hs.const_smul (c := Gamma c)
  have hp : Gamma c • regularizedHGFunSeries {a} {c} =
      FormalMultilinearSeries.ofScalars ℂ (kummerMCoeff a c) := by
    rw [regularizedHGFunSeries, ← FormalMultilinearSeries.ofScalars_smul]
    congr 1
    funext n
    exact (kummerMCoeff_eq_mul_regularizedHGFunCoeff hc n).symm
  have hf : Gamma c • regularizedHGFun {a} {c} = kummerM a c := by
    funext z
    exact (kummerM_eq_mul_regularizedHGFun hc).symm
  rwa [hp, hf] at ht

/-- The coefficient recurrence for the confluent hypergeometric equation. -/
theorem kummerMCoeff_recurrence {a c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    (n + 1 : ℂ) * (c + n) * kummerMCoeff a c (n + 1) =
      (a + n) * kummerMCoeff a c n := by
  have hcp := poch_ne_zero_of_not_neg_nat hc n
  have hcn : c + (n : ℂ) ≠ 0 := by
    simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hc n
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [kummerMCoeff, poch_succ, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field [hcp, hcn, hn, Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- Chu–Vandermonde evaluates the coefficient convolution in Kummer's transformation. -/
theorem kummerMCoeff_kummer_convolution {a c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      kummerMCoeff (c - a) c k * (-1 : ℂ) ^ k / (n - k).factorial) =
      kummerMCoeff a c n := by
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      kummerMCoeff (c - a) c k * (-1 : ℂ) ^ k / (n - k).factorial =
        gaussHGCoeff (-(n : ℂ)) (c - a) c k / n.factorial := by
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hk0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hnk : ((n - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
    have hch : (n.choose k : ℂ) = n.factorial / (k.factorial * (n - k).factorial) := by
      apply (eq_div_iff (mul_ne_zero hk0 hnk)).2
      simpa [mul_assoc] using congrArg (Nat.cast : ℕ → ℂ)
        (Nat.choose_mul_factorial_mul_factorial hk')
    rw [gaussHGCoeff_neg_nat, hch]
    unfold kummerMCoeff
    field [hn, hk0, hnk, poch_ne_zero_of_not_neg_nat hc k]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  have hv := chu_vandermonde n (b := c - a) hc
  rw [ordinaryHypergeometric_eq_sum_neg_nat] at hv
  simp only [one_pow, mul_one, sub_sub_cancel] at hv
  rw [hv]
  unfold kummerMCoeff
  ring

/-- Kummer's transformation `M(a,c,z) = e^z M(c-a,c,-z)` (AAR (4.1.11), p. 191).
AAR excludes nonpositive integer denominator parameters in §2.1, p. 62; that standing
restriction must be explicit for our totalized series. There is also a typographical error
in the supplied AAR printing: the right-hand denominator in (4.1.11) is printed as `a`
instead of `c`. The formula below uses the intended denominator `c`. -/
@[dlmf 13.2.E39]
theorem kummerM_kummer_transform {a c z : ℂ} (hc : ∀ k : ℕ, c ≠ -k) :
    kummerM a c z = exp z * kummerM (c - a) c (-z) := by
  have hf := (hasFPowerSeriesOnBall_kummerM (a := c - a) hc).hasSum_mul_pow
    (z := -z) (by simp)
  have hg : HasSum (fun n : ℕ => z ^ n / n.factorial) (exp z) := by
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp z
  rw [mul_comm, ← hf.tsum_eq, ← hg.tsum_eq,
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf.summable.norm hg.summable.norm]
  unfold kummerM
  apply tsum_congr
  intro n
  change kummerMCoeff a c n * z ^ n = _
  rw [← kummerMCoeff_kummer_convolution hc n, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hp : z ^ k * z ^ (n - k) = z ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hk']
  symm
  rw [neg_pow]
  calc
    _ = (kummerMCoeff (c - a) c k * (-1 : ℂ) ^ k / (n - k).factorial) *
        (z ^ k * z ^ (n - k)) := by ring
    _ = _ := by rw [hp]

/-- The confluent hypergeometric equation
`z y'' + (c-z) y' - a y = 0` (AAR §4.1). -/
@[dlmf 13.2.E1]
theorem kummerM_ode {a c z : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (hz : z ≠ 0) :
    z * iteratedDeriv 2 (kummerM a c) z + (c - z) * deriv (kummerM a c) z -
      a * kummerM a c z = 0 := by
  have h := (hasFPowerSeriesOnBall_kummerM (a := a) hc).ode_of_recurrence
    (A := 0) (B := 1) (C := a) (D := c) (fun n => ?_)
    (z := z) (by simp)
  · simpa [iteratedDeriv_succ, iteratedDeriv_zero] using h
  · rw [kummerMCoeff_recurrence hc]
    ring

/-- Differentiating the confluent equation repeatedly gives the shifted equations. -/
theorem confluent_ode_iteratedDeriv {a c : ℂ} {f : ℂ → ℂ}
    (hf : ∀ w, AnalyticAt ℂ f w)
    (hode : ∀ w, w * deriv (deriv f) w + (c - w) * deriv f w - a * f w = 0)
    (n : ℕ) (w : ℂ) :
    w * iteratedDeriv (n + 2) f w + (c + n - w) * iteratedDeriv (n + 1) f w -
      (a + n) * iteratedDeriv n f w = 0 := by
  have ha (k : ℕ) (z : ℂ) : AnalyticAt ℂ (iteratedDeriv k f) z := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hf z
    | succ k ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hd (k : ℕ) (z : ℂ) : HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f z) z := by
    simpa only [iteratedDeriv_succ] using (ha k z).differentiableAt.hasDerivAt
  induction n generalizing w with
  | zero => simpa only [Nat.cast_zero, add_zero, iteratedDeriv_succ, iteratedDeriv_zero] using hode w
  | succ n ih =>
    have he : (id * iteratedDeriv (n + 2) f +
        ((fun _ => c + n) - id) * iteratedDeriv (n + 1) f -
        (fun z => (a + n) * iteratedDeriv n f z)) = (fun _ => 0) := funext ih
    have ht := (((hasDerivAt_id w).mul (hd (n + 2) w)).add
      (((hasDerivAt_const w (c + n)).sub (hasDerivAt_id w)).mul (hd (n + 1) w))).sub
      ((hd n w).const_mul (a + n))
    have he' := ht.deriv
    rw [he, deriv_const] at he'
    simp only [id_eq, one_mul, zero_sub, Pi.sub_apply] at he'
    push_cast
    linear_combination -he'

/-- Entire solutions of the confluent equation are determined by their value at zero
when the denominator parameter is not a nonpositive integer. -/
theorem confluent_ode_unique {a c : ℂ} {f g : ℂ → ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (hf : ∀ w, AnalyticAt ℂ f w) (hg : ∀ w, AnalyticAt ℂ g w)
    (hfeq : ∀ w, w * deriv (deriv f) w + (c - w) * deriv f w - a * f w = 0)
    (hgeq : ∀ w, w * deriv (deriv g) w + (c - w) * deriv g w - a * g w = 0)
    (hzero : f 0 = g 0) : f = g := by
  have he (n : ℕ) : iteratedDeriv n f 0 = iteratedDeriv n g 0 := by
    induction n with
    | zero => exact hzero
    | succ n ih =>
      have hfn := confluent_ode_iteratedDeriv hf hfeq n 0
      have hgn := confluent_ode_iteratedDeriv hg hgeq n 0
      have hcn : c + (n : ℂ) ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hc n
      have hm : (c + n) * (iteratedDeriv (n + 1) f 0 - iteratedDeriv (n + 1) g 0) = 0 := by
        rw [ih] at hfn
        linear_combination hfn - hgn
      exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hcn)
  apply AnalyticOnNhd.eq_of_eventuallyEq (fun w _ => hf w) (fun w _ => hg w) (z₀ := 0)
  have hp := (hf 0).hasFPowerSeriesAt
  have hq := (hg 0).hasFPowerSeriesAt
  simp_rw [he] at hp
  filter_upwards [hp.eventually_hasSum_sub, hq.eventually_hasSum_sub] with w hw₁ hw₂
  exact hw₁.unique hw₂

/-- The normalized Pochhammer factors have a recurrence with limit multiplier one. -/
theorem poch_div_pow_succ {b : ℂ} (hb : b ≠ 0) (n : ℕ) :
    poch b (n + 1) / b ^ (n + 1) = (poch b n / b ^ n) * (1 + (n : ℂ) / b) := by
  rw [poch_succ, pow_succ]
  field_simp

/-- Each normalized Pochhammer symbol tends to one as its parameter tends to infinity. -/
theorem tendsto_poch_div_pow (n : ℕ) :
    Tendsto (fun b : ℕ => poch (b : ℂ) n / (b : ℂ) ^ n) atTop (𝓝 1) := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    have ht := ih.mul ((tendsto_const_div_atTop_nhds_zero_nat (n : ℂ)).const_add 1)
    simp only [add_zero, mul_one] at ht
    apply ht.congr'
    filter_upwards [Filter.eventually_ne_atTop 0] with b hb
    exact (poch_div_pow_succ (Nat.cast_ne_zero.mpr hb) n).symm

/-- `(c + t)_k / t^k → 1` as the real variable `t → ∞`. -/
theorem tendsto_poch_add_div_pow (c : ℂ) (k : ℕ) :
    Tendsto (fun t : ℝ => poch (c + t) k / (t : ℂ) ^ k) atTop (𝓝 1) := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    have h0 : Tendsto (fun t : ℝ => (c + k) / (t : ℂ)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have : Tendsto (fun t : ℝ => ‖c + k‖ / t) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [norm_div, norm_real, Real.norm_of_nonneg ht.le]
    have ht := ih.mul (h0.const_add 1)
    simp only [add_zero, mul_one] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    rw [poch_succ, pow_succ]
    field_simp
    ring

/-- `(-N)_k / (-N)^k → 1` as the natural number `N → ∞`. -/
theorem tendsto_poch_neg_div_pow (k : ℕ) :
    Tendsto (fun N : ℕ => poch (-(N : ℂ)) k / (-(N : ℂ)) ^ k) atTop (𝓝 1) := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    have h0 : Tendsto (fun N : ℕ => -((k : ℂ) / N)) atTop (𝓝 0) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat (k : ℂ)).neg
    have ht := ih.mul (h0.const_add 1)
    simp only [add_zero, mul_one] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with N hN
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    rw [poch_succ, pow_succ]
    field_simp
    ring

/-- Normalized positive Pochhammer symbols decrease as the parameter increases. -/
theorem norm_poch_div_pow_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (n : ℕ) :
    ‖poch (y : ℂ) n / (y : ℂ) ^ n‖ ≤ ‖poch (x : ℂ) n / (x : ℂ) ^ n‖ := by
  have hy : 0 < y := hx.trans_le hxy
  have hnorm (t : ℝ) (ht : 0 < t) (k : ℕ) :
      ‖1 + (k : ℂ) / (t : ℂ)‖ = 1 + (k : ℝ) / t := by
    have he : (1 : ℂ) + k / (t : ℂ) = ((1 + (k : ℝ) / t : ℝ) : ℂ) := by push_cast; rfl
    rw [he, norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [poch_div_pow_succ (ofReal_ne_zero.mpr (ne_of_gt hy)),
      poch_div_pow_succ (ofReal_ne_zero.mpr (ne_of_gt hx)), norm_mul, norm_mul, hnorm y hy, hnorm x hx]
    exact mul_le_mul ih (add_le_add_right (div_le_div_of_nonneg_left (Nat.cast_nonneg n) hx hxy) 1)
      (by positivity) (norm_nonneg _)

/-- Rescaled Gauss coefficients separate into confluent coefficients and a normalized Pochhammer. -/
theorem gaussHGCoeff_mul_div_pow (a b c z : ℂ) (n : ℕ) :
    gaussHGCoeff a b c n * (z / b) ^ n =
      (kummerMCoeff a c n * z ^ n) * (poch b n / b ^ n) := by
  simp only [gaussHGCoeff, kummerMCoeff, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Confluence: `M(a,c,z) = lim_{b→∞} ₂F₁(a,b;c;z/b)`. -/
theorem tendsto_ordinaryHypergeometric_div_atTop {a c z : ℂ} :
    Tendsto (fun b : ℕ => ₂F₁ a (b : ℂ) c (z / b)) atTop (𝓝 (kummerM a c z)) := by
  obtain ⟨B, hB⟩ := exists_nat_gt ‖z‖
  have hBpos : (0 : ℝ) < B := (norm_nonneg z).trans_lt hB
  have harg : ‖z / (B : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_natCast, div_lt_one hBpos]
    exact hB
  let f (b n : ℕ) := gaussHGCoeff a (b : ℂ) c n * (z / b) ^ n
  let bound (n : ℕ) := ‖f B n‖
  have hsum : Summable bound :=
    ((hasFPowerSeriesOnBall_ordinaryHypergeometric a (B : ℂ) c).hasSum_mul_pow
      (mem_eball_one_of_norm_lt_one harg)).summable.norm
  have hlim (n : ℕ) : Tendsto (fun b => f b n) atTop (𝓝 (kummerMCoeff a c n * z ^ n)) := by
    simpa only [f, gaussHGCoeff_mul_div_pow, mul_one] using
      (tendsto_poch_div_pow n).const_mul (kummerMCoeff a c n * z ^ n)
  have hbound : ∀ᶠ b : ℕ in atTop, ∀ n, ‖f b n‖ ≤ bound n := by
    filter_upwards [eventually_ge_atTop B] with b hb n
    dsimp [bound, f]
    simp only [gaussHGCoeff_mul_div_pow, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    simpa only [ofReal_natCast] using norm_poch_div_pow_le hBpos (Nat.cast_le.mpr hb) n
  have ht := tendsto_tsum_of_dominated_convergence hsum hlim hbound
  have he (b : ℕ) : ₂F₁ a (b : ℂ) c (z / b) = ∑' n, f b n := by
    rw [ordinaryHypergeometric_eq_tsum]
    apply tsum_congr
    intro n
    simp only [f, gaussHGCoeff, poch, smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  simpa only [← he, kummerM, kummerMCoeff] using ht


/-- The connection formula for Tricomi's function at noninteger second parameter.
At integers, totalized Gamma factors do not give the continued value. -/
def kummerUConnection (a b z : ℂ) : ℂ :=
  Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b z +
    Gamma (b - 1) / Gamma a * z ^ (1 - b) * kummerM (a - b + 1) (2 - b) z

/-- Tricomi's principal-branch function, with integer second parameters assigned
by limits of the connection formula along noninteger parameters.
The definition alone does not establish existence of these limits; a `Tendsto`
theorem is required when using the integer branch. -/
@[dlmf 13.2.E42]
def kummerU (a b z : ℂ) : ℂ := by
  classical
  exact if ∀ k : ℤ, b ≠ k then kummerUConnection a b z else
    Filter.limUnder (𝓝[integerComplement] b) (fun c => kummerUConnection a c z)

/-- Tricomi's function agrees with its connection formula at noninteger parameters. -/
theorem kummerU_eq_connection (a b z : ℂ) (hb : ∀ k : ℤ, b ≠ k) :
    kummerU a b z = kummerUConnection a b z := by
  simp [kummerU, hb]

/-- The connection formula at zero first parameter is identically one away from integers. -/
theorem kummerUConnection_zero (b z : ℂ) (hb : ∀ k : ℤ, b ≠ k) :
    kummerUConnection 0 b z = 1 := by
  have hp : ∀ k : ℕ, 1 - b ≠ -(k : ℂ) := by
    intro k hk
    apply hb ((k : ℤ) + 1)
    push_cast
    linear_combination -hk
  simp only [kummerUConnection, kummerM_of_zero_param, Gamma_zero, div_zero,
    zero_mul, add_zero, mul_one]
  rw [show (0 : ℂ) - b + 1 = 1 - b by ring, div_self (Gamma_ne_zero hp)]

/-- The connection formula at zero first parameter converges to one at every second parameter. -/
theorem tendsto_kummerUConnection_zero (b z : ℂ) :
    Tendsto (fun c => kummerUConnection 0 c z) (𝓝[integerComplement] b) (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  symm
  apply kummerUConnection_zero c z
  intro k hk
  exact hc ⟨k, hk.symm⟩

/-- Tricomi's value at zero first parameter, including integer second parameters. -/
theorem kummerU_zero (b z : ℂ) : kummerU 0 b z = 1 := by
  classical
  unfold kummerU
  split_ifs with hb
  · exact kummerUConnection_zero b z hb
  · have hd : Dense integerComplement :=
      (Set.countable_range (fun k : ℤ => (k : ℂ))).dense_compl ℂ
    have : NeBot (𝓝[integerComplement] b) :=
      mem_closure_iff_nhdsWithin_neBot.mp (hd b)
    exact (tendsto_kummerUConnection_zero b z).limUnder_eq

/-- The noninteger connection formula on the logarithmic argument plane.
The variable `w` represents a logarithm of the actual argument `exp w`. -/
def kummerUOnLog (a b w : ℂ) : ℂ :=
  Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b (exp w) +
    Gamma (b - 1) / Gamma a * exp ((1 - b) * w) *
      kummerM (a - b + 1) (2 - b) (exp w)

/-- Euler's integral for Kummer's function, obtained by integrating the exponential
series against the beta weight (AAR §4.2). This is the `M` form of DLMF 13.4.1. -/
@[dlmf 13.4.E1]
theorem kummerM_eq_euler_integral {a c z : ℂ}
    (ha : 0 < a.re) (hca : 0 < (c - a).re) :
    kummerM a c z = Gamma c / (Gamma a * Gamma (c - a)) *
      ∫ t : ℝ in (0 : ℝ)..1,
        (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (c - a - 1) * exp (z * t) := by
  let w : ℝ → ℂ := fun t => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (c - a - 1)
  let d : ℕ → ℂ := fun n => z ^ n / n.factorial
  let F : ℕ → ℝ → ℂ := fun n t => w t * (d n * (t : ℂ) ^ n)
  have hexp (u : ℂ) : HasSum (fun n : ℕ => u ^ n / n.factorial) (exp u) := by
    simpa only [exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp u
  have hw : IntervalIntegrable w MeasureTheory.volume 0 1 := betaIntegral_convergent ha hca
  have hd : Summable (fun n => ‖d n‖) := (hexp z).summable.norm
  have hFi (n : ℕ) : IntervalIntegrable (F n) MeasureTheory.volume 0 1 :=
    hw.mul_continuousOn (by fun_prop)
  have hs := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 1) (μ := MeasureTheory.volume)
    (F := F) (f := fun t => w t * exp (z * t))
    (fun n t => ‖d n‖ * ‖w t‖) (fun n => (hFi n).def'.aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun t ht => ?_)
    (Filter.Eventually.of_forall fun t _ => hd.mul_right ‖w t‖)
    (by simp_rw [tsum_mul_right]; exact hw.norm.const_mul _)
    (Filter.Eventually.of_forall fun t _ => ?_)
  · have hterm (n : ℕ) : ∫ t : ℝ in (0 : ℝ)..1, F n t =
        betaIntegral (a + n) (c - a) / n.factorial * z ^ n := by
      rw [betaIntegral, div_eq_mul_inv, ← intervalIntegral.integral_mul_const,
        ← intervalIntegral.integral_mul_const]
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      have hp : (t : ℂ) ^ (a + n - 1) = (t : ℂ) ^ (a - 1) * (t : ℂ) ^ n := by
        rw [show a + n - 1 = (a - 1) + n by ring,
          cpow_add _ _ (ofReal_ne_zero.mpr ht.1.ne'), cpow_natCast]
      dsimp [F, w, d]
      rw [hp]
      ring
    have hscaled (n : ℕ) : Gamma c / (Gamma a * Gamma (c - a)) *
        (∫ t : ℝ in (0 : ℝ)..1, F n t) = kummerMCoeff a c n * z ^ n := by
      have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
      have he := euler_term_eq_gaussHGCoeff (a := 1) n ha hca
      simp only [poch_nat_one, div_self hf, one_mul, gaussHGCoeff] at he
      rw [hterm]
      dsimp [kummerMCoeff]
      linear_combination (norm := (field_simp; ring)) (z ^ n / n.factorial) * he
    have hs' := hs.mul_left (Gamma c / (Gamma a * Gamma (c - a)))
    simp_rw [hscaled] at hs'
    exact hs'.tsum_eq
  · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht1 : ‖(t : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1] using ht.2
    calc
      ‖F n t‖ = ‖w t‖ * (‖d n‖ * ‖(t : ℂ)‖ ^ n) := by
        simp only [F, norm_mul, norm_pow]
      _ ≤ ‖w t‖ * (‖d n‖ * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) ht1) (norm_nonneg _))
          (norm_nonneg _)
      _ = _ := by ring
  · convert (hexp (z * t)).mul_left (w t) using 1
    congr 1
    funext n
    simp only [F, d, mul_pow]
    ring

/-- The error function, entire in `z`, through the confluent series of AAR §4.4:
`erf z = (2z/√π) M(1/2, 3/2, -z²)`. On the real line it is TauCeti's `TauCeti.Real.erf`
(`erf_ofReal`). -/
@[dlmf 13.6.E7]
def erf (z : ℂ) : ℂ :=
  (2 : ℂ) / (Real.sqrt π : ℂ) * z * kummerM (1 / 2) (3 / 2) (-(z ^ 2))

/-- Complementary error function `erfc z = 1 - erf z`. -/
def erfc (z : ℂ) : ℂ := 1 - erf z

/-- `erf 0 = 0`. -/
theorem erf_zero : erf 0 = 0 := by simp [erf]

/-- The coefficient identity for the Gaussian antiderivative. -/
theorem kummerMCoeff_half (n : ℕ) :
    (2 * n + 1 : ℂ) * kummerMCoeff (1 / 2) (3 / 2) n = 1 / n.factorial := by
  have hp : poch (1 / 2 : ℂ) n ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (fun k hk => by
      have he := congrArg Complex.re hk
      simp at he
      have := Nat.cast_nonneg (α := ℝ) k
      linarith) n
  have hn : (2 * n + 1 : ℂ) ≠ 0 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  rw [kummerMCoeff, poch_three_halves_eq]
  field [hp, hn, Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- A first-order relation between the confluent series and the exponential. -/
theorem kummerM_half_add_two_mul_deriv (w : ℂ) :
    kummerM (1 / 2) (3 / 2) w +
      2 * w * deriv (kummerM (1 / 2) (3 / 2)) w = exp w := by
  have hc : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -k := by
    intro k hk
    have he := congrArg Complex.re hk
    simp at he
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hf := hasFPowerSeriesOnBall_kummerM (a := (1 / 2 : ℂ)) hc
  have hs := (hf.hasSum_mul_pow (z := w) (by simp)).add
    ((hf.hasSum_z_mul_deriv (z := w) (by simp)).mul_left 2)
  have heq : (fun n : ℕ => kummerMCoeff (1 / 2) (3 / 2) n * w ^ n +
      2 * ((n : ℂ) * kummerMCoeff (1 / 2) (3 / 2) n * w ^ n)) =
      (fun n : ℕ => w ^ n / n.factorial) := by
    funext n
    calc
      _ = ((2 * n + 1 : ℂ) * kummerMCoeff (1 / 2) (3 / 2) n) * w ^ n := by ring
      _ = _ := by rw [kummerMCoeff_half]; ring
  rw [heq] at hs
  simpa [mul_assoc] using hs.unique (by
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp w)

/-- Differentiating the confluent representation gives the Gaussian. -/
theorem hasDerivAt_gaussianPrimitive (z : ℂ) :
    HasDerivAt (fun z : ℂ => z * kummerM (1 / 2) (3 / 2) (-(z ^ 2)))
      (exp (-(z ^ 2))) z := by
  have hc : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -k := by
    intro k hk
    have he := congrArg Complex.re hk
    simp at he
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hf := hasFPowerSeriesOnBall_kummerM (a := (1 / 2 : ℂ)) hc
  have hm := (hf.analyticAt_of_mem (y := -(z ^ 2)) (by simp)).differentiableAt.hasDerivAt
  have hd := (hasDerivAt_id z).mul (hm.comp z (((hasDerivAt_id z).pow 2).neg))
  convert! hd using 1
  have h := kummerM_half_add_two_mul_deriv (-(z ^ 2))
  simp only [id_eq, Function.comp_apply, Pi.neg_apply, Pi.pow_apply,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, one_mul]
  linear_combination -h

/-- Integral representation `erf z = (2/√π) ∫_0^z e^{-t²} dt`. -/
@[dlmf 7.2.E1]
theorem erf_eq_integral (z : ℝ) :
    erf z =
      (2 : ℂ) / (Real.sqrt π : ℂ) *
        ∫ t : ℝ in (0 : ℝ)..z, Complex.exp (-(t : ℂ) ^ 2) := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_ : x ∈ Set.uIcc (0 : ℝ) z) => (hasDerivAt_gaussianPrimitive (x : ℂ)).comp_ofReal)
    (show IntervalIntegrable (fun t : ℝ => exp (-(t : ℂ) ^ 2)) MeasureTheory.volume 0 z from
      Continuous.intervalIntegrable (by fun_prop) _ _)
  simpa [erf, mul_assoc] using congrArg (fun w : ℂ => (2 : ℂ) / Real.sqrt π * w) hi.symm

/-- The complex error function on real inputs agrees with TauCeti's real error function. -/
theorem erf_ofReal (x : ℝ) : erf x = (TauCeti.Real.erf x : ℂ) := by
  rw [erf_eq_integral, TauCeti.Real.erf_def]
  push_cast
  congr 1
  rw [← intervalIntegral.integral_ofReal]
  congr 1
  funext t
  simp

/-- The complex complementary error function restricts to TauCeti's real complement. -/
theorem erfc_ofReal (x : ℝ) : erfc x = (TauCeti.Real.erfc x : ℂ) := by
  simp [erfc, erf_ofReal, TauCeti.Real.erfc_def]

/-- Lower incomplete gamma via `₁F₁`, AAR §4.4:
`γ(s,z) = z^s / s · M(s, s+1, -z)`. -/
@[dlmf 13.6.E5]
def lowerIncGamma (s z : ℂ) : ℂ :=
  z ^ s / s * kummerM s (s + 1) (-z)

section ParabolicRegion

/-! Saff–Varga zero-free parabolic regions (AAR §4.16); helper prefix `parab_`. -/

open Set Metric
open scoped NNReal

/-- The basic step of Saff–Varga: if `z` lies in the parabolic region `P_α` and `Re β ≥ α > 0`,
then `z + β ≠ 0` and `Re (z / (z + β)) < 1`. -/
theorem parab_step {α : ℝ} (hα : 0 < α) {z β : ℂ} (hz : z.im ^ 2 < 4 * α * (z.re + α))
    (hβ : α ≤ β.re) : z + β ≠ 0 ∧ (z / (z + β)).re < 1 := by
  have key : 0 < z.re * β.re + z.im * β.im + (β.re ^ 2 + β.im ^ 2) := by
    have h1 : 0 < z.re + β.re + α := by nlinarith [sq_nonneg z.im]
    have h2 : α * (z.re + α) ≤ β.re * (z.re + β.re) := by nlinarith
    nlinarith [sq_nonneg (β.im + z.im / 2)]
  have hne : z + β ≠ 0 := by
    intro h
    have hb : β = -z := by linear_combination h
    rw [hb] at key
    simp at key
    nlinarith
  refine ⟨hne, ?_⟩
  have hn : 0 < Complex.normSq (z + β) := Complex.normSq_pos.2 hne
  rw [Complex.div_re, ← add_div, div_lt_one hn]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im] at hn ⊢
  nlinarith

/-- **Saff–Varga for partial sums** (AAR Theorem 4.16.1 and Corollary 4.16.3). Let `A k > 0`
and `b (k+1) = A k / A (k+1)`. If `0 < α ≤ b 1` and `α ≤ b (k+2) - b (k+1)` for all `k`, then
no partial sum `∑_{k ≤ n} A k z^k` vanishes in the parabolic region `y² < 4α(x+α)`. -/
theorem parab_partialSums {A b : ℕ → ℝ} (hA : ∀ k, 0 < A k) (hb : ∀ k, 0 < b (k + 1))
    (hbA : ∀ k, b (k + 1) * A (k + 1) = A k) {α : ℝ} (hα : 0 < α) (h1 : α ≤ b 1)
    (h2 : ∀ k, α ≤ b (k + 2) - b (k + 1)) {z : ℂ} (hz : z.im ^ 2 < 4 * α * (z.re + α)) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (A k : ℂ) * z ^ k) ≠ 0 := by
  set S : ℕ → ℂ := fun n => ∑ k ∈ Finset.range (n + 1), (A k : ℂ) * z ^ k with hS
  have hbA' : ∀ k, (b (k + 1) : ℂ) * A (k + 1) = A k := fun k => by exact_mod_cast hbA k
  have hrec : ∀ n, (b (n + 2) : ℂ) * S (n + 2) = (z + b (n + 2)) * S (n + 1) - z * S n := by
    intro n
    simp only [hS, Finset.sum_range_succ]
    linear_combination (z ^ (n + 2)) * hbA' (n + 1)
  have hS0 : S 0 = A 0 := by simp [hS]
  have hb' : ∀ k, (b (k + 1) : ℂ) ≠ 0 := fun k => by exact_mod_cast (hb k).ne'
  have claim : ∀ n, S (n + 1) ≠ 0 ∧ (z * S n / (b (n + 1) * S (n + 1))).re < 1 := by
    intro n
    induction n with
    | zero =>
      have hrec1 : (b 1 : ℂ) * S 1 = (z + b 1) * S 0 := by
        simp only [hS, Finset.sum_range_succ, Finset.sum_range_zero]
        linear_combination z * hbA' 0
      obtain ⟨hne, hlt⟩ := parab_step hα (β := (b 1 : ℂ)) hz (by simpa using h1)
      have hA0 : S 0 ≠ 0 := by rw [hS0]; exact_mod_cast (hA 0).ne'
      have hS1 : S 1 = (z + b 1) * S 0 / b 1 := by
        rw [eq_div_iff (hb' 0), mul_comm, hrec1]
      refine ⟨by rw [hS1]; exact div_ne_zero (mul_ne_zero hne hA0) (hb' 0), ?_⟩
      rw [show (b (0 + 1) : ℂ) * S (0 + 1) = (z + b 1) * S 0 by simpa using hrec1]
      rwa [mul_div_mul_right _ _ hA0]
    | succ n ih =>
      obtain ⟨hne, hlt⟩ := ih
      set μ := z * S n / (b (n + 1) * S (n + 1)) with hμ
      set β : ℂ := b (n + 2) - b (n + 1) * μ with hβ
      have hβre : α ≤ β.re := by
        have : β.re = b (n + 2) - b (n + 1) * μ.re := by
          simp [hβ, Complex.mul_re]
        rw [this]
        have := h2 n
        nlinarith [hb n]
      obtain ⟨hzβ, hlt'⟩ := parab_step hα hz hβre
      have hμS : (b (n + 1) : ℂ) * μ * S (n + 1) = z * S n := by
        rw [hμ]; field_simp [hb' n]
      have hrec' : (b (n + 2) : ℂ) * S (n + 2) = S (n + 1) * (z + β) := by
        rw [hrec n, hβ]; linear_combination hμS
      have hS2 : S (n + 2) = S (n + 1) * (z + β) / b (n + 2) := by
        rw [eq_div_iff (hb' (n + 1)), mul_comm, hrec']
      refine ⟨by rw [hS2]; exact div_ne_zero (mul_ne_zero hne hzβ) (hb' (n + 1)), ?_⟩
      rw [show (b (n + 1 + 1) : ℂ) * S (n + 1 + 1) = S (n + 1) * (z + β) from hrec',
        mul_comm (S (n + 1)), mul_div_mul_right _ _ hne]
      exact hlt'
  rcases n with _ | n
  · change S 0 ≠ 0
    rw [hS0]; exact_mod_cast (hA 0).ne'
  · exact (claim n).1

/-- **A Hurwitz-type lemma.** Let functions `s n`, eventually zero-free on an open set `U`,
converge to `f` uniformly on every ball about `0`, and let `f` be analytic and not locally zero
at `z₀ ∈ U`. Then `f z₀ ≠ 0`. The proof applies the maximum modulus principle to `1 / s n` on a
small disk about `z₀`. -/
theorem parab_hurwitz {f : ℂ → ℂ} {s : ℕ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) {z₀ : ℂ}
    (hz₀ : z₀ ∈ U) (hf : AnalyticAt ℂ f z₀) (hfne : ¬∀ᶠ z in 𝓝 z₀, f z = 0)
    (hs : ∀ n, Differentiable ℂ (s n)) (hsU : ∀ᶠ n in atTop, ∀ z ∈ U, s n z ≠ 0)
    (hconv : ∀ R : ℝ≥0, TendstoUniformlyOn s f atTop (ball 0 R)) : f z₀ ≠ 0 := by
  intro h0
  rcases hf.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact hfne h
  obtain ⟨ε, hε, hεf⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
  obtain ⟨ε', hε', hε'U⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  set r := min ε ε' / 2 with hr
  have hm0 : 0 < min ε ε' := lt_min hε hε'
  have hr0 : 0 < r := by positivity
  have hrε : r < ε := by have := min_le_left ε ε'; linarith
  have hrε' : r < ε' := by have := min_le_right ε ε'; linarith
  have hcb : closedBall z₀ r ⊆ U := fun z hz =>
    hε'U (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hz) hrε'))
  have hsph : ∀ z ∈ sphere z₀ r, f z ≠ 0 := fun z hz => by
    rw [mem_sphere] at hz
    refine hεf (by rw [hz]; exact hrε) ?_
    intro hzz
    rw [hzz, dist_self] at hz
    exact hr0.ne' hz.symm
  set R : ℝ≥0 := ⟨‖z₀‖ + r + 1, by positivity⟩ with hR
  have hsub : closedBall z₀ r ⊆ ball 0 R := fun z hz => by
    rw [mem_ball, dist_zero_right]
    have h1 := mem_closedBall.1 hz
    rw [dist_eq_norm] at h1
    have h2 := norm_le_norm_add_norm_sub' z z₀
    change ‖z‖ < ‖z₀‖ + r + 1
    linarith
  have hfc : ContinuousOn f (closedBall z₀ r) :=
    ((hconv R).continuousOn (Frequently.of_forall fun n => (hs n).continuous.continuousOn)).mono
      hsub
  obtain ⟨w, hw, hwmin⟩ := (isCompact_sphere z₀ r).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 hr0.le)
    (continuous_norm.comp_continuousOn (hfc.mono sphere_subset_closedBall))
  set m := ‖f w‖ with hmdef
  have hm : 0 < m := norm_pos_iff.2 (hsph w hw)
  have hun := Metric.tendstoUniformlyOn_iff.1 (hconv R) (m / 2) (by positivity)
  obtain ⟨n, hn1, hn2⟩ := (hun.and hsU).exists
  have hsn0 : ‖s n z₀‖ < m / 2 := by
    have := hn1 z₀ (hsub (mem_closedBall_self hr0.le))
    rwa [dist_eq_norm, h0, zero_sub, norm_neg] at this
  have hsph' : ∀ z ∈ sphere z₀ r, m / 2 ≤ ‖s n z‖ := fun z hz => by
    have h1 : m ≤ ‖f z‖ := hwmin hz
    have h2 := hn1 z (hsub (sphere_subset_closedBall hz))
    rw [dist_eq_norm] at h2
    have h3 := norm_sub_norm_le (f z) (f z - s n z)
    rw [sub_sub_cancel] at h3
    linarith
  have hd : DiffContOnCl ℂ (fun z => (s n z)⁻¹) (ball z₀ r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z₀ hr0.ne']
    exact fun z hz => ((hs n z).inv (hn2 z (hcb hz))).differentiableWithinAt
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd (C := 2 / m)
    (fun z hz => by
      rw [frontier_ball z₀ hr0.ne'] at hz
      rw [norm_inv, ← inv_div]
      exact inv_anti₀ (by positivity) (hsph' z hz))
    (subset_closure (mem_ball_self hr0))
  have hpos : 0 < ‖s n z₀‖ := norm_pos_iff.2 (hn2 z₀ hz₀)
  rw [norm_inv, ← inv_div] at hmax
  have := (inv_le_inv₀ hpos (by positivity)).1 hmax
  linarith

/-- The ratio `b (k+1) = A k / A (k+1) = (k+1)(c+k)/(a+k)` of consecutive coefficients of
Kummer's series. -/
noncomputable def parab_b (a c : ℝ) (k : ℕ) : ℝ := k * (c + k - 1) / (a + k - 1)

/-- The real coefficients `(a)_k / ((c)_k k!)` of Kummer's series. -/
noncomputable def parab_A (a c : ℝ) (k : ℕ) : ℝ :=
  (ascPochhammer ℝ k).eval a / ((ascPochhammer ℝ k).eval c * k !)

/-- The three parameter cases of AAR Corollary 4.16.4 give the Saff–Varga conditions. -/
theorem parab_params {a c α : ℝ}
    (hparams : (0 < c ∧ c ≤ a ∧ α = c / a) ∨
      (1 ≤ a ∧ a ≤ c ∧ α = 1) ∨
      (0 < a ∧ a < 1 ∧ a ≤ c ∧ c < 2 * a / (1 - a) ∧
        α = (2 * a - c + c * a) / (a ^ 2 + a))) :
    0 < a ∧ 0 < c ∧ 0 < α ∧ α ≤ parab_b a c 1 ∧
      ∀ k : ℕ, α ≤ parab_b a c (k + 2) - parab_b a c (k + 1) := by
  have hdiff : ∀ k : ℕ, 0 < a → parab_b a c (k + 2) - parab_b a c (k + 1) =
      (a * c + 2 * a * (k + 1) - c + (k + 1) ^ 2 - (k + 1)) / ((a + (k + 1)) * (a + k)) := by
    intro k ha
    have h1 : 0 < a + k := by positivity
    have h2 : 0 < a + (k + 1) := by positivity
    simp only [parab_b]
    push_cast
    rw [div_sub_div _ _ (by ring_nf; positivity) (by ring_nf; positivity), div_eq_div_iff
      (by ring_nf; positivity) (by positivity)]
    ring
  rcases hparams with ⟨hc, hca, rfl⟩ | ⟨ha, hac, rfl⟩ | ⟨ha, ha1, hac, hc2, rfl⟩
  · have ha : 0 < a := lt_of_lt_of_le hc hca
    refine ⟨ha, hc, div_pos hc ha, by simp [parab_b], fun k => ?_⟩
    rw [hdiff k ha, div_le_div_iff₀ ha (by positivity)]
    have : (a * c + 2 * a * (k + 1) - c + (k + 1) ^ 2 - (k + 1)) * a -
        c * ((a + (k + 1)) * (a + k)) = (k + 1) * (a - c) * (2 * a + k) := by ring
    have : 0 ≤ ((k:ℝ) + 1) * (a - c) * (2 * a + k) := by
      have : (0:ℝ) ≤ k := k.cast_nonneg
      apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith
  · have ha0 : 0 < a := by linarith
    have hc : 0 < c := by linarith
    refine ⟨ha0, hc, one_pos, ?_, fun k => ?_⟩
    · have : parab_b a c 1 = c / a := by simp [parab_b]
      rw [this, le_div_iff₀ ha0]; linarith
    · rw [hdiff k ha0, le_div_iff₀ (by positivity)]
      have : (a * c + 2 * a * (k + 1) - c + (k + 1) ^ 2 - (k + 1)) -
          ((a + (k + 1)) * (a + k)) = (a - 1) * (c - a) := by ring
      nlinarith [mul_nonneg (show 0 ≤ a - 1 by linarith) (show 0 ≤ c - a by linarith)]
  · have hc : 0 < c := by linarith
    have h1a : 0 < 1 - a := by linarith
    have hα : 0 < 2 * a - c + c * a := by
      rw [lt_div_iff₀ h1a] at hc2; nlinarith
    have hden : 0 < a ^ 2 + a := by positivity
    refine ⟨ha, hc, div_pos hα hden, ?_, fun k => ?_⟩
    · simp only [parab_b]; push_cast
      rw [div_le_div_iff₀ hden (by linarith)]
      nlinarith [mul_nonneg (show 0 ≤ c - a by linarith) ha.le]
    · rw [hdiff k ha, div_le_div_iff₀ hden (by positivity)]
      have : (a * c + 2 * a * (k + 1) - c + (k + 1) ^ 2 - (k + 1)) * (a ^ 2 + a) -
          (2 * a - c + c * a) * ((a + (k + 1)) * (a + k)) =
          (1 - a) * (c - a) * (2 * a + k + 1) * k := by ring
      have : 0 ≤ (1 - a) * (c - a) * (2 * a + k + 1) * k := by
        have : (0:ℝ) ≤ k := k.cast_nonneg
        apply mul_nonneg (mul_nonneg (mul_nonneg h1a.le (by linarith)) (by linarith)) this
      nlinarith

/-- The parabolic zero-free regions of AAR Corollary 4.16.4. The partial sums are
zero-free there by Saff–Varga (`parab_partialSums`), and the limit by a Hurwitz-type
argument (`parab_hurwitz`). The hypothesis `hre` is implied by `him`. -/
theorem kummerM_ne_zero_of_mem_parabolicRegion {a c α : ℝ} {z : ℂ}
    (hparams : (0 < c ∧ c ≤ a ∧ α = c / a) ∨
      (1 ≤ a ∧ a ≤ c ∧ α = 1) ∨
      (0 < a ∧ a < 1 ∧ a ≤ c ∧ c < 2 * a / (1 - a) ∧
        α = (2 * a - c + c * a) / (a ^ 2 + a)))
    (hre : -α < z.re) (him : z.im ^ 2 < 4 * α * (z.re + α)) :
    kummerM a c z ≠ 0 := by
  obtain ⟨ha, hc, hα, h1, h2⟩ := parab_params hparams
  have hck : ∀ k : ℕ, (c : ℂ) ≠ -k := fun k h => by
    have : c = -(k : ℝ) := by exact_mod_cast h
    have := k.cast_nonneg (α := ℝ); linarith
  have hA : ∀ k, 0 < parab_A a c k := fun k => by
    unfold parab_A
    have := ascPochhammer_pos k a ha
    have := ascPochhammer_pos k c hc
    positivity
  have hb : ∀ k, 0 < parab_b a c (k + 1) := fun k => by
    unfold parab_b; push_cast
    have : (0:ℝ) ≤ k := k.cast_nonneg
    apply div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hbA : ∀ k, parab_b a c (k + 1) * parab_A a c (k + 1) = parab_A a c k := fun k => by
    unfold parab_b parab_A
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, Nat.factorial_succ]
    have h1 : 0 < a + k := by positivity
    have h2 : 0 < c + k := by positivity
    have h3 := ascPochhammer_pos k c hc
    have h4 := ascPochhammer_pos k a ha
    push_cast
    rw [show a + ((k:ℝ) + 1) - 1 = a + k by ring, show c + ((k:ℝ) + 1) - 1 = c + k by ring,
      div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hcoef : ∀ k, kummerMCoeff a c k = (parab_A a c k : ℂ) := fun k => by
    simp only [kummerMCoeff, parab_A, poch_ofReal]
    push_cast; ring
  set p := FormalMultilinearSeries.ofScalars ℂ (kummerMCoeff a c) with hp
  have hps := hasFPowerSeriesOnBall_kummerM (a := (a : ℂ)) hck
  have hsum : ∀ n, (fun y => p.partialSum n y) =
      fun y => ∑ k ∈ Finset.range n, (parab_A a c k : ℂ) * y ^ k := fun n => by
    funext y
    simp only [FormalMultilinearSeries.partialSum, hp, FormalMultilinearSeries.ofScalars_apply_eq,
      hcoef, smul_eq_mul]
  set U : Set ℂ := {z | z.im ^ 2 < 4 * α * (z.re + α)} with hU
  have hUo : IsOpen U := isOpen_lt (by fun_prop) (by fun_prop)
  refine parab_hurwitz (s := fun n y => p.partialSum n y) hUo him
    (hps.analyticAt_of_mem (by simp)) ?_ (fun n => ?_) ?_ (fun R => ?_)
  · intro hev
    have hon : AnalyticOnNhd ℂ (kummerM a c) univ := fun w _ => hps.analyticAt_of_mem (by simp)
    have := hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ z) hev (mem_univ 0)
    simp at this
  · simp only [hsum n]; fun_prop
  · filter_upwards [eventually_ge_atTop 1] with n hn w hw
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    simp only [hsum (m + 1)]
    exact parab_partialSums hA hb hbA hα h1 h2 hw m
  · have := hps.tendstoUniformlyOn (r' := R) ENNReal.coe_lt_top
    simpa using this


end ParabolicRegion

end DLMF.Confluent
