/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Whittaker
public import DLMF.Hypergeometric.Asymptotics
public import DLMF.Confluent.IntegralRepresentations
public import DLMF.Confluent.Continuation

/-!
# Asymptotic expansions (DLMF §§13.7, 13.8, 13.19)

Poincaré expansions are stated along the positive real axis. The two-sided expansion of
regularized M on closed upper-half-plane sectors (13.7.2) and the limits 13.2.6, 13.2.23 are in
`DLMF.Confluent.AsymptoticConsequences`, which follows the rotated-sector expansions. Tricomi remainder
statements include an error bound or an asymptotic order, rather than an arbitrary
additive error. Remainder-region machinery 13.7.5–13.7.9 and 13.7.11–13.7.13, uniform
parabolic-cylinder/Bessel approximations 13.8.4–13.8.16, and the uniform
turning-point expansions of §§13.20–13.21 (Airy/Bessel with `envAi`/`envJ`)
are deferred.

Following Temme, *Special Functions*, §§7.1–7.2, the positive-axis expansions are derived
from Watson's lemma (`DLMFMathlib.Analysis.Asymptotics.Watson`):

* `hasAsymptoticExpansion_kummerU`: `U(a,b,x) ~ ∑ (-1)^s (a)_s (a-b+1)_s / s! · x^{-a-s}`
  for all complex `a, b`, from the Laplace integral for `re a > 0` and the contiguous
  relation 13.3.10;
* `kummerU_poincare_finite`: for real `a > 0`, `b ≤ a + 1` the remainder is bounded by the
  first omitted term;
* `hasAsymptoticExpansion_kummerU_sector`: the same expansion for complex `z → ∞` in every
  sector `δ |z| ≤ re z`, from Watson's lemma in a sector;
* `hasAsymptoticExpansion_regularizedConfluent`: `𝐌(a,b,x) ~ eˣ x^{a-b}/Γ(a) ·
  ∑ (1-a)_s (b-a)_s / s! · x^{-s}` for all complex `a, b`, from the Euler integral and the
  regularized contiguous relations;
* `kummerM_large_b_poincare` (13.8.2) for all complex `a`: Watson's lemma for `re a > 0`, then
  uniqueness of asymptotic expansions against 13.8.1 and the identity theorem in `a`.
-/

@[expose] public section

open Complex Filter MeasureTheory Asymptotics
open scoped Real Topology Nat
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- The coefficient `(-1)^s (a)_s (a-b+1)_s / s!` of the Tricomi expansion. -/
def tricomiCoeff (a b : ℂ) (s : ℕ) : ℂ :=
  (-1) ^ s * poch a s * poch (a - b + 1) s / s.factorial

/-- Binomial coefficients with negated upper index as Pochhammer symbols. -/
theorem ring_choose_neg_eq_poch (r : ℂ) (n : ℕ) :
    Ring.choose (-r) n = (-1) ^ n * poch r n / n.factorial := by
  rw [Ring.choose_neg', Int.negOnePow_def, zpow_natCast, Units.smul_def, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one, zsmul_eq_mul]
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer r n
  rw [Polynomial.ascPochhammer_smeval_eq_eval, nsmul_eq_mul] at h
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [eq_div_iff hf, poch, ← h]
  push_cast
  ring

/-- The binomial expansion of `(1+t)^β` at `t = 0⁺`, with an `O(t^N)` remainder. -/
theorem one_add_cpow_sub_sum_isBigO (β : ℂ) (N : ℕ) :
    (fun t : ℝ => (1 + (t : ℂ)) ^ β - ∑ n ∈ Finset.range N, Ring.choose β n * (t : ℂ) ^ n)
      =O[𝓝[>] 0] fun t => t ^ N := by
  have h := (Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := β)).isBigO_sub_partialSum_pow N
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  refine ((h.comp_tendsto ht).congr' (Eventually.of_forall fun t => ?_) ?_)
  · simp [FormalMultilinearSeries.partialSum, binomialSeries,
      smul_eq_mul, mul_comm]
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp [abs_of_pos (show (0 : ℝ) < t from ht)]

/-- **Tricomi's expansion for `re a > 0`**, by Watson's lemma applied to the Laplace
representation 13.4.4. -/
theorem hasAsymptoticExpansion_kummerU_of_re_pos {a b : ℂ} (ha : 0 < a.re) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => (x : ℂ) ^ (-((n : ℂ) + a)))
      (tricomiCoeff a b) (fun x : ℝ => kummerU a b x) := by
  set F : ℝ → ℂ := fun t => (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1) with hFdef
  have hint : IntegrableOn (fun t => Real.exp (-1 * t) • F t) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun (kummerU_laplace_integrable (b := b) ha
      (z := 1) (by simp)) (fun t _ => ?_) measurableSet_Ioi
    simp only [hFdef, Complex.real_smul, Complex.ofReal_exp]
    push_cast
    ring
  have hF : ∀ N : ℕ, (fun t => F t - ∑ n ∈ Finset.range N,
      ((t : ℂ) ^ ((n : ℂ) + a - 1)) • Ring.choose (b - a - 1) n) =O[𝓝[>] 0]
      fun t => t ^ ((N : ℝ) + a.re - 1) := by
    intro N
    have h1 : (fun t : ℝ => (t : ℂ) ^ (a - 1)) =O[𝓝[>] 0] fun t => t ^ (a.re - 1) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht : (0 : ℝ) < t := ht
      rw [norm_cpow_eq_rpow_re_of_pos ht, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos ht _)]
      simp
    refine ((h1.mul (one_add_cpow_sub_sum_isBigO (b - a - 1) N)).congr' ?_ ?_)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
      simp only [hFdef, smul_eq_mul, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [show (n : ℂ) + a - 1 = (n : ℂ) + (a - 1) by ring, Complex.cpow_add _ _ ht0,
        Complex.cpow_natCast]
      ring
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht : (0 : ℝ) < t := ht
      rw [show (N : ℝ) + a.re - 1 = (a.re - 1) + N by ring, Real.rpow_add ht,
        Real.rpow_natCast]
  have hW := (hasAsymptoticExpansion_integral_exp_smul_cpow ha hint hF).const_smul
    (1 / Gamma a)
  have ha' : ∀ k : ℕ, a ≠ -k := fun k hk => by
    have := congrArg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  refine (hW.congr' ?_).congr_coeff ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [kummerU_laplace ha (by simpa using hx)]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hFdef, Complex.real_smul, Complex.ofReal_exp]
    push_cast
    ring
  · funext n
    have hG : Gamma (a + n) / Gamma a = poch a n := Gamma_add_nat_div_Gamma_eq (n := n) a ha'
    have hG0 : Gamma a ≠ 0 := Complex.Gamma_ne_zero ha'
    simp only [Pi.smul_apply, smul_eq_mul, tricomiCoeff]
    rw [show b - a - 1 = -(a - b + 1) by ring, ring_choose_neg_eq_poch,
      show (n : ℂ) + a = a + n by ring, ← hG]
    field_simp

/-- The coefficient recurrence behind 13.3.10. -/
theorem tricomiCoeff_sub_one_succ (a b : ℂ) (n : ℕ) :
    tricomiCoeff (a - 1) b (n + 1) =
      tricomiCoeff a (b + 1) (n + 1) - (b - a) * tricomiCoeff a b n := by
  simp only [tricomiCoeff]
  have h1 : poch (a - 1) (n + 1) = (a - 1) * poch a n := by
    rw [poch_succ_left, sub_add_cancel]
  have h2 : poch (a - 1 - b + 1) (n + 1) = (a - b) * poch (a - b + 1) n := by
    rw [poch_succ_left]; ring_nf
  have h3 : poch (a - (b + 1) + 1) (n + 1) = (a - b) * poch (a - b + 1) n := by
    rw [poch_succ_left]; ring_nf
  rw [h1, h2, h3, poch_succ, Nat.factorial_succ]
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  push_cast
  field_simp
  ring

/-- The leading coefficient of the Tricomi expansion is `1`. -/
theorem tricomiCoeff_zero (a b : ℂ) : tricomiCoeff a b 0 = 1 := by
  simp [tricomiCoeff, poch_zero]

/-- The norm of the Tricomi scale on the positive axis. -/
theorem norm_ofReal_cpow_neg_add {x : ℝ} (hx : 0 < x) (n : ℕ) (a : ℂ) :
    ‖(x : ℂ) ^ (-((n : ℂ) + a))‖ = x ^ (-((n : ℝ) + a.re)) := by
  rw [norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- The downward step in the first parameter, from DLMF 13.3.10:
`U(a-1,b,x) = x U(a,b+1,x) - (b-a) U(a,b,x)`. -/
theorem hasAsymptoticExpansion_kummerU_sub_one {a b : ℂ}
    (h1 : HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => (x : ℂ) ^ (-((n : ℂ) + a)))
      (tricomiCoeff a (b + 1)) (fun x : ℝ => kummerU a (b + 1) x))
    (h2 : HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => (x : ℂ) ^ (-((n : ℂ) + a)))
      (tricomiCoeff a b) (fun x : ℝ => kummerU a b x)) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => (x : ℂ) ^ (-((n : ℂ) + (a - 1))))
      (tricomiCoeff (a - 1) b) (fun x : ℝ => kummerU (a - 1) b x) := by
  intro N
  have hx1 : (fun x : ℝ => (x : ℂ) * ((x : ℂ) ^ (-((N : ℂ) + a)))) =ᶠ[atTop]
      fun x : ℝ => (x : ℂ) ^ (-((N : ℂ) + (a - 1))) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [show -((N : ℂ) + (a - 1)) = 1 + -((N : ℂ) + a) by ring, Complex.cpow_add _ _ hx0,
      Complex.cpow_one]
  have hA : (fun x : ℝ => (x : ℂ) * (kummerU a (b + 1) x -
      ∑ n ∈ Finset.range N, (x : ℂ) ^ (-((n : ℂ) + a)) • tricomiCoeff a (b + 1) n)) =O[atTop]
      fun x : ℝ => (x : ℂ) ^ (-((N : ℂ) + (a - 1))) :=
    ((isBigO_refl (fun x : ℝ => (x : ℂ)) atTop).mul (h1 N)).congr' EventuallyEq.rfl hx1
  have hφ : (fun x : ℝ => (x : ℂ) ^ (-(((N - 1 : ℕ) : ℂ) + a))) =O[atTop]
      fun x : ℝ => (x : ℂ) ^ (-((N : ℂ) + (a - 1))) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    have hx0 : 0 < x := by linarith
    rw [norm_ofReal_cpow_neg_add hx0, one_mul, norm_cpow_eq_rpow_re_of_pos hx0]
    refine Real.rpow_le_rpow_of_exponent_le hx ?_
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.sub_re,
      Complex.one_re]
    have : (N : ℝ) ≤ ((N - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : N ≤ N - 1 + 1)
    linarith
  have hB := (((h2 (N - 1)).trans hφ).const_mul_left (b - a))
  refine (hA.sub hB).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hU := kummerU_contiguous_shift_a a b x hx0
  have hsh : ∀ n : ℕ, (x : ℂ) ^ (-((n : ℂ) + a)) =
      (x : ℂ) ^ (-(((n + 1 : ℕ) : ℂ) + (a - 1))) := fun n => by push_cast; ring_nf
  have hmul : ∀ n : ℕ, (x : ℂ) * (x : ℂ) ^ (-((n : ℂ) + a)) =
      (x : ℂ) ^ (-((n : ℂ) + (a - 1))) := fun n => by
    rw [show -((n : ℂ) + (a - 1)) = 1 + -((n : ℂ) + a) by ring, Complex.cpow_add _ _ hx0,
      Complex.cpow_one]
  simp only [smul_eq_mul]
  rcases N with _ | M
  · simp only [Finset.range_zero, Finset.sum_empty, sub_zero]
    linear_combination -hU
  · have hsum : ∑ n ∈ Finset.range (M + 1), (x : ℂ) ^ (-((n : ℂ) + (a - 1))) *
        tricomiCoeff (a - 1) b n =
        (x : ℂ) * ∑ n ∈ Finset.range (M + 1), (x : ℂ) ^ (-((n : ℂ) + a)) *
          tricomiCoeff a (b + 1) n -
        (b - a) * ∑ n ∈ Finset.range M, (x : ℂ) ^ (-((n : ℂ) + a)) * tricomiCoeff a b n := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum, mul_add,
        Finset.mul_sum]
      have hterm : ∀ i ∈ Finset.range M,
          (x : ℂ) ^ (-(((i + 1 : ℕ) : ℂ) + (a - 1))) * tricomiCoeff (a - 1) b (i + 1) =
          (x : ℂ) * ((x : ℂ) ^ (-(((i + 1 : ℕ) : ℂ) + a)) * tricomiCoeff a (b + 1) (i + 1)) -
            (b - a) * ((x : ℂ) ^ (-((i : ℂ) + a)) * tricomiCoeff a b i) := by
        intro i _
        rw [tricomiCoeff_sub_one_succ, hsh i, ← hmul (i + 1)]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← hmul 0]
      simp only [tricomiCoeff_zero, Nat.cast_zero]
      ring
    simp only [Nat.add_sub_cancel]
    rw [hsum]
    linear_combination -hU

/-- **Tricomi's asymptotic expansion** (DLMF 13.7.3, Temme §7.2) on the positive axis:
`U(a,b,x) ~ ∑ (-1)^s (a)_s (a-b+1)_s / s! · x^{-a-s}` as `x → +∞`, for all complex `a, b`. -/
theorem hasAsymptoticExpansion_kummerU (a b : ℂ) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => (x : ℂ) ^ (-((n : ℂ) + a)))
      (tricomiCoeff a b) (fun x : ℝ => kummerU a b x) := by
  suffices h : ∀ m : ℕ, ∀ a b : ℂ, 0 < (a + m).re →
      HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => (x : ℂ) ^ (-((n : ℂ) + a)))
        (tricomiCoeff a b) (fun x : ℝ => kummerU a b x) by
    obtain ⟨m, hm⟩ := exists_nat_gt (-a.re)
    exact h m a b (by simp; linarith)
  intro m
  induction m with
  | zero => intro a b ha; exact hasAsymptoticExpansion_kummerU_of_re_pos (by simpa using ha)
  | succ m ih =>
    intro a b ha
    have h := hasAsymptoticExpansion_kummerU_sub_one
      (ih (a + 1) (b + 1) (by simp at ha ⊢; linarith))
      (ih (a + 1) b (by simp at ha ⊢; linarith))
    simpa using h


/-- The downward step in `a` along any filter on which `|z| ≥ 1` eventually. -/
theorem hasAsymptoticExpansion_kummerU_sub_one_of_filter {l : Filter ℂ}
    (hl : ∀ᶠ z in l, 1 ≤ ‖z‖) {a b : ℂ}
    (h1 : HasAsymptoticExpansion l (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + a)))
      (tricomiCoeff a (b + 1)) (fun z => kummerU a (b + 1) z))
    (h2 : HasAsymptoticExpansion l (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + a)))
      (tricomiCoeff a b) (fun z => kummerU a b z)) :
    HasAsymptoticExpansion l (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + (a - 1))))
      (tricomiCoeff (a - 1) b) (fun z => kummerU (a - 1) b z) := by
  intro N
  have hz0 : ∀ᶠ z in l, z ≠ 0 := hl.mono fun z hz h => by rw [h, norm_zero] at hz; linarith
  have hmul : ∀ z : ℂ, z ≠ 0 → ∀ w : ℂ, z * z ^ (-(w + a)) = z ^ (-(w + (a - 1))) := by
    intro z hz w
    rw [show -(w + (a - 1)) = 1 + -(w + a) by ring, Complex.cpow_add _ _ hz, Complex.cpow_one]
  have hA : (fun z : ℂ => z * (kummerU a (b + 1) z -
      ∑ n ∈ Finset.range N, z ^ (-((n : ℂ) + a)) • tricomiCoeff a (b + 1) n)) =O[l]
      fun z : ℂ => z ^ (-((N : ℂ) + (a - 1))) :=
    ((isBigO_refl (fun z : ℂ => z) l).mul (h1 N)).congr' EventuallyEq.rfl
      (hz0.mono fun z hz => hmul z hz _)
  have hφ : (fun z : ℂ => z ^ (-(((N - 1 : ℕ) : ℂ) + a))) =O[l]
      fun z : ℂ => z ^ (-((N : ℂ) + (a - 1))) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hl] with z hz
    have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [Nat.zero_sub, CharP.cast_eq_zero, zero_add, one_mul]
      rw [show -(a - 1) = 1 + -a by ring, Complex.cpow_add _ _ hz0, Complex.cpow_one, norm_mul]
      exact le_mul_of_one_le_left (norm_nonneg _) hz
    · rw [one_mul, show ((N - 1 : ℕ) : ℂ) + a = (N : ℂ) + (a - 1) by
        rw [Nat.cast_sub hN]; push_cast; ring]
  have hB := (((h2 (N - 1)).trans hφ).const_mul_left (b - a))
  refine (hA.sub hB).congr' ?_ EventuallyEq.rfl
  filter_upwards [hz0] with x hx0
  have hU := kummerU_contiguous_shift_a a b x hx0
  have hsh : ∀ n : ℕ, x ^ (-((n : ℂ) + a)) = x ^ (-(((n + 1 : ℕ) : ℂ) + (a - 1))) :=
    fun n => by push_cast; ring_nf
  simp only [smul_eq_mul]
  rcases N with _ | M
  · simp only [Finset.range_zero, Finset.sum_empty, sub_zero]
    linear_combination -hU
  · have hsum : ∑ n ∈ Finset.range (M + 1), x ^ (-((n : ℂ) + (a - 1))) *
        tricomiCoeff (a - 1) b n =
        x * ∑ n ∈ Finset.range (M + 1), x ^ (-((n : ℂ) + a)) * tricomiCoeff a (b + 1) n -
        (b - a) * ∑ n ∈ Finset.range M, x ^ (-((n : ℂ) + a)) * tricomiCoeff a b n := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum, mul_add,
        Finset.mul_sum]
      have hterm : ∀ i ∈ Finset.range M,
          x ^ (-(((i + 1 : ℕ) : ℂ) + (a - 1))) * tricomiCoeff (a - 1) b (i + 1) =
          x * (x ^ (-(((i + 1 : ℕ) : ℂ) + a)) * tricomiCoeff a (b + 1) (i + 1)) -
            (b - a) * (x ^ (-((i : ℂ) + a)) * tricomiCoeff a b i) := by
        intro i _
        rw [tricomiCoeff_sub_one_succ, hsh i, ← hmul x hx0 ((i + 1 : ℕ) : ℂ)]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← hmul x hx0 ((0 : ℕ) : ℂ)]
      simp only [tricomiCoeff_zero, Nat.cast_zero]
      ring
    simp only [Nat.add_sub_cancel]
    rw [hsum]
    linear_combination -hU

/-- Eventually along a sector filter at infinity, `1 ≤ |z|`. -/
theorem one_le_norm_sectorAtTop (δ : ℝ) : ∀ᶠ z in sectorAtTop δ, 1 ≤ ‖z‖ :=
  eventually_sectorAtTop (R := 1) fun _ hz _ => hz

/-- **Tricomi's expansion in a sector**, for `re a > 0`: as `z → ∞` with `δ |z| ≤ re z`,
`U(a,b,z) ~ ∑ (-1)^s (a)_s (a-b+1)_s / s! · z^{-a-s}` (DLMF 13.7.3). -/
theorem hasAsymptoticExpansion_kummerU_sector_of_re_pos {a b : ℂ} (ha : 0 < a.re) {δ : ℝ}
    (hδ : 0 < δ) :
    HasAsymptoticExpansion (sectorAtTop δ) (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + a)))
      (tricomiCoeff a b) (fun z => kummerU a b z) := by
  set F : ℝ → ℂ := fun t => (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1) with hFdef
  have hint : IntegrableOn (fun t => Real.exp (-1 * t) • F t) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun (kummerU_laplace_integrable (b := b) ha
      (z := 1) (by simp)) (fun t _ => ?_) measurableSet_Ioi
    simp only [hFdef, Complex.real_smul, Complex.ofReal_exp]
    push_cast
    ring
  have hF : ∀ N : ℕ, (fun t => F t - ∑ n ∈ Finset.range N,
      ((t : ℂ) ^ ((n : ℂ) + a - 1)) • Ring.choose (b - a - 1) n) =O[𝓝[>] 0]
      fun t => t ^ ((N : ℝ) + a.re - 1) := by
    intro N
    have h1 : (fun t : ℝ => (t : ℂ) ^ (a - 1)) =O[𝓝[>] 0] fun t => t ^ (a.re - 1) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht : (0 : ℝ) < t := ht
      rw [norm_cpow_eq_rpow_re_of_pos ht, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos ht _)]
      simp
    refine ((h1.mul (one_add_cpow_sub_sum_isBigO (b - a - 1) N)).congr' ?_ ?_)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
      simp only [hFdef, smul_eq_mul, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [show (n : ℂ) + a - 1 = (n : ℂ) + (a - 1) by ring, Complex.cpow_add _ _ ht0,
        Complex.cpow_natCast]
      ring
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht : (0 : ℝ) < t := ht
      rw [show (N : ℝ) + a.re - 1 = (a.re - 1) + N by ring, Real.rpow_add ht,
        Real.rpow_natCast]
  have hW := (hasAsymptoticExpansion_integral_cexp_smul_sector ha hδ hint hF).const_smul
    (1 / Gamma a)
  have ha' : ∀ k : ℕ, a ≠ -k := fun k hk => by
    have := congrArg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  refine (hW.congr' ?_).congr_coeff ?_
  · refine eventually_sectorAtTop (R := 1) fun z hz hzs => ?_
    have hre : 0 < z.re := lt_of_lt_of_le (by positivity) hzs
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [kummerU_laplace ha hre]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hFdef, smul_eq_mul]
    ring_nf
  · funext n
    have hG : Gamma (a + n) / Gamma a = poch a n := Gamma_add_nat_div_Gamma_eq (n := n) a ha'
    have hG0 : Gamma a ≠ 0 := Complex.Gamma_ne_zero ha'
    simp only [Pi.smul_apply, smul_eq_mul, tricomiCoeff]
    rw [show b - a - 1 = -(a - b + 1) by ring, ring_choose_neg_eq_poch,
      show (n : ℂ) + a = a + n by ring, ← hG]
    field_simp

/-- **Tricomi's expansion in a sector** (DLMF 13.7.3, Temme §7.2): for all complex `a, b`, as
`z → ∞` with `δ |z| ≤ re z` (`δ > 0`), `U(a,b,z) ~ ∑ (-1)^s (a)_s (a-b+1)_s / s! · z^{-a-s}`. -/
theorem hasAsymptoticExpansion_kummerU_sector (a b : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    HasAsymptoticExpansion (sectorAtTop δ) (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + a)))
      (tricomiCoeff a b) (fun z => kummerU a b z) := by
  suffices h : ∀ m : ℕ, ∀ a b : ℂ, 0 < (a + m).re →
      HasAsymptoticExpansion (sectorAtTop δ) (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + a)))
        (tricomiCoeff a b) (fun z => kummerU a b z) by
    obtain ⟨m, hm⟩ := exists_nat_gt (-a.re)
    exact h m a b (by simp; linarith)
  intro m
  induction m with
  | zero =>
    intro a b ha
    exact hasAsymptoticExpansion_kummerU_sector_of_re_pos (by simpa using ha) hδ
  | succ m ih =>
    intro a b ha
    have h := hasAsymptoticExpansion_kummerU_sub_one_of_filter (one_le_norm_sectorAtTop δ)
      (ih (a + 1) (b + 1) (by simp at ha ⊢; linarith))
      (ih (a + 1) b (by simp at ha ⊢; linarith))
    simpa using h

/-- The partial sums of Tricomi's expansion in the form of DLMF 13.7.3. -/
theorem kummerU_sum_eq {x : ℝ} (hx : 0 < x) (a b : ℂ) (n : ℕ) :
    ∑ s ∈ Finset.range n, (x : ℂ) ^ (-((s : ℂ) + a)) • tricomiCoeff a b s =
      (x : ℂ) ^ (-a) * ∑ s ∈ Finset.range n,
        poch a s * poch (a - b + 1) s / s.factorial * (-(x : ℂ)) ^ (-(s : ℂ)) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_eq_mul, tricomiCoeff, Complex.cpow_neg (-(x : ℂ)), Complex.cpow_natCast,
    show -((s : ℂ) + a) = -a + -(s : ℂ) by ring, Complex.cpow_add _ _ hx0,
    Complex.cpow_neg _ (s : ℂ), Complex.cpow_natCast, neg_pow (x : ℂ) s, mul_inv]
  have h1 : ((-1 : ℂ) ^ s)⁻¹ = (-1) ^ s := by rw [← inv_pow, inv_neg, inv_one]
  rw [h1]
  ring

/-- The binomial expansion of `(1-t)^β` at `t = 0⁺`, with an `O(t^N)` remainder. -/
theorem one_sub_cpow_sub_sum_isBigO (β : ℂ) (N : ℕ) :
    (fun t : ℝ => (1 - (t : ℂ)) ^ β -
      ∑ n ∈ Finset.range N, Ring.choose β n * (-(t : ℂ)) ^ n) =O[𝓝[>] 0] fun t => t ^ N := by
  have h := (Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := β)).isBigO_sub_partialSum_pow N
  have ht : Tendsto (fun t : ℝ => -(t : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => -(t : ℂ) := by fun_prop
    exact (hc.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
  refine ((h.comp_tendsto ht).congr' (Eventually.of_forall fun t => ?_) ?_)
  · simp [FormalMultilinearSeries.partialSum, binomialSeries, smul_eq_mul, mul_comm,
      sub_eq_add_neg]
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp [abs_of_pos (show (0 : ℝ) < t from ht)]

/-- The coefficient `(1-a)_s (b-a)_s / (s! Γ(a))` of the Kummer expansion 13.7.1. -/
def kummerCoeff (a b : ℂ) (s : ℕ) : ℂ :=
  poch (1 - a) s * poch (b - a) s / s.factorial * (Gamma a)⁻¹

/-- **The expansion of `𝐌(a,b,x)` for `re b > re a > 0`**, by Watson's lemma applied to the
Euler integral 13.4.1 after the substitution `t ↦ 1 - t`. -/
theorem hasAsymptoticExpansion_regularizedConfluent_of_re_pos {a b : ℂ} (ha : 0 < a.re)
    (hba : 0 < (b - a).re) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => exp (x : ℂ) * (x : ℂ) ^ (a - b - n))
      (kummerCoeff a b) (fun x : ℝ => regularizedHGFun {a} {b} (x : ℂ)) := by
  set G : ℝ → ℂ := fun t => (t : ℂ) ^ (b - a - 1) * (1 - (t : ℂ)) ^ (a - 1) with hGdef
  set F : ℝ → ℂ := Set.indicator (Set.Iio 1) G with hFdef
  have hGint : IntegrableOn G (Set.Ioo 0 1) := by
    have h := betaIntegral_convergent (u := b - a) (v := a) hba ha
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp h
  have hint : IntegrableOn (fun t => Real.exp (-0 * t) • F t) (Set.Ioi 0) := by
    simp only [neg_zero, zero_mul, Real.exp_zero, one_smul, hFdef]
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Iio]
    change Integrable G ((volume.restrict (Set.Ioi 0)).restrict (Set.Iio 1))
    rw [Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi]
    exact hGint
  have hF : ∀ N : ℕ, (fun t => F t - ∑ n ∈ Finset.range N,
      ((t : ℂ) ^ ((n : ℂ) + (b - a) - 1)) • ((-1) ^ n * Ring.choose (a - 1) n)) =O[𝓝[>] 0]
      fun t => t ^ ((N : ℝ) + (b - a).re - 1) := by
    intro N
    have h1 : (fun t : ℝ => (t : ℂ) ^ (b - a - 1)) =O[𝓝[>] 0] fun t => t ^ ((b - a).re - 1) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht : (0 : ℝ) < t := ht
      rw [norm_cpow_eq_rpow_re_of_pos ht, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos ht _)]
      simp
    refine ((h1.mul (one_sub_cpow_sub_sum_isBigO (a - 1) N)).congr' ?_ ?_)
    · have h1mem : Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
        nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
      filter_upwards [self_mem_nhdsWithin, h1mem] with t ht ht1
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
      simp only [hFdef, hGdef, Set.indicator_of_mem (show t ∈ Set.Iio 1 from ht1), smul_eq_mul,
        mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [show (n : ℂ) + (b - a) - 1 = (n : ℂ) + (b - a - 1) by ring, Complex.cpow_add _ _ ht0,
        Complex.cpow_natCast, neg_pow]
      ring
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht : (0 : ℝ) < t := ht
      rw [show (N : ℝ) + (b - a).re - 1 = ((b - a).re - 1) + N by ring, Real.rpow_add ht,
        Real.rpow_natCast]
  have hW := ((hasAsymptoticExpansion_integral_exp_smul_cpow hba hint hF).const_smul
    (1 / (Gamma a * Gamma (b - a)))).mul_left (fun x : ℝ => exp (x : ℂ))
  have hba' : ∀ k : ℕ, b - a ≠ -k := fun k hk => by
    have := congrArg Complex.re hk
    simp only [Complex.neg_re, Complex.natCast_re] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have ha' : ∀ k : ℕ, a ≠ -k := fun k hk => by
    have := congrArg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  refine ((hW.congr' ?_).congr_scale fun n => Eventually.of_forall fun x => ?_).congr_coeff ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Pi.smul_apply, smul_eq_mul]
    have hI : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-x * t) • F t =
        ∫ t in (0 : ℝ)..1, Real.exp (-x * t) • G t := by
      have hfun : (fun t => Real.exp (-x * t) • F t) =
          Set.indicator (Set.Iio 1) (fun t => Real.exp (-x * t) • G t) := by
        funext t
        by_cases ht : t < 1 <;> simp [hFdef, Set.indicator, ht]
      rw [hfun, setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio,
        intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    have hsub := intervalIntegral.integral_comp_sub_left
      (fun t : ℝ => exp ((x : ℂ) * t) * (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1))
      (a := 0) (b := 1) 1
    simp only [sub_self, sub_zero] at hsub
    have hcongr : ∀ t : ℝ, exp (x : ℂ) * (Real.exp (-x * t) • G t) =
        exp ((x : ℂ) * ((1 - t : ℝ) : ℂ)) * (((1 - t : ℝ) : ℂ)) ^ (a - 1) *
          (1 - (((1 - t : ℝ) : ℂ))) ^ (b - a - 1) := by
      intro t
      simp only [hGdef, Complex.real_smul, Complex.ofReal_exp]
      push_cast
      rw [show (1 : ℂ) - (1 - t) = t by ring, ← mul_assoc, ← Complex.exp_add]
      ring_nf
    have hI2 : (∫ t in (0 : ℝ)..1, exp ((x : ℂ) * ((1 - t : ℝ) : ℂ)) *
        (((1 - t : ℝ) : ℂ)) ^ (a - 1) * (1 - (((1 - t : ℝ) : ℂ))) ^ (b - a - 1)) =
        exp (x : ℂ) * ∫ t in (0 : ℝ)..1, Real.exp (-x * t) • G t := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun t _ => (hcongr t).symm
    rw [regularized_euler_integral ha hba, ← hsub, hI]
    simp only [Complex.ofReal_sub, Complex.ofReal_one] at hI2 ⊢
    rw [hI2]
    ring
  · ring_nf
  · funext n
    have hG : Gamma (b - a + n) / Gamma (b - a) = poch (b - a) n :=
      Gamma_add_nat_div_Gamma_eq (n := n) (b - a) hba'
    have hG0 : Gamma (b - a) ≠ 0 := Complex.Gamma_ne_zero hba'
    have hGa : Gamma a ≠ 0 := Complex.Gamma_ne_zero ha'
    simp only [Pi.smul_apply, smul_eq_mul, kummerCoeff]
    rw [show a - 1 = -(1 - a) by ring, ring_choose_neg_eq_poch,
      show (n : ℂ) + (b - a) = b - a + n by ring, ← hG]
    field_simp
    have h1 : ((-1 : ℂ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    rw [h1, mul_one]

/-- The leading Kummer expansion coefficient is `1/Γ(a)`. -/
theorem kummerCoeff_zero (a b : ℂ) : kummerCoeff a b 0 = (Gamma a)⁻¹ := by
  simp [kummerCoeff, poch_zero]

/-- The coefficient recurrence behind the regularized 13.3.4. -/
theorem kummerCoeff_sub_one (a b : ℂ) (m : ℕ) :
    kummerCoeff (a - 1) b m = kummerCoeff a b (m + 1) - kummerCoeff a (b + 1) (m + 1) := by
  simp only [kummerCoeff]
  rw [one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a - 1), sub_add_cancel,
    show 1 - (a - 1) = 2 - a by ring, show b - (a - 1) = b - a + 1 by ring,
    show b + 1 - a = b - a + 1 by ring, poch_succ_left (1 - a),
    show 1 - a + 1 = 2 - a by ring, poch_succ_left (b - a), poch_succ (b - a + 1),
    Nat.factorial_succ]
  have hf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have hn : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast m.succ_ne_zero
  push_cast
  field_simp
  ring

/-- The coefficient recurrence behind the regularized 13.3.2. -/
theorem kummerCoeff_b_sub_one (a b : ℂ) (m : ℕ) :
    kummerCoeff a (b - 1) (m + 1) =
      kummerCoeff a b (m + 1) + (b - 1) * kummerCoeff a b m -
        (b - a) * kummerCoeff a (b + 1) m := by
  simp only [kummerCoeff]
  rw [show b - 1 - a = b - a - 1 by ring, show b + 1 - a = b - a + 1 by ring,
    poch_succ (1 - a), poch_succ_left (b - a - 1), sub_add_cancel, poch_succ (b - a),
    Nat.factorial_succ]
  have key : (b - a) * poch (b - a + 1) m = poch (b - a) m * (b - a + m) := by
    rw [← poch_succ_left, poch_succ]
  have hf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have hn : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast m.succ_ne_zero
  push_cast
  field_simp
  linear_combination (poch (1 - a) m * (m + 1) / Gamma a) * key

/-- Comparison of the scales `eˣ x^c` at `+∞`. -/
theorem isBigO_exp_mul_cpow {c d : ℂ} (h : c.re ≤ d.re) :
    (fun x : ℝ => exp (x : ℂ) * (x : ℂ) ^ c) =O[atTop]
      fun x : ℝ => exp (x : ℂ) * (x : ℂ) ^ d := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : 0 < x := by linarith
  rw [one_mul, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx0,
    norm_cpow_eq_rpow_re_of_pos hx0]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx h) (norm_nonneg _)

/-- For real `x > 0`, `x · (eˣ x^c) = eˣ x^{c+1}`. -/
theorem ofReal_mul_exp_mul_cpow {x : ℝ} (hx : 0 < x) (c : ℂ) :
    (x : ℂ) * (exp (x : ℂ) * (x : ℂ) ^ c) = exp (x : ℂ) * (x : ℂ) ^ (c + 1) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [Complex.cpow_add _ _ hx0, Complex.cpow_one]
  ring

/-- `x • O(eˣ x^c) = O(eˣ x^{c+1})`. -/
theorem isBigO_ofReal_mul_of_isBigO_exp_mul_cpow {f : ℝ → ℂ} {c : ℂ}
    (h : f =O[atTop] fun x : ℝ => exp (x : ℂ) * (x : ℂ) ^ c) :
    (fun x : ℝ => (x : ℂ) * f x) =O[atTop] fun x : ℝ => exp (x : ℂ) * (x : ℂ) ^ (c + 1) :=
  ((isBigO_refl (fun x : ℝ => (x : ℂ)) atTop).mul h).congr' EventuallyEq.rfl
    (by filter_upwards [eventually_gt_atTop 0] with x hx using ofReal_mul_exp_mul_cpow hx c)

/-- The downward step in `a`, from the regularized 13.3.4. -/
theorem hasAsymptoticExpansion_regularizedConfluent_sub_one {a b : ℂ}
    (h1 : HasAsymptoticExpansion atTop
      (fun (n : ℕ) (x : ℝ) => exp (x : ℂ) * (x : ℂ) ^ (a - b - n))
      (kummerCoeff a b) (fun x : ℝ => regularizedHGFun {a} {b} (x : ℂ)))
    (h2 : HasAsymptoticExpansion atTop
      (fun (n : ℕ) (x : ℝ) => exp (x : ℂ) * (x : ℂ) ^ (a - (b + 1) - n))
      (kummerCoeff a (b + 1)) (fun x : ℝ => regularizedHGFun {a} {b + 1} (x : ℂ))) :
    HasAsymptoticExpansion atTop
      (fun (n : ℕ) (x : ℝ) => exp (x : ℂ) * (x : ℂ) ^ (a - 1 - b - n))
      (kummerCoeff (a - 1) b) (fun x : ℝ => regularizedHGFun {a - 1} {b} (x : ℂ)) := by
  intro N
  have hA := (h1 (N + 1)).trans (isBigO_exp_mul_cpow (c := a - b - ((N + 1 : ℕ) : ℂ))
    (d := a - 1 - b - N) (by simp; linarith))
  have hB := (isBigO_ofReal_mul_of_isBigO_exp_mul_cpow (h2 (N + 1))).trans (isBigO_exp_mul_cpow
    (c := a - (b + 1) - ((N + 1 : ℕ) : ℂ) + 1) (d := a - 1 - b - N) (by simp; linarith))
  refine (hA.sub hB).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hrel := regularizedConfluent_contiguous_shift_a a b x
  have hmul : ∀ n : ℕ, (x : ℂ) * (exp (x : ℂ) * (x : ℂ) ^ (a - (b + 1) - n)) =
      exp (x : ℂ) * (x : ℂ) ^ (a - b - n) := fun n => by
    rw [ofReal_mul_exp_mul_cpow hx]; ring_nf
  have hsh : ∀ n : ℕ, exp (x : ℂ) * (x : ℂ) ^ (a - b - ((n + 1 : ℕ) : ℂ)) =
      exp (x : ℂ) * (x : ℂ) ^ (a - 1 - b - n) := fun n => by push_cast; ring_nf
  have hsum : ∑ n ∈ Finset.range N, exp (x : ℂ) * (x : ℂ) ^ (a - 1 - b - n) *
      kummerCoeff (a - 1) b n =
      ∑ n ∈ Finset.range (N + 1), exp (x : ℂ) * (x : ℂ) ^ (a - b - n) * kummerCoeff a b n -
        (x : ℂ) * ∑ n ∈ Finset.range (N + 1),
          exp (x : ℂ) * (x : ℂ) ^ (a - (b + 1) - n) * kummerCoeff a (b + 1) n := by
    simp only [Finset.mul_sum, ← mul_assoc, hmul]
    rw [← Finset.sum_sub_distrib, Finset.sum_range_succ']
    simp only [kummerCoeff_zero, sub_self, add_zero, Nat.cast_zero, sub_zero, ← mul_sub, ← hsh,
      kummerCoeff_sub_one]
  simp only [smul_eq_mul] at hsum ⊢
  rw [hsum]
  linear_combination hrel

/-- The downward step in `b`, from the regularized 13.3.2. -/
theorem hasAsymptoticExpansion_regularizedConfluent_b_sub_one {a b : ℂ}
    (h1 : HasAsymptoticExpansion atTop
      (fun (n : ℕ) (x : ℝ) => exp (x : ℂ) * (x : ℂ) ^ (a - b - n))
      (kummerCoeff a b) (fun x : ℝ => regularizedHGFun {a} {b} (x : ℂ)))
    (h2 : HasAsymptoticExpansion atTop
      (fun (n : ℕ) (x : ℝ) => exp (x : ℂ) * (x : ℂ) ^ (a - (b + 1) - n))
      (kummerCoeff a (b + 1)) (fun x : ℝ => regularizedHGFun {a} {b + 1} (x : ℂ))) :
    HasAsymptoticExpansion atTop
      (fun (n : ℕ) (x : ℝ) => exp (x : ℂ) * (x : ℂ) ^ (a - (b - 1) - n))
      (kummerCoeff a (b - 1)) (fun x : ℝ => regularizedHGFun {a} {b - 1} (x : ℂ)) := by
  intro N
  have hNre : ((N : ℂ) - 1).re ≤ ((N - 1 : ℕ) : ℂ).re := by
    simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re]
    have : (N : ℝ) ≤ ((N - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : N ≤ N - 1 + 1)
    linarith
  have hA := (isBigO_ofReal_mul_of_isBigO_exp_mul_cpow (h1 N)).trans
    (isBigO_exp_mul_cpow (c := a - b - N + 1) (d := a - (b - 1) - N) (by simp; linarith))
  have hB := ((h1 (N - 1)).trans (isBigO_exp_mul_cpow (c := a - b - ((N - 1 : ℕ) : ℂ))
    (d := a - (b - 1) - N) (by simp at hNre ⊢; linarith))).const_mul_left (b - 1)
  have hC := ((isBigO_ofReal_mul_of_isBigO_exp_mul_cpow (h2 (N - 1))).trans
    (isBigO_exp_mul_cpow (c := a - (b + 1) - ((N - 1 : ℕ) : ℂ) + 1) (d := a - (b - 1) - N)
      (by simp at hNre ⊢; linarith))).const_mul_left (b - a)
  refine ((hA.add hB).sub hC).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hrel := regularizedConfluent_contiguous_b a b x
  have f1 : ∀ n : ℕ, (x : ℂ) * (exp (x : ℂ) * (x : ℂ) ^ (a - b - n)) =
      exp (x : ℂ) * (x : ℂ) ^ (a - (b - 1) - n) := fun n => by
    rw [ofReal_mul_exp_mul_cpow hx]; ring_nf
  have f2 : ∀ n : ℕ, exp (x : ℂ) * (x : ℂ) ^ (a - b - n) =
      exp (x : ℂ) * (x : ℂ) ^ (a - (b - 1) - ((n + 1 : ℕ) : ℂ)) := fun n => by
    push_cast; ring_nf
  have f3 : ∀ n : ℕ, (x : ℂ) * (exp (x : ℂ) * (x : ℂ) ^ (a - (b + 1) - n)) =
      exp (x : ℂ) * (x : ℂ) ^ (a - (b - 1) - ((n + 1 : ℕ) : ℂ)) := fun n => by
    rw [ofReal_mul_exp_mul_cpow hx]; push_cast; ring_nf
  simp only [smul_eq_mul]
  rcases N with _ | M
  · simp only [Finset.range_zero, Finset.sum_empty, sub_zero, zero_tsub]
    linear_combination -hrel
  · have hterm : ∀ m ∈ Finset.range M,
        exp (x : ℂ) * (x : ℂ) ^ (a - (b - 1) - ((m + 1 : ℕ) : ℂ)) *
          kummerCoeff a (b - 1) (m + 1) =
        (x : ℂ) * (exp (x : ℂ) * (x : ℂ) ^ (a - b - ((m + 1 : ℕ) : ℂ)) *
          kummerCoeff a b (m + 1)) +
        (b - 1) * (exp (x : ℂ) * (x : ℂ) ^ (a - b - m) * kummerCoeff a b m) -
        (b - a) * ((x : ℂ) * (exp (x : ℂ) * (x : ℂ) ^ (a - (b + 1) - m) *
          kummerCoeff a (b + 1) m)) := by
      intro m _
      have e1 := f1 (m + 1)
      have e2 := f2 m
      have e3 := f3 m
      rw [kummerCoeff_b_sub_one]
      linear_combination (-kummerCoeff a b (m + 1)) * e1 - (b - 1) * kummerCoeff a b m * e2 +
        (b - a) * kummerCoeff a (b + 1) m * e3
    have hsum : ∑ n ∈ Finset.range (M + 1), exp (x : ℂ) * (x : ℂ) ^ (a - (b - 1) - n) *
        kummerCoeff a (b - 1) n =
        (x : ℂ) * ∑ n ∈ Finset.range (M + 1), exp (x : ℂ) * (x : ℂ) ^ (a - b - n) *
          kummerCoeff a b n +
        (b - 1) * ∑ n ∈ Finset.range M, exp (x : ℂ) * (x : ℂ) ^ (a - b - n) *
          kummerCoeff a b n -
        (b - a) * ((x : ℂ) * ∑ n ∈ Finset.range M, exp (x : ℂ) * (x : ℂ) ^ (a - (b + 1) - n) *
          kummerCoeff a (b + 1) n) := by
      rw [Finset.sum_range_succ', Finset.sum_congr rfl hterm, Finset.mul_sum,
        Finset.sum_range_succ' (fun n => (x : ℂ) * (exp (x : ℂ) * (x : ℂ) ^ (a - b - n) *
          kummerCoeff a b n)), Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        Finset.sum_sub_distrib, Finset.sum_add_distrib]
      have e0 := f1 0
      simp only [kummerCoeff_zero, Nat.cast_zero] at e0 ⊢
      linear_combination (-(Gamma a)⁻¹) * e0
    simp only [Nat.add_sub_cancel]
    rw [hsum]
    linear_combination -hrel

/-- **Expansion of the regularized Kummer function** (DLMF 13.7.1 on the positive axis,
Temme §7.1): `𝐌(a,b,x) ~ eˣ x^{a-b} / Γ(a) · ∑ (1-a)_s (b-a)_s / s! · x^{-s}` as `x → +∞`,
for all complex `a, b`. -/
theorem hasAsymptoticExpansion_regularizedConfluent (a b : ℂ) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => exp (x : ℂ) * (x : ℂ) ^ (a - b - n))
      (kummerCoeff a b) (fun x : ℝ => regularizedHGFun {a} {b} (x : ℂ)) := by
  -- first all `b` with `re (b - a)` large, by lowering `a`
  have hQ : ∀ m : ℕ, ∀ a b : ℂ, 0 < (a + m).re → (m : ℝ) < (b - a).re →
      HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => exp (x : ℂ) * (x : ℂ) ^ (a - b - n))
        (kummerCoeff a b) (fun x : ℝ => regularizedHGFun {a} {b} (x : ℂ)) := by
    intro m
    induction m with
    | zero =>
      intro a b ha hba
      exact hasAsymptoticExpansion_regularizedConfluent_of_re_pos (by simpa using ha)
        (by simpa using hba)
    | succ m ih =>
      intro a b ha hba
      have ha1 : 0 < (a + 1 + m).re := by simp at ha ⊢; linarith
      have hb1 : (m : ℝ) < (b - (a + 1)).re := by simp at hba ⊢; linarith
      have hb2 : (m : ℝ) < (b + 1 - (a + 1)).re := by simp at hba ⊢; linarith
      have h1 := ih (a + 1) b ha1 hb1
      have h2 := ih (a + 1) (b + 1) ha1 hb2
      have h := hasAsymptoticExpansion_regularizedConfluent_sub_one h1 h2
      simp only [add_sub_cancel_right] at h
      refine h.congr_scale fun n => Eventually.of_forall fun x => ?_
      ring_nf
  obtain ⟨m, hm⟩ := exists_nat_gt (-a.re)
  -- then lower `b`
  have hR : ∀ k : ℕ, ∀ b : ℂ, (m : ℝ) < (b + k - a).re →
      HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) => exp (x : ℂ) * (x : ℂ) ^ (a - b - n))
        (kummerCoeff a b) (fun x : ℝ => regularizedHGFun {a} {b} (x : ℂ)) := by
    intro k
    induction k with
    | zero =>
      intro b hb
      exact hQ m a b (by simp; linarith) (by simpa using hb)
    | succ k ih =>
      intro b hb
      have h1 := ih (b + 1) (by simp at hb ⊢; linarith)
      have h2 := ih (b + 1 + 1) (by simp at hb ⊢; linarith)
      have h := hasAsymptoticExpansion_regularizedConfluent_b_sub_one h1 h2
      simp only [add_sub_cancel_right] at h
      exact h
  obtain ⟨k, hk⟩ := exists_nat_gt ((m : ℝ) - (b - a).re)
  exact hR k b (by simp only [Complex.sub_re] at hk; simp; linarith)

/-- The partial sums of the Kummer expansion in the form of DLMF 13.7.1. -/
theorem regularizedConfluent_sum_eq {x : ℝ} (hx : 0 < x) (a b : ℂ) (n : ℕ) :
    ∑ s ∈ Finset.range n, (exp (x : ℂ) * (x : ℂ) ^ (a - b - s)) • kummerCoeff a b s =
      exp (x : ℂ) * (x : ℂ) ^ (a - b) / Gamma a * ∑ s ∈ Finset.range n,
        poch (1 - a) s * poch (b - a) s / s.factorial * (x : ℂ) ^ (-(s : ℂ)) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_eq_mul, kummerCoeff, show a - b - s = (a - b) + -(s : ℂ) by ring,
    Complex.cpow_add _ _ hx0]
  ring

/-- The remainder of the binomial series `(1+t)^{-r} = ∑ (-1)^k (r)_k / k! t^k` after
`n` terms. -/
def binomRem (r : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (1 + t) ^ (-r) - ∑ k ∈ Finset.range n, (-1) ^ k * (ascPochhammer ℝ k).eval r / k ! * t ^ k

/-- The Pochhammer recursion `(r)_{n+1} = r (r+1)_n` over the reals. -/
theorem ascPochhammer_eval_succ_left' (r : ℝ) (n : ℕ) :
    (ascPochhammer ℝ (n + 1)).eval r = r * (ascPochhammer ℝ n).eval (r + 1) := by
  rw [ascPochhammer_succ_left]
  simp [Polynomial.eval_comp]

/-- The binomial remainder satisfies `d/dt R_{n+1}(r; t) = -r R_n(r+1; t)` for `t > -1`. -/
theorem hasDerivAt_binomRem (r : ℝ) (n : ℕ) {t : ℝ} (ht : -1 < t) :
    HasDerivAt (binomRem r (n + 1)) (-r * binomRem (r + 1) n t) t := by
  have h1 : HasDerivAt (fun t : ℝ => (1 + t) ^ (-r)) (-r * (1 + t) ^ (-(r + 1))) t := by
    have := ((hasDerivAt_id t).const_add 1).rpow_const (p := -r) (Or.inl (by
      simp only [id]; linarith))
    simp only [id_eq] at this
    convert this using 1
    ring_nf
  have h2 : HasDerivAt (fun t : ℝ => ∑ j ∈ Finset.range n,
      (-1) ^ (j + 1) * (ascPochhammer ℝ (j + 1)).eval r / (j + 1)! * t ^ (j + 1))
      (∑ j ∈ Finset.range n, (-1) ^ (j + 1) * (ascPochhammer ℝ (j + 1)).eval r / (j + 1)! *
        ((j + 1 : ℕ) * t ^ j)) t :=
    HasDerivAt.fun_sum fun j _ => (hasDerivAt_pow (j + 1) t).const_mul _
  have h := h1.sub (h2.add_const 1)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  · simp only [binomRem, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ascPochhammer_eval_succ_left', Nat.factorial_succ]
    have hf : (j ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
    have hj : (j : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · simp only [binomRem, Pi.sub_apply]
    rw [Finset.sum_range_succ']
    simp

/-- The binomial remainder is bounded by the first omitted term, for `r ≥ 0` and `t ≥ 0`. -/
theorem abs_binomRem_le {r : ℝ} (hr : 0 ≤ r) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |binomRem r n t| ≤ (ascPochhammer ℝ n).eval r / n ! * t ^ n := by
  induction n generalizing r t with
  | zero =>
    simp only [binomRem, Finset.range_zero, Finset.sum_empty, sub_zero, ascPochhammer_zero,
      Polynomial.eval_one, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, mul_one]
    rw [abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  | succ n ih =>
    have hB : ∀ s : ℝ, HasDerivAt (fun s => (ascPochhammer ℝ (n + 1)).eval r / (n + 1)! *
        s ^ (n + 1)) ((ascPochhammer ℝ (n + 1)).eval r / (n + 1)! * ((n + 1 : ℕ) * s ^ n)) s :=
      fun s => (hasDerivAt_pow (n + 1) s).const_mul _
    have hcont : ContinuousOn (binomRem r (n + 1)) (Set.Icc 0 t) := fun s hs =>
      (hasDerivAt_binomRem r n (by linarith [hs.1])).continuousAt.continuousWithinAt
    have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := t) hcont
      (fun s hs => (hasDerivAt_binomRem r n (by linarith [hs.1])).hasDerivWithinAt)
      (B := fun s => (ascPochhammer ℝ (n + 1)).eval r / (n + 1)! * s ^ (n + 1)) (by
        simp [binomRem, Finset.sum_range_succ']) hB (fun s hs => ?_) (Set.right_mem_Icc.mpr ht)
    · simpa [Real.norm_eq_abs] using h
    · rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hr]
      have := ih (r := r + 1) (by linarith) (t := s) hs.1
      rw [ascPochhammer_eval_succ_left', Nat.factorial_succ]
      have hf : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      calc r * |binomRem (r + 1) n s|
          ≤ r * ((ascPochhammer ℝ n).eval (r + 1) / n ! * s ^ n) :=
            mul_le_mul_of_nonneg_left this hr
        _ = _ := by push_cast; field_simp

/-- The real Pochhammer symbol `(r)_k`, cast to `ℂ`, is the complex Pochhammer symbol at `r`. -/
theorem ofReal_ascPochhammer_eval (r : ℝ) (k : ℕ) :
    (((ascPochhammer ℝ k).eval r : ℝ) : ℂ) = (ascPochhammer ℂ k).eval (r : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih => rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]; push_cast; rw [ih]

@[dlmf 13.7.E1]
theorem regularizedHGFun_poincare_real (a b : ℂ) (n : ℕ) (_ha : ∀ k : ℕ, a ≠ -k) :
    Asymptotics.IsBigO atTop
      (fun x : ℝ => regularizedHGFun {a} {b} x -
        exp x * (x : ℂ) ^ (a - b) / Gamma a *
          ∑ s ∈ Finset.range n, poch (1 - a) s * poch (b - a) s / s.factorial *
            (x : ℂ) ^ (-(s : ℂ)))
      (fun x : ℝ => exp x * (x : ℂ) ^ (a - b - n)) := by
  refine (hasAsymptoticExpansion_regularizedConfluent a b n).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [regularizedConfluent_sum_eq hx]

@[dlmf 13.7.E3]
theorem kummerU_poincare (a b : ℂ) (n : ℕ) :
    Asymptotics.IsBigO atTop
      (fun x : ℝ => kummerU a b x -
        (x : ℂ) ^ (-a) * ∑ s ∈ Finset.range n,
          poch a s * poch (a - b + 1) s / s.factorial * (-(x : ℂ)) ^ (-(s : ℂ)))
      (fun x : ℝ => (x : ℂ) ^ (-a - n)) := by
  refine (hasAsymptoticExpansion_kummerU a b n).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [kummerU_sum_eq hx]
  · exact Eventually.of_forall fun x => by ring_nf

/-- For positive real `a` and `b ≤ a + 1`, the positive-ray Tricomi
truncation error is bounded by the magnitude of the first omitted term. -/
@[dlmf 13.7.E4]
theorem kummerU_poincare_finite {a b x : ℝ} (ha : 0 < a) (hb : b ≤ a + 1)
    (hx : 0 < x) (n : ℕ) :
    ‖kummerU a b x -
      (x : ℂ) ^ (-(a : ℂ)) * ∑ s ∈ Finset.range n,
        poch (a : ℂ) s * poch ((a : ℂ) - b + 1) s / s.factorial *
          (-(x : ℂ)) ^ (-(s : ℂ))‖ ≤
      ‖(x : ℂ) ^ (-(a : ℂ) - n) *
        poch (a : ℂ) n * poch ((a : ℂ) - b + 1) n / n.factorial‖ := by
  set r : ℝ := a - b + 1 with hr
  have hr0 : 0 ≤ r := by linarith
  have haC : 0 < (a : ℂ).re := by simpa using ha
  have ha' : ∀ k : ℕ, (a : ℂ) ≠ -k := fun k hk => by
    have := congrArg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hGa : Gamma (a : ℂ) ≠ 0 := Complex.Gamma_ne_zero ha'
  have hpr : ∀ k : ℕ, poch ((a : ℂ) - b + 1) k = (((ascPochhammer ℝ k).eval r : ℝ) : ℂ) := by
    intro k
    rw [ofReal_ascPochhammer_eval, hr]
    push_cast
    rfl
  have hpa : ∀ k : ℕ, poch (a : ℂ) k = Gamma ((k : ℂ) + a) / Gamma a := fun k => by
    rw [add_comm]; exact (Gamma_add_nat_div_Gamma_eq (n := k) (a : ℂ) ha').symm
  -- the coefficients of the binomial series of `(1+t)^{-r}`
  set c : ℕ → ℂ := fun k => (((-1) ^ k * (ascPochhammer ℝ k).eval r / k ! : ℝ) : ℂ) with hc
  set F : ℝ → ℂ := fun t => (t : ℂ) ^ ((a : ℂ) - 1) * (1 + (t : ℂ)) ^ ((b : ℂ) - a - 1) with hF
  set P : ℝ → ℂ := fun t => ∑ k ∈ Finset.range n, (t : ℂ) ^ ((k : ℂ) + a - 1) • c k with hP
  have hsk : ∀ k : ℕ, 0 < ((k : ℂ) + a).re := fun k => by simp; positivity
  have hFint : IntegrableOn (fun t => Real.exp (-x * t) • F t) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun (kummerU_laplace_integrable (b := (b : ℂ)) haC
      (z := (x : ℂ)) (by simpa using hx)) (fun t _ => ?_) measurableSet_Ioi
    simp only [hF, Complex.real_smul, Complex.ofReal_exp]
    push_cast
    ring
  have hPk : ∀ k : ℕ, IntegrableOn (fun t : ℝ => Real.exp (-x * t) • ((t : ℂ) ^ ((k : ℂ) + a - 1)
      • c k)) (Set.Ioi 0) := fun k =>
    IntegrableOn.congr_fun ((integrableOn_exp_neg_mul_smul_cpow_sub_one (hsk k) hx).smul_const
      (c k)) (fun t _ => by rw [smul_assoc]) measurableSet_Ioi
  have hPint : IntegrableOn (fun t => Real.exp (-x * t) • P t) (Set.Ioi 0) :=
    IntegrableOn.congr_fun (integrable_finsetSum (Finset.range n) fun k _ => hPk k)
      (fun t _ => by simp only [hP, Finset.smul_sum]) measurableSet_Ioi
  -- the three integral identities
  have hU : kummerU a b x = 1 / Gamma a * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-x * t) • F t := by
    rw [kummerU_laplace haC (by simpa using hx)]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hF, Complex.real_smul, Complex.ofReal_exp]
    push_cast
    ring
  have hS : (x : ℂ) ^ (-(a : ℂ)) * ∑ s ∈ Finset.range n,
      poch (a : ℂ) s * poch ((a : ℂ) - b + 1) s / s.factorial * (-(x : ℂ)) ^ (-(s : ℂ)) =
      1 / Gamma a * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-x * t) • P t := by
    rw [← kummerU_sum_eq hx]
    simp only [hP, Finset.smul_sum]
    rw [integral_finsetSum _ fun k _ => hPk k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp_rw [← smul_assoc]
    rw [integral_smul_const, integral_exp_neg_mul_smul_cpow_sub_one (hsk k) hx, tricomiCoeff,
      hpa, hpr, hc]
    simp only [smul_eq_mul]
    push_cast
    field_simp
  have hdiff : ∀ t ∈ Set.Ioi (0 : ℝ), Real.exp (-x * t) • F t - Real.exp (-x * t) • P t =
      Real.exp (-x * t) • ((t : ℂ) ^ ((a : ℂ) - 1) * (binomRem r n t : ℂ)) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    rw [← smul_sub]
    congr 1
    have h1 : (1 + (t : ℂ)) ^ ((b : ℂ) - a - 1) = (((1 + t) ^ (-r) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by linarith [show (0 : ℝ) < t from ht]), hr]
      push_cast
      ring_nf
    simp only [hF, hP, binomRem, h1, hc, smul_eq_mul]
    push_cast
    rw [mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (k : ℂ) + a - 1 = (k : ℂ) + (a - 1) by ring, Complex.cpow_add _ _ ht0,
      Complex.cpow_natCast]
    ring
  rw [hU, hS, ← mul_sub, ← integral_sub hFint hPint, setIntegral_congr_fun measurableSet_Ioi hdiff]
  -- the bound
  have hGpos : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hGa' : Gamma (a : ℂ) = (Real.Gamma a : ℂ) := Complex.Gamma_ofReal a
  set K : ℝ := (ascPochhammer ℝ n).eval r / n ! with hK
  have hK0 : 0 ≤ K := div_nonneg (DLMF.Hypergeometric.poch_eval_nonneg hr0 n) (by positivity)
  have hmaj : IntegrableOn (fun t : ℝ => K * (Real.exp (-x * t) * t ^ ((a + n) - 1)))
      (Set.Ioi 0) := (integrableOn_exp_neg_mul_mul_rpow_sub_one (by positivity) hx).const_mul K
  have hInt : ‖∫ t in Set.Ioi (0 : ℝ), Real.exp (-x * t) •
      ((t : ℂ) ^ ((a : ℂ) - 1) * (binomRem r n t : ℂ))‖ ≤
      K * (Real.Gamma (a + n) * x ^ (-(a + n))) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_exp_neg_mul_mul_rpow_sub_one (by positivity) hx, ← integral_const_mul]
    refine setIntegral_mono_on ?_ hmaj measurableSet_Ioi fun t ht => ?_
    · exact (IntegrableOn.congr_fun (hFint.sub hPint) hdiff measurableSet_Ioi).norm
    · have ht : (0 : ℝ) < t := ht
      rw [norm_smul, norm_mul, Real.norm_eq_abs, Real.abs_exp,
        norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real, Real.norm_eq_abs]
      have hb := abs_binomRem_le hr0 n ht.le
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
      rw [show (a + n) - 1 = (a - 1) + n by ring, Real.rpow_add ht, Real.rpow_natCast]
      have he := Real.exp_pos (-x * t)
      have hp := Real.rpow_pos_of_pos ht (a - 1)
      calc Real.exp (-x * t) * (t ^ (a - 1) * |binomRem r n t|)
          ≤ Real.exp (-x * t) * (t ^ (a - 1) * (K * t ^ n)) := by gcongr
        _ = _ := by ring
  rw [norm_mul]
  calc ‖1 / Gamma (a : ℂ)‖ * ‖∫ t in Set.Ioi (0 : ℝ), Real.exp (-x * t) •
        ((t : ℂ) ^ ((a : ℂ) - 1) * (binomRem r n t : ℂ))‖
      ≤ (Real.Gamma a)⁻¹ * (K * (Real.Gamma (a + n) * x ^ (-(a + n)))) := by
        rw [hGa', one_div, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hGpos]
        exact mul_le_mul_of_nonneg_left hInt (by positivity)
    _ = _ := by
        rw [hpr, hpa, hGa', show ((n : ℂ) + a) = ((n + a : ℝ) : ℂ) by push_cast; ring,
          Complex.Gamma_ofReal, show -(a : ℂ) - n = ((-(a + n) : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_cpow hx.le]
        rw [show ((x ^ (-(a + n)) : ℝ) : ℂ) * (((Real.Gamma (n + a)) : ℂ) / (Real.Gamma a : ℂ)) *
          (((ascPochhammer ℝ n).eval r : ℝ) : ℂ) / (n.factorial : ℂ) =
          ((x ^ (-(a + n)) * (Real.Gamma (n + a) / Real.Gamma a) *
            (ascPochhammer ℝ n).eval r / n.factorial : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by
            have := DLMF.Hypergeometric.poch_eval_nonneg hr0 n
            have := Real.Gamma_pos_of_pos (show 0 < (n : ℝ) + a by positivity)
            positivity), hK, add_comm (n : ℝ) a]
        field_simp

/-- A positive-ray remainder function with the stated order of decay.
This gives an actual asymptotic bound, not just an arbitrary additive error.
It does not yet assert the exponentially improved expansion of DLMF 13.7.10. -/
@[dlmf 13.7.E4]
theorem kummerU_poincare_remainder (a b : ℂ) (n : ℕ) :
    ∃ R : ℝ → ℂ,
      (∀ x : ℝ, 0 < x → kummerU a b x =
        (x : ℂ) ^ (-a) * ∑ s ∈ Finset.range n,
          poch a s * poch (a - b + 1) s / s.factorial * (-(x : ℂ)) ^ (-(s : ℂ)) + R x) ∧
      Asymptotics.IsBigO atTop R (fun x : ℝ => (x : ℂ) ^ (-a - n)) :=
  ⟨_, fun _ _ => (add_sub_cancel _ _).symm, kummerU_poincare a b n⟩

@[dlmf 13.8.E1]
theorem kummerM_large_b (a z : ℂ) (n : ℕ) :
    Asymptotics.IsBigO atTop
      (fun b : ℝ => kummerM a b z -
        ∑ s ∈ Finset.range n, poch a s / (poch (b : ℂ) s * s.factorial) * z ^ s)
      (fun b : ℝ => ((b : ℂ)⁻¹) ^ n) := by
  set r := ‖z‖
  set α := ‖a‖
  set A : ℝ := α + n
  let Q : ℕ → ℝ := fun s => (ascPochhammer ℝ s).eval ((n : ℝ) + 1)
  let tt : ℕ → ℝ := fun s => (ascPochhammer ℝ s).eval A * r ^ s / (Q s * s.factorial)
  set K0 : ℝ := (ascPochhammer ℝ n).eval α * r ^ n / n.factorial
  have hQpos (s : ℕ) : 0 < Q s := ascPochhammer_pos s _ (by positivity)
  -- the comparison series is Kummer's series `M(A, n + 1, r)`
  have htt : Summable tt := by
    have hc : ∀ k : ℕ, ((((n : ℝ) + 1 : ℝ)) : ℂ) ≠ -k :=
      not_neg_nat_of_re_pos (by simp; positivity)
    have hs := (hasFPowerSeriesOnBall_kummerM (a := ((A : ℝ) : ℂ)) hc).hasSum_mul_pow
      (z := ((r : ℝ) : ℂ)) (by simp)
    have ht : ∀ s : ℕ, kummerMCoeff ((A : ℝ) : ℂ) (((n : ℝ) + 1 : ℝ) : ℂ) s *
        ((r : ℝ) : ℂ) ^ s = (tt s : ℂ) := by
      intro s
      simp only [tt, Q, kummerMCoeff]
      rw [poch_ofReal, poch_ofReal]
      push_cast
      ring
    simp only [ht] at hs
    exact (by simpa using Complex.hasSum_re hs : HasSum tt _).summable
  have hfac (s : ℕ) : ((s + n).factorial : ℝ) = n.factorial * Q s := by
    have h := Nat.factorial_mul_ascFactorial n s
    have hQ : Q s = ((n + 1).ascFactorial s : ℝ) := by
      simp only [Q]
      rw [← ascPochhammer_nat_eq_natCast_ascFactorial ℝ (n + 1) s]
      push_cast
      rfl
    rw [hQ, add_comm s n, ← h]
    push_cast
    rfl
  have hsplit (x : ℝ) (s : ℕ) : (ascPochhammer ℝ (s + n)).eval x =
      (ascPochhammer ℝ n).eval x * (ascPochhammer ℝ s).eval (x + n) := by
    rw [add_comm s n, ← ascPochhammer_mul, Polynomial.eval_mul, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_natCast]
  refine Asymptotics.IsBigO.of_bound (K0 * ∑' s, tt s) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
  have hb0 : 0 < b := by linarith
  have hbc : ∀ k : ℕ, ((b : ℝ) : ℂ) ≠ -k := not_neg_nat_of_re_pos (by simpa using hb0)
  have hS := (hasFPowerSeriesOnBall_kummerM (a := a) hbc).hasSum_mul_pow (z := z) (by simp)
  have hT := (hasSum_nat_add_iff' n).mpr hS
  have hpow : ‖((b : ℂ)⁻¹) ^ n‖ = (b ^ n)⁻¹ := by
    rw [norm_pow, norm_inv, norm_real, Real.norm_of_nonneg hb0.le, inv_pow]
  have hbn : 0 < b ^ n := pow_pos hb0 n
  have hterm (s : ℕ) : ‖kummerMCoeff a b (s + n) * z ^ (s + n)‖ ≤
      (b ^ n)⁻¹ * (K0 * tt s) := by
    have hnum : ‖poch a (s + n)‖ ≤
        (ascPochhammer ℝ n).eval α * (ascPochhammer ℝ s).eval A := by
      rw [← hsplit]; exact norm_poch_le a (s + n)
    have hden : b ^ n * Q s ≤ ‖poch ((b : ℝ) : ℂ) (s + n)‖ := by
      rw [poch_ofReal, norm_real, hsplit,
        Real.norm_of_nonneg (mul_nonneg (poch_eval_nonneg hb0.le n)
          (poch_eval_nonneg (by positivity) s))]
      have h1 : ∀ m : ℕ, b ^ m ≤ (ascPochhammer ℝ m).eval b := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [pow_succ, ascPochhammer_succ_eval]
          exact mul_le_mul ih (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
            hb0.le (poch_eval_nonneg hb0.le m)
      have h2 : Q s ≤ (ascPochhammer ℝ s).eval (b + n) :=
        poch_eval_mono (by positivity) (by linarith) s
      exact mul_le_mul (h1 n) h2 (hQpos s).le (poch_eval_nonneg hb0.le n)
    have hQF : (s.factorial : ℝ) ≤ Q s := by
      rw [← ascPochhammer_eval_one]
      exact poch_eval_mono zero_le_one (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) s
    have hF : (0 : ℝ) < s.factorial := by positivity
    have hN : (0 : ℝ) < n.factorial := by positivity
    have hP1 : 0 ≤ (ascPochhammer ℝ n).eval α := poch_eval_nonneg (norm_nonneg a) n
    have hP2 : 0 ≤ (ascPochhammer ℝ s).eval A := poch_eval_nonneg (by positivity) s
    rw [kummerMCoeff, norm_mul, norm_div, norm_mul, norm_pow, Complex.norm_natCast, hfac]
    calc ‖poch a (s + n)‖ / (‖poch ((b : ℝ) : ℂ) (s + n)‖ * (n.factorial * Q s)) * r ^ (s + n)
        ≤ (ascPochhammer ℝ n).eval α * (ascPochhammer ℝ s).eval A /
            (b ^ n * Q s * (n.factorial * s.factorial)) * r ^ (s + n) := by
          have hden' : b ^ n * Q s * (n.factorial * s.factorial) ≤
              ‖poch ((b : ℝ) : ℂ) (s + n)‖ * (n.factorial * Q s) :=
            mul_le_mul hden (mul_le_mul_of_nonneg_left hQF hN.le) (by positivity)
              (norm_nonneg _)
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact div_le_div₀ (mul_nonneg hP1 hP2) hnum
            (mul_pos (mul_pos hbn (hQpos s)) (mul_pos hN hF)) hden'
      _ = (b ^ n)⁻¹ * (K0 * tt s) := by
          simp only [K0, tt, pow_add]
          field_simp
  have hle := tsum_of_norm_bounded ((htt.hasSum.mul_left K0).mul_left (b ^ n)⁻¹) hterm
  rw [hT.tsum_eq] at hle
  rw [hpow, mul_comm]
  exact hle

/-- Analytic normalization of the generating function in 13.8.3.
The former product of singular powers assigned zero at the removable point. -/
@[dlmf 13.8.E3]
def largeBGenerating (a z t : ℂ) : ℂ :=
  DLMF.Hypergeometric.expSubOneDiv t ^ (a - 1) * exp (t + z * (1 - exp (-t)))

/-- The `s`-th Taylor coefficient at `0` of `largeBGenerating a z`. -/
@[dlmf 13.8.E3]
def largeBCoeff (a z : ℂ) (s : ℕ) : ℂ :=
  iteratedDeriv s (largeBGenerating a z) 0 / s.factorial

/-- The zeroth large-`b` coefficient is `1`. -/
@[simp]
theorem largeBCoeff_zero (a z : ℂ) : largeBCoeff a z 0 = 1 := by
  simp [largeBCoeff, largeBGenerating, DLMF.Hypergeometric.expSubOneDiv]

/-! ### The large-`b` expansion 13.8.2

For `re a > 0`, Euler's integral in the variable `s = 1 - e^{-t}` is the Laplace transform
`∫₀^∞ e^{-bt} t^{a-1} q(t) dt` of the generating function 13.8.3, and Watson's lemma gives
`b^a Γ(b-a)/Γ(b) M(a,b,z) ~ ∑ (a)_s q_s(z) b^{-s}` (`hcub_largeB_base`). For every `a`,
13.8.1 multiplied by the Gamma-ratio expansion 5.11.13 gives an expansion of the same function
with explicit coefficients `hcub_largeBMix` (`hcub_largeB_mix`). Uniqueness of asymptotic
expansions identifies the two coefficient sequences for `re a > 0`; both are entire in `a`
(the `q_s` through Cauchy's integral formula), so the identity theorem gives the coefficient
identity for all `a` (`hcub_largeBMix_eq`), and with it 13.8.2 without restriction on `a`.
-/

section LargeBPoincare

open Set

/-- The large-`b` generating function is analytic at `t = 0`. -/
theorem hcub_analyticAt_largeBGenerating (a z : ℂ) : AnalyticAt ℂ (largeBGenerating a z) 0 := by
  have h1 : expSubOneDiv 0 ∈ slitPlane := by simp [expSubOneDiv]
  have h2 : AnalyticAt ℂ (fun t : ℂ => exp (t + z * (1 - exp (-t)))) 0 :=
    (analyticAt_id.add (analyticAt_const.mul (analyticAt_const.sub analyticAt_id.neg.cexp))).cexp
  exact ((analyticAt_expSubOneDiv 0).cpow analyticAt_const h1).mul h2

/-- The Taylor remainder of the large-`b` generating function after `N` terms is `O(|t|^N)` as `t →
0`. -/
theorem hcub_largeB_taylor (a z : ℂ) (N : ℕ) :
    (fun t => largeBGenerating a z t - ∑ n ∈ Finset.range N, largeBCoeff a z n * t ^ n)
      =O[𝓝 0] fun t => ‖t‖ ^ N := by
  have h := (hcub_analyticAt_largeBGenerating a z).hasFPowerSeriesAt.isBigO_sub_partialSum_pow N
  refine h.congr' (Eventually.of_forall fun s => ?_) EventuallyEq.rfl
  simp only [zero_add, FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, largeBCoeff]

/-- The substitution `s = 1 - e^{-t}` transforms the Euler integrand of `M(a,b,z)` into `e^{-bt}
t^{a-1} G(a,z,t)`, with `G` the large-`b` generating function. -/
theorem hcub_subst (a z : ℂ) (b : ℝ) {t : ℝ} (ht : 0 < t) :
    |Real.exp (-t)| • (((1 - Real.exp (-t) : ℝ) : ℂ) ^ (a - 1) *
      (1 - ((1 - Real.exp (-t) : ℝ) : ℂ)) ^ ((b : ℂ) - a - 1) *
        exp (z * ((1 - Real.exp (-t) : ℝ) : ℂ))) =
    Real.exp (-b * t) • ((t : ℂ) ^ (a - 1) * largeBGenerating a z t) := by
  set E : ℝ := (Real.exp t - 1) / t with hE
  have hE0 : 0 < E := div_pos (by linarith [Real.add_one_lt_exp ht.ne']) ht
  have hEc : expSubOneDiv (t : ℂ) = (E : ℂ) := by
    rw [expSubOneDiv, ite_eq_right_iff.mpr (fun h => absurd h (by exact_mod_cast ht.ne')), hE]
    push_cast; rfl
  have hs : (1 - Real.exp (-t) : ℝ) = Real.exp (-t) * (t * E) := by
    rw [hE, Real.exp_neg]; field_simp
  have hc : ((1 - Real.exp (-t) : ℝ) : ℂ) ^ (a - 1) =
      exp (-(t : ℂ) * (a - 1)) * ((t : ℂ) ^ (a - 1) * (E : ℂ) ^ (a - 1)) := by
    rw [hs, Complex.ofReal_mul, mul_cpow_ofReal_nonneg (Real.exp_pos _).le
      (by positivity), Complex.ofReal_mul, mul_cpow_ofReal_nonneg ht.le hE0.le, hcub_ofReal_cpow_exp]
    push_cast; ring_nf
  rw [hc, show (1 : ℂ) - ((1 - Real.exp (-t) : ℝ) : ℂ) = ((Real.exp (-t) : ℝ) : ℂ) by push_cast; ring,
    hcub_ofReal_cpow_exp, abs_of_pos (Real.exp_pos _), Complex.real_smul,
    Complex.real_smul, largeBGenerating, hEc]
  push_cast
  have e1 : exp (-(t : ℂ)) * (exp (-(t : ℂ) * (a - 1)) * ((t : ℂ) ^ (a - 1) * (E : ℂ) ^ (a - 1)) *
      exp (-(t : ℂ) * ((b : ℂ) - a - 1)) * exp (z * (1 - exp (-(t : ℂ))))) =
      (t : ℂ) ^ (a - 1) * (E : ℂ) ^ (a - 1) *
        exp (-(t : ℂ) + -(t : ℂ) * (a - 1) + -(t : ℂ) * ((b : ℂ) - a - 1) +
          z * (1 - exp (-(t : ℂ)))) := by
    simp only [Complex.exp_add]; ring
  have e2 : exp (-(b : ℂ) * t) * ((t : ℂ) ^ (a - 1) * ((E : ℂ) ^ (a - 1) *
      exp (t + z * (1 - exp (-(t : ℂ)))))) =
      (t : ℂ) ^ (a - 1) * (E : ℂ) ^ (a - 1) *
        exp (-(b : ℂ) * t + (t + z * (1 - exp (-(t : ℂ))))) := by
    simp only [Complex.exp_add]; ring
  rw [e1, e2]
  congr 2
  ring

/-- The Euler integral `∫₀¹ s^{a-1}(1-s)^{b-a-1} e^{zs} ds` equals the Laplace integral `∫₀^∞
e^{-bt} t^{a-1} G(a,z,t) dt`. -/
theorem hcub_euler_eq_laplace (a z : ℂ) (b : ℝ) :
    ∫ s : ℝ in (0 : ℝ)..1, (s : ℂ) ^ (a - 1) * (1 - (s : ℂ)) ^ ((b : ℂ) - a - 1) * exp (z * s) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-b * t) • ((t : ℂ) ^ (a - 1) * largeBGenerating a z t) := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, ← hcub_image,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi (fun t _ => hcub_hasDerivWithinAt t)
      hcub_injOn]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  exact hcub_subst a z b ht

/-- For `0 < Re a < b`, the Laplace integrand `e^{-bt} t^{a-1} G(a,z,t)` is integrable on `(0, ∞)`.
-/
theorem hcub_integrableOn (a z : ℂ) (ha : 0 < a.re) {b : ℝ} (hb : a.re < b) :
    IntegrableOn (fun t : ℝ => Real.exp (-b * t) • ((t : ℂ) ^ (a - 1) * largeBGenerating a z t))
      (Ioi 0) := by
  have hβ := betaIntegral_convergent (u := a) (v := (b : ℂ) - a) ha (by simp; linarith)
  have h1 : IntervalIntegrable (fun s : ℝ => (s : ℂ) ^ (a - 1) * (1 - (s : ℂ)) ^ ((b : ℂ) - a - 1) *
      exp (z * s)) volume 0 1 := hβ.mul_continuousOn (by fun_prop)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h1
  have h2 := h1.mono_set Ioo_subset_Ioc_self
  rw [← hcub_image, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t _ => hcub_hasDerivWithinAt t) hcub_injOn] at h2
  refine h2.congr_fun (fun t ht => hcub_subst a z b ht) measurableSet_Ioi


/-- Watson's lemma for the Laplace form of Euler's integral: the large-`b` expansion of
`b^a Γ(b-a)/Γ(b) M(a,b,z)` when `re a > 0`. -/
theorem hcub_largeB_base (a z : ℂ) (ha : 0 < a.re) (n : ℕ) :
    (fun b : ℝ => (b : ℂ) ^ a * Gamma (b - a) / Gamma b * kummerM a b z -
       ∑ s ∈ Finset.range n, poch a s * largeBCoeff a z s * ((b : ℂ)⁻¹) ^ s)
      =O[atTop] fun b => ((b : ℂ)⁻¹) ^ n := by
  set F : ℝ → ℂ := fun t => (t : ℂ) ^ (a - 1) * largeBGenerating a z t with hF
  have hF : ∀ N : ℕ, (fun t : ℝ => F t - ∑ k ∈ Finset.range N,
      ((t : ℂ) ^ ((k : ℂ) + a - 1)) • largeBCoeff a z k) =O[𝓝[>] 0]
        fun t : ℝ => t ^ ((N : ℝ) + a.re - 1) := by
    intro N
    have hT : (fun t : ℝ => largeBGenerating a z t - ∑ k ∈ Finset.range N,
        largeBCoeff a z k * (t : ℂ) ^ k) =O[𝓝[>] 0] fun t : ℝ => ‖(t : ℂ)‖ ^ N := by
      have hc : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 0) := by
        have := (continuous_ofReal.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
      exact (hcub_largeB_taylor a z N).comp_tendsto hc
    have hT' : (fun t : ℝ => largeBGenerating a z t - ∑ k ∈ Finset.range N,
        largeBCoeff a z k * (t : ℂ) ^ k) =O[𝓝[>] 0] fun t : ℝ => (t : ℂ) ^ N :=
      hT.trans (IsBigO.of_bound 1 (Eventually.of_forall fun t => by simp))
    have hm := (isBigO_refl (fun t : ℝ => (t : ℂ) ^ (a - 1)) (𝓝[>] 0)).mul hT'
    refine (hm.congr' ?_ EventuallyEq.rfl).trans (IsBigO.of_bound 1 ?_)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
      simp only [hF, mul_sub, Finset.mul_sum, smul_eq_mul]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show (k : ℂ) + a - 1 = (k : ℂ) + (a - 1) by ring, cpow_add _ _ ht0, cpow_natCast]
      ring
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0 : ℝ) < t := ht
      rw [norm_mul, norm_pow, norm_cpow_eq_rpow_re_of_pos ht', Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos ht', Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos ht' _), one_mul,
        show (N : ℝ) + a.re - 1 = (a - 1).re + N by simp; ring, Real.rpow_add ht',
        Real.rpow_natCast]
  have hW := hasAsymptoticExpansion_integral_exp_smul_cpow (μ := a) (c := a.re + 1) ha
    (hcub_integrableOn a z ha (by linarith)) hF n
  have hm := (isBigO_refl (fun b : ℝ => (b : ℂ) ^ a / Gamma a) atTop).mul hW
  have hGa : Gamma a ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos ha)
  refine (hm.congr' ?_ ?_).trans (isBigO_const_mul_self (Gamma a)⁻¹ _ atTop)
  · filter_upwards [eventually_gt_atTop (a.re + 1)] with b hb
    have hb0 : 0 < b := by linarith
    have hba : 0 < ((b : ℂ) - a).re := by simp; linarith
    have hGb : Gamma (b : ℂ) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos (by simpa using hb0))
    have hGba : Gamma ((b : ℂ) - a) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos hba)
    rw [kummerM_eq_euler_integral ha hba, hcub_euler_eq_laplace]
    simp only [smul_eq_mul, mul_sub, Finset.mul_sum]
    congr 1
    · field_simp
    · refine Finset.sum_congr rfl fun s _ => ?_
      have hp : Gamma ((s : ℂ) + a) = Gamma a * poch a s := by
        have h1 := DLMF.Gamma.poch_mul_recip_Gamma_add_nat a s
        have h2 : Gamma (a + s) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos (by simp; positivity))
        rw [add_comm]
        field_simp at h1
        linear_combination -h1
      rw [hp, ← hcub_cpow_mul_cpow_neg hb0 a s]
      field_simp
  · filter_upwards [eventually_gt_atTop 0] with b hb
    rw [← hcub_cpow_mul_cpow_neg hb a n]
    field_simp


/-- `b^a Γ(b-a)/Γ(b+s) = ∑_{k<n-s} G_k b^{-s-k} + O(b^{-n})`, from the Gamma-ratio expansion
5.11.13. -/
theorem hcub_ratio_shift_kummer (a : ℂ) {s n : ℕ} (hs : s ≤ n) :
    (fun b : ℝ => (b : ℂ) ^ a * Gamma ((b : ℂ) - a) / Gamma ((b : ℂ) + s) -
      ∑ k ∈ Finset.range (n - s), DLMF.Gamma.stirlingRatioG (-a) s k * ((b : ℂ)⁻¹) ^ (s + k))
      =O[atTop] fun b => ((b : ℂ)⁻¹) ^ n := by
  have h := DLMF.Gamma.Gamma_ratio_expansion (-a) (s : ℂ) (n - s)
  have hm := (isBigO_refl (fun b : ℝ => (b : ℂ) ^ a) atTop).mul h
  refine hm.congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with b hb
    have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← sub_eq_add_neg]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun k _ => ?_
      have := hcub_cpow_mul_cpow_neg hb a s
      rw [show -a - (s : ℂ) = -((s : ℂ) + a) by ring, pow_add, ← this, inv_pow]
      ring
  · filter_upwards [eventually_gt_atTop 0] with b hb
    rw [show -a - (s : ℂ) - ((n - s : ℕ) : ℂ) = -((n : ℂ) + a) by push_cast [hs]; ring,
      hcub_cpow_mul_cpow_neg hb]

/-- `b^a Γ(b-a)/Γ(b)` is bounded as `b → +∞`. -/
theorem hcub_ratio_isBigO_one (a : ℂ) :
    (fun b : ℝ => (b : ℂ) ^ a * Gamma ((b : ℂ) - a) / Gamma (b : ℂ)) =O[atTop]
      fun _ => (1 : ℂ) := by
  have h := hcub_ratio_shift_kummer a (s := 0) (n := 0) le_rfl
  simpa using h

/-- Coefficients of 13.8.1 re-expanded in powers of `1/b` after multiplication by
`b^a Γ(b-a)/Γ(b)`. -/
noncomputable def hcub_largeBMix (a z : ℂ) (N : ℕ) : ℂ :=
  ∑ s ∈ Finset.range (N + 1), poch a s * z ^ s / s ! * DLMF.Gamma.stirlingRatioG (-a) s (N - s)

/-- 13.8.1 re-expanded: `b^a Γ(b-a)/Γ(b) M(a,b,z) ~ ∑ hcub_largeBMix a z N b^{-N}` for all `a`. -/
theorem hcub_largeB_mix (a z : ℂ) (n : ℕ) :
    (fun b : ℝ => (b : ℂ) ^ a * Gamma (b - a) / Gamma b * kummerM a b z -
       ∑ N ∈ Finset.range n, hcub_largeBMix a z N * ((b : ℂ)⁻¹) ^ N)
      =O[atTop] fun b => ((b : ℂ)⁻¹) ^ n := by
  have h1 := kummerM_large_b a z n
  have h2 := ((hcub_ratio_isBigO_one a).mul h1).congr_right fun b => one_mul _
  have h3 : (fun b : ℝ => ∑ s ∈ Finset.range n, poch a s * z ^ s / s ! *
      ((b : ℂ) ^ a * Gamma ((b : ℂ) - a) / Gamma ((b : ℂ) + s) -
        ∑ k ∈ Finset.range (n - s), DLMF.Gamma.stirlingRatioG (-a) s k * ((b : ℂ)⁻¹) ^ (s + k)))
      =O[atTop] fun b => ((b : ℂ)⁻¹) ^ n :=
    IsBigO.fun_sum fun s hs => (hcub_ratio_shift_kummer a
      (Finset.mem_range.mp hs).le).const_mul_left _
  refine (h2.add h3).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with b hb
  have hb' : ∀ k : ℕ, (b : ℂ) ≠ -k := not_neg_nat_of_re_pos (by simpa using hb)
  have hGb : Gamma (b : ℂ) ≠ 0 := Gamma_ne_zero hb'
  have hflip := Finset.sum_range_diag_flip n fun s k =>
    poch a s * z ^ s / s ! * (DLMF.Gamma.stirlingRatioG (-a) s k * ((b : ℂ)⁻¹) ^ (s + k))
  simp only [hcub_largeBMix, Finset.sum_mul]
  have hN : ∀ m ∈ Finset.range n, ∑ k ∈ Finset.range (m + 1),
      poch a k * z ^ k / k ! * DLMF.Gamma.stirlingRatioG (-a) k (m - k) * ((b : ℂ)⁻¹) ^ m =
      ∑ k ∈ Finset.range (m + 1), poch a k * z ^ k / k ! *
        (DLMF.Gamma.stirlingRatioG (-a) k (m - k) * ((b : ℂ)⁻¹) ^ (k + (m - k))) := by
    intro m _
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
    ring
  rw [Finset.sum_congr rfl hN, hflip]
  have hS : ∀ s ∈ Finset.range n, poch a s / (poch (b : ℂ) s * s !) * z ^ s *
      ((b : ℂ) ^ a * Gamma ((b : ℂ) - a) / Gamma (b : ℂ)) =
      poch a s * z ^ s / s ! * ((b : ℂ) ^ a * Gamma ((b : ℂ) - a) / Gamma ((b : ℂ) + s)) := by
    intro s _
    have h := DLMF.Gamma.poch_mul_recip_Gamma_add_nat (b : ℂ) s
    have hp : poch (b : ℂ) s ≠ 0 := poch_ne_zero_of_not_neg_nat hb' s
    have hGs : Gamma ((b : ℂ) + s) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos (by simp; positivity))
    have hf : (s ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp at h
    rw [← h]
    field_simp
  simp only [mul_sub, Finset.mul_sum] at *
  rw [Finset.sum_congr rfl (fun s hs => (mul_comm _ _).trans (hS s hs))]
  simp only [Finset.sum_sub_distrib]
  ring


/-- For `re a > 0` the re-expanded coefficients of 13.8.1 are those of 13.8.2. -/
theorem hcub_largeBMix_eq_of_re_pos (a z : ℂ) (ha : 0 < a.re) (N : ℕ) :
    hcub_largeBMix a z N = poch a N * largeBCoeff a z N := by
  have h := HasAsymptoticExpansion.unique hcub_isAsymptoticScale hcub_frequently_ne
    (a := hcub_largeBMix a z) (b := fun N => poch a N * largeBCoeff a z N)
    (f := fun b : ℝ => (b : ℂ) ^ a * Gamma (b - a) / Gamma b * kummerM a b z)
    (fun n => (hcub_largeB_mix a z n).congr_left fun b => by
      simp only [smul_eq_mul]; congr 1; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _)
    (fun n => (hcub_largeB_base a z ha n).congr_left fun b => by
      simp only [smul_eq_mul]; congr 1; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _)
  exact congrFun h N

/-- The explicit large-`b` coefficient sum is entire in `a`. -/
theorem hcub_differentiable_largeBMix (z : ℂ) (N : ℕ) :
    Differentiable ℂ (fun a => hcub_largeBMix a z N) := by
  unfold hcub_largeBMix
  refine Differentiable.fun_sum fun s _ => ?_
  exact (((Polynomial.differentiable _).mul (differentiable_const _)).div_const _).mul
    ((hcub_differentiable_stirlingRatioG _ _).comp differentiable_neg)

/-- The large-`b` generating function is complex differentiable in `t` for `|t| ≤ 1/2`. -/
theorem hcub_differentiableAt_largeBGenerating (a z : ℂ) {t : ℂ} (ht : ‖t‖ ≤ 1 / 2) :
    DifferentiableAt ℂ (largeBGenerating a z) t := by
  have hE : DifferentiableAt ℂ expSubOneDiv t := (analyticAt_expSubOneDiv t).differentiableAt
  show DifferentiableAt ℂ (fun t => expSubOneDiv t ^ (a - 1) * exp (t + z * (1 - exp (-t)))) t
  exact (hE.cpow (differentiableAt_const _) (hcub_expSubOneDiv_mem_slitPlane ht)).mul
    (by fun_prop)

/-- Each large-`b` coefficient is an entire function of `a`. -/
theorem hcub_differentiable_largeBCoeff (z : ℂ) (N : ℕ) :
    Differentiable ℂ (fun a => largeBCoeff a z N) := by
  have hE : ∀ t : ℂ, DifferentiableAt ℂ expSubOneDiv t := fun t =>
    (analyticAt_expSubOneDiv t).differentiableAt
  have hrest : ∀ t : ℂ, DifferentiableAt ℂ (fun t : ℂ => exp (t + z * (1 - exp (-t)))) t :=
    fun t => by fun_prop
  have h := hcub_differentiable_iteratedDeriv (G := fun a t => largeBGenerating a z t)
    (r := 1 / 2) (by norm_num)
    (fun a t ht => by
      have hEc : ContinuousAt (fun p : ℂ × ℂ => expSubOneDiv p.2) (a, t) :=
        ContinuousAt.comp (f := fun p : ℂ × ℂ => p.2) (g := expSubOneDiv) (hE t).continuousAt
          continuous_snd.continuousAt
      have hpow : ContinuousAt (fun p : ℂ × ℂ => expSubOneDiv p.2 ^ (p.1 - 1)) (a, t) :=
        hEc.cpow (continuous_fst.sub continuous_const).continuousAt
          (hcub_expSubOneDiv_mem_slitPlane ht.le)
      have hr : ContinuousAt (fun p : ℂ × ℂ => exp (p.2 + z * (1 - exp (-p.2)))) (a, t) :=
        ContinuousAt.comp (f := fun p : ℂ × ℂ => p.2)
          (g := fun t : ℂ => exp (t + z * (1 - exp (-t)))) (hrest t).continuousAt
          continuous_snd.continuousAt
      exact hpow.mul hr)
    (fun a t ht => (hcub_differentiableAt_largeBGenerating a z
      (by simpa using ht)).differentiableWithinAt)
    (fun t ht => by
      have h0 : expSubOneDiv t ≠ 0 := slitPlane_ne_zero (hcub_expSubOneDiv_mem_slitPlane ht.le)
      intro a
      exact ((differentiableAt_id.sub (differentiableAt_const _)).const_cpow
        (Or.inl h0)).mul (differentiableAt_const _)) N
  exact h.div_const _

/-- The coefficient identity behind 13.8.2, for all `a`: the re-expansion of 13.8.1 has the
coefficients `(a)_N q_N(a,z)`. Proved for `re a > 0` by uniqueness of asymptotic expansions
(Watson's lemma on one side, 13.8.1 on the other) and continued by the identity theorem. -/
theorem hcub_largeBMix_eq (a z : ℂ) (N : ℕ) :
    hcub_largeBMix a z N = poch a N * largeBCoeff a z N := by
  set f : ℂ → ℂ := fun a => hcub_largeBMix a z N - poch a N * largeBCoeff a z N with hfdef
  have hf : Differentiable ℂ f := (hcub_differentiable_largeBMix z N).sub
    ((Polynomial.differentiable _).mul (hcub_differentiable_largeBCoeff z N))
  have hA : AnalyticOnNhd ℂ f univ := fun x _ => hf.analyticAt x
  have h0 : f =ᶠ[𝓝 1] 0 := by
    have hopen : IsOpen {a : ℂ | 0 < a.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (1 : ℂ) ∈ {a : ℂ | 0 < a.re})] with x hx
    simp [hfdef, hcub_largeBMix_eq_of_re_pos x z hx N]
  have := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ 1) h0
    (mem_univ a)
  simpa [hfdef, sub_eq_zero] using this

/-- `Γ(b)/Γ(b-a) b^{-a}` is bounded as `b → +∞`. -/
theorem hcub_ratio_isBigO_one' (a : ℂ) :
    (fun b : ℝ => Gamma (b : ℂ) / Gamma ((b : ℂ) - a) * (b : ℂ) ^ (-a)) =O[atTop]
      fun _ => (1 : ℂ) := by
  have h := DLMF.Gamma.Gamma_ratio_expansion 0 (-a) 0
  have hm := (isBigO_refl (fun b : ℝ => (b : ℂ) ^ (-a)) atTop).mul h
  refine hm.congr' (Eventually.of_forall fun b => ?_) ?_
  · simp [sub_eq_add_neg]; ring
  · filter_upwards [eventually_gt_atTop 0] with b hb
    have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    rw [← cpow_add _ _ hb0]; simp

end LargeBPoincare

/- The Gamma ratio grows like b^a, so the absolute remainder is O(b^(-n)). -/
@[dlmf 13.8.E2]
theorem kummerM_large_b_poincare (a z : ℂ) (n : ℕ) :
    Asymptotics.IsBigO atTop
      (fun b : ℝ => kummerM a b z -
        Gamma (b : ℂ) / Gamma ((b : ℂ) - a) *
          ∑ s ∈ Finset.range n, poch a s * largeBCoeff a z s * (b : ℂ) ^ (-(s : ℂ) - a))
      (fun b : ℝ => (b : ℂ) ^ (-(n : ℂ))) := by
  have hK := hcub_largeB_mix a z n
  simp only [hcub_largeBMix_eq] at hK
  refine ((hcub_ratio_isBigO_one' a).mul hK).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (max 0 a.re)] with b hb
    have hb0' : 0 < b := lt_of_le_of_lt (le_max_left _ _) hb
    have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb0'.ne'
    have hba : 0 < ((b : ℂ) - a).re := by simp; linarith [le_max_right 0 a.re]
    have hGb : Gamma (b : ℂ) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos (by simpa using hb0'))
    have hGba : Gamma ((b : ℂ) - a) ≠ 0 := Gamma_ne_zero (not_neg_nat_of_re_pos hba)
    have hpa : (b : ℂ) ^ (-a) * (b : ℂ) ^ a = 1 := by
      rw [← cpow_add _ _ hb0]; simp
    have hs : ∀ s : ℕ, (b : ℂ) ^ (-(s : ℂ) - a) = (b : ℂ) ^ (-a) * ((b : ℂ)⁻¹) ^ s := by
      intro s
      rw [sub_eq_add_neg, add_comm, cpow_add _ _ hb0, cpow_neg (b : ℂ) (s : ℂ), cpow_natCast,
        inv_pow]
    simp only [hs, mul_sub, Finset.mul_sum]
    congr 1
    · field_simp
      linear_combination (kummerM a b z) * hpa
    · refine Finset.sum_congr rfl fun s _ => by ring
  · filter_upwards [eventually_gt_atTop 0] with b hb
    rw [one_mul, cpow_neg, cpow_natCast, inv_pow]

@[dlmf 13.8.E6]
theorem kummerM_transition (a : ℂ) :
    Asymptotics.IsBigO atTop
      (fun b : ℝ => kummerM a b b -
        (Real.sqrt π : ℂ) * (b / 2 : ℂ) ^ (a / 2) *
          (1 / Gamma ((a + 1) / 2) + (a + 1) * (8 / b : ℂ) ^ (1 / 2 : ℂ) / (3 * Gamma (a / 2))))
      (fun b : ℝ => (b : ℂ) ^ (a / 2 - 1)) := by
  sorry

@[dlmf 13.8.E7]
theorem kummerU_transition (a : ℂ) :
    Asymptotics.IsBigO atTop
      (fun b : ℝ => kummerU a b b -
        (Real.sqrt π : ℂ) * (2 * b : ℂ) ^ (-(a / 2)) *
          (1 / Gamma ((a + 1) / 2) - (a + 1) * (8 / b : ℂ) ^ (1 / 2 : ℂ) / (3 * Gamma (a / 2))))
      (fun b : ℝ => (b : ℂ) ^ (-(a / 2) - 1)) := by
  sorry

/- DLMF uses scaled Gamma in M, ordinary Gamma in U, and a relative error in U.
The parameter ray is real and positive, as in the source statement. -/
@[dlmf 13.8.E17]
theorem kummerM_large_a_b (ν : ℝ) (z : ℂ) (hν : 0 < ν) (hν1 : ν < 1) :
    Asymptotics.IsBigO atTop
      (fun a : ℝ => kummerM a (a / ν) z -
        exp (ν * z) * DLMF.Gamma.scaledGamma (a / ν : ℂ) / DLMF.Gamma.scaledGamma (a : ℂ) *
          (1 + (1 - ν) * (1 + 6 * ν ^ 2 * z ^ 2) / (12 * a)))
      (fun a : ℝ => (a : ℂ)⁻¹ ^ 2) := by
  sorry

@[dlmf 13.8.E18]
theorem kummerU_large_a_b (ν : ℝ) (z : ℂ) (hν : 0 < ν) (hν1 : ν < 1)
    (hz : 0 < z.re) :
    Asymptotics.IsBigO atTop
      (fun a : ℝ => kummerU a (a / ν + 1) z -
        z ^ (-(a / ν : ℂ)) * exp ((1 - ν) * z) * Gamma (a / ν : ℂ) / Gamma (a : ℂ) *
          (1 + ν * z * (1 - ν) * (2 - ν * z) / (2 * a)))
      (fun a : ℝ => z ^ (-(a / ν : ℂ)) * exp ((1 - ν) * z) *
        Gamma (a / ν : ℂ) / Gamma (a : ℂ) * (a : ℂ)⁻¹ ^ 2) := by
  sorry

@[dlmf 13.19.E1]
theorem whittakerM_poincare_real (κ μ : ℂ) (n : ℕ)
    (hκ : ∀ k : ℕ, μ - κ ≠ -1 / 2 - k) (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    Asymptotics.IsBigO atTop
      (fun x : ℝ => whittakerM κ μ x -
        Gamma (1 + 2 * μ) / Gamma (1 / 2 + μ - κ) * exp (x / 2) * (x : ℂ) ^ (-κ) *
          ∑ s ∈ Finset.range n,
            poch (1 / 2 - μ + κ) s * poch (1 / 2 + μ + κ) s / s.factorial *
              (x : ℂ) ^ (-(s : ℂ)))
      (fun x : ℝ => exp (x / 2) * (x : ℂ) ^ (-κ - n)) := by
  have h := regularizedHGFun_poincare_real (μ - κ + 1 / 2) (1 + 2 * μ) n (fun k hk =>
    hκ k (by linear_combination hk))
  rw [show 1 - (μ - κ + 1 / 2) = 1 / 2 - μ + κ by ring,
    show 1 + 2 * μ - (μ - κ + 1 / 2) = 1 / 2 + μ + κ by ring,
    show μ - κ + 1 / 2 = 1 / 2 + μ - κ by ring] at h
  refine (((isBigO_refl (fun x : ℝ => Gamma (1 + 2 * μ) * exp (-x / 2) * (x : ℂ) ^ (μ + 1 / 2))
    atTop).mul h).congr' ?_ ?_).trans (isBigO_const_mul_self (Gamma (1 + 2 * μ))
      (fun x : ℝ => exp (x / 2) * (x : ℂ) ^ (-κ - n)) atTop)
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [whittakerM, kummerM_eq_mul_regularizedHGFun hμ]
    have hp : exp (-(x : ℂ) / 2) * (x : ℂ) ^ (μ + 1 / 2) * (exp (x : ℂ) *
        (x : ℂ) ^ (1 / 2 + μ - κ - (1 + 2 * μ))) = exp ((x : ℂ) / 2) * (x : ℂ) ^ (-κ) := by
      rw [show exp (-(x : ℂ) / 2) * (x : ℂ) ^ (μ + 1 / 2) * (exp (x : ℂ) *
        (x : ℂ) ^ (1 / 2 + μ - κ - (1 + 2 * μ))) = (exp (-(x : ℂ) / 2) * exp (x : ℂ)) *
          ((x : ℂ) ^ (μ + 1 / 2) * (x : ℂ) ^ (1 / 2 + μ - κ - (1 + 2 * μ))) by ring,
        ← Complex.exp_add, ← Complex.cpow_add _ _ hx0]
      ring_nf
    rw [show 1 / 2 + μ - κ = μ - κ + 1 / 2 by ring] at hp ⊢
    linear_combination (-Gamma (1 + 2 * μ) / Gamma (μ - κ + 1 / 2) * ∑ s ∈ Finset.range n,
      poch (1 / 2 - μ + κ) s * poch (1 / 2 + μ + κ) s / s.factorial *
        (x : ℂ) ^ (-(s : ℂ))) * hp
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [show Gamma (1 + 2 * μ) * exp (-(x : ℂ) / 2) * (x : ℂ) ^ (μ + 1 / 2) *
      (exp (x : ℂ) * (x : ℂ) ^ (1 / 2 + μ - κ - (1 + 2 * μ) - n)) =
      Gamma (1 + 2 * μ) * ((exp (-(x : ℂ) / 2) * exp (x : ℂ)) *
        ((x : ℂ) ^ (μ + 1 / 2) * (x : ℂ) ^ (1 / 2 + μ - κ - (1 + 2 * μ) - n))) by ring,
      ← Complex.exp_add, ← Complex.cpow_add _ _ hx0]
    ring_nf

@[dlmf 13.19.E3]
theorem whittakerW_poincare (κ μ : ℂ) (n : ℕ) :
    Asymptotics.IsBigO atTop
      (fun x : ℝ => whittakerW κ μ x -
        exp (-x / 2) * (x : ℂ) ^ κ *
          ∑ s ∈ Finset.range n,
            poch (1 / 2 + μ - κ) s * poch (1 / 2 - μ - κ) s / s.factorial *
              (-(x : ℂ)) ^ (-(s : ℂ)))
      (fun x : ℝ => exp (-x / 2) * (x : ℂ) ^ (κ - n)) := by
  have h := kummerU_poincare (1 / 2 + μ - κ) (1 + 2 * μ) n
  rw [show 1 / 2 + μ - κ - (1 + 2 * μ) + 1 = 1 / 2 - μ - κ by ring] at h
  refine ((isBigO_refl (fun x : ℝ => exp (-x / 2) * (x : ℂ) ^ (1 / 2 + μ)) atTop).mul h
    ).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [whittakerW_eq_kummerU (by simpa using hx)]
    have hp : (x : ℂ) ^ (1 / 2 + μ) * (x : ℂ) ^ (-(1 / 2 + μ - κ)) = (x : ℂ) ^ κ := by
      rw [← Complex.cpow_add _ _ hx0]; ring_nf
    linear_combination (-exp (-x / 2) * ∑ s ∈ Finset.range n,
      poch (1 / 2 + μ - κ) s * poch (1 / 2 - μ - κ) s / s.factorial *
        (-(x : ℂ)) ^ (-(s : ℂ))) * hp
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [mul_assoc, ← Complex.cpow_add _ _ hx0]
    ring_nf

end DLMF.Confluent
