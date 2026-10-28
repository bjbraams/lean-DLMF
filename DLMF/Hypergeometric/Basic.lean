/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# The hypergeometric series (AAR §2.1)

Mathlib defines `ordinaryHypergeometric` / `₂F₁` and proves that its radius of convergence is
`1` (or `⊤` when the series terminates). AAR Theorem 2.1.1 for `p = 2`, `q = 1` is that
statement. Elementary specializations (2.1.3)–(2.1.6) are recorded below.
-/

@[expose] public section

open Complex Filter Nat
open scoped Topology Real

noncomputable section

namespace DLMF.Hypergeometric

/-- The `n`-th Pochhammer symbol `(a)_n`. -/
abbrev poch (a : ℂ) (n : ℕ) : ℂ :=
  (ascPochhammer ℂ n).eval a

@[dlmf 5.2.E4]
theorem poch_zero (a : ℂ) : poch a 0 = 1 := by simp [poch]

/-- `(a)₁ = a`. -/
theorem poch_one (a : ℂ) : poch a 1 = a := by simp [poch]

@[dlmf 5.2.E4]
theorem poch_succ (a : ℂ) (n : ℕ) : poch a (n + 1) = poch a n * (a + n) :=
  ascPochhammer_succ_eval n a

/-- `(1)ₙ = n!`. -/
theorem poch_nat_one (n : ℕ) : poch (1 : ℂ) n = n ! := by
  simp [poch, ascPochhammer_eval_one]

/-- `(2)ₙ = (n + 1)!`. -/
theorem poch_nat_two (n : ℕ) : poch (2 : ℂ) n = ((n + 1)! : ℂ) := by
  unfold poch
  rw [show (2 : ℂ) = ↑(2 : ℕ) by simp, ascPochhammer_nat_eq_natCast_ascFactorial]
  simp [Nat.ascFactorial_eq_div (n := 1) n, Nat.factorial_one, add_comm]

/-- `(0)ₙ₊₁ = 0`. -/
theorem poch_zero_succ (n : ℕ) : poch (0 : ℂ) (n + 1) = 0 := by
  rw [poch, (ascPochhammer_eval_eq_zero_iff _ _).2]
  exact ⟨0, Nat.succ_pos n, by simp⟩

/-- `(a)ₙ ≠ 0` when `a` is not a nonpositive integer. -/
theorem poch_ne_zero_of_not_neg_nat {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) (n : ℕ) :
    poch a n ≠ 0 := by
  intro h
  obtain ⟨k, hk, hk'⟩ := (ascPochhammer_eval_eq_zero_iff (R := ℂ) n a).1 h
  exact ha k (neg_eq_iff_eq_neg.mp hk'.symm)

/-- Concatenation of Pochhammer symbols: `(a)_{n+m} = (a)_n (a+n)_m`. -/
theorem poch_add (a : ℂ) (n m : ℕ) : poch a (n + m) = poch a n * poch (a + n) m := by
  induction m with
  | zero => simp [poch_zero]
  | succ m ih =>
    rw [Nat.add_succ, poch_succ, ih, poch_succ]
    push_cast
    ring

/-- Binomial theorem for rising factorials: `(a + b)_N = ∑ C(N,m) (a)_m (b)_{N-m}`. -/
theorem poch_add_eq_sum (a b : ℂ) (N : ℕ) :
    poch (a + b) N = ∑ m ∈ Finset.range (N + 1), (N.choose m : ℂ) * poch a m * poch b (N - m) := by
  induction N with
  | zero => simp [poch_zero]
  | succ N ih =>
    rw [poch_succ, ih, Finset.sum_mul]
    rw [Finset.sum_range_succ' _ (N + 1)]
    simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, Finset.sum_add_distrib,
      Nat.choose_zero_right, Nat.cast_one, one_mul, poch_zero, Nat.sub_zero, Nat.succ_eq_add_one]
    have hB : ∑ m ∈ Finset.range (N + 1), (N.choose (m + 1) : ℂ) * poch a (m + 1) *
        poch b (N + 1 - (m + 1)) + poch b (N + 1) =
        ∑ m ∈ Finset.range (N + 1), (N.choose m : ℂ) * poch a m * poch b (N + 1 - m) := by
      rw [Finset.sum_range_succ' (fun m => (N.choose m : ℂ) * poch a m * poch b (N + 1 - m)),
        Finset.sum_range_succ]
      simp [Nat.choose_succ_self, poch_zero]
    conv_rhs => rw [add_assoc, hB, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmN : m ≤ N := by simp at hm; omega
    rw [show N + 1 - (m + 1) = N - m by omega, show N + 1 - m = (N - m) + 1 by omega,
      poch_succ a m, poch_succ b (N - m), Nat.cast_sub hmN]
    ring

/-- Distributing a power over the factors of a Pochhammer symbol. -/
theorem poch_mul_pow (c t : ℂ) (k : ℕ) :
    poch c k * t ^ k = ∏ j ∈ Finset.range k, ((c + j) * t) := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih => rw [poch_succ, Finset.prod_range_succ, ← ih]; ring

/-- Helper lemma for terminating hypergeometric sums: `(-n)_k = (-1)^k n^{\underline{k}}`. -/
theorem poch_neg_coe_nat (n k : ℕ) :
    poch (-(n : ℂ)) k = (-1 : ℂ) ^ k * n.descFactorial k := by
  rw [poch, ascPochhammer_eval_neg_eq_descPochhammer ℂ (n : ℂ) k,
    descPochhammer_eval_eq_descFactorial ℂ n k]

/-- Binomial theorem in Pochhammer form: `∑ₖ (-n)ₖ yᵏ / k! = (1 - y)ⁿ`. -/
theorem sum_poch_neg_nat_div_factorial_mul_pow (n : ℕ) (y : ℂ) :
    ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k / k ! * y ^ k = (1 - y) ^ n := by
  rw [sub_eq_add_neg, add_comm (1 : ℂ), add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  rw [poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose, one_pow, neg_pow y]
  push_cast
  field_simp

/-- Helper lemma for terminating hypergeometric sums. -/
@[dlmf 5.2.E7]
theorem poch_neg_nat_eq_zero {n k : ℕ} (h : n < k) : poch (-(n : ℂ)) k = 0 := by
  rw [poch, ascPochhammer_eval_eq_zero_iff]
  exact ⟨n, h, by simp⟩

/-- The series `₂F₁(0,b;c;z)` terminates after the constant term. -/
theorem ordinaryHypergeometric_zero_left (b c z : ℂ) : ₂F₁ (0 : ℂ) b c z = 1 := by
  rw [ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul]
  have h : (fun n : ℕ =>
      (n !⁻¹ : ℂ) * (ascPochhammer ℂ n).eval 0 * (ascPochhammer ℂ n).eval b *
        ((ascPochhammer ℂ n).eval c)⁻¹ * z ^ n) =
      fun n => if n = 0 then 1 else 0 := by
    ext n
    cases n with
    | zero => simp
    | succ n => simp
  rw [h, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

/-- The coefficient of `z^n` in `₂F₁(a,b;c;z)`. -/
def gaussHGCoeff (a b c : ℂ) (n : ℕ) : ℂ :=
  poch a n * poch b n / (poch c n * n !)

/-- Mathlib's `ordinaryHypergeometricCoefficient` agrees with the project coefficient
  `gaussHGCoeff`. -/
theorem ordinaryHypergeometricCoefficient_eq (a b c : ℂ) (n : ℕ) :
    ordinaryHypergeometricCoefficient a b c n = gaussHGCoeff a b c n := by
  simp [ordinaryHypergeometricCoefficient, gaussHGCoeff, poch, div_eq_mul_inv, mul_assoc,
    mul_left_comm, mul_comm]

/-- Helper lemma for Chu–Vandermonde and the shifted Legendre evaluation. -/
theorem gaussHGCoeff_neg_nat (n : ℕ) (b c : ℂ) (k : ℕ) :
    gaussHGCoeff (-(n : ℂ)) b c k =
      (-1 : ℂ) ^ k * n.choose k * poch b k / poch c k := by
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  rw [gaussHGCoeff, poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field [hk]

/-- A terminating `₂F₁(-n,b;c;z)` is a polynomial of degree at most `n`. -/
@[dlmf 15.2.E4]
theorem ordinaryHypergeometric_eq_sum_neg_nat (n : ℕ) (b c z : ℂ) :
    ₂F₁ (-(n : ℂ)) b c z =
      ∑ k ∈ Finset.range (n + 1), gaussHGCoeff (-(n : ℂ)) b c k * z ^ k := by
  rw [ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul]
  have hterm : (fun k : ℕ =>
      (k !⁻¹ : ℂ) * (ascPochhammer ℂ k).eval (-(n : ℂ)) *
        (ascPochhammer ℂ k).eval b * ((ascPochhammer ℂ k).eval c)⁻¹ * z ^ k) =
      fun k => gaussHGCoeff (-(n : ℂ)) b c k * z ^ k := by
    funext k
    simp [gaussHGCoeff, poch, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  rw [hterm]
  refine tsum_eq_sum fun k hk => ?_
  have hkn : n < k := by
    rw [Finset.mem_range] at hk
    omega
  simp [gaussHGCoeff, poch_neg_nat_eq_zero hkn]

/-- The coefficients of `₂F₁(1, 1; 2; z)` are `1/(n + 1)`. -/
theorem gaussHGCoeff_one_one_two (n : ℕ) : gaussHGCoeff 1 1 2 n = 1 / (n + 1 : ℂ) := by
  have hfact : ((n + 1)! : ℂ) = (n ! : ℂ) * (n + 1) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_comm]
  rw [gaussHGCoeff, poch_nat_one, poch_nat_two, hfact]
  field [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]

/-- The series `₂F₁(1, 1; 2; z)` has radius of convergence `1`. -/
theorem radius_ordinaryHypergeometric_one_one_two :
    (ordinaryHypergeometricSeries ℂ (1 : ℂ) 1 2).radius = 1 :=
  ordinaryHypergeometricSeries_radius_eq_one ℂ (1 : ℂ) 1 2 fun kn => by
    have hk : (0 : ℝ) ≤ kn := Nat.cast_nonneg kn
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have : (kn : ℝ) = -1 := by simpa using congrArg Complex.re h
      linarith
    · intro h
      have : (kn : ℝ) = -1 := by simpa using congrArg Complex.re h
      linarith
    · intro h
      have : (kn : ℝ) = -2 := by simpa using congrArg Complex.re h
      linarith

/-- Helper lemma for series identities inside the unit disk. -/
theorem mem_eball_one_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    z ∈ Metric.eball (0 : ℂ) 1 := by
  rw [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm]
  exact ENNReal.coe_lt_coe.mpr (mod_cast hz)

/-- Helper lemma for `log_one_add_eq_ordinaryHypergeometric`: the series of `₂F₁(1,1;2;-x)`. -/
theorem hasSum_ordinaryHypergeometric_one_one_two {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => (-x) ^ n / (n + 1 : ℂ)) (₂F₁ (1 : ℂ) 1 2 (-x)) := by
  have hmem : -x ∈ Metric.eball (0 : ℂ)
      (ordinaryHypergeometricSeries ℂ (1 : ℂ) 1 2).radius := by
    rw [radius_ordinaryHypergeometric_one_one_two]
    exact mem_eball_one_of_norm_lt_one (by simpa)
  have hs := (ordinaryHypergeometricSeries ℂ (1 : ℂ) 1 2).hasSum hmem
  have heq : (fun n : ℕ => ordinaryHypergeometricSeries ℂ (1 : ℂ) 1 2 n fun _ => -x) =
      fun n : ℕ => (-x) ^ n / (n + 1 : ℂ) := by
    refine funext fun (n : ℕ) => ?_
    rw [ordinaryHypergeometricSeries_apply_eq]
    change ordinaryHypergeometricCoefficient 1 1 2 n • (-x) ^ n = _
    rw [ordinaryHypergeometricCoefficient_eq, gaussHGCoeff_one_one_two, smul_eq_mul]
    ring
  rwa [heq] at hs

/-- AAR (2.1.3): `log(1+x) = x · ₂F₁(1,1;2;-x)` for `|x| < 1`. -/
@[dlmf 15.4.E1]
theorem log_one_add_eq_ordinaryHypergeometric {x : ℂ} (hx : ‖x‖ < 1) :
    log (1 + x) = x * ₂F₁ (1 : ℂ) 1 2 (-x) := by
  have hx' : ‖-x‖ < 1 := by simpa
  have hF := (hasSum_ordinaryHypergeometric_one_one_two hx).mul_left x
  have hlog : HasSum (fun n : ℕ => x * ((-x) ^ n / (n + 1 : ℂ))) (log (1 + x)) := by
    have h := (hasSum_taylorSeries_neg_log' hx').neg
    have heq : (fun n : ℕ => -((-x) ^ (n + 1) / (n + 1 : ℂ))) =
        fun n : ℕ => x * ((-x) ^ n / (n + 1 : ℂ)) := by
      refine funext fun (n : ℕ) => ?_
      rw [pow_succ]
      ring
    have hlog' : - -log (1 - -x) = log (1 + x) := by simp [sub_neg_eq_add]
    rw [hlog'] at h
    rwa [heq] at h
  exact hlog.unique hF

/-- Helper lemma for `ordinaryHypergeometric_eq_one_sub_neg_cpow`. -/
theorem ordinaryHypergeometricSeries_eq_binomialSeries_comp {a c : ℂ}
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c) :
    ordinaryHypergeometricSeries ℂ a c c =
      (binomialSeries ℂ (-a)).compContinuousLinearMap (-1 : ℂ →L[ℂ] ℂ) := by
  rw [binomialSeries_eq_ordinaryHypergeometricSeries (a := -a) hc,
    FormalMultilinearSeries.compContinuousLinearMap_comp]
  have hid : (-ContinuousLinearMap.id ℂ ℂ).comp (-1 : ℂ →L[ℂ] ℂ) =
      ContinuousLinearMap.id ℂ ℂ := by
    ext
    simp
  rw [neg_neg, hid, FormalMultilinearSeries.compContinuousLinearMap_id]

/-- AAR (2.1.6): `₂F₁(a,c;c;z) = (1-z)^{-a}` for `|z| < 1`. -/
@[dlmf 15.4.E6]
theorem ordinaryHypergeometric_eq_one_sub_neg_cpow {a c z : ℂ}
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c) (hz : ‖z‖ < 1) :
    ₂F₁ a c c z = (1 - z) ^ (-a) := by
  have h0 : HasFPowerSeriesOnBall (fun x : ℂ => (1 + x) ^ (-a))
      (binomialSeries ℂ (-a)) (-0) 1 := by
    simpa using one_add_cpow_hasFPowerSeriesOnBall_zero (a := -a)
  have hfps : HasFPowerSeriesOnBall (fun x : ℂ => (1 - x) ^ (-a))
      (ordinaryHypergeometricSeries ℂ a c c) 0 1 := by
    rw [ordinaryHypergeometricSeries_eq_binomialSeries_comp hc]
    simpa [Function.comp_def, sub_eq_add_neg] using
      h0.compContinuousLinearMap (u := (-1 : ℂ →L[ℂ] ℂ)) (x := (0 : ℂ))
  have hz' : z ∈ Metric.eball (0 : ℂ) 1 := mem_eball_one_of_norm_lt_one hz
  have hs : HasSum (fun n : ℕ => ordinaryHypergeometricSeries ℂ a c c n fun _ => z)
      ((1 - z) ^ (-a)) := by
    simpa using hfps.hasSum hz'
  have hmem : z ∈ Metric.eball (0 : ℂ) (ordinaryHypergeometricSeries ℂ a c c).radius :=
    Metric.eball_subset_eball hfps.r_le hz'
  exact ((ordinaryHypergeometricSeries ℂ a c c).hasSum hmem).unique hs

/-- Helper lemma for `arctan_eq_ordinaryHypergeometric`. -/
theorem poch_three_halves_eq (n : ℕ) :
    poch (3 / 2 : ℂ) n = (2 * n + 1 : ℂ) * poch (1 / 2) n := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [poch_succ, poch_succ, ih]
    push_cast
    ring

/-- Helper lemma for `arctan_eq_ordinaryHypergeometric`. -/
theorem gaussHGCoeff_half_one_three_halves (n : ℕ) :
    gaussHGCoeff (1 / 2) 1 (3 / 2) n = 1 / (2 * n + 1 : ℂ) := by
  have hne : (2 * n + 1 : ℂ) ≠ 0 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    intro h
    have : (2 * n + 1 : ℝ) = 0 := by simpa using congrArg Complex.re h
    linarith
  have hp : poch (1 / 2 : ℂ) n ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (fun k hk => by
      have : ((1 : ℝ) / 2) = -k := by simpa using congrArg Complex.re hk
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith) n
  rw [gaussHGCoeff, poch_nat_one, poch_three_halves_eq]
  field [Nat.cast_ne_zero.mpr n.factorial_ne_zero, hne, hp]

/-- Helper lemma for `arctan_eq_ordinaryHypergeometric`. -/
theorem radius_ordinaryHypergeometric_half_one_three_halves :
    (ordinaryHypergeometricSeries ℂ (1 / 2 : ℂ) 1 (3 / 2)).radius = 1 :=
  ordinaryHypergeometricSeries_radius_eq_one ℂ (1 / 2 : ℂ) 1 (3 / 2) fun kn => by
    have hk : (0 : ℝ) ≤ kn := Nat.cast_nonneg kn
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    · intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    · intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith

/-- Helper lemma for `arctan_eq_ordinaryHypergeometric`: the series of
`₂F₁(1/2,1;3/2;-x²)`. -/
theorem hasSum_ordinaryHypergeometric_half_one_three_halves {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => (-(x ^ 2)) ^ n / (2 * n + 1 : ℂ))
      (₂F₁ (1 / 2 : ℂ) 1 (3 / 2) (-(x ^ 2))) := by
  have hx2 : ‖-(x ^ 2)‖ < 1 := by
    rw [norm_neg, norm_pow]
    exact pow_lt_one₀ (norm_nonneg x) hx (by norm_num)
  have hmem : -(x ^ 2) ∈ Metric.eball (0 : ℂ)
      (ordinaryHypergeometricSeries ℂ (1 / 2 : ℂ) 1 (3 / 2)).radius := by
    rw [radius_ordinaryHypergeometric_half_one_three_halves]
    exact mem_eball_one_of_norm_lt_one hx2
  have hs := (ordinaryHypergeometricSeries ℂ (1 / 2 : ℂ) 1 (3 / 2)).hasSum hmem
  have heq :
      (fun n : ℕ => ordinaryHypergeometricSeries ℂ (1 / 2 : ℂ) 1 (3 / 2) n fun _ => -(x ^ 2)) =
        fun n : ℕ => (-(x ^ 2)) ^ n / (2 * n + 1 : ℂ) := by
    refine funext fun (n : ℕ) => ?_
    rw [ordinaryHypergeometricSeries_apply_eq]
    change ordinaryHypergeometricCoefficient (1 / 2) 1 (3 / 2) n • (-(x ^ 2)) ^ n = _
    rw [ordinaryHypergeometricCoefficient_eq, gaussHGCoeff_half_one_three_halves, smul_eq_mul]
    ring
  rwa [heq] at hs

/-- AAR (2.1.4): `arctan x = x · ₂F₁(1/2,1;3/2;-x²)` for `|x| < 1`. -/
@[dlmf 15.4.E3]
theorem arctan_eq_ordinaryHypergeometric {x : ℂ} (hx : ‖x‖ < 1) :
    arctan x = x * ₂F₁ (1 / 2 : ℂ) 1 (3 / 2) (-(x ^ 2)) := by
  have hF := (hasSum_ordinaryHypergeometric_half_one_three_halves hx).mul_left x
  have hart : HasSum (fun n : ℕ => x * ((-(x ^ 2)) ^ n / (2 * n + 1 : ℂ))) (arctan x) := by
    have h := hasSum_arctan hx
    have heq : (fun n : ℕ => (-1) ^ n * x ^ (2 * n + 1) / ↑(2 * n + 1)) =
        fun n : ℕ => x * ((-(x ^ 2)) ^ n / (2 * n + 1 : ℂ)) := by
      refine funext fun (n : ℕ) => ?_
      have hn : (-(x ^ 2)) ^ n = (-1) ^ n * x ^ (2 * n) := by
        rw [neg_pow (x ^ 2), pow_mul]
      rw [hn, pow_succ]
      push_cast
      ring
    rwa [heq] at h
  exact hart.unique hF

/-- Euler's Gamma approximants written using Pochhammer symbols. -/
theorem GammaSeq_eq_poch (s : ℂ) (n : ℕ) :
    GammaSeq s n = (n : ℂ) ^ s * n.factorial / (poch s n * (s + n)) := by
  have hp (k : ℕ) : (∏ j ∈ Finset.range k, (s + j)) = poch s k := by
    induction k with
    | zero => simp [poch_zero]
    | succ k ih => rw [Finset.prod_range_succ, ih, poch_succ]
  rw [GammaSeq, hp, poch_succ]

/-- The normalized Gauss coefficients have a finite Gamma-ratio limit. -/
theorem tendsto_gaussHGCoeff_div_cpow {a b c : ℂ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hc : ∀ k : ℕ, c ≠ -k) :
    Tendsto (fun n : ℕ => gaussHGCoeff a b c n / (n : ℂ) ^ (a + b - c - 1))
      atTop (𝓝 (Gamma c / (Gamma a * Gamma b))) := by
  have hlim (s : ℂ) : Tendsto (fun n : ℕ => 1 + s / (n : ℂ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat s).const_add 1
  have ht := ((hlim c).div ((hlim a).mul (hlim b)) (by norm_num)).mul
    ((GammaSeq_tendsto_Gamma c).div
      ((GammaSeq_tendsto_Gamma a).mul (GammaSeq_tendsto_Gamma b))
      (mul_ne_zero (Gamma_ne_zero ha) (Gamma_ne_zero hb)))
  simp only [mul_one, div_one, one_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hs (s : ℂ) (h : ∀ k : ℕ, s ≠ -k) : s + (n : ℂ) ≠ 0 := by
    simpa only [ne_eq, eq_neg_iff_add_eq_zero] using h n
  have hp (s : ℂ) : (n : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hn0)
  simp only [Pi.div_apply]
  rw [GammaSeq_eq_poch, GammaSeq_eq_poch, GammaSeq_eq_poch,
    gaussHGCoeff, cpow_sub _ _ hn0, cpow_sub _ _ hn0, cpow_add _ _ hn0, cpow_one]
  field [hn0, hs a ha, hs b hb, hs c hc,
    show (n : ℂ) + a ≠ 0 by simpa only [add_comm] using hs a ha,
    show (n : ℂ) + b ≠ 0 by simpa only [add_comm] using hs b hb, hp a, hp b, hp c,
    poch_ne_zero_of_not_neg_nat ha n, poch_ne_zero_of_not_neg_nat hb n,
    poch_ne_zero_of_not_neg_nat hc n, Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- AAR Theorem 2.1.2 (absolute convergence on the unit circle). -/
@[dlmf 15.2.i]
theorem ordinaryHypergeometric_summable_of_mem_sphere {a b c z : ℂ}
    (hz : ‖z‖ = 1) (h : 0 < (c - a - b).re) :
    Summable fun n : ℕ => gaussHGCoeff a b c n * z ^ n := by
  have hfinite (k : ℕ) (hk : a = -k ∨ b = -k ∨ c = -k) :
      Summable fun n : ℕ => gaussHGCoeff a b c n * z ^ n := by
    apply (summable_nat_add_iff (k + 1)).mp
    have he : (fun n : ℕ => gaussHGCoeff a b c (n + (k + 1)) * z ^ (n + (k + 1))) =
        fun _ => (0 : ℂ) := by
      funext n
      have hn : k < n + (k + 1) := by omega
      rcases hk with rfl | rfl | rfl <;> simp [gaussHGCoeff, poch_neg_nat_eq_zero hn]
    rw [he]
    exact summable_zero
  by_cases ha : ∀ k : ℕ, a ≠ -k
  · by_cases hb : ∀ k : ℕ, b ≠ -k
    · by_cases hc : ∀ k : ℕ, c ≠ -k
      · have ht := (tendsto_gaussHGCoeff_div_cpow ha hb hc).norm
        have hlim : Tendsto (fun n : ℕ => ‖gaussHGCoeff a b c n‖ /
            (n : ℝ) ^ (a + b - c - 1).re) atTop (𝓝 ‖Gamma c / (Gamma a * Gamma b)‖) := by
          apply ht.congr'
          filter_upwards [eventually_gt_atTop 0] with n hn
          rw [norm_div, norm_natCast_cpow_of_pos hn]
        have hs : Summable (fun n : ℕ => ‖gaussHGCoeff a b c n‖) :=
          summable_of_isBigO_nat (Real.summable_nat_rpow.mpr (by
            simp only [sub_re, add_re, one_re] at h ⊢; linarith))
            (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow hlim)
        apply Summable.of_norm
        simpa only [norm_mul, norm_pow, hz, one_pow, mul_one] using hs
      · push Not at hc
        obtain ⟨k, hk⟩ := hc
        exact hfinite k (Or.inr (Or.inr hk))
    · push Not at hb
      obtain ⟨k, hk⟩ := hb
      exact hfinite k (Or.inr (Or.inl hk))
  · push Not at ha
    obtain ⟨k, hk⟩ := ha
    exact hfinite k (Or.inl hk)

end DLMF.Hypergeometric
