/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.NumberTheory.Asymptotics.DivisorSums
public import DLMF.NumberTheory.Asymptotics.MoebiusSums

/-!
# Asymptotic formulas for arithmetic and prime sums (DLMF §27.11)

The asymptotic formulas of DLMF §27.11 for divisor and totient sums, sums of `σ_α`, sums over
primes (also in arithmetic progressions) and sums of the Möbius function. The conventions for
partial sums and error terms are described in `DLMF.NumberTheory.Asymptotics`.

## Main definitions

* `primeLogDivSum`: `P(n) = ∑_{p ≤ n} (ln p)/p`.
* `mertensBound`: the constant bounding `|∑_{p ≤ N} (ln p)/p - ln N|`.

## Main results

* `sum_sigma_zero_asymptotic`, `sum_sigma_zero_huxley`, `sum_sigma_zero_div_asymptotic`:
  Dirichlet's divisor sum DLMF 27.11.2 with Huxley's bound on its error term, and DLMF 27.11.3.
* `sum_sigma_one_asymptotic`, `sum_sigmaC_asymptotic`: the sums of `σ₁` and `σ_α`
  (DLMF 27.11.4 and 27.11.5).
* `sum_totient_asymptotic`, `sum_totient_div_asymptotic`: DLMF 27.11.6 and 27.11.7.
* `sum_prime_inv_asymptotic`, `sum_prime_inv_ap_asymptotic`: Mertens' sum of `1/p`, also over an
  arithmetic progression (DLMF 27.11.8 and 27.11.9).
* `sum_log_prime_div_asymptotic`, `sum_log_prime_div_ap_asymptotic`: the sums of `(ln p)/p`
  (DLMF 27.11.10 and 27.11.11).
* `infinite_primes_mod`: Dirichlet's theorem on primes in arithmetic progressions.
* `sum_moebius_isBigO`, `tendsto_sum_moebius_div`, `tendsto_sum_moebius_div_self`,
  `tendsto_sum_moebius_log_div`: the Möbius sums DLMF 27.11.12–27.11.15.
* `primeCounting_ap_isEquivalent`: the prime number theorem for arithmetic progressions.
-/

@[expose] public noncomputable section

open Finset Filter Asymptotics ArithmeticFunction

open scoped ArithmeticFunction.sigma ArithmeticFunction.Moebius Real

namespace DLMF.NumberTheory

section Helpers
open scoped ArithmeticFunction.zeta

/-- `∑_{n ≤ N} Λ(n)/n` as a double sum over primes and exponents (after Mathlib's
`Chebyshev.psi_eq_sum_mul_log_prime`). -/
private lemma sum_vonMangoldt_div_eq_sum_primesLE (n : ℕ) :
    ∑ m ∈ Ioc 0 n, Λ m / m =
      ∑ p ∈ Nat.primesLE n, ∑ k ∈ Icc 1 (Nat.log p n), Real.log p / (p : ℝ) ^ k := by
  have hI : Ioc 0 n = Icc 1 n := by ext; simp only [mem_Ioc, mem_Icc]; omega
  calc ∑ m ∈ Ioc 0 n, Λ m / m
    _ = ∑ m ∈ ((Icc 1 n).filter Nat.Prime).biUnion
            fun p ↦ image (p ^ ·) (Icc 1 (Nat.log p n)), Λ m / m := by
        rw [hI]
        refine (sum_subset (fun q hq ↦ ?_) fun x hx hnot ↦ ?_).symm
        · simp only [mem_biUnion, mem_filter, mem_Icc, mem_image] at hq ⊢
          obtain ⟨p, _, k, ⟨_, hk⟩, rfl⟩ := hq
          exact ⟨by grind, Nat.pow_le_of_le_log (by linarith) hk⟩
        · suffices Λ x = 0 by rw [this, zero_div]
          rw [vonMangoldt_eq_zero_iff, isPrimePow_nat_iff]
          rintro ⟨p, k, hp, hk, rfl⟩
          simp only [mem_Icc] at hx
          have hpn : p ≤ n := (Nat.le_of_dvd (by lia) (dvd_pow_self p hk.ne')).trans hx.2
          apply hnot
          simp only [mem_biUnion, mem_filter, mem_Icc, mem_image]
          exact ⟨p, ⟨⟨hp.one_le, hpn⟩, hp⟩, k, ⟨by lia, Nat.le_log_of_pow_le hp.one_lt hx.2⟩,
            rfl⟩
    _ = ∑ p ∈ Icc 1 n with p.Prime, ∑ q ∈ image (fun k ↦ p ^ k) (Icc 1 (Nat.log p n)),
            Λ q / q := by
        rw [sum_biUnion <| by rw [pairwiseDisjoint_iff]; grind [Nat.Prime.pow_inj']]
    _ = ∑ p ∈ Nat.primesLE n, ∑ k ∈ Icc 1 (Nat.log p n), Λ (p ^ k) / ((p ^ k : ℕ) : ℝ) := by
        refine sum_congr (Nat.primesLE_eq_filter_Icc_one n).symm fun p hp ↦ ?_
        exact sum_image fun a _ b _ hab ↦
          Nat.pow_right_injective (Nat.two_le_of_mem_primesLE hp) hab
    _ = _ := by
        refine sum_congr rfl fun p hp ↦ sum_congr rfl fun k hk ↦ ?_
        rw [vonMangoldt_apply_pow (by grind), vonMangoldt_apply_prime <|
          Nat.prime_of_mem_primesLE hp, Nat.cast_pow]

/-- `1/p ≤ ∑_{k=1}^K p^{-k} ≤ 1/(p-1)` for `p ≥ 2`, `K ≥ 1`. -/
private lemma sum_Icc_one_div_pow_bounds {p : ℝ} (hp : 2 ≤ p) {K : ℕ} (hK : 1 ≤ K) :
    1 / p ≤ ∑ k ∈ Icc 1 K, 1 / p ^ k ∧ ∑ k ∈ Icc 1 K, 1 / p ^ k ≤ 1 / (p - 1) := by
  have hp0 : 0 < p := by linarith
  have hr : ∀ K : ℕ, (∑ k ∈ Icc 1 K, 1 / p ^ k) * (p - 1) = 1 - 1 / p ^ K := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [sum_Icc_succ_top (by omega), add_mul, ih]
      field_simp; ring
  constructor
  · have := single_le_sum (f := fun k ↦ 1 / p ^ k) (fun k _ ↦ by positivity)
      (show 1 ∈ Icc 1 K by simp [hK])
    simpa using this
  · rw [le_div_iff₀ (by linarith), hr]
    have : 0 < 1 / p ^ K := by positivity
    linarith

/-- `∑_{n ≤ N} ln n = ln N!`. -/
private lemma sum_Ioc_log_eq_log_factorial (N : ℕ) :
    ∑ n ∈ Ioc 0 N, Real.log n = Real.log N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Ioc_succ_top (by omega), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity), add_comm]

/-- `N ln N - N ≤ ln N! ≤ N ln N`. -/
private lemma log_factorial_bounds (N : ℕ) :
    N * Real.log N - N ≤ Real.log N.factorial ∧ Real.log N.factorial ≤ N * Real.log N := by
  rw [← sum_Ioc_log_eq_log_factorial]
  constructor
  · rw [sum_Ioc_log_eq_log_factorial]
    have h := Real.pow_div_factorial_le_exp (x := (N : ℝ)) (by positivity) N
    have hf : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have := Real.log_le_log (by positivity) h
    rw [Real.log_exp, Real.log_div (by positivity) hf.ne', Real.log_pow] at this
    linarith
  · calc ∑ n ∈ Ioc 0 N, Real.log n ≤ ∑ n ∈ Ioc 0 N, Real.log N := by
          refine sum_le_sum fun n hn ↦ ?_
          obtain ⟨h1, h2⟩ := mem_Ioc.mp hn
          exact Real.log_le_log (by exact_mod_cast h1) (by exact_mod_cast h2)
      _ = N * Real.log N := by rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.sub_zero]

/-- `ln N - 1 ≤ ∑_{n ≤ N} Λ(n)/n ≤ ln N + ln 4 + 4` for `N ≥ 1`. -/
private lemma sum_vonMangoldt_div_bounds {N : ℕ} (hN : 1 ≤ N) :
    Real.log N - 1 ≤ ∑ m ∈ Ioc 0 N, Λ m / m ∧
      ∑ m ∈ Ioc 0 N, Λ m / m ≤ Real.log N + (Real.log 4 + 4) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hleg : ∑ n ∈ Ioc 0 N, Real.log n = ∑ d ∈ Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) := by
    rw [← sum_Ioc_mul_zeta_eq_sum, vonMangoldt_mul_zeta]
    rfl
  rw [sum_Ioc_log_eq_log_factorial] at hleg
  set E := ∑ d ∈ Ioc 0 N, Λ d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))
  have hE : N * ∑ m ∈ Ioc 0 N, Λ m / m - E = Real.log N.factorial := by
    rw [hleg, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun d _ ↦ ?_
    ring
  have hE0 : 0 ≤ E := sum_nonneg fun d hd ↦ by
    have := (natCast_div_le_and_lt_add_one N d (mem_Ioc.mp hd).1).1
    exact mul_nonneg vonMangoldt_nonneg (by linarith)
  have hE1 : E ≤ (Real.log 4 + 4) * N := by
    calc E ≤ ∑ d ∈ Ioc 0 N, Λ d := sum_le_sum fun d hd ↦ by
          have := (natCast_div_le_and_lt_add_one N d (mem_Ioc.mp hd).1).2
          exact mul_le_of_le_one_right vonMangoldt_nonneg (by linarith)
      _ = Chebyshev.psi N := by rw [Chebyshev.psi, Nat.floor_natCast]
      _ ≤ _ := Chebyshev.psi_le_const_mul_self (by positivity)
  obtain ⟨hf1, hf2⟩ := log_factorial_bounds N
  set A := ∑ m ∈ Ioc 0 N, Λ m / m
  have hA : A = (Real.log N.factorial + E) / N := by
    rw [eq_div_iff hN'.ne']; linarith
  rw [hA]
  constructor
  · rw [le_div_iff₀ hN']; nlinarith
  · rw [div_le_iff₀ hN']; nlinarith

/-- `0 ≤ ∑_{n ≤ N} Λ(n)/n - ∑_{p ≤ N} (ln p)/p ≤ ∑' e`. -/
private lemma sum_vonMangoldt_div_sub_sum_log_prime_div_bounds (N : ℕ) :
    0 ≤ ∑ m ∈ Ioc 0 N, Λ m / m - ∑ p ∈ Nat.primesLE N, Real.log p / p ∧
      ∑ m ∈ Ioc 0 N, Λ m / m - ∑ p ∈ Nat.primesLE N, Real.log p / p ≤
        ∑' a, logDivTelescopeError a := by
  rw [sum_vonMangoldt_div_eq_sum_primesLE, ← sum_sub_distrib]
  have hterm : ∀ p ∈ Nat.primesLE N,
      0 ≤ ∑ k ∈ Icc 1 (Nat.log p N), Real.log p / (p : ℝ) ^ k - Real.log p / p ∧
      ∑ k ∈ Icc 1 (Nat.log p N), Real.log p / (p : ℝ) ^ k - Real.log p / p ≤
        logDivTelescopeError p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hpN : p ≤ N := Nat.le_of_mem_primesLE hp
    have hK : 1 ≤ Nat.log p N := Nat.le_log_of_pow_le hpp.one_lt (by simpa using hpN)
    obtain ⟨g1, g2⟩ := sum_Icc_one_div_pow_bounds hp2 hK
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have he : ∑ k ∈ Icc 1 (Nat.log p N), Real.log p / (p : ℝ) ^ k =
        Real.log p * ∑ k ∈ Icc 1 (Nat.log p N), 1 / (p : ℝ) ^ k := by
      rw [mul_sum]; exact sum_congr rfl fun k _ ↦ by ring
    rw [he]
    constructor
    · have := mul_le_mul_of_nonneg_left g1 hl
      rw [mul_one_div] at this; linarith
    · have := mul_le_mul_of_nonneg_left g2 hl
      unfold logDivTelescopeError
      have hp1 : (0 : ℝ) < p - 1 := by linarith
      have h1 : Real.log p * (1 / ((p : ℝ) - 1)) - Real.log p / p =
          Real.log p / (p * ((p : ℝ) - 1)) := by field_simp; ring
      have h2 : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
      linarith
  constructor
  · exact sum_nonneg fun p hp ↦ (hterm p hp).1
  · calc _ ≤ ∑ p ∈ Nat.primesLE N, logDivTelescopeError p := sum_le_sum fun p hp ↦ (hterm p hp).2
      _ ≤ _ := summable_logDivTelescopeError.sum_le_tsum _ fun a _ ↦ logDivTelescopeError_nonneg a

/-- DLMF 27.11.10 (proof). -/
private lemma isBigO_sum_log_prime_div_sub_log :
    (fun x : ℝ ↦ ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x) =O[atTop]
      fun _ ↦ (1 : ℝ) := by
  refine IsBigO.of_bound (∑' a, logDivTelescopeError a + 10) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hlN : Real.log N ≤ Real.log x := Real.log_le_log (by positivity) hNx
  have hdiff : Real.log x - Real.log N ≤ 1 := by
    rw [← Real.log_div hx0.ne' (by positivity)]
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one (by positivity), div_le_one (by positivity)]
    linarith
  obtain ⟨a1, a2⟩ := sum_vonMangoldt_div_bounds hN1
  obtain ⟨b1, b2⟩ := sum_vonMangoldt_div_sub_sum_log_prime_div_bounds N
  have hl4 : Real.log 4 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    calc (4 : ℝ) < 2.7182818283 ^ 2 := by norm_num
      _ < Real.exp 1 ^ 2 := by gcongr
      _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hC0 : 0 ≤ ∑' a, logDivTelescopeError a := tsum_nonneg logDivTelescopeError_nonneg
  rw [norm_one, mul_one, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- The constant bounding `|∑_{p ≤ N} (ln p)/p - ln N|`. -/
noncomputable def mertensBound : ℝ := ∑' a, logDivTelescopeError a + 6

/-- Estimate under the stated parameter and domain assumptions: `0 ≤ mertensBound`. -/
private lemma mertensBound_nonneg : 0 ≤ mertensBound := by
  have : 0 ≤ ∑' a, logDivTelescopeError a := tsum_nonneg logDivTelescopeError_nonneg
  unfold mertensBound; linarith

/-- `|∑_{p ≤ N} (ln p)/p - ln N| ≤ C` for `N ≥ 1`. -/
private lemma abs_sum_log_prime_div_sub_log_le {N : ℕ} (hN : 1 ≤ N) :
    |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ mertensBound := by
  obtain ⟨a1, a2⟩ := sum_vonMangoldt_div_bounds hN
  obtain ⟨b1, b2⟩ := sum_vonMangoldt_div_sub_sum_log_prime_div_bounds N
  have hl4 : Real.log 4 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    calc (4 : ℝ) < 2.7182818283 ^ 2 := by norm_num
      _ < Real.exp 1 ^ 2 := by gcongr
      _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hC0 : 0 ≤ ∑' a, logDivTelescopeError a := tsum_nonneg logDivTelescopeError_nonneg
  unfold mertensBound
  rw [abs_le]
  constructor <;> linarith

/-- Sums over `primesLE` as sums over `range` with an indicator. -/
private lemma sum_primesLE_eq_sum_range_ite (h : ℕ → ℝ) (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, h p = ∑ m ∈ range (N + 1), if m.Prime then h m else 0 := by
  rw [← sum_filter]; rfl

/-- `P(n) = ∑_{p ≤ n} (ln p)/p`. -/
noncomputable def primeLogDivSum (n : ℕ) : ℝ := ∑ p ∈ Nat.primesLE n, Real.log p / p

/-- `f(n) = 1/ln n` (with `f 0 = f 1 = 0`). -/
noncomputable def invLogNat (n : ℕ) : ℝ := 1 / Real.log n

/-- Abel summation: `∑_{p ≤ N} 1/p = P(N) f(N) + ∑_{n < N} P(n) (f(n) - f(n+1))`. -/
private lemma sum_primesLE_inv_eq_abel_summation (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, (1 / p : ℝ) =
      primeLogDivSum N * invLogNat N + ∑ n ∈ range N, primeLogDivSum n *
          (invLogNat n - invLogNat (n + 1)) := by
  have hP : ∀ n, primeLogDivSum n = ∑ m ∈ range (n + 1), if m.Prime then Real.log m / m else 0 :=
    fun n ↦ sum_primesLE_eq_sum_range_ite _ n
  rw [sum_primesLE_eq_sum_range_ite]
  induction N with
  | zero => simp [hP, invLogNat]
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ _ N, hP (N + 1), sum_range_succ, ← hP N]
    have : (if (N + 1).Prime then (1 / ((N + 1 : ℕ) : ℝ)) else 0) =
        (if (N + 1).Prime then Real.log ((N + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) else 0) *
          invLogNat (N + 1) := by
      split_ifs with hp
      · have : Real.log ((N + 1 : ℕ) : ℝ) ≠ 0 := by
          have := Real.log_pos (show (1 : ℝ) < ((N + 1 : ℕ) : ℝ) by exact_mod_cast hp.one_lt)
          exact this.ne'
        simp only [invLogNat]; field_simp
      · simp
    rw [this]; ring

/-- `G(n) = P(n)(f(n) - f(n+1)) - (ln ln (n+1) - ln ln n)`. -/
noncomputable def mertensAbelError (n : ℕ) : ℝ :=
  primeLogDivSum n * (invLogNat n - invLogNat (n + 1)) -
    (Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log n))

/-- Estimate under the stated parameter and domain assumptions: `0 ≤ invLogNat n`. -/
private lemma invLogNat_nonneg (n : ℕ) : 0 ≤ invLogNat n := by
  unfold invLogNat
  have : 0 ≤ Real.log n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp
    · exact Real.log_nonneg (by exact_mod_cast h)
  positivity

/-- For `n ≥ 2`: `0 ≤ f(n) - f(n+1)` and `|G(n)| ≤ (C + 1)(f(n) - f(n+1))`. -/
private lemma abs_mertensAbelError_le {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ invLogNat n - invLogNat (n + 1) ∧
      |mertensAbelError n| ≤ (mertensBound + 1) * (invLogNat n - invLogNat (n + 1)) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set L0 := Real.log n with hL0
  set L1 := Real.log ((n + 1 : ℕ) : ℝ) with hL1
  have hc : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
  have hL0p : 0 < L0 := Real.log_pos (by linarith)
  have hL01 : L0 ≤ L1 := Real.log_le_log hn0 (by rw [hc]; linarith)
  have hL1p : 0 < L1 := lt_of_lt_of_le hL0p hL01
  have hd : L1 - L0 ≤ 1 / n := by
    rw [hL1, hL0, ← Real.log_div (by positivity) hn0.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
    rw [hc]; field_simp; ring
  have hd1 : L1 - L0 ≤ 1 := hd.trans (by rw [div_le_one hn0]; linarith)
  have hh : invLogNat n - invLogNat (n + 1) = (L1 - L0) / (L0 * L1) := by
    simp only [invLogNat]
    rw [← hL0, show Real.log ((n + 1 : ℕ) : ℝ) = L1 from rfl]
    field_simp
  have hh0 : 0 ≤ (L1 - L0) / (L0 * L1) := div_nonneg (by linarith) (by positivity)
  refine ⟨hh ▸ hh0, ?_⟩
  -- D = ln(L1/L0)
  have hD : Real.log L1 - Real.log L0 = Real.log (L1 / L0) := (Real.log_div hL1p.ne' hL0p.ne').symm
  have hDu : Real.log (L1 / L0) ≤ (L1 - L0) / L0 := by
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
    field_simp
  have hDl : (L1 - L0) / L1 ≤ Real.log (L1 / L0) := by
    have := Real.log_le_sub_one_of_pos (show 0 < L0 / L1 by positivity)
    rw [Real.log_div hL0p.ne' hL1p.ne'] at this
    rw [Real.log_div hL1p.ne' hL0p.ne']
    have he : L0 / L1 - 1 = -((L1 - L0) / L1) := by field_simp; ring
    linarith
  have hR := abs_sum_log_prime_div_sub_log_le (show 1 ≤ n by omega)
  set R := primeLogDivSum n - L0 with hRdef
  have hPe : primeLogDivSum n = L0 + R := by rw [hRdef]; ring
  have hGe : mertensAbelError n = R * ((L1 - L0) / (L0 * L1)) +
      ((L1 - L0) / L1 - Real.log (L1 / L0)) := by
    unfold mertensAbelError
    rw [hh, hPe, ← hL0, ← hD]
    have : L0 * ((L1 - L0) / (L0 * L1)) = (L1 - L0) / L1 := by field_simp
    rw [← hL1]
    linear_combination this
  have hgap : Real.log (L1 / L0) - (L1 - L0) / L1 ≤ (L1 - L0) / (L0 * L1) := by
    have : (L1 - L0) / L0 - (L1 - L0) / L1 = (L1 - L0) * ((L1 - L0) / (L0 * L1)) := by
      field_simp
    have h2 : (L1 - L0) * ((L1 - L0) / (L0 * L1)) ≤ (L1 - L0) / (L0 * L1) :=
      mul_le_of_le_one_left hh0 hd1
    linarith
  have hRb : |R * ((L1 - L0) / (L0 * L1))| ≤ mertensBound * ((L1 - L0) / (L0 * L1)) := by
    rw [abs_mul, abs_of_nonneg hh0]
    exact mul_le_mul_of_nonneg_right (by simpa [hRdef, primeLogDivSum] using hR) hh0
  rw [hGe, hh]
  rw [abs_le] at hRb ⊢
  constructor <;> nlinarith

/-- Telescoped tail bound: `∑_{i < M} |G(i + N)| ≤ (C + 1) f(N)` for `N ≥ 2`. -/
private lemma sum_abs_mertensAbelError_tail_le {N : ℕ} (hN : 2 ≤ N) (M : ℕ) :
    ∑ i ∈ range M, |mertensAbelError (i + N)| ≤ (mertensBound + 1) * invLogNat N := by
  calc ∑ i ∈ range M, |mertensAbelError (i + N)|
      ≤ ∑ i ∈ range M, (mertensBound + 1) * (invLogNat (i + N) - invLogNat (i + 1 + N)) := by
        refine sum_le_sum fun i _ ↦ ?_
        have := (abs_mertensAbelError_le (show 2 ≤ i + N by omega)).2
        rwa [show i + N + 1 = i + 1 + N by ring] at this
    _ = (mertensBound + 1) * (invLogNat N - invLogNat (M + N)) := by
        rw [← mul_sum, sum_range_sub' (fun i ↦ invLogNat (i + N)), zero_add]
    _ ≤ (mertensBound + 1) * invLogNat N := by
        have := invLogNat_nonneg (M + N)
        have := mertensBound_nonneg
        nlinarith

/-- The series with terms `mertensAbelError` is summable. -/
private lemma summable_mertensAbelError : Summable mertensAbelError := by
  rw [← summable_nat_add_iff 2]
  refine Summable.of_abs ?_
  exact summable_of_sum_range_le (fun _ ↦ abs_nonneg _) (sum_abs_mertensAbelError_tail_le le_rfl)

/-- Mertens 27.11.8 for integer `N ≥ 2`. -/
private lemma abs_sum_primesLE_inv_sub_log_log_le {N : ℕ} (hN : 2 ≤ N) :
    |∑ p ∈ Nat.primesLE N, (1 / p : ℝ) - (Real.log (Real.log N) + (1 + ∑' n, mertensAbelError n))| ≤
      (2 * mertensBound + 1) * invLogNat N := by
  have habel := sum_primesLE_inv_eq_abel_summation N
  have htel : ∑ n ∈ range N, primeLogDivSum n * (invLogNat n - invLogNat (n + 1)) =
      ∑ n ∈ range N, mertensAbelError n + Real.log (Real.log N) := by
    unfold mertensAbelError
    rw [sum_sub_distrib]
    have := sum_range_sub (fun n ↦ Real.log (Real.log n)) N
    simp only [Nat.cast_zero, Real.log_zero, sub_zero] at this
    push_cast at this ⊢
    rw [this]; ring
  have hsplit := summable_mertensAbelError.sum_add_tsum_nat_add N
  have htail : |∑' i, mertensAbelError (i + N)| ≤ (mertensBound + 1) * invLogNat N := by
    have hs : Summable fun i ↦ |mertensAbelError (i + N)| :=
      summable_of_sum_range_le (fun _ ↦ abs_nonneg _) (sum_abs_mertensAbelError_tail_le hN)
    calc |∑' i, mertensAbelError (i + N)| ≤ ∑' i, |mertensAbelError (i + N)| := by
          rw [← Real.norm_eq_abs]
          exact norm_tsum_le_tsum_norm (by simpa [Real.norm_eq_abs] using hs)
      _ ≤ _ := Real.tsum_le_of_sum_range_le (fun _ ↦ abs_nonneg _)
          (sum_abs_mertensAbelError_tail_le hN)
  have hN1 : 1 ≤ N := by omega
  have hR := abs_sum_log_prime_div_sub_log_le hN1
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hPf : primeLogDivSum N * invLogNat N = 1 + (primeLogDivSum N - Real.log N) *
      invLogNat N := by
    simp only [invLogNat]; field_simp; ring
  have hRf : |(primeLogDivSum N - Real.log N) * invLogNat N| ≤ mertensBound * invLogNat N := by
    rw [abs_mul, abs_of_nonneg (invLogNat_nonneg N)]
    exact mul_le_mul_of_nonneg_right hR (invLogNat_nonneg N)
  rw [habel, htel, hPf, ← hsplit]
  have he : 1 + (primeLogDivSum N - Real.log N) * invLogNat N + (∑ n ∈ range N, mertensAbelError n +
      Real.log (Real.log N)) - (Real.log (Real.log N) + (1 + (∑ i ∈ range N, mertensAbelError i +
        ∑' i, mertensAbelError (i + N)))) = (primeLogDivSum N - Real.log N) * invLogNat N - ∑' i,
            mertensAbelError (i + N) := by
    ring
  rw [he]
  calc _ ≤ |(primeLogDivSum N - Real.log N) * invLogNat N| + |∑' i,
         mertensAbelError (i + N)| := abs_sub _ _
    _ ≤ _ := by linarith

/-- DLMF 27.11.8 (proof). -/
private lemma exists_isBigO_sum_prime_inv_sub_log_log :
    ∃ A : ℝ, (fun x : ℝ ↦ ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 / p : ℝ) - (Real.log (Real.log x) + A))
      =O[atTop] fun x ↦ 1 / Real.log x := by
  refine ⟨1 + ∑' n, mertensAbelError n, IsBigO.of_bound (2 * (2 * mertensBound + 2)) ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hcore := abs_sum_primesLE_inv_sub_log_log_le hN2
  have hlN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlNx : Real.log N ≤ Real.log x := Real.log_le_log (by positivity) hNx
  have hlx : 0 < Real.log x := lt_of_lt_of_le hlN hlNx
  have hdiff : Real.log x - Real.log N ≤ 1 / N := by
    rw [← Real.log_div hx0.ne' (by positivity)]
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one (by positivity), div_le_div_iff_of_pos_right (by positivity)]
    linarith
  have hl2 : 1 / 2 ≤ Real.log N := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hN2'
    linarith
  have h1N : 1 / (N : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hlx2 : Real.log x ≤ 2 * Real.log N := by linarith
  -- ln ln x - ln ln N
  have hll0 : 0 ≤ Real.log (Real.log x) - Real.log (Real.log N) := by
    have := Real.log_le_log hlN hlNx; linarith
  have hll1 : Real.log (Real.log x) - Real.log (Real.log N) ≤ invLogNat N := by
    rw [← Real.log_div hlx.ne' hlN.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one hlN.ne', invLogNat, div_le_div_iff_of_pos_right hlN]
    linarith
  have hfN : invLogNat N ≤ 2 * (1 / Real.log x) := by
    rw [invLogNat, div_le_iff₀ hlN, mul_comm, ← mul_assoc, mul_one_div, mul_comm,
      le_div_iff₀ hlx]
    linarith
  have hC := mertensBound_nonneg
  have hf0 := invLogNat_nonneg N
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
  have he : ∑ p ∈ Nat.primesLE N, (1 / p : ℝ) -
      (Real.log (Real.log x) + (1 + ∑' n, mertensAbelError n)) =
      (∑ p ∈ Nat.primesLE N, (1 / p : ℝ) -
          (Real.log (Real.log N) + (1 + ∑' n, mertensAbelError n))) -
        (Real.log (Real.log x) - Real.log (Real.log N)) := by ring
  rw [he]
  calc _ ≤ |∑ p ∈ Nat.primesLE N, (1 / p : ℝ) - (Real.log (Real.log N) +
        (1 + ∑' n, mertensAbelError n))| + |Real.log (Real.log x) -
            Real.log (Real.log N)| := abs_sub _ _
    _ ≤ (2 * mertensBound + 1) * invLogNat N + invLogNat N := by
        rw [abs_of_nonneg hll0]; linarith
    _ = (2 * mertensBound + 2) * invLogNat N := by ring
    _ ≤ (2 * mertensBound + 2) * (2 * (1 / Real.log x)) :=
        mul_le_mul_of_nonneg_left hfN (by linarith)
    _ = _ := by ring

/-- Mean-value bounds for `t ↦ t^(α+1)`: `p u^α (v-u) ≤ v^p - u^p ≤ p v^α (v-u)`. -/
private lemma rpow_add_one_sub_rpow_add_one_bounds {α : ℝ} (hα : 0 < α) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) :
    (α + 1) * u ^ α * (v - u) ≤ v ^ (α + 1) - u ^ (α + 1) ∧
      v ^ (α + 1) - u ^ (α + 1) ≤ (α + 1) * v ^ α * (v - u) := by
  have hp : 1 ≤ α + 1 := by linarith
  constructor
  · rcases eq_or_lt_of_le hu with rfl | hu0
    · rw [Real.zero_rpow hα.ne', Real.zero_rpow (by linarith)]
      have : 0 ≤ v ^ (α + 1) := Real.rpow_nonneg (by linarith) _
      simpa using this
    · have hb := one_add_mul_self_le_rpow_one_add (s := v / u - 1) (by
        have : 0 ≤ v / u := div_nonneg (by linarith) hu0.le
        linarith) hp
      rw [add_sub_cancel] at hb
      have hvu : v = u * (v / u) := by field_simp
      have h1 : v ^ (α + 1) = u ^ (α + 1) * (v / u) ^ (α + 1) := by
        conv_lhs => rw [hvu]
        exact Real.mul_rpow hu0.le (div_nonneg (by linarith) hu0.le)
      have h2 : u ^ (α + 1) = u ^ α * u := by rw [Real.rpow_add hu0, Real.rpow_one]
      have hup : 0 ≤ u ^ (α + 1) := Real.rpow_nonneg hu0.le _
      have h3 : u ^ (α + 1) * (1 + (α + 1) * (v / u - 1)) =
          u ^ (α + 1) + (α + 1) * u ^ α * (v - u) := by
        rw [h2]; field_simp
      nlinarith [mul_le_mul_of_nonneg_left hb hup]
  · have hv0 : 0 < v ∨ v = 0 := by
      rcases eq_or_lt_of_le (hu.trans huv) with h | h
      · exact Or.inr h.symm
      · exact Or.inl h
    rcases hv0 with hv0 | hv0
    · have hb := one_add_mul_self_le_rpow_one_add (s := u / v - 1) (by
        have : 0 ≤ u / v := div_nonneg hu hv0.le
        linarith) hp
      rw [add_sub_cancel] at hb
      have huv' : u = v * (u / v) := by field_simp
      have h1 : u ^ (α + 1) = v ^ (α + 1) * (u / v) ^ (α + 1) := by
        conv_lhs => rw [huv']
        exact Real.mul_rpow hv0.le (div_nonneg hu hv0.le)
      have h2 : v ^ (α + 1) = v ^ α * v := by rw [Real.rpow_add hv0, Real.rpow_one]
      have hvp : 0 ≤ v ^ (α + 1) := Real.rpow_nonneg hv0.le _
      have h3 : v ^ (α + 1) * (1 + (α + 1) * (u / v - 1)) =
          v ^ (α + 1) - (α + 1) * v ^ α * (v - u) := by
        rw [h2]; field_simp; ring
      nlinarith [mul_le_mul_of_nonneg_left hb hvp]
    · have : u = 0 := le_antisymm (hv0 ▸ huv) hu
      subst this; subst hv0; simp

/-- `M^p/p ≤ ∑_{m ≤ M} m^α ≤ M^p/p + M^α`, `p = α + 1`. -/
private lemma sum_Ioc_rpow_bounds {α : ℝ} (hα : 0 < α) (M : ℕ) :
    (M : ℝ) ^ (α + 1) / (α + 1) ≤ ∑ m ∈ Ioc 0 M, (m : ℝ) ^ α ∧
      ∑ m ∈ Ioc 0 M, (m : ℝ) ^ α ≤ (M : ℝ) ^ (α + 1) / (α + 1) + (M : ℝ) ^ α := by
  have hp : 0 < α + 1 := by linarith
  induction M with
  | zero =>
    simp [Real.zero_rpow hα.ne', Real.zero_rpow hp.ne']
  | succ M ih =>
    rw [sum_Ioc_succ_top (by omega)]
    obtain ⟨h1, h2⟩ := rpow_add_one_sub_rpow_add_one_bounds hα (u := M) (v := (M + 1 : ℕ))
        (by positivity)
      (by push_cast; linarith)
    have hd : ((M + 1 : ℕ) : ℝ) - M = 1 := by push_cast; ring
    rw [hd, mul_one] at h1 h2
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · rw [div_le_iff₀ hp] at ih1 ⊢
      nlinarith
    · have : (M : ℝ) ^ (α + 1) / (α + 1) + (M : ℝ) ^ α ≤ ((M + 1 : ℕ) : ℝ) ^ (α + 1) / (α + 1) := by
        rw [div_add' _ _ _ hp.ne', div_le_div_iff_of_pos_right hp]; linarith
      linarith

/-- Integral comparison: `∑_{i < M} f(N + i + 1) ≤ N^{-a}/a` for `f(t) = (t^{a+1})⁻¹`, `a > 0`. -/
private lemma sum_range_inv_rpow_add_one_le {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 1 ≤ N) (M : ℕ) :
    ∑ i ∈ range M, (((N + (i + 1 : ℕ) : ℝ)) ^ (a + 1))⁻¹ ≤ (N : ℝ) ^ (-a) / a := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hanti : AntitoneOn (fun t : ℝ ↦ t ^ (-(a + 1))) (Set.Icc (N : ℝ) (N + M)) := by
    intro s hs t ht hst
    have hs0 : 0 < s := by linarith [hs.1]
    exact Real.rpow_le_rpow_of_nonpos hs0 hst (by linarith)
  have h := hanti.sum_le_integral
  have hint : ∫ t in (N : ℝ)..(N + M), t ^ (-(a + 1)) =
      (((N : ℝ) + M) ^ (-a) - (N : ℝ) ^ (-a)) / (-a) := by
    rw [integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
    · congr 1 <;> ring_nf
    · rw [Set.uIcc_of_le (by linarith)]
      intro h0; linarith [h0.1]
  rw [hint] at h
  calc ∑ i ∈ range M, (((N + (i + 1 : ℕ) : ℝ)) ^ (a + 1))⁻¹
      = ∑ i ∈ range M, ((N : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-(a + 1)) := by
        refine sum_congr rfl fun i _ ↦ ?_
        rw [Real.rpow_neg (by positivity)]
    _ ≤ _ := h
    _ ≤ (N : ℝ) ^ (-a) / a := by
        rw [div_neg, ← neg_div, neg_sub]
        have : 0 ≤ ((N : ℝ) + M) ^ (-a) := Real.rpow_nonneg (by positivity) _
        gcongr
        linarith

/-- `∑_{d ≤ N} d^{-a} ≤ 1 + (N^{1-a} - 1)/(1 - a)` for `a > 0`, `a ≠ 1`, `N ≥ 1`. -/
private lemma sum_Ioc_inv_rpow_le {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ a)⁻¹ ≤ 1 + ((N : ℝ) ^ (1 - a) - 1) / (1 - a) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hanti : AntitoneOn (fun t : ℝ ↦ t ^ (-a)) (Set.Icc (1 : ℝ) (1 + M)) := by
    intro s hs t ht hst
    have hs0 : 0 < s := by linarith [hs.1]
    exact Real.rpow_le_rpow_of_nonpos hs0 hst (by linarith)
  have h := hanti.sum_le_integral
  have hint : ∫ t in (1 : ℝ)..(1 + M), t ^ (-a) =
      (((M + 1 : ℕ) : ℝ) ^ (1 - a) - 1) / (1 - a) := by
    rw [integral_rpow (Or.inr ⟨fun h ↦ ha1 (by linarith), ?_⟩)]
    · push_cast
      rw [Real.one_rpow, show -a + 1 = 1 - a by ring, add_comm (1 : ℝ)]
    · rw [Set.uIcc_of_le (by linarith)]
      intro h0; linarith [h0.1]
  rw [hint] at h
  have hsplit : ∑ d ∈ Ioc 0 (M + 1), ((d : ℝ) ^ a)⁻¹ =
      1 + ∑ i ∈ range M, (1 + ((i + 1 : ℕ) : ℝ)) ^ (-a) := by
    have : Ioc 0 (M + 1) = insert 1 ((range M).map ⟨(· + 2), add_left_injective 2⟩) := by
      ext d; simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_map, Finset.mem_range,
        Function.Embedding.coeFn_mk]
      constructor
      · intro hd
        by_cases h1 : d = 1
        · exact Or.inl h1
        · exact Or.inr ⟨d - 2, by omega, by omega⟩
      · rintro (rfl | ⟨i, hi, rfl⟩) <;> omega
    rw [this, sum_insert (by simp), sum_map]
    simp only [Nat.cast_one, Real.one_rpow, inv_one, Function.Embedding.coeFn_mk]
    congr 1
    refine sum_congr rfl fun i _ ↦ ?_
    rw [Real.rpow_neg (by positivity)]
    push_cast; ring_nf
  rw [hsplit]
  linarith

/-- `∑_{n ≤ N} σ_α(n) = ∑_{d ≤ N} ∑_{m ≤ N/d} m^α` (real `α > 0`). -/
private lemma sum_sum_divisors_rpow_eq (α : ℝ) (hα : 0 < α) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, (d : ℝ) ^ α =
      ∑ d ∈ Ioc 0 N, ∑ m ∈ Ioc 0 (N / d), (m : ℝ) ^ α := by
  let g : ArithmeticFunction ℝ := ⟨fun m ↦ (m : ℝ) ^ α, by simp [Real.zero_rpow hα.ne']⟩
  have h := sum_Ioc_mul_eq_sum_sum ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) g N
  have hI : Icc 1 N = Ioc 0 N := by ext; simp only [mem_Ioc, mem_Icc]; omega
  rw [hI]
  have hl : ∀ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, (d : ℝ) ^ α =
      (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) * g) n := by
    intro n _
    rw [coe_zeta_mul_apply]; rfl
  rw [sum_congr rfl hl, h]
  refine sum_congr rfl fun d hd ↦ ?_
  have hd0 : d ≠ 0 := (mem_Ioc.mp hd).1.ne'
  simp [natCoe_apply, zeta_apply, hd0, g]

/-- One term: `|S(⌊N/d⌋) - (N/d)^p/p| ≤ (N/d)^α`. -/
private lemma abs_sum_rpow_floor_div_sub_le {α : ℝ} (hα : 0 < α) {N d : ℕ} (hd : d ∈ Ioc 0 N) :
    |∑ m ∈ Ioc 0 (N / d), (m : ℝ) ^ α - (N : ℝ) ^ (α + 1) / (α + 1) * ((d : ℝ) ^ (α + 1))⁻¹|
      ≤ (N : ℝ) ^ α * ((d : ℝ) ^ α)⁻¹ := by
  obtain ⟨hd0, hdN⟩ := mem_Ioc.mp hd
  have hp : 0 < α + 1 := by linarith
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
  set y : ℝ := (N : ℝ) / d
  obtain ⟨hM1, hM2⟩ := natCast_div_le_and_lt_add_one N d hd0
  set M := N / d
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hy1 : M ≤ y := hM1
  obtain ⟨s1, s2⟩ := sum_Ioc_rpow_bounds hα M
  obtain ⟨-, m2⟩ := rpow_add_one_sub_rpow_add_one_bounds hα hM0 hy1
  have hyM : y - M ≤ 1 := by linarith
  have hya : 0 ≤ y ^ α := Real.rpow_nonneg (by positivity) _
  have hMa : (M : ℝ) ^ α ≤ y ^ α := Real.rpow_le_rpow hM0 hy1 hα.le
  have hMp : (M : ℝ) ^ (α + 1) ≤ y ^ (α + 1) := Real.rpow_le_rpow hM0 hy1 hp.le
  have hyp : y ^ (α + 1) = (N : ℝ) ^ (α + 1) * ((d : ℝ) ^ (α + 1))⁻¹ := by
    rw [Real.div_rpow (by positivity) hdr.le, div_eq_mul_inv]
  have hyα : y ^ α = (N : ℝ) ^ α * ((d : ℝ) ^ α)⁻¹ := by
    rw [Real.div_rpow (by positivity) hdr.le, div_eq_mul_inv]
  rw [← hyα, mul_comm ((N : ℝ) ^ (α + 1) / (α + 1)), ← mul_div_assoc,
    mul_comm _ ((N : ℝ) ^ (α + 1)), ← hyp]
  have h3 : y ^ (α + 1) - (M : ℝ) ^ (α + 1) ≤ (α + 1) * y ^ α := by
    calc _ ≤ (α + 1) * y ^ α * (y - M) := m2
      _ ≤ (α + 1) * y ^ α * 1 := by gcongr
      _ = _ := by ring
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, ← sub_eq_neg_add, sub_le_iff_le_add]
    have : y ^ (α + 1) / (α + 1) ≤ (M : ℝ) ^ (α + 1) / (α + 1) + y ^ α := by
      rw [div_add' _ _ _ hp.ne', div_le_div_iff_of_pos_right hp]; linarith
    linarith
  · have : (M : ℝ) ^ (α + 1) / (α + 1) ≤ y ^ (α + 1) / (α + 1) := by gcongr
    linarith

/-- `Z = ∑ 1/d^p`. -/
noncomputable def realZetaSucc (α : ℝ) : ℝ := ∑' d : ℕ, ((d : ℝ) ^ (α + 1))⁻¹

/-- `0 ≤ Z - ∑_{d ≤ N} d^{-p} ≤ N^{-α}/α`. -/
private lemma realZetaSucc_sub_sum_bounds {α : ℝ} (hα : 0 < α) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ realZetaSucc α - ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ (α + 1))⁻¹ ∧
      realZetaSucc α - ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ (α + 1))⁻¹ ≤ (N : ℝ) ^ (-α) / α := by
  have hs : Summable fun d : ℕ ↦ ((d : ℝ) ^ (α + 1))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  have hsplit := hs.sum_add_tsum_nat_add (N + 1)
  have hr : ∑ d ∈ range (N + 1), ((d : ℝ) ^ (α + 1))⁻¹ = ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ (α + 1))⁻¹ := by
    rw [range_succ_eq_insert_Ioc, sum_insert (by simp)]
    simp [Real.zero_rpow (show α + 1 ≠ 0 by linarith)]
  rw [hr] at hsplit
  have he : realZetaSucc α - ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ (α + 1))⁻¹ =
      ∑' i, (((i + (N + 1) : ℕ) : ℝ) ^ (α + 1))⁻¹ := by
    rw [realZetaSucc, ← hsplit, add_sub_cancel_left]
  rw [he]
  constructor
  · exact tsum_nonneg fun i ↦ by positivity
  · refine Real.tsum_le_of_sum_range_le (fun i ↦ by positivity) fun M ↦ ?_
    have := sum_range_inv_rpow_add_one_le hα hN M
    convert this using 3 with i
    push_cast; ring_nf

/-- 27.11.5 for integer `N`: `|∑_{n ≤ N} σ_α(n) - Z N^p/p| ≤ N/(pα) + N^α ∑_{d ≤ N} d^{-α}`. -/
private lemma abs_sum_sum_divisors_rpow_sub_le {α : ℝ} (hα : 0 < α) {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, (d : ℝ) ^ α - realZetaSucc α * (N : ℝ) ^ (α + 1) / (α + 1)| ≤
      N / ((α + 1) * α) + (N : ℝ) ^ α * ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ α)⁻¹ := by
  have hp : 0 < α + 1 := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [sum_sum_divisors_rpow_eq α hα]
  set A := ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ (α + 1))⁻¹
  have he : ∑ d ∈ Ioc 0 N, ∑ m ∈ Ioc 0 (N / d), (m : ℝ) ^ α - realZetaSucc α * (N : ℝ) ^ (α + 1) /
      (α + 1) = ∑ d ∈ Ioc 0 N, (∑ m ∈ Ioc 0 (N / d), (m : ℝ) ^ α -
        (N : ℝ) ^ (α + 1) / (α + 1) * ((d : ℝ) ^ (α + 1))⁻¹) -
        (N : ℝ) ^ (α + 1) / (α + 1) * (realZetaSucc α - A) := by
    rw [sum_sub_distrib, ← mul_sum]; ring
  rw [he]
  have h1 : |∑ d ∈ Ioc 0 N, (∑ m ∈ Ioc 0 (N / d), (m : ℝ) ^ α -
      (N : ℝ) ^ (α + 1) / (α + 1) * ((d : ℝ) ^ (α + 1))⁻¹)| ≤
      (N : ℝ) ^ α * ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ α)⁻¹ := by
    rw [mul_sum]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd ↦ abs_sum_rpow_floor_div_sub_le hα hd)
  obtain ⟨t0, t1⟩ := realZetaSucc_sub_sum_bounds hα hN
  have hNp : 0 ≤ (N : ℝ) ^ (α + 1) / (α + 1) := by positivity
  have hNN : (N : ℝ) ^ (α + 1) * (N : ℝ) ^ (-α) = N := by
    rw [← Real.rpow_add hN0]; simp
  have h2 : (N : ℝ) ^ (α + 1) / (α + 1) * (realZetaSucc α - A) ≤ N / ((α + 1) * α) := by
    calc _ ≤ (N : ℝ) ^ (α + 1) / (α + 1) * ((N : ℝ) ^ (-α) / α) :=
          mul_le_mul_of_nonneg_left t1 hNp
      _ = (N : ℝ) ^ (α + 1) * (N : ℝ) ^ (-α) / ((α + 1) * α) := by field_simp
      _ = _ := by rw [hNN]
  have h3 : 0 ≤ (N : ℝ) ^ (α + 1) / (α + 1) * (realZetaSucc α - A) := mul_nonneg hNp t0
  calc _ ≤ |∑ d ∈ Ioc 0 N, (∑ m ∈ Ioc 0 (N / d), (m : ℝ) ^ α -
        (N : ℝ) ^ (α + 1) / (α + 1) * ((d : ℝ) ^ (α + 1))⁻¹)| +
        |(N : ℝ) ^ (α + 1) / (α + 1) * (realZetaSucc α - A)| := abs_sub _ _
    _ ≤ _ := by rw [abs_of_nonneg h3]; linarith

/-- The integer bound of 27.11.5 is `O(N^β)`, `β = max(1, α)`. -/
private lemma exists_abs_sum_sum_divisors_rpow_sub_le {α : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, (d : ℝ) ^ α - realZetaSucc α *
          (N : ℝ) ^ (α + 1) / (α + 1)| ≤
        K * (N : ℝ) ^ max 1 α := by
  have hp : 0 < α + 1 := by linarith
  refine ⟨1 / ((α + 1) * α) + 1 + 1 / |1 - α|, by positivity, fun N hN ↦ ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hb := abs_sum_sum_divisors_rpow_sub_le hα hN
  have hs := sum_Ioc_inv_rpow_le hα hα1 hN
  have hNa : 0 ≤ (N : ℝ) ^ α := by positivity
  refine hb.trans ?_
  have hab : 0 < |1 - α| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hα1))
  rcases lt_or_gt_of_ne hα1 with h | h
  · -- `α < 1`, `β = 1`
    rw [max_eq_left h.le, Real.rpow_one, abs_of_pos (by linarith)]
    have hNaN : (N : ℝ) ^ α ≤ N := by
      calc (N : ℝ) ^ α ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 h.le
        _ = N := Real.rpow_one _
    have hpow : (N : ℝ) ^ α * (N : ℝ) ^ (1 - α) = N := by
      rw [← Real.rpow_add hN0]; simp
    have h1a : 0 < 1 - α := by linarith
    have hI : (N : ℝ) ^ α * (((N : ℝ) ^ (1 - α) - 1) / (1 - α)) ≤ N / (1 - α) := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right h1a, mul_sub, hpow]
      linarith
    calc (N : ℝ) / ((α + 1) * α) + (N : ℝ) ^ α * ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ α)⁻¹
        ≤ N / ((α + 1) * α) + (N : ℝ) ^ α * (1 + ((N : ℝ) ^ (1 - α) - 1) / (1 - α)) := by
          gcongr
      _ = N / ((α + 1) * α) + (N : ℝ) ^ α + (N : ℝ) ^ α * (((N : ℝ) ^ (1 - α) - 1) / (1 - α)) := by
          ring
      _ ≤ N / ((α + 1) * α) + N + N / (1 - α) := by linarith
      _ = _ := by ring
  · -- `α > 1`, `β = α`
    rw [max_eq_right h.le, abs_of_neg (by linarith)]
    have hNN : (N : ℝ) ≤ (N : ℝ) ^ α := by
      calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (N : ℝ) ^ α := Real.rpow_le_rpow_of_exponent_le hN1 h.le
    have hI : ((N : ℝ) ^ (1 - α) - 1) / (1 - α) ≤ 1 / -(1 - α) := by
      have : 0 ≤ (N : ℝ) ^ (1 - α) := by positivity
      have e1 : ((N : ℝ) ^ (1 - α) - 1) / (1 - α) = (1 - (N : ℝ) ^ (1 - α)) / (α - 1) := by
        rw [div_eq_div_iff (by linarith) (by linarith)]; ring
      rw [e1, neg_sub, div_le_div_iff_of_pos_right (by linarith)]
      linarith
    calc (N : ℝ) / ((α + 1) * α) + (N : ℝ) ^ α * ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ α)⁻¹
        ≤ (N : ℝ) ^ α / ((α + 1) * α) + (N : ℝ) ^ α * (1 + 1 / -(1 - α)) := by
          gcongr
          linarith
      _ = _ := by ring

/-- Estimate under the stated parameter and domain assumptions: `0 ≤ realZetaSucc α`. -/
private lemma realZetaSucc_nonneg (α : ℝ) : 0 ≤ realZetaSucc α := tsum_nonneg fun d ↦ by positivity

/-- `ζ(α + 1) = Z` for real `α > 0`. -/
private lemma riemannZeta_add_one_eq_realZetaSucc {α : ℝ} (hα : 0 < α) :
    riemannZeta ((α : ℂ) + 1) = (realZetaSucc α : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by simp; linarith), realZetaSucc, Complex.ofReal_tsum]
  refine tsum_congr fun n ↦ ?_
  rw [Complex.ofReal_inv, Complex.ofReal_cpow (by positivity), one_div]
  push_cast; rfl

/-- `σ_α(n)` for real `α` is the real divisor sum. -/
private lemma sigmaC_ofReal (α : ℝ) (n : ℕ) :
    sigmaC α n = ((∑ d ∈ n.divisors, (d : ℝ) ^ α : ℝ) : ℂ) := by
  rw [sigmaC_apply, Complex.ofReal_sum]
  refine sum_congr rfl fun d _ ↦ ?_
  rw [Complex.ofReal_cpow (by positivity)]
  rfl

/-- DLMF 27.11.5 (proof). -/
private lemma hasPartialSumAsymptotic_sigmaC {α : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) :
    HasPartialSumAsymptotic (fun n ↦ sigmaC α n)
      (fun x ↦ riemannZeta (α + 1) / (α + 1) * ((x ^ (α + 1) : ℝ) : ℂ))
      (fun x ↦ ((x ^ max 1 α : ℝ) : ℂ)) := by
  unfold HasPartialSumAsymptotic
  obtain ⟨K, hK0, hK⟩ := exists_abs_sum_sum_divisors_rpow_sub_le hα hα1
  have hp : 0 < α + 1 := by linarith
  have he : (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, sigmaC α n -
      riemannZeta (α + 1) / (α + 1) * ((x ^ (α + 1) : ℝ) : ℂ)) =
      fun x ↦ ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ d ∈ n.divisors, (d : ℝ) ^ α -
        realZetaSucc α * x ^ (α + 1) / (α + 1) : ℝ) : ℂ) := by
    funext x
    simp only [sigmaC_ofReal, riemannZeta_add_one_eq_realZetaSucc hα]
    push_cast; ring
  rw [he]
  refine isBigO_ofReal_of_abs_le (K + realZetaSucc α) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hcore := hK N hN1
  obtain ⟨-, m2⟩ := rpow_add_one_sub_rpow_add_one_bounds hα (u := N) (v := x) (by positivity) hNx
  obtain ⟨m1, -⟩ := rpow_add_one_sub_rpow_add_one_bounds hα (u := N) (v := x) (by positivity) hNx
  have hβ : 0 ≤ max 1 α := le_max_of_le_left zero_le_one
  have hxβ : 0 ≤ x ^ max 1 α := by positivity
  rw [abs_of_nonneg hxβ]
  have hNβ : (N : ℝ) ^ max 1 α ≤ x ^ max 1 α := Real.rpow_le_rpow (by positivity) hNx hβ
  have hxα : x ^ α ≤ x ^ max 1 α := Real.rpow_le_rpow_of_exponent_le hx (le_max_right _ _)
  have hZ := realZetaSucc_nonneg α
  have hxa0 : 0 ≤ x ^ α := by positivity
  have hd : x ^ (α + 1) - (N : ℝ) ^ (α + 1) ≤ (α + 1) * x ^ α := by
    calc _ ≤ (α + 1) * x ^ α * (x - N) := m2
      _ ≤ (α + 1) * x ^ α * 1 := by gcongr; linarith
      _ = _ := by ring
  have hd0 : 0 ≤ x ^ (α + 1) - (N : ℝ) ^ (α + 1) := by
    have : 0 ≤ (α + 1) * (N : ℝ) ^ α * (x - N) := by
      have : 0 ≤ x - N := by linarith
      positivity
    linarith
  have hZd : realZetaSucc α * (x ^ (α + 1) - (N : ℝ) ^ (α + 1)) / (α + 1) ≤ realZetaSucc α *
      x ^ max 1 α := by
    rw [div_le_iff₀ hp]
    calc realZetaSucc α * (x ^ (α + 1) - (N : ℝ) ^ (α + 1)) ≤ realZetaSucc α * ((α + 1) * x ^ α) :=
          mul_le_mul_of_nonneg_left hd hZ
      _ ≤ realZetaSucc α * ((α + 1) * x ^ max 1 α) := by gcongr
      _ = _ := by ring
  have hZd0 : 0 ≤ realZetaSucc α * (x ^ (α + 1) - (N : ℝ) ^ (α + 1)) / (α + 1) := by positivity
  have he2 : ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, (d : ℝ) ^ α - realZetaSucc α *
      x ^ (α + 1) / (α + 1)
      = (∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, (d : ℝ) ^ α -
        realZetaSucc α * (N : ℝ) ^ (α + 1) / (α + 1)) -
        realZetaSucc α * (x ^ (α + 1) - (N : ℝ) ^ (α + 1)) / (α + 1) := by ring
  rw [he2]
  have hKN : K * (N : ℝ) ^ max 1 α ≤ K * x ^ max 1 α := mul_le_mul_of_nonneg_left hNβ hK0
  calc _ ≤ |∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, (d : ℝ) ^ α -
        realZetaSucc α * (N : ℝ) ^ (α + 1) / (α + 1)| +
        |realZetaSucc α * (x ^ (α + 1) - (N : ℝ) ^ (α + 1)) / (α + 1)| := abs_sub _ _
    _ ≤ K * x ^ max 1 α + realZetaSucc α * x ^ max 1 α := by
        rw [abs_of_nonneg hZd0]; linarith
    _ = _ := by ring

end Helpers
/-- DLMF 27.11.2 (Dirichlet): `∑_{n≤x} d(n) = x ln x + (2γ - 1)x + O(√x)`. -/
@[dlmf 27.11.E2]
theorem sum_sigma_zero_asymptotic :
    HasPartialSumAsymptotic (fun n ↦ (σ 0 n : ℂ))
      (fun x ↦ (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x : ℝ))
      (fun x ↦ (Real.sqrt x : ℂ)) :=
  hasPartialSumAsymptotic_sigma_zero

/-- §27.11 after 27.11.2, Huxley's bound in Dirichlet's divisor problem: the error term in
27.11.2 is `O(x^θ)` for every `θ > 131/416`. -/
@[dlmf 27.11]
theorem sum_sigma_zero_huxley {θ : ℝ} (hθ : 131 / 416 < θ) :
    HasPartialSumAsymptotic (fun n ↦ (σ 0 n : ℂ))
      (fun x ↦ (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x : ℝ))
      (fun x ↦ ((x ^ θ : ℝ) : ℂ)) := by
  sorry

/-- DLMF 27.11.3: `∑_{n≤x} d(n)/n = ½(ln x)² + 2γ ln x + O(1)`. -/
@[dlmf 27.11.E3]
theorem sum_sigma_zero_div_asymptotic :
    HasPartialSumAsymptotic (fun n ↦ (σ 0 n : ℂ) / n)
      (fun x ↦ (Real.log x ^ 2 / 2 + 2 * Real.eulerMascheroniConstant * Real.log x : ℝ))
      (fun _ ↦ (1 : ℂ)) :=
  hasPartialSumAsymptotic_sigma_zero_div

/-- DLMF 27.11.4: `∑_{n≤x} σ₁(n) = (π²/12) x² + O(x ln x)`. -/
@[dlmf 27.11.E4]
theorem sum_sigma_one_asymptotic :
    HasPartialSumAsymptotic (fun n ↦ (σ 1 n : ℂ)) (fun x ↦ (π ^ 2 / 12 * x ^ 2 : ℝ))
      (fun x ↦ (x * Real.log x : ℝ)) :=
  hasPartialSumAsymptotic_sigma_one

/-- DLMF 27.11.5: `∑_{n≤x} σ_α(n) = ζ(α + 1)/(α + 1) x^{α+1} + O(x^β)`, `α > 0`, `α ≠ 1`,
`β = max(1, α)`. -/
@[dlmf 27.11.E5]
theorem sum_sigmaC_asymptotic {α : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) :
    HasPartialSumAsymptotic (fun n ↦ sigmaC α n)
      (fun x ↦ riemannZeta (α + 1) / (α + 1) * ((x ^ (α + 1) : ℝ) : ℂ))
      (fun x ↦ ((x ^ max 1 α : ℝ) : ℂ)) :=
  hasPartialSumAsymptotic_sigmaC hα hα1

/-- DLMF 27.11.6: `∑_{n≤x} φ(n) = (3/π²) x² + O(x ln x)`. -/
@[dlmf 27.11.E6]
theorem sum_totient_asymptotic :
    HasPartialSumAsymptotic (fun n ↦ (n.totient : ℂ)) (fun x ↦ (3 / π ^ 2 * x ^ 2 : ℝ))
      (fun x ↦ (x * Real.log x : ℝ)) :=
  hasPartialSumAsymptotic_totient

/-- DLMF 27.11.7: `∑_{n≤x} φ(n)/n = (6/π²) x + O(ln x)`. -/
@[dlmf 27.11.E7]
theorem sum_totient_div_asymptotic :
    HasPartialSumAsymptotic (fun n ↦ (n.totient : ℂ) / n) (fun x ↦ (6 / π ^ 2 * x : ℝ))
      (fun x ↦ (Real.log x : ℂ)) :=
  hasPartialSumAsymptotic_totient_div

/-- DLMF 27.11.8 (Mertens): there is a constant `A` with
`∑_{p≤x} 1/p = ln ln x + A + O(1/ln x)`. -/
@[dlmf 27.11.E8]
theorem sum_prime_inv_asymptotic :
    ∃ A : ℝ, (fun x : ℝ ↦ ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 / p : ℝ) - (Real.log (Real.log x) + A))
      =O[atTop] fun x ↦ 1 / Real.log x :=
  exists_isBigO_sum_prime_inv_sub_log_log

/-- DLMF 27.11.9: for `(h, k) = 1`, `k > 0`, there is a constant `B` (depending on `h, k`) with
`∑_{p≤x, p≡h (mod k)} 1/p = (1/φ(k)) ln ln x + B + O(1/ln x)`. -/
@[dlmf 27.11.E9]
theorem sum_prime_inv_ap_asymptotic {h k : ℕ} (hk : 0 < k) (hhk : h.Coprime k) :
    ∃ B : ℝ, (fun x : ℝ ↦ ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ p ≡ h [MOD k]), (1 / p : ℝ)
      - (Real.log (Real.log x) / k.totient + B)) =O[atTop] fun x ↦ 1 / Real.log x := by
  sorry

/-- DLMF 27.11.10 (Mertens): `∑_{p≤x} (ln p)/p = ln x + O(1)`. -/
@[dlmf 27.11.E10]
theorem sum_log_prime_div_asymptotic :
    (fun x : ℝ ↦ ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x) =O[atTop]
      fun _ ↦ (1 : ℝ) :=
  isBigO_sum_log_prime_div_sub_log

/-- DLMF 27.11.11: for `(h, k) = 1`, `k > 0`,
`∑_{p≤x, p≡h (mod k)} (ln p)/p = (1/φ(k)) ln x + O(1)`. -/
@[dlmf 27.11.E11]
theorem sum_log_prime_div_ap_asymptotic {h k : ℕ} (hk : 0 < k) (hhk : h.Coprime k) :
    (fun x : ℝ ↦ ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ p ≡ h [MOD k]), Real.log p / p
      - Real.log x / k.totient) =O[atTop] fun _ ↦ (1 : ℝ) := by
  sorry

/-- §27.11 after 27.11.11 and §27.12 (Prime Number Theorem paragraph): Dirichlet's theorem,
there are infinitely many primes `p ≡ h (mod k)` when `(h, k) = 1`. -/
@[dlmf 27.11, dlmf 27.12]
theorem infinite_primes_mod {h k : ℕ} (hk : 0 < k) (hhk : h.Coprime k) :
    {p : ℕ | p.Prime ∧ p ≡ h [MOD k]}.Infinite :=
  Nat.infinite_setOfPred_prime_and_modEq hk.ne' hhk

/-- DLMF 27.11.12: for some constant `C > 0`, `∑_{n≤x} μ(n) = O(x e^{-C√(ln x)})`. -/
@[dlmf 27.11.E12]
theorem sum_moebius_isBigO :
    ∃ C : ℝ, 0 < C ∧ (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ))) =O[atTop]
      fun x ↦ x * Real.exp (-C * Real.sqrt (Real.log x)) := by
  sorry

/-- DLMF 27.11.13: `lim_{x→∞} x⁻¹ ∑_{n≤x} μ(n) = 0` (equivalent to the prime number
theorem). -/
@[dlmf 27.11.E13]
theorem tendsto_sum_moebius_div :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ)) / x) atTop (nhds 0) := by
  have h1 := (isLittleO_sum_moebius.tendsto_div_nhds_zero).comp
    (tendsto_nat_floor_atTop (α := ℝ))
  have h2 := h1.mul (tendsto_nat_floor_div_atTop (R := ℝ))
  rw [zero_mul] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hN : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast Nat.floor_pos.mpr hx
  have hI : Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ := by ext; simp only [mem_Icc, mem_Ioc]; omega
  simp only [Function.comp_apply, hI]
  field_simp

/-- DLMF 27.11.14: `lim_{x→∞} ∑_{n≤x} μ(n)/n = 0`. -/
@[dlmf 27.11.E14]
theorem tendsto_sum_moebius_div_self :
    Tendsto (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) / n) atTop (nhds 0) := by
  refine (tendsto_sum_moebius_div_self_nat.comp (tendsto_nat_floor_atTop (α := ℝ))).congr
    fun x ↦ ?_
  have hI : Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ := by ext; simp only [mem_Icc, mem_Ioc]; omega
  simp only [Function.comp_apply, hI]

/-- DLMF 27.11.15: `lim_{x→∞} ∑_{n≤x} μ(n) ln n / n = -1`. -/
@[dlmf 27.11.E15]
theorem tendsto_sum_moebius_log_div :
    Tendsto (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ) * Real.log n / n) atTop
      (nhds (-1)) := by
  sorry

/-- §27.11 after 27.11.15, the prime number theorem for arithmetic progressions: for
`(h, k) = 1`, `k > 0`, the number of primes `p ≤ x` with `p ≡ h (mod k)` is asymptotic to
`x/(φ(k) ln x)`. -/
@[dlmf 27.11]
theorem primeCounting_ap_isEquivalent {h k : ℕ} (hk : 0 < k) (hhk : h.Coprime k) :
    (fun x : ℝ ↦ (((Nat.primesLE ⌊x⌋₊).filter (fun p ↦ p ≡ h [MOD k])).card : ℝ)) ~[atTop]
      fun x ↦ x / (k.totient * Real.log x) :=
  -- TauCeti's natural-density Chebotarev theorem for `ℚ(ζ_k)`, via
  -- `DLMFMathlib.NumberTheory.PrimeNumberTheorem`
  Nat.card_primesLE_modEq_isEquivalent hk hhk

end DLMF.NumberTheory

end
