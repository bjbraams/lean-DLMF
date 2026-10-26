/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.NumberTheory.Functions
public import DLMF.ExpIntegrals.Basic
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.CarmichaelNumber
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Asymptotic formulas: primes (DLMF §27.12)

`p_n` is `nthPrime n` (`p₁ = 2`), `π(x)` is `primePi x`, and the logarithmic integral `li(x)`
(DLMF 6.2.8) is the project's `DLMF.Confluent.Real.logIntLi` (a principal value at `t = 1`).
Statements equivalent to or conditional on the Riemann hypothesis use Mathlib's
`RiemannHypothesis`.

**Correction (27.12.3).** Legendre's formula as printed,
`π(x) = ⌊x⌋ - 1 - ∑_{p_j ≤ √x} ⌊x/p_j⌋ + ∑_{r≥2} (-1)^r ∑ ⌊x/(p_{j_1}⋯p_{j_r})⌋`,
gives `π(x) - π(√x)`, not `π(x)`: at `x = 10` the right-hand side is
`10 - 1 - (5 + 3) + 1 = 2`, whereas `π(10) = 4`. The sum counts the integers in `(1, x]`
free of the primes `≤ √x`, which are the primes in `(√x, x]`. The corrected form
`π(x) = π(√x) - 1 + ∑_{d ∣ P} μ(d) ⌊x/d⌋`, `P = ∏_{p ≤ √x} p`, is acquired
(`primePi_legendre`); checked numerically for `x = 1, 2, 3, 10, 30, 57.5, 100, 200`.
-/

@[expose] public noncomputable section

open Finset Filter Asymptotics ArithmeticFunction
open scoped Real

namespace DLMF.NumberTheory

/-- The logarithmic integral `li(x)` (DLMF 6.2.8), the project's `DLMF.Confluent.Real.logIntLi`. -/
abbrev li (x : ℝ) : ℝ := DLMF.Confluent.Real.logIntLi x

/-- DLMF 27.12.1: `lim_{n→∞} p_n/(n ln n) = 1`. -/
@[dlmf 27.12.E1]
theorem tendsto_nthPrime_div :
    Tendsto (fun n : ℕ ↦ (nthPrime n : ℝ) / (n * Real.log n)) atTop (nhds 1) := by
  have h := nthPrime_isEquivalent.div (IsEquivalent.refl (u := fun n : ℕ ↦ (n : ℝ) * Real.log n))
  have h1 : Tendsto ((fun n : ℕ ↦ (n : ℝ) * Real.log n) / fun n : ℕ ↦ (n : ℝ) * Real.log n)
      atTop (nhds 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 < Real.log n := Real.log_pos (by linarith)
    rw [Pi.div_apply, div_self (by positivity)]
  exact h.symm.tendsto_nhds h1

/-- DLMF 27.12.2 (Rosser): `p_n > n ln n`, `n = 1, 2, …`. -/
@[dlmf 27.12.E2]
theorem nthPrime_gt {n : ℕ} (hn : 0 < n) : (n : ℝ) * Real.log n < nthPrime n := by
  sorry

/-- Inclusion–exclusion (sieve of Eratosthenes): the number of `1 ≤ n ≤ N` divisible by no
prime of a set `T` of primes is `∑_{S ⊆ T} (-1)^{|S|} ⌊N/∏S⌋`. -/
theorem r27_sieve_card (N : ℕ) (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    ((Ioc 0 N).filter (fun n ↦ ∀ p ∈ T, ¬ p ∣ n)).card =
      ∑ S ∈ T.powerset, (-1 : ℤ) ^ S.card * ((N / ∏ p ∈ S, p : ℕ) : ℤ) := by
  have hdvd : ∀ S ∈ T.powerset, ∀ n, (∏ p ∈ S, p) ∣ n ↔ ∀ p ∈ S, p ∣ n := by
    intro S hS n
    refine ⟨fun h p hp ↦ (dvd_prod_of_mem _ hp).trans h, fun h ↦ ?_⟩
    exact Finset.prod_primes_dvd n (fun p hp ↦ (hT p (mem_powerset.mp hS hp)).prime) h
  have h1 : ∀ S ∈ T.powerset, ((N / ∏ p ∈ S, p : ℕ) : ℤ) =
      ∑ n ∈ Ioc 0 N, if ∀ p ∈ S, p ∣ n then (1 : ℤ) else 0 := by
    intro S hS
    rw [← Nat.Ioc_filter_dvd_card_eq_div, sum_boole]
    congr 2
    ext n; simp only [mem_filter]; rw [hdvd S hS]
  rw [sum_congr rfl fun S hS ↦ by rw [h1 S hS, mul_sum], sum_comm, ← sum_boole]
  refine sum_congr rfl fun n _ ↦ ?_
  have hU : T.powerset.filter (fun S ↦ ∀ p ∈ S, p ∣ n) = (T.filter (· ∣ n)).powerset := by
    ext S
    simp only [mem_filter, mem_powerset, subset_iff]
    constructor
    · rintro ⟨h1, h2⟩ p hp; exact ⟨h1 hp, h2 p hp⟩
    · intro h; exact ⟨fun p hp ↦ (h hp).1, fun p hp ↦ (h hp).2⟩
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← sum_filter, hU, sum_powerset_neg_one_pow_card]
  congr 1
  simp only [filter_eq_empty_iff]

/-- DLMF 27.12.3, Legendre's formula, in the corrected form (see the module docstring):
`π(x) = π(√x) - 1 + ∑_{S} (-1)^{|S|} ⌊x/∏S⌋`, the sum over all sets `S` of primes `≤ √x`, for
`x ≥ 1`. -/
@[dlmf 27.12.E3]
theorem primePi_legendre {x : ℝ} (hx : 1 ≤ x) :
    (primePi x : ℤ) = primePi (Real.sqrt x) - 1 +
      ∑ S ∈ (Nat.primesLE ⌊Real.sqrt x⌋₊).powerset, (-1) ^ S.card * ⌊x / ∏ p ∈ S, (p : ℝ)⌋ := by
  set N := ⌊x⌋₊ with hN
  set y := ⌊Real.sqrt x⌋₊ with hy
  set T := Nat.primesLE y
  have hT : ∀ p ∈ T, p.Prime := fun p hp ↦ Nat.prime_of_mem_primesLE hp
  have hx0 : 0 ≤ x := by linarith
  have hsx : Real.sqrt x ≤ x := Real.sqrt_le_iff.mpr ⟨hx0, by nlinarith⟩
  have hyN : y ≤ N := Nat.floor_le_floor hsx
  have hfl : ∀ S ∈ T.powerset, ⌊x / ∏ p ∈ S, (p : ℝ)⌋ = ((N / ∏ p ∈ S, p : ℕ) : ℤ) := by
    intro S _
    rw [← Nat.cast_prod, Int.floor_div_natCast, ← Int.natCast_floor_eq_floor hx0, Int.natCast_div]
  rw [sum_congr rfl fun S hS ↦ by rw [hfl S hS], ← r27_sieve_card N T hT]
  -- the sieved set is `{1} ∪ {primes in (y, N]}`
  have hset : (Ioc 0 N).filter (fun n ↦ ∀ p ∈ T, ¬ p ∣ n) =
      insert 1 ((Ioc y N).filter Nat.Prime) := by
    have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
    ext n
    simp only [mem_filter, mem_Ioc, mem_insert]
    constructor
    · rintro ⟨⟨h0, hnN⟩, hnd⟩
      by_cases h1 : n = 1
      · exact Or.inl h1
      right
      have hp := Nat.minFac_prime h1
      have hpy : y < n.minFac := by
        by_contra h
        exact hnd _ (Nat.mem_primesLE.mpr ⟨by omega, hp⟩) (Nat.minFac_dvd n)
      have hpr : n.Prime := by
        by_contra hnp
        have hsq := Nat.minFac_sq_le_self h0 hnp
        have hle : (n.minFac : ℝ) ≤ Real.sqrt x := by
          rw [Real.le_sqrt (by positivity) hx0]
          have : ((n.minFac ^ 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hsq.trans hnN
          push_cast at this
          exact this.trans (Nat.floor_le hx0)
        have := Nat.le_floor hle
        omega
      refine ⟨⟨?_, hnN⟩, hpr⟩
      rwa [hpr.minFac_eq] at hpy
    · rintro (rfl | ⟨⟨hyn, hnN⟩, hpr⟩)
      · refine ⟨⟨one_pos, hN1⟩, fun p hp hd ↦ ?_⟩
        exact (hT p hp).one_lt.ne' (Nat.dvd_one.mp hd)
      · refine ⟨⟨by omega, hnN⟩, fun p hp hd ↦ ?_⟩
        have := (Nat.prime_dvd_prime_iff_eq (hT p hp) hpr).mp hd
        have := Nat.le_of_mem_primesLE hp
        omega
  have hy1 : 1 ∉ (Ioc y N).filter Nat.Prime := by simp [Nat.not_prime_one]
  have hcount : Nat.primeCounting N = Nat.primeCounting y + ((Ioc y N).filter Nat.Prime).card := by
    rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE, Nat.primesLE, Nat.primesBelow_eq_filter_range, Nat.primesBelow_eq_filter_range,
      ← card_union_of_disjoint]
    · congr 1
      ext n; simp only [mem_filter, mem_range, mem_union, mem_Ioc]
      by_cases hp : n.Prime <;> simp only [hp, and_true, and_false, or_false]
      omega
    · rw [disjoint_left]; intro n h1 h2
      simp only [mem_filter, mem_range, mem_Ioc] at h1 h2
      omega
  rw [hset, card_insert_of_notMem hy1]
  simp only [primePi]
  rw [← hN, ← hy, hcount]
  push_cast; ring

/-- DLMF 27.12.4: the asymptotic expansion `π(x) ∼ ∑_{k≥1} (k-1)! x/(ln x)^k` as `x → ∞`. -/
@[dlmf 27.12.E4]
theorem primePi_hasAsymptoticExpansion :
    HasAsymptoticExpansion atTop (fun k x ↦ x / Real.log x ^ (k + 1))
      (fun k ↦ (Nat.factorial k : ℝ))
      (fun x ↦ (primePi x : ℝ)) := by
  sorry

/-- DLMF 27.12.5 (de la Vallée Poussin): there is `c > 0` with
`|π(x) - li(x)| = O(x exp(-c (ln x)^{1/2}))`. -/
@[dlmf 27.12.E5]
theorem primePi_sub_li_isBigO :
    ∃ c : ℝ, 0 < c ∧ (fun x : ℝ ↦ (primePi x : ℝ) - li x) =O[atTop]
      fun x ↦ x * Real.exp (-c * Real.log x ^ (1 / 2 : ℝ)) := by
  sorry

/-- DLMF 27.12.6 (Korobov, Vinogradov): there is `d > 0` with
`|π(x) - li(x)| = O(x exp(-d (ln x)^{3/5} (ln ln x)^{-1/5}))`. -/
@[dlmf 27.12.E6]
theorem primePi_sub_li_isBigO_vinogradov :
    ∃ d : ℝ, 0 < d ∧ (fun x : ℝ ↦ (primePi x : ℝ) - li x) =O[atTop]
      fun x ↦ x * Real.exp (-d * Real.log x ^ (3 / 5 : ℝ) *
        Real.log (Real.log x) ^ (-(1 / 5 : ℝ))) := by
  sorry

/-- §27.12 (Prime Number Theorem paragraph, Littlewood): `π(x) - li(x)` changes sign infinitely
often as `x → ∞`. -/
@[dlmf 27.12]
theorem primePi_sub_li_sign_changes :
    (∃ᶠ x in atTop, 0 < (primePi x : ℝ) - li x) ∧ ∃ᶠ x in atTop, (primePi x : ℝ) - li x < 0 := by
  sorry

/-- DLMF 27.12.7: the Riemann hypothesis is equivalent to
`|π(x) - li(x)| < (1/(8π)) √x ln x` for every `x ≥ 2657`. -/
@[dlmf 27.12.E7]
theorem riemannHypothesis_iff_primePi :
    RiemannHypothesis ↔ ∀ x : ℝ, 2657 ≤ x →
      |(primePi x : ℝ) - li x| < 1 / (8 * π) * Real.sqrt x * Real.log x := by
  sorry

/-- DLMF 27.12.8 (Siegel–Walfisz): for every `α > 0` there is `λ(α) > 0` such that the number of
primes `p ≤ x`, `p ≡ a (mod m)`, `(a, m) = 1`, is `li(x)/φ(m) + O(x exp(-λ(α)(ln x)^{1/2}))`
uniformly for `m ≤ (ln x)^α`. -/
@[dlmf 27.12.E8]
theorem primeCounting_ap_siegelWalfisz {α : ℝ} (hα : 0 < α) :
    ∃ l : ℝ, 0 < l ∧ ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ m a : ℕ, 0 < m → (m : ℝ) ≤ Real.log x ^ α →
      a.Coprime m →
        |((((Nat.primesLE ⌊x⌋₊).filter (fun p ↦ p ≡ a [MOD m])).card : ℕ) : ℝ) -
          li x / m.totient| ≤ C * x * Real.exp (-l * Real.log x ^ (1 / 2 : ℝ)) := by
  sorry

/-- §27.12: a Mersenne prime is a prime of the form `2^p - 1` (Mathlib's `mersenne p`); then
`p` is prime. The record value of the largest known prime is excluded (numerical). -/
@[dlmf 27.12]
theorem prime_of_mersenne_prime {p : ℕ} (h : (mersenne p).Prime) : p.Prime :=
  Nat.Prime.of_mersenne h

/-- §27.12, the pseudoprime test: if `2^n ≢ 2 (mod n)` then `n` is composite. -/
@[dlmf 27.12]
theorem not_prime_of_two_pow_not_modEq {n : ℕ} (h : ¬ 2 ^ n ≡ 2 [MOD n]) : ¬ n.Prime := by
  intro hp
  have := Fact.mk hp
  apply h
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  exact ZMod.pow_card 2

/-- DLMF §27.12, Carmichael numbers (proof via Korselt's criterion). -/
theorem q27_isCarmichael_iff_dlmf {n : ℕ} :
    n.IsCarmichael ↔ 1 < n ∧ ¬ n.Prime ∧ ∀ b : ℕ, b ^ n ≡ b [MOD n] := by
  constructor
  · intro h
    obtain ⟨h2, hnp, hsq, hdvd⟩ := Nat.isCarmichael_iff_korselt.mp h
    refine ⟨by omega, hnp, fun b ↦ ?_⟩
    rw [Nat.modEq_iff_dvd]
    rw [show (n : ℤ) = ∏ p ∈ n.primeFactors, (p : ℤ) by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]]
    refine Finset.prod_dvd_of_coprime ?_ fun p hp ↦ ?_
    · intro p hp q hq hpq
      exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
    · have hp' := Nat.prime_of_mem_primeFactors hp
      have := Fact.mk hp'
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [sub_eq_zero]
      obtain ⟨t, ht⟩ := hdvd p hp' (Nat.dvd_of_mem_primeFactors hp)
      by_cases hb : (b : ZMod p) = 0
      · rw [hb, zero_pow (by omega)]
      · have hn : n = (p - 1) * t + 1 := by omega
        rw [hn, pow_succ, pow_mul, ZMod.pow_card_sub_one_eq_one hb, one_pow, one_mul]
  · rintro ⟨h1, hnp, h⟩
    have h2 : 2 < n := by
      rcases Nat.lt_or_ge 2 n with h' | h'
      · exact h'
      · exact absurd (show n = 2 by omega ▸ Nat.prime_two) hnp
    refine ⟨h2, hnp, fun b hb ↦ ?_⟩
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [Nat.coprime_zero_left] at hb; omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hb1 : 1 ≤ b ^ m := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hb0)
    have h4 : b * b ^ m ≡ b * 1 [MOD m + 1] := by rw [mul_one, ← pow_succ']; exact h b
    have h3 := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hb) h4
    show m + 1 ∣ b ^ (m + 1 - 1) - 1
    rw [Nat.add_sub_cancel]
    exact (Nat.modEq_iff_dvd' hb1).mp h3.symm

/-- §27.12: a Carmichael number is a composite `n` with `b^n ≡ b (mod n)` for all `b ∈ ℕ`; this is
Mathlib's `Nat.IsCarmichael` (Korselt's criterion). -/
@[dlmf 27.12]
theorem isCarmichael_iff_dlmf {n : ℕ} :
    n.IsCarmichael ↔ 1 < n ∧ ¬ n.Prime ∧ ∀ b : ℕ, b ^ n ≡ b [MOD n] :=
  q27_isCarmichael_iff_dlmf

/-- §27.12 (Alford–Granville–Pomerance): there are infinitely many Carmichael numbers. -/
@[dlmf 27.12]
theorem infinite_setOf_isCarmichael : {n : ℕ | n.IsCarmichael}.Infinite := by
  sorry

end DLMF.NumberTheory
