/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.NumberTheory.PrimeNumberTheorem
public import Mathlib.Algebra.Order.Antidiag.Nat
public import Mathlib.Data.Finset.NatDivisors
public import Mathlib.NumberTheory.ArithmeticFunction.Liouville

/-!
# Functions of multiplicative number theory (DLMF §27.2)

DLMF §27.2 introduces the number-theoretic functions of Chapter 27. Most of them are
Mathlib's:

* `ν(n)` is `ArithmeticFunction.cardDistinctFactors` (`ω`), `Ω` is `cardFactors`;
* `φ(n)` is `Nat.totient`, `d(n) = σ₀(n)` and `σ_k(n)` (natural `k`) are
  `ArithmeticFunction.sigma`;
* `μ`, `λ`, `Λ` are `ArithmeticFunction.moebius`, `ArithmeticFunction.liouville`,
  `ArithmeticFunction.vonMangoldt`;
* `π(n)` is `Nat.primeCounting`, the `n`th prime `p_n` is `Nat.nth Nat.Prime (n - 1)` (DLMF
  starts at `p₁ = 2`, Mathlib's `Nat.nth` at index `0`).

This file defines the others, with their defining formulas, and DLMF's notions of
multiplicative and completely multiplicative functions (DLMF 27.3.1, 27.3.9).

## Main definitions

* `primePi`: the prime counting function `π(x) = π(⌊x⌋)` of a real argument (DLMF 27.2.2).
* `nthPrime`: the `n`th prime `p_n`, with `p₁ = 2`.
* `totientPowerSum`: the power sums `φ_k(n)` of the reduced residues (DLMF 27.2.6).
* `IsPrimitiveRootMod`: primitive roots mod `n` (DLMF §27.2(i)).
* `divisorCountK`: `d_k(n)`, the number of ordered factorizations of `n` into `k` factors.
* `powC`, `sigmaC`: the arithmetic function `n ↦ n^α` and the divisor function `σ_α(n)` for
  complex `α` (DLMF 27.2.10).
* `jordanTotient`: Jordan's function `J_k(n)` (DLMF 27.2.11).
* `IsMultiplicativeFn`, `IsCompletelyMultiplicativeFn`: multiplicative and completely
  multiplicative functions on the positive integers (DLMF 27.3.1, 27.3.9).

## Main results

* `prod_primeFactors_pow_factorization`, `eq_factorization_of_prod`: the fundamental theorem
  of arithmetic (DLMF 27.2.1).
* `primePi_eq_card`, `primePi_isEquivalent`, `nthPrime_isEquivalent`: DLMF 27.2.2, and the
  prime number theorem in the forms DLMF 27.2.3 and 27.2.4.
* `floor_one_div`: DLMF 27.2.5.
* `totientPowerSum_zero`, `IsPrimitiveRootMod.reduced_residue_system`,
  `sigma_zero_eq_card_divisors`, `divisorCountK_two`, `sigmaC_apply`, `sigmaC_natCast`,
  `jordanTotient_one`: the defining formulas DLMF 27.2.7–27.2.11.
* `isMultiplicative_powC`, `isMultiplicative_sigmaC`: `n ↦ n^α` and `σ_α` are multiplicative.
* `moebius_eq_cases`, `liouville_eq_cases`, `vonMangoldt_eq_cases`: DLMF 27.2.12–27.2.14 for
  Mathlib's `μ`, `λ` and `Λ`.
* `isMultiplicative_iff_isMultiplicativeFn`: Mathlib's multiplicativity is DLMF's.
* `IsCompletelyMultiplicativeFn.isMultiplicativeFn`: completely multiplicative functions are
  multiplicative.

## Implementation notes

DLMF's functions live on the positive integers `n = 1, 2, …`; the Lean definitions are total
on `ℕ` and all statements carry `0 < n` (or `n ≠ 0`) where DLMF has `n ≥ 1`. Tables 27.2.1
and 27.2.2 (§27.2(ii)) are tabulated values and are out of scope. The multiplicative
properties of §27.3 are in `DLMF.NumberTheory.Functions`.
-/

@[expose] public noncomputable section

open Finset Filter Asymptotics ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.Moebius ArithmeticFunction.omega
  ArithmeticFunction.Omega

namespace DLMF.NumberTheory

/-! ### §27.2(i) Definitions -/

/-- The `n`th prime `p_n` in DLMF's numbering `p₁ = 2, p₂ = 3, …` (DLMF 27.2.4, 27.12). The
value at the meaningless index `n = 0` is `p₁`. -/
def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The prime counting function `π(x)`, the number of primes not exceeding the real number `x`
(DLMF 27.2.2). It is `Nat.primeCounting ⌊x⌋₊` (and `0` for `x < 2`). -/
def primePi (x : ℝ) : ℕ := Nat.primeCounting ⌊x⌋₊

/-- DLMF 27.2.1 (fundamental theorem of arithmetic, existence): every `n ≥ 1` is the product
of the prime powers `p^{a_p}` over its distinct prime factors, and `ν(n) = ω(n)` is the number
of those factors (`ν(1) = 0`). -/
@[dlmf 27.2.E1]
theorem prod_primeFactors_pow_factorization {n : ℕ} (hn : n ≠ 0) :
    n = ∏ p ∈ n.primeFactors, p ^ n.factorization p ∧ ω n = n.primeFactors.card := by
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rfl
  · rw [cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors]

/-- DLMF 27.2.1 (uniqueness): a representation of `n ≥ 1` as a product of powers of distinct
primes is the prime factorization. -/
@[dlmf 27.2.E1]
theorem eq_factorization_of_prod {n : ℕ} (hn : n ≠ 0) (f : ℕ →₀ ℕ)
    (hf : ∀ p ∈ f.support, p.Prime) (h : f.prod (· ^ ·) = n) : f = n.factorization :=
  (Nat.eq_factorization_iff hn hf).mpr h


/-- DLMF 27.2.2: `π(x) = ∑_{p ≤ x} 1`. -/
@[dlmf 27.2.E2]
theorem primePi_eq_card (x : ℝ) :
    primePi x = ((Finset.Iic ⌊x⌋₊).filter Nat.Prime).card := by
  rw [primePi, ← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_range]
  congr 1
  ext p
  simp

/-- DLMF 27.2.3, the prime number theorem: `π(x) ∼ x/ln x` as `x → ∞` (conjectured by Gauss
and Legendre, proved by Hadamard and de la Vallée Poussin). -/
@[dlmf 27.2.E3]
theorem primePi_isEquivalent :
    (fun x : ℝ ↦ (primePi x : ℝ)) ~[atTop] fun x ↦ x / Real.log x :=
  -- TauCeti's prime ideal theorem for `ℚ`, via `DLMFMathlib.NumberTheory.PrimeNumberTheorem`
  Nat.primeCounting_floor_isEquivalent

/-- DLMF 27.2.4: the equivalent form `p_n ∼ n ln n` of the prime number theorem. -/
@[dlmf 27.2.E4]
theorem nthPrime_isEquivalent :
    (fun n : ℕ ↦ (nthPrime n : ℝ)) ~[atTop] fun n ↦ n * Real.log n := by
  have hsub : Tendsto (fun n : ℕ ↦ n - 1) atTop atTop := tendsto_sub_atTop_nat 1
  have h := Nat.nth_prime_isEquivalent.comp_tendsto hsub
  -- `(n - 1 : ℕ) ~ n`
  have hn : (fun n : ℕ ↦ ((n - 1 : ℕ) : ℝ)) ~[atTop] fun n ↦ (n : ℝ) := by
    refine (Nat.natCast_add_one_isEquivalent.comp_tendsto hsub).symm.congr_right ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Function.comp_apply]
    rw [Nat.cast_sub hn, Nat.cast_one, sub_add_cancel]
  have hlog := hn.log tendsto_natCast_atTop_atTop
  exact h.trans (hn.mul hlog)

/-- DLMF 27.2.5: `⌊1/n⌋ = 1` for `n = 1` and `0` for `n > 1`. -/
@[dlmf 27.2.E5]
theorem floor_one_div {n : ℕ} (hn : 0 < n) :
    ⌊(1 : ℝ) / n⌋ = if n = 1 then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · rw [Int.floor_eq_iff]
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    have hpos : (0 : ℝ) < n := by positivity
    refine ⟨by simp, ?_⟩
    rw [div_lt_iff₀ hpos]
    push_cast
    linarith

/-- DLMF 27.2.6: `φ_k(n) = ∑_{(m,n)=1} m^k`, the sum of the `k`th powers of the positive
integers `m ≤ n` that are relatively prime to `n`. -/
@[dlmf 27.2.E6]
def totientPowerSum (k n : ℕ) : ℕ :=
  ∑ m ∈ (Finset.Icc 1 n).filter (fun m ↦ m.Coprime n), m ^ k

/-- DLMF 27.2.7: Euler's totient is `φ(n) = φ₀(n)`, the number of positive integers `≤ n`
relatively prime to `n`. -/
@[dlmf 27.2.E7]
theorem totientPowerSum_zero (n : ℕ) : totientPowerSum 0 n = n.totient := by
  rw [totientPowerSum, ← Nat.filter_coprime_Ico_eq_totient n 1]
  simp only [pow_zero, sum_const, smul_eq_mul, mul_one]
  congr 1
  ext m
  simp only [mem_filter, mem_Icc, mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h3.symm⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h3.symm⟩


/-- §27.2(i) after 27.2.8: `a` is a primitive root mod `n` if `(a, n) = 1` and `φ(n)` is the
smallest positive exponent `f` with `a^f ≡ 1 (mod n)`, i.e. the order of `a` in `ℤ/nℤ` is
`φ(n)`. -/
@[dlmf 27.2.i]
def IsPrimitiveRootMod (a n : ℕ) : Prop :=
  a.Coprime n ∧ orderOf (a : ZMod n) = n.totient

/-- §27.2(i) after 27.2.8: for a primitive root `a` mod `n ≥ 1`, the `φ(n)` numbers
`a, a², …, a^{φ(n)}` are relatively prime to `n` and pairwise incongruent mod `n` (a reduced
residue system). -/
@[dlmf 27.2.i]
theorem IsPrimitiveRootMod.reduced_residue_system {a n : ℕ} (h : IsPrimitiveRootMod a n) :
    (∀ i, (a ^ i).Coprime n) ∧
      ∀ i ∈ Finset.Icc 1 n.totient, ∀ j ∈ Finset.Icc 1 n.totient,
        a ^ i ≡ a ^ j [MOD n] → i = j := by
  refine ⟨fun i ↦ Nat.Coprime.pow_left i h.1, ?_⟩
  intro i hi j hj hij
  rw [← ZMod.natCast_eq_natCast_iff] at hij
  push_cast at hij
  simp only [mem_Icc] at hi hj
  have key : ∀ i j : ℕ, 1 ≤ i → i ≤ n.totient → 1 ≤ j → j ≤ n.totient →
      ((a : ZMod n) ^ i = (a : ZMod n) ^ j) → i ≤ j → i = j := by
    intro i j hi1 hi2 hj1 hj2 hij hle
    have hj' : (a : ZMod n) ^ (j - i) * (a : ZMod n) ^ i = 1 * (a : ZMod n) ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hle, one_mul, hij]
    have hu : IsUnit (a : ZMod n) := (ZMod.unitOfCoprime a h.1).isUnit
    have h1 : (a : ZMod n) ^ (j - i) = 1 := (hu.pow i).mul_right_cancel hj'
    by_contra hne
    have hpos : 0 < j - i := by omega
    have := orderOf_le_of_pow_eq_one hpos h1
    rw [h.2] at this
    omega
  rcases le_total i j with hle | hle
  · exact key i j hi.1 hi.2 hj.1 hj.2 hij hle
  · exact (key j i hj.1 hj.2 hi.1 hi.2 hij.symm hle).symm

/-- `d_k(n)`: the number of ways of writing `n` as an ordered product of `k` factors
(§27.2(i) after 27.2.9). -/
@[dlmf 27.2.E9]
def divisorCountK (k n : ℕ) : ℕ := (Nat.finMulAntidiag k n).card

/-- DLMF 27.2.9: `d(n) = ∑_{d∣n} 1` is the number of divisors of `n`; it is `σ₀(n)`. -/
@[dlmf 27.2.E9]
theorem sigma_zero_eq_card_divisors (n : ℕ) : σ 0 n = ∑ _d ∈ n.divisors, 1 := by
  simp [sigma_zero_apply]

/-- §27.2(i) after 27.2.9: `d(n)` is the special case `k = 2` of `d_k(n)`. -/
@[dlmf 27.2.E9]
theorem divisorCountK_two (n : ℕ) : divisorCountK 2 n = σ 0 n := by
  rw [divisorCountK, sigma_zero_apply, ← Finset.card_map ⟨fun d ↦ (d, n / d), fun _ _ h ↦
      (Prod.ext_iff.mp h).1⟩, Nat.map_div_right_divisors,
    ← Nat.image_piFinTwoEquiv_finMulAntidiag, Finset.card_image_of_injective _
      (Equiv.injective _)]

/-- `n ↦ n^α` as an arithmetic function (with value `0` at `0`), `α ∈ ℂ`. -/
def powC (α : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n = 0 then 0 else (n : ℂ) ^ α, by simp⟩

/-- Identity under the stated parameter and domain assumptions: `powC α n = (n : ℂ) ^ α`. -/
theorem powC_apply {α : ℂ} {n : ℕ} (hn : n ≠ 0) : powC α n = (n : ℂ) ^ α := by
  simp [powC, hn]

/-- The stated relation follows from the given hypotheses: `IsMultiplicative (powC α)`. -/
theorem isMultiplicative_powC (α : ℂ) : IsMultiplicative (powC α) := by
  refine ⟨by simp [powC], fun {m n} _ ↦ ?_⟩
  by_cases hm : m = 0
  · simp [powC, hm]
  by_cases hn : n = 0
  · simp [powC, hn]
  rw [powC_apply hm, powC_apply hn, powC_apply (mul_ne_zero hm hn), Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow]

/-- DLMF 27.2.10: the divisor function `σ_α(n) = ∑_{d∣n} d^α` for complex `α`, as the
arithmetic function `ζ * (n ↦ n^α)`. -/
def sigmaC (α : ℂ) : ArithmeticFunction ℂ := (zeta : ArithmeticFunction ℂ) * powC α

/-- DLMF 27.2.10: `σ_α(n) = ∑_{d∣n} d^α`, `α ∈ ℂ`. -/
@[dlmf 27.2.E10]
theorem sigmaC_apply (α : ℂ) (n : ℕ) : sigmaC α n = ∑ d ∈ n.divisors, (d : ℂ) ^ α := by
  rw [sigmaC, coe_zeta_mul_apply]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [powC_apply (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))]

/-- `σ_α` is multiplicative. -/
theorem isMultiplicative_sigmaC (α : ℂ) : IsMultiplicative (sigmaC α) :=
  isMultiplicative_zeta.natCast.mul (isMultiplicative_powC α)

/-- For natural exponents, `sigmaC` is Mathlib's `σ`. -/
theorem sigmaC_natCast (k n : ℕ) : sigmaC k n = (σ k n : ℂ) := by
  rw [sigmaC_apply, sigma_apply]
  push_cast
  simp_rw [Complex.cpow_natCast]

/-- §27.2(i) after 27.2.10: `σ₀(n) = d(n)`. -/
@[dlmf 27.2.E10]
theorem sigmaC_zero (n : ℕ) : sigmaC 0 n = (σ 0 n : ℂ) := by
  exact_mod_cast sigmaC_natCast 0 n

/-- DLMF 27.2.11: Jordan's function `J_k(n)`, the number of `k`-tuples of integers in
`[1, n]` whose greatest common divisor is relatively prime to `n`. -/
@[dlmf 27.2.E11]
def jordanTotient (k n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin k ↦ Finset.Icc 1 n).filter
    fun d ↦ (Finset.univ.gcd d).Coprime n).card

/-- §27.2(i) after 27.2.11: `J₁(n) = φ(n)`. -/
@[dlmf 27.2.E11]
theorem jordanTotient_one (n : ℕ) : jordanTotient 1 n = n.totient := by
  rw [← totientPowerSum_zero, totientPowerSum, jordanTotient]
  simp only [pow_zero, sum_const, smul_eq_mul, mul_one]
  refine Finset.card_bij (fun d _ ↦ d 0) ?_ ?_ ?_
  · intro d hd
    simp only [mem_filter, Fintype.mem_piFinset] at hd ⊢
    refine ⟨hd.1 0, ?_⟩
    simpa [Finset.univ_unique, Finset.gcd_singleton] using hd.2
  · intro d₁ _ d₂ _ h
    funext i
    fin_cases i
    exact h
  · intro m hm
    refine ⟨fun _ ↦ m, ?_, rfl⟩
    simp only [mem_filter, Fintype.mem_piFinset] at hm ⊢
    refine ⟨fun _ ↦ hm.1, ?_⟩
    simpa [Finset.univ_unique, Finset.gcd_singleton] using hm.2

/-- DLMF 27.2.12: the Möbius function `μ(n)` is `1` for `n = 1`, `(-1)^{ν(n)}` when all
exponents `a_r` equal `1`, and `0` otherwise (Mathlib's `ArithmeticFunction.moebius`). -/
@[dlmf 27.2.E12]
theorem moebius_eq_cases {n : ℕ} (hn : n ≠ 0) :
    μ n = if n = 1 then 1 else
      if ∀ p ∈ n.primeFactors, n.factorization p = 1 then (-1) ^ ω n else 0 := by
  split_ifs with h1 h2
  · subst h1; simp
  · have hsq : Squarefree n := by
      rw [Nat.squarefree_iff_factorization_le_one hn]
      intro p
      by_cases hp : p ∈ n.primeFactors
      · exact (h2 p hp).le
      · rw [Finsupp.notMem_support_iff.mp (by simpa using hp)]; omega
    rw [moebius_apply_of_squarefree hsq,
      (cardDistinctFactors_eq_cardFactors_iff_squarefree hn).mpr hsq]
  · push Not at h2
    obtain ⟨p, hp, hne⟩ := h2
    have hpos : 0 < n.factorization p :=
      (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn
        (Nat.dvd_of_mem_primeFactors hp)
    have hsq : ¬ Squarefree n := by
      rw [Nat.squarefree_iff_factorization_le_one hn]
      intro h
      have := h p
      omega
    exact moebius_eq_zero_of_not_squarefree hsq

/-- DLMF 27.2.13: Liouville's function `λ(n)` is `1` for `n = 1` and `(-1)^{a₁ + ⋯ + a_ν}` for
`n > 1` (Mathlib's `ArithmeticFunction.liouville`). -/
@[dlmf 27.2.E13]
theorem liouville_eq_cases {n : ℕ} (hn : n ≠ 0) :
    liouville n = if n = 1 then 1 else (-1) ^ (∑ p ∈ n.primeFactors, n.factorization p) := by
  split_ifs with h1
  · subst h1; exact liouville_apply_one
  · rw [liouville_apply hn, cardFactors_eq_sum_factorization]
    rfl

/-- DLMF 27.2.14: Mangoldt's function is `Λ(p^a) = ln p` for a prime power `p^a`, `a ≥ 1`,
and `Λ(n) = 0` otherwise (Mathlib's `ArithmeticFunction.vonMangoldt`). -/
@[dlmf 27.2.E14]
theorem vonMangoldt_eq_cases :
    (∀ {p a : ℕ}, p.Prime → a ≠ 0 → vonMangoldt (p ^ a) = Real.log p) ∧
      ∀ {n : ℕ}, ¬ IsPrimePow n → vonMangoldt n = 0 :=
  ⟨fun hp ha ↦ by rw [vonMangoldt_apply_pow ha, vonMangoldt_apply_prime hp],
    fun h ↦ vonMangoldt_eq_zero_iff.mpr h⟩

/-! ### §27.3 Multiplicative functions -/

/-- DLMF 27.3.1: `f` is multiplicative on the positive integers if `f(1) = 1` and
`f(mn) = f(m)f(n)` whenever `(m, n) = 1`. -/
@[dlmf 27.3.E1]
def IsMultiplicativeFn {R : Type*} [MonoidWithZero R] (f : ℕ → R) : Prop :=
  f 1 = 1 ∧ ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → f (m * n) = f m * f n

/-- Mathlib's `ArithmeticFunction.IsMultiplicative` is DLMF's notion (27.3.1). -/
@[dlmf 27.3.E1]
theorem isMultiplicative_iff_isMultiplicativeFn {R : Type*} [MonoidWithZero R]
    (f : ArithmeticFunction R) : f.IsMultiplicative ↔ IsMultiplicativeFn (f : ℕ → R) := by
  refine ⟨fun h ↦ ⟨h.1, fun m n _ _ hmn ↦ h.2 hmn⟩, fun h ↦ ⟨h.1, fun {m n} hmn ↦ ?_⟩⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  exact h.2 m n hm hn hmn

/-- DLMF 27.3.9: `f` is completely multiplicative if `f(1) = 1` and `f(mn) = f(m)f(n)` for
all `m, n = 1, 2, …`. -/
@[dlmf 27.3.E9]
def IsCompletelyMultiplicativeFn {R : Type*} [MonoidWithZero R] (f : ℕ → R) : Prop :=
  f 1 = 1 ∧ ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n

/-- Completely multiplicative functions are multiplicative. -/
theorem IsCompletelyMultiplicativeFn.isMultiplicativeFn {R : Type*} [MonoidWithZero R]
    {f : ℕ → R} (h : IsCompletelyMultiplicativeFn f) : IsMultiplicativeFn f :=
  ⟨h.1, fun m n hm hn _ ↦ h.2 m n hm hn⟩


end DLMF.NumberTheory
