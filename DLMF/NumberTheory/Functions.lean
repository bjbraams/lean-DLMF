/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Liouville
public import Mathlib.Algebra.Order.Antidiag.Nat
public import Mathlib.Data.Finset.NatDivisors
public import DLMFMathlib.NumberTheory.T27aPrimeNumberTheorem

/-!
# Functions of multiplicative number theory (DLMF §§27.1–27.3)

DLMF §27.2 introduces the number-theoretic functions of Chapter 27 and §27.3 their
multiplicative properties. Most of them are Mathlib's:

* `ν(n)` is `ArithmeticFunction.cardDistinctFactors` (`ω`), `Ω` is `cardFactors`;
* `φ(n)` is `Nat.totient`, `d(n) = σ₀(n)` and `σ_k(n)` (natural `k`) are
  `ArithmeticFunction.sigma`;
* `μ`, `λ`, `Λ` are `ArithmeticFunction.moebius`, `ArithmeticFunction.liouville`,
  `ArithmeticFunction.vonMangoldt`;
* `π(n)` is `Nat.primeCounting`, the `n`th prime `p_n` is `Nat.nth Nat.Prime (n - 1)` (DLMF
  starts at `p₁ = 2`, Mathlib's `Nat.nth` at index `0`).

New here: the real-argument prime counting function `primePi x = π(⌊x⌋)` (DLMF 27.2.2, `x`
real), `nthPrime`, the power sums `φ_k(n)` of the reduced residues (`totientPowerSum`, 27.2.6),
the multiplicative divisor function `d_k(n)` (`divisorCountK`, the number of ordered
factorizations into `k` factors), the divisor function `σ_α(n)` for complex `α` (`sigmaC`,
27.2.10) and Jordan's function `J_k(n)` (`jordanTotient`, 27.2.11), together with the
definitions of multiplicative and completely multiplicative functions on the positive
integers (27.3.1, 27.3.9).

DLMF's functions live on the positive integers `n = 1, 2, …`; the Lean definitions are total
on `ℕ` and all statements carry `0 < n` (or `n ≠ 0`) where DLMF has `n ≥ 1`. Tables 27.2.1
and 27.2.2 (§27.2(ii)) are tabulated values and are not acquired (excluded: numerical).

**Correction (27.3, first sentence).** DLMF says that, except for `ν`, `Λ`, `p_n` and `π(x)`,
the functions of §27.2 are multiplicative. The power sums `φ_k` with `k ≥ 1` are not:
`φ₁(2)φ₁(3) = 1 · 3 ≠ 6 = φ₁(6)` (`totientPowerSum_one_not_multiplicative`). The remaining
functions (`⌊1/n⌋`, `φ = φ₀`, `d`, `d_k`, `σ_α`, `J_k`, `μ`, `λ`) are multiplicative.

**Correction (27.3.6).** For complex `α` the hypothesis `α ≠ 0` does not keep the denominators
`p^α - 1` away from zero (`p^α = 1` for `α = 2πi m / ln p`); the formula is stated under
`p^α ≠ 1` for every prime `p ∣ n`, which holds for every real `α ≠ 0`.
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

/-- §27.2(i): Euclid's theorem, there are infinitely many primes. -/
@[dlmf 27.2.i]
theorem infinite_setOf_prime' : {p : ℕ | p.Prime}.Infinite := Nat.infinite_setOfPred_prime

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
  -- TauCeti's prime ideal theorem for `ℚ`, via `DLMFMathlib.NumberTheory.T27aPrimeNumberTheorem`
  Nat.t27a_primeCounting_isEquivalent

/-- DLMF 27.2.4: the equivalent form `p_n ∼ n ln n` of the prime number theorem. -/
@[dlmf 27.2.E4]
theorem nthPrime_isEquivalent :
    (fun n : ℕ ↦ (nthPrime n : ℝ)) ~[atTop] fun n ↦ n * Real.log n := by
  have hsub : Tendsto (fun n : ℕ ↦ n - 1) atTop atTop := tendsto_sub_atTop_nat 1
  have h := Nat.t27a_nth_prime_isEquivalent.comp_tendsto hsub
  -- `(n - 1 : ℕ) ~ n`
  have hn : (fun n : ℕ ↦ ((n - 1 : ℕ) : ℝ)) ~[atTop] fun n ↦ (n : ℝ) := by
    refine (Nat.t27a_natCast_add_one_isEquivalent.comp_tendsto hsub).symm.congr_right ?_
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

/-- DLMF 27.2.8, the Euler–Fermat theorem: `a^{φ(n)} ≡ 1 (mod n)` when `(a, n) = 1`. -/
@[dlmf 27.2.E8]
theorem pow_totient_modEq_one {a n : ℕ} (h : a.Coprime n) : a ^ n.totient ≡ 1 [MOD n] :=
  Nat.ModEq.pow_totient h

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

/-! ### §27.3 Multiplicative properties -/

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

/-- §27.3 after 27.3.9: `⌊1/n⌋` is completely multiplicative. -/
@[dlmf 27.3.E9]
theorem isCompletelyMultiplicativeFn_floor_one_div :
    IsCompletelyMultiplicativeFn fun n : ℕ ↦ ⌊(1 : ℝ) / n⌋ := by
  refine ⟨by simp, fun m n hm hn ↦ ?_⟩
  dsimp only
  rw [floor_one_div hm, floor_one_div hn, floor_one_div (Nat.mul_pos hm hn)]
  by_cases h1 : m = 1 <;> by_cases h2 : n = 1 <;> simp [h1, h2, mul_eq_one]

/-- §27.3 after 27.3.9: Liouville's `λ` is completely multiplicative. -/
@[dlmf 27.3.E9]
theorem isCompletelyMultiplicativeFn_liouville :
    IsCompletelyMultiplicativeFn fun n : ℕ ↦ liouville n :=
  ⟨liouville_apply_one, fun m n _ _ ↦ liouville_apply_mul m n⟩

/-- §27.3, first sentence: `φ`, `d = σ₀`, `σ_α`, `μ` and `λ` are multiplicative; the
corresponding facts for `⌊1/n⌋`, `d_k` and `J_k` are `isCompletelyMultiplicativeFn_floor_one_div`,
`isMultiplicativeFn_divisorCountK` and `isMultiplicativeFn_jordanTotient`. -/
@[dlmf 27.3]
theorem isMultiplicativeFn_basic (α : ℂ) :
    IsMultiplicativeFn (fun n ↦ n.totient) ∧ IsMultiplicativeFn (σ 0 : ℕ → ℕ) ∧
      IsMultiplicativeFn (sigmaC α : ℕ → ℂ) ∧ IsMultiplicativeFn (μ : ℕ → ℤ) ∧
      IsMultiplicativeFn (liouville : ℕ → ℤ) := by
  refine ⟨⟨Nat.totient_one, fun m n _ _ h ↦ Nat.totient_mul h⟩,
    (isMultiplicative_iff_isMultiplicativeFn _).mp isMultiplicative_sigma,
    (isMultiplicative_iff_isMultiplicativeFn _).mp
      (isMultiplicative_sigmaC α),
    (isMultiplicative_iff_isMultiplicativeFn _).mp isMultiplicative_moebius,
    (isMultiplicative_iff_isMultiplicativeFn _).mp isMultiplicative_liouville⟩

section q27
open scoped ArithmeticFunction.zeta

/-- Recursion for the ordered factorizations: split off the first factor. -/
lemma q27_card_finMulAntidiag_succ (k n : ℕ) :
    (Nat.finMulAntidiag (k + 1) n).card =
      ∑ ab ∈ n.divisorsAntidiagonal, (Nat.finMulAntidiag k ab.2).card := by
  rw [card_eq_sum_card_fiberwise (f := fun g : Fin (k + 1) → ℕ ↦ (g 0, ∏ i, Fin.tail g i))
    (t := n.divisorsAntidiagonal)]
  · refine sum_congr rfl fun ab hab ↦ ?_
    rw [Nat.mem_divisorsAntidiagonal] at hab
    refine card_nbij' (fun g ↦ Fin.tail g) (fun g ↦ Fin.cons ab.1 g) ?_ ?_ ?_ ?_
    · intro g hg
      rw [mem_coe, mem_filter, Nat.mem_finMulAntidiag, Prod.ext_iff] at hg
      rw [mem_coe, Nat.mem_finMulAntidiag]
      refine ⟨hg.2.2, ?_⟩
      rintro h; rw [h, mul_zero] at hab; exact hab.2 hab.1.symm
    · intro g hg
      rw [mem_coe, Nat.mem_finMulAntidiag] at hg
      rw [mem_coe, mem_filter, Nat.mem_finMulAntidiag, Prod.ext_iff, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail_cons]
      exact ⟨⟨by rw [hg.1, hab.1], hab.2⟩, trivial, hg.1⟩
    · intro g hg
      rw [mem_coe, mem_filter, Prod.ext_iff] at hg
      simp only
      rw [← hg.2.1]; exact Fin.cons_self_tail g
    · intro g _; simp
  · intro g hg
    rw [mem_coe, Nat.mem_finMulAntidiag] at hg
    rw [mem_coe, Nat.mem_divisorsAntidiagonal]
    refine ⟨?_, hg.2⟩
    rw [← hg.1, Fin.prod_univ_succ]
    rfl

/-- `d_k = ζ^k` as arithmetic functions (Dirichlet power of `ζ`). -/
theorem q27_divisorCountK_eq_zeta_pow (k n : ℕ) :
    divisorCountK k n = ((ζ : ArithmeticFunction ℕ) ^ k) n := by
  induction k generalizing n with
  | zero =>
    rw [pow_zero, one_apply, divisorCountK]
    split_ifs with h
    · subst h; rw [Nat.finMulAntidiag_one, card_singleton]
    · rw [Nat.finMulAntidiag_zero_left h, card_empty]
  | succ k ih =>
    rw [divisorCountK, q27_card_finMulAntidiag_succ, pow_succ', mul_apply]
    refine sum_congr rfl fun ab hab ↦ ?_
    rw [← divisorCountK, ih, zeta_apply, ite_eq_right (Nat.ne_of_gt (Nat.pos_of_mem_divisors
      (Nat.fst_mem_divisors_of_mem_antidiagonal hab))), one_mul]

/-- `∑_{d∣n} J_k(d) = n^k` (DLMF 27.6.3), proved here for use in §27.3. -/
theorem q27_sum_divisors_jordanTotient (k : ℕ) {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, jordanTotient k d = n ^ k := by
  have hcard : (Fintype.piFinset fun _ : Fin k ↦ Finset.Icc 1 n).card = n ^ k := by
    simp
  rw [← hcard, card_eq_sum_card_fiberwise (f := fun a : Fin k → ℕ ↦
    n / Nat.gcd (univ.gcd a) n) (t := n.divisors)]
  · refine sum_congr rfl fun e he ↦ ?_
    have hen : e ∣ n := Nat.dvd_of_mem_divisors he
    obtain ⟨c, hc⟩ := hen
    have he0 : 0 < e := Nat.pos_of_mem_divisors he
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [h, mul_zero] at hc; omega
      · exact h
    have hne : n / e = c := by rw [hc, Nat.mul_div_cancel_left _ he0]
    have hG : ∀ b : Fin k → ℕ, (univ.gcd fun i ↦ c * b i) = c * univ.gcd b := fun b ↦ by
      rw [Finset.gcd_mul_left, normalize_eq]
    unfold jordanTotient
    symm
    refine card_nbij' (fun a i ↦ a i / c) (fun b i ↦ c * b i) ?_ ?_ ?_ ?_
    · intro a ha
      rw [mem_coe, mem_filter, Fintype.mem_piFinset] at ha
      rw [mem_coe, mem_filter, Fintype.mem_piFinset]
      have hg : Nat.gcd (univ.gcd a) n = c := by
        obtain ⟨m, hm⟩ := Nat.gcd_dvd_right (univ.gcd a) n
        have hg0 := Nat.gcd_pos_of_pos_right (univ.gcd a) hn
        set g := Nat.gcd (univ.gcd a) n with hgdef
        have h2 : n / g = e := ha.2
        rw [hm, Nat.mul_div_cancel_left _ hg0] at h2
        rw [h2] at hm
        rw [hm, mul_comm] at hc
        exact Nat.eq_of_mul_eq_mul_left he0 hc
      have hcd : ∀ i, c ∣ a i := fun i ↦
        hg ▸ (Nat.gcd_dvd_left _ _).trans (Finset.gcd_dvd (mem_univ i))
      have ha' : a = fun i ↦ c * (a i / c) := funext fun i ↦ (Nat.mul_div_cancel' (hcd i)).symm
      refine ⟨fun i ↦ ?_, ?_⟩
      · have := mem_Icc.mp (ha.1 i)
        rw [mem_Icc]
        constructor
        · exact (Nat.le_div_iff_mul_le hc0).mpr (by
            obtain ⟨t, ht⟩ := hcd i
            rw [ht] at this ⊢
            have : 0 < t := by
              rcases Nat.eq_zero_or_pos t with h | h
              · rw [h, mul_zero] at this; omega
              · exact h
            nlinarith)
        · exact (Nat.div_le_iff_le_mul_add_pred hc0).mpr (by
            rw [hc] at this; nlinarith [this.2])
      · rw [ha', hG, hc, mul_comm e c, Nat.gcd_mul_left] at hg
        have : Nat.gcd (univ.gcd fun i ↦ a i / c) e = 1 := by
          have := hg
          exact Nat.eq_of_mul_eq_mul_left hc0 (this.trans (mul_one c).symm)
        exact this
    · intro b hb
      rw [mem_coe, mem_filter, Fintype.mem_piFinset] at hb
      rw [mem_coe, mem_filter, Fintype.mem_piFinset]
      refine ⟨fun i ↦ ?_, ?_⟩
      · have := mem_Icc.mp (hb.1 i)
        rw [mem_Icc]
        constructor
        · nlinarith
        · rw [hc, mul_comm e c]; exact Nat.mul_le_mul_left c this.2
      · simp only
        rw [hG, hc, mul_comm e c, Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hb.2, mul_one,
          Nat.mul_div_cancel_left _ hc0]
    · intro a ha
      rw [mem_coe, mem_filter, Fintype.mem_piFinset] at ha
      have hg : Nat.gcd (univ.gcd a) n = c := by
        obtain ⟨m, hm⟩ := Nat.gcd_dvd_right (univ.gcd a) n
        have hg0 := Nat.gcd_pos_of_pos_right (univ.gcd a) hn
        set g := Nat.gcd (univ.gcd a) n with hgdef
        have h2 : n / g = e := ha.2
        rw [hm, Nat.mul_div_cancel_left _ hg0] at h2
        rw [h2] at hm
        rw [hm, mul_comm] at hc
        exact Nat.eq_of_mul_eq_mul_left he0 hc
      funext i
      exact Nat.mul_div_cancel' (hg ▸ (Nat.gcd_dvd_left _ _).trans (Finset.gcd_dvd (mem_univ i)))
    · intro b _
      funext i
      simp only
      exact Nat.mul_div_cancel_left _ hc0
  · intro a _
    rw [mem_coe, Nat.mem_divisors]
    exact ⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _), hn.ne'⟩

/-- `J_k(0) = 0`. -/
lemma q27_jordanTotient_zero_right (k : ℕ) : jordanTotient k 0 = 0 := by
  rcases k with _ | k
  · decide
  · simp [jordanTotient]

/-- Jordan's totient as an integer-valued arithmetic function. -/
def q27_jordanAF (k : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n ↦ jordanTotient k n, by simp [q27_jordanTotient_zero_right]⟩

/-- Möbius inversion of `∑_{d∣n} J_k(d) = n^k`: `J_k = μ * n^k`. -/
lemma q27_jordanAF_eq (k : ℕ) :
    q27_jordanAF k = (μ : ArithmeticFunction ℤ) * (pow k : ArithmeticFunction ℤ) := by
  have h : (ζ : ArithmeticFunction ℤ) * q27_jordanAF k = (pow k : ArithmeticFunction ℤ) := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [coe_zeta_mul_apply, natCoe_apply, pow_apply, ite_eq_right (by omega)]
    change ∑ i ∈ n.divisors, ((jordanTotient k i : ℕ) : ℤ) = _
    exact_mod_cast q27_sum_divisors_jordanTotient k hn
  rw [← h, ← mul_assoc, moebius_mul_coe_zeta, one_mul]

/-- `J_k` is multiplicative. -/
lemma q27_isMultiplicative_jordanAF (k : ℕ) : (q27_jordanAF k).IsMultiplicative := by
  rw [q27_jordanAF_eq]
  exact isMultiplicative_moebius.mul isMultiplicative_pow.natCast

/-- `J_k` is multiplicative (all `k`). -/
lemma q27_isMultiplicativeFn_jordanTotient (k : ℕ) :
    IsMultiplicativeFn (jordanTotient k) := by
  have h := (isMultiplicative_iff_isMultiplicativeFn _).mp (q27_isMultiplicative_jordanAF k)
  refine ⟨?_, fun m n hm hn hmn ↦ ?_⟩
  · have h1 : ((jordanTotient k 1 : ℕ) : ℤ) = 1 := h.1
    exact_mod_cast h1
  · have h2 : ((jordanTotient k (m * n) : ℕ) : ℤ) = jordanTotient k m * jordanTotient k n :=
      h.2 m n hm hn hmn
    exact_mod_cast h2

/-- `J_k(p^{e+1}) = p^{(e+1)k} - p^{ek}`. -/
lemma q27_jordanTotient_prime_pow (k : ℕ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (jordanTotient k (p ^ (e + 1)) : ℤ) = (p : ℤ) ^ ((e + 1) * k) - (p : ℤ) ^ (e * k) := by
  have h1 := q27_sum_divisors_jordanTotient k (pow_pos hp.pos (e + 1))
  have h2 := q27_sum_divisors_jordanTotient k (pow_pos hp.pos e)
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ] at h1
  rw [Nat.sum_divisors_prime_pow hp] at h2
  rw [h2] at h1
  have h3 : jordanTotient k (p ^ (e + 1)) + p ^ (e * k) = p ^ ((e + 1) * k) := by
    rw [pow_mul, pow_mul]; omega
  rw [eq_sub_iff_add_eq]
  exact_mod_cast h3

end q27

/-- §27.3, first sentence: `d_k` is multiplicative (`k ≥ 1`). -/
@[dlmf 27.3]
theorem isMultiplicativeFn_divisorCountK (k : ℕ) (hk : 0 < k) :
    IsMultiplicativeFn (divisorCountK k) := by
  have h := (isMultiplicative_iff_isMultiplicativeFn _).mp
    (isMultiplicative_zeta.pow (k := k) : ((zeta : ArithmeticFunction ℕ) ^ k).IsMultiplicative)
  have he : divisorCountK k = ⇑((zeta : ArithmeticFunction ℕ) ^ k) :=
    funext (q27_divisorCountK_eq_zeta_pow k)
  rw [he]
  exact h

/-- §27.3, first sentence: Jordan's `J_k` is multiplicative (`k ≥ 1`). -/
@[dlmf 27.3]
theorem isMultiplicativeFn_jordanTotient (k : ℕ) (hk : 0 < k) :
    IsMultiplicativeFn (jordanTotient k) := by
  exact q27_isMultiplicativeFn_jordanTotient k

/-- Correction to §27.3, first sentence: `φ_k` is not multiplicative for `k ≥ 1`; for `k = 1`,
`φ₁(2) φ₁(3) = 3 ≠ 6 = φ₁(6)`. -/
@[dlmf 27.3]
theorem totientPowerSum_one_not_multiplicative :
    ¬ IsMultiplicativeFn (totientPowerSum 1) := by
  rintro ⟨-, h⟩
  have := h 2 3 (by norm_num) (by norm_num) (by norm_num)
  revert this
  decide

/-- DLMF 27.3.2: a multiplicative `f` is determined by its values at prime powers,
`f(n) = ∏_r f(p_r^{a_r})`. -/
@[dlmf 27.3.E2]
theorem IsMultiplicativeFn.eq_prod_primeFactors {R : Type*} [CommMonoidWithZero R]
    {f : ℕ → R} (hf : IsMultiplicativeFn f) {n : ℕ} (hn : n ≠ 0) :
    f n = ∏ p ∈ n.primeFactors, f (p ^ n.factorization p) := by
  have := Nat.multiplicative_factorization f (fun a b hab ↦ ?_) hf.1 hn
  · rw [this]; rfl
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [(Nat.coprime_zero_left _).mp hab, hf.1]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [(Nat.coprime_zero_right _).mp hab, hf.1]
    exact hf.2 a b ha hb hab

/-- DLMF 27.3.3: `φ(n) = n ∏_{p∣n} (1 - p⁻¹)`. -/
@[dlmf 27.3.E3]
theorem totient_eq_mul_prod (n : ℕ) :
    (n.totient : ℚ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) :=
  Nat.totient_eq_mul_prod_factors n

/-- DLMF 27.3.4: `J_k(n) = n^k ∏_{p∣n} (1 - p^{-k})`. -/
@[dlmf 27.3.E4]
theorem jordanTotient_eq_mul_prod (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    (jordanTotient k n : ℚ) = (n : ℚ) ^ k * ∏ p ∈ n.primeFactors, (1 - ((p : ℚ) ^ k)⁻¹) := by
  rw [(q27_isMultiplicativeFn_jordanTotient k).eq_prod_primeFactors hn.ne']
  have hnq : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ (n.factorization p) := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn.ne'
  rw [hnq, Nat.cast_prod, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  have he : n.factorization p ≠ 0 :=
    (hp'.factorization_pos_of_dvd hn.ne' (Nat.dvd_of_mem_primeFactors hp)).ne'
  obtain ⟨e, he'⟩ := Nat.exists_eq_succ_of_ne_zero he
  rw [he']
  have := q27_jordanTotient_prime_pow k hp' e
  have hq : ((jordanTotient k (p ^ (e + 1)) : ℤ) : ℚ) =
      (((p : ℤ) ^ ((e + 1) * k) - (p : ℤ) ^ (e * k) : ℤ) : ℚ) := by rw [this]
  push_cast at hq
  rw [hq]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp'.ne_zero
  rw [mul_sub, mul_one, ← pow_mul, mul_comm (e+1) k, mul_comm e k, mul_add, mul_one, pow_add]
  field_simp

/-- DLMF 27.3.5: `d(n) = ∏_r (1 + a_r)`. -/
@[dlmf 27.3.E5]
theorem sigma_zero_eq_prod {n : ℕ} (hn : n ≠ 0) :
    σ 0 n = ∏ p ∈ n.primeFactors, (1 + n.factorization p) := by
  rw [sigma_zero_apply, Nat.card_divisors hn]
  exact Finset.prod_congr rfl fun _ _ ↦ add_comm _ _

/-- DLMF 27.3.6: `σ_α(n) = ∏_r (p_r^{α(1+a_r)} - 1)/(p_r^α - 1)`. Stated under `p^α ≠ 1` for
every prime `p ∣ n`; DLMF's `α ≠ 0` suffices for real `α` but not for complex `α` (see the module
docstring). -/
@[dlmf 27.3.E6]
theorem sigmaC_eq_prod {α : ℂ} {n : ℕ} (hn : n ≠ 0)
    (hα : ∀ p ∈ n.primeFactors, (p : ℂ) ^ α ≠ 1) :
    sigmaC α n = ∏ p ∈ n.primeFactors,
      ((p : ℂ) ^ (α * (1 + n.factorization p)) - 1) / ((p : ℂ) ^ α - 1) := by
  rw [((isMultiplicative_iff_isMultiplicativeFn _).mp
    (isMultiplicative_sigmaC α)).eq_prod_primeFactors hn]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp'.ne_zero
  rw [eq_div_iff (sub_ne_zero.mpr (hα p hp))]
  change sigmaC α (p ^ n.factorization p) * _ = _
  rw [sigmaC_apply, Nat.divisors_prime_pow hp', Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hpow : ∀ i : ℕ, (((p ^ i : ℕ) : ℂ)) ^ α = ((p : ℂ) ^ α) ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]
  simp_rw [hpow]
  rw [geom_sum_mul, ← Complex.cpow_nat_mul]
  congr 2
  push_cast
  ring

/-- `G(m + n + 1) = G(m) + x^{m+1} G(n)` for `G(j) = ∑_{i ≤ j} x^i`. -/
lemma s27_geom_split {R : Type*} [CommRing R] (x : R) (m n : ℕ) :
    ∑ i ∈ range (m + n + 2), x ^ i =
      ∑ i ∈ range (m + 1), x ^ i + x ^ (m + 1) * ∑ i ∈ range (n + 1), x ^ i := by
  rw [show m + n + 2 = (m + 1) + (n + 1) by ring, sum_range_add, mul_sum]
  congr 1
  exact sum_congr rfl fun i _ ↦ by rw [pow_add]

/-- Prime-power case of 27.3.7: `∑_{k ≤ a} x^k G(2a + t - 2k) = G(a) G(a + t)`. -/
lemma s27_geom_hecke {R : Type*} [CommRing R] (x : R) (a t : ℕ) :
    ∑ k ∈ range (a + 1), x ^ k * ∑ i ∈ range (2 * a + t - 2 * k + 1), x ^ i =
      (∑ i ∈ range (a + 1), x ^ i) * ∑ i ∈ range (a + t + 1), x ^ i := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [sum_range_succ']
    have hsh : ∑ k ∈ range (a + 1), x ^ (k + 1) *
        ∑ i ∈ range (2 * (a + 1) + t - 2 * (k + 1) + 1), x ^ i =
        x * ∑ k ∈ range (a + 1), x ^ k * ∑ i ∈ range (2 * a + t - 2 * k + 1), x ^ i := by
      rw [mul_sum]
      refine sum_congr rfl fun k hk ↦ ?_
      have hk' : k ≤ a := Nat.lt_succ_iff.mp (mem_range.mp hk)
      rw [show 2 * (a + 1) + t - 2 * (k + 1) = 2 * a + t - 2 * k by omega, pow_succ]
      ring
    rw [hsh, ih]
    simp only [pow_zero, one_mul, Nat.mul_zero, Nat.sub_zero]
    -- G(a+1) G(a+1+t) = G(2a+2+t) + x G(a) G(a+t)
    have h1 : ∑ i ∈ range (a + 1 + 1), x ^ i = 1 + x * ∑ i ∈ range (a + 1), x ^ i := by
      rw [sum_range_succ', mul_sum]; simp [pow_succ, mul_comm, add_comm]
    have h2 : ∑ i ∈ range (a + 1 + t + 1), x ^ i =
        ∑ i ∈ range (a + t + 1), x ^ i + x ^ (a + t + 1) := by
      rw [show a + 1 + t + 1 = a + t + 1 + 1 by ring, sum_range_succ]
    have h3 := s27_geom_split x (a + t + 1) a
    rw [show a + t + 1 + a + 2 = 2 * (a + 1) + t + 1 by ring] at h3
    rw [h3, h1, h2, show a + t + 1 + 1 = a + 1 + t + 1 by ring, h2]
    ring

/-- `(p^i)^α = (p^α)^i`. -/
lemma s27_natPow_cpow (p i : ℕ) (α : ℂ) : (((p ^ i : ℕ) : ℂ)) ^ α = ((p : ℂ) ^ α) ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

/-- `σ_α(p^j) = ∑_{i ≤ j} (p^α)^i`. -/
lemma s27_sigmaC_prime_pow (α : ℂ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    sigmaC α (p ^ j) = ∑ i ∈ range (j + 1), ((p : ℂ) ^ α) ^ i := by
  rw [sigmaC_apply, Nat.sum_divisors_prime_pow hp]
  exact sum_congr rfl fun i _ ↦ s27_natPow_cpow p i α

/-- 27.3.7 for prime powers. -/
lemma s27_sigmaC_hecke_prime_pow (α : ℂ) {p : ℕ} (hp : p.Prime) (a b : ℕ) :
    ∑ d ∈ (p ^ min a b).divisors, (d : ℂ) ^ α * sigmaC α (p ^ (a + b) / d ^ 2) =
      sigmaC α (p ^ a) * sigmaC α (p ^ b) := by
  wlog hab : a ≤ b generalizing a b
  · rw [min_comm, add_comm, mul_comm]; exact this b a (by omega)
  obtain ⟨t, rfl⟩ : ∃ t, b = a + t := ⟨b - a, by omega⟩
  rw [min_eq_left hab, Nat.sum_divisors_prime_pow hp, s27_sigmaC_prime_pow α hp,
    s27_sigmaC_prime_pow α hp, ← s27_geom_hecke]
  refine sum_congr rfl fun k hk ↦ ?_
  have hk' : k ≤ a := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [s27_natPow_cpow, ← pow_mul, Nat.pow_div (by omega) hp.pos, s27_sigmaC_prime_pow α hp]
  congr 3
  omega

/-- `gcd(p^a m', p^b n') = p^{min(a,b)} gcd(m', n')` for `m', n'` coprime to `p`. -/
theorem s27_gcd_split {p a b m' n' : ℕ} (hm : p.Coprime m') (hn : p.Coprime n') :
    (p ^ a * m').gcd (p ^ b * n') = p ^ min a b * m'.gcd n' := by
  have h1 : (p ^ b).Coprime n' := Nat.Coprime.pow_left b hn
  have h2 : m'.Coprime (p ^ b) := (Nat.Coprime.pow_left b hm).symm
  have h3 : (p ^ a).Coprime n' := Nat.Coprime.pow_left a hn
  rw [Nat.Coprime.gcd_mul _ h1, Nat.Coprime.gcd_mul_right_cancel _ h2,
    Nat.Coprime.gcd_mul_left_cancel _ h3]
  congr 1
  rcases le_total a b with h | h
  · rw [min_eq_left h]; exact Nat.gcd_eq_left (Nat.pow_dvd_pow p h)
  · rw [min_eq_right h]; exact Nat.gcd_eq_right (Nat.pow_dvd_pow p h)

/-- Splitting off the `p`-part of the right side of 27.3.7. -/
lemma s27_hecke_split (α : ℂ) {p a b m' n' : ℕ} (hm : p.Coprime m')
    (hn : p.Coprime n') :
    ∑ d ∈ ((p ^ a * m').gcd (p ^ b * n')).divisors,
        (d : ℂ) ^ α * sigmaC α (p ^ a * m' * (p ^ b * n') / d ^ 2) =
      (∑ i ∈ (p ^ min a b).divisors, (i : ℂ) ^ α * sigmaC α (p ^ (a + b) / i ^ 2)) *
        ∑ j ∈ (m'.gcd n').divisors, (j : ℂ) ^ α * sigmaC α (m' * n' / j ^ 2) := by
  have hcop : (p ^ min a b).Coprime (m'.gcd n') :=
    Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left m' n') hm)
  rw [s27_gcd_split hm hn, Nat.divisors_mul, Finset.mul_def,
    sum_image (Nat.Coprime.mul_injOn_divisors hcop), sum_product, sum_mul_sum]
  refine sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ ?_
  have hi' : i ∣ p ^ min a b := Nat.dvd_of_mem_divisors hi
  have hj' : j ∣ m'.gcd n' := Nat.dvd_of_mem_divisors hj
  have hi2 : i ^ 2 ∣ p ^ (a + b) :=
    (pow_dvd_pow_of_dvd hi' 2).trans (by rw [← pow_mul]; exact Nat.pow_dvd_pow p (by omega))
  have hj2 : j ^ 2 ∣ m' * n' := by
    rw [sq]
    exact mul_dvd_mul (hj'.trans (Nat.gcd_dvd_left _ _)) (hj'.trans (Nat.gcd_dvd_right _ _))
  have hnum : p ^ a * m' * (p ^ b * n') / (i * j) ^ 2 =
      p ^ (a + b) / i ^ 2 * (m' * n' / j ^ 2) := by
    rw [Nat.div_mul_div_comm hi2 hj2, mul_pow]
    congr 1
    rw [pow_add]; ring
  have hc : (p ^ (a + b) / i ^ 2).Coprime (m' * n' / j ^ 2) := by
    have : (p ^ (a + b)).Coprime (m' * n') := Nat.Coprime.pow_left _ (Nat.Coprime.mul_right hm hn)
    exact (this.coprime_dvd_left (Nat.div_dvd_of_dvd hi2)).coprime_dvd_right
      (Nat.div_dvd_of_dvd hj2)
  rw [hnum, (isMultiplicative_sigmaC α).map_mul_of_coprime hc, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow]
  ring

/-- DLMF 27.3.7 (proof). -/
lemma s27_sigmaC_mul_sigmaC (α : ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    sigmaC α m * sigmaC α n =
      ∑ d ∈ (m.gcd n).divisors, (d : ℂ) ^ α * sigmaC α (m * n / d ^ 2) := by
  induction h : m * n using Nat.strong_induction_on generalizing m n with
  | _ N ih =>
  rw [← h]
  rcases Nat.lt_or_ge (m * n) 2 with hlt | hge
  · have hm1 : m = 1 := by nlinarith
    have hn1 : n = 1 := by nlinarith
    subst hm1 hn1
    simp [sigmaC_apply]
  set p := (m * n).minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpmn : p ∣ m * n := Nat.minFac_dvd _
  set a := m.factorization p
  set b := n.factorization p
  set m' := m / p ^ a
  set n' := n / p ^ b
  have hmm : p ^ a * m' = m := Nat.ordProj_mul_ordCompl_eq_self m p
  have hnn : p ^ b * n' = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hcm : p.Coprime m' := Nat.coprime_ordCompl hp hm.ne'
  have hcn : p.Coprime n' := Nat.coprime_ordCompl hp hn.ne'
  have hm' : 0 < m' := Nat.pos_of_ne_zero fun h0 ↦ by rw [h0, mul_zero] at hmm; omega
  have hn' : 0 < n' := Nat.pos_of_ne_zero fun h0 ↦ by rw [h0, mul_zero] at hnn; omega
  have hab : 1 ≤ a + b := by
    rcases (Nat.Prime.dvd_mul hp).mp hpmn with h1 | h1
    · have := hp.factorization_pos_of_dvd hm.ne' h1; omega
    · have := hp.factorization_pos_of_dvd hn.ne' h1; omega
  have hlt : m' * n' < N := by
    rw [← h, ← hmm, ← hnn]
    have hpow : 2 ≤ p ^ a * p ^ b := by
      rw [← pow_add]
      calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (a + b) := Nat.pow_le_pow_right hp.pos hab
    have : 0 < m' * n' := Nat.mul_pos hm' hn'
    nlinarith
  have ih' := ih (m' * n') hlt hm' hn' rfl
  rw [← hmm, ← hnn, s27_hecke_split α hcm hcn, ← ih',
    s27_sigmaC_hecke_prime_pow α hp,
    (isMultiplicative_sigmaC α).map_mul_of_coprime (Nat.Coprime.pow_left a hcm),
    (isMultiplicative_sigmaC α).map_mul_of_coprime (Nat.Coprime.pow_left b hcn)]
  ring

/-- DLMF 27.3.7: `σ_α(m) σ_α(n) = ∑_{d∣(m,n)} d^α σ_α(mn/d²)`. -/
@[dlmf 27.3.E7]
theorem sigmaC_mul_sigmaC (α : ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    sigmaC α m * sigmaC α n =
      ∑ d ∈ (m.gcd n).divisors, (d : ℂ) ^ α * sigmaC α (m * n / d ^ 2) :=
  s27_sigmaC_mul_sigmaC α hm hn

/-- DLMF 27.3.8: `φ(m) φ(n) = φ(mn) φ((m,n))/(m,n)`. -/
@[dlmf 27.3.E8]
theorem totient_mul_totient (m n : ℕ) (hm : 0 < m) :
    (m.totient * n.totient : ℚ) = (m * n).totient * (m.gcd n).totient / m.gcd n := by
  have hg : (m.gcd n : ℚ) ≠ 0 := by exact_mod_cast (Nat.gcd_pos_of_pos_left n hm).ne'
  rw [eq_div_iff hg]
  exact_mod_cast (by rw [mul_comm ((m * n).totient), Nat.totient_gcd_mul_totient_mul] :
    (m * n).totient * (m.gcd n).totient = m.totient * n.totient * m.gcd n).symm

/-- DLMF 27.3.10: a completely multiplicative `f` satisfies `f(n) = ∏_r f(p_r)^{a_r}`. -/
@[dlmf 27.3.E10]
theorem IsCompletelyMultiplicativeFn.eq_prod_primeFactors {R : Type*} [CommMonoidWithZero R]
    {f : ℕ → R} (hf : IsCompletelyMultiplicativeFn f) {n : ℕ} (hn : n ≠ 0) :
    f n = ∏ p ∈ n.primeFactors, f p ^ n.factorization p := by
  rw [hf.isMultiplicativeFn.eq_prod_primeFactors hn]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
  induction n.factorization p with
  | zero => simp [hf.1]
  | succ a ih => rw [pow_succ, hf.2 _ _ (pow_pos hp0 a) hp0, ih, pow_succ]

end DLMF.NumberTheory
