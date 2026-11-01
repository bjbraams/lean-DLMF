/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.NumberTheory.Basic.Functions
public import Mathlib.Algebra.Order.Antidiag.Nat
public import Mathlib.Data.Finset.NatDivisors
public import Mathlib.NumberTheory.ArithmeticFunction.Liouville

/-!
# Multiplicative properties of number-theoretic functions (DLMF §27.3)

DLMF §27.3 describes the multiplicative properties of the functions of §27.2. The functions
themselves, their defining formulas (§27.2) and DLMF's notions `IsMultiplicativeFn` and
`IsCompletelyMultiplicativeFn` (DLMF 27.3.1, 27.3.9) are in the foundational module
`DLMF.NumberTheory.Basic.Functions`.

## Main definitions

* `jordanArithmeticFunction`: Jordan's function `J_k` as an arithmetic function.

## Main results

* `isCompletelyMultiplicativeFn_floor_one_div`, `isCompletelyMultiplicativeFn_liouville`:
  completely multiplicative examples (DLMF 27.3.9).
* `isMultiplicativeFn_basic`, `isMultiplicativeFn_divisorCountK`,
  `isMultiplicativeFn_jordanTotient`, `totientPowerSum_one_not_multiplicative`: which functions
  of §27.2 are multiplicative (corrected, see below).
* `divisorCountK_eq_zeta_pow`, `sum_divisors_jordanTotient_eq_pow`: `d_k = ζ^k` and
  `∑_{d∣n} J_k(d) = n^k`.
* `IsMultiplicativeFn.eq_prod_primeFactors`, `IsCompletelyMultiplicativeFn.eq_prod_primeFactors`:
  DLMF 27.3.2 and 27.3.10.
* `jordanTotient_eq_mul_prod`, `sigma_zero_eq_prod`, `sigmaC_eq_prod`: the product formulas
  DLMF 27.3.4–27.3.6.
* `sigmaC_mul_sigmaC`, `totient_mul_totient`: DLMF 27.3.7 and 27.3.8.

## Implementation notes

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

/-! ### §27.3 Multiplicative properties -/

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

section ArithmeticFunctions
open scoped ArithmeticFunction.zeta

/-- Recursion for the ordered factorizations: split off the first factor. -/
private lemma card_finMulAntidiag_succ (k n : ℕ) :
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
theorem divisorCountK_eq_zeta_pow (k n : ℕ) :
    divisorCountK k n = ((ζ : ArithmeticFunction ℕ) ^ k) n := by
  induction k generalizing n with
  | zero =>
    rw [pow_zero, one_apply, divisorCountK]
    split_ifs with h
    · subst h; rw [Nat.finMulAntidiag_one, card_singleton]
    · rw [Nat.finMulAntidiag_zero_left h, card_empty]
  | succ k ih =>
    rw [divisorCountK, card_finMulAntidiag_succ, pow_succ', mul_apply]
    refine sum_congr rfl fun ab hab ↦ ?_
    rw [← divisorCountK, ih, zeta_apply, ite_eq_right (Nat.ne_of_gt (Nat.pos_of_mem_divisors
      (Nat.fst_mem_divisors_of_mem_antidiagonal hab))), one_mul]

/-- `∑_{d∣n} J_k(d) = n^k` (DLMF 27.6.3), proved here for use in §27.3. -/
theorem sum_divisors_jordanTotient_eq_pow (k : ℕ) {n : ℕ} (hn : 0 < n) :
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
private lemma jordanTotient_zero_right (k : ℕ) : jordanTotient k 0 = 0 := by
  rcases k with _ | k
  · decide
  · simp [jordanTotient]

/-- Jordan's totient as an integer-valued arithmetic function. -/
def jordanArithmeticFunction (k : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n ↦ jordanTotient k n, by simp [jordanTotient_zero_right]⟩

/-- Möbius inversion of `∑_{d∣n} J_k(d) = n^k`: `J_k = μ * n^k`. -/
private lemma jordanArithmeticFunction_eq_moebius_mul_pow (k : ℕ) :
    jordanArithmeticFunction k = (μ : ArithmeticFunction ℤ) * (pow k : ArithmeticFunction ℤ) := by
  have h : (ζ : ArithmeticFunction ℤ) * jordanArithmeticFunction k = (pow k : ArithmeticFunction ℤ) := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [coe_zeta_mul_apply, natCoe_apply, pow_apply, ite_eq_right (by omega)]
    change ∑ i ∈ n.divisors, ((jordanTotient k i : ℕ) : ℤ) = _
    exact_mod_cast sum_divisors_jordanTotient_eq_pow k hn
  rw [← h, ← mul_assoc, moebius_mul_coe_zeta, one_mul]

/-- `J_k` is multiplicative. -/
private lemma isMultiplicative_jordanArithmeticFunction (k : ℕ) : (jordanArithmeticFunction k).IsMultiplicative := by
  rw [jordanArithmeticFunction_eq_moebius_mul_pow]
  exact isMultiplicative_moebius.mul isMultiplicative_pow.natCast

/-- `J_k` is multiplicative (all `k`). -/
private lemma isMultiplicativeFn_jordanTotient' (k : ℕ) :
    IsMultiplicativeFn (jordanTotient k) := by
  have h := (isMultiplicative_iff_isMultiplicativeFn _).mp (isMultiplicative_jordanArithmeticFunction k)
  refine ⟨?_, fun m n hm hn hmn ↦ ?_⟩
  · have h1 : ((jordanTotient k 1 : ℕ) : ℤ) = 1 := h.1
    exact_mod_cast h1
  · have h2 : ((jordanTotient k (m * n) : ℕ) : ℤ) = jordanTotient k m * jordanTotient k n :=
      h.2 m n hm hn hmn
    exact_mod_cast h2

/-- `J_k(p^{e+1}) = p^{(e+1)k} - p^{ek}`. -/
private lemma jordanTotient_prime_pow_succ (k : ℕ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (jordanTotient k (p ^ (e + 1)) : ℤ) = (p : ℤ) ^ ((e + 1) * k) - (p : ℤ) ^ (e * k) := by
  have h1 := sum_divisors_jordanTotient_eq_pow k (pow_pos hp.pos (e + 1))
  have h2 := sum_divisors_jordanTotient_eq_pow k (pow_pos hp.pos e)
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ] at h1
  rw [Nat.sum_divisors_prime_pow hp] at h2
  rw [h2] at h1
  have h3 : jordanTotient k (p ^ (e + 1)) + p ^ (e * k) = p ^ ((e + 1) * k) := by
    rw [pow_mul, pow_mul]; omega
  rw [eq_sub_iff_add_eq]
  exact_mod_cast h3

end ArithmeticFunctions
/-- §27.3, first sentence: `d_k` is multiplicative, for every `k` (DLMF: `k ≥ 1`). -/
@[dlmf 27.3]
theorem isMultiplicativeFn_divisorCountK (k : ℕ) :
    IsMultiplicativeFn (divisorCountK k) := by
  have h := (isMultiplicative_iff_isMultiplicativeFn _).mp
    (isMultiplicative_zeta.pow (k := k) : ((zeta : ArithmeticFunction ℕ) ^ k).IsMultiplicative)
  have he : divisorCountK k = ⇑((zeta : ArithmeticFunction ℕ) ^ k) :=
    funext (divisorCountK_eq_zeta_pow k)
  rw [he]
  exact h

/-- §27.3, first sentence: Jordan's `J_k` is multiplicative, for every `k` (DLMF: `k ≥ 1`). -/
@[dlmf 27.3]
theorem isMultiplicativeFn_jordanTotient (k : ℕ) :
    IsMultiplicativeFn (jordanTotient k) := by
  exact isMultiplicativeFn_jordanTotient' k

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


/-- DLMF 27.3.4: `J_k(n) = n^k ∏_{p∣n} (1 - p^{-k})`. -/
@[dlmf 27.3.E4]
theorem jordanTotient_eq_mul_prod (k n : ℕ) (hn : 0 < n) :
    (jordanTotient k n : ℚ) = (n : ℚ) ^ k * ∏ p ∈ n.primeFactors, (1 - ((p : ℚ) ^ k)⁻¹) := by
  rw [(isMultiplicativeFn_jordanTotient' k).eq_prod_primeFactors hn.ne']
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
  have := jordanTotient_prime_pow_succ k hp' e
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
private lemma geom_sum_range_add_add_two {R : Type*} [CommRing R] (x : R) (m n : ℕ) :
    ∑ i ∈ range (m + n + 2), x ^ i =
      ∑ i ∈ range (m + 1), x ^ i + x ^ (m + 1) * ∑ i ∈ range (n + 1), x ^ i := by
  rw [show m + n + 2 = (m + 1) + (n + 1) by ring, sum_range_add, mul_sum]
  congr 1
  exact sum_congr rfl fun i _ ↦ by rw [pow_add]

/-- Prime-power case of 27.3.7: `∑_{k ≤ a} x^k G(2a + t - 2k) = G(a) G(a + t)`. -/
private lemma sum_pow_mul_geom_sum_eq_mul_geom_sum {R : Type*} [CommRing R] (x : R) (a t : ℕ) :
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
    have h3 := geom_sum_range_add_add_two x (a + t + 1) a
    rw [show a + t + 1 + a + 2 = 2 * (a + 1) + t + 1 by ring] at h3
    rw [h3, h1, h2, show a + t + 1 + 1 = a + 1 + t + 1 by ring, h2]
    ring

/-- `(p^i)^α = (p^α)^i`. -/
private lemma natCast_pow_cpow (p i : ℕ) (α : ℂ) : (((p ^ i : ℕ) : ℂ)) ^ α = ((p : ℂ) ^ α) ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

/-- `σ_α(p^j) = ∑_{i ≤ j} (p^α)^i`. -/
private lemma sigmaC_prime_pow (α : ℂ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    sigmaC α (p ^ j) = ∑ i ∈ range (j + 1), ((p : ℂ) ^ α) ^ i := by
  rw [sigmaC_apply, Nat.sum_divisors_prime_pow hp]
  exact sum_congr rfl fun i _ ↦ natCast_pow_cpow p i α

/-- 27.3.7 for prime powers. -/
private lemma sum_divisors_cpow_mul_sigmaC_prime_pow (α : ℂ) {p : ℕ} (hp : p.Prime) (a b : ℕ) :
    ∑ d ∈ (p ^ min a b).divisors, (d : ℂ) ^ α * sigmaC α (p ^ (a + b) / d ^ 2) =
      sigmaC α (p ^ a) * sigmaC α (p ^ b) := by
  wlog hab : a ≤ b generalizing a b
  · rw [min_comm, add_comm, mul_comm]; exact this b a (by omega)
  obtain ⟨t, rfl⟩ : ∃ t, b = a + t := ⟨b - a, by omega⟩
  rw [min_eq_left hab, Nat.sum_divisors_prime_pow hp, sigmaC_prime_pow α hp,
    sigmaC_prime_pow α hp, ← sum_pow_mul_geom_sum_eq_mul_geom_sum]
  refine sum_congr rfl fun k hk ↦ ?_
  have hk' : k ≤ a := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [natCast_pow_cpow, ← pow_mul, Nat.pow_div (by omega) hp.pos, sigmaC_prime_pow α hp]
  congr 3
  omega

/-- `gcd(p^a m', p^b n') = p^{min(a,b)} gcd(m', n')` for `m', n'` coprime to `p`. -/
theorem gcd_prime_pow_mul_prime_pow_mul {p a b m' n' : ℕ} (hm : p.Coprime m') (hn : p.Coprime n') :
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
private lemma sum_divisors_gcd_cpow_mul_sigmaC_split (α : ℂ) {p a b m' n' : ℕ} (hm : p.Coprime m')
    (hn : p.Coprime n') :
    ∑ d ∈ ((p ^ a * m').gcd (p ^ b * n')).divisors,
        (d : ℂ) ^ α * sigmaC α (p ^ a * m' * (p ^ b * n') / d ^ 2) =
      (∑ i ∈ (p ^ min a b).divisors, (i : ℂ) ^ α * sigmaC α (p ^ (a + b) / i ^ 2)) *
        ∑ j ∈ (m'.gcd n').divisors, (j : ℂ) ^ α * sigmaC α (m' * n' / j ^ 2) := by
  have hcop : (p ^ min a b).Coprime (m'.gcd n') :=
    Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left m' n') hm)
  rw [gcd_prime_pow_mul_prime_pow_mul hm hn, Nat.divisors_mul, Finset.mul_def,
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
lemma sigmaC_mul_sigmaC_eq_sum_divisors_gcd (α : ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
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
  rw [← hmm, ← hnn, sum_divisors_gcd_cpow_mul_sigmaC_split α hcm hcn, ← ih',
    sum_divisors_cpow_mul_sigmaC_prime_pow α hp,
    (isMultiplicative_sigmaC α).map_mul_of_coprime (Nat.Coprime.pow_left a hcm),
    (isMultiplicative_sigmaC α).map_mul_of_coprime (Nat.Coprime.pow_left b hcn)]
  ring

/-- DLMF 27.3.7: `σ_α(m) σ_α(n) = ∑_{d∣(m,n)} d^α σ_α(mn/d²)`. -/
@[dlmf 27.3.E7]
theorem sigmaC_mul_sigmaC (α : ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    sigmaC α m * sigmaC α n =
      ∑ d ∈ (m.gcd n).divisors, (d : ℂ) ^ α * sigmaC α (m * n / d ^ 2) :=
  sigmaC_mul_sigmaC_eq_sum_divisors_gcd α hm hn

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
