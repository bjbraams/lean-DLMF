/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.NumberTheory.Inversion

/-!
# Divisor sums and Lambert series (DLMF §§27.6–27.7)

Divisor sums are written `∑ d ∈ n.divisors, …`; DLMF's `∑_{d²∣n}` is the sum over the divisors
`d` of `n` with `d² ∣ n`. DLMF 27.6.2 is stated by DLMF for `n > 1`; it holds for `n = 1` as
well and is proved for all `n ≥ 1`. Lambert series (27.7.1) are written with the index shifted
to `n + 1 ≥ 1`; for `|x| < 1` every series of §27.7 converges absolutely, and the identities
are stated with `HasSum`. Mathlib's `tsum_pow_div_one_sub_eq_tsum_sigma` is 27.7.5 for natural
`α` (as an equality of `tsum`s over `ℕ+`).
-/

@[expose] public noncomputable section

open Finset Filter ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.Moebius ArithmeticFunction.omega
  ArithmeticFunction.zeta

namespace DLMF.NumberTheory

/-! ### §27.6 Divisor sums -/

/-- DLMF 27.6.1: `∑_{d∣n} λ(d)` is `1` if `n` is a square and `0` otherwise. -/
@[dlmf 27.6.E1]
theorem sum_divisors_liouville {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, liouville d = if IsSquare n then 1 else 0 := by
  have hn0 : n ≠ 0 := hn.ne'
  set g : ArithmeticFunction ℤ := liouville * ζ with hgdef
  have hg : g.IsMultiplicative := isMultiplicative_liouville.mul isMultiplicative_zeta.natCast
  have hgn : ∀ m, g m = ∑ d ∈ m.divisors, liouville d := fun m ↦ by
    rw [hgdef, coe_mul_zeta_apply]
  have hpp : ∀ p a, p.Prime → g (p ^ a) = if Even a then 1 else 0 := by
    intro p a hp
    rw [hgn, Nat.divisors_prime_pow hp, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk]
    have h1 : ∀ i, liouville (p ^ i) = (-1) ^ i := fun i ↦ by
      rw [liouville_apply (pow_ne_zero _ hp.ne_zero), cardFactors_apply_prime_pow hp]
    simp_rw [h1]
    induction a with
    | zero => simp
    | succ a ih =>
      rw [Finset.sum_range_succ, ih]
      rcases Nat.even_or_odd a with h | h
      · simp [h, Nat.even_add_one, pow_succ, h.neg_one_pow]
      · simp [h, pow_succ, h.neg_one_pow, Nat.not_even_iff_odd.mpr h]
  rw [← hgn, hg.multiplicative_factorization g hn0, Nat.prod_factorization_eq_prod_primeFactors,
    Finset.prod_congr rfl (fun p hp ↦ hpp p _ (Nat.prime_of_mem_primeFactors hp)),
    Finset.prod_boole]
  congr 1
  apply propext
  rw [Nat.isSquare_iff_even_factorization]
  constructor
  · intro h p hp
    by_cases hpn : p ∈ n.primeFactors
    · exact h p hpn
    · rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hpn
      rw [hpn]
      exact Even.zero
  · intro h p hp
    exact h p (Nat.prime_of_mem_primeFactors hp)

/-- The prime power case of 27.6.2: `∑_{d∣p^k} μ(d) g(d) = g(1) - g(p)` for `k ≥ 1`. -/
lemma n27_sum_divisors_prime_pow_moebius_mul {R : Type*} [CommRing R] (g : ℕ → R)
    {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    ∑ d ∈ (p ^ k).divisors, (μ d : R) * g d = g 1 - g p := by
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [Finset.sum_range_succ']
  have h : ∀ i ∈ range (k + 1), (μ (p ^ (i + 1)) : R) * g (p ^ (i + 1)) =
      if i = 0 then -g p else 0 := by
    intro i _
    rw [moebius_apply_prime_pow hp (Nat.succ_ne_zero i)]
    split_ifs with h1 h2 h2
    · subst h2; simp
    · omega
    · omega
    · simp
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' (range (k + 1)) 0]
  simp
  ring

/-- DLMF 27.6.2: for multiplicative `f`, `∑_{d∣n} μ(d) f(d) = ∏_{p∣n} (1 - f(p))`, for all
`n ≥ 1` (DLMF states `n > 1`). -/
@[dlmf 27.6.E2]
theorem sum_divisors_moebius_mul {R : Type*} [CommRing R] (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (μ d : R) * f d = ∏ p ∈ n.primeFactors, (1 - f p) := by
  set g : ArithmeticFunction R := ((μ : ArithmeticFunction R).pmul f) * ζ with hgdef
  have hg : g.IsMultiplicative := (isMultiplicative_moebius.intCast.pmul hf).mul
    isMultiplicative_zeta.natCast
  have hgn : ∀ m, g m = ∑ d ∈ m.divisors, (μ d : R) * f d := by
    intro m
    rw [hgdef, coe_mul_zeta_apply]
    simp [pmul_apply, intCoe_apply]
  rw [← hgn, hg.multiplicative_factorization g hn, Nat.prod_factorization_eq_prod_primeFactors]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  rw [hgn, n27_sum_divisors_prime_pow_moebius_mul f hp'
    (hp'.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)).ne', hf.1]

/-- DLMF 27.6.3: `∑_{d∣n} |μ(d)| = 2^{ν(n)}`. -/
@[dlmf 27.6.E3]
theorem sum_divisors_abs_moebius {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, |μ d| = 2 ^ ω n := by
  have h := sum_divisors_moebius_mul (R := ℤ) liouville isMultiplicative_liouville hn
  have habs : ∀ d ∈ n.divisors, |μ d| = (μ d : ℤ) * liouville d := by
    intro d hd
    have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    by_cases hsq : Squarefree d
    · rw [moebius_apply_of_squarefree hsq, liouville_apply hd0, ← pow_add, ← two_mul,
        pow_mul]
      simp
    · simp [moebius_eq_zero_of_not_squarefree hsq]
  rw [Finset.sum_congr rfl habs]
  simp only [Int.cast_id] at h
  rw [h, (prod_primeFactors_pow_factorization hn).2]
  rw [Finset.prod_congr rfl fun p hp ↦ by
    rw [show liouville p = -1 by
      rw [liouville_apply (Nat.prime_of_mem_primeFactors hp).ne_zero,
        cardFactors_apply_prime (Nat.prime_of_mem_primeFactors hp)]; rfl]]
  simp

/-- `λ(d)/φ(d)` as a rational arithmetic function. -/
def q27_liouvilleDivTotient : ArithmeticFunction ℚ :=
  ⟨fun d ↦ (liouville d : ℚ) / d.totient, by simp⟩

/-- `λ/φ` is multiplicative. -/
lemma q27_isMultiplicative_liouvilleDivTotient : q27_liouvilleDivTotient.IsMultiplicative := by
  refine ⟨by simp [q27_liouvilleDivTotient, liouville_apply_one], fun {m n} hmn ↦ ?_⟩
  change (liouville (m * n) : ℚ) / (m * n).totient =
    (liouville m : ℚ) / m.totient * ((liouville n : ℚ) / n.totient)
  rw [liouville_apply_mul, Nat.totient_mul hmn]
  push_cast
  rw [mul_div_mul_comm]

/-- DLMF 27.6.5 (proof). -/
lemma q27_sum_divisors_abs_moebius_div_totient {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (|μ d| : ℚ) / d.totient = n / n.totient := by
  have h := sum_divisors_moebius_mul (R := ℚ) q27_liouvilleDivTotient
    q27_isMultiplicative_liouvilleDivTotient hn
  have habs : ∀ d ∈ n.divisors, (|μ d| : ℚ) / d.totient =
      (μ d : ℚ) * q27_liouvilleDivTotient d := by
    intro d hd
    have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    change _ = (μ d : ℚ) * ((liouville d : ℚ) / d.totient)
    rw [← mul_div_assoc]
    congr 1
    by_cases hsq : Squarefree d
    · rw [moebius_apply_of_squarefree hsq, liouville_apply hd0]
      rcases neg_one_pow_eq_or ℤ (cardFactors d) with h | h <;> simp [h]
    · simp [moebius_eq_zero_of_not_squarefree hsq]
  rw [sum_congr rfl habs, h]
  have ht := Nat.totient_eq_mul_prod_factors n
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hprod : ∀ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) ≠ 0 := by
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).one_lt
    have h1 : (1 : ℚ) < p := by exact_mod_cast this
    have : (p : ℚ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
    linarith
  rw [ht, div_mul_cancel_left₀ hn', ← prod_inv_distrib]
  refine prod_congr rfl fun p hp ↦ ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  change 1 - (liouville p : ℚ) / p.totient = _
  rw [liouville_apply hp'.ne_zero, cardFactors_apply_prime hp', Nat.totient_prime hp',
    Nat.cast_sub hp'.one_le]
  have h1 : (1 : ℚ) < p := by exact_mod_cast hp'.one_lt
  have h2 : (p : ℚ) - 1 ≠ 0 := by linarith
  have h3 : (p : ℚ) ≠ 0 := by linarith
  have e : (1 - (p : ℚ)⁻¹) = (p - 1) / p := by field_simp
  rw [e, inv_div, pow_one, Int.cast_neg, Int.cast_one, Nat.cast_one, neg_div, sub_neg_eq_add,
    eq_div_iff h2, add_mul, div_mul_cancel₀ _ h2]
  ring

/-- DLMF 27.6.6 (proof): group `m ≤ n` by `n/(m,n)`. -/
lemma q27_sum_divisors_totientPowerSum (k n : ℕ) :
    ∑ d ∈ n.divisors, totientPowerSum k d * (n / d) ^ k = ∑ m ∈ Finset.Icc 1 n, m ^ k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [← sum_fiberwise_of_maps_to (g := fun m ↦ n / Nat.gcd m n) (t := n.divisors)
    (s := Icc 1 n) (f := fun m ↦ m ^ k)]
  · refine sum_congr rfl fun e he ↦ ?_
    obtain ⟨c, hc⟩ := Nat.dvd_of_mem_divisors he
    have he0 : 0 < e := Nat.pos_of_mem_divisors he
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [h, mul_zero] at hc; omega
      · exact h
    have hne : n / e = c := by rw [hc, Nat.mul_div_cancel_left _ he0]
    have hg : ∀ m, n / Nat.gcd m n = e → Nat.gcd m n = c := by
      intro m hm
      obtain ⟨t, ht⟩ := Nat.gcd_dvd_right m n
      have hg0 := Nat.gcd_pos_of_pos_right m hn
      set g := Nat.gcd m n
      rw [ht, Nat.mul_div_cancel_left _ hg0] at hm
      rw [hm] at ht
      rw [ht, mul_comm] at hc
      exact Nat.eq_of_mul_eq_mul_left he0 hc
    rw [hne, totientPowerSum, sum_mul]
    symm
    refine sum_nbij' (fun m ↦ m / c) (fun r ↦ c * r) ?_ ?_ ?_ ?_ ?_
    · intro m hm
      rw [mem_filter, mem_Icc] at hm
      have hgc := hg m hm.2
      have hcm : c ∣ m := hgc ▸ Nat.gcd_dvd_left m n
      obtain ⟨t, rfl⟩ := hcm
      rw [mem_filter, mem_Icc, Nat.mul_div_cancel_left _ hc0]
      have ht0 : 0 < t := by
        rcases Nat.eq_zero_or_pos t with h | h
        · rw [h, mul_zero] at hm; omega
        · exact h
      refine ⟨⟨ht0, ?_⟩, ?_⟩
      · rw [hc, mul_comm e c] at hm
        exact Nat.le_of_mul_le_mul_left hm.1.2 hc0
      · rw [hc, mul_comm e c, Nat.gcd_mul_left] at hgc
        exact Nat.eq_of_mul_eq_mul_left hc0 (hgc.trans (mul_one c).symm)
    · intro r hr
      rw [mem_filter, mem_Icc] at hr
      rw [mem_filter, mem_Icc]
      refine ⟨⟨by nlinarith, ?_⟩, ?_⟩
      · rw [hc, mul_comm e c]; exact Nat.mul_le_mul_left c hr.1.2
      · rw [hc, mul_comm e c, Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hr.2, mul_one,
          Nat.mul_div_cancel_left _ hc0]
    · intro m hm
      rw [mem_filter] at hm
      exact Nat.mul_div_cancel' ((hg m hm.2) ▸ Nat.gcd_dvd_left m n)
    · intro r _
      exact Nat.mul_div_cancel_left _ hc0
    · intro m hm
      rw [mem_filter] at hm
      obtain ⟨t, ht⟩ : c ∣ m := (hg m hm.2) ▸ Nat.gcd_dvd_left m n
      rw [ht, Nat.mul_div_cancel_left _ hc0, mul_pow, mul_comm]
  · intro m _
    rw [Nat.mem_divisors]
    exact ⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _), hn.ne'⟩

/-- DLMF 27.6.4: `∑_{d² ∣ n} μ(d) = |μ(n)|`. -/
@[dlmf 27.6.E4]
theorem sum_sq_dvd_moebius {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors with d ^ 2 ∣ n, μ d = |μ n| :=
  q27_sum_sq_dvd_moebius hn

/-- DLMF 27.6.5: `∑_{d∣n} |μ(d)|/φ(d) = n/φ(n)`. -/
@[dlmf 27.6.E5]
theorem sum_divisors_abs_moebius_div_totient {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (|μ d| : ℚ) / d.totient = n / n.totient :=
  q27_sum_divisors_abs_moebius_div_totient hn

/-- DLMF 27.6.6: `∑_{d∣n} φ_k(d) (n/d)^k = 1^k + 2^k + ⋯ + n^k`. -/
@[dlmf 27.6.E6]
theorem sum_divisors_totientPowerSum (k n : ℕ) :
    ∑ d ∈ n.divisors, totientPowerSum k d * (n / d) ^ k = ∑ m ∈ Finset.Icc 1 n, m ^ k :=
  q27_sum_divisors_totientPowerSum k n

/-- DLMF 27.6.8: `∑_{d∣n} J_k(d) = n^k`. -/
@[dlmf 27.6.E8]
theorem sum_divisors_jordanTotient (k : ℕ) {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, jordanTotient k d = n ^ k :=
  q27_sum_divisors_jordanTotient k hn

/-- DLMF 27.6.7: `∑_{d∣n} μ(d) (n/d)^k = J_k(n)`; the Möbius inverse of 27.6.8. -/
@[dlmf 27.6.E7]
theorem sum_divisors_moebius_pow (k : ℕ) {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, μ d * ((n / d : ℕ) : ℤ) ^ k = jordanTotient k n := by
  have h := (moebius_inversion (fun n ↦ (jordanTotient k n : ℤ)) (fun n ↦ (n : ℤ) ^ k)).mp
    (fun m hm ↦ by exact_mod_cast (sum_divisors_jordanTotient k hm).symm) n hn
  rw [h, ← Nat.sum_div_divisors n (fun d ↦ (μ d : ℤ) * ((n / d : ℕ) : ℤ) ^ k)]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hn.ne']
  push_cast
  ring

/-! ### §27.7 Lambert series as generating functions -/

/-- DLMF 27.7.1: the Lambert series `∑_{n≥1} f(n) xⁿ/(1 - xⁿ)` (a totalized `tsum`; the
statements below assert convergence). -/
@[dlmf 27.7.E1]
def lambertSeries (f : ℕ → ℂ) (x : ℂ) : ℂ :=
  ∑' n : ℕ, f (n + 1) * x ^ (n + 1) / (1 - x ^ (n + 1))

/-- `∑_{b≥1} y^b = y/(1 - y)` for `‖y‖ < 1`, over `ℕ+`. -/
lemma q27_hasSum_geometric_pnat {K : Type*} [NormedDivisionRing K] [CompleteSpace K]
    {y : K} (hy : ‖y‖ < 1) : HasSum (fun b : ℕ+ ↦ y ^ (b : ℕ)) (y * (1 - y)⁻¹) := by
  rw [← (Equiv.pnatEquivNat.symm.hasSum_iff (f := fun b : ℕ+ ↦ y ^ (b : ℕ)))]
  have := (hasSum_geometric_of_norm_lt_one hy).mul_left y
  convert this using 1
  funext n
  simp [Equiv.pnatEquivNat, pow_succ']

/-- Lambert series rearrangement: the double series `∑_{a,b≥1} f(a) x^{ab}` summed by rows and
by diagonals. -/
lemma q27_lambert_core (f : ℕ → ℂ) {x : ℂ} (hx : ‖x‖ < 1)
    (hf : Summable fun n : ℕ ↦ ‖f (n + 1)‖ * ‖x‖ ^ (n + 1)) :
    HasSum (fun n : ℕ ↦ f (n + 1) * x ^ (n + 1) / (1 - x ^ (n + 1)))
        (∑' c : ℕ+ × ℕ+, f c.1 * x ^ ((c.1 : ℕ) * c.2)) ∧
      HasSum (fun n : ℕ ↦ (∑ d ∈ (n + 1).divisors, f d) * x ^ (n + 1))
        (∑' c : ℕ+ × ℕ+, f c.1 * x ^ ((c.1 : ℕ) * c.2)) := by
  set r := ‖x‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg x
  have hpow : ∀ a : ℕ+, ‖x ^ (a : ℕ)‖ < 1 := fun a ↦ by
    rw [norm_pow]; exact pow_lt_one₀ hr0 hx a.ne_zero
  set c : ℕ+ × ℕ+ → ℂ := fun c ↦ f c.1 * x ^ ((c.1 : ℕ) * c.2) with hc
  have hrow : ∀ a : ℕ+, HasSum (fun b ↦ c (a, b))
      (f a * (x ^ (a : ℕ) * (1 - x ^ (a : ℕ))⁻¹)) := by
    intro a
    have := (q27_hasSum_geometric_pnat (hpow a)).mul_left (f a)
    convert this using 2 with b
    simp only [hc, pow_mul]
  have hsumm : Summable c := by
    refine Summable.of_norm ?_
    have hnn : 0 ≤ fun c' ↦ ‖c c'‖ := fun _ ↦ norm_nonneg _
    refine (summable_prod_of_nonneg hnn).mpr ⟨fun a ↦ ?_, ?_⟩
    · exact ((hrow a).summable.norm)
    · have hra : ∀ a : ℕ+, ∑' b, ‖c (a, b)‖ ≤ ‖f a‖ * r ^ (a : ℕ) * (1 - r)⁻¹ := by
        intro a
        have hr1 : r ^ (a : ℕ) < 1 := pow_lt_one₀ hr0 hx a.ne_zero
        have hg := (q27_hasSum_geometric_pnat (K := ℝ) (y := r ^ (a : ℕ))
          (by rw [Real.norm_of_nonneg (pow_nonneg hr0 _)]; exact hr1)).mul_left ‖f a‖
        have : HasSum (fun b ↦ ‖c (a, b)‖) (‖f a‖ * (r ^ (a : ℕ) * (1 - r ^ (a : ℕ))⁻¹)) := by
          convert hg using 2 with b
          simp only [hc, norm_mul, norm_pow, pow_mul, hr]
        rw [this.tsum_eq, ← mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h1r : 0 < 1 - r := by linarith
        refine inv_anti₀ h1r ?_
        have : r ^ (a : ℕ) ≤ r := pow_le_of_le_one hr0 hx.le a.ne_zero
        linarith
      refine Summable.of_nonneg_of_le (fun a ↦ tsum_nonneg fun b ↦ norm_nonneg _) hra ?_
      refine Summable.mul_right _ ?_
      rw [← Equiv.pnatEquivNat.symm.summable_iff]
      convert hf using 2 with n
      simp [Equiv.pnatEquivNat]
  have hT := hsumm.hasSum
  refine ⟨?_, ?_⟩
  · have h1 := hT.prod_fiberwise hrow
    rw [q27_hasSum_pnat_iff] at h1
    convert h1 using 2 with n
    simp [div_eq_mul_inv, mul_assoc]
  · have h2 := q27_hasSum_divisorsAntidiagonal hT
    rw [q27_hasSum_pnat_iff] at h2
    convert h2 using 2 with n
    rw [Nat.succPNat_coe, sum_mul, ← Nat.sum_divisorsAntidiagonal (fun a _ ↦ f a * x ^ (n + 1))]
    refine sum_congr rfl fun y hy ↦ ?_
    have hy' := Nat.mem_divisorsAntidiagonal.mp hy
    have h0 : 0 < y.1 ∧ 0 < y.2 :=
      ⟨Nat.pos_of_ne_zero (left_ne_zero_of_mul (hy'.1 ▸ Nat.succ_ne_zero n)),
        Nat.pos_of_ne_zero (right_ne_zero_of_mul (hy'.1 ▸ Nat.succ_ne_zero n))⟩
    rw [dite_eq_left h0]
    simp only [hc, PNat.mk_coe, hy'.1]

/-- DLMF 27.7.2 (proof). -/
lemma q27_lambertSeries_hasSum (f : ℕ → ℂ) {x : ℂ} (hx : ‖x‖ < 1)
    (hf : Summable fun n : ℕ ↦ ‖f (n + 1)‖ * ‖x‖ ^ (n + 1)) :
    HasSum (fun n : ℕ ↦ f (n + 1) * x ^ (n + 1) / (1 - x ^ (n + 1))) (lambertSeries f x) ∧
      HasSum (fun n : ℕ ↦ (∑ d ∈ (n + 1).divisors, f d) * x ^ (n + 1)) (lambertSeries f x) := by
  obtain ⟨h1, h2⟩ := q27_lambert_core f hx hf
  have : lambertSeries f x = ∑' c : ℕ+ × ℕ+, f c.1 * x ^ ((c.1 : ℕ) * c.2) := h1.tsum_eq
  rw [this]
  exact ⟨h1, h2⟩

/-- `∑ (n+1)^k r^{n+1}` converges for `0 ≤ r < 1`. -/
lemma q27_summable_shift_pow_mul (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ k * r ^ (n + 1) := by
  have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k
    (by rw [Real.norm_of_nonneg hr0]; exact hr)
  exact (summable_nat_add_iff 1).mpr this

/-- DLMF 27.7.3 (proof). -/
lemma q27_lambert_moebius {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ ↦ (μ (n + 1) : ℂ) * x ^ (n + 1) / (1 - x ^ (n + 1))) x := by
  have hr0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hf : Summable fun n : ℕ ↦ ‖((μ (n + 1) : ℤ) : ℂ)‖ * ‖x‖ ^ (n + 1) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_)
      ((summable_geometric_of_lt_one hr0 hx).mul_left ‖x‖)
    rw [pow_succ', ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine mul_le_of_le_one_left hr0 ?_
    rw [Complex.norm_intCast]
    exact_mod_cast abs_moebius_le_one
  obtain ⟨h1, h2⟩ := q27_lambert_core (fun n ↦ ((μ n : ℤ) : ℂ)) hx hf
  have h3 : HasSum (fun n : ℕ ↦ (∑ d ∈ (n + 1).divisors, ((μ d : ℤ) : ℂ)) * x ^ (n + 1)) x := by
    have : (fun n : ℕ ↦ (∑ d ∈ (n + 1).divisors, ((μ d : ℤ) : ℂ)) * x ^ (n + 1)) =
        fun n ↦ if n = 0 then x else 0 := by
      funext n
      rw [q27_sum_divisors_moebius_eq_ite]
      split_ifs with h h' h' <;> simp_all
    rw [this]
    exact hasSum_ite_eq 0 x
  rw [h2.unique h3] at h1
  exact h1

/-- DLMF 27.7.4 (proof). -/
lemma q27_lambert_totient {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ ↦ ((n + 1).totient : ℂ) * x ^ (n + 1) / (1 - x ^ (n + 1)))
      (x / (1 - x) ^ 2) := by
  have hr0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hf : Summable fun n : ℕ ↦ ‖(((n + 1).totient : ℕ) : ℂ)‖ * ‖x‖ ^ (n + 1) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_)
      (q27_summable_shift_pow_mul 1 hr0 hx)
    rw [pow_one, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact_mod_cast Nat.totient_le _
  obtain ⟨h1, h2⟩ := q27_lambert_core (fun n ↦ ((n.totient : ℕ) : ℂ)) hx hf
  have h3 : HasSum (fun n : ℕ ↦ (∑ d ∈ (n + 1).divisors, ((d.totient : ℕ) : ℂ)) * x ^ (n + 1))
      (x / (1 - x) ^ 2) := by
    have h0 := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℂ) hx
    have h4 := (hasSum_nat_add_iff' (f := fun n : ℕ ↦ (n : ℂ) * x ^ n) 1).mpr h0
    rw [sum_range_one, Nat.cast_zero, zero_mul, sub_zero] at h4
    refine h4.congr_fun fun n ↦ ?_
    rw [← Nat.cast_sum, Nat.sum_totient]
  rw [h2.unique h3] at h1
  exact h1

/-- DLMF 27.7.5 (proof). -/
lemma q27_lambert_cpow (α : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ) ^ α * x ^ (n + 1) / (1 - x ^ (n + 1)))
      (∑' n : ℕ, sigmaC α (n + 1) * x ^ (n + 1)) ∧
      Summable fun n : ℕ ↦ sigmaC α (n + 1) * x ^ (n + 1) := by
  have hr0 : 0 ≤ ‖x‖ := norm_nonneg x
  obtain ⟨K, hK⟩ := exists_nat_ge α.re
  have hf : Summable fun n : ℕ ↦ ‖((n + 1 : ℕ) : ℂ) ^ α‖ * ‖x‖ ^ (n + 1) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_)
      (q27_summable_shift_pow_mul K hr0 hx)
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n), ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) hK
  obtain ⟨h1, h2⟩ := q27_lambert_core (fun n ↦ (n : ℂ) ^ α) hx hf
  have h3 : HasSum (fun n : ℕ ↦ sigmaC α (n + 1) * x ^ (n + 1))
      (∑' c : ℕ+ × ℕ+, ((c.1 : ℕ) : ℂ) ^ α * x ^ ((c.1 : ℕ) * c.2)) := by
    refine h2.congr_fun fun n ↦ ?_
    rw [sigmaC_apply]
  rw [← h3.tsum_eq] at h1
  exact ⟨h1, h3.summable⟩

/-- DLMF 27.7.6 (proof). -/
lemma q27_lambert_liouville {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ ↦ (liouville (n + 1) : ℂ) * x ^ (n + 1) / (1 - x ^ (n + 1)))
      (∑' n : ℕ, x ^ ((n + 1) ^ 2)) := by
  have hr0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hf : Summable fun n : ℕ ↦ ‖((liouville (n + 1) : ℤ) : ℂ)‖ * ‖x‖ ^ (n + 1) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_)
      ((summable_geometric_of_lt_one hr0 hx).mul_left ‖x‖)
    rw [pow_succ', ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine mul_le_of_le_one_left hr0 ?_
    rw [Complex.norm_intCast, liouville_apply (Nat.succ_ne_zero n)]
    simp
  obtain ⟨h1, h2⟩ := q27_lambert_core (fun n ↦ ((liouville n : ℤ) : ℂ)) hx hf
  set T := ∑' c : ℕ+ × ℕ+, ((liouville c.1 : ℤ) : ℂ) * x ^ ((c.1 : ℕ) * c.2)
  have h3 : HasSum (fun n : ℕ ↦ if IsSquare (n + 1) then x ^ (n + 1) else 0) T := by
    refine h2.congr_fun fun n ↦ ?_
    rw [← Int.cast_sum, sum_divisors_liouville (Nat.succ_pos n)]
    split_ifs <;> simp
  have hinj : Function.Injective fun m : ℕ ↦ (m + 1) ^ 2 - 1 := by
    intro a b h
    have ha : 1 ≤ (a + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos a)
    have hb : 1 ≤ (b + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos b)
    have : (a + 1) ^ 2 = (b + 1) ^ 2 := by simp only at h; omega
    have := Nat.pow_left_injective two_ne_zero this
    omega
  have h4 := (hinj.hasSum_iff (f := fun n : ℕ ↦ if IsSquare (n + 1) then x ^ (n + 1) else 0)
    ?_).mpr h3
  · have h5 : HasSum (fun m : ℕ ↦ x ^ ((m + 1) ^ 2)) T := by
      refine h4.congr_fun fun m ↦ ?_
      have hm : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos m)
      simp only [Function.comp]
      rw [Nat.sub_add_cancel hm, ite_eq_left ⟨m + 1, sq (m + 1)⟩]
    rw [h5.tsum_eq]
    exact h1
  · intro n hn
    rw [ite_eq_right]
    rintro ⟨r, hr⟩
    apply hn
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · rw [h] at hr; omega
      · exact h
    refine ⟨r - 1, ?_⟩
    simp only
    rw [Nat.sub_add_cancel hr1, sq, ← hr]
    omega

/-- DLMF 27.7.2: for `|x| < 1`, if `∑ |f(n)| |x|ⁿ < ∞` the Lambert series converges absolutely
and equals the power series `∑_{n≥1} (∑_{d∣n} f(d)) xⁿ`. -/
@[dlmf 27.7.E2]
theorem lambertSeries_hasSum (f : ℕ → ℂ) {x : ℂ} (hx : ‖x‖ < 1)
    (hf : Summable fun n : ℕ ↦ ‖f (n + 1)‖ * ‖x‖ ^ (n + 1)) :
    HasSum (fun n : ℕ ↦ f (n + 1) * x ^ (n + 1) / (1 - x ^ (n + 1))) (lambertSeries f x) ∧
      HasSum (fun n : ℕ ↦ (∑ d ∈ (n + 1).divisors, f d) * x ^ (n + 1)) (lambertSeries f x) :=
  q27_lambertSeries_hasSum f hx hf

/-- DLMF 27.7.3: `∑_{n≥1} μ(n) xⁿ/(1 - xⁿ) = x`, `|x| < 1`. -/
@[dlmf 27.7.E3]
theorem lambert_moebius {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ ↦ (μ (n + 1) : ℂ) * x ^ (n + 1) / (1 - x ^ (n + 1))) x :=
  q27_lambert_moebius hx

/-- DLMF 27.7.4: `∑_{n≥1} φ(n) xⁿ/(1 - xⁿ) = x/(1 - x)²`, `|x| < 1`. -/
@[dlmf 27.7.E4]
theorem lambert_totient {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ ↦ ((n + 1).totient : ℂ) * x ^ (n + 1) / (1 - x ^ (n + 1)))
      (x / (1 - x) ^ 2) :=
  q27_lambert_totient hx

/-- DLMF 27.7.5: `∑_{n≥1} n^α xⁿ/(1 - xⁿ) = ∑_{n≥1} σ_α(n) xⁿ`, `|x| < 1`, `α ∈ ℂ`; both series
converge. -/
@[dlmf 27.7.E5]
theorem lambert_cpow (α : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ) ^ α * x ^ (n + 1) / (1 - x ^ (n + 1)))
      (∑' n : ℕ, sigmaC α (n + 1) * x ^ (n + 1)) ∧
      Summable fun n : ℕ ↦ sigmaC α (n + 1) * x ^ (n + 1) :=
  q27_lambert_cpow α hx

/-- DLMF 27.7.6: `∑_{n≥1} λ(n) xⁿ/(1 - xⁿ) = ∑_{n≥1} x^{n²}`, `|x| < 1`. -/
@[dlmf 27.7.E6]
theorem lambert_liouville {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ ↦ (liouville (n + 1) : ℂ) * x ^ (n + 1) / (1 - x ^ (n + 1)))
      (∑' n : ℕ, x ^ ((n + 1) ^ 2)) :=
  q27_lambert_liouville hx

end DLMF.NumberTheory
