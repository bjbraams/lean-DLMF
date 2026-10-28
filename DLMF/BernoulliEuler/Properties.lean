/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.BernoulliEuler.GeneratingFunctions
public import Mathlib.Algebra.Group.ForwardDiff

/-!
# Bernoulli and Euler polynomials: basic properties (DLMF §24.4)

Difference equations, symmetry, sums of powers, finite expansions, multiplication formulas,
special values and symbolic (umbral) operations, for complex `x` (DLMF §24.1: "`x` real or
complex"). Polynomial identities in `ℚ[X]` from Mathlib (`Polynomial.bernoulli_comp_one_add_X`,
…) and from `DLMFMathlib.NumberTheory.EulerPolynomials` are evaluated at complex points with
`Polynomial.aeval_comp`. Identities that Mathlib proves only for real `x` (Raabe's theorem
`bernoulliFun_mul`) are extended to complex `x` by the identity theorem for polynomials
(`b24a_eq_zero_of_real`).

The derivatives 24.4.34–24.4.35 are `hasDerivAt_bernoulliPolyB`, `hasDerivAt_eulerPolyE`
(`DLMF.BernoulliEuler.Basic`); the finite expansions 24.4.12–24.4.13 are `bernoulliPolyB_add`,
`eulerPolyE_add` (ibid.).

## Corrections

* 24.4.7 and 24.4.8 fail for `n = 0` (the printed sums start at `k = 1`; for `n = 0`,
  `∑_{k=1}^m k⁰ = m` while the right side of 24.4.7 is `m + 1`, and 24.4.8 gives
  `(1 + (-1)^m)/2` against `∑_{k=1}^m (-1)^{m-k}`). They are acquired for `n ≥ 1`.
* 24.4.11 fails for `m = 1` (left side `1`, right side `(Bₙ₊₁(1) - Bₙ₊₁)/(n+1) = 0` for `n ≥ 1`);
  acquired for `m ≥ 2`.
* 24.4.24 is false as printed: for `n = 1` its right side is `mx - m + 1/2` instead of
  `mx - 1/2` (the inner sum is `∑_{r=1}^{m-1} e^{2πir/m}/(1 - e^{2πir/m}) = -(m-1)/2`); numerical
  checks also fail for `n = 2, …, 5`, `m = 2, 3, 4` and for every sign or exponent variant tried.
  The corrected form, derived from the generating function by the partial fractions
  `m/(w^m - 1) = ∑_r ζ^r/(w - ζ^r)` and expanding `1/(ζ^{-r}e^t - 1)` in powers of `eᵗ - 1`, is
  `Bₙ(mx) = mⁿ Bₙ(x) - n ∑_{k=1}^{n} ∑_{j=0}^{k-1} (-1)^j (k-1 choose j)
    (∑_{r=1}^{m-1} ζ^r/(1 - ζ^r)^k) (j + mx)^{n-1}` with `ζ = e^{2πi/m}`
  (verified numerically to working precision for `n ≤ 7`, `2 ≤ m ≤ 5`, complex `x`).
-/

@[expose] public section

noncomputable section

open Polynomial (aeval X C)
open Finset
open scoped Nat Real Polynomial

namespace DLMF.BernoulliEuler

/-! ### Helpers -/

/-- Complex evaluation of a rational polynomial as evaluation of the mapped polynomial. -/
theorem b24a_aeval_eq_eval_map (p : ℚ[X]) (z : ℂ) :
    aeval z p = (p.map (algebraMap ℚ ℂ)).eval z := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]

/-- The identity theorem for polynomial functions: a function of `z ∈ ℂ` given by a complex
polynomial that vanishes at every real point vanishes everywhere. -/
lemma b24a_eq_zero_of_real {f : ℂ → ℂ} (F : ℂ[X]) (hF : ∀ z, F.eval z = f z)
    (hreal : ∀ x : ℝ, f x = 0) (z : ℂ) : f z = 0 := by
  have hF0 : F = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot F ?_
    refine Set.infinite_of_injective_forall_mem (f := fun x : ℝ => (x : ℂ))
      Complex.ofReal_injective fun x => ?_
    simp [Polynomial.IsRoot, hF, hreal]
  rw [← hF, hF0, Polynomial.eval_zero]

/-- Identity under the stated parameter and domain assumptions: `aeval z ((Polynomial.bernoulli
n).comp p) = bernoulliPolyB n (aeval z p)`. -/
lemma b24a_bernoulliPolyB_comp (n : ℕ) (p : ℚ[X]) (z : ℂ) :
    aeval z ((Polynomial.bernoulli n).comp p) = bernoulliPolyB n (aeval z p) := by
  rw [Polynomial.aeval_comp]; rfl

/-- Identity under the stated parameter and domain assumptions: `aeval z ((Polynomial.euler
n).comp p) = eulerPolyE n (aeval z p)`. -/
lemma b24a_eulerPolyE_comp (n : ℕ) (p : ℚ[X]) (z : ℂ) :
    aeval z ((Polynomial.euler n).comp p) = eulerPolyE n (aeval z p) := by
  rw [Polynomial.aeval_comp]; rfl

/-- A complex polynomial with `F(z + h) + F(z) = 0` for all `z`, `h ≠ 0`, vanishes. -/
theorem b24a_eq_zero_of_add_add_self {F : ℂ[X]} {h : ℂ} (hh : h ≠ 0)
    (hF : ∀ z, F.eval (z + h) + F.eval z = 0) : F = 0 := by
  have hper : ∀ z, F.eval (z + 2 * h) = F.eval z := by
    intro z
    have h1 := hF z
    have h2 := hF (z + h)
    rw [show z + h + h = z + 2 * h by ring] at h2
    linear_combination h2 - h1
  have hk : ∀ k : ℕ, F.eval (k * (2 * h)) = F.eval 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, hper, ih]
  have hc : F - Polynomial.C (F.eval 0) = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
    refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k : ℂ) * (2 * h)) ?_ ?_
    · intro a b hab
      have h2 : (2 * h) ≠ 0 := mul_ne_zero two_ne_zero hh
      exact_mod_cast mul_right_cancel₀ h2 hab
    · intro k; simp [Polynomial.IsRoot, hk]
  have hF0 : F = Polynomial.C (F.eval 0) := sub_eq_zero.mp hc
  have := hF 0
  rw [hF0] at this ⊢
  simp only [Polynomial.eval_C] at this
  have : F.eval 0 = 0 := by linear_combination this / 2
  rw [this, map_zero]

/-- Alternating telescoping sum. -/
lemma b24a_sum_alt_telescope (g : ℕ → ℂ) (m : ℕ) :
    ∑ k ∈ range m, (-1 : ℂ) ^ k * (g (k + 1) + g k) = g 0 - (-1) ^ m * g m := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih, pow_succ]; ring

/-! ### §24.4(i) Difference equations -/

/-- **DLMF 24.4.1**: `Bₙ(x+1) - Bₙ(x) = n x^{n-1}`. -/
@[dlmf 24.4.E1]
theorem bernoulliPolyB_add_one_sub (n : ℕ) (x : ℂ) :
    bernoulliPolyB n (x + 1) - bernoulliPolyB n x = n * x ^ (n - 1) := by
  have h := congrArg (aeval x) (Polynomial.bernoulli_comp_one_add_X n)
  rw [b24a_bernoulliPolyB_comp] at h
  simp only [map_add, map_one, Polynomial.aeval_X, nsmul_eq_mul] at h
  rw [add_comm x 1, h]; simp [bernoulliPolyB]

/-- **DLMF 24.4.2**: `Eₙ(x+1) + Eₙ(x) = 2xⁿ`. -/
@[dlmf 24.4.E2]
theorem eulerPolyE_add_one_add (n : ℕ) (x : ℂ) :
    eulerPolyE n (x + 1) + eulerPolyE n x = 2 * x ^ n := by
  have h := congrArg (aeval x) (Polynomial.euler_comp_X_add_one_add n)
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, map_ofNat] at h
  rw [b24a_eulerPolyE_comp] at h
  simpa [eulerPolyE] using h

/-! ### §24.4(ii) Symmetry -/

/-- **DLMF 24.4.3**: `Bₙ(1-x) = (-1)ⁿ Bₙ(x)`. -/
@[dlmf 24.4.E3]
theorem bernoulliPolyB_one_sub (n : ℕ) (x : ℂ) :
    bernoulliPolyB n (1 - x) = (-1) ^ n * bernoulliPolyB n x := by
  have h := congrArg (aeval x) (Polynomial.bernoulli_comp_one_sub_X n)
  rw [b24a_bernoulliPolyB_comp] at h
  simpa [bernoulliPolyB] using h

/-- **DLMF 24.4.4**: `Eₙ(1-x) = (-1)ⁿ Eₙ(x)`. -/
@[dlmf 24.4.E4]
theorem eulerPolyE_one_sub (n : ℕ) (x : ℂ) :
    eulerPolyE n (1 - x) = (-1) ^ n * eulerPolyE n x := by
  have h := congrArg (aeval x) (Polynomial.euler_comp_one_sub_X n)
  rw [b24a_eulerPolyE_comp] at h
  simpa [eulerPolyE] using h

/-- **DLMF 24.4.5**: `(-1)ⁿ Bₙ(-x) = Bₙ(x) + n x^{n-1}`. -/
@[dlmf 24.4.E5]
theorem bernoulliPolyB_neg (n : ℕ) (x : ℂ) :
    (-1) ^ n * bernoulliPolyB n (-x) = bernoulliPolyB n x + n * x ^ (n - 1) := by
  have h := bernoulliPolyB_one_sub n (x + 1)
  rw [show 1 - (x + 1) = -x by ring] at h
  rw [h, ← mul_assoc, ← mul_pow, show (-1 : ℂ) * -1 = 1 by norm_num, one_pow, one_mul]
  linear_combination bernoulliPolyB_add_one_sub n x

/-- **DLMF 24.4.6**: `(-1)ⁿ⁺¹ Eₙ(-x) = Eₙ(x) - 2xⁿ`. -/
@[dlmf 24.4.E6]
theorem eulerPolyE_neg (n : ℕ) (x : ℂ) :
    (-1) ^ (n + 1) * eulerPolyE n (-x) = eulerPolyE n x - 2 * x ^ n := by
  have h := eulerPolyE_one_sub n (x + 1)
  rw [show 1 - (x + 1) = -x by ring] at h
  rw [h]
  have h2 : ((-1 : ℂ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  linear_combination (-1 : ℂ) * (eulerPolyE_add_one_add n x) - eulerPolyE n (x + 1) * h2

/-! ### §24.4(iii) Sums of powers -/

/-- **DLMF 24.4.9**: `∑_{k=0}^{m-1} (a + dk)ⁿ = dⁿ/(n+1) (Bₙ₊₁(m + a/d) - Bₙ₊₁(a/d))`,
complex `a`, `d ≠ 0`. -/
@[dlmf 24.4.E9]
theorem sum_range_add_mul_pow (n m : ℕ) (a d : ℂ) (hd : d ≠ 0) :
    ∑ k ∈ range m, (a + d * k) ^ n =
      d ^ n / (n + 1) * (bernoulliPolyB (n + 1) (m + a / d) - bernoulliPolyB (n + 1) (a / d)) := by
  have htel := Finset.sum_range_sub (fun k : ℕ => bernoulliPolyB (n + 1) (a / d + k)) m
  simp only [Nat.cast_succ, ← add_assoc, bernoulliPolyB_add_one_sub, Nat.add_sub_cancel,
    Nat.cast_zero, add_zero] at htel
  rw [add_comm (m : ℂ), ← htel, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [show a + d * k = d * (a / d + k) by field_simp, mul_pow]
  field_simp

/-- **DLMF 24.4.10**: `∑_{k=0}^{m-1} (-1)ᵏ (a + dk)ⁿ = dⁿ/2 ((-1)^{m-1} Eₙ(m + a/d) + Eₙ(a/d))`,
complex `a`, `d ≠ 0`, `m ≥ 1`. -/
@[dlmf 24.4.E10]
theorem sum_range_neg_one_pow_mul_add_mul_pow (n : ℕ) {m : ℕ} (hm : 1 ≤ m) (a d : ℂ)
    (hd : d ≠ 0) :
    ∑ k ∈ range m, (-1) ^ k * (a + d * k) ^ n =
      d ^ n / 2 * ((-1) ^ (m - 1) * eulerPolyE n (m + a / d) + eulerPolyE n (a / d)) := by
  have htel := Finset.sum_range_sub (fun k : ℕ => (-1 : ℂ) ^ k * eulerPolyE n (a / d + k)) m
  simp only [Nat.cast_succ, ← add_assoc, Nat.cast_zero, add_zero, pow_zero, one_mul] at htel
  have hterm : ∀ k : ℕ, (-1 : ℂ) ^ (k + 1) * eulerPolyE n (a / d + k + 1) -
      (-1) ^ k * eulerPolyE n (a / d + k) = -2 * ((-1) ^ k * (a / d + k) ^ n) := by
    intro k
    have := eulerPolyE_add_one_add n (a / d + k)
    rw [pow_succ]; linear_combination (-(-1 : ℂ) ^ k) * this
  simp only [hterm, ← mul_sum] at htel
  have hm' : (-1 : ℂ) ^ m = -(-1) ^ (m - 1) := by
    rw [show m = m - 1 + 1 by omega, pow_succ]; simp
  have : ∑ k ∈ range m, (-1 : ℂ) ^ k * (a + d * k) ^ n =
      d ^ n * ∑ k ∈ range m, (-1) ^ k * (a / d + k) ^ n := by
    rw [mul_sum]; refine sum_congr rfl fun k _ => ?_
    rw [show a + d * k = d * (a / d + k) by field_simp, mul_pow]; ring
  rw [this, add_comm (m : ℂ)]
  rw [hm'] at htel
  linear_combination (-d ^ n / 2) * htel

/-- **DLMF 24.4.7** (corrected: `n ≥ 1`): `∑_{k=1}^{m} kⁿ = (Bₙ₊₁(m+1) - Bₙ₊₁)/(n+1)`. For `n = 0`
the printed formula is off by one. -/
@[dlmf 24.4.E7]
theorem sum_Icc_pow_eq_bernoulli {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    ∑ k ∈ Icc 1 m, (k : ℚ) ^ n =
      ((Polynomial.bernoulli (n + 1)).eval ((m : ℚ) + 1) - bernoulli (n + 1)) / (n + 1) := by
  have h := Polynomial.sum_range_pow_eq_bernoulli_sub (m + 1) n
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos m), Nat.succ_eq_add_one,
    Finset.Ico_add_one_right_eq_Icc] at h
  simp only [Nat.cast_zero, zero_pow (by omega : n ≠ 0), zero_add, Nat.cast_add,
    Nat.cast_one] at h
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  rw [← h]; field_simp

/-- **DLMF 24.4.8** (corrected: `n ≥ 1`):
`∑_{k=1}^{m} (-1)^{m-k} kⁿ = (Eₙ(m+1) + (-1)^m Eₙ(0))/2`. -/
@[dlmf 24.4.E8]
theorem sum_Icc_neg_one_pow_mul_pow_eq_euler {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    ∑ k ∈ Icc 1 m, (-1 : ℚ) ^ (m - k) * (k : ℚ) ^ n =
      ((Polynomial.euler n).eval ((m : ℚ) + 1) + (-1) ^ m * (Polynomial.euler n).eval 0) / 2 := by
  have h := Polynomial.sum_range_neg_one_pow_mul_pow n (m + 1)
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos m), Nat.succ_eq_add_one,
    Finset.Ico_add_one_right_eq_Icc] at h
  simp only [Nat.cast_zero, zero_pow (by omega : n ≠ 0), mul_zero, zero_add, Nat.cast_add,
    Nat.cast_one] at h
  have hs : ∑ k ∈ Icc 1 m, (-1 : ℚ) ^ (m - k) * (k : ℚ) ^ n =
      (-1) ^ m * ∑ k ∈ Icc 1 m, (-1 : ℚ) ^ k * (k : ℚ) ^ n := by
    rw [mul_sum]; refine sum_congr rfl fun k hk => ?_
    have hkm : k ≤ m := (mem_Icc.mp hk).2
    rw [← mul_assoc, ← pow_add, show m + k = (m - k) + 2 * k by omega, pow_add, pow_mul]
    simp
  rw [hs]
  have h2 : ((-1 : ℚ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  linear_combination ((-1 : ℚ) ^ m / 2) * h + ((Polynomial.euler n).eval ((m : ℚ) + 1) / 2) * h2

/-- Inclusion–exclusion over the prime factors of `m`:
`[gcd(k, m) = 1] = ∑_{T ⊆ P(m)} (-1)^{|T|} [∏T ∣ k]`. -/
lemma r24a_coprime_indicator (k : ℕ) {m : ℕ} (hm0 : m ≠ 0) :
    (if Nat.Coprime k m then (1 : ℚ) else 0) = ∑ T ∈ m.primeFactors.powerset,
      (-1 : ℚ) ^ T.card * (if (∏ p ∈ T, p) ∣ k then 1 else 0) := by
  have h1 : (if Nat.Coprime k m then (1 : ℚ) else 0) =
      ∏ p ∈ m.primeFactors, ((-(if p ∣ k then (1 : ℚ) else 0)) + 1) := by
    have : ∀ p ∈ m.primeFactors, (-(if p ∣ k then (1 : ℚ) else 0)) + 1 =
        if ¬ p ∣ k then 1 else 0 := fun p _ => by split_ifs <;> norm_num
    rw [prod_congr rfl this, prod_boole]
    congr 1
    apply propext
    constructor
    · intro h p hp hpk
      have hp' := Nat.prime_of_mem_primeFactors hp
      have := Nat.dvd_gcd hpk (Nat.dvd_of_mem_primeFactors hp)
      rw [h] at this
      exact hp'.one_lt.ne' (Nat.dvd_one.mp this)
    · intro h
      refine Nat.coprime_of_dvd fun p hp hpk hpm => ?_
      exact h p (Nat.mem_primeFactors.mpr ⟨hp, hpm, hm0⟩) hpk
  rw [h1, prod_add]
  refine sum_congr rfl fun T hT => ?_
  rw [prod_const_one, mul_one, prod_neg, prod_boole]
  congr 1
  have hTp : ∀ p ∈ T, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (mem_powerset.mp hT hp)
  congr 1
  apply propext
  exact ⟨fun h => prod_primes_dvd k (fun p hp => (hTp p hp).prime) h,
    fun h p hp => (dvd_prod_of_mem _ hp).trans h⟩

/-- Sum of `kⁿ` over the multiples of `d` in `[1, m]`: `dⁿ ∑_{j=1}^{m/d} jⁿ`. -/
lemma r24a_sum_dvd_pow {d m : ℕ} (hd : 0 < d) (n : ℕ) :
    ∑ k ∈ Icc 1 m, (if d ∣ k then (1 : ℚ) else 0) * (k : ℚ) ^ n =
      (d : ℚ) ^ n * ∑ j ∈ Icc 1 (m / d), (j : ℚ) ^ n := by
  have hfilt : (Icc 1 m).filter (fun k => d ∣ k) =
      (Icc 1 (m / d)).image (fun j => d * j) := by
    ext k
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨hk1, hkm⟩, j, rfl⟩
      refine ⟨j, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp at hk1
        · exact hj
      · exact (Nat.le_div_iff_mul_le hd).mpr (by linarith [mul_comm d j])
    · rintro ⟨j, ⟨hj1, hjm⟩, rfl⟩
      refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right d j⟩
      have := (Nat.le_div_iff_mul_le hd).mp hjm
      linarith [mul_comm d j]
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [← sum_filter, hfilt, sum_image (fun a _ b _ h => by simpa [hd.ne'] using h), mul_sum]
  refine sum_congr rfl fun j _ => ?_
  push_cast; ring

/-- Faulhaber with `B'`: `∑_{j=1}^{q} jⁿ = 1/(n+1) ∑_{j=1}^{n+1} (n+1 choose j) B'_{n+1-j} qʲ`. -/
lemma r24a_sum_Icc_pow (q n : ℕ) :
    ∑ j ∈ Icc 1 q, (j : ℚ) ^ n = 1 / (n + 1) * ∑ j ∈ Icc 1 (n + 1),
      ((n + 1).choose j : ℚ) * bernoulli' (n + 1 - j) * (q : ℚ) ^ j := by
  rw [show Icc 1 q = Ico 1 (q + 1) from rfl, sum_Ico_pow, show Icc 1 (n + 1) = Ico 1 (n + 1 + 1)
    from rfl, sum_Ico_eq_sum_range, show n + 1 + 1 - 1 = n + 1 by omega, ← sum_range_reflect,
    mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [show n + 1 - 1 - i = n + 1 - (i + 1) by omega,
    show n + 1 - (n + 1 - (i + 1)) = i + 1 by omega,
    Nat.choose_symm (by omega : i + 1 ≤ n + 1), add_comm 1 i]
  ring

/-- **DLMF 24.4.11** (corrected: `m ≥ 2`): the sum of the `n`-th powers of the integers in
`[1, m]` prime to `m`:
`∑_{1≤k≤m, (k,m)=1} kⁿ = 1/(n+1) ∑_{j=1}^{n+1} (n+1 choose j) (∏_{p∣m} (1 - p^{n-j})) Bₙ₊₁₋ⱼ mʲ`.
For `m = 1` the printed formula fails (left side `1`, right side `0` for `n ≥ 1`). -/
@[dlmf 24.4.E11]
theorem sum_coprime_pow (n : ℕ) {m : ℕ} (hm : 2 ≤ m) :
    ∑ k ∈ (Icc 1 m).filter (fun k => Nat.Coprime k m), (k : ℚ) ^ n =
      1 / (n + 1) * ∑ j ∈ Icc 1 (n + 1), ((n + 1).choose j : ℚ) *
        ((∏ p ∈ m.primeFactors, (1 - (p : ℚ) ^ ((n : ℤ) - j))) * bernoulli (n + 1 - j)) *
          (m : ℚ) ^ j := by
  have hm0 : m ≠ 0 := by omega
  set P := m.primeFactors with hP
  have hdvd : ∀ T ∈ P.powerset, (∏ p ∈ T, p) ∣ m := fun T hT =>
    prod_primes_dvd m (fun p hp => (Nat.prime_of_mem_primeFactors (mem_powerset.mp hT hp)).prime)
      fun p hp => Nat.dvd_of_mem_primeFactors (mem_powerset.mp hT hp)
  have hpos : ∀ T ∈ P.powerset, 0 < ∏ p ∈ T, p := fun T hT =>
    prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (mem_powerset.mp hT hp)).pos
  -- step 1: inclusion–exclusion
  have s1 : ∑ k ∈ (Icc 1 m).filter (fun k => Nat.Coprime k m), (k : ℚ) ^ n =
      ∑ T ∈ P.powerset, (-1 : ℚ) ^ T.card *
        (((∏ p ∈ T, p : ℕ) : ℚ) ^ n * ∑ j ∈ Icc 1 (m / ∏ p ∈ T, p), (j : ℚ) ^ n) := by
    rw [sum_filter]
    have : ∀ k ∈ Icc 1 m, (if Nat.Coprime k m then (k : ℚ) ^ n else 0) =
        ∑ T ∈ P.powerset, (-1 : ℚ) ^ T.card *
          ((if (∏ p ∈ T, p) ∣ k then 1 else 0) * (k : ℚ) ^ n) := fun k _ => by
      rw [show (if Nat.Coprime k m then (k : ℚ) ^ n else 0) =
        (if Nat.Coprime k m then (1 : ℚ) else 0) * (k : ℚ) ^ n by split_ifs <;> simp,
        r24a_coprime_indicator k hm0, sum_mul]
      exact sum_congr rfl fun _ _ => by ring
    rw [sum_congr rfl this, sum_comm]
    refine sum_congr rfl fun T hT => ?_
    rw [← mul_sum, r24a_sum_dvd_pow (hpos T hT)]
  -- step 2: Faulhaber and `dⁿ (m/d)ʲ = mʲ d^{n-j}`
  have s2 : ∀ T ∈ P.powerset, (((∏ p ∈ T, p : ℕ) : ℚ) ^ n *
      ∑ j ∈ Icc 1 (m / ∏ p ∈ T, p), (j : ℚ) ^ n) = 1 / (n + 1) * ∑ j ∈ Icc 1 (n + 1),
        ((n + 1).choose j : ℚ) * bernoulli' (n + 1 - j) * (m : ℚ) ^ j *
          ∏ p ∈ T, (p : ℚ) ^ ((n : ℤ) - j) := by
    intro T hT
    rw [r24a_sum_Icc_pow, mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    have hd0 : ((∏ p ∈ T, p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (hpos T hT).ne'
    rw [Nat.cast_div (hdvd T hT) hd0, prod_zpow, ← Nat.cast_prod, zpow_sub₀ hd0, zpow_natCast,
      zpow_natCast, div_pow]
    field_simp
  -- step 3: sum over `T`
  have s3 : ∀ j : ℕ, ∑ T ∈ P.powerset, (-1 : ℚ) ^ T.card * ∏ p ∈ T, (p : ℚ) ^ ((n : ℤ) - j) =
      ∏ p ∈ P, (1 - (p : ℚ) ^ ((n : ℤ) - j)) := by
    intro j
    have := prod_add (fun p : ℕ => -((p : ℚ) ^ ((n : ℤ) - j))) (fun _ => (1 : ℚ)) P
    simp only [prod_const_one, mul_one, prod_neg] at this
    rw [← this]
    exact prod_congr rfl fun _ _ => by ring
  rw [s1, sum_congr rfl fun T hT => by rw [s2 T hT], mul_sum]
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  have : ∑ T ∈ P.powerset, (-1 : ℚ) ^ T.card * (1 / (n + 1) * (((n + 1).choose j : ℚ) *
      bernoulli' (n + 1 - j) * (m : ℚ) ^ j * ∏ p ∈ T, (p : ℚ) ^ ((n : ℤ) - j))) =
      1 / (n + 1) * (((n + 1).choose j : ℚ) * bernoulli' (n + 1 - j) * (m : ℚ) ^ j *
        ∑ T ∈ P.powerset, (-1 : ℚ) ^ T.card * ∏ p ∈ T, (p : ℚ) ^ ((n : ℤ) - j)) := by
    rw [mul_sum, mul_sum]; exact sum_congr rfl fun _ _ => by ring
  rw [this, s3]
  -- step 4: `B'` versus `B`
  by_cases h1 : n + 1 - j = 1
  · have hj' : (n : ℤ) - j = 0 := by have := (mem_Icc.mp hj).2; omega
    obtain ⟨p, hp⟩ : P.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
    rw [hj', prod_eq_zero hp (by simp)]
    ring
  · rw [bernoulli_eq_bernoulli'_of_ne_one h1]
    ring

/-! ### §24.4(v) Multiplication formulas -/

/-- **Raabe's theorem, DLMF 24.4.18**: `Bₙ(mx) = m^{n-1} ∑_{k=0}^{m-1} Bₙ(x + k/m)`, complex `x`,
`m ≥ 1`. Extended from Mathlib's real `bernoulliFun_mul` by the identity theorem. -/
@[dlmf 24.4.E18]
theorem bernoulliPolyB_mul (n : ℕ) {m : ℕ} (hm : m ≠ 0) (x : ℂ) :
    bernoulliPolyB n (m * x) =
      (m : ℂ) ^ n / m * ∑ k ∈ range m, bernoulliPolyB n (x + k / m) := by
  set P := (Polynomial.bernoulli n).map (algebraMap ℚ ℂ)
  have hB : ∀ w, bernoulliPolyB n w = P.eval w := fun w => b24a_aeval_eq_eval_map _ w
  have := b24a_eq_zero_of_real
    (f := fun z => bernoulliPolyB n (m * z) -
      (m : ℂ) ^ n / m * ∑ k ∈ range m, bernoulliPolyB n (z + k / m))
    (P.comp (Polynomial.C (m : ℂ) * X) - Polynomial.C ((m : ℂ) ^ n / m) *
      ∑ k ∈ range m, P.comp (X + Polynomial.C ((k : ℂ) / m)))
    (fun z => by simp [hB, Polynomial.eval_finsetSum])
    (fun y => by
      have hr := bernoulliFun_mul n hm y
      rw [show (m : ℂ) * y = ((m * y : ℝ) : ℂ) by push_cast; ring, bernoulliPolyB_ofReal, hr]
      simp only [show ∀ k : ℕ, (y : ℂ) + k / m = ((y + k / m : ℝ) : ℂ) by intro k; push_cast; ring,
        bernoulliPolyB_ofReal]
      push_cast; ring) x
  exact sub_eq_zero.mp this

/-- **DLMF 24.4.19**: `Eₙ(mx) = -(2mⁿ/(n+1)) ∑_{k=0}^{m-1} (-1)ᵏ Bₙ₊₁(x + k/m)`, `m` even. -/
@[dlmf 24.4.E19]
theorem eulerPolyE_mul_of_even (n : ℕ) {m : ℕ} (hm : Even m) (hm0 : m ≠ 0) (x : ℂ) :
    eulerPolyE n (m * x) = -(2 * (m : ℂ) ^ n / (n + 1)) *
      ∑ k ∈ range m, (-1) ^ k * bernoulliPolyB (n + 1) (x + k / m) := by
  have hm0' : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  set P := (Polynomial.euler n).map (algebraMap ℚ ℂ)
  set Q := (Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℂ)
  have hE : ∀ w, eulerPolyE n w = P.eval w := fun w => b24a_aeval_eq_eval_map _ w
  have hB : ∀ w, bernoulliPolyB (n + 1) w = Q.eval w := fun w => b24a_aeval_eq_eval_map _ w
  set F : ℂ[X] := P.comp (Polynomial.C (m : ℂ) * X) + Polynomial.C (2 * (m : ℂ) ^ n / (n + 1)) *
      ∑ k ∈ range m, Polynomial.C ((-1 : ℂ) ^ k) * Q.comp (X + Polynomial.C ((k : ℂ) / m))
  have hFe : ∀ z, F.eval z = eulerPolyE n (m * z) +
      2 * (m : ℂ) ^ n / (n + 1) * ∑ k ∈ range m, (-1) ^ k * bernoulliPolyB (n + 1) (z + k / m) := by
    intro z; simp [F, hE, hB, Polynomial.eval_finsetSum]
  have hF : F = 0 := by
    refine b24a_eq_zero_of_add_add_self (h := 1 / m) (by simpa using hm0') fun z => ?_
    rw [hFe, hFe]
    have h1 := eulerPolyE_add_one_add n (m * z)
    rw [show (m : ℂ) * (z + 1 / m) = m * z + 1 by field_simp]
    have h2 := b24a_sum_alt_telescope (fun k => bernoulliPolyB (n + 1) (z + k / m)) m
    simp only [Nat.cast_succ, Nat.cast_zero, zero_div, add_zero, hm.neg_one_pow, one_mul] at h2
    rw [show z + (m : ℂ) / m = z + 1 by field_simp] at h2
    have h4 := bernoulliPolyB_add_one_sub (n + 1) z
    have h3 : ∀ k : ℕ, z + 1 / m + k / m = z + ((k : ℂ) + 1) / m := fun k => by ring
    simp only [h3]
    rw [mul_pow] at h1
    have : ∑ k ∈ range m, (-1 : ℂ) ^ k * bernoulliPolyB (n + 1) (z + ((k : ℂ) + 1) / m) +
        ∑ k ∈ range m, (-1 : ℂ) ^ k * bernoulliPolyB (n + 1) (z + k / m) = -((n + 1) * z ^ n) := by
      rw [← sum_add_distrib]
      rw [show ∑ k ∈ range m, ((-1 : ℂ) ^ k * bernoulliPolyB (n + 1) (z + ((k : ℂ) + 1) / m) +
        (-1 : ℂ) ^ k * bernoulliPolyB (n + 1) (z + k / m)) = ∑ k ∈ range m, (-1 : ℂ) ^ k *
        (bernoulliPolyB (n + 1) (z + ((k : ℂ) + 1) / m) + bernoulliPolyB (n + 1) (z + k / m)) from
        sum_congr rfl fun k _ => by ring, h2]
      push_cast at h4
      linear_combination -h4
    have hc : 2 * (m : ℂ) ^ n / (n + 1) * (n + 1) = 2 * (m : ℂ) ^ n := by field_simp
    linear_combination h1 + (2 * (m : ℂ) ^ n / (n + 1)) * this - z ^ n * hc
  have := hFe x
  rw [hF, Polynomial.eval_zero] at this
  linear_combination -this

/-- **DLMF 24.4.20**: `Eₙ(mx) = mⁿ ∑_{k=0}^{m-1} (-1)ᵏ Eₙ(x + k/m)`, `m` odd. -/
@[dlmf 24.4.E20]
theorem eulerPolyE_mul_of_odd (n : ℕ) {m : ℕ} (hm : Odd m) (x : ℂ) :
    eulerPolyE n (m * x) = (m : ℂ) ^ n * ∑ k ∈ range m, (-1) ^ k * eulerPolyE n (x + k / m) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.pos.ne'
  set P := (Polynomial.euler n).map (algebraMap ℚ ℂ)
  have hE : ∀ w, eulerPolyE n w = P.eval w := fun w => b24a_aeval_eq_eval_map _ w
  set F : ℂ[X] := P.comp (Polynomial.C (m : ℂ) * X) - Polynomial.C ((m : ℂ) ^ n) *
      ∑ k ∈ range m, Polynomial.C ((-1 : ℂ) ^ k) * P.comp (X + Polynomial.C ((k : ℂ) / m))
  have hFe : ∀ z, F.eval z = eulerPolyE n (m * z) -
      (m : ℂ) ^ n * ∑ k ∈ range m, (-1) ^ k * eulerPolyE n (z + k / m) := by
    intro z; simp [F, hE, Polynomial.eval_finsetSum]
  have hF : F = 0 := by
    refine b24a_eq_zero_of_add_add_self (h := 1 / m) (by simpa using hm0) fun z => ?_
    rw [hFe, hFe]
    have h1 := eulerPolyE_add_one_add n (m * z)
    rw [show (m : ℂ) * (z + 1 / m) = m * z + 1 by field_simp]
    have h2 := b24a_sum_alt_telescope (fun k => eulerPolyE n (z + k / m)) m
    simp only [Nat.cast_succ, Nat.cast_zero, zero_div, add_zero, hm.neg_one_pow] at h2
    rw [show z + (m : ℂ) / m = z + 1 by field_simp] at h2
    have h3 : ∀ k : ℕ, z + 1 / m + k / m = z + ((k : ℂ) + 1) / m := fun k => by ring
    simp only [h3]
    rw [mul_pow] at h1
    have : ∑ k ∈ range m, (-1 : ℂ) ^ k * eulerPolyE n (z + ((k : ℂ) + 1) / m) +
        ∑ k ∈ range m, (-1 : ℂ) ^ k * eulerPolyE n (z + k / m) = 2 * z ^ n := by
      rw [← sum_add_distrib]
      rw [show ∑ k ∈ range m, ((-1 : ℂ) ^ k * eulerPolyE n (z + ((k : ℂ) + 1) / m) +
        (-1 : ℂ) ^ k * eulerPolyE n (z + k / m)) = ∑ k ∈ range m, (-1 : ℂ) ^ k *
        (eulerPolyE n (z + ((k : ℂ) + 1) / m) + eulerPolyE n (z + k / m)) from
        sum_congr rfl fun k _ => by ring, h2]
      linear_combination eulerPolyE_add_one_add n z
    linear_combination h1 - (m : ℂ) ^ n * this
  have := hFe x
  rw [hF, Polynomial.eval_zero] at this
  exact (sub_eq_zero.mp this.symm)

/-- **DLMF 24.4.21**: `Bₙ(x) = 2^{n-1}(Bₙ(x/2) + Bₙ(x/2 + 1/2))`. -/
@[dlmf 24.4.E21]
theorem bernoulliPolyB_eq_half (n : ℕ) (x : ℂ) :
    bernoulliPolyB n x =
      2 ^ n / 2 * (bernoulliPolyB n (x / 2) + bernoulliPolyB n (x / 2 + 1 / 2)) := by
  have h := bernoulliPolyB_mul n (m := 2) (by norm_num) (x / 2)
  simp only [sum_range_succ, sum_range_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    zero_div, add_zero, zero_add] at h
  rw [show (2 : ℂ) * (x / 2) = x by ring] at h
  rw [h]

/-- **DLMF 24.4.23**: `Eₙ₋₁(x) = (2ⁿ/n)(Bₙ(x/2 + 1/2) - Bₙ(x/2))`, `n ≥ 1` (written for `n+1`). -/
@[dlmf 24.4.E23]
theorem eulerPolyE_eq_bernoulliPolyB_sub (n : ℕ) (x : ℂ) :
    eulerPolyE n x = 2 ^ (n + 1) / (n + 1) *
      (bernoulliPolyB (n + 1) (x / 2 + 1 / 2) - bernoulliPolyB (n + 1) (x / 2)) := by
  have h := congrArg (aeval x) (Polynomial.euler_eq_bernoulli n)
  simp only [map_mul, map_add, map_natCast, map_one, map_sub, Polynomial.aeval_C,
    b24a_bernoulliPolyB_comp, Polynomial.aeval_X, eq_ratCast] at h
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast at h
  rw [show (1 : ℂ) / 2 * x + 1 / 2 = x / 2 + 1 / 2 by ring,
    show (1 : ℂ) / 2 * x = x / 2 by ring] at h
  rw [show eulerPolyE n x = aeval x (Polynomial.euler n) from rfl, div_mul_eq_mul_div,
    eq_div_iff hn]
  linear_combination h

/-- **DLMF 24.4.22**: `Eₙ₋₁(x) = (2/n)(Bₙ(x) - 2ⁿ Bₙ(x/2))`, `n ≥ 1` (written for `n+1`). -/
@[dlmf 24.4.E22]
theorem eulerPolyE_eq_bernoulliPolyB_sub' (n : ℕ) (x : ℂ) :
    eulerPolyE n x = 2 / (n + 1) *
      (bernoulliPolyB (n + 1) x - 2 ^ (n + 1) * bernoulliPolyB (n + 1) (x / 2)) := by
  rw [eulerPolyE_eq_bernoulliPolyB_sub, bernoulliPolyB_eq_half (n + 1) x]
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp
  ring

/-- **DLMF 24.4.14**: `Eₙ₋₁(x) = (2/n) ∑_{k=0}^{n} (n choose k)(1 - 2ᵏ) Bₖ x^{n-k}`, `n ≥ 1`
(written for `n+1`). -/
@[dlmf 24.4.E14]
theorem eulerPolyE_eq_sum_bernoulli (n : ℕ) (x : ℂ) :
    eulerPolyE n x = 2 / (n + 1) * ∑ k ∈ range (n + 2),
      ((n + 1).choose k : ℂ) * (1 - 2 ^ k) * bernoulli k * x ^ (n + 1 - k) := by
  rw [eulerPolyE_eq_bernoulliPolyB_sub', bernoulliPolyB_eq_sum, bernoulliPolyB_eq_sum, mul_sum,
    ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n + 1 := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [div_pow, show (2 : ℂ) ^ (n + 1) = 2 ^ k * 2 ^ (n + 1 - k) by
    rw [← pow_add, Nat.add_sub_cancel' hk']]
  field_simp

/-! ### Helpers for 24.4.24 -/

/-- Alternating binomial sums `∑_{j≤k} (-1)^j (k choose j) (j + y)^{n-1}`. -/
def s24a_D (n k : ℕ) (y : ℂ) : ℂ :=
  ∑ j ∈ range (k + 1), (-1) ^ j * (k.choose j : ℂ) * ((j : ℂ) + y) ^ (n - 1)

/-- `s24a_D` as an iterated forward difference. -/
lemma s24a_D_eq_fwdDiff (n k : ℕ) (y : ℂ) :
    s24a_D n k y = (-1) ^ k * (fwdDiff 1)^[k] (fun r : ℂ => r ^ (n - 1)) y := by
  rw [fwdDiff_iter_eq_sum_shift, s24a_D, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
  simp only [zsmul_eq_mul, nsmul_eq_mul, mul_one]
  push_cast
  rw [add_comm (j : ℂ) y, ← mul_assoc, ← mul_assoc, ← pow_add,
    show k + (k - j) = j + 2 * (k - j) by omega, pow_add, pow_mul]
  simp

/-- Pascal recursion for `s24a_D`. -/
lemma s24a_D_shift (n k : ℕ) (y : ℂ) :
    s24a_D n k (y + 1) = s24a_D n k y - s24a_D n (k + 1) y := by
  rw [s24a_D_eq_fwdDiff, s24a_D_eq_fwdDiff, s24a_D_eq_fwdDiff, Function.iterate_succ_apply',
    fwdDiff, pow_succ]
  ring

/-- `s24a_D n n = 0`: the `n`-th difference of `y^{n-1}` vanishes. -/
lemma s24a_D_self {n : ℕ} (hn : 1 ≤ n) (y : ℂ) : s24a_D n n y = 0 := by
  rw [s24a_D_eq_fwdDiff, fwdDiff_iter_pow_eq_zero_of_lt (by omega)]
  simp

/-- The polynomial solution of `h(y+1) - ζ h(y) = y^{n-1}`, `ζ ≠ 1`. -/
def s24a_h (n : ℕ) (ζ y : ℂ) : ℂ :=
  ∑ k ∈ range n, ((1 - ζ)⁻¹) ^ (k + 1) * s24a_D n k y

/-- The difference equation `h(y+1) = ζ h(y) + y^{n-1}`. -/
lemma s24a_h_shift {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ} (hζ : ζ ≠ 1) (y : ℂ) :
    s24a_h n ζ (y + 1) = ζ * s24a_h n ζ y + y ^ (n - 1) := by
  have h1 : (1 : ℂ) - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hζ)
  set a := (1 - ζ)⁻¹
  have ha : a ≠ 0 := inv_ne_zero h1
  have hζa : ζ = 1 - a⁻¹ := by simp [a]
  have key : y ^ (n - 1) =
      ∑ k ∈ range n, (a ^ k * s24a_D n k y - a ^ (k + 1) * s24a_D n (k + 1) y) := by
    rw [sum_range_sub' (fun k : ℕ => a ^ k * s24a_D n k y) n, s24a_D_self hn]
    simp [s24a_D]
  rw [s24a_h, s24a_h, key, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [s24a_D_shift, hζa]
  field_simp
  ring

/-- Iterating `f(z+1) = ζ f(z) + q(z)`. -/
lemma s24a_iter {f q : ℂ → ℂ} {ζ : ℂ} (hf : ∀ z, f (z + 1) = ζ * f z + q z) (y : ℂ) (s : ℕ) :
    f (y + s) = ζ ^ s * f y + ∑ t ∈ range s, ζ ^ (s - 1 - t) * q (y + (t : ℂ)) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.cast_succ, ← add_assoc, hf, ih, sum_range_succ, mul_add, mul_sum, pow_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    have : ∀ t ∈ range s, ζ * (ζ ^ (s - 1 - t) * q (y + t)) = ζ ^ (s - t) * q (y + t) := by
      intro t ht
      have : t < s := mem_range.mp ht
      rw [← mul_assoc, ← pow_succ', show s - 1 - t + 1 = s - t by omega]
    rw [sum_congr rfl this]
    have : ∀ t ∈ range s, ζ ^ (s - t) * q (y + t) = ζ ^ (s + 1 - 1 - t) * q (y + t) := by
      intro t _; congr 2
    rw [sum_congr rfl this]
    ring

/-- `ζ_r^j = ω^{rj}` with `ω = e^{2πi/m}`. -/
lemma s24a_zeta_pow (m r j : ℕ) :
    Complex.exp (2 * π * Complex.I * r / m) ^ j =
      Complex.exp (2 * π * Complex.I / m) ^ (r * j) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Sums over the nontrivial `m`-th roots of unity: `∑_{r=1}^{m-1} ζ_r^j` is `m - 1` for
`j = m` and `-1` for `0 < j < m`. -/
lemma s24a_sum_zeta_pow {m j : ℕ} (hm : 2 ≤ m) (hj0 : 0 < j) (hjm : j ≤ m) :
    ∑ r ∈ Icc 1 (m - 1), Complex.exp (2 * π * Complex.I * r / m) ^ j =
      if j = m then (m : ℂ) - 1 else -1 := by
  have hω := Complex.isPrimitiveRoot_exp m (by omega)
  set ω := Complex.exp (2 * π * Complex.I / m)
  have hI : Icc 1 (m - 1) = Ico 1 m := by ext; simp; omega
  have hfull : ∑ r ∈ range m, (ω ^ j) ^ r = if j = m then (m : ℂ) else 0 := by
    split_ifs with h
    · subst h; simp [hω.pow_eq_one]
    · have hne : ω ^ j ≠ 1 := hω.pow_ne_one_of_pos_of_lt (by omega) (by omega)
      rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self,
        zero_div]
  have hsplit : ∑ r ∈ range m, (ω ^ j) ^ r = 1 + ∑ r ∈ Icc 1 (m - 1), (ω ^ j) ^ r := by
    rw [hI, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), pow_zero]
  simp only [s24a_zeta_pow, mul_comm _ j, pow_mul]
  by_cases h : j = m
  · have e1 : (if j = m then (m : ℂ) - 1 else -1) = (m : ℂ) - 1 := by simp [h]
    have e2 : (if j = m then (m : ℂ) else 0) = m := by simp [h]
    rw [e2] at hfull; rw [e1]; linear_combination hfull - hsplit
  · have e1 : (if j = m then (m : ℂ) - 1 else -1) = -1 := by simp [h]
    have e2 : (if j = m then (m : ℂ) else 0) = 0 := by simp [h]
    rw [e2] at hfull; rw [e1]; linear_combination hfull - hsplit

/-- `ζ_r ≠ 1` for `1 ≤ r ≤ m - 1`. -/
lemma s24a_zeta_ne_one {m r : ℕ} (hr : r ∈ Icc 1 (m - 1)) :
    Complex.exp (2 * π * Complex.I * r / m) ≠ 1 := by
  simp only [mem_Icc] at hr
  have hω := Complex.isPrimitiveRoot_exp m (by omega)
  rw [← pow_one (Complex.exp _), s24a_zeta_pow, mul_one]
  exact hω.pow_ne_one_of_pos_of_lt (by omega) (by omega)

/-- `ζ_r^m = 1`. -/
lemma s24a_zeta_pow_m (m r : ℕ) (hm : m ≠ 0) :
    Complex.exp (2 * π * Complex.I * r / m) ^ m = 1 := by
  rw [s24a_zeta_pow, show r * m = m * r from mul_comm r m, pow_mul,
    (Complex.isPrimitiveRoot_exp m hm).pow_eq_one, one_pow]

/-- `∑_{s<m} ζ_r^s = 0` for `1 ≤ r ≤ m - 1`. -/
lemma s24a_geom_zeta {m r : ℕ} (hr : r ∈ Icc 1 (m - 1)) :
    ∑ s ∈ range m, Complex.exp (2 * π * Complex.I * r / m) ^ s = 0 := by
  have hm : m ≠ 0 := by simp only [mem_Icc] at hr; omega
  rw [geom_sum_eq (s24a_zeta_ne_one hr), s24a_zeta_pow_m m r hm, sub_self, zero_div]

/-- A polynomial function with a nonzero period is constant. -/
lemma s24a_periodic_const (P : ℂ[X]) {c : ℂ} (hc : c ≠ 0) (hP : ∀ y, P.eval (y + c) = P.eval y)
    (y z : ℂ) : P.eval y = P.eval z := by
  set Q := P - Polynomial.C (P.eval z)
  have hroot : ∀ k : ℕ, Q.eval (z + k * c) = 0 := by
    intro k
    induction k with
    | zero => simp [Q]
    | succ k ih =>
      have := hP (z + k * c)
      simp only [Q, Polynomial.eval_sub, Polynomial.eval_C] at ih ⊢
      rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, this, ih]
  have hQ : Q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot Q ?_
    refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => z + k * c) ?_ fun k => hroot k
    intro a b hab
    simpa [hc] using hab
  have := congrArg (Polynomial.eval y) hQ
  simpa [Q, sub_eq_zero] using this

/-- **DLMF 24.4.24, corrected** (see the module docstring): for `n ≥ 1`, `m ≥ 2` and
`ζ = e^{2πi/m}`, `Bₙ(mx) = mⁿ Bₙ(x) - n ∑_{k=1}^{n} ∑_{j=0}^{k-1} (-1)^j (k-1 choose j)
(∑_{r=1}^{m-1} ζ^r/(1 - ζ^r)^k) (j + mx)^{n-1}`. The printed formula (with `(n choose k)`,
`ζ^{(k-j)r}/(1 - ζ^r)ⁿ` and a plus sign) is false, already for `n = 1`. -/
@[dlmf 24.4.E24]
theorem bernoulliPolyB_mul_eq_roots_of_unity {n m : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) (x : ℂ) :
    bernoulliPolyB n (m * x) = (m : ℂ) ^ n * bernoulliPolyB n x -
      n * ∑ k ∈ Icc 1 n, ∑ j ∈ range k, (-1) ^ j * ((k - 1).choose j : ℂ) *
        (∑ r ∈ Icc 1 (m - 1), Complex.exp (2 * π * Complex.I * r / m) /
          (1 - Complex.exp (2 * π * Complex.I * r / m)) ^ k) * (j + m * x) ^ (n - 1) := by
  set ζ : ℕ → ℂ := fun r => Complex.exp (2 * π * Complex.I * r / m) with hζdef
  set R := Icc 1 (m - 1)
  set G : ℂ → ℂ := fun y => ∑ r ∈ R, ζ r * s24a_h n (ζ r) y with hG
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  -- the right side in terms of `G`
  have hRHS : ∀ y : ℂ, ∑ k ∈ Icc 1 n, ∑ j ∈ range k, (-1) ^ j * ((k - 1).choose j : ℂ) *
      (∑ r ∈ R, ζ r / (1 - ζ r) ^ k) * (j + y) ^ (n - 1) = G y := by
    intro y
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    simp only [G, s24a_h, s24a_D, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    simp only [add_comm 1 k, Nat.add_sub_cancel]
    rw [sum_comm]
    refine sum_congr rfl fun (j : ℕ) _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun (r : ℕ) _ => ?_
    rw [div_eq_mul_inv, ← inv_pow]
    ring
  have hζ1 : ∀ r ∈ R, ζ r ≠ 1 := fun r hr => s24a_zeta_ne_one hr
  -- shifts of `G`
  have hGs : ∀ (y : ℂ) (s : ℕ), G (y + s) = ∑ r ∈ R, ζ r * (ζ r ^ s * s24a_h n (ζ r) y) +
      ∑ t ∈ range s, (y + t) ^ (n - 1) * ∑ r ∈ R, ζ r ^ (s - t) := by
    intro y s
    have : ∀ r ∈ R, ζ r * s24a_h n (ζ r) (y + s) = ζ r * (ζ r ^ s * s24a_h n (ζ r) y) +
        ∑ t ∈ range s, (y + t) ^ (n - 1) * ζ r ^ (s - t) := by
      intro r hr
      rw [s24a_iter (f := s24a_h n (ζ r)) (q := fun z => z ^ (n - 1))
        (s24a_h_shift hn (hζ1 r hr)) y s, mul_add, mul_sum]
      congr 1
      refine sum_congr rfl fun t ht => ?_
      have := mem_range.mp ht
      rw [← mul_assoc, ← pow_succ', show s - 1 - t + 1 = s - t by omega]
      ring
    simp only [G]
    rw [sum_congr rfl this, sum_add_distrib, sum_comm (s := R)]
    simp only [mul_sum]
  have hGm : ∀ y : ℂ, G (y + m) = G y + m * y ^ (n - 1) - ∑ t ∈ range m, (y + t) ^ (n - 1) := by
    intro y
    rw [hGs]
    have h1 : ∑ r ∈ R, ζ r * (ζ r ^ m * s24a_h n (ζ r) y) = G y := by
      refine sum_congr rfl fun r _ => ?_
      rw [show ζ r ^ m = 1 from s24a_zeta_pow_m m r (by omega), one_mul]
    rw [h1, range_eq_Ico,
      sum_eq_sum_Ico_succ_bot (f := fun t => (y + t) ^ (n - 1) * ∑ r ∈ R, ζ r ^ (m - t)) (by omega),
      sum_eq_sum_Ico_succ_bot (f := fun t => (y + (t : ℂ)) ^ (n - 1)) (by omega)]
    have h2 : ∑ r ∈ R, ζ r ^ (m - 0) = (m : ℂ) - 1 := by
      rw [Nat.sub_zero, s24a_sum_zeta_pow hm (by omega) le_rfl]; simp
    have h3 : ∀ t ∈ Ico (0 + 1) m, (y + t) ^ (n - 1) * ∑ r ∈ R, ζ r ^ (m - t) =
        -(y + t) ^ (n - 1) := by
      intro t ht
      simp only [mem_Ico] at ht
      rw [s24a_sum_zeta_pow hm (by omega) (by omega)]
      simp [show m - t ≠ m by omega]
    rw [h2, sum_congr rfl h3, sum_neg_distrib]
    simp only [Nat.cast_zero, add_zero]
    ring
  have hGsum : ∀ y : ℂ, ∑ s ∈ range m, G (y + s) =
      -∑ s ∈ range m, ∑ t ∈ range s, (y + t) ^ (n - 1) := by
    intro y
    simp only [hGs, sum_add_distrib]
    have h1 : ∑ s ∈ range m, ∑ r ∈ R, ζ r * (ζ r ^ s * s24a_h n (ζ r) y) = 0 := by
      rw [sum_comm]
      refine sum_eq_zero fun r hr => ?_
      rw [← mul_sum, ← sum_mul, s24a_geom_zeta hr, zero_mul, mul_zero]
    rw [h1, zero_add, ← sum_neg_distrib]
    refine sum_congr rfl fun s hs => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun t ht => ?_
    have := mem_range.mp hs
    have := mem_range.mp ht
    rw [s24a_sum_zeta_pow hm (by omega) (by omega)]
    simp [show s - t ≠ m by omega]
  -- shifts of `Bₙ`
  have hB : ∀ (y : ℂ) (s : ℕ), bernoulliPolyB n (y + s) =
      bernoulliPolyB n y + ∑ t ∈ range s, n * (y + t) ^ (n - 1) := by
    intro y s
    have := s24a_iter (f := bernoulliPolyB n) (q := fun z => n * z ^ (n - 1)) (ζ := 1)
      (fun z => by rw [one_mul, ← bernoulliPolyB_add_one_sub]; ring) y s
    simpa using this
  set Φ : ℂ → ℂ := fun y => bernoulliPolyB n y + n * G y - (m : ℂ) ^ n * bernoulliPolyB n (y / m)
    with hΦ
  have hpow : ∀ y : ℂ, (m : ℂ) ^ n * (y / m) ^ (n - 1) = m * y ^ (n - 1) := by
    intro y
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, div_pow, pow_succ]
    field_simp
  have hper : ∀ y, Φ (y + m) = Φ y := by
    intro y
    have h1 := hB y m
    have h2 := bernoulliPolyB_add_one_sub n (y / m)
    rw [show y / m + 1 = (y + m) / m by field_simp] at h2
    rw [← mul_sum] at h1
    simp only [Φ]
    rw [hGm]
    linear_combination h1 - (m : ℂ) ^ n * h2 - (n : ℂ) * hpow y
  have hsum : ∀ y, ∑ s ∈ range m, Φ (y + s) = 0 := by
    intro y
    have hmul := bernoulliPolyB_mul n (m := m) (by omega) (y / m)
    rw [mul_div_cancel₀ _ hm0] at hmul
    have h3 : ∑ s ∈ range m, bernoulliPolyB n ((y + s) / m) =
        ∑ k ∈ range m, bernoulliPolyB n (y / m + k / m) := by
      refine sum_congr rfl fun s _ => ?_; rw [add_div]
    have hmul' : (m : ℂ) * bernoulliPolyB n y =
        (m : ℂ) ^ n * ∑ k ∈ range m, bernoulliPolyB n (y / m + k / m) := by
      rw [hmul]; field_simp
    simp only [Φ, sum_sub_distrib, sum_add_distrib, ← mul_sum, hGsum, hB, h3]
    simp only [sum_const, card_range, nsmul_eq_mul]
    linear_combination hmul'
  -- `Φ` is a polynomial function
  set Bp : ℂ[X] := (Polynomial.bernoulli n).map (algebraMap ℚ ℂ)
  set P : ℂ[X] := Bp + Polynomial.C (n : ℂ) * ∑ r ∈ R, Polynomial.C (ζ r) *
      ∑ k ∈ range n, Polynomial.C ((1 - ζ r)⁻¹ ^ (k + 1)) *
        ∑ j ∈ range (k + 1), Polynomial.C ((-1) ^ j * (k.choose j : ℂ)) *
          (Polynomial.C (j : ℂ) + X) ^ (n - 1) -
      Polynomial.C ((m : ℂ) ^ n) * Bp.comp (Polynomial.C (m : ℂ)⁻¹ * X)
  have hP : ∀ y, P.eval y = Φ y := by
    intro y
    simp only [P, Φ, G, s24a_h, s24a_D, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_comp, bernoulliPolyB, b24a_aeval_eq_eval_map, Bp,
      div_eq_inv_mul]
  have hconst : ∀ y, Φ y = Φ 0 := fun y => by
    rw [← hP, ← hP]; exact s24a_periodic_const P hm0 (fun z => by rw [hP, hP, hper]) y 0
  have h0 : Φ 0 = 0 := by
    have := hsum 0
    simp only [hconst _, sum_const, card_range, nsmul_eq_mul] at this
    exact (mul_eq_zero.mp this).resolve_left hm0
  have hx := hconst (m * x)
  rw [h0] at hx
  simp only [Φ, mul_div_cancel_left₀ _ hm0] at hx
  rw [hRHS]
  linear_combination hx

/-! ### §24.4(vi) Special values -/

/-- **DLMF 24.4.25**: `Bₙ(0) = (-1)ⁿ Bₙ(1) = Bₙ`. -/
@[dlmf 24.4.E25]
theorem bernoulliPolyB_zero_one (n : ℕ) :
    bernoulliPolyB n 0 = (-1) ^ n * bernoulliPolyB n 1 ∧
      (-1) ^ n * bernoulliPolyB n 1 = (bernoulli n : ℂ) := by
  have h1 : bernoulliPolyB n 1 = (bernoulli' n : ℂ) := by
    have := bernoulliPolyB_ratCast n 1
    push_cast at this
    rw [this, Polynomial.bernoulli_eval_one]
  have h2 : (-1 : ℂ) ^ n * bernoulliPolyB n 1 = (bernoulli n : ℂ) := by
    rw [h1, bernoulli'_eq_bernoulli]; push_cast
    rw [← mul_assoc, ← mul_pow]; norm_num
  exact ⟨by rw [h2, bernoulliPolyB_zero_arg], h2⟩

/-- **DLMF 24.4.26**: `Eₙ(0) = -Eₙ(1) = -(2/(n+1))(2ⁿ⁺¹ - 1)Bₙ₊₁` for `n > 0`. -/
@[dlmf 24.4.E26]
theorem eulerPolyE_zero_one {n : ℕ} (hn : 0 < n) :
    eulerPolyE n 0 = -eulerPolyE n 1 ∧
      -eulerPolyE n 1 = -(2 / (n + 1)) * (2 ^ (n + 1) - 1) * (bernoulli (n + 1) : ℂ) := by
  have h01 : eulerPolyE n 1 + eulerPolyE n 0 = 0 := by
    have := Polynomial.euler_eval_one_add_eval_zero n
    rw [zero_pow hn.ne', mul_zero] at this
    rw [show (1 : ℂ) = ((1 : ℚ) : ℂ) by norm_num, show (0 : ℂ) = ((0 : ℚ) : ℂ) by norm_num,
      eulerPolyE_ratCast, eulerPolyE_ratCast]
    exact_mod_cast this
  have h0 : eulerPolyE n 0 = -(2 / (n + 1)) * (2 ^ (n + 1) - 1) * (bernoulli (n + 1) : ℂ) := by
    have h := eulerPolyE_eq_bernoulliPolyB_sub n 0
    have hhalf : bernoulliPolyB (n + 1) (1 / 2) =
        ((2 / 2 ^ (n + 1) - 1) * bernoulli (n + 1) : ℝ) := by
      rw [show (1 / 2 : ℂ) = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, bernoulliPolyB_ofReal,
        bernoulliFun_eval_half]
    simp only [zero_div, zero_add, bernoulliPolyB_zero_arg] at h
    rw [h, hhalf]
    have hn' : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    push_cast
    field_simp
    ring
  exact ⟨by linear_combination h01, by linear_combination -h01 + h0⟩

/-- **DLMF 24.4.27**: `Bₙ(1/2) = -(1 - 2^{1-n}) Bₙ`. -/
@[dlmf 24.4.E27]
theorem bernoulliPolyB_half (n : ℕ) :
    bernoulliPolyB n (1 / 2) = -(1 - (2 : ℂ) ^ (1 - (n : ℤ))) * bernoulli n := by
  rw [show (1 / 2 : ℂ) = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, bernoulliPolyB_ofReal,
    bernoulliFun_eval_half]
  push_cast
  rw [zpow_sub₀ (by norm_num : (2 : ℂ) ≠ 0), zpow_one, zpow_natCast]
  ring

/-- **DLMF 24.4.28**: `Eₙ(1/2) = 2⁻ⁿ Eₙ`. -/
@[dlmf 24.4.E28]
theorem eulerPolyE_half' (n : ℕ) : eulerPolyE n (1 / 2) = (2 : ℂ)⁻¹ ^ n * eulerNumber n := by
  rw [eulerPolyE_half, inv_pow]; ring

/-- **DLMF 24.4.29**: `B₂ₙ(1/3) = B₂ₙ(2/3) = -(1/2)(1 - 3^{1-2n}) B₂ₙ`. -/
@[dlmf 24.4.E29]
theorem bernoulliPolyB_third (n : ℕ) :
    bernoulliPolyB (2 * n) (1 / 3) = bernoulliPolyB (2 * n) (2 / 3) ∧
      bernoulliPolyB (2 * n) (2 / 3) =
        -(1 / 2) * (1 - (3 : ℂ) ^ (1 - 2 * (n : ℤ))) * bernoulli (2 * n) := by
  have hsym : bernoulliPolyB (2 * n) (1 / 3) = bernoulliPolyB (2 * n) (2 / 3) := by
    have := bernoulliPolyB_one_sub (2 * n) (1 / 3)
    rw [show (1 : ℂ) - 1 / 3 = 2 / 3 by norm_num, pow_mul] at this
    rw [this]; norm_num
  refine ⟨hsym, ?_⟩
  have h := bernoulliPolyB_mul (2 * n) (m := 3) (by norm_num) 0
  simp only [sum_range_succ, sum_range_zero, mul_zero, zero_add, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, zero_div, bernoulliPolyB_zero_arg] at h
  rw [hsym] at h
  rw [zpow_sub₀ (by norm_num : (3 : ℂ) ≠ 0), zpow_one, show (2 : ℤ) * n = ((2 * n : ℕ) : ℤ) by
    push_cast; ring, zpow_natCast]
  have h3 : (3 : ℂ) ^ (2 * n) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  field_simp at h
  linear_combination (-1 : ℂ) * h

/-- **DLMF 24.4.31**: `Bₙ(1/4) = (-1)ⁿ Bₙ(3/4) = -(1 - 2^{1-n})Bₙ/2ⁿ - n Eₙ₋₁/4ⁿ`, `n ≥ 1`. -/
@[dlmf 24.4.E31]
theorem bernoulliPolyB_quarter {n : ℕ} (hn : 1 ≤ n) :
    bernoulliPolyB n (1 / 4) = (-1) ^ n * bernoulliPolyB n (3 / 4) ∧
      (-1) ^ n * bernoulliPolyB n (3 / 4) =
        -(1 - (2 : ℂ) ^ (1 - (n : ℤ))) / 2 ^ n * bernoulli n - n / 4 ^ n * eulerNumber (n - 1) := by
  have hsym : bernoulliPolyB n (1 / 4) = (-1) ^ n * bernoulliPolyB n (3 / 4) := by
    have := bernoulliPolyB_one_sub n (1 / 4)
    rw [show (1 : ℂ) - 1 / 4 = 3 / 4 by norm_num] at this
    rw [this, ← mul_assoc, ← mul_pow]; norm_num
  refine ⟨hsym, ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [← hsym, Nat.add_sub_cancel]
  have h := eulerPolyE_eq_bernoulliPolyB_sub' k (1 / 2)
  rw [eulerPolyE_half, show (1 : ℂ) / 2 / 2 = 1 / 4 by norm_num, bernoulliPolyB_half] at h
  have hz : (2 : ℂ) ^ (1 - ((k + 1 : ℕ) : ℤ)) = 2 / 2 ^ (k + 1) := by
    rw [zpow_sub₀ (by norm_num), zpow_one, zpow_natCast]
  rw [hz] at h ⊢
  have h2 : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [show (4 : ℂ) ^ (k + 1) = 2 ^ (k + 1) * 2 ^ (k + 1) by rw [← mul_pow]; norm_num]
  push_cast
  field_simp at h ⊢
  apply mul_left_cancel₀ (mul_ne_zero two_ne_zero h2)
  linear_combination h

/-- **DLMF 24.4.32**: `B₂ₙ(1/6) = B₂ₙ(5/6) = (1/2)(1 - 2^{1-2n})(1 - 3^{1-2n}) B₂ₙ`. -/
@[dlmf 24.4.E32]
theorem bernoulliPolyB_sixth (n : ℕ) :
    bernoulliPolyB (2 * n) (1 / 6) = bernoulliPolyB (2 * n) (5 / 6) ∧
      bernoulliPolyB (2 * n) (5 / 6) = 1 / 2 * (1 - (2 : ℂ) ^ (1 - 2 * (n : ℤ))) *
        (1 - (3 : ℂ) ^ (1 - 2 * (n : ℤ))) * bernoulli (2 * n) := by
  have hsym : bernoulliPolyB (2 * n) (1 / 6) = bernoulliPolyB (2 * n) (5 / 6) := by
    have := bernoulliPolyB_one_sub (2 * n) (1 / 6)
    rw [show (1 : ℂ) - 1 / 6 = 5 / 6 by norm_num, pow_mul] at this
    rw [this]; norm_num
  refine ⟨hsym, ?_⟩
  obtain ⟨h13, h3v⟩ := bernoulliPolyB_third n
  have h := bernoulliPolyB_eq_half (2 * n) (1 / 3)
  rw [show (1 : ℂ) / 3 / 2 = 1 / 6 by norm_num, show (1 : ℂ) / 6 + 1 / 2 = 2 / 3 by norm_num,
    hsym, h13] at h
  have hz : ∀ b : ℂ, b ≠ 0 → b ^ (1 - 2 * (n : ℤ)) = b / b ^ (2 * n) := fun b hb => by
    rw [zpow_sub₀ hb, zpow_one, show (2 : ℤ) * n = ((2 * n : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast]
  rw [hz 2 (by norm_num), hz 3 (by norm_num)]
  rw [h3v, hz 3 (by norm_num)] at h
  have h2 : (2 : ℂ) ^ (2 * n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : (3 : ℂ) ^ (2 * n) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp at h ⊢
  linear_combination -h

/-- **DLMF 24.4.33**: `E₂ₙ(1/6) = E₂ₙ(5/6) = (1 + 3^{-2n}) E₂ₙ/2^{2n+1}`. -/
@[dlmf 24.4.E33]
theorem eulerPolyE_sixth (n : ℕ) :
    eulerPolyE (2 * n) (1 / 6) = eulerPolyE (2 * n) (5 / 6) ∧
      eulerPolyE (2 * n) (5 / 6) =
        (1 + (3 : ℂ)⁻¹ ^ (2 * n)) / 2 ^ (2 * n + 1) * eulerNumber (2 * n) := by
  have hsym : eulerPolyE (2 * n) (1 / 6) = eulerPolyE (2 * n) (5 / 6) := by
    have := eulerPolyE_one_sub (2 * n) (1 / 6)
    rw [show (1 : ℂ) - 1 / 6 = 5 / 6 by norm_num, pow_mul] at this
    rw [this]; norm_num
  refine ⟨hsym, ?_⟩
  have h := eulerPolyE_mul_of_odd (2 * n) (m := 3) (by decide) (1 / 6)
  simp only [sum_range_succ, sum_range_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
  norm_num at h
  rw [hsym, eulerPolyE_half] at h
  have h2 : (2 : ℂ) ^ (2 * n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : (3 : ℂ) ^ (2 * n) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [inv_pow, pow_succ]
  field_simp at h ⊢
  linear_combination -h

/-- **DLMF 24.4.30**: `E₂ₙ₋₁(1/3) = -E₂ₙ₋₁(2/3) = -(1 - 3^{1-2n})(2²ⁿ - 1)B₂ₙ/(2n)`, `n ≥ 1`. -/
@[dlmf 24.4.E30]
theorem eulerPolyE_third {n : ℕ} (hn : 1 ≤ n) :
    eulerPolyE (2 * n - 1) (1 / 3) = -eulerPolyE (2 * n - 1) (2 / 3) ∧
      -eulerPolyE (2 * n - 1) (2 / 3) =
        -(1 - (3 : ℂ) ^ (1 - 2 * (n : ℤ))) * (2 ^ (2 * n) - 1) / (2 * n) * bernoulli (2 * n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  have hsym : eulerPolyE (2 * k + 1) (1 / 3) = -eulerPolyE (2 * k + 1) (2 / 3) := by
    have := eulerPolyE_one_sub (2 * k + 1) (1 / 3)
    rw [show (1 : ℂ) - 1 / 3 = 2 / 3 by norm_num, pow_succ, pow_mul] at this
    rw [this]; norm_num
  refine ⟨hsym, ?_⟩
  rw [← hsym]
  have h := eulerPolyE_eq_bernoulliPolyB_sub' (2 * k + 1) (1 / 3)
  rw [show (1 : ℂ) / 3 / 2 = 1 / 6 by norm_num, show 2 * k + 1 + 1 = 2 * (k + 1) by ring] at h
  obtain ⟨h13, h3v⟩ := bernoulliPolyB_third (k + 1)
  obtain ⟨h16, h6v⟩ := bernoulliPolyB_sixth (k + 1)
  rw [h13, h3v, h16, h6v] at h
  rw [h]
  have hz : ∀ b : ℂ, b ≠ 0 → b ^ (1 - 2 * ((k + 1 : ℕ) : ℤ)) = b / b ^ (2 * (k + 1)) :=
      fun b hb => by
    rw [zpow_sub₀ hb, zpow_one, show (2 : ℤ) * ((k + 1 : ℕ) : ℤ) = ((2 * (k + 1) : ℕ) : ℤ) by
      push_cast; ring, zpow_natCast]
  rw [hz 2 (by norm_num), hz 3 (by norm_num)]
  have h2 : (2 : ℂ) ^ (2 * (k + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : (3 : ℂ) ^ (2 * (k + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hk2 : 2 * (k : ℂ) + 1 + 1 ≠ 0 := by
    rw [show 2 * (k : ℂ) + 1 + 1 = 2 * (k + 1) by ring]; exact mul_ne_zero two_ne_zero hk
  push_cast
  field_simp
  ring

/-! ### Helpers for §24.4(iv) -/

/-- Splitting a sum over `range (2m)` into even and odd indices. -/
lemma q24a_sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ k ∈ range (2 * m), f k = ∑ j ∈ range m, (f (2 * j) + f (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

/-- Reindexing `Icc 1 n` to `range n`. -/
theorem q24a_sum_Icc_one {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ Icc 1 n, f k = ∑ k ∈ range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

/-- `∑_{k ≤ 2n+1} (2n+1 choose k)(1-2^k) Bₖ 2^k = (2n+1)E₂ₙ`, the core of 24.4.16–17. -/
lemma q24a_eulerNumber_two_mul_sum (n : ℕ) :
    ((2 * n + 1 : ℕ) : ℂ) * eulerNumber (2 * n) = ∑ k ∈ range (2 * n + 2),
      ((2 * n + 1).choose k : ℂ) * (1 - 2 ^ k) * bernoulli k * 2 ^ k := by
  have h1 := eulerPolyE_eq_sum_bernoulli (2 * n) (1 / 2)
  rw [eulerPolyE_half] at h1
  have hn : ((2 * n : ℕ) : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  have h2 : ∑ k ∈ range (2 * n + 2), ((2 * n + 1).choose k : ℂ) * (1 - 2 ^ k) * bernoulli k *
      (1 / 2) ^ (2 * n + 1 - k) = (1 / 2) ^ (2 * n + 1) * ∑ k ∈ range (2 * n + 2),
      ((2 * n + 1).choose k : ℂ) * (1 - 2 ^ k) * bernoulli k * 2 ^ k := by
    rw [mul_sum]; refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ 2 * n + 1 := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [show (1 / 2 : ℂ) ^ (2 * n + 1) = (1 / 2) ^ (2 * n + 1 - k) * (1 / 2) ^ k by
      rw [← pow_add, Nat.sub_add_cancel hk']]
    rw [show (2 : ℂ) ^ k = 1 / (1 / 2) ^ k by rw [one_div_pow, one_div_one_div]]
    field_simp
  rw [h2] at h1
  have h3 : (2 : ℂ) ^ (2 * n) * (1 / 2) ^ (2 * n) = 1 := by rw [← mul_pow]; norm_num
  generalize (∑ k ∈ range (2 * n + 2),
      ((2 * n + 1).choose k : ℂ) * (1 - 2 ^ k) * bernoulli k * 2 ^ k) = S at h1 ⊢
  field_simp at h1
  push_cast at h1 hn ⊢
  linear_combination h1 + S * h3

/-- Splitting `range (2n+2)` when the odd terms beyond the first vanish. -/
lemma q24a_sum_range_even_split (g : ℕ → ℂ) (n : ℕ) (hg : ∀ j, 1 ≤ j → g (2 * j + 1) = 0) :
    ∑ k ∈ range (2 * n + 2), g k = g 0 + g 1 + ∑ j ∈ range n, g (2 * (j + 1)) := by
  rw [show 2 * n + 2 = 2 * (n + 1) by ring, q24a_sum_range_two_mul, sum_range_succ',
    sum_add_distrib, sum_congr rfl fun j _ => hg (j + 1) (by omega)]
  simp only [sum_const_zero, add_zero, mul_zero, zero_add]
  ring

/-- From `B₂ₙ₊₁(1/2) = 0`: `∑_{j=1}^{n} (2n+1 choose 2j) B₂ⱼ 2^{2j} = 2n`. -/
theorem q24a_sum_choose_bernoulli_two_pow (n : ℕ) :
    ∑ j ∈ range n, ((2 * n + 1).choose (2 * (j + 1)) : ℂ) * bernoulli (2 * (j + 1)) *
      2 ^ (2 * (j + 1)) = 2 * n := by
  have h1 := bernoulliPolyB_eq_sum (2 * n + 1) (1 / 2)
  rw [bernoulliPolyB_half] at h1
  have h0 : -(1 - (2 : ℂ) ^ (1 - ((2 * n + 1 : ℕ) : ℤ))) * (bernoulli (2 * n + 1) : ℂ) = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [bernoulli_eq_zero_of_odd (odd_two_mul_add_one n) (by omega)]; simp
  rw [h0] at h1
  have h2 : ∑ k ∈ range (2 * n + 1 + 1), ((2 * n + 1).choose k : ℂ) * bernoulli k *
      (1 / 2) ^ (2 * n + 1 - k) = (1 / 2) ^ (2 * n + 1) * ∑ k ∈ range (2 * n + 2),
      ((2 * n + 1).choose k : ℂ) * bernoulli k * 2 ^ k := by
    rw [mul_sum]; refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ 2 * n + 1 := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [show (1 / 2 : ℂ) ^ (2 * n + 1) = (1 / 2) ^ (2 * n + 1 - k) * (1 / 2) ^ k by
      rw [← pow_add, Nat.sub_add_cancel hk']]
    rw [show (2 : ℂ) ^ k = 1 / (1 / 2) ^ k by rw [one_div_pow, one_div_one_div]]
    field_simp
  rw [h2, q24a_sum_range_even_split _ n (fun j hj => by
    rw [bernoulli_eq_zero_of_odd (odd_two_mul_add_one j) (by omega)]; simp)] at h1
  have h3 : (1 / 2 : ℂ) ^ (2 * n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h4 := (mul_eq_zero.mp h1.symm).resolve_left h3
  simp only [Nat.choose_zero_right, bernoulli_zero, Nat.choose_one_right, bernoulli_one] at h4
  push_cast at h4
  linear_combination h4

/-! ### §24.4(iv) Finite expansions -/

/-- **DLMF 24.4.15**: `B₂ₙ = 2n/(2²ⁿ(2²ⁿ - 1)) ∑_{k=0}^{n-1} (2n-1 choose 2k) E₂ₖ`, `n ≥ 1`. -/
@[dlmf 24.4.E15]
theorem bernoulli_two_mul_eq_sum_euler {n : ℕ} (hn : 1 ≤ n) :
    bernoulli (2 * n) = 2 * n / (2 ^ (2 * n) * (2 ^ (2 * n) - 1)) *
      ∑ k ∈ range n, ((2 * n - 1).choose (2 * k) : ℚ) * eulerNumber (2 * k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := eulerPolyE_eq_sum (2 * m + 1) 0
  rw [(eulerPolyE_zero_one (by omega : 0 < 2 * m + 1)).1,
    (eulerPolyE_zero_one (by omega : 0 < 2 * m + 1)).2,
    show 2 * m + 1 + 1 = 2 * (m + 1) by ring, q24a_sum_range_two_mul] at h1
  have hodd : ∀ j ∈ range (m + 1), ((2 * m + 1).choose (2 * j) : ℂ) *
      ((eulerNumber (2 * j) : ℂ) / 2 ^ (2 * j)) * (0 - 1 / 2) ^ (2 * m + 1 - 2 * j) +
      ((2 * m + 1).choose (2 * j + 1) : ℂ) * ((eulerNumber (2 * j + 1) : ℂ) / 2 ^ (2 * j + 1)) *
        (0 - 1 / 2) ^ (2 * m + 1 - (2 * j + 1)) =
      -(((2 * m + 1).choose (2 * j) : ℂ) * eulerNumber (2 * j)) / 2 ^ (2 * m + 1) := by
    intro j hj
    have hj' : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [eulerNumber_eq_zero_of_odd (odd_two_mul_add_one j)]
    rw [show (0 : ℂ) - 1 / 2 = -1 / 2 by ring, div_pow,
      (show Odd (2 * m + 1 - 2 * j) from ⟨m - j, by omega⟩).neg_one_pow,
      show (2 : ℂ) ^ (2 * m + 1) = 2 ^ (2 * j) * 2 ^ (2 * m + 1 - 2 * j) by
        rw [← pow_add]; congr 1; omega]
    have h4 : (2 : ℂ) ^ (2 * j) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h5 : (2 : ℂ) ^ (2 * m + 1 - 2 * j) ≠ 0 := pow_ne_zero _ (by norm_num)
    push_cast
    field_simp
    simp
  rw [sum_congr rfl hodd, ← sum_div, sum_neg_distrib] at h1
  have hm : (m : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero m
  have h4 : (2 : ℂ) ^ (2 * (m + 1)) - 1 ≠ 0 := by
    rw [sub_ne_zero]; norm_cast
    exact (Nat.one_lt_pow (by omega) (by norm_num)).ne'
  have : ((bernoulli (2 * (m + 1)) : ℚ) : ℂ) = ((2 * (m + 1 : ℕ) / (2 ^ (2 * (m + 1)) *
      (2 ^ (2 * (m + 1)) - 1)) * ∑ k ∈ range (m + 1), ((2 * (m + 1) - 1).choose (2 * k) : ℚ) *
        eulerNumber (2 * k) : ℚ) : ℂ) := by
    rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
    push_cast at h1 hm ⊢
    generalize (∑ k ∈ range (m + 1), ((2 * m + 1).choose (2 * k) : ℂ) * eulerNumber (2 * k)) = S
      at h1 ⊢
    rw [show (2 : ℂ) ^ (2 * (m + 1)) = 2 * 2 ^ (2 * m + 1) by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ]; ring] at h1 h4 ⊢
    have h5 : (2 : ℂ) ^ (2 * m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    generalize (2 : ℂ) ^ (2 * m + 1) = P at h1 h4 h5 ⊢
    have hm2 : 2 * (m : ℂ) + 1 + 1 ≠ 0 := by
      rw [show 2 * (m : ℂ) + 1 + 1 = 2 * (m + 1) by ring]; exact mul_ne_zero two_ne_zero hm
    field_simp at h1 ⊢
    linear_combination (-1 / 2 : ℂ) * h1
  exact_mod_cast this

/-- **DLMF 24.4.16**: `E₂ₙ = 1/(2n+1) - ∑_{k=1}^{n} (2n choose 2k-1) 2²ᵏ(2²ᵏ⁻¹ - 1)B₂ₖ/k`. -/
@[dlmf 24.4.E16]
theorem eulerNumber_two_mul_eq_sum_bernoulli (n : ℕ) :
    eulerNumber (2 * n) = 1 / (2 * n + 1) - ∑ k ∈ Icc 1 n, ((2 * n).choose (2 * k - 1) : ℚ) *
      (2 ^ (2 * k) * (2 ^ (2 * k - 1) - 1) * bernoulli (2 * k) / k) := by
  have h := q24a_eulerNumber_two_mul_sum n
  rw [q24a_sum_range_even_split _ n (fun j hj => by
    rw [bernoulli_eq_zero_of_odd (odd_two_mul_add_one j) (by omega)]; simp)] at h
  simp only [Nat.choose_zero_right, bernoulli_zero, Nat.choose_one_right, bernoulli_one,
    pow_zero, sub_self, mul_zero, zero_mul, zero_add] at h
  have h2 := q24a_sum_choose_bernoulli_two_pow n
  have hn : ((2 * n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have key : ((2 * n + 1 : ℕ) : ℂ) * ∑ k ∈ Icc 1 n, ((2 * n).choose (2 * k - 1) : ℂ) *
      (2 ^ (2 * k) * (2 ^ (2 * k - 1) - 1) * bernoulli (2 * k) / k) =
      ∑ j ∈ range n, (-(((2 * n + 1).choose (2 * (j + 1)) : ℂ) * (1 - 2 ^ (2 * (j + 1))) *
        bernoulli (2 * (j + 1)) * 2 ^ (2 * (j + 1))) - ((2 * n + 1).choose (2 * (j + 1)) : ℂ) *
          bernoulli (2 * (j + 1)) * 2 ^ (2 * (j + 1))) := by
    rw [q24a_sum_Icc_one, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    have hc := Nat.add_one_mul_choose_eq (2 * n) (2 * j + 1)
    rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, show 2 * j + 1 + 1 = 2 * (j + 1) by ring] at *
    have hc' : ((2 * n + 1 : ℕ) : ℂ) * ((2 * n).choose (2 * j + 1) : ℂ) =
        ((2 * n + 1).choose (2 * (j + 1)) : ℂ) * (2 * ((j + 1 : ℕ) : ℂ)) := by exact_mod_cast hc
    have hj : ((j + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [show (2 : ℂ) ^ (2 * (j + 1)) = 2 * 2 ^ (2 * j + 1) by
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ]; ring]
    generalize ((2 * n).choose (2 * j + 1) : ℂ) = c at hc' ⊢
    generalize ((2 * n + 1).choose (2 * (j + 1)) : ℂ) = c' at hc' ⊢
    generalize ((j + 1 : ℕ) : ℂ) = d at hc' hj ⊢
    generalize (2 : ℂ) ^ (2 * j + 1) = q
    generalize (bernoulli (2 * (j + 1)) : ℂ) = b
    calc ((2 * n + 1 : ℕ) : ℂ) * (c * (2 * q * (q - 1) * b / d))
        = (((2 * n + 1 : ℕ) : ℂ) * c) * (2 * q * (q - 1) * b) / d := by ring
      _ = c' * (2 * d) * (2 * q * (q - 1) * b) / d := by rw [hc']
      _ = _ := by field_simp; ring
  have : ((eulerNumber (2 * n) : ℚ) : ℂ) = ((1 / (2 * n + 1) - ∑ k ∈ Icc 1 n,
      ((2 * n).choose (2 * k - 1) : ℚ) *
      (2 ^ (2 * k) * (2 ^ (2 * k - 1) - 1) * bernoulli (2 * k) / k) : ℚ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ hn
    rw [mul_sub, key, h, sum_sub_distrib, sum_neg_distrib, h2]
    push_cast at hn ⊢
    field_simp; ring
  exact_mod_cast this

/-- **DLMF 24.4.17**: `E₂ₙ = 1 - ∑_{k=1}^{n} (2n choose 2k-1) 2²ᵏ(2²ᵏ - 1)B₂ₖ/(2k)`. -/
@[dlmf 24.4.E17]
theorem eulerNumber_two_mul_eq_one_sub_sum_bernoulli (n : ℕ) :
    eulerNumber (2 * n) = 1 - ∑ k ∈ Icc 1 n, ((2 * n).choose (2 * k - 1) : ℚ) *
      (2 ^ (2 * k) * (2 ^ (2 * k) - 1) * bernoulli (2 * k) / (2 * k)) := by
  have h := q24a_eulerNumber_two_mul_sum n
  rw [q24a_sum_range_even_split _ n (fun j hj => by
    rw [bernoulli_eq_zero_of_odd (odd_two_mul_add_one j) (by omega)]; simp)] at h
  simp only [Nat.choose_zero_right, bernoulli_zero, Nat.choose_one_right, bernoulli_one,
    pow_zero, sub_self, mul_zero, zero_mul, zero_add] at h
  have hn : ((2 * n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have key : ((2 * n + 1 : ℕ) : ℂ) * ∑ k ∈ Icc 1 n, ((2 * n).choose (2 * k - 1) : ℂ) *
      (2 ^ (2 * k) * (2 ^ (2 * k) - 1) * bernoulli (2 * k) / (2 * k)) =
      -∑ j ∈ range n, ((2 * n + 1).choose (2 * (j + 1)) : ℂ) * (1 - 2 ^ (2 * (j + 1))) *
        bernoulli (2 * (j + 1)) * 2 ^ (2 * (j + 1)) := by
    rw [q24a_sum_Icc_one, mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    have hc := Nat.add_one_mul_choose_eq (2 * n) (2 * j + 1)
    rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, show 2 * j + 1 + 1 = 2 * (j + 1) by ring] at *
    have hc' : ((2 * n + 1 : ℕ) : ℂ) * ((2 * n).choose (2 * j + 1) : ℂ) =
        ((2 * n + 1).choose (2 * (j + 1)) : ℂ) * (2 * ((j + 1 : ℕ) : ℂ)) := by exact_mod_cast hc
    have hj : ((j + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    generalize ((2 * n).choose (2 * j + 1) : ℂ) = c at hc' ⊢
    generalize ((2 * n + 1).choose (2 * (j + 1)) : ℂ) = c' at hc' ⊢
    generalize ((j + 1 : ℕ) : ℂ) = d at hc' hj ⊢
    generalize (2 : ℂ) ^ (2 * (j + 1)) = q
    generalize (bernoulli (2 * (j + 1)) : ℂ) = b
    calc ((2 * n + 1 : ℕ) : ℂ) * (c * (q * (q - 1) * b / (2 * d)))
        = (((2 * n + 1 : ℕ) : ℂ) * c) * (q * (q - 1) * b) / (2 * d) := by ring
      _ = c' * (2 * d) * (q * (q - 1) * b) / (2 * d) := by rw [hc']
      _ = -(c' * (1 - q) * b * q) := by field_simp; ring
  have : ((eulerNumber (2 * n) : ℚ) : ℂ) = ((1 - ∑ k ∈ Icc 1 n, ((2 * n).choose (2 * k - 1) : ℚ) *
      (2 ^ (2 * k) * (2 ^ (2 * k) - 1) * bernoulli (2 * k) / (2 * k)) : ℚ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ hn
    rw [mul_sub, key, h]
    push_cast; ring
  exact_mod_cast this

/-! ### §24.4(viii) Symbolic operations -/

/-- Generic umbral functional `yⁱ ↦ F i`. -/
def b24a_umbral (F : ℕ → ℂ) (P : ℂ[X]) : ℂ := P.sum fun i a => a * F i

/-- Identity under the stated parameter and domain assumptions: `b24a_umbral F (p + q) =
b24a_umbral F p + b24a_umbral F q`. -/
lemma b24a_umbral_add (F : ℕ → ℂ) (p q : ℂ[X]) :
    b24a_umbral F (p + q) = b24a_umbral F p + b24a_umbral F q :=
  Polynomial.sum_add_index p q _ (fun i => by simp) (fun i a b => by ring)

/-- Identity under the stated parameter and domain assumptions: `b24a_umbral F
(Polynomial.monomial n a) = a * F n`. -/
lemma b24a_umbral_monomial (F : ℕ → ℂ) (n : ℕ) (a : ℂ) :
    b24a_umbral F (Polynomial.monomial n a) = a * F n :=
  Polynomial.sum_monomial_index _ _ (by simp)

/-- Formula under the stated hypotheses: `b24a_umbral F (∑ i ∈ s, p i) = ∑ i ∈ s, b24a_umbral F (p
i)`. -/
lemma b24a_umbral_sum (F : ℕ → ℂ) (s : Finset ℕ) (p : ℕ → ℂ[X]) :
    b24a_umbral F (∑ i ∈ s, p i) = ∑ i ∈ s, b24a_umbral F (p i) := by
  induction s using Finset.induction_on with
  | empty => simp [b24a_umbral]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, b24a_umbral_add, ih]

/-- Formula under the stated hypotheses: `b24a_umbral F (C a * (X + C h) ^ n) = a * ∑ k ∈ range (n
+ 1), (n.choose k : ℂ) * F k * h ^ (n - k)`. -/
lemma b24a_umbral_C_mul_X_add_C_pow (F : ℕ → ℂ) (n : ℕ) (a h : ℂ) :
    b24a_umbral F (C a * (X + C h) ^ n) =
      a * ∑ k ∈ range (n + 1), (n.choose k : ℂ) * F k * h ^ (n - k) := by
  rw [add_pow, mul_sum, b24a_umbral_sum, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [show C a * (X ^ k * C h ^ (n - k) * (n.choose k : ℂ[X])) =
      Polynomial.monomial k (a * h ^ (n - k) * n.choose k) by
    rw [← Polynomial.C_mul_X_pow_eq_monomial]; simp only [map_mul, map_pow, map_natCast]; ring,
    b24a_umbral_monomial]
  ring

/-- The umbral substitution of DLMF §24.4(viii) for Bernoulli polynomials: expand the complex
polynomial `P` in powers of its variable and replace each power `yⁿ` by `Bₙ(x)`; this is the
meaning of `P(B(x))` with `(B(x))ⁿ = Bₙ(x)`. -/
@[dlmf 24.4.viii]
def umbralBernoulli (x : ℂ) (P : ℂ[X]) : ℂ := b24a_umbral (fun i => bernoulliPolyB i x) P

/-- The umbral substitution `(E(x))ⁿ = Eₙ(x)` of DLMF §24.4(viii). -/
@[dlmf 24.4.viii]
def umbralEuler (x : ℂ) (P : ℂ[X]) : ℂ := b24a_umbral (fun i => eulerPolyE i x) P

/-- **DLMF 24.4.36**: `P(B(x) + 1) - P(B(x)) = P'(x)` for every polynomial `P`. -/
@[dlmf 24.4.E36]
theorem umbralBernoulli_comp_add_one_sub (x : ℂ) (P : ℂ[X]) :
    umbralBernoulli x (P.comp (X + 1)) - umbralBernoulli x P =
      (Polynomial.derivative P).eval x := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [umbralBernoulli, Polynomial.add_comp, b24a_umbral_add, Polynomial.derivative_add,
      Polynomial.eval_add] at *
    linear_combination hp + hq
  | monomial n a =>
    rw [umbralBernoulli, umbralBernoulli, Polynomial.monomial_comp,
      show (X + 1 : ℂ[X]) = X + C 1 by simp, b24a_umbral_C_mul_X_add_C_pow, b24a_umbral_monomial,
      Polynomial.derivative_monomial, Polynomial.eval_monomial]
    have h := bernoulliPolyB_add n x 1
    rw [← h]
    linear_combination a * bernoulliPolyB_add_one_sub n x

/-- **DLMF 24.4.37**: `Bₙ(x + h) = (B(x) + h)ⁿ`. -/
@[dlmf 24.4.E37]
theorem umbralBernoulli_X_add_C_pow (n : ℕ) (x h : ℂ) :
    bernoulliPolyB n (x + h) = umbralBernoulli x ((X + Polynomial.C h) ^ n) := by
  rw [umbralBernoulli, ← one_mul ((X + Polynomial.C h) ^ n), ← map_one Polynomial.C,
    b24a_umbral_C_mul_X_add_C_pow, one_mul, bernoulliPolyB_add]

/-- **DLMF 24.4.38**: `P(E(x) + 1) + P(E(x)) = 2P(x)` for every polynomial `P`. -/
@[dlmf 24.4.E38]
theorem umbralEuler_comp_add_one_add (x : ℂ) (P : ℂ[X]) :
    umbralEuler x (P.comp (X + 1)) + umbralEuler x P = 2 * P.eval x := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [umbralEuler, Polynomial.add_comp, b24a_umbral_add, Polynomial.eval_add] at *
    linear_combination hp + hq
  | monomial n a =>
    rw [umbralEuler, umbralEuler, Polynomial.monomial_comp,
      show (X + 1 : ℂ[X]) = X + C 1 by simp, b24a_umbral_C_mul_X_add_C_pow, b24a_umbral_monomial,
      Polynomial.eval_monomial]
    have h := eulerPolyE_add n x 1
    rw [← h]
    linear_combination a * eulerPolyE_add_one_add n x

/-- **DLMF 24.4.39**: `Eₙ(x + h) = (E(x) + h)ⁿ`. -/
@[dlmf 24.4.E39]
theorem umbralEuler_X_add_C_pow (n : ℕ) (x h : ℂ) :
    eulerPolyE n (x + h) = umbralEuler x ((X + Polynomial.C h) ^ n) := by
  rw [umbralEuler, ← one_mul ((X + Polynomial.C h) ^ n), ← map_one Polynomial.C,
    b24a_umbral_C_mul_X_add_C_pow, one_mul, eulerPolyE_add]

end DLMF.BernoulliEuler
