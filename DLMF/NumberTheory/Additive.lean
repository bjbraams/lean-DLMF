/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.RingTheory.PowerSeriesEvaluation
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import Mathlib.NumberTheory.SumFourSquares

/-!
# Functions of additive number theory (DLMF §27.13)

Waring's `g(k)` and `G(k)` (§27.13(iii)) are defined as infima of the admissible numbers of
`k`th powers (`waringSmallG`, `waringBigG`); `sInf ∅ = 0` is only a junk value, Hilbert's
theorem (`waring_hilbert`) shows that the sets are nonempty. `r_k(n)` (27.13.3) is
`sumSquaresCount k n`, the number of `(x₁, …, x_k) ∈ ℤ^k` with `x₁² + ⋯ + x_k² = n`. DLMF's
`ϑ(x) = 1 + 2∑ x^{m²}` (27.13.4) is `jacobiThetaSeries x`; it is Mathlib's `jacobiTheta τ` at
`x = e^{πiτ}` (`jacobiTheta_eq_jacobiThetaSeries`) and the project's `θ₃(0, q)`.

Goldbach's conjecture and the Hardy–Littlewood conjectures on `G(k)` are open: they are named
as propositions (`GoldbachConjecture`, `HardyLittlewoodWaringConjecture`) and not asserted.
Lagrange's four-square theorem is Mathlib's `Nat.sum_four_squares`.
-/

@[expose] public noncomputable section

open Finset Filter ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.Omega Real

namespace DLMF.NumberTheory

/-! ### §27.13(ii) Goldbach conjecture -/

/-- §27.13(ii): Goldbach's conjecture, every even integer `n > 4` is the sum of two odd primes
(an open problem; stated as a proposition only). -/
@[dlmf 27.13.ii]
def GoldbachConjecture : Prop :=
  ∀ n : ℕ, Even n → 4 < n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ n = p + q

/-- §27.13(ii) (Vinogradov): every sufficiently large odd integer is the sum of three odd
primes. -/
@[dlmf 27.13.ii]
theorem vinogradov_three_primes :
    ∀ᶠ n : ℕ in atTop, Odd n →
      ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  sorry

/-- §27.13(ii) (Chen): every sufficiently large even integer is the sum of a prime and a number
with at most two prime factors. -/
@[dlmf 27.13.ii]
theorem chen_even :
    ∀ᶠ n : ℕ in atTop, Even n → ∃ p m : ℕ, p.Prime ∧ 1 < m ∧ Ω m ≤ 2 ∧ n = p + m := by
  sorry

/-! ### §27.13(iii) Waring's problem -/

/-- DLMF 27.13.1: every `n ≥ 1` is a sum `x₁^k + ⋯ + x_m^k` of `m` `k`th powers of
nonnegative integers. -/
@[dlmf 27.13.E1]
def IsWaringNumber (k m : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ x : Fin m → ℕ, n = ∑ i, x i ^ k

/-- §27.13(iii): `g(k)`, the smallest `m` for which 27.13.1 is solvable for all `n ≥ 1`. -/
@[dlmf 27.13.E1]
def waringSmallG (k : ℕ) : ℕ := sInf {m | IsWaringNumber k m}

/-- §27.13(iii): `G(k)`, the smallest `m` for which 27.13.1 is solvable for all sufficiently
large `n`. -/
@[dlmf 27.13.E1]
def waringBigG (k : ℕ) : ℕ :=
  sInf {m | ∀ᶠ n : ℕ in atTop, ∃ x : Fin m → ℕ, n = ∑ i, x i ^ k}

/-- §27.13(iii) (Lagrange): every positive integer is a sum of four squares; Mathlib's
`Nat.sum_four_squares`. -/
@[dlmf 27.13.iii]
theorem isWaringNumber_two_four : IsWaringNumber 2 4 := by
  intro n _
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  exact ⟨![a, b, c, d], by simp [Fin.sum_univ_four, h]⟩

/-- §27.13(iii) (Lagrange): `g(2) = 4`. -/
@[dlmf 27.13.iii]
theorem waringSmallG_two : waringSmallG 2 = 4 := by
  have h7 : ∀ m ≤ 3, ¬ IsWaringNumber 2 m := by
    intro m hm h
    obtain ⟨x, hx⟩ := h 7 (by norm_num)
    have hb : ∀ i, x i ≤ 2 := by
      intro i
      have : x i ^ 2 ≤ 7 := by
        rw [hx]
        exact Finset.single_le_sum (f := fun i ↦ x i ^ 2) (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_univ i)
      nlinarith
    interval_cases m
    · simp at hx
    · simp at hx
      have := hb 0; interval_cases (x 0) <;> omega
    · simp [Fin.sum_univ_succ] at hx
      have := hb 0; have := hb 1; interval_cases (x 0) <;> interval_cases (x 1) <;> omega
    · simp [Fin.sum_univ_succ] at hx
      have := hb 0; have := hb 1; have := hb 2
      interval_cases (x 0) <;> interval_cases (x 1) <;> interval_cases (x 2) <;> omega
  apply le_antisymm (Nat.sInf_le isWaringNumber_two_four)
  have hne : {m | IsWaringNumber 2 m}.Nonempty := ⟨4, isWaringNumber_two_four⟩
  by_contra hlt
  exact h7 _ (by omega) (Nat.sInf_mem hne)

/-- §27.13(iii) (Hilbert): `g(k)` exists for every `k ≥ 1`. -/
@[dlmf 27.13.iii]
theorem waring_hilbert (k : ℕ) (hk : 1 ≤ k) : ∃ m, IsWaringNumber k m := by
  sorry

/-- §27.13(iii): `g(3) = 9`, `g(4) = 19`, `g(5) = 37`, `g(6) = 73`, `g(7) = 143`, `g(8) = 279`. -/
@[dlmf 27.13.iii]
theorem waringSmallG_values :
    waringSmallG 3 = 9 ∧ waringSmallG 4 = 19 ∧ waringSmallG 5 = 37 ∧ waringSmallG 6 = 73 ∧
      waringSmallG 7 = 143 ∧ waringSmallG 8 = 279 := by
  sorry

/-- DLMF 27.13.2: `g(k) ≥ 2^k + ⌊3^k/2^k⌋ - 2` for all `k ≥ 2`. -/
@[dlmf 27.13.E2]
theorem waringSmallG_ge (k : ℕ) (hk : 2 ≤ k) : 2 ^ k + 3 ^ k / 2 ^ k - 2 ≤ waringSmallG k := by
  sorry

/-- §27.13(iii) after 27.13.2: equality holds in 27.13.2 for `4 ≤ k ≤ 200000`. -/
@[dlmf 27.13.E2]
theorem waringSmallG_eq_of_le (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 200000) :
    waringSmallG k = 2 ^ k + 3 ^ k / 2 ^ k - 2 := by
  sorry

/-- §27.13(iii) after 27.13.2: if `3^k = q 2^k + r` with `0 < r < 2^k`, equality holds in
27.13.2 provided `r + q ≤ 2^k`. -/
@[dlmf 27.13.E2]
theorem waringSmallG_eq_of_rem (k : ℕ) (hk : 2 ≤ k) (h : 3 ^ k % 2 ^ k + 3 ^ k / 2 ^ k ≤ 2 ^ k) :
    waringSmallG k = 2 ^ k + 3 ^ k / 2 ^ k - 2 := by
  sorry

/-- §27.13(iii) after 27.13.2 (Mahler): the condition `r + q ≤ 2^k` fails for at most finitely
many `k`. -/
@[dlmf 27.13.E2]
theorem waring_rem_condition_eventually :
    ∀ᶠ k : ℕ in atTop, 3 ^ k % 2 ^ k + 3 ^ k / 2 ^ k ≤ 2 ^ k := by
  sorry

/-- §27.13(iii): `G(k) ≤ g(k)` (`k ≥ 1`). -/
@[dlmf 27.13.iii]
theorem waringBigG_le_waringSmallG (k : ℕ) (hk : 1 ≤ k) : waringBigG k ≤ waringSmallG k := by
  apply Nat.sInf_le
  have hne : {m | IsWaringNumber k m}.Nonempty := waring_hilbert k hk
  have hmem : IsWaringNumber k (waringSmallG k) := Nat.sInf_mem hne
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact hmem n hn

/-- §27.13(iii): `G(2) = 4` and `G(4) = 16`. -/
@[dlmf 27.13.iii]
theorem waringBigG_values : waringBigG 2 = 4 ∧ waringBigG 4 = 16 := by
  sorry

/-- §27.13(iii): `G(3) ≤ 7`, `G(5) ≤ 23`, `G(6) ≤ 36`, `G(7) ≤ 53`, `G(8) ≤ 73`. -/
@[dlmf 27.13.iii]
theorem waringBigG_bounds :
    waringBigG 3 ≤ 7 ∧ waringBigG 5 ≤ 23 ∧ waringBigG 6 ≤ 36 ∧ waringBigG 7 ≤ 53 ∧
      waringBigG 8 ≤ 73 := by
  sorry

/-- §27.13(iii): the Hardy–Littlewood conjectures `G(k) < 2k + 1` for `k` not a power of `2`
and `G(k) ≤ 4k` for `k` a power of `2` (open; stated as a proposition only). -/
@[dlmf 27.13.iii]
def HardyLittlewoodWaringConjecture : Prop :=
  ∀ k : ℕ, 2 ≤ k → ((¬ ∃ j, k = 2 ^ j) → waringBigG k < 2 * k + 1) ∧
    ((∃ j, k = 2 ^ j) → waringBigG k ≤ 4 * k)

/-- §27.13(iii): `G(k) < c k ln k` for some constant `c`. -/
@[dlmf 27.13.iii]
theorem waringBigG_lt : ∃ c : ℝ, ∀ k : ℕ, 2 ≤ k → (waringBigG k : ℝ) < c * k * Real.log k := by
  sorry

/-! ### §27.13(iv) Representation by squares -/

/-- DLMF 27.13.3: `r_k(n)`, the number of solutions of `n = x₁² + ⋯ + x_k²` in integers
(positive, negative or zero, order taken into account). -/
@[dlmf 27.13.E3]
def sumSquaresCount (k n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin k ↦ Finset.Icc (-(n : ℤ)) n).filter
    fun x ↦ ∑ i, x i ^ 2 = (n : ℤ)).card

/-- DLMF 27.13.4: `ϑ(x) = 1 + 2 ∑_{m≥1} x^{m²}`, `|x| < 1` (a totalized `tsum`). -/
@[dlmf 27.13.E4]
def jacobiThetaSeries (x : ℂ) : ℂ := 1 + 2 * ∑' m : ℕ, x ^ ((m + 1) ^ 2)

/-- §27.13(iv) after 27.13.4: `ϑ(e^{πiτ})` is Mathlib's `jacobiTheta τ` (`= θ₃(0|τ)`),
`ℑτ > 0`. -/
@[dlmf 27.13.E4]
theorem jacobiTheta_eq_jacobiThetaSeries {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta τ = jacobiThetaSeries (Complex.exp (π * Complex.I * τ)) := by
  rw [jacobiTheta_eq_tsum_nat hτ, jacobiThetaSeries]
  congr 3
  funext n
  rw [← Complex.exp_nat_mul]
  push_cast
  ring_nf

section R27Helpers

open PowerSeries

/-- Sums over `I^{k+1}` split off the first coordinate. -/
lemma r27_sum_piFinset_succ {k : ℕ} (I : Finset ℤ) (g : (Fin (k + 1) → ℤ) → ℤ) :
    ∑ v ∈ Fintype.piFinset (fun _ : Fin (k + 1) ↦ I), g v =
      ∑ a ∈ I, ∑ w ∈ Fintype.piFinset (fun _ : Fin k ↦ I), g (Fin.cons a w) := by
  rw [← sum_product' (f := fun a w ↦ g (Fin.cons a w))]
  refine sum_nbij' (fun v ↦ (v 0, Fin.tail v)) (fun p ↦ Fin.cons p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Fintype.mem_piFinset] at hv
    simp only [mem_product, Fintype.mem_piFinset]
    exact ⟨hv 0, fun i ↦ hv i.succ⟩
  · intro p hp
    simp only [mem_product, Fintype.mem_piFinset] at hp
    simp only [Fintype.mem_piFinset]
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa using hp.1
    · simpa using hp.2 j
  · intro v _; simp
  · intro p _; simp
  · intro v _; simp

/-- The number of `v ∈ [-B, B]^k` with `∑ vᵢ² = m`. -/
def r27_cnt (k B : ℕ) (m : ℤ) : ℤ :=
  ∑ v ∈ Fintype.piFinset (fun _ : Fin k ↦ Icc (-(B : ℤ)) B), if ∑ i, v i ^ 2 = m then 1 else 0

/-- `cnt₀(m) = [m = 0]`. -/
lemma r27_cnt_zero (B : ℕ) (m : ℤ) : r27_cnt 0 B m = if 0 = m then 1 else 0 := by
  simp [r27_cnt]

/-- Recursion for the representation counts. -/
lemma r27_cnt_succ (k B : ℕ) (m : ℤ) :
    r27_cnt (k + 1) B m = ∑ a ∈ Icc (-(B : ℤ)) B, r27_cnt k B (m - a ^ 2) := by
  rw [r27_cnt, r27_sum_piFinset_succ]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [r27_cnt]
  refine sum_congr rfl fun w _ ↦ ?_
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  congr 1
  apply propext; constructor <;> intro h <;> linarith

/-- `r_k(n)` with any box `[-B, B]`, `B ≥ n`. -/
lemma r27_sumSquaresCount_eq_cnt (k n B : ℕ) (hB : n ≤ B) :
    (sumSquaresCount k n : ℤ) = r27_cnt k B n := by
  rw [r27_cnt, sum_boole, sumSquaresCount]
  congr 1
  apply congrArg
  ext v
  simp only [mem_filter, Fintype.mem_piFinset, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun i ↦ ⟨by linarith [(h1 i).1], by linarith [(h1 i).2]⟩, h2⟩
  · rintro ⟨_, h2⟩
    refine ⟨fun i ↦ ?_, h2⟩
    have hle : v i ^ 2 ≤ n := by
      rw [← h2]
      exact single_le_sum (f := fun j ↦ v j ^ 2) (fun j _ ↦ sq_nonneg _) (mem_univ i)
    have : |v i| ≤ v i ^ 2 := by
      rcases eq_or_ne (v i) 0 with h | h
      · simp [h]
      · rw [← sq_abs]; nlinarith [abs_pos.mpr h, Int.one_le_abs h]
    constructor <;> [linarith [neg_abs_le (v i)]; linarith [le_abs_self (v i)]]

/-- No representations of negative numbers. -/
lemma r27_cnt_neg (k B : ℕ) {m : ℤ} (hm : m < 0) : r27_cnt k B m = 0 := by
  rw [r27_cnt]
  refine sum_eq_zero fun v _ ↦ ?_
  have : 0 ≤ ∑ i, v i ^ 2 := sum_nonneg fun i _ ↦ sq_nonneg _
  have h : ∑ i, v i ^ 2 ≠ m := by intro h; linarith
  simp [h]

/-- `∑_{x ∈ ℤ} X^{x²}` as an integer power series (coefficients `r₁(n)`). -/
def r27_thetaSeries : PowerSeries ℤ := PowerSeries.mk fun n ↦ (sumSquaresCount 1 n : ℤ)

/-- The coefficients of `ϑ^k` are `r_k(n)` (formal identity). -/
lemma r27_coeff_thetaSeries_pow (k n : ℕ) :
    coeff n (r27_thetaSeries ^ k) = sumSquaresCount k n := by
  induction k generalizing n with
  | zero =>
    rw [pow_zero, coeff_one, r27_sumSquaresCount_eq_cnt 0 n n le_rfl, r27_cnt_zero]
    by_cases h : n = 0 <;> simp [h, eq_comm]
  | succ k ih =>
    rw [pow_succ, coeff_mul, r27_sumSquaresCount_eq_cnt (k + 1) n n le_rfl, r27_cnt_succ]
    have h1 : ∀ p ∈ antidiagonal n, coeff p.1 (r27_thetaSeries ^ k) * coeff p.2 r27_thetaSeries =
        ∑ a ∈ Icc (-(n : ℤ)) n, r27_cnt k n p.1 * (if (p.2 : ℤ) = a ^ 2 then 1 else 0) := by
      intro p hp
      have hp' := mem_antidiagonal.mp hp
      have hp1 : p.1 ≤ n := by omega
      have hp2 : p.2 ≤ n := by omega
      rw [ih, r27_sumSquaresCount_eq_cnt k p.1 n hp1, r27_thetaSeries, coeff_mk,
        r27_sumSquaresCount_eq_cnt 1 p.2 n hp2, r27_cnt_succ, mul_sum]
      refine sum_congr rfl fun a _ ↦ ?_
      rw [r27_cnt_zero]
      congr 1
      by_cases h : (p.2 : ℤ) = a ^ 2
      · simp [h]
      · have : (0 : ℤ) ≠ p.2 - a ^ 2 := by omega
        simp [h, this]
    rw [sum_congr rfl h1, sum_comm]
    refine sum_congr rfl fun a _ ↦ ?_
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only
    by_cases ha : a ^ 2 ≤ n
    · have ha0 : 0 ≤ a ^ 2 := sq_nonneg a
      set t := (a ^ 2).toNat with ht
      have hta : (t : ℤ) = a ^ 2 := Int.toNat_of_nonneg ha0
      have htn : t ≤ n := by omega
      rw [sum_eq_single (n - t)]
      · have : ((n - (n - t) : ℕ) : ℤ) = a ^ 2 := by rw [Nat.sub_sub_self htn, hta]
        simp only [this, ite_true, mul_one]
        congr 1; push_cast [Nat.cast_sub htn]; omega
      · intro i hi hit
        rw [mem_range] at hi
        have : ((n - i : ℕ) : ℤ) ≠ a ^ 2 := by
          rw [← hta]; intro h; apply hit; omega
        simp [this]
      · intro h; exfalso; apply h; rw [mem_range]; omega
    · rw [r27_cnt_neg k n (by omega)]
      refine sum_eq_zero fun i hi ↦ ?_
      rw [mem_range] at hi
      have : ((n - i : ℕ) : ℤ) ≠ a ^ 2 := by omega
      simp [this]

open Classical in
/-- `r₁(n)`: `1` at `n = 0`, `2` at positive squares, `0` otherwise. -/
lemma r27_sumSquaresCount_one (n : ℕ) :
    (sumSquaresCount 1 n : ℤ) = if n = 0 then 1 else if ∃ m : ℕ, (m + 1) ^ 2 = n then 2 else 0 := by
  rw [r27_sumSquaresCount_eq_cnt 1 n n le_rfl, r27_cnt_succ]
  simp_rw [r27_cnt_zero]
  rw [sum_boole]
  have key : ∀ a : ℤ, (0 = (n : ℤ) - a ^ 2) ↔ a ^ 2 = n := fun a ↦ by
    constructor <;> intro h <;> linarith
  simp_rw [key]
  split_ifs with h0 hm
  · subst h0
    rw [show ((Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ)).filter fun a : ℤ ↦ a ^ 2 = ((0 : ℕ) : ℤ)) =
        {0} by
      ext a; simp only [mem_filter, mem_Icc, mem_singleton]; constructor
      · rintro ⟨_, h⟩; simpa using h
      · rintro rfl; simp]
    simp
  · obtain ⟨m, rfl⟩ := hm
    rw [show ((Icc (-(((m + 1) ^ 2 : ℕ) : ℤ)) (((m + 1) ^ 2 : ℕ) : ℤ)).filter
        fun a : ℤ ↦ a ^ 2 = (((m + 1) ^ 2 : ℕ) : ℤ)) = {((m + 1 : ℕ) : ℤ), -((m + 1 : ℕ) : ℤ)} by
      ext a; simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]
      push_cast
      constructor
      · rintro ⟨_, h⟩; exact sq_eq_sq_iff_eq_or_eq_neg.mp h
      · rintro (rfl | rfl) <;> refine ⟨⟨by nlinarith, by nlinarith⟩, by ring⟩]
    rw [card_insert_of_notMem (by simp; omega)]
    simp
  · rw [Finset.card_eq_zero.mpr]
    · simp
    rw [filter_eq_empty_iff]
    intro a _ ha
    apply hm
    refine ⟨a.natAbs - 1, ?_⟩
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha; omega
    have : 1 ≤ a.natAbs := Int.natAbs_pos.mpr ha0
    have h2 : ((a.natAbs : ℤ)) ^ 2 = n := by rw [Int.natAbs_sq]; exact ha
    have h3 : (a.natAbs - 1 + 1) = a.natAbs := by omega
    rw [h3]; exact_mod_cast h2

open Classical in
/-- `ϑ(x) = ∑ r₁(n) xⁿ` converges absolutely in the unit disc. -/
lemma r27_absEval_thetaSeries {x : ℂ} (hx : ‖x‖ < 1) :
    PowerSeries.HasSumAt r27_thetaSeries x (jacobiThetaSeries x) := by
  have hc : ∀ n, ((coeff n r27_thetaSeries : ℤ) : ℂ) * x ^ n =
      (if n = 0 then 1 else 0) +
        (if ∃ m : ℕ, (m + 1) ^ 2 = n then 2 * x ^ n else 0) := by
    intro n
    rw [r27_thetaSeries, coeff_mk, r27_sumSquaresCount_one]
    by_cases h0 : n = 0
    · subst h0; simp
    · by_cases hm : ∃ m : ℕ, (m + 1) ^ 2 = n <;> simp [h0]
  have hb := PowerSeries.hasSumAt_of_bounded (P := r27_thetaSeries) (C := 2) (fun n ↦ by
    rw [r27_thetaSeries, coeff_mk, r27_sumSquaresCount_one]; split_ifs <;> norm_num) hx
  convert hb using 1
  rw [jacobiThetaSeries]
  symm
  refine HasSum.tsum_eq ?_
  simp_rw [hc]
  refine (hasSum_ite_eq 0 (1 : ℂ)).add ?_
  have hinj : Function.Injective fun m : ℕ ↦ (m + 1) ^ 2 := by
    intro a b h; simp only at h
    have := Nat.pow_left_injective (n := 2) (by norm_num) h; omega
  have hsumm : Summable fun m : ℕ ↦ x ^ ((m + 1) ^ 2) := by
    refine (summable_geometric_of_lt_one (norm_nonneg x) hx).of_norm_bounded fun m ↦ ?_
    rw [norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg x) hx.le (by nlinarith)
  rw [← hinj.hasSum_iff]
  · convert (hsumm.hasSum.mul_left 2) using 1
    funext m
    simp only [Function.comp_apply]
    simp
  · intro n hn
    have : ¬ ∃ m : ℕ, (m + 1) ^ 2 = n := by rintro ⟨m, rfl⟩; exact hn ⟨m, rfl⟩
    simp [this]

end R27Helpers

/-- DLMF 27.13.5: `ϑ(x)² = 1 + ∑_{n≥1} r₂(n) xⁿ`, `|x| < 1`. -/
@[dlmf 27.13.E5]
theorem jacobiThetaSeries_sq {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ ↦ (sumSquaresCount 2 (n + 1) : ℂ) * x ^ (n + 1))
      (jacobiThetaSeries x ^ 2 - 1) := by
  open PowerSeries in
  have h := (PowerSeries.HasSumAt.pow (r27_absEval_thetaSeries hx) 2)
  simp only [PowerSeries.HasSumAt, r27_coeff_thetaSeries_pow, Int.cast_natCast] at h
  have h0 : sumSquaresCount 2 0 = 1 := by rfl
  have h1 := (hasSum_nat_add_iff' 1).mpr h
  simpa [h0] using h1

/-- §27.13(iv) (Mordell): `r_k(n)` is the coefficient of `xⁿ` in `ϑ(x)^k`, `|x| < 1`. -/
@[dlmf 27.13.iv]
theorem jacobiThetaSeries_pow (k : ℕ) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ ↦ (sumSquaresCount k n : ℂ) * x ^ n) (jacobiThetaSeries x ^ k) := by
  open PowerSeries in
  have h := (PowerSeries.HasSumAt.pow (r27_absEval_thetaSeries hx) k)
  simpa only [PowerSeries.HasSumAt, r27_coeff_thetaSeries_pow, Int.cast_natCast] using h

/-- DLMF 27.13.6 (Jacobi): `ϑ(x)² = 1 + 4 ∑_{n≥1} (δ₁(n) - δ₃(n)) xⁿ`, with `δ_j(n)` the number of
divisors of `n` congruent to `j` mod 4. -/
@[dlmf 27.13.E6]
theorem jacobiThetaSeries_sq_divisors {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ ↦ 4 * ((((n + 1).divisors.filter (· % 4 = 1)).card : ℂ) -
        ((n + 1).divisors.filter (· % 4 = 3)).card) * x ^ (n + 1))
      (jacobiThetaSeries x ^ 2 - 1) := by
  sorry

/-- DLMF 27.13.7 (Jacobi): `r₂(n) = 4(δ₁(n) - δ₃(n))`, `n ≥ 1`. -/
@[dlmf 27.13.E7]
theorem sumSquaresCount_two {n : ℕ} (hn : 1 ≤ n) :
    (sumSquaresCount 2 n : ℤ) =
      4 * (((n.divisors.filter (· % 4 = 1)).card : ℤ) - (n.divisors.filter (· % 4 = 3)).card) := by
  sorry

/-- §27.13(iv) after 27.13.7: `r₂(5) = 8`. -/
@[dlmf 27.13.E7]
theorem sumSquaresCount_two_five : sumSquaresCount 2 5 = 8 := by
  rfl

/-- §27.13(iv) (Jacobi): `r₄(n) = 8σ₁(n)` for odd `n`, and `r₄(n) = 24 ∑_{d∣n, d odd} d` for
even `n ≥ 2`. -/
@[dlmf 27.13.iv]
theorem sumSquaresCount_four {n : ℕ} (hn : 1 ≤ n) :
    (Odd n → sumSquaresCount 4 n = 8 * σ 1 n) ∧
      (Even n → sumSquaresCount 4 n = 24 * ∑ d ∈ n.divisors.filter Odd, d) := by
  sorry

end DLMF.NumberTheory
