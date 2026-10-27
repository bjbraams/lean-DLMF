/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.NumberTheory.DirichletSeries
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# Inversion formulas (DLMF §27.5)

The Dirichlet product (27.5.1) is the multiplication of Mathlib's `ArithmeticFunction` ring,
and on plain sequences `LSeries.convolution` (`f ⍟ g`); `LSeriesHasSum.convolution` is the
statement that `F(s)G(s)` generates `f ⍟ g`. The Möbius inversion formulas 27.5.3 and 27.5.8
are Mathlib's `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` and
`ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_of_nonzero`, restated here with DLMF's
divisor-sum form `∑_{d∣n} g(d) μ(n/d)`. For 27.5.8 the values must be nonzero (DLMF's
`g(n/d)^{μ(d)}` with `μ(d) = -1` needs inverses). For 27.5.6 only the values on `x ≥ 1`
enter, and for 27.5.7 we add the absolute convergence hypotheses that DLMF leaves implicit.
-/

@[expose] public noncomputable section

open Finset Filter ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.Moebius ArithmeticFunction.zeta
  LSeries.notation

namespace DLMF.NumberTheory

/-- DLMF 27.5.1: the Dirichlet product `h(n) = ∑_{d∣n} f(d) g(n/d)`; if `F(s)` generates `f`
and `G(s)` generates `g`, then `F(s)G(s)` generates `h`. -/
@[dlmf 27.5.E1]
theorem dirichletProduct_apply_hasSum (f g : ArithmeticFunction ℂ) {s a b : ℂ}
    (hf : LSeriesHasSum ↗f s a) (hg : LSeriesHasSum ↗g s b) :
    (∀ n, (f * g) n = ∑ d ∈ n.divisors, f d * g (n / d)) ∧
      LSeriesHasSum ↗(f * g) s (a * b) := by
  refine ⟨fun n ↦ ?_, LSeriesHasSum_mul hf hg⟩
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y ↦ f x * g y)]

/-- §27.5, after 27.5.1: the functions with `f(1) ≠ 0` are the units of the ring of
arithmetic functions (an abelian group under Dirichlet multiplication), with identity
`⌊1/n⌋`; the multiplicative functions form a subgroup. -/
@[dlmf 27.5]
theorem isUnit_iff_apply_one_ne_zero (f : ArithmeticFunction ℂ) :
    IsUnit f ↔ f 1 ≠ 0 := by
  rw [isUnit_iff_isUnit_apply_one, isUnit_iff_ne_zero]

/-- §27.5, after 27.5.1: the identity of Dirichlet multiplication is `⌊1/n⌋` (27.2.5). -/
@[dlmf 27.5]
theorem one_apply_eq_floor {n : ℕ} (hn : 0 < n) :
    ((1 : ArithmeticFunction ℤ) n) = ⌊(1 : ℝ) / n⌋ := by
  rw [floor_one_div hn, one_apply]

/-- The multiplicative function with prescribed values `h(p^e)` at prime powers. -/
def q27_multOfPrimePow {R : Type*} [CommMonoidWithZero R] (h : ℕ → R) : ArithmeticFunction R :=
  ⟨fun n ↦ if n = 0 then 0 else ∏ p ∈ n.primeFactors, h (p ^ n.factorization p), by simp⟩

/-- Value of `q27_multOfPrimePow` at `n ≠ 0`. -/
lemma q27_multOfPrimePow_apply {R : Type*} [CommMonoidWithZero R] (h : ℕ → R) {n : ℕ}
    (hn : n ≠ 0) : q27_multOfPrimePow h n = ∏ p ∈ n.primeFactors, h (p ^ n.factorization p) := by
  simp [q27_multOfPrimePow, hn]

/-- `q27_multOfPrimePow h` is multiplicative. -/
lemma q27_isMultiplicative_multOfPrimePow {R : Type*} [CommMonoidWithZero R] (h : ℕ → R) :
    (q27_multOfPrimePow h).IsMultiplicative := by
  refine ⟨by simp [q27_multOfPrimePow_apply], fun {m n} hmn ↦ ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [q27_multOfPrimePow_apply h (mul_ne_zero hm hn), q27_multOfPrimePow_apply h hm,
    q27_multOfPrimePow_apply h hn, Nat.Coprime.primeFactors_mul hmn,
    prod_union hmn.disjoint_primeFactors, Nat.factorization_mul hm hn]
  congr 1
  · refine prod_congr rfl fun p hp ↦ ?_
    have h0 : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd fun hpn ↦
      (Nat.prime_of_mem_primeFactors hp).one_lt.ne'
        ((hmn.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp)).eq_one_of_dvd hpn)
    rw [Finsupp.add_apply, h0, add_zero]
  · refine prod_congr rfl fun p hp ↦ ?_
    have h0 : m.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd fun hpm ↦
      (Nat.prime_of_mem_primeFactors hp).one_lt.ne'
        ((hmn.symm.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp)).eq_one_of_dvd hpm)
    rw [Finsupp.add_apply, h0, zero_add]

/-- The Dirichlet inverse of a multiplicative function is multiplicative. -/
lemma q27_isMultiplicative_of_mul_eq_one {f h : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) (hh : f * h = 1) : h.IsMultiplicative := by
  set g := q27_multOfPrimePow (fun n ↦ h n) with hgdef
  have hg : g.IsMultiplicative := q27_isMultiplicative_multOfPrimePow _
  have hgpp : ∀ p e, p.Prime → g (p ^ e) = h (p ^ e) := by
    intro p e hp
    rcases e with _ | e
    · rw [pow_zero, hg.map_one]
      have := congrArg (fun F : ArithmeticFunction ℂ ↦ F 1) hh
      simp only [mul_apply, Nat.divisorsAntidiagonal_one, sum_singleton, one_one,
        hf.map_one, one_mul] at this
      exact this.symm
    rw [hgdef, q27_multOfPrimePow_apply _ (pow_ne_zero _ hp.ne_zero), Nat.primeFactors_prime_pow
      (Nat.succ_ne_zero e) hp, prod_singleton, Nat.factorization_pow_self hp]
  have hfg : f * g = 1 := by
    refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (hf.mul hg) _
      isMultiplicative_one).mpr fun p e hp ↦ ?_
    rw [← hh, q27_mul_apply_prime_pow _ _ hp, q27_mul_apply_prime_pow _ _ hp]
    exact sum_congr rfl fun i _ ↦ by rw [hgpp p _ hp]
  have : h = g := by
    calc h = h * (f * g) := by rw [hfg, mul_one]
      _ = (f * h) * g := by ring
      _ = g := by rw [hh, one_mul]
  rw [this]; exact hg

/-- §27.5, after 27.5.1: multiplicative functions are closed under Dirichlet products and
inverses. -/
@[dlmf 27.5]
theorem isMultiplicative_mul_inv {f g : ArithmeticFunction ℂ} (hf : f.IsMultiplicative)
    (hg : g.IsMultiplicative) :
    (f * g).IsMultiplicative ∧ ∀ h : ArithmeticFunction ℂ, f * h = 1 → h.IsMultiplicative := by
  exact ⟨hf.mul hg, fun h hh ↦ q27_isMultiplicative_of_mul_eq_one hf hh⟩

/-- DLMF 27.5.2: `∑_{d∣n} μ(d) = ⌊1/n⌋`. -/
@[dlmf 27.5.E2]
theorem sum_divisors_moebius {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, μ d = ⌊(1 : ℝ) / n⌋ := by
  rw [← one_apply_eq_floor hn, ← coe_mul_zeta_apply, moebius_mul_coe_zeta]

/-- DLMF 27.5.3, the Möbius inversion formula:
`g(n) = ∑_{d∣n} f(d) ⟺ f(n) = ∑_{d∣n} g(d) μ(n/d)` (for all `n ≥ 1`). -/
@[dlmf 27.5.E3]
theorem moebius_inversion {R : Type*} [CommRing R] (f g : ℕ → R) :
    (∀ n > 0, g n = ∑ d ∈ n.divisors, f d) ↔
      ∀ n > 0, f n = ∑ d ∈ n.divisors, g d * μ (n / d) := by
  have h := sum_eq_iff_sum_mul_moebius_eq (f := f) (g := g)
  constructor
  · intro H n hn
    rw [← h.mp (fun n hn ↦ (H n hn).symm) n hn,
      Nat.sum_divisorsAntidiagonal' (fun x y ↦ (μ x : R) * g y)]
    exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  · intro H n hn
    refine (h.mpr (fun n hn ↦ ?_) n hn).symm
    rw [H n hn, Nat.sum_divisorsAntidiagonal' (fun x y ↦ (μ x : R) * g y)]
    exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- DLMF 27.5.4: `n = ∑_{d∣n} φ(d)` and, equivalently, `φ(n) = ∑_{d∣n} d μ(n/d)`. -/
@[dlmf 27.5.E4]
theorem sum_totient_and_inverse {n : ℕ} (hn : 0 < n) :
    (n = ∑ d ∈ n.divisors, d.totient) ∧
      (n.totient : ℤ) = ∑ d ∈ n.divisors, (d : ℤ) * μ (n / d) := by
  refine ⟨(Nat.sum_totient n).symm, ?_⟩
  refine (moebius_inversion (fun n ↦ (n.totient : ℤ)) (fun n ↦ (n : ℤ))).mp
    (fun m _ ↦ ?_) n hn
  exact_mod_cast (Nat.sum_totient m).symm

/-- DLMF 27.5.5: `ln n = ∑_{d∣n} Λ(d)` and, equivalently, `Λ(n) = ∑_{d∣n} (ln d) μ(n/d)`. -/
@[dlmf 27.5.E5]
theorem sum_vonMangoldt_and_inverse {n : ℕ} (hn : 0 < n) :
    (Real.log n = ∑ d ∈ n.divisors, vonMangoldt d) ∧
      vonMangoldt n = ∑ d ∈ n.divisors, Real.log d * μ (n / d) := by
  refine ⟨vonMangoldt_sum.symm, ?_⟩
  refine (moebius_inversion (fun n ↦ vonMangoldt n) (fun n ↦ Real.log n)).mp
    (fun m _ ↦ vonMangoldt_sum.symm) n hn

/-- `∑_{n≤N} ∑_{m≤N/n} c(n,m) = ∑_{k≤N} ∑_{ab=k} c(a,b)`. -/
lemma q27_sum_Icc_sum_Icc_div {R : Type*} [AddCommMonoid R] (c : ℕ → ℕ → R) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / n), c n m =
      ∑ k ∈ Icc 1 N, ∑ x ∈ k.divisorsAntidiagonal, c x.1 x.2 := by
  have hP : ∀ k ∈ Icc 1 N, k.divisorsAntidiagonal =
      ((Icc 1 N ×ˢ Icc 1 N).filter (fun x ↦ x.1 * x.2 ≤ N)).filter (fun x ↦ x.1 * x.2 = k) := by
    intro k hk
    rw [mem_Icc] at hk
    ext ⟨a, b⟩
    simp only [Nat.mem_divisorsAntidiagonal, mem_filter, mem_product, mem_Icc]
    constructor
    · rintro ⟨rfl, h0⟩
      have ha : 0 < a := Nat.pos_of_ne_zero (left_ne_zero_of_mul h0)
      have hb : 0 < b := Nat.pos_of_ne_zero (right_ne_zero_of_mul h0)
      refine ⟨⟨⟨⟨ha, ?_⟩, hb, ?_⟩, hk.2⟩, rfl⟩
      · exact le_trans (Nat.le_mul_of_pos_right a hb) hk.2
      · exact le_trans (Nat.le_mul_of_pos_left b ha) hk.2
    · rintro ⟨-, rfl⟩
      exact ⟨rfl, by omega⟩
  have hR : ∑ k ∈ Icc 1 N, ∑ x ∈ k.divisorsAntidiagonal, c x.1 x.2 =
      ∑ k ∈ Icc 1 N, ∑ x ∈ ((Icc 1 N ×ˢ Icc 1 N).filter (fun x ↦ x.1 * x.2 ≤ N)).filter
        (fun x ↦ x.1 * x.2 = k), c x.1 x.2 := sum_congr rfl fun k hk ↦ by rw [hP k hk]
  rw [hR]
  rw [sum_fiberwise_of_maps_to (s := (Icc 1 N ×ˢ Icc 1 N).filter (fun x ↦ x.1 * x.2 ≤ N))
    (t := Icc 1 N) (g := fun x ↦ x.1 * x.2) (f := fun x ↦ c x.1 x.2)]
  · rw [sum_filter, sum_product]
    refine sum_congr rfl fun n hn ↦ ?_
    rw [mem_Icc] at hn
    rw [← sum_filter]
    refine sum_congr ?_ fun _ _ ↦ rfl
    ext m
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, le_trans h2 (Nat.div_le_self N n)⟩,
        (Nat.le_div_iff_mul_le hn.1).mp h2 |>.trans_eq' (mul_comm _ _)⟩
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, (Nat.le_div_iff_mul_le hn.1).mpr (by rw [mul_comm]; exact h2)⟩
  · intro x hx
    simp only [mem_filter, mem_product, mem_Icc] at hx ⊢
    exact ⟨Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega)), hx.2⟩


/-- `∑_{d∣k} μ(d) = [k = 1]` in `ℂ`. -/
theorem q27_sum_divisors_moebius_eq_ite (k : ℕ) :
    ∑ d ∈ k.divisors, (μ d : ℂ) = if k = 1 then 1 else 0 := by
  have := congrArg (fun F : ArithmeticFunction ℤ ↦ ((F k : ℤ) : ℂ)) coe_zeta_mul_moebius
  simp only [coe_zeta_mul_apply, one_apply, Int.cast_sum] at this
  rw [this]; split_ifs <;> simp

/-- DLMF 27.5.6 (proof). -/
lemma q27_moebius_inversion_floor (F G : ℝ → ℂ) :
    (∀ x : ℝ, 1 ≤ x → G x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, F (x / n)) ↔
      ∀ x : ℝ, 1 ≤ x → F x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℂ) * G (x / n) := by
  have hdiv : ∀ x : ℝ, 1 ≤ x → ∀ n ∈ Icc 1 ⌊x⌋₊, 1 ≤ x / n ∧ ⌊x / n⌋₊ = ⌊x⌋₊ / n := by
    intro x hx n hn
    rw [mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    refine ⟨?_, Nat.floor_div_natCast x n⟩
    rw [le_div_iff₀ hn0, one_mul]
    exact (Nat.cast_le.mpr hn.2).trans (Nat.floor_le (by linarith))
  have hxk : ∀ (x : ℝ) (a b : ℕ), x / a / b = x / ((a * b : ℕ) : ℝ) := by
    intro x a b; push_cast; rw [div_div]
  have hfin : ∀ (x : ℝ) (H : ℝ → ℂ), 1 ≤ x →
      ∑ k ∈ Icc 1 ⌊x⌋₊, (if k = 1 then (1 : ℂ) else 0) * H (x / k) = H x := by
    intro x H hx
    have h1 : 1 ∈ Icc 1 ⌊x⌋₊ := mem_Icc.mpr ⟨le_rfl, Nat.le_floor (by simpa using hx)⟩
    rw [sum_eq_single_of_mem 1 h1]
    · simp
    · intro b _ hb; simp [hb]
  constructor
  · intro H x hx
    have e1 : ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℂ) * G (x / n) =
        ∑ n ∈ Icc 1 ⌊x⌋₊, ∑ m ∈ Icc 1 (⌊x⌋₊ / n), (μ n : ℂ) * F (x / ((n * m : ℕ) : ℝ)) := by
      refine sum_congr rfl fun n hn ↦ ?_
      rw [H _ (hdiv x hx n hn).1, (hdiv x hx n hn).2, mul_sum]
      exact sum_congr rfl fun m _ ↦ by rw [hxk]
    rw [e1, q27_sum_Icc_sum_Icc_div (fun n m ↦ (μ n : ℂ) * F (x / ((n * m : ℕ) : ℝ)))]
    have e2 : ∀ k ∈ Icc 1 ⌊x⌋₊, ∑ y ∈ k.divisorsAntidiagonal,
        (μ y.1 : ℂ) * F (x / ((y.1 * y.2 : ℕ) : ℝ)) = (if k = 1 then 1 else 0) * F (x / k) := by
      intro k _
      rw [← q27_sum_divisors_moebius_eq_ite, sum_mul,
        ← Nat.sum_divisorsAntidiagonal (fun a _ ↦ (μ a : ℂ) * F (x / k))]
      refine sum_congr rfl fun y hy ↦ ?_
      rw [(Nat.mem_divisorsAntidiagonal.mp hy).1]
    rw [sum_congr rfl e2, hfin x F hx]
  · intro H x hx
    have e1 : ∑ n ∈ Icc 1 ⌊x⌋₊, F (x / n) =
        ∑ n ∈ Icc 1 ⌊x⌋₊, ∑ m ∈ Icc 1 (⌊x⌋₊ / n), (μ m : ℂ) * G (x / ((n * m : ℕ) : ℝ)) := by
      refine sum_congr rfl fun n hn ↦ ?_
      rw [H _ (hdiv x hx n hn).1, (hdiv x hx n hn).2]
      exact sum_congr rfl fun m _ ↦ by rw [hxk]
    rw [e1, q27_sum_Icc_sum_Icc_div (fun n m ↦ (μ m : ℂ) * G (x / ((n * m : ℕ) : ℝ)))]
    have e2 : ∀ k ∈ Icc 1 ⌊x⌋₊, ∑ y ∈ k.divisorsAntidiagonal,
        (μ y.2 : ℂ) * G (x / ((y.1 * y.2 : ℕ) : ℝ)) = (if k = 1 then 1 else 0) * G (x / k) := by
      intro k _
      rw [← q27_sum_divisors_moebius_eq_ite, sum_mul,
        ← Nat.sum_divisorsAntidiagonal' (fun _ b ↦ (μ b : ℂ) * G (x / k))]
      refine sum_congr rfl fun y hy ↦ ?_
      rw [(Nat.mem_divisorsAntidiagonal.mp hy).1]
    rw [sum_congr rfl e2, hfin x G hx]

/-- DLMF 27.5.6: `G(x) = ∑_{n≤x} F(x/n) ⟺ F(x) = ∑_{n≤x} μ(n) G(x/n)`, for all `x ≥ 1`
(for `x ≥ 1` and `n ≤ x` only values on `[1, ∞)` enter). -/
@[dlmf 27.5.E6]
theorem moebius_inversion_floor (F G : ℝ → ℂ) :
    (∀ x : ℝ, 1 ≤ x → G x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, F (x / n)) ↔
      ∀ x : ℝ, 1 ≤ x → F x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℂ) * G (x / n) :=
  q27_moebius_inversion_floor F G

/-- Reindex a sum over `ℕ+` by `n ↦ n + 1`. -/
theorem q27_hasSum_pnat_iff {g : ℕ+ → ℂ} {a : ℂ} :
    HasSum g a ↔ HasSum (fun n : ℕ ↦ g n.succPNat) a :=
  (Equiv.pnatEquivNat.symm.hasSum_iff (f := g)).symm

/-- Diagonal summation over `ℕ+ × ℕ+`: `∑_{a,b} c(a,b) = ∑_n ∑_{ab=n} c(a,b)`. -/
theorem q27_hasSum_divisorsAntidiagonal {c : ℕ+ × ℕ+ → ℂ} {T : ℂ} (h : HasSum c T) :
    HasSum (fun n : ℕ+ ↦ ∑ x ∈ (n : ℕ).divisorsAntidiagonal,
      if h : 0 < x.1 ∧ 0 < x.2 then c (⟨x.1, h.1⟩, ⟨x.2, h.2⟩) else 0) T := by
  have h1 := (sigmaAntidiagonalEquivProd.hasSum_iff (f := c)).mpr h
  refine h1.sigma fun n ↦ ?_
  have := hasSum_fintype
    (fun x : (n : ℕ).divisorsAntidiagonal ↦ c (sigmaAntidiagonalEquivProd ⟨n, x⟩))
  have heq : (∑ x ∈ (n : ℕ).divisorsAntidiagonal,
      if h : 0 < x.1 ∧ 0 < x.2 then c (⟨x.1, h.1⟩, ⟨x.2, h.2⟩) else 0) =
      ∑ x : (n : ℕ).divisorsAntidiagonal, c (sigmaAntidiagonalEquivProd ⟨n, x⟩) := by
    rw [← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have hx := Nat.mem_divisorsAntidiagonal.mp x.2
    have h0 : 0 < x.1.1 ∧ 0 < x.1.2 :=
      ⟨Nat.pos_of_ne_zero (left_ne_zero_of_mul (hx.1 ▸ n.ne_zero)),
        Nat.pos_of_ne_zero (right_ne_zero_of_mul (hx.1 ▸ n.ne_zero))⟩
    rw [dite_eq_left h0]
    rfl
  rw [heq]
  exact this


/-- Absolute convergence of `∑_{a,b} w(a,b) H(abx)/(ab)^s` from `∑ d(n)|H(nx)|/n^σ < ∞`,
`|w| ≤ 1`. -/
lemma q27_summable_div_cpow (H : ℝ → ℂ) (s : ℂ) (x : ℝ)
    (hH : Summable fun n : ℕ ↦ (σ 0 (n + 1) : ℝ) * ‖H ((n + 1) * x)‖ / (n + 1 : ℝ) ^ s.re)
    (w : ℕ+ × ℕ+ → ℂ) (hw : ∀ c, ‖w c‖ ≤ 1) :
    Summable fun c : ℕ+ × ℕ+ ↦
      w c * H (((c.1 * c.2 : ℕ) : ℝ) * x) / ((c.1 * c.2 : ℕ) : ℂ) ^ s := by
  set g : ℕ → ℝ := fun n ↦ ‖H ((n : ℝ) * x)‖ / (n : ℝ) ^ s.re with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n ↦ div_nonneg (norm_nonneg _) (by positivity)
  have hbound : ∀ c : ℕ+ × ℕ+, ‖w c * H (((c.1 * c.2 : ℕ) : ℝ) * x) /
      ((c.1 * c.2 : ℕ) : ℂ) ^ s‖ ≤ g (c.1 * c.2) := by
    intro c
    have hpos : 0 < (c.1 : ℕ) * c.2 := Nat.mul_pos c.1.pos c.2.pos
    rw [norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos hpos]
    simp only [hg]
    gcongr
    calc ‖w c‖ * ‖H _‖ ≤ 1 * ‖H _‖ := mul_le_mul_of_nonneg_right (hw c) (norm_nonneg _)
      _ = _ := one_mul _
  refine Summable.of_norm_bounded (g := fun c : ℕ+ × ℕ+ ↦ g (c.1 * c.2)) ?_ hbound
  rw [← sigmaAntidiagonalEquivProd.summable_iff]
  refine (summable_sigma_of_nonneg (fun _ ↦ hg0 _)).mpr ⟨fun n ↦ (hasSum_fintype _).summable, ?_⟩
  have hfib : ∀ n : ℕ+, ∑' y : (n : ℕ).divisorsAntidiagonal,
      (fun c : ℕ+ × ℕ+ ↦ g (c.1 * c.2)) (sigmaAntidiagonalEquivProd ⟨n, y⟩) =
      (σ 0 n : ℝ) * g n := by
    intro n
    rw [tsum_fintype]
    have : ∀ y : (n : ℕ).divisorsAntidiagonal,
        (fun c : ℕ+ × ℕ+ ↦ g (c.1 * c.2)) (sigmaAntidiagonalEquivProd ⟨n, y⟩) = g n := by
      intro y
      have := divisorsAntidiagonalFactors_eq y
      exact congrArg g this
    rw [Fintype.sum_congr _ _ this, Finset.sum_const, card_univ, Fintype.card_coe,
      ← Nat.map_div_right_divisors, card_map, sigma_zero_apply, nsmul_eq_mul]
  simp_rw [hfib]
  rw [← Equiv.pnatEquivNat.symm.summable_iff]
  convert hH using 2 with n
  simp only [Function.comp, Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe, hg]
  push_cast
  ring

/-- Diagonal summation of a Möbius-weighted double series collapses to the `n = 1` term. -/
lemma q27_hasSum_diag_moebius (H : ℝ → ℂ) (s : ℂ) (x : ℝ) (sel : ℕ × ℕ → ℕ)
    (hsel : ∀ n : ℕ, ∑ y ∈ n.divisorsAntidiagonal, (μ (sel y) : ℂ) = if n = 1 then 1 else 0)
    {T : ℂ} (h : HasSum (fun c : ℕ+ × ℕ+ ↦ (μ (sel (c.1, c.2)) : ℂ) *
      H (((c.1 * c.2 : ℕ) : ℝ) * x) / ((c.1 * c.2 : ℕ) : ℂ) ^ s) T) : T = H x := by
  have h2 := q27_hasSum_divisorsAntidiagonal h
  have h3 : HasSum (fun n : ℕ+ ↦ if n = 1 then H x else 0) (H x) := hasSum_ite_eq 1 (H x)
  refine h2.unique ?_
  convert h3 using 2 with n
  calc _ = ∑ y ∈ (n : ℕ).divisorsAntidiagonal,
        (μ (sel y) : ℂ) * (H (((n : ℕ) : ℝ) * x) / ((n : ℕ) : ℂ) ^ s) := by
        refine sum_congr rfl fun y hy ↦ ?_
        have hy' := Nat.mem_divisorsAntidiagonal.mp hy
        have h0 : 0 < y.1 ∧ 0 < y.2 :=
          ⟨Nat.pos_of_ne_zero (left_ne_zero_of_mul (hy'.1 ▸ n.ne_zero)),
            Nat.pos_of_ne_zero (right_ne_zero_of_mul (hy'.1 ▸ n.ne_zero))⟩
        rw [dite_eq_left h0]
        simp only [PNat.mk_coe, hy'.1, mul_div_assoc]
    _ = _ := by
        rw [← sum_mul, hsel]
        by_cases h1 : n = 1
        · subst h1; simp
        · have h1' : (n : ℕ) ≠ 1 := fun h ↦ h1 (PNat.coe_eq_one_iff.mp h)
          simp [h1, h1']

/-- `n^s ≠ 0` for `n ≥ 1`. -/
lemma q27_natCast_cpow_ne_zero {n : ℕ} (hn : 0 < n) (s : ℂ) : (n : ℂ) ^ s ≠ 0 := by
  intro h
  have := Complex.norm_natCast_cpow_of_pos hn s
  rw [h, norm_zero] at this
  exact (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _).ne this

/-- DLMF 27.5.7, forward direction (proof). -/
lemma q27_moebius_inversion_series (F G : ℝ → ℂ) (s : ℂ)
    (hF : ∀ x : ℝ, 0 < x →
      Summable fun n : ℕ ↦ (σ 0 (n + 1) : ℝ) * ‖F ((n + 1) * x)‖ / (n + 1 : ℝ) ^ s.re)
    (hG : ∀ x : ℝ, 0 < x →
      HasSum (fun m : ℕ ↦ F ((m + 1) * x) / ((m + 1 : ℕ) : ℂ) ^ s) (G x)) :
    ∀ x : ℝ, 0 < x →
      HasSum (fun m : ℕ ↦ (μ (m + 1) : ℂ) * G ((m + 1) * x) / ((m + 1 : ℕ) : ℂ) ^ s) (F x) := by
  intro x hx
  have hsum := q27_summable_div_cpow F s x (hF x hx) (fun c ↦ (μ (c.1 : ℕ) : ℂ))
    (fun c ↦ by rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one)
  have hT := hsum.hasSum
  have hTF := q27_hasSum_diag_moebius F s x Prod.fst (fun n ↦ by
    rw [Nat.sum_divisorsAntidiagonal (fun a _ ↦ (μ a : ℂ)), q27_sum_divisors_moebius_eq_ite]) hT
  have hrow : ∀ a : ℕ+, HasSum (fun b : ℕ+ ↦ (μ (a : ℕ) : ℂ) *
      F ((((a, b).1 * (a, b).2 : ℕ) : ℝ) * x) / (((a, b).1 * (a, b).2 : ℕ) : ℂ) ^ s)
      ((μ (a : ℕ) : ℂ) * G ((a : ℝ) * x) / ((a : ℕ) : ℂ) ^ s) := by
    intro a
    have ha : (0 : ℝ) < (a : ℝ) * x := mul_pos (by exact_mod_cast a.pos) hx
    have h1 := (q27_hasSum_pnat_iff (g := fun b : ℕ+ ↦
      F (((b : ℕ) : ℝ) * ((a : ℝ) * x)) / ((b : ℕ) : ℂ) ^ s)).mpr (by
        convert hG _ ha using 2 with m
        simp)
    have h2 := h1.mul_left ((μ (a : ℕ) : ℂ) / ((a : ℕ) : ℂ) ^ s)
    have ha0 : ((a : ℕ) : ℂ) ^ s ≠ 0 := q27_natCast_cpow_ne_zero a.pos s
    convert h2 using 1
    · funext b
      have hb0 : ((b : ℕ) : ℂ) ^ s ≠ 0 := q27_natCast_cpow_ne_zero b.pos s
      simp only
      rw [show (((a : ℕ) * (b : ℕ) : ℕ) : ℝ) * x = ((b : ℕ) : ℝ) * ((a : ℝ) * x) by push_cast; ring,
        Nat.cast_mul (α := ℂ), Complex.natCast_mul_natCast_cpow]
      field_simp
    · field_simp
  have h1 := hT.prod_fiberwise hrow
  rw [hTF, q27_hasSum_pnat_iff] at h1
  convert h1 using 2 with m
  simp

/-- DLMF 27.5.7, backward direction (proof). -/
lemma q27_moebius_inversion_series_symm (F G : ℝ → ℂ) (s : ℂ)
    (hG : ∀ x : ℝ, 0 < x →
      Summable fun n : ℕ ↦ (σ 0 (n + 1) : ℝ) * ‖G ((n + 1) * x)‖ / (n + 1 : ℝ) ^ s.re)
    (hF : ∀ x : ℝ, 0 < x →
      HasSum (fun m : ℕ ↦ (μ (m + 1) : ℂ) * G ((m + 1) * x) / ((m + 1 : ℕ) : ℂ) ^ s) (F x)) :
    ∀ x : ℝ, 0 < x →
      HasSum (fun m : ℕ ↦ F ((m + 1) * x) / ((m + 1 : ℕ) : ℂ) ^ s) (G x) := by
  intro x hx
  have hsum := q27_summable_div_cpow G s x (hG x hx) (fun c ↦ (μ (c.2 : ℕ) : ℂ))
    (fun c ↦ by rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one)
  have hT := hsum.hasSum
  have hTG := q27_hasSum_diag_moebius G s x Prod.snd (fun n ↦ by
    rw [Nat.sum_divisorsAntidiagonal' (fun _ b ↦ (μ b : ℂ)), q27_sum_divisors_moebius_eq_ite]) hT
  have hrow : ∀ a : ℕ+, HasSum (fun b : ℕ+ ↦ (μ ((a, b).2 : ℕ) : ℂ) *
      G ((((a, b).1 * (a, b).2 : ℕ) : ℝ) * x) / (((a, b).1 * (a, b).2 : ℕ) : ℂ) ^ s)
      (F ((a : ℝ) * x) / ((a : ℕ) : ℂ) ^ s) := by
    intro a
    have ha : (0 : ℝ) < (a : ℝ) * x := mul_pos (by exact_mod_cast a.pos) hx
    have h1 := (q27_hasSum_pnat_iff (g := fun b : ℕ+ ↦
      (μ (b : ℕ) : ℂ) * G (((b : ℕ) : ℝ) * ((a : ℝ) * x)) / ((b : ℕ) : ℂ) ^ s)).mpr (by
        convert hF _ ha using 2 with m
        simp)
    have h2 := h1.mul_left (1 / ((a : ℕ) : ℂ) ^ s)
    have ha0 : ((a : ℕ) : ℂ) ^ s ≠ 0 := q27_natCast_cpow_ne_zero a.pos s
    convert h2 using 1
    · funext b
      have hb0 : ((b : ℕ) : ℂ) ^ s ≠ 0 := q27_natCast_cpow_ne_zero b.pos s
      simp only
      rw [show (((a : ℕ) * (b : ℕ) : ℕ) : ℝ) * x = ((b : ℕ) : ℝ) * ((a : ℝ) * x) by push_cast; ring,
        Nat.cast_mul (α := ℂ), Complex.natCast_mul_natCast_cpow]
      field_simp
    · field_simp
  have h1 := hT.prod_fiberwise hrow
  rw [hTG, q27_hasSum_pnat_iff] at h1
  convert h1 using 2 with m
  simp

/-- DLMF 27.5.7, forward direction: if `G(x) = ∑_{m≥1} F(mx)/m^s` for all `x > 0`, with
`∑_n d(n) |F(nx)| n^{-ℜs} < ∞` (so that the double series converges absolutely), then
`F(x) = ∑_{m≥1} μ(m) G(mx)/m^s`. -/
@[dlmf 27.5.E7]
theorem moebius_inversion_series (F G : ℝ → ℂ) (s : ℂ)
    (hF : ∀ x : ℝ, 0 < x →
      Summable fun n : ℕ ↦ (σ 0 (n + 1) : ℝ) * ‖F ((n + 1) * x)‖ / (n + 1 : ℝ) ^ s.re)
    (hG : ∀ x : ℝ, 0 < x →
      HasSum (fun m : ℕ ↦ F ((m + 1) * x) / ((m + 1 : ℕ) : ℂ) ^ s) (G x)) :
    ∀ x : ℝ, 0 < x →
      HasSum (fun m : ℕ ↦ (μ (m + 1) : ℂ) * G ((m + 1) * x) / ((m + 1 : ℕ) : ℂ) ^ s) (F x) :=
  q27_moebius_inversion_series F G s hF hG

/-- DLMF 27.5.7, backward direction: if `F(x) = ∑_{m≥1} μ(m) G(mx)/m^s` for all `x > 0`, with
`∑_n d(n) |G(nx)| n^{-ℜs} < ∞`, then `G(x) = ∑_{m≥1} F(mx)/m^s`. -/
@[dlmf 27.5.E7]
theorem moebius_inversion_series_symm (F G : ℝ → ℂ) (s : ℂ)
    (hG : ∀ x : ℝ, 0 < x →
      Summable fun n : ℕ ↦ (σ 0 (n + 1) : ℝ) * ‖G ((n + 1) * x)‖ / (n + 1 : ℝ) ^ s.re)
    (hF : ∀ x : ℝ, 0 < x →
      HasSum (fun m : ℕ ↦ (μ (m + 1) : ℂ) * G ((m + 1) * x) / ((m + 1 : ℕ) : ℂ) ^ s) (F x)) :
    ∀ x : ℝ, 0 < x →
      HasSum (fun m : ℕ ↦ F ((m + 1) * x) / ((m + 1 : ℕ) : ℂ) ^ s) (G x) :=
  q27_moebius_inversion_series_symm F G s hG hF

/-- DLMF 27.5.8, multiplicative Möbius inversion:
`g(n) = ∏_{d∣n} f(d) ⟺ f(n) = ∏_{d∣n} g(n/d)^{μ(d)}`, for nonvanishing `f`, `g`. -/
@[dlmf 27.5.E8]
theorem moebius_inversion_prod (f g : ℕ → ℂ) (hf : ∀ n, 0 < n → f n ≠ 0)
    (hg : ∀ n, 0 < n → g n ≠ 0) :
    (∀ n > 0, g n = ∏ d ∈ n.divisors, f d) ↔
      ∀ n > 0, f n = ∏ d ∈ n.divisors, g (n / d) ^ μ d := by
  have h := prod_eq_iff_prod_pow_moebius_eq_of_nonzero hf hg
  simp_rw [Nat.prod_divisorsAntidiagonal (fun x y ↦ g y ^ μ x)] at h
  constructor
  · intro H n hn
    exact (h.mp (fun n hn ↦ (H n hn).symm) n hn).symm
  · intro H n hn
    exact (h.mpr (fun n hn ↦ (H n hn).symm) n hn).symm

end DLMF.NumberTheory
