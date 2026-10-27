/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.NumberTheory.Functions
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Euler products and Dirichlet series (DLMF §27.4)

The Dirichlet series `F(s) = ∑_{n≥1} f(n) n^{-s}` of DLMF 27.4.4 is Mathlib's `LSeries f s`
(a totalized `tsum`, the term at `n = 0` being `0`); convergence is asserted with
`LSeriesHasSum f s a`, which is `HasSum` of the terms `f(n)/n^s`, `n ≥ 1`. Mathlib's Euler
products (`EulerProduct.eulerProduct_hasProd`,
`EulerProduct.eulerProduct_completely_multiplicative_hasProd`, `riemannZeta_eulerProduct_hasProd`)
give 27.4.1–27.4.3; `LSeries_zeta_mul_Lseries_moebius` and
`LSeries_vonMangoldt_eq_deriv_riemannZeta_div` give 27.4.5 and 27.4.12. All half-plane
conditions are DLMF's.
-/

@[expose] public noncomputable section

open Finset Filter Asymptotics ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.Moebius ArithmeticFunction.omega
  ArithmeticFunction.zeta LSeries.notation

namespace DLMF.NumberTheory

/-- DLMF 27.4.1: the Euler product of an absolutely convergent series with multiplicative
coefficients, `∑_{n≥1} f(n) = ∏_p (1 + ∑_{r≥1} f(p^r))`; the product converges. -/
@[dlmf 27.4.E1]
theorem eulerProduct_multiplicative (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hsum : Summable fun n ↦ ‖f n‖) :
    HasProd (fun p : Nat.Primes ↦ 1 + ∑' r : ℕ, f ((p : ℕ) ^ (r + 1))) (∑' n, f n) := by
  have h := EulerProduct.eulerProduct_hasProd (f := (f : ℕ → ℂ)) hf.1 hf.2 hsum (by simp)
  convert h using 2 with p
  have hs : Summable fun e : ℕ ↦ f ((p : ℕ) ^ e) :=
    hsum.of_norm.comp_injective (Nat.pow_right_injective p.prop.two_le)
  rw [hs.tsum_eq_zero_add]
  simp [hf.1]

/-- DLMF 27.4.2: for completely multiplicative `f` with `∑ |f(n)| < ∞`,
`∑_{n≥1} f(n) = ∏_p (1 - f(p))⁻¹`. -/
@[dlmf 27.4.E2]
theorem eulerProduct_completelyMultiplicative (f : ℕ →*₀ ℂ) (hsum : Summable fun n ↦ ‖f n‖) :
    HasProd (fun p : Nat.Primes ↦ (1 - f p)⁻¹) (∑' n, f n) :=
  EulerProduct.eulerProduct_completely_multiplicative_hasProd hsum

/-- DLMF 27.4.3: `ζ(s) = ∑_{n≥1} n^{-s} = ∏_p (1 - p^{-s})⁻¹`, `ℜs > 1`. -/
@[dlmf 27.4.E3]
theorem riemannZeta_hasSum_hasProd {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum 1 s (riemannZeta s) ∧
      HasProd (fun p : Nat.Primes ↦ (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s) :=
  ⟨LSeriesHasSum_one hs, riemannZeta_eulerProduct_hasProd hs⟩

/-- DLMF 27.4.5: `∑ μ(n) n^{-s} = 1/ζ(s)`, `ℜs > 1`. -/
@[dlmf 27.4.E5]
theorem LSeriesHasSum_moebius {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum ↗μ s (riemannZeta s)⁻¹ := by
  have h := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at h
  rw [← eq_inv_of_mul_eq_one_right h]
  exact (LSeriesSummable_moebius_iff.mpr hs).LSeriesHasSum

/-- The Dirichlet series of `n ↦ n^α` is `ζ(s - α)`, `ℜs > 1 + ℜα`. -/
lemma n27_LSeriesHasSum_powC (α : ℂ) {s : ℂ} (hs : 1 + α.re < s.re) :
    LSeriesHasSum ↗(powC α) s (riemannZeta (s - α)) := by
  have h := LSeriesHasSum_one (s := s - α) (by simp; linarith)
  unfold LSeriesHasSum at h ⊢
  convert h using 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, powC_apply hn,
    Complex.cpow_sub _ _ (by exact_mod_cast hn)]
  simp [div_div_eq_mul_div]

/-! ### Helpers for §27.4 (proof round 2) -/

/-- Dirichlet convolution at a prime power. -/
theorem q27_mul_apply_prime_pow {R : Type*} [Semiring R] (f g : ArithmeticFunction R) {p : ℕ}
    (hp : p.Prime) (e : ℕ) :
    (f * g) (p ^ e) = ∑ i ∈ range (e + 1), f (p ^ i) * g (p ^ (e - i)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b ↦ f a * g b), Nat.divisors_prime_pow hp,
    sum_map]
  refine sum_congr rfl fun i hi ↦ ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div (by simpa [Nat.lt_succ_iff] using hi) hp.pos]

/-- The Dirichlet series of the unit `δ` is `1`. -/
lemma q27_LSeriesHasSum_one {s : ℂ} : LSeriesHasSum ↗(1 : ArithmeticFunction ℂ) s 1 := by
  rw [one_eq_delta]
  unfold LSeriesHasSum
  simp_rw [funext (LSeries.term_delta s)]
  exact hasSum_ite_eq 1 1

/-- Division of Dirichlet series: if `f * g = h`, `L f = a ≠ 0`, `L h = c` and `L g` converges,
then `L g = c / a`. -/
lemma q27_LSeriesHasSum_of_mul_eq {f g h : ArithmeticFunction ℂ} {s a c : ℂ}
    (hfg : f * g = h) (hf : LSeriesHasSum ↗f s a) (ha : a ≠ 0) (hg : LSeriesSummable ↗g s)
    (hh : LSeriesHasSum ↗h s c) : LSeriesHasSum ↗g s (c / a) := by
  have h1 := LSeriesHasSum_mul hf hg.LSeriesHasSum
  rw [hfg] at h1
  have h2 : a * LSeries ↗g s = c := h1.unique hh
  rw [← h2, mul_div_cancel_left₀ _ ha]
  exact hg.LSeriesHasSum

/-- The function `n ↦ g(√n)` on squares, `0` elsewhere. -/
def q27_sqLift (g : ℕ → ℂ) : ℕ → ℂ := fun n ↦ if IsSquare n then g (Nat.sqrt n) else 0

/-- `∑ g(m) (m²)^{-s} = ∑ g(m) m^{-2s}`. -/
lemma q27_LSeriesHasSum_sqLift {g : ℕ → ℂ} {s a : ℂ} (h : LSeriesHasSum g (2 * s) a) :
    LSeriesHasSum (q27_sqLift g) s a := by
  unfold LSeriesHasSum at h ⊢
  have hinj : Function.Injective (fun m : ℕ ↦ m ^ 2) := Nat.pow_left_injective two_ne_zero
  rw [← hinj.hasSum_iff]
  · convert h using 1
    funext m
    simp only [Function.comp]
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rw [LSeries.term_of_ne_zero (pow_ne_zero 2 hm), LSeries.term_of_ne_zero hm, q27_sqLift,
      ite_eq_left ⟨m, sq m⟩, Nat.sqrt_eq' m]
    congr 1
    rw [Nat.cast_pow, sq, Complex.natCast_mul_natCast_cpow,
      show (2 : ℂ) * s = ((2 : ℕ) : ℂ) * s by norm_num, Complex.cpow_nat_mul, sq]
  · intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    rw [LSeries.term_of_ne_zero hn0, q27_sqLift, ite_eq_right, zero_div]
    rintro ⟨r, rfl⟩
    exact hn ⟨r, sq r⟩


/-- `φ` as a complex arithmetic function. -/
def q27_totientC : ArithmeticFunction ℂ := ⟨fun n ↦ (n.totient : ℂ), by simp⟩

/-- `∑_{d∣n} φ(d) = n` as a Dirichlet convolution. -/
lemma q27_zeta_mul_totientC : (ζ : ArithmeticFunction ℂ) * q27_totientC = powC 1 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [coe_zeta_mul_apply, powC_apply hn, Complex.cpow_one]
  change ∑ i ∈ n.divisors, ((i.totient : ℕ) : ℂ) = _
  exact_mod_cast Nat.sum_totient n

/-- DLMF 27.4.6 (proof). -/
lemma q27_LSeriesHasSum_totient {s : ℂ} (hs : 2 < s.re) :
    LSeriesHasSum (fun n ↦ (n.totient : ℂ)) s (riemannZeta (s - 1) / riemannZeta s) := by
  have h1 : 1 < s.re := by linarith
  have hsum : LSeriesSummable ↗q27_totientC s := by
    refine LSeriesSummable_of_le_const_mul_rpow (x := 2) hs ⟨1, fun n hn ↦ ?_⟩
    change ‖((n.totient : ℕ) : ℂ)‖ ≤ 1 * (n : ℝ) ^ ((2 : ℝ) - 1)
    rw [Complex.norm_natCast, one_mul, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    exact_mod_cast Nat.totient_le n
  have hpow : LSeriesHasSum ↗(powC 1) s (riemannZeta (s - 1)) :=
    n27_LSeriesHasSum_powC 1 (s := s) (by rw [Complex.one_re]; linarith)
  have hfun : (fun n ↦ (n.totient : ℂ)) = ↗q27_totientC := rfl
  rw [hfun]
  exact q27_LSeriesHasSum_of_mul_eq q27_zeta_mul_totientC (LSeriesHasSum_zeta h1)
    (riemannZeta_ne_zero_of_one_lt_re h1) hsum hpow


/-- DLMF 27.6.2 (core): `∑_{d²∣n} μ(d) = |μ(n)|`. -/
theorem q27_sum_sq_dvd_moebius {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors with d ^ 2 ∣ n, μ d = |μ n| := by
  obtain ⟨b, a, hab, hsq⟩ := exists_sq_mul_squarefree n
  have hb0 : b ≠ 0 := by rintro rfl; simp at hab; exact hn hab.symm
  have key : ∀ d, d ^ 2 ∣ n ↔ d ∣ b := by
    intro d
    constructor
    · intro hd
      have hg0 : 0 < Nat.gcd d b := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hb0)
      obtain ⟨d', b', hcop, hd', hb'⟩ := Nat.exists_coprime d b
      set g := Nat.gcd d b with hg
      rw [← hab, hd', hb', mul_pow, mul_pow] at hd
      have h1 : d' ^ 2 ∣ b' ^ 2 * a := by
        refine Nat.dvd_of_mul_dvd_mul_right (pow_pos hg0 2) ?_
        rw [show b' ^ 2 * a * g ^ 2 = b' ^ 2 * g ^ 2 * a by ring]
        exact hd
      have h2 : d' ^ 2 ∣ a := (Nat.Coprime.pow 2 2 hcop).dvd_of_dvd_mul_left h1
      have h3 : d' = 1 := Nat.isUnit_iff.mp (hsq d' (by rwa [← sq]))
      rw [hd', hb', h3, one_mul]
      exact Dvd.intro_left _ rfl
    · intro hd
      rw [← hab]
      exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hd 2) a
  have hfilter : n.divisors.filter (fun d ↦ d ^ 2 ∣ n) = b.divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, key]
    constructor
    · rintro ⟨-, h⟩; exact ⟨h, hb0⟩
    · rintro ⟨h, -⟩
      refine ⟨⟨?_, hn⟩, h⟩
      rw [← hab]
      exact (h.trans (Dvd.intro_left _ (sq b).symm)).mul_right a
  rw [hfilter]
  have hsum : ∑ d ∈ b.divisors, μ d = if b = 1 then 1 else 0 := by
    have := congrArg (fun f : ArithmeticFunction ℤ ↦ f b) coe_zeta_mul_moebius
    simp only [coe_zeta_mul_apply, one_apply] at this
    exact this
  rw [hsum]
  split_ifs with h1
  · subst h1
    rw [one_pow, one_mul] at hab
    rw [← hab, abs_moebius_eq_one_of_squarefree hsq]
  · have hns : ¬ Squarefree n := by
      intro hn'
      apply h1
      exact Nat.isUnit_iff.mp (hn' b (by rw [← hab, ← sq]; exact Dvd.intro _ rfl))
    rw [moebius_eq_zero_of_not_squarefree hns, abs_zero]


/-- `|μ|` as an integer-valued arithmetic function. -/
def q27_absMoebius : ArithmeticFunction ℤ := ⟨fun n ↦ |μ n|, by simp⟩

/-- Value of `q27_absMoebius`. -/
lemma q27_absMoebius_apply (n : ℕ) : q27_absMoebius n = |μ n| := rfl

/-- `|μ|` is multiplicative. -/
lemma q27_isMultiplicative_absMoebius : q27_absMoebius.IsMultiplicative := by
  refine ⟨by simp [q27_absMoebius_apply], fun {m n} hmn ↦ ?_⟩
  simp only [q27_absMoebius_apply]
  rw [isMultiplicative_moebius.map_mul_of_coprime hmn, abs_mul]

/-- `|μ(p^j)| = 1` for `j ≤ 1` and `0` otherwise. -/
lemma q27_absMoebius_prime_pow {p : ℕ} (hp : p.Prime) (j : ℕ) :
    q27_absMoebius (p ^ j) = if j ≤ 1 then 1 else 0 := by
  rw [q27_absMoebius_apply]
  rcases j with _ | j
  · simp
  rw [moebius_apply_prime_pow hp (Nat.succ_ne_zero j)]
  rcases j with _ | j <;> simp

/-- `λ * |μ| = δ`. -/
lemma q27_liouville_mul_absMoebius :
    (liouville : ArithmeticFunction ℤ) * q27_absMoebius = 1 := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_liouville.mul q27_isMultiplicative_absMoebius) _
    isMultiplicative_one).mpr fun p i hp ↦ ?_
  rcases i with _ | e
  · simp [q27_absMoebius_apply, liouville_apply_one]
  rw [q27_mul_apply_prime_pow _ _ hp, one_apply_ne (Nat.one_lt_pow (Nat.succ_ne_zero e)
    hp.one_lt).ne', sum_range_succ, sum_range_succ, sum_eq_zero]
  · simp only [q27_absMoebius_prime_pow hp, liouville_apply (pow_ne_zero _ hp.ne_zero),
      cardFactors_apply_prime_pow hp]
    simp [pow_succ]
  · intro i hi
    rw [mem_range] at hi
    rw [q27_absMoebius_prime_pow hp, ite_eq_right (by omega), mul_zero]

/-- `∑_{d∣p^{e+1}} |μ(d)| = 2`. -/
lemma q27_zeta_mul_absMoebius_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ((ζ : ArithmeticFunction ℤ) * q27_absMoebius) (p ^ (e + 1)) = 2 := by
  rw [coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp, sum_range_succ', sum_range_succ',
    sum_eq_zero]
  · simp [q27_absMoebius_apply, moebius_apply_prime hp]
  · intro i _
    rw [q27_absMoebius_prime_pow hp, ite_eq_right (by omega)]

/-- `2^{ω(n)}` as an integer-valued arithmetic function. -/
def q27_twoPowOmega : ArithmeticFunction ℤ := ⟨fun n ↦ if n = 0 then 0 else 2 ^ ω n, by simp⟩

/-- `2^{ω(n)} = ∑_{d∣n} |μ(d)|`. -/
lemma q27_twoPowOmega_eq : q27_twoPowOmega = (ζ : ArithmeticFunction ℤ) * q27_absMoebius := by
  have hmul : q27_twoPowOmega.IsMultiplicative := by
    refine ⟨by simp [q27_twoPowOmega], fun {m n} hmn ↦ ?_⟩
    change (if m * n = 0 then 0 else 2 ^ ω (m * n) : ℤ) =
      (if m = 0 then 0 else 2 ^ ω m) * (if n = 0 then 0 else 2 ^ ω n)
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [ite_eq_right (mul_ne_zero hm hn), ite_eq_right hm, ite_eq_right hn,
      cardDistinctFactors_mul hmn, pow_add]
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ hmul _
    (isMultiplicative_zeta.natCast.mul q27_isMultiplicative_absMoebius)).mpr fun p i hp ↦ ?_
  rcases i with _ | e
  · simp [q27_twoPowOmega, q27_absMoebius_apply]
  rw [q27_zeta_mul_absMoebius_prime_pow hp]
  change (if p ^ (e + 1) = 0 then 0 else 2 ^ ω (p ^ (e + 1)) : ℤ) = 2
  rw [ite_eq_right (pow_ne_zero _ hp.ne_zero), cardDistinctFactors_apply_prime_pow hp (by omega),
    pow_one]

/-- `μ(√n)` on squares, `0` elsewhere, as a complex arithmetic function. -/
def q27_moebiusSq : ArithmeticFunction ℂ :=
  ⟨q27_sqLift fun m ↦ (μ m : ℂ), by simp [q27_sqLift]⟩

/-- `∑_{d²∣n} μ(d) = |μ(n)|` as a Dirichlet convolution. -/
lemma q27_zeta_mul_moebiusSq :
    (ζ : ArithmeticFunction ℂ) * q27_moebiusSq = (q27_absMoebius : ArithmeticFunction ℂ) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [coe_zeta_mul_apply, intCoe_apply, q27_absMoebius_apply, ← q27_sum_sq_dvd_moebius hn]
  change ∑ d ∈ n.divisors, q27_sqLift (fun m ↦ (μ m : ℂ)) d = _
  simp only [q27_sqLift]
  rw [← sum_filter, Int.cast_sum]
  refine sum_nbij' Nat.sqrt (fun e ↦ e ^ 2) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdn, -⟩, ⟨r, rfl⟩⟩ := hd
    rw [mem_filter, Nat.mem_divisors, Nat.sqrt_eq]
    exact ⟨⟨(Dvd.intro r rfl).trans hdn, hn⟩, by rw [sq]; exact hdn⟩
  · intro e he
    rw [mem_filter, Nat.mem_divisors] at he
    rw [mem_filter, Nat.mem_divisors]
    exact ⟨⟨he.2, hn⟩, ⟨e, sq e⟩⟩
  · intro d hd
    rw [mem_filter] at hd
    obtain ⟨-, ⟨r, rfl⟩⟩ := hd
    rw [Nat.sqrt_eq, sq]
  · intro e _
    exact Nat.sqrt_eq' e
  · intro d _
    rfl

/-- DLMF 27.4.8 (proof). -/
lemma q27_LSeriesHasSum_abs_moebius {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ ((|μ n| : ℤ) : ℂ)) s (riemannZeta s / riemannZeta (2 * s)) := by
  have h2 : 1 < (2 * s).re := by
    rw [show (2 : ℂ) * s = ((2 : ℝ) : ℂ) * s by norm_num, Complex.re_ofReal_mul]; linarith
  have hsq : LSeriesHasSum ↗q27_moebiusSq s (riemannZeta (2 * s))⁻¹ := by
    have e1 : ↗q27_moebiusSq = q27_sqLift (fun m ↦ ((μ m : ℤ) : ℂ)) := rfl
    rw [e1]
    exact q27_LSeriesHasSum_sqLift (LSeriesHasSum_moebius h2)
  have h := LSeriesHasSum_mul (f := (ζ : ArithmeticFunction ℂ)) (LSeriesHasSum_zeta hs) hsq
  rw [q27_zeta_mul_moebiusSq, ← div_eq_mul_inv] at h
  have hfun : (fun n ↦ ((|μ n| : ℤ) : ℂ)) = ↗(q27_absMoebius : ArithmeticFunction ℂ) := by
    funext n; rw [intCoe_apply, q27_absMoebius_apply]
  rw [hfun]
  exact h

/-- DLMF 27.4.7 (proof). -/
lemma q27_LSeriesHasSum_liouville {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (liouville n : ℂ)) s (riemannZeta (2 * s) / riemannZeta s) := by
  have h2 : 1 < (2 * s).re := by
    rw [show (2 : ℂ) * s = ((2 : ℝ) : ℂ) * s by norm_num, Complex.re_ofReal_mul]; linarith
  have habs : LSeriesHasSum ↗(q27_absMoebius : ArithmeticFunction ℂ) s
      (riemannZeta s / riemannZeta (2 * s)) := by
    have hfun : ↗(q27_absMoebius : ArithmeticFunction ℂ) = (fun n ↦ ((|μ n| : ℤ) : ℂ)) := by
      funext n; rw [intCoe_apply, q27_absMoebius_apply]
    rw [hfun]; exact q27_LSeriesHasSum_abs_moebius hs
  have hne : riemannZeta s / riemannZeta (2 * s) ≠ 0 :=
    div_ne_zero (riemannZeta_ne_zero_of_one_lt_re hs) (riemannZeta_ne_zero_of_one_lt_re h2)
  have hsum : LSeriesSummable ↗(liouville : ArithmeticFunction ℂ) s := by
    refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n hn ↦ ?_) hs
    rw [intCoe_apply, liouville_apply hn]
    simp
  have hmul : (q27_absMoebius : ArithmeticFunction ℂ) * (liouville : ArithmeticFunction ℂ) = 1 := by
    rw [← intCoe_mul, mul_comm, q27_liouville_mul_absMoebius, intCoe_one]
  have h := q27_LSeriesHasSum_of_mul_eq hmul habs hne hsum q27_LSeriesHasSum_one
  rw [one_div, inv_div] at h
  have hfun : (fun n ↦ (liouville n : ℂ)) = ↗(liouville : ArithmeticFunction ℂ) := by
    funext n; rw [intCoe_apply]
  rw [hfun]
  exact h

/-- DLMF 27.4.9 (proof). -/
lemma q27_LSeriesHasSum_two_pow_cardDistinctFactors {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ if n = 0 then 0 else (2 : ℂ) ^ ω n) s
      (riemannZeta s ^ 2 / riemannZeta (2 * s)) := by
  have habs : LSeriesHasSum ↗(q27_absMoebius : ArithmeticFunction ℂ) s
      (riemannZeta s / riemannZeta (2 * s)) := by
    have hfun : ↗(q27_absMoebius : ArithmeticFunction ℂ) = (fun n ↦ ((|μ n| : ℤ) : ℂ)) := by
      funext n; rw [intCoe_apply, q27_absMoebius_apply]
    rw [hfun]; exact q27_LSeriesHasSum_abs_moebius hs
  have h := LSeriesHasSum_mul (f := (ζ : ArithmeticFunction ℂ)) (LSeriesHasSum_zeta hs) habs
  have hfun : (fun n ↦ if n = 0 then 0 else (2 : ℂ) ^ ω n) =
      ↗((ζ : ArithmeticFunction ℂ) * (q27_absMoebius : ArithmeticFunction ℂ)) := by
    rw [← coe_coe, ← intCoe_mul, ← q27_twoPowOmega_eq]
    funext n
    rw [intCoe_apply]
    change _ = ((if n = 0 then 0 else 2 ^ ω n : ℤ) : ℂ)
    split_ifs <;> simp
  rw [hfun, sq, mul_div_assoc]
  exact h

/-- Casting commutes with Dirichlet powers. -/
lemma q27_natCoe_pow (f : ArithmeticFunction ℕ) (k : ℕ) :
    ((f ^ k : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) = (f : ArithmeticFunction ℂ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, natCoe_mul, ih, pow_succ]

/-- DLMF 27.4.10 (proof). -/
lemma q27_LSeriesHasSum_divisorCountK (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (divisorCountK k n : ℂ)) s (riemannZeta s ^ k) := by
  have hfun : (fun n ↦ (divisorCountK k n : ℂ)) = ↗((ζ : ArithmeticFunction ℂ) ^ k) := by
    funext n
    rw [q27_divisorCountK_eq_zeta_pow, ← natCoe_apply, q27_natCoe_pow]
  rw [hfun]
  clear hfun
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact q27_LSeriesHasSum_one
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact LSeriesHasSum_mul ih (LSeriesHasSum_zeta hs)

/-- DLMF 27.4.6: `∑ φ(n) n^{-s} = ζ(s - 1)/ζ(s)`, `ℜs > 2`. -/
@[dlmf 27.4.E6]
theorem LSeriesHasSum_totient {s : ℂ} (hs : 2 < s.re) :
    LSeriesHasSum (fun n ↦ (n.totient : ℂ)) s (riemannZeta (s - 1) / riemannZeta s) :=
  q27_LSeriesHasSum_totient hs

/-- DLMF 27.4.7: `∑ λ(n) n^{-s} = ζ(2s)/ζ(s)`, `ℜs > 1`. -/
@[dlmf 27.4.E7]
theorem LSeriesHasSum_liouville {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (liouville n : ℂ)) s (riemannZeta (2 * s) / riemannZeta s) :=
  q27_LSeriesHasSum_liouville hs

/-- DLMF 27.4.8: `∑ |μ(n)| n^{-s} = ζ(s)/ζ(2s)`, `ℜs > 1`. -/
@[dlmf 27.4.E8]
theorem LSeriesHasSum_abs_moebius {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ ((|μ n| : ℤ) : ℂ)) s (riemannZeta s / riemannZeta (2 * s)) :=
  q27_LSeriesHasSum_abs_moebius hs

/-- DLMF 27.4.9: `∑ 2^{ν(n)} n^{-s} = ζ(s)²/ζ(2s)`, `ℜs > 1`. -/
@[dlmf 27.4.E9]
theorem LSeriesHasSum_two_pow_cardDistinctFactors {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ if n = 0 then 0 else (2 : ℂ) ^ ω n) s
      (riemannZeta s ^ 2 / riemannZeta (2 * s)) :=
  q27_LSeriesHasSum_two_pow_cardDistinctFactors hs

/-- DLMF 27.4.10: `∑ d_k(n) n^{-s} = ζ(s)^k`, `ℜs > 1`. -/
@[dlmf 27.4.E10]
theorem LSeriesHasSum_divisorCountK (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (divisorCountK k n : ℂ)) s (riemannZeta s ^ k) :=
  q27_LSeriesHasSum_divisorCountK k hs

/-- DLMF 27.4.11: `∑ σ_α(n) n^{-s} = ζ(s) ζ(s - α)`, `ℜs > max(1, 1 + ℜα)`. -/
@[dlmf 27.4.E11]
theorem LSeriesHasSum_sigmaC (α : ℂ) {s : ℂ} (hs : max 1 (1 + α.re) < s.re) :
    LSeriesHasSum ↗(sigmaC α) s (riemannZeta s * riemannZeta (s - α)) := by
  have h1 : 1 < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have h2 : 1 + α.re < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  exact LSeriesHasSum_mul (LSeriesHasSum_zeta h1) (n27_LSeriesHasSum_powC α h2)

/-- DLMF 27.4.12: `∑ Λ(n) n^{-s} = -ζ'(s)/ζ(s)`, `ℜs > 1`. -/
@[dlmf 27.4.E12]
theorem LSeriesHasSum_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (vonMangoldt n : ℂ)) s
      (-deriv riemannZeta s / riemannZeta s) := by
  rw [← LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  exact (LSeriesSummable_vonMangoldt hs).LSeriesHasSum

/-- DLMF 27.4.13: `∑_{n≥2} (ln n) n^{-s} = -ζ'(s)`, `ℜs > 1`. -/
@[dlmf 27.4.E13]
theorem LSeriesHasSum_log {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (Real.log n : ℂ)) s (-deriv riemannZeta s) := by
  have habs : LSeries.abscissaOfAbsConv 1 < s.re := by
    rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast hs
  have hderiv : deriv riemannZeta s = deriv (LSeries 1) s := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact (LSeries_one_eq_riemannZeta hz).symm
  rw [hderiv, LSeries_deriv habs, neg_neg]
  have hsum := LSeriesSummable_logMul_of_lt_re habs
  convert hsum.LSeriesHasSum using 2 with n
  simp [LSeries.logMul, Complex.ofReal_log (Nat.cast_nonneg n)]

end DLMF.NumberTheory
