/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Modified
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Neumann series of Bessel functions

A *Neumann series* is an expansion `∑ₖ aₖ J_{ν+nₖ}(z)` (or with `I`) in Bessel functions whose
orders increase by integers. Writing `J_{ν+n}(z) = (z/2)^ν (z/2)^n ₀F̃₁(;ν+n+1;-(z/2)²)`, such a
series is a double series in `(k, m)`. This file proves:

* `exists_norm_recip_Gamma_add_nat_le`: `|1/Γ(c+n)| ≤ C 2ⁿ/n!`, uniformly in `n`, for every `c`;
  hence `exists_norm_regularized0F1Coeff_le`, a bound on the `₀F̃₁` coefficients uniform in
  the integer shift of the order;
* `hasSum_neumann`: under `∑ₖ |aₖ| |w|^{eₖ} 2^{nₖ}/nₖ! < ∞` the double series is absolutely
  summable and the Neumann series is its sum (rearrangement theorem);
* `hasSum_neumannCoeff`: for `eₖ = 2k` the same sum is the power series `∑ⱼ bⱼ w^{2j}` whose
  coefficients `bⱼ = neumannCoeff` are finite antidiagonal convolutions;
* `hasSum_besselJ_neumann`, `hasSum_besselI_neumann`: the corresponding statements for
  `∑ₖ aₖ (z/2)^{pₖ} J_{ν+nₖ}(z)` and `I`, with `pₖ + nₖ = 2k`, and `differentiable_neumann`;
* coefficient identities: the partial-fraction sum `sum_antidiagonal_neg_one_pow_div_add`,
  Neumann's expansion of a power `(z/2)^λ = ∑ₖ (λ+2k)Γ(λ+k)/k! J_{λ+2k}(z)`
  (`hasSum_besselJ_neumann_power`), and the Lommel-type coefficients
  (`neumannCoeff_lommel`, `hasSum_besselJ_neumann_lommel`), obtained from the Bessel operator at
  coefficient level;
* growth bounds for the coefficients (`exists_norm_powerNeumannCoeff_le`,
  `summable_neumann_of_norm_le`) and small Pochhammer/binomial helpers;
* Neumann series with `eₖ = k` (orders of both parities): `hasSum_neumannLinCoeff`,
  `hasSum_besselJ_neumann_linear`, `hasSum_besselI_neumann_linear`, via the fibre-summation
  lemma `hasSum_sum_range_fiber`;
* two terminating hypergeometric identities in polynomial form, proved by WZ certificates and
  valid for all parameters: the very-well-poised `₄F₃(-1)` sum `sum_range_vwpTerm` and
  `sum_range_kumTerm`, which gives the power series of `₀F̃₁(;c;w²) e^{2w}`
  (`hasSum_regularized0F1_mul_exp`, the regularized DLMF 13.6.9).
-/

@[expose] public noncomputable section

open Complex Finset
open scoped Real Nat Topology
open DLMF.Confluent

namespace DLMF.Bessel

/-- Lower bound `i! |Γ(s)| ≤ |Γ(s+i)|` for `Re s ≥ 1`. -/
theorem norm_Gamma_add_nat_ge {s : ℂ} (hs : 1 ≤ s.re) (i : ℕ) :
    (i ! : ℝ) * ‖Gamma s‖ ≤ ‖Gamma (s + i)‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hne : s + i ≠ 0 := by
      intro h; have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hne, norm_mul, Nat.factorial_succ,
      Nat.cast_mul]
    have h1 : ((i:ℝ) + 1) ≤ ‖s + i‖ := by
      have := Complex.re_le_norm (s + i); simp at this; linarith
    calc ((i + 1 : ℕ) : ℝ) * i ! * ‖Gamma s‖ = ((i:ℝ) + 1) * (i ! * ‖Gamma s‖) := by
          push_cast; ring
      _ ≤ ‖s + i‖ * ‖Gamma (s + i)‖ := by
          gcongr

/-- Uniform reciprocal-Gamma bound `|1/Γ(c+n)| ≤ C 2ⁿ/n!` for every `c` (zeros of `1/Γ`
included). -/
theorem exists_norm_recip_Gamma_add_nat_le (c : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖(Gamma (c + n))⁻¹‖ ≤ C * (2 ^ n / n !) := by
  set N : ℕ := ⌈1 - c.re⌉₊
  set s : ℂ := c + N
  have hs : 1 ≤ s.re := by
    have := Nat.le_ceil (1 - c.re); simp [s]; linarith
  have hGs : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hGs' : 0 < ‖Gamma s‖ := norm_pos_iff.mpr hGs
  set M : ℝ := ‖Gamma s‖⁻¹ + ∑ i ∈ range N, ‖(Gamma (c + i))⁻¹‖
  have hM0 : 0 ≤ M := by positivity
  refine ⟨N ! * M, by positivity, fun n => ?_⟩
  rcases lt_or_ge n N with hn | hn
  · have h1 : ‖(Gamma (c + n))⁻¹‖ ≤ M := by
      have : ‖(Gamma (c + n))⁻¹‖ ≤ ∑ i ∈ range N, ‖(Gamma (c + i))⁻¹‖ :=
        Finset.single_le_sum (f := fun i : ℕ => ‖(Gamma (c + i))⁻¹‖)
          (fun i _ => norm_nonneg _) (Finset.mem_range.mpr hn)
      linarith [inv_nonneg.mpr hGs'.le]
    have h2 : (1:ℝ) ≤ N ! * (2 ^ n / n !) := by
      have hf : (n ! : ℝ) ≤ N ! := by exact_mod_cast Nat.factorial_le hn.le
      have hp : (1:ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      nlinarith [Nat.factorial_pos n]
    calc ‖(Gamma (c + n))⁻¹‖ ≤ M * 1 := by simpa using h1
      _ ≤ M * (N ! * (2 ^ n / n !)) := by gcongr
      _ = N ! * M * (2 ^ n / n !) := by ring
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hci : c + ((N + i : ℕ) : ℂ) = s + i := by simp [s]; ring
    rw [hci, norm_inv]
    have hb := norm_Gamma_add_nat_ge hs i
    have hfi : (0:ℝ) < i ! := by exact_mod_cast Nat.factorial_pos i
    have hch : ((N + i)! : ℝ) = (N + i).choose N * N ! * i ! := by
      have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right N i)
      rw [Nat.add_sub_cancel_left] at this
      exact_mod_cast this.symm
    have hc2 : ((N + i).choose N : ℝ) ≤ 2 ^ (N + i) := by
      exact_mod_cast Nat.choose_le_two_pow (N + i) N
    have hpos : 0 < ‖Gamma (s + i)‖ := lt_of_lt_of_le (by positivity) hb
    rw [inv_le_iff_one_le_mul₀ hpos]
    have hMs : ‖Gamma s‖⁻¹ ≤ M := by
      have : 0 ≤ ∑ i ∈ range N, ‖(Gamma (c + i))⁻¹‖ := sum_nonneg fun i _ => norm_nonneg _
      simp only [M]; linarith
    rw [hch]
    have key : (1:ℝ) ≤ ‖Gamma s‖⁻¹ * (N ! * (2 ^ (N + i) / ((N + i).choose N * N ! * i !)))
        * (i ! * ‖Gamma s‖) := by
      have hcpos : (0:ℝ) < (N + i).choose N := by
        exact_mod_cast Nat.choose_pos (Nat.le_add_right N i)
      field_simp
      exact hc2
    calc (1:ℝ) ≤ ‖Gamma s‖⁻¹ * (N ! * (2 ^ (N + i) / ((N + i).choose N * N ! * i !)))
        * (i ! * ‖Gamma s‖) := key
      _ ≤ M * (N ! * (2 ^ (N + i) / ((N + i).choose N * N ! * i !))) * ‖Gamma (s + i)‖ := by
        gcongr
      _ = _ := by ring


/-- The `₀F̃₁` coefficients `1/(m! Γ(ν+n+1+m))` are bounded by `C (2ⁿ/n!) (2ᵐ/m!)`, uniformly
in the integer shift `n` of the order. -/
theorem exists_norm_regularized0F1Coeff_le (ν : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n m : ℕ,
      ‖regularizedHGFunCoeff (∅ : Multiset ℂ) {ν + n + 1} m‖ ≤
        C * (2 ^ n / n !) * (2 ^ m / m !) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_recip_Gamma_add_nat_le (ν + 1)
  refine ⟨C, hC0, fun n m => ?_⟩
  rw [regularizedHGFunCoeff_empty,
    show ν + n + 1 + m = (ν + 1) + ((n + m : ℕ) : ℂ) by push_cast; ring,
    one_div, mul_inv, norm_mul, norm_inv, Complex.norm_natCast]
  have h := hC (n + m)
  have hf : (n ! : ℝ) * m ! ≤ (n + m)! := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add n m)
  have hm1 : ((m ! : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m))
  have hnm : C * (2 ^ (n + m) / (n + m)!) ≤ C * (2 ^ n / n !) * (2 ^ m / m !) := by
    rw [mul_assoc, div_mul_div_comm, ← pow_add]
    gcongr
  calc ((m ! : ℝ))⁻¹ * ‖(Gamma ((ν + 1) + ((n + m : ℕ) : ℂ)))⁻¹‖
      ≤ 1 * (C * (2 ^ (n + m) / (n + m)!)) := by gcongr
    _ ≤ _ := by rw [one_mul]; exact hnm

/-- The term `(k, m)` of the double series of a Neumann-type series
`∑ₖ aₖ w^{eₖ} ₀F̃₁(;ν+nₖ+1;σw²)`. -/
def neumannTerm (ν σ w : ℂ) (a : ℕ → ℂ) (n e : ℕ → ℕ) (p : ℕ × ℕ) : ℂ :=
  a p.1 * w ^ e p.1 * (regularizedHGFunCoeff (∅ : Multiset ℂ) {ν + n p.1 + 1} p.2 * (σ * w ^ 2) ^ p.2)

/-- Absolute summability of the Neumann double series under
`∑ₖ |aₖ| |w|^{eₖ} 2^{nₖ}/nₖ! < ∞`. -/
theorem summable_norm_neumannTerm (ν σ w : ℂ) (a : ℕ → ℂ) (n e : ℕ → ℕ)
    (ha : Summable fun k => ‖a k‖ * ‖w‖ ^ e k * (2 ^ n k / (n k)!)) :
    Summable fun p => ‖neumannTerm ν σ w a n e p‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_regularized0F1Coeff_le ν
  have hg : Summable fun m : ℕ => (2 * (‖σ‖ * ‖w‖ ^ 2)) ^ m / m ! :=
    Real.summable_pow_div_factorial _
  have hprod := (ha.mul_of_nonneg hg (fun k => by positivity) (fun m => by positivity)).mul_left C
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hprod
  simp only [neumannTerm, norm_mul, norm_pow]
  have h := hC (n p.1) p.2
  calc ‖a p.1‖ * ‖w‖ ^ e p.1 * (‖regularizedHGFunCoeff (∅ : Multiset ℂ) {ν + ↑(n p.1) + 1} p.2‖ *
        (‖σ‖ * ‖w‖ ^ 2) ^ p.2)
      ≤ ‖a p.1‖ * ‖w‖ ^ e p.1 * (C * (2 ^ n p.1 / (n p.1)!) * (2 ^ p.2 / p.2 !) *
        (‖σ‖ * ‖w‖ ^ 2) ^ p.2) := by gcongr
    _ = C * (‖a p.1‖ * ‖w‖ ^ e p.1 * (2 ^ n p.1 / (n p.1)!) *
        ((2 * (‖σ‖ * ‖w‖ ^ 2)) ^ p.2 / p.2 !)) := by rw [mul_pow]; ring

/-- Inner sums of the Neumann double series. -/
theorem hasSum_neumannTerm_inner (ν σ w : ℂ) (a : ℕ → ℂ) (n e : ℕ → ℕ) (k : ℕ) :
    HasSum (fun m => neumannTerm ν σ w a n e (k, m))
      (a k * w ^ e k * regularizedHGFun (∅ : Multiset ℂ) {ν + n k + 1} (σ * w ^ 2)) :=
  ((hasFPowerSeriesOnBall_regularized0F1 _).hasSum_mul_pow (by simp)).mul_left _

/-- **Neumann rearrangement**: under absolute convergence, the Neumann series equals the
sum of its double series. -/
theorem hasSum_neumann (ν σ w : ℂ) (a : ℕ → ℂ) (n e : ℕ → ℕ)
    (ha : Summable fun k => ‖a k‖ * ‖w‖ ^ e k * (2 ^ n k / (n k)!)) :
    HasSum (fun k => a k * w ^ e k * regularizedHGFun (∅ : Multiset ℂ) {ν + n k + 1} (σ * w ^ 2))
      (∑' p, neumannTerm ν σ w a n e p) :=
  (summable_norm_neumannTerm ν σ w a n e ha).of_norm.hasSum.prod_fiberwise
    (hasSum_neumannTerm_inner ν σ w a n e)

/-- Coefficient of `w^{2j}` in a Neumann series with `eₖ = 2k`. -/
def neumannCoeff (ν σ : ℂ) (a : ℕ → ℂ) (n : ℕ → ℕ) (j : ℕ) : ℂ :=
  ∑ p ∈ antidiagonal j, a p.1 * σ ^ p.2 * regularizedHGFunCoeff (∅ : Multiset ℂ) {ν + n p.1 + 1} p.2

/-- **Neumann series as a power series** (`eₖ = 2k`): the coefficients are finite convolutions. -/
theorem hasSum_neumannCoeff (ν σ w : ℂ) (a : ℕ → ℂ) (n : ℕ → ℕ)
    (ha : Summable fun k => ‖a k‖ * ‖w‖ ^ (2 * k) * (2 ^ n k / (n k)!)) :
    HasSum (fun j => neumannCoeff ν σ a n j * w ^ (2 * j))
      (∑' p, neumannTerm ν σ w a n (fun k => 2 * k) p) := by
  have hs := (summable_norm_neumannTerm ν σ w a n (fun k => 2 * k) ha).of_norm.hasSum
  rw [← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd).hasSum_iff] at hs
  refine hs.sigma fun j => ?_
  convert hasSum_fintype _ using 1
  simp only [Function.comp_apply, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
  rw [Finset.sum_coe_sort (antidiagonal j)
    (fun p => neumannTerm ν σ w a n (fun k => 2 * k) p), neumannCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [mem_antidiagonal] at hp
  simp only [neumannTerm, ← hp, mul_pow, ← pow_mul]
  ring

/-- Partial fractions for the reciprocal shifted factorial:
`∑_{k+m=j} (-1)^m/(k! m! (x+k)) = (-1)^j / ∏_{i ≤ j} (x+i)`. -/
theorem sum_antidiagonal_neg_one_pow_div_add (j : ℕ) {x : ℂ} (hx : ∀ i : ℕ, x + i ≠ 0) :
    ∑ p ∈ antidiagonal j, (-1 : ℂ) ^ p.2 / ((p.1 ! : ℂ) * p.2 ! * (x + p.1)) =
      (-1) ^ j / ∏ i ∈ range (j + 1), (x + i) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    have hx1 : ∀ i : ℕ, x + 1 + i ≠ 0 := fun i => by
      simpa [add_assoc, add_comm (1:ℂ)] using hx (i + 1)
    have hj : ((j : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero j
    have hsplit : ((j : ℂ) + 1) * ∑ p ∈ antidiagonal (j + 1),
        (-1 : ℂ) ^ p.2 / ((p.1 ! : ℂ) * p.2 ! * (x + p.1)) =
        ∑ p ∈ antidiagonal (j + 1), (-1 : ℂ) ^ p.2 * p.1 / ((p.1 ! : ℂ) * p.2 ! * (x + p.1)) +
        ∑ p ∈ antidiagonal (j + 1), (-1 : ℂ) ^ p.2 * p.2 / ((p.1 ! : ℂ) * p.2 ! * (x + p.1)) := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun p hp => ?_
      rw [mem_antidiagonal] at hp
      have : ((j : ℂ) + 1) = p.1 + p.2 := by exact_mod_cast hp.symm
      rw [this]; ring
    have h1 : ∑ p ∈ antidiagonal (j + 1), (-1 : ℂ) ^ p.2 * p.1 / ((p.1 ! : ℂ) * p.2 ! * (x + p.1))
        = ∑ p ∈ antidiagonal j, (-1 : ℂ) ^ p.2 / ((p.1 ! : ℂ) * p.2 ! * (x + 1 + p.1)) := by
      rw [Nat.sum_antidiagonal_succ]
      simp only [Nat.cast_zero, mul_zero, zero_div, zero_add]
      refine sum_congr rfl fun p _ => ?_
      rw [Nat.factorial_succ]
      have h := hx1 p.1
      have hf : (p.1 ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hf2 : (p.2 ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      push_cast
      rw [show x + ((p.1 : ℂ) + 1) = x + 1 + p.1 by ring]
      field_simp
    have h2 : ∑ p ∈ antidiagonal (j + 1), (-1 : ℂ) ^ p.2 * p.2 / ((p.1 ! : ℂ) * p.2 ! * (x + p.1))
        = -∑ p ∈ antidiagonal j, (-1 : ℂ) ^ p.2 / ((p.1 ! : ℂ) * p.2 ! * (x + p.1)) := by
      rw [Nat.sum_antidiagonal_succ', ← sum_neg_distrib]
      simp only [Nat.cast_zero, mul_zero, zero_div, zero_add]
      refine sum_congr rfl fun p _ => ?_
      rw [Nat.factorial_succ]
      have h := hx p.1
      have hf : (p.1 ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hf2 : (p.2 ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      push_cast
      field_simp
      ring
    rw [h1, h2, ih hx1, ih hx] at hsplit
    have hP : ∏ i ∈ range (j + 1 + 1), (x + i) = x * ∏ i ∈ range (j + 1), (x + 1 + i) := by
      rw [prod_range_succ']
      simp only [Nat.cast_zero, add_zero, Nat.cast_succ]
      rw [mul_comm]; congr 1
      exact prod_congr rfl fun i _ => by ring
    have hP' : ∏ i ∈ range (j + 1 + 1), (x + i) = (∏ i ∈ range (j + 1), (x + i)) * (x + (j + 1)) := by
      rw [prod_range_succ]; push_cast; ring
    have hA : ∏ i ∈ range (j + 1), (x + i) ≠ 0 := prod_ne_zero_iff.mpr fun i _ => hx i
    have hB : ∏ i ∈ range (j + 1), (x + 1 + i) ≠ 0 := prod_ne_zero_iff.mpr fun i _ => hx1 i
    have hx0 : x ≠ 0 := by simpa using hx 0
    have hxj : x + (j + 1) ≠ 0 := by simpa using hx (j + 1)
    apply mul_left_cancel₀ hj
    rw [hsplit]
    have e1 : (∏ i ∈ range (j + 1), (x + 1 + i)) = (∏ i ∈ range (j + 1 + 1), (x + i)) / x := by
      rw [hP]; field_simp
    have e2 : (∏ i ∈ range (j + 1), (x + i)) = (∏ i ∈ range (j + 1 + 1), (x + i)) / (x + (j+1)) := by
      rw [hP']; field_simp
    have hC : ∏ i ∈ range (j + 1 + 1), (x + i) ≠ 0 := prod_ne_zero_iff.mpr fun i _ => hx i
    rw [e1, e2]
    field_simp
    ring

/-- Summand of Neumann's expansion of a power, in range form. -/
def powerNeumannSummand (l : ℂ) (j k : ℕ) : ℂ :=
  (-1) ^ (j - k) * (l + 2 * k) * Gamma (l + k) / ((k ! : ℂ) * ((j - k) ! : ℂ) * Gamma (l + j + k + 1))

/-- `Γ(λ+n) ≠ 0` for `λ ∉ -ℕ`. -/
theorem Gamma_add_nat_ne_zero_of_ne {l : ℂ} (hl : ∀ n : ℕ, l ≠ -n) (n : ℕ) : Gamma (l + n) ≠ 0 := by
  refine Complex.Gamma_ne_zero fun m h => hl (m + n) ?_
  push_cast; linear_combination h

/-- `λ+n ≠ 0` for `λ ∉ -ℕ`. -/
theorem add_nat_ne_zero_of_ne {l : ℂ} (hl : ∀ n : ℕ, l ≠ -n) (n : ℕ) : l + n ≠ 0 := fun h =>
  hl n (by linear_combination h)

/-- Closed partial sums of `powerNeumannSummand`. -/
theorem sum_range_powerNeumannSummand {l : ℂ} (hl : ∀ n : ℕ, l ≠ -n) (K e : ℕ) :
    ∑ k ∈ range (K + 1), powerNeumannSummand l (K + 1 + e) k =
      (-1) ^ (e + 1) * Gamma (l + K + 1) /
        (((K + 1 + e : ℕ) : ℂ) * (K ! : ℂ) * (e ! : ℂ) * Gamma (l + 2 * K + 2 + e)) := by
  induction K generalizing e with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, powerNeumannSummand, Nat.sub_zero,
      Nat.cast_zero, mul_zero, add_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
    have h0 := add_nat_ne_zero_of_ne hl 0
    have hG := Gamma_add_nat_ne_zero_of_ne hl 0
    have hG2 := Gamma_add_nat_ne_zero_of_ne hl (e + 2)
    simp only [Nat.cast_zero, add_zero] at h0 hG
    rw [show l + ((1 + e : ℕ) : ℂ) + 1 = l + ((e + 2 : ℕ) : ℂ) by push_cast; ring,
      show l + 2 + (e : ℂ) = l + ((e + 2 : ℕ) : ℂ) by push_cast; ring,
      Complex.Gamma_add_one _ h0, show 1 + e = e + 1 by ring, Nat.factorial_succ]
    have hf : (e ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    push_cast
    field_simp
  | succ K ih =>
    rw [sum_range_succ, show K + 1 + 1 + e = K + 1 + (e + 1) by ring, ih (e + 1)]
    simp only [powerNeumannSummand]
    rw [show K + 1 + (e + 1) - (K + 1) = e + 1 by omega]
    have hf1 : (K ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [Nat.factorial_succ]
    push_cast
    have h1 : l + K + 1 ≠ 0 := by
      have := add_nat_ne_zero_of_ne hl (K + 1); push_cast at this; rwa [← add_assoc] at this
    have h2 : l + 2 * K + 3 + e ≠ 0 := by
      have := add_nat_ne_zero_of_ne hl (2 * K + 3 + e); push_cast at this
      rwa [← add_assoc, ← add_assoc] at this
    have hg : Gamma (l + K + 1) ≠ 0 := by
      have := Gamma_add_nat_ne_zero_of_ne hl (K + 1); push_cast at this; rwa [← add_assoc] at this
    have hG : Gamma (l + 2 * K + 3 + e) ≠ 0 := by
      have := Gamma_add_nat_ne_zero_of_ne hl (2 * K + 3 + e); push_cast at this
      rwa [← add_assoc, ← add_assoc] at this
    rw [show l + ((K : ℂ) + 1) = l + K + 1 by ring,
      show l + 2 * (K : ℂ) + 2 + ((e : ℂ) + 1) = l + 2 * K + 3 + e by ring,
      show l + ((K : ℂ) + 1 + ((e : ℂ) + 1)) + ((K : ℂ) + 1) + 1 = (l + 2 * K + 3 + e) + 1 by ring,
      show l + 2 * ((K : ℂ) + 1) + 2 + (e : ℂ) = (l + 2 * K + 3 + e) + 1 by ring,
      Complex.Gamma_add_one _ h1, Complex.Gamma_add_one _ h2]
    generalize Gamma (l + K + 1) = g at hg ⊢
    generalize Gamma (l + 2 * K + 3 + e) = G at hG ⊢
    have hf2 : (e ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hK : (K : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero K
    have he : (e : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero e
    have hKe : (K : ℂ) + 1 + ((e : ℂ) + 1) ≠ 0 := by
      have := Nat.cast_add_one_ne_zero (R := ℂ) (K + 1 + e); push_cast at this
      rwa [show (K : ℂ) + 1 + e + 1 = K + 1 + (e + 1) by ring] at this
    rw [div_add_div _ _ (by simp [*]) (by simp [*]), div_eq_div_iff (by simp [*]) (by simp [*])]
    ring

/-- Coefficients of Neumann's expansion of `(z/2)^λ` in Bessel functions. -/
def powerNeumannCoeff (l : ℂ) (k : ℕ) : ℂ := (l + 2 * k) * Gamma (l + k) / k !

/-- The convolution identity behind Neumann's expansion of a power:
`∑_{k+m=j} (λ+2k)Γ(λ+k)/k! · (-1)^m/(m! Γ(λ+2k+m+1)) = δ_{j0}`. -/
theorem neumannCoeff_powerNeumannCoeff {l : ℂ} (hl : ∀ n : ℕ, l ≠ -n) (j : ℕ) :
    neumannCoeff l (-1) (powerNeumannCoeff l) (fun k => 2 * k) j = if j = 0 then 1 else 0 := by
  have hterm : ∀ k ∈ range (j + 1), powerNeumannCoeff l k * (-1) ^ (j - k) *
      regularizedHGFunCoeff (∅ : Multiset ℂ) {l + ((2 * k : ℕ) : ℂ) + 1} (j - k) =
      powerNeumannSummand l j k := by
    intro k hk
    have hkj : k ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [regularizedHGFunCoeff_empty, powerNeumannCoeff, powerNeumannSummand]
    rw [show l + ((2 * k : ℕ) : ℂ) + 1 + ((j - k : ℕ) : ℂ) = l + j + k + 1 by
      push_cast [Nat.cast_sub hkj]; ring]
    field_simp
  rw [neumannCoeff, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_congr rfl hterm]
  rcases j with _ | J
  · simp only [zero_add, range_one, sum_singleton, powerNeumannSummand, Nat.sub_zero,
      Nat.cast_zero, mul_zero, add_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul,
      ite_true]
    have h0 := add_nat_ne_zero_of_ne hl 0
    have hG := Gamma_add_nat_ne_zero_of_ne hl 0
    simp only [Nat.cast_zero, add_zero] at h0 hG
    rw [Complex.Gamma_add_one _ h0]
    field_simp
  · rw [sum_range_succ, show J + 1 = J + 1 + 0 by rfl, sum_range_powerNeumannSummand hl J 0]
    simp only [powerNeumannSummand, Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one,
      mul_one, add_zero, one_mul, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
      Nat.cast_zero, Nat.cast_add]
    have h1 : l + 2 * J + 2 ≠ 0 := by
      have := add_nat_ne_zero_of_ne hl (2 * J + 2); push_cast at this
      rwa [← add_assoc] at this
    have hg : Gamma (l + J + 1) ≠ 0 := by
      have := Gamma_add_nat_ne_zero_of_ne hl (J + 1); push_cast at this
      rwa [← add_assoc] at this
    have hG : Gamma (l + 2 * J + 2) ≠ 0 := by
      have := Gamma_add_nat_ne_zero_of_ne hl (2 * J + 2); push_cast at this
      rwa [← add_assoc] at this
    rw [Nat.factorial_succ]
    push_cast
    rw [show l + ((J : ℂ) + 1) + ((J : ℂ) + 1) + 1 = (l + 2 * J + 2) + 1 by ring,
      Complex.Gamma_add_one _ h1, show l + ((J : ℂ) + 1) = l + J + 1 by ring]
    generalize Gamma (l + J + 1) = g at hg ⊢
    generalize Gamma (l + 2 * J + 2) = G at hG ⊢
    have hf : (J ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hJ : (J : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero J
    rw [div_add_div _ _ (by simp [*]) (by simp [*]), div_eq_iff (by simp [*])]
    ring

/-- The Bessel operator `z²D² + zD + z² - ν²` at the level of Neumann coefficients: with
`a + b = λ`, multiplying `cₖ` by `(k+a)(k+b)` corresponds to the recurrence
`(j+1+a)(j+1+b) T_{j+1} + T_j`. -/
theorem neumannCoeff_bessel_recurrence {l a b : ℂ} (hab : a + b = l) (c : ℕ → ℂ) (j : ℕ) :
    (j + 1 + a) * (j + 1 + b) * neumannCoeff l (-1) c (fun k => 2 * k) (j + 1) +
        neumannCoeff l (-1) c (fun k => 2 * k) j =
      neumannCoeff l (-1) (fun k => (k + a) * (k + b) * c k) (fun k => 2 * k) (j + 1) := by
  simp only [neumannCoeff]
  rw [Nat.sum_antidiagonal_succ', Nat.sum_antidiagonal_succ', mul_add, add_assoc,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  push_cast
  congr 1
  · ring
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [mem_antidiagonal] at hp
  have hr := regularized0F1_coeff_recurrence (l + ((2 * p.1 : ℕ) : ℂ) + 1) p.2
  push_cast at hr ⊢
  have hj : (j : ℂ) = p.1 + p.2 := by exact_mod_cast hp.symm
  rw [← hr, hj, ← hab]
  ring

/-- Lommel-type Neumann coefficients: with `a + b = λ`,
`∑_{k+m=j} (λ+2k)Γ(λ+k)/(k!(k+a)(k+b)) · (-1)^m/(m!Γ(λ+2k+m+1)) = (-1)^j/∏_{i≤j}(i+a)(i+b)`. -/
theorem neumannCoeff_lommel {l a b : ℂ} (hab : a + b = l) (hl : ∀ n : ℕ, l ≠ -n)
    (ha : ∀ n : ℕ, (n : ℂ) + a ≠ 0) (hb : ∀ n : ℕ, (n : ℂ) + b ≠ 0) (j : ℕ) :
    neumannCoeff l (-1) (fun k => powerNeumannCoeff l k / ((k + a) * (k + b))) (fun k => 2 * k) j =
      (-1) ^ j / ∏ i ∈ range (j + 1), ((i + a) * (i + b)) := by
  induction j with
  | zero =>
    simp only [neumannCoeff, Finset.Nat.antidiagonal_zero, sum_singleton, powerNeumannCoeff,
      regularizedHGFunCoeff_empty, zero_add, range_one, prod_singleton]
    have h0 := add_nat_ne_zero_of_ne hl 0
    have hG := Gamma_add_nat_ne_zero_of_ne hl 0
    have ha0 := ha 0
    simp only [Nat.cast_zero, add_zero, mul_zero, zero_add, Nat.factorial_zero, Nat.cast_one]
      at h0 hG ha0 ⊢
    rw [Complex.Gamma_add_one _ h0]
    have hb0 := hb 0
    simp only [Nat.cast_zero, zero_add] at hb0
    field_simp
  | succ j ih =>
    have hrec := neumannCoeff_bessel_recurrence hab
      (fun k => powerNeumannCoeff l k / ((k + a) * (k + b))) j
    have hfun : (fun k : ℕ => ((k : ℂ) + a) * (k + b) *
        (powerNeumannCoeff l k / ((k + a) * (k + b)))) = powerNeumannCoeff l := by
      funext k
      have := ha k; have := hb k
      field_simp
    rw [hfun, neumannCoeff_powerNeumannCoeff hl, ite_eq_right_iff.mpr (fun h => absurd h (Nat.succ_ne_zero j)), ih] at hrec
    have hA : ((j : ℂ) + 1 + a) * (j + 1 + b) ≠ 0 := by
      have h1 := ha (j + 1); have h2 := hb (j + 1); push_cast at h1 h2
      exact mul_ne_zero h1 h2
    have hP : ∏ i ∈ range (j + 1), (((i : ℂ) + a) * (i + b)) ≠ 0 :=
      prod_ne_zero_iff.mpr fun i _ => mul_ne_zero (ha i) (hb i)
    rw [prod_range_succ, pow_succ]
    push_cast
    rw [eq_div_iff (mul_ne_zero hP hA)]
    have := eq_neg_of_add_eq_zero_left hrec
    calc _ = (∏ i ∈ range (j + 1), (((i : ℂ) + a) * (i + b))) *
          (((j : ℂ) + 1 + a) * (j + 1 + b) *
            neumannCoeff l (-1) (fun k => powerNeumannCoeff l k / ((k + a) * (k + b)))
              (fun k => 2 * k) (j + 1)) := by ring
      _ = _ := by rw [this]; field_simp

/-- `J_{ν+n}(z) = (z/2)^ν (z/2)^n ₀F̃₁(;ν+n+1;-(z/2)²)` for `z ≠ 0`. -/
theorem besselJ_add_nat {z : ℂ} (hz : z ≠ 0) (ν : ℂ) (n : ℕ) :
    besselJ (ν + n) z = (z / 2) ^ ν * ((z / 2) ^ n *
      regularizedHGFun (∅ : Multiset ℂ) {ν + n + 1} (-1 * (z / 2) ^ 2)) := by
  rw [besselJ_eq_regularized, cpow_add _ _ (div_ne_zero hz two_ne_zero), cpow_natCast,
    show -(z ^ 2 / 4) = -1 * (z / 2) ^ 2 by ring]
  ring

/-- `I_{ν+n}(z) = (z/2)^ν (z/2)^n ₀F̃₁(;ν+n+1;(z/2)²)` for `z ≠ 0`. -/
theorem besselI_add_nat {z : ℂ} (hz : z ≠ 0) (ν : ℂ) (n : ℕ) :
    besselI (ν + n) z = (z / 2) ^ ν * ((z / 2) ^ n *
      regularizedHGFun (∅ : Multiset ℂ) {ν + n + 1} (1 * (z / 2) ^ 2)) := by
  rw [besselI, cpow_add _ _ (div_ne_zero hz two_ne_zero), cpow_natCast,
    show z ^ 2 / 4 = 1 * (z / 2) ^ 2 by ring]
  ring

/-- A Neumann series with `eₖ = 2k` sums to the power series of its convolution coefficients. -/
theorem hasSum_neumann_tsum (ν σ w : ℂ) (a : ℕ → ℂ) (n : ℕ → ℕ)
    (ha : Summable fun k => ‖a k‖ * ‖w‖ ^ (2 * k) * (2 ^ n k / (n k)!)) :
    HasSum (fun k => a k * w ^ (2 * k) *
        regularizedHGFun (∅ : Multiset ℂ) {ν + n k + 1} (σ * w ^ 2))
      (∑' j, neumannCoeff ν σ a n j * w ^ (2 * j)) := by
  rw [(hasSum_neumannCoeff ν σ w a n ha).tsum_eq]
  exact hasSum_neumann ν σ w a n (fun k => 2 * k) ha

/-- **Neumann series of `J` as a power series.** If `pₖ + nₖ = 2k` and
`∑ₖ |aₖ| |z/2|^{2k} 2^{nₖ}/nₖ! < ∞`, then
`∑ₖ aₖ (z/2)^{pₖ} J_{ν+nₖ}(z) = (z/2)^ν ∑ⱼ bⱼ (z/2)^{2j}` with
`bⱼ = ∑_{k+m=j} aₖ (-1)^m/(m! Γ(ν+nₖ+m+1))`. -/
theorem hasSum_besselJ_neumann {z : ℂ} (hz : z ≠ 0) (ν : ℂ) (a : ℕ → ℂ) (p n : ℕ → ℕ)
    (hpn : ∀ k, p k + n k = 2 * k)
    (ha : Summable fun k => ‖a k‖ * ‖z / 2‖ ^ (2 * k) * (2 ^ n k / (n k)!)) :
    HasSum (fun k => a k * (z / 2) ^ p k * besselJ (ν + n k) z)
      ((z / 2) ^ ν * ∑' j, neumannCoeff ν (-1) a n j * (z / 2) ^ (2 * j)) := by
  convert (hasSum_neumann_tsum ν (-1) (z / 2) a n ha).mul_left ((z / 2) ^ ν) using 1
  funext k
  rw [besselJ_add_nat hz, ← hpn k, pow_add]
  ring

/-- **Neumann series of `I` as a power series**, the analogue of `hasSum_besselJ_neumann`. -/
theorem hasSum_besselI_neumann {z : ℂ} (hz : z ≠ 0) (ν : ℂ) (a : ℕ → ℂ) (p n : ℕ → ℕ)
    (hpn : ∀ k, p k + n k = 2 * k)
    (ha : Summable fun k => ‖a k‖ * ‖z / 2‖ ^ (2 * k) * (2 ^ n k / (n k)!)) :
    HasSum (fun k => a k * (z / 2) ^ p k * besselI (ν + n k) z)
      ((z / 2) ^ ν * ∑' j, neumannCoeff ν 1 a n j * (z / 2) ^ (2 * j)) := by
  convert (hasSum_neumann_tsum ν 1 (z / 2) a n ha).mul_left ((z / 2) ^ ν) using 1
  funext k
  rw [besselI_add_nat hz, ← hpn k, pow_add]
  ring

/-- Comparison form of `hasSum_besselJ_neumann`: identify the coefficients with those of a
known power series. -/
theorem hasSum_besselJ_neumann_of_coeff {z : ℂ} (hz : z ≠ 0) (ν : ℂ) (a : ℕ → ℂ)
    (p n : ℕ → ℕ) (hpn : ∀ k, p k + n k = 2 * k)
    (ha : Summable fun k => ‖a k‖ * ‖z / 2‖ ^ (2 * k) * (2 ^ n k / (n k)!))
    (b : ℕ → ℂ) (hb : ∀ j, neumannCoeff ν (-1) a n j = b j) :
    HasSum (fun k => a k * (z / 2) ^ p k * besselJ (ν + n k) z)
      ((z / 2) ^ ν * ∑' j, b j * (z / 2) ^ (2 * j)) := by
  simpa only [hb] using hasSum_besselJ_neumann hz ν a p n hpn ha

/-- **Holomorphy of Neumann series**: under the summability condition for every radius, the
Neumann series is an entire function of `w`. -/
theorem differentiable_neumann (ν σ : ℂ) (a : ℕ → ℂ) (n e : ℕ → ℕ)
    (ha : ∀ r : ℝ, Summable fun k => ‖a k‖ * r ^ e k * (2 ^ n k / (n k)!)) :
    Differentiable ℂ (fun w => ∑' k, a k * w ^ e k *
      regularizedHGFun (∅ : Multiset ℂ) {ν + n k + 1} (σ * w ^ 2)) := by
  intro w₀
  obtain ⟨C, hC0, hC⟩ := exists_norm_regularized0F1Coeff_le ν
  set R : ℝ := ‖w₀‖ + 1
  have hR : 0 ≤ R := by positivity
  set T : ℝ := ∑' m : ℕ, (2 * (‖σ‖ * R ^ 2)) ^ m / (m ! : ℝ)
  have hT := Real.summable_pow_div_factorial (2 * (‖σ‖ * R ^ 2))
  have hu : Summable fun k => ‖a k‖ * R ^ e k * (2 ^ n k / (n k)!) * C * T :=
    ((ha R).mul_right C).mul_right T
  have hbound : ∀ k, ∀ w ∈ Metric.ball (0 : ℂ) R, ‖a k * w ^ e k *
      regularizedHGFun (∅ : Multiset ℂ) {ν + n k + 1} (σ * w ^ 2)‖ ≤
        ‖a k‖ * R ^ e k * (2 ^ n k / (n k)!) * C * T := by
    intro k w hw
    have hwR : ‖w‖ ≤ R := (mem_ball_zero_iff.mp hw).le
    have hs := (hasFPowerSeriesOnBall_regularized0F1 (ν + n k + 1)).hasSum_mul_pow
      (z := σ * w ^ 2) (by simp)
    have hF : ‖regularizedHGFun (∅ : Multiset ℂ) {ν + n k + 1} (σ * w ^ 2)‖ ≤
        C * (2 ^ n k / (n k)!) * T := by
      refine hs.norm_le_of_bounded ((hT.hasSum).mul_left (C * (2 ^ n k / (n k)!))) fun m => ?_
      rw [norm_mul, norm_pow, norm_mul, norm_pow]
      calc ‖regularizedHGFunCoeff (∅ : Multiset ℂ) {ν + n k + 1} m‖ * (‖σ‖ * ‖w‖ ^ 2) ^ m
          ≤ C * (2 ^ n k / (n k)!) * (2 ^ m / m !) * (‖σ‖ * R ^ 2) ^ m := by
            gcongr
            exact hC (n k) m
        _ = C * (2 ^ n k / (n k)!) * ((2 * (‖σ‖ * R ^ 2)) ^ m / m !) := by
            rw [mul_pow]; ring_nf
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖a k‖ * ‖w‖ ^ e k * ‖regularizedHGFun (∅ : Multiset ℂ) {ν + n k + 1} (σ * w ^ 2)‖
        ≤ ‖a k‖ * R ^ e k * (C * (2 ^ n k / (n k)!) * T) := by gcongr
      _ = _ := by ring
  have hdiff : ∀ k, DifferentiableOn ℂ (fun w => a k * w ^ e k *
      regularizedHGFun (∅ : Multiset ℂ) {ν + n k + 1} (σ * w ^ 2)) (Metric.ball 0 R) := by
    intro k
    have hF : Differentiable ℂ (regularizedHGFun (∅ : Multiset ℂ) {ν + n k + 1}) :=
      fun x => (analyticAt_regularized0F1 _ x).differentiableAt
    exact ((differentiable_const _).mul (differentiable_pow _)).mul
      (hF.comp (differentiable_const _ |>.mul (differentiable_pow 2))) |>.differentiableOn
  have h := differentiableOn_tsum_of_summable_norm hu hdiff Metric.isOpen_ball hbound
  exact h.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp [R]))

/-- A uniform bound for `1/(n+c)` (with `1/0 = 0`). -/
theorem exists_norm_recip_nat_add_le (c : ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ‖((n : ℂ) + c)⁻¹‖ ≤ B := by
  set N : ℕ := ⌈‖c‖⌉₊ + 1
  refine ⟨1 + ∑ i ∈ range N, ‖((i : ℂ) + c)⁻¹‖, by positivity, fun n => ?_⟩
  rcases lt_or_ge n N with hn | hn
  · have : ‖((n : ℂ) + c)⁻¹‖ ≤ ∑ i ∈ range N, ‖((i : ℂ) + c)⁻¹‖ :=
      Finset.single_le_sum (f := fun i : ℕ => ‖((i : ℂ) + c)⁻¹‖)
        (fun i _ => norm_nonneg _) (Finset.mem_range.mpr hn)
    linarith
  · have hN : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hc' : ‖c‖ + 1 ≤ N := by
      have := Nat.le_ceil ‖c‖; simp only [N]; push_cast; linarith
    have h1 : 1 ≤ ‖(n : ℂ) + c‖ := by
      have := norm_add_le ((n : ℂ) + c) (-c)
      simp only [add_neg_cancel_right, Complex.norm_natCast, norm_neg] at this
      linarith
    have : ‖((n : ℂ) + c)⁻¹‖ ≤ 1 := by
      rw [norm_inv]; exact inv_le_one_of_one_le₀ h1
    have : 0 ≤ ∑ i ∈ range N, ‖((i : ℂ) + c)⁻¹‖ := sum_nonneg fun i _ => norm_nonneg _
    linarith

/-- Growth bound `|Γ(c+n)| ≤ C 2ⁿ n!`, uniformly in `n`, for every `c`. -/
theorem exists_norm_Gamma_add_nat_le (c : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖Gamma (c + n)‖ ≤ C * (2 ^ n * n !) := by
  set N : ℕ := ⌈1 - c.re⌉₊
  set s : ℂ := c + N
  have hs : 1 ≤ s.re := by
    have := Nat.le_ceil (1 - c.re); simp [s]; linarith
  set M : ℕ := ⌈‖s‖⌉₊
  have hM : ‖s‖ ≤ M := Nat.le_ceil _
  have hstep : ∀ i : ℕ, ‖Gamma (s + i)‖ * M ! ≤ ‖Gamma s‖ * (M + i)! := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hne : s + i ≠ 0 := by
        intro h; have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
      rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hne, norm_mul,
        show M + (i + 1) = (M + i) + 1 by ring, Nat.factorial_succ, Nat.cast_mul]
      have h1 : ‖s + i‖ ≤ ((M + i + 1 : ℕ) : ℝ) := by
        have := norm_add_le s (i : ℂ)
        simp only [Complex.norm_natCast] at this
        push_cast; linarith
      calc ‖s + ↑i‖ * ‖Gamma (s + ↑i)‖ * ↑M ! = ‖s + ↑i‖ * (‖Gamma (s + ↑i)‖ * ↑M !) := by ring
        _ ≤ ((M + i + 1 : ℕ) : ℝ) * (‖Gamma s‖ * (M + i)!) := by gcongr
        _ = _ := by ring
  refine ⟨‖Gamma s‖ * 2 ^ M + ∑ i ∈ range N, ‖Gamma (c + i)‖, by positivity, fun n => ?_⟩
  have hfac1 : (1 : ℝ) ≤ 2 ^ n * n ! := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n))
  have hS0 : 0 ≤ ∑ i ∈ range N, ‖Gamma (c + i)‖ := sum_nonneg fun i _ => norm_nonneg _
  rcases lt_or_ge n N with hn | hn
  · have : ‖Gamma (c + n)‖ ≤ ∑ i ∈ range N, ‖Gamma (c + i)‖ :=
      Finset.single_le_sum (f := fun i : ℕ => ‖Gamma (c + i)‖)
        (fun i _ => norm_nonneg _) (Finset.mem_range.mpr hn)
    have h0 : 0 ≤ ‖Gamma s‖ * 2 ^ M := by positivity
    nlinarith
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hci : c + ((N + i : ℕ) : ℂ) = s + i := by simp [s]; ring
    rw [hci]
    have hMi : ((M + i)! : ℝ) ≤ 2 ^ (M + i) * M ! * i ! := by
      have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right M i)
      rw [Nat.add_sub_cancel_left] at h
      have h2 : ((M + i).choose M : ℝ) ≤ 2 ^ (M + i) := by
        exact_mod_cast Nat.choose_le_two_pow (M + i) M
      rw [← h]; push_cast
      gcongr
    have hfM : (0 : ℝ) < M ! := by exact_mod_cast Nat.factorial_pos M
    have hb : ‖Gamma (s + i)‖ ≤ ‖Gamma s‖ * 2 ^ M * (2 ^ i * i !) := by
      have := hstep i
      rw [← le_div_iff₀ hfM] at this
      refine this.trans ?_
      rw [div_le_iff₀ hfM]
      calc ‖Gamma s‖ * ((M + i)! : ℝ) ≤ ‖Gamma s‖ * (2 ^ (M + i) * M ! * i !) := by gcongr
        _ = _ := by ring
    have hii : (2 : ℝ) ^ i * i ! ≤ 2 ^ (N + i) * (N + i)! := by
      gcongr
      · norm_num
      all_goals omega
    calc ‖Gamma (s + i)‖ ≤ ‖Gamma s‖ * 2 ^ M * (2 ^ i * i !) := hb
      _ ≤ ‖Gamma s‖ * 2 ^ M * (2 ^ (N + i) * (N + i)!) := by gcongr
      _ ≤ _ := by gcongr; linarith

/-- Neumann coefficients of a power grow at most geometrically. -/
theorem exists_norm_powerNeumannCoeff_le (l : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ‖powerNeumannCoeff l k‖ ≤ C * 4 ^ k := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_Gamma_add_nat_le l
  refine ⟨C * (‖l‖ + 2), by positivity, fun k => ?_⟩
  have hk : ((k : ℝ) + 1) ≤ 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self (n := k)
  have hl2 : ‖l + 2 * k‖ ≤ (‖l‖ + 2) * 2 ^ k := by
    have := norm_add_le l (2 * (k : ℂ))
    rw [norm_mul, Complex.norm_natCast, Complex.norm_two] at this
    nlinarith [norm_nonneg l]
  have hf : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  rw [powerNeumannCoeff, norm_div, norm_mul, Complex.norm_natCast, div_le_iff₀ hf]
  calc ‖l + 2 * k‖ * ‖Gamma (l + k)‖ ≤ ((‖l‖ + 2) * 2 ^ k) * (C * (2 ^ k * k !)) := by
        gcongr; exact hC k
    _ = C * (‖l‖ + 2) * 4 ^ k * k ! := by
        rw [show (4 : ℝ) ^ k = 2 ^ k * 2 ^ k by rw [← mul_pow]; norm_num]; ring

/-- Summability hypothesis of the Neumann theorems for geometrically bounded coefficients and
orders `ν + nₖ` with `k ≤ nₖ ≤ 2k`. -/
theorem summable_neumann_of_norm_le {a : ℕ → ℂ} {C D : ℝ} (hD : 0 ≤ D)
    (h : ∀ k, ‖a k‖ ≤ C * D ^ k) (n : ℕ → ℕ) (hn : ∀ k, k ≤ n k ∧ n k ≤ 2 * k) (r : ℝ) :
    Summable fun k => ‖a k‖ * r ^ (2 * k) * (2 ^ n k / (n k)!) := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (h 0)
  have hr : ∀ k : ℕ, 0 ≤ r ^ (2 * k) := fun k => by rw [pow_mul]; positivity
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (mul_nonneg (norm_nonneg _) (hr k))
    (by positivity)) (fun k => ?_)
    ((Real.summable_pow_div_factorial (4 * D * r ^ 2)).mul_left C)
  have h2 : (2 : ℝ) ^ n k ≤ 4 ^ k := by
    rw [show (4 : ℝ) ^ k = 2 ^ (2 * k) by rw [pow_mul]; norm_num]
    exact pow_le_pow_right₀ (by norm_num) (hn k).2
  have hf : (k ! : ℝ) ≤ (n k)! := by exact_mod_cast Nat.factorial_le (hn k).1
  have hf0 : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  calc ‖a k‖ * r ^ (2 * k) * (2 ^ n k / (n k)!) ≤ (C * D ^ k) * r ^ (2 * k) * (4 ^ k / k !) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (h k) (hr k)) (div_le_div₀ (by positivity) h2 hf0 hf)
          (by positivity) (mul_nonneg (by positivity) (hr k))
    _ = C * ((4 * D * r ^ 2) ^ k / k !) := by rw [pow_mul]; ring

/-- Division by a positive real commutes with complex powers. -/
theorem div_ofReal_cpow {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ 0) (c : ℂ) :
    (z / r) ^ c = z ^ c / (r : ℂ) ^ c := by
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hlog : log (z / r) = log z - log r := by
    rw [div_eq_mul_inv, ← ofReal_inv, log_mul_ofReal _ (inv_pos.mpr hr) _ hz, Real.log_inv,
      ofReal_neg, ofReal_log hr.le]
    ring
  rw [cpow_def_of_ne_zero (div_ne_zero hz hr'), hlog, sub_mul, exp_sub,
    ← cpow_def_of_ne_zero hz, ← cpow_def_of_ne_zero hr']

/-- `(z/2)^c = z^c / 2^c` for `z ≠ 0`. -/
theorem div_two_cpow {z : ℂ} (hz : z ≠ 0) (c : ℂ) : (z / 2) ^ c = z ^ c / 2 ^ c := by
  simpa using div_ofReal_cpow (r := 2) two_pos hz c

/-- `Γ(x+j+1) = Γ(x) ∏_{i ≤ j} (x+i)` away from the poles. -/
theorem Gamma_add_nat_succ_eq_prod {x : ℂ} (hx : ∀ i : ℕ, x + i ≠ 0) (j : ℕ) :
    Gamma (x + j + 1) = Gamma x * ∏ i ∈ range (j + 1), (x + i) := by
  induction j with
  | zero => simpa [mul_comm] using Complex.Gamma_add_one x (by simpa using hx 0)
  | succ j ih =>
    rw [prod_range_succ, Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ (by
      simpa [add_assoc] using hx (j + 1)), ih]
    ring

/-- **Neumann's expansion of a power** (Watson §5.2):
`(z/2)^λ = ∑ₖ (λ+2k) Γ(λ+k)/k! J_{λ+2k}(z)` for `λ ∉ -ℕ`, `z ≠ 0`. -/
theorem hasSum_besselJ_neumann_power {l z : ℂ} (hl : ∀ n : ℕ, l ≠ -n) (hz : z ≠ 0) :
    HasSum (fun k : ℕ => (l + 2 * k) * Gamma (l + k) / k ! * besselJ (l + 2 * k) z)
      ((z / 2) ^ l) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_powerNeumannCoeff_le l
  have h := hasSum_besselJ_neumann_of_coeff hz l (powerNeumannCoeff l) (fun _ => 0)
    (fun k => 2 * k) (fun k => by simp)
    (summable_neumann_of_norm_le (by norm_num) hC _ (fun k => ⟨by omega, le_rfl⟩) _)
    (fun j => if j = 0 then 1 else 0) (neumannCoeff_powerNeumannCoeff hl)
  have ht : ∑' j : ℕ, (if j = 0 then (1 : ℂ) else 0) * (z / 2) ^ (2 * j) = 1 := by
    rw [tsum_eq_single 0 (fun j hj => by simp [hj])]; simp
  rw [ht, mul_one] at h
  convert h using 1
  funext k
  simp [powerNeumannCoeff]

/-- **Lommel-type Neumann series.** For `a + b = λ`, `λ ∉ -ℕ`, `a, b ∉ -ℕ`, `z ≠ 0`:
`∑ₖ (λ+2k)Γ(λ+k)/(k!(k+a)(k+b)) J_{λ+2k}(z) = (z/2)^λ ∑ⱼ (-1)^j (z/2)^{2j}/∏_{i≤j}(i+a)(i+b)`.
This is the expansion of the Lommel function `s_{λ-1,b-a}` (DLMF 11.9.7) in coefficient form. -/
theorem hasSum_besselJ_neumann_lommel {l a b z : ℂ} (hab : a + b = l) (hl : ∀ n : ℕ, l ≠ -n)
    (ha : ∀ n : ℕ, (n : ℂ) + a ≠ 0) (hb : ∀ n : ℕ, (n : ℂ) + b ≠ 0) (hz : z ≠ 0) :
    HasSum (fun k : ℕ => powerNeumannCoeff l k / ((k + a) * (k + b)) * besselJ (l + 2 * k) z)
      ((z / 2) ^ l * ∑' j : ℕ, (-1) ^ j / (∏ i ∈ range (j + 1), (((i : ℂ) + a) * (i + b))) *
        (z / 2) ^ (2 * j)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_powerNeumannCoeff_le l
  obtain ⟨Ba, hBa0, hBa⟩ := exists_norm_recip_nat_add_le a
  obtain ⟨Bb, hBb0, hBb⟩ := exists_norm_recip_nat_add_le b
  have hbd : ∀ k : ℕ, ‖powerNeumannCoeff l k / ((k + a) * (k + b))‖ ≤ (C * Ba * Bb) * 4 ^ k := by
    intro k
    rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul]
    calc ‖powerNeumannCoeff l k‖ * (‖((k : ℂ) + a)⁻¹‖ * ‖((k : ℂ) + b)⁻¹‖)
        ≤ (C * 4 ^ k) * (Ba * Bb) := by gcongr <;> simp_all
      _ = _ := by ring
  have h := hasSum_besselJ_neumann_of_coeff hz l
    (fun k => powerNeumannCoeff l k / ((k + a) * (k + b))) (fun _ => 0) (fun k => 2 * k)
    (fun k => by simp)
    (summable_neumann_of_norm_le (by norm_num) hbd _ (fun k => ⟨by omega, le_rfl⟩) _) _
    (neumannCoeff_lommel hab hl ha hb)
  convert h using 1
  funext k
  simp

/-- `(n+1)_m · n! = (n+m)!` for natural `n`. -/
theorem poch_natCast_add_one_mul_factorial (n m : ℕ) :
    DLMF.Hypergeometric.poch ((n : ℂ) + 1) m * n ! = ((n + m)! : ℕ) := by
  induction m with
  | zero => simp [DLMF.Hypergeometric.poch_zero]
  | succ m ih =>
    rw [DLMF.Hypergeometric.poch_succ, show n + (m + 1) = (n + m) + 1 by ring, Nat.factorial_succ]
    push_cast at ih ⊢
    rw [← ih]; ring

/-- The Pochhammer factor of the Bessel product series (DLMF 10.8.3) at half-integer orders:
`(2k+m+2)_m / m! = C(2k+2m+1, m)`. -/
theorem poch_div_factorial_eq_choose (k m : ℕ) :
    DLMF.Hypergeometric.poch (2 * k + m + 2 : ℂ) m / m ! = ((2 * k + 2 * m + 1).choose m : ℕ) := by
  have h1 := poch_natCast_add_one_mul_factorial (2 * k + m + 1) m
  have h2 := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * k + 2 * m + 1 by omega)
  rw [show 2 * k + 2 * m + 1 - m = 2 * k + m + 1 by omega] at h2
  rw [show 2 * k + m + 1 + m = 2 * k + 2 * m + 1 by ring, ← h2] at h1
  have hf1 : ((2 * k + m + 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf2 : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  push_cast at h1 ⊢
  rw [div_eq_iff hf2]
  apply mul_right_cancel₀ hf1
  rw [show (2 * (k : ℂ) + m + 2) = 2 * k + m + 1 + 1 by ring, h1]


/-! ### Very-well-poised and Kummer-type polynomial identities; Neumann series with `eₖ = k` -/

section LinearNeumann

open DLMF.Hypergeometric

/-- Summand of the very-well-poised polynomial identity `sum_range_vwpTerm`. -/
noncomputable def vwpTerm (A B : ℂ) (n s : ℕ) : ℂ :=
  (n.choose s : ℂ) * poch A s * poch B s * (A + 2 * s) * poch (A + 1 - B + s) (n - s) *
    poch (A + n + s + 1) (n - s)

/-- WZ certificate for `sum_range_vwpTerm`. -/
noncomputable def vwpCert (A B : ℂ) (n : ℕ) : ℕ → ℂ
  | 0 => 0
  | r + 1 => -((n.choose r : ℂ) * poch A (r + 1) * poch B (r + 1) * poch (A - B + r + 1) (n - r) *
      poch (A + n + r + 2) (n + 1 - r))

/-- `(x)_e (x+e)(x+e+1) = x (x+1)_{e+1}`. -/
theorem poch_mul_two_succ (x : ℂ) (e : ℕ) :
    poch x e * ((x + e) * (x + e + 1)) = x * poch (x + 1) (e + 1) := by
  rw [← poch_succ_left, poch_succ, poch_succ]; push_cast; ring

/-- The WZ step for `sum_range_vwpTerm`. -/
theorem vwpTerm_succ_sub (A B : ℂ) (n s : ℕ) (hs : s ≤ n + 1) :
    vwpTerm A B (n + 1) s - (A + 2 * n + 1) * (A + 2 * n + 2) * vwpTerm A B n s =
      vwpCert A B n (s + 1) - vwpCert A B n s := by
  rcases Nat.lt_or_ge n s with h | h
  · -- s = n + 1
    obtain rfl : s = n + 1 := by omega
    simp only [vwpTerm, vwpCert, Nat.choose_succ_self, Nat.choose_self, Nat.sub_self,
      Nat.cast_zero, zero_mul, mul_zero, sub_zero, show n + 1 - n = 1 by omega, poch_zero,
      poch_one, Nat.cast_one]
    push_cast
    ring
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
    have hY := poch_mul_two_succ (A + 2 * s + e + 1) e
    have hR := poch_succ (A + 1 - B + s) e
    rcases s with _ | r
    · simp only [vwpTerm, vwpCert, Nat.choose_zero_right, Nat.cast_one, poch_zero, Nat.cast_zero,
        Nat.sub_zero, zero_add, poch_one]
      simp only [Nat.cast_zero] at hY hR
      rw [hR, show A + ((e + 1 : ℕ) : ℂ) + 0 + 1 = A + 2 * 0 + e + 1 + 1 by push_cast; ring,
        show A + (e : ℂ) + 0 + 1 = A + 2 * 0 + e + 1 by ring,
        show A - B + 0 + 1 = A + 1 - B + 0 by ring,
        show A + (e : ℂ) + 0 + 2 = A + 2 * 0 + e + 1 + 1 by ring]
      generalize poch (A + 1 - B + 0) e = X at *
      generalize poch (A + 2 * 0 + ↑e + 1 + 1) (e + 1) = Y at *
      generalize poch (A + 2 * 0 + ↑e + 1) e = Z at *
      linear_combination (-(A * X)) * hY
    · simp only [vwpTerm, vwpCert, show r + 1 + e + 1 - (r + 1) = e + 1 by omega,
        show r + 1 + e - (r + 1) = e by omega, show r + 1 + e - r = e + 1 by omega,
        show r + 1 + e + 1 - r = e + 2 by omega]
      have hb : ((r + 1 + e).choose (r + 1) : ℂ) * ((r : ℂ) + 1) =
          ((r + 1 + e).choose r : ℂ) * ((e : ℂ) + 1) := by
        have := Nat.choose_succ_right_eq (r + 1 + e) r
        rw [show r + 1 + e - r = e + 1 by omega] at this
        exact_mod_cast this
      have hC1 : ((r + 1 + e + 1).choose (r + 1) : ℂ) =
          ((r + 1 + e).choose r : ℂ) + ((r + 1 + e).choose (r + 1) : ℂ) := by
        exact_mod_cast Nat.choose_succ_succ (r + 1 + e) r
      rw [hR, poch_succ A (r + 1), poch_succ B (r + 1), poch_succ_left (A - B + r + 1) e,
        show A + ((r + 1 + e + 1 : ℕ) : ℂ) + ((r + 1 : ℕ) : ℂ) + 1 =
          A + 2 * ((r + 1 : ℕ) : ℂ) + e + 1 + 1 by push_cast; ring,
        show A + ((r + 1 + e : ℕ) : ℂ) + ((r + 1 : ℕ) : ℂ) + 1 =
          A + 2 * ((r + 1 : ℕ) : ℂ) + e + 1 by push_cast; ring,
        show A - B + ((r + 1 : ℕ) : ℂ) + 1 = A + 1 - B + ((r + 1 : ℕ) : ℂ) by push_cast; ring,
        show A - B + (r : ℂ) + 1 + 1 = A + 1 - B + ((r + 1 : ℕ) : ℂ) by push_cast; ring,
        show A + ((r + 1 + e : ℕ) : ℂ) + ((r + 1 : ℕ) : ℂ) + 2 =
          A + 2 * ((r + 1 : ℕ) : ℂ) + e + 1 + 1 by push_cast; ring,
        show A + ((r + 1 + e : ℕ) : ℂ) + (r : ℂ) + 2 = A + 2 * ((r + 1 : ℕ) : ℂ) + e + 1 by
          push_cast; ring,
        poch_succ_left (A + 2 * ((r + 1 : ℕ) : ℂ) + e + 1) (e + 1)]
      rw [hC1]
      generalize poch A (r + 1) = PA at *
      generalize poch B (r + 1) = PB at *
      generalize poch (A + 1 - B + ((r + 1 : ℕ) : ℂ)) e = X at *
      generalize poch (A + 2 * ((r + 1 : ℕ) : ℂ) + e + 1 + 1) (e + 1) = Y at *
      generalize poch (A + 2 * ((r + 1 : ℕ) : ℂ) + e + 1) e = Z at *
      generalize ((r + 1 + e).choose (r + 1) : ℂ) = C0 at *
      generalize ((r + 1 + e).choose r : ℂ) = Cm at *
      push_cast at hY hb ⊢
      linear_combination (-(PA * PB * (A + 2 * (r + 1)) * X * C0)) * hY +
        (-(PA * PB * X * Y * (B + r + 1))) * hb

/-- A terminating very-well-poised `₄F₃(-1)` sum in polynomial form:
`∑ₛ C(n,s) (A)ₛ (B)ₛ (A+2s) (A+1-B+s)_{n-s} (A+n+s+1)_{n-s} = (A)_{2n+1}`. -/
theorem sum_range_vwpTerm (A B : ℂ) (n : ℕ) :
    ∑ s ∈ range (n + 1), vwpTerm A B n s = poch A (2 * n + 1) := by
  induction n with
  | zero => simp [vwpTerm, poch_one, poch_zero]
  | succ n ih =>
    have h := Finset.sum_congr rfl fun s (hs : s ∈ range (n + 2)) =>
      vwpTerm_succ_sub A B n s (by rw [Finset.mem_range] at hs; omega)
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub, ← Finset.mul_sum, Finset.sum_range_succ (fun s => vwpTerm A B n s) (n + 1),
      ih] at h
    have h0 : vwpTerm A B n (n + 1) = 0 := by simp [vwpTerm, Nat.choose_succ_self]
    have h1 : vwpCert A B n (n + 1 + 1) = 0 := by simp [vwpCert, Nat.choose_succ_self]
    rw [h0, h1, show vwpCert A B n 0 = 0 from rfl, add_zero, sub_zero, sub_eq_zero] at h
    rw [show n + 1 + 1 = n + 2 by ring, h, show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring,
      poch_succ A (2 * n + 1 + 1), poch_succ A (2 * n + 1)]
    push_cast
    ring

/-- Summand of `sum_range_kumTerm`: `C(K,2m) (2m)!/m! 2^{K-2m} (c+m)_{K-m}`. -/
noncomputable def kumTerm (c : ℂ) (K m : ℕ) : ℂ :=
  (K.choose (2 * m) : ℂ) * ((2 * m)! / m ! : ℂ) * 2 ^ (K - 2 * m) * poch (c + m) (K - m)

/-- WZ certificate for `sum_range_kumTerm`. -/
noncomputable def kumCert (c : ℂ) (K m : ℕ) : ℂ :=
  -(2 * m * ((2 * m)! / m ! : ℂ) * ((K + 1).choose (2 * m) : ℂ) / (K + 1) * 2 ^ (K + 1 - 2 * m) *
    poch (c + m) (K + 1 - m))

/-- `(2m+2)!/(m+1)! = 2(2m+1) (2m)!/m!`. -/
theorem two_mul_succ_factorial_div (m : ℕ) :
    ((2 * (m + 1))! / (m + 1)! : ℂ) = 2 * (2 * m + 1) * ((2 * m)! / m ! : ℂ) := by
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
    Nat.factorial_succ m]
  have h1 : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  push_cast
  field_simp
  ring

/-- The WZ step for `sum_range_kumTerm` (a contiguous relation in `c`). -/
theorem kumTerm_succ_sub (c : ℂ) (K m : ℕ) :
    kumTerm c (K + 1) m - (2 * c + K) * kumTerm (c + 1) K m =
      kumCert c K (m + 1) - kumCert c K m := by
  have hK : ((K : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero K
  have hq := two_mul_succ_factorial_div m
  by_cases h1 : 2 * m + 2 ≤ K + 1
  · obtain ⟨e, rfl⟩ : ∃ e, K = 2 * m + e + 1 := ⟨K - 2 * m - 1, by omega⟩
    have hB1 : ((2 * m + e + 1 + 1).choose (2 * m) : ℂ) * ((e : ℂ) + 2) =
        ((2 * m + e + 1).choose (2 * m) : ℂ) * (2 * m + e + 2) := by
      have h2 := Nat.choose_mul_succ_eq (2 * m + e + 1) (2 * m)
      rw [show 2 * m + e + 1 + 1 - 2 * m = e + 2 by omega] at h2
      have h2' : ((2 * m + e + 1).choose (2 * m) : ℂ) * ((2 * m + e + 1 + 1 : ℕ) : ℂ) =
          ((2 * m + e + 1 + 1).choose (2 * m) : ℂ) * ((e + 2 : ℕ) : ℂ) := by exact_mod_cast h2
      push_cast at h2'
      linear_combination -h2'
    have hB2 : ((2 * m + e + 1 + 1).choose (2 * (m + 1)) : ℂ) * ((2 * m + 1) * (2 * m + 2)) =
        ((2 * m + e + 1 + 1).choose (2 * m) : ℂ) * ((e + 2) * (e + 1)) := by
      have h3 := Nat.choose_succ_right_eq (2 * m + e + 2) (2 * m)
      have h4 := Nat.choose_succ_right_eq (2 * m + e + 2) (2 * m + 1)
      rw [show 2 * m + e + 2 - 2 * m = e + 2 by omega] at h3
      rw [show 2 * m + e + 2 - (2 * m + 1) = e + 1 by omega] at h4
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, show 2 * m + e + 1 + 1 = 2 * m + e + 2 by ring]
      have h3' : ((2 * m + e + 2).choose (2 * m + 1) : ℂ) * (2 * m + 1) =
          ((2 * m + e + 2).choose (2 * m) : ℂ) * (e + 2) := by exact_mod_cast h3
      have h4' : ((2 * m + e + 2).choose (2 * m + 1 + 1) : ℂ) * (2 * m + 1 + 1) =
          ((2 * m + e + 2).choose (2 * m + 1) : ℂ) * (e + 1) := by exact_mod_cast h4
      linear_combination (2 * m + 1 : ℂ) * h4' + (e + 1 : ℂ) * h3'
    simp only [kumTerm, kumCert]
    rw [show 2 * m + e + 1 + 1 - 2 * m = e + 2 by omega, show 2 * m + e + 1 - 2 * m = e + 1 by omega,
      show 2 * m + e + 1 + 1 - m = (m + e + 1) + 1 by omega,
      show 2 * m + e + 1 - m = m + e + 1 by omega,
      show 2 * m + e + 1 + 1 - 2 * (m + 1) = e by omega,
      show 2 * m + e + 1 + 1 - (m + 1) = m + e + 1 by omega, poch_succ_left (c + m) (m + e + 1),
      show c + (m : ℂ) + 1 = c + 1 + m by ring, hq]
    push_cast
    rw [show c + ((m : ℂ) + 1) = c + 1 + m by ring]
    generalize poch (c + 1 + m) (m + e + 1) = X
    generalize ((2 * m)! / m ! : ℂ) = q at *
    have hD : (2 * (m : ℂ) + e + 1 + 1) ≠ 0 := by exact_mod_cast (show 2 * m + e + 1 + 1 ≠ 0 by omega)
    have hI := mul_inv_cancel₀ hD
    simp only [div_eq_mul_inv]
    generalize (2 * (m : ℂ) + e + 1 + 1)⁻¹ = I at *
    generalize ((2 * m + e + 1 + 1).choose (2 * m) : ℂ) = B1 at *
    generalize ((2 * m + e + 1).choose (2 * m) : ℂ) = B0 at *
    generalize ((2 * m + e + 1 + 1).choose (2 * (m + 1)) : ℂ) = B2 at *
    linear_combination (q * 2 ^ e * X) * ((2 * (2 * c + 2 * m + e + 1) * B0 - 4 * B1 * (c + m)) * hI +
      2 * (2 * c + 2 * m + e + 1) * I * hB1 + 2 * I * hB2)
  · by_cases h2 : K = 2 * m
    · subst h2
      simp only [kumTerm, kumCert]
      rw [show 2 * m + 1 - 2 * m = 1 by omega, show 2 * m + 1 - m = m + 1 by omega, Nat.sub_self,
        show 2 * m - m = m by omega, show 2 * m + 1 - 2 * (m + 1) = 0 by omega,
        Nat.choose_eq_zero_of_lt (show 2 * m + 1 < 2 * (m + 1) by omega), Nat.choose_self,
        Nat.choose_succ_self_right, poch_succ_left (c + m) m, show c + (m : ℂ) + 1 = c + 1 + m by ring]
      have hm : (2 * (m : ℂ) + 1) ≠ 0 := by exact_mod_cast (show 2 * m + 1 ≠ 0 by omega)
      push_cast
      field_simp
      ring
    by_cases h3 : K + 1 = 2 * m
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      obtain rfl : K = 2 * j + 1 := by omega
      simp only [kumTerm, kumCert]
      rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, Nat.choose_self,
        Nat.choose_eq_zero_of_lt (show 2 * j + 1 < 2 * (j + 1) by omega),
        Nat.choose_eq_zero_of_lt (show 2 * (j + 1) < 2 * (j + 1 + 1) by omega), Nat.sub_self,
        show 2 * (j + 1) - (j + 1) = j + 1 by omega]
      have hm : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast (show j + 1 ≠ 0 by omega)
      have hm2 : (2 * (j : ℂ) + 1 + 1) ≠ 0 := by exact_mod_cast (show 2 * j + 1 + 1 ≠ 0 by omega)
      push_cast
      generalize (((2 * (j + 1))! : ℕ) / ((j + 1)! : ℕ) : ℂ) = q
      simp only [zero_mul, mul_zero, zero_div, sub_zero, neg_zero, zero_sub, one_mul, pow_zero,
        mul_one]
      rw [show (2 * (j : ℂ) + 1 + 1) = 2 * ((j : ℂ) + 1) by ring]
      field_simp
    · simp only [kumTerm, kumCert]
      rw [Nat.choose_eq_zero_of_lt (show K + 1 < 2 * m by omega),
        Nat.choose_eq_zero_of_lt (show K < 2 * m by omega),
        Nat.choose_eq_zero_of_lt (show K + 1 < 2 * (m + 1) by omega)]
      simp

/-- The coefficient identity behind `e^{2w} ₀F₁(;c;w²) = M(c-1/2, 2c-1, 4w)` in polynomial form:
`∑ₘ C(K,2m) (2m)!/m! 2^{K-2m} (c+m)_{K-m} = (2c+K-1)_K`, valid for every `c`. -/
theorem sum_range_kumTerm (c : ℂ) (K : ℕ) :
    ∑ m ∈ range (K + 1), kumTerm c K m = poch (2 * c + K - 1) K := by
  induction K generalizing c with
  | zero => simp [kumTerm, poch_zero]
  | succ K ih =>
    have h := Finset.sum_congr rfl fun m (_ : m ∈ range (K + 2)) => kumTerm_succ_sub c K m
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub, ← Finset.mul_sum,
      Finset.sum_range_succ (fun m => kumTerm (c + 1) K m) (K + 1), ih] at h
    have h0 : kumTerm (c + 1) K (K + 1) = 0 := by
      simp [kumTerm, Nat.choose_eq_zero_of_lt (show K < 2 * (K + 1) by omega)]
    have h1 : kumCert c K (K + 1 + 1) = 0 := by
      simp [kumCert, Nat.choose_eq_zero_of_lt (show K + 1 < 2 * (K + 1 + 1) by omega)]
    have h2 : kumCert c K 0 = 0 := by simp [kumCert]
    rw [h0, h1, h2, add_zero, sub_zero, sub_eq_zero] at h
    rw [show K + 1 + 1 = K + 2 by ring, h, poch_succ_left]
    push_cast
    rw [show 2 * (c + 1) + K - 1 = 2 * c + (K + 1) - 1 + 1 by ring,
      show 2 * c + K = 2 * c + (K + 1) - 1 by ring]

/-- `Γ(x+n) = Γ(x) (x)_n` away from the poles. -/
theorem Gamma_add_nat_eq_mul_poch {x : ℂ} (hx : ∀ i : ℕ, x + i ≠ 0) (n : ℕ) :
    Gamma (x + n) = Gamma x * poch x n := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ (hx n), ih, poch_succ]; ring

/-- Summing a summable family on `ℕ × ℕ` along the fibres of `(m, r) ↦ d m + r` (`d ≥ 1`). -/
theorem hasSum_sum_range_fiber {d : ℕ} (hd : 0 < d) {f : ℕ × ℕ → ℂ} {s : ℂ} (hf : HasSum f s) :
    HasSum (fun K => ∑ m ∈ range (K + 1), if d * m ≤ K then f (m, K - d * m) else 0) s := by
  set h : ℕ × ℕ → ℂ := fun p => if d * p.2 ≤ p.1 then f (p.2, p.1 - d * p.2) else 0 with hh
  set g : ℕ × ℕ → ℕ × ℕ := fun p => (d * p.1 + p.2, p.1) with hg
  have hginj : Function.Injective g := by
    intro p q hpq
    simp only [hg, Prod.mk.injEq] at hpq
    obtain ⟨h1, h2⟩ := hpq
    rw [h2] at h1
    exact Prod.ext h2 (by omega)
  have hhg : h ∘ g = f := by
    funext p
    simp [hh, hg]
  have hzero : ∀ x ∉ Set.range g, h x = 0 := by
    intro x hx
    simp only [hh]
    split_ifs with hc
    · exact absurd ⟨(x.2, x.1 - d * x.2), Prod.ext (by simp only [hg]; omega) rfl⟩ hx
    · rfl
  have hH : HasSum h s := by rw [← hginj.hasSum_iff hzero, hhg]; exact hf
  have hin : ∀ K : ℕ, HasSum (fun m => h (K, m)) (∑ m ∈ range (K + 1), h (K, m)) := fun K =>
    hasSum_sum_of_ne_finset_zero fun m hm => by
      simp only [Finset.mem_range, not_lt] at hm
      have : m ≤ d * m := Nat.le_mul_of_pos_left m hd
      simp only [hh]
      split_ifs with hc
      · omega
      · rfl
  exact hH.prod_fiberwise hin

/-- Power series of `₀F̃₁(;c;w²) e^{2w}`: the coefficients are `(2c+K-1)_K / (K! Γ(c+K))`
(the regularized form of `M(c-1/2, 2c-1, 4w)`, DLMF 13.6.9), valid for every `c ∉ -ℕ`. -/
theorem hasSum_regularized0F1_mul_exp {c : ℂ} (hc : ∀ j : ℕ, c + j ≠ 0) (w : ℂ) :
    HasSum (fun K : ℕ => poch (2 * c + K - 1) K / (K ! * Gamma (c + K)) * w ^ K)
      (regularizedHGFun (∅ : Multiset ℂ) {c} (w ^ 2) * exp (2 * w)) := by
  have h1 : HasSum (fun m => regularizedHGFunCoeff (∅ : Multiset ℂ) {c} m * (w ^ 2) ^ m)
      (regularizedHGFun (∅ : Multiset ℂ) {c} (w ^ 2)) :=
    (hasFPowerSeriesOnBall_regularized0F1 c).hasSum_mul_pow (by simp)
  have h2 : HasSum (fun r => (2 * w) ^ r / r !) (exp (2 * w)) := by
    simpa [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (2 * w)
  obtain ⟨C, hC0, hC⟩ := exists_norm_regularized0F1Coeff_le (c - 1)
  have hs1 : Summable fun m => ‖regularizedHGFunCoeff (∅ : Multiset ℂ) {c} m * (w ^ 2) ^ m‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      ((Real.summable_pow_div_factorial (2 * ‖w‖ ^ 2)).mul_left C)
    have := hC 0 m
    simp only [Nat.cast_zero, add_zero, sub_add_cancel, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, mul_one] at this
    rw [norm_mul, norm_pow, norm_pow]
    calc ‖regularizedHGFunCoeff (∅ : Multiset ℂ) {c} m‖ * (‖w‖ ^ 2) ^ m
        ≤ C * (2 ^ m / m !) * (‖w‖ ^ 2) ^ m := by gcongr
      _ = C * ((2 * ‖w‖ ^ 2) ^ m / m !) := by rw [mul_pow]; ring
  have hs2 : Summable fun r : ℕ => ‖(2 * w) ^ r / (r ! : ℂ)‖ := by
    simpa [norm_div, norm_pow] using Real.summable_pow_div_factorial ‖2 * w‖
  have hprod := h1.mul h2 (summable_mul_of_summable_norm (f := fun m =>
    regularizedHGFunCoeff (∅ : Multiset ℂ) {c} m * (w ^ 2) ^ m) (g := fun r : ℕ => (2 * w) ^ r / (r ! : ℂ)) hs1 hs2)
  have hfib := hasSum_sum_range_fiber (d := 2) two_pos hprod
  refine hfib.congr_fun ?_
  intro K
  rw [← sum_range_kumTerm c K, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs with h2m
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h2m
    have hcm : ∀ i : ℕ, c + m + i ≠ 0 := fun i => by
      rw [add_assoc, ← Nat.cast_add]; exact hc _
    have hG := Gamma_add_nat_eq_mul_poch hcm (m + r)
    rw [show c + (m : ℂ) + ((m + r : ℕ) : ℂ) = c + ((2 * m + r : ℕ) : ℂ) by push_cast; ring] at hG
    have hΓm : Gamma (c + m) ≠ 0 := by
      have := Gamma_add_nat_ne_zero_of_ne (l := c) (fun n h => hc n (by rw [h]; ring)) m
      exact this
    have hΓK : Gamma (c + ((2 * m + r : ℕ) : ℂ)) ≠ 0 :=
      Gamma_add_nat_ne_zero_of_ne (l := c) (fun n h => hc n (by rw [h]; ring)) _
    have hP : poch (c + m) (m + r) ≠ 0 := by
      intro h; rw [h, mul_zero] at hG; exact hΓK hG
    have hfac := Nat.choose_mul_factorial_mul_factorial (show 2 * m ≤ 2 * m + r by omega)
    rw [show 2 * m + r - 2 * m = r by omega] at hfac
    have hfac' : ((2 * m + r).choose (2 * m) : ℂ) * (2 * m)! * r ! = (2 * m + r)! := by
      exact_mod_cast hfac
    simp only [kumTerm, regularizedHGFunCoeff_empty]
    rw [hG, show 2 * m + r - 2 * m = r by omega, show 2 * m + r - m = m + r by omega]
    have hm0 : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hr0 : (r ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hK0 : ((2 * m + r)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hch : ((2 * m + r).choose (2 * m) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
    have h2m0 : ((2 * m)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [← hfac']
    field_simp
    ring
  · simp [kumTerm, Nat.choose_eq_zero_of_lt (show K < 2 * m by omega)]

/-- `‖(x)_K‖ ≤ (‖x‖ + K)^K`. -/
theorem norm_poch_le_pow (x : ℂ) (K : ℕ) : ‖poch x K‖ ≤ (‖x‖ + K) ^ K := by
  induction K with
  | zero => simp [poch_zero]
  | succ K ih =>
    rw [poch_succ, norm_mul, pow_succ]
    have h1 : ‖x + K‖ ≤ ‖x‖ + (K + 1 : ℕ) := by
      calc ‖x + K‖ ≤ ‖x‖ + ‖(K : ℂ)‖ := norm_add_le _ _
        _ ≤ ‖x‖ + (K + 1 : ℕ) := by simp
    have h2 : (‖x‖ + K) ^ K ≤ (‖x‖ + (K + 1 : ℕ)) ^ K :=
      pow_le_pow_left₀ (by positivity) (by push_cast; linarith) K
    exact mul_le_mul (ih.trans h2) h1 (norm_nonneg _) (by positivity)

/-- `‖(x)_K‖ ≤ K! e^{‖x‖+K}`. -/
theorem norm_poch_le_factorial_mul_exp (x : ℂ) (K : ℕ) :
    ‖poch x K‖ ≤ K ! * Real.exp (‖x‖ + K) := by
  have h := Real.pow_div_factorial_le_exp (‖x‖ + K) (by positivity) K
  have hK : (0 : ℝ) < K ! := by exact_mod_cast Nat.factorial_pos K
  rw [div_le_iff₀ hK] at h
  linarith [norm_poch_le_pow x K]

/-- Odd duplication: `(2ν)_{2N+1} = 2·4^N (ν)_{N+1} (ν+1/2)_N`. -/
theorem poch_two_mul_two_mul_add_one (ν : ℂ) (N : ℕ) :
    poch (2 * ν) (2 * N + 1) = 2 * 4 ^ N * poch ν (N + 1) * poch (ν + 1 / 2) N := by
  induction N with
  | zero => simp [poch_one, poch_zero]
  | succ N ih =>
    rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 by ring, poch_succ, poch_succ, ih,
      poch_succ ν (N + 1), poch_succ (ν + 1 / 2) N, pow_succ]
    push_cast
    ring

/-- Uniform bound on the coefficients of `₀F̃₁(;ν+k+1;w²) e^{2w}` (`hasSum_regularized0F1_mul_exp`). -/
theorem exists_norm_regularized0F1_mul_exp_coeff_le (ν : ℂ) :
    ∃ C X : ℝ, 0 ≤ C ∧ 1 ≤ X ∧ ∀ k K : ℕ,
      ‖poch (2 * (ν + k + 1) + K - 1) K / (K ! * Gamma (ν + k + 1 + K))‖ ≤
        C * (X ^ (k + K) / (k + K)!) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_recip_Gamma_add_nat_le (ν + 1)
  refine ⟨C * Real.exp ‖2 * ν + 1‖, 2 * Real.exp 1 ^ 2, by positivity, ?_, fun k K => ?_⟩
  · nlinarith [Real.add_one_le_exp 1, pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      (by linarith [Real.add_one_le_exp 1] : (2 : ℝ) ≤ Real.exp 1) 2]
  have hK : (0 : ℝ) < K ! := by exact_mod_cast Nat.factorial_pos K
  have hx : ‖2 * (ν + k + 1) + K - 1‖ ≤ ‖2 * ν + 1‖ + 2 * k + K := by
    rw [show 2 * (ν + k + 1) + (K : ℂ) - 1 = (2 * ν + 1) + ((2 * k + K : ℕ) : ℂ) by push_cast; ring]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [Complex.norm_natCast]; push_cast; ring
  have h1 := norm_poch_le_factorial_mul_exp (2 * (ν + k + 1) + K - 1) K
  have h2 := hC (k + K)
  rw [show ν + 1 + ((k + K : ℕ) : ℂ) = ν + k + 1 + K by push_cast; ring] at h2
  rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul, norm_inv (K ! : ℂ), Complex.norm_natCast]
  calc ‖poch (2 * (ν + k + 1) + K - 1) K‖ * ((K ! : ℝ)⁻¹ * ‖(Gamma (ν + k + 1 + K))⁻¹‖)
      ≤ (K ! * Real.exp (‖2 * ν + 1‖ + 2 * k + K + K)) *
          ((K ! : ℝ)⁻¹ * (C * (2 ^ (k + K) / (k + K)!))) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = _ := by
        have e1 : Real.exp (‖2 * ν + 1‖ + 2 * k + K + K) =
            Real.exp ‖2 * ν + 1‖ * (Real.exp 1 ^ 2) ^ (k + K) := by
          rw [← pow_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
        rw [e1, mul_pow]
        field_simp

/-- Coefficient of `w^N` in a Neumann series with `eₖ = k`:
`∑_{k+2m=N} aₖ σ^m / (m! Γ(ν+nₖ+m+1))`. -/
noncomputable def neumannLinCoeff (ν σ : ℂ) (a : ℕ → ℂ) (n : ℕ → ℕ) (N : ℕ) : ℂ :=
  ∑ m ∈ range (N + 1), if 2 * m ≤ N then a (N - 2 * m) * σ ^ m *
    regularizedHGFunCoeff (∅ : Multiset ℂ) {ν + n (N - 2 * m) + 1} m else 0

/-- **Neumann series as a power series** (`eₖ = k`, all integer order shifts). -/
theorem hasSum_neumannLinCoeff (ν σ w : ℂ) (a : ℕ → ℂ) (n : ℕ → ℕ)
    (ha : Summable fun k => ‖a k‖ * ‖w‖ ^ k * (2 ^ n k / (n k)!)) :
    HasSum (fun N => neumannLinCoeff ν σ a n N * w ^ N)
      (∑' p, neumannTerm ν σ w a n (fun k => k) p) := by
  have hT := (summable_norm_neumannTerm ν σ w a n (fun k => k) ha).of_norm.hasSum
  rw [← (Equiv.prodComm ℕ ℕ).hasSum_iff] at hT
  refine (hasSum_sum_range_fiber (d := 2) two_pos hT).congr_fun fun N => ?_
  rw [neumannLinCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs with hm
  · simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, neumannTerm]
    rw [show w ^ N = w ^ (N - 2 * m) * (w ^ 2) ^ m by
      rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hm], mul_pow]
    ring
  · simp

/-- Neumann series with `eₖ = k` summed as a power series. -/
theorem hasSum_neumann_linear_tsum (ν σ w : ℂ) (a : ℕ → ℂ) (n : ℕ → ℕ)
    (ha : Summable fun k => ‖a k‖ * ‖w‖ ^ k * (2 ^ n k / (n k)!)) :
    HasSum (fun k => a k * w ^ k * regularizedHGFun (∅ : Multiset ℂ) {ν + n k + 1} (σ * w ^ 2))
      (∑' N, neumannLinCoeff ν σ a n N * w ^ N) := by
  rw [(hasSum_neumannLinCoeff ν σ w a n ha).tsum_eq]
  exact hasSum_neumann ν σ w a n (fun k => k) ha

/-- **Neumann series `∑ₖ aₖ (z/2)^{pₖ} J_{ν+nₖ}(z)` with `pₖ + nₖ = k`** (orders of both
parities) as a power series in `z/2`. -/
theorem hasSum_besselJ_neumann_linear {z : ℂ} (hz : z ≠ 0) (ν : ℂ) (a : ℕ → ℂ) (p n : ℕ → ℕ)
    (hpn : ∀ k, p k + n k = k)
    (ha : Summable fun k => ‖a k‖ * ‖z / 2‖ ^ k * (2 ^ n k / (n k)!)) :
    HasSum (fun k => a k * (z / 2) ^ p k * besselJ (ν + n k) z)
      ((z / 2) ^ ν * ∑' N, neumannLinCoeff ν (-1) a n N * (z / 2) ^ N) := by
  refine ((hasSum_neumann_linear_tsum ν (-1) (z / 2) a n ha).mul_left ((z / 2) ^ ν)).congr_fun
    fun k => ?_
  rw [besselJ_add_nat hz]
  rw [show (z / 2) ^ k = (z / 2) ^ p k * (z / 2) ^ n k by rw [← pow_add, hpn k]]
  ring

/-- The modified-Bessel analogue of `hasSum_besselJ_neumann_linear`. -/
theorem hasSum_besselI_neumann_linear {z : ℂ} (hz : z ≠ 0) (ν : ℂ) (a : ℕ → ℂ) (p n : ℕ → ℕ)
    (hpn : ∀ k, p k + n k = k)
    (ha : Summable fun k => ‖a k‖ * ‖z / 2‖ ^ k * (2 ^ n k / (n k)!)) :
    HasSum (fun k => a k * (z / 2) ^ p k * besselI (ν + n k) z)
      ((z / 2) ^ ν * ∑' N, neumannLinCoeff ν 1 a n N * (z / 2) ^ N) := by
  refine ((hasSum_neumann_linear_tsum ν 1 (z / 2) a n ha).mul_left ((z / 2) ^ ν)).congr_fun
    fun k => ?_
  rw [besselI_add_nat hz]
  rw [show (z / 2) ^ k = (z / 2) ^ p k * (z / 2) ^ n k by rw [← pow_add, hpn k]]
  ring

end LinearNeumann

end DLMF.Bessel
