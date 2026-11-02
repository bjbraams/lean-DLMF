/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.NumberTheory.PrimeNumberTheorem
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Sum
public import Mathlib.Algebra.Order.Floor.Semifield

/-!
# The Möbius partial sums (DLMF 27.11.13, 27.11.14)

This file proves `M(N) = ∑_{n ≤ N} μ(n) = o(N)` from the prime number theorem `ψ(x) ~ x`, by
the classical argument of Landau: the identity `μ log = -(Λ * μ)` gives
`∑_{n ≤ N} μ(n) log n = -∑_{d ≤ N} μ(d) ψ(N/d)`; writing `ψ(N/d) = ⌊N/d⌋ + R(N/d)` with
`R(y) = o(y)` and using `∑_{d ≤ N} μ(d) ⌊N/d⌋ = 1` shows that this sum is `o(N log N)`, and
`∑_{n ≤ N} μ(n) log(N/n) = O(N)`.

Landau's deduction then gives `∑_{n ≤ L} μ(n)/n → 0`: splitting `1 = ∑_{n ≤ N} μ(n) ⌊N/n⌋` at
`n = N/K`, the head is `N ∑_{n ≤ N/K} μ(n)/n + O(N/K)` and the tail is a combination of `K`
blocks of `M`, each `o(N)`.

## Main results

* `isLittleO_sum_moebius`: `∑_{n ≤ N} μ(n) = o(N)` as `N → ∞` (DLMF 27.11.13).
* `tendsto_sum_moebius_div_self_nat`: `∑_{n ≤ L} μ(n)/n → 0` (DLMF 27.11.14).

## Implementation notes

`ψ(x) ~ x` is `Chebyshev.psi_isEquivalent` from `DLMFMathlib.NumberTheory.PrimeNumberTheorem`,
which derives it from TauCeti's prime ideal theorem for `ℚ` (`TauCeti.primeIdealTheorem`).
-/

@[expose] public noncomputable section

open Filter Asymptotics Finset ArithmeticFunction Chebyshev IsDedekindDomain
open scoped NumberField ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace DLMF.NumberTheory

/-- `∑_{n ≤ N} μ(n) log n = -∑_{d ≤ N} μ(d) ψ(N/d)`. -/
private lemma sum_moebius_mul_log_eq_neg_sum_psi (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (μ n : ℝ) * Real.log n =
      -∑ d ∈ Ioc 0 N, (μ d : ℝ) * ψ ((N / d : ℕ) : ℝ) := by
  set f : ArithmeticFunction ℝ := (μ : ArithmeticFunction ℝ).pmul log with hf
  have hfz : f * (ζ : ArithmeticFunction ℝ) = -Λ := by
    ext n
    rw [coe_mul_zeta_apply, hf]
    simp only [pmul_apply, intCoe_apply, log_apply, ArithmeticFunction.neg_apply]
    exact ArithmeticFunction.sum_moebius_mul_log_eq
  have hf' : f = -(Λ * (μ : ArithmeticFunction ℝ)) := by
    calc f = f * ((ζ : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ)) := by
          rw [coe_zeta_mul_coe_moebius, mul_one]
      _ = (-Λ) * (μ : ArithmeticFunction ℝ) := by rw [← mul_assoc, hfz]
      _ = -(Λ * (μ : ArithmeticFunction ℝ)) := neg_mul Λ (μ : ArithmeticFunction ℝ)
  have h1 : ∀ n, (μ n : ℝ) * Real.log n = f n := fun n => by
    simp [hf, pmul_apply, log_apply]
  simp_rw [h1, hf', ArithmeticFunction.neg_apply, sum_neg_distrib, mul_comm Λ,
    sum_Ioc_mul_eq_sum_sum]
  congr 1
  refine sum_congr rfl fun d _ => ?_
  rw [psi, Nat.floor_natCast]
  simp

/-- `∑_{d ≤ N} μ(d) ⌊N/d⌋ = 1` for `N ≥ 1`. -/
private lemma sum_moebius_mul_div (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Ioc 0 N, (μ d : ℝ) * ((N / d : ℕ) : ℝ) = 1 := by
  have h := sum_Ioc_mul_zeta_eq_sum (μ : ArithmeticFunction ℝ) N
  rw [coe_moebius_mul_coe_zeta] at h
  rw [← sum_congr rfl fun d _ => by rw [← intCoe_apply (R := ℝ)], ← h]
  rw [sum_eq_single 1]
  · simp
  · intro b _ hb; simp [one_apply, hb]
  · intro h1; exact absurd (mem_Ioc.mpr ⟨one_pos, hN⟩) h1

/-- `∑_{n ≤ N} log(N/n) ≤ N`. -/
private lemma sum_log_sub_le (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (Real.log N - Real.log n) ≤ N := by
  rw [sum_sub_distrib, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  have := Real.le_sum_log_nat N
  linarith

/-- `|ψ(k) - k| ≤ εk + C` for all `k`, from `ψ(x) - x = o(x)`. -/
private lemma exists_abs_psi_sub_le (hR : (fun k : ℕ => ψ k - k) =o[atTop] fun k => (k : ℝ))
    {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, |ψ k - k| ≤ ε * k + C := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hR.def hε)
  refine ⟨∑ k ∈ range K, |ψ k - k|, sum_nonneg fun _ _ => abs_nonneg _, fun k => ?_⟩
  by_cases hk : K ≤ k
  · have := hK k hk
    simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k)] at this
    linarith [sum_nonneg fun j (_ : j ∈ range K) => abs_nonneg (ψ j - j)]
  · have h1 : |ψ k - k| ≤ ∑ j ∈ range K, |ψ j - j| :=
      single_le_sum (f := fun j : ℕ => |ψ j - j|) (fun _ _ => abs_nonneg _)
        (mem_range.mpr (by omega))
    have : 0 ≤ ε * k := by positivity
    linarith

/-- The Möbius partial sums are `o(N)`, given `ψ(x) - x = o(x)` on the integers. -/
private lemma isLittleO_sum_moebius_of_psi
    (hR : (fun k : ℕ => ψ k - k) =o[atTop] fun k => (k : ℝ)) :
    (fun N : ℕ => ∑ n ∈ Ioc 0 N, (μ n : ℝ)) =o[atTop] fun N => (N : ℝ) := by
  refine isLittleO_iff.mpr fun c hc => ?_
  set ε := c / 6 with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨C, hC0, hC⟩ := exists_abs_psi_sub_le hR hε
  have hlog : ∀ᶠ N : ℕ in atTop, max 1 ((C + 2) / ε) ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hlog, eventually_ge_atTop 1] with N hN hN1
  have hL1 : 1 ≤ Real.log N := le_trans (le_max_left _ _) hN
  have hL2 : (C + 2) / ε ≤ Real.log N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  set M := ∑ n ∈ Ioc 0 N, (μ n : ℝ) with hM
  set S := ∑ d ∈ Ioc 0 N, (μ d : ℝ) * (ψ ((N / d : ℕ) : ℝ) - ((N / d : ℕ) : ℝ)) with hS
  -- the main identity `M log N = -1 - S + T`
  have hid : M * Real.log N = -1 - S + ∑ n ∈ Ioc 0 N, (μ n : ℝ) * (Real.log N - Real.log n) := by
    have h1 := sum_moebius_mul_log_eq_neg_sum_psi N
    have h2 := sum_moebius_mul_div N hN1
    have e1 : M * Real.log N = ∑ n ∈ Ioc 0 N, (μ n : ℝ) * Real.log n +
        ∑ n ∈ Ioc 0 N, (μ n : ℝ) * (Real.log N - Real.log n) := by
      rw [hM, sum_mul, ← sum_add_distrib]
      exact sum_congr rfl fun n _ => by ring
    have e2 : ∑ d ∈ Ioc 0 N, (μ d : ℝ) * ψ ((N / d : ℕ) : ℝ) =
        ∑ d ∈ Ioc 0 N, (μ d : ℝ) * ((N / d : ℕ) : ℝ) + S := by
      rw [hS, ← sum_add_distrib]
      exact sum_congr rfl fun n _ => by ring
    linarith
  have hT : |∑ n ∈ Ioc 0 N, (μ n : ℝ) * (Real.log N - Real.log n)| ≤ N := by
    refine (abs_sum_le_sum_abs _ _).trans (le_trans (sum_le_sum fun n hn => ?_) (sum_log_sub_le N))
    rw [abs_mul]
    have hμ : |(μ n : ℝ)| ≤ 1 := by
      have := abs_moebius_le_one (n := n); exact_mod_cast this
    have hn := mem_Ioc.mp hn
    have hle : Real.log n ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2)
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    exact mul_le_of_le_one_left (sub_nonneg.mpr hle) hμ
  have hSb : |S| ≤ ε * (N * (1 + Real.log N)) + C * N := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ d ∈ Ioc 0 N, |(μ d : ℝ) * (ψ ((N / d : ℕ) : ℝ) - ((N / d : ℕ) : ℝ))|
        ≤ ∑ d ∈ Ioc 0 N, (ε * ((N : ℝ) / d) + C) := by
          refine sum_le_sum fun d hd => ?_
          rw [abs_mul]
          have hμ : |(μ d : ℝ)| ≤ 1 := by
            have := abs_moebius_le_one (n := d); exact_mod_cast this
          have h1 := hC (N / d)
          have h2 : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
          have h3 : 0 ≤ |ψ ((N / d : ℕ) : ℝ) - ((N / d : ℕ) : ℝ)| := abs_nonneg _
          nlinarith [abs_nonneg (μ d : ℝ)]
      _ = ε * (N * harmonic N) + C * N := by
          have hI : Icc 1 N = Ioc 0 N := by ext; simp only [mem_Icc, mem_Ioc]; omega
          rw [sum_add_distrib, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul,
            harmonic_eq_sum_Icc, hI, ← mul_sum]
          push_cast
          simp only [div_eq_mul_inv]
          rw [← mul_sum]
          ring
      _ ≤ _ := by
          have := harmonic_le_one_add_log N
          gcongr
  have hL2' : C + 2 ≤ ε * Real.log N := by rwa [div_le_iff₀ hε, mul_comm] at hL2
  have hMa : |M| * Real.log N ≤ 1 + |S| + N := by
    rw [show |M| * Real.log N = |M * Real.log N| by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.log N)], hid]
    have := abs_add_le (-1 - S) (∑ n ∈ Ioc 0 N, (μ n : ℝ) * (Real.log N - Real.log n))
    have h2 := abs_sub (-1) S
    rw [abs_neg, abs_one] at h2
    linarith
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hkey : |M| * Real.log N ≤ (c * N) * Real.log N := by
    have h3 : ε * N ≤ ε * N * Real.log N := le_mul_of_one_le_right (by positivity) hL1
    have h4 : 1 + N + C * N ≤ ε * N * Real.log N := by nlinarith
    have h5 : ε * (N * (1 + Real.log N)) = ε * N + ε * N * Real.log N := by ring
    have h6 : c * N * Real.log N = 6 * (ε * N * Real.log N) := by rw [hεdef]; ring
    have h7 : 0 ≤ ε * N * Real.log N := by positivity
    linarith
  have := le_of_mul_le_mul_right hkey (by linarith)
  simpa [Real.norm_eq_abs, abs_of_pos hNpos] using this

/-- `ψ(x) - x = o(x)` (the prime number theorem for `ψ`, from TauCeti's prime ideal theorem). -/
private lemma psi_sub_isLittleO : (fun x : ℝ => ψ x - x) =o[atTop] fun x => x :=
  Chebyshev.psi_isEquivalent.isLittleO

/-- DLMF 27.11.13 on the integers: `∑_{n ≤ N} μ(n) = o(N)`. -/
theorem isLittleO_sum_moebius :
    (fun N : ℕ => ∑ n ∈ Ioc 0 N, (μ n : ℝ)) =o[atTop] fun N => (N : ℝ) :=
  isLittleO_sum_moebius_of_psi (psi_sub_isLittleO.comp_tendsto tendsto_natCast_atTop_atTop)

/-- A block sum of `μ` is bounded by twice a bound for the partial sums. -/
private lemma abs_sum_Ioc_moebius_le {N : ℕ} {B : ℝ}
    (hB : ∀ y ≤ N, |∑ n ∈ Ioc 0 y, (μ n : ℝ)| ≤ B) {a b : ℕ} (hb : b ≤ N) :
    |∑ n ∈ Ioc a b, (μ n : ℝ)| ≤ 2 * B := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 (Nat.zero_le _))
  rcases le_or_gt b a with hab | hab
  · rw [Ioc_eq_empty_of_le hab]; simp; linarith
  · have h := sum_Ioc_consecutive (fun n => (μ n : ℝ)) (Nat.zero_le a) hab.le
    have e : ∑ n ∈ Ioc a b, (μ n : ℝ) = ∑ n ∈ Ioc 0 b, (μ n : ℝ) - ∑ n ∈ Ioc 0 a, (μ n : ℝ) := by
      linarith
    rw [e]
    have h1 := hB b hb
    have h2 := hB a (by omega)
    calc _ ≤ |∑ n ∈ Ioc 0 b, (μ n : ℝ)| + |∑ n ∈ Ioc 0 a, (μ n : ℝ)| := abs_sub _ _
      _ ≤ _ := by linarith

/-- The tail `∑_{N/K < n ≤ N} μ(n) ⌊N/n⌋` as a sum of `K` Möbius blocks. -/
private lemma sum_Ioc_moebius_mul_div_eq (N K : ℕ) (hK : 1 ≤ K) :
    ∑ n ∈ Ioc (N / K) N, (μ n : ℝ) * ((N / n : ℕ) : ℝ) =
      ∑ j ∈ Ioc 0 K, ∑ n ∈ Ioc (N / K) (N / j), (μ n : ℝ) := by
  have hcount : ∀ n ∈ Ioc (N / K) N, ((N / n : ℕ) : ℝ) =
      ∑ j ∈ Ioc 0 K, if j ≤ N / n then (1 : ℝ) else 0 := by
    intro n hn
    rw [mem_Ioc] at hn
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn.1
    have hlt : N / n < K := by
      rw [Nat.div_lt_iff_lt_mul hn0]
      have := (Nat.div_lt_iff_lt_mul (by omega : 0 < K)).mp hn.1
      linarith [mul_comm n K]
    rw [sum_boole]
    congr 1
    rw [show (Ioc 0 K).filter (fun j => j ≤ N / n) = Ioc 0 (N / n) by
      ext j; simp only [mem_filter, mem_Ioc]; omega]
    simp
  rw [sum_congr rfl fun n hn => by rw [hcount n hn, mul_sum], sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_Ioc] at hj
  simp only [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) h1
    exact ⟨h1, (Nat.le_div_iff_mul_le hj.1).mpr (by
      have := (Nat.le_div_iff_mul_le hn0).mp h3; linarith [mul_comm j n])⟩
  · rintro ⟨h1, h2⟩
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) h1
    have hjn : n * j ≤ N := (Nat.le_div_iff_mul_le hj.1).mp h2
    refine ⟨⟨h1, ?_⟩, (Nat.le_div_iff_mul_le hn0).mpr (by linarith [mul_comm j n])⟩
    exact le_trans h2 (Nat.div_le_self _ _)

/-- `|∑_{n ≤ y} μ(n)| ≤ y`. -/
private lemma abs_sum_moebius_le_card (y : ℕ) : |∑ n ∈ Ioc 0 y, (μ n : ℝ)| ≤ y := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ n ∈ Ioc 0 y, |(μ n : ℝ)| ≤ ∑ n ∈ Ioc 0 y, (1 : ℝ) :=
        sum_le_sum fun n _ => by exact_mod_cast abs_moebius_le_one (n := n)
    _ = y := by simp

/-- `∑_{n ≤ L} μ(n)/n → 0`, given `∑_{n ≤ N} μ(n) = o(N)` (Landau). -/
private lemma tendsto_sum_moebius_div_self_of
    (hM : (fun N : ℕ => ∑ n ∈ Ioc 0 N, (μ n : ℝ)) =o[atTop] fun N => (N : ℝ)) :
    Tendsto (fun L : ℕ => ∑ n ∈ Ioc 0 L, (μ n : ℝ) / n) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 3 / ε < K := exists_nat_gt _
  have hKpos : (0 : ℝ) < K := lt_trans (by positivity) hK
  have hK1 : 1 ≤ K := by exact_mod_cast hKpos
  set δ := ε / (6 * K) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (hM.def hδpos)
  have hB : ∀ y : ℕ, |∑ n ∈ Ioc 0 y, (μ n : ℝ)| ≤ δ * y + N0 := by
    intro y
    rcases le_or_gt N0 y with hy | hy
    · have := hN0 y hy
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (Nat.cast_nonneg _)] at this
      linarith [(Nat.cast_nonneg N0 : (0 : ℝ) ≤ N0)]
    · have h1 := abs_sum_moebius_le_card y
      have h2 : (y : ℝ) ≤ N0 := by exact_mod_cast hy.le
      have : 0 ≤ δ * y := by positivity
      linarith
  obtain ⟨L0, hL0⟩ : ∃ L0 : ℕ, 3 * (1 + 2 * N0) / ε < L0 := exists_nat_gt _
  refine ⟨max 1 L0, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hLL0 : (L0 : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  set N := L * K with hN
  have hNK : N / K = L := by rw [hN, Nat.mul_div_cancel _ (by omega)]
  have hNpos : (0 : ℝ) < N := by rw [hN]; push_cast; positivity
  have hLN : L ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_right _ (by omega)
  -- the identity `1 = A + B`
  have hsplit := sum_Ioc_consecutive (fun n => (μ n : ℝ) * ((N / n : ℕ) : ℝ)) (Nat.zero_le L) hLN
  rw [sum_moebius_mul_div N (by omega), ← hNK, sum_Ioc_moebius_mul_div_eq N K hK1, hNK] at hsplit
  -- bound on the tail
  have hBN : ∀ y ≤ N, |∑ n ∈ Ioc 0 y, (μ n : ℝ)| ≤ δ * N + N0 := fun y hy =>
    (hB y).trans (by gcongr)
  have htail : |∑ j ∈ Ioc 0 K, ∑ n ∈ Ioc L (N / j), (μ n : ℝ)| ≤ K * (2 * (δ * N + N0)) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Ioc 0 K, |∑ n ∈ Ioc L (N / j), (μ n : ℝ)|
        ≤ ∑ j ∈ Ioc 0 K, 2 * (δ * N + N0) :=
          sum_le_sum fun j _ => abs_sum_Ioc_moebius_le hBN (Nat.div_le_self _ _)
      _ = _ := by simp
  -- the head is `N m(L)` up to `L`
  have hhead : |∑ n ∈ Ioc 0 L, (μ n : ℝ) * ((N / n : ℕ) : ℝ) -
      N * ∑ n ∈ Ioc 0 L, (μ n : ℝ) / n| ≤ L := by
    rw [mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ n ∈ Ioc 0 L, |(μ n : ℝ) * ((N / n : ℕ) : ℝ) - N * ((μ n : ℝ) / n)|
        ≤ ∑ n ∈ Ioc 0 L, (1 : ℝ) := by
          refine sum_le_sum fun n hn => ?_
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
          rw [show (μ n : ℝ) * ((N / n : ℕ) : ℝ) - N * ((μ n : ℝ) / n) =
              (μ n : ℝ) * (((N / n : ℕ) : ℝ) - N / n) by ring, abs_mul]
          have hμ : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := n)
          have h1 : ((N / n : ℕ) : ℝ) ≤ N / n := Nat.cast_div_le
          have h2 : (N : ℝ) / n - 1 < ((N / n : ℕ) : ℝ) := by
            rw [← Nat.floor_div_eq_div (K := ℝ)]
            exact Nat.sub_one_lt_floor _
          have h3 : |((N / n : ℕ) : ℝ) - N / n| ≤ 1 := by
            rw [abs_le]; constructor <;> linarith
          calc |(μ n : ℝ)| * |((N / n : ℕ) : ℝ) - N / n| ≤ 1 * 1 := by
                gcongr
            _ = 1 := one_mul 1
      _ = L := by simp
  set m := ∑ n ∈ Ioc 0 L, (μ n : ℝ) / n with hm
  have hNm : |N * m| ≤ 1 + L + K * (2 * (δ * N + N0)) := by
    have := abs_sub_abs_le_abs_sub (N * m)
      (∑ n ∈ Ioc 0 L, (μ n : ℝ) * ((N / n : ℕ) : ℝ))
    rw [abs_sub_comm] at this
    have e : ∑ n ∈ Ioc 0 L, (μ n : ℝ) * ((N / n : ℕ) : ℝ) =
        1 - ∑ j ∈ Ioc 0 K, ∑ n ∈ Ioc L (N / j), (μ n : ℝ) := by linarith
    have h4 : |∑ n ∈ Ioc 0 L, (μ n : ℝ) * ((N / n : ℕ) : ℝ)| ≤
        1 + K * (2 * (δ * N + N0)) := by
      rw [e]
      have := abs_sub (1 : ℝ) (∑ j ∈ Ioc 0 K, ∑ n ∈ Ioc L (N / j), (μ n : ℝ))
      rw [abs_one] at this
      linarith
    linarith
  rw [dist_zero_right, Real.norm_eq_abs]
  rw [abs_mul, abs_of_pos hNpos] at hNm
  have hNLK : (N : ℝ) = L * K := by rw [hN]; push_cast; ring
  have hm' : |m| ≤ (1 + L + K * (2 * (δ * N + N0))) / N := by
    rw [le_div_iff₀ hNpos, mul_comm]; exact hNm
  have e1 : (1 + L + K * (2 * (δ * N + N0))) / N =
      1 / N + 1 / K + 2 * K * δ + 2 * N0 / L := by
    rw [hNLK]; field_simp; ring
  have e2 : 2 * K * δ = ε / 3 := by rw [hδ]; field_simp; ring
  have e3 : 1 / (K : ℝ) < ε / 3 := by
    rw [div_lt_iff₀ hKpos]; rw [div_lt_iff₀ hε] at hK; linarith
  have e4 : 1 / (N : ℝ) ≤ 1 / L := by
    gcongr
  have e5 : (1 + 2 * N0) / (L : ℝ) < ε / 3 := by
    rw [div_lt_iff₀ hLpos]; rw [div_lt_iff₀ hε] at hL0; nlinarith
  have e6 : 1 / (L : ℝ) + 2 * N0 / L = (1 + 2 * N0) / L := by ring
  linarith

/-- DLMF 27.11.14 on the integers: `∑_{n ≤ L} μ(n)/n → 0`. -/
theorem tendsto_sum_moebius_div_self_nat :
    Tendsto (fun L : ℕ => ∑ n ∈ Ioc 0 L, (μ n : ℝ) / n) atTop (nhds 0) :=
  tendsto_sum_moebius_div_self_of isLittleO_sum_moebius

end DLMF.NumberTheory
