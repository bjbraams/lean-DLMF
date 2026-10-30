/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.NumberTheory.Functions
public import DLMF.NumberTheory.T27bHecke
public import DLMF.Partitions
public import DLMF.Weierstrass.ModularFunctions
public import DLMFMathlib.RingTheory.PowerSeriesEvaluation
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
public import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
public import TauCeti.NumberTheory.ModularForms.LevelOne.DiscriminantEigenform

/-!
# Unrestricted partitions (DLMF §27.14)

`p(n)` is the project's `DLMF.Partitions.partitionFunction n = Fintype.card (Nat.Partition n)`
(27.14.1) and `p_k(n)` is `partitionsAtMost k n`. Euler's reciprocal function
`f(x) = ∏_{m≥1} (1 - xᵐ)` (27.14.2) is `eulerReciprocal x`; it equals `(x; x)_∞`
(`DLMF.QSeries.qPochhammerInf x x`) for every `x` and Mathlib's `eulerFunction x` for `|x| < 1`.
The pentagonal numbers `ω(±k) = (3k² ∓ k)/2` (27.14.5) are Mathlib's `pentagonal (±k)`.

The Dedekind sum `s(h, k)` (27.14.11) is `DLMF.Weierstrass.dedekindSum h k` (DLMF 23.18.7, the
same formula) and `η(τ)` (27.14.12) is Mathlib's `ModularForm.eta`. DLMF's discriminant
`Δ(τ) = (2π)¹² η(τ)²⁴` (27.14.16) is `discriminantDLMF`; Mathlib's `ModularForm.discriminant`
is `η²⁴` without the factor `(2π)¹²`. Ramanujan's `τ(n)` (27.14.18) is `ramanujanTau n`, defined
as the `n`th coefficient of the formal power series `X ∏_{m≥1} (1 - Xᵐ)²⁴ ∈ ℤ⟦X⟧`, so that it is
integer valued by construction; the analytic generating function is `hasSum_ramanujanTau`.

27.14.17 is proved for every `𝒜 ∈ SL(2, ℤ)` (stronger than DLMF, which assumes `c > 0`).
Ramanujan's congruences are `DLMF.Partitions.ramanujan_mod_five` etc. (tagged there). Lehmer's
conjecture `τ(n) ≠ 0` is open and stated only as a proposition (`LehmerConjecture`); Lehmer's
numerical verification bound is excluded (numerical).

The multiplicativity of `τ` and 27.14.19 come from Tau Ceti's Hecke eigenform theory of `Δ`
(`TauCeti.ModularForm.discriminant_qExpansion_coeff_mul`,
`TauCeti.ModularForm.discriminant_qExpansion_coeff_prime_pow_add_two`), transported to
`ramanujanTau` by `t27b_ramanujanTau_eq_coeff` (Mathlib's `qExpansion_coeff_unique`). The
congruence 27.14.20 compares `q`-expansions in `E₁₂ - E₆² = c Δ` (Mathlib's
`CuspForm.exists_smul_discriminant_of_weight_eq_twelve` and
`EisensteinSeries.E_qExpansion_coeff`).
-/

@[expose] public noncomputable section

open Finset Filter Asymptotics ArithmeticFunction Complex
open UpperHalfPlane hiding I
open scoped ArithmeticFunction.sigma Real MatrixGroups ModularForm

namespace DLMF.NumberTheory

open DLMF.Partitions

/-! ### Formal and analytic partition generating function (helpers) -/

section R27Helpers

open PowerSeries
open scoped PowerSeries.WithPiTopology

/-- The partition generating function as a formal power series. -/
def r27_partitionSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n ↦ (partitionFunction n : ℤ)

/-- Formal identity `(∑ p(n) Xⁿ) ∏ (1 - Xᵐ) = 1` in `ℤ⟦X⟧`. -/
lemma r27_partitionSeries_mul_pentagonal :
    r27_partitionSeries * pentagonalSeries ℤ = 1 := by
  have h1 := Nat.Partition.powerSeriesMk_card_restricted_eq_tprod ℤ (fun _ ↦ True)
  have h2 : r27_partitionSeries = PowerSeries.mk fun n ↦
      ((Nat.Partition.restricted n (fun _ ↦ True)).card : ℤ) := by
    ext n; simp [r27_partitionSeries, Nat.Partition.restricted, partitionFunction]
  rw [h2, h1, ← PowerSeries.WithPiTopology.tprod_one_sub_X_pow ℤ]
  simp only [ite_true]
  rw [← Multipliable.tprod_mul ?_ (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ)]
  · convert tprod_one with i
    simp_rw [pow_mul]
    exact PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)
  · simpa using Nat.Partition.multipliable_powerSeriesMk_card_restricted ℤ (fun _ ↦ True)

/-- `|k| ≤ ω(k)` for every integer `k`. -/
lemma r27_natAbs_le_pentagonal (k : ℤ) : k.natAbs ≤ pentagonal k := by
  have h := two_mul_natCast_pentagonal k
  have : (k.natAbs : ℤ) ≤ pentagonal k := by
    rcases le_or_gt 0 k with hk | hk
    · rw [Int.natAbs_of_nonneg hk]; rcases eq_or_lt_of_le hk with rfl | hk; · simp
      nlinarith
    · rw [Int.ofNat_natAbs_of_nonpos hk.le]; nlinarith
  exact_mod_cast this

/-- Reindexing a sum over `i ≤ n` supported on pentagonal numbers by `k ∈ [-n, n]`. -/
lemma r27_sum_range_extend_pentagonal (g : ℤ → ℤ) (n : ℕ) :
    ∑ i ∈ range (n + 1), Function.extend pentagonal g 0 i =
      ∑ k ∈ Icc (-(n : ℤ)) n, if pentagonal k ≤ n then g k else 0 := by
  rw [← sum_filter]
  rw [show ∑ k ∈ (Icc (-(n : ℤ)) n).filter (fun k ↦ pentagonal k ≤ n), g k =
      ∑ k ∈ (Icc (-(n : ℤ)) n).filter (fun k ↦ pentagonal k ≤ n),
        Function.extend pentagonal g 0 (pentagonal k) from
      sum_congr rfl fun k _ ↦ (pentagonal_injective.extend_apply g 0 k).symm,
    ← sum_image (f := fun i ↦ Function.extend pentagonal g 0 i)
      (fun a _ b _ h ↦ pentagonal_injective h)]
  · symm
    apply sum_subset
    · intro i hi
      simp only [mem_image, mem_filter] at hi
      obtain ⟨k, ⟨_, hk⟩, rfl⟩ := hi
      simp; omega
    · intro i hi hni
      rw [Function.extend_apply']
      · rfl
      rintro ⟨k, rfl⟩
      apply hni
      simp only [mem_range] at hi
      have := r27_natAbs_le_pentagonal k
      simp only [mem_image, mem_filter, mem_Icc]
      exact ⟨k, ⟨⟨by omega, by omega⟩, by omega⟩, rfl⟩

/-- Splitting a sum over `[-n, n]` into `k = 0` and the pairs `±k`. -/
lemma r27_sum_Icc_neg_self (h : ℤ → ℤ) (n : ℕ) :
    ∑ k ∈ Icc (-(n : ℤ)) n, h k = h 0 + ∑ k ∈ Icc 1 n, (h k + h (-k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) =
        insert (-((n + 1 : ℕ) : ℤ)) (insert ((n + 1 : ℕ) : ℤ) (Icc (-(n : ℤ)) n)) := by
      ext k; simp only [mem_insert, mem_Icc]; push_cast; omega
    rw [e, sum_insert (by simp; omega), sum_insert (by simp), ih, sum_Icc_succ_top (by omega)]
    push_cast; ring

/-- Generating function of partitions with parts `≤ N` as a finite product. -/
lemma r27_restrictedSeries_eq (N : ℕ) :
    (PowerSeries.mk fun n ↦ ((Nat.Partition.restricted n (· ≤ N)).card : ℤ)) =
      ∏ i ∈ range N, PowerSeries.geomSeriesOnMultiples (i + 1) := by
  rw [Nat.Partition.powerSeriesMk_card_restricted_eq_tprod ℤ (· ≤ N)]
  rw [tprod_eq_prod (s := range N) (fun i hi ↦ by
    simp at hi; rw [ite_eq_right_iff.mpr (fun h ↦ absurd h (by omega))])]
  refine prod_congr rfl fun i hi ↦ ?_
  simp only [show i + 1 ≤ N by simp at hi; omega, ite_true]
  have h1 : (∑' j : ℕ, (X : PowerSeries ℤ) ^ ((i + 1) * j)) * (1 - X ^ (i + 1)) = 1 := by
    simp_rw [pow_mul]
    exact PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)
  have h2 := PowerSeries.geomSeriesOnMultiples_mul_one_sub_X_pow (Nat.succ_pos i)
  have hne : (1 - X ^ (i + 1) : PowerSeries ℤ) ≠ 0 := by
    intro h
    have := congrArg (coeff 0) h
    simp at this
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

/-- The coefficients `n ≤ N` of `∏_{m ≤ N} 1/(1 - Xᵐ)` are `p(n)`. -/
lemma r27_coeff_prod_geomSeries {n N : ℕ} (hn : n ≤ N) :
    coeff n (∏ i ∈ range N, PowerSeries.geomSeriesOnMultiples (i + 1)) = partitionFunction n := by
  rw [← r27_restrictedSeries_eq, coeff_mk, Nat.Partition.restricted]
  congr 1
  rw [Finset.filter_true_of_mem fun p _ i hi ↦ (Nat.Partition.le_of_mem_parts hi).trans hn]
  rfl

/-- `∏_{m ≤ N} (1 - tᵐ)⁻¹ ≤ exp(1/(1 - t)²)` for `0 ≤ t < 1`. -/
lemma r27_prod_inv_one_sub_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1) (N : ℕ) :
    ∏ i ∈ range N, (1 - t ^ (i + 1))⁻¹ ≤ Real.exp (1 / (1 - t) ^ 2) := by
  have h1t : 0 < 1 - t := by linarith
  calc ∏ i ∈ range N, (1 - t ^ (i + 1))⁻¹ ≤ ∏ i ∈ range N, Real.exp (t ^ i / (1 - t)) := by
        apply prod_le_prod₀ (fun i _ ↦ ?_) (fun i _ ↦ ?_)
        · have : t ^ (i + 1) < 1 := pow_lt_one₀ ht0 ht (by omega)
          exact inv_nonneg.mpr (by linarith)
        · have hu : t ^ (i + 1) ≤ t := pow_le_of_le_one ht0 ht.le (by omega)
          have hu0 : 0 ≤ t ^ (i + 1) := pow_nonneg ht0 _
          have hd : 0 < 1 - t ^ (i + 1) := by linarith
          calc (1 - t ^ (i + 1))⁻¹ = t ^ (i + 1) / (1 - t ^ (i + 1)) + 1 := by
                field_simp; ring
            _ ≤ Real.exp (t ^ (i + 1) / (1 - t ^ (i + 1))) := Real.add_one_le_exp _
            _ ≤ Real.exp (t ^ i / (1 - t)) := by
                apply Real.exp_le_exp.mpr
                rw [div_le_div_iff₀ hd h1t]
                have : t ^ (i + 1) = t * t ^ i := by ring
                have hti : 0 ≤ t ^ i := pow_nonneg ht0 _
                have hti1 : t ^ (i + 1) ≤ t ^ i := pow_le_pow_of_le_one ht0 ht.le (by omega)
                nlinarith
    _ = Real.exp (∑ i ∈ range N, t ^ i / (1 - t)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (1 / (1 - t) ^ 2) := by
        apply Real.exp_le_exp.mpr
        rw [← sum_div]
        have : ∑ i ∈ range N, t ^ i ≤ 1 / (1 - t) := by
          simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := N) ht0 ht
        calc (∑ i ∈ range N, t ^ i) / (1 - t) ≤ (1 / (1 - t)) / (1 - t) := by gcongr
          _ = 1 / (1 - t) ^ 2 := by field_simp

/-- `∑ p(n) tⁿ` converges for `0 ≤ t < 1`. -/
lemma r27_summable_partitionFunction {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1) :
    Summable fun n ↦ (partitionFunction n : ℝ) * t ^ n := by
  refine summable_of_sum_range_le (c := Real.exp (1 / (1 - t) ^ 2))
    (fun n ↦ by positivity) fun N ↦ ?_
  set Q := ∏ i ∈ range N, PowerSeries.geomSeriesOnMultiples (i + 1)
  have hx : ‖(t : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht
  have hQ : PowerSeries.HasSumAt Q t (∏ i ∈ range N, (1 - (t : ℂ) ^ (i + 1))⁻¹) :=
    PowerSeries.HasSumAt.prod _ fun i _ ↦ PowerSeries.hasSumAt_geomSeriesOnMultiples (Nat.succ_pos i) hx
  have hre := Complex.hasSum_re hQ
  have hv : (∏ i ∈ range N, (1 - (t : ℂ) ^ (i + 1))⁻¹).re = ∏ i ∈ range N, (1 - t ^ (i + 1))⁻¹ := by
    rw [show (∏ i ∈ range N, (1 - (t : ℂ) ^ (i + 1))⁻¹) =
      ((∏ i ∈ range N, (1 - t ^ (i + 1))⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
  rw [hv] at hre
  have hterm : ∀ n, ((((coeff n Q : ℤ) : ℂ) * (t : ℂ) ^ n)).re = ((coeff n Q : ℤ) : ℝ) * t ^ n := by
    intro n
    rw [show (((coeff n Q : ℤ) : ℂ) * (t : ℂ) ^ n) = ((((coeff n Q : ℤ) : ℝ) * t ^ n : ℝ) : ℂ) by
      push_cast; rfl, Complex.ofReal_re]
  simp only [hterm] at hre
  have hnn : ∀ n, 0 ≤ ((coeff n Q : ℤ) : ℝ) * t ^ n := by
    intro n
    have : coeff n Q = ((Nat.Partition.restricted n (· ≤ N)).card : ℤ) := by
      simp only [Q]; rw [← r27_restrictedSeries_eq, coeff_mk]
    rw [this]; positivity
  calc ∑ n ∈ range N, (partitionFunction n : ℝ) * t ^ n
      = ∑ n ∈ range N, ((coeff n Q : ℤ) : ℝ) * t ^ n := by
        refine sum_congr rfl fun n hn ↦ ?_
        rw [r27_coeff_prod_geomSeries (by simp at hn; omega)]; simp
    _ ≤ ∏ i ∈ range N, (1 - t ^ (i + 1))⁻¹ := sum_le_hasSum _ (fun n _ ↦ hnn n) hre
    _ ≤ _ := r27_prod_inv_one_sub_le ht0 ht N

/-- The pentagonal series converges absolutely to Euler's function in the unit disc. -/
lemma r27_absEval_pentagonalSeries {x : ℂ} (hx : ‖x‖ < 1) :
    PowerSeries.HasSumAt (pentagonalSeries ℤ) x (eulerFunction x) := by
  have hc : ∀ n, ((coeff n (pentagonalSeries ℤ) : ℤ) : ℂ) = coeff n (pentagonalSeries ℂ) := by
    intro n
    by_cases hn : n ∈ Set.range pentagonal
    · obtain ⟨k, rfl⟩ := hn
      simp only [coeff_pentagonalSeries_pentagonal]
      rcases Int.even_or_odd k with h | h <;> simp [Int.negOnePow_even, Int.negOnePow_odd, h]
    · simp [coeff_pentagonalSeries_eq_zero _ hn]
  have hb := PowerSeries.hasSumAt_of_bounded (P := pentagonalSeries ℤ) (C := 1) (fun n ↦ by
    by_cases hn : n ∈ Set.range pentagonal
    · obtain ⟨k, rfl⟩ := hn
      simp only [coeff_pentagonalSeries_pentagonal]
      rcases Int.even_or_odd k with h | h <;> simp [Int.negOnePow_even, Int.negOnePow_odd, h]
    · simp [coeff_pentagonalSeries_eq_zero _ hn]) hx
  simp only [PowerSeries.HasSumAt, hc] at hb ⊢
  rwa [← eulerFunction_def] at hb

/-- The partition series converges absolutely in the unit disc. -/
lemma r27_absEval_partitionSeries {x : ℂ} (hx : ‖x‖ < 1) :
    PowerSeries.HasSumAt r27_partitionSeries x (∑' n, (partitionFunction n : ℂ) * x ^ n) := by
  have hc : ∀ n, ((coeff n r27_partitionSeries : ℤ) : ℂ) = (partitionFunction n : ℂ) := by
    intro n; simp [r27_partitionSeries]
  have hs : Summable fun n ↦ ‖((coeff n r27_partitionSeries : ℤ) : ℂ) * x ^ n‖ := by
    simp only [hc, norm_mul, norm_pow, Complex.norm_natCast]
    exact r27_summable_partitionFunction (norm_nonneg x) hx
  simp only [PowerSeries.HasSumAt, hc] at hs ⊢
  exact hs.of_norm.hasSum

/-- Euler's pentagonal recursion for `p(n)` (DLMF 27.14.6). -/
lemma r27_rec {n : ℕ} (hn : 1 ≤ n) :
    (partitionFunction n : ℤ) = ∑ k ∈ Finset.Icc 1 n, (-1) ^ (k + 1) *
      ((if pentagonal k ≤ n then (partitionFunction (n - pentagonal k) : ℤ) else 0) +
        (if pentagonal (-k) ≤ n then (partitionFunction (n - pentagonal (-k)) : ℤ) else 0)) := by
  have h0 : coeff n (pentagonalSeries ℤ * r27_partitionSeries) = 0 := by
    rw [mul_comm, r27_partitionSeries_mul_pentagonal, coeff_one,
      ite_eq_right_iff.mpr (fun h ↦ absurd h (by omega))]
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ coeff i (pentagonalSeries ℤ) * coeff j r27_partitionSeries)] at h0
  simp only [r27_partitionSeries, coeff_mk] at h0
  simp_rw [coeff_pentagonalSeries_mul_eq_extend _ _ (fun j ↦ (partitionFunction (n - j) : ℤ))]
    at h0
  rw [r27_sum_range_extend_pentagonal, r27_sum_Icc_neg_self] at h0
  have hp0 : pentagonal 0 = 0 := by simp [pentagonal_def]
  simp only [hp0, Nat.sub_zero, zero_le, ite_true, Int.negOnePow_zero, Units.val_one,
    Int.cast_id, one_mul] at h0
  rw [eq_neg_of_add_eq_zero_left h0, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Int.negOnePow_neg, Int.coe_negOnePow_natCast]
  split_ifs <;> ring

/-- `X g_k' = g_k (k X^k g_k)` for the geometric series `g_k = 1/(1 - X^k)`. -/
lemma r27_X_derivative_geomSeries {k : ℕ} (hk : 0 < k) :
    X * d⁄dX (PowerSeries.geomSeriesOnMultiples k) =
      PowerSeries.geomSeriesOnMultiples k * ((k : PowerSeries ℤ) * X ^ k * PowerSeries.geomSeriesOnMultiples k) := by
  have h := PowerSeries.geomSeriesOnMultiples_mul_one_sub_X_pow hk
  have hd := congrArg (fun f : PowerSeries ℤ ↦ d⁄dX f) h
  rw [Derivation.leibniz, derivative_one, map_sub, derivative_one, derivative_pow,
    derivative_X] at hd
  simp only [smul_eq_mul, zero_sub, mul_one] at hd
  -- hd : g * -(k X^{k-1}) + (1 - X^k) * g' = 0
  have key : (1 - X ^ k) * d⁄dX (PowerSeries.geomSeriesOnMultiples k) =
      PowerSeries.geomSeriesOnMultiples k * ((k : PowerSeries ℤ) * X ^ (k - 1)) := by
    linear_combination hd
  have hXk : X * X ^ (k - 1) = (X ^ k : PowerSeries ℤ) := by
    rw [← pow_succ']; congr 1; omega
  calc X * d⁄dX (PowerSeries.geomSeriesOnMultiples k)
      = X * (PowerSeries.geomSeriesOnMultiples k * (1 - X ^ k)) * d⁄dX (PowerSeries.geomSeriesOnMultiples k) := by rw [h]; ring
    _ = X * PowerSeries.geomSeriesOnMultiples k * ((1 - X ^ k) * d⁄dX (PowerSeries.geomSeriesOnMultiples k)) := by ring
    _ = _ := by rw [key, ← hXk]; ring

/-- Logarithmic derivative of a finite product of geometric series. -/
lemma r27_X_derivative_prod_geomSeries (N : ℕ) :
    X * d⁄dX (∏ i ∈ range N, PowerSeries.geomSeriesOnMultiples (i + 1)) =
      (∏ i ∈ range N, PowerSeries.geomSeriesOnMultiples (i + 1)) *
        ∑ i ∈ range N, (((i + 1 : ℕ) : PowerSeries ℤ) * X ^ (i + 1) * PowerSeries.geomSeriesOnMultiples (i + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hg := r27_X_derivative_geomSeries (Nat.succ_pos N)
    rw [prod_range_succ, sum_range_succ, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    simp only [Nat.succ_eq_add_one] at hg ⊢
    linear_combination (∏ i ∈ range N, PowerSeries.geomSeriesOnMultiples (i + 1)) * hg + PowerSeries.geomSeriesOnMultiples (N + 1) * ih

/-- Coefficients of `∑_{k ≤ N} k X^k/(1 - X^k)`: `σ₁(m)` for `1 ≤ m ≤ N`. -/
lemma r27_coeff_sigmaSeries {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    coeff m (∑ i ∈ range N, (((i + 1 : ℕ) : PowerSeries ℤ) * X ^ (i + 1) *
      PowerSeries.geomSeriesOnMultiples (i + 1))) = (σ 1 m : ℤ) := by
  rw [map_sum]
  have : ∀ i ∈ range N, coeff m (((i + 1 : ℕ) : PowerSeries ℤ) * X ^ (i + 1) *
      PowerSeries.geomSeriesOnMultiples (i + 1)) = if (i + 1) ∣ m then ((i + 1 : ℕ) : ℤ) else 0 := by
    intro i _
    rw [← map_natCast (C (R := ℤ)), mul_assoc, coeff_C_mul, coeff_X_pow_mul', PowerSeries.geomSeriesOnMultiples]
    split_ifs with h1 h2 h2
    · simp [coeff_mk, (Nat.dvd_sub_iff_left h1 dvd_rfl).mpr h2]
    · have h3 : ¬ (i + 1) ∣ m - (i + 1) := fun h ↦ h2 ((Nat.dvd_sub_iff_left h1 dvd_rfl).mp h)
      simp [coeff_mk, h3]
    · exact absurd (Nat.le_of_dvd (by omega) h2) h1
    · simp
  rw [sum_congr rfl this, ArithmeticFunction.sigma_one_apply, Nat.cast_sum, ← sum_filter]
  refine sum_nbij' (fun i ↦ i + 1) (fun d ↦ d - 1) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [mem_filter, mem_range] at hi
    simp [Nat.mem_divisors]; exact ⟨hi.2, by omega⟩
  · intro d hd; simp only [Nat.mem_divisors] at hd
    have := Nat.pos_of_dvd_of_pos hd.1 (by omega)
    have := Nat.le_of_dvd (by omega) hd.1
    simp only [mem_filter, mem_range]; refine ⟨by omega, ?_⟩
    rw [Nat.sub_add_cancel (by omega)]; exact hd.1
  · intro i _; simp
  · intro d hd; simp only [Nat.mem_divisors] at hd
    have := Nat.pos_of_dvd_of_pos hd.1 (by omega)
    omega
  · intro i _; simp

end R27Helpers

/-! ### §27.14(i) Partition functions -/

/-- DLMF 27.14.1: `p(n)` is the number of solutions of `n = a₁ + a₂ + ⋯`,
`a₁ ≥ a₂ ≥ ⋯ ≥ 1`, i.e. the number of partitions of `n`. -/
@[dlmf 27.14.E1]
theorem partitionFunction_eq_card (n : ℕ) :
    partitionFunction n = Fintype.card (Nat.Partition n) := rfl

/-- §27.14(i): `p(5) = 7`. -/
@[dlmf 27.14.i]
theorem partitionFunction_five : partitionFunction 5 = 7 := by
  have e2 := r27_rec (n := 2) (by norm_num)
  have e3 := r27_rec (n := 3) (by norm_num)
  have e4 := r27_rec (n := 4) (by norm_num)
  have e5 := r27_rec (n := 5) (by norm_num)
  simp only [Finset.sum_Icc_succ_top, Finset.Icc_self, Finset.sum_singleton, Nat.reduceLeDiff,
    pentagonal_def] at e2 e3 e4 e5
  norm_num at e2 e3 e4 e5
  omega

/-- §27.14(i): `p_k(n)`, the number of partitions of `n` into at most `k` parts. -/
@[dlmf 27.14.i]
def partitionsAtMost (k n : ℕ) : ℕ :=
  (Finset.univ.filter fun q : Nat.Partition n ↦ q.parts.card ≤ k).card

/-! ### §27.14(ii) Generating functions and recursions -/

/-- DLMF 27.14.2: Euler's reciprocal function `f(x) = ∏_{m≥1} (1 - xᵐ)`, `|x| < 1`
(a totalized `tprod`). -/
@[dlmf 27.14.E2]
def eulerReciprocal (x : ℂ) : ℂ := ∏' m : ℕ, (1 - x ^ (m + 1))

/-- DLMF 27.14.2: `f(x) = (x; x)_∞`. -/
@[dlmf 27.14.E2]
theorem eulerReciprocal_eq_qPochhammerInf (x : ℂ) :
    eulerReciprocal x = DLMF.QSeries.qPochhammerInf x x := by
  simp only [eulerReciprocal, DLMF.QSeries.qPochhammerInf, pow_succ']

/-- DLMF 27.14.2: for `|x| < 1` the product converges to Mathlib's `eulerFunction x`. -/
@[dlmf 27.14.E2]
theorem hasProd_eulerReciprocal {x : ℂ} (hx : ‖x‖ < 1) :
    HasProd (fun m : ℕ ↦ 1 - x ^ (m + 1)) (eulerReciprocal x) ∧
      eulerReciprocal x = eulerFunction x := by
  have h := hasProd_eulerFunction hx
  exact ⟨by rw [eulerReciprocal, h.tprod_eq]; exact h, h.tprod_eq⟩

/-- DLMF 27.14.3: `1/f(x) = ∑_{n≥0} p(n) xⁿ`, `|x| < 1`. -/
@[dlmf 27.14.E3]
theorem hasSum_partitionFunction {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ ↦ (partitionFunction n : ℂ) * x ^ n) (1 / eulerReciprocal x) := by
  have hF := r27_absEval_partitionSeries hx
  have h1 := PowerSeries.HasSumAt.mul hF (r27_absEval_pentagonalSeries hx)
  rw [r27_partitionSeries_mul_pentagonal] at h1
  have h2 := PowerSeries.HasSumAt.unique h1 (PowerSeries.hasSumAt_one x)
  rw [(hasProd_eulerReciprocal hx).2, ← eq_one_div_of_mul_eq_one_left h2]
  have hc : ∀ n, ((PowerSeries.coeff n r27_partitionSeries : ℤ) : ℂ) =
      (partitionFunction n : ℂ) := by
    intro n; simp [r27_partitionSeries]
  simpa only [PowerSeries.HasSumAt, hc] using hF

/-- DLMF 27.14.5: the pentagonal numbers `ω(±k) = (3k² ∓ k)/2`. -/
@[dlmf 27.14.E5]
theorem pentagonal_pm (k : ℕ) :
    (pentagonal k : ℤ) = (3 * k ^ 2 - k) / 2 ∧ (pentagonal (-k) : ℤ) = (3 * k ^ 2 + k) / 2 := by
  constructor
  · rw [natCast_pentagonal]; ring_nf
  · rw [pentagonal_neg, Int.toNat_of_nonneg (by positivity)]; ring_nf

/-- DLMF 27.14.4 (Euler's pentagonal number theorem):
`f(x) = 1 + ∑_{k≥1} (-1)^k (x^{ω(k)} + x^{ω(-k)})`, `|x| < 1`. -/
@[dlmf 27.14.E4]
theorem eulerReciprocal_pentagonal {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ ↦ (-1) ^ (k + 1) *
        (x ^ pentagonal (k + 1 : ℕ) + x ^ pentagonal (-(k + 1 : ℕ))))
      (eulerReciprocal x - 1) := by
  have h := (hasSum_eulerFunction_pentagonal hx).nat_add_neg
  rw [← (hasProd_eulerReciprocal hx).2] at h
  have h1 := (hasSum_nat_add_iff' 1).mpr h
  convert h1 using 1
  · funext k
    simp only [Int.coe_negOnePow, Int.negOnePow_neg]
    push_cast
    rw [show ((k : ℤ) + 1).natAbs = k + 1 by omega]
    ring
  · simp [pentagonal_def]

/-- DLMF 27.14.6: `p(n) = ∑_{k≥1} (-1)^{k+1} (p(n - ω(k)) + p(n - ω(-k)))`, `n ≥ 1`, with
`p(m) = 0` for `m < 0`; the terms vanish for `k > n`. -/
@[dlmf 27.14.E6]
theorem partitionFunction_recursion {n : ℕ} (hn : 1 ≤ n) :
    (partitionFunction n : ℤ) = ∑ k ∈ Finset.Icc 1 n, (-1) ^ (k + 1) *
      ((if pentagonal k ≤ n then (partitionFunction (n - pentagonal k) : ℤ) else 0) +
        (if pentagonal (-k) ≤ n then (partitionFunction (n - pentagonal (-k)) : ℤ) else 0)) :=
  r27_rec hn

/-- DLMF 27.14.7: `n p(n) = ∑_{k=1}^{n} σ₁(k) p(n - k)`. -/
@[dlmf 27.14.E7]
theorem partitionFunction_sigma_recursion (n : ℕ) :
    n * partitionFunction n = ∑ k ∈ Finset.Icc 1 n, σ 1 k * partitionFunction (n - k) := by
  open PowerSeries in
  have h := congrArg (coeff n) (r27_X_derivative_prod_geomSeries n)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [coeff_succ_X_mul, coeff_derivative, r27_coeff_prod_geomSeries le_rfl, mul_comm _ (∑ i ∈ _, _),
    coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ coeff i (∑ i ∈ range (m + 1), (((i + 1 : ℕ) : PowerSeries ℤ) * X ^ (i + 1) *
        PowerSeries.geomSeriesOnMultiples (i + 1))) * coeff j (∏ i ∈ range (m + 1), PowerSeries.geomSeriesOnMultiples (i + 1))),
    sum_range_succ'] at h
  have h0 : coeff 0 (∑ i ∈ range (m + 1), (((i + 1 : ℕ) : PowerSeries ℤ) * X ^ (i + 1) *
      PowerSeries.geomSeriesOnMultiples (i + 1))) = 0 := by
    rw [map_sum]
    refine sum_eq_zero fun i _ ↦ ?_
    rw [← map_natCast (C (R := ℤ)), mul_assoc, coeff_C_mul, coeff_X_pow_mul']
    simp
  rw [h0, zero_mul, add_zero] at h
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [mul_comm, h, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [mem_range] at hk
  rw [r27_coeff_sigmaSeries (by omega) (by omega), r27_coeff_prod_geomSeries (by omega),
    add_comm 1 k]

/-! ### §27.14(iii) Asymptotic formulas -/

/-- DLMF 27.14.8 (Hardy–Ramanujan): `p(n) ∼ e^{K√n}/(4n√3)`, `K = π√(2/3)`. -/
@[dlmf 27.14.E8]
theorem partitionFunction_isEquivalent :
    (fun n : ℕ ↦ (partitionFunction n : ℝ)) ~[atTop]
      fun n ↦ Real.exp (π * Real.sqrt (2 / 3) * Real.sqrt n) / (4 * n * Real.sqrt 3) := by
  sorry

/-- DLMF 27.14.11: the Dedekind sum `s(h, k) = ∑_{r=1}^{k-1} (r/k)(hr/k - ⌊hr/k⌋ - 1/2)` is the
project's `DLMF.Weierstrass.dedekindSum` (DLMF 23.18.7). -/
@[dlmf 27.14.E11]
theorem dedekindSum_eq (h k : ℤ) :
    DLMF.Weierstrass.dedekindSum h k =
      ∑ r ∈ Finset.Ico (1 : ℤ) k, (r / k : ℝ) * ((h * r / k : ℝ) - ⌊(h * r / k : ℝ)⌋ - 1 / 2) :=
  rfl

/-- DLMF 27.14.10: `A_k(n) = ∑_{1≤h≤k, (h,k)=1} exp(πi s(h, k) - 2πi n h/k)`. -/
@[dlmf 27.14.E10]
def rademacherA (k n : ℕ) : ℂ :=
  ∑ h ∈ (Finset.Icc 1 k).filter (fun h ↦ h.Coprime k),
    cexp (π * I * (DLMF.Weierstrass.dedekindSum h k : ℂ) - 2 * π * I * n * h / k)

/-- DLMF 27.14.9 (Rademacher): `p(n) = (1/(π√2)) ∑_{k≥1} √k A_k(n)
[d/dt (sinh(K√t/k)/√t)]_{t = n - 1/24}`, `n ≥ 1`, `K = π√(2/3)`. -/
@[dlmf 27.14.E9]
theorem partitionFunction_rademacher {n : ℕ} (hn : 1 ≤ n) :
    HasSum (fun k : ℕ ↦ 1 / (π * Real.sqrt 2) * Real.sqrt (k + 1) * rademacherA (k + 1) n *
        (deriv (fun t : ℝ ↦ Real.sinh (π * Real.sqrt (2 / 3) * Real.sqrt t / (k + 1)) /
          Real.sqrt t) (n - 1 / 24) : ℂ))
      (partitionFunction n : ℂ) := by
  sorry

/-! ### §27.14(iv) Relation to modular functions -/

/-- DLMF 27.14.12: `η(τ) = e^{πiτ/12} ∏_{n≥1} (1 - e^{2πinτ})`, `ℑτ > 0`; Mathlib's
`ModularForm.eta`. -/
@[dlmf 27.14.E12]
theorem eta_eq_prod (τ : ℂ) :
    η τ = cexp (π * I * τ / 12) * ∏' n : ℕ, (1 - cexp (2 * π * I * (n + 1) * τ)) := by
  rw [ModularForm.eta, Function.Periodic.qParam]
  simp_rw [ModularForm.eta_q_eq_cexp]
  congr 2
  push_cast
  ring

/-- DLMF 27.14.13: `η(τ) = e^{πiτ/12} f(e^{2πiτ})`. -/
@[dlmf 27.14.E13]
theorem eta_eq_eulerReciprocal (τ : ℂ) :
    η τ = cexp (π * I * τ / 12) * eulerReciprocal (cexp (2 * π * I * τ)) := by
  rw [ModularForm.eta, Function.Periodic.qParam, eulerReciprocal]
  simp_rw [ModularForm.eta_q_eq_pow]
  congr 2
  push_cast
  ring

/-- DLMF 27.14.14: for `a, b, c, d ∈ ℤ`, `ad - bc = 1`, `c > 0`,
`η((aτ + b)/(cτ + d)) = ε (-i(cτ + d))^{1/2} η(τ)` with
`ε = exp(πi((a + d)/(12c) - s(d, c)))` and the principal square root. This is DLMF 23.18.5
(`DLMF.Weierstrass.eta_smul`) with `s(-d, c) = -s(d, c)`. -/
@[dlmf 27.14.E14]
theorem eta_transform (A : SL(2, ℤ)) (hc : 0 < A 1 0) (τ : ℍ) :
    η (A • τ : ℍ) = cexp (π * I * (((A 0 0 + A 1 1 : ℤ) : ℂ) / (12 * (A 1 0 : ℂ)) -
        (DLMF.Weierstrass.dedekindSum (A 1 1) (A 1 0) : ℂ))) *
      (-I * ((A 1 0 : ℂ) * τ + A 1 1)) ^ (1 / 2 : ℂ) * η (τ : ℂ) := by
  sorry

/-! ### §27.14(v) Divisibility properties -/

/-- DLMF 27.14.15 (Ramanujan): `5 f(x⁵)⁵ / f(x)⁶ = ∑_{n≥0} p(5n + 4) xⁿ`, `|x| < 1`. -/
@[dlmf 27.14.E15]
theorem hasSum_partitionFunction_five {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ ↦ (partitionFunction (5 * n + 4) : ℂ) * x ^ n)
      (5 * eulerReciprocal (x ^ 5) ^ 5 / eulerReciprocal x ^ 6) := by
  sorry

/-- §27.14(v) (Ono): for every prime `q > 3` there are integers `a > 0` and `b ≥ 0` with
`p(an + b) ≡ 0 (mod q)` for all `n`. -/
@[dlmf 27.14.v]
theorem exists_partition_congruence {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) :
    ∃ a b : ℕ, 0 < a ∧ ∀ n : ℕ, q ∣ partitionFunction (a * n + b) := by
  sorry

/-- §27.14(v): `p(157525693 n + 111247) ≡ 0 (mod 13)`. -/
@[dlmf 27.14.v]
theorem partitionFunction_mod_thirteen (n : ℕ) :
    13 ∣ partitionFunction (157525693 * n + 111247) := by
  sorry

/-! ### §27.14(vi) Ramanujan's tau function -/

/-- DLMF 27.14.16: the discriminant `Δ(τ) = (2π)¹² η(τ)²⁴`, `ℑτ > 0`. -/
@[dlmf 27.14.E16]
def discriminantDLMF (τ : ℂ) : ℂ := (2 * π) ^ 12 * η τ ^ 24

/-- DLMF 27.14.16: `Δ_DLMF = (2π)¹² Δ_Mathlib`. -/
@[dlmf 27.14.E16]
theorem discriminantDLMF_eq (τ : ℍ) :
    discriminantDLMF τ = (2 * π) ^ 12 * ModularForm.discriminant τ := rfl

/-- DLMF 27.14.17: `Δ((aτ + b)/(cτ + d)) = (cτ + d)¹² Δ(τ)` for all `𝒜 ∈ SL(2, ℤ)`
(stronger than DLMF, which assumes `c > 0`). -/
@[dlmf 27.14.E17]
theorem discriminantDLMF_transform (A : SL(2, ℤ)) (τ : ℍ) :
    discriminantDLMF (A • τ : ℍ) = ((A 1 0 : ℂ) * τ + A 1 1) ^ 12 * discriminantDLMF τ := by
  have h := SlashInvariantForm.slash_action_eqn' CuspForm.discriminant (Γ := 𝒮ℒ)
    (γ := Matrix.SpecialLinearGroup.mapGL ℝ A) (MonoidHom.mem_range.mpr ⟨A, rfl⟩) τ
  simp only [CuspForm.coe_discriminant] at h
  have h' : ModularForm.discriminant (A • τ : ℍ) =
      ((A 1 0 : ℂ) * τ + A 1 1) ^ 12 * ModularForm.discriminant τ := by
    convert h using 2 <;> rfl
  rw [discriminantDLMF_eq, discriminantDLMF_eq, h']
  ring

/-- DLMF 27.14.18: Ramanujan's `τ(n)`, the `n`th coefficient of `x ∏_{m≥1} (1 - xᵐ)²⁴`. -/
@[dlmf 27.14.E18]
def ramanujanTau (n : ℕ) : ℤ :=
  PowerSeries.coeff n (PowerSeries.X * PowerSeries.pentagonalSeries ℤ ^ 24)

/-- DLMF 27.14.18: `x ∏_{n≥1} (1 - xⁿ)²⁴ = ∑_{n≥1} τ(n) xⁿ`, `|x| < 1`. -/
@[dlmf 27.14.E18]
theorem hasSum_ramanujanTau {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ ↦ (ramanujanTau n : ℂ) * x ^ n) (x * eulerReciprocal x ^ 24) := by
  rw [(hasProd_eulerReciprocal hx).2]
  exact (PowerSeries.HasSumAt.mul (PowerSeries.hasSumAt_X x) (PowerSeries.HasSumAt.pow (r27_absEval_pentagonalSeries hx) 24))

/-! #### Bridge to Mathlib's discriminant and Eisenstein series (helpers) -/

/-- Mathlib's `Δ(τ) = η(τ)²⁴` is `∑ τ(m) qᵐ` with `q = e^{2πiτ}`. -/
lemma t27b_hasSum_discriminant (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (ramanujanTau m : ℂ) • Function.Periodic.qParam 1 τ ^ m)
      (ModularForm.discriminant τ) := by
  have hq : ‖Function.Periodic.qParam 1 τ‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have h := hasSum_ramanujanTau hq
  simp only [smul_eq_mul]
  convert h using 1
  rw [ModularForm.discriminant, eta_eq_eulerReciprocal, mul_pow, Function.Periodic.qParam,
    ← Complex.exp_nat_mul]
  congr 2
  · push_cast; ring_nf
  · congr 2; push_cast; ring

/-- `τ(m)` is the `m`th `q`-expansion coefficient of Mathlib's `Δ`. -/
lemma t27b_ramanujanTau_eq_coeff (m : ℕ) :
    (ramanujanTau m : ℂ) = (UpperHalfPlane.qExpansion 1 ModularForm.discriminant).coeff m :=
  ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL
    (f := CuspForm.discriminant) t27b_hasSum_discriminant m

/-- `τ(mn) = τ(m) τ(n)` for coprime `m, n` (Tau Ceti). -/
lemma t27b_ramanujanTau_mul_coprime {m n : ℕ} (h : m.Coprime n) :
    ramanujanTau (m * n) = ramanujanTau m * ramanujanTau n := by
  have := TauCeti.ModularForm.discriminant_qExpansion_coeff_mul h
  rw [← t27b_ramanujanTau_eq_coeff, ← t27b_ramanujanTau_eq_coeff,
    ← t27b_ramanujanTau_eq_coeff] at this
  exact_mod_cast this

/-- `τ(1) = 1`. -/
lemma t27b_ramanujanTau_one : ramanujanTau 1 = 1 := by
  have := ModularForm.discriminant_qExpansion_coeff_one
  rw [← t27b_ramanujanTau_eq_coeff] at this
  exact_mod_cast this

/-- `τ(p^{r+2}) = τ(p) τ(p^{r+1}) - p¹¹ τ(p^r)` (Tau Ceti). -/
lemma t27b_ramanujanTau_prime_pow_add_two {p : ℕ} (hp : p.Prime) (r : ℕ) :
    ramanujanTau (p ^ (r + 2)) =
      ramanujanTau p * ramanujanTau (p ^ (r + 1)) - (p : ℤ) ^ 11 * ramanujanTau (p ^ r) := by
  have := TauCeti.ModularForm.discriminant_qExpansion_coeff_prime_pow_add_two hp r
  simp only [← t27b_ramanujanTau_eq_coeff] at this
  exact_mod_cast this

section T27b691

open ModularForm EisensteinSeries
open scoped ArithmeticFunction.sigma

/-- `B₁₂ = -691/2730`. -/
private lemma t27b_bernoulli_twelve : bernoulli 12 = -691 / 2730 := by decide +kernel

/-- `E₁₂ - E₆²` as a level-one modular form of weight 12. -/
private def t27b_G : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by decide) (E (k := 12) (by norm_num)) -
    ModularForm.mcast (by decide) (E₆.pow 2)

/-- The `q`-expansion of `E₁₂ - E₆²`. -/
private lemma t27b_G_qExpansion :
    qExpansion 1 t27b_G = qExpansion 1 (E (k := 12) (by norm_num)) -
      qExpansion 1 E₆ * qExpansion 1 E₆ := by
  simp only [t27b_G, FunLike.coe_sub, coe_mcast,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  ring

/-- The coefficients of `E₁₂`: `1` and `(65520/691) σ₁₁(m)`. -/
private lemma t27b_E12_coeff (m : ℕ) :
    (qExpansion 1 (E (k := 12) (by norm_num))).coeff m =
      if m = 0 then 1 else (65520 / 691 : ℂ) * (σ 11 m : ℂ) := by
  rw [E_qExpansion_coeff (by norm_num) ⟨6, rfl⟩, t27b_bernoulli_twelve]
  norm_num

/-- `E₁₂ - E₆²` is a cusp form. -/
private lemma t27b_G_isCuspForm : IsCuspForm t27b_G := by
  simp [isCuspForm_iff_coeffZero_eq_zero, t27b_G_qExpansion,
    PowerSeries.coeff_mul, -PowerSeries.coeff_zero_eq_constantCoeff,
    E_qExpansion_coeff_zero _ ⟨3, rfl⟩, E_qExpansion_coeff_zero _ ⟨6, rfl⟩]

/-- Integer coefficients of `E₆`. -/
private def t27b_e6 (m : ℕ) : ℤ := if m = 0 then 1 else -504 * (σ 5 m : ℤ)

/-- The coefficients of `E₆` are the integers `t27b_e6 m`. -/
private lemma t27b_E6_coeff (m : ℕ) :
    (qExpansion 1 E₆).coeff m = (t27b_e6 m : ℂ) := by
  rw [E_qExpansion_coeff (by norm_num) ⟨3, rfl⟩, t27b_e6]
  have hb : bernoulli 6 = 1 / 42 := by decide +kernel
  split_ifs <;> norm_num [hb]

/-- The coefficients of `E₁₂ - E₆²` for `n ≥ 1`. -/
private lemma t27b_G_coeff (n : ℕ) (hn : n ≠ 0) :
    (qExpansion 1 t27b_G).coeff n = (65520 / 691 : ℂ) * (σ 11 n : ℂ) -
      ((∑ x ∈ Finset.antidiagonal n, t27b_e6 x.1 * t27b_e6 x.2 : ℤ) : ℂ) := by
  rw [t27b_G_qExpansion, map_sub, t27b_E12_coeff, PowerSeries.coeff_mul]
  simp [hn, t27b_E6_coeff]

/-- `E₁₂ - E₆² = c Δ`, coefficientwise. -/
private lemma t27b_G_eq : ∃ c : ℂ, ∀ n, (qExpansion 1 t27b_G).coeff n =
    c * (ramanujanTau n : ℂ) := by
  obtain ⟨g, hg⟩ := t27b_G_isCuspForm
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve g
  have hgE : (g : ℍ → ℂ) = t27b_G := congrArg DFunLike.coe hg
  have hcΔ : (c • CuspForm.discriminant : ℍ → ℂ) = g := congrArg DFunLike.coe hc
  have hgΔ := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c
    CuspForm.discriminant
  rw [hcΔ, hgE] at hgΔ
  refine ⟨c, fun n ↦ ?_⟩
  rw [hgΔ, PowerSeries.coeff_smul, smul_eq_mul, CuspForm.coe_discriminant,
    t27b_ramanujanTau_eq_coeff]

end T27b691

/-- §27.14(vi): `τ` is multiplicative. -/
@[dlmf 27.14.vi]
theorem isMultiplicativeFn_ramanujanTau :
    IsMultiplicativeFn (fun n ↦ (ramanujanTau n : ℂ)) := by
  refine ⟨by simp [t27b_ramanujanTau_one], fun m n _ _ h ↦ ?_⟩
  simp only [t27b_ramanujanTau_mul_coprime h, Int.cast_mul]

/-- DLMF 27.14.19: `τ(m)τ(n) = ∑_{d ∣ (m,n)} d¹¹ τ(mn/d²)`, `m, n ≥ 1`. -/
@[dlmf 27.14.E19]
theorem ramanujanTau_mul {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ramanujanTau m * ramanujanTau n =
      ∑ d ∈ (Nat.gcd m n).divisors, (d : ℤ) ^ 11 * ramanujanTau (m * n / d ^ 2) := by
  have hf : IsMultiplicativeFn ramanujanTau :=
    ⟨t27b_ramanujanTau_one, fun m n _ _ h ↦ t27b_ramanujanTau_mul_coprime h⟩
  refine t27b_hecke_mul (w := fun d ↦ (d : ℤ) ^ 11) hf (fun i j ↦ by push_cast; ring)
    (fun p hp a b ↦ t27b_hecke_prime_pow _ _ hp (fun k ↦ by push_cast; ring)
      t27b_ramanujanTau_one (t27b_ramanujanTau_prime_pow_add_two hp) a b) hm hn

/-- §27.14(vi): Lehmer's conjecture `τ(n) ≠ 0` for `n ≥ 1` (open; stated as a proposition
only). -/
@[dlmf 27.14.vi]
def LehmerConjecture : Prop := ∀ n : ℕ, 1 ≤ n → ramanujanTau n ≠ 0

/-- DLMF 27.14.20: `τ(n) ≡ σ₁₁(n) (mod 691)`. -/
@[dlmf 27.14.E20]
theorem ramanujanTau_modEq (n : ℕ) : ramanujanTau n ≡ (σ 11 n : ℤ) [ZMOD 691] := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [ramanujanTau]
  obtain ⟨c, hc⟩ := t27b_G_eq
  have h1 := hc 1
  have hA1 : (∑ x ∈ Finset.antidiagonal 1, t27b_e6 x.1 * t27b_e6 x.2) = -1008 := by
    simp [t27b_e6, Finset.Nat.antidiagonal_succ]
  rw [t27b_G_coeff 1 one_ne_zero, t27b_ramanujanTau_one, hA1] at h1
  have hc' : c = 65520 / 691 + 1008 := by
    simp at h1
    linear_combination -h1
  have hn' := hc n
  rw [t27b_G_coeff n hn, hc'] at hn'
  set A := ∑ x ∈ Finset.antidiagonal n, t27b_e6 x.1 * t27b_e6 x.2
  have key : 65520 * (σ 11 n : ℤ) - 691 * A = 762048 * ramanujanTau n := by
    have : ((65520 * (σ 11 n : ℤ) - 691 * A : ℤ) : ℂ) =
        ((762048 * ramanujanTau n : ℤ) : ℂ) := by
      push_cast
      linear_combination 691 * hn'
    exact_mod_cast this
  have hdvd : (691 : ℤ) ∣ 566 * ((σ 11 n : ℤ) - ramanujanTau n) :=
    ⟨A - 94 * σ 11 n + 1102 * ramanujanTau n, by linear_combination key⟩
  have hcop : IsCoprime (691 : ℤ) 566 := Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num)
  exact (Int.modEq_iff_dvd).mpr (hcop.dvd_of_dvd_mul_left hdvd)

end DLMF.NumberTheory
