/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.PSeriesComplex

/-!
# The alternating harmonic series and Dirichlet's `η` and `λ` (Duverney §2.5)

Mathlib has `ζ(s)` but neither the sum `∑ (-1)^{i}/(i+1) = ln 2` nor the companion series
`η(s) = ∑ (-1)^{n-1} n^{-s}` and `λ(s) = ∑ (2n+1)^{-s}`. This file proves:
* `tendsto_sum_alternating_harmonic`: the partial sums of `∑ (-1)^i/(i+1)` tend to `ln 2`, by
  Abel's limit theorem, after the pattern of Mathlib's Leibniz series for `π`;
* `dirichletLambda_eq`: `λ(s) = (1 - 2^{-s}) ζ(s)` and `dirichletEta_eq`:
  `η(s) = (1 - 2^{1-s}) ζ(s)` for `Re s > 1`, by splitting `ζ` into odd and even terms;
* `tendsto_dirichletEta_one`: `η(1) = ln 2` as a limit of partial sums;
* `tendsto_riemannZeta_atTop`: `ζ(s) → 1` as real `s → ∞`.
-/

@[expose] public section

open Complex Filter Finset
open scoped Topology

noncomputable section

namespace DLMF.Constants

/-- **The alternating harmonic series** (Duverney (8.8), (2.70)):
`∑_{i<n} (-1)^i/(i+1) → ln 2`, by Abel's limit theorem. -/
theorem tendsto_sum_alternating_harmonic :
    Tendsto (fun n : ℕ => ∑ i ∈ range n, (-1 : ℝ) ^ i / (i + 1)) atTop (𝓝 (Real.log 2)) := by
  obtain ⟨l, h⟩ : ∃ l, Tendsto (fun n : ℕ => ∑ i ∈ range n, (-1 : ℝ) ^ i / (i + 1))
      atTop (𝓝 l) := by
    apply Antitone.tendsto_alternating_series_of_tendsto_zero
    · exact antitone_iff_forall_lt.mpr fun _ _ h => by gcongr
    · simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have abel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt h
  have m : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 := nhdsWithin_le_nhds
  have abel' := abel.mul ((continuous_id.tendsto 1).mono_left m)
  rw [id, mul_one] at abel'
  have hlog : Tendsto (fun x : ℝ => Real.log (1 + x)) (𝓝[<] 1) (𝓝 (Real.log 2)) := by
    have := ((continuous_const.add continuous_id).tendsto (1 : ℝ)).log
      (show (1 : ℝ) + id 1 ≠ 0 by norm_num)
    norm_num at this
    exact this.mono_left m
  have heq : (fun x : ℝ => (∑' n : ℕ, (-1 : ℝ) ^ n / (n + 1) * x ^ n) * id x) =ᶠ[𝓝[<] 1]
      fun x => Real.log (1 + x) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    have hx' : |(-x)| < 1 := by rw [abs_neg, abs_lt]; constructor <;> linarith [hx.1, hx.2]
    have hs := (Real.hasSum_pow_div_log_of_abs_lt_one hx').neg
    rw [sub_neg_eq_add, neg_neg] at hs
    rw [← hs.tsum_eq, id, ← tsum_mul_right]
    congr 1; funext n
    rw [neg_pow, pow_succ]; ring
  exact tendsto_nhds_unique (abel'.congr' heq) hlog ▸ h

/-- Dirichlet's eta function `η(s) = ∑_{n≥1} (-1)^{n-1} n^{-s}` (Duverney (2.69)). -/
def dirichletEta (s : ℂ) : ℂ := ∑' n : ℕ, (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s

/-- Dirichlet's lambda function `λ(s) = ∑_{n≥0} (2n+1)^{-s}` (Duverney (2.74)). -/
def dirichletLambda (s : ℂ) : ℂ := ∑' n : ℕ, 1 / (2 * n + 1 : ℂ) ^ s

/-- `∑ 1/(n+1)^s` converges for `Re s > 1`. -/
lemma summable_one_div_nat_add_one_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ => 1 / (n + 1 : ℂ) ^ s := by
  refine ((Complex.summable_one_div_nat_cpow.mpr hs).comp_injective
    (add_left_injective 1)).congr fun n => ?_
  simp

/-- `ζ(s) = ∑ 1/(n+1)^s` for `Re s > 1`, as a `HasSum`. -/
lemma hasSum_zeta {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) (riemannZeta s) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  exact (summable_one_div_nat_add_one_cpow hs).hasSum

/-- The terms `1/(2n+2)^s = 2^{-s}/(n+1)^s` sum to `2^{-s} ζ(s)`. -/
lemma hasSum_even_terms {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => 1 / (2 * (n : ℂ) + 2) ^ s) (2 ^ (-s) * riemannZeta s) := by
  refine ((hasSum_zeta hs).mul_left (2 ^ (-s))).congr_fun fun n => ?_
  have h : 2 * (n : ℂ) + 2 = ((2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [h, natCast_mul_natCast_cpow, cpow_neg, one_div, one_div, mul_inv]
  push_cast
  ring

/-- `∑ 1/(2n+1)^s` converges for `Re s > 1`. -/
lemma summable_odd_terms {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ => 1 / (2 * (n : ℂ) + 1) ^ s := by
  refine ((hasSum_zeta hs).summable.comp_injective
    (mul_right_injective₀ (two_ne_zero' ℕ))).congr fun n => ?_
  simp only [Function.comp, Nat.cast_mul, Nat.cast_ofNat]

/-- `λ(s) = (1 - 2^{-s}) ζ(s)` for `Re s > 1` (Duverney (2.75)). -/
@[dlmf 25.2.E2]
theorem dirichletLambda_eq {s : ℂ} (hs : 1 < s.re) :
    dirichletLambda s = (1 - 2 ^ (-s)) * riemannZeta s := by
  have hz := hasSum_zeta hs
  have he := hasSum_even_terms hs
  set f : ℕ → ℂ := fun n => 1 / (n + 1 : ℂ) ^ s with hf
  have ho : HasSum (fun k => f (2 * k)) (dirichletLambda s) := by
    refine ((summable_odd_terms hs).hasSum).congr_fun fun k => ?_
    simp only [hf]; push_cast; rfl
  have he' : HasSum (fun k => f (2 * k + 1)) (2 ^ (-s) * riemannZeta s) := by
    refine he.congr_fun fun k => ?_
    simp only [hf]; push_cast; ring_nf
  have := (HasSum.even_add_odd ho he').unique hz
  linear_combination this

/-- The series of `η(s)` converges absolutely to `(1 - 2^{1-s}) ζ(s)` for `Re s > 1`. -/
@[dlmf 25.2.E3]
theorem hasSum_dirichletEta {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s) ((1 - 2 ^ (1 - s)) * riemannZeta s) := by
  set g : ℕ → ℂ := fun n => (-1 : ℂ) ^ n / (n + 1 : ℂ) ^ s with hg
  have ho : HasSum (fun k => g (2 * k)) (dirichletLambda s) := by
    refine ((summable_odd_terms hs).hasSum).congr_fun fun k => ?_
    simp only [hg, pow_mul]; push_cast; ring_nf
  have he : HasSum (fun k => g (2 * k + 1)) (-(2 ^ (-s) * riemannZeta s)) := by
    refine (hasSum_even_terms hs).neg.congr_fun fun k => ?_
    simp only [hg, pow_succ, pow_mul]; push_cast; ring_nf
  have h2 : (2 : ℂ) ^ (1 - s) = 2 * 2 ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ two_ne_zero, cpow_one]
  convert HasSum.even_add_odd ho he using 1
  rw [dirichletLambda_eq hs, h2]
  ring

/-- `η(s) = (1 - 2^{1-s}) ζ(s)` for `Re s > 1` (Duverney (2.71)). -/
theorem dirichletEta_eq {s : ℂ} (hs : 1 < s.re) :
    dirichletEta s = (1 - 2 ^ (1 - s)) * riemannZeta s :=
  (hasSum_dirichletEta hs).tsum_eq

/-- `η(1) = ln 2`, as the limit of the partial sums of the (conditionally convergent) series
(Duverney (2.70)). -/
theorem tendsto_dirichletEta_one :
    Tendsto (fun n : ℕ => ∑ i ∈ range n, (-1 : ℂ) ^ i / (i + 1 : ℂ) ^ (1 : ℂ)) atTop
      (𝓝 (Real.log 2 : ℂ)) := by
  have h := (continuous_ofReal.tendsto _).comp tendsto_sum_alternating_harmonic
  refine h.congr fun n => ?_
  simp [Function.comp]

/-- `ζ(s) → 1` as real `s → ∞` (Duverney (2.73)). -/
theorem tendsto_riemannZeta_atTop :
    Tendsto (fun s : ℝ => riemannZeta s) atTop (𝓝 1) := by
  have hC : Summable fun n : ℕ => 1 / ((n : ℝ) + 2) ^ (2 : ℕ) := by
    have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    refine (this.comp_injective (add_left_injective 2)).congr fun n => ?_
    simp [Function.comp]
  set C := ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ (2 : ℕ)
  have hbound : ∀ᶠ s : ℝ in atTop, ‖riemannZeta s - 1‖ ≤ (2 : ℝ) ^ (2 - s) * C := by
    filter_upwards [eventually_ge_atTop 2] with s hs
    have hs1 : 1 < (s : ℂ).re := by simp; linarith
    have hz := hasSum_zeta hs1
    have ht : HasSum (fun n : ℕ => 1 / ((n + 1 : ℕ) + 1 : ℂ) ^ (s : ℂ)) (riemannZeta s - 1) := by
      have := (hasSum_nat_add_iff' 1).mpr hz
      simpa using this
    have hn (n : ℕ) : ‖1 / ((n + 1 : ℕ) + 1 : ℂ) ^ (s : ℂ)‖ ≤
        (2 : ℝ) ^ (2 - s) * (1 / ((n : ℝ) + 2) ^ (2 : ℕ)) := by
      have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      rw [show (((n + 1 : ℕ) : ℂ) + 1) = (((n : ℝ) + 2 : ℝ) : ℂ) by push_cast; ring, norm_div,
        norm_one, norm_cpow_eq_rpow_re_of_pos hpos, ofReal_re]
      rw [show (2 : ℝ) ^ (2 - s) * (1 / ((n : ℝ) + 2) ^ (2 : ℕ)) =
        ((2 : ℝ) / ((n : ℝ) + 2)) ^ (2 - s) / ((n : ℝ) + 2) ^ s by
          rw [Real.div_rpow (by norm_num) hpos.le, Real.rpow_sub hpos, Real.rpow_two]
          field_simp]
      have h1 : ((2 : ℝ) / ((n : ℝ) + 2)) ^ (2 - s) ≥ 1 := by
        apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity)
        · rw [div_le_one hpos]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
        · linarith
      have h2 : 0 < ((n : ℝ) + 2) ^ s := Real.rpow_pos_of_pos hpos _
      rw [div_le_div_iff_of_pos_right h2]
      exact h1
    calc ‖riemannZeta s - 1‖ = ‖∑' n : ℕ, 1 / ((n + 1 : ℕ) + 1 : ℂ) ^ (s : ℂ)‖ := by
          rw [ht.tsum_eq]
      _ ≤ ∑' n : ℕ, (2 : ℝ) ^ (2 - s) * (1 / ((n : ℝ) + 2) ^ (2 : ℕ)) :=
          tsum_of_norm_bounded (hC.mul_left _).hasSum hn
      _ = (2 : ℝ) ^ (2 - s) * C := tsum_mul_left
  have hlim : Tendsto (fun s : ℝ => (2 : ℝ) ^ (2 - s) * C) atTop (𝓝 0) := by
    have hl : Tendsto (fun s : ℝ => (2 - s) * Real.log 2) atTop atBot := by
      refine Tendsto.atBot_mul_const (Real.log_pos (by norm_num)) ?_
      exact tendsto_atBot_add_const_left atTop 2 tendsto_neg_atTop_atBot
    have h := (Real.tendsto_exp_atBot.comp hl).mul_const C
    rw [zero_mul] at h
    refine h.congr fun s => ?_
    simp only [Function.comp]
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm (Real.log 2)]
  exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm' hbound hlim)

end DLMF.Constants

end
