/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic
public import DLMF.Confluent.Whittaker
public import DLMF.Bessel.Basic
public import DLMF.Bessel.Modified
public import DLMF.Bessel.NeumannSeries
public import DLMF.Gamma.RecipGammaDeriv
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Complex.TaylorSeries
public import DLMFMathlib.Analysis.Complex.TaylorParameter
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp

/-!
# Series expansions (DLMF §§13.11, 13.24)

Bessel-function expansions of `M` and `M_{κ,μ}`. The generating function 13.11.4
for the coefficients `A_s` and 13.24.3 for `p_s^{(μ)}` are included.
The Buchholz generating function has independently proved disk holomorphy and a
parameter differential equation. Its Taylor coefficients have locally uniform bounds
and a differential recurrence; identification of the full Buchholz sum remains open.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology Nat
open DLMF.Hypergeometric
open DLMF.Bessel

noncomputable section

namespace DLMF.Confluent

/-- Coefficients of the Bessel-function expansion DLMF 13.11.1. -/
noncomputable def kummerBesselISeriesCoeff (a b : ℂ) (k : ℕ) : ℂ :=
  poch (2 * a - 1) k * poch (2 * a - b) k / (poch b k * k !) * (a - 1 / 2 + k)

/-- The coefficient identity behind DLMF 13.11.1: the Cauchy coefficients of the Bessel
expansion reproduce `(a)_N 4^N / ((b)_N N!)`. -/
theorem kummerBesselISeriesCoeff_sum {a b : ℂ} (hν : ∀ j : ℕ, a - 1 / 2 + j ≠ 0) (hb : ∀ k : ℕ, b ≠ -k)
    (N : ℕ) :
    Gamma (a - 1 / 2) * ∑ k ∈ Finset.range (N + 1), (if k ≤ N then kummerBesselISeriesCoeff a b k *
      (poch (2 * (a - 1 / 2 + k + 1) + ((N - k : ℕ) : ℂ) - 1) (N - k) /
        ((N - k)! * Gamma (a - 1 / 2 + k + 1 + ((N - k : ℕ) : ℂ)))) else 0) =
      kummerMCoeff a b N * 4 ^ N := by
  set ν := a - 1 / 2 with hνdef
  have hpb : ∀ n, poch b n ≠ 0 := poch_ne_zero_of_not_neg_nat hb
  have hGN : ∀ n : ℕ, Gamma (ν + n + 1) = Gamma ν * poch ν (n + 1) := by
    intro n
    rw [add_assoc, show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring]
    exact Gamma_add_nat_eq_mul_poch hν _
  have hpν : ∀ n, poch ν n ≠ 0 := poch_ne_zero_of_not_neg_nat
    (fun k h => hν k (by rw [h]; ring))
  have hΓν : Gamma ν ≠ 0 := by
    have := Gamma_add_nat_ne_zero_of_ne (l := ν) (fun n h => hν n (by rw [h]; ring)) 0
    simpa using this
  have hterm : ∀ k ∈ Finset.range (N + 1), (if k ≤ N then kummerBesselISeriesCoeff a b k *
      (poch (2 * (ν + k + 1) + ((N - k : ℕ) : ℂ) - 1) (N - k) /
        ((N - k)! * Gamma (ν + k + 1 + ((N - k : ℕ) : ℂ)))) else 0) =
      vwpTerm (2 * ν) (2 * a - b) N k / (2 * N ! * poch b N * Gamma (ν + N + 1)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    simp only [show k ≤ N by omega, ↓reduceIte]
    obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le (show k ≤ N by omega)
    simp only [kummerBesselISeriesCoeff, vwpTerm, Nat.add_sub_cancel_left]
    rw [← hνdef, show 2 * (ν + k + 1) + (K : ℂ) - 1 = 2 * ν + ((k + K : ℕ) : ℂ) + k + 1 by push_cast; ring,
      show ν + k + 1 + (K : ℂ) = ν + ((k + K : ℕ) : ℂ) + 1 by push_cast; ring,
      show 2 * ν + 1 - (2 * a - b) + k = b + k by rw [hνdef]; ring,
      show 2 * a - 1 = 2 * ν by rw [hνdef]; ring, poch_add b k K]
    have hfac := Nat.choose_mul_factorial_mul_factorial (show k ≤ k + K by omega)
    rw [Nat.add_sub_cancel_left] at hfac
    have hfac' : ((k + K).choose k : ℂ) * k ! * K ! = (k + K)! := by exact_mod_cast hfac
    have hk0 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hK0 : (K ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hpbk := hpb k
    have hpbK : poch (b + k) K ≠ 0 := by
      intro h; apply hpb (k + K); rw [poch_add, h, mul_zero]
    have hG : Gamma (ν + ((k + K : ℕ) : ℂ) + 1) ≠ 0 := by
      rw [hGN]; exact mul_ne_zero hΓν (hpν _)
    have hch : ((k + K).choose k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
    rw [← hfac']
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, sum_range_vwpTerm, poch_two_mul_two_mul_add_one, hGN,
    show ν + 1 / 2 = a by rw [hνdef]; ring]
  have hN0 : (N ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have := hpb N
  have := hpν (N + 1)
  simp only [kummerMCoeff]
  field_simp


/-- Geometric growth of `kummerBesselISeriesCoeff`. -/
theorem exists_norm_kummerBesselISeriesCoeff_le (a : ℂ) {b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    ∃ C X : ℝ, 0 ≤ C ∧ 1 ≤ X ∧ ∀ k, ‖kummerBesselISeriesCoeff a b k‖ ≤ C * X ^ k := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_recip_Gamma_add_nat_le b
  have hbi : ∀ i : ℕ, b + i ≠ 0 := fun i h => hb i (by rw [← sub_eq_zero, sub_neg_eq_add, h])
  refine ⟨‖Gamma b‖ * C * Real.exp (‖2 * a - 1‖ + ‖2 * a - b‖ + ‖a - 1 / 2‖),
    2 * Real.exp 1 ^ 3, by positivity, ?_, fun k => ?_⟩
  · have := Real.add_one_le_exp 1
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (2 : ℝ) ≤ Real.exp 1) 3]
  have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have h1 := norm_poch_le_factorial_mul_exp (2 * a - 1) k
  have h2 := norm_poch_le_factorial_mul_exp (2 * a - b) k
  have hG := Gamma_add_nat_eq_mul_poch hbi k
  have hpb : poch b k ≠ 0 := poch_ne_zero_of_not_neg_nat hb k
  have h3 : ‖(poch b k)⁻¹‖ ≤ ‖Gamma b‖ * (C * (2 ^ k / k !)) := by
    have hΓb : Gamma b ≠ 0 := by simpa using Gamma_add_nat_ne_zero_of_ne (l := b) hb 0
    rw [show (poch b k)⁻¹ = Gamma b * (Gamma (b + k))⁻¹ by rw [hG]; field_simp, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC k) (norm_nonneg _)
  have h4 : ‖a - 1 / 2 + k‖ ≤ Real.exp (‖a - 1 / 2‖ + k) := by
    calc ‖a - 1 / 2 + k‖ ≤ ‖a - 1 / 2‖ + k := by
            refine (norm_add_le _ _).trans ?_; simp
      _ ≤ _ := by linarith [Real.add_one_le_exp (‖a - 1 / 2‖ + k)]
  simp only [kummerBesselISeriesCoeff]
  rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv (k ! : ℂ),
    Complex.norm_natCast]
  calc ‖poch (2 * a - 1) k‖ * ‖poch (2 * a - b) k‖ * (‖(poch b k)⁻¹‖ * (k ! : ℝ)⁻¹) *
        ‖a - 1 / 2 + k‖
      ≤ (k ! * Real.exp (‖2 * a - 1‖ + k)) * (k ! * Real.exp (‖2 * a - b‖ + k)) *
          ((‖Gamma b‖ * (C * (2 ^ k / k !))) * (k ! : ℝ)⁻¹) * Real.exp (‖a - 1 / 2‖ + k) := by
        gcongr
    _ = ‖Gamma b‖ * C * 2 ^ k * (Real.exp (‖2 * a - 1‖ + k) * Real.exp (‖2 * a - b‖ + k) *
          Real.exp (‖a - 1 / 2‖ + k)) := by
        field_simp
    _ = _ := by
        have e1 : Real.exp (‖2 * a - 1‖ + k) * Real.exp (‖2 * a - b‖ + k) *
            Real.exp (‖a - 1 / 2‖ + k) =
            Real.exp (‖2 * a - 1‖ + ‖2 * a - b‖ + ‖a - 1 / 2‖) * (Real.exp 1 ^ 3) ^ k := by
          rw [← pow_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1; push_cast; ring
        rw [e1, mul_pow]; ring


/-- Entire form of DLMF 13.11.1: `M(a,b,4w) = Γ(a-½) e^{2w} ∑ₖ cₖ wᵏ ₀F̃₁(;a+½+k;w²)`. -/
theorem kummerM_four_mul_eq_tsum {a b : ℂ} (hν : ∀ j : ℕ, a - 1 / 2 + j ≠ 0)
    (hb : ∀ k : ℕ, b ≠ -k) (w : ℂ) :
    kummerM a b (4 * w) = Gamma (a - 1 / 2) * exp (2 * w) *
      ∑' k : ℕ, kummerBesselISeriesCoeff a b k *
        (w ^ k * regularizedHGFun (∅ : Multiset ℂ) {a - 1 / 2 + k + 1} (w ^ 2)) := by
  set ν := a - 1 / 2 with hνdef
  have hc : ∀ k j : ℕ, ν + k + 1 + j ≠ 0 := fun k j => by
    have := hν (k + 1 + j)
    push_cast at this
    rwa [show ν + k + 1 + j = ν + (k + 1 + j) by ring]
  set d : ℕ → ℕ → ℂ := fun k K =>
    poch (2 * (ν + k + 1) + K - 1) K / (K ! * Gamma (ν + k + 1 + K)) with hd
  set f : ℕ × ℕ → ℂ := fun p => kummerBesselISeriesCoeff a b p.1 * w ^ p.1 * (d p.1 p.2 * w ^ p.2)
    with hf
  have hinner : ∀ k, HasSum (fun K => f (k, K)) (kummerBesselISeriesCoeff a b k * w ^ k *
      (regularizedHGFun (∅ : Multiset ℂ) {ν + k + 1} (w ^ 2) * exp (2 * w))) := fun k =>
    (hasSum_regularized0F1_mul_exp (hc k) w).mul_left _
  obtain ⟨C1, X1, hC1, hX1, h1⟩ := exists_norm_kummerBesselISeriesCoeff_le a hb
  obtain ⟨C2, X2, hC2, hX2, h2⟩ := exists_norm_regularized0F1_mul_exp_coeff_le ν
  set Y := X1 * X2 * (‖w‖ + 1) with hY
  have hsum : Summable fun p => ‖f p‖ := by
    have hg := Real.summable_pow_div_factorial Y
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      ((hg.mul_of_nonneg hg (fun _ => by positivity) (fun _ => by positivity)).mul_left (C1 * C2))
    obtain ⟨k, K⟩ := p
    simp only [hf, norm_mul, norm_pow]
    have hfac : ((k ! : ℝ) * K !) ≤ (k + K)! := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _)
        (Nat.factorial_mul_factorial_dvd_factorial_add k K)
    have hk0 : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
    have hK0 : (0 : ℝ) < K ! := by exact_mod_cast Nat.factorial_pos K
    have hY1 : X1 * X2 * ‖w‖ ≤ Y := by
      rw [hY]; gcongr; linarith
    have hY2 : X2 * ‖w‖ ≤ Y := by
      rw [hY]
      calc X2 * ‖w‖ ≤ X1 * X2 * ‖w‖ := by
            have : 0 ≤ X2 * ‖w‖ := by positivity
            nlinarith
        _ ≤ _ := hY1
    calc ‖kummerBesselISeriesCoeff a b k‖ * ‖w‖ ^ k * (‖d k K‖ * ‖w‖ ^ K)
        ≤ C1 * X1 ^ k * ‖w‖ ^ k * (C2 * (X2 ^ (k + K) / (k + K)!) * ‖w‖ ^ K) := by
          gcongr
          · exact h1 k
          · exact h2 k K
      _ = C1 * C2 * ((X1 * X2 * ‖w‖) ^ k * (X2 * ‖w‖) ^ K / (k + K)!) := by
          rw [pow_add, mul_pow, mul_pow, mul_pow]; ring
      _ ≤ C1 * C2 * (Y ^ k * Y ^ K / ((k ! : ℝ) * K !)) := by
          gcongr
      _ = C1 * C2 * (Y ^ k / k ! * (Y ^ K / K !)) := by
          field_simp
  have hT := hsum.of_norm.hasSum
  have hk := hT.prod_fiberwise hinner
  have hN := hasSum_sum_range_fiber (d := 1) one_pos hT
  have hM : HasSum (fun N => kummerMCoeff a b N * (4 * w) ^ N) (kummerM a b (4 * w)) :=
    (hasFPowerSeriesOnBall_kummerM hb).hasSum_mul_pow (by simp)
  have hM' : HasSum (fun N => kummerMCoeff a b N * (4 * w) ^ N) (Gamma ν * ∑' p, f p) := by
    refine (hN.mul_left (Gamma ν)).congr_fun fun N => ?_
    rw [mul_pow, ← mul_assoc, ← kummerBesselISeriesCoeff_sum hν hb N, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [one_mul]
    split_ifs with hkN
    · simp only [hf, hd]
      rw [show w ^ N = w ^ k * w ^ (N - k) by rw [← pow_add, Nat.add_sub_cancel' hkN]]
      ring
    · simp
  have heq := hM.unique hM'
  have hE : exp (2 * w) ≠ 0 := exp_ne_zero _
  have hg : HasSum (fun k => kummerBesselISeriesCoeff a b k *
      (w ^ k * regularizedHGFun (∅ : Multiset ℂ) {ν + k + 1} (w ^ 2)))
      ((∑' p, f p) / exp (2 * w)) := by
    refine (hk.div_const (exp (2 * w))).congr_fun fun k => ?_
    field_simp
  rw [heq, hg.tsum_eq]
  field_simp


/-- Conversion of the entire form at `w = z/4` into modified Bessel functions. -/
theorem tsum_kummerBesselISeriesCoeff_besselI {a b z : ℂ} (hz : z ≠ 0) (σ : ℂ) (hσ : σ ^ 2 = 1) :
    ∑' s : ℕ, kummerBesselISeriesCoeff a b s * ((σ * (z / 4)) ^ s *
      regularizedHGFun (∅ : Multiset ℂ) {a - 1 / 2 + s + 1} ((σ * (z / 4)) ^ 2)) =
      (z / 4) ^ (-(a - 1 / 2)) * ∑' s : ℕ, σ ^ s * kummerBesselISeriesCoeff a b s *
        besselI (a - 1 / 2 + s) (z / 2) := by
  have hw : z / 4 ≠ 0 := div_ne_zero hz (by norm_num)
  have hI : ∀ s : ℕ, besselI (a - 1 / 2 + s) (z / 2) = (z / 4) ^ (a - 1 / 2) *
      ((z / 4) ^ s * regularizedHGFun (∅ : Multiset ℂ) {a - 1 / 2 + s + 1} ((z / 4) ^ 2)) := by
    intro s
    rw [besselI_add_nat (div_ne_zero hz two_ne_zero), show z / 2 / 2 = z / 4 by ring, one_mul]
  simp_rw [hI]
  have h : ∀ s : ℕ, σ ^ s * kummerBesselISeriesCoeff a b s * ((z / 4) ^ (a - 1 / 2) * ((z / 4) ^ s *
      regularizedHGFun (∅ : Multiset ℂ) {a - 1 / 2 + s + 1} ((z / 4) ^ 2))) =
      (z / 4) ^ (a - 1 / 2) * (kummerBesselISeriesCoeff a b s * ((σ * (z / 4)) ^ s *
        regularizedHGFun (∅ : Multiset ℂ) {a - 1 / 2 + s + 1} ((σ * (z / 4)) ^ 2))) := by
    intro s
    rw [mul_pow σ (z / 4) 2, hσ, one_mul, mul_pow]
    ring
  simp_rw [h, tsum_mul_left, ← mul_assoc, cpow_neg]
  rw [inv_mul_cancel₀ (by rw [cpow_def_of_ne_zero hw]; exact exp_ne_zero _), one_mul]

@[dlmf 13.11.E1]
theorem kummerM_besselI_series {a b z : ℂ}
    (ha : ∀ k : ℕ, a + 1 / 2 ≠ -k) (ha0 : a ≠ 1 / 2) (hb : ∀ k : ℕ, b ≠ -k) (hz : z ∈ slitPlane) :
    kummerM a b z =
      Gamma (a - 1 / 2) * exp (z / 2) * (z / 4) ^ (1 / 2 - a) *
        ∑' s : ℕ, poch (2 * a - 1) s * poch (2 * a - b) s / (poch b s * s.factorial) *
          (a - 1 / 2 + s) * besselI (a - 1 / 2 + s) (z / 2) := by
  have hν : ∀ j : ℕ, a - 1 / 2 + j ≠ 0 := by
    intro j
    rcases j with _ | i
    · intro h; apply ha0; push_cast at h; linear_combination h
    · intro h; apply ha i; push_cast at h; linear_combination h
  have hz0 := slitPlane_ne_zero hz
  have core := kummerM_four_mul_eq_tsum hν hb (z / 4)
  rw [show 4 * (z / 4) = z by ring, show 2 * (z / 4) = z / 2 by ring] at core
  have hc := tsum_kummerBesselISeriesCoeff_besselI (a := a) (b := b) hz0 1 (by norm_num)
  simp only [one_mul, one_pow] at hc
  rw [core, hc, show (1 : ℂ) / 2 - a = -(a - 1 / 2) by ring]
  simp only [kummerBesselISeriesCoeff]
  ring

@[dlmf 13.11.E2]
theorem kummerM_besselI_series_complement {a b z : ℂ}
    (hab : ∀ k : ℕ, b - a + 1 / 2 ≠ -k) (hab0 : b - a ≠ 1 / 2) (hb : ∀ k : ℕ, b ≠ -k)
    (hz : z ∈ slitPlane) :
    kummerM a b z =
      Gamma (b - a - 1 / 2) * exp (z / 2) * (z / 4) ^ (a - b + 1 / 2) *
        ∑' s : ℕ, (-1 : ℂ) ^ s * poch (2 * b - 2 * a - 1) s * poch (b - 2 * a) s *
          (b - a - 1 / 2 + s) / (poch b s * s.factorial) *
          besselI (b - a - 1 / 2 + s) (z / 2) := by
  have hν : ∀ j : ℕ, b - a - 1 / 2 + j ≠ 0 := by
    intro j
    rcases j with _ | i
    · intro h; apply hab0; push_cast at h; linear_combination h
    · intro h; apply hab i; push_cast at h; linear_combination h
  have hz0 := slitPlane_ne_zero hz
  have core := kummerM_four_mul_eq_tsum hν hb ((-1) * (z / 4))
  rw [show 4 * ((-1) * (z / 4)) = -z by ring, show 2 * ((-1) * (z / 4)) = -(z / 2) by ring] at core
  have hc := tsum_kummerBesselISeriesCoeff_besselI (a := b - a) (b := b) hz0 (-1) (by norm_num)
  rw [kummerM_kummer_transform hb, core, hc, show a - b + 1 / 2 = -(b - a - 1 / 2) by ring]
  have hT : ∑' s : ℕ, (-1 : ℂ) ^ s * kummerBesselISeriesCoeff (b - a) b s *
      besselI (b - a - 1 / 2 + s) (z / 2) =
      ∑' s : ℕ, (-1 : ℂ) ^ s * poch (2 * b - 2 * a - 1) s * poch (b - 2 * a) s *
        (b - a - 1 / 2 + s) / (poch b s * s.factorial) * besselI (b - a - 1 / 2 + s) (z / 2) := by
    refine tsum_congr fun s => ?_
    simp only [kummerBesselISeriesCoeff]
    rw [show 2 * (b - a) - 1 = 2 * b - 2 * a - 1 by ring, show 2 * (b - a) - b = b - 2 * a by ring]
    ring
  rw [hT]
  have hexp : exp z * exp (-(z / 2)) = exp (z / 2) := by
    rw [← Complex.exp_add]; ring_nf
  linear_combination (Gamma (b - a - 1 / 2) * (z / 4) ^ (-(b - a - 1 / 2)) *
    ∑' s : ℕ, (-1 : ℂ) ^ s * poch (2 * b - 2 * a - 1) s * poch (b - 2 * a) s *
        (b - a - 1 / 2 + s) / (poch b s * s.factorial) * besselI (b - a - 1 / 2 + s) (z / 2)) * hexp

/-- Coefficients `A_s` in DLMF 13.11.3–13.11.4. -/
@[dlmf 13.11.E4]
def besselExpansionCoeff (a b : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => 0
  | 2 => b / 2
  | n + 3 =>
    ((n + 1 + b) * besselExpansionCoeff a b (n + 1) +
      (2 * a - b) * besselExpansionCoeff a b n) / (n + 3 : ℂ)

section BesselExpansion

open Finset

/-- Terms of `[tᴺ] (1-t)^{-a} (1+t)^{a-b} = ∑_{m+r=N} (a)_m 2^m (-1)^r (b+m)_r / (m! r!)`. -/
def besselExpansionTerm (a b : ℂ) (m r : ℕ) : ℂ :=
  poch a m * 2 ^ m * (-1) ^ r * poch (b + m) r / (m ! * r !)

/-- `[tᴺ] (1-t)^{-a} (1+t)^{a-b}`, the coefficients of `e^{-(b-2a)t} ∑ A_s t^s`. -/
def besselExpansionB (a b : ℂ) (N : ℕ) : ℂ :=
  ∑ m ∈ range (N + 1), besselExpansionTerm a b m (N - m)

theorem besselExpansionB_zero (a b : ℂ) : besselExpansionB a b 0 = 1 := by
  simp [besselExpansionB, besselExpansionTerm, poch_zero]

theorem besselExpansionB_one (a b : ℂ) :
    besselExpansionB a b 1 = (2 * a - b) * besselExpansionB a b 0 := by
  simp [besselExpansionB, besselExpansionTerm, sum_range_succ, poch_zero, poch_one]
  ring

/-- The recurrence `(N+2) B_{N+2} = (2a-b) B_{N+1} + (N+b) B_N` of the coefficients of
`(1-t)^{-a} (1+t)^{a-b}`, by telescoping in the summation index. -/
theorem besselExpansionB_rec (a b : ℂ) (N : ℕ) :
    (N + 2) * besselExpansionB a b (N + 2) =
      (2 * a - b) * besselExpansionB a b (N + 1) + (N + b) * besselExpansionB a b N := by
  set T := besselExpansionTerm a b
  set G : ℕ → ℂ := fun m => if m = 0 then 0 else -2 * (a + (m - 1 : ℕ)) * T (m - 1) (N + 2 - m)
    with hG
  have hterm : ∀ m ∈ range (N + 1), (N + 2) * T m (N + 2 - m) - (2 * a - b) * T m (N + 1 - m) -
      (N + b) * T m (N - m) = G (m + 1) - G m := by
    intro m hm
    obtain ⟨r, rfl⟩ : ∃ r, N = m + r := ⟨N - m, by simp at hm; omega⟩
    rw [show m + r + 2 - m = r + 2 by omega, show m + r + 1 - m = r + 1 by omega,
      show m + r - m = r by omega]
    simp only [hG, T, besselExpansionTerm, Nat.add_sub_cancel, show m + 1 ≠ 0 by omega,
      ite_false, show m + r + 2 - (m + 1) = r + 1 by omega]
    rcases m with _ | j
    · simp only [ite_true, Nat.cast_zero, add_zero, poch_zero, pow_zero, Nat.factorial_zero,
        Nat.cast_one, one_mul, zero_add]
      rw [show r + 2 = r + 1 + 1 from rfl, poch_succ b (r + 1), poch_succ b r]
      simp only [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      push_cast
      have h1 : (r : ℂ) + 1 ≠ 0 := by norm_cast
      have h2 : (r : ℂ) + 1 + 1 ≠ 0 := by norm_cast
      field_simp
      ring
    · simp only [show j + 1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel,
        show j + 1 + r + 2 - (j + 1) = r + 2 by omega]
      rw [show (b + ((j + 1 : ℕ) : ℂ)) = b + j + 1 by push_cast; ring,
        show r + 2 = r + 1 + 1 from rfl,
        poch_succ a j, poch_succ (b + j + 1) (r + 1), poch_succ (b + j + 1) r,
        poch_succ (b + j) (r + 1), poch_succ_left (b + j) r]
      simp only [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      push_cast
      have h1 : (r : ℂ) + 1 ≠ 0 := by norm_cast
      have h2 : (r : ℂ) + 1 + 1 ≠ 0 := by norm_cast
      have h3 : (j : ℂ) + 1 ≠ 0 := by norm_cast
      field_simp
      ring
  have htel := Finset.sum_range_sub G (N + 1)
  rw [← Finset.sum_congr rfl hterm] at htel
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at htel
  simp only [besselExpansionB]
  rw [sum_range_succ _ (N + 2), sum_range_succ _ (N + 1), sum_range_succ _ (N + 1)]
  have hG0 : G 0 = 0 := by simp [hG]
  rw [hG0, sub_zero] at htel
  simp only [hG, show N + 1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel,
    show N + 2 - (N + 1) = 1 by omega] at htel
  rw [show N + 2 - (N + 2) = 0 by omega, show N + 2 - (N + 1) = 1 by omega,
    show N + 1 - (N + 1) = 0 by omega]
  have hb : (N + 2) * T (N + 2) 0 + (N + 2) * T (N + 1) 1 - (2 * a - b) * T (N + 1) 0 =
      2 * (a + N) * T N 1 := by
    simp only [T, besselExpansionTerm, poch_zero, poch_one, pow_zero, pow_one,
      Nat.factorial_zero, Nat.cast_one, mul_one, poch_succ a (N + 1), poch_succ a N]
    simp only [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    push_cast
    have h1 : (N : ℂ) + 1 ≠ 0 := by norm_cast
    have h2 : (N : ℂ) + 1 + 1 ≠ 0 := by norm_cast
    field_simp
    ring
  linear_combination htel + hb

open PowerSeries in
/-- Coefficient form of the formal first-order equation `(1-X²) f' = (p + qX + rX²) f`. -/
theorem besselExpansion_formalODE_iff (f : ℕ → ℂ) (p q r : ℂ) :
    (1 - X ^ 2) * d⁄dX (mk f) = (C p + C q * X + C r * X ^ 2) * mk f ↔
      f 1 = p * f 0 ∧ 2 * f 2 = p * f 1 + q * f 0 ∧
        ∀ n : ℕ, (n + 3) * f (n + 3) - (n + 1) * f (n + 1) =
          p * f (n + 2) + q * f (n + 1) + r * f n := by
  have hc : ∀ n, coeff n ((1 - X ^ 2) * d⁄dX (mk f)) =
      coeff n (d⁄dX (mk f)) - if 2 ≤ n then coeff (n - 2) (d⁄dX (mk f)) else 0 := by
    intro n
    rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul']
  have hd : ∀ n, coeff n ((C p + C q * X + C r * X ^ 2) * mk f) =
      p * f n + (if 1 ≤ n then q * f (n - 1) else 0) + (if 2 ≤ n then r * f (n - 2) else 0) := by
    intro n
    rw [add_mul, add_mul, map_add, map_add, coeff_C_mul, coeff_mk, mul_assoc, coeff_C_mul,
      mul_assoc, coeff_C_mul, coeff_X_pow_mul', ← pow_one (X : PowerSeries ℂ), coeff_X_pow_mul']
    simp only [coeff_mk]
    split_ifs <;> ring
  constructor
  · intro h
    have e := fun n => congrArg (coeff n) h
    refine ⟨?_, ?_, fun n => ?_⟩
    · have := e 0; rw [hc, hd] at this; simpa [coeff_derivative] using this
    · have := e 1; rw [hc, hd] at this
      simp [coeff_derivative] at this; linear_combination this
    · have := e (n + 2); rw [hc, hd] at this
      simp [coeff_derivative] at this;
      linear_combination this
  · rintro ⟨h0, h1, h2⟩
    ext n
    rw [hc, hd]
    rcases n with _ | _ | n
    · simpa [coeff_derivative] using h0
    · simp [coeff_derivative]; linear_combination h1
    · simp [coeff_derivative]; linear_combination h2 n

open PowerSeries in
/-- The formal exponential `e^{cX}` satisfies `(e^{cX})' = c e^{cX}`. -/
theorem besselExpansion_formal_exp_deriv (c : ℂ) :
    d⁄dX (mk fun n => c ^ n / (n ! : ℂ)) = C c * mk fun n => c ^ n / (n ! : ℂ) := by
  ext n
  rw [coeff_derivative, coeff_mk, coeff_C_mul, coeff_mk, Nat.factorial_succ]
  push_cast
  have : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h1 : (n : ℂ) + 1 ≠ 0 := by norm_cast
  field_simp
  ring

open PowerSeries in
/-- `e^{cX} e^{dX} = e^{(c+d)X}` for formal exponentials. -/
theorem besselExpansion_formal_exp_mul (c d : ℂ) :
    (mk fun n => c ^ n / (n ! : ℂ)) * (mk fun n => d ^ n / (n ! : ℂ)) =
      mk fun n => (c + d) ^ n / (n ! : ℂ) := by
  have h : ∀ c : ℂ, (mk fun n => c ^ n / (n ! : ℂ)) = rescale c (exp ℂ) := by
    intro c; ext n; simp [coeff_rescale, coeff_exp, div_eq_mul_inv]
  rw [h, h, h, exp_mul_exp_eq_exp_add]

open PowerSeries in
/-- `e^{0X} = 1` for formal exponentials. -/
theorem besselExpansion_formal_exp_zero : (mk fun n => (0 : ℂ) ^ n / (n ! : ℂ)) = 1 := by
  ext n; rcases n with _ | n <;> simp [coeff_one]

open PowerSeries in
/-- Uniqueness for the formal equation `(1-X²) f' = (p + qX + rX²) f` given `f(0)`. -/
theorem besselExpansion_formalODE_unique {u v : PowerSeries ℂ} {p q r : ℂ}
    (hu : (1 - X ^ 2) * d⁄dX u = (C p + C q * X + C r * X ^ 2) * u)
    (hv : (1 - X ^ 2) * d⁄dX v = (C p + C q * X + C r * X ^ 2) * v)
    (h0 : coeff 0 u = coeff 0 v) : u = v := by
  set g : ℕ → ℂ := fun n => coeff n u - coeff n v with hgdef
  have hg : mk g = u - v := by ext n; simp [g]
  have hode : (1 - X ^ 2) * d⁄dX (mk g) = (C p + C q * X + C r * X ^ 2) * mk g := by
    rw [hg, map_sub, mul_sub, mul_sub, hu, hv]
  obtain ⟨h1, h2, h3⟩ := (besselExpansion_formalODE_iff g p q r).1 hode
  have hz : ∀ n, g n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | _ | _ | n
      · simp [g, h0]
      · rw [h1, ih 0 (by omega), mul_zero]
      · have := h2; rw [ih 1 (by omega), ih 0 (by omega)] at this
        simpa using this
      · have h := h3 n
        rw [ih (n + 2) (by omega), ih (n + 1) (by omega), ih n (by omega)] at h
        have hn : (n : ℂ) + 3 ≠ 0 := by norm_cast
        have : ((n : ℂ) + 3) * g (n + 3) = 0 := by linear_combination h
        exact (mul_eq_zero.mp this).resolve_left hn
  ext n
  have := hz n
  simp only [g, sub_eq_zero] at this
  exact this

open PowerSeries in
/-- The recurrence 13.11.4 for `A_s` as the formal equation `(1-X²) A' = (bX + (2a-b)X²) A`. -/
theorem besselExpansionCoeff_formalODE (a b : ℂ) :
    (1 - X ^ 2) * d⁄dX (mk (besselExpansionCoeff a b)) =
      (C 0 + C b * X + C (2 * a - b) * X ^ 2) * mk (besselExpansionCoeff a b) := by
  refine (besselExpansion_formalODE_iff _ 0 b (2 * a - b)).2 ⟨by simp [besselExpansionCoeff],
    by simp [besselExpansionCoeff]; ring, fun n => ?_⟩
  simp only [besselExpansionCoeff]
  have hn : (n : ℂ) + 3 ≠ 0 := by norm_cast
  field_simp
  ring

open PowerSeries in
/-- The formal equation `(1-X²) B' = ((2a-b) + bX) B` of `(1-t)^{-a} (1+t)^{a-b}`. -/
theorem besselExpansionB_formalODE (a b : ℂ) :
    (1 - X ^ 2) * d⁄dX (mk (besselExpansionB a b)) =
      (C (2 * a - b) + C b * X + C 0 * X ^ 2) * mk (besselExpansionB a b) := by
  refine (besselExpansion_formalODE_iff _ (2 * a - b) b 0).2
    ⟨besselExpansionB_one a b, ?_, fun n => ?_⟩
  · have := besselExpansionB_rec a b 0
    push_cast at this
    linear_combination this
  · have := besselExpansionB_rec a b (n + 1)
    push_cast at this
    linear_combination this

open PowerSeries in
/-- `∑ A_s t^s = e^{(b-2a)t} ∑ B_N t^N`. -/
theorem besselExpansionCoeff_eq_mul (a b : ℂ) :
    mk (besselExpansionCoeff a b) =
      mk (besselExpansionB a b) * mk fun n => (b - 2 * a) ^ n / (n ! : ℂ) := by
  refine besselExpansion_formalODE_unique (besselExpansionCoeff_formalODE a b) ?_ ?_
  · rw [Derivation.leibniz, besselExpansion_formal_exp_deriv, smul_eq_mul, smul_eq_mul]
    have hc : (C (2 * a - b) : PowerSeries ℂ) = - C (b - 2 * a) := by
      rw [← map_neg]; congr 1; ring
    have e := besselExpansionB_formalODE a b
    rw [hc] at e ⊢
    simp only [map_zero, zero_mul, add_zero, zero_add] at e ⊢
    linear_combination (mk fun n => (b - 2 * a) ^ n / (n ! : ℂ)) * e
  · simp [coeff_mul, besselExpansionCoeff, besselExpansionB_zero]

open PowerSeries in
/-- The convolution `∑_{s+k=N} A_s (-(b-2a))^k/k!` equals `B_N`. -/
theorem sum_antidiagonal_besselExpansionCoeff (a b : ℂ) (N : ℕ) :
    ∑ p ∈ antidiagonal N, besselExpansionCoeff a b p.1 * ((-(b - 2 * a)) ^ p.2 / (p.2 ! : ℂ)) =
      besselExpansionB a b N := by
  have h := congrArg (fun u => coeff N (u * mk fun n => (-(b - 2 * a)) ^ n / (n ! : ℂ)))
    (besselExpansionCoeff_eq_mul a b)
  simp only [mul_assoc, besselExpansion_formal_exp_mul, add_neg_cancel,
    besselExpansion_formal_exp_zero, mul_one, coeff_mk] at h
  rw [← h, coeff_mul]
  simp [coeff_mk]

/-- Geometric bound on the coefficients `A_s` of DLMF 13.11.3. -/
theorem norm_besselExpansionCoeff_le (a b : ℂ) (n : ℕ) :
    ‖besselExpansionCoeff a b n‖ ≤ (1 + ‖b‖ + ‖2 * a - b‖) ^ n := by
  set M := 1 + ‖b‖ + ‖2 * a - b‖ with hM
  have hM1 : 1 ≤ M := by rw [hM]; linarith [norm_nonneg b, norm_nonneg (2 * a - b)]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | n
    · simp [besselExpansionCoeff]
    · simp [besselExpansionCoeff]; linarith
    · simp only [besselExpansionCoeff, norm_div, Complex.norm_ofNat]
      nlinarith [norm_nonneg b, norm_nonneg (2 * a - b)]
    · simp only [besselExpansionCoeff]
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      have hn3 : ‖((n : ℂ) + 3)‖ = n + 3 := by
        rw [show ((n : ℂ) + 3) = ((n + 3 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
        push_cast; ring
      have hnb : ‖(n : ℂ) + 1 + b‖ ≤ n + 1 + ‖b‖ := by
        calc ‖(n : ℂ) + 1 + b‖ ≤ ‖((n + 1 : ℕ) : ℂ)‖ + ‖b‖ := by
              rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring]; exact norm_add_le _ _
          _ = n + 1 + ‖b‖ := by rw [Complex.norm_natCast]; push_cast; ring
      rw [norm_div, hn3, div_le_iff₀ (by positivity)]
      have hpn : 0 ≤ M ^ n := by positivity
      have hp1 : M ^ (n + 1) ≤ M ^ (n + 3) := pow_le_pow_right₀ hM1 (by omega)
      have hp2 : M ^ (n + 2) ≤ M ^ (n + 3) := pow_le_pow_right₀ hM1 (by omega)
      have hbM : ‖b‖ + ‖2 * a - b‖ ≤ M := by rw [hM]; linarith
      calc ‖((n : ℂ) + 1 + b) * besselExpansionCoeff a b (n + 1) +
            (2 * a - b) * besselExpansionCoeff a b n‖
          ≤ (n + 1 + ‖b‖) * M ^ (n + 1) + ‖2 * a - b‖ * M ^ n := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
            gcongr
        _ ≤ (n + 1) * M ^ (n + 1) + (‖b‖ + ‖2 * a - b‖) * M ^ (n + 1) := by
            have : M ^ n ≤ M ^ (n + 1) := pow_le_pow_right₀ hM1 (by omega)
            nlinarith [norm_nonneg (2 * a - b), norm_nonneg b]
        _ ≤ (n + 1) * M ^ (n + 3) + M * M ^ (n + 1) := by
            gcongr
        _ ≤ M ^ (n + 3) * (n + 3) := by
            rw [← pow_succ']
            have h3 : 0 ≤ M ^ (n + 3) := by positivity
            nlinarith

/-- **DLMF 13.11.3 in branch-free form**: for all `a, b, z`,
`𝐌(a,b,z) = e^{z/2} ∑ₛ Aₛ (z/2)^s ₀F̃₁(;b+s;-(b-2a)z/2)`.

Stronger than DLMF: the printed form `(b-2a)^{(1-b-s)/2} (z/2)^{(1-b+s)/2} J_{b-1+s}(√(2z(b-2a)))`
of each term is this term only when the principal branches of `z` and `b-2a` are compatible
(`regularizedHGFun_besselJ_series`); the form here involves no branches and holds without any
condition on `a`, `b`, `z`. -/
@[dlmf 13.11.E3]
theorem regularizedHGFun_eq_besselExpansion (a b z : ℂ) :
    regularizedHGFun {a} {b} z =
      exp (z / 2) * ∑' s : ℕ, besselExpansionCoeff a b s * (z / 2) ^ s *
        regularizedHGFun (∅ : Multiset ℂ) {b + s} (-((b - 2 * a) * z / 2)) := by
  set c := b - 2 * a with hcdef
  set w := z / 2 with hw
  set y := -(c * z / 2) with hy
  set A := besselExpansionCoeff a b
  set M := 1 + ‖b‖ + ‖2 * a - b‖
  set u : ℕ × ℕ → ℂ := fun p =>
    A p.1 * w ^ p.1 * (regularizedHGFunCoeff (∅ : Multiset ℂ) {b + p.1} p.2 * y ^ p.2) with hu
  obtain ⟨C0, hC0, hC⟩ := exists_norm_regularized0F1Coeff_le (b - 1)
  have hcoef : ∀ s k : ℕ, ‖regularizedHGFunCoeff (∅ : Multiset ℂ) {b + s} k‖ ≤
      C0 * (2 ^ s / s !) * (2 ^ k / k !) := by
    intro s k
    have := hC s k
    rwa [show b - 1 + s + 1 = b + s by ring] at this
  have hsum : Summable fun p => ‖u p‖ := by
    have hg1 := Real.summable_pow_div_factorial (2 * M * ‖w‖)
    have hg2 := Real.summable_pow_div_factorial (2 * ‖y‖)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      ((hg1.mul_of_nonneg hg2 (fun _ => by positivity) (fun _ => by positivity)).mul_left C0)
    obtain ⟨s, k⟩ := p
    simp only [hu, norm_mul, norm_pow]
    calc ‖A s‖ * ‖w‖ ^ s * (‖regularizedHGFunCoeff (∅ : Multiset ℂ) {b + s} k‖ * ‖y‖ ^ k)
        ≤ M ^ s * ‖w‖ ^ s * (C0 * (2 ^ s / s !) * (2 ^ k / k !) * ‖y‖ ^ k) := by
          gcongr
          · exact norm_besselExpansionCoeff_le a b s
          · exact hcoef s k
      _ = C0 * ((2 * M * ‖w‖) ^ s / s ! * ((2 * ‖y‖) ^ k / k !)) := by
          rw [mul_pow, mul_pow, mul_pow]; ring
  have hT := hsum.of_norm.hasSum
  have hinner : ∀ s, HasSum (fun k => u (s, k))
      (A s * w ^ s * regularizedHGFun (∅ : Multiset ℂ) {b + s} y) := fun s =>
    ((hasFPowerSeriesOnBall_regularized0F1 _).hasSum_mul_pow (by simp)).mul_left _
  have hS := hT.prod_fiberwise hinner
  -- regroup along antidiagonals
  have hN : HasSum (fun N : ℕ => (Gamma (b + N))⁻¹ * w ^ N * besselExpansionB a b N)
      (∑' p, u p) := by
    have hs := hT
    rw [← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd).hasSum_iff] at hs
    refine hs.sigma fun N => ?_
    convert hasSum_fintype _ using 1
    simp only [Function.comp_apply, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
    rw [Finset.sum_coe_sort (antidiagonal N) u, ← sum_antidiagonal_besselExpansionCoeff,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [mem_antidiagonal] at hp
    simp only [hu, regularizedHGFunCoeff_empty, hy]
    rw [← hp, show b + (p.1 : ℂ) + p.2 = b + ((p.1 + p.2 : ℕ) : ℂ) by push_cast; ring, pow_add,
      show -(c * z / 2) = -c * w by rw [hw]; ring, mul_pow]
    ring
  -- Cauchy product with `e^{-z/2}`
  set f : ℕ → ℂ := fun m => regularizedHGFunCoeff {a} {b} m * z ^ m with hf
  set g : ℕ → ℂ := fun r => (-w) ^ r / (r ! : ℂ) with hg
  obtain ⟨Cg, hCg0, hCg⟩ := exists_norm_recip_Gamma_add_nat_le b
  have hfs : Summable fun m => ‖f m‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      ((Real.summable_pow_div_factorial (2 * Real.exp 1 * ‖z‖)).mul_left (Cg * Real.exp ‖a‖))
    have e : f m = poch a m * ((m ! : ℂ)⁻¹ * (Gamma (b + m))⁻¹) * z ^ m := by
      show regularizedHGFunCoeff {a} {b} m * z ^ m = _
      rw [regularizedHGFunCoeff_singleton, div_eq_mul_inv, mul_inv]
    rw [e, norm_mul, norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    have hm : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
    have h1 := norm_poch_le_factorial_mul_exp a m
    have h2 := hCg m
    calc ‖poch a m‖ * ((m ! : ℝ)⁻¹ * ‖(Gamma (b + m))⁻¹‖) * ‖z‖ ^ m
        ≤ (m ! * Real.exp (‖a‖ + m)) * ((m ! : ℝ)⁻¹ * (Cg * (2 ^ m / m !))) * ‖z‖ ^ m := by
          gcongr
      _ = Cg * Real.exp ‖a‖ * ((2 * Real.exp 1 * ‖z‖) ^ m / m !) := by
          rw [Real.exp_add, show Real.exp (m : ℝ) = Real.exp 1 ^ m by
            rw [← Real.exp_nat_mul, mul_one], mul_pow, mul_pow]
          field_simp
  have hgs : Summable fun r => ‖g r‖ := by
    simpa [hg, norm_div, norm_pow] using Real.summable_pow_div_factorial ‖-w‖
  have hfsum : ∑' m, f m = regularizedHGFun {a} {b} z := (regularizedHGFun_eq_tsum _ _ z).symm
  have hgsum : ∑' r, g r = exp (-w) := by
    have := NormedSpace.expSeries_div_hasSum_exp (-w)
    rw [← Complex.exp_eq_exp_ℂ] at this
    exact this.tsum_eq
  have hcauchy := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfs hgs
  have hterm : ∀ N, ∑ p ∈ antidiagonal N, f p.1 * g p.2 =
      (Gamma (b + N))⁻¹ * w ^ N * besselExpansionB a b N := by
    intro N
    rw [besselExpansionB, show ∑ m ∈ range (N + 1), besselExpansionTerm a b m (N - m) =
      ∑ p ∈ antidiagonal N, besselExpansionTerm a b p.1 p.2 from
        (Finset.Nat.sum_antidiagonal_eq_sum_range_succ _ N).symm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [mem_antidiagonal] at hp
    have hG := DLMF.Gamma.poch_mul_recip_Gamma_add_nat (b + p.1) p.2
    rw [add_assoc, ← Nat.cast_add, hp] at hG
    simp only [hf, hg, regularizedHGFunCoeff_singleton, besselExpansionTerm]
    rw [div_eq_mul_inv (poch a p.1), mul_inv, ← hG, ← hp, pow_add, hw, neg_pow, div_pow, div_pow]
    have h1 : (p.1 ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : (p.2 ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h3 : (2 : ℂ) ^ p.1 ≠ 0 := pow_ne_zero _ two_ne_zero
    field_simp
  simp_rw [hterm] at hcauchy
  rw [hfsum, hgsum, hN.tsum_eq, ← hS.tsum_eq] at hcauchy
  rw [← hcauchy, mul_comm (exp w), mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, mul_one]

/-- Each term of DLMF 13.11.3 in Bessel form reduces to the branch-free term when the branches
of `z` and `b-2a` are compatible. -/
theorem besselExpansion_term_eq_besselJ {b c z : ℂ} (s : ℕ) (hz : z ≠ 0) (hc : c ≠ 0)
    (harg : arg z + arg c ∈ Set.Ioc (-π) π) :
    c ^ ((1 - b - s) / 2) * (z / 2) ^ ((1 - b + s) / 2) *
        besselJ (b - 1 + s) ((2 * z * c) ^ (1 / 2 : ℂ)) =
      (z / 2) ^ s * regularizedHGFun (∅ : Multiset ℂ) {b + s} (-(c * z / 2)) := by
  set x := (2 * z * c) ^ (1 / 2 : ℂ) with hxdef
  have h2zc : 2 * z * c ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hz) hc
  have hx2 : x ^ 2 = 2 * z * c := by
    rw [hxdef, one_div]; exact cpow_ofNat_inv_pow _ 2
  have hx0 : x ≠ 0 := by
    rw [hxdef, cpow_def_of_ne_zero h2zc]; exact exp_ne_zero _
  have hl2 : ∀ w : ℂ, w ≠ 0 → log (2 * w) = Real.log 2 + log w := fun w hw => by
    have := log_ofReal_mul (r := 2) (by norm_num) hw
    simpa using this
  have hlh : ∀ w : ℂ, w ≠ 0 → log (w / 2) = log w - Real.log 2 := fun w hw => by
    have := log_ofReal_mul (r := 1 / 2) (by norm_num) hw
    rw [show ((1 / 2 : ℝ) : ℂ) * w = w / 2 by push_cast; ring, Real.log_div one_ne_zero two_ne_zero,
      Real.log_one] at this
    rw [this]; push_cast; ring
  have him : (log (2 * z * c) * (1 / 2 : ℂ)).im = arg (2 * z * c) / 2 := by
    simp [Complex.mul_im, Complex.log_im]
    ring
  have hlogx : log x = log (2 * z * c) / 2 := by
    rw [hxdef, cpow_def_of_ne_zero h2zc, log_exp]
    · ring
    · rw [him]; linarith [neg_pi_lt_arg (2 * z * c), Real.pi_pos]
    · rw [him]; linarith [arg_le_pi (2 * z * c), Real.pi_pos]
  have hlzc : log (2 * z * c) = Real.log 2 + (log z + log c) := by
    rw [mul_assoc, hl2 _ (mul_ne_zero hz hc), Complex.log_mul hz hc harg]
  rw [besselJ_eq_regularized, show b - 1 + s + 1 = b + s by ring,
    show -(x ^ 2 / 4) = -(c * z / 2) by rw [hx2]; ring, ← mul_assoc]
  congr 1
  rw [cpow_def_of_ne_zero hc, cpow_def_of_ne_zero (div_ne_zero hz two_ne_zero),
    cpow_def_of_ne_zero (div_ne_zero hx0 two_ne_zero), ← cpow_natCast,
    cpow_def_of_ne_zero (div_ne_zero hz two_ne_zero), ← Complex.exp_add, ← Complex.exp_add,
    hlh _ hz, hlh _ hx0, hlogx, hlzc]
  congr 1
  ring

/-- DLMF 13.11.3 as printed, with principal branches. The hypothesis on `arg z + arg (b-2a)` is
needed: at `a = 0.2-0.5i`, `b = 1.4+0.4i`, `z = -1.2+0.3i` (where `Re(b-2a) > 0` but
`arg z + arg (b-2a) > π`) the printed right side is `2.834-3.390i`, while
`𝐌(a,b,z) = 1.185+0.468i`. See `regularizedHGFun_eq_besselExpansion` for the branch-free form. -/
@[dlmf 13.11.E3]
theorem regularizedHGFun_besselJ_series {a b z : ℂ} (hz : z ≠ 0) (hba0 : b - 2 * a ≠ 0)
    (harg : arg z + arg (b - 2 * a) ∈ Set.Ioc (-π) π) :
    regularizedHGFun {a} {b} z =
      exp (z / 2) * ∑' s : ℕ, besselExpansionCoeff a b s *
        (b - 2 * a) ^ ((1 - b - s) / 2) * (z / 2) ^ ((1 - b + s) / 2) *
          besselJ (b - 1 + s) ((2 * z * (b - 2 * a)) ^ (1 / 2 : ℂ)) := by
  rw [regularizedHGFun_eq_besselExpansion]
  congr 1
  refine tsum_congr fun s => ?_
  have h := besselExpansion_term_eq_besselJ (b := b) s hz hba0 harg
  linear_combination (-besselExpansionCoeff a b s) * h

end BesselExpansion

@[dlmf 13.24.E1]
theorem whittakerM_besselI_series {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 2 * μ ≠ -k - 1) (hκ : ∀ k : ℕ, κ + μ ≠ -k - 1) (hκμ : κ + μ ≠ 0)
    (hz : z ∈ slitPlane) :
    whittakerM κ μ z =
      Gamma (κ + μ) * (2 : ℂ) ^ (2 * κ + 2 * μ) * z ^ (1 / 2 - κ) *
        ∑' s : ℕ, (-1 : ℂ) ^ s * poch (2 * κ + 2 * μ) s * poch (2 * κ) s /
          (poch (1 + 2 * μ) s * s.factorial) * (κ + μ + s) *
          besselI (κ + μ + s) (z / 2) := by
  have hz0 := slitPlane_ne_zero hz
  have h := kummerM_besselI_series_complement (a := μ - κ + 1 / 2) (b := 1 + 2 * μ)
    (fun k h => hκ k (by linear_combination h)) (fun h => hκμ (by linear_combination h))
    (fun k h => hμ k (by linear_combination h)) hz
  rw [show 1 + 2 * μ - (μ - κ + 1 / 2) - 1 / 2 = κ + μ by ring,
    show μ - κ + 1 / 2 - (1 + 2 * μ) + 1 / 2 = -(κ + μ) by ring,
    show 2 * (1 + 2 * μ) - 2 * (μ - κ + 1 / 2) - 1 = 2 * κ + 2 * μ by ring,
    show 1 + 2 * μ - 2 * (μ - κ + 1 / 2) = 2 * κ by ring] at h
  rw [whittakerM, h]
  have hT : ∑' s : ℕ, (-1 : ℂ) ^ s * poch (2 * κ + 2 * μ) s * poch (2 * κ) s *
      (κ + μ + s) / (poch (1 + 2 * μ) s * s.factorial) * besselI (κ + μ + s) (z / 2) =
      ∑' s : ℕ, (-1 : ℂ) ^ s * poch (2 * κ + 2 * μ) s * poch (2 * κ) s /
        (poch (1 + 2 * μ) s * s.factorial) * (κ + μ + s) * besselI (κ + μ + s) (z / 2) :=
    tsum_congr fun s => by ring
  rw [hT]
  have e4 : (4 : ℂ) ^ (κ + μ) = (2 : ℂ) ^ (2 * κ + 2 * μ) := by
    rw [show (2 : ℂ) ^ (2 * κ + 2 * μ) = 2 ^ (κ + μ) * 2 ^ (κ + μ) by
      rw [← cpow_add _ _ two_ne_zero]; congr 1; ring]
    rw [show (4 : ℂ) = ((2 : ℝ) : ℂ) * ((2 : ℝ) : ℂ) by push_cast; norm_num,
      mul_cpow_ofReal_nonneg (by norm_num) (by norm_num)]
    push_cast; ring
  have h4 : (z / 4) ^ (-(κ + μ)) = z ^ (-(κ + μ)) * (2 : ℂ) ^ (2 * κ + 2 * μ) := by
    have := div_ofReal_cpow (r := 4) (by norm_num) hz0 (-(κ + μ))
    push_cast at this
    rw [this, cpow_neg (4 : ℂ), div_inv_eq_mul, e4]
  have hzz : z ^ (μ + 1 / 2) * z ^ (-(κ + μ)) = z ^ (1 / 2 - κ) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  have hexp : exp (-z / 2) * exp (z / 2) = 1 := by
    rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
  rw [h4]
  linear_combination (Gamma (κ + μ) * (2 : ℂ) ^ (2 * κ + 2 * μ) *
      (∑' s : ℕ, (-1 : ℂ) ^ s * poch (2 * κ + 2 * μ) s * poch (2 * κ) s /
        (poch (1 + 2 * μ) s * s.factorial) * (κ + μ + s) * besselI (κ + μ + s) (z / 2))) *
      (z ^ (μ + 1 / 2) * z ^ (-(κ + μ)) * hexp + hzz)

/-- Generating function for `p_s^{(μ)}(z)` in DLMF 13.24.3. -/
@[dlmf 13.24.E3]
def whittakerBesselGenerating (μ z t : ℂ) : ℂ :=
  if t = 0 then 1
  else exp (-z / 2 * (cosh t / sinh t - t⁻¹)) * (t / sinh t) ^ (1 - 2 * μ)

@[dlmf 13.24.E3]
def whittakerBesselCoeff (μ z : ℂ) (s : ℕ) : ℂ :=
  iteratedDeriv s (whittakerBesselGenerating μ z) 0 / s.factorial * (-z) ^ s

/-- `sinh t / t`, extended by `1` at the origin, stays within distance `sinh 1 - 1 < 1` of `1`
on the unit disc. -/
theorem norm_dslope_sinh_sub_one_le {t : ℂ} (ht : ‖t‖ ≤ 1) :
    ‖dslope sinh 0 t - 1‖ ≤ Real.sinh 1 - 1 := by
  have hreal : HasSum (fun n : ℕ => (1 : ℝ) / ((2 * (n + 1) + 1)! : ℝ)) (Real.sinh 1 - 1) := by
    have h := Real.hasSum_sinh 1
    simp only [one_pow] at h
    have := (hasSum_nat_add_iff' 1).mpr h
    simpa using this
  rcases eq_or_ne t 0 with rfl | ht0
  · rw [dslope_same, (Complex.hasDerivAt_sinh 0).deriv, Complex.cosh_zero, sub_self, norm_zero]
    exact hreal.nonneg fun n => by positivity
  · have hs := (Complex.hasSum_sinh t).div_const t
    have hs' : HasSum (fun n : ℕ => t ^ (2 * n) / ((2 * n + 1)! : ℂ)) (dslope sinh 0 t) := by
      rw [dslope_of_ne _ ht0, slope_def_field, Complex.sinh_zero, sub_zero, sub_zero]
      refine hs.congr_fun fun n => ?_
      rw [pow_succ]; field_simp
    have h1 := (hasSum_nat_add_iff' 1).mpr hs'
    simp only [Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, zero_add,
      Nat.factorial_one, Nat.cast_one, div_one] at h1
    refine h1.norm_le_of_bounded hreal fun n => ?_
    rw [norm_div, norm_pow, Complex.norm_natCast]
    gcongr
    exact pow_le_one₀ (norm_nonneg _) ht

/-- `sinh 1 < 2`. -/
theorem real_sinh_one_lt_two : Real.sinh 1 < 2 := by
  rw [Real.sinh_eq]
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_pos (-1)
  linarith

/-- whittakerBesselBase; support for the Buchholz coefficient transformation. -/
private noncomputable def whittakerBesselBase (t : ℂ) : ℂ := if t=0 then 1 else t/sinh t

/-- whittakerBessel core analytic; support for the Buchholz coefficient transformation. -/
private lemma whittakerBessel_core_analytic :
    DifferentiableOn ℂ (fun t : ℂ => cosh t/sinh t-t⁻¹) (Metric.ball 0 1) ∧
    DifferentiableOn ℂ whittakerBesselBase (Metric.ball 0 1) ∧
    ∀ t : ℂ, ‖t‖ < 1 → whittakerBesselBase t ∈ slitPlane := by
  set S : ℂ → ℂ := dslope sinh 0 with hS
  set h : ℂ → ℂ := fun t => t * cosh t - sinh t with hh
  set E : ℂ → ℂ := dslope (dslope h 0) 0 with hE
  have hhd : Differentiable ℂ h := by
    simp only [hh]; fun_prop
  have hSd : Differentiable ℂ S := fun x =>
    ((Complex.differentiableOn_dslope Filter.univ_mem).mpr
      Complex.differentiable_sinh.differentiableOn x (Set.mem_univ x)).differentiableAt
      Filter.univ_mem
  have hE1 : Differentiable ℂ (dslope h 0) := fun x =>
    ((Complex.differentiableOn_dslope Filter.univ_mem).mpr hhd.differentiableOn x
      (Set.mem_univ x)).differentiableAt Filter.univ_mem
  have hEd : Differentiable ℂ E := fun x =>
    ((Complex.differentiableOn_dslope Filter.univ_mem).mpr hE1.differentiableOn x
      (Set.mem_univ x)).differentiableAt Filter.univ_mem
  have hS_ne : ∀ x : ℂ, x ≠ 0 → S x = sinh x / x := fun x hx => by
    rw [hS, dslope_of_ne _ hx, slope_def_field, Complex.sinh_zero, sub_zero, sub_zero]
  have hS0 : S 0 = 1 := by
    rw [hS, dslope_same, (Complex.hasDerivAt_sinh 0).deriv, Complex.cosh_zero]
  have hh0 : h 0 = 0 := by simp [hh]
  have hh'0 : deriv h 0 = 0 := by
    have hd : HasDerivAt h (1 * cosh 0 + 0 * sinh 0 - cosh 0) 0 :=
      ((hasDerivAt_id 0).mul (Complex.hasDerivAt_cosh 0)).sub (Complex.hasDerivAt_sinh 0)
    rw [hd.deriv]; ring
  have hE_ne : ∀ x : ℂ, x ≠ 0 → E x = h x / x ^ 2 := fun x hx => by
    rw [hE, dslope_of_ne _ hx, slope_def_field, dslope_same, hh'0, dslope_of_ne _ hx,
      slope_def_field, hh0]
    field_simp
    ring
  have hE0 : E 0 = 0 := by
    have hodd : ∀ x : ℂ, x ≠ 0 → E (-x) = -E x := fun x hx => by
      rw [hE_ne x hx, hE_ne (-x) (neg_ne_zero.mpr hx)]
      simp only [hh, Complex.cosh_neg, Complex.sinh_neg]
      ring
    have h1 : Tendsto E (𝓝[≠] 0) (𝓝 (E 0)) := (hEd 0).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
    have h2 : Tendsto (fun x => E (-x)) (𝓝[≠] 0) (𝓝 (E 0)) := by
      have hn : Tendsto (fun x : ℂ => -x) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_neg.tendsto (0 : ℂ))
      exact ((hEd 0).continuousAt.tendsto.comp hn).mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun x => E (-x)) (𝓝[≠] 0) (𝓝 (-E 0)) := by
      refine h1.neg.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (hodd x hx).symm
    have := tendsto_nhds_unique h2 h3
    linear_combination this / 2
  have hSb : ∀ x : ℂ, ‖x‖ < 1 → ‖S x - 1‖ < 1 := fun x hx =>
    (norm_dslope_sinh_sub_one_le hx.le).trans_lt (by linarith [real_sinh_one_lt_two])
  have hSre : ∀ x : ℂ, ‖x‖ < 1 → 0 < (S x).re := fun x hx => by
    have h1 := hSb x hx
    have h2 := Complex.abs_re_le_norm (S x - 1)
    rw [Complex.sub_re, Complex.one_re] at h2
    linarith [abs_le.mp (h2.trans h1.le), neg_abs_le ((S x).re - 1)]
  have hSne : ∀ x : ℂ, ‖x‖ < 1 → S x ≠ 0 := fun x hx h0 => by
    have := hSre x hx; rw [h0, Complex.zero_re] at this; exact lt_irrefl _ this
  have hslit : ∀ x : ℂ, ‖x‖ < 1 → 1 / S x ∈ slitPlane := fun x hx => by
    rw [mem_slitPlane_iff, one_div, Complex.inv_re]
    exact Or.inl (div_pos (hSre x hx) (Complex.normSq_pos.mpr (hSne x hx)))
  have hball : ∀ x ∈ Metric.ball (0 : ℂ) 1, ‖x‖ < 1 := fun x hx => by simpa using hx

  have hAeq : Set.EqOn (fun t : ℂ => cosh t/sinh t-t⁻¹)
      (fun t => E t/S t) (Metric.ball 0 1) := by
    intro t ht
    have ht' := hball t ht
    change cosh t/sinh t-t⁻¹=E t/S t
    rcases eq_or_ne t 0 with rfl | ht0
    · simp [hE0,hS0]
    · rw [hE_ne t ht0,hS_ne t ht0]
      have hsh : sinh t ≠ 0 := fun h0 => hSne t ht' (by rw [hS_ne t ht0,h0,zero_div])
      simp only [hh]
      field_simp
  have hBeq : Set.EqOn whittakerBesselBase (fun t => 1/S t) (Metric.ball 0 1) := by
    intro t ht
    rcases eq_or_ne t 0 with rfl | ht0
    · simp [whittakerBesselBase,hS0]
    · simp only [whittakerBesselBase,ht0,↓reduceIte,hS_ne t ht0]
      field_simp
  have hAd : DifferentiableOn ℂ (fun t => E t/S t) (Metric.ball 0 1) :=
    fun t ht => ((hEd t).div (hSd t) (hSne t (hball t ht))).differentiableWithinAt
  have hBd : DifferentiableOn ℂ (fun t => 1/S t) (Metric.ball 0 1) :=
    fun t ht => ((differentiableAt_const _).div (hSd t)
      (hSne t (hball t ht))).differentiableWithinAt
  refine ⟨hAd.congr hAeq,hBd.congr hBeq,?_⟩
  intro t ht
  rw [hBeq (by simpa using ht)]
  exact hslit t ht

/-- whittakerBesselGenerating eq core; support for the Buchholz coefficient transformation. -/
private lemma whittakerBesselGenerating_eq_core (μ z t : ℂ) :
    whittakerBesselGenerating μ z t=
      exp (-z/2*(cosh t/sinh t-t⁻¹))*whittakerBesselBase t^(1-2*μ) := by
  by_cases ht : t=0
  · simp [whittakerBesselGenerating,whittakerBesselBase,ht]
  · simp [whittakerBesselGenerating,whittakerBesselBase,ht]

/-- whittakerBesselGenerating differentiableOn; support for the Buchholz coefficient transformation. -/
lemma whittakerBesselGenerating_differentiableOn (μ z : ℂ) :
    DifferentiableOn ℂ (whittakerBesselGenerating μ z) (Metric.ball 0 1) := by
  have h := whittakerBessel_core_analytic
  have hf : DifferentiableOn ℂ (fun t : ℂ =>
      exp (-z/2*(cosh t/sinh t-t⁻¹))*whittakerBesselBase t^(1-2*μ)) (Metric.ball 0 1) := by
    intro t ht
    have hA := h.1.differentiableAt (Metric.isOpen_ball.mem_nhds ht)
    have hB := h.2.1.differentiableAt (Metric.isOpen_ball.mem_nhds ht)
    exact (((hA.const_mul _).cexp).mul (hB.cpow (differentiableAt_const _)
      (h.2.2 t (by simpa using ht)))).differentiableWithinAt
  exact hf.congr fun t _ => whittakerBesselGenerating_eq_core μ z t

/-- whittakerBesselGenerating joint continuousAt; support for the Buchholz coefficient transformation. -/
lemma whittakerBesselGenerating_joint_continuousAt (μ : ℂ) {z t : ℂ} (ht : ‖t‖ < 1) :
    ContinuousAt (fun p : ℂ × ℂ => whittakerBesselGenerating μ p.1 p.2) (z,t) := by
  have ht' : t ∈ Metric.ball (0:ℂ) 1 := by simpa using ht
  have h := whittakerBessel_core_analytic
  have hA : ContinuousAt (fun p : ℂ × ℂ => cosh p.2/sinh p.2-p.2⁻¹) (z,t) :=
    (h.1.differentiableAt (Metric.isOpen_ball.mem_nhds ht')).continuousAt.comp (x:=(z,t)) continuousAt_snd
  have hBc : ContinuousAt whittakerBesselBase t :=
    (h.2.1.differentiableAt (Metric.isOpen_ball.mem_nhds ht')).continuousAt
  have hB : ContinuousAt (fun p : ℂ × ℂ => whittakerBesselBase p.2) (z,t) :=
    hBc.comp (g:=whittakerBesselBase) (f:=fun p : ℂ × ℂ => p.2) (x:=(z,t)) continuousAt_snd
  have hf : ContinuousAt (fun p : ℂ × ℂ =>
      exp (-p.1/2*(cosh p.2/sinh p.2-p.2⁻¹))*whittakerBesselBase p.2^(1-2*μ)) (z,t) :=
    (((continuousAt_fst.neg.div_const 2).mul hA).cexp).mul
      (hB.cpow continuousAt_const (h.2.2 t ht))
  exact hf.congr (Eventually.of_forall fun p => (whittakerBesselGenerating_eq_core μ p.1 p.2).symm)

/-- whittakerBessel base mem slit; support for the Buchholz coefficient transformation. -/
private lemma whittakerBessel_base_mem_slit {t : ℂ} (ht : t ≠ 0) (hsmall : ‖t‖ < 1) :
    t/sinh t ∈ slitPlane := by
  have hbd := (norm_dslope_sinh_sub_one_le hsmall.le).trans_lt
    (show Real.sinh 1-1 < 1 by linarith [real_sinh_one_lt_two])
  have h1 := Complex.abs_re_le_norm (dslope sinh 0 t-1)
  rw [Complex.sub_re,Complex.one_re] at h1
  have hS : 0 < (dslope sinh 0 t).re := by linarith [neg_abs_le ((dslope sinh 0 t).re-1)]
  have hSn : dslope sinh 0 t ≠ 0 := fun h0 => by simpa [h0] using hS
  have hEq : dslope sinh 0 t=sinh t/t := by
    rw [dslope_of_ne _ ht,slope_def_field,sinh_zero,sub_zero,sub_zero]
  have hBase : t/sinh t=(dslope sinh 0 t)⁻¹ := by rw [hEq,inv_div]
  rw [hBase,mem_slitPlane_iff,inv_re]
  exact Or.inl (div_pos hS (normSq_pos.mpr hSn))

/-- whittakerBessel hasDerivAt z; support for the Buchholz coefficient transformation. -/
lemma whittakerBesselGenerating_hasDerivAt_z (μ z t : ℂ) :
    HasDerivAt (fun w => whittakerBesselGenerating μ w t)
      (-(cosh t/sinh t-t⁻¹)/2*whittakerBesselGenerating μ z t) z := by
  by_cases ht : t=0
  · subst t
    simpa [whittakerBesselGenerating] using hasDerivAt_const z (1:ℂ)
  · have h := (((hasDerivAt_id' z).const_mul (-(cosh t/sinh t-t⁻¹)/2)).cexp).mul_const
      ((t/sinh t)^(1-2*μ))
    convert h using 1
    · funext w
      simp only [whittakerBesselGenerating,ht,↓reduceIte]
      congr 2 <;> ring
    · simp only [whittakerBesselGenerating,ht,↓reduceIte]
      have he : -(cosh t/sinh t-t⁻¹)/2*z = -z/2*(cosh t/sinh t-t⁻¹) := by ring
      rw [he]
      ring

/-- whittakerBessel deriv z; support for the Buchholz coefficient transformation. -/
lemma whittakerBesselGenerating_deriv_z (μ z t : ℂ) :
    deriv (fun w => whittakerBesselGenerating μ w t) z =
      -(cosh t/sinh t-t⁻¹)/2*whittakerBesselGenerating μ z t :=
  (whittakerBesselGenerating_hasDerivAt_z μ z t).deriv

/-- whittakerBessel iteratedDeriv two z; support for the Buchholz coefficient transformation. -/
lemma whittakerBesselGenerating_iteratedDeriv_two_z (μ z t : ℂ) :
    iteratedDeriv 2 (fun w => whittakerBesselGenerating μ w t) z =
      (cosh t/sinh t-t⁻¹)^2/4*whittakerBesselGenerating μ z t := by
  have he : deriv (fun w => whittakerBesselGenerating μ w t) =
      fun w => -(cosh t/sinh t-t⁻¹)/2*whittakerBesselGenerating μ w t :=
    funext fun w => whittakerBesselGenerating_deriv_z μ w t
  rw [iteratedDeriv_succ,iteratedDeriv_one,he]
  rw [((whittakerBesselGenerating_hasDerivAt_z μ z t).const_mul
    (-(cosh t/sinh t-t⁻¹)/2)).deriv]
  ring

/-- whittakerBessel hasDerivAt t; support for the Buchholz coefficient transformation. -/
lemma whittakerBesselGenerating_hasDerivAt_t {μ z t : ℂ} (ht : t ≠ 0) (hsmall : ‖t‖ < 1) :
    HasDerivAt (whittakerBesselGenerating μ z)
      (2*z*iteratedDeriv 2 (fun w => whittakerBesselGenerating μ w t) z -
        2*z/t*deriv (fun w => whittakerBesselGenerating μ w t) z -
        2*(2*μ-1)*deriv (fun w => whittakerBesselGenerating μ w t) z -
        z/2*whittakerBesselGenerating μ z t) t := by
  have hbase := whittakerBessel_base_mem_slit ht hsmall
  have hbase0 := slitPlane_ne_zero hbase
  have hsh : sinh t ≠ 0 := fun h0 => hbase0 (by rw [h0,div_zero])
  have hquot := (Complex.hasDerivAt_cosh t).div (Complex.hasDerivAt_sinh t) hsh
  have hexp := ((hquot.sub ((hasDerivAt_id' t).inv ht)).const_mul (-z/2)).cexp
  have hpow := ((hasDerivAt_id' t).div (Complex.hasDerivAt_sinh t) hsh).cpow_const
    (c:=1-2*μ) hbase
  have h := hexp.mul hpow
  have heq : whittakerBesselGenerating μ z =ᶠ[𝓝 t]
      fun v => exp (-z/2*(cosh v/sinh v-v⁻¹))*(v/sinh v)^(1-2*μ) := by
    filter_upwards [eventually_ne_nhds ht] with v hv
    simp [whittakerBesselGenerating,hv]
  apply (h.congr_of_eventuallyEq heq).congr_deriv
  rw [whittakerBesselGenerating_deriv_z,whittakerBesselGenerating_iteratedDeriv_two_z]
  simp only [whittakerBesselGenerating,ht,↓reduceIte,Pi.div_apply,Pi.sub_apply,Pi.inv_apply,id_eq]
  rw [Complex.cpow_sub (1-2*μ) 1 hbase0,Complex.cpow_one]
  generalize exp (-z/2*(cosh t/sinh t-t⁻¹)) = E
  generalize (t/sinh t)^(1-2*μ) = P
  field_simp [ht,hsh]
  ring_nf


/-- whittakerGenD; support for the Buchholz coefficient transformation. -/
private noncomputable def whittakerGenD (μ : ℂ) (j : ℕ) (z t : ℂ) : ℂ :=
  (-(cosh t/sinh t-t⁻¹)/2)^j*whittakerBesselGenerating μ z t

/-- whittakerTaylorD; support for the Buchholz coefficient transformation. -/
private noncomputable def whittakerTaylorD (μ : ℂ) (j : ℕ) (z : ℂ) (s : ℕ) : ℂ :=
  iteratedDeriv s (whittakerGenD μ j z) 0/s.factorial

/-- whittakerGenD t diff; support for the Buchholz coefficient transformation. -/
private lemma whittakerGenD_t_diff (μ : ℂ) (j : ℕ) (z : ℂ) :
    DifferentiableOn ℂ (whittakerGenD μ j z) (Metric.ball 0 1) := by
  exact ((((whittakerBessel_core_analytic.1.neg).div_const 2).pow j).mul
    (whittakerBesselGenerating_differentiableOn μ z))

/-- whittakerGenD joint cont; support for the Buchholz coefficient transformation. -/
private lemma whittakerGenD_joint_cont (μ : ℂ) (j : ℕ) {z t : ℂ} (ht : ‖t‖ < 1) :
    ContinuousAt (fun p : ℂ × ℂ => whittakerGenD μ j p.1 p.2) (z,t) := by
  have ht' : t ∈ Metric.ball (0:ℂ) 1 := by simpa using ht
  have hA : ContinuousAt (fun p : ℂ × ℂ => cosh p.2/sinh p.2-p.2⁻¹) (z,t) :=
    (whittakerBessel_core_analytic.1.differentiableAt
      (Metric.isOpen_ball.mem_nhds ht')).continuousAt.comp (x:=(z,t)) continuousAt_snd
  exact (((hA.neg.div_const 2).pow j).mul (whittakerBesselGenerating_joint_continuousAt μ ht))

/-- whittakerGenD z deriv; support for the Buchholz coefficient transformation. -/
private lemma whittakerGenD_z_deriv (μ : ℂ) (j : ℕ) (z t : ℂ) :
    HasDerivAt (fun w => whittakerGenD μ j w t) (whittakerGenD μ (j+1) z t) z := by
  convert (whittakerBesselGenerating_hasDerivAt_z μ z t).const_mul
    ((-(cosh t/sinh t-t⁻¹)/2)^j) using 1
  · rfl
  · simp only [whittakerGenD,pow_succ]
    ring

/-- whittakerTaylorD hasDerivAt; support for the Buchholz coefficient transformation. -/
private lemma whittakerTaylorD_hasDerivAt (μ : ℂ) (j s : ℕ) (z : ℂ) :
    HasDerivAt (fun w => whittakerTaylorD μ j w s) (whittakerTaylorD μ (j+1) z s) z := by
  have hdt (j : ℕ) (z : ℂ) : DifferentiableOn ℂ (whittakerGenD μ j z)
      (Metric.closedBall 0 (1/2)) := by
    apply (whittakerGenD_t_diff μ j z).mono
    intro t ht
    have ht' : ‖t‖ ≤ 1/2 := by simpa using ht
    simpa using (show ‖t‖ < 1 by linarith)
  have h := Complex.hasDerivAt_iteratedDeriv_param (G:=whittakerGenD μ j)
    (Gz:=whittakerGenD μ (j+1)) (r:=1/2) (by norm_num)
    (fun z t ht => whittakerGenD_joint_cont μ j (by rw [ht];norm_num))
    (fun z t ht => whittakerGenD_joint_cont μ (j+1) (by rw [ht];norm_num))
    (hdt j) (hdt (j+1)) (fun z t _ => whittakerGenD_z_deriv μ j z t) s z
  exact h.div_const _

/-- whittakerTaylorD uniform bound; support for the Buchholz coefficient transformation. -/
private lemma whittakerTaylorD_uniform_bound (μ : ℂ) (j : ℕ) (R : ℝ) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ z ∈ Metric.closedBall (0:ℂ) R,∀ s : ℕ,
      ‖whittakerTaylorD μ j z s‖ ≤ M*2^s := by
  have hdt (z : ℂ) : DifferentiableOn ℂ (whittakerGenD μ j z)
      (Metric.closedBall 0 (1/2)) := by
    apply (whittakerGenD_t_diff μ j z).mono
    intro t ht
    have ht' : ‖t‖ ≤ 1/2 := by simpa using ht
    simpa using (show ‖t‖ < 1 by linarith)
  obtain ⟨M,hM,hbd⟩ := Complex.exists_uniform_norm_taylorCoeff_le (G:=whittakerGenD μ j)
    (r:=1/2) (by norm_num)
    (fun z t ht => whittakerGenD_joint_cont μ j (by rw [ht];norm_num)) hdt 0 R
  refine ⟨M,hM,fun z hz s => ?_⟩
  have h := hbd z hz s
  simpa only [whittakerTaylorD,one_div,inv_pow,div_inv_eq_mul] using h


/-- whittakerGenD analyticAt; support for the Buchholz coefficient transformation. -/
private lemma whittakerGenD_analyticAt (μ : ℂ) (j : ℕ) (z : ℂ) {t : ℂ} (ht : ‖t‖ < 1) :
    AnalyticAt ℂ (whittakerGenD μ j z) t :=
  (whittakerGenD_t_diff μ j z).analyticOnNhd Metric.isOpen_ball t (by simpa using ht)

/-- whittakerGenD zero; support for the Buchholz coefficient transformation. -/
private lemma whittakerGenD_zero (μ z : ℂ) : whittakerGenD μ 0 z=whittakerBesselGenerating μ z := by
  funext t
  simp [whittakerGenD]

/-- buchholz iteratedDeriv id mul zero; support for the Buchholz coefficient transformation. -/
private lemma buchholz_iteratedDeriv_id_mul_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    iteratedDeriv (n+1) (fun t : ℂ => t*f t) 0 = (n+1)*iteratedDeriv n f 0 := by
  rw [iteratedDeriv_fun_mul (f:=fun t:ℂ=>t) (g:=f) contDiffAt_id hf.contDiffAt]
  simp only [iteratedDeriv_fun_id_zero,mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
  simp [show 1 < n+1+1 by omega]

/-- whittakerBesselGenerating pde; support for the Buchholz coefficient transformation. -/
private lemma whittakerBesselGenerating_pde {μ z t : ℂ} (ht : ‖t‖ < 1) :
    t*deriv (whittakerBesselGenerating μ z) t+2*z*whittakerGenD μ 1 z t =
      2*z*(t*whittakerGenD μ 2 z t)-2*(2*μ-1)*(t*whittakerGenD μ 1 z t)-
        z/2*(t*whittakerGenD μ 0 z t) := by
  by_cases ht0 : t=0
  · subst t
    simp [whittakerGenD]
  · rw [(whittakerBesselGenerating_hasDerivAt_t ht0 ht).deriv,
      whittakerBesselGenerating_deriv_z,whittakerBesselGenerating_iteratedDeriv_two_z]
    simp only [whittakerGenD,pow_zero,pow_one,one_mul]
    field_simp
    ring

/-- whittakerTaylorD recurrence; support for the Buchholz coefficient transformation. -/
private lemma whittakerTaylorD_recurrence (μ z : ℂ) (s : ℕ) :
    (s+1)*whittakerTaylorD μ 0 z (s+1)+2*z*whittakerTaylorD μ 1 z (s+1) =
      2*z*whittakerTaylorD μ 2 z s-2*(2*μ-1)*whittakerTaylorD μ 1 z s-
        z/2*whittakerTaylorD μ 0 z s := by
  let G := whittakerBesselGenerating μ z
  have hG : AnalyticAt ℂ G 0 := by
    exact (whittakerBesselGenerating_differentiableOn μ z).analyticOnNhd Metric.isOpen_ball 0 (by simp)
  have hF (j : ℕ) : AnalyticAt ℂ (whittakerGenD μ j z) 0 :=
    whittakerGenD_analyticAt μ j z (by simp)
  have hX (j : ℕ) : AnalyticAt ℂ (fun t : ℂ => t*whittakerGenD μ j z t) 0 :=
    analyticAt_id.mul (hF j)
  have he : (fun t : ℂ => t*deriv G t+2*z*whittakerGenD μ 1 z t) =ᶠ[𝓝 0]
      (fun t : ℂ => 2*z*(t*whittakerGenD μ 2 z t)-2*(2*μ-1)*(t*whittakerGenD μ 1 z t)-
        z/2*(t*whittakerGenD μ 0 z t)) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ) < 1)] with t ht
    exact whittakerBesselGenerating_pde (by simpa using ht)
  have h := he.iteratedDeriv_eq (s+1)
  have hL1 : AnalyticAt ℂ (fun t : ℂ => t*deriv G t) 0 := analyticAt_id.mul hG.deriv
  have hL2 : AnalyticAt ℂ (fun t : ℂ => 2*z*whittakerGenD μ 1 z t) 0 :=
    analyticAt_const.mul (hF 1)
  have hR1 : AnalyticAt ℂ (fun t : ℂ => 2*z*(t*whittakerGenD μ 2 z t)) 0 :=
    analyticAt_const.mul (hX 2)
  have hR2 : AnalyticAt ℂ (fun t : ℂ => 2*(2*μ-1)*(t*whittakerGenD μ 1 z t)) 0 :=
    analyticAt_const.mul (hX 1)
  have hR3 : AnalyticAt ℂ (fun t : ℂ => z/2*(t*whittakerGenD μ 0 z t)) 0 :=
    analyticAt_const.mul (hX 0)
  rw [iteratedDeriv_fun_add hL1.contDiffAt hL2.contDiffAt] at h
  change _ = iteratedDeriv (s+1)
    (((fun t : ℂ => 2*z*(t*whittakerGenD μ 2 z t)) -
      (fun t : ℂ => 2*(2*μ-1)*(t*whittakerGenD μ 1 z t))) -
      (fun t : ℂ => z/2*(t*whittakerGenD μ 0 z t))) 0 at h
  rw [iteratedDeriv_sub (hR1.sub hR2).contDiffAt hR3.contDiffAt,
    iteratedDeriv_sub hR1.contDiffAt hR2.contDiffAt] at h
  simp only [iteratedDeriv_const_mul_field] at h
  rw [buchholz_iteratedDeriv_id_mul_zero hG.deriv,
    buchholz_iteratedDeriv_id_mul_zero (hF 2),buchholz_iteratedDeriv_id_mul_zero (hF 1),
    buchholz_iteratedDeriv_id_mul_zero (hF 0)] at h
  simp only [←iteratedDeriv_succ'] at h
  dsimp only [G] at h
  rw [←whittakerGenD_zero μ z] at h
  dsimp only [whittakerTaylorD]
  have hfac : (s.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr s.factorial_ne_zero
  have hs : (s+1:ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero s
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  linear_combination 2*h


/-- buchholzC; support for the Buchholz coefficient transformation. -/
private noncomputable def buchholzC (μ : ℂ) (s : ℕ) (z : ℂ) : ℂ :=
  (-1/2:ℂ)^s*z^s*whittakerTaylorD μ 0 z s

/-- buchholzC1; support for the Buchholz coefficient transformation. -/
private noncomputable def buchholzC1 (μ : ℂ) (s : ℕ) (z : ℂ) : ℂ :=
  (-1/2:ℂ)^s*((s:ℂ)*z^(s-1)*whittakerTaylorD μ 0 z s+z^s*whittakerTaylorD μ 1 z s)

/-- buchholzC2; support for the Buchholz coefficient transformation. -/
private noncomputable def buchholzC2 (μ : ℂ) (s : ℕ) (z : ℂ) : ℂ :=
  (-1/2:ℂ)^s*((s:ℂ)*(s-1:ℕ)*z^(s-2)*whittakerTaylorD μ 0 z s+
    2*s*z^(s-1)*whittakerTaylorD μ 1 z s+z^s*whittakerTaylorD μ 2 z s)

/-- buchholzC hasDerivAt; support for the Buchholz coefficient transformation. -/
private lemma buchholzC_hasDerivAt (μ : ℂ) (s : ℕ) (z : ℂ) :
    HasDerivAt (buchholzC μ s) (buchholzC1 μ s z) z := by
  convert (((hasDerivAt_id' z).pow s).mul (whittakerTaylorD_hasDerivAt μ 0 s z)).const_mul
    ((-1/2:ℂ)^s) using 1
  · funext w
    simp only [buchholzC,Pi.mul_apply,Pi.pow_apply]
    ring
  · simp only [buchholzC1,Pi.pow_apply,Nat.zero_add,mul_one]

/-- buchholzC1 hasDerivAt; support for the Buchholz coefficient transformation. -/
private lemma buchholzC1_hasDerivAt (μ : ℂ) (s : ℕ) (z : ℂ) :
    HasDerivAt (buchholzC1 μ s) (buchholzC2 μ s z) z := by
  have h := (((((hasDerivAt_id' z).pow (s-1)).const_mul (s:ℂ)).mul
    (whittakerTaylorD_hasDerivAt μ 0 s z)).add
    (((hasDerivAt_id' z).pow s).mul (whittakerTaylorD_hasDerivAt μ 1 s z))).const_mul
      ((-1/2:ℂ)^s)
  convert h using 1
  · rfl
  · simp only [buchholzC2,Nat.sub_sub,Pi.pow_apply,Nat.zero_add,Nat.reduceAdd,mul_one]
    ring

/-- buchholzC weighted deriv; support for the Buchholz coefficient transformation. -/
private lemma buchholzC_weighted_deriv (μ : ℂ) (s : ℕ) (z : ℂ) :
    z*buchholzC1 μ s z=(-1/2:ℂ)^s*z^s*((s:ℂ)*whittakerTaylorD μ 0 z s+
      z*whittakerTaylorD μ 1 z s) := by
  cases s with
  | zero => simp [buchholzC1]
  | succ s => simp only [buchholzC1,Nat.add_sub_cancel,pow_succ];ring

/-- buchholzC weighted second; support for the Buchholz coefficient transformation. -/
private lemma buchholzC_weighted_second (μ : ℂ) (s : ℕ) (z : ℂ) :
    z^2*buchholzC2 μ s z=(-1/2:ℂ)^s*z^s*((s:ℂ)*(s-1)*whittakerTaylorD μ 0 z s+
      2*s*z*whittakerTaylorD μ 1 z s+z^2*whittakerTaylorD μ 2 z s) := by
  cases s with
  | zero => simp [buchholzC2]
  | succ s => cases s with
    | zero => simp [buchholzC2];ring
    | succ s =>
      simp only [buchholzC2,show s+1+1-2=s by omega,show s+1+1-1=s+1 by omega,
        Nat.cast_add,Nat.cast_one,pow_succ]
      ring

/-- buchholzA; support for the Buchholz coefficient transformation. -/
private noncomputable def buchholzA (μ : ℂ) (s : ℕ) (z : ℂ) : ℂ :=
  (-1/2:ℂ)^s*z^s*((s:ℂ)*whittakerTaylorD μ 0 z s+2*z*whittakerTaylorD μ 1 z s)

/-- buchholzA eq; support for the Buchholz coefficient transformation. -/
private lemma buchholzA_eq (μ : ℂ) (s : ℕ) (z : ℂ) :
    buchholzA μ s z=2*z*buchholzC1 μ s z-(s:ℂ)*buchholzC μ s z := by
  rw [show 2*z*buchholzC1 μ s z=2*(z*buchholzC1 μ s z) by ring,buchholzC_weighted_deriv]
  simp only [buchholzA,buchholzC]
  ring

/-- buchholzC recurrence; support for the Buchholz coefficient transformation. -/
private lemma buchholzC_recurrence (μ : ℂ) (s : ℕ) (z : ℂ) :
    buchholzA μ (s+1) z = -z^2*buchholzC2 μ s z+(2*s+2*μ-1)*z*buchholzC1 μ s z-
      (s:ℂ)*(s+2*μ)*buchholzC μ s z+z^2/4*buchholzC μ s z := by
  rw [show -z^2*buchholzC2 μ s z= -(z^2*buchholzC2 μ s z) by ring,
    show (2*s+2*μ-1)*z*buchholzC1 μ s z=(2*s+2*μ-1)*(z*buchholzC1 μ s z) by ring,
    buchholzC_weighted_second,buchholzC_weighted_deriv]
  simp only [buchholzA,buchholzC,pow_succ,Nat.cast_add,Nat.cast_one]
  have h := whittakerTaylorD_recurrence μ z s
  push_cast at h
  linear_combination ((-1/2:ℂ)^s*z^(s+1)*(-1/2))*h



@[dlmf 13.24.E3]
theorem whittakerBesselCoeff_hasSum {μ z t : ℂ} (ht : t ≠ 0) (hz : z ≠ 0)
    (hsmall : ‖t‖ < 1) :
    HasSum (fun s : ℕ => whittakerBesselCoeff μ z s * (-t / z) ^ s)
      (exp (-z / 2 * (cosh t / sinh t - 1 / t)) * (t / sinh t) ^ (1 - 2 * μ)) := by
  have hGd := whittakerBesselGenerating_differentiableOn μ z
  have hT := Complex.hasSum_taylorSeries_on_ball hGd (z := t) (by simpa using hsmall)
  convert hT using 1
  · funext s
    simp only [whittakerBesselCoeff, sub_zero, smul_eq_mul]
    rw [div_pow, mul_div_assoc', mul_assoc, ← mul_pow, show -z * -t = z * t by ring, mul_pow]
    have hf : (s ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  · simp only [whittakerBesselGenerating, ht, ↓reduceIte, one_div]

/-- Exponential coefficient bound from the generating function inside its disk. -/
theorem exists_norm_whittakerBesselCoeff_le (μ : ℂ) {z : ℂ} (hz : z ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℕ, ‖whittakerBesselCoeff μ z s‖ ≤ C*(2*‖z‖)^s := by
  have hs := (whittakerBesselCoeff_hasSum (μ := μ) (z := z) (t := 1/2)
    (by norm_num) hz (by norm_num)).summable.norm
  let C := ∑' s : ℕ, ‖whittakerBesselCoeff μ z s * (-(1/2:ℂ)/z)^s‖
  refine ⟨C, tsum_nonneg fun _ => norm_nonneg _, fun s => ?_⟩
  have h := hs.le_tsum s (fun _ _ => norm_nonneg _)
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hpow : 0 < (2*‖z‖)^s := pow_pos (by positivity) s
  have he : ‖whittakerBesselCoeff μ z s * (-(1/2:ℂ)/z)^s‖ =
      ‖whittakerBesselCoeff μ z s‖ / (2*‖z‖)^s := by
    simp only [norm_mul, norm_pow, norm_div, norm_neg]
    norm_num
    rw [div_div, div_pow, one_pow, ← mul_div_assoc, mul_one]
  rw [he] at h
  exact (div_le_iff₀ hpow).mp h

/-- Absolute convergence of the regularized form of the Buchholz series. -/
theorem summable_whittakerBessel_regularized (κ μ : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Summable fun s : ℕ => whittakerBesselCoeff μ z s / (2:ℂ)^s *
      regularizedHGFun (∅ : Multiset ℂ) {2*μ+s+1} (-(κ*z)) := by
  obtain ⟨C, hC, hcoef⟩ := exists_norm_whittakerBesselCoeff_le μ hz
  have hs : Summable fun s : ℕ => ‖whittakerBesselCoeff μ z s‖ / s ! := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun s => ?_)
      ((Real.summable_pow_div_factorial (2*‖z‖)).mul_left C)
    exact (div_le_div_of_nonneg_right (hcoef s) (by positivity)).trans_eq (by ring)
  have ha : Summable fun s : ℕ => ‖whittakerBesselCoeff μ z s / (2:ℂ)^s‖ *
      ‖(1:ℂ)‖ ^ (0:ℕ) * ((2:ℝ)^s/s !) := by
    convert hs using 1
    funext s
    simp only [norm_div, norm_pow, norm_ofNat, pow_zero, mul_one]
    field_simp
  simpa using (hasSum_neumann (2*μ) (-(κ*z)) 1
    (fun s => whittakerBesselCoeff μ z s / (2:ℂ)^s) id (fun _ => 0) ha).summable

/-- Cancellation of principal powers in each Buchholz Bessel term. -/
theorem whittakerBessel_term_eq_regularized {κ z : ℂ} (hκ : κ ≠ 0) (hz : z ≠ 0)
    (μ : ℂ) (s : ℕ) :
    (2:ℂ)^(2*μ) * (2*(κ*z)^(1/2:ℂ))^(-(2*μ+s)) *
      besselJ (2*μ+s) (2*(κ*z)^(1/2:ℂ)) =
    1/(2:ℂ)^s * regularizedHGFun (∅ : Multiset ℂ) {2*μ+s+1} (-(κ*z)) := by
  set x := 2*(κ*z)^(1/2:ℂ)
  have hx0 : x ≠ 0 := mul_ne_zero two_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero hκ hz)))
  have hx2 : x^2/4 = κ*z := by
    dsimp only [x]
    rw [mul_pow, one_div, cpow_ofNat_inv_pow]
    ring
  rw [besselJ_eq_regularized, hx2]
  have hp : (x/2)^(2*μ+s) = x^(2*μ+s)/(2:ℂ)^(2*μ+s) := by
    simpa using div_ofReal_cpow (r := 2) (by norm_num) hx0 (2*μ+s)
  rw [hp, cpow_add _ _ two_ne_zero, cpow_natCast, cpow_neg]
  have hxpow : x^(2*μ+s) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hx0)
  have h2pow : (2:ℂ)^(2*μ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have h2s : (2:ℂ)^s ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp

/-- The Buchholz sum has no residual principal-branch factors after normalization. -/
theorem whittakerBessel_series_eq_regularized {κ z : ℂ} (hκ : κ ≠ 0) (hz : z ≠ 0)
    (μ : ℂ) :
    (2:ℂ)^(2*μ) * (∑' s : ℕ, whittakerBesselCoeff μ z s *
      (2*(κ*z)^(1/2:ℂ))^(-(2*μ+s)) *
      besselJ (2*μ+s) (2*(κ*z)^(1/2:ℂ))) =
    ∑' s : ℕ, whittakerBesselCoeff μ z s / (2:ℂ)^s *
      regularizedHGFun (∅ : Multiset ℂ) {2*μ+s+1} (-(κ*z)) := by
  rw [← tsum_mul_left]
  refine tsum_congr fun s => ?_
  have h := whittakerBessel_term_eq_regularized hκ hz μ s
  linear_combination whittakerBesselCoeff μ z s * h

/-- The Bessel series in DLMF 13.24.2 is absolutely convergent. -/
theorem summable_whittakerM_besselJ_series {κ z : ℂ} (hκ : κ ≠ 0) (hz : z ≠ 0)
    (μ : ℂ) :
    Summable fun s : ℕ => ‖whittakerBesselCoeff μ z s *
      (2*(κ*z)^(1/2:ℂ))^(-(2*μ+s)) *
      besselJ (2*μ+s) (2*(κ*z)^(1/2:ℂ))‖ := by
  have h2pow : (2:ℂ)^(2*μ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hs := (summable_whittakerBessel_regularized κ μ hz).mul_left ((2:ℂ)^(2*μ))⁻¹
  apply Summable.norm
  refine hs.congr fun s => ?_
  have h := whittakerBessel_term_eq_regularized hκ hz μ s
  field_simp at h ⊢
  linear_combination -(whittakerBesselCoeff μ z s)*h
/- The Buchholz transform identifying this convergent series with Whittaker M
remains to be proved. Convergence and cancellation of the principal powers are
established above using the existing Neumann-series estimates. -/
@[dlmf 13.24.E2]
theorem whittakerM_besselJ_series {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hκ : 0 < κ.re) (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ z / Gamma (1 + 2 * μ) =
      (2 : ℂ) ^ (2 * μ) * z ^ (μ + 1 / 2) *
        ∑' s : ℕ, whittakerBesselCoeff μ z s *
          (2 * (κ * z) ^ (1 / 2 : ℂ)) ^ (-(2 * μ + s)) *
          besselJ (2 * μ + s) (2 * (κ * z) ^ (1 / 2 : ℂ)) := by
  sorry

end DLMF.Confluent
