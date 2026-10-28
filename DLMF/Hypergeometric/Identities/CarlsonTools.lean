/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.FurtherTransformations
public import DLMF.Bailey
public import DLMF.Gamma.Inequalities
public import DLMF.Gamma.Asymptotics
public import ToMathlib.Analysis.Complex.Carlson

/-!
# Carlson bounds for hypergeometric summations

Terminating sums and analytic bounds prepare Carlson continuation for hypergeometric identities.

Source references and common attribution are retained in
`DLMF.Hypergeometric.Identities`.
-/

@[expose] public section

open Complex

open scoped Real

noncomputable section

namespace DLMF.Hypergeometric

/-- Kummer's theorem:
`₂F₁(a,b;1+a-b;-1) = Γ(1+a-b) Γ(1+a/2) / (Γ(1+a) Γ(1+a/2-b))`. -/
@[dlmf 15.4.E26]
theorem kummer_theorem {a b : ℂ}
    (h : ∀ k : ℕ, (1 + a - b : ℂ) ≠ -k)
    (ha : ∀ k : ℕ, (1 + a / 2 : ℂ) ≠ -k) (hb : b.re < 1 / 2) :
    ₂F₁ a b (1 + a - b) (-1 : ℂ) =
      Gamma (1 + a - b) * Gamma (1 + a / 2) /
        (Gamma (1 + a) * Gamma (1 + a / 2 - b)) := by
  set C := 1 + a - b with hCdef
  have hC' : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ) := by
    rw [show a - b + 1 = C by rw [hCdef]; ring]; exact h
  have hre : 0 < (C - a - b).re := by
    rw [show C - a - b = 1 - 2 * b by rw [hCdef]; ring]; simp; linarith
  have hre' : 0 < (C - a / 2 - (a / 2 - b + 1 / 2)).re := by
    rw [show C - a / 2 - (a / 2 - b + 1 / 2) = 1 / 2 by rw [hCdef]; ring]; norm_num
  -- The series as a power series with coefficients multiplied by `(-1)^n`.
  have htsum : ∀ x : ℂ, ₂F₁ a b C x = ∑' n, gaussHGCoeff a b C n * x ^ n := by
    intro x
    rw [ordinaryHypergeometric_eq_tsum]
    simp only [smul_eq_mul]
    congr 1
    funext n
    simp [gaussHGCoeff, poch, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hsum : Summable fun n => gaussHGCoeff a b C n * (-1 : ℂ) ^ n :=
    ordinaryHypergeometric_summable_of_mem_sphere (z := -1) (by simp) hre
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt
    (f := fun n => gaussHGCoeff a b C n * (-1 : ℂ) ^ n) hsum.hasSum.tendsto_sum_nat
  rw [Filter.tendsto_map'_iff] at habel
  have hneg : Filter.Tendsto (fun x : ℝ => -x) (nhdsWithin (-1) (Set.Ioi (-1)))
      (nhdsWithin 1 (Set.Iio 1)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := (continuous_neg.tendsto (-1 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (-1 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_Iio, Set.mem_Ioi] at hx ⊢; linarith
  have hL : Filter.Tendsto (fun x : ℝ => ₂F₁ a b C (x : ℂ)) (nhdsWithin (-1) (Set.Ioi (-1)))
      (nhds (₂F₁ a b C (-1))) := by
    rw [htsum (-1)]
    refine (habel.comp hneg).congr fun x => ?_
    simp only [Function.comp_apply]
    rw [htsum]
    refine tsum_congr fun n => ?_
    push_cast
    rw [neg_pow]
    ring_nf
    rw [mul_comm n 2, pow_mul, neg_one_sq, one_pow, mul_one]
  -- The right-hand side of 15.8.16 along `x → -1⁺`.
  have hv : Filter.Tendsto (fun x : ℝ => -4 * x / (1 - x) ^ 2) (nhdsWithin (-1) (Set.Ioi (-1)))
      (nhdsWithin 1 (Set.Iio 1)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hcont : ContinuousAt (fun x : ℝ => -4 * x / (1 - x) ^ 2) (-1) :=
        ((continuousAt_const.mul continuousAt_id).div
          ((continuousAt_const.sub continuousAt_id).pow 2) (by norm_num))
      have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (-1 : ℝ)))
      norm_num at this ⊢
      exact this
    · filter_upwards [Ioo_mem_nhdsGT (show (-1 : ℝ) < 0 by norm_num)] with x hx
      simp only [Set.mem_Iio]
      have h1x : 0 < (1 - x) ^ 2 := by nlinarith [hx.2]
      rw [div_lt_one h1x]
      nlinarith [hx.1, hx.2]
  have hR1 := (DLMF.Hypergeometric.tendsto_ordinaryHypergeometric_left_one
    (a := a / 2) (b := a / 2 - b + 1 / 2) (c := C) hre').comp hv
  have hR2 : Filter.Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (-a)) (nhdsWithin (-1) (Set.Ioi (-1)))
      (nhds ((2 : ℂ) ^ (-a))) := by
    have h2 : (2 : ℂ) ∈ slitPlane := by simp
    have h1 := ((show Continuous (fun x : ℝ => (1 : ℂ) - x) by fun_prop).tendsto (-1 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (-1 : ℝ)))
    rw [show (1 : ℂ) - ((-1 : ℝ) : ℂ) = 2 by push_cast; ring] at h1
    exact (continuousAt_cpow_const (b := -a) h2).tendsto.comp h1
  have heq : ∀ᶠ x : ℝ in nhdsWithin (-1) (Set.Ioi (-1)), ₂F₁ a b C (x : ℂ) =
      (1 - (x : ℂ)) ^ (-a) * ₂F₁ (a / 2) (a / 2 - b + 1 / 2) C ((-4 * x / (1 - x) ^ 2 : ℝ) : ℂ) := by
    filter_upwards [Ioo_mem_nhdsGT (show (-1 : ℝ) < 0 by norm_num)] with x hx
    have hxn : ‖(x : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]; constructor <;> linarith [hx.1, hx.2]
    have hvn : ‖-4 * (x : ℂ) / (1 - x) ^ 2‖ < 1 := by
      rw [show -4 * (x : ℂ) / (1 - x) ^ 2 = ((-4 * x / (1 - x) ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      have h1x : 0 < (1 - x) ^ 2 := by nlinarith [hx.2]
      rw [abs_of_pos (div_pos (by nlinarith [hx.2]) h1x), div_lt_one h1x]
      nlinarith [hx.1, hx.2]
    have hq := DLMF.Hypergeometric.quadratic_well_poised_minus (a := a) (b := b) hC' hxn hvn
    rw [show a - b + 1 = C by rw [hCdef]; ring] at hq
    rw [hq]
    push_cast
    ring_nf
  have hlim := tendsto_nhds_unique hL ((hR2.mul hR1).congr' (by
    filter_upwards [heq] with x hx
    rw [hx]; rfl))
  rw [hlim, gauss_summation (a := a / 2) (b := a / 2 - b + 1 / 2) h hre',
    show C - a / 2 - (a / 2 - b + 1 / 2) = 1 / 2 by rw [hCdef]; ring,
    show C - a / 2 = 1 + a / 2 - b by rw [hCdef]; ring,
    show C - (a / 2 - b + 1 / 2) = a / 2 + 1 / 2 by rw [hCdef]; ring, Gamma_one_half_eq]
  -- Duplication formula at `s = (a+1)/2`.
  have hdup := Complex.Gamma_mul_Gamma_add_half (a / 2 + 1 / 2)
  rw [show a / 2 + 1 / 2 + 1 / 2 = 1 + a / 2 by ring, show 1 - 2 * (a / 2 + 1 / 2) = -a by ring,
    show 2 * (a / 2 + 1 / 2) = 1 + a by ring] at hdup
  have hsq : ((Real.sqrt Real.pi : ℝ) : ℂ) = (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf
  rw [hsq] at hdup
  have hG2 : Gamma (1 + a / 2) ≠ 0 := Complex.Gamma_ne_zero ha
  have h2a : (2 : ℂ) ^ (-a) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hπ : (Real.pi : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  by_cases hG1 : Gamma (a / 2 + 1 / 2) = 0
  · have : Gamma (1 + a) = 0 := by
      rw [hG1, zero_mul] at hdup
      rcases mul_eq_zero.mp (mul_eq_zero.mp hdup.symm |>.resolve_right hπ) with h' | h'
      · exact h'
      · exact absurd h' h2a
    rw [hG1, this]
    simp
  · have hG3 : Gamma (1 + a) ≠ 0 := by
      intro h0; rw [h0, zero_mul, zero_mul] at hdup
      exact mul_ne_zero hG1 hG2 hdup
    by_cases hG4 : Gamma (1 + a / 2 - b) = 0
    · rw [hG4]; simp
    · rw [← mul_div_assoc, div_eq_div_iff (mul_ne_zero hG4 hG1) (mul_ne_zero hG3 hG4)]
      linear_combination (-(Gamma C * Gamma (1 + a / 2 - b))) * hdup

section CarlsonApplications

/-! ### Carlson's theorem for Dixon's and Dougall's sums

Both sums satisfy a first-order recurrence in one parameter (by telescoping), so a
Gamma-normalized difference of the two sides is `1`-periodic. On a vertical strip it grows like
`e^{π|y|/2}`, and it vanishes at the integers by Gauss's summation (Dougall) or by the
terminating case (Dixon), so it vanishes by Carlson's theorem. -/

open Filter Set
open scoped Topology

namespace CarlsonAux

/-- A polynomial factor is absorbed by any exponential: `(1+t)^K ≤ M e^{εt}` for `t ≥ 0`. -/
theorem exists_one_add_pow_le_exp (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 0 ≤ t → (1 + t) ^ K ≤ M * Real.exp (ε * t) := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · exact ⟨1, one_pos, fun t ht => by simpa using Real.one_le_exp (by positivity)⟩
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  set L : ℝ := max 1 (K / ε) with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  refine ⟨L ^ K, by positivity, fun t ht => ?_⟩
  have h1 : 1 + t ≤ L * (1 + ε * t / K) := by
    rcases le_total 1 (K / ε) with h | h
    · rw [hL, max_eq_right h, mul_add, mul_one]
      have : K / ε * (ε * t / K) = t := by field_simp
      rw [this]; linarith
    · rw [hL, max_eq_left h, one_mul]
      have hεK : 1 ≤ ε / K := by
        rw [le_div_iff₀ hK']; rw [div_le_iff₀ hε] at h; linarith
      have : t ≤ ε * t / K := by
        rw [mul_div_right_comm]; nlinarith
      linarith
  have h2 : (1 + ε * t / K) ^ K ≤ Real.exp (ε * t) := by
    calc (1 + ε * t / K) ^ K ≤ Real.exp (ε * t / K) ^ K :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (ε * t / K)]) K
      _ = Real.exp (ε * t) := by rw [← Real.exp_nat_mul]; congr 1; field_simp
  calc (1 + t) ^ K ≤ (L * (1 + ε * t / K)) ^ K := pow_le_pow_left₀ (by positivity) h1 K
    _ = L ^ K * (1 + ε * t / K) ^ K := mul_pow _ _ _
    _ ≤ L ^ K * Real.exp (ε * t) := by gcongr

/-- **Carlson's theorem for periodic functions.** A `1`-periodic function, holomorphic on a
neighbourhood of the closed right half-plane, of growth `(1+|y|)^K e^{σ|y|}` with `σ < π` on the
strip `0 ≤ re ≤ 1`, and vanishing at `0`, vanishes on the closed right half-plane. -/
theorem eq_zero_of_periodic_of_bound {f : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f {w : ℂ | -δ < w.re})
    (hper : ∀ w : ℂ, 0 ≤ w.re → f (w + 1) = f w)
    {C σ : ℝ} {K : ℕ} (hσ : σ < π)
    (hb : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖f w‖ ≤ C * (1 + |w.im|) ^ K * Real.exp (σ * |w.im|))
    (h0 : f 0 = 0) : ∀ w : ℂ, 0 ≤ w.re → f w = 0 := by
  have hnat : ∀ (k : ℕ) (w : ℂ), 0 ≤ w.re → f (w + k) = f w := by
    intro k
    induction k with
    | zero => intro w _; simp
    | succ k ih =>
      intro w hw
      have hre : 0 ≤ (w + k).re := by simp; positivity
      rw [Nat.cast_succ, ← add_assoc, hper _ hre, ih w hw]
  have hstrip : ∀ w : ℂ, 0 ≤ w.re →
      ‖f w‖ ≤ C * (1 + |w.im|) ^ K * Real.exp (σ * |w.im|) := by
    intro w hw
    set k := ⌊w.re⌋₊
    have hk : (k : ℝ) ≤ w.re := Nat.floor_le hw
    have hk1 : w.re < k + 1 := Nat.lt_floor_add_one _
    have h := hb (w - k) (by simp; linarith) (by simp; linarith)
    have hw' : f (w - k + k) = f (w - k) := hnat k (w - k) (by simp; linarith)
    rw [sub_add_cancel] at hw'
    simpa [hw'] using h
  have hC : 0 ≤ C := by
    have h := hb 0 (by simp) (by simp)
    simp only [zero_im, abs_zero, add_zero, one_pow, mul_one, mul_zero, Real.exp_zero] at h
    exact (norm_nonneg _).trans h
  set ε : ℝ := (π - σ) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨M, hM, hMb⟩ := exists_one_add_pow_le_exp K hε
  have hbound : ∀ w : ℂ, 0 ≤ w.re → ‖f w‖ ≤ (C * M) * Real.exp ((σ + ε) * |w.im|) := by
    intro w hw
    refine (hstrip w hw).trans ?_
    have h := hMb |w.im| (abs_nonneg _)
    calc C * (1 + |w.im|) ^ K * Real.exp (σ * |w.im|)
        ≤ C * (M * Real.exp (ε * |w.im|)) * Real.exp (σ * |w.im|) := by gcongr
      _ = (C * M) * Real.exp ((σ + ε) * |w.im|) := by
        rw [add_mul, Real.exp_add]; ring
  have hd : DiffContOnCl ℂ f {z : ℂ | 0 < z.re} := by
    refine ⟨hf.mono fun z hz => by simp at hz ⊢; linarith, ?_⟩
    refine hf.continuousOn.mono ?_
    intro z hz
    have := closure_lt_subset_le continuous_const continuous_re hz
    simp only [Set.mem_ofPred_eq] at this ⊢
    linarith
  refine Complex.eqOn_zero_of_natCast_eq_zero hd (C := C * M) (τ := |σ + ε|) (c := σ + ε)
    (fun z hz => (hbound z hz).trans ?_) (fun y => ?_) (by rw [hεdef]; linarith) (fun n => ?_)
  · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    calc (σ + ε) * |z.im| ≤ |σ + ε| * |z.im| :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)
      _ ≤ |σ + ε| * ‖z‖ := mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) (abs_nonneg _)
  · have h := hbound (y * I) (by simp)
    simpa using h
  · have := hnat n 0 (by simp)
    rw [zero_add] at this
    rw [this, h0]

/-- `z / Γ(z+1) = 1 / Γ(z)` for every `z`, including the poles. -/
theorem mul_recip_Gamma_add_one (z : ℂ) : z * (Gamma (z + 1))⁻¹ = (Gamma z)⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Complex.Gamma_zero]
  rw [Complex.Gamma_add_one z hz, mul_inv, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]

/-- `‖sin z‖ ≤ e^{|Im z|}`. -/
theorem norm_sin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have h := Complex.norm_sin_add_mul_I_sq z.re z.im
  rw [show (z.re : ℂ) + z.im * I = z from Complex.re_add_im z] at h
  have hc : Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 ≤ Real.exp |z.im| ^ 2 := by
    have h1 := Real.sin_sq_le_one z.re
    have h2 : Real.sinh z.im ^ 2 + 1 = Real.cosh z.im ^ 2 := by
      nlinarith [Real.cosh_sq z.im]
    have h3 : Real.cosh z.im ≤ Real.exp |z.im| := DLMF.Gamma.cosh_le_exp_abs z.im
    have h4 : 0 ≤ Real.cosh z.im := (Real.cosh_pos _).le
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).mp (h ▸ hc)

/-- Growth of `1/Γ` to the right of `1/2`: `‖1/Γ(z)‖ ≤ e^{π|Im z|/2}/Γ(Re z)`. -/
theorem norm_recip_Gamma_le_of_half_le {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    ‖(Gamma z)⁻¹‖ ≤ Real.exp (π * |z.im| / 2) / Real.Gamma z.re := by
  have h := DLMF.Gamma.norm_recip_Gamma_sq_le hz z.im
  have hz' : (z.re : ℂ) + I * z.im = z := by rw [mul_comm]; exact Complex.re_add_im z
  rw [hz'] at h
  have hG := Real.Gamma_pos_of_pos (show 0 < z.re by linarith)
  have hE : Real.exp (π * |z.im|) / Real.Gamma z.re ^ 2 =
      (Real.exp (π * |z.im| / 2) / Real.Gamma z.re) ^ 2 := by
    rw [div_pow, ← Real.exp_nat_mul]; ring_nf
  rw [hE] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- Growth of `1/Γ` to the left of `1/2`, by reflection:
`‖1/Γ(z)‖ ≤ e^{π|Im z|} Γ(1 - Re z)/π`. -/
theorem norm_recip_Gamma_le_of_lt_half {z : ℂ} (hz : z.re < 1 / 2) :
    ‖(Gamma z)⁻¹‖ ≤ Real.exp (π * |z.im|) * Real.Gamma (1 - z.re) / π := by
  have hG := Real.Gamma_pos_of_pos (show 0 < 1 - z.re by linarith)
  by_cases hpole : ∃ m : ℕ, z = -m
  · obtain ⟨m, rfl⟩ := hpole
    rw [Complex.Gamma_neg_nat_eq_zero, inv_zero, norm_zero]
    positivity
  push Not at hpole
  have hsin : Complex.sin (π * z) ≠ 0 := by
    rw [Ne, Complex.sin_eq_zero_iff]
    rintro ⟨k, hk⟩
    have hk' : z = k := by
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      apply mul_left_cancel₀ hπ; rw [hk]; ring
    rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
    · have : (z.re) = m := by rw [hk']; simp
      have hm : (m : ℝ) < 1 / 2 := this ▸ hz
      have hm0 : m = 0 := by
        by_contra h; have : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
        linarith
      exact hpole 0 (by rw [hk', hm0]; simp)
    · exact hpole m (by rw [hk']; simp)
  have hGz : Gamma z ≠ 0 := by
    intro h0
    have := Complex.Gamma_mul_Gamma_one_sub z
    rw [h0, zero_mul] at this
    exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero) hsin this.symm
  have hrefl : (Gamma z)⁻¹ = Gamma (1 - z) * Complex.sin (π * z) / π := by
    have h := Complex.Gamma_mul_Gamma_one_sub z
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    rw [h, mul_comm z]
    field_simp
  rw [hrefl, norm_div, norm_mul]
  have h1 : ‖Gamma (1 - z)‖ ≤ Real.Gamma (1 - z.re) := by
    have h := DLMF.Gamma.norm_Gamma_add_mul_I_le (x := 1 - z.re) (y := -z.im) (by linarith)
    have he : ((1 - z.re : ℝ) : ℂ) + I * ((-z.im : ℝ) : ℂ) = 1 - z := by
      apply Complex.ext <;> simp
    rw [he, abs_of_pos hG] at h
    exact h
  have h2 : ‖Complex.sin (π * z)‖ ≤ Real.exp (π * |z.im|) := by
    have h := norm_sin_le_exp_abs_im (π * z)
    have : (↑π * z).im = π * z.im := by simp
    rw [this, abs_mul, abs_of_pos Real.pi_pos] at h
    exact h
  have hπn : ‖(π : ℂ)‖ = π := by simp [abs_of_pos Real.pi_pos]
  rw [hπn]
  have := mul_le_mul h1 h2 (norm_nonneg _) hG.le
  rw [div_le_div_iff_of_pos_right Real.pi_pos]
  linarith [mul_comm (Real.Gamma (1 - z.re)) (Real.exp (π * |z.im|))]

/-- **Uniform vertical decay of `Γ`** on a strip `X₁ ≤ Re z ≤ X₂` with `X₁ > 0`. -/
theorem exists_norm_Gamma_le_strip {X₁ X₂ : ℝ} (hX₁ : 0 < X₁) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ z : ℂ, X₁ ≤ z.re → z.re ≤ X₂ →
      ‖Gamma z‖ ≤ C * (1 + |z.im|) ^ K * Real.exp (-(π * |z.im|) / 2) := by
  set X := max X₁ X₂ with hXdef
  have hX : 0 < X := lt_of_lt_of_le hX₁ (le_max_left _ _)
  obtain ⟨C₀, K, hC₀⟩ := DLMF.Gamma.exists_norm_Gamma_le hX
  have hC₀0 : 0 ≤ C₀ := by
    have := (norm_nonneg _).trans (hC₀ 0); simpa using this
  set G := max (Real.Gamma X₁) (Real.Gamma X) with hGdef
  have hGX := Real.Gamma_pos_of_pos hX
  refine ⟨G * C₀ / Real.Gamma X, K, fun z hz1 hz2 => ?_⟩
  set x := z.re
  set y := z.im
  have hx0 : 0 < x := lt_of_lt_of_le hX₁ hz1
  have hxX : x ≤ X := le_trans hz2 (le_max_right _ _)
  have hz' : (x : ℂ) + I * y = z := by rw [mul_comm]; exact Complex.re_add_im z
  have hsq := DLMF.Gamma.norm_Gamma_sq_eq hx0 y
  have hsqX := DLMF.Gamma.norm_Gamma_sq_eq hX y
  have hP := DLMF.Gamma.gammaVertProd_anti hx0 hxX y
  have hP1 := DLMF.Gamma.one_le_gammaVertProd X y
  have hPx1 := DLMF.Gamma.one_le_gammaVertProd x y
  have hGx : Real.Gamma x ≤ G := Real.convexOn_Gamma.le_max_of_mem_Icc
    (show X₁ ∈ Ioi (0 : ℝ) from hX₁) (show X ∈ Ioi (0 : ℝ) from hX) ⟨hz1, hxX⟩
  have hGx0 := Real.Gamma_pos_of_pos hx0
  have hB := hC₀ y
  set B := C₀ * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2)
  have hB0 : 0 ≤ B := by positivity
  -- `‖Γ(X+iy)‖² = Γ(X)²/P(X,y)` gives `1/P(X,y) ≤ B²/Γ(X)²`
  have hinvP : (DLMF.Gamma.gammaVertProd X y)⁻¹ ≤ B ^ 2 / Real.Gamma X ^ 2 := by
    have h1 : Real.Gamma X ^ 2 / DLMF.Gamma.gammaVertProd X y ≤ B ^ 2 := by
      rw [← hsqX]; exact pow_le_pow_left₀ (norm_nonneg _) hB 2
    rw [div_le_iff₀ (by positivity)] at h1
    rw [le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity)]
    linarith
  have hfin : ‖Gamma z‖ ^ 2 ≤ (G * B / Real.Gamma X) ^ 2 := by
    rw [← hz', hsq]
    calc Real.Gamma x ^ 2 / DLMF.Gamma.gammaVertProd x y
        ≤ Real.Gamma x ^ 2 / DLMF.Gamma.gammaVertProd X y := by
          gcongr
      _ = Real.Gamma x ^ 2 * (DLMF.Gamma.gammaVertProd X y)⁻¹ := div_eq_mul_inv _ _
      _ ≤ G ^ 2 * (B ^ 2 / Real.Gamma X ^ 2) := by
          gcongr
      _ = (G * B / Real.Gamma X) ^ 2 := by ring
  have h := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hfin
  calc ‖Gamma z‖ ≤ G * B / Real.Gamma X := h
    _ = G * C₀ / Real.Gamma X * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2) := by
      simp only [B]; ring

/-- **Uniform vertical growth of `1/Γ`** on a strip `|Re z| ≤ X`. -/
theorem exists_norm_recip_Gamma_le_strip (X : ℝ) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ z : ℂ, |z.re| ≤ X →
      ‖(Gamma z)⁻¹‖ ≤ C * (1 + |z.im|) ^ K * Real.exp (π * |z.im| / 2) := by
  obtain ⟨C, K, hC⟩ := DLMF.Gamma.exists_norm_recip_Gamma_le X
  refine ⟨C, K, fun z hz => ?_⟩
  have hz' : (z.re : ℂ) + I * z.im = z := by rw [mul_comm]; exact Complex.re_add_im z
  have h := hC z.re ⟨by linarith [neg_abs_le z.re], le_trans (le_abs_self _) hz⟩ z.im
  rwa [hz'] at h

/-- `1 + |y + β| ≤ (1 + |β|) (1 + |y|)`. -/
theorem one_add_abs_add_le (y β : ℝ) : 1 + |y + β| ≤ (1 + |β|) * (1 + |y|) := by
  have := abs_add_le y β
  nlinarith [abs_nonneg y, abs_nonneg β]

/-- `‖sin(π(z + n))‖ = ‖sin(πz)‖` for integer `n`. -/
theorem norm_sin_pi_mul_add_int (z : ℂ) (n : ℤ) :
    ‖Complex.sin (π * (z + n))‖ = ‖Complex.sin (π * z)‖ := by
  rw [show (π : ℂ) * (z + n) = π * z + n * π by ring,
    Complex.sin_antiperiodic.add_int_mul_eq n]
  rcases Int.isUnit_iff.mp (Int.negOnePow n).isUnit with h | h <;> simp [h]

/-- Asymptotics of a product of Gamma ratios: `Γ(k+p)Γ(k+q)/(Γ(k+r)Γ(k+s)) = O(k^{p+q-r-s})`. -/
theorem isBigO_Gamma_ratio (p q r s : ℂ) :
    (fun k : ℕ => Gamma (k + p) * Gamma (k + q) * (Gamma (k + r))⁻¹ * (Gamma (k + s))⁻¹)
      =O[atTop] fun k : ℕ => (k : ℝ) ^ (p + q - r - s).re := by
  have hT (a : ℂ) : Tendsto (fun k : ℕ => Gamma (k + a) / (Gamma k * (k : ℂ) ^ a)) atTop (𝓝 1) :=
    by
      have h := (DLMF.Gamma.tendsto_Gamma_add_div_Gamma_mul_cpow a).comp
        tendsto_natCast_atTop_atTop
      refine h.congr fun k => ?_
      simp [Function.comp]
  have hQ := ((hT p).mul (hT q)).div ((hT r).mul (hT s)) (by norm_num)
  rw [mul_one, div_one] at hQ
  set e : ℂ := p + q - r - s
  refine Asymptotics.IsBigO.of_bound 2 ?_
  have hev := (hQ.norm.eventually (gt_mem_nhds (show ‖(1 : ℂ)‖ < 2 by norm_num)))
  filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hkey : Gamma (k + p) * Gamma (k + q) * (Gamma (k + r))⁻¹ * (Gamma (k + s))⁻¹ =
      (Gamma (k + p) / (Gamma k * (k : ℂ) ^ p) * (Gamma (k + q) / (Gamma k * (k : ℂ) ^ q)) /
        (Gamma (k + r) / (Gamma k * (k : ℂ) ^ r) * (Gamma (k + s) / (Gamma k * (k : ℂ) ^ s)))) *
        (k : ℂ) ^ e := by
    have hG : Gamma (k : ℂ) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (s := (k : ℂ)) (by simp; exact_mod_cast hk1)
    have hcp : (k : ℂ) ^ e = (k : ℂ) ^ p * (k : ℂ) ^ q * ((k : ℂ) ^ r)⁻¹ * ((k : ℂ) ^ s)⁻¹ := by
      simp only [e, sub_eq_add_neg, Complex.cpow_add _ _ hk0, Complex.cpow_neg]
    rw [hcp]
    have h1 : (k : ℂ) ^ p ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hk0)
    have h2 : (k : ℂ) ^ q ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hk0)
    have h3 : (k : ℂ) ^ r ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hk0)
    have h4 : (k : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hk0)
    by_cases hr : Gamma (k + r) = 0
    · simp [hr]
    by_cases hs : Gamma (k + s) = 0
    · simp [hs]
    field_simp
  rw [hkey, norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)]
  have : ‖Gamma (k + p) / (Gamma k * (k : ℂ) ^ p) * (Gamma (k + q) / (Gamma k * (k : ℂ) ^ q)) /
        (Gamma (k + r) / (Gamma k * (k : ℂ) ^ r) * (Gamma (k + s) / (Gamma k * (k : ℂ) ^ s)))‖
        < 2 := by simpa using hk
  exact mul_le_mul_of_nonneg_right this.le (Real.rpow_nonneg (Nat.cast_nonneg k) _)

/-- If `Re (p + q - r - s) < -1`, the norms of `Γ(k + p) Γ(k + q) / (Γ(k + r) Γ(k + s))` are
  summable over `k ∈ ℕ`. -/
theorem summable_norm_Gamma_ratio (p q r s : ℂ) (h : (p + q - r - s).re < -1) :
    Summable fun k : ℕ =>
      ‖Gamma (k + p) * Gamma (k + q) * (Gamma (k + r))⁻¹ * (Gamma (k + s))⁻¹‖ :=
  summable_of_isBigO_nat (Real.summable_nat_rpow.mpr h) (isBigO_Gamma_ratio p q r s).norm_left

/-- Growth of the Gauss coefficients: `(a)_n (b)_n / ((c)_n n!) = O(n^{a+b-c-1})`. -/
theorem isBigO_gaussHGCoeff (a b c : ℂ) (hc : ∀ k : ℕ, c ≠ -k) :
    (gaussHGCoeff a b c) =O[atTop] fun n : ℕ => (n : ℝ) ^ (a + b - c - 1).re := by
  by_cases hpole : ∃ k : ℕ, a = -k ∨ b = -k
  · obtain ⟨k, hk⟩ := hpole
    refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [eventually_gt_atTop k] with n hn
    rcases hk with rfl | rfl <;> simp [gaussHGCoeff, poch_neg_nat_eq_zero hn]
  push Not at hpole
  have ht := tendsto_gaussHGCoeff_div_cpow (fun k => (hpole k).1) (fun k => (hpole k).2) hc
  have hb := ht.norm.isBoundedUnder_le
  obtain ⟨C, hC⟩ := hb
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Filter.eventually_map.mp hC, eventually_ge_atTop 1] with n hn hn1
  simp only [norm_div] at hn
  rw [Complex.norm_natCast_cpow_of_pos (by omega)] at hn
  have hpos : 0 < (n : ℝ) ^ (a + b - c - 1).re := Real.rpow_pos_of_pos (by exact_mod_cast hn1) _
  rw [div_le_iff₀ hpos] at hn
  rw [Real.norm_eq_abs, abs_of_pos hpos]
  exact hn

/-- Reflection for `1/Γ` away from the positive integers: `1/Γ(z) = Γ(1-z) sin(πz)/π`. -/
theorem recip_Gamma_eq_reflect {z : ℂ} (hz : ∀ m : ℕ, z ≠ m + 1) :
    (Gamma z)⁻¹ = Gamma (1 - z) * Complex.sin (π * z) / π := by
  by_cases hpole : ∃ m : ℕ, z = -m
  · obtain ⟨m, rfl⟩ := hpole
    have hs : Complex.sin (π * -(m : ℂ)) = 0 := by
      rw [Complex.sin_eq_zero_iff]; exact ⟨-(m : ℤ), by push_cast; ring⟩
    rw [Complex.Gamma_neg_nat_eq_zero, inv_zero, hs, mul_zero, zero_div]
  push Not at hpole
  have hsin : Complex.sin (π * z) ≠ 0 := by
    rw [Ne, Complex.sin_eq_zero_iff]
    rintro ⟨k, hk⟩
    have hk' : z = k := by
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      apply mul_left_cancel₀ hπ; rw [hk]; ring
    rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact hpole 0 (by rw [hk']; simp)
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hm
        exact hz j (by rw [hk']; push_cast; ring)
    · exact hpole m (by rw [hk']; simp)
  have h := Complex.Gamma_mul_Gamma_one_sub z
  have hGz : Gamma z ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero) hsin h.symm
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  rw [h, mul_comm z]
  field_simp

/-- `‖Γ(z)‖ = π / (‖sin(πz)‖ ‖Γ(1-z)‖)` away from the integers. -/
theorem norm_Gamma_eq_reflect {z : ℂ} (hz : ∀ n : ℤ, z ≠ n) :
    ‖Gamma z‖ = π / (‖Complex.sin (π * z)‖ * ‖Gamma (1 - z)‖) := by
  have h := Complex.Gamma_mul_Gamma_one_sub z
  have hsin : Complex.sin (π * z) ≠ 0 := by
    rw [Ne, Complex.sin_eq_zero_iff]
    rintro ⟨k, hk⟩
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact hz k (mul_left_cancel₀ hπ (by rw [hk]; ring))
  have hG1 : Gamma (1 - z) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h
    exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero) hsin h.symm
  have h2 : ‖Gamma z‖ * ‖Gamma (1 - z)‖ = π / ‖Complex.sin (π * z)‖ := by
    rw [← norm_mul, h, norm_div]; simp [abs_of_pos Real.pi_pos]
  rw [eq_div_iff (mul_ne_zero (norm_ne_zero_iff.mpr hsin) (norm_ne_zero_iff.mpr hG1))]
  rw [eq_div_iff (norm_ne_zero_iff.mpr hsin)] at h2
  linarith [h2]

/-- A uniform bound for `1/Γ` on the strip `-2 ≤ Re z ≤ 3`. -/
theorem exists_norm_recip_Gamma_mid :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, -2 ≤ z.re → z.re ≤ 3 →
      ‖(Gamma z)⁻¹‖ ≤ M * Real.exp (π * |z.im|) := by
  have hcont : ContinuousOn Real.Gamma (Icc (1 / 2 : ℝ) 3) := fun x hx =>
    (Real.differentiableAt_Gamma fun k h => by
      have := hx.1; rw [h] at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      ).continuousAt.continuousWithinAt
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (by norm_num : (1 / 2 : ℝ) ≤ 3)) hcont
  set m := Real.Gamma x₀
  have hm : 0 < m := Real.Gamma_pos_of_pos (by linarith [hx₀.1])
  set G₀ := max (Real.Gamma (1 / 2)) (Real.Gamma 3)
  refine ⟨max m⁻¹ (G₀ / π), le_trans (inv_nonneg.mpr hm.le) (le_max_left _ _), fun z hz1 hz2 => ?_⟩
  have hE : Real.exp (π * |z.im| / 2) ≤ Real.exp (π * |z.im|) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg z.im, Real.pi_pos])
  rcases le_or_gt (1 / 2) z.re with h | h
  · refine (norm_recip_Gamma_le_of_half_le h).trans ?_
    have hGz : m ≤ Real.Gamma z.re := hmin ⟨h, hz2⟩
    calc Real.exp (π * |z.im| / 2) / Real.Gamma z.re ≤ Real.exp (π * |z.im|) / m := by
          gcongr
      _ = m⁻¹ * Real.exp (π * |z.im|) := by ring
      _ ≤ max m⁻¹ (G₀ / π) * Real.exp (π * |z.im|) := by gcongr; exact le_max_left _ _
  · refine (norm_recip_Gamma_le_of_lt_half h).trans ?_
    have hG : Real.Gamma (1 - z.re) ≤ G₀ := Real.convexOn_Gamma.le_max_of_mem_Icc
      (show (1 / 2 : ℝ) ∈ Ioi 0 by norm_num) (show (3 : ℝ) ∈ Ioi 0 by norm_num)
      ⟨by linarith, by linarith⟩
    calc Real.exp (π * |z.im|) * Real.Gamma (1 - z.re) / π
        ≤ Real.exp (π * |z.im|) * G₀ / π := by gcongr
      _ = G₀ / π * Real.exp (π * |z.im|) := by ring
      _ ≤ max m⁻¹ (G₀ / π) * Real.exp (π * |z.im|) := by gcongr; exact le_max_right _ _

/-- Uniform vertical decay of `Γ(d + p)` in terms of `Im d`, on a strip of `Re (d + p)`. -/
theorem exists_norm_Gamma_add_le_strip (p : ℂ) {X₁ X₂ : ℝ} (hX₁ : 0 < X₁) :
    ∃ C : ℝ, ∃ K : ℕ, 0 ≤ C ∧ ∀ d : ℂ, X₁ ≤ (d + p).re → (d + p).re ≤ X₂ →
      ‖Gamma (d + p)‖ ≤ C * (1 + |d.im|) ^ K * Real.exp (-(π * |d.im|) / 2) := by
  obtain ⟨C, K, hC⟩ := exists_norm_Gamma_le_strip (X₂ := X₂) hX₁
  refine ⟨max C 0 * (1 + |p.im|) ^ K * Real.exp (π * |p.im| / 2), K, by positivity,
    fun d h1 h2 => ?_⟩
  refine (hC (d + p) h1 h2).trans ?_
  have him : (d + p).im = d.im + p.im := by simp
  rw [him]
  have e1 : (1 + |d.im + p.im|) ^ K ≤ ((1 + |p.im|) * (1 + |d.im|)) ^ K :=
    pow_le_pow_left₀ (by positivity) (one_add_abs_add_le _ _) K
  have e2 : Real.exp (-(π * |d.im + p.im|) / 2) ≤
      Real.exp (π * |p.im| / 2) * Real.exp (-(π * |d.im|) / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : |d.im| ≤ |d.im + p.im| + |p.im| := by
      have := abs_sub (d.im + p.im) p.im; simp at this; linarith
    nlinarith [Real.pi_pos]
  calc C * (1 + |d.im + p.im|) ^ K * Real.exp (-(π * |d.im + p.im|) / 2)
      ≤ max C 0 * ((1 + |p.im|) * (1 + |d.im|)) ^ K *
          (Real.exp (π * |p.im| / 2) * Real.exp (-(π * |d.im|) / 2)) := by
        gcongr
        · exact le_max_left _ _
    _ = max C 0 * (1 + |p.im|) ^ K * Real.exp (π * |p.im| / 2) * (1 + |d.im|) ^ K *
          Real.exp (-(π * |d.im|) / 2) := by rw [mul_pow]; ring

/-- Uniform vertical growth of `1/Γ(d + p)` in terms of `Im d`, on a strip `|Re (d + p)| ≤ X`. -/
theorem exists_norm_recip_Gamma_add_le_strip (p : ℂ) (X : ℝ) :
    ∃ C : ℝ, ∃ K : ℕ, 0 ≤ C ∧ ∀ d : ℂ, |(d + p).re| ≤ X →
      ‖(Gamma (d + p))⁻¹‖ ≤ C * (1 + |d.im|) ^ K * Real.exp (π * |d.im| / 2) := by
  obtain ⟨C, K, hC⟩ := exists_norm_recip_Gamma_le_strip X
  refine ⟨max C 0 * (1 + |p.im|) ^ K * Real.exp (π * |p.im| / 2), K, by positivity,
    fun d h1 => ?_⟩
  refine (hC (d + p) h1).trans ?_
  have him : (d + p).im = d.im + p.im := by simp
  rw [him]
  have e1 : (1 + |d.im + p.im|) ^ K ≤ ((1 + |p.im|) * (1 + |d.im|)) ^ K :=
    pow_le_pow_left₀ (by positivity) (one_add_abs_add_le _ _) K
  have e2 : Real.exp (π * |d.im + p.im| / 2) ≤
      Real.exp (π * |p.im| / 2) * Real.exp (π * |d.im| / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := abs_add_le d.im p.im
    nlinarith [Real.pi_pos]
  calc C * (1 + |d.im + p.im|) ^ K * Real.exp (π * |d.im + p.im| / 2)
      ≤ max C 0 * ((1 + |p.im|) * (1 + |d.im|)) ^ K *
          (Real.exp (π * |p.im| / 2) * Real.exp (π * |d.im| / 2)) := by
        gcongr
        · exact le_max_left _ _
    _ = max C 0 * (1 + |p.im|) ^ K * Real.exp (π * |p.im| / 2) * (1 + |d.im|) ^ K *
          Real.exp (π * |d.im| / 2) := by rw [mul_pow]; ring

/-- A majorant for `1/Γ(d + n)`, `n ∈ ℤ`, uniform for `x₁ ≤ Re d ≤ x₁ + 1`. -/
theorem exists_recip_Gamma_shift_bound (x₁ : ℝ) :
    ∃ B : ℤ → ℝ, (∀ n, 0 ≤ B n) ∧
      (∀ n : ℤ, (2 : ℝ) ≤ x₁ + n → B n = (Real.Gamma (x₁ + n))⁻¹) ∧
      (∀ n : ℤ, ¬ (2 : ℝ) ≤ x₁ + n → x₁ + 1 + n ≤ -1 → B n = Real.Gamma (1 - x₁ - n) / π) ∧
      ∀ (n : ℤ) (d : ℂ), x₁ ≤ d.re → d.re ≤ x₁ + 1 →
        ‖(Gamma (d + n))⁻¹‖ ≤ Real.exp (π * |d.im|) * B n := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_recip_Gamma_mid
  set B : ℤ → ℝ := fun n => if (2 : ℝ) ≤ x₁ + n then (Real.Gamma (x₁ + n))⁻¹
    else if x₁ + 1 + n ≤ -1 then Real.Gamma (1 - x₁ - n) / π else M with hBdef
  have hB0 : ∀ n, 0 ≤ B n := by
    intro n
    simp only [hBdef]
    split_ifs with h1 h2
    · exact inv_nonneg.mpr (Real.Gamma_pos_of_pos (by linarith)).le
    · exact div_nonneg (Real.Gamma_pos_of_pos (by linarith)).le Real.pi_pos.le
    · exact hM0
  have hbound : ∀ (n : ℤ) (d : ℂ), x₁ ≤ d.re → d.re ≤ x₁ + 1 →
      ‖(Gamma (d + n))⁻¹‖ ≤ Real.exp (π * |d.im|) * B n := by
    intro n d hd1 hd2
    have hre : (d + n).re = d.re + n := by simp
    have him : (d + n).im = d.im := by simp
    simp only [hBdef]
    split_ifs with h1 h2
    · have hz : 1 / 2 ≤ (d + n).re := by rw [hre]; linarith
      refine (norm_recip_Gamma_le_of_half_le hz).trans ?_
      rw [hre, him]
      have hmono : Real.Gamma (x₁ + n) ≤ Real.Gamma (d.re + n) :=
        Real.Gamma_strictMonoOn_Ici.monotoneOn (show (2 : ℝ) ≤ x₁ + n from h1)
          (show (2 : ℝ) ≤ d.re + n by linarith) (by linarith)
      have hpos := Real.Gamma_pos_of_pos (show 0 < x₁ + n by linarith)
      have hE : Real.exp (π * |d.im| / 2) ≤ Real.exp (π * |d.im|) :=
        Real.exp_le_exp.mpr (by nlinarith [abs_nonneg d.im, Real.pi_pos])
      calc Real.exp (π * |d.im| / 2) / Real.Gamma (d.re + n)
          ≤ Real.exp (π * |d.im|) / Real.Gamma (x₁ + n) := by gcongr
        _ = Real.exp (π * |d.im|) * (Real.Gamma (x₁ + n))⁻¹ := div_eq_mul_inv _ _
    · have hz : (d + n).re < 1 / 2 := by rw [hre]; linarith
      refine (norm_recip_Gamma_le_of_lt_half hz).trans ?_
      rw [hre, him]
      have hmono : Real.Gamma (1 - (d.re + n)) ≤ Real.Gamma (1 - x₁ - n) :=
        Real.Gamma_strictMonoOn_Ici.monotoneOn (show (2 : ℝ) ≤ 1 - (d.re + n) by linarith)
          (show (2 : ℝ) ≤ 1 - x₁ - n by linarith) (by linarith)
      calc Real.exp (π * |d.im|) * Real.Gamma (1 - (d.re + n)) / π
          ≤ Real.exp (π * |d.im|) * Real.Gamma (1 - x₁ - n) / π := by gcongr
        _ = Real.exp (π * |d.im|) * (Real.Gamma (1 - x₁ - n) / π) := by ring
    · have h1' : x₁ + n < 2 := lt_of_not_ge h1
      have h2' : -1 < x₁ + 1 + n := lt_of_not_ge h2
      have := hM (d + n) (by rw [hre]; linarith) (by rw [hre]; linarith)
      rw [him] at this
      linarith [this]
  exact ⟨B, hB0, fun n hn => by simp only [hBdef]; rw [ite_eq_left hn],
    fun n hn1 hn2 => by simp only [hBdef]; rw [ite_eq_right hn1, ite_eq_left hn2], hbound⟩

end CarlsonAux

namespace DougallAux

open CarlsonAux

variable {a b c : ℂ}

end DougallAux
end CarlsonApplications
end DLMF.Hypergeometric
end
end
