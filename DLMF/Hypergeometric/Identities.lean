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
# Summation identities and Chapter 3 transformations (AAR §§2.7–2.8, 3.3–3.5)

Kummer's theorem, Dixon's theorem, Whipple's `₇F₆` transformation, and Dougall's bilateral
sum are the main closed-form identities of AAR Chapter 3 that are absent from Mathlib.
The terminating Whipple transformation is proved from the rational Watson transformation
in `DLMF.Bailey`, taking finite q-Pochhammer limits with complex exponential parameters.
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

/-- The terms of Dougall's bilateral series. -/
def term (a b c d : ℂ) (n : ℤ) : ℂ :=
  Gamma (a + n) * Gamma (b + n) / (Gamma (c + n) * Gamma (d + n))

/-- The norm of a Dougall term factors into the norms of its four Gamma factors. -/
theorem norm_term (a b c d : ℂ) (n : ℤ) :
    ‖term a b c d n‖ = ‖Gamma (a + n)‖ * ‖Gamma (b + n)‖ * ‖(Gamma (c + n))⁻¹‖ *
      ‖(Gamma (d + n))⁻¹‖ := by
  rw [term, div_eq_mul_inv, mul_inv, norm_mul, norm_mul, norm_mul]; ring

/-- A majorant for Dougall's terms, uniform for `x₁ ≤ Re d ≤ x₁ + 1`. -/
theorem exists_bound (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k) {x₁ : ℝ}
    (hx₁ : 1 + (a + b - c).re < x₁) :
    ∃ u : ℤ → ℝ, Summable u ∧ (∀ n, 0 ≤ u n) ∧ ∀ (n : ℤ) (d : ℂ), x₁ ≤ d.re → d.re ≤ x₁ + 1 →
      ‖term a b c d n‖ ≤ Real.exp (π * |d.im|) * u n := by
  simp only [Complex.sub_re, Complex.add_re] at hx₁
  set h : ℤ → ℝ := fun n => ‖Gamma (a + n)‖ * ‖Gamma (b + n)‖ * ‖(Gamma (c + n))⁻¹‖ with hh
  obtain ⟨B, hB0, hBpos, hBneg, hbound⟩ := exists_recip_Gamma_shift_bound x₁
  refine ⟨fun n => h n * B n, ?_, fun n => mul_nonneg (by positivity) (hB0 n),
    fun n d hd1 hd2 => ?_⟩
  swap
  · rw [norm_term]
    calc ‖Gamma (a + n)‖ * ‖Gamma (b + n)‖ * ‖(Gamma (c + n))⁻¹‖ * ‖(Gamma (d + n))⁻¹‖
        = h n * ‖(Gamma (d + n))⁻¹‖ := rfl
      _ ≤ h n * (Real.exp (π * |d.im|) * B n) := by
          gcongr; exact hbound n d hd1 hd2
      _ = Real.exp (π * |d.im|) * (h n * B n) := by ring
  -- summability over `ℤ`
  refine Summable.of_nat_of_neg ?_ ?_
  · -- `n → +∞`: a Gamma ratio with exponent `Re(a+b-c) - x₁ < -1`
    refine Summable.of_norm_bounded_eventually_nat
      (summable_norm_Gamma_ratio a b c x₁ (by simp; linarith)) ?_
    obtain ⟨K₀, hK₀⟩ := exists_nat_ge (2 - x₁)
    filter_upwards [eventually_ge_atTop K₀] with k hk
    have hk' : (2 : ℝ) ≤ x₁ + ((k : ℤ) : ℝ) := by
      push_cast; linarith [(show (K₀ : ℝ) ≤ k by exact_mod_cast hk)]
    have hBk : B k = (Real.Gamma (x₁ + k))⁻¹ := by
      rw [hBpos _ hk']; push_cast; rfl
    have hpos := Real.Gamma_pos_of_pos (show 0 < x₁ + k by push_cast at hk'; linarith)
    have hGx : ‖(Gamma ((k : ℂ) + (x₁ : ℂ)))⁻¹‖ = (Real.Gamma (x₁ + k))⁻¹ := by
      rw [show (k : ℂ) + (x₁ : ℂ) = ((x₁ + k : ℝ) : ℂ) by push_cast; ring,
        Complex.Gamma_ofReal, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hpos)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hB0 _)), hBk]
    simp only [hh, norm_mul, hGx]
    push_cast
    rw [add_comm a, add_comm b, add_comm c]
  · -- `n → -∞`: reflect to a Gamma ratio at `1 - c, 1 - x₁; 1 - a, 1 - b`
    set Kc : ℝ := ‖Complex.sin (π * c)‖ / (‖Complex.sin (π * a)‖ * ‖Complex.sin (π * b)‖)
    refine Summable.of_norm_bounded_eventually_nat
      ((summable_norm_Gamma_ratio (1 - c) (1 - x₁) (1 - a) (1 - b)
        (by simp; linarith)).mul_left Kc) ?_
    obtain ⟨K₁, hK₁⟩ := exists_nat_ge (|x₁| + 2 + |c.re|)
    filter_upwards [eventually_ge_atTop K₁] with k hk
    have hkR' : |x₁| + 2 + |c.re| ≤ k := le_trans hK₁ (by exact_mod_cast hk)
    have hkR : x₁ + 2 + |c.re| ≤ k := le_trans (by linarith [le_abs_self x₁]) hkR'
    have hn1 : ¬ (2 : ℝ) ≤ x₁ + ((-(k : ℤ) : ℤ) : ℝ) := by
      push_cast; linarith [abs_nonneg c.re]
    have hn2 : x₁ + 1 + ((-(k : ℤ) : ℤ) : ℝ) ≤ -1 := by
      push_cast; linarith [abs_nonneg c.re]
    have hBk : B (-(k : ℤ)) = Real.Gamma (1 - x₁ + k) / π := by
      rw [hBneg _ hn1 hn2]; push_cast; ring_nf
    have hsa : ∀ n : ℤ, a - k ≠ n := fun n h => ha (n + k) (by push_cast; linear_combination h)
    have hsb : ∀ n : ℤ, b - k ≠ n := fun n h => hb (n + k) (by push_cast; linear_combination h)
    have hsc : ∀ m : ℕ, c - k ≠ m + 1 := by
      intro m h
      have := congrArg Complex.re h
      simp at this
      have : c.re ≤ |c.re| := le_abs_self _
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), abs_nonneg x₁]
    have hA := norm_Gamma_eq_reflect hsa
    have hB := norm_Gamma_eq_reflect hsb
    have hC := recip_Gamma_eq_reflect hsc
    have hsin (z : ℂ) : ‖Complex.sin (π * (z - k))‖ = ‖Complex.sin (π * z)‖ := by
      have := norm_sin_pi_mul_add_int z (-(k : ℤ)); push_cast at this
      rwa [← sub_eq_add_neg] at this
    have hGx : Real.Gamma (1 - x₁ + k) = ‖Gamma ((k : ℂ) + (1 - x₁ : ℂ))‖ := by
      have hpos := Real.Gamma_pos_of_pos (show 0 < 1 - x₁ + k by linarith [abs_nonneg c.re])
      rw [show (k : ℂ) + (1 - x₁ : ℂ) = ((1 - x₁ + k : ℝ) : ℂ) by push_cast; ring,
        Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    have hsa0 : Complex.sin (π * a) ≠ 0 := by
      rw [Ne, Complex.sin_eq_zero_iff]; rintro ⟨n, hn⟩
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact ha n (mul_left_cancel₀ hπ (by rw [hn]; ring))
    have hsb0 : Complex.sin (π * b) ≠ 0 := by
      rw [Ne, Complex.sin_eq_zero_iff]; rintro ⟨n, hn⟩
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact hb n (mul_left_cancel₀ hπ (by rw [hn]; ring))
    have hGa : Gamma ((k : ℂ) + (1 - a)) ≠ 0 := by
      intro h0
      have := hA; rw [show 1 - (a - k) = (k : ℂ) + (1 - a) by ring, h0, norm_zero,
        mul_zero, div_zero] at this
      exact (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero (fun m hm => hsa (-m)
        (by rw [hm]; push_cast; ring)))) this
    have hGb : Gamma ((k : ℂ) + (1 - b)) ≠ 0 := by
      intro h0
      have := hB; rw [show 1 - (b - k) = (k : ℂ) + (1 - b) by ring, h0, norm_zero,
        mul_zero, div_zero] at this
      exact (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero (fun m hm => hsb (-m)
        (by rw [hm]; push_cast; ring)))) this
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hB0 _)), hBk]
    simp only [hh]
    push_cast
    rw [← sub_eq_add_neg, ← sub_eq_add_neg, ← sub_eq_add_neg, hA, hB, hC,
      show 1 - (a - k) = (k : ℂ) + (1 - a) by ring, show 1 - (b - k) = (k : ℂ) + (1 - b) by ring,
      show 1 - (c - k) = (k : ℂ) + (1 - c) by ring, hsin, hsin, hGx, norm_div, norm_mul,
      norm_mul, norm_mul, norm_mul, norm_inv, norm_inv, hsin]
    have hπn : ‖(π : ℂ)‖ = π := by simp [abs_of_pos Real.pi_pos]
    rw [hπn]
    simp only [Kc]
    have h1 := norm_ne_zero_iff.mpr hsa0
    have h2 := norm_ne_zero_iff.mpr hsb0
    have h3 := norm_ne_zero_iff.mpr hGa
    have h4 := norm_ne_zero_iff.mpr hGb
    have hπ0 : π ≠ 0 := Real.pi_ne_zero
    apply le_of_eq
    field_simp

/-- Dougall's bilateral series converges absolutely when `a, b` are not integers and `Re d > 1 + Re
  (a + b - c)`. -/
theorem summable_term (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k) {d : ℂ}
    (hd : 1 + (a + b - c).re < d.re) : Summable (term a b c d) := by
  obtain ⟨u, hu, -, hbd⟩ := exists_bound (c := c) ha hb hd
  exact Summable.of_norm_bounded (hu.mul_left (Real.exp (π * |d.im|)))
    fun n => hbd n d le_rfl (by linarith)

/-- Dougall's sum is holomorphic in `d` on its half-plane of convergence. -/
theorem differentiableOn_tsum (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k) :
    DifferentiableOn ℂ (fun d => ∑' n : ℤ, term a b c d n)
      {d : ℂ | 1 + (a + b - c).re < d.re} := by
  intro d₀ hd₀
  simp only [Set.mem_ofPred_eq] at hd₀
  set r : ℝ := min (1 / 2) ((d₀.re - (1 + (a + b - c).re)) / 2) with hr
  have hr0 : 0 < r := lt_min (by norm_num) (by linarith)
  have hr1 : r ≤ 1 / 2 := min_le_left _ _
  have hr2 : r ≤ (d₀.re - (1 + (a + b - c).re)) / 2 := min_le_right _ _
  obtain ⟨u, hu, hu0, hbd⟩ := exists_bound (c := c) ha hb (x₁ := d₀.re - r) (by linarith)
  have hball : DifferentiableOn ℂ (fun d => ∑' n : ℤ, term a b c d n) (Metric.ball d₀ r) := by
    refine differentiableOn_tsum_of_summable_norm
      (hu.mul_left (Real.exp (π * (|d₀.im| + 1)))) (fun n => ?_) Metric.isOpen_ball
      (fun n d hd => ?_)
    · have hfun : (fun d => term a b c d n) = fun d =>
          Gamma (a + n) * Gamma (b + n) * (Gamma (c + n))⁻¹ * (Gamma (d + n))⁻¹ := by
        funext d; rw [term, div_eq_mul_inv, mul_inv]; ring
      rw [hfun]
      exact ((Complex.differentiable_one_div_Gamma.comp
        (differentiable_id.add_const _)).const_mul _).differentiableOn
    · have hdist : ‖d - d₀‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hd
      have hre : |d.re - d₀.re| < r :=
        lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (d - d₀)) hdist
      have him : |d.im - d₀.im| < r :=
        lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (d - d₀)) hdist
      refine (hbd n d (by linarith [abs_lt.mp hre]) (by linarith [abs_lt.mp hre])).trans ?_
      have := hu0 n
      gcongr
      have : |d.im| ≤ |d₀.im| + |d.im - d₀.im| := by
        have := abs_add_le d₀.im (d.im - d₀.im); simp at this; linarith [abs_sub_comm d.im d₀.im]
      linarith [abs_lt.mp him]
  exact (hball.differentiableAt (Metric.ball_mem_nhds _ hr0)).differentiableWithinAt

/-- Termwise telescoping identity behind the recurrence in `d`. -/
theorem term_recurrence (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k) (d : ℂ) (n : ℤ) :
    (d - a) * (d - b) * term a b c (d + 1) n - (c + d - a - b - 1) * term a b c d n =
      term a b (c - 1) d (n + 1) - term a b (c - 1) d n := by
  have hA : a + n ≠ 0 := fun h => ha (-n) (by push_cast; linear_combination h)
  have hB : b + n ≠ 0 := fun h => hb (-n) (by push_cast; linear_combination h)
  have e1 : Gamma (a + ((n + 1 : ℤ) : ℂ)) = (a + n) * Gamma (a + n) := by
    rw [show a + ((n + 1 : ℤ) : ℂ) = (a + n) + 1 by push_cast; ring, Complex.Gamma_add_one _ hA]
  have e2 : Gamma (b + ((n + 1 : ℤ) : ℂ)) = (b + n) * Gamma (b + n) := by
    rw [show b + ((n + 1 : ℤ) : ℂ) = (b + n) + 1 by push_cast; ring, Complex.Gamma_add_one _ hB]
  have e3 : (Gamma (c - 1 + n))⁻¹ = (c - 1 + n) * (Gamma (c + n))⁻¹ := by
    rw [← mul_recip_Gamma_add_one (c - 1 + n)]; ring_nf
  have e4 : (Gamma (d + n))⁻¹ = (d + n) * (Gamma (d + n + 1))⁻¹ := by
    rw [← mul_recip_Gamma_add_one (d + n)]
  have e5 : c - 1 + ((n + 1 : ℤ) : ℂ) = c + n := by push_cast; ring
  have e6 : d + 1 + (n : ℂ) = d + n + 1 := by ring
  have e7 : d + ((n + 1 : ℤ) : ℂ) = d + n + 1 := by push_cast; ring
  simp only [term, div_eq_mul_inv, mul_inv]
  rw [e1, e2, e3, e5, e6, e7, e4]
  ring

/-- The first-order recurrence of Dougall's sum in `d`. -/
theorem tsum_recurrence (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k) {d : ℂ}
    (hd : 2 + (a + b - c).re < d.re) :
    (d - a) * (d - b) * ∑' n : ℤ, term a b c (d + 1) n =
      (c + d - a - b - 1) * ∑' n : ℤ, term a b c d n := by
  have h1 : Summable (term a b c (d + 1)) := summable_term ha hb (by simp at hd ⊢; linarith)
  have h2 : Summable (term a b c d) := summable_term ha hb (by linarith)
  have h3 : Summable (term a b (c - 1) d) :=
    summable_term ha hb (by simp at hd ⊢; linarith)
  have h4 : Summable fun n : ℤ => term a b (c - 1) d (n + 1) :=
    (Equiv.addRight (1 : ℤ)).summable_iff.mpr h3
  have hshift : ∑' n : ℤ, term a b (c - 1) d (n + 1) = ∑' n : ℤ, term a b (c - 1) d n :=
    (Equiv.addRight (1 : ℤ)).tsum_eq (term a b (c - 1) d)
  rw [← sub_eq_zero, ← tsum_mul_left, ← tsum_mul_left,
    ← (h1.mul_left _).tsum_sub (h2.mul_left _)]
  simp_rw [term_recurrence (c := c) ha hb d]
  rw [h4.tsum_sub h3, hshift, sub_self]

/-- `sin(π(z + j)) = (-1)^j sin(πz)` in the form used below. -/
theorem sin_pi_mul_add_int (z : ℂ) (j : ℤ) :
    Complex.sin (π * (z + j)) = ((j.negOnePow : ℤ) : ℂ) * Complex.sin (π * z) := by
  rw [show (π : ℂ) * (z + j) = π * z + j * π by ring, Complex.sin_antiperiodic.add_int_mul_eq j]

/-- `((-1)^j)² = 1` for `j ∈ ℤ`, cast to `ℂ`. -/
theorem negOnePow_sq_cast (j : ℤ) : ((j.negOnePow : ℤ) : ℂ) * ((j.negOnePow : ℤ) : ℂ) = 1 := by
  rcases Int.isUnit_iff.mp (Int.negOnePow j).isUnit with h | h <;> simp [h]

/-- **Dougall's sum at an integer `d`**, from Gauss's summation. -/
theorem tsum_at_int (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k) (m : ℤ)
    (hγ : ∀ k : ℕ, c + 1 - m ≠ -k) (hconv : 1 + (a + b).re < (c + m).re) :
    ∑' n : ℤ, term a b c m n =
      π ^ 2 * Gamma (c + m - a - b - 1) /
        (Complex.sin (π * a) * Complex.sin (π * b) * Gamma (c - a) * Gamma (m - a) *
          Gamma (c - b) * Gamma (m - b)) := by
  set α := a + 1 - m with hα
  set β := b + 1 - m with hβ
  set γ := c + 1 - m with hγdef
  -- the terms with `n + m ≤ 0` vanish
  set g : ℕ → ℤ := fun k => (k : ℤ) + 1 - m with hg
  have hginj : Function.Injective g := fun i j h => by
    simp only [hg] at h; exact_mod_cast (show (i : ℤ) = j by linarith)
  have hsupp : Function.support (term a b c m) ⊆ Set.range g := by
    intro n hn
    by_contra hnot
    apply hn
    have hle : n + m ≤ 0 := by
      by_contra hlt
      push Not at hlt
      exact hnot ⟨(n + m - 1).toNat, by simp only [hg]; rw [Int.toNat_of_nonneg (by omega)]; ring⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, n + m = -(j : ℤ) := ⟨(-(n + m)).toNat, by omega⟩
    have : (m : ℂ) + n = -(j : ℂ) := by exact_mod_cast (show (m : ℤ) + n = -(j : ℤ) by omega)
    simp only [term, this, Complex.Gamma_neg_nat_eq_zero, mul_zero, div_zero]
  rw [← hginj.tsum_eq hsupp]
  -- each surviving term is a Gauss coefficient
  have hαn : ∀ k : ℕ, α ≠ -k := fun k h => ha (m - 1 - k) (by
    rw [hα] at h; push_cast; linear_combination h)
  have hβn : ∀ k : ℕ, β ≠ -k := fun k h => hb (m - 1 - k) (by
    rw [hβ] at h; push_cast; linear_combination h)
  have hGα : Gamma α ≠ 0 := Complex.Gamma_ne_zero hαn
  have hGβ : Gamma β ≠ 0 := Complex.Gamma_ne_zero hβn
  have hGγ : Gamma γ ≠ 0 := Complex.Gamma_ne_zero hγ
  have hterm : ∀ k : ℕ, term a b c m (g k) =
      Gamma α * Gamma β / Gamma γ * gaussHGCoeff α β γ k := by
    intro k
    have e1 : a + ((g k : ℤ) : ℂ) = α + k := by simp only [hg, hα]; push_cast; ring
    have e2 : b + ((g k : ℤ) : ℂ) = β + k := by simp only [hg, hβ]; push_cast; ring
    have e3 : c + ((g k : ℤ) : ℂ) = γ + k := by simp only [hg, hγdef]; push_cast; ring
    have e4 : (m : ℂ) + ((g k : ℤ) : ℂ) = k + 1 := by simp only [hg]; push_cast; ring
    have pα : Gamma (α + k) = Gamma α * poch α k := by
      have h := Complex.Gamma_add_nat_div_Gamma_eq (n := k) α hαn
      rw [div_eq_iff hGα] at h
      rw [h, poch, mul_comm]
    have pβ : Gamma (β + k) = Gamma β * poch β k := by
      have h := Complex.Gamma_add_nat_div_Gamma_eq (n := k) β hβn
      rw [div_eq_iff hGβ] at h
      rw [h, poch, mul_comm]
    have pγ : Gamma (γ + k) = Gamma γ * poch γ k := by
      have h := Complex.Gamma_add_nat_div_Gamma_eq (n := k) γ hγ
      rw [div_eq_iff hGγ] at h
      rw [h, poch, mul_comm]
    have hpγ : poch γ k ≠ 0 := poch_ne_zero_of_not_neg_nat hγ k
    have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    rw [term, e1, e2, e3, e4, Complex.Gamma_nat_eq_factorial, pα, pβ, pγ, gaussHGCoeff]
    field_simp
  simp_rw [hterm]
  rw [tsum_mul_left, ← ordinaryHypergeometric_one_eq_tsum]
  have hre : 0 < (γ - α - β).re := by
    simp only [hα, hβ, hγdef, Complex.sub_re, Complex.add_re, Complex.one_re] at hconv ⊢
    linarith
  rw [gauss_summation hγ hre]
  have e5 : γ - α - β = c + m - a - b - 1 := by simp only [hα, hβ, hγdef]; ring
  have e6 : γ - α = c - a := by simp only [hα, hγdef]; ring
  have e7 : γ - β = c - b := by simp only [hβ, hγdef]; ring
  rw [e5, e6, e7]
  -- reflection: `Γ(α) Γ(m - a) = π / sin(πα)`, and likewise for `β`
  have rα := Complex.Gamma_mul_Gamma_one_sub α
  have rβ := Complex.Gamma_mul_Gamma_one_sub β
  rw [show 1 - α = (m : ℂ) - a by simp only [hα]; ring] at rα
  rw [show 1 - β = (m : ℂ) - b by simp only [hβ]; ring] at rβ
  have sα : Complex.sin (π * α) = (((1 - m).negOnePow : ℤ) : ℂ) * Complex.sin (π * a) := by
    rw [← sin_pi_mul_add_int]; congr 1; simp only [hα]; push_cast; ring
  have sβ : Complex.sin (π * β) = (((1 - m).negOnePow : ℤ) : ℂ) * Complex.sin (π * b) := by
    rw [← sin_pi_mul_add_int]; congr 1; simp only [hβ]; push_cast; ring
  have hsa0 : Complex.sin (π * a) ≠ 0 := by
    rw [Ne, Complex.sin_eq_zero_iff]; rintro ⟨n, hn⟩
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact ha n (mul_left_cancel₀ hπ (by rw [hn]; ring))
  have hsb0 : Complex.sin (π * b) ≠ 0 := by
    rw [Ne, Complex.sin_eq_zero_iff]; rintro ⟨n, hn⟩
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact hb n (mul_left_cancel₀ hπ (by rw [hn]; ring))
  have hma : Gamma ((m : ℂ) - a) ≠ 0 := Complex.Gamma_ne_zero fun k h =>
    ha (m + k) (by push_cast; linear_combination -h)
  have hmb : Gamma ((m : ℂ) - b) ≠ 0 := Complex.Gamma_ne_zero fun k h =>
    hb (m + k) (by push_cast; linear_combination -h)
  have hs := negOnePow_sq_cast (1 - m)
  set s : ℂ := (((1 - m).negOnePow : ℤ) : ℂ)
  have hs0 : s ≠ 0 := by intro h0; rw [h0, zero_mul] at hs; exact zero_ne_one hs
  rw [sα] at rα
  rw [sβ] at rβ
  have hGα' : Gamma α = π / (s * Complex.sin (π * a)) / Gamma ((m : ℂ) - a) := by
    rw [← rα]; field_simp
  have hGβ' : Gamma β = π / (s * Complex.sin (π * b)) / Gamma ((m : ℂ) - b) := by
    rw [← rβ]; field_simp
  rw [hGα', hGβ']
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  by_cases hca : Gamma (c - a) = 0
  · simp [hca]
  by_cases hcb : Gamma (c - b) = 0
  · simp [hcb]
  field_simp
  linear_combination (-Gamma (c + m - a - b - 1)) * hs

/-- **Dougall's bilateral sum** for non-integral `c`, by Carlson's theorem in `d`: the sum times
`Γ(d-a)Γ(d-b)/Γ(c+d-a-b-1)` is `1`-periodic in `d`, of exponential type `π/2` on vertical lines,
and takes the right value at the integers by Gauss's summation. -/
theorem tsum_eq_of_not_int (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k) (hc : ∀ k : ℤ, c ≠ k)
    {d : ℂ} (hconv : 1 + (a + b).re < (c + d).re) :
    ∑' n : ℤ, term a b c d n =
      π ^ 2 * Gamma (c + d - a - b - 1) /
        (Complex.sin (π * a) * Complex.sin (π * b) * Gamma (c - a) * Gamma (d - a) *
          Gamma (c - b) * Gamma (d - b)) := by
  set L : ℂ → ℂ := fun d => ∑' n : ℤ, term a b c d n with hL
  set K : ℂ := π ^ 2 /
    (Complex.sin (π * a) * Complex.sin (π * b) * Gamma (c - a) * Gamma (c - b)) with hK
  set R : ℂ → ℂ := fun d =>
    K * Gamma (c + d - a - b - 1) * (Gamma (d - a))⁻¹ * (Gamma (d - b))⁻¹ with hR
  have hRform : ∀ d : ℂ, π ^ 2 * Gamma (c + d - a - b - 1) /
      (Complex.sin (π * a) * Complex.sin (π * b) * Gamma (c - a) * Gamma (d - a) *
        Gamma (c - b) * Gamma (d - b)) = R d := by
    intro d; simp only [hR, hK, div_eq_mul_inv, mul_inv]; ring
  rw [hRform]
  set N : ℂ → ℂ := fun d =>
    Gamma (d - a) * Gamma (d - b) * (Gamma (c + d - a - b - 1))⁻¹ with hN
  set s : ℝ := (a + b - c).re with hs
  have hsre : s = a.re + b.re - c.re := by simp [hs]
  obtain ⟨m₀, hm₀⟩ := exists_nat_ge (4 + |s| + |a.re| + |b.re|)
  have hm₀' : (4 : ℝ) + |s| + |a.re| + |b.re| ≤ m₀ := hm₀
  have hsa := le_abs_self s
  have hna := neg_abs_le a.re
  have hnb := neg_abs_le b.re
  have hpa := le_abs_self a.re
  have hpb := le_abs_self b.re
  have hns := neg_abs_le s
  have hreg : ∀ d : ℂ, (m₀ : ℝ) - 1 / 2 < d.re →
      2 + s < d.re ∧ 0 < (d - a).re ∧ 0 < (d - b).re ∧ 0 < (c + d - a - b - 1).re := by
    intro d hd
    refine ⟨by linarith [abs_nonneg a.re, abs_nonneg b.re], ?_, ?_, ?_⟩
    · simp only [Complex.sub_re]; linarith [abs_nonneg s, abs_nonneg b.re]
    · simp only [Complex.sub_re]; linarith [abs_nonneg s, abs_nonneg a.re]
    · simp only [Complex.sub_re, Complex.add_re, Complex.one_re]
      linarith [abs_nonneg a.re, abs_nonneg b.re]
  have hne : ∀ d : ℂ, (m₀ : ℝ) - 1 / 2 < d.re →
      Gamma (d - a) ≠ 0 ∧ Gamma (d - b) ≠ 0 ∧ Gamma (c + d - a - b - 1) ≠ 0 ∧
        d - a ≠ 0 ∧ d - b ≠ 0 ∧ c + d - a - b - 1 ≠ 0 := by
    intro d hd
    obtain ⟨-, h1, h2, h3⟩ := hreg d hd
    exact ⟨Complex.Gamma_ne_zero_of_re_pos h1, Complex.Gamma_ne_zero_of_re_pos h2,
      Complex.Gamma_ne_zero_of_re_pos h3, fun h => by rw [h] at h1; simp at h1,
      fun h => by rw [h] at h2; simp at h2, fun h => by rw [h] at h3; simp at h3⟩
  set F : ℂ → ℂ := fun w => L (m₀ + w) * N (m₀ + w) - K with hF
  -- holomorphy
  have hLd : DifferentiableOn ℂ L {d : ℂ | 1 + s < d.re} := differentiableOn_tsum ha hb
  have hFd : DifferentiableOn ℂ F {w : ℂ | -(1 / 2) < w.re} := by
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw
    have hd : (m₀ : ℝ) - 1 / 2 < ((m₀ : ℂ) + w).re := by simp; linarith
    obtain ⟨hd2, h1, h2, h3⟩ := hreg _ hd
    apply DifferentiableAt.differentiableWithinAt
    have hLw : DifferentiableAt ℂ (fun w => L (m₀ + w)) w := by
      have hU : {d : ℂ | 1 + s < d.re} ∈ 𝓝 ((m₀ : ℂ) + w) :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
          simp only [Set.mem_ofPred_eq]; linarith)
      exact (hLd.differentiableAt hU).comp w (differentiableAt_id.const_add _)
    have hG1 : DifferentiableAt ℂ (fun w => Gamma ((m₀ : ℂ) + w - a)) w :=
      (Complex.differentiableAt_Gamma _ fun m hm => by
        rw [hm] at h1; simp at h1; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).comp w
        ((differentiableAt_id.const_add _).sub_const _)
    have hG2 : DifferentiableAt ℂ (fun w => Gamma ((m₀ : ℂ) + w - b)) w :=
      (Complex.differentiableAt_Gamma _ fun m hm => by
        rw [hm] at h2; simp at h2; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).comp w
        ((differentiableAt_id.const_add _).sub_const _)
    have hG3 : DifferentiableAt ℂ (fun w => (Gamma (c + ((m₀ : ℂ) + w) - a - b - 1))⁻¹) w :=
      (Complex.differentiable_one_div_Gamma _).comp w (by fun_prop)
    exact ((hLw.mul ((hG1.mul hG2).mul hG3)).sub_const K)
  -- periodicity
  have hper : ∀ w : ℂ, 0 ≤ w.re → F (w + 1) = F w := by
    intro w hw
    set d : ℂ := (m₀ : ℂ) + w with hd
    have hdre : (m₀ : ℝ) - 1 / 2 < d.re := by simp [hd]; linarith
    obtain ⟨hd2, -, -, -⟩ := hreg d hdre
    obtain ⟨-, -, hG3, hda, hdb, he⟩ := hne d hdre
    have hrec := tsum_recurrence (c := c) ha hb (d := d) hd2
    have e1 : (m₀ : ℂ) + (w + 1) = d + 1 := by rw [hd]; ring
    simp only [hF]
    rw [e1, ← hd]
    congr 1
    simp only [hN, hL]
    have g1 : Gamma (d + 1 - a) = (d - a) * Gamma (d - a) := by
      rw [show d + 1 - a = (d - a) + 1 by ring, Complex.Gamma_add_one _ hda]
    have g2 : Gamma (d + 1 - b) = (d - b) * Gamma (d - b) := by
      rw [show d + 1 - b = (d - b) + 1 by ring, Complex.Gamma_add_one _ hdb]
    have g3 : Gamma (c + (d + 1) - a - b - 1) =
        (c + d - a - b - 1) * Gamma (c + d - a - b - 1) := by
      rw [show c + (d + 1) - a - b - 1 = (c + d - a - b - 1) + 1 by ring,
        Complex.Gamma_add_one _ he]
    rw [g1, g2, g3, mul_inv]
    field_simp
    linear_combination (Gamma (d - a) * Gamma (d - b)) * hrec
  -- the value at `0`, from Gauss's summation at `d = m₀`
  have hF0 : F 0 = 0 := by
    have hγ : ∀ k : ℕ, c + 1 - ((m₀ : ℤ) : ℂ) ≠ -k := fun k h =>
      hc (m₀ - 1 - k) (by push_cast at h ⊢; linear_combination h)
    have hcv : 1 + (a + b).re < (c + ((m₀ : ℤ) : ℂ)).re := by
      simp only [Complex.add_re, Int.cast_natCast, Complex.natCast_re]
      linarith [abs_nonneg a.re, abs_nonneg b.re, abs_nonneg s, hsre]
    have h := tsum_at_int (c := c) ha hb (m₀ : ℤ) hγ hcv
    simp only [Int.cast_natCast] at h
    have hdre : (m₀ : ℝ) - 1 / 2 < ((m₀ : ℂ)).re := by simp
    obtain ⟨hGa, hGb, hG3, -, -, -⟩ := hne _ hdre
    simp only [hF, add_zero, hL, hN]
    rw [h, hRform, sub_eq_zero]
    simp only [hR]
    field_simp
  -- the strip bound
  obtain ⟨C₁, K₁, hC₁, hb₁⟩ := exists_norm_Gamma_add_le_strip (-a)
    (X₁ := m₀ - a.re) (X₂ := m₀ + 1 - a.re) (by linarith [abs_nonneg s, abs_nonneg b.re])
  obtain ⟨C₂, K₂, hC₂, hb₂⟩ := exists_norm_Gamma_add_le_strip (-b)
    (X₁ := m₀ - b.re) (X₂ := m₀ + 1 - b.re) (by linarith [abs_nonneg s, abs_nonneg a.re])
  obtain ⟨C₃, K₃, hC₃, hb₃⟩ := exists_norm_recip_Gamma_add_le_strip (c - a - b - 1)
    (m₀ + 1 + |(c - a - b - 1).re|)
  obtain ⟨u, hu, hu0, hbd⟩ := exists_bound (c := c) ha hb (x₁ := m₀)
    (by linarith [abs_nonneg a.re, abs_nonneg b.re])
  set S := ∑' n : ℤ, u n with hS
  have hS0 : 0 ≤ S := tsum_nonneg hu0
  have hstrip : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖F w‖ ≤ (S * (C₁ * C₂ * C₃) + ‖K‖) * (1 + |w.im|) ^ (K₁ + K₂ + K₃) *
        Real.exp (π / 2 * |w.im|) := by
    intro w hw0 hw1
    set d : ℂ := (m₀ : ℂ) + w with hd
    have hdre0 : (m₀ : ℝ) ≤ d.re := by simp [hd]; linarith
    have hdre1 : d.re ≤ m₀ + 1 := by simp [hd]; linarith
    have hdim : d.im = w.im := by simp [hd]
    set y := w.im
    have hLb : ‖L d‖ ≤ Real.exp (π * |y|) * S := by
      rw [← hdim]
      exact tsum_of_norm_bounded (hu.hasSum.mul_left _) fun n => hbd n d hdre0 hdre1
    have h1 : ‖Gamma (d - a)‖ ≤ C₁ * (1 + |y|) ^ K₁ * Real.exp (-(π * |y|) / 2) := by
      rw [← hdim, sub_eq_add_neg]
      exact hb₁ d (by simp; linarith) (by simp; linarith)
    have h2 : ‖Gamma (d - b)‖ ≤ C₂ * (1 + |y|) ^ K₂ * Real.exp (-(π * |y|) / 2) := by
      rw [← hdim, sub_eq_add_neg]
      exact hb₂ d (by simp; linarith) (by simp; linarith)
    have h3 : ‖(Gamma (c + d - a - b - 1))⁻¹‖ ≤
        C₃ * (1 + |y|) ^ K₃ * Real.exp (π * |y| / 2) := by
      rw [← hdim, show c + d - a - b - 1 = d + (c - a - b - 1) by ring]
      refine hb₃ d ?_
      rw [abs_le]
      have := abs_le.mp (le_refl |(c - a - b - 1).re|)
      constructor
      · simp only [Complex.add_re]; linarith [neg_abs_le (c - a - b - 1).re]
      · simp only [Complex.add_re]; linarith [le_abs_self (c - a - b - 1).re]
    have hNb : ‖N d‖ ≤ (C₁ * C₂ * C₃) * (1 + |y|) ^ (K₁ + K₂ + K₃) *
        Real.exp (-(π * |y|) / 2) := by
      simp only [hN, norm_mul]
      calc ‖Gamma (d - a)‖ * ‖Gamma (d - b)‖ * ‖(Gamma (c + d - a - b - 1))⁻¹‖
          ≤ (C₁ * (1 + |y|) ^ K₁ * Real.exp (-(π * |y|) / 2)) *
              (C₂ * (1 + |y|) ^ K₂ * Real.exp (-(π * |y|) / 2)) *
              (C₃ * (1 + |y|) ^ K₃ * Real.exp (π * |y| / 2)) := by
            gcongr
        _ = (C₁ * C₂ * C₃) * (1 + |y|) ^ (K₁ + K₂ + K₃) * Real.exp (-(π * |y|) / 2) := by
            have hEE : Real.exp (-(π * |y|) / 2) * Real.exp (π * |y| / 2) = 1 := by
              rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
            rw [pow_add, pow_add]
            linear_combination (C₁ * C₂ * C₃ * (1 + |y|) ^ K₁ * (1 + |y|) ^ K₂ *
              (1 + |y|) ^ K₃ * Real.exp (-(π * |y|) / 2)) * hEE
    have hpos : 1 ≤ (1 + |y|) ^ (K₁ + K₂ + K₃) * Real.exp (π / 2 * |y|) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [abs_nonneg y]))
        (Real.one_le_exp (by positivity))
    calc ‖F w‖ = ‖L d * N d - K‖ := rfl
      _ ≤ ‖L d‖ * ‖N d‖ + ‖K‖ := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_mul]
      _ ≤ (Real.exp (π * |y|) * S) *
            ((C₁ * C₂ * C₃) * (1 + |y|) ^ (K₁ + K₂ + K₃) * Real.exp (-(π * |y|) / 2)) +
            ‖K‖ * ((1 + |y|) ^ (K₁ + K₂ + K₃) * Real.exp (π / 2 * |y|)) := by
          gcongr
          · exact le_mul_of_one_le_right (norm_nonneg _) hpos
      _ = (S * (C₁ * C₂ * C₃) + ‖K‖) * (1 + |y|) ^ (K₁ + K₂ + K₃) *
            Real.exp (π / 2 * |y|) := by
          have : Real.exp (π * |y|) * Real.exp (-(π * |y|) / 2) = Real.exp (π / 2 * |y|) := by
            rw [← Real.exp_add]; ring_nf
          linear_combination (S * (C₁ * C₂ * C₃) * (1 + |y|) ^ (K₁ + K₂ + K₃)) * this
  -- Carlson
  have hzero := CarlsonAux.eq_zero_of_periodic_of_bound (by norm_num : (0 : ℝ) < 1 / 2) hFd hper
    (σ := π / 2) (by linarith [Real.pi_pos]) hstrip hF0
  -- hence `L = R` on `Re d ≥ m₀`
  have hLR : ∀ d : ℂ, (m₀ : ℝ) ≤ d.re → L d = R d := by
    intro d hd
    have h := hzero (d - m₀) (by simp; linarith)
    simp only [hF, add_sub_cancel, sub_eq_zero] at h
    obtain ⟨hGa, hGb, hG3, -, -, -⟩ := hne d (by linarith)
    simp only [hN] at h
    simp only [hR]
    rw [← h]
    field_simp
  -- extend by the identity theorem
  set U : Set ℂ := {d : ℂ | 1 + s < d.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hdU : d ∈ U := by
    simp only [hU, Set.mem_ofPred_eq, hsre]
    simp only [Complex.add_re] at hconv
    linarith
  have hRd : DifferentiableOn ℂ R U := by
    intro z hz
    simp only [hU, Set.mem_ofPred_eq, hsre] at hz
    have hre : 0 < (c + z - a - b - 1).re := by
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; linarith
    apply DifferentiableAt.differentiableWithinAt
    have hG : DifferentiableAt ℂ (fun z => Gamma (c + z - a - b - 1)) z :=
      (Complex.differentiableAt_Gamma _ fun m hm => by
        rw [hm] at hre; simp at hre; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).comp z
        (by fun_prop)
    have hi1 : DifferentiableAt ℂ (fun z => (Gamma (z - a))⁻¹) z :=
      (Complex.differentiable_one_div_Gamma _).comp z (by fun_prop)
    have hi2 : DifferentiableAt ℂ (fun z => (Gamma (z - b))⁻¹) z :=
      (Complex.differentiable_one_div_Gamma _).comp z (by fun_prop)
    exact ((hG.const_mul K).mul hi1).mul hi2
  have hz₀ : (m₀ : ℂ) + 1 ∈ U := by
    simp only [hU, Set.mem_ofPred_eq]; simp
    linarith [abs_nonneg a.re, abs_nonneg b.re]
  have hev : L =ᶠ[𝓝 ((m₀ : ℂ) + 1)] R := by
    have hopen : {z : ℂ | (m₀ : ℝ) < z.re} ∈ 𝓝 ((m₀ : ℂ) + 1) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hopen] with z hz
    exact hLR z (le_of_lt hz)
  exact ((hLd.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hRd.analyticOnNhd hUo)
    (convex_halfSpace_re_gt (1 + s)).isPreconnected hz₀ hev) hdU

/-- Dougall's terms are symmetric in the denominator parameters `c` and `d`. -/
theorem term_comm (a b c d : ℂ) (n : ℤ) : term a b c d n = term a b d c n := by
  simp only [term, mul_comm (Gamma (c + n))]

/-- The right-hand side of Dougall's formula is symmetric in `c` and `d`. -/
theorem rhs_comm (a b c d : ℂ) :
    π ^ 2 * Gamma (d + c - a - b - 1) /
        (Complex.sin (π * a) * Complex.sin (π * b) * Gamma (d - a) * Gamma (c - a) *
          Gamma (d - b) * Gamma (c - b)) =
      π ^ 2 * Gamma (c + d - a - b - 1) /
        (Complex.sin (π * a) * Complex.sin (π * b) * Gamma (c - a) * Gamma (d - a) *
          Gamma (c - b) * Gamma (d - b)) := by
  rw [add_comm d c]; ring

/-- Dougall's sum when both `c` and `d` are integers, with `d ≤ c`. -/
theorem tsum_at_int_int (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k) {j m : ℤ} (hjm : m ≤ j)
    (hconv : 1 + (a + b).re < ((j : ℂ) + m).re) :
    ∑' n : ℤ, term a b j m n =
      π ^ 2 * Gamma (j + m - a - b - 1) /
        (Complex.sin (π * a) * Complex.sin (π * b) * Gamma (j - a) * Gamma (m - a) *
          Gamma (j - b) * Gamma (m - b)) := by
  refine tsum_at_int ha hb m (fun k h => ?_) hconv
  have h' : ((j + 1 - m : ℤ) : ℂ) = ((-(k : ℤ) : ℤ) : ℂ) := by push_cast; linear_combination h
  have := Int.cast_injective h'
  omega

end DougallAux

namespace DixonAux

open CarlsonAux

variable {a b : ℂ}

/-- The normalized terms `(a)_n (b)_n (c)_n / ((1+a-b)_n n! Γ(1+a-c+n))` of Dixon's series. -/
def s (a b c : ℂ) (n : ℕ) : ℂ :=
  gaussHGCoeff a b (1 + a - b) n * poch c n * (Gamma (1 + a - c + n))⁻¹

/-- The WZ certificate. -/
def H (a b c : ℂ) (n : ℕ) : ℂ :=
  gaussHGCoeff a b (1 + a - b) n * (a + n) * (b + n) * poch c n * (Gamma (2 + a - c + n))⁻¹

/-- The WZ relation for Dixon's series at `n = 0`. -/
theorem wz_zero (a b c : ℂ) :
    (1 + a / 2 - b - c) * s a b c 0 - (1 + a / 2 - c) * (1 + a - b - c) * s a b (c - 1) 0 =
      -(1 / 2) * H a b c 0 := by
  have e : (Gamma (1 + a - c))⁻¹ = (1 + a - c) * (Gamma (2 + a - c))⁻¹ := by
    rw [← mul_recip_Gamma_add_one]; ring_nf
  simp only [s, H, gaussHGCoeff, poch_zero, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero,
    add_zero, mul_one, div_one]
  rw [show 1 + a - (c - 1) = 2 + a - c by ring, e]
  ring

/-- The WZ relation for Dixon's series: the `c`-difference of `s` telescopes through the certificate
  `H`. -/
theorem wz_succ (hb : ∀ k : ℕ, 1 + a - b ≠ -k) (c : ℂ) (n : ℕ) :
    (1 + a / 2 - b - c) * s a b c (n + 1) -
        (1 + a / 2 - c) * (1 + a - b - c) * s a b (c - 1) (n + 1) =
      -(1 / 2) * (H a b c (n + 1) - H a b c n) := by
  have hp : poch (1 + a - b) n ≠ 0 := poch_ne_zero_of_not_neg_nat hb n
  have hq : 1 + a - b + n ≠ 0 := fun h => hb n (by linear_combination h)
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have e2 : (Gamma (2 + a - c + n))⁻¹ = (2 + a - c + n) * (Gamma (3 + a - c + n))⁻¹ := by
    rw [← mul_recip_Gamma_add_one]; ring_nf
  have c1 : poch (c - 1) (n + 1) = (c - 1) * poch c n := by
    rw [poch_succ_left]; ring_nf
  simp only [s, H]
  rw [c1]
  simp only [gaussHGCoeff, poch_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  rw [show 1 + a - c + ((n : ℂ) + 1) = 2 + a - c + n by ring,
    show 1 + a - (c - 1) + ((n : ℂ) + 1) = 3 + a - c + n by ring,
    show 2 + a - c + ((n : ℂ) + 1) = 3 + a - c + n by ring, e2]
  field_simp
  ring

/-- The normalized Dixon series. -/
def Lh (a b c : ℂ) : ℂ := ∑' n : ℕ, s a b c n

/-- **The recurrence in `c`**, from the WZ pair. -/
theorem recurrence (hb : ∀ k : ℕ, 1 + a - b ≠ -k) {c : ℂ} (h1 : Summable (s a b c))
    (h2 : Summable (s a b (c - 1))) (hH : Tendsto (H a b c) atTop (𝓝 0)) :
    (1 + a / 2 - b - c) * Lh a b c = (1 + a / 2 - c) * (1 + a - b - c) * Lh a b (c - 1) := by
  set T : ℕ → ℂ := fun n =>
    (1 + a / 2 - b - c) * s a b c n - (1 + a / 2 - c) * (1 + a - b - c) * s a b (c - 1) n
  have hT : Summable T := (h1.mul_left _).sub (h2.mul_left _)
  have hpartial : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), T n = -(1 / 2) * H a b c N := by
    intro N
    induction N with
    | zero => simp [T, wz_zero]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [T]
      rw [wz_succ hb]
      ring
  have hlim : Tendsto (fun N => ∑ n ∈ Finset.range N, T n) atTop (𝓝 (∑' n, T n)) :=
    hT.hasSum.tendsto_sum_nat
  have hlim' : Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), T n) atTop (𝓝 0) := by
    simp_rw [hpartial]; simpa using hH.const_mul (-(1 / 2) : ℂ)
  have h0 : ∑' n, T n = 0 :=
    tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).mpr hlim) hlim'
  simp only [T] at h0
  rw [(h1.mul_left _).tsum_sub (h2.mul_left _), tsum_mul_left, tsum_mul_left,
    sub_eq_zero] at h0
  exact h0

/-- The periodic normalization. -/
def P (a b c : ℂ) : ℂ :=
  Lh a b c * Gamma (1 + a / 2 - c) * Gamma (1 + a - b - c) * (Gamma (1 + a / 2 - b - c))⁻¹

/-- Under convergence, the normalization `P` is invariant under `c ↦ c - 1`. -/
theorem P_sub_one (hb : ∀ k : ℕ, 1 + a - b ≠ -k) {c : ℂ} (h1 : Summable (s a b c))
    (h2 : Summable (s a b (c - 1))) (hH : Tendsto (H a b c) atTop (𝓝 0))
    (hc1 : 1 + a / 2 - c ≠ 0) (hc2 : 1 + a - b - c ≠ 0) :
    P a b (c - 1) = P a b c := by
  have hrec := recurrence hb h1 h2 hH
  have g1 : Gamma (1 + a / 2 - (c - 1)) = (1 + a / 2 - c) * Gamma (1 + a / 2 - c) := by
    rw [show 1 + a / 2 - (c - 1) = (1 + a / 2 - c) + 1 by ring, Complex.Gamma_add_one _ hc1]
  have g2 : Gamma (1 + a - b - (c - 1)) = (1 + a - b - c) * Gamma (1 + a - b - c) := by
    rw [show 1 + a - b - (c - 1) = (1 + a - b - c) + 1 by ring, Complex.Gamma_add_one _ hc2]
  have g3 : (Gamma (1 + a / 2 - b - c))⁻¹ =
      (1 + a / 2 - b - c) * (Gamma (1 + a / 2 - b - (c - 1)))⁻¹ := by
    rw [← mul_recip_Gamma_add_one]; ring_nf
  simp only [P]
  rw [g1, g2, g3]
  linear_combination (Gamma (1 + a / 2 - c) * Gamma (1 + a - b - c) *
    (Gamma (1 + a / 2 - b - (c - 1)))⁻¹) * hrec.symm

/-- `(a + n)(b + n) = O(n²)`. -/
theorem isBigO_mul_add_mul_add (a b : ℂ) :
    (fun n : ℕ => (a + n) * (b + n)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (2 : ℝ) := by
  refine Asymptotics.IsBigO.of_bound ((‖a‖ + 1) * (‖b‖ + 1)) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : ‖a + n‖ ≤ (‖a‖ + 1) * n := by
    refine (norm_add_le _ _).trans ?_; simp; nlinarith [norm_nonneg a]
  have hb : ‖b + n‖ ≤ (‖b‖ + 1) * n := by
    refine (norm_add_le _ _).trans ?_; simp; nlinarith [norm_nonneg b]
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    show (n : ℝ) ^ (2 : ℝ) = n * n by rw [Real.rpow_two]; ring]
  calc ‖a + n‖ * ‖b + n‖ ≤ ((‖a‖ + 1) * n) * ((‖b‖ + 1) * n) :=
        mul_le_mul ha hb (norm_nonneg _) (by positivity)
    _ = (‖a‖ + 1) * (‖b‖ + 1) * (n * n) := by ring

/-- For `c = -j`, the Dixon terms vanish beyond index `j`. -/
theorem s_neg_nat_eq_zero (a b : ℂ) {j n : ℕ} (h : j < n) : s a b (-(j : ℂ)) n = 0 := by
  simp [s, poch_neg_nat_eq_zero h]

/-- For `c = -j`, the WZ certificate vanishes beyond index `j`. -/
theorem H_neg_nat_eq_zero (a b : ℂ) {j n : ℕ} (h : j < n) : H a b (-(j : ℂ)) n = 0 := by
  simp [H, poch_neg_nat_eq_zero h]

/-- For `c = -j` the Dixon series terminates, hence is summable. -/
theorem summable_s_neg_nat (a b : ℂ) (j : ℕ) : Summable (s a b (-(j : ℂ))) :=
  summable_of_ne_finset_zero (s := Finset.range (j + 1)) fun n hn => by
    simp only [Finset.mem_range, not_lt] at hn
    exact s_neg_nat_eq_zero a b (by omega)

/-- For `c = -j` the WZ certificate tends to `0`. -/
theorem tendsto_H_neg_nat (a b : ℂ) (j : ℕ) : Tendsto (H a b (-(j : ℂ))) atTop (𝓝 0) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [eventually_gt_atTop j] with n hn
    exact (H_neg_nat_eq_zero a b hn).symm)

/-- Convergence of the normalized Dixon series and decay of the certificate, for
`Re(1 + a/2 - b - c) > 0`. -/
theorem summable_s_and_tendsto_H (hb : ∀ k : ℕ, 1 + a - b ≠ -k) {c : ℂ}
    (hc : 0 < (1 + a / 2 - b - c).re) :
    Summable (s a b c) ∧ Tendsto (H a b c) atTop (𝓝 0) := by
  by_cases hneg : ∃ j : ℕ, c = -j
  · obtain ⟨j, rfl⟩ := hneg
    exact ⟨summable_s_neg_nat a b j, tendsto_H_neg_nat a b j⟩
  push Not at hneg
  have hGc : Gamma c ≠ 0 := Complex.Gamma_ne_zero hneg
  have hpoch : ∀ n : ℕ, poch c n = Gamma (n + c) * (Gamma c)⁻¹ := by
    intro n
    have h := Complex.Gamma_add_nat_div_Gamma_eq (n := n) c hneg
    rw [poch, ← h, add_comm, div_eq_mul_inv]
  have hone : ∀ n : ℕ, Gamma ((n : ℂ) + 1) * (Gamma ((n : ℂ) + 1))⁻¹ = 1 := fun n =>
    mul_inv_cancel₀ (by rw [Complex.Gamma_nat_eq_factorial]; exact_mod_cast n.factorial_ne_zero)
  have hcoef := isBigO_gaussHGCoeff a b (1 + a - b) hb
  have hre : (a + b - (1 + a - b) - 1).re = 2 * b.re - 2 := by simp; ring
  rw [hre] at hcoef
  have hcre : 0 < 1 + a.re / 2 - b.re - c.re := by simpa using hc
  constructor
  · -- `s_n = O(n^{2Re b - 2} · n^{2 Re c - Re a - 1})`
    have hrat := isBigO_Gamma_ratio c 1 (1 + a - c) 1
    have heq : (s a b c) = fun n : ℕ => (Gamma c)⁻¹ * (gaussHGCoeff a b (1 + a - b) n *
        (Gamma (n + c) * Gamma (n + 1) * (Gamma (n + (1 + a - c)))⁻¹ * (Gamma (n + 1))⁻¹)) := by
      funext n
      simp only [s, hpoch]
      rw [show (1 : ℂ) + a - c + n = n + (1 + a - c) by ring]
      have := hone n
      linear_combination (gaussHGCoeff a b (1 + a - b) n * Gamma (↑n + c) * (Gamma c)⁻¹ *
        (Gamma (↑n + (1 + a - c)))⁻¹) * this.symm
    rw [heq]
    refine Summable.mul_left _ (summable_of_isBigO_nat
      (Real.summable_nat_rpow.mpr (show (2 * b.re - 2) + (c + 1 - (1 + a - c) - 1).re < -1 by
        simp; linarith)) ?_)
    refine (hcoef.mul hrat).trans ?_
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [one_mul, ← Real.rpow_add hn0]
  · -- `H_n = O(n^{2 Re b + 2 Re c - Re a - 2})`, a negative exponent
    have hrat := isBigO_Gamma_ratio c 1 (2 + a - c) 1
    have hpoly := isBigO_mul_add_mul_add a b
    have heq : (H a b c) = fun n : ℕ => (Gamma c)⁻¹ * (gaussHGCoeff a b (1 + a - b) n *
        ((a + n) * (b + n)) *
        (Gamma (n + c) * Gamma (n + 1) * (Gamma (n + (2 + a - c)))⁻¹ * (Gamma (n + 1))⁻¹)) := by
      funext n
      simp only [H, hpoch]
      rw [show (2 : ℂ) + a - c + n = n + (2 + a - c) by ring]
      have := hone n
      linear_combination (gaussHGCoeff a b (1 + a - b) n * (a + n) * (b + n) *
        Gamma (↑n + c) * (Gamma c)⁻¹ * (Gamma (↑n + (2 + a - c)))⁻¹) * this.symm
    rw [heq]
    have hexp : (2 * b.re - 2) + 2 + (c + 1 - (2 + a - c) - 1).re < 0 := by simp; linarith
    have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ ((2 * b.re - 2) + 2 +
        (c + 1 - (2 + a - c) - 1).re)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (show 0 < -((2 * b.re - 2) + 2 +
        (c + 1 - (2 + a - c) - 1).re) by linarith)).comp tendsto_natCast_atTop_atTop
      refine this.congr fun n => ?_
      simp only [Function.comp, neg_neg]
    have hbig : (fun n : ℕ => gaussHGCoeff a b (1 + a - b) n * ((a + n) * (b + n)) *
        (Gamma (n + c) * Gamma (n + 1) * (Gamma (n + (2 + a - c)))⁻¹ * (Gamma (n + 1))⁻¹))
        =O[atTop] fun n : ℕ => (n : ℝ) ^ ((2 * b.re - 2) + 2 +
          (c + 1 - (2 + a - c) - 1).re) := by
      refine ((hcoef.mul hpoly).mul hrat).trans ?_
      refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [one_mul, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
    simpa using (hbig.trans_tendsto hlim).const_mul (Gamma c)⁻¹

/-- The constant `Γ(1+a/2)Γ(1+a-b)/(Γ(1+a)Γ(1+a/2-b))`. -/
def K (a b : ℂ) : ℂ :=
  Gamma (1 + a / 2) * Gamma (1 + a - b) * (Gamma (1 + a))⁻¹ * (Gamma (1 + a / 2 - b))⁻¹

/-- At `c = 0` the normalization `P` equals the constant `K`. -/
theorem P_zero (a b : ℂ) : P a b 0 = K a b := by
  have hL : Lh a b 0 = (Gamma (1 + a))⁻¹ := by
    rw [Lh, tsum_eq_single 0]
    · simp [s, gaussHGCoeff, poch_zero]
    · intro n hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      simp [s]
  simp only [P, K, hL, sub_zero]
  ring

/-- **Terminating Dixon** in normalized form: `P(-j) = K` for all `j`. -/
theorem P_neg_nat (ha : ∀ k : ℕ, 1 + a / 2 ≠ -k) (hb : ∀ k : ℕ, 1 + a - b ≠ -k) (j : ℕ) :
    P a b (-(j : ℂ)) = K a b := by
  induction j with
  | zero => simpa using P_zero a b
  | succ j ih =>
    have h := P_sub_one hb (c := -(j : ℂ)) (summable_s_neg_nat a b j)
      (by simpa [sub_eq_add_neg, add_comm] using summable_s_neg_nat a b (j + 1))
      (tendsto_H_neg_nat a b j)
      (fun h0 => ha j (by linear_combination h0)) (fun h0 => hb j (by linear_combination h0))
    rw [← ih, ← h]
    congr 1
    push_cast; ring

/-- `(c)_n / Γ(1-c) = (-1)^n / Γ(1-c-n)`, for every `c`. -/
theorem poch_mul_recip_Gamma_one_sub (c : ℂ) (n : ℕ) :
    poch c n * (Gamma (1 - c))⁻¹ = (-1) ^ n * (Gamma (1 - c - n))⁻¹ := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    have h := mul_recip_Gamma_add_one (-c - n)
    rw [show -c - (n : ℂ) + 1 = 1 - c - n by ring] at h
    rw [poch_succ, mul_right_comm, ih, show (1 : ℂ) - c - ((n + 1 : ℕ) : ℂ) = -c - n by
      push_cast; ring, ← h, pow_succ]
    ring

/-- `‖(c)ₙ‖ = ‖Γ(1 - c)‖ ‖1/Γ(1 - c - n)‖` when `Γ(1 - c) ≠ 0` (reflection form of the Pochhammer
  symbol). -/
theorem norm_poch_eq {c : ℂ} (hc : Gamma (1 - c) ≠ 0) (n : ℕ) :
    ‖poch c n‖ = ‖Gamma (1 - c)‖ * ‖(Gamma (1 - c - n))⁻¹‖ := by
  have h := congrArg norm (poch_mul_recip_Gamma_one_sub c n)
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_inv] at h
  rw [← h]
  field_simp [norm_ne_zero_iff.mpr hc]

/-- A majorant for the normalized Dixon terms, uniform for `x₁ ≤ Re(1-c) ≤ x₁ + 1`. -/
theorem exists_bound (hb : ∀ k : ℕ, 1 + a - b ≠ -k) {x₁ : ℝ} (hx₁ : 2 ≤ x₁)
    (hx₁a : 2 ≤ a.re + x₁) (hx₁b : b.re - a.re / 2 < x₁) :
    ∃ u : ℕ → ℝ, Summable u ∧ (∀ n, 0 ≤ u n) ∧ ∀ (n : ℕ) (c : ℂ),
      x₁ ≤ (1 - c).re → (1 - c).re ≤ x₁ + 1 →
        ‖s a b c n‖ ≤ ‖Gamma (1 - c)‖ * Real.exp (π * |c.im|) *
          Real.exp (π * (|c.im| + |a.im|) / 2) * u n := by
  obtain ⟨B, hB0, -, hBneg, hbound⟩ := exists_recip_Gamma_shift_bound x₁
  set coef := gaussHGCoeff a b (1 + a - b)
  set u : ℕ → ℝ := fun n => ‖coef n‖ * B (-(n : ℤ)) * (Real.Gamma (a.re + x₁ + n))⁻¹ with hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => mul_nonneg (mul_nonneg (norm_nonneg _) (hB0 _))
    (inv_nonneg.mpr (Real.Gamma_pos_of_pos (by positivity)).le)
  refine ⟨u, ?_, hu0, fun n c hc1 hc2 => ?_⟩
  · -- summability: `u_n = O(n^{2 Re b - 2} n^{1 - 2x₁ - Re a})`
    have hcoef := isBigO_gaussHGCoeff a b (1 + a - b) hb
    have hrat := isBigO_Gamma_ratio ((1 - x₁ : ℝ) : ℂ) 1 ((a.re + x₁ : ℝ) : ℂ) 1
    have hexp : (a + b - (1 + a - b) - 1).re +
        (((1 - x₁ : ℝ) : ℂ) + 1 - ((a.re + x₁ : ℝ) : ℂ) - 1).re < -1 := by
      simp; linarith
    refine summable_of_isBigO_nat (Real.summable_nat_rpow.mpr hexp) ?_
    have hbig := (hcoef.mul hrat).const_mul_left (π⁻¹ : ℂ)
    have hbig' := hbig.norm_left.trans (Asymptotics.IsBigO.of_bound 1 (by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [one_mul, ← Real.rpow_add hn0]) : (fun n : ℕ =>
        ((n : ℝ) ^ (a + b - (1 + a - b) - 1).re *
          (n : ℝ) ^ (((1 - x₁ : ℝ) : ℂ) + 1 - ((a.re + x₁ : ℝ) : ℂ) - 1).re)) =O[atTop] _)
    refine hbig'.congr' ?_ (Filter.EventuallyEq.rfl)
    · obtain ⟨K₁, hK₁⟩ := exists_nat_ge (x₁ + 2)
      filter_upwards [eventually_ge_atTop K₁] with n hn
      have hn' : x₁ + 2 ≤ n := le_trans hK₁ (by exact_mod_cast hn)
      have hn1 : ¬ (2 : ℝ) ≤ x₁ + ((-(n : ℤ) : ℤ) : ℝ) := by push_cast; linarith
      have hn2 : x₁ + 1 + ((-(n : ℤ) : ℤ) : ℝ) ≤ -1 := by push_cast; linarith
      have hBn : B (-(n : ℤ)) = Real.Gamma (1 - x₁ + n) / π := by
        rw [hBneg _ hn1 hn2]; push_cast; ring_nf
      have hg1 : ‖Gamma ((n : ℂ) + ((1 - x₁ : ℝ) : ℂ))‖ = Real.Gamma (1 - x₁ + n) := by
        rw [show (n : ℂ) + ((1 - x₁ : ℝ) : ℂ) = ((1 - x₁ + n : ℝ) : ℂ) by push_cast; ring,
          Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.Gamma_pos_of_pos (by linarith))]
      have hg2 : ‖(Gamma ((n : ℂ) + ((a.re + x₁ : ℝ) : ℂ)))⁻¹‖ =
          (Real.Gamma (a.re + x₁ + n))⁻¹ := by
        rw [show (n : ℂ) + ((a.re + x₁ : ℝ) : ℂ) = ((a.re + x₁ + n : ℝ) : ℂ) by push_cast; ring,
          Complex.Gamma_ofReal, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.Gamma_pos_of_pos (by positivity))]
      have hone : Gamma ((n : ℂ) + 1) * (Gamma ((n : ℂ) + 1))⁻¹ = 1 :=
        mul_inv_cancel₀ (by rw [Complex.Gamma_nat_eq_factorial]; exact_mod_cast n.factorial_ne_zero)
      simp only [hu, hBn, norm_mul, norm_inv, hg1, hg2, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      have hone' : ‖Gamma ((n : ℂ) + 1)‖ * ‖(Gamma ((n : ℂ) + 1))⁻¹‖ = 1 := by
        rw [← norm_mul, hone, norm_one]
      rw [norm_inv] at hone'
      linear_combination (π⁻¹ * ‖coef n‖ * Real.Gamma (1 - x₁ + n) *
        (Real.Gamma (a.re + x₁ + n))⁻¹) * hone'
  -- the pointwise bound
  have hre1 : 0 < (1 - c).re := by linarith
  have hG1 : Gamma (1 - c) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre1
  have hpoch := norm_poch_eq hG1 n
  have hB := hbound (-(n : ℤ)) (1 - c) hc1 hc2
  rw [show (1 - c) + ((-(n : ℤ) : ℤ) : ℂ) = 1 - c - n by push_cast; ring,
    show (1 - c).im = -c.im by simp, abs_neg] at hB
  set z : ℂ := 1 + a - c + n with hz
  have hzre : z.re = a.re + (1 - c).re + n := by simp [hz]; ring
  have hzre2 : (2 : ℝ) ≤ a.re + x₁ + n := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hzim : |z.im| ≤ |c.im| + |a.im| := by
    have : z.im = a.im - c.im := by simp [hz]
    rw [this]; have := abs_sub a.im c.im; linarith [abs_sub_comm a.im c.im]
  have hGz : ‖(Gamma z)⁻¹‖ ≤ Real.exp (π * (|c.im| + |a.im|) / 2) *
      (Real.Gamma (a.re + x₁ + n))⁻¹ := by
    refine (norm_recip_Gamma_le_of_half_le (by rw [hzre]; linarith)).trans ?_
    have hmono : Real.Gamma (a.re + x₁ + n) ≤ Real.Gamma z.re :=
      Real.Gamma_strictMonoOn_Ici.monotoneOn hzre2 (show (2 : ℝ) ≤ z.re by rw [hzre]; linarith)
        (by rw [hzre]; linarith)
    have hpos := Real.Gamma_pos_of_pos (show 0 < a.re + x₁ + n by linarith)
    calc Real.exp (π * |z.im| / 2) / Real.Gamma z.re
        ≤ Real.exp (π * (|c.im| + |a.im|) / 2) / Real.Gamma (a.re + x₁ + n) := by
          gcongr
      _ = _ := div_eq_mul_inv _ _
  calc ‖s a b c n‖ = ‖coef n‖ * ‖poch c n‖ * ‖(Gamma z)⁻¹‖ := by
        simp only [s, norm_mul, hz]; rfl
    _ ≤ ‖coef n‖ * (‖Gamma (1 - c)‖ * (Real.exp (π * |c.im|) * B (-(n : ℤ)))) *
          (Real.exp (π * (|c.im| + |a.im|) / 2) * (Real.Gamma (a.re + x₁ + n))⁻¹) := by
        rw [hpoch]
        have := hB0 (-(n : ℤ))
        gcongr
    _ = ‖Gamma (1 - c)‖ * Real.exp (π * |c.im|) * Real.exp (π * (|c.im| + |a.im|) / 2) * u n := by
        simp only [hu]; ring

/-- Holomorphy of the normalized Dixon series in a left half-plane. -/
theorem differentiableOn_Lh (hb : ∀ k : ℕ, 1 + a - b ≠ -k) {X : ℝ} (hX : 3 ≤ X)
    (hXa : 3 ≤ a.re + X) (hXb : b.re - a.re / 2 + 1 < X) :
    DifferentiableOn ℂ (Lh a b) {c : ℂ | X < (1 - c).re} := by
  intro c₀ hc₀
  simp only [Set.mem_ofPred_eq] at hc₀
  set r : ℝ := min (1 / 2) (((1 - c₀).re - X) / 2) with hr
  have hr0 : 0 < r := lt_min (by norm_num) (by linarith)
  have hr1 : r ≤ 1 / 2 := min_le_left _ _
  have hr2 : r ≤ ((1 - c₀).re - X) / 2 := min_le_right _ _
  set x₁ := (1 - c₀).re - r
  obtain ⟨u, hu, hu0, hbd⟩ := exists_bound (a := a) (b := b) hb (x₁ := x₁) (by linarith)
    (by linarith) (by linarith)
  have hball : DifferentiableOn ℂ (Lh a b) (Metric.ball c₀ r) := by
    refine differentiableOn_tsum_of_summable_norm
      (hu.mul_left (Real.Gamma (x₁ + 1) * Real.exp (π * (|c₀.im| + 1)) *
        Real.exp (π * ((|c₀.im| + 1) + |a.im|) / 2))) (fun n => ?_) Metric.isOpen_ball
      (fun n c hc => ?_)
    · have hpoly : Differentiable ℂ fun c : ℂ => poch c n :=
        (ascPochhammer ℂ n).differentiable
      exact (((hpoly.const_mul _).mul ((Complex.differentiable_one_div_Gamma).comp
        (by fun_prop))).differentiableOn)
    · have hdist : ‖c - c₀‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hc
      have hre : |c.re - c₀.re| < r :=
        lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (c - c₀)) hdist
      have him : |c.im - c₀.im| < r :=
        lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (c - c₀)) hdist
      have h1re : (1 - c).re = 1 - c.re := by simp
      have h1re0 : (1 - c₀).re = 1 - c₀.re := by simp
      have hc1 : x₁ ≤ (1 - c).re := by
        rw [h1re]; simp only [x₁, h1re0]; linarith [abs_lt.mp hre]
      have hc2 : (1 - c).re ≤ x₁ + 1 := by
        rw [h1re]; simp only [x₁, h1re0]; linarith [abs_lt.mp hre]
      refine (hbd n c hc1 hc2).trans ?_
      have hcim : |c.im| ≤ |c₀.im| + 1 := by
        have := abs_add_le c₀.im (c.im - c₀.im); simp at this
        linarith [abs_lt.mp him]
      have hG : ‖Gamma (1 - c)‖ ≤ Real.Gamma (x₁ + 1) := by
        have h := DLMF.Gamma.norm_Gamma_add_mul_I_le (x := (1 - c).re) (y := (1 - c).im)
          (by linarith)
        rw [show (((1 - c).re : ℝ) : ℂ) + I * (((1 - c).im : ℝ) : ℂ) = 1 - c by
          rw [mul_comm]; exact Complex.re_add_im _,
          abs_of_pos (Real.Gamma_pos_of_pos (by linarith))] at h
        exact h.trans (Real.Gamma_strictMonoOn_Ici.monotoneOn (show (2 : ℝ) ≤ (1 - c).re by
          linarith) (show (2 : ℝ) ≤ x₁ + 1 by linarith) hc2)
      have := hu0 n
      have hGx := (Real.Gamma_pos_of_pos (show 0 < x₁ + 1 by linarith)).le
      gcongr
  exact (hball.differentiableAt (Metric.ball_mem_nhds _ hr0)).differentiableWithinAt

/-- **Carlson's theorem in `c`**: `P(c) = K` on a left half-plane. -/
theorem exists_P_eq_K (ha : ∀ k : ℕ, 1 + a / 2 ≠ -k) (hb : ∀ k : ℕ, 1 + a - b ≠ -k) :
    ∃ X : ℝ, ∀ c : ℂ, c.re ≤ -X → P a b c = K a b := by
  obtain ⟨m₀, hm₀⟩ := exists_nat_ge (10 + 2 * |a.re| + 2 * |b.re|)
  have hm : (10 : ℝ) + 2 * |a.re| + 2 * |b.re| ≤ m₀ := hm₀
  have h1 := le_abs_self a.re
  have h2 := neg_abs_le a.re
  have h3 := le_abs_self b.re
  have h4 := neg_abs_le b.re
  have hreg : ∀ c : ℂ, c.re ≤ -(m₀ : ℝ) + 1 / 2 →
      0 < (1 + a / 2 - b - c).re ∧ 0 < (1 + a / 2 - c).re ∧ 0 < (1 + a - b - c).re := by
    intro c hc
    refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith
  have hnz : ∀ c : ℂ, c.re ≤ -(m₀ : ℝ) + 1 / 2 → 1 + a / 2 - c ≠ 0 ∧ 1 + a - b - c ≠ 0 := by
    intro c hc
    obtain ⟨-, h5, h6⟩ := hreg c hc
    exact ⟨fun h => by rw [h] at h5; simp at h5, fun h => by rw [h] at h6; simp at h6⟩
  set F : ℂ → ℂ := fun w => P a b (-(m₀ : ℂ) - w) - K a b with hF
  -- holomorphy
  have hLd := differentiableOn_Lh (a := a) (b := b) hb (X := m₀ + 1 / 2) (by linarith)
    (by linarith) (by linarith)
  have hFd : DifferentiableOn ℂ F {w : ℂ | -(1 / 2) < w.re} := by
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw
    have hc : (-(m₀ : ℂ) - w).re ≤ -(m₀ : ℝ) + 1 / 2 := by simp; linarith
    obtain ⟨-, h5, h6⟩ := hreg _ hc
    apply DifferentiableAt.differentiableWithinAt
    have hL : DifferentiableAt ℂ (fun w => Lh a b (-(m₀ : ℂ) - w)) w := by
      have hU : {c : ℂ | (m₀ : ℝ) + 1 / 2 < (1 - c).re} ∈ 𝓝 (-(m₀ : ℂ) - w) :=
        (isOpen_lt continuous_const (Complex.continuous_re.comp
          (continuous_const.sub continuous_id))).mem_nhds (by simp; linarith)
      exact (hLd.differentiableAt hU).comp w ((differentiableAt_const _).sub differentiableAt_id)
    have hG1 : DifferentiableAt ℂ (fun w => Gamma (1 + a / 2 - (-(m₀ : ℂ) - w))) w :=
      (Complex.differentiableAt_Gamma _ fun m hm => by
        rw [hm] at h5; simp at h5; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).comp w
        (by fun_prop)
    have hG2 : DifferentiableAt ℂ (fun w => Gamma (1 + a - b - (-(m₀ : ℂ) - w))) w :=
      (Complex.differentiableAt_Gamma _ fun m hm => by
        rw [hm] at h6; simp at h6; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).comp w
        (by fun_prop)
    have hG3 : DifferentiableAt ℂ (fun w => (Gamma (1 + a / 2 - b - (-(m₀ : ℂ) - w)))⁻¹) w :=
      (Complex.differentiable_one_div_Gamma _).comp w (by fun_prop)
    exact (((hL.mul hG1).mul hG2).mul hG3).sub_const _
  -- periodicity
  have hper : ∀ w : ℂ, 0 ≤ w.re → F (w + 1) = F w := by
    intro w hw
    set c : ℂ := -(m₀ : ℂ) - w with hcdef
    have hc : c.re ≤ -(m₀ : ℝ) + 1 / 2 := by simp [hcdef]; linarith
    have hc' : (c - 1).re ≤ -(m₀ : ℝ) + 1 / 2 := by simp [hcdef]; linarith
    obtain ⟨hcv, -, -⟩ := hreg c hc
    obtain ⟨hcv', -, -⟩ := hreg (c - 1) hc'
    obtain ⟨hs1, hH⟩ := summable_s_and_tendsto_H hb hcv
    obtain ⟨hs2, -⟩ := summable_s_and_tendsto_H hb hcv'
    obtain ⟨hn1, hn2⟩ := hnz c hc
    simp only [hF]
    rw [show -(m₀ : ℂ) - (w + 1) = c - 1 by rw [hcdef]; ring, P_sub_one hb hs1 hs2 hH hn1 hn2]
  -- the value at `0`: terminating Dixon
  have hF0 : F 0 = 0 := by
    simp only [hF, sub_zero]
    rw [P_neg_nat ha hb m₀, sub_self]
  -- the strip bound
  obtain ⟨u, hu, hu0, hbd⟩ := exists_bound (a := a) (b := b) hb (x₁ := 1 + m₀) (by linarith)
    (by linarith) (by linarith)
  set S := ∑' n : ℕ, u n with hS
  have hS0 : 0 ≤ S := tsum_nonneg hu0
  obtain ⟨C₁, K₁, hC₁, hb₁⟩ := exists_norm_Gamma_add_le_strip (1 + (m₀ : ℂ))
    (X₁ := 1 + m₀) (X₂ := 2 + m₀) (by linarith)
  obtain ⟨C₂, K₂, hC₂, hb₂⟩ := exists_norm_Gamma_add_le_strip (1 + a / 2 + m₀)
    (X₁ := 1 + a.re / 2 + m₀) (X₂ := 2 + a.re / 2 + m₀) (by linarith)
  obtain ⟨C₃, K₃, hC₃, hb₃⟩ := exists_norm_Gamma_add_le_strip (1 + a - b + m₀)
    (X₁ := 1 + a.re - b.re + m₀) (X₂ := 2 + a.re - b.re + m₀) (by linarith)
  obtain ⟨C₄, K₄, hC₄, hb₄⟩ := exists_norm_recip_Gamma_add_le_strip (1 + a / 2 - b + m₀)
    (|1 + a.re / 2 - b.re + m₀| + 1)
  set A : ℝ := C₁ * C₂ * C₃ * C₄ * S * Real.exp (π * |a.im| / 2) with hA
  have hstrip : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖F w‖ ≤ (A + ‖K a b‖) * (1 + |w.im|) ^ (K₁ + K₂ + K₃ + K₄) *
        Real.exp (π / 2 * |w.im|) := by
    intro w hw0 hw1
    set c : ℂ := -(m₀ : ℂ) - w with hcdef
    set y := w.im
    have hcim : |c.im| = |y| := by simp [hcdef, y]
    have e1 : 1 - c = w + (1 + (m₀ : ℂ)) := by rw [hcdef]; ring
    have e2 : 1 + a / 2 - c = w + (1 + a / 2 + m₀) := by rw [hcdef]; ring
    have e3 : 1 + a - b - c = w + (1 + a - b + m₀) := by rw [hcdef]; ring
    have e4 : 1 + a / 2 - b - c = w + (1 + a / 2 - b + m₀) := by rw [hcdef]; ring
    have hx1 : (1 + (m₀ : ℝ)) ≤ (1 - c).re := by rw [e1]; simp; linarith
    have hx2 : (1 - c).re ≤ 1 + m₀ + 1 := by rw [e1]; simp; linarith
    have hL : ‖Lh a b c‖ ≤ ‖Gamma (1 - c)‖ * Real.exp (π * |y|) *
        Real.exp (π * (|y| + |a.im|) / 2) * S := by
      rw [← hcim]
      exact tsum_of_norm_bounded (hu.hasSum.mul_left _) fun n => hbd n c hx1 hx2
    have g1 : ‖Gamma (1 - c)‖ ≤ C₁ * (1 + |y|) ^ K₁ * Real.exp (-(π * |y|) / 2) := by
      rw [e1]; exact hb₁ w (by simp; linarith) (by simp; linarith)
    have g2 : ‖Gamma (1 + a / 2 - c)‖ ≤ C₂ * (1 + |y|) ^ K₂ * Real.exp (-(π * |y|) / 2) := by
      rw [e2]; exact hb₂ w (by simp; linarith) (by simp; linarith)
    have g3 : ‖Gamma (1 + a - b - c)‖ ≤ C₃ * (1 + |y|) ^ K₃ * Real.exp (-(π * |y|) / 2) := by
      rw [e3]; exact hb₃ w (by simp; linarith) (by simp; linarith)
    have g4 : ‖(Gamma (1 + a / 2 - b - c))⁻¹‖ ≤ C₄ * (1 + |y|) ^ K₄ * Real.exp (π * |y| / 2) := by
      rw [e4]
      refine hb₄ w ?_
      rw [abs_le]
      have := le_abs_self (1 + a.re / 2 - b.re + m₀)
      have := neg_abs_le (1 + a.re / 2 - b.re + m₀)
      constructor <;> simp <;> linarith
    have hP : ‖P a b c‖ ≤ A * (1 + |y|) ^ (K₁ + K₂ + K₃ + K₄) * Real.exp (π / 2 * |y|) := by
      simp only [P, norm_mul]
      have hE : Real.exp (-(π * |y|) / 2) * Real.exp (π * |y|) * Real.exp (π * (|y| + |a.im|) / 2) *
          Real.exp (-(π * |y|) / 2) * Real.exp (-(π * |y|) / 2) * Real.exp (π * |y| / 2) =
          Real.exp (π / 2 * |y|) * Real.exp (π * |a.im| / 2) := by
        simp only [← Real.exp_add]; ring_nf
      calc ‖Lh a b c‖ * ‖Gamma (1 + a / 2 - c)‖ * ‖Gamma (1 + a - b - c)‖ *
            ‖(Gamma (1 + a / 2 - b - c))⁻¹‖
          ≤ ((C₁ * (1 + |y|) ^ K₁ * Real.exp (-(π * |y|) / 2)) * Real.exp (π * |y|) *
              Real.exp (π * (|y| + |a.im|) / 2) * S) *
              (C₂ * (1 + |y|) ^ K₂ * Real.exp (-(π * |y|) / 2)) *
              (C₃ * (1 + |y|) ^ K₃ * Real.exp (-(π * |y|) / 2)) *
              (C₄ * (1 + |y|) ^ K₄ * Real.exp (π * |y| / 2)) := by
            gcongr
            exact hL.trans (by gcongr)
        _ = C₁ * C₂ * C₃ * C₄ * S * ((1 + |y|) ^ K₁ * (1 + |y|) ^ K₂ * (1 + |y|) ^ K₃ *
              (1 + |y|) ^ K₄) * (Real.exp (-(π * |y|) / 2) * Real.exp (π * |y|) *
              Real.exp (π * (|y| + |a.im|) / 2) * Real.exp (-(π * |y|) / 2) *
              Real.exp (-(π * |y|) / 2) * Real.exp (π * |y| / 2)) := by ring
        _ = A * (1 + |y|) ^ (K₁ + K₂ + K₃ + K₄) * Real.exp (π / 2 * |y|) := by
            rw [hE, hA, pow_add, pow_add, pow_add]; ring
    have hpos : 1 ≤ (1 + |y|) ^ (K₁ + K₂ + K₃ + K₄) * Real.exp (π / 2 * |y|) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [abs_nonneg y]))
        (Real.one_le_exp (by positivity))
    calc ‖F w‖ ≤ ‖P a b c‖ + ‖K a b‖ := norm_sub_le _ _
      _ ≤ A * (1 + |y|) ^ (K₁ + K₂ + K₃ + K₄) * Real.exp (π / 2 * |y|) +
            ‖K a b‖ * ((1 + |y|) ^ (K₁ + K₂ + K₃ + K₄) * Real.exp (π / 2 * |y|)) := by
          gcongr
          exact le_mul_of_one_le_right (norm_nonneg _) hpos
      _ = (A + ‖K a b‖) * (1 + |y|) ^ (K₁ + K₂ + K₃ + K₄) * Real.exp (π / 2 * |y|) := by ring
  have hzero := eq_zero_of_periodic_of_bound (by norm_num : (0 : ℝ) < 1 / 2) hFd hper
    (σ := π / 2) (by linarith [Real.pi_pos]) hstrip hF0
  refine ⟨m₀, fun c hc => ?_⟩
  have h := hzero (-(m₀ : ℂ) - c) (by simp; linarith)
  simp only [hF, sub_eq_zero] at h
  simpa using h

/-- The normalized right-hand side of Dixon's formula. -/
def Rh (a b c : ℂ) : ℂ :=
  K a b * Gamma (1 + a / 2 - b - c) * (Gamma (1 + a / 2 - c))⁻¹ * (Gamma (1 + a - b - c))⁻¹

/-- The normalized right-hand side of Dixon's formula satisfies the same recurrence in `c` as the
  series. -/
theorem Rh_recurrence {c : ℂ} (hc : 1 + a / 2 - b - c ≠ 0) :
    (1 + a / 2 - b - c) * Rh a b c = (1 + a / 2 - c) * (1 + a - b - c) * Rh a b (c - 1) := by
  have g1 : Gamma (1 + a / 2 - b - (c - 1)) = (1 + a / 2 - b - c) * Gamma (1 + a / 2 - b - c) := by
    rw [show 1 + a / 2 - b - (c - 1) = (1 + a / 2 - b - c) + 1 by ring,
      Complex.Gamma_add_one _ hc]
  have g2 : (1 + a / 2 - c) * (Gamma (1 + a / 2 - (c - 1)))⁻¹ = (Gamma (1 + a / 2 - c))⁻¹ := by
    have h := mul_recip_Gamma_add_one (1 + a / 2 - c)
    rwa [show 1 + a / 2 - c + 1 = 1 + a / 2 - (c - 1) by ring] at h
  have g3 : (1 + a - b - c) * (Gamma (1 + a - b - (c - 1)))⁻¹ = (Gamma (1 + a - b - c))⁻¹ := by
    have h := mul_recip_Gamma_add_one (1 + a - b - c)
    rwa [show 1 + a - b - c + 1 = 1 + a - b - (c - 1) by ring] at h
  simp only [Rh]
  rw [g1, ← g2, ← g3]
  ring

end DixonAux

end CarlsonApplications

open DixonAux in
/-- Dixon's well-poised `₃F₂(1)` evaluation (AAR Theorem 3.4.1). -/
@[dlmf 16.4.E4]
theorem dixon_sum {a b c : ℂ}
    (h : 0 < (1 + a / 2 - b - c).re)
    (ha : ∀ k : ℕ, (1 + a / 2 : ℂ) ≠ -k)
    (hb : ∀ k : ℕ, (1 + a - b : ℂ) ≠ -k)
    (hc : ∀ k : ℕ, (1 + a - c : ℂ) ≠ -k) :
    (∑' n : ℕ, poch a n * poch b n * poch c n /
        (poch (1 + a - b) n * poch (1 + a - c) n *
          (n.factorial : ℂ))) =
      Gamma (1 + a / 2) * Gamma (1 + a - b) * Gamma (1 + a - c) *
        Gamma (1 + a / 2 - b - c) /
        (Gamma (1 + a) * Gamma (1 + a / 2 - b) * Gamma (1 + a / 2 - c) *
          Gamma (1 + a - b - c)) := by
  -- `Lh = Rh` on a left half-plane, by Carlson's theorem
  obtain ⟨X, hX⟩ := exists_P_eq_K ha hb
  have hfar : ∀ c' : ℂ, c'.re ≤ -(max X (|a.re| + |b.re| + 2)) → Lh a b c' = Rh a b c' := by
    intro c' hc'
    have hP := hX c' (by linarith [le_max_left X (|a.re| + |b.re| + 2)])
    have hm := le_max_right X (|a.re| + |b.re| + 2)
    have h1 := le_abs_self a.re
    have h2 := neg_abs_le a.re
    have h3 := le_abs_self b.re
    have h4 := neg_abs_le b.re
    have r1 : 0 < (1 + a / 2 - c').re := by simp; linarith
    have r2 : 0 < (1 + a - b - c').re := by simp; linarith
    have r3 : 0 < (1 + a / 2 - b - c').re := by simp; linarith
    have n1 := Complex.Gamma_ne_zero_of_re_pos r1
    have n2 := Complex.Gamma_ne_zero_of_re_pos r2
    have n3 := Complex.Gamma_ne_zero_of_re_pos r3
    simp only [P] at hP
    simp only [Rh]
    rw [← hP]
    have i1 := mul_inv_cancel₀ n1
    have i2 := mul_inv_cancel₀ n2
    have i3 := inv_mul_cancel₀ n3
    linear_combination (-(Lh a b c' * (Gamma (1 + a - b - c') * (Gamma (1 + a - b - c'))⁻¹) *
      ((Gamma (1 + a / 2 - b - c'))⁻¹ * Gamma (1 + a / 2 - b - c')))) * i1 +
      (-(Lh a b c' * ((Gamma (1 + a / 2 - b - c'))⁻¹ * Gamma (1 + a / 2 - b - c')))) * i2 +
      (-Lh a b c') * i3
  -- climb back to `c` with the recurrence
  set E : ℂ → ℂ := fun c' => Lh a b c' - Rh a b c' with hE
  obtain ⟨k₀, hk₀⟩ := exists_nat_ge (c.re + max X (|a.re| + |b.re| + 2))
  have hrec : ∀ c' : ℂ, 0 < (1 + a / 2 - b - c').re → E (c' - 1) = 0 → E c' = 0 := by
    intro c' hc' h0
    have hc'1 : 0 < (1 + a / 2 - b - (c' - 1)).re := by simp at hc' ⊢; linarith
    obtain ⟨hs1, hH⟩ := summable_s_and_tendsto_H hb hc'
    obtain ⟨hs2, -⟩ := summable_s_and_tendsto_H hb hc'1
    have hne : 1 + a / 2 - b - c' ≠ 0 := fun h => by rw [h] at hc'; simp at hc'
    have hL := recurrence hb hs1 hs2 hH
    have hR := Rh_recurrence (a := a) (b := b) hne
    have : (1 + a / 2 - b - c') * E c' = 0 := by
      simp only [hE] at h0 ⊢
      rw [mul_sub, hL, hR, ← mul_sub, h0, mul_zero]
    exact (mul_eq_zero.mp this).resolve_left hne
  have hclimb : ∀ i : ℕ, E (c - ((k₀ - i : ℕ) : ℂ)) = 0 := by
    intro i
    induction i with
    | zero =>
      simp only [hE, Nat.sub_zero, sub_eq_zero]
      exact hfar _ (by simp; linarith)
    | succ i ih =>
      rcases le_or_gt (i + 1) k₀ with hi | hi
      · have hk : (k₀ - i : ℕ) = (k₀ - (i + 1) : ℕ) + 1 := by omega
        rw [hk, Nat.cast_add, Nat.cast_one, ← sub_sub] at ih
        refine hrec _ ?_ ih
        have : (0 : ℝ) ≤ ((k₀ - (i + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
        have h' := h
        simp at h' ⊢
        linarith
      · rwa [show k₀ - (i + 1) = k₀ - i by omega]
  have hEc : E c = 0 := by simpa using hclimb k₀
  have hLR : Lh a b c = Rh a b c := sub_eq_zero.mp hEc
  -- back to the statement
  have hG : Gamma (1 + a - c) ≠ 0 := Complex.Gamma_ne_zero hc
  have hterm : ∀ n : ℕ, poch a n * poch b n * poch c n /
      (poch (1 + a - b) n * poch (1 + a - c) n * (n.factorial : ℂ)) =
      Gamma (1 + a - c) * s a b c n := by
    intro n
    have hp : poch (1 + a - c) n ≠ 0 := poch_ne_zero_of_not_neg_nat hc n
    have hpb : poch (1 + a - b) n ≠ 0 := poch_ne_zero_of_not_neg_nat hb n
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hGn : Gamma (1 + a - c + n) = Gamma (1 + a - c) * poch (1 + a - c) n := by
      have h := Complex.Gamma_add_nat_div_Gamma_eq (n := n) (1 + a - c) hc
      rw [div_eq_iff hG] at h
      rw [h, poch, mul_comm]
    simp only [s, gaussHGCoeff, hGn]
    field_simp
  simp_rw [hterm]
  rw [tsum_mul_left]
  change Gamma (1 + a - c) * Lh a b c = _
  rw [hLR]
  simp only [Rh, K, div_eq_mul_inv, mul_inv]
  ring

section Whipple

open Filter Finset DLMF.QSeries
open scoped Topology Nat

/-- The exponential difference quotient tends to its complex exponent. -/
private lemma whipple_exp_ratio (a : ℂ) :
    Tendsto (fun t : ℂ => (1-exp (a*t))/(1-exp t)) (𝓝[≠] 0) (𝓝 a) := by
  have h (a : ℂ) : Tendsto (fun t : ℂ => (exp (a*t)-1)/t) (𝓝[≠] 0) (𝓝 a) := by
    have hd : HasDerivAt (fun t : ℂ => exp (a*t)) a 0 := by
      convert ((hasDerivAt_id' (0:ℂ)).const_mul a).cexp using 1; simp
    simpa only [zero_add,mul_zero,exp_zero,smul_eq_mul,div_eq_mul_inv,mul_comm]
      using hd.tendsto_slope_zero
  have hh := (h a).div (h 1) (by norm_num : (1:ℂ) ≠ 0)
  simp only [one_mul,div_one] at hh
  refine hh.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ ht]
  rw [show 1-exp (a*t)=-(exp (a*t)-1) by ring,
    show 1-exp t=-(exp t-1) by ring,neg_div_neg_eq]

/-- The exponential base is different from one on a punctured neighborhood of zero. -/
private lemma whipple_exp_base_ne : ∀ᶠ t : ℂ in 𝓝[≠] 0, 1-exp t ≠ 0 := by
  have h : Tendsto (fun t : ℂ => (exp t-1)/t) (𝓝[≠] 0) (𝓝 (1:ℂ)) := by
    simpa only [zero_add,exp_zero,smul_eq_mul,div_eq_mul_inv,mul_comm]
      using (Complex.hasDerivAt_exp 0).tendsto_slope_zero
  filter_upwards [h.eventually_ne (by norm_num : (1:ℂ) ≠ 0)] with t ht
  intro he
  apply ht
  rw [sub_eq_zero.mp he,sub_self,zero_div]

/-- Finite q-Pochhammer symbols have the classical Pochhammer limit for complex exponents. -/
private lemma whipple_exp_qpoch (a : ℂ) (k : ℕ) :
    Tendsto (fun t : ℂ => qPochhammer (exp (a*t)) (exp t) k/(1-exp t)^k)
      (𝓝[≠] 0) (𝓝 (poch a k)) := by
  induction k with
  | zero => simp [qPochhammer_zero,poch_zero]
  | succ k ih =>
    have h := ih.mul (whipple_exp_ratio (a+k))
    rw [poch_succ]
    refine h.congr' ?_
    filter_upwards [whipple_exp_base_ne] with t ht
    rw [qPochhammer_succ,pow_succ]
    have he : exp (a*t)*exp t^k=exp ((a+k)*t) := by
      rw [←exp_nat_mul,←exp_add];congr 1;ring
    rw [he]
    field_simp

/-- The very-well-poised classical numerator after cancelling its half-parameter ratio. -/
private noncomputable def whippleUnit (a : ℂ) : ℕ → ℂ
  | 0 => 1
  | k+1 => poch (a+1) k*(a+2*(k+1))

/-- The cancelled very-well-poised factor has its classical limit. -/
private lemma whipple_unit_limit (a : ℂ) (k : ℕ) :
    Tendsto (fun t : ℂ => DLMF.Bailey.unitD (exp (a*t)) (exp t) k/(1-exp t)^k)
      (𝓝[≠] 0) (𝓝 (whippleUnit a k)) := by
  cases k with
  | zero => simp [DLMF.Bailey.unitD,whippleUnit]
  | succ k =>
    have h := (whipple_exp_qpoch (a+1) k).mul (whipple_exp_ratio (a+2*(k+1)))
    refine h.congr' ?_
    filter_upwards [whipple_exp_base_ne] with t ht
    rw [DLMF.Bailey.unitD]
    have he : exp (a*t)*exp t=exp ((a+1)*t) := by rw [←exp_add];congr 1;ring
    have he' : exp (a*t)*exp t^(2*(k+1))=exp ((a+2*(k+1))*t) := by
      rw [←exp_nat_mul,←exp_add];congr 1;push_cast;ring
    rw [he,he',pow_succ]
    field_simp


/-- The cancelled numerator equals the standard half-parameter Pochhammer ratio. -/
private lemma whippleUnit_eq (a : ℂ) (ha : ∀ j : ℕ, a/2 ≠ -j) (k : ℕ) :
    whippleUnit a k=poch a k*poch (a/2+1) k/poch (a/2) k := by
  cases k with
  | zero => simp [whippleUnit,poch_zero]
  | succ k =>
    have ha0 : a ≠ 0 := by intro h;simpa [h] using ha 0
    have hP := poch_ne_zero_of_not_neg_nat ha (k+1)
    have hs : (a/2)*poch (a/2+1) (k+1)=poch (a/2) (k+1)*(a/2+(k+1)) := by
      rw [←poch_succ_left,poch_succ]
      push_cast
      ring
    rw [whippleUnit,poch_succ_left a k]
    generalize poch (a/2+1) (k+1)=X at hs ⊢
    generalize poch (a/2) (k+1)=Y at hP hs ⊢
    field_simp
    linear_combination -2*poch (a+1) k*hs

/-- A finite product of normalized q-Pochhammer factors has its termwise limit. -/
private lemma whipple_qprod_limit (xs : List ℂ) (k : ℕ) :
    Tendsto (fun t : ℂ => (xs.map (fun a => qPochhammer (exp (a*t)) (exp t) k/(1-exp t)^k)).prod)
      (𝓝[≠] 0) (𝓝 ((xs.map (fun a => poch a k)).prod)) := by
  induction xs with
  | nil => simp
  | cons a xs ih => simpa only [List.map_cons,List.prod_cons] using (whipple_exp_qpoch a k).mul ih

/-- Collect the common normalization power in a finite q-Pochhammer product. -/
private lemma whipple_qprod_normalize (xs : List ℂ) (k : ℕ) (t : ℂ) :
    (xs.map (fun a => qPochhammer (exp (a*t)) (exp t) k/(1-exp t)^k)).prod =
      (xs.map (fun a => qPochhammer (exp (a*t)) (exp t) k)).prod/(1-exp t)^(xs.length*k) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,ih,Nat.add_mul,pow_add]
    rw [mul_comm ((1-exp t)^(xs.length*k)) ((1-exp t)^(1*k))]
    simp only [one_mul]
    ring

/-- Ratios with equally many finite q-Pochhammer factors have classical limits. -/
private lemma whipple_qratio_limit (xs ys : List ℂ) (hlen : xs.length=ys.length) (k : ℕ)
    (hy : ∀ a ∈ ys, poch a k ≠ 0) :
    Tendsto (fun t : ℂ => (xs.map (fun a => qPochhammer (exp (a*t)) (exp t) k)).prod /
      (ys.map (fun a => qPochhammer (exp (a*t)) (exp t) k)).prod)
      (𝓝[≠] 0) (𝓝 ((xs.map (fun a => poch a k)).prod/(ys.map (fun a => poch a k)).prod)) := by
  have hY : (ys.map (fun a => poch a k)).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hx
    obtain ⟨a,ha,h0⟩ := List.mem_map.mp hx
    exact hy a ha h0
  have h := (whipple_qprod_limit xs k).div (whipple_qprod_limit ys k) hY
  refine h.congr' ?_
  filter_upwards [whipple_exp_base_ne] with t ht
  simp only [Pi.div_apply,whipple_qprod_normalize,hlen]
  exact div_div_div_cancel_right₀ (pow_ne_zero _ ht) _ _

/-- Include the cancelled very-well-poised factor in the finite product limit. -/
private lemma whipple_unit_ratio_limit (a : ℂ) (xs ys : List ℂ) (hlen : xs.length+1=ys.length) (k : ℕ)
    (hy : ∀ b ∈ ys, poch b k ≠ 0) :
    Tendsto (fun t : ℂ => DLMF.Bailey.unitD (exp (a*t)) (exp t) k *
      (xs.map (fun b => qPochhammer (exp (b*t)) (exp t) k)).prod /
      (ys.map (fun b => qPochhammer (exp (b*t)) (exp t) k)).prod)
      (𝓝[≠] 0) (𝓝 (whippleUnit a k*(xs.map (fun b => poch b k)).prod/
        (ys.map (fun b => poch b k)).prod)) := by
  have hY : (ys.map (fun b => poch b k)).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hx
    obtain ⟨b,hb,h0⟩ := List.mem_map.mp hx
    exact hy b hb h0
  have h := ((whipple_unit_limit a k).mul (whipple_qprod_limit xs k)).div
    (whipple_qprod_limit ys k) hY
  refine h.congr' ?_
  filter_upwards [whipple_exp_base_ne] with t ht
  simp only [Pi.div_apply,whipple_qprod_normalize,←hlen,Nat.add_mul,pow_add,one_mul]
  field_simp


/-- The shifted denominator parameter in exponential coordinates. -/
private lemma whipple_exp_param (a b t : ℂ) :
    exp (a*t)*exp t/exp (b*t)=exp ((a-b+1)*t) := by
  rw [←exp_add,←exp_sub];congr 1;ring

/-- A negative integer base power in exponential coordinates. -/
private lemma whipple_exp_neg_pow (t : ℂ) (n : ℕ) : (exp t)⁻¹^n=exp (-(n:ℂ)*t) := by
  rw [←exp_neg,←exp_nat_mul];congr 1;ring

/-- The terminating denominator parameter in exponential coordinates. -/
private lemma whipple_exp_nparam (a t : ℂ) (n : ℕ) :
    exp (a*t)*exp t*exp t^n=exp ((a+n+1)*t) := by
  rw [←exp_nat_mul,←exp_add,←exp_add];congr 1;ring

/-- The balanced denominator parameter in exponential coordinates. -/
private lemma whipple_exp_yparam (a d e t : ℂ) (n : ℕ) :
    exp (d*t)*exp (e*t)*(exp t)⁻¹^n/exp (a*t)=exp ((d+e-a-n)*t) := by
  rw [whipple_exp_neg_pow,←exp_add,←exp_add,←exp_sub];congr 1;ring

/-- The transformed numerator parameter in exponential coordinates. -/
private lemma whipple_exp_xparam (a b c t : ℂ) :
    exp (a*t)*exp t/(exp (b*t)*exp (c*t))=exp ((a-b-c+1)*t) := by
  rw [←exp_add,←exp_add,←exp_sub];congr 1;ring

/-- Every exponential parameter tends to one with the base. -/
private lemma whipple_exp_tendsto (a : ℂ) : Tendsto (fun t : ℂ => exp (a*t)) (𝓝[≠] 0) (𝓝 1) := by
  have h : ContinuousAt (fun t : ℂ => exp (a*t)) 0 := by fun_prop
  simpa using h.tendsto.mono_left nhdsWithin_le_nhds

/-- The finite Watson summand tends to the very-well-poised classical summand. -/
private lemma whipple_watson8_limit (a b c d e : ℂ) (n k : ℕ)
    (hden : ∀ p ∈ [a-b+1,a-c+1,a-d+1,a-e+1,a+n+1,1], ∀ j : ℕ, p ≠ -j) :
    Tendsto (fun t : ℂ => DLMF.Bailey.watsonR8 (exp (a*t)) (exp (b*t))
      (exp (c*t)) (exp (d*t)) (exp (e*t)) (exp t) n k) (𝓝[≠] 0)
      (𝓝 (whippleUnit a k*poch b k*poch c k*poch d k*poch e k*poch (-(n:ℂ)) k/
        (poch (a-b+1) k*poch (a-c+1) k*poch (a-d+1) k*poch (a-e+1) k*
          poch (a+n+1) k*poch 1 k))) := by
  have hscale := (((((whipple_exp_tendsto a).pow 2).mul
    ((whipple_exp_tendsto 1).pow 2)).mul ((whipple_exp_tendsto 1).pow n)).div
    ((((whipple_exp_tendsto b).mul (whipple_exp_tendsto c)).mul
      (whipple_exp_tendsto d)).mul (whipple_exp_tendsto e)) (by norm_num)).pow k
  simp only [one_mul,one_pow,one_div,inv_one] at hscale
  have h := (whipple_unit_ratio_limit a [b,c,d,e,-(n:ℂ)]
    [a-b+1,a-c+1,a-d+1,a-e+1,a+n+1,1] rfl k
    (fun p hp => poch_ne_zero_of_not_neg_nat (hden p hp) k)).mul hscale
  convert h using 1
  · funext t
    simp only [Pi.div_apply,neg_mul,DLMF.Bailey.watsonR8,List.map_cons,List.map_nil,List.prod_cons,
      List.prod_nil,mul_one,one_mul,whipple_exp_neg_pow,whipple_exp_param,whipple_exp_nparam]
    ring
  · simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    ring

/-- The transformed Watson summand tends to its classical terminating summand. -/
private lemma whipple_watson4_limit (a b c d e : ℂ) (n k : ℕ)
    (hden : ∀ p ∈ [a-b+1,a-c+1,d+e-a-n,1], ∀ j : ℕ, p ≠ -j) :
    Tendsto (fun t : ℂ => DLMF.Bailey.watsonR4 (exp (a*t)) (exp (b*t))
      (exp (c*t)) (exp (d*t)) (exp (e*t)) (exp t) n k) (𝓝[≠] 0)
      (𝓝 (poch (a-b-c+1) k*poch d k*poch e k*poch (-(n:ℂ)) k/
        (poch (a-b+1) k*poch (a-c+1) k*poch (d+e-a-n) k*poch 1 k))) := by
  have h := (whipple_qratio_limit [-(n:ℂ),d,e,a-b-c+1]
    [a-b+1,a-c+1,d+e-a-n,1] rfl k
    (fun p hp => poch_ne_zero_of_not_neg_nat (hden p hp) k)).mul
      ((whipple_exp_tendsto 1).pow k)
  convert h using 1
  · funext t
    simp only [DLMF.Bailey.watsonR4]
    rw [whipple_exp_yparam]
    simp only [neg_mul,List.map_cons,List.map_nil,List.prod_cons,
      List.prod_nil,mul_one,one_mul,whipple_exp_neg_pow,whipple_exp_param,whipple_exp_xparam]
    ring
  · simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,one_pow]
    ring


/-- The shifted numerator parameter in exponential coordinates. -/
private lemma whipple_exp_oneparam (a t : ℂ) : exp (a*t)*exp t=exp ((a+1)*t) := by
  rw [←exp_add];congr 1;ring

/-- A nonzero classical Pochhammer limit ensures nonzero nearby q-Pochhammer factors. -/
private lemma whipple_qpoch_eventually_ne (a : ℂ) (k : ℕ) (ha : poch a k ≠ 0) :
    ∀ᶠ t : ℂ in 𝓝[≠] 0,qPochhammer (exp (a*t)) (exp t) k ≠ 0 := by
  filter_upwards [(whipple_exp_qpoch a k).eventually_ne ha] with t ht
  intro h0
  apply ht
  rw [h0,zero_div]

/-- Whipple's terminating very well-poised `₇F₆(1)` transformation into a balanced
`₄F₃(1)`, AAR Theorem 3.4.4 and the terminating case of DLMF 16.4.15.
The proof takes the complex-parameter exponential-base limit of the proved rational
Watson transformation `DLMF.Bailey.watsonR`. -/
@[dlmf 16.4.E15]
theorem whipple_7F6 {a b c d e : ℂ} (m : ℕ)
    (hden : ∀ z ∈ [a / 2, a - b + 1, a - c + 1, a - d + 1,
      a - e + 1, a + m + 1, d + e - a - m], ∀ k : ℕ, z ≠ -k) :
    (∑ n ∈ Finset.range (m + 1),
      poch a n * poch (a / 2 + 1) n * poch b n * poch c n * poch d n * poch e n *
        poch (-m : ℂ) n /
        (poch (a / 2) n * poch (a - b + 1) n * poch (a - c + 1) n *
          poch (a - d + 1) n * poch (a - e + 1) n * poch (a + m + 1) n * n.factorial)) =
      poch (a + 1) m * poch (a - d - e + 1) m /
        (poch (a - d + 1) m * poch (a - e + 1) m) *
      (∑ n ∈ Finset.range (m + 1),
        poch (a - b - c + 1) n * poch d n * poch e n * poch (-m : ℂ) n /
          (poch (a - b + 1) n * poch (a - c + 1) n *
            poch (d + e - a - m) n * n.factorial)) := by
  have hA := hden (a/2) (by simp)
  have hB := hden (a-b+1) (by simp)
  have hC := hden (a-c+1) (by simp)
  have hD := hden (a-d+1) (by simp)
  have hE := hden (a-e+1) (by simp)
  have hN := hden (a+m+1) (by simp)
  have hY := hden (d+e-a-m) (by simp)
  have h1 : ∀ j : ℕ,(1:ℂ) ≠ -j := not_neg_nat_of_re_pos (by norm_num)
  have hden8 : ∀ p ∈ [a-b+1,a-c+1,a-d+1,a-e+1,a+m+1,1], ∀ j : ℕ,p ≠ -j := by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hden4 : ∀ p ∈ [a-b+1,a-c+1,d+e-a-m,1], ∀ j : ℕ,p ≠ -j := by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption
  have hL := tendsto_finsetSum (Finset.range (m+1)) fun k _ =>
    whipple_watson8_limit a b c d e m k hden8
  have hPref0 := whipple_qratio_limit [a+1,a-d-e+1] [a-d+1,a-e+1] rfl m (by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact poch_ne_zero_of_not_neg_nat hD m
    · exact poch_ne_zero_of_not_neg_nat hE m)
  have hPref : Tendsto (fun t : ℂ =>
      qPochhammer (exp (a*t)*exp t) (exp t) m*
        qPochhammer (exp (a*t)*exp t/(exp (d*t)*exp (e*t))) (exp t) m/
      (qPochhammer (exp (a*t)*exp t/exp (d*t)) (exp t) m*
        qPochhammer (exp (a*t)*exp t/exp (e*t)) (exp t) m)) (𝓝[≠] 0)
      (𝓝 (poch (a+1) m*poch (a-d-e+1) m/(poch (a-d+1) m*poch (a-e+1) m))) := by
    convert hPref0 using 1
    · funext t
      rw [whipple_exp_xparam,whipple_exp_param,whipple_exp_param,whipple_exp_oneparam]
      simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    · simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  have hR := hPref.mul (tendsto_finsetSum (Finset.range (m+1)) fun k _ =>
    whipple_watson4_limit a b c d e m k hden4)
  have hQB := whipple_qpoch_eventually_ne (a-b+1) m (poch_ne_zero_of_not_neg_nat hB m)
  have hQC := whipple_qpoch_eventually_ne (a-c+1) m (poch_ne_zero_of_not_neg_nat hC m)
  have hQD := whipple_qpoch_eventually_ne (a-d+1) m (poch_ne_zero_of_not_neg_nat hD m)
  have hQE := whipple_qpoch_eventually_ne (a-e+1) m (poch_ne_zero_of_not_neg_nat hE m)
  have hQN := whipple_qpoch_eventually_ne (a+m+1) m (poch_ne_zero_of_not_neg_nat hN m)
  have hQY := whipple_qpoch_eventually_ne (d+e-a-m) m (poch_ne_zero_of_not_neg_nat hY m)
  have hQQ : ∀ᶠ t : ℂ in 𝓝[≠] 0,∀ k ∈ Finset.range (m+1),
      qPochhammer (exp t) (exp t) k ≠ 0 := by
    refine (Filter.eventually_all_finset _).mpr fun k _ => ?_
    simpa only [one_mul] using
      whipple_qpoch_eventually_ne 1 k (poch_ne_zero_of_not_neg_nat h1 k)
  have heq : (fun t : ℂ => ∑ k ∈ Finset.range (m+1),DLMF.Bailey.watsonR8
      (exp (a*t)) (exp (b*t)) (exp (c*t)) (exp (d*t)) (exp (e*t)) (exp t) m k) =ᶠ[𝓝[≠] 0]
      (fun t : ℂ =>
      qPochhammer (exp (a*t)*exp t) (exp t) m*
        qPochhammer (exp (a*t)*exp t/(exp (d*t)*exp (e*t))) (exp t) m/
      (qPochhammer (exp (a*t)*exp t/exp (d*t)) (exp t) m*
        qPochhammer (exp (a*t)*exp t/exp (e*t)) (exp t) m)*
      ∑ k ∈ Finset.range (m+1),DLMF.Bailey.watsonR4
        (exp (a*t)) (exp (b*t)) (exp (c*t)) (exp (d*t)) (exp (e*t)) (exp t) m k) := by
    filter_upwards [hQB,hQC,hQD,hQE,hQN,hQY,hQQ] with t hB hC hD hE hN hY hQ
    refine DLMF.Bailey.watsonR m (exp_ne_zero _) (exp_ne_zero _) (exp_ne_zero _)
      (exp_ne_zero _) (exp_ne_zero _) (exp_ne_zero _) (fun k hk => hQ k (by simpa using hk))
      ?_ ?_ ?_ ?_ ?_ ?_
    · simpa only [whipple_exp_param] using hB
    · simpa only [whipple_exp_param] using hC
    · simpa only [whipple_exp_param] using hD
    · simpa only [whipple_exp_param] using hE
    · simpa only [whipple_exp_yparam] using hY
    · simpa only [whipple_exp_nparam] using hN
  have h := tendsto_nhds_unique hL (hR.congr' heq.symm)
  simp only [poch_nat_one] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [whippleUnit_eq a hA]
  ring


end Whipple

open DougallAux in
/-- Dougall's bilateral `₂H₂` sum, in Gamma form (AAR Theorem 2.8.2). -/
@[dlmf 15.4.E25, dlmf 16.4.E17]
theorem dougall_bilateral {a b c d : ℂ}
    (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k)
    (hconv : 1 + (a + b).re < (c + d).re) :
    (∑' n : ℤ, Gamma (a + n) * Gamma (b + n) /
      (Gamma (c + n) * Gamma (d + n))) =
      π ^ 2 * Gamma (c + d - a - b - 1) /
        (sin (π * a) * sin (π * b) * Gamma (c - a) * Gamma (d - a) *
          Gamma (c - b) * Gamma (d - b)) := by
  change ∑' n : ℤ, term a b c d n = _
  by_cases hc : ∀ k : ℤ, c ≠ k
  · exact tsum_eq_of_not_int ha hb hc hconv
  by_cases hd : ∀ k : ℤ, d ≠ k
  · rw [← rhs_comm]
    simp_rw [term_comm a b c d]
    exact tsum_eq_of_not_int ha hb hd (by rwa [add_comm d c])
  push Not at hc hd
  obtain ⟨j, rfl⟩ := hc
  obtain ⟨m, rfl⟩ := hd
  rcases le_total m j with hjm | hjm
  · exact tsum_at_int_int ha hb hjm hconv
  · rw [← rhs_comm]
    simp_rw [term_comm a b (j : ℂ) (m : ℂ)]
    exact tsum_at_int_int ha hb hjm (by rwa [add_comm (m : ℂ) (j : ℂ)])

/-- The complete elliptic integral of the first kind as the hypergeometric series of AAR §3.2,
in the modulus `k`: `K = (π/2) ₂F₁(1/2, 1/2; 1; k²)`, meaningful for `‖k‖ < 1`. The real integral
form in the parameter `m = k²` is `DLMF.Elliptic.Real.compEllIntKm`. -/
@[dlmf 19.5.E1]
def compEllIntKkSeries (k : ℂ) : ℂ :=
  (π / 2) * ₂F₁ (1 / 2 : ℂ) (1 / 2) 1 (k ^ 2)

/-- The reciprocal square root of the square of a positive real number. -/
theorem cpow_sq_neg_half {x : ℝ} (hx : 0 < x) :
    ((x : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) = (x : ℂ)⁻¹ := by
  have hh : ((x : ℂ) ^ 2) ^ (1 / 2 : ℂ) = (x : ℂ) := by
    rw [← ofReal_pow, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← ofReal_cpow (sq_nonneg x), ← Real.sqrt_eq_rpow, Real.sqrt_sq hx.le]
  rw [cpow_neg, hh]

/-- The substitution `t = sin² θ` for the beta weight with parameters `1/2, 1/2`. -/
theorem integral_beta_half_weight (f : ℝ → ℂ) :
    (∫ t : ℝ in (0 : ℝ)..1,
      (t : ℂ) ^ (-(1 / 2 : ℂ)) * (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ)) * f t) =
      2 * ∫ θ : ℝ in (0 : ℝ)..(π / 2), f (Real.sin θ ^ 2) := by
  let g : ℝ → ℂ := fun t =>
    (t : ℂ) ^ (-(1 / 2 : ℂ)) * (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ)) * f t
  have hd (θ : ℝ) : HasDerivAt (fun u : ℝ => Real.sin u ^ 2)
      (2 * Real.sin θ * Real.cos θ) θ := by
    convert! (Real.hasDerivAt_sin θ).pow 2 using 1
    simp
  have hnonneg {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
      0 ≤ 2 * Real.sin θ * Real.cos θ := by
    have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a := (0 : ℝ)) (b := π / 2) (g := g)
    (show ContinuousOn (fun θ : ℝ => Real.sin θ ^ 2) (Set.uIcc 0 (π / 2)) by fun_prop)
    (fun θ _ => hd θ) (fun θ hθ => hnonneg (by
      simpa [min_eq_left Real.pi_div_two_pos.le, max_eq_right Real.pi_div_two_pos.le] using hθ))
  simp only [Real.sin_zero, zero_pow (by decide : 2 ≠ 0), Real.sin_pi_div_two,
    one_pow] at hsub
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le Real.pi_div_two_pos.le
  intro θ hθ
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hsq : 1 - (Real.sin θ : ℂ) ^ 2 = (Real.cos θ : ℂ) ^ 2 := by
    exact_mod_cast (by nlinarith [Real.sin_sq_add_cos_sq θ] :
      1 - Real.sin θ ^ 2 = Real.cos θ ^ 2)
  simp only [Function.comp_apply, g, real_smul, ofReal_mul, ofReal_ofNat, ofReal_pow]
  rw [hsq, cpow_sq_neg_half hs, cpow_sq_neg_half hc]
  field_simp [ofReal_ne_zero.mpr hs.ne', ofReal_ne_zero.mpr hc.ne']
  apply (div_eq_iff (mul_ne_zero (ofReal_ne_zero.mpr hs.ne')
    (ofReal_ne_zero.mpr hc.ne'))).2
  ring

/-- AAR §3.2: `K(k) = (π/2) ₂F₁(1/2,1/2;1;k²)` is the definition above; the equivalent
integral `∫_0^{π/2} (1-k² sin²θ)^{-1/2} dθ` follows by `t = sin² θ` in Euler's integral. -/
@[dlmf 19.2.E4]
theorem compEllIntKkSeries_eq_integral {k : ℝ} (hk : |k| < 1) :
    compEllIntKkSeries k =
      ∫ θ : ℝ in (0 : ℝ)..(π / 2), (1 - (k : ℂ) ^ 2 * sin θ ^ 2) ^ (-(1 / 2 : ℂ)) := by
  have hhalf : (0 : ℝ) < (1 / 2 : ℂ).re := by norm_num
  have hsub : (1 : ℂ) - 1 / 2 = 1 / 2 := by ring
  have hz : ‖(k : ℂ) ^ 2‖ < 1 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact pow_lt_one₀ (abs_nonneg k) hk (by decide)
  have hgamma : Gamma (1 / 2 : ℂ) * Gamma (1 / 2) = (π : ℂ) := by
    have h := Gamma_mul_Gamma_one_sub (1 / 2)
    rw [hsub, show (π : ℂ) * (1 / 2) = π / 2 by ring, sin_pi_div_two, div_one] at h
    exact h
  unfold compEllIntKkSeries
  rw [ordinaryHypergeometric_eq_integral hhalf (by rwa [hsub]) hz,
    hsub, Gamma_one, hgamma]
  have hexp : (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) := by ring
  simp only [hexp]
  rw [integral_beta_half_weight]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hi : (∫ θ : ℝ in (0 : ℝ)..(π / 2),
      (1 - (k : ℂ) ^ 2 * ((Real.sin θ ^ 2 : ℝ) : ℂ)) ^ (-(1 / 2 : ℂ))) =
      ∫ θ : ℝ in (0 : ℝ)..(π / 2),
        (1 - (k : ℂ) ^ 2 * sin θ ^ 2) ^ (-(1 / 2 : ℂ)) := by
    simp only [ofReal_pow, ofReal_sin]
  rw [hi]
  field [hpi]

end DLMF.Hypergeometric
