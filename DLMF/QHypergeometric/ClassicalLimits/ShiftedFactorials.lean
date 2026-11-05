/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic.SeriesProperties
public import DLMF.Hypergeometric.Basic.Pochhammer
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Classical limits of finite q-shifted factorials

The normalized finite q-shifted factorial tends to the ordinary rising factorial as the
positive real base approaches one from below. Uniform estimates for its individual factors
control the simultaneous limit in which the factor index tends to infinity.
-/

@[expose] public noncomputable section

open Complex Filter Finset Set
open scoped Real Topology

namespace DLMF.QHypergeometric

open DLMF.QSeries

/-- The normalized principal-power increment tends to its exponent as the real base approaches one.
-/
lemma tendsto_cpow_increment (a : ℂ) :
    Tendsto (fun q : ℝ => (1 - (q : ℂ) ^ a) / (1 - (q : ℂ))) (𝓝[<] 1) (𝓝 a) := by
  have hd : HasDerivAt (fun z : ℂ => z ^ a) a 1 := by
    simpa using (hasDerivAt_id (1 : ℂ)).cpow_const (by simp : (1 : ℂ) ∈ slitPlane)
  have hq : Tendsto (fun q : ℝ => (q : ℂ)) (𝓝[<] 1) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with q (hq : q < 1)
      simpa using (show (q : ℂ) ≠ 1 by exact_mod_cast hq.ne)
  have h := hd.tendsto_slope.comp hq
  simp only [Function.comp_def, slope_def_field, Complex.one_cpow] at h
  convert h using 1
  ext q
  rw [show 1 - (q : ℂ) ^ a = -((q : ℂ) ^ a - 1) by ring,
    show 1 - (q : ℂ) = -((q : ℂ) - 1) by ring, neg_div_neg_eq]

/-- A normalized finite q-Pochhammer symbol tends to the ordinary rising factorial. -/
lemma tendsto_qPochhammer_normalized (a : ℂ) (n : ℕ) :
    Tendsto (fun q : ℝ => qPochhammer ((q : ℂ) ^ a) q n / (1 - (q : ℂ)) ^ n)
      (𝓝[<] 1) (𝓝 (DLMF.Hypergeometric.pochhammer a n)) := by
  induction n with
  | zero =>
    simp only [qPochhammer_zero, pow_zero, div_one, DLMF.Hypergeometric.pochhammer_zero]
    exact tendsto_const_nhds
  | succ n ih =>
    have h := ih.mul (tendsto_cpow_increment (a + n))
    rw [DLMF.Hypergeometric.pochhammer_succ]
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with q hq
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.1.ne'
    rw [qPochhammer_succ, pow_succ, ← Complex.cpow_natCast q n,
      ← Complex.cpow_add _ _ hq0, mul_div_mul_comm]


namespace ClassicalLimit

/-- The signs in the phase and classical argument scaling cancel for every integer exponent. -/
lemma scaling_phase (q z : ℂ) (n : ℕ) (e : ℤ) :
    (((-1 : ℂ) ^ n * q ^ DLMF.QSeries.TripleProduct.tri (n : ℤ)) ^ e) *
        (((q - 1) ^ e * z) ^ n) =
      q ^ (DLMF.QSeries.TripleProduct.tri (n : ℤ) * e) *
        (1 - q) ^ ((n : ℤ) * e) * z ^ n := by
  have he : ((q - 1) ^ e) ^ n = ((q - 1) ^ n) ^ e := by
    simp only [← zpow_natCast, ← zpow_mul, mul_comm]
  have hs : (-1 : ℂ) ^ n * (q - 1) ^ n = (1 - q) ^ n := by
    rw [← mul_pow]
    congr 1
    ring
  rw [mul_pow, ← mul_assoc, he, ← mul_zpow]
  rw [show ((-1 : ℂ) ^ n * q ^ DLMF.QSeries.TripleProduct.tri (n : ℤ)) * (q - 1) ^ n =
    q ^ DLMF.QSeries.TripleProduct.tri (n : ℤ) * (1 - q) ^ n by rw [mul_right_comm, hs]; ring]
  rw [mul_zpow, ← zpow_mul, ← zpow_natCast (1 - q) n, ← zpow_mul]


/-- A single shifted-factorial factor normalized by the corresponding q-factorial factor. -/
def normalizedFactor (a : ℂ) (q : ℝ) (n : ℕ) : ℂ :=
  (1 - (q : ℂ) ^ a * (q : ℂ) ^ n) / (1 - (q : ℂ) ^ (n + 1))

/-- The normalized factors differ from one by a uniformly bounded multiple of `1 / (n + 1)`.
-/
lemma norm_normalizedFactor_sub_one_le (a : ℂ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (n : ℕ) :
    ‖normalizedFactor a q n - 1‖ ≤
      ‖(1 - (q : ℂ) ^ a) / (1 - (q : ℂ)) - 1‖ / ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hp : q ^ (n + 1) < 1 := pow_lt_one₀ hq0 hq1 (by omega)
  have hqC : 1 - (q : ℂ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hq1.ne')
  have hpC : 1 - (q : ℂ) ^ (n + 1) ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr hp.ne')
  have heq : normalizedFactor a q n - 1 =
      ((1 - (q : ℂ) ^ a) / (1 - (q : ℂ)) - 1) *
        ((q : ℂ) ^ n * (1 - (q : ℂ)) / (1 - (q : ℂ) ^ (n + 1))) := by
    dsimp [normalizedFactor]
    field_simp [hqC, hpC]
    simp only [pow_succ]
    ring
  have hsum : ((n : ℝ) + 1) * q ^ n ≤ ∑ j ∈ range (n + 1), q ^ j := by
    calc
      ((n : ℝ) + 1) * q ^ n = ∑ _j ∈ range (n + 1), q ^ n := by simp
      _ ≤ ∑ j ∈ range (n + 1), q ^ j := by
        apply sum_le_sum
        intro j hj
        exact pow_le_pow_of_le_one hq0 hq1.le (by simpa using mem_range.mp hj)
  have hbound : q ^ n * (1 - q) / (1 - q ^ (n + 1)) ≤ 1 / ((n : ℝ) + 1) := by
    rw [div_le_div_iff₀ (sub_pos.mpr hp) hn]
    have hh := mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr hq1.le)
    rw [geom_sum_mul_neg] at hh
    nlinarith
  rw [heq, norm_mul]
  have hnorm : ‖(q : ℂ) ^ n * (1 - (q : ℂ)) / (1 - (q : ℂ) ^ (n + 1))‖ =
      q ^ n * (1 - q) / (1 - q ^ (n + 1)) := by
    rw [show (q : ℂ) ^ n * (1 - (q : ℂ)) / (1 - (q : ℂ) ^ (n + 1)) =
      ((q ^ n * (1 - q) / (1 - q ^ (n + 1)) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hnorm]
  simpa only [div_eq_mul_inv, one_mul] using
    mul_le_mul_of_nonneg_left hbound
      (norm_nonneg ((1 - (q : ℂ) ^ a) / (1 - (q : ℂ)) - 1))

/-- Normalized shifted-factorial factors tend uniformly to one when the base tends to one
and the factor index tends to infinity. -/
lemma tendsto_normalizedFactor (a : ℂ) :
    Tendsto (fun p : ℝ × ℕ => normalizedFactor a p.1 p.2)
      ((𝓝[<] 1) ×ˢ atTop) (𝓝 1) := by
  have hC := ((tendsto_cpow_increment a).sub_const 1).norm
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ q : ℝ in 𝓝[<] 1, ‖(1 - (q : ℂ) ^ a) / (1 - (q : ℂ)) - 1‖ ≤ C := by
    refine ⟨‖a - 1‖ + 1, by positivity, ?_⟩
    exact (hC.eventually_lt_const (by linarith : ‖a - 1‖ < ‖a - 1‖ + 1)).mono fun _ h => h.le
  have hb : ∀ᶠ p : ℝ × ℕ in (𝓝[<] 1) ×ˢ atTop,
      ‖normalizedFactor a p.1 p.2 - 1‖ ≤ C * (1 / ((p.2 : ℝ) + 1)) := by
    filter_upwards [tendsto_fst.eventually hC,
      tendsto_fst.eventually (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))] with p hp hq
    exact (norm_normalizedFactor_sub_one_le a hq.1.le hq.2 p.2).trans
      (by simpa only [div_eq_mul_inv, one_mul] using
        div_le_div_of_nonneg_right hp (by positivity : 0 ≤ (p.2 : ℝ) + 1))
  have hzero : Tendsto (fun p : ℝ × ℕ => C * (1 / ((p.2 : ℝ) + 1)))
      ((𝓝[<] 1) ×ˢ atTop) (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_snd : Tendsto Prod.snd ((𝓝[<] (1 : ℝ)) ×ˢ atTop) atTop) |>.const_mul C
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hb hzero)

/-- A regular classical lower parameter remains off the q-lattice for every index when the
positive real base is sufficiently close to one. -/
lemma eventually_cpow_mul_pow_ne_one (c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    ∀ᶠ q : ℝ in 𝓝[<] 1, ∀ n : ℕ, (q : ℂ) ^ c * (q : ℂ) ^ n ≠ 1 := by
  obtain ⟨P, hP, Q, hQ, hPQ⟩ :=
    eventually_prod_iff.mp ((tendsto_normalizedFactor c).eventually_ne one_ne_zero)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hQ
  have hprefix := (tendsto_qPochhammer_normalized c N).eventually_ne
    (DLMF.Hypergeometric.pochhammer_ne_zero_of_not_neg_nat hc N)
  filter_upwards [hP, hprefix] with q hq hprefix
  intro n hn
  by_cases hsmall : n < N
  · have hprod : qPochhammer ((q : ℂ) ^ c) q N = 0 := by
      rw [qPochhammer_eq_prod]
      exact prod_eq_zero (mem_range.mpr hsmall) (by rw [hn, sub_self])
    exact hprefix (by rw [hprod, zero_div])
  · have hfactor := hPQ hq (hN n (Nat.le_of_not_gt hsmall))
    exact hfactor (by simp only [normalizedFactor, hn, sub_self, zero_div])

/-- A finite list of regular classical lower parameters remains q-regular near the classical
limit. -/
lemma eventually_qDenominatorRegular_cpow (b : List ℂ)
    (hb : ∀ c ∈ b, ∀ n : ℕ, c ≠ -(n : ℂ)) :
    ∀ᶠ q : ℝ in 𝓝[<] 1, QDenominatorRegular (b.map fun c => (q : ℂ) ^ c) q := by
  induction b with
  | nil => simp [QDenominatorRegular]
  | cons c b ih =>
    filter_upwards [eventually_cpow_mul_pow_ne_one c (hb c (by simp)),
      ih (fun x hx => hb x (by simp [hx]))] with q hc hb
    intro x hx
    simp only [List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hc
    · exact hb x hx

end ClassicalLimit

end DLMF.QHypergeometric
