/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.ModulusPhase.ReciprocalExpansions

/-!
# Asymptotic expansions of Airy phases

Integration of the reciprocal-modulus expansions gives the Airy phase expansions with their
additive constants fixed.

Source references and common attribution are retained in
`DLMF.Airy.ModulusPhase`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent

open scoped Real Topology

namespace DLMF.Airy

/-! ### The phase expansions 9.8.22 and 9.8.23 -/
/-- If `u → 1`, `u sin θ - sin β → 0`, `u cos θ - cos β → 0` and `θ - β → L`, then
`cos L = 1`. -/
theorem airyMod_cos_eq_one_of_limits {u θ β : ℝ → ℝ} {L : ℝ} (hu : Tendsto u atTop (𝓝 1))
    (hs : Tendsto (fun s => u s * Real.sin (θ s) - Real.sin (β s)) atTop (𝓝 0))
    (hc : Tendsto (fun s => u s * Real.cos (θ s) - Real.cos (β s)) atTop (𝓝 0))
    (hL : Tendsto (fun s => θ s - β s) atTop (𝓝 L)) : Real.cos L = 1 := by
  have key : ∀ s, u s * Real.cos (θ s - β s) = 1 +
      (u s * Real.cos (θ s) - Real.cos (β s)) * Real.cos (β s) +
      (u s * Real.sin (θ s) - Real.sin (β s)) * Real.sin (β s) := fun s => by
    rw [Real.cos_sub]; linear_combination Real.sin_sq_add_cos_sq (β s)
  have t1 : Tendsto (fun s => (u s * Real.cos (θ s) - Real.cos (β s)) * Real.cos (β s))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun s => ?_) (by simpa using hc.norm)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (by simpa using Real.abs_cos_le_one _)
  have t2 : Tendsto (fun s => (u s * Real.sin (θ s) - Real.sin (β s)) * Real.sin (β s))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun s => ?_) (by simpa using hs.norm)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (by simpa using Real.abs_sin_le_one _)
  have h1 : Tendsto (fun s => u s * Real.cos (θ s - β s)) atTop (𝓝 1) := by
    simp only [key]; simpa using (tendsto_const_nhds.add t1).add t2
  have h2 : Tendsto (fun s => u s * Real.cos (θ s - β s)) atTop (𝓝 (1 * Real.cos L)) :=
    hu.mul ((Real.continuous_cos.tendsto L).comp hL)
  have := tendsto_nhds_unique h2 h1
  linarith

/-- A real `x` with `cos x = 1` and `|x| < 2π` is `0`. -/
theorem airyMod_eq_zero_of_cos_eq_one {x : ℝ} (h : Real.cos x = 1) (hx : |x| < 2 * π) : x = 0 := by
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff x).mp h
  have hπ := Real.pi_pos
  rw [← hn] at hx ⊢
  have h1 : |(n : ℝ)| < 1 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hx
    nlinarith
  have h2 : |n| < 1 := by exact_mod_cast h1
  have : n = 0 := by have := abs_lt.mp h2; omega
  simp [this]

/-- Bounds for the limit `L` of `E` from derivative bounds `a ≤ E' ≤ b` on `(0,1)` and
`|E'(s)| ≤ K s^{-5/2}` on `[1,∞)`. -/
theorem airyMod_limit_bounds {E e : ℝ → ℝ} {L a b K : ℝ} (hc : ContinuousOn E (Ici 0))
    (hd : ∀ s, 0 < s → HasDerivAt E (e s) s) (hab : ∀ s, 0 < s → s < 1 → a ≤ e s ∧ e s ≤ b)
    (hK : ∀ s, 1 ≤ s → |e s| ≤ K * s ^ (-(5 / 2) : ℝ)) (hL : Tendsto E atTop (𝓝 L)) :
    E 0 + a - 2 / 3 * K ≤ L ∧ L ≤ E 0 + b + 2 / 3 * K := by
  have hc' : ContinuousOn E (Icc 0 1) := hc.mono Icc_subset_Ici_self
  have mono : ∀ {g g' : ℝ → ℝ}, ContinuousOn g (Icc 0 1) → (∀ s, 0 < s → s < 1 → HasDerivAt g (g' s) s) →
      (∀ s, 0 < s → s < 1 → 0 ≤ g' s) → g 0 ≤ g 1 := by
    intro g g' hgc hg hg'
    have hm : MonotoneOn g (Icc 0 1) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := g') (convex_Icc 0 1) hgc
        (fun s hs => ?_) (fun s hs => ?_)
      · rw [interior_Icc] at hs; exact (hg s hs.1 hs.2).hasDerivWithinAt
      · rw [interior_Icc] at hs; exact hg' s hs.1 hs.2
    exact hm ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  have m1 := mono (g := fun s => E s - a * s) (g' := fun s => e s - a)
    (hc'.sub (continuousOn_const.mul continuousOn_id))
    (fun s hs _ => by convert (hd s hs).sub ((hasDerivAt_id s).const_mul a) using 1 <;> first | rfl | ring)
    (fun s hs hs1 => by linarith [(hab s hs hs1).1])
  have m2 := mono (g := fun s => b * s - E s) (g' := fun s => b - e s)
    ((continuousOn_const.mul continuousOn_id).sub hc')
    (fun s hs _ => by convert ((hasDerivAt_id s).const_mul b).sub (hd s hs) using 1 <;> first | rfl | ring)
    (fun s hs hs1 => by linarith [(hab s hs hs1).2])
  simp only [mul_zero, sub_zero, mul_one, zero_sub] at m1 m2
  obtain ⟨L', hL', hb⟩ := airyMod_tendsto_of_deriv_bound (F := E) (f := e) (R := 1) (K := K)
    (p := -(3 / 2)) one_pos (by norm_num) (fun s hs => hd s (by linarith))
    (fun s hs => by rw [show (-(3 / 2) : ℝ) - 1 = -(5 / 2) by norm_num]; exact hK s hs)
  have hLL := tendsto_nhds_unique hL' hL
  subst hLL
  have h1 := hb 1 le_rfl
  rw [Real.one_rpow, mul_one] at h1
  rw [abs_le] at h1
  constructor <;> linarith [h1.1, h1.2]

/-- `(-s)^{-3k} = (-(s³)⁻¹)^k`. -/
theorem airyMod_neg_zpow (s : ℝ) (k : ℕ) : (-s) ^ (-(3 * k : ℤ)) = (-(s ^ 3)⁻¹) ^ k := by
  rw [show (-(3 * k : ℤ)) = -((3 * k : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    pow_mul, ← inv_pow, neg_pow s 3, show (-1 : ℝ) ^ 3 = -1 by norm_num, neg_one_mul, inv_neg]

/-- The first coefficients of the expansion of `M²`. -/
theorem airyMod_coeff_values : airyModulusCoeff 0 = 1 ∧ airyModulusCoeff 1 = 5 / 32 ∧
    0 < airyModulusCoeff 2 := by
  refine ⟨by simp [airyModulusCoeff], by norm_num [airyModulusCoeff, Finset.prod_range_succ], ?_⟩
  unfold airyModulusCoeff
  refine div_pos (Finset.prod_pos fun j _ => by positivity) (by positivity)

/-- Two-sided bounds for `π s^{1/2} M(-s)²`: `1 - 5/(32 s³) ≤ π s^{1/2} M(-s)² < 1`. -/
theorem airyMod_modulus_bounds {s : ℝ} (hs : 0 < s) :
    1 - 5 / 32 * (s ^ 3)⁻¹ ≤ π * s ^ (1 / 2 : ℝ) * airyModulus (-s) ^ 2 ∧
      π * s ^ (1 / 2 : ℝ) * airyModulus (-s) ^ 2 < 1 := by
  have hπ := Real.pi_pos
  obtain ⟨c0, c1, c2⟩ := airyMod_coeff_values
  have hq : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  have hqi : s ^ (-1 / 2 : ℝ) = (s ^ (1 / 2 : ℝ))⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hs.le]
  constructor
  · have h := (airyModulus_error (x := -s) (by linarith) (N := 2) (by norm_num)).2
    rw [neg_neg] at h
    simp only [airyModulusSum, Finset.sum_range_succ, Finset.sum_range_zero, ite_false,
      Bool.false_eq_true, airyMod_neg_zpow, c0, c1, hqi] at h
    have hw : 0 < (s ^ 3)⁻¹ := by positivity
    have hpos : 0 < (s ^ (1 / 2 : ℝ))⁻¹ / π * airyModulusCoeff 2 * (-(s ^ 3)⁻¹) ^ 2 := by
      have : 0 < (-(s ^ 3)⁻¹) ^ 2 := by rw [neg_sq]; positivity
      positivity
    have h' := (mul_nonneg_iff_of_pos_right hpos).mp h
    simp only [pow_zero, pow_one, mul_one, zero_add] at h'
    have : (s ^ (1 / 2 : ℝ))⁻¹ / π * (1 + 5 / 32 * -(s ^ 3)⁻¹) ≤ airyModulus (-s) ^ 2 := by
      linarith
    have e : π * s ^ (1 / 2 : ℝ) * ((s ^ (1 / 2 : ℝ))⁻¹ / π * (1 + 5 / 32 * -(s ^ 3)⁻¹)) =
        1 - 5 / 32 * (s ^ 3)⁻¹ := by field_simp; ring
    rw [← e]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  · have := airyMod_sqrt_mul_sq_lt hs
    calc π * s ^ (1 / 2 : ℝ) * airyModulus (-s) ^ 2 = π * (s ^ (1 / 2 : ℝ) * airyModulus (-s) ^ 2) := by ring
      _ < π * (1 / π) := by gcongr
      _ = 1 := by field_simp

/-- If `f = O(s^b)` and `a + b < 0`, then `c s^a f(s) → 0`. -/
theorem airyMod_tendsto_rpow_mul {f : ℝ → ℝ} {a b : ℝ} (c : ℝ) (hab : a + b < 0)
    (hf : f =O[atTop] (fun s => s ^ b)) : Tendsto (fun s => c * s ^ a * f s) atTop (𝓝 0) := by
  refine ((isBigO_refl (fun s => c * s ^ a) atTop).mul hf).trans_tendsto ?_
  have h := (tendsto_rpow_neg_atTop (y := -(a + b)) (by linarith)).const_mul c
  rw [mul_zero, neg_neg] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  rw [Real.rpow_add hs]; ring

/-- `Ai(-s) = π^{-1/2} s^{-1/4} cos(ζ - π/4) + O(s^{-7/4})`, real form. -/
theorem airyMod_aiReal_neg_sub :
    (fun s : ℝ => airyAiReal (-s) - s ^ (-(1 / 4) : ℝ) / Real.sqrt π * Real.cos (airyZeta s - π / 4))
      =O[atTop] (fun s : ℝ => s ^ (-(7 / 4) : ℝ)) := by
  refine (airyMod_ai_neg_sub.norm_left.congr_left fun s => ?_).of_norm_left
  rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring, airyAi_ofReal_eq, ← ofReal_sub,
    norm_real]

/-- `Bi(-s) = -π^{-1/2} s^{-1/4} sin(ζ - π/4) + O(s^{-7/4})`, real form. -/
theorem airyMod_biReal_neg_sub :
    (fun s : ℝ => airyBiReal (-s) + s ^ (-(1 / 4) : ℝ) / Real.sqrt π * Real.sin (airyZeta s - π / 4))
      =O[atTop] (fun s : ℝ => s ^ (-(7 / 4) : ℝ)) := by
  refine (airyMod_bi_neg_sub.norm_left.congr_left fun s => ?_).of_norm_left
  rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring, airyBi_ofReal_eq, ← ofReal_add,
    norm_real]

/-- `√(π s^{1/2} M²) = √π s^{1/4} M` for `s > 0`. -/
theorem airyMod_sqrt_eq {s m : ℝ} (hs : 0 < s) (hm : 0 ≤ m) (a : ℝ) :
    Real.sqrt (π * s ^ a * m ^ 2) = Real.sqrt π * s ^ (a / 2) * m := by
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hm,
    Real.sqrt_eq_rpow (s ^ a), ← Real.rpow_mul hs.le]
  ring_nf

/-- The phase `θ(-s)` has derivative `1/(π M(-s)²)`. -/
theorem airyMod_phase_hasDerivAt (s : ℝ) :
    HasDerivAt (fun s => airyPhase (-s)) (1 / (π * airyModulus (-s) ^ 2)) s := by
  convert (hasDerivAt_airyPhase (-s)).comp s (hasDerivAt_neg s) using 1 <;> first | rfl | ring

/-- Reciprocal expansion of `1/(π M(-s)²)` as `s → ∞`. -/
theorem airyMod_phase_integrand (N : ℕ) :
    (fun s => 1 / (π * airyModulus (-s) ^ 2) - ∑ k ∈ Finset.range N,
      s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * airyReciprocalCoeff airyModulusCoeff k) =O[atTop]
      (fun s => s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * N : ℤ))) := by
  refine airyMod_integrand_expansion (F := fun x => airyModulus x ^ 2)
    (p := fun x => (-x) ^ (-1 / 2 : ℝ) / π) airyModulus_asymptotic
    (fun x hx => div_ne_zero (Real.rpow_pos_of_pos (by linarith) _).ne' Real.pi_ne_zero)
    airyMod_coeff_values.1 (fun s hs => ?_) N
  have hM := (airyModulus_pos (-s)).ne'
  have hq : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  simp only [neg_neg]
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hs.le]
  field_simp

/-- The phase expansion at `+∞` in the variable `s = -x`, with an undetermined constant. -/
theorem airyMod_phase_expansion_s : ∃ L, Tendsto (fun s => airyPhase (-s) - 2 / 3 * s ^ (3 / 2 : ℝ))
      atTop (𝓝 L) ∧
    ∀ N : ℕ, (fun s => airyPhase (-s) - L - ∑ k ∈ Finset.range N,
      2 / 3 * s ^ (3 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * airyPhaseCoeff k) =O[atTop]
      (fun s => 2 / 3 * s ^ (3 / 2 : ℝ) * (-s) ^ (-(3 * N : ℤ))) := by
  obtain ⟨L, hL, hN⟩ := airyMod_expansion_of_deriv (fun s _ => airyMod_phase_hasDerivAt s)
    airyMod_phase_integrand
  refine ⟨L, by simpa [airyReciprocalCoeff] using hL, fun N => ?_⟩
  simpa [airyPhaseCoeff] using hN N

/-- Explicit bounds on the constant `L` of the phase expansion. -/
private lemma airyMod_phase_limit_bounds {L : ℝ}
    (hL : Tendsto (fun s => airyPhase (-s) - 2 / 3 * s ^ (3 / 2 : ℝ)) atTop (𝓝 L)) :
    π / 6 + 0 - 2 / 3 * (5 / 27) ≤ L ∧ L ≤ π / 6 + 32 / 27 + 2 / 3 * (5 / 27) := by
  have hπ := Real.pi_pos
  have h := airyMod_limit_bounds (E := fun s => airyPhase (-s) - 2 / 3 * s ^ (3 / 2 : ℝ))
    (e := fun s => 1 / (π * airyModulus (-s) ^ 2) - s ^ (1 / 2 : ℝ)) (a := 0) (b := 32 / 27)
    (K := 5 / 27)
    (((airyPhase_continuous.comp continuous_neg).sub
      (continuous_const.mul (Real.continuous_rpow_const (by norm_num)))).continuousOn)
    (fun s hs => by
      convert (airyMod_phase_hasDerivAt s).sub
        ((Real.hasDerivAt_rpow_const (p := 3 / 2) (Or.inl hs.ne')).const_mul (2 / 3)) using 1
      norm_num; ring_nf)
    (fun s hs hs1 => by
      obtain ⟨h1, h2⟩ := airyMod_modulus_bounds hs
      obtain ⟨h3, _⟩ := airyMod_modulus_bounds one_pos
      have hm := airyMod_sq_strictMono (show -1 < -s by linarith)
      simp only [Real.one_rpow, mul_one, one_pow, inv_one] at h3
      have hA := airyModulus_pos (-s)
      have hq : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
      have hA2 : 0 < π * airyModulus (-s) ^ 2 := by positivity
      constructor
      · rw [sub_nonneg, le_div_iff₀ hA2]; nlinarith
      · have : 27 / 32 ≤ π * airyModulus (-s) ^ 2 := by nlinarith
        have : 1 / (π * airyModulus (-s) ^ 2) ≤ 32 / 27 := by
          rw [div_le_iff₀ hA2]; linarith
        linarith)
    (fun s hs => by
      have hs0 : 0 < s := by linarith
      obtain ⟨h1, h2⟩ := airyMod_modulus_bounds hs0
      set q := s ^ (1 / 2 : ℝ)
      set w := (s ^ 3)⁻¹
      set y := π * q * airyModulus (-s) ^ 2
      have hq : 0 < q := Real.rpow_pos_of_pos hs0 _
      have hw : 0 < w := by positivity
      have hw1 : w ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hs)
      have hy : 27 / 32 ≤ y := by nlinarith
      have he : 1 / (π * airyModulus (-s) ^ 2) = q / y := by
        simp only [y]; field_simp
      have hp : s ^ (-(5 / 2) : ℝ) = q * w := by
        rw [show (-(5 / 2) : ℝ) = 1 / 2 + (-3 : ℝ) by norm_num, Real.rpow_add hs0,
          Real.rpow_neg hs0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [he, hp]
      have hy0 : 0 < y := by linarith
      have hnn : 0 ≤ q / y - q := by
        rw [sub_nonneg, le_div_iff₀ hy0]; nlinarith
      rw [abs_of_nonneg hnn, div_sub' hy0.ne', div_le_iff₀ hy0]
      nlinarith [mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℝ) ≤ 5 * q * w)])
    hL
  simpa [airyPhase_zero, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)] using h
-- the oscillatory asymptotics fix `L - π/4 ∈ 2πℤ`

/-- The oscillatory asymptotics of `Ai`, `Bi` force `cos (L - π/4) = 1`. -/
private lemma airyMod_phase_limit_cos {L : ℝ}
    (hL : Tendsto (fun s => airyPhase (-s) - 2 / 3 * s ^ (3 / 2 : ℝ)) atTop (𝓝 L)) :
    Real.cos (L - π / 4) = 1 := by
  have hπ := Real.pi_pos
  set y : ℝ → ℝ := fun s => π * s ^ (1 / 2 : ℝ) * airyModulus (-s) ^ 2
  have hy : Tendsto y atTop (𝓝 1) := by
    have hw : Tendsto (fun s : ℝ => 1 - 5 / 32 * (s ^ 3)⁻¹) atTop (𝓝 1) := by
      have := ((tendsto_pow_atTop (α := ℝ) (by norm_num : (3 : ℕ) ≠ 0)).inv_tendsto_atTop).const_mul
        (5 / 32 : ℝ)
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hw tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with s hs using (airyMod_modulus_bounds hs).1
    · filter_upwards [eventually_gt_atTop 0] with s hs using (airyMod_modulus_bounds hs).2.le
  have hu : Tendsto (fun s => Real.sqrt (y s)) atTop (𝓝 1) := by
    have := (Real.continuous_sqrt.tendsto 1).comp hy
    rw [Real.sqrt_one] at this
    exact this
  refine airyMod_cos_eq_one_of_limits (u := fun s => Real.sqrt (y s))
    (θ := fun s => airyPhase (-s)) (β := fun s => airyZeta s - π / 4 + π / 2) hu ?_ ?_ ?_
  · refine (airyMod_tendsto_rpow_mul (Real.sqrt π) (a := 1 / 4) (by norm_num)
      airyMod_aiReal_neg_sub).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    simp only [y]
    rw [airyMod_sqrt_eq hs (airyModulus_pos _).le, Real.sin_add_pi_div_two,
      airyAiReal_eq_modulus_sin (-s)]
    have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
    have h4 : s ^ (1 / 4 : ℝ) * s ^ (-(1 / 4) : ℝ) = 1 := by
      rw [← Real.rpow_add hs]; norm_num
    field_simp
    norm_num
    linear_combination (-Real.cos ((4 * airyZeta s - π) / 4)) * h4
  · refine (airyMod_tendsto_rpow_mul (Real.sqrt π) (a := 1 / 4) (by norm_num)
      airyMod_biReal_neg_sub).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    simp only [y]
    rw [airyMod_sqrt_eq hs (airyModulus_pos _).le, Real.cos_add_pi_div_two,
      airyBiReal_eq_modulus_cos (-s)]
    have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
    have h4 : s ^ (1 / 4 : ℝ) * s ^ (-(1 / 4) : ℝ) = 1 := by
      rw [← Real.rpow_add hs]; norm_num
    field_simp
    norm_num
    linear_combination (Real.sin ((4 * airyZeta s - π) / 4)) * h4
  · refine (hL.sub_const (π / 4)).congr fun s => ?_
    simp only [airyZeta]; ring

/-- The constant in the phase expansion is `π/4`. -/
theorem airyMod_phase_limit {L : ℝ}
    (hL : Tendsto (fun s => airyPhase (-s) - 2 / 3 * s ^ (3 / 2 : ℝ)) atTop (𝓝 L)) :
    L = π / 4 := by
  have hπ := Real.pi_pos
  have hb := airyMod_phase_limit_bounds hL
  have := airyMod_eq_zero_of_cos_eq_one (airyMod_phase_limit_cos hL) (by
    rw [abs_lt]; constructor <;> nlinarith [Real.pi_gt_three])
  linarith

/-- The first coefficients of the expansion of `N²`. -/
theorem airyMod_derivCoeff_values : airyDerivModulusCoeff 0 = 1 ∧ airyDerivModulusCoeff 1 = -(7 / 32) ∧
    airyDerivModulusCoeff 2 < 0 := by
  obtain ⟨c0, c1, c2⟩ := airyMod_coeff_values
  refine ⟨by simp [airyDerivModulusCoeff, c0], by rw [airyDerivModulusCoeff, c1]; norm_num, ?_⟩
  rw [airyDerivModulusCoeff]
  push_cast
  have : (1 - 6 * (2 : ℝ)) < 0 := by norm_num
  exact div_neg_of_pos_of_neg (by positivity) this

/-- Two-sided bounds for `π s^{-1/2} N(-s)²`: `1 ≤ π s^{-1/2} N(-s)² ≤ 1 + 7/(32 s³)`. -/
theorem airyMod_derivModulus_bounds {s : ℝ} (hs : 0 < s) :
    1 ≤ π * s ^ (-(1 / 2) : ℝ) * airyDerivModulus (-s) ^ 2 ∧
      π * s ^ (-(1 / 2) : ℝ) * airyDerivModulus (-s) ^ 2 ≤ 1 + 7 / 32 * (s ^ 3)⁻¹ := by
  have hπ := Real.pi_pos
  obtain ⟨c0, c1, c2⟩ := airyMod_derivCoeff_values
  have hq : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  have hqi : s ^ (-(1 / 2) : ℝ) = (s ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg hs.le _
  have hw : 0 < (s ^ 3)⁻¹ := by positivity
  rw [hqi]
  constructor
  · have h := (airyDerivModulus_error (x := -s) (by linarith) (N := 1) le_rfl).2
    rw [neg_neg] at h
    simp only [airyModulusSum, Finset.sum_range_succ, Finset.sum_range_zero, ite_true,
      airyMod_neg_zpow, c0, c1] at h
    have hpos : 0 < s ^ (1 / 2 : ℝ) / π * -(7 / 32) * (-(s ^ 3)⁻¹) ^ 1 := by
      rw [pow_one]; nlinarith [div_pos hq hπ]
    have h' := (mul_nonneg_iff_of_pos_right hpos).mp h
    simp only [pow_zero, mul_one, zero_add] at h'
    have : s ^ (1 / 2 : ℝ) / π ≤ airyDerivModulus (-s) ^ 2 := by linarith
    calc (1 : ℝ) = π * (s ^ (1 / 2 : ℝ))⁻¹ * (s ^ (1 / 2 : ℝ) / π) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
  · have h := (airyDerivModulus_error (x := -s) (by linarith) (N := 2) (by norm_num)).2
    rw [neg_neg] at h
    simp only [airyModulusSum, Finset.sum_range_succ, Finset.sum_range_zero, ite_true,
      airyMod_neg_zpow, c0, c1] at h
    have hneg : s ^ (1 / 2 : ℝ) / π * airyDerivModulusCoeff 2 * (-(s ^ 3)⁻¹) ^ 2 < 0 := by
      have : 0 < (-(s ^ 3)⁻¹) ^ 2 := by rw [neg_sq]; positivity
      have h3 : s ^ (1 / 2 : ℝ) / π * airyDerivModulusCoeff 2 < 0 :=
        mul_neg_of_pos_of_neg (div_pos hq hπ) c2
      exact mul_neg_of_neg_of_pos h3 this
    have h' : airyDerivModulus (-s) ^ 2 - s ^ (1 / 2 : ℝ) / π *
        (0 + 1 * (-(s ^ 3)⁻¹) ^ 0 + -(7 / 32) * (-(s ^ 3)⁻¹) ^ 1) ≤ 0 := by
      by_contra hc
      push Not at hc
      nlinarith
    simp only [pow_zero, pow_one, mul_one, zero_add] at h'
    have : airyDerivModulus (-s) ^ 2 ≤ s ^ (1 / 2 : ℝ) / π * (1 + 7 / 32 * (s ^ 3)⁻¹) := by
      linarith
    calc π * (s ^ (1 / 2 : ℝ))⁻¹ * airyDerivModulus (-s) ^ 2
        ≤ π * (s ^ (1 / 2 : ℝ))⁻¹ * (s ^ (1 / 2 : ℝ) / π * (1 + 7 / 32 * (s ^ 3)⁻¹)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by field_simp

/-- `Ai'(-s) = π^{-1/2} s^{1/4} sin(ζ - π/4) + O(s^{-5/4})`, real form. -/
theorem airyMod_aiDerivReal_neg_sub :
    (fun s : ℝ => airyAiDerivReal (-s) - s ^ (1 / 4 : ℝ) / Real.sqrt π * Real.sin (airyZeta s - π / 4))
      =O[atTop] (fun s : ℝ => s ^ (-(5 / 4) : ℝ)) := by
  refine (airyInt_aiDeriv_neg_sub.norm_left.congr_left fun s => ?_).of_norm_left
  rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring, airyAiDeriv_ofReal_eq, ← ofReal_sub,
    norm_real]

/-- `Bi'(-s) = π^{-1/2} s^{1/4} cos(ζ - π/4) + O(s^{-5/4})`, real form. -/
theorem airyMod_biDerivReal_neg_sub :
    (fun s : ℝ => airyBiDerivReal (-s) - s ^ (1 / 4 : ℝ) / Real.sqrt π * Real.cos (airyZeta s - π / 4))
      =O[atTop] (fun s : ℝ => s ^ (-(5 / 4) : ℝ)) := by
  refine (airyInt_biDeriv_neg_sub.norm_left.congr_left fun s => ?_).of_norm_left
  rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring, airyBiDeriv_ofReal_eq, ← ofReal_sub,
    norm_real]

/-- The derivative phase `φ(-s)` has derivative `s/(π N(-s)²)`. -/
theorem airyMod_derivPhase_hasDerivAt (s : ℝ) :
    HasDerivAt (fun s => airyDerivPhase (-s)) (s / (π * airyDerivModulus (-s) ^ 2)) s := by
  convert (hasDerivAt_airyDerivPhase (-s)).comp s (hasDerivAt_neg s) using 1 <;>
    first | rfl | ring

/-- Reciprocal expansion of `s/(π N(-s)²)` as `s → ∞`. -/
theorem airyMod_derivPhase_integrand (N : ℕ) :
    (fun s => s / (π * airyDerivModulus (-s) ^ 2) - ∑ k ∈ Finset.range N,
      s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * airyReciprocalCoeff airyDerivModulusCoeff k)
      =O[atTop] (fun s => s ^ (1 / 2 : ℝ) * (-s) ^ (-(3 * N : ℤ))) := by
  refine airyMod_integrand_expansion (F := fun x => airyDerivModulus x ^ 2)
    (p := fun x => (-x) ^ (1 / 2 : ℝ) / π) airyDerivModulus_asymptotic
    (fun x hx => div_ne_zero (Real.rpow_pos_of_pos (by linarith) _).ne' Real.pi_ne_zero)
    airyMod_derivCoeff_values.1 (fun s hs => ?_) N
  have hM := (airyDerivModulus_pos (-s)).ne'
  have hq : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  have hsq : s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ) = s := by
    rw [← Real.rpow_add hs]; norm_num
  simp only [neg_neg]
  have e : s ^ (1 / 2 : ℝ) * (airyDerivModulus (-s) ^ 2 / (s ^ (1 / 2 : ℝ) / π))⁻¹ =
      (s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ)) / (π * airyDerivModulus (-s) ^ 2) := by
    rw [inv_div]; field_simp
  rw [e, hsq]

/-- The derivative-phase expansion at `+∞` in `s = -x`, with an undetermined constant. -/
theorem airyMod_derivPhase_expansion_s : ∃ L, Tendsto (fun s => airyDerivPhase (-s) -
      2 / 3 * s ^ (3 / 2 : ℝ)) atTop (𝓝 L) ∧
    ∀ N : ℕ, (fun s => airyDerivPhase (-s) - L - ∑ k ∈ Finset.range N,
      2 / 3 * s ^ (3 / 2 : ℝ) * (-s) ^ (-(3 * k : ℤ)) * airyDerivPhaseCoeff k) =O[atTop]
      (fun s => 2 / 3 * s ^ (3 / 2 : ℝ) * (-s) ^ (-(3 * N : ℤ))) := by
  obtain ⟨L, hL, hN⟩ := airyMod_expansion_of_deriv (fun s _ => airyMod_derivPhase_hasDerivAt s)
    airyMod_derivPhase_integrand
  refine ⟨L, by simpa [airyReciprocalCoeff] using hL, fun N => ?_⟩
  simpa [airyDerivPhaseCoeff] using hN N

/-- Explicit bounds on the constant `L` of the derivative-phase expansion. -/
private lemma airyMod_derivPhase_limit_bounds {L : ℝ}
    (hL : Tendsto (fun s => airyDerivPhase (-s) - 2 / 3 * s ^ (3 / 2 : ℝ)) atTop (𝓝 L)) :
    -π / 6 + -1 - 2 / 3 * (7 / 32) ≤ L ∧ L ≤ -π / 6 + 0 + 2 / 3 * (7 / 32) := by
  have hπ := Real.pi_pos
  have h := airyMod_limit_bounds (E := fun s => airyDerivPhase (-s) - 2 / 3 * s ^ (3 / 2 : ℝ))
    (e := fun s => s / (π * airyDerivModulus (-s) ^ 2) - s ^ (1 / 2 : ℝ)) (a := -1) (b := 0)
    (K := 7 / 32)
    (((airyDerivPhase_continuous.comp continuous_neg).sub
      (continuous_const.mul (Real.continuous_rpow_const (by norm_num)))).continuousOn)
    (fun s hs => by
      convert (airyMod_derivPhase_hasDerivAt s).sub
        ((Real.hasDerivAt_rpow_const (p := 3 / 2) (Or.inl hs.ne')).const_mul (2 / 3)) using 1
      norm_num; ring_nf)
    (fun s hs hs1 => by
      obtain ⟨h1, h2⟩ := airyMod_derivModulus_bounds hs
      have hA := airyDerivModulus_pos (-s)
      have hq : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
      have hq1 : s ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hs.le hs1.le (by norm_num)
      have hsq : s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ) = s := by
        rw [← Real.rpow_add hs]; norm_num
      have hqi : s ^ (-(1 / 2) : ℝ) = (s ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg hs.le _
      rw [hqi] at h1
      have hA2 : 0 < π * airyDerivModulus (-s) ^ 2 := by positivity
      have hkey : s ^ (1 / 2 : ℝ) ≤ π * airyDerivModulus (-s) ^ 2 := by
        have := mul_le_mul_of_nonneg_left h1 hq.le
        rw [show s ^ (1 / 2 : ℝ) * (π * (s ^ (1 / 2 : ℝ))⁻¹ * airyDerivModulus (-s) ^ 2) =
          π * airyDerivModulus (-s) ^ 2 by field_simp] at this
        linarith
      have hnn : 0 ≤ s / (π * airyDerivModulus (-s) ^ 2) := by positivity
      constructor
      · linarith
      · rw [sub_nonpos, div_le_iff₀ hA2]
        calc s = s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ) := hsq.symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hkey hq.le)
    (fun s hs => by
      have hs0 : 0 < s := by linarith
      obtain ⟨h1, h2⟩ := airyMod_derivModulus_bounds hs0
      set q := s ^ (1 / 2 : ℝ)
      set w := (s ^ 3)⁻¹
      have hq : 0 < q := Real.rpow_pos_of_pos hs0 _
      have hw : 0 < w := by positivity
      have hqi : s ^ (-(1 / 2) : ℝ) = q⁻¹ := Real.rpow_neg hs0.le _
      rw [hqi] at h1 h2
      set z := π * q⁻¹ * airyDerivModulus (-s) ^ 2
      have hsq : q * q = s := by
        simp only [q]; rw [← Real.rpow_add hs0]; norm_num
      have he : s / (π * airyDerivModulus (-s) ^ 2) = q / z := by
        simp only [z]; rw [← hsq]; field_simp
      have hp : s ^ (-(5 / 2) : ℝ) = q * w := by
        rw [show (-(5 / 2) : ℝ) = 1 / 2 + (-3 : ℝ) by norm_num, Real.rpow_add hs0,
          Real.rpow_neg hs0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [he, hp]
      have hz0 : 0 < z := by linarith
      have hnp : q / z - q ≤ 0 := by
        rw [sub_nonpos, div_le_iff₀ hz0]; nlinarith
      rw [abs_of_nonpos hnp, neg_sub, sub_div' hz0.ne', div_le_iff₀ hz0]
      nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 7 / 32 * q * w)])
    hL
  simpa [airyDerivPhase_zero, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)] using h

/-- The oscillatory asymptotics of `Ai'`, `Bi'` force `cos (L + π/4) = 1`. -/
private lemma airyMod_derivPhase_limit_cos {L : ℝ}
    (hL : Tendsto (fun s => airyDerivPhase (-s) - 2 / 3 * s ^ (3 / 2 : ℝ)) atTop (𝓝 L)) :
    Real.cos (L + π / 4) = 1 := by
  have hπ := Real.pi_pos
  set y : ℝ → ℝ := fun s => π * s ^ (-(1 / 2) : ℝ) * airyDerivModulus (-s) ^ 2
  have hy : Tendsto y atTop (𝓝 1) := by
    have hw : Tendsto (fun s : ℝ => 1 + 7 / 32 * (s ^ 3)⁻¹) atTop (𝓝 1) := by
      have := ((tendsto_pow_atTop (α := ℝ) (by norm_num : (3 : ℕ) ≠ 0)).inv_tendsto_atTop).const_mul
        (7 / 32 : ℝ)
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hw ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with s hs using (airyMod_derivModulus_bounds hs).1
    · filter_upwards [eventually_gt_atTop 0] with s hs using (airyMod_derivModulus_bounds hs).2
  have hu : Tendsto (fun s => Real.sqrt (y s)) atTop (𝓝 1) := by
    have := (Real.continuous_sqrt.tendsto 1).comp hy
    rw [Real.sqrt_one] at this
    exact this
  refine airyMod_cos_eq_one_of_limits (u := fun s => Real.sqrt (y s))
    (θ := fun s => airyDerivPhase (-s)) (β := fun s => airyZeta s - π / 4) hu ?_ ?_ ?_
  · refine (airyMod_tendsto_rpow_mul (Real.sqrt π) (a := -(1 / 4)) (by norm_num)
      airyMod_aiDerivReal_neg_sub).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    simp only [y]
    rw [airyMod_sqrt_eq hs (airyDerivModulus_pos _).le, airyAiDerivReal_eq_modulus_sin (-s)]
    have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
    have h4 : s ^ (-(1 / 4) : ℝ) * s ^ (1 / 4 : ℝ) = 1 := by
      rw [← Real.rpow_add hs]; norm_num
    generalize airyZeta s - π / 4 = α
    norm_num
    field_simp
    linear_combination (-Real.sin α) * h4
  · refine (airyMod_tendsto_rpow_mul (Real.sqrt π) (a := -(1 / 4)) (by norm_num)
      airyMod_biDerivReal_neg_sub).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    simp only [y]
    rw [airyMod_sqrt_eq hs (airyDerivModulus_pos _).le, airyBiDerivReal_eq_modulus_cos (-s)]
    have hsp : 0 < Real.sqrt π := Real.sqrt_pos.mpr hπ
    have h4 : s ^ (-(1 / 4) : ℝ) * s ^ (1 / 4 : ℝ) = 1 := by
      rw [← Real.rpow_add hs]; norm_num
    generalize airyZeta s - π / 4 = α
    norm_num
    field_simp
    linear_combination (-Real.cos α) * h4
  · refine (hL.add_const (π / 4)).congr fun s => ?_
    simp only [airyZeta]; ring

/-- The constant in the derivative-phase expansion is `-π/4`. -/
theorem airyMod_derivPhase_limit {L : ℝ}
    (hL : Tendsto (fun s => airyDerivPhase (-s) - 2 / 3 * s ^ (3 / 2 : ℝ)) atTop (𝓝 L)) :
    L = -π / 4 := by
  have hπ := Real.pi_pos
  have hb := airyMod_derivPhase_limit_bounds hL
  have := airyMod_eq_zero_of_cos_eq_one (airyMod_derivPhase_limit_cos hL) (by
    rw [abs_lt]; constructor <;> nlinarith [Real.pi_gt_three])
  linarith

/-- As `x → -∞`, `θ(x) - π/4 ∼ (2/3)(-x)^{3/2} ∑ₖ cₖ x^{-3k}` with the coefficients
`airyPhaseCoeff` (DLMF 9.8.22). -/
@[dlmf 9.8.E22]
theorem airyPhase_asymptotic :
    HasAsymptoticExpansion atBot (fun k (x : ℝ) => 2 / 3 * (-x) ^ (3 / 2 : ℝ) * x ^ (-(3 * k : ℤ)))
      airyPhaseCoeff (fun x => airyPhase x - (π / 4)) := by
  obtain ⟨L, hL, hN⟩ := airyMod_phase_expansion_s
  have hL4 := airyMod_phase_limit hL
  subst hL4
  intro N
  refine ((hN N).comp_tendsto tendsto_neg_atBot_atTop).congr' ?_ ?_
  · exact Eventually.of_forall fun x => by simp only [Function.comp_apply, neg_neg, smul_eq_mul]
  · exact Eventually.of_forall fun x => by simp only [Function.comp_apply, neg_neg]

/-- As `x → -∞`, `φ(x) + π/4 ∼ (2/3)(-x)^{3/2} ∑ₖ dₖ x^{-3k}` with the coefficients
`airyDerivPhaseCoeff` (DLMF 9.8.23). -/
@[dlmf 9.8.E23]
theorem airyDerivPhase_asymptotic :
    HasAsymptoticExpansion atBot (fun k (x : ℝ) => 2 / 3 * (-x) ^ (3 / 2 : ℝ) * x ^ (-(3 * k : ℤ)))
      airyDerivPhaseCoeff (fun x => airyDerivPhase x - (-π / 4)) := by
  obtain ⟨L, hL, hN⟩ := airyMod_derivPhase_expansion_s
  have hL4 := airyMod_derivPhase_limit hL
  subst hL4
  intro N
  refine ((hN N).comp_tendsto tendsto_neg_atBot_atTop).congr' ?_ ?_
  · exact Eventually.of_forall fun x => by simp only [Function.comp_apply, neg_neg, smul_eq_mul]
  · exact Eventually.of_forall fun x => by simp only [Function.comp_apply, neg_neg]

/-- Every printed coefficient in the phase expansions 9.8.22 and 9.8.23. -/
@[dlmf 9.8.E22, dlmf 9.8.E23]
theorem airy_phase_printed_coefficients :
    (∀ n < 5, airyPhaseCoeff n = ([1, 5/32, 1105/6144, 82825/65536, 1282031525/58720256] : List ℝ)[n]!) ∧
    (∀ n < 5, airyDerivPhaseCoeff n = ([1, -7/32, -1463/6144, -495271/327680, -206530429/8388608] : List ℝ)[n]!) := by
  constructor <;> intro n hn <;> interval_cases n <;>
    norm_num [airyPhaseCoeff, airyDerivPhaseCoeff, airyReciprocalCoeff,
      airyModulusCoeff, airyDerivModulusCoeff, Finset.sum_range_succ, Finset.prod_range_succ]

end DLMF.Airy

end
