/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.SineCosine.GammaRepresentations

/-!
# Spherical series for generalized sine and cosine integrals

Spherical-function expansions and complementary tail identities for generalized trigonometric
integrals.

Source references and common attribution are retained in
`DLMF.IncompleteGamma.SineCosine`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF

open scoped Real Topology Nat

namespace DLMF.Confluent

/-- The entire part of the generalized sine integral, `∑ (-1)^k z^{2k+1}/((2k+1+a)(2k+1)!)`:
its Euler image `z H' + a H` is `sin z`. -/
theorem gsSph_sin_part {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) :
    let h : ℕ → ℂ → ℂ := fun k w => (-1 : ℂ)^k*w^(2*k+1)/((2*k+a+1)*(2*k+1).factorial)
    Differentiable ℂ (fun w => ∑' k, h k w) ∧
      ∀ w, w * deriv (fun w => ∑' k, h k w) w + a * ∑' k, h k w = sin w := by
  intro h
  have hne : ∀ k : ℕ, (2*k+a+1 : ℂ) ≠ 0 := fun k e => ha k (by linear_combination e)
  have hf : ∀ k w, HasDerivAt (h k) ((-1 : ℂ)^k*((2*k+1:ℕ) * w^(2*k))/
      ((2*k+a+1)*(2*k+1).factorial)) w := fun k w => by
    have := ((hasDerivAt_pow (2*k+1) w).const_mul ((-1:ℂ)^k)).div_const
      ((2*k+a+1)*(2*k+1).factorial)
    simpa using this
  have hb : ∀ R : ℝ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ n w, ‖w‖ < R → ‖h n w‖ ≤ u n := by
    intro R
    refine ⟨fun k => ‖(2*k+a+1 : ℂ)⁻¹‖ * (|R|^(2*k+1)/(2*k+1).factorial), ?_, fun k w hw => ?_⟩
    · have hd : Function.Injective (fun n : ℕ => 2*n+1) := by intro n m e; dsimp at e; omega
      refine Summable.of_norm_bounded_eventually_nat
        ((Real.summable_pow_div_factorial |R|).comp_injective hd) ?_
      filter_upwards [eventually_ge_atTop ⌈‖a‖⌉₊] with k hk
      have hk' : ‖a‖ ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
      have h1 : 1 ≤ ‖(2*k+a+1 : ℂ)‖ := by
        have := norm_sub_norm_le ((2*k+1 : ℂ)) (-a)
        rw [show (2*k+1:ℂ) - -a = 2*k+a+1 by ring, norm_neg,
          show (2*k+1:ℂ) = ((2*k+1:ℕ):ℂ) by push_cast; ring, Complex.norm_natCast] at this
        push_cast at this; linarith
      have hp : 0 ≤ |R|^(2*k+1)/((2*k+1).factorial : ℝ) := by positivity
      rw [Real.norm_of_nonneg (by positivity), norm_inv]
      simp only [Function.comp_apply]
      calc ‖(2*k+a+1 : ℂ)‖⁻¹ * (|R|^(2*k+1)/((2*k+1).factorial : ℝ))
          ≤ 1 * (|R|^(2*k+1)/((2*k+1).factorial : ℝ)) := by
            gcongr; exact inv_le_one_of_one_le₀ h1
        _ = _ := one_mul _
    · have hw' : ‖w‖ ≤ |R| := hw.le.trans (le_abs_self R)
      simp only [h, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Complex.norm_natCast]
      rw [div_eq_mul_inv, mul_inv, norm_inv]
      calc ‖w‖^(2*k+1) * (‖(2*k+a+1 : ℂ)‖⁻¹ * ((2*k+1).factorial : ℝ)⁻¹)
          ≤ |R|^(2*k+1) * (‖(2*k+a+1 : ℂ)‖⁻¹ * ((2*k+1).factorial : ℝ)⁻¹) := by gcongr
        _ = _ := by ring
  obtain ⟨hD, hS⟩ := sphSeries_euler_hasSum a hf hb
  refine ⟨hD, fun w => (hS w).unique ?_⟩
  refine (Complex.hasSum_sin w).congr_fun fun k => ?_
  have hf' : ((2*k+1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp only [h]
  field_simp [hne k]
  push_cast
  ring

/-- The entire part of the generalized cosine integral, `∑ (-1)^k z^{2k}/((2k+a)(2k)!)`:
its Euler image `z H' + a H` is `cos z`. -/
theorem gsSph_cos_part {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) :
    let h : ℕ → ℂ → ℂ := fun k w => (-1 : ℂ)^k*w^(2*k)/((2*k+a)*(2*k).factorial)
    Differentiable ℂ (fun w => ∑' k, h k w) ∧
      ∀ w, w * deriv (fun w => ∑' k, h k w) w + a * ∑' k, h k w = cos w := by
  intro h
  have hne : ∀ k : ℕ, (2*k+a : ℂ) ≠ 0 := fun k e => ha k (by linear_combination e)
  have hf : ∀ k w, HasDerivAt (h k) ((-1 : ℂ)^k*((2*k:ℕ) * w^(2*k-1))/
      ((2*k+a)*(2*k).factorial)) w := fun k w => by
    have := ((hasDerivAt_pow (2*k) w).const_mul ((-1:ℂ)^k)).div_const
      ((2*k+a)*(2*k).factorial)
    simpa using this
  have hb : ∀ R : ℝ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ n w, ‖w‖ < R → ‖h n w‖ ≤ u n := by
    intro R
    refine ⟨fun k => ‖(2*k+a : ℂ)⁻¹‖ * (|R|^(2*k)/(2*k).factorial), ?_, fun k w hw => ?_⟩
    · have hd : Function.Injective (fun n : ℕ => 2*n) := by intro n m e; dsimp at e; omega
      refine Summable.of_norm_bounded_eventually_nat
        ((Real.summable_pow_div_factorial |R|).comp_injective hd) ?_
      filter_upwards [eventually_ge_atTop (⌈‖a‖⌉₊+1)] with k hk
      have hk' : ‖a‖ + 1 ≤ 2*k := by
        have := (Nat.le_ceil ‖a‖).trans (by exact_mod_cast (Nat.le_of_succ_le hk) : (⌈‖a‖⌉₊:ℝ) ≤ k)
        have h1 : (1:ℝ) ≤ k := by exact_mod_cast (Nat.one_le_of_lt hk)
        linarith
      have h1 : 1 ≤ ‖(2*k+a : ℂ)‖ := by
        have := norm_sub_norm_le ((2*k : ℂ)) (-a)
        rw [show (2*k:ℂ) - -a = 2*k+a by ring, norm_neg,
          show (2*k:ℂ) = ((2*k:ℕ):ℂ) by push_cast; ring, Complex.norm_natCast] at this
        push_cast at this; linarith
      rw [Real.norm_of_nonneg (by positivity), norm_inv]
      simp only [Function.comp_apply]
      calc ‖(2*k+a : ℂ)‖⁻¹ * (|R|^(2*k)/((2*k).factorial : ℝ))
          ≤ 1 * (|R|^(2*k)/((2*k).factorial : ℝ)) := by
            gcongr; exact inv_le_one_of_one_le₀ h1
        _ = _ := one_mul _
    · have hw' : ‖w‖ ≤ |R| := hw.le.trans (le_abs_self R)
      simp only [h, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Complex.norm_natCast]
      rw [div_eq_mul_inv, mul_inv, norm_inv]
      calc ‖w‖^(2*k) * (‖(2*k+a : ℂ)‖⁻¹ * ((2*k).factorial : ℝ)⁻¹)
          ≤ |R|^(2*k) * (‖(2*k+a : ℂ)‖⁻¹ * ((2*k).factorial : ℝ)⁻¹) := by gcongr
        _ = _ := by ring
  obtain ⟨hD, hS⟩ := sphSeries_euler_hasSum a hf hb
  refine ⟨hD, fun w => (hS w).unique ?_⟩
  refine (Complex.hasSum_cos w).congr_fun fun k => ?_
  have hf' : ((2*k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp only [h]
  rcases k with _ | k
  · have ha0 : a ≠ 0 := by simpa using hne 0
    simp; field_simp [ha0]
  · have hp : w * w^(2*(k+1)-1) = w^(2*(k+1)) := by
      rw [show 2*(k+1)-1 = 2*k+1 by omega, show 2*(k+1) = 2*k+1+1 by ring, pow_succ]; ring
    field_simp [hne (k+1)]
    rw [div_eq_iff (hne (k+1))]
    push_cast at hp ⊢
    linear_combination (2*((k:ℂ)+1)) * hp

/-- The series with terms `(fun k : ℕ => z^a*(2*k+3/2 : ℂ)*poch (1-a/2) k/poch (1/2+a/2)
(k+1)*sphericalJ (2*k+1) z)` converges to `(genSinInt a z)`. -/
@[dlmf 8.21.E16]
theorem genSinInt_spherical_series {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => z^a*(2*k+3/2 : ℂ)*poch (1-a/2) k/poch (1/2+a/2) (k+1)*sphericalJ (2*k+1) z) (genSinInt a z) := by
  obtain ⟨hHd, hHL⟩ := gsSph_sin_part ha
  set H : ℂ → ℂ := fun w => ∑' k : ℕ, (-1 : ℂ)^k*w^(2*k+1)/((2*k+a+1)*(2*k+1).factorial) with hH
  have hQ : ∀ k : ℕ, (1/2+a/2+k : ℂ) ≠ 0 := fun k e => ha k (by linear_combination 2*e)
  have hQk : ∀ k : ℕ, poch (1/2+a/2) k ≠ 0 := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [poch_succ]; exact mul_ne_zero ih (hQ k)
  set c : ℕ → ℂ := fun k => (2*k+3/2 : ℂ)*poch (1-a/2) k/poch (1/2+a/2) (k+1) with hc
  set e : ℕ → ℂ := fun k => poch (1-a/2) k/poch (1/2+a/2) k with he
  clear_value c e
  have hratio := sphSeries_eventually_norm_add_le (1-a/2) (1/2+a/2)
  have hratio2 := sphSeries_eventually_norm_add_le (1-a/2) (1/2+a/2+1)
  have he_r : ∀ᶠ k in atTop, ‖e (k+1)‖ ≤ 2 * ‖e k‖ := by
    filter_upwards [hratio] with k hk
    simp only [he, poch_succ]
    rw [mul_div_mul_comm, norm_mul, norm_div]
    have hq := norm_pos_iff.mpr (hQ k)
    rw [mul_comm, show (1/2+a/2+k : ℂ) = 1/2+a/2+(k:ℂ) from rfl]
    have hb : ‖(1-a/2+k : ℂ)‖/‖(1/2+a/2+k : ℂ)‖ ≤ 2 := by rw [div_le_iff₀ hq]; linarith
    exact mul_le_mul_of_nonneg_right (by rw [norm_div]; exact hb) (by positivity)
  have hc_r : ∀ᶠ k in atTop, ‖c (k+1)‖ ≤ 6 * ‖c k‖ := by
    filter_upwards [hratio2] with k hk
    have hq := norm_pos_iff.mpr (hQ (k+1))
    have e1 : c (k+1) = c k * ((2*k+7/2)/(2*k+3/2)) * ((1-a/2+k)/(1/2+a/2+(k+1:ℕ))) := by
      have h32 : (2*(k:ℂ)+3/2) ≠ 0 := by
        have : (0:ℝ) < 2*k+3/2 := by positivity
        have h' : ((2*k+3/2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
        push_cast at h'; exact h'
      have hQ1 : (1/2+a/2+((k:ℂ)+1)) ≠ 0 := by have := hQ (k+1); push_cast at this; exact this
      have hQ0 := hQ k
      simp only [hc, poch_succ]
      push_cast
      generalize poch (1-a/2) k = P
      have hQk' := hQk k
      generalize poch (1/2+a/2) k = Q at hQk' ⊢
      generalize (1/2+a/2+(k:ℂ)) = u at hQ0 ⊢
      generalize (1/2+a/2+((k:ℂ)+1)) = v at hQ1 ⊢
      generalize (2*(k:ℂ)+3/2) = t at h32 ⊢
      field_simp
      ring
    rw [e1, norm_mul, norm_mul, norm_div, norm_div]
    have h1 : ‖(2*k+7/2 : ℂ)‖ ≤ 3 * ‖(2*k+3/2 : ℂ)‖ := by
      rw [show (2*k+7/2 : ℂ) = ((2*k+7/2 : ℝ) : ℂ) by push_cast; ring,
        show (2*k+3/2 : ℂ) = ((2*k+3/2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity)]
      linarith
    have h2 : ‖(1-a/2+k : ℂ)‖ ≤ 2 * ‖(1/2+a/2+(k+1:ℕ) : ℂ)‖ := by
      push_cast; rw [show (1/2+a/2+((k:ℂ)+1)) = 1/2+a/2+1+(k:ℂ) by ring]; exact hk
    have hp1 : 0 < ‖(2*k+3/2 : ℂ)‖ := by
      rw [show (2*k+3/2 : ℂ) = ((2*k+3/2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      positivity
    have hq' : 0 < ‖(1/2+a/2+(k+1:ℕ) : ℂ)‖ := by push_cast at hq ⊢; exact hq
    calc ‖c k‖ * (‖(2*k+7/2 : ℂ)‖/‖(2*k+3/2 : ℂ)‖) *
          (‖(1-a/2+k : ℂ)‖/‖(1/2+a/2+(k+1:ℕ) : ℂ)‖) ≤ ‖c k‖ * 3 * 2 := by
          gcongr
          · rw [div_le_iff₀ hp1]; linarith
          · rw [div_le_iff₀ hq']; linarith
      _ = 6 * ‖c k‖ := by ring
  have hL : ∀ k w, w * (c k * (((((2*k:ℕ):ℂ)+1) * sphericalJ (2*k) w - (((2*k:ℕ):ℂ)+2) *
      sphericalJ (2*k+2) w) / (2*((2*k:ℕ):ℂ)+3))) + a * (c k * sphericalJ (2*k+1) w) =
      w * (e k * sphericalJ (2*k) w) - w * (e (k+1) * sphericalJ (2*(k+1)) w) := by
    intro k w
    have hr := sphSeries_sphericalJ_recurrence (2*k) w
    have h3 : (2*((2*k:ℕ):ℂ)+3) ≠ 0 := by
      have : (0:ℝ) < 2*((2*k:ℕ):ℝ)+3 := by positivity
      have h' : ((2*((2*k:ℕ):ℝ)+3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
      push_cast at h' ⊢; exact h'
    have hJ : sphericalJ (2*k+1) w = w * (sphericalJ (2*k) w + sphericalJ (2*k+2) w) /
        (2*((2*k:ℕ):ℂ)+3) := by rw [eq_div_iff h3]; linear_combination -hr
    simp only [hc, he, poch_succ]
    rw [hJ, show 2*(k+1) = 2*k+2 by ring]
    have hQk' := hQk k
    have hQ' := hQ k
    push_cast at h3 ⊢
    generalize poch (1-a/2) k = P
    generalize poch (1/2+a/2) k = Q at hQk' ⊢
    generalize hu : (1/2+a/2+(k:ℂ)) = u at hQ' ⊢
    generalize ht : (2*(2*(k:ℂ))+3) = t at h3 ⊢
    field_simp
    subst hu ht
    ring
  have hpar : ∀ m : ℕ, a + m = 0 → iteratedDeriv m
      (fun w => ∑' n, c n * sphericalJ (2*n+1) w - H w) 0 = 0 := by
    intro m hm
    have hodd : ∀ w, (∑' n, c n * sphericalJ (2*n+1) (-w) - H (-w)) =
        (-1) * (∑' n, c n * sphericalJ (2*n+1) w - H w) := by
      intro w
      have h1 : ∑' n, c n * sphericalJ (2*n+1) (-w) = -∑' n, c n * sphericalJ (2*n+1) w := by
        rw [← tsum_neg]; congr 1; funext n
        rw [sphSeries_sphericalJ_neg, pow_succ, pow_mul]; simp
      have h2 : H (-w) = -H w := by
        simp only [hH]; rw [← tsum_neg]; congr 1; funext k
        rw [neg_pow w, pow_succ (-1:ℂ) (2*k), pow_mul]; simp; ring
      rw [h1, h2]; ring
    have hp := sphSeries_iteratedDeriv_parity
      (D := fun w => ∑' n, c n * sphericalJ (2*n+1) w - H w) hodd m
    rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
    · subst hr
      rw [← two_mul, pow_mul, neg_one_sq, one_pow] at hp
      rw [← two_mul]
      have : (1 - (-1) : ℂ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp hp).resolve_left this
    · exact absurd (by rw [hr] at hm; push_cast at hm; linear_combination hm) (ha r)
  have key := sphSeries_hasSum_of_euler (f := fun k w => c k * sphericalJ (2*k+1) w)
    (f' := fun k w => c k * (((((2*k:ℕ):ℂ)+1) * sphericalJ (2*k) w - (((2*k:ℕ):ℂ)+2) *
      sphericalJ (2*k+2) w) / (2*((2*k:ℕ):ℂ)+3)))
    (g := fun k w => w * (e k * sphericalJ (2*k) w)) (F := H) a
    (fun k w => (sphSeries_hasDerivAt_sphericalJ_succ (2*k) w).const_mul (c k))
    hL
    (fun w => by simpa using (sphSeries_tendsto_coeff_mul_sphericalJ e he_r 0 w).const_mul w)
    (sphSeries_bound_coeff_mul_sphericalJ c hc_r 1)
    hHd (fun w => by
      rw [hHL w]; simp [he, poch_zero, ← sphSeries_mul_sphericalJ_zero])
    hpar z
  -- conclude
  have hG := genSinInt_hasSum ha hz
  have hval : genSinInt a z = z^a * H z := by
    rw [hH, ← tsum_mul_left]
    refine hG.tsum_eq.symm.trans ?_
    exact tsum_congr (fun k => by ring)
  rw [hval]
  convert key.mul_left (z^a) using 1
  funext k; simp only [hc]; ring

/-- The series with terms `(fun k : ℕ => z^a*(2*k+1/2 : ℂ)*poch (1/2-a/2) k/poch (a/2)
(k+1)*sphericalJ (2*k) z)` converges to `(genCosInt a z)`. -/
@[dlmf 8.21.E17]
theorem genCosInt_spherical_series {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => z^a*(2*k+1/2 : ℂ)*poch (1/2-a/2) k/poch (a/2) (k+1)*sphericalJ (2*k) z) (genCosInt a z) := by
  obtain ⟨hHd, hHL⟩ := gsSph_cos_part ha
  set H : ℂ → ℂ := fun w => ∑' k : ℕ, (-1 : ℂ)^k*w^(2*k)/((2*k+a)*(2*k).factorial) with hH
  have hQ : ∀ k : ℕ, (a/2+k : ℂ) ≠ 0 := fun k e => ha k (by linear_combination 2*e)
  have hQk : ∀ k : ℕ, poch (a/2) k ≠ 0 := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [poch_succ]; exact mul_ne_zero ih (hQ k)
  set c : ℕ → ℂ := fun k => (2*k+1/2 : ℂ)*poch (1/2-a/2) k/poch (a/2) (k+1) with hc
  set e : ℕ → ℂ := fun k => poch (1/2-a/2) k/poch (a/2) k with he
  clear_value c e
  have hratio := sphSeries_eventually_norm_add_le (1/2-a/2) (a/2)
  have hratio2 := sphSeries_eventually_norm_add_le (1/2-a/2) (a/2+1)
  have he_r : ∀ᶠ k in atTop, ‖e (k+1)‖ ≤ 2 * ‖e k‖ := by
    filter_upwards [hratio] with k hk
    simp only [he, poch_succ]
    rw [mul_div_mul_comm, norm_mul, norm_div]
    have hq := norm_pos_iff.mpr (hQ k)
    rw [mul_comm]
    have hb : ‖(1/2-a/2+k : ℂ)‖/‖(a/2+k : ℂ)‖ ≤ 2 := by rw [div_le_iff₀ hq]; linarith
    exact mul_le_mul_of_nonneg_right (by rw [norm_div]; exact hb) (by positivity)
  have hc_r : ∀ᶠ k in atTop, ‖c (k+1)‖ ≤ 10 * ‖c k‖ := by
    filter_upwards [hratio2] with k hk
    have hq := norm_pos_iff.mpr (hQ (k+1))
    have e1 : c (k+1) = c k * ((2*k+5/2)/(2*k+1/2)) * ((1/2-a/2+k)/(a/2+(k+1:ℕ))) := by
      have h32 : (2*(k:ℂ)+1/2) ≠ 0 := by
        have : (0:ℝ) < 2*k+1/2 := by positivity
        have h' : ((2*k+1/2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
        push_cast at h'; exact h'
      have hQ1 : (a/2+((k:ℂ)+1)) ≠ 0 := by have := hQ (k+1); push_cast at this; exact this
      have hQ0 := hQ k
      simp only [hc, poch_succ]
      push_cast
      generalize poch (1/2-a/2) k = P
      have hQk' := hQk k
      generalize poch (a/2) k = Q at hQk' ⊢
      generalize (a/2+(k:ℂ)) = u at hQ0 ⊢
      generalize (a/2+((k:ℂ)+1)) = v at hQ1 ⊢
      generalize (2*(k:ℂ)+1/2) = t at h32 ⊢
      field_simp
      ring
    rw [e1, norm_mul, norm_mul, norm_div, norm_div]
    have h1 : ‖(2*k+5/2 : ℂ)‖ ≤ 5 * ‖(2*k+1/2 : ℂ)‖ := by
      rw [show (2*k+5/2 : ℂ) = ((2*k+5/2 : ℝ) : ℂ) by push_cast; ring,
        show (2*k+1/2 : ℂ) = ((2*k+1/2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity)]
      linarith
    have h2 : ‖(1/2-a/2+k : ℂ)‖ ≤ 2 * ‖(a/2+(k+1:ℕ) : ℂ)‖ := by
      push_cast; rw [show (a/2+((k:ℂ)+1)) = a/2+1+(k:ℂ) by ring]; exact hk
    have hp1 : 0 < ‖(2*k+1/2 : ℂ)‖ := by
      rw [show (2*k+1/2 : ℂ) = ((2*k+1/2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      positivity
    have hq' : 0 < ‖(a/2+(k+1:ℕ) : ℂ)‖ := by push_cast at hq ⊢; exact hq
    calc ‖c k‖ * (‖(2*k+5/2 : ℂ)‖/‖(2*k+1/2 : ℂ)‖) *
          (‖(1/2-a/2+k : ℂ)‖/‖(a/2+(k+1:ℕ) : ℂ)‖) ≤ ‖c k‖ * 5 * 2 := by
          gcongr
          · rw [div_le_iff₀ hp1]; linarith
          · rw [div_le_iff₀ hq']; linarith
      _ = 10 * ‖c k‖ := by ring
  set f' : ℕ → ℂ → ℂ := fun k w => c k * deriv (sphericalJ (2*k)) w with hf'
  have hdj0 := sphSeries_hasDerivAt_sphericalJ_zero
  have hdj : ∀ k w, HasDerivAt (sphericalJ (2*k)) (deriv (sphericalJ (2*k)) w) w := by
    intro k w
    rcases k with _ | k
    · exact (hdj0 w).differentiableAt.hasDerivAt
    · rw [show 2*(k+1) = (2*k+1)+1 by ring]
      exact (sphSeries_hasDerivAt_sphericalJ_succ (2*k+1) w).differentiableAt.hasDerivAt
  have hL : ∀ k w, w * f' k w + a * (c k * sphericalJ (2*k) w) =
      (if k = 0 then cos w else w * (e k * sphericalJ (2*k-1) w)) -
      (if k+1 = 0 then cos w else w * (e (k+1) * sphericalJ (2*(k+1)-1) w)) := by
    intro k w
    simp only [hf']
    rcases k with _ | k
    · rw [(hdj0 w).deriv]
      simp only [ite_true, one_ne_zero, ite_false,
        mul_zero, zero_add, show 2*(0+1)-1 = 1 by rfl]
      rw [← sphSeries_sphericalJ_zero_sub]
      have hQ0 := hQ 0
      have ha0 : a ≠ 0 := by have := ha 0; simpa using this
      simp only [hc, he, poch_succ, poch_zero]
      push_cast
      field_simp
      have hinv := mul_inv_cancel₀ ha0
      linear_combination (sphericalJ 0 w - w * sphericalJ 1 w) * hinv
    · rw [show 2*(k+1) = (2*k+1)+1 by ring, (sphSeries_hasDerivAt_sphericalJ_succ (2*k+1) w).deriv]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
      rw [show 2*k+1+1-1 = 2*k+1 by omega, show 2*(k+1+1)-1 = 2*k+1+2 by omega]
      have hr := sphSeries_sphericalJ_recurrence (2*k+1) w
      have h3 : (2*((2*k+1:ℕ):ℂ)+3) ≠ 0 := by
        have : (0:ℝ) < 2*((2*k+1:ℕ):ℝ)+3 := by positivity
        have h' : ((2*((2*k+1:ℕ):ℝ)+3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
        push_cast at h' ⊢; exact h'
      have hJ : sphericalJ (2*k+1+1) w = w * (sphericalJ (2*k+1) w + sphericalJ (2*k+1+2) w) /
          (2*((2*k+1:ℕ):ℂ)+3) := by rw [eq_div_iff h3]; linear_combination -hr
      simp only [hc, he, poch_succ]
      rw [hJ]
      have hQk' := hQk k
      have hQ' := hQ k
      have hQ'' : (a/2+((k:ℂ)+1)) ≠ 0 := by have := hQ (k+1); push_cast at this; exact this
      push_cast at h3 ⊢
      generalize poch (1/2-a/2) k = P
      generalize poch (a/2) k = Q at hQk' ⊢
      generalize hu : (a/2+(k:ℂ)) = u at hQ' ⊢
      generalize hv : (a/2+((k:ℂ)+1)) = v at hQ'' ⊢
      generalize ht : (2*(2*(k:ℂ)+1)+3) = t at h3 ⊢
      field_simp
      subst hu hv ht
      ring
  have hpar : ∀ m : ℕ, a + m = 0 → iteratedDeriv m
      (fun w => ∑' n, c n * sphericalJ (2*n) w - H w) 0 = 0 := by
    intro m hm
    have hev : ∀ w, (∑' n, c n * sphericalJ (2*n) (-w) - H (-w)) =
        1 * (∑' n, c n * sphericalJ (2*n) w - H w) := by
      intro w
      have h1 : ∑' n, c n * sphericalJ (2*n) (-w) = ∑' n, c n * sphericalJ (2*n) w := by
        congr 1; funext n
        rw [sphSeries_sphericalJ_neg, pow_mul]; simp
      have h2 : H (-w) = H w := by
        simp only [hH]; congr 1; funext k
        rw [neg_pow w, pow_mul (-1:ℂ)]; simp
      rw [h1, h2]; ring
    have hp := sphSeries_iteratedDeriv_parity
      (D := fun w => ∑' n, c n * sphericalJ (2*n) w - H w) hev m
    rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact absurd (by rw [hr] at hm; push_cast at hm; linear_combination hm) (ha r)
    · subst hr
      rw [pow_succ, pow_mul, neg_one_sq, one_pow] at hp
      have : ((1:ℂ) * (-1) - 1) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp hp).resolve_left this
  have hg : ∀ w, Tendsto (fun k => if k = 0 then cos w else
      w * (e k * sphericalJ (2*k-1) w)) atTop (𝓝 0) := by
    intro w
    rw [← tendsto_add_atTop_iff_nat 1]
    have he_r' : ∀ᶠ k in atTop, ‖e (k+1+1)‖ ≤ 2 * ‖e (k+1)‖ :=
      (tendsto_add_atTop_nat 1).eventually he_r
    have := (sphSeries_tendsto_coeff_mul_sphericalJ (fun k => e (k+1)) he_r' 1 w).const_mul w
    simp only [mul_zero] at this
    refine this.congr fun k => ?_
    simp [show 2*(k+1)-1 = 2*k+1 by omega]
  have key := sphSeries_hasSum_of_euler (f := fun k w => c k * sphericalJ (2*k) w)
    (f' := f') (F := H) a
    (fun k w => (hdj k w).const_mul (c k)) hL hg
    (sphSeries_bound_coeff_mul_sphericalJ c hc_r 0)
    hHd (fun w => by rw [hHL w]; simp)
    hpar z
  have hG := genCosInt_hasSum ha hz
  have hval : genCosInt a z = z^a * H z := by
    rw [hH, ← tsum_mul_left]
    refine hG.tsum_eq.symm.trans ?_
    exact tsum_congr (fun k => by ring)
  rw [hval]
  convert key.mul_left (z^a) using 1
  funext k; simp only [hc]; ring

/-- Generalized auxiliary f. -/
@[dlmf 8.21.E18]
def genTrigAuxF (a z : ℂ) : ℂ :=
  genSinIntTail a z*cos z-genCosIntTail a z*sin z

/-- Generalized auxiliary g. -/
@[dlmf 8.21.E19]
def genTrigAuxG (a z : ℂ) : ℂ :=
  genSinIntTail a z*sin z+genCosIntTail a z*cos z

/-- Identity under the stated parameter and domain assumptions: `genSinIntTail a z=genTrigAuxF a
z*cos z+genTrigAuxG a z*sin z`. -/
@[dlmf 8.21.E20]
theorem genSinIntTail_aux (a z : ℂ) :
    genSinIntTail a z=genTrigAuxF a z*cos z+genTrigAuxG a z*sin z := by
  unfold genTrigAuxF genTrigAuxG
  have h := Complex.sin_sq_add_cos_sq z
  linear_combination -genSinIntTail a z*h

/-- Identity under the stated parameter and domain assumptions: `genCosIntTail a z = -genTrigAuxF
a z*sin z+genTrigAuxG a z*cos z`. -/
@[dlmf 8.21.E21]
theorem genCosIntTail_aux (a z : ℂ) :
    genCosIntTail a z = -genTrigAuxF a z*sin z+genTrigAuxG a z*cos z := by
  unfold genTrigAuxF genTrigAuxG
  have h := Complex.sin_sq_add_cos_sq z
  linear_combination -genCosIntTail a z*h

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => sin t*(t+z)^(a-1)) 0
(genTrigAuxF a z)`. -/
@[dlmf 8.21.E22]
theorem genTrigAuxF_oscillatory_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => sin t*(t+z)^(a-1)) 0 (genTrigAuxF a z) := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => -cos z*genSinIntTail a (z+t)+sin z*genCosIntTail a (z+t))
      (sin t*(t+z)^(a-1)) t := by
    intro t ht
    obtain ⟨hS, hC⟩ := hasDerivAt_genTrigTail a (add_ofReal_mem_slitPlane hz ht)
    refine (hasDerivAt_comp_add_ofReal (g := fun w => -cos z*genSinIntTail a w+sin z*genCosIntTail a w)
      ((hS.const_mul _).add (hC.const_mul _))).congr_deriv ?_
    have hs : sin (t:ℂ) = sin (z+t)*cos z-cos (z+t)*sin z := by rw [← Complex.sin_sub]; ring_nf
    rw [hs, add_comm (t:ℂ) z]
    ring
  have hc : ContinuousOn (fun t : ℝ => sin t*(t+z)^(a-1)) (Ici 0) := by
    refine ContinuousOn.mul (by fun_prop) (fun t ht => ?_)
    have := add_ofReal_mem_slitPlane hz ht
    rw [add_comm] at this
    exact ((continuous_ofReal.continuousAt.add continuousAt_const).cpow continuousAt_const
      this).continuousWithinAt
  have hl : Tendsto (fun t : ℝ => -cos z*genSinIntTail a (z+t)+sin z*genCosIntTail a (z+t)) atTop (𝓝 0) := by
    obtain ⟨h1, h2⟩ := tendsto_genTrigTail_add_ofReal ha z
    simpa using (h1.const_mul (-cos z)).add (h2.const_mul (sin z))
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc hl
  convert h using 1
  simp [genTrigAuxF]; ring

/-- Horizontal-ray integral representation: `HasIntegralAtTop (fun t : ℝ => cos t*(t+z)^(a-1)) 0
(genTrigAuxG a z)`. -/
@[dlmf 8.21.E23]
theorem genTrigAuxG_oscillatory_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => cos t*(t+z)^(a-1)) 0 (genTrigAuxG a z) := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => -sin z*genSinIntTail a (z+t)-cos z*genCosIntTail a (z+t))
      (cos t*(t+z)^(a-1)) t := by
    intro t ht
    obtain ⟨hS, hC⟩ := hasDerivAt_genTrigTail a (add_ofReal_mem_slitPlane hz ht)
    refine (hasDerivAt_comp_add_ofReal (g := fun w => -sin z*genSinIntTail a w-cos z*genCosIntTail a w)
      ((hS.const_mul _).sub (hC.const_mul _))).congr_deriv ?_
    have hs : cos (t:ℂ) = cos (z+t)*cos z+sin (z+t)*sin z := by rw [← Complex.cos_sub]; ring_nf
    rw [hs, add_comm (t:ℂ) z]
    ring
  have hc : ContinuousOn (fun t : ℝ => cos t*(t+z)^(a-1)) (Ici 0) := by
    refine ContinuousOn.mul (by fun_prop) (fun t ht => ?_)
    have := add_ofReal_mem_slitPlane hz ht
    rw [add_comm] at this
    exact ((continuous_ofReal.continuousAt.add continuousAt_const).cpow continuousAt_const
      this).continuousWithinAt
  have hl : Tendsto (fun t : ℝ => -sin z*genSinIntTail a (z+t)-cos z*genCosIntTail a (z+t)) atTop (𝓝 0) := by
    obtain ⟨h1, h2⟩ := tendsto_genTrigTail_add_ofReal ha z
    simpa using (h1.const_mul (-sin z)).sub (h2.const_mul (cos z))
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc hl
  convert h using 1
  simp [genTrigAuxG]; ring

/-- Identity under the stated parameter and domain assumptions: `c.re = 0 ∧ (c.im = 1 ∨ c.im =
-1)`. -/
theorem incG_unit_cases {c : ℂ} (hc : c = I ∨ c = -I) : c.re = 0 ∧ (c.im = 1 ∨ c.im = -1) := by
  rcases hc with rfl | rfl <;> simp

/-- `(1+t)^k e^{-bt}` is integrable on `(0,∞)` for `b > 0`. -/
theorem incG_integrableOn_one_add_rpow_mul_exp {k b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => (1+t)^k * Real.exp (-b*t)) (Ioi 0) := by
  refine integrable_of_isBigO_exp_neg (b := b/2) (by positivity) ?_ ?_
  · intro t ht
    have ht0 : (0:ℝ) < 1+t := by have : (0:ℝ) ≤ t := ht; linarith
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')).comp
      (continuousAt_const.add continuousAt_id) |>.mul
      (Real.continuous_exp.continuousAt.comp (continuousAt_const.mul continuousAt_id))).continuousWithinAt
  · have h1 := (isLittleO_rpow_exp_pos_mul_atTop k (b := b/2) (by positivity)).isBigO.comp_tendsto
      (tendsto_atTop_add_const_left atTop 1 tendsto_id)
    have h := h1.mul (isBigO_refl (fun t : ℝ => Real.exp (-b*t)) atTop)
    have h2 : (fun t : ℝ => Real.exp (b/2*(1+t)) * Real.exp (-b*t)) =O[atTop]
        fun t => Real.exp (-(b/2)*t) := by
      refine (isBigO_const_mul_self (Real.exp (b/2)) _ _).congr' (Eventually.of_forall fun t => ?_)
        (Eventually.of_forall fun t => rfl)
      simp only; rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    exact (h.trans h2).congr' (Eventually.of_forall fun t => by simp [id]) (Eventually.of_forall fun _ => rfl)

/-- Estimate under the stated parameter and domain assumptions: `‖(1+c*t)^(a-1)‖ ≤ (1+t)^|a.re-1|
* Real.exp (π/2*|a.im|)`. -/
theorem incG_norm_one_add_cpow_le {c : ℂ} (hc : c = I ∨ c = -I) (a : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖(1+c*t)^(a-1)‖ ≤ (1+t)^|a.re-1| * Real.exp (π/2*|a.im|) := by
  obtain ⟨hre, him⟩ := incG_unit_cases hc
  have hu0 : (1+c*t) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hre] at this
  have hre1 : (1+c*(t:ℂ)).re = 1 := by simp [hre]
  rw [norm_cpow_of_ne_zero hu0]
  have hn1 : 1 ≤ ‖1+c*(t:ℂ)‖ := by
    have := Complex.abs_re_le_norm (1+c*(t:ℂ)); rw [hre1] at this; simpa using this
  have hn2 : ‖1+c*(t:ℂ)‖ ≤ 1+t := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    have : ‖c‖ = 1 := by rcases hc with rfl | rfl <;> simp
    rw [this, one_mul]
  have harg : |arg (1+c*(t:ℂ))| ≤ π/2 := abs_arg_le_pi_div_two_iff.mpr (by rw [hre1]; norm_num)
  have hA : ‖1+c*(t:ℂ)‖ ^ (a-1).re ≤ (1+t)^|a.re-1| := by
    rw [show (a-1).re = a.re - 1 by simp]
    rcases le_or_gt 0 (a.re-1) with h | h
    · rw [abs_of_nonneg h]; exact Real.rpow_le_rpow (by linarith) hn2 h
    · calc ‖1+c*(t:ℂ)‖ ^ (a.re-1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 h.le
        _ ≤ (1+t)^|a.re-1| := Real.one_le_rpow (by linarith) (abs_nonneg _)
  have hB : 1 / Real.exp (arg (1+c*(t:ℂ)) * (a-1).im) ≤ Real.exp (π/2*|a.im|) := by
    rw [one_div, ← Real.exp_neg, Real.exp_le_exp, show (a-1).im = a.im by simp]
    have := abs_mul (arg (1+c*(t:ℂ))) a.im
    have h2 : |arg (1+c*(t:ℂ))| * |a.im| ≤ π/2 * |a.im| := mul_le_mul_of_nonneg_right harg (abs_nonneg _)
    nlinarith [neg_abs_le (arg (1+c*(t:ℂ)) * a.im)]
  calc ‖1+c*(t:ℂ)‖ ^ (a-1).re / Real.exp (arg (1+c*(t:ℂ)) * (a-1).im)
      = ‖1+c*(t:ℂ)‖ ^ (a-1).re * (1 / Real.exp (arg (1+c*(t:ℂ)) * (a-1).im)) := by ring
    _ ≤ (1+t)^|a.re-1| * Real.exp (π/2*|a.im|) :=
        mul_le_mul hA hB (by positivity) (by positivity)

/-- Formula under the stated hypotheses: `1 + c*t ∈ slitPlane`. -/
theorem incG_one_add_mul_mem_slitPlane {c : ℂ} (hc : c = I ∨ c = -I) (t : ℝ) :
    1 + c*t ∈ slitPlane := Or.inl (by obtain ⟨hre, _⟩ := incG_unit_cases hc; simp [hre])

/-- The kernel `(fun t : ℝ => (1+c*t)^(a-1)*exp (-z*t))` is integrable on `(Ioi 0)`. -/
theorem incG_integrableOn_trigLap {c : ℂ} (hc : c = I ∨ c = -I) (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (1+c*t)^(a-1)*exp (-z*t)) (Ioi 0) := by
  refine Integrable.mono' ((incG_integrableOn_one_add_rpow_mul_exp (k := |a.re-1|) hz).mul_const
    (Real.exp (π/2*|a.im|))) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t _ => ContinuousAt.continuousWithinAt ?_) measurableSet_Ioi
    refine ContinuousAt.mul ?_ (by fun_prop)
    exact (continuousAt_const.add (continuousAt_const.mul continuous_ofReal.continuousAt)).cpow
      continuousAt_const (incG_one_add_mul_mem_slitPlane hc t)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0:ℝ) ≤ t := le_of_lt ht
    rw [norm_mul, Complex.norm_exp]
    have hre : (-z*(t:ℂ)).re = -z.re*t := by simp
    rw [hre]
    calc ‖(1+c*(t:ℂ))^(a-1)‖ * Real.exp (-z.re*t)
        ≤ ((1+t)^|a.re-1| * Real.exp (π/2*|a.im|)) * Real.exp (-z.re*t) :=
          mul_le_mul_of_nonneg_right (incG_norm_one_add_cpow_le hc a ht0) (Real.exp_pos _).le
      _ = (1+t)^|a.re-1| * Real.exp (-z.re*t) * Real.exp (π/2*|a.im|) := by ring

/-- Formula under the stated hypotheses: `z*(t-c) ∈ slitPlane`. -/
theorem incG_ray_mem_slitPlane {c : ℂ} (hc : c = I ∨ c = -I) {z : ℂ} (hz : 0 < z.re) {t : ℝ}
    (ht : 0 ≤ t) : z*(t-c) ∈ slitPlane := by
  obtain ⟨hre, him⟩ := incG_unit_cases hc
  rw [mem_slitPlane_iff]
  by_cases h : (z*((t:ℂ)-c)).im = 0
  · left
    simp only [mul_im, mul_re, sub_re, sub_im, ofReal_re, ofReal_im, hre] at h ⊢
    rcases him with h1 | h1 <;> rw [h1] at h ⊢ <;>
    · rcases ht.eq_or_lt with h0 | h0
      · subst h0; nlinarith
      · nlinarith [mul_pos hz h0, sq_nonneg t]
  · exact Or.inr h

/-- Splitting the power along the ray. -/
theorem incG_ray_cpow {c : ℂ} (hc : c = I ∨ c = -I) (a : ℂ) {z : ℂ} (hz : 0 < z.re) {t : ℝ}
    (ht : 0 ≤ t) :
    (z*(t-c))^(a-1) = z^(a-1)*((-c)^(a-1)*(1+c*t)^(a-1)) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  obtain ⟨hre, him⟩ := incG_unit_cases hc
  have hc0 : c ≠ 0 := by intro h; rw [h] at him; simp at him
  have hw0 : ((t:ℂ)-c) ≠ 0 := by intro h; have := congrArg Complex.im h; simp at this; rcases him with h1 | h1 <;> linarith
  have hv0 : (1+c*(t:ℂ)) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hre] at this
  have hfac : ((t:ℂ)-c) = (-c)*(1+c*t) := by
    have : c*c = -1 := by rcases hc with rfl | rfl <;> simp
    linear_combination (t:ℂ) * this
  have hzarg : |arg z| < π/2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have hwarg : |arg ((t:ℂ)-c)| ≤ π/2 := abs_arg_le_pi_div_two_iff.mpr (by simp [hre, ht])
  have hl1 : log (z*((t:ℂ)-c)) = log z + log ((t:ℂ)-c) := by
    refine Complex.log_mul hz0 hw0 ?_
    constructor <;> [skip; skip] <;> rw [abs_lt] at hzarg <;> rw [abs_le] at hwarg <;> linarith
  have hl2 : log ((-c)*(1+c*(t:ℂ))) = log (-c) + log (1+c*(t:ℂ)) := by
    refine Complex.log_mul (neg_ne_zero.mpr hc0) hv0 ?_
    have hv : |arg (1+c*(t:ℂ))| ≤ π/2 := abs_arg_le_pi_div_two_iff.mpr (by simp [hre])
    rcases hc with rfl | rfl
    · have : 0 ≤ arg (1+I*(t:ℂ)) := arg_nonneg_iff.mpr (by simp [ht])
      simp only [arg_neg_I]; rw [abs_le] at hv; constructor <;> linarith [Real.pi_pos]
    · have : arg (1+(-I)*(t:ℂ)) ≤ 0 := by
        rcases ht.eq_or_lt with h0 | h0
        · subst h0; simp
        · exact (arg_neg_iff.mpr (by simp [h0])).le
      simp only [neg_neg, arg_I]; rw [abs_le] at hv; constructor <;> linarith [Real.pi_pos]
  rw [cpow_def_of_ne_zero (mul_ne_zero hz0 hw0), hl1, cpow_def_of_ne_zero hz0,
    hfac, hl2, cpow_def_of_ne_zero (neg_ne_zero.mpr hc0), cpow_def_of_ne_zero hv0,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1; ring

/-- `Γ(a, z(t-c)) → 0` along the ray. -/
theorem incG_tendsto_upperIncGamma_ray (c : ℂ) (a : ℂ) {z : ℂ}
    (hz : 0 < z.re) :
    Tendsto (fun t : ℝ => upperIncGamma a (z*(t-c))) atTop (𝓝 0) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hn : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  set u : ℂ := z/‖z‖
  have hu : ‖u‖ = 1 := by simp [u, hn.ne']
  have hure : 0 < u.re := by simp [u]; exact div_pos hz hn
  have hray := tendsto_ray_sectorAtTop (-c*‖z‖) u hu (δ := u.re/2) (by positivity) (by linarith)
  have hs : Tendsto (fun t : ℝ => t*‖z‖) atTop atTop := tendsto_id.atTop_mul_const hn
  have h := (tendsto_exp_neg_mul_kummerU_sectorAtTop (1-a) (1-a) (δ := u.re/2) (by positivity)).comp
    (hray.comp hs)
  refine h.congr fun t => ?_
  simp only [Function.comp_apply, upperIncGamma]
  have hn' : ((‖z‖:ℝ):ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  congr 2 <;> · simp only [u]; push_cast; field_simp; ring

/-- Rotating the upper Gamma integral onto the ray `z(t - c)`, `c = ±i`. -/
theorem incG_upperIncGamma_rot {c : ℂ} (hc : c = I ∨ c = -I) (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    upperIncGamma a (-c*z) = z^a*(-c)^(a-1)*exp (c*z) *
      ∫ t : ℝ in Ioi 0, (1+c*t)^(a-1)*exp (-z*t) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  set F : ℝ → ℂ := fun t => upperIncGamma a (z*(t-c))
  set F' : ℝ → ℂ := fun t => -(z*(t-c))^(a-1)*exp (-(z*(t-c)))*z
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt F (F' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => z*((t:ℂ)-c)) z t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.sub_const c).const_mul z
    exact (hasDerivAt_upperIncGamma_complex a (incG_ray_mem_slitPlane hc hz ht)).comp t h1
  have hF' : ∀ t : ℝ, 0 ≤ t → F' t = -(z^a*(-c)^(a-1)*exp (c*z)) * ((1+c*t)^(a-1)*exp (-z*t)) := by
    intro t ht
    simp only [F']
    rw [incG_ray_cpow hc a hz ht, show -(z*((t:ℂ)-c)) = c*z + -z*t by ring, Complex.exp_add,
      cpow_sub _ _ hz0, cpow_one]
    field_simp
  have hint : IntegrableOn F' (Ioi 0) := by
    have h0 : IntegrableOn (fun t : ℝ => -(z^a*(-c)^(a-1)*exp (c*z)) * ((1+c*t)^(a-1)*exp (-z*t)))
        (Ioi 0) := (incG_integrableOn_trigLap hc a hz).const_mul _
    exact h0.congr_fun (fun t ht => (hF' t (le_of_lt ht)).symm) measurableSet_Ioi
  have hcont : ContinuousWithinAt F (Ici 0) 0 := (hd 0 le_rfl).continuousAt.continuousWithinAt
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun t ht => hd t (le_of_lt ht)) hint
    (incG_tendsto_upperIncGamma_ray c a hz)
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hF' t (le_of_lt ht)),
    integral_const_mul] at h
  simp only [F, ofReal_zero, zero_sub] at h
  rw [show z*(-c) = -c*z by ring] at h
  linear_combination h

/-- The two rotated upper Gamma values in the tails, as Laplace integrals. -/
theorem incG_trigTail_rot (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    genSinIntTail a z = (exp (π*I*a/2)*upperIncGamma a (-I*z) -
        exp (-π*I*a/2)*upperIncGamma a (I*z))/(2*I) ∧
    genCosIntTail a z = (exp (π*I*a/2)*upperIncGamma a (-I*z) +
        exp (-π*I*a/2)*upperIncGamma a (I*z))/2 := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have harg : |arg z| < π/2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [abs_lt] at harg
  have h1 : upperIncGammaOnLog a (log z - π*I/2) = upperIncGamma a (-I*z) := by
    rw [upperIncGammaOnLog_eq_upperIncGamma]
    · rw [sub_eq_add_neg, Complex.exp_add, Complex.exp_log hz0]
      congr 1
      rw [show -(↑π*I/2) = ((-(π/2):ℝ):ℂ)*I by push_cast; ring, Complex.exp_mul_I]
      simp; ring
    · simp [log_im]; linarith
    · simp [log_im]; linarith
  have h2 : upperIncGammaOnLog a (log z + π*I/2) = upperIncGamma a (I*z) := by
    rw [upperIncGammaOnLog_eq_upperIncGamma]
    · rw [Complex.exp_add, Complex.exp_log hz0]
      congr 1
      rw [show (↑π*I/2) = (((π/2):ℝ):ℂ)*I by push_cast; ring, Complex.exp_mul_I]
      simp; ring
    · simp [log_im]; linarith
    · simp [log_im]; linarith
  constructor
  · rw [genSinIntTail, genSinIntTailOnLog, h1, h2]
  · rw [genCosIntTail, genCosIntTailOnLog, h1, h2]

/-- Identity under the stated parameter and domain assumptions: `(-I)^(a-1) = exp (-π*I*a/2)*I`. -/
theorem incG_negI_cpow (a : ℂ) : (-I)^(a-1) = exp (-π*I*a/2)*I := by
  rw [cpow_sub _ _ (neg_ne_zero.mpr I_ne_zero), cpow_one, cpow_def_of_ne_zero (neg_ne_zero.mpr I_ne_zero),
    log_neg_I]
  field_simp
  ring_nf
  rw [I_sq]

/-- Identity under the stated parameter and domain assumptions: `I^(a-1) = -(exp (π*I*a/2)*I)`. -/
theorem incG_I_cpow (a : ℂ) : I^(a-1) = -(exp (π*I*a/2)*I) := by
  rw [cpow_sub _ _ I_ne_zero, cpow_one, cpow_def_of_ne_zero I_ne_zero, log_I]
  field_simp
  ring_nf
  rw [I_sq]; ring_nf

/-- Identity under the stated parameter and domain assumptions: `genTrigAuxF a z=z^a/2*(∫ t : ℝ in
Ioi 0, ((1+I*t)^(a-1)+(1-I*t)^(a-1))*exp (-z*t)) ∧ genTrigAuxG a z=z^a/(2*I)*(∫ t : ℝ in Ioi
0, ((1-I*t)^(a-1)-(1+I*t)^(a-1))*exp (-z*t))`. -/
lemma incG_genTrigAux_laplace (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    genTrigAuxF a z=z^a/2*(∫ t : ℝ in Ioi 0, ((1+I*t)^(a-1)+(1-I*t)^(a-1))*exp (-z*t)) ∧
    genTrigAuxG a z=z^a/(2*I)*(∫ t : ℝ in Ioi 0, ((1-I*t)^(a-1)-(1+I*t)^(a-1))*exp (-z*t)) := by
  obtain ⟨hS, hC⟩ := incG_trigTail_rot a hz
  have K1 := incG_upperIncGamma_rot (c := I) (Or.inl rfl) a hz
  have K2 := incG_upperIncGamma_rot (c := -I) (Or.inr rfl) a hz
  rw [neg_neg] at K2
  have hJ2 : (∫ t : ℝ in Ioi 0, (1+(-I)*t)^(a-1)*exp (-z*t)) =
      ∫ t : ℝ in Ioi 0, (1-I*t)^(a-1)*exp (-z*t) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [neg_mul, ← sub_eq_add_neg]
  rw [hJ2, incG_I_cpow] at K2
  rw [incG_negI_cpow] at K1
  set Jp := ∫ t : ℝ in Ioi 0, (1+I*t)^(a-1)*exp (-z*t)
  set Jm := ∫ t : ℝ in Ioi 0, (1-I*t)^(a-1)*exp (-z*t)
  have hip := incG_integrableOn_trigLap (c := I) (Or.inl rfl) a hz
  have him : IntegrableOn (fun t : ℝ => (1-I*t)^(a-1)*exp (-z*t)) (Ioi 0) := by
    have := incG_integrableOn_trigLap (c := -I) (Or.inr rfl) a hz
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only; rw [neg_mul, ← sub_eq_add_neg]
  have hsum : (∫ t : ℝ in Ioi 0, ((1+I*t)^(a-1)+(1-I*t)^(a-1))*exp (-z*t)) = Jp + Jm := by
    rw [← integral_add hip him]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  have hdiff : (∫ t : ℝ in Ioi 0, ((1-I*t)^(a-1)-(1+I*t)^(a-1))*exp (-z*t)) = Jm - Jp := by
    rw [← integral_sub him hip]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  rw [hsum, hdiff]
  have e1 : exp (-π*I*a/2) = (exp (π*I*a/2))⁻¹ := by rw [← Complex.exp_neg]; ring_nf
  have e2 : exp (-I*z) = (exp (I*z))⁻¹ := by rw [← Complex.exp_neg]; ring_nf
  have hcos' : cos z = (exp (I*z) + (exp (I*z))⁻¹)/2 := by
    have := two_cos z
    rw [show z*I = I*z by ring, show -z*I = -(I*z) by ring, Complex.exp_neg] at this
    linear_combination this/2
  have hsin' : sin z = ((exp (I*z))⁻¹ - exp (I*z))*I/2 := by
    have := two_sin z
    rw [show z*I = I*z by ring, show -z*I = -(I*z) by ring, Complex.exp_neg] at this
    linear_combination this/2
  have hE0 := Complex.exp_ne_zero (π*I*a/2)
  have hW0 := Complex.exp_ne_zero (I*z)
  constructor
  · rw [genTrigAuxF, hS, hC, K1, K2, hcos', hsin', e1, e2]
    field_simp
    ring_nf; rw [I_sq]; ring
  · rw [genTrigAuxG, hS, hC, K1, K2, hcos', hsin', e1, e2]
    field_simp
    ring_nf; rw [I_sq]; ring

/-- Identity under the stated parameter and domain assumptions: `genTrigAuxF a z=z^a/2*(∫ t : ℝ in
Ioi 0, ((1+I*t)^(a-1)+(1-I*t)^(a-1))*exp (-z*t))`. -/
@[dlmf 8.21.E24]
theorem genTrigAuxF_laplace_integral (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    genTrigAuxF a z=z^a/2*(∫ t : ℝ in Ioi 0, ((1+I*t)^(a-1)+(1-I*t)^(a-1))*exp (-z*t)) :=
  (incG_genTrigAux_laplace a hz).1

/-- Identity under the stated parameter and domain assumptions: `genTrigAuxG a z=z^a/(2*I)*(∫ t :
ℝ in Ioi 0, ((1-I*t)^(a-1)-(1+I*t)^(a-1))*exp (-z*t))`. -/
@[dlmf 8.21.E25]
theorem genTrigAuxG_laplace_integral (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    genTrigAuxG a z=z^a/(2*I)*(∫ t : ℝ in Ioi 0, ((1-I*t)^(a-1)-(1+I*t)^(a-1))*exp (-z*t)) :=
  (incG_genTrigAux_laplace a hz).2

/-- `e^{e^w} Γ(a, e^w) ~ ∑ (-1)^k (1-a)_k e^{(a-1-k) w}` on the logarithmic sector
`|im w| ≤ 3π/2 - δ` (DLMF 8.11.2 continued to the logarithmic plane). -/
theorem upperIncGammaOnLog_logSector_asymptotic (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/2) :
    HasAsymptoticExpansion (logSector (3*π/2-δ)) (fun (k : ℕ) w => exp ((a-1-k)*w))
      (fun k => (-1 : ℂ)^k*poch (1-a) k) (fun w => exp (exp w) * upperIncGammaOnLog a w) := by
  have h := (genExpIntE_log_sector_asymptotic (1-a) hδ hδ1).mul_left (fun w => exp (a*w + exp w))
  have hφ : (fun (k : ℕ) (w : ℂ) => exp (a*w + exp w) * exp (-exp w-(k+1 : ℂ)*w)) =
      fun (k : ℕ) w => exp ((a-1-k)*w) := by
    funext k w; rw [← Complex.exp_add]; congr 1; ring
  have hf : (fun w => exp (a*w + exp w) • genExpIntEOnLog (1-a) w) =
      fun w => exp (exp w) * upperIncGammaOnLog a w := by
    funext w
    rw [smul_eq_mul, genExpIntEOnLog, show (1:ℂ) - (1 - a) = a by ring, ← mul_assoc,
      ← Complex.exp_add]
    congr 2; ring
  rw [hφ, hf] at h
  exact h

/-- `z ↦ log z + iπ s/2` (`s = ±1`) maps `|arg z| ≤ π - δ` into the logarithmic sector
`|im w| ≤ 3π/2 - δ`, uniformly towards infinity. -/
theorem tendsto_log_add_sector {s : ℝ} (hs : |s| ≤ 1) {δ : ℝ} :
    Tendsto (fun z : ℂ => log z + s*π*I/2) (sector (π-δ)) (logSector (3*π/2-δ)) := by
  unfold sector logSector
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
  · refine (tendsto_comap.mono_left inf_le_left).congr' ?_
    filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
    obtain ⟨hz0, -⟩ := hz
    simp only [Function.comp, add_re, log_re]
    simp [Real.exp_log (norm_pos_iff.mpr hz0)]
  · filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
    obtain ⟨-, hza⟩ := hz
    show |(log z + s*π*I/2).im| ≤ 3*π/2-δ
    have him : (log z + s*π*I/2).im = arg z + s*π/2 := by simp [log_im]
    rw [him]
    have h1 := abs_le.mp hza
    have h2 := abs_le.mp hs
    rw [abs_le]; constructor <;> nlinarith [Real.pi_pos]

/-- `exp(s π i/2) = s i` for `s = ±1`. -/
theorem exp_sign_mul_pi_div_two_mul_I {s : ℝ} (hs : s = 1 ∨ s = -1) :
    exp ((s : ℂ) * π * I / 2) = s * I := by
  rcases hs with rfl | rfl
  · push_cast; rw [show (1:ℂ) * π * I / 2 = π / 2 * I by ring, exp_pi_div_two_mul_I]; ring
  · push_cast; rw [show (-1:ℂ) * π * I / 2 = -π / 2 * I by ring, exp_neg_pi_div_two_mul_I]; ring

/-- One exponential piece of the generalized auxiliary functions:
`e^{-sπia/2} e^{siz} Γ(a, z e^{sπi/2}) ~ ∑ e^{-s(k+1)πi/2} (-1)^k (1-a)_k z^{a-1-k}` (`s = ±1`)
in the sector `|arg z| ≤ π - δ`. -/
theorem upperIncGamma_rotated_piece_asymptotic (a : ℂ) {s : ℝ} (hs : s = 1 ∨ s = -1) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < π) :
    HasAsymptoticExpansion (sector (π-δ)) (fun (k : ℕ) z => z^(a-1-k))
      (fun k => exp (-((s : ℂ)*(k+1)*π*I/2)) * ((-1 : ℂ)^k*poch (1-a) k))
      (fun z => exp (-((s : ℂ)*π*I*a/2)) * (exp ((s : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + s*π*I/2))) := by
  have hs1 : |s| ≤ 1 := by rcases hs with rfl | rfl <;> norm_num
  have hnz : ∀ᶠ z in sector (π-δ), z ≠ 0 := by
    filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
    exact hz.1
  have h1 := (upperIncGammaOnLog_logSector_asymptotic a hδ (by linarith)).comp_tendsto
    (tendsto_log_add_sector hs1 (δ := δ))
  have h2 := h1.smul_scale (ψ := fun (k : ℕ) (z : ℂ) => z^(a-1-k))
    (κ := fun (k : ℕ) => exp ((a-1-k)*((s : ℂ)*π*I/2))) (fun k => by
      filter_upwards [hnz] with z hz0
      rw [cpow_def_of_ne_zero hz0, ← Complex.exp_add]; congr 1; ring)
  have h3 := h2.const_smul (exp (-((s : ℂ)*π*I*a/2)))
  refine (h3.congr' ?_).congr_coeff ?_
  · filter_upwards [hnz] with z hz0
    simp only [Pi.smul_apply, smul_eq_mul, Function.comp]
    rw [Complex.exp_add, Complex.exp_log hz0, exp_sign_mul_pi_div_two_mul_I hs]
    congr 2; ring_nf
  · funext k
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2; ring

/-- `exp(-s(k+1)πi/2) = (-s i)^{k+1}` for `s = ±1`. -/
theorem exp_neg_sign_mul_pi_div_two_mul_I_pow {s : ℝ} (hs : s = 1 ∨ s = -1) (k : ℕ) :
    exp (-((s : ℂ)*(k+1)*π*I/2)) = (-(s : ℂ) * I)^(k+1) := by
  have h := exp_sign_mul_pi_div_two_mul_I (s := -s) (by rcases hs with rfl | rfl <;> norm_num)
  rw [show -((s : ℂ)*(k+1)*π*I/2) = ((k+1 : ℕ) : ℂ) * (((-s : ℝ) : ℂ)*π*I/2) by push_cast; ring,
    Complex.exp_nat_mul, h]
  push_cast; ring

/-- The auxiliary functions in terms of the two exponential pieces. -/
lemma genTrigAux_eq_pieces (a z : ℂ) :
    genTrigAuxF a z = (exp (-(((-1:ℝ) : ℂ)*π*I*a/2)) * (exp (((-1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((-1:ℝ) : ℂ)*π*I/2)) -
      exp (-(((1:ℝ) : ℂ)*π*I*a/2)) * (exp (((1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((1:ℝ) : ℂ)*π*I/2))) / (2*I) ∧
    genTrigAuxG a z = (exp (-(((-1:ℝ) : ℂ)*π*I*a/2)) * (exp (((-1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((-1:ℝ) : ℂ)*π*I/2)) +
      exp (-(((1:ℝ) : ℂ)*π*I*a/2)) * (exp (((1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((1:ℝ) : ℂ)*π*I/2))) / 2 := by
  have e1 : log z + ((-1:ℝ) : ℂ)*π*I/2 = log z - π*I/2 := by push_cast; ring
  have e2 : log z + ((1:ℝ) : ℂ)*π*I/2 = log z + π*I/2 := by push_cast; ring
  have e3 : exp (-(((-1:ℝ) : ℂ)*π*I*a/2)) = exp (π*I*a/2) := by congr 1; push_cast; ring
  have e4 : exp (-(((1:ℝ) : ℂ)*π*I*a/2)) = exp (-π*I*a/2) := by congr 1; push_cast; ring
  have e5 : exp (((-1:ℝ) : ℂ)*I*z) = exp (-z*I) := by congr 1; push_cast; ring
  have e6 : exp (((1:ℝ) : ℂ)*I*z) = exp (z*I) := by congr 1; push_cast; ring
  rw [e1, e2, e3, e4, e5, e6]
  simp only [genTrigAuxF, genTrigAuxG, genSinIntTail, genCosIntTail, genSinIntTailOnLog,
    genCosIntTailOnLog, Complex.cos, Complex.sin]
  set X := upperIncGammaOnLog a (log z - π*I/2)
  set Y := upperIncGammaOnLog a (log z + π*I/2)
  set α := exp (π*I*a/2)
  set β := exp (-π*I*a/2)
  set u := exp (z*I)
  set v := exp (-z*I)
  constructor
  · field_simp
    ring_nf
    rw [I_sq]
    ring
  · field_simp
    ring_nf

/-- Identity under the stated parameter and domain assumptions: `HasAsymptoticExpansion (sector
(π-δ)) (fun k z => z^(a-1-2*k-0)) (fun k => (-1 : ℂ)^k*poch (1-a) (2*k+0)) (genTrigAuxF a)`. -/
@[dlmf 8.21.E26]
theorem genTrigAuxF_sector_asymptotic (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) :
    HasAsymptoticExpansion (sector (π-δ)) (fun k z => z^(a-1-2*k-0)) (fun k => (-1 : ℂ)^k*poch (1-a) (2*k+0)) (genTrigAuxF a) := by
  have hm := upperIncGamma_rotated_piece_asymptotic a (s := -1) (Or.inr rfl) hδ hδ1
  have hp := upperIncGamma_rotated_piece_asymptotic a (s := 1) (Or.inl rfl) hδ hδ1
  have h := (hm.sub hp).const_smul (1 / (2 * I))
  have hf : ((1 / (2 * I)) • ((fun z => exp (-(((-1:ℝ) : ℂ)*π*I*a/2)) * (exp (((-1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((-1:ℝ) : ℂ)*π*I/2))) -
      (fun z => exp (-(((1:ℝ) : ℂ)*π*I*a/2)) * (exp (((1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((1:ℝ) : ℂ)*π*I/2))))) = genTrigAuxF a := by
    funext z
    rw [(genTrigAux_eq_pieces a z).1]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [hf] at h
  have he := h.even (fun n => by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inr rfl),
      exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inl rfl)]
    push_cast
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_mul, pow_mul]
    simp)
  refine (he.congr_scale fun n => Eventually.of_forall fun z => ?_).congr_coeff ?_
  · simp only
    congr 1; push_cast; ring
  · funext n
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, add_zero]
    rw [exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inr rfl),
      exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inl rfl)]
    push_cast
    have h1 : (-(-1:ℂ) * I)^(2*n+1) = (-1)^n * I := by rw [pow_succ, pow_mul]; simp
    have h2 : (-(1:ℂ) * I)^(2*n+1) = -((-1)^n * I) := by rw [pow_succ, pow_mul]; simp
    rw [h1, h2, pow_mul (-1:ℂ) 2 n]
    field_simp
    ring

/-- Identity under the stated parameter and domain assumptions: `HasAsymptoticExpansion (sector
(π-δ)) (fun k z => z^(a-1-2*k-1)) (fun k => (-1 : ℂ)^k*poch (1-a) (2*k+1)) (genTrigAuxG a)`. -/
@[dlmf 8.21.E27]
theorem genTrigAuxG_sector_asymptotic (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) :
    HasAsymptoticExpansion (sector (π-δ)) (fun k z => z^(a-1-2*k-1)) (fun k => (-1 : ℂ)^k*poch (1-a) (2*k+1)) (genTrigAuxG a) := by
  have hm := upperIncGamma_rotated_piece_asymptotic a (s := -1) (Or.inr rfl) hδ hδ1
  have hp := upperIncGamma_rotated_piece_asymptotic a (s := 1) (Or.inl rfl) hδ hδ1
  have h := (hm.add hp).const_smul (1 / 2 : ℂ)
  have hf : ((1 / 2 : ℂ) • ((fun z => exp (-(((-1:ℝ) : ℂ)*π*I*a/2)) * (exp (((-1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((-1:ℝ) : ℂ)*π*I/2))) +
      (fun z => exp (-(((1:ℝ) : ℂ)*π*I*a/2)) * (exp (((1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((1:ℝ) : ℂ)*π*I/2))))) = genTrigAuxG a := by
    funext z
    rw [(genTrigAux_eq_pieces a z).2]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [hf] at h
  have ho := h.odd (fun n => by
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inr rfl),
      exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inl rfl)]
    push_cast
    have h1 : (-(-1:ℂ) * I)^(2*n+1) = (-1)^n * I := by rw [pow_succ, pow_mul]; simp
    have h2 : (-(1:ℂ) * I)^(2*n+1) = -((-1)^n * I) := by rw [pow_succ, pow_mul]; simp
    rw [h1, h2]
    ring)
  refine (ho.congr_scale fun n => Eventually.of_forall fun z => ?_).congr_coeff ?_
  · simp only
    congr 1; push_cast; ring
  · funext n
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inr rfl),
      exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inl rfl)]
    push_cast
    have h1 : (-(-1:ℂ) * I)^(2*n+1+1) = (-1)^(n+1) := by
      rw [show 2*n+1+1 = 2*(n+1) by ring, pow_mul]; simp
    have h2 : (-(1:ℂ) * I)^(2*n+1+1) = (-1)^(n+1) := by
      rw [show 2*n+1+1 = 2*(n+1) by ring, pow_mul]; simp
    rw [h1, h2, pow_succ (-1:ℂ) (2*n), pow_mul (-1:ℂ) 2 n, pow_succ (-1:ℂ) n]
    ring

end DLMF.Confluent

end
