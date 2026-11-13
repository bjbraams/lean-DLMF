/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import TauCeti.NumberTheory.ModularForms.JacobiTheta.OneVariable
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.Topology.Algebra.InfiniteSum.NatInt

/-!
# Quadratic Gauss reciprocity from the theta function

For positive integers `m,n` with even product, the Gauss sums with phases
`-πimr²/n` and `πinr²/m` are related by the principal factor `exp(-πi/4) √(n/m)`.
Coprimality is not needed. This proves the finite-sum identity underlying DLMF 20.11.2.

The residue-class calculation generalizes `jacobiTheta_two_div_add` from
`TauCeti.NumberTheory.ModularForms.JacobiTheta.GaussSum`. Mathlib supplies the theta
functional equation. TauCeti supplies integer-series splitting, theta bounds at infinity
and principal-power scaling. Comparing two normalized limits fixes the phase.

## Main results

* `GaussReciprocity.jacobiTheta_rational_add`: the finite residue-class identity.
* `GaussReciprocity.tendsto_sqrt_mul_jacobiTheta_rational`: its normalized cusp limit.
* `GaussReciprocity.sum_reciprocity`: the Gauss reciprocity identity.
-/

public section
open Complex Filter Topology TauCeti
open scoped Real
namespace DLMF.Theta.GaussReciprocity

/-- Splitting a theta function at a rational cusp into residue classes, with even quadratic
period. -/
lemma jacobiTheta_rational_add (a : ℤ) (N : ℕ) [NeZero N]
    (heven : Even (a * N)) {δ : ℂ} (hδ : 0 < δ.im) :
    jacobiTheta ((a : ℂ) / N + δ) =
      1 / (-I * ((N : ℂ) ^ 2 * δ)) ^ (1 / 2 : ℂ) *
        ∑ r : Fin N, cexp (π * I * a * (r : ℕ) ^ 2 / N) *
          jacobiTheta₂ ((r : ℕ) / N) (-1 / ((N : ℂ) ^ 2 * δ)) := by
  have exp_periodic (x : ℂ) (k : ℤ) : cexp (x + k * (2 * π * I)) = cexp x := by
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hδ0 : δ ≠ 0 := fun h => by simp [h] at hδ
  let T : ℂ := N ^ 2 * δ
  have hT0 : T ≠ 0 := mul_ne_zero (pow_ne_zero 2 hN) hδ0
  have hτ : 0 < ((a : ℂ) / N + δ).im := by
    rw [add_im, ← ofReal_intCast, ← ofReal_natCast, ← ofReal_div, ofReal_im, zero_add]
    exact hδ
  obtain ⟨b, hb⟩ := heven
  rw [jacobiTheta_eq_jacobiTheta₂, jacobiTheta₂,
    tsum_int_eq_sum_fin_tsum ((summable_jacobiTheta₂_term_iff _ _).2 hτ) N, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  let x : ℂ := (r : ℕ) / N
  have hterm (q : ℤ) : jacobiTheta₂_term (q * N + (r : ℕ)) 0 ((a : ℂ) / N + δ) =
      cexp (π * I * a * (r : ℕ) ^ 2 / N) * cexp (π * I * T * x ^ 2) *
        jacobiTheta₂_term q (T * x) T := by
    rw [jacobiTheta₂_term, jacobiTheta₂_term, ← Complex.exp_add, ← Complex.exp_add,
      ← exp_periodic _ (-(b * q ^ 2 + a * q * (r : ℕ)))]
    congr 1
    dsimp only [T, x]
    push_cast
    field_simp [hN]
    have hb' : (a : ℂ) * N = b + b := by exact_mod_cast hb
    linear_combination ((q : ℂ) ^ 2 * N) * hb'
  rw [tsum_congr hterm, tsum_mul_left, ← jacobiTheta₂, jacobiTheta₂_functional_equation,
    mul_div_cancel_left₀ _ hT0]
  have hcancel : cexp (π * I * T * x ^ 2) * cexp (-π * I * (T * x) ^ 2 / T) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    field_simp [hT0]
    ring_nf
  linear_combination (1 / (-I * T) ^ (1 / 2 : ℂ) * cexp (π * I * a * (r : ℕ) ^ 2 / N) *
    jacobiTheta₂ x (-1 / T)) * hcancel


/-- For a fixed real first argument, the two-variable theta function tends to one vertically at
infinity. -/
lemma tendsto_jacobiTheta₂_real_shift (x c d : ℝ) (hd : 0 < d) :
    Tendsto (fun t : ℝ => jacobiTheta₂ x (c + I / (d * t))) (𝓝[>] 0) (𝓝 1) := by
  have harg : Tendsto (fun t : ℝ => I / (d * t)) (𝓝[>] 0) (comap im atTop) := by
    refine tendsto_comap_iff.2 ?_
    have heq : (fun t : ℝ => (I / (d * t)).im) = fun t => d⁻¹ * t⁻¹ := by
      funext t
      rw [← ofReal_mul, div_ofReal_im, I_im, one_div, mul_inv]
    rw [Function.comp_def, heq]
    exact tendsto_inv_nhdsGT_zero.const_mul_atTop (inv_pos.2 hd)
  have hlim := (tendsto_iff_norm_sub_tendsto_zero.1
    (TauCeti.tendsto_jacobiTheta_comap_im_atTop.comp harg))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have him : ((c : ℂ) + I / (d * t)).im = 1 / (d * t) := by
    rw [add_im, ← ofReal_mul, div_ofReal_im, I_im, ofReal_im, zero_add]
  refine (TauCeti.norm_jacobiTheta₂_sub_one_le (by simp)
    (by rw [him]; positivity)).trans_eq ?_
  rw [him]
  congr 3
  push_cast
  field_simp [hd.ne', ht.ne']

/-- The theta function near a rational cusp, normalized by the positive real square root. -/
lemma sqrt_mul_jacobiTheta_rational_add_I_mul (a : ℤ) (N : ℕ) [NeZero N]
    (heven : Even (a * N)) {t : ℝ} (ht : 0 < t) :
    (Real.sqrt t : ℂ) * jacobiTheta ((a : ℂ) / N + I * t) =
      (1 / N : ℂ) * ∑ r : Fin N, cexp (π * I * a * (r : ℕ) ^ 2 / N) *
        jacobiTheta₂ ((r : ℕ) / N) (I / ((N : ℂ) ^ 2 * t)) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hNp : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
  have hs : ((N : ℂ) * Real.sqrt t) ^ 2 = -I * ((N : ℂ) ^ 2 * (I * t)) := by
    rw [mul_pow, ← ofReal_pow, Real.sq_sqrt ht.le]
    linear_combination ((N : ℂ) ^ 2 * t) * I_sq
  have hsre : 0 < ((N : ℂ) * Real.sqrt t).re := by
    simp only [← ofReal_natCast, ← ofReal_mul, ofReal_re]
    positivity
  have hroot : (-I * ((N : ℂ) ^ 2 * (I * t))) ^ (1 / 2 : ℂ) = N * Real.sqrt t := by
    rw [← hs, one_div]
    exact sq_cpow_two_inv hsre
  have harg : -1 / ((N : ℂ) ^ 2 * (I * t)) = I / ((N : ℂ) ^ 2 * t) := by
    field_simp [hN, htC]
    linear_combination -I_sq
  rw [jacobiTheta_rational_add a N heven (by simpa using ht), hroot, harg]
  have hst : (Real.sqrt t : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 ht).ne'
  field_simp [hN, hst]

/-- The normalized theta limit at a rational cusp is its quadratic Gauss sum divided by the
modulus. -/
lemma tendsto_sqrt_mul_jacobiTheta_rational (a : ℤ) (N : ℕ) [NeZero N]
    (heven : Even (a * N)) :
    Tendsto (fun t : ℝ => (Real.sqrt t : ℂ) * jacobiTheta ((a : ℂ) / N + I * t))
      (𝓝[>] 0) (𝓝 ((1 / N : ℂ) *
        ∑ r : Fin N, cexp (π * I * a * (r : ℕ) ^ 2 / N))) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have hsum : Tendsto (fun t : ℝ => ∑ r : Fin N,
      cexp (π * I * a * (r : ℕ) ^ 2 / N) *
        jacobiTheta₂ ((r : ℕ) / N) (I / ((N : ℂ) ^ 2 * t)))
      (𝓝[>] 0) (𝓝 (∑ r : Fin N, cexp (π * I * a * (r : ℕ) ^ 2 / N) * 1)) := by
    refine tendsto_finsetSum _ fun r _ => ?_
    have ht := tendsto_jacobiTheta₂_real_shift ((r : ℕ) / (N : ℝ)) 0 ((N : ℝ) ^ 2)
      (by positivity)
    push_cast at ht
    simpa only [zero_add] using ht.const_mul (cexp (π * I * a * (r : ℕ) ^ 2 / N))
  have hL : Tendsto (fun t : ℝ => (1 / N : ℂ) * ∑ r : Fin N,
      cexp (π * I * a * (r : ℕ) ^ 2 / N) *
        jacobiTheta₂ ((r : ℕ) / N) (I / ((N : ℂ) ^ 2 * t)))
      (𝓝[>] 0) (𝓝 ((1 / N : ℂ) *
        ∑ r : Fin N, cexp (π * I * a * (r : ℕ) ^ 2 / N))) := by
    simpa only [mul_one] using hsum.const_mul (1 / N : ℂ)
  refine hL.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  exact (sqrt_mul_jacobiTheta_rational_add_I_mul a N heven ht).symm


/-- The inverted normalized theta function is a finite sum with a continuous principal-root
prefactor. -/
lemma sqrt_mul_jacobiTheta_inversion_eq_sum (m n : ℕ) [NeZero m] [NeZero n]
    (heven : Even (m * n)) {t : ℝ} (ht : 0 < t) :
    (Real.sqrt t : ℂ) * jacobiTheta (-(m : ℂ) / n + I * t) =
      (1 / ((-I * (-(m : ℂ) / n + I * t)) ^ (1 / 2 : ℂ) *
        (-((m : ℂ) * n) / (-(m : ℂ) / n + I * t)) ^ (1 / 2 : ℂ))) *
      ∑ r : Fin m, cexp (π * I * n * (r : ℕ) ^ 2 / m) *
        jacobiTheta₂ ((r : ℕ) / m) (1 / ((m : ℂ) * n) + I / ((n : ℂ) ^ 2 * t)) := by
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
  let τ : ℂ := -(m : ℂ) / n + I * t
  have hτim : τ.im = t := by
    dsimp only [τ]
    rw [add_im, ← ofReal_natCast, ← ofReal_neg, ← ofReal_natCast,
      ← ofReal_div, ofReal_im, zero_add]
    simp
  have hτ0 : τ ≠ 0 := fun h => by rw [h, zero_im] at hτim; exact ht.ne' hτim.symm
  let δ : ℂ := -1 / τ - n / m
  have hδim : 0 < δ.im := by
    have hnR : (n : ℂ) / m = ((n / m : ℝ) : ℂ) := by push_cast; rfl
    dsimp only [δ]
    rw [sub_im, hnR, ofReal_im, sub_zero, neg_div, one_div, neg_im, inv_im, neg_div, neg_neg, hτim]
    exact div_pos ht (normSq_pos.2 hτ0)
  have hδ : δ = -(n : ℂ) * I * t / (m * τ) := by
    have htau : (n : ℂ) * τ = -(m : ℂ) + I * n * t := by
      dsimp only [τ]
      field_simp [hnC]
    dsimp only [δ]
    field_simp [hmC, hnC, hτ0]
    linear_combination -htau
  have harg : -1 / ((m : ℂ) ^ 2 * δ) =
      1 / ((m : ℂ) * n) + I / ((n : ℂ) ^ 2 * t) := by
    rw [hδ]
    dsimp only [τ]
    field_simp [hmC, hnC, htC, hτ0]
    linear_combination -(m : ℂ) * I_sq
  have hsplit : -I * ((m : ℂ) ^ 2 * δ) =
      (t : ℂ) * (-((m : ℂ) * n) / τ) := by
    rw [hδ]
    field_simp [hmC, hτ0]
    linear_combination I_sq
  have hroot : (-I * ((m : ℂ) ^ 2 * δ)) ^ (1 / 2 : ℂ) =
      (Real.sqrt t : ℂ) * (-((m : ℂ) * n) / τ) ^ (1 / 2 : ℂ) := by
    rw [hsplit, TauCeti.ofReal_mul_cpow ht.le]
    congr 1
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ht.le]
    norm_num
  have hF : jacobiTheta τ = 1 / (-I * τ) ^ (1 / 2 : ℂ) * jacobiTheta (-1 / τ) := by
    simpa only [jacobiTheta_eq_jacobiTheta₂, zero_pow (by decide : (2 : ℕ) ≠ 0),
      zero_mul, mul_zero, zero_div, exp_zero, mul_one] using
      jacobiTheta₂_functional_equation (0 : ℂ) τ
  have hpar : Even ((n : ℤ) * m) := by exact_mod_cast (by simpa [Nat.mul_comm] using heven)
  have hθ := jacobiTheta_rational_add (n : ℤ) m hpar hδim
  push_cast at hθ
  have hτarg : (n : ℂ) / m + δ = -1 / τ := by dsimp only [δ]; ring_nf
  rw [hτarg, harg, hroot] at hθ
  dsimp only [τ] at hF hθ
  rw [hF, hθ]
  have hs0 : (Real.sqrt t : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 ht).ne'
  field_simp [hmC, hnC, htC, hs0, hτ0]


set_option maxHeartbeats 0 in
/-- Gauss reciprocity for positive moduli with even product; coprimality is not required. -/
lemma sum_reciprocity (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (heven : Even (m * n)) :
    1 / (Real.sqrt n : ℂ) * ∑ k ∈ Finset.range n, cexp (-(π * I * k ^ 2 * m / n)) =
      cexp (-(π * I / 4)) / Real.sqrt m *
        ∑ j ∈ Finset.range m, cexp (π * I * j ^ 2 * n / m) := by
  have : NeZero m := ⟨hm.ne'⟩
  have : NeZero n := ⟨hn.ne'⟩
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let A : ℂ := ∑ r : Fin n, cexp (π * I * (-(m : ℂ)) * (r : ℕ) ^ 2 / n)
  let B : ℂ := ∑ r : Fin m, cexp (π * I * n * (r : ℕ) ^ 2 / m)
  let τ : ℝ → ℂ := fun t => -(m : ℂ) / n + I * t
  have hτ : Tendsto τ (𝓝[>] 0) (𝓝 (-(m : ℂ) / n)) := by
    have hc : Continuous τ := by dsimp only [τ]; fun_prop
    simpa only [τ, ofReal_zero, mul_zero, add_zero] using
      (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hτ0 : -(m : ℂ) / n ≠ 0 := div_ne_zero (neg_ne_zero.mpr hmC) hnC
  have hu : Tendsto (fun t => -I * τ t) (𝓝[>] 0) (𝓝 (I * m / n)) := by
    convert hτ.const_mul (-I) using 1; ring_nf
  have hv : Tendsto (fun t => -((m : ℂ) * n) / τ t) (𝓝[>] 0) (𝓝 ((n : ℂ) ^ 2)) := by
    have h := (tendsto_const_nhds (x := -((m : ℂ) * n))).div hτ hτ0
    convert h using 1
    field_simp [hmC, hnC]
  have huSlit : I * m / (n : ℂ) ∈ slitPlane := by
    right
    have hi : (I * m / (n : ℂ)).im = (m : ℝ) / n := by
      rw [← ofReal_natCast, ← ofReal_natCast, mul_div_assoc, ← ofReal_div, mul_im]
      simp
    rw [hi]
    positivity
  have hvSlit : (n : ℂ) ^ 2 ∈ slitPlane := by
    left
    rw [← ofReal_natCast, ← ofReal_pow, ofReal_re]
    positivity
  have hur : Tendsto (fun t => (-I * τ t) ^ (1 / 2 : ℂ)) (𝓝[>] 0)
      (𝓝 ((I * m / (n : ℂ)) ^ (1 / 2 : ℂ))) :=
    (continuousAt_cpow_const huSlit).tendsto.comp hu
  have hvr : Tendsto (fun t => (-((m : ℂ) * n) / τ t) ^ (1 / 2 : ℂ)) (𝓝[>] 0)
      (𝓝 (((n : ℂ) ^ 2) ^ (1 / 2 : ℂ))) :=
    (continuousAt_cpow_const hvSlit).tendsto.comp hv
  have huRoot0 : (I * m / (n : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (div_ne_zero (mul_ne_zero I_ne_zero hmC) hnC))
  have hvRoot0 : ((n : ℂ) ^ 2) ^ (1 / 2 : ℂ) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (pow_ne_zero 2 hnC))
  have hcoef : Tendsto (fun t =>
      1 / ((-I * τ t) ^ (1 / 2 : ℂ) * (-((m : ℂ) * n) / τ t) ^ (1 / 2 : ℂ)))
      (𝓝[>] 0) (𝓝 (1 / ((I * m / (n : ℂ)) ^ (1 / 2 : ℂ) *
        ((n : ℂ) ^ 2) ^ (1 / 2 : ℂ)))) :=
    tendsto_const_nhds.div (hur.mul hvr) (mul_ne_zero huRoot0 hvRoot0)
  have hsum : Tendsto (fun t : ℝ => ∑ r : Fin m, cexp (π * I * n * (r : ℕ) ^ 2 / m) *
      jacobiTheta₂ ((r : ℕ) / m) (1 / ((m : ℂ) * n) + I / ((n : ℂ) ^ 2 * t)))
      (𝓝[>] 0) (𝓝 B) := by
    have hsum' : Tendsto (fun t : ℝ => ∑ r : Fin m,
        cexp (π * I * n * (r : ℕ) ^ 2 / m) *
          jacobiTheta₂ ((r : ℕ) / m) (1 / ((m : ℂ) * n) + I / ((n : ℂ) ^ 2 * t)))
        (𝓝[>] 0) (𝓝 (∑ r : Fin m, cexp (π * I * n * (r : ℕ) ^ 2 / m) * 1)) := by
      refine tendsto_finsetSum _ fun r _ => ?_
      have h := tendsto_jacobiTheta₂_real_shift ((r : ℕ) / (m : ℝ)) (1 / ((m : ℝ) * n))
        ((n : ℝ) ^ 2) (by positivity)
      push_cast at h
      exact h.const_mul _
    simpa only [B, mul_one] using hsum'
  have hright : Tendsto (fun t : ℝ => (Real.sqrt t : ℂ) * jacobiTheta (τ t))
      (𝓝[>] 0) (𝓝 (1 / ((I * m / (n : ℂ)) ^ (1 / 2 : ℂ) *
        ((n : ℂ) ^ 2) ^ (1 / 2 : ℂ)) * B)) := by
    refine (hcoef.mul hsum).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact (sqrt_mul_jacobiTheta_inversion_eq_sum m n heven ht).symm
  have hEint : Even ((m : ℤ) * n) := by exact_mod_cast heven
  have hEneg : Even ((-(m : ℤ)) * n) := by simpa only [neg_mul] using hEint.neg
  have hleft : Tendsto (fun t : ℝ => (Real.sqrt t : ℂ) * jacobiTheta (τ t))
      (𝓝[>] 0) (𝓝 ((1 / n : ℂ) * A)) := by
    simpa only [τ, Int.cast_neg, Int.cast_natCast, A] using
      tendsto_sqrt_mul_jacobiTheta_rational (-(m : ℤ)) n hEneg
  have heq := tendsto_nhds_unique hleft hright
  have hI : I ^ (1 / 2 : ℂ) = cexp (π * I / 4) := by
    simpa only [Complex.sqrt, one_div] using Complex.sqrt_I_eq_exp
  have hreal (x : ℝ) (hx : 0 ≤ x) : (x : ℂ) ^ (1 / 2 : ℂ) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx]
    norm_num
  have huroot : (I * m / (n : ℂ)) ^ (1 / 2 : ℂ) =
      (Real.sqrt ((m : ℝ) / n) : ℂ) * cexp (π * I / 4) := by
    have hbase : I * m / (n : ℂ) = (((m : ℝ) / n : ℝ) : ℂ) * I := by push_cast; ring_nf
    rw [hbase, TauCeti.ofReal_mul_cpow (by positivity), hreal _ (by positivity), hI]
  have hvroot : ((n : ℂ) ^ 2) ^ (1 / 2 : ℂ) = n := by
    rw [one_div]
    exact sq_cpow_two_inv (by simpa using hnR)
  rw [huroot, hvroot, Real.sqrt_div hmR.le, ofReal_div] at heq
  have hsN : (Real.sqrt n : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 hnR).ne'
  have hsM : (Real.sqrt m : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 hmR).ne'
  have he0 : cexp (π * I / 4) ≠ 0 := exp_ne_zero _
  have hneg : cexp (-(π * I / 4)) = (cexp (π * I / 4))⁻¹ := exp_neg _
  have hA : A = ∑ k ∈ Finset.range n, cexp (-(π * I * k ^ 2 * m / n)) := by
    dsimp only [A]
    rw [← Fin.sum_univ_eq_sum_range (fun k => cexp (-(π * I * k ^ 2 * m / n)))]
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    ring_nf
  have hB : B = ∑ j ∈ Finset.range m, cexp (π * I * j ^ 2 * n / m) := by
    dsimp only [B]
    rw [← Fin.sum_univ_eq_sum_range (fun j => cexp (π * I * j ^ 2 * n / m))]
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    ring_nf
  rw [← hA, ← hB, hneg]
  field_simp [hmC, hnC, hsN, hsM, he0] at heq ⊢
  linear_combination heq

end DLMF.Theta.GaussReciprocity
