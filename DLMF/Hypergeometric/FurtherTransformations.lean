/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Solutions
public import DLMF.Hypergeometric.ArgumentContinuation

/-!
# Further transformations (DLMF §15.8)

All nonterminating series arguments are restricted to their convergence disks.
Regularized linear transformations retain singular denominator parameters.
Terminating transformations have no disk restriction, but denominator parameters
must still avoid undefined cancellations. E18 is already `gauss_quadratic` and its
inverse `kummer_quadratic`. E12 is `regularized_euler` with `c = a+b-m`.
E29 and E30 are specializations of E21 and of E13/E15, respectively.
Remaining two-term quadratic and logarithmic formulas are in `ConnectionFormulas`.
Formulas that require global continuation are not recorded here.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology ComplexConjugate

noncomputable section

namespace DLMF.Hypergeometric

@[dlmf 15.8.E1]
theorem regularized_euler (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z =
      (1 - z) ^ (c - a - b) * regularizedGaussHGFun (c - a) (c - b) c z :=
  regularizedGaussHGFun_euler a b c hz

@[dlmf 15.8.E1]
theorem regularized_pfaff (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (ht : ‖z / (z - 1)‖ < 1) :
    regularizedGaussHGFun a b c z =
      (1 - z) ^ (-a) * regularizedGaussHGFun a (c - b) c (z / (z - 1)) :=
  regularizedGaussHGFun_pfaff a b c hz ht

@[dlmf 15.8.E4]
theorem regularized_connection_one_sub (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (ht : ‖1 - z‖ < 1) :
    sin (Real.pi * (c - a - b)) / Real.pi * regularizedGaussHGFun a b c z =
      regularizedGaussHGFun a b (a + b - c + 1) (1 - z) / (Gamma (c - a) * Gamma (c - b)) - (1 - z) ^ (c - a
        - b) / (Gamma a * Gamma b) * regularizedGaussHGFun (c - a) (c - b) (c - a - b + 1) (1 - z) := by
  have h := connLhs_eq_connRhs a b c (z := z) ⟨hz, ht⟩
  simp only [connLhs, connRhs] at h
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show sin (Real.pi * (c - a - b)) / Real.pi * regularizedGaussHGFun a b c z =
    (sin (Real.pi * (c - a - b)) * regularizedGaussHGFun a b c z) / Real.pi by ring, h]
  field_simp

@[dlmf 15.8.E3]
theorem regularized_connection_one_div_one_sub
    (a b c : ℂ)
    {z : ℂ}
    (hz : ‖z‖ < 1)
    (ht : ‖1 /
    (1 - z)‖ < 1) :
    sin (Real.pi * (b - a)) / Real.pi * regularizedGaussHGFun a b c z =
      (1 - z) ^ (-a) / (Gamma b * Gamma (c - a)) * regularizedGaussHGFun a (c - b) (a - b + 1) (1 / (1 - z))
        - (1 - z) ^ (-b) / (Gamma a * Gamma (c - b)) * regularizedGaussHGFun b (c - a) (b - a + 1) (1 / (1 -
        z)) := by
  have h1z : 1 - z ≠ 0 := by
    intro h
    have h1 : z = 1 := by linear_combination -h
    rw [h1] at hz
    simp at hz
  have hz1 : z - 1 ≠ 0 := by intro h; apply h1z; linear_combination -h
  have hw : 1 < ‖1 - z‖ := by
    rw [norm_div, norm_one, div_lt_iff₀ (norm_pos_iff.mpr h1z)] at ht
    linarith
  have hu : ‖z / (z - 1)‖ < 1 := by
    rw [norm_div, norm_sub_rev, div_lt_one (by linarith)]
    linarith
  have h1u : 1 - z / (z - 1) = 1 / (1 - z) := by
    field_simp
    ring
  have hslit : 1 - z ∈ slitPlane := by
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    have := (re_le_norm z).trans_lt hz
    simp only [sub_re, one_re]
    linarith
  have key := regularized_connection_one_sub a (c - b) c (z := z / (z - 1)) hu (by rwa [h1u])
  rw [show c - a - (c - b) = b - a by ring, show c - (c - b) = b by ring,
    show a + (c - b) - c + 1 = a - b + 1 by ring, show b - a + 1 = b - a + 1 by ring, h1u,
    regularizedGaussHGFun_symm (c - a) b] at key
  rw [regularized_pfaff a b c hz hu]
  have hp : (1 - z) ^ (-a) * (1 / (1 - z)) ^ (b - a) = (1 - z) ^ (-b) := by
    rw [one_div, inv_cpow _ _ (by
      intro h
      rcases mem_slitPlane_iff.mp hslit with h' | h'
      · rw [arg_eq_pi_iff] at h; linarith [h.1]
      · rw [arg_eq_pi_iff] at h; exact h' h.2), ← cpow_neg, ← cpow_add _ _ h1z]
    ring_nf
  calc sin (Real.pi * (b - a)) / Real.pi * ((1 - z) ^ (-a) *
        regularizedGaussHGFun a (c - b) c (z / (z - 1)))
      = (1 - z) ^ (-a) * (sin (Real.pi * (b - a)) / Real.pi *
        regularizedGaussHGFun a (c - b) c (z / (z - 1))) := by ring
    _ = _ := by
      rw [key, ← hp]
      ring

@[dlmf 15.8.E5]
theorem regularized_connection_one_sub_recip
    (a b c : ℂ)
    {z : ℂ}
    (hz : ‖z‖ < 1)
    (ht : ‖1 - 1 / z‖ < 1) :
    sin (Real.pi * (c - a - b)) / Real.pi * regularizedGaussHGFun a b c z =
      z ^ (-a) / (Gamma (c - a) * Gamma (c - b)) * regularizedGaussHGFun a (a - c + 1) (a + b - c + 1) (1 -
        1 / z) - (1 - z) ^ (c - a - b) * z ^ (a - c) / (Gamma a * Gamma b) * regularizedGaussHGFun (c - a)
        (1 - a) (c - a - b + 1) (1 - 1 / z) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at ht
  have hlt : ‖1 - z‖ < ‖z‖ := by
    have : ‖(z - 1) / z‖ < 1 := by
      rw [show (z - 1) / z = 1 - 1 / z by field_simp]; exact ht
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hz0), norm_sub_rev] at this
    exact this
  have hw : ‖1 - z‖ < 1 := hlt.trans hz
  have hmap : (1 - z) / (1 - z - 1) = 1 - 1 / z := by
    rw [show (1 : ℂ) - z - 1 = -z by ring]
    field_simp
    ring
  have hw' : ‖(1 - z) / (1 - z - 1)‖ < 1 := by rwa [hmap]
  have key := regularized_connection_one_sub a b c hz hw
  rw [regularized_pfaff a b (a + b - c + 1) hw hw', regularized_pfaff (c - a) (c - b)
    (c - a - b + 1) hw hw', hmap, sub_sub_cancel, show a + b - c + 1 - b = a - c + 1 by ring,
    show c - a - b + 1 - (c - b) = 1 - a by ring, show -(c - a) = a - c by ring] at key
  rw [key]
  ring

/-- Reflection of Pochhammer symbols: `(1-y-n)_n = (-1)^n (y)_n`. -/
theorem poch_one_sub_sub (y : ℂ) (n : ℕ) : poch (1 - y - n) n = (-1 : ℂ) ^ n * poch y n :=
  poch_reflect y n

@[dlmf 15.8.E6]
theorem terminating_reciprocal
    {b c z : ℂ}
    (m : ℕ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, 1 - b - m ≠ -(k : ℂ))
    (hz : z ≠ 0) :
    ₂F₁ (-m : ℂ) b c z =
      poch b m / poch c m * (-z) ^ m * ₂F₁ (-m : ℂ) (1 - c - m) (1 - b - m) (1 / z) := by
  have hcm := poch_ne_zero_of_not_neg_nat hc m
  rw [ordinaryHypergeometric_eq_sum_neg_nat, ordinaryHypergeometric_eq_sum_neg_nat,
    Finset.mul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show m + 1 - 1 - k = m - k by omega, gaussHGCoeff_neg_nat, gaussHGCoeff_neg_nat,
    Nat.choose_symm hkm]
  have hmk : m - (m - k) = k := by omega
  have hc1 := poch_one_sub_sub_mul (x := c) (Nat.sub_le m k)
  have hb1 := poch_one_sub_sub_mul (x := b) (Nat.sub_le m k)
  rw [hmk] at hc1 hb1
  have hbk : poch (1 - b - m) k ≠ 0 := poch_ne_zero_of_not_neg_nat ht k
  have hck : poch c (m - k) ≠ 0 := poch_ne_zero_of_not_neg_nat hc (m - k)
  have hpm : (-1 : ℂ) ^ m = (-1) ^ (m - k) * (-1) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkm]
  have hzm : z ^ m = z ^ (m - k) * z ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkm]
  have hsq : ((-1 : ℂ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [neg_pow z, hpm, hzm, one_div, inv_pow]
  field_simp
  linear_combination (m.choose k : ℂ) * poch c m * hb1 -
    (m.choose k : ℂ) * poch b m * ((-1 : ℂ) ^ k) ^ 2 * hc1 -
    (m.choose k : ℂ) * (-1 : ℂ) ^ k * poch b m * poch c m * hsq

/-- Pfaff's transformation for a terminating series, for every `w ≠ 1`. -/
theorem terminating_pfaff (m : ℕ) {b c w : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hw : w ≠ 1) :
    ₂F₁ (-m : ℂ) b c w = (1 - w) ^ m * ₂F₁ (-m : ℂ) (c - b) c (w / (w - 1)) := by
  set Q : ℂ → ℂ := fun v => ∑ k ∈ Finset.range (m + 1),
    gaussHGCoeff (-m : ℂ) (c - b) c k * (-1 : ℂ) ^ k * v ^ k * (1 - v) ^ (m - k) with hQ
  have hQeq (v : ℂ) (hv : v ≠ 1) :
      (1 - v) ^ m * ₂F₁ (-m : ℂ) (c - b) c (v / (v - 1)) = Q v := by
    have hv1 : 1 - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv)
    rw [ordinaryHypergeometric_eq_sum_neg_nat, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show v / (v - 1) = -v / (1 - v) by rw [show v - 1 = -(1 - v) by ring, div_neg, neg_div],
      div_pow, neg_pow v, show (1 - v) ^ m = (1 - v) ^ (m - k) * (1 - v) ^ k by
        rw [← pow_add, Nat.sub_add_cancel hkm]]
    field_simp
  have hP : AnalyticOnNhd ℂ (fun v : ℂ => ₂F₁ (-m : ℂ) b c v) Set.univ := by
    have : (fun v : ℂ => ₂F₁ (-m : ℂ) b c v) =
        fun v => ∑ k ∈ Finset.range (m + 1), gaussHGCoeff (-(m : ℂ)) b c k * v ^ k := by
      funext v
      exact ordinaryHypergeometric_eq_sum_neg_nat m b c v
    rw [this]
    exact fun v _ => (Differentiable.analyticAt (by fun_prop) v)
  have hQa : AnalyticOnNhd ℂ Q Set.univ := fun v _ =>
    (Differentiable.analyticAt (by simp only [hQ]; fun_prop) v)
  have hball : Set.EqOn (fun v : ℂ => ₂F₁ (-m : ℂ) b c v) Q (Metric.ball 0 (1 / 2)) := by
    intro v hv
    rw [Metric.mem_ball, dist_zero_right] at hv
    have hv1 : v ≠ 1 := by rintro rfl; norm_num at hv
    have hn : 1 / 2 < ‖v - 1‖ := by
      have := norm_sub_norm_le (1 : ℂ) v
      rw [norm_one, norm_sub_rev] at this
      linarith
    have hvn : ‖v / (v - 1)‖ < 1 := by
      rw [norm_div, div_lt_one (by linarith)]
      linarith
    simp only
    rw [pfaff_transformation_of_ne_neg_nat hc (by linarith) hvn, show -(-(m : ℂ)) = m by ring,
      ← hQeq v hv1]
    norm_cast
  have hall := eq_of_analyticOnNhd_univ_of_eqOn hP hQa Metric.isOpen_ball
    ⟨0, by simp⟩ hball
  rw [hQeq w hw]
  exact congrFun hall w

@[dlmf 15.8.E6]
theorem terminating_reciprocal_one_sub
    {b c z : ℂ}
    (m : ℕ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, 1 - b - m ≠ -(k : ℂ))
    (hz : z ≠ 1) :
    ₂F₁ (-m : ℂ) b c z =
      poch b m / poch c m * (1 - z) ^ m * ₂F₁ (-m : ℂ) (c - b) (1 - b - m) (1 / (1 - z)) := by
  by_cases hz0 : z = 0
  · subst hz0
    have hbm : poch b m ≠ 0 := by
      intro h
      apply poch_ne_zero_of_not_neg_nat ht m
      rw [poch_one_sub_sub, h, mul_zero]
    rw [ordinaryHypergeometric_zero, sub_zero, div_one, one_pow, mul_one, chu_vandermonde m ht,
      show 1 - b - m - (c - b) = 1 - c - m by ring, poch_one_sub_sub, poch_one_sub_sub]
    field_simp [poch_ne_zero_of_not_neg_nat hc m]
  · rw [terminating_reciprocal m hc ht hz0,
      terminating_pfaff m ht (by
        intro h
        apply hz
        field_simp at h
        exact h.symm),
      show 1 - b - m - (1 - c - m) = c - b by ring,
      show 1 / z / (1 / z - 1) = 1 / (1 - z) by
        have : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
        field_simp]
    rw [← mul_assoc, mul_assoc (poch b m / poch c m), ← mul_pow,
      show -z * (1 - 1 / z) = 1 - z by field_simp; ring]

@[dlmf 15.8.E7]
theorem terminating_one_sub_recip
    {b c z : ℂ}
    (m : ℕ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, b - c - m + 1 ≠ -(k : ℂ))
    (hz : z ≠ 0) :
    ₂F₁ (-m : ℂ) b c z =
      poch (c - b) m / poch c m * z ^ m * ₂F₁ (-m : ℂ) (1 - c - m) (b - c - m + 1) (1 - 1 / z) := by
  by_cases hz1 : z = 1
  · subst hz1
    rw [chu_vandermonde m hc, div_one, sub_self, ordinaryHypergeometric_zero, one_pow]
    ring
  · have hu0 : z / (z - 1) ≠ 0 := div_ne_zero hz (sub_ne_zero.mpr hz1)
    have ht' : ∀ k : ℕ, 1 - (c - b) - m ≠ -(k : ℂ) := by
      simpa [show ∀ x : ℂ, b - c - m + 1 = x ↔ 1 - (c - b) - m = x from fun x => by
        constructor <;> intro h <;> linear_combination h] using ht
    rw [terminating_pfaff m hc hz1, terminating_reciprocal m hc ht' hu0,
      show 1 - (c - b) - m = b - c - m + 1 by ring,
      show 1 / (z / (z - 1)) = 1 - 1 / z by field_simp,
      show (1 - z) ^ m * (poch (c - b) m / poch c m * (-(z / (z - 1))) ^ m *
          ₂F₁ (-(m : ℂ)) (1 - c - m) (b - c - m + 1) (1 - 1 / z)) =
        poch (c - b) m / poch c m * ((1 - z) * -(z / (z - 1))) ^ m *
          ₂F₁ (-(m : ℂ)) (1 - c - m) (b - c - m + 1) (1 - 1 / z) by rw [mul_pow]; ring,
      show (1 - z) * -(z / (z - 1)) = z by
        have : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
        field_simp
        ring]

@[dlmf 15.8.E7]
theorem terminating_one_sub
    {b c z : ℂ}
    (m : ℕ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, b - c - m + 1 ≠ -(k : ℂ)) :
    ₂F₁ (-m : ℂ) b c z =
      poch (c - b) m / poch c m * ₂F₁ (-m : ℂ) b (b - c - m + 1) (1 - z) := by
  have hCm : poch (c - b) m ≠ 0 := by
    intro h
    apply poch_ne_zero_of_not_neg_nat ht m
    rw [show b - c - m + 1 = 1 - (c - b) - m by ring, poch_one_sub_sub, h, mul_zero]
  by_cases hz0 : z = 0
  · subst hz0
    rw [ordinaryHypergeometric_zero, sub_zero, chu_vandermonde m ht,
      show b - c - m + 1 - b = 1 - c - m by ring, show b - c - m + 1 = 1 - (c - b) - m by ring,
      poch_one_sub_sub, poch_one_sub_sub]
    field_simp [poch_ne_zero_of_not_neg_nat hc m]
  · rw [terminating_one_sub_recip m hc ht hz0, terminating_pfaff m ht (by
        intro h
        have h' : (1 : ℂ) / z = 0 := by linear_combination -h
        simp [hz0] at h'),
      show b - c - m + 1 - (1 - c - m) = b by ring,
      show (1 - 1 / z) / (1 - 1 / z - 1) = 1 - z by field_simp; ring,
      show (1 : ℂ) - (1 - 1 / z) = 1 / z by ring]
    rw [show poch (c - b) m / poch c m * z ^ m * ((1 / z) ^ m * ₂F₁ (-(m : ℂ)) b (b - c - m + 1)
        (1 - z)) = poch (c - b) m / poch c m * (z * (1 / z)) ^ m *
          ₂F₁ (-(m : ℂ)) b (b - c - m + 1) (1 - z) by rw [mul_pow]; ring,
      mul_one_div_cancel hz0, one_pow, mul_one]

/-! ### Uniqueness at the origin and Gauss's quadratic transformation -/

/-- An analytic solution of the Gauss equation near the origin with value `1` there is
`₂F₁(a,b;c;·)`, when `c` is not a nonpositive integer. -/
theorem eq_ordinaryHypergeometric_of_gaussOperator {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (Metric.ball 0 r))
    (hode : ∀ w ∈ Metric.ball (0 : ℂ) r, gaussOperator a b c g w = 0) (h0 : g 0 = 1) :
    ∀ w ∈ Metric.ball (0 : ℂ) r, g w = ₂F₁ a b c w := by
  have hU : ∀ w ∈ Metric.ball (0 : ℂ) r, ‖w‖ < 1 := fun w hw =>
    lt_of_lt_of_le (by simpa using hw) hr1
  have hF : AnalyticOnNhd ℂ (₂F₁ a b c : ℂ → ℂ) (Metric.ball 0 r) := fun w hw =>
    analyticAt_ordinaryHypergeometric (hU w hw)
  have hFode : ∀ w ∈ Metric.ball (0 : ℂ) r, gaussOperator a b c (₂F₁ a b c : ℂ → ℂ) w = 0 :=
    fun w hw => gaussOperator_ordinaryHypergeometric hc (hU w hw)
  have h0U : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := Metric.mem_ball_self hr
  have hall (n : ℕ) : iteratedDeriv n g 0 = iteratedDeriv n (₂F₁ a b c) 0 := by
    induction n with
    | zero => simp [h0, ordinaryHypergeometric_zero]
    | succ n ih =>
      have hg' := gaussOperator_iteratedDeriv Metric.isOpen_ball hg hode n 0 h0U
      have hF' := gaussOperator_iteratedDeriv Metric.isOpen_ball hF hFode n 0 h0U
      have hcn : (n : ℂ) + c ≠ 0 := by
        simpa only [ne_eq, eq_neg_iff_add_eq_zero, add_comm] using hc n
      have hm : ((n : ℂ) + c) * (iteratedDeriv (n + 1) g 0 -
          iteratedDeriv (n + 1) (₂F₁ a b c) 0) = 0 := by
        linear_combination hg' - hF' -
          (-((n : ℂ) * (n - 1)) - n * (a + b + 1) - a * b) * ih
      exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hcn)
  have hp := (hg 0 h0U).hasFPowerSeriesAt
  have hq := (hF 0 h0U).hasFPowerSeriesAt
  simp_rw [hall] at hp
  have hev : g =ᶠ[𝓝 0] ₂F₁ a b c := by
    filter_upwards [hp.eventually_hasSum_sub, hq.eventually_hasSum_sub] with w hw₁ hw₂
    exact hw₁.unique hw₂
  exact hg.eqOn_of_preconnected_of_eventuallyEq hF (convex_ball 0 r).isPreconnected h0U hev

/-- Principal square root of a square in the right half-plane. -/
theorem sq_cpow_half {x : ℂ} (hx : 0 < x.re) : (x ^ 2) ^ (1 / 2 : ℂ) = x := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have harg : |x.arg| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  have hsq : x ^ 2 = exp (2 * log x) := by
    rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, exp_nat_mul, exp_log hx0]
  have hlog : log (x ^ 2) = 2 * log x := by
    rw [hsq, log_exp]
    · simp only [mul_im, log_im, re_ofNat, im_ofNat, zero_mul, add_zero]
      have := (abs_lt.mp harg).1
      linarith
    · simp only [mul_im, log_im, re_ofNat, im_ofNat, zero_mul, add_zero]
      have := (abs_lt.mp harg).2
      linarith
  rw [cpow_def_of_ne_zero (pow_ne_zero 2 hx0), hlog,
    show 2 * log x * (1 / 2) = log x by ring, exp_log hx0]

/-- The principal square root of a point of the right half-plane lies in the right half-plane. -/
theorem re_cpow_half_pos {y : ℂ} (hy : 0 < y.re) : 0 < (y ^ (1 / 2 : ℂ)).re := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have harg : |y.arg| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy)
  rw [cpow_def_of_ne_zero hy0, exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  simp only [mul_im, log_im, log_re, one_div, inv_re, inv_im, re_ofNat, im_ofNat]
  have h1 := (abs_lt.mp harg).1
  have h2 := (abs_lt.mp harg).2
  constructor <;> norm_num <;> nlinarith [Real.pi_pos]

/-- `(y^{1/2})² = y` for `y ≠ 0`. -/
theorem cpow_half_sq {y : ℂ} (hy : y ≠ 0) : (y ^ (1 / 2 : ℂ)) ^ 2 = y := by
  rw [sq, ← cpow_add _ _ hy]
  norm_num

/-- The quadratic lobe `Re z < 1/2`, `‖4z(1-z)‖ < 1` lies in the unit disk. -/
theorem norm_lt_one_of_quadratic_lobe {z : ℂ} (hre : z.re < 1 / 2)
    (hzt : ‖4 * z * (1 - z)‖ < 1) : ‖z‖ < 1 := by
  by_contra h
  push Not at h
  have h1 : 1 / 2 < ‖1 - z‖ := by
    have := re_le_norm (1 - z)
    simp only [sub_re, one_re] at this
    linarith
  rw [norm_mul, norm_mul] at hzt
  have : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [this] at hzt
  nlinarith [norm_nonneg z, norm_nonneg (1 - z)]

/-- The inverse of the quadratic map `z ↦ 4z(1-z)` on the unit disk. -/
theorem quadratic_lobe_of_mem_ball {w : ℂ} (hw : ‖w‖ < 1) :
    let z := (1 - (1 - w) ^ (1 / 2 : ℂ)) / 2
    ‖z‖ < 1 ∧ ‖4 * z * (1 - z)‖ < 1 ∧ z.re < 1 / 2 ∧ 4 * z * (1 - z) = w := by
  intro z
  have hre1 : 0 < (1 - w).re := by
    have := (re_le_norm w).trans_lt hw
    simp only [sub_re, one_re]
    linarith
  have h1w : 1 - w ≠ 0 := by rintro h; rw [h] at hre1; simp at hre1
  have hsq := cpow_half_sq h1w
  have hzw : 4 * z * (1 - z) = w := by
    simp only [z]
    linear_combination -hsq
  have hzre : z.re < 1 / 2 := by
    have := re_cpow_half_pos hre1
    simp only [z, div_re, sub_re, one_re, re_ofNat, im_ofNat, normSq_ofNat]
    norm_num
    linarith
  refine ⟨norm_lt_one_of_quadratic_lobe hzre (by rw [hzw]; exact hw), by rw [hzw]; exact hw,
    hzre, hzw⟩

/-- Gauss's quadratic transformation, AAR (3.1.3), on the component containing zero. -/
@[dlmf 15.8.E18]
theorem gauss_quadratic {a b z : ℂ}
    (hc : ∀ k : ℕ, a + b + 1 / 2 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1) (hzt : ‖4 * z * (1 - z)‖ < 1) (hre : z.re < 1 / 2) :
    ₂F₁ (2 * a) (2 * b) (a + b + 1 / 2) z =
      ₂F₁ a b (a + b + 1 / 2) (4 * z * (1 - z)) := by
  set c := a + b + 1 / 2 with hcdef
  set G : ℂ → ℂ := fun w => ₂F₁ a b c (4 * w * (1 - w)) with hG
  have hφ : ∀ w : ℂ, HasDerivAt (fun w : ℂ => 4 * w * (1 - w)) (4 - 8 * w) w := by
    intro w
    exact (((hasDerivAt_id w).const_mul 4).mul
      ((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w))).congr_deriv (by simp; ring)
  have hφa : ∀ w : ℂ, AnalyticAt ℂ (fun w : ℂ => 4 * w * (1 - w)) w := fun w =>
    (analyticAt_const.mul analyticAt_id).mul (analyticAt_const.sub analyticAt_id)
  -- Step 1: `G` solves the Gauss equation for `(2a, 2b, c)` near the origin.
  have hsmall : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 8), ‖4 * w * (1 - w)‖ < 1 := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    rw [norm_mul, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
    have : ‖1 - w‖ ≤ 1 + ‖w‖ := by
      have := norm_sub_le (1 : ℂ) w
      rwa [norm_one] at this
    nlinarith [norm_nonneg w, norm_nonneg (1 - w)]
  have hGan : AnalyticOnNhd ℂ G (Metric.ball 0 (1 / 8)) := fun w hw =>
    (analyticAt_ordinaryHypergeometric (hsmall w hw)).comp
      (f := fun v : ℂ => 4 * v * (1 - v)) (hφa w)
  have hGode : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 8), gaussOperator (2 * a) (2 * b) c G w = 0 := by
    intro w hw
    have hFw : AnalyticAt ℂ (₂F₁ a b c) (4 * w * (1 - w)) :=
      analyticAt_ordinaryHypergeometric (hsmall w hw)
    have hd1 : deriv G =ᶠ[𝓝 w] fun v => deriv (₂F₁ a b c) (4 * v * (1 - v)) * (4 - 8 * v) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hw] with v hv
      exact ((analyticAt_ordinaryHypergeometric (hsmall v hv)).differentiableAt.hasDerivAt.comp
        v (hφ v)).deriv
    have hd2 : HasDerivAt (fun v => deriv (₂F₁ a b c) (4 * v * (1 - v)) * (4 - 8 * v))
        (iteratedDeriv 2 (₂F₁ a b c) (4 * w * (1 - w)) * (4 - 8 * w) * (4 - 8 * w) +
          deriv (₂F₁ a b c) (4 * w * (1 - w)) * (-8)) w := by
      have h1 := (hFw.deriv.differentiableAt.hasDerivAt).comp w (hφ w)
      have h2 : HasDerivAt (fun v : ℂ => 4 - 8 * v) (-8) w := by
        simpa using ((hasDerivAt_id w).const_mul 8).const_sub 4
      refine (h1.mul h2).congr_deriv ?_
      simp only [iteratedDeriv_succ, iteratedDeriv_zero, Function.comp_apply]
    have hode := gaussOperator_ordinaryHypergeometric (a := a) (b := b) hc (hsmall w hw)
    simp only [gaussOperator] at hode ⊢
    rw [show iteratedDeriv 2 G w = deriv (deriv G) w by
      simp only [iteratedDeriv_succ, iteratedDeriv_zero], hd1.deriv_eq, hd2.deriv, hd1.eq_of_nhds]
    simp only [hG]
    rw [hcdef] at hode ⊢
    linear_combination 4 * hode
  have hsmallEq := eq_ordinaryHypergeometric_of_gaussOperator
    (a := 2 * a) (b := 2 * b) (c := c) (by
      simpa [hcdef, show 2 * a + 2 * b = 2 * (a + b) by ring] using hc)
    (by norm_num) (by norm_num) hGan hGode (by simp [hG, ordinaryHypergeometric_zero])
  -- Step 2: extend along the lobe, the image of the unit disk under the inverse map.
  set D : Set ℂ := {w | ‖w‖ < 1 ∧ ‖4 * w * (1 - w)‖ < 1 ∧ w.re < 1 / 2} with hD
  have hDc : IsPreconnected D := by
    have himg : D = (fun w : ℂ => (1 - (1 - w) ^ (1 / 2 : ℂ)) / 2) '' Metric.ball 0 1 := by
      ext z
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨4 * z * (1 - z), by simpa using h2, ?_⟩
        show (1 - (1 - 4 * z * (1 - z)) ^ (1 / 2 : ℂ)) / 2 = z
        rw [show 1 - 4 * z * (1 - z) = (1 - 2 * z) ^ 2 by ring,
          sq_cpow_half (by simp; linarith)]
        ring
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨h1, h2, h3, -⟩ := quadratic_lobe_of_mem_ball (by simpa using hw)
        exact ⟨h1, h2, h3⟩
    rw [himg]
    refine (convex_ball (0 : ℂ) 1).isPreconnected.image _ fun w hw => ?_
    have hw' : ‖w‖ < 1 := by simpa using hw
    have hslit : 1 - w ∈ slitPlane := by
      refine mem_slitPlane_iff.mpr (Or.inl ?_)
      have := (re_le_norm w).trans_lt hw'
      simp only [sub_re, one_re]
      linarith
    exact ((continuousAt_const.sub ((continuousAt_cpow_const hslit).comp
      (continuousAt_const.sub continuousAt_id))).div_const 2).continuousWithinAt
  have hLan : AnalyticOnNhd ℂ (₂F₁ (2 * a) (2 * b) c : ℂ → ℂ) D := fun w hw =>
    analyticAt_ordinaryHypergeometric hw.1
  have hRan : AnalyticOnNhd ℂ G D := fun w hw =>
    (analyticAt_ordinaryHypergeometric hw.2.1).comp (f := fun v : ℂ => 4 * v * (1 - v)) (hφa w)
  have h0D : (0 : ℂ) ∈ D := by simp [hD]
  have hev : (₂F₁ (2 * a) (2 * b) c : ℂ → ℂ) =ᶠ[𝓝 0] G := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 8)] with w hw
    exact (hsmallEq w hw).symm
  exact hLan.eqOn_of_preconnected_of_eventuallyEq hRan hDc h0D hev ⟨hz, hzt, hre⟩

/-- First derivative of `p · (F ∘ φ)` near a point, for analytic data. -/
theorem deriv_mul_comp_eventuallyEq {p φ F : ℂ → ℂ} {z : ℂ} (hp : AnalyticAt ℂ p z)
    (hφ : AnalyticAt ℂ φ z) (hF : AnalyticAt ℂ F (φ z)) :
    deriv (fun w => p w * F (φ w)) =ᶠ[𝓝 z]
      fun w => deriv p w * F (φ w) + p w * (deriv F (φ w) * deriv φ w) := by
  filter_upwards [hp.eventually_analyticAt, hφ.eventually_analyticAt,
    hφ.continuousAt.tendsto.eventually hF.eventually_analyticAt] with w h1 h2 h3
  exact (h1.differentiableAt.hasDerivAt.mul
    (h3.differentiableAt.hasDerivAt.comp w h2.differentiableAt.hasDerivAt)).deriv

/-- Second derivative of `p · (F ∘ φ)`, for analytic data. -/
theorem deriv_deriv_mul_comp {p φ F : ℂ → ℂ} {z : ℂ} (hp : AnalyticAt ℂ p z)
    (hφ : AnalyticAt ℂ φ z) (hF : AnalyticAt ℂ F (φ z)) :
    deriv (deriv (fun w => p w * F (φ w))) z =
      deriv (deriv p) z * F (φ z) + 2 * deriv p z * (deriv F (φ z) * deriv φ z) +
        p z * (iteratedDeriv 2 F (φ z) * deriv φ z ^ 2 + deriv F (φ z) * deriv (deriv φ) z) := by
  rw [(deriv_mul_comp_eventuallyEq hp hφ hF).deriv_eq]
  have hFφ := hF.differentiableAt.hasDerivAt.comp z hφ.differentiableAt.hasDerivAt
  have hF'φ := hF.deriv.differentiableAt.hasDerivAt.comp z hφ.differentiableAt.hasDerivAt
  have h := (hp.deriv.differentiableAt.hasDerivAt.mul hFφ).add
    (hp.differentiableAt.hasDerivAt.mul (hF'φ.mul hφ.deriv.differentiableAt.hasDerivAt))
  have h' : HasDerivAt (fun w => deriv p w * F (φ w) + p w * (deriv F (φ w) * deriv φ w)) _ z := h
  rw [h'.deriv]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, Function.comp_apply, Pi.mul_apply]
  ring

/-- Gauss operator of `p · (F ∘ φ)` in terms of the derivatives of `p`, `φ`, `F`. -/
theorem gaussOperator_mul_comp {a b c : ℂ} {p φ F : ℂ → ℂ} {z : ℂ} (hp : AnalyticAt ℂ p z)
    (hφ : AnalyticAt ℂ φ z) (hF : AnalyticAt ℂ F (φ z)) :
    gaussOperator a b c (fun w => p w * F (φ w)) z =
      z * (1 - z) * (deriv (deriv p) z * F (φ z) + 2 * deriv p z * (deriv F (φ z) * deriv φ z) +
        p z * (iteratedDeriv 2 F (φ z) * deriv φ z ^ 2 + deriv F (φ z) * deriv (deriv φ) z)) +
      (c - (a + b + 1) * z) * (deriv p z * F (φ z) + p z * (deriv F (φ z) * deriv φ z)) -
      a * b * (p z * F (φ z)) := by
  rw [gaussOperator, show iteratedDeriv 2 (fun w => p w * F (φ w)) z =
      deriv (deriv (fun w => p w * F (φ w))) z by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero], deriv_deriv_mul_comp hp hφ hF,
    (deriv_mul_comp_eventuallyEq hp hφ hF).eq_of_nhds]

/-- Derivatives of an affine power `w ↦ (α + β w)^s`, written through the power itself. -/
theorem deriv_affine_cpow {α β s z : ℂ} (h : α + β * z ∈ slitPlane) :
    deriv (fun w => (α + β * w) ^ s) z = s * β * (α + β * z) ^ s / (α + β * z) := by
  have h0 : α + β * z ≠ 0 := slitPlane_ne_zero h
  have hd := ((hasDerivAt_id z).const_mul β |>.const_add α).cpow_const (c := s) (by simpa using h)
  have hd' : HasDerivAt (fun w => (α + β * w) ^ s) _ z := hd
  rw [hd'.deriv]
  simp only [id, mul_one]
  rw [cpow_sub _ _ h0, cpow_one]
  ring

/-- Second derivative of `(α + βw)^s` on the slit plane: `s(s - 1)β²(α + βz)^s/(α + βz)²`. -/
theorem deriv_deriv_affine_cpow {α β s z : ℂ} (h : α + β * z ∈ slitPlane) :
    deriv (deriv (fun w => (α + β * w) ^ s)) z =
      s * (s - 1) * β ^ 2 * (α + β * z) ^ s / (α + β * z) ^ 2 := by
  have h0 : α + β * z ≠ 0 := slitPlane_ne_zero h
  have hev : deriv (fun w => (α + β * w) ^ s) =ᶠ[𝓝 z]
      fun w => s * β * (α + β * w) ^ s / (α + β * w) := by
    have hopen : IsOpen {w : ℂ | α + β * w ∈ slitPlane} :=
      isOpen_slitPlane.preimage (by fun_prop)
    filter_upwards [hopen.mem_nhds h] with w hw
    exact deriv_affine_cpow hw
  rw [hev.deriv_eq]
  have hp := ((hasDerivAt_id z).const_mul β |>.const_add α).cpow_const (c := s) (by simpa using h)
  have hq : HasDerivAt (fun w => α + β * w) β z := by
    simpa using ((hasDerivAt_id z).const_mul β).const_add α
  have hd := ((hp.const_mul (s * β)).div hq h0)
  simp only [id, mul_one] at hd
  have hd' : HasDerivAt (fun w => s * β * (α + β * w) ^ s / (α + β * w)) _ z := hd
  rw [hd'.deriv, cpow_sub _ _ h0, cpow_one]
  field_simp

/-- Kummer's quadratic transformation, AAR §3.1 (first formula). -/
@[dlmf 15.8.E18]
theorem kummer_quadratic {a b z : ℂ}
    (hc : ∀ k : ℕ, a + b + 1 / 2 ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    ₂F₁ a b (a + b + 1 / 2) z =
      ₂F₁ (2 * a) (2 * b) (a + b + 1 / 2) ((1 - (1 - z) ^ (1 / 2 : ℂ)) / 2) := by
  obtain ⟨h1, h2, h3, h4⟩ := quadratic_lobe_of_mem_ball hz
  rw [gauss_quadratic hc h1 h2 h3, h4]

@[dlmf 15.8.E13]
theorem quadratic_double_denominator
    {a b z : ℂ}
    (hc : ∀ k : ℕ, 2 * b ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, b + 1 / 2 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1) :
    ₂F₁ a b (2 * b) z =
      (1 - z / 2) ^ (-a) * ₂F₁ (a / 2) ((a + 1) / 2) (b + 1 / 2) ((z / (2 - z)) ^ 2) := by
  set H : ℂ → ℂ := ₂F₁ (a / 2) ((a + 1) / 2) (b + 1 / 2) with hH
  set P : ℂ → ℂ := fun w => (1 + (-1 / 2) * w) ^ (-a) with hP
  set φ : ℂ → ℂ := fun w => (w / (2 - w)) ^ 2 with hφdef
  have hdisk : ∀ w ∈ Metric.ball (0 : ℂ) 1, ‖w‖ < 1 := fun w hw => by simpa using hw
  have h2w : ∀ w : ℂ, ‖w‖ < 1 → 2 - w ≠ 0 := by
    intro w hw h
    have : w = 2 := by linear_combination -h
    rw [this] at hw; norm_num at hw
  have hslit : ∀ w : ℂ, ‖w‖ < 1 → 1 + (-1 / 2) * w ∈ slitPlane := by
    intro w hw
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    have := (re_le_norm w).trans_lt hw
    simp only [add_re, one_re, mul_re, div_re, neg_re, one_re, re_ofNat, im_ofNat, neg_im,
      one_im, normSq_ofNat]
    norm_num
    linarith
  have hφn : ∀ w : ℂ, ‖w‖ < 1 → ‖φ w‖ < 1 := by
    intro w hw
    have h2 : 1 < ‖2 - w‖ := by
      have := norm_sub_norm_le (2 : ℂ) w
      rw [show ‖(2 : ℂ)‖ = 2 by norm_num] at this
      linarith
    simp only [hφdef, norm_pow, norm_div]
    have : ‖w‖ / ‖2 - w‖ < 1 := by rw [div_lt_one (by linarith)]; linarith
    have h0 : 0 ≤ ‖w‖ / ‖2 - w‖ := by positivity
    nlinarith
  have hPa : ∀ w : ℂ, ‖w‖ < 1 → AnalyticAt ℂ P w := fun w hw =>
    (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).cpow analyticAt_const (hslit w hw)
  have hφa : ∀ w : ℂ, ‖w‖ < 1 → AnalyticAt ℂ φ w := fun w hw =>
    (analyticAt_id.div (analyticAt_const.sub analyticAt_id) (h2w w hw)).pow 2
  have hHa : ∀ w : ℂ, ‖w‖ < 1 → AnalyticAt ℂ H (φ w) := fun w hw =>
    analyticAt_ordinaryHypergeometric (hφn w hw)
  have hφd : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt φ (4 * w / (2 - w) ^ 3) w := by
    intro w hw
    have h := ((hasDerivAt_id w).div ((hasDerivAt_const w (2 : ℂ)).sub (hasDerivAt_id w))
      (h2w w hw)).pow 2
    refine h.congr_deriv ?_
    have := h2w w hw
    simp only [id, Pi.div_apply, Pi.sub_apply, Nat.cast_ofNat,
      show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    field_simp
    ring
  have hφdd : ∀ w : ℂ, ‖w‖ < 1 → deriv (deriv φ) w = 8 * (1 + w) / (2 - w) ^ 4 := by
    intro w hw
    have hev : deriv φ =ᶠ[𝓝 w] fun v => 4 * v / (2 - v) ^ 3 := by
      have hopen : IsOpen {v : ℂ | ‖v‖ < 1} := isOpen_lt continuous_norm continuous_const
      filter_upwards [hopen.mem_nhds hw] with v hv
      exact (hφd v hv).deriv
    rw [hev.deriv_eq]
    have h := ((hasDerivAt_id w).const_mul 4).div
      (((hasDerivAt_const w (2 : ℂ)).sub (hasDerivAt_id w)).pow 3) (pow_ne_zero 3 (h2w w hw))
    have h' : HasDerivAt (fun v => 4 * v / (2 - v) ^ 3) _ w := h
    rw [h'.deriv]
    have := h2w w hw
    simp only [id, Pi.sub_apply, Pi.pow_apply]
    field_simp
    ring
  have hG : ∀ w ∈ Metric.ball (0 : ℂ) 1, (fun v => P v * H (φ v)) w = ₂F₁ a b (2 * b) w := by
    refine eq_ordinaryHypergeometric_of_gaussOperator hc (by norm_num) le_rfl ?_ ?_ ?_
    · intro w hw
      exact (hPa w (hdisk w hw)).mul ((hHa w (hdisk w hw)).comp (f := φ) (hφa w (hdisk w hw)))
    · intro w hw
      have hw1 := hdisk w hw
      rw [gaussOperator_mul_comp (hPa w hw1) (hφa w hw1) (hHa w hw1),
        show deriv P w = _ from deriv_affine_cpow (hslit w hw1),
        show deriv (deriv P) w = _ from deriv_deriv_affine_cpow (hslit w hw1),
        (hφd w hw1).deriv, hφdd w hw1]
      have hode := gaussOperator_ordinaryHypergeometric (a := a / 2) (b := (a + 1) / 2) ht
        (hφn w hw1)
      simp only [gaussOperator] at hode
      have h2 := h2w w hw1
      have h1 : 1 + (-1 / 2) * w ≠ 0 := slitPlane_ne_zero (hslit w hw1)
      have key : w * (1 - w) * (-a * (-a - 1) * (-1 / 2) ^ 2 * (1 + -1 / 2 * w) ^ (-a) /
            (1 + -1 / 2 * w) ^ 2 * H (φ w) +
          2 * (-a * (-1 / 2) * (1 + -1 / 2 * w) ^ (-a) / (1 + -1 / 2 * w)) *
            (deriv H (φ w) * (4 * w / (2 - w) ^ 3)) +
          P w * (iteratedDeriv 2 H (φ w) * (4 * w / (2 - w) ^ 3) ^ 2 +
            deriv H (φ w) * (8 * (1 + w) / (2 - w) ^ 4))) +
          (2 * b - (a + b + 1) * w) * (-a * (-1 / 2) * (1 + -1 / 2 * w) ^ (-a) /
            (1 + -1 / 2 * w) * H (φ w) + P w * (deriv H (φ w) * (4 * w / (2 - w) ^ 3))) -
          a * b * (P w * H (φ w)) =
          P w * 4 * w / (2 - w) ^ 2 *
            (φ w * (1 - φ w) * iteratedDeriv 2 H (φ w) +
              (b + 1 / 2 - (a / 2 + (a + 1) / 2 + 1) * φ w) * deriv H (φ w) -
              a / 2 * ((a + 1) / 2) * H (φ w)) := by
        simp only [hP]
        generalize H (φ w) = h0
        generalize deriv H (φ w) = h1
        generalize iteratedDeriv 2 H (φ w) = h2
        generalize (1 + -1 / 2 * w) ^ (-a) = pw
        rw [show (1 : ℂ) + -1 / 2 * w = (2 - w) / 2 by ring]
        simp only [hφdef]
        field_simp
        ring
      rw [key, hode, mul_zero]
    · simp [hP, hφdef, hH, ordinaryHypergeometric_zero]
  have := hG z (by simpa using hz)
  simp only [hP, hφdef, hH] at this
  rw [← this, show (1 : ℂ) - z / 2 = 1 + -1 / 2 * z by ring]

/-- Sign bookkeeping for `arg`: if `0 < re w` then `|arg w| < π/2`, and the sign of `arg`
follows the sign of the imaginary part. -/
theorem arg_le_zero_of_im_nonpos {w : ℂ} (hre : 0 < w.re) (him : w.im ≤ 0) : w.arg ≤ 0 := by
  rcases him.lt_or_eq with h | h
  · exact (arg_neg_iff.mpr h).le
  · exact (arg_eq_zero_iff.mpr ⟨hre.le, h⟩).le

/-- For `‖z‖ < 1`, `(1 - z/2)^{-a} (1 - (z/(2 - z))²)^{-a/2} = (1 - z)^{-a/2}`. -/
theorem phase_double_denominator {a z : ℂ} (hz : ‖z‖ < 1) :
    (1 - z / 2) ^ (-a) * (1 - (z / (2 - z)) ^ 2) ^ (-(a / 2)) = (1 - z) ^ (-a / 2) := by
  have hre1 : 0 < (1 - z).re := by
    have := (re_le_norm z).trans_lt hz
    simp only [sub_re, one_re]; linarith
  have hre2 : 0 < (1 - z / 2).re := by
    have := (re_le_norm z).trans_lt hz
    simp only [sub_re, one_re, div_re, re_ofNat, im_ofNat, normSq_ofNat]
    norm_num; linarith
  have hu : 1 - z ≠ 0 := by intro h; rw [h] at hre1; simp at hre1
  have hv : 1 - z / 2 ≠ 0 := by intro h; rw [h] at hre2; simp at hre2
  have h2z : 2 - z ≠ 0 := by
    intro h; apply hv; linear_combination h / 2
  have harg1 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre1)
  have harg2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre2)
  have hsame : ((1 - z).arg ≤ 0 ∧ (1 - z / 2).arg ≤ 0) ∨
      (0 ≤ (1 - z).arg ∧ 0 ≤ (1 - z / 2).arg) := by
    rcases le_total z.im 0 with h | h
    · right
      exact ⟨arg_nonneg_iff.mpr (by simp; linarith),
        arg_nonneg_iff.mpr (by simp; linarith)⟩
    · left
      exact ⟨arg_le_zero_of_im_nonpos hre1 (by simp; linarith),
        arg_le_zero_of_im_nonpos hre2 (by simp; linarith)⟩
  have hexp : exp (log (1 - z) - 2 * log (1 - z / 2)) = 1 - (z / (2 - z)) ^ 2 := by
    rw [exp_sub, show (2 : ℂ) * log (1 - z / 2) = ((2 : ℕ) : ℂ) * log (1 - z / 2) by norm_num,
      exp_nat_mul, exp_log hu, exp_log hv]
    field_simp
    ring
  have him : (log (1 - z) - 2 * log (1 - z / 2)).im = (1 - z).arg - 2 * (1 - z / 2).arg := by
    simp [log_im]
  have hb := abs_lt.mp harg1
  have hc := abs_lt.mp harg2
  rw [cpow_eq_exp_of_exp_eq hexp (by rw [him]; rcases hsame with h | h <;> nlinarith)
      (by rw [him]; rcases hsame with h | h <;> nlinarith),
    cpow_def_of_ne_zero hv, cpow_def_of_ne_zero hu, ← exp_add]
  congr 1
  ring

@[dlmf 15.8.E14]
theorem quadratic_double_denominator_one_sub
    {a b z : ℂ}
    (hc : ∀ k : ℕ, 2 * b ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, b + 1 / 2 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hw : ‖z ^ 2 /
    (4 * z - 4)‖ < 1) :
    ₂F₁ a b (2 * b) z =
      (1 - z) ^ (-a / 2) * ₂F₁ (a / 2) (b - a / 2) (b + 1 / 2) (z ^ 2 / (4 * z - 4)) := by
  have h1z : z ≠ 1 := by rintro rfl; simp at hz
  have h2z : 2 - z ≠ 0 := by
    intro h; have : z = 2 := by linear_combination -h
    rw [this] at hz; norm_num at hz
  have hy : ‖(z / (2 - z)) ^ 2‖ < 1 := by
    have h2 : 1 < ‖2 - z‖ := by
      have := norm_sub_norm_le (2 : ℂ) z
      rw [show ‖(2 : ℂ)‖ = 2 by norm_num] at this
      linarith
    rw [norm_pow, norm_div]
    have : ‖z‖ / ‖2 - z‖ < 1 := by rw [div_lt_one (by linarith)]; linarith
    have h0 : 0 ≤ ‖z‖ / ‖2 - z‖ := by positivity
    nlinarith
  have hyy : (z / (2 - z)) ^ 2 / ((z / (2 - z)) ^ 2 - 1) = z ^ 2 / (4 * z - 4) := by
    have : z - 1 ≠ 0 := sub_ne_zero.mpr h1z
    have h4 : 4 * z - 4 ≠ 0 := by
      intro h; apply this; linear_combination h / 4
    have hden : (z / (2 - z)) ^ 2 - 1 = (4 * z - 4) / (2 - z) ^ 2 := by
      field_simp
      ring
    rw [hden]
    field_simp
  rw [quadratic_double_denominator hc ht hz, pfaff_transformation_of_ne_neg_nat ht hy
    (by rwa [hyy]), hyy, show b + 1 / 2 - (a + 1) / 2 = b - a / 2 by ring, ← mul_assoc,
    phase_double_denominator hz]

/-- `0 < Re((1-z)/(1+z))` on the unit disk. -/
theorem re_one_sub_div_one_add_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < ((1 - z) / (1 + z)).re := by
  have h1z : 1 + z ≠ 0 := by
    intro h; have : z = -1 := by linear_combination h
    rw [this] at hz; simp at hz
  have hn : normSq z < 1 := by
    rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  rw [div_re]
  have hpos : 0 < normSq (1 + z) := normSq_pos.mpr h1z
  have : ((1 - z).re * (1 + z).re + (1 - z).im * (1 + z).im) = 1 - normSq z := by
    simp [normSq_apply]; ring
  rw [← add_div, this]
  exact div_pos (by linarith) hpos

/-- The well-poised quadratic domain is the image of the unit disk under an inverse map. -/
theorem isPreconnected_wellPoised :
    IsPreconnected {z : ℂ | ‖z‖ < 1 ∧ ‖4 * z / (1 + z) ^ 2‖ < 1} := by
  have himg : {z : ℂ | ‖z‖ < 1 ∧ ‖4 * z / (1 + z) ^ 2‖ < 1} =
      (fun w : ℂ => (1 - (1 - w) ^ (1 / 2 : ℂ)) / (1 + (1 - w) ^ (1 / 2 : ℂ))) ''
        Metric.ball 0 1 := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      have h1z : 1 + z ≠ 0 := by
        intro h; have : z = -1 := by linear_combination h
        rw [this] at h1; simp at h1
      refine ⟨4 * z / (1 + z) ^ 2, by simpa using h2, ?_⟩
      show (1 - (1 - 4 * z / (1 + z) ^ 2) ^ (1 / 2 : ℂ)) /
        (1 + (1 - 4 * z / (1 + z) ^ 2) ^ (1 / 2 : ℂ)) = z
      rw [show 1 - 4 * z / (1 + z) ^ 2 = ((1 - z) / (1 + z)) ^ 2 by field_simp; ring,
        sq_cpow_half (re_one_sub_div_one_add_pos h1)]
      field_simp
      ring
    · rintro ⟨w, hw, rfl⟩
      have hw' : ‖w‖ < 1 := by simpa using hw
      have hre1 : 0 < (1 - w).re := by
        have := (re_le_norm w).trans_lt hw'
        simp only [sub_re, one_re]; linarith
      have h1w : 1 - w ≠ 0 := by intro h; rw [h] at hre1; simp at hre1
      set t := (1 - w) ^ (1 / 2 : ℂ) with ht
      have htre : 0 < t.re := re_cpow_half_pos hre1
      have ht1 : 1 + t ≠ 0 := by
        intro h; have := congrArg re h; simp at this; linarith
      have htsq : t ^ 2 = 1 - w := cpow_half_sq h1w
      refine ⟨?_, ?_⟩
      · rw [norm_div, div_lt_one (norm_pos_iff.mpr ht1)]
        have e1 : ‖1 - t‖ ^ 2 < ‖1 + t‖ ^ 2 := by
          rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_apply, normSq_apply]
          simp only [sub_re, one_re, sub_im, one_im, add_re, add_im]
          nlinarith
        nlinarith [norm_nonneg (1 - t), norm_nonneg (1 + t)]
      · have : 4 * ((1 - t) / (1 + t)) / (1 + (1 - t) / (1 + t)) ^ 2 = w := by
          field_simp
          linear_combination (-4 : ℂ) * htsq
        rw [this]; exact hw'
  rw [himg]
  refine (convex_ball (0 : ℂ) 1).isPreconnected.image _ fun w hw => ?_
  have hw' : ‖w‖ < 1 := by simpa using hw
  have hre1 : 0 < (1 - w).re := by
    have := (re_le_norm w).trans_lt hw'
    simp only [sub_re, one_re]; linarith
  have hslit : 1 - w ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hre1)
  have hcont : ContinuousAt (fun w : ℂ => (1 - w) ^ (1 / 2 : ℂ)) w :=
    (continuousAt_cpow_const hslit).comp (continuousAt_const.sub continuousAt_id)
  have hne : 1 + (1 - w) ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h; have := congrArg re h
    have := re_cpow_half_pos hre1
    simp at *; linarith
  exact ((continuousAt_const.sub hcont).div (continuousAt_const.add hcont) hne).continuousWithinAt

@[dlmf 15.8.E15]
theorem quadratic_well_poised_plus
    {a b z : ℂ}
    (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hw : ‖4 * z /
    (1 + z) ^ 2‖ < 1) :
    ₂F₁ a b (a - b + 1) z =
      (1 + z) ^ (-a) * ₂F₁ (a / 2) ((a + 1) / 2) (a - b + 1) (4 * z / (1 + z) ^ 2) := by
  set H : ℂ → ℂ := ₂F₁ (a / 2) ((a + 1) / 2) (a - b + 1) with hH
  set P : ℂ → ℂ := fun w => (1 + 1 * w) ^ (-a) with hP
  set ψ : ℂ → ℂ := fun w => 4 * w / (1 + w) ^ 2 with hψdef
  have h1w : ∀ w : ℂ, ‖w‖ < 1 → 1 + w ≠ 0 := by
    intro w hw h; have : w = -1 := by linear_combination h
    rw [this] at hw; simp at hw
  have hslit : ∀ w : ℂ, ‖w‖ < 1 → 1 + 1 * w ∈ slitPlane := by
    intro w hw
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    have := neg_le_of_abs_le (abs_re_le_norm w)
    simp only [add_re, one_re, one_mul]; linarith
  have hPa : ∀ w : ℂ, ‖w‖ < 1 → AnalyticAt ℂ P w := fun w hw =>
    (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).cpow analyticAt_const (hslit w hw)
  have hψa : ∀ w : ℂ, ‖w‖ < 1 → AnalyticAt ℂ ψ w := fun w hw =>
    (analyticAt_const.mul analyticAt_id).div ((analyticAt_const.add analyticAt_id).pow 2)
      (pow_ne_zero 2 (h1w w hw))
  have hψd : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt ψ (4 * (1 - w) / (1 + w) ^ 3) w := by
    intro w hw
    have h := ((hasDerivAt_id w).const_mul 4).div
      (((hasDerivAt_const w (1 : ℂ)).add (hasDerivAt_id w)).pow 2) (pow_ne_zero 2 (h1w w hw))
    refine h.congr_deriv ?_
    have := h1w w hw
    simp only [id, Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl,
      pow_one]
    field_simp
    ring
  have hψdd : ∀ w : ℂ, ‖w‖ < 1 → deriv (deriv ψ) w = 8 * (w - 2) / (1 + w) ^ 4 := by
    intro w hw
    have hev : deriv ψ =ᶠ[𝓝 w] fun v => 4 * (1 - v) / (1 + v) ^ 3 := by
      have hopen : IsOpen {v : ℂ | ‖v‖ < 1} := isOpen_lt continuous_norm continuous_const
      filter_upwards [hopen.mem_nhds hw] with v hv
      exact (hψd v hv).deriv
    rw [hev.deriv_eq]
    have h := (((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w)).const_mul 4).div
      (((hasDerivAt_const w (1 : ℂ)).add (hasDerivAt_id w)).pow 3) (pow_ne_zero 3 (h1w w hw))
    have h' : HasDerivAt (fun v => 4 * (1 - v) / (1 + v) ^ 3) _ w := h
    rw [h'.deriv]
    have := h1w w hw
    simp only [id, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat]
    field_simp
    ring
  have hψs : ∀ w : ℂ, ‖w‖ < 1 / 8 → ‖ψ w‖ < 1 := by
    intro w hw
    have h1 : 7 / 8 < ‖1 + w‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-w)
      rw [norm_one, norm_neg, sub_neg_eq_add] at this
      linarith
    simp only [hψdef, norm_div, norm_mul, norm_pow, show ‖(4 : ℂ)‖ = 4 by norm_num]
    rw [div_lt_one (by positivity)]
    nlinarith [norm_nonneg w]
  have hball : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 8), (fun v => P v * H (ψ v)) w =
      ₂F₁ a b (a - b + 1) w := by
    have hb : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 8), ‖w‖ < 1 / 8 := fun w hw => by simpa using hw
    refine eq_ordinaryHypergeometric_of_gaussOperator hc (by norm_num) (by norm_num) ?_ ?_ ?_
    · intro w hw
      have h1 : ‖w‖ < 1 := by linarith [hb w hw]
      exact (hPa w h1).mul ((analyticAt_ordinaryHypergeometric (hψs w (hb w hw))).comp
        (f := ψ) (hψa w h1))
    · intro w hw
      have h8 := hb w hw
      have h1 : ‖w‖ < 1 := by linarith
      rw [gaussOperator_mul_comp (hPa w h1) (hψa w h1)
          (analyticAt_ordinaryHypergeometric (hψs w h8)),
        show deriv P w = _ from deriv_affine_cpow (hslit w h1),
        show deriv (deriv P) w = _ from deriv_deriv_affine_cpow (hslit w h1),
        (hψd w h1).deriv, hψdd w h1]
      have hode := gaussOperator_ordinaryHypergeometric (a := a / 2) (b := (a + 1) / 2) hc (hψs w h8)
      simp only [gaussOperator] at hode
      have hw1 := h1w w h1
      have key : w * (1 - w) * (-a * (-a - 1) * 1 ^ 2 * (1 + 1 * w) ^ (-a) / (1 + 1 * w) ^ 2 *
            H (ψ w) + 2 * (-a * 1 * (1 + 1 * w) ^ (-a) / (1 + 1 * w)) *
            (deriv H (ψ w) * (4 * (1 - w) / (1 + w) ^ 3)) +
          P w * (iteratedDeriv 2 H (ψ w) * (4 * (1 - w) / (1 + w) ^ 3) ^ 2 +
            deriv H (ψ w) * (8 * (w - 2) / (1 + w) ^ 4))) +
          (a - b + 1 - (a + b + 1) * w) * (-a * 1 * (1 + 1 * w) ^ (-a) / (1 + 1 * w) * H (ψ w) +
            P w * (deriv H (ψ w) * (4 * (1 - w) / (1 + w) ^ 3))) -
          a * b * (P w * H (ψ w)) =
          P w * 4 * (1 - w) / (1 + w) ^ 2 *
            (ψ w * (1 - ψ w) * iteratedDeriv 2 H (ψ w) +
              (a - b + 1 - (a / 2 + (a + 1) / 2 + 1) * ψ w) * deriv H (ψ w) -
              a / 2 * ((a + 1) / 2) * H (ψ w)) := by
        simp only [hP]
        generalize H (ψ w) = h0
        generalize deriv H (ψ w) = h1
        generalize iteratedDeriv 2 H (ψ w) = h2
        generalize (1 + 1 * w) ^ (-a) = pw
        rw [show (1 : ℂ) + 1 * w = 1 + w by ring]
        simp only [hψdef]
        field_simp
        ring
      rw [key, hode, mul_zero]
    · simp [hP, hψdef, hH, ordinaryHypergeometric_zero]
  -- Continuation over the connected domain.
  set D : Set ℂ := {z : ℂ | ‖z‖ < 1 ∧ ‖4 * z / (1 + z) ^ 2‖ < 1} with hD
  have hLan : AnalyticOnNhd ℂ (₂F₁ a b (a - b + 1) : ℂ → ℂ) D := fun w hw =>
    analyticAt_ordinaryHypergeometric hw.1
  have hRan : AnalyticOnNhd ℂ (fun v => P v * H (ψ v)) D := fun w hw =>
    (hPa w hw.1).mul ((analyticAt_ordinaryHypergeometric hw.2).comp (f := ψ) (hψa w hw.1))
  have hev : (₂F₁ a b (a - b + 1) : ℂ → ℂ) =ᶠ[𝓝 0] fun v => P v * H (ψ v) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 8)] with w hw
    exact (hball w hw).symm
  have := hLan.eqOn_of_preconnected_of_eventuallyEq hRan isPreconnected_wellPoised
    (by simp [hD]) hev ⟨hz, hw⟩
  rw [this]
  simp only [hP, hψdef, hH, one_mul]

@[dlmf 15.8.E16]
theorem quadratic_well_poised_minus
    {a b z : ℂ}
    (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hw : ‖-4 * z /
    (1 - z) ^ 2‖ < 1) :
    ₂F₁ a b (a - b + 1) z =
      (1 - z) ^ (-a) * ₂F₁ (a / 2) (a / 2 - b + 1 / 2) (a - b + 1) (-4 * z / (1 - z) ^ 2) := by
  set H : ℂ → ℂ := ₂F₁ (a / 2) (a / 2 - b + 1 / 2) (a - b + 1) with hH
  set P : ℂ → ℂ := fun w => (1 + (-1) * w) ^ (-a) with hP
  set χ : ℂ → ℂ := fun w => -4 * w / (1 - w) ^ 2 with hχdef
  have h1w : ∀ w : ℂ, ‖w‖ < 1 → 1 - w ≠ 0 := by
    intro w hw h; have : w = 1 := by linear_combination -h
    rw [this] at hw; simp at hw
  have hslit : ∀ w : ℂ, ‖w‖ < 1 → 1 + (-1) * w ∈ slitPlane := by
    intro w hw
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    have := (re_le_norm w).trans_lt hw
    simp only [add_re, one_re, mul_re, neg_re, one_re, neg_im, one_im]; linarith
  have hPa : ∀ w : ℂ, ‖w‖ < 1 → AnalyticAt ℂ P w := fun w hw =>
    (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).cpow analyticAt_const (hslit w hw)
  have hχa : ∀ w : ℂ, ‖w‖ < 1 → AnalyticAt ℂ χ w := fun w hw =>
    (analyticAt_const.mul analyticAt_id).div ((analyticAt_const.sub analyticAt_id).pow 2)
      (pow_ne_zero 2 (h1w w hw))
  have hχd : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt χ (-4 * (1 + w) / (1 - w) ^ 3) w := by
    intro w hw
    have h := ((hasDerivAt_id w).const_mul (-4)).div
      (((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w)).pow 2) (pow_ne_zero 2 (h1w w hw))
    refine h.congr_deriv ?_
    have := h1w w hw
    simp only [id, Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl,
      pow_one]
    field_simp
    ring
  have hχdd : ∀ w : ℂ, ‖w‖ < 1 → deriv (deriv χ) w = -8 * (2 + w) / (1 - w) ^ 4 := by
    intro w hw
    have hev : deriv χ =ᶠ[𝓝 w] fun v => -4 * (1 + v) / (1 - v) ^ 3 := by
      have hopen : IsOpen {v : ℂ | ‖v‖ < 1} := isOpen_lt continuous_norm continuous_const
      filter_upwards [hopen.mem_nhds hw] with v hv
      exact (hχd v hv).deriv
    rw [hev.deriv_eq]
    have h := (((hasDerivAt_const w (1 : ℂ)).add (hasDerivAt_id w)).const_mul (-4)).div
      (((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w)).pow 3) (pow_ne_zero 3 (h1w w hw))
    have h' : HasDerivAt (fun v => -4 * (1 + v) / (1 - v) ^ 3) _ w := h
    rw [h'.deriv]
    have := h1w w hw
    simp only [id, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat]
    field_simp
    ring
  have hχs : ∀ w : ℂ, ‖w‖ < 1 / 8 → ‖χ w‖ < 1 := by
    intro w hw
    have h1 : 7 / 8 < ‖1 - w‖ := by
      have := norm_sub_norm_le (1 : ℂ) w
      rw [norm_one] at this
      linarith
    simp only [hχdef, norm_div, norm_mul, norm_pow, show ‖(-4 : ℂ)‖ = 4 by norm_num]
    rw [div_lt_one (by positivity)]
    nlinarith [norm_nonneg w]
  have hball : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 8), (fun v => P v * H (χ v)) w =
      ₂F₁ a b (a - b + 1) w := by
    have hb : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 8), ‖w‖ < 1 / 8 := fun w hw => by simpa using hw
    refine eq_ordinaryHypergeometric_of_gaussOperator hc (by norm_num) (by norm_num) ?_ ?_ ?_
    · intro w hw
      have h1 : ‖w‖ < 1 := by linarith [hb w hw]
      exact (hPa w h1).mul ((analyticAt_ordinaryHypergeometric (hχs w (hb w hw))).comp
        (f := χ) (hχa w h1))
    · intro w hw
      have h8 := hb w hw
      have h1 : ‖w‖ < 1 := by linarith
      rw [gaussOperator_mul_comp (hPa w h1) (hχa w h1)
          (analyticAt_ordinaryHypergeometric (hχs w h8)),
        show deriv P w = _ from deriv_affine_cpow (hslit w h1),
        show deriv (deriv P) w = _ from deriv_deriv_affine_cpow (hslit w h1),
        (hχd w h1).deriv, hχdd w h1]
      have hode := gaussOperator_ordinaryHypergeometric (a := a / 2) (b := a / 2 - b + 1 / 2) hc
        (hχs w h8)
      simp only [gaussOperator] at hode
      have hw1 := h1w w h1
      have key : w * (1 - w) * (-a * (-a - 1) * (-1) ^ 2 * (1 + -1 * w) ^ (-a) /
            (1 + -1 * w) ^ 2 * H (χ w) + 2 * (-a * -1 * (1 + -1 * w) ^ (-a) / (1 + -1 * w)) *
            (deriv H (χ w) * (-4 * (1 + w) / (1 - w) ^ 3)) +
          P w * (iteratedDeriv 2 H (χ w) * (-4 * (1 + w) / (1 - w) ^ 3) ^ 2 +
            deriv H (χ w) * (-8 * (2 + w) / (1 - w) ^ 4))) +
          (a - b + 1 - (a + b + 1) * w) * (-a * -1 * (1 + -1 * w) ^ (-a) / (1 + -1 * w) * H (χ w) +
            P w * (deriv H (χ w) * (-4 * (1 + w) / (1 - w) ^ 3))) -
          a * b * (P w * H (χ w)) =
          -4 * P w / (1 - w) *
            (χ w * (1 - χ w) * iteratedDeriv 2 H (χ w) +
              (a - b + 1 - (a / 2 + (a / 2 - b + 1 / 2) + 1) * χ w) * deriv H (χ w) -
              a / 2 * (a / 2 - b + 1 / 2) * H (χ w)) := by
        simp only [hP]
        generalize H (χ w) = h0
        generalize deriv H (χ w) = h1
        generalize iteratedDeriv 2 H (χ w) = h2
        generalize (1 + -1 * w) ^ (-a) = pw
        rw [show (1 : ℂ) + -1 * w = 1 - w by ring]
        simp only [hχdef]
        field_simp
        ring
      rw [key, hode, mul_zero]
    · simp [hP, hχdef, hH, ordinaryHypergeometric_zero]
  -- Continuation over the connected domain, the reflection of the well-poised one.
  set D : Set ℂ := {z : ℂ | ‖z‖ < 1 ∧ ‖-4 * z / (1 - z) ^ 2‖ < 1} with hD
  have hDc : IsPreconnected D := by
    have : D = (fun z : ℂ => -z) '' {z : ℂ | ‖z‖ < 1 ∧ ‖4 * z / (1 + z) ^ 2‖ < 1} := by
      ext z
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨-z, ⟨by simpa using h1, ?_⟩, by simp⟩
        rw [show 4 * -z / (1 + -z) ^ 2 = -4 * z / (1 - z) ^ 2 by ring]
        exact h2
      · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
        refine ⟨by simpa using h1, ?_⟩
        rw [show -4 * -w / (1 - -w) ^ 2 = 4 * w / (1 + w) ^ 2 by ring]
        exact h2
    rw [this]
    exact isPreconnected_wellPoised.image _ continuous_neg.continuousOn
  have hLan : AnalyticOnNhd ℂ (₂F₁ a b (a - b + 1) : ℂ → ℂ) D := fun w hw =>
    analyticAt_ordinaryHypergeometric hw.1
  have hRan : AnalyticOnNhd ℂ (fun v => P v * H (χ v)) D := fun w hw =>
    (hPa w hw.1).mul ((analyticAt_ordinaryHypergeometric hw.2).comp (f := χ) (hχa w hw.1))
  have hev : (₂F₁ a b (a - b + 1) : ℂ → ℂ) =ᶠ[𝓝 0] fun v => P v * H (χ v) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 8)] with w hw
    exact (hball w hw).symm
  have := hLan.eqOn_of_preconnected_of_eventuallyEq hRan hDc (by simp [hD]) hev ⟨hz, hw⟩
  rw [this]
  simp only [hP, hχdef, hH, neg_one_mul, ← sub_eq_add_neg]

/-- Principal powers of a square in the right half-plane. -/
theorem sq_cpow {x : ℂ} (hx : 0 < x.re) (y : ℂ) : (x ^ 2) ^ y = x ^ (2 * y) := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have harg : |x.arg| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  have hsq : x ^ 2 = exp (2 * log x) := by
    rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, exp_nat_mul, exp_log hx0]
  have hlog : log (x ^ 2) = 2 * log x := by
    rw [hsq, log_exp]
    · simp only [mul_im, log_im, re_ofNat, im_ofNat, zero_mul, add_zero]
      linarith [(abs_lt.mp harg).1]
    · simp only [mul_im, log_im, re_ofNat, im_ofNat, zero_mul, add_zero]
      linarith [(abs_lt.mp harg).2]
  rw [cpow_def_of_ne_zero (pow_ne_zero 2 hx0), hlog, cpow_def_of_ne_zero hx0]
  ring_nf

/-- `‖1 - 1/s‖ < 1` exactly when `Re s > 1/2`. -/
theorem norm_one_sub_recip_lt_one_iff {s : ℂ} (hs : s ≠ 0) : ‖1 - 1 / s‖ < 1 ↔ 1 / 2 < s.re := by
  rw [show 1 - 1 / s = (s - 1) / s by field_simp, norm_div, div_lt_one (norm_pos_iff.mpr hs),
    ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq, ← normSq_eq_norm_sq,
    normSq_apply, normSq_apply]
  simp only [sub_re, one_re, sub_im, one_im, sub_zero]
  constructor <;> intro h <;> nlinarith

/-- The half-sum quadratic domain is star-shaped about the origin. -/
theorem isPreconnected_halfSum :
    IsPreconnected {z : ℂ | ‖z‖ < 1 ∧ z.re < 1 / 2 ∧ ‖4 * z * (z - 1) / (1 - 2 * z) ^ 2‖ < 1} := by
  have hv : ∀ z : ℂ, 1 - 2 * z ≠ 0 →
      4 * z * (z - 1) / (1 - 2 * z) ^ 2 = 1 - 1 / (1 - 2 * z) ^ 2 := by
    intro z hz
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hz)]
    ring
  have hstar : StarConvex ℝ 0
      {z : ℂ | ‖z‖ < 1 ∧ z.re < 1 / 2 ∧ ‖4 * z * (z - 1) / (1 - 2 * z) ^ 2‖ < 1} := by
    intro z ⟨h1, h2, h3⟩ t u ht hu htu
    have hu' : u = 1 - t := by linarith
    subst hu'
    simp only [smul_zero, zero_add, real_smul]
    have hre0 : 0 < (1 - 2 * z).re := by simp; linarith
    have hz0 : 1 - 2 * z ≠ 0 := by intro h; rw [h] at hre0; simp at hre0
    have e0 : (1 - 2 * ((1 - t : ℝ) : ℂ) * z).re = 1 - 2 * (1 - t) * z.re := by
      simp [mul_re]
    have hre0' : 0 < (1 - 2 * ((1 - t : ℝ) : ℂ) * z).re := by
      rw [e0]
      rcases le_or_gt z.re 0 with h | h <;> nlinarith
    have hz0' : 1 - 2 * ((1 - t : ℝ) : ℂ) * z ≠ 0 := by
      intro h; rw [h] at hre0'; simp at hre0'
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      nlinarith [norm_nonneg z]
    · simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
      rcases le_or_gt z.re 0 with h | h
      · nlinarith
      · nlinarith
    · rw [show 4 * (((1 - t : ℝ) : ℂ) * z) * (((1 - t : ℝ) : ℂ) * z - 1) /
          (1 - 2 * (((1 - t : ℝ) : ℂ) * z)) ^ 2 =
          1 - 1 / (1 - 2 * ((1 - t : ℝ) : ℂ) * z) ^ 2 by
            rw [hv _ (by rwa [← mul_assoc]), ← mul_assoc]]
      rw [hv z hz0, norm_one_sub_recip_lt_one_iff (pow_ne_zero 2 hz0)] at h3
      rw [norm_one_sub_recip_lt_one_iff (pow_ne_zero 2 hz0')]
      have hsq : (1 - 2 * z) ^ 2 = (1 - 2 * z) * (1 - 2 * z) := sq _
      have hR : 1 / 2 < (1 - 2 * z).re ^ 2 - (1 - 2 * z).im ^ 2 := by
        rw [hsq, mul_re] at h3; nlinarith
      have hx0 : 1 / 2 < (1 - 2 * z).re := by nlinarith
      have e : 1 - 2 * ((1 - t : ℝ) : ℂ) * z = (t : ℂ) + ((1 - t : ℝ) : ℂ) * (1 - 2 * z) := by
        push_cast; ring
      rw [e, sq, mul_re]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero, add_im, mul_im,
        zero_add, add_zero]
      have hpos : 0 < t ^ 2 / 2 + (1 - t) ^ 2 * ((1 - 2 * z).re ^ 2 - (1 - 2 * z).im ^ 2 - 1 / 2) := by
        rcases eq_or_lt_of_le ht with h | h
        · subst h; simp at hR ⊢; linarith
        · have : 0 < t ^ 2 / 2 := by positivity
          nlinarith [sq_nonneg (1 - t)]
      nlinarith [mul_nonneg (mul_nonneg ht hu) (le_of_lt (sub_pos.mpr hx0))]
  exact (hstar.isPathConnected ⟨by simp, by simp, by simp⟩).isConnected.isPreconnected

@[dlmf 15.8.E17]
theorem quadratic_half_sum
    {a b z : ℂ}
    (hc : ∀ k : ℕ,
    (a + b + 1) / 2 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hr : z.re < 1 / 2)
    (hw : ‖4 * z *
    (z - 1) /
    (1 - 2 * z) ^ 2‖ < 1) :
    ₂F₁ a b ((a + b + 1) / 2) z =
      (1 - 2 * z) ^ (-a) * ₂F₁ (a / 2) ((a + 1) / 2) ((a + b + 1) / 2) (4 * z * (z - 1) / (1 - 2 * z) ^ 2) := by
  set C := (a + b + 1) / 2 with hC
  set H : ℂ → ℂ := ₂F₁ (a / 2) ((a + 1) / 2) C with hH
  set v : ℂ → ℂ := fun w => 4 * w * (w - 1) / (1 - 2 * w) ^ 2 with hvdef
  have hre : ∀ w : ℂ, w.re < 1 / 2 → 0 < (1 - 2 * w).re := fun w hw => by simp; linarith
  have hne : ∀ w : ℂ, w.re < 1 / 2 → 1 - 2 * w ≠ 0 := fun w hw h => by
    have := hre w hw; rw [h] at this; simp at this
  have hslit : ∀ w : ℂ, w.re < 1 / 2 → 1 - 2 * w ∈ slitPlane := fun w hw =>
    mem_slitPlane_iff.mpr (Or.inl (hre w hw))
  have hva : ∀ w : ℂ, w.re < 1 / 2 → AnalyticAt ℂ v w := fun w hw =>
    ((analyticAt_const.mul analyticAt_id).mul (analyticAt_id.sub analyticAt_const)).div
      ((analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).pow 2)
      (pow_ne_zero 2 (hne w hw))
  have hPa : ∀ w : ℂ, w.re < 1 / 2 → AnalyticAt ℂ (fun w : ℂ => (1 - 2 * w) ^ (-a)) w :=
    fun w hw => (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).cpow
      analyticAt_const (hslit w hw)
  -- Near the origin, via Gauss's quadratic transformation and Pfaff's transformation.
  have hball : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 16),
      ₂F₁ a b C w = (1 - 2 * w) ^ (-a) * H (v w) := by
    intro w hw
    have hw' : ‖w‖ < 1 / 16 := by simpa using hw
    have hw1 : ‖w‖ < 1 := by linarith
    have hwre : w.re < 1 / 2 := by linarith [re_le_norm w]
    have hn1 : ‖1 - w‖ ≤ 1 + ‖w‖ := by
      have := norm_sub_le (1 : ℂ) w; rwa [norm_one] at this
    have hy : ‖4 * w * (1 - w)‖ < 1 := by
      rw [norm_mul, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
      nlinarith [norm_nonneg w, norm_nonneg (1 - w)]
    have h12 : 7 / 8 ≤ ‖1 - 2 * w‖ := by
      have := norm_sub_norm_le (1 : ℂ) (2 * w)
      rw [norm_one, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num] at this
      linarith
    have hyy : 4 * w * (1 - w) / (4 * w * (1 - w) - 1) = v w := by
      have := hne w hwre
      have h' : 4 * w * (1 - w) - 1 = -(1 - 2 * w) ^ 2 := by ring
      rw [h']
      simp only [hvdef]
      field_simp
      ring
    have hvw : ‖v w‖ < 1 := by
      simp only [hvdef, norm_div, norm_mul, norm_pow, show ‖(4 : ℂ)‖ = 4 by norm_num]
      rw [div_lt_one (by positivity)]
      have hn2 : ‖w - 1‖ ≤ 1 + ‖w‖ := by
        have := norm_sub_le w (1 : ℂ); rwa [norm_one, add_comm] at this
      nlinarith [norm_nonneg w, norm_nonneg (w - 1)]
    have hq := gauss_quadratic (a := a / 2) (b := b / 2)
      (by rw [show a / 2 + b / 2 + 1 / 2 = C by rw [hC]; ring]; exact hc) hw1 hy hwre
    rw [show a / 2 + b / 2 + 1 / 2 = C by rw [hC]; ring, show 2 * (a / 2) = a by ring,
      show 2 * (b / 2) = b by ring] at hq
    rw [hq, pfaff_transformation_of_ne_neg_nat hc hy (by rwa [hyy]), hyy,
      show C - b / 2 = (a + 1) / 2 by rw [hC]; ring,
      show 1 - 4 * w * (1 - w) = (1 - 2 * w) ^ 2 by ring, sq_cpow (hre w hwre),
      show 2 * -(a / 2) = -a by ring]
  -- Continuation over the star-shaped domain.
  set D : Set ℂ :=
    {z : ℂ | ‖z‖ < 1 ∧ z.re < 1 / 2 ∧ ‖4 * z * (z - 1) / (1 - 2 * z) ^ 2‖ < 1} with hD
  have hLan : AnalyticOnNhd ℂ (₂F₁ a b C : ℂ → ℂ) D := fun w hw =>
    analyticAt_ordinaryHypergeometric hw.1
  have hRan : AnalyticOnNhd ℂ (fun w => (1 - 2 * w) ^ (-a) * H (v w)) D := fun w hw =>
    (hPa w hw.2.1).mul ((analyticAt_ordinaryHypergeometric hw.2.2).comp (f := v)
      (hva w hw.2.1))
  have hev : (₂F₁ a b C : ℂ → ℂ) =ᶠ[𝓝 0] fun w => (1 - 2 * w) ^ (-a) * H (v w) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 16)] with w hw
    exact hball w hw
  exact hLan.eqOn_of_preconnected_of_eventuallyEq hRan isPreconnected_halfSum
    (by simp [hD]) hev ⟨hz, hr, hw⟩

@[dlmf 15.8.E19]
theorem quadratic_complementary
    {a c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hr : z.re < 1 / 2)
    (hw : ‖4 * z *
    (z - 1) /
    (1 - 2 * z) ^ 2‖ < 1) :
    ₂F₁ a (1 - a) c z =
      (1 - 2 * z) ^ (1 - a - c) * (1 - z) ^ (c - 1) * ₂F₁ ((a + c) / 2) ((a + c - 1) / 2) c (4 * z * (z - 1)
        / (1 - 2 * z) ^ 2) := by
  have hc' : ∀ k : ℕ, (c + a - 1 + (c - a) + 1) / 2 ≠ -(k : ℂ) := by
    rw [show (c + a - 1 + (c - a) + 1) / 2 = c by ring]; exact hc
  have h := quadratic_half_sum (a := c + a - 1) (b := c - a) hc' hz hr hw
  rw [show (c + a - 1 + (c - a) + 1) / 2 = c by ring] at h
  rw [euler_transformation_of_ne_neg_nat hc hz, show c - a - (1 - a) = c - 1 by ring,
    show c - (1 - a) = c + a - 1 by ring, ordinaryHypergeometric_symm (c - a) (c + a - 1), h,
    show -(c + a - 1) = 1 - a - c by ring, show (c + a - 1) / 2 = (a + c - 1) / 2 by ring,
    show (c + a - 1 + 1) / 2 = (a + c) / 2 by ring,
    ordinaryHypergeometric_symm ((a + c - 1) / 2) ((a + c) / 2)]
  ring

@[dlmf 15.8.E20]
theorem quadratic_complementary_four_mul
    {a c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hr : z.re < 1 / 2)
    (hw : ‖4 * z *
    (1 - z)‖ < 1) :
    ₂F₁ a (1 - a) c z =
      (1 - z) ^ (c - 1) * ₂F₁ ((c - a) / 2) ((a + c - 1) / 2) c (4 * z * (1 - z)) := by
  have hq := gauss_quadratic (a := (c - a) / 2) (b := (a + c - 1) / 2)
    (by rw [show (c - a) / 2 + (a + c - 1) / 2 + 1 / 2 = c by ring]; exact hc) hz hw hr
  rw [show (c - a) / 2 + (a + c - 1) / 2 + 1 / 2 = c by ring,
    show 2 * ((c - a) / 2) = c - a by ring, show 2 * ((a + c - 1) / 2) = c - (1 - a) by ring] at hq
  rw [euler_transformation_of_ne_neg_nat hc hz, show c - a - (1 - a) = c - 1 by ring, hq]

/-- The principal square root of a point of the slit plane lies in the right half-plane. -/
theorem re_cpow_half_pos_of_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) :
    0 < (z ^ (1 / 2 : ℂ)).re := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have h1 : -Real.pi < z.arg := neg_pi_lt_arg z
  have h2 : z.arg < Real.pi := arg_lt_pi_iff.mpr (by
    rcases mem_slitPlane_iff.mp hz with h | h
    · exact Or.inl h.le
    · exact Or.inr h)
  rw [cpow_def_of_ne_zero hz0, exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  simp only [mul_im, log_im, log_re, one_div, inv_re, inv_im, re_ofNat, im_ofNat]
  constructor <;> norm_num <;> nlinarith [Real.pi_pos]

/-- Branch bookkeeping for the square-root quadratic transformation. -/
theorem phase_quadratic_sqrt {a z : ℂ} (hz : ‖z‖ < 1) (hs : z ∈ slitPlane) :
    (1 + z ^ (1 / 2 : ℂ)) ^ (-2 * a) *
      ((1 + z) / (1 + z ^ (1 / 2 : ℂ)) ^ 2) ^ (-a) = (1 + z) ^ (-a) := by
  set t := z ^ (1 / 2 : ℂ) with ht
  have htre : 0 < t.re := re_cpow_half_pos_of_mem_slitPlane hs
  have hz0 : z ≠ 0 := slitPlane_ne_zero hs
  have htsq : t ^ 2 = z := cpow_half_sq hz0
  have hre1 : 0 < (1 + z).re := by
    have := neg_le_of_abs_le (abs_re_le_norm z)
    simp only [add_re, one_re]; linarith
  have hre2 : 0 < (1 + t).re := by simp only [add_re, one_re]; linarith
  have h1 : 1 + z ≠ 0 := by intro h; rw [h] at hre1; simp at hre1
  have h2 : 1 + t ≠ 0 := by intro h; rw [h] at hre2; simp at hre2
  have harg1 := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre1))
  have harg2 := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre2))
  have himz : z.im = 2 * t.re * t.im := by rw [← htsq, sq, mul_im]; ring
  have hsame : ((1 + z).arg ≤ 0 ∧ (1 + t).arg ≤ 0) ∨ (0 ≤ (1 + z).arg ∧ 0 ≤ (1 + t).arg) := by
    rcases le_total t.im 0 with h | h
    · left
      exact ⟨arg_le_zero_of_im_nonpos hre1 (by simp; nlinarith),
        arg_le_zero_of_im_nonpos hre2 (by simp; linarith)⟩
    · right
      exact ⟨arg_nonneg_iff.mpr (by simp; nlinarith), arg_nonneg_iff.mpr (by simp; linarith)⟩
  have hexp : exp (log (1 + z) - 2 * log (1 + t)) = (1 + z) / (1 + t) ^ 2 := by
    rw [exp_sub, show (2 : ℂ) * log (1 + t) = ((2 : ℕ) : ℂ) * log (1 + t) by norm_num,
      exp_nat_mul, exp_log h1, exp_log h2]
  have him : (log (1 + z) - 2 * log (1 + t)).im = (1 + z).arg - 2 * (1 + t).arg := by
    simp [log_im]
  rw [cpow_eq_exp_of_exp_eq hexp (by rw [him]; rcases hsame with h | h <;> nlinarith)
      (by rw [him]; rcases hsame with h | h <;> nlinarith),
    cpow_def_of_ne_zero h2, cpow_def_of_ne_zero h1, ← exp_add]
  congr 1
  ring

@[dlmf 15.8.E21]
theorem quadratic_sqrt
    {a b z : ℂ}
    (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, 2 * a - 2 * b + 1 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane)
    (hw : ‖4 * z ^
    (1 / 2 : ℂ) /
    (1 + z ^
    (1 / 2 : ℂ)) ^ 2‖ < 1) :
    ₂F₁ a b (a - b + 1) z =
      (1 + z ^ (1 / 2 : ℂ)) ^ (-2 * a) * ₂F₁ a (a - b + 1 / 2) (2 * a - 2 * b + 1) (4 * z ^ (1 / 2 : ℂ) / (1
        + z ^ (1 / 2 : ℂ)) ^ 2) := by
  set t := z ^ (1 / 2 : ℂ) with htdef
  have htre : 0 < t.re := re_cpow_half_pos_of_mem_slitPlane hs
  have hz0 : z ≠ 0 := slitPlane_ne_zero hs
  have htsq : t ^ 2 = z := cpow_half_sq hz0
  have h1t : 1 + t ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  have h1z : 1 + z ≠ 0 := by
    intro h; have : z = -1 := by linear_combination h
    rw [this] at hz; simp at hz
  set z' := 4 * t / (1 + t) ^ 2 with hz'
  have hz'n : ‖z'‖ < 1 := hw
  have h2z' : 2 - z' ≠ 0 := by
    intro h; have : z' = 2 := by linear_combination -h
    rw [this] at hz'n; norm_num at hz'n
  have hsq : (z' / (2 - z')) ^ 2 = 4 * z / (1 + z) ^ 2 := by
    have e : 2 - z' = 2 * (1 + z) / (1 + t) ^ 2 := by
      rw [hz', ← htsq]; field_simp; ring
    rw [e, hz', ← htsq]
    field_simp
    ring
  have hw15 : ‖4 * z / (1 + z) ^ 2‖ < 1 := by
    rw [← hsq]
    have h2 : 1 < ‖2 - z'‖ := by
      have := norm_sub_norm_le (2 : ℂ) z'
      rw [show ‖(2 : ℂ)‖ = 2 by norm_num] at this
      linarith
    rw [norm_pow, norm_div]
    have : ‖z'‖ / ‖2 - z'‖ < 1 := by rw [div_lt_one (by linarith)]; linarith
    have h0 : 0 ≤ ‖z'‖ / ‖2 - z'‖ := by positivity
    nlinarith
  have h13 := quadratic_double_denominator (a := a) (b := a - b + 1 / 2) (z := z')
    (by rw [show 2 * (a - b + 1 / 2) = 2 * a - 2 * b + 1 by ring]; exact ht)
    (by rw [show a - b + 1 / 2 + 1 / 2 = a - b + 1 by ring]; exact hc) hz'n
  rw [show 2 * (a - b + 1 / 2) = 2 * a - 2 * b + 1 by ring,
    show a - b + 1 / 2 + 1 / 2 = a - b + 1 by ring, hsq] at h13
  have h1z' : 1 - z' / 2 = (1 + z) / (1 + t) ^ 2 := by
    rw [hz', ← htsq]; field_simp; ring
  rw [h13, quadratic_well_poised_plus hc hz hw15, h1z', ← mul_assoc,
    phase_quadratic_sqrt hz hs]

/-- Complex powers of a positive real through the real logarithm. -/
theorem ofReal_cpow_eq_exp_log {u : ℝ} (hu : 0 < u) (s : ℂ) :
    (u : ℂ) ^ s = exp (Real.log u * s) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hu.ne'), ofReal_log hu.le]

/-- Data for the real quadratic transformations on `(-1, 0)`. -/
theorem reciprocal_sqrt_data {x : ℝ} (hx : -1 < x) (hx0 : x < 0) :
    2 < 1 - 1 / x ∧ 1 < Real.sqrt (1 - 1 / x) ∧
      Real.sqrt (1 - 1 / x) ^ 2 = 1 - 1 / x ∧ x / (x - 1) = 1 / (1 - 1 / x) := by
  have hq : 2 < 1 - 1 / x := by
    have : 1 / x < -1 := by
      rw [div_lt_iff_of_neg hx0]; linarith
    linarith
  have hsq : Real.sqrt (1 - 1 / x) ^ 2 = 1 - 1 / x := Real.sq_sqrt (by linarith)
  refine ⟨hq, ?_, hsq, ?_⟩
  · exact (Real.lt_sqrt (by norm_num)).mpr (by linarith)
  · have : x - 1 ≠ 0 := by linarith
    have : x ≠ 0 := by linarith
    field_simp

@[dlmf 15.8.E22]
theorem quadratic_reciprocal_sqrt
    {a b : ℂ}
    {x : ℝ}
    (hc : ∀ k : ℕ,
    (a + b + 1) / 2 ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, a + b ≠ -(k : ℂ))
    (hx : -1 < x)
    (hx0 : x < 0) :
    ₂F₁ a b ((a + b + 1) / 2) (x : ℂ) =
      ((((1 - 1 / x).sqrt - 1) / ((1 - 1 / x).sqrt + 1) : ℝ) : ℂ) ^ a * ₂F₁ a ((a + b) / 2) (a + b) ((4 * (1
        - 1 / x).sqrt / ((1 - 1 / x).sqrt + 1) ^ 2 : ℝ) : ℂ) := by
  obtain ⟨hq, hr1, hrsq, hy⟩ := reciprocal_sqrt_data hx hx0
  set q := 1 - 1 / x with hqdef
  set r := Real.sqrt q with hrdef
  have hr0 : 0 < r := by linarith
  set y : ℝ := x / (x - 1) with hydef
  have hy0 : 0 < y := by rw [hy]; positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have hxn : ‖(x : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  have hyC : (x : ℂ) / ((x : ℂ) - 1) = (y : ℂ) := by push_cast [hydef]; ring
  have hyn : ‖(y : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]; exact hy1
  have hys : (y : ℂ) ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by simpa using hy0))
  have hsqrt : (y : ℂ) ^ (1 / 2 : ℂ) = ((1 / r : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hy0.le,
      ← Real.sqrt_eq_rpow, hy, Real.sqrt_div' _ (by linarith : (0 : ℝ) ≤ q), Real.sqrt_one]
  have harg : 4 * (y : ℂ) ^ (1 / 2 : ℂ) / (1 + (y : ℂ) ^ (1 / 2 : ℂ)) ^ 2 =
      ((4 * r / (r + 1) ^ 2 : ℝ) : ℂ) := by
    rw [hsqrt]
    have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
    have hr1' : (r : ℂ) + 1 ≠ 0 := by
      rw [← ofReal_one, ← ofReal_add, ofReal_ne_zero]; linarith
    push_cast
    field_simp
  have hargn : ‖4 * (y : ℂ) ^ (1 / 2 : ℂ) / (1 + (y : ℂ) ^ (1 / 2 : ℂ)) ^ 2‖ < 1 := by
    rw [harg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
      div_lt_one (by positivity)]
    nlinarith
  have h21 := quadratic_sqrt (a := a) (b := (a - b + 1) / 2) (z := (y : ℂ))
    (by rw [show a - (a - b + 1) / 2 + 1 = (a + b + 1) / 2 by ring]; exact hc)
    (by rw [show 2 * a - 2 * ((a - b + 1) / 2) + 1 = a + b by ring]; exact ht) hyn hys hargn
  rw [show a - (a - b + 1) / 2 + 1 = (a + b + 1) / 2 by ring,
    show a - (a - b + 1) / 2 + 1 / 2 = (a + b) / 2 by ring,
    show 2 * a - 2 * ((a - b + 1) / 2) + 1 = a + b by ring, harg, hsqrt] at h21
  rw [pfaff_transformation_of_ne_neg_nat hc hxn (by rw [hyC]; exact hyn), hyC,
    show (a + b + 1) / 2 - b = (a - b + 1) / 2 by ring, h21, ← mul_assoc]
  congr 1
  have h1x : 0 < 1 - x := by linarith
  have hrm : 0 < r - 1 := by linarith
  rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
    show (1 : ℂ) + ((1 / r : ℝ) : ℂ) = ((1 + 1 / r : ℝ) : ℂ) by push_cast; ring,
    ofReal_cpow_eq_exp_log h1x, ofReal_cpow_eq_exp_log (by positivity),
    ofReal_cpow_eq_exp_log (by positivity : (0 : ℝ) < (r - 1) / (r + 1)), ← exp_add]
  congr 1
  have e1 : 1 - x = r ^ 2 / ((r - 1) * (r + 1)) := by
    have hx' : x ≠ 0 := by linarith
    rw [show (r - 1) * (r + 1) = r ^ 2 - 1 by ring, hrsq, hqdef]
    field_simp
    ring
  have e2 : 1 + 1 / r = (r + 1) / r := by field_simp
  rw [e1, e2, Real.log_div (by positivity) (by positivity), Real.log_mul hrm.ne' (by positivity),
    Real.log_div (by positivity) hr0.ne', Real.log_div hrm.ne' (by positivity),
    Real.log_pow]
  push_cast
  ring

@[dlmf 15.8.E23]
theorem quadratic_reciprocal_sqrt_complementary
    {a c : ℂ}
    {x : ℝ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, 2 * c - 1 ≠ -(k : ℂ))
    (hx : -1 < x)
    (hx0 : x < 0) :
    ₂F₁ a (1 - a) c (x : ℂ) =
      (((1 - 1 / x).sqrt - 1 : ℝ) : ℂ) ^ (1 - a) * (((1 - 1 / x).sqrt + 1 : ℝ) : ℂ) ^ (a - 2 * c + 1) * ((1
        - 1 / x : ℝ) : ℂ) ^ (c - 1) * ₂F₁ (c - a) (c - 1 / 2) (2 * c - 1) ((4 * (1 - 1 / x).sqrt / ((1 - 1 /
        x).sqrt + 1) ^ 2 : ℝ) : ℂ) := by
  obtain ⟨hq, hr1, hrsq, hy⟩ := reciprocal_sqrt_data hx hx0
  set q := 1 - 1 / x with hqdef
  set r := Real.sqrt q with hrdef
  have hxn : ‖(x : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  have h22 := quadratic_reciprocal_sqrt (a := c - a) (b := c + a - 1)
    (by rw [show (c - a + (c + a - 1) + 1) / 2 = c by ring]; exact hc)
    (by rw [show c - a + (c + a - 1) = 2 * c - 1 by ring]; exact ht) hx hx0
  rw [show (c - a + (c + a - 1) + 1) / 2 = c by ring,
    show (c - a + (c + a - 1)) / 2 = c - 1 / 2 by ring,
    show c - a + (c + a - 1) = 2 * c - 1 by ring] at h22
  rw [euler_transformation_of_ne_neg_nat hc hxn, show c - a - (1 - a) = c - 1 by ring,
    show c - (1 - a) = c + a - 1 by ring, h22, ← mul_assoc]
  congr 1
  have hr0 : 0 < r := by linarith
  have hrm : 0 < r - 1 := by linarith
  have h1x : 0 < 1 - x := by linarith
  rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
    ofReal_cpow_eq_exp_log h1x, ofReal_cpow_eq_exp_log (by positivity : (0 : ℝ) < (r - 1) / (r + 1)),
    ofReal_cpow_eq_exp_log hrm, ofReal_cpow_eq_exp_log (by positivity : (0 : ℝ) < r + 1),
    ofReal_cpow_eq_exp_log (by linarith : (0 : ℝ) < q), ← exp_add, ← exp_add, ← exp_add]
  congr 1
  have e1 : 1 - x = q / ((r - 1) * (r + 1)) := by
    have hx' : x ≠ 0 := by linarith
    rw [show (r - 1) * (r + 1) = r ^ 2 - 1 by ring, hrsq, hqdef]
    field_simp
    ring
  rw [e1, Real.log_div (by linarith) (by positivity), Real.log_mul hrm.ne' (by positivity),
    Real.log_div hrm.ne' (by positivity)]
  push_cast
  ring

/-- `exp L` lies in the slit plane when `|Im L| < π`. -/
theorem exp_mem_slitPlane_of_im_mem {L : ℂ} (h1 : -Real.pi < L.im) (h2 : L.im < Real.pi) : exp L ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases hs : Real.sin L.im = 0
  · left
    have : L.im = 0 := by
      rcases Real.sin_eq_zero_iff_of_lt_of_lt h1 h2 |>.mp hs with h
      exact h
    rw [exp_re, this, Real.cos_zero, mul_one]
    exact Real.exp_pos _
  · right
    rw [exp_im]
    exact mul_ne_zero (Real.exp_pos _).ne' hs

/-- Arguments of two points with the same imaginary part, the second further right. -/
theorem arg_le_arg_of_im_eq {p q : ℂ} (hq : 0 < q.re) (hpq : q.re ≤ p.re) (him : p.im = q.im)
    (hy : 0 ≤ p.im) : 0 ≤ p.arg ∧ p.arg ≤ q.arg := by
  have hp : 0 < p.re := lt_of_lt_of_le hq hpq
  rw [arg_of_re_nonneg hp.le, arg_of_re_nonneg hq.le]
  have hnp : 0 < ‖p‖ := norm_pos_iff.mpr (by rintro rfl; simp at hp)
  have hnq : 0 < ‖q‖ := norm_pos_iff.mpr (by rintro rfl; simp at hq)
  have hle : ‖q‖ ≤ ‖p‖ := by
    rw [← sq_le_sq₀ hnq.le hnp.le, ← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_apply,
      normSq_apply, him]
    nlinarith
  constructor
  · exact Real.arcsin_nonneg.mpr (div_nonneg hy hnp.le)
  · apply Real.arcsin_le_arcsin
    rw [him]
    exact div_le_div_of_nonneg_left (by rw [← him]; exact hy) hnq hle

/-- The cubic map sends the half-plane `Re z < 8/9` into the cut plane. -/
theorem cubic_map_mem_cutPlane {z : ℂ} (hr : z.re < 8 / 9) :
    27 * z ^ 2 * (z - 1) / (9 * z - 8) ^ 2 ∈ cutPlane := by
  rw [mem_cutPlane]
  set p : ℂ := 4 / 3 - z with hp
  set q : ℂ := 8 / 9 - z with hq
  have hqre : 0 < q.re := by simp [hq]; linarith
  have hpq : q.re ≤ p.re := by simp [hp, hq]; norm_num
  have him : p.im = q.im := by simp [hp, hq]
  have hp0 : p ≠ 0 := by intro h; rw [h] at hpq; simp at hpq; linarith
  have hq0 : q ≠ 0 := by intro h; rw [h] at hqre; simp at hqre
  have h98 : 9 * z - 8 ≠ 0 := by
    intro h; apply hq0; rw [hq]; linear_combination -h / 9
  have hval : 1 - 27 * z ^ 2 * (z - 1) / (9 * z - 8) ^ 2 =
      (1 / 3 : ℝ) * exp (3 * log p - 2 * log q) := by
    have he : exp (3 * log p - 2 * log q) = p ^ 3 / q ^ 2 := by
      rw [exp_sub, show (3 : ℂ) * log p = ((3 : ℕ) : ℂ) * log p by norm_num, exp_nat_mul,
        exp_log hp0, show (2 : ℂ) * log q = ((2 : ℕ) : ℂ) * log q by norm_num, exp_nat_mul,
        exp_log hq0]
    rw [he]
    have hzq : z = 8 / 9 - q := by rw [hq]; ring
    have hpq' : p = 4 / 9 + q := by rw [hp, hq]; ring
    rw [hpq', hzq, show 9 * (8 / 9 - q) - 8 = -(9 * q) by ring]
    push_cast
    field_simp
    ring
  rw [hval]
  have hL : -Real.pi < (3 * log p - 2 * log q).im ∧ (3 * log p - 2 * log q).im < Real.pi := by
    have him' : (3 * log p - 2 * log q).im = 3 * p.arg - 2 * q.arg := by
      simp [log_im]
    rw [him']
    have hq2 : |q.arg| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hqre)
    rw [abs_lt] at hq2
    rcases le_total 0 p.im with hy | hy
    · obtain ⟨h1, h2⟩ := arg_le_arg_of_im_eq hqre hpq him hy
      constructor <;> linarith
    · have hc := arg_le_arg_of_im_eq (p := conj p) (q := conj q) (by simpa using hqre)
        (by simpa using hpq) (by simp [him]) (by simp; linarith)
      have hpc : (conj p).arg = -p.arg := by
        rw [arg_conj]; split_ifs with h
        · exfalso; have := (arg_eq_pi_iff.mp h).1; linarith
        · rfl
      have hqc : (conj q).arg = -q.arg := by
        rw [arg_conj]; split_ifs with h
        · exfalso; have := (arg_eq_pi_iff.mp h).1; linarith
        · rfl
      rw [hpc, hqc] at hc
      obtain ⟨h1, h2⟩ := hc
      constructor <;> linarith
  have hexp := exp_mem_slitPlane_of_im_mem hL.1 hL.2
  rw [mem_slitPlane_iff] at hexp ⊢
  rcases hexp with h | h
  · left; simp; positivity
  · right; simp; exact h

@[dlmf 15.8.E31]
theorem cubic_transformation
    {a z : ℂ}
    (hc : ∀ k : ℕ, 4 * a + 2 / 3 ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, 2 * a + 5 / 6 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hr : z.re < 8 / 9)
    (hw : ‖27 * z ^ 2 *
    (z - 1) /
    (9 * z - 8) ^ 2‖ < 1) :
    ₂F₁ (3 * a) (3 * a + 1 / 2) (4 * a + 2 / 3) z =
      (1 - 9 * z / 8) ^ (-2 * a) * ₂F₁ a (a + 1 / 2) (2 * a + 5 / 6) (27 * z ^ 2 * (z - 1) / (9 * z - 8) ^
        2) := by
  set H : ℂ → ℂ := ₂F₁ a (a + 1 / 2) (2 * a + 5 / 6) with hH
  set P : ℂ → ℂ := fun w => (1 + (-9 / 8) * w) ^ (-2 * a) with hP
  set φ : ℂ → ℂ := fun w => 27 * w ^ 2 * (w - 1) / (9 * w - 8) ^ 2 with hφdef
  have hsmall : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 4), ‖w‖ < 1 / 4 := fun w hw => by simpa using hw
  have h98 : ∀ w : ℂ, w.re < 8 / 9 → 9 * w - 8 ≠ 0 := by
    intro w hw h
    have := congrArg re h
    simp at this; linarith
  have hslit : ∀ w : ℂ, w.re < 8 / 9 → 1 + (-9 / 8) * w ∈ slitPlane := by
    intro w hw
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    simp; linarith
  have hre : ∀ w : ℂ, ‖w‖ < 1 / 4 → w.re < 8 / 9 := fun w hw => by
    have := re_le_norm w; linarith
  have hφn : ∀ w : ℂ, ‖w‖ < 1 / 4 → ‖φ w‖ < 1 := by
    intro w hw
    have h1 : 23 / 4 ≤ ‖9 * w - 8‖ := by
      have := norm_sub_norm_le (8 : ℂ) (9 * w)
      rw [norm_sub_rev] at this
      rw [show ‖(8 : ℂ)‖ = 8 by norm_num, norm_mul, show ‖(9 : ℂ)‖ = 9 by norm_num] at this
      linarith
    have h2 : ‖w - 1‖ ≤ 5 / 4 := by
      have := norm_sub_le w 1; rw [norm_one] at this; linarith
    simp only [hφdef, norm_div, norm_mul, norm_pow, show ‖(27 : ℂ)‖ = 27 by norm_num]
    rw [div_lt_one (by positivity)]
    have hw0 := norm_nonneg w
    have : ‖w‖ ^ 2 ≤ 1 / 16 := by nlinarith
    calc 27 * ‖w‖ ^ 2 * ‖w - 1‖ ≤ 27 * (1 / 16) * (5 / 4) := by gcongr
      _ < (23 / 4) ^ 2 := by norm_num
      _ ≤ ‖9 * w - 8‖ ^ 2 := by gcongr
  have hPa : ∀ w : ℂ, w.re < 8 / 9 → AnalyticAt ℂ P w := fun w hw =>
    (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).cpow analyticAt_const (hslit w hw)
  have hφa : ∀ w : ℂ, w.re < 8 / 9 → AnalyticAt ℂ φ w := fun w hw =>
    ((analyticAt_const.mul (analyticAt_id.pow 2)).mul (analyticAt_id.sub analyticAt_const)).div
      (((analyticAt_const.mul analyticAt_id).sub analyticAt_const).pow 2) (pow_ne_zero 2 (h98 w hw))
  have hφd : ∀ w : ℂ, w.re < 8 / 9 → HasDerivAt φ (27 * w * (3 * w - 4) ^ 2 / (9 * w - 8) ^ 3) w := by
    intro w hw
    have h := ((((hasDerivAt_id w).pow 2).const_mul 27).mul ((hasDerivAt_id w).sub_const 1)).div
      ((((hasDerivAt_id w).const_mul 9).sub_const 8).pow 2) (pow_ne_zero 2 (h98 w hw))
    refine h.congr_deriv ?_
    have := h98 w hw
    simp only [id, Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    rw [div_eq_div_iff (pow_ne_zero _ (pow_ne_zero _ this)) (pow_ne_zero _ this)]
    ring
  have hφdd : ∀ w : ℂ, w.re < 8 / 9 → deriv (deriv φ) w = 864 * (3 * w - 4) / (9 * w - 8) ^ 4 := by
    intro w hw
    have hev : deriv φ =ᶠ[𝓝 w] fun v => 27 * v * (3 * v - 4) ^ 2 / (9 * v - 8) ^ 3 := by
      have hopen : IsOpen {v : ℂ | v.re < 8 / 9} := isOpen_lt continuous_re continuous_const
      filter_upwards [hopen.mem_nhds hw] with v hv
      exact (hφd v hv).deriv
    rw [hev.deriv_eq]
    have h := (((hasDerivAt_id w).const_mul 27).mul ((((hasDerivAt_id w).const_mul 3).sub_const
      4).pow 2)).div ((((hasDerivAt_id w).const_mul 9).sub_const 8).pow 3)
      (pow_ne_zero 3 (h98 w hw))
    have h' : HasDerivAt (fun v => 27 * v * (3 * v - 4) ^ 2 / (9 * v - 8) ^ 3) _ w := h
    rw [h'.deriv]
    have := h98 w hw
    simp only [id, Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl,
      show (3 : ℕ) - 1 = 2 from rfl, pow_one]
    rw [div_eq_div_iff (pow_ne_zero _ (pow_ne_zero _ this)) (pow_ne_zero _ this)]
    ring
  have hG : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 4), (fun v => P v * H (φ v)) w =
      ₂F₁ (3 * a) (3 * a + 1 / 2) (4 * a + 2 / 3) w := by
    refine eq_ordinaryHypergeometric_of_gaussOperator hc (by norm_num) (by norm_num) ?_ ?_ ?_
    · intro w hw
      have hw1 := hsmall w hw
      exact (hPa w (hre w hw1)).mul ((analyticAt_ordinaryHypergeometric (hφn w hw1)).comp
        (f := φ) (hφa w (hre w hw1)))
    · intro w hw
      have hw1 := hsmall w hw
      have hwr := hre w hw1
      have hHa : AnalyticAt ℂ H (φ w) := analyticAt_ordinaryHypergeometric (hφn w hw1)
      rw [gaussOperator_mul_comp (hPa w hwr) (hφa w hwr) hHa,
        show deriv P w = _ from deriv_affine_cpow (hslit w hwr),
        show deriv (deriv P) w = _ from deriv_deriv_affine_cpow (hslit w hwr),
        (hφd w hwr).deriv, hφdd w hwr]
      have hode := gaussOperator_ordinaryHypergeometric (a := a) (b := a + 1 / 2) ht (hφn w hw1)
      simp only [gaussOperator] at hode
      have h9 := h98 w hwr
      have h1 : 1 + (-9 / 8) * w ≠ 0 := slitPlane_ne_zero (hslit w hwr)
      have key : w * (1 - w) * (-2 * a * (-2 * a - 1) * (-9 / 8) ^ 2 * (1 + -9 / 8 * w) ^ (-2 * a) /
            (1 + -9 / 8 * w) ^ 2 * H (φ w) +
          2 * (-2 * a * (-9 / 8) * (1 + -9 / 8 * w) ^ (-2 * a) / (1 + -9 / 8 * w)) *
            (deriv H (φ w) * (27 * w * (3 * w - 4) ^ 2 / (9 * w - 8) ^ 3)) +
          P w * (iteratedDeriv 2 H (φ w) * (27 * w * (3 * w - 4) ^ 2 / (9 * w - 8) ^ 3) ^ 2 +
            deriv H (φ w) * (864 * (3 * w - 4) / (9 * w - 8) ^ 4))) +
          (4 * a + 2 / 3 - (3 * a + (3 * a + 1 / 2) + 1) * w) *
            (-2 * a * (-9 / 8) * (1 + -9 / 8 * w) ^ (-2 * a) / (1 + -9 / 8 * w) * H (φ w) +
              P w * (deriv H (φ w) * (27 * w * (3 * w - 4) ^ 2 / (9 * w - 8) ^ 3))) -
          3 * a * (3 * a + 1 / 2) * (P w * H (φ w)) =
          P w * 27 * w * (3 * w - 4) / (9 * w - 8) ^ 2 *
            (φ w * (1 - φ w) * iteratedDeriv 2 H (φ w) +
              (2 * a + 5 / 6 - (a + (a + 1 / 2) + 1) * φ w) * deriv H (φ w) -
              a * (a + 1 / 2) * H (φ w)) := by
        simp only [hP]
        generalize H (φ w) = h0
        generalize deriv H (φ w) = h1
        generalize iteratedDeriv 2 H (φ w) = h2
        generalize (1 + -9 / 8 * w) ^ (-2 * a) = pw
        simp only [hφdef]
        obtain ⟨u, hu⟩ : ∃ u, u = 9 * w - 8 := ⟨_, rfl⟩
        have hwu : w = (u + 8) / 9 := by rw [hu]; ring
        have hu0 : u ≠ 0 := by rw [hu]; exact h9
        rw [show (1 : ℂ) + -9 / 8 * w = -u / 8 by rw [hu]; ring, ← hu]
        subst hwu
        field_simp
        ring
      rw [key, hode, mul_zero]
    · simp [hP, hφdef, hH, ordinaryHypergeometric_zero]
  -- extension to `‖w‖ < 1, Re w < 8/9` through the cut-plane continuation
  set c₂ := 2 * a + 5 / 6 with hc₂
  set R : ℂ → ℂ := fun w => P w * (Gamma c₂ * regularizedGaussHG a (a + 1 / 2) c₂ (φ w)) with hR
  set A : Set ℂ := {w | ‖w‖ < 1 ∧ w.re < 8 / 9} with hA
  have hAc : IsPreconnected A := by
    have : A = Metric.ball (0 : ℂ) 1 ∩ {w | w.re < 8 / 9} := by
      ext w; simp [hA]
    rw [this]
    exact ((convex_ball (0 : ℂ) 1).inter (convex_halfSpace_re_lt (8 / 9))).isPreconnected
  have hRe : ∀ w : ℂ, ‖φ w‖ < 1 → R w = P w * H (φ w) := by
    intro w hw
    simp only [hR, hH]
    rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw, regularizedGaussHGFun_eq_div_Gamma ht,
      mul_div_cancel₀ _ (Gamma_ne_zero ht)]
  have hLan : AnalyticOnNhd ℂ (₂F₁ (3 * a) (3 * a + 1 / 2) (4 * a + 2 / 3) : ℂ → ℂ) A :=
    fun w hw => analyticAt_ordinaryHypergeometric hw.1
  have hRan : AnalyticOnNhd ℂ R A := fun w hw =>
    (hPa w hw.2).mul (analyticAt_const.mul ((analyticAt_regularizedGaussHG _ _ _
      (cubic_map_mem_cutPlane hw.2)).comp (f := φ) (hφa w hw.2)))
  have h0A : (0 : ℂ) ∈ A := by simp [hA]
  have hev : (₂F₁ (3 * a) (3 * a + 1 / 2) (4 * a + 2 / 3) : ℂ → ℂ) =ᶠ[𝓝 0] R := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4)] with w hw
    rw [hRe w (hφn w (hsmall w hw))]
    exact (hG w hw).symm
  have hEq := hLan.eqOn_of_preconnected_of_eventuallyEq hRan hAc h0A hev ⟨hz, hr⟩
  rw [hEq, hRe z hw]
  simp only [hP, hφdef, hH]
  rw [show (1 : ℂ) - 9 * z / 8 = 1 + -9 / 8 * z by ring]

/-- Second derivative of a composition, for analytic data. -/
theorem deriv_deriv_comp {φ F : ℂ → ℂ} {z : ℂ} (hφ : AnalyticAt ℂ φ z)
    (hF : AnalyticAt ℂ F (φ z)) :
    deriv (deriv (fun w => F (φ w))) z =
      iteratedDeriv 2 F (φ z) * deriv φ z ^ 2 + deriv F (φ z) * deriv (deriv φ) z := by
  have hev : deriv (fun w => F (φ w)) =ᶠ[𝓝 z] fun w => deriv F (φ w) * deriv φ w := by
    filter_upwards [hφ.eventually_analyticAt,
      hφ.continuousAt.tendsto.eventually hF.eventually_analyticAt] with w h1 h2
    exact (h2.differentiableAt.hasDerivAt.comp w h1.differentiableAt.hasDerivAt).deriv
  rw [hev.deriv_eq]
  have h := (hF.deriv.differentiableAt.hasDerivAt.comp z hφ.differentiableAt.hasDerivAt).mul
    hφ.deriv.differentiableAt.hasDerivAt
  have h' : HasDerivAt (fun w => deriv F (φ w) * deriv φ w) _ z := h
  rw [h'.deriv]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, Function.comp_apply]
  ring

/-- The principal cube root has positive real part. -/
theorem re_cpow_third_pos {x : ℂ} (hx : x ≠ 0) : 0 < (x ^ (1 / 3 : ℂ)).re := by
  rw [cpow_def_of_ne_zero hx, exp_re]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
  · have := neg_pi_lt_arg x
    simp [log_im]
    nlinarith [Real.pi_pos]
  · have := arg_le_pi x
    simp [log_im]
    nlinarith [Real.pi_pos]

/-- `(x^{1/3})³ = x`. -/
theorem cpow_third_cube (x : ℂ) : (x ^ (1 / 3 : ℂ)) ^ 3 = x := by
  rw [← cpow_nat_mul]; norm_num

/-- `‖1 - t‖ < ‖1 + 2t‖` when `Re t > 0`. -/
theorem norm_one_sub_lt_norm_one_add_two_mul {t : ℂ} (ht : 0 < t.re) : ‖1 - t‖ < ‖1 + 2 * t‖ := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq, ← normSq_eq_norm_sq,
    normSq_apply, normSq_apply]
  simp only [sub_re, one_re, sub_im, one_im, add_re, add_im, mul_re, mul_im, re_ofNat, im_ofNat]
  nlinarith [sq_nonneg t.im, sq_nonneg t.re]

/-- The cubic transformation of the Borweins for `₂F₁(1/3,2/3;1;·)`. -/
theorem borwein_cubic {v : ℂ} (hv : ‖v‖ < 1) :
    ₂F₁ (1 / 3 : ℂ) (2 / 3) 1 v = 3 / (1 + 2 * (1 - v) ^ (1 / 3 : ℂ)) *
      ₂F₁ (1 / 3 : ℂ) (2 / 3) 1 (((1 - (1 - v) ^ (1 / 3 : ℂ)) / (1 + 2 * (1 - v) ^ (1 / 3 : ℂ))) ^ 3) := by
  set H : ℂ → ℂ := ₂F₁ (1 / 3 : ℂ) (2 / 3) 1 with hH
  set S : ℂ → ℂ := fun v => (1 - v) ^ (1 / 3 : ℂ) with hS
  set p : ℂ → ℂ := fun t => 3 / (1 + 2 * t) with hp
  set ψ : ℂ → ℂ := fun t => ((1 - t) / (1 + 2 * t)) ^ 3 with hψ
  have hball : ∀ w ∈ Metric.ball (0 : ℂ) 1, ‖w‖ < 1 := fun w hw => by simpa using hw
  have h1v : ∀ w : ℂ, ‖w‖ < 1 → 1 - w ∈ slitPlane := by
    intro w hw
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    have := (re_le_norm w).trans_lt hw
    simp only [sub_re, one_re]; linarith
  have hSre : ∀ w : ℂ, ‖w‖ < 1 → 0 < (S w).re := fun w hw =>
    re_cpow_third_pos (slitPlane_ne_zero (h1v w hw))
  have h12 : ∀ t : ℂ, 0 < t.re → 1 + 2 * t ≠ 0 := by
    intro t ht h
    have := congrArg re h
    simp at this; linarith
  have hS0 : ∀ w : ℂ, ‖w‖ < 1 → S w ≠ 0 := fun w hw h => by
    have := hSre w hw; rw [h] at this; simp at this
  have hψn : ∀ t : ℂ, 0 < t.re → ‖ψ t‖ < 1 := by
    intro t ht
    simp only [hψ, norm_pow, norm_div]
    have h1 := norm_one_sub_lt_norm_one_add_two_mul ht
    have h2 : 0 < ‖1 + 2 * t‖ := norm_pos_iff.mpr (h12 t ht)
    have h3 : ‖1 - t‖ / ‖1 + 2 * t‖ < 1 := by rw [div_lt_one h2]; exact h1
    have h4 : 0 ≤ ‖1 - t‖ / ‖1 + 2 * t‖ := by positivity
    calc (‖1 - t‖ / ‖1 + 2 * t‖) ^ 3 < 1 ^ 3 := by gcongr
      _ = 1 := one_pow 3
  have hS3 : ∀ w : ℂ, S w ^ 3 = 1 - w := fun w => cpow_third_cube _
  -- derivatives of `S`
  have hSd : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt S (-1 / (3 * S w ^ 2)) w := by
    intro w hw
    have h := ((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w)).cpow_const (c := 1 / 3) (h1v w hw)
    refine h.congr_deriv ?_
    have h0 := hS0 w hw
    have h1 : (1 - w) ≠ 0 := slitPlane_ne_zero (h1v w hw)
    simp only [id, Pi.sub_apply]
    rw [cpow_sub _ _ h1, cpow_one]
    have e : (1 - w) = S w ^ 3 := (hS3 w).symm
    simp only [hS] at h0 e ⊢
    generalize (1 - w) ^ (1 / 3 : ℂ) = s at h0 e ⊢
    rw [e]
    field_simp
    ring
  have hSa : ∀ w : ℂ, ‖w‖ < 1 → AnalyticAt ℂ S w := fun w hw =>
    (analyticAt_const.sub analyticAt_id).cpow analyticAt_const (h1v w hw)
  have hSdd : ∀ w : ℂ, ‖w‖ < 1 → deriv (deriv S) w = -2 / (9 * S w ^ 5) := by
    intro w hw
    have hopen : IsOpen {w : ℂ | ‖w‖ < 1} := isOpen_lt continuous_norm continuous_const
    have hev : deriv S =ᶠ[𝓝 w] fun v => -1 / (3 * S v ^ 2) := by
      filter_upwards [hopen.mem_nhds hw] with v hv
      exact (hSd v hv).deriv
    rw [hev.deriv_eq]
    have h0 := hS0 w hw
    have h := ((hSd w hw).pow 2).const_mul 3 |>.inv (by simpa using h0) |>.const_mul (-1)
    have h' : HasDerivAt (fun v => -1 / (3 * S v ^ 2)) (-2 / (9 * S w ^ 5)) w := by
      have h2 := h.congr_of_eventuallyEq (f₁ := fun v => -1 / (3 * S v ^ 2))
        (Eventually.of_forall fun v => by simp [div_eq_mul_inv])
      refine h2.congr_deriv ?_
      simp only [Pi.pow_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      field_simp
      ring
    rw [h'.deriv]
  -- derivatives of `p` and `ψ`
  have hpd : ∀ t : ℂ, 1 + 2 * t ≠ 0 → HasDerivAt p (-6 / (1 + 2 * t) ^ 2) t := by
    intro t ht
    have h := (hasDerivAt_const t (3 : ℂ)).div (((hasDerivAt_id t).const_mul 2).const_add 1) ht
    refine h.congr_deriv ?_
    simp only [id]; field_simp; ring
  have hψd : ∀ t : ℂ, 1 + 2 * t ≠ 0 → HasDerivAt ψ (-9 * (1 - t) ^ 2 / (1 + 2 * t) ^ 4) t := by
    intro t ht
    have h := (((hasDerivAt_const t (1 : ℂ)).sub (hasDerivAt_id t)).div
      (((hasDerivAt_id t).const_mul 2).const_add 1) ht).pow 3
    refine h.congr_deriv ?_
    simp only [id, Pi.div_apply, Pi.sub_apply, Nat.cast_ofNat, show (3 : ℕ) - 1 = 2 from rfl]
    field_simp
    ring
  have hopen12 : IsOpen {t : ℂ | 1 + 2 * t ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
  have hpdd : ∀ t : ℂ, 1 + 2 * t ≠ 0 → deriv (deriv p) t = 24 / (1 + 2 * t) ^ 3 := by
    intro t ht
    have hev : deriv p =ᶠ[𝓝 t] fun u => -6 / (1 + 2 * u) ^ 2 := by
      filter_upwards [hopen12.mem_nhds ht] with u hu
      exact (hpd u hu).deriv
    rw [hev.deriv_eq]
    have h := (hasDerivAt_const t (-6 : ℂ)).div ((((hasDerivAt_id t).const_mul 2).const_add 1).pow 2)
      (pow_ne_zero 2 ht)
    have h' : HasDerivAt (fun u => -6 / (1 + 2 * u) ^ 2) _ t := h
    rw [h'.deriv]
    simp only [id, Pi.pow_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    field_simp
    ring
  have hψdd : ∀ t : ℂ, 1 + 2 * t ≠ 0 →
      deriv (deriv ψ) t = 18 * (1 - t) * (5 - 2 * t) / (1 + 2 * t) ^ 5 := by
    intro t ht
    have hev : deriv ψ =ᶠ[𝓝 t] fun u => -9 * (1 - u) ^ 2 / (1 + 2 * u) ^ 4 := by
      filter_upwards [hopen12.mem_nhds ht] with u hu
      exact (hψd u hu).deriv
    rw [hev.deriv_eq]
    have h := ((((hasDerivAt_const t (1 : ℂ)).sub (hasDerivAt_id t)).pow 2).const_mul (-9)).div
      ((((hasDerivAt_id t).const_mul 2).const_add 1).pow 4) (pow_ne_zero 4 ht)
    have h' : HasDerivAt (fun u => -9 * (1 - u) ^ 2 / (1 + 2 * u) ^ 4) _ t := h
    rw [h'.deriv]
    simp only [id, Pi.pow_apply, Pi.sub_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl,
      show (4 : ℕ) - 1 = 3 from rfl, pow_one]
    field_simp
    ring
  have hpa : ∀ t : ℂ, 1 + 2 * t ≠ 0 → AnalyticAt ℂ p t := fun t ht =>
    analyticAt_const.div (analyticAt_const.add (analyticAt_const.mul analyticAt_id)) ht
  have hψa : ∀ t : ℂ, 1 + 2 * t ≠ 0 → AnalyticAt ℂ ψ t := fun t ht =>
    ((analyticAt_const.sub analyticAt_id).div
      (analyticAt_const.add (analyticAt_const.mul analyticAt_id)) ht).pow 3
  set Q : ℂ → ℂ := fun t => p t * H (ψ t) with hQ
  have hQa : ∀ t : ℂ, 0 < t.re → AnalyticAt ℂ Q t := fun t ht =>
    (hpa t (h12 t ht)).mul ((analyticAt_ordinaryHypergeometric (hψn t ht)).comp
      (f := ψ) (hψa t (h12 t ht)))
  have hc1 : ∀ k : ℕ, (1 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hG := eq_ordinaryHypergeometric_of_gaussOperator (a := 1 / 3) (b := 2 / 3) hc1 one_pos le_rfl
    (g := fun v => Q (S v)) ?_ ?_ ?_ v (by simpa using hv)
  · exact hG.symm
  · intro w hw
    exact (hQa _ (hSre w (hball w hw))).comp (f := S) (hSa w (hball w hw))
  · intro w hw
    have hw1 := hball w hw
    set t := S w with ht
    have htre := hSre w hw1
    have ht12 := h12 t htre
    have ht0 := hS0 w hw1
    have hHa : AnalyticAt ℂ H (ψ t) := analyticAt_ordinaryHypergeometric (hψn t htre)
    have hd1 : deriv (fun v => Q (S v)) w = deriv Q t * deriv S w := by
      have hQd : HasDerivAt Q (deriv Q t) (S w) := (hQa t htre).differentiableAt.hasDerivAt
      have h := hQd.comp w (hSa w hw1).differentiableAt.hasDerivAt
      exact h.deriv
    have hd2 := deriv_deriv_comp (hSa w hw1) (hQa t htre)
    have hQ1 : deriv Q t = deriv p t * H (ψ t) + p t * (deriv H (ψ t) * deriv ψ t) :=
      (deriv_mul_comp_eventuallyEq (hpa t ht12) (hψa t ht12) hHa).eq_of_nhds
    have hQ2 : iteratedDeriv 2 Q t = deriv (deriv p) t * H (ψ t) +
        2 * deriv p t * (deriv H (ψ t) * deriv ψ t) +
        p t * (iteratedDeriv 2 H (ψ t) * deriv ψ t ^ 2 + deriv H (ψ t) * deriv (deriv ψ) t) := by
      rw [show iteratedDeriv 2 Q t = deriv (deriv Q) t by
        simp only [iteratedDeriv_succ, iteratedDeriv_zero]]
      exact deriv_deriv_mul_comp (hpa t ht12) (hψa t ht12) hHa
    simp only [gaussOperator]
    rw [show iteratedDeriv 2 (fun v => Q (S v)) w = deriv (deriv (fun v => Q (S v))) w by
      simp only [iteratedDeriv_succ, iteratedDeriv_zero], hd2, hd1, hQ2, hQ1,
      (hSd w hw1).deriv, hSdd w hw1, (hpd t ht12).deriv, hpdd t ht12, (hψd t ht12).deriv,
      hψdd t ht12]
    have hode : gaussOperator (1 / 3) (2 / 3) 1 H (ψ t) = 0 :=
      gaussOperator_ordinaryHypergeometric (a := 1 / 3) (b := 2 / 3) hc1 (hψn t htre)
    simp only [gaussOperator] at hode
    have hwt : w = 1 - t ^ 3 := by rw [hS3 w]; ring
    rw [← ht]
    have ht0' : t ≠ 0 := ht0
    clear_value t
    simp only [hQ]
    generalize H (ψ t) = h0 at hode ⊢
    generalize deriv H (ψ t) = h1 at hode ⊢
    generalize iteratedDeriv 2 H (ψ t) = h2 at hode ⊢
    simp only [hp, hψ] at hode ⊢
    rw [hwt]
    have hu : (1 + 2 * t) ≠ 0 := ht12
    obtain ⟨u, hu', rfl⟩ : ∃ u : ℂ, u ≠ 0 ∧ t = (u - 1) / 2 := ⟨1 + 2 * t, hu, by ring⟩
    have hu1 : u - 1 ≠ 0 := by intro h; apply ht0'; rw [h]; ring
    rw [show 1 + 2 * ((u - 1) / 2) = u by ring] at hode ⊢
    linear_combination (norm := skip) (3 * ((u - 1) / 2 - 1) ^ 2 / (((u - 1) / 2) ^ 2 * u ^ 3)) * hode
    field_simp
    ring
  · simp [hQ, hp, hψ, hS, hH, ordinaryHypergeometric_zero]
    norm_num

@[dlmf 15.8.E33]
theorem ramanujan_cubic {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ₂F₁ (1 / 3 : ℂ) (2 / 3) 1 (1 - (((1 - x) / (1 + 2 * x) : ℝ) : ℂ) ^ 3) =
      (1 + 2 * (x : ℂ)) * ₂F₁ (1 / 3 : ℂ) (2 / 3) 1 ((x : ℂ) ^ 3) := by
  set r : ℝ := (1 - x) / (1 + 2 * x) with hr
  have h12 : 0 < 1 + 2 * x := by linarith
  have hr0 : 0 < r := div_pos (by linarith) h12
  have hr1 : r < 1 := by rw [hr, div_lt_one h12]; linarith
  have hv : ‖1 - (r : ℂ) ^ 3‖ < 1 := by
    rw [show 1 - (r : ℂ) ^ 3 = ((1 - r ^ 3 : ℝ) : ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs]
    have : r ^ 3 < 1 := by
      calc r ^ 3 < 1 ^ 3 := by gcongr
        _ = 1 := one_pow 3
    have : 0 < r ^ 3 := by positivity
    rw [abs_lt]; constructor <;> linarith
  have hroot : (1 - (1 - (r : ℂ) ^ 3)) ^ (1 / 3 : ℂ) = r := by
    rw [sub_sub_cancel, show (r : ℂ) ^ 3 = ((r ^ 3 : ℝ) : ℂ) by push_cast; ring,
      show (1 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
      show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast hr0.le (by norm_num)]
  rw [borwein_cubic hv, hroot]
  have e1 : (3 : ℂ) / (1 + 2 * (r : ℂ)) = 1 + 2 * (x : ℂ) := by
    have : (1 + 2 * r) * (1 + 2 * x) = 3 := by rw [hr]; field_simp; ring
    have h1r : (1 + 2 * (r : ℂ)) ≠ 0 := by
      exact_mod_cast (show (1 + 2 * r : ℝ) ≠ 0 by linarith)
    rw [div_eq_iff h1r]
    exact_mod_cast (by linarith [this] : (3 : ℝ) = (1 + 2 * x) * (1 + 2 * r))
  have e2 : (1 - (r : ℂ)) / (1 + 2 * (r : ℂ)) = x := by
    have : (1 - r) / (1 + 2 * r) = x := by rw [hr]; field_simp; ring
    exact_mod_cast this
  rw [e1, e2]

attribute [dlmf 15.8.E12] regularized_euler
attribute [dlmf 15.8.E29] quadratic_sqrt
attribute [dlmf 15.8.E30] quadratic_double_denominator quadratic_well_poised_plus
attribute [dlmf 15.10.E11] regularized_euler regularized_pfaff

end DLMF.Hypergeometric
