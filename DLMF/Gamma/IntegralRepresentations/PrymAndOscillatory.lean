/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.IntegralRepresentations.HankelAndGaussian

/-!
# Prym decomposition and oscillatory Gamma integrals

Prym decomposition and the oscillatory sine and cosine representations of the Gamma function.

Source references and common attribution are retained in
`DLMF.Gamma.IntegralRepresentations`.
-/

@[expose] public section

open Complex Filter MeasureTheory intervalIntegral

open scoped Real Topology

noncomputable section

namespace DLMF.Gamma

local macro "deriv_simp" : tactic => `(tactic| first
  | (simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, id_eq];
      field_simp; ring)
  | (simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, id_eq];
      field_simp; done)
  | (simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, id_eq];
      ring)
  | (field_simp; ring) | (field_simp; done) | ring | (simp; field_simp; ring) | (simp; done))

section Prym

/-! ### Prym's decomposition (Temme §3.2.1)

`Γ(z) = ∫₁^∞ t^{z-1} e^{-t} dt + ∑ₖ (-1)ᵏ/((z+k) k!)`. For `Re z > 0` this is Euler's integral
split at `t = 1`, with the exponential series integrated termwise on `(0, 1]`. Both terms
satisfy `F(z+1) = z F(z)` up to the same constant `e⁻¹` with opposite signs, so the sum obeys
the recursion of `Γ`, which carries the formula to all `z ∉ -ℕ`. -/

open Set

/-- Prym's series `∑ₖ (-1)ᵏ/((z+k) k!)`. -/
def prymSeries (z : ℂ) : ℂ := ∑' k : ℕ, (-1 : ℂ) ^ k / ((z + k) * k.factorial)

/-- The upper incomplete Euler integral `∫₁^∞ t^{z-1} e^{-t} dt`. -/
def prymIntegral (z : ℂ) : ℂ := ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (z - 1) * Complex.exp (-(t : ℂ))

/-- Prym's series `∑ₖ (-1)^k/((z + k) k!)` converges. -/
theorem summable_prym (z : ℂ) :
    Summable fun k : ℕ => (-1 : ℂ) ^ k / ((z + k) * k.factorial) := by
  refine Summable.of_norm_bounded_eventually_nat (g := fun k => 1 ^ k / (k.factorial : ℝ))
    (Real.summable_pow_div_factorial 1) ?_
  filter_upwards [eventually_ge_atTop (⌈‖z‖⌉₊ + 1)] with k hk
  have hk' : ‖z‖ + 1 ≤ k := by
    have := Nat.le_ceil ‖z‖
    have : ((⌈‖z‖⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at this
    linarith
  have h1 : 1 ≤ ‖z + k‖ := by
    have := norm_sub_norm_le (k : ℂ) (-z)
    rw [norm_neg, Complex.norm_natCast, sub_neg_eq_add, add_comm] at this
    linarith
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast,
    div_le_div_iff₀ (by positivity) hf]
  nlinarith

/-- `t^(z-1) e^(-t)` is integrable on `(1, ∞)`. -/
theorem integrableOn_prymIntegral (z : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * Complex.exp (-(t : ℂ))) (Ioi 1) := by
  set s := max z.re 1 with hs
  have hs0 : 0 < s := lt_max_of_lt_right one_pos
  have hG := (Real.GammaIntegral_convergent hs0).mono_set (Ioi_subset_Ioi zero_le_one)
  refine hG.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht' : (0 : ℝ) < t := zero_lt_one.trans ht
    exact ((continuousAt_ofReal_cpow_const t (z - 1) (Or.inr ht'.ne')).mul
      (by fun_prop : Continuous fun t : ℝ => Complex.exp (-(t : ℂ))).continuousAt)
      |>.continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht' : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht'
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_exp, neg_re, ofReal_re, sub_re,
      one_re, mul_comm]
    gcongr
    · exact ht'.le
    · simp [hs]

/-- `∫₁^∞ t^z e^{-t} dt = e⁻¹ + z ∫₁^∞ t^{z-1} e^{-t} dt`, by parts. -/
theorem prymIntegral_add_one (z : ℂ) :
    prymIntegral (z + 1) = Complex.exp (-1) + z * prymIntegral z := by
  have hu : ∀ t ∈ Ioi (1 : ℝ), HasDerivAt (fun t : ℝ => (t : ℂ) ^ z) (z * (t : ℂ) ^ (z - 1)) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    have := ((hasDerivAt_id (t : ℂ)).cpow_const (c := z) (by simpa using ht0)).comp_ofReal
    simpa using this
  have hv : ∀ t ∈ Ioi (1 : ℝ), HasDerivAt (fun t : ℝ => -Complex.exp (-(t : ℂ)))
      (Complex.exp (-(t : ℂ))) t := by
    intro t _
    have := ((hasDerivAt_id (t : ℂ)).neg.cexp.neg).comp_ofReal
    simpa using this
  have huv' : IntegrableOn (fun t : ℝ => (t : ℂ) ^ z * Complex.exp (-(t : ℂ))) (Ioi 1) := by
    simpa using integrableOn_prymIntegral (z + 1)
  have hu'v : IntegrableOn (fun t : ℝ => z * (t : ℂ) ^ (z - 1) * -Complex.exp (-(t : ℂ)))
      (Ioi 1) := by
    have := ((integrableOn_prymIntegral z).const_mul (-z))
    refine IntegrableOn.congr_fun this (fun t _ => by ring) measurableSet_Ioi
  have hzero : Tendsto (fun t : ℝ => (t : ℂ) ^ z * -Complex.exp (-(t : ℂ))) (𝓝[>] 1)
      (𝓝 (-Complex.exp (-1))) := by
    have hc : ContinuousAt (fun t : ℝ => (t : ℂ) ^ z * -Complex.exp (-(t : ℂ))) 1 :=
      (continuousAt_ofReal_cpow_const 1 z (Or.inr one_ne_zero)).mul
        (by fun_prop : Continuous fun t : ℝ => -Complex.exp (-(t : ℂ))).continuousAt
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hinfty : Tendsto (fun t : ℝ => (t : ℂ) ^ z * -Complex.exp (-(t : ℂ))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero z.re 1 one_pos).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
    simp
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hzero hinfty
  simp only [prymIntegral, add_sub_cancel_right]
  rw [h, sub_neg_eq_add, zero_add, ← MeasureTheory.integral_const_mul, sub_eq_add_neg,
    ← MeasureTheory.integral_neg]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

/-- `z S(z) = e⁻¹ + S(z+1)`. -/
theorem mul_prymSeries {z : ℂ} (hz : ∀ k : ℕ, z ≠ -k) :
    z * prymSeries z = Complex.exp (-1) + prymSeries (z + 1) := by
  have hzk : ∀ k : ℕ, z + k ≠ 0 := fun k h => hz k (eq_neg_of_add_eq_zero_left h)
  have hexp : HasSum (fun k : ℕ => (-1 : ℂ) ^ k / k.factorial) (Complex.exp (-1)) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp (-1 : ℂ)
  set g : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * k / ((z + k) * k.factorial) with hg
  have hsplit : ∀ k : ℕ, z * ((-1 : ℂ) ^ k / ((z + k) * k.factorial)) =
      (-1 : ℂ) ^ k / k.factorial - g k := by
    intro k
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    simp only [hg]
    field_simp
    have := hzk k
    field_simp
    ring
  have hgs : Summable g := by
    have h1 := (summable_prym z).mul_left z
    simp_rw [hsplit] at h1
    have := hexp.summable.sub h1
    simpa using this
  have hg0 : ∀ j : ℕ, g (j + 1) = -((-1 : ℂ) ^ j / ((z + 1 + j) * j.factorial)) := by
    intro j
    have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    have hzj : z + 1 + j ≠ 0 := by
      have := hzk (j + 1); push_cast at this; rwa [add_assoc, add_comm (1 : ℂ)]
    simp only [hg, Nat.factorial_succ]
    push_cast
    field_simp
    rw [show z + (j + 1) = z + 1 + j by ring]
    field_simp
    ring
  have hgsum : ∑' k, g k = -prymSeries (z + 1) := by
    rw [hgs.tsum_eq_zero_add, prymSeries, ← tsum_neg]
    simp only [hg, Nat.cast_zero, mul_zero, zero_div, zero_add]
    exact tsum_congr hg0
  rw [prymSeries, ← tsum_mul_left]
  simp_rw [hsplit]
  rw [(hexp.summable).tsum_sub hgs, hexp.tsum_eq, hgsum, sub_neg_eq_add]

/-- The `k`-th term `(-1)ᵏ t^{z+k-1}/k!` of `t^{z-1} e^{-t}`. -/
def prymTerm (z : ℂ) (k : ℕ) (t : ℝ) : ℂ := (-1 : ℂ) ^ k / k.factorial * (t : ℂ) ^ (z + k - 1)

/-- For `Re(z + k) > 0`, the `k`-th term `(-1)^k t^(z+k-1)/k!` is integrable on `(0, 1]`. -/
theorem integrableOn_prymTerm {z : ℂ} {k : ℕ} (hk : 0 < (z + k).re) :
    IntegrableOn (prymTerm z k) (Ioc 0 1) := by
  have hre : -1 < (z + k - 1).re := by simp at hk ⊢; linarith
  have := (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1) hre).const_mul
    ((-1 : ℂ) ^ k / k.factorial)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
  exact this

/-- `∫₀¹ (-1)^k t^(z+k-1)/k! dt = (-1)^k/((z + k) k!)` for `Re(z + k) > 0`. -/
theorem integral_prymTerm {z : ℂ} {k : ℕ} (hk : 0 < (z + k).re) :
    ∫ t in Ioc (0 : ℝ) 1, prymTerm z k t = (-1 : ℂ) ^ k / ((z + k) * k.factorial) := by
  have hre : -1 < (z + k - 1).re := by simp at hk ⊢; linarith
  have hzk : z + k ≠ 0 := fun h => by rw [h, zero_re] at hk; exact lt_irrefl _ hk
  simp only [prymTerm]
  rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl hre), sub_add_cancel, ofReal_one, one_cpow, ofReal_zero,
    zero_cpow hzk, sub_zero]
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp

/-- `∫₀¹ |(-1)^k t^(z+k-1)/k!| dt = 1/(k! Re(z + k))` for `Re(z + k) > 0`. -/
theorem integral_norm_prymTerm {z : ℂ} {k : ℕ} (hk : 0 < (z + k).re) :
    ∫ t in Ioc (0 : ℝ) 1, ‖prymTerm z k t‖ = 1 / (k.factorial * (z + k).re) := by
  have hk' : 0 < z.re + k := by simpa using hk
  have hre : -1 < z.re + k - 1 := by linarith
  have heq : EqOn (fun t => ‖prymTerm z k t‖) (fun t => 1 / k.factorial * t ^ (z.re + k - 1))
      (Ioc 0 1) := by
    intro t ht
    simp only [prymTerm]
    rw [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast,
      norm_cpow_eq_rpow_re_of_pos ht.1]
    simp
  rw [setIntegral_congr_fun measurableSet_Ioc heq, MeasureTheory.integral_const_mul,
    ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hre)]
  rw [sub_add_cancel, Real.one_rpow, Real.zero_rpow hk'.ne', sub_zero]
  simp only [add_re, natCast_re]
  field_simp

/-- `∫₀¹ ∑_{k ≥ m} (-1)ᵏ t^{z+k-1}/k! dt = ∑_{k ≥ m} (-1)ᵏ/((z+k) k!)` when `Re z + m > 0`. -/
theorem integral_tsum_prymTerm {z : ℂ} {m : ℕ} (hm : 0 < z.re + m) :
    ∫ t in Ioc (0 : ℝ) 1, ∑' j : ℕ, prymTerm z (j + m) t =
      ∑' j : ℕ, (-1 : ℂ) ^ (j + m) / ((z + (j + m : ℕ)) * (j + m).factorial) := by
  have hk : ∀ j : ℕ, 0 < (z + (j + m : ℕ)).re := fun j => by
    have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
    simp only [add_re, natCast_re, Nat.cast_add]
    linarith
  have hsum : Summable fun j : ℕ => ∫ t in Ioc (0 : ℝ) 1, ‖prymTerm z (j + m) t‖ := by
    simp_rw [integral_norm_prymTerm (hk _)]
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
      ((Real.summable_pow_div_factorial 1).mul_left (1 / (z.re + m)))
    · have := hk j; positivity
    · have hf : (0 : ℝ) < j.factorial := by exact_mod_cast j.factorial_pos
      have hf' : (j.factorial : ℝ) ≤ (j + m).factorial := by
        exact_mod_cast Nat.factorial_le (Nat.le_add_right j m)
      have hre : z.re + m ≤ (z + (j + m : ℕ)).re := by
        have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
        simp only [add_re, natCast_re, Nat.cast_add]
        linarith
      rw [one_pow, div_mul_div_comm, one_mul, one_div_le_one_div (by have := hk j; positivity)
        (by positivity)]
      nlinarith [mul_le_mul hf' hre hm.le (by positivity : (0 : ℝ) ≤ (j + m).factorial)]
  rw [← integral_tsum_of_summable_integral_norm (fun j => integrableOn_prymTerm (hk j)) hsum]
  exact tsum_congr fun j => integral_prymTerm (hk j)

/-- `t^{z-1} e^{-t} = ∑ₖ (-1)ᵏ t^{z+k-1}/k!` for `t > 0`. -/
theorem hasSum_prymTerm (z : ℂ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun k => prymTerm z k t) ((t : ℂ) ^ (z - 1) * Complex.exp (-(t : ℂ))) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hexp : HasSum (fun k : ℕ => (-(t : ℂ)) ^ k / k.factorial) (Complex.exp (-(t : ℂ))) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  convert hexp.mul_left ((t : ℂ) ^ (z - 1)) using 1
  funext k
  simp only [prymTerm]
  rw [show z + k - 1 = (z - 1) + k by ring, cpow_add _ _ ht0, cpow_natCast, neg_pow]
  ring

/-- Prym's formula for `Re z > 0`. -/
theorem Gamma_eq_prym_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    Complex.Gamma z = prymIntegral z + prymSeries z := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral]
  have hint : IntegrableOn (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ (z - 1)) (Ioi 0) :=
    Complex.GammaIntegral_convergent hz
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi zero_le_one)), add_comm]
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    push_cast
    ring
  have h := integral_tsum_prymTerm (z := z) (m := 0) (by simpa using hz)
  simp only [add_zero] at h
  rw [prymSeries, ← h]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  rw [(hasSum_prymTerm z ht.1).tsum_eq]
  push_cast
  ring

/-- Prym's formula for all `z ∉ -ℕ`, via the recursion of `Γ`. -/
theorem Gamma_eq_prym {z : ℂ} (hz : ∀ k : ℕ, z ≠ -k) :
    Complex.Gamma z = prymIntegral z + prymSeries z := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-z.re)
  induction n generalizing z with
  | zero => exact Gamma_eq_prym_of_re_pos (by simpa using hn)
  | succ n ih =>
    have hz1 : ∀ k : ℕ, z + 1 ≠ -k := fun k h =>
      hz (k + 1) (by push_cast; linear_combination h)
    have h1 := ih hz1 (by simp only [add_re, one_re]; push_cast at hn; linarith)
    have hz0 : z ≠ 0 := by simpa using hz 0
    have hP : prymIntegral (z + 1) + prymSeries (z + 1) =
        z * (prymIntegral z + prymSeries z) := by
      rw [prymIntegral_add_one, mul_add, mul_prymSeries hz]; ring
    have hG := Complex.Gamma_add_one z hz0
    rw [h1, hP] at hG
    exact (mul_left_cancel₀ hz0 hG).symm

/-- DLMF 5.9.4, Prym's decomposition: `Γ(z) = ∫₁^∞ t^(z-1) e^(-t) dt + ∑ₖ (-1)^k/((z + k) k!)` for
`z` not a nonpositive integer. -/
@[dlmf 5.9.E4]
theorem Gamma_incomplete_sum {z : ℂ} (hz : ∀ k : ℕ, z ≠ -k) :
    Complex.Gamma z =
      (∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (z - 1) * Complex.exp (-(t : ℂ))) +
        ∑' k : ℕ, (-1 : ℂ) ^ k / ((z + k) * k.factorial) := by
  simpa only [prymIntegral, prymSeries] using Gamma_eq_prym hz

end Prym

open Set in
/-- The Cauchy–Saalschütz representation (Temme §3.2.2), from Prym's formula: on `(1, ∞)`
each power `t^{z+k-1}`, `k ≤ n`, integrates to `-1/(z+k)`, and on `(0, 1]` the tail of the
exponential series integrates to the remaining terms of Prym's series. -/
@[dlmf 5.9.E5]
theorem Gamma_truncated_exp {z : ℂ} {n : ℕ}
    (hlo : -((n + 1 : ℕ) : ℝ) < z.re) (hhi : z.re < -n) :
    Complex.Gamma z =
      ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (z - 1) *
          (Complex.exp (-(t : ℂ)) -
            ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (t : ℂ) ^ k / k.factorial) := by
  push_cast at hlo
  have hz : ∀ k : ℕ, z ≠ -k := by
    intro k hk
    have h := congrArg Complex.re hk
    simp only [neg_re, natCast_re] at h
    rw [h] at hlo hhi
    have h1 : (n : ℝ) < k := by linarith
    have h2 : (k : ℝ) < n + 1 := by linarith
    have h1' : n < k := by exact_mod_cast h1
    have h2' : k < n + 1 := by exact_mod_cast h2
    omega
  -- the integrand
  set f : ℝ → ℂ := fun t => (t : ℂ) ^ (z - 1) * (Complex.exp (-(t : ℂ)) -
    ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (t : ℂ) ^ k / k.factorial) with hf
  have hfk : ∀ t : ℝ, 0 < t → f t = (t : ℂ) ^ (z - 1) * Complex.exp (-(t : ℂ)) -
      ∑ k ∈ Finset.range (n + 1), prymTerm z k t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    simp only [hf, mul_sub, Finset.mul_sum, prymTerm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show z + k - 1 = (z - 1) + k by ring, cpow_add _ _ ht0, cpow_natCast]
    ring
  -- on `(0, 1]`: the tail of the series
  have htail : ∀ t ∈ Ioc (0 : ℝ) 1, f t = ∑' j : ℕ, prymTerm z (j + (n + 1)) t := by
    intro t ht
    rw [hfk t ht.1, ← (hasSum_prymTerm z ht.1).tsum_eq,
      ← (hasSum_prymTerm z ht.1).summable.sum_add_tsum_nat_add (n + 1)]
    ring
  have hm : 0 < z.re + (n + 1 : ℕ) := by push_cast; linarith
  -- on `(1, ∞)`: Euler's integral minus finitely many powers
  have hpow : ∀ k ∈ Finset.range (n + 1), IntegrableOn (prymTerm z k) (Ioi 1) ∧
      ∫ t in Ioi (1 : ℝ), prymTerm z k t = -((-1 : ℂ) ^ k / ((z + k) * k.factorial)) := by
    intro k hk
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hre : (z + k - 1).re < -1 := by simp; linarith
    have hzk : z + k ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hf' : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    refine ⟨(integrableOn_Ioi_cpow_of_lt hre zero_lt_one).const_mul _, ?_⟩
    simp only [prymTerm]
    rw [MeasureTheory.integral_const_mul, integral_Ioi_cpow_of_lt hre zero_lt_one, sub_add_cancel,
      ofReal_one, one_cpow]
    field_simp
  have hint1 : IntegrableOn f (Ioi 1) := by
    have := (integrableOn_prymIntegral z).sub (integrable_finsetSum _ fun k hk => (hpow k hk).1)
    refine IntegrableOn.congr_fun this (fun t ht => ?_) measurableSet_Ioi
    rw [hfk t (zero_lt_one.trans ht)]
    simp
  have hint0 : IntegrableOn f (Ioc 0 1) := by
    -- `|e^{-t} - Pₙ(t)| ≤ C t^{n+1}` on `(0, 1]`
    set C : ℝ := ((n + 1 : ℕ).succ : ℝ) / ((n + 1).factorial * (n + 1 : ℕ))
    have hrpow : IntegrableOn (fun t : ℝ => C * t ^ (z.re + n)) (Ioc 0 1) := by
      have hre : -1 < z.re + n := by linarith
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hre).const_mul C
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    refine hrpow.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioc
      exact ((continuousAt_ofReal_cpow_const t (z - 1) (Or.inr ht.1.ne')).mul
        (by fun_prop : Continuous fun t : ℝ => Complex.exp (-(t : ℂ)) -
          ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (t : ℂ) ^ k / k.factorial).continuousAt)
        |>.continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
      have ht0 : 0 < t := ht.1
      have hreal : Complex.exp (-(t : ℂ)) -
          ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (t : ℂ) ^ k / k.factorial =
          ((Real.exp (-t) - ∑ k ∈ Finset.range (n + 1), (-t) ^ k / k.factorial : ℝ) : ℂ) := by
        push_cast
        congr 1
        refine Finset.sum_congr rfl fun k _ => by ring
      have hb := Real.exp_bound (x := -t) (by rw [abs_neg, abs_of_pos ht0]; exact ht.2)
        (n := n + 1) (Nat.succ_pos n)
      rw [abs_neg, abs_of_pos ht0] at hb
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, hreal, Complex.norm_real, Real.norm_eq_abs]
      have hpow' : t ^ (n + 1) = t * t ^ (n : ℝ) := by
        rw [Real.rpow_natCast]; ring
      calc t ^ (z - 1).re * |Real.exp (-t) - ∑ k ∈ Finset.range (n + 1), (-t) ^ k / k.factorial|
          ≤ t ^ (z - 1).re * (t ^ (n + 1) * C) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = C * t ^ (z.re + n) := by
            rw [hpow', sub_re, one_re, Real.rpow_add ht0, Real.rpow_sub_one ht0.ne']
            field_simp
  -- assemble
  have hΓ : Complex.Gamma z = prymIntegral z + prymSeries z := Gamma_eq_prym hz
  rw [hΓ, prymSeries, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint0 hint1,
    setIntegral_congr_fun measurableSet_Ioc htail, integral_tsum_prymTerm hm]
  have h1 : ∫ t in Ioi (1 : ℝ), f t = prymIntegral z +
      ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k / ((z + k) * k.factorial) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
        (fun t (ht : 1 < t) => hfk t (zero_lt_one.trans ht)),
      integral_sub (integrableOn_prymIntegral z)
        (integrable_finsetSum _ fun k hk => (hpow k hk).1),
      integral_finsetSum _ fun k hk => (hpow k hk).1, prymIntegral,
      Finset.sum_congr rfl fun k hk => (hpow k hk).2, Finset.sum_neg_distrib, sub_neg_eq_add]
  rw [h1, ← (summable_prym z).sum_add_tsum_nat_add (n + 1)]
  push_cast
  ring

section Oscillatory

/-! ### Oscillatory integrals (DLMF 5.9.6–9)

For `x < 1` and `t > 0` we write `t^{x-1} = Γ(1-x)⁻¹ ∫₀^∞ s^{-x} e^{-ts} ds` and exchange the
order of integration over `(0, R) × (0, ∞)`. The inner integrals `∫₀^R e^{-st} cos t dt` and
`∫₀^R e^{-st} sin t dt` are elementary, and dominated convergence as `R → ∞` leaves the Mellin
transform `∫₀^∞ s^{a-1}/(1+s²) ds = π/(2 sin(πa/2))`, itself the beta integral
`∫₀^∞ u^{b-1}/(1+u) du = Γ(b) Γ(1-b)`. -/

open Set

/-- `∫₀^∞ u^{b-1}/(1+u) du = Γ(b) Γ(1-b)` for `0 < b < 1`, via
`1/(1+u) = ∫₀^∞ e^{-(1+u)r} dr` and Fubini. -/
theorem integral_rpow_div_one_add {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    IntegrableOn (fun u : ℝ => u ^ (b - 1) / (1 + u)) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), u ^ (b - 1) / (1 + u) = Real.Gamma b * Real.Gamma (1 - b) := by
  set μ := volume.restrict (Ioi (0 : ℝ))
  set f : ℝ → ℝ → ℝ := fun u r => u ^ (b - 1) * Real.exp (-((1 + u) * r)) with hf
  have hnn : ∀ u r : ℝ, 0 < u → 0 ≤ f u r := fun u r hu => by simp only [hf]; positivity
  -- inner integral in `u`
  have hinner_u : ∀ r : ℝ, 0 < r → IntegrableOn (fun u => f u r) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), f u r = Real.exp (-r) * (r ^ (-b) * Real.Gamma b) := by
    intro r hr
    have hconv := (Real.GammaIntegral_convergent hb0)
    have heq : ∀ u : ℝ, f u r = Real.exp (-r) * (u ^ (b - 1) * Real.exp (-(r * u))) := by
      intro u; simp only [hf]; rw [mul_left_comm, ← Real.exp_add]; ring_nf
    have hint : IntegrableOn (fun u : ℝ => u ^ (b - 1) * Real.exp (-(r * u))) (Ioi 0) := by
      have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := b - 1) (b := r)
        (by linarith) one_pos hr
      refine IntegrableOn.congr_fun this (fun u _ => ?_) measurableSet_Ioi
      simp [Real.rpow_one]
    refine ⟨IntegrableOn.congr_fun (hint.const_mul (Real.exp (-r))) (fun u _ => (heq u).symm)
      measurableSet_Ioi, ?_⟩
    simp_rw [heq]
    rw [MeasureTheory.integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hb0 hr,
      Real.rpow_neg hr.le, one_div, Real.inv_rpow hr.le]
  -- inner integral in `r`
  have hinner_r : ∀ u : ℝ, 0 < u → ∫ r in Ioi (0 : ℝ), f u r = u ^ (b - 1) / (1 + u) := by
    intro u hu
    have hm : -(1 + u) < 0 := by linarith
    simp only [hf]
    rw [MeasureTheory.integral_const_mul]
    have := integral_exp_mul_Ioi hm 0
    simp only [mul_zero, Real.exp_zero] at this
    rw [show (fun r => Real.exp (-((1 + u) * r))) = fun r => Real.exp (-(1 + u) * r) by
      funext r; ring_nf, this]
    field_simp
  have hmeas : AEStronglyMeasurable (Function.uncurry f) (μ.prod μ) :=
    (by fun_prop : Measurable fun p : ℝ × ℝ =>
      p.1 ^ (b - 1) * Real.exp (-((1 + p.1) * p.2))).aestronglyMeasurable
  have hprod : Integrable (Function.uncurry f) (μ.prod μ) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact (hinner_u r hr).1
    · have hG := (Real.GammaIntegral_convergent (by linarith : 0 < 1 - b)).const_mul
        (Real.Gamma b)
      refine IntegrableOn.congr_fun hG (fun r hr => ?_) measurableSet_Ioi
      have hr' : (0 : ℝ) < r := hr
      simp only [Function.uncurry_apply_pair]
      rw [setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) =>
        Real.norm_of_nonneg (hnn u r hu), (hinner_u r hr').2]
      rw [show (1 - b - 1) = -b by ring]
      ring
  have hswap := integral_integral_swap hprod
  have hL : ∫ u in Ioi (0 : ℝ), ∫ r in Ioi (0 : ℝ), f u r =
      ∫ u in Ioi (0 : ℝ), u ^ (b - 1) / (1 + u) :=
    setIntegral_congr_fun measurableSet_Ioi fun u hu => hinner_r u hu
  have hR : ∫ r in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), f u r = Real.Gamma b * Real.Gamma (1 - b) := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => (hinner_u r hr).2,
      Real.Gamma_eq_integral (by linarith : 0 < 1 - b), ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    rw [show (1 - b - 1) = -b by ring]
    ring
  refine ⟨?_, by rw [← hL, hswap, hR]⟩
  have := hprod.integral_prod_left
  exact IntegrableOn.congr_fun this (fun u hu => hinner_r u hu) measurableSet_Ioi

/-- `∫₀^∞ s^{a-1}/(1+s²) ds = π/(2 sin(πa/2))` for `0 < a < 2`. -/
theorem integral_rpow_div_one_add_sq {a : ℝ} (ha0 : 0 < a) (ha2 : a < 2) :
    IntegrableOn (fun s : ℝ => s ^ (a - 1) / (1 + s ^ 2)) (Ioi 0) ∧
      ∫ s in Ioi (0 : ℝ), s ^ (a - 1) / (1 + s ^ 2) = π / (2 * Real.sin (π * a / 2)) := by
  obtain ⟨hint, hval⟩ := integral_rpow_div_one_add (b := a / 2) (by positivity) (by linarith)
  set g : ℝ → ℝ := fun u => u ^ (a / 2 - 1) / (1 + u) with hg
  have heq : EqOn (fun s : ℝ => (|(2 : ℝ)| * s ^ ((2 : ℝ) - 1)) • g (s ^ (2 : ℝ)))
      (fun s => 2 * (s ^ (a - 1) / (1 + s ^ 2))) (Ioi 0) := by
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    simp only [hg, smul_eq_mul, Real.rpow_two, abs_two]
    rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs'.le]
    push_cast
    rw [show (2 : ℝ) * (a / 2 - 1) = a - 2 by ring, show (2 : ℝ) - 1 = 1 by norm_num,
      Real.rpow_one, show a - 1 = 1 + (a - 2) by ring, Real.rpow_add hs', Real.rpow_one]
    ring
  have hint' : IntegrableOn (fun s : ℝ => 2 * (s ^ (a - 1) / (1 + s ^ 2))) (Ioi 0) :=
    ((integrableOn_Ioi_comp_rpow_iff g two_ne_zero).mpr hint).congr_fun heq measurableSet_Ioi
  refine ⟨IntegrableOn.congr_fun (hint'.const_mul (1 / 2)) (fun s _ => by ring)
    measurableSet_Ioi, ?_⟩
  have h := integral_comp_rpow_Ioi g (two_ne_zero : (2 : ℝ) ≠ 0)
  rw [setIntegral_congr_fun measurableSet_Ioi heq, MeasureTheory.integral_const_mul, hg,
    hval, Real.Gamma_mul_Gamma_one_sub, show π * (a / 2) = π * a / 2 by ring] at h
  have hs : Real.sin (π * a / 2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi (by positivity)
    (by nlinarith [Real.pi_pos])).ne'
  rw [eq_div_iff (mul_ne_zero two_ne_zero hs)]
  rw [eq_div_iff hs] at h
  linarith

/-- `t^{x-1} = Γ(1-x)⁻¹ ∫₀^∞ s^{-x} e^{-ts} ds` for `x < 1`, `t > 0`. -/
theorem rpow_eq_recip_Gamma_mul_integral {x t : ℝ} (hx : x < 1) (ht : 0 < t) :
    t ^ (x - 1) = (Real.Gamma (1 - x))⁻¹ *
      ∫ s in Ioi (0 : ℝ), s ^ (-x) * Real.exp (-(t * s)) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 - x) (r := t) (by linarith) ht
  rw [show (1 - x - 1) = -x by ring] at h
  rw [h, one_div, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, neg_sub]
  have := (Real.Gamma_pos_of_pos (by linarith : 0 < 1 - x)).ne'
  field_simp

/-- `s^(-x) e^(-ts)` is integrable on `(0, ∞)` for `x < 1`, `t > 0`. -/
theorem integrableOn_rpow_neg_mul_exp {x t : ℝ} (hx : x < 1) (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => s ^ (-x) * Real.exp (-(t * s))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -x) (b := t) (by linarith)
    one_pos ht
  refine IntegrableOn.congr_fun this (fun u _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one]

/-- Fubini for `∫₀^R t^{x-1} g(t) dt`. -/
theorem integral_rpow_mul_eq {x R : ℝ} (hx : x < 1) (hR : 0 ≤ R) {g : ℝ → ℝ} (hg : Continuous g)
    (hint : IntegrableOn (fun t => |g t| * t ^ (x - 1)) (Ioc 0 R)) :
    ∫ t in (0 : ℝ)..R, t ^ (x - 1) * g t = (Real.Gamma (1 - x))⁻¹ *
      ∫ s in Ioi (0 : ℝ), s ^ (-x) * ∫ t in (0 : ℝ)..R, Real.exp (-(s * t)) * g t := by
  set μ := volume.restrict (Ioc (0 : ℝ) R)
  set ν := volume.restrict (Ioi (0 : ℝ))
  set F : ℝ → ℝ → ℝ := fun t s => s ^ (-x) * Real.exp (-(t * s)) * g t with hF
  have hG := Real.Gamma_pos_of_pos (by linarith : 0 < 1 - x)
  have hinner : ∀ t : ℝ, 0 < t → ∫ s in Ioi (0 : ℝ), s ^ (-x) * Real.exp (-(t * s)) =
      Real.Gamma (1 - x) * t ^ (x - 1) := by
    intro t ht
    rw [rpow_eq_recip_Gamma_mul_integral hx ht]
    field_simp
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν) :=
    (by fun_prop : Measurable fun p : ℝ × ℝ =>
      p.2 ^ (-x) * Real.exp (-(p.1 * p.2)) * g p.1).aestronglyMeasurable
  have hprod : Integrable (Function.uncurry F) (μ.prod ν) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (integrableOn_rpow_neg_mul_exp hx ht.1).mul_const (g t)
    · refine IntegrableOn.congr_fun (hint.const_mul (Real.Gamma (1 - x))) (fun t ht => ?_)
        measurableSet_Ioc
      simp only [Function.uncurry_apply_pair, hF]
      rw [setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => by
          rw [norm_mul, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs],
        MeasureTheory.integral_mul_const, hinner t ht.1]
      ring
  have hswap := integral_integral_swap hprod
  rw [intervalIntegral.integral_of_le hR]
  have hL : ∫ t in Ioc (0 : ℝ) R, ∫ s in Ioi (0 : ℝ), F t s =
      Real.Gamma (1 - x) * ∫ t in Ioc (0 : ℝ) R, t ^ (x - 1) * g t := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    simp only [hF]
    rw [MeasureTheory.integral_mul_const, hinner t ht.1]
    ring
  have hR' : ∫ s in Ioi (0 : ℝ), ∫ t in Ioc (0 : ℝ) R, F t s =
      ∫ s in Ioi (0 : ℝ), s ^ (-x) * ∫ t in (0 : ℝ)..R, Real.exp (-(s * t)) * g t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [intervalIntegral.integral_of_le hR, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    simp only [hF]
    ring_nf
  rw [hL, hR'] at hswap
  rw [← hswap]
  field_simp

/-- `∫₀^R e^{-st} cos t dt`. -/
theorem integral_exp_mul_cos {s R : ℝ} :
    ∫ t in (0 : ℝ)..R, Real.exp (-(s * t)) * Real.cos t =
      (s - Real.exp (-(s * R)) * (s * Real.cos R - Real.sin R)) / (s ^ 2 + 1) := by
  have hd : ∀ t ∈ uIcc 0 R, HasDerivAt
      (fun t => Real.exp (-(s * t)) * (Real.sin t - s * Real.cos t) / (s ^ 2 + 1))
      (Real.exp (-(s * t)) * Real.cos t) t := by
    intro t _
    have := ((((hasDerivAt_id t).const_mul s).neg.exp).mul
      ((Real.hasDerivAt_sin t).sub ((Real.hasDerivAt_cos t).const_mul s))).div_const (s ^ 2 + 1)
    have hs2 : s ^ 2 + 1 ≠ 0 := by positivity
    have hs2' : 1 + s ^ 2 ≠ 0 := by positivity
    exact this.congr_deriv (by deriv_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t => Real.exp (-(s * t)) * Real.cos t).intervalIntegrable _ _)]
  simp only [mul_zero, neg_zero, Real.exp_zero, Real.sin_zero, Real.cos_zero]
  ring

/-- `∫₀^R e^{-st} sin t dt`. -/
theorem integral_exp_mul_sin {s R : ℝ} :
    ∫ t in (0 : ℝ)..R, Real.exp (-(s * t)) * Real.sin t =
      (1 - Real.exp (-(s * R)) * (s * Real.sin R + Real.cos R)) / (s ^ 2 + 1) := by
  have hd : ∀ t ∈ uIcc 0 R, HasDerivAt
      (fun t => -(Real.exp (-(s * t)) * (Real.cos t + s * Real.sin t)) / (s ^ 2 + 1))
      (Real.exp (-(s * t)) * Real.sin t) t := by
    intro t _
    have := ((((hasDerivAt_id t).const_mul s).neg.exp).mul
      ((Real.hasDerivAt_cos t).add ((Real.hasDerivAt_sin t).const_mul s))).neg.div_const
      (s ^ 2 + 1)
    have hs2 : s ^ 2 + 1 ≠ 0 := by positivity
    have hs2' : 1 + s ^ 2 ≠ 0 := by positivity
    exact this.congr_deriv (by deriv_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t => Real.exp (-(s * t)) * Real.sin t).intervalIntegrable _ _)]
  simp only [mul_zero, neg_zero, Real.exp_zero, Real.sin_zero, Real.cos_zero]
  ring

/-- Dominated convergence for `∫₀^∞ s^{-x} K(s, R) ds` as `R → ∞`, where
`K(s, R) = (p(s) - e^{-sR} q(s, R))/(s² + 1)` with `|q(s, R)| ≤ s + 1`. -/
theorem tendsto_integral_rpow_neg_mul_kernel {x : ℝ} (hx : x < 1) {p : ℝ → ℝ}
    {q : ℝ → ℝ → ℝ} (hp : Continuous p) (hq : Continuous (Function.uncurry q))
    (hqb : ∀ s R, 0 < s → |q s R| ≤ s + 1)
    (hpint : IntegrableOn (fun s : ℝ => s ^ (-x) * (|p s| / (s ^ 2 + 1))) (Ioi 0)) :
    Tendsto (fun R : ℝ => ∫ s in Ioi (0 : ℝ),
        s ^ (-x) * ((p s - Real.exp (-(s * R)) * q s R) / (s ^ 2 + 1))) atTop
      (𝓝 (∫ s in Ioi (0 : ℝ), s ^ (-x) * (p s / (s ^ 2 + 1)))) := by
  have hb2 := (Real.GammaIntegral_convergent (by linarith : 0 < 2 - x))
  have hb1 := (Real.GammaIntegral_convergent (by linarith : 0 < 1 - x))
  have hbint : Integrable (fun s : ℝ => s ^ (-x) * (|p s| / (s ^ 2 + 1)) +
      (Real.exp (-s) * s ^ (2 - x - 1) + Real.exp (-s) * s ^ (1 - x - 1)))
      (volume.restrict (Ioi 0)) := hpint.add (hb2.add hb1)
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun s => s ^ (-x) * (|p s| / (s ^ 2 + 1)) +
      (Real.exp (-s) * s ^ (2 - x - 1) + Real.exp (-s) * s ^ (1 - x - 1))) ?_ ?_ hbint ?_
  · exact Eventually.of_forall fun R => (by fun_prop : Measurable fun s : ℝ =>
      s ^ (-x) * ((p s - Real.exp (-(s * R)) * q s R) / (s ^ 2 + 1))).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 1] with R hR
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : (0 : ℝ) < s := hs
    have hsx : 0 < s ^ (-x) := Real.rpow_pos_of_pos hs' _
    have hd : (0 : ℝ) < s ^ 2 + 1 := by positivity
    have he : Real.exp (-(s * R)) ≤ Real.exp (-s) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hq' := hqb s R hs'
    have hpow2 : s ^ (2 - x - 1) = s ^ (-x) * s := by
      rw [show 2 - x - 1 = -x + 1 by ring, Real.rpow_add hs', Real.rpow_one]
    have hpow1 : s ^ (1 - x - 1) = s ^ (-x) := by ring_nf
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hsx, abs_div, abs_of_pos hd, hpow2, hpow1]
    have h1 : |p s - Real.exp (-(s * R)) * q s R| ≤ |p s| + Real.exp (-s) * (s + 1) := by
      calc |p s - Real.exp (-(s * R)) * q s R|
          ≤ |p s| + |Real.exp (-(s * R)) * q s R| := abs_sub _ _
        _ ≤ |p s| + Real.exp (-s) * (s + 1) := by
          rw [abs_mul, Real.abs_exp]
          gcongr
    have h2 : Real.exp (-s) * (s + 1) / (s ^ 2 + 1) ≤ Real.exp (-s) * (s + 1) :=
      div_le_self (by positivity) (by nlinarith)
    calc s ^ (-x) * (|p s - Real.exp (-(s * R)) * q s R| / (s ^ 2 + 1))
        ≤ s ^ (-x) * ((|p s| + Real.exp (-s) * (s + 1)) / (s ^ 2 + 1)) := by gcongr
      _ = s ^ (-x) * (|p s| / (s ^ 2 + 1)) + s ^ (-x) *
          (Real.exp (-s) * (s + 1) / (s ^ 2 + 1)) := by ring
      _ ≤ s ^ (-x) * (|p s| / (s ^ 2 + 1)) + s ^ (-x) * (Real.exp (-s) * (s + 1)) := by gcongr
      _ = _ := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : (0 : ℝ) < s := hs
    have hexp : Tendsto (fun R => Real.exp (-(s * R))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun R : ℝ => s * R) atTop atTop :=
        Tendsto.const_mul_atTop hs' tendsto_id
      have := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
      simpa [Function.comp_def] using this
    have hbdd : Tendsto (fun R => Real.exp (-(s * R)) * q s R) atTop (𝓝 0) := by
      refine hexp.zero_mul_isBoundedUnder_le ?_
      exact isBoundedUnder_of_eventually_le (a := s + 1)
        (Eventually.of_forall fun R => by simpa [Real.norm_eq_abs] using hqb s R hs')
    have := ((tendsto_const_nhds (x := p s)).sub hbdd).div_const (s ^ 2 + 1) |>.const_mul
      (s ^ (-x))
    simpa using this

/-- `∫₀^R t^{x-1} cos t dt → π/(2 Γ(1-x) sin(πx/2))` for `0 < x < 1`. -/
theorem tendsto_integral_rpow_mul_cos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, t ^ (x - 1) * Real.cos t) atTop
      (𝓝 ((Real.Gamma (1 - x))⁻¹ * (π / (2 * Real.sin (π * (2 - x) / 2))))) := by
  obtain ⟨hM, hval⟩ := integral_rpow_div_one_add_sq (a := 2 - x) (by linarith) (by linarith)
  have hpint : IntegrableOn (fun s : ℝ => s ^ (-x) * (|s| / (s ^ 2 + 1))) (Ioi 0) := by
    refine IntegrableOn.congr_fun hM (fun s hs => ?_) measurableSet_Ioi
    have hs' : (0 : ℝ) < s := hs
    show s ^ (2 - x - 1) / (1 + s ^ 2) = s ^ (-x) * (|s| / (s ^ 2 + 1))
    rw [abs_of_pos hs', show 2 - x - 1 = -x + 1 by ring, Real.rpow_add hs', Real.rpow_one]
    ring
  have hlim := tendsto_integral_rpow_neg_mul_kernel hx1 (p := fun s => s)
    (q := fun s R => s * Real.cos R - Real.sin R) continuous_id (by fun_prop)
    (fun s R hs => by
      have := abs_sub (s * Real.cos R) (Real.sin R)
      rw [abs_mul, abs_of_pos hs] at this
      nlinarith [Real.abs_cos_le_one R, Real.abs_sin_le_one R]) hpint
  have hval' : ∫ s in Ioi (0 : ℝ), s ^ (-x) * (s / (s ^ 2 + 1)) =
      π / (2 * Real.sin (π * (2 - x) / 2)) := by
    rw [← hval]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs' : (0 : ℝ) < s := hs
    rw [show 2 - x - 1 = -x + 1 by ring, Real.rpow_add hs', Real.rpow_one]
    ring
  rw [hval'] at hlim
  refine (hlim.const_mul (Real.Gamma (1 - x))⁻¹).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  have hint : IntegrableOn (fun t => |Real.cos t| * t ^ (x - 1)) (Ioc 0 R) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := R)
      (by linarith : -1 < x - 1))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR] at this
    refine this.mono' ((by fun_prop : Measurable fun t =>
      |Real.cos t| * t ^ (x - 1)).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.rpow_pos_of_pos ht.1 _)]
    exact mul_le_of_le_one_left (Real.rpow_pos_of_pos ht.1 _).le (Real.abs_cos_le_one t)
  rw [integral_rpow_mul_eq hx1 hR Real.continuous_cos hint]
  simp_rw [integral_exp_mul_cos]

/-- `∫₀^R t^{x-1} sin t dt → π/(2 Γ(1-x) cos(πx/2))` for `-1 < x < 1`. -/
theorem tendsto_integral_rpow_mul_sin {x : ℝ} (hx0 : -1 < x) (hx1 : x < 1) :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, t ^ (x - 1) * Real.sin t) atTop
      (𝓝 ((Real.Gamma (1 - x))⁻¹ * (π / (2 * Real.sin (π * (1 - x) / 2))))) := by
  obtain ⟨hM, hval⟩ := integral_rpow_div_one_add_sq (a := 1 - x) (by linarith) (by linarith)
  have hpint : IntegrableOn (fun s : ℝ => s ^ (-x) * (|(1 : ℝ)| / (s ^ 2 + 1))) (Ioi 0) := by
    refine IntegrableOn.congr_fun hM (fun s _ => ?_) measurableSet_Ioi
    show s ^ (1 - x - 1) / (1 + s ^ 2) = s ^ (-x) * (|(1 : ℝ)| / (s ^ 2 + 1))
    rw [abs_one, show 1 - x - 1 = -x by ring]
    ring
  have hlim := tendsto_integral_rpow_neg_mul_kernel hx1 (p := fun _ => 1)
    (q := fun s R => s * Real.sin R + Real.cos R) continuous_const (by fun_prop)
    (fun s R hs => by
      have := abs_add_le (s * Real.sin R) (Real.cos R)
      rw [abs_mul, abs_of_pos hs] at this
      nlinarith [Real.abs_cos_le_one R, Real.abs_sin_le_one R]) hpint
  have hval' : ∫ s in Ioi (0 : ℝ), s ^ (-x) * (1 / (s ^ 2 + 1)) =
      π / (2 * Real.sin (π * (1 - x) / 2)) := by
    rw [← hval]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [show 1 - x - 1 = -x by ring]
    ring
  rw [hval'] at hlim
  refine (hlim.const_mul (Real.Gamma (1 - x))⁻¹).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  have hint : IntegrableOn (fun t => |Real.sin t| * t ^ (x - 1)) (Ioc 0 R) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := R) hx0)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR] at this
    refine this.mono' ((by fun_prop : Measurable fun t =>
      |Real.sin t| * t ^ (x - 1)).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    have ht' : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.rpow_pos_of_pos ht' _)]
    have h1 : |Real.sin t| ≤ t := by simpa [abs_of_pos ht'] using Real.abs_sin_le_abs (x := t)
    calc |Real.sin t| * t ^ (x - 1) ≤ t * t ^ (x - 1) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_pos_of_pos ht' _).le
      _ = t ^ x := by
          rw [Real.rpow_sub_one ht'.ne']; field_simp
  rw [integral_rpow_mul_eq hx1 hR Real.continuous_sin hint]
  simp_rw [integral_exp_mul_sin]

/-- A cosine integral for Gamma. The integral converges only conditionally at infinity, so it is
stated as the limit of integrals over `(0, R)`; Lean's integral over `(0, ∞)` would be `0`. -/
@[dlmf 5.9.E6]
theorem Gamma_cos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun R : ℝ => ∫ t : ℝ in (0 : ℝ)..R, t ^ (x - 1) * Real.cos t) atTop
      (𝓝 (Real.Gamma x * Real.cos (π * x / 2))) := by
  convert tendsto_integral_rpow_mul_cos hx0 hx1 using 2
  have hrefl := Real.Gamma_mul_Gamma_one_sub x
  have hs : 0 < Real.sin (π * x / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hc : 0 < Real.cos (π * x / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hG := Real.Gamma_pos_of_pos (by linarith : 0 < 1 - x)
  have h2 : Real.sin (π * (2 - x) / 2) = Real.sin (π * x / 2) := by
    rw [show π * (2 - x) / 2 = π - π * x / 2 by ring, Real.sin_pi_sub]
  have hdbl : Real.sin (π * x) = 2 * Real.sin (π * x / 2) * Real.cos (π * x / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  rw [h2]
  set S := Real.sin (π * x / 2)
  set C := Real.cos (π * x / 2)
  have hΓx : Real.Gamma x = π / (2 * S * C) / Real.Gamma (1 - x) := by
    rw [eq_div_iff hG.ne', hrefl, hdbl]
  rw [hΓx]
  field_simp

/-- A sine integral for Gamma, with the removable value `π/2` at `x = 0`.
The former literal product `Gamma x * sin (π*x/2)` was false at zero because
`Real.Gamma 0 = 0`. Reflection gives the regular expression used here.
The limit formulation includes the conditionally convergent cases at infinity;
Lean's Bochner integral over `(0, ∞)` would return `0` in those cases. -/
@[dlmf 5.9.E7]
theorem Gamma_sin {x : ℝ} (hx0 : -1 < x) (hx1 : x < 1) :
    Tendsto (fun R : ℝ => ∫ t : ℝ in (0 : ℝ)..R, t ^ (x - 1) * Real.sin t) atTop
      (𝓝 (π / (2 * Real.Gamma (1 - x) * Real.cos (π * x / 2)))) := by
  convert tendsto_integral_rpow_mul_sin hx0 hx1 using 2
  have h1 : Real.sin (π * (1 - x) / 2) = Real.cos (π * x / 2) := by
    rw [show π * (1 - x) / 2 = π / 2 - π * x / 2 by ring, Real.sin_pi_div_two_sub]
  rw [h1]
  field_simp

/-- `∫₀^R g(tⁿ) dt = n⁻¹ ∫₀^{Rⁿ} u^{1/n - 1} g(u) du`. -/
theorem integral_comp_pow {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R) (g : ℝ → ℝ) :
    ∫ t in (0 : ℝ)..R, g (t ^ n) =
      (n : ℝ)⁻¹ * ∫ u in (0 : ℝ)..R ^ n, u ^ ((1 : ℝ) / n - 1) * g u := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hf' : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivWithinAt (fun t : ℝ => t ^ n)
      ((n : ℝ) * t ^ (n - 1)) (Ioo 0 R) t := fun t _ =>
    (hasDerivAt_pow n t).hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => t ^ n) (Ioo 0 R) := fun a ha b hb h =>
    (pow_left_inj₀ ha.1.le hb.1.le hn.ne').mp h
  have himg : (fun t : ℝ => t ^ n) '' Ioo 0 R = Ioo 0 (R ^ n) := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨pow_pos ht.1 n, pow_lt_pow_left₀ ht.2 ht.1.le hn.ne'⟩
    · rintro ⟨hu0, huR⟩
      refine ⟨u ^ ((1 : ℝ) / n), ⟨Real.rpow_pos_of_pos hu0 _, ?_⟩, ?_⟩
      · have := Real.rpow_lt_rpow hu0.le huR (by positivity : (0 : ℝ) < 1 / n)
        rwa [← Real.rpow_natCast, ← Real.rpow_mul hR.le, mul_one_div_cancel hn'.ne',
          Real.rpow_one] at this
      · simp only
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le, one_div_mul_cancel hn'.ne',
          Real.rpow_one]
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hf' hinj
    (fun u => u ^ ((1 : ℝ) / n - 1) * g u)
  rw [himg] at h
  rw [intervalIntegral.integral_of_le hR.le, intervalIntegral.integral_of_le (by positivity),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, h,
    ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have ht0 : 0 < t := ht.1
  simp only [smul_eq_mul]
  rw [abs_of_pos (by positivity), ← Real.rpow_natCast t n, ← Real.rpow_mul ht0.le,
    show (n : ℝ) * (1 / n - 1) = 1 - n by field_simp]
  rw [Real.rpow_sub ht0, Real.rpow_one, Real.rpow_natCast]
  have hpow : t ^ n = t * t ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hpow]
  have : t ^ (n - 1) ≠ 0 := by positivity
  field_simp

/-- The generalized Fresnel integrals reduce to `Gamma_cos`, `Gamma_sin` by `u = tⁿ`. -/
theorem tendsto_integral_comp_pow {n : ℕ} (hn : 2 ≤ n) {g : ℝ → ℝ} {L : ℝ}
    (hg : Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, t ^ ((1 : ℝ) / n - 1) * g t) atTop (𝓝 L)) :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, g (t ^ n)) atTop (𝓝 ((n : ℝ)⁻¹ * L)) := by
  have hn0 : 0 < n := by omega
  refine ((hg.comp (tendsto_pow_atTop hn0.ne')).const_mul (n : ℝ)⁻¹).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  rw [integral_comp_pow hn0 hR g]
  rfl

/-- The generalized Fresnel cosine integral. The integral converges only conditionally at infinity,
so it is stated as the limit of integrals over `(0, R)`; Lean's integral over `(0, ∞)` would be
`0`. -/
@[dlmf 5.9.E8]
theorem Gamma_cos_pow (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun R : ℝ => ∫ t : ℝ in (0 : ℝ)..R, Real.cos (t ^ n)) atTop
      (𝓝 (Real.Gamma (1 + 1 / n) * Real.cos (π / (2 * n)))) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < 1 / n := by positivity
  have hx1 : (1 : ℝ) / n < 1 := by rw [div_lt_one (by linarith)]; linarith
  convert tendsto_integral_comp_pow hn (Gamma_cos hx0 hx1) using 2
  rw [add_comm, Real.Gamma_add_one hx0.ne', show π * (1 / n) / 2 = π / (2 * n) by ring]
  field_simp

/-- The generalized Fresnel sine integral. The integral converges only conditionally at infinity, so
it is stated as the limit of integrals over `(0, R)`; Lean's integral over `(0, ∞)` would be
`0`. -/
@[dlmf 5.9.E9]
theorem Gamma_sin_pow (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun R : ℝ => ∫ t : ℝ in (0 : ℝ)..R, Real.sin (t ^ n)) atTop
      (𝓝 (Real.Gamma (1 + 1 / n) * Real.sin (π / (2 * n)))) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < 1 / n := by positivity
  have hx1 : (1 : ℝ) / n < 1 := by rw [div_lt_one (by linarith)]; linarith
  convert tendsto_integral_comp_pow hn (Gamma_sin (by linarith) hx1) using 2
  -- `π/(2 Γ(1-x) cos(πx/2)) = Γ(x) sin(πx/2)` by reflection
  have hrefl := Real.Gamma_mul_Gamma_one_sub (1 / n)
  have hs : 0 < Real.sin (π * (1 / n) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hc : 0 < Real.cos (π * (1 / n) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hG := Real.Gamma_pos_of_pos (by linarith : 0 < 1 - 1 / (n : ℝ))
  have hG' := Real.Gamma_pos_of_pos hx0
  have hdbl : Real.sin (π * (1 / n)) = 2 * Real.sin (π * (1 / n) / 2) *
      Real.cos (π * (1 / n) / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  rw [add_comm, Real.Gamma_add_one hx0.ne', show π / (2 * n) = π * (1 / n) / 2 by ring]
  set S := Real.sin (π * (1 / n) / 2)
  set C := Real.cos (π * (1 / n) / 2)
  have hΓx : Real.Gamma (1 / n) = π / (2 * S * C) / Real.Gamma (1 - 1 / n) := by
    rw [eq_div_iff hG.ne', hrefl, hdbl]
  rw [hΓx]
  field_simp

end Oscillatory

end DLMF.Gamma
end
end
