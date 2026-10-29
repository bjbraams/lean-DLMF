/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.Watson
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# Logarithmic moments for Watson's lemma

The logarithmic exponential moment is the order derivative of the Gamma integral.
Absolute convergence follows from Mathlib's Mellin differentiation criterion; a positive
dilation gives its exact dependence on the Laplace parameter.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped Topology

/-- The logarithmic Gamma integrand is absolutely integrable for positive order
and positive exponential decay. -/
theorem integrableOn_exp_neg_mul_rpow_sub_one_mul_log {s z : ℝ} (hs : 0 < s) (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => Real.exp (-z * t) * t ^ (s - 1) * Real.log t) (Ioi 0) := by
  let f : ℝ → ℂ := fun t => (Real.exp (-z * t) : ℂ)
  have hc : Continuous f := by dsimp [f]; fun_prop
  have htop : f =O[atTop] (fun t : ℝ => t ^ (-(s + 1))) := by
    simpa only [f, Complex.isBigO_ofReal_left] using
      (isLittleO_exp_neg_mul_rpow_atTop hz (-(s + 1))).isBigO
  have hbot : f =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) :=
    isBigO_const_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) one_ne_zero
  have hm := (mellin_hasDerivAt_of_isBigO_rpow (s := (s : ℂ)) (b := 0)
    (hc.continuousOn.locallyIntegrableOn measurableSet_Ioi) htop
    (by simp) (by simpa using hbot) (by simpa using hs)).1
  have hr := hm.re
  refine hr.congr_fun (fun t ht => ?_) measurableSet_Ioi
  change (((t : ℂ) ^ ((s : ℂ) - 1) *
    ((Real.log t : ℂ) * (Real.exp (-z * t) : ℂ))).re) = _
  rw [show (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow ht.le]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- The logarithmic exponential moment equals
`x⁻ˢ (Γ'(s) - log x Γ(s))` for positive order and Laplace parameter. -/
theorem integral_exp_neg_mul_rpow_sub_one_mul_log {s z : ℝ} (hs : 0 < s) (hz : 0 < z) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-z * t) * t ^ (s - 1) * Real.log t) =
      (deriv Real.Gamma s - Real.log z * Real.Gamma s) * z ^ (-s) := by
  have hG : (∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ (s - 1) * Real.log t) =
      deriv Real.Gamma s := by
    rw [(Real.hasDerivAt_Gamma_of_pos hs).deriv]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    ring
  have hlog := integrableOn_exp_neg_mul_rpow_sub_one_mul_log hs (by norm_num : (0 : ℝ) < 1)
  have hbase := integrableOn_exp_neg_mul_mul_rpow_sub_one hs (by norm_num : (0 : ℝ) < 1)
  simp only [one_mul, neg_mul] at hlog hbase
  have hsub := integral_comp_mul_left_Ioi
    (fun u : ℝ => Real.exp (-u) * u ^ (s - 1) * (Real.log u - Real.log z)) 0 hz
  rw [mul_zero] at hsub
  have heq : (∫ t in Ioi (0 : ℝ), Real.exp (-(z * t)) * (z * t) ^ (s - 1) *
      (Real.log (z * t) - Real.log z)) =
      z ^ (s - 1) * ∫ t in Ioi (0 : ℝ),
        Real.exp (-z * t) * t ^ (s - 1) * Real.log t := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [Real.mul_rpow hz.le ht.le, Real.log_mul hz.ne' ht.ne']
    ring
  rw [heq] at hsub
  have hright : (∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ (s - 1) *
      (Real.log u - Real.log z)) = deriv Real.Gamma s - Real.log z * Real.Gamma s := by
    simp_rw [mul_sub]
    rw [integral_sub hlog (hbase.mul_const _), integral_mul_const, hG]
    have hΓ := integral_exp_neg_mul_mul_rpow_sub_one hs (by norm_num : (0 : ℝ) < 1)
    simp only [neg_mul, one_mul, Real.one_rpow, mul_one] at hΓ
    rw [hΓ, mul_comm (Real.Gamma s)]
  rw [hright] at hsub
  apply mul_left_cancel₀ (Real.rpow_pos_of_pos hz (s - 1)).ne'
  rw [hsub]
  have he : z ^ (s - 1) * z ^ (-s) = z⁻¹ := by
    rw [← Real.rpow_add hz]
    rw [show s - 1 + -s = -1 by ring, Real.rpow_neg_one]
  calc z⁻¹ • (deriv Real.Gamma s - Real.log z * Real.Gamma s) =
      (deriv Real.Gamma s - Real.log z * Real.Gamma s) * (z ^ (s - 1) * z ^ (-s)) := by
        rw [he, smul_eq_mul, mul_comm]
    _ = _ := by ring

/-- A finite sum of logarithmic Gamma kernels is integrable against positive
exponential decay. -/
theorem integrableOn_exp_neg_mul_sum_rpow_mul_log (e a : ℕ → ℝ) (N : ℕ)
    (he : ∀ n, 0 < e n) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => Real.exp (-z * t) *
      (∑ n ∈ Finset.range N, t ^ (e n - 1) * a n) * Real.log t) (Ioi 0) := by
  have h := integrable_finsetSum (Finset.range N) (fun n _ =>
    (integrableOn_exp_neg_mul_rpow_sub_one_mul_log (he n) hz).mul_const (a n))
  refine IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
  simp only [Finset.mul_sum, Finset.sum_mul]
  congr 1
  ext n
  ring

/-- Integrating a finite logarithmic power expansion gives the corresponding
Gamma-derivative coefficients. -/
theorem integral_exp_neg_mul_sum_rpow_mul_log (e a : ℕ → ℝ) (N : ℕ)
    (he : ∀ n, 0 < e n) {z : ℝ} (hz : 0 < z) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-z * t) *
      (∑ n ∈ Finset.range N, t ^ (e n - 1) * a n) * Real.log t) =
      ∑ n ∈ Finset.range N,
        (deriv Real.Gamma (e n) - Real.log z * Real.Gamma (e n)) * a n * z ^ (-e n) := by
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ (fun n _ => by
    convert (integrableOn_exp_neg_mul_rpow_sub_one_mul_log (he n) hz).mul_const (a n) using 1
    ext t
    ring)]
  apply Finset.sum_congr rfl
  intro n _
  have heq : (∫ t in Ioi (0 : ℝ),
      Real.exp (-z * t) * (t ^ (e n - 1) * a n) * Real.log t) =
      (∫ t in Ioi (0 : ℝ), Real.exp (-z * t) * t ^ (e n - 1) * Real.log t) * a n := by
    rw [← integral_mul_const]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    ring
  rw [heq, integral_exp_neg_mul_rpow_sub_one_mul_log (he n) hz]
  ring

/-- A Laplace transform of a logarithmically weighted remainder has a power bound
if the unweighted remainder has any strictly higher order at zero. -/
theorem isBigO_integral_exp_mul_log {F : ℝ → ℝ} {s r c : ℝ}
    (hs : 0 < s) (hsr : s < r)
    (hint : IntegrableOn (fun t => Real.exp (-c * t) * F t * Real.log t) (Ioi 0))
    (hF : F =O[𝓝[>] 0] (fun t : ℝ => t ^ (r - 1))) :
    (fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * F t * Real.log t) =O[atTop]
      (fun x : ℝ => x ^ (-s)) := by
  have hb := isBigO_rpow_zero_log_smul
    (a := -(r - 1)) (b := -(s - 1)) (by linarith) (by simpa using hF)
  have hi : IntegrableOn (fun t => Real.exp (-c * t) • (Real.log t * F t)) (Ioi 0) := by
    convert hint using 1
    ext t
    simp only [smul_eq_mul]
    ring
  have h := isBigO_integral_exp_smul hs hi (by simpa using hb)
  convert h using 1
  ext x
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [smul_eq_mul]
  ring

/-- A logarithmic Gamma moment has the order `x⁻ˢ log x` at infinity. -/
theorem isBigO_log_gamma_term (s a : ℝ) :
    (fun x : ℝ => (deriv Real.Gamma s - Real.log x * Real.Gamma s) * a * x ^ (-s))
      =O[atTop] (fun x : ℝ => x ^ (-s) * Real.log x) := by
  have hc : (fun _ : ℝ => deriv Real.Gamma s) =O[atTop] Real.log :=
    Real.isLittleO_const_log_atTop.isBigO
  have hl : (fun x => Real.log x * Real.Gamma s) =O[atTop] Real.log := by
    simpa only [mul_comm] using (isBigO_refl Real.log atTop).const_mul_left (Real.Gamma s)
  have h := ((hc.sub hl).const_mul_left a).mul (isBigO_refl (fun x : ℝ => x ^ (-s)) atTop)
  simpa only [mul_comm, mul_left_comm] using h

/-- Watson's lemma with a logarithmic factor for a strictly increasing sequence
of positive exponents. An extra term of the input expansion absorbs the logarithm in
the remainder, so no differentiation of an asymptotic error estimate is needed. -/
theorem isBigO_integral_exp_mul_log_sub_sum {F : ℝ → ℝ} {e a : ℕ → ℝ} {c : ℝ}
    (he : ∀ n, 0 < e n) (he_step : ∀ n, e n < e (n + 1))
    (hint : IntegrableOn (fun t => Real.exp (-c * t) * F t * Real.log t) (Ioi 0))
    (hF : ∀ N : ℕ, (fun t => F t - ∑ n ∈ Finset.range N, t ^ (e n - 1) * a n)
      =O[𝓝[>] 0] (fun t => t ^ (e N - 1))) (N : ℕ) :
    (fun x : ℝ => (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * F t * Real.log t) -
      ∑ n ∈ Finset.range N,
        (deriv Real.Gamma (e n) - Real.log x * Real.Gamma (e n)) * a n * x ^ (-e n))
      =O[atTop] (fun x : ℝ => x ^ (-e N) * Real.log x) := by
  let c' := max c 0 + 1
  have hc' : 0 < c' := by dsimp [c']; linarith [le_max_right c 0]
  have hcc' : c ≤ c' := by dsimp [c']; linarith [le_max_left c 0]
  have hi (x : ℝ) (hx : c ≤ x) :
      IntegrableOn (fun t => Real.exp (-x * t) * F t * Real.log t) (Ioi 0) := by
    have h : IntegrableOn (fun t => Real.exp (-c * t) • (F t * Real.log t)) (Ioi 0) := by
      simpa only [smul_eq_mul, mul_assoc] using hint
    simpa only [smul_eq_mul, mul_assoc] using h.exp_neg_mul_smul_of_le hx
  let R : ℝ → ℝ := fun t => F t - ∑ n ∈ Finset.range (N + 1), t ^ (e n - 1) * a n
  have hiR : IntegrableOn (fun t => Real.exp (-c' * t) * R t * Real.log t) (Ioi 0) := by
    have h := (hi c' hcc').sub
      (integrableOn_exp_neg_mul_sum_rpow_mul_log e a (N + 1) he hc')
    convert h using 1
    ext t
    dsimp [R]
    ring
  have hb := isBigO_integral_exp_mul_log (he N) (he_step N) hiR (hF (N + 1))
  have hscale : (fun x : ℝ => x ^ (-e N)) =O[atTop]
      (fun x : ℝ => x ^ (-e N) * Real.log x) := by
    simpa only [mul_one] using (isBigO_refl (fun x : ℝ => x ^ (-e N)) atTop).mul
      (Real.isLittleO_const_log_atTop (c := 1)).isBigO
  refine ((hb.trans hscale).add (isBigO_log_gamma_term (e N) (a N))).congr' ?_ .rfl
  filter_upwards [eventually_ge_atTop c'] with x hx
  have hx0 : 0 < x := hc'.trans_le hx
  dsimp only [R]
  simp_rw [mul_sub, sub_mul]
  rw [integral_sub (hi x (hcc'.trans hx))
    (integrableOn_exp_neg_mul_sum_rpow_mul_log e a (N + 1) he hx0),
    integral_exp_neg_mul_sum_rpow_mul_log e a (N + 1) he hx0, Finset.sum_range_succ]
  ring_nf
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  ring
