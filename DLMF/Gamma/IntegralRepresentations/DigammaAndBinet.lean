/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.IntegralRepresentations.PrymAndOscillatory

/-!
# Digamma integrals and Binet formulas

Integral representations of the digamma function and the Binet formulas for log Gamma.

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

section DigammaIntegrals

open Set

/-- `∫₀¹ (tⁿ - t^{n+x-1}) dt = 1/(n+1) - 1/(n+x)`. -/
theorem integral_pow_sub_rpow {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∫ t in Ioo (0 : ℝ) 1, (t ^ n - t ^ ((n : ℝ) + x - 1)) = Real.digammaSeriesTerm x n := by
  have h1 : (-1 : ℝ) < (n : ℝ) + x - 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_pow _)
      (intervalIntegral.intervalIntegrable_rpow' h1), integral_pow,
    integral_rpow (Or.inl h1), Real.digammaSeriesTerm]
  rw [zero_pow (Nat.succ_ne_zero n), Real.one_rpow,
    Real.zero_rpow (by linarith : (n : ℝ) + x - 1 + 1 ≠ 0), one_pow,
    show (n : ℝ) + x - 1 + 1 = x + n by ring]
  have : (x + n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- `tⁿ - t^{n+x-1} = tⁿ (1 - t^{x-1})` for `t > 0`. -/
theorem pow_sub_rpow_eq {x t : ℝ} (ht : 0 < t) (n : ℕ) :
    t ^ n - t ^ ((n : ℝ) + x - 1) = t ^ n * (1 - t ^ (x - 1)) := by
  rw [show (n : ℝ) + x - 1 = n + (x - 1) by ring, Real.rpow_add ht, Real.rpow_natCast]; ring

/-- `ψ(x) + γ = ∫₀¹ (1 - t^{x-1})/(1 - t) dt`, from the digamma series. -/
theorem digamma_add_euler_Ioo {x : ℝ} (hx : 0 < x) :
    Real.digamma x + Real.eulerMascheroniConstant =
      ∫ t in Ioo (0 : ℝ) 1, (1 - t ^ (x - 1)) / (1 - t) := by
  set F : ℕ → ℝ → ℝ := fun n t => t ^ n - t ^ ((n : ℝ) + x - 1) with hF
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioo (0 : ℝ) 1)) := by
    intro n
    have h1 : (-1 : ℝ) < (n : ℝ) + x - 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have := ((intervalIntegral.intervalIntegrable_pow (μ := volume) (a := 0) (b := 1) n).sub
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) h1))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    exact this.mono_set Ioo_subset_Ioc_self
  -- the terms do not change sign on `(0, 1)`
  have hsign : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ n, ∀ t ∈ Ioo (0 : ℝ) 1, ‖F n t‖ = ε * F n t := by
    by_cases hx1 : 1 ≤ x
    · refine ⟨1, Or.inl rfl, fun n t ht => ?_⟩
      have h := Real.rpow_le_one ht.1.le ht.2.le (by linarith : (0 : ℝ) ≤ x - 1)
      simp only [hF, pow_sub_rpow_eq ht.1, one_mul]
      rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht.1.le _) (by linarith))]
    · refine ⟨-1, Or.inr rfl, fun n t ht => ?_⟩
      have h := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2.le
        (by linarith : x - 1 ≤ 0)
      simp only [hF, pow_sub_rpow_eq ht.1]
      rw [Real.norm_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ht.1.le _)
        (by linarith))]
      ring
  obtain ⟨ε, hε, hεF⟩ := hsign
  have hnorm : ∀ n, ∫ t in Ioo (0 : ℝ) 1, ‖F n t‖ = ε * Real.digammaSeriesTerm x n := by
    intro n
    rw [setIntegral_congr_fun measurableSet_Ioo (hεF n), MeasureTheory.integral_const_mul,
      integral_pow_sub_rpow hx]
  have hsum : Summable fun n => ∫ t in Ioo (0 : ℝ) 1, ‖F n t‖ := by
    simp_rw [hnorm]
    exact (Real.summable_digammaSeriesTerm hx).mul_left ε
  have key := integral_tsum_of_summable_integral_norm hint hsum
  simp_rw [hF, integral_pow_sub_rpow hx] at key
  rw [Real.digamma_eq_tsum hx, neg_add_cancel_comm, key]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  simp only [pow_sub_rpow_eq ht.1]
  rw [tsum_mul_right, tsum_geometric_of_lt_one ht.1.le ht.2]
  field_simp

/-- `∫₀^∞ (e^{-(n+1)t} - e^{-(n+x)t}) dt = 1/(n+1) - 1/(n+x)`. -/
theorem integral_exp_sub_exp {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), (Real.exp (-((n : ℝ) + 1) * t) - Real.exp (-((n : ℝ) + x) * t)) =
      Real.digammaSeriesTerm x n := by
  have h1 : -((n : ℝ) + 1) < 0 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2 : -((n : ℝ) + x) < 0 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [integral_sub (integrableOn_exp_mul_Ioi h1 0) (integrableOn_exp_mul_Ioi h2 0),
    integral_exp_mul_Ioi h1, integral_exp_mul_Ioi h2, Real.digammaSeriesTerm]
  simp only [mul_zero, Real.exp_zero]
  have : (x + n : ℝ) ≠ 0 := by positivity
  have : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- Factorization of the exponential series term. -/
theorem exp_sub_exp_eq {x t : ℝ} (n : ℕ) :
    Real.exp (-((n : ℝ) + 1) * t) - Real.exp (-((n : ℝ) + x) * t) =
      Real.exp (-t) ^ n * (Real.exp (-t) - Real.exp (-x * t)) := by
  rw [← Real.exp_nat_mul, mul_sub, ← Real.exp_add, ← Real.exp_add]
  congr 2 <;> ring

/-- `ψ(x) + γ = ∫₀^∞ (e^{-t} - e^{-xt})/(1 - e^{-t}) dt`, from the digamma series. -/
theorem digamma_add_euler_Ioi {x : ℝ} (hx : 0 < x) :
    Real.digamma x + Real.eulerMascheroniConstant =
      ∫ t in Ioi (0 : ℝ), (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t)) := by
  set F : ℕ → ℝ → ℝ := fun n t =>
    Real.exp (-((n : ℝ) + 1) * t) - Real.exp (-((n : ℝ) + x) * t) with hF
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi (0 : ℝ))) := by
    intro n
    have h1 : -((n : ℝ) + 1) < 0 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h2 : -((n : ℝ) + x) < 0 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact (integrableOn_exp_mul_Ioi h1 0).sub (integrableOn_exp_mul_Ioi h2 0)
  have hsign : ∃ ε : ℝ, ∀ n, ∀ t ∈ Ioi (0 : ℝ), ‖F n t‖ = ε * F n t := by
    by_cases hx1 : 1 ≤ x
    · refine ⟨1, fun n t ht => ?_⟩
      have h : Real.exp (-x * t) ≤ Real.exp (-t) :=
        Real.exp_le_exp.mpr (by nlinarith [show (0 : ℝ) < t from ht])
      simp only [hF, exp_sub_exp_eq, one_mul]
      rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (by linarith))]
    · refine ⟨-1, fun n t ht => ?_⟩
      have h : Real.exp (-t) ≤ Real.exp (-x * t) :=
        Real.exp_le_exp.mpr (by nlinarith [show (0 : ℝ) < t from ht])
      simp only [hF, exp_sub_exp_eq]
      rw [Real.norm_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (Real.exp_pos _).le _)
        (by linarith))]
      ring
  obtain ⟨ε, hεF⟩ := hsign
  have hnorm : ∀ n, ∫ t in Ioi (0 : ℝ), ‖F n t‖ = ε * Real.digammaSeriesTerm x n := by
    intro n
    rw [setIntegral_congr_fun measurableSet_Ioi (hεF n), MeasureTheory.integral_const_mul,
      integral_exp_sub_exp hx]
  have hsum : Summable fun n => ∫ t in Ioi (0 : ℝ), ‖F n t‖ := by
    simp_rw [hnorm]
    exact (Real.summable_digammaSeriesTerm hx).mul_left ε
  have key := integral_tsum_of_summable_integral_norm hint hsum
  simp_rw [hF, integral_exp_sub_exp hx] at key
  rw [Real.digamma_eq_tsum hx, neg_add_cancel_comm, key]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [exp_sub_exp_eq]
  have he1 : Real.exp (-t) < 1 :=
    Real.exp_lt_one_iff.mpr (by simpa using (show (0 : ℝ) < t from ht))
  rw [tsum_mul_right, tsum_geometric_of_lt_one (Real.exp_pos _).le he1]
  field_simp

/-- The digamma function is monotone on `(0, ∞)`. -/
theorem digamma_le_digamma {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.digamma x ≤ Real.digamma y := by
  have hy : 0 < y := hx.trans_le hxy
  rw [Real.digamma_eq_tsum hx, Real.digamma_eq_tsum hy]
  refine add_le_add_right ((Real.summable_digammaSeriesTerm hx).tsum_le_tsum (fun n => ?_)
    (Real.summable_digammaSeriesTerm hy)) _
  simp only [Real.digammaSeriesTerm]
  have : 0 < x + n := by positivity
  gcongr

/-- `log x - 1/x ≤ ψ(x) ≤ log x`. -/
theorem digamma_le_log_and {x : ℝ} (hx : 0 < x) :
    Real.log x - 1 / x ≤ Real.digamma x ∧ Real.digamma x ≤ Real.log x := by
  -- mean value theorem for `log Γ` on `[x, x + 1]`
  have hcont : ContinuousOn (fun s => Real.log (Real.Gamma s)) (Icc x (x + 1)) := by
    intro s hs
    exact (Real.hasDerivAt_log_Gamma (hx.trans_le hs.1)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hderiv⟩ := exists_hasDerivAt_eq_slope (fun s => Real.log (Real.Gamma s))
    Real.digamma (by linarith) hcont
    (fun s hs => Real.hasDerivAt_log_Gamma (hx.trans hs.1))
  have hslope : (Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x)) / (x + 1 - x) =
      Real.log x := by
    rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
    ring
  rw [hslope] at hderiv
  have h1 := digamma_le_digamma hx hc.1.le
  have h2 := digamma_le_digamma (hx.trans hc.1) hc.2.le
  rw [Real.digamma_add_one hx] at h2
  constructor
  · rw [one_div]; linarith
  · linarith

/-- `|e^{-t} - e^{-xt}| ≤ |x - 1| t e^{-min(1,x) t}` for `t ≥ 0`. -/
theorem abs_exp_neg_sub_exp_neg_le {x t : ℝ} (ht : 0 ≤ t) :
    |Real.exp (-t) - Real.exp (-x * t)| ≤ |x - 1| * t * Real.exp (-min 1 x * t) := by
  have key : ∀ a b : ℝ, a ≤ b → 0 ≤ Real.exp (-a * t) - Real.exp (-b * t) ∧
      Real.exp (-a * t) - Real.exp (-b * t) ≤ (b - a) * t * Real.exp (-a * t) := by
    intro a b hab
    have h1 : Real.exp (-b * t) = Real.exp (-a * t) * Real.exp (-((b - a) * t)) := by
      rw [← Real.exp_add]; ring_nf
    have h2 := Real.add_one_le_exp (-((b - a) * t))
    have h3 : Real.exp (-((b - a) * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    have he := Real.exp_pos (-a * t)
    rw [h1]
    constructor <;> nlinarith
  rcases le_total 1 x with h | h
  · obtain ⟨k0, k1⟩ := key 1 x h
    rw [min_eq_left h]
    simp only [neg_mul, one_mul] at k0 k1 ⊢
    rw [abs_of_nonneg k0, abs_of_nonneg (show (0 : ℝ) ≤ x - 1 by linarith)]
    exact k1
  · obtain ⟨k0, k1⟩ := key x 1 h
    rw [min_eq_right h]
    simp only [neg_mul, one_mul] at k0 k1 ⊢
    rw [abs_of_nonpos (show Real.exp (-t) - Real.exp (-(x * t)) ≤ 0 by linarith),
      abs_of_nonpos (show x - 1 ≤ 0 by linarith)]
    linarith

/-- Integrability of the Frullani integrand `(e^{-t} - e^{-xt})/t`. -/
theorem integrableOn_exp_neg_sub_exp_neg_div {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t⁻¹ * (Real.exp (-t) - Real.exp (-x * t))) (Ioi 0) := by
  have hm : -min 1 x < 0 := by simp [hx]
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi hm 0).const_mul |x - 1|) ?_ ?_
  · exact (ContinuousOn.mul (continuousOn_inv₀.mono fun t ht => (ne_of_gt ht))
      (by fun_prop)).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos ht']
    have := abs_exp_neg_sub_exp_neg_le (x := x) ht'.le
    rw [inv_mul_le_iff₀ ht']
    nlinarith

/-- Frullani: `∫₀^∞ (e^{-t} - e^{-xt})/t dt = log x`. -/
theorem integral_exp_neg_sub_exp_neg_div {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), t⁻¹ * (Real.exp (-t) - Real.exp (-x * t)) = Real.log x := by
  have hc : Continuous fun t : ℝ => Real.exp (-t) := by fun_prop
  have hloc : LocallyIntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) :=
    hc.locallyIntegrable.locallyIntegrableOn _
  have hL : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝 1) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hint : IntegrableOn (fun t : ℝ => t⁻¹ • (Real.exp (-(1 * t)) - Real.exp (-(x * t))))
      (Ioi 0) := by
    simpa [neg_mul, smul_eq_mul] using integrableOn_exp_neg_sub_exp_neg_div hx
  have h := Frullani.integral_Ioi_eq hloc one_pos hx hL Real.tendsto_exp_neg_atTop_nhds_zero hint
  simpa [neg_mul, smul_eq_mul] using h

/-- The Binet kernel `1/(1 - e^{-t}) - 1/t`. -/
def binetKernel (t : ℝ) : ℝ := 1 / (1 - Real.exp (-t)) - 1 / t

/-- `0 ≤ 1/(1 - e^{-t}) - 1/t ≤ 1` for `t > 0`. -/
theorem binetKernel_mem_Icc {t : ℝ} (ht : 0 < t) : binetKernel t ∈ Icc (0 : ℝ) 1 := by
  have he : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpos : 0 < 1 - Real.exp (-t) := by linarith
  have h1 := Real.add_one_le_exp (-t)
  have h2 : t + 1 ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have h3 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have hep := Real.exp_pos (-t)
  unfold binetKernel
  constructor
  · rw [sub_nonneg, div_le_div_iff₀ ht hpos]; linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hpos]
    have : 1 / t * (1 - Real.exp (-t)) = (1 - Real.exp (-t)) / t := by ring
    rw [add_mul, one_mul, this, ← sub_le_iff_le_add', le_div_iff₀ ht]
    nlinarith

/-- Integrability of `e^{-xt}` times the Binet kernel. -/
theorem integrableOn_exp_mul_binetKernel {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => Real.exp (-x * t) * binetKernel t) (Ioi 0) := by
  have hm : -x < 0 := by linarith
  refine Integrable.mono' (integrableOn_exp_mul_Ioi hm 0) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h1 : 1 - Real.exp (-t) ≠ 0 := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
    have h2 : t ≠ 0 := ht'.ne'
    unfold binetKernel
    exact (ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption)))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    obtain ⟨h0, h1⟩ := binetKernel_mem_Icc ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg h0]
    nlinarith [Real.exp_pos (-x * t)]

/-- `J(x) = ∫₀^∞ e^{-xt} (1/(1 - e^{-t}) - 1/t) dt` lies in `[0, 1/x]`. -/
theorem integral_exp_mul_binetKernel_mem {x : ℝ} (hx : 0 < x) :
    0 ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t ≤ 1 / x := by
  have hm : -x < 0 := by linarith
  constructor
  · refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    exact mul_nonneg (Real.exp_pos _).le (binetKernel_mem_Icc ht).1
  · have hle : ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t ≤
        ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) := by
      refine setIntegral_mono_on (integrableOn_exp_mul_binetKernel hx)
        (integrableOn_exp_mul_Ioi hm 0) measurableSet_Ioi fun t ht => ?_
      have := (binetKernel_mem_Icc ht).2
      nlinarith [Real.exp_pos (-x * t)]
    rw [integral_exp_mul_Ioi hm] at hle
    simpa [neg_div, div_neg] using hle

/-- `ψ(x) + γ - log x = J(1) - J(x)`. -/
theorem digamma_add_euler_sub_log {x : ℝ} (hx : 0 < x) :
    Real.digamma x + Real.eulerMascheroniConstant - Real.log x =
      (∫ t in Ioi (0 : ℝ), Real.exp (-1 * t) * binetKernel t) -
        ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t := by
  rw [digamma_add_euler_Ioi hx, ← integral_exp_neg_sub_exp_neg_div hx,
    ← integral_sub (integrableOn_exp_mul_binetKernel one_pos) (integrableOn_exp_mul_binetKernel hx)]
  have heq : EqOn (fun t => (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t)))
      (fun t => (Real.exp (-1 * t) * binetKernel t - Real.exp (-x * t) * binetKernel t) +
        t⁻¹ * (Real.exp (-t) - Real.exp (-x * t))) (Ioi 0) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h1 : 1 - Real.exp (-t) ≠ 0 := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
    simp only [binetKernel, neg_mul, one_mul]
    field_simp
    ring
  have hi1 : IntegrableOn (fun t => Real.exp (-1 * t) * binetKernel t -
      Real.exp (-x * t) * binetKernel t) (Ioi 0) :=
    (integrableOn_exp_mul_binetKernel one_pos).sub (integrableOn_exp_mul_binetKernel hx)
  rw [setIntegral_congr_fun measurableSet_Ioi heq,
    integral_add hi1 (integrableOn_exp_neg_sub_exp_neg_div hx)]
  ring

/-- Binet's formula for the digamma function, together with `J(1) = γ`. -/
theorem digamma_eq_log_sub {x : ℝ} (hx : 0 < x) :
    Real.digamma x = Real.log x - ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t := by
  set J : ℝ → ℝ := fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t with hJ
  -- `ψ(y) - log y + J(y)` is constant
  have hconst : ∀ y : ℝ, 0 < y →
      Real.digamma y - Real.log y + J y = J 1 - Real.eulerMascheroniConstant := by
    intro y hy
    have := digamma_add_euler_sub_log hy
    simp only [hJ]
    linarith
  have hlim : Tendsto (fun y : ℝ => Real.digamma y - Real.log y + J y) atTop (𝓝 0) := by
    have hinv : Tendsto (fun y : ℝ => 1 / y) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero
    have h1 : Tendsto (fun y : ℝ => Real.digamma y - Real.log y) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hinv.neg.trans (by simp))
        tendsto_const_nhds
        ?_ ?_
      · filter_upwards [eventually_gt_atTop 0] with y hy
        have := (digamma_le_log_and hy).1; linarith
      · filter_upwards [eventually_gt_atTop 0] with y hy
        have := (digamma_le_log_and hy).2; linarith
    have h2 : Tendsto J atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
      · filter_upwards [eventually_gt_atTop 0] with y hy
        exact (integral_exp_mul_binetKernel_mem hy).1
      · filter_upwards [eventually_gt_atTop 0] with y hy
        exact (integral_exp_mul_binetKernel_mem hy).2
    simpa using h1.add h2
  have hc : J 1 - Real.eulerMascheroniConstant = 0 := by
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
    filter_upwards [eventually_gt_atTop 0] with y hy
    exact (hconst y hy).symm
  have := hconst x hx
  simp only [hJ] at this hc ⊢
  linarith

/-- `J(1) = ∫₀^∞ e^{-t} (1/(1 - e^{-t}) - 1/t) dt = γ`. -/
theorem integral_exp_mul_binetKernel_one :
    ∫ t in Ioi (0 : ℝ), Real.exp (-1 * t) * binetKernel t = Real.eulerMascheroniConstant := by
  have := digamma_eq_log_sub one_pos
  rw [Real.digamma_one, Real.log_one] at this
  linarith

/-- Integrability of `(e^{-t} - e^{-xt})/(1 - e^{-t})` on `(0, ∞)`. -/
theorem integrableOn_digamma_add_euler {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t))) (Ioi 0) := by
  have hi := ((integrableOn_exp_mul_binetKernel one_pos).sub
    (integrableOn_exp_mul_binetKernel hx)).add (integrableOn_exp_neg_sub_exp_neg_div hx)
  refine IntegrableOn.congr_fun hi (fun t ht => ?_) measurableSet_Ioi
  have ht' : (0 : ℝ) < t := ht
  have h1 : 1 - Real.exp (-t) ≠ 0 := by
    have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
  simp only [Pi.add_apply, Pi.sub_apply, binetKernel, neg_mul, one_mul]
  field_simp
  ring

end DigammaIntegrals

section Binet

/-! ### Binet's formulas for `log Γ`

We follow Temme, *Special Functions*, §3.4 and §3.6: Binet's formula (3.12) for `ψ` is
`digamma_eq_log_sub`; integrating it gives (3.20), and the constant of integration is fixed
by Stirling's formula along the integers (Temme uses the duplication formula instead). -/

open Set

/-- Binet's function `β(t) = 1/(eᵗ - 1) - 1/t + 1/2` (Temme (3.12)). -/
def binetBeta (t : ℝ) : ℝ := 1 / (Real.exp t - 1) - 1 / t + 1 / 2

/-- `e^t - 1 > 0` for `t > 0`. -/
theorem exp_sub_one_pos {t : ℝ} (ht : 0 < t) : 0 < Real.exp t - 1 := by
  have := Real.add_one_lt_exp ht.ne'; linarith

/-- `1/(1 - e^(-t)) - 1/t = β(t) + 1/2`, with `β(t) = 1/(e^t - 1) - 1/t + 1/2`. -/
theorem binetKernel_eq_binetBeta {t : ℝ} (ht : 0 < t) : binetKernel t = binetBeta t + 1 / 2 := by
  have h1 := (exp_sub_one_pos ht).ne'
  have h0 : Real.exp t ≠ 0 := Real.exp_ne_zero t
  have h2 : 1 - (Real.exp t)⁻¹ = (Real.exp t - 1) / Real.exp t := by field_simp
  unfold binetKernel binetBeta
  rw [Real.exp_neg, h2]
  field_simp
  ring

/-- `β(t) ≥ 0` for `t > 0`, i.e. `eᵗ (t - 2) + t + 2 ≥ 0`. -/
theorem binetBeta_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ binetBeta t := by
  set g : ℝ → ℝ := fun s => Real.exp s * (s - 2) + s + 2 with hg
  have hd : ∀ s, HasDerivAt g (Real.exp s * (s - 1) + 1) s := by
    intro s
    have := (((Real.hasDerivAt_exp s).mul ((hasDerivAt_id s).sub_const 2)).add
      (hasDerivAt_id s)).add_const 2
    exact this.congr_deriv (by deriv_simp)
  have hmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun s _ => (hd s).continuousAt.continuousWithinAt)
      (fun s _ => (hd s).differentiableAt.differentiableWithinAt) fun s _ => ?_
    rw [(hd s).deriv]
    have h1 := Real.add_one_le_exp (-s)
    have h2 : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos s]
  have hgt : g 0 ≤ g t := hmono self_mem_Ici ht.le ht.le
  have hg0 : g 0 = 0 := by simp [hg]
  have hE := exp_sub_one_pos ht
  have heq : binetBeta t = g t / (2 * t * (Real.exp t - 1)) := by
    simp only [binetBeta, hg]
    field_simp
    ring
  rw [heq]
  exact div_nonneg (hg0 ▸ hgt) (by positivity)

/-- `β(t) ≤ t/12` for `t > 0`: the Padé bound `eᵗ (t² - 6t + 12) ≥ t² + 6t + 12`. -/
theorem binetBeta_le {t : ℝ} (ht : 0 < t) : binetBeta t ≤ t / 12 := by
  have hE := exp_sub_one_pos ht
  have hq : 0 < t ^ 2 - 6 * t + 12 := by nlinarith [sq_nonneg (t - 3)]
  have hP := Real.sum_le_exp_of_nonneg ht.le 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hP
  norm_num at hP
  have h5 : 0 ≤ t ^ 5 * (t ^ 2 - t + 2) := by
    have : 0 < t ^ 2 - t + 2 := by nlinarith [sq_nonneg (t - 1 / 2)]
    positivity
  have key : 0 ≤ Real.exp t * (t ^ 2 - 6 * t + 12) - (t ^ 2 + 6 * t + 12) := by
    nlinarith [mul_le_mul_of_nonneg_right hP hq.le]
  have heq : t / 12 - binetBeta t =
      (Real.exp t * (t ^ 2 - 6 * t + 12) - (t ^ 2 + 6 * t + 12)) / (12 * t * (Real.exp t - 1)) := by
    unfold binetBeta
    field_simp
    ring
  have : 0 ≤ t / 12 - binetBeta t := by rw [heq]; positivity
  linarith

/-- `β(t) ≤ 1/2` for `t > 0`. -/
theorem binetBeta_le_half {t : ℝ} (ht : 0 < t) : binetBeta t ≤ 1 / 2 := by
  have := (binetKernel_mem_Icc ht).2
  rw [binetKernel_eq_binetBeta ht] at this
  linarith

/-- `β(t) = 1/(e^t - 1) - 1/t + 1/2` is continuous on `(0, ∞)`. -/
theorem continuousOn_binetBeta : ContinuousOn binetBeta (Ioi 0) := by
  intro t ht
  have h1 := (exp_sub_one_pos ht).ne'
  have h2 : t ≠ 0 := (ne_of_gt ht)
  unfold binetBeta
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))

/-- Integrability of `e^{-xt} β(t)`. -/
theorem integrableOn_exp_mul_binetBeta {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => Real.exp (-x * t) * binetBeta t) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by linarith : -x < 0) 0).const_mul (1 / 2))
    ?_ ?_
  · exact ((by fun_prop : Continuous fun t => Real.exp (-x * t)).continuousOn.mul
      continuousOn_binetBeta).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (binetBeta_nonneg ht))]
    nlinarith [Real.exp_pos (-x * t), binetBeta_le_half ht]

/-- Integrability of `e^{-xt} β(t)/t`. -/
theorem integrableOn_exp_mul_binetBeta_div {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => Real.exp (-x * t) * binetBeta t / t) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by linarith : -x < 0) 0).const_mul (1 / 12))
    ?_ ?_
  · refine (((by fun_prop : Continuous fun t => Real.exp (-x * t)).continuousOn.mul
      continuousOn_binetBeta).div continuousOn_id fun t ht => ?_).aestronglyMeasurable
      measurableSet_Ioi
    exact (ne_of_gt ht)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg (Real.exp_pos _).le
      (binetBeta_nonneg ht')) ht'.le), div_le_iff₀ ht']
    nlinarith [Real.exp_pos (-x * t), binetBeta_le ht']

/-- Binet's integral `Φ(x) = ∫₀^∞ e^{-xt} β(t)/t dt` (Temme (3.27)). -/
def binetIntegral (x : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetBeta t / t

/-- `0 ≤ Φ(x) ≤ 1/(12x)`. -/
theorem binetIntegral_mem {x : ℝ} (hx : 0 < x) :
    0 ≤ binetIntegral x ∧ binetIntegral x ≤ 1 / (12 * x) := by
  have hm : -x < 0 := by linarith
  constructor
  · refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (binetBeta_nonneg ht)) (le_of_lt ht)
  · have hle : binetIntegral x ≤ ∫ t in Ioi (0 : ℝ), 1 / 12 * Real.exp (-x * t) := by
      refine setIntegral_mono_on (integrableOn_exp_mul_binetBeta_div hx)
        ((integrableOn_exp_mul_Ioi hm 0).const_mul _) measurableSet_Ioi fun t ht => ?_
      have ht' : (0 : ℝ) < t := ht
      rw [div_le_iff₀ ht']
      nlinarith [Real.exp_pos (-x * t), binetBeta_le ht']
    rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi hm] at hle
    convert hle using 1
    simp only [mul_zero, Real.exp_zero]
    field_simp

/-- `Φ'(x) = -∫₀^∞ e^{-xt} β(t) dt`. -/
theorem hasDerivAt_binetIntegral {x : ℝ} (hx : 0 < x) :
    HasDerivAt binetIntegral (∫ t in Ioi (0 : ℝ), -(Real.exp (-x * t) * binetBeta t)) x := by
  set δ := x / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hball : Metric.ball x δ ∈ 𝓝 x := Metric.ball_mem_nhds _ hδ0
  have hre : ∀ y ∈ Metric.ball x δ, δ < y := by
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
    have := (abs_lt.mp hy).1
    linarith
  have hmeas (y : ℝ) : AEStronglyMeasurable (fun t => Real.exp (-y * t) * binetBeta t / t)
      (volume.restrict (Ioi 0)) :=
    (((by fun_prop : Continuous fun t => Real.exp (-y * t)).continuousOn.mul
      continuousOn_binetBeta).div continuousOn_id fun t ht => (ne_of_gt ht)).aestronglyMeasurable
      measurableSet_Ioi
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun y t => Real.exp (-y * t) * binetBeta t / t)
    (F' := fun y t => -(Real.exp (-y * t) * binetBeta t))
    (bound := fun t => 1 / 2 * Real.exp (-δ * t))
    hball (Eventually.of_forall hmeas) (integrableOn_exp_mul_binetBeta_div hx)
    (integrableOn_exp_mul_binetBeta hx).neg.aestronglyMeasurable ?_
    ((integrableOn_exp_mul_Ioi (by linarith : -δ < 0) 0).const_mul _) ?_
  · exact h.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht y hy
    have ht' : (0 : ℝ) < t := ht
    have hexp : Real.exp (-y * t) ≤ Real.exp (-δ * t) :=
      Real.exp_le_exp.mpr (by nlinarith [hre y hy])
    rw [norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (binetBeta_nonneg ht'))]
    nlinarith [Real.exp_pos (-y * t), binetBeta_le_half ht', binetBeta_nonneg ht']
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht y _
    have ht' : (0 : ℝ) < t := ht
    have ht0 : t ≠ 0 := ht'.ne'
    have h := (((hasDerivAt_id y).neg.mul_const t).exp.mul_const (binetBeta t)).div_const t
    exact h.congr_deriv (by deriv_simp)

/-- `ψ(x) = log x - 1/(2x) - ∫₀^∞ e^{-xt} β(t) dt` (Temme (3.12)). -/
theorem digamma_eq_log_sub_binetBeta {x : ℝ} (hx : 0 < x) :
    Real.digamma x = Real.log x - 1 / (2 * x) -
      ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetBeta t := by
  have hm : -x < 0 := by linarith
  have hsplit : ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t =
      (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetBeta t) +
        ∫ t in Ioi (0 : ℝ), 1 / 2 * Real.exp (-x * t) := by
    rw [← integral_add (integrableOn_exp_mul_binetBeta hx)
      ((integrableOn_exp_mul_Ioi hm 0).const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [binetKernel_eq_binetBeta ht]
    ring
  rw [digamma_eq_log_sub hx, hsplit, MeasureTheory.integral_const_mul,
    integral_exp_mul_Ioi hm]
  simp only [mul_zero, Real.exp_zero]
  field_simp
  ring

/-- A function with zero derivative on `(0, ∞)` is constant there. -/
theorem eq_of_hasDerivAt_zero_Ioi {G : ℝ → ℝ} (hG : ∀ y, 0 < y → HasDerivAt G 0 y)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : G a = G b := by
  have key : ∀ a b : ℝ, 0 < a → a < b → G a = G b := by
    intro a b ha hab
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope G (fun _ => (0 : ℝ)) hab
      (fun y hy => (hG y (ha.trans_le hy.1)).continuousAt.continuousWithinAt)
      (fun y hy => hG y (ha.trans hy.1))
    have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
    rw [eq_div_iff hne, zero_mul] at hslope
    linarith
  rcases lt_trichotomy a b with h | h | h
  · exact key a b ha h
  · rw [h]
  · exact (key b a hb h).symm

/-- DLMF 5.9.10 (exponential form): `ln Γ(x) = (x - 1/2) ln x - x + (1/2) ln 2π + ∫₀^∞ e^(-xt)
(1/(e^t - 1) - 1/t + 1/2) dt/t` for `x > 0`. -/
@[dlmf 5.9.E10_2]
theorem log_Gamma_binet_exp {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + (1 / 2) * Real.log (2 * π) +
        ∫ t : ℝ in Set.Ioi 0,
          Real.exp (-x * t) * (1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t := by
  set M : ℝ → ℝ := fun y => (y - 1 / 2) * Real.log y - y + (1 / 2) * Real.log (2 * π) with hM
  set G : ℝ → ℝ := fun y => Real.log (Real.Gamma y) - M y - binetIntegral y with hG
  have hG' : ∀ y, 0 < y → HasDerivAt G 0 y := by
    intro y hy
    have h2 : HasDerivAt M (Real.log y - 1 / (2 * y)) y := by
      have := ((((hasDerivAt_id y).sub_const (1 / 2)).mul (Real.hasDerivAt_log hy.ne')).sub
        (hasDerivAt_id y)).add_const ((1 / 2) * Real.log (2 * π))
      exact this.congr_deriv (by deriv_simp)
    have := ((Real.hasDerivAt_log_Gamma hy).sub h2).sub (hasDerivAt_binetIntegral hy)
    exact this.congr_deriv (by
      rw [MeasureTheory.integral_neg, digamma_eq_log_sub_binetBeta hy]; ring)
  have hlimG : Tendsto (fun n : ℕ => G n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.log (Real.Gamma n / Real.stirlingGamma n)) atTop
        (𝓝 0) := by
      simpa using Real.tendsto_Gamma_nat_div_stirlingGamma.log one_ne_zero
    have hinv : Tendsto (fun y : ℝ => 1 / (12 * y)) atTop (𝓝 0) := by
      refine (tendsto_inv_atTop_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 12))).congr fun y => ?_
      simp [one_div]
    have h2 : Tendsto binetIntegral atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
      · filter_upwards [eventually_gt_atTop 0] with y hy
        exact (binetIntegral_mem hy).1
      · filter_upwards [eventually_gt_atTop 0] with y hy
        exact (binetIntegral_mem hy).2
    have h3 := h1.sub (h2.comp tendsto_natCast_atTop_atTop)
    rw [sub_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Function.comp_apply, hG, hM]
    rw [Real.log_div (Real.Gamma_pos_of_pos hn').ne' (Real.stirlingGamma_ne_zero hn'),
      Real.log_stirlingGamma hn']
    ring
  have hGx : G x = 0 := by
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlimG
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact eq_of_hasDerivAt_zero_Ioi hG' hx (by exact_mod_cast hn)
  simp only [hG, hM, binetIntegral, binetBeta] at hGx
  linarith

/-- `β(t) > 0` for `t > 0`. -/
theorem binetBeta_pos {t : ℝ} (ht : 0 < t) : 0 < binetBeta t := by
  set g : ℝ → ℝ := fun s => Real.exp s * (s - 2) + s + 2 with hg
  have hd : ∀ s, HasDerivAt g (Real.exp s * (s - 1) + 1) s := by
    intro s
    have := (((Real.hasDerivAt_exp s).mul ((hasDerivAt_id s).sub_const 2)).add
      (hasDerivAt_id s)).add_const 2
    exact this.congr_deriv (by deriv_simp)
  have hmono : StrictMonoOn g (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0)
      (fun s _ => (hd s).continuousAt.continuousWithinAt) fun s hs => ?_
    rw [interior_Ici] at hs
    rw [(hd s).deriv]
    have h1 := Real.add_one_lt_exp (by linarith [mem_Ioi.mp hs] : -s ≠ 0)
    have h2 : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos s]
  have hgt : g 0 < g t := hmono self_mem_Ici ht.le ht
  have hg0 : g 0 = 0 := by simp [hg]
  have hE := exp_sub_one_pos ht
  have heq : binetBeta t = g t / (2 * t * (Real.exp t - 1)) := by
    simp only [binetBeta, hg]
    field_simp
    ring
  rw [heq]
  exact div_pos (hg0 ▸ hgt) (by positivity)

/-- `β(t) < t/12` for `t > 0`. -/
theorem binetBeta_lt {t : ℝ} (ht : 0 < t) : binetBeta t < t / 12 := by
  have hE := exp_sub_one_pos ht
  have hq : 0 < t ^ 2 - 6 * t + 12 := by nlinarith [sq_nonneg (t - 3)]
  have hP := Real.sum_le_exp_of_nonneg ht.le 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hP
  norm_num at hP
  have h5 : 0 < t ^ 5 * (t ^ 2 - t + 2) := by
    have : 0 < t ^ 2 - t + 2 := by nlinarith [sq_nonneg (t - 1 / 2)]
    positivity
  have key : 0 < Real.exp t * (t ^ 2 - 6 * t + 12) - (t ^ 2 + 6 * t + 12) := by
    nlinarith [mul_le_mul_of_nonneg_right hP hq.le]
  have heq : t / 12 - binetBeta t =
      (Real.exp t * (t ^ 2 - 6 * t + 12) - (t ^ 2 + 6 * t + 12)) / (12 * t * (Real.exp t - 1)) := by
    unfold binetBeta
    field_simp
    ring
  have : 0 < t / 12 - binetBeta t := by rw [heq]; positivity
  linarith

/-- `0 < Φ(x) < 1/(12x)` (Temme §3.6.1). -/
theorem binetIntegral_pos_lt {x : ℝ} (hx : 0 < x) :
    0 < binetIntegral x ∧ binetIntegral x < 1 / (12 * x) := by
  have hm : -x < 0 := by linarith
  have hsupp : ∀ f : ℝ → ℝ, (∀ t ∈ Ioi (0 : ℝ), 0 < f t) → IntegrableOn f (Ioi 0) →
      0 < ∫ t in Ioi (0 : ℝ), f t := by
    intro f hf hfi
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => (hf t ht).le))
      hfi]
    have : Function.support f ∩ Ioi 0 = Ioi 0 :=
      inter_eq_right.mpr fun t ht => (hf t ht).ne'
    rw [this, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  constructor
  · exact hsupp _ (fun t ht => div_pos (mul_pos (Real.exp_pos _) (binetBeta_pos ht)) ht)
      (integrableOn_exp_mul_binetBeta_div hx)
  · have hI : ∫ t in Ioi (0 : ℝ), 1 / 12 * Real.exp (-x * t) = 1 / (12 * x) := by
      rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi hm]
      simp only [mul_zero, Real.exp_zero]
      field_simp
    have hdiff := hsupp (fun t => 1 / 12 * Real.exp (-x * t) - Real.exp (-x * t) * binetBeta t / t)
      (fun t ht => by
        have ht' : (0 : ℝ) < t := ht
        have := binetBeta_lt ht'
        have he := Real.exp_pos (-x * t)
        rw [sub_pos, div_lt_iff₀ ht']
        nlinarith)
      (((integrableOn_exp_mul_Ioi hm 0).const_mul _).sub (integrableOn_exp_mul_binetBeta_div hx))
    rw [integral_sub ((integrableOn_exp_mul_Ioi hm 0).const_mul _)
      (integrableOn_exp_mul_binetBeta_div hx), hI] at hdiff
    unfold binetIntegral
    linarith

/-- `ln Γ(x) = (x - 1/2) ln x - x + (1/2) ln 2π + Φ(x)` with Binet's integral `Φ(x) = ∫₀^∞ e^(-xt)
β(t)/t dt`. -/
theorem log_Gamma_eq_add_binetIntegral {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + (1 / 2) * Real.log (2 * π) + binetIntegral x := by
  rw [log_Gamma_binet_exp hx, binetIntegral]
  rfl

/-! #### Partial fractions and Laplace transforms

The remaining Binet formulas rest on the partial fraction expansion of `coth`, which turns
`β(s)` into `∑ₘ 2s/(s² + aₘ²)` with `aₘ = 2π(m+1)` (Temme (3.26) with `N = 0`), and on the
symmetric Laplace identities obtained by one application of Fubini's theorem. -/

/-- `cosh(s/2)/sinh(s/2) = 2β(s) + 2/s`. -/
theorem cosh_div_sinh_half {s : ℝ} (hs : 0 < s) :
    Real.cosh (s / 2) / Real.sinh (s / 2) = 2 * binetBeta s + 2 / s := by
  have hs2 : Real.exp s = Real.exp (s / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hE1 : Real.exp (s / 2) ^ 2 - 1 ≠ 0 := by rw [← hs2]; exact (exp_sub_one_pos hs).ne'
  have hE0 : Real.exp (s / 2) ≠ 0 := Real.exp_ne_zero _
  have hsh : Real.exp (s / 2) - (Real.exp (s / 2))⁻¹ ≠ 0 := by
    intro h
    apply hE1
    field_simp at h
    linarith
  rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
  unfold binetBeta
  rw [hs2]
  field_simp
  ring

/-- The partial fraction expansion `β(s) = ∑ₘ 2s/(s² + (2π(m+1))²)`, from Mathlib's
`cot_series_rep'` at the imaginary point `x = i s/(2π)`. -/
theorem hasSum_binetBeta {s : ℝ} (hs : 0 < s) :
    HasSum (fun m : ℕ => 2 * s / (s ^ 2 + (2 * π * (m + 1)) ^ 2)) (binetBeta s) := by
  set f : ℕ → ℝ := fun m => 2 * s / (s ^ 2 + (2 * π * (m + 1)) ^ 2) with hf
  set c : ℂ := -(2 * π) * I with hc
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc0 : c ≠ 0 := by simp [hc, Real.pi_ne_zero]
  have hσ : 0 < s / (2 * π) := by positivity
  set x : ℂ := ((s / (2 * π) : ℝ) : ℂ) * I with hxdef
  have hxim : x.im = s / (2 * π) := by rw [hxdef, mul_I_im, ofReal_re]
  have hx : x ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have := congrArg Complex.im hn
    rw [hxim, intCast_im] at this
    linarith
  have hterm : ∀ n : ℕ, cotTerm x n = c * (f n : ℂ) := by
    intro n
    have hprod : (x + (n + 1)) * (x - (n + 1)) =
        -(((s / (2 * π)) ^ 2 + ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
      simp only [hxdef]
      push_cast
      linear_combination ((s : ℂ) / (2 * π)) ^ 2 * I_sq
    have hD : (0 : ℝ) < (s / (2 * π)) ^ 2 + ((n : ℝ) + 1) ^ 2 := by positivity
    have hD' : (0 : ℝ) < s ^ 2 + (2 * π * ((n : ℝ) + 1)) ^ 2 := by positivity
    rw [cotTerm_identity hx n, hprod]
    simp only [hf, hc, hxdef]
    have h1 : (((s / (2 * π)) ^ 2 + ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    have h2 : ((s ^ 2 + (2 * π * ((n : ℝ) + 1)) ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD'.ne'
    push_cast at h1 h2 ⊢
    field_simp
  have hcot : (π : ℂ) * Complex.cot (π * x) - 1 / x = c * (binetBeta s : ℂ) := by
    have hpx : (π : ℂ) * x = ((s / 2 : ℝ) : ℂ) * I := by
      rw [hxdef, ← mul_assoc, ← ofReal_mul, show π * (s / (2 * π)) = s / 2 by
        field_simp]
    have hsinh : Real.sinh (s / 2) ≠ 0 := (Real.sinh_pos_iff.mpr (by linarith)).ne'
    have hC : Real.cosh (s / 2) = (2 * binetBeta s + 2 / s) * Real.sinh (s / 2) := by
      rw [← cosh_div_sinh_half hs]; field_simp
    rw [hpx, Complex.cot_eq_cos_div_sin, Complex.cos_mul_I, Complex.sin_mul_I, ← ofReal_cosh,
      ← ofReal_sinh, hC, ofReal_mul]
    have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
    have hsh : (Real.sinh (s / 2) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hsinh
    generalize ((Real.sinh (s / 2) : ℝ) : ℂ) = S at hsh ⊢
    have hσ0 : ((s / (2 * π) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
    rw [mul_comm S I, mul_div_mul_right _ _ hsh, hxdef, ← div_div, Complex.div_I,
      Complex.div_I, hc]
    push_cast
    field_simp
    ring
  have hsumC : Summable fun n => c * (f n : ℂ) := (summable_cotTerm hx).congr hterm
  have hsumR : Summable f := by
    have := hsumC.mul_left c⁻¹
    simp only [← mul_assoc, inv_mul_cancel₀ hc0, one_mul] at this
    exact Complex.summable_ofReal.mp this
  have h := cot_series_rep' hx
  rw [hcot] at h
  have hterm' : ∀ n : ℕ, 1 / (x - (n + 1)) + 1 / (x + (n + 1)) = c * (f n : ℂ) := hterm
  simp_rw [hterm'] at h
  rw [tsum_mul_left, ← Complex.ofReal_tsum] at h
  have h' : binetBeta s = ∑' n, f n := by exact_mod_cast mul_left_cancel₀ hc0 h
  rw [h']
  exact hsumR.hasSum

/-- `β(s)/s = ∑ₘ 2/(s² + (2π(m+1))²)`. -/
theorem hasSum_binetBeta_div {s : ℝ} (hs : 0 < s) :
    HasSum (fun m : ℕ => 2 / (s ^ 2 + (2 * π * (m + 1)) ^ 2)) (binetBeta s / s) := by
  convert (hasSum_binetBeta hs).div_const s using 1
  funext m
  field_simp

/-- `1/(e^{2πt} - 1) = ∑ₘ e^{-2π(m+1)t}`. -/
theorem hasSum_recip_exp_two_pi_sub_one {t : ℝ} (ht : 0 < t) :
    HasSum (fun m : ℕ => Real.exp (-(2 * π * (m + 1)) * t))
      (1 / (Real.exp (2 * π * t) - 1)) := by
  set q := Real.exp (-(2 * π * t)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hterm : ∀ m : ℕ, Real.exp (-(2 * π * (m + 1)) * t) = q * q ^ m := by
    intro m
    rw [hq, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hval : 1 / (Real.exp (2 * π * t) - 1) = q * (1 - q)⁻¹ := by
    have h1 : Real.exp (2 * π * t) * q = 1 := by rw [hq, ← Real.exp_add]; simp
    have h2 : Real.exp (2 * π * t) - 1 ≠ 0 := (exp_sub_one_pos (by positivity)).ne'
    have h3 : 1 - q ≠ 0 := by linarith
    field_simp
    linear_combination -h1
  simp_rw [hterm, hval]
  exact (hasSum_geometric_of_lt_one hq0 hq1).mul_left q

/-- The Laplace transforms of `cos` and `sin`. -/
theorem integral_exp_mul_cos_sin {x t : ℝ} (hx : 0 < x) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) * Real.cos (t * s) = x / (x ^ 2 + t ^ 2) ∧
      ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) * Real.sin (t * s) = t / (x ^ 2 + t ^ 2) := by
  set a : ℂ := -x + t * I with ha
  have hare : a.re < 0 := by simp [ha]; linarith
  have hint := integrableOn_exp_mul_complex_Ioi hare 0
  have h := integral_exp_mul_complex_Ioi hare 0
  simp only [ofReal_zero, mul_zero, Complex.exp_zero] at h
  have ha0 : a ≠ 0 := fun h0 => by rw [h0, zero_re] at hare; exact lt_irrefl _ hare
  have hd : ((x ^ 2 + t ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < x ^ 2 + t ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hval : -1 / a = ((x / (x ^ 2 + t ^ 2) : ℝ) : ℂ) + ((t / (x ^ 2 + t ^ 2) : ℝ) : ℂ) * I := by
    have hd' : (x : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hd
    have e : ((x / (x ^ 2 + t ^ 2) : ℝ) : ℂ) + ((t / (x ^ 2 + t ^ 2) : ℝ) : ℂ) * I =
        ((x : ℂ) + t * I) / ((x : ℂ) ^ 2 + (t : ℂ) ^ 2) := by
      push_cast; field_simp
    rw [e, div_eq_div_iff ha0 hd', ha]
    linear_combination (-(t : ℂ) ^ 2) * I_sq
  rw [hval] at h
  have hre : ∀ s : ℝ, RCLike.re (Complex.exp (a * s)) =
      Real.exp (-x * s) * Real.cos (t * s) := by
    intro s
    rw [RCLike.re_to_complex, Complex.exp_re]
    simp [ha]
  have him : ∀ s : ℝ, RCLike.im (Complex.exp (a * s)) =
      Real.exp (-x * s) * Real.sin (t * s) := by
    intro s
    rw [RCLike.im_to_complex, Complex.exp_im]
    simp [ha]
  constructor
  · have := integral_re hint
    simp_rw [hre] at this
    rw [this, h, RCLike.re_to_complex, add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero]
  · have := integral_im hint
    simp_rw [him] at this
    rw [this, h, RCLike.im_to_complex, add_im, ofReal_im, mul_I_im, ofReal_re, zero_add]

/-- Integrability on `(0, ∞)²` of `e^{-xs} e^{-at} g(st)` with `|g| ≤ 1`. -/
theorem integrable_exp_mul_exp_prod {x a : ℝ} (hx : 0 < x) (ha : 0 < a) {g : ℝ → ℝ}
    (hg : Continuous g) (hg1 : ∀ y, |g y| ≤ 1) :
    Integrable (Function.uncurry fun s t : ℝ => Real.exp (-x * s) * Real.exp (-a * t) * g (s * t))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hprod := (integrableOn_exp_mul_Ioi (by linarith : -x < 0) 0).mul_prod
    (integrableOn_exp_mul_Ioi (by linarith : -a < 0) 0)
  refine hprod.mono' ?_ (Eventually.of_forall fun p => ?_)
  · exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
      Real.exp (-x * p.1) * Real.exp (-a * p.2) * g (p.1 * p.2)).aestronglyMeasurable
  · obtain ⟨u, v⟩ := p
    simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul, Real.abs_exp]
    have := hg1 (u * v)
    have h1 := Real.exp_pos (-x * u)
    have h2 := Real.exp_pos (-a * v)
    nlinarith [mul_pos h1 h2, abs_nonneg (g (u * v))]

/-- `a ∫₀^∞ e^{-xs}/(s² + a²) ds = x ∫₀^∞ e^{-at}/(t² + x²) dt`. -/
theorem integral_exp_div_sq_add_sq_symm {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    a * ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) / (s ^ 2 + a ^ 2) =
      x * ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) / (t ^ 2 + x ^ 2) := by
  have hswap := integral_integral_swap
    (integrable_exp_mul_exp_prod hx ha Real.continuous_cos fun y => Real.abs_cos_le_one y)
  have hL : ∀ s ∈ Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ),
      Real.exp (-x * s) * Real.exp (-a * t) * Real.cos (s * t) =
        a * (Real.exp (-x * s) / (s ^ 2 + a ^ 2)) := by
    intro s _
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => show Real.exp (-x * s) *
      Real.exp (-a * t) * Real.cos (s * t) = Real.exp (-x * s) * (Real.exp (-a * t) *
        Real.cos (s * t)) by ring), MeasureTheory.integral_const_mul,
      (integral_exp_mul_cos_sin (t := s) ha).1]
    field_simp
    ring
  have hR : ∀ t ∈ Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
      Real.exp (-x * s) * Real.exp (-a * t) * Real.cos (s * t) =
        x * (Real.exp (-a * t) / (t ^ 2 + x ^ 2)) := by
    intro t _
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => show Real.exp (-x * s) *
      Real.exp (-a * t) * Real.cos (s * t) = Real.exp (-a * t) * (Real.exp (-x * s) *
        Real.cos (t * s)) by rw [mul_comm s t]; ring), MeasureTheory.integral_const_mul,
      (integral_exp_mul_cos_sin (t := t) hx).1]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hL, setIntegral_congr_fun measurableSet_Ioi hR,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hswap
  exact hswap

/-- `∫₀^∞ e^{-xs} s/(s² + a²) ds = ∫₀^∞ e^{-at} t/(t² + x²) dt`. -/
theorem integral_exp_mul_div_sq_add_sq_symm {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) * (s / (s ^ 2 + a ^ 2)) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * (t / (t ^ 2 + x ^ 2)) := by
  have hswap := integral_integral_swap
    (integrable_exp_mul_exp_prod hx ha Real.continuous_sin fun y => Real.abs_sin_le_one y)
  have hL : ∀ s ∈ Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ),
      Real.exp (-x * s) * Real.exp (-a * t) * Real.sin (s * t) =
        Real.exp (-x * s) * (s / (s ^ 2 + a ^ 2)) := by
    intro s _
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => show Real.exp (-x * s) *
      Real.exp (-a * t) * Real.sin (s * t) = Real.exp (-x * s) * (Real.exp (-a * t) *
        Real.sin (s * t)) by ring), MeasureTheory.integral_const_mul,
      (integral_exp_mul_cos_sin (t := s) ha).2]
    ring_nf
  have hR : ∀ t ∈ Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
      Real.exp (-x * s) * Real.exp (-a * t) * Real.sin (s * t) =
        Real.exp (-a * t) * (t / (t ^ 2 + x ^ 2)) := by
    intro t _
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => show Real.exp (-x * s) *
      Real.exp (-a * t) * Real.sin (s * t) = Real.exp (-a * t) * (Real.exp (-x * s) *
        Real.sin (t * s)) by rw [mul_comm s t]; ring), MeasureTheory.integral_const_mul,
      (integral_exp_mul_cos_sin (t := t) hx).2]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hL, setIntegral_congr_fun measurableSet_Ioi hR]
    at hswap
  exact hswap

/-- `e^(-xs)/(s² + a²)` is integrable on `(0, ∞)` for `x, a > 0`. -/
theorem integrableOn_exp_div_sq_add_sq {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    IntegrableOn (fun s => Real.exp (-x * s) / (s ^ 2 + a ^ 2)) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by linarith : -x < 0) 0).const_mul
    (1 / a ^ 2)) ?_ (Eventually.of_forall fun s => ?_)
  · exact (Continuous.div (by fun_prop) (by fun_prop) fun s => by positivity).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_div, Real.abs_exp, abs_of_pos (by positivity : 0 < s ^ 2 + a ^ 2),
      div_le_iff₀ (by positivity)]
    have := Real.exp_pos (-x * s)
    field_simp
    nlinarith [sq_nonneg s]

/-- `∫₀^∞ e^{-xs}/(s² + a²) ds ≤ 1/(a² x)`. -/
theorem integral_exp_div_sq_add_sq_le {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) / (s ^ 2 + a ^ 2) ≤ 1 / (a ^ 2 * x) := by
  have hm : -x < 0 := by linarith
  have hle : ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) / (s ^ 2 + a ^ 2) ≤
      ∫ s in Ioi (0 : ℝ), 1 / a ^ 2 * Real.exp (-x * s) := by
    refine setIntegral_mono_on (integrableOn_exp_div_sq_add_sq hx ha)
      ((integrableOn_exp_mul_Ioi hm 0).const_mul _) measurableSet_Ioi fun s _ => ?_
    rw [div_le_iff₀ (by positivity)]
    have := Real.exp_pos (-x * s)
    field_simp
    nlinarith [sq_nonneg s]
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi hm] at hle
  convert hle using 1
  simp only [mul_zero, Real.exp_zero]
  field_simp

/-- `∫₀^∞ e^(-xs)/(s² + a²) ds ≥ 0`. -/
theorem integral_exp_div_sq_add_sq_nonneg {x a : ℝ} :
    0 ≤ ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) / (s ^ 2 + a ^ 2) :=
  setIntegral_nonneg measurableSet_Ioi fun s _ => by positivity

/-- `∑ₘ 1/(aₘ² x)` is summable. -/
theorem summable_recip_sq_two_pi {x : ℝ} :
    Summable fun m : ℕ => 1 / ((2 * π * (m + 1)) ^ 2 * x) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  convert h.mul_left (1 / (4 * π ^ 2 * x)) using 1
  funext m
  push_cast
  field_simp
  ring

/-- `Φ(x) = ∑ₘ 2 ∫₀^∞ e^{-xs}/(s² + aₘ²) ds`. -/
theorem hasSum_binetIntegral {x : ℝ} (hx : 0 < x) :
    HasSum (fun m : ℕ => 2 * ∫ s in Ioi (0 : ℝ),
      Real.exp (-x * s) / (s ^ 2 + (2 * π * (m + 1)) ^ 2)) (binetIntegral x) := by
  set F : ℕ → ℝ → ℝ := fun m s => 2 * (Real.exp (-x * s) / (s ^ 2 + (2 * π * (m + 1)) ^ 2))
    with hF
  have ha : ∀ m : ℕ, 0 < 2 * π * (m + 1) := fun m => by positivity
  have hint : ∀ m, Integrable (F m) (volume.restrict (Ioi (0 : ℝ))) :=
    fun m => (integrableOn_exp_div_sq_add_sq hx (ha m)).const_mul 2
  have hnorm : ∀ m, ∫ s in Ioi (0 : ℝ), ‖F m s‖ = ∫ s in Ioi (0 : ℝ), F m s := fun m =>
    setIntegral_congr_fun measurableSet_Ioi fun s _ => Real.norm_of_nonneg (by positivity)
  have hsum : Summable fun m => ∫ s in Ioi (0 : ℝ), ‖F m s‖ := by
    simp_rw [hnorm, hF, MeasureTheory.integral_const_mul]
    refine Summable.of_nonneg_of_le (fun m => by
      have := integral_exp_div_sq_add_sq_nonneg (x := x) (a := 2 * π * (m + 1)); positivity)
      (fun m => by
        have := integral_exp_div_sq_add_sq_le hx (ha m)
        exact mul_le_mul_of_nonneg_left this zero_le_two)
      (summable_recip_sq_two_pi.mul_left 2)
  have key := integral_tsum_of_summable_integral_norm hint hsum
  have hsum' : Summable fun m => ∫ s in Ioi (0 : ℝ), F m s := hsum.congr hnorm
  simp_rw [hF, MeasureTheory.integral_const_mul] at hsum' key
  rw [show binetIntegral x = ∑' m : ℕ, 2 * ∫ s in Ioi (0 : ℝ),
      Real.exp (-x * s) / (s ^ 2 + (2 * π * (m + 1)) ^ 2) from ?_]
  · exact hsum'.hasSum
  rw [key, binetIntegral]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs' : (0 : ℝ) < s := hs
  rw [mul_div_assoc, ← (hasSum_binetBeta_div hs').tsum_eq, ← tsum_mul_left]
  congr 1
  funext m
  ring

/-- `∫₀^∞ arctan(t/x) e^{-at} dt = (x/a) ∫₀^∞ e^{-at}/(t² + x²) dt`, by parts. -/
theorem integral_arctan_mul_exp {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), Real.arctan (t / x) * Real.exp (-a * t) =
      x / a * ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) / (t ^ 2 + x ^ 2) := by
  have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t => Real.arctan (t / x))
      (x / (t ^ 2 + x ^ 2)) t := by
    intro t _
    have := (Real.hasDerivAt_arctan (t / x)).comp t ((hasDerivAt_id t).div_const x)
    have hx' : x ≠ 0 := hx.ne'
    exact this.congr_deriv (by deriv_simp)
  have hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t => -Real.exp (-a * t) / a)
      (Real.exp (-a * t)) t := by
    intro t _
    have := (((hasDerivAt_id t).const_mul (-a)).exp.neg).div_const a
    have ha' : a ≠ 0 := ha.ne'
    exact this.congr_deriv (by deriv_simp)
  have hm : -a < 0 := by linarith
  have hbound : ∀ t, |Real.arctan (t / x)| ≤ π / 2 := fun t =>
    abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  have huv' : IntegrableOn (fun t => Real.arctan (t / x) * Real.exp (-a * t)) (Ioi 0) := by
    refine Integrable.mono' ((integrableOn_exp_mul_Ioi hm 0).const_mul (π / 2)) ?_
      (Eventually.of_forall fun t => ?_)
    · exact (by fun_prop : Continuous fun t => Real.arctan (t / x) * Real.exp (-a * t))
        |>.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
      exact mul_le_mul_of_nonneg_right (hbound t) (Real.exp_pos _).le
  have hu'v : IntegrableOn (fun t => x / (t ^ 2 + x ^ 2) * (-Real.exp (-a * t) / a)) (Ioi 0) := by
    have := ((integrableOn_exp_div_sq_add_sq ha hx).const_mul (-(x / a)))
    refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
    field_simp
  have hzero : Tendsto (fun t => Real.arctan (t / x) * (-Real.exp (-a * t) / a)) (𝓝[>] 0)
      (𝓝 0) := by
    have : Continuous fun t => Real.arctan (t / x) * (-Real.exp (-a * t) / a) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hinfty : Tendsto (fun t => Real.arctan (t / x) * (-Real.exp (-a * t) / a)) atTop
      (𝓝 0) := by
    have hexp : Tendsto (fun t => -Real.exp (-a * t) / a) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hm)).neg.div_const a
      simpa [Function.comp_def] using this
    refine (hexp.zero_mul_isBoundedUnder_le ?_).congr fun t => mul_comm _ _
    exact isBoundedUnder_of_eventually_le (a := π / 2) (Eventually.of_forall fun t => by
      simpa [Real.norm_eq_abs] using hbound t)
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hzero hinfty
  rw [h, sub_self, zero_sub, ← MeasureTheory.integral_neg, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

/-- `∫₀^∞ arctan(t/x) e^{-at} dt = ∫₀^∞ e^{-xs}/(s² + a²) ds`. -/
theorem integral_arctan_mul_exp_eq {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), Real.arctan (t / x) * Real.exp (-a * t) =
      ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) / (s ^ 2 + a ^ 2) := by
  rw [integral_arctan_mul_exp hx ha, div_mul_eq_mul_div, ← integral_exp_div_sq_add_sq_symm hx ha]
  field_simp

/-- DLMF 5.9.10, Binet's second formula: `ln Γ(x) = (x - 1/2) ln x - x + (1/2) ln 2π + 2 ∫₀^∞
arctan(t/x)/(e^(2πt) - 1) dt` for `x > 0`. -/
@[dlmf 5.9.E10]
theorem log_Gamma_binet_arctan {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + (1 / 2) * Real.log (2 * π) +
        2 * ∫ t : ℝ in Set.Ioi 0,
          Real.arctan (t / x) / (Real.exp (2 * π * t) - 1) := by
  rw [log_Gamma_eq_add_binetIntegral hx]
  congr 1
  set F : ℕ → ℝ → ℝ := fun m t => Real.arctan (t / x) * Real.exp (-(2 * π * (m + 1)) * t)
    with hF
  have ha : ∀ m : ℕ, 0 < 2 * π * (m + 1) := fun m => by positivity
  have hval : ∀ m, ∫ t in Ioi (0 : ℝ), F m t =
      ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) / (s ^ 2 + (2 * π * (m + 1)) ^ 2) := fun m =>
    integral_arctan_mul_exp_eq hx (ha m)
  have hFnn : ∀ m, ∀ t ∈ Ioi (0 : ℝ), 0 ≤ F m t := fun m t ht =>
    mul_nonneg (Real.arctan_nonneg.mpr (div_nonneg (le_of_lt ht) hx.le)) (Real.exp_pos _).le
  have hint : ∀ m, Integrable (F m) (volume.restrict (Ioi (0 : ℝ))) := by
    intro m
    refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by linarith [ha m] :
      -(2 * π * (m + 1)) < 0) 0).const_mul (π / 2)) ?_ (Eventually.of_forall fun t => ?_)
    · exact (by fun_prop : Continuous (F m)).aestronglyMeasurable
    · simp only [hF, Real.norm_eq_abs, abs_mul, Real.abs_exp]
      have h1 := Real.neg_pi_div_two_lt_arctan (t / x)
      exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith, (Real.arctan_lt_pi_div_two _).le⟩)
        (Real.exp_pos _).le
  have hnorm : ∀ m, ∫ t in Ioi (0 : ℝ), ‖F m t‖ = ∫ t in Ioi (0 : ℝ), F m t := fun m =>
    setIntegral_congr_fun measurableSet_Ioi fun t ht => Real.norm_of_nonneg (hFnn m t ht)
  have hS := hasSum_binetIntegral hx
  have hsum : Summable fun m => ∫ t in Ioi (0 : ℝ), ‖F m t‖ := by
    simp_rw [hnorm, hval]
    exact (hS.summable.mul_left (1 / 2)).congr fun m => by ring
  have key := integral_tsum_of_summable_integral_norm hint hsum
  rw [← hS.tsum_eq, ← MeasureTheory.integral_const_mul]
  simp_rw [hval] at key
  rw [tsum_mul_left, key, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [hF]
  rw [tsum_mul_left, (hasSum_recip_exp_two_pi_sub_one ht).tsum_eq]
  ring

/-- DLMF 5.9.10 (logarithmic form): `ln Γ(x) = (x - 1/2) ln x - x + (1/2) ln 2π - (x/π) ∫₀^∞ ln(1 -
e^(-2πt))/(t² + x²) dt` for `x > 0`. -/
@[dlmf 5.9.E10_1]
theorem log_Gamma_binet_log {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + (1 / 2) * Real.log (2 * π) -
        x / π * ∫ t : ℝ in Set.Ioi 0,
          Real.log (1 - Real.exp (-2 * π * t)) / (t ^ 2 + x ^ 2) := by
  rw [log_Gamma_eq_add_binetIntegral hx]
  suffices h : binetIntegral x = x / π * ∫ t : ℝ in Set.Ioi 0,
      -(Real.log (1 - Real.exp (-2 * π * t)) / (t ^ 2 + x ^ 2)) by
    rw [h, MeasureTheory.integral_neg]; ring
  set F : ℕ → ℝ → ℝ := fun m t =>
    Real.exp (-(2 * π * (m + 1)) * t) / (t ^ 2 + x ^ 2) / (m + 1) with hF
  have ha : ∀ m : ℕ, 0 < 2 * π * (m + 1) := fun m => by positivity
  have hval : ∀ m, x / π * ∫ t in Ioi (0 : ℝ), F m t =
      2 * ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) / (s ^ 2 + (2 * π * (m + 1)) ^ 2) := by
    intro m
    have h := integral_exp_div_sq_add_sq_symm hx (ha m)
    simp only [hF]
    rw [MeasureTheory.integral_div]
    set I1 := ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) / (s ^ 2 + (2 * π * (m + 1)) ^ 2)
    set I2 := ∫ t in Ioi (0 : ℝ), Real.exp (-(2 * π * (m + 1)) * t) / (t ^ 2 + x ^ 2)
    have hπ := Real.pi_pos
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    calc x / π * (I2 / (m + 1)) = (x * I2) / (π * (m + 1)) := by field_simp
      _ = (2 * π * (m + 1) * I1) / (π * (m + 1)) := by rw [h]
      _ = 2 * I1 := by field_simp
  have hint : ∀ m, Integrable (F m) (volume.restrict (Ioi (0 : ℝ))) := fun m =>
    (integrableOn_exp_div_sq_add_sq (ha m) hx).div_const _
  have hnorm : ∀ m, ∫ t in Ioi (0 : ℝ), ‖F m t‖ = ∫ t in Ioi (0 : ℝ), F m t := fun m =>
    setIntegral_congr_fun measurableSet_Ioi fun t _ => Real.norm_of_nonneg (by positivity)
  have hS := hasSum_binetIntegral hx
  have hsum : Summable fun m => ∫ t in Ioi (0 : ℝ), ‖F m t‖ := by
    simp_rw [hnorm]
    have : (fun m => ∫ t in Ioi (0 : ℝ), F m t) = fun m : ℕ => π / x * (2 *
        ∫ s in Ioi (0 : ℝ), Real.exp (-x * s) / (s ^ 2 + (2 * π * (m + 1)) ^ 2)) := by
      funext m
      rw [← hval m]
      field_simp
    rw [this]
    exact hS.summable.mul_left _
  have key := integral_tsum_of_summable_integral_norm hint hsum
  rw [← hS.tsum_eq]
  simp_rw [← hval]
  rw [tsum_mul_left, key]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  have hq : |Real.exp (-2 * π * t)| < 1 := by
    rw [Real.abs_exp, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have hlog := (Real.hasSum_pow_div_log_of_abs_lt_one hq).div_const (t ^ 2 + x ^ 2)
  rw [← neg_div, ← hlog.tsum_eq]
  congr 1
  funext m
  simp only [hF]
  rw [← Real.exp_nat_mul]
  push_cast
  field_simp

end Binet

end DLMF.Gamma
end
end
