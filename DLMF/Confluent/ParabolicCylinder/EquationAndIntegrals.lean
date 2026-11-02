/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Basic.Functions
public import DLMF.ParabolicCylinder.Basic.WeberEquation

public import DLMF.Confluent.Asymptotics
public import DLMF.Confluent.Relations
public import TauCeti.RingTheory.Polynomial.Hermite.Derivative

/-!
# Parabolic cylinder functions: Weber's equation, recurrences and integrals

Weber's function `U(a,z)` (`pcfU`) is the solution of `w'' = (z²/4 + a) w` that is recessive as
`z → +∞` (DLMF Chapter 12, Temme §7.3.3). It is defined, following DLMF 12.4.1, through the even
and odd Kummer solutions `u₁(a,z) = e^{-z²/4} M(a/2 + 1/4, 1/2, z²/2)` and
`u₂(a,z) = z e^{-z²/4} M(a/2 + 3/4, 3/2, z²/2)` with the initial values 12.2.6 and 12.2.7, so
that `U(a, ·)` is entire for every `a`. This file proves the relation to Tricomi's function,
the asymptotic expansion and the Laplace-type integral of `U`. Weber's equation, the initial
values, uniqueness of solutions, the recurrences and the Hermite specialization are in
`DLMF.ParabolicCylinder.Basic.WeberEquation`.

## Main results

* `pcfU_eq_kummerU`: `U(a,z) = 2^{-1/4-a/2} e^{-z²/4} U(a/2 + 1/4, 1/2, z²/2)` for `re z > 0`
  (DLMF 12.7.14).
* `hasAsymptoticExpansion_pcfU`:
  `U(a,x) ~ e^{-x²/4} x^{-a-1/2} ∑ (-1)^s (a + 1/2)_{2s}/(s! (2x²)^s)` (DLMF 12.9.1).
* `pcfU_eq_integral`: `U(a,z) = e^{-z²/4}/Γ(1/2+a) ∫₀^∞ t^{a-1/2} e^{-t²/2-zt} dt` for
  `re a > -1/2` (DLMF 12.5.1).

## Implementation notes

Whittaker's `D_ν(z) = U(-ν - 1/2, z)` is `pcfD`.
-/

@[expose] public section

open Complex Filter MeasureTheory Asymptotics Set

open scoped Real Topology Nat

open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- **`U(a,z)` through Tricomi's function** (DLMF 12.7.14), for `re z > 0`:
`U(a,z) = 2^{-1/4 - a/2} e^{-z²/4} U(a/2 + 1/4, 1/2, z²/2)`. -/
@[dlmf 12.7.E14]
theorem pcfU_eq_kummerU (a : ℂ) {z : ℂ} (hre : 0 < z.re) :
    pcfU a z = (2 : ℂ) ^ (-(1 / 4) - a / 2) * exp (-z ^ 2 / 4) *
      kummerU (a / 2 + 1 / 4) (1 / 2) (z ^ 2 / 2) := by
  have hb : ∀ k : ℤ, (1 / 2 : ℂ) ≠ k := fun k h => by
    have := congrArg Complex.re h
    simp at this
    have h2 : (2 : ℝ) * k = 1 := by linarith
    have : (2 : ℤ) * k = 1 := by exact_mod_cast h2
    omega
  set s2 : ℂ := (Real.sqrt 2 : ℂ) with hs2
  have hs2sq : s2 * s2 = 2 := by
    rw [hs2, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs20 : s2 ≠ 0 := by intro h; rw [h, zero_mul] at hs2sq; norm_num at hs2sq
  have hy : z ^ 2 / 2 = (z / s2) ^ 2 := by
    rw [div_pow, sq s2, hs2sq]
  have hre' : 0 < (z / s2).re := by
    rw [hs2, Complex.div_ofReal_re]
    exact div_pos hre (Real.sqrt_pos.mpr (by norm_num))
  have hsqrt : (z ^ 2 / 2) ^ (1 / 2 : ℂ) = z / s2 := by
    rw [hy, sq_cpow_of_re_pos hre', show (2 : ℂ) * (1 / 2) = 1 by norm_num, Complex.cpow_one]
  have hGm : Gamma (-1 / 2 : ℂ) = -2 * (Real.sqrt π : ℂ) := by
    have h := Complex.Gamma_add_one (-1 / 2 : ℂ) (by norm_num)
    rw [show (-1 / 2 : ℂ) + 1 = 1 / 2 by ring, Complex.Gamma_one_half_eq_sqrt] at h
    linear_combination 2 * h
  have h2pow : (2 : ℂ) ^ (-(a / 2 - 1 / 4)) = (2 : ℂ) ^ (-(1 / 4) - a / 2) * s2 := by
    rw [hs2, ← two_cpow_half, ← Complex.cpow_add _ _ two_ne_zero]
    ring_nf
  rw [kummerU_eq_connection _ _ _ hb, kummerUConnection, pcfU, pcfEven, pcfOdd,
    show (1 : ℂ) - 1 / 2 = 1 / 2 by ring, show a / 2 + 1 / 4 - 1 / 2 + 1 = 3 / 4 + a / 2 by ring,
    show (1 / 2 : ℂ) - 1 = -1 / 2 by ring, show (2 : ℂ) - 1 / 2 = 3 / 2 by ring,
    show a / 2 + 3 / 4 = 3 / 4 + a / 2 by ring, show a / 2 + 1 / 4 = 1 / 4 + a / 2 by ring,
    hsqrt, hGm, Complex.Gamma_one_half_eq_sqrt, h2pow, show -(1 / 4 + a / 2) = -(1 / 4) - a / 2 by ring]
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  generalize kummerM (3 / 4 + a / 2) (3 / 2) (z ^ 2 / 2) = N
  generalize kummerM (1 / 4 + a / 2) (1 / 2) (z ^ 2 / 2) = M
  generalize Gamma (1 / 4 + a / 2) = G1
  generalize Gamma (3 / 4 + a / 2) = G3
  field_simp
  linear_combination (-(z * N * G1⁻¹)) * hs2sq

/-- Legendre duplication for Pochhammer symbols: `(2c)_{2s} = 4^s (c)_s (c + 1/2)_s`. -/
theorem poch_two_mul (c : ℂ) (s : ℕ) :
    poch (2 * c) (2 * s) = 4 ^ s * poch c s * poch (c + 1 / 2) s := by
  induction s with
  | zero => simp [poch_zero]
  | succ s ih =>
    rw [show 2 * (s + 1) = 2 * s + 1 + 1 by ring, poch_succ, poch_succ, ih, poch_succ c,
      poch_succ (c + 1 / 2), pow_succ]
    push_cast
    ring

/-- **Asymptotic expansion of `U(a,x)`** (DLMF 12.9.1, Temme §7.3.3):
`U(a,x) ~ e^{-x²/4} x^{-a-1/2} ∑ (-1)^s (a + 1/2)_{2s} / (s! (2x²)^s)` as `x → +∞`. -/
@[dlmf 12.9.E1]
theorem hasAsymptoticExpansion_pcfU (a : ℂ) :
    HasAsymptoticExpansion atTop
      (fun (s : ℕ) (x : ℝ) => exp (-(x : ℂ) ^ 2 / 4) * (x : ℂ) ^ (-a - 1 / 2 - 2 * (s : ℂ)))
      (fun s => (-1) ^ s * poch (a + 1 / 2) (2 * s) / (2 ^ s * s.factorial))
      (fun x : ℝ => pcfU a x) := by
  set α : ℂ := a / 2 + 1 / 4 with hα
  have hsq : Tendsto (fun x : ℝ => x ^ 2 / 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos
  have h := (((hasAsymptoticExpansion_kummerU α (1 / 2)).comp_tendsto hsq).mul_left
    (fun x : ℝ => (2 : ℂ) ^ (-(1 / 4) - a / 2) * exp (-(x : ℂ) ^ 2 / 4))).smul_scale
    (κ := fun s => (2 : ℂ) ^ s) (ψ := fun (s : ℕ) (x : ℝ) =>
      exp (-(x : ℂ) ^ 2 / 4) * (x : ℂ) ^ (-a - 1 / 2 - 2 * (s : ℂ))) (fun s => ?_)
  · refine (h.congr' ?_).congr_coeff ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx
      simp only [Function.comp_apply, smul_eq_mul]
      rw [pcfU_eq_kummerU a (by simpa using hx)]
      push_cast
      ring
    · funext s
      rw [tricomiCoeff, show α - 1 / 2 + 1 = α + 1 / 2 by ring, smul_eq_mul,
        show a + 1 / 2 = 2 * α by rw [hα]; ring, poch_two_mul]
      have hf : (s.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr s.factorial_ne_zero
      rw [show (4 : ℂ) ^ s = 2 ^ s * 2 ^ s by rw [← mul_pow]; norm_num]
      field_simp
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hxy : (((x ^ 2 / 2 : ℝ)) : ℂ) ^ (-((s : ℂ) + α)) =
        (x : ℂ) ^ (2 * (-((s : ℂ) + α))) * (2 : ℂ) ^ ((s : ℂ) + α) := by
      rw [show (x ^ 2 / 2 : ℝ) = x ^ 2 * (1 / 2) by ring, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (by positivity) (by norm_num), Complex.ofReal_pow,
        sq_cpow_of_re_pos (by simpa using hx), one_div, Complex.ofReal_inv,
        Complex.inv_cpow _ _ (by norm_num [Complex.arg_ofReal_of_nonneg, Real.pi_pos.ne]),
        ← Complex.cpow_neg]
      push_cast
      ring_nf
    rw [hxy]
    have h2 : (2 : ℂ) ^ (-(1 / 4) - a / 2) * (2 : ℂ) ^ ((s : ℂ) + α) = 2 ^ s := by
      rw [← Complex.cpow_add _ _ two_ne_zero, hα,
        show -(1 / 4) - a / 2 + ((s : ℂ) + (a / 2 + 1 / 4)) = (s : ℂ) by ring,
        Complex.cpow_natCast]
    rw [show (x : ℂ) ^ (2 * (-((s : ℂ) + α))) = (x : ℂ) ^ (-a - 1 / 2 - 2 * (s : ℂ)) by
      rw [hα]; ring_nf]
    linear_combination (exp (-(x : ℂ) ^ 2 / 4) * (x : ℂ) ^ (-a - 1 / 2 - 2 * (s : ℂ))) * h2

/-! ### The Laplace-type integral 12.5.1 -/

/-- `-t²/2 - xt ≤ -t²/4 + x²`. -/
theorem pcf_exponent_le (t x : ℝ) : -t ^ 2 / 2 - x * t ≤ -t ^ 2 / 4 + x ^ 2 := by
  nlinarith [sq_nonneg (t / 2 + x)]

/-- For `t > 0`, `|t^c e^{-t²/2 - zt}| = t^{Re c} e^{-t²/2 - (Re z) t}`. -/
theorem norm_pcfIntegrand (c z : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ c * exp (-(t : ℂ) ^ 2 / 2 - z * t)‖ =
      t ^ c.re * Real.exp (-t ^ 2 / 2 - z.re * t) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  congr 2
  simp [Complex.sub_re, Complex.mul_re, sq]

/-- For `|Re z| ≤ R` and `t > 0`, `|t^c e^{-t²/2 - zt}| ≤ e^{R²} t^{Re c} e^{-t²/4}`. -/
theorem norm_pcfIntegrand_le (c z : ℂ) {R : ℝ} (hR : |z.re| ≤ R) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ c * exp (-(t : ℂ) ^ 2 / 2 - z * t)‖ ≤
      Real.exp (R ^ 2) * (t ^ c.re * Real.exp (-t ^ 2 / 4)) := by
  rw [norm_pcfIntegrand c z ht]
  have hx : z.re ^ 2 ≤ R ^ 2 := by
    have := sq_abs z.re ▸ pow_le_pow_left₀ (abs_nonneg _) hR 2
    exact this
  have he : Real.exp (-t ^ 2 / 2 - z.re * t) ≤ Real.exp (R ^ 2) * Real.exp (-t ^ 2 / 4) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [pcf_exponent_le t z.re])
  calc t ^ c.re * Real.exp (-t ^ 2 / 2 - z.re * t)
      ≤ t ^ c.re * (Real.exp (R ^ 2) * Real.exp (-t ^ 2 / 4)) :=
        mul_le_mul_of_nonneg_left he (Real.rpow_nonneg ht.le _)
    _ = _ := by ring

/-- For `p > -1`, `t^p e^{-t²/4}` is integrable on `(0, ∞)`. -/
theorem integrableOn_rpow_mul_exp_neg_sq_div_four {p : ℝ} (hp : -1 < p) :
    IntegrableOn (fun t : ℝ => t ^ p * Real.exp (-t ^ 2 / 4)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := p) (p := 2) (b := 1 / 4) hp
    (by norm_num) (by norm_num)
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only
  rw [show (t ^ (2 : ℝ)) = t ^ 2 from Real.rpow_two t]
  ring_nf

/-- The integrand `t^c e^{-t²/2 - zt}` is continuous on `(0, ∞)`. -/
theorem continuousOn_pcfIntegrand (c z : ℂ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ c * exp (-(t : ℂ) ^ 2 / 2 - z * t)) (Ioi 0) := by
  refine ContinuousOn.mul (fun t ht => ?_) (by fun_prop)
  exact (Complex.continuousAt_ofReal_cpow_const t c (Or.inr (ne_of_gt ht))).continuousWithinAt

/-- For `Re c > -1`, the integrand `t^c e^{-t²/2 - zt}` is integrable on `(0, ∞)`. -/
theorem integrableOn_pcfIntegrand {c : ℂ} (hc : -1 < c.re) (z : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ c * exp (-(t : ℂ) ^ 2 / 2 - z * t)) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_rpow_mul_exp_neg_sq_div_four hc).const_mul
    (Real.exp (|z.re| ^ 2))) ((continuousOn_pcfIntegrand c z).aestronglyMeasurable
      measurableSet_Ioi) ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
    norm_pcfIntegrand_le c z le_rfl ht

/-- Differentiation of the moments in `z`: `∂_z M_c(z) = -M_{c+1}(z)`. -/
theorem hasDerivAt_pcfMoment {c : ℂ} (hc : -1 < c.re) (z₀ : ℂ) :
    HasDerivAt (pcfMoment c) (-pcfMoment (c + 1) z₀) z₀ := by
  set R : ℝ := ‖z₀‖ + 1
  have hc1 : -1 < (c + 1).re := by simp; linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun (z : ℂ) (t : ℝ) => (t : ℂ) ^ c * exp (-(t : ℂ) ^ 2 / 2 - z * t))
    (F' := fun (z : ℂ) (t : ℝ) => -((t : ℂ) ^ (c + 1) * exp (-(t : ℂ) ^ 2 / 2 - z * t)))
    (x₀ := z₀) (bound := fun t => Real.exp (R ^ 2) * (t ^ (c + 1).re * Real.exp (-t ^ 2 / 4)))
    (s := Metric.ball z₀ 1) (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (continuousOn_pcfIntegrand c z).aestronglyMeasurable
      measurableSet_Ioi)
    (integrableOn_pcfIntegrand hc z₀)
    ((continuousOn_pcfIntegrand (c + 1) z₀).aestronglyMeasurable measurableSet_Ioi).neg
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht z hz => by
      rw [norm_neg]
      refine norm_pcfIntegrand_le (c + 1) z ?_ ht
      have h1 : ‖z‖ < ‖z₀‖ + 1 := by
        have := norm_sub_norm_le z z₀
        rw [Metric.mem_ball, dist_eq_norm] at hz
        linarith
      exact (Complex.abs_re_le_norm z).trans h1.le)
    ((integrableOn_rpow_mul_exp_neg_sq_div_four hc1).const_mul _)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht z _ => by
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
      have h := (((hasDerivAt_id z).mul_const (t : ℂ)).const_sub
        (-(t : ℂ) ^ 2 / 2)).cexp.const_mul ((t : ℂ) ^ c)
      refine h.congr_deriv ?_
      rw [Complex.cpow_add _ _ ht0, Complex.cpow_one]
      simp only [id]
      ring)
  have hfun : (fun z => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ c * exp (-(t : ℂ) ^ 2 / 2 - z * t)) =
      pcfMoment c := rfl
  rw [hfun, integral_neg] at key
  exact key.2

/-- Integration by parts: `M_{c+2}(z) + z M_{c+1}(z) = (c + 1) M_c(z)`. -/
theorem pcfMoment_ibp {c : ℂ} (hc : -1 < c.re) (z : ℂ) :
    pcfMoment (c + 2) z + z * pcfMoment (c + 1) z = (c + 1) * pcfMoment c z := by
  have hc1 : -1 < (c + 1).re := by simp; linarith
  have hc2 : -1 < (c + 2).re := by simp; linarith
  have hc0 : c + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  set E : ℝ → ℂ := fun t => exp (-(t : ℂ) ^ 2 / 2 - z * t) with hE
  set g : ℝ → ℂ := fun t => (t : ℂ) ^ (c + 1) * E t with hg
  set g' : ℝ → ℂ := fun t => (c + 1) * ((t : ℂ) ^ c * E t) -
    ((t : ℂ) ^ (c + 2) * E t) - z * ((t : ℂ) ^ (c + 1) * E t) with hg'
  have hEd (t : ℝ) : HasDerivAt E (E t * (-(t : ℂ) - z)) t := by
    have hi : HasDerivAt (fun w : ℂ => -w ^ 2 / 2 - z * w) (-(t : ℂ) - z) (t : ℂ) := by
      convert (((hasDerivAt_pow 2 (t : ℂ)).div_const 2).neg.sub
        ((hasDerivAt_id (t : ℂ)).const_mul z)) using 1
      · funext w; simp only [Pi.sub_apply, Pi.neg_apply, id]; ring
      · ring
    exact hi.cexp.comp_ofReal
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt g (g' t) t := fun t ht => by
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    have hp := hasDerivAt_ofReal_cpow_const (ne_of_gt ht) hc0
    have h1 : (t : ℂ) ^ (c + 1) = (t : ℂ) ^ c * t := by
      rw [Complex.cpow_add _ _ ht0, Complex.cpow_one]
    have h2 : (t : ℂ) ^ (c + 2) = (t : ℂ) ^ c * t ^ 2 := by
      rw [Complex.cpow_add _ _ ht0, Complex.cpow_two]
    refine (hp.mul (hEd t)).congr_deriv ?_
    simp only [hg']
    rw [show c + 1 - 1 = c by ring, h1, h2]
    ring
  have hcont : ContinuousWithinAt g (Ici 0) 0 := by
    refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ (by fun_prop))
    exact Complex.continuousAt_ofReal_cpow_const 0 (c + 1) (Or.inl (by simp; linarith))
  have hint : IntegrableOn g' (Ioi 0) :=
    (((integrableOn_pcfIntegrand hc z).const_mul (c + 1)).sub
      (integrableOn_pcfIntegrand hc2 z)).sub ((integrableOn_pcfIntegrand hc1 z).const_mul z)
  have hlim : Tendsto g atTop (𝓝 0) := by
    have hb : Tendsto (fun t : ℝ => Real.exp (|z.re| ^ 2) *
        (t ^ (c + 1).re * Real.exp (-(1 / 4) * t))) atTop (𝓝 0) := by
      have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (c + 1).re (1 / 4)
        (by norm_num)).const_mul (Real.exp (|z.re| ^ 2))
      rwa [mul_zero] at this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop 1] with t ht
    have ht0 : 0 < t := by linarith
    refine (norm_pcfIntegrand_le (c + 1) z le_rfl ht0).trans ?_
    gcongr
    nlinarith
  have hibp := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have hg0 : g 0 = 0 := by
    simp only [hg, Complex.ofReal_zero]
    rw [Complex.zero_cpow hc0, zero_mul]
  rw [hg0, sub_zero] at hibp
  have hsplit : ∫ t in Ioi (0 : ℝ), g' t =
      (c + 1) * pcfMoment c z - pcfMoment (c + 2) z - z * pcfMoment (c + 1) z := by
    have i0 := (integrableOn_pcfIntegrand hc z).const_mul (c + 1)
    have i1 := integrableOn_pcfIntegrand hc2 z
    have i2 := (integrableOn_pcfIntegrand hc1 z).const_mul z
    have e1 := integral_sub i0 i1
    have e2 := integral_sub (i0.sub i1) i2
    simp only [Pi.sub_apply] at e1 e2
    simp only [pcfMoment]
    rw [← integral_const_mul, ← integral_const_mul, ← e1, ← e2]
  rw [hsplit] at hibp
  linear_combination -hibp

/-- `M_c(0) = 2^{(c-1)/2} Γ((c+1)/2)`, in the form `(1/2) Γ((c+1)/2) 2^{(c+1)/2}`. -/
theorem pcfMoment_zero {c : ℂ} (hc : -1 < c.re) :
    pcfMoment c 0 = 1 / 2 * Gamma ((c + 1) / 2) * (2 : ℂ) ^ ((c + 1) / 2) := by
  have h := DLMF.Gamma.Gamma_laplace_power (μ := 2) (ν := c + 1) (z := 1 / 2) (by norm_num)
    (by norm_num) (by simp; linarith) (by norm_num)
  have hinv : (1 / 2 : ℂ) ^ (-((c + 1) / 2)) = (2 : ℂ) ^ ((c + 1) / 2) := by
    rw [one_div, Complex.inv_cpow _ _ (by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.arg_ofReal_of_nonneg (by norm_num)]
      exact Real.pi_ne_zero.symm), Complex.cpow_neg,
      inv_inv]
  rw [hinv, show c + 1 - 1 = c by ring] at h
  rw [h, pcfMoment]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [Complex.cpow_two, zero_mul, sub_zero]
  ring_nf

/-- **Laplace-type integral for `U(a,z)`** (DLMF 12.5.1): for `re a > -1/2` and all `z`,
`U(a,z) = e^{-z²/4}/Γ(1/2 + a) ∫₀^∞ t^{a-1/2} e^{-t²/2 - z t} dt`. -/
@[dlmf 12.5.E1]
theorem pcfU_eq_integral {a : ℂ} (ha : -1 / 2 < a.re) (z : ℂ) :
    pcfU a z = exp (-z ^ 2 / 4) / Gamma (1 / 2 + a) *
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1 / 2) * exp (-(t : ℂ) ^ 2 / 2 - z * t) := by
  have h0 : -1 < (a - 1 / 2).re := by simp; linarith
  have h1 : -1 < (a - 1 / 2 + 1).re := by simp; linarith
  have h2 : -1 < (a - 1 / 2 + 1 + 1).re := by simp; linarith
  set G := (Gamma (1 / 2 + a))⁻¹ with hG
  have hs : IsWeberSol a (fun w => G * (exp (-w ^ 2 / 4) * pcfMoment (a - 1 / 2) w))
      (fun w => G * (exp (-w ^ 2 / 4) *
        (-pcfMoment (a - 1 / 2 + 1) w - w / 2 * pcfMoment (a - 1 / 2) w))) := fun w => by
    have hM0 := hasDerivAt_pcfMoment h0 w
    have hM1 := hasDerivAt_pcfMoment h1 w
    have he := hasDerivAt_exp_neg_sq_div_four w
    have hibp := pcfMoment_ibp h0 w
    rw [show a - 1 / 2 + 2 = a - 1 / 2 + 1 + 1 by ring] at hibp
    refine ⟨((he.mul hM0).const_mul G).congr_deriv (by ring), ?_⟩
    refine ((he.mul ((hM1.neg).sub (((hasDerivAt_id w).div_const 2).mul hM0))).const_mul G)
      |>.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
    · simp only [id, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply]
      linear_combination G * exp (-w ^ 2 / 4) * hibp
    · exact Eventually.of_forall fun v => by simp [Pi.sub_apply, Pi.neg_apply, Pi.mul_apply]
  have hd := Complex.Gamma_mul_Gamma_add_half (a / 2 + 1 / 4)
  rw [show a / 2 + 1 / 4 + 1 / 2 = 3 / 4 + a / 2 by ring,
    show 2 * (a / 2 + 1 / 4) = 1 / 2 + a by ring,
    show 1 - (1 / 2 + a) = 1 / 2 - a by ring] at hd
  have hGa : Gamma (1 / 2 + a) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hG1 : Gamma (a / 2 + 1 / 4) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hG3 : Gamma (3 / 4 + a / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hpow (x y : ℂ) (hxy : 1 / 2 - a + x = 1 + y) :
      (2 : ℂ) ^ (1 / 2 - a) * 2 ^ x = 2 * 2 ^ y := by
    rw [← Complex.cpow_add _ _ two_ne_zero, hxy, Complex.cpow_add _ _ two_ne_zero,
      Complex.cpow_one]
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hinit0 : G * (exp (-(0 : ℂ) ^ 2 / 4) * pcfMoment (a - 1 / 2) 0) = pcfU a 0 := by
    have hp := hpow (a / 2 + 1 / 4) (-(a / 2 + 1 / 4)) (by ring)
    rw [pcfMoment_zero h0, pcfU_zero', hG, show (a - 1 / 2 + 1) / 2 = a / 2 + 1 / 4 by ring]
    simp only [zero_pow two_ne_zero, neg_zero, zero_div, Complex.exp_zero, one_mul]
    generalize Gamma (1 / 2 + a) = A at hGa hd ⊢
    generalize Gamma (a / 2 + 1 / 4) = B at hG1 hd ⊢
    generalize Gamma (3 / 4 + a / 2) = C at hG3 hd ⊢
    generalize (2 : ℂ) ^ (a / 2 + 1 / 4) = P at hp ⊢
    generalize (2 : ℂ) ^ (-(a / 2 + 1 / 4)) = Q at hp ⊢
    generalize (2 : ℂ) ^ (1 / 2 - a) = T at hd hp
    field_simp
    linear_combination P * hd + A * (Real.sqrt π : ℂ) * hp
  have hinit1 : G * (exp (-(0 : ℂ) ^ 2 / 4) *
      (-pcfMoment (a - 1 / 2 + 1) 0 - 0 / 2 * pcfMoment (a - 1 / 2) 0)) = pcfUDeriv a 0 := by
    have hp := hpow (a / 2 + 3 / 4) (-(a / 2 - 1 / 4)) (by ring)
    rw [pcfMoment_zero h1, pcfUDeriv_zero', hG,
      show (a - 1 / 2 + 1 + 1) / 2 = 3 / 4 + a / 2 by ring,
      show (3 / 4 + a / 2 : ℂ) = a / 2 + 3 / 4 by ring]
    rw [show (1 / 4 + a / 2 : ℂ) = a / 2 + 1 / 4 by ring]
    simp only [zero_pow two_ne_zero, neg_zero, zero_div, Complex.exp_zero, one_mul, zero_mul,
      sub_zero]
    rw [show a / 2 + 3 / 4 = 3 / 4 + a / 2 by ring] at hp ⊢
    generalize Gamma (1 / 2 + a) = A at hGa hd ⊢
    generalize Gamma (a / 2 + 1 / 4) = B at hG1 hd ⊢
    generalize Gamma (3 / 4 + a / 2) = C at hG3 hd ⊢
    generalize (2 : ℂ) ^ (3 / 4 + a / 2) = P at hp ⊢
    generalize (2 : ℂ) ^ (-(a / 2 - 1 / 4)) = Q at hp ⊢
    generalize (2 : ℂ) ^ (1 / 2 - a) = T at hd hp
    field_simp
    linear_combination -P * hd - A * (Real.sqrt π : ℂ) * hp
  have := hs.eq_of_initial (isWeberSol_pcfU a) hinit0 hinit1 z
  rw [← this, pcfMoment, hG]
  ring

end DLMF.Confluent
end
end
