/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Integrals.HankelKernels

/-!
# Bessel transforms with confluent hypergeometric parameters

Large-parameter Bessel kernels and their transforms into Kummer and Tricomi functions.

Source references and common attribution are retained in
`DLMF.Confluent.Integrals`.
-/

@[expose] public section

open Complex Filter MeasureTheory FormalMultilinearSeries

open scoped Real Topology ENNReal

open DLMF.Hypergeometric

open DLMF.Bessel

noncomputable section

namespace DLMF.Confluent

section LargeParamBessel

/-! ### The Hankel transform 13.10.13

Helpers with prefix `confLP_`. The integral, written with `t^{-ν/2} J_ν(2√(xt)) = x^{ν/2}
𝐅(;ν+1;-xt)`, is evaluated in the Euler region `0 < re a < re b < re ν + 1` by the Euler integral
of `𝐌(b-a,b,-t)`, the Laplace transform of `t^{b-1} 𝐅(;ν+1;-xt)`, the Euler integral of
`𝐌(b,ν+1,-x/s)` and two applications of Fubini's theorem. It is continued analytically in `a`,
and then extended to all orders `ν` by the downward recurrence that the `₀F₁` contiguous relation
and the Kummer contiguous relations induce on both sides. -/

open Set
open scoped Nat

/-- Laplace transform of `t^{β-1} 𝐅(;c;-xt)`. -/
theorem confLP_laplace_0F1 {β c x : ℂ} (hβ : 0 < β.re) {s : ℝ} (hs : 0 < s) :
    ∫ t : ℝ in Ioi 0, exp (-(s * t : ℂ)) * ((t : ℂ) ^ (β - 1) *
        regularizedHGFun (∅ : Multiset ℂ) {c} (-x * t)) =
      Gamma β * (s : ℂ) ^ (-β) * regularizedHGFun {β} {c} (-x / s) := by
  set d := regularizedHGFunCoeff (∅ : Multiset ℂ) {c} with hd
  set F : ℕ → ℝ → ℂ := fun k t => (d k * (-x) ^ k) *
    ((t : ℂ) ^ (β + k - 1) * exp (-(s * t : ℂ))) with hF
  have hβk : ∀ k : ℕ, 0 < (β + k).re := fun k => by
    simp; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hGk : ∀ k : ℕ, ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (β + k - 1) * exp (-(s * t : ℂ)) =
      (1 / (s : ℂ)) ^ (β + k) * Gamma (β + k) := fun k => by
    have := integral_cpow_mul_exp_neg_mul_Ioi (a := β + k) (r := s) (hβk k) hs
    simpa using this
  have hIk : ∀ k : ℕ, IntegrableOn (fun t : ℝ => (t : ℂ) ^ (β + k - 1) *
      exp (-(s * t : ℂ))) (Ioi 0) := fun k => by
    have h := cfInt_integrableOn_rpow_exp (r := (β + k).re - 1) (by linarith [hβk k]) hs
    refine h.mono' ?_ ?_
    · exact (ContinuousOn.mul (ContinuousOn.cpow continuous_ofReal.continuousOn
        continuousOn_const fun t ht => ofReal_mem_slitPlane.mpr ht)
        (by fun_prop : Continuous fun t : ℝ => exp (-(s * t : ℂ))).continuousOn)
        |>.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_exp]
      apply le_of_eq; simp
  have hFi : ∀ k, IntegrableOn (F k) (Ioi 0) := fun k => (hIk k).const_mul _
  set β0 := β.re with hβ0
  obtain ⟨Cg, hCg0, hCg⟩ := exists_norm_recip_Gamma_add_nat_le c
  have hβ0k : ∀ k : ℕ, ∀ i : ℕ, (β0 : ℂ) + i ≠ 0 := fun k i h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
  have hnormF : ∀ k : ℕ, ∫ t : ℝ in Ioi 0, ‖F k t‖ ≤
      (‖Gamma (β0 : ℂ)‖ * Cg * Real.exp β0 * s ^ (-β0)) *
        ((2 * Real.exp 1 * (‖x‖ / s)) ^ k / k !) := by
    intro k
    have hint : ∫ t : ℝ in Ioi 0, ‖F k t‖ = ‖d k‖ * ‖x‖ ^ k *
        (Real.Gamma (β0 + k) * s ^ (-(β0 + k))) := by
      have : ∀ t ∈ Ioi (0 : ℝ), ‖F k t‖ = ‖d k‖ * ‖x‖ ^ k *
          (t ^ (β0 + k - 1) * Real.exp (-(s * t))) := by
        intro t ht
        have ht0 : (0 : ℝ) < t := ht
        simp only [hF, norm_mul, norm_pow, norm_neg]
        rw [norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_exp]
        have : (-(↑s * ↑t : ℂ)).re = -(s * t) := by simp
        rw [this]; simp [hβ0]
      rw [setIntegral_congr_fun measurableSet_Ioi this, integral_const_mul,
        cfInt_integral_rpow_exp (by linarith [hβk k, show (β + k).re = β0 + k by simp [hβ0]]) hs]
      ring_nf
    rw [hint, hd, DLMF.Bessel.regularizedHGFunCoeff_empty]
    have hGR : Real.Gamma (β0 + k) = ‖Gamma (β0 : ℂ)‖ * ‖poch (β0 : ℂ) k‖ := by
      rw [← norm_mul, ← Gamma_add_nat_eq_mul_poch (hβ0k k) k,
        show (β0 : ℂ) + k = ((β0 + k : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
        Complex.norm_real, Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by
          linarith [hβk k, show (β + k).re = β0 + k by simp [hβ0]])).le]
    have hp := norm_poch_le_factorial_mul_exp (β0 : ℂ) k
    rw [Complex.norm_real, Real.norm_of_nonneg hβ.le] at hp
    have hc := hCg k
    have hfac : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
    rw [hGR, show -(β0 + k) = -β0 + -(k : ℝ) by ring, Real.rpow_add hs, Real.rpow_neg hs.le (k : ℝ),
      Real.rpow_natCast]
    simp only [norm_div, norm_one, norm_mul, Complex.norm_natCast]
    rw [div_eq_mul_inv, one_mul, mul_inv, ← norm_inv]
    have hsk : (0 : ℝ) < s ^ k := by positivity
    have e1 : Real.exp (β0 + k) = Real.exp β0 * Real.exp 1 ^ k := by
      rw [Real.exp_add, ← Real.exp_nat_mul, mul_one]
    calc (k ! : ℝ)⁻¹ * ‖(Gamma (c + k))⁻¹‖ * ‖x‖ ^ k *
          (‖Gamma (β0 : ℂ)‖ * ‖poch (β0 : ℂ) k‖ * (s ^ (-β0) * (s ^ k)⁻¹))
        ≤ (k ! : ℝ)⁻¹ * (Cg * (2 ^ k / k !)) * ‖x‖ ^ k *
          (‖Gamma (β0 : ℂ)‖ * (k ! * Real.exp (β0 + k)) * (s ^ (-β0) * (s ^ k)⁻¹)) := by
          gcongr
      _ = _ := by
          rw [e1, mul_pow, mul_pow, div_pow]
          field_simp
  have hsum : Summable fun k => ∫ t : ℝ in Ioi 0, ‖F k t‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _) hnormF ?_
    exact (Real.summable_pow_div_factorial _).mul_left _
  have hs' := hasSum_integral_of_summable_integral_norm hFi hsum
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hterm : ∀ k : ℕ, ∫ t : ℝ in Ioi 0, F k t =
      Gamma β * (s : ℂ) ^ (-β) * (regularizedHGFunCoeff {β} {c} k * (-x / s) ^ k) := by
    intro k
    simp only [hF]
    rw [integral_const_mul, hGk k, hd, DLMF.Bessel.regularizedHGFunCoeff_empty,
      regularizedHGFunCoeff_singleton]
    have hp : (1 / (s : ℂ)) ^ (β + k) = (s : ℂ) ^ (-β) * ((s : ℂ) ^ k)⁻¹ := by
      rw [one_div, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hs.le]; exact Real.pi_ne_zero.symm),
        ← cpow_neg, show -(β + k) = -β + -(k : ℂ) by ring, cpow_add _ _ hs0,
        cpow_neg (s : ℂ) (k : ℂ), cpow_natCast]
    have hG : Gamma (β + k) = Gamma β * poch β k := Gamma_add_nat_eq_mul_poch (fun i h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]) k
    rw [hp, hG, div_pow]
    field_simp
  simp_rw [hterm] at hs'
  have hR := ((hasFPowerSeriesOnBall_regularizedConfluent β c).hasSum_mul_pow
    (by simp : (-x / s) ∈ Metric.eball (0 : ℂ) ⊤)).mul_left (Gamma β * (s : ℂ) ^ (-β))
  rw [← hs'.unique hR]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  have h0 := ((DLMF.Bessel.hasFPowerSeriesOnBall_regularized0F1 c).hasSum_mul_pow
    (z := -x * t) (by simp)).mul_left (exp (-(s * t : ℂ)) * (t : ℂ) ^ (β - 1))
  refine Eq.trans ?_ (h0.tsum_eq.symm.trans (tsum_congr fun k => ?_))
  · ring
  · simp only [hF, ← hd]
    rw [show β + k - 1 = (β - 1) + k by ring, cpow_add _ _ htc, cpow_natCast, mul_pow]
    ring

/-- The inner integral `∫₀¹ s^{c-1}(1-s)^{a-1} s^{-(c+a)} e^{-y/s} ds = e^{-y} Γ(a) y^{-a}`. -/
theorem confLP_inner_integral {a c y : ℂ} (hy : 0 < y.re) (ha : 0 < a.re) :
    ∫ s in Ioo (0 : ℝ) 1, (s : ℂ) ^ (c - 1) * (1 - (s : ℂ)) ^ (a - 1) *
        ((s : ℂ) ^ (-(c + a)) * exp (-y / s)) =
      exp (-y) * (Gamma a * y ^ (-a)) := by
  have h := cfInt_euler_subst_U (a := a) (c := c) (ν := c + a - 1) (x := y) hy ha
  rw [show c + a - 1 + 1 = c + a by ring, show c + a - 1 + 2 - c = a + 1 by ring] at h
  have hy0 : y ≠ 0 := fun h0 => by simp [h0] at hy
  rw [h, kummerU_kummer_transform_all a _ hy0, show a - (a + 1) + 1 = 0 by ring, kummerU_zero,
    show (1 : ℂ) - (a + 1) = -a by ring, mul_one]

/-- `‖𝐅(;ν+1;-rt)‖ ≤ K (1+t)^{-(re ν/2 + 1/4)}` on `(0,∞)`. -/
theorem confLP_exists_norm_0F1_le (ν : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ K, ∀ t : ℝ, 0 < t → ‖regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t)‖ ≤
      K * (1 + t) ^ (-(ν.re / 2 + 1 / 4)) := by
  obtain ⟨C, hC⟩ := cfInt_exists_norm_kernel_le ν hr
  have hx0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hn : 0 < ‖(r : ℂ) ^ (ν / 2)‖ := norm_pos_iff.mpr (by
    rw [cpow_def_of_ne_zero hx0]; exact exp_ne_zero _)
  refine ⟨C / ‖(r : ℂ) ^ (ν / 2)‖, fun t ht => ?_⟩
  have h := hC t ht
  rw [cfInt_kernel_eq ν hx0 ht, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht] at h
  have htσ : 0 < t ^ ν.re := Real.rpow_pos_of_pos ht _
  rw [div_mul_eq_mul_div, le_div_iff₀ hn]
  have : ‖(r : ℂ) ^ (ν / 2)‖ * (t ^ ν.re *
      ‖regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t)‖) ≤
      t ^ ν.re * (C * (1 + t) ^ (-(ν.re / 2 + 1 / 4))) := by linarith
  nlinarith [norm_nonneg (regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t))]

/-- Continuity of `t ↦ 𝐅(;ν+1;-rt)`. -/
theorem confLP_continuous_0F1 (ν : ℂ) (r : ℝ) :
    Continuous fun t : ℝ => regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t) := by
  have h := continuous_regularized0F1.comp
    (show Continuous fun t : ℝ => ((ν + 1 : ℂ), -(r : ℂ) * t) by fun_prop)
  exact h

/-- Integrability of the 13.10.13 integrand in the `₀F₁` form. -/
theorem confLP_integrableOn {a b ν : ℂ} {r : ℝ} (hr : 0 < r) (hb : 0 < b.re)
    (hν : 2 * a.re < ν.re + 1 / 2) :
    IntegrableOn (fun t : ℝ => exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t *
      regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t)) (Ioi 0) := by
  obtain ⟨K, hK⟩ := confLP_exists_norm_0F1_le ν hr
  have h := integrableOn_cpow_mul_regularizedHGFun_neg_mul (a := b - a) (b := b) (c := b)
    (h := fun t : ℝ => regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t)) (K := K)
    (r := ν.re / 2 + 1 / 4) (confLP_continuous_0F1 ν r).continuousOn hK hb
    (by simp only [sub_re]; linarith)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  rw [regularizedConfluent_kummer_transform a b (t : ℂ)]
  have he : exp (-(t : ℂ)) * exp (t : ℂ) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  linear_combination (-((t : ℂ) ^ (b - 1) * regularizedHGFun {b - a} {b} (-(t : ℂ)) *
    regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t))) * he

/-- Norm-integral of a function that is real and nonnegative on `S`. -/
theorem confLP_setIntegral_norm_of_ofReal {S : Set ℝ} {f : ℝ → ℂ} {g : ℝ → ℝ}
    (hS : MeasurableSet S) (hfg : ∀ s ∈ S, f s = (g s : ℂ)) (hg : ∀ s ∈ S, 0 ≤ g s) :
    ∫ s in S, ‖f s‖ = ‖∫ s in S, f s‖ := by
  rw [setIntegral_congr_fun hS (fun s hs => by
      rw [hfg s hs, Complex.norm_real, Real.norm_of_nonneg (hg s hs)]),
    setIntegral_congr_fun hS hfg, integral_complex_ofReal, Complex.norm_real,
    Real.norm_of_nonneg (setIntegral_nonneg hS hg)]

/-- A set integral that is nonzero comes from an integrable function. -/
theorem confLP_integrableOn_of_ne_zero {S : Set ℝ} {f : ℝ → ℂ} (h : ∫ s in S, f s ≠ 0) :
    IntegrableOn f S := by
  by_contra hf
  exact h (integral_undef hf)

/-- The Euler kernel with real parameters is real and nonnegative. -/
theorem confLP_eulerKernel_ofReal (γ β : ℝ) (t : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    kumDec_eulerKernel (γ : ℂ) (β : ℂ) t s =
      ((Real.exp (-(t * s)) * s ^ (γ - 1) * (1 - s) ^ (β - γ - 1) : ℝ) : ℂ) := by
  simp only [kumDec_eulerKernel]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_exp,
    ofReal_cpow hs.1.le, ofReal_cpow (by linarith [hs.2] : (0:ℝ) ≤ 1 - s)]
  push_cast
  ring_nf

/-- The double-integral kernel of the second Fubini step. -/
def confLP_Q (c a b μ : ℂ) (r s ρ : ℝ) : ℂ :=
  (s : ℂ) ^ (c - 1) * (1 - (s : ℂ)) ^ (a - 1) * (s : ℂ) ^ (-b) *
    (exp (-(r : ℂ) / s * ρ) * (ρ : ℂ) ^ (b - 1) * (1 - (ρ : ℂ)) ^ (μ - b))

/-- Measurability of the kernel `confLP_Q`. -/
theorem confLP_measurable_Q (c a b μ : ℂ) (r : ℝ) :
    Measurable (Function.uncurry (confLP_Q c a b μ r)) := by
  unfold confLP_Q
  fun_prop

/-- The modulus of the kernel `confLP_Q` on the open unit square. -/
theorem confLP_norm_Q (c a b μ : ℂ) (r : ℝ) {s ρ : ℝ} (hs : s ∈ Ioo (0:ℝ) 1)
    (hρ : ρ ∈ Ioo (0:ℝ) 1) :
    ‖confLP_Q c a b μ r s ρ‖ = s ^ (c.re - 1) * (1 - s) ^ (a.re - 1) * s ^ (-b.re) *
      (Real.exp (-(r / s * ρ)) * ρ ^ (b.re - 1) * (1 - ρ) ^ (μ.re - b.re)) := by
  have h1 : (1 : ℂ) - s = ((1 - s : ℝ) : ℂ) := by push_cast; ring
  have h2 : (1 : ℂ) - ρ = ((1 - ρ : ℝ) : ℂ) := by push_cast; ring
  simp only [confLP_Q, norm_mul, Complex.norm_exp]
  rw [h1, h2, norm_cpow_eq_rpow_re_of_pos hs.1, norm_cpow_eq_rpow_re_of_pos hs.1,
    norm_cpow_eq_rpow_re_of_pos (by linarith [hs.2]), norm_cpow_eq_rpow_re_of_pos hρ.1,
    norm_cpow_eq_rpow_re_of_pos (by linarith [hρ.2])]
  have : (-(r : ℂ) / s * ρ).re = -(r / s * ρ) := by
    rw [show -(r : ℂ) / s * ρ = ((-(r / s * ρ) : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  rw [this]
  simp

/-- With real parameters the kernel `confLP_Q` is real. -/
theorem confLP_Q_ofReal (γ α β μ r : ℝ) {s ρ : ℝ} (hs : s ∈ Ioo (0:ℝ) 1)
    (hρ : ρ ∈ Ioo (0:ℝ) 1) :
    confLP_Q (γ : ℂ) (α : ℂ) (β : ℂ) (μ : ℂ) r s ρ =
      ((s ^ (γ - 1) * (1 - s) ^ (α - 1) * s ^ (-β) *
        (Real.exp (-(r / s * ρ)) * ρ ^ (β - 1) * (1 - ρ) ^ (μ - β)) : ℝ) : ℂ) := by
  simp only [confLP_Q]
  push_cast
  rw [ofReal_cpow hs.1.le, ofReal_cpow (by linarith [hs.2] : (0:ℝ) ≤ 1 - s),
    ofReal_cpow hs.1.le, ofReal_cpow hρ.1.le, ofReal_cpow (by linarith [hρ.2] : (0:ℝ) ≤ 1 - ρ)]
  push_cast
  ring_nf

/-- The inner integral of `confLP_Q` over `s`. -/
theorem confLP_integral_Q {c a b μ : ℂ} {r : ℝ} (hr : 0 < r) (hcab : c + a = b) (ha : 0 < a.re)
    {ρ : ℝ} (hρ : ρ ∈ Ioo (0:ℝ) 1) :
    ∫ s in Ioo (0:ℝ) 1, confLP_Q c a b μ r s ρ =
      (ρ : ℂ) ^ (b - 1) * (1 - (ρ : ℂ)) ^ (μ - b) *
        (exp (-((r : ℂ) * ρ)) * (Gamma a * ((r : ℂ) * ρ) ^ (-a))) := by
  have hy : 0 < ((r : ℂ) * ρ).re := by
    rw [show (r : ℂ) * ρ = ((r * ρ : ℝ) : ℂ) by push_cast; ring, ofReal_re]
    exact mul_pos hr hρ.1
  have h := confLP_inner_integral (a := a) (c := c) (y := (r : ℂ) * ρ) hy ha
  rw [hcab] at h
  rw [← h, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  simp only [confLP_Q]
  rw [show -(r : ℂ) / s * ρ = -((r : ℂ) * ρ) / s by ring]
  ring

/-- The Fubini integrand `confLP_Q` of the base case of 13.10.13 is integrable on the unit
square, for `Re a, Re c > 0`, `c + a = b` and `Re(ν + 1 - b) > 0`. -/
private lemma confLP_integrable_Q {a b c ν : ℂ} {r : ℝ} (hr : 0 < r) (ha : 0 < a.re)
    (hc0 : 0 < c.re) (hνb : 0 < (ν + 1 - b).re) (hcab : c + a = b) :
    Integrable (Function.uncurry (confLP_Q c a b ν r))
      ((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioo (0:ℝ) 1))) := by
  set γ := c.re with hγ
  set α := a.re with hα
  set β := b.re with hβ
  have hβγα : β = γ + α := by simp [hβ, hγ, hα, ← hcab]
  have hQm := confLP_measurable_Q c a b ν r
  set Q := confLP_Q c a b ν r with hQ
  set ν' := ν.re with hν'
  have hcpow : ∀ {z : ℂ} (w : ℂ), z ≠ 0 → z ^ w ≠ 0 := fun w hz => by
    rw [cpow_def_of_ne_zero hz]; exact exp_ne_zero _
  have hnQ : ∀ ρ ∈ Ioo (0:ℝ) 1, ∀ s ∈ Ioo (0:ℝ) 1,
      ‖Q s ρ‖ = ‖confLP_Q (γ:ℂ) (α:ℂ) (β:ℂ) (ν':ℂ) r s ρ‖ := by
    intro ρ hρ s hs
    rw [hQ, confLP_norm_Q _ _ _ _ _ hs hρ, confLP_norm_Q _ _ _ _ _ hs hρ]
    simp only [ofReal_re]
    rfl
  have hRint : ∀ ρ ∈ Ioo (0:ℝ) 1, ∫ s in Ioo (0:ℝ) 1, confLP_Q (γ:ℂ) (α:ℂ) (β:ℂ) (ν':ℂ) r s ρ =
      (ρ : ℂ) ^ ((β:ℂ) - 1) * (1 - (ρ : ℂ)) ^ ((ν':ℂ) - β) *
        (exp (-((r : ℂ) * ρ)) * (Gamma (α:ℂ) * ((r : ℂ) * ρ) ^ (-(α:ℂ)))) := fun ρ hρ =>
    confLP_integral_Q hr (by rw [hβγα]; push_cast; ring) (by simpa using ha) hρ
  have hRnorm : ∀ ρ ∈ Ioo (0:ℝ) 1, ∫ s in Ioo (0:ℝ) 1, ‖Q s ρ‖ =
      ‖∫ s in Ioo (0:ℝ) 1, confLP_Q (γ:ℂ) (α:ℂ) (β:ℂ) (ν':ℂ) r s ρ‖ := by
    intro ρ hρ
    rw [setIntegral_congr_fun measurableSet_Ioo (hnQ ρ hρ)]
    refine confLP_setIntegral_norm_of_ofReal measurableSet_Ioo
      (fun s hs => confLP_Q_ofReal γ α β ν' r hs hρ) (fun s hs => ?_)
    have := hs.1; have := hs.2; have := hρ.1; have := hρ.2
    positivity
  refine (integrable_prod_iff' hQm.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
    have hρc : (ρ:ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ.1.ne'
    have h1ρ : (1 - (ρ:ℂ)) ≠ 0 := by
      rw [sub_ne_zero]; intro h; have := congrArg re h; simp at this; linarith [hρ.2]
    have hrρ : (r:ℂ) * ρ ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hr.ne') hρc
    have hne : ∫ s in Ioo (0:ℝ) 1, confLP_Q (γ:ℂ) (α:ℂ) (β:ℂ) (ν':ℂ) r s ρ ≠ 0 := by
      rw [hRint ρ hρ]
      exact mul_ne_zero (mul_ne_zero (hcpow _ hρc) (hcpow _ h1ρ)) (mul_ne_zero (exp_ne_zero _)
        (mul_ne_zero (Gamma_ne_zero_of_re_pos (by simpa using ha)) (hcpow _ hrρ)))
    have hint := confLP_integrableOn_of_ne_zero hne
    refine hint.norm.mono' ((hQm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (hnQ ρ hρ s hs).le
  · have hB := Complex.betaIntegral_convergent (u := ((γ : ℝ) : ℂ))
      (v := ((ν' - β + 1 : ℝ) : ℂ)) (by simpa using hc0) (by
        simp only [ofReal_re]
        have : (ν + 1 - b).re = ν' - β + 1 := by simp [hν', hβ]; ring
        linarith)
    have hB' := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hB.norm
    refine (hB'.const_mul (‖Gamma (α:ℂ)‖ * r ^ (-α))).mono'
      hQm.aestronglyMeasurable.norm.prod_swap.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp only [Function.uncurry_apply_pair]
    rw [hRnorm ρ hρ, hRint ρ hρ]
    have h1 : (1 : ℂ) - ρ = ((1 - ρ : ℝ) : ℂ) := by push_cast; ring
    have hrρ : (r : ℂ) * ρ = ((r * ρ : ℝ) : ℂ) := by push_cast; ring
    have h1ρ : (0:ℝ) < 1 - ρ := by linarith [hρ.2]
    rw [h1, hrρ]
    simp only [norm_mul, norm_cpow_eq_rpow_re_of_pos hρ.1, norm_cpow_eq_rpow_re_of_pos h1ρ,
      norm_cpow_eq_rpow_re_of_pos (mul_pos hr hρ.1), Complex.norm_exp]
    simp only [sub_re, ofReal_re, one_re, neg_re]
    rw [show ν' - β + 1 - 1 = ν' - β by ring, Real.mul_rpow hr.le hρ.1.le]
    have he : Real.exp (-(r * ρ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hρ.1])
    have hpow : ρ ^ (β - 1) * ρ ^ (-α) = ρ ^ (γ - 1) := by
      rw [← Real.rpow_add hρ.1, hβγα]; ring_nf
    have hρn : (0:ℝ) ≤ ρ ^ (γ - 1) * (1 - ρ) ^ (ν' - β) := by
      have := hρ.1; positivity
    calc ρ ^ (β - 1) * (1 - ρ) ^ (ν' - β) * (Real.exp (-(r * ρ)) *
          (‖Gamma (α:ℂ)‖ * (r ^ (-α) * ρ ^ (-α))))
        = (‖Gamma (α:ℂ)‖ * r ^ (-α)) * (ρ ^ (γ - 1) * (1 - ρ) ^ (ν' - β)) *
            Real.exp (-(r * ρ)) := by rw [← hpow]; ring
      _ ≤ (‖Gamma (α:ℂ)‖ * r ^ (-α)) * (ρ ^ (γ - 1) * (1 - ρ) ^ (ν' - β)) * 1 := by
          gcongr
      _ = _ := mul_one _

/-- The Fubini integrand `t^{b-1} ₀F̃₁(;ν+1;-rt) e^{-ts} s^{c-1} (1-s)^{a-1}` of the base case
of 13.10.13 is integrable on `(0, ∞) × (0, 1)`, for `Re a, Re c > 0`, `c + a = b` and
`2 Re a < Re ν + 1/2`. -/
private lemma confLP_integrable_G {a b c ν : ℂ} {r : ℝ} (hr : 0 < r) (ha : 0 < a.re)
    (hc0 : 0 < c.re) (hcab : c + a = b) (hν : 2 * a.re < ν.re + 1 / 2) :
    Integrable (Function.uncurry fun (t s : ℝ) =>
        (t : ℂ) ^ (b - 1) * regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t) *
          kumDec_eulerKernel c b t s)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioo (0:ℝ) 1))) := by
  have hbc : b - c = a := by rw [← hcab]; ring
  have hb0 : 0 < b.re := by rw [← hcab, add_re]; linarith
  set p := ν.re / 2 + 1 / 4 with hp
  have hap : a.re < p := by rw [hp]; linarith
  set F : ℝ → ℂ := fun t => regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t) with hF
  have hFc : Continuous F := confLP_continuous_0F1 ν r
  obtain ⟨KF, hKF⟩ := confLP_exists_norm_0F1_le ν hr
  set P : ℝ → ℂ := fun t => (t : ℂ) ^ (b - 1) * F t with hP
  set E : ℝ → ℝ → ℂ := fun t s => kumDec_eulerKernel c b t s with hE
  set G : ℝ → ℝ → ℂ := fun t s => P t * E t s with hG
  show Integrable (Function.uncurry G) _
  have hEm : Measurable (Function.uncurry E) := by
    simp only [hE, kumDec_eulerKernel]
    fun_prop
  have hPm : Measurable P := by
    simp only [hP]
    exact (by fun_prop : Measurable fun t : ℝ => (t : ℂ) ^ (b - 1)).mul hFc.measurable
  have hm1 : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioo (0:ℝ) 1))) :=
    ((hPm.comp measurable_fst).mul hEm).aestronglyMeasurable
  set γ := c.re with hγ
  set α := a.re with hα
  set β := b.re with hβ
  have hβγα : β = γ + α := by simp [hβ, hγ, hα, ← hcab]
  refine (integrable_prod_iff hm1).mpr ⟨Eventually.of_forall fun t => ?_, ?_⟩
  · have h := kumDec_intervalIntegrable_eulerKernel (a := c) (b := b) hc0
      (by rw [hbc]; exact ha) t
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp h).const_mul (P t)
  · have hI := integrableOn_cpow_mul_regularizedHGFun_neg_mul (a := (γ : ℂ)) (b := (β : ℂ))
      (c := (β : ℂ)) (h := F) (K := KF) (r := p) hFc.continuousOn hKF (by simpa using hb0)
      (by simp only [ofReal_re]; linarith)
    refine IntegrableOn.congr_fun (hI.norm.const_mul ‖Gamma (γ : ℂ) * Gamma (α : ℂ)‖) (fun t ht => ?_)
      measurableSet_Ioi
    have ht0 : (0:ℝ) < t := ht
    simp only [Function.uncurry_apply_pair]
    have hn : ∀ s ∈ Ioo (0:ℝ) 1, ‖G t s‖ = ‖P t‖ * ‖kumDec_eulerKernel (γ : ℂ) (β : ℂ) t s‖ := by
      intro s hs
      simp only [hG, hE, norm_mul]
      rw [kumDec_norm_eulerKernel c b hs, kumDec_norm_eulerKernel (γ : ℂ) (β : ℂ) hs, hbc]
      simp only [sub_re, ofReal_re]
      rw [show β - γ = α by rw [hβγα]; ring]
    rw [setIntegral_congr_fun measurableSet_Ioo hn, integral_const_mul,
      confLP_setIntegral_norm_of_ofReal measurableSet_Ioo
        (fun s hs => confLP_eulerKernel_ofReal γ β t hs) (fun s hs => by
          have := hs.1; have := hs.2
          exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _))
            (Real.rpow_nonneg (by linarith) _))]
    have hR := kumDec_regularizedHGFun_neg_eq (a := (γ : ℂ)) (b := (β : ℂ)) (by simpa using hc0)
      (by simp only [sub_re, ofReal_re]; linarith) t
    rw [show (β : ℂ) - γ = (α : ℂ) by rw [hβγα]; push_cast; ring] at hR
    have hGγ : Gamma (γ : ℂ) * Gamma (α : ℂ) ≠ 0 :=
      mul_ne_zero (Gamma_ne_zero_of_re_pos (by simpa using hc0))
        (Gamma_ne_zero_of_re_pos (by simpa using ha))
    have hint : ∫ s in Ioo (0:ℝ) 1, kumDec_eulerKernel (γ : ℂ) (β : ℂ) t s =
        Gamma (γ : ℂ) * Gamma (α : ℂ) * regularizedHGFun {(γ : ℂ)} {(β : ℂ)} (-(t : ℂ)) := by
      rw [hR, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
        ← mul_assoc, mul_one_div_cancel hGγ, one_mul]
    rw [hint, norm_mul, norm_mul, norm_mul, norm_mul]
    simp only [norm_mul]
    rw [norm_cpow_eq_rpow_re_of_pos ht0, norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [sub_re, ofReal_re, one_re]
    ring

/-- Base case of 13.10.13 (in `₀F₁` form) in the Euler region. -/
theorem confLP_base {a b ν : ℂ} {r : ℝ} (hr : 0 < r) (ha : 0 < a.re) (hba : 0 < (b - a).re)
    (hνb : 0 < (ν + 1 - b).re) (hν : 2 * a.re < ν.re + 1 / 2) :
    ∫ t : ℝ in Ioi 0, exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t *
        regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t) =
      (r : ℂ) ^ (-a) * exp (-(r : ℂ)) * regularizedHGFun {ν - b + 1} {ν - a + 1} r := by
  set c := b - a with hc
  have hbc : b - c = a := by rw [hc]; ring
  have hc0 : 0 < c.re := hba
  have hb0 : 0 < b.re := by
    have : b.re = c.re + a.re := by simp [hc]
    linarith
  set F : ℝ → ℂ := fun t => regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t) with hF
  set P : ℝ → ℂ := fun t => (t : ℂ) ^ (b - 1) * F t with hP
  set E : ℝ → ℝ → ℂ := fun t s => kumDec_eulerKernel c b t s with hE
  set G : ℝ → ℝ → ℂ := fun t s => P t * E t s with hG
  have hstep1 : ∀ t : ℝ, exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t *
      F t = P t * regularizedHGFun {c} {b} (-(t : ℂ)) := by
    intro t
    rw [regularizedConfluent_kummer_transform a b (t : ℂ)]
    have he : exp (-(t : ℂ)) * exp (t : ℂ) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    simp only [hP]
    linear_combination ((t : ℂ) ^ (b - 1) * regularizedHGFun {c} {b} (-(t : ℂ)) * F t) * he
  have hGa := Gamma_ne_zero_of_re_pos ha
  have hGc := Gamma_ne_zero_of_re_pos hc0
  have hGb := Gamma_ne_zero_of_re_pos hb0
  have hGνb := Gamma_ne_zero_of_re_pos hνb
  have hts : ∀ t : ℝ, ∫ s in Ioo 0 1, G t s =
      P t * (Gamma c * Gamma a * regularizedHGFun {c} {b} (-(t : ℂ))) := by
    intro t
    have h := kumDec_regularizedHGFun_neg_eq (a := c) (b := b) hc0 (by rw [hbc]; exact ha) t
    rw [hbc] at h
    simp only [hG]
    rw [integral_const_mul, h, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
    field_simp
    rfl
  have hGi : Integrable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioo (0:ℝ) 1))) :=
    confLP_integrable_G hr ha hc0 (sub_add_cancel b a) hν
  have hst : ∀ s ∈ Ioo (0:ℝ) 1, ∫ t in Ioi 0, G t s =
      (s : ℂ) ^ (c - 1) * (1 - (s : ℂ)) ^ (a - 1) *
        (Gamma b * (s : ℂ) ^ (-b) * regularizedHGFun {b} {ν + 1} (-(r : ℂ) / s)) := by
    intro s hs
    have h := confLP_laplace_0F1 (β := b) (c := ν + 1) (x := (r : ℂ)) hb0 hs.1
    rw [← h, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hG, hE, kumDec_eulerKernel]
    rw [hbc, show -(t : ℂ) * s = -(s * t : ℂ) by ring]
    ring
  set Q := confLP_Q c a b ν r with hQ
  have hsQ : ∀ s : ℝ, (s : ℂ) ^ (c - 1) * (1 - (s : ℂ)) ^ (a - 1) *
      (Gamma b * (s : ℂ) ^ (-b) * regularizedHGFun {b} {ν + 1} (-(r : ℂ) / s)) =
      (Gamma (ν + 1 - b))⁻¹ * ∫ ρ in Ioo (0:ℝ) 1, Q s ρ := by
    intro s
    rw [regularized_euler_integral hb0 hνb, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, ← integral_const_mul, ← integral_const_mul,
      ← integral_const_mul, ← integral_const_mul]
    congr 1
    funext ρ
    simp only [hQ, confLP_Q]
    rw [show ν + 1 - b - 1 = ν - b by ring]
    field_simp
  have hQi : Integrable (Function.uncurry Q)
      ((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioo (0:ℝ) 1))) :=
    confLP_integrable_Q hr ha hc0 hνb (sub_add_cancel b a)
  have hcab : c + a = b := by rw [hc]; ring
  have hνac : 0 < (ν + 1 - a - c).re := by
    rw [show ν + 1 - a - c = ν + 1 - b by rw [hc]; ring]; exact hνb
  have hV : ∫ ρ in Ioo (0:ℝ) 1, (ρ : ℂ) ^ (b - 1) * (1 - (ρ : ℂ)) ^ (ν - b) *
        (exp (-((r : ℂ) * ρ)) * (Gamma a * ((r : ℂ) * ρ) ^ (-a))) =
      Gamma a * (r : ℂ) ^ (-a) * (Gamma c * Gamma (ν + 1 - b) *
        regularizedHGFun {c} {ν + 1 - a} (-(r : ℂ))) := by
    have hE2 := regularized_euler_integral (a := c) (b := ν + 1 - a) (z := -(r : ℂ)) hc0 hνac
    rw [show ν + 1 - a - c = ν + 1 - b by rw [hc]; ring, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo] at hE2
    rw [hE2, ← mul_assoc (Gamma c * Gamma (ν + 1 - b)), mul_one_div_cancel (mul_ne_zero hGc hGνb),
      one_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun ρ hρ => ?_
    have hρc : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ.1.ne'
    rw [mul_cpow_ofReal_nonneg hr.le hρ.1.le,
      show ν + 1 - b - 1 = ν - b by ring]
    have hp : (ρ : ℂ) ^ (b - 1) * (ρ : ℂ) ^ (-a) = (ρ : ℂ) ^ (c - 1) := by
      rw [← cpow_add _ _ hρc]; congr 1; rw [hc]; ring
    rw [show -(r : ℂ) * ρ = -((r : ℂ) * ρ) by ring]
    linear_combination (Gamma a * (r : ℂ) ^ (-a) * exp (-((r : ℂ) * ρ)) *
      (1 - (ρ : ℂ)) ^ (ν - b)) * hp
  calc ∫ t : ℝ in Ioi 0, exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t * F t
      = ∫ t : ℝ in Ioi 0, (Gamma c * Gamma a)⁻¹ * ∫ s in Ioo 0 1, G t s := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        rw [hstep1 t, hts t]
        field_simp
    _ = (Gamma c * Gamma a)⁻¹ * ∫ s in Ioo 0 1, ∫ t in Ioi 0, G t s := by
        rw [integral_const_mul, integral_integral_swap hGi]
    _ = (Gamma c * Gamma a)⁻¹ * ∫ s in Ioo (0:ℝ) 1,
          (Gamma (ν + 1 - b))⁻¹ * ∫ ρ in Ioo (0:ℝ) 1, Q s ρ := by
        rw [setIntegral_congr_fun measurableSet_Ioo fun s hs => (hst s hs).trans (hsQ s)]
    _ = (Gamma c * Gamma a)⁻¹ * ((Gamma (ν + 1 - b))⁻¹ *
          ∫ ρ in Ioo (0:ℝ) 1, ∫ s in Ioo (0:ℝ) 1, Q s ρ) := by
        rw [integral_const_mul, integral_integral_swap hQi]
    _ = (Gamma c * Gamma a)⁻¹ * ((Gamma (ν + 1 - b))⁻¹ *
          (Gamma a * (r : ℂ) ^ (-a) * (Gamma c * Gamma (ν + 1 - b) *
            regularizedHGFun {c} {ν + 1 - a} (-(r : ℂ))))) := by
        rw [← hV]
        congr 2
        exact setIntegral_congr_fun measurableSet_Ioo fun ρ hρ => confLP_integral_Q hr hcab ha hρ
    _ = _ := by
        rw [regularizedConfluent_kummer_transform c (ν + 1 - a) (-(r : ℂ)), neg_neg,
          show ν + 1 - a - c = ν - b + 1 by rw [hc]; ring, show ν + 1 - a = ν - a + 1 by ring]
        field_simp

/-- 13.10.13 (in `₀F₁` form) for `0 < re b < re ν + 1`, `re ν > -1/2`, by analytic continuation
in `a` from the Euler region. -/
theorem confLP_of_strip {a b ν : ℂ} {r : ℝ} (hr : 0 < r) (hb : 0 < b.re)
    (hbν : 0 < (ν + 1 - b).re) (hν0 : -1 / 2 < ν.re) (hν : 2 * a.re < ν.re + 1 / 2) :
    ∫ t : ℝ in Ioi 0, exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t *
        regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t) =
      (r : ℂ) ^ (-a) * exp (-(r : ℂ)) * regularizedHGFun {ν - b + 1} {ν - a + 1} r := by
  set p := ν.re / 2 + 1 / 4 with hp
  set F : ℝ → ℂ := fun t => regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t) with hF
  have hFc : Continuous F := confLP_continuous_0F1 ν r
  obtain ⟨KF, hKF⟩ := confLP_exists_norm_0F1_le ν hr
  have hKF0 : 0 ≤ KF := by
    have h := (norm_nonneg _).trans (hKF 1 one_pos)
    exact (mul_nonneg_iff_of_pos_right (by positivity)).mp h
  set Φ : ℂ → ℝ → ℂ := fun w t => (t : ℂ) ^ (b - 1) * regularizedHGFun {b - w} {b} (-(t : ℂ)) * F t
    with hΦ
  have hΨ : ∀ w : ℂ, ∫ t : ℝ in Ioi 0, exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) *
      regularizedHGFun {w} {b} t * F t = ∫ t : ℝ in Ioi 0, Φ w t := by
    intro w
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [regularizedConfluent_kummer_transform w b (t : ℂ)]
    have he : exp (-(t : ℂ)) * exp (t : ℂ) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    simp only [hΦ]
    linear_combination ((t : ℂ) ^ (b - 1) * regularizedHGFun {b - w} {b} (-(t : ℂ)) * F t) * he
  set U : Set ℂ := {w : ℂ | w.re < p} with hU
  have hUo : IsOpen U := isOpen_lt continuous_re continuous_const
  have hpre : IsPreconnected U := (convex_halfSpace_re_lt p).isPreconnected
  have hFd : DifferentiableOn ℂ (fun w => ∫ t : ℝ in Ioi 0, Φ w t) U := by
    refine Complex.differentiableOn_integral_Ioi_of_locally_dominated hUo 0 ?_ ?_ ?_
    · intro w _
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      exact ((ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
        fun t ht => ofReal_mem_slitPlane.mpr ht).mul
        (kumDec_continuous_neg (b - w) b).continuousOn).mul hFc.continuousOn
    · refine Eventually.of_forall fun t => ?_
      exact (((differentiable_regularizedConfluent_comp (A := fun w => b - w) (B := fun _ => b)
        (differentiable_const b |>.sub differentiable_id) (differentiable_const b)
        (-(t : ℂ))).const_mul ((t : ℂ) ^ (b - 1))).mul_const (F t)).differentiableOn
    · intro w₀ hw₀
      have hw₀' : w₀.re < p := hw₀
      set ε := (p - w₀.re) / 2 with hε
      have hε0 : 0 < ε := by rw [hε]; linarith
      obtain ⟨C, hC⟩ := exists_eventually_norm_regularizedHGFun_neg_le (b - w₀) b hε0
      have htend : Tendsto (fun w : ℂ => (b - w, b)) (𝓝 w₀) (𝓝 (b - w₀, b)) :=
        ((continuous_const.sub continuous_id).prodMk continuous_const).tendsto w₀
      refine ⟨_, htend.eventually hC, fun t => t ^ (b.re - 1) * (C * (1 + t) ^ (-(b - w₀).re + ε)) *
        (KF * (1 + t) ^ (-p)), ?_, ?_⟩
      · have hI := DLMF.Gamma.integrableOn_rpow_mul_one_add_rpow (σ := b.re)
          (α := p + (b - w₀).re - ε) hb (by simp only [sub_re]; rw [hε]; linarith)
        refine IntegrableOn.congr_fun (Integrable.const_mul hI (C * KF)) (fun t ht => ?_)
          measurableSet_Ioi
        have ht0 : (0:ℝ) < t := ht
        have e : (1 + t) ^ (-(b - w₀).re + ε) * (1 + t) ^ (-p) =
            (1 + t) ^ (-(p + (b - w₀).re - ε)) := by
          rw [← Real.rpow_add (by linarith)]; ring_nf
        rw [← e]
        ring
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        intro y hy
        have ht0 : (0:ℝ) < t := ht
        simp only [hΦ, norm_mul]
        rw [norm_cpow_eq_rpow_re_of_pos ht0]
        simp only [sub_re, one_re]
        refine mul_le_mul (mul_le_mul_of_nonneg_left (hy t ht0.le) (by positivity))
          (hKF t ht0) (norm_nonneg _) (by
            have := hy t ht0.le
            have h0 : 0 ≤ C * (1 + t) ^ (-(b - w₀).re + ε) := (norm_nonneg _).trans this
            exact mul_nonneg (by positivity) h0)
  set H : ℂ → ℂ := fun w => (r : ℂ) ^ (-w) * exp (-(r : ℂ)) *
    regularizedHGFun {ν - b + 1} {ν - w + 1} r with hH
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hHd : Differentiable ℂ H := by
    refine ((differentiable_neg.const_cpow (Or.inl hr0)).mul_const _).mul ?_
    exact differentiable_regularizedConfluent_comp (A := fun _ => ν - b + 1)
      (B := fun w => ν - w + 1) (differentiable_const _)
      ((differentiable_const ν |>.sub differentiable_id).add_const 1) (r : ℂ)
  set m := min b.re p / 2 with hm
  have hp0 : 0 < p := by rw [hp]; linarith
  have hm0 : 0 < m := by rw [hm]; exact half_pos (lt_min hb hp0)
  have hmb : m < b.re := by rw [hm]; linarith [min_le_left b.re p]
  have hmp : m < p := by rw [hm]; linarith [min_le_right b.re p]
  have hmU : (m : ℂ) ∈ U := by show (m : ℂ).re < p; simpa using hmp
  have heq : Set.EqOn (fun w => ∫ t : ℝ in Ioi 0, Φ w t) H U := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hFd.analyticOnNhd hUo)
      (fun z _ => hHd.analyticAt z) hpre hmU ?_
    have hopen : IsOpen {w : ℂ | 0 < w.re ∧ w.re < b.re ∧ w.re < p} :=
      (isOpen_lt continuous_const continuous_re).and
        ((isOpen_lt continuous_re continuous_const).and (isOpen_lt continuous_re continuous_const))
    filter_upwards [hopen.mem_nhds (show (m : ℂ) ∈ _ by
      simp only [Set.mem_ofPred_eq, ofReal_re]; exact ⟨hm0, hmb, hmp⟩)] with w hw
    rw [← hΨ w]
    exact confLP_base hr hw.1 (by simp only [sub_re]; linarith [hw.2.1]) hbν
      (by rw [hp] at hw; linarith [hw.2.2])
  have hfin := heq (show a ∈ U by show a.re < p; rw [hp]; linarith)
  rw [hΨ a]
  exact hfin

/-- The contiguous relation `𝐌(a,b,z) = (b-a) 𝐌(a,b+1,z) + a 𝐌(a+1,b+1,z)`, for all
parameters. -/
theorem confLP_contiguous_b (a b z : ℂ) :
    regularizedHGFun {a} {b} z =
      (b - a) * regularizedHGFun {a} {b + 1} z + a * regularizedHGFun {a + 1} {b + 1} z := by
  rw [regularizedConfluent_eq_tsum, regularizedConfluent_eq_tsum, regularizedConfluent_eq_tsum,
    ← tsum_mul_left, ← tsum_mul_left,
    ← ((summable_regularizedConfluent_term a (b + 1) z).mul_left (b - a)).tsum_add
      ((summable_regularizedConfluent_term (a + 1) (b + 1) z).mul_left a)]
  refine tsum_congr fun n => ?_
  have hp : a * poch (a + 1) n = poch a n * (a + n) := by
    rw [← poch_succ_left, poch_succ]
  rw [one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (b + n), show b + n + 1 = b + 1 + n by ring]
  linear_combination (-(z ^ n / n.factorial * (Gamma (b + 1 + n))⁻¹)) * hp

/-- The contiguous relation `𝐌(A-1,B-1,x) = (B-1) 𝐌(A,B,x) - (B-A) x 𝐌(A,B+1,x)`, for all
parameters. -/
theorem confLP_contiguous_down (A B x : ℂ) :
    regularizedHGFun {A - 1} {B - 1} x =
      (B - 1) * regularizedHGFun {A} {B} x - (B - A) * x * regularizedHGFun {A} {B + 1} x := by
  set T : ℂ → ℂ → ℕ → ℂ := fun a b n => poch a n * x ^ n / n.factorial * (Gamma (b + n))⁻¹
    with hT
  have hS : ∀ a b, HasSum (T a b) (regularizedHGFun {a} {b} x) := fun a b => by
    rw [regularizedConfluent_eq_tsum]
    exact (summable_regularizedConfluent_term a b x).hasSum
  set u : ℕ → ℂ := fun n => T (A - 1) (B - 1) n - (B - 1) * T A B n with hu
  have hU : HasSum u (regularizedHGFun {A - 1} {B - 1} x - (B - 1) * regularizedHGFun {A} {B} x) :=
    (hS _ _).sub ((hS A B).mul_left _)
  have hu0 : u 0 = 0 := by
    simp only [hu, hT, poch_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
      CharP.cast_eq_zero, add_zero]
    rw [one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (B - 1), sub_add_cancel]
    ring
  have husucc : ∀ n : ℕ, u (n + 1) = -(B - A) * x * T A (B + 1) n := by
    intro n
    simp only [hu, hT]
    have hp1 : poch (A - 1) (n + 1) = (A - 1) * poch A n := by
      rw [poch_succ_left, sub_add_cancel]
    rw [hp1, poch_succ, Nat.factorial_succ, pow_succ]
    push_cast
    rw [show B - 1 + ((n : ℂ) + 1) = B + n by ring,
      one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (B + n),
      show B + (n : ℂ) + 1 = B + 1 + n by ring, show B + ((n : ℂ) + 1) = B + 1 + n by ring]
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
    field_simp
    ring
  have hU' : HasSum (fun n => u (n + 1)) (-(B - A) * x * regularizedHGFun {A} {B + 1} x) := by
    simp_rw [husucc]
    exact (hS A (B + 1)).mul_left _
  have h2 := (hasSum_nat_add_iff' 1).mpr hU
  simp only [Finset.range_one, Finset.sum_singleton, hu0, sub_zero] at h2
  have := h2.unique hU'
  linear_combination this

/-- The integral of 13.10.13 in `₀F₁` form. -/
def confLP_Psi (a b ν : ℂ) (r : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi 0, exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t *
    regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-(r : ℂ) * t)

/-- The right side of 13.10.13 in `₀F₁` form. -/
def confLP_R (a b ν : ℂ) (r : ℝ) : ℂ :=
  (r : ℂ) ^ (-a) * exp (-(r : ℂ)) * regularizedHGFun {ν - b + 1} {ν - a + 1} r

/-- The order recurrence of the 13.10.13 integrals, from the `₀F₁` and Kummer contiguous
relations. -/
theorem confLP_Psi_rec {a b ν : ℂ} {r : ℝ} (hr : 0 < r) (hb : 0 < b.re)
    (hν : 2 * a.re < ν.re + 1 / 2) :
    confLP_Psi a b ν r = (ν + 1) * confLP_Psi a b (ν + 1) r -
      r * (b - a) * confLP_Psi a (b + 1) (ν + 2) r - r * a * confLP_Psi (a + 1) (b + 1) (ν + 2) r := by
  have h1 := confLP_integrableOn (a := a) (b := b) (ν := ν + 1) hr hb (by simp; linarith)
  have h2 := confLP_integrableOn (a := a) (b := b + 1) (ν := ν + 2) hr (by simp; linarith)
    (by simp; linarith)
  have h3 := confLP_integrableOn (a := a + 1) (b := b + 1) (ν := ν + 2) hr (by simp; linarith)
    (by simp; linarith)
  simp only [confLP_Psi]
  set f1 := fun t : ℝ => exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t *
    regularizedHGFun (∅ : Multiset ℂ) {ν + 1 + 1} (-(r : ℂ) * t) with hf1
  set f2 := fun t : ℝ => exp (-(t : ℂ)) * (t : ℂ) ^ (b + 1 - 1) * regularizedHGFun {a} {b + 1} t *
    regularizedHGFun (∅ : Multiset ℂ) {ν + 2 + 1} (-(r : ℂ) * t) with hf2
  set f3 := fun t : ℝ => exp (-(t : ℂ)) * (t : ℂ) ^ (b + 1 - 1) *
    regularizedHGFun {a + 1} {b + 1} t *
    regularizedHGFun (∅ : Multiset ℂ) {ν + 2 + 1} (-(r : ℂ) * t) with hf3
  have e : ∫ t in Ioi (0:ℝ), ((ν + 1) * f1 t - r * (b - a) * f2 t - r * a * f3 t) =
      (ν + 1) * (∫ t in Ioi (0:ℝ), f1 t) - r * (b - a) * (∫ t in Ioi (0:ℝ), f2 t) -
        r * a * (∫ t in Ioi (0:ℝ), f3 t) := by
    rw [integral_sub (f := fun t => (ν + 1) * f1 t - r * (b - a) * f2 t)
        (g := fun t => r * a * f3 t) ((h1.const_mul _).sub (h2.const_mul _)) (h3.const_mul _),
      integral_sub (f := fun t => (ν + 1) * f1 t) (g := fun t => r * (b - a) * f2 t)
        (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul]
  rw [← e]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0:ℝ) < t := ht
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
  simp only [hf1, hf2, hf3]
  have hF := regularized0F1_contiguous (ν + 1) (-(r : ℂ) * t)
  have hM := confLP_contiguous_b a b (t : ℂ)
  have hp : (t : ℂ) ^ (b + 1 - 1) = (t : ℂ) * (t : ℂ) ^ (b - 1) := by
    rw [show b + 1 - 1 = (b - 1) + 1 by ring, cpow_add _ _ htc, cpow_one]; ring
  rw [hp]
  rw [show ν + 1 + 1 + 1 = ν + 2 + 1 by ring] at hF
  rw [hF, hM]
  ring

/-- The right sides satisfy the same recurrence. -/
theorem confLP_R_rec (a b ν : ℂ) {r : ℝ} (hr : 0 < r) :
    confLP_R a b ν r = (ν + 1) * confLP_R a b (ν + 1) r -
      r * (b - a) * confLP_R a (b + 1) (ν + 2) r - r * a * confLP_R (a + 1) (b + 1) (ν + 2) r := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  simp only [confLP_R]
  have h := confLP_contiguous_down (ν + 1 - b + 1) (ν + 1 - a + 1) (r : ℂ)
  rw [show ν + 1 - b + 1 - 1 = ν - b + 1 by ring, show ν + 1 - a + 1 - 1 = ν - a + 1 by ring,
    show ν + 1 - a + 1 + 1 = ν + 2 - a + 1 by ring] at h
  rw [show ν + 2 - (b + 1) + 1 = ν + 1 - b + 1 by ring, show ν + 2 - (a + 1) + 1 = ν + 1 - a + 1 by ring,
    h]
  have hpow : (r : ℂ) ^ (-(a + 1)) * r = (r : ℂ) ^ (-a) := by
    rw [show -(a + 1) = -a + -1 by ring, cpow_add _ _ hr0, cpow_neg_one, mul_assoc,
      inv_mul_cancel₀ hr0, mul_one]
  linear_combination (a * exp (-(r : ℂ)) * regularizedHGFun {ν + 1 - b + 1} {ν + 1 - a + 1} r) * hpow

/-- 13.10.13 in `₀F₁` form for all admissible parameters. -/
theorem confLP_Psi_eq_R : ∀ n : ℕ, ∀ a b ν : ℂ, ∀ {r : ℝ}, 0 < r → 0 < b.re →
    -1 / 2 < ν.re + n → b.re < ν.re + 1 + n → 2 * a.re < ν.re + 1 / 2 →
    confLP_Psi a b ν r = confLP_R a b ν r := by
  intro n
  induction n with
  | zero =>
    intro a b ν r hr hb h1 h2 hν
    simp only [CharP.cast_eq_zero, add_zero] at h1 h2
    exact confLP_of_strip hr hb (by simp; linarith) h1 hν
  | succ n ih =>
    intro a b ν r hr hb h1 h2 hν
    push_cast at h1 h2
    rw [confLP_Psi_rec hr hb hν, confLP_R_rec a b ν hr,
      ih a b (ν + 1) hr hb (by simp; linarith) (by simp; linarith) (by simp; linarith),
      ih a (b + 1) (ν + 2) hr (by simp; linarith) (by simp; linarith) (by simp; linarith)
        (by simp; linarith),
      ih (a + 1) (b + 1) (ν + 2) hr (by simp; linarith) (by simp; linarith) (by simp; linarith)
        (by simp; linarith)]

end LargeParamBessel

/-- A Hankel-type transform of `𝐌`, for real `x > 0`. For non-real `x` the Bessel kernel grows like
`exp (c √t)`; the parameter bound makes the integrand absolutely integrable, as required for
Lean's integral. -/
@[dlmf 13.10.E13]
theorem bessel_regularizedHGFun {a b ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hb : 0 < b.re) (hν : 2 * a.re < ν.re + 1 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1 - ν / 2) * regularizedHGFun {a} {b} t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      x ^ (-a + ν / 2) * exp (-x) * regularizedHGFun {ν - b + 1} {ν - a + 1} x := by
  set r := x.re with hr
  have hxr : x = (r : ℂ) := Complex.ext (by simp [hr]) (by simp [hxi])
  have hx0 : x ≠ 0 := by rw [hxr]; exact ofReal_ne_zero.mpr hx.ne'
  obtain ⟨n, hn⟩ := exists_nat_gt (max (-1 / 2 - ν.re) (b.re - ν.re - 1))
  have hm1 := le_max_left (-1 / 2 - ν.re) (b.re - ν.re - 1)
  have hm2 := le_max_right (-1 / 2 - ν.re) (b.re - ν.re - 1)
  have hP := confLP_Psi_eq_R n a b ν hx hb (by linarith) (by linarith) hν
  simp only [confLP_Psi, confLP_R] at hP
  rw [← hxr] at hP
  have hpt : ∀ t ∈ Set.Ioi (0:ℝ), exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1 - ν / 2) *
      regularizedHGFun {a} {b} t * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      x ^ (ν / 2) * (exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t *
        regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-x * t)) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    have hk := cfInt_kernel_eq ν hx0 ht0
    have hne : (t : ℂ) ^ (ν / 2) ≠ 0 := by
      rw [cpow_def_of_ne_zero htc]; exact exp_ne_zero _
    have e1 : (t : ℂ) ^ (b - 1 - ν / 2) * (t : ℂ) ^ (ν / 2) = (t : ℂ) ^ (b - 1) := by
      rw [← cpow_add _ _ htc]; ring_nf
    have e2 : (t : ℂ) ^ ν = (t : ℂ) ^ (ν / 2) * (t : ℂ) ^ (ν / 2) := by
      rw [← cpow_add _ _ htc]; ring_nf
    apply mul_left_cancel₀ hne
    rw [e2] at hk
    linear_combination (exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1 - ν / 2) *
      regularizedHGFun {a} {b} t) * hk +
      (x ^ (ν / 2) * exp (-(t : ℂ)) * regularizedHGFun {a} {b} t *
        regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (-x * t) * (t : ℂ) ^ (ν / 2)) * e1
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, hP,
    cpow_add _ _ hx0]
  ring

open Set in
/-- A Hankel-type transform of `𝐌` in terms of U, for real `x > 0`. For non-real `x` the Bessel
kernel grows like `exp (c √t)`; the parameter bound makes the integrand absolutely integrable,
as required for Lean's integral. -/
@[dlmf 13.10.E14]
theorem bessel_regularizedHGFun_U {a b ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hν0 : -1 < ν.re) (hν1 : ν.re < 2 * (b - a).re - 3 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ)) * (t : ℂ) ^ (ν / 2) * regularizedHGFun {a} {b} t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      x ^ (ν / 2) * exp (-x) / Gamma (b - a) * kummerU a (a - b + ν + 2) x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  set r := x.re with hr
  have hxr : x = (r : ℂ) := Complex.ext (by simp [hr]) (by simp [hxi])
  set c := b - a with hc
  set σ := ν.re with hσ
  set p := σ / 2 + 1 / 4 with hp
  set K : ℝ → ℂ := fun t => (t : ℂ) ^ (ν / 2) * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) with hK
  have hpt : ∀ t : ℝ, exp (-(t : ℂ)) * (t : ℂ) ^ (ν / 2) * regularizedHGFun {a} {b} t *
      besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) = K t * regularizedHGFun {c} {b} (-(t : ℂ)) := by
    intro t
    rw [regularizedConfluent_kummer_transform a b (t : ℂ)]
    have he : exp (-(t : ℂ)) * exp (t : ℂ) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    simp only [hK]
    linear_combination ((t : ℂ) ^ (ν / 2) * regularizedHGFun {c} {b} (-(t : ℂ)) *
      besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ))) * he
  rw [setIntegral_congr_fun measurableSet_Ioi fun t _ => hpt t]
  set F : ℂ → ℂ := fun w => ∫ t : ℝ in Ioi 0, K t * regularizedHGFun {c} {w + c} (-(t : ℂ))
    with hF
  set H : ℂ → ℂ := fun w => x ^ (ν / 2) * exp (-x) / Gamma c * kummerU w (ν + 2 - c) x with hH
  have hFH : ∀ w : ℂ, 0 < w.re → F w = H w := by
    intro w hw
    have h := cfInt_bessel_M_euler (a := w) (b := w + c) hx hxi hw hν0
      (by rw [show w + c - w = c by ring]; exact hν1)
    rw [show w + c - w = c by ring, show w - (w + c) + ν + 2 = ν + 2 - c by ring] at h
    exact h
  have hKc : ContinuousOn K (Ioi 0) := cfInt_continuousOn_kernel ν hx0
  obtain ⟨CK, hCK⟩ := cfInt_exists_norm_kernel_le ν hx
  have hKb : ∀ t : ℝ, 0 < t → ‖K t‖ ≤ CK * (t ^ σ * (1 + t) ^ (-p)) := by
    intro t ht
    have := hCK t ht
    simp only [hK]; rw [hxr]; exact this
  have hCK0 : 0 ≤ CK := by
    have h := (norm_nonneg _).trans (hKb 1 one_pos)
    exact (mul_nonneg_iff_of_pos_right (by positivity)).mp h
  have hcre : σ / 2 + 3 / 4 < c.re := by linarith
  set ε := (c.re - σ / 2 - 3 / 4) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hFd : Differentiable ℂ F := by
    refine differentiableOn_univ.mp (Complex.differentiableOn_integral_Ioi_of_locally_dominated
      (Φ := fun w t => K t * regularizedHGFun {c} {w + c} (-(t : ℂ))) isOpen_univ 0 ?_ ?_ ?_)
    · intro w _
      exact (hKc.aestronglyMeasurable measurableSet_Ioi).mul
        (kumDec_continuous_neg c (w + c)).aestronglyMeasurable
    · refine Eventually.of_forall fun t => ?_
      exact ((differentiable_regularizedConfluent_comp (A := fun _ => c) (B := fun w => w + c)
        (differentiable_const c) (differentiable_id.add_const c) (-(t : ℂ))).const_mul
        (K t)).differentiableOn
    · intro w₀ _
      obtain ⟨C, hC⟩ := exists_eventually_norm_regularizedHGFun_neg_le c (w₀ + c) hε0
      have htend : Tendsto (fun w : ℂ => (c, w + c)) (𝓝 w₀) (𝓝 (c, w₀ + c)) :=
        ((continuous_const.prodMk (continuous_id.add continuous_const)).tendsto w₀)
      refine ⟨_, htend.eventually hC, fun t => CK * (t ^ σ * (1 + t) ^ (-p)) *
        (C * (1 + t) ^ (-c.re + ε)), ?_, ?_⟩
      · have hI := DLMF.Gamma.integrableOn_rpow_mul_one_add_rpow (σ := σ + 1)
          (α := p + c.re - ε) (by linarith) (by rw [hp, hε]; linarith)
        refine IntegrableOn.congr_fun (Integrable.const_mul hI (CK * C)) (fun t ht => ?_)
          measurableSet_Ioi
        have ht0 : (0:ℝ) < t := ht
        have e : (1 + t) ^ (-p) * (1 + t) ^ (-c.re + ε) = (1 + t) ^ (-(p + c.re - ε)) := by
          rw [← Real.rpow_add (by linarith)]; ring_nf
        rw [show σ + 1 - 1 = σ by ring, ← e]
        ring
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        intro y hy
        have ht0 : (0:ℝ) < t := ht
        rw [norm_mul]
        exact mul_le_mul (hKb t ht0) (hy t ht0.le) (norm_nonneg _) (by positivity)
  have hHd : Differentiable ℂ H :=
    (cfInt_differentiable_kummerU_fst (ν + 2 - c) hx0).const_mul _
  have heq : F = H := by
    refine AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hFd.analyticAt z)
      (fun z _ => hHd.analyticAt z) (z₀ := 1) ?_
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (0:ℝ) < (1:ℂ).re)] with w hw
    exact hFH w hw
  have h := congrFun heq a
  simp only [hF, hH, show a + c = b by rw [hc]; ring] at h
  rw [h, show ν + 2 - c = a - b + ν + 2 by rw [hc]; ring]

open Set in
/-- A Hankel-type transform of Tricomi U, for real `x > 0`. For non-real `x` the Bessel kernel grows
like `exp (c √t)`; the parameter bound makes the integrand absolutely integrable, as required
for Lean's integral. -/
@[dlmf 13.10.E15]
theorem bessel_kummerU {a b ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hν0 : (b - 2).re < ν.re) (hν1 : -1 < ν.re) (hν2 : ν.re < 2 * a.re - 3 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (ν / 2) * kummerU a b t * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      Gamma (ν - b + 2) / Gamma a * x ^ (ν / 2) * kummerU (ν - b + 2) (ν - a + 2) x := by
  set r := x.re with hr
  have hxr : x = (r : ℂ) := Complex.ext (by simp [hr]) (by simp [hxi])
  have hx0 : x ≠ 0 := by rw [hxr]; exact ofReal_ne_zero.mpr hx.ne'
  set σ := ν.re with hσ
  set α := a.re with hα
  set β := b.re with hβ
  have hb2 : β - 2 < σ := by simpa [hβ] using hν0
  have ha : 0 < α := by linarith
  have hGa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  set K : ℝ → ℂ := fun t => (t : ℂ) ^ (ν / 2) * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) with hK
  set f : ℝ → ℂ := fun s => (s : ℂ) ^ (a - 1) * (1 + (s : ℂ)) ^ (b - a - 1) with hf
  set G : ℝ → ℝ → ℂ := fun t s => K t * (exp (-(s * t : ℂ)) * f s) with hG
  have hKc : ContinuousOn K (Ioi 0) := cfInt_continuousOn_kernel ν hx0
  have hfc : ContinuousOn f (Ioi 0) := by
    refine ContinuousOn.mul ?_ ?_
    · exact ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
        fun t ht => ofReal_mem_slitPlane.mpr ht
    · refine ContinuousOn.cpow (by fun_prop) continuousOn_const fun t ht => ?_
      rw [show (1 : ℂ) + t = ((1 + t : ℝ) : ℂ) by push_cast; ring]
      exact ofReal_mem_slitPlane.mpr (by linarith [show (0 : ℝ) < t from ht])
  obtain ⟨CK, hCK⟩ := cfInt_exists_norm_kernel_le ν hx
  set p := σ / 2 + 1 / 4 with hp
  obtain ⟨CL, hCL⟩ := cfInt_laplace_rpow_le (r := σ) (p := p) hν1 (by rw [hp]; linarith)
  have hnf : ∀ s : ℝ, 0 < s → ‖f s‖ = s ^ (α - 1) * (1 + s) ^ (β - α - 1) := by
    intro s hs
    rw [hf, norm_mul, norm_cpow_eq_rpow_re_of_pos hs,
      show (1 : ℂ) + s = ((1 + s : ℝ) : ℂ) by push_cast; ring,
      norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp [hα, hβ]
  have hKb : ∀ t : ℝ, 0 < t → ‖K t‖ ≤ CK * (t ^ σ * (1 + t) ^ (-p)) := by
    intro t ht
    have := hCK t ht
    simp only [hK]; rw [hxr]; exact this
  have hCK0 : 0 ≤ CK := by
    have h := (norm_nonneg _).trans (hKb 1 one_pos)
    exact (mul_nonneg_iff_of_pos_right (by positivity)).mp h
  have hm : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) :=
    ((hKc.aestronglyMeasurable measurableSet_Ioi).comp_fst
      (ν := volume.restrict (Ioi (0:ℝ)))).mul
      ((Continuous.aestronglyMeasurable (by fun_prop :
        Continuous fun q : ℝ × ℝ => exp (-((q.2 : ℂ) * q.1)))).mul
        ((hfc.aestronglyMeasurable measurableSet_Ioi).comp_snd))
  have hinner : ∀ s : ℝ, 0 < s → IntegrableOn (fun t => G t s) (Ioi 0) ∧
      ∫ t in Ioi 0, ‖G t s‖ ≤ ‖f s‖ * CK * (CL * (s ^ (p - σ - 1) * (1 + s) ^ (-p))) := by
    intro s hs
    obtain ⟨hI, hle⟩ := hCL s hs
    have hbd : ∀ t ∈ Ioi (0:ℝ), ‖G t s‖ ≤
        ‖f s‖ * CK * (t ^ σ * (1 + t) ^ (-p) * Real.exp (-(s * t))) := by
      intro t ht
      have ht0 : (0:ℝ) < t := ht
      show ‖K t * (exp (-(s * t : ℂ)) * f s)‖ ≤ _
      rw [norm_mul (K t), norm_mul (exp _), Complex.norm_exp]
      have : (-(↑s * ↑t : ℂ)).re = -(s * t) := by simp
      rw [this]
      calc ‖K t‖ * (Real.exp (-(s * t)) * ‖f s‖)
          ≤ (CK * (t ^ σ * (1 + t) ^ (-p))) * (Real.exp (-(s * t)) * ‖f s‖) := by
            gcongr; exact hKb t ht0
        _ = _ := by ring
    have hInt : IntegrableOn (fun t => G t s) (Ioi 0) := by
      refine (hI.const_mul (‖f s‖ * CK)).mono' ?_ ?_
      · exact (hKc.aestronglyMeasurable measurableSet_Ioi).mul
          ((Continuous.aestronglyMeasurable (by fun_prop)).mul aestronglyMeasurable_const)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hbd t ht
    refine ⟨hInt, ?_⟩
    calc ∫ t in Ioi 0, ‖G t s‖
        ≤ ∫ t in Ioi 0, ‖f s‖ * CK * (t ^ σ * (1 + t) ^ (-p) * Real.exp (-(s * t))) :=
          setIntegral_mono_on hInt.norm (hI.const_mul _) measurableSet_Ioi hbd
      _ = ‖f s‖ * CK * ∫ t in Ioi 0, t ^ σ * (1 + t) ^ (-p) * Real.exp (-(s * t)) :=
          integral_const_mul _ _
      _ ≤ _ := by gcongr
  have hmaj : IntegrableOn (fun s : ℝ => s ^ ((α + p - σ - 1) - 1) * (1 + s) ^ (-(α + 1 + p - β)))
      (Ioi 0) :=
    DLMF.Gamma.integrableOn_rpow_mul_one_add_rpow (by rw [hp]; linarith) (by linarith)
  have hGi : Integrable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine (integrable_prod_iff' hm).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact (hinner s hs).1
    · refine (hmaj.const_mul (CK * CL)).mono' hm.norm.prod_swap.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : (0:ℝ) < s := hs
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      refine (hinner s hs0).2.trans (le_of_eq ?_)
      rw [hnf s hs0]
      have e1 : s ^ ((α + p - σ - 1) - 1) = s ^ (α - 1) * s ^ (p - σ - 1) := by
        rw [← Real.rpow_add hs0]; ring_nf
      have e2 : (1 + s) ^ (-(α + 1 + p - β)) = (1 + s) ^ (β - α - 1) * (1 + s) ^ (-p) := by
        rw [← Real.rpow_add (by linarith)]; ring_nf
      rw [e1, e2]; ring
  have hts : ∀ t ∈ Ioi (0:ℝ), ∫ s in Ioi 0, G t s = K t * (Gamma a * kummerU a b t) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have hU := kummerU_laplace (a := a) (b := b) (z := t) ha (by simpa using ht0)
    simp only [hG]
    rw [integral_const_mul, hU]
    field_simp
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp only [hf]
    rw [show -((s : ℂ) * t) = -(t : ℂ) * s by ring]; ring_nf
  have hst : ∀ s ∈ Ioi (0:ℝ), ∫ t in Ioi 0, G t s =
      (s : ℂ) ^ (a - 1) * (1 + (s : ℂ)) ^ (b - a - 1) *
        (x ^ (ν / 2) * ((s : ℂ) ^ (-(ν + 1)) * exp (-x / s))) := by
    intro s hs
    have hs0 : (0:ℝ) < s := hs
    have h := cfInt_laplace_kernel hν1 hx0 hs0
    simp only [hG]
    rw [← h, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hf, hK]; ring
  calc ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (ν / 2) * kummerU a b t * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ))
      = ∫ t : ℝ in Ioi 0, (Gamma a)⁻¹ * ∫ s in Ioi 0, G t s := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        rw [hts t ht]; simp only [hK]; field_simp
    _ = (Gamma a)⁻¹ * ∫ s in Ioi 0, ∫ t in Ioi 0, G t s := by
        rw [integral_const_mul, integral_integral_swap hGi]
    _ = (Gamma a)⁻¹ * (x ^ (ν / 2) * ∫ s : ℝ in Ioi 0, (s : ℂ) ^ (a - 1) *
          (1 + (s : ℂ)) ^ (b - a - 1) * ((s : ℂ) ^ (-(ν + 1)) * exp (-x / s))) := by
        rw [setIntegral_congr_fun measurableSet_Ioi hst, ← integral_const_mul,
          ← integral_const_mul, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
        ring
    _ = _ := by
        rw [cfInt_recip_subst_U hx (by simp; linarith)]
        field_simp

end DLMF.Confluent
end
end
