/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Integrals.BesselTransforms

/-!
# Laplace transforms of Whittaker functions

Closed Laplace-transform formulas for Whittaker functions and related Bessel-Kummer kernels.

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

/-- `𝐅(a,b;c;0) = 1/Γ(c)`. -/
theorem regularizedGaussHG_zero_arg (a b c : ℂ) : regularizedGaussHG a b c 0 = (Gamma c)⁻¹ := by
  rw [regularizedGaussHG_eq_regularizedGaussHGFun a b c (by simp), regularizedGaussHGFun_eq_tsum,
    tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  simp

open Set in
open scoped Nat in
/-- Termwise integration of the Bessel series against the Tricomi Laplace transform; the
factor `t^n e^{-t/2} ≤ 2^n n!` gives a summable majorant. -/
@[dlmf 13.10.E16]
theorem bessel_kummerU_M {a b ν x : ℂ} (hx : 0 < x.re)
    (hν0 : (b - 2).re < ν.re) (hν1 : -1 < ν.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ)) * (t : ℂ) ^ (ν / 2) * kummerU a b t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      Gamma (ν - b + 2) * x ^ (ν / 2) * exp (-x) *
        regularizedHGFun {a} {a - b + ν + 2} x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  set d := regularizedHGFunCoeff (∅ : Multiset ℂ) {ν + 1} with hd
  set F : ℕ → ℝ → ℂ := fun n t => (x ^ (ν / 2) * (d n * (-x) ^ n)) *
    tricomiLaplaceKernel a (ν + n + 1) b 1 t with hF
  have hν0' : b.re - 2 < ν.re := by
    have h := hν0; simp only [sub_re] at h; norm_num at h; linarith
  have hνn : ∀ n : ℕ, 0 < (ν + n + 1).re := fun n => by
    simp; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hνb : ∀ n : ℕ, (b - 1).re < (ν + n + 1).re := fun n => by
    simp; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hL : ∀ n : ℕ, _ := fun n =>
    laplace_kummerU_gauss (a := a) (b := ν + n + 1) (c := b) (z := 1) (hνn n) (hνb n) (by simp)
  have hFi : ∀ n : ℕ, IntegrableOn (F n) (Ioi 0) := fun n => (hL n).1.const_mul _
  -- the fixed half-weight majorant
  have hK0 := (laplace_kummerU_gauss (a := a) (b := ν + 1) (c := b) (z := (1 / 2 : ℂ))
    (by simp; linarith) (by simp; linarith) (by norm_num)).1
  set K0 := tricomiLaplaceKernel a (ν + 1) b (1 / 2) with hK0def
  have hker : ∀ n : ℕ, ∀ t : ℝ, 0 < t → tricomiLaplaceKernel a (ν + n + 1) b 1 t =
      ((t ^ n * Real.exp (-(t / 2)) : ℝ) : ℂ) * K0 t := by
    intro n t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    simp only [hK0def, tricomiLaplaceKernel]
    rw [show ν + n + 1 - 1 = (ν + 1 - 1) + n by ring, cpow_add _ _ ht0, cpow_natCast]
    have he : exp (-1 * (t : ℂ)) = exp (-(1 / 2) * (t : ℂ)) * exp (-(t / 2 : ℝ) : ℂ) := by
      rw [← exp_add]; push_cast; ring_nf
    rw [he]; push_cast; ring
  have htn : ∀ n : ℕ, ∀ t : ℝ, 0 < t → t ^ n * Real.exp (-(t / 2)) ≤ 2 ^ n * n ! := by
    intro n t ht
    have h := Real.pow_div_factorial_le_exp (x := t / 2) (by positivity) n
    rw [div_pow, div_div, div_le_iff₀ (by positivity)] at h
    have he : Real.exp (t / 2) * Real.exp (-(t / 2)) = 1 := by rw [← Real.exp_add]; simp
    calc t ^ n * Real.exp (-(t / 2)) ≤ Real.exp (t / 2) * (2 ^ n * n !) * Real.exp (-(t / 2)) := by
          gcongr
      _ = _ := by rw [mul_comm, ← mul_assoc, mul_comm (Real.exp _), he, one_mul]
  set C0 := ∫ t : ℝ in Ioi 0, ‖K0 t‖ with hC0
  have hbound : ∀ n : ℕ, (∫ t : ℝ in Ioi 0, ‖F n t‖) ≤
      ‖x ^ (ν / 2)‖ * C0 * (‖regularizedHGFunCoeff {(1 : ℂ)} {ν + 1} n‖ * (2 * ‖x‖) ^ n) := by
    intro n
    have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖F n t‖ ≤
        (‖x ^ (ν / 2)‖ * ‖d n‖ * ‖x‖ ^ n * (2 ^ n * n !)) * ‖K0 t‖ := by
      intro t ht
      have ht0 : (0 : ℝ) < t := ht
      simp only [hF]
      rw [hker n t ht0, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_neg,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have := htn n t ht0
      have h0 := norm_nonneg (K0 t)
      calc _ = (‖x ^ (ν / 2)‖ * ‖d n‖ * ‖x‖ ^ n) * (t ^ n * Real.exp (-(t / 2))) * ‖K0 t‖ := by ring
        _ ≤ (‖x ^ (ν / 2)‖ * ‖d n‖ * ‖x‖ ^ n) * (2 ^ n * n !) * ‖K0 t‖ := by gcongr
        _ = _ := by ring
    calc (∫ t : ℝ in Ioi 0, ‖F n t‖) ≤ ∫ t : ℝ in Ioi 0,
          (‖x ^ (ν / 2)‖ * ‖d n‖ * ‖x‖ ^ n * (2 ^ n * n !)) * ‖K0 t‖ :=
        setIntegral_mono_on (hFi n).norm (hK0.norm.const_mul _) measurableSet_Ioi hpt
      _ = _ := by
        rw [MeasureTheory.integral_const_mul, ← hC0, regularizedHGFunCoeff_singleton, hd,
          DLMF.Bessel.regularizedHGFunCoeff_empty]
        have hp : poch (1 : ℂ) n = n ! := by
          simp [poch, ascPochhammer_eval_one]
        have hfac : (n ! : ℝ) ≠ 0 := by positivity
        rw [hp]
        simp only [norm_div, norm_mul, one_div, norm_inv, Complex.norm_natCast, mul_pow]
        field_simp
  have hsum : Summable (fun n => ∫ t : ℝ in Ioi 0, ‖F n t‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) hbound ?_
    have h := ((hasFPowerSeriesOnBall_regularizedConfluent 1 (ν + 1)).hasSum_mul_pow
      (z := ((2 * ‖x‖ : ℝ) : ℂ)) (by simp)).summable.norm.mul_left (‖x ^ (ν / 2)‖ * C0)
    refine h.congr fun n => ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hs := hasSum_integral_of_summable_integral_norm hFi hsum
  have hc : 0 < (ν - b + 2).re := by simp; linarith
  have hterm : ∀ n : ℕ, (∫ t : ℝ in Ioi 0, F n t) = x ^ (ν / 2) * Gamma (ν - b + 2) *
      (regularizedHGFunCoeff {ν - b + 2} {a - b + ν + 2} n * (-x) ^ n) := by
    intro n
    simp only [hF]
    rw [MeasureTheory.integral_const_mul, (hL n).2, sub_self, regularizedGaussHG_zero_arg, hd,
      DLMF.Bessel.regularizedHGFunCoeff_empty, regularizedHGFunCoeff_singleton]
    have hp := (Gamma_add_nat_div_Gamma_eq (n := n) (ν - b + 2) (not_neg_nat_of_re_pos hc))
    have hG1 : Gamma (ν + 1 + n) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
    have hG2 : Gamma (ν - b + 2) ≠ 0 := Gamma_ne_zero_of_re_pos hc
    rw [show poch (ν - b + 2) n = Gamma (ν - b + 2 + n) / Gamma (ν - b + 2) from hp.symm,
      show ν + n + 1 = ν + 1 + n by ring, show ν + 1 + n - b + 1 = ν - b + 2 + n by ring,
      show a + (ν + 1 + n) - b + 1 = a - b + ν + 2 + n by ring]
    field_simp
  simp_rw [hterm] at hs
  have hM := ((hasFPowerSeriesOnBall_regularizedConfluent (ν - b + 2) (a - b + ν + 2)).hasSum_mul_pow
    (z := -x) (by simp)).mul_left (x ^ (ν / 2) * Gamma (ν - b + 2))
  have hpt : ∀ t ∈ Ioi (0 : ℝ), exp (-(t : ℂ)) * (t : ℂ) ^ (ν / 2) * kummerU a b t *
      besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) = ∑' n, F n t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    have h0 := ((DLMF.Bessel.hasFPowerSeriesOnBall_regularized0F1 (ν + 1)).hasSum_mul_pow
      (z := -x * t) (by simp)).mul_left (x ^ (ν / 2) * (exp (-(t : ℂ)) * (t : ℂ) ^ ν * kummerU a b t))
    rw [besselJ_two_sqrt hx0 ht0]
    have hνt : (t : ℂ) ^ (ν / 2) * (t : ℂ) ^ (ν / 2) = (t : ℂ) ^ ν := by
      rw [← cpow_add _ _ htc]; ring_nf
    refine Eq.trans ?_ (h0.tsum_eq.symm.trans (tsum_congr fun n => ?_))
    · linear_combination (exp (-(t : ℂ)) * kummerU a b t * x ^ (ν / 2) *
        regularizedHGFun ∅ {ν + 1} (-x * t)) * hνt
    · simp only [hF, hd, tricomiLaplaceKernel]
      rw [show ν + n + 1 - 1 = ν + n by ring, cpow_add _ _ htc, cpow_natCast, mul_pow]
      ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, hs.unique hM,
    regularizedConfluent_kummer_transform (ν - b + 2) (a - b + ν + 2) (-x), neg_neg,
    show a - b + ν + 2 - (ν - b + 2) = a by ring]
  ring

/-- Identity under the stated parameter and domain assumptions: `∫ t : ℝ in Set.Ioi 0, exp (-z *
t) * (t : ℂ) ^ (ν - 1) * whittakerM κ μ t = Gamma (μ + ν + 1 / 2) / (z + 1 / 2) ^ (μ + ν + 1 /
2) * ₂F₁ (1 / 2 + μ - κ) (1 / 2 + μ + ν) (1 + 2 * μ) (1 / (z + 1 / 2))`. -/
@[dlmf 13.23.E1]
theorem laplace_whittakerM {κ μ ν z : ℂ}
    (h : 0 < μ.re + ν.re + 1 / 2) (hz : 1 / 2 < z.re) :
    ∫ t : ℝ in Set.Ioi 0, exp (-z * t) * (t : ℂ) ^ (ν - 1) * whittakerM κ μ t =
      Gamma (μ + ν + 1 / 2) / (z + 1 / 2) ^ (μ + ν + 1 / 2) *
        ₂F₁ (1 / 2 + μ - κ) (1 / 2 + μ + ν) (1 + 2 * μ) (1 / (z + 1 / 2)) := by
  set A := 1 / 2 + μ - κ
  set B := 1 / 2 + μ + ν
  set C := 1 + 2 * μ
  set Z := z + 1 / 2
  rw [show μ + ν + 1 / 2 = B by simp only [B]; ring]
  have hB : 0 < B.re := by simp [B]; linarith
  have hZ : 0 < Z.re := by simp [Z]; linarith
  have hZ1 : ‖(1 : ℂ)‖ < Z.re := by simp [Z]; linarith
  have hZ0 : Z ≠ 0 := by intro h; simp [h] at hZ
  have hw : ‖1 / Z‖ < 1 := by
    rw [norm_div, norm_one, div_lt_one (norm_pos_iff.mpr hZ0)]
    exact (by simpa using hZ1 : (1 : ℝ) < Z.re).trans_le (re_le_norm Z)
  have hcongr : ∀ t ∈ Set.Ioi (0 : ℝ),
      exp (-z * t) * (t : ℂ) ^ (ν - 1) * whittakerM κ μ t =
        exp (-Z * t) * (t : ℂ) ^ (B - 1) * kummerM A C t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have hp : (t : ℂ) ^ (ν - 1) * (t : ℂ) ^ (μ + 1 / 2) = (t : ℂ) ^ (B - 1) := by
      rw [← cpow_add _ _ ht0]; congr 1; simp only [B]; ring
    have he : exp (-z * t) * exp (-(t : ℂ) / 2) = exp (-Z * t) := by
      rw [← Complex.exp_add]; congr 1; simp only [Z]; ring
    rw [whittakerM, show μ - κ + 1 / 2 = A by simp only [A]; ring, ← hp, ← he]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, div_eq_mul_inv, ← cpow_neg]
  by_cases hC : ∀ k : ℕ, C ≠ -(k : ℂ)
  · have hl := laplace_regularizedHGFun_of_norm_lt (a := A) (c := C) (k := 1) hB hZ hZ1
    simp only [one_mul] at hl
    have hG := Gamma_ne_zero hC
    rw [DLMF.Hypergeometric.regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw,
      DLMF.Hypergeometric.regularizedGaussHGFun_eq_div_Gamma hC] at hl
    simp_rw [kummerM_eq_mul_regularizedHGFun hC]
    have hm : (∫ t : ℝ in Set.Ioi 0,
        exp (-Z * t) * (t : ℂ) ^ (B - 1) * (Gamma C * regularizedHGFun {A} {C} t)) =
        Gamma C * ∫ t : ℝ in Set.Ioi 0,
          exp (-Z * t) * (t : ℂ) ^ (B - 1) * regularizedHGFun {A} {C} t := by
      rw [← integral_const_mul]; congr 1; funext t; ring
    rw [hm, hl]
    field_simp
  · push_neg at hC
    obtain ⟨m, hm⟩ := hC
    have hK : ∀ t : ℂ, kummerM A C t =
        ∑ n ∈ Finset.range (m + 1), poch A n / (poch C n * (n.factorial : ℂ)) * t ^ n := by
      intro t
      unfold kummerM
      refine tsum_eq_sum fun n hn => ?_
      have hmn : m < n := by rw [Finset.mem_range] at hn; omega
      simp [hm, poch_neg_nat_eq_zero hmn]
    have hF : ₂F₁ A B C (1 / Z) =
        ∑ n ∈ Finset.range (m + 1), gaussHGCoeff A B C n * (1 / Z) ^ n := by
      rw [ordinaryHypergeometric_eq_tsum]
      simp only [smul_eq_mul]
      have hterm : (fun k : ℕ =>
          ((k.factorial : ℂ)⁻¹) * (ascPochhammer ℂ k).eval A *
            (ascPochhammer ℂ k).eval B * ((ascPochhammer ℂ k).eval C)⁻¹ * (1 / Z) ^ k) =
          fun k => gaussHGCoeff A B C k * (1 / Z) ^ k := by
        funext k
        simp [gaussHGCoeff, poch, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      rw [hterm]
      refine tsum_eq_sum fun k hk => ?_
      have hmk : m < k := by rw [Finset.mem_range] at hk; omega
      simp [gaussHGCoeff, hm, poch_neg_nat_eq_zero hmk]
    have hBn (n : ℕ) : 0 < (B + n).re := by simp; positivity
    have hFi (n : ℕ) : IntegrableOn
        (fun t : ℝ => poch A n / (poch C n * (n.factorial : ℂ)) *
          ((t : ℂ) ^ (B + n - 1) * exp (-(Z * t)))) (Set.Ioi 0) := by
      refine Integrable.const_mul ?_ _
      have hreal := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1)
        (s := B.re + n - 1) (b := Z.re)
        (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) one_pos hZ
      simp only [Real.rpow_one] at hreal
      apply Integrable.mono' hreal (Measurable.aestronglyMeasurable (by fun_prop))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
      simp
    have hpt : ∀ t ∈ Set.Ioi (0 : ℝ),
        exp (-Z * t) * (t : ℂ) ^ (B - 1) * kummerM A C t =
          ∑ n ∈ Finset.range (m + 1), poch A n / (poch C n * (n.factorial : ℂ)) *
            ((t : ℂ) ^ (B + n - 1) * exp (-(Z * t))) := by
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
      rw [hK, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [show B + n - 1 = (B - 1) + n by ring, cpow_add _ _ ht0, cpow_natCast,
        neg_mul]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_finsetSum _ fun n _ => hFi n,
      hF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul, DLMF.Gamma.integral_cpow_mul_exp_neg_mul_Ioi (hBn n) hZ]
    have hp := not_neg_nat_of_re_pos hB
    have hGb := (div_eq_iff (Gamma_ne_zero hp)).mp (Gamma_add_nat_div_Gamma_eq (n := n) B hp)
    rw [hGb, show -(B + (n : ℂ)) = -B + -(n : ℂ) by ring, cpow_add _ _ hZ0, cpow_neg Z (n : ℂ),
      cpow_natCast, gaussHGCoeff, one_div, inv_pow]
    simp only [poch]
    ring

/-- Identity under the stated parameter and domain assumptions: `∫ t : ℝ in Set.Ioi 0, exp (-z *
t) * (t : ℂ) ^ (μ - 1 / 2) * whittakerM κ μ t = Gamma (2 * μ + 1) * (z + 1 / 2) ^ (-κ - μ - 1
/ 2) * (z - 1 / 2) ^ (κ - μ - 1 / 2)`. -/
@[dlmf 13.23.E2]
theorem laplace_whittakerM_closed {κ μ z : ℂ}
    (hμ : -1 / 2 < μ.re) (hz : 1 / 2 < z.re) :
    ∫ t : ℝ in Set.Ioi 0, exp (-z * t) * (t : ℂ) ^ (μ - 1 / 2) * whittakerM κ μ t =
      Gamma (2 * μ + 1) * (z + 1 / 2) ^ (-κ - μ - 1 / 2) *
        (z - 1 / 2) ^ (κ - μ - 1 / 2) := by
  have hb : 0 < (2 * μ + 1).re := by simp; linarith
  have hp : ∀ k : ℕ, 1 + 2 * μ ≠ -(k : ℂ) :=
    not_neg_nat_of_re_pos (by simpa [add_comm] using hb)
  have hB : 0 < (z + 1 / 2).re := by simp; linarith
  have hA : 0 < (z - 1 / 2).re := by simp; linarith
  have hB0 : z + 1 / 2 ≠ 0 := by intro h; rw [h] at hB; simpa using hB
  have hA0 : z - 1 / 2 ≠ 0 := by intro h; rw [h] at hA; simpa using hA
  have hr : 1 - (z + 1 / 2)⁻¹ = (z - 1 / 2) / (z + 1 / 2) := by
    apply (eq_div_iff hB0).mpr
    rw [sub_mul, one_mul, inv_mul_cancel₀ hB0]
    ring
  have hargA := (abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hA)))
  have hargB := (abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hB)))
  have hargBπ : (z + 1 / 2).arg ≠ Real.pi := by linarith [Real.pi_pos]
  have hlog : log ((z - 1 / 2) / (z + 1 / 2)) = log (z - 1 / 2) - log (z + 1 / 2) := by
    rw [div_eq_mul_inv, Complex.log_mul hA0 (inv_ne_zero hB0), Complex.log_inv _ hargBπ]
    · rfl
    · rw [arg_inv, if_neg hargBπ]
      constructor <;> linarith [hargA.1, hargA.2, hargB.1, hargB.2]
  have hpow : (1 - (z + 1 / 2)⁻¹) ^ (κ - μ - 1 / 2) =
      (z - 1 / 2) ^ (κ - μ - 1 / 2) * (z + 1 / 2) ^ (-(κ - μ - 1 / 2)) := by
    rw [hr, cpow_def_of_ne_zero (div_ne_zero hA0 hB0), hlog,
      sub_mul, exp_sub, cpow_def_of_ne_zero hA0, cpow_def_of_ne_zero hB0,
      mul_neg, exp_neg, div_eq_mul_inv]
  have hi : (∫ t : ℝ in Set.Ioi 0,
      exp (-z * t) * (t : ℂ) ^ (μ - 1 / 2) * whittakerM κ μ t) =
      Gamma (2 * μ + 1) * ∫ t : ℝ in Set.Ioi 0,
        exp (-(z + 1 / 2) * t) * (t : ℂ) ^ ((2 * μ + 1) - 1) *
          regularizedHGFun {μ - κ + 1 / 2} {2 * μ + 1} t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [whittakerM, kummerM_eq_mul_regularizedHGFun hp,
      show 1 + 2 * μ = 2 * μ + 1 by ring]
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have he : exp (-z * t) * exp (-(t : ℂ) / 2) = exp (-(z + 1 / 2) * t) := by
      rw [← exp_add]
      congr 1
      ring
    have htP : (t : ℂ) ^ (μ - 1 / 2) * (t : ℂ) ^ (μ + 1 / 2) =
        (t : ℂ) ^ ((2 * μ + 1) - 1) := by
      rw [← cpow_add _ _ ht0]
      congr 1
      ring
    calc
      _ = Gamma (2 * μ + 1) * (exp (-z * t) * exp (-(t : ℂ) / 2)) *
          ((t : ℂ) ^ (μ - 1 / 2) * (t : ℂ) ^ (μ + 1 / 2)) *
          regularizedHGFun {μ - κ + 1 / 2} {2 * μ + 1} t := by ring
      _ = _ := by rw [he, htP]; ring
  rw [hi, laplace_regularizedHGFun_self hb (by simp; linarith),
    show -(μ - κ + 1 / 2) = κ - μ - 1 / 2 by ring, hpow]
  rw [show -(2 * μ + 1) = (-κ - μ - 1 / 2) + (κ - μ - 1 / 2) by ring,
    cpow_add _ _ hB0]
  have hc : (z + 1 / 2) ^ (κ - μ - 1 / 2) * (z + 1 / 2) ^ (-(κ - μ - 1 / 2)) = 1 := by
    rw [cpow_neg, mul_inv_cancel₀ (cpow_ne_zero_iff.mpr (Or.inl hB0))]
  linear_combination Gamma (2 * μ + 1) * (z + 1 / 2) ^ (-κ - μ - 1 / 2) *
    (z - 1 / 2) ^ (κ - μ - 1 / 2) * hc

/-- The Mellin transform uses regularized M, including exceptional second parameters. -/
@[dlmf 13.23.E3]
theorem mellin_whittakerM {κ μ ν : ℂ}
    (h0 : -1 / 2 - μ.re < ν.re) (h1 : ν.re < κ.re) :
    ∫ t : ℝ in Set.Ioi 0, exp (-(t : ℂ) / 2) * (t : ℂ) ^ (ν - 1) *
        regularizedWhittakerM κ μ t =
      Gamma (μ + ν + 1 / 2) * Gamma (κ - ν) /
        (Gamma (1 / 2 + μ + κ) * Gamma (1 / 2 + μ - ν)) := by
  have hm := mellin_regularizedHGFun_exp (a := μ - κ + 1 / 2)
    (b := μ + ν + 1 / 2) (c := 1 + 2 * μ) (by simp; linarith) (by simp; linarith)
  have he : ∀ t ∈ Set.Ioi (0 : ℝ),
      exp (-(t : ℂ) / 2) * (t : ℂ) ^ (ν - 1) * regularizedWhittakerM κ μ t =
      exp (-(t : ℂ)) * (t : ℂ) ^ (μ + ν + 1 / 2 - 1) *
        regularizedHGFun {μ - κ + 1 / 2} {1 + 2 * μ} t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have hp : (t : ℂ) ^ (ν - 1) * (t : ℂ) ^ (μ + 1 / 2) =
        (t : ℂ) ^ (μ + ν + 1 / 2 - 1) := by
      rw [← cpow_add _ _ ht0]; congr 1; ring
    have hx : exp (-(t : ℂ) / 2) * exp (-(t : ℂ) / 2) = exp (-(t : ℂ)) := by
      rw [← exp_add]; congr 1; ring
    rw [regularizedWhittakerM, ← hp, ← hx]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi he, hm,
    show (1 + 2 * μ) - (μ - κ + 1 / 2) - (μ + ν + 1 / 2) = κ - ν by ring,
    show (1 + 2 * μ) - (μ - κ + 1 / 2) = 1 / 2 + μ + κ by ring,
    show (1 + 2 * μ) - (μ + ν + 1 / 2) = 1 / 2 + μ - ν by ring]

/-- Identity under the stated parameter and domain assumptions: `∫ t : ℝ in Set.Ioi 0, exp (-z *
t) * (t : ℂ) ^ (ν - 1) * whittakerW κ μ t = Gamma (1 / 2 + μ + ν) * Gamma (1 / 2 - μ + ν) *
DLMF.Hypergeometric.regularizedGaussHG (1 / 2 - μ + ν) (1 / 2 + μ + ν) (ν - κ + 1) (1 / 2 -
z)`. -/
@[dlmf 13.23.E4]
theorem laplace_whittakerW {κ μ ν z : ℂ}
    (h : |μ.re| < ν.re + 1 / 2) (hz : -1 / 2 < z.re) :
    ∫ t : ℝ in Set.Ioi 0, exp (-z * t) * (t : ℂ) ^ (ν - 1) * whittakerW κ μ t =
      Gamma (1 / 2 + μ + ν) * Gamma (1 / 2 - μ + ν) *
        DLMF.Hypergeometric.regularizedGaussHG (1 / 2 - μ + ν) (1 / 2 + μ + ν) (ν - κ + 1)
            (1 / 2 - z) := by
  have hμ := abs_le.mp (le_refl |μ.re|)
  have hm := (laplace_kummerU_gauss (a := 1 / 2 + μ - κ) (b := μ + ν + 1 / 2)
    (c := 1 + 2 * μ) (z := z + 1 / 2) (by simp; linarith)
      (by simp; linarith) (by simp; linarith)).2
  have he : ∀ t ∈ Set.Ioi (0 : ℝ),
      exp (-z * t) * (t : ℂ) ^ (ν - 1) * whittakerW κ μ t =
        tricomiLaplaceKernel (1 / 2 + μ - κ) (μ + ν + 1 / 2) (1 + 2 * μ) (z + 1 / 2) t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have hp : (t : ℂ) ^ (ν - 1) * (t : ℂ) ^ (1 / 2 + μ) =
        (t : ℂ) ^ (μ + ν + 1 / 2 - 1) := by
      rw [← cpow_add _ _ ht0]; congr 1; ring
    have hx : exp (-z * t) * exp (-(t : ℂ) / 2) = exp (-(z + 1 / 2) * t) := by
      rw [← exp_add]; congr 1; ring
    rw [whittakerW, tricomiLaplaceKernel, ← hp, ← hx]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi he, hm,
    show μ + ν + 1 / 2 = 1 / 2 + μ + ν by ring,
    show (1 / 2 + μ + ν) - (1 + 2 * μ) + 1 = 1 / 2 - μ + ν by ring,
    show (1 / 2 + μ - κ) + (1 / 2 + μ + ν) - (1 + 2 * μ) + 1 = ν - κ + 1 by ring,
    show 1 - (z + 1 / 2) = 1 / 2 - z by ring,
    DLMF.Hypergeometric.regularizedGaussHG_symm _ _ _ (by
      change 1 - (1 / 2 - z) ∈ slitPlane
      left; simp; linarith)]

/-- Identity under the stated parameter and domain assumptions: `∫ t : ℝ in Set.Ioi 0, exp ((t :
ℂ) / 2) * (t : ℂ) ^ (ν - 1) * whittakerW κ μ t = Gamma (1 / 2 + μ + ν) * Gamma (1 / 2 - μ + ν)
* Gamma (-κ - ν) / (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ))`. -/
@[dlmf 13.23.E5]
theorem mellin_whittakerW {κ μ ν : ℂ}
    (h0 : |μ.re| - 1 / 2 < ν.re) (h1 : ν.re < -κ.re) :
    ∫ t : ℝ in Set.Ioi 0, exp ((t : ℂ) / 2) * (t : ℂ) ^ (ν - 1) * whittakerW κ μ t =
      Gamma (1 / 2 + μ + ν) * Gamma (1 / 2 - μ + ν) * Gamma (-κ - ν) /
        (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) := by
  have hμ := abs_le.mp (le_refl |μ.re|)
  have hm := mellin_kummerU (a := 1 / 2 + μ - κ) (b := 1 + 2 * μ) (lam := ν + μ + 1 / 2)
    (by simp; linarith) (by simp; linarith) (by simp; linarith)
  have hcongr : ∀ t ∈ Set.Ioi (0 : ℝ),
      exp ((t : ℂ) / 2) * (t : ℂ) ^ (ν - 1) * whittakerW κ μ t =
        (t : ℂ) ^ (ν + μ + 1 / 2 - 1) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have hp : (t : ℂ) ^ (ν - 1) * (t : ℂ) ^ (1 / 2 + μ) = (t : ℂ) ^ (ν + μ + 1 / 2 - 1) := by
      rw [← cpow_add _ _ ht0]; ring_nf
    have he : exp ((t : ℂ) / 2) * exp (-(t : ℂ) / 2) = 1 := by
      rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
    rw [whittakerW, ← hp]
    linear_combination ((t : ℂ) ^ (ν - 1) * (t : ℂ) ^ (1 / 2 + μ) *
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) t) * he
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, hm]
  congr 1
  · rw [show ν + μ + 1 / 2 = 1 / 2 + μ + ν by ring,
      show 1 / 2 + μ - κ - (1 / 2 + μ + ν) = -κ - ν by ring,
      show 1 / 2 + μ + ν - (1 + 2 * μ) + 1 = 1 / 2 - μ + ν by ring]
    ring
  · rw [show 1 / 2 + μ - κ - (1 + 2 * μ) + 1 = 1 / 2 - μ - κ by ring]

open Set in
/-- A cosine transform of regularized Whittaker M. For `κ + μ ≤ 0` the integral converges only
conditionally, which Lean's integral does not capture, so `0 < κ + μ` is required. -/
@[dlmf 13.23.E8]
theorem cosine_whittakerM {κ μ x : ℝ} (hx : 0 < x)
    (h : 0 < (κ + μ : ℂ).re) :
    ∫ t : ℝ in Set.Ioi 0,
        Complex.cos (2 * x * t) * exp (-(t : ℂ) ^ 2 / 2) *
          (t : ℂ) ^ (-(2 * (μ : ℂ) + 1)) *
          regularizedWhittakerM κ μ ((t : ℂ) ^ 2) =
      (Real.sqrt π : ℂ) * exp (-(x : ℂ) ^ 2 / 2) * (x : ℂ) ^ ((μ : ℂ) + κ - 1) /
        (2 * Gamma (1 / 2 + (μ : ℂ) + κ)) *
        whittakerW (κ / 2 - 3 * μ / 2) (κ / 2 + μ / 2) (x ^ 2) := by
  have hκμ : 0 < κ + μ := by simpa using h
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hC := cosine_regularizedHGFun (a := μ + κ + 1 / 2) (b := 1 + 2 * μ) hx (by linarith)
  push_cast at hC
  have hcongr : ∀ t ∈ Ioi (0 : ℝ),
      Complex.cos (2 * x * t) * exp (-(t : ℂ) ^ 2 / 2) * (t : ℂ) ^ (-(2 * (μ : ℂ) + 1)) *
          regularizedWhittakerM κ μ ((t : ℂ) ^ 2) =
        Complex.cos (2 * x * t) *
          regularizedHGFun {(μ : ℂ) + κ + 1 / 2} {1 + 2 * (μ : ℂ)} (-(t : ℂ) ^ 2) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    have hp : (t : ℂ) ^ (-(2 * (μ : ℂ) + 1)) * ((t : ℂ) ^ 2) ^ ((μ : ℂ) + 1 / 2) = 1 := by
      rw [sq, mul_cpow_ofReal_nonneg ht0.le ht0.le, ← cpow_add _ _ htc, ← cpow_add _ _ htc]
      ring_nf; exact cpow_zero _
    have he : exp (-(t : ℂ) ^ 2 / 2) * exp (-((t : ℂ) ^ 2) / 2) * exp ((t : ℂ) ^ 2) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf; exact Complex.exp_zero
    rw [regularizedWhittakerM, regularizedConfluent_kummer_transform,
      show 1 + 2 * (μ : ℂ) - ((μ : ℂ) - κ + 1 / 2) = (μ : ℂ) + κ + 1 / 2 by ring]
    linear_combination (Complex.cos (2 * x * t) *
      regularizedHGFun {(μ : ℂ) + κ + 1 / 2} {1 + 2 * (μ : ℂ)} (-(t : ℂ) ^ 2)) *
      (exp (-(t : ℂ) ^ 2 / 2) * exp (-((t : ℂ) ^ 2) / 2) * exp ((t : ℂ) ^ 2) * hp + he)
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, hC, whittakerW]
  rw [show (1 : ℂ) / 2 + ((κ : ℂ) / 2 + (μ : ℂ) / 2) - ((κ : ℂ) / 2 - 3 * (μ : ℂ) / 2) =
      1 + 2 * (μ : ℂ) - 1 / 2 by ring,
    show (1 : ℂ) + 2 * ((κ : ℂ) / 2 + (μ : ℂ) / 2) = (μ : ℂ) + κ + 1 / 2 + 1 / 2 by ring,
    show (1 : ℂ) / 2 + (μ : ℂ) + κ = (μ : ℂ) + κ + 1 / 2 by ring]
  have hp : (x : ℂ) ^ ((μ : ℂ) + κ - 1) * ((x : ℂ) ^ 2) ^ ((1 : ℂ) / 2 + ((κ : ℂ) / 2 + (μ : ℂ) / 2)) =
      (x : ℂ) ^ (2 * ((μ : ℂ) + κ + 1 / 2) - 1) := by
    rw [sq, mul_cpow_ofReal_nonneg hx.le hx.le, ← cpow_add _ _ hx0, ← cpow_add _ _ hx0]
    ring_nf
  have he : exp (-(x : ℂ) ^ 2 / 2) * exp (-((x : ℂ) ^ 2) / 2) = exp (-(x : ℂ) ^ 2) := by
    rw [← Complex.exp_add]; ring_nf
  rw [← hp, ← he]
  ring

/-- A Hankel-type transform of regularized Whittaker M, for real `x > 0`. For non-real `x` the Bessel kernel
grows like `exp (c √t)`; the parameter bound makes the integrand absolutely integrable, as
required for Lean's integral. -/
@[dlmf 13.23.E9]
theorem bessel_whittakerM {κ μ ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hμ : -1 / 2 < μ.re) (hμ' : μ.re < κ.re + ν.re / 2 - 1 / 4) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ) / 2) * (t : ℂ) ^ (μ - (ν + 1) / 2) * regularizedWhittakerM κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      exp (-x / 2) *
        x ^ ((κ - μ - 3 / 2) / 2) *
        regularizedWhittakerM ((κ + 3 * μ - ν + 1 / 2) / 2) ((κ - μ + ν - 1 / 2) / 2) x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have h := bessel_regularizedHGFun (a := μ - κ + 1 / 2) (b := 1 + 2 * μ) (ν := ν) hx hxi
    (by simp; linarith) (by simp; linarith)
  have hpt : ∀ t ∈ Set.Ioi (0:ℝ), exp (-(t : ℂ) / 2) * (t : ℂ) ^ (μ - (ν + 1) / 2) *
      regularizedWhittakerM κ μ t * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      exp (-(t : ℂ)) * (t : ℂ) ^ (1 + 2 * μ - 1 - ν / 2) *
        regularizedHGFun {μ - κ + 1 / 2} {1 + 2 * μ} t * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    have e1 : (t : ℂ) ^ (μ - (ν + 1) / 2) * (t : ℂ) ^ (μ + 1 / 2) = (t : ℂ) ^ (1 + 2 * μ - 1 - ν / 2) := by
      rw [← cpow_add _ _ htc]; ring_nf
    have e2 : exp (-(t : ℂ) / 2) * exp (-(t : ℂ) / 2) = exp (-(t : ℂ)) := by
      rw [← Complex.exp_add]; ring_nf
    simp only [regularizedWhittakerM]
    rw [← e1, ← e2]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, h]
  simp only [regularizedWhittakerM]
  have e3 : x ^ ((κ - μ - 3 / 2) / 2) * x ^ ((κ - μ + ν - 1 / 2) / 2 + 1 / 2) =
      x ^ (-(μ - κ + 1 / 2) + ν / 2) := by
    rw [← cpow_add _ _ hx0]; ring_nf
  have e2 : exp (-x / 2) * exp (-x / 2) = exp (-x) := by
    rw [← Complex.exp_add]; ring_nf
  rw [show (κ - μ + ν - 1 / 2) / 2 - (κ + 3 * μ - ν + 1 / 2) / 2 + 1 / 2 = ν - (1 + 2 * μ) + 1 by ring,
    show 1 + 2 * ((κ - μ + ν - 1 / 2) / 2) = ν - (μ - κ + 1 / 2) + 1 by ring, ← e3, ← e2]
  ring

open Set in
/-- A Hankel-type transform of regularized Whittaker M in terms of W, for real `x > 0`. For non-real `x` the
Bessel kernel grows like `exp (c √t)`; the parameter bound makes the integrand absolutely
integrable, as required for Lean's integral. -/
@[dlmf 13.23.E10]
theorem bessel_whittakerM_W {κ μ ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hν0 : -1 < ν.re) (hν1 : ν.re < 2 * (κ + μ).re - 1 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ) / 2) * (t : ℂ) ^ ((ν - 1) / 2 - μ) * regularizedWhittakerM κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      exp (-x / 2) * x ^ ((κ + μ - 3 / 2) / 2) / Gamma (1 / 2 + μ + κ) *
        whittakerW ((κ - 3 * μ + ν + 1 / 2) / 2) ((κ + μ - ν - 1 / 2) / 2) x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hM := bessel_regularizedHGFun_U (a := μ - κ + 1 / 2) (b := 1 + 2 * μ) (ν := ν) hx hxi hν0
    (by simp at hν1 ⊢; linarith)
  have hcongr : ∀ t ∈ Ioi (0 : ℝ),
      exp (-(t : ℂ) / 2) * (t : ℂ) ^ ((ν - 1) / 2 - μ) * regularizedWhittakerM κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
        exp (-(t : ℂ)) * (t : ℂ) ^ (ν / 2) * regularizedHGFun {μ - κ + 1 / 2} {1 + 2 * μ} t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have hp : (t : ℂ) ^ ((ν - 1) / 2 - μ) * (t : ℂ) ^ (μ + 1 / 2) = (t : ℂ) ^ (ν / 2) := by
      rw [← cpow_add _ _ ht0]; ring_nf
    have he : exp (-(t : ℂ) / 2) * exp (-(t : ℂ) / 2) = exp (-(t : ℂ)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [regularizedWhittakerM, ← hp, ← he]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, hM, whittakerW,
    show 1 / 2 + (κ + μ - ν - 1 / 2) / 2 - (κ - 3 * μ + ν + 1 / 2) / 2 =
      (μ - κ + 1 / 2) - (μ - κ + 1 / 2 - (1 + 2 * μ) + ν + 2) + 1 by ring,
    show 1 + 2 * ((κ + μ - ν - 1 / 2) / 2) = 2 - (μ - κ + 1 / 2 - (1 + 2 * μ) + ν + 2) by ring,
    kummerU_kummer_transform_all (μ - κ + 1 / 2) (μ - κ + 1 / 2 - (1 + 2 * μ) + ν + 2) hx0,
    show 1 + 2 * μ - (μ - κ + 1 / 2) = 1 / 2 + μ + κ by ring]
  have hp1 : x ^ (ν / 2) * x ^ (1 - (μ - κ + 1 / 2 - (1 + 2 * μ) + ν + 2)) =
      x ^ ((κ + μ - 3 / 2) / 2) * x ^ (1 / 2 + (κ + μ - ν - 1 / 2) / 2) := by
    rw [← cpow_add _ _ hx0, ← cpow_add _ _ hx0]; ring_nf
  have he : exp (-x / 2) * exp (-x / 2) = exp (-x) := by
    rw [← Complex.exp_add]; ring_nf
  rw [← he]
  linear_combination (exp (-x / 2) * exp (-x / 2) / Gamma (1 / 2 + μ + κ) *
    kummerU (μ - κ + 1 / 2 - (μ - κ + 1 / 2 - (1 + 2 * μ) + ν + 2) + 1)
      (2 - (μ - κ + 1 / 2 - (1 + 2 * μ) + ν + 2)) x) * hp1

open Set in
/-- A Hankel-type transform of `e^{t/2}` times Whittaker W, for real `x > 0`. For non-real `x` the
Bessel kernel grows like `exp (c √t)`; the parameter bound makes the integrand absolutely
integrable, as required for Lean's integral. -/
@[dlmf 13.23.E11]
theorem bessel_whittakerW {κ μ ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hν0 : (2 * μ.re - 1) < ν.re) (hν1 : -1 < ν.re) (hν2 : ν.re < 2 * (μ - κ).re - 1 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        exp ((t : ℂ) / 2) * (t : ℂ) ^ ((ν - 1) / 2 - μ) * whittakerW κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      Gamma (ν - 2 * μ + 1) / Gamma (1 / 2 + μ - κ) * exp (x / 2) *
        x ^ ((μ - κ - 3 / 2) / 2) *
        whittakerW ((κ + 3 * μ - ν - 1 / 2) / 2) ((κ - μ + ν + 1 / 2) / 2) x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hK := bessel_kummerU (a := 1 / 2 + μ - κ) (b := 1 + 2 * μ) (ν := ν) hx hxi
    (by simp; linarith) hν1 (by simp at hν2 ⊢; linarith)
  have hcongr : ∀ t ∈ Ioi (0 : ℝ),
      exp ((t : ℂ) / 2) * (t : ℂ) ^ ((ν - 1) / 2 - μ) * whittakerW κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
        (t : ℂ) ^ (ν / 2) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have hp : (t : ℂ) ^ ((ν - 1) / 2 - μ) * (t : ℂ) ^ (1 / 2 + μ) = (t : ℂ) ^ (ν / 2) := by
      rw [← cpow_add _ _ ht0]; ring_nf
    have he : exp ((t : ℂ) / 2) * exp (-(t : ℂ) / 2) = 1 := by
      rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
    rw [whittakerW, ← hp]
    linear_combination ((t : ℂ) ^ ((ν - 1) / 2 - μ) * (t : ℂ) ^ (1 / 2 + μ) *
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) t * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ))) * he
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, hK, whittakerW,
    show 1 / 2 + (κ - μ + ν + 1 / 2) / 2 - (κ + 3 * μ - ν - 1 / 2) / 2 = ν - (1 + 2 * μ) + 2 by
      ring,
    show 1 + 2 * ((κ - μ + ν + 1 / 2) / 2) = ν - (1 / 2 + μ - κ) + 2 by ring]
  have hp : x ^ ((μ - κ - 3 / 2) / 2) * x ^ (1 / 2 + (κ - μ + ν + 1 / 2) / 2) = x ^ (ν / 2) := by
    rw [← cpow_add _ _ hx0]; ring_nf
  have he : exp (x / 2) * exp (-x / 2) = 1 := by
    rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
  rw [show ν - 2 * μ + 1 = ν - (1 + 2 * μ) + 2 by ring, ← hp]
  linear_combination (Gamma (ν - (1 + 2 * μ) + 2) / Gamma (1 / 2 + μ - κ) *
    (x ^ ((μ - κ - 3 / 2) / 2) * x ^ (1 / 2 + (κ - μ + ν + 1 / 2) / 2)) *
    kummerU (ν - (1 + 2 * μ) + 2) (ν - (1 / 2 + μ - κ) + 2) x) * (-he)

open Set in
/-- The output M is regularized; Gamma poles in its second parameter are retained. -/
@[dlmf 13.23.E12]
theorem bessel_whittakerW_M {κ μ ν x : ℂ} (hx : 0 < x.re)
    (hν0 : (2 * μ.re - 1) < ν.re) (hν1 : -1 < ν.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ) / 2) * (t : ℂ) ^ ((ν - 1) / 2 - μ) * whittakerW κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      Gamma (ν - 2 * μ + 1) * exp (-x / 2) *
        x ^ ((μ + κ - 3 / 2) / 2) *
        regularizedWhittakerM ((κ - 3 * μ + ν + 1 / 2) / 2) ((ν - μ - κ + 1 / 2) / 2) x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      exp (-(t : ℂ) / 2) * (t : ℂ) ^ ((ν - 1) / 2 - μ) * whittakerW κ μ t *
        besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      exp (-(t : ℂ)) * (t : ℂ) ^ (ν / 2) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) t *
        besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) := by
    intro t ht
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have he : exp (-(t : ℂ) / 2) * exp (-(t : ℂ) / 2) = exp (-(t : ℂ)) := by
      rw [← exp_add]; ring_nf
    have hp : (t : ℂ) ^ ((ν - 1) / 2 - μ) * (t : ℂ) ^ (1 / 2 + μ) = (t : ℂ) ^ (ν / 2) := by
      rw [← cpow_add _ _ htc]; ring_nf
    rw [whittakerW, ← he, ← hp]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    bessel_kummerU_M hx (by simp; linarith) hν1, regularizedWhittakerM,
    show 1 / 2 + μ - κ - (1 + 2 * μ) + ν + 2 = 1 + 2 * ((ν - μ - κ + 1 / 2) / 2) by ring,
    show ν - (1 + 2 * μ) + 2 = ν - 2 * μ + 1 by ring,
    show 1 / 2 + μ - κ = (ν - μ - κ + 1 / 2) / 2 - (κ - 3 * μ + ν + 1 / 2) / 2 + 1 / 2 by ring]
  have he : exp (-x / 2) * exp (-x / 2) = exp (-x) := by rw [← exp_add]; ring_nf
  have hp : x ^ ((μ + κ - 3 / 2) / 2) * x ^ ((ν - μ - κ + 1 / 2) / 2 + 1 / 2) = x ^ (ν / 2) := by
    rw [← cpow_add _ _ hx0]; ring_nf
  rw [← he, ← hp]; ring

end DLMF.Confluent
end
end
