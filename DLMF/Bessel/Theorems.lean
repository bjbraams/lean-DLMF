/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Generating
public import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Recurrences, integrals, addition formulae, and zeros (AAR §§4.6–4.11, 4.14–4.15)

These are the remaining named identities of AAR Chapter 4 that are absent from Mathlib.
-/

@[expose] public section

open Complex intervalIntegral
open scoped Real Nat Topology
open DLMF.OrthogonalPolynomials
open DLMF.Hypergeometric
open DLMF.Confluent

noncomputable section

namespace DLMF.Bessel

/-- Recurrence `(2ν/z) J_ν(z) = J_{ν-1}(z) + J_{ν+1}(z)` (AAR (4.6.5), p. 202). -/
@[dlmf 10.6.E1]
theorem besselJ_add_sub {ν z : ℂ} (hz : z ≠ 0) :
    (2 * ν / z) * besselJ ν z = besselJ (ν - 1) z + besselJ (ν + 1) z := by
  have he := regularized0F1_contiguous ν (-(z ^ 2 / 4))
  simp only [besselJ_eq_regularized]
  rw [cpow_sub _ _ (div_ne_zero hz (by norm_num)),
    cpow_add _ _ (div_ne_zero hz (by norm_num)), cpow_one]
  rw [show ν - 1 + 1 = ν by ring]
  linear_combination (norm := (field_simp [hz]; ring)) (-2 * (z / 2) ^ ν / z) * he

/-- Derivative identity `2 J_ν'(z) = J_{ν-1}(z) - J_{ν+1}(z)` (AAR (4.6.6), p. 202). -/
@[dlmf 10.6.E1]
theorem two_deriv_besselJ {ν z : ℂ} (hz : z ∈ slitPlane) :
    2 * deriv (besselJ ν) z = besselJ (ν - 1) z - besselJ (ν + 1) z := by
  rw [(hasDerivAt_besselJ hz).deriv]
  linear_combination besselJ_add_sub (ν := ν) (slitPlane_ne_zero hz)

/-- Poisson's integral (AAR §4.7). -/
@[dlmf 10.9.E4]
theorem besselJ_eq_poisson_integral {ν : ℂ} {x : ℝ}
    (hν : -1 / 2 < ν.re) (hx : 0 < x) :
    besselJ ν x =
      (x / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) *
        ∫ t : ℝ in (-1 : ℝ)..1,
          (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2) * exp (I * x * t) := by
  have ha : 0 < (ν + 1 / 2).re := by
    norm_num
    linarith
  have hb : 0 < (ν + 1).re := by simp only [add_re, one_re]; linarith
  have hc : 0 < (2 * ν + 1).re := by simp; linarith
  have hca : 2 * ν + 1 - (ν + 1 / 2) = ν + 1 / 2 := by ring
  let w : ℝ → ℂ := fun u => (u : ℂ) ^ (ν - 1 / 2) *
    (1 - (u : ℂ)) ^ (ν - 1 / 2) * exp (2 * I * x * u)
  let f : ℝ → ℂ := fun t => (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2) * exp (I * x * t)
  have hi : (∫ t : ℝ in (-1 : ℝ)..1, f t) =
      2 * (4 : ℂ) ^ (ν - 1 / 2) * exp (-I * x) * ∫ u : ℝ in (0 : ℝ)..1, w u := by
    have hsub := intervalIntegral.smul_integral_comp_mul_sub f
      (a := (0 : ℝ)) (b := 1) 2 1
    simp only [mul_zero, zero_sub, mul_one, show (2 : ℝ) - 1 = 1 by norm_num,
      Complex.real_smul, ofReal_ofNat] at hsub
    rw [← hsub, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    have hbase : 1 - ((2 * u - 1 : ℝ) : ℂ) ^ 2 =
        (4 : ℂ) * ((u : ℂ) * ((1 - u : ℝ) : ℂ)) := by push_cast; ring
    have hpow : (1 - ((2 * u - 1 : ℝ) : ℂ) ^ 2) ^ (ν - 1 / 2) =
        (4 : ℂ) ^ (ν - 1 / 2) *
          ((u : ℂ) ^ (ν - 1 / 2) * (1 - (u : ℂ)) ^ (ν - 1 / 2)) := by
      rw [hbase, ← ofReal_mul, ← ofReal_ofNat (n := 4),
        mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 4)
          (mul_nonneg hu.1.le (sub_nonneg.mpr hu.2.le)), ofReal_mul,
        mul_cpow_ofReal_nonneg hu.1.le (sub_nonneg.mpr hu.2.le), ofReal_sub, ofReal_one]
    have he : I * (x : ℂ) * ((2 * u - 1 : ℝ) : ℂ) = -I * x + 2 * I * x * u := by
      push_cast; ring
    dsimp [f, w]
    rw [hpow, he, exp_add]
    ring
  have hM := kummerM_eq_euler_integral (z := 2 * I * x) ha
    (show 0 < (2 * ν + 1 - (ν + 1 / 2)).re by rwa [hca])
  rw [hca, show ν + 1 / 2 - 1 = ν - 1 / 2 by ring] at hM
  change kummerM (ν + 1 / 2) (2 * ν + 1) (2 * I * x) =
    Gamma (2 * ν + 1) / (Gamma (ν + 1 / 2) * Gamma (ν + 1 / 2)) *
      ∫ u : ℝ in (0 : ℝ)..1, w u at hM
  have hA : Gamma (ν + 1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hB : Gamma (ν + 1) ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hP : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpow : (4 : ℂ) ^ (ν - 1 / 2) * (2 : ℂ) ^ (-2 * ν) = 1 / 2 := by
    rw [show (4 : ℂ) = (2 : ℝ) * (2 : ℝ) by norm_num,
      mul_cpow_ofReal_nonneg (by norm_num) (by norm_num), ofReal_ofNat, ← cpow_add _ _ (by norm_num),
      ← cpow_add _ _ (by norm_num)]
    rw [show ν - 1 / 2 + (ν - 1 / 2) + -2 * ν = -1 by ring, cpow_neg_one]
    norm_num
  have hd := Gamma_mul_Gamma_add_half (ν + 1 / 2)
  rw [show ν + 1 / 2 + 1 / 2 = ν + 1 by ring,
    show 2 * (ν + 1 / 2) = 2 * ν + 1 by ring,
    show 1 - (2 * ν + 1) = -2 * ν by ring] at hd
  have hG : Gamma (2 * ν + 1) =
      2 * (4 : ℂ) ^ (ν - 1 / 2) * Gamma (ν + 1 / 2) * Gamma (ν + 1) / Real.sqrt π := by
    apply (eq_div_iff hP).mpr
    linear_combination -2 * Gamma (2 * ν + 1) * (Real.sqrt π : ℂ) * hpow -
      2 * (4 : ℂ) ^ (ν - 1 / 2) * hd
  rw [besselJ_eq_kummerM (not_neg_nat_of_re_pos hb) (not_neg_nat_of_re_pos hc), hM]
  change _ = (x / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) *
    ∫ t : ℝ in (-1 : ℝ)..1, f t
  rw [hi, hG]
  field [hA, hB, hP]

/-- The generating function for integer-order Bessel functions, AAR (4.9.10). -/
@[dlmf 10.12.E1]
theorem besselJ_generating_function (z t : ℂ) (ht : t ≠ 0) :
    exp (z / 2 * (t - t⁻¹)) = ∑' n : ℤ, besselJ n z * t ^ n := by
  exact (hasSum_besselJ_generating_function z t ht).tsum_eq.symm

-- Gegenbauer's addition theorem `besselJ_addition` (DLMF 10.23.8) is proved in
-- `DLMF/SphericalHarmonics/BesselAddition.lean`, which can import the Gegenbauer polynomial API.

/-- At a nonzero point, a zero of regularized `₀F₁` has nonzero derivative.
The contiguous relation propagates a hypothetical double zero to every derivative. -/
lemma regularized0F1_deriv_ne_zero {c w : ℂ} (hc : ∀ k : ℕ, c ≠ -k)
    (hw : w ≠ 0) (hroot : regularizedHGFun (∅ : Multiset ℂ) {c} w = 0) :
    deriv (regularizedHGFun (∅ : Multiset ℂ) {c}) w ≠ 0 := by
  intro hd
  rw [deriv_regularized0F1] at hd
  have hshift (n : ℕ) : regularizedHGFun (∅ : Multiset ℂ) {c + n} w = 0 ∧
      regularizedHGFun (∅ : Multiset ℂ) {c + n + 1} w = 0 := by
    induction n with
    | zero => simpa only [Nat.cast_zero, add_zero] using And.intro hroot hd
    | succ n ih =>
      have he := regularized0F1_contiguous (c + n) w
      rw [ih.1, ih.2, mul_zero, zero_add] at he
      have hn := (mul_eq_zero.mp he.symm).resolve_left hw
      simpa only [Nat.cast_add, Nat.cast_one, ← add_assoc] using And.intro ih.2 hn
  have hder (n : ℕ) : iteratedDeriv n (regularizedHGFun (∅ : Multiset ℂ) {c}) =
      regularizedHGFun (∅ : Multiset ℂ) {c + n} := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext z
      rw [deriv_regularized0F1]
      congr 2
      push_cast
      ring
  have he (n : ℕ) : iteratedDeriv n (regularizedHGFun (∅ : Multiset ℂ) {c}) w =
      iteratedDeriv n (fun _ : ℂ => (0 : ℂ)) w := by
    rw [hder, (hshift n).1]
    simp
  have hf : regularizedHGFun (∅ : Multiset ℂ) {c} = (fun _ : ℂ => (0 : ℂ)) := by
    apply AnalyticOnNhd.eq_of_eventuallyEq
      (fun z _ => analyticAt_regularized0F1 c z) (fun _ _ => analyticAt_const) (z₀ := w)
    have hp := (analyticAt_regularized0F1 c w).hasFPowerSeriesAt
    have hq := (analyticAt_const (𝕜 := ℂ) (v := (0 : ℂ)) (x := w)).hasFPowerSeriesAt
    simp_rw [he] at hp
    filter_upwards [hp.eventually_hasSum_sub, hq.eventually_hasSum_sub] with z hz₁ hz₂
    exact hz₁.unique hz₂
  have hz := congrFun hf 0
  rw [DLMF.Confluent.regularizedHGFun_zero, regularizedHGFunCoeff_empty] at hz
  simp [Gamma_ne_zero hc] at hz

/-- The positive zeros of `J_ν` are simple. -/
theorem besselJ_zeros_simple {ν x : ℝ} (hν : -1 < ν) (hx : 0 < x)
    (hroot : besselJ ν x = 0) :
    deriv (besselJ ν) (x : ℂ) ≠ 0 := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hxslit : (x : ℂ) ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    exact Or.inl hx
  have hp (μ : ℂ) : ((x : ℂ) / 2) ^ μ ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (div_ne_zero hx0 (by norm_num)))
  have hf : regularizedHGFun (∅ : Multiset ℂ) {(ν : ℂ) + 1} (-((x : ℂ) ^ 2 / 4)) = 0 := by
    rw [besselJ_eq_regularized] at hroot
    exact (mul_eq_zero.mp hroot).resolve_left (hp ν)
  have hc : ∀ k : ℕ, (ν : ℂ) + 1 ≠ -k := not_neg_nat_of_re_pos (by simp; linarith)
  have hw : -((x : ℂ) ^ 2 / 4) ≠ 0 := neg_ne_zero.mpr (div_ne_zero (pow_ne_zero _ hx0) (by norm_num))
  have hne := regularized0F1_deriv_ne_zero hc hw hf
  rw [deriv_regularized0F1] at hne
  rw [(hasDerivAt_besselJ hxslit).deriv, hroot, mul_zero, zero_sub, neg_ne_zero,
    besselJ_eq_regularized]
  exact mul_ne_zero (hp _) hne

end DLMF.Bessel
