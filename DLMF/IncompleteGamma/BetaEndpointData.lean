/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.Beta
public import DLMF.IncompleteGamma.UniformAsymptotics

/-!
# Endpoint data for incomplete Beta asymptotics

The fixed-argument expansion and endpoint auxiliary functions for DLMF 8.18.1–8.18.7,
including the generating kernel, its real analyticity, and its Taylor coefficients.
The endpoint moments satisfy the recurrence and initial-value identities in DLMF 8.18.4–8.18.5.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
open DLMF.Core

namespace DLMF.Statistical

open DLMF.Confluent

/-- Finite diagonal shifts of the incomplete Beta function. -/
theorem regularizedIncompleteBeta_diagonal_remainder {a b z : ℂ} (ha : ∀ k : ℕ, a+1 ≠ -k)
    (hz : ‖z‖ < 1) (hz0 : z ≠ 0) (N : ℕ) :
    regularizedIncompleteBeta a b z = regularizedIncompleteBeta (a+N) (b-N) z +
      Gamma (a+b)*z^a*(1-z)^(b-1) *
        ∑ k ∈ Finset.range N, (z/(1-z))^k/(Gamma (a+k+1)*Gamma (b-k)) := by
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  have hy : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  induction N with
  | zero => simp
  | succ N ih =>
    have haN : ∀ k : ℕ, (a+N)+1 ≠ -k := by
      intro k h
      exact ha (N+k) (by push_cast; linear_combination h)
    have hs := regularizedIncompleteBeta_shift_diagonal (a+N) (b-N) haN hz hz0
    have hp : z^(a+N)*(1-z)^(b-N-1) = z^a*(1-z)^(b-1)*(z/(1-z))^N := by
      rw [cpow_add _ _ hz0, cpow_natCast,
        show b-(N:ℂ)-1=(b-1)-(N:ℂ) by ring, cpow_sub _ _ hy, cpow_natCast, div_pow]
      field_simp
    rw [show a+((N+1:ℕ):ℂ) = (a+N)+1 by push_cast; ring,
      show b-((N+1:ℕ):ℂ) = (b-N)-1 by push_cast; ring,
      Finset.sum_range_succ, ih, hs,
      show (a+(N:ℂ))+(b-N)=a+b by ring]
    linear_combination (Gamma (a+b) / Gamma (b-N) / Gamma (a+N+1)) * hp

/-- A beta-type Gauss function has a majorant independent of its positive real parameter. -/
theorem incompleteBeta_gauss_uniform_bound (b : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a →
      ‖regularizedGaussHypergeometric a b (a+1) z‖ ≤ C * ‖1 / Gamma ((a:ℂ)+1)‖ := by
  let g : ℕ → ℝ := fun k => ‖gaussHypergeometricCoeff 1 b 1 k * z^k‖
  have hg : Summable g := summable_norm_gaussHypergeometricCoeff_mul_pow 1 b 1 hz
  refine ⟨∑' k, g k, tsum_nonneg (fun k => norm_nonneg _), ?_⟩
  intro a ha
  have hden : ∀ k : ℕ, (a:ℂ)+1 ≠ -k := by
    intro k h; have h' := congrArg Complex.re h; simp at h';
        linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  rw [regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ hz,
    regularizedGaussHypergeometricFun_eq_div_Gamma hden]
  have hF : ₂F₁ (a:ℂ) b ((a:ℂ)+1) z = ∑' k, gaussHypergeometricCoeff a b (a+1) k*z^k := by
    rw [ordinaryHypergeometric_eq_tsum]
    simp only [smul_eq_mul]
    apply tsum_congr; intro k
    simp [gaussHypergeometricCoeff, pochhammer, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hbd : ∀ k : ℕ, ‖gaussHypergeometricCoeff a b (a+1) k*z^k‖ ≤ g k := by
    intro k
    have hpa : ‖pochhammer (a:ℂ) k‖ ≤ ‖pochhammer ((a:ℂ)+1) k‖ := by
      rw [show ((a:ℂ)+1) = ((a+1:ℝ):ℂ) by push_cast; rfl,
        pochhammer, pochhammer, ascPochhammer_eval_ofReal, ascPochhammer_eval_ofReal,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (DLMF.Hypergeometric.ascPochhammer_eval_nonneg ha.le k),
        abs_of_nonneg (DLMF.Hypergeometric.ascPochhammer_eval_nonneg (by linarith) k)]
      exact DLMF.Hypergeometric.ascPochhammer_eval_mono ha.le (by linarith) k
    have hpk : 0 < ‖pochhammer ((a:ℂ)+1) k‖ :=
        norm_pos_iff.mpr (pochhammer_ne_zero_of_not_neg_nat hden k)
    have hfac : (0:ℝ) < k.factorial := by positivity
    have hgk : g k = ‖pochhammer b k‖ * ‖z‖^k / k.factorial := by
      dsimp only [g, gaussHypergeometricCoeff]
      rw [pochhammer_nat_one]
      simp only [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
      field_simp
    rw [hgk]
    simp only [gaussHypergeometricCoeff, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (mul_pos hpk hfac) hfac]
    nlinarith [mul_le_mul_of_nonneg_right hpa
        (mul_nonneg (norm_nonneg (pochhammer b k)) (pow_nonneg (norm_nonneg z) k))]
  have hbnd : ‖₂F₁ (a:ℂ) b ((a:ℂ)+1) z‖ ≤ ∑' k, g k := by
    rw [hF]
    exact tsum_of_norm_bounded hg.hasSum hbd
  rw [norm_div, norm_div, norm_one]
  simpa only [div_eq_mul_inv, one_mul] using
    div_le_div_of_nonneg_right hbnd (norm_nonneg (Gamma ((a:ℂ)+1)))

/-- Fixed-argument incomplete-Beta expansion, with a finite shifted remainder. -/
@[dlmf 8.18.E1]
theorem incompleteBeta_large_a_fixed_x {b x : ℝ} (hb : 0 < b) (hx : 0 < x) (hx1 : x < 1) (N : ℕ) :
    IsBigO atTop (fun a : ℝ =>
        regularizedIncompleteBeta a b x/(Gamma (a+b)*(x : ℂ)^(a : ℂ)*(1-x : ℂ)^((b : ℂ)-1))-∑ k ∈
            Finset.range N,
        ((x : ℂ)/(1-x))^k/(Gamma (a+k+1)*Gamma ((b : ℂ)-k))) (fun a : ℝ => 1/Gamma (a+N+1)) := by
  have hxn : ‖(x:ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hx.le]; exact hx1
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hxne : (x:ℂ) ≠ 1 := by exact_mod_cast hx1.ne
  have hy0 : (1:ℂ)-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxne)
  obtain ⟨C, hC, hbound⟩ := incompleteBeta_gauss_uniform_bound (1-((b:ℂ)-N)) hxn
  set K : ℂ := (x:ℂ)^N/(Gamma ((b:ℂ)-N)*((1:ℂ)-x)^((b:ℂ)-1))
  refine IsBigO.of_bound (‖K‖*C) ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
  have haN : 0 < a+(N:ℝ) := by positivity
  have ha1 : ∀ k : ℕ, (a:ℂ)+1 ≠ -k := by
    intro k h; have h' := congrArg Complex.re h; simp at h';
        linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hG : Gamma ((a:ℂ)+b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using add_pos ha hb)
  have hX : (x:ℂ)^(a:ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  have hY : ((1:ℂ)-x)^((b:ℂ)-1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hy0)
  have hP : Gamma ((a:ℂ)+b)*(x:ℂ)^(a:ℂ)*((1:ℂ)-x)^((b:ℂ)-1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hG hX) hY
  have hd := regularizedIncompleteBeta_diagonal_remainder (a := (a:ℂ)) (b := (b:ℂ)) ha1 hxn hx0 N
  have he : regularizedIncompleteBeta (a:ℂ) b x/(Gamma (a+b)*(x:ℂ)^(a:ℂ)*((1:ℂ)-x)^((b:ℂ)-1)) -
      ∑ k ∈ Finset.range N, ((x:ℂ)/(1-x))^k/(Gamma (a+k+1)*Gamma ((b:ℂ)-k)) =
      regularizedIncompleteBeta ((a:ℂ)+N) ((b:ℂ)-N) x /
        (Gamma ((a:ℂ)+b)*(x:ℂ)^(a:ℂ)*((1:ℂ)-x)^((b:ℂ)-1)) := by
    rw [hd, add_div, mul_div_cancel_left₀ _ hP]
    ring
  rw [he]
  have hr : regularizedIncompleteBeta ((a:ℂ)+N) ((b:ℂ)-N) x /
      (Gamma ((a:ℂ)+b)*(x:ℂ)^(a:ℂ)*((1:ℂ)-x)^((b:ℂ)-1)) =
      K*regularizedGaussHypergeometric ((a:ℂ)+N) (1-((b:ℂ)-N)) ((a:ℂ)+N+1) x := by
    rw [regularizedIncompleteBeta, if_neg hxne,
      show ((a:ℂ)+N)+((b:ℂ)-N) = (a:ℂ)+b by ring,
      cpow_add _ _ hx0, cpow_natCast]
    dsimp only [K]
    by_cases hGb : Gamma ((b:ℂ)-N) = 0
    · simp [hGb]
    · field_simp
  rw [hr, norm_mul]
  have hB := hbound (a+N) haN
  simp only [Complex.ofReal_add, Complex.ofReal_natCast] at hB
  calc ‖K‖*‖regularizedGaussHypergeometric ((a:ℂ)+N) (1-((b:ℂ)-N)) ((a:ℂ)+N+1) x‖ ≤
      ‖K‖*(C*‖1/Gamma ((a:ℂ)+N+1)‖) := mul_le_mul_of_nonneg_left hB (norm_nonneg _)
    _ = _ := by ring

/-- Formula under the stated hypotheses:
`regularizedIncompleteBeta a b x=Gamma (a+b)*(x : ℂ)^(a : ℂ)*(1-x : ℂ)^((b : ℂ)-1)*(∑ k ∈
Finset.range N, ((x : ℂ)/(1-x))^k/(Gamma (a+k+1)*Gamma ((b : ℂ)-k)))`. -/
@[dlmf 8.18.E1]
theorem incompleteBeta_large_a_integer_b_exact {a : ℝ} (ha : 0 < a) {b N : ℕ}
    (hb : 1 ≤ b) (hN : b ≤ N)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    regularizedIncompleteBeta a b x=Gamma
        (a+b)*(x : ℂ)^(a : ℂ)*(1-x : ℂ)^((b : ℂ)-1)*(∑ k ∈ Finset.range N,
        ((x : ℂ)/(1-x))^k/(Gamma (a+k+1)*Gamma ((b : ℂ)-k))) := by
  set X : ℂ := (x:ℂ)
  set Y : ℂ := 1 - (x:ℂ)
  set R : ℂ := X/Y
  have hY : Y ≠ 0 := by
    simp only [Y]; intro h
    have := congrArg Complex.re h; simp at this; linarith
  have hXY : X + Y = 1 := by simp [X, Y]
  have hRY : R * Y = X := by simp only [R]; field_simp
  set G : ℂ → ℂ := fun w => (Gamma w)⁻¹
  have hG (w : ℂ) : G w = w * G (w+1) := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one w
  have hGneg (m : ℕ) : G (-(m:ℂ)) = 0 := by simp [G, Gamma_neg_nat_eq_zero]
  have hterm (b : ℕ) (k : ℕ) : R^k/(Gamma (a+k+1)*Gamma ((b : ℂ)-k)) = R^k*(G (a+k+1)*G (b-k)) := by
    simp only [G, div_eq_mul_inv, mul_inv]
  set S : ℕ → ℂ := fun b => ∑ k ∈ Finset.range N, R^k*(G (a+k+1)*G ((b:ℂ)-k))
  have hS (b : ℕ) : (∑ k ∈ Finset.range N, R^k/(Gamma (a+k+1)*Gamma ((b : ℂ)-k))) = S b :=
    Finset.sum_congr rfl fun k _ => hterm b k
  rw [hS]
  have hxn : ‖(x:ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hx.le]; exact hx1
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have ha1 : ∀ k : ℕ, (a:ℂ)+1 ≠ -k := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  induction b, hb using Nat.le_induction with
  | base =>
    have h1 := regularizedIncompleteBeta_ofReal (a := (a:ℂ)) (b := 1)
        (by simpa using ha) (by norm_num)
      (x := x) ⟨hx.le, hx1.le⟩
    rw [Nat.cast_one, h1, Real.regularizedIncompleteBeta_one_right (by simpa using ha)]
    have hS1 : S 1 = G (a+1) := by
      simp only [S]
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N-1, by omega⟩
      rw [Finset.sum_range_succ']
      have hz : ∀ k ∈ Finset.range M, R^(k+1)*(G (a+((k+1:ℕ):ℂ)+1)*G ((1:ℕ)-((k+1:ℕ):ℂ))) = 0 := by
        intro k _
        rw [show ((1:ℕ):ℂ)-((k+1:ℕ):ℂ) = -(k:ℂ) by push_cast; ring, hGneg, mul_zero, mul_zero]
      rw [Finset.sum_eq_zero hz]
      simp [G]
    rw [hS1, sub_self, cpow_zero]
    simp only [G]
    have hGa : Gamma ((a:ℂ)+1) ≠ 0 := Gamma_ne_zero (by
      intro m hm; exact ha1 m hm)
    field_simp
    rfl
  | succ b hb ih =>
    have ih := ih (by omega)
    have hab : (a:ℂ)+b ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this;
          linarith [(Nat.cast_nonneg b : (0:ℝ) ≤ b)]
    have hsh := regularizedIncompleteBeta_shift_right (a:ℂ) b ha1 hab hxn
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N-1, by omega⟩
    have hbM : b ≤ M := by omega
    have hA : (∑ k ∈ Finset.range (M+1), R^k*(G (a+k)*G (((b+1:ℕ):ℂ)-k))) =
        G a * G (b+1) + R * S b := by
      rw [Finset.sum_range_succ']
      simp only [S]
      rw [Finset.sum_range_succ (fun k => R^k*(G (a+k+1)*G ((b:ℂ)-k))) M]
      obtain ⟨j, hj⟩ : ∃ j, M = b + j := ⟨M-b, by omega⟩
      rw [show (b:ℂ)-(M:ℕ) = -(j:ℂ) by rw [hj]; push_cast; ring, hGneg, mul_zero, mul_zero,
        add_zero, Finset.mul_sum]
      push_cast
      simp only [add_zero, pow_zero, one_mul, sub_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show (a:ℂ)+(k+1) = a+k+1 by ring, show (b:ℂ)+1-(k+1) = b-k by ring, pow_succ]
      ring
    have hB : ((a:ℂ)+b) * S (b+1) = S b + ∑ k ∈ Finset.range (M+1),
        R^k*(G (a+k)*G (((b+1:ℕ):ℂ)-k)) := by
      simp only [S]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have e1 := hG ((a:ℂ)+k)
      have e2 := hG ((b:ℂ)-k)
      rw [show (b:ℂ)-k+1 = ((b+1:ℕ):ℂ)-k by push_cast; ring] at e2
      rw [e1, e2]
      push_cast
      ring
    rw [hA] at hB
    have hYb : Y^(((b+1:ℕ):ℂ)-1) = Y * Y^((b:ℂ)-1) := by
      rw [show ((b+1:ℕ):ℂ)-1 = 1 + ((b:ℂ)-1) by push_cast; ring, cpow_add _ _ hY, cpow_one]
    have hYb' : Y^(b:ℂ) = Y * Y^((b:ℂ)-1) := by
      rw [show (b:ℂ) = 1 + ((b:ℂ)-1) by ring, cpow_add _ _ hY, cpow_one]
      ring_nf
    have hGab : Gamma ((a:ℂ)+((b+1:ℕ):ℂ)) = ((a:ℂ)+b) * Gamma (a+b) := by
      rw [show (a:ℂ)+((b+1:ℕ):ℂ) = (a+b)+1 by push_cast; ring, Gamma_add_one _ hab]
    have hsh' : regularizedIncompleteBeta (a:ℂ) ((b+1:ℕ):ℂ) X = regularizedIncompleteBeta a b X +
        Gamma (a+b)/Gamma (b+1)*X^(a:ℂ)*Y^(b:ℂ)/Gamma a := by
      rw [Nat.cast_succ]; exact hsh
    rw [hsh', ih, hGab, hYb, hYb']
    have hGb : (Gamma ((b:ℂ)+1))⁻¹ = G (b+1) := rfl
    have hGa : (Gamma (a:ℂ))⁻¹ = G a := rfl
    rw [div_eq_mul_inv, div_eq_mul_inv, hGb, hGa]
    clear_value S G R Y X
    linear_combination (-(Gamma (a+b) * X^(a:ℂ) * Y^((b:ℂ)-1))) * Y * hB -
      (Gamma (a+b) * X^(a:ℂ) * Y^((b:ℂ)-1)) * S b * hXY -
      (Gamma (a+b) * X^(a:ℂ) * Y^((b:ℂ)-1)) * S b * hRY

/-- The endpoint variable ξ. -/
@[dlmf 8.18.E2]
def Real.betaXi (x : ℝ) : ℝ :=
  -Real.log x

/-- The removable generating function at t=0. -/
def Real.betaGeneratingKernel (b t : ℝ) : ℝ :=
  if t=0 then 1 else ((1-Real.exp (-t))/t)^(b-1)

/-- Taylor coefficients d_k at ξ. -/
@[dlmf 8.18.E6]
def Real.betaGeneratingCoeff (b ξ : ℝ) (k : ℕ) : ℝ :=
  iteratedDeriv k (Real.betaGeneratingKernel b) ξ/(k.factorial : ℝ)

/-- The endpoint auxiliary functions F_k. -/
def betaAuxF (k : ℕ) (a b ξ : ℝ) : ℂ :=
  (∫ t : ℝ in Ioi ξ, (t-ξ)^k*t^(b-1)*Real.exp (-a*t))/Gamma b

/-- Integrability of the integrands of the endpoint auxiliary functions `F_k`. -/
lemma integrableOn_betaAux_integrand (k : ℕ) {a b ξ : ℝ} (ha : 0 < a) (hb : 0 < b) (hξ : 0 ≤ ξ) :
    IntegrableOn (fun t : ℝ => (t-ξ)^k*t^(b-1)*Real.exp (-a*t)) (Ioi ξ) := by
  have hg : IntegrableOn (fun t : ℝ => t^((k:ℝ)+b-1)*Real.exp (-a*t^(1:ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
        (by have := (Nat.cast_nonneg k : (0:ℝ) ≤ k); linarith) one_pos ha
  have hg' := hg.mono_set (Ioi_subset_Ioi hξ)
  refine hg'.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := lt_of_le_of_lt hξ ht
    refine ContinuousAt.continuousWithinAt ?_
    exact ((continuousAt_id.sub continuousAt_const).pow k).mul
      (Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')) |>.mul (by fun_prop)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
    have ht0 : 0 < t := lt_of_le_of_lt hξ ht
    have h1 : 0 ≤ t - ξ := by linarith [mem_Ioi.mp ht]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_one,
      show (k:ℝ)+b-1 = k + (b-1) by ring, Real.rpow_add ht0, Real.rpow_natCast]
    gcongr
    linarith [mem_Ioi.mp ht]

/-- Integration by parts for the integrals defining `F_k`, including the boundary term
`0^k ξ^b e^{-aξ}`. -/
lemma betaAux_integral_parts (k : ℕ) {a b ξ : ℝ} (ha : 0 < a) (hb : 0 < b) (hξ : 0 ≤ ξ) :
    a*(∫ t in Ioi ξ, (t-ξ)^(k+1)*t^(b-1)*Real.exp (-a*t)) =
      (k+b-a*ξ)*(∫ t in Ioi ξ, (t-ξ)^k*t^(b-1)*Real.exp (-a*t)) +
      k*ξ*(∫ t in Ioi ξ, (t-ξ)^(k-1)*t^(b-1)*Real.exp (-a*t)) + 0^k*ξ^b*Real.exp (-a*ξ) := by
  set f : ℕ → ℝ → ℝ := fun j t => (t-ξ)^j*t^(b-1)*Real.exp (-a*t) with hf
  have hI : ∀ j, IntegrableOn (f j) (Ioi ξ) := fun j => integrableOn_betaAux_integrand j ha hb hξ
  set G : ℝ → ℝ := fun t => (t-ξ)^k*t^b*Real.exp (-a*t) with hG
  set G' : ℝ → ℝ := fun t => (k+b-a*ξ)*f k t + k*ξ*f (k-1) t - a*f (k+1) t with hG'
  have hderiv : ∀ t ∈ Ioi ξ, HasDerivAt G (G' t) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_le_of_lt hξ ht
    have h1 : HasDerivAt (fun t : ℝ => (t-ξ)^k) (k*(t-ξ)^(k-1)) t := by
      have := (hasDerivAt_pow k (t-ξ)).comp t ((hasDerivAt_id t).sub_const ξ)
      simpa [Function.comp_def] using this
    have h2 := Real.hasDerivAt_rpow_const (x := t) (p := b) (Or.inl ht0.ne')
    have h3 : HasDerivAt (fun t : ℝ => Real.exp (-a*t)) (Real.exp (-a*t) * (-a)) t := by
      simpa using ((hasDerivAt_id t).const_mul (-a)).exp
    convert (h1.mul h2).mul h3 using 1
    simp only [hG', hf, Pi.mul_apply]
    have htb : t^b = t*t^(b-1) := by
      rw [← Real.rpow_one_add' ht0.le (by linarith)]; ring_nf
    rcases k with _ | k
    · push_cast
      linear_combination (a * Real.exp (-a*t)) * htb
    · simp only [Nat.add_sub_cancel]
      push_cast
      linear_combination (-(((k:ℝ)+1)*(t-ξ)^k - a*(t-ξ)^(k+1)) * Real.exp (-a*t)) * htb
  have hcont : ContinuousWithinAt G (Ici ξ) ξ := by
    refine ContinuousAt.continuousWithinAt ?_
    exact ((continuousAt_id.sub continuousAt_const).pow k).mul
      (Real.continuousAt_rpow_const _ _ (Or.inr hb.le)) |>.mul (by fun_prop)
  have hlim : Tendsto G atTop (𝓝 0) := by
    have hT := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k:ℝ)+b) a ha
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT ?_ ?_
    · filter_upwards [eventually_ge_atTop ξ] with t ht
      have : 0 ≤ t - ξ := by linarith
      have ht0 : 0 ≤ t := le_trans hξ ht
      positivity
    · filter_upwards [eventually_gt_atTop ξ] with t ht
      have ht0 : 0 < t := lt_of_le_of_lt hξ ht
      simp only [hG]
      rw [Real.rpow_add ht0, Real.rpow_natCast]
      gcongr
      linarith
  have hint : IntegrableOn G' (Ioi ξ) :=
    (((hI k).const_mul _).add ((hI (k-1)).const_mul _)).sub ((hI (k+1)).const_mul _)
  have hparts := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have e : ∫ t in Ioi ξ, G' t = (k+b-a*ξ)*(∫ t in Ioi ξ, f k t) + k*ξ*(∫ t in Ioi ξ, f (k-1) t) -
      a*(∫ t in Ioi ξ, f (k+1) t) := by
    simp only [hG']
    rw [integral_sub (f := fun t => (k+b-a*ξ)*f k t + k*ξ*f (k-1) t) (g := fun t => a*f (k+1) t)
      (((hI k).const_mul _).add ((hI (k-1)).const_mul _)) ((hI (k+1)).const_mul _),
      integral_add (f := fun t => (k+b-a*ξ)*f k t) (g := fun t => k*ξ*f (k-1) t)
      ((hI k).const_mul _) ((hI (k-1)).const_mul _), integral_const_mul,
      integral_const_mul, integral_const_mul]
  rw [e] at hparts
  simp only [hG, hf, sub_self] at hparts ⊢
  linear_combination -hparts

/-- Identity under the stated parameter and domain assumptions: `a*betaAuxF (k+1) a b
ξ=(k+b-a*ξ)*betaAuxF k a b ξ+k*ξ*betaAuxF (k-1) a b ξ`. -/
@[dlmf 8.18.E4]
theorem betaAuxF_recurrence {a b ξ : ℝ} (ha : 0 < a) (hb : 0 < b) (hξ : 0 ≤ ξ)
    {k : ℕ} (hk : 1 ≤ k) :
    a*betaAuxF (k+1) a b ξ=(k+b-a*ξ)*betaAuxF k a b ξ+k*ξ*betaAuxF (k-1) a b ξ := by
  have h := betaAux_integral_parts k ha hb hξ
  rw [zero_pow (by omega), zero_mul, zero_mul, add_zero] at h
  have hG : Gamma (b:ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hb)
  have h' := congrArg (fun r : ℝ => (r:ℂ)) h
  simp only [ofReal_mul, ofReal_add, ofReal_sub, ofReal_natCast] at h'
  simp only [betaAuxF]
  linear_combination (Gamma (b:ℂ))⁻¹ * h'

/-- The `F₀` integral as an upper incomplete Gamma value, including the endpoint `ξ = 0`. -/
lemma betaAux_integral_zero {a b ξ : ℝ} (ha : 0 < a) (hb : 0 < b) (hξ : 0 ≤ ξ) :
    ((∫ t in Ioi ξ, t^(b-1)*Real.exp (-a*t) : ℝ) : ℂ) =
      (a : ℂ)^(-(b : ℂ))*(Gamma b*regularizedIncompleteGammaQ b (a*ξ)) := by
  have hb0 : (b:ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have hnp : ∀ n : ℕ, (b:ℂ) ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  -- the Gamma-type integral over `Ioi (a ξ)`
  have hQ : Gamma b*regularizedIncompleteGammaQ b (a*ξ) =
      ∫ t in Ioi (a*ξ), (t : ℂ)^((b:ℂ)-1)*Real.exp (-t) := by
    rcases hξ.lt_or_eq with hξ | hξ
    · have hx : 0 < a*ξ := mul_pos ha hξ
      have hz : ((a*ξ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
      rw [show (a:ℂ)*ξ = ((a*ξ : ℝ) : ℂ) by push_cast; ring, regularizedIncompleteGammaQ_eq hnp hz,
        mul_div_cancel₀ _ (Gamma_ne_zero hnp),
            upperIncompleteGamma_eq_integral _ hx]
    · subst hξ
      rw [mul_zero, ofReal_zero, mul_zero, regularizedIncompleteGammaQ, regularizedGamma,
        zero_cpow hb0, zero_mul, sub_zero, mul_one,
        Complex.Gamma_eq_integral (by simpa using hb), Complex.GammaIntegral]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp only [ofReal_exp, ofReal_neg]; ring
  rw [hQ]
  have hsub := integral_comp_mul_left_Ioi (fun t : ℝ => (t : ℂ)^((b:ℂ)-1)*Real.exp (-t)) ξ ha
  rw [show (∫ t in Ioi (a*ξ), (t : ℂ)^((b:ℂ)-1)*Real.exp (-t)) =
      a • ∫ x in Ioi ξ, ((a*x : ℝ) : ℂ)^((b:ℂ)-1)*Real.exp (-(a*x)) by
    rw [hsub, smul_inv_smul₀ ha.ne']]
  rw [← integral_complex_ofReal, Complex.real_smul, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 ≤ t := le_trans hξ (le_of_lt ht)
  rw [ofReal_mul, ofReal_cpow ht0, ofReal_mul, mul_cpow_ofReal_nonneg ha.le ht0,
    show -(a*t) = -a*t by ring]
  have ha0 : (a:ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hab : (a:ℂ)^(-(b:ℂ)) * ((a:ℂ) * (a:ℂ)^((b:ℂ)-1)) = 1 := by
    have e1 : (a:ℂ)*(a:ℂ)^((b:ℂ)-1) = (a:ℂ)^(b:ℂ) := by
      conv_rhs => rw [show (b:ℂ) = 1 + ((b:ℂ)-1) by ring, cpow_add _ _ ha0, cpow_one]
    rw [e1, ← cpow_add _ _ ha0, neg_add_cancel, cpow_zero]
  push_cast
  linear_combination (-((t:ℂ)^((b:ℂ)-1) * cexp (-(a:ℂ)*t))) * hab

/-- Identity under the stated parameter and domain assumptions: `betaAuxF 0 a b ξ=(a : ℂ)^(-(b :
ℂ))*regularizedIncompleteGammaQ b (a*ξ) ∧ betaAuxF 1 a b ξ=(b-a*ξ)/a*betaAuxF 0 a b
ξ+((ξ^b*Real.exp (-a*ξ) : ℝ) : ℂ)/(a*Gamma b)`. -/
@[dlmf 8.18.E5]
theorem betaAuxF_initial {a b ξ : ℝ} (ha : 0 < a) (hb : 0 < b) (hξ : 0 ≤ ξ) :
    betaAuxF 0 a b ξ=(a : ℂ)^(-(b : ℂ))*regularizedIncompleteGammaQ b (a*ξ) ∧
        betaAuxF 1 a b ξ=(b-a*ξ)/a*betaAuxF 0 a b
        ξ+((ξ^b*Real.exp (-a*ξ) : ℝ) : ℂ)/(a*Gamma b) := by
  have hG : Gamma (b:ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hb)
  have ha0 : (a:ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  constructor
  · simp only [betaAuxF, pow_zero, one_mul]
    rw [betaAux_integral_zero ha hb hξ]
    field_simp
  · have h := betaAux_integral_parts 0 ha hb hξ
    simp only [betaAuxF]
    generalize (∫ t in Ioi ξ, (t-ξ)^(0+1)*t^(b-1)*Real.exp (-a*t)) = I1 at h ⊢
    generalize (∫ t in Ioi ξ, (t-ξ)^0*t^(b-1)*Real.exp (-a*t)) = I0 at h ⊢
    generalize (∫ t in Ioi ξ, (t-ξ)^(0-1)*t^(b-1)*Real.exp (-a*t)) = Im at h
    simp only [pow_zero, Nat.cast_zero, zero_mul, zero_add, add_zero, one_mul] at h
    have h' := congrArg (fun r : ℝ => (r:ℂ)) h
    simp only [ofReal_mul, ofReal_add, ofReal_sub] at h' ⊢
    generalize ((ξ ^ b : ℝ) : ℂ) = P at h' ⊢
    generalize ((Real.exp (-a * ξ) : ℝ) : ℂ) = Q at h' ⊢
    field_simp
    linear_combination h'

/-- A real-analytic function is the sum of its Taylor series near the expansion point. -/
theorem IncompleteBetaUniform.hasSum_taylor_of_analyticAt {f : ℝ → ℝ} {ξ : ℝ}
    (hf : AnalyticAt ℝ f ξ) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t-ξ| < r →
      HasSum (fun k : ℕ => iteratedDeriv k f ξ/(k.factorial : ℝ)*(t-ξ)^k) (f t) := by
  obtain ⟨p, R, hp⟩ := hf
  obtain ⟨r, -, hr0, hrR⟩ := ENNReal.lt_iff_exists_real_btwn.mp hp.r_pos
  refine ⟨r, ENNReal.ofReal_pos.mp hr0, fun t ht => ?_⟩
  have hy : t-ξ ∈ Metric.eball (0:ℝ) R := by
    rw [Metric.mem_eball, edist_zero_right]
    refine lt_of_le_of_lt ?_ hrR
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal ht.le
  have h := hp.hasSum_iteratedFDeriv hy
  rw [show ξ + (t-ξ) = t by ring] at h
  refine h.congr_fun fun k => ?_
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  simp [smul_eq_mul, Finset.prod_const]
  ring

end DLMF.Statistical

namespace DLMF.Confluent.IncompleteBetaUniform

open DLMF.Statistical

/-- The incomplete-Beta endpoint generating kernel is real analytic at every real argument. -/
theorem analyticAt_betaGeneratingKernel (b ξ : ℝ) :
    AnalyticAt ℝ (Real.betaGeneratingKernel b) ξ := by
  set h : ℝ → ℝ := fun t => 1-Real.exp (-t)
  set D := dslope h 0
  have hD : ∀ t, 0 < D t := by
    intro t
    simp only [D]
    rcases lt_trichotomy t 0 with ht | ht | ht
    · rw [dslope_of_ne _ ht.ne, slope_def_field]
      simp only [h, neg_zero, Real.exp_zero, sub_self, sub_zero]
      apply div_pos_of_neg_of_neg _ ht
      have : 1 < Real.exp (-t) := Real.one_lt_exp_iff.mpr (by linarith)
      linarith
    · subst ht
      rw [dslope_same]
      have hd : HasDerivAt h (Real.exp (-0)) 0 := by
        have := ((hasDerivAt_neg (0:ℝ)).exp).const_sub 1
        convert this using 1; simp
      rw [hd.deriv]; simp
    · rw [dslope_of_ne _ ht.ne', slope_def_field]
      simp only [h, neg_zero, Real.exp_zero, sub_self, sub_zero]
      apply div_pos _ ht
      have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
  have hK : Real.betaGeneratingKernel b = fun t => Real.exp (Real.log (D t) * (b-1)) := by
    funext t
    rw [← Real.rpow_def_of_pos (hD t)]
    unfold Real.betaGeneratingKernel
    split_ifs with ht
    · subst ht
      have hd : HasDerivAt h (Real.exp (-0)) 0 := by
        have := ((hasDerivAt_neg (0:ℝ)).exp).const_sub 1
        convert this using 1; simp
      simp only [D, dslope_same, hd.deriv]; simp
    · simp only [D]
      rw [dslope_of_ne _ ht, slope_def_field]
      simp [h]
  have ha : AnalyticAt ℝ (Real.betaGeneratingKernel b) ξ := by
    rw [hK]
    have hh : AnalyticAt ℝ h ξ := by
      simp only [h]; fun_prop
    exact analyticAt_rexp.comp (((hh.dslope 0).log (hD ξ)).mul analyticAt_const)
  exact ha

end DLMF.Confluent.IncompleteBetaUniform

namespace DLMF.Statistical

open DLMF.Confluent

/-- Estimate under the stated parameter and domain assumptions: `∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t-ξ| <
r → HasSum (fun k : ℕ => Real.betaGeneratingCoeff b ξ k*(t-ξ)^k) (Real.betaGeneratingKernel b
t)`. -/
@[dlmf 8.18.E6]
theorem Real.betaGenerating_hasSum {b ξ : ℝ} :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t-ξ| < r →
                                      HasSum (fun k : ℕ => Real.betaGeneratingCoeff b ξ k*(t-ξ)^k)
                                      (Real.betaGeneratingKernel b t) := by
  exact IncompleteBetaUniform.hasSum_taylor_of_analyticAt
    (DLMF.Confluent.IncompleteBetaUniform.analyticAt_betaGeneratingKernel b ξ)

/-- Identity under the stated parameter and domain assumptions: `Real.betaGeneratingCoeff b
(Real.betaXi x) 0=((1-x)/Real.betaXi x)^(b-1) ∧ Real.betaGeneratingCoeff b (Real.betaXi x)
1=(x*Real.betaXi x+x-1)/((1-x)*Real.betaXi x)*(b-1)*Real.betaGeneratingCoeff b (Real.betaXi x)
0`. -/
@[dlmf 8.18.E7]
theorem Real.betaGeneratingCoeff_first {b x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    Real.betaGeneratingCoeff b (Real.betaXi x) 0=((1-x)/Real.betaXi x)^(b-1) ∧
        Real.betaGeneratingCoeff b (Real.betaXi x)
        1=(x*Real.betaXi x+x-1)/((1-x)*Real.betaXi x)*(b-1)*Real.betaGeneratingCoeff b
        (Real.betaXi x) 0 := by
  set ξ := Real.betaXi x with hξdef
  have hξ : 0 < ξ := by
    simp only [hξdef, Real.betaXi]; exact neg_pos.mpr (Real.log_neg hx hx1)
  have hex : Real.exp (-ξ) = x := by
    simp only [hξdef, Real.betaXi, neg_neg, Real.exp_log hx]
  have h0 : Real.betaGeneratingCoeff b ξ 0 = ((1-x)/ξ)^(b-1) := by
    simp [Real.betaGeneratingCoeff, Real.betaGeneratingKernel, hξ.ne', hex]
  refine ⟨h0, ?_⟩
  set h : ℝ → ℝ := fun t => (1-Real.exp (-t))/t
  have hK : Real.betaGeneratingKernel b =ᶠ[𝓝 ξ] fun t => h t ^ (b-1) := by
    filter_upwards [eventually_ne_nhds hξ.ne'] with t ht
    simp [Real.betaGeneratingKernel, ht, h]
  have hhd : HasDerivAt h ((Real.exp (-ξ)*ξ - (1-Real.exp (-ξ)))/ξ^2) ξ := by
    have h1 : HasDerivAt (fun t => 1 - Real.exp (-t)) (Real.exp (-ξ)) ξ := by
      have := ((hasDerivAt_neg ξ).exp).const_sub 1
      simpa using this
    have := h1.div (hasDerivAt_id ξ) hξ.ne'
    convert this using 1
    · funext t; simp [h]
    · simp
  have hpos : 0 < h ξ := by
    simp only [h, hex]; exact div_pos (by linarith) hξ
  have hd := (hhd.rpow_const (p := b-1) (Or.inl hpos.ne')).congr_of_eventuallyEq hK
  rw [Real.betaGeneratingCoeff, iteratedDeriv_one, hd.deriv, h0]
  simp only [h, hex]
  have hx1' : (1-x) ≠ 0 := by linarith
  rw [show b-1-1 = (b-1) - 1 by ring, Real.rpow_sub_one (div_pos (by linarith) hξ).ne']
  field_simp
  ring

/-- The removable function `(1-e^{-t})/t` has derivative `-1/2` at the origin. -/
theorem hasDerivAt_one_sub_exp_neg_div_zero :
    HasDerivAt (fun t : ℝ => if t = 0 then 1 else (1-Real.exp (-t))/t) (-1/2) 0 := by
  rw [hasDerivAt_iff_isLittleO]
  refine IsBigO.trans_isLittleO (g := fun t : ℝ => t^2) ?_
    (by simpa using (isLittleO_pow_id (𝕜 := ℝ) one_lt_two))
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) one_pos] with t ht
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
  by_cases h0 : t = 0
  · subst h0; simp
  have hb := Real.exp_bound (x := -t) (by rw [abs_neg]; exact ht.le) (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial, abs_neg] at hb
  norm_num at hb
  simp only [h0, ↓reduceIte, sub_zero, smul_eq_mul, Real.norm_eq_abs, one_mul]
  have ht0 : 0 < |t| := abs_pos.mpr h0
  have : (1 - Real.exp (-t))/t - 1 - t*(-1/2) = -(Real.exp (-t) - (1 + -t + t^2/2))/t := by
    field_simp; ring
  rw [this, abs_div, abs_neg, div_le_iff₀ ht0, abs_pow]
  calc |Real.exp (-t) - (1 + -t + t^2/2)| ≤ |t|^3 * (4/18) := by
        convert hb using 2; ring
    _ ≤ |t|^2 * |t| := by
        have : |t|^3 = |t|^2*|t| := by ring
        rw [this]; nlinarith [sq_nonneg |t|, ht0]

/-- Identity under the stated parameter and domain assumptions: `Real.betaGeneratingCoeff b 0 0=1
∧ Real.betaGeneratingCoeff b 0 1=(1-b)/2`. -/
@[dlmf 8.18.E7]
theorem Real.betaGeneratingCoeff_at_endpoint {b : ℝ} :
    Real.betaGeneratingCoeff b 0 0=1 ∧ Real.betaGeneratingCoeff b 0 1=(1-b)/2 := by
  refine ⟨by simp [Real.betaGeneratingCoeff, Real.betaGeneratingKernel], ?_⟩
  have hK : Real.betaGeneratingKernel b =
      fun t => (if t = 0 then 1 else (1-Real.exp (-t))/t) ^ (b-1) := by
    funext t
    by_cases ht : t = 0 <;> simp [Real.betaGeneratingKernel, ht]
  have hd := hasDerivAt_one_sub_exp_neg_div_zero.rpow_const (p := b-1) (Or.inl (by simp))
  rw [Real.betaGeneratingCoeff, iteratedDeriv_one, hK, hd.deriv]
  simp
  ring

end DLMF.Statistical
