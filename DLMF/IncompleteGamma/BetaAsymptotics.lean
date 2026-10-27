/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.IncompleteGamma.Beta
public import DLMF.IncompleteGamma.UniformAsymptotics

/-!
# Incomplete Beta asymptotic expansions and inverse, DLMF §8.18

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
The fixed-argument expansion uses finite diagonal shifts and a binomial-series
majorant independent of the large positive parameter. Other remaining admissions
are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Statistical

open DLMF.Confluent

/-- Finite diagonal shifts of the incomplete Beta function. -/
theorem normIncBetaI_diagonal_remainder {a b z : ℂ} (ha : ∀ k : ℕ, a+1 ≠ -k)
    (hz : ‖z‖ < 1) (hz0 : z ≠ 0) (N : ℕ) :
    normIncBetaI a b z = normIncBetaI (a+N) (b-N) z +
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
    have hs := normIncBetaI_shift_diagonal (a+N) (b-N) haN hz hz0
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
theorem incBeta_gauss_uniform_bound (b : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a →
      ‖regularizedGaussHG a b (a+1) z‖ ≤ C * ‖1 / Gamma ((a:ℂ)+1)‖ := by
  let g : ℕ → ℝ := fun k => ‖gaussHGCoeff 1 b 1 k * z^k‖
  have hg : Summable g := summable_norm_gaussHGCoeff_mul_pow 1 b 1 hz
  refine ⟨∑' k, g k, tsum_nonneg (fun k => norm_nonneg _), ?_⟩
  intro a ha
  have hden : ∀ k : ℕ, (a:ℂ)+1 ≠ -k := by
    intro k h; have h' := congrArg Complex.re h; simp at h'; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz,
    regularizedGaussHGFun_eq_div_Gamma hden]
  have hF : ₂F₁ (a:ℂ) b ((a:ℂ)+1) z = ∑' k, gaussHGCoeff a b (a+1) k*z^k := by
    rw [ordinaryHypergeometric_eq_tsum]
    simp only [smul_eq_mul]
    apply tsum_congr; intro k
    simp [gaussHGCoeff, poch, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hbd : ∀ k : ℕ, ‖gaussHGCoeff a b (a+1) k*z^k‖ ≤ g k := by
    intro k
    have hpa : ‖poch (a:ℂ) k‖ ≤ ‖poch ((a:ℂ)+1) k‖ := by
      rw [show ((a:ℂ)+1) = ((a+1:ℝ):ℂ) by push_cast; rfl,
        poch, poch, ascPochhammer_eval_ofReal, ascPochhammer_eval_ofReal,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (DLMF.Hypergeometric.ascPochhammer_eval_nonneg ha.le k),
        abs_of_nonneg (DLMF.Hypergeometric.ascPochhammer_eval_nonneg (by linarith) k)]
      exact DLMF.Hypergeometric.ascPochhammer_eval_mono ha.le (by linarith) k
    have hpk : 0 < ‖poch ((a:ℂ)+1) k‖ := norm_pos_iff.mpr (poch_ne_zero_of_not_neg_nat hden k)
    have hfac : (0:ℝ) < k.factorial := by positivity
    have hgk : g k = ‖poch b k‖ * ‖z‖^k / k.factorial := by
      dsimp only [g, gaussHGCoeff]
      rw [poch_nat_one]
      simp only [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
      field_simp
    rw [hgk]
    simp only [gaussHGCoeff, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (mul_pos hpk hfac) hfac]
    nlinarith [mul_le_mul_of_nonneg_right hpa (mul_nonneg (norm_nonneg (poch b k)) (pow_nonneg (norm_nonneg z) k))]
  have hbnd : ‖₂F₁ (a:ℂ) b ((a:ℂ)+1) z‖ ≤ ∑' k, g k := by
    rw [hF]
    exact tsum_of_norm_bounded hg.hasSum hbd
  rw [norm_div, norm_div, norm_one]
  simpa only [div_eq_mul_inv, one_mul] using
    div_le_div_of_nonneg_right hbnd (norm_nonneg (Gamma ((a:ℂ)+1)))


/-- Fixed-argument incomplete-Beta expansion, with a finite shifted remainder. -/
@[dlmf 8.18.E1]
theorem incBeta_large_a_fixed_x {b x : ℝ} (hb : 0 < b) (hx : 0 < x) (hx1 : x < 1) (N : ℕ) :
    IsBigO atTop (fun a : ℝ => normIncBetaI a b x/(Gamma (a+b)*(x : ℂ)^(a : ℂ)*(1-x : ℂ)^((b : ℂ)-1))-∑ k ∈ Finset.range N, ((x : ℂ)/(1-x))^k/(Gamma (a+k+1)*Gamma ((b : ℂ)-k))) (fun a : ℝ => 1/Gamma (a+N+1)) := by
  have hxn : ‖(x:ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hx.le]; exact hx1
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hxne : (x:ℂ) ≠ 1 := by exact_mod_cast hx1.ne
  have hy0 : (1:ℂ)-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxne)
  obtain ⟨C, hC, hbound⟩ := incBeta_gauss_uniform_bound (1-((b:ℂ)-N)) hxn
  set K : ℂ := (x:ℂ)^N/(Gamma ((b:ℂ)-N)*((1:ℂ)-x)^((b:ℂ)-1))
  refine IsBigO.of_bound (‖K‖*C) ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
  have haN : 0 < a+(N:ℝ) := by positivity
  have ha1 : ∀ k : ℕ, (a:ℂ)+1 ≠ -k := by
    intro k h; have h' := congrArg Complex.re h; simp at h'; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hG : Gamma ((a:ℂ)+b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using add_pos ha hb)
  have hX : (x:ℂ)^(a:ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  have hY : ((1:ℂ)-x)^((b:ℂ)-1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hy0)
  have hP : Gamma ((a:ℂ)+b)*(x:ℂ)^(a:ℂ)*((1:ℂ)-x)^((b:ℂ)-1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hG hX) hY
  have hd := normIncBetaI_diagonal_remainder (a := (a:ℂ)) (b := (b:ℂ)) ha1 hxn hx0 N
  have he : normIncBetaI (a:ℂ) b x/(Gamma (a+b)*(x:ℂ)^(a:ℂ)*((1:ℂ)-x)^((b:ℂ)-1)) -
      ∑ k ∈ Finset.range N, ((x:ℂ)/(1-x))^k/(Gamma (a+k+1)*Gamma ((b:ℂ)-k)) =
      normIncBetaI ((a:ℂ)+N) ((b:ℂ)-N) x /
        (Gamma ((a:ℂ)+b)*(x:ℂ)^(a:ℂ)*((1:ℂ)-x)^((b:ℂ)-1)) := by
    rw [hd, add_div, mul_div_cancel_left₀ _ hP]
    ring
  rw [he]
  have hr : normIncBetaI ((a:ℂ)+N) ((b:ℂ)-N) x /
      (Gamma ((a:ℂ)+b)*(x:ℂ)^(a:ℂ)*((1:ℂ)-x)^((b:ℂ)-1)) =
      K*regularizedGaussHG ((a:ℂ)+N) (1-((b:ℂ)-N)) ((a:ℂ)+N+1) x := by
    rw [normIncBetaI, if_neg hxne,
      show ((a:ℂ)+N)+((b:ℂ)-N) = (a:ℂ)+b by ring,
      cpow_add _ _ hx0, cpow_natCast]
    dsimp only [K]
    by_cases hGb : Gamma ((b:ℂ)-N) = 0
    · simp [hGb]
    · field_simp
  rw [hr, norm_mul]
  have hB := hbound (a+N) haN
  simp only [Complex.ofReal_add, Complex.ofReal_natCast] at hB
  calc ‖K‖*‖regularizedGaussHG ((a:ℂ)+N) (1-((b:ℂ)-N)) ((a:ℂ)+N+1) x‖ ≤
      ‖K‖*(C*‖1/Gamma ((a:ℂ)+N+1)‖) := mul_le_mul_of_nonneg_left hB (norm_nonneg _)
    _ = _ := by ring


/-- incBeta large a integer b exact. -/
@[dlmf 8.18.E1]
theorem incBeta_large_a_integer_b_exact {a : ℝ} (ha : 0 < a) {b N : ℕ} (hb : 1 ≤ b) (hN : b ≤ N) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    normIncBetaI a b x=Gamma (a+b)*(x : ℂ)^(a : ℂ)*(1-x : ℂ)^((b : ℂ)-1)*(∑ k ∈ Finset.range N, ((x : ℂ)/(1-x))^k/(Gamma (a+k+1)*Gamma ((b : ℂ)-k))) := by
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
    have h1 := normIncBetaI_ofReal (a := (a:ℂ)) (b := 1) (by simpa using ha) (by norm_num)
      (x := x) ⟨hx.le, hx1.le⟩
    rw [Nat.cast_one, h1, Real.normIncBetaI_one_right (by simpa using ha)]
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
      intro h; have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg b : (0:ℝ) ≤ b)]
    have hsh := normIncBetaI_shift_right (a:ℂ) b ha1 hab hxn hx0
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
    have hB : ((a:ℂ)+b) * S (b+1) = S b + ∑ k ∈ Finset.range (M+1), R^k*(G (a+k)*G (((b+1:ℕ):ℂ)-k)) := by
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
    have hsh' : normIncBetaI (a:ℂ) ((b+1:ℕ):ℂ) X = normIncBetaI a b X +
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
    integrableOn_rpow_mul_exp_neg_mul_rpow (by have := (Nat.cast_nonneg k : (0:ℝ) ≤ k); linarith) one_pos ha
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

/-- betaAuxF recurrence. -/
@[dlmf 8.18.E4]
theorem betaAuxF_recurrence {a b ξ : ℝ} (ha : 0 < a) (hb : 0 < b) (hξ : 0 ≤ ξ) {k : ℕ} (hk : 1 ≤ k) :
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
      (a : ℂ)^(-(b : ℂ))*(Gamma b*normIncGammaQContinued b (a*ξ)) := by
  have hb0 : (b:ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have hnp : ∀ n : ℕ, (b:ℂ) ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  -- the Gamma-type integral over `Ioi (a ξ)`
  have hQ : Gamma b*normIncGammaQContinued b (a*ξ) =
      ∫ t in Ioi (a*ξ), (t : ℂ)^((b:ℂ)-1)*Real.exp (-t) := by
    rcases hξ.lt_or_eq with hξ | hξ
    · have hx : 0 < a*ξ := mul_pos ha hξ
      have hz : ((a*ξ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
      rw [show (a:ℂ)*ξ = ((a*ξ : ℝ) : ℂ) by push_cast; ring, normIncGammaQContinued_eq hnp hz,
        normIncGammaQ, mul_div_cancel₀ _ (Gamma_ne_zero hnp), upperIncGamma_eq_integral _ hx]
    · subst hξ
      rw [mul_zero, ofReal_zero, mul_zero, normIncGammaQContinued, normIncGammaPContinued,
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

/-- betaAuxF initial. -/
@[dlmf 8.18.E5]
theorem betaAuxF_initial {a b ξ : ℝ} (ha : 0 < a) (hb : 0 < b) (hξ : 0 ≤ ξ) :
    betaAuxF 0 a b ξ=(a : ℂ)^(-(b : ℂ))*normIncGammaQContinued b (a*ξ) ∧ betaAuxF 1 a b ξ=(b-a*ξ)/a*betaAuxF 0 a b ξ+((ξ^b*Real.exp (-a*ξ) : ℝ) : ℂ)/(a*Gamma b) := by
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
theorem incG_hasSum_taylor_of_analyticAt {f : ℝ → ℝ} {ξ : ℝ} (hf : AnalyticAt ℝ f ξ) :
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

/-- Real.betaGenerating hasSum. -/
@[dlmf 8.18.E6]
theorem Real.betaGenerating_hasSum {b ξ : ℝ} (hb : 0 < b) (hξ : 0 ≤ ξ) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t-ξ| < r → HasSum (fun k : ℕ => Real.betaGeneratingCoeff b ξ k*(t-ξ)^k) (Real.betaGeneratingKernel b t) := by
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
  exact incG_hasSum_taylor_of_analyticAt ha

/-- Real.betaGeneratingCoeff first. -/
@[dlmf 8.18.E7]
theorem Real.betaGeneratingCoeff_first {b x : ℝ} (hb : 0 < b) (hx : 0 < x) (hx1 : x < 1) :
    Real.betaGeneratingCoeff b (Real.betaXi x) 0=((1-x)/Real.betaXi x)^(b-1) ∧ Real.betaGeneratingCoeff b (Real.betaXi x) 1=(x*Real.betaXi x+x-1)/((1-x)*Real.betaXi x)*(b-1)*Real.betaGeneratingCoeff b (Real.betaXi x) 0 := by
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

/-- Real.betaGeneratingCoeff at endpoint. -/
@[dlmf 8.18.E7]
theorem Real.betaGeneratingCoeff_at_endpoint {b : ℝ} (hb : 0 < b) :
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

/-- incBeta large a uniform. -/
@[dlmf 8.18.E3]
theorem incBeta_large_a_uniform {b : ℝ} (hb : 0 < b) (N : ℕ) :
    IsBigO (comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1}) (fun p => Gamma p.1/Gamma (p.1+b)*normIncBetaI p.1 b p.2-∑ k ∈ Finset.range N, Real.betaGeneratingCoeff b (Real.betaXi p.2) k*betaAuxF k p.1 b (Real.betaXi p.2)) (fun p => (p.1 : ℂ)^(-(N : ℤ))*betaAuxF 0 p.1 b (Real.betaXi p.2)) := by
  sorry

/-- The transition center x₀. -/
@[dlmf 8.18.E8]
def Real.betaCenter (a b : ℝ) : ℝ :=
  a/(a+b)

/-- The signed transition variable, continuous with η/(x-x₀)>0. -/
@[dlmf 8.18.E10]
def Real.betaEta (x₀ x : ℝ) : ℝ :=
  (if x < x₀ then -1 else 1)*Real.sqrt (-2*(x₀*Real.log (x/x₀)+(1-x₀)*Real.log ((1-x)/(1-x₀))))

/-- The real inverse of the monotone signed transition map. -/
def Real.betaEtaInverse (x₀ η : ℝ) : ℝ :=
  Classical.epsilon (fun x : ℝ => 0 < x ∧ x < 1 ∧ Real.betaEta x₀ x=η)

/-- Real.betaEta equation. -/
@[dlmf 8.18.E10]
theorem Real.betaEta_equation {x₀ x : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hx : 0 < x) (hx1 : x < 1) :
    -Real.betaEta x₀ x^2/2=x₀*Real.log (x/x₀)+(1-x₀)*Real.log ((1-x)/(1-x₀)) ∧ (x ≠ x₀ → 0 < Real.betaEta x₀ x/(x-x₀)) := by
  set L := x₀*Real.log (x/x₀)+(1-x₀)*Real.log ((1-x)/(1-x₀)) with hL
  have h1 : 0 < x/x₀ := div_pos hx hx₀
  have h2 : 0 < (1-x)/(1-x₀) := div_pos (by linarith) (by linarith)
  have hsum : x₀*(x/x₀-1)+(1-x₀)*((1-x)/(1-x₀)-1) = 0 := by
    field_simp; ring
  have hLle : L ≤ 0 := by
    have e1 := Real.log_le_sub_one_of_pos h1
    have e2 := Real.log_le_sub_one_of_pos h2
    have : x₀*Real.log (x/x₀) ≤ x₀*(x/x₀-1) := mul_le_mul_of_nonneg_left e1 hx₀.le
    have : (1-x₀)*Real.log ((1-x)/(1-x₀)) ≤ (1-x₀)*((1-x)/(1-x₀)-1) :=
      mul_le_mul_of_nonneg_left e2 (by linarith)
    linarith
  have hsq : Real.betaEta x₀ x^2 = -2*L := by
    rw [Real.betaEta, mul_pow, Real.sq_sqrt (by linarith)]
    split_ifs <;> ring
  refine ⟨by rw [hsq]; ring, fun hne => ?_⟩
  have hLlt : L < 0 := by
    have hne1 : x/x₀ ≠ 1 := by
      intro h; apply hne; field_simp at h; linarith
    have e1 := Real.log_lt_sub_one_of_pos h1 hne1
    have e2 := Real.log_le_sub_one_of_pos h2
    have : x₀*Real.log (x/x₀) < x₀*(x/x₀-1) := mul_lt_mul_of_pos_left e1 hx₀
    have : (1-x₀)*Real.log ((1-x)/(1-x₀)) ≤ (1-x₀)*((1-x)/(1-x₀)-1) :=
      mul_le_mul_of_nonneg_left e2 (by linarith)
    linarith
  have hs : 0 < Real.sqrt (-2*L) := Real.sqrt_pos.mpr (by linarith)
  rw [Real.betaEta, ← hL]
  rcases lt_or_gt_of_ne hne with h | h
  · simp only [h, ↓reduceIte]
    exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · simp only [not_lt.mpr h.le, ↓reduceIte]
    exact div_pos (by linarith) (by linarith)

/-- The radicand of the transition map is continuous on `(0,1)`. -/
theorem incG_betaEta_sqrt_continuousOn {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) :
    ContinuousOn (fun x : ℝ => Real.sqrt (-2*(x₀*Real.log (x/x₀)+(1-x₀)*Real.log ((1-x)/(1-x₀)))))
      (Ioo 0 1) := by
  refine Real.continuous_sqrt.comp_continuousOn (ContinuousOn.mul continuousOn_const ?_)
  refine ContinuousOn.add (continuousOn_const.mul ?_) (continuousOn_const.mul ?_)
  · exact Real.continuousOn_log.comp (continuousOn_id.div_const _) fun x hx =>
      (div_pos hx.1 hx₀).ne'
  · exact Real.continuousOn_log.comp ((continuousOn_const.sub continuousOn_id).div_const _)
      fun x hx => (div_pos (by linarith [hx.2]) (by linarith)).ne'

/-- Every real value is taken by the transition map on `(0,1)`. -/
theorem incG_betaEta_exists {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (η : ℝ) :
    ∃ x : ℝ, 0 < x ∧ x < 1 ∧ Real.betaEta x₀ x = η := by
  set g : ℝ → ℝ := fun x => Real.sqrt (-2*(x₀*Real.log (x/x₀)+(1-x₀)*Real.log ((1-x)/(1-x₀))))
  have hg := incG_betaEta_sqrt_continuousOn hx₀ hx₀1
  have hgx₀ : g x₀ = 0 := by simp [g, div_self hx₀.ne', div_self (show 1-x₀ ≠ 0 by linarith)]
  have hE : ∀ x, Real.betaEta x₀ x = (if x < x₀ then -1 else 1) * g x := fun x => rfl
  have hl0 : Real.log x₀ < 0 := Real.log_neg hx₀ hx₀1
  have hl1 : Real.log (1-x₀) < 0 := Real.log_neg (by linarith) (by linarith)
  rcases lt_trichotomy η 0 with hη | hη | hη
  · -- left branch
    set M : ℝ := (η^2-2*(1-x₀)*Real.log (1-x₀))/(2*x₀)+1
    have hM : 0 < M := by
      have : 0 ≤ (η^2-2*(1-x₀)*Real.log (1-x₀))/(2*x₀) := by
        apply div_nonneg _ (by linarith); nlinarith
      linarith
    set x₁ := x₀*Real.exp (-M)
    have he : Real.exp (-M) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hx₁0 : 0 < x₁ := by positivity
    have hx₁ : x₁ < x₀ := by nlinarith
    have hgx₁ : -η ≤ g x₁ := by
      have hq : Real.log (x₁/x₀) = -M := by
        rw [show x₁/x₀ = Real.exp (-M) by simp only [x₁]; field_simp]; exact Real.log_exp _
      have hr : Real.log ((1-x₁)/(1-x₀)) ≤ -Real.log (1-x₀) := by
        rw [Real.log_div (by linarith) (by linarith)]
        have : Real.log (1-x₁) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
        linarith
      have hrad : η^2 ≤ -2*(x₀*Real.log (x₁/x₀)+(1-x₀)*Real.log ((1-x₁)/(1-x₀))) := by
        rw [hq]
        have : (1-x₀)*Real.log ((1-x₁)/(1-x₀)) ≤ (1-x₀)*(-Real.log (1-x₀)) :=
          mul_le_mul_of_nonneg_left hr (by linarith)
        have hMx : 2*x₀*M = η^2-2*(1-x₀)*Real.log (1-x₀) + 2*x₀ := by
          simp only [M]; field_simp
        nlinarith
      calc -η = Real.sqrt (η^2) := by rw [Real.sqrt_sq_eq_abs, abs_of_neg hη]
        _ ≤ g x₁ := Real.sqrt_le_sqrt hrad
    have hc : ContinuousOn (fun x => -g x) (Icc x₁ x₀) :=
      (hg.mono fun x (hx : x ∈ Icc x₁ x₀) => ⟨lt_of_lt_of_le hx₁0 hx.1, lt_of_le_of_lt hx.2 hx₀1⟩).neg
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hx₁.le hc
      (show η ∈ Icc (-g x₁) (-g x₀) by rw [hgx₀]; constructor <;> linarith)
    have hxx : x < x₀ := by
      rcases hx.2.lt_or_eq with h | h
      · exact h
      · simp only at hfx; rw [h, hgx₀] at hfx; linarith
    refine ⟨x, lt_of_lt_of_le hx₁0 hx.1, by linarith [hx.2], ?_⟩
    rw [hE]; simp only [hxx, ↓reduceIte]; simp only at hfx; linarith
  · subst hη
    exact ⟨x₀, hx₀, hx₀1, by rw [hE, hgx₀]; ring⟩
  · -- right branch
    set M : ℝ := (η^2-2*x₀*Real.log x₀)/(2*(1-x₀))+1
    have hM : 0 < M := by
      have : 0 ≤ (η^2-2*x₀*Real.log x₀)/(2*(1-x₀)) := by
        apply div_nonneg _ (by linarith); nlinarith
      linarith
    set x₁ := 1-(1-x₀)*Real.exp (-M)
    have he : Real.exp (-M) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hep : 0 < Real.exp (-M) := Real.exp_pos _
    have hx₁1 : x₁ < 1 := by have : 0 < (1-x₀)*Real.exp (-M) := by nlinarith
                             linarith
    have hx₁ : x₀ < x₁ := by nlinarith
    have hgx₁ : η ≤ g x₁ := by
      have hq : Real.log ((1-x₁)/(1-x₀)) = -M := by
        rw [show (1-x₁)/(1-x₀) = Real.exp (-M) by simp only [x₁]; field_simp; ring]; exact Real.log_exp _
      have hr : Real.log (x₁/x₀) ≤ -Real.log x₀ := by
        rw [Real.log_div (by linarith) (by linarith)]
        have : Real.log x₁ ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
        linarith
      have hrad : η^2 ≤ -2*(x₀*Real.log (x₁/x₀)+(1-x₀)*Real.log ((1-x₁)/(1-x₀))) := by
        rw [hq]
        have : x₀*Real.log (x₁/x₀) ≤ x₀*(-Real.log x₀) := mul_le_mul_of_nonneg_left hr hx₀.le
        have hMx : 2*(1-x₀)*M = η^2-2*x₀*Real.log x₀ + 2*(1-x₀) := by
          simp only [M]; field_simp
        nlinarith
      calc η = Real.sqrt (η^2) := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hη]
        _ ≤ g x₁ := Real.sqrt_le_sqrt hrad
    have hc : ContinuousOn g (Icc x₀ x₁) :=
      hg.mono fun x (hx : x ∈ Icc x₀ x₁) => ⟨lt_of_lt_of_le hx₀ hx.1, lt_of_le_of_lt hx.2 hx₁1⟩
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hx₁.le hc
      (show η ∈ Icc (g x₀) (g x₁) by rw [hgx₀]; constructor <;> linarith)
    refine ⟨x, lt_of_lt_of_le hx₀ hx.1, lt_of_le_of_lt hx.2 hx₁1, ?_⟩
    rw [hE]; simp only [not_lt.mpr hx.1, ↓reduceIte, one_mul]; exact hfx

/-- Real.betaEtaInverse spec. -/
@[dlmf 8.18.E10]
theorem Real.betaEtaInverse_spec {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (η : ℝ) :
    0 < Real.betaEtaInverse x₀ η ∧ Real.betaEtaInverse x₀ η < 1 ∧ Real.betaEta x₀ (Real.betaEtaInverse x₀ η)=η := by
  exact Classical.epsilon_spec (incG_betaEta_exists hx₀ hx₀1 η)

/-- The symmetric coefficients c_k(η), with x₀ retained as a parameter. -/
def betaSymmetricC (k : ℕ) (x₀ η : ℝ) : ℂ :=
  (-1 : ℂ)^k*asymptoticCoeff (fun t : ℝ => let x := Real.betaEtaInverse x₀ η; Real.sqrt (2*π*t)*Real.exp (t*η^2/2)*(normIncBetaI (t*x₀) (t*(1-x₀)) x-DLMF.Confluent.erfc (-η*Real.sqrt (t/2))/2)) k

/-- betaSymmetricC first. -/
@[dlmf 8.18.E11]
theorem betaSymmetricC_first {x₀ η : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hη : η ≠ 0) :
    betaSymmetricC 0 x₀ η=(1/η-Real.sqrt (x₀*(1-x₀))/(Real.betaEtaInverse x₀ η-x₀) : ℝ) := by
  sorry

/-- betaSymmetricC at zero. -/
@[dlmf 8.18.E12]
theorem betaSymmetricC_at_zero {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) :
    betaSymmetricC 0 x₀ 0=((1-2*x₀)/(3*Real.sqrt (x₀*(1-x₀))) : ℝ) := by
  sorry

/-- The removable singularities of all c_k at η=0. -/
theorem betaSymmetricC_analytic (k : ℕ) {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) :
    AnalyticAt ℝ (betaSymmetricC k x₀) 0 := by
  sorry

/-- incBeta symmetric uniform expansion. -/
@[dlmf 8.18.E9]
theorem incBeta_symmetric_uniform_expansion {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1/2) (N : ℕ) :
    IsBigO (comap (fun p : ℝ × ℝ × ℝ => p.1) atTop ⊓ 𝓟 {p : ℝ × ℝ × ℝ | 0 < p.1 ∧ δ ≤ p.2.1 ∧ p.2.1 ≤ 1-δ ∧ 0 < p.2.2 ∧ p.2.2 < 1}) (fun p => let η := Real.betaEta p.2.1 p.2.2; Real.sqrt (2*π*p.1)*Real.exp (p.1*η^2/2)*(normIncBetaI (p.1*p.2.1) (p.1*(1-p.2.1)) p.2.2-DLMF.Confluent.erfc (-η*Real.sqrt (p.1/2))/2)-∑ k ∈ Finset.range N, (-1 : ℂ)^k*betaSymmetricC k p.2.1 η/(p.1 : ℂ)^k) (fun p => p.1^(-(N : ℤ))) := by
  sorry

/-- The general-case transition variable ζ with its required branch. -/
@[dlmf 8.18.E15]
def Real.betaZeta (μ x : ℝ) : ℝ :=
  if x=1/(1+μ) then μ else Classical.epsilon (fun ζ : ℝ => 0 < ζ ∧ μ*Real.log ζ-ζ=Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ ∧ 0 < (ζ-μ)/(1/(1+μ)-x))

/-- The inverse real transition map. -/
def Real.betaGeneralX (μ ζ : ℝ) : ℝ :=
  if ζ=μ then 1/(1+μ) else Classical.epsilon (fun x : ℝ => 0 < x ∧ x < 1 ∧ μ*Real.log ζ-ζ=Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ ∧ 0 < (ζ-μ)/(1/(1+μ)-x))

/-- `ζ ↦ μ log ζ - ζ` increases strictly on `(0, μ]`. -/
theorem incG_betaPhi_strictMonoOn (μ : ℝ) :
    StrictMonoOn (fun ζ : ℝ => μ*Real.log ζ-ζ) (Ioc 0 μ) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioc 0 μ) ?_ ?_
  · intro ζ hζ
    exact ((continuousAt_const.mul (Real.continuousAt_log hζ.1.ne')).sub
      continuousAt_id).continuousWithinAt
  · intro ζ hζ
    rw [interior_Ioc] at hζ
    have hd : HasDerivAt (fun ζ : ℝ => μ*Real.log ζ-ζ) (μ*ζ⁻¹-1) ζ :=
      ((Real.hasDerivAt_log hζ.1.ne').const_mul μ).sub (hasDerivAt_id ζ)
    rw [hd.deriv, sub_pos, ← div_eq_mul_inv, one_lt_div hζ.1]; exact hζ.2

/-- `ζ ↦ μ log ζ - ζ` decreases strictly on `[μ, ∞)`. -/
theorem incG_betaPhi_strictAntiOn {μ : ℝ} (hμ : 0 < μ) :
    StrictAntiOn (fun ζ : ℝ => μ*Real.log ζ-ζ) (Ici μ) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici μ) ?_ ?_
  · intro ζ hζ
    exact ((continuousAt_const.mul (Real.continuousAt_log (by
      have : μ ≤ ζ := hζ; linarith : (0:ℝ) < ζ).ne')).sub continuousAt_id).continuousWithinAt
  · intro ζ hζ
    rw [interior_Ici] at hζ
    have hζ0 : 0 < ζ := hμ.trans hζ
    have hd : HasDerivAt (fun ζ : ℝ => μ*Real.log ζ-ζ) (μ*ζ⁻¹-1) ζ :=
      ((Real.hasDerivAt_log hζ0.ne').const_mul μ).sub (hasDerivAt_id ζ)
    rw [hd.deriv, sub_neg, ← div_eq_mul_inv, div_lt_one hζ0]; exact hζ

theorem incG_betaR_hasDerivAt {μ x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun x : ℝ => Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ)
      (x⁻¹ - μ*(1-x)⁻¹) x := by
  have h1 := Real.hasDerivAt_log hx.ne'
  have h2 := ((hasDerivAt_id x).const_sub 1).log (by simp; linarith)
  have := ((h1.add (h2.const_mul μ)).add_const ((1+μ)*Real.log (1+μ))).sub_const μ
  convert this using 1
  · funext y; simp only [Pi.add_apply, id]
  · simp only [id]; rw [neg_div, one_div]; ring

theorem incG_betaR_continuousAt {μ x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ContinuousAt (fun x : ℝ => Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ) x :=
  (incG_betaR_hasDerivAt hx hx1).continuousAt

/-- `R` increases strictly on `(0, 1/(1+μ)]`. -/
theorem incG_betaR_strictMonoOn {μ : ℝ} (hμ : 0 < μ) :
    StrictMonoOn (fun x : ℝ => Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ)
      (Ioc 0 (1/(1+μ))) := by
  have hx0 : 1/(1+μ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  refine strictMonoOn_of_deriv_pos (convex_Ioc _ _) ?_ ?_
  · intro x hx
    exact (incG_betaR_continuousAt hx.1 (hx.2.trans_lt hx0)).continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    have h1 : x < 1 := hx.2.trans hx0
    rw [(incG_betaR_hasDerivAt hx.1 h1).deriv]
    have hlt : x*(1+μ) < 1 := by have h := hx.2; rw [lt_div_iff₀ (by linarith)] at h; linarith
    have : 0 < 1 - x := by linarith
    rw [sub_pos, ← div_eq_mul_inv, ← one_div, div_lt_div_iff₀ this hx.1]; nlinarith

/-- `R` decreases strictly on `[1/(1+μ), 1)`. -/
theorem incG_betaR_strictAntiOn {μ : ℝ} (hμ : 0 < μ) :
    StrictAntiOn (fun x : ℝ => Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ)
      (Ico (1/(1+μ)) 1) := by
  have hx0 : 0 < 1/(1+μ) := by positivity
  refine strictAntiOn_of_deriv_neg (convex_Ico _ _) ?_ ?_
  · intro x hx
    exact (incG_betaR_continuousAt (hx0.trans_le hx.1) hx.2).continuousWithinAt
  · intro x hx
    rw [interior_Ico] at hx
    have h0 : 0 < x := hx0.trans hx.1
    rw [(incG_betaR_hasDerivAt h0 hx.2).deriv]
    have hgt : 1 < x*(1+μ) := by have h := hx.1; rw [div_lt_iff₀ (by linarith)] at h; linarith
    have : 0 < 1 - x := by linarith [hx.2]
    rw [sub_neg, ← div_eq_mul_inv, ← one_div, div_lt_div_iff₀ h0 this]; nlinarith

/-- The two sides agree at the turning points. -/
theorem incG_betaR_turning {μ : ℝ} (hμ : 0 < μ) :
    Real.log (1/(1+μ))+μ*Real.log (1-1/(1+μ))+(1+μ)*Real.log (1+μ)-μ = μ*Real.log μ-μ := by
  have h1 : (1:ℝ) - 1/(1+μ) = μ/(1+μ) := by field_simp; ring
  rw [h1, one_div, Real.log_inv, Real.log_div hμ.ne' (by linarith)]; ring

/-- Existence of the transition variable on the correct side. -/
theorem incG_betaZeta_exists {μ x : ℝ} (hμ : 0 < μ) (hx : 0 < x) (hx1 : x < 1)
    (hne : x ≠ 1/(1+μ)) :
    ∃ ζ : ℝ, 0 < ζ ∧ μ*Real.log ζ-ζ=Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ ∧
      0 < (ζ-μ)/(1/(1+μ)-x) := by
  set R := Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ with hR
  have hx0 : 0 < 1/(1+μ) := by positivity
  have hx01 : 1/(1+μ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hRlt : R < μ*Real.log μ-μ := by
    rw [← incG_betaR_turning hμ]
    rcases lt_or_gt_of_ne hne with h | h
    · exact incG_betaR_strictMonoOn hμ ⟨hx, h.le⟩ ⟨hx0, le_rfl⟩ h
    · exact incG_betaR_strictAntiOn hμ ⟨le_rfl, hx01⟩ ⟨h.le, hx1⟩ h
  rcases lt_or_gt_of_ne hne with h | h
  · -- ζ > μ
    set s : ℝ := 2*μ + |R| + 1
    have hs : 0 < s := by positivity
    have hμs : μ ≤ s^2 := by nlinarith [abs_nonneg R]
    have hφs : μ*Real.log (s^2) - s^2 ≤ R := by
      have hl : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs
      rw [Real.log_pow]; push_cast
      have : -|R| ≤ R := neg_abs_le R
      nlinarith [abs_nonneg R]
    have hcont : ContinuousOn (fun ζ : ℝ => μ*Real.log ζ-ζ) (Icc μ (s^2)) := fun ζ hζ =>
      ((continuousAt_const.mul (Real.continuousAt_log (by linarith [hζ.1] : (0:ℝ) < ζ).ne')).sub
        continuousAt_id).continuousWithinAt
    obtain ⟨ζ, hζ, hζR⟩ := intermediate_value_Icc' hμs hcont ⟨hφs, hRlt.le⟩
    have hζμ : ζ ≠ μ := by rintro rfl; simp only at hζR; linarith
    have hgt : μ < ζ := lt_of_le_of_ne hζ.1 (Ne.symm hζμ)
    exact ⟨ζ, hμ.trans hgt, hζR, div_pos (by linarith) (by linarith)⟩
  · -- ζ < μ
    set e : ℝ := Real.exp (R/μ)
    have he : 0 < e := Real.exp_pos _
    have heμ : e < μ := by
      rw [← Real.exp_log hμ]; refine Real.exp_lt_exp.mpr ?_
      rw [div_lt_iff₀ hμ]; nlinarith
    have hφe : μ*Real.log e - e ≤ R := by
      rw [Real.log_exp]; field_simp; linarith
    have hcont : ContinuousOn (fun ζ : ℝ => μ*Real.log ζ-ζ) (Icc e μ) := fun ζ hζ =>
      ((continuousAt_const.mul (Real.continuousAt_log (by linarith [hζ.1] : (0:ℝ) < ζ).ne')).sub
        continuousAt_id).continuousWithinAt
    obtain ⟨ζ, hζ, hζR⟩ := intermediate_value_Icc heμ.le hcont ⟨hφe, hRlt.le⟩
    have hζμ : ζ ≠ μ := by rintro rfl; simp only at hζR; linarith
    have hlt : ζ < μ := lt_of_le_of_ne hζ.2 hζμ
    exact ⟨ζ, he.trans_le hζ.1, hζR, div_pos_of_neg_of_neg (by linarith) (by linarith)⟩

theorem incG_betaZeta_spec {μ x : ℝ} (hμ : 0 < μ) (hx : 0 < x) (hx1 : x < 1) :
    0 < Real.betaZeta μ x ∧ μ*Real.log (Real.betaZeta μ x)-Real.betaZeta μ x=Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ ∧ Real.betaGeneralX μ (Real.betaZeta μ x)=x ∧ (x ≠ 1/(1+μ) → 0 < (Real.betaZeta μ x-μ)/(1/(1+μ)-x)) := by
  have hx0 : 0 < 1/(1+μ) := by positivity
  have hx01 : 1/(1+μ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  by_cases hne : x = 1/(1+μ)
  · have hz : Real.betaZeta μ x = μ := by simp [Real.betaZeta, hne]
    rw [hz]
    refine ⟨hμ, ?_, by simp [Real.betaGeneralX, hne], fun h => absurd hne h⟩
    rw [hne, incG_betaR_turning hμ]
  have hspec := Classical.epsilon_spec (incG_betaZeta_exists hμ hx hx1 hne)
  have hz : Real.betaZeta μ x = Classical.epsilon (fun ζ : ℝ => 0 < ζ ∧ μ*Real.log ζ-ζ=Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ ∧ 0 < (ζ-μ)/(1/(1+μ)-x)) := by
    simp only [Real.betaZeta, hne, ↓reduceIte]
  rw [← hz] at hspec
  obtain ⟨hζ0, hζR, hsign⟩ := hspec
  set ζ := Real.betaZeta μ x
  refine ⟨hζ0, hζR, ?_, fun _ => hsign⟩
  have hζμ : ζ ≠ μ := by rintro h; rw [h, sub_self, zero_div] at hsign; exact lt_irrefl _ hsign
  have hX : Real.betaGeneralX μ ζ = Classical.epsilon (fun x : ℝ => 0 < x ∧ x < 1 ∧ μ*Real.log ζ-ζ=Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ ∧ 0 < (ζ-μ)/(1/(1+μ)-x)) := by
    simp only [Real.betaGeneralX, hζμ, ↓reduceIte]
  have hex : ∃ y : ℝ, 0 < y ∧ y < 1 ∧ μ*Real.log ζ-ζ=Real.log y+μ*Real.log (1-y)+(1+μ)*Real.log (1+μ)-μ ∧ 0 < (ζ-μ)/(1/(1+μ)-y) :=
    ⟨x, hx, hx1, hζR, hsign⟩
  obtain ⟨hy0, hy1, hyR, hysign⟩ := Classical.epsilon_spec hex
  rw [hX]
  set y := Classical.epsilon (fun x : ℝ => 0 < x ∧ x < 1 ∧ μ*Real.log ζ-ζ=Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ ∧ 0 < (ζ-μ)/(1/(1+μ)-x))
  have hRR : (fun x : ℝ => Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ) y =
      (fun x : ℝ => Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ) x := by
    simp only; rw [← hyR, hζR]
  rcases div_pos_iff.mp hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h2' : 0 < 1/(1+μ) - y := by
      rcases div_pos_iff.mp hysign with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · linarith
    exact (incG_betaR_strictMonoOn hμ).injOn ⟨hy0, by linarith⟩ ⟨hx, by linarith⟩ hRR
  · have h2' : 1/(1+μ) - y < 0 := by
      rcases div_pos_iff.mp hysign with ⟨h, _⟩ | ⟨_, h⟩
      · linarith
      · exact h
    exact (incG_betaR_strictAntiOn hμ).injOn ⟨by linarith, hy1⟩ ⟨by linarith, hx1⟩ hRR

/-- Real.betaZeta spec. -/
@[dlmf 8.18.E15]
theorem Real.betaZeta_spec {μ x : ℝ} (hμ : 0 < μ) (hx : 0 < x) (hx1 : x < 1) :
    0 < Real.betaZeta μ x ∧ μ*Real.log (Real.betaZeta μ x)-Real.betaZeta μ x=Real.log x+μ*Real.log (1-x)+(1+μ)*Real.log (1+μ)-μ ∧ Real.betaGeneralX μ (Real.betaZeta μ x)=x ∧ (x ≠ 1/(1+μ) → 0 < (Real.betaZeta μ x-μ)/(1/(1+μ)-x)) :=
  incG_betaZeta_spec hμ hx hx1

/-- The general coefficients h_k(ζ,μ) extracted from the exact normalized remainder. -/
def betaGeneralH (k : ℕ) (ζ μ : ℝ) : ℂ :=
  asymptoticCoeff (fun a : ℝ => let x := Real.betaGeneralX μ ζ; let x₀ := 1/(1+μ); -gammaScaled (a*μ)*Real.sqrt (2*π*a*μ)*Real.exp (-a*Real.log (x/x₀)-a*μ*Real.log ((1-x)/(1-x₀)))*(normIncBetaI a (a*μ) x-normIncGammaQContinued (a*μ) (a*ζ))) k

/-- betaGeneralH first. -/
@[dlmf 8.18.E16]
theorem betaGeneralH_first {μ ζ : ℝ} (hμ : 0 < μ) (hζ : 0 < ζ) (hζμ : ζ ≠ μ) :
    betaGeneralH 0 ζ μ=(μ*(1/(ζ-μ)-(1+μ)^(-3/2 : ℝ)/(1/(1+μ)-Real.betaGeneralX μ ζ)) : ℝ) := by
  sorry

/-- betaGeneralH at transition. -/
@[dlmf 8.18.E17]
theorem betaGeneralH_at_transition {μ : ℝ} (hμ : 0 < μ) :
    betaGeneralH 0 μ μ=(((1-μ)/Real.sqrt (1+μ)-1)/3 : ℝ) := by
  sorry

/-- All general-case coefficient singularities at ζ=μ are removable. -/
theorem betaGeneralH_analytic (k : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    AnalyticAt ℝ (fun ζ => betaGeneralH k ζ μ) μ := by
  sorry

/-- Uniform normalized remainder with the natural sqrt(1+b/a) coefficient-growth envelope. -/
@[dlmf 8.18.E14]
theorem incBeta_general_uniform_expansion (N : ℕ) :
    IsBigO (comap (fun p : ℝ × ℝ × ℝ => p.1) atTop ⊓ 𝓟 {p : ℝ × ℝ × ℝ | 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧ p.2.2 < 1}) (fun p => let μ := p.2.1/p.1; let x₀ := 1/(1+μ); let ζ := Real.betaZeta μ p.2.2; -gammaScaled p.2.1*Real.sqrt (2*π*p.2.1)*Real.exp (-p.1*Real.log (p.2.2/x₀)-p.2.1*Real.log ((1-p.2.2)/(1-x₀)))*(normIncBetaI p.1 p.2.1 p.2.2-normIncGammaQContinued p.2.1 (p.1*ζ))-∑ k ∈ Finset.range N, betaGeneralH k ζ μ/(p.1 : ℂ)^k) (fun p => p.1^(-(N : ℤ))*Real.sqrt (1+p.2.1/p.1)) := by
  sorry

/-- Inverse of normalized incomplete Beta on [0,1]. -/
@[dlmf 8.18.E18]
def Real.incBetaInverse (a b p : ℝ) : ℝ :=
  if p=0 then 0 else if p=1 then 1 else Classical.epsilon (fun x : ℝ => x ∈ Icc (0 : ℝ) 1 ∧ (normIncBetaI a b x).re=p)

/-- For real positive parameters, `x ↦ Re I_x(a,b)` takes every value of `[0,1]` on `[0,1]`. -/
theorem incG_exists_normIncBetaI_eq {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ x ∈ Icc (0:ℝ) 1, (Real.normIncBetaI a b x).re = p := by
  have ha' : 0 < (a:ℂ).re := by simpa using ha
  have hb' : 0 < (b:ℂ).re := by simpa using hb
  set f : ℝ → ℝ := fun x => (Real.normIncBetaI a b x).re
  have hc : ContinuousOn f (Icc 0 1) := by
    have hi : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((a:ℂ) - 1) * (1 - (t : ℂ)) ^ ((b:ℂ) - 1)) (uIcc 0 1) := by
      have := betaIntegral_convergent ha' hb'
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one] at this
      simpa [uIcc_of_le zero_le_one] using this
    have := intervalIntegral.continuousOn_primitive_interval hi
    rw [uIcc_of_le zero_le_one] at this
    exact Complex.continuous_re.comp_continuousOn (this.div_const _)
  have h0 : f 0 = 0 := by simp [f, Real.normIncBetaI, Real.incBeta_zero]
  have h1 : f 1 = 1 := by simp [f, Real.normIncBetaI_one ha' hb']
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc zero_le_one hc
    (show p ∈ Icc (f 0) (f 1) by rw [h0, h1]; exact ⟨hp, hp1⟩)
  exact ⟨x, hx, hfx⟩

/-- Real.incBetaInverse spec. -/
@[dlmf 8.18.E18]
theorem Real.incBetaInverse_spec {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.incBetaInverse a b p ∈ Icc (0 : ℝ) 1 ∧ (normIncBetaI a b (Real.incBetaInverse a b p)).re=p := by
  rcases hp.eq_or_lt with h0 | h0
  · subst h0
    simp [Real.incBetaInverse, Real.normIncBetaI, Real.incBeta_zero]
  rcases hp1.eq_or_lt with h1 | h1
  · subst h1
    simp [Real.incBetaInverse, Real.normIncBetaI_one (a := (a:ℂ)) (b := (b:ℂ)) (by simpa using ha)
      (by simpa using hb)]
  have hs := Classical.epsilon_spec (incG_exists_normIncBetaI_eq ha hb hp hp1)
  simp only [Real.incBetaInverse, h0.ne', h1.ne, ite_false]
  exact hs


end DLMF.Statistical
