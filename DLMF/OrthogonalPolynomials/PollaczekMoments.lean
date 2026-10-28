/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.ProductIntegral
public import DLMF.OrthogonalPolynomials.HahnMoments
public import DLMF.Hypergeometric.FiniteConvolution
/-!
# Tilted Gamma moments and Meixner--Pollaczek orthogonality

The two-Gamma Mellin--Barnes transform is continued to the full strip needed by
DLMF 18.19.9, using the project's proved vertical Gamma bounds and holomorphic
integral theorem. Chu--Vandermonde then evaluates all polynomial moments, including
the exact square norm. Every finite integral exchange uses absolute integrability.

The analytic continuation step reuses `DLMF.Bessel.frequently_of_forall_nat_add`
and `DLMF.Bessel.ofReal_mul_cpow_of_pos` from `Bessel/ProductIntegral`. The finite
basis change and Gamma-shift formula reuse `HahnMoments`, avoiding a second proof.
-/

@[expose] public section

open Complex Filter Set MeasureTheory
open scoped Real Topology Nat
open DLMF.Gamma (Gamma_add_nat_eq_poch_mul_Gamma)
noncomputable section
namespace DLMF.OrthogonalPolynomials.PollaczekMoments
/-- A rescaled Gamma pair, suited to the existing half-plane Mellin--Barnes API. -/
def pairHalf (a b : ℝ) (y : ℝ) : ℂ :=
  Gamma ((a:ℂ)+I*(y/2)) * Gamma ((b:ℂ)-I*(y/2))
/-- The rescaled Gamma pair is continuous for positive real parameters. -/
theorem pairHalf_continuous {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Continuous (pairHalf a b) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  exact ((DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simpa using ha)).comp (by fun_prop)).mul
    ((DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simpa using hb)).comp (by fun_prop))
/-- The existing vertical Gamma estimates give exponential decay of the pair. -/
theorem pairHalf_bound {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ y : ℝ,
      ‖pairHalf a b y‖ ≤ C*(1+|y|)^K*Real.exp (-(π*|y|)/2) := by
  obtain ⟨A, k, hA⟩ := DLMF.Gamma.exists_norm_Gamma_shift_le ha 0
  obtain ⟨B, l, hB⟩ := DLMF.Gamma.exists_norm_Gamma_shift_le hb 0
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (by simpa using hA 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (by simpa using hB 0)
  refine ⟨A*B,k+l,fun y => ?_⟩
  have h1 := hA (y/2)
  have h2 := hB (-y/2)
  norm_num [abs_div] at h1
  have h2' : ‖Gamma ((b:ℂ)-I*(y/2))‖ ≤
      B*(1+|y|/2)^l*Real.exp (-(π*(|y|/2))/2) := by
    simpa [abs_div, neg_div, sub_eq_add_neg] using h2
  simp only [pairHalf, norm_mul]
  calc _ ≤ (A*(1+|y|/2)^k*Real.exp (-(π*(|y|/2))/2))*
        (B*(1+|y|/2)^l*Real.exp (-(π*(|y|/2))/2)) :=
      mul_le_mul h1 h2' (norm_nonneg _) (by positivity)
    _ = A*B*(1+|y|/2)^(k+l)*Real.exp (-(π*|y|)/2) := by
      rw [pow_add, show -(π*|y|)/2 = -(π*(|y|/2))/2 + -(π*(|y|/2))/2 by ring,
        Real.exp_add]
      ring
    _ ≤ A*B*(1+|y|)^(k+l)*Real.exp (-(π*|y|)/2) := by
      gcongr
      linarith [abs_nonneg y]
/-- The rescaled Mellin--Barnes transform is holomorphic in the right half-plane. -/
theorem pairHalf_transform_differentiable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    DifferentiableOn ℂ (fun w : ℂ => ∫ y : ℝ, pairHalf a b y*w^(I*y)) {w | 0 < w.re} := by
  obtain ⟨C,K,h⟩ := pairHalf_bound ha hb
  simpa using DLMF.Gamma.differentiableOn_integral_mul_cpow (pairHalf_continuous ha hb) h 0


/-- Evaluation of the rescaled transform on the positive real axis. -/
theorem pairHalf_transform_real {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {w : ℝ} (hw : 0 < w) :
    (∫ y : ℝ, pairHalf a b y*(w:ℂ)^(I*y)) =
      4*π*Gamma ((a:ℂ)+b)*(w:ℂ)^(2*(b:ℂ))*(1+(w:ℂ)^2)^(-((a:ℂ)+b)) := by
  let u : ℝ := (w⁻¹)^2
  have hu : 0 < u := by dsimp [u]; positivity
  have hw0 : (w:ℂ) ≠ 0 := ofReal_ne_zero.mpr hw.ne'
  have hu0 : (u:ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  have hplus : (1+(w:ℂ)^2) ≠ 0 := by
    exact_mod_cast (show (1:ℝ)+w^2 ≠ 0 by positivity)
  have hlU : log (u:ℂ) = -2*log (w:ℂ) := by
    rw [← ofReal_log hu.le, ← ofReal_log hw.le]
    simp only [u, Real.log_pow, Real.log_inv]
    push_cast
    ring
  have hlP : log ((1+u:ℝ):ℂ) = log (1+(w:ℂ)^2)-2*log (w:ℂ) := by
    have he : (1+u:ℝ) = (1+w^2)/w^2 := by dsimp [u]; field_simp; ring
    rw [show 1+(w:ℂ)^2 = ((1+w^2:ℝ):ℂ) by push_cast; rfl,
      ← ofReal_log (by positivity : 0 ≤ 1+w^2),
      ← ofReal_log hw.le, ← ofReal_log (by positivity : 0 ≤ 1+u), he,
      Real.log_div (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hp : ((1+u:ℝ):ℂ)^(-((a:ℂ)+b)) =
      (w:ℂ)^(2*(a:ℂ))*((w:ℂ)^(2*(b:ℂ))*(1+(w:ℂ)^2)^(-((a:ℂ)+b))) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (show (1+u:ℝ) ≠ 0 by positivity)),
      cpow_def_of_ne_zero hw0, cpow_def_of_ne_zero hw0, cpow_def_of_ne_zero hplus,
      ← Complex.exp_add, ← Complex.exp_add, hlP]
    congr 1
    ring
  let J := ∫ x : ℝ, Gamma ((a:ℂ)+I*x)*Gamma ((b:ℂ)-I*x)*(w:ℂ)^(2*I*x)
  have hscale : (∫ y : ℝ, pairHalf a b y*(w:ℂ)^(I*y)) = 2*J := by
    have h := Measure.integral_comp_div (fun x : ℝ =>
      Gamma ((a:ℂ)+I*x)*Gamma ((b:ℂ)-I*x)*(w:ℂ)^(2*I*x)) 2
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 2), real_smul, ofReal_ofNat] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [pairHalf, ofReal_div, ofReal_ofNat]
    congr 2
    ring
  have ht (y : ℝ) : (u:ℂ)^(-((a:ℂ)+y*I)) =
      (w:ℂ)^(2*(a:ℂ))*(w:ℂ)^(2*I*y) := by
    rw [cpow_def_of_ne_zero hu0, cpow_def_of_ne_zero hw0, cpow_def_of_ne_zero hw0,
      ← Complex.exp_add, hlU]
    congr 1
    ring
  have h := DLMF.Gamma.Gamma_mul_one_add_cpow_neg (a := (a:ℂ)+b) (σ := a) ha
    (by simp; linarith) hu
  have hi : (∫ y : ℝ, Gamma ((a:ℂ)+y*I)*Gamma ((a:ℂ)+b-((a:ℂ)+y*I))*
      (u:ℂ)^(-((a:ℂ)+y*I))) = (w:ℂ)^(2*(a:ℂ))*J := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [ht, show (a:ℂ)+b-((a:ℂ)+y*I) = (b:ℂ)-I*y by ring,
      show (a:ℂ)+y*I = (a:ℂ)+I*y by ring]
    ring
  rw [hi, hp] at h
  rw [hscale]
  have hpow : (w:ℂ)^(2*(a:ℂ)) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hw0)
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp at h
  apply mul_left_cancel₀ hpow
  ring_nf at h ⊢
  linear_combination -2*h


/-- The rescaled Barnes transform throughout the right half-plane. -/
theorem pairHalf_transform {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {w : ℂ} (hw : 0 < w.re) :
    (∫ y : ℝ, pairHalf a b y*w^(I*y)) =
      4*π*Gamma ((a:ℂ)+b)*w^(2*(b:ℂ))*(1+w^2)^(-((a:ℂ)+b)) := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
  have hf := (pairHalf_transform_differentiable ha hb).analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (fun w : ℂ =>
      4*π*Gamma ((a:ℂ)+b)*w^(2*(b:ℂ))*(1+w^2)^(-((a:ℂ)+b))) {w | 0 < w.re} := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    have hs : 1+z^2 ∈ slitPlane := by
      by_cases hi : z.im = 0
      · left
        simp [pow_two, hi]
        nlinarith [sq_nonneg z.re]
      · right
        simp only [add_im, one_im, zero_add, pow_two, mul_im]
        intro h
        have hmul : z.re*z.im = 0 := by linear_combination h/2
        exact (mul_ne_zero (show z.re ≠ 0 from ne_of_gt hz) hi) hmul
    exact DifferentiableAt.differentiableWithinAt
      (((differentiableAt_const _).mul (differentiableAt_id.cpow (differentiableAt_const _) (Or.inl hz))).mul
        ((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => 1+z^2) z).cpow (differentiableAt_const _) hs))
  refine hf.eqOn_of_preconnected_of_frequently_eq hg (convex_halfSpace_re_gt 0).isPreconnected
    (show (1:ℂ) ∈ {w | 0 < w.re} by simp)
    (DLMF.Bessel.frequently_of_forall_nat_add fun n => ?_) hw
  simpa using pairHalf_transform_real ha hb (w := 1+1/((n:ℝ)+1)) (by positivity)

/-- The tilted two-Gamma integral, in the symmetric trigonometric normalization. -/
theorem tilted_Gamma_integral {a b θ : ℝ} (ha : 0 < a) (hb : 0 < b) (hθ : |θ| < π) :
    (∫ y : ℝ, Gamma ((a:ℂ)+I*y)*Gamma ((b:ℂ)-I*y)*exp (θ*y)) =
      2*π*Gamma ((a:ℂ)+b)*exp (I*θ*((a:ℂ)-b)/2)/
        ((2*Real.cos (θ/2):ℝ):ℂ)^((a:ℂ)+b) := by
  let w : ℂ := exp (-I*θ/2)
  have hangle : |θ/2| < π/2 := by rw [abs_div]; norm_num; linarith
  have hcos : 0 < Real.cos (θ/2) := Real.cos_pos_of_mem_Ioo (abs_lt.mp hangle)
  have hw : 0 < w.re := by
    simp only [w, Complex.exp_re, Complex.div_re, Complex.div_im, mul_re, mul_im, neg_re,
      neg_im, I_re, I_im, ofReal_re, ofReal_im]
    norm_num
    rw [show -(θ*2)/4 = -(θ/2) by ring, Real.cos_neg]
    exact hcos
  have hw0 : w ≠ 0 := exp_ne_zero _
  have hlw : log w = -I*θ/2 := by
    dsimp only [w]
    rw [Complex.log_exp]
    · simp; linarith [(abs_lt.mp hθ).2, Real.pi_pos]
    · simp; linarith [(abs_lt.mp hθ).1, Real.pi_pos]
  have hp (y : ℝ) : w^(I*y) = exp (θ*y/2) := by
    rw [cpow_def_of_ne_zero hw0, hlw]
    congr 1
    ring_nf
    rw [I_sq]
    ring
  have hscale : (∫ y : ℝ, pairHalf a b y*w^(I*y)) =
      2*(∫ y : ℝ, Gamma ((a:ℂ)+I*y)*Gamma ((b:ℂ)-I*y)*exp (θ*y)) := by
    have h := Measure.integral_comp_div (fun y : ℝ =>
      Gamma ((a:ℂ)+I*y)*Gamma ((b:ℂ)-I*y)*exp (θ*y)) 2
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 2), real_smul, ofReal_ofNat] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [pairHalf, ofReal_div, ofReal_ofNat, hp]
    congr 1
    congr 1
    ring
  have hfac : 1+w^2 = ((2*Real.cos (θ/2):ℝ):ℂ)*w := by
    have hc : ((2*Real.cos (θ/2):ℝ):ℂ) = exp (I*θ/2)+exp (-I*θ/2) := by
      push_cast
      rw [Complex.two_cos]
      congr 1 <;> congr 1 <;> ring
    rw [hc, add_mul]
    have he : exp (I*θ/2)*w = 1 := by
      dsimp only [w]
      rw [← Complex.exp_add, show I*θ/2+-I*θ/2 = 0 by ring, Complex.exp_zero]
    rw [he]
    change 1+w^2 = 1+w*w
    ring
  have hsum : (1+w^2)^(-((a:ℂ)+b)) =
      (((2*Real.cos (θ/2):ℝ):ℂ)^((a:ℂ)+b))⁻¹ * w^(-((a:ℂ)+b)) := by
    rw [hfac, DLMF.Bessel.ofReal_mul_cpow_of_pos (by positivity), cpow_neg]
  have hpow : w^(2*(b:ℂ))*w^(-((a:ℂ)+b)) = exp (I*θ*((a:ℂ)-b)/2) := by
    rw [← cpow_add _ _ hw0, cpow_def_of_ne_zero hw0, hlw]
    congr 1
    ring
  have h := pairHalf_transform ha hb hw
  rw [hscale, hsum] at h
  have he : w^(2*(b:ℂ))*((((2*Real.cos (θ/2):ℝ):ℂ)^((a:ℂ)+b))⁻¹*w^(-((a:ℂ)+b))) =
      exp (I*θ*((a:ℂ)-b)/2)/(((2*Real.cos (θ/2):ℝ):ℂ)^((a:ℂ)+b)) := by
    rw [← hpow]; ring
  rw [mul_assoc (4*π*Gamma ((a:ℂ)+b)), he] at h
  linear_combination h/2

/-- The exponentially tilted Gamma pair is absolutely integrable throughout its strip. -/
theorem integrable_tilted_Gamma {a b θ : ℝ} (ha : 0 < a) (hb : 0 < b) (hθ : |θ| < π) :
    Integrable (fun y : ℝ => Gamma ((a:ℂ)+I*y)*Gamma ((b:ℂ)-I*y)*exp (θ*y)) := by
  obtain ⟨C,K,h⟩ := pairHalf_bound ha hb
  have hC : 0 ≤ C := (norm_nonneg _).trans (by simpa using h 0)
  have hi := (DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg (sub_pos.mpr hθ) K).const_mul (C*2^K)
  apply hi.mono' (show AEStronglyMeasurable _ volume from ?_) (Eventually.of_forall fun y => ?_)
  · apply Continuous.aestronglyMeasurable
    have hc : Continuous (fun y : ℝ => pairHalf a b (2*y)) := (pairHalf_continuous ha hb).comp (by fun_prop)
    have hc' : Continuous (fun y : ℝ => Gamma ((a:ℂ)+I*y)*Gamma ((b:ℂ)-I*y)) := by
      simpa [pairHalf] using hc
    exact hc'.mul (show Continuous (fun y : ℝ => exp ((θ:ℂ)*y)) by fun_prop)
  · have hh := h (2*y)
    norm_num [pairHalf, abs_mul] at hh
    rw [norm_mul, Complex.norm_exp]
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    calc _ ≤ C*(1+2*|y|)^K*Real.exp (-(π*|y|)) * Real.exp (θ*y) :=
          mul_le_mul_of_nonneg_right (by rw [norm_mul]; convert hh using 1; ring_nf) (by positivity)
      _ = C*(1+2*|y|)^K*Real.exp (-(π*|y|)+θ*y) := by rw [Real.exp_add]; ring
      _ ≤ C*(2*(1+|y|))^K*Real.exp (-(π*|y|)+|θ| * |y|) := by
          apply mul_le_mul
          · gcongr; linarith [abs_nonneg y]
          · apply Real.exp_le_exp.mpr
            linarith [le_abs_self (θ*y), abs_mul θ y]
          · positivity
          · positivity
      _ = C*2^K*((1+|y|)^K*Real.exp (-((π-|θ|)*|y|))) := by
          rw [mul_pow]
          rw [show -(π*|y|)+|θ| * |y| = -((π-|θ|)*|y|) by ring]
          ring
open DLMF.Hypergeometric
/-- The tilted two-Gamma weight. -/
def weight (lam θ : ℝ) (x : ℝ) : ℂ :=
  Gamma ((lam:ℂ)+I*x)*Gamma ((lam:ℂ)-I*x)*exp (θ*x)
/-- The positive scale in the tilted Gamma transform. -/
def scale (θ : ℝ) : ℂ := (2*Real.cos (θ/2):ℝ)
/-- The phase in the tilted Gamma transform. -/
def phase (θ : ℝ) : ℂ := exp (I*θ/2)
/-- The reversed rising-factorial moment. -/
def moment (lam θ : ℝ) (j : ℕ) : ℂ :=
  2*π*Gamma (2*(lam:ℂ)+j)*exp (-I*θ*j/2) / scale θ^(2*(lam:ℂ)+j)
/-- The transform scale does not vanish inside the convergence strip. -/
theorem scale_ne_zero {θ : ℝ} (hθ : |θ| < π) : scale θ ≠ 0 := by
  apply ofReal_ne_zero.mpr
  have hc : 0 < Real.cos (θ/2) := Real.cos_pos_of_mem_Ioo (by
    rw [abs_lt] at hθ
    constructor <;> linarith)
  exact ne_of_gt (mul_pos (by norm_num) hc)
/-- Polynomial factors shift the two Gamma parameters. -/
theorem mixed_moment {lam θ : ℝ} (hlam : 0 < lam) (hθ : |θ| < π) (k j : ℕ) :
    Integrable (fun x : ℝ => poch ((lam:ℂ)+I*x) k * poch ((lam:ℂ)-I*x) j * weight lam θ x) ∧
    (∫ x : ℝ, poch ((lam:ℂ)+I*x) k * poch ((lam:ℂ)-I*x) j * weight lam θ x) =
      moment lam θ j * poch (2*(lam:ℂ)+j) k * (phase θ / scale θ)^k := by
  have he (x : ℝ) : poch ((lam:ℂ)+I*x) k * poch ((lam:ℂ)-I*x) j * weight lam θ x =
      Gamma (((lam+k:ℝ):ℂ)+I*x)*Gamma (((lam+j:ℝ):ℂ)-I*x)*exp (θ*x) := by
    dsimp only [weight]
    push_cast
    rw [show (lam:ℂ)+k+I*x = ((lam:ℂ)+I*x)+k by ring,
      show (lam:ℂ)+j-I*x = ((lam:ℂ)-I*x)+j by ring,
      Gamma_add_nat_eq_poch_mul_Gamma (by simpa using hlam),
      Gamma_add_nat_eq_poch_mul_Gamma (by simpa using hlam)]
    ring
  simp_rw [he]
  refine ⟨integrable_tilted_Gamma (by positivity) (by positivity) hθ, ?_⟩
  rw [tilted_Gamma_integral (by positivity) (by positivity) hθ]
  push_cast
  rw [show (lam:ℂ)+k+((lam:ℂ)+j) = (2*(lam:ℂ)+j)+k by ring,
    Gamma_add_nat_eq_poch_mul_Gamma (by simp; positivity)]
  have hexp : exp (I*θ*((lam:ℂ)+k-((lam:ℂ)+j))/2) =
      exp (-I*θ*j/2)*phase θ^k := by
    dsimp only [phase]
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    ring
  rw [hexp, show 2*cos ((θ:ℂ)/2) = scale θ by simp [scale, ofReal_cos, ofReal_div],
    cpow_add _ _ (scale_ne_zero hθ), cpow_natCast]
  dsimp only [moment, scale]
  rw [div_pow]
  ring
/-- A terminating Pollaczek sum with its transform-adapted argument. -/
def poly (lam θ : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), ((-1:ℂ)^k*n.choose k/poch (2*(lam:ℂ)) k)*
    (scale θ / phase θ)^k * poch ((lam:ℂ)+I*x) k
/-- Absolute integrability of every polynomial against a reversed rising factorial. -/
theorem integrable_poly_basis {lam θ : ℝ} (hlam : 0 < lam) (hθ : |θ| < π) (n j : ℕ) :
    Integrable (fun x : ℝ => poly lam θ n x * poch ((lam:ℂ)-I*x) j * weight lam θ x) := by
  simp only [poly, Finset.sum_mul]
  apply integrable_finsetSum
  intro k hk
  simpa only [mul_assoc] using ((mixed_moment hlam hθ k j).1.const_mul
    (((-1:ℂ)^k*n.choose k/poch (2*(lam:ℂ)) k)*(scale θ/phase θ)^k))
/-- Chu--Vandermonde evaluates all reversed moments of a Pollaczek polynomial. -/
theorem integral_poly_basis {lam θ : ℝ} (hlam : 0 < lam) (hθ : |θ| < π) (n j : ℕ) :
    (∫ x : ℝ, poly lam θ n x * poch ((lam:ℂ)-I*x) j * weight lam θ x) =
      moment lam θ j * poch (-(j:ℂ)) n / poch (2*(lam:ℂ)) n := by
  have hP (k : ℕ) : poch (2*(lam:ℂ)) k ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; positivity)) k
  have hr : phase θ ≠ 0 := Complex.exp_ne_zero _
  have hs := scale_ne_zero hθ
  have he : (fun x : ℝ => poly lam θ n x * poch ((lam:ℂ)-I*x) j * weight lam θ x) =
      fun x : ℝ => ∑ k ∈ Finset.range (n+1),
        (((-1:ℂ)^k*n.choose k/poch (2*(lam:ℂ)) k)*(scale θ/phase θ)^k)*
        (poch ((lam:ℂ)+I*x) k*poch ((lam:ℂ)-I*x) j*weight lam θ x) := by
    funext x
    simp only [poly, Finset.sum_mul, mul_assoc]
  rw [he, integral_finsetSum _ (fun k hk => (mixed_moment hlam hθ k j).1.const_mul _)]
  simp_rw [integral_const_mul, (mixed_moment hlam hθ _ j).2]
  have ht (k : ℕ) : (((-1:ℂ)^k*n.choose k/poch (2*(lam:ℂ)) k)*(scale θ/phase θ)^k)*
      (moment lam θ j*poch (2*(lam:ℂ)+j) k*(phase θ/scale θ)^k) =
      moment lam θ j*((-1:ℂ)^k*n.choose k*poch (2*(lam:ℂ)+j) k/poch (2*(lam:ℂ)) k) := by
    rw [div_pow, div_pow]
    field_simp
  simp_rw [ht]
  rw [← Finset.mul_sum, ← poch_ratio_vandermonde _ _ hP,
    show 2*(lam:ℂ)-(2*(lam:ℂ)+j) = -(j:ℂ) by ring]
  ring

/-- A same-direction moment reduces to the finite reversed-basis expansion. -/
theorem poly_same_basis {lam θ : ℝ} (hlam : 0 < lam) (hθ : |θ| < π) (n k : ℕ) :
    Integrable (fun x : ℝ => poly lam θ n x*poch ((lam:ℂ)+I*x) k*weight lam θ x) ∧
    (∫ x : ℝ, poly lam θ n x*poch ((lam:ℂ)+I*x) k*weight lam θ x) =
      ∑ j ∈ Finset.range (k+1), ((-1:ℂ)^k*k.choose j*poch (-2*(lam:ℂ)-k+1) (k-j))*
        (moment lam θ j*poch (-(j:ℂ)) n/poch (2*(lam:ℂ)) n) := by
  let C (j : ℕ) : ℂ := (-1:ℂ)^k*k.choose j*poch (-2*(lam:ℂ)-k+1) (k-j)
  have he : (fun x : ℝ => poly lam θ n x*poch ((lam:ℂ)+I*x) k*weight lam θ x) =
      fun x : ℝ => ∑ j ∈ Finset.range (k+1), C j*(poly lam θ n x*poch ((lam:ℂ)-I*x) j*weight lam θ x) := by
    funext x
    rw [show (lam:ℂ)+I*x = 2*(lam:ℂ)-((lam:ℂ)-I*x) by ring,
      HahnMoments.poch_reverse_basis, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [C]
    ring
  rw [he]
  have hi (j : ℕ) := (integrable_poly_basis hlam hθ n j).const_mul (C j)
  refine ⟨integrable_finsetSum _ (fun j hj => hi j), ?_⟩
  rw [integral_finsetSum _ (fun j hj => hi j)]
  simp_rw [integral_const_mul, integral_poly_basis hlam hθ]
  rfl
/-- A Pollaczek polynomial annihilates each lower-degree rising factorial. -/
theorem integral_poly_same_basis_zero {lam θ : ℝ} (hlam : 0 < lam) (hθ : |θ| < π) {n k : ℕ} (hk : k < n) :
    (∫ x : ℝ, poly lam θ n x*poch ((lam:ℂ)+I*x) k*weight lam θ x) = 0 := by
  rw [(poly_same_basis hlam hθ n k).2]
  apply Finset.sum_eq_zero
  intro j hj
  rw [poch_neg_nat_eq_zero (show j < n by have := Finset.mem_range.mp hj; omega)]
  ring
/-- Only the leading reversed rising factorial contributes in equal degree. -/
theorem integral_poly_same_basis_self {lam θ : ℝ} (hlam : 0 < lam) (hθ : |θ| < π) (n : ℕ) :
    (∫ x : ℝ, poly lam θ n x*poch ((lam:ℂ)+I*x) n*weight lam θ x) =
      (-1:ℂ)^n*(moment lam θ n*poch (-(n:ℂ)) n/poch (2*(lam:ℂ)) n) := by
  rw [(poly_same_basis hlam hθ n n).2, Finset.sum_eq_single n]
  · simp [poch_zero]
  · intro j hj hjn
    rw [poch_neg_nat_eq_zero (show j < n by have := Finset.mem_range.mp hj; omega)]
    ring
  · simp
/-- The finite sum defining a second polynomial can be integrated term by term. -/
theorem integral_poly_mul_poly {lam θ : ℝ} (hlam : 0 < lam) (hθ : |θ| < π) (m n : ℕ) :
    (∫ x : ℝ, poly lam θ m x*poly lam θ n x*weight lam θ x) =
      ∑ k ∈ Finset.range (m+1), (((-1:ℂ)^k*m.choose k/poch (2*(lam:ℂ)) k)*(scale θ/phase θ)^k)*
        (∫ x : ℝ, poly lam θ n x*poch ((lam:ℂ)+I*x) k*weight lam θ x) := by
  have he : (fun x : ℝ => poly lam θ m x*poly lam θ n x*weight lam θ x) =
      fun x : ℝ => ∑ k ∈ Finset.range (m+1),
        (((-1:ℂ)^k*m.choose k/poch (2*(lam:ℂ)) k)*(scale θ/phase θ)^k)*
        (poly lam θ n x*poch ((lam:ℂ)+I*x) k*weight lam θ x) := by
    funext x
    rw [poly, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he, integral_finsetSum _ (fun k hk => (poly_same_basis hlam hθ n k).1.const_mul _)]
  simp_rw [integral_const_mul]
/-- Unequal-degree Pollaczek polynomials are orthogonal. -/
theorem poly_orthogonal {lam θ : ℝ} (hlam : 0 < lam) (hθ : |θ| < π) {m n : ℕ} (hmn : m ≠ n) :
    (∫ x : ℝ, poly lam θ m x*poly lam θ n x*weight lam θ x) = 0 := by
  have hlt (m n : ℕ) (hmn : m < n) :
      (∫ x : ℝ, poly lam θ m x*poly lam θ n x*weight lam θ x) = 0 := by
    rw [integral_poly_mul_poly hlam hθ]
    apply Finset.sum_eq_zero
    intro k hk
    rw [integral_poly_same_basis_zero hlam hθ (show k < n by have := Finset.mem_range.mp hk; omega), mul_zero]
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hlt m n h
  · rw [show (fun x : ℝ => poly lam θ m x*poly lam θ n x*weight lam θ x) =
        fun x : ℝ => poly lam θ n x*poly lam θ m x*weight lam θ x by funext x; ring]
    exact hlt n m h
/-- The exact square norm of the unnormalized terminating sum. -/
theorem poly_square {lam θ : ℝ} (hlam : 0 < lam) (hθ : |θ| < π) (n : ℕ) :
    (∫ x : ℝ, poly lam θ n x*poly lam θ n x*weight lam θ x) =
      (scale θ/phase θ)^n*moment lam θ n*poch (-(n:ℂ)) n/poch (2*(lam:ℂ)) n^2 := by
  rw [integral_poly_mul_poly hlam hθ, Finset.sum_eq_single n]
  · rw [integral_poly_same_basis_self hlam hθ]
    simp only [Nat.choose_self, Nat.cast_one, mul_one]
    have hn : ((-1:ℂ)^n)^2 = 1 := by rw [← pow_mul, mul_comm n 2, pow_mul]; simp
    calc _ = ((-1:ℂ)^n)^2 * ((scale θ/phase θ)^n*moment lam θ n*poch (-(n:ℂ)) n/poch (2*(lam:ℂ)) n^2) := by ring
      _ = _ := by rw [hn, one_mul]
  · intro k hk hkn
    rw [integral_poly_same_basis_zero hlam hθ (show k < n by have := Finset.mem_range.mp hk; omega), mul_zero]
  · simp

/-- The standard Pollaczek normalization cancels the phase in the square norm. -/
theorem normalized_square {lam θ : ℝ} (hlam : 0 < lam) (hθ : |θ| < π) (n : ℕ) :
    (poch (2*(lam:ℂ)) n/n.factorial*(I*phase θ)^n)^2 *
      (∫ x : ℝ, poly lam θ n x*poly lam θ n x*weight lam θ x) =
      2*π*Gamma (2*(lam:ℂ)+n)/(scale θ^(2*(lam:ℂ))*n.factorial) := by
  have hP : poch (2*(lam:ℂ)) n ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos (by simp; positivity)) n
  have hf : (n.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hs := scale_ne_zero hθ
  have hr : phase θ ≠ 0 := Complex.exp_ne_zero _
  have hpow : ((I*phase θ)^n)^2 = (-1:ℂ)^n*(phase θ^n)^2 := by
    rw [mul_pow, mul_pow, ← pow_mul I, mul_comm n 2, pow_mul, I_sq]
  have hneg : poch (-(n:ℂ)) n = (-1:ℂ)^n*n.factorial := by
    rw [poch_neg_coe_nat, Nat.descFactorial_self]
  have he : exp (-I*θ*n/2) = (phase θ^n)⁻¹ := by
    dsimp only [phase]
    rw [← Complex.exp_nat_mul, ← Complex.exp_neg]
    congr 1
    ring
  have hn : ((-1:ℂ)^n)^2 = 1 := by rw [← pow_mul, mul_comm n 2, pow_mul]; simp
  rw [poly_square hlam hθ, mul_pow, hpow, hneg]
  dsimp only [moment]
  rw [he, cpow_add _ _ hs, cpow_natCast, div_pow]
  field_simp [hs, hr, hP, hf]
  ring_nf at hn ⊢
  rw [hn]
  simp only [inv_pow]
  field_simp

end DLMF.OrthogonalPolynomials.PollaczekMoments
