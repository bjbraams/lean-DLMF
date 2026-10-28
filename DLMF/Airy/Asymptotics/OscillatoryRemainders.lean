/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Asymptotics.SectorRemainders

/-!
# Signed oscillatory Airy remainder bounds

Signed estimates for the even and odd subseries of the oscillatory Airy expansions.

Source references and common attribution are retained in
`DLMF.Airy.Asymptotics`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent

open scoped Real Topology Interval

namespace DLMF.Airy

/-! ### Signed bounds for the oscillatory subseries on the negative axis (DLMF §9.7(iii))

On the rays `arg w = ±π/3` the Stieltjes ray of the normalized `Ai` (σ = 1/6 form) and of the
normalized `Ai'` (kernel `t^{1/6}(1+t)^{1/6}`, whose binomial remainder is again a Stieltjes
transform with a nonnegative weight) is `θ = ∓π/2`, where `Re (1 + s e^{iθ})⁻¹ ∈ [0, 1]`. Hence the
remainder after `M` terms is `(A + iB)` times the first neglected term with `0 ≤ A ≤ 1`
(`airyDer_ray_ratio`). The even and odd parts `(F₊ ± F₋)/2`, `(F₊ - F₋)/(2i)` of the normalized
function at `x e^{±iπ/3}` are the real components of 9.7.9–9.7.12 (`airyDer_comp_false`,
`airyDer_comp_true`); their truncation errors are real and equal to `Ā` times the first
neglected term, which gives the bound together with its sign. Helper names carry the prefix
`airyDer_`. -/
/-- Estimate under the stated parameter and domain assumptions: `0 ≤ ((1 + (s : ℂ) * exp (θ *
I))⁻¹).re ∧ ((1 + (s : ℂ) * exp (θ * I))⁻¹).re ≤ 1`. -/
theorem airyDer_re_recip_mem {θ : ℝ} (hθ : 0 ≤ Real.cos θ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ ((1 + (s : ℂ) * exp (θ * I))⁻¹).re ∧ ((1 + (s : ℂ) * exp (θ * I))⁻¹).re ≤ 1 := by
  set w := 1 + (s : ℂ) * exp (θ * I) with hw
  have hre : w.re = 1 + s * Real.cos θ := by simp [hw, exp_ofReal_mul_I_re]
  have h1 : 1 ≤ w.re := by rw [hre]; nlinarith
  have hns : 0 < normSq w := by rw [normSq_apply]; nlinarith [mul_self_nonneg w.im]
  rw [inv_re]
  refine ⟨div_nonneg (by linarith) hns.le, (div_le_one hns).mpr ?_⟩
  rw [normSq_apply]; nlinarith [mul_self_nonneg w.im]

/-- `‖(1 + s e^{iθ})⁻¹‖ ≤ 1` when `cos θ ≥ 0` and `s ≥ 0`. -/
theorem airyDer_norm_recip_le {θ : ℝ} (hθ : 0 ≤ Real.cos θ) {s : ℝ} (hs : 0 ≤ s) :
    ‖(1 + (s : ℂ) * exp (θ * I))⁻¹‖ ≤ 1 := by
  rw [norm_inv]; exact inv_le_one_of_one_le₀ (Complex.one_le_norm_one_add_ofReal_mul_exp hs hθ)

/-- `1 + (r e^{iθ}) τ = 1 + (r τ) e^{iθ}`. -/
theorem airyDer_one_add_eq (θ r τ : ℝ) :
    1 + ((r : ℂ) * exp (θ * I)) * τ = 1 + ((r * τ : ℝ) : ℂ) * exp (θ * I) := by
  push_cast; ring

/-- For integrable real `g` on `(0,1)` and `cos θ ≥ 0`, `g(τ)/(1 + r e^{iθ} τ)` is integrable. -/
theorem airyDer_integrableOn_inner {g : ℝ → ℝ} (hgm : Measurable g) (hgi : IntegrableOn g (Ioo 0 1))
    {θ : ℝ} (hcos : 0 ≤ Real.cos θ) {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun τ : ℝ => (g τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹) (Ioo 0 1) := by
  refine Integrable.mono' hgi.norm ?_ ?_
  · exact (by fun_prop : Measurable fun τ : ℝ =>
      (g τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun τ hτ => ?_)
    rw [norm_mul, Complex.norm_real, airyDer_one_add_eq]
    calc ‖g τ‖ * ‖(1 + ((r * τ : ℝ) : ℂ) * exp (θ * I))⁻¹‖ ≤ ‖g τ‖ * 1 :=
          mul_le_mul_of_nonneg_left (airyDer_norm_recip_le hcos (mul_nonneg hr hτ.1.le))
            (norm_nonneg _)
      _ = ‖g τ‖ := mul_one _

/-- For a nonnegative integrable weight `g` on `(0,1)`, `cos θ ≥ 0` and `r ≥ 0`, the inner
Stieltjes integral `q(r) = ∫₀¹ g(τ)/(1 + r e^{iθ} τ) dτ` has `‖q(r)‖ ≤ ∫ g` and
`0 ≤ Re q(r) ≤ ∫ g`. -/
private lemma airyDer_inner_bounds {g : ℝ → ℝ} (hgm : Measurable g)
    (hg0 : ∀ τ ∈ Ioo (0 : ℝ) 1, 0 ≤ g τ) (hgi : IntegrableOn g (Ioo 0 1)) {θ : ℝ}
    (hcos : 0 ≤ Real.cos θ) {r : ℝ} (hr : 0 ≤ r) :
    ‖∫ τ in Ioo (0 : ℝ) 1, (g τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹‖ ≤
        ∫ τ in Ioo (0 : ℝ) 1, g τ ∧
      0 ≤ (∫ τ in Ioo (0 : ℝ) 1, (g τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹).re ∧
      (∫ τ in Ioo (0 : ℝ) 1, (g τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹).re ≤
        ∫ τ in Ioo (0 : ℝ) 1, g τ := by
  refine ⟨?_, ?_⟩
  · refine (norm_integral_le_of_norm_le hgi ?_).trans le_rfl
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun τ hτ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hg0 τ hτ), airyDer_one_add_eq]
    calc g τ * ‖(1 + ((r * τ : ℝ) : ℂ) * exp (θ * I))⁻¹‖ ≤ g τ * 1 :=
          mul_le_mul_of_nonneg_left (airyDer_norm_recip_le hcos (mul_nonneg hr hτ.1.le))
            (hg0 τ hτ)
      _ = g τ := mul_one _
  have hi := airyDer_integrableOn_inner hgm hgi hcos hr
  have he : (∫ τ in Ioo (0 : ℝ) 1, (g τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹).re =
      ∫ τ in Ioo (0 : ℝ) 1, g τ * ((1 + ((r * τ : ℝ) : ℂ) * exp (θ * I))⁻¹).re := by
    rw [← RCLike.re_to_complex, ← integral_re hi]
    refine setIntegral_congr_fun measurableSet_Ioo fun τ _ => ?_
    simp only [RCLike.re_to_complex]
    rw [airyDer_one_add_eq, re_ofReal_mul]
  rw [he]
  have hi' : IntegrableOn (fun τ => g τ * ((1 + ((r * τ : ℝ) : ℂ) * exp (θ * I))⁻¹).re)
      (Ioo 0 1) := by
    refine (hi.re).congr_fun (fun τ _ => ?_) measurableSet_Ioo
    simp only [RCLike.re_to_complex]
    rw [airyDer_one_add_eq, re_ofReal_mul]
  constructor
  · exact setIntegral_nonneg measurableSet_Ioo fun τ hτ =>
      mul_nonneg (hg0 τ hτ) (airyDer_re_recip_mem hcos (mul_nonneg hr hτ.1.le)).1
  · refine setIntegral_mono_on hi' hgi measurableSet_Ioo fun τ hτ => ?_
    calc g τ * ((1 + ((r * τ : ℝ) : ℂ) * exp (θ * I))⁻¹).re ≤ g τ * 1 :=
          mul_le_mul_of_nonneg_left (airyDer_re_recip_mem hcos (mul_nonneg hr hτ.1.le)).2
            (hg0 τ hτ)
      _ = g τ := mul_one _

/-- **The ray remainder as a damped multiple of the first neglected term.** For `cos θ ≥ 0` and a
nonnegative weight `g` on `(0,1)`, the ray Stieltjes integral equals `(A + iB)` times its value
with the Stieltjes denominator replaced by `1`, with `0 ≤ A ≤ 1`. -/
theorem airyDer_ray_ratio {b W θ : ℝ} (hb : 0 < b) (hW : 0 < W) (hθ : |θ| < π)
    (hcos : 0 ≤ Real.cos θ) (N : ℕ) {g : ℝ → ℝ} (hgm : Measurable g)
    (hg0 : ∀ τ ∈ Ioo (0 : ℝ) 1, 0 ≤ g τ) (hgi : IntegrableOn g (Ioo 0 1)) :
    ∃ A B : ℝ, 0 ≤ A ∧ A ≤ 1 ∧
      ∫ r in Ioi (0 : ℝ), Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) *
        ((-((r : ℂ) * exp (θ * I))) ^ N * ∫ τ in Ioo (0 : ℝ) 1,
          (g τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹)) =
      (A + B * I) * ((((-1) ^ N * ∫ τ in Ioo (0 : ℝ) 1, g τ : ℝ) : ℂ) *
        exp (θ * I * ((b : ℂ) - 1 + N)) * (Gamma ((b : ℂ) + N) * (W : ℂ) ^ (-((b : ℂ) + N)))) := by
  set q : ℝ → ℂ := fun r => ∫ τ in Ioo (0 : ℝ) 1,
    (g τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹ with hq
  set C : ℝ := ∫ τ in Ioo (0 : ℝ) 1, g τ with hC
  set ρ : ℝ → ℝ := fun r => r ^ ((b + N) - 1) * Real.exp (-(W * r)) with hρ
  set ph : ℂ := exp (θ * I * ((b : ℂ) - 1 + N)) with hph
  set K : ℝ := Real.Gamma (b + N) * W ^ (-(b + N)) with hK
  have hbN : 0 < b + N := by positivity
  have hKpos : 0 < K := mul_pos (Real.Gamma_pos_of_pos hbN) (Real.rpow_pos_of_pos hW _)
  have hKc : Gamma ((b : ℂ) + N) * (W : ℂ) ^ (-((b : ℂ) + N)) = (K : ℂ) := by
    have hg : Gamma ((b : ℂ) + N) = ((Real.Gamma (b + N) : ℝ) : ℂ) := by
      rw [← Complex.Gamma_ofReal]; push_cast; rfl
    have hw : (W : ℂ) ^ (-((b : ℂ) + N)) = ((W ^ (-(b + N)) : ℝ) : ℂ) := by
      rw [ofReal_cpow hW.le]; push_cast; rfl
    rw [hg, hw, hK]; push_cast; ring
  rw [hKc]
  have hC0 : 0 ≤ C := setIntegral_nonneg measurableSet_Ioo hg0
  -- pointwise form
  have hpt : ∀ r ∈ Ioi (0 : ℝ), Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) *
      ((-((r : ℂ) * exp (θ * I))) ^ N * q r)) = ((-1) ^ N * ph) * ((ρ r : ℂ) * q r) := by
    intro r hr
    have h := airySt_term_eq (b := b) (W := W) hθ N hr
    rw [neg_pow ((r : ℂ) * exp (θ * I)) N]
    rw [show Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) *
      ((-1) ^ N * ((r : ℂ) * exp (θ * I)) ^ N * q r)) = (-1) ^ N * q r *
      (Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ ((b : ℂ) - 1) *
      ((r : ℂ) * exp (θ * I)) ^ N)) by ring, h, hρ, hph]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  -- bounds on q
  have hqn : ∀ r : ℝ, 0 ≤ r → ‖q r‖ ≤ C := fun r hr =>
    (airyDer_inner_bounds hgm hg0 hgi hcos hr).1
  have hqre : ∀ r : ℝ, 0 ≤ r → 0 ≤ (q r).re ∧ (q r).re ≤ C := fun r hr =>
    (airyDer_inner_bounds hgm hg0 hgi hcos hr).2
  -- integrability of ρ q
  have hρi : IntegrableOn ρ (Ioi 0) := stRem_integrableOn_rpow_exp (by linarith) hW
  have hqm : AEStronglyMeasurable q (volume.restrict (Ioi 0)) := by
    have hG : StronglyMeasurable (Function.uncurry fun (r τ : ℝ) =>
        (g τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹) := by
      refine Measurable.stronglyMeasurable ?_
      fun_prop
    exact (hG.integral_prod_right (ν := volume.restrict (Ioo 0 1))).aestronglyMeasurable
  have hJi : IntegrableOn (fun r => (ρ r : ℂ) * q r) (Ioi 0) := by
    refine Integrable.mono' (hρi.mul_const C) ((hρi.ofReal (𝕜 := ℂ)).aestronglyMeasurable.mul hqm) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    have hr : (0 : ℝ) < r := hr
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hqn r hr.le) (by positivity)
  set J : ℂ := ∫ r in Ioi (0 : ℝ), (ρ r : ℂ) * q r with hJ
  have hJre : J.re = ∫ r in Ioi (0 : ℝ), ρ r * (q r).re := by
    rw [hJ, ← RCLike.re_to_complex, ← integral_re hJi]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [RCLike.re_to_complex]; rw [re_ofReal_mul]
  have hρq : IntegrableOn (fun r => ρ r * (q r).re) (Ioi 0) := by
    refine (hJi.re).congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp only [RCLike.re_to_complex]; rw [re_ofReal_mul]
  have hρ0 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ ρ r := fun r hr => by
    have hr : (0 : ℝ) < r := hr
    simp only [hρ]; positivity
  have hJ0 : 0 ≤ J.re := by
    rw [hJre]; exact setIntegral_nonneg measurableSet_Ioi fun r hr =>
      mul_nonneg (hρ0 r hr) (hqre r (le_of_lt hr)).1
  have hJ1 : J.re ≤ C * K := by
    rw [hJre]
    calc ∫ r in Ioi (0 : ℝ), ρ r * (q r).re ≤ ∫ r in Ioi (0 : ℝ), ρ r * C :=
          setIntegral_mono_on hρq (hρi.mul_const C) measurableSet_Ioi fun r hr =>
            mul_le_mul_of_nonneg_left (hqre r (le_of_lt hr)).2 (hρ0 r hr)
      _ = C * K := by
          rw [integral_mul_const, hρ, airySt_gamma_int hbN hW, hK]; ring
  rcases eq_or_lt_of_le hC0 with hC0' | hCpos
  · -- degenerate weight
    have hJz : J = 0 := by
      have : ‖J‖ ≤ 0 := by
        rw [hJ]
        refine norm_integral_le_of_norm_le (g := fun _ => (0 : ℝ)) (integrable_zero _ _ _) ?_
          |>.trans (by simp)
        refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
        have hr : (0 : ℝ) < r := hr
        rw [norm_mul]
        have := hqn r hr.le
        rw [← hC0'] at this
        nlinarith [norm_nonneg (q r), norm_nonneg ((ρ r : ℂ))]
      exact norm_le_zero_iff.mp this
    refine ⟨0, 0, le_rfl, zero_le_one, ?_⟩
    rw [hJz, ← hC0']; simp
  · refine ⟨J.re / (C * K), J.im / (C * K), div_nonneg hJ0 (by positivity),
      (div_le_one (by positivity)).mpr hJ1, ?_⟩
    have hCK : ((C * K : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
    have hAB : (((J.re / (C * K) : ℝ) : ℂ) + ((J.im / (C * K) : ℝ) : ℂ) * I) =
        J / ((C * K : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [add_re, ofReal_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, div_ofReal_re]; ring
      · rw [add_im, ofReal_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, div_ofReal_im]; ring
    rw [hAB, div_mul_eq_mul_div, eq_div_iff hCK]
    push_cast; ring

/-- Measurability of `τ ↦ c τ^N w_a(τ)`. -/
theorem airyDer_measurable_w (a : ℝ) (N : ℕ) (c : ℝ) :
    Measurable fun τ : ℝ => c * (τ ^ N * airySt_w a τ) := by
  unfold airySt_w; fun_prop

/-- **The Ai remainder on `|arg z| ≤ π/3`** is `(A + iB)` times the first neglected term,
`0 ≤ A ≤ 1`. -/
theorem airyDer_ai_ratio {z : ℂ} (hz : z ≠ 0) (harg : |arg z| ≤ π / 3) (N : ℕ) :
    ∃ A B : ℝ, 0 ≤ A ∧ A ≤ 1 ∧
      airyRemainder .ai N z = (A + B * I) * (airyExpansionCoeff .ai N / airyZetaComplex z ^ N) := by
  have hπ := Real.pi_pos
  have harg' : |arg z| < 2 * π / 3 := by linarith
  obtain ⟨h1, h2⟩ := airySt_ai_remainder hz harg' N
  have hθ := airySt_theta_lt harg'
  have hcos : 0 ≤ Real.cos (-(3 / 2 * arg z)) := by
    rw [Real.cos_neg]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [(abs_le.mp harg).1],
      by linarith [(abs_le.mp harg).2]⟩
  have hW : 0 < Real.exp (log 2 + airyLogZeta z).re := Real.exp_pos _
  rw [h1, h2, airySt_rem_repr (a := 5 / 6) (b := 1 / 6) (by norm_num) (by norm_num) (by norm_num)
    hW hθ N (airySt_hint hθ hW)]
  set c : ℝ := 1 / (Real.Gamma (5 / 6) * Real.Gamma (1 - 5 / 6)) with hc
  have hQ : ∀ t : ℂ, airySt_Q (5 / 6) N t = ∫ τ in Ioo (0 : ℝ) 1,
      ((c * (τ ^ N * airySt_w (5 / 6) τ) : ℝ) : ℂ) * (1 + t * τ)⁻¹ := by
    intro t; unfold airySt_Q; rw [← hc, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    push_cast; ring
  simp_rw [hQ]
  have hc0 : 0 < c := by
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 5 / 6 by norm_num)
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 - 5 / 6 by norm_num)
    positivity
  obtain ⟨A, B, hA0, hA1, hE⟩ := airyDer_ray_ratio (b := 1 / 6) (by norm_num) hW hθ hcos N
    (airyDer_measurable_w (5 / 6) N c)
    (fun τ hτ => mul_nonneg hc0.le (mul_nonneg (pow_nonneg hτ.1.le _) (airySt_w_nonneg _ hτ)))
    ((airySt_integrableOn_w (by norm_num) (by norm_num) N).const_mul c)
  refine ⟨A, B, hA0, hA1, ?_⟩
  rw [hE]
  have hcoef : ((-1) ^ N * ∫ τ in Ioo (0 : ℝ) 1, c * (τ ^ N * airySt_w (5 / 6) τ) : ℝ) =
      airySt_coef (5 / 6) N := by
    rw [integral_const_mul, airySt_moment (by norm_num) (by norm_num) N, airySt_coef, hc]
    have h1 : Real.Gamma (1 - 5 / 6) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
    have h2 : Real.Gamma (5 / 6) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
    field_simp
  rw [hcoef]; unfold airySt_T; ring

/-- `cos (w - π/4)` and `sin (w - π/4)` through `e^{∓iw}`. -/
theorem airyDer_cos_sin (w : ℂ) :
    cos (w - π / 4) = exp (π * I / 4) / 2 * exp (-(w * I)) + exp (-(π * I / 4)) / 2 * exp (w * I) ∧
    sin (w - π / 4) =
      I * (exp (π * I / 4) / 2 * exp (-(w * I)) - exp (-(π * I / 4)) / 2 * exp (w * I)) := by
  have e1 : exp ((w - π / 4) * I) = exp (-(π * I / 4)) * exp (w * I) := by
    rw [← exp_add]; congr 1; ring
  have e2 : exp (-(w - π / 4) * I) = exp (π * I / 4) * exp (-(w * I)) := by
    rw [← exp_add]; congr 1; ring
  constructor
  · rw [Complex.cos, e1, e2]; ring
  · rw [Complex.sin, e1, e2]
    field_simp

/-- `Ai(-z)` through the even and odd parts of the normalized `Ai`, exactly (DLMF 9.7.9). -/
theorem airyDer_airyAi_neg {z : ℂ} (hz0 : z ≠ 0) (hz3 : |arg z| < 2 * π / 3) :
    airyAi (-z) = airyOscPrefactor .ai z *
      (cos (airyZetaComplex z - π / 4) * airyRot_even (fun w => airyAi w / airyPrefactor .ai w) z +
        sin (airyZetaComplex z - π / 4) *
          airyRot_odd (fun w => airyAi w / airyPrefactor .ai w) z) := by
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
  have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hp1 := airyRot_prefactor_ne_zero .ai (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
  have hp2 := airyRot_prefactor_ne_zero .ai
    (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
  obtain ⟨hc, hs⟩ := airyDer_cos_sin (airyZetaComplex z)
  rw [hc, hs]
  rw [airyRot_airyAi_neg z]
  rw [show airyAi (z * exp ((π / 3 : ℝ) * I)) = airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) *
      (airyAi (z * exp ((π / 3 : ℝ) * I)) / airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I))) by
      field_simp,
    show airyAi (z * exp ((-(π / 3) : ℝ) * I)) =
      airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) *
      (airyAi (z * exp ((-(π / 3) : ℝ) * I)) /
        airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
  rw [← mul_assoc, ← mul_assoc]
  rw [airyRot_decomp (fun w => airyAi w / airyPrefactor .ai w)]
  have ep : exp (π * I / 3) * airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) =
      airyOscPrefactor .ai z * (exp (π * I / 4) / 2 * exp (-(airyZetaComplex z * I))) := by
    simp only [airyPrefactor, airyOscPrefactor]
    rw [d1, d3, u4, u3]
    field_simp
    rw [hu]; ring_nf
  have em : exp (-π * I / 3) * airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) =
      airyOscPrefactor .ai z * (exp (-(π * I / 4)) / 2 * exp (airyZetaComplex z * I)) := by
    simp only [airyPrefactor, airyOscPrefactor]
    rw [d2, d4, um4, um3, neg_neg]
    field_simp
    rw [hu]; ring_nf
  rw [ep, em]
  ring

/-- `Bi(-z)` through the even and odd parts of the normalized `Ai`, exactly (DLMF 9.7.11). -/
theorem airyDer_airyBi_neg {z : ℂ} (hz0 : z ≠ 0) (hz3 : |arg z| < 2 * π / 3) :
    airyBi (-z) = airyOscPrefactor .ai z *
      (-sin (airyZetaComplex z - π / 4) *
          airyRot_even (fun w => airyAi w / airyPrefactor .ai w) z +
        cos (airyZetaComplex z - π / 4) *
          airyRot_odd (fun w => airyAi w / airyPrefactor .ai w) z) := by
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
  have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hp1 := airyRot_prefactor_ne_zero .ai
    (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
  have hp2 := airyRot_prefactor_ne_zero .ai
    (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
  have hcs : cos (airyZetaComplex z - π / 4) =
      I * (exp (-(π * I / 4)) / 2 * exp (-(airyZetaComplex z * I)) -
        exp (π * I / 4) / 2 * exp (airyZetaComplex z * I)) ∧
      -sin (airyZetaComplex z - π / 4) = exp (-(π * I / 4)) / 2 * exp (-(airyZetaComplex z * I)) +
        exp (π * I / 4) / 2 * exp (airyZetaComplex z * I) := by
    rw [show cos (airyZetaComplex z - π / 4) = sin (airyZetaComplex z - π / 4 + π / 2) from
        (Complex.sin_add_pi_div_two _).symm,
      show sin (airyZetaComplex z - π / 4) = -cos (airyZetaComplex z - π / 4 + π / 2) by
        rw [Complex.cos_add_pi_div_two]; ring]
    simp only [Complex.cos, Complex.sin]
    have e1 : exp ((airyZetaComplex z - π / 4 + π / 2) * I) =
        exp (π * I / 4) * exp (airyZetaComplex z * I) := by
      rw [← exp_add]; congr 1; ring
    have e2 : exp (-(airyZetaComplex z - π / 4 + π / 2) * I) =
        exp (-(π * I / 4)) * exp (-(airyZetaComplex z * I)) := by
      rw [← exp_add]; congr 1; ring
    rw [e1, e2]
    constructor
    · field_simp
    · ring
  rw [hcs.1, hcs.2]
  rw [airyRot_airyBi_neg z]
  rw [show airyAi (z * exp ((π / 3 : ℝ) * I)) =
      airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) *
      (airyAi (z * exp ((π / 3 : ℝ) * I)) /
        airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I))) by field_simp,
    show airyAi (z * exp ((-(π / 3) : ℝ) * I)) =
      airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) *
      (airyAi (z * exp ((-(π / 3) : ℝ) * I)) /
        airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
  rw [← mul_assoc, ← mul_assoc]
  rw [airyRot_decomp (fun w => airyAi w / airyPrefactor .ai w)]
  have ep : exp (-π * I / 6) * airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) =
      airyOscPrefactor .ai z *
        (exp (-(π * I / 4)) / 2 * exp (-(airyZetaComplex z * I))) := by
    simp only [airyPrefactor, airyOscPrefactor]
    rw [d1, d3, ← hu, um2, um3]
    field_simp
  have em : exp (π * I / 6) * airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) =
      airyOscPrefactor .ai z * (exp (π * I / 4) / 2 * exp (airyZetaComplex z * I)) := by
    simp only [airyPrefactor, airyOscPrefactor]
    rw [d2, d4, ← hu, u2, u3, neg_neg]
    field_simp
  rw [ep, em]
  ring

/-- The even part of `(Σ_{k<2N} c_k (iZ)^{-k} + Σ_{k<2N} c_k (-iZ)^{-k})/2`. -/
theorem airyDer_sum_even (c : ℕ → ℂ) {Z : ℂ} (hZ : Z ≠ 0) (N : ℕ) :
    (∑ k ∈ Finset.range (2 * N), c k / (Z * I) ^ k +
        ∑ k ∈ Finset.range (2 * N), c k / (-(Z * I)) ^ k) / 2 =
      ∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * c (2 * j) / Z ^ (2 * j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hm : ((-1 : ℂ) ^ N) * (-1) ^ N = 1 := by rw [← mul_pow]; norm_num
    have hm0 : ((-1 : ℂ) ^ N) ≠ 0 := pow_ne_zero _ (by norm_num)
    have p1 : (Z * I) ^ (2 * N) = (-1) ^ N * Z ^ (2 * N) := by
      rw [mul_pow, pow_mul I, I_sq]; ring
    have p2 : (-(Z * I)) ^ (2 * N) = (-1) ^ N * Z ^ (2 * N) := by
      rw [pow_mul, neg_sq, ← pow_mul, p1]
    have p3 : (Z * I) ^ (2 * N + 1) = (-1) ^ N * Z ^ (2 * N) * (Z * I) := by
      rw [pow_succ, p1]
    have p4 : (-(Z * I)) ^ (2 * N + 1) = -((-1) ^ N * Z ^ (2 * N) * (Z * I)) := by
      rw [pow_succ, p2]; ring
    have hZ2 : Z ^ (2 * N) ≠ 0 := pow_ne_zero _ hZ
    have hs : ∀ f : ℕ → ℂ, ∑ k ∈ Finset.range (2 * (N + 1)), f k =
        ∑ k ∈ Finset.range (2 * N), f k + f (2 * N) + f (2 * N + 1) := fun f => by
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ]
    have key : (c (2 * N) / (Z * I) ^ (2 * N) + c (2 * N + 1) / (Z * I) ^ (2 * N + 1) +
        (c (2 * N) / (-(Z * I)) ^ (2 * N) + c (2 * N + 1) / (-(Z * I)) ^ (2 * N + 1))) / 2 =
        (-1) ^ N * c (2 * N) / Z ^ (2 * N) := by
      rw [p1, p2, p3, p4]
      have hI : I ≠ 0 := I_ne_zero
      field_simp
      linear_combination (-(2 * c (2 * N) * Z * I)) * hm
    rw [hs, hs, Finset.sum_range_succ]
    linear_combination ih + key

/-- The odd part of `(Σ_{k≤2N} c_k (iZ)^{-k} - Σ_{k≤2N} c_k (-iZ)^{-k})/(2i)`. -/
theorem airyDer_sum_odd (c : ℕ → ℂ) {Z : ℂ} (hZ : Z ≠ 0) (N : ℕ) :
    (∑ k ∈ Finset.range (2 * N + 1), c k / (Z * I) ^ k -
        ∑ k ∈ Finset.range (2 * N + 1), c k / (-(Z * I)) ^ k) / (2 * I) =
      ∑ j ∈ Finset.range N, -((-1 : ℂ) ^ j * c (2 * j + 1)) / Z ^ (2 * j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hm : ((-1 : ℂ) ^ N) * (-1) ^ N = 1 := by rw [← mul_pow]; norm_num
    have hm0 : ((-1 : ℂ) ^ N) ≠ 0 := pow_ne_zero _ (by norm_num)
    have p1 : (Z * I) ^ (2 * N) = (-1) ^ N * Z ^ (2 * N) := by
      rw [mul_pow, pow_mul I, I_sq]; ring
    have p3 : (Z * I) ^ (2 * N + 1) = (-1) ^ N * Z ^ (2 * N) * (Z * I) := by
      rw [pow_succ, p1]
    have p4 : (-(Z * I)) ^ (2 * N + 1) = -((-1) ^ N * Z ^ (2 * N) * (Z * I)) := by
      rw [pow_succ, pow_mul, neg_sq, ← pow_mul, p1]; ring
    have p5 : (Z * I) ^ (2 * N + 2) = -((-1) ^ N * Z ^ (2 * N) * Z ^ 2) := by
      rw [pow_succ, pow_succ, p1]; ring_nf; rw [I_sq]; ring
    have p6 : (-(Z * I)) ^ (2 * N + 2) = -((-1) ^ N * Z ^ (2 * N) * Z ^ 2) := by
      rw [pow_succ, pow_succ, pow_mul, neg_sq, ← pow_mul, p1]; ring_nf; rw [I_sq]; ring
    have hZ2 : Z ^ (2 * N) ≠ 0 := pow_ne_zero _ hZ
    have hs : ∀ f : ℕ → ℂ, ∑ k ∈ Finset.range (2 * (N + 1) + 1), f k =
        ∑ k ∈ Finset.range (2 * N + 1), f k + f (2 * N + 1) + f (2 * N + 2) := fun f => by
      rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ]
    have key : (c (2 * N + 1) / (Z * I) ^ (2 * N + 1) + c (2 * N + 2) / (Z * I) ^ (2 * N + 2) -
        (c (2 * N + 1) / (-(Z * I)) ^ (2 * N + 1) + c (2 * N + 2) / (-(Z * I)) ^ (2 * N + 2))) /
          (2 * I) = -((-1) ^ N * c (2 * N + 1)) / Z ^ (2 * N + 1) := by
      rw [p3, p4, p5, p6]
      have hI : I ≠ 0 := I_ne_zero
      field_simp
      linear_combination (-(2 * c (2 * N + 1) * Z ^ 2 * Z ^ (2 * N))) * hm +
        (2 * c (2 * N + 1) * Z ^ 2 * Z ^ (2 * N) * (-1) ^ N * (-1) ^ N) * I_sq
    rw [hs, hs, Finset.sum_range_succ (fun j => -((-1 : ℂ) ^ j * c (2 * j + 1)) / Z ^ (2 * j + 1)) N]
    linear_combination ih + key

/-- The normalized `Ai`. -/
theorem airyDer_comp_false {x : ℝ} (hx : 0 < x) :
    airyOscComponent false 0 x = airyRot_even (fun w => airyAi w / airyPrefactor .ai w) x ∧
    airyOscComponent false 1 x = airyRot_odd (fun w => airyAi w / airyPrefactor .ai w) x := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x : ℂ)| < 2 * π / 3 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  have hA := airyDer_airyAi_neg hx0 harg
  have hB := airyDer_airyBi_neg hx0 harg
  rw [airyReal_zeta_ofReal hx] at hA hB
  have hP : airyOscPrefactor .ai (x : ℂ) ≠ 0 := by
    simp only [airyOscPrefactor]
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : (x : ℂ) ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
    exact one_div_ne_zero (mul_ne_zero hπs hq)
  have hcs := Complex.cos_sq_add_sin_sq (((airyZeta x : ℝ) : ℂ) - π / 4)
  simp only [airyOscComponent, Bool.false_eq_true, ite_false, Fin.val_zero, Fin.val_one,
    ite_true, one_ne_zero]
  rw [hA, hB]
  constructor
  · rw [div_eq_iff hP]
    linear_combination (airyOscPrefactor .ai (x : ℂ) *
      airyRot_even (fun w => airyAi w / airyPrefactor .ai w) x) * hcs
  · rw [div_eq_iff hP]
    linear_combination (airyOscPrefactor .ai (x : ℂ) *
      airyRot_odd (fun w => airyAi w / airyPrefactor .ai w) x) * hcs

/-- `Ai'` is real on the real axis (as in `DLMF.Airy.ModulusPhase`, which this file does not
import). -/
theorem airyDer_aiDeriv_ofReal_im (x : ℝ) : (airyAiDeriv x).im = 0 := by
  have h := ((hasDerivAt_airyAi x).comp_ofReal).hasFDerivAt.restrictScalars ℝ
  have h1 : HasDerivAt (fun t : ℝ => (airyAi t).im) (airyAiDeriv x).im x := by
    have := (Complex.imCLM.hasFDerivAt.comp x h).hasDerivAt
    simpa [Function.comp_def] using this
  have h0 : (fun t : ℝ => (airyAi t).im) = fun _ => 0 := funext airyAi_ofReal_im
  rw [h0] at h1
  exact (h1.unique (hasDerivAt_const x 0))

/-- `Bi'` is real on the real axis. -/
theorem airyDer_biDeriv_ofReal_im (x : ℝ) : (airyBiDeriv x).im = 0 := by
  have h := ((hasDerivAt_airyBi x).comp_ofReal).hasFDerivAt.restrictScalars ℝ
  have h1 : HasDerivAt (fun t : ℝ => (airyBi t).im) (airyBiDeriv x).im x := by
    have := (Complex.imCLM.hasFDerivAt.comp x h).hasDerivAt
    simpa [Function.comp_def] using this
  have h0 : (fun t : ℝ => (airyBi t).im) = fun _ => 0 := funext airyBi_ofReal_im
  rw [h0] at h1
  exact (h1.unique (hasDerivAt_const x 0))

/-- A complex number with zero imaginary part is the cast of its real part. -/
theorem airyDer_eq_ofReal {w : ℂ} (h : w.im = 0) : w = (w.re : ℂ) :=
  Complex.ext (by simp) (by simp [h])

/-- The oscillatory components are real on the positive axis. -/
theorem airyDer_comp_im (derivative : Bool) (parity : Fin 2) {x : ℝ} (hx : 0 < x) :
    (airyOscComponent derivative parity x).im = 0 := by
  have hneg : (-(x : ℂ)) = ((-x : ℝ) : ℂ) := by push_cast; ring
  have hA := airyDer_eq_ofReal (w := airyAi (-(x : ℂ))) (by rw [hneg]; exact airyAi_ofReal_im _)
  have hB := airyDer_eq_ofReal (w := airyBi (-(x : ℂ))) (by rw [hneg]; exact airyBi_ofReal_im _)
  have hA' := airyDer_eq_ofReal (w := airyAiDeriv (-(x : ℂ)))
    (by rw [hneg]; exact airyDer_aiDeriv_ofReal_im _)
  have hB' := airyDer_eq_ofReal (w := airyBiDeriv (-(x : ℂ)))
    (by rw [hneg]; exact airyDer_biDeriv_ofReal_im _)
  have hq : (x : ℂ) ^ (1 / 4 : ℂ) = ((x ^ (1 / 4 : ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow hx.le]; push_cast; rfl
  have hc : cos (((airyZeta x : ℝ) : ℂ) - π / 4) = ((Real.cos (airyZeta x - π / 4) : ℝ) : ℂ) := by
    push_cast; rfl
  have hs : sin (((airyZeta x : ℝ) : ℂ) - π / 4) = ((Real.sin (airyZeta x - π / 4) : ℝ) : ℂ) := by
    push_cast; rfl
  cases derivative <;> simp only [airyOscComponent, Bool.false_eq_true, ite_false, ite_true,
    airyOscPrefactor, hq, hc, hs] <;> split_ifs <;>
    first
    | rw [hA, hB]; norm_cast
    | rw [hA', hB']; norm_cast

/-- The truncated oscillatory sums are real on the positive axis. -/
theorem airyDer_oscSum_im (derivative : Bool) (parity N : ℕ) {x : ℝ} (hx : 0 < x) :
    (airyOscSum derivative parity N x).im = 0 := by
  unfold airyOscSum
  rw [airyReal_zeta_ofReal hx, Complex.im_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [show (-1 : ℂ) ^ k * ((if derivative then airyV (2 * k + parity) else airyU (2 * k + parity) : ℝ) : ℂ)
      / ((airyZeta x : ℝ) : ℂ) ^ (2 * k + parity) = (((-1) ^ k *
        (if derivative then airyV (2 * k + parity) else airyU (2 * k + parity)) /
          airyZeta x ^ (2 * k + parity) : ℝ) : ℂ) by push_cast; rfl]
  exact ofReal_im _

/-- A real number written as `(A + iB) τ` with `τ` real and `0 ≤ A ≤ 1`. -/
theorem airyDer_assemble {D τ : ℂ} {A B τr : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hτ : τ = τr)
    (hD : D = (A + B * I) * τ) (hDim : D.im = 0) : ‖D‖ ≤ ‖τ‖ ∧ D.re = A * τr := by
  have hre : D.re = A * τr := by rw [hD, hτ]; simp
  refine ⟨?_, hre⟩
  rw [airyDer_eq_ofReal hDim, hre, hτ, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg hA0]
  exact mul_le_of_le_one_left (abs_nonneg _) hA1

/-- The `Ai` coefficients: even ones are `u_{2j}`, odd ones `-u_{2j+1}`. -/
theorem airyDer_coeff_ai (j : ℕ) :
    airyExpansionCoeff .ai (2 * j) = airyU (2 * j) ∧
      airyExpansionCoeff .ai (2 * j + 1) = -(airyU (2 * j + 1) : ℂ) := by
  have h := airyRot_coeff_parity .ai (Or.inl rfl) j
  simpa using h

/-- Rotating `x > 0` by `±π/3`. -/
theorem airyDer_rot_data {x : ℝ} (hx : 0 < x) :
    (x : ℂ) * exp ((π / 3 : ℝ) * I) ≠ 0 ∧ |arg ((x : ℂ) * exp ((π / 3 : ℝ) * I))| ≤ π / 3 ∧
    (x : ℂ) * exp ((-(π / 3) : ℝ) * I) ≠ 0 ∧ |arg ((x : ℂ) * exp ((-(π / 3) : ℝ) * I))| ≤ π / 3 := by
  have hπ := Real.pi_pos
  refine ⟨airyRot_ofReal_mul_exp_ne_zero hx _, ?_, airyRot_ofReal_mul_exp_ne_zero hx _, ?_⟩
  · rw [airyRot_arg hx (by linarith) (by linarith), abs_of_pos (by positivity)]
  · rw [airyRot_arg hx (by linarith) (by linarith), abs_neg, abs_of_pos (by positivity)]

/-- **Signed even bound, abstract form.** If the remainders of `Φ` after `2N` terms at
`x e^{±iπ/3}` are `(A + iB)` times the first neglected term with `0 ≤ A ≤ 1`, and the even part
minus its truncated series is real, then that difference is enclosed by its first neglected term,
with the same sign. -/
theorem airyDer_even_bound (Φ : ℂ → ℂ) (c : ℕ → ℂ) (u : ℕ → ℝ) (hc : ∀ j, c (2 * j) = u (2 * j))
    {x : ℝ} (hx : 0 < x) (N : ℕ)
    (hp : ∃ A B : ℝ, 0 ≤ A ∧ A ≤ 1 ∧ Φ ((x : ℂ) * exp ((π / 3 : ℝ) * I)) -
      ∑ k ∈ Finset.range (2 * N), c k / airyZetaComplex ((x : ℂ) * exp ((π / 3 : ℝ) * I)) ^ k =
        (A + B * I) * (c (2 * N) / airyZetaComplex ((x : ℂ) * exp ((π / 3 : ℝ) * I)) ^ (2 * N)))
    (hm : ∃ A B : ℝ, 0 ≤ A ∧ A ≤ 1 ∧ Φ ((x : ℂ) * exp ((-(π / 3) : ℝ) * I)) -
      ∑ k ∈ Finset.range (2 * N), c k / airyZetaComplex ((x : ℂ) * exp ((-(π / 3) : ℝ) * I)) ^ k =
        (A + B * I) * (c (2 * N) / airyZetaComplex ((x : ℂ) * exp ((-(π / 3) : ℝ) * I)) ^ (2 * N)))
    (hre : (airyRot_even Φ x - ∑ j ∈ Finset.range N,
      (-1 : ℂ) ^ j * (u (2 * j) : ℂ) / airyZetaComplex x ^ (2 * j)).im = 0) :
    ‖airyRot_even Φ x - ∑ j ∈ Finset.range N,
        (-1 : ℂ) ^ j * (u (2 * j) : ℂ) / airyZetaComplex x ^ (2 * j)‖ ≤
        ‖(-1 : ℂ) ^ N * (u (2 * N) : ℂ) / airyZetaComplex x ^ (2 * N)‖ ∧
      0 ≤ (airyRot_even Φ x - ∑ j ∈ Finset.range N,
        (-1 : ℂ) ^ j * (u (2 * j) : ℂ) / airyZetaComplex x ^ (2 * j)).re *
        ((-1 : ℝ) ^ N * u (2 * N)) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x : ℂ)| < 2 * π / 3 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  obtain ⟨d1, d2, -, -⟩ := airyRot_third_data hx0 harg
  obtain ⟨Ap, Bp, hAp0, hAp1, hp⟩ := hp
  obtain ⟨Am, Bm, hAm0, hAm1, hm⟩ := hm
  set Z := airyZetaComplex (x : ℂ) with hZ
  have hZ0 : Z ≠ 0 := airySt_zeta_ne_zero hx0
  set τr : ℝ := (-1) ^ N * u (2 * N) / airyZeta x ^ (2 * N) with hτr
  have hτ : (-1 : ℂ) ^ N * (u (2 * N) : ℂ) / Z ^ (2 * N) = (τr : ℂ) := by
    rw [hZ, airyReal_zeta_ofReal hx, hτr]; push_cast; ring
  have p1 : (Z * I) ^ (2 * N) = (-1) ^ N * Z ^ (2 * N) := by
    rw [mul_pow, pow_mul I, I_sq]; ring
  have p2 : (-(Z * I)) ^ (2 * N) = (-1) ^ N * Z ^ (2 * N) := by
    rw [pow_mul, neg_sq, ← pow_mul, p1]
  have hm2 : ((-1 : ℂ) ^ N) * (-1) ^ N = 1 := by rw [← mul_pow]; norm_num
  have hZN : Z ^ (2 * N) ≠ 0 := pow_ne_zero _ hZ0
  have ht : ∀ W : ℂ, W ^ (2 * N) = (-1) ^ N * Z ^ (2 * N) →
      c (2 * N) / W ^ (2 * N) = (τr : ℂ) := by
    intro W hW
    rw [hW, hc N, ← hτ]
    field_simp
    linear_combination (-(u (2 * N) : ℂ)) * hm2
  rw [d1, ht _ p1] at hp
  rw [d2, ht _ p2] at hm
  have hE : airyRot_even Φ x - ∑ j ∈ Finset.range N,
      (-1 : ℂ) ^ j * (u (2 * j) : ℂ) / Z ^ (2 * j) =
      (((Ap + Am) / 2 : ℝ) + ((Bp + Bm) / 2 : ℝ) * I) * (τr : ℂ) := by
    have hS := airyDer_sum_even c hZ0 N
    simp only [hc] at hS
    rw [← hS, airyRot_even]
    push_cast at hp hm ⊢
    linear_combination (1 / 2 : ℂ) * hp + (1 / 2 : ℂ) * hm
  obtain ⟨h1, h2⟩ := airyDer_assemble (by linarith) (by linarith) rfl hE hre
  refine ⟨by rwa [hτ], ?_⟩
  rw [h2, hτr]
  have hz : 0 < airyZeta x := airyZeta_pos hx
  have : 0 ≤ ((-1 : ℝ) ^ N * u (2 * N)) ^ 2 / airyZeta x ^ (2 * N) := by positivity
  calc (0 : ℝ) ≤ (Ap + Am) / 2 * (((-1 : ℝ) ^ N * u (2 * N)) ^ 2 / airyZeta x ^ (2 * N)) :=
        mul_nonneg (by linarith) this
    _ = _ := by ring

/-- **Signed odd bound, abstract form.** -/
theorem airyDer_odd_bound (Φ : ℂ → ℂ) (c : ℕ → ℂ) (u : ℕ → ℝ)
    (hc : ∀ j, c (2 * j + 1) = -(u (2 * j + 1) : ℂ)) {x : ℝ} (hx : 0 < x) (N : ℕ)
    (hp : ∃ A B : ℝ, 0 ≤ A ∧ A ≤ 1 ∧ Φ ((x : ℂ) * exp ((π / 3 : ℝ) * I)) -
      ∑ k ∈ Finset.range (2 * N + 1), c k / airyZetaComplex ((x : ℂ) * exp ((π / 3 : ℝ) * I)) ^ k =
        (A + B * I) * (c (2 * N + 1) /
          airyZetaComplex ((x : ℂ) * exp ((π / 3 : ℝ) * I)) ^ (2 * N + 1)))
    (hm : ∃ A B : ℝ, 0 ≤ A ∧ A ≤ 1 ∧ Φ ((x : ℂ) * exp ((-(π / 3) : ℝ) * I)) -
      ∑ k ∈ Finset.range (2 * N + 1), c k /
        airyZetaComplex ((x : ℂ) * exp ((-(π / 3) : ℝ) * I)) ^ k =
        (A + B * I) * (c (2 * N + 1) /
          airyZetaComplex ((x : ℂ) * exp ((-(π / 3) : ℝ) * I)) ^ (2 * N + 1)))
    (hre : (airyRot_odd Φ x - ∑ j ∈ Finset.range N,
      (-1 : ℂ) ^ j * (u (2 * j + 1) : ℂ) / airyZetaComplex x ^ (2 * j + 1)).im = 0) :
    ‖airyRot_odd Φ x - ∑ j ∈ Finset.range N,
        (-1 : ℂ) ^ j * (u (2 * j + 1) : ℂ) / airyZetaComplex x ^ (2 * j + 1)‖ ≤
        ‖(-1 : ℂ) ^ N * (u (2 * N + 1) : ℂ) / airyZetaComplex x ^ (2 * N + 1)‖ ∧
      0 ≤ (airyRot_odd Φ x - ∑ j ∈ Finset.range N,
        (-1 : ℂ) ^ j * (u (2 * j + 1) : ℂ) / airyZetaComplex x ^ (2 * j + 1)).re *
        ((-1 : ℝ) ^ N * u (2 * N + 1)) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x : ℂ)| < 2 * π / 3 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  obtain ⟨d1, d2, -, -⟩ := airyRot_third_data hx0 harg
  obtain ⟨Ap, Bp, hAp0, hAp1, hp⟩ := hp
  obtain ⟨Am, Bm, hAm0, hAm1, hm⟩ := hm
  set Z := airyZetaComplex (x : ℂ) with hZ
  have hZ0 : Z ≠ 0 := airySt_zeta_ne_zero hx0
  set τr : ℝ := (-1) ^ N * u (2 * N + 1) / airyZeta x ^ (2 * N + 1) with hτr
  have hτ : (-1 : ℂ) ^ N * (u (2 * N + 1) : ℂ) / Z ^ (2 * N + 1) = (τr : ℂ) := by
    rw [hZ, airyReal_zeta_ofReal hx, hτr]; push_cast; ring
  have p1 : (Z * I) ^ (2 * N) = (-1) ^ N * Z ^ (2 * N) := by
    rw [mul_pow, pow_mul I, I_sq]; ring
  have p3 : (Z * I) ^ (2 * N + 1) = (-1) ^ N * Z ^ (2 * N) * (Z * I) := by
    rw [pow_succ, p1]
  have p4 : (-(Z * I)) ^ (2 * N + 1) = -((-1) ^ N * Z ^ (2 * N) * (Z * I)) := by
    rw [pow_succ, pow_mul, neg_sq, ← pow_mul, p1]; ring
  have hm2 : ((-1 : ℂ) ^ N) * (-1) ^ N = 1 := by rw [← mul_pow]; norm_num
  have hZN : Z ^ (2 * N) ≠ 0 := pow_ne_zero _ hZ0
  have hI : I ≠ 0 := I_ne_zero
  have htp : c (2 * N + 1) / (Z * I) ^ (2 * N + 1) = I * (τr : ℂ) := by
    rw [p3, hc N, ← hτ, pow_succ]
    field_simp
    linear_combination (u (2 * N + 1) : ℂ) * hm2 +
      (-((u (2 * N + 1) : ℂ) * (-1) ^ N * (-1) ^ N)) * I_sq
  have htm : c (2 * N + 1) / (-(Z * I)) ^ (2 * N + 1) = -(I * (τr : ℂ)) := by
    rw [p4, div_neg, ← p3, htp]
  rw [d1, htp] at hp
  rw [d2, htm] at hm
  have hE : airyRot_odd Φ x - ∑ j ∈ Finset.range N,
      (-1 : ℂ) ^ j * (u (2 * j + 1) : ℂ) / Z ^ (2 * j + 1) =
      (((Ap + Am) / 2 : ℝ) + ((Bp + Bm) / 2 : ℝ) * I) * (τr : ℂ) := by
    have hS := airyDer_sum_odd c hZ0 N
    have hS' : ∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * (u (2 * j + 1) : ℂ) / Z ^ (2 * j + 1) =
        ∑ j ∈ Finset.range N, -((-1 : ℂ) ^ j * c (2 * j + 1)) / Z ^ (2 * j + 1) :=
      Finset.sum_congr rfl fun j _ => by rw [hc j]; ring
    rw [hS', ← hS, airyRot_odd]
    rw [div_sub_div_same, div_eq_iff (mul_ne_zero two_ne_zero hI)]
    push_cast at hp hm ⊢
    linear_combination hp - hm
  obtain ⟨h1, h2⟩ := airyDer_assemble (by linarith) (by linarith) rfl hE hre
  refine ⟨by rwa [hτ], ?_⟩
  rw [h2, hτr]
  have hz : 0 < airyZeta x := airyZeta_pos hx
  have : 0 ≤ ((-1 : ℝ) ^ N * u (2 * N + 1)) ^ 2 / airyZeta x ^ (2 * N + 1) := by positivity
  calc (0 : ℝ) ≤ (Ap + Am) / 2 *
        (((-1 : ℝ) ^ N * u (2 * N + 1)) ^ 2 / airyZeta x ^ (2 * N + 1)) :=
        mul_nonneg (by linarith) this
    _ = _ := by ring

/-- The remainder of the normalized `Ai` in the form used by the abstract bounds. -/
theorem airyDer_ai_ratio' {w : ℂ} (hw : w ≠ 0) (harg : |arg w| ≤ π / 3) (M : ℕ) :
    ∃ A B : ℝ, 0 ≤ A ∧ A ≤ 1 ∧ airyAi w / airyPrefactor .ai w -
      ∑ k ∈ Finset.range M, airyExpansionCoeff .ai k / airyZetaComplex w ^ k =
        (A + B * I) * (airyExpansionCoeff .ai M / airyZetaComplex w ^ M) := by
  obtain ⟨A, B, h0, h1, h⟩ := airyDer_ai_ratio hw harg M
  exact ⟨A, B, h0, h1, by rw [← h]; rfl⟩

/-- DLMF §9.7(iii) for the even subseries of the `Ai`, `Bi` oscillatory expansions. -/
theorem airyDer_osc_even {x : ℝ} (hx : 0 < x) (N : ℕ) :
    ‖airyOscComponent false 0 x - airyOscSum false 0 N x‖ ≤
        ‖(-1 : ℂ) ^ N * (airyU (2 * N) : ℂ) / airyZetaComplex x ^ (2 * N)‖ ∧
      0 ≤ (airyOscComponent false 0 x - airyOscSum false 0 N x).re *
        ((-1 : ℝ) ^ N * airyU (2 * N)) := by
  obtain ⟨hp0, hpa, hm0, hma⟩ := airyDer_rot_data hx
  have hS : airyOscSum false 0 N x = ∑ j ∈ Finset.range N,
      (-1 : ℂ) ^ j * (airyU (2 * j) : ℂ) / airyZetaComplex x ^ (2 * j) := by
    simp [airyOscSum]
  have hre := (airyDer_comp_im false 0 hx)
  have hre' := airyDer_oscSum_im false 0 N hx
  rw [hS] at hre'
  rw [(airyDer_comp_false hx).1] at hre ⊢
  rw [hS]
  exact airyDer_even_bound _ (airyExpansionCoeff .ai) airyU (fun j => (airyDer_coeff_ai j).1) hx N
    (airyDer_ai_ratio' hp0 hpa _) (airyDer_ai_ratio' hm0 hma _)
    (by rw [sub_im, hre, hre', sub_zero])

/-- DLMF §9.7(iii) for the odd subseries of the `Ai`, `Bi` oscillatory expansions. -/
theorem airyDer_osc_odd {x : ℝ} (hx : 0 < x) (N : ℕ) :
    ‖airyOscComponent false 1 x - airyOscSum false 1 N x‖ ≤
        ‖(-1 : ℂ) ^ N * (airyU (2 * N + 1) : ℂ) / airyZetaComplex x ^ (2 * N + 1)‖ ∧
      0 ≤ (airyOscComponent false 1 x - airyOscSum false 1 N x).re *
        ((-1 : ℝ) ^ N * airyU (2 * N + 1)) := by
  obtain ⟨hp0, hpa, hm0, hma⟩ := airyDer_rot_data hx
  have hS : airyOscSum false 1 N x = ∑ j ∈ Finset.range N,
      (-1 : ℂ) ^ j * (airyU (2 * j + 1) : ℂ) / airyZetaComplex x ^ (2 * j + 1) := by
    simp [airyOscSum]
  have hre := (airyDer_comp_im false 1 hx)
  have hre' := airyDer_oscSum_im false 1 N hx
  rw [hS] at hre'
  rw [(airyDer_comp_false hx).2] at hre ⊢
  rw [hS]
  exact airyDer_odd_bound _ (airyExpansionCoeff .ai) airyU (fun j => (airyDer_coeff_ai j).2) hx N
    (airyDer_ai_ratio' hp0 hpa _) (airyDer_ai_ratio' hm0 hma _)
    (by rw [sub_im, hre, hre', sub_zero])

/-- The binomial coefficients of `(1+t)^{1/6}`: `d_k = (-1)^k (-1/6)_k / k!`. -/
def airyDer_d (k : ℕ) : ℝ :=
  (-1) ^ k * (ascPochhammer ℝ k).eval (-1 / 6) / k.factorial

/-- The binomial coefficient of `(1+t)^{-5/6}` is `(-1)^k (5/6)_k / k!`. -/
theorem airyDer_c_eq (k : ℕ) :
    airySt_coef (5 / 6) k = (-1) ^ k * (ascPochhammer ℝ k).eval (5 / 6) / k.factorial := by
  have h := airySt_gamma_ratio_real k (x := 5 / 6) (by norm_num)
  have g := Real.Gamma_pos_of_pos (show (0 : ℝ) < 5 / 6 by norm_num)
  unfold airySt_coef
  rw [Real.Gamma_nat_eq_factorial, ← h]
  have hf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  field_simp

/-- `d_0 = 1`. -/
theorem airyDer_d_zero : airyDer_d 0 = 1 := by simp [airyDer_d]

/-- The zeroth binomial coefficient of `(1+t)^{-5/6}` is `1`. -/
theorem airyDer_c_zero : airySt_coef (5 / 6) 0 = 1 := by simp [airyDer_c_eq]

/-- `d_{k+1} = c_{k+1} + c_k`, from `(1+t)^{1/6} = (1+t)(1+t)^{-5/6}`. -/
theorem airyDer_d_succ (k : ℕ) :
    airyDer_d (k + 1) = airySt_coef (5 / 6) (k + 1) + airySt_coef (5 / 6) k := by
  rw [airyDer_c_eq, airyDer_c_eq]
  unfold airyDer_d
  have h1 : (ascPochhammer ℝ (k + 1)).eval (-1 / 6) = (-1 / 6) * (ascPochhammer ℝ k).eval (5 / 6) := by
    rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    norm_num
  rw [h1, ascPochhammer_succ_eval, Nat.factorial_succ]
  have hf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  push_cast
  field_simp
  ring

/-- `Σ_{k≤N} d_k t^k = (1+t) Σ_{k≤N} c_k t^k - c_N t^{N+1}`. -/
theorem airyDer_sum_id (t : ℂ) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (airyDer_d k : ℂ) * t ^ k =
      (1 + t) * ∑ k ∈ Finset.range (N + 1), (airySt_coef (5 / 6) k : ℂ) * t ^ k -
        (airySt_coef (5 / 6) N : ℂ) * t ^ (N + 1) := by
  induction N with
  | zero => simp [airyDer_d_zero, airyDer_c_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => (airySt_coef (5 / 6) k : ℂ) * t ^ k)
      (N + 1), airyDer_d_succ]
    push_cast; ring

/-- The weight `τ^N (1-τ) τ^{-1/6} (1-τ)^{-5/6}` of the `(1+t)^{1/6}` remainder, normalized. -/
def airyDer_g (N : ℕ) (τ : ℝ) : ℝ :=
  1 / (Real.Gamma (5 / 6) * Real.Gamma (1 - 5 / 6)) * (τ ^ N * (1 - τ) * airySt_w (5 / 6) τ)

/-- The weight `airyDer_g N` is nonnegative on `(0,1)`. -/
theorem airyDer_g_nonneg (N : ℕ) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) : 0 ≤ airyDer_g N τ := by
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 5 / 6 by norm_num)
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 - 5 / 6 by norm_num)
  unfold airyDer_g
  exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (pow_nonneg hτ.1.le _)
    (by linarith [hτ.2])) (airySt_w_nonneg _ hτ))

/-- The weight `airyDer_g N` is measurable. -/
theorem airyDer_g_measurable (N : ℕ) : Measurable (airyDer_g N) := by
  unfold airyDer_g airySt_w; fun_prop

/-- `τ^N (1-τ) w(τ) = τ^N w(τ) - τ^{N+1} w(τ)`. -/
theorem airyDer_g_eq (N : ℕ) {τ : ℝ} :
    τ ^ N * (1 - τ) * airySt_w (5 / 6) τ = τ ^ N * airySt_w (5 / 6) τ -
      τ ^ (N + 1) * airySt_w (5 / 6) τ := by ring

/-- `τ^N (1-τ) w_{5/6}(τ)` is integrable on `(0,1)`. -/
theorem airyDer_integrableOn_g0 (N : ℕ) :
    IntegrableOn (fun τ : ℝ => τ ^ N * (1 - τ) * airySt_w (5 / 6) τ) (Ioo 0 1) := by
  have h := (airySt_integrableOn_w (a := 5 / 6) (by norm_num) (by norm_num) N).sub
    (airySt_integrableOn_w (a := 5 / 6) (by norm_num) (by norm_num) (N + 1))
  exact h.congr_fun (fun τ _ => (airyDer_g_eq N).symm) measurableSet_Ioo

/-- The weight `airyDer_g N` is integrable on `(0,1)`. -/
theorem airyDer_integrableOn_g (N : ℕ) : IntegrableOn (airyDer_g N) (Ioo 0 1) :=
  (airyDer_integrableOn_g0 N).const_mul _

/-- **The `(1+t)^{1/6}` binomial remainder in Stieltjes form**: after `N+1` terms it is
`-(-t)^{N+1} ∫₀¹ g_N(τ) (1+tτ)⁻¹ dτ` with the nonnegative weight `g_N`. -/
theorem airyDer_binom_rem {t : ℂ} (ht : 1 + t ∈ slitPlane) (N : ℕ) :
    (1 + t) ^ (((1 / 6 : ℝ)) : ℂ) - ∑ k ∈ Finset.range (N + 1), (airyDer_d k : ℂ) * t ^ k =
      -((-t) ^ (N + 1) * ∫ τ in Ioo (0 : ℝ) 1, (airyDer_g N τ : ℂ) * (1 + t * τ)⁻¹) := by
  have h1t : 1 + t ≠ 0 := slitPlane_ne_zero ht
  have hpow : (1 + t) ^ (((1 / 6 : ℝ)) : ℂ) = (1 + t) * (1 + t) ^ (-(((5 / 6 : ℝ)) : ℂ)) := by
    rw [show (((1 / 6 : ℝ)) : ℂ) = 1 + -(((5 / 6 : ℝ)) : ℂ) by push_cast; ring, cpow_add _ _ h1t,
      cpow_one]
  have hb := airySt_binom_rem (a := 5 / 6) (by norm_num) (by norm_num) ht (N + 1)
  set c' : ℝ := 1 / (Real.Gamma (5 / 6) * Real.Gamma (1 - 5 / 6)) with hc'
  have hne : ∀ τ ∈ Ioo (0 : ℝ) 1, 1 + t * τ ≠ 0 := fun τ hτ =>
    slitPlane_ne_zero (airySt_one_add_mul_mem ht (Ioo_subset_Icc_self hτ))
  have hcont : ContinuousOn (fun τ : ℝ => (1 + t * τ)⁻¹) (Icc 0 1) :=
    ContinuousOn.inv₀ (by fun_prop) fun τ hτ => slitPlane_ne_zero (airySt_one_add_mul_mem ht hτ)
  have hi1 : IntegrableOn (fun τ : ℝ => ((τ ^ N * airySt_w (5 / 6) τ : ℝ) : ℂ)) (Ioo 0 1) :=
    (airySt_integrableOn_w (by norm_num) (by norm_num) N).ofReal
  have hi2 : IntegrableOn (fun τ : ℝ => ((τ ^ N * (1 - τ) * airySt_w (5 / 6) τ : ℝ) : ℂ) *
      (1 + t * τ)⁻¹) (Ioo 0 1) :=
    ((airyDer_integrableOn_g0 N).ofReal).mul_continuousOn_of_subset hcont measurableSet_Ioo
      isCompact_Icc Ioo_subset_Icc_self
  have hkey : (1 + t) * ∫ τ in Ioo (0 : ℝ) 1, ((τ ^ (N + 1) * airySt_w (5 / 6) τ : ℝ) : ℂ) *
      (1 + t * τ)⁻¹ = (∫ τ in Ioo (0 : ℝ) 1, ((τ ^ N * airySt_w (5 / 6) τ : ℝ) : ℂ)) -
        ∫ τ in Ioo (0 : ℝ) 1, ((τ ^ N * (1 - τ) * airySt_w (5 / 6) τ : ℝ) : ℂ) *
          (1 + t * τ)⁻¹ := by
    rw [← integral_const_mul, ← integral_sub hi1 hi2]
    refine setIntegral_congr_fun measurableSet_Ioo fun τ hτ => ?_
    have h := hne τ hτ
    push_cast
    field_simp
    ring
  have hmom : (c' : ℂ) * ∫ τ in Ioo (0 : ℝ) 1, ((τ ^ N * airySt_w (5 / 6) τ : ℝ) : ℂ) =
      (-1) ^ N * (airySt_coef (5 / 6) N : ℂ) := by
    have h1 : Real.Gamma (1 - 5 / 6) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
    have h2 : Real.Gamma (5 / 6) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
    have h3 : Real.Gamma (N + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hr : c' * (Real.Gamma (5 / 6 + N) * Real.Gamma (1 - 5 / 6) / Real.Gamma (N + 1)) =
        (-1) ^ N * airySt_coef (5 / 6) N := by
      rw [airySt_coef, show (-1 : ℝ) ^ N * ((-1) ^ N * Real.Gamma (5 / 6 + N) /
          (Real.Gamma (5 / 6) * Real.Gamma (N + 1))) = ((-1) ^ N * (-1) ^ N) *
            Real.Gamma (5 / 6 + N) / (Real.Gamma (5 / 6) * Real.Gamma (N + 1)) by ring,
        ← mul_pow, hc']
      norm_num
      field_simp
    rw [integral_complex_ofReal, airySt_moment (by norm_num) (by norm_num) N]
    exact_mod_cast hr
  have hg : ∫ τ in Ioo (0 : ℝ) 1, (airyDer_g N τ : ℂ) * (1 + t * τ)⁻¹ = (c' : ℂ) *
      ∫ τ in Ioo (0 : ℝ) 1, ((τ ^ N * (1 - τ) * airySt_w (5 / 6) τ : ℝ) : ℂ) * (1 + t * τ)⁻¹ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only [airyDer_g, hc']; push_cast; ring
  rw [hpow, airyDer_sum_id, hg]
  have hb' : (1 + t) ^ (-(((5 / 6 : ℝ)) : ℂ)) = ∑ k ∈ Finset.range (N + 1),
      (airySt_coef (5 / 6) k : ℂ) * t ^ k + (-t) ^ (N + 1) * ((c' : ℂ) *
        ∫ τ in Ioo (0 : ℝ) 1, ((τ ^ (N + 1) * airySt_w (5 / 6) τ : ℝ) : ℂ) * (1 + t * τ)⁻¹) := by
    rw [← hb]; ring
  rw [hb']
  have e : (1 + t) * ((-t) ^ (N + 1) * ((c' : ℂ) * ∫ τ in Ioo (0 : ℝ) 1,
      ((τ ^ (N + 1) * airySt_w (5 / 6) τ : ℝ) : ℂ) * (1 + t * τ)⁻¹)) =
      (-t) ^ (N + 1) * ((c' : ℂ) * ∫ τ in Ioo (0 : ℝ) 1, ((τ ^ N * airySt_w (5 / 6) τ : ℝ) : ℂ)) -
      (-t) ^ (N + 1) * ((c' : ℂ) * ∫ τ in Ioo (0 : ℝ) 1,
        ((τ ^ N * (1 - τ) * airySt_w (5 / 6) τ : ℝ) : ℂ) * (1 + t * τ)⁻¹) := by
    rw [← mul_sub, ← mul_sub, ← hkey]; ring
  have hm : ((-1 : ℂ) ^ N) * (-1) ^ N = 1 := by rw [← mul_pow]; norm_num
  rw [mul_add, e, hmom, neg_pow t (N + 1)]
  linear_combination (-(airySt_coef (5 / 6) N : ℂ) * t ^ (N + 1)) * hm

/-- `2 · 3^{1/6} e^{(4/3)L} = e^{(7/6)(log 2 + L)} z^{1/4}`. -/
theorem airyDer_norm_const {z : ℂ} (hz : z ≠ 0) :
    2 * (3 : ℂ) ^ (1 / 6 : ℂ) * exp (4 / 3 * airyLogZeta z) =
      exp ((7 / 6 : ℂ) * (log 2 + airyLogZeta z)) * z ^ (1 / 4 : ℂ) := by
  rw [cpow_def_of_ne_zero hz, cpow_def_of_ne_zero (by norm_num : (3 : ℂ) ≠ 0), airyLogZeta,
    log_two_thirds]
  calc 2 * exp (log 3 * (1 / 6)) * exp (4 / 3 * (log 2 - log 3 + 3 / 2 * log z))
      = exp (log 2) * exp (log 3 * (1 / 6)) * exp (4 / 3 * (log 2 - log 3 + 3 / 2 * log z)) := by
        rw [exp_log two_ne_zero]
    _ = _ := by simp only [← exp_add]; congr 1; ring

/-- **The normalized `Ai'` as a rotated Laplace integral** of `t^{1/6}(1+t)^{1/6}`. -/
theorem airyDer_G_eq {z : ℂ} (hz : z ≠ 0) {θ : ℝ} (hθ : |θ| < π)
    (hzθ : |3 / 2 * arg z + θ| < π / 2) :
    airyAiDeriv z / airyPrefactor .aiDeriv z = exp ((7 / 6 : ℂ) * (log 2 + airyLogZeta z)) *
      (1 / Gamma ((7 / 6 : ℝ) : ℂ) * (exp (θ * I) *
        airyRot_lap (7 / 6) (1 / 6) θ (exp (log 2 + airyLogZeta z + θ * I)))) := by
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz)
  rw [airyRot_eq_of_anchor (hf := fun w => (hasDerivAt_airyAiDeriv w).differentiableAt) _ _
    (7 / 6) (1 / 6) (by norm_num) (fun w hw harg => airyRot_airyAiDeriv_anchor hw harg) hθ hz hzθ]
  have hN : exp ((7 / 6 : ℂ) * (log 2 + airyLogZeta z)) =
      2 * (3 : ℂ) ^ (1 / 6 : ℂ) * exp (4 / 3 * airyLogZeta z) / z ^ (1 / 4 : ℂ) :=
    (eq_div_iff hq).mpr (airyDer_norm_const hz).symm
  rw [hN]
  simp only [airyPrefactor]
  generalize airyRot_lap (7 / 6) (1 / 6) θ (exp (log 2 + airyLogZeta z + θ * I)) = K
  have hG : Gamma ((7 / 6 : ℝ) : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp)
  rw [exp_sub, exp_neg]
  have hE : exp (airyZetaComplex z) ≠ 0 := exp_ne_zero _
  field_simp

/-- The `Ai'` coefficients: `d_k Γ(7/6+k)/Γ(7/6) = (-1)^k v_k 2^k`. -/
theorem airyDer_coef_aiDeriv (k : ℕ) :
    airyDer_d k * Real.Gamma (7 / 6 + k) / Real.Gamma (7 / 6) = (-1) ^ k * airyV k * 2 ^ k := by
  have h1 := airySt_gamma_ratio_real k (x := 7 / 6) (by norm_num)
  rw [mul_div_assoc, h1, airyRot_poch_seven_sixths]
  unfold airyDer_d airyV airyU
  rw [← airyRot_poch_neg_sixth]
  have hf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have h6 : (1 - 6 * (k : ℝ)) ≠ 0 := by
    intro h
    have h' : (6 * k : ℝ) = 1 := by linarith
    have : (6 * k : ℕ) = 1 := by exact_mod_cast h'
    omega
  field_simp

/-- The terms of the `Ai'` ray expansion. -/
def airyDer_T (θ W : ℝ) (k : ℕ) : ℂ :=
  (airyDer_d k : ℂ) * exp (θ * I * (((7 / 6 : ℝ) : ℂ) - 1 + k)) *
    (Gamma (((7 / 6 : ℝ) : ℂ) + k) * (W : ℂ) ^ (-(((7 / 6 : ℝ) : ℂ) + k)))

/-- The `Ai'` ray Laplace integral of `t^{1/6}(1+t)^{1/6}`. -/
def airyDer_L (θ W : ℝ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ (((7 / 6 : ℝ) : ℂ) - 1) *
    (1 + (r : ℂ) * exp (θ * I)) ^ (((1 / 6 : ℝ)) : ℂ))

/-- The rotated Laplace integral of `t^{1/6}(1+t)^{1/6}` is `airyDer_L`. -/
theorem airyDer_lap_eq (θ W : ℝ) :
    airyRot_lap (7 / 6) (1 / 6) θ (W : ℂ) = airyDer_L θ W := by
  unfold airyRot_lap airyDer_L airyRot_kernel
  rfl

/-- Integrability of `e^{-Wr} t^{1/6} (1+t)^{1/6}`, `t = r e^{iθ}`, for `|θ| < π`. -/
theorem airyDer_hint {θ W : ℝ} (hθ : |θ| < π) (hW : 0 < W) :
    IntegrableOn (fun r : ℝ => Complex.exp (-(W * r)) *
      (((r : ℂ) * exp (θ * I)) ^ (((7 / 6 : ℝ) : ℂ) - 1) *
        (1 + (r : ℂ) * exp (θ * I)) ^ (((1 / 6 : ℝ)) : ℂ))) (Ioi 0) := by
  have h := airyRot_integrableOn (7 / 6) (1 / 6) (by norm_num) hθ hW
  refine h.congr_fun (fun r _ => ?_) measurableSet_Ioi
  simp only [airyRot_kernel, Complex.real_smul, ofReal_exp]
  push_cast; ring_nf

/-- **Exact remainder of the `Ai'` ray expansion** after `N+1` terms. -/
theorem airyDer_rem_repr {W θ : ℝ} (hW : 0 < W) (hθ : |θ| < π) (N : ℕ) :
    airyDer_L θ W - ∑ k ∈ Finset.range (N + 1), airyDer_T θ W k =
      -∫ r in Ioi (0 : ℝ), Complex.exp (-(W * r)) *
        (((r : ℂ) * exp (θ * I)) ^ (((7 / 6 : ℝ) : ℂ) - 1) *
        ((-((r : ℂ) * exp (θ * I))) ^ (N + 1) * ∫ τ in Ioo (0 : ℝ) 1,
          (airyDer_g N τ : ℂ) * (1 + ((r : ℂ) * exp (θ * I)) * τ)⁻¹)) := by
  have hb : (0 : ℝ) < 7 / 6 := by norm_num
  have hT : ∀ k, airyDer_T θ W k = ∫ r in Ioi (0 : ℝ), (airyDer_d k : ℂ) *
      (Complex.exp (-(W * r)) * (((r : ℂ) * exp (θ * I)) ^ (((7 / 6 : ℝ) : ℂ) - 1) *
        ((r : ℂ) * exp (θ * I)) ^ k)) := by
    intro k
    rw [integral_const_mul, airySt_term_integral hb hW hθ k, airyDer_T]
    ring
  simp_rw [hT]
  rw [← integral_finsetSum _ (fun k _ => (airySt_term_integrableOn hb hW hθ k).const_mul _),
    airyDer_L, ← integral_neg, ← integral_sub (airyDer_hint hθ hW) (integrable_finsetSum _ fun k _ =>
      (airySt_term_integrableOn hb hW hθ k).const_mul _)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr : (0 : ℝ) ≤ r := le_of_lt hr
  have h := airyDer_binom_rem (airySt_one_add_mem hr hθ) N
  have hs : ∑ k ∈ Finset.range (N + 1), (airyDer_d k : ℂ) * (Complex.exp (-(W * r)) *
      (((r : ℂ) * exp (θ * I)) ^ (((7 / 6 : ℝ) : ℂ) - 1) * ((r : ℂ) * exp (θ * I)) ^ k)) =
      Complex.exp (-(W * r)) * ((r : ℂ) * exp (θ * I)) ^ (((7 / 6 : ℝ) : ℂ) - 1) *
        ∑ k ∈ Finset.range (N + 1), (airyDer_d k : ℂ) * ((r : ℂ) * exp (θ * I)) ^ k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [hs]
  linear_combination (Complex.exp (-(W * r)) *
    ((r : ℂ) * exp (θ * I)) ^ (((7 / 6 : ℝ) : ℂ) - 1)) * h

/-- **Ai' remainder as a ray remainder** on `|arg z| < 2π/3`, with ray `θ = -(3/2) arg z`. -/
theorem airyDer_aiDeriv_remainder {z : ℂ} (hz : z ≠ 0) (harg : |arg z| < 2 * π / 3) (N : ℕ) :
    airyRemainder .aiDeriv N z = exp ((7 / 6 : ℂ) * (log 2 + airyLogZeta z)) *
        (1 / Gamma ((7 / 6 : ℝ) : ℂ)) * exp (((-(3 / 2 * arg z) : ℝ) : ℂ) * I) *
      (airyDer_L (-(3 / 2 * arg z)) (Real.exp (log 2 + airyLogZeta z).re) -
        ∑ k ∈ Finset.range N, airyDer_T (-(3 / 2 * arg z))
          (Real.exp (log 2 + airyLogZeta z).re) k) ∧
    ∀ k : ℕ, airyExpansionCoeff .aiDeriv k / airyZetaComplex z ^ k =
      exp ((7 / 6 : ℂ) * (log 2 + airyLogZeta z)) *
        (1 / Gamma ((7 / 6 : ℝ) : ℂ)) * exp (((-(3 / 2 * arg z) : ℝ) : ℂ) * I) *
      airyDer_T (-(3 / 2 * arg z)) (Real.exp (log 2 + airyLogZeta z).re) k := by
  set θ : ℝ := -(3 / 2 * arg z) with hθdef
  set ℓ := log 2 + airyLogZeta z with hℓdef
  set W : ℝ := Real.exp ℓ.re with hWdef
  have hθ : |θ| < π := by
    rw [hθdef, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]; linarith
  have hzθ : |3 / 2 * arg z + θ| < π / 2 := by
    rw [hθdef, add_neg_cancel, abs_zero]; positivity
  have hF := airyDer_G_eq hz hθ hzθ
  rw [airySt_W_real, airyDer_lap_eq] at hF
  have hG : Gamma ((7 / 6 : ℝ) : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp)
  have hcT : ∀ k : ℕ, airyExpansionCoeff .aiDeriv k / airyZetaComplex z ^ k =
      exp ((7 / 6 : ℂ) * ℓ) * (1 / Gamma ((7 / 6 : ℝ) : ℂ)) * exp (θ * I) *
        airyDer_T θ W k := by
    intro k
    have hℓ : ℓ = (ℓ.re : ℂ) + ((-θ : ℝ) : ℂ) * I := by
      have h := im_log_two_add_airyLogZeta z
      simp only [add_im] at h
      apply Complex.ext
      · simp
      · simp [hℓdef, hθdef, h]
    have hWc : (W : ℂ) ^ (-(((7 / 6 : ℝ) : ℂ) + k)) =
        exp (-(((7 / 6 : ℝ) : ℂ) + k) * (ℓ.re : ℂ)) := by
      rw [hWdef, ofReal_exp, cpow_def_of_ne_zero (exp_ne_zero _), log_exp (by simp [Real.pi_pos])
        (by simp [Real.pi_pos.le]), mul_comm]
    have hζ : airyZetaComplex z = exp ℓ / 2 := by
      rw [hℓdef, exp_log_two_add_airyLogZeta hz]; ring
    have hc := airyDer_coef_aiDeriv k
    have hgk : Gamma (((7 / 6 : ℝ) : ℂ) + k) = ((Real.Gamma (7 / 6 + k) : ℝ) : ℂ) := by
      rw [← Complex.Gamma_ofReal]; push_cast; rfl
    have hg0 : Gamma ((7 / 6 : ℝ) : ℂ) = ((Real.Gamma (7 / 6) : ℝ) : ℂ) := by
      rw [← Complex.Gamma_ofReal]
    have hc' : ((-1 : ℂ) ^ k * (airyV k : ℂ)) = (airyDer_d k : ℂ) *
        Gamma (((7 / 6 : ℝ) : ℂ) + k) / Gamma ((7 / 6 : ℝ) : ℂ) / 2 ^ k := by
      rw [hgk, hg0]
      have : ((airyDer_d k * Real.Gamma (7 / 6 + k) / Real.Gamma (7 / 6) : ℝ) : ℂ) =
          (((-1) ^ k * airyV k * 2 ^ k : ℝ) : ℂ) := by rw [hc]
      push_cast at this
      rw [this]; field_simp
    have key : exp ((7 / 6 : ℂ) * ℓ) * exp (θ * I) * exp (θ * I * (((7 / 6 : ℝ) : ℂ) - 1 + k)) *
        exp (-(((7 / 6 : ℝ) : ℂ) + k) * (ℓ.re : ℂ)) * exp (k * ℓ) = 1 := by
      rw [← exp_add, ← exp_add, ← exp_add, ← exp_add]
      convert exp_zero using 2
      generalize ℓ.re = R at hℓ ⊢
      rw [hℓ]; push_cast; ring
    simp only [airyExpansionCoeff, airyDer_T]
    rw [hc', hWc, hζ, div_pow, ← Complex.exp_nat_mul]
    generalize exp ((7 / 6 : ℂ) * ℓ) = E1 at key ⊢
    generalize exp (θ * I) = E2 at key ⊢
    generalize exp (θ * I * (((7 / 6 : ℝ) : ℂ) - 1 + k)) = E3 at key ⊢
    generalize exp (-(((7 / 6 : ℝ) : ℂ) + k) * (ℓ.re : ℂ)) = E4 at key ⊢
    have hE5 : exp (k * ℓ) ≠ 0 := exp_ne_zero _
    generalize exp (k * ℓ) = E5 at key hE5 ⊢
    field_simp
    linear_combination (-((airyDer_d k : ℂ) * Gamma (((7 / 6 : ℝ) : ℂ) + k))) * key
  refine ⟨?_, hcT⟩
  rw [airyRemainder, airyFunction, hF, airyExponentialSum]
  simp_rw [hcT]
  rw [← Finset.mul_sum]
  ring

/-- `∫ g_N = (-1)^N d_{N+1}`. -/
theorem airyDer_int_g (N : ℕ) :
    ∫ τ in Ioo (0 : ℝ) 1, airyDer_g N τ = (-1) ^ N * airyDer_d (N + 1) := by
  unfold airyDer_g
  rw [integral_const_mul, setIntegral_congr_fun measurableSet_Ioo (fun τ _ => airyDer_g_eq N),
    integral_sub (airySt_integrableOn_w (by norm_num) (by norm_num) N)
      (airySt_integrableOn_w (by norm_num) (by norm_num) (N + 1)),
    airySt_moment (by norm_num) (by norm_num), airySt_moment (by norm_num) (by norm_num)]
  have h1 := airySt_gamma_ratio_real N (x := 5 / 6) (by norm_num)
  have h2 := airySt_gamma_ratio_real (N + 1) (x := 5 / 6) (by norm_num)
  have g1 := Real.Gamma_pos_of_pos (show (0 : ℝ) < 5 / 6 by norm_num)
  have g2 := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 - 5 / 6 by norm_num)
  rw [div_eq_iff g1.ne'] at h1 h2
  rw [h1, h2, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]
  unfold airyDer_d
  have h3 : (ascPochhammer ℝ (N + 1)).eval (-1 / 6) =
      (-1 / 6) * (ascPochhammer ℝ N).eval (5 / 6) := by
    rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    norm_num
  rw [h3, ascPochhammer_succ_eval, Nat.factorial_succ]
  have hf : (N.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr N.factorial_ne_zero
  have hm : ((-1 : ℝ) ^ N) * (-1) ^ N = 1 := by rw [← mul_pow]; norm_num
  push_cast
  field_simp
  linear_combination (-(ascPochhammer ℝ N).eval (5 / 6)) * hm

/-- **The Ai' remainder on `|arg z| ≤ π/3`** after `N+1` terms is `(A + iB)` times the first
neglected term, `0 ≤ A ≤ 1`. -/
theorem airyDer_aiDeriv_ratio {z : ℂ} (hz : z ≠ 0) (harg : |arg z| ≤ π / 3) (N : ℕ) :
    ∃ A B : ℝ, 0 ≤ A ∧ A ≤ 1 ∧ airyRemainder .aiDeriv (N + 1) z =
      (A + B * I) * (airyExpansionCoeff .aiDeriv (N + 1) / airyZetaComplex z ^ (N + 1)) := by
  have hπ := Real.pi_pos
  have harg' : |arg z| < 2 * π / 3 := by linarith
  obtain ⟨h1, h2⟩ := airyDer_aiDeriv_remainder hz harg' (N + 1)
  have hθ := airySt_theta_lt harg'
  have hcos : 0 ≤ Real.cos (-(3 / 2 * arg z)) := by
    rw [Real.cos_neg]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [(abs_le.mp harg).1],
      by linarith [(abs_le.mp harg).2]⟩
  have hW : 0 < Real.exp (log 2 + airyLogZeta z).re := Real.exp_pos _
  rw [h1, h2, airyDer_rem_repr hW hθ N]
  obtain ⟨A, B, hA0, hA1, hE⟩ := airyDer_ray_ratio (b := 7 / 6) (by norm_num) hW hθ hcos (N + 1)
    (airyDer_g_measurable N) (fun τ hτ => airyDer_g_nonneg N hτ) (airyDer_integrableOn_g N)
  refine ⟨A, B, hA0, hA1, ?_⟩
  have hs : ((-1 : ℝ) ^ (N + 1) * ((-1) ^ N * airyDer_d (N + 1))) = -airyDer_d (N + 1) := by
    rw [pow_succ, show (-1 : ℝ) ^ N * -1 * ((-1) ^ N * airyDer_d (N + 1)) =
      -(((-1) ^ N * (-1) ^ N) * airyDer_d (N + 1)) by ring, ← mul_pow]
    norm_num
  rw [hE, airyDer_int_g, hs]
  unfold airyDer_T
  push_cast
  ring

/-- `cos (w - π/4)` and `-sin (w - π/4)` through `e^{∓iw}`, second form. -/
theorem airyDer_cos_sin' (w : ℂ) :
    cos (w - π / 4) = I * (exp (-(π * I / 4)) / 2 * exp (-(w * I)) -
        exp (π * I / 4) / 2 * exp (w * I)) ∧
      -sin (w - π / 4) = exp (-(π * I / 4)) / 2 * exp (-(w * I)) +
        exp (π * I / 4) / 2 * exp (w * I) := by
  rw [show cos (w - π / 4) = sin (w - π / 4 + π / 2) from (Complex.sin_add_pi_div_two _).symm,
    show sin (w - π / 4) = -cos (w - π / 4 + π / 2) by rw [Complex.cos_add_pi_div_two]; ring]
  simp only [Complex.cos, Complex.sin]
  have e1 : exp ((w - π / 4 + π / 2) * I) = exp (π * I / 4) * exp (w * I) := by
    rw [← exp_add]; congr 1; ring
  have e2 : exp (-(w - π / 4 + π / 2) * I) = exp (-(π * I / 4)) * exp (-(w * I)) := by
    rw [← exp_add]; congr 1; ring
  rw [e1, e2]
  constructor
  · field_simp
  · ring

/-- `Ai'(-z)` through the even and odd parts of the normalized `Ai'`, exactly (DLMF 9.7.10). -/
theorem airyDer_airyAiDeriv_neg {z : ℂ} (hz0 : z ≠ 0) (hz3 : |arg z| < 2 * π / 3) :
    airyAiDeriv (-z) = airyOscPrefactor .aiDeriv z *
      (sin (airyZetaComplex z - π / 4) *
          airyRot_even (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) z -
        cos (airyZetaComplex z - π / 4) *
          airyRot_odd (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) z) := by
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
  have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hp1 := airyRot_prefactor_ne_zero .aiDeriv
    (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
  have hp2 := airyRot_prefactor_ne_zero .aiDeriv
    (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
  obtain ⟨hc, hs⟩ := airyDer_cos_sin' (airyZetaComplex z)
  rw [show sin (airyZetaComplex z - π / 4) = -(-sin (airyZetaComplex z - π / 4)) by ring, hs, hc]
  rw [airyRot_airyAiDeriv_neg z]
  rw [show airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) =
      airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) *
      (airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) /
        airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I))) by field_simp,
    show airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
      airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) *
      (airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) /
        airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
  rw [← mul_assoc, ← mul_assoc]
  rw [airyRot_decomp (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)]
  have ep : exp (-π * I / 3) * airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) =
      airyOscPrefactor .aiDeriv z *
        (-(exp (-(π * I / 4)) / 2) * exp (-(airyZetaComplex z * I))) := by
    simp only [airyPrefactor, airyOscPrefactor]
    rw [d1, d3, ← hu, um4, um3]
    field_simp
  have em : exp (π * I / 3) * airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
      airyOscPrefactor .aiDeriv z * (-(exp (π * I / 4) / 2) * exp (airyZetaComplex z * I)) := by
    simp only [airyPrefactor, airyOscPrefactor]
    rw [d2, d4, ← hu, u4, u3, neg_neg]
    field_simp
  rw [ep, em]
  ring

/-- `Bi'(-z)` through the even and odd parts of the normalized `Ai'`, exactly (DLMF 9.7.12). -/
theorem airyDer_airyBiDeriv_neg {z : ℂ} (hz0 : z ≠ 0) (hz3 : |arg z| < 2 * π / 3) :
    airyBiDeriv (-z) = airyOscPrefactor .aiDeriv z *
      (cos (airyZetaComplex z - π / 4) *
          airyRot_even (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) z +
        sin (airyZetaComplex z - π / 4) *
          airyRot_odd (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) z) := by
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
  have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hp1 := airyRot_prefactor_ne_zero .aiDeriv
    (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
  have hp2 := airyRot_prefactor_ne_zero .aiDeriv
    (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
  obtain ⟨hc, hs⟩ := airyDer_cos_sin (airyZetaComplex z)
  rw [hc, hs]
  rw [airyRot_airyBiDeriv_neg z]
  rw [show airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) =
      airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) *
      (airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) /
        airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I))) by field_simp,
    show airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
      airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) *
      (airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) /
        airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
  rw [← mul_assoc, ← mul_assoc]
  rw [airyRot_decomp (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)]
  have ep : -exp (π * I / 6) * airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) =
      airyOscPrefactor .aiDeriv z *
        (exp (π * I / 4) / 2 * exp (-(airyZetaComplex z * I))) := by
    simp only [airyPrefactor, airyOscPrefactor]
    rw [d1, d3, ← hu, u2, u3]
    field_simp
  have em : -exp (-π * I / 6) * airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
      airyOscPrefactor .aiDeriv z * (exp (-(π * I / 4)) / 2 * exp (airyZetaComplex z * I)) := by
    simp only [airyPrefactor, airyOscPrefactor]
    rw [d2, d4, ← hu, um2, um3, neg_neg]
    field_simp
  rw [ep, em]
  ring

/-- The derivative components are the even and odd parts of the normalized `Ai'`. -/
theorem airyDer_comp_true {x : ℝ} (hx : 0 < x) :
    airyOscComponent true 0 x =
        airyRot_even (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) x ∧
    airyOscComponent true 1 x =
        airyRot_odd (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) x := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x : ℂ)| < 2 * π / 3 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  have hA := airyDer_airyAiDeriv_neg hx0 harg
  have hB := airyDer_airyBiDeriv_neg hx0 harg
  rw [airyReal_zeta_ofReal hx] at hA hB
  have hP : airyOscPrefactor .aiDeriv (x : ℂ) ≠ 0 := by
    simp only [airyOscPrefactor]
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : (x : ℂ) ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
    exact div_ne_zero hq hπs
  have hcs := Complex.cos_sq_add_sin_sq (((airyZeta x : ℝ) : ℂ) - π / 4)
  simp only [airyOscComponent, ite_true, Fin.val_zero, Fin.val_one, one_ne_zero, ite_false]
  rw [hA, hB]
  constructor
  · rw [div_eq_iff hP]
    linear_combination (airyOscPrefactor .aiDeriv (x : ℂ) *
      airyRot_even (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) x) * hcs
  · rw [div_eq_iff hP]
    linear_combination (airyOscPrefactor .aiDeriv (x : ℂ) *
      airyRot_odd (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) x) * hcs

/-- The `Ai'` coefficients: even ones are `v_{2j}`, odd ones `-v_{2j+1}`. -/
theorem airyDer_coeff_aiDeriv (j : ℕ) :
    airyExpansionCoeff .aiDeriv (2 * j) = airyV (2 * j) ∧
      airyExpansionCoeff .aiDeriv (2 * j + 1) = -(airyV (2 * j + 1) : ℂ) := by
  have h := airyRot_coeff_parity .aiDeriv (Or.inr rfl) j
  simpa using h

/-- For `|arg w| ≤ π/3` and `M ≥ 1` the `Ai'` remainder is `(A + iB)` times the first
neglected term with `0 ≤ A ≤ 1`. -/
theorem airyDer_aiDeriv_ratio' {w : ℂ} (hw : w ≠ 0) (harg : |arg w| ≤ π / 3) {M : ℕ} (hM : 1 ≤ M) :
    ∃ A B : ℝ, 0 ≤ A ∧ A ≤ 1 ∧ airyAiDeriv w / airyPrefactor .aiDeriv w -
      ∑ k ∈ Finset.range M, airyExpansionCoeff .aiDeriv k / airyZetaComplex w ^ k =
        (A + B * I) * (airyExpansionCoeff .aiDeriv M / airyZetaComplex w ^ M) := by
  obtain ⟨K, rfl⟩ : ∃ K, M = K + 1 := ⟨M - 1, by omega⟩
  obtain ⟨A, B, h0, h1, h⟩ := airyDer_aiDeriv_ratio hw harg K
  exact ⟨A, B, h0, h1, by rw [← h]; rfl⟩

/-- DLMF §9.7(iii) for the even subseries of the `Ai'`, `Bi'` oscillatory expansions. -/
theorem airyDer_osc_even_deriv {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) :
    ‖airyOscComponent true 0 x - airyOscSum true 0 N x‖ ≤
        ‖(-1 : ℂ) ^ N * (airyV (2 * N) : ℂ) / airyZetaComplex x ^ (2 * N)‖ ∧
      0 ≤ (airyOscComponent true 0 x - airyOscSum true 0 N x).re *
        ((-1 : ℝ) ^ N * airyV (2 * N)) := by
  obtain ⟨hp0, hpa, hm0, hma⟩ := airyDer_rot_data hx
  have hS : airyOscSum true 0 N x = ∑ j ∈ Finset.range N,
      (-1 : ℂ) ^ j * (airyV (2 * j) : ℂ) / airyZetaComplex x ^ (2 * j) := by
    simp [airyOscSum]
  have hre := (airyDer_comp_im true 0 hx)
  have hre' := airyDer_oscSum_im true 0 N hx
  rw [hS] at hre'
  rw [(airyDer_comp_true hx).1] at hre ⊢
  rw [hS]
  exact airyDer_even_bound _ (airyExpansionCoeff .aiDeriv) airyV
    (fun j => (airyDer_coeff_aiDeriv j).1) hx N
    (airyDer_aiDeriv_ratio' hp0 hpa (by omega)) (airyDer_aiDeriv_ratio' hm0 hma (by omega))
    (by rw [sub_im, hre, hre', sub_zero])

/-- DLMF §9.7(iii) for the odd subseries of the `Ai'`, `Bi'` oscillatory expansions. -/
theorem airyDer_osc_odd_deriv {x : ℝ} (hx : 0 < x) (N : ℕ) :
    ‖airyOscComponent true 1 x - airyOscSum true 1 N x‖ ≤
        ‖(-1 : ℂ) ^ N * (airyV (2 * N + 1) : ℂ) / airyZetaComplex x ^ (2 * N + 1)‖ ∧
      0 ≤ (airyOscComponent true 1 x - airyOscSum true 1 N x).re *
        ((-1 : ℝ) ^ N * airyV (2 * N + 1)) := by
  obtain ⟨hp0, hpa, hm0, hma⟩ := airyDer_rot_data hx
  have hS : airyOscSum true 1 N x = ∑ j ∈ Finset.range N,
      (-1 : ℂ) ^ j * (airyV (2 * j + 1) : ℂ) / airyZetaComplex x ^ (2 * j + 1) := by
    simp [airyOscSum]
  have hre := (airyDer_comp_im true 1 hx)
  have hre' := airyDer_oscSum_im true 1 N hx
  rw [hS] at hre'
  rw [(airyDer_comp_true hx).2] at hre ⊢
  rw [hS]
  exact airyDer_odd_bound _ (airyExpansionCoeff .aiDeriv) airyV
    (fun j => (airyDer_coeff_aiDeriv j).2) hx N
    (airyDer_aiDeriv_ratio' hp0 hpa (by omega)) (airyDer_aiDeriv_ratio' hm0 hma (by omega))
    (by rw [sub_im, hre, hre', sub_zero])

/-- `v_2 < 0`. -/
theorem airyDer_airyV_two_neg : airyV 2 < 0 := by
  have h := airySt_airyU_pos 2
  unfold airyV
  norm_num
  linarith

/-- The signed first-neglected-term bound for each real oscillatory subseries, 9.7(iii).
The hypothesis explicitly retains the source's condition on the following term. -/
theorem airy_oscillatory_real_error (derivative : Bool) (parity : Fin 2)
    {x : ℝ} (hx : 0 < x) (N : ℕ)
    (hopposite : ((-1 : ℝ) ^ N * (if derivative then airyV (2 * N + parity.val) else airyU (2 * N + parity.val))) *
      ((-1 : ℝ) ^ (N + 1) * (if derivative then airyV (2 * (N + 1) + parity.val) else airyU (2 * (N + 1) + parity.val))) < 0) :
    ‖airyOscComponent derivative parity x - airyOscSum derivative parity.val N x‖ ≤
      ‖(-1 : ℂ) ^ N * (if derivative then airyV (2 * N + parity.val) else airyU (2 * N + parity.val)) /
        airyZetaComplex x ^ (2 * N + parity.val)‖ ∧
    0 ≤ (airyOscComponent derivative parity x - airyOscSum derivative parity.val N x).re *
      ((-1 : ℝ) ^ N * (if derivative then airyV (2 * N + parity.val) else airyU (2 * N + parity.val))) := by
  cases derivative
  · fin_cases parity
    · simpa using airyDer_osc_even hx N
    · simpa using airyDer_osc_odd hx N
  · fin_cases parity
    · rcases Nat.eq_zero_or_pos N with rfl | hN
      · exfalso
        have h0 : airyV 0 = 1 := by simp [airyV, airyU]
        simp [h0] at hopposite
        linarith [airyDer_airyV_two_neg]
      · simpa using airyDer_osc_even_deriv hx hN
    · simpa using airyDer_osc_odd_deriv hx N

end DLMF.Airy
end
