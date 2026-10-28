/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Integrals.WhittakerTransforms

/-!
# Gauss and Stieltjes representations of Tricomi functions

Gauss and Stieltjes integral representations, with local domination and analytic continuation.

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

/-! ### Gauss and Stieltjes representations (DLMF 13.4.5, 13.4.8, 13.16.6, 13.16.9)

These representations from §13.4 and §13.16 are proved here, after the Laplace transforms
they use. For `Re a > 0`, two applications of the regularized Kummer Laplace transform and
Fubini reduce 13.4.8 to Tricomi's Laplace representation. Tricomi's contiguous relation in
`a`, matched by a regularized Gauss contiguous relation that also raises `c`, then removes
the restriction on `a`. The Stieltjes form follows from `1/(t+z) = ∫ e^{-(t+z)s} ds`, the
Tricomi Laplace transform, Pfaff's transformation and 13.4.8 with `c = 1`. It is first proved
for `Re z > 0` and then continued holomorphically to the slit plane. -/

section GaussStieltjes

open Set

/-- `𝐅(a,c;c;w) = (1-w)^{-a}/Γ(c)` on the cut plane. -/
theorem regularizedGaussHG_self_right (a c : ℂ) {w : ℂ} (hw : w ∈ cutPlane) :
    regularizedGaussHG a c c w = (1 - w) ^ (-a) * (Gamma c)⁻¹ := by
  have h0 : regularizedGaussHG 0 (c - a) c w = (Gamma c)⁻¹ :=
    eqOn_cutPlane_of_eqOn_disk (f := regularizedGaussHG 0 (c - a) c) (g := fun _ => (Gamma c)⁻¹)
      (analyticOnNhd_regularizedGaussHG _ _ _) analyticOnNhd_const (fun u hu => by
        rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hu, regularizedGaussHGFun_eq_tsum,
          tsum_eq_single 0 (fun n hn => by
            obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
            simp [ascPochhammer_succ_left])]
        simp) hw
  rw [regularizedGaussHG_euler, show c - c = (0 : ℂ) by ring, regularizedGaussHG_symm _ _ _ hw, h0,
    show c - a - c = -a by ring]
  exact hw

/-- For real `t ≥ 0`, `-t` lies in the cut plane `ℂ \ [1, ∞)`. -/
theorem neg_ofReal_mem_cutPlane {t : ℝ} (ht : 0 ≤ t) : (-(t : ℂ)) ∈ cutPlane := by
  change 1 - -(t : ℂ) ∈ slitPlane
  rw [sub_neg_eq_add]
  exact Or.inl (by simp; linarith)

/-- The kernel of the Gauss–Laplace representation 13.4.8. -/
def kummerUGaussKernel (a b c z : ℂ) (t : ℝ) : ℂ :=
  exp (-z * t) * (t : ℂ) ^ (c - 1) * regularizedGaussHG a (a - b + 1) c (-(t : ℂ))

/-- For `Re a, Re c, Re z > 0`, `U(a,b,z) = z^{c-a} ∫₀^∞ e^{-zt} t^{c-1} ₂F̃₁(a, a-b+1; c; -t) dt`,
with the integrand integrable (DLMF 13.4.8 for `Re a > 0`). -/
theorem kummerU_gauss_of_re_pos {a b c z : ℂ} (ha : 0 < a.re) (hc : 0 < c.re) (hz : 0 < z.re) :
    IntegrableOn (kummerUGaussKernel a b c z) (Ioi 0) ∧
      kummerU a b z = z ^ (c - a) * ∫ t : ℝ in Ioi 0, kummerUGaussKernel a b c z t := by
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, β = a - b + 1 := ⟨_, rfl⟩
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  set F : ℝ → ℝ → ℂ := fun t s => exp (-z * t) * (t : ℂ) ^ (c - 1) *
    (exp (-z * s) * (s : ℂ) ^ (a - 1) * regularizedHGFun {β} {c} ((-z * t) * s)) with hF
  obtain ⟨C, hC, N, hM⟩ := regularizedConfluent_ray_growth β c (-z)
  have hmax : max 0 (-z).re = 0 := by simp; linarith
  have hRc : Continuous (fun q : ℝ × ℝ => regularizedHGFun {β} {c} ((-z * q.1) * q.2)) :=
    (continuous_regularizedConfluent.comp (show Continuous (fun w : ℂ => (β, c, w)) by fun_prop)).comp
      (show Continuous (fun q : ℝ × ℝ => (-z * (q.1 : ℂ)) * (q.2 : ℂ)) by fun_prop)
  have hRm := hRc.measurable
  have hmeas : AEStronglyMeasurable (Function.uncurry F) ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine Measurable.aestronglyMeasurable ?_
    simp only [hF, Function.uncurry_def]
    fun_prop
  have hf1 := integrableOn_rpow_mul_one_add_pow_mul_exp (s := c.re - 1) (by linarith) hz N
  have hf2 := integrableOn_rpow_mul_one_add_pow_mul_exp (s := a.re - 1) (by linarith) hz N
  have hFi : Integrable (Function.uncurry F) ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine ((hf1.mul_prod hf2).const_mul C).mono' hmeas ?_
    have hset : ∀ᵐ q ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))), q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
    filter_upwards [hset] with q hq
    obtain ⟨t, s⟩ := q
    obtain ⟨ht, hs⟩ := hq
    change 0 < t at ht; change 0 < s at hs
    have hb := hM (t * s) (by positivity)
    rw [hmax, zero_mul, Real.exp_zero, mul_one] at hb
    have harg : (-z * t) * s = -z * ((t * s : ℝ) : ℂ) := by push_cast; ring
    simp only [hF, Function.uncurry_def, norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos ht,
      norm_cpow_eq_rpow_re_of_pos hs, harg]
    simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, sub_re, one_re]
    have h1 : (1 + t * s) ^ N ≤ (1 + t) ^ N * (1 + s) ^ N := by
      rw [← mul_pow]; gcongr; nlinarith
    calc _ ≤ Real.exp (-(z.re * t)) * t ^ (c.re - 1) *
          (Real.exp (-(z.re * s)) * s ^ (a.re - 1) * (C * ((1 + t) ^ N * (1 + s) ^ N))) := by
          gcongr
          rw [← neg_mul]
          exact hb.trans (mul_le_mul_of_nonneg_left h1 hC)
      _ = _ := by ring
  have hpt : ∀ t ∈ Ioi (0 : ℝ), kummerUGaussKernel a b c z t =
      (Gamma a)⁻¹ * z ^ a * ∫ s : ℝ in Ioi 0, F t s := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hL := laplace_regularizedHGFun (a := β) (b := a) (c := c) (k := -z * t) (z := z) ha
      (by simp; nlinarith) hz
    have harg : (-z * t) / z = -(t : ℂ) := by field_simp
    rw [harg] at hL
    have hF' : ∫ s : ℝ in Ioi 0, F t s = exp (-z * t) * (t : ℂ) ^ (c - 1) *
        ∫ s : ℝ in Ioi 0, exp (-z * s) * (s : ℂ) ^ (a - 1) * regularizedHGFun {β} {c} ((-z * t) * s) := by
      simp only [hF]; rw [integral_const_mul]
    rw [hF', hL, kummerUGaussKernel, ← hβ,
      regularizedGaussHG_symm _ _ _ (neg_ofReal_mem_cutPlane ht0.le)]
    have hGa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
    have hza : z ^ a * z ^ (-a) = 1 := by rw [← cpow_add _ _ hz0]; simp
    have e : ∀ X Y : ℂ, (Gamma a)⁻¹ * z ^ a * (X * (Gamma a * z ^ (-a) * Y)) =
        X * Y * (z ^ a * z ^ (-a)) * ((Gamma a)⁻¹ * Gamma a) := fun X Y => by ring
    rw [e, hza, inv_mul_cancel₀ hGa]; ring
  have hinner : ∀ s ∈ Ioi (0 : ℝ), ∫ t : ℝ in Ioi 0, F t s =
      z ^ (-c) * (exp (-z * s) * (s : ℂ) ^ (a - 1) * (1 + (s : ℂ)) ^ (b - a - 1)) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hL := laplace_regularizedHGFun (a := β) (b := c) (c := c) (k := -z * s) (z := z) hc
      (by simp; nlinarith) hz
    have harg : (-z * s) / z = -(s : ℂ) := by field_simp
    rw [harg, regularizedGaussHG_self_right _ _ (neg_ofReal_mem_cutPlane hs0.le)] at hL
    have hF' : ∫ t : ℝ in Ioi 0, F t s = (exp (-z * s) * (s : ℂ) ^ (a - 1)) *
        ∫ t : ℝ in Ioi 0, exp (-z * t) * (t : ℂ) ^ (c - 1) * regularizedHGFun {β} {c} ((-z * s) * t) := by
      rw [← integral_const_mul]
      congr 1; funext t
      simp only [hF]
      rw [show (-z * (t : ℂ)) * s = (-z * s) * t by ring]
      ring
    rw [hF', hL, sub_neg_eq_add, hβ, show -(a - b + 1) = b - a - 1 by ring]
    field_simp [Gamma_ne_zero_of_re_pos hc]
  have hint := (hFi.integral_prod_left.const_mul ((Gamma a)⁻¹ * z ^ a)).congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact (hpt t ht).symm)
  refine ⟨hint, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_integral_swap hFi, setIntegral_congr_fun measurableSet_Ioi hinner, integral_const_mul,
    kummerU_laplace ha hz]
  have hzz : z ^ (c - a) * z ^ a * z ^ (-c) = 1 := by
    rw [← cpow_add _ _ hz0, ← cpow_add _ _ hz0]; ring_nf; exact cpow_zero _
  generalize (∫ s : ℝ in Ioi 0, exp (-z * s) * (s : ℂ) ^ (a - 1) * (1 + (s : ℂ)) ^ (b - a - 1)) = J
  linear_combination (-(Gamma a)⁻¹ * J) * hzz

/-- 13.4.8 with absolute integrability, for every first parameter, by Tricomi's
contiguous relation in `a` and the matching regularized Gauss relation. -/
lemma kummerU_gauss_aux {a b c z : ℂ} (hc : 0 < c.re) (hz : 0 < z.re) :
    IntegrableOn (kummerUGaussKernel a b c z) (Ioi 0) ∧
      kummerU a b z = z ^ (c - a) * ∫ t : ℝ in Ioi 0, kummerUGaussKernel a b c z t := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hshift : ∀ N : ℕ, ∀ a b c : ℂ, 0 < a.re + N → 0 < c.re →
      IntegrableOn (kummerUGaussKernel a b c z) (Ioi 0) ∧
        kummerU a b z = z ^ (c - a) * ∫ t : ℝ in Ioi 0, kummerUGaussKernel a b c z t := by
    intro N
    induction N with
    | zero => intro a b c ha hc; exact kummerU_gauss_of_re_pos (by simpa using ha) hc hz
    | succ N ih =>
      intro a b c ha hc
      have h1 := ih (a + 1) (b + 1) c (by simp at ha ⊢; linarith) hc
      have h2 := ih (a + 1) b (c + 1) (by simp at ha ⊢; linarith) (by simp; linarith)
      have hpt : ∀ t ∈ Ioi (0 : ℝ), kummerUGaussKernel a b c z t =
          kummerUGaussKernel (a + 1) (b + 1) c z t +
            (a - b + 1) * kummerUGaussKernel (a + 1) b (c + 1) z t := by
        intro t ht
        have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
        have hw := neg_ofReal_mem_cutPlane (le_of_lt (mem_Ioi.mp ht))
        have hg := regularizedGaussHG_contiguous_shift_b (a - b + 1) a c hw
        rw [regularizedGaussHG_symm _ _ _ hw, regularizedGaussHG_symm (a - b + 1) (a + 1) c hw,
          regularizedGaussHG_symm (a - b + 1 + 1) (a + 1) (c + 1) hw] at hg
        simp only [kummerUGaussKernel]
        rw [show a + 1 - (b + 1) + 1 = a - b + 1 by ring, show a + 1 - b + 1 = a - b + 1 + 1 by ring,
          show c + 1 - 1 = (c - 1) + 1 by ring, cpow_add _ _ ht0, cpow_one]
        linear_combination (exp (-z * t) * (t : ℂ) ^ (c - 1)) * hg
      have hi : IntegrableOn (kummerUGaussKernel a b c z) (Ioi 0) :=
        (h1.1.add (h2.1.const_mul (a - b + 1))).congr (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact (hpt t ht).symm)
      refine ⟨hi, ?_⟩
      have hU := kummerU_contiguous_shift_a (a + 1) b z hz0
      rw [add_sub_cancel_right] at hU
      rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add h1.1 (h2.1.const_mul _),
        integral_const_mul]
      have hz1 : z ^ (c - a) = z * z ^ (c - (a + 1)) := by
        rw [show c - a = 1 + (c - (a + 1)) by ring, cpow_add _ _ hz0, cpow_one]
      rw [show c + 1 - (a + 1) = c - a by ring] at h2
      rw [h1.2, h2.2] at hU
      rw [hz1] at hU ⊢
      linear_combination hU
  obtain ⟨N, hN⟩ := exists_nat_gt (-a.re)
  exact hshift N a b c (by linarith) hc

/-- Identity under the stated parameter and domain assumptions: `kummerU a b z = z ^ (c - a) * ∫ t
: ℝ in Set.Ioi 0, exp (-z * t) * (t : ℂ) ^ (c - 1) * DLMF.Hypergeometric.regularizedGaussHG a
(a - b + 1) c (-(t : ℂ))`. -/
@[dlmf 13.4.E8]
theorem kummerU_gauss {a b c z : ℂ} (ha : 0 < c.re) (hz : 0 < z.re) :
    kummerU a b z =
      z ^ (c - a) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-z * t) * (t : ℂ) ^ (c - 1) *
            DLMF.Hypergeometric.regularizedGaussHG a (a - b + 1) c (-(t : ℂ)) :=
  (kummerU_gauss_aux ha hz).2

/-- Identity under the stated parameter and domain assumptions: `whittakerW κ μ z = exp (-z / 2) *
z ^ (κ + c) * ∫ t : ℝ in Set.Ioi 0, exp (-z * t) * (t : ℂ) ^ (c - 1) *
DLMF.Hypergeometric.regularizedGaussHG (1 / 2 + μ - κ) (1 / 2 - μ - κ) c (-(t : ℂ))`. -/
@[dlmf 13.16.E9]
theorem whittakerW_gauss {κ μ c z : ℂ} (hc : 0 < c.re) (hz : 0 < z.re) :
    whittakerW κ μ z =
      exp (-z / 2) * z ^ (κ + c) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-z * t) * (t : ℂ) ^ (c - 1) *
            DLMF.Hypergeometric.regularizedGaussHG (1 / 2 + μ - κ) (1 / 2 - μ - κ) c (-(t : ℂ)) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [whittakerW, kummerU_gauss (b := 1 + 2 * μ) hc hz,
    show 1 / 2 + μ - κ - (1 + 2 * μ) + 1 = 1 / 2 - μ - κ by ring]
  have hp : z ^ (1 / 2 + μ) * z ^ (c - (1 / 2 + μ - κ)) = z ^ (κ + c) := by
    rw [← cpow_add _ _ hz0]; ring_nf
  rw [← hp]; ring

/-- Points of the slit plane stay uniformly away from the closed negative ray. -/
theorem exists_forall_le_norm_add_of_mem_slitPlane {z₀ : ℂ} (hz₀ : z₀ ∈ slitPlane) :
    ∃ δ > 0, ∀ t : ℝ, 0 ≤ t → ∀ z ∈ Metric.ball z₀ δ, δ ≤ ‖(t : ℂ) + z‖ := by
  have hd : ∃ d > 0, ∀ t : ℝ, 0 ≤ t → d ≤ ‖(t : ℂ) + z₀‖ := by
    by_cases hre : 0 < z₀.re
    · refine ⟨z₀.re, hre, fun t ht => ?_⟩
      calc z₀.re ≤ ((t : ℂ) + z₀).re := by simp; linarith
        _ ≤ _ := re_le_norm _
    · have him : z₀.im ≠ 0 := by
        rcases mem_slitPlane_iff.mp hz₀ with h | h
        · exact absurd h hre
        · exact h
      refine ⟨|z₀.im|, abs_pos.mpr him, fun t _ => ?_⟩
      calc |z₀.im| = |((t : ℂ) + z₀).im| := by simp
        _ ≤ _ := abs_im_le_norm _
  obtain ⟨d, hd0, hd⟩ := hd
  refine ⟨d / 2, by linarith, fun t ht z hz => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have h1 := hd t ht
  have h2 : ‖(t : ℂ) + z₀‖ ≤ ‖(t : ℂ) + z‖ + ‖z - z₀‖ := by
    calc ‖(t : ℂ) + z₀‖ = ‖((t : ℂ) + z) - (z - z₀)‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  linarith

/-- The Stieltjes transform of an integrable function on the positive half-line is
holomorphic on the slit plane. -/
theorem differentiableOn_stieltjes_integral {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0)) :
    DifferentiableOn ℂ (fun z => ∫ t : ℝ in Ioi 0, g t / ((t : ℂ) + z)) slitPlane := by
  intro z₀ hz₀
  obtain ⟨δ, hδ, hδb⟩ := exists_forall_le_norm_add_of_mem_slitPlane hz₀
  have hpos : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using le_of_lt ht
  have hne : ∀ t : ℝ, 0 ≤ t → ∀ z ∈ Metric.ball z₀ δ, (t : ℂ) + z ≠ 0 := fun t ht z hz h => by
    have := hδb t ht z hz; rw [h, norm_zero] at this; linarith
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ => g t / ((t : ℂ) + z))
      (volume.restrict (Ioi 0)) := fun z =>
    hg.aestronglyMeasurable.mul (Measurable.aestronglyMeasurable (by fun_prop))
  have hint : Integrable (fun t : ℝ => g t / ((t : ℂ) + z₀)) (volume.restrict (Ioi 0)) := by
    refine (hg.norm.const_mul δ⁻¹).mono' (hmeas z₀) ?_
    filter_upwards [hpos] with t ht
    rw [norm_div, div_eq_mul_inv, mul_comm]
    gcongr
    exact hδb t ht z₀ (Metric.mem_ball_self hδ)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0))
    (F := fun z (t : ℝ) => g t / ((t : ℂ) + z))
    (F' := fun z (t : ℝ) => -(g t / ((t : ℂ) + z) ^ 2))
    (bound := fun t => (δ ^ 2)⁻¹ * ‖g t‖)
    (Metric.ball_mem_nhds _ hδ) (Eventually.of_forall hmeas) hint
    ((hg.aestronglyMeasurable.mul (Measurable.aestronglyMeasurable (by fun_prop))).neg)
    ?_ (hg.norm.const_mul _) ?_
  · exact hd.2.differentiableAt.differentiableWithinAt
  · filter_upwards [hpos] with t ht z hz
    rw [norm_neg, norm_div, norm_pow, div_eq_mul_inv, mul_comm]
    gcongr
    exact hδb t ht z hz
  · filter_upwards [hpos] with t ht z hz
    have h0 := hne t ht z hz
    have h := ((hasDerivAt_id z).const_add (t : ℂ)).inv h0
    have h' := h.const_mul (g t)
    simp only [id_eq] at h'
    convert h' using 1
    · ext w; simp [div_eq_mul_inv]
    · field_simp

/-- Tricomi's Stieltjes representation 13.4.5 in the right half-plane, by Fubini against
`1/(t+z) = ∫ e^{-(t+z)s} ds`, the Tricomi Laplace transform and Pfaff's transformation. -/
theorem kummerU_stieltjes_of_re_pos {a b z : ℂ} (hz : 0 < z.re)
    (ha : (b - 1).re < a.re) (ha0 : 0 < a.re) :
    kummerU a b z = z ^ (1 - a) / (Gamma a * Gamma (1 + a - b)) *
      ∫ t : ℝ in Set.Ioi 0, kummerU (b - a) b t * exp (-(t : ℂ)) * (t : ℂ) ^ (a - 1) /
        ((t : ℂ) + z) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hab : 0 < (1 + a - b).re := by simp only [sub_re, add_re, one_re] at ha ⊢; linarith
  have hGa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha0
  have hGab : Gamma (1 + a - b) ≠ 0 := Gamma_ne_zero_of_re_pos hab
  have hK := (laplace_kummerU_gauss (a := b - a) (b := a) (c := b) (z := 1) ha0 ha (by simp)).1
  set K := tricomiLaplaceKernel (b - a) a b 1 with hKdef
  set G : ℝ → ℝ → ℂ := fun t s => K t * exp (-((t : ℂ) + z) * s) with hG
  have he : IntegrableOn (fun s : ℝ => Real.exp (-z.re * s)) (Ioi 0) := exp_neg_integrableOn_Ioi 0 hz
  have hGi : Integrable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine (hK.norm.mul_prod he).mono' ?_ ?_
    · have hm : AEStronglyMeasurable (fun q : ℝ × ℝ => K q.1 * exp (-((q.1 : ℂ) + z) * q.2))
          ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) :=
        (hK.aestronglyMeasurable.comp_fst (ν := volume.restrict (Ioi (0:ℝ)))).mul
          (Continuous.aestronglyMeasurable (by fun_prop))
      exact hm
    · have hset : ∀ᵐ q ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))),
          q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
        rw [Measure.prod_restrict]
        exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
      filter_upwards [hset] with q hq
      obtain ⟨t, s⟩ := q
      obtain ⟨ht, hs⟩ := hq
      change 0 < t at ht; change 0 < s at hs
      simp only [hG, Function.uncurry_def, norm_mul, Complex.norm_exp]
      gcongr
      simp; nlinarith
  have hsinner : ∀ t ∈ Ioi (0 : ℝ), ∫ s : ℝ in Ioi 0, G t s = K t / ((t : ℂ) + z) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hne : (t : ℂ) + z ≠ 0 := fun h => by
      have := congrArg re h; simp at this; linarith
    simp only [hG]
    rw [integral_const_mul, integral_exp_mul_complex_Ioi (by simp; linarith) 0]
    simp only [ofReal_zero, mul_zero, exp_zero]
    field_simp
  have htinner : ∀ s ∈ Ioi (0 : ℝ), ∫ t : ℝ in Ioi 0, G t s =
      Gamma a * Gamma (1 + a - b) *
        kummerUGaussKernel a b 1 z s := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hL := laplace_kummerU (a := b - a) (b := a) (c := b) (z := 1 + s) ha0 ha
      (by simp; linarith)
    have h1s : (1 + (s : ℂ)) = ((1 + s : ℝ) : ℂ) := by push_cast; ring
    have hw : 1 - (1 + (s : ℂ))⁻¹ ∈ cutPlane := by
      change 1 - (1 - (1 + (s : ℂ))⁻¹) ∈ slitPlane
      rw [sub_sub_cancel, h1s, ← ofReal_inv]
      exact ofReal_mem_slitPlane.mpr (by positivity)
    have hp := regularizedGaussHG_pfaff a (b - a) 1 hw
    rw [regularizedGaussHG_symm _ _ _ hw] at hL
    have hq : (1 - (1 + (s : ℂ))⁻¹) / (1 - (1 + (s : ℂ))⁻¹ - 1) = -(s : ℂ) := by
      have : (1 + (s : ℂ)) ≠ 0 := by rw [h1s]; exact ofReal_ne_zero.mpr (by positivity)
      field_simp; ring
    rw [hq, sub_sub_cancel, show (1 : ℂ) - (b - a) = a - b + 1 by ring] at hp
    rw [show b - a + a - b + 1 = (1 : ℂ) by ring, hp] at hL
    have hpow : (1 + (s : ℂ)) ^ (-a) * ((1 + (s : ℂ))⁻¹) ^ (-a) = 1 := by
      rw [h1s, ← ofReal_inv, ← mul_cpow_ofReal_nonneg (by positivity) (by positivity),
        ← ofReal_mul, mul_inv_cancel₀ (by positivity : (1 + s : ℝ) ≠ 0), ofReal_one, one_cpow]
    have hG' : ∀ t : ℝ, G t s = tricomiLaplaceKernel (b - a) a b (1 + s) t * exp (-z * s) := by
      intro t
      simp only [hG, hKdef, tricomiLaplaceKernel]
      have : exp (-1 * (t : ℂ)) * exp (-((t : ℂ) + z) * s) = exp (-(1 + (s : ℂ)) * t) * exp (-z * s) := by
        rw [← exp_add, ← exp_add]; ring_nf
      linear_combination ((t : ℂ) ^ (a - 1) * kummerU (b - a) b t) * this
    simp_rw [hG']
    rw [integral_mul_const]
    change (∫ t : ℝ in Ioi 0, exp (-(1 + (s : ℂ)) * t) * (t : ℂ) ^ (a - 1) * kummerU (b - a) b t) *
      exp (-z * s) = _
    rw [hL, kummerUGaussKernel, sub_self, cpow_zero,
      show a - b + 1 = 1 + a - b by ring]
    linear_combination (Gamma a * Gamma (1 + a - b) * exp (-z * s) *
      regularizedGaussHG a (1 + a - b) 1 (-(s : ℂ))) * hpow
  have hrw : ∀ t ∈ Ioi (0 : ℝ), kummerU (b - a) b t * exp (-(t : ℂ)) * (t : ℂ) ^ (a - 1) /
      ((t : ℂ) + z) = ∫ s : ℝ in Ioi 0, G t s := by
    intro t ht
    rw [hsinner t ht, hKdef, tricomiLaplaceKernel]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hrw, integral_integral_swap hGi,
    setIntegral_congr_fun measurableSet_Ioi htinner, integral_const_mul]
  have hU := (kummerU_gauss_aux (a := a) (b := b) (c := 1) (by simp) hz).2
  rw [hU]
  field_simp

/-- Identity under the stated parameter and domain assumptions: `kummerU a b z = z ^ (1 - a) /
(Gamma a * Gamma (1 + a - b)) * ∫ t : ℝ in Set.Ioi 0, kummerU (b - a) b t * exp (-(t : ℂ)) *
(t : ℂ) ^ (a - 1) / ((t : ℂ) + z)`. -/
@[dlmf 13.4.E5]
theorem kummerU_stieltjes {a b z : ℂ} (hz : z ∈ slitPlane)
    (ha : (b - 1).re < a.re) (ha0 : 0 < a.re) :
    kummerU a b z =
      z ^ (1 - a) / (Gamma a * Gamma (1 + a - b)) *
        ∫ t : ℝ in Set.Ioi 0,
          kummerU (b - a) b t * exp (-(t : ℂ)) * (t : ℂ) ^ (a - 1) /
            ((t : ℂ) + z) := by
  have hK := (laplace_kummerU_gauss (a := b - a) (b := a) (c := b) (z := 1) ha0 ha (by simp)).1
  have hg : IntegrableOn (fun t : ℝ => kummerU (b - a) b t * exp (-(t : ℂ)) * (t : ℂ) ^ (a - 1))
      (Ioi 0) := hK.congr (Eventually.of_forall fun t => by
        simp only [tricomiLaplaceKernel, neg_mul, one_mul]; ring)
  have hS := differentiableOn_stieltjes_integral hg
  set h : ℂ → ℂ := fun z => z ^ (1 - a) / (Gamma a * Gamma (1 + a - b)) *
    ∫ t : ℝ in Set.Ioi 0, kummerU (b - a) b t * exp (-(t : ℂ)) * (t : ℂ) ^ (a - 1) /
      ((t : ℂ) + z) with hh
  have hf : AnalyticOnNhd ℂ (kummerU a b) slitPlane :=
    (differentiableOn_kummerU a b).analyticOnNhd isOpen_slitPlane
  have hha : AnalyticOnNhd ℂ h slitPlane := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) isOpen_slitPlane
    exact (((differentiableAt_id.cpow (differentiableAt_const _) hw).div_const _).differentiableWithinAt).mul
      (hS w hw)
  have heq : kummerU a b =ᶠ[𝓝 1] h := by
    have hnh : {w : ℂ | 0 < w.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [hnh] with w hw
    exact kummerU_stieltjes_of_re_pos hw ha ha0
  exact hf.eqOn_of_preconnected_of_eventuallyEq hha ((starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected)
    one_mem_slitPlane heq hz

/-- `1/(t+z)` is `O((1+t)^{-1})` on the positive half-line, for `z` in the slit plane. -/
theorem cfInt_norm_recip_add_le {z : ℂ} (hz : z ∈ slitPlane) :
    ∃ K, ∀ t : ℝ, 0 < t → ‖((t : ℂ) + z)⁻¹‖ ≤ K * (1 + t) ^ (-1 : ℝ) := by
  obtain ⟨δ, hδ, hδb⟩ := exists_forall_le_norm_add_of_mem_slitPlane hz
  refine ⟨1 / δ + 1 + ‖z‖ / δ, fun t ht => ?_⟩
  have h1 := hδb t ht.le z (Metric.mem_ball_self hδ)
  have hpos : 0 < ‖(t : ℂ) + z‖ := hδ.trans_le h1
  have h2 : t ≤ ‖(t : ℂ) + z‖ + ‖z‖ := by
    have := norm_sub_le ((t : ℂ) + z) z
    rw [add_sub_cancel_right, norm_real, Real.norm_of_nonneg ht.le] at this
    exact this
  have h3 : 1 + t ≤ (1 / δ + 1 + ‖z‖ / δ) * ‖(t : ℂ) + z‖ := by
    have e1 : 1 ≤ ‖(t : ℂ) + z‖ / δ := by rw [le_div_iff₀ hδ]; linarith
    have e2 : ‖z‖ ≤ ‖z‖ / δ * ‖(t : ℂ) + z‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    calc 1 + t ≤ ‖(t : ℂ) + z‖ / δ + (‖(t : ℂ) + z‖ + ‖z‖ / δ * ‖(t : ℂ) + z‖) := by
          linarith
      _ = _ := by ring
  rw [Real.rpow_neg_one, norm_inv, ← div_eq_mul_inv, le_div_iff₀ (by linarith),
    inv_mul_eq_div, div_le_iff₀ hpos]
  linarith

/-- For `-Re b < n < 1 + Re(a-b)` and `z` in the slit plane, `M̃(a,b,-t) t^{b+n-1}/(t+z)` is
integrable on `(0, ∞)`. -/
theorem cfInt_integrableOn_stieltjes {a b z : ℂ} {n : ℕ} (hz : z ∈ slitPlane)
    (h0 : -b.re < n) (h1 : (n : ℝ) < 1 + (a - b).re) :
    IntegrableOn (fun t : ℝ => regularizedHGFun {a} {b} (-(t : ℂ)) * (t : ℂ) ^ (b + n - 1) /
      ((t : ℂ) + z)) (Ioi 0) := by
  obtain ⟨K, hK⟩ := cfInt_norm_recip_add_le hz
  have hne : ∀ t : ℝ, 0 < t → (t : ℂ) + z ≠ 0 := fun t ht h => by
    obtain ⟨δ, hδ, hδb⟩ := exists_forall_le_norm_add_of_mem_slitPlane hz
    have := hδb t ht.le z (Metric.mem_ball_self hδ)
    rw [h, norm_zero] at this; linarith
  have hh : ContinuousOn (fun t : ℝ => ((t : ℂ) + z)⁻¹) (Ioi 0) :=
    ContinuousOn.inv₀ (by fun_prop) fun t ht => hne t ht
  have hI := integrableOn_cpow_mul_regularizedHGFun_neg_mul (a := a) (b := b) (c := b + n)
    hh hK (by simp; linarith) (by simp at h1 ⊢; linarith)
  refine hI.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [div_eq_mul_inv]
  ring

/-- `∫₀^∞ e^{-ws} ds = 1/w` for `Re w > 0`. -/
theorem cfInt_integral_exp_Ioi {w : ℂ} (hw : 0 < w.re) :
    ∫ s : ℝ in Ioi 0, exp (-w * s) = w⁻¹ := by
  rw [integral_exp_mul_complex_Ioi (by simpa using hw) 0]
  simp [div_neg, neg_div]

/-- `∫₀^∞ |e^{-ws}| ds = 1/Re w` for `Re w > 0`. -/
theorem cfInt_integral_norm_exp_Ioi {w : ℂ} (hw : 0 < w.re) :
    ∫ s : ℝ in Ioi 0, ‖exp (-w * s)‖ = (w.re)⁻¹ := by
  have h := cfInt_integral_exp_Ioi (w := (w.re : ℂ)) (by simpa using hw)
  have he : ∀ s : ℝ, ‖exp (-w * s)‖ = Real.exp (-w.re * s) := fun s => by
    rw [Complex.norm_exp]; simp
  simp_rw [he]
  have h2 : ∫ s : ℝ in Ioi 0, ((Real.exp (-w.re * s) : ℝ) : ℂ) = ((w.re)⁻¹ : ℝ) := by
    rw [ofReal_inv, ← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [ofReal_exp]; push_cast; ring_nf
  rw [integral_complex_ofReal] at h2
  exact_mod_cast h2

/-- The base case `n = 0` of 13.4.6 in the right half-plane, by Fubini against
`1/(t+z) = ∫ e^{-(t+z)s} ds`, the Kummer Laplace transform 13.10.3 and Tricomi's Laplace
integral 13.4.4. -/
theorem cfInt_stieltjes_zero_of_re_pos {a b z : ℂ} (hz : 0 < z.re) (hb : 0 < b.re)
    (hab : b.re < 1 + a.re) :
    ∫ t : ℝ in Ioi 0, regularizedHGFun {a} {b} (-(t : ℂ)) * (t : ℂ) ^ (b - 1) / ((t : ℂ) + z) =
      z ^ (b - 1) * Gamma (1 + a - b) * kummerU a b z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  set g : ℝ → ℂ := fun t => regularizedHGFun {a} {b} (-(t : ℂ)) * (t : ℂ) ^ (b - 1) with hg
  set G : ℝ → ℝ → ℂ := fun t s => g t * exp (-((t : ℂ) + z) * s) with hG
  have hgc : ContinuousOn g (Ioi 0) :=
    (kumDec_continuous_neg a b).continuousOn.mul (ContinuousOn.cpow continuous_ofReal.continuousOn
      continuousOn_const fun t ht => ofReal_mem_slitPlane.mpr ht)
  have hxz : ((z.re : ℝ) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hz
  have hS := cfInt_integrableOn_stieltjes (a := a) (b := b) (n := 0) hxz (by simpa using hb)
    (by simp; linarith)
  simp only [CharP.cast_eq_zero, add_zero] at hS
  have hGi : Integrable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    have hm : AEStronglyMeasurable (Function.uncurry G)
        ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) :=
      ((hgc.aestronglyMeasurable measurableSet_Ioi).comp_fst
        (ν := volume.restrict (Ioi (0:ℝ)))).mul (Continuous.aestronglyMeasurable (by fun_prop))
    refine (integrable_prod_iff hm).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      exact (integrableOn_exp_mul_complex_Ioi (a := -((t : ℂ) + z)) (by simp; linarith) 0).const_mul
        (g t) |>.congr (Eventually.of_forall fun s => by simp [Function.uncurry, hG])
    · refine hS.norm.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      simp only [Function.uncurry_apply_pair, hG, norm_mul]
      rw [integral_const_mul, cfInt_integral_norm_exp_Ioi (by simp; linarith), norm_div,
        div_eq_mul_inv]
      congr 2
      rw [show ((t : ℂ) + ((z.re : ℝ) : ℂ)) = ((t + z.re : ℝ) : ℂ) by push_cast; ring, norm_real,
        Real.norm_of_nonneg (by linarith)]
      simp
  have hsinner : ∀ t ∈ Ioi (0 : ℝ), ∫ s : ℝ in Ioi 0, G t s = g t / ((t : ℂ) + z) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    simp only [hG]
    rw [integral_const_mul, cfInt_integral_exp_Ioi (by simp; linarith), div_eq_mul_inv]
  have htinner : ∀ s ∈ Ioi (0 : ℝ), ∫ t : ℝ in Ioi 0, G t s =
      exp (-z * s) * ((s : ℂ) ^ (a - b) * (1 + (s : ℂ)) ^ (-a)) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hL := laplace_regularizedHGFun (a := a) (b := b) (c := b) (k := -1) (z := s) hb
      (by simp; linarith) (by simpa using hs0)
    have hw : (-1 : ℂ) / s ∈ cutPlane := by
      change 1 - (-1 : ℂ) / s ∈ slitPlane
      rw [show (1 : ℂ) - (-1) / s = ((1 + s⁻¹ : ℝ) : ℂ) by push_cast; ring]
      exact ofReal_mem_slitPlane.mpr (by positivity)
    rw [regularizedGaussHG_self_right a b hw] at hL
    have hpow : (s : ℂ) ^ (-b) * (1 - (-1 : ℂ) / s) ^ (-a) =
        (s : ℂ) ^ (a - b) * (1 + (s : ℂ)) ^ (-a) := by
      have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs0.ne'
      rw [show (1 : ℂ) - (-1) / s = ((1 + s : ℝ) : ℂ) * ((s⁻¹ : ℝ) : ℂ) by push_cast; field_simp; ring,
        mul_cpow_ofReal_nonneg (by positivity) (by positivity), ofReal_inv,
        inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hs0.le]; exact Real.pi_ne_zero.symm),
        ← cpow_neg, neg_neg, sub_eq_add_neg, cpow_add _ _ hs']
      push_cast; ring
    have hGb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
    calc ∫ t : ℝ in Ioi 0, G t s
        = exp (-z * s) * ∫ t : ℝ in Ioi 0,
            exp (-(s : ℂ) * t) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} (-1 * t) := by
          rw [← integral_const_mul]
          refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
          simp only [hG, hg, neg_one_mul]
          have : exp (-((t : ℂ) + z) * s) = exp (-z * s) * exp (-(s : ℂ) * t) := by
            rw [← Complex.exp_add]; ring_nf
          rw [this]; ring
      _ = _ := by
          rw [hL, mul_assoc (Gamma b), ← mul_assoc ((s : ℂ) ^ (-b)), hpow]
          field_simp
  have hU := kummerU_laplace (a := a - b + 1) (b := 2 - b) (z := z) (by simp; linarith) hz
  rw [show (2 - b) - (a - b + 1) - 1 = -a by ring, show a - b + 1 - 1 = a - b by ring] at hU
  have hG1 : Gamma (a - b + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hK := kummerU_kummer_transform_all a b hz0
  calc ∫ t : ℝ in Ioi 0, regularizedHGFun {a} {b} (-(t : ℂ)) * (t : ℂ) ^ (b - 1) / ((t : ℂ) + z)
      = ∫ t : ℝ in Ioi 0, ∫ s : ℝ in Ioi 0, G t s :=
        setIntegral_congr_fun measurableSet_Ioi fun t ht => (hsinner t ht).symm
    _ = ∫ s : ℝ in Ioi 0, ∫ t : ℝ in Ioi 0, G t s := integral_integral_swap hGi
    _ = ∫ s : ℝ in Ioi 0, exp (-z * s) * ((s : ℂ) ^ (a - b) * (1 + (s : ℂ)) ^ (-a)) :=
        setIntegral_congr_fun measurableSet_Ioi htinner
    _ = Gamma (a - b + 1) * kummerU (a - b + 1) (2 - b) z := by
        rw [hU]; field_simp
    _ = _ := by
        have hzz : z ^ (b - 1) * z ^ (1 - b) = 1 := by
          rw [← cpow_add _ _ hz0, show b - 1 + (1 - b) = 0 by ring, cpow_zero]
        rw [hK, show 1 + a - b = a - b + 1 by ring]
        linear_combination (-(Gamma (a - b + 1) * kummerU (a - b + 1) (2 - b) z)) * hzz

/-- For `z` in the slit plane and real `t ≥ 0`, `t + z ≠ 0`. -/
theorem cfInt_add_ne_zero {z : ℂ} (hz : z ∈ slitPlane) {t : ℝ} (ht : 0 ≤ t) : (t : ℂ) + z ≠ 0 := by
  obtain ⟨δ, hδ, hδb⟩ := exists_forall_le_norm_add_of_mem_slitPlane hz
  intro h
  have := hδb t ht z (Metric.mem_ball_self hδ)
  rw [h, norm_zero] at this; linarith

/-- A Stieltjes transform is holomorphic on the slit plane as soon as `g(t)/(t+1)` is integrable. -/
theorem cfInt_differentiableOn_stieltjes {g : ℝ → ℂ}
    (hg : IntegrableOn (fun t : ℝ => g t / ((t : ℂ) + 1)) (Ioi 0)) :
    DifferentiableOn ℂ (fun z => ∫ t : ℝ in Ioi 0, g t / ((t : ℂ) + z)) slitPlane := by
  set h : ℝ → ℂ := fun t => g t / ((t : ℂ) + 1) with hh
  have hS := differentiableOn_stieltjes_integral hg
  have hD : DifferentiableOn ℂ (fun z => (∫ t : ℝ in Ioi 0, h t) +
      (1 - z) * ∫ t : ℝ in Ioi 0, h t / ((t : ℂ) + z)) slitPlane :=
    (differentiableOn_const _).add ((differentiableOn_const _ |>.sub differentiableOn_id).mul hS)
  refine hD.congr fun z hz => ?_
  obtain ⟨δ, hδ, hδb⟩ := exists_forall_le_norm_add_of_mem_slitPlane hz
  have hint : IntegrableOn (fun t : ℝ => h t / ((t : ℂ) + z)) (Ioi 0) := by
    refine (hg.norm.const_mul δ⁻¹).mono' (hg.aestronglyMeasurable.mul
      (Measurable.aestronglyMeasurable (by fun_prop))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_div, div_eq_mul_inv, mul_comm]
    gcongr
    exact hδb t (le_of_lt ht) z (Metric.mem_ball_self hδ)
  rw [← integral_const_mul, ← integral_add hg (hint.const_mul _)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have h1 : (t : ℂ) + 1 ≠ 0 := cfInt_add_ne_zero one_mem_slitPlane (le_of_lt ht)
  have h2 : (t : ℂ) + z ≠ 0 := cfInt_add_ne_zero hz (le_of_lt ht)
  simp only [hh]
  field_simp
  ring

/-- The case `n = 0` of 13.4.6 on the slit plane. -/
theorem cfInt_stieltjes_zero {a b z : ℂ} (hz : z ∈ slitPlane) (hb : 0 < b.re)
    (hab : b.re < 1 + a.re) :
    ∫ t : ℝ in Ioi 0, regularizedHGFun {a} {b} (-(t : ℂ)) * (t : ℂ) ^ (b - 1) / ((t : ℂ) + z) =
      z ^ (b - 1) * Gamma (1 + a - b) * kummerU a b z := by
  have hS := cfInt_integrableOn_stieltjes (a := a) (b := b) (n := 0) one_mem_slitPlane
    (by simpa using hb) (by simp; linarith)
  simp only [CharP.cast_eq_zero, add_zero] at hS
  have hL := cfInt_differentiableOn_stieltjes hS
  have hLa : AnalyticOnNhd ℂ (fun z => ∫ t : ℝ in Ioi 0,
      regularizedHGFun {a} {b} (-(t : ℂ)) * (t : ℂ) ^ (b - 1) / ((t : ℂ) + z)) slitPlane :=
    hL.analyticOnNhd isOpen_slitPlane
  have hRa : AnalyticOnNhd ℂ (fun z => z ^ (b - 1) * Gamma (1 + a - b) * kummerU a b z)
      slitPlane := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) isOpen_slitPlane
    exact ((((differentiableAt_id.cpow (differentiableAt_const _) hw).mul_const _).mul
      ((differentiableOn_kummerU a b).differentiableAt (isOpen_slitPlane.mem_nhds hw)))).differentiableWithinAt
  have heq : (fun z => ∫ t : ℝ in Ioi 0,
      regularizedHGFun {a} {b} (-(t : ℂ)) * (t : ℂ) ^ (b - 1) / ((t : ℂ) + z)) =ᶠ[𝓝 1]
      fun z => z ^ (b - 1) * Gamma (1 + a - b) * kummerU a b z := by
    have hnh : {w : ℂ | 0 < w.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [hnh] with w hw
    exact cfInt_stieltjes_zero_of_re_pos hw hb hab
  exact hLa.eqOn_of_preconnected_of_eventuallyEq hRa
    ((starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected)
    one_mem_slitPlane heq hz

/-- `b U(a,b+1,z) - a z U(a+1,b+2,z) = (b-a) U(a,b,z)`, from the contiguous relations 13.3.9
and 13.3.10; it is the Tricomi counterpart of 13.3.20 with `n = 1`. -/
theorem cfInt_kummerU_rel (a b : ℂ) {z : ℂ} (hz : z ≠ 0) :
    b * kummerU a (b + 1) z - a * z * kummerU (a + 1) (b + 2) z = (b - a) * kummerU a b z := by
  have h1 := kummerU_contiguous_shift_a (a + 1) (b + 1) z hz
  have h2 := kummerU_contiguous_a_b a (b + 1) z hz
  rw [add_sub_cancel_right, show b + 1 + 1 = b + 2 by ring] at h1
  rw [add_sub_cancel_right] at h2
  linear_combination a * h1 + (b - a) * h2

/-- 13.4.6 in the form `∫ 𝐌(a,b,-t) t^{b+n-1}/(t+z) dt = (-1)^n z^{b+n-1} Γ(1+a-b) U(a,b,z)`. -/
theorem cfInt_stieltjes_nat : ∀ n : ℕ, ∀ a b z : ℂ, z ∈ slitPlane → -b.re < n →
    (n : ℝ) < 1 + (a - b).re →
    ∫ t : ℝ in Ioi 0, regularizedHGFun {a} {b} (-(t : ℂ)) * (t : ℂ) ^ (b + n - 1) /
        ((t : ℂ) + z) =
      (-1) ^ n * z ^ (b + n - 1) * Gamma (1 + a - b) * kummerU a b z := by
  intro n
  induction n with
  | zero =>
    intro a b z hz h0 h1
    simp only [CharP.cast_eq_zero, add_zero, pow_zero, one_mul] at h0 h1 ⊢
    exact cfInt_stieltjes_zero hz (by linarith) (by simp at h1; linarith)
  | succ n ih =>
    intro a b z hz h0 h1
    have hz0 : z ≠ 0 := slitPlane_ne_zero hz
    push_cast at h0 h1
    have hab : (n : ℝ) < (a - b).re := by linarith
    have i1 := ih a (b + 1) z hz (by simp; linarith) (by simp at hab ⊢; linarith)
    have i2 := ih (a + 1) (b + 2) z hz (by simp; linarith) (by simp at hab ⊢; linarith)
    have I1 := cfInt_integrableOn_stieltjes (a := a) (b := b + 1) (n := n) hz
      (by simp; linarith) (by simp at hab ⊢; linarith)
    have I2 := cfInt_integrableOn_stieltjes (a := a + 1) (b := b + 2) (n := n) hz
      (by simp; linarith) (by simp at hab ⊢; linarith)
    have hpt : ∀ t ∈ Ioi (0 : ℝ), regularizedHGFun {a} {b} (-(t : ℂ)) *
        (t : ℂ) ^ (b + ((n + 1 : ℕ) : ℂ) - 1) / ((t : ℂ) + z) =
        b * (regularizedHGFun {a} {b + 1} (-(t : ℂ)) * (t : ℂ) ^ (b + 1 + n - 1) /
          ((t : ℂ) + z)) -
        a * (regularizedHGFun {a + 1} {b + 2} (-(t : ℂ)) * (t : ℂ) ^ (b + 2 + n - 1) /
          ((t : ℂ) + z)) := by
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
      have hrel := regularizedConfluent_contiguous_mixed_b_pred a (b + 1) (-(t : ℂ))
      rw [add_sub_cancel_right, show b + 1 + 1 = b + 2 by ring] at hrel
      have hp : (t : ℂ) ^ (b + 2 + n - 1) = (t : ℂ) * (t : ℂ) ^ (b + 1 + n - 1) := by
        rw [show b + 2 + n - 1 = 1 + (b + 1 + n - 1) by ring, cpow_add _ _ ht0, cpow_one]
      rw [hp, show b + ((n + 1 : ℕ) : ℂ) - 1 = b + 1 + n - 1 by push_cast; ring]
      have h2 : (t : ℂ) + z ≠ 0 := cfInt_add_ne_zero hz (le_of_lt ht)
      field_simp
      linear_combination (-(t : ℂ) ^ (b + 1 + n - 1)) * hrel
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub (I1.const_mul _)
      (I2.const_mul _), integral_const_mul, integral_const_mul, i1, i2]
    have hrel := cfInt_kummerU_rel a b hz0
    have hG : Gamma (1 + a - b) = (a - b) * Gamma (a - b) := by
      rw [show 1 + a - b = (a - b) + 1 by ring, Gamma_add_one]
      intro h; rw [h] at hab; simp at hab; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hpz : z ^ (b + 2 + n - 1) = z * z ^ (b + 1 + n - 1) := by
      rw [show b + 2 + n - 1 = 1 + (b + 1 + n - 1) by ring, cpow_add _ _ hz0, cpow_one]
    rw [show b + ((n + 1 : ℕ) : ℂ) - 1 = b + 1 + n - 1 by push_cast; ring, hpz, hG,
      show 1 + a - (b + 1) = a - b by ring, show 1 + (a + 1) - (b + 2) = a - b by ring, pow_succ]
    linear_combination ((-1) ^ n * z ^ (b + 1 + n - 1) * Gamma (a - b)) * hrel

/-- Tricomi's Stieltjes representation 13.4.6, for every admissible `n`. The case `n = 0` is
Fubini against `1/(t+z) = ∫ e^{-(t+z)s} ds`, the Kummer Laplace transform 13.10.3 and
Tricomi's Laplace integral 13.4.4, continued from the right half-plane; the decay
`𝐌(a,b,-t) = O(t^{-Re a})` (`DLMF.Confluent.KummerDecay`) gives convergence. The step
`n ↦ n + 1` combines the contiguous relation 13.3.20 (`n = 1`) of `𝐌` with its Tricomi
counterpart `cfInt_kummerU_rel`. (Moved unchanged from `IntegralRepresentations`, which
precedes the Laplace transforms in the import order.) -/
@[dlmf 13.4.E6]
theorem kummerU_stieltjes_regularized {a b z : ℂ} (n : ℕ) (hz : z ∈ slitPlane)
    (hn0 : -b.re < n) (hn1 : (n : ℝ) < 1 + (a - b).re) :
    kummerU a b z =
      (-1 : ℂ) ^ n * z ^ (1 - b - n) / Gamma (1 + a - b) *
        ∫ t : ℝ in Set.Ioi 0,
          regularizedHGFun {b - a} {b} t * exp (-(t : ℂ)) * (t : ℂ) ^ (b + n - 1) /
            ((t : ℂ) + z) := by
  have hz0 := slitPlane_ne_zero hz
  have h := cfInt_stieltjes_nat n a b z hz hn0 hn1
  have hG : Gamma (1 + a - b) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp only [sub_re, add_re, one_re] at hn1 ⊢; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hcongr : ∀ t ∈ Ioi (0 : ℝ), regularizedHGFun {b - a} {b} t * exp (-(t : ℂ)) *
      (t : ℂ) ^ (b + n - 1) / ((t : ℂ) + z) =
      regularizedHGFun {a} {b} (-(t : ℂ)) * (t : ℂ) ^ (b + n - 1) / ((t : ℂ) + z) := by
    intro t _
    rw [regularizedConfluent_kummer_transform a b (-(t : ℂ)), neg_neg]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, h]
  have hzz : z ^ (1 - b - n) * z ^ (b + n - 1) = 1 := by
    rw [← cpow_add _ _ hz0, show 1 - b - n + (b + n - 1) = 0 by ring, cpow_zero]
  have hpm : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  calc kummerU a b z = ((-1 : ℂ) ^ n * (-1) ^ n) * (z ^ (1 - b - n) * z ^ (b + n - 1)) *
        (Gamma (1 + a - b) / Gamma (1 + a - b)) * kummerU a b z := by
        rw [hpm, hzz, div_self hG]; ring
    _ = _ := by ring

/-- Identity under the stated parameter and domain assumptions: `whittakerW κ μ z = exp (-z / 2) *
z ^ (κ + 1) / (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) * ∫ t : ℝ in Set.Ioi 0,
whittakerW (-κ) μ t * exp (-(t : ℂ) / 2) * (t : ℂ) ^ (-κ - 1) / ((t : ℂ) + z)`. -/
@[dlmf 13.16.E6]
theorem whittakerW_stieltjes {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hκ : (2 * μ.re) < (1 / 2 + μ - κ).re) (hκ0 : 0 < (1 / 2 + μ - κ).re) :
    whittakerW κ μ z =
      exp (-z / 2) * z ^ (κ + 1) /
          (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) *
        ∫ t : ℝ in Set.Ioi 0,
          whittakerW (-κ) μ t * exp (-(t : ℂ) / 2) * (t : ℂ) ^ (-κ - 1) /
            ((t : ℂ) + z) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hU := kummerU_stieltjes (a := 1 / 2 + μ - κ) (b := 1 + 2 * μ) hz
    (by simpa using hκ) hκ0
  rw [show 1 + (1 / 2 + μ - κ) - (1 + 2 * μ) = 1 / 2 - μ - κ by ring,
    show 1 + 2 * μ - (1 / 2 + μ - κ) = 1 / 2 + μ - (-κ) by ring] at hU
  have hint : ∀ t ∈ Ioi (0 : ℝ),
      whittakerW (-κ) μ t * exp (-(t : ℂ) / 2) * (t : ℂ) ^ (-κ - 1) / ((t : ℂ) + z) =
        kummerU (1 / 2 + μ - (-κ)) (1 + 2 * μ) t * exp (-(t : ℂ)) * (t : ℂ) ^ (1 / 2 + μ - κ - 1) /
          ((t : ℂ) + z) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    rw [whittakerW, show 1 / 2 + μ - κ - 1 = (1 / 2 + μ) + (-κ - 1) by ring,
      cpow_add (x := (t : ℂ)) (1 / 2 + μ) (-κ - 1) ht0]
    have he : exp (-(t : ℂ) / 2) * exp (-(t : ℂ) / 2) = exp (-(t : ℂ)) := by
      rw [← exp_add]; ring_nf
    rw [← he]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hint, whittakerW, hU]
  have hp : z ^ (1 / 2 + μ) * z ^ (1 - (1 / 2 + μ - κ)) = z ^ (κ + 1) := by
    rw [← cpow_add _ _ hz0]; ring_nf
  rw [← hp]; ring

end GaussStieltjes

/-!
### The Gaussian transform 13.10.6

Proof of 13.10.6 for real `z = ζ > 0`: subordinate `e^{-ζt}` to a Gaussian in `t` via the
`K_{1/2}` Schläfli integral, interchange the integrals (Fubini), evaluate the inner `t`-integral
by 13.10.3 with `s = t²`, apply Pfaff's transformation, and recognize the outer integral as
13.4.8 after `u ↦ 1/u`. The identity is then continued holomorphically to `Re z > 0`.
-/

end DLMF.Confluent
end
end
