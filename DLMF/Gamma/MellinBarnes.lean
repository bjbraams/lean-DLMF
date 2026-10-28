/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.VerticalBounds
public import DLMF.Gamma.BetaFunction
public import Mathlib.Analysis.MellinInversion
import DLMF.Gamma.RecipGammaDeriv

/-!
# The basic Mellin–Barnes integral

For `0 < σ < re a` and `u > 0`,

`Γ(a) (1+u)^{-a} = 1/(2π) ∫ Γ(σ+iy) Γ(a-σ-iy) u^{-σ-iy} dy`,

the Mellin inversion (Mathlib's `mellinInv_mellin_eq`) of the Beta integral
`∫₀^∞ t^{s-1} (1+t)^{-a} dt = Γ(s)Γ(a-s)/Γ(a)` (DLMF 5.12.3). The vertical integrability comes
from the bounds of `DLMF.Gamma.VerticalBounds`.
-/

@[expose] public section

open Complex Filter Set MeasureTheory
open scoped Topology Real

noncomputable section

namespace DLMF.Gamma

/-- A bound `C (1+|y|)^K e^{-π|y|/2}` for `Γ(x + i(β+y))`, any real shift `β`. -/
theorem exists_norm_Gamma_shift_le {x : ℝ} (hx : 0 < x) (β : ℝ) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ y : ℝ,
      ‖Complex.Gamma (x + I * (β + y))‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2) := by
  obtain ⟨C, K, hC⟩ := exists_norm_Gamma_le hx
  refine ⟨C * (1 + |β|) ^ K * Real.exp (π * |β| / 2), K, fun y => ?_⟩
  have h := hC (β + y)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (by simpa using hC 0)
  push_cast at h
  refine h.trans ?_
  have h1 : (1 + |β + y|) ^ K ≤ (1 + |β|) ^ K * (1 + |y|) ^ K := by
    rw [← mul_pow]
    gcongr
    nlinarith [abs_add_le β y, abs_nonneg β, abs_nonneg y]
  have h2 : Real.exp (-(π * |β + y|) / 2) ≤ Real.exp (π * |β| / 2) * Real.exp (-(π * |y|) / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : |y| ≤ |β + y| + |β| := by
      have := abs_add_le (β + y) (-β)
      rwa [abs_neg, show β + y + -β = y by ring] at this
    nlinarith [Real.pi_pos]
  calc C * (1 + |β + y|) ^ K * Real.exp (-(π * |β + y|) / 2)
      ≤ C * ((1 + |β|) ^ K * (1 + |y|) ^ K) *
          (Real.exp (π * |β| / 2) * Real.exp (-(π * |y|) / 2)) := by
        gcongr
    _ = _ := by ring

/-- The Beta integral as a Mellin transform (DLMF 5.12.3). -/
theorem mellin_one_add_cpow_neg {a s : ℂ} (hs : 0 < s.re) (hsa : s.re < a.re) :
    mellin (fun t : ℝ => ((1 + t : ℝ) : ℂ) ^ (-a)) s = Gamma s * Gamma (a - s) / Gamma a := by
  have has : 0 < (a - s).re := by simp only [sub_re]; linarith
  have hb := beta_on_Ioi hs has
  rw [show s + (a - s) = a by ring] at hb
  have hΓ := Complex.Gamma_mul_Gamma_eq_betaIntegral hs has
  rw [show s + (a - s) = a by ring] at hΓ
  have ha : Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  rw [mellin, eq_div_iff ha, hΓ, ← hb, mul_comm]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [smul_eq_mul]
  rw [cpow_neg, div_eq_mul_inv]
  push_cast; ring

/-- `t^(σ-1) (1 + t)^(-α)` is integrable on `(0, ∞)` when `0 < σ < α`. -/
theorem integrableOn_rpow_mul_one_add_rpow {σ α : ℝ} (hσ : 0 < σ) (hσα : σ < α) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * (1 + t) ^ (-α)) (Ioi 0) := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ (σ - 1) * (1 + t) ^ (-α)) (Ioi 0) := by
    intro t ht
    have ht0 : 0 < t := ht
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')).mul
      (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt (by linarith : (0 : ℝ) < 1 + t))) |>.comp
        (continuousAt_const.add continuousAt_id))).continuousWithinAt
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun t : ℝ => t ^ (σ - 1)) (Ioc 0 1) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
    refine h1.mono' ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : (1 + t) ^ (-α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    calc t ^ (σ - 1) * (1 + t) ^ (-α) ≤ t ^ (σ - 1) * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := mul_one _
  · have h1 : IntegrableOn (fun t : ℝ => t ^ (σ - 1 - α)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine h1.mono' ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (1 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h2 : (1 + t) ^ (-α) ≤ t ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    calc t ^ (σ - 1) * (1 + t) ^ (-α) ≤ t ^ (σ - 1) * t ^ (-α) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by rw [← Real.rpow_add (by linarith)]; ring_nf

/-- The Mellin transform of `(1 + t)^(-a)` converges at `σ` when `0 < σ < Re a`. -/
theorem mellinConvergent_one_add_cpow_neg {a : ℂ} {σ : ℝ} (hσ : 0 < σ) (hσa : σ < a.re) :
    MellinConvergent (fun t : ℝ => ((1 + t : ℝ) : ℂ) ^ (-a)) σ := by
  have hg := integrableOn_rpow_mul_one_add_rpow hσ hσa
  have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ ((σ : ℂ) - 1) • ((1 + t : ℝ) : ℂ) ^ (-a))
      (Ioi 0) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    refine ContinuousAt.continuousWithinAt ?_
    simp only [smul_eq_mul]
    refine ContinuousAt.mul ?_ ?_
    · exact ContinuousAt.cpow continuous_ofReal.continuousAt continuousAt_const
        (ofReal_mem_slitPlane.mpr ht0)
    · exact ContinuousAt.cpow (continuous_ofReal.continuousAt.comp
        (continuousAt_const.add continuousAt_id)) continuousAt_const
        (ofReal_mem_slitPlane.mpr (by linarith))
  refine hg.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht0, norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simp

/-- The complex Gamma function is continuous at every point of the right half-plane. -/
theorem continuousAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) : ContinuousAt Complex.Gamma s :=
  (Complex.differentiableAt_Gamma s fun m h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).continuousAt

/-- `y ↦ Γ(σ+iy) Γ(a-σ-iy)` is integrable for `0 < σ < re a`. -/
theorem integrable_Gamma_mul_Gamma_vertical {a : ℂ} {σ : ℝ} (hσ : 0 < σ) (hσa : σ < a.re) :
    Integrable (fun y : ℝ => Gamma (σ + y * I) * Gamma (a - (σ + y * I))) := by
  obtain ⟨C₁, K₁, h₁⟩ := exists_norm_Gamma_shift_le hσ 0
  obtain ⟨C₂, K₂, h₂⟩ := exists_norm_Gamma_shift_le (x := a.re - σ) (by linarith) a.im
  have e₁ : ∀ y : ℝ, (σ : ℂ) + y * I = ((σ : ℝ) : ℂ) + I * (((0 : ℝ) : ℂ) + (y : ℂ)) := fun y => by
    push_cast; ring
  have e₂ : ∀ y : ℝ, a - (σ + y * I) = ((a.re - σ : ℝ) : ℂ) + I * ((a.im : ℂ) + ((-y : ℝ) : ℂ)) :=
    fun y => by apply Complex.ext <;> simp; ring
  have hcont : Continuous fun y : ℝ => Gamma (σ + y * I) * Gamma (a - (σ + y * I)) := by
    refine continuous_iff_continuousAt.mpr fun y => ContinuousAt.mul ?_ ?_
    · exact (continuousAt_Gamma_of_re_pos (by simp [hσ])).comp (by fun_prop)
    · exact (continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
  refine ((integrable_one_add_abs_pow_mul_exp_neg Real.pi_pos (K₁ + K₂)).const_mul
    (C₁ * C₂)).mono' hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have b₁ := h₁ y
  have b₂ := h₂ (-y)
  rw [← e₁] at b₁
  rw [← e₂, abs_neg] at b₂
  rw [norm_mul]
  calc ‖Gamma (σ + y * I)‖ * ‖Gamma (a - (σ + y * I))‖
      ≤ (C₁ * (1 + |y|) ^ K₁ * Real.exp (-(π * |y|) / 2)) *
          (C₂ * (1 + |y|) ^ K₂ * Real.exp (-(π * |y|) / 2)) :=
        mul_le_mul b₁ b₂ (norm_nonneg _) ((norm_nonneg _).trans b₁)
    _ = C₁ * C₂ * ((1 + |y|) ^ (K₁ + K₂) * Real.exp (-(π * |y|))) := by
        rw [pow_add, show -(π * |y|) = -(π * |y|) / 2 + -(π * |y|) / 2 by ring, Real.exp_add]
        ring_nf

/-- **The basic Mellin–Barnes integral** (DLMF 5.13.? in Mellin form): for `0 < σ < re a` and
`u > 0`, `Γ(a) (1+u)^{-a} = 1/(2π) ∫ Γ(σ+iy) Γ(a-σ-iy) u^{-σ-iy} dy`. -/
theorem Gamma_mul_one_add_cpow_neg {a : ℂ} {σ : ℝ} (hσ : 0 < σ) (hσa : σ < a.re) {u : ℝ}
    (hu : 0 < u) :
    Gamma a * ((1 + u : ℝ) : ℂ) ^ (-a) =
      1 / (2 * π) * ∫ y : ℝ, Gamma (σ + y * I) * Gamma (a - (σ + y * I)) *
        (u : ℂ) ^ (-((σ : ℂ) + y * I)) := by
  set f : ℝ → ℂ := fun t => ((1 + t : ℝ) : ℂ) ^ (-a) with hf
  have hmel : ∀ y : ℝ, mellin f (σ + y * I) =
      Gamma (σ + y * I) * Gamma (a - (σ + y * I)) / Gamma a := fun y =>
    mellin_one_add_cpow_neg (by simp [hσ]) (by simp [hσa])
  have hvert : VerticalIntegrable (mellin f) σ := by
    refine ((integrable_Gamma_mul_Gamma_vertical hσ hσa).div_const (Gamma a)).congr
      (Eventually.of_forall fun y => ?_)
    exact (hmel y).symm
  have hcont : ContinuousAt f u :=
    ContinuousAt.cpow (continuous_ofReal.continuousAt.comp
      (continuousAt_const.add continuousAt_id)) continuousAt_const
      (ofReal_mem_slitPlane.mpr (by linarith))
  have hinv := mellinInv_mellin_eq σ f hu (mellinConvergent_one_add_cpow_neg hσ hσa) hvert hcont
  rw [mellinInv] at hinv
  simp only [hmel, smul_eq_mul] at hinv
  have ha : Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  rw [show f u = ((1 + u : ℝ) : ℂ) ^ (-a) from rfl] at hinv
  rw [← hinv]
  have hint : ∫ y : ℝ, (u : ℂ) ^ (-((σ : ℂ) + y * I)) *
      (Gamma (σ + y * I) * Gamma (a - (σ + y * I)) / Gamma a) =
      (∫ y : ℝ, Gamma (σ + y * I) * Gamma (a - (σ + y * I)) *
        (u : ℂ) ^ (-((σ : ℂ) + y * I))) / Gamma a := by
    rw [← integral_div]; congr 1; funext y; ring
  rw [hint, Complex.real_smul]
  generalize (∫ y : ℝ, Gamma (σ + y * I) * Gamma (a - (σ + y * I)) *
    (u : ℂ) ^ (-((σ : ℂ) + y * I))) = J
  push_cast
  field_simp

/-- A bound for `1/Γ` on closed unit discs about the points `c + σ + iy`, `c` near `c₀`. -/
theorem exists_norm_recip_Gamma_disc_le (c₀ : ℂ) (σ : ℝ) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ c ∈ Metric.ball c₀ 1, ∀ y : ℝ, ∀ w : ℂ, ‖w - (c + σ + I * y)‖ ≤ 1 →
      ‖(Gamma w)⁻¹‖ ≤ C * (1 + |y|) ^ K * Real.exp (π * |y| / 2) := by
  obtain ⟨C, K, hC⟩ := exists_norm_recip_Gamma_le (|c₀.re + σ| + 2)
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1 ⟨by linarith [abs_nonneg (c₀.re + σ)],
      by linarith [abs_nonneg (c₀.re + σ)]⟩ 0)
    simpa using this
  refine ⟨C * (3 + |c₀.im|) ^ K * Real.exp (π * (|c₀.im| + 2) / 2), K, fun c hc y w hw => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hc
  have hre : |w.re - (c₀.re + σ)| ≤ 2 := by
    have h1 := abs_re_le_norm (w - (c + σ + I * y))
    have h2 := abs_re_le_norm (c - c₀)
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, mul_zero,
      sub_zero, add_zero] at h1 h2
    replace h1 := h1.trans hw
    have := abs_sub (w.re - (c.re + σ)) (c₀.re - c.re)
    rw [abs_le] at h1 h2 ⊢; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have him : |w.im| ≤ |y| + |c₀.im| + 2 := by
    have h1 := abs_im_le_norm (w - (c + σ + I * y))
    have h2 := abs_im_le_norm (c - c₀)
    simp only [sub_im, add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, one_mul, zero_mul,
      add_zero, zero_add] at h1 h2
    replace h1 := h1.trans hw
    rw [abs_le] at h1 h2
    rw [abs_le]; constructor <;>
      linarith [h1.1, h1.2, h2.1, h2.2, le_abs_self y, neg_abs_le y, le_abs_self c₀.im,
        neg_abs_le c₀.im]
  have hwx : w.re ∈ Icc (-(|c₀.re + σ| + 2)) (|c₀.re + σ| + 2) := by
    rw [abs_le] at hre
    constructor <;> linarith [hre.1, hre.2, le_abs_self (c₀.re + σ), neg_abs_le (c₀.re + σ)]
  have hb := hC w.re hwx w.im
  rw [show ((w.re : ℂ) + I * w.im) = w by rw [mul_comm]; exact re_add_im w] at hb
  refine hb.trans ?_
  have h1 : (1 + |w.im|) ^ K ≤ (3 + |c₀.im|) ^ K * (1 + |y|) ^ K := by
    rw [← mul_pow]; gcongr; nlinarith [abs_nonneg y, abs_nonneg c₀.im]
  have h2 : Real.exp (π * |w.im| / 2) ≤
      Real.exp (π * (|c₀.im| + 2) / 2) * Real.exp (π * |y| / 2) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
  calc C * (1 + |w.im|) ^ K * Real.exp (π * |w.im| / 2)
      ≤ C * ((3 + |c₀.im|) ^ K * (1 + |y|) ^ K) *
          (Real.exp (π * (|c₀.im| + 2) / 2) * Real.exp (π * |y| / 2)) := by gcongr
    _ = _ := by ring

/-- **Integrals against `1/Γ` are entire in the parameter**: if `A` is continuous with
`|A(y)| ≤ C (1+|y|)^K e^{-π|y|}`, then `c ↦ ∫ A(y)/Γ(c+σ+iy) dy` is entire. -/
theorem differentiable_integral_mul_recip_Gamma {A : ℝ → ℂ} (hA : Continuous A) {C : ℝ} {K : ℕ}
    (hAb : ∀ y : ℝ, ‖A y‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(π * |y|))) (σ : ℝ) :
    Differentiable ℂ fun c : ℂ => ∫ y : ℝ, A y * (Gamma (c + σ + I * y))⁻¹ := by
  intro c₀
  obtain ⟨D, L, hD⟩ := exists_norm_recip_Gamma_disc_le c₀ σ
  set g : ℂ → ℂ := fun s => (Gamma s)⁻¹
  have hg : Differentiable ℂ g := differentiable_recip_Gamma
  set F : ℂ → ℝ → ℂ := fun c y => A y * g (c + σ + I * y) with hF
  set F' : ℂ → ℝ → ℂ := fun c y => A y * deriv g (c + σ + I * y) with hF'
  set bound : ℝ → ℝ := fun y => C * D * ((1 + |y|) ^ (K + L) * Real.exp (-(π / 2 * |y|)))
  have hbound : Integrable bound :=
    (integrable_one_add_abs_pow_mul_exp_neg (by positivity) (K + L)).const_mul (C * D)
  have hC0 : 0 ≤ C := by have := (norm_nonneg _).trans (hAb 0); simpa using this
  -- the bound for `g` on the discs and for its derivative
  have hgb : ∀ c ∈ Metric.ball c₀ 1, ∀ y : ℝ,
      ‖g (c + σ + I * y)‖ ≤ D * (1 + |y|) ^ L * Real.exp (π * |y| / 2) := by
    intro c hc y
    exact hD c hc y _ (by simp)
  have hdb : ∀ c ∈ Metric.ball c₀ 1, ∀ y : ℝ,
      ‖deriv g (c + σ + I * y)‖ ≤ D * (1 + |y|) ^ L * Real.exp (π * |y| / 2) := by
    intro c hc y
    have h := norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hg.diffContOnCl
      (fun w hw => hD c hc y w (by rw [Metric.mem_sphere, dist_eq_norm] at hw; exact hw.le))
    simpa using h
  have hexp : ∀ y : ℝ, Real.exp (-(π * |y|)) * Real.exp (π * |y| / 2) =
      Real.exp (-(π / 2 * |y|)) := fun y => by rw [← Real.exp_add]; ring_nf
  have hmain : ∀ y : ℝ, ∀ z : ℂ, ‖z‖ ≤ D * (1 + |y|) ^ L * Real.exp (π * |y| / 2) →
      ‖A y * z‖ ≤ bound y := by
    intro y z hz
    rw [norm_mul]
    calc ‖A y‖ * ‖z‖ ≤ (C * (1 + |y|) ^ K * Real.exp (-(π * |y|))) *
          (D * (1 + |y|) ^ L * Real.exp (π * |y| / 2)) :=
          mul_le_mul (hAb y) hz (norm_nonneg _) (by positivity)
      _ = bound y := by simp only [bound]; rw [pow_add, ← hexp y]; ring
  have hc₀ : c₀ ∈ Metric.ball c₀ 1 := Metric.mem_ball_self one_pos
  have hcontg : ∀ c : ℂ, Continuous fun y : ℝ => g (c + σ + I * y) := fun c =>
    hg.continuous.comp (by fun_prop)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (bound := bound) (Metric.ball_mem_nhds c₀ one_pos)
    (Eventually.of_forall fun c => (hA.mul (hcontg c)).aestronglyMeasurable)
    (hbound.mono' (hA.mul (hcontg c₀)).aestronglyMeasurable
      (Eventually.of_forall fun y => hmain y _ (hgb c₀ hc₀ y)))
    (hA.aestronglyMeasurable.mul ((measurable_deriv g).comp
      (by fun_prop : Continuous fun y : ℝ => c₀ + σ + I * y).measurable).aestronglyMeasurable)
    (Eventually.of_forall fun y c hc => hmain y _ (hdb c hc y)) hbound
    (Eventually.of_forall fun y c hc => by
      have h := ((hg (c + σ + I * y)).hasDerivAt.comp c
        (((hasDerivAt_id c).add_const (σ : ℂ)).add_const (I * y))).const_mul (A y)
      simpa [F, F'] using h)
  exact key.2.differentiableAt

/-- `y ↦ Γ(σ+iy)` is integrable for `σ > 0`. -/
theorem integrable_Gamma_vertical {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun y : ℝ => Gamma (σ + y * I)) := by
  obtain ⟨C, K, hC⟩ := exists_norm_Gamma_shift_le hσ 0
  have hcont : Continuous fun y : ℝ => Gamma (σ + y * I) :=
    continuous_iff_continuousAt.mpr fun y =>
      (continuousAt_Gamma_of_re_pos (by simp [hσ])).comp (by fun_prop)
  refine ((integrable_one_add_abs_pow_mul_exp_neg (c := π / 2) (by positivity) K).const_mul
    C).mono' hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have h := hC y
  rw [show ((σ : ℝ) : ℂ) + I * (((0 : ℝ) : ℂ) + (y : ℂ)) = σ + y * I by push_cast; ring] at h
  refine h.trans (le_of_eq ?_)
  ring_nf

/-- **The Cahen–Mellin integral**: `e^{-u} = 1/(2π) ∫ Γ(σ+iy) u^{-σ-iy} dy` for `σ, u > 0`. -/
theorem exp_neg_eq_integral {σ : ℝ} (hσ : 0 < σ) {u : ℝ} (hu : 0 < u) :
    ((Real.exp (-u) : ℝ) : ℂ) =
      1 / (2 * π) * ∫ y : ℝ, Gamma (σ + y * I) * (u : ℂ) ^ (-((σ : ℂ) + y * I)) := by
  set f : ℝ → ℂ := fun t => ((Real.exp (-t) : ℝ) : ℂ) with hf
  have hmel : ∀ s : ℂ, 0 < s.re → mellin f s = Gamma s := by
    intro s hs
    rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hf, smul_eq_mul]; push_cast; ring
  have hconv : MellinConvergent f σ := by
    have h := Complex.GammaIntegral_convergent (s := (σ : ℂ)) (by simp [hσ])
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [hf, smul_eq_mul]; push_cast; ring
  have hvert : VerticalIntegrable (mellin f) σ :=
    (integrable_Gamma_vertical hσ).congr (Eventually.of_forall fun y =>
      (hmel _ (by simp [hσ])).symm)
  have hcont : ContinuousAt f u := by fun_prop
  have hinv := mellinInv_mellin_eq σ f hu hconv hvert hcont
  rw [mellinInv] at hinv
  have hm' : ∀ y : ℝ, mellin f (σ + y * I) = Gamma (σ + y * I) := fun y =>
    hmel _ (by simp [hσ])
  simp only [hm', smul_eq_mul] at hinv
  rw [show f u = ((Real.exp (-u) : ℝ) : ℂ) from rfl] at hinv
  rw [← hinv, Complex.real_smul]
  congr 1
  · push_cast; ring
  · congr 1; funext y; ring

/-- On a disc in the right half-plane, `|arg w|` stays below `π/2` uniformly. -/
theorem exists_abs_arg_le_of_ball {w₀ : ℂ} (hw₀ : 0 < w₀.re) :
    ∃ θ : ℝ, θ < π / 2 ∧ ∀ w ∈ Metric.ball w₀ (w₀.re / 2), |arg w| ≤ θ ∧
      w₀.re / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ ‖w₀‖ + w₀.re / 2 ∧ 0 < w.re := by
  set ρ₀ := w₀.re / 2 with hρ₀
  set R := ‖w₀‖ + ρ₀ with hR
  have hρ0 : 0 < ρ₀ := by positivity
  have hρR : ρ₀ ≤ R := by have := norm_nonneg w₀; linarith
  set κ := ρ₀ / R with hκ
  have hR0 : 0 < R := by linarith
  have hκ0 : 0 < κ := div_pos hρ0 hR0
  have hκ1 : κ ≤ 1 := (div_le_one hR0).mpr hρR
  refine ⟨Real.arccos κ, Real.arccos_lt_pi_div_two.mpr hκ0, fun w hw => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have hre : ρ₀ < w.re := by
    have := abs_re_le_norm (w - w₀); rw [sub_re, abs_le] at this
    linarith [this.1]
  have hwn : ‖w‖ ≤ R := by
    have := norm_sub_norm_le w w₀; linarith
  have hwre : w.re ≤ ‖w‖ := re_le_norm w
  have hw0 : w ≠ 0 := by rintro rfl; rw [zero_re] at hre; linarith
  refine ⟨?_, by linarith, hwn, by linarith⟩
  have hcos : κ ≤ Real.cos (arg w) := by
    rw [cos_arg hw0, hκ]
    have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    rw [div_le_div_iff₀ hR0 hn]; nlinarith
  by_contra hlt
  push Not at hlt
  have habs : |arg w| ≤ π := abs_le.mpr ⟨by linarith [neg_pi_lt_arg w], arg_le_pi w⟩
  have h1 := Real.cos_lt_cos_of_nonneg_of_le_pi (Real.arccos_nonneg κ) habs hlt
  rw [Real.cos_arccos (by linarith) hκ1, Real.cos_abs] at h1
  linarith

/-- On an annular sector `ρ₀ ≤ |w| ≤ R`, `|arg w| ≤ θ`, the power `w^(τ + iy)` is bounded by
`(ρ₀^τ + R^τ) e^(θ|y|)`. -/
private lemma norm_cpow_ofReal_add_I_mul_le {w : ℂ} {θ ρ₀ R : ℝ} (hρ0 : 0 < ρ₀)
    (harg : |arg w| ≤ θ) (h1 : ρ₀ ≤ ‖w‖) (h2 : ‖w‖ ≤ R) (hre : 0 < w.re) (τ y : ℝ) :
    ‖w ^ ((τ : ℂ) + I * y)‖ ≤ (ρ₀ ^ τ + R ^ τ) * Real.exp (θ * |y|) := by
  have hpow : ∀ r : ℝ, ρ₀ ≤ r → r ≤ R → r ^ τ ≤ ρ₀ ^ τ + R ^ τ := by
    intro r hr1 hr2
    have hr0 : 0 < r := by linarith
    rcases le_total 0 τ with hτ | hτ
    · have := Real.rpow_le_rpow hr0.le hr2 hτ
      linarith [Real.rpow_nonneg hρ0.le τ]
    · have := Real.rpow_le_rpow_of_nonpos hρ0 hr1 hτ
      linarith [Real.rpow_nonneg (show (0 : ℝ) ≤ R by linarith) τ]
  have hw0 : w ≠ 0 := by rintro rfl; simp at hre
  rw [norm_cpow_of_ne_zero hw0]
  simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, sub_zero, mul_zero,
    add_zero, add_im, mul_im, one_mul, zero_add]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  have hy : -(arg w * y) ≤ θ * |y| := by
    have h3 : |arg w * y| ≤ θ * |y| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right harg (abs_nonneg y)
    linarith [neg_abs_le (arg w * y)]
  exact mul_le_mul (hpow _ h1 h2) (Real.exp_le_exp.mpr hy) (Real.exp_pos _).le
    (add_nonneg (Real.rpow_nonneg hρ0.le τ) (Real.rpow_nonneg (by linarith) τ))

/-- **Integrals against `w^{σ+iy}` are holomorphic in the right half-plane**: if `B` is continuous
with `|B(y)| ≤ C (1+|y|)^K e^{-π|y|/2}`, then `w ↦ ∫ B(y) w^{σ+iy} dy` is holomorphic on
`re w > 0`. -/
theorem differentiableOn_integral_mul_cpow {B : ℝ → ℂ} (hB : Continuous B) {C : ℝ} {K : ℕ}
    (hBb : ∀ y : ℝ, ‖B y‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2)) (σ : ℝ) :
    DifferentiableOn ℂ (fun w : ℂ => ∫ y : ℝ, B y * w ^ ((σ : ℂ) + I * y)) {w | 0 < w.re} := by
  intro w₀ hw₀
  change 0 < w₀.re at hw₀
  obtain ⟨θ, hθ, hball⟩ := exists_abs_arg_le_of_ball hw₀
  set ρ₀ := w₀.re / 2
  set R := ‖w₀‖ + w₀.re / 2
  have hρ0 : 0 < ρ₀ := by positivity
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (by simpa using hBb 0)
  have hnorm : ∀ w ∈ Metric.ball w₀ (w₀.re / 2), ∀ τ : ℝ, ∀ y : ℝ,
      ‖w ^ ((τ : ℂ) + I * y)‖ ≤ (ρ₀ ^ τ + R ^ τ) * Real.exp (θ * |y|) := fun w hw τ y => by
    obtain ⟨harg, h1, h2, hre⟩ := hball w hw
    exact norm_cpow_ofReal_add_I_mul_le hρ0 harg h1 h2 hre τ y
  set c := π / 2 - θ with hc
  have hc0 : 0 < c := by linarith
  set F : ℂ → ℝ → ℂ := fun w y => B y * w ^ ((σ : ℂ) + I * y) with hF
  set F' : ℂ → ℝ → ℂ := fun w y => B y * (((σ : ℂ) + I * y) * w ^ ((σ : ℂ) + I * y - 1)) with hF'
  have hexp : ∀ y : ℝ, Real.exp (-(π * |y|) / 2) * Real.exp (θ * |y|) = Real.exp (-(c * |y|)) :=
    fun y => by rw [← Real.exp_add]; congr 1; rw [hc]; ring
  set bound : ℝ → ℝ := fun y => C * (1 + |σ|) * ((ρ₀ ^ (σ - 1) + R ^ (σ - 1)) + (ρ₀ ^ σ + R ^ σ)) *
    ((1 + |y|) ^ (K + 1) * Real.exp (-(c * |y|)))
  have hbound : Integrable bound :=
    (integrable_one_add_abs_pow_mul_exp_neg hc0 (K + 1)).const_mul _
  have hP : 0 ≤ ρ₀ ^ (σ - 1) + R ^ (σ - 1) := by
    have : (0 : ℝ) ≤ R := by positivity
    positivity
  have hP' : 0 ≤ ρ₀ ^ σ + R ^ σ := by
    have : (0 : ℝ) ≤ R := by positivity
    positivity
  have hw₀b : w₀ ∈ Metric.ball w₀ (w₀.re / 2) := Metric.mem_ball_self (by positivity)
  have hcontF : ∀ w ∈ Metric.ball w₀ (w₀.re / 2), Continuous (F w) := by
    intro w hw
    have hw0 : w ≠ 0 := by obtain ⟨-, -, -, hre⟩ := hball w hw; rintro rfl; simp at hre
    exact hB.mul (Continuous.const_cpow (by fun_prop) (Or.inl hw0))
  have hcontF' : Continuous (F' w₀) := by
    have hw0 : w₀ ≠ 0 := by rintro rfl; simp at hw₀
    exact hB.mul ((by fun_prop : Continuous fun y : ℝ => (σ : ℂ) + I * y).mul
      (Continuous.const_cpow (by fun_prop) (Or.inl hw0)))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (bound := bound) (Metric.ball_mem_nhds w₀ (by positivity : 0 < w₀.re / 2))
    (eventually_of_mem (Metric.ball_mem_nhds w₀ (by positivity : 0 < w₀.re / 2))
      fun w hw => (hcontF w hw).aestronglyMeasurable)
    (hbound.mono' (hcontF w₀ hw₀b).aestronglyMeasurable (Eventually.of_forall fun y => by
      simp only [hF, norm_mul]
      have h1 := hBb y
      have h2 := hnorm w₀ hw₀b σ y
      calc ‖B y‖ * ‖w₀ ^ ((σ : ℂ) + I * y)‖
          ≤ (C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2)) *
              ((ρ₀ ^ σ + R ^ σ) * Real.exp (θ * |y|)) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = C * (ρ₀ ^ σ + R ^ σ) * ((1 + |y|) ^ K * Real.exp (-(c * |y|))) := by
            rw [← hexp y]; ring
        _ ≤ bound y := by
            simp only [bound]
            have hy1 : (1 + |y|) ^ K ≤ (1 + |y|) ^ (K + 1) :=
              pow_le_pow_right₀ (by linarith [abs_nonneg y]) (Nat.le_succ K)
            have hs1 : (1 : ℝ) ≤ 1 + |σ| := by linarith [abs_nonneg σ]
            have he := Real.exp_pos (-(c * |y|))
            have hA : C * (ρ₀ ^ σ + R ^ σ) ≤
                C * (1 + |σ|) * ((ρ₀ ^ (σ - 1) + R ^ (σ - 1)) + (ρ₀ ^ σ + R ^ σ)) := by
              have h3 : ρ₀ ^ σ + R ^ σ ≤
                  (1 + |σ|) * ((ρ₀ ^ (σ - 1) + R ^ (σ - 1)) + (ρ₀ ^ σ + R ^ σ)) := by
                nlinarith [abs_nonneg σ]
              have := mul_le_mul_of_nonneg_left h3 hC0
              linarith
            exact mul_le_mul hA (mul_le_mul_of_nonneg_right hy1 he.le) (by positivity)
              (by positivity)))
    hcontF'.aestronglyMeasurable
    (Eventually.of_forall fun y w hw => by
      simp only [hF', norm_mul]
      have h1 := hBb y
      have h2 := hnorm w hw (σ - 1) y
      have hs : ‖(σ : ℂ) + I * y‖ ≤ (1 + |σ|) * (1 + |y|) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_real, norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        nlinarith [abs_nonneg σ, abs_nonneg y]
      rw [show (σ : ℂ) + I * y - 1 = ((σ - 1 : ℝ) : ℂ) + I * y by push_cast; ring]
      calc ‖B y‖ * (‖(σ : ℂ) + I * y‖ * ‖w ^ (((σ - 1 : ℝ) : ℂ) + I * y)‖)
          ≤ (C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2)) *
              (((1 + |σ|) * (1 + |y|)) *
                ((ρ₀ ^ (σ - 1) + R ^ (σ - 1)) * Real.exp (θ * |y|))) := by
            gcongr
        _ = C * (1 + |σ|) * (ρ₀ ^ (σ - 1) + R ^ (σ - 1)) *
              ((1 + |y|) ^ (K + 1) * Real.exp (-(c * |y|))) := by
            rw [← hexp y, pow_succ]; ring
        _ ≤ bound y := by
            simp only [bound]
            have he := Real.exp_pos (-(c * |y|))
            have hy : 0 ≤ (1 + |y|) ^ (K + 1) := by positivity
            have hs1 : (0 : ℝ) ≤ 1 + |σ| := by positivity
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right hP') (by positivity)) (by positivity))
    hbound
    (Eventually.of_forall fun y w hw => by
      obtain ⟨-, -, -, hre⟩ := hball w hw
      have hslit : w ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hre)
      have h := ((hasDerivAt_id w).cpow_const (c := (σ : ℂ) + I * y) hslit).const_mul (B y)
      simpa [hF, hF'] using h)
  exact key.2.differentiableAt.differentiableWithinAt

/-- A bound `C (1+|y|)^K e^{π|y|/2}` for `1/Γ(x + i(β+y))`. -/
theorem exists_norm_recip_Gamma_shift_le (x β : ℝ) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ y : ℝ,
      ‖(Gamma (x + I * (β + y)))⁻¹‖ ≤ C * (1 + |y|) ^ K * Real.exp (π * |y| / 2) := by
  obtain ⟨C, K, hC⟩ := exists_norm_recip_Gamma_le |x|
  have hx : x ∈ Set.Icc (-|x|) |x| := ⟨neg_abs_le x, le_abs_self x⟩
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC x hx 0); simpa using this
  refine ⟨C * (1 + |β|) ^ K * Real.exp (π * |β| / 2), K, fun y => ?_⟩
  have h := hC x hx (β + y)
  push_cast at h
  refine h.trans ?_
  have h1 : (1 + |β + y|) ^ K ≤ (1 + |β|) ^ K * (1 + |y|) ^ K := by
    rw [← mul_pow]; gcongr; nlinarith [abs_add_le β y, abs_nonneg β, abs_nonneg y]
  have h2 : Real.exp (π * |β + y| / 2) ≤ Real.exp (π * |β| / 2) * Real.exp (π * |y| / 2) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, abs_add_le β y]
  calc C * (1 + |β + y|) ^ K * Real.exp (π * |β + y| / 2)
      ≤ C * ((1 + |β|) ^ K * (1 + |y|) ^ K) *
          (Real.exp (π * |β| / 2) * Real.exp (π * |y| / 2)) := by gcongr
    _ = _ := by ring

end DLMF.Gamma
