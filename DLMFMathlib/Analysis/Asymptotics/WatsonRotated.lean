/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Asymptotics.WatsonSector
public import DLMFMathlib.Analysis.Complex.RotateRay

/-!
# Watson's lemma along rotated rays

Watson's lemma (`hasAsymptoticExpansion_integral_cexp_smul_sector`) gives the expansion of a
Laplace transform `f(z) = ∫₀^∞ e^{-zt} F(t) dt` in closed subsectors of `|arg z| < π/2`. When `F`
extends holomorphically to a sector `|arg t| ≤ α` with at most polynomial growth, rotating the
ray of integration to `arg t = θ`, `|θ| ≤ α`, gives

`f(z) = e^{iθ} ∫₀^∞ e^{-z e^{iθ} r} F(r e^{iθ}) dr`,

which continues `f` to the half-plane `re (z e^{iθ}) > 0`; Watson's lemma for the rotated
integral then gives the same Poincaré expansion uniformly in closed subsectors of
`|arg z + θ| < π/2`. Taking `θ = ±β` covers closed subsectors of `|arg z| < π/2 + α`
(Temme, *Special Functions*, §2.2; Olver, *Asymptotics and Special Functions*, §4.5).

## Main results

* `differentiableOn_integral_cexp_neg_mul_smul`: a Laplace transform is holomorphic on its
  half-plane of absolute convergence.
* `integral_cexp_neg_mul_mul_eq_rotate`: rotation of the ray in a Laplace integral, for a
  kernel holomorphic in the sector swept, with an integrable singularity at `0` and
  polynomial growth at `∞`.
* `hasAsymptoticExpansion_integral_cexp_smul_rotate`: Watson's lemma along a rotated ray, in
  the rotated variable `w = z e^{iθ}`, for `-π < θ ≤ π`.
* `hasAsymptoticExpansion_integral_cexp_smul_rotate_comap`: the same in the original variable
  `z`, uniformly for `δ |z| ≤ re (z e^{iθ})`, for `|θ| < π/2`.
* `Asymptotics.HasAsymptoticExpansion.sup`, `.of_le_sup`: gluing expansions valid on
  overlapping sectors along functions that agree there (for instance by the identity theorem).
* `Asymptotics.le_sup_comap_rotate`: two rotated sectors cover a closed sector `|arg z| ≤ α`.
* `Asymptotics.HasAsymptoticExpansion.even`, `.odd`: passing to even or odd scale functions
  when the other coefficients vanish.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Finset Asymptotics Complex

open scoped Topology Interval Real

section Laplace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- `t e^{-δ t} ≤ 1/δ` for `δ > 0`. -/
theorem mul_exp_neg_mul_le_recip {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    t * Real.exp (-δ * t) ≤ δ⁻¹ := by
  have h1 := Real.add_one_le_exp (δ * t)
  have h2 : Real.exp (-δ * t) * Real.exp (δ * t) = 1 := by
    rw [← Real.exp_add]; simp
  have he := Real.exp_pos (-δ * t)
  rw [← one_div, le_div_iff₀ hδ]
  nlinarith

/-- **The Laplace transform is holomorphic** on the half-plane of absolute convergence: if
`e^{-ct} G(t)` is integrable on `(0, ∞)`, then `w ↦ ∫₀^∞ e^{-wt} G(t) dt` is complex
differentiable on `re w > c`. -/
theorem differentiableOn_integral_cexp_neg_mul_smul {G : ℝ → V} {c : ℝ}
    (hint : IntegrableOn (fun t => Real.exp (-c * t) • G t) (Ioi 0)) :
    DifferentiableOn ℂ (fun w : ℂ => ∫ t in Ioi (0 : ℝ), Complex.exp (-(w * t)) • G t)
      {w : ℂ | c < w.re} := by
  intro w₀ hw₀
  have hw₀' : c < w₀.re := hw₀
  set δ := (w₀.re - c) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hGm : AEStronglyMeasurable G (volume.restrict (Ioi 0)) := by
    have hc : AEStronglyMeasurable (fun t : ℝ => Real.exp (c * t)) (volume.restrict (Ioi 0)) :=
      (by fun_prop : Continuous fun t : ℝ => Real.exp (c * t)).aestronglyMeasurable
    refine (hc.smul hint.aestronglyMeasurable).congr (Eventually.of_forall fun t => ?_)
    show Real.exp (c * t) • (Real.exp (-c * t) • G t) = G t
    rw [smul_smul, ← Real.exp_add]
    simp
  have hball : Metric.ball w₀ δ ∈ 𝓝 w₀ := Metric.ball_mem_nhds _ hδ0
  have hre : ∀ w ∈ Metric.ball w₀ δ, c + δ < w.re := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have h1 := abs_re_le_norm (w - w₀)
    rw [sub_re] at h1
    have h2 := (abs_lt.mp (lt_of_le_of_lt h1 hw)).1
    linarith
  have hbint : Integrable (fun t : ℝ => δ⁻¹ * (Real.exp (-c * t) * ‖G t‖))
      (volume.restrict (Ioi 0)) := by
    refine Integrable.const_mul ?_ _
    refine IntegrableOn.congr_fun hint.norm (fun t _ => ?_) measurableSet_Ioi
    simp [norm_smul, Real.abs_exp]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0))
    (F := fun w (t : ℝ) => Complex.exp (-(w * t)) • G t)
    (F' := fun w (t : ℝ) => (Complex.exp (-(w * t)) * -(t : ℂ)) • G t)
    (bound := fun t : ℝ => δ⁻¹ * (Real.exp (-c * t) * ‖G t‖))
    hball (Eventually.of_forall fun w =>
      ((by fun_prop : Continuous fun t : ℝ => Complex.exp (-(w * t))).aestronglyMeasurable).smul
        hGm)
    (integrableOn_cexp_neg_mul_smul_of_le hint hw₀'.le)
    (((by fun_prop : Continuous fun t : ℝ => Complex.exp (-(w₀ * t)) * -(t : ℂ)
      ).aestronglyMeasurable).smul hGm) ?_ hbint ?_
  · exact h.2.differentiableAt.differentiableWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    have ht' : (0 : ℝ) < t := ht
    have hwre := hre w hw
    rw [norm_smul, norm_mul, norm_neg, Complex.norm_exp, Complex.norm_real,
      Real.norm_of_nonneg ht'.le]
    have hexp : Real.exp (-(w * t)).re ≤ Real.exp (-c * t) * Real.exp (-δ * t) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      nlinarith
    have hm := mul_exp_neg_mul_le_recip hδ0 t
    calc Real.exp (-(w * t)).re * t * ‖G t‖
        ≤ Real.exp (-c * t) * Real.exp (-δ * t) * t * ‖G t‖ := by gcongr
      _ = (t * Real.exp (-δ * t)) * (Real.exp (-c * t) * ‖G t‖) := by ring
      _ ≤ δ⁻¹ * (Real.exp (-c * t) * ‖G t‖) := by gcongr
  · filter_upwards with t w _
    have := ((hasDerivAt_id w).mul_const (t : ℂ)).neg.cexp
    simpa using this.smul_const (G t)

/-- A Laplace transform of a continuous function with `|G(t)| ≤ C t^k + D`, `k > -1`, on
`(0, ∞)` is holomorphic on the right half-plane. -/
theorem differentiableOn_integral_cexp_neg_mul_smul_of_le_rpow {G : ℝ → V} {C D k : ℝ}
    (hk : -1 < k) (hG : ContinuousOn G (Ioi 0)) (hb : ∀ r : ℝ, 0 < r → ‖G r‖ ≤ C * r ^ k + D) :
    DifferentiableOn ℂ (fun w : ℂ => ∫ t in Ioi (0 : ℝ), Complex.exp (-(w * t)) • G t)
      {w : ℂ | 0 < w.re} := by
  intro w hw
  have hw : 0 < w.re := hw
  have hint : IntegrableOn (fun t => Real.exp (-(w.re / 2) * t) • G t) (Ioi 0) := by
    have hmaj := ((integrableOn_exp_neg_mul_mul_rpow_sub_one (s := k + 1) (by linarith)
      (by positivity : 0 < w.re / 2)).const_mul C).add
      ((exp_neg_integrableOn_Ioi 0 (by positivity : 0 < w.re / 2)).const_mul D)
    refine hmaj.mono' (((by fun_prop : Continuous fun t : ℝ => Real.exp (-(w.re / 2) * t)
      ).continuousOn.smul hG).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_smul, Real.norm_eq_abs, Real.abs_exp, add_sub_cancel_right]
    calc Real.exp (-(w.re / 2) * t) * ‖G t‖ ≤ Real.exp (-(w.re / 2) * t) * (C * t ^ k + D) :=
          mul_le_mul_of_nonneg_left (hb t ht) (Real.exp_pos _).le
      _ = _ := by simp only [Pi.add_apply]; ring
  exact ((differentiableOn_integral_cexp_neg_mul_smul hint).differentiableAt
    ((isOpen_lt continuous_const continuous_re).mem_nhds
      (show w.re / 2 < w.re by linarith))).differentiableWithinAt

end Laplace

section Rotate

/-- A power is dominated by any decaying exponential on `[1, ∞)`. -/
theorem exists_rpow_mul_exp_neg_le' (k : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ K, 0 ≤ K ∧ ∀ r : ℝ, 1 ≤ r → r ^ k * Real.exp (-b * r) ≤ K := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero k b hb).eventually
    (eventually_le_nhds (zero_lt_one' ℝ))
  obtain ⟨R, hR⟩ := eventually_atTop.mp h
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := max R 1)).exists_bound_of_continuousOn
    (f := fun r : ℝ => r ^ k * Real.exp (-b * r)) (fun r hr => by
      have hr0 : (0 : ℝ) < r := by linarith [hr.1]
      exact ((Real.continuousAt_rpow_const _ _ (Or.inl hr0.ne')).mul
        (by fun_prop)).continuousWithinAt)
  refine ⟨max 1 M, by positivity, fun r hr => ?_⟩
  rcases le_or_gt r (max R 1) with h1 | h1
  · have := hM r ⟨hr, h1⟩
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_right _ _))
  · exact (hR r (le_of_lt ((le_max_left R 1).trans_lt h1))).trans (le_max_left _ _)

/-- **Rotation of the ray in a Laplace integral.** Let `F` be holomorphic at every point
`r e^{iy}`, `r > 0`, `y` between `0` and `θ`, with `|F(r e^{iy})| ≤ C r^{σ-1}` for `r ≤ 1`
(`σ > 0`) and `|F(r e^{iy})| ≤ C r^k` for `r ≥ 1`. If `re (z e^{iy}) > 0` for all `y` between
`0` and `θ`, then
`∫₀^∞ e^{-zt} F(t) dt = e^{iθ} ∫₀^∞ e^{-z e^{iθ} r} F(r e^{iθ}) dr`. -/
theorem integral_cexp_neg_mul_mul_eq_rotate {F : ℂ → ℂ} {θ σ C k : ℝ} {z : ℂ} (hσ : 0 < σ)
    (hd : ∀ r : ℝ, 0 < r → ∀ y ∈ [[0, θ]], DifferentiableAt ℂ F (r * exp (y * I)))
    (h0 : ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ y ∈ [[0, θ]], ‖F (r * exp (y * I))‖ ≤ C * r ^ (σ - 1))
    (hinf : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ [[0, θ]], ‖F (r * exp (y * I))‖ ≤ C * r ^ k)
    (hz : ∀ y ∈ [[0, θ]], 0 < (z * exp (y * I)).re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-(z * t)) * F t =
      exp (θ * I) * ∫ r in Ioi (0 : ℝ), Complex.exp (-(z * exp (θ * I) * r)) *
        F (r * exp (θ * I)) := by
  obtain ⟨y₀, hy₀, hmin⟩ := isCompact_uIcc.exists_isMinOn (nonempty_uIcc (a := (0 : ℝ)) (b := θ))
    (f := fun y : ℝ => (z * exp (y * I)).re) (by fun_prop)
  set κ := (z * exp (y₀ * I)).re with hκ
  have hκ0 : 0 < κ := hz y₀ hy₀
  have hκle : ∀ y ∈ [[0, θ]], κ ≤ (z * exp (y * I)).re := fun y hy => hmin hy
  obtain ⟨K, hK0, hK⟩ := exists_rpow_mul_exp_neg_le' k (half_pos hκ0)
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hinf 1 le_rfl 0 left_mem_uIcc)
    simpa using this
  have hnexp : ∀ r : ℝ, 0 < r → ∀ y ∈ [[0, θ]],
      ‖Complex.exp (-(z * ((r : ℂ) * exp (y * I))))‖ ≤ Real.exp (-κ * r) := by
    intro r hr y hy
    rw [Complex.norm_exp, Real.exp_le_exp]
    have : (-(z * ((r : ℂ) * exp (y * I)))).re = -(r * (z * exp (y * I)).re) := by
      rw [show z * ((r : ℂ) * exp (y * I)) = (r : ℂ) * (z * exp (y * I)) by ring, neg_re,
        re_ofReal_mul]
    rw [this]
    nlinarith [hκle y hy]
  have hrot := integral_Ioi_eq_exp_mul_integral_Ioi_rotate (f := fun t => Complex.exp (-(z * t)) *
    F t) (α := θ) (σ := σ) (κ := κ / 2) (C := C + C * K) hσ (half_pos hκ0)
    (fun r hr y hy => (by fun_prop : Differentiable ℂ fun t => Complex.exp (-(z * t))
      ).differentiableAt.mul (hd r hr y hy))
    (fun r hr hr1 y hy => by
      rw [norm_mul]
      have h1 := hnexp r hr y hy
      have h2 : Real.exp (-κ * r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have h3 := h0 r hr hr1 y hy
      calc ‖Complex.exp (-(z * ((r : ℂ) * exp (y * I))))‖ * ‖F (r * exp (y * I))‖
          ≤ 1 * (C * r ^ (σ - 1)) := by gcongr; exact h1.trans h2
        _ ≤ (C + C * K) * r ^ (σ - 1) := by
          rw [one_mul]; gcongr; nlinarith [mul_nonneg hC hK0])
    (fun r hr y hy => by
      rw [norm_mul]
      have hr0 : (0 : ℝ) < r := by linarith
      have h1 := hnexp r hr0 y hy
      have h3 := hinf r hr y hy
      have hk := hK r hr
      have hsplit : Real.exp (-κ * r) = Real.exp (-(κ / 2) * r) * Real.exp (-(κ / 2) * r) := by
        rw [← Real.exp_add]; ring_nf
      calc ‖Complex.exp (-(z * ((r : ℂ) * exp (y * I))))‖ * ‖F (r * exp (y * I))‖
          ≤ Real.exp (-κ * r) * (C * r ^ k) := by gcongr
        _ = C * (r ^ k * Real.exp (-(κ / 2) * r)) * Real.exp (-(κ / 2) * r) := by
          rw [hsplit]; ring
        _ ≤ C * K * Real.exp (-(κ / 2) * r) := by gcongr
        _ ≤ (C + C * K) * Real.exp (-(κ / 2) * r) := by gcongr; linarith)
  rw [hrot]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  ring_nf

end Rotate

namespace Complex

/-- `re (z e^{iy}) = |z| cos(arg z + y)`. -/
theorem re_mul_exp_ofReal_mul_I (z : ℂ) (y : ℝ) :
    (z * exp (y * I)).re = ‖z‖ * Real.cos (arg z + y) := by
  conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
  rw [mul_assoc, ← exp_add, show (arg z : ℂ) * I + y * I = ((arg z + y : ℝ) : ℂ) * I by
    push_cast; ring, re_ofReal_mul, exp_ofReal_mul_I_re]

/-- `(z e^{iθ})^w = z^w e^{iθw}` when `arg z + θ ∈ (-π, π]`. -/
theorem cpow_mul_exp_ofReal_mul_I {z : ℂ} (hz : z ≠ 0) {θ : ℝ} (h1 : -π < arg z + θ)
    (h2 : arg z + θ ≤ π) (w : ℂ) :
    (z * exp (θ * I)) ^ w = z ^ w * exp (θ * I * w) := by
  have hlog : log (z * exp (θ * I)) = log z + θ * I := by
    have : z * exp (θ * I) = exp (log z + θ * I) := by rw [exp_add, exp_log hz]
    rw [this, log_exp] <;> simp [log_im] <;> linarith
  rw [cpow_def_of_ne_zero (mul_ne_zero hz (exp_ne_zero _)), hlog, cpow_def_of_ne_zero hz,
    ← exp_add]
  ring_nf

/-- `(r e^{iθ})^w = r^w e^{iθw}` for `r > 0` and `θ ∈ (-π, π]`. -/
theorem ofReal_mul_exp_cpow {r : ℝ} (hr : 0 < r) {θ : ℝ} (h1 : -π < θ) (h2 : θ ≤ π) (w : ℂ) :
    ((r : ℂ) * exp (θ * I)) ^ w = (r : ℂ) ^ w * exp (θ * I * w) :=
  cpow_mul_exp_ofReal_mul_I (ofReal_ne_zero.mpr hr.ne')
    (by rw [arg_ofReal_of_nonneg hr.le, zero_add]; exact h1)
    (by rw [arg_ofReal_of_nonneg hr.le, zero_add]; exact h2) w

/-- An angle in `(-3π/2, 3π/2)` with positive cosine lies in `(-π/2, π/2)`. -/
theorem abs_lt_pi_div_two_of_cos_pos' {u : ℝ} (h1 : -(3 * Real.pi / 2) < u)
    (h2 : u < 3 * Real.pi / 2) (hc : 0 < Real.cos u) : |u| < Real.pi / 2 := by
  rw [abs_lt]
  constructor
  · by_contra h
    push Not at h
    have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := -u) (by linarith) (by linarith)
    rw [Real.cos_neg] at this; linarith
  · by_contra h
    push Not at h
    have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := u) h (by linarith)
    linarith

/-- If `re (z e^{iθ}) > 0` with `|θ| < π/2`, then `|arg z + θ| < π/2`. -/
theorem abs_arg_add_lt_of_re_mul_exp_pos {z : ℂ} {θ : ℝ} (hθ : |θ| < Real.pi / 2)
    (h : 0 < (z * exp (θ * I)).re) : |arg z + θ| < Real.pi / 2 := by
  rw [re_mul_exp_ofReal_mul_I] at h
  have hc : 0 < Real.cos (arg z + θ) := by
    by_contra hc; push Not at hc; nlinarith [norm_nonneg z]
  have h1 := Complex.neg_pi_lt_arg z
  have h2 := Complex.arg_le_pi z
  exact abs_lt_pi_div_two_of_cos_pos' (by linarith [neg_abs_le θ]) (by linarith [le_abs_self θ]) hc

/-- If `re z > 0` and `re (z e^{iθ}) > 0` with `|θ| < π/2`, then `re (z e^{iy}) > 0` for every
`y` between `0` and `θ`. -/
theorem re_mul_exp_pos_of_mem_uIcc {z : ℂ} {θ y : ℝ} (hθ : |θ| < π / 2) (hz : 0 < z.re)
    (hzθ : 0 < (z * exp (θ * I)).re) (hy : y ∈ [[0, θ]]) : 0 < (z * exp (y * I)).re := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have h0 : |arg z| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have h1 := abs_arg_add_lt_of_re_mul_exp_pos hθ hzθ
  have h2 : |arg z + y| < π / 2 := by
    rcases le_total 0 θ with h | h
    · rw [uIcc_of_le h] at hy
      rw [abs_lt] at h0 h1 ⊢; constructor <;> linarith [hy.1, hy.2]
    · rw [uIcc_of_ge h] at hy
      rw [abs_lt] at h0 h1 ⊢; constructor <;> linarith [hy.1, hy.2]
  rw [re_mul_exp_ofReal_mul_I]
  refine mul_pos (norm_pos_iff.mpr hz0) ?_
  rw [← Real.cos_abs]
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg (arg z + y), Real.pi_pos], h2⟩

/-- `(r e^{iy})² = r² e^{2iy}`. -/
theorem ofReal_mul_exp_ofReal_mul_I_sq (r y : ℝ) :
    ((r : ℂ) * exp (y * I)) ^ 2 = ((r ^ 2 : ℝ) : ℂ) * exp (((2 * y : ℝ) : ℂ) * I) := by
  rw [mul_pow, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- `|sin u| ≤ |1 + s e^{iu}|` for real `s`. -/
theorem abs_sin_le_norm_one_add_ofReal_mul_exp (s u : ℝ) :
    |Real.sin u| ≤ ‖1 + (s : ℂ) * exp (u * I)‖ := by
  have hsq : ‖1 + (s : ℂ) * exp (u * I)‖ ^ 2 =
      (1 + s * Real.cos u) ^ 2 + (s * Real.sin u) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [add_re, one_re, re_ofReal_mul, exp_ofReal_mul_I_re, add_im, one_im,
      im_ofReal_mul, exp_ofReal_mul_I_im, zero_add]
    ring
  have h : Real.sin u ^ 2 ≤ ‖1 + (s : ℂ) * exp (u * I)‖ ^ 2 := by
    rw [hsq]; nlinarith [sq_nonneg (Real.cos u + s), Real.sin_sq_add_cos_sq u]
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h

/-- `1 ≤ |1 + s e^{iu}|` for `s ≥ 0` and `cos u ≥ 0`. -/
theorem one_le_norm_one_add_ofReal_mul_exp {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ Real.cos u) :
    1 ≤ ‖1 + (s : ℂ) * exp (u * I)‖ := by
  have h := Complex.re_le_norm (1 + (s : ℂ) * exp (u * I))
  simp only [add_re, one_re, re_ofReal_mul, exp_ofReal_mul_I_re] at h
  nlinarith [mul_nonneg hs hu]

/-- A uniform lower bound for `|1 + s e^{iu}|`, `s ≥ 0`, `|u| ≤ Φ < π`. -/
theorem exists_pos_le_norm_one_add_ofReal_mul_exp {Φ : ℝ} (hΦ : Φ < π) :
    ∃ c > 0, ∀ s : ℝ, 0 ≤ s → ∀ u : ℝ, |u| ≤ Φ → c ≤ ‖1 + (s : ℂ) * exp (u * I)‖ := by
  by_cases h : Φ ≤ π / 2
  · refine ⟨1, one_pos, fun s hs u hu => one_le_norm_one_add_ofReal_mul_exp hs ?_⟩
    rw [← Real.cos_abs]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg u, Real.pi_pos], by linarith⟩
  push Not at h
  have hsin : 0 < Real.sin Φ := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) hΦ
  refine ⟨Real.sin Φ, hsin, fun s hs u hu => ?_⟩
  by_cases hc : 0 ≤ Real.cos u
  · exact (Real.sin_le_one Φ).trans (one_le_norm_one_add_ofReal_mul_exp hs hc)
  push Not at hc
  have hu2 : π / 2 < |u| := by
    by_contra h2; push Not at h2
    rw [← Real.cos_abs] at hc
    linarith [Real.cos_nonneg_of_mem_Icc (x := |u|) ⟨by linarith [abs_nonneg u, Real.pi_pos], h2⟩]
  refine le_trans ?_ (abs_sin_le_norm_one_add_ofReal_mul_exp s u)
  have habs : Real.sin |u| ≤ |Real.sin u| := by
    rcases le_total 0 u with h0 | h0
    · rw [abs_of_nonneg h0]; exact le_abs_self _
    · rw [abs_of_nonpos h0, Real.sin_neg]; exact neg_le_abs _
  refine le_trans ?_ habs
  rw [← Real.sin_pi_sub, ← Real.sin_pi_sub |u|]
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

end Complex

/-- Points between `0` and `θ` have modulus at most `|θ|`. -/
theorem abs_le_abs_of_mem_uIcc_zero {θ y : ℝ} (hy : y ∈ [[0, θ]]) : |y| ≤ |θ| := by
  rcases le_total 0 θ with h | h
  · rw [uIcc_of_le h] at hy
    rw [abs_of_nonneg hy.1, abs_of_nonneg h]; exact hy.2
  · rw [uIcc_of_ge h] at hy
    rw [abs_of_nonpos hy.2, abs_of_nonpos h]; linarith [hy.1]

section Watson

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- **Watson's lemma along a rotated ray**, in the rotated variable `w = z e^{iθ}`. Let
`F(r e^{iθ}) - ∑_{n<N} (r e^{iθ})^{n+μ-1} aₙ = O(r^{N + re μ - 1})` as `r → 0⁺` for every `N`,
with `re μ > 0`, `-π < θ ≤ π`, and let `e^{-cr} F(r e^{iθ})` be integrable on `(0, ∞)`. Then
`e^{iθ} ∫₀^∞ e^{-wr} F(r e^{iθ}) dr ~ ∑ Γ(n+μ) e^{iθ(n+μ)} aₙ w^{-(n+μ)}` as `w → ∞` with
`δ |w| ≤ re w`. -/
theorem hasAsymptoticExpansion_integral_cexp_smul_rotate {F : ℂ → V} {a : ℕ → V} {μ : ℂ}
    {c δ θ : ℝ} (hθ1 : -Real.pi < θ) (hθ2 : θ ≤ Real.pi) (hμ : 0 < μ.re) (hδ : 0 < δ)
    (hint : IntegrableOn (fun r : ℝ => Real.exp (-c * r) • F (r * exp (θ * I))) (Ioi 0))
    (hF : ∀ N : ℕ, (fun r : ℝ => F (r * exp (θ * I)) -
        ∑ n ∈ range N, (((r : ℂ) * exp (θ * I)) ^ ((n : ℂ) + μ - 1)) • a n)
      =O[𝓝[>] 0] fun r => r ^ ((N : ℝ) + μ.re - 1)) :
    HasAsymptoticExpansion (sectorAtTop δ) (fun (n : ℕ) (w : ℂ) => w ^ (-((n : ℂ) + μ)))
      (fun n => Complex.Gamma ((n : ℂ) + μ) • exp (θ * I * ((n : ℂ) + μ)) • a n)
      (fun w => exp (θ * I) • ∫ r in Ioi (0 : ℝ), Complex.exp (-(w * r)) •
        F (r * exp (θ * I))) := by
  have hint' : IntegrableOn (fun r : ℝ => Real.exp (-c * r) • (exp (θ * I) • F (r * exp (θ * I))))
      (Ioi 0) := by
    refine IntegrableOn.congr_fun (hint.smul (exp (θ * I))) (fun r _ => ?_) measurableSet_Ioi
    simp only [Pi.smul_apply]
    rw [smul_comm]
  have hG : ∀ N : ℕ, (fun r : ℝ => exp (θ * I) • F (r * exp (θ * I)) - ∑ n ∈ range N,
      ((r : ℂ) ^ ((n : ℂ) + μ - 1)) • (exp (θ * I * ((n : ℂ) + μ)) • a n))
      =O[𝓝[>] 0] fun r => r ^ ((N : ℝ) + μ.re - 1) := by
    intro N
    refine ((hF N).const_smul_left (exp (θ * I))).congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : (0 : ℝ) < r := hr
    simp only [Pi.smul_apply]
    rw [smul_sub, Finset.smul_sum]
    congr 1
    refine sum_congr rfl fun n _ => ?_
    rw [Complex.ofReal_mul_exp_cpow hr hθ1 hθ2, smul_smul, smul_smul, mul_comm, mul_assoc,
      ← Complex.exp_add]
    congr 2
    ring_nf
  refine (hasAsymptoticExpansion_integral_cexp_smul_sector hμ hδ hint' hG).congr'
    (Eventually.of_forall fun w => ?_)
  show _ = exp (θ * I) • _
  rw [← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  rw [smul_comm]

/-- **Watson's lemma along a rotated ray**, in the original variable: for `|θ| < π/2` the
rotated Laplace integral `e^{iθ} ∫₀^∞ e^{-z e^{iθ} r} F(r e^{iθ}) dr` has the expansion
`∑ Γ(n+μ) aₙ z^{-(n+μ)}` as `z → ∞` with `δ |z e^{iθ}| ≤ re (z e^{iθ})`, that is, uniformly in
the closed sector `|arg z + θ| ≤ arccos δ`. Taking `θ` and `-θ` covers `|arg z| ≤ π/2 + θ - ε`
(`le_sup_comap_rotate`), so that, when the rotated integral continues `f`, Watson's expansion
of `f` extends beyond the right half-plane. -/
theorem hasAsymptoticExpansion_integral_cexp_smul_rotate_comap {F : ℂ → V} {a : ℕ → V}
    {μ : ℂ} {c δ θ : ℝ} (hθ : |θ| < Real.pi / 2) (hμ : 0 < μ.re) (hδ : 0 < δ)
    (hint : IntegrableOn (fun r : ℝ => Real.exp (-c * r) • F (r * exp (θ * I))) (Ioi 0))
    (hF : ∀ N : ℕ, (fun r : ℝ => F (r * exp (θ * I)) -
        ∑ n ∈ range N, (((r : ℂ) * exp (θ * I)) ^ ((n : ℂ) + μ - 1)) • a n)
      =O[𝓝[>] 0] fun r => r ^ ((N : ℝ) + μ.re - 1)) :
    HasAsymptoticExpansion (comap (fun z : ℂ => z * exp (θ * I)) (sectorAtTop δ))
      (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + μ)))
      (fun n => Complex.Gamma ((n : ℂ) + μ) • a n)
      (fun z => exp (θ * I) • ∫ r in Ioi (0 : ℝ), Complex.exp (-(z * exp (θ * I) * r)) •
        F (r * exp (θ * I))) := by
  have hθ1 : -Real.pi < θ := by linarith [neg_abs_le θ, Real.pi_pos]
  have hθ2 : θ ≤ Real.pi := by linarith [le_abs_self θ, Real.pi_pos]
  have hW := (hasAsymptoticExpansion_integral_cexp_smul_rotate hθ1 hθ2 hμ hδ hint hF).comp_tendsto
    (tendsto_comap : Tendsto (fun z : ℂ => z * exp (θ * I))
      (comap (fun z : ℂ => z * exp (θ * I)) (sectorAtTop δ)) (sectorAtTop δ))
  have hev : ∀ᶠ z in comap (fun z : ℂ => z * exp (θ * I)) (sectorAtTop δ),
      z ≠ 0 ∧ |arg z + θ| < Real.pi / 2 := by
    have h := (tendsto_comap : Tendsto (fun z : ℂ => z * exp (θ * I))
      (comap (fun z : ℂ => z * exp (θ * I)) (sectorAtTop δ)) (sectorAtTop δ)).eventually
      (eventually_sectorAtTop (R := 1) (p := fun w : ℂ => 0 < w.re) fun w hw hws => by
        nlinarith)
    filter_upwards [h] with z hz
    refine ⟨fun h0 => by simp [h0] at hz, Complex.abs_arg_add_lt_of_re_mul_exp_pos hθ hz⟩
  refine ((hW.smul_scale (κ := fun n => exp (θ * I * (-((n : ℂ) + μ))))
    (ψ := fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + μ))) fun n => ?_)).congr_coeff ?_
  · filter_upwards [hev] with z hz
    rw [Complex.cpow_mul_exp_ofReal_mul_I hz.1 (by linarith [(abs_lt.mp hz.2).1, Real.pi_pos])
      (by linarith [(abs_lt.mp hz.2).2, Real.pi_pos])]
    ring
  · funext n
    rw [smul_smul, smul_smul]
    congr 1
    rw [mul_right_comm, ← Complex.exp_add, show (θ : ℂ) * I * -((n : ℂ) + μ) +
      θ * I * ((n : ℂ) + μ) = 0 by ring, Complex.exp_zero, one_mul]

end Watson

namespace Asymptotics

namespace HasAsymptoticExpansion

variable {α 𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {l l₁ l₂ : Filter α} {φ : ℕ → α → 𝕜} {a : ℕ → E} {f f₁ f₂ : α → E}

/-- Expansions restrict to smaller filters. -/
theorem mono (hf : HasAsymptoticExpansion l₁ φ a f) (hl : l₂ ≤ l₁) :
    HasAsymptoticExpansion l₂ φ a f := fun N => (hf N).mono hl

/-- **Gluing**: an expansion valid along `l₁` and along `l₂` is valid along `l₁ ⊔ l₂`. -/
theorem sup (h₁ : HasAsymptoticExpansion l₁ φ a f) (h₂ : HasAsymptoticExpansion l₂ φ a f) :
    HasAsymptoticExpansion (l₁ ⊔ l₂) φ a f := fun N => (h₁ N).sup (h₂ N)

/-- **Gluing along analytic continuations**: if `f` agrees eventually with `f₁` along `l₁` and
with `f₂` along `l₂` (typically two integral representations, valid on overlapping sectors,
that continue `f` analytically), and `f₁`, `f₂` have the same expansion along `l₁`, `l₂`,
then `f` has that expansion along every filter `l ≤ l₁ ⊔ l₂`. -/
theorem of_le_sup (h₁ : HasAsymptoticExpansion l₁ φ a f₁) (h₂ : HasAsymptoticExpansion l₂ φ a f₂)
    (hf₁ : f₁ =ᶠ[l₁] f) (hf₂ : f₂ =ᶠ[l₂] f) (hl : l ≤ l₁ ⊔ l₂) :
    HasAsymptoticExpansion l φ a f :=
  ((h₁.congr' hf₁).sup (h₂.congr' hf₂)).mono hl

/-- An expansion with vanishing odd coefficients is an expansion in the even scale functions. -/
theorem even (hf : HasAsymptoticExpansion l φ a f) (ha : ∀ n, a (2 * n + 1) = 0) :
    HasAsymptoticExpansion l (fun n => φ (2 * n)) (fun n => a (2 * n)) f := by
  have hs : ∀ (N : ℕ) (x : α), ∑ m ∈ range (2 * N), φ m x • a m =
      ∑ n ∈ range N, φ (2 * n) x • a (2 * n) := by
    intro N x
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, ha,
        smul_zero, add_zero, sum_range_succ]
  intro N
  exact (hf (2 * N)).congr_left fun x => by rw [hs]

/-- An expansion with vanishing even coefficients is an expansion in the odd scale functions. -/
theorem odd (hf : HasAsymptoticExpansion l φ a f) (ha : ∀ n, a (2 * n) = 0) :
    HasAsymptoticExpansion l (fun n => φ (2 * n + 1)) (fun n => a (2 * n + 1)) f := by
  have hs : ∀ (N : ℕ) (x : α), ∑ m ∈ range (2 * N + 1), φ m x • a m =
      ∑ n ∈ range N, φ (2 * n + 1) x • a (2 * n + 1) := by
    intro N x
    induction N with
    | zero => simp [ha 0]
    | succ N ih =>
      rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
        show 2 * N + 1 + 1 = 2 * (N + 1) by ring, ha, smul_zero, add_zero, sum_range_succ]
  intro N
  exact (hf (2 * N + 1)).congr_left fun x => by rw [hs]

end HasAsymptoticExpansion

/-- **Two rotated sectors cover a sector.** If `0 ≤ β ≤ γ`, `α - β ≤ γ` and `γ < π/2`, the
closed sector `|arg z| ≤ α` at infinity is covered by the rotated sectors
`|arg (z e^{∓iβ})| ≤ γ`, described as `cos γ |w| ≤ re w` with `w = z e^{∓iβ}`. -/
theorem le_sup_comap_rotate {α β γ : ℝ} (hβ : 0 ≤ β) (hβγ : β ≤ γ) (hαβ : α - β ≤ γ)
    (hγ : γ < Real.pi / 2) :
    comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z : ℂ | z ≠ 0 ∧ |Complex.arg z| ≤ α} ≤
      comap (fun z : ℂ => z * Complex.exp (((-β : ℝ) : ℂ) * Complex.I))
          (sectorAtTop (Real.cos γ)) ⊔
        comap (fun z : ℂ => z * Complex.exp ((β : ℂ) * Complex.I)) (sectorAtTop (Real.cos γ)) := by
  set A : Set ℂ := {z : ℂ | z ≠ 0 ∧ |Complex.arg z| ≤ α}
  have hsplit : A ⊆ {z | 0 ≤ Complex.arg z ∧ z ∈ A} ∪ {z | Complex.arg z ≤ 0 ∧ z ∈ A} := by
    intro z hz
    rcases le_total 0 (Complex.arg z) with h | h
    · exact Or.inl ⟨h, hz⟩
    · exact Or.inr ⟨h, hz⟩
  have hγpi : γ ≤ Real.pi := by linarith [Real.pi_pos]
  have key : ∀ y : ℝ, ∀ z : ℂ, z ≠ 0 → |Complex.arg z + y| ≤ γ →
      Real.cos γ * ‖z * Complex.exp (y * Complex.I)‖ ≤ (z * Complex.exp (y * Complex.I)).re := by
    intro y z _ hy
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.re_mul_exp_ofReal_mul_I,
      mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [← Real.cos_abs (Complex.arg z + y)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hγpi hy
  have hnorm : ∀ y : ℝ, ∀ z : ℂ, ‖z * Complex.exp (y * Complex.I)‖ = ‖z‖ := fun y z => by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have htend : ∀ (y : ℝ) (S : Set ℂ), (∀ z ∈ S, z ≠ 0 ∧ |Complex.arg z + y| ≤ γ) →
      comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 S ≤
        comap (fun z : ℂ => z * Complex.exp (y * Complex.I)) (sectorAtTop (Real.cos γ)) := by
    intro y S hS
    rw [← map_le_iff_le_comap, sectorAtTop, le_inf_iff]
    constructor
    · rw [map_le_iff_le_comap, comap_comap]
      refine inf_le_left.trans (le_of_eq ?_)
      congr 1
      funext z
      exact (hnorm y z).symm
    · rw [map_le_iff_le_comap, comap_principal]
      refine inf_le_right.trans (principal_mono.mpr fun z hz => ?_)
      exact key y z (hS z hz).1 (hS z hz).2
  calc comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 A
      ≤ comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 ({z | 0 ≤ Complex.arg z ∧ z ∈ A} ∪
          {z | Complex.arg z ≤ 0 ∧ z ∈ A}) := inf_le_inf_left _ (principal_mono.mpr hsplit)
    _ = comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z | 0 ≤ Complex.arg z ∧ z ∈ A} ⊔
          comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z | Complex.arg z ≤ 0 ∧ z ∈ A} := by
        rw [← sup_principal, inf_sup_left]
    _ ≤ _ := by
        refine sup_le_sup (htend _ _ fun z hz => ⟨hz.2.1, ?_⟩) (htend _ _ fun z hz => ⟨hz.2.1, ?_⟩)
        · have := (abs_le.mp hz.2.2).2
          rw [abs_le]; constructor <;> linarith [hz.1]
        · have := (abs_le.mp hz.2.2).1
          rw [abs_le]; constructor <;> linarith [hz.1]

end Asymptotics
