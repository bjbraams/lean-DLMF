/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.BarnesResidue
public import DLMFMathlib.Analysis.Complex.LaurentAnnulus
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy

/-!
# Shifting a vertical line of integration across isolated singularities

Let `f` be holomorphic on the closed strip `c₁ ≤ ℜz ≤ c₂` except at finitely many points of the
open strip, where it may have arbitrary isolated singularities (poles or essential singularities).
If `f` is integrable on both boundary lines and its integrals over horizontal cross-sections of
the strip tend to `0` at `±i∞`, then for every small `r > 0`
`i (∫ f(c₂ + iy) dy - ∫ f(c₁ + iy) dy) = ∑ₚ ∮_{|z - p| = r} f(z) dz`.

The proof subtracts from `2πi f` the principal parts `-∮_{C(p,r)} f(w)/(w - z) dw` (made
integrable along vertical lines by a rational correction with its pole outside the strip). By the
Cauchy integral formula on an annulus the difference extends holomorphically to the closed strip,
and the pole-free shift `Complex.BarnesResidue.vertical_shift_of_differentiableOn` applies to it.
The principal parts are `A/(z - p) + O(‖z - p‖⁻²)` with `A = ∮_{C(p,r)} f`; the
`O(‖z - p‖⁻²)` remainders have vanishing line integrals (shift the line to `±∞`) and the simple
poles are handled by `Complex.BarnesResidue.vertical_shift`.

## Main results

* `Complex.integral_vertical_sub_eq_sum_circleIntegral`: the shift of a vertical line of
  integration across finitely many isolated singularities.
* `Complex.differentiableOn_circleIntegral_sub_inv_mul`: the Cauchy integral
  `z ↦ ∮_{C(c,r)} f(w)/(w - z) dw` is holomorphic off the circle.
* `Complex.norm_circleIntegral_sub_inv_mul_add_le`: the Cauchy integral minus its leading term
  `-A/(z - c)` at infinity is `O(‖z - c‖⁻²)`.
* `Complex.integral_vertical_eq_zero_of_norm_le`, `Complex.integral_vertical_eq_zero_of_norm_le'`:
  a function holomorphic and `O(‖z - p‖⁻²)` on a closed half-plane not containing `p` has
  vanishing integral along the boundary line.
-/

@[expose] public section

open Set Metric Filter MeasureTheory
open scoped Real Topology Interval

namespace Complex

/-- The Cauchy integral `z ↦ ∮_{C(c,r)} (w - z)⁻¹ f(w) dw` is holomorphic off the circle. -/
theorem differentiableOn_circleIntegral_sub_inv_mul {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ContinuousOn f (sphere c r)) :
    DifferentiableOn ℂ (fun z => ∮ w in C(c, r), (w - z)⁻¹ * f w) (sphere c r)ᶜ := by
  obtain ⟨M, hM⟩ := (isCompact_sphere c r).exists_bound_of_continuousOn hf
  have hfc : Continuous fun θ => f (circleMap c r θ) :=
    hf.comp_continuous (continuous_circleMap c r) fun θ => circleMap_mem_sphere c hr θ
  have hne : ∀ z ∈ (sphere c r)ᶜ, ∀ θ, circleMap c r θ - z ≠ 0 := fun z hz θ h =>
    hz (sub_eq_zero.mp h ▸ circleMap_mem_sphere c hr θ)
  unfold circleIntegral
  refine differentiableOn_intervalIntegral_of_locally_dominated isClosed_sphere.isOpen_compl
    0 (2 * π) (fun z hz => ?_) (Eventually.of_forall fun θ => ?_) (fun z hz => ?_)
  · refine (Continuous.aestronglyMeasurable ?_)
    simp only [deriv_circleMap]
    refine ((continuous_circleMap 0 r).mul continuous_const).smul (Continuous.mul ?_ hfc)
    exact ((continuous_circleMap c r).sub continuous_const).inv₀ (hne z hz)
  · intro z hz
    have : DifferentiableAt ℂ (fun x : ℂ => (circleMap c r θ - x)⁻¹ * f (circleMap c r θ)) z :=
      (((differentiableAt_const _).sub differentiableAt_id).inv (hne z hz θ)).mul_const _
    exact (this.const_smul (deriv (circleMap c r) θ)).differentiableWithinAt
  · set δ : ℝ := |‖z - c‖ - r| with hδ
    have hδ0 : 0 < δ := by
      rw [hδ, abs_pos, sub_ne_zero]
      intro h; exact hz (by rw [mem_sphere, dist_eq_norm, h])
    refine ⟨ball z (δ / 2), ball_mem_nhds z (by positivity), fun _ => r * (M * (2 / δ)),
      ?_, Eventually.of_forall fun θ y hy => ?_⟩
    · simp only [uIoc_of_le Real.two_pi_pos.le]
      exact integrableOn_const measure_Ioc_lt_top.ne
    · rw [norm_smul, deriv_circleMap, norm_mul, norm_mul,
        norm_circleMap_zero, norm_I, mul_one, abs_of_nonneg hr, norm_inv]
      refine mul_le_mul_of_nonneg_left ?_ hr
      have hw : ‖circleMap c r θ - c‖ = r := by
        rw [circleMap_sub_center, norm_circleMap_zero, abs_of_nonneg hr]
      have hy' : ‖y - z‖ < δ / 2 := by rwa [mem_ball, dist_eq_norm] at hy
      have hdist : δ / 2 ≤ ‖circleMap c r θ - y‖ := by
        have h1 : |‖z - c‖ - ‖y - c‖| ≤ ‖y - z‖ := by
          have := abs_norm_sub_norm_le (z - c) (y - c)
          rwa [show z - c - (y - c) = -(y - z) by ring, norm_neg] at this
        have h2 : |‖y - c‖ - r| ≤ ‖circleMap c r θ - y‖ := by
          have := abs_norm_sub_norm_le (y - c) (circleMap c r θ - c)
          rwa [hw, show y - c - (circleMap c r θ - c) = -(circleMap c r θ - y) by ring,
            norm_neg] at this
        have h3 : δ ≤ |‖y - c‖ - r| + |‖z - c‖ - ‖y - c‖| := by
          rw [hδ]
          calc |‖z - c‖ - r| = |(‖y - c‖ - r) + (‖z - c‖ - ‖y - c‖)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        linarith
      have hMθ := hM _ (circleMap_mem_sphere c hr θ)
      rw [mul_comm]
      refine mul_le_mul hMθ ?_ (by positivity) ((norm_nonneg _).trans hMθ)
      rw [inv_le_comm₀ (by linarith) (by positivity), inv_div]
      exact hdist


/-- The Cauchy integral over `C(c, r)` minus its leading term at infinity is `O(‖z - c‖⁻²)`. -/
theorem norm_circleIntegral_sub_inv_mul_add_le {f : ℂ → ℂ} {c z : ℂ} {r M : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (sphere c r)) (hM : ∀ w ∈ sphere c r, ‖f w‖ ≤ M)
    (hz : r < ‖z - c‖) :
    ‖(∮ w in C(c, r), (w - z)⁻¹ * f w) + (∮ w in C(c, r), f w) / (z - c)‖ ≤
      2 * π * r * (M * r / ((‖z - c‖ - r) * ‖z - c‖)) := by
  have hzc : z - c ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith
  have hne : ∀ w ∈ sphere c r, w - z ≠ 0 := fun w hw h => by
    rw [mem_sphere, dist_eq_norm, sub_eq_zero.mp h] at hw; linarith
  have hcont : ContinuousOn (fun w => (w - z)⁻¹) (sphere c r) := fun w hw =>
    ((continuousAt_id.sub continuousAt_const).inv₀ (hne w hw)).continuousWithinAt
  have hi1 : CircleIntegrable (fun w => (w - z)⁻¹ * f w) c r :=
    (hcont.mul hf).circleIntegrable hr.le
  have hi2 : CircleIntegrable f c r := hf.circleIntegrable hr.le
  have heq : (∮ w in C(c, r), (w - z)⁻¹ * f w) + (∮ w in C(c, r), f w) / (z - c) =
      ∮ w in C(c, r), f w * (w - c) / ((w - z) * (z - c)) := by
    rw [div_eq_mul_inv, mul_comm, ← circleIntegral.integral_const_mul,
      ← circleIntegral.integral_add hi1 (g := fun w => (z - c)⁻¹ * f w)
      ((continuousOn_const.mul hf).circleIntegrable hr.le)]
    refine circleIntegral.integral_congr hr.le fun w hw => ?_
    have := hne w hw
    field_simp
    ring
  rw [heq]
  refine circleIntegral.norm_integral_le_of_norm_le_const hr.le fun w hw => ?_
  have hfw := hM w hw
  have hw : ‖w - c‖ = r := by rwa [mem_sphere, dist_eq_norm] at hw
  have hwz : ‖z - c‖ - r ≤ ‖w - z‖ := by
    have := norm_sub_norm_le (z - c) (w - c)
    rw [hw, show z - c - (w - c) = -(w - z) by ring, norm_neg] at this
    exact this
  have hpos : 0 < ‖z - c‖ - r := by linarith
  rw [norm_div, norm_mul, norm_mul, hw]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hfw
  exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hfw hr.le) (by positivity)
    (mul_le_mul_of_nonneg_right hwz (norm_nonneg _))


/-- `y ↦ (s² + (y - b)²)⁻¹` is integrable for `s ≠ 0`. -/
theorem integrable_inv_sq_add_sub_sq {s : ℝ} (hs : s ≠ 0) (b : ℝ) :
    Integrable fun y : ℝ => (s ^ 2 + (y - b) ^ 2)⁻¹ := by
  have h := ((integrable_inv_one_add_sq.comp_div hs).comp_sub_right b).const_mul (s ^ 2)⁻¹
  refine h.congr (Eventually.of_forall fun y => ?_)
  field_simp

/-- `‖σ + yi - p‖² = (σ - Re p)² + (y - Im p)²`. -/
theorem norm_add_mul_I_sub_sq (σ y : ℝ) (p : ℂ) :
    ‖(σ : ℂ) + y * I - p‖ ^ 2 = (σ - p.re) ^ 2 + (y - p.im) ^ 2 := by
  rw [← normSq_eq_norm_sq, normSq_apply]
  simp
  ring

/-- A function holomorphic on the closed half-plane `ℜz ≥ c` and `O(‖z - p‖⁻²)` there, with
`ℜp < c`, has vanishing integral along the line `ℜz = c` (shift the line to `+∞`). -/
theorem integral_vertical_eq_zero_of_norm_le {k : ℂ → ℂ} {c K : ℝ} {p : ℂ} (hp : p.re < c)
    (hk : DifferentiableOn ℂ k {z | c ≤ z.re})
    (hb : ∀ z : ℂ, c ≤ z.re → ‖k z‖ ≤ K / ‖z - p‖ ^ 2) :
    ∫ y : ℝ, k (c + y * I) = 0 := by
  set a := p.re
  set b := p.im
  have hsq : ∀ σ y : ℝ, ‖(σ : ℂ) + y * I - p‖ ^ 2 = (σ - a) ^ 2 + (y - b) ^ 2 :=
    fun σ y => norm_add_mul_I_sub_sq σ y p
  have hK : 0 ≤ K := by
    have h := hb (c : ℂ) (by simp)
    have hpos : 0 < ‖(c : ℂ) - p‖ ^ 2 := by
      have := hsq c 0
      simp only [ofReal_zero, zero_mul, add_zero] at this
      rw [this]; nlinarith
    by_contra hneg
    have : K / ‖(c : ℂ) - p‖ ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith) hpos
    linarith [norm_nonneg (k c)]
  have hbound : ∀ σ y : ℝ, c ≤ σ → ‖k (σ + y * I)‖ ≤ K * ((σ - a) ^ 2 + (y - b) ^ 2)⁻¹ := by
    intro σ y hσ
    have := hb (σ + y * I) (by simpa using hσ)
    rw [hsq] at this
    rwa [← div_eq_mul_inv]
  have hcont : ∀ σ : ℝ, c ≤ σ → Continuous fun y : ℝ => k (σ + y * I) := fun σ hσ =>
    hk.continuousOn.comp_continuous (by fun_prop) fun y => by simpa using hσ
  have hint : ∀ σ : ℝ, c ≤ σ → Integrable fun y : ℝ => k (σ + y * I) := by
    intro σ hσ
    refine ((integrable_inv_sq_add_sub_sq (by linarith : σ - a ≠ 0) b).const_mul K).mono'
      (hcont σ hσ).aestronglyMeasurable (Eventually.of_forall fun y => hbound σ y hσ)
  -- horizontal cross-sections
  have hhor : ∀ C : ℝ, c ≤ C → ∀ l : Filter ℝ, Tendsto (fun T => |T - b|) l atTop →
      Tendsto (fun T : ℝ => ∫ x in c..C, k (x + T * I)) l (𝓝 0) := by
    intro C hC l hl
    have hlim : Tendsto (fun T => (C - c) * (K / |T - b| ^ 2)) l (𝓝 0) := by
      have := (tendsto_const_nhds (x := K)).div_atTop
        ((tendsto_pow_atTop two_ne_zero).comp hl)
      simpa using this.const_mul (C - c)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hl.eventually_gt_atTop 0] with T hT
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := C)
      (C := K / |T - b| ^ 2) (f := fun x => k (x + T * I)) fun x hx => by
        have hx' : c ≤ x := by
          rw [uIoc_of_le hC] at hx; exact hx.1.le
        refine (hbound x T hx').trans ?_
        rw [← div_eq_mul_inv, sq_abs]
        exact div_le_div_of_nonneg_left hK (by rw [← sq_abs]; exact pow_pos hT 2) (by nlinarith)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ C - c)] at h
    exact h.trans_eq (mul_comm _ _)
  have htop : Tendsto (fun T => |T - b|) atTop atTop :=
    tendsto_abs_atTop_atTop.comp (tendsto_atTop_add_const_right _ _ tendsto_id)
  have hbot : Tendsto (fun T => |T - b|) atBot atTop :=
    tendsto_abs_atBot_atTop.comp (tendsto_atBot_add_const_right _ _ tendsto_id)
  have hshift : ∀ C : ℝ, c < C → (∫ y : ℝ, k (C + y * I)) = ∫ y : ℝ, k (c + y * I) :=
    fun C hC => BarnesResidue.vertical_shift_of_differentiableOn hC
      (hk.mono fun z hz => hz.1) (hint c le_rfl) (hint C hC.le) (hhor C hC.le _ htop)
      (hhor C hC.le _ hbot)
  -- dominated convergence as the line moves to `+∞`
  have hdct : Tendsto (fun C : ℝ => ∫ y : ℝ, k (C + y * I)) atTop (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence
      (fun y : ℝ => K * ((c - a) ^ 2 + (y - b) ^ 2)⁻¹) (F := fun (C : ℝ) (y : ℝ) => k (C + y * I))
      (f := fun _ => (0 : ℂ)) (l := atTop) (μ := volume)
      (by filter_upwards [eventually_ge_atTop c] with C hC
          exact (hcont C hC).aestronglyMeasurable)
      (by filter_upwards [eventually_ge_atTop c] with C hC
          refine Eventually.of_forall fun y => (hbound C y hC).trans ?_
          gcongr)
      ((integrable_inv_sq_add_sub_sq (by linarith : c - a ≠ 0) b).const_mul K)
      (Eventually.of_forall fun y => by
        have hlim : Tendsto (fun C : ℝ => K * ((C - a) ^ 2)⁻¹) atTop (𝓝 0) := by
          have h1 : Tendsto (fun C : ℝ => (C - a) ^ 2) atTop atTop :=
            (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right _ _ tendsto_id)
          simpa using (h1.inv_tendsto_atTop).const_mul K
        refine squeeze_zero_norm' ?_ hlim
        filter_upwards [eventually_gt_atTop a, eventually_ge_atTop c] with C hCa hC
        refine (hbound C y hC).trans ?_
        gcongr
        nlinarith)
    simpa using this
  have hconst : Tendsto (fun C : ℝ => ∫ y : ℝ, k (C + y * I)) atTop
      (𝓝 (∫ y : ℝ, k (c + y * I))) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_gt_atTop c] with C hC using (hshift C hC).symm)
  exact tendsto_nhds_unique hconst hdct


/-- The mirror image of `integral_vertical_eq_zero_of_norm_le`: a function holomorphic on the
closed half-plane `ℜz ≤ d` and `O(‖z - p‖⁻²)` there, with `d < ℜp`, has vanishing integral along
the line `ℜz = d`. -/
theorem integral_vertical_eq_zero_of_norm_le' {k : ℂ → ℂ} {d K : ℝ} {p : ℂ} (hp : d < p.re)
    (hk : DifferentiableOn ℂ k {z | z.re ≤ d})
    (hb : ∀ z : ℂ, z.re ≤ d → ‖k z‖ ≤ K / ‖z - p‖ ^ 2) :
    ∫ y : ℝ, k (d + y * I) = 0 := by
  have h := integral_vertical_eq_zero_of_norm_le (k := fun z => k (-z)) (c := -d) (K := K)
    (p := -p) (by simpa using hp)
    (hk.comp (differentiableOn_neg _) fun z (hz : -d ≤ z.re) => by
      show (-z).re ≤ d
      rw [neg_re]; linarith)
    (fun z hz => by
      have := hb (-z) (by simp only [neg_re]; linarith)
      rwa [show -z - p = -(z - -p) by ring, norm_neg] at this)
  rw [← h, ← integral_neg_eq_self]
  congr 1
  funext y
  congr 1
  push_cast
  ring

/-- `1 + |ℑz| ≤ (1 + (1 + |ℑw|)/ε) ‖z - w‖` when `‖z - w‖ ≥ ε > 0`. -/
theorem one_add_abs_im_le {z w : ℂ} {ε : ℝ} (hε : 0 < ε) (h : ε ≤ ‖z - w‖) :
    1 + |z.im| ≤ (1 + (1 + |w.im|) / ε) * ‖z - w‖ := by
  have h1 : |z.im| ≤ |w.im| + ‖z - w‖ := by
    have := abs_im_le_norm (z - w)
    rw [sub_im] at this
    have := abs_sub_abs_le_abs_sub z.im w.im
    linarith
  have h2 : 1 + |w.im| ≤ (1 + |w.im|) / ε * ‖z - w‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hε]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  nlinarith

/-- A continuous `g : ℝ → ℂ` with `‖g y‖ ≤ K (1 + |y|)⁻²` is integrable. -/
theorem integrable_of_norm_le_inv_one_add_abs_sq {g : ℝ → ℂ} {K : ℝ} (hg : Continuous g)
    (hb : ∀ y, ‖g y‖ ≤ K * ((1 + |y|) ^ 2)⁻¹) : Integrable g := by
  have h := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).const_mul K
  refine h.mono' hg.aestronglyMeasurable (Eventually.of_forall fun y => (hb y).trans_eq ?_)
  rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two]

/-- Horizontal cross-section integrals of a function bounded by `K (1 + |ℑz|)⁻²` tend to `0`. -/
theorem tendsto_intervalIntegral_horizontal_of_norm_le {g : ℂ → ℂ} {a b K : ℝ} {l : Filter ℝ}
    (hl : Tendsto (fun T => |T|) l atTop)
    (hb : ∀ᶠ T : ℝ in l, ∀ x : ℝ, x ∈ Ι a b → ‖g (x + T * I)‖ ≤ K * ((1 + |T|) ^ 2)⁻¹) :
    Tendsto (fun T : ℝ => ∫ x in a..b, g (x + T * I)) l (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => K * ((1 + |T|) ^ 2)⁻¹ * |b - a|) l (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => (1 + |T|) ^ 2) l atTop :=
      (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_left _ _ hl)
    simpa using ((h1.inv_tendsto_atTop).const_mul K).mul_const |b - a|
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hb] with T hT
  exact intervalIntegral.norm_integral_le_of_norm_le_const hT


/-- A common radius for small circles around the points of a finite set in an open strip. -/
private lemma exists_radius_of_finset (P : Finset ℂ) {c₁ c₂ : ℝ}
    (hP : ∀ p ∈ P, c₁ < p.re ∧ p.re < c₂) :
    ∃ ρ > 0, ∀ p ∈ P, c₁ < p.re - 4 * ρ ∧ p.re + 4 * ρ < c₂ ∧
      ∀ q ∈ P, q ≠ p → 4 * ρ < ‖q - p‖ := by
  classical
  rcases P.eq_empty_or_nonempty with hP0 | hne
  · exact ⟨1, one_pos, by simp [hP0]⟩
  set e : ℂ × ℂ → ℝ := fun pq => if pq.1 = pq.2 then min (pq.1.re - c₁) (c₂ - pq.1.re)
    else ‖pq.1 - pq.2‖ with he
  have hepos : ∀ pq ∈ P ×ˢ P, 0 < e pq := by
    rintro ⟨p, q⟩ hpq
    rw [Finset.mem_product] at hpq
    simp only [he]
    split_ifs with h
    · have := hP p hpq.1; exact lt_min (by linarith) (by linarith)
    · exact norm_pos_iff.mpr (sub_ne_zero.mpr h)
  have hne2 : (P ×ˢ P).Nonempty := hne.product hne
  set m := (P ×ˢ P).inf' hne2 e
  have hm : 0 < m := (Finset.lt_inf'_iff hne2).mpr hepos
  have hle : ∀ pq ∈ P ×ˢ P, m ≤ e pq := fun pq hpq => Finset.inf'_le _ hpq
  refine ⟨m / 8, by positivity, fun p hp => ?_⟩
  have hpp := hle (p, p) (Finset.mem_product.mpr ⟨hp, hp⟩)
  simp only [he, ↓reduceIte] at hpp
  refine ⟨by linarith [min_le_left (p.re - c₁) (c₂ - p.re)],
    by linarith [min_le_right (p.re - c₁) (c₂ - p.re)], fun q hq hqp => ?_⟩
  have hqp' := hle (q, p) (Finset.mem_product.mpr ⟨hq, hp⟩)
  simp only [he, hqp, ↓reduceIte] at hqp'
  linarith

/-- `‖z - w‖⁻¹ ≤ C (1 + |ℑz|)⁻¹` with `C = 1 + (1 + |ℑw|)/ε` when `‖z - w‖ ≥ ε > 0`. -/
private lemma inv_norm_sub_le {z w : ℂ} {ε : ℝ} (hε : 0 < ε) (h : ε ≤ ‖z - w‖) :
    ‖z - w‖⁻¹ ≤ (1 + (1 + |w.im|) / ε) * (1 + |z.im|)⁻¹ := by
  have h1 := one_add_abs_im_le hε h
  have hpos : 0 < ‖z - w‖ := hε.trans_le h
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ hpos]
  linarith [mul_comm (1 + (1 + |w.im|) / ε) ‖z - w‖]

/-- The remainder `J(z) + A/(z - c)` of a Cauchy integral is `O(‖z - c‖⁻²)` for
`‖z - c‖ ≥ 2r`. -/
private lemma norm_circleIntegral_add_le_sq {f : ℂ → ℂ} {c z : ℂ} {r M : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (sphere c r)) (hM : ∀ w ∈ sphere c r, ‖f w‖ ≤ M)
    (hz : 2 * r ≤ ‖z - c‖) :
    ‖(∮ w in C(c, r), (w - z)⁻¹ * f w) + (∮ w in C(c, r), f w) / (z - c)‖ ≤
      4 * π * r ^ 2 * M / ‖z - c‖ ^ 2 := by
  have h := norm_circleIntegral_sub_inv_mul_add_le hr hf hM (by linarith)
  refine h.trans ?_
  have hM0 : 0 ≤ M := by
    have := hM (c + r) (by simp [abs_of_pos hr]); exact (norm_nonneg _).trans this
  have hpos : 0 < ‖z - c‖ := by linarith
  rw [show 2 * π * r * (M * r / ((‖z - c‖ - r) * ‖z - c‖)) =
    2 * π * r ^ 2 * M / ((‖z - c‖ - r) * ‖z - c‖) by ring,
    show 4 * π * r ^ 2 * M / ‖z - c‖ ^ 2 = 2 * π * r ^ 2 * M / (‖z - c‖ / 2 * ‖z - c‖) by
      field_simp; ring]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_right (by linarith) hpos.le)


/-- **Shifting a vertical line of integration across isolated singularities.** Let `f` be
holomorphic on the closed strip `c₁ ≤ ℜz ≤ c₂` except at the points of a finite set `P` in the open
strip (the singularities may be essential), integrable on both boundary lines, with horizontal
cross-section integrals tending to `0` at `±i∞`. Then for all small `r > 0`,
`i (∫ f(c₂ + iy) dy - ∫ f(c₁ + iy) dy) = ∑_{p ∈ P} ∮_{|z - p| = r} f(z) dz`. -/
theorem integral_vertical_sub_eq_sum_circleIntegral {f : ℂ → ℂ} {c₁ c₂ : ℝ} (h : c₁ < c₂)
    (P : Finset ℂ) (hP : ∀ p ∈ P, c₁ < p.re ∧ p.re < c₂)
    (hf : DifferentiableOn ℂ f (re ⁻¹' Icc c₁ c₂ \ P))
    (hi₁ : Integrable fun y : ℝ => f (c₁ + y * I))
    (hi₂ : Integrable fun y : ℝ => f (c₂ + y * I))
    (htop : Tendsto (fun T : ℝ => ∫ x in c₁..c₂, f (x + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in c₁..c₂, f (x + T * I)) atBot (𝓝 0)) :
    ∃ ρ > 0, ∀ r, 0 < r → r < ρ →
      I * ((∫ y : ℝ, f (c₂ + y * I)) - ∫ y : ℝ, f (c₁ + y * I)) =
        ∑ p ∈ P, ∮ z in C(p, r), f z := by
  classical
  obtain ⟨ρ, hρ, hρP⟩ := exists_radius_of_finset P hP
  refine ⟨ρ, hρ, fun r hr hrρ => ?_⟩
  set R := 2 * r with hRdef
  -- differentiability of `f` near the singularities and in the open strip
  have hfa : ∀ w : ℂ, c₁ < w.re → w.re < c₂ → w ∉ P → DifferentiableAt ℂ f w := by
    intro w h1 h2 hw
    refine hf.differentiableAt (Filter.mem_of_superset ((((isOpen_Ioo (a := c₁) (b := c₂)).preimage
      continuous_re).inter P.finite_toSet.isClosed.isOpen_compl).mem_nhds ⟨⟨h1, h2⟩, hw⟩) ?_)
    rintro v ⟨hv, hvP⟩
    exact ⟨Ioo_subset_Icc_self hv, hvP⟩
  have hnear : ∀ p ∈ P, ∀ w : ℂ, w ≠ p → ‖w - p‖ < 4 * ρ → DifferentiableAt ℂ f w := by
    intro p hp w hwp hw
    obtain ⟨h1, h2, h3⟩ := hρP p hp
    have hre : |w.re - p.re| ≤ ‖w - p‖ := by
      rw [← sub_re]; exact abs_re_le_norm _
    refine hfa w (by linarith [neg_abs_le (w.re - p.re)]) (by linarith [le_abs_self (w.re - p.re)])
      fun hwP => ?_
    have := h3 w hwP hwp
    linarith
  have hrR : r < R := by rw [hRdef]; linarith
  have hR4 : R < 4 * ρ := by rw [hRdef]; linarith
  -- continuity of `f` on circles and annuli around the singularities
  have hcontA : ∀ p ∈ P, ContinuousOn f (closedBall p R \ ball p r) := by
    intro p hp w hw
    have hw1 : ‖w - p‖ ≤ R := by simpa [dist_eq_norm] using hw.1
    have hw2 : r ≤ ‖w - p‖ := by simpa [dist_eq_norm] using hw.2
    refine (hnear p hp w (fun h => ?_) (by linarith)).continuousAt.continuousWithinAt
    rw [h, sub_self, norm_zero] at hw2; linarith
  have hsphr : ∀ p ∈ P, ContinuousOn f (sphere p r) := fun p hp =>
    (hcontA p hp).mono fun w hw => ⟨closedBall_subset_closedBall hrR.le
      (sphere_subset_closedBall hw), by rw [mem_ball, not_lt, mem_sphere.mp hw]⟩
  have hsphR : ∀ p ∈ P, ContinuousOn f (sphere p R) := fun p hp =>
    (hcontA p hp).mono fun w hw => ⟨sphere_subset_closedBall hw, by
      rw [mem_ball, not_lt, mem_sphere.mp hw]; exact hrR.le⟩
  -- the auxiliary functions
  set J : ℂ → ℂ → ℂ := fun p z => ∮ w in C(p, r), (w - z)⁻¹ * f w with hJ
  set O : ℂ → ℂ → ℂ := fun p z => ∮ w in C(p, R), (w - z)⁻¹ * f w with hO
  set A : ℂ → ℂ := fun p => ∮ w in C(p, r), f w with hA
  set q₀ : ℂ := ((c₁ - 1 : ℝ) : ℂ) with hq₀
  set Kf : ℂ → ℂ → ℂ := fun p z => -(J p z + A p / (z - p)) with hKf
  set Rf : ℂ → ℂ → ℂ := fun p z => A p * (p - q₀) / (z - q₀) / (z - p) with hRf
  set Et : ℂ → ℂ → ℂ := fun p z => if ‖z - p‖ ≤ r then 2 * π * I * f z - O p z - A p / (z - q₀)
    else -J p z - A p / (z - q₀) with hEt
  set Ψ : ℂ → ℂ := fun z => 2 * π * I * f z - ∑ p ∈ P, Et p z with hΨ
  have hJd : ∀ p ∈ P, DifferentiableOn ℂ (J p) {z | r < ‖z - p‖} := fun p hp =>
    (differentiableOn_circleIntegral_sub_inv_mul hr.le (hsphr p hp)).mono fun z hz hz' => by
      rw [mem_sphere, dist_eq_norm] at hz'
      have hz2 : r < ‖z - p‖ := hz
      linarith
  have hOd : ∀ p ∈ P, DifferentiableOn ℂ (O p) (ball p R) := fun p hp =>
    (differentiableOn_circleIntegral_sub_inv_mul (by linarith) (hsphR p hp)).mono
      fun z hz hz' => by
        rw [mem_ball] at hz; rw [mem_sphere] at hz'; linarith
  have hann : ∀ p ∈ P, ∀ z : ℂ, r < ‖z - p‖ → ‖z - p‖ < R → O p z - J p z = 2 * π * I * f z :=
    fun p hp z h1 h2 => circleIntegral_sub_inv_mul_annulus hr h1 h2 (hcontA p hp)
      fun w hw => hnear p hp w (fun h => by
        have := hw.2; rw [h] at this; exact this (by simp [hr.le])) (by
        have := hw.1; rw [mem_ball, dist_eq_norm] at this; linarith)
  have hfar : ∀ p ∈ P, ∀ q ∈ P, q ≠ p → ∀ w : ℂ, ‖w - p‖ < R → r < ‖w - q‖ := by
    intro p hp q hq hqp w hw
    have h1 := (hρP p hp).2.2 q hq hqp
    have h2 : ‖q - p‖ ≤ ‖w - q‖ + ‖w - p‖ := by
      calc ‖q - p‖ = ‖(w - p) - (w - q)‖ := by ring_nf
        _ ≤ ‖w - p‖ + ‖w - q‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    rw [hRdef] at hw
    linarith
  have hq₀re : q₀.re = c₁ - 1 := by simp [hq₀]
  have hneq₀ : ∀ w : ℂ, c₁ ≤ w.re → w - q₀ ≠ 0 := fun w hw h0 => by
    have := congrArg re h0
    rw [sub_re, hq₀re, zero_re] at this
    linarith
  have hnearre : ∀ p ∈ P, ∀ w : ℂ, ‖w - p‖ < 4 * ρ → c₁ < w.re ∧ w.re < c₂ := by
    intro p hp w hw
    obtain ⟨h1, h2, -⟩ := hρP p hp
    have hre : |w.re - p.re| ≤ ‖w - p‖ := by
      rw [← sub_re]; exact abs_re_le_norm _
    constructor
    · linarith [neg_abs_le (w.re - p.re)]
    · linarith [le_abs_self (w.re - p.re)]
  have hEt_near : ∀ p ∈ P, ∀ w : ℂ, ‖w - p‖ < R →
      Et p w = 2 * π * I * f w - O p w - A p / (w - q₀) := by
    intro p hp w hw
    by_cases hwr : ‖w - p‖ ≤ r
    · simp only [hEt, hwr, ↓reduceIte]
    · simp only [hEt, hwr, ↓reduceIte]
      have := hann p hp w (lt_of_not_ge hwr) hw
      linear_combination this
  have hEt_far : ∀ p : ℂ, ∀ w : ℂ, r < ‖w - p‖ → Et p w = -J p w - A p / (w - q₀) := by
    intro p w hw
    simp only [hEt, not_le.mpr hw, ↓reduceIte]
  have hJat : ∀ p ∈ P, ∀ w : ℂ, r < ‖w - p‖ → DifferentiableAt ℂ (J p) w := fun p hp w hw =>
    (hJd p hp).differentiableAt ((isOpen_lt continuous_const
      (continuous_id.sub continuous_const).norm).mem_nhds hw)
  -- `Ψ` is holomorphic on the closed strip
  have hΨd : DifferentiableOn ℂ Ψ (re ⁻¹' Icc c₁ c₂) := by
    intro z hz
    have hzc₁ : c₁ ≤ z.re := hz.1
    by_cases hz' : ∃ p ∈ P, ‖z - p‖ ≤ r
    · obtain ⟨p, hp, hzp⟩ := hz'
      set G : ℂ → ℂ := fun w => O p w + A p / (w - q₀) -
        ∑ q ∈ P.erase p, (-J q w - A q / (w - q₀)) with hG
      have hzb : z ∈ ball p R := by rw [mem_ball, dist_eq_norm]; linarith
      have heq : Ψ =ᶠ[𝓝 z] G := by
        filter_upwards [isOpen_ball.mem_nhds hzb] with w hw
        rw [mem_ball, dist_eq_norm] at hw
        simp only [hΨ, hG]
        rw [← Finset.add_sum_erase P _ hp, hEt_near p hp w hw,
          Finset.sum_congr rfl fun q hq => hEt_far q w
            (hfar p hp q (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq) w hw)]
        ring
      have hzq : z - q₀ ≠ 0 := hneq₀ z hzc₁
      have hGd : DifferentiableAt ℂ G z := by
        refine (((hOd p hp).differentiableAt (isOpen_ball.mem_nhds hzb)).add
          ((differentiableAt_const _).div (differentiableAt_id.sub_const _) hzq)).sub ?_
        refine DifferentiableAt.fun_sum fun q hq => ?_
        exact (hJat q (Finset.mem_of_mem_erase hq) z (hfar p hp q (Finset.mem_of_mem_erase hq)
          (Finset.ne_of_mem_erase hq) z (by rw [mem_ball, dist_eq_norm] at hzb; exact hzb))).neg.sub
          ((differentiableAt_const _).div (differentiableAt_id.sub_const _) hzq)
      exact (hGd.congr_of_eventuallyEq heq).differentiableWithinAt
    · push Not at hz'
      have hzP : z ∉ P := fun hzP => by
        have := hz' z hzP; rw [sub_self, norm_zero] at this; linarith
      set H : ℂ → ℂ := fun w => 2 * π * I * f w - ∑ p ∈ P, (-J p w - A p / (w - q₀)) with hH
      have hV : ∀ᶠ w in 𝓝 z, ∀ p ∈ P, r < ‖w - p‖ :=
        (Filter.eventually_all_finset P).mpr fun p hp => (isOpen_lt continuous_const
          (continuous_id.sub continuous_const).norm).mem_nhds (hz' p hp)
      have heq : Ψ =ᶠ[𝓝 z] H := by
        filter_upwards [hV] with w hw
        simp only [hΨ, hH]
        rw [Finset.sum_congr rfl fun p hp => hEt_far p w (hw p hp)]
      have hfz : DifferentiableWithinAt ℂ f (re ⁻¹' Icc c₁ c₂) z :=
        (hf z ⟨hz, hzP⟩).mono_of_mem_nhdsWithin
          (inter_mem_nhdsWithin _ (P.finite_toSet.isClosed.isOpen_compl.mem_nhds hzP))
      have hzq : z - q₀ ≠ 0 := hneq₀ z hzc₁
      have hHd : DifferentiableWithinAt ℂ H (re ⁻¹' Icc c₁ c₂) z := by
        refine (hfz.const_mul _).sub ?_
        refine DifferentiableWithinAt.fun_sum fun p hp => ?_
        exact ((hJat p hp z (hz' p hp)).neg.sub ((differentiableAt_const _).div
          (differentiableAt_id.sub_const _) hzq)).differentiableWithinAt
      exact hHd.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds
  -- bounds away from the singularities
  obtain ⟨M₀, hM₀⟩ : ∃ M, ∀ w ∈ ⋃ p ∈ P, sphere p r, ‖f w‖ ≤ M := by
    refine (P.finite_toSet.isCompact_biUnion fun p _ => isCompact_sphere p r)
      |>.exists_bound_of_continuousOn fun w hw => ?_
    obtain ⟨p, hp, hw⟩ := mem_iUnion₂.mp hw
    refine (hnear p hp w (fun h => ?_) ?_).continuousAt.continuousWithinAt
    · rw [h, mem_sphere, dist_self] at hw; linarith
    · rw [mem_sphere, dist_eq_norm] at hw; linarith
  set M : ℝ := max M₀ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ p ∈ P, ∀ w ∈ sphere p r, ‖f w‖ ≤ M := fun p hp w hw =>
    (hM₀ w (mem_iUnion₂.mpr ⟨p, hp, hw⟩)).trans (le_max_left _ _)
  have hKb : ∀ p ∈ P, ∀ z : ℂ, R ≤ ‖z - p‖ → ‖Kf p z‖ ≤ 4 * π * r ^ 2 * M / ‖z - p‖ ^ 2 :=
    fun p hp z hz => by
      simp only [hKf, norm_neg]
      exact norm_circleIntegral_add_le_sq hr (hsphr p hp) (hM p hp) hz
  set Cp : ℂ → ℝ := fun p => 1 + (1 + |p.im|) / R with hCp
  set C0 : ℝ := 1 + (1 + |q₀.im|) / 1 with hC0
  have hR0 : 0 < R := by linarith
  have hCp0 : ∀ p, 0 ≤ Cp p := fun p => by simp only [hCp]; positivity
  have hC00 : 0 ≤ C0 := by simp only [hC0]; positivity
  have hup : ∀ p : ℂ, ∀ z : ℂ, R ≤ ‖z - p‖ → ‖z - p‖⁻¹ ≤ Cp p * (1 + |z.im|)⁻¹ :=
    fun p z hz => inv_norm_sub_le hR0 hz
  have hu0 : ∀ z : ℂ, c₁ ≤ z.re → ‖z - q₀‖⁻¹ ≤ C0 * (1 + |z.im|)⁻¹ := by
    intro z hz
    refine inv_norm_sub_le one_pos ?_
    have := re_le_norm (z - q₀)
    rw [sub_re, hq₀re] at this
    linarith
  have hKu : ∀ p ∈ P, ∀ z : ℂ, R ≤ ‖z - p‖ →
      ‖Kf p z‖ ≤ 4 * π * r ^ 2 * M * Cp p ^ 2 * ((1 + |z.im|) ^ 2)⁻¹ := by
    intro p hp z hz
    have hu := hup p z hz
    refine (hKb p hp z hz).trans ?_
    rw [div_eq_mul_inv]
    simp only [← inv_pow]
    have := pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) hu 2
    rw [mul_pow] at this
    calc 4 * π * r ^ 2 * M * ‖z - p‖⁻¹ ^ 2 ≤
        4 * π * r ^ 2 * M * (Cp p ^ 2 * (1 + |z.im|)⁻¹ ^ 2) := by gcongr
      _ = _ := by ring
  have hRu : ∀ p ∈ P, ∀ z : ℂ, c₁ ≤ z.re → R ≤ ‖z - p‖ →
      ‖Rf p z‖ ≤ ‖A p * (p - q₀)‖ * C0 * Cp p * ((1 + |z.im|) ^ 2)⁻¹ := by
    intro p hp z hz hzp
    have hu := hup p z hzp
    have hi0 : 0 ≤ (1 + |z.im|)⁻¹ := by positivity
    simp only [hRf, norm_div]
    rw [div_div, div_eq_mul_inv, mul_inv, ← inv_pow]
    have h0 := hu0 z hz
    calc ‖A p * (p - q₀)‖ * (‖z - q₀‖⁻¹ * ‖z - p‖⁻¹) ≤
        ‖A p * (p - q₀)‖ * ((C0 * (1 + |z.im|)⁻¹) * (Cp p * (1 + |z.im|)⁻¹)) := by
          gcongr
      _ = _ := by ring
  set G : ℂ → ℂ := fun z => ∑ p ∈ P, (Kf p z + Rf p z) with hGdef
  set KG : ℝ := ∑ p ∈ P, (4 * π * r ^ 2 * M * Cp p ^ 2 + ‖A p * (p - q₀)‖ * C0 * Cp p) with hKG
  have hGb : ∀ z : ℂ, c₁ ≤ z.re → (∀ p ∈ P, R ≤ ‖z - p‖) →
      ‖G z‖ ≤ KG * ((1 + |z.im|) ^ 2)⁻¹ := by
    intro z hz hzP
    simp only [hGdef, hKG, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    refine (norm_add_le _ _).trans ?_
    have h1 := hKu p hp z (hzP p hp)
    have h2 := hRu p hp z hz (hzP p hp)
    linarith
  -- continuity away from the singularities
  have hKd : ∀ p ∈ P, DifferentiableOn ℂ (Kf p) {z | r < ‖z - p‖} := by
    intro p hp z hz
    have hzp : z - p ≠ 0 := fun h0 => by
      have hz' : r < ‖z - p‖ := hz
      rw [h0, norm_zero] at hz'; linarith
    exact ((hJat p hp z hz).add ((differentiableAt_const _).div
      (differentiableAt_id.sub_const _) hzp)).neg.differentiableWithinAt
  set Wset : Set ℂ := {z | c₁ ≤ z.re ∧ ∀ p ∈ P, R ≤ ‖z - p‖} with hWset
  have hRc : ∀ p ∈ P, ContinuousOn (Rf p) Wset := by
    intro p hp z hz
    have hzp : z - p ≠ 0 := fun h0 => by
      have := hz.2 p hp; rw [h0, norm_zero] at this; linarith
    exact (((continuousAt_const.div (continuousAt_id.sub continuousAt_const)
      (hneq₀ z hz.1)).div (continuousAt_id.sub continuousAt_const) hzp)).continuousWithinAt
  have hKc : ∀ p ∈ P, ContinuousOn (Kf p) Wset := fun p hp =>
    (hKd p hp).continuousOn.mono fun z hz => by
      have := hz.2 p hp; show r < ‖z - p‖; linarith
  have hGc : ContinuousOn G Wset := continuousOn_finsetSum _ fun p hp => (hKc p hp).add (hRc p hp)
  have hEtKR : ∀ p ∈ P, ∀ z ∈ Wset, Et p z = Kf p z + Rf p z := by
    intro p hp z hz
    have hzp : z - p ≠ 0 := fun h0 => by
      have := hz.2 p hp; rw [h0, norm_zero] at this; linarith
    have hzq := hneq₀ z hz.1
    rw [hEt_far p z (by linarith [hz.2 p hp])]
    simp only [hKf, hRf]
    field_simp
    ring
  have hΨG : ∀ z ∈ Wset, Ψ z = 2 * π * I * f z - G z := fun z hz => by
    simp only [hΨ, hGdef]
    rw [Finset.sum_congr rfl fun p hp => hEtKR p hp z hz]
  -- the boundary lines lie in `Wset`
  have hline : ∀ σ : ℝ, (σ = c₁ ∨ σ = c₂) → ∀ y : ℝ, (σ : ℂ) + y * I ∈ Wset := by
    intro σ hσ y
    refine ⟨by rcases hσ with rfl | rfl <;> simp [h.le], fun p hp => ?_⟩
    obtain ⟨h1, h2, -⟩ := hρP p hp
    have hre : |σ - p.re| ≤ ‖(σ : ℂ) + y * I - p‖ := by
      have := abs_re_le_norm ((σ : ℂ) + y * I - p); simpa using this
    rcases hσ with rfl | rfl
    · rw [abs_of_neg (by linarith)] at hre; linarith
    · rw [abs_of_pos (by linarith)] at hre; linarith
  have him : ∀ σ y : ℝ, ((σ : ℂ) + y * I).im = y := fun σ y => by simp
  have hlineInt : ∀ σ : ℝ, (σ = c₁ ∨ σ = c₂) → ∀ g : ℂ → ℂ, ∀ K : ℝ, ContinuousOn g Wset →
      (∀ z ∈ Wset, ‖g z‖ ≤ K * ((1 + |z.im|) ^ 2)⁻¹) → Integrable fun y : ℝ => g (σ + y * I) :=
    fun σ hσ g K hg hb => integrable_of_norm_le_inv_one_add_abs_sq
      (hg.comp_continuous (by fun_prop) (hline σ hσ)) fun y => by
        have := hb _ (hline σ hσ y); rwa [him] at this
  have hKW : ∀ p ∈ P, ∀ z ∈ Wset, ‖Kf p z‖ ≤ 4 * π * r ^ 2 * M * Cp p ^ 2 *
      ((1 + |z.im|) ^ 2)⁻¹ := fun p hp z hz => hKu p hp z (hz.2 p hp)
  have hRW : ∀ p ∈ P, ∀ z ∈ Wset, ‖Rf p z‖ ≤ ‖A p * (p - q₀)‖ * C0 * Cp p *
      ((1 + |z.im|) ^ 2)⁻¹ := fun p hp z hz => hRu p hp z hz.1 (hz.2 p hp)
  have hGW : ∀ z ∈ Wset, ‖G z‖ ≤ KG * ((1 + |z.im|) ^ 2)⁻¹ := fun z hz => hGb z hz.1 hz.2
  -- horizontal cross-sections eventually lie in `Wset`
  have hev : ∀ l : Filter ℝ, Tendsto (fun T => |T|) l atTop →
      ∀ᶠ T : ℝ in l, ∀ x : ℝ, x ∈ Icc c₁ c₂ → (x : ℂ) + T * I ∈ Wset := by
    intro l hl
    filter_upwards [(Filter.eventually_all_finset P).mpr fun p _ =>
      hl.eventually_ge_atTop (R + |p.im|)] with T hT x hx
    refine ⟨by simpa using hx.1, fun p hp => ?_⟩
    have h1 : |T - p.im| ≤ ‖(x : ℂ) + T * I - p‖ := by
      have := abs_im_le_norm ((x : ℂ) + T * I - p); simpa using this
    have h2 := abs_sub_abs_le_abs_sub T p.im
    linarith [hT p hp]
  have hhor : ∀ l : Filter ℝ, Tendsto (fun T => |T|) l atTop → ∀ g : ℂ → ℂ, ∀ K : ℝ,
      (∀ z ∈ Wset, ‖g z‖ ≤ K * ((1 + |z.im|) ^ 2)⁻¹) →
      Tendsto (fun T : ℝ => ∫ x in c₁..c₂, g (x + T * I)) l (𝓝 0) := by
    intro l hl g K hb
    refine tendsto_intervalIntegral_horizontal_of_norm_le (K := K) hl ?_
    filter_upwards [hev l hl] with T hT x hx
    rw [uIoc_of_le h.le] at hx
    have := hb _ (hT x (Ioc_subset_Icc_self hx))
    rwa [him] at this
  have htopA : Tendsto (fun T : ℝ => |T|) atTop atTop := tendsto_abs_atTop_atTop
  have hbotA : Tendsto (fun T : ℝ => |T|) atBot atTop := tendsto_abs_atBot_atTop
  have hc₁ : c₁ = c₁ ∨ c₁ = c₂ := Or.inl rfl
  have hc₂ : c₂ = c₁ ∨ c₂ = c₂ := Or.inr rfl
  -- integrability on the boundary lines
  have hKi : ∀ σ : ℝ, (σ = c₁ ∨ σ = c₂) → ∀ p ∈ P, Integrable fun y : ℝ => Kf p (σ + y * I) :=
    fun σ hσ p hp => hlineInt σ hσ _ _ (hKc p hp) (hKW p hp)
  have hRi : ∀ σ : ℝ, (σ = c₁ ∨ σ = c₂) → ∀ p ∈ P, Integrable fun y : ℝ => Rf p (σ + y * I) :=
    fun σ hσ p hp => hlineInt σ hσ _ _ (hRc p hp) (hRW p hp)
  have hGi : ∀ σ : ℝ, (σ = c₁ ∨ σ = c₂) → Integrable fun y : ℝ => G (σ + y * I) :=
    fun σ hσ => hlineInt σ hσ _ _ hGc hGW
  have hΨline : ∀ σ : ℝ, (σ = c₁ ∨ σ = c₂) → (fun y : ℝ => Ψ (σ + y * I)) =
      fun y : ℝ => 2 * π * I * f (σ + y * I) - G (σ + y * I) :=
    fun σ hσ => funext fun y => hΨG _ (hline σ hσ y)
  have hΨi₁ : Integrable fun y : ℝ => Ψ (c₁ + y * I) := by
    rw [hΨline c₁ hc₁]; exact (hi₁.const_mul _).sub (hGi c₁ hc₁)
  have hΨi₂ : Integrable fun y : ℝ => Ψ (c₂ + y * I) := by
    rw [hΨline c₂ hc₂]; exact (hi₂.const_mul _).sub (hGi c₂ hc₂)
  -- horizontal cross-sections of `Ψ`
  have hΨhor : ∀ l : Filter ℝ, Tendsto (fun T => |T|) l atTop →
      Tendsto (fun T : ℝ => ∫ x in c₁..c₂, f (x + T * I)) l (𝓝 0) →
      Tendsto (fun T : ℝ => ∫ x in c₁..c₂, Ψ (x + T * I)) l (𝓝 0) := by
    intro l hl hfl
    have hlim := (hfl.const_mul (2 * π * I)).sub (hhor l hl G KG hGW)
    rw [mul_zero, sub_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [hev l hl] with T hT
    have hfT : IntervalIntegrable (fun x : ℝ => f (x + T * I)) volume c₁ c₂ := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le h.le]
      refine hf.continuousOn.comp (Continuous.continuousOn (by fun_prop)) fun x hx => ?_
      refine ⟨by simpa using hx, fun hP' => ?_⟩
      have := (hT x hx).2 _ hP'
      rw [sub_self, norm_zero] at this; linarith
    have hGT : IntervalIntegrable (fun x : ℝ => G (x + T * I)) volume c₁ c₂ := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le h.le]
      exact hGc.comp (by fun_prop) fun x hx => hT x hx
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (hfT.const_mul _) hGT]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le h.le] at hx
    exact (hΨG _ (hT x hx)).symm
  have hshift := BarnesResidue.vertical_shift_of_differentiableOn h hΨd hΨi₁ hΨi₂
    (hΨhor atTop htopA htop) (hΨhor atBot hbotA hbot)
  -- the remainders `Kf` have vanishing line integrals
  have hreN : ∀ p : ℂ, ∀ z : ℂ, |z.re - p.re| ≤ ‖z - p‖ := fun p z => by
    rw [← sub_re]; exact abs_re_le_norm _
  have hK0 : ∀ σ : ℝ, (σ = c₁ ∨ σ = c₂) → ∀ p ∈ P, ∫ y : ℝ, Kf p (σ + y * I) = 0 := by
    intro σ hσ p hp
    obtain ⟨h1, h2, -⟩ := hρP p hp
    rcases hσ with hσ | hσ <;> rw [hσ]
    · refine integral_vertical_eq_zero_of_norm_le' (K := 4 * π * r ^ 2 * M) (by linarith)
        ((hKd p hp).mono fun z (hz : z.re ≤ c₁) => ?_) fun z (hz : z.re ≤ c₁) => ?_
      · have := hreN p z
        rw [abs_of_neg (by linarith)] at this
        show r < ‖z - p‖; linarith
      · have := hreN p z
        rw [abs_of_neg (by linarith)] at this
        exact hKb p hp z (by linarith)
    · refine integral_vertical_eq_zero_of_norm_le (K := 4 * π * r ^ 2 * M) (by linarith)
        ((hKd p hp).mono fun z (hz : c₂ ≤ z.re) => ?_) fun z (hz : c₂ ≤ z.re) => ?_
      · have := hreN p z
        rw [abs_of_pos (by linarith)] at this
        show r < ‖z - p‖; linarith
      · have := hreN p z
        rw [abs_of_pos (by linarith)] at this
        exact hKb p hp z (by linarith)
  -- the rational parts `Rf` carry the residues
  have hR2 : ∀ p ∈ P, (∫ y : ℝ, Rf p (c₂ + y * I)) - ∫ y : ℝ, Rf p (c₁ + y * I) =
      2 * π * A p := by
    intro p hp
    have hpq : p - q₀ ≠ 0 := hneq₀ p (hP p hp).1.le
    have := BarnesResidue.vertical_shift (φ := fun z => A p * (p - q₀) / (z - q₀))
      (hP p hp).1 (hP p hp).2
      (fun z hz => by
        have : DifferentiableAt ℂ (fun w : ℂ => A p * (p - q₀) / (w - q₀)) z :=
          (differentiableAt_const _).div (differentiableAt_id.sub_const _) (hneq₀ z hz.1)
        exact this.differentiableWithinAt)
      (hRi c₁ hc₁ p hp) (hRi c₂ hc₂ p hp) (hhor atTop htopA (Rf p) _ (hRW p hp))
      (hhor atBot hbotA (Rf p) _ (hRW p hp))
    rw [mul_div_assoc, div_self hpq, mul_one] at this
    exact this
  have hΨint : ∀ σ : ℝ, (σ = c₁ ∨ σ = c₂) → ∫ y : ℝ, Ψ (σ + y * I) =
      2 * π * I * (∫ y : ℝ, f (σ + y * I)) - ∑ p ∈ P, ∫ y : ℝ, Rf p (σ + y * I) := by
    intro σ hσ
    have hfi : Integrable fun y : ℝ => f (σ + y * I) := by rcases hσ with rfl | rfl <;> assumption
    rw [hΨline σ hσ, integral_sub (hfi.const_mul _) (hGi σ hσ), integral_const_mul]
    congr 1
    simp only [hGdef]
    rw [integral_finsetSum P (f := fun p (y : ℝ) => Kf p (σ + y * I) + Rf p (σ + y * I))
      fun p hp => (hKi σ hσ p hp).add (hRi σ hσ p hp)]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [integral_add (hKi σ hσ p hp) (hRi σ hσ p hp), hK0 σ hσ p hp, zero_add]
  rw [hΨint c₁ hc₁, hΨint c₂ hc₂] at hshift
  have hsum : ∑ p ∈ P, ((∫ y : ℝ, Rf p (c₂ + y * I)) - ∫ y : ℝ, Rf p (c₁ + y * I)) =
      2 * π * ∑ p ∈ P, A p := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl hR2
  rw [Finset.sum_sub_distrib] at hsum
  have hpi : (2 * π : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr this.ne')
  refine mul_left_cancel₀ hpi ?_
  linear_combination hshift + hsum

end Complex
