/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Associated
public import DLMF.OrthogonalPolynomials.ClassicalInstances
public import DLMFMathlib.Analysis.ODE.SturmCount
public import DLMFMathlib.Analysis.ODE.SturmDeformation

/-!
# Zero counts of Ferrers functions by Sturm comparison

Tools for the real zero counts of DLMF §14.16(ii). The Ferrers functions of real parameters
satisfy the self-adjoint equation `((1-x²)y')' + (ν(ν+1) - μ²/(1-x²)) y = 0` on `(-1, 1)`
(`lzt_ferrersP_sol`). For two solutions `y`, `u` with coefficients `qy < qu`, the weighted
Wronskian `W = (1-x²)(u'y - uy')` is strictly monotone wherever `u y > 0`; this gives

* the classical Sturm comparison between consecutive zeros (`lzt_between`);
* comparisons at the ends `x = ±1`, where a sign of `W` forces `y/u` to diverge like
  `log(1∓x)` as soon as `(1-x²)u² = O(1∓x)` (`lzt_upper_right`, `lzt_lower_right`,
  `lzt_lower_left`, `lzt_lower_whole`), using `ODE.sturmCount_exists_pos_of_deriv_ge`;
* lower and upper zero counts from an exactly known comparison function (`lzt_lower_count`,
  `lzt_upper_count`).

The comparison functions are the polynomial cases
`𝖯^{-m}_{m+j}(x) = B (1-x²)^{m/2} C_j^{(m+1/2)}(x)` (`lzt_ferrersP_base`, from DLMF 14.3.1 and
Euler's transformation 15.8.1), whose zeros are those of the Gegenbauer polynomial
(`ultrasphPoly_zeros_Ioo`, DLMF 18.16(i)). Zeros of `𝖯^{-m}_ν` are simple by the Wronskians
14.2.3–14.2.4 (`lzt_ferrersP_simple`), and `𝖯^{-m}_ν` has no zeros near `1`
(`lzt_ferrersP_near_one`). The result is the exact count `max(⌈ν - m⌉, 0)` of zeros of
`𝖯^{-m}_ν`, `m ≥ 0`, `ν ≥ -1/2`, in `(-1, 1)` (`lzt_ferrersP_neg_order_zero_count`); no
continuity in the parameters is needed.

All helper names carry the prefix `lzt_`.
-/

@[expose] public noncomputable section

open Set Filter Topology

namespace DLMF.Legendre

/-- `y` (with derivative `y'`) solves `((1-x²) y')' + q y = 0` on `(-1, 1)`. -/
def lzt_IsSol (q y y' : ℝ → ℝ) : Prop :=
  ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt y (y' x) x ∧
    HasDerivAt (fun t => (1 - t ^ 2) * y' t) (-(q x * y x)) x

/-- The negative of a solution is a solution. -/
theorem lzt_IsSol.neg {q y y' : ℝ → ℝ} (h : lzt_IsSol q y y') :
    lzt_IsSol q (fun x => -y x) (fun x => -y' x) := fun x hx => by
  refine ⟨(h x hx).1.neg, ?_⟩
  have := (h x hx).2.neg
  convert this using 1
  · funext t; simp only [Pi.neg_apply]; ring
  · ring

/-- The weighted Wronskian `(1-x²)(u'y - uy')` of two solutions. -/
def lzt_W (u u' y y' : ℝ → ℝ) (x : ℝ) : ℝ := (1 - x ^ 2) * (u' x * y x - u x * y' x)

/-- Derivative of the weighted Wronskian: `W' = (qy - qu) u y`. -/
theorem lzt_hasDerivAt_W {qy qu y y' u u' : ℝ → ℝ} (hy : lzt_IsSol qy y y') (hu : lzt_IsSol qu u u')
    {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (lzt_W u u' y y') ((qy x - qu x) * u x * y x) x := by
  have h1 := (hu x hx).2.mul (hy x hx).1
  have h2 := (hu x hx).1.mul (hy x hx).2
  have := h1.sub h2
  convert this using 1
  · funext t; simp only [lzt_W, Pi.mul_apply, Pi.sub_apply]; ring
  · ring

/-- The weighted Wronskian is continuous on subsets of `(-1, 1)`. -/
theorem lzt_W_continuousOn {qy qu y y' u u' : ℝ → ℝ} (hy : lzt_IsSol qy y y')
    (hu : lzt_IsSol qu u u') {s : Set ℝ} (hs : s ⊆ Ioo (-1:ℝ) 1) :
    ContinuousOn (lzt_W u u' y y') s := fun _x hx =>
  (lzt_hasDerivAt_W hy hu (hs hx)).continuousAt.continuousWithinAt

/-- At a zero `a` followed by positive values, the derivative is nonnegative. -/
theorem lzt_deriv_nonneg_right {y : ℝ → ℝ} {d a b : ℝ} (hd : HasDerivAt y d a) (h0 : y a = 0)
    (hab : a < b) (hpos : ∀ x ∈ Ioo a b, 0 < y x) : 0 ≤ d := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsGT_le_nhdsNE a)
  refine ge_of_tendsto hs ?_
  filter_upwards [Ioo_mem_nhdsGT hab] with x hx
  rw [slope_def_field, h0, sub_zero]
  exact (div_pos (hpos x hx) (sub_pos.mpr hx.1)).le

/-- At a zero `b` preceded by positive values, the derivative is nonpositive. -/
theorem lzt_deriv_nonpos_left {y : ℝ → ℝ} {d a b : ℝ} (hd : HasDerivAt y d b) (h0 : y b = 0)
    (hab : a < b) (hpos : ∀ x ∈ Ioo a b, 0 < y x) : d ≤ 0 := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsLT_le_nhdsNE b)
  refine le_of_tendsto hs ?_
  filter_upwards [Ioo_mem_nhdsLT hab] with x hx
  rw [slope_def_field, h0, sub_zero]
  exact (div_neg_of_pos_of_neg (hpos x hx) (sub_neg.mpr hx.2)).le

/-- Nonnegativity at the left end by continuity. -/
theorem lzt_nonneg_left {u : ℝ → ℝ} {a b : ℝ} (hc : ContinuousAt u a) (hab : a < b)
    (hpos : ∀ x ∈ Ioo a b, 0 < u x) : 0 ≤ u a := by
  refine ge_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi a))) ?_
  filter_upwards [Ioo_mem_nhdsGT hab] with x hx using (hpos x hx).le

/-- Nonnegativity at the right end by continuity. -/
theorem lzt_nonneg_right {u : ℝ → ℝ} {a b : ℝ} (hc : ContinuousAt u b) (hab : a < b)
    (hpos : ∀ x ∈ Ioo a b, 0 < u x) : 0 ≤ u b := by
  refine ge_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio b))) ?_
  filter_upwards [Ioo_mem_nhdsLT hab] with x hx using (hpos x hx).le

/-- A continuous function without zeros on an interval has constant sign there. -/
theorem lzt_sign {f : ℝ → ℝ} {s : Set ℝ} (hs : s.OrdConnected) (hc : ContinuousOn f s)
    (hne : ∀ x ∈ s, f x ≠ 0) : (∀ x ∈ s, 0 < f x) ∨ (∀ x ∈ s, f x < 0) := by
  by_contra h
  push Not at h
  obtain ⟨⟨x₁, hx₁, h₁⟩, ⟨x₂, hx₂, h₂⟩⟩ := h
  have h₁' : f x₁ < 0 := lt_of_le_of_ne h₁ (hne x₁ hx₁)
  have h₂' : 0 < f x₂ := lt_of_le_of_ne h₂ (hne x₂ hx₂).symm
  rcases le_total x₁ x₂ with hle | hle
  · obtain ⟨c, hc', hc0⟩ := intermediate_value_Icc hle (hc.mono (hs.out hx₁ hx₂))
      ⟨h₁'.le, h₂'.le⟩
    exact hne c (hs.out hx₁ hx₂ hc') hc0
  · obtain ⟨c, hc', hc0⟩ := intermediate_value_Icc' hle (hc.mono (hs.out hx₂ hx₁))
      ⟨h₁'.le, h₂'.le⟩
    exact hne c (hs.out hx₂ hx₁ hc') hc0


/-- **Divergence of a ratio at the right end.** If `u > 0`, `(1-x²)u² ≤ K(1-x)` and the
weighted Wronskian satisfies `W ≤ -c₀ < 0` on `[s, 1)`, then `y/u` is unbounded above there. -/
theorem lzt_ratio_right {y y' u u' : ℝ → ℝ} {s K c₀ : ℝ} (hs : s < 1) (hK : 0 < K) (hc₀ : 0 < c₀)
    (hyd : ∀ x ∈ Ico s 1, HasDerivAt y (y' x) x) (hud : ∀ x ∈ Ico s 1, HasDerivAt u (u' x) x)
    (hup : ∀ x ∈ Ico s 1, 0 < u x) (hp : ∀ x ∈ Ico s 1, 0 < 1 - x ^ 2)
    (hb : ∀ x ∈ Ico s 1, (1 - x ^ 2) * u x ^ 2 ≤ K * (1 - x))
    (hW : ∀ x ∈ Ico s 1, lzt_W u u' y y' x ≤ -c₀) (C : ℝ) :
    ∃ x ∈ Ioo s 1, C < y x / u x := by
  have hge : ∀ x ∈ Ico s 1, c₀ / K / (1 - x) ≤ (y' x * u x - y x * u' x) / u x ^ 2 := by
    intro x hx
    have h1x : 0 < 1 - x := by linarith [hx.2]
    have hu2 : 0 < u x ^ 2 := pow_pos (hup x hx) 2
    have hWx := hW x hx
    simp only [lzt_W] at hWx
    set D := y' x * u x - y x * u' x
    have hD : c₀ ≤ (1 - x ^ 2) * D := by simp only [D]; linarith
    have hDp : 0 < D := by
      by_contra h; push Not at h; nlinarith [hp x hx]
    rw [div_div, div_le_div_iff₀ (mul_pos hK h1x) hu2]
    have := hb x hx
    nlinarith [mul_le_mul_of_nonneg_right hD hu2.le, mul_le_mul_of_nonneg_left this hDp.le]
  obtain ⟨x, hx, hpos⟩ := ODE.sturmCount_exists_pos_of_deriv_ge (r := fun x => y x / u x - C)
    (r' := fun x => (y' x * u x - y x * u' x) / u x ^ 2) (c := c₀ / K) hs (div_pos hc₀ hK)
    (fun x hx => ((hyd x hx).div (hud x hx) (hup x hx).ne').sub_const C) hge
  exact ⟨x, hx, by linarith⟩

/-- **Divergence of a ratio at the left end.** If `u > 0`, `(1-x²)u² ≤ K(1+x)` and `W ≤ -c₀ < 0`
on `(-1, s]`, then `y/u` takes negative values there. -/
theorem lzt_ratio_left {y y' u u' : ℝ → ℝ} {s K c₀ : ℝ} (hs : -1 < s) (hK : 0 < K) (hc₀ : 0 < c₀)
    (hyd : ∀ x ∈ Ioc (-1) s, HasDerivAt y (y' x) x) (hud : ∀ x ∈ Ioc (-1) s, HasDerivAt u (u' x) x)
    (hup : ∀ x ∈ Ioc (-1) s, 0 < u x) (hp : ∀ x ∈ Ioc (-1) s, 0 < 1 - x ^ 2)
    (hb : ∀ x ∈ Ioc (-1) s, (1 - x ^ 2) * u x ^ 2 ≤ K * (1 + x))
    (hW : ∀ x ∈ Ioc (-1) s, lzt_W u u' y y' x ≤ -c₀) :
    ∃ x ∈ Ioo (-1) s, y x / u x < 0 := by
  refine ODE.sturmCount_exists_neg_of_deriv_ge (r := fun x => y x / u x)
    (r' := fun x => (y' x * u x - y x * u' x) / u x ^ 2) (c := c₀ / K) hs (div_pos hc₀ hK)
    (fun x hx => (hyd x hx).div (hud x hx) (hup x hx).ne') (fun x hx => ?_)
  have h1x : 0 < x - -1 := by linarith [hx.1]
  have hu2 : 0 < u x ^ 2 := pow_pos (hup x hx) 2
  have hWx := hW x hx
  simp only [lzt_W] at hWx
  set D := y' x * u x - y x * u' x
  have hD : c₀ ≤ (1 - x ^ 2) * D := by simp only [D]; linarith
  have hDp : 0 < D := by
    by_contra h; push Not at h; nlinarith [hp x hx]
  rw [div_div, div_le_div_iff₀ (mul_pos hK h1x) hu2, show x - -1 = 1 + x by ring]
  have := hb x hx
  nlinarith [mul_le_mul_of_nonneg_right hD hu2.le, mul_le_mul_of_nonneg_left this hDp.le]


section Comparison

variable {qy qu y y' u u' : ℝ → ℝ}

/-- `1 - x² > 0` on `(-1, 1)`. -/
theorem lzt_p_pos {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) : 0 < 1 - x ^ 2 := by
  nlinarith [hx.1, hx.2]

/-- Solutions are continuous on subsets of `(-1, 1)`. -/
theorem lzt_IsSol.continuousOn {q y y' : ℝ → ℝ} (h : lzt_IsSol q y y') {s : Set ℝ}
    (hs : s ⊆ Ioo (-1:ℝ) 1) : ContinuousOn y s := fun _x hx =>
  (h _ (hs hx)).1.continuousAt.continuousWithinAt

/-- `W = (1-x²)(u'y-uy')` is strictly decreasing where `u, y > 0` and `qy < qu`. -/
theorem lzt_W_strictAntiOn (hy : lzt_IsSol qy y y') (hu : lzt_IsSol qu u u')
    (hq : ∀ x ∈ Ioo (-1:ℝ) 1, qy x < qu x) {s : Set ℝ} (hs : s ⊆ Ioo (-1:ℝ) 1) (hcv : Convex ℝ s)
    (hpos : ∀ x ∈ interior s, 0 < u x ∧ 0 < y x) : StrictAntiOn (lzt_W u u' y y') s := by
  refine strictAntiOn_of_deriv_neg hcv (lzt_W_continuousOn hy hu hs) fun x hx => ?_
  have hx' := hs (interior_subset hx)
  rw [(lzt_hasDerivAt_W hy hu hx').deriv]
  have := hq x hx'
  have h2 := mul_pos (hpos x hx).1 (hpos x hx).2
  nlinarith

/-- `W = (1-x²)(u'y-uy')` is strictly increasing where `u, y > 0` and `qu < qy`. -/
theorem lzt_W_strictMonoOn (hy : lzt_IsSol qy y y') (hu : lzt_IsSol qu u u')
    (hq : ∀ x ∈ Ioo (-1:ℝ) 1, qu x < qy x) {s : Set ℝ} (hs : s ⊆ Ioo (-1:ℝ) 1) (hcv : Convex ℝ s)
    (hpos : ∀ x ∈ interior s, 0 < u x ∧ 0 < y x) : StrictMonoOn (lzt_W u u' y y') s := by
  refine strictMonoOn_of_deriv_pos hcv (lzt_W_continuousOn hy hu hs) fun x hx => ?_
  have hx' := hs (interior_subset hx)
  rw [(lzt_hasDerivAt_W hy hu hx').deriv]
  have := hq x hx'
  have h2 := mul_pos (hpos x hx).1 (hpos x hx).2
  nlinarith

/-- Sign-normalized core of `lzt_between`. -/
theorem lzt_between_core (hy : lzt_IsSol qy y y') (hu : lzt_IsSol qu u u')
    (hq : ∀ x ∈ Ioo (-1:ℝ) 1, qy x < qu x) {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (ya : y a = 0) (yb : y b = 0) (ypos : ∀ x ∈ Ioo a b, 0 < y x)
    (upos : ∀ x ∈ Ioo a b, 0 < u x) : False := by
  have hsub : Icc a b ⊆ Ioo (-1:ℝ) 1 := Icc_subset_Ioo ha hb
  have hanti := lzt_W_strictAntiOn hy hu hq hsub (convex_Icc a b) fun x hx => by
    rw [interior_Icc] at hx; exact ⟨upos x hx, ypos x hx⟩
  have hWab := hanti (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hab
  have ha' := hsub (left_mem_Icc.2 hab.le)
  have hb' := hsub (right_mem_Icc.2 hab.le)
  have hua := lzt_nonneg_left (hu a ha').1.continuousAt hab upos
  have hub := lzt_nonneg_right (hu b hb').1.continuousAt hab upos
  have hya := lzt_deriv_nonneg_right (hy a ha').1 ya hab ypos
  have hyb := lzt_deriv_nonpos_left (hy b hb').1 yb hab ypos
  have pa := lzt_p_pos ha'
  have pb := lzt_p_pos hb'
  simp only [lzt_W, ya, yb, mul_zero, zero_sub] at hWab
  have h1 : 0 ≤ (1 - b ^ 2) * -(u b * y' b) := mul_nonneg pb.le (by nlinarith)
  have h2 : (1 - a ^ 2) * -(u a * y' a) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos pa.le (by nlinarith [mul_nonneg hua hya])
  linarith

/-- **Sturm comparison.** If `qy < qu`, then between two consecutive zeros of `y` the function
`u` has a zero. -/
theorem lzt_between (hy : lzt_IsSol qy y y') (hu : lzt_IsSol qu u u')
    (hq : ∀ x ∈ Ioo (-1:ℝ) 1, qy x < qu x) {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (ya : y a = 0) (yb : y b = 0) (hyne : ∀ x ∈ Ioo a b, y x ≠ 0) :
    ∃ c ∈ Ioo a b, u c = 0 := by
  by_contra hcon
  push Not at hcon
  have hsub : Ioo a b ⊆ Ioo (-1:ℝ) 1 := Ioo_subset_Ioo ha.le hb.le
  rcases lzt_sign ordConnected_Ioo (hy.continuousOn hsub) hyne with hy1 | hy1 <;>
  rcases lzt_sign ordConnected_Ioo (hu.continuousOn hsub) hcon with hu1 | hu1
  · exact lzt_between_core hy hu hq ha hb hab ya yb hy1 hu1
  · exact lzt_between_core hy hu.neg hq ha hb hab ya yb hy1 fun x hx => neg_pos.mpr (hu1 x hx)
  · exact lzt_between_core hy.neg hu hq ha hb hab (by simp [ya]) (by simp [yb])
      (fun x hx => neg_pos.mpr (hy1 x hx)) hu1
  · exact lzt_between_core hy.neg hu.neg hq ha hb hab (by simp [ya]) (by simp [yb])
      (fun x hx => neg_pos.mpr (hy1 x hx)) fun x hx => neg_pos.mpr (hu1 x hx)


/-- Sign-normalized core of `lzt_upper_right`. -/
theorem lzt_upper_right_core (hy : lzt_IsSol qy y y') (hu : lzt_IsSol qu u u')
    (hq : ∀ x ∈ Ioo (-1:ℝ) 1, qy x < qu x) {z s₀ C K : ℝ} (hz : z ∈ Ioo (-1:ℝ) 1) (hs₀ : s₀ < 1)
    (hK : 0 < K) (yz : y z = 0) (ypos : ∀ x ∈ Ioo z 1, 0 < y x) (upos : ∀ x ∈ Ioo z 1, 0 < u x)
    (hC : ∀ x ∈ Ioo s₀ 1, y x ≤ C * u x)
    (hb : ∀ x ∈ Ioo s₀ 1, (1 - x ^ 2) * u x ^ 2 ≤ K * (1 - x)) : False := by
  have hsub : Ico z 1 ⊆ Ioo (-1:ℝ) 1 := fun x hx => ⟨by linarith [hz.1, hx.1], hx.2⟩
  have hanti := lzt_W_strictAntiOn hy hu hq hsub (convex_Ico z 1) fun x hx => by
    rw [interior_Ico] at hx; exact ⟨upos x hx, ypos x hx⟩
  have hWz : lzt_W u u' y y' z ≤ 0 := by
    have hua := lzt_nonneg_left (hu z hz).1.continuousAt hz.2 upos
    have hya := lzt_deriv_nonneg_right (hy z hz).1 yz hz.2 ypos
    simp only [lzt_W, yz, mul_zero, zero_sub]
    exact mul_nonpos_of_nonneg_of_nonpos (lzt_p_pos hz).le (by nlinarith [mul_nonneg hua hya])
  set s₁ := (max z s₀ + 1) / 2 with hs₁
  have hm : max z s₀ < 1 := max_lt hz.2 hs₀
  have hzs : z < s₁ := by have := le_max_left z s₀; linarith
  have hs0s : s₀ < s₁ := by have := le_max_right z s₀; linarith
  have hs1 : s₁ < 1 := by linarith
  have hW1 : lzt_W u u' y y' s₁ < lzt_W u u' y y' z :=
    hanti ⟨le_rfl, hz.2⟩ ⟨hzs.le, hs1⟩ hzs
  have hIco : ∀ x ∈ Ico s₁ 1, x ∈ Ioo z 1 := fun x hx => ⟨by linarith [hx.1], hx.2⟩
  obtain ⟨x, hx, hxC⟩ := lzt_ratio_right (y := y) (u := u) (c₀ := -lzt_W u u' y y' s₁) hs1 hK
    (by linarith) (fun x hx => (hy x (hsub (Ico_subset_Ico_left hzs.le hx))).1)
    (fun x hx => (hu x (hsub (Ico_subset_Ico_left hzs.le hx))).1)
    (fun x hx => upos x (hIco x hx)) (fun x hx => lzt_p_pos (hsub (Ico_subset_Ico_left hzs.le hx)))
    (fun x hx => hb x ⟨by linarith [hx.1], hx.2⟩)
    (fun x hx => by
      have := hanti.antitoneOn ⟨hzs.le, hs1⟩ (Ico_subset_Ico_left hzs.le hx) hx.1
      linarith) C
  have hx' : x ∈ Ioo z 1 := ⟨by linarith [hx.1], hx.2⟩
  have := hC x ⟨by linarith [hx.1], hx.2⟩
  rw [lt_div_iff₀ (upos x hx')] at hxC
  linarith

/-- **Comparison at the right end.** Let `qy < qu`, let `z` be the last zero of `y`, and let
`y/u` stay bounded and `(1-x²)u² = O(1-x)` near `1`. Then `u` has a zero in `(z, 1)`. -/
theorem lzt_upper_right (hy : lzt_IsSol qy y y') (hu : lzt_IsSol qu u u')
    (hq : ∀ x ∈ Ioo (-1:ℝ) 1, qy x < qu x) {z s₀ C K : ℝ} (hz : z ∈ Ioo (-1:ℝ) 1) (hs₀ : s₀ < 1)
    (hK : 0 < K) (yz : y z = 0) (hyne : ∀ x ∈ Ioo z 1, y x ≠ 0)
    (hC : ∀ x ∈ Ioo s₀ 1, |y x| ≤ C * |u x|)
    (hb : ∀ x ∈ Ioo s₀ 1, (1 - x ^ 2) * u x ^ 2 ≤ K * (1 - x)) : ∃ c ∈ Ioo z 1, u c = 0 := by
  by_contra hcon
  push Not at hcon
  have hsub : Ioo z 1 ⊆ Ioo (-1:ℝ) 1 := Ioo_subset_Ioo hz.1.le le_rfl
  have hb' : ∀ x ∈ Ioo s₀ 1, (1 - x ^ 2) * (-u x) ^ 2 ≤ K * (1 - x) := fun x hx => by
    rw [neg_sq]; exact hb x hx
  have key : ∀ (y₁ y₁' u₁ u₁' : ℝ → ℝ), lzt_IsSol qy y₁ y₁' → lzt_IsSol qu u₁ u₁' → y₁ z = 0 →
      (∀ x ∈ Ioo z 1, 0 < y₁ x) → (∀ x ∈ Ioo z 1, 0 < u₁ x) →
      (∀ x ∈ Ioo s₀ 1, |y₁ x| ≤ C * |u₁ x|) →
      (∀ x ∈ Ioo s₀ 1, (1 - x ^ 2) * u₁ x ^ 2 ≤ K * (1 - x)) → False := by
    intro y₁ y₁' u₁ u₁' h1 h2 h3 h4 h5 h6 h7
    refine lzt_upper_right_core (C := C) h1 h2 hq hz (max_lt hz.2 hs₀) hK h3 h4 h5 (fun x hx => ?_)
      (fun x hx => h7 x ⟨lt_of_le_of_lt (le_max_right _ _) hx.1, hx.2⟩)
    have hxz : x ∈ Ioo z 1 := ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, hx.2⟩
    have := h6 x ⟨lt_of_le_of_lt (le_max_right _ _) hx.1, hx.2⟩
    rwa [abs_of_pos (h4 x hxz), abs_of_pos (h5 x hxz)] at this
  have hCn1 : ∀ x ∈ Ioo s₀ 1, |-y x| ≤ C * |u x| := fun x hx => by
    rw [abs_neg]; exact hC x hx
  have hCn2 : ∀ x ∈ Ioo s₀ 1, |y x| ≤ C * |-u x| := fun x hx => by
    rw [abs_neg]; exact hC x hx
  have hCn3 : ∀ x ∈ Ioo s₀ 1, |-y x| ≤ C * |-u x| := fun x hx => by
    rw [abs_neg, abs_neg]; exact hC x hx
  rcases lzt_sign ordConnected_Ioo (hy.continuousOn hsub) hyne with hy1 | hy1 <;>
  rcases lzt_sign ordConnected_Ioo (hu.continuousOn hsub) hcon with hu1 | hu1
  · exact key _ _ _ _ hy hu yz hy1 hu1 hC hb
  · exact key _ _ _ _ hy hu.neg yz hy1 (fun x hx => neg_pos.mpr (hu1 x hx)) hCn2 hb'
  · exact key _ _ _ _ hy.neg hu (by simp [yz]) (fun x hx => neg_pos.mpr (hy1 x hx)) hu1 hCn1 hb
  · exact key _ _ _ _ hy.neg hu.neg (by simp [yz]) (fun x hx => neg_pos.mpr (hy1 x hx))
      (fun x hx => neg_pos.mpr (hu1 x hx)) hCn3 hb'


/-- The weighted Wronskian is odd in `y`. -/
theorem lzt_W_neg (u u' y y' : ℝ → ℝ) (x : ℝ) :
    lzt_W u u' (fun x => -y x) (fun x => -y' x) x = -lzt_W u u' y y' x := by
  simp only [lzt_W]; ring

variable {qw w w' : ℝ → ℝ}

/-- Sign-normalized core of `lzt_lower_right`. -/
theorem lzt_lower_right_core (hy : lzt_IsSol qy y y') (hw : lzt_IsSol qw w w')
    (hq : ∀ x ∈ Ioo (-1:ℝ) 1, qw x < qy x) {z s₀ K : ℝ} (hz : z ∈ Ioo (-1:ℝ) 1) (hs₀ : s₀ < 1)
    (hK : 0 < K) (wz : w z = 0) (ypos : ∀ x ∈ Ioo z 1, 0 < y x) (wpos : ∀ x ∈ Ioo z 1, 0 < w x)
    (hb : ∀ x ∈ Ioo s₀ 1, (1 - x ^ 2) * w x ^ 2 ≤ K * (1 - x)) : False := by
  have hsub : Ico z 1 ⊆ Ioo (-1:ℝ) 1 := fun x hx => ⟨by linarith [hz.1, hx.1], hx.2⟩
  have hmono := lzt_W_strictMonoOn hy hw hq hsub (convex_Ico z 1) fun x hx => by
    rw [interior_Ico] at hx; exact ⟨wpos x hx, ypos x hx⟩
  have hWz : 0 ≤ lzt_W w w' y y' z := by
    have hya := lzt_nonneg_left (hy z hz).1.continuousAt hz.2 ypos
    have hwa := lzt_deriv_nonneg_right (hw z hz).1 wz hz.2 wpos
    simp only [lzt_W, wz, zero_mul, sub_zero]
    exact mul_nonneg (lzt_p_pos hz).le (mul_nonneg hwa hya)
  set s₁ := (max z s₀ + 1) / 2 with hs₁
  have hm : max z s₀ < 1 := max_lt hz.2 hs₀
  have hzs : z < s₁ := by have := le_max_left z s₀; linarith
  have hs0s : s₀ < s₁ := by have := le_max_right z s₀; linarith
  have hs1 : s₁ < 1 := by linarith
  have hW1 : lzt_W w w' y y' z < lzt_W w w' y y' s₁ := hmono ⟨le_rfl, hz.2⟩ ⟨hzs.le, hs1⟩ hzs
  have hIco : ∀ x ∈ Ico s₁ 1, x ∈ Ioo z 1 := fun x hx => ⟨by linarith [hx.1], hx.2⟩
  obtain ⟨x, hx, hxC⟩ := lzt_ratio_right (y := fun x => -y x) (y' := fun x => -y' x) (u := w)
    (c₀ := lzt_W w w' y y' s₁) hs1 hK (by linarith)
    (fun x hx => (hy x (hsub (Ico_subset_Ico_left hzs.le hx))).1.neg)
    (fun x hx => (hw x (hsub (Ico_subset_Ico_left hzs.le hx))).1)
    (fun x hx => wpos x (hIco x hx)) (fun x hx => lzt_p_pos (hsub (Ico_subset_Ico_left hzs.le hx)))
    (fun x hx => hb x ⟨by linarith [hx.1], hx.2⟩)
    (fun x hx => by
      rw [lzt_W_neg]
      have := hmono.monotoneOn ⟨hzs.le, hs1⟩ (Ico_subset_Ico_left hzs.le hx) hx.1
      linarith) 0
  have hx' : x ∈ Ioo z 1 := ⟨by linarith [hx.1], hx.2⟩
  rw [neg_div, lt_neg, neg_zero] at hxC
  exact absurd hxC (not_lt.mpr (div_pos (ypos x hx') (wpos x hx')).le)

/-- Sign-normalized core of `lzt_lower_left`. -/
theorem lzt_lower_left_core (hy : lzt_IsSol qy y y') (hw : lzt_IsSol qw w w')
    (hq : ∀ x ∈ Ioo (-1:ℝ) 1, qw x < qy x) {z s₀ K : ℝ} (hz : z ∈ Ioo (-1:ℝ) 1) (hs₀ : -1 < s₀)
    (hK : 0 < K) (wz : w z = 0) (ypos : ∀ x ∈ Ioo (-1) z, 0 < y x)
    (wpos : ∀ x ∈ Ioo (-1) z, 0 < w x)
    (hb : ∀ x ∈ Ioo (-1) s₀, (1 - x ^ 2) * w x ^ 2 ≤ K * (1 + x)) : False := by
  have hsub : Ioc (-1) z ⊆ Ioo (-1:ℝ) 1 := fun x hx => ⟨hx.1, by linarith [hz.2, hx.2]⟩
  have hmono := lzt_W_strictMonoOn hy hw hq hsub (convex_Ioc (-1) z) fun x hx => by
    rw [interior_Ioc] at hx; exact ⟨wpos x hx, ypos x hx⟩
  have hWz : lzt_W w w' y y' z ≤ 0 := by
    have hya := lzt_nonneg_right (hy z hz).1.continuousAt hz.1 ypos
    have hwa := lzt_deriv_nonpos_left (hw z hz).1 wz hz.1 wpos
    simp only [lzt_W, wz, zero_mul, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (lzt_p_pos hz).le (by nlinarith [mul_nonneg hya (neg_nonneg.mpr hwa)])
  set s₁ := (-1 + min z s₀) / 2 with hs₁
  have hm : -1 < min z s₀ := lt_min hz.1 hs₀
  have hzs : s₁ < z := by have := min_le_left z s₀; linarith
  have hs0s : s₁ < s₀ := by have := min_le_right z s₀; linarith
  have hs1 : -1 < s₁ := by linarith
  have hW1 : lzt_W w w' y y' s₁ < lzt_W w w' y y' z := hmono ⟨hs1, hzs.le⟩ ⟨hz.1, le_rfl⟩ hzs
  have hIoc : ∀ x ∈ Ioc (-1) s₁, x ∈ Ioc (-1) z := fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  obtain ⟨x, hx, hxC⟩ := lzt_ratio_left (y := y) (u := w)
    (c₀ := -lzt_W w w' y y' s₁) hs1 hK (by linarith)
    (fun x hx => (hy x (hsub (hIoc x hx))).1) (fun x hx => (hw x (hsub (hIoc x hx))).1)
    (fun x hx => wpos x ⟨hx.1, by linarith [hx.2]⟩) (fun x hx => lzt_p_pos (hsub (hIoc x hx)))
    (fun x hx => hb x ⟨hx.1, by linarith [hx.2]⟩)
    (fun x hx => by
      have := hmono.monotoneOn (hIoc x hx) ⟨hs1, hzs.le⟩ hx.2
      linarith)
  have hx' : x ∈ Ioo (-1) z := ⟨hx.1, by linarith [hx.2]⟩
  exact absurd hxC (not_lt.mpr (div_pos (ypos x hx') (wpos x hx')).le)

/-- Sign-normalized core of `lzt_lower_whole`. -/
theorem lzt_lower_whole_core (hy : lzt_IsSol qy y y') (hw : lzt_IsSol qw w w')
    (hq : ∀ x ∈ Ioo (-1:ℝ) 1, qw x < qy x) {s₀ s₀' K : ℝ} (hs₀ : s₀ < 1) (hs₀' : -1 < s₀')
    (hK : 0 < K) (ypos : ∀ x ∈ Ioo (-1) 1, 0 < y x) (wpos : ∀ x ∈ Ioo (-1) 1, 0 < w x)
    (hb : ∀ x ∈ Ioo s₀ 1, (1 - x ^ 2) * w x ^ 2 ≤ K * (1 - x))
    (hb' : ∀ x ∈ Ioo (-1) s₀', (1 - x ^ 2) * w x ^ 2 ≤ K * (1 + x)) : False := by
  have hmono := lzt_W_strictMonoOn hy hw hq subset_rfl (convex_Ioo (-1) 1) fun x hx => by
    rw [interior_Ioo] at hx; exact ⟨wpos x hx, ypos x hx⟩
  have h0 : (0:ℝ) ∈ Ioo (-1:ℝ) 1 := ⟨by norm_num, by norm_num⟩
  by_cases hW0 : 0 ≤ lzt_W w w' y y' 0
  · set s₁ := (max 0 s₀ + 1) / 2 with hs₁
    have hm : max 0 s₀ < 1 := max_lt (by norm_num) hs₀
    have hzs : 0 < s₁ := by have := le_max_left 0 s₀; linarith
    have hs0s : s₀ < s₁ := by have := le_max_right 0 s₀; linarith
    have hs1 : s₁ < 1 := by linarith
    have hS : ∀ x ∈ Ico s₁ 1, x ∈ Ioo (-1:ℝ) 1 := fun x hx => ⟨by linarith [hx.1], hx.2⟩
    have hW1 : lzt_W w w' y y' 0 < lzt_W w w' y y' s₁ := hmono h0 (hS s₁ ⟨le_rfl, hs1⟩) hzs
    obtain ⟨x, hx, hxC⟩ := lzt_ratio_right (y := fun x => -y x) (y' := fun x => -y' x) (u := w)
      (c₀ := lzt_W w w' y y' s₁) hs1 hK (by linarith) (fun x hx => (hy x (hS x hx)).1.neg)
      (fun x hx => (hw x (hS x hx)).1) (fun x hx => wpos x (hS x hx))
      (fun x hx => lzt_p_pos (hS x hx)) (fun x hx => hb x ⟨by linarith [hx.1], hx.2⟩)
      (fun x hx => by
        rw [lzt_W_neg]
        have := hmono.monotoneOn (hS s₁ ⟨le_rfl, hs1⟩) (hS x hx) hx.1
        linarith) 0
    have hx' := hS x (Ioo_subset_Ico_self hx)
    rw [neg_div, lt_neg, neg_zero] at hxC
    exact absurd hxC (not_lt.mpr (div_pos (ypos x hx') (wpos x hx')).le)
  · push Not at hW0
    set s₁ := (-1 + min 0 s₀') / 2 with hs₁
    have hm : -1 < min 0 s₀' := lt_min (by norm_num) hs₀'
    have hzs : s₁ < 0 := by have := min_le_left 0 s₀'; linarith
    have hs0s : s₁ < s₀' := by have := min_le_right 0 s₀'; linarith
    have hs1 : -1 < s₁ := by linarith
    have hS : ∀ x ∈ Ioc (-1) s₁, x ∈ Ioo (-1:ℝ) 1 := fun x hx => ⟨hx.1, by linarith [hx.2]⟩
    have hW1 : lzt_W w w' y y' s₁ < lzt_W w w' y y' 0 := hmono (hS s₁ ⟨hs1, le_rfl⟩) h0 hzs
    obtain ⟨x, hx, hxC⟩ := lzt_ratio_left (y := y) (u := w)
      (c₀ := -lzt_W w w' y y' s₁) hs1 hK (by linarith)
      (fun x hx => (hy x (hS x hx)).1) (fun x hx => (hw x (hS x hx)).1)
      (fun x hx => wpos x (hS x hx)) (fun x hx => lzt_p_pos (hS x hx))
      (fun x hx => hb' x ⟨hx.1, by linarith [hx.2]⟩)
      (fun x hx => by
        have := hmono.monotoneOn (hS x hx) (hS s₁ ⟨hs1, le_rfl⟩) hx.2
        linarith)
    have hx' := hS x (Ioo_subset_Ioc_self hx)
    exact absurd hxC (not_lt.mpr (div_pos (ypos x hx') (wpos x hx')).le)


/-- Bounds on `(1-x²)w²` are unchanged by `w ↦ -w`. -/
theorem lzt_neg_sq_bound {w : ℝ → ℝ} {S : Set ℝ} {g : ℝ → ℝ}
    (hb : ∀ x ∈ S, (1 - x ^ 2) * w x ^ 2 ≤ g x) : ∀ x ∈ S, (1 - x ^ 2) * (-w x) ^ 2 ≤ g x :=
  fun x hx => by rw [neg_sq]; exact hb x hx

/-- **Comparison at the right end (lower function).** Let `qw < qy`, let `z` be the last zero of
`w`, and let `(1-x²)w² = O(1-x)` near `1`. Then `y` has a zero in `(z, 1)`. -/
theorem lzt_lower_right (hy : lzt_IsSol qy y y') (hw : lzt_IsSol qw w w')
    (hq : ∀ x ∈ Ioo (-1:ℝ) 1, qw x < qy x) {z s₀ K : ℝ} (hz : z ∈ Ioo (-1:ℝ) 1) (hs₀ : s₀ < 1)
    (hK : 0 < K) (wz : w z = 0) (hwne : ∀ x ∈ Ioo z 1, w x ≠ 0)
    (hb : ∀ x ∈ Ioo s₀ 1, (1 - x ^ 2) * w x ^ 2 ≤ K * (1 - x)) : ∃ c ∈ Ioo z 1, y c = 0 := by
  by_contra hcon
  push Not at hcon
  have hsub : Ioo z 1 ⊆ Ioo (-1:ℝ) 1 := Ioo_subset_Ioo hz.1.le le_rfl
  have wz' : (fun x => -w x) z = 0 := by simp [wz]
  rcases lzt_sign ordConnected_Ioo (hy.continuousOn hsub) hcon with hy1 | hy1 <;>
  rcases lzt_sign ordConnected_Ioo (hw.continuousOn hsub) hwne with hu1 | hu1
  · exact lzt_lower_right_core hy hw hq hz hs₀ hK wz hy1 hu1 hb
  · exact lzt_lower_right_core hy hw.neg hq hz hs₀ hK wz' hy1 (fun x hx => neg_pos.mpr (hu1 x hx))
      (lzt_neg_sq_bound hb)
  · exact lzt_lower_right_core hy.neg hw hq hz hs₀ hK wz (fun x hx => neg_pos.mpr (hy1 x hx)) hu1 hb
  · exact lzt_lower_right_core hy.neg hw.neg hq hz hs₀ hK wz' (fun x hx => neg_pos.mpr (hy1 x hx))
      (fun x hx => neg_pos.mpr (hu1 x hx)) (lzt_neg_sq_bound hb)

/-- **Comparison at the left end (lower function).** Let `qw < qy`, let `z` be the first zero of
`w`, and let `(1-x²)w² = O(1+x)` near `-1`. Then `y` has a zero in `(-1, z)`. -/
theorem lzt_lower_left (hy : lzt_IsSol qy y y') (hw : lzt_IsSol qw w w')
    (hq : ∀ x ∈ Ioo (-1:ℝ) 1, qw x < qy x) {z s₀ K : ℝ} (hz : z ∈ Ioo (-1:ℝ) 1) (hs₀ : -1 < s₀)
    (hK : 0 < K) (wz : w z = 0) (hwne : ∀ x ∈ Ioo (-1) z, w x ≠ 0)
    (hb : ∀ x ∈ Ioo (-1) s₀, (1 - x ^ 2) * w x ^ 2 ≤ K * (1 + x)) :
    ∃ c ∈ Ioo (-1) z, y c = 0 := by
  by_contra hcon
  push Not at hcon
  have hsub : Ioo (-1) z ⊆ Ioo (-1:ℝ) 1 := Ioo_subset_Ioo le_rfl hz.2.le
  have wz' : (fun x => -w x) z = 0 := by simp [wz]
  rcases lzt_sign ordConnected_Ioo (hy.continuousOn hsub) hcon with hy1 | hy1 <;>
  rcases lzt_sign ordConnected_Ioo (hw.continuousOn hsub) hwne with hu1 | hu1
  · exact lzt_lower_left_core hy hw hq hz hs₀ hK wz hy1 hu1 hb
  · exact lzt_lower_left_core hy hw.neg hq hz hs₀ hK wz' hy1 (fun x hx => neg_pos.mpr (hu1 x hx))
      (lzt_neg_sq_bound hb)
  · exact lzt_lower_left_core hy.neg hw hq hz hs₀ hK wz (fun x hx => neg_pos.mpr (hy1 x hx)) hu1 hb
  · exact lzt_lower_left_core hy.neg hw.neg hq hz hs₀ hK wz' (fun x hx => neg_pos.mpr (hy1 x hx))
      (fun x hx => neg_pos.mpr (hu1 x hx)) (lzt_neg_sq_bound hb)

/-- **Comparison on the whole interval.** Let `qw < qy`, let `w` have no zeros in `(-1, 1)` and
`(1-x²)w² = O(1∓x)` near `±1`. Then `y` has a zero in `(-1, 1)`. -/
theorem lzt_lower_whole (hy : lzt_IsSol qy y y') (hw : lzt_IsSol qw w w')
    (hq : ∀ x ∈ Ioo (-1:ℝ) 1, qw x < qy x) {s₀ s₀' K : ℝ} (hs₀ : s₀ < 1) (hs₀' : -1 < s₀')
    (hK : 0 < K) (hwne : ∀ x ∈ Ioo (-1) 1, w x ≠ 0)
    (hb : ∀ x ∈ Ioo s₀ 1, (1 - x ^ 2) * w x ^ 2 ≤ K * (1 - x))
    (hb' : ∀ x ∈ Ioo (-1) s₀', (1 - x ^ 2) * w x ^ 2 ≤ K * (1 + x)) :
    ∃ c ∈ Ioo (-1) 1, y c = 0 := by
  by_contra hcon
  push Not at hcon
  rcases lzt_sign ordConnected_Ioo (hy.continuousOn subset_rfl) hcon with hy1 | hy1 <;>
  rcases lzt_sign ordConnected_Ioo (hw.continuousOn subset_rfl) hwne with hu1 | hu1
  · exact lzt_lower_whole_core hy hw hq hs₀ hs₀' hK hy1 hu1 hb hb'
  · exact lzt_lower_whole_core hy hw.neg hq hs₀ hs₀' hK hy1 (fun x hx => neg_pos.mpr (hu1 x hx))
      (lzt_neg_sq_bound hb) (lzt_neg_sq_bound hb')
  · exact lzt_lower_whole_core hy.neg hw hq hs₀ hs₀' hK (fun x hx => neg_pos.mpr (hy1 x hx)) hu1
      hb hb'
  · exact lzt_lower_whole_core hy.neg hw.neg hq hs₀ hs₀' hK (fun x hx => neg_pos.mpr (hy1 x hx))
      (fun x hx => neg_pos.mpr (hu1 x hx)) (lzt_neg_sq_bound hb) (lzt_neg_sq_bound hb')


/-- **Lower zero count by comparison.** If `qw < qy` and the zeros of `w` in `(-1, 1)` are
exactly `e₀ < ⋯ < e_{j-1}`, with `(1-x²)w² = O(1∓x)` at `±1`, then `y` has `j+1` distinct zeros,
one in each gap. -/
theorem lzt_lower_count (hy : lzt_IsSol qy y y') (hw : lzt_IsSol qw w w')
    (hq : ∀ x ∈ Ioo (-1:ℝ) 1, qw x < qy x) {j : ℕ} {e : Fin j → ℝ} (he : StrictMono e)
    (heI : ∀ i, e i ∈ Ioo (-1:ℝ) 1) (hwz : ∀ x ∈ Ioo (-1:ℝ) 1, w x = 0 ↔ ∃ i, x = e i)
    {s₀ s₀' K : ℝ} (hs₀ : s₀ < 1) (hs₀' : -1 < s₀') (hK : 0 < K)
    (hb : ∀ x ∈ Ioo s₀ 1, (1 - x ^ 2) * w x ^ 2 ≤ K * (1 - x))
    (hb' : ∀ x ∈ Ioo (-1) s₀', (1 - x ^ 2) * w x ^ 2 ≤ K * (1 + x)) :
    ∃ c : Fin (j + 1) → ℝ, StrictMono c ∧ ∀ i, c i ∈ Ioo (-1:ℝ) 1 ∧ y (c i) = 0 := by
  let lo : Fin (j + 1) → ℝ := fun i => if h : i.val = 0 then -1 else e ⟨i.val - 1, by omega⟩
  let hi : Fin (j + 1) → ℝ := fun i => if h : i.val = j then 1 else e ⟨i.val, by omega⟩
  have hgap : ∀ i : Fin (j + 1), ∃ c ∈ Ioo (lo i) (hi i), y c = 0 := by
    intro i
    have hne : ∀ x ∈ Ioo (lo i) (hi i), x ∈ Ioo (-1:ℝ) 1 → w x ≠ 0 := by
      intro x hx hxI h0
      obtain ⟨k, rfl⟩ := (hwz x hxI).1 h0
      have h1 : i.val ≠ 0 → i.val - 1 < k.val := fun h => by
        have := hx.1; simp only [lo, h, ↓reduceDIte] at this
        exact he.lt_iff_lt.1 this
      have h2 : i.val ≠ j → k.val < i.val := fun h => by
        have := hx.2; simp only [hi, h, ↓reduceDIte] at this
        exact he.lt_iff_lt.1 this
      have := k.isLt
      have := i.isLt
      by_cases a : i.val = 0 <;> by_cases b : i.val = j
      · omega
      · have := h2 b; omega
      · have := h1 a; omega
      · have := h1 a; have := h2 b; omega
    by_cases a : i.val = 0 <;> by_cases b : i.val = j
    · have hl : lo i = -1 := dite_eq_left a
      have hh : hi i = 1 := dite_eq_left b
      rw [hl, hh] at hne ⊢
      exact lzt_lower_whole hy hw hq hs₀ hs₀' hK (fun x hx => hne x hx hx) hb hb'
    · have hl : lo i = -1 := dite_eq_left a
      have hh : hi i = e ⟨i.val, by omega⟩ := dite_eq_right b
      have hz := heI ⟨i.val, by omega⟩
      rw [hl, hh] at hne ⊢
      exact lzt_lower_left hy hw hq hz hs₀' hK ((hwz _ hz).2 ⟨_, rfl⟩)
        (fun x hx => hne x hx ⟨hx.1, hx.2.trans hz.2⟩) hb'
    · have hl : lo i = e ⟨i.val - 1, by omega⟩ := dite_eq_right a
      have hh : hi i = 1 := dite_eq_left b
      have hz := heI ⟨i.val - 1, by omega⟩
      rw [hl, hh] at hne ⊢
      exact lzt_lower_right hy hw hq hz hs₀ hK ((hwz _ hz).2 ⟨_, rfl⟩)
        (fun x hx => hne x hx ⟨hz.1.trans hx.1, hx.2⟩) hb
    · have hl : lo i = e ⟨i.val - 1, by omega⟩ := dite_eq_right a
      have hh : hi i = e ⟨i.val, by omega⟩ := dite_eq_right b
      have hz1 := heI ⟨i.val - 1, by omega⟩
      have hz2 := heI ⟨i.val, by omega⟩
      have hlt : e ⟨i.val - 1, by omega⟩ < e ⟨i.val, by omega⟩ :=
        he (Fin.mk_lt_mk.2 (by omega))
      rw [hl, hh] at hne ⊢
      exact lzt_between hw hy hq hz1.1 hz2.2 hlt ((hwz _ hz1).2 ⟨_, rfl⟩)
        ((hwz _ hz2).2 ⟨_, rfl⟩) fun x hx => hne x hx ⟨hz1.1.trans hx.1, hx.2.trans hz2.2⟩
  choose c hc hc0 using hgap
  have hlo : ∀ i, -1 ≤ lo i := fun i => by
    simp only [lo]; split_ifs
    · exact le_rfl
    · exact (heI _).1.le
  have hhi : ∀ i, hi i ≤ 1 := fun i => by
    simp only [hi]; split_ifs
    · exact le_rfl
    · exact (heI _).2.le
  refine ⟨c, fun i₁ i₂ h12 => ?_, fun i => ⟨⟨(hlo i).trans_lt (hc i).1, (hc i).2.trans_le (hhi i)⟩,
    hc0 i⟩⟩
  have h12' : i₁.val < i₂.val := h12
  have : hi i₁ ≤ lo i₂ := by
    have a : i₁.val ≠ j := by have := i₂.isLt; omega
    have b : i₂.val ≠ 0 := by omega
    rw [show hi i₁ = e ⟨i₁.val, by omega⟩ from dite_eq_right a,
      show lo i₂ = e ⟨i₂.val - 1, by omega⟩ from dite_eq_right b]
    exact he.monotone (Fin.mk_le_mk.2 (by omega))
  linarith [(hc i₁).2, (hc i₂).1]


/-- **Upper zero count by comparison.** If `qy < qu`, the zeros of `u` in `(-1, 1)` are among
`e₀, …, e_{k-1}`, the zeros of `y` are simple and stay away from `1`, `y/u` is bounded and
`(1-x²)u² = O(1-x)` near `1`, then `y` has at most `k` zeros in `(-1, 1)`. -/
theorem lzt_upper_count (hy : lzt_IsSol qy y y') (hu : lzt_IsSol qu u u')
    (hq : ∀ x ∈ Ioo (-1:ℝ) 1, qy x < qu x) {k : ℕ} {e : Fin k → ℝ}
    (huz : ∀ x ∈ Ioo (-1:ℝ) 1, u x = 0 → ∃ i, x = e i)
    (hsimple : ∀ x ∈ Ioo (-1:ℝ) 1, y x = 0 → y' x ≠ 0) {δ : ℝ} (hδ : δ < 1)
    (hnear : ∀ x ∈ Ioo δ 1, y x ≠ 0) {s₀ C K : ℝ} (hs₀ : s₀ < 1) (hK : 0 < K)
    (hC : ∀ x ∈ Ioo s₀ 1, |y x| ≤ C * |u x|)
    (hb : ∀ x ∈ Ioo s₀ 1, (1 - x ^ 2) * u x ^ 2 ≤ K * (1 - x)) :
    {x | x ∈ Ioo (-1:ℝ) 1 ∧ y x = 0}.Finite ∧ {x | x ∈ Ioo (-1:ℝ) 1 ∧ y x = 0}.ncard ≤ k := by
  set Z := {x | x ∈ Ioo (-1:ℝ) 1 ∧ y x = 0} with hZ
  have claim : ∀ T : Finset ℝ, (↑T : Set ℝ) ⊆ Z → T.card ≤ k := by
    intro T hT
    by_contra hlt
    push Not at hlt
    set n := T.card with hn
    let f := T.orderEmbOfFin hn.symm
    have hfZ : ∀ i, f i ∈ Z := fun i => hT (T.orderEmbOfFin_mem hn.symm i)
    let hi : Fin n → ℝ := fun i => if h : i.val + 1 < n then f ⟨i.val + 1, h⟩ else 1
    have hgap : ∀ i, ∃ c ∈ Ioo (f i) (hi i), u c = 0 := by
      intro i
      have ha := hfZ i
      by_cases h : i.val + 1 < n
      · rw [show hi i = f ⟨i.val + 1, h⟩ from dite_eq_left h]
        have hb' := hfZ ⟨i.val + 1, h⟩
        have hab : f i < f ⟨i.val + 1, h⟩ := f.strictMono (Fin.mk_lt_mk.2 (by omega))
        have hsub : Icc (f i) (f ⟨i.val + 1, h⟩) ⊆ Ioo (-1:ℝ) 1 := Icc_subset_Ioo ha.1.1 hb'.1.2
        have hfin := ODE.sturmDef_finite (f' := y') (fun x hx => (hy x (hsub hx)).1)
          (fun x hx h0 => hsimple x (hsub hx) h0)
        set S := {x | x ∈ Ioc (f i) (f ⟨i.val + 1, h⟩) ∧ y x = 0} with hS
        have hSfin : S.Finite := hfin.subset fun x hx => ⟨Ioc_subset_Icc_self hx.1, hx.2⟩
        have hSne : hSfin.toFinset.Nonempty :=
          (Set.Finite.toFinset_nonempty hSfin).2 ⟨_, ⟨⟨hab, le_rfl⟩, hb'.2⟩⟩
        have hzS : hSfin.toFinset.min' hSne ∈ S := hSfin.mem_toFinset.1 (Finset.min'_mem _ _)
        have hmin : ∀ x ∈ S, hSfin.toFinset.min' hSne ≤ x := fun x hx =>
          Finset.min'_le _ _ (hSfin.mem_toFinset.2 hx)
        obtain ⟨c, hc, hc0⟩ := lzt_between hy hu hq ha.1.1 (hzS.1.2.trans_lt hb'.1.2) hzS.1.1
          ha.2 hzS.2 fun x hx h0 => by
            have := hmin x ⟨⟨hx.1, hx.2.le.trans hzS.1.2⟩, h0⟩
            linarith [hx.2]
        exact ⟨c, ⟨hc.1, hc.2.trans_le hzS.1.2⟩, hc0⟩
      · rw [show hi i = 1 from dite_eq_right h]
        set d := max δ (f i) with hd
        have hd1 : d < 1 := max_lt hδ ha.1.2
        have hsub : Icc (f i) d ⊆ Ioo (-1:ℝ) 1 := Icc_subset_Ioo ha.1.1 hd1
        have hfin := ODE.sturmDef_finite (f' := y') (fun x hx => (hy x (hsub hx)).1)
          (fun x hx h0 => hsimple x (hsub hx) h0)
        have hSne : hfin.toFinset.Nonempty :=
          (Set.Finite.toFinset_nonempty hfin).2 ⟨_, ⟨⟨le_rfl, le_max_right _ _⟩, ha.2⟩⟩
        have hzS := hfin.mem_toFinset.1 (Finset.max'_mem _ hSne)
        have hmax : ∀ x ∈ {x | x ∈ Icc (f i) d ∧ y x = 0}, x ≤ hfin.toFinset.max' hSne :=
          fun x hx => Finset.le_max' _ _ (hfin.mem_toFinset.2 hx)
        obtain ⟨c, hc, hc0⟩ := lzt_upper_right hy hu hq (hsub hzS.1) hs₀ hK hzS.2
          (fun x hx h0 => by
            by_cases hxd : x ≤ d
            · have := hmax x ⟨⟨hzS.1.1.trans hx.1.le, hxd⟩, h0⟩
              linarith [hx.1]
            · exact hnear x ⟨lt_of_le_of_lt (le_max_left _ _) (not_le.mp hxd), hx.2⟩ h0) hC hb
        exact ⟨c, ⟨hzS.1.1.trans_lt hc.1, hc.2⟩, hc0⟩
    choose g hg hg0 using hgap
    have hhi : ∀ i, hi i ≤ 1 := fun i => by
      simp only [hi]; split_ifs
      · exact (hfZ _).1.2.le
      · exact le_rfl
    have hgI : ∀ i, g i ∈ Ioo (-1:ℝ) 1 := fun i =>
      ⟨(hfZ i).1.1.trans (hg i).1, (hg i).2.trans_le (hhi i)⟩
    have hgm : StrictMono g := fun i₁ i₂ h12 => by
      have h12' : i₁.val < i₂.val := h12
      have a : i₁.val + 1 < n := by have := i₂.isLt; omega
      have : hi i₁ ≤ f i₂ := by
        rw [show hi i₁ = f ⟨i₁.val + 1, a⟩ from dite_eq_left a]
        exact f.monotone (Fin.mk_le_mk.2 (by omega))
      linarith [(hg i₁).2, (hg i₂).1]
    choose σ hσ using fun i => huz (g i) (hgI i) (hg0 i)
    have hinj : Function.Injective σ := fun i₁ i₂ h => hgm.injective (by rw [hσ, hσ, h])
    have := Fintype.card_le_of_injective σ hinj
    simp only [Fintype.card_fin] at this
    omega
  have hfin : Z.Finite := by
    by_contra hinf
    obtain ⟨T, hT, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (k + 1)
    have := claim T hT
    omega
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card Z hfin]
  exact claim _ (by simp)



end Comparison

section Ferrers

open Complex DLMF.Hypergeometric DLMF.OrthogonalPolynomials
open scoped Real Nat

/-- The normalizing constant in `𝖯^{-m}_{m+j} = B (1-x²)^{m/2} C_j^{(m+1/2)}`. -/
noncomputable def lzt_baseConst (m : ℝ) (j : ℕ) : ℝ :=
  j ! / (2 ^ m * Real.Gamma (m + 1) * (ascPochhammer ℝ j).eval (2 * m + 1))

/-- The normalizing constant of the polynomial case is positive. -/
theorem lzt_baseConst_pos {m : ℝ} (hm : 0 ≤ m) (j : ℕ) : 0 < lzt_baseConst m j := by
  unfold lzt_baseConst
  have h1 : 0 < (ascPochhammer ℝ j).eval (2 * m + 1) := ascPochhammer_pos _ _ (by linarith)
  have h2 := Real.Gamma_pos_of_pos (show 0 < m + 1 by linarith)
  have h3 : (0:ℝ) < 2 ^ m := Real.rpow_pos_of_pos (by norm_num) m
  positivity

/-- **Polynomial case.** `𝖯^{-m}_{m+j}(x) = B (1-x²)^{m/2} C_j^{(m+1/2)}(x)` for `m ≥ 0`. -/
theorem lzt_ferrersP_base {m : ℝ} (hm : 0 ≤ m) (j : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ((m + j : ℝ) : ℂ) ((-m : ℝ) : ℂ) x =
      ((lzt_baseConst m j * (1 - x ^ 2) ^ (m / 2) *
        (ultrasphPolyR (m + 1 / 2) j).eval x : ℝ) : ℂ) := by
  have ht : ((1:ℂ) - x) / 2 ∈ cutPlane := by
    rw [mem_cutPlane, show (1:ℂ) - (1 - (x:ℂ)) / 2 = (((1 + x) / 2 : ℝ) : ℂ) by push_cast; ring]
    exact Or.inl (by simp only [ofReal_re]; linarith [hx.1])
  have htn : ‖((1:ℂ) - x) / 2‖ < 1 := by
    rw [show ((1:ℂ) - x) / 2 = (((1 - x) / 2 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hc : ∀ k : ℕ, (1 : ℂ) + m ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hU := eval_ultrasphPolyR (show -1/2 < m + 1/2 by linarith) j x
  unfold ultrasphPoly at hU
  unfold ferrersP
  rw [regularizedGaussHG_euler _ _ _ ht, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ htn]
  have e1 : (1:ℂ) - ((-m:ℝ):ℂ) - (((m + j:ℝ):ℂ) + 1) - -((m + j:ℝ):ℂ) = ((-(-m):ℝ):ℂ) := by
    push_cast; ring
  have e2 : (1:ℂ) - ((-m:ℝ):ℂ) - (((m + j:ℝ):ℂ) + 1) = -(j:ℂ) := by push_cast; ring
  have e3 : (1:ℂ) - ((-m:ℝ):ℂ) - -((m + j:ℝ):ℂ) = (j:ℂ) + 2 * ((m + 1/2 : ℝ) : ℂ) := by
    push_cast; ring
  have e4 : (1:ℂ) - ((-m:ℝ):ℂ) = ((m + 1/2 : ℝ) : ℂ) + 1/2 := by push_cast; ring
  rw [e1, e2, e3, e4, regularizedGaussHGFun_eq_div_Gamma (by rw [← e4]; push_cast; simpa [sub_neg_eq_add] using hc)]
  have hg := ferrers_quadratic_gauge ((-m:ℝ):ℂ) hx
  rw [show (1:ℂ) - (1 - (x:ℂ)) / 2 = (1 + (x:ℂ)) / 2 by ring]
  rw [show 2 * ((m + 1/2 : ℝ) : ℂ) = ((2 * m + 1 : ℝ) : ℂ) by push_cast; ring,
    poch_ofReal_eq_eval] at hU
  have hpoch : 0 < (ascPochhammer ℝ j).eval (2 * m + 1) := ascPochhammer_pos _ _ (by linarith)
  have hF : ₂F₁ (-(j:ℂ)) ((j:ℂ) + ((2 * m + 1 : ℝ) : ℂ)) (((m + 1/2 : ℝ) : ℂ) + 1/2)
      ((1 - (x:ℂ)) / 2) = (((ultrasphPolyR (m + 1 / 2) j).eval x : ℝ) : ℂ) * j ! /
        (((ascPochhammer ℝ j).eval (2 * m + 1) : ℝ) : ℂ) := by
    rw [hU]
    have : (((ascPochhammer ℝ j).eval (2 * m + 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpoch.ne'
    have hj : ((j ! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
    field_simp
  rw [show (2 : ℂ) * ((m + 1/2 : ℝ) : ℂ) = ((2 * m + 1 : ℝ) : ℂ) by push_cast; ring, hF,
    show ((- -m : ℝ) : ℂ) = -((-m : ℝ) : ℂ) by push_cast; ring, ← mul_assoc, hg,
    show (1:ℂ) - (x:ℂ) ^ 2 = ((1 - x ^ 2 : ℝ) : ℂ) by push_cast; ring,
    show -((-m : ℝ) : ℂ) / 2 = ((m / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (by nlinarith [hx.1, hx.2] : (0:ℝ) ≤ 1 - x ^ 2),
    show ((m + 1/2 : ℝ) : ℂ) + 1/2 = ((m + 1 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
    show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, ← ofReal_cpow (by norm_num : (0:ℝ) ≤ 2)]
  unfold lzt_baseConst
  have h2 := Real.Gamma_pos_of_pos (show 0 < m + 1 by linarith)
  have h3 : (0:ℝ) < 2 ^ m := Real.rpow_pos_of_pos (by norm_num) m
  rw [Real.rpow_neg (by norm_num)]
  push_cast
  field_simp


/-- `𝖯^μ_ν` solves the associated Legendre equation on `(-1, 1)`. -/
theorem lzt_isSol_P (ν μ : ℂ) : IsFerrersSolution ν μ (ferrersP ν μ) :=
  ((ferrersEven_isFerrersSolution ν μ).add_smul (ferrersOdd_isFerrersSolution ν μ) _ _).congr
    (ferrersP_eqOn_even_odd ν μ).symm

/-- Real form of the associated Legendre equation for the real parts of `𝖯^μ_ν`. -/
theorem lzt_ferrersP_sol (ν μ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun t => (ferrersP ν μ t).re) (deriv (ferrersP ν μ) x).re x ∧
    HasDerivAt (fun t => (1 - t ^ 2) * (deriv (ferrersP ν μ) t).re)
      (-((ν * (ν + 1) - μ ^ 2 / (1 - x ^ 2)) * (ferrersP ν μ x).re)) x := by
  obtain ⟨hd, f2, hf2, heq⟩ := lzt_isSol_P ν μ x hx
  have hre : ∀ {g : ℝ → ℂ} {g' : ℂ}, HasDerivAt g g' x → HasDerivAt (fun t => (g t).re) g'.re x :=
    fun h => by
      have h1 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
      simpa only [Function.comp_def, Complex.reCLM_apply] using h1
  refine ⟨hre hd.hasDerivAt, ?_⟩
  have h2 := ((hasDerivAt_id x).pow 2).const_sub 1 |>.mul (hre hf2)
  convert h2 using 1
  · funext t; simp
  have := congrArg Complex.re heq
  have e1 : (1 - (x:ℂ) ^ 2) = ((1 - x ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : ((ν:ℂ) * ((ν:ℂ) + 1) - (μ:ℂ) ^ 2 / (1 - (x:ℂ) ^ 2)) =
      ((ν * (ν + 1) - μ ^ 2 / (1 - x ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [e2, e1, show (2:ℂ) * x = ((2 * x : ℝ) : ℂ) by push_cast; ring] at this
  simp only [Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.zero_re] at this
  simp only [id, Nat.cast_ofNat, Pi.pow_apply]
  norm_num
  linarith [this]

/-- A real-valued `𝖯^μ_ν` agrees with its real part, together with its derivative. -/
theorem lzt_ferrersP_real_data (ν μ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν μ x = ((ferrersP ν μ x).re : ℂ) ∧
      deriv (ferrersP ν μ) x = ((deriv (ferrersP ν μ) x).re : ℂ) := by
  have hd := ((lzt_isSol_P ν μ) x hx).1
  have hreal : ∀ᶠ y in 𝓝 x, (ferrersP ν μ y).im = 0 :=
    Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) fun y hy => ferrersP_real ν μ hy
  have him : HasDerivAt (fun y => (ferrersP ν μ y).im) (deriv (ferrersP ν μ) x).im x := by
    have h1 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hd.hasDerivAt
    simpa only [Function.comp_def, Complex.imCLM_apply] using h1
  have him0 : HasDerivAt (fun y => (ferrersP ν μ y).im) 0 x :=
    (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq (hreal.mono fun y hy => hy)
  have h0 : (deriv (ferrersP ν μ) x).im = 0 := him.unique him0
  exact ⟨Complex.ext (by simp) (by simpa using ferrersP_real ν μ hx),
    Complex.ext (by simp) (by simp [h0])⟩


/-- The zeros of `𝖯^{-m}_ν` in `(-1, 1)` are simple (`m ≥ 0`, `ν ≥ -1/2`), by the Wronskians
DLMF 14.2.4 (with `𝖰^{-m}_ν`) and 14.2.3 (with `𝖯^{-m}_ν(-x)`). -/
theorem lzt_ferrersP_simple {ν m : ℝ} (hm : 0 ≤ m) (hν : -1/2 ≤ ν) {x : ℝ}
    (hx : x ∈ Ioo (-1:ℝ) 1) (h0 : (ferrersP ν (-m : ℝ) x).re = 0) :
    (deriv (ferrersP ν (-m : ℝ)) x).re ≠ 0 := by
  intro h1
  obtain ⟨e0, e1⟩ := lzt_ferrersP_real_data ν (-m) hx
  rw [h0] at e0
  rw [h1] at e1
  simp only [Complex.ofReal_zero] at e0 e1
  have hx2 : (1 - (x:ℂ) ^ 2) ≠ 0 := by
    rw [show (1 - (x:ℂ) ^ 2) = ((1 - x ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact_mod_cast (show (1 - x ^ 2) ≠ 0 by nlinarith [hx.1, hx.2])
  have hG2 : Gamma ((ν:ℂ) + m + 1) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  by_cases hr : LegendreQRegular (ν:ℂ) ((-m:ℝ):ℂ)
  · have hW := ferrers_wronskian_4 _ _ hr hx
    rw [ferrersWronskian, e0, e1] at hW
    simp only [zero_mul, mul_zero, sub_zero] at hW
    have hG1 : Gamma ((ν:ℂ) + ((-m:ℝ):ℂ) + 1) ≠ 0 := by
      refine Complex.Gamma_ne_zero fun n hn => hr n ?_
      linear_combination hn
    have hG2' : Gamma ((ν:ℂ) - ((-m:ℝ):ℂ) + 1) ≠ 0 := by
      rw [show (ν:ℂ) - ((-m:ℝ):ℂ) + 1 = (ν:ℂ) + m + 1 by push_cast; ring]; exact hG2
    exact (div_ne_zero hG1 (mul_ne_zero hG2' hx2)) hW.symm
  · simp only [LegendreQRegular, not_forall, not_not] at hr
    obtain ⟨n, hn⟩ := hr
    have hW := ferrers_wronskian_3 (ν:ℂ) (m:ℂ) hx
    rw [show -(m:ℂ) = ((-m:ℝ):ℂ) by push_cast; ring, ferrersWronskian, e0, e1] at hW
    simp only [zero_mul, mul_zero, sub_zero] at hW
    have hG1 : Gamma ((m:ℂ) - ν) ≠ 0 := by
      rw [show (m:ℂ) - ν = ((n + 1 : ℕ) : ℂ) by push_cast at hn ⊢; linear_combination -hn]
      exact Complex.Gamma_ne_zero_of_re_pos (by simp; positivity)
    exact (div_ne_zero two_ne_zero (mul_ne_zero (mul_ne_zero hG1 hG2) hx2)) hW.symm


/-- `((1+x)/(1-x))^{-m/2} ≤ (1-x²)^{m/2}` for `0 ≤ x < 1`, `m ≥ 0`. -/
theorem lzt_rpow_le {m x : ℝ} (hm : 0 ≤ m) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ((1 + x) / (1 - x)) ^ (-m / 2) ≤ (1 - x ^ 2) ^ (m / 2) := by
  have h1 : 0 < 1 + x := by linarith
  have h2 : 0 < 1 - x := by linarith
  rw [Real.rpow_def_of_pos (div_pos h1 h2), Real.rpow_def_of_pos (by nlinarith),
    Real.log_div h1.ne' h2.ne', show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
    Real.log_mul h2.ne' h1.ne']
  have : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  exact Real.exp_le_exp.2 (by nlinarith)

/-- Near `x = 1`, `𝖯^{-m}_ν` (`m ≥ 0`) has no zeros and is `O((1-x²)^{m/2})`. -/
theorem lzt_ferrersP_near_one (ν : ℝ) {m : ℝ} (hm : 0 ≤ m) :
    ∃ s₀ < 1, ∃ M, ∀ x ∈ Ioo s₀ 1, (ferrersP ν (-m : ℝ) x).re ≠ 0 ∧
      |(ferrersP ν (-m : ℝ) x).re| ≤ M * (1 - x ^ 2) ^ (m / 2) := by
  set g : ℝ → ℂ := fun x => regularizedGaussHG ((ν:ℂ) + 1) (-(ν:ℂ)) (1 - ((-m:ℝ):ℂ))
    ((1 - (x:ℂ)) / 2) with hg
  have h0c : (0:ℂ) ∈ cutPlane := mem_cutPlane_of_norm_lt_one (by simp)
  have hcont : ContinuousAt g 1 := by
    have h1 : ContinuousAt (fun x : ℝ => (1 - (x:ℂ)) / 2) 1 := by fun_prop
    have h2 : ((1:ℂ) - ((1:ℝ):ℂ)) / 2 = 0 := by simp
    have h3 := (analyticOnNhd_regularizedGaussHG ((ν:ℂ) + 1) (-(ν:ℂ)) (1 - ((-m:ℝ):ℂ)) 0
      h0c).continuousAt
    exact h3.comp_of_eq h1 h2
  have hc : ∀ k : ℕ, (1:ℂ) - ((-m:ℝ):ℂ) ≠ -(k:ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hg1 : g 1 = ((Real.Gamma (1 + m))⁻¹ : ℝ) := by
    simp only [hg, ofReal_one, sub_self, zero_div]
    rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by simp),
      regularizedGaussHGFun_eq_div_Gamma hc, ordinaryHypergeometric_zero,
      show (1:ℂ) - ((-m:ℝ):ℂ) = ((1 + m : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast; ring
  have hG := Real.Gamma_pos_of_pos (show 0 < 1 + m by linarith)
  have hre1 : 0 < (g 1).re := by rw [hg1, ofReal_re]; positivity
  have hev : ∀ᶠ x in 𝓝 (1:ℝ), 0 < (g x).re ∧ ‖g x‖ < ‖g 1‖ + 1 := by
    have t1 := (Complex.continuous_re.continuousAt.comp hcont).eventually (lt_mem_nhds
      (show (g 1).re / 2 < (g 1).re by linarith))
    have t2 := (continuous_norm.continuousAt.comp hcont).eventually (gt_mem_nhds
      (show ‖g 1‖ < ‖g 1‖ + 1 by linarith))
    filter_upwards [t1, t2] with x h1 h2
    exact ⟨by simp only [Function.comp] at h1; linarith, h2⟩
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp (nhdsWithin_le_nhds hev)
  refine ⟨max l 0, max_lt hl (by norm_num), ‖g 1‖ + 1, fun x hx => ?_⟩
  have hxl : x ∈ Ioo l 1 := ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, hx.2⟩
  have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx.1)
  obtain ⟨hgr, hgn⟩ := hsub hxl
  have hpos : 0 ≤ (1 + x) / (1 - x) := div_nonneg (by linarith) (by linarith [hx.2])
  have hrep : (ferrersP ν (-m : ℝ) x).re = ((1 + x) / (1 - x)) ^ (-m / 2) * (g x).re := by
    simp only [ferrersP, hg]
    rw [show ((-m:ℝ):ℂ) / 2 = ((-m / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hpos,
      re_ofReal_mul]
  have hr : 0 < ((1 + x) / (1 - x)) ^ (-m / 2) :=
    Real.rpow_pos_of_pos (div_pos (by linarith) (by linarith [hx.2])) _
  refine ⟨by rw [hrep]; exact (mul_pos hr hgr).ne', ?_⟩
  rw [hrep, abs_mul, abs_of_pos hr]
  have hle := lzt_rpow_le hm hx0 hx.2
  have hq : 0 ≤ (1 - x ^ 2) ^ (m / 2) := Real.rpow_nonneg (by nlinarith [hx.2]) _
  calc ((1 + x) / (1 - x)) ^ (-m / 2) * |(g x).re| ≤ (1 - x ^ 2) ^ (m / 2) * (‖g 1‖ + 1) :=
        mul_le_mul hle ((Complex.abs_re_le_norm _).trans hgn.le) (abs_nonneg _) hq
    _ = (‖g 1‖ + 1) * (1 - x ^ 2) ^ (m / 2) := by ring


/-- Zeros, boundedness and the behaviour at `1` of the polynomial case `𝖯^{-m}_{m+j}`. -/
theorem lzt_base_data {m : ℝ} (hm : 0 ≤ m) (j : ℕ) :
    ∃ e : Fin j → ℝ, StrictMono e ∧ (∀ i, e i ∈ Ioo (-1:ℝ) 1) ∧
      (∀ x ∈ Ioo (-1:ℝ) 1, (ferrersP ((m + j : ℝ) : ℂ) ((-m : ℝ) : ℂ) x).re = 0 ↔
        ∃ i, x = e i) ∧
      (∃ K > 0, ∀ x ∈ Ioo (-1:ℝ) 1,
        (1 - x ^ 2) * (ferrersP ((m + j : ℝ) : ℂ) ((-m : ℝ) : ℂ) x).re ^ 2 ≤ K * (1 - x) ∧
        (1 - x ^ 2) * (ferrersP ((m + j : ℝ) : ℂ) ((-m : ℝ) : ℂ) x).re ^ 2 ≤ K * (1 + x)) ∧
      (∃ s₀ < 1, ∃ c > 0, ∀ x ∈ Ioo s₀ 1,
        c * (1 - x ^ 2) ^ (m / 2) ≤ |(ferrersP ((m + j : ℝ) : ℂ) ((-m : ℝ) : ℂ) x).re|) := by
  obtain ⟨e, he, heI, hz⟩ := ultrasphPoly_zeros_Ioo (lam := m + 1/2) (by linarith)
    (by linarith) j
  set P := ultrasphPolyR (m + 1 / 2) j with hP
  set B := lzt_baseConst m j with hB
  have hB0 : 0 < B := lzt_baseConst_pos hm j
  have hval : ∀ x ∈ Ioo (-1:ℝ) 1, (ferrersP ((m + j : ℝ) : ℂ) ((-m : ℝ) : ℂ) x).re =
      B * (1 - x ^ 2) ^ (m / 2) * P.eval x := fun x hx => by
    rw [lzt_ferrersP_base hm j hx, ofReal_re]
  have hrp : ∀ x ∈ Ioo (-1:ℝ) 1, 0 < (1 - x ^ 2) ^ (m / 2) := fun x hx =>
    Real.rpow_pos_of_pos (by nlinarith [hx.1, hx.2]) _
  have hr1 : ∀ x ∈ Ioo (-1:ℝ) 1, (1 - x ^ 2) ^ (m / 2) ≤ 1 := fun x hx =>
    Real.rpow_le_one (by nlinarith [hx.1, hx.2]) (by nlinarith) (by linarith)
  have hPz : ∀ x : ℝ, P.eval x = 0 ↔ ∃ i, x = e i := fun x => by
    rw [← ofReal_eq_zero, eval_ultrasphPolyR (by linarith), hz]
    simp only [ofReal_inj]
  refine ⟨e, he, heI, fun x hx => ?_, ?_, ?_⟩
  · rw [hval x hx, mul_eq_zero, or_iff_right (mul_pos hB0 (hrp x hx)).ne', hPz]
  · obtain ⟨Mp, hMp⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (P.continuous.continuousOn (s := Icc (-1:ℝ) 1))
    refine ⟨2 * B ^ 2 * Mp ^ 2 + 1, by positivity, fun x hx => ?_⟩
    have hM := hMp x (Ioo_subset_Icc_self hx)
    rw [Real.norm_eq_abs] at hM
    have hsq : (ferrersP ((m + j : ℝ) : ℂ) ((-m : ℝ) : ℂ) x).re ^ 2 ≤ B ^ 2 * Mp ^ 2 := by
      rw [hval x hx, mul_pow, mul_pow]
      have h1 : ((1 - x ^ 2) ^ (m / 2)) ^ 2 ≤ 1 := by
        have := hr1 x hx; have := hrp x hx; nlinarith
      have h2 : P.eval x ^ 2 ≤ Mp ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hM 2
      have h3 : 0 ≤ ((1 - x ^ 2) ^ (m / 2)) ^ 2 := sq_nonneg _
      have h4 : 0 ≤ P.eval x ^ 2 := sq_nonneg _
      have := mul_le_mul h1 h2 h4 zero_le_one
      nlinarith [sq_nonneg B]
    have hp : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have hm1 := mul_le_mul_of_nonneg_left hsq hp
    have hBM : 0 ≤ B ^ 2 * Mp ^ 2 := by positivity
    have e1 : 1 - x ^ 2 ≤ 2 * (1 - x) := by nlinarith [hx.1, hx.2]
    have e2 : 1 - x ^ 2 ≤ 2 * (1 + x) := by nlinarith [hx.1, hx.2]
    have f1 := mul_le_mul_of_nonneg_right e1 hBM
    have f2 := mul_le_mul_of_nonneg_right e2 hBM
    constructor <;> nlinarith [hx.1, hx.2]
  · have hP1 : P.eval 1 ≠ 0 := fun h => by
      obtain ⟨i, hi⟩ := (hPz 1).1 h
      have := (heI i).2; linarith
    have hev : ∀ᶠ x in 𝓝 (1:ℝ), |P.eval 1| / 2 < |P.eval x| :=
      (continuous_abs.continuousAt.comp P.continuous.continuousAt).eventually
        (lt_mem_nhds (show |P.eval 1| / 2 < |P.eval 1| by
          have := abs_pos.mpr hP1; linarith))
    obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp (nhdsWithin_le_nhds hev)
    refine ⟨max l (-1), max_lt hl (by norm_num), B * (|P.eval 1| / 2),
      mul_pos hB0 (by have := abs_pos.mpr hP1; linarith), fun x hx => ?_⟩
    have hxI : x ∈ Ioo (-1:ℝ) 1 := ⟨lt_of_le_of_lt (le_max_right _ _) hx.1, hx.2⟩
    have hxl : |P.eval 1| / 2 < |P.eval x| := hsub ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, hx.2⟩
    rw [hval x hxI, abs_mul, abs_mul, abs_of_pos hB0, abs_of_pos (hrp x hxI)]
    have := hrp x hxI
    nlinarith [mul_le_mul_of_nonneg_left hxl.le (mul_pos hB0 this).le]


/-- **Zero count of `𝖯^{-m}_ν`** (DLMF 14.16(ii)). For `m ≥ 0` and `ν ≥ -1/2`, the Ferrers
function `𝖯^{-m}_ν` has exactly `max(⌈ν - m⌉, 0)` zeros in `(-1, 1)`. With
`k = max(⌈ν - m⌉, 0)`, the count is squeezed between Sturm comparisons with the polynomial cases
of degrees `m + k - 1` and `m + k`. -/
theorem lzt_ferrersP_neg_order_zero_count {ν m : ℝ} (hm : 0 ≤ m) (hν : -1/2 ≤ ν) :
    {x | x ∈ Ioo (-1:ℝ) 1 ∧ (ferrersP ν (-m : ℝ) x).re = 0}.Finite ∧
      {x | x ∈ Ioo (-1:ℝ) 1 ∧ (ferrersP ν (-m : ℝ) x).re = 0}.ncard =
        (max ⌈ν - m⌉ 0).toNat := by
  set Z := {x | x ∈ Ioo (-1:ℝ) 1 ∧ (ferrersP ν (-m : ℝ) x).re = 0} with hZ
  set k := (max ⌈ν - m⌉ 0).toNat with hk
  have hkz : (k : ℤ) = max ⌈ν - m⌉ 0 := Int.toNat_of_nonneg (le_max_right _ _)
  have hkr : ν - m ≤ k := by
    have h1 : (⌈ν - m⌉ : ℝ) ≤ k := by exact_mod_cast hkz ▸ le_max_left _ _
    exact (Int.le_ceil _).trans h1
  set q : ℝ → ℝ → ℝ := fun a x => a * (a + 1) - (-m) ^ 2 / (1 - x ^ 2) with hq
  have hsol : ∀ a : ℝ, lzt_IsSol (q a) (fun x => (ferrersP a (-m : ℝ) x).re)
      (fun x => (deriv (ferrersP a (-m : ℝ)) x).re) := fun a x hx => lzt_ferrersP_sol a (-m) hx
  have hqlt : ∀ a b : ℝ, -1/2 ≤ a → a < b → ∀ x ∈ Ioo (-1:ℝ) 1, q a x < q b x := by
    intro a b ha hab x _
    simp only [hq]
    nlinarith
  -- the upper bound, by comparison with the polynomial case of degree `m + k`
  obtain ⟨e, he, heI, hez, ⟨K, hK, hKb⟩, ⟨s₁, hs₁, c, hc, hcb⟩⟩ := lzt_base_data hm k
  have hupper : Z.Finite ∧ Z.ncard ≤ k := by
    rcases eq_or_lt_of_le (show ν ≤ m + k by linarith) with heq | hlt
    · have hc : (ν : ℂ) = ((m + k : ℝ) : ℂ) := by rw [heq]
      have hZe : Z = range e := by
        ext x
        simp only [hZ, mem_ofPred_eq, mem_range, hc]
        constructor
        · rintro ⟨hx, h0⟩
          obtain ⟨i, rfl⟩ := (hez x hx).1 h0
          exact ⟨i, rfl⟩
        · rintro ⟨i, rfl⟩
          exact ⟨heI i, (hez _ (heI i)).2 ⟨i, rfl⟩⟩
      rw [hZe]
      refine ⟨finite_range e, ?_⟩
      rw [ncard_range_of_injective he.injective, Nat.card_eq_fintype_card, Fintype.card_fin]
    · obtain ⟨s₀, hs₀, M, hM⟩ := lzt_ferrersP_near_one ν hm
      set t := max (max s₀ s₁) 0 with ht
      have ht1 : t < 1 := max_lt (max_lt hs₀ hs₁) (by norm_num)
      have htI : ∀ x ∈ Ioo t 1, x ∈ Ioo (-1:ℝ) 1 ∧ x ∈ Ioo s₀ 1 ∧ x ∈ Ioo s₁ 1 := by
        intro x hx
        have a1 := le_max_left (max s₀ s₁) 0
        have a2 := le_max_right (max s₀ s₁) 0
        have a3 := le_max_left s₀ s₁
        have a4 := le_max_right s₀ s₁
        exact ⟨⟨by linarith [hx.1], hx.2⟩, ⟨by linarith [hx.1], hx.2⟩, ⟨by linarith [hx.1], hx.2⟩⟩
      refine lzt_upper_count (hsol ν) (hsol (m + k)) (hqlt ν (m + k) hν hlt) (e := e)
        (fun x hx h0 => (hez x hx).1 h0) (fun x hx h0 => lzt_ferrersP_simple hm hν hx h0)
        hs₀ (fun x hx => (hM x hx).1) ht1 hK (C := |M| / c) (fun x hx => ?_)
        (fun x hx => (hKb x (htI x hx).1).1)
      obtain ⟨hxI, hx0, hx1⟩ := htI x hx
      have h1 := (hM x hx0).2
      have h2 := hcb x hx1
      have hr : 0 ≤ (1 - x ^ 2) ^ (m / 2) := Real.rpow_nonneg (by nlinarith [hxI.1, hxI.2]) _
      have h3 : |(ferrersP ν (-m : ℝ) x).re| ≤ |M| * (1 - x ^ 2) ^ (m / 2) :=
        h1.trans (mul_le_mul_of_nonneg_right (le_abs_self M) hr)
      calc |(ferrersP ν (-m : ℝ) x).re| ≤ |M| * (1 - x ^ 2) ^ (m / 2) := h3
        _ = |M| / c * (c * (1 - x ^ 2) ^ (m / 2)) := by field_simp
        _ ≤ |M| / c * |(ferrersP ((m + k : ℝ) : ℂ) ((-m : ℝ) : ℂ) x).re| :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg (abs_nonneg _) hc.le)
  -- the lower bound, by comparison with the polynomial case of degree `m + k - 1`
  refine ⟨hupper.1, le_antisymm hupper.2 ?_⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0]; exact Nat.zero_le _
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt hkpos
  rw [zero_add] at hj
  have hνj : m + j < ν := by
    have h1 : ⌈ν - m⌉ = (k : ℤ) := by
      rw [hkz]; refine (max_eq_left ?_).symm
      by_contra h; push Not at h
      have : max ⌈ν - m⌉ 0 = 0 := max_eq_right h.le
      rw [this] at hkz; omega
    have h2 := Int.ceil_lt_add_one (ν - m)
    rw [h1, hj] at h2
    push_cast at h2
    linarith
  obtain ⟨e', he', heI', hez', ⟨K', hK', hKb'⟩, -⟩ := lzt_base_data hm j
  obtain ⟨cz, hcz, hczZ⟩ := lzt_lower_count (hsol ν) (hsol (m + j))
    (hqlt (m + j) ν (by have := (j.cast_nonneg : (0:ℝ) ≤ j); linarith) hνj) he' heI' hez'
    (s₀ := 0) (s₀' := 0) (by norm_num) (by norm_num) hK'
    (fun x hx => (hKb' x ⟨by linarith [hx.1], hx.2⟩).1)
    (fun x hx => (hKb' x ⟨hx.1, by linarith [hx.2]⟩).2)
  have hsub : range cz ⊆ Z := by
    rintro _ ⟨i, rfl⟩; exact hczZ i
  have := ncard_le_ncard hsub hupper.1
  rwa [ncard_range_of_injective hcz.injective, Nat.card_eq_fintype_card, Fintype.card_fin,
    ← hj] at this

end Ferrers

end DLMF.Legendre
