/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.CoulombIrregular
public import DLMF.Confluent.AsymptoticConsequences
public import DLMF.Confluent.Relations
public import DLMF.OrthogonalPolynomials.ClassicalInstances
public import DLMFMathlib.Analysis.ODE.SturmCount
public import DLMFMathlib.Analysis.ODE.SturmDeformation

/-!
# Zero counts of Tricomi's `U` by Sturm comparison

Tools for the real zero counts of DLMF §13.9(ii). For real parameters `a`, `b` and `x > 0`,
`U(a,b,x)` is real (`kzt_U_real`) and satisfies the self-adjoint form
`(x^b e^{-x} y')' - a x^{b-1} e^{-x} y = 0` of Kummer's equation on `(0, ∞)` (`kzt_U_isSol`).

The comparison theory is that of `DLMF/Legendre/ZeroTools.lean` (prefix `lzt_`), transplanted
from `(-1, 1)` to `(0, ∞)` with a general positive weight `p`: for two solutions `y`, `u` of
`(p y')' + q y = 0` with coefficients `qy < qu`, the weighted Wronskian `W = p (u'y - uy')` is
strictly monotone wherever `u y > 0`. This gives

* the classical Sturm comparison between consecutive zeros (`kzt_between`);
* comparisons at the ends, where a sign of `W` forces `y/u` to diverge as soon as
  `p u² = O(x)` at `0` (`kzt_lower_left`) or `p u² = O(1)` at `∞` (`kzt_upper_right`,
  `kzt_lower_right`), and on the whole half-line (`kzt_lower_whole`);
* lower and upper zero counts from exactly known comparison functions (`kzt_lower_count`,
  `kzt_upper_count`).

The comparison functions are the polynomial cases `U(-n,b,x) = (-1)ⁿ n! L_n^{(b-1)}(x)`
(DLMF 13.6.19), whose zeros are those of the Laguerre polynomial (`laguerrePolyL_zeros_pos`,
DLMF 18.16(iv)). Zeros of `U(a,b,·)`, `a ∉ -ℕ`, are simple by the Wronskian 13.2.34
(`kzt_U_simple`), and `U(a,b,x) ~ x^{-a}` at `∞` (`kzt_U_asymp`, DLMF 13.2.6). The result is the
count `⌈-a⌉` of positive zeros of `U(a,b,·)` for `a < 0` nonintegral and `b ≥ 1`
(`kzt_U_posZeros_count`), which gives DLMF 13.9.14 by Kummer's transformation.

All helper names carry the prefix `kzt_`.
-/

@[expose] public noncomputable section

open Set Filter Topology

namespace DLMF.Confluent

/-! ### Sturm comparison on `(0, ∞)` -/

/-- `y` (with derivative `y'`) solves `(p y')' + q y = 0` on `(0, ∞)`. -/
def kzt_IsSol (p q y y' : ℝ → ℝ) : Prop :=
  ∀ x ∈ Ioi (0:ℝ), HasDerivAt y (y' x) x ∧
    HasDerivAt (fun t => p t * y' t) (-(q x * y x)) x

/-- The negative of a solution is a solution. -/
lemma kzt_IsSol.neg {p q y y' : ℝ → ℝ} (h : kzt_IsSol p q y y') :
    kzt_IsSol p q (fun x => -y x) (fun x => -y' x) := fun x hx => by
  refine ⟨(h x hx).1.neg, ?_⟩
  have := (h x hx).2.neg
  convert this using 1
  · funext t; simp only [Pi.neg_apply]; ring
  · ring

/-- Solutions are continuous on subsets of `(0, ∞)`. -/
lemma kzt_IsSol.continuousOn {p q y y' : ℝ → ℝ} (h : kzt_IsSol p q y y') {s : Set ℝ}
    (hs : s ⊆ Ioi (0:ℝ)) : ContinuousOn y s := fun _x hx =>
  (h _ (hs hx)).1.continuousAt.continuousWithinAt

/-- The weighted Wronskian `p (u'y - uy')` of two solutions. -/
def kzt_W (p u u' y y' : ℝ → ℝ) (x : ℝ) : ℝ := p x * (u' x * y x - u x * y' x)

/-- The weighted Wronskian is odd in `y`. -/
lemma kzt_W_neg (p u u' y y' : ℝ → ℝ) (x : ℝ) :
    kzt_W p u u' (fun x => -y x) (fun x => -y' x) x = -kzt_W p u u' y y' x := by
  simp only [kzt_W]; ring

section Comparison

variable {p qy qu qw y y' u u' w w' : ℝ → ℝ}

/-- Derivative of the weighted Wronskian: `W' = (qy - qu) u y`. -/
lemma kzt_hasDerivAt_W (hy : kzt_IsSol p qy y y') (hu : kzt_IsSol p qu u u')
    {x : ℝ} (hx : x ∈ Ioi (0:ℝ)) :
    HasDerivAt (kzt_W p u u' y y') ((qy x - qu x) * u x * y x) x := by
  have h1 := (hu x hx).2.mul (hy x hx).1
  have h2 := (hu x hx).1.mul (hy x hx).2
  have := h1.sub h2
  convert this using 1
  · funext t; simp only [kzt_W, Pi.mul_apply, Pi.sub_apply]; ring
  · ring

/-- The weighted Wronskian is continuous on subsets of `(0, ∞)`. -/
lemma kzt_W_continuousOn (hy : kzt_IsSol p qy y y') (hu : kzt_IsSol p qu u u') {s : Set ℝ}
    (hs : s ⊆ Ioi (0:ℝ)) : ContinuousOn (kzt_W p u u' y y') s := fun _x hx =>
  (kzt_hasDerivAt_W hy hu (hs hx)).continuousAt.continuousWithinAt

/-- At a zero `a` followed by positive values, the derivative is nonnegative. -/
lemma kzt_deriv_nonneg_right {f : ℝ → ℝ} {d a b : ℝ} (hd : HasDerivAt f d a) (h0 : f a = 0)
    (hab : a < b) (hpos : ∀ x ∈ Ioo a b, 0 < f x) : 0 ≤ d := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsGT_le_nhdsNE a)
  refine ge_of_tendsto hs ?_
  filter_upwards [Ioo_mem_nhdsGT hab] with x hx
  rw [slope_def_field, h0, sub_zero]
  exact (div_pos (hpos x hx) (sub_pos.mpr hx.1)).le

/-- At a zero `b` preceded by positive values, the derivative is nonpositive. -/
lemma kzt_deriv_nonpos_left {f : ℝ → ℝ} {d a b : ℝ} (hd : HasDerivAt f d b) (h0 : f b = 0)
    (hab : a < b) (hpos : ∀ x ∈ Ioo a b, 0 < f x) : d ≤ 0 := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsLT_le_nhdsNE b)
  refine le_of_tendsto hs ?_
  filter_upwards [Ioo_mem_nhdsLT hab] with x hx
  rw [slope_def_field, h0, sub_zero]
  exact (div_neg_of_pos_of_neg (hpos x hx) (sub_neg.mpr hx.2)).le

/-- Nonnegativity at the left end by continuity. -/
lemma kzt_nonneg_left {f : ℝ → ℝ} {a b : ℝ} (hc : ContinuousAt f a) (hab : a < b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) : 0 ≤ f a := by
  refine ge_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi a))) ?_
  filter_upwards [Ioo_mem_nhdsGT hab] with x hx using (hpos x hx).le

/-- Nonnegativity at the right end by continuity. -/
lemma kzt_nonneg_right {f : ℝ → ℝ} {a b : ℝ} (hc : ContinuousAt f b) (hab : a < b)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) : 0 ≤ f b := by
  refine ge_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio b))) ?_
  filter_upwards [Ioo_mem_nhdsLT hab] with x hx using (hpos x hx).le

/-- A continuous function without zeros on an order-connected set has constant sign there. -/
lemma kzt_sign {f : ℝ → ℝ} {s : Set ℝ} (hs : s.OrdConnected) (hc : ContinuousOn f s)
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

/-- **Divergence of a ratio at `∞`.** If `u > 0`, `p u² ≤ K` and the weighted Wronskian
satisfies `W ≤ -c₀ < 0` on `[s, ∞)`, then `y/u` is unbounded above there. -/
lemma kzt_ratio_top {s K c₀ : ℝ} (hK : 0 < K) (hc₀ : 0 < c₀)
    (hyd : ∀ x ∈ Ici s, HasDerivAt y (y' x) x) (hud : ∀ x ∈ Ici s, HasDerivAt u (u' x) x)
    (hup : ∀ x ∈ Ici s, 0 < u x) (hp : ∀ x ∈ Ici s, 0 < p x)
    (hb : ∀ x ∈ Ici s, p x * u x ^ 2 ≤ K)
    (hW : ∀ x ∈ Ici s, kzt_W p u u' y y' x ≤ -c₀) (C : ℝ) :
    ∃ x ∈ Ioi s, C < y x / u x := by
  have hge : ∀ x ∈ Ici s, c₀ / K ≤ (y' x * u x - y x * u' x) / u x ^ 2 := by
    intro x hx
    have hu2 : 0 < u x ^ 2 := pow_pos (hup x hx) 2
    have hWx := hW x hx
    simp only [kzt_W] at hWx
    set D := y' x * u x - y x * u' x
    have hD : c₀ ≤ p x * D := by simp only [D]; linarith
    have hDp : 0 < D := by
      by_contra h; push Not at h; nlinarith [hp x hx]
    rw [div_le_div_iff₀ hK hu2]
    have := hb x hx
    nlinarith [mul_le_mul_of_nonneg_right hD hu2.le, mul_le_mul_of_nonneg_left this hDp.le]
  set r : ℝ → ℝ := fun x => y x / u x - c₀ / K * x with hr
  have hrd : ∀ x ∈ Ici s, HasDerivAt r ((y' x * u x - y x * u' x) / u x ^ 2 - c₀ / K) x :=
    fun x hx => ((hyd x hx).div (hud x hx) (hup x hx).ne').sub (by
      simpa using (hasDerivAt_id x).const_mul (c₀ / K))
  have hmono : MonotoneOn r (Ici s) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici s)
      (fun x hx => (hrd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hrd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
      fun x hx => ?_
    rw [(hrd x (interior_subset hx)).deriv]
    linarith [hge x (interior_subset hx)]
  set x := s + (|C - y s / u s| + 1) * (K / c₀) with hx
  have hKc : 0 < K / c₀ := div_pos hK hc₀
  have hsx : s < x := by
    have : 0 < (|C - y s / u s| + 1) * (K / c₀) := by positivity
    linarith
  refine ⟨x, hsx, ?_⟩
  have h := hmono (mem_Ici.2 le_rfl) (le_of_lt hsx) hsx.le
  simp only [hr] at h
  have hmul : c₀ / K * (x - s) = |C - y s / u s| + 1 := by
    rw [hx]; field_simp; ring
  have := le_abs_self (C - y s / u s)
  nlinarith

/-- **Divergence of a ratio at `0`.** If `u > 0`, `p u² ≤ K x` and `W ≤ -c₀ < 0` on `(0, s]`,
then `y/u` takes negative values there. -/
lemma kzt_ratio_zero {s K c₀ : ℝ} (hs : 0 < s) (hK : 0 < K) (hc₀ : 0 < c₀)
    (hyd : ∀ x ∈ Ioc 0 s, HasDerivAt y (y' x) x) (hud : ∀ x ∈ Ioc 0 s, HasDerivAt u (u' x) x)
    (hup : ∀ x ∈ Ioc 0 s, 0 < u x) (hp : ∀ x ∈ Ioc 0 s, 0 < p x)
    (hb : ∀ x ∈ Ioc 0 s, p x * u x ^ 2 ≤ K * x)
    (hW : ∀ x ∈ Ioc 0 s, kzt_W p u u' y y' x ≤ -c₀) :
    ∃ x ∈ Ioo 0 s, y x / u x < 0 := by
  refine ODE.sturmCount_exists_neg_of_deriv_ge (r := fun x => y x / u x)
    (r' := fun x => (y' x * u x - y x * u' x) / u x ^ 2) (c := c₀ / K) hs (div_pos hc₀ hK)
    (fun x hx => (hyd x hx).div (hud x hx) (hup x hx).ne') (fun x hx => ?_)
  have h1x : 0 < x - 0 := by linarith [hx.1]
  have hu2 : 0 < u x ^ 2 := pow_pos (hup x hx) 2
  have hWx := hW x hx
  simp only [kzt_W] at hWx
  set D := y' x * u x - y x * u' x
  have hD : c₀ ≤ p x * D := by simp only [D]; linarith
  have hDp : 0 < D := by
    by_contra h; push Not at h; nlinarith [hp x hx]
  rw [div_div, div_le_div_iff₀ (mul_pos hK h1x) hu2, sub_zero]
  have := hb x hx
  nlinarith [mul_le_mul_of_nonneg_right hD hu2.le, mul_le_mul_of_nonneg_left this hDp.le]

variable (hp : ∀ x ∈ Ioi (0:ℝ), 0 < p x)
include hp

omit hp in
/-- `W = p (u'y - uy')` is strictly decreasing where `u, y > 0` and `qy < qu`. -/
lemma kzt_W_strictAntiOn (hy : kzt_IsSol p qy y y') (hu : kzt_IsSol p qu u u')
    (hq : ∀ x ∈ Ioi (0:ℝ), qy x < qu x) {s : Set ℝ} (hs : s ⊆ Ioi (0:ℝ)) (hcv : Convex ℝ s)
    (hpos : ∀ x ∈ interior s, 0 < u x ∧ 0 < y x) : StrictAntiOn (kzt_W p u u' y y') s := by
  refine strictAntiOn_of_deriv_neg hcv (kzt_W_continuousOn hy hu hs) fun x hx => ?_
  have hx' := hs (interior_subset hx)
  rw [(kzt_hasDerivAt_W hy hu hx').deriv]
  have := hq x hx'
  have h2 := mul_pos (hpos x hx).1 (hpos x hx).2
  nlinarith

omit hp in
/-- `W = p (u'y - uy')` is strictly increasing where `u, y > 0` and `qu < qy`. -/
lemma kzt_W_strictMonoOn (hy : kzt_IsSol p qy y y') (hu : kzt_IsSol p qu u u')
    (hq : ∀ x ∈ Ioi (0:ℝ), qu x < qy x) {s : Set ℝ} (hs : s ⊆ Ioi (0:ℝ)) (hcv : Convex ℝ s)
    (hpos : ∀ x ∈ interior s, 0 < u x ∧ 0 < y x) : StrictMonoOn (kzt_W p u u' y y') s := by
  refine strictMonoOn_of_deriv_pos hcv (kzt_W_continuousOn hy hu hs) fun x hx => ?_
  have hx' := hs (interior_subset hx)
  rw [(kzt_hasDerivAt_W hy hu hx').deriv]
  have := hq x hx'
  have h2 := mul_pos (hpos x hx).1 (hpos x hx).2
  nlinarith

/-- Sign-normalized core of `kzt_between`. -/
lemma kzt_between_core (hy : kzt_IsSol p qy y y') (hu : kzt_IsSol p qu u u')
    (hq : ∀ x ∈ Ioi (0:ℝ), qy x < qu x) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (ya : y a = 0) (yb : y b = 0) (ypos : ∀ x ∈ Ioo a b, 0 < y x)
    (upos : ∀ x ∈ Ioo a b, 0 < u x) : False := by
  have hsub : Icc a b ⊆ Ioi (0:ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  have hanti := kzt_W_strictAntiOn hy hu hq hsub (convex_Icc a b) fun x hx => by
    rw [interior_Icc] at hx; exact ⟨upos x hx, ypos x hx⟩
  have hWab := hanti (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hab
  have ha' := hsub (left_mem_Icc.2 hab.le)
  have hb' := hsub (right_mem_Icc.2 hab.le)
  have hua := kzt_nonneg_left (hu a ha').1.continuousAt hab upos
  have hub := kzt_nonneg_right (hu b hb').1.continuousAt hab upos
  have hya := kzt_deriv_nonneg_right (hy a ha').1 ya hab ypos
  have hyb := kzt_deriv_nonpos_left (hy b hb').1 yb hab ypos
  have pa := hp a ha'
  have pb := hp b hb'
  simp only [kzt_W, ya, yb, mul_zero, zero_sub] at hWab
  have h1 : 0 ≤ p b * -(u b * y' b) := mul_nonneg pb.le (by nlinarith)
  have h2 : p a * -(u a * y' a) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos pa.le (by nlinarith [mul_nonneg hua hya])
  linarith

/-- **Sturm comparison.** If `qy < qu`, then between two consecutive zeros of `y` the function
`u` has a zero. -/
theorem kzt_between (hy : kzt_IsSol p qy y y') (hu : kzt_IsSol p qu u u')
    (hq : ∀ x ∈ Ioi (0:ℝ), qy x < qu x) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (ya : y a = 0) (yb : y b = 0) (hyne : ∀ x ∈ Ioo a b, y x ≠ 0) :
    ∃ c ∈ Ioo a b, u c = 0 := by
  by_contra hcon
  push Not at hcon
  have hsub : Ioo a b ⊆ Ioi (0:ℝ) := fun x hx => ha.trans hx.1
  rcases kzt_sign ordConnected_Ioo (hy.continuousOn hsub) hyne with hy1 | hy1 <;>
  rcases kzt_sign ordConnected_Ioo (hu.continuousOn hsub) hcon with hu1 | hu1
  · exact kzt_between_core hp hy hu hq ha hab ya yb hy1 hu1
  · exact kzt_between_core hp hy hu.neg hq ha hab ya yb hy1 fun x hx => neg_pos.mpr (hu1 x hx)
  · exact kzt_between_core hp hy.neg hu hq ha hab (by simp [ya]) (by simp [yb])
      (fun x hx => neg_pos.mpr (hy1 x hx)) hu1
  · exact kzt_between_core hp hy.neg hu.neg hq ha hab (by simp [ya]) (by simp [yb])
      (fun x hx => neg_pos.mpr (hy1 x hx)) fun x hx => neg_pos.mpr (hu1 x hx)

/-- Sign-normalized core of `kzt_upper_right`. -/
lemma kzt_upper_right_core (hy : kzt_IsSol p qy y y') (hu : kzt_IsSol p qu u u')
    (hq : ∀ x ∈ Ioi (0:ℝ), qy x < qu x) {z s₀ C K : ℝ} (hz : 0 < z)
    (hK : 0 < K) (yz : y z = 0) (ypos : ∀ x ∈ Ioi z, 0 < y x) (upos : ∀ x ∈ Ioi z, 0 < u x)
    (hC : ∀ x ∈ Ioi s₀, y x ≤ C * u x)
    (hb : ∀ x ∈ Ioi s₀, p x * u x ^ 2 ≤ K) : False := by
  have hsub : Ici z ⊆ Ioi (0:ℝ) := fun x hx => lt_of_lt_of_le hz hx
  have hanti := kzt_W_strictAntiOn hy hu hq hsub (convex_Ici z) fun x hx => by
    rw [interior_Ici] at hx; exact ⟨upos x hx, ypos x hx⟩
  have hz1 : z < z + 1 := by linarith
  have hWz : kzt_W p u u' y y' z ≤ 0 := by
    have hpz : ∀ x ∈ Ioo z (z + 1), 0 < u x := fun x hx => upos x hx.1
    have hpy : ∀ x ∈ Ioo z (z + 1), 0 < y x := fun x hx => ypos x hx.1
    have hua := kzt_nonneg_left (hu z hz).1.continuousAt hz1 hpz
    have hya := kzt_deriv_nonneg_right (hy z hz).1 yz hz1 hpy
    simp only [kzt_W, yz, mul_zero, zero_sub]
    exact mul_nonpos_of_nonneg_of_nonpos (hp z hz).le (by nlinarith [mul_nonneg hua hya])
  set s₁ := max z s₀ + 1 with hs₁
  have hzs : z < s₁ := by have := le_max_left z s₀; linarith
  have hs0s : s₀ < s₁ := by have := le_max_right z s₀; linarith
  have hW1 : kzt_W p u u' y y' s₁ < kzt_W p u u' y y' z :=
    hanti ((mem_Ici.2 le_rfl)) (mem_Ici.2 hzs.le) hzs
  have hIci : ∀ x ∈ Ici s₁, x ∈ Ioi z := fun x hx => lt_of_lt_of_le hzs hx
  have hIci0 : ∀ x ∈ Ici s₁, x ∈ Ioi s₀ := fun x hx => lt_of_lt_of_le hs0s hx
  obtain ⟨x, hx, hxC⟩ := kzt_ratio_top (p := p) (y := y) (u := u) (c₀ := -kzt_W p u u' y y' s₁)
    hK (by linarith)
    (fun x hx => (hy x (hsub (le_of_lt (hIci x hx)))).1)
    (fun x hx => (hu x (hsub (le_of_lt (hIci x hx)))).1)
    (fun x hx => upos x (hIci x hx)) (fun x hx => hp x (hsub (le_of_lt (hIci x hx))))
    (fun x hx => hb x (hIci0 x hx))
    (fun x hx => by
      have := hanti.antitoneOn (mem_Ici.2 hzs.le) (mem_Ici.2 (le_of_lt (hIci x hx))) hx
      linarith) C
  have hx' : x ∈ Ioi z := hIci x (le_of_lt hx)
  have := hC x (hIci0 x (le_of_lt hx))
  rw [lt_div_iff₀ (upos x hx')] at hxC
  linarith

/-- **Comparison at `∞`.** Let `qy < qu`, let `z` be the last zero of `y`, and let `y/u` stay
bounded and `p u² = O(1)` near `∞`. Then `u` has a zero in `(z, ∞)`. -/
theorem kzt_upper_right (hy : kzt_IsSol p qy y y') (hu : kzt_IsSol p qu u u')
    (hq : ∀ x ∈ Ioi (0:ℝ), qy x < qu x) {z s₀ C K : ℝ} (hz : 0 < z)
    (hK : 0 < K) (yz : y z = 0) (hyne : ∀ x ∈ Ioi z, y x ≠ 0)
    (hC : ∀ x ∈ Ioi s₀, |y x| ≤ C * |u x|)
    (hb : ∀ x ∈ Ioi s₀, p x * u x ^ 2 ≤ K) : ∃ c ∈ Ioi z, u c = 0 := by
  by_contra hcon
  push Not at hcon
  have hsub : Ioi z ⊆ Ioi (0:ℝ) := fun x hx => hz.trans hx
  have hb' : ∀ x ∈ Ioi s₀, p x * (-u x) ^ 2 ≤ K := fun x hx => by
    rw [neg_sq]; exact hb x hx
  have key : ∀ (y₁ y₁' u₁ u₁' : ℝ → ℝ), kzt_IsSol p qy y₁ y₁' → kzt_IsSol p qu u₁ u₁' →
      y₁ z = 0 → (∀ x ∈ Ioi z, 0 < y₁ x) → (∀ x ∈ Ioi z, 0 < u₁ x) →
      (∀ x ∈ Ioi s₀, |y₁ x| ≤ C * |u₁ x|) →
      (∀ x ∈ Ioi s₀, p x * u₁ x ^ 2 ≤ K) → False := by
    intro y₁ y₁' u₁ u₁' h1 h2 h3 h4 h5 h6 h7
    refine kzt_upper_right_core (s₀ := max z s₀) (C := C) hp h1 h2 hq hz hK h3 h4 h5
      (fun x hx => ?_) (fun x hx => h7 x (lt_of_le_of_lt (le_max_right _ _) hx))
    have hxz : x ∈ Ioi z := lt_of_le_of_lt (le_max_left _ _) hx
    have := h6 x (lt_of_le_of_lt (le_max_right _ _) hx)
    rwa [abs_of_pos (h4 x hxz), abs_of_pos (h5 x hxz)] at this
  have hCn1 : ∀ x ∈ Ioi s₀, |-y x| ≤ C * |u x| := fun x hx => by
    rw [abs_neg]; exact hC x hx
  have hCn2 : ∀ x ∈ Ioi s₀, |y x| ≤ C * |-u x| := fun x hx => by
    rw [abs_neg]; exact hC x hx
  have hCn3 : ∀ x ∈ Ioi s₀, |-y x| ≤ C * |-u x| := fun x hx => by
    rw [abs_neg, abs_neg]; exact hC x hx
  rcases kzt_sign ordConnected_Ioi (hy.continuousOn hsub) hyne with hy1 | hy1 <;>
  rcases kzt_sign ordConnected_Ioi (hu.continuousOn hsub) hcon with hu1 | hu1
  · exact key _ _ _ _ hy hu yz hy1 hu1 hC hb
  · exact key _ _ _ _ hy hu.neg yz hy1 (fun x hx => neg_pos.mpr (hu1 x hx)) hCn2 hb'
  · exact key _ _ _ _ hy.neg hu (by simp [yz]) (fun x hx => neg_pos.mpr (hy1 x hx)) hu1 hCn1 hb
  · exact key _ _ _ _ hy.neg hu.neg (by simp [yz]) (fun x hx => neg_pos.mpr (hy1 x hx))
      (fun x hx => neg_pos.mpr (hu1 x hx)) hCn3 hb'

/-- Sign-normalized core of `kzt_lower_right`. -/
lemma kzt_lower_right_core (hy : kzt_IsSol p qy y y') (hw : kzt_IsSol p qw w w')
    (hq : ∀ x ∈ Ioi (0:ℝ), qw x < qy x) {z s₀ K : ℝ} (hz : 0 < z)
    (hK : 0 < K) (wz : w z = 0) (ypos : ∀ x ∈ Ioi z, 0 < y x) (wpos : ∀ x ∈ Ioi z, 0 < w x)
    (hb : ∀ x ∈ Ioi s₀, p x * w x ^ 2 ≤ K) : False := by
  have hsub : Ici z ⊆ Ioi (0:ℝ) := fun x hx => lt_of_lt_of_le hz hx
  have hmono := kzt_W_strictMonoOn hy hw hq hsub (convex_Ici z) fun x hx => by
    rw [interior_Ici] at hx; exact ⟨wpos x hx, ypos x hx⟩
  have hz1 : z < z + 1 := by linarith
  have hWz : 0 ≤ kzt_W p w w' y y' z := by
    have hya := kzt_nonneg_left (hy z hz).1.continuousAt hz1 fun x hx => ypos x hx.1
    have hwa := kzt_deriv_nonneg_right (hw z hz).1 wz hz1 fun x hx => wpos x hx.1
    simp only [kzt_W, wz, zero_mul, sub_zero]
    exact mul_nonneg (hp z hz).le (mul_nonneg hwa hya)
  set s₁ := max z s₀ + 1 with hs₁
  have hzs : z < s₁ := by have := le_max_left z s₀; linarith
  have hs0s : s₀ < s₁ := by have := le_max_right z s₀; linarith
  have hW1 : kzt_W p w w' y y' z < kzt_W p w w' y y' s₁ :=
    hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hzs.le) hzs
  have hIci : ∀ x ∈ Ici s₁, x ∈ Ioi z := fun x hx => lt_of_lt_of_le hzs hx
  have hIci0 : ∀ x ∈ Ici s₁, x ∈ Ioi s₀ := fun x hx => lt_of_lt_of_le hs0s hx
  obtain ⟨x, hx, hxC⟩ := kzt_ratio_top (p := p) (y := fun x => -y x) (y' := fun x => -y' x)
    (u := w) (c₀ := kzt_W p w w' y y' s₁) hK (by linarith)
    (fun x hx => (hy x (hsub (le_of_lt (hIci x hx)))).1.neg)
    (fun x hx => (hw x (hsub (le_of_lt (hIci x hx)))).1)
    (fun x hx => wpos x (hIci x hx)) (fun x hx => hp x (hsub (le_of_lt (hIci x hx))))
    (fun x hx => hb x (hIci0 x hx))
    (fun x hx => by
      rw [kzt_W_neg]
      have := hmono.monotoneOn (mem_Ici.2 hzs.le) (mem_Ici.2 (le_of_lt (hIci x hx))) hx
      linarith) 0
  have hx' : x ∈ Ioi z := hIci x (le_of_lt hx)
  rw [neg_div, lt_neg, neg_zero] at hxC
  exact absurd hxC (not_lt.mpr (div_pos (ypos x hx') (wpos x hx')).le)

/-- Sign-normalized core of `kzt_lower_left`. -/
lemma kzt_lower_left_core (hy : kzt_IsSol p qy y y') (hw : kzt_IsSol p qw w w')
    (hq : ∀ x ∈ Ioi (0:ℝ), qw x < qy x) {z s₀ K : ℝ} (hz : 0 < z) (hs₀ : 0 < s₀)
    (hK : 0 < K) (wz : w z = 0) (ypos : ∀ x ∈ Ioo 0 z, 0 < y x)
    (wpos : ∀ x ∈ Ioo 0 z, 0 < w x)
    (hb : ∀ x ∈ Ioo 0 s₀, p x * w x ^ 2 ≤ K * x) : False := by
  have hsub : Ioc 0 z ⊆ Ioi (0:ℝ) := fun x hx => hx.1
  have hmono := kzt_W_strictMonoOn hy hw hq hsub (convex_Ioc 0 z) fun x hx => by
    rw [interior_Ioc] at hx; exact ⟨wpos x hx, ypos x hx⟩
  have hWz : kzt_W p w w' y y' z ≤ 0 := by
    have hya := kzt_nonneg_right (hy z hz).1.continuousAt hz ypos
    have hwa := kzt_deriv_nonpos_left (hw z hz).1 wz hz wpos
    simp only [kzt_W, wz, zero_mul, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (hp z hz).le
      (by nlinarith [mul_nonneg hya (neg_nonneg.mpr hwa)])
  set s₁ := min z s₀ / 2 with hs₁
  have hm : 0 < min z s₀ := lt_min hz hs₀
  have hzs : s₁ < z := by have := min_le_left z s₀; linarith
  have hs0s : s₁ < s₀ := by have := min_le_right z s₀; linarith
  have hs1 : 0 < s₁ := by linarith
  have hW1 : kzt_W p w w' y y' s₁ < kzt_W p w w' y y' z :=
    hmono ⟨hs1, hzs.le⟩ ⟨hz, le_rfl⟩ hzs
  have hIoc : ∀ x ∈ Ioc 0 s₁, x ∈ Ioc 0 z := fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  obtain ⟨x, hx, hxC⟩ := kzt_ratio_zero (p := p) (y := y) (u := w)
    (c₀ := -kzt_W p w w' y y' s₁) hs1 hK (by linarith)
    (fun x hx => (hy x (hsub (hIoc x hx))).1) (fun x hx => (hw x (hsub (hIoc x hx))).1)
    (fun x hx => wpos x ⟨hx.1, by linarith [hx.2]⟩) (fun x hx => hp x (hsub (hIoc x hx)))
    (fun x hx => hb x ⟨hx.1, by linarith [hx.2]⟩)
    (fun x hx => by
      have := hmono.monotoneOn (hIoc x hx) ⟨hs1, hzs.le⟩ hx.2
      linarith)
  have hx' : x ∈ Ioo 0 z := ⟨hx.1, by linarith [hx.2]⟩
  exact absurd hxC (not_lt.mpr (div_pos (ypos x hx') (wpos x hx')).le)

/-- Sign-normalized core of `kzt_lower_whole`. -/
lemma kzt_lower_whole_core (hy : kzt_IsSol p qy y y') (hw : kzt_IsSol p qw w w')
    (hq : ∀ x ∈ Ioi (0:ℝ), qw x < qy x) {s₀ s₀' K : ℝ} (hs₀' : 0 < s₀')
    (hK : 0 < K) (ypos : ∀ x ∈ Ioi 0, 0 < y x) (wpos : ∀ x ∈ Ioi 0, 0 < w x)
    (hb : ∀ x ∈ Ioi s₀, p x * w x ^ 2 ≤ K)
    (hb' : ∀ x ∈ Ioo 0 s₀', p x * w x ^ 2 ≤ K * x) : False := by
  have hmono := kzt_W_strictMonoOn hy hw hq subset_rfl (convex_Ioi 0) fun x hx => by
    rw [interior_Ioi] at hx; exact ⟨wpos x hx, ypos x hx⟩
  have h1 : (1:ℝ) ∈ Ioi (0:ℝ) := by norm_num
  by_cases hW0 : 0 ≤ kzt_W p w w' y y' 1
  · set s₁ := max 1 s₀ + 1 with hs₁
    have hzs : 1 < s₁ := by have := le_max_left 1 s₀; linarith
    have hs0s : s₀ < s₁ := by have := le_max_right 1 s₀; linarith
    have hS : ∀ x ∈ Ici s₁, x ∈ Ioi (0:ℝ) := fun x hx => by
      have : (0:ℝ) < s₁ := by linarith
      exact lt_of_lt_of_le this hx
    have hW1 : kzt_W p w w' y y' 1 < kzt_W p w w' y y' s₁ := hmono h1 (hS s₁ (mem_Ici.2 le_rfl)) hzs
    obtain ⟨x, hx, hxC⟩ := kzt_ratio_top (p := p) (y := fun x => -y x) (y' := fun x => -y' x)
      (u := w) (c₀ := kzt_W p w w' y y' s₁) hK (by linarith)
      (fun x hx => (hy x (hS x hx)).1.neg)
      (fun x hx => (hw x (hS x hx)).1) (fun x hx => wpos x (hS x hx))
      (fun x hx => hp x (hS x hx)) (fun x hx => hb x (lt_of_lt_of_le hs0s hx))
      (fun x hx => by
        rw [kzt_W_neg]
        have := hmono.monotoneOn (hS s₁ (mem_Ici.2 le_rfl)) (hS x hx) hx
        linarith) 0
    have hx' := hS x (le_of_lt hx)
    rw [neg_div, lt_neg, neg_zero] at hxC
    exact absurd hxC (not_lt.mpr (div_pos (ypos x hx') (wpos x hx')).le)
  · push Not at hW0
    set s₁ := min 1 s₀' / 2 with hs₁
    have hm : 0 < min 1 s₀' := lt_min (by norm_num) hs₀'
    have hzs : s₁ < 1 := by have := min_le_left 1 s₀'; linarith
    have hs0s : s₁ < s₀' := by have := min_le_right 1 s₀'; linarith
    have hs1 : 0 < s₁ := by linarith
    have hS : ∀ x ∈ Ioc 0 s₁, x ∈ Ioi (0:ℝ) := fun x hx => hx.1
    have hW1 : kzt_W p w w' y y' s₁ < kzt_W p w w' y y' 1 := hmono hs1 h1 hzs
    obtain ⟨x, hx, hxC⟩ := kzt_ratio_zero (p := p) (y := y) (u := w)
      (c₀ := -kzt_W p w w' y y' s₁) hs1 hK (by linarith)
      (fun x hx => (hy x (hS x hx)).1) (fun x hx => (hw x (hS x hx)).1)
      (fun x hx => wpos x (hS x hx)) (fun x hx => hp x (hS x hx))
      (fun x hx => hb' x ⟨hx.1, by linarith [hx.2]⟩)
      (fun x hx => by
        have := hmono.monotoneOn (hS x hx) hs1 hx.2
        linarith)
    exact absurd hxC (not_lt.mpr (div_pos (ypos x hx.1) (wpos x hx.1)).le)

omit hp in
/-- Bounds on `p w²` are unchanged by `w ↦ -w`. -/
lemma kzt_neg_sq_bound {S : Set ℝ} {g : ℝ → ℝ}
    (hb : ∀ x ∈ S, p x * w x ^ 2 ≤ g x) : ∀ x ∈ S, p x * (-w x) ^ 2 ≤ g x :=
  fun x hx => by rw [neg_sq]; exact hb x hx

/-- **Comparison at `∞` (lower function).** Let `qw < qy`, let `z` be the last zero of `w`, and
let `p w² = O(1)` near `∞`. Then `y` has a zero in `(z, ∞)`. -/
theorem kzt_lower_right (hy : kzt_IsSol p qy y y') (hw : kzt_IsSol p qw w w')
    (hq : ∀ x ∈ Ioi (0:ℝ), qw x < qy x) {z s₀ K : ℝ} (hz : 0 < z)
    (hK : 0 < K) (wz : w z = 0) (hwne : ∀ x ∈ Ioi z, w x ≠ 0)
    (hb : ∀ x ∈ Ioi s₀, p x * w x ^ 2 ≤ K) : ∃ c ∈ Ioi z, y c = 0 := by
  by_contra hcon
  push Not at hcon
  have hsub : Ioi z ⊆ Ioi (0:ℝ) := fun x hx => hz.trans hx
  have wz' : (fun x => -w x) z = 0 := by simp [wz]
  rcases kzt_sign ordConnected_Ioi (hy.continuousOn hsub) hcon with hy1 | hy1 <;>
  rcases kzt_sign ordConnected_Ioi (hw.continuousOn hsub) hwne with hu1 | hu1
  · exact kzt_lower_right_core hp hy hw hq hz hK wz hy1 hu1 hb
  · exact kzt_lower_right_core hp hy hw.neg hq hz hK wz' hy1 (fun x hx => neg_pos.mpr (hu1 x hx))
      (kzt_neg_sq_bound hb)
  · exact kzt_lower_right_core hp hy.neg hw hq hz hK wz (fun x hx => neg_pos.mpr (hy1 x hx))
      hu1 hb
  · exact kzt_lower_right_core hp hy.neg hw.neg hq hz hK wz'
      (fun x hx => neg_pos.mpr (hy1 x hx)) (fun x hx => neg_pos.mpr (hu1 x hx))
      (kzt_neg_sq_bound hb)

/-- **Comparison at `0` (lower function).** Let `qw < qy`, let `z` be the first zero of `w`, and
let `p w² = O(x)` near `0`. Then `y` has a zero in `(0, z)`. -/
theorem kzt_lower_left (hy : kzt_IsSol p qy y y') (hw : kzt_IsSol p qw w w')
    (hq : ∀ x ∈ Ioi (0:ℝ), qw x < qy x) {z s₀ K : ℝ} (hz : 0 < z) (hs₀ : 0 < s₀)
    (hK : 0 < K) (wz : w z = 0) (hwne : ∀ x ∈ Ioo 0 z, w x ≠ 0)
    (hb : ∀ x ∈ Ioo 0 s₀, p x * w x ^ 2 ≤ K * x) :
    ∃ c ∈ Ioo 0 z, y c = 0 := by
  by_contra hcon
  push Not at hcon
  have hsub : Ioo 0 z ⊆ Ioi (0:ℝ) := fun x hx => hx.1
  have wz' : (fun x => -w x) z = 0 := by simp [wz]
  rcases kzt_sign ordConnected_Ioo (hy.continuousOn hsub) hcon with hy1 | hy1 <;>
  rcases kzt_sign ordConnected_Ioo (hw.continuousOn hsub) hwne with hu1 | hu1
  · exact kzt_lower_left_core hp hy hw hq hz hs₀ hK wz hy1 hu1 hb
  · exact kzt_lower_left_core hp hy hw.neg hq hz hs₀ hK wz' hy1
      (fun x hx => neg_pos.mpr (hu1 x hx)) (kzt_neg_sq_bound hb)
  · exact kzt_lower_left_core hp hy.neg hw hq hz hs₀ hK wz (fun x hx => neg_pos.mpr (hy1 x hx))
      hu1 hb
  · exact kzt_lower_left_core hp hy.neg hw.neg hq hz hs₀ hK wz'
      (fun x hx => neg_pos.mpr (hy1 x hx)) (fun x hx => neg_pos.mpr (hu1 x hx))
      (kzt_neg_sq_bound hb)

/-- **Comparison on the whole half-line.** Let `qw < qy`, let `w` have no zeros in `(0, ∞)`,
`p w² = O(x)` near `0` and `p w² = O(1)` near `∞`. Then `y` has a zero in `(0, ∞)`. -/
theorem kzt_lower_whole (hy : kzt_IsSol p qy y y') (hw : kzt_IsSol p qw w w')
    (hq : ∀ x ∈ Ioi (0:ℝ), qw x < qy x) {s₀ s₀' K : ℝ} (hs₀' : 0 < s₀')
    (hK : 0 < K) (hwne : ∀ x ∈ Ioi 0, w x ≠ 0)
    (hb : ∀ x ∈ Ioi s₀, p x * w x ^ 2 ≤ K)
    (hb' : ∀ x ∈ Ioo 0 s₀', p x * w x ^ 2 ≤ K * x) :
    ∃ c ∈ Ioi 0, y c = 0 := by
  by_contra hcon
  push Not at hcon
  rcases kzt_sign ordConnected_Ioi (hy.continuousOn subset_rfl) hcon with hy1 | hy1 <;>
  rcases kzt_sign ordConnected_Ioi (hw.continuousOn subset_rfl) hwne with hu1 | hu1
  · exact kzt_lower_whole_core hp hy hw hq hs₀' hK hy1 hu1 hb hb'
  · exact kzt_lower_whole_core hp hy hw.neg hq hs₀' hK hy1 (fun x hx => neg_pos.mpr (hu1 x hx))
      (kzt_neg_sq_bound hb) (kzt_neg_sq_bound hb')
  · exact kzt_lower_whole_core hp hy.neg hw hq hs₀' hK (fun x hx => neg_pos.mpr (hy1 x hx)) hu1
      hb hb'
  · exact kzt_lower_whole_core hp hy.neg hw.neg hq hs₀' hK (fun x hx => neg_pos.mpr (hy1 x hx))
      (fun x hx => neg_pos.mpr (hu1 x hx)) (kzt_neg_sq_bound hb) (kzt_neg_sq_bound hb')

/-- **Lower zero count by comparison.** If `qw < qy` and the zeros of `w` in `(0, ∞)` are
exactly `e₀ < ⋯ < e_{j-1}`, with `p w² = O(x)` at `0` and `p w² = O(1)` at `∞`, then `y` has
`j+1` distinct zeros, one in each gap. -/
theorem kzt_lower_count (hy : kzt_IsSol p qy y y') (hw : kzt_IsSol p qw w w')
    (hq : ∀ x ∈ Ioi (0:ℝ), qw x < qy x) {j : ℕ} {e : Fin j → ℝ} (he : StrictMono e)
    (heI : ∀ i, 0 < e i) (hwz : ∀ x ∈ Ioi (0:ℝ), w x = 0 ↔ ∃ i, x = e i)
    {s₀ s₀' K : ℝ} (hs₀' : 0 < s₀') (hK : 0 < K)
    (hb : ∀ x ∈ Ioi s₀, p x * w x ^ 2 ≤ K)
    (hb' : ∀ x ∈ Ioo 0 s₀', p x * w x ^ 2 ≤ K * x) :
    ∃ c : Fin (j + 1) → ℝ, StrictMono c ∧ ∀ i, 0 < c i ∧ y (c i) = 0 := by
  have hgap : ∀ i : Fin (j + 1), ∃ c, 0 < c ∧
      (∀ h : i.val ≠ 0, e ⟨i.val - 1, by omega⟩ < c) ∧
      (∀ h : i.val ≠ j, c < e ⟨i.val, by omega⟩) ∧ y c = 0 := by
    intro i
    by_cases a : i.val = 0 <;> by_cases b : i.val = j
    · have hwne : ∀ x ∈ Ioi (0:ℝ), w x ≠ 0 := fun x hx h0 => by
        obtain ⟨k, -⟩ := (hwz x hx).1 h0
        exact absurd k.isLt (by omega)
      obtain ⟨c, hc, hc0⟩ := kzt_lower_whole hp hy hw hq hs₀' hK hwne hb hb'
      exact ⟨c, hc, fun h => absurd a h, fun h => absurd b h, hc0⟩
    · have hz := heI ⟨i.val, by omega⟩
      have hwne : ∀ x ∈ Ioo 0 (e ⟨i.val, by omega⟩), w x ≠ 0 := fun x hx h0 => by
        obtain ⟨k, rfl⟩ := (hwz x hx.1).1 h0
        have := he.lt_iff_lt.1 hx.2
        have : k.val < i.val := this
        omega
      obtain ⟨c, hc, hc0⟩ := kzt_lower_left hp hy hw hq hz hs₀' hK ((hwz _ hz).2 ⟨_, rfl⟩)
        hwne hb'
      exact ⟨c, hc.1, fun h => absurd a h, fun _ => hc.2, hc0⟩
    · have hz := heI ⟨i.val - 1, by omega⟩
      have hwne : ∀ x ∈ Ioi (e ⟨i.val - 1, by omega⟩), w x ≠ 0 := fun x hx h0 => by
        obtain ⟨k, rfl⟩ := (hwz x (hz.trans hx)).1 h0
        have := he.lt_iff_lt.1 hx
        have : i.val - 1 < k.val := this
        have := k.isLt
        omega
      obtain ⟨c, hc, hc0⟩ := kzt_lower_right hp hy hw hq hz hK ((hwz _ hz).2 ⟨_, rfl⟩) hwne hb
      exact ⟨c, hz.trans hc, fun _ => hc, fun h => absurd b h, hc0⟩
    · have hz1 := heI ⟨i.val - 1, by omega⟩
      have hz2 := heI ⟨i.val, by omega⟩
      have hlt : e ⟨i.val - 1, by omega⟩ < e ⟨i.val, by omega⟩ :=
        he (Fin.mk_lt_mk.2 (by omega))
      obtain ⟨c, hc, hc0⟩ := kzt_between hp hw hy hq hz1 hlt ((hwz _ hz1).2 ⟨_, rfl⟩)
        ((hwz _ hz2).2 ⟨_, rfl⟩) fun x hx h0 => by
          obtain ⟨k, rfl⟩ := (hwz x (hz1.trans hx.1)).1 h0
          have h1 : i.val - 1 < k.val := he.lt_iff_lt.1 hx.1
          have h2 : k.val < i.val := he.lt_iff_lt.1 hx.2
          omega
      exact ⟨c, hz1.trans hc.1, fun _ => hc.1, fun _ => hc.2, hc0⟩
  choose c hc0 hclo hchi hcz using hgap
  refine ⟨c, fun i₁ i₂ h12 => ?_, fun i => ⟨hc0 i, hcz i⟩⟩
  have h12' : i₁.val < i₂.val := h12
  have a : i₁.val ≠ j := by have := i₂.isLt; omega
  have b : i₂.val ≠ 0 := by omega
  have h1 := hchi i₁ a
  have h2 := hclo i₂ b
  have h3 : e ⟨i₁.val, by omega⟩ ≤ e ⟨i₂.val - 1, by omega⟩ :=
    he.monotone (Fin.mk_le_mk.2 (by omega))
  linarith

/-- **Upper zero count by comparison.** If `qy < qu`, the zeros of `u` in `(0, ∞)` are among
`e₀, …, e_{k-1}`, the zeros of `y` are simple and stay away from `∞`, `y/u` is bounded and
`p u² = O(1)` near `∞`, then `y` has at most `k` zeros in `(0, ∞)`. -/
theorem kzt_upper_count (hy : kzt_IsSol p qy y y') (hu : kzt_IsSol p qu u u')
    (hq : ∀ x ∈ Ioi (0:ℝ), qy x < qu x) {k : ℕ} {e : Fin k → ℝ}
    (huz : ∀ x ∈ Ioi (0:ℝ), u x = 0 → ∃ i, x = e i)
    (hsimple : ∀ x ∈ Ioi (0:ℝ), y x = 0 → y' x ≠ 0) {δ : ℝ}
    (hnear : ∀ x ∈ Ioi δ, y x ≠ 0) {s₀ C K : ℝ} (hK : 0 < K)
    (hC : ∀ x ∈ Ioi s₀, |y x| ≤ C * |u x|)
    (hb : ∀ x ∈ Ioi s₀, p x * u x ^ 2 ≤ K) :
    {x | 0 < x ∧ y x = 0}.Finite ∧ {x | 0 < x ∧ y x = 0}.ncard ≤ k := by
  set Z := {x | 0 < x ∧ y x = 0} with hZ
  have claim : ∀ T : Finset ℝ, (↑T : Set ℝ) ⊆ Z → T.card ≤ k := by
    intro T hT
    by_contra hlt
    push Not at hlt
    set n := T.card with hn
    let f := T.orderEmbOfFin hn.symm
    have hfZ : ∀ i, f i ∈ Z := fun i => hT (T.orderEmbOfFin_mem hn.symm i)
    have hgap : ∀ i : Fin n, ∃ c, f i < c ∧ (∀ h : i.val + 1 < n, c < f ⟨i.val + 1, h⟩) ∧
        u c = 0 := by
      intro i
      have ha := hfZ i
      by_cases h : i.val + 1 < n
      · have hb' := hfZ ⟨i.val + 1, h⟩
        have hab : f i < f ⟨i.val + 1, h⟩ := f.strictMono (Fin.mk_lt_mk.2 (by omega))
        have hsub : Icc (f i) (f ⟨i.val + 1, h⟩) ⊆ Ioi (0:ℝ) := fun x hx =>
          lt_of_lt_of_le ha.1 hx.1
        have hfin := ODE.sturmDef_finite (f' := y') (fun x hx => (hy x (hsub hx)).1)
          (fun x hx h0 => hsimple x (hsub hx) h0)
        set S := {x | x ∈ Ioc (f i) (f ⟨i.val + 1, h⟩) ∧ y x = 0} with hS
        have hSfin : S.Finite := hfin.subset fun x hx => ⟨Ioc_subset_Icc_self hx.1, hx.2⟩
        have hSne : hSfin.toFinset.Nonempty :=
          (Set.Finite.toFinset_nonempty hSfin).2 ⟨_, ⟨⟨hab, le_rfl⟩, hb'.2⟩⟩
        have hzS : hSfin.toFinset.min' hSne ∈ S := hSfin.mem_toFinset.1 (Finset.min'_mem _ _)
        have hmin : ∀ x ∈ S, hSfin.toFinset.min' hSne ≤ x := fun x hx =>
          Finset.min'_le _ _ (hSfin.mem_toFinset.2 hx)
        obtain ⟨c, hc, hc0⟩ := kzt_between hp hy hu hq ha.1 hzS.1.1
          ha.2 hzS.2 fun x hx h0 => by
            have := hmin x ⟨⟨hx.1, hx.2.le.trans hzS.1.2⟩, h0⟩
            linarith [hx.2]
        exact ⟨c, hc.1, fun _ => hc.2.trans_le hzS.1.2, hc0⟩
      · set d := max δ (f i) with hd
        have hsub : Icc (f i) d ⊆ Ioi (0:ℝ) := fun x hx => lt_of_lt_of_le ha.1 hx.1
        have hfin := ODE.sturmDef_finite (f' := y') (fun x hx => (hy x (hsub hx)).1)
          (fun x hx h0 => hsimple x (hsub hx) h0)
        have hSne : hfin.toFinset.Nonempty :=
          (Set.Finite.toFinset_nonempty hfin).2 ⟨_, ⟨⟨le_rfl, le_max_right _ _⟩, ha.2⟩⟩
        have hzS := hfin.mem_toFinset.1 (Finset.max'_mem _ hSne)
        have hmax : ∀ x ∈ {x | x ∈ Icc (f i) d ∧ y x = 0}, x ≤ hfin.toFinset.max' hSne :=
          fun x hx => Finset.le_max' _ _ (hfin.mem_toFinset.2 hx)
        obtain ⟨c, hc, hc0⟩ := kzt_upper_right hp hy hu hq (hsub hzS.1) hK hzS.2
          (fun x hx h0 => by
            by_cases hxd : x ≤ d
            · have := hmax x ⟨⟨hzS.1.1.trans (le_of_lt hx), hxd⟩, h0⟩
              linarith [mem_Ioi.1 hx]
            · exact hnear x (lt_of_le_of_lt (le_max_left _ _) (not_le.mp hxd)) h0) hC hb
        exact ⟨c, lt_of_le_of_lt hzS.1.1 hc, fun h' => absurd h' h, hc0⟩
    choose g hg hg' hg0 using hgap
    have hgI : ∀ i, g i ∈ Ioi (0:ℝ) := fun i => (hfZ i).1.trans (hg i)
    have hgm : StrictMono g := fun i₁ i₂ h12 => by
      have h12' : i₁.val < i₂.val := h12
      have a : i₁.val + 1 < n := by have := i₂.isLt; omega
      have : f ⟨i₁.val + 1, a⟩ ≤ f i₂ := f.monotone (Fin.mk_le_mk.2 (by omega))
      linarith [hg' i₁ a, hg i₂]
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

/-! ### Tricomi's `U` on the positive real axis -/

section Kummer

open Complex DLMF.Hypergeometric DLMF.OrthogonalPolynomials

/-- `U(a,b,x)` on the positive real axis, as a real function (its real part). -/
def kzt_U (a b : ℝ) (x : ℝ) : ℝ := (kummerU (a : ℂ) (b : ℂ) (x : ℂ)).re

/-- The derivative `-a U(a+1,b+1,x)` of `kzt_U` (DLMF 13.3.22). -/
def kzt_dU (a b : ℝ) (x : ℝ) : ℝ := -a * (kummerU ((a : ℂ) + 1) ((b : ℂ) + 1) (x : ℂ)).re

/-- The weight `p(x) = x^b e^{-x}` of the self-adjoint form of Kummer's equation. -/
def kzt_p (b : ℝ) (x : ℝ) : ℝ := x ^ b * Real.exp (-x)

/-- The coefficient `q(x) = -a x^{b-1} e^{-x}` of the self-adjoint form of Kummer's equation. -/
def kzt_q (a b : ℝ) (x : ℝ) : ℝ := -a * (x ^ (b - 1) * Real.exp (-x))

/-- The weight `x^b e^{-x}` is positive on `(0, ∞)`. -/
lemma kzt_p_pos (b : ℝ) : ∀ x ∈ Ioi (0:ℝ), 0 < kzt_p b x := fun _ hx =>
  mul_pos (Real.rpow_pos_of_pos hx b) (Real.exp_pos _)

/-- `U(a,b,x)` is real for real `a`, `b` and `x > 0`. -/
lemma kzt_U_im (a b : ℝ) {x : ℝ} (hx : 0 < x) : (kummerU (a : ℂ) (b : ℂ) (x : ℂ)).im = 0 := by
  have h := conj_kummerU (a : ℂ) (b : ℂ) (z := (x : ℂ)) (ofReal_mem_slitPlane.2 hx)
  simp only [conj_ofReal] at h
  exact conj_eq_iff_im.mp h

/-- `U(a,b,x)` equals the real number `kzt_U a b x` for `x > 0`. -/
lemma kzt_U_eq (a b : ℝ) {x : ℝ} (hx : 0 < x) :
    kummerU (a : ℂ) (b : ℂ) (x : ℂ) = (kzt_U a b x : ℂ) :=
  Complex.ext (by simp [kzt_U]) (by simp [kzt_U_im a b hx])

/-- The shifted values `U(a+k, b+k, x)` are real. -/
lemma kzt_U_eq_add (a b : ℝ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    kummerU ((a : ℂ) + k) ((b : ℂ) + k) (x : ℂ) =
      ((kummerU ((a : ℂ) + k) ((b : ℂ) + k) (x : ℂ)).re : ℂ) := by
  have h := kzt_U_eq (a + k) (b + k) hx
  push_cast at h
  rw [h]; simp [kzt_U]

/-- **Self-adjoint form of Kummer's equation.** For real `a`, `b`, the function `U(a,b,·)`
solves `(x^b e^{-x} y')' - a x^{b-1} e^{-x} y = 0` on `(0, ∞)` (DLMF 13.2.1 with 13.3.22). -/
theorem kzt_U_isSol (a b : ℝ) : kzt_IsSol (kzt_p b) (kzt_q a b) (kzt_U a b) (kzt_dU a b) := by
  intro x hx
  have hx' : (0:ℝ) < x := hx
  have hz : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 hx'
  refine ⟨?_, ?_⟩
  · have h := (hasDerivAt_kummerU (a : ℂ) (b : ℂ) hz).real_of_complex
    refine h.congr_deriv ?_
    simp only [kzt_dU]
    rw [show -(a : ℂ) * kummerU ((a : ℂ) + 1) ((b : ℂ) + 1) x =
      ((-a : ℝ) : ℂ) * kummerU ((a : ℂ) + 1) ((b : ℂ) + 1) x by push_cast; ring, re_ofReal_mul]
  · have h1 := (hasDerivAt_kummerU ((a : ℂ) + 1) ((b : ℂ) + 1) hz).real_of_complex
    have hdU : HasDerivAt (kzt_dU a b)
        (-a * (-(a + 1) * (kummerU ((a : ℂ) + 2) ((b : ℂ) + 2) (x : ℂ)).re)) x := by
      refine (h1.const_mul (-a)).congr_deriv ?_
      rw [show -((a : ℂ) + 1) * kummerU ((a : ℂ) + 1 + 1) ((b : ℂ) + 1 + 1) x =
        ((-(a + 1) : ℝ) : ℂ) * kummerU ((a : ℂ) + 2) ((b : ℂ) + 2) x by
          push_cast; ring_nf, re_ofReal_mul]
    have hpow := Real.hasDerivAt_rpow_const (x := x) (p := b) (Or.inl hx'.ne')
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-x) * (-1)) x :=
      (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    have hp : HasDerivAt (kzt_p b) (b * x ^ (b - 1) * Real.exp (-x) +
        x ^ b * (Real.exp (-x) * (-1))) x := hpow.mul hexp
    have hprod := hp.mul hdU
    convert hprod using 1
    -- the contiguous relation 13.3.14 at `x`
    have hc := kummerU_ode_contiguous (a : ℂ) (b : ℂ) (x : ℂ) (ofReal_ne_zero.2 hx'.ne')
    have e1 := kzt_U_eq_add a b 1 hx'
    have e2 := kzt_U_eq_add a b 2 hx'
    push_cast at e1 e2
    rw [e1, e2, kzt_U_eq a b hx'] at hc
    set U0 := kzt_U a b x
    set U1 := (kummerU ((a : ℂ) + 1) ((b : ℂ) + 1) (x : ℂ)).re
    set U2 := (kummerU ((a : ℂ) + 2) ((b : ℂ) + 2) (x : ℂ)).re
    have hr : (a + 1) * x * U2 + (x - b) * U1 - U0 = 0 := by exact_mod_cast hc
    have hxb : x ^ b = x * x ^ (b - 1) := by
      rw [Real.rpow_sub_one hx'.ne']; field_simp
    simp only [kzt_q, kzt_p, kzt_dU]
    rw [hxb]
    linear_combination (-(a * x ^ (b - 1) * Real.exp (-x))) * hr

/-- **Simple zeros.** For `a ∉ -ℕ`, the zeros of `U(a,b,·)` on `(0, ∞)` are simple, by the
Wronskian 13.2.34 of `𝐌(a,b,·)` and `U(a,b,·)`. -/
theorem kzt_U_simple (a b : ℝ) (ha : ∀ n : ℕ, a ≠ -(n : ℝ)) :
    ∀ x ∈ Ioi (0:ℝ), kzt_U a b x = 0 → kzt_dU a b x ≠ 0 := by
  intro x hx h0 hd
  have hx' : (0:ℝ) < x := hx
  have hz : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 hx'
  have ha' : ∀ k : ℕ, (a : ℂ) ≠ -(k : ℂ) := fun k h => ha k (by exact_mod_cast h)
  have hW := wronskian_regularizedHGFun_kummerU (a : ℂ) (b : ℂ) hz ha'
  have hU : kummerU (a : ℂ) (b : ℂ) (x : ℂ) = 0 := by rw [kzt_U_eq a b hx', h0]; simp
  have hdU : deriv (kummerU (a : ℂ) (b : ℂ)) (x : ℂ) = 0 := by
    have e1 := kzt_U_eq_add a b 1 hx'
    push_cast at e1
    rw [deriv_kummerU _ _ hz, e1]
    simp only [kzt_dU] at hd
    rw [show -(a : ℂ) * ((kummerU ((a : ℂ) + 1) ((b : ℂ) + 1) (x : ℂ)).re : ℂ) =
      ((-a * (kummerU ((a : ℂ) + 1) ((b : ℂ) + 1) (x : ℂ)).re : ℝ) : ℂ) by push_cast; ring, hd]
    simp
  simp only [wronskian, hU, hdU, mul_zero, zero_mul, sub_zero] at hW
  have hG : Gamma (a : ℂ) ≠ 0 := Gamma_ne_zero ha'
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx'.ne'
  have hpw : (x : ℂ) ^ (-(b : ℂ)) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hx0 h.1
  have : -((x : ℂ) ^ (-(b : ℂ)) * exp (x : ℂ)) / Gamma (a : ℂ) ≠ 0 :=
    div_ne_zero (neg_ne_zero.2 (mul_ne_zero hpw (exp_ne_zero _))) hG
  exact this hW.symm

/-- **Behaviour at `∞`.** `U(a,b,x) x^a → 1` as `x → ∞` (DLMF 13.2.6), for real parameters. -/
theorem kzt_U_asymp (a b : ℝ) : Tendsto (fun x => kzt_U a b x * x ^ a) atTop (𝓝 1) := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_kummerU_mul_cpow_atTop (a : ℂ) (b : ℂ))
  rw [one_re] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Function.comp_apply]
  rw [kzt_U_eq a b hx, ← ofReal_cpow hx.le, ← ofReal_mul, ofReal_re]

/-- Two-sided bounds `x^{-a}/2 ≤ U(a,b,x) ≤ 2 x^{-a}` for large `x`. -/
theorem kzt_U_eventually (a b : ℝ) :
    ∀ᶠ x in atTop, x ^ (-a) / 2 ≤ kzt_U a b x ∧ kzt_U a b x ≤ 2 * x ^ (-a) := by
  have h := kzt_U_asymp a b
  filter_upwards [h.eventually (Ioo_mem_nhds (show (1:ℝ)/2 < 1 by norm_num)
    (show (1:ℝ) < 2 by norm_num)), eventually_gt_atTop 0] with x hx hx0
  have hp : 0 < x ^ a := Real.rpow_pos_of_pos hx0 a
  have hneg : x ^ (-a) = (x ^ a)⁻¹ := Real.rpow_neg hx0.le a
  rw [hneg]
  obtain ⟨h1, h2⟩ := hx
  constructor
  · rw [show (x ^ a)⁻¹ / 2 = (1 / 2) / x ^ a by field_simp, div_le_iff₀ hp]; linarith
  · rw [show 2 * (x ^ a)⁻¹ = 2 / x ^ a by ring, le_div_iff₀ hp]; linarith

/-- **Polynomial case.** For `b > 0` and `n ∈ ℕ`, the positive zeros of `U(-n,b,·)` are those of
the Laguerre polynomial `L_n^{(b-1)}` (DLMF 13.6.19 and 18.16(iv)), `n` simple points. -/
theorem kzt_base_zeros {b : ℝ} (hb : 0 < b) (n : ℕ) :
    ∃ e : Fin n → ℝ, StrictMono e ∧ (∀ i, 0 < e i) ∧
      ∀ x ∈ Ioi (0:ℝ), kzt_U (-(n : ℝ)) b x = 0 ↔ ∃ i, x = e i := by
  obtain ⟨e, he, hpos, hz⟩ := laguerrePolyL_zeros_pos (α := b - 1) (by linarith) n
  refine ⟨e, he, hpos, fun x hx => ?_⟩
  have hα : ∀ k : ℕ, (((b - 1 : ℝ) : ℂ)) + 1 ≠ -(k : ℂ) := fun k h => by
    have : ((b : ℝ) : ℂ) = -(k : ℂ) := by push_cast at h ⊢; linear_combination h
    have h2 : b = -(k : ℝ) := by exact_mod_cast this
    have := k.cast_nonneg (α := ℝ); linarith
  have hL := (kummerU_laguerrePolyL n ((b - 1 : ℝ) : ℂ) (x : ℂ) hα).2
  rw [show ((b - 1 : ℝ) : ℂ) + 1 = (b : ℂ) by push_cast; ring] at hL
  have hcast : ((-(n : ℝ) : ℝ) : ℂ) = -(n : ℂ) := by push_cast; ring
  rw [← ofReal_eq_zero, ← kzt_U_eq _ _ (show (0:ℝ) < x from hx), hcast, hL]
  have hne : (-1 : ℂ) ^ n * (n.factorial : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast n.factorial_ne_zero)
  rw [mul_eq_zero, or_iff_right hne, hz]
  simp only [ofReal_inj]

/-- `U(-n,b,x)` is a real polynomial in `x`, times `(-1)ⁿ n!`. -/
lemma kzt_base_poly {b : ℝ} (hb : 0 < b) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    kzt_U (-(n : ℝ)) b x = (-1) ^ n * n.factorial * (laguerrePolyLR (b - 1) n).eval x := by
  have hα : ∀ k : ℕ, (((b - 1 : ℝ) : ℂ)) + 1 ≠ -(k : ℂ) := fun k h => by
    have : ((b : ℝ) : ℂ) = -(k : ℂ) := by push_cast at h ⊢; linear_combination h
    have h2 : b = -(k : ℝ) := by exact_mod_cast this
    have := k.cast_nonneg (α := ℝ); linarith
  have hL := (kummerU_laguerrePolyL n ((b - 1 : ℝ) : ℂ) (x : ℂ) hα).2
  rw [show ((b - 1 : ℝ) : ℂ) + 1 = (b : ℂ) by push_cast; ring] at hL
  have hcast : ((-(n : ℝ) : ℝ) : ℂ) = -(n : ℂ) := by push_cast; ring
  have hP : laguerrePolyL ((b - 1 : ℝ) : ℂ) n (x : ℂ) =
      (((laguerrePolyLR (b - 1) n).eval x : ℝ) : ℂ) := by
    rw [← eval_map_laguerrePolyLR, Polynomial.eval_map_algebraMap,
      ← Complex.coe_algebraMap, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
  apply ofReal_injective
  rw [← kzt_U_eq _ _ hx, hcast, hL, hP]
  push_cast; ring

/-- **Weight bounds for the polynomial case.** For `b ≥ 1`, `p U(-n,b,·)² = O(x)` on `(0, 1)` and
`p U(-n,b,·)² = O(1)` near `∞`. -/
theorem kzt_base_bounds {b : ℝ} (hb : 1 ≤ b) (n : ℕ) :
    ∃ K > 0, (∀ x ∈ Ioo (0:ℝ) 1, kzt_p b x * kzt_U (-(n : ℝ)) b x ^ 2 ≤ K * x) ∧
      ∃ s₀, ∀ x ∈ Ioi s₀, kzt_p b x * kzt_U (-(n : ℝ)) b x ^ 2 ≤ K := by
  set P := laguerrePolyLR (b - 1) n
  obtain ⟨Mp, hMp⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (P.continuous.continuousOn (s := Icc (0:ℝ) 1))
  set K := (n.factorial : ℝ) ^ 2 * Mp ^ 2 + 1 with hK
  have hK0 : 0 < K := by positivity
  refine ⟨K, hK0, fun x hx => ?_, ?_⟩
  · rw [kzt_base_poly (by linarith) n hx.1]
    have hM := hMp x (Ioo_subset_Icc_self hx)
    rw [Real.norm_eq_abs] at hM
    have hsq : ((-1) ^ n * (n.factorial : ℝ) * P.eval x) ^ 2 ≤ K := by
      rw [mul_pow, mul_pow,
        show ((-1:ℝ) ^ n) ^ 2 = 1 by rw [← pow_mul, mul_comm, pow_mul]; norm_num, one_mul]
      have : P.eval x ^ 2 ≤ Mp ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hM 2
      nlinarith [sq_nonneg (n.factorial : ℝ)]
    have hp1 : kzt_p b x ≤ x := by
      simp only [kzt_p]
      have h1 : x ^ b ≤ x ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2.le hb
      rw [Real.rpow_one] at h1
      have h2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [hx.1])
      have h3 : 0 ≤ x ^ b := (Real.rpow_pos_of_pos hx.1 b).le
      nlinarith [Real.exp_pos (-x)]
    have hp0 : 0 ≤ kzt_p b x := (kzt_p_pos b x hx.1).le
    calc kzt_p b x * _ ≤ x * K := mul_le_mul hp1 hsq (sq_nonneg _) hx.1.le
      _ = K * x := by ring
  · have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b + 2 * n) 1 one_pos
    have hev := (hlim.eventually (gt_mem_nhds (show (0:ℝ) < 1 / 4 by norm_num))).and
      ((kzt_U_eventually (-(n : ℝ)) b).and (eventually_gt_atTop 0))
    obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 hev
    refine ⟨s₀, fun x hx => ?_⟩
    obtain ⟨h1, ⟨h2, h3⟩, hx0⟩ := hs₀ x (le_of_lt hx)
    rw [neg_neg] at h2 h3
    have hxn : x ^ (n : ℝ) = x ^ n := Real.rpow_natCast x n
    rw [hxn] at h2 h3
    have hxn0 : 0 < x ^ n := pow_pos hx0 n
    have hU2 : kzt_U (-(n : ℝ)) b x ^ 2 ≤ 4 * (x ^ n) ^ 2 := by
      have : 0 ≤ kzt_U (-(n : ℝ)) b x := by linarith
      nlinarith
    have hpow : x ^ (b + 2 * n) = x ^ b * (x ^ n) ^ 2 := by
      rw [Real.rpow_add hx0, ← pow_mul, show (2 * (n : ℝ)) = ((n * 2 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    rw [hpow, neg_one_mul] at h1
    have hp0 : 0 ≤ kzt_p b x := (kzt_p_pos b x hx0).le
    simp only [kzt_p] at hp0 ⊢
    calc x ^ b * Real.exp (-x) * kzt_U (-(n : ℝ)) b x ^ 2
        ≤ x ^ b * Real.exp (-x) * (4 * (x ^ n) ^ 2) := mul_le_mul_of_nonneg_left hU2 hp0
      _ = 4 * (x ^ b * (x ^ n) ^ 2 * Real.exp (-x)) := by ring
      _ ≤ 4 * (1 / 4) := by linarith
      _ ≤ K := by rw [hK]; nlinarith [sq_nonneg ((n.factorial : ℝ) * Mp)]

/-- The coefficients `q` are ordered by the first parameter. -/
lemma kzt_q_lt {a a' : ℝ} (b : ℝ) (h : a' < a) : ∀ x ∈ Ioi (0:ℝ), kzt_q a b x < kzt_q a' b x :=
  fun x hx => by
    have : 0 < x ^ (b - 1) * Real.exp (-x) :=
      mul_pos (Real.rpow_pos_of_pos hx _) (Real.exp_pos _)
    simp only [kzt_q]; nlinarith

/-- **Zero count of `U(a,b,·)` on `(0, ∞)`.** For `b ≥ 1` and `a < 0` nonintegral, `U(a,b,x)`
has exactly `⌈-a⌉` positive zeros. With `n = ⌊-a⌋`, the count is squeezed between Sturm
comparisons with the polynomial cases `U(-n,b,·)` and `U(-n-1,b,·)`. -/
theorem kzt_U_posZeros_count {a b : ℝ} (hb : 1 ≤ b) (ha : a < 0) (hai : ∀ n : ℤ, a ≠ n) :
    {x : ℝ | 0 < x ∧ kummerU (a : ℂ) (b : ℂ) (x : ℂ) = 0}.encard = Int.toNat ⌈-a⌉ := by
  set Z := {x : ℝ | 0 < x ∧ kummerU (a : ℂ) (b : ℂ) (x : ℂ) = 0} with hZ
  have hZ' : Z = {x | 0 < x ∧ kzt_U a b x = 0} := by
    ext x
    simp only [hZ, mem_ofPred_eq]
    constructor
    · rintro ⟨hx, h0⟩; exact ⟨hx, by simp [kzt_U, h0]⟩
    · rintro ⟨hx, h0⟩; exact ⟨hx, by rw [kzt_U_eq a b hx, h0]; simp⟩
  -- `n = ⌊-a⌋`, so that `n < -a < n + 1`
  set n := (⌊-a⌋).toNat with hn
  have hfl : (0:ℤ) ≤ ⌊-a⌋ := Int.floor_nonneg.2 (by linarith)
  have hnz : (n : ℤ) = ⌊-a⌋ := Int.toNat_of_nonneg hfl
  have hn1 : (n : ℝ) < -a := by
    have h1 : ((⌊-a⌋ : ℤ) : ℝ) ≤ -a := Int.floor_le _
    have h2 : ((⌊-a⌋ : ℤ) : ℝ) ≠ -a := fun h => hai (-⌊-a⌋) (by push_cast; linarith)
    have : ((n : ℤ) : ℝ) = ((⌊-a⌋ : ℤ) : ℝ) := by rw [hnz]
    push_cast at this
    rw [this]; exact lt_of_le_of_ne h1 h2
  have hn2 : -a < (n : ℝ) + 1 := by
    have h1 := Int.lt_floor_add_one (-a)
    have : ((n : ℤ) : ℝ) = ((⌊-a⌋ : ℤ) : ℝ) := by rw [hnz]
    push_cast at this
    rw [this]; exact h1
  have hceil : Int.toNat ⌈-a⌉ = n + 1 := by
    have h1 : ⌈-a⌉ ≤ (n : ℤ) + 1 := Int.ceil_le.2 (by push_cast; linarith)
    have h2 : (n : ℤ) < ⌈-a⌉ := Int.lt_ceil.2 (by push_cast; linarith)
    omega
  have hai' : ∀ m : ℕ, a ≠ -(m : ℝ) := fun m h => hai (-(m : ℤ)) (by push_cast; exact h)
  have hb0 : 0 < b := by linarith
  have hp := kzt_p_pos b
  have hy := kzt_U_isSol a b
  -- the upper bound, by comparison with `U(-n-1,b,·)`
  have hupper : Z.Finite ∧ Z.ncard ≤ n + 1 := by
    rw [hZ']
    obtain ⟨e, -, -, hez⟩ := kzt_base_zeros hb0 (n + 1)
    obtain ⟨K, hK, -, s₁, hs₁⟩ := kzt_base_bounds hb (n + 1)
    have hev := ((kzt_U_eventually a b).and (kzt_U_eventually (-((n + 1 : ℕ) : ℝ)) b)).and
      (eventually_ge_atTop (1:ℝ))
    obtain ⟨s₂, hs₂⟩ := eventually_atTop.1 hev
    refine kzt_upper_count hp hy (kzt_U_isSol (-((n + 1 : ℕ) : ℝ)) b)
      (kzt_q_lt b (by push_cast; linarith)) (e := e) (fun x hx h0 => (hez x hx).1 h0)
      (kzt_U_simple a b hai') (δ := s₂) (fun x hx => ?_) (s₀ := max s₁ s₂) (C := 4) hK
      (fun x hx => ?_) (fun x hx => hs₁ x (lt_of_le_of_lt (le_max_left _ _) hx))
    · obtain ⟨⟨⟨h1, -⟩, -⟩, h3⟩ := hs₂ x (le_of_lt hx)
      have : 0 < x ^ (-a) / 2 := by
        have := Real.rpow_pos_of_pos (show (0:ℝ) < x by linarith) (-a); linarith
      linarith
    · have hx2 : s₂ ≤ x := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx)
      obtain ⟨⟨⟨h1, h2⟩, ⟨h3, -⟩⟩, h5⟩ := hs₂ x hx2
      rw [neg_neg] at h3
      have hx0 : (0:ℝ) < x := by linarith
      have hpa : 0 < x ^ (-a) := Real.rpow_pos_of_pos hx0 _
      have hle : x ^ (-a) ≤ x ^ (((n + 1 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le h5 (by push_cast; linarith)
      have hu0 : 0 < kzt_U (-((n + 1 : ℕ) : ℝ)) b x := by
        have := Real.rpow_pos_of_pos hx0 (((n + 1 : ℕ) : ℝ)); linarith
      rw [abs_of_pos (by linarith), abs_of_pos hu0]
      linarith
  -- the lower bound, by comparison with `U(-n,b,·)`
  obtain ⟨e, he, heI, hez⟩ := kzt_base_zeros hb0 n
  obtain ⟨K, hK, hK0, s₁, hs₁⟩ := kzt_base_bounds hb n
  obtain ⟨cz, hcz, hczZ⟩ := kzt_lower_count hp hy (kzt_U_isSol (-(n : ℝ)) b)
    (kzt_q_lt b (by linarith)) he heI hez (s₀ := s₁) (s₀' := 1) one_pos hK hs₁ hK0
  have hsub : range cz ⊆ Z := by
    rintro _ ⟨i, rfl⟩
    rw [hZ']
    exact hczZ i
  have hlow := ncard_le_ncard hsub hupper.1
  rw [ncard_range_of_injective hcz.injective, Nat.card_eq_fintype_card, Fintype.card_fin] at hlow
  rw [hceil, ← hupper.1.cast_ncard_eq, le_antisymm hupper.2 hlow]

end Kummer

/-! ### Tricomi's `U` on the negative real axis -/

section NegativeAxis

open Complex DLMF.Hypergeometric
open scoped Real

/-- **DLMF 13.2.41 on the negative real axis.** For `x < 0`, where the principal branch has
`ph x = π`, the lower-sign connection formula
`𝐌(a,b,x) = e^{πia} U(a,b,x)/Γ(b-a) + e^{-πi(b-a)} e^x U(b-a,b,-x)/Γ(a)` holds for all complex
`a`, `b`. -/
theorem kzt_connection_neg (a b : ℂ) {x : ℝ} (hx : x < 0) :
    regularizedHGFun {a} {b} (x : ℂ) =
      exp (a * π * I) / Gamma (b - a) * kummerU a b x +
        exp (-(b - a) * π * I) / Gamma a * exp (x : ℂ) * kummerU (b - a) b (-(x : ℂ)) := by
  have hz0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne
  have harg : arg (x : ℂ) = π := arg_ofReal_of_neg hx
  have hc : ∀ w : ℂ, (-(x : ℂ)) ^ w = (x : ℂ) ^ w * exp ((-1) * π * I * w) := by
    refine neg_cpow_of_arg hz0 (-1) (Or.inr rfl) ?_ ?_ <;> rw [harg] <;> simp <;>
      linarith [Real.pi_pos]
  have hiG : Continuous fun s : ℂ => (Gamma s)⁻¹ := by
    simpa [one_div] using differentiable_one_div_Gamma.continuous
  have hnz : -(x : ℂ) ≠ 0 := neg_ne_zero.mpr hz0
  refine eq_of_continuousAt_of_integerComplement
    (f := fun c => regularizedHGFun {a} {c} x)
    (g := fun c => exp (a * π * I) / Gamma (c - a) * kummerU a c x +
      exp (-(c - a) * π * I) / Gamma a * exp (x : ℂ) * kummerU (c - a) c (-(x : ℂ))) ?_ ?_ ?_
  · exact (continuous_regularizedConfluent.comp (by fun_prop :
      Continuous fun c : ℂ => (a, c, (x : ℂ)))).continuousAt
  · simp only [div_eq_mul_inv]
    refine ContinuousAt.add (ContinuousAt.mul (continuousAt_const.mul
      (hiG.comp (by fun_prop : Continuous fun c : ℂ => c - a)).continuousAt)
      (continuousAt_kummerU_comp continuousAt_const continuousAt_id hz0)) ?_
    refine ContinuousAt.mul ((ContinuousAt.mul (by fun_prop) continuousAt_const).mul
      continuousAt_const) (continuousAt_kummerU_comp (by fun_prop) continuousAt_id hnz)
  · intro c hc'
    have hcz := forall_of_mem_integerComplement hc'
    have hcn : ∀ k : ℕ, c ≠ -k := fun k h => hcz (-k) (by simp [h])
    rw [regularizedConfluent_eq_div_Gamma hcn]
    have := kummerM_div_Gamma_connection_of_not_int a c hcz (-1) (Or.inr rfl) (hc _)
    rw [this]
    congr 3 <;> ring_nf

/-- `𝐌(a,b,x)` is real for real `a`, `b`, `x`. -/
lemma kzt_regM_im (a b x : ℝ) : (regularizedHGFun {(a : ℂ)} {(b : ℂ)} (x : ℂ)).im = 0 := by
  rw [regularizedConfluent_eq_tsum]
  have : ∀ n : ℕ, poch (a : ℂ) n * (x : ℂ) ^ n / n.factorial * (Gamma ((b : ℂ) + n))⁻¹ =
      (((ascPochhammer ℝ n).eval a * x ^ n / n.factorial * (Real.Gamma (b + n))⁻¹ : ℝ) : ℂ) := by
    intro n
    rw [poch_ofReal, show (b : ℂ) + n = ((b + n : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast; ring
  simp_rw [this, ← ofReal_tsum, ofReal_im]

/-- Continuity of `z ↦ z^s` at a negative real point within the closed upper half-plane. -/
lemma kzt_cpow_continuousWithinAt (s : ℂ) {x : ℝ} (hx : x < 0) :
    ContinuousWithinAt (fun z : ℂ => z ^ s) {z : ℂ | 0 ≤ z.im} (x : ℂ) := by
  have hl := continuousWithinAt_log_of_re_neg_of_im_zero (z := (x : ℂ)) (by simpa using hx)
    (by simp)
  have h : ContinuousWithinAt (fun z => exp (log z * s)) {z : ℂ | 0 ≤ z.im} (x : ℂ) :=
    (hl.mul (continuousWithinAt_const (b := s))).cexp
  have hz0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne
  refine h.congr_of_eventuallyEq ?_ (by rw [cpow_def_of_ne_zero hz0])
  filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds hz0)] with z hz
  exact cpow_def_of_ne_zero hz s

/-- For noninteger `b`, `U(a,b,·)` is continuous at a negative real point within the closed upper
half-plane (its connection formula is). -/
lemma kzt_U_continuousWithinAt (a : ℂ) {b : ℂ} (hb : ∀ n : ℤ, b ≠ n) {x : ℝ} (hx : x < 0) :
    ContinuousWithinAt (kummerU a b) {z : ℂ | 0 ≤ z.im} (x : ℂ) := by
  have hbk : ∀ k : ℕ, b ≠ -k := fun k h => hb (-k) (by simp [h])
  have h2b : ∀ k : ℕ, 2 - b ≠ -k := fun k h => hb (k + 2) (by push_cast; linear_combination -h)
  have hfun : kummerU a b = fun z => Gamma (1 - b) / Gamma (a - b + 1) * kummerM a b z +
      Gamma (b - 1) / Gamma a * z ^ (1 - b) * kummerM (a - b + 1) (2 - b) z := by
    funext z; rw [kummerU_eq_connection a b z hb]; rfl
  rw [hfun]
  have hM1 := (hasFPowerSeriesOnBall_kummerM (a := a) hbk).analyticAt_of_mem
    (y := (x : ℂ)) (by simp)
  have hM2 := (hasFPowerSeriesOnBall_kummerM (a := a - b + 1) h2b).analyticAt_of_mem
    (y := (x : ℂ)) (by simp)
  exact (continuousWithinAt_const.mul hM1.continuousAt.continuousWithinAt).add
    ((continuousWithinAt_const.mul (kzt_cpow_continuousWithinAt (1 - b) hx)).mul
      hM2.continuousAt.continuousWithinAt)

/-- **The Wronskian 13.2.34 on the negative real axis**, written with the principal values of the
contiguous functions: for `x < 0` and all complex `a`, `b`,
`𝐌(a,b,x)(-a U(a+1,b+1,x)) - U(a,b,x)(a 𝐌(a+1,b+1,x)) = -x^{-b} e^x / Γ(a)`. -/
theorem kzt_wronskian_neg (a b : ℂ) {x : ℝ} (hx : x < 0) :
    regularizedHGFun {a} {b} (x : ℂ) * (-a * kummerU (a + 1) (b + 1) x) -
      kummerU a b x * (a * regularizedHGFun {a + 1} {b + 1} (x : ℂ)) =
        -((x : ℂ) ^ (-b) * exp (x : ℂ)) / Gamma a := by
  have hz0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne
  set H : Set ℂ := {z : ℂ | 0 ≤ z.im} with hH
  -- noninteger second parameter: limit from the upper half-plane
  have key : ∀ c ∈ integerComplement,
      regularizedHGFun {a} {c} (x : ℂ) * (-a * kummerU (a + 1) (c + 1) x) -
        kummerU a c x * (a * regularizedHGFun {a + 1} {c + 1} (x : ℂ)) =
          -((x : ℂ) ^ (-c) * exp (x : ℂ)) / Gamma a := by
    intro c hc
    have hcz := forall_of_mem_integerComplement hc
    have hc1 : ∀ n : ℤ, c + 1 ≠ n := fun n h => hcz (n - 1) (by push_cast; linear_combination h)
    set F : ℂ → ℂ := fun z => regularizedHGFun {a} {c} z * (-a * kummerU (a + 1) (c + 1) z) -
        kummerU a c z * (a * regularizedHGFun {a + 1} {c + 1} z) with hF
    set G : ℂ → ℂ := fun z => -(z ^ (-c) * exp z) / Gamma a with hG
    have hMc : ∀ (p q : ℂ), Continuous fun z : ℂ => regularizedHGFun {p} {q} z := fun p q =>
      continuous_regularizedConfluent.comp (by fun_prop : Continuous fun z : ℂ => (p, q, z))
    have hFc : ContinuousWithinAt F H (x : ℂ) :=
      ((hMc a c).continuousWithinAt.mul (continuousWithinAt_const.mul
        (kzt_U_continuousWithinAt (a + 1) hc1 hx))).sub
        ((kzt_U_continuousWithinAt a hcz hx).mul
          (continuousWithinAt_const.mul (hMc (a + 1) (c + 1)).continuousWithinAt))
    have hGc : ContinuousWithinAt G H (x : ℂ) :=
      (((kzt_cpow_continuousWithinAt (-c) hx).mul
        (Complex.continuous_exp.continuousWithinAt)).neg).div_const _
    -- the path `ε ↦ x + iε`
    set g : ℝ → ℂ := fun ε => (x : ℂ) + ε * I with hg
    have hgt : Tendsto g (𝓝[>] 0) (𝓝[H] (x : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Continuous g := by fun_prop
        have h0 : g 0 = x := by simp [hg]
        exact h0 ▸ (this.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        simp [hH, hg, le_of_lt (mem_Ioi.1 hε)]
    have h1 := hFc.tendsto.comp hgt
    have h2 := hGc.tendsto.comp hgt
    refine tendsto_nhds_unique h1 (h2.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0:ℝ) < ε := hε
    have hz : g ε ∈ slitPlane := by
      rw [mem_slitPlane_iff]; right; simp [hg, hε'.ne']
    have hW := wronskian_regularizedHGFun_kummerU_all a c hz
    rw [wronskian, deriv_kummerU _ _ hz, deriv_regularizedConfluent] at hW
    simp only [Function.comp_apply, hF, hG]
    rw [← hW]
  refine eq_of_continuousAt_of_integerComplement
    (f := fun c => regularizedHGFun {a} {c} (x : ℂ) * (-a * kummerU (a + 1) (c + 1) x) -
        kummerU a c x * (a * regularizedHGFun {a + 1} {c + 1} (x : ℂ)))
    (g := fun c => -((x : ℂ) ^ (-c) * exp (x : ℂ)) / Gamma a) ?_ ?_ key
  · have hR : ∀ (p : ℂ) (q : ℂ → ℂ), Continuous q →
        ContinuousAt (fun c => regularizedHGFun {p} {q c} (x : ℂ)) b := fun p q hq =>
      (continuous_regularizedConfluent.comp (by fun_prop :
        Continuous fun c : ℂ => (p, q c, (x : ℂ)))).continuousAt
    exact ((hR a id continuous_id).mul (continuousAt_const.mul
      (continuousAt_kummerU_comp continuousAt_const (by fun_prop) hz0))).sub
      ((continuousAt_kummerU_comp continuousAt_const continuousAt_id hz0).mul
        (continuousAt_const.mul (hR (a + 1) (fun c => c + 1) (by fun_prop))))
  · exact (((continuousAt_id.neg.const_cpow (Or.inl hz0)).mul continuousAt_const).neg).div_const _

/-- `U(a,b,·)` and `𝐌(a,b,·)` have no common zero on the negative axis when `a ∉ -ℕ`, by
`kzt_wronskian_neg`. -/
lemma kzt_neg_no_common_zero {a b : ℂ} (ha : ∀ m : ℕ, a ≠ -m) {x : ℝ} (hx : x < 0)
    (hU : kummerU a b x = 0) (hM : regularizedHGFun {a} {b} (x : ℂ) = 0) : False := by
  have hW := kzt_wronskian_neg a b hx
  rw [hU, hM] at hW
  have hz0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne
  have hpw : (x : ℂ) ^ (-b) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz0 h.1
  have : -((x : ℂ) ^ (-b) * exp (x : ℂ)) / Gamma a ≠ 0 :=
    div_ne_zero (neg_ne_zero.2 (mul_ne_zero hpw (exp_ne_zero _))) (Gamma_ne_zero ha)
  exact this (by simpa using hW.symm)

/-- The term `e^{-πi s} e^x U(b-a,b,-x)/Γ(a)` of `kzt_connection_neg` is `e^{-πi s}` times a real
number. -/
lemma kzt_neg_second_term (a b : ℝ) {x : ℝ} (hx : x < 0) (θ : ℂ) :
    θ / Gamma (a : ℂ) * exp (x : ℂ) * kummerU ((b : ℂ) - a) b (-(x : ℂ)) =
      θ * ((Real.exp x * kzt_U (b - a) b (-x) / Real.Gamma a : ℝ) : ℂ) := by
  have ht : (0:ℝ) < -x := by linarith
  have hU := kzt_U_eq (b - a) b ht
  push_cast at hU
  rw [hU, Complex.Gamma_ofReal]
  push_cast
  ring

/-- **No zeros on the negative axis, noninteger `b - a`.** For real `a ∉ -ℕ` and real `b` with
`b - a ∉ ℤ`, the principal branch of `U(a,b,·)` has no zeros on `(-∞, 0)`. -/
theorem kzt_U_neg_ne_zero_of_nonint (a b : ℝ) (ha : ∀ m : ℕ, a ≠ -(m : ℝ))
    (hba : ∀ n : ℤ, b - a ≠ n) {x : ℝ} (hx : x < 0) : kummerU (a : ℂ) b x ≠ 0 := by
  intro hU
  have ha' : ∀ m : ℕ, (a : ℂ) ≠ -(m : ℂ) := fun m h => ha m (by exact_mod_cast h)
  have hL := kzt_connection_neg (a : ℂ) b hx
  rw [hU, mul_zero, zero_add, kzt_neg_second_term a b hx] at hL
  set Q := Real.exp x * kzt_U (b - a) b (-x) / Real.Gamma a with hQ
  have him := kzt_regM_im a b x
  rw [hL] at him
  have hE : exp (-((b : ℂ) - a) * π * I) = exp (((-(b - a) * π : ℝ) : ℂ) * I) := by
    push_cast; ring_nf
  rw [hE, Complex.mul_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, ofReal_re, ofReal_im,
    mul_zero, zero_add] at him
  have hsin : Real.sin (-(b - a) * π) ≠ 0 := by
    rw [Ne, Real.sin_eq_zero_iff]
    rintro ⟨n, hn⟩
    apply hba (-n)
    have := Real.pi_pos
    push_cast
    have : ((n : ℝ) + (b - a)) * π = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hQ0 : Q = 0 := (mul_eq_zero.1 him).resolve_left hsin
  refine kzt_neg_no_common_zero ha' hx hU ?_
  rw [hL, hQ0]; simp

/-- **Imaginary part on the negative axis, integer `b`.** For `n, k ∈ ℕ` with `k ≤ n` and
`x < 0`, `Im U(n,k,x) = (-1)^k π 𝐌(n,k,x) / Γ(n-k+1)`. -/
theorem kzt_U_neg_im_nat (n k : ℕ) (hkn : k ≤ n) {x : ℝ} (hx : x < 0) :
    (kummerU (n : ℂ) (k : ℂ) x).im =
      (-1) ^ k * π * (regularizedHGFun {((n : ℝ) : ℂ)} {(k : ℂ)} (x : ℂ)).re /
        Real.Gamma (n - k + 1) := by
  set f : ℝ → ℝ := fun a => (kummerU (a : ℂ) (k : ℂ) x).im with hf
  set g : ℝ → ℝ := fun a => (-1) ^ k * π * (regularizedHGFun {(a : ℂ)} {(k : ℂ)} (x : ℂ)).re /
    Real.Gamma (a - k + 1) with hg
  have hz0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne
  have hpos : (0:ℝ) < n - k + 1 := by
    have : (k:ℝ) ≤ n := by exact_mod_cast hkn
    linarith
  -- the identity for noninteger `a ∈ (n, n+1)`
  have hoff : ∀ a ∈ Ioo (n : ℝ) (n + 1), f a = g a := by
    intro a ha
    have hai : ∀ m : ℤ, a ≠ m := fun m h => by
      rw [h] at ha
      have h1 : (n : ℤ) < m := by exact_mod_cast ha.1
      have h2 : m < (n : ℤ) + 1 := by exact_mod_cast ha.2
      omega
    have ha0 : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg n) ha.1
    have hka : ∀ m : ℤ, (k : ℝ) - a ≠ m := fun m h => hai (k - m) (by push_cast; linarith)
    have hG1 : Real.Gamma (a - k + 1) ≠ 0 := Real.Gamma_ne_zero fun m h =>
      hai (k - 1 - m) (by push_cast; linarith)
    have hG2 : Real.Gamma (k - a) ≠ 0 := Real.Gamma_ne_zero fun m h =>
      hka (-m) (by push_cast; linarith)
    have hL := kzt_connection_neg (a : ℂ) (k : ℂ) hx
    rw [show ((k : ℂ)) = ((k : ℝ) : ℂ) by push_cast; rfl, kzt_neg_second_term a k hx] at hL
    set Q := Real.exp x * kzt_U (k - a) k (-x) / Real.Gamma a
    set Mr := (regularizedHGFun {(a : ℂ)} {((k : ℝ) : ℂ)} (x : ℂ)).re with hMr
    have hMc : regularizedHGFun {(a : ℂ)} {((k : ℝ) : ℂ)} (x : ℂ) = (Mr : ℂ) :=
      Complex.ext (by simp [hMr]) (by have := kzt_regM_im a k x; simpa using this)
    rw [hMc, show ((k : ℝ) : ℂ) - a = ((k - a : ℝ) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal] at hL
    -- solve for `U`
    have hE1 : exp ((a : ℂ) * π * I) ≠ 0 := exp_ne_zero _
    have hGc : ((Real.Gamma (k - a) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hG2
    have hU : kummerU (a : ℂ) ((k : ℝ) : ℂ) x = (Real.Gamma (k - a) : ℂ) *
        (exp (((-(a * π)) : ℝ) * I) * Mr - (-1) ^ k * Q) := by
      have hk : exp (-(((k - a : ℝ) : ℂ)) * π * I) = exp (((a * π : ℝ) : ℂ) * I) * (-1) ^ k := by
        rw [show -(((k - a : ℝ) : ℂ)) * π * I = ((a * π : ℝ) : ℂ) * I + (k : ℂ) * (-(π * I))
          by push_cast; ring, exp_add, exp_nat_mul, exp_neg, exp_pi_mul_I]
        norm_num
      rw [hk] at hL
      have hE : exp (((-(a * π)) : ℝ) * I) * exp ((a : ℂ) * π * I) = 1 := by
        rw [← exp_add]; push_cast; ring_nf; exact exp_zero
      have hE' : exp (((a * π : ℝ) : ℂ) * I) = exp ((a : ℂ) * π * I) := by push_cast; ring_nf
      rw [hE'] at hL
      have hinv : (Real.Gamma (k - a) : ℂ) * (Real.Gamma (k - a) : ℂ)⁻¹ = 1 :=
        mul_inv_cancel₀ hGc
      rw [hL]
      linear_combination (-(kummerU (a : ℂ) ((k : ℝ) : ℂ) x) * exp (((-(a * π)) : ℝ) * I) *
        exp ((a : ℂ) * π * I)) * hinv + (-(kummerU (a : ℂ) ((k : ℝ) : ℂ) x) -
        (Real.Gamma (k - a) : ℂ) * (-1) ^ k * Q) * hE
    have hfa : f a = Real.Gamma (k - a) * (-Real.sin (a * π) * Mr) := by
      simp only [hf]
      rw [show (k : ℂ) = ((k : ℝ) : ℂ) by push_cast; rfl, hU]
      have h1 : ((-1 : ℂ) ^ k * (Q : ℂ)) = (((-1) ^ k * Q : ℝ) : ℂ) := by push_cast; ring
      rw [h1, Complex.mul_im, Complex.sub_im, Complex.mul_im, exp_ofReal_mul_I_re,
        exp_ofReal_mul_I_im, ofReal_re, ofReal_im, ofReal_im, ofReal_re, ofReal_im,
        Real.sin_neg]
      ring
    -- Gamma reflection
    have hrefl := Real.Gamma_mul_Gamma_one_sub (k - a)
    rw [show 1 - (k - a) = a - k + 1 by ring] at hrefl
    have hsin : Real.sin (π * (k - a)) = -((-1) ^ k * Real.sin (a * π)) := by
      rw [show π * (k - a) = k * π - a * π by ring, Real.sin_nat_mul_pi_sub]
    have hsin0 : Real.sin (π * (k - a)) ≠ 0 := by
      intro h; rw [h, div_zero] at hrefl
      exact mul_ne_zero hG2 hG1 hrefl
    have hprod : Real.Gamma (k - a) * Real.Gamma (a - k + 1) * Real.sin (π * (k - a)) = π := by
      rw [hrefl]; field_simp
    rw [hfa]
    simp only [hg]
    rw [eq_div_iff hG1]
    have hsq : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [hsin] at hprod
    have : Mr = (regularizedHGFun {(a : ℂ)} {(k : ℂ)} (x : ℂ)).re := by
      simp [hMr]
    rw [← this]
    linear_combination ((-1 : ℝ) ^ k * Mr) * hprod + (Real.Gamma (k - a) *
      Real.Gamma (a - k + 1) * Real.sin (a * π) * Mr) * hsq
  -- continuity at `n`
  have hfc : ContinuousAt f n := by
    have h := continuousAt_kummerU_comp (A := id) (B := fun _ => (k : ℂ)) (b := ((n : ℝ) : ℂ))
      continuousAt_id continuousAt_const hz0
    exact Complex.continuous_im.continuousAt.comp
      (h.comp (f := fun a : ℝ => (a : ℂ)) continuous_ofReal.continuousAt)
  have hgc : ContinuousAt g n := by
    have hM : Continuous fun a : ℝ => (regularizedHGFun {(a : ℂ)} {(k : ℂ)} (x : ℂ)).re :=
      Complex.continuous_re.comp (continuous_regularizedConfluent.comp
        (by fun_prop : Continuous fun a : ℝ => ((a : ℂ), (k : ℂ), (x : ℂ))))
    have hG : ContinuousAt (fun a : ℝ => Real.Gamma (a - k + 1)) n :=
      (Real.differentiableAt_Gamma (fun m h => by linarith [(m.cast_nonneg : (0:ℝ) ≤ m)])
        ).continuousAt.comp (by fun_prop)
    exact (continuousAt_const.mul hM.continuousAt).div hG (Real.Gamma_pos_of_pos hpos).ne'
  have := tendsto_nhds_unique (hfc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (n : ℝ))))
    ((hgc.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (eventually_of_mem (Ioo_mem_nhdsGT (show (n : ℝ) < n + 1 by linarith))
        fun a ha => (hoff a ha).symm))
  simpa [hf, hg] using this

/-- **No zeros on the negative axis, integer parameters.** For `n, k ∈ ℕ` with `1 ≤ n` and
`k ≤ n`, `U(n,k,·)` has no zeros on `(-∞, 0)`. -/
theorem kzt_U_neg_ne_zero_nat (n k : ℕ) (hn : 1 ≤ n) (hkn : k ≤ n) {x : ℝ} (hx : x < 0) :
    kummerU (n : ℂ) (k : ℂ) x ≠ 0 := by
  intro hU
  have him := kzt_U_neg_im_nat n k hkn hx
  rw [hU, zero_im] at him
  have hpos : (0:ℝ) < n - k + 1 := by
    have : (k:ℝ) ≤ n := by exact_mod_cast hkn
    linarith
  have hG := Real.Gamma_pos_of_pos hpos
  have hpk : ((-1 : ℝ) ^ k * π) ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) Real.pi_ne_zero
  have hMr : (regularizedHGFun {((n : ℝ) : ℂ)} {(k : ℂ)} (x : ℂ)).re = 0 := by
    have h := him.symm
    rw [div_eq_zero_iff, or_iff_left hG.ne', mul_eq_zero, or_iff_right hpk] at h
    exact h
  have hM : regularizedHGFun {(n : ℂ)} {(k : ℂ)} (x : ℂ) = 0 := by
    have hi := kzt_regM_im n k x
    push_cast at hMr hi
    exact Complex.ext hMr hi
  refine kzt_neg_no_common_zero (a := (n : ℂ)) (fun m h => ?_) hx hU hM
  have : (n : ℝ) = -(m : ℝ) := by exact_mod_cast h
  have : (1:ℝ) ≤ n := by exact_mod_cast hn
  linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]

/-- **No zeros on the negative axis (DLMF 13.9.13 in pointwise form).** For real `a ∉ -ℕ` and
real `b ≤ a + 1`, the principal branch of `U(a,b,·)` has no zeros on `(-∞, 0)`. -/
theorem kzt_U_neg_ne_zero {a b : ℝ} (h : a + 1 ≥ b) (ha : ∀ m : ℕ, a ≠ -(m : ℝ)) {x : ℝ}
    (hx : x < 0) : kummerU (a : ℂ) b x ≠ 0 := by
  have hz0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne
  have hpw : ∀ c : ℂ, (x : ℂ) ^ c ≠ 0 := fun c => by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hz0 h.1
  by_cases hba : ∀ n : ℤ, b - a ≠ n
  · exact kzt_U_neg_ne_zero_of_nonint a b ha hba hx
  push Not at hba
  obtain ⟨j, hj⟩ := hba
  have hj1 : j ≤ 1 := by
    have : (j : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  have hb : b = a + j := by linarith
  have hnat : ∀ (z : ℤ), 0 ≤ z → ((z.toNat : ℕ) : ℂ) = ((z : ℝ) : ℂ) := fun z hz => by
    have : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz
    have h2 : ((((z.toNat : ℕ) : ℤ) : ℝ) : ℂ) = ((z : ℝ) : ℂ) := by rw [this]
    push_cast at h2 ⊢; exact h2
  rcases eq_or_lt_of_le hj1 with hj1 | hj1
  · -- `b = a + 1`
    subst hj1
    rw [kummerU_kummer_transform_all _ _ hz0]
    refine mul_ne_zero (hpw _) ?_
    rw [show (a : ℂ) - b + 1 = 0 by rw [hb]; push_cast; ring, kummerU_zero]
    exact one_ne_zero
  have hj0 : j ≤ 0 := by omega
  have ha' : (a : ℂ) - b + 1 = (((1 - j : ℤ) : ℝ) : ℂ) := by rw [hb]; push_cast; ring
  have hb' : (2 : ℂ) - b = ((2 - b : ℝ) : ℂ) := by push_cast; ring
  by_cases hai : ∀ m : ℤ, a ≠ m
  · rw [kummerU_kummer_transform_all _ _ hz0]
    refine mul_ne_zero (hpw _) ?_
    rw [ha', hb']
    refine kzt_U_neg_ne_zero_of_nonint _ _ (fun m hm => ?_) (fun m hm => hai (1 - m) ?_) hx
    · have : ((1 - j : ℤ) : ℝ) ≥ 1 := by
        have : (1 : ℤ) ≤ 1 - j := by omega
        exact_mod_cast this
      linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
    · push_cast at hm ⊢; linarith
  push Not at hai
  obtain ⟨m, hm⟩ := hai
  have hm1 : 1 ≤ m := by
    by_contra hcon
    refine ha (-m).toNat ?_
    have h3 := hnat (-m) (by omega)
    have h4 : (((-m).toNat : ℕ) : ℝ) = -(m : ℝ) := by
      have := congrArg Complex.re h3
      simpa using this
    rw [hm, h4]; ring
  by_cases hbn : 0 ≤ m + j
  · have hA : (a : ℂ) = ((m.toNat : ℕ) : ℂ) := by rw [hnat m (by omega), hm]
    have hB : (b : ℂ) = (((m + j).toNat : ℕ) : ℂ) := by
      rw [hnat _ hbn, hb, hm]; push_cast; ring
    rw [hA, hB]
    exact kzt_U_neg_ne_zero_nat _ _ (by omega) (by omega) hx
  · rw [kummerU_kummer_transform_all _ _ hz0]
    refine mul_ne_zero (hpw _) ?_
    have hn : (a : ℂ) - b + 1 = (((1 - j).toNat : ℕ) : ℂ) := by
      rw [ha', hnat _ (by omega)]
    have hk : (2 : ℂ) - b = (((2 - m - j).toNat : ℕ) : ℂ) := by
      rw [hnat _ (by omega), hb, hm]; push_cast; ring
    rw [hn, hk]
    exact kzt_U_neg_ne_zero_nat _ _ (by omega) (by omega) hx

end NegativeAxis

end DLMF.Confluent
