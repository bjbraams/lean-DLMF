/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Bounds and integrability for the symmetric elliptic integrands

Analytic infrastructure for DLMF §19.16 (round-1 helpers, prefix `p19sR1_`), stated for the
explicit integrands `s(t)⁻¹`, `(s(t) (t + p))⁻¹` and `s(t)⁻¹ (∑ x/(t + x)) t` with
`s(t) = √(t + x) √(t + y) √(t + z)` (principal square roots), so that it can be imported by
`DLMF.EllipticIntegrals.Symmetric`:

* the lower bound `‖t + w‖ ≥ c (t + 1)` for `w ∈ ℂ \ (-∞, 0]`, `t ≥ 0`
  (`p19sR1_norm_add_ge`), from `|t + w|² ≥ ((|w| + ℜw)/(2|w|)) (t + |w|)²`;
* integrability on `(0, ∞)` of the integrands of `R_F`, `R_J` (hence `R_D`) and `R_G` when one
  variable is admissible (slit plane or `0`) and the others lie in the slit plane, by domination
  with `(√t (t + 1))⁻¹`;
* the derivative of `t ↦ (t + w)^{1/2}`;
* the integral identity behind DLMF 19.21.10 (`p19sR1_RG_identity`), by the exact antiderivative
  `(t (x + y) + xy)/s(t)`, valid also for `x = 0`.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-- `‖w^{1/2}‖ = √‖w‖`. -/
theorem p19sR1_norm_cpow_half (w : ℂ) : ‖w ^ (1 / 2 : ℂ)‖ = Real.sqrt ‖w‖ := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real,
    Real.sqrt_eq_rpow]

/-- For `w` in the slit plane, `‖t + w‖ ≥ c (t + 1)` for all `t ≥ 0`, with `c > 0`. -/
theorem p19sR1_norm_add_ge {w : ℂ} (hw : w ∈ slitPlane) :
    ∃ c > 0, ∀ t : ℝ, 0 ≤ t → c * (t + 1) ≤ ‖(t : ℂ) + w‖ := by
  set r := ‖w‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr (slitPlane_ne_zero hw)
  have hr2 : r ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [hr, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hra : 0 < r + w.re := by
    rcases mem_slitPlane_iff.mp hw with h | h
    · linarith
    · by_contra hc
      push Not at hc
      have : w.re ^ 2 < r ^ 2 := by
        rw [hr2]; have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; linarith
      nlinarith
  set κ := (r + w.re) / (2 * r) with hκ
  have hκ0 : 0 < κ := div_pos hra (by positivity)
  refine ⟨Real.sqrt κ * min 1 r, mul_pos (Real.sqrt_pos.mpr hκ0) (lt_min one_pos hr0), ?_⟩
  intro t ht
  have hn2 : ‖(t : ℂ) + w‖ ^ 2 = (t + w.re) ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have key : κ * (t + r) ^ 2 ≤ ‖(t : ℂ) + w‖ ^ 2 := by
    rw [hn2, hκ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have hra' : w.re ≤ r := by
      have := Complex.re_le_norm w; linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hra') (sq_nonneg (t - r))]
  have h1 : Real.sqrt κ * (t + r) ≤ ‖(t : ℂ) + w‖ := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ t + r), ← Real.sqrt_mul hκ0.le,
      ← Real.sqrt_sq (norm_nonneg ((t : ℂ) + w))]
    exact Real.sqrt_le_sqrt key
  have h2 : min 1 r * (t + 1) ≤ t + r := by
    have := min_le_left 1 r; have := min_le_right 1 r
    nlinarith
  calc Real.sqrt κ * min 1 r * (t + 1) = Real.sqrt κ * (min 1 r * (t + 1)) := by ring
    _ ≤ Real.sqrt κ * (t + r) := by gcongr
    _ ≤ _ := h1

/-- Square-root form: `‖(t + w)^{1/2}‖ ≥ c √(t + 1)` for slit-plane `w`, `t ≥ 0`. -/
theorem p19sR1_norm_cpow_half_ge {w : ℂ} (hw : w ∈ slitPlane) :
    ∃ c > 0, ∀ t : ℝ, 0 ≤ t → c * Real.sqrt (t + 1) ≤ ‖((t : ℂ) + w) ^ (1 / 2 : ℂ)‖ := by
  obtain ⟨c, hc, h⟩ := p19sR1_norm_add_ge hw
  refine ⟨Real.sqrt c, Real.sqrt_pos.mpr hc, fun t ht => ?_⟩
  rw [p19sR1_norm_cpow_half, ← Real.sqrt_mul hc.le]
  exact Real.sqrt_le_sqrt (h t ht)

/-- For an admissible `w` (slit plane or `0`), `‖(t + w)^{1/2}‖ ≥ c √t` for `t > 0`. -/
theorem p19sR1_norm_cpow_half_ge' {w : ℂ} (hw : w ∈ slitPlane ∨ w = 0) :
    ∃ c > 0, ∀ t : ℝ, 0 < t → c * Real.sqrt t ≤ ‖((t : ℂ) + w) ^ (1 / 2 : ℂ)‖ := by
  rcases hw with hw | rfl
  · obtain ⟨c, hc, h⟩ := p19sR1_norm_cpow_half_ge hw
    refine ⟨c, hc, fun t ht => le_trans ?_ (h t ht.le)⟩
    gcongr; linarith
  · refine ⟨1, one_pos, fun t ht => ?_⟩
    rw [add_zero, p19sR1_norm_cpow_half, Complex.norm_real, Real.norm_of_nonneg ht.le, one_mul]

/-- The dominating function `t ↦ (√t (t + 1))⁻¹` is integrable on `(0, ∞)`. -/
lemma p19sR1_integrableOn_bound :
    IntegrableOn (fun t : ℝ => (Real.sqrt t * (t + 1))⁻¹) (Ioi 0) := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (Real.sqrt t * (t + 1))⁻¹) := by
    fun_prop
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun t : ℝ => t ^ (-1 / 2 : ℝ)) (Ioc 0 1) := by
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (r := -1 / 2) (by norm_num))
    refine h1.mono' hmeas.restrict ?_
    refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
    have ht0 : 0 < t := ht.1
    rw [Real.norm_of_nonneg (by positivity)]
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg ht0.le, ← Real.sqrt_eq_rpow]
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    rw [inv_le_inv₀ (by positivity) hs]
    nlinarith
  · have h1 : IntegrableOn (fun t : ℝ => t ^ (-3 / 2 : ℝ)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
    refine h1.mono' hmeas.restrict ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    have ht0 : 0 < t := lt_trans one_pos ht
    rw [Real.norm_of_nonneg (by positivity)]
    rw [show (-3 / 2 : ℝ) = -(1 / 2 + 1) by norm_num, Real.rpow_neg ht0.le,
      Real.rpow_add ht0, Real.rpow_one, ← Real.sqrt_eq_rpow]
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    nlinarith


/-- For `t > 0` and admissible `w`, `t + w` lies in the slit plane. -/
theorem p19sR1_add_mem_slitPlane {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : w ∈ slitPlane ∨ w = 0) :
    (t : ℂ) + w ∈ slitPlane := by
  rcases hw with hw | rfl
  · rcases mem_slitPlane_iff.mp hw with h | h
    · exact mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
    · exact mem_slitPlane_iff.mpr (Or.inr (by simpa using h))
  · simpa using ofReal_mem_slitPlane.mpr ht

/-- For `t > 0` and admissible `w`, `(t + w)^{1/2} ≠ 0`. -/
theorem p19sR1_cpow_half_ne_zero {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : w ∈ slitPlane ∨ w = 0) :
    ((t : ℂ) + w) ^ (1 / 2 : ℂ) ≠ 0 := by
  rw [Ne, cpow_eq_zero_iff]; push Not
  intro h; exact absurd h (slitPlane_ne_zero (p19sR1_add_mem_slitPlane ht hw))

/-- `w^{1/2} ≠ 0` on the slit plane. -/
theorem p19sR1_cpow_half_ne_zero_of_mem {w : ℂ} (hw : w ∈ slitPlane) : w ^ (1 / 2 : ℂ) ≠ 0 :=
  fun h => slitPlane_ne_zero hw ((cpow_eq_zero_iff _ _).mp h).1

/-- `(w^{1/2})² = w`. -/
theorem p19sR1_cpow_half_sq (w : ℂ) : (w ^ (1 / 2 : ℂ)) ^ 2 = w := by
  rw [show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num, cpow_nat_inv_pow _ two_ne_zero]

/-- Continuity of `t ↦ (t + w)^{1/2}` where `t + w` is in the slit plane. -/
theorem p19sR1_continuousAt_cpow_half {t : ℝ} {w : ℂ} (h : (t : ℂ) + w ∈ slitPlane) :
    ContinuousAt (fun s : ℝ => ((s : ℂ) + w) ^ (1 / 2 : ℂ)) t :=
  (continuousAt_cpow_const h).comp (f := fun s : ℝ => (s : ℂ) + w) (by fun_prop)

/-- Continuity of `t ↦ (t + w)^{1/2}` on `(0, ∞)` for admissible `w`. -/
theorem p19sR1_continuousOn_cpow_half {w : ℂ} (hw : w ∈ slitPlane ∨ w = 0) :
    ContinuousOn (fun s : ℝ => ((s : ℂ) + w) ^ (1 / 2 : ℂ)) (Ioi 0) := fun _t ht =>
  (p19sR1_continuousAt_cpow_half (p19sR1_add_mem_slitPlane ht hw)).continuousWithinAt

/-- `d/dt (t + w)^{1/2} = (t + w)^{1/2} / (2 (t + w))` for `t + w` in the slit plane. -/
theorem p19sR1_hasDerivAt_cpow_half {t : ℝ} {w : ℂ} (h : (t : ℂ) + w ∈ slitPlane) :
    HasDerivAt (fun s : ℝ => ((s : ℂ) + w) ^ (1 / 2 : ℂ))
      (((t : ℂ) + w) ^ (1 / 2 : ℂ) / (2 * ((t : ℂ) + w))) t := by
  have h0 : (t : ℂ) + w ≠ 0 := slitPlane_ne_zero h
  have hd : HasDerivAt (fun s : ℂ => s + w) 1 (t : ℂ) := (hasDerivAt_id _).add_const w
  have := (hd.cpow_const (c := 1 / 2) h).comp_ofReal
  convert this using 1
  rw [show (1 / 2 : ℂ) - 1 = 1 / 2 + (-1) by norm_num, cpow_add _ _ h0, cpow_neg_one]
  field_simp

/-- A function continuous on `(0, ∞)` and bounded by a multiple of `(√t (t + 1))⁻¹` is
integrable there. -/
theorem p19sR1_integrableOn_of_le {f : ℝ → ℂ} (hf : ContinuousOn f (Ioi 0)) {C : ℝ}
    (h : ∀ t : ℝ, 0 < t → ‖f t‖ ≤ C * (Real.sqrt t * (t + 1))⁻¹) : IntegrableOn f (Ioi 0) := by
  refine (p19sR1_integrableOn_bound.const_mul C).mono' (hf.aestronglyMeasurable measurableSet_Ioi) ?_
  exact (ae_restrict_mem measurableSet_Ioi).mono fun t ht => h t ht

/-- The bound for `R_F`'s integrand: `a` admissible, `b, c` in the slit plane. -/
theorem p19sR1_norm_inv_s_le {a b c : ℂ} (ha : a ∈ slitPlane ∨ a = 0) (hb : b ∈ slitPlane)
    (hc : c ∈ slitPlane) : ∃ C, ∀ t : ℝ, 0 < t →
      ‖(((t : ℂ) + a) ^ (1 / 2 : ℂ) * ((t : ℂ) + b) ^ (1 / 2 : ℂ) *
        ((t : ℂ) + c) ^ (1 / 2 : ℂ))⁻¹‖ ≤ C * (Real.sqrt t * (t + 1))⁻¹ := by
  obtain ⟨ca, hca, ha'⟩ := p19sR1_norm_cpow_half_ge' ha
  obtain ⟨cb, hcb, hb'⟩ := p19sR1_norm_cpow_half_ge hb
  obtain ⟨cc, hcc, hc'⟩ := p19sR1_norm_cpow_half_ge hc
  refine ⟨(ca * cb * cc)⁻¹, fun t ht => ?_⟩
  have h1 := ha' t ht
  have h2 := hb' t ht.le
  have h3 := hc' t ht.le
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs1 : 0 < Real.sqrt (t + 1) := Real.sqrt_pos.mpr (by linarith)
  have hss : Real.sqrt (t + 1) * Real.sqrt (t + 1) = t + 1 := Real.mul_self_sqrt (by linarith)
  rw [norm_inv, norm_mul, norm_mul, ← mul_inv]
  rw [inv_le_inv₀ (by
    have := mul_pos (mul_pos (lt_of_lt_of_le (by positivity) h1) (lt_of_lt_of_le (by positivity) h2))
      (lt_of_lt_of_le (by positivity) h3)
    exact this) (by positivity)]
  calc ca * cb * cc * (Real.sqrt t * (t + 1))
      = (ca * Real.sqrt t) * (cb * Real.sqrt (t + 1)) * (cc * Real.sqrt (t + 1)) := by
        linear_combination (-(ca * cb * cc * Real.sqrt t)) * hss
    _ ≤ _ := by gcongr

/-- `‖(t + q)⁻¹‖ ≤ C` for `q` in the slit plane and `t > 0`. -/
lemma p19sR1_norm_inv_add_le {q : ℂ} (hq : q ∈ slitPlane) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ‖((t : ℂ) + q)⁻¹‖ ≤ C := by
  obtain ⟨c, hc, h⟩ := p19sR1_norm_add_ge hq
  refine ⟨c⁻¹, by positivity, fun t ht => ?_⟩
  rw [norm_inv]
  have := h t ht.le
  have hpos : 0 < ‖(t : ℂ) + q‖ := lt_of_lt_of_le (by positivity) this
  rw [inv_le_inv₀ hpos hc]
  nlinarith

/-- `t ‖w/(t + w)‖ ≤ K` for admissible `w` and `t > 0`. -/
lemma p19sR1_mul_norm_div_add_le {w : ℂ} (hw : w ∈ slitPlane ∨ w = 0) :
    ∃ K, ∀ t : ℝ, 0 < t → t * ‖w / ((t : ℂ) + w)‖ ≤ K := by
  rcases hw with hw | rfl
  · obtain ⟨c, hc, h⟩ := p19sR1_norm_add_ge hw
    refine ⟨‖w‖ / c, fun t ht => ?_⟩
    have := h t ht.le
    have hpos : 0 < ‖(t : ℂ) + w‖ := lt_of_lt_of_le (by positivity) this
    rw [norm_div, mul_div_assoc', div_le_div_iff₀ hpos hc]
    have := norm_nonneg w
    nlinarith
  · exact ⟨0, fun t _ => by simp⟩

/-- Continuity of `s(t)⁻¹` on `(0, ∞)` for admissible variables. -/
lemma p19sR1_continuousOn_inv_s {a b c : ℂ} (ha : a ∈ slitPlane ∨ a = 0)
    (hb : b ∈ slitPlane ∨ b = 0) (hc : c ∈ slitPlane ∨ c = 0) :
    ContinuousOn (fun t : ℝ => (((t : ℂ) + a) ^ (1 / 2 : ℂ) * ((t : ℂ) + b) ^ (1 / 2 : ℂ) *
        ((t : ℂ) + c) ^ (1 / 2 : ℂ))⁻¹) (Ioi 0) :=
  (((p19sR1_continuousOn_cpow_half ha).mul (p19sR1_continuousOn_cpow_half hb)).mul
    (p19sR1_continuousOn_cpow_half hc)).inv₀ fun _t ht =>
      mul_ne_zero (mul_ne_zero (p19sR1_cpow_half_ne_zero ht ha) (p19sR1_cpow_half_ne_zero ht hb))
        (p19sR1_cpow_half_ne_zero ht hc)

/-- Integrability of `R_F`'s integrand: `a` admissible, `b, c` in the slit plane. -/
theorem p19sR1_integrableOn_RF {a b c : ℂ} (ha : a ∈ slitPlane ∨ a = 0) (hb : b ∈ slitPlane)
    (hc : c ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => (((t : ℂ) + a) ^ (1 / 2 : ℂ) * ((t : ℂ) + b) ^ (1 / 2 : ℂ) *
        ((t : ℂ) + c) ^ (1 / 2 : ℂ))⁻¹) (Ioi 0) := by
  obtain ⟨C, hC⟩ := p19sR1_norm_inv_s_le ha hb hc
  exact p19sR1_integrableOn_of_le (p19sR1_continuousOn_inv_s ha (Or.inl hb) (Or.inl hc)) hC

/-- Integrability of `R_J`'s integrand: `a` admissible, `b, c, p` in the slit plane. -/
theorem p19sR1_integrableOn_RJ {a b c p : ℂ} (ha : a ∈ slitPlane ∨ a = 0) (hb : b ∈ slitPlane)
    (hc : c ∈ slitPlane) (hp : p ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => (((t : ℂ) + a) ^ (1 / 2 : ℂ) * ((t : ℂ) + b) ^ (1 / 2 : ℂ) *
        ((t : ℂ) + c) ^ (1 / 2 : ℂ) * ((t : ℂ) + p))⁻¹) (Ioi 0) := by
  obtain ⟨C, hC⟩ := p19sR1_norm_inv_s_le ha hb hc
  obtain ⟨Cp, hCp0, hCp⟩ := p19sR1_norm_inv_add_le hp
  refine p19sR1_integrableOn_of_le (C := C * Cp) ?_ fun t ht => ?_
  · refine ((p19sR1_continuousOn_inv_s ha (Or.inl hb) (Or.inl hc)).mul
      (((continuous_ofReal.add continuous_const).continuousOn).inv₀ fun t ht =>
        slitPlane_ne_zero (p19sR1_add_mem_slitPlane ht (Or.inl hp)))).congr fun t _ => ?_
    exact mul_inv _ _
  · rw [mul_inv, norm_mul]
    have h1 := hC t ht
    have h2 := hCp t ht
    have hB : 0 ≤ (Real.sqrt t * (t + 1))⁻¹ := by positivity
    calc _ ≤ C * (Real.sqrt t * (t + 1))⁻¹ * Cp :=
          mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      _ = _ := by ring

/-- Integrability of `R_G`'s integrand: `a` admissible, `b, c` in the slit plane. -/
lemma p19sR1_integrableOn_RG {a b c : ℂ} (ha : a ∈ slitPlane ∨ a = 0) (hb : b ∈ slitPlane)
    (hc : c ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => (((t : ℂ) + a) ^ (1 / 2 : ℂ) * ((t : ℂ) + b) ^ (1 / 2 : ℂ) *
        ((t : ℂ) + c) ^ (1 / 2 : ℂ))⁻¹ *
        (a / ((t : ℂ) + a) + b / ((t : ℂ) + b) + c / ((t : ℂ) + c)) * t) (Ioi 0) := by
  obtain ⟨C, hC⟩ := p19sR1_norm_inv_s_le ha hb hc
  obtain ⟨Ka, hKa⟩ := p19sR1_mul_norm_div_add_le ha
  obtain ⟨Kb, hKb⟩ := p19sR1_mul_norm_div_add_le (Or.inl hb)
  obtain ⟨Kc, hKc⟩ := p19sR1_mul_norm_div_add_le (Or.inl hc)
  have hne : ∀ w : ℂ, (w ∈ slitPlane ∨ w = 0) → ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) + w ≠ 0 :=
    fun w hw t ht => slitPlane_ne_zero (p19sR1_add_mem_slitPlane ht hw)
  have hcd : ∀ w : ℂ, (w ∈ slitPlane ∨ w = 0) →
      ContinuousOn (fun t : ℝ => w / ((t : ℂ) + w)) (Ioi 0) := fun w hw =>
    continuousOn_const.div (continuous_ofReal.add continuous_const).continuousOn (hne w hw)
  refine p19sR1_integrableOn_of_le (C := C * (Ka + Kb + Kc)) ?_ fun t ht => ?_
  · exact ((p19sR1_continuousOn_inv_s ha (Or.inl hb) (Or.inl hc)).mul
      (((hcd a ha).add (hcd b (Or.inl hb))).add (hcd c (Or.inl hc)))).mul
      continuous_ofReal.continuousOn
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le, mul_assoc]
    have h1 := hC t ht
    have h2 : ‖a / ((t : ℂ) + a) + b / ((t : ℂ) + b) + c / ((t : ℂ) + c)‖ * t ≤ Ka + Kb + Kc := by
      have := norm_add₃_le (a := a / ((t : ℂ) + a)) (b := b / ((t : ℂ) + b))
        (c := c / ((t : ℂ) + c))
      have := hKa t ht; have := hKb t ht; have := hKc t ht
      nlinarith
    calc _ ≤ C * (Real.sqrt t * (t + 1))⁻¹ * (Ka + Kb + Kc) :=
          mul_le_mul h1 h2 (by positivity) (le_trans (norm_nonneg _) h1)
      _ = _ := by ring

/-- The algebraic identity behind `p19sR1_RG_identity`, with `u² = t + x` etc. -/
lemma p19sR1_alg_RG (t u v w x y z : ℂ) (hu : u ^ 2 = t + x) (hv : v ^ 2 = t + y)
    (hw : w ^ 2 = t + z) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hw0 : w ≠ 0) :
    (x + y) * (u * v * w)⁻¹ + (t * (x + y) + x * y) *
      (-((u / (2 * (t + x)) * v + u * (v / (2 * (t + y)))) * w + u * v * (w / (2 * (t + z)))) /
        (u * v * w) ^ 2) =
    -(1 / 2) * ((u * v * w)⁻¹ * (x / (t + x) + y / (t + y) + z / (t + z)) * t - z * (u * v * w)⁻¹
      + (x - z) * (y - z) * (u * v * w * (t + z))⁻¹) := by
  obtain rfl : x = u ^ 2 - t := by linear_combination -hu
  obtain rfl : y = v ^ 2 - t := by linear_combination -hv
  obtain rfl : z = w ^ 2 - t := by linear_combination -hw
  simp only [add_sub_cancel]
  field_simp
  ring

/-- **The integral identity behind DLMF 19.21.10**, by an exact antiderivative
`h(t) = (t (x + y) + xy)/s(t)`: with `s(t) = √(t+x) √(t+y) √(t+z)`, `x` admissible (possibly
`0`) and `y, z` in the slit plane,
`∫ s⁻¹ (∑ x/(t+x)) t - z ∫ s⁻¹ + (x - z)(y - z) ∫ (s (t + z))⁻¹ = 2 x^{1/2} y^{1/2} z^{-1/2}`. -/
theorem p19sR1_RG_identity {x y z : ℂ} (hx : x ∈ slitPlane ∨ x = 0) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    (∫ t in Ioi (0 : ℝ), (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y) ^ (1 / 2 : ℂ) *
        ((t : ℂ) + z) ^ (1 / 2 : ℂ))⁻¹ *
        (x / ((t : ℂ) + x) + y / ((t : ℂ) + y) + z / ((t : ℂ) + z)) * t)
      - z * (∫ t in Ioi (0 : ℝ), (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y) ^ (1 / 2 : ℂ) *
        ((t : ℂ) + z) ^ (1 / 2 : ℂ))⁻¹)
      + (x - z) * (y - z) * (∫ t in Ioi (0 : ℝ), (((t : ℂ) + x) ^ (1 / 2 : ℂ) *
        ((t : ℂ) + y) ^ (1 / 2 : ℂ) * ((t : ℂ) + z) ^ (1 / 2 : ℂ) * ((t : ℂ) + z))⁻¹)
      = 2 * (x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ)) := by
  set S : ℝ → ℂ := fun t => ((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y) ^ (1 / 2 : ℂ) *
    ((t : ℂ) + z) ^ (1 / 2 : ℂ) with hS
  set G : ℝ → ℂ := fun t => (S t)⁻¹ *
    (x / ((t : ℂ) + x) + y / ((t : ℂ) + y) + z / ((t : ℂ) + z)) * t with hG
  set F : ℝ → ℂ := fun t => (S t)⁻¹ with hF
  set D : ℝ → ℂ := fun t => (S t * ((t : ℂ) + z))⁻¹ with hD
  have iG : IntegrableOn G (Ioi 0) := p19sR1_integrableOn_RG hx hy hz
  have iF : IntegrableOn F (Ioi 0) := p19sR1_integrableOn_RF hx hy hz
  have iD : IntegrableOn D (Ioi 0) := p19sR1_integrableOn_RJ hx hy hz hz
  set f : ℝ → ℂ := fun t => -(1 / 2) * (G t - z * F t + (x - z) * (y - z) * D t) with hf
  set h : ℝ → ℂ := fun t => ((t : ℂ) * (x + y) + x * y) * (S t)⁻¹ with hh
  have iff : IntegrableOn f (Ioi 0) :=
    ((iG.sub (iF.const_mul z)).add (iD.const_mul ((x - z) * (y - z)))).const_mul _
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt h (f t) t := by
    intro t ht
    have hx' := p19sR1_add_mem_slitPlane ht hx
    have hy' := p19sR1_add_mem_slitPlane ht (Or.inl hy)
    have hz' := p19sR1_add_mem_slitPlane ht (Or.inl hz)
    have hs := ((p19sR1_hasDerivAt_cpow_half hx').mul (p19sR1_hasDerivAt_cpow_half hy')).mul
      (p19sR1_hasDerivAt_cpow_half hz')
    have hu0 := p19sR1_cpow_half_ne_zero ht hx
    have hv0 := p19sR1_cpow_half_ne_zero ht (Or.inl hy)
    have hw0 := p19sR1_cpow_half_ne_zero ht (Or.inl hz)
    have hinv := hs.inv (mul_ne_zero (mul_ne_zero hu0 hv0) hw0)
    have hp : HasDerivAt (fun s : ℝ => (s : ℂ) * (x + y) + x * y) (1 * (x + y)) t :=
      ((hasDerivAt_id (t : ℂ)).comp_ofReal.mul_const (x + y)).add_const (x * y)
    have := hp.mul hinv
    rw [one_mul] at this
    convert this using 1
    simp only [hf, hG, hF, hD, hS, Pi.mul_apply, Pi.inv_apply]
    exact (p19sR1_alg_RG (t : ℂ) _ _ _ x y z (p19sR1_cpow_half_sq _) (p19sR1_cpow_half_sq _)
      (p19sR1_cpow_half_sq _) hu0 hv0 hw0).symm
  obtain ⟨C, hC⟩ := p19sR1_norm_inv_s_le hx hy hz
  have hC0 : 0 ≤ C := by
    have := hC 1 one_pos
    have h2 : 0 < (Real.sqrt 1 * (1 + 1))⁻¹ := by positivity
    by_contra hneg; push Not at hneg
    have : C * (Real.sqrt 1 * (1 + 1))⁻¹ < 0 := mul_neg_of_neg_of_pos hneg h2
    linarith [norm_nonneg (S 1)⁻¹]
  have hbound : ∀ t : ℝ, 0 < t → ‖h t‖ ≤ (‖x + y‖ + ‖x * y‖) * C * (Real.sqrt t)⁻¹ := by
    intro t ht
    have h1 := hC t ht
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    have hpoly : ‖(t : ℂ) * (x + y) + x * y‖ ≤ (‖x + y‖ + ‖x * y‖) * (t + 1) := by
      calc _ ≤ ‖(t : ℂ) * (x + y)‖ + ‖x * y‖ := norm_add_le _ _
        _ = t * ‖x + y‖ + ‖x * y‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
        _ ≤ _ := by nlinarith [norm_nonneg (x + y), norm_nonneg (x * y)]
    simp only [hh]
    rw [norm_mul]
    calc _ ≤ (‖x + y‖ + ‖x * y‖) * (t + 1) * (C * (Real.sqrt t * (t + 1))⁻¹) :=
          mul_le_mul hpoly h1 (norm_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hlim : Tendsto h atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun t => (‖x + y‖ + ‖x * y‖) * C * (Real.sqrt t)⁻¹) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with t ht using hbound t ht
    · simpa using (Real.tendsto_sqrt_atTop.inv_tendsto_atTop).const_mul ((‖x + y‖ + ‖x * y‖) * C)
  have hcont : ContinuousWithinAt h (Ici 0) 0 := by
    rcases hx with hx | rfl
    · refine ContinuousAt.continuousWithinAt ?_
      have h0 : ∀ w : ℂ, w ∈ slitPlane → ((0 : ℝ) : ℂ) + w ∈ slitPlane := fun w hw => by simpa
      refine ((((continuous_ofReal.mul continuous_const).add continuous_const).continuousAt).mul
        ((((p19sR1_continuousAt_cpow_half (h0 x hx)).mul
          (p19sR1_continuousAt_cpow_half (h0 y hy))).mul
          (p19sR1_continuousAt_cpow_half (h0 z hz))).inv₀ ?_))
      exact mul_ne_zero (mul_ne_zero (p19sR1_cpow_half_ne_zero_of_mem (h0 x hx))
        (p19sR1_cpow_half_ne_zero_of_mem (h0 y hy))) (p19sR1_cpow_half_ne_zero_of_mem (h0 z hz))
    · have h00 : h 0 = 0 := by simp [hh]
      rw [ContinuousWithinAt, h00]
      have hb0 : ∀ t ∈ Ici (0 : ℝ), ‖h t‖ ≤ ‖y‖ * C * Real.sqrt t := by
        intro t ht
        rcases (mem_Ici.mp ht).eq_or_lt with rfl | ht
        · rw [h00, norm_zero]; positivity
        · have h1 := hC t ht
          have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
          simp only [hh, add_zero, zero_add, zero_mul]
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
          calc _ ≤ t * ‖y‖ * (C * (Real.sqrt t * (t + 1))⁻¹) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = ‖y‖ * C * (t / Real.sqrt t) * (t + 1)⁻¹ := by rw [mul_inv]; ring
            _ = ‖y‖ * C * Real.sqrt t * (t + 1)⁻¹ := by rw [Real.div_sqrt]
            _ ≤ _ := by
                have : (t + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
                have : 0 ≤ ‖y‖ * C * Real.sqrt t := by positivity
                nlinarith
      refine squeeze_zero_norm' (a := fun t => ‖y‖ * C * Real.sqrt t) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with t ht using hb0 t ht
      · have : Tendsto (fun t : ℝ => ‖y‖ * C * Real.sqrt t) (𝓝 0) (𝓝 (‖y‖ * C * Real.sqrt 0)) :=
          (Real.continuous_sqrt.tendsto 0).const_mul _
        rw [Real.sqrt_zero, mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv iff hlim
  have hsplit : ∫ t in Ioi (0 : ℝ), f t = -(1 / 2) * ((∫ t in Ioi (0 : ℝ), G t) -
      z * (∫ t in Ioi (0 : ℝ), F t) + (x - z) * (y - z) * ∫ t in Ioi (0 : ℝ), D t) := by
    have i1 : IntegrableOn (fun a => G a - z * F a) (Ioi 0) := iG.sub (iF.const_mul z)
    have i2 : IntegrableOn (fun a => (x - z) * (y - z) * D a) (Ioi 0) := iD.const_mul _
    simp only [hf]
    rw [integral_const_mul, integral_add i1 i2, integral_sub iG (iF.const_mul z),
      integral_const_mul, integral_const_mul]
  have h0 : h 0 = x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ) := by
    simp only [hh, hS, ofReal_zero, zero_mul, zero_add]
    rcases hx with hx | rfl
    · have e1 := p19sR1_cpow_half_sq x
      have e2 := p19sR1_cpow_half_sq y
      have hx0 : x ^ (1 / 2 : ℂ) ≠ 0 := fun h => slitPlane_ne_zero hx ((cpow_eq_zero_iff _ _).mp h).1
      have hy0 : y ^ (1 / 2 : ℂ) ≠ 0 := fun h => slitPlane_ne_zero hy ((cpow_eq_zero_iff _ _).mp h).1
      have hz0 : z ^ (1 / 2 : ℂ) ≠ 0 := fun h => slitPlane_ne_zero hz ((cpow_eq_zero_iff _ _).mp h).1
      rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, cpow_neg]
      field_simp
      rw [e1, e2]
    · simp
  rw [hsplit, h0] at key
  simp only [hG, hF, hD] at key
  linear_combination (-2) * key
end DLMF.EllipticIntegrals
