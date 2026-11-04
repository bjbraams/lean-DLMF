/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Properties.BasicSolutions
public import DLMF.Mathieu.SturmBridge
public import DLMFMathlib.Analysis.ODE.SturmDeformationContinuity

/-!
# Continuity of the Mathieu eigenvalues and of the zeros of `ce_n`, `se_n` in `q`

For real `q` the eigenvalues `a_n(q)`, `b_n(q)` (DLMF §28.2(v)) are the ordered real roots of
the four characteristic functions `w_I'(π/2; a, q)`, `w_I(π/2; a, q)`, `w_II'(π/2; a, q)`,
`w_II(π/2; a, q)` of Table 28.2.1. Lagrange's identity on `[0, π/2]` gives a difference formula
`F(a', q) - F(a, q) = (a' - a) g(a, a', q)` with `g` jointly continuous, and the Wronskian shows
that `g(a, a, q) ≠ 0` at a root: all roots are simple. Since no root lies below `-(2|q| + 1)`,
the `k`-th root depends continuously on `q`
(`ODE.SturmDeformation.eventually_exists_zero_encard_inter_Iio_eq`).

The zeros of `w_I(x; a_n(q), q)` and `w_II(x; b_n(q), q)` in `0 < x < π/2` are simple and their
number does not depend on `q` (Sturm oscillation, `DLMF.Mathieu.encard_zeros_mathieuWI_mathieuA`),
so the same argument, now in the variable `x`, shows that they are continuous functions of `q`
(DLMF §28.9).

## Main results

* `continuous_mathieuA`, `continuous_mathieuB`: `a_n(q)`, `b_n(q)` are continuous in real `q`.
* `exists_continuous_zeros_mathieuWI_mathieuA`, `exists_continuous_zeros_mathieuWII_mathieuB`:
  the zeros of `w_I(x; a_n(q), q)` and `w_II(x; b_n(q), q)` in `(0, π/2)` are continuous
  functions of `q`.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real

namespace DLMF.Mathieu

namespace SpectralContinuity

/-! ### The real basic solutions -/

/-- The basic solution `w_I` (`b = false`) or `w_II` (`b = true`). -/
private def W (b : Bool) (a q : ℂ) : ℂ → ℂ := if b then mathieuWII a q else mathieuWI a q

private lemma isMathieuSolution_W (b : Bool) (a q : ℂ) : IsMathieuSolution a q (W b a q) := by
  cases b
  · exact isMathieuSolution_mathieuWI a q
  · exact isMathieuSolution_mathieuWII a q

private lemma W_zero (b : Bool) (a q : ℂ) : W b a q 0 = ((if b then 0 else 1 : ℝ) : ℂ) := by
  cases b
  · simp [W, (mathieuWI_spec a q).2.1]
  · simp [W, (mathieuWII_spec a q).2.1]

private lemma deriv_W_zero (b : Bool) (a q : ℂ) :
    deriv (W b a q) 0 = ((if b then 1 else 0 : ℝ) : ℂ) := by
  cases b
  · simp [W, (mathieuWI_spec a q).2.2]
  · simp [W, (mathieuWII_spec a q).2.2]

private lemma fam (b : Bool) (Q : ℝ) :
    (∀ (a x : ℝ), W b a Q x = ((W b a Q x).re : ℂ) ∧
      deriv (W b a Q) x = ((deriv (W b a Q) x).re : ℂ)) ∧
    (∀ (a x : ℝ), HasDerivAt (fun x : ℝ => (W b a Q x).re) (deriv (W b a Q) x).re x) ∧
    (∀ (a x : ℝ), HasDerivAt (fun x : ℝ => (deriv (W b a Q) x).re)
      ((2 * Q * Real.cos (2 * x) - a) * (W b a Q x).re) x) ∧
    ∀ (x : ℝ), (Differentiable ℂ fun a => W b a Q x) ∧
      Differentiable ℂ fun a => deriv (W b a Q) x :=
  real_family_of_isMathieuSolution Q (w := fun a => W b a Q)
    (fun a => isMathieuSolution_W b a Q) (W_zero b · Q) (deriv_W_zero b · Q)

/-- Real restriction of the basic solution. -/
private def R (b : Bool) (a Q x : ℝ) : ℝ := (W b a Q x).re
/-- Real restriction of its derivative. -/
private def D (b : Bool) (a Q x : ℝ) : ℝ := (deriv (W b a Q) x).re

private lemma R_real (b : Bool) (a Q x : ℝ) : W b a Q x = (R b a Q x : ℂ) := ((fam b Q).1 a x).1
private lemma D_real (b : Bool) (a Q x : ℝ) : deriv (W b a Q) x = (D b a Q x : ℂ) :=
  ((fam b Q).1 a x).2

private lemma hasDerivAt_R (b : Bool) (a Q x : ℝ) : HasDerivAt (R b a Q) (D b a Q x) x :=
  (fam b Q).2.1 a x
private lemma hasDerivAt_D (b : Bool) (a Q x : ℝ) :
    HasDerivAt (D b a Q) ((2 * Q * Real.cos (2 * x) - a) * R b a Q x) x :=
  (fam b Q).2.2.1 a x

private lemma R_zero (b : Bool) (a Q : ℝ) : R b a Q 0 = if b then 0 else 1 := by
  simp only [R]
  rw [show ((0 : ℝ) : ℂ) = 0 from Complex.ofReal_zero, W_zero, Complex.ofReal_re]
private lemma D_zero (b : Bool) (a Q : ℝ) : D b a Q 0 = if b then 1 else 0 := by
  simp only [D]
  rw [show ((0 : ℝ) : ℂ) = 0 from Complex.ofReal_zero, deriv_W_zero, Complex.ofReal_re]

/-- The sign of the Wronskian `R_b D_{¬b} - D_b R_{¬b}`. -/
private def sgn (b : Bool) : ℝ := if b then -1 else 1

private lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> norm_num [sgn]

private lemma wronskian (b : Bool) (a Q x : ℝ) :
    R b a Q x * D (!b) a Q x - D b a Q x * R (!b) a Q x = sgn b := by
  have h := mathieuWI_wronskian (a := (a : ℂ)) (q := (Q : ℂ)) (x : ℂ)
  have e1 := R_real false a Q x
  have e2 := R_real true a Q x
  have e3 := D_real false a Q x
  have e4 := D_real true a Q x
  simp only [W, Bool.false_eq_true, ↓reduceIte] at e1 e2 e3 e4
  rw [e1, e2, e3, e4] at h
  have h' : R false a Q x * D true a Q x - D false a Q x * R true a Q x = 1 := by exact_mod_cast h
  cases b
  · simpa [sgn] using h'
  · simp only [Bool.not_true, sgn, ↓reduceIte]; linarith

private lemma continuous_R (b : Bool) :
    Continuous (fun p : ℝ × ℝ × ℝ => R b p.1 p.2.1 p.2.2) := by
  have hm : Continuous (fun p : ℝ × ℝ × ℝ => (((p.2.2 : ℝ) : ℂ), ((p.1 : ℝ) : ℂ),
      ((p.2.1 : ℝ) : ℂ))) := by fun_prop
  cases b
  · exact Complex.continuous_re.comp (differentiable_mathieuWI_mathieuWII.1.continuous.comp hm)
  · exact Complex.continuous_re.comp (differentiable_mathieuWI_mathieuWII.2.continuous.comp hm)

private lemma D_eq (b : Bool) (a Q x : ℝ) :
    D b a Q x = D b a Q 0 + ∫ s in (0 : ℝ)..x, (2 * Q * Real.cos (2 * s) - a) * R b a Q s := by
  have hc : Continuous (fun s => (2 * Q * Real.cos (2 * s) - a) * R b a Q s) := by
    have : Continuous (R b a Q) := (continuous_R b).comp (by fun_prop :
      Continuous (fun x : ℝ => (a, Q, x)))
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_D b a Q s)
    (hc.intervalIntegrable _ _)]
  ring

private lemma continuous_D (b : Bool) :
    Continuous (fun p : ℝ × ℝ × ℝ => D b p.1 p.2.1 p.2.2) := by
  have e : (fun p : ℝ × ℝ × ℝ => D b p.1 p.2.1 p.2.2) = fun p =>
      (if b then 1 else 0) + ∫ s in (0 : ℝ)..p.2.2,
        (2 * p.2.1 * Real.cos (2 * s) - p.1) * R b p.1 p.2.1 s := by
    funext p; rw [D_eq, D_zero]
  rw [e]
  refine continuous_const.add ?_
  have hf : Continuous (Function.uncurry fun (p : ℝ × ℝ) (s : ℝ) =>
      (2 * p.2 * Real.cos (2 * s) - p.1) * R b p.1 p.2 s) := by
    have : Continuous (fun p : (ℝ × ℝ) × ℝ => R b p.1.1 p.1.2 p.2) :=
      (continuous_R b).comp (by fun_prop :
        Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.1, p.1.2, p.2)))
    exact (by fun_prop : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      (2 * p.1.2 * Real.cos (2 * p.2) - p.1.1))).mul this
  have := intervalIntegral.continuous_parametric_primitive_of_continuous
    (μ := MeasureTheory.volume) (a₀ := 0) hf
  exact this.comp (by fun_prop : Continuous (fun p : ℝ × ℝ × ℝ => ((p.1, p.2.1), p.2.2)))

/-! ### Lagrange's identity and the difference formula -/

/-- Lagrange's identity on `[0, X]` for solutions with parameters `a` and `a'`. -/
private lemma integral_cross {a a' Q X : ℝ} {y y' z z' : ℝ → ℝ}
    (hy : ∀ x, HasDerivAt y (y' x) x)
    (hy' : ∀ x, HasDerivAt y' ((2 * Q * Real.cos (2 * x) - a) * y x) x)
    (hz : ∀ x, HasDerivAt z (z' x) x)
    (hz' : ∀ x, HasDerivAt z' ((2 * Q * Real.cos (2 * x) - a') * z x) x) :
    (a' - a) * ∫ x in (0 : ℝ)..X, z x * y x =
      (z X * y' X - z' X * y X) - (z 0 * y' 0 - z' 0 * y 0) := by
  have hc : Continuous (fun x => (a' - a) * (z x * y x)) := by
    have := continuous_iff_continuousAt.2 fun x => (hz x).continuousAt
    have := continuous_iff_continuousAt.2 fun x => (hy x).continuousAt
    fun_prop
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => z x * y' x - z' x * y x)
    (fun x _ => ?_) (hc.intervalIntegrable _ _)
  convert ((hz x).mul (hy' x)).sub ((hz' x).mul (hy x)) using 1
  ring

/-- `∫₀^X R_b(a') R_c(a)`. -/
private def I (b c : Bool) (a a' Q X : ℝ) : ℝ := ∫ x in (0 : ℝ)..X, R b a' Q x * R c a Q x

/-- **Difference formulas** for the basic solutions at `X`. -/
private lemma R_sub_and_D_sub (b : Bool) (a a' Q X : ℝ) :
    R b a' Q X - R b a Q X = (a' - a) * (sgn b * (R b a Q X * I b (!b) a a' Q X -
        R (!b) a Q X * I b b a a' Q X)) ∧
      D b a' Q X - D b a Q X = (a' - a) * (sgn b * (D b a Q X * I b (!b) a a' Q X -
        D (!b) a Q X * I b b a a' Q X)) := by
  have h1 := integral_cross (X := X) (hasDerivAt_R b a Q) (hasDerivAt_D b a Q)
    (hasDerivAt_R b a' Q) (hasDerivAt_D b a' Q)
  have h2 := integral_cross (X := X) (hasDerivAt_R (!b) a Q) (hasDerivAt_D (!b) a Q)
    (hasDerivAt_R b a' Q) (hasDerivAt_D b a' Q)
  have hW0 := wronskian b a Q 0
  have hWX := wronskian b a Q X
  have hs := sgn_mul_self b
  have e1 : R b a' Q 0 = R b a Q 0 := by rw [R_zero, R_zero]
  have e2 : D b a' Q 0 = D b a Q 0 := by rw [D_zero, D_zero]
  rw [e1, e2] at h1 h2
  simp only [I]
  constructor
  · linear_combination (-(sgn b * R b a Q X)) * h2 + (sgn b * R (!b) a Q X) * h1 +
      (-(sgn b * R b a' Q X)) * hWX + (sgn b * R b a Q X) * hW0 +
      (-(R b a' Q X - R b a Q X)) * hs
  · linear_combination (-(sgn b * D b a Q X)) * h2 + (sgn b * D (!b) a Q X) * h1 +
      (-(sgn b * D b a' Q X)) * hWX + (sgn b * D b a Q X) * hW0 +
      (-(D b a' Q X - D b a Q X)) * hs

private lemma continuous_I (b c : Bool) (X : ℝ) :
    Continuous (fun p : ℝ × ℝ × ℝ => I b c p.1 p.2.1 p.2.2 X) := by
  simp only [I]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have h1 : Continuous (fun p : (ℝ × ℝ × ℝ) × ℝ => R b p.1.2.1 p.1.2.2 p.2) :=
    (continuous_R b).comp (by fun_prop :
      Continuous (fun p : (ℝ × ℝ × ℝ) × ℝ => (p.1.2.1, p.1.2.2, p.2)))
  have h2 : Continuous (fun p : (ℝ × ℝ × ℝ) × ℝ => R c p.1.1 p.1.2.2 p.2) :=
    (continuous_R c).comp (by fun_prop :
      Continuous (fun p : (ℝ × ℝ × ℝ) × ℝ => (p.1.1, p.1.2.2, p.2)))
  exact h1.mul h2

/-! ### The characteristic functions at `π/2` -/

/-- The characteristic function: `w_b'(π/2; a, Q)` (`e = true`) or `w_b(π/2; a, Q)`. -/
private def F (e b : Bool) (a Q : ℝ) : ℝ := if e then D b a Q (π / 2) else R b a Q (π / 2)

/-- The slope in the difference formula for `F`. -/
private def G (e b : Bool) (a a' Q : ℝ) : ℝ :=
  sgn b * (F e b a Q * I b (!b) a a' Q (π / 2) - F e (!b) a Q * I b b a a' Q (π / 2))

private lemma F_sub (e b : Bool) (a a' Q : ℝ) :
    F e b a' Q - F e b a Q = (a' - a) * G e b a a' Q := by
  obtain ⟨h1, h2⟩ := R_sub_and_D_sub b a a' Q (π / 2)
  cases e
  · simpa [F, G] using h1
  · simpa [F, G] using h2

private lemma continuous_F (e b : Bool) : Continuous (fun p : ℝ × ℝ => F e b p.1 p.2) := by
  cases e
  · exact (continuous_R b).comp (by fun_prop : Continuous (fun p : ℝ × ℝ => (p.1, p.2, π / 2)))
  · exact (continuous_D b).comp (by fun_prop : Continuous (fun p : ℝ × ℝ => (p.1, p.2, π / 2)))

private lemma continuous_G (e b : Bool) :
    Continuous (fun p : ℝ × ℝ × ℝ => G e b p.1 p.2.1 p.2.2) := by
  have hF : ∀ c : Bool, Continuous (fun p : ℝ × ℝ × ℝ => F e c p.1 p.2.2) := fun c =>
    (continuous_F e c).comp (by fun_prop : Continuous (fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)))
  simp only [G]
  exact continuous_const.mul (((hF b).mul (continuous_I b (!b) _)).sub
    ((hF (!b)).mul (continuous_I b b _)))

/-- The derivative of `a ↦ F(a, Q)` is `G(a, a, Q)`. -/
private lemma hasDerivAt_F (e b : Bool) (a Q : ℝ) :
    HasDerivAt (fun a => F e b a Q) (G e b a a Q) a := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hc : Tendsto (fun a' => G e b a a' Q) (𝓝[≠] a) (𝓝 (G e b a a Q)) := by
    have : Continuous (fun a' => G e b a a' Q) :=
      (continuous_G e b).comp (by fun_prop : Continuous (fun a' : ℝ => (a, a', Q)))
    exact this.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine hc.congr' (eventually_nhdsWithin_of_forall fun a' ha' => ?_)
  have hne : a' - a ≠ 0 := sub_ne_zero.mpr ha'
  rw [slope_def_field, F_sub]
  field_simp

/-- A solution with nonzero initial data has `∫₀^X y² > 0`. -/
private lemma integral_mul_self_pos {y y' : ℝ → ℝ} (hy : ∀ x, HasDerivAt y (y' x) x)
    (hne : y 0 ≠ 0 ∨ y' 0 ≠ 0) {X : ℝ} (hX : 0 < X) : 0 < ∫ x in (0 : ℝ)..X, y x * y x := by
  have hc : Continuous y := continuous_iff_continuousAt.2 fun x => (hy x).continuousAt
  obtain ⟨p, hp, hyp⟩ : ∃ p ∈ Ioo 0 X, y p ≠ 0 := by
    by_cases h0 : y 0 = 0
    · have h1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), y x ≠ y 0 :=
        ((hy 0).eventually_ne (hne.resolve_left (not_not.mpr h0))).filter_mono
          (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
      obtain ⟨p, hp1, hp2⟩ := (h1.and (Ioo_mem_nhdsGT hX)).exists
      exact ⟨p, hp2, h0 ▸ hp1⟩
    · have h1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), y x ≠ 0 :=
        nhdsWithin_le_nhds (hc.continuousAt.eventually_ne h0)
      obtain ⟨p, hp1, hp2⟩ := (h1.and (Ioo_mem_nhdsGT hX)).exists
      exact ⟨p, hp2, hp1⟩
  have hcont : Continuous (fun x => y x * y x) := hc.mul hc
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae'
    (MeasureTheory.ae_of_all _ fun x => mul_self_nonneg _) (hcont.intervalIntegrable _ _)]
  refine ⟨hX, ?_⟩
  have hopen : IsOpen (Function.support fun x => y x * y x) := hcont.isOpen_support
  have hpS : p ∈ Function.support fun x => y x * y x := by simpa using hyp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen p hpS
  set r := min ε (min p (X - p)) with hr
  have hr0 : 0 < r := lt_min hε (lt_min hp.1 (by linarith [hp.2]))
  have hsub : Ioo (p - r) (p + r) ⊆ (Function.support fun x => y x * y x) ∩ Ioc 0 X := by
    intro x hx
    have h1 : r ≤ ε := min_le_left _ _
    have h2 : r ≤ p := (min_le_right _ _).trans (min_le_left _ _)
    have h3 : r ≤ X - p := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨hball ?_, by linarith [hx.1], by linarith [hx.2]⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  refine lt_of_lt_of_le ?_ (MeasureTheory.measure_mono hsub)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (by linarith)

/-- **Simple roots**: at a root of `F`, the derivative `G(a, a, Q)` does not vanish. -/
private lemma G_ne_zero (e b : Bool) {a Q : ℝ} (h : F e b a Q = 0) : G e b a a Q ≠ 0 := by
  have hW := wronskian b a Q (π / 2)
  have hF' : F e (!b) a Q ≠ 0 := by
    intro h'
    cases e <;> simp only [F, Bool.false_eq_true, ↓reduceIte] at h h' <;>
      rw [h, h'] at hW <;> cases b <;> norm_num [sgn] at hW
  have hI : 0 < I b b a a Q (π / 2) := integral_mul_self_pos (hasDerivAt_R b a Q)
    (by cases b <;> simp [R_zero, D_zero]) (by positivity)
  simp only [G, h, zero_mul, zero_sub, mul_neg, neg_ne_zero]
  refine mul_ne_zero (by cases b <;> norm_num [sgn]) (mul_ne_zero hF' hI.ne')

/-- No roots below `-(2|Q| + 1)`. -/
private lemma F_ne_zero_of_lt (e b : Bool) {a Q : ℝ} (ha : a < -(2 * |Q| + 1)) :
    F e b a Q ≠ 0 := by
  have hQ : ∀ x ∈ Icc (0 : ℝ) (π / 2), |2 * Q * Real.cos (2 * x)| ≤ 2 * |Q| + 1 := by
    intro x _
    rw [abs_mul, abs_mul, abs_two]
    have := Real.abs_cos_le_one (2 * x)
    nlinarith [abs_nonneg Q]
  have h := ODE.endpoint_ne_zero_of_lt_neg (Q := fun x => 2 * Q * Real.cos (2 * x))
    (by positivity) hQ ha (hasDerivAt_R b a Q) (hasDerivAt_D b a Q)
    (by cases b <;> simp [R_zero, D_zero]) (by cases b <;> simp [R_zero, D_zero])
  cases e
  · exact h.1
  · exact h.2

/-- **Continuity of the `k`-th root** of `F(·, Q)` in `Q`. -/
private lemma continuous_nthLeast (e b : Bool) (k : ℕ)
    (hex : ∀ Q, ∃ x ∈ {a : ℝ | F e b a Q = 0}, ({a : ℝ | F e b a Q = 0} ∩ Iio x).encard = k) :
    Continuous fun Q => nthLeast {a : ℝ | F e b a Q = 0} k := by
  rw [continuous_iff_continuousAt]
  intro Q₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨hz, hzk⟩ := nthLeast_spec (hex Q₀)
  set z := nthLeast {a : ℝ | F e b a Q₀ = 0} k with hzdef
  set A := -(2 * (|Q₀| + 1) + 1) - 1 with hA
  have hnear : ∀ᶠ Q in 𝓝 Q₀, |Q| < |Q₀| + 1 := by
    filter_upwards [Metric.ball_mem_nhds Q₀ one_pos] with Q hQ
    rw [Metric.mem_ball, Real.dist_eq] at hQ
    have := abs_sub_abs_le_abs_sub Q Q₀
    linarith
  have hlow : ∀ Q, |Q| < |Q₀| + 1 → ∀ a, a ≤ A + 1 → F e b a Q ≠ 0 := fun Q hQ a ha =>
    F_ne_zero_of_lt e b (by linarith)
  have hset : ∀ Q, |Q| < |Q₀| + 1 → {a | A < a ∧ F e b a Q = 0} = {a | F e b a Q = 0} := by
    intro Q hQ
    ext a
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    by_contra hle
    exact hlow Q hQ a (by linarith) h
  have hQ₀ : |Q₀| < |Q₀| + 1 := by linarith
  have hzA : A < z := by
    by_contra hle
    exact hlow Q₀ hQ₀ z (by linarith) hz
  have hcY : ContinuousOn (Function.uncurry fun Q a => F e b a Q) (univ ×ˢ univ) :=
    ((continuous_F e b).comp continuous_swap).continuousOn
  have hcY' : ContinuousOn (Function.uncurry fun Q a => G e b a a Q) (univ ×ˢ univ) :=
    ((continuous_G e b).comp (by fun_prop :
      Continuous (fun p : ℝ × ℝ => (p.2, p.2, p.1)))).continuousOn
  have hev := ODE.SturmDeformation.eventually_exists_zero_encard_inter_Iio_eq
    (Y := fun Q a => F e b a Q) (Y' := fun Q a => G e b a a Q) isOpen_univ hcY hcY'
    (fun Q _ a _ => hasDerivAt_F e b a Q) (fun Q _ a _ h => G_ne_zero e b h) (mem_univ Q₀)
    (A := A) one_pos (by
      filter_upwards [hnear] with Q hQ x hx
      exact hlow Q hQ x hx.2) hzA hz (by rw [hset Q₀ hQ₀]; exact hzk) hε
  filter_upwards [hev, hnear] with Q hx hQ
  obtain ⟨x, hxz, -, hx0, hxk⟩ := hx
  rw [hset Q hQ] at hxk
  rw [nthLeast_eq_of hx0 hxk, Real.dist_eq]
  exact hxz

/-- `((π / 2 : ℝ) : ℂ) = π / 2`. -/
private lemma ofReal_pi_div_two' : ((π / 2 : ℝ) : ℂ) = (π : ℂ) / 2 := by push_cast; ring

private lemma mathieuSpecA_eq (n : ℕ) (q : ℝ) :
    mathieuSpecA n q = {a : ℝ | F (decide (Even n)) false a q = 0} := by
  unfold mathieuSpecA
  have e1 := fun a : ℝ => R_real false a q (π / 2)
  have e2 := fun a : ℝ => D_real false a q (π / 2)
  simp only [W, Bool.false_eq_true, ↓reduceIte, ofReal_pi_div_two'] at e1 e2
  split_ifs with h
  · ext a; simp [F, h, e2 a]
  · ext a; simp [F, h, e1 a]

private lemma mathieuSpecB_eq (n : ℕ) (q : ℝ) :
    mathieuSpecB n q = {a : ℝ | F (!decide (Even n)) true a q = 0} := by
  unfold mathieuSpecB
  have e1 := fun a : ℝ => R_real true a q (π / 2)
  have e2 := fun a : ℝ => D_real true a q (π / 2)
  simp only [W, ↓reduceIte, ofReal_pi_div_two'] at e1 e2
  split_ifs with h
  · ext a; simp [F, h, e1 a]
  · ext a; simp [F, h, e2 a]

end SpectralContinuity

open SpectralContinuity

/-- **Continuity of `a_n(q)`** in real `q` (DLMF §28.2(v), §28.7: the eigenvalues are analytic,
in particular continuous, functions of real `q`). -/
theorem continuous_mathieuA (n : ℕ) : Continuous (mathieuA n) := by
  have e : mathieuA n = fun q => nthLeast {a : ℝ | F (decide (Even n)) false a q = 0} (n / 2) :=
    funext fun q => by simp only [mathieuA, mathieuSpecA_eq]
  rw [e]
  exact continuous_nthLeast _ _ _ fun q => by
    rw [← mathieuSpecA_eq]; exact mathieuSpecA_exists n q _

/-- **Continuity of `b_n(q)`** in real `q` (DLMF §28.2(v)); `b_0` is the junk value `0`. -/
theorem continuous_mathieuB (n : ℕ) : Continuous (mathieuB n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have e : mathieuB 0 = fun _ => 0 := funext fun q => by simp [mathieuB]
    rw [e]; exact continuous_const
  have e : mathieuB n = fun q =>
      nthLeast {a : ℝ | F (!decide (Even n)) true a q = 0} ((n - 1) / 2) :=
    funext fun q => by simp only [mathieuB, hn, ↓reduceIte, mathieuSpecB_eq]
  rw [e]
  exact continuous_nthLeast _ _ _ fun q => by
    rw [← mathieuSpecB_eq]; exact mathieuSpecB_exists n q _

namespace SpectralContinuity

/-! ### Zeros in `x` -/

/-- The elements of a finite set of reals can be enumerated in increasing order. -/
private lemma exists_encard_inter_Iio_of_encard {S : Set ℝ} {n : ℕ} (hS : S.encard = n)
    {k : ℕ} (hk : k < n) : ∃ x ∈ S, (S ∩ Iio x).encard = k := by
  have hfin : S.Finite := Set.finite_of_encard_eq_coe hS
  have hcard : hfin.toFinset.card = n := by
    rw [← Set.ncard_eq_toFinset_card S hfin]; exact ncard_eq_of_encard_eq_natCast hS
  set f := hfin.toFinset.orderEmbOfFin hcard
  have hmem : ∀ j, f j ∈ S := fun j => by
    have := hfin.toFinset.orderEmbOfFin_mem hcard j
    rwa [Set.Finite.mem_toFinset] at this
  refine ⟨f ⟨k, hk⟩, hmem _, ?_⟩
  have hset : S ∩ Iio (f ⟨k, hk⟩) = f '' ((Finset.Iio (⟨k, hk⟩ : Fin n) : Finset (Fin n)) :
      Set (Fin n)) := by
    ext y
    constructor
    · rintro ⟨hy, hlt⟩
      have : y ∈ Set.range f := by
        rw [Finset.range_orderEmbOfFin]; simpa using hy
      obtain ⟨j, rfl⟩ := this
      exact ⟨j, by simpa using f.lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨hmem j, f.lt_iff_lt.mpr (by simpa using hj)⟩
  rw [hset, f.injective.encard_image, Set.encard_coe_eq_coe_finsetCard, Fin.card_Iio]

/-- **Continuity of the zeros in `(0, L)`.** For a family `y(t, ·)` with jointly continuous `y`,
`∂ₓ y`, simple zeros, a constant number `n` of zeros in `(0, L)` and no zeros entering at `0`,
the zeros in `(0, L)` are `n` continuous functions of `t`. -/
private lemma exists_continuous_zeros {Y Y' : ℝ → ℝ → ℝ} {L : ℝ}
    (hcY : Continuous (Function.uncurry Y)) (hcY' : Continuous (Function.uncurry Y'))
    (hd : ∀ t x, HasDerivAt (Y t) (Y' t x) x) (hs : ∀ t x, Y t x = 0 → Y' t x ≠ 0)
    (hA : ∀ t₀, ∃ η > 0, ∀ᶠ t in 𝓝 t₀, ∀ x ∈ Ioc 0 η, Y t x ≠ 0) {n : ℕ}
    (hn : ∀ t, {x | x ∈ Ioo 0 L ∧ Y t x = 0}.encard = n) :
    ∃ Z : Fin n → ℝ → ℝ, (∀ k, Continuous (Z k)) ∧
      ∀ t, {x | x ∈ Ioo 0 L ∧ Y t x = 0} = range fun k => Z k t := by
  set E := fun t => {x | x ∈ Ioo 0 L ∧ Y t x = 0} with hE
  refine ⟨fun k t => nthLeast (E t) k, fun k => ?_, fun t => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro t₀
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨hz, hzk⟩ := nthLeast_spec (exists_encard_inter_Iio_of_encard (hn t₀) k.2)
    set z := nthLeast (E t₀) k with hzdef
    have hT : ∀ t x, x ≤ L → {y | 0 < y ∧ Y t y = 0} ∩ Iio x = E t ∩ Iio x := by
      intro t x hx
      ext y
      simp only [hE, mem_inter_iff, mem_ofPred_eq, mem_Ioo, mem_Iio]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨h1, by linarith⟩, h2⟩, h3⟩
      · rintro ⟨⟨⟨h1, -⟩, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    obtain ⟨η, hη, hAη⟩ := hA t₀
    have hεL : 0 < min ε (L - z) := lt_min hε (by linarith [hz.1.2])
    have hev := ODE.SturmDeformation.eventually_exists_zero_encard_inter_Iio_eq (Y := Y)
      (Y' := Y') (Λ := univ) isOpen_univ hcY.continuousOn hcY'.continuousOn
      (fun t _ x _ => hd t x) (fun t _ x _ => hs t x) (mem_univ t₀) (A := 0) hη
      (by simpa using hAη) hz.1.1 hz.2 (by rw [hT t₀ z hz.1.2.le]; exact hzk) hεL
    filter_upwards [hev] with t hx
    obtain ⟨x, hxz, hx0, hxY, hxk⟩ := hx
    have hxε : |x - z| < ε := hxz.trans_le (min_le_left _ _)
    have hxL : x < L := by
      have := hxz.trans_le (min_le_right _ _)
      rw [abs_lt] at this; linarith
    rw [hT t x hxL.le] at hxk
    have hxE : x ∈ E t := ⟨⟨hx0, hxL⟩, hxY⟩
    rw [Real.dist_eq, nthLeast_eq_of hxE hxk]
    exact hxε
  · ext x
    constructor
    · intro hx
      have hfin : (E t ∩ Iio x).Finite :=
        (Set.finite_of_encard_eq_coe (hn t)).subset inter_subset_left
      have hlt : (E t ∩ Iio x).encard < n := by
        rw [← hn t]
        refine (Set.finite_of_encard_eq_coe (hn t)).subset inter_subset_left |>.encard_lt_encard
          ⟨inter_subset_left, fun h => lt_irrefl x (h hx).2⟩
      set j := (E t ∩ Iio x).encard.toNat with hj
      have hjE : (E t ∩ Iio x).encard = j := by
        rw [hj, ENat.natCast_toNat hfin.encard_lt_top.ne]
      have hjn : j < n := by
        have := hlt; rw [hjE] at this; exact_mod_cast this
      exact ⟨⟨j, hjn⟩, nthLeast_eq_of hx hjE⟩
    · rintro ⟨k, rfl⟩
      exact (nthLeast_spec (exists_encard_inter_Iio_of_encard (hn t) k.2)).1

/-- No zeros enter at `0` when `y(t₀, 0) ≠ 0`. -/
private lemma exists_Ioc_ne_zero_of_ne {Y : ℝ → ℝ → ℝ} (hc : Continuous (Function.uncurry Y))
    {t₀ : ℝ} (h : Y t₀ 0 ≠ 0) : ∃ η > 0, ∀ᶠ t in 𝓝 t₀, ∀ x ∈ Ioc 0 η, Y t x ≠ 0 := by
  have hev : ∀ᶠ p in 𝓝 (t₀, (0 : ℝ)), Function.uncurry Y p ≠ 0 :=
    hc.continuousAt.eventually_ne h
  rw [nhds_prod_eq] at hev
  obtain ⟨u, hu, v, hv, huv⟩ := mem_prod_iff.mp hev
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hv
  refine ⟨r / 2, by positivity, ?_⟩
  filter_upwards [hu] with t ht x hx
  refine huv (show (t, x) ∈ u ×ˢ v from ⟨ht, hball ?_⟩)
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx.1]
  linarith [hx.2]

/-- No zeros enter at `0` when `y(t, 0) = 0` for all `t` and the zero at `0` is simple. -/
private lemma exists_Ioc_ne_zero_of_zero {Y Y' : ℝ → ℝ → ℝ}
    (hcY : Continuous (Function.uncurry Y)) (hcY' : Continuous (Function.uncurry Y'))
    (hd : ∀ t x, HasDerivAt (Y t) (Y' t x) x) (h0 : ∀ t, Y t 0 = 0) {t₀ : ℝ}
    (h1 : Y' t₀ 0 ≠ 0) : ∃ η > 0, ∀ᶠ t in 𝓝 t₀, ∀ x ∈ Ioc 0 η, Y t x ≠ 0 := by
  obtain ⟨δ₀, hδ₀, hloc⟩ := ODE.SturmDeformation.local (Λ := univ) (U := univ) isOpen_univ
    isOpen_univ hcY.continuousOn hcY'.continuousOn (fun t _ x _ => hd t x) (mem_univ t₀)
    (mem_univ 0) (h0 t₀) h1
  refine ⟨δ₀ / 2, by positivity, ?_⟩
  filter_upwards [hloc δ₀ hδ₀ le_rfl] with t ht x hx hx0
  obtain ⟨y, -, hy⟩ := ht
  have e1 := hy x ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, hx0⟩
  have e2 := hy 0 ⟨⟨by linarith, by linarith⟩, h0 t⟩
  linarith [hx.1, e1.trans e2.symm]

private lemma mathieuWI_eq_zero_iff (a q x : ℝ) : mathieuWI a q x = 0 ↔ R false a q x = 0 := by
  have := R_real false a q x
  simp only [W, Bool.false_eq_true, ↓reduceIte] at this
  rw [this, Complex.ofReal_eq_zero]

private lemma mathieuWII_eq_zero_iff (a q x : ℝ) : mathieuWII a q x = 0 ↔ R true a q x = 0 := by
  have := R_real true a q x
  simp only [W, ↓reduceIte] at this
  rw [this, Complex.ofReal_eq_zero]

private lemma R_D_ne_zero (b : Bool) {a q x : ℝ} (h : R b a q x = 0) : D b a q x ≠ 0 := by
  intro h'
  have := wronskian b a q x
  rw [h, h'] at this
  cases b <;> norm_num [sgn] at this

end SpectralContinuity

/-- **Continuity of the zeros of `w_I(x; a_m(q), q)`** in `(0, π/2)`: with `n = ⌊m/2⌋`, they are
`n` continuous functions of real `q` (DLMF §28.9). -/
theorem exists_continuous_zeros_mathieuWI_mathieuA (m : ℕ) {n : ℕ} (hmn : m / 2 = n) :
    ∃ Z : Fin n → ℝ → ℝ, (∀ k, Continuous (Z k)) ∧ ∀ q : ℝ,
      {x : ℝ | x ∈ Ioo 0 (π / 2) ∧ mathieuWI (mathieuA m q) q x = 0} =
        range fun k => Z k q := by
  set Y : ℝ → ℝ → ℝ := fun q x => R false (mathieuA m q) q x
  have hcY : Continuous (Function.uncurry Y) := (continuous_R false).comp
    (((continuous_mathieuA m).comp continuous_fst).prodMk continuous_id)
  have hcY' : Continuous (Function.uncurry fun q x => D false (mathieuA m q) q x) :=
    (continuous_D false).comp (((continuous_mathieuA m).comp continuous_fst).prodMk continuous_id)
  have hset : ∀ q : ℝ, {x : ℝ | x ∈ Ioo 0 (π / 2) ∧ mathieuWI (mathieuA m q) q x = 0} =
      {x | x ∈ Ioo 0 (π / 2) ∧ Y q x = 0} := fun q => by
    ext x; simp only [mem_ofPred_eq, Y, mathieuWI_eq_zero_iff]
  simp_rw [hset]
  refine exists_continuous_zeros hcY hcY' (fun q x => hasDerivAt_R false _ q x)
    (fun q x h => R_D_ne_zero false h) (fun t₀ => exists_Ioc_ne_zero_of_ne hcY (by
      simp [Y, R_zero])) fun q => ?_
  rw [← hset, encard_zeros_mathieuWI_mathieuA, hmn]

/-- **Continuity of the zeros of `w_II(x; b_m(q), q)`** in `(0, π/2)`, `m ≥ 1`: with
`n = ⌊(m-1)/2⌋`, they are `n` continuous functions of real `q` (DLMF §28.9). -/
theorem exists_continuous_zeros_mathieuWII_mathieuB {m : ℕ} (hm : m ≠ 0) {n : ℕ}
    (hmn : (m - 1) / 2 = n) :
    ∃ Z : Fin n → ℝ → ℝ, (∀ k, Continuous (Z k)) ∧ ∀ q : ℝ,
      {x : ℝ | x ∈ Ioo 0 (π / 2) ∧ mathieuWII (mathieuB m q) q x = 0} =
        range fun k => Z k q := by
  set Y : ℝ → ℝ → ℝ := fun q x => R true (mathieuB m q) q x
  have hcY : Continuous (Function.uncurry Y) := (continuous_R true).comp
    (((continuous_mathieuB m).comp continuous_fst).prodMk continuous_id)
  have hcY' : Continuous (Function.uncurry fun q x => D true (mathieuB m q) q x) :=
    (continuous_D true).comp (((continuous_mathieuB m).comp continuous_fst).prodMk continuous_id)
  have hset : ∀ q : ℝ, {x : ℝ | x ∈ Ioo 0 (π / 2) ∧ mathieuWII (mathieuB m q) q x = 0} =
      {x | x ∈ Ioo 0 (π / 2) ∧ Y q x = 0} := fun q => by
    ext x; simp only [mem_ofPred_eq, Y, mathieuWII_eq_zero_iff]
  simp_rw [hset]
  refine exists_continuous_zeros hcY hcY' (fun q x => hasDerivAt_R true _ q x)
    (fun q x h => R_D_ne_zero true h) (fun t₀ => exists_Ioc_ne_zero_of_zero hcY hcY'
      (fun q x => hasDerivAt_R true _ q x) (fun q => by simp [Y, R_zero])
      (by simp [D_zero])) fun q => ?_
  rw [← hset, encard_zeros_mathieuWII_mathieuB hm, hmn]

end DLMF.Mathieu
