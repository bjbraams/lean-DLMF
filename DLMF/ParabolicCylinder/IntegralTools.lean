/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Relations
public import DLMF.Confluent.IntegralRepresentations
public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
public import DLMF.Confluent.TricomiLaplace
public import DLMF.Hypergeometric.Elementary

/-!
# Tools for the cylinder Laplace integrals (DLMF 12.5.2–12.5.3)

The integral `pcfInt_F c p w = ∫₀^∞ t^{c-1} e^{-t} (w+2t)^p dt` is holomorphic in `w` on the
slit plane (`pcfInt_differentiableOn`, by locally uniform domination). For real `x > 0` the
Laplace integral of Kummer's `U` (`kummerU_laplace`) rescales to it (`pcfInt_laplace_scale`),
giving DLMF 12.5.2–12.5.3 on the positive axis (`pcfInt_U_real_2`, `pcfInt_U_real_3`); the
identity theorem (`pcfInt_eq_of_real`) then extends them to the right half-plane.

For DLMF 12.12.1–12.12.2 the substitution `x = t²/2` (`pcfInt_sq_half_subst`) turns the
integrands into the Laplace kernel of `U(a/2+1/4, 1/2, x)` (`pcfInt_integrand_1`,
`pcfInt_integrand_2`), whose transform is DLMF 13.10.7 (`laplace_kummerU_gauss`); at `z = 2`
the resulting `₂F₁(-b,b;1/2;1/2)` is evaluated by DLMF 15.4.12 (`pcfInt_laplace_two`).

For DLMF 12.5.8 the Barnes integral of Kummer's `U` (DLMF 13.4.17, `kummerU_barnes`) and the
duplication formula give the real case (`pcfInt_B_real`); a uniform bound for the integrand
(`pcfInt_norm_B_le`) gives holomorphy on the sector `|arg z| < 3π/4` (`pcfInt_B_differentiableOn`)
and the identity theorem the general case (`pcfInt_B_integral`).
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Metric DLMF DLMF.Hypergeometric
open scoped Real Topology

namespace DLMF.Confluent

/-- The Laplace-type integral `∫₀^∞ t^{c-1} e^{-t} (w+2t)^p dt` behind DLMF 12.5.2–3. -/
noncomputable def pcfInt_F (c p w : ℂ) : ℂ :=
  ∫ t in Ioi (0:ℝ), (t:ℂ)^(c-1) * exp (-t) * (w + 2*t)^p

/-- Adding a nonnegative real multiple of `2` keeps a point in the slit plane. -/
lemma pcfInt_add_mem_slitPlane {w : ℂ} (hw : w ∈ slitPlane) {t : ℝ} (ht : 0 ≤ t) :
    w + 2*t ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hw ⊢
  simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, re_ofNat, im_ofNat]
  rcases hw with h | h
  · left; nlinarith
  · right; simpa using h

/-- The square of a point of the right half-plane lies in the slit plane. -/
lemma pcfInt_sq_mem_slitPlane {z : ℂ} (hz : 0 < z.re) : z^2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases h : z.im = 0
  · left; simp [sq, h]; nlinarith
  · right; simp only [sq, mul_im]
    have := mul_ne_zero hz.ne' h
    intro h'; apply this; linarith

/-- Near a point of the slit plane, `w + 2t` (`t ≥ 0`) stays uniformly away from `0`. -/
lemma pcfInt_norm_add_ge {w₀ : ℂ} (hw₀ : w₀ ∈ slitPlane) :
    ∃ ε > 0, ∀ w ∈ ball w₀ ε, ∀ t : ℝ, 0 ≤ t → ε ≤ ‖w + 2*t‖ := by
  obtain ⟨δ, hδ, hsub⟩ := isOpen_iff.mp isOpen_slitPlane w₀ hw₀
  refine ⟨δ/2, half_pos hδ, fun w hw t ht => ?_⟩
  by_contra hlt
  push Not at hlt
  have hm : ((-(2*t):ℝ):ℂ) ∈ ball w₀ δ := by
    rw [mem_ball, dist_eq] at hw ⊢
    calc ‖((-(2*t):ℝ):ℂ) - w₀‖ = ‖-(w + 2*t) + (w - w₀)‖ := by push_cast; ring_nf
      _ ≤ ‖w + 2*t‖ + ‖w - w₀‖ := by rw [← norm_neg (w + 2*t)]; exact norm_add_le _ _
      _ < δ := by linarith
  have := hsub hm
  rw [mem_slitPlane_iff] at this
  simp at this
  linarith

/-- An elementary bound `u^q ≤ K e^{t/2}` for `ε ≤ u ≤ R + 2t`. -/
lemma pcfInt_rpow_bound (q : ℝ) {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u t : ℝ, 0 ≤ t → ε ≤ u → u ≤ R + 2*t → u^q ≤ K * Real.exp (t/2) := by
  set m : ℝ := |q| + 1 with hm
  have hm0 : 0 < m := by positivity
  refine ⟨ε^q + (R+4*m)^q, by positivity, fun u t ht hεu huR => ?_⟩
  have he1 : 1 ≤ Real.exp (t/2) := Real.one_le_exp (by linarith)
  have hu0 : 0 < u := hε.trans_le hεu
  rcases le_total q 0 with hq | hq
  · have : u^q ≤ ε^q := Real.rpow_le_rpow_of_nonpos hε hεu hq
    have h2 : 0 ≤ (R+4*m)^q := by positivity
    nlinarith [Real.rpow_nonneg hε.le q]
  · have h1 : u^q ≤ ((R+4*m) * (1 + t/(2*m)))^q := by
      apply Real.rpow_le_rpow hu0.le _ hq
      have : R + 2*t ≤ (R+4*m) * (1 + t/(2*m)) := by
        rw [mul_add, mul_one, add_mul, mul_div_assoc', mul_div_assoc']
        have e : 4*m*t/(2*m) = 2*t := by field_simp; ring
        rw [e]; have : 0 ≤ R*t/(2*m) := by positivity
        linarith
      linarith
    rw [Real.mul_rpow (by positivity) (by positivity)] at h1
    have h2 : (1 + t/(2*m))^q ≤ Real.exp (t/2) := by
      calc (1 + t/(2*m))^q ≤ (Real.exp (t/(2*m)))^q :=
            Real.rpow_le_rpow (by positivity) (by linarith [Real.add_one_le_exp (t/(2*m))]) hq
        _ = Real.exp (t/(2*m) * q) := (Real.exp_mul _ _).symm
        _ ≤ Real.exp (t/2) := by
          apply Real.exp_le_exp.mpr
          have hqm : q ≤ m := by rw [hm]; linarith [le_abs_self q]
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
    have h3 : 0 ≤ (R+4*m)^q := by positivity
    calc u^q ≤ (R+4*m)^q * (1 + t/(2*m))^q := h1
      _ ≤ (R+4*m)^q * Real.exp (t/2) := mul_le_mul_of_nonneg_left h2 h3
      _ ≤ _ := by nlinarith [Real.rpow_nonneg hε.le q, Real.exp_pos (t/2)]

/-- `‖u^p‖ ≤ ‖u‖^{Re p} e^{π |Im p|}`. -/
lemma pcfInt_norm_cpow_le (u p : ℂ) : ‖u^p‖ ≤ ‖u‖^p.re * Real.exp (π * |p.im|) := by
  refine (norm_cpow_le u p).trans ?_
  rw [div_eq_mul_inv, ← Real.exp_neg]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have h1 := abs_arg_le_pi u
  have : |arg u * p.im| ≤ π * |p.im| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  linarith [neg_abs_le (arg u * p.im)]

/-- Local domination of the integrand of `pcfInt_F`. -/
lemma pcfInt_dom {c : ℂ} (p : ℂ) {w₀ : ℂ} (hw₀ : w₀ ∈ slitPlane) :
    ∃ ε > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ ball w₀ ε, ∀ t : ℝ, 0 < t →
      ‖(t:ℂ)^(c-1) * exp (-t) * (w + 2*t)^p‖ ≤ M * (t^(c.re-1) * Real.exp (-(1/2) * t^(1:ℝ))) := by
  obtain ⟨ε, hε, hε'⟩ := pcfInt_norm_add_ge hw₀
  obtain ⟨K, hK, hK'⟩ := pcfInt_rpow_bound p.re hε (R := ‖w₀‖ + ε) (by positivity)
  refine ⟨ε, hε, K * Real.exp (π * |p.im|), by positivity, fun w hw t ht => ?_⟩
  have hup : ‖w + 2*t‖ ≤ ‖w₀‖ + ε + 2*t := by
    have : ‖w‖ ≤ ‖w₀‖ + ε := by
      rw [mem_ball, dist_eq] at hw
      linarith [norm_le_norm_add_norm_sub' w w₀]
    calc ‖w + 2*t‖ ≤ ‖w‖ + ‖(2:ℂ)*t‖ := norm_add_le _ _
      _ = ‖w‖ + 2*t := by
        rw [show (2:ℂ)*t = ((2*t:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_of_nonneg (by linarith)]
      _ ≤ _ := by linarith
  have hb := hK' _ t ht.le (hε' w hw t ht.le) hup
  rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, show ((-(t:ℂ))) = ((-t:ℝ):ℂ) by push_cast; rfl,
    Complex.norm_exp_ofReal, Real.rpow_one]
  have hc := pcfInt_norm_cpow_le (w + 2*t) p
  have e : Real.exp (-t) = Real.exp (-(1/2)*t) * Real.exp (-(t/2)) := by
    rw [← Real.exp_add]; ring_nf
  have hx : ‖w + 2*t‖^p.re * Real.exp (-t) ≤ K * Real.exp (-(1/2)*t) := by
    rw [e]
    calc ‖w + 2*t‖^p.re * (Real.exp (-(1/2)*t) * Real.exp (-(t/2)))
        ≤ K * Real.exp (t/2) * (Real.exp (-(1/2)*t) * Real.exp (-(t/2))) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ = K * Real.exp (-(1/2)*t) * (Real.exp (t/2) * Real.exp (-(t/2))) := by ring
      _ = K * Real.exp (-(1/2)*t) := by rw [← Real.exp_add]; simp
  have h0 : 0 ≤ t^(c.re-1) := by positivity
  calc t^(c.re-1) * Real.exp (-t) * ‖(w + 2*t)^p‖
      ≤ t^(c.re-1) * Real.exp (-t) * (‖w + 2*t‖^p.re * Real.exp (π * |p.im|)) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = t^(c.re-1) * Real.exp (π * |p.im|) * (‖w + 2*t‖^p.re * Real.exp (-t)) := by ring
    _ ≤ t^(c.re-1) * Real.exp (π * |p.im|) * (K * Real.exp (-(1/2)*t)) :=
        mul_le_mul_of_nonneg_left hx (by positivity)
    _ = _ := by ring

/-- Continuity of the integrand of `pcfInt_F` on `(0,∞)`. -/
lemma pcfInt_continuousOn (c p : ℂ) {w : ℂ} (hw : w ∈ slitPlane) :
    ContinuousOn (fun t : ℝ => (t:ℂ)^(c-1) * exp (-t) * (w + 2*t)^p) (Ioi 0) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have ht' : (t:ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr ht
  have h1 : ContinuousAt (fun t : ℝ => (t:ℂ)^(c-1)) t :=
    (continuous_ofReal.continuousAt (x := t)).cpow continuousAt_const ht'
  have h3 : ContinuousAt (fun t : ℝ => (w + 2*(t:ℂ))^p) t :=
    (continuousAt_const.add (continuousAt_const.mul continuous_ofReal.continuousAt)).cpow continuousAt_const
      (pcfInt_add_mem_slitPlane hw (le_of_lt ht))
  exact (h1.mul (continuous_ofReal.continuousAt.neg.cexp)).mul h3

/-- Integrability of the majorant `M t^{Re c - 1} e^{-t/2}`. -/
lemma pcfInt_integrable_majorant {c : ℂ} (hc : 0 < c.re) (M : ℝ) :
    IntegrableOn (fun t : ℝ => M * (t^(c.re-1) * Real.exp (-(1/2) * t^(1:ℝ)))) (Ioi 0) :=
  (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos (by norm_num)).const_mul M

/-- The integrand of `pcfInt_F` is integrable for `w` in the slit plane. -/
lemma pcfInt_integrableOn {c : ℂ} (hc : 0 < c.re) (p : ℂ) {w : ℂ} (hw : w ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^(c-1) * exp (-t) * (w + 2*t)^p) (Ioi 0) := by
  obtain ⟨ε, hε, M, -, hM⟩ := pcfInt_dom (c := c) p hw
  refine (pcfInt_integrable_majorant hc M).mono' ((pcfInt_continuousOn c p hw).aestronglyMeasurable
    measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact hM w (mem_ball_self hε) t ht

/-- `pcfInt_F c p` is holomorphic on the slit plane. -/
lemma pcfInt_differentiableOn {c : ℂ} (hc : 0 < c.re) (p : ℂ) :
    DifferentiableOn ℂ (pcfInt_F c p) slitPlane := by
  unfold pcfInt_F
  refine differentiableOn_integral_Ioi_of_locally_dominated isOpen_slitPlane 0
    (fun w hw => (pcfInt_continuousOn c p hw).aestronglyMeasurable measurableSet_Ioi) ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.const_mul
    exact (differentiableAt_id.add_const _).cpow_const (pcfInt_add_mem_slitPlane hw (le_of_lt ht))
  · intro w hw
    obtain ⟨ε, hε, M, -, hM⟩ := pcfInt_dom (c := c) p hw
    refine ⟨ball w ε, ball_mem_nhds w hε, _, pcfInt_integrable_majorant hc M, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact fun y hy => hM y hy t ht

/-- Rescaling the Laplace integral of Kummer's `U` (real positive scale). -/
lemma pcfInt_laplace_scale (c p : ℂ) {b : ℝ} (hb : 0 < b) :
    ∫ s in Ioi (0:ℝ), exp (-(b:ℂ) * s) * (s:ℂ)^(c-1) * (1 + (s:ℂ))^p =
      (b:ℂ)^(-c) * ((2*b:ℝ):ℂ)^(-p) * pcfInt_F c p ((2*b:ℝ):ℂ) := by
  set g : ℝ → ℂ := fun t => (t:ℂ)^(c-1) * exp (-t) * (((2*b:ℝ):ℂ) + 2*t)^p with hg
  have h := integral_comp_mul_left_Ioi g 0 hb
  rw [mul_zero] at h
  set K : ℂ := (b:ℂ)^(c-1) * ((2*b:ℝ):ℂ)^p with hK
  have hpt : ∀ s ∈ Ioi (0:ℝ), g (b*s) = K * (exp (-(b:ℂ) * s) * (s:ℂ)^(c-1) * (1 + (s:ℂ))^p) := by
    intro s hs
    have hs0 : (0:ℝ) ≤ s := le_of_lt hs
    simp only [hg, hK]
    rw [ofReal_mul, mul_cpow_ofReal_nonneg hb.le hs0,
      show ((2*b:ℝ):ℂ) + 2*((b:ℂ)*s) = ((2*b:ℝ):ℂ) * ((1+s:ℝ):ℂ) by push_cast; ring,
      mul_cpow_ofReal_nonneg (by linarith) (by linarith)]
    push_cast; ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul] at h
  have hb0 : (b:ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have h2b : ((2*b:ℝ):ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have hK0 : K ≠ 0 := mul_ne_zero (by rw [Ne, cpow_eq_zero_iff]; tauto)
    (by rw [Ne, cpow_eq_zero_iff]; tauto)
  have hF : pcfInt_F c p ((2*b:ℝ):ℂ) = ∫ t in Ioi (0:ℝ), g t := rfl
  rw [hF, real_smul, ofReal_inv] at *
  rw [eq_inv_mul_iff_mul_eq₀ hb0] at h
  have hbc : (b:ℂ)^c ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; tauto
  have hbp : ((2*b:ℝ):ℂ)^p ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; tauto
  rw [← h, hK, cpow_neg, cpow_neg, cpow_sub _ _ hb0, cpow_one]
  field_simp

/-- Power bookkeeping for positive reals: `(x²/2)^{-e} (x²)^{-d} = 2^e (x²)^{-e-d}`. -/
lemma pcfInt_const_aux {x : ℝ} (hx : 0 < x) (e d : ℂ) :
    ((x^2/2:ℝ):ℂ)^(-e) * ((x^2:ℝ):ℂ)^(-d) = (2:ℂ)^e * ((x^2:ℝ):ℂ)^(-e-d) := by
  have hx2 : ((x^2:ℝ):ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  rw [show ((x^2/2:ℝ):ℂ) = ((x^2:ℝ):ℂ) * ((1/2:ℝ):ℂ) by push_cast; ring,
    mul_cpow_ofReal_nonneg (by positivity) (by norm_num),
    show ((1/2:ℝ):ℂ) = (2:ℂ)⁻¹ by push_cast; ring, inv_cpow _ _ (by rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_cast, arg_ofReal_of_nonneg (by norm_num)]; exact Real.pi_ne_zero.symm),
    ← cpow_neg, neg_neg, sub_eq_add_neg, cpow_add _ _ hx2]
  ring

/-- `(x²)^{1/2} = x` for `x > 0`. -/
lemma pcfInt_sq_cpow_half {x : ℝ} (hx : 0 < x) : ((x^2:ℝ):ℂ)^(1/2:ℂ) = x := by
  rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
    ← Real.sqrt_eq_rpow, Real.sqrt_sq hx.le]

/-- `(x²)^{-1/2} = x⁻¹` for `x > 0`. -/
lemma pcfInt_sq_cpow_neg_half {x : ℝ} (hx : 0 < x) : ((x^2:ℝ):ℂ)^(-1/2:ℂ) = (x:ℂ)⁻¹ := by
  rw [show (-1/2:ℂ) = -(1/2) by ring, cpow_neg, pcfInt_sq_cpow_half hx]

/-- DLMF 12.5.2 for real positive argument. -/
lemma pcfInt_U_real_2 {a : ℂ} (ha : -1/2 < a.re) {x : ℝ} (hx : 0 < x) :
    pcfU a x = x * exp (-(x:ℂ)^2/4) / Gamma (a/2+1/4) * pcfInt_F (a/2+1/4) (-a/2-3/4) (x^2) := by
  have hα : 0 < (a/2+1/4).re := by simp; linarith
  have hre : 0 < (x:ℂ).re := by simpa using hx
  have hb : (0:ℝ) < x^2/2 := by positivity
  have hw : (0:ℝ) < ((x:ℂ)^2/2).re := by
    rw [show (x:ℂ)^2/2 = ((x^2/2:ℝ):ℂ) by push_cast; ring, ofReal_re]; exact hb
  rw [pcfU_eq_kummerU a hre, kummerU_laplace hα hw,
    show (x:ℂ)^2/2 = ((x^2/2:ℝ):ℂ) by push_cast; ring,
    show (1/2:ℂ) - (a/2+1/4) - 1 = -a/2-3/4 by ring, pcfInt_laplace_scale _ _ hb,
    show 2*(x^2/2) = x^2 by ring]
  have key := pcfInt_const_aux hx (a/2+1/4) (-a/2-3/4)
  rw [show -(a/2+1/4) - (-a/2-3/4) = 1/2 by ring, pcfInt_sq_cpow_half hx] at key
  have h2 : (2:ℂ)^(-(1/4:ℂ)-a/2) * (2:ℂ)^(a/2+1/4) = 1 := by
    rw [← cpow_add _ _ two_ne_zero, show -(1/4:ℂ)-a/2 + (a/2+1/4) = 0 by ring, cpow_zero]
  push_cast at key ⊢
  linear_combination (exp (-(x:ℂ)^2/4) * (1 / Gamma (a/2+1/4)) * pcfInt_F (a/2+1/4) (-a/2-3/4) ((x:ℂ)^2)) *
    ((2:ℂ)^(-(1/4:ℂ)-a/2) * key + x * h2)

/-- DLMF 12.5.3 for real positive argument. -/
lemma pcfInt_U_real_3 {a : ℂ} (ha : -3/2 < a.re) {x : ℝ} (hx : 0 < x) :
    pcfU a x = exp (-(x:ℂ)^2/4) / Gamma (a/2+3/4) * pcfInt_F (a/2+3/4) (-a/2-1/4) (x^2) := by
  have hα : 0 < (a/2+3/4).re := by simp; linarith
  have hre : 0 < (x:ℂ).re := by simpa using hx
  have hb : (0:ℝ) < x^2/2 := by positivity
  have hw : (0:ℝ) < ((x:ℂ)^2/2).re := by
    rw [show (x:ℂ)^2/2 = ((x^2/2:ℝ):ℂ) by push_cast; ring, ofReal_re]; exact hb
  rw [pcfU_kummerU_odd a hre, kummerU_laplace hα hw,
    show (x:ℂ)^2/2 = ((x^2/2:ℝ):ℂ) by push_cast; ring,
    show (3/2:ℂ) - (a/2+3/4) - 1 = -a/2-1/4 by ring, pcfInt_laplace_scale _ _ hb,
    show 2*(x^2/2) = x^2 by ring]
  have key := pcfInt_const_aux hx (a/2+3/4) (-a/2-1/4)
  rw [show -(a/2+3/4) - (-a/2-1/4) = -1/2 by ring, pcfInt_sq_cpow_neg_half hx] at key
  have h2 : (2:ℂ)^(-3/4-a/2) * (2:ℂ)^(a/2+3/4) = 1 := by
    rw [← cpow_add _ _ two_ne_zero, show (-3/4:ℂ)-a/2 + (a/2+3/4) = 0 by ring, cpow_zero]
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  push_cast at key ⊢
  have hk : (x:ℂ) * ((x:ℂ)⁻¹) = 1 := mul_inv_cancel₀ hx0
  linear_combination (exp (-(x:ℂ)^2/4) * (1 / Gamma (a/2+3/4)) * pcfInt_F (a/2+3/4) (-a/2-1/4) ((x:ℂ)^2)) *
    ((2:ℂ)^(-3/4-a/2) * x * key + (2:ℂ)^(-3/4-a/2) * (2:ℂ)^(a/2+3/4) * hk + h2)

/-- Identity theorem on the right half-plane from agreement on the positive reals. -/
lemma pcfInt_eq_of_real {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f {z | 0 < z.re})
    (hg : DifferentiableOn ℂ g {z | 0 < z.re}) (h : ∀ x : ℝ, 0 < x → f x = g x)
    {z : ℂ} (hz : 0 < z.re) : f z = g z := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), f w = g w := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have := (continuous_ofReal.tendsto (1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℝ)))
        rwa [ofReal_one] at this
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa using hr
    apply ht.frequently
    apply Eventually.frequently
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with r hr
    exact h r hr
  exact (hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hU)
    (convex_halfSpace_re_gt 0).isPreconnected (by simp) hfreq hz

/-- `z ↦ pcfInt_F c p (z²)` is holomorphic on the right half-plane. -/
lemma pcfInt_differentiableOn_comp {c : ℂ} (hc : 0 < c.re) (p : ℂ) :
    DifferentiableOn ℂ (fun z : ℂ => pcfInt_F c p (z^2)) {z | 0 < z.re} :=
  (pcfInt_differentiableOn hc p).comp (differentiableOn_id.pow 2)
    (fun _ hz => pcfInt_sq_mem_slitPlane hz)


/-- `𝐅(a,b;c;0) = 1/Γ(c)` for every `c` (both sides vanish at the poles of `Γ`). -/
lemma pcfInt_regularizedGaussHG_zero (a b c : ℂ) : regularizedGaussHG a b c 0 = (Gamma c)⁻¹ := by
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by simp), regularizedGaussHGFun_eq_tsum,
    tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  simp

/-- The substitution `x = t²/2` on the half-line. -/
lemma pcfInt_sq_half_subst {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0)) :
    IntegrableOn (fun t : ℝ => (t:ℂ) * g (t^2/2)) (Ioi 0) ∧
      ∫ t in Ioi (0:ℝ), (t:ℂ) * g (t^2/2) = ∫ x in Ioi (0:ℝ), g x := by
  set h : ℝ → ℂ := fun y => (1/2:ℂ) * g ((1/2) * y) with hh
  have hhi : IntegrableOn h (Ioi 0) :=
    ((integrableOn_Ioi_comp_mul_left_iff g 0 (by norm_num : (0:ℝ) < 1/2)).mpr
      (by simpa using hg)).const_mul _
  have heq : EqOn (fun t : ℝ => (|(2:ℝ)| * t ^ ((2:ℝ) - 1)) • h (t ^ (2:ℝ)))
      (fun t : ℝ => (t:ℂ) * g (t^2/2)) (Ioi 0) := by
    intro t ht
    simp only [hh, real_smul]
    rw [show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
      show (1/2:ℝ) * t^2 = t^2/2 by ring]
    push_cast; rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]; push_cast; ring
  refine ⟨((integrableOn_Ioi_comp_rpow_iff h two_ne_zero).mpr hhi).congr_fun heq measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi heq, integral_comp_rpow_Ioi h two_ne_zero, hh,
    integral_const_mul, integral_comp_mul_left_Ioi g 0 (by norm_num : (0:ℝ) < 1/2), mul_zero,
    real_smul]
  push_cast; ring

/-- `(t²)^s = t^{2s}` for `t > 0`. -/
lemma pcfInt_sq_cpow {t : ℝ} (ht : 0 < t) (s : ℂ) : ((t^2:ℝ):ℂ)^s = (t:ℂ)^(2*s) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (by positivity)),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht.ne'), ← ofReal_log (by positivity), Real.log_pow,
    ← ofReal_log ht.le]
  push_cast; ring_nf

/-- The integrand of DLMF 12.12.1 in terms of the Laplace kernel of Kummer's `U`. -/
lemma pcfInt_integrand_1 (μ a : ℂ) {t : ℝ} (ht : 0 < t) :
    exp (-t^2/4) * (t:ℂ)^(μ-1) * pcfU a t =
      (2:ℂ)^(-(1/4)-a/2) * (2:ℂ)^(μ/2-1) *
        ((t:ℂ) * tricomiLaplaceKernel (a/2+1/4) (μ/2) (1/2) 1 (t^2/2)) := by
  have hre : 0 < (t:ℂ).re := by simpa using ht
  have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  rw [pcfU_eq_kummerU a hre, tricomiLaplaceKernel, show (t:ℂ)^2/2 = ((t^2/2:ℝ):ℂ) by push_cast; ring]
  have key := pcfInt_const_aux ht (1-μ/2) 0
  rw [neg_zero, cpow_zero, mul_one, sub_zero, neg_sub, pcfInt_sq_cpow ht] at key
  rw [key]
  have e1 : (t:ℂ)^(μ-1) = (t:ℂ) * (t:ℂ)^(2*(μ/2-1)) := by
    rw [show μ - 1 = 1 + 2*(μ/2-1) by ring, cpow_add _ _ ht0, cpow_one]
  have e2 : exp (-(t:ℂ)^2/4) * exp (-(t:ℂ)^2/4) = exp (-1 * ((t^2/2:ℝ):ℂ)) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  have e3 : (2:ℂ)^(μ/2-1) * (2:ℂ)^(1-μ/2) = 1 := by
    rw [← cpow_add _ _ two_ne_zero, show μ/2-1 + (1-μ/2) = 0 by ring, cpow_zero]
  rw [e1, ← e2]
  linear_combination -(exp (-(t:ℂ)^2/4) * exp (-(t:ℂ)^2/4) * (2:ℂ)^(-(1/4)-a/2) * (t:ℂ) *
    (t:ℂ)^(2*(μ/2-1)) * kummerU (a/2+1/4) (1/2) ((t^2/2:ℝ):ℂ)) * e3

/-- The integrand of DLMF 12.12.2 in terms of the Laplace kernel of Kummer's `U` at `z = 2`. -/
lemma pcfInt_integrand_2 (μ a : ℂ) {t : ℝ} (ht : 0 < t) :
    exp (-3*t^2/4) * (t:ℂ)^(μ-1) * pcfU a t =
      (2:ℂ)^(-(1/4)-a/2) * (2:ℂ)^(μ/2-1) *
        ((t:ℂ) * tricomiLaplaceKernel (a/2+1/4) (μ/2) (1/2) 2 (t^2/2)) := by
  have hre : 0 < (t:ℂ).re := by simpa using ht
  have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  rw [pcfU_eq_kummerU a hre, tricomiLaplaceKernel, show (t:ℂ)^2/2 = ((t^2/2:ℝ):ℂ) by push_cast; ring]
  have key := pcfInt_const_aux ht (1-μ/2) 0
  rw [neg_zero, cpow_zero, mul_one, sub_zero, neg_sub, pcfInt_sq_cpow ht] at key
  rw [key]
  have e1 : (t:ℂ)^(μ-1) = (t:ℂ) * (t:ℂ)^(2*(μ/2-1)) := by
    rw [show μ - 1 = 1 + 2*(μ/2-1) by ring, cpow_add _ _ ht0, cpow_one]
  have e2 : exp (-3*(t:ℂ)^2/4) * exp (-(t:ℂ)^2/4) = exp (-2 * ((t^2/2:ℝ):ℂ)) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  have e3 : (2:ℂ)^(μ/2-1) * (2:ℂ)^(1-μ/2) = 1 := by
    rw [← cpow_add _ _ two_ne_zero, show μ/2-1 + (1-μ/2) = 0 by ring, cpow_zero]
  rw [e1, ← e2]
  linear_combination -(exp (-3*(t:ℂ)^2/4) * exp (-(t:ℂ)^2/4) * (2:ℂ)^(-(1/4)-a/2) * (t:ℂ) *
    (t:ℂ)^(2*(μ/2-1)) * kummerU (a/2+1/4) (1/2) ((t^2/2:ℝ):ℂ)) * e3

/-- The value of the `U` Laplace integral at `z = 2`, `c = 1/2`, `a = -b` (via DLMF 13.10.7
and DLMF 15.4.12). The 13.10.7 step repeats the proof of `laplace_kummerU`
(`DLMF/Confluent/Integrals.lean`). -/
lemma pcfInt_laplace_two {b : ℂ} (hb : 0 < b.re) :
    ∫ t in Ioi (0:ℝ), tricomiLaplaceKernel (-b) b (1/2) 2 t =
      Gamma b * Gamma (b + 1/2) * (2:ℂ)^(-b) * cos (b*π/2) / Real.sqrt π := by
  have hm := (laplace_kummerU_gauss (a := -b) (b := b) (c := 1/2) (z := 2) hb
    (by simp; linarith) (by simp)).2
  rw [hm]
  have hz0 : (2:ℂ) ≠ 0 := two_ne_zero
  have hw : 1 - (2:ℂ) ∈ DLMF.Hypergeometric.cutPlane := by
    change 1 - (1 - (2:ℂ)) ∈ slitPlane
    rw [sub_sub_cancel]; exact Or.inl (by simp)
  have hp := DLMF.Hypergeometric.regularizedGaussHG_pfaff b (b - 1/2 + 1) (-b + b - 1/2 + 1) hw
  have hs := DLMF.Hypergeometric.regularizedGaussHG_symm b (-b) (-b + b - 1/2 + 1)
    (DLMF.Hypergeometric.div_sub_one_mem_cutPlane hw)
  rw [show (1 - (2:ℂ)) / (1 - 2 - 1) = 1/2 by norm_num] at hp hs
  rw [sub_sub_cancel, show (-b + b - 1/2 + 1) - (b - 1/2 + 1) = -b by ring] at hp
  rw [hp, hs, show -b + b - 1/2 + 1 = (1/2:ℂ) by ring,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by norm_num),
    regularizedGaussHGFun_eq_div_Gamma (fun k h => by
      have := congrArg re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])]
  have hsin : ((Real.sin (π/4) : ℂ))^2 = 1/2 := by
    rw [Real.sin_pi_div_four]; push_cast
    rw [div_pow, ← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hF := DLMF.Hypergeometric.sin_sq_cos b (x := π/4) (by
    rw [abs_of_pos (by positivity)]; linarith [Real.pi_pos])
  rw [hsin] at hF
  have hg : Gamma (1/2:ℂ) = (Real.sqrt π : ℂ) := by
    rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]; norm_num
  rw [hF, show b - 1/2 + 1 = b + 1/2 by ring, hg, show 2 * b * ((π/4:ℝ):ℂ) = b * π/2 by push_cast; ring]
  ring


/-- An integrable function has its Lebesgue integral as whole-line improper integral. -/
lemma pcfInt_hasIntegralWholeLine {f : ℝ → ℂ} (hf : Integrable f) :
    HasIntegralWholeLine f (∫ y, f y) :=
  ⟨_, _, intervalIntegral_tendsto_integral_Iic 0 hf.integrableOn tendsto_id,
    intervalIntegral_tendsto_integral_Ioi 0 hf.integrableOn tendsto_id,
    intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn⟩


/-- The Barnes integrand `Γ(t) Γ(1/2+a-2t) 2^t z^{2t}`, `t = c+iy`, of DLMF 12.5.8. -/
noncomputable def pcfInt_B (a z : ℂ) (c y : ℝ) : ℂ :=
  Gamma (c+y*I)*Gamma (1/2+1*a-2*(c+y*I))*2^((c:ℂ)+y*I)*z^(2*((c:ℂ)+y*I))*1

/-- `‖z^{2t}‖ ≤ ‖z‖^{2c} e^{2|arg z||y|}` for `t = c+iy`. -/
lemma pcfInt_norm_cpow_two_mul_le {z : ℂ} (hz : z ≠ 0) (c y : ℝ) :
    ‖z^(2*((c:ℂ)+y*I))‖ ≤ ‖z‖^(2*c) * Real.exp (2*|arg z| *|y|) := by
  rw [norm_cpow_of_ne_zero hz]
  have hre : (2*((c:ℂ)+y*I)).re = 2*c := by simp
  have him : (2*((c:ℂ)+y*I)).im = 2*y := by simp
  rw [hre, him, div_eq_mul_inv, ← Real.exp_neg]
  gcongr
  have h1 : -(arg z * (2*y)) ≤ |arg z * (2*y)| := neg_le_abs _
  rw [abs_mul, abs_mul, abs_two] at h1
  linarith

/-- The uniform bound `C ‖z‖^{2c} (1+|y|)^K e^{-(3π/2 - 2|arg z|)|y|}` for the 12.5.8 integrand. -/
lemma pcfInt_norm_B_le (a : ℂ) {c : ℝ} (hc : 0 < c) (hca : 2*c < 1/2 + a.re) :
    ∃ C : ℝ, ∃ K : ℕ, 0 ≤ C ∧ ∀ z : ℂ, z ≠ 0 → ∀ y : ℝ,
      ‖pcfInt_B a z c y‖ ≤ C * ‖z‖^(2*c) * ((1+|y|)^K * Real.exp (-((3*π/2 - 2*|arg z|)*|y|))) := by
  have hx0 : 0 < 1/2 + a.re - 2*c := by linarith
  obtain ⟨C1, K1, h1⟩ := DLMF.Gamma.exists_norm_Gamma_le hc
  obtain ⟨C2, K2, h2⟩ := DLMF.Gamma.exists_norm_Gamma_le hx0
  have hC1 : 0 ≤ C1 := (norm_nonneg _).trans (by simpa using h1 0)
  have hC2 : 0 ≤ C2 := (norm_nonneg _).trans (by simpa using h2 0)
  set D : ℝ := (2*(1+|a.im|))^K2 * Real.exp (π*|a.im|/2)
  refine ⟨C1 * C2 * D * (2:ℝ)^c, K1+K2, by positivity, fun z hz y => ?_⟩
  have e1 : (c:ℂ)+y*I = c + I*y := by ring
  have e2 : 1/2+1*a-2*((c:ℂ)+y*I) = ((1/2 + a.re - 2*c : ℝ) : ℂ) + I*((a.im - 2*y : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have g1 := h1 y; rw [← e1] at g1
  have g2 := h2 (a.im - 2*y); rw [← e2] at g2
  have hp : (1 + |a.im - 2*y|)^K2 ≤ (2*(1+|a.im|))^K2 * (1+|y|)^K2 := by
    rw [← mul_pow]; gcongr
    have := abs_sub (a.im) (2*y); rw [abs_mul, abs_two] at this
    nlinarith [abs_nonneg a.im, abs_nonneg y]
  have he : Real.exp (-(π * |a.im - 2*y|) / 2) ≤ Real.exp (π*|a.im|/2) * Real.exp (-(π*|y|)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    have := abs_sub_abs_le_abs_sub (2*y) (a.im)
    rw [abs_mul, abs_two, abs_sub_comm] at this
    nlinarith [Real.pi_pos]
  have h2t : ‖(2:ℂ)^((c:ℂ)+y*I)‖ = (2:ℝ)^c := by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_cast, norm_cpow_eq_rpow_re_of_pos (by norm_num)]; simp
  have hz2 := pcfInt_norm_cpow_two_mul_le hz c y
  unfold pcfInt_B
  rw [mul_one, norm_mul, norm_mul, norm_mul, h2t]
  calc ‖Gamma (c+y*I)‖ * ‖Gamma (1/2+1*a-2*((c:ℂ)+y*I))‖ * (2:ℝ)^c * ‖z^(2*((c:ℂ)+y*I))‖
      ≤ (C1 * (1 + |y|)^K1 * Real.exp (-(π*|y|)/2)) *
          (C2 * ((2*(1+|a.im|))^K2 * (1+|y|)^K2) * (Real.exp (π*|a.im|/2) * Real.exp (-(π*|y|)))) *
          (2:ℝ)^c * (‖z‖^(2*c) * Real.exp (2*|arg z| *|y|)) := by
        gcongr
        exact g2.trans (by gcongr)
    _ = C1 * C2 * D * (2:ℝ)^c * ‖z‖^(2*c) * ((1+|y|)^(K1+K2) *
          (Real.exp (-(π*|y|)/2) * Real.exp (-(π*|y|)) * Real.exp (2*|arg z| *|y|))) := by
        simp only [D]; ring
    _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf

/-- Pointwise form of the 12.5.8 integrand from Kummer's Barnes integrand (duplication formula). -/
lemma pcfInt_B_real_pt (a : ℂ) {x : ℝ} (hx : 0 < x) (c y : ℝ) :
    Gamma (a/2+1/4 - ((c:ℂ)+y*I)) * Gamma (a/2+1/4+1/2 - ((c:ℂ)+y*I)) * Gamma ((c:ℂ)+y*I) *
      ((x^2/2:ℝ):ℂ)^((c:ℂ)+y*I) =
    (Real.sqrt π : ℂ) * (2:ℂ)^(1/2-a) * pcfInt_B a x c y := by
  set t : ℂ := (c:ℂ)+y*I
  have hd := Complex.Gamma_mul_Gamma_add_half (a/2+1/4 - t)
  rw [show a/2+1/4 - t + 1/2 = a/2+1/4+1/2 - t by ring,
    show 2*(a/2+1/4 - t) = 1/2+1*a-2*t by ring] at hd
  rw [hd]
  have hX : ((x^2/2:ℝ):ℂ)^t = (x:ℂ)^(2*t) * (2:ℂ)^(-t) := by
    rw [show ((x^2/2:ℝ):ℂ) = ((x^2:ℝ):ℂ) * ((1/2:ℝ):ℂ) by push_cast; ring,
      mul_cpow_ofReal_nonneg (by positivity) (by norm_num), pcfInt_sq_cpow hx,
      show ((1/2:ℝ):ℂ) = (2:ℂ)⁻¹ by push_cast; ring,
      inv_cpow _ _ (by rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_cast, arg_ofReal_of_nonneg (by norm_num)]; exact Real.pi_ne_zero.symm), cpow_neg]
  have h2 : (2:ℂ)^(1 - (1/2+1*a-2*t)) * (2:ℂ)^(-t) = (2:ℂ)^(1/2-a) * (2:ℂ)^t := by
    rw [← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero]; ring_nf
  rw [hX]
  unfold pcfInt_B
  linear_combination (Gamma (1/2+1*a-2*t) * Real.sqrt π * Gamma t * (x:ℂ)^(2*t)) * h2

/-- DLMF 12.5.8 for real positive argument, from Kummer's Barnes integral (DLMF 13.4.17). -/
lemma pcfInt_B_real (a : ℂ) {c : ℝ} (hc : 0 < c) (hca : 2*c < 1/2 + a.re) {x : ℝ} (hx : 0 < x) :
    ∫ y, pcfInt_B a x c y = 2*π*Gamma (1/2+1*a)*(exp ((x:ℂ)^2/4)*(x:ℂ)^(a+1/2))*pcfU a x := by
  set α : ℂ := a/2+1/4 with hα
  have hX : (0:ℝ) < x^2/2 := by positivity
  have hb := kummerU_barnes (a := α) (b := 1/2) (σ := -c) hX (by simp [hα]; linarith)
    (by simp [hα]; linarith) (by linarith)
  set Kc : ℂ := (Real.sqrt π : ℂ) * (2:ℂ)^(1/2-a) * I / (Gamma α * Gamma (1 + α - 1/2))
  have hpt : ∀ y : ℝ, Gamma (α + ((-c:ℝ):ℂ) + I * ((-y:ℝ):ℂ)) *
      Gamma (1 + α - 1/2 + ((-c:ℝ):ℂ) + I * ((-y:ℝ):ℂ)) *
      Gamma (-(((-c:ℝ):ℂ) + I * ((-y:ℝ):ℂ))) / (Gamma α * Gamma (1 + α - 1/2)) *
      ((x^2/2:ℝ):ℂ) ^ (-(((-c:ℝ):ℂ) + I * ((-y:ℝ):ℂ))) * I = Kc * pcfInt_B a x c y := by
    intro y
    have e1 : α + ((-c:ℝ):ℂ) + I * ((-y:ℝ):ℂ) = a/2+1/4 - ((c:ℂ)+y*I) := by
      rw [hα]; push_cast; ring
    have e2 : 1 + α - 1/2 + ((-c:ℝ):ℂ) + I * ((-y:ℝ):ℂ) = a/2+1/4+1/2 - ((c:ℂ)+y*I) := by
      rw [hα]; push_cast; ring
    have e3 : -(((-c:ℝ):ℂ) + I * ((-y:ℝ):ℂ)) = (c:ℂ)+y*I := by push_cast; ring
    rw [e1, e2, e3]
    have := pcfInt_B_real_pt a hx c y
    simp only [Kc]
    linear_combination (I / (Gamma α * Gamma (1 + α - 1/2))) * this
  rw [← integral_neg_eq_self] at hb
  simp only [hpt] at hb
  rw [integral_const_mul] at hb
  have hre : 0 < (x:ℂ).re := by simpa using hx
  have hd := Complex.Gamma_mul_Gamma_add_half α
  rw [show 2*α = 1/2+1*a by rw [hα]; ring, show 1 - (1/2+1*a) = 1/2 - a by ring] at hd
  have hXa := pcfInt_const_aux hx α 0
  rw [neg_zero, cpow_zero, mul_one, sub_zero, pcfInt_sq_cpow hx] at hXa
  have hG : Gamma (1/2+1*a) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hW : (2:ℂ)^(1/2-a) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; simp
  have hs : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1 : (2:ℂ)^(-(1/4)-a/2) = ((2:ℂ)^α)⁻¹ := by
    rw [← cpow_neg, hα]; congr 1; ring
  have h2 : (x:ℂ)^(2*(-α)) = ((x:ℂ)^(a+1/2))⁻¹ := by
    rw [← cpow_neg, hα]; congr 1; ring
  have h3 : exp (-(x:ℂ)^2/4) = (exp ((x:ℂ)^2/4))⁻¹ := by rw [← Complex.exp_neg]; congr 1; ring
  have hQ : (2:ℂ)^α ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; simp
  have hR : (x:ℂ)^(a+1/2) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; simp [hx.ne']
  rw [pcfU_eq_kummerU a hre, show (x:ℂ)^2/2 = ((x^2/2:ℝ):ℂ) by push_cast; ring, hb, hXa,
    show 1 + α - 1/2 = α + 1/2 by ring] at *
  simp only [Kc]
  rw [show 1 + α - 1/2 = α + 1/2 by ring, hd, h1, h2, h3]
  generalize Gamma (1/2+1*a) = G at hG ⊢
  generalize (x:ℂ)^(a+1/2) = R at hR ⊢
  field_simp

/-- The sector `|arg z| < 3π/4` (origin excluded) of DLMF 12.5.8. -/
noncomputable def pcfInt_sector : Set ℂ := slitPlane ∩ (fun z : ℂ => |arg z|) ⁻¹' Iio (3*π/4)

/-- The sector is open. -/
lemma pcfInt_isOpen_sector : IsOpen pcfInt_sector :=
  ContinuousOn.isOpen_inter_preimage (fun _ hz => (continuousAt_arg hz).abs.continuousWithinAt)
    isOpen_slitPlane isOpen_Iio

/-- Membership in the sector. -/
lemma pcfInt_mem_sector {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 3*π/4) : z ∈ pcfInt_sector := by
  refine ⟨mem_slitPlane_iff_arg.mpr ⟨fun h => ?_, hz0⟩, hz⟩
  rw [h, abs_of_pos Real.pi_pos] at hz; linarith [Real.pi_pos]

/-- The sector is preconnected (the image of a strip under `exp`). -/
lemma pcfInt_isPreconnected_sector : IsPreconnected pcfInt_sector := by
  have hS : IsPreconnected (im ⁻¹' Ioo (-(3*π/4)) (3*π/4)) :=
    ((convex_Ioo _ _).linear_preimage imLm).isPreconnected
  have himg : exp '' (im ⁻¹' Ioo (-(3*π/4)) (3*π/4)) = pcfInt_sector := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : -(3*π/4) < w.im ∧ w.im < 3*π/4 := hw
      have hlog : log (exp w) = w := log_exp (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      have harg : arg (exp w) = w.im := by rw [← log_im, hlog]
      exact pcfInt_mem_sector (exp_ne_zero w) (by rw [harg, abs_lt]; exact hw')
    · rintro ⟨hz, hz'⟩
      have hz0 : z ≠ 0 := slitPlane_ne_zero hz
      refine ⟨log z, ?_, exp_log hz0⟩
      have : |arg z| < 3*π/4 := hz'
      rw [mem_preimage, log_im, mem_Ioo]; exact abs_lt.mp this
  rw [← himg]
  exact hS.image _ continuous_exp.continuousOn

/-- The 12.5.8 integrand is continuous in `y`. -/
lemma pcfInt_B_continuous (a : ℂ) {z : ℂ} (hz : z ≠ 0) {c : ℝ} (hc : 0 < c)
    (hca : 2*c < 1/2 + a.re) : Continuous (pcfInt_B a z c) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  unfold pcfInt_B
  refine ContinuousAt.mul (ContinuousAt.mul (ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_) ?_)
    continuousAt_const
  · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp [hc])).comp (by fun_prop)
  · exact (DLMF.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
  · exact (Continuous.const_cpow (f := fun y : ℝ => (c:ℂ)+y*I) (by fun_prop)
      (Or.inl two_ne_zero)).continuousAt
  · exact (Continuous.const_cpow (f := fun y : ℝ => 2*((c:ℂ)+y*I)) (by fun_prop)
      (Or.inl hz)).continuousAt

/-- The 12.5.8 integrand is integrable for `|arg z| < 3π/4`. -/
lemma pcfInt_B_integrable (a : ℂ) {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 3*π/4) {c : ℝ}
    (hc : 0 < c) (hca : 2*c < 1/2 + a.re) : Integrable (pcfInt_B a z c) := by
  obtain ⟨C, K, -, hCK⟩ := pcfInt_norm_B_le a hc hca
  exact ((DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg (c := 3*π/2 - 2*|arg z|)
    (by linarith) K).const_mul (C * ‖z‖^(2*c))).mono'
    (pcfInt_B_continuous a hz0 hc hca).aestronglyMeasurable
    (Eventually.of_forall fun y => (hCK z hz0 y).trans (le_of_eq (by ring)))

/-- The 12.5.8 integral is holomorphic in `z` on the sector. -/
lemma pcfInt_B_differentiableOn (a : ℂ) {c : ℝ} (hc : 0 < c) (hca : 2*c < 1/2 + a.re) :
    DifferentiableOn ℂ (fun z => ∫ y, pcfInt_B a z c y) pcfInt_sector := by
  obtain ⟨C, K, hC0, hCK⟩ := pcfInt_norm_B_le a hc hca
  refine Complex.differentiableOn_integral_of_locally_dominated pcfInt_isOpen_sector
    (fun z hz => (pcfInt_B_continuous a (slitPlane_ne_zero hz.1) hc hca).aestronglyMeasurable)
    ?_ ?_
  · refine Eventually.of_forall fun y z hz => ?_
    unfold pcfInt_B
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (((differentiableAt_const _).mul (differentiableAt_id.cpow_const hz.1)).mul
      (differentiableAt_const _))
  · intro z0 hz0
    have hθ0 : |arg z0| < 3*π/4 := hz0.2
    set θ : ℝ := (|arg z0| + 3*π/4)/2
    set R : ℝ := ‖z0‖ + 1
    have harg : ∀ᶠ z in 𝓝 z0, |arg z| < θ :=
      ((continuousAt_arg hz0.1).abs).eventually_lt continuousAt_const (by simp only [θ]; linarith)
    have hnorm : ∀ᶠ z in 𝓝 z0, ‖z‖ < R :=
      continuous_norm.continuousAt.eventually_lt continuousAt_const (by simp only [R]; linarith)
    refine ⟨_, (harg.and hnorm).and (pcfInt_isOpen_sector.mem_nhds hz0),
      fun y => C * R^(2*c) * ((1+|y|)^K * Real.exp (-((3*π/2 - 2*θ)*|y|))), ?_,
      Eventually.of_forall fun y z hz => ?_⟩
    · exact (DLMF.Gamma.integrable_one_add_abs_pow_mul_exp_neg (by simp only [θ]; linarith)
        K).const_mul _
    · obtain ⟨⟨h1, h2⟩, h3⟩ := hz
      refine (hCK z (slitPlane_ne_zero h3.1) y).trans ?_
      have hR : ‖z‖^(2*c) ≤ R^(2*c) :=
        Real.rpow_le_rpow (norm_nonneg _) h2.le (by linarith)
      have he : Real.exp (-((3*π/2 - 2*|arg z|)*|y|)) ≤ Real.exp (-((3*π/2 - 2*θ)*|y|)) := by
        apply Real.exp_le_exp.mpr; nlinarith [abs_nonneg y]
      dsimp only
      gcongr

/-- DLMF 12.5.8, value and integrability. -/
lemma pcfInt_B_integral (a : ℂ) {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 3*π/4) {c : ℝ}
    (hc : 0 < c) (hca : 2*c < 1/2 + a.re) :
    ∫ y, pcfInt_B a z c y = 2*π*Gamma (1/2+1*a)*(exp (z^2/4)*z^(a+1/2))*pcfU a z := by
  have hF := (pcfInt_B_differentiableOn a hc hca).analyticOnNhd pcfInt_isOpen_sector
  have hG : AnalyticOnNhd ℂ (fun z => 2*π*Gamma (1/2+1*a)*(exp (z^2/4)*z^(a+1/2))*pcfU a z)
      pcfInt_sector := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) pcfInt_isOpen_sector
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((differentiableAt_const _).mul ((((differentiableAt_id.pow 2).div_const 4).cexp).mul
      (differentiableAt_id.cpow_const hz.1))).mul ((pcfU_entire a) z)
  have h1 : (1:ℂ) ∈ pcfInt_sector := pcfInt_mem_sector one_ne_zero (by simp; positivity)
  have hfreq : ∃ᶠ w in 𝓝[≠] (1:ℂ), (∫ y, pcfInt_B a w c y) =
      2*π*Gamma (1/2+1*a)*(exp (w^2/4)*w^(a+1/2))*pcfU a w := by
    have hmap : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[≠] (1:ℝ)) (𝓝[≠] (1:ℂ)) := by
      have := continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (s := {(1:ℝ)}ᶜ)
        (t := {(1:ℂ)}ᶜ) (x := 1) (fun x hx h => hx (by simp at h ⊢; exact_mod_cast h))
      simpa using this
    have hev : ∀ᶠ x : ℝ in 𝓝[≠] (1:ℝ), (∫ y, pcfInt_B a (x:ℂ) c y) =
        2*π*Gamma (1/2+1*a)*(exp ((x:ℂ)^2/4)*(x:ℂ)^(a+1/2))*pcfU a x := by
      filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with x hx
      exact pcfInt_B_real a hc hca hx
    exact hmap.frequently hev.frequently
  exact hF.eqOn_of_preconnected_of_frequently_eq hG pcfInt_isPreconnected_sector h1 hfreq
    (pcfInt_mem_sector hz0 hz)

end DLMF.Confluent
