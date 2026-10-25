/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Asymptotics
public import DLMFMathlib.Analysis.Complex.RotateRay

/-!
# Tricomi's function along rotated rays (Temme §7.2; DLMF 13.4.4, 13.7.3)

For `re a > 0` and `|α| < π/2`, rotating the ray of integration in Tricomi's Laplace integral
gives

`U(a,b,z) = 1/Γ(a) · e^{iα} ∫₀^∞ e^{-z r e^{iα}} (r e^{iα})^{a-1} (1 + r e^{iα})^{b-a-1} dr`

on the half-plane `re (z e^{iα}) > 0` (`kummerU_eq_tricomiRotated`). The rotation uses
`Complex.integral_Ioi_eq_exp_mul_integral_Ioi_rotate` on the common half-plane and extends by
analytic continuation. Watson's lemma in a sector then gives Tricomi's expansion as `z → ∞` in
every rotated sector `δ |z| ≤ re (z e^{iα})` (`hasAsymptoticExpansion_kummerU_rotSector`).
These sectors cover `|arg z| ≤ π - ε`, including the imaginary axis needed for the Coulomb
and Fresnel functions.
-/

@[expose] public section

open Complex Filter MeasureTheory Asymptotics Set
open scoped Real Topology Nat Interval
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-- `(z e^{iα})^w = z^w e^{iαw}` when `arg z + α ∈ (-π, π]`. -/
lemma cpow_mul_exp_mul_I {z : ℂ} (hz : z ≠ 0) {α : ℝ} (h1 : -π < arg z + α)
    (h2 : arg z + α ≤ π) (w : ℂ) :
    (z * exp (α * I)) ^ w = z ^ w * exp (α * I * w) := by
  have hlog : log (z * exp (α * I)) = log z + α * I := by
    have : z * exp (α * I) = exp (log z + α * I) := by rw [exp_add, exp_log hz]
    rw [this, log_exp] <;> simp [log_im] <;> linarith
  rw [cpow_def_of_ne_zero (mul_ne_zero hz (exp_ne_zero _)), hlog, cpow_def_of_ne_zero hz,
    ← exp_add]
  ring_nf

/-- `re (z e^{iy}) = |z| cos(arg z + y)`. -/
lemma re_mul_exp_mul_I (z : ℂ) (y : ℝ) : (z * exp (y * I)).re = ‖z‖ * Real.cos (arg z + y) := by
  conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
  rw [mul_assoc, ← exp_add, show (arg z : ℂ) * I + y * I = ((arg z + y : ℝ) : ℂ) * I by
    push_cast; ring, re_ofReal_mul, exp_ofReal_mul_I_re]

/-- A real angle in `(-3π/2, 3π/2)` with positive cosine lies in `(-π/2, π/2)`. -/
lemma abs_lt_pi_div_two_of_cos_pos {u : ℝ} (h1 : -(3 * π / 2) < u) (h2 : u < 3 * π / 2)
    (hc : 0 < Real.cos u) : |u| < π / 2 := by
  rw [abs_lt]
  constructor
  · by_contra h
    push_neg at h
    have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := -u) (by linarith) (by linarith)
    rw [Real.cos_neg] at this; linarith
  · by_contra h
    push_neg at h
    have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := u) h (by linarith)
    linarith

/-- Along the sector between two directions where `re (z e^{iy}) > 0`, the real part stays
above the smaller endpoint value. -/
lemma re_mul_exp_mul_I_ge {z : ℂ} {α : ℝ} (hα : |α| < π / 2) (hz0 : 0 < z.re)
    (hzα : 0 < (z * exp (α * I)).re) {y : ℝ} (hy : y ∈ [[0, α]]) :
    min z.re (z * exp (α * I)).re ≤ (z * exp (y * I)).re := by
  have hz : z ≠ 0 := by intro h; rw [h] at hz0; simp at hz0
  have hφ : |arg z| < π / 2 := by
    rw [Complex.abs_arg_lt_pi_div_two_iff]; exact Or.inl hz0
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [re_mul_exp_mul_I] at hzα ⊢
  rw [re_mul_exp_mul_I]
  have hcosα : 0 < Real.cos (arg z + α) := by
    by_contra h; push_neg at h; nlinarith
  have hφα : |arg z + α| < π / 2 := abs_lt_pi_div_two_of_cos_pos
    (by linarith [abs_lt.mp hφ, abs_lt.mp hα]) (by linarith [abs_lt.mp hφ, abs_lt.mp hα]) hcosα
  have hre0 : z.re = ‖z‖ * Real.cos (arg z + 0) := by
    rw [← re_mul_exp_mul_I]; simp
  rw [hre0, add_zero]
  -- `|arg z + y| ≤ max (|arg z|, |arg z + α|)`
  have hmax : |arg z + y| ≤ max |arg z| |arg z + α| := by
    rcases le_total 0 α with h | h
    · rw [uIcc_of_le h] at hy
      rw [abs_le]; constructor
      · have := neg_abs_le (arg z); have := le_max_left |arg z| |arg z + α|; linarith [hy.1]
      · have := le_abs_self (arg z + α); have := le_max_right |arg z| |arg z + α|; linarith [hy.2]
    · rw [uIcc_of_ge h] at hy
      rw [abs_le]; constructor
      · have := neg_abs_le (arg z + α); have := le_max_right |arg z| |arg z + α|; linarith [hy.1]
      · have := le_abs_self (arg z); have := le_max_left |arg z| |arg z + α|; linarith [hy.2]
  have hmaxpi : max |arg z| |arg z + α| ≤ π := by
    rw [max_le_iff]; constructor <;> linarith [Real.pi_pos]
  have hcos : Real.cos (max |arg z| |arg z + α|) ≤ Real.cos (arg z + y) := by
    rw [← Real.cos_abs (arg z + y)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hmaxpi hmax
  have hmin :
      min (Real.cos (arg z)) (Real.cos (arg z + α)) ≤ Real.cos (max |arg z| |arg z + α|) := by
    rcases le_total |arg z| |arg z + α| with h | h
    · rw [max_eq_right h, ← Real.cos_abs (arg z + α)]; exact min_le_right _ _
    · rw [max_eq_left h, ← Real.cos_abs (arg z)]; exact min_le_left _ _
  rw [← mul_min_of_nonneg _ _ hzn.le]
  exact mul_le_mul_of_nonneg_left (hmin.trans hcos) hzn.le

lemma norm_cpow_le_exp (t w : ℂ) : ‖t ^ w‖ ≤ ‖t‖ ^ w.re * Real.exp (π * |w.im|) := by
  refine (norm_cpow_le t w).trans ?_
  rw [div_eq_mul_inv, ← Real.exp_neg]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg (norm_nonneg _) _)
  have h1 := Complex.abs_arg_le_pi t
  have h2 : |arg t * w.im| ≤ π * |w.im| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  linarith [neg_abs_le (arg t * w.im)]

lemma norm_one_add_cpow_le {t c : ℂ} (ht : 0 ≤ t.re) {N : ℕ} (hN : |c.re| ≤ N) :
    ‖(1 + t) ^ c‖ ≤ (1 + ‖t‖) ^ N * Real.exp (π * |c.im|) := by
  refine (norm_cpow_le_exp _ _).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  have h1 : 1 ≤ ‖1 + t‖ := by
    have := Complex.re_le_norm (1 + t); simp at this; linarith
  have h2 : ‖1 + t‖ ≤ 1 + ‖t‖ := by simpa using norm_add_le (1 : ℂ) t
  rcases le_total 0 c.re with hc | hc
  · calc ‖1 + t‖ ^ c.re ≤ (1 + ‖t‖) ^ c.re := Real.rpow_le_rpow (by linarith) h2 hc
      _ ≤ (1 + ‖t‖) ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg t])
          (by linarith [le_abs_self c.re])
      _ = _ := Real.rpow_natCast _ _
  · calc ‖1 + t‖ ^ c.re ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 hc
      _ ≤ (1 + ‖t‖) ^ N := one_le_pow₀ (by linarith [norm_nonneg t])

/-- `r^s e^{-br}` is bounded on `[1, ∞)` for `b > 0`. -/
lemma exists_rpow_mul_exp_neg_le (s : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ M, ∀ r : ℝ, 1 ≤ r → r ^ s * Real.exp (-b * r) ≤ M := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb).eventually (ge_mem_nhds zero_lt_one))
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := max R 1)).exists_bound_of_continuousOn
    (f := fun r : ℝ => r ^ s * Real.exp (-b * r)) (fun r hr => by
      have : r ≠ 0 := by linarith [hr.1]
      exact (((Real.continuousAt_rpow_const r s (Or.inl this)).mul
        (by fun_prop : Continuous fun r : ℝ => Real.exp (-b * r)).continuousAt)).continuousWithinAt)
  refine ⟨max M 1, fun r hr => ?_⟩
  by_cases h : r ≤ max R 1
  · have := hM r ⟨hr, h⟩
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  · push_neg at h
    exact (hR r (le_of_lt ((le_max_left R 1).trans_lt h))).trans (le_max_right _ _)

/-- The integrand of Tricomi's Laplace representation. -/
def tricomiKernel (a b z t : ℂ) : ℂ := exp (-z * t) * t ^ (a - 1) * (1 + t) ^ (b - a - 1)

lemma norm_tricomiKernel_le (a b z t : ℂ) (ht : 0 ≤ t.re) {N : ℕ} (hN : |(b - a - 1).re| ≤ N) :
    ‖tricomiKernel a b z t‖ ≤ Real.exp (-(z * t).re) * ‖t‖ ^ (a.re - 1) * (1 + ‖t‖) ^ N *
      (Real.exp (π * |a.im|) * Real.exp (π * |(b - a - 1).im|)) := by
  rw [tricomiKernel, norm_mul, norm_mul, Complex.norm_exp, neg_mul, neg_re]
  have h1 := norm_cpow_le_exp t (a - 1)
  simp only [sub_re, one_re, sub_im, one_im, sub_zero] at h1
  have h2 := norm_one_add_cpow_le (c := b - a - 1) ht hN
  have he := Real.exp_pos (-(z * t).re)
  calc Real.exp (-(z * t).re) * ‖t ^ (a - 1)‖ * ‖(1 + t) ^ (b - a - 1)‖
      ≤ Real.exp (-(z * t).re) * (‖t‖ ^ (a.re - 1) * Real.exp (π * |a.im|)) *
          ((1 + ‖t‖) ^ N * Real.exp (π * |(b - a - 1).im|)) := by gcongr
    _ = _ := by ring

lemma re_ofReal_mul_exp_pos {r y : ℝ} (hr : 0 < r) (hy : |y| < π / 2) :
    0 < ((r : ℂ) * exp (y * I)).re := by
  rw [re_ofReal_mul, exp_ofReal_mul_I_re]
  exact mul_pos hr
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩)

lemma abs_lt_of_mem_uIcc {α y : ℝ} (hα : |α| < π / 2) (hy : y ∈ [[0, α]]) : |y| < π / 2 := by
  refine lt_of_le_of_lt ?_ hα
  rcases le_total 0 α with h | h
  · rw [uIcc_of_le h] at hy; rw [abs_of_nonneg hy.1, abs_of_nonneg h]; exact hy.2
  · rw [uIcc_of_ge h] at hy; rw [abs_of_nonpos hy.2, abs_of_nonpos h]; linarith [hy.1]

lemma differentiableAt_tricomiKernel (a b z : ℂ) {t : ℂ} (ht : 0 < t.re) :
    DifferentiableAt ℂ (tricomiKernel a b z) t := by
  have h1 : t ∈ slitPlane := Or.inl ht
  have h2 : 1 + t ∈ slitPlane := Or.inl (by simp; linarith)
  unfold tricomiKernel
  exact ((by fun_prop : DifferentiableAt ℂ (fun t : ℂ => exp (-z * t)) t).mul
    (differentiableAt_id.cpow (differentiableAt_const _) h1)).mul
    ((differentiableAt_const _ |>.add differentiableAt_id).cpow (differentiableAt_const _) h2)

/-- **Rotation of Tricomi's Laplace integral**: for `re a > 0`, `|α| < π/2` and `z` with
`re z > 0`, `re (z e^{iα}) > 0`,
`U(a,b,z) = 1/Γ(a) · e^{iα} ∫₀^∞ e^{-z r e^{iα}} (r e^{iα})^{a-1} (1 + r e^{iα})^{b-a-1} dr`. -/
lemma kummerU_eq_rotated_of_re_pos {a b z : ℂ} {α : ℝ} (ha : 0 < a.re) (hα : |α| < π / 2)
    (hz0 : 0 < z.re) (hzα : 0 < (z * exp (α * I)).re) :
    kummerU a b z = 1 / Gamma a * (exp (α * I) *
      ∫ r in Ioi (0 : ℝ), tricomiKernel a b z (r * exp (α * I))) := by
  set κ0 := min z.re (z * exp (α * I)).re with hκ0
  have hκ0pos : 0 < κ0 := lt_min hz0 hzα
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |(b - a - 1).re| ≤ N := ⟨⌈|(b - a - 1).re|⌉₊, Nat.le_ceil _⟩
  set E := Real.exp (π * |a.im|) * Real.exp (π * |(b - a - 1).im|) with hE
  have hE0 : 0 < E := by positivity
  obtain ⟨M, hM⟩ := exists_rpow_mul_exp_neg_le (a.re - 1 + N) (b := κ0 / 2) (by positivity)
  have hM0 : 0 ≤ M :=
    (by positivity : (0 : ℝ) ≤ 1 ^ (a.re - 1 + N) * Real.exp (-(κ0 / 2) * 1)).trans
    (hM 1 le_rfl)
  set C := max (2 ^ N * E) (2 ^ N * E * M) with hC
  -- the pointwise bound on the sector
  have hbound : ∀ r : ℝ, 0 < r → ∀ y ∈ [[0, α]], ‖tricomiKernel a b z (r * exp (y * I))‖ ≤
      Real.exp (-κ0 * r) * r ^ (a.re - 1) * (1 + r) ^ N * E := by
    intro r hr y hy
    have hy' := abs_lt_of_mem_uIcc hα hy
    have ht := re_ofReal_mul_exp_pos hr hy'
    have hb := norm_tricomiKernel_le a b z _ ht.le hN
    have hnorm : ‖(r : ℂ) * exp (y * I)‖ = r := by
      rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]
    rw [hnorm] at hb
    refine hb.trans ?_
    have hre : κ0 * r ≤ (z * ((r : ℂ) * exp (y * I))).re := by
      rw [mul_left_comm, re_ofReal_mul]
      have := re_mul_exp_mul_I_ge hα hz0 hzα hy
      nlinarith
    gcongr
    linarith
  rw [kummerU_laplace ha hz0]
  congr 1
  rw [← Complex.integral_Ioi_eq_exp_mul_integral_Ioi_rotate (σ := a.re) (κ := κ0 / 2) (C := C)
    ha (by positivity)]
  · rfl
  · intro r hr y hy
    exact differentiableAt_tricomiKernel a b z
      (re_ofReal_mul_exp_pos hr (abs_lt_of_mem_uIcc hα hy))
  · intro r hr hr1 y hy
    refine (hbound r hr y hy).trans ?_
    have h1 : Real.exp (-κ0 * r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h2 : (1 + r) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    have h3 := Real.rpow_nonneg hr.le (a.re - 1)
    calc Real.exp (-κ0 * r) * r ^ (a.re - 1) * (1 + r) ^ N * E
        ≤ 1 * r ^ (a.re - 1) * 2 ^ N * E := by gcongr
      _ = 2 ^ N * E * r ^ (a.re - 1) := by ring
      _ ≤ C * r ^ (a.re - 1) := by gcongr; exact le_max_left _ _
  · intro r hr y hy
    have hr0 : 0 < r := by linarith
    refine (hbound r hr0 y hy).trans ?_
    have h2 : (1 + r) ^ N ≤ 2 ^ N * r ^ N := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) N
    have hsplit : Real.exp (-κ0 * r) = Real.exp (-(κ0 / 2) * r) * Real.exp (-(κ0 / 2) * r) := by
      rw [← Real.exp_add]; ring_nf
    have hrN : r ^ (a.re - 1) * r ^ N = r ^ (a.re - 1 + N) := by
      rw [Real.rpow_add hr0, Real.rpow_natCast]
    have hMr := hM r hr
    calc Real.exp (-κ0 * r) * r ^ (a.re - 1) * (1 + r) ^ N * E
        ≤ Real.exp (-κ0 * r) * r ^ (a.re - 1) * (2 ^ N * r ^ N) * E := by gcongr
      _ = 2 ^ N * E * (r ^ (a.re - 1 + N) * Real.exp (-(κ0 / 2) * r)) *
            Real.exp (-(κ0 / 2) * r) := by rw [hsplit, ← hrN]; ring
      _ ≤ 2 ^ N * E * M * Real.exp (-(κ0 / 2) * r) := by gcongr
      _ ≤ C * Real.exp (-(κ0 / 2) * r) := by gcongr; exact le_max_right _ _

/-- The rotated Laplace integral `1/Γ(a) · e^{iα} ∫₀^∞ K(r e^{iα}) dr`. -/
def tricomiRotated (a b : ℂ) (α : ℝ) (z : ℂ) : ℂ :=
  1 / Gamma a * (exp (α * I) * ∫ r in Ioi (0 : ℝ), tricomiKernel a b z (r * exp (α * I)))

/-- A real majorant `e^{-δr} r^{s} (1+r)^N` is integrable on `(0, ∞)` for `s > -1`, `δ > 0`. -/
lemma integrableOn_exp_mul_rpow_mul_one_add_pow {s δ : ℝ} (hs : -1 < s) (hδ : 0 < δ) (N : ℕ) :
    IntegrableOn (fun r : ℝ => Real.exp (-δ * r) * r ^ s * (1 + r) ^ N) (Ioi 0) := by
  have h := (kummerU_laplace_integrable (a := (s + 1 : ℝ)) (b := (s + 1 : ℝ) + N + 1)
    (z := (δ : ℂ)) (by simp; linarith) (by simpa using hδ)).norm
  refine IntegrableOn.congr_fun h (fun r hr => ?_) measurableSet_Ioi
  have hr : (0 : ℝ) < r := hr
  rw [norm_mul, norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos hr,
    show ((s + 1 : ℝ) : ℂ) + N + 1 - ((s + 1 : ℝ) : ℂ) - 1 = (N : ℂ) by ring, cpow_natCast,
    norm_pow, show 1 + (r : ℂ) = ((1 + r : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg (by linarith)]
  simp

lemma norm_mul_exp_I_eq (r : ℝ) (hr : 0 ≤ r) (y : ℝ) : ‖(r : ℂ) * exp (y * I)‖ = r := by
  rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hr]

/-- The rotated integral is holomorphic on the half-plane `re (z e^{iα}) > 0`. -/
lemma differentiableOn_tricomiRotated {a b : ℂ} {α : ℝ} (ha : 0 < a.re) (hα : |α| < π / 2) :
    DifferentiableOn ℂ (tricomiRotated a b α) {z : ℂ | 0 < (z * exp (α * I)).re} := by
  intro z₀ hz₀
  change 0 < (z₀ * exp (α * I)).re at hz₀
  set ω := exp (α * I) with hω
  set δ : ℝ := (z₀ * ω).re / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hre : ∀ z ∈ Metric.ball z₀ δ, ∀ r : ℝ, 0 ≤ r → δ * r ≤ (z * ((r : ℂ) * ω)).re := by
    intro z hz r hr
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 : |((z - z₀) * ω).re| ≤ ‖z - z₀‖ := by
      refine (abs_re_le_norm _).trans ?_
      rw [norm_mul, hω, norm_exp_ofReal_mul_I, mul_one]
    have h2 : (z * ((r : ℂ) * ω)).re = r * (z * ω).re := by
      rw [mul_left_comm, re_ofReal_mul]
    have h3 : (z * ω).re = (z₀ * ω).re + ((z - z₀) * ω).re := by
      rw [← add_re]; ring_nf
    rw [h2, h3]
    have := (abs_le.mp h1).1
    nlinarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |(b - a - 1).re| ≤ N := ⟨⌈|(b - a - 1).re|⌉₊, Nat.le_ceil _⟩
  set E := Real.exp (π * |a.im|) * Real.exp (π * |(b - a - 1).im|) with hE
  set F : ℂ → ℝ → ℂ := fun z r => tricomiKernel a b z (r * ω) with hF
  have hslit : ∀ r : ℝ, 0 < r → 0 < ((r : ℂ) * ω).re := fun r hr =>
    re_ofReal_mul_exp_pos hr hα
  have hcontF : ∀ z : ℂ, ContinuousOn (F z) (Ioi 0) := fun z r hr =>
    (ContinuousAt.comp (g := tricomiKernel a b z) (f := fun r : ℝ => (r : ℂ) * ω) (x := r)
      (differentiableAt_tricomiKernel a b z (hslit r hr)).continuousAt
      (by fun_prop : Continuous fun r : ℝ => (r : ℂ) * ω).continuousAt).continuousWithinAt
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (F z) (volume.restrict (Ioi 0)) := fun z =>
    (hcontF z).aestronglyMeasurable measurableSet_Ioi
  have hbnd : ∀ z ∈ Metric.ball z₀ δ, ∀ r : ℝ, 0 < r →
      ‖F z r‖ ≤ Real.exp (-δ * r) * r ^ (a.re - 1) * (1 + r) ^ N * E := by
    intro z hz r hr
    have hb := norm_tricomiKernel_le a b z _ (hslit r hr).le hN
    rw [norm_mul_exp_I_eq r hr.le] at hb
    refine hb.trans ?_
    have := hre z hz r hr.le
    gcongr
    linarith
  set G : ℝ → ℝ := fun r => Real.exp (-δ * r) * r ^ a.re * (1 + r) ^ N * E with hGdef
  have hG : IntegrableOn G (Ioi 0) :=
    (integrableOn_exp_mul_rpow_mul_one_add_pow (by linarith) hδ0 N).mul_const E
  have hint0 : Integrable (F z₀) (volume.restrict (Ioi 0)) := by
    refine Integrable.mono' ((integrableOn_exp_mul_rpow_mul_one_add_pow (s := a.re - 1)
      (by linarith) hδ0 N).mul_const E) (hmeas z₀) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    exact hbnd z₀ (Metric.mem_ball_self hδ0) r hr
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) (F := F) (F' := fun z r => -((r : ℂ) * ω) * F z r)
    (bound := G) (Metric.ball_mem_nhds _ hδ0) (Eventually.of_forall hmeas) hint0
    ((((by fun_prop : Continuous fun r : ℝ => -((r : ℂ) * ω)).continuousOn).mul
      (hcontF z₀)).aestronglyMeasurable measurableSet_Ioi) ?_ hG ?_
  · exact ((hd.2.const_mul ω).const_mul (1 / Gamma a)).differentiableAt.differentiableWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr z hz => ?_)
    have hr : (0 : ℝ) < r := hr
    rw [norm_mul, norm_neg, norm_mul_exp_I_eq r hr.le]
    have hp : r * r ^ (a.re - 1) = r ^ a.re := by
      rw [mul_comm, ← Real.rpow_add_one hr.ne', sub_add_cancel]
    calc r * ‖F z r‖ ≤ r * (Real.exp (-δ * r) * r ^ (a.re - 1) * (1 + r) ^ N * E) :=
          mul_le_mul_of_nonneg_left (hbnd z hz r hr) hr.le
      _ = G r := by rw [hGdef]; simp only; rw [← hp]; ring
  · refine Eventually.of_forall fun r z _ => ?_
    have h := (((hasDerivAt_id z).neg.mul_const ((r : ℂ) * ω)).cexp.mul_const
      (((r : ℂ) * ω) ^ (a - 1))).mul_const ((1 + (r : ℂ) * ω) ^ (b - a - 1))
    simp only [hF, tricomiKernel]
    convert h using 1
    · funext w; simp
    · simp; ring

/-- **Rotated Laplace representation of `U`** (Temme §7.2): for `re a > 0`, `|α| < π/2` and
`re (z e^{iα}) > 0`, `U(a,b,z) = 1/Γ(a) · e^{iα} ∫₀^∞ e^{-z r e^{iα}} (r e^{iα})^{a-1}
(1 + r e^{iα})^{b-a-1} dr`. This continues `U` beyond the right half-plane. -/
theorem kummerU_eq_tricomiRotated {a b z : ℂ} {α : ℝ} (ha : 0 < a.re) (hα : |α| < π / 2)
    (hz : 0 < (z * exp (α * I)).re) : kummerU a b z = tricomiRotated a b α z := by
  set ω := exp (α * I) with hω
  set H : Set ℂ := {z : ℂ | 0 < (z * ω).re} with hH
  have hcosα : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le α, Real.pi_pos],
      by linarith [le_abs_self α, Real.pi_pos]⟩
  have hHo : IsOpen H := isOpen_lt continuous_const (by fun_prop)
  have hHc : Convex ℝ H := by
    intro z₁ hz₁ z₂ hz₂ s t hs ht hst
    change 0 < ((s • z₁ + t • z₂) * ω).re
    change 0 < (z₁ * ω).re at hz₁
    change 0 < (z₂ * ω).re at hz₂
    rw [add_mul, add_re, smul_mul_assoc, smul_mul_assoc, Complex.smul_re, Complex.smul_re,
      smul_eq_mul, smul_eq_mul]
    rcases eq_or_lt_of_le hs with h | h
    · subst h; simp at hst; subst hst; simpa using hz₂
    · nlinarith [mul_pos h hz₁, mul_nonneg ht hz₂.le]
  have hHslit : H ⊆ slitPlane := by
    intro w hw
    change 0 < (w * ω).re at hw
    by_contra h
    rw [mem_slitPlane_iff, not_or] at h
    push_neg at h
    have hw' : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [h.2])
    rw [hw', re_ofReal_mul, hω, exp_ofReal_mul_I_re] at hw
    nlinarith [h.1]
  have hU : AnalyticOnNhd ℂ (kummerU a b) H :=
    ((differentiableOn_kummerU a b).mono hHslit).analyticOnNhd hHo
  have hV : AnalyticOnNhd ℂ (tricomiRotated a b α) H :=
    (differentiableOn_tricomiRotated ha hα).analyticOnNhd hHo
  set zs : ℂ := exp ((-(α / 2) : ℝ) * I) with hzs
  have hzs0 : 0 < zs.re := by
    rw [hzs, exp_ofReal_mul_I_re, Real.cos_neg]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le α, Real.pi_pos],
      by linarith [le_abs_self α, Real.pi_pos]⟩
  have hzsH : 0 < (zs * ω).re := by
    rw [hzs, hω, ← exp_add, show ((-(α / 2) : ℝ) : ℂ) * I + α * I = ((α / 2 : ℝ) : ℂ) * I by
      push_cast; ring, exp_ofReal_mul_I_re]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le α, Real.pi_pos],
      by linarith [le_abs_self α, Real.pi_pos]⟩
  have hev : kummerU a b =ᶠ[𝓝 zs] tricomiRotated a b α := by
    have hopen : IsOpen {w : ℂ | 0 < w.re ∧ 0 < (w * ω).re} :=
      (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const
        (by fun_prop : Continuous fun w : ℂ => (w * ω).re))
    filter_upwards [hopen.mem_nhds ⟨hzs0, hzsH⟩] with w hw
    exact kummerU_eq_rotated_of_re_pos ha hα hw.1 hw.2
  exact hU.eqOn_of_preconnected_of_eventuallyEq hV hHc.isPreconnected hzsH hev hz

/-- The binomial expansion of `(1 + tω)^β` at `t = 0⁺` with an `O(t^N)` remainder. -/
lemma one_add_mul_cpow_sub_sum_isBigO (ω β : ℂ) (N : ℕ) :
    (fun t : ℝ => (1 + (t : ℂ) * ω) ^ β -
      ∑ n ∈ Finset.range N, Ring.choose β n * ((t : ℂ) * ω) ^ n) =O[𝓝[>] 0] fun t => t ^ N := by
  have h := (Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := β)).isBigO_sub_partialSum_pow N
  have ht : Tendsto (fun t : ℝ => (t : ℂ) * ω) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => (t : ℂ) * ω := by fun_prop
    exact (hc.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
  refine ((h.comp_tendsto ht).congr' (Eventually.of_forall fun t => ?_) ?_).trans
    (isBigO_const_mul_self (‖ω‖ ^ N) _ _)
  · simp [FormalMultilinearSeries.partialSum, binomialSeries, smul_eq_mul, mul_comm]
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp [abs_of_pos (show (0 : ℝ) < t from ht), mul_pow, mul_comm]

/-- The filter `z → ∞` with `δ |z e^{iα}| ≤ re (z e^{iα})`. -/
def rotSectorAtTop (δ α : ℝ) : Filter ℂ :=
  comap (fun z : ℂ => z * exp (α * I)) (sectorAtTop δ)

lemma tendsto_rotSectorAtTop (δ α : ℝ) :
    Tendsto (fun z : ℂ => z * exp (α * I)) (rotSectorAtTop δ α) (sectorAtTop δ) := tendsto_comap

lemma eventually_rotSectorAtTop {δ α : ℝ} (hδ : 0 < δ) (hα : |α| < π / 2) :
    ∀ᶠ z in rotSectorAtTop δ α, 1 ≤ ‖z‖ ∧ 0 < (z * exp (α * I)).re ∧
      |arg z + α| < π / 2 := by
  have h := (tendsto_rotSectorAtTop δ α).eventually (eventually_sectorAtTop (R := 1)
    (p := fun w : ℂ => 1 ≤ ‖w‖ ∧ 0 < w.re) fun w hw hws => ⟨hw, by nlinarith⟩)
  filter_upwards [h] with z hz
  have hn : ‖z * exp (α * I)‖ = ‖z‖ := by rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]
  rw [hn] at hz
  refine ⟨hz.1, hz.2, ?_⟩
  have hre := hz.2
  rw [re_mul_exp_mul_I] at hre
  have hz0 : 0 < ‖z‖ := by linarith [hz.1]
  have hc : 0 < Real.cos (arg z + α) := by
    by_contra h; push_neg at h; nlinarith
  have h1 := Complex.neg_pi_lt_arg z
  have h2 := Complex.arg_le_pi z
  exact abs_lt_pi_div_two_of_cos_pos (by linarith [neg_abs_le α]) (by linarith [le_abs_self α]) hc

/-- Tricomi's expansion in the rotated sector, for `re a > 0`. -/
lemma hasAsymptoticExpansion_kummerU_rotSector_of_re_pos {a b : ℂ} (ha : 0 < a.re) {δ α : ℝ}
    (hδ : 0 < δ) (hα : |α| < π / 2) :
    HasAsymptoticExpansion (rotSectorAtTop δ α) (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + a)))
      (tricomiCoeff a b) (fun z => kummerU a b z) := by
  set ω := exp (α * I) with hω
  have hαpi1 : -π < 0 + α := by linarith [neg_abs_le α, Real.pi_pos]
  have hαpi2 : 0 + α ≤ π := by linarith [le_abs_self α, Real.pi_pos]
  have hrpow : ∀ (r : ℝ), 0 < r → ∀ w : ℂ, ((r : ℂ) * ω) ^ w = (r : ℂ) ^ w * exp (α * I * w) := by
    intro r hr w
    have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
    have := cpow_mul_exp_mul_I hr0 (α := α) (by rw [arg_ofReal_of_nonneg hr.le]; exact hαpi1)
      (by rw [arg_ofReal_of_nonneg hr.le]; exact hαpi2) w
    rw [hω]; exact this
  set F : ℝ → ℂ := fun r => ω * (((r : ℂ) * ω) ^ (a - 1) * (1 + (r : ℂ) * ω) ^ (b - a - 1))
    with hF
  set A : ℕ → ℂ := fun n => exp (α * I * ((n : ℂ) + a)) * Ring.choose (b - a - 1) n with hA
  obtain ⟨N0, hN0⟩ : ∃ N : ℕ, |(b - a - 1).re| ≤ N := ⟨⌈|(b - a - 1).re|⌉₊, Nat.le_ceil _⟩
  set E := Real.exp (π * |a.im|) * Real.exp (π * |(b - a - 1).im|) with hE
  have hslit : ∀ r : ℝ, 0 < r → 0 < ((r : ℂ) * ω).re := fun r hr => re_ofReal_mul_exp_pos hr hα
  have hFcont : ContinuousOn F (Ioi 0) := fun r hr => by
    have h1 : (r : ℂ) * ω ∈ slitPlane := Or.inl (hslit r hr)
    have h2 : 1 + (r : ℂ) * ω ∈ slitPlane := Or.inl (by rw [add_re, one_re]; linarith [hslit r hr])
    have hc : ContinuousAt (fun r : ℝ => (r : ℂ) * ω) r := by fun_prop
    exact (continuousAt_const.mul ((hc.cpow continuousAt_const h1).mul
      ((continuousAt_const.add hc).cpow continuousAt_const h2))).continuousWithinAt
  have hFb : ∀ r : ℝ, 0 < r → ‖F r‖ ≤ r ^ (a.re - 1) * (1 + r) ^ N0 * E := by
    intro r hr
    have h1 := norm_cpow_le_exp ((r : ℂ) * ω) (a - 1)
    have h2 := norm_one_add_cpow_le (t := (r : ℂ) * ω) (c := b - a - 1) (hslit r hr).le hN0
    rw [hω, norm_mul_exp_I_eq r hr.le] at h1 h2
    simp only [sub_re, one_re, sub_im, one_im, sub_zero] at h1
    rw [hF, norm_mul, norm_mul, hω, norm_exp_ofReal_mul_I, one_mul]
    calc ‖((r : ℂ) * exp (α * I)) ^ (a - 1)‖ * ‖(1 + (r : ℂ) * exp (α * I)) ^ (b - a - 1)‖
        ≤ (r ^ (a.re - 1) * Real.exp (π * |a.im|)) *
          ((1 + r) ^ N0 * Real.exp (π * |(b - a - 1).im|)) := by gcongr
      _ = _ := by rw [hE]; ring
  have hint : IntegrableOn (fun r => Real.exp (-1 * r) • F r) (Ioi 0) := by
    refine ((integrableOn_exp_mul_rpow_mul_one_add_pow (s := a.re - 1) (by linarith) one_pos
      N0).mul_const E).mono' ((((by fun_prop : Continuous fun r : ℝ => Real.exp (-1 * r)
        ).continuousOn.smul hFcont)).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    rw [norm_smul, Real.norm_eq_abs, Real.abs_exp]
    have := hFb r hr
    calc Real.exp (-1 * r) * ‖F r‖ ≤ Real.exp (-1 * r) * (r ^ (a.re - 1) * (1 + r) ^ N0 * E) :=
          mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
      _ = _ := by ring
  have hFexp : ∀ N : ℕ, (fun r => F r - ∑ n ∈ Finset.range N,
      ((r : ℂ) ^ ((n : ℂ) + a - 1)) • A n) =O[𝓝[>] 0] fun r => r ^ ((N : ℝ) + a.re - 1) := by
    intro N
    have h1 : (fun r : ℝ => ω * exp (α * I * (a - 1)) * (r : ℂ) ^ (a - 1)) =O[𝓝[>] 0]
        fun r => r ^ (a.re - 1) := by
      refine IsBigO.of_bound ‖ω * exp (α * I * (a - 1))‖ ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr : (0 : ℝ) < r := hr
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hr _)]
      simp
    refine ((h1.mul (one_add_mul_cpow_sub_sum_isBigO ω (b - a - 1) N)).congr' ?_ ?_)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr : (0 : ℝ) < r := hr
      have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
      simp only [hF, hA, smul_eq_mul, mul_sub, Finset.mul_sum]
      rw [hrpow r hr]
      congr 1
      · ring
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [show (n : ℂ) + a - 1 = (n : ℂ) + (a - 1) by ring, Complex.cpow_add _ _ hr0,
        Complex.cpow_natCast, mul_pow, hω, ← Complex.exp_nat_mul,
        show α * I * ((n : ℂ) + a) = α * I * (a - 1) + (n * (α * I) + α * I) by ring,
        Complex.exp_add, Complex.exp_add]
      ring
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr : (0 : ℝ) < r := hr
      rw [show (N : ℝ) + a.re - 1 = (a.re - 1) + N by ring, Real.rpow_add hr,
        Real.rpow_natCast]
  have hW := ((hasAsymptoticExpansion_integral_cexp_smul_sector ha hδ hint hFexp).const_smul
    (1 / Gamma a)).comp_tendsto (tendsto_rotSectorAtTop δ α)
  have ha' : ∀ k : ℕ, a ≠ -k := fun k hk => by
    have := congrArg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hev := eventually_rotSectorAtTop hδ hα
  refine ((hW.smul_scale (κ := fun n => exp (α * I * (-((n : ℂ) + a)))) (ψ := fun (n : ℕ) (z : ℂ) =>
    z ^ (-((n : ℂ) + a))) fun n => ?_).congr' ?_).congr_coeff ?_
  · filter_upwards [hev] with z hz
    have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith [hz.1]
    rw [cpow_mul_exp_mul_I hz0 (by linarith [(abs_lt.mp hz.2.2).1, Real.pi_pos])
      (by linarith [(abs_lt.mp hz.2.2).2, Real.pi_pos])]
    ring
  · filter_upwards [hev] with z hz
    rw [Function.comp_apply, Pi.smul_apply, smul_eq_mul, kummerU_eq_tricomiRotated ha hα hz.2.1,
      tricomiRotated, ← integral_const_mul (exp (α * I))]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [tricomiKernel, hF, smul_eq_mul, hω]
    ring_nf
  · funext n
    have hG : Gamma (a + n) / Gamma a = poch a n := Gamma_add_nat_div_Gamma_eq (n := n) a ha'
    have hG0 : Gamma a ≠ 0 := Complex.Gamma_ne_zero ha'
    simp only [Pi.smul_apply, smul_eq_mul, hA, tricomiCoeff]
    rw [show b - a - 1 = -(a - b + 1) by ring, ring_choose_neg_eq_poch,
      show (n : ℂ) + a = a + n by ring, ← hG]
    have he : exp (-(α * I * (a + n))) * exp (α * I * (a + n)) = 1 := by
      rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
    field_simp
    linear_combination (Gamma (a + n) * poch (a - b + 1) n / n.factorial) * he

/-- **Tricomi's expansion in rotated sectors** (DLMF 13.7.3, Temme §7.2): for all complex `a, b`,
`|α| < π/2` and `δ > 0`, as `z → ∞` with `δ |z| ≤ re (z e^{iα})`,
`U(a,b,z) ~ ∑ (-1)^s (a)_s (a-b+1)_s / s! · z^{-a-s}`. Together these sectors cover
`|arg z| ≤ π - ε` for every `ε > 0`. -/
theorem hasAsymptoticExpansion_kummerU_rotSector (a b : ℂ) {δ α : ℝ} (hδ : 0 < δ)
    (hα : |α| < π / 2) :
    HasAsymptoticExpansion (rotSectorAtTop δ α) (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + a)))
      (tricomiCoeff a b) (fun z => kummerU a b z) := by
  have hl : ∀ᶠ z in rotSectorAtTop δ α, 1 ≤ ‖z‖ :=
    (eventually_rotSectorAtTop hδ hα).mono fun z hz => hz.1
  suffices h : ∀ m : ℕ, ∀ a b : ℂ, 0 < (a + m).re →
      HasAsymptoticExpansion (rotSectorAtTop δ α) (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + a)))
        (tricomiCoeff a b) (fun z => kummerU a b z) by
    obtain ⟨m, hm⟩ := exists_nat_gt (-a.re)
    exact h m a b (by simp; linarith)
  intro m
  induction m with
  | zero =>
    intro a b ha
    exact hasAsymptoticExpansion_kummerU_rotSector_of_re_pos (by simpa using ha) hδ hα
  | succ m ih =>
    intro a b ha
    have h := hasAsymptoticExpansion_kummerU_sub_one_of_filter hl
      (ih (a + 1) (b + 1) (by simp at ha ⊢; linarith))
      (ih (a + 1) b (by simp at ha ⊢; linarith))
    simpa using h

end DLMF.Confluent
