/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.Trigonometric.InverseIdentities

/-!
# Exact trigonometric values and integral formulas

Exact algebraic tables, antiderivatives and conditionally convergent improper integrals.

Source references and common attribution are retained in
`DLMF.Elementary.Trigonometric`.
This module uses results of the Tau Ceti contributors; see also `CREDITS.md`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Polynomial

open scoped Real Topology Nat

namespace DLMF.Elementary

/-! ## Exact trigonometric tables -/

/-- The six real trigonometric functions in the order used by the exact-value tables. -/
def trigRealVector (θ : ℝ) : Fin 6→ℝ :=
  ![Real.sin θ,Real.cos θ,Real.tan θ,(Real.sin θ)⁻¹,(Real.cos θ)⁻¹,Real.cot θ]

/-- Signs of the six functions in quadrants I, II, III and IV. -/
def trigQuadrantSigns : Fin 4→Fin 6→ℝ :=
  ![![1,1,1,1,1,1],![1,-1,-1,1,-1,-1],![-1,-1,1,-1,-1,1],![-1,1,-1,-1,1,-1]]

/-- Sign of a positive real. -/
private lemma trigR4_sign_pos {x : ℝ} (h : 0 < x) : trigRealSign x = 1 := by
  simp [trigRealSign, h]

/-- Sign of a negative real. -/
private lemma trigR4_sign_neg {x : ℝ} (h : x < 0) : trigRealSign x = -1 := by
  simp [trigRealSign, h, not_lt.mpr h.le]

/-- DLMF 4.16.T1: trig quadrant signs. -/
@[dlmf 4.16.T1]
theorem trig_quadrant_signs (q : Fin 4) {θ : ℝ}
    (hθ : θ∈Ioo ((q:ℝ)*π/2) (((q:ℝ)+1)*π/2)) (j : Fin 6) :
    trigRealSign (trigRealVector θ j)=trigQuadrantSigns q j := by
  have hp := Real.pi_pos
  obtain ⟨h1, h2⟩ := hθ
  fin_cases q
  · simp at h1 h2
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    fin_cases j <;> simp [trigRealVector, trigQuadrantSigns, Real.tan_eq_sin_div_cos,
      Real.cot_eq_cos_div_sin, trigR4_sign_pos, hs, hc]
  · simp at h1 h2
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hc : Real.cos θ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
    fin_cases j <;> simp [trigRealVector, trigQuadrantSigns, Real.tan_eq_sin_div_cos,
      Real.cot_eq_cos_div_sin, trigR4_sign_pos, trigR4_sign_neg, hs, hc, div_neg_of_pos_of_neg,
      div_neg_of_neg_of_pos]
  · simp at h1 h2
    norm_num at h1 h2
    have hs : Real.sin θ < 0 := by
      have := Real.sin_pos_of_pos_of_lt_pi (x := θ - π) (by linarith) (by linarith)
      rw [Real.sin_sub_pi] at this; linarith
    have hc : Real.cos θ < 0 := by
      have := Real.cos_pos_of_mem_Ioo (x := θ - π) ⟨by linarith, by linarith⟩
      rw [Real.cos_sub_pi] at this; linarith
    fin_cases j <;> simp [trigRealVector, trigQuadrantSigns, Real.tan_eq_sin_div_cos,
      Real.cot_eq_cos_div_sin, trigR4_sign_pos, trigR4_sign_neg, hs, hc, div_pos_of_neg_of_neg]
  · simp at h1 h2
    norm_num at h1 h2
    have hs : Real.sin θ < 0 := by
      have := Real.sin_pos_of_pos_of_lt_pi (x := θ - π) (by linarith) (by linarith)
      rw [Real.sin_sub_pi] at this; linarith
    have hc : 0 < Real.cos θ := by
      have := Real.cos_pos_of_mem_Ioo (x := θ - 2*π) ⟨by linarith, by linarith⟩
      rwa [Real.cos_sub_two_pi] at this
    fin_cases j <;> simp [trigRealVector, trigQuadrantSigns, Real.tan_eq_sin_div_cos,
      Real.cot_eq_cos_div_sin, trigR4_sign_pos, trigR4_sign_neg, hs, hc, div_neg_of_pos_of_neg,
      div_neg_of_neg_of_pos]

/-- All quarter-period identities; reflection and the full period supply both signs in Table 4.16.2. -/
@[dlmf 4.16.T2]
theorem trig_quarter_period_table (θ : ℝ) (q : Fin 4) :
    trigRealVector (θ+(q:ℝ)*π/2)=
    (![trigRealVector θ,
      ![Real.cos θ,-Real.sin θ,-Real.cot θ,(Real.cos θ)⁻¹,-(Real.sin θ)⁻¹,-Real.tan θ],
      ![-Real.sin θ,-Real.cos θ,Real.tan θ,-(Real.sin θ)⁻¹,-(Real.cos θ)⁻¹,Real.cot θ],
      ![-Real.cos θ,Real.sin θ,-Real.cot θ,-(Real.cos θ)⁻¹,(Real.sin θ)⁻¹,-Real.tan θ]] : Fin 4→Fin 6→ℝ) q := by
  have hs3 : Real.sin (3*Real.pi/2)= -1 := by
    rw [show (3:ℝ)*Real.pi/2=Real.pi+Real.pi/2 by ring,Real.sin_add]
    norm_num
  have hc3 : Real.cos (3*Real.pi/2)=0 := by
    rw [show (3:ℝ)*Real.pi/2=Real.pi+Real.pi/2 by ring,Real.cos_add]
    norm_num
  fin_cases q <;> ext j <;> fin_cases j <;>
    norm_num [trigRealVector,Real.tan_eq_sin_div_cos,Real.cot_eq_cos_div_sin,
      Real.sin_add,Real.cos_add,hs3,hc3,neg_div,div_neg]

/-- Algebraic interrelations; rows are output functions, columns are the known function. -/
def trigInterrelationTable (a : ℝ) : Fin 6→Fin 6→ℝ :=
  ![![a,Real.sqrt (1-a^2),a/Real.sqrt (1+a^2),a⁻¹,Real.sqrt (a^2-1)/a,(Real.sqrt (1+a^2))⁻¹],
    ![Real.sqrt (1-a^2),a,(Real.sqrt (1+a^2))⁻¹,Real.sqrt (a^2-1)/a,a⁻¹,a/Real.sqrt (1+a^2)],
    ![a/Real.sqrt (1-a^2),Real.sqrt (1-a^2)/a,a,(Real.sqrt (a^2-1))⁻¹,Real.sqrt (a^2-1),a⁻¹],
    ![a⁻¹,(Real.sqrt (1-a^2))⁻¹,Real.sqrt (1+a^2)/a,a,a/Real.sqrt (a^2-1),Real.sqrt (1+a^2)],
    ![(Real.sqrt (1-a^2))⁻¹,a⁻¹,Real.sqrt (1+a^2),a/Real.sqrt (a^2-1),a,Real.sqrt (1+a^2)/a],
    ![Real.sqrt (1-a^2)/a,a/Real.sqrt (1-a^2),a⁻¹,Real.sqrt (a^2-1),(Real.sqrt (a^2-1))⁻¹,a]]

/-- Every cell of the interrelation table, with its nonnegative finite principal-root convention. -/
@[dlmf 4.16.T3]
theorem trig_interrelation_table {θ : ℝ} (hs : 0<Real.sin θ) (hc : 0<Real.cos θ) (i j : Fin 6) :
    trigRealVector θ i=trigInterrelationTable (trigRealVector θ j) i j := by
  have key : trigRealVector θ = ![Real.sin θ, Real.cos θ, Real.sin θ / Real.cos θ,
      (Real.sin θ)⁻¹, (Real.cos θ)⁻¹, Real.cos θ / Real.sin θ] := by
    ext k; fin_cases k <;> simp [trigRealVector, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin]
  have hsc := Real.sin_sq_add_cos_sq θ
  rw [key]
  generalize Real.sin θ = s at hs hsc ⊢
  generalize Real.cos θ = c at hc hsc ⊢
  have hs0 : s ≠ 0 := hs.ne'
  have hc0 : c ≠ 0 := hc.ne'
  have f1 : Real.sqrt (1 - s^2) = c := by
    rw [show 1 - s^2 = c^2 by linarith, Real.sqrt_sq hc.le]
  have f2 : Real.sqrt (1 - c^2) = s := by
    rw [show 1 - c^2 = s^2 by linarith, Real.sqrt_sq hs.le]
  have f3 : Real.sqrt (1 + (s/c)^2) = c⁻¹ := by
    rw [show 1 + (s/c)^2 = (c⁻¹)^2 by field_simp; linarith, Real.sqrt_sq (inv_pos.mpr hc).le]
  have f4 : Real.sqrt (1 + (c/s)^2) = s⁻¹ := by
    rw [show 1 + (c/s)^2 = (s⁻¹)^2 by field_simp; linarith, Real.sqrt_sq (inv_pos.mpr hs).le]
  have f5 : Real.sqrt ((s⁻¹)^2 - 1) = c/s := by
    rw [show (s⁻¹)^2 - 1 = (c/s)^2 by field_simp; linarith, Real.sqrt_sq (div_pos hc hs).le]
  have f6 : Real.sqrt ((c⁻¹)^2 - 1) = s/c := by
    rw [show (c⁻¹)^2 - 1 = (s/c)^2 by field_simp; linarith, Real.sqrt_sq (div_pos hs hc).le]
  fin_cases i <;> fin_cases j <;> simp [trigInterrelationTable, f1, f2, f3, f4, f5, f6] <;>
    field_simp <;> grind

/-- Exact values at all multiples of pi/12 from zero to pi; pole cells contain placeholders. -/
def trigTwelfthTable : Fin 13→Fin 6→ℝ :=
  let r := Real.sqrt 2
  let t := Real.sqrt 3
  ![![0,1,0,0,1,0],
    ![r*(t-1)/4,r*(t+1)/4,2-t,r*(t+1),r*(t-1),2+t],
    ![1/2,t/2,t/3,2,2*t/3,t],
    ![r/2,r/2,1,r,r,1],
    ![t/2,1/2,t,2*t/3,2,t/3],
    ![r*(t+1)/4,r*(t-1)/4,2+t,r*(t-1),r*(t+1),2-t],
    ![1,0,0,1,0,0],
    ![r*(t+1)/4,-r*(t-1)/4,-(2+t),r*(t-1),-r*(t+1),-(2-t)],
    ![t/2,-1/2,-t,2*t/3,-2,-t/3],
    ![r/2,-r/2,-1,r,-r,-1],
    ![1/2,-t/2,-t/3,2,-2*t/3,-t],
    ![r*(t-1)/4,-r*(t+1)/4,-(2-t),r*(t+1),-r*(t-1),-(2+t)],
    ![0,-1,0,0,-1,0]]

/-- Pole cells of the exact trigonometric value table; they are not finite values. -/
def trigTwelfthPole (q : Fin 13) (j : Fin 6) : Prop :=
  ((q=0 ∨ q=12) ∧ (j=3 ∨ j=5)) ∨ (q=6 ∧ (j=2 ∨ j=4))

/-- Exact sine and cosine at `π/12`. -/
lemma trigR4_sin_cos_pi_div_twelve :
    Real.sin (π/12) = Real.sqrt 2 * (Real.sqrt 3 - 1) / 4 ∧
    Real.cos (π/12) = Real.sqrt 2 * (Real.sqrt 3 + 1) / 4 := by
  have h : π/12 = π/3 - π/4 := by ring
  rw [h, Real.sin_sub, Real.cos_sub, Real.sin_pi_div_three, Real.cos_pi_div_three,
    Real.sin_pi_div_four, Real.cos_pi_div_four]
  constructor <;> ring

/-- DLMF 4.17.T1: trig twelfth exact values. -/
@[dlmf 4.17.T1]
theorem trig_twelfth_exact_values (q : Fin 13) (j : Fin 6) (h : ¬trigTwelfthPole q j) :
    trigRealVector ((q:ℝ)*π/12) j=trigTwelfthTable q j := by
  obtain ⟨s1, c1⟩ := trigR4_sin_cos_pi_div_twelve
  have hr : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ht : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 < Real.sqrt 2 := by positivity
  have ht1 : 1 < Real.sqrt 3 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have key : ∀ θ s c : ℝ, Real.sin θ = s → Real.cos θ = c →
      trigRealVector θ = ![s, c, s/c, s⁻¹, c⁻¹, c/s] := by
    intro θ s c hs hc
    ext k; fin_cases k <;> simp [trigRealVector, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin, hs, hc]
  fin_cases q
  · rw [key _ 0 1 (by simp) (by simp)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢
  · rw [key _ _ _ (by simpa using s1) (by simpa using c1)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢ <;> grind
  · have hs : Real.sin (2*π/12) = 1/2 := by rw [show (2:ℝ)*π/12 = π/6 by ring, Real.sin_pi_div_six]
    have hc : Real.cos (2*π/12) = Real.sqrt 3/2 := by rw [show (2:ℝ)*π/12 = π/6 by ring, Real.cos_pi_div_six]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢ <;> grind
  · have hs : Real.sin (3*π/12) = Real.sqrt 2/2 := by rw [show (3:ℝ)*π/12 = π/4 by ring, Real.sin_pi_div_four]
    have hc : Real.cos (3*π/12) = Real.sqrt 2/2 := by rw [show (3:ℝ)*π/12 = π/4 by ring, Real.cos_pi_div_four]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢
  · have hs : Real.sin (4*π/12) = Real.sqrt 3/2 := by rw [show (4:ℝ)*π/12 = π/3 by ring, Real.sin_pi_div_three]
    have hc : Real.cos (4*π/12) = 1/2 := by rw [show (4:ℝ)*π/12 = π/3 by ring, Real.cos_pi_div_three]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢ <;> grind
  · have hs : Real.sin (5*π/12) = Real.sqrt 2 * (Real.sqrt 3 + 1) / 4 := by
      rw [show (5:ℝ)*π/12 = π/2 - π/12 by ring, Real.sin_pi_div_two_sub, c1]
    have hc : Real.cos (5*π/12) = Real.sqrt 2 * (Real.sqrt 3 - 1) / 4 := by
      rw [show (5:ℝ)*π/12 = π/2 - π/12 by ring, Real.cos_pi_div_two_sub, s1]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢ <;> grind
  · have hs : Real.sin (6*π/12) = 1 := by rw [show (6:ℝ)*π/12 = π/2 by ring, Real.sin_pi_div_two]
    have hc : Real.cos (6*π/12) = 0 := by rw [show (6:ℝ)*π/12 = π/2 by ring, Real.cos_pi_div_two]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢
  · have hs : Real.sin (7*π/12) = Real.sqrt 2 * (Real.sqrt 3 + 1) / 4 := by
      rw [show (7:ℝ)*π/12 = π - (π/2 - π/12) by ring, Real.sin_pi_sub, Real.sin_pi_div_two_sub, c1]
    have hc : Real.cos (7*π/12) = -(Real.sqrt 2 * (Real.sqrt 3 - 1) / 4) := by
      rw [show (7:ℝ)*π/12 = π - (π/2 - π/12) by ring, Real.cos_pi_sub, Real.cos_pi_div_two_sub, s1]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢ <;> grind
  · have hs : Real.sin (8*π/12) = Real.sqrt 3/2 := by
      rw [show (8:ℝ)*π/12 = π - (π/3) by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
    have hc : Real.cos (8*π/12) = -(1/2) := by
      rw [show (8:ℝ)*π/12 = π - (π/3) by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢ <;> grind
  · have hs : Real.sin (9*π/12) = Real.sqrt 2/2 := by
      rw [show (9:ℝ)*π/12 = π - (π/4) by ring, Real.sin_pi_sub, Real.sin_pi_div_four]
    have hc : Real.cos (9*π/12) = -(Real.sqrt 2/2) := by
      rw [show (9:ℝ)*π/12 = π - (π/4) by ring, Real.cos_pi_sub, Real.cos_pi_div_four]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢ <;> grind
  · have hs : Real.sin (10*π/12) = 1/2 := by
      rw [show (10:ℝ)*π/12 = π - (π/6) by ring, Real.sin_pi_sub, Real.sin_pi_div_six]
    have hc : Real.cos (10*π/12) = -(Real.sqrt 3/2) := by
      rw [show (10:ℝ)*π/12 = π - (π/6) by ring, Real.cos_pi_sub, Real.cos_pi_div_six]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢ <;> grind
  · have hs : Real.sin (11*π/12) = Real.sqrt 2 * (Real.sqrt 3 - 1) / 4 := by
      rw [show (11:ℝ)*π/12 = π - (π/12) by ring, Real.sin_pi_sub, s1]
    have hc : Real.cos (11*π/12) = -(Real.sqrt 2 * (Real.sqrt 3 + 1) / 4) := by
      rw [show (11:ℝ)*π/12 = π - (π/12) by ring, Real.cos_pi_sub, c1]
    rw [key _ _ _ (by simpa using hs) (by simpa using hc)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢ <;> grind
  · rw [key _ 0 (-1) (by simp) (by simp)]
    fin_cases j <;> simp [trigTwelfthTable, trigTwelfthPole] at h ⊢

/-- Real reciprocal blow-up at a simple zero. -/
lemma trigR4_real_pole {g h : ℝ → ℝ} {a : ℝ} {g' : ℝ} (hg : HasDerivAt g g' a) (hg' : g' ≠ 0)
    (hga : g a = 0) (hh : ContinuousAt h a) (hha : h a ≠ 0) :
    Tendsto (fun θ => |h θ * (g θ)⁻¹|) (𝓝[≠] a) atTop := by
  have hne : ∀ᶠ θ in 𝓝[≠] a, g θ ≠ 0 := by simpa [hga] using hg.eventually_ne hg'
  have h0 : Tendsto (fun θ => |g θ|) (𝓝[≠] a) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (hg.continuousAt.abs).tendsto.mono_left (nhdsWithin_le_nhds (s := {a}ᶜ))
      simpa [hga] using this
    · filter_upwards [hne] with θ hθ using abs_pos.mpr hθ
  have hinv := tendsto_inv_nhdsGT_zero.comp h0
  have hn : Tendsto (fun θ => |h θ|) (𝓝[≠] a) (𝓝 |h a|) :=
    (hh.abs).tendsto.mono_left nhdsWithin_le_nhds
  have := hn.pos_mul_atTop (abs_pos.mpr hha) hinv
  refine this.congr' (Eventually.of_forall fun θ => ?_)
  simp [abs_mul, abs_inv]

/-- DLMF 4.17.T1: trig twelfth poles. -/
@[dlmf 4.17.T1]
theorem trig_twelfth_poles (q : Fin 13) (j : Fin 6) (h : trigTwelfthPole q j) :
    Tendsto (fun θ : ℝ => |trigRealVector θ j|) (𝓝[≠] ((q:ℝ)*π/12)) atTop := by
  have hsin : ∀ a : ℝ, Real.sin a = 0 → Real.cos a ≠ 0 →
      Tendsto (fun θ : ℝ => |1 * (Real.sin θ)⁻¹|) (𝓝[≠] a) atTop ∧
      Tendsto (fun θ : ℝ => |Real.cos θ * (Real.sin θ)⁻¹|) (𝓝[≠] a) atTop := fun a h0 hc =>
    ⟨trigR4_real_pole (Real.hasDerivAt_sin a) hc h0 continuousAt_const one_ne_zero,
     trigR4_real_pole (Real.hasDerivAt_sin a) hc h0 Real.continuous_cos.continuousAt hc⟩
  have hcos : ∀ a : ℝ, Real.cos a = 0 → Real.sin a ≠ 0 →
      Tendsto (fun θ : ℝ => |1 * (Real.cos θ)⁻¹|) (𝓝[≠] a) atTop ∧
      Tendsto (fun θ : ℝ => |Real.sin θ * (Real.cos θ)⁻¹|) (𝓝[≠] a) atTop := fun a h0 hs =>
    ⟨trigR4_real_pole (Real.hasDerivAt_cos a) (neg_ne_zero.mpr hs) h0 continuousAt_const one_ne_zero,
     trigR4_real_pole (Real.hasDerivAt_cos a) (neg_ne_zero.mpr hs) h0 Real.continuous_sin.continuousAt hs⟩
  simp only [trigTwelfthPole] at h
  rcases h with ⟨hq | hq, hj | hj⟩ | ⟨hq, hj | hj⟩ <;> subst hq <;> subst hj
  · simpa [trigRealVector] using (hsin 0 (by simp) (by simp)).1
  · simpa [trigRealVector, Real.cot_eq_cos_div_sin, div_eq_mul_inv] using (hsin 0 (by simp) (by simp)).2
  · simpa [trigRealVector] using (hsin π (by simp) (by simp)).1
  · have e : ((12:Fin 13):ℝ)*π/12 = π := by norm_num
    rw [e]
    simpa [trigRealVector, Real.cot_eq_cos_div_sin, div_eq_mul_inv] using (hsin π (by simp) (by simp)).2
  · have e : ((6:Fin 13):ℝ)*π/12 = π/2 := by norm_num; ring
    rw [e]
    simpa [trigRealVector, Real.tan_eq_sin_div_cos, div_eq_mul_inv] using (hcos (π/2) (by simp) (by simp)).2
  · have e : ((6:Fin 13):ℝ)*π/12 = π/2 := by norm_num; ring
    rw [e]
    simpa [trigRealVector] using (hcos (π/2) (by simp) (by simp)).1

/-- Real inverse functions where the table specifies finite real values. -/
def inverseTrigRealVector (x : ℝ) : Fin 6→ℝ :=
  ![Real.arcsin x,Real.arccos x,Real.arctan x,Real.arcsin x⁻¹,Real.arccos x⁻¹,Real.arctan x⁻¹]

/-- DLMF 4.23.T1: inverse trig exact table. -/
@[dlmf 4.23.T1]
theorem inverse_trig_exact_table (q : Fin 3) (j : Fin 6) (h : q≠1 ∨ (j:ℕ)<3) :
    inverseTrigRealVector ((q:ℝ)-1) j=
      (![![-π/2,π,-π/4,-π/2,π,-π/4],![0,π/2,0,0,0,0],![π/2,0,π/4,π/2,0,π/4]] : Fin 3→Fin 6→ℝ) q j := by
  fin_cases q <;> fin_cases j <;>
    norm_num [inverseTrigRealVector,Real.arcsin_neg,Real.arccos_neg,Real.arctan_neg,neg_div] at *

/-- DLMF 4.23.T1: inverse reciprocal limits. -/
@[dlmf 4.23.T1]
theorem inverse_reciprocal_limits (positive : Bool) :
    Tendsto (fun x : ℝ => Real.arcsin x⁻¹) (if positive then atTop else atBot) (𝓝 0) ∧
    Tendsto (fun x : ℝ => Real.arccos x⁻¹) (if positive then atTop else atBot) (𝓝 (π/2)) ∧
    Tendsto (fun x : ℝ => Real.arctan x⁻¹) (if positive then atTop else atBot) (𝓝 0) := by
  have hi : Tendsto (fun x : ℝ => x⁻¹) (if positive then atTop else atBot) (𝓝 0) := by
    cases positive
    · exact tendsto_inv_atBot_zero
    · exact tendsto_inv_atTop_zero
  exact ⟨by simpa [Function.comp_def] using (Real.continuous_arcsin.tendsto 0).comp hi,
    by simpa [Function.comp_def] using (Real.continuous_arccos.tendsto 0).comp hi,
    by simpa [Function.comp_def] using (Real.continuous_arctan.tendsto 0).comp hi⟩

/-- DLMF 4.23.T1: arccot zero bank limits. -/
@[dlmf 4.23.T1]
theorem arccot_zero_bank_limits :
    Tendsto (fun x : ℝ => Real.arctan x⁻¹) (𝓝[>] 0) (𝓝 (π/2)) ∧
    Tendsto (fun x : ℝ => Real.arctan x⁻¹) (𝓝[<] 0) (𝓝 (-π/2)) := by
  constructor
  · have h := (Real.continuous_arctan.continuousAt (x:=0)).const_sub (Real.pi/2)
    have heq : (fun x : ℝ => Real.arctan x⁻¹)=ᶠ[𝓝[>] 0]
        (fun x => Real.pi/2-Real.arctan x) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact Real.arctan_inv_of_pos hx
    simpa using (h.mono_left nhdsWithin_le_nhds).congr' heq.symm
  · have h := (Real.continuous_arctan.continuousAt (x:=0)).const_sub (-Real.pi/2)
    have heq : (fun x : ℝ => Real.arctan x⁻¹)=ᶠ[𝓝[<] 0]
        (fun x => -Real.pi/2-Real.arctan x) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      simpa only [neg_div] using Real.arctan_inv_of_neg hx
    simpa using (h.mono_left nhdsWithin_le_nhds).congr' heq.symm

/-- The prose inverse secant/cotangent interrelation, with positive real finite principal roots. -/
@[dlmf 4.23.vii]
theorem arcsec_arccot_interrelation {a : ℝ} (ha : 1<a) :
    Real.arccos a⁻¹=Real.arctan (Real.sqrt (a^2-1)) := by
  rw [Real.arccos_eq_arctan (inv_pos.mpr (lt_trans zero_lt_one ha)),trig_sqrt_inverse ha]
  congr 1
  field_simp

/-! ## Antiderivatives and conditionally convergent improper integrals -/

/-- DLMF 4.26.E3: hasDerivAt neg log cos. -/
@[dlmf 4.26.E3]
theorem hasDerivAt_neg_log_cos {x : ℝ} (hx : |x|<π/2) : HasDerivAt (fun x : ℝ => -Real.log (Real.cos x)) (Real.tan x) x := by
  have hc : Real.cos x≠0 := (Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)).ne'
  convert ((Real.hasDerivAt_cos x).log hc).neg using 1
  simp only [Real.tan_eq_sin_div_cos]
  ring

/-- DLMF 4.26.E4: hasDerivAt log tan half. -/
@[dlmf 4.26.E4]
theorem hasDerivAt_log_tan_half {x : ℝ} (hx : x∈Ioo 0 π) : HasDerivAt (fun x : ℝ => Real.log (Real.tan (x/2))) ((Real.sin x)⁻¹) x := by
  have hhalf : x/2∈Ioo (-(π/2)) (π/2) := ⟨by linarith [Real.pi_pos,hx.1],by linarith [hx.2]⟩
  have hc : Real.cos (x/2)≠0 := (Real.cos_pos_of_mem_Ioo hhalf).ne'
  have hs : Real.sin (x/2)≠0 := (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2,Real.pi_pos])).ne'
  have ht : Real.tan (x/2)≠0 := by simpa only [Real.tan_eq_sin_div_cos] using div_ne_zero hs hc
  have hd0 : HasDerivAt (fun t:ℝ=>Real.tan (t/2)) (1/Real.cos (x/2)^2*(1/2)) x := by
    exact (Real.hasDerivAt_tan (x:=x/2) hc).comp x ((hasDerivAt_id x).div_const (2:ℝ))
  have hd:=hd0.log ht
  convert hd using 1
  rw [Real.tan_eq_sin_div_cos]
  have hsin : Real.sin x=2*Real.sin (x/2)*Real.cos (x/2) := by
    rw [← Real.sin_two_mul,show (2:ℝ)*(x/2)=x by ring]
  rw [hsin]
  field_simp

/-- DLMF 4.26.E5: hasDerivAt inverse gudermannian. -/
@[dlmf 4.26.E5]
theorem hasDerivAt_inverse_gudermannian {x : ℝ} (hx : |x|<π/2) : HasDerivAt (inverseGudermannian) ((Real.cos x)⁻¹) x := by
  have hcos : ∀t∈uIcc (0:ℝ) x,Real.cos t≠0 := by
    intro t ht
    apply (Real.cos_pos_of_mem_Ioo _).ne'
    rcases le_total 0 x with h|h
    · rw [uIcc_of_le h] at ht
      exact ⟨by linarith [ht.1,Real.pi_pos],by linarith [ht.2,(abs_lt.mp hx).2]⟩
    · rw [uIcc_of_ge h] at ht
      exact ⟨by linarith [ht.1,(abs_lt.mp hx).1],by linarith [ht.2,Real.pi_pos]⟩
  have hcont : ContinuousOn (fun t:ℝ=>(Real.cos t)⁻¹) (uIcc 0 x) := Real.continuous_cos.continuousOn.inv₀ hcos
  have hxcos : Real.cos x≠0 := (Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)).ne'
  apply intervalIntegral.integral_hasDerivAt_right hcont.intervalIntegrable
  · exact Real.continuous_cos.measurable.inv.aestronglyMeasurable.stronglyMeasurableAtFilter
  · exact Real.continuous_cos.continuousAt.inv₀ hxcos

/-- DLMF 4.26.E6: hasDerivAt log sin. -/
@[dlmf 4.26.E6]
theorem hasDerivAt_log_sin {x : ℝ} (hx : x∈Ioo 0 π) : HasDerivAt (fun x : ℝ => Real.log (Real.sin x)) (Real.cot x) x := by
  have hs : Real.sin x≠0 := (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2).ne'
  simpa only [Real.cot_eq_cos_div_sin] using (Real.hasDerivAt_sin x).log hs

/-- The exponential-trigonometric primitive, valid for complex parameters when its denominator is nonzero. -/
@[dlmf 4.26.E7]
theorem hasDerivAt_exp_sin_antiderivative {a b : ℂ} (h : a^2+b^2≠0) (z : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (a*z)/(a^2+b^2)*(a*Complex.sin (b*z)-b*Complex.cos (b*z)))
      (Complex.exp (a*z)*Complex.sin (b*z)) z := by
  have hd := ((((hasDerivAt_id z).const_mul a).cexp.div_const (a^2+b^2)).mul
    ((((hasDerivAt_id z).const_mul b).csin.const_mul a).sub
      (((hasDerivAt_id z).const_mul b).ccos.const_mul b)))
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    field_simp
    ring

/-- The exponential-trigonometric primitive, valid for complex parameters when its denominator is nonzero. -/
@[dlmf 4.26.E8]
theorem hasDerivAt_exp_cos_antiderivative {a b : ℂ} (h : a^2+b^2≠0) (z : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (a*z)/(a^2+b^2)*(a*Complex.cos (b*z)+b*Complex.sin (b*z)))
      (Complex.exp (a*z)*Complex.cos (b*z)) z := by
  have hd := ((((hasDerivAt_id z).const_mul a).cexp.div_const (a^2+b^2)).mul
    ((((hasDerivAt_id z).const_mul b).ccos.const_mul a).add
      (((hasDerivAt_id z).const_mul b).csin.const_mul b)))
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    field_simp
    ring

/-- Integer sine orthogonality requires both m not equal n and m not equal -n. -/
@[dlmf 4.26.E9]
theorem integral_sin_integer_orthogonal (m n : ℤ) (hne : m≠n) (hneg : m≠ -n) :
    (∫ t in (0:ℝ)..π,Real.sin ((m:ℝ)*t)*Real.sin ((n:ℝ)*t))=0 := by
  have hp : m+n≠0 := by omega
  have hm : m-n≠0 := by omega
  have hc (k : ℤ) : IntervalIntegrable (fun t : ℝ => Real.cos ((k:ℝ)*t)) volume 0 Real.pi :=
    (by fun_prop : Continuous (fun t : ℝ => Real.cos ((k:ℝ)*t))).intervalIntegrable _ _
  have he : ∀ t : ℝ,Real.sin ((m:ℝ)*t)*Real.sin ((n:ℝ)*t)=
      (Real.cos (((m-n:ℤ):ℝ)*t)-Real.cos (((m+n:ℤ):ℝ)*t))/2 := by
    intro t
    push_cast
    rw [sub_mul,add_mul,Real.cos_sub,Real.cos_add]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_div,intervalIntegral.integral_sub (hc _) (hc _),
    TauCeti.integral_cos_int_mul,TauCeti.integral_cos_int_mul,if_neg hm,if_neg hp]
  norm_num

/-- Integer cosine orthogonality with the missing opposite-frequency exclusion. -/
@[dlmf 4.26.E10]
theorem integral_cos_integer_orthogonal (m n : ℤ) (hne : m≠n) (hneg : m≠ -n) :
    (∫ t in (0:ℝ)..π,Real.cos ((m:ℝ)*t)*Real.cos ((n:ℝ)*t))=0 := by
  have hp : m+n≠0 := by omega
  have hm : m-n≠0 := by omega
  have hc (k : ℤ) : IntervalIntegrable (fun t : ℝ => Real.cos ((k:ℝ)*t)) volume 0 Real.pi :=
    (by fun_prop : Continuous (fun t : ℝ => Real.cos ((k:ℝ)*t))).intervalIntegrable _ _
  have he : ∀ t : ℝ,Real.cos ((m:ℝ)*t)*Real.cos ((n:ℝ)*t)=
      (Real.cos (((m-n:ℤ):ℝ)*t)+Real.cos (((m+n:ℤ):ℝ)*t))/2 := by
    intro t
    push_cast
    rw [sub_mul,add_mul,Real.cos_sub,Real.cos_add]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_div,intervalIntegral.integral_add (hc _) (hc _),
    TauCeti.integral_cos_int_mul,TauCeti.integral_cos_int_mul,if_neg hm,if_neg hp]
  norm_num

/-- DLMF 4.26.E11: integral trig integer squares. -/
@[dlmf 4.26.E11]
theorem integral_trig_integer_squares {n : ℤ} (hn : n≠0) :
    (∫ t in (0:ℝ)..π,(Real.sin ((n:ℝ)*t))^2)=π/2 ∧
    (∫ t in (0:ℝ)..π,(Real.cos ((n:ℝ)*t))^2)=π/2 := by
  have hn' : (n:ℝ)≠0 := Int.cast_ne_zero.mpr hn
  constructor
  · have h := intervalIntegral.mul_integral_comp_mul_left
      (f:=fun x : ℝ => Real.sin x^2) (a:=(0:ℝ)) (b:=Real.pi) (n:ℝ)
    rw [integral_sin_sq,mul_zero,Real.sin_zero,Real.sin_int_mul_pi] at h
    apply mul_left_cancel₀ hn'
    convert h using 1 <;> ring
  · have h := intervalIntegral.mul_integral_comp_mul_left
      (f:=fun x : ℝ => Real.cos x^2) (a:=(0:ℝ)) (b:=Real.pi) (n:ℝ)
    rw [integral_cos_sq,mul_zero,Real.sin_zero,Real.sin_int_mul_pi] at h
    apply mul_left_cancel₀ hn'
    convert h using 1 <;> ring

/-- Dirichlet integral as an ordered improper limit, stronger real frequency version. -/
@[dlmf 4.26.E12]
theorem dirichlet_integral_scaled (m : ℝ) :
    Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R,Real.sin (m*t)/t) atTop
      (𝓝 (trigRealSign m*π/2)) := by
  rcases lt_trichotomy m 0 with h | h | h
  · have := (TauCeti.Contour.tendsto_integral_sin_mul_div_atTop (neg_pos.mpr h)).neg
    have hs : trigRealSign m = -1 := by simp [trigRealSign, h, not_lt.mpr h.le]
    rw [hs]
    convert this using 1
    · funext R
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [neg_mul, Real.sin_neg]; ring
    · ring_nf
  · subst h; simp [trigRealSign]
  · have hs : trigRealSign m = 1 := by simp [trigRealSign, h]
    rw [hs, one_mul]
    exact TauCeti.Contour.tendsto_integral_sin_mul_div_atTop h

/-- DLMF 4.26.E13: fresnel integrals elementary. -/
@[dlmf 4.26.E13]
theorem fresnel_integrals_elementary :
    Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R,Real.sin (t^2)) atTop (𝓝 (Real.sqrt (π/2)/2)) ∧
    Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R,Real.cos (t^2)) atTop (𝓝 (Real.sqrt (π/2)/2)) := by
  have hv : Real.Gamma (1 + 1 / ((2:ℕ):ℝ)) = Real.sqrt π / 2 := by
    rw [show (1:ℝ) + 1/((2:ℕ):ℝ) = 1/2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]; ring
  have he : Real.sqrt π / 2 * (Real.sqrt 2 / 2) = Real.sqrt (π/2)/2 := by
    rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 2)]
    have h2 : 0 < Real.sqrt 2 := by positivity
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hp : π / (2 * ((2:ℕ):ℝ)) = π/4 := by norm_num
  constructor
  · have := DLMF.Gamma.Gamma_sin_pow 2 le_rfl
    rwa [hv, hp, Real.sin_pi_div_four, he] at this
  · have := DLMF.Gamma.Gamma_cos_pow 2 le_rfl
    rwa [hv, hp, Real.cos_pi_div_four, he] at this

/-- DLMF 4.26.E14: hasDerivAt arcsin antiderivative. -/
@[dlmf 4.26.E14]
theorem hasDerivAt_arcsin_antiderivative {x : ℝ} (hx : |x|<1) : HasDerivAt (fun x : ℝ => x*Real.arcsin x+Real.sqrt (1-x^2)) (Real.arcsin x) x := by
  have hx1 : x≠1 := ne_of_lt (abs_lt.mp hx).2
  have hxm : x≠ -1 := ne_of_gt (abs_lt.mp hx).1
  have hs : 0<1-x^2 := by nlinarith [(abs_lt.mp hx).1,(abs_lt.mp hx).2]
  have hroot := Real.sq_sqrt hs.le
  have hroot0 : Real.sqrt (1-x^2)≠0 := (Real.sqrt_pos.mpr hs).ne'
  have hd := ((hasDerivAt_id x).mul (Real.hasDerivAt_arcsin hxm hx1)).add
    ((((hasDerivAt_id x).pow 2).const_sub 1).sqrt (ne_of_gt hs))
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul] <;> field_simp <;> nlinarith

/-- DLMF 4.26.E15: hasDerivAt arccos antiderivative. -/
@[dlmf 4.26.E15]
theorem hasDerivAt_arccos_antiderivative {x : ℝ} (hx : |x|<1) : HasDerivAt (fun x : ℝ => x*Real.arccos x-Real.sqrt (1-x^2)) (Real.arccos x) x := by
  have hx1 : x≠1 := ne_of_lt (abs_lt.mp hx).2
  have hxm : x≠ -1 := ne_of_gt (abs_lt.mp hx).1
  have hs : 0<1-x^2 := by nlinarith [(abs_lt.mp hx).1,(abs_lt.mp hx).2]
  have hroot := Real.sq_sqrt hs.le
  have hroot0 : Real.sqrt (1-x^2)≠0 := (Real.sqrt_pos.mpr hs).ne'
  have hd := ((hasDerivAt_id x).mul (Real.hasDerivAt_arccos hxm hx1)).sub
    ((((hasDerivAt_id x).pow 2).const_sub 1).sqrt (ne_of_gt hs))
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul] <;> field_simp <;> nlinarith

/-- DLMF 4.26.E16: hasDerivAt arctan antiderivative. -/
@[dlmf 4.26.E16]
theorem hasDerivAt_arctan_antiderivative {x : ℝ} : HasDerivAt (fun x : ℝ => x*Real.arctan x-Real.log (1+x^2)/2) (Real.arctan x) x := by
  have hlog : (1+x^2:ℝ)≠0 := by positivity
  have hd := ((hasDerivAt_id x).mul (Real.hasDerivAt_arctan x)).sub
    ((((hasDerivAt_id x).pow 2).const_add 1).log hlog |>.div_const 2)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    field_simp
    ring

/-- DLMF 4.26.E17: hasDerivAt arccsc antiderivative. -/
@[dlmf 4.26.E17]
theorem hasDerivAt_arccsc_antiderivative {x : ℝ} (hx : 1<x) : HasDerivAt (fun x : ℝ => x*Real.arcsin x⁻¹+Real.log (x+Real.sqrt (x^2-1))) (Real.arcsin x⁻¹) x := by
  have hx0 : 0<x := lt_trans zero_lt_one hx
  have hi : x⁻¹<1 := inv_lt_one_of_one_lt₀ hx
  have hip : 0<x⁻¹ := inv_pos.mpr hx0
  have hxm : x⁻¹≠ -1 := by linarith
  have hs : 0<x^2-1 := by nlinarith
  have hs0 : Real.sqrt (x^2-1)≠0 := (Real.sqrt_pos.mpr hs).ne'
  have hinv : HasDerivAt (fun t:ℝ=>Real.arcsin t⁻¹) ((Real.sqrt (1-x⁻¹^2))⁻¹ * (-1/x^2)) x := by
    simpa only [one_div,id_eq,Function.comp_def] using (Real.hasDerivAt_arcsin hxm hi.ne).comp x ((hasDerivAt_id x).inv hx0.ne')
  have hd := ((hasDerivAt_id x).mul hinv).add (Real.hasDerivAt_arcosh hx)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.add_apply]
    rw [trig_sqrt_inverse hx]
    field_simp
    ring

/-- DLMF 4.26.E18: hasDerivAt arcsec antiderivative. -/
@[dlmf 4.26.E18]
theorem hasDerivAt_arcsec_antiderivative {x : ℝ} (hx : 1<x) : HasDerivAt (fun x : ℝ => x*Real.arccos x⁻¹-Real.log (x+Real.sqrt (x^2-1))) (Real.arccos x⁻¹) x := by
  have hx0 : 0<x := lt_trans zero_lt_one hx
  have hi : x⁻¹<1 := inv_lt_one_of_one_lt₀ hx
  have hip : 0<x⁻¹ := inv_pos.mpr hx0
  have hxm : x⁻¹≠ -1 := by linarith
  have hs : 0<x^2-1 := by nlinarith
  have hs0 : Real.sqrt (x^2-1)≠0 := (Real.sqrt_pos.mpr hs).ne'
  have hinv : HasDerivAt (fun t:ℝ=>Real.arccos t⁻¹) (-(Real.sqrt (1-x⁻¹^2))⁻¹ * (-1/x^2)) x := by
    simpa only [one_div,id_eq,Function.comp_def] using (Real.hasDerivAt_arccos hxm hi.ne).comp x ((hasDerivAt_id x).inv hx0.ne')
  have hd := ((hasDerivAt_id x).mul hinv).sub (Real.hasDerivAt_arcosh hx)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply]
    rw [trig_sqrt_inverse hx]
    field_simp
    ring

/-- DLMF 4.26.E19: hasDerivAt arccot antiderivative. -/
@[dlmf 4.26.E19]
theorem hasDerivAt_arccot_antiderivative {x : ℝ} (hx : 0<x) : HasDerivAt (fun x : ℝ => x*Real.arctan x⁻¹+Real.log (1+x^2)/2) (Real.arctan x⁻¹) x := by
  have hx0 : x≠0 := hx.ne'
  have hlog : (1+x^2:ℝ)≠0 := by positivity
  have hd := ((hasDerivAt_id x).mul ((hasDerivAt_id x).inv hx0 |>.arctan)).add
    ((((hasDerivAt_id x).pow 2).const_add 1).log hlog |>.div_const 2)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.inv_apply,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    field_simp
    ring

/-- DLMF 4.26.E20: hasDerivAt mul arcsin antiderivative. -/
@[dlmf 4.26.E20]
theorem hasDerivAt_mul_arcsin_antiderivative {x : ℝ} (hx : |x|<1) : HasDerivAt (fun x : ℝ => (x^2/2-1/4)*Real.arcsin x+x/4*Real.sqrt (1-x^2)) (x*Real.arcsin x) x := by
  have hx1 : x≠1 := ne_of_lt (abs_lt.mp hx).2
  have hxm : x≠ -1 := ne_of_gt (abs_lt.mp hx).1
  have hs : 0<1-x^2 := by nlinarith [(abs_lt.mp hx).1,(abs_lt.mp hx).2]
  have hroot := Real.sq_sqrt hs.le
  have hroot0 : Real.sqrt (1-x^2)≠0 := (Real.sqrt_pos.mpr hs).ne'
  have hd := ((((hasDerivAt_id x).pow 2).div_const 2 |>.sub_const (1/4)).mul
    (Real.hasDerivAt_arcsin hxm hx1)).add
    (((hasDerivAt_id x).div_const 4).mul
      ((((hasDerivAt_id x).pow 2).const_sub 1).sqrt (ne_of_gt hs)))
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul] <;> field_simp <;> nlinarith

/-- DLMF 4.26.E21: hasDerivAt mul arccos antiderivative. -/
@[dlmf 4.26.E21]
theorem hasDerivAt_mul_arccos_antiderivative {x : ℝ} (hx : |x|<1) : HasDerivAt (fun x : ℝ => (x^2/2-1/4)*Real.arccos x-x/4*Real.sqrt (1-x^2)) (x*Real.arccos x) x := by
  have hx1 : x≠1 := ne_of_lt (abs_lt.mp hx).2
  have hxm : x≠ -1 := ne_of_gt (abs_lt.mp hx).1
  have hs : 0<1-x^2 := by nlinarith [(abs_lt.mp hx).1,(abs_lt.mp hx).2]
  have hroot := Real.sq_sqrt hs.le
  have hroot0 : Real.sqrt (1-x^2)≠0 := (Real.sqrt_pos.mpr hs).ne'
  have hd := ((((hasDerivAt_id x).pow 2).div_const 2 |>.sub_const (1/4)).mul
    (Real.hasDerivAt_arccos hxm hx1)).sub
    (((hasDerivAt_id x).div_const 4).mul
      ((((hasDerivAt_id x).pow 2).const_sub 1).sqrt (ne_of_gt hs)))
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul] <;> field_simp <;> nlinarith

/-- Complex antiderivatives use local continuous logarithm branches and exclude reciprocal poles. -/
@[dlmf 4.26.i]
theorem complex_trig_log_primitives {U : Set ℂ} (hU : IsOpen U) {L : ℂ→ℂ}
    (hL : AnalyticOnNhd ℂ L U) {z : ℂ} (hz : z∈U) :
    ((∀ w∈U,Complex.exp (L w)=Complex.cos w) → HasDerivAt (fun w => -L w) (Complex.tan z) z) ∧
    ((∀ w∈U,Complex.exp (L w)=Complex.sin w) → HasDerivAt L (Complex.cot z) z) ∧
    ((∀ w∈U,Complex.exp (L w)=sec w+Complex.tan w) →
      Complex.cos z≠0 → HasDerivAt L (sec z) z) := by
  have hdL:HasDerivAt L (deriv L z) z := (hL z hz).differentiableAt.hasDerivAt
  have hlog {f:ℂ→ℂ} {d:ℂ} (hf:HasDerivAt f d z)
      (he:∀w∈U,Complex.exp (L w)=f w) : HasDerivAt L (d/f z) z := by
    have heq:(fun w=>Complex.exp (L w))=ᶠ[𝓝 z] f := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact he w hw
    have hdexp:=hdL.cexp
    have hdeq:=hdexp.unique (hf.congr_of_eventuallyEq heq)
    have hf0:f z≠0 := by rw [← he z hz]; exact Complex.exp_ne_zero _
    convert hdL using 1
    rw [← hdeq,he z hz]
    field_simp
  refine ⟨?_,?_,?_⟩
  · intro he
    have hd:=(hlog (Complex.hasDerivAt_cos z) he).neg
    convert hd using 1
    simp [Complex.tan,neg_div]
  · intro he
    simpa only [Complex.cot] using hlog (Complex.hasDerivAt_sin z) he
  · intro he hc
    have hd:=hlog ((hasDerivAt_sec hc).add (Complex.hasDerivAt_tan hc)) he
    have hdEq:sec z*Complex.tan z+1/(Complex.cos z)^2=(sec z+Complex.tan z)*sec z := by
      rw [sec]
      ring
    rw [hdEq] at hd
    have he0:sec z+Complex.tan z≠0 := by rw [← he z hz]; exact Complex.exp_ne_zero _
    simpa only [Pi.add_apply,mul_div_cancel_left₀ (sec z) he0] using hd

/-- Real phase-amplitude reduction with its argument convention made explicit. -/
@[dlmf 4.21.E1_5]
theorem trig_phase_amplitude (A B : ℝ) (u : ℂ) :
    (A:ℂ)*Complex.cos u+B*Complex.sin u=(Real.sqrt (A^2+B^2):ℂ)*
      Complex.cos (u-(Complex.arg ((A:ℂ)+B*I):ℂ)) := by
  let z:ℂ:=(A:ℂ)+B*I
  have hn:Real.sqrt (A^2+B^2)=‖z‖ := by
    rw [Complex.norm_def]
    congr 1
    simp [z,Complex.normSq]
    ring
  have hc:(‖z‖:ℂ)*Complex.cos (Complex.arg z:ℂ)=(A:ℂ) := by
    rw [← Complex.ofReal_cos,← Complex.ofReal_mul,Complex.norm_mul_cos_arg]
    simp [z]
  have hs:(‖z‖:ℂ)*Complex.sin (Complex.arg z:ℂ)=(B:ℂ) := by
    rw [← Complex.ofReal_sin,← Complex.ofReal_mul,Complex.norm_mul_sin_arg]
    simp [z]
  rw [hn,Complex.cos_sub]
  linear_combination -Complex.cos u*hc -Complex.sin u*hs

/-- The two rectangular hyperbolas bounding Euler's transformed arctangent domain. -/
@[dlmf 4.24.E6]
theorem arctan_euler_boundary (z : ℂ) :
    (z^2).re= -(1/2:ℝ) ↔ z.re^2-z.im^2= -(1/2:ℝ) := by
  simp [Complex.mul_re,pow_two]

/-- No analytic inverse branch of sine or cosine crosses either finite branch point. -/
@[dlmf 4.23.i]
theorem inverse_sin_cos_branch_points (a : ℂ) (ha : a=1 ∨ a= -1) :
    ¬∃ U : Set ℂ,IsOpen U ∧ a∈U ∧ ∃ f : ℂ→ℂ,AnalyticOnNhd ℂ f U ∧
      ((∀ z∈U,Complex.sin (f z)=z) ∨ (∀ z∈U,Complex.cos (f z)=z)) := by
  rintro ⟨U,hU,haU,f,hf,hInv⟩
  have hdf:=(hf a haU).differentiableAt.hasDerivAt
  rcases hInv with hs|hc
  · have hzero:Complex.cos (f a)=0 := by
      apply sq_eq_zero_iff.mp
      rw [Complex.cos_sq',hs a haU]
      rcases ha with rfl|rfl <;> norm_num
    have hd:=(Complex.hasDerivAt_sin (f a)).comp a hdf
    rw [hzero,zero_mul] at hd
    have heq:id=ᶠ[𝓝 a] Complex.sin∘f := by
      filter_upwards [hU.mem_nhds haU] with z hz
      exact (hs z hz).symm
    have hcontra:=(hd.congr_of_eventuallyEq heq).unique (hasDerivAt_id a)
    norm_num at hcontra
  · have hzero:Complex.sin (f a)=0 := by
      apply sq_eq_zero_iff.mp
      rw [Complex.sin_sq,hc a haU]
      rcases ha with rfl|rfl <;> norm_num
    have hd:=(Complex.hasDerivAt_cos (f a)).comp a hdf
    rw [hzero,neg_zero,zero_mul] at hd
    have heq:id=ᶠ[𝓝 a] Complex.cos∘f := by
      filter_upwards [hU.mem_nhds haU] with z hz
      exact (hc z hz).symm
    have hcontra:=(hd.congr_of_eventuallyEq heq).unique (hasDerivAt_id a)
    norm_num at hcontra

/-- The logarithmic tangent branch points have no finite nonpolar inverse images. -/
@[dlmf 4.23.i]
theorem inverse_tan_cot_branch_points (a : ℂ) (ha : a=I ∨ a= -I) :
    arctanGeneral a=∅ ∧ arccotGeneral a=∅ := by
  have ha2:a^2= -1 := by rcases ha with rfl|rfl <;> simp
  constructor
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro w ⟨hc,ht⟩
    have hs:Complex.sin w=a*Complex.cos w := (div_eq_iff hc).mp ht
    have hp:=Complex.sin_sq_add_cos_sq w
    rw [hs,mul_pow,ha2] at hp
    ring_nf at hp
    norm_num at hp
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro w ⟨hs,ht⟩
    have hc:Complex.cos w=a*Complex.sin w := (div_eq_iff hs).mp ht
    have hp:=Complex.sin_sq_add_cos_sq w
    rw [hc,mul_pow,ha2] at hp
    ring_nf at hp
    norm_num at hp

/-- Reciprocal inverse sine/cosine branches have the same endpoint obstructions. -/
@[dlmf 4.23.i]
theorem inverse_reciprocal_branch_points (a : ℂ) (ha : a=1 ∨ a= -1) :
    ¬∃ U : Set ℂ,IsOpen U ∧ a∈U ∧ ∃ f : ℂ→ℂ,AnalyticOnNhd ℂ f U ∧
      ((∀ z∈U,Complex.sin (f z)≠0 ∧ csc (f z)=z) ∨
       (∀ z∈U,Complex.cos (f z)≠0 ∧ sec (f z)=z)) := by
  rintro ⟨U,hU,haU,f,hf,hInv⟩
  have hdf:=(hf a haU).differentiableAt.hasDerivAt
  have hai:a⁻¹=a := by rcases ha with rfl|rfl <;> norm_num
  rcases hInv with hs|hc
  · have hsval:Complex.sin (f a)=a := by
      simpa only [csc,inv_inv,hai] using congrArg Inv.inv (hs a haU).2
    have hzero:Complex.cos (f a)=0 := by
      apply sq_eq_zero_iff.mp
      rw [Complex.cos_sq',hsval]
      rcases ha with rfl|rfl <;> norm_num
    have hd:=(hasDerivAt_csc (hs a haU).1).comp a hdf
    have hcot:Complex.cot (f a)=0 := by simp [Complex.cot,hzero]
    rw [hcot,mul_zero,zero_mul] at hd
    have heq:id=ᶠ[𝓝 a] csc∘f := by
      filter_upwards [hU.mem_nhds haU] with z hz
      exact (hs z hz).2.symm
    have hcontra:=(hd.congr_of_eventuallyEq heq).unique (hasDerivAt_id a)
    norm_num at hcontra
  · have hcval:Complex.cos (f a)=a := by
      simpa only [sec,inv_inv,hai] using congrArg Inv.inv (hc a haU).2
    have hzero:Complex.sin (f a)=0 := by
      apply sq_eq_zero_iff.mp
      rw [Complex.sin_sq,hcval]
      rcases ha with rfl|rfl <;> norm_num
    have hd:=(hasDerivAt_sec (hc a haU).1).comp a hdf
    have htan:Complex.tan (f a)=0 := by simp [Complex.tan,hzero]
    rw [htan,mul_zero,zero_mul] at hd
    have heq:id=ᶠ[𝓝 a] sec∘f := by
      filter_upwards [hU.mem_nhds haU] with z hz
      exact (hc z hz).2.symm
    have hcontra:=(hd.congr_of_eventuallyEq heq).unique (hasDerivAt_id a)
    norm_num at hcontra

/-- Principal complex inverse-sine and cosine primitives on their common cut plane. -/
@[dlmf 4.26.i]
theorem complex_inverse_sin_cos_primitives {z : ℂ} (hz : z∈arcsinCutPlane) :
    HasDerivAt (fun w : ℂ => w*arcsinPrincipal w+Complex.sqrt (1-w^2)) (arcsinPrincipal z) z ∧
    HasDerivAt (fun w : ℂ => w*arccosPrincipal w-Complex.sqrt (1-w^2)) (arccosPrincipal z) z ∧
    HasDerivAt (fun w : ℂ => (w^2/2-1/4)*arcsinPrincipal w+w/4*Complex.sqrt (1-w^2))
      (z*arcsinPrincipal z) z ∧
    HasDerivAt (fun w : ℂ => (w^2/2-1/4)*arccosPrincipal w-w/4*Complex.sqrt (1-w^2))
      (z*arccosPrincipal z) z := by
  have hq:=trig_one_sub_sq_slit hz
  have hr:Complex.sqrt (1-z^2)≠0 := by
    intro h
    have hs:=trig_sqrt_sq (1-z^2)
    rw [h,zero_pow two_ne_zero] at hs
    exact (Complex.mem_slitPlane_iff_arg.mp hq).2 hs.symm
  have hS:HasDerivAt (fun w:ℂ=>Complex.sqrt (1-w^2)) (-z/Complex.sqrt (1-z^2)) z := by
    convert (trig_hasDerivAt_sqrt hq).comp z (((hasDerivAt_id z).pow 2).const_sub 1) using 1 <;>
      simp only [id_eq,Function.comp_def,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one] <;> ring
  have hA:=trig_hasDerivAt_arcsin hz
  have hC:=hasDerivAt_arccos_principal hz
  have hroot:=trig_sqrt_sq (1-z^2)
  refine ⟨?_,?_,?_,?_⟩
  · have hd:=((hasDerivAt_id z).mul hA).add hS
    convert hd using 1
    · rfl
    · dsimp only [id,Pi.mul_apply,Pi.add_apply]
      field_simp
      ring
  · have hd:=((hasDerivAt_id z).mul hC).sub hS
    convert hd using 1
    · rfl
    · dsimp only [id,Pi.mul_apply,Pi.sub_apply]
      field_simp
      ring
  · have hd:=((((hasDerivAt_id z).pow 2).div_const 2).sub_const (1/4)).mul hA |>.add
      (((hasDerivAt_id z).div_const 4).mul hS)
    convert hd using 1
    · rfl
    · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
      norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
      field_simp
      rw [hroot]
      ring
  · have hd:=((((hasDerivAt_id z).pow 2).div_const 2).sub_const (1/4)).mul hC |>.sub
      (((hasDerivAt_id z).div_const 4).mul hS)
    convert hd using 1
    · rfl
    · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
      norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
      field_simp
      rw [hroot]
      ring

/-- The complex arctangent primitive on its principal cut plane. -/
@[dlmf 4.26.i]
theorem complex_arctan_primitive {z : ℂ} (hz : z∈arctanCutPlane) :
    HasDerivAt (fun w : ℂ => w*Complex.arctan w-Complex.log (1+w^2)/2) (Complex.arctan z) z := by
  have hlog := (Complex.hasDerivAt_log (trig_one_add_sq_slit hz)).comp z
    (((hasDerivAt_id z).pow 2).const_add 1)
  have hd := ((hasDerivAt_id z).mul (trig_hasDerivAt_arctan hz)).sub (hlog.div_const 2)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.pow_apply]
    field_simp
    ring

/-- Reciprocal inverse primitives on the right component, using principal square roots and logs. -/
@[dlmf 4.26.i]
theorem complex_reciprocal_inverse_primitives {z : ℂ} (hz : z∈arccscCutPlane) (hr : 0<z.re) :
    HasDerivAt (fun w : ℂ => w*arccscPrincipal w+Complex.log (w+Complex.sqrt (w^2-1)))
      (arccscPrincipal z) z ∧
    HasDerivAt (fun w : ℂ => w*arcsecPrincipal w-Complex.log (w+Complex.sqrt (w^2-1)))
      (arcsecPrincipal z) z := by
  have hq : z^2-1 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases hy : z.im = 0
    · left
      have hv0 : (z⁻¹).im = 0 := by rw [Complex.inv_im, hy]; simp
      have hlt : |(z⁻¹).re| < 1 := hz.2.resolve_left (not_not.mpr hv0)
      have hNx : Complex.normSq z = z.re^2 := by rw [Complex.normSq_apply, hy]; ring
      have hux : (z⁻¹).re * z.re = 1 := by
        rw [Complex.inv_re, hNx]; field_simp
      have h1 : ((z⁻¹).re * z.re)^2 = 1 := by rw [hux]; norm_num
      simp only [Complex.sub_re, pow_two, Complex.mul_re, hy, Complex.one_re]
      nlinarith [abs_mul_abs_self (z⁻¹).re, abs_nonneg (z⁻¹).re, sq_nonneg z.re]
    · right
      simp only [Complex.sub_im, pow_two, Complex.mul_im, Complex.one_im]
      have : z.re*z.im ≠ 0 := mul_ne_zero hr.ne' hy
      intro h; apply this; linarith
  have hr0 : 0 ≤ (Complex.sqrt (z^2-1)).re := by
    rw [(trigR4_sqrt_re_im _).1]; exact Real.sqrt_nonneg _
  have hp : z + Complex.sqrt (z^2-1) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simp only [Complex.add_re]; linarith
  have hb0 : Complex.sqrt (z^2-1) ≠ 0 := by
    intro h
    have := trig_sqrt_sq (z^2-1); rw [h, zero_pow two_ne_zero] at this
    exact Complex.slitPlane_ne_zero hq this.symm
  have hp0 : z + Complex.sqrt (z^2-1) ≠ 0 := Complex.slitPlane_ne_zero hp
  have hS : HasDerivAt (fun w : ℂ => Complex.sqrt (w^2-1)) (z/Complex.sqrt (z^2-1)) z := by
    have hsq : HasDerivAt Complex.sqrt ((Complex.sqrt (z^2-1))⁻¹/2) (z^2-1) := by
      simpa only [Complex.sqrt,show (-1/2:ℂ)= -(2⁻¹:ℂ) by norm_num,Complex.cpow_neg] using
        Complex.hasDerivAt_sqrt hq
    have h1 := hsq.comp z (((hasDerivAt_id z).pow 2).sub_const 1)
    convert h1 using 1
    · funext w; rfl
    · simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      field_simp
  have hL := (Complex.hasDerivAt_log hp).comp z ((hasDerivAt_id z).add hS)
  have hA := hasDerivAt_arccsc_principal hz hr.ne'
  have hzero : z ≠ 0 := hz.1
  simp only [hr, ite_true] at hA
  have hroot := trig_sqrt_sq (z^2-1)
  constructor
  · have hd := ((hasDerivAt_id z).mul hA).add hL
    convert hd using 1
    · rfl
    · simp only [id_eq]
      field_simp
      ring
  · have hA' : HasDerivAt arcsecPrincipal (1/(z*Complex.sqrt (z^2-1))) z := by
      have h := hA.const_sub ((π:ℂ)/2)
      convert h using 1
      · funext w; rw [arcsec_principal_complement]
      · ring
    have hd := ((hasDerivAt_id z).mul hA').sub hL
    convert hd using 1
    · rfl
    · simp only [id_eq]
      field_simp
      ring

/-- The inverse cotangent primitive away from the imaginary logarithm cuts. -/
@[dlmf 4.26.i]
theorem complex_arccot_primitive {z : ℂ} (hz : z∈arccotCutPlane) (hr : z.re≠0) :
    HasDerivAt (fun w : ℂ => w*arccotPrincipal w+Complex.log (1+w^2)/2) (arccotPrincipal z) z := by
  have hlog := (Complex.hasDerivAt_log (trig_one_add_sq_slit (Or.inl hr))).comp z
    (((hasDerivAt_id z).pow 2).const_add 1)
  have hd := ((hasDerivAt_id z).mul (hasDerivAt_arccot_principal hz)).add (hlog.div_const 2)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.add_apply,Pi.pow_apply]
    field_simp
    ring

end DLMF.Elementary

end
