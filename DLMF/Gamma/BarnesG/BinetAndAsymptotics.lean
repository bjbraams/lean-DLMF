/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Gamma.BarnesG.WeierstrassProduct

/-!
# Binet formulas and asymptotics of Barnes G

Binet remainder formulas, integer values and asymptotic expansions of the Barnes G function.

Source references and common attribution are retained in
`DLMF.Gamma.BarnesG`.
-/

@[expose] public section

open Complex Filter MeasureTheory intervalIntegral

open scoped Real Topology

noncomputable section

namespace DLMF.Gamma

/-! ### Proof of 5.17.5

Write `D(t)` for the difference in 5.17.5. By 5.17.4, `D(t) = E(t) - ∫₀ᵗ log Γ(s+1) ds` with `E`
elementary. With `Ψ(t) = ∫₀¹ x log Γ(x+t) dx`, Binet's bound `0 ≤ μ(x) ≤ 1/(12x)` gives
`D(t) - V(t) = B(t) = O(1/t)`, where `V` has derivative `R(t) - ∫ₜ^{t+1} log Γ` with zero
derivative, so `V` is affine. At the integers `G(n+1) = ∏ k!` (5.17.2) turns `D(n)` into
`log A - h(n)` with `h(n) = ∑ k log k - (n²/2 + n/2 + 1/12) log n + n²/4`. The Euler–Maclaurin
continuation `ζ(s) = 1/(s-1) + 1/2 + s/12 + ∑ eₙ(s)` (valid for `re s > -2`, by the identity
theorem), differentiated termwise at `s = -1`, gives `h(n) → 1/12 - ζ'(-1) = log A` (5.17.7).
Hence `V(n) → 0`, so `V = 0` and `D = B`.
-/

namespace BarnesAsymp

/-- The local Euler–Maclaurin error on `[n, n+1]` for `x ↦ x^{-s}`, with the `B₂` correction. -/
def zetaTerm (s : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) ^ (-s) + ((n : ℂ) + 1) ^ (-s)) / 2 -
    (((n : ℂ) + 1) ^ (1 - s) - (n : ℂ) ^ (1 - s)) / (1 - s) +
    s / 12 * (((n : ℂ) + 1) ^ (-s - 1) - (n : ℂ) ^ (-s - 1))

/-- `v ↦ (N + v)^a` has derivative `a (N + v)^(a-1)` where `N + v > 0`. -/
theorem hasDerivAt_pw {N : ℝ} (a : ℂ) {v : ℝ} (hv : 0 < N + v) :
    HasDerivAt (fun v : ℝ => ((N + v : ℝ) : ℂ) ^ a) (a * ((N + v : ℝ) : ℂ) ^ (a - 1)) v := by
  have h1 : HasDerivAt (fun v : ℝ => ((N + v : ℝ) : ℂ)) 1 v := by
    simpa using ((hasDerivAt_id v).const_add N).ofReal_comp
  have h2 := (Complex.hasStrictDerivAt_cpow_const (c := a)
    (Complex.ofReal_mem_slitPlane.2 hv)).hasDerivAt
  have h3 := h2.comp v h1
  simp only [Function.comp_def, mul_one] at h3
  exact h3

/-- Mean value bound on `[0, 1]`: if `|f'| ≤ C` there, then `|f(v) - f(0)| ≤ C`. -/
lemma mvt01 {f f' : ℝ → ℂ} {C : ℝ} (hf : ∀ v ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' v) v)
    (hC : ∀ v ∈ Set.Icc (0 : ℝ) 1, ‖f' v‖ ≤ C) (hC0 : 0 ≤ C) :
    ∀ v ∈ Set.Icc (0 : ℝ) 1, ‖f v - f 0‖ ≤ C := by
  intro v hv
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (a := 0) (b := 1)
    (fun x hx => (hf x hx).hasDerivWithinAt) (fun x hx => hC x (Set.Ico_subset_Icc_self hx)) v hv
  calc ‖f v - f 0‖ ≤ C * (v - 0) := this
    _ ≤ C * 1 := by gcongr; linarith [hv.2]
    _ = C := mul_one C

/-- The local Euler–Maclaurin error `zetaTerm s n` is bounded by `|s(s+1)(s+2)| n^(-Re s - 3)`. -/
theorem norm_zetaTerm_le {s : ℂ} (hs : s ≠ 1) (hre : -3 ≤ s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖zetaTerm s n‖ ≤ ‖s * (s + 1) * (s + 2)‖ * (n : ℝ) ^ (-s.re - 3) := by
  set N : ℝ := (n : ℝ) with hNdef
  have hN : 0 < N := by rw [hNdef]; exact_mod_cast hn
  have hs1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  set pw : ℂ → ℝ → ℂ := fun a v => ((N + v : ℝ) : ℂ) ^ a with hpw_def
  have hpw : ∀ a : ℂ, ∀ v ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (pw a) (a * pw (a - 1) v) v :=
    fun a v hv => hasDerivAt_pw a (by linarith [hv.1])
  set M : ℝ := ‖s * (s + 1) * (s + 2)‖ * N ^ (-s.re - 3) with hM
  have hM0 : 0 ≤ M := by positivity
  let g0 : ℝ → ℂ := fun v => pw (-s) v
  let g1 : ℝ → ℂ := fun v => -s * pw (-s - 1) v
  let g2 : ℝ → ℂ := fun v => s * (s + 1) * pw (-s - 2) v
  let g3 : ℝ → ℂ := fun v => -(s * (s + 1) * (s + 2)) * pw (-s - 3) v
  have hg0 : ∀ v ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g0 (g1 v) v := fun v hv => hpw (-s) v hv
  have hg1 : ∀ v ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g1 (g2 v) v := by
    intro v hv
    refine ((hpw (-s - 1) v hv).const_mul (-s)).congr_deriv ?_
    simp only [g2, show -s - 1 - 1 = -s - 2 by ring]
    ring
  have hg2 : ∀ v ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g2 (g3 v) v := by
    intro v hv
    refine ((hpw (-s - 2) v hv).const_mul (s * (s + 1))).congr_deriv ?_
    simp only [g3, show -s - 2 - 1 = -s - 3 by ring]
    ring
  have hg3 : ∀ v ∈ Set.Icc (0 : ℝ) 1, ‖g3 v‖ ≤ M := by
    intro v hv
    have hNv : 0 < N + v := by linarith [hv.1]
    show ‖-(s * (s + 1) * (s + 2)) * ((N + v : ℝ) : ℂ) ^ (-s - 3)‖ ≤ M
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hNv, hM,
      show (-s - 3).re = -s.re - 3 by simp]
    gcongr ?_ * ?_
    exact Real.rpow_le_rpow_of_nonpos hN (by linarith [hv.1]) (by linarith)
  -- step (a)
  have ha : ∀ w ∈ Set.Icc (0 : ℝ) 1, ‖g2 w - g2 0‖ ≤ M := mvt01 hg2 hg3 hM0
  -- step (b)
  have hb : ∀ v ∈ Set.Icc (0 : ℝ) 1, ‖g1 v - (v : ℂ) * g2 v - g1 0‖ ≤ 2 * M := by
    intro v hv
    let h : ℝ → ℂ := fun w => g1 w - (w : ℂ) * g2 v
    have hh : ∀ w ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h (g2 w - g2 v) w := by
      intro w hw
      have := (hg1 w hw).sub ((hasDerivAt_id w).ofReal_comp.mul_const (g2 v))
      exact this.congr_deriv (by push_cast; ring)
    have hbd : ∀ w ∈ Set.Icc (0 : ℝ) 1, ‖g2 w - g2 v‖ ≤ 2 * M := by
      intro w hw
      calc ‖g2 w - g2 v‖ = ‖(g2 w - g2 0) - (g2 v - g2 0)‖ := by ring_nf
        _ ≤ ‖g2 w - g2 0‖ + ‖g2 v - g2 0‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (ha w hw) (ha v hv)
        _ = 2 * M := by ring
    have := mvt01 hh hbd (by positivity) v hv
    simpa [h] using this
  -- the error function
  let E : ℝ → ℂ := fun v => (v : ℂ) / 2 * (g0 0 + g0 v) - (pw (1 - s) v - pw (1 - s) 0) / (1 - s)
    - (v : ℂ) ^ 2 / 12 * (g1 v - g1 0)
  let E' : ℝ → ℂ := fun v => (g0 0 - g0 v) / 2 + (v : ℂ) / 3 * g1 v + (v : ℂ) / 6 * g1 0
    - (v : ℂ) ^ 2 / 12 * g2 v
  let E'' : ℝ → ℂ := fun v => -(g1 v - (v : ℂ) * g2 v - g1 0) / 6 - (v : ℂ) ^ 2 / 12 * g3 v
  have hE : ∀ v ∈ Set.Icc (0 : ℝ) 1, HasDerivAt E (E' v) v := by
    intro v hv
    have hx : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 v := (hasDerivAt_id v).ofReal_comp
    have h1 := (hx.div_const 2).mul ((hg0 v hv).const_add (g0 0))
    have h2 := ((hpw (1 - s) v hv).sub_const (pw (1 - s) 0)).div_const (1 - s)
    have h3 := ((hx.pow 2).div_const 12).mul ((hg1 v hv).sub_const (g1 0))
    refine ((h1.sub h2).sub h3).congr_deriv ?_
    simp only [E', g0, Pi.pow_apply, show (1 : ℂ) - s - 1 = -s by ring]
    field_simp
    ring
  have hE' : ∀ v ∈ Set.Icc (0 : ℝ) 1, HasDerivAt E' (E'' v) v := by
    intro v hv
    have hx : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 v := (hasDerivAt_id v).ofReal_comp
    have h1 := ((hg0 v hv).const_sub (g0 0)).div_const 2
    have h2 := (hx.div_const 3).mul (hg1 v hv)
    have h3 := (hx.div_const 6).mul_const (g1 0)
    have h4 := ((hx.pow 2).div_const 12).mul (hg2 v hv)
    refine (((h1.add h2).add h3).sub h4).congr_deriv ?_
    simp only [E'', Pi.pow_apply]
    ring
  have hE'' : ∀ v ∈ Set.Icc (0 : ℝ) 1, ‖E'' v‖ ≤ M := by
    intro v hv
    have hv2 : ‖(v : ℂ) ^ 2 / 12‖ ≤ 1 / 12 := by
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv.1]
      norm_num
      nlinarith [hv.1, hv.2]
    calc ‖E'' v‖ ≤ ‖g1 v - (v : ℂ) * g2 v - g1 0‖ / 6 + ‖(v : ℂ) ^ 2 / 12‖ * ‖g3 v‖ := by
          simp only [E'']
          refine (norm_sub_le _ _).trans ?_
          rw [norm_div, norm_neg, norm_mul]
          norm_num
      _ ≤ 2 * M / 6 + 1 / 12 * M := by
          gcongr
          · exact hb v hv
          · exact hg3 v hv
      _ ≤ M := by linarith
  have hE'0 : E' 0 = 0 := by simp [E']
  have hE'b : ∀ v ∈ Set.Icc (0 : ℝ) 1, ‖E' v‖ ≤ M := by
    intro v hv
    simpa [hE'0] using mvt01 hE' hE'' hM0 v hv
  have hE0 : E 0 = 0 := by simp [E]
  have hE1 := mvt01 hE hE'b hM0 1 ⟨zero_le_one, le_rfl⟩
  rw [hE0, sub_zero] at hE1
  have hEq : E 1 = zetaTerm s n := by
    simp only [E, g0, g1, pw, zetaTerm, hNdef]
    push_cast
    simp only [add_zero]
    field_simp
    ring
  rw [← hEq]
  exact hE1

/-- Telescoped partial sums of the Euler–Maclaurin errors `zetaTerm s (i + 1)`. -/
theorem sum_zetaTerm (s : ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range N, zetaTerm s (i + 1) =
      ∑ k ∈ Finset.range (N + 1), ((k : ℂ) + 1) ^ (-s) - (1 + ((N : ℂ) + 1) ^ (-s)) / 2 -
        (((N : ℂ) + 1) ^ (1 - s) - 1) / (1 - s) + s / 12 * (((N : ℂ) + 1) ^ (-s - 1) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (n := N + 1)]
    simp only [zetaTerm]
    push_cast
    ring

/-- `∑ (i + 1)^p` converges for `p < -1`. -/
theorem summable_rpow_succ {p : ℝ} (hp : p < -1) :
    Summable (fun i : ℕ => ((i : ℝ) + 1) ^ p) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
  refine this.congr fun i => ?_
  push_cast
  rfl

/-- A locally uniform bound for the terms near `s₀` with `-2 < re s₀`. -/
theorem norm_zetaTerm_le_near {s₀ s : ℂ} (h₀ : -2 < s₀.re)
    (hs : s ∈ Metric.ball s₀ ((s₀.re + 2) / 2)) (hs1 : s ≠ 1) (i : ℕ) :
    ‖zetaTerm s (i + 1)‖ ≤
      (‖s₀‖ + (s₀.re + 2) / 2 + 2) ^ 3 * ((i : ℝ) + 1) ^ (-1 - (s₀.re + 2) / 2) := by
  set δ := (s₀.re + 2) / 2 with hδ
  have hd : ‖s - s₀‖ < δ := by simpa [dist_eq_norm] using hs
  have hre : s₀.re - δ < s.re := by
    have := Complex.abs_re_le_norm (s - s₀)
    rw [Complex.sub_re] at this
    have := (abs_lt.mp (lt_of_le_of_lt this hd)).1
    linarith
  have hsn : ‖s‖ ≤ ‖s₀‖ + δ := by
    have := norm_sub_norm_le s s₀
    linarith
  have hb := norm_zetaTerm_le hs1 (by linarith) (n := i + 1) (by omega)
  refine hb.trans ?_
  push_cast
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have h1 : ‖s + 1‖ ≤ ‖s₀‖ + δ + 2 := by
    have := norm_add_le s 1
    rw [norm_one] at this
    linarith
  have h2 : ‖s + 2‖ ≤ ‖s₀‖ + δ + 2 := by
    have := norm_add_le s 2
    rw [show ‖(2 : ℂ)‖ = 2 by simp] at this
    linarith
  have h0 : ‖s‖ ≤ ‖s₀‖ + δ + 2 := by linarith
  have hA : ‖s * (s + 1) * (s + 2)‖ ≤ (‖s₀‖ + δ + 2) ^ 3 := by
    rw [norm_mul, norm_mul, pow_three]
    calc ‖s‖ * ‖s + 1‖ * ‖s + 2‖ ≤ (‖s₀‖ + δ + 2) * (‖s₀‖ + δ + 2) * (‖s₀‖ + δ + 2) := by
          gcongr
      _ = _ := by ring
  have hB : ((i : ℝ) + 1) ^ (-s.re - 3) ≤ ((i : ℝ) + 1) ^ (-1 - δ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)])
      (by linarith)
  exact mul_le_mul hA hB (by positivity) (by positivity)

/-- Each Euler–Maclaurin error term is holomorphic in `s ≠ 1`. -/
theorem differentiableAt_zetaTerm {s : ℂ} (hs : s ≠ 1) (n : ℕ) (hn : 1 ≤ n) :
    DifferentiableAt ℂ (fun s => zetaTerm s n) s := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
  have hs1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have e1 : ∀ c : ℂ, c ≠ 0 → ∀ b : ℂ,
      DifferentiableAt ℂ (fun s : ℂ => c ^ (b - s)) s := fun c hc b =>
    ((differentiableAt_const b).sub differentiableAt_id).const_cpow (Or.inl hc)
  have e2 : ∀ c : ℂ, c ≠ 0 → DifferentiableAt ℂ (fun s : ℂ => c ^ (-s)) s := fun c hc =>
    differentiableAt_id.neg.const_cpow (Or.inl hc)
  have e3 : ∀ c : ℂ, c ≠ 0 → DifferentiableAt ℂ (fun s : ℂ => c ^ (-s - 1)) s := fun c hc =>
    (differentiableAt_id.neg.sub_const 1).const_cpow (Or.inl hc)
  unfold zetaTerm
  exact ((((e2 _ hn0).add (e2 _ hn1)).div_const 2).sub
    (((e1 _ hn1 1).sub (e1 _ hn0 1)).div ((differentiableAt_const 1).sub differentiableAt_id)
      hs1)).add ((differentiableAt_id.div_const 12).mul ((e3 _ hn1).sub (e3 _ hn0)))

/-- The domain: the half-plane `re s > -2` slit along `[1, ∞)`. -/
def zetaDom : Set ℂ := {s | -2 < s.re} \ {s | s.im = 0 ∧ 1 ≤ s.re}

/-- The domain `zetaDom` is open. -/
theorem isOpen_zetaDom : IsOpen zetaDom :=
  (isOpen_lt continuous_const Complex.continuous_re).sdiff
    ((isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re))

/-- Points of `zetaDom` differ from `1`. -/
theorem ne_one_of_mem_zetaDom {s : ℂ} (hs : s ∈ zetaDom) : s ≠ 1 := by
  rintro rfl
  exact hs.2 ⟨by simp, by simp⟩

/-- The domain `zetaDom` is preconnected. -/
theorem isPreconnected_zetaDom : IsPreconnected zetaDom := by
  have h0 : (0 : ℂ) ∈ zetaDom := ⟨by simp, fun h => by norm_num at h⟩
  have hstar : StarConvex ℝ 0 zetaDom := by
    intro y hy a b ha hb hab
    simp only [smul_zero, zero_add]
    obtain ⟨hy1, hy2⟩ := hy
    simp only [Set.mem_ofPred_eq] at hy1 hy2
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      rcases le_or_gt 0 y.re with h | h
      · nlinarith
      · nlinarith
    · rintro ⟨h1, h2⟩
      simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, Complex.mul_im, add_zero] at h1 h2
      have hb0 : 0 < b := by
        rcases eq_or_lt_of_le hb with h | h
        · rw [← h] at h2; simp at h2; linarith
        · exact h
      have him : y.im = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · linarith
        · exact h
      have hre : 0 < y.re := by
        by_contra hc
        push Not at hc
        nlinarith
      exact hy2 ⟨him, by nlinarith⟩
  exact (hstar.isPathConnected h0).isConnected.isPreconnected

/-- The continued series. -/
def zetaSeries (s : ℂ) : ℂ := ∑' i : ℕ, zetaTerm s (i + 1)

/-- The Euler–Maclaurin continuation of `ζ` to `re s > -2`. -/
def zetaEM (s : ℂ) : ℂ := 1 / (s - 1) + 1 / 2 + s / 12 + zetaSeries s

/-- The series `∑ zetaTerm s (i + 1)` is holomorphic on `zetaDom`. -/
theorem differentiableAt_zetaSeries {s₀ : ℂ} (h : s₀ ∈ zetaDom) :
    DifferentiableAt ℂ zetaSeries s₀ := by
  have h₀ : -2 < s₀.re := h.1
  set W := zetaDom ∩ Metric.ball s₀ ((s₀.re + 2) / 2) with hW
  have hWo : IsOpen W := isOpen_zetaDom.inter Metric.isOpen_ball
  have hs₀W : s₀ ∈ W := ⟨h, Metric.mem_ball_self (by linarith)⟩
  have hd : DifferentiableOn ℂ (fun w : ℂ => ∑' i : ℕ, zetaTerm w (i + 1)) W := by
    refine differentiableOn_tsum_of_summable_norm
      ((summable_rpow_succ (p := -1 - (s₀.re + 2) / 2) (by linarith)).mul_left
        ((‖s₀‖ + (s₀.re + 2) / 2 + 2) ^ 3)) (fun i w hw => ?_) hWo (fun i w hw => ?_)
    · exact (differentiableAt_zetaTerm (ne_one_of_mem_zetaDom hw.1) (i + 1)
        (by omega)).differentiableWithinAt
    · exact norm_zetaTerm_le_near h₀ hw.2 (ne_one_of_mem_zetaDom hw.1) i
  exact hd.differentiableAt (hWo.mem_nhds hs₀W)

/-- The Euler–Maclaurin form `zetaEM` of `ζ` is holomorphic on `zetaDom`. -/
theorem differentiableAt_zetaEM {s : ℂ} (h : s ∈ zetaDom) : DifferentiableAt ℂ zetaEM s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_mem_zetaDom h)
  have hA : DifferentiableAt ℂ (fun s : ℂ => 1 / (s - 1)) s :=
    (differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const 1) hs1
  have hB : DifferentiableAt ℂ (fun s : ℂ => s / 12) s := differentiableAt_id.div_const 12
  exact ((hA.add_const (1 / 2 : ℂ)).add hB).add (differentiableAt_zetaSeries h)

/-- `(N + 1)^(-w) → 0` for `Re w > 0`. -/
theorem tendsto_cpow_neg {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (-w)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : ∀ N : ℕ, ‖((N : ℂ) + 1) ^ (-w)‖ = ((N : ℝ) + 1) ^ (-w.re) := by
    intro N
    have : ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]
  simp only [h]
  exact (tendsto_rpow_neg_atTop hw).comp
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

/-- `ζ(s) = zetaEM s` for `Re s > 1`. -/
theorem zeta_eq_zetaEM {s : ℂ} (hs : 1 < s.re) : riemannZeta s = zetaEM s := by
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have hs1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hsum : Summable (fun i : ℕ => zetaTerm s (i + 1)) := by
    refine Summable.of_norm_bounded
      ((summable_rpow_succ (p := -s.re - 3) (by linarith)).mul_left ‖s * (s + 1) * (s + 2)‖)
      (fun i => ?_)
    have := norm_zetaTerm_le hs1 (by linarith) (n := i + 1) (by omega)
    simpa using this
  have hA := hsum.hasSum.tendsto_sum_nat
  -- the partial sums of `ζ`
  have hz : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), ((k : ℂ) + 1) ^ (-s)) atTop
      (𝓝 (riemannZeta s)) := by
    have hsz : Summable (fun k : ℕ => 1 / ((k : ℂ) + 1) ^ s) := by
      have := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
      refine this.congr fun k => ?_
      push_cast
      rfl
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    have := (hsz.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    refine this.congr fun N => ?_
    simp only [Function.comp_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.cpow_neg, one_div]
  have hB : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, zetaTerm s (i + 1)) atTop
      (𝓝 (riemannZeta s - (1 + 0) / 2 - (0 - 1) / (1 - s) + s / 12 * (0 - 1))) := by
    simp only [sum_zetaTerm]
    refine (((hz.sub ((tendsto_const_nhds.add (tendsto_cpow_neg (w := s) (by linarith))).div_const
      2)).sub (((?_ : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (1 - s)) atTop (𝓝 0)).sub_const
        1).div_const _)).add
      (((?_ : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (-s - 1)) atTop (𝓝 0)).sub_const
        1).const_mul _))
    · have := tendsto_cpow_neg (w := s - 1) (by simp; linarith)
      simpa using this
    · have := tendsto_cpow_neg (w := s + 1) (by simp; linarith)
      refine this.congr fun N => ?_
      congr 1
      ring
  have heq := tendsto_nhds_unique hA hB
  unfold zetaEM zetaSeries
  rw [heq]
  have hs2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

/-- `ζ = zetaEM` on `zetaDom`, by analytic continuation. -/
theorem eqOn_zeta_zetaEM : Set.EqOn riemannZeta zetaEM zetaDom := by
  have hζ : AnalyticOnNhd ℂ riemannZeta zetaDom :=
    DifferentiableOn.analyticOnNhd (fun s hs =>
      (differentiableAt_riemannZeta (ne_one_of_mem_zetaDom hs)).differentiableWithinAt)
      isOpen_zetaDom
  have hZ : AnalyticOnNhd ℂ zetaEM zetaDom :=
    DifferentiableOn.analyticOnNhd (fun s hs => (differentiableAt_zetaEM hs).differentiableWithinAt)
      isOpen_zetaDom
  have hz₀ : (2 + I : ℂ) ∈ zetaDom := ⟨by norm_num, fun h => by norm_num at h⟩
  refine hζ.eqOn_of_preconnected_of_eventuallyEq hZ isPreconnected_zetaDom hz₀ ?_
  have : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 + I : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [this] with s hs using zeta_eq_zetaEM hs

/-- The derivative at `s = -1` of the `n`-th term. -/
def dz (n : ℕ) : ℝ :=
  -((n : ℝ) * Real.log n + ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)) / 2 +
    (((n : ℝ) + 1) ^ 2 * Real.log ((n : ℝ) + 1) - (n : ℝ) ^ 2 * Real.log n) / 2 -
    (2 * (n : ℝ) + 1) / 4 + (Real.log ((n : ℝ) + 1) - Real.log n) / 12

/-- The derivative of `s ↦ zetaTerm s n` at `s = -1` is `dz n`. -/
theorem hasDerivAt_zetaTerm (n : ℕ) (hn : 1 ≤ n) :
    HasDerivAt (fun s => zetaTerm s n) (dz n : ℂ) (-1) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
  have hlog0 : Complex.log (n : ℂ) = (Real.log n : ℂ) := Complex.natCast_log.symm
  have hlog1 : Complex.log ((n : ℂ) + 1) = (Real.log ((n : ℝ) + 1) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]
    push_cast
    rfl
  have hid : HasDerivAt (fun s : ℂ => s) 1 (-1) := hasDerivAt_id _
  have p1 := fun (c : ℂ) (hc : c ≠ 0) => hid.neg.const_cpow (c := c) (Or.inl hc)
  have p2 := fun (c : ℂ) (hc : c ≠ 0) => (hid.const_sub 1).const_cpow (c := c) (Or.inl hc)
  have p3 := fun (c : ℂ) (hc : c ≠ 0) => (hid.neg.sub_const 1).const_cpow (c := c) (Or.inl hc)
  have hden : HasDerivAt (fun s : ℂ => 1 - s) (-1) (-1) := by simpa using hid.const_sub 1
  have hT := ((((p1 _ hn0).add (p1 _ hn1)).div_const 2).sub
    (((p2 _ hn1).sub (p2 _ hn0)).div hden (by norm_num))).add
    ((hid.div_const 12).mul ((p3 _ hn1).sub (p3 _ hn0)))
  unfold zetaTerm
  refine hT.congr_deriv ?_
  simp only [Pi.neg_apply, Pi.sub_apply, neg_neg, cpow_one, sub_self, cpow_zero,
    show (1 : ℂ) - -1 = 2 by norm_num, hlog0, hlog1, dz, cpow_ofNat]
  push_cast
  ring

/-- The normalized hyperfactorial sequence. -/
def hseq (N : ℕ) : ℝ := ∑ k ∈ Finset.range (N + 1), (k : ℝ) * Real.log k -
    ((N : ℝ) ^ 2 / 2 + N / 2 + 1 / 12) * Real.log N + (N : ℝ) ^ 2 / 4

/-- `∑_{i<M} dz(i + 1) = 1/4 - hseq(M + 1)`. -/
theorem sum_dz (M : ℕ) : ∑ i ∈ Finset.range M, dz (i + 1) = 1 / 4 - hseq (M + 1) := by
  induction M with
  | zero => simp [hseq, Finset.sum_range_succ]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [hseq, dz]
    rw [Finset.sum_range_succ _ (M + 1 + 1)]
    push_cast
    ring

/-- Glaisher's limit, with the constant identified through `ζ'(-1)`. -/
theorem tendsto_hseq : Tendsto hseq atTop (𝓝 (Real.log glaisherKinkelin)) := by
  have hm1 : (-1 : ℂ) ∈ zetaDom := ⟨by norm_num, fun h => by norm_num at h⟩
  have hEv : riemannZeta =ᶠ[𝓝 (-1)] zetaEM := by
    filter_upwards [isOpen_zetaDom.mem_nhds hm1] with s hs using eqOn_zeta_zetaEM hs
  set S := deriv zetaSeries (-1) with hSdef
  have hne : ∀ w ∈ Metric.ball (-1 : ℂ) (((-1 : ℂ).re + 2) / 2), w ≠ 1 := by
    intro w hw h
    rw [h] at hw
    simp [dist_eq_norm] at hw
    norm_num at hw
  have hS0 : HasSum (fun i : ℕ => deriv (fun w => zetaTerm w (i + 1)) (-1)) S :=
    hasSum_deriv_of_summable_norm
      ((summable_rpow_succ (p := -1 - ((-1 : ℂ).re + 2) / 2) (by norm_num)).mul_left
        ((‖(-1 : ℂ)‖ + ((-1 : ℂ).re + 2) / 2 + 2) ^ 3))
      (fun i w hw => (differentiableAt_zetaTerm (hne w hw) (i + 1)
        (by omega)).differentiableWithinAt)
      Metric.isOpen_ball
      (fun i w hw => norm_zetaTerm_le_near (by norm_num) hw (hne w hw) i)
      (Metric.mem_ball_self (by norm_num))
  have hS1 : HasSum (fun i : ℕ => (dz (i + 1) : ℂ)) S := by
    refine hS0.congr_fun fun i => ?_
    exact ((hasDerivAt_zetaTerm (i + 1) (by omega)).deriv).symm
  have hS2 : HasSum (fun i : ℕ => dz (i + 1)) S.re := by
    simpa using Complex.hasSum_re hS1
  -- the derivative of `ζ` at `-1`
  have hZ : HasDerivAt zetaEM (-1 / 4 + 1 / 12 + S) (-1) := by
    have h1 : HasDerivAt (fun s : ℂ => 1 / (s - 1)) (-1 / 4) (-1) := by
      have := (hasDerivAt_const (-1 : ℂ) (1 : ℂ)).div ((hasDerivAt_id (-1 : ℂ)).sub_const 1)
        (by norm_num)
      refine this.congr_deriv ?_
      norm_num
    have h2 : HasDerivAt (fun s : ℂ => s / 12) (1 / 12) (-1) := (hasDerivAt_id _).div_const 12
    have h3 : HasDerivAt zetaSeries S (-1) := (differentiableAt_zetaSeries hm1).hasDerivAt
    exact ((h1.add_const (1 / 2 : ℂ)).add h2).add h3
  have hd : deriv riemannZeta (-1) = -1 / 4 + 1 / 12 + S := by
    rw [hEv.deriv_eq]
    exact hZ.deriv
  have hlim : Tendsto (fun M : ℕ => hseq (M + 1)) atTop (𝓝 (1 / 4 - S.re)) := by
    have := hS2.tendsto_sum_nat
    refine (tendsto_const_nhds.sub this).congr fun M => ?_
    rw [sum_dz]
    ring
  rw [← tendsto_add_atTop_iff_nat 1]
  convert hlim using 2
  rw [glaisherKinkelin_eq_zeta_neg_one, hd]
  simp
  ring

/-! ### The real form of 5.17.4 and the integer values -/

/-- For `x > 0`, `ln G(x + 1) = (x/2) ln 2π - x(x+1)/2 + x ln Γ(x + 1) - ∫₀ˣ ln Γ(t + 1) dt` (real
form of 5.17.4). -/
theorem log_barnesGSucc_re {x : ℝ} (hx : 0 < x) :
    Real.log (barnesGSucc x).re =
      x / 2 * Real.log (2 * π) - x * (x + 1) / 2 + x * Real.log (Real.Gamma (x + 1)) -
        ∫ t in (0 : ℝ)..x, Real.log (Real.Gamma (t + 1)) := by
  have hsub : Set.uIcc 0 x ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le hx.le]; exact Set.Icc_subset_Ici_self
  have hG : ∀ t : ℝ, 0 ≤ t →
      Complex.log (Complex.Gamma (t + 1)) = ((Real.log (Real.Gamma (t + 1)) : ℝ) : ℂ) := by
    intro t ht
    rw [show (t : ℂ) + 1 = ((t + 1 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
      Complex.ofReal_log (Real.Gamma_pos_of_pos (by linarith)).le]
  have hlog : Complex.log (2 * π) = ((Real.log (2 * π) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
  have h := log_barnesGSucc hx
  set r : ℝ := x / 2 * Real.log (2 * π) - x * (x + 1) / 2 -
    Real.eulerMascheroniConstant * x ^ 2 / 2 + ∑' n, barnesLogTerm x n with hr
  have hb : barnesGSucc x = ((Real.exp r : ℝ) : ℂ) := barnesGSucc_ofReal hx.le
  rw [hb, ← Complex.ofReal_log (Real.exp_pos _).le, hG x hx.le, intervalIntegral.integral_congr
      (g := fun t : ℝ => ((Real.log (Real.Gamma (t + 1)) : ℝ) : ℂ)) fun t ht => hG t (hsub ht),
    intervalIntegral.integral_ofReal, hlog] at h
  rw [hb, Complex.ofReal_re]
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  ring

/-- `∑_{k<n} ln k! = n ln n! - ∑_{k≤n} k ln k`. -/
theorem sum_log_factorial (n : ℕ) :
    ∑ k ∈ Finset.range n, Real.log (k.factorial : ℝ) =
      n * Real.log (n.factorial : ℝ) - ∑ k ∈ Finset.range (n + 1), (k : ℝ) * Real.log k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ _ (n + 1), Nat.factorial_succ]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]
    ring

/-- The statement's function at a positive integer. -/
theorem barnes_nat_eq (n : ℕ) (hn : 1 ≤ n) :
    Real.log (barnesGSucc ((n : ℝ) : ℂ)).re -
        ((1 / 4) * (n : ℝ) ^ 2 + n * Real.log (Real.Gamma (n + 1)) -
          ((1 / 2) * n * (n + 1) + 1 / 12) * Real.log n - Real.log glaisherKinkelin) =
      Real.log glaisherKinkelin - hseq n := by
  have hG : barnesGSucc ((n : ℝ) : ℂ) = ∏ k ∈ Finset.Icc 1 (n - 1), (k.factorial : ℂ) := by
    have := barnesG_nat (n + 1) (by omega)
    rw [show n + 1 - 2 = n - 1 by omega] at this
    rw [← this, barnesG]
    push_cast
    ring_nf
  have hprod : (∏ k ∈ Finset.Icc 1 (n - 1), (k.factorial : ℂ)).re =
      ∏ k ∈ Finset.Icc 1 (n - 1), (k.factorial : ℝ) := by
    have : (∏ k ∈ Finset.Icc 1 (n - 1), (k.factorial : ℂ)) =
        ((∏ k ∈ Finset.Icc 1 (n - 1), (k.factorial : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_re]
  have hsum : Real.log (∏ k ∈ Finset.Icc 1 (n - 1), (k.factorial : ℝ)) =
      ∑ k ∈ Finset.range n, Real.log (k.factorial : ℝ) := by
    rw [Real.log_prod (fun k _ => by positivity)]
    have : Finset.range n = insert 0 (Finset.Icc 1 (n - 1)) := by
      ext k; simp; omega
    rw [this, Finset.sum_insert (by simp)]
    simp
  rw [hG, hprod, hsum, sum_log_factorial, Real.Gamma_nat_eq_factorial, hseq]
  ring

/-! ### The averaged Binet remainder -/

/-- `log Γ` is continuous on `(0, ∞)`. -/
theorem continuousOn_logGamma : ContinuousOn (fun t => Real.log (Real.Gamma t)) (Set.Ioi 0) := by
  intro t ht
  have ht' : (0 : ℝ) < t := ht
  have hc : ContinuousAt Real.Gamma t :=
    (Real.differentiableAt_Gamma fun m h => by
      have : (0 : ℝ) ≤ m := m.cast_nonneg
      linarith).continuousAt
  exact (hc.log (Real.Gamma_pos_of_pos ht').ne').continuousWithinAt

/-- `Ψ(t) = ∫₀¹ x log Γ(x+t) dx`. -/
def barnesPsi (t : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, x * Real.log (Real.Gamma (x + t))

/-- The comparison function `B(t)`. -/
def barnesB (t : ℝ) : ℝ :=
  (t / 2 + 1 / 12) * Real.log t - t / 2 + Real.log (2 * π) / 4 - barnesPsi t

/-- `|(x + t - 1/2)(ln(x + t) - ln t) - x| ≤ 1/t` for `0 ≤ x ≤ 1`, `t ≥ 1`. -/
theorem log_one_add_bounds {x t : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ht : 1 ≤ t) :
    |(x + t - 1 / 2) * (Real.log (x + t) - Real.log t) - x| ≤ 1 / t := by
  have ht0 : 0 < t := by linarith
  have hu : 0 ≤ x / t := div_nonneg hx0 ht0.le
  have hL : Real.log (x + t) - Real.log t = Real.log (1 + x / t) := by
    rw [← Real.log_div (by linarith) ht0.ne']
    congr 1
    field_simp
    ring
  rw [hL]
  set L := Real.log (1 + x / t)
  have hL1 : L ≤ x / t := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + x / t by positivity)
    linarith
  have hL2 : x / t - (x / t) ^ 2 / 2 ≤ L := sub_sq_div_two_le_log_one_add hu
  have hc : 0 ≤ x + t - 1 / 2 := by linarith
  have hup : (x + t - 1 / 2) * L ≤ (x + t - 1 / 2) * (x / t) := mul_le_mul_of_nonneg_left hL1 hc
  have hlo : (x + t - 1 / 2) * (x / t - (x / t) ^ 2 / 2) ≤ (x + t - 1 / 2) * L :=
    mul_le_mul_of_nonneg_left hL2 hc
  have e1 : (x + t - 1 / 2) * (x / t) - x = (x ^ 2 - x / 2) / t := by
    field_simp
    ring
  have e2 : (x + t - 1 / 2) * (x / t - (x / t) ^ 2 / 2) - x =
      (x ^ 2 - x / 2) / t - (x + t - 1 / 2) * x ^ 2 / (2 * t ^ 2) := by
    field_simp
    ring
  have b1 : (x ^ 2 - x / 2) / t ≤ 1 / t := by
    apply div_le_div_of_nonneg_right _ ht0.le
    nlinarith
  have b2 : -(1 / 16) / t ≤ (x ^ 2 - x / 2) / t := by
    apply div_le_div_of_nonneg_right _ ht0.le
    nlinarith [sq_nonneg (x - 1 / 4)]
  have b3 : (x + t - 1 / 2) * x ^ 2 / (2 * t ^ 2) ≤ 3 / 4 / t := by
    rw [div_le_div_iff₀ (by positivity) ht0]
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have h1 : (x + t - 1 / 2) * x ^ 2 ≤ (x + t - 1 / 2) * 1 := mul_le_mul_of_nonneg_left hx2 hc
    have h2 : (x + t - 1 / 2) * x ^ 2 * t ≤ (3 / 2 * t) * t :=
      mul_le_mul_of_nonneg_right (by linarith) ht0.le
    nlinarith
  rw [abs_le]
  constructor
  · have : -(1 / 16) / t - 3 / 4 / t ≥ -(1 / t) := by
      rw [ge_iff_le, ← sub_nonneg]
      have : -(1 / 16) / t - 3 / 4 / t - -(1 / t) = (3 / 16) / t := by ring
      rw [this]; positivity
    linarith
  · linarith

/-- `|B(t)| ≤ 2/t` for `t ≥ 1`. -/
theorem abs_barnesB_le {t : ℝ} (ht : 1 ≤ t) : |barnesB t| ≤ 2 / t := by
  have ht0 : 0 < t := by linarith
  set g : ℝ → ℝ := fun x => x * (x + t - 1 / 2) * Real.log t - t * x + x / 2 * Real.log (2 * π)
    with hg
  have hgint : ∫ x in (0 : ℝ)..1, g x =
      (t / 2 + 1 / 12) * Real.log t - t / 2 + Real.log (2 * π) / 4 := by
    have hF : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt
        (fun x : ℝ => (x ^ 3 / 3 + (t - 1 / 2) * x ^ 2 / 2) * Real.log t - t * x ^ 2 / 2 +
          x ^ 2 / 4 * Real.log (2 * π)) (g x) x := by
      intro x _
      have := ((((((hasDerivAt_pow 3 x).div_const 3).add
        (((hasDerivAt_pow 2 x).const_mul (t - 1 / 2)).div_const 2)).mul_const (Real.log t)).sub
          (((hasDerivAt_pow 2 x).const_mul t).div_const 2)).add
          (((hasDerivAt_pow 2 x).div_const 4).mul_const (Real.log (2 * π))))
      refine this.congr_deriv ?_
      simp only [hg]
      push_cast
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      ((by fun_prop : Continuous g).intervalIntegrable 0 1)]
    ring
  have hcont : ContinuousOn (fun x : ℝ => x * Real.log (Real.Gamma (x + t))) (Set.uIcc 0 1) := by
    refine continuousOn_id.mul ?_
    refine continuousOn_logGamma.comp (continuousOn_id.add continuousOn_const) ?_
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    show (0 : ℝ) < x + t
    linarith [hx.1]
  have hpt : ∀ x ∈ Set.uIoc (0 : ℝ) 1,
      ‖x * Real.log (Real.Gamma (x + t)) - g x‖ ≤ 2 / t := by
    intro x hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    have hx0 : 0 ≤ x := hx.1.le
    have hx1 : x ≤ 1 := hx.2
    have hxt : 0 < x + t := by linarith
    obtain ⟨hμ0, hμ1⟩ := binetIntegral_mem hxt
    have hρ := log_one_add_bounds hx0 hx1 ht
    have hμ : binetIntegral (x + t) ≤ 1 / (12 * t) :=
      hμ1.trans (one_div_le_one_div_of_le (by positivity) (by linarith))
    have he : x * Real.log (Real.Gamma (x + t)) - g x =
        x * (((x + t - 1 / 2) * (Real.log (x + t) - Real.log t) - x) +
          binetIntegral (x + t)) := by
      rw [log_Gamma_eq_add_binetIntegral hxt, hg]
      ring
    rw [he, Real.norm_eq_abs, abs_mul, abs_of_nonneg hx0]
    have h12 : 1 / (12 * t) ≤ 1 / t := one_div_le_one_div_of_le ht0 (by linarith)
    have : |((x + t - 1 / 2) * (Real.log (x + t) - Real.log t) - x) + binetIntegral (x + t)|
        ≤ 2 / t := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_nonneg hμ0]
      have : 2 / t = 1 / t + 1 / t := by ring
      linarith
    calc x * |((x + t - 1 / 2) * (Real.log (x + t) - Real.log t) - x) + binetIntegral (x + t)|
        ≤ 1 * (2 / t) := by
          gcongr
      _ = 2 / t := one_mul _
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [intervalIntegral.integral_sub (hcont.intervalIntegrable)
    ((by fun_prop : Continuous g).intervalIntegrable 0 1), hgint] at hint
  have hB : barnesB t = -((∫ x in (0 : ℝ)..1, x * Real.log (Real.Gamma (x + t))) -
      ((t / 2 + 1 / 12) * Real.log t - t / 2 + Real.log (2 * π) / 4)) := by
    rw [barnesB, barnesPsi]; ring
  rw [hB, abs_neg]
  simpa using hint

/-! ### `D - B` is constant -/

/-- `y ↦ ∫₁ʸ f` has derivative `f(y)` for `f` continuous on `(0, ∞)` and `y > 0`. -/
theorem hasDerivAt_integral_one {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0)) {y : ℝ}
    (hy : 0 < y) : HasDerivAt (fun y => ∫ u in (1 : ℝ)..y, f u) (f y) y := by
  have hsub : Set.uIcc 1 y ⊆ Set.Ioi 0 := by
    intro u hu
    rcases Set.mem_uIcc.mp hu with h | h
    · show (0 : ℝ) < u; linarith [h.1]
    · show (0 : ℝ) < u; linarith [h.1]
  exact intervalIntegral.integral_hasDerivAt_right ((hf.mono hsub).intervalIntegrable)
    (hf.stronglyMeasurableAtFilter isOpen_Ioi y hy) (hf.continuousAt (Ioi_mem_nhds hy))

/-- `Λ(y) = ∫₁^y log Γ`. -/
def barnesLam (y : ℝ) : ℝ := ∫ u in (1 : ℝ)..y, Real.log (Real.Gamma u)

/-- `P(y) = ∫₁^y u log Γ(u) du`. -/
def barnesP (y : ℝ) : ℝ := ∫ u in (1 : ℝ)..y, u * Real.log (Real.Gamma u)

/-- `u ↦ u log Γ(u)` is continuous on `(0, ∞)`. -/
theorem continuousOn_mul_logGamma :
    ContinuousOn (fun u : ℝ => u * Real.log (Real.Gamma u)) (Set.Ioi 0) :=
  continuousOn_id.mul continuousOn_logGamma

/-- A function continuous on `(0, ∞)` is interval integrable between positive reals. -/
theorem intervalIntegrable_of_pos {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0)) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) : IntervalIntegrable f volume a b := by
  refine (hf.mono fun u hu => ?_).intervalIntegrable
  rcases Set.mem_uIcc.mp hu with h | h
  · show (0 : ℝ) < u; linarith [h.1]
  · show (0 : ℝ) < u; linarith [h.1]

/-- `Ψ(t) = (P(t + 1) - P(t)) - t(Λ(t + 1) - Λ(t))`, with `Λ(y) = ∫₁ʸ ln Γ` and `P(y) = ∫₁ʸ u ln
Γ(u) du`. -/
theorem barnesPsi_eq {t : ℝ} (ht : 0 < t) :
    barnesPsi t = (barnesP (t + 1) - barnesP t) - t * (barnesLam (t + 1) - barnesLam t) := by
  have h1 : barnesPsi t = ∫ u in t..t + 1, (u - t) * Real.log (Real.Gamma u) := by
    have := intervalIntegral.integral_comp_add_right
      (fun u => (u - t) * Real.log (Real.Gamma u)) t (a := 0) (b := 1)
    simp only [zero_add, add_sub_cancel_right] at this
    rw [barnesPsi, this, add_comm 1 t]
  have ht1 : 0 < t + 1 := by linarith
  have hI1 := intervalIntegrable_of_pos continuousOn_logGamma ht ht1
  have hI2 := intervalIntegrable_of_pos continuousOn_mul_logGamma ht ht1
  have h2 : ∫ u in t..t + 1, (u - t) * Real.log (Real.Gamma u) =
      (∫ u in t..t + 1, u * Real.log (Real.Gamma u)) -
        t * ∫ u in t..t + 1, Real.log (Real.Gamma u) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hI2
      (hI1.const_mul t)]
    congr 1
    ext u
    ring
  rw [h1, h2, barnesP, barnesP, barnesLam, barnesLam,
    intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_of_pos continuousOn_mul_logGamma one_pos ht1)
      (intervalIntegrable_of_pos continuousOn_mul_logGamma one_pos ht),
    intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_of_pos continuousOn_logGamma one_pos ht1)
      (intervalIntegrable_of_pos continuousOn_logGamma one_pos ht)]

/-- The function in 5.17.5. -/
def barnesD (t : ℝ) : ℝ :=
  Real.log (barnesGSucc t).re -
    ((1 / 4) * t ^ 2 + t * Real.log (Real.Gamma (t + 1)) -
      ((1 / 2) * t * (t + 1) + 1 / 12) * Real.log t - Real.log glaisherKinkelin)

/-- `D - B` in terms of `Λ` and `P`. -/
def barnesV (t : ℝ) : ℝ :=
  t / 2 * Real.log (2 * π) - 3 * t ^ 2 / 4 + t ^ 2 / 2 * Real.log t - barnesLam (t + 1) +
    ((barnesP (t + 1) - barnesP t) - t * (barnesLam (t + 1) - barnesLam t)) +
    Real.log glaisherKinkelin - Real.log (2 * π) / 4

/-- `D(t) - B(t) = V(t)` for `t > 0`. -/
theorem barnesD_sub_barnesB {t : ℝ} (ht : 0 < t) : barnesD t - barnesB t = barnesV t := by
  have hΛ : ∫ s in (0 : ℝ)..t, Real.log (Real.Gamma (s + 1)) = barnesLam (t + 1) := by
    have := intervalIntegral.integral_comp_add_right
      (fun u => Real.log (Real.Gamma u)) 1 (a := 0) (b := t)
    simp only [zero_add] at this
    rw [this, barnesLam]
  rw [barnesD, log_barnesGSucc_re ht, hΛ, barnesB, barnesPsi_eq ht, barnesV]
  ring

/-- The derivative of `V`. -/
def barnesW (t : ℝ) : ℝ :=
  Real.log (2 * π) / 2 - t + t * Real.log t - (barnesLam (t + 1) - barnesLam t)

/-- `V' = W` on `(0, ∞)`. -/
theorem hasDerivAt_barnesV {t : ℝ} (ht : 0 < t) : HasDerivAt barnesV (barnesW t) t := by
  have ht1 : 0 < t + 1 := by linarith
  have hL := hasDerivAt_integral_one continuousOn_logGamma ht
  have hL1 := (hasDerivAt_integral_one continuousOn_logGamma ht1).comp_add_const t 1
  have hP := hasDerivAt_integral_one continuousOn_mul_logGamma ht
  have hP1 := (hasDerivAt_integral_one continuousOn_mul_logGamma ht1).comp_add_const t 1
  have a1 := ((hasDerivAt_id t).div_const 2).mul_const (Real.log (2 * π))
  have a2 := ((hasDerivAt_pow 2 t).const_mul (3 : ℝ)).div_const 4
  have a3 := ((hasDerivAt_pow 2 t).div_const 2).mul (Real.hasDerivAt_log ht.ne')
  have a7 := (hasDerivAt_id t).mul (hL1.sub hL)
  have hT := (((((a1.sub a2).add a3).sub hL1).add ((hP1.sub hP).sub a7)).add_const
    (Real.log glaisherKinkelin)).sub_const (Real.log (2 * π) / 4)
  refine hT.congr_deriv ?_
  simp only [barnesW, barnesLam, id, Pi.sub_apply]
  field_simp
  ring

/-- `W' = 0` on `(0, ∞)`. -/
theorem hasDerivAt_barnesW {t : ℝ} (ht : 0 < t) : HasDerivAt barnesW 0 t := by
  have ht1 : 0 < t + 1 := by linarith
  have hL := hasDerivAt_integral_one continuousOn_logGamma ht
  have hL1 := (hasDerivAt_integral_one continuousOn_logGamma ht1).comp_add_const t 1
  have b1 := (hasDerivAt_id t).mul (Real.hasDerivAt_log ht.ne')
  have hT := (((hasDerivAt_const t (Real.log (2 * π) / 2)).sub (hasDerivAt_id t)).add b1).sub
    (hL1.sub hL)
  refine hT.congr_deriv ?_
  have hG : Real.log (Real.Gamma (t + 1)) = Real.log t + Real.log (Real.Gamma t) := by
    rw [Real.Gamma_add_one ht.ne', Real.log_mul ht.ne' (Real.Gamma_pos_of_pos ht).ne']
  simp only [id, hG]
  field_simp
  ring

/-- `V(t) = V(1) + W(1)(t - 1)` for `t > 0`. -/
theorem barnesV_eq {t : ℝ} (ht : 0 < t) :
    barnesV t = barnesV 1 + barnesW 1 * (t - 1) := by
  have hWc : ∀ t ∈ Set.Ioi (0 : ℝ), barnesW t = barnesW 1 := fun t ht =>
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun x hx => (hasDerivAt_barnesW hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hasDerivAt_barnesW hx).deriv) ht (Set.mem_Ioi.mpr one_pos)
  have hU : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun t => barnesV t - barnesW 1 * t) 0 x := by
    intro x hx
    have := (hasDerivAt_barnesV hx).sub ((hasDerivAt_id x).const_mul (barnesW 1))
    refine this.congr_deriv ?_
    rw [hWc x hx]
    simp
  have := isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun x hx => (hU x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hU x hx).deriv) (Set.mem_Ioi.mpr ht) (Set.mem_Ioi.mpr one_pos)
  linarith

/-- `D(t) = O(1/t)` as `t → ∞`. -/
theorem isBigO_barnesD :
    Asymptotics.IsBigO atTop barnesD (fun t : ℝ => t ^ (-(1 : ℝ))) := by
  set α := barnesV 1 - barnesW 1
  set β := barnesW 1
  have hDB : ∀ t : ℝ, 0 < t → barnesD t = barnesB t + (α + β * t) := by
    intro t ht
    have := barnesD_sub_barnesB ht
    rw [barnesV_eq ht] at this
    simp only [α, β]
    linarith
  have hD : Tendsto (fun n : ℕ => barnesD n) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := Real.log glaisherKinkelin)).sub tendsto_hseq
    rw [sub_self] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (barnes_nat_eq n hn).symm
  have hB : Tendsto (fun n : ℕ => barnesB n) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n : ℕ => 2 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact abs_barnesB_le (by exact_mod_cast hn)
  have hab : Tendsto (fun n : ℕ => α + β * n) atTop (𝓝 0) := by
    have h := hD.sub hB
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hDB n (by exact_mod_cast hn)]
    ring
  have hβ : β = 0 := by
    have h := ((hab.comp (tendsto_add_atTop_nat 1)).sub hab)
    rw [sub_zero] at h
    have h' : (fun n : ℕ => ((fun n : ℕ => α + β * n) ∘ fun n => n + 1) n - (α + β * n)) =
        fun _ => β := by
      ext n; simp only [Function.comp_apply]; push_cast; ring
    rw [h'] at h
    exact tendsto_nhds_unique tendsto_const_nhds h
  have hα : α = 0 := by
    simp only [hβ, zero_mul, add_zero] at hab
    exact tendsto_nhds_unique tendsto_const_nhds hab
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : 0 < t := by linarith
  rw [hDB t ht0, hα, hβ, zero_mul, add_zero, add_zero, Real.rpow_neg_one, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
  simpa [div_eq_mul_inv] using abs_barnesB_le ht

end BarnesAsymp

/-- DLMF 5.17.5 (in the form used here): `ln G(t + 1) = t²/4 + t ln Γ(t + 1) - (t(t+1)/2 + 1/12) ln
t - ln A + O(1/t)` as `t → ∞`. -/
@[dlmf 5.17.E5]
theorem log_barnesG_asymptotic :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Real.log (barnesGSucc t).re -
        ((1 / 4) * t ^ 2 + t * Real.log (Real.Gamma (t + 1)) -
          ((1 / 2) * t * (t + 1) + 1 / 12) * Real.log t -
          Real.log glaisherKinkelin))
      (fun t : ℝ => (t : ℝ) ^ (-(1 : ℝ))) :=
  BarnesAsymp.isBigO_barnesD

end DLMF.Gamma

end
end
