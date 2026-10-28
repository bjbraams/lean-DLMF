/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Volterra integral equations for perturbed oscillators

For the perturbed oscillator `u'' + ω² u = g u` on an interval `[a, b]` (with `u` taking values
in a real Banach space and `g` real and continuous) we prove the variation-of-constants
formula

`u x = u₀ x + ω⁻¹ ∫_a^x sin (ω (x - t)) g t u t dt`,

where `u₀ = oscFree ω a (u a) (u' a)` is the free oscillation with the same data at `a`, and
the Gronwall-type estimate

`‖u x - u₀ x‖ ≤ M (exp ((∫_a^x |g|) / |ω|) - 1)`

whenever `‖u₀‖ ≤ M` on `[a, b]` (Beals–Wong, §13.1). This is the basic tool for
large-parameter asymptotics of solutions of second-order equations. A solution is described
by functions `u` and `u'` with `HasDerivAt u (u' t) t` and
`HasDerivAt u' ((g t - ω ^ 2) • u t) t` on `[a, b]`; no existence theory is used.

## Main results

* `ODE.add_integral_le_mul_exp_integral`: Gronwall's inequality in integral form.
* `ODE.eq_oscFree_add_integral`: the Volterra integral equation.
* `ODE.norm_sub_oscFree_le`: the perturbation estimate, and `ODE.norm_sub_oscFree_le'` with
  `M = ‖u a‖ + ‖u' a‖ / |ω|`.
* `ODE.exists_norm_sub_oscillation_le`: on a half-line with `∫_a^∞ |g| < ∞`, every solution is
  `cos (ω x) A + sin (ω x) B + O(∫_x^∞ |g|)`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace ODE

/-! ### Gronwall's inequality in integral form -/

/-- **Gronwall's inequality** in integral form: if `φ ≤ M + ∫_a^t h φ` on `[a, b]` with
`h ≥ 0`, then `M + ∫_a^x h φ ≤ M exp (∫_a^x h)`, and in particular `φ x ≤ M exp (∫_a^x h)`. -/
theorem add_integral_le_mul_exp_integral {a b M : ℝ} {φ h : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc a b)) (hh : ContinuousOn h (Icc a b))
    (hh0 : ∀ t ∈ Icc a b, 0 ≤ h t)
    (hle : ∀ t ∈ Icc a b, φ t ≤ M + ∫ s in a..t, h s * φ s) {x : ℝ} (hx : x ∈ Icc a b) :
    M + ∫ s in a..x, h s * φ s ≤ M * Real.exp (∫ s in a..x, h s) := by
  have hab : a ≤ b := hx.1.trans hx.2
  set Ψ : ℝ → ℝ := fun t => ∫ s in a..t, h s * φ s with hΨ
  set H : ℝ → ℝ := fun t => ∫ s in a..t, h s with hH
  set F : ℝ → ℝ := fun t => (M + Ψ t) * Real.exp (-H t) with hF
  have hhφ : ContinuousOn (fun s => h s * φ s) (Icc a b) := hh.mul hφ
  have hprim : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc a b) →
      ContinuousOn (fun t => ∫ s in a..t, f s) (Icc a b) := by
    intro f hf
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := a) (b := b)
      (f := f) (by rw [uIcc_of_le hab]; exact hf.integrableOn_compact isCompact_Icc)
    rwa [uIcc_of_le hab] at this
  have hderiv : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc a b) → ∀ t ∈ Ioo a b,
      HasDerivAt (fun t => ∫ s in a..t, f s) (f t) t := by
    intro f hf t ht
    exact intervalIntegral.integral_hasDerivAt_right
      ((hf.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
      ((hf.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
      (hf.continuousAt (Icc_mem_nhds ht.1 ht.2))
  have hFd : ∀ t ∈ Ioo a b, HasDerivAt F
      (h t * φ t * Real.exp (-H t) + (M + Ψ t) * (Real.exp (-H t) * -h t)) t := by
    intro t ht
    exact ((hderiv hhφ t ht).const_add M).mul (hderiv hh t ht).neg.exp
  have hanti : AntitoneOn F (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    · exact ((hprim hhφ).const_add M).mul (hprim hh).neg.rexp
    · intro t ht
      rw [interior_Icc] at ht
      exact (hFd t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hFd t ht).deriv]
      have h1 := hle t (Ioo_subset_Icc_self ht)
      have h2 := hh0 t (Ioo_subset_Icc_self ht)
      have h3 := Real.exp_pos (-H t)
      have : h t * φ t * Real.exp (-H t) + (M + Ψ t) * (Real.exp (-H t) * -h t) =
          h t * Real.exp (-H t) * (φ t - (M + Ψ t)) := by ring
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg h2 h3.le) (by linarith)
  have hFa : F a = M := by simp [hF, hΨ, hH]
  have hle' : F x ≤ M := hFa ▸ hanti ⟨le_rfl, hab⟩ hx hx.1
  have hexp : Real.exp (-H x) * Real.exp (H x) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc M + Ψ x = (M + Ψ x) * Real.exp (-H x) * Real.exp (H x) := by
        rw [mul_assoc, hexp, mul_one]
    _ ≤ M * Real.exp (H x) := by gcongr

/-! ### The perturbed oscillator -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The free oscillation `cos (ω (x - a)) c + (sin (ω (x - a)) / ω) d`, the solution of
`u'' + ω² u = 0` with `u a = c` and `u' a = d`. -/
noncomputable def oscFree (ω a : ℝ) (c d : E) (x : ℝ) : E :=
  Real.cos (ω * (x - a)) • c + (Real.sin (ω * (x - a)) / ω) • d

/-- Identity under the stated parameter and domain assumptions: `oscFree ω a c d a = c`. -/
theorem oscFree_self (ω a : ℝ) (c d : E) : oscFree ω a c d a = c := by
  simp [oscFree]

/-- Estimate under the stated parameter and domain assumptions: `‖oscFree ω a c d x‖ ≤ ‖c‖ + ‖d‖ /
|ω|`. -/
theorem norm_oscFree_le (ω a : ℝ) (c d : E) (x : ℝ) :
    ‖oscFree ω a c d x‖ ≤ ‖c‖ + ‖d‖ / |ω| := by
  unfold oscFree
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)
  · rw [norm_smul, Real.norm_eq_abs, abs_div, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)) (abs_nonneg ω)

/-- **Variation of constants** for `u'' + ω² u = g u`: the Volterra integral equation
`u x = u₀ x + ω⁻¹ ∫_a^x sin (ω (x - t)) g t u t dt`. -/
theorem eq_oscFree_add_integral [CompleteSpace E] {a b ω : ℝ} (hω : ω ≠ 0) {g : ℝ → ℝ}
    {u u' : ℝ → E}
    (hg : ContinuousOn g (Icc a b))
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u' t) t)
    (hu' : ∀ t ∈ Icc a b, HasDerivAt u' ((g t - ω ^ 2) • u t) t) {x : ℝ}
    (hx : x ∈ Icc a b) :
    u x = oscFree ω a (u a) (u' a) x +
      ω⁻¹ • ∫ t in a..x, (Real.sin (ω * (x - t)) * g t) • u t := by
  have hax : a ≤ x := hx.1
  have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
  have huc : ContinuousOn u (Icc a b) := fun t ht => (hu t ht).continuousAt.continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => Real.sin (ω * (x - t)) • u' t + (ω * Real.cos (ω * (x - t))) • u t)
    (f' := fun t => (Real.sin (ω * (x - t)) * g t) • u t) (a := a) (b := x) ?_ ?_
  · simp only [sub_self, mul_zero, Real.sin_zero, zero_smul, Real.cos_zero, mul_one,
      zero_add] at hFTC
    rw [hFTC, oscFree, smul_sub, smul_add, smul_smul, smul_smul, smul_smul,
      inv_mul_cancel₀ hω, one_smul, show ω⁻¹ * (ω * Real.cos (ω * (x - a))) =
        Real.cos (ω * (x - a)) by field_simp,
      show ω⁻¹ * Real.sin (ω * (x - a)) = Real.sin (ω * (x - a)) / ω by ring]
    abel
  · intro t ht
    rw [uIcc_of_le hax] at ht
    have htb := hsub ht
    have h1 : HasDerivAt (fun t => ω * (x - t)) (ω * (-1)) t :=
      ((hasDerivAt_id t).const_sub x).const_mul ω
    have := (h1.sin.smul (hu' t htb)).add ((h1.cos.const_mul ω).smul (hu t htb))
    convert this using 1
    simp only [smul_smul]
    module
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hax]
    refine ContinuousOn.smul (ContinuousOn.mul ?_ (hg.mono hsub)) (huc.mono hsub)
    exact (Real.continuous_sin.comp (continuous_const.mul
      (continuous_const.sub continuous_id))).continuousOn

/-- **The perturbation estimate** for `u'' + ω² u = g u`: if the free oscillation `u₀` with
the data of `u` at `a` is bounded by `M` on `[a, b]`, then
`‖u x - u₀ x‖ ≤ M (exp ((∫_a^x |g|) / |ω|) - 1)` on `[a, b]` (Beals–Wong, §13.1). -/
theorem norm_sub_oscFree_le [CompleteSpace E] {a b ω M : ℝ} (hω : ω ≠ 0) {g : ℝ → ℝ} {u u' : ℝ → E}
    (hg : ContinuousOn g (Icc a b))
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u' t) t)
    (hu' : ∀ t ∈ Icc a b, HasDerivAt u' ((g t - ω ^ 2) • u t) t)
    (hM : ∀ t ∈ Icc a b, ‖oscFree ω a (u a) (u' a) t‖ ≤ M) {x : ℝ} (hx : x ∈ Icc a b) :
    ‖u x - oscFree ω a (u a) (u' a) x‖ ≤
      M * (Real.exp ((∫ t in a..x, |g t|) / |ω|) - 1) := by
  set h : ℝ → ℝ := fun t => |g t| / |ω| with hh
  set φ : ℝ → ℝ := fun t => ‖u t‖ with hφ
  have huc : ContinuousOn u (Icc a b) := fun t ht => (hu t ht).continuousAt.continuousWithinAt
  have hφc : ContinuousOn φ (Icc a b) := huc.norm
  have hhc : ContinuousOn h (Icc a b) := hg.abs.div_const _
  have key : ∀ t ∈ Icc a b,
      ‖u t - oscFree ω a (u a) (u' a) t‖ ≤ ∫ s in a..t, h s * φ s := by
    intro t ht
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    have heq := eq_oscFree_add_integral hω hg hu hu' ht
    have hcs : ContinuousOn (fun s => (Real.sin (ω * (t - s)) * g s) • u s) (Icc a t) :=
      ((Real.continuous_sin.comp (continuous_const.mul
        (continuous_const.sub continuous_id))).continuousOn.mul (hg.mono hsub)).smul
        (huc.mono hsub)
    calc ‖u t - oscFree ω a (u a) (u' a) t‖
        = |ω|⁻¹ * ‖∫ s in a..t, (Real.sin (ω * (t - s)) * g s) • u s‖ := by
          rw [heq, add_sub_cancel_left, norm_smul, norm_inv, Real.norm_eq_abs]
      _ ≤ |ω|⁻¹ * ∫ s in a..t, |g s| * φ s := by
          gcongr
          refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
          refine intervalIntegral.integral_mono_on ht.1
            (hcs.norm.intervalIntegrable_of_Icc ht.1)
            (((hg.mono hsub).abs.mul (hφc.mono hsub)).intervalIntegrable_of_Icc ht.1) ?_
          intro s _
          rw [norm_smul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right
            (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)) (norm_nonneg _)
      _ = ∫ s in a..t, h s * φ s := by
          rw [← intervalIntegral.integral_const_mul]
          congr 1
          ext s
          simp only [hh, hφ]
          ring
  have hle : ∀ t ∈ Icc a b, φ t ≤ M + ∫ s in a..t, h s * φ s := fun t ht =>
    (norm_le_norm_add_norm_sub' (u t) (oscFree ω a (u a) (u' a) t)).trans
      (add_le_add (hM t ht) (key t ht))
  have hgr := add_integral_le_mul_exp_integral hφc hhc
    (fun t _ => div_nonneg (abs_nonneg _) (abs_nonneg _)) hle hx
  have hHx : ∫ s in a..x, h s = (∫ t in a..x, |g t|) / |ω| := intervalIntegral.integral_div _ _
  rw [hHx] at hgr
  calc ‖u x - oscFree ω a (u a) (u' a) x‖ ≤ ∫ s in a..x, h s * φ s := key x hx
    _ ≤ M * (Real.exp ((∫ t in a..x, |g t|) / |ω|) - 1) := by linarith

/-- The perturbation estimate with the bound `M = ‖u a‖ + ‖u' a‖ / |ω|` for the free
oscillation. -/
theorem norm_sub_oscFree_le' [CompleteSpace E] {a b ω : ℝ} (hω : ω ≠ 0) {g : ℝ → ℝ} {u u' : ℝ → E}
    (hg : ContinuousOn g (Icc a b))
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u' t) t)
    (hu' : ∀ t ∈ Icc a b, HasDerivAt u' ((g t - ω ^ 2) • u t) t) {x : ℝ}
    (hx : x ∈ Icc a b) :
    ‖u x - oscFree ω a (u a) (u' a) x‖ ≤
      (‖u a‖ + ‖u' a‖ / |ω|) * (Real.exp ((∫ t in a..x, |g t|) / |ω|) - 1) :=
  norm_sub_oscFree_le hω hg hu hu' (fun t _ => norm_oscFree_le ω a (u a) (u' a) t) hx

/-! ### The half-line -/

/-- **Asymptotically free oscillation** on a half-line (Beals–Wong, §13.1): if `g` is
integrable on `(a, ∞)`, every solution of `u'' + ω² u = g u` on `[a, ∞)` is a free
oscillation `cos (ω x) A + sin (ω x) B` up to an error `O(∫_x^∞ |g|)`. -/
theorem exists_norm_sub_oscillation_le [CompleteSpace E] {a ω : ℝ} (hω : 0 < ω) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici a)) (hgi : IntegrableOn g (Ioi a)) {u u' : ℝ → E}
    (hu : ∀ t ∈ Ici a, HasDerivAt u (u' t) t)
    (hu' : ∀ t ∈ Ici a, HasDerivAt u' ((g t - ω ^ 2) • u t) t) :
    ∃ A B : E, ∃ K : ℝ, ∀ x, a ≤ x →
      ‖u x - (Real.cos (ω * x) • A + Real.sin (ω * x) • B)‖ ≤ K * ∫ t in Ioi x, |g t| := by
  have hωne : ω ≠ 0 := hω.ne'
  set M0 := ‖u a‖ + ‖u' a‖ / |ω| with hM0
  set G := ∫ t in Ioi a, |g t| with hG
  set U := M0 * Real.exp (G / |ω|) with hU
  have hM0nn : 0 ≤ M0 := by positivity
  have huc : ContinuousOn u (Ici a) := fun t ht => (hu t ht).continuousAt.continuousWithinAt
  -- a uniform bound for `u`
  have hbound : ∀ t, a ≤ t → ‖u t‖ ≤ U := by
    intro t ht
    have hsub : Icc a t ⊆ Ici a := Icc_subset_Ici_self
    have h := norm_sub_oscFree_le' hωne (hg.mono hsub) (fun s hs => hu s (hsub hs))
      (fun s hs => hu' s (hsub hs)) (b := t) ⟨ht, le_rfl⟩
    have hint : ∫ s in a..t, |g s| ≤ G := by
      rw [intervalIntegral.integral_of_le ht]
      exact setIntegral_mono_set hgi.abs (ae_restrict_of_forall_mem measurableSet_Ioi
        fun s _ => abs_nonneg _) (Ioc_subset_Ioi_self.eventuallyLE)
    have hexp : Real.exp ((∫ s in a..t, |g s|) / |ω|) ≤ Real.exp (G / |ω|) :=
      Real.exp_le_exp.2 (div_le_div_of_nonneg_right hint (abs_nonneg ω))
    calc ‖u t‖ ≤ ‖oscFree ω a (u a) (u' a) t‖ + ‖u t - oscFree ω a (u a) (u' a) t‖ :=
          norm_le_norm_add_norm_sub' _ _
      _ ≤ M0 + M0 * (Real.exp ((∫ s in a..t, |g s|) / |ω|) - 1) :=
          add_le_add (norm_oscFree_le _ _ _ _ _) h
      _ ≤ U := by rw [hU]; nlinarith
  -- the forcing `f = g u` is integrable on `(a, ∞)`
  set f : ℝ → E := fun t => g t • u t with hf
  have hfc : ContinuousOn f (Ici a) := hg.smul huc
  have hfi : ∀ c : ℝ → ℝ, Continuous c → (∀ t, |c t| ≤ 1) →
      IntegrableOn (fun t => c t • f t) (Ioi a) := by
    intro c hc hc1
    refine Integrable.mono' (hgi.norm.mul_const U)
      (((hc.continuousOn.smul hfc).mono Ioi_subset_Ici_self).aestronglyMeasurable
        measurableSet_Ioi) (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    rw [norm_smul, hf, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |c t| * (|g t| * ‖u t‖) ≤ 1 * (|g t| * U) := by
          gcongr
          · exact hc1 t
          · exact hbound t (le_of_lt ht)
      _ = ‖g t‖ * U := by rw [one_mul, Real.norm_eq_abs]
  set Cc := ∫ t in Ioi a, Real.cos (ω * t) • f t
  set Ss := ∫ t in Ioi a, Real.sin (ω * t) • f t
  refine ⟨Real.cos (ω * a) • u a - (Real.sin (ω * a) / ω) • u' a - ω⁻¹ • Ss,
    Real.sin (ω * a) • u a + (Real.cos (ω * a) / ω) • u' a + ω⁻¹ • Cc, 2 * U / ω, ?_⟩
  intro x hx
  have hsub : Icc a x ⊆ Ici a := Icc_subset_Ici_self
  have hV := eq_oscFree_add_integral hωne (hg.mono hsub) (fun s hs => hu s (hsub hs))
    (fun s hs => hu' s (hsub hs)) (b := x) ⟨hx, le_rfl⟩
  -- split the integrals at `x`
  have hsplit : ∀ c : ℝ → ℝ, Continuous c → (∀ t, |c t| ≤ 1) →
      ∫ t in a..x, c t • f t =
        (∫ t in Ioi a, c t • f t) - ∫ t in Ioi x, c t • f t := by
    intro c hc hc1
    have hi := hfi c hc hc1
    rw [intervalIntegral.integral_of_le hx, ← Ioc_union_Ioi_eq_Ioi hx,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hi.mono_set (Ioc_subset_Ioi_self)) (hi.mono_set (Ioi_subset_Ioi hx))]
    abel
  have hfcx : ContinuousOn f (uIcc a x) := by rw [uIcc_of_le hx]; exact hfc.mono hsub
  have hii : ∀ c : ℝ → ℝ, Continuous c → ∀ k : ℝ,
      IntervalIntegrable (fun t => k • (c t • f t)) volume a x := fun c hc k =>
    (continuousOn_const.smul (hc.continuousOn.smul hfcx)).intervalIntegrable
  have hker : ∫ t in a..x, (Real.sin (ω * (x - t)) * g t) • u t =
      Real.sin (ω * x) • (∫ t in a..x, Real.cos (ω * t) • f t) -
        Real.cos (ω * x) • ∫ t in a..x, Real.sin (ω * t) • f t := by
    rw [← intervalIntegral.integral_smul, ← intervalIntegral.integral_smul,
      ← intervalIntegral.integral_sub (hii _ (by fun_prop) _) (hii _ (by fun_prop) _)]
    congr 1
    ext t
    simp only [hf, mul_sub, Real.sin_sub, smul_smul]
    module
  have hR : ∀ c : ℝ → ℝ, Continuous c → (∀ t, |c t| ≤ 1) →
      ‖∫ t in Ioi x, c t • f t‖ ≤ U * ∫ t in Ioi x, |g t| := by
    intro c hc hc1
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le ((hgi.mono_set (Ioi_subset_Ioi hx)).abs.const_mul U)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    rw [norm_smul, hf, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |c t| * (|g t| * ‖u t‖) ≤ 1 * (|g t| * U) := by
          gcongr
          · exact hc1 t
          · exact hbound t (hx.trans (le_of_lt ht))
      _ = U * |g t| := by ring
  have hRc := hR (fun t => Real.cos (ω * t)) (by fun_prop) (fun t => Real.abs_cos_le_one _)
  have hRs := hR (fun t => Real.sin (ω * t)) (by fun_prop) (fun t => Real.abs_sin_le_one _)
  have hid : u x - (Real.cos (ω * x) •
        (Real.cos (ω * a) • u a - (Real.sin (ω * a) / ω) • u' a - ω⁻¹ • Ss) +
        Real.sin (ω * x) •
          (Real.sin (ω * a) • u a + (Real.cos (ω * a) / ω) • u' a + ω⁻¹ • Cc)) =
      ω⁻¹ • (Real.cos (ω * x) • (∫ t in Ioi x, Real.sin (ω * t) • f t) -
        Real.sin (ω * x) • ∫ t in Ioi x, Real.cos (ω * t) • f t) := by
    rw [hV, hker, hsplit _ (by fun_prop) (fun t => Real.abs_cos_le_one _),
      hsplit _ (by fun_prop) (fun t => Real.abs_sin_le_one _), oscFree, mul_sub, Real.cos_sub,
      Real.sin_sub]
    module
  rw [hid, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hω]
  have hU0 : 0 ≤ U := by positivity
  calc ω⁻¹ * ‖Real.cos (ω * x) • (∫ t in Ioi x, Real.sin (ω * t) • f t) -
        Real.sin (ω * x) • ∫ t in Ioi x, Real.cos (ω * t) • f t‖
      ≤ ω⁻¹ * (U * (∫ t in Ioi x, |g t|) + U * ∫ t in Ioi x, |g t|) := by
        gcongr
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_eq_abs]
          exact (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)).trans hRs
        · rw [norm_smul, Real.norm_eq_abs]
          exact (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)).trans hRc
    _ = 2 * U / ω * ∫ t in Ioi x, |g t| := by
        field_simp
        ring

end ODE
