/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.LiouvilleGreenEndpoint
public import DLMFMathlib.Analysis.ODE.LinearInterval
public import DLMFMathlib.Analysis.Calculus.LHopitalInfinity

/-!
# Dominant solutions complementary to a recessive Liouville–Green solution

An independent interior initial condition normalizes the Wronskian to one. The quotient by
the recessive solution then has derivative `1/u²`. L'Hôpital's rule identifies its leading
exponential term. See Olver, *Asymptotics and Special Functions*, Chapter 6, §2.
-/

@[expose] public section

open Set Filter Topology

namespace LiouvilleGreen.Interval

/-- A recessive right-endpoint solution has a dominant companion with the reciprocal
exponential leading term. -/
theorem exists_dominant_of_recessive {a b : ℝ} (hab : a < b) {A ξ q u u' : ℝ → ℝ}
    (hA : ∀ x ∈ Ioo a b, 0 < A x)
    (hξ : ∀ x ∈ Ioo a b, HasDerivAt ξ ((A x ^ 2)⁻¹) x)
    (hξtop : Tendsto ξ (𝓝[<] b) atTop) (hq : ContinuousOn q (Ioo a b))
    (hu : ∀ x ∈ Ioo a b, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Ioo a b, HasDerivAt u' (q x * u x) x)
    (hue : Tendsto (fun x => u x / (A x * Real.exp (-ξ x))) (𝓝[<] b) (𝓝 1)) :
    ∃ w w' : ℝ → ℝ,
      (∀ x ∈ Ioo a b, HasDerivAt w (w' x) x ∧ HasDerivAt w' (q x * w x) x) ∧
      Tendsto (fun x => w x / (A x * Real.exp (ξ x))) (𝓝[<] b) (𝓝 1) ∧
      Tendsto (fun x => u x / w x) (𝓝[<] b) (𝓝 0) := by
  have hune : ∀ᶠ x in 𝓝[<] b, u x ≠ 0 := by
    filter_upwards [hue.eventually_const_lt zero_lt_one] with x hx
    intro hxu
    simp [hxu] at hx
  obtain ⟨c, hcu, hc⟩ := (hune.and (Ioo_mem_nhdsLT hab)).exists
  obtain ⟨v, v', hv0, hv1, hv⟩ := ODE.exists_linear_ode_Ioo hc
    (p := fun _ => (0 : ℝ)) continuousOn_const hq (0 : ℝ) (u c)⁻¹
  let Ω : ℝ → ℝ := fun x => u x * v' x - u' x * v x
  have hΩd : ∀ x ∈ Ioo a b, HasDerivAt Ω 0 x := by
    intro x hx
    exact (((hu x hx).mul (by simpa using (hv x hx).2)).sub
      ((hu' x hx).mul (hv x hx).1)).congr_deriv (by ring)
  have hΩ : ∀ x ∈ Ioo a b, Ω x = 1 := by
    intro x hx
    have hh := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
      (fun z hz => (hΩd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hΩd z hz).deriv) hx hc
    rw [hh]
    dsimp [Ω]
    rw [hv0, hv1, mul_zero, sub_zero, mul_inv_cancel₀ hcu]
  let F : ℝ → ℝ := fun x => v x / u x
  let G : ℝ → ℝ := fun x => Real.exp (2 * ξ x)
  have hFd : ∀ x ∈ Ioo a b, u x ≠ 0 → HasDerivAt F ((u x ^ 2)⁻¹) x := by
    intro x hx hxu
    refine ((hv x hx).1.div (hu x hx) hxu).congr_deriv ?_
    have hh := hΩ x hx
    dsimp [Ω] at hh
    rw [inv_eq_one_div]
    congr 1
    linear_combination hh
  have hGd : ∀ x ∈ Ioo a b,
      HasDerivAt G (2 * (A x ^ 2)⁻¹ * G x) x := by
    intro x hx
    exact ((hξ x hx).const_mul 2).exp.congr_deriv (by dsimp [G]; ring)
  have hGpos : ∀ x, 0 < G x := fun x => Real.exp_pos _
  have hGtop : Tendsto (fun x => |G x|) (𝓝[<] b) atTop := by
    simpa only [abs_of_pos (hGpos _), G, Function.comp_def] using Real.tendsto_exp_atTop.comp
      (hξtop.const_mul_atTop' (show (0 : ℝ) < 2 by norm_num))
  have hdiv : Tendsto (fun x => deriv F x / deriv G x) (𝓝[<] b) (𝓝 (1 / 2)) := by
    have ht : Tendsto
        (fun x => (2 * (u x / (A x * Real.exp (-ξ x))) ^ 2)⁻¹)
        (𝓝[<] b) (𝓝 (1 / 2)) := by
      simpa using ((hue.pow 2).const_mul 2).inv₀ (by norm_num)
    refine ht.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hab, hune] with x hx hxu
    rw [(hFd x hx hxu).deriv, (hGd x hx).deriv]
    have hAx := (hA x hx).ne'
    have hEx := (Real.exp_pos (ξ x)).ne'
    dsimp [G]
    rw [show 2 * ξ x = ξ x + ξ x by ring, Real.exp_add, Real.exp_neg]
    field_simp
  have hlim : Tendsto (fun x => F x / G x) (𝓝[<] b) (𝓝 (1 / 2)) := by
    refine deriv.lhopital_infty_nhdsLT ?_ ?_ ?_ hGtop hdiv
    · filter_upwards [Ioo_mem_nhdsLT hab, hune] with x hx hxu
      exact (hFd x hx hxu).differentiableAt
    · filter_upwards [Ioo_mem_nhdsLT hab] with x hx
      exact (hGd x hx).differentiableAt
    · filter_upwards [Ioo_mem_nhdsLT hab] with x hx
      rw [(hGd x hx).deriv]
      exact (mul_pos (mul_pos (by norm_num) (inv_pos.2 (sq_pos_of_pos (hA x hx))))
        (hGpos x)).ne'
  have hdom : Tendsto (fun x => 2 * v x / (A x * Real.exp (ξ x)))
      (𝓝[<] b) (𝓝 1) := by
    have ht := (hlim.mul hue).const_mul 2
    norm_num at ht
    refine ht.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hab, hune] with x hx hxu
    have hAx := (hA x hx).ne'
    have hEx := (Real.exp_pos (ξ x)).ne'
    dsimp [F, G]
    rw [show 2 * ξ x = ξ x + ξ x by ring, Real.exp_add, Real.exp_neg]
    field_simp
  have hwne : ∀ᶠ x in 𝓝[<] b, 2 * v x ≠ 0 := by
    filter_upwards [hdom.eventually_const_lt zero_lt_one] with x hx
    intro hwx
    simp [hwx] at hx
  refine ⟨fun x => 2 * v x, fun x => 2 * v' x, ?_, hdom, ?_⟩
  · intro x hx
    refine ⟨((hv x hx).1.const_mul 2), ?_⟩
    exact ((hv x hx).2.const_mul 2).congr_deriv (by simp; ring)
  · have hExp : Tendsto (fun x => Real.exp (-(2 * ξ x))) (𝓝[<] b) (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (hξtop.const_mul_atTop' (show (0 : ℝ) < 2 by norm_num))
    have ht := (hue.div hdom one_ne_zero).mul hExp
    norm_num at ht
    refine ht.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hab, hwne] with x hx hwx
    have hAx := (hA x hx).ne'
    have hEx := (Real.exp_pos (ξ x)).ne'
    rw [show -(2 * ξ x) = -(ξ x) + -(ξ x) by ring, Real.exp_add, Real.exp_neg]
    field_simp


/-- The dominant companion at a left endpoint, obtained by reflection. -/
theorem exists_dominant_of_recessive_left {a b : ℝ} (hab : a < b) {A ξ q u u' : ℝ → ℝ}
    (hA : ∀ x ∈ Ioo a b, 0 < A x)
    (hξ : ∀ x ∈ Ioo a b, HasDerivAt ξ ((A x ^ 2)⁻¹) x)
    (hξbot : Tendsto ξ (𝓝[>] a) atBot) (hq : ContinuousOn q (Ioo a b))
    (hu : ∀ x ∈ Ioo a b, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Ioo a b, HasDerivAt u' (q x * u x) x)
    (hue : Tendsto (fun x => u x / (A x * Real.exp (ξ x))) (𝓝[>] a) (𝓝 1)) :
    ∃ w w' : ℝ → ℝ,
      (∀ x ∈ Ioo a b, HasDerivAt w (w' x) x ∧ HasDerivAt w' (q x * w x) x) ∧
      Tendsto (fun x => w x / (A x * Real.exp (-ξ x))) (𝓝[>] a) (𝓝 1) ∧
      Tendsto (fun x => u x / w x) (𝓝[>] a) (𝓝 0) := by
  have hneg : ∀ x ∈ Ioo (-b) (-a), -x ∈ Ioo a b := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hξR : ∀ x ∈ Ioo (-b) (-a),
      HasDerivAt (fun t => -ξ (-t)) (((A (-x)) ^ 2)⁻¹) x := by
    intro x hx
    convert ((hξ (-x) (hneg x hx)).comp x (hasDerivAt_neg x)).neg using 1 <;>
      simp [Function.comp_def, funext_iff]
  have huR : ∀ x ∈ Ioo (-b) (-a), HasDerivAt (fun t => u (-t)) (-u' (-x)) x := by
    intro x hx
    simpa [Function.comp_def] using (hu (-x) (hneg x hx)).comp x (hasDerivAt_neg x)
  have huR' : ∀ x ∈ Ioo (-b) (-a),
      HasDerivAt (fun t => -u' (-t)) (q (-x) * u (-x)) x := by
    intro x hx
    convert ((hu' (-x) (hneg x hx)).comp x (hasDerivAt_neg x)).neg using 1 <;>
      simp [Function.comp_def, funext_iff]
  have hnt : Tendsto (fun x : ℝ => -x) (𝓝[<] (-a)) (𝓝[>] a) :=
    tendsto_neg_nhdsLT_neg
  have hξRtop : Tendsto (fun x => -ξ (-x)) (𝓝[<] (-a)) atTop :=
    tendsto_neg_atBot_atTop.comp (hξbot.comp hnt)
  have hueR : Tendsto (fun x => u (-x) / (A (-x) * Real.exp (-(-ξ (-x)))))
      (𝓝[<] (-a)) (𝓝 1) := by
    simpa only [neg_neg, Function.comp_def] using hue.comp hnt
  obtain ⟨w, w', hw, hwe, hur⟩ := exists_dominant_of_recessive (neg_lt_neg hab)
    (fun x hx => hA (-x) (hneg x hx)) hξR hξRtop
    (hq.comp continuous_neg.continuousOn hneg) huR huR' hueR
  have hnt' : Tendsto (fun x : ℝ => -x) (𝓝[>] a) (𝓝[<] (-a)) :=
    by simpa only [neg_neg] using (tendsto_neg_nhdsGT_neg (a := -a))
  refine ⟨fun x => w (-x), fun x => -w' (-x), ?_, ?_, ?_⟩
  · intro x hx
    have hxR : -x ∈ Ioo (-b) (-a) := ⟨neg_lt_neg hx.2, neg_lt_neg hx.1⟩
    refine ⟨?_, ?_⟩
    · simpa [Function.comp_def] using (hw (-x) hxR).1.comp x (hasDerivAt_neg x)
    · convert ((hw (-x) hxR).2.comp x (hasDerivAt_neg x)).neg using 1 <;>
        simp [Function.comp_def, funext_iff]
  · simpa only [Function.comp_def, neg_neg] using hwe.comp hnt'
  · simpa only [Function.comp_def, neg_neg] using hur.comp hnt'

end LiouvilleGreen.Interval
