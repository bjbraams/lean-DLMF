/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.LiouvilleGreenInterval
public import DLMFMathlib.Analysis.ODE.PowerSeriesUniqueness

/-!
# Uniqueness of a recessive solution at a singular endpoint

A Wronskian argument characterizes the solution recessive relative to a positive amplitude.
The phase derivative is the inverse square of that amplitude and the phase diverges at the
right endpoint. This is the uniqueness argument of Olver, *Asymptotics and Special Functions*,
Chapter 6, §2, expressed directly in the original independent variable.
-/

@[expose] public section

open Set Filter Topology

namespace LiouvilleGreen.Interval

/-- A solution negligible relative to the amplitude is uniquely determined by its leading
coefficient at a singular right endpoint. -/
theorem eqOn_of_recessive_ratio {a b : ℝ} (hab : a < b) {A ξ q u u' v v' : ℝ → ℝ}
    (hA : ∀ x ∈ Ioo a b, 0 < A x)
    (hξ : ∀ x ∈ Ioo a b, HasDerivAt ξ ((A x ^ 2)⁻¹) x)
    (hξtop : Tendsto ξ (𝓝[<] b) atTop) (hq : ContinuousOn q (Ioo a b))
    (hu : ∀ x ∈ Ioo a b, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Ioo a b, HasDerivAt u' (q x * u x) x)
    (hv : ∀ x ∈ Ioo a b, HasDerivAt v (v' x) x)
    (hv' : ∀ x ∈ Ioo a b, HasDerivAt v' (q x * v x) x)
    (hune : ∀ᶠ x in 𝓝[<] b, u x ≠ 0)
    (hsmall : Tendsto (fun x => u x / A x) (𝓝[<] b) (𝓝 0))
    (hratio : Tendsto (fun x => v x / u x) (𝓝[<] b) (𝓝 1)) :
    EqOn v u (Ioo a b) := by
  let Ω : ℝ → ℝ := fun x => u x * v' x - u' x * v x
  have hΩd : ∀ x ∈ Ioo a b, HasDerivAt Ω 0 x := by
    intro x hx
    exact (((hu x hx).mul (hv' x hx)).sub ((hu' x hx).mul (hv x hx))).congr_deriv
      (by ring)
  have hΩ : ∀ {x y : ℝ}, x ∈ Ioo a b → y ∈ Ioo a b → Ω x = Ω y := by
    intro x y hx hy
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
      (fun z hz => (hΩd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hΩd z hz).deriv) hx hy
  have he : ∀ᶠ x in 𝓝[<] b, x ∈ Ioo a b ∧ u x ≠ 0 ∧ u x ^ 2 ≤ A x ^ 2 := by
    have hs := hsmall.eventually (Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [Ioo_mem_nhdsLT hab, hune, hs] with x hx hxu hxs
    refine ⟨hx, hxu, ?_⟩
    have ha := hA x hx
    have h₁ : -A x < u x := by simpa using (lt_div_iff₀ ha).1 hxs.1
    have h₂ : u x < A x := by simpa using (div_lt_iff₀ ha).1 hxs.2
    nlinarith [sq_nonneg (A x - u x), sq_nonneg (A x + u x)]
  obtain ⟨c, hcb, hc⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 he
  change c < b at hcb
  let d := (max a c + b) / 2
  have hdb : d < b := by dsimp [d]; have := max_lt hab hcb; linarith
  have had : a < d := by dsimp [d]; have := le_max_left a c; linarith
  have hcd : c < d := by
    dsimp [d]
    have := le_max_right a c
    have := max_lt hab hcb
    linarith
  have hd : d ∈ Ioo a b := ⟨had, hdb⟩
  have hgood : ∀ x ∈ Ioo d b, x ∈ Ioo a b ∧ u x ≠ 0 ∧ u x ^ 2 ≤ A x ^ 2 :=
    fun x hx => hc ⟨hcd.trans hx.1, hx.2⟩
  let e := (d + b) / 2
  have hde : d < e := by dsimp [e]; linarith
  have heb : e < b := by dsimp [e]; linarith
  have heI : e ∈ Ioo d b := ⟨hde, heb⟩
  have heS : e ∈ Ioo a b := (hgood e heI).1
  let W := Ω e
  have hW : W = 0 := by
    by_contra hW
    let F : ℝ → ℝ := fun x => v x / (W * u x) - ξ x
    have hFd : ∀ x ∈ Ioo d b,
        HasDerivAt F ((u x ^ 2)⁻¹ - (A x ^ 2)⁻¹) x := by
      intro x hx
      obtain ⟨hxS, hxu, -⟩ := hgood x hx
      refine (((hv x hxS).div ((hu x hxS).const_mul W) (mul_ne_zero hW hxu)).sub
        (hξ x hxS)).congr_deriv ?_
      have hΩx : Ω x = W := hΩ hxS heS
      dsimp [Ω] at hΩx
      field_simp
      linear_combination hΩx
    have hFm : MonotoneOn F (Ioo d b) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ioo d b)
        (fun x hx => (hFd x hx).continuousAt.continuousWithinAt)
        (fun x hx => by
          rw [interior_Ioo] at hx
          exact (hFd x hx).differentiableAt.differentiableWithinAt) (fun x hx => ?_)
      rw [interior_Ioo] at hx
      rw [(hFd x hx).deriv]
      obtain ⟨hxS, hxu, hxA⟩ := hgood x hx
      have hxA0 := hA x hxS
      exact sub_nonneg.2 (inv_le_inv₀ (sq_pos_of_pos hxA0) (sq_pos_of_ne_zero hxu) |>.2 hxA)
    have hvb : ∀ᶠ x in 𝓝[<] b, v x / (W * u x) < 1 / W + 1 := by
      have ht := (hratio.div_const W).eventually_lt_const (by linarith : 1 / W < 1 / W + 1)
      simpa only [div_div, mul_comm W] using ht
    have hlarge := hξtop.eventually_gt_atTop (1 / W + 1 - F e)
    have hcontr : ∀ᶠ x in 𝓝[<] b, False := by
      filter_upwards [Ioo_mem_nhdsLT heb, hvb, hlarge] with x hx hxb hxl
      have hmono := hFm heI ⟨hde.trans hx.1, hx.2⟩ hx.1.le
      dsimp [F] at hmono
      linarith
    exact hcontr.exists.elim fun _ h => h
  have hrd : ∀ x ∈ Ioo d b, HasDerivAt (fun x => v x / u x) 0 x := by
    intro x hx
    obtain ⟨hxS, hxu, -⟩ := hgood x hx
    refine ((hv x hxS).div (hu x hxS) hxu).congr_deriv ?_
    have hΩx : Ω x = 0 := (hΩ hxS heS).trans hW
    dsimp [Ω] at hΩx
    rw [div_eq_zero_iff]
    exact Or.inl (by linear_combination hΩx)
  have hrc : ∀ x ∈ Ioo d b, v x / u x = v e / u e := by
    intro x hx
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo d b).isPreconnected
      (fun z hz => (hrd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hrd z hz).deriv) hx heI
  have hlim : Tendsto (fun x => v x / u x) (𝓝[<] b) (𝓝 (v e / u e)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsLT hdb] with x hx using (hrc x hx).symm)
  have hval : v e = u e := (div_eq_one_iff_eq (hgood e heI).2.1).1
    (tendsto_nhds_unique hlim hratio)
  have hder : v' e = u' e := by
    have hΩe : u e * v' e - u' e * v e = 0 := hW
    rw [hval] at hΩe
    exact (mul_left_cancel₀ (hgood e heI).2.1) (by linear_combination hΩe)
  exact (ODE.eqOn_of_linear_ode (p := fun _ => 0) isOpen_Ioo (convex_Ioo a b).ordConnected heS
    continuousOn_const hq
    (fun x hx => ⟨hv x hx, by simpa using hv' x hx⟩)
    (fun x hx => ⟨hu x hx, by simpa using hu' x hx⟩) hval hder).1


/-- The left-endpoint version of recessive uniqueness, obtained by reflection. -/
theorem eqOn_of_recessive_ratio_left {a b : ℝ} (hab : a < b) {A ξ q u u' v v' : ℝ → ℝ}
    (hA : ∀ x ∈ Ioo a b, 0 < A x)
    (hξ : ∀ x ∈ Ioo a b, HasDerivAt ξ ((A x ^ 2)⁻¹) x)
    (hξbot : Tendsto ξ (𝓝[>] a) atBot) (hq : ContinuousOn q (Ioo a b))
    (hu : ∀ x ∈ Ioo a b, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Ioo a b, HasDerivAt u' (q x * u x) x)
    (hv : ∀ x ∈ Ioo a b, HasDerivAt v (v' x) x)
    (hv' : ∀ x ∈ Ioo a b, HasDerivAt v' (q x * v x) x)
    (hune : ∀ᶠ x in 𝓝[>] a, u x ≠ 0)
    (hsmall : Tendsto (fun x => u x / A x) (𝓝[>] a) (𝓝 0))
    (hratio : Tendsto (fun x => v x / u x) (𝓝[>] a) (𝓝 1)) :
    EqOn v u (Ioo a b) := by
  have hneg : ∀ x ∈ Ioo (-b) (-a), -x ∈ Ioo a b := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hξR : ∀ x ∈ Ioo (-b) (-a),
      HasDerivAt (fun t => -ξ (-t)) (((A (-x)) ^ 2)⁻¹) x := by
    intro x hx
    convert ((hξ (-x) (hneg x hx)).comp x (hasDerivAt_neg x)).neg using 1 <;>
      simp [Function.comp_def, funext_iff]
  have hdR : ∀ {z z' r : ℝ → ℝ},
      (∀ x ∈ Ioo a b, HasDerivAt z (z' x) x) →
      (∀ x ∈ Ioo a b, HasDerivAt z' (r x * z x) x) →
      (∀ x ∈ Ioo (-b) (-a), HasDerivAt (fun t => z (-t)) (-z' (-x)) x) ∧
      (∀ x ∈ Ioo (-b) (-a), HasDerivAt (fun t => -z' (-t)) (r (-x) * z (-x)) x) := by
    intro z z' r hz hz'
    constructor
    · intro x hx
      simpa [Function.comp_def] using (hz (-x) (hneg x hx)).comp x (hasDerivAt_neg x)
    · intro x hx
      convert ((hz' (-x) (hneg x hx)).comp x (hasDerivAt_neg x)).neg using 1 <;>
        simp [Function.comp_def, funext_iff]
  have hnt : Tendsto (fun x : ℝ => -x) (𝓝[<] (-a)) (𝓝[>] a) :=
    tendsto_neg_nhdsLT_neg
  have hξRtop : Tendsto (fun x => -ξ (-x)) (𝓝[<] (-a)) atTop := by
    exact tendsto_neg_atBot_atTop.comp
      (hξbot.comp hnt)
  have huneR : ∀ᶠ x in 𝓝[<] (-a), u (-x) ≠ 0 :=
    hnt.eventually hune
  have hsmallR : Tendsto (fun x => u (-x) / A (-x)) (𝓝[<] (-a)) (𝓝 0) :=
    hsmall.comp hnt
  have hratioR : Tendsto (fun x => v (-x) / u (-x)) (𝓝[<] (-a)) (𝓝 1) :=
    hratio.comp hnt
  have h := eqOn_of_recessive_ratio (neg_lt_neg hab) (fun x hx => hA (-x) (hneg x hx))
    hξR hξRtop (hq.comp continuous_neg.continuousOn hneg)
    (hdR hu hu').1 (hdR hu hu').2 (hdR hv hv').1 (hdR hv hv').2 huneR hsmallR hratioR
  intro x hx
  simpa using h ⟨neg_lt_neg hx.2, neg_lt_neg hx.1⟩

end LiouvilleGreen.Interval
