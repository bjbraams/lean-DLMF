/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Spheroidal.Basic.Ferrers
public import DLMF.AlgebraicAnalytic.ODE.SecondOrder
public import DLMFMathlib.Analysis.ODE.PowerSeriesUniqueness
public import Mathlib.Analysis.Convex.Contractible

/-!
# Solutions of the spheroidal equation on the cut plane

Solutions of the spheroidal equation 30.2.1 on the cut plane `ℂ ∖ (-∞, 1]` of DLMF §30.6 and on
the doubly cut plane `ℂ ∖ ((-∞, -1] ∪ [1, ∞))`, and their boundary values on `(-1, 1)` from the
upper half plane. Both domains are star-shaped, hence simply connected, so the general existence
theorem `DLMF.AlgebraicAnalytic.exists_isLinearODE2SolutionOn` applies. A solution on the upper
half plane continues to the doubly cut plane, which contains `(-1, 1)`; this gives the boundary
values and, by the identity theorem, uniqueness from boundary values.

## Main results

* `exists_isSpheroidalSolutionOn`, `isSpheroidalSolutionOn_unique`: existence and uniqueness of
  solutions with prescribed data on simply connected, resp. connected, open sets avoiding `±1`.
* `exists_isSpheroidalSolutionOn_cutPlane_boundary`: a solution on the cut plane with boundary
  values from above `c₁ f₁ + c₂ f₂` for real solutions `f₁`, `f₂` on `(-1, 1)`.
* `eq_of_isSpheroidalSolutionOn_cutPlane_boundary`: such a solution is unique.
* `isSpheroidalSolutionOn_wronskian_const`: Abel's identity `(1-z²) 𝒲{w, v} = const`.
* `wronskian_cutPlane_of_boundary`: the Wronskian on the cut plane from the boundary values.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real

namespace DLMF.Spheroidal

/-- The plane cut along `(-∞, -1]` and `[1, ∞)`. -/
def spheroidalDoubleCutPlane : Set ℂ := {z : ℂ | 1 - z ∈ slitPlane ∧ 1 + z ∈ slitPlane}

/-- Membership in the doubly cut plane. -/
lemma mem_spheroidalDoubleCutPlane_iff {z : ℂ} :
    z ∈ spheroidalDoubleCutPlane ↔ z.im ≠ 0 ∨ (-1 < z.re ∧ z.re < 1) := by
  simp only [spheroidalDoubleCutPlane, mem_ofPred_eq, mem_slitPlane_iff, sub_re, one_re, sub_im,
    one_im, add_re, add_im]
  constructor
  · rintro ⟨h1 | h1, h2 | h2⟩
    · right; constructor <;> linarith
    · left; simpa using h2
    · left; simpa using h1
    · left; simpa using h2
  · rintro (h | ⟨h1, h2⟩)
    · exact ⟨Or.inr (by simpa using h), Or.inr (by simpa using h)⟩
    · exact ⟨Or.inl (by linarith), Or.inl (by linarith)⟩

/-- Membership in the cut plane `ℂ ∖ (-∞, 1]`. -/
lemma mem_spheroidalCutPlane_iff' {z : ℂ} :
    z ∈ spheroidalCutPlane ↔ z.im ≠ 0 ∨ 1 < z.re := by
  simp only [spheroidalCutPlane, mem_ofPred_eq, mem_slitPlane_iff, sub_re, one_re, sub_im, one_im,
    sub_zero]
  constructor
  · rintro (h | h)
    · right; linarith
    · left; exact h
  · rintro (h | h)
    · right; exact h
    · left; linarith

/-- The doubly cut plane is open. -/
lemma isOpen_spheroidalDoubleCutPlane : IsOpen spheroidalDoubleCutPlane :=
  (isOpen_slitPlane.preimage (continuous_const.sub continuous_id)).inter
    (isOpen_slitPlane.preimage (continuous_const.add continuous_id))

/-- The cut plane is open. -/
lemma isOpen_spheroidalCutPlane : IsOpen spheroidalCutPlane :=
  isOpen_slitPlane.preimage (continuous_id.sub continuous_const)

/-- The doubly cut plane is star-shaped with respect to `0`. -/
lemma starConvex_spheroidalDoubleCutPlane : StarConvex ℝ 0 spheroidalDoubleCutPlane := by
  intro z hz a b ha hb hab
  rw [mem_spheroidalDoubleCutPlane_iff] at hz ⊢
  simp only [smul_zero, zero_add, Complex.real_smul, mul_im, ofReal_re, ofReal_im, zero_mul,
    add_zero, mul_re, sub_zero]
  rcases eq_or_lt_of_le hb with h0 | hpos
  · subst h0; right; simp
  rcases hz with h | ⟨h1, h2⟩
  · left; exact mul_ne_zero hpos.ne' h
  · right; constructor <;> nlinarith

/-- The cut plane is star-shaped with respect to `2`. -/
lemma starConvex_spheroidalCutPlane : StarConvex ℝ 2 spheroidalCutPlane := by
  intro z hz a b ha hb hab
  rw [mem_spheroidalCutPlane_iff'] at hz ⊢
  simp only [Complex.real_smul, add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero,
    add_re, mul_re, sub_zero, re_ofNat, im_ofNat, mul_zero]
  rcases eq_or_lt_of_le hb with h0 | hpos
  · subst h0; right; simp at hab; subst hab; norm_num
  rcases hz with h | h
  · left; simpa using mul_ne_zero hpos.ne' h
  · right; nlinarith

/-- The doubly cut plane is simply connected. -/
lemma isSimplyConnected_spheroidalDoubleCutPlane : IsSimplyConnected spheroidalDoubleCutPlane :=
  haveI := starConvex_spheroidalDoubleCutPlane.contractibleSpace
    ⟨0, by rw [mem_spheroidalDoubleCutPlane_iff]; right; norm_num⟩
  SimplyConnectedSpace.ofContractible _

/-- The cut plane is simply connected. -/
lemma isSimplyConnected_spheroidalCutPlane : IsSimplyConnected spheroidalCutPlane :=
  haveI := starConvex_spheroidalCutPlane.contractibleSpace
    ⟨2, by rw [mem_spheroidalCutPlane_iff']; right; norm_num⟩
  SimplyConnectedSpace.ofContractible _



/-- On an open set avoiding `±1`, 30.2.1 is the equation `w'' + f w' + g w = 0` of §1.13 with
`f = -2z/(1-z²)` and `g = c/(1-z²)`. -/
lemma isSpheroidalSolutionOn_iff_isLinearODE2SolutionOn {lam γ2 μ : ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hU1 : ∀ z ∈ U, 1 - z ^ 2 ≠ 0) {w : ℂ → ℂ} :
    IsSpheroidalSolutionOn lam γ2 μ U w ↔ AlgebraicAnalytic.IsLinearODE2SolutionOn
      (fun z => -(2 * z) / (1 - z ^ 2))
      (fun z => (lam + γ2 * (1 - z ^ 2) - μ ^ 2 / (1 - z ^ 2)) / (1 - z ^ 2)) 0 w U := by
  have hq : ∀ z : ℂ, HasDerivAt (fun t : ℂ => 1 - t ^ 2) (-(2 * z)) z := fun z => by
    simpa using ((hasDerivAt_pow 2 z).const_sub 1)
  constructor
  · intro hw z hz
    refine ⟨hw.differentiableAt z hz, ?_⟩
    have h := (hw.hasDerivAt z hz).div (hq z) (hU1 z hz)
    have hev : (fun t => (1 - t ^ 2) * deriv w t / (1 - t ^ 2)) =ᶠ[𝓝 z] deriv w := by
      filter_upwards [hU.mem_nhds hz] with t ht
      field_simp [hU1 t ht]
    refine (h.congr_of_eventuallyEq hev.symm).congr_deriv ?_
    have := hU1 z hz
    simp only [Pi.zero_apply]
    field_simp
    ring
  · intro hw
    refine ⟨fun z hz => (hw z hz).1, fun z hz => ?_⟩
    have h := (hq z).mul (hw z hz).2
    refine h.congr_deriv ?_
    have := hU1 z hz
    simp only [Pi.zero_apply]
    field_simp
    ring

private lemma coeff_differentiableOn {lam γ2 μ : ℂ} {U : Set ℂ}
    (hU1 : ∀ z ∈ U, 1 - z ^ 2 ≠ 0) :
    DifferentiableOn ℂ (fun z : ℂ => -(2 * z) / (1 - z ^ 2)) U ∧
      DifferentiableOn ℂ
        (fun z => (lam + γ2 * (1 - z ^ 2) - μ ^ 2 / (1 - z ^ 2)) / (1 - z ^ 2)) U := by
  constructor
  · exact DifferentiableOn.div (by fun_prop) (by fun_prop) hU1
  · refine DifferentiableOn.div ?_ (by fun_prop) hU1
    show DifferentiableOn ℂ (fun z => lam + γ2 * (1 - z ^ 2) - μ ^ 2 / (1 - z ^ 2)) U
    exact (by fun_prop : DifferentiableOn ℂ (fun z : ℂ => lam + γ2 * (1 - z ^ 2)) U).sub
      (DifferentiableOn.div (by fun_prop) (by fun_prop) hU1)

/-- Existence of solutions of 30.2.1 with prescribed data on a simply connected open set
avoiding `±1`. -/
theorem exists_isSpheroidalSolutionOn {lam γ2 μ : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hsc : IsSimplyConnected U) (hU1 : ∀ z ∈ U, 1 - z ^ 2 ≠ 0) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (w₀ w₁ : ℂ) :
    ∃ w, IsSpheroidalSolutionOn lam γ2 μ U w ∧ w z₀ = w₀ ∧ deriv w z₀ = w₁ := by
  obtain ⟨hf, hg⟩ := coeff_differentiableOn (lam := lam) (γ2 := γ2) (μ := μ) hU1
  obtain ⟨w, hw, h0, h1⟩ :=
    AlgebraicAnalytic.exists_isLinearODE2SolutionOn hU hsc hf hg hz₀ w₀ w₁
  exact ⟨w, (isSpheroidalSolutionOn_iff_isLinearODE2SolutionOn hU hU1).2 hw, h0, h1⟩

/-- Uniqueness of solutions of 30.2.1 with given data on a connected open set avoiding `±1`. -/
theorem isSpheroidalSolutionOn_unique {lam γ2 μ : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hU' : IsPreconnected U) (hU1 : ∀ z ∈ U, 1 - z ^ 2 ≠ 0) {w v : ℂ → ℂ}
    (hw : IsSpheroidalSolutionOn lam γ2 μ U w) (hv : IsSpheroidalSolutionOn lam γ2 μ U v)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (h₀ : w z₀ = v z₀) (h₁ : deriv w z₀ = deriv v z₀) : EqOn w v U := by
  obtain ⟨hf, hg⟩ := coeff_differentiableOn (lam := lam) (γ2 := γ2) (μ := μ) hU1
  exact AlgebraicAnalytic.isLinearODE2SolutionOn_unique hU hU' hf hg
    ((isSpheroidalSolutionOn_iff_isLinearODE2SolutionOn hU hU1).1 hw)
    ((isSpheroidalSolutionOn_iff_isLinearODE2SolutionOn hU hU1).1 hv) hz₀ h₀ h₁

/-- Restriction of a solution to an open subset. -/
theorem IsSpheroidalSolutionOn.mono {lam γ2 μ : ℂ} {U V : Set ℂ} {w : ℂ → ℂ}
    (hw : IsSpheroidalSolutionOn lam γ2 μ U w) (hVU : V ⊆ U) :
    IsSpheroidalSolutionOn lam γ2 μ V w :=
  ⟨fun z hz => hw.differentiableAt z (hVU hz), fun z hz => hw.hasDerivAt z (hVU hz)⟩


/-- Solutions are stable under change on the complement of an open set. -/
theorem IsSpheroidalSolutionOn.congr {lam γ2 μ : ℂ} {U : Set ℂ} {w v : ℂ → ℂ} (hU : IsOpen U)
    (hw : IsSpheroidalSolutionOn lam γ2 μ U w) (hwv : EqOn w v U) :
    IsSpheroidalSolutionOn lam γ2 μ U v := by
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · exact (hw.differentiableAt z hz).congr_of_eventuallyEq
      (eventually_of_mem (hU.mem_nhds hz) fun y hy => (hwv hy).symm)
  · have hev : w =ᶠ[𝓝 z] v := eventually_of_mem (hU.mem_nhds hz) fun y hy => hwv hy
    have hd : (fun t => (1 - t ^ 2) * deriv w t) =ᶠ[𝓝 z] fun t => (1 - t ^ 2) * deriv v t := by
      filter_upwards [hev.eventuallyEq_nhds] with y hy
      rw [hy.deriv_eq]
    rw [← hwv hz]
    exact (hw.hasDerivAt z hz).congr_of_eventuallyEq hd.symm

/-- The cut plane avoids `±1`. -/
lemma one_sub_sq_ne_zero_of_mem_spheroidalCutPlane {z : ℂ} (hz : z ∈ spheroidalCutPlane) :
    1 - z ^ 2 ≠ 0 := by
  intro h
  have h' : (1 - z) * (1 + z) = 0 := by linear_combination h
  rw [mem_spheroidalCutPlane_iff'] at hz
  rcases mul_eq_zero.1 h' with h1 | h1
  · rw [show z = 1 by linear_combination -h1] at hz; norm_num at hz
  · rw [show z = -1 by linear_combination h1] at hz; norm_num at hz

/-- The doubly cut plane avoids `±1`. -/
lemma one_sub_sq_ne_zero_of_mem_spheroidalDoubleCutPlane {z : ℂ}
    (hz : z ∈ spheroidalDoubleCutPlane) : 1 - z ^ 2 ≠ 0 := by
  intro h
  have h' : (1 - z) * (1 + z) = 0 := by linear_combination h
  rw [mem_spheroidalDoubleCutPlane_iff] at hz
  rcases mul_eq_zero.1 h' with h1 | h1
  · rw [show z = 1 by linear_combination -h1] at hz; norm_num at hz
  · rw [show z = -1 by linear_combination h1] at hz; norm_num at hz

/-- The upper half plane lies in the cut plane. -/
private lemma upper_subset_cut : {z : ℂ | 0 < z.im} ⊆ spheroidalCutPlane := fun z hz => by
  rw [mem_spheroidalCutPlane_iff']; left; exact (ne_of_gt hz)

private lemma upper_subset_doubleCut : {z : ℂ | 0 < z.im} ⊆ spheroidalDoubleCutPlane :=
  fun z hz => by rw [mem_spheroidalDoubleCutPlane_iff]; left; exact (ne_of_gt hz)

private lemma isOpen_upper : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const continuous_im

private lemma isPreconnected_upper : IsPreconnected {z : ℂ | 0 < z.im} :=
  (convex_halfSpace_im_gt 0).isPreconnected

private lemma I_mem_upper : I ∈ {z : ℂ | 0 < z.im} := by simp

private lemma ofReal_mem_doubleCut {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (x : ℂ) ∈ spheroidalDoubleCutPlane := by
  rw [mem_spheroidalDoubleCutPlane_iff]; right; simpa using hx

/-- A solution on the upper half plane is the restriction of a solution on a simply connected
open set `U` containing it and avoiding `±1`. -/
theorem exists_eqOn_upper_of_isSpheroidalSolutionOn {lam γ2 μ : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hsc : IsSimplyConnected U) (hU1 : ∀ z ∈ U, 1 - z ^ 2 ≠ 0)
    (hHU : {z : ℂ | 0 < z.im} ⊆ U) {F : ℂ → ℂ}
    (hF : IsSpheroidalSolutionOn lam γ2 μ {z : ℂ | 0 < z.im} F) :
    ∃ K, IsSpheroidalSolutionOn lam γ2 μ U K ∧ EqOn K F {z : ℂ | 0 < z.im} := by
  obtain ⟨K, hK, h0, h1⟩ := exists_isSpheroidalSolutionOn (lam := lam) (γ2 := γ2) (μ := μ) hU hsc
    hU1 (hHU I_mem_upper) (F I) (deriv F I)
  exact ⟨K, hK, isSpheroidalSolutionOn_unique isOpen_upper isPreconnected_upper
    (fun z hz => hU1 z (hHU hz)) (hK.mono hHU) hF I_mem_upper h0 h1⟩

private lemma tendsto_vertical (x : ℝ) :
    Tendsto (fun ε : ℝ => (x : ℂ) + ε * I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
  have : Continuous fun ε : ℝ => (x : ℂ) + ε * I := by fun_prop
  simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds

private lemma vertical_mem_upper (x : ℝ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, (x : ℂ) + ε * I ∈ {z : ℂ | 0 < z.im} := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simpa using hε

/-- Boundary values from above of a solution on the upper half plane, through its extension. -/
private lemma tendsto_of_eqOn_upper {lam γ2 μ : ℂ} {K F : ℂ → ℂ}
    (hK : IsSpheroidalSolutionOn lam γ2 μ spheroidalDoubleCutPlane K)
    (hKF : EqOn K F {z : ℂ | 0 < z.im}) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Tendsto (fun ε : ℝ => F (x + ε * I)) (𝓝[>] 0) (𝓝 (K x)) := by
  have hc := (hK.differentiableAt x (ofReal_mem_doubleCut hx)).continuousAt.tendsto.comp
    (tendsto_vertical x)
  refine hc.congr' ?_
  filter_upwards [vertical_mem_upper x] with ε hε using hKF hε

/-- The real-line coefficients. -/
private noncomputable def coeffP (x : ℝ) : ℂ := 2 * x / (1 - (x : ℂ) ^ 2)

private noncomputable def coeffQ (lam γ2 μ : ℂ) (x : ℝ) : ℂ :=
  -((lam + γ2 * (1 - (x : ℂ) ^ 2) - μ ^ 2 / (1 - (x : ℂ) ^ 2)) / (1 - (x : ℂ) ^ 2))

private lemma ofReal_one_sub_sq_ne_zero {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    1 - (x : ℂ) ^ 2 ≠ 0 := by
  have : (0 : ℝ) < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  exact_mod_cast this.ne'

private lemma continuousOn_coeffP : ContinuousOn coeffP (Ioo (-1 : ℝ) 1) :=
  ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ofReal_one_sub_sq_ne_zero hx

private lemma continuousOn_coeffQ (lam γ2 μ : ℂ) :
    ContinuousOn (coeffQ lam γ2 μ) (Ioo (-1 : ℝ) 1) := by
  have h := fun x (hx : x ∈ Ioo (-1 : ℝ) 1) => ofReal_one_sub_sq_ne_zero hx
  refine ContinuousOn.neg (ContinuousOn.div ?_ (by fun_prop) h)
  show ContinuousOn (fun x : ℝ => lam + γ2 * (1 - (x : ℂ) ^ 2) - μ ^ 2 / (1 - (x : ℂ) ^ 2)) _
  exact (by fun_prop : ContinuousOn (fun x : ℝ => lam + γ2 * (1 - (x : ℂ) ^ 2)) _).sub
    (ContinuousOn.div (by fun_prop) (by fun_prop) h)

/-- A solution on the doubly cut plane restricted to `(-1, 1)`. -/
private lemma real_ode_of_isSpheroidalSolutionOn {lam γ2 μ : ℂ} {K : ℂ → ℂ}
    (hK : IsSpheroidalSolutionOn lam γ2 μ spheroidalDoubleCutPlane K) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => K t) (deriv K x) x ∧
      HasDerivAt (fun t : ℝ => deriv K t)
        (coeffP x • deriv K x + coeffQ lam γ2 μ x • K x) x := by
  have hm := ofReal_mem_doubleCut hx
  have hL := (isSpheroidalSolutionOn_iff_isLinearODE2SolutionOn isOpen_spheroidalDoubleCutPlane
    (fun z hz => one_sub_sq_ne_zero_of_mem_spheroidalDoubleCutPlane hz)).1 hK _ hm
  refine ⟨(hK.differentiableAt _ hm).hasDerivAt.comp_ofReal, ?_⟩
  refine hL.2.comp_ofReal.congr_deriv ?_
  simp only [coeffP, coeffQ, Pi.zero_apply, smul_eq_mul]
  ring

/-- A real solution on `(-1, 1)`, cast to `ℂ`. -/
private lemma real_ode_of_isSpheroidalSolutionReal {lam γ2 μ : ℝ} {f : ℝ → ℝ}
    (hf : IsSpheroidalSolutionReal lam γ2 μ f) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => (f t : ℂ)) ((deriv f x : ℝ) : ℂ) x ∧
      HasDerivAt (fun t : ℝ => ((deriv f t : ℝ) : ℂ))
        (coeffP x • ((deriv f x : ℝ) : ℂ) + coeffQ lam γ2 μ x • (f x : ℂ)) x := by
  have hpos : ∀ y ∈ Ioo (-1 : ℝ) 1, 1 - y ^ 2 ≠ 0 := fun y hy => by nlinarith [hy.1, hy.2]
  refine ⟨(hf.differentiableAt x hx).hasDerivAt.ofReal_comp, ?_⟩
  have hq : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub 1)
  have h := (hf.hasDerivAt x hx).div hq (hpos x hx)
  have hev : (fun t => (1 - t ^ 2) * deriv f t / (1 - t ^ 2)) =ᶠ[𝓝 x] deriv f := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
    field_simp [hpos t ht]
  have h2 := (h.congr_of_eventuallyEq hev.symm).ofReal_comp
  refine h2.congr_deriv ?_
  have h3 := ofReal_one_sub_sq_ne_zero hx
  have h4 := hpos x hx
  simp only [coeffP, coeffQ, smul_eq_mul]
  push_cast
  field_simp
  ring


private lemma isPreconnected_doubleCut : IsPreconnected spheroidalDoubleCutPlane :=
  isSimplyConnected_spheroidalDoubleCutPlane.isPathConnected.isConnected.isPreconnected

private lemma isPreconnected_cut : IsPreconnected spheroidalCutPlane :=
  isSimplyConnected_spheroidalCutPlane.isPathConnected.isConnected.isPreconnected

/-- A solution on the doubly cut plane is determined on `(-1, 1)` by its data at `0`. -/
private lemma eqOn_Ioo_of_real_ode {lam γ2 μ : ℂ} {K : ℂ → ℂ}
    (hK : IsSpheroidalSolutionOn lam γ2 μ spheroidalDoubleCutPlane K) {Φ Φ' : ℝ → ℂ}
    (hΦ : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt Φ (Φ' x) x ∧
      HasDerivAt Φ' (coeffP x • Φ' x + coeffQ lam γ2 μ x • Φ x) x)
    (h0 : K 0 = Φ 0) (h1 : deriv K 0 = Φ' 0) : ∀ x ∈ Ioo (-1 : ℝ) 1, K x = Φ x := by
  have h := ODE.eqOn_of_linear_ode (𝕜 := ℂ) (E := ℂ) isOpen_Ioo ordConnected_Ioo
    (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 by norm_num) continuousOn_coeffP (continuousOn_coeffQ lam γ2 μ)
    (f := fun t : ℝ => K t) (f' := fun t : ℝ => deriv K t) (g := Φ) (g' := Φ')
    (fun x hx => real_ode_of_isSpheroidalSolutionOn hK hx) hΦ (by simpa using h0)
    (by simpa using h1)
  exact fun x hx => h.1 hx

/-- **Solutions on `ℂ ∖ (-∞, 1]` with prescribed boundary values from above** on `(-1, 1)`:
for real solutions `f₁`, `f₂` of 30.2.1 on `(-1, 1)` and `c₁ c₂ : ℂ` there is a solution on the
cut plane, vanishing off it, whose boundary values from the upper half plane are
`c₁ f₁ + c₂ f₂`. -/
theorem exists_isSpheroidalSolutionOn_cutPlane_boundary {lam γ2 μ : ℝ} {f₁ f₂ : ℝ → ℝ}
    (hf₁ : IsSpheroidalSolutionReal lam γ2 μ f₁) (hf₂ : IsSpheroidalSolutionReal lam γ2 μ f₂)
    (c₁ c₂ : ℂ) :
    ∃ F, IsSpheroidalSolutionOn lam γ2 μ spheroidalCutPlane F ∧
      (∀ z, z ∉ spheroidalCutPlane → F z = 0) ∧
      ∀ x ∈ Ioo (-1 : ℝ) 1, Tendsto (fun ε : ℝ => F (x + ε * I)) (𝓝[>] 0)
        (𝓝 (c₁ * f₁ x + c₂ * f₂ x)) := by
  set Φ : ℝ → ℂ := fun x => c₁ * f₁ x + c₂ * f₂ x
  set Φ' : ℝ → ℂ := fun x => c₁ * ((deriv f₁ x : ℝ) : ℂ) + c₂ * ((deriv f₂ x : ℝ) : ℂ)
  have hΦ : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt Φ (Φ' x) x ∧
      HasDerivAt Φ' (coeffP x • Φ' x + coeffQ lam γ2 μ x • Φ x) x := by
    intro x hx
    obtain ⟨a1, b1⟩ := real_ode_of_isSpheroidalSolutionReal hf₁ hx
    obtain ⟨a2, b2⟩ := real_ode_of_isSpheroidalSolutionReal hf₂ hx
    refine ⟨(a1.const_mul c₁).add (a2.const_mul c₂), ?_⟩
    refine ((b1.const_mul c₁).add (b2.const_mul c₂)).congr_deriv ?_
    simp only [Φ, Φ', smul_eq_mul]
    ring
  have hD1 := fun z (hz : z ∈ spheroidalDoubleCutPlane) =>
    one_sub_sq_ne_zero_of_mem_spheroidalDoubleCutPlane hz
  have hC1 := fun z (hz : z ∈ spheroidalCutPlane) => one_sub_sq_ne_zero_of_mem_spheroidalCutPlane hz
  have h0D : (0 : ℂ) ∈ spheroidalDoubleCutPlane := by
    rw [mem_spheroidalDoubleCutPlane_iff]; right; norm_num
  obtain ⟨K, hK, hK0, hK1⟩ := exists_isSpheroidalSolutionOn (lam := lam) (γ2 := γ2) (μ := μ)
    isOpen_spheroidalDoubleCutPlane isSimplyConnected_spheroidalDoubleCutPlane hD1 h0D
    (Φ 0) (Φ' 0)
  have hKΦ := eqOn_Ioo_of_real_ode hK hΦ hK0 hK1
  obtain ⟨F₀, hF₀, hF0, hF1⟩ := exists_isSpheroidalSolutionOn (lam := lam) (γ2 := γ2) (μ := μ)
    isOpen_spheroidalCutPlane isSimplyConnected_spheroidalCutPlane hC1
    (upper_subset_cut I_mem_upper)
    (K I) (deriv K I)
  have hKF : EqOn K F₀ {z : ℂ | 0 < z.im} := isSpheroidalSolutionOn_unique isOpen_upper
    isPreconnected_upper (fun z hz => hD1 z (upper_subset_doubleCut hz))
    (hK.mono upper_subset_doubleCut) (hF₀.mono upper_subset_cut) I_mem_upper hF0.symm hF1.symm
  classical
  set F : ℂ → ℂ := fun z => if z ∈ spheroidalCutPlane then F₀ z else 0
  have hFF : EqOn F₀ F spheroidalCutPlane := fun z hz => by simp [F, hz]
  refine ⟨F, hF₀.congr isOpen_spheroidalCutPlane hFF, fun z hz => by simp [F, hz],
    fun x hx => ?_⟩
  have := tendsto_of_eqOn_upper hK (fun z hz => (hKF hz).trans (hFF (upper_subset_cut hz))) hx
  rwa [hKΦ x hx] at this

/-- **Uniqueness from boundary values from above**: two solutions of 30.2.1 on `ℂ ∖ (-∞, 1]`,
vanishing off it, with the same boundary values from the upper half plane on `(-1, 1)`,
coincide. -/
theorem eq_of_isSpheroidalSolutionOn_cutPlane_boundary {lam γ2 μ : ℂ} {F₁ F₂ : ℂ → ℂ}
    (hF₁ : IsSpheroidalSolutionOn lam γ2 μ spheroidalCutPlane F₁)
    (hF₂ : IsSpheroidalSolutionOn lam γ2 μ spheroidalCutPlane F₂)
    (ho₁ : ∀ z, z ∉ spheroidalCutPlane → F₁ z = 0) (ho₂ : ∀ z, z ∉ spheroidalCutPlane → F₂ z = 0)
    {L : ℝ → ℂ}
    (hb₁ : ∀ x ∈ Ioo (-1 : ℝ) 1, Tendsto (fun ε : ℝ => F₁ (x + ε * I)) (𝓝[>] 0) (𝓝 (L x)))
    (hb₂ : ∀ x ∈ Ioo (-1 : ℝ) 1, Tendsto (fun ε : ℝ => F₂ (x + ε * I)) (𝓝[>] 0) (𝓝 (L x))) :
    F₁ = F₂ := by
  have hD1 := fun z (hz : z ∈ spheroidalDoubleCutPlane) =>
    one_sub_sq_ne_zero_of_mem_spheroidalDoubleCutPlane hz
  have hC1 := fun z (hz : z ∈ spheroidalCutPlane) => one_sub_sq_ne_zero_of_mem_spheroidalCutPlane hz
  obtain ⟨K₁, hK₁, hKF₁⟩ := exists_eqOn_upper_of_isSpheroidalSolutionOn
    isOpen_spheroidalDoubleCutPlane isSimplyConnected_spheroidalDoubleCutPlane hD1
    upper_subset_doubleCut (hF₁.mono upper_subset_cut)
  obtain ⟨K₂, hK₂, hKF₂⟩ := exists_eqOn_upper_of_isSpheroidalSolutionOn
    isOpen_spheroidalDoubleCutPlane isSimplyConnected_spheroidalDoubleCutPlane hD1
    upper_subset_doubleCut (hF₂.mono upper_subset_cut)
  have hKx : ∀ x ∈ Ioo (-1 : ℝ) 1, K₁ x = K₂ x := fun x hx =>
    (tendsto_nhds_unique (tendsto_of_eqOn_upper hK₁ hKF₁ hx) (hb₁ x hx)).trans
      (tendsto_nhds_unique (tendsto_of_eqOn_upper hK₂ hKF₂ hx) (hb₂ x hx)).symm
  have hA₁ : AnalyticOnNhd ℂ K₁ spheroidalDoubleCutPlane :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hK₁.differentiableAt z hz).differentiableWithinAt)
      isOpen_spheroidalDoubleCutPlane
  have hA₂ : AnalyticOnNhd ℂ K₂ spheroidalDoubleCutPlane :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hK₂.differentiableAt z hz).differentiableWithinAt)
      isOpen_spheroidalDoubleCutPlane
  have h0D : (0 : ℂ) ∈ spheroidalDoubleCutPlane := by
    rw [mem_spheroidalDoubleCutPlane_iff]; right; norm_num
  have hfr : ∃ᶠ z in 𝓝[≠] (0 : ℂ), K₁ z = K₂ z := by
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using hx
    refine ht.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < 1 by norm_num))] with x hx
    exact hKx x hx
  have hK := hA₁.eqOn_of_preconnected_of_frequently_eq hA₂ isPreconnected_doubleCut h0D hfr
  have hH : EqOn F₁ F₂ {z : ℂ | 0 < z.im} := fun z hz =>
    (hKF₁ hz).symm.trans ((hK (upper_subset_doubleCut hz)).trans (hKF₂ hz))
  have hev : F₁ =ᶠ[𝓝 I] F₂ := eventually_of_mem (isOpen_upper.mem_nhds I_mem_upper) hH
  have hC := isSpheroidalSolutionOn_unique isOpen_spheroidalCutPlane isPreconnected_cut hC1 hF₁ hF₂
    (upper_subset_cut I_mem_upper) (hH I_mem_upper) hev.deriv_eq
  funext z
  by_cases hz : z ∈ spheroidalCutPlane
  · exact hC hz
  · rw [ho₁ z hz, ho₂ z hz]


/-- **Abel's identity** for 30.2.1: for two solutions on a connected open set avoiding `±1`,
`(1-z²)(w v' - w' v)` is constant. -/
theorem isSpheroidalSolutionOn_wronskian_const {lam γ2 μ : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hU' : IsPreconnected U) {w v : ℂ → ℂ} (hw : IsSpheroidalSolutionOn lam γ2 μ U w)
    (hv : IsSpheroidalSolutionOn lam γ2 μ U v) {z y : ℂ} (hz : z ∈ U) (hy : y ∈ U) :
    (1 - z ^ 2) * (w z * deriv v z - deriv w z * v z) =
      (1 - y ^ 2) * (w y * deriv v y - deriv w y * v y) := by
  have hD : ∀ t ∈ U, HasDerivAt
      (fun s => w s * ((1 - s ^ 2) * deriv v s) - (1 - s ^ 2) * deriv w s * v s) 0 t := by
    intro t ht
    have h1 := (hw.differentiableAt t ht).hasDerivAt.mul (hv.hasDerivAt t ht)
    have h2 := (hw.hasDerivAt t ht).mul (hv.differentiableAt t ht).hasDerivAt
    refine (h1.sub h2).congr_deriv ?_
    ring
  have hfun : ∀ s, (1 - s ^ 2) * (w s * deriv v s - deriv w s * v s) =
      w s * ((1 - s ^ 2) * deriv v s) - (1 - s ^ 2) * deriv w s * v s := fun s => by ring
  simp only [hfun]
  exact hU.is_const_of_deriv_eq_zero hU'
    (fun t ht => (hD t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hD t ht).deriv) hz hy

/-- The extension to the doubly cut plane of a solution on the cut plane with boundary values
`c₁ f₁ + c₂ f₂` from above, with its values and derivatives on `(-1, 1)`. -/
private lemma exists_doubleCut_of_boundary {lam γ2 μ : ℝ} {F : ℂ → ℂ}
    (hF : IsSpheroidalSolutionOn lam γ2 μ spheroidalCutPlane F) {f₁ f₂ : ℝ → ℝ}
    (hf₁ : IsSpheroidalSolutionReal lam γ2 μ f₁) (hf₂ : IsSpheroidalSolutionReal lam γ2 μ f₂)
    {c₁ c₂ : ℂ}
    (hb : ∀ x ∈ Ioo (-1 : ℝ) 1, Tendsto (fun ε : ℝ => F (x + ε * I)) (𝓝[>] 0)
      (𝓝 (c₁ * f₁ x + c₂ * f₂ x))) :
    ∃ K, IsSpheroidalSolutionOn lam γ2 μ spheroidalDoubleCutPlane K ∧
      EqOn K F {z : ℂ | 0 < z.im} ∧ ∀ x ∈ Ioo (-1 : ℝ) 1, K x = c₁ * f₁ x + c₂ * f₂ x ∧
        deriv K x = c₁ * ((deriv f₁ x : ℝ) : ℂ) + c₂ * ((deriv f₂ x : ℝ) : ℂ) := by
  have hD1 := fun z (hz : z ∈ spheroidalDoubleCutPlane) =>
    one_sub_sq_ne_zero_of_mem_spheroidalDoubleCutPlane hz
  obtain ⟨K, hK, hKF⟩ := exists_eqOn_upper_of_isSpheroidalSolutionOn
    isOpen_spheroidalDoubleCutPlane isSimplyConnected_spheroidalDoubleCutPlane hD1
    upper_subset_doubleCut (hF.mono upper_subset_cut)
  have hval : ∀ x ∈ Ioo (-1 : ℝ) 1, K x = c₁ * f₁ x + c₂ * f₂ x := fun x hx =>
    tendsto_nhds_unique (tendsto_of_eqOn_upper hK hKF hx) (hb x hx)
  refine ⟨K, hK, hKF, fun x hx => ⟨hval x hx, ?_⟩⟩
  have h1 := (real_ode_of_isSpheroidalSolutionOn hK hx).1
  have h2 := ((real_ode_of_isSpheroidalSolutionReal hf₁ hx).1.const_mul c₁).add
    ((real_ode_of_isSpheroidalSolutionReal hf₂ hx).1.const_mul c₂)
  refine h1.unique (h2.congr_of_eventuallyEq ?_)
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht using hval t ht

/-- **Wronskian from boundary values**: if solutions `F`, `G` of 30.2.1 on `ℂ ∖ (-∞, 1]` have
boundary values from above `Φ = c₁ f₁ + c₂ f₂` and `Ψ = d₁ g₁ + d₂ g₂` on `(-1, 1)` (real
solutions `fᵢ`, `gᵢ`), then `(1-z²) 𝒲{F, G}(z) = (1-x²)(Φ Ψ' - Φ' Ψ)(x)` for `z` in the cut plane
and `-1 < x < 1`. -/
theorem wronskian_cutPlane_of_boundary {lam γ2 μ : ℝ} {F G : ℂ → ℂ}
    (hF : IsSpheroidalSolutionOn lam γ2 μ spheroidalCutPlane F)
    (hG : IsSpheroidalSolutionOn lam γ2 μ spheroidalCutPlane G) {f₁ f₂ g₁ g₂ : ℝ → ℝ}
    (hf₁ : IsSpheroidalSolutionReal lam γ2 μ f₁) (hf₂ : IsSpheroidalSolutionReal lam γ2 μ f₂)
    (hg₁ : IsSpheroidalSolutionReal lam γ2 μ g₁) (hg₂ : IsSpheroidalSolutionReal lam γ2 μ g₂)
    {c₁ c₂ d₁ d₂ : ℂ}
    (hbF : ∀ x ∈ Ioo (-1 : ℝ) 1, Tendsto (fun ε : ℝ => F (x + ε * I)) (𝓝[>] 0)
      (𝓝 (c₁ * f₁ x + c₂ * f₂ x)))
    (hbG : ∀ x ∈ Ioo (-1 : ℝ) 1, Tendsto (fun ε : ℝ => G (x + ε * I)) (𝓝[>] 0)
      (𝓝 (d₁ * g₁ x + d₂ * g₂ x)))
    {z : ℂ} (hz : z ∈ spheroidalCutPlane) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (1 - z ^ 2) * (F z * deriv G z - deriv F z * G z) =
      (1 - (x : ℂ) ^ 2) * ((c₁ * f₁ x + c₂ * f₂ x) *
          (d₁ * ((deriv g₁ x : ℝ) : ℂ) + d₂ * ((deriv g₂ x : ℝ) : ℂ)) -
        (c₁ * ((deriv f₁ x : ℝ) : ℂ) + c₂ * ((deriv f₂ x : ℝ) : ℂ)) *
          (d₁ * g₁ x + d₂ * g₂ x)) := by
  obtain ⟨KF, hKF, hKFe, hKFx⟩ := exists_doubleCut_of_boundary hF hf₁ hf₂ hbF
  obtain ⟨KG, hKG, hKGe, hKGx⟩ := exists_doubleCut_of_boundary hG hg₁ hg₂ hbG
  have hI := upper_subset_cut I_mem_upper
  have e1 := isSpheroidalSolutionOn_wronskian_const isOpen_spheroidalCutPlane isPreconnected_cut
    hF hG hz hI
  have hevF : KF =ᶠ[𝓝 I] F := eventually_of_mem (isOpen_upper.mem_nhds I_mem_upper) hKFe
  have hevG : KG =ᶠ[𝓝 I] G := eventually_of_mem (isOpen_upper.mem_nhds I_mem_upper) hKGe
  have e2 := isSpheroidalSolutionOn_wronskian_const isOpen_spheroidalDoubleCutPlane
    isPreconnected_doubleCut hKF hKG (upper_subset_doubleCut I_mem_upper) (ofReal_mem_doubleCut hx)
  rw [hevF.eq_of_nhds, hevG.eq_of_nhds, hevF.deriv_eq, hevG.deriv_eq] at e2
  rw [e1, e2, (hKFx x hx).1, (hKFx x hx).2, (hKGx x hx).1, (hKGx x hx).2]

end DLMF.Spheroidal
