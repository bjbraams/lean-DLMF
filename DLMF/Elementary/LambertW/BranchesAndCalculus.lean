/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.LogExpBasic
public import DLMF.Gamma.Asymptotics
public import DLMFMathlib.Analysis.Complex.LagrangeBurmann
public import DLMF.Core.Framework
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Branches and calculus of the Lambert W function

Branch definitions, differential identities and local analytic properties of Lambert W.

Source references and common attribution are retained in
`DLMF.Elementary.LambertW`.
-/

@[expose] public section

open Complex Filter Set Finset

open scoped Topology Real

noncomputable section

namespace DLMF.Elementary

/-- The principal Lambert branch domain with its square-root cut removed. -/
def lambertPrincipalDomain : Set ℂ :=
  {z | -Real.exp (-1) < z.re ∨ z.im ≠ 0}

/-- Analytic and boundary normalization determining every integer Lambert branch. -/
structure LambertBranchFamily where
  /-- Upper-side branch values. -/
  value : ℤ → ℂ → ℂ
  /-- The defining inverse equation. -/
  equation : ∀ k z, z ≠ 0 ∨ k = 0 → value k z * Complex.exp (value k z) = z
  /-- Canonical totalization outside the nonprincipal branch domains. -/
  zero : ∀ k, value k 0 = 0
  /-- Principal-branch holomorphy, including the origin. -/
  principal_analytic : AnalyticOnNhd ℂ (value 0) lambertPrincipalDomain
  /-- Holomorphy of all other branches on the ordinary slit plane. -/
  other_analytic : ∀ k, k ≠ 0 → AnalyticOnNhd ℂ (value k) Complex.slitPlane
  /-- The principal branch is the nonnegative inverse at the positive basepoint. -/
  principal_basepoint : (value 0 1).im = 0 ∧ 0 ≤ (value 0 1).re
  /-- Positive branch indices at the positive basepoint. -/
  positive_basepoint : ∀ k : ℤ, 0 < k →
    (2 * k - 1 : ℝ) * Real.pi < (value k 1).im ∧ (value k 1).im < 2 * k * Real.pi
  /-- Negative branch indices at the positive basepoint. -/
  negative_basepoint : ∀ k : ℤ, k < 0 →
    2 * k * Real.pi < (value k 1).im ∧ (value k 1).im < (2 * k + 1 : ℝ) * Real.pi
  /-- Values on the cut are limits from its upper side. -/
  upper_boundary : ∀ k (x : ℝ), x < 0 →
    Tendsto (value k) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (value k x))

/-- `y ↦ y e^y` is strictly increasing on `[-1, ∞)`. -/
lemma lwR4_strictMonoOn : StrictMonoOn (fun y : ℝ => y * Real.exp y) (Ici (-1)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · exact (continuous_id.mul Real.continuous_exp).continuousOn
  · intro y hy
    rw [interior_Ici] at hy
    have : deriv (fun y : ℝ => y * Real.exp y) y = (y + 1) * Real.exp y := by
      have := (hasDerivAt_id y).fun_mul (Real.hasDerivAt_exp y)
      simp only [id] at this; rw [this.deriv]; ring
    rw [this]; exact mul_pos (by simp at hy; linarith) (Real.exp_pos _)

/-- `-1/e` is the strict minimum of `y e^y` on the real line. -/
lemma lwR4_gt_branchPoint {y : ℝ} (hy : y ≠ -1) : -Real.exp (-1) < y * Real.exp y := by
  have hu : -(y + 1) ≠ 0 := by intro h; apply hy; linarith
  have h1 := Real.add_one_lt_exp hu
  have he : Real.exp y * Real.exp (-(y + 1)) = Real.exp (-1) := by
    rw [← Real.exp_add]; ring_nf
  have hpos : 0 < Real.exp y := Real.exp_pos _
  nlinarith [Real.exp_pos (-(y+1))]

/-- Local injectivity of `w ↦ w e^w` away from the critical point `-1`. -/
lemma lwR4_locInj {w₀ : ℂ} (h : 1 + w₀ ≠ 0) :
    ∃ ε > 0, InjOn (fun w : ℂ => w * Complex.exp w) (Metric.ball w₀ ε) := by
  have hf : HasStrictDerivAt (fun w : ℂ => w * Complex.exp w)
      (1 * Complex.exp w₀ + w₀ * Complex.exp w₀) w₀ :=
    (hasStrictDerivAt_id w₀).mul (Complex.hasStrictDerivAt_exp w₀)
  have hne : 1 * Complex.exp w₀ + w₀ * Complex.exp w₀ ≠ 0 := by
    rw [← add_mul]; exact mul_ne_zero h (Complex.exp_ne_zero _)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hf.eventually_left_inverse hne)
  refine ⟨ε, hε, fun a ha b hb hab => ?_⟩
  have ha' := hball ha; have hb' := hball hb
  simp only [mem_ofPred_eq] at ha' hb'
  rw [← ha', ← hb']
  exact congrArg _ hab

/-- The open analytic domain of the branch `k`. -/
def lwR4_dom (k : ℤ) : Set ℂ := if k = 0 then lambertPrincipalDomain else Complex.slitPlane

/-- The `if`-form of the branch domain hypotheses. -/
lemma lwR4_mem_dom_iff (k : ℤ) (z : ℂ) :
    (if k = 0 then z ∈ lambertPrincipalDomain else z ∈ Complex.slitPlane) ↔ z ∈ lwR4_dom k := by
  unfold lwR4_dom; split_ifs <;> rfl

/-- The principal domain is open. -/
lemma lwR4_isOpen_principal : IsOpen lambertPrincipalDomain :=
  (isOpen_lt continuous_const Complex.continuous_re).union
    (isOpen_ne_fun Complex.continuous_im continuous_const)

/-- Each branch domain is open. -/
lemma lwR4_isOpen_dom (k : ℤ) : IsOpen (lwR4_dom k) := by
  unfold lwR4_dom; split_ifs
  · exact lwR4_isOpen_principal
  · exact Complex.isOpen_slitPlane

/-- The branch point `-1/e` lies in no branch domain. -/
lemma lwR4_branchPoint_not_mem (k : ℤ) : ((-Real.exp (-1) : ℝ) : ℂ) ∉ lwR4_dom k := by
  have he : 0 < Real.exp (-1) := Real.exp_pos _
  unfold lwR4_dom; split_ifs
  · simp only [lambertPrincipalDomain, mem_ofPred_eq, ofReal_re, ofReal_im, ne_eq,
      not_true_eq_false, or_false, lt_self_iff_false, not_false_eq_true]
  · rw [Complex.mem_slitPlane_iff]
    simp only [ofReal_re, ofReal_im, ne_eq, not_true_eq_false, or_false, not_lt]
    linarith

/-- Two continuous solutions of `w e^w = z` on a preconnected open set either agree everywhere
or nowhere, provided one of them avoids the critical value `-1`. -/
lemma lwR4_eq_or_ne {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) {f g : ℂ → ℂ}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hfe : ∀ z ∈ U, f z * Complex.exp (f z) = z) (hge : ∀ z ∈ U, g z * Complex.exp (g z) = z)
    (hf1 : ∀ z ∈ U, 1 + f z ≠ 0) :
    (∀ z ∈ U, f z = g z) ∨ (∀ z ∈ U, f z ≠ g z) := by
  set u := {z | z ∈ U ∧ f z = g z}
  set v := {z | z ∈ U ∧ f z ≠ g z}
  have hu : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    rintro z0 ⟨hz0, heq⟩
    obtain ⟨ε, hε, hinj⟩ := lwR4_locInj (hf1 z0 hz0)
    have hfc := (hf.continuousAt (hU.mem_nhds hz0)).preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
    have hball : Metric.ball (f z0) ε ∈ 𝓝 (g z0) := by
      rw [← heq]; exact Metric.ball_mem_nhds _ hε
    have hgc := (hg.continuousAt (hU.mem_nhds hz0)).preimage_mem_nhds hball
    filter_upwards [hU.mem_nhds hz0, hfc, hgc] with z hz h1 h2
    exact ⟨hz, hinj h1 h2 ((hfe z hz).trans (hge z hz).symm)⟩
  have hv : IsOpen v := by
    rw [isOpen_iff_mem_nhds]
    rintro z0 ⟨hz0, hne⟩
    filter_upwards [hU.mem_nhds hz0, ((hf.continuousAt (hU.mem_nhds hz0)).ne_iff_eventually_ne
      (hg.continuousAt (hU.mem_nhds hz0))).mp hne] with z hz h
    exact ⟨hz, h⟩
  have huv : Disjoint u v := by
    rw [Set.disjoint_left]; rintro z ⟨_, h1⟩ ⟨_, h2⟩; exact h2 h1
  have hsub : U ⊆ u ∪ v := by
    intro z hz; by_cases h : f z = g z
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  by_cases hne : (U ∩ u).Nonempty
  · left
    intro z hz
    exact (hUc.subset_left_of_subset_union hu hv huv hsub hne hz).2
  · right
    intro z hz heq
    exact hne ⟨z, hz, hz, heq⟩

/-- The auxiliary function whose zeros are the imaginary parts of roots of `w e^w = 1`. -/
noncomputable def lwR4_psi (y : ℝ) : ℝ := Real.log (-y / Real.sin y) - y * Real.cos y / Real.sin y

/-- The derivative of `lwR4_psi`, with numerator `(sin y - y cos y)² + y² sin² y`. -/
lemma lwR4_psi_hasDerivAt {y : ℝ} (hy : y ≠ 0) (hs : Real.sin y ≠ 0) :
    HasDerivAt lwR4_psi (((Real.sin y - y * Real.cos y) ^ 2 + y ^ 2 * Real.sin y ^ 2) /
      (y * Real.sin y ^ 2)) y := by
  have hg : HasDerivAt (fun y => -y / Real.sin y)
      ((-1 * Real.sin y - -y * Real.cos y) / Real.sin y ^ 2) y :=
    ((hasDerivAt_id y).neg.div (Real.hasDerivAt_sin y) hs)
  have hgne : -y / Real.sin y ≠ 0 := div_ne_zero (neg_ne_zero.mpr hy) hs
  have hh : HasDerivAt (fun y => y * Real.cos y / Real.sin y)
      (((1 * Real.cos y + y * -Real.sin y) * Real.sin y - y * Real.cos y * Real.cos y) /
        Real.sin y ^ 2) y :=
    ((hasDerivAt_id y).mul (Real.hasDerivAt_cos y)).div (Real.hasDerivAt_sin y) hs
  refine ((hg.log hgne).sub hh).congr_deriv ?_
  have hc := Real.sin_sq_add_cos_sq y
  field_simp
  ring

/-- Roots of `w e^w = 1` off the real multiples of `π`: the real part is `-y cot y` and
`ψ(y) = 0`. -/
lemma lwR4_root_parts {w : ℂ} (hw : w * Complex.exp w = 1) (hs : Real.sin w.im ≠ 0) :
    w.re = -w.im * Real.cos w.im / Real.sin w.im ∧ lwR4_psi w.im = 0 := by
  set x := w.re; set y := w.im
  have hre := congrArg Complex.re hw
  have him := congrArg Complex.im hw
  simp only [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im, one_re,
    one_im] at hre him
  change x * (Real.exp x * Real.cos y) - y * (Real.exp x * Real.sin y) = 1 at hre
  change x * (Real.exp x * Real.sin y) + y * (Real.exp x * Real.cos y) = 0 at him
  have hex := Real.exp_pos x
  have h1 : x * Real.sin y + y * Real.cos y = 0 := by
    have : Real.exp x * (x * Real.sin y + y * Real.cos y) = 0 := by linear_combination him
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hex.ne'
    · exact h
  have hx : x = -y * Real.cos y / Real.sin y := by
    field_simp; linear_combination h1
  have hc := Real.sin_sq_add_cos_sq y
  have h2 : Real.exp x * (-y / Real.sin y) = 1 := by
    rw [mul_div_assoc', div_eq_iff hs]
    linear_combination (Real.sin y) * hre + (-(Real.exp x) * Real.cos y) * h1 +
      (y * Real.exp x) * hc
  refine ⟨hx, ?_⟩
  have hg : -y / Real.sin y = Real.exp (-x) := by
    rw [Real.exp_neg]; exact eq_inv_of_mul_eq_one_right h2
  unfold lwR4_psi
  rw [hg, Real.log_exp, hx]; ring

/-- Uniqueness of the root of `w e^w = 1` in a horizontal strip `mπ < Im w < (m+1)π`. -/
lemma lwR4_strip_unique (m : ℤ) {w₁ w₂ : ℂ} (h₁ : w₁ * Complex.exp w₁ = 1)
    (h₂ : w₂ * Complex.exp w₂ = 1)
    (hy₁ : w₁.im ∈ Ioo (m * π) ((m + 1) * π)) (hy₂ : w₂.im ∈ Ioo (m * π) ((m + 1) * π)) :
    w₁ = w₂ := by
  have hsin : ∀ y ∈ Ioo (m * π) ((m + 1) * π), Real.sin y ≠ 0 := by
    intro y hy h
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
    rw [← hn] at hy
    obtain ⟨a, b⟩ := hy
    have a' : (m : ℝ) < n := lt_of_mul_lt_mul_right a Real.pi_pos.le
    have b' : (n : ℝ) < m + 1 := lt_of_mul_lt_mul_right b Real.pi_pos.le
    have : m < n := by exact_mod_cast a'
    have : n < m + 1 := by exact_mod_cast b'
    omega
  have hy0 : ∀ y ∈ Ioo (m * π) ((m + 1) * π), y ≠ 0 := by
    intro y hy h; apply hsin y hy; rw [h, Real.sin_zero]
  have hcont : ContinuousOn lwR4_psi (Ioo (m * π) ((m + 1) * π)) := fun y hy =>
    (lwR4_psi_hasDerivAt (hy0 y hy) (hsin y hy)).continuousAt.continuousWithinAt
  have hinj : InjOn lwR4_psi (Ioo (m * π) ((m + 1) * π)) := by
    rcases le_or_gt 0 m with hm | hm
    · have hpos : ∀ y ∈ Ioo (m * π) ((m + 1) * π), 0 < y := fun y hy => by
        have : (0 : ℝ) ≤ m := by exact_mod_cast hm
        have := hy.1; nlinarith [Real.pi_pos]
      refine (strictMonoOn_of_deriv_pos (convex_Ioo _ _) hcont fun y hy => ?_).injOn
      rw [interior_Ioo] at hy
      rw [(lwR4_psi_hasDerivAt (hy0 y hy) (hsin y hy)).deriv]
      have h1 := hsin y hy; have h2 := hpos y hy
      have hs2 : 0 < Real.sin y ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h1))
      apply div_pos
      · have : 0 < y ^ 2 * Real.sin y ^ 2 := mul_pos (pow_pos h2 2) hs2
        nlinarith [sq_nonneg (Real.sin y - y * Real.cos y)]
      · exact mul_pos h2 hs2
    · have hneg : ∀ y ∈ Ioo (m * π) ((m + 1) * π), y < 0 := fun y hy => by
        have : (m : ℝ) + 1 ≤ 0 := by exact_mod_cast hm
        have := hy.2; nlinarith [Real.pi_pos]
      refine (strictAntiOn_of_deriv_neg (convex_Ioo _ _) hcont fun y hy => ?_).injOn
      rw [interior_Ioo] at hy
      rw [(lwR4_psi_hasDerivAt (hy0 y hy) (hsin y hy)).deriv]
      have h1 := hsin y hy; have h2 := hneg y hy
      have hs2 : 0 < Real.sin y ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h1))
      apply div_neg_of_pos_of_neg
      · have : 0 < y ^ 2 * Real.sin y ^ 2 :=
          mul_pos (lt_of_le_of_ne (sq_nonneg y) (Ne.symm (pow_ne_zero 2 h2.ne))) hs2
        nlinarith [sq_nonneg (Real.sin y - y * Real.cos y)]
      · nlinarith
  obtain ⟨hx₁, hp₁⟩ := lwR4_root_parts h₁ (hsin _ hy₁)
  obtain ⟨hx₂, hp₂⟩ := lwR4_root_parts h₂ (hsin _ hy₂)
  have hy : w₁.im = w₂.im := hinj hy₁ hy₂ (hp₁.trans hp₂.symm)
  apply Complex.ext
  · rw [hx₁, hx₂, hy]
  · exact hy

/-- Every branch family satisfies the inverse equation on the analytic domains. -/
lemma lwR4_fam_equation (F : LambertBranchFamily) {k : ℤ} {z : ℂ} (hz : z ∈ lwR4_dom k) :
    F.value k z * Complex.exp (F.value k z) = z := by
  apply F.equation
  unfold lwR4_dom at hz; split_ifs at hz with h
  · exact Or.inr h
  · exact Or.inl (Complex.slitPlane_ne_zero hz)

/-- Branch families avoid the critical value `-1` on the analytic domains. -/
lemma lwR4_fam_one_add_ne_zero (F : LambertBranchFamily) {k : ℤ} {z : ℂ} (hz : z ∈ lwR4_dom k) :
    1 + F.value k z ≠ 0 := by
  intro h
  have hW : F.value k z = -1 := by linear_combination h
  have := lwR4_fam_equation F hz
  rw [hW] at this
  apply lwR4_branchPoint_not_mem k
  convert hz using 1
  rw [← this]; push_cast; ring

/-- Continuity of each branch on its analytic domain. -/
lemma lwR4_fam_continuousOn (F : LambertBranchFamily) (k : ℤ) :
    ContinuousOn (F.value k) (lwR4_dom k) := by
  unfold lwR4_dom; split_ifs with h
  · subst h; exact F.principal_analytic.continuousOn
  · exact (F.other_analytic k h).continuousOn

/-- Each branch domain is preconnected. -/
lemma lwR4_isPreconnected_dom (k : ℤ) : IsPreconnected (lwR4_dom k) := by
  unfold lwR4_dom; split_ifs
  · have hstar : StarConvex ℝ 0 lambertPrincipalDomain := by
      intro y hy a b ha hb hab
      simp only [smul_zero, zero_add]
      rcases hb.lt_or_eq with hb' | hb'
      · rcases hy with h | h
        · left
          have : (b • y).re = b * y.re := by simp
          rw [this]
          rcases le_or_gt 0 y.re with h0 | h0
          · nlinarith [Real.exp_pos (-1)]
          · nlinarith
        · right; simp [hb'.ne', h]
      · rw [← hb']; left; simp [Real.exp_pos]
    exact (hstar.isPathConnected (by left; simp [Real.exp_pos])).isConnected.isPreconnected
  · exact (Complex.starConvex_one_slitPlane.isPathConnected
      (by simp [Complex.mem_slitPlane_iff])).isConnected.isPreconnected

/-- The basepoint `1` lies in every branch domain. -/
lemma lwR4_one_mem_dom (k : ℤ) : (1 : ℂ) ∈ lwR4_dom k := by
  unfold lwR4_dom; split_ifs
  · left; simp only [one_re]; linarith [Real.exp_pos (-1)]
  · simp [Complex.mem_slitPlane_iff]

/-- Two branch families agree at the basepoint `1`. -/
lemma lwR4_fam_basepoint (F G : LambertBranchFamily) (k : ℤ) : F.value k 1 = G.value k 1 := by
  have hF := lwR4_fam_equation F (lwR4_one_mem_dom k)
  have hG := lwR4_fam_equation G (lwR4_one_mem_dom k)
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · apply lwR4_strip_unique (2 * k) hF hG
    · have := F.negative_basepoint k hk; push_cast; constructor <;> linarith [this.1, this.2]
    · have := G.negative_basepoint k hk; push_cast; constructor <;> linarith [this.1, this.2]
  · obtain ⟨hFi, hFr⟩ := F.principal_basepoint
    obtain ⟨hGi, hGr⟩ := G.principal_basepoint
    have hFw : F.value 0 1 = ((F.value 0 1).re : ℂ) := Complex.ext (by simp) (by simpa using hFi)
    have hGw : G.value 0 1 = ((G.value 0 1).re : ℂ) := Complex.ext (by simp) (by simpa using hGi)
    have eF : (F.value 0 1).re * Real.exp (F.value 0 1).re = 1 := by
      rw [hFw, ← Complex.ofReal_exp, ← Complex.ofReal_mul] at hF; exact_mod_cast hF
    have eG : (G.value 0 1).re * Real.exp (G.value 0 1).re = 1 := by
      rw [hGw, ← Complex.ofReal_exp, ← Complex.ofReal_mul] at hG; exact_mod_cast hG
    have := lwR4_strictMonoOn.injOn (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith))
      (eF.trans eG.symm)
    rw [hFw, hGw, this]
  · apply lwR4_strip_unique (2 * k - 1) hF hG
    · have := F.positive_basepoint k hk; push_cast; constructor <;> linarith [this.1, this.2]
    · have := G.positive_basepoint k hk; push_cast; constructor <;> linarith [this.1, this.2]

/-- Existence of the normalized integer branch family (4.13, defining prose). -/
theorem exists_lambertBranchFamily : Nonempty LambertBranchFamily := by
  sorry

/-- Uniqueness of the normalized branches, including the declared totalization. -/
theorem lambertBranchFamily_unique (F G : LambertBranchFamily) : F.value = G.value := by
  funext k
  -- agreement on the analytic domain
  have hdom : ∀ z ∈ lwR4_dom k, F.value k z = G.value k z := by
    rcases lwR4_eq_or_ne (lwR4_isOpen_dom k) (lwR4_isPreconnected_dom k)
      (lwR4_fam_continuousOn F k) (lwR4_fam_continuousOn G k)
      (fun z hz => lwR4_fam_equation F hz) (fun z hz => lwR4_fam_equation G hz)
      (fun z hz => lwR4_fam_one_add_ne_zero F hz) with h | h
    · exact h
    · exact absurd (lwR4_fam_basepoint F G k) (h 1 (lwR4_one_mem_dom k))
  have hupper : ∀ z : ℂ, 0 < z.im → z ∈ lwR4_dom k := by
    intro z hz
    unfold lwR4_dom; split_ifs
    · right; exact hz.ne'
    · exact Complex.mem_slitPlane_iff.mpr (Or.inr hz.ne')
  -- agreement on the negative real axis via upper boundary values
  have hcut : ∀ x : ℝ, x < 0 → F.value k x = G.value k x := by
    intro x hx
    have hne : (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)).NeBot := by
      apply mem_closure_iff_nhdsWithin_neBot.mp
      rw [Complex.closure_setOfPred_lt_im]; simp
    have h1 := F.upper_boundary k x hx
    have h2 := G.upper_boundary k x hx
    have h1' : Tendsto (G.value k) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (F.value k x)) := by
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hdom z (hupper z hz)
    exact tendsto_nhds_unique h1' h2
  funext z
  by_cases hz : z ∈ lwR4_dom k
  · exact hdom z hz
  · have him : z.im = 0 := by
      by_contra h
      apply hz; unfold lwR4_dom; split_ifs
      · right; exact h
      · exact Complex.mem_slitPlane_iff.mpr (Or.inr h)
    have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
    rcases lt_trichotomy z.re 0 with hneg | hzero | hpos
    · rw [hz']; exact hcut _ hneg
    · have : z = 0 := by rw [hz', hzero]; simp
      rw [this, F.zero, G.zero]
    · exfalso; apply hz; unfold lwR4_dom; split_ifs
      · left; linarith [Real.exp_pos (-1)]
      · exact Complex.mem_slitPlane_iff.mpr (Or.inl hpos)

/-- The Lambert W branch with integer index, using the upper-side convention on cuts. -/
def lambertW (k : ℤ) (z : ℂ) : ℂ :=
  (Classical.choice exists_lambertBranchFamily).value k z

/-- Lower-side cut values; away from the cut this agrees with analytic continuation. -/
def lambertWLower (k : ℤ) (z : ℂ) : ℂ := star (lambertW (-k) (star z))

/-- Wright omega with its unwinding-number branch convention. -/
def wrightOmega (z : ℂ) : ℂ :=
  lambertW ⌈(z.im - Real.pi) / (2 * Real.pi)⌉ (Complex.exp z)

/-- The tree T-function on the principal branch. -/
def treeT (z : ℂ) : ℂ := -lambertW 0 (-z)

/-- The Lambert inverse equation on every valid branch. -/
@[dlmf 4.13.E1]
theorem lambertW_equation (k : ℤ) (z : ℂ) (hz : z ≠ 0 ∨ k = 0) :
    lambertW k z * Complex.exp (lambertW k z) = z :=
  (Classical.choice exists_lambertBranchFamily).equation k z hz

/-- The logarithmic sheet used in the branch asymptotics. -/
def lambertXi (k : ℤ) (z : ℂ) : ℂ := Complex.log z + 2 * Real.pi * I * k

/-- Derivative polynomials, given by their full recurrence (4.13.4_2). -/
@[dlmf 4.13.E4_2]
def lambertDerivPolynomial : ℕ → Polynomial ℂ
  | 0 => 1
  | n + 1 => (1 + Polynomial.X) * (lambertDerivPolynomial n).derivative +
      (1 - Polynomial.C (n + 1 : ℂ) * (Polynomial.X + 3)) * lambertDerivPolynomial n

/-- Coefficients of the logarithmic square-root parameter at the branch point. -/
def lambertC (n : ℕ) : ℝ :=
  if h0 : n = 0 then 1 else if h1 : n = 1 then 1 else
    lambertC (n - 1) / (n + 1) - 1 / 2 *
      ∑ k : Fin (n - 2), lambertC (k.val + 2) * lambertC (n - 1 - k.val)
termination_by n
decreasing_by all_goals omega

/-- Coefficients in the principal Puiseux parameter at the branch point. -/
def lambertD (m : ℕ) : ℝ :=
  if h0 : m = 0 then -1 else if h1 : m = 1 then Real.sqrt 2 else
    (-2 * lambertD (m - 1) + (m - 1 : ℝ) / 2 *
      (∑ k : Fin (m - 2), lambertD (k.val + 1) * lambertD (m - 2 - k.val)) -
      (m + 1 : ℝ) / 2 *
      (∑ k : Fin (m - 2), lambertD (k.val + 2) * lambertD (m - 1 - k.val))) /
      ((m + 1 : ℝ) * Real.sqrt 2)
termination_by m
decreasing_by all_goals omega

/-- The normalized removable quotient `W₀(z)/z` at zero. -/
def lambertWOver (z : ℂ) : ℂ := if z = 0 then 1 else lambertW 0 z / z

/-- The exact nth outer term of the large-argument Lambert expansion. -/
def lambertAsymptoticTerm (k : ℤ) (z : ℂ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ (n + 1) / lambertXi k z ^ (n + 1) *
    ∑ m ∈ range (n + 1), (Nat.stirlingFirst (n + 1) (n + 1 - m) : ℂ) *
      (-Complex.log (lambertXi k z)) ^ (m + 1) / (m + 1).factorial

/-- All integer branches have their normalized leading asymptotic at complex infinity. -/
@[dlmf 4.13.E1_1]
theorem lambertW_leading_asymptotic (k : ℤ) :
    Tendsto (fun z : ℂ => lambertW k z - lambertXi k z + Complex.log (lambertXi k z))
      (Bornology.cobounded ℂ) (𝓝 0) := by
  sorry

/-- The Wright omega equation with the closed logarithm on cut values. -/
@[dlmf 4.13.E1_2]
theorem wrightOmega_equation (z : ℂ) : ∃ l ∈ closedLogValues (wrightOmega z), wrightOmega z + l = z := by
  sorry

/-- The usual principal logarithm form whenever omega lies off its logarithm cut. -/
@[dlmf 4.13.E1_2]
theorem wrightOmega_equation_principal {z : ℂ} (hz : wrightOmega z ∈ Complex.slitPlane) :
    wrightOmega z + Complex.log (wrightOmega z) = z := by
  sorry

/-- The tree T-function satisfies its inverse equation. -/
@[dlmf 4.13.E1_3]
theorem treeT_equation (z : ℂ) : treeT z * Complex.exp (-treeT z) = z := by
  have := lambertW_equation 0 (-z) (Or.inr rfl)
  simp only [treeT, neg_neg]
  linear_combination -this

/-- A real point lies in the principal domain iff it exceeds `-1/e`. -/
lemma lwR4_mem_principal_real {x : ℝ} : (x : ℂ) ∈ lambertPrincipalDomain ↔ -Real.exp (-1) < x := by
  simp [lambertPrincipalDomain]

/-- On `(-1/e, ∞)` the principal branch is real and larger than `-1`. -/
lemma lwR4_principal_real_gt {x : ℝ} (hx : -Real.exp (-1) < x) :
    (lambertW 0 x).im = 0 ∧ -1 < (lambertW 0 x).re := by
  set a := -Real.exp (-1)
  have hcont : ∀ x : ℝ, a < x → ContinuousAt (fun x : ℝ => lambertW 0 x) x := fun x hx =>
    (((Classical.choice exists_lambertBranchFamily).principal_analytic _ (lwR4_mem_principal_real.mpr hx)).continuousAt).comp
      Complex.continuous_ofReal.continuousAt
  set u := {x : ℝ | a < x ∧ (lambertW 0 x).im = 0 ∧ -1 < (lambertW 0 x).re}
  set v := {x : ℝ | a < x ∧ ((lambertW 0 x).im ≠ 0 ∨ (lambertW 0 x).re < -1)}
  have hv : IsOpen v := by
    rw [isOpen_iff_mem_nhds]
    intro x0 hx0
    have hO : IsOpen {w : ℂ | w.im ≠ 0 ∨ w.re < -1} :=
      (isOpen_ne_fun Complex.continuous_im continuous_const).union
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [Ioi_mem_nhds hx0.1, (hcont x0 hx0.1).preimage_mem_nhds
      (hO.mem_nhds hx0.2)] with x h1 h2
    exact ⟨h1, h2⟩
  have hu : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    intro x0 hx0
    obtain ⟨hax, him, hre⟩ := hx0
    set w0 := lambertW 0 x0
    have h1 : 1 + w0 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    obtain ⟨ε, hε, hinj⟩ := lwR4_locInj h1
    set ε' := min ε (w0.re + 1)
    have hε' : 0 < ε' := lt_min hε (by linarith)
    filter_upwards [Ioi_mem_nhds hax, (hcont x0 hax).preimage_mem_nhds
      (Metric.ball_mem_nhds w0 hε')] with x hxa hball
    simp only [Set.mem_preimage, Metric.mem_ball] at hball
    have hw0 : (starRingEnd ℂ) w0 = w0 := Complex.conj_eq_iff_im.mpr him
    have hc : dist ((starRingEnd ℂ) (lambertW 0 x)) w0 < ε' := by
      rw [dist_eq_norm, ← hw0, ← map_sub, Complex.norm_conj, ← dist_eq_norm]; exact hball
    have hmem : (x : ℂ) ∈ lambertPrincipalDomain := lwR4_mem_principal_real.mpr hxa
    have heq := lambertW_equation 0 x (Or.inr rfl)
    have hconj : (starRingEnd ℂ) (lambertW 0 x) * Complex.exp ((starRingEnd ℂ) (lambertW 0 x)) =
        lambertW 0 x * Complex.exp (lambertW 0 x) := by
      rw [Complex.exp_conj, ← map_mul, heq, Complex.conj_ofReal]
    have hself := hinj (Metric.mem_ball.mpr (lt_of_lt_of_le hc (min_le_left _ _)))
      (Metric.mem_ball.mpr (lt_of_lt_of_le hball (min_le_left _ _))) hconj
    refine ⟨hxa, Complex.conj_eq_iff_im.mp hself, ?_⟩
    have := (Complex.abs_re_le_norm (lambertW 0 x - w0)).trans_lt
      ((dist_eq_norm _ _).symm.trans_lt (lt_of_lt_of_le hball (min_le_right _ _)))
    rw [Complex.sub_re, abs_lt] at this
    linarith
  have huv : Disjoint u v := by
    rw [Set.disjoint_left]
    rintro x ⟨_, h1, h2⟩ ⟨_, h3⟩
    rcases h3 with h3 | h3
    · exact h3 h1
    · linarith
  have hsub : Ioi a ⊆ u ∪ v := by
    intro x hx
    by_cases him : (lambertW 0 x).im = 0
    · rcases lt_trichotomy (lambertW 0 x).re (-1) with h | h | h
      · exact Or.inr ⟨hx, Or.inr h⟩
      · exfalso
        have hW : lambertW 0 x = -1 := Complex.ext (by simpa using h) (by simpa using him)
        have heq := lambertW_equation 0 x (Or.inr rfl)
        rw [hW] at heq
        have : ((-1 * Real.exp (-1) : ℝ) : ℂ) = (x : ℂ) := by push_cast; exact heq
        have := Complex.ofReal_injective this
        simp only [Set.mem_Ioi] at hx; linarith
      · exact Or.inl ⟨hx, him, h⟩
    · exact Or.inr ⟨hx, Or.inl him⟩
  have h1 : (1 : ℝ) ∈ Ioi a ∩ u := by
    have hb := (Classical.choice exists_lambertBranchFamily).principal_basepoint
    have ha : a < 1 := by simp only [a]; linarith [Real.exp_pos (-1)]
    refine ⟨ha, ha, ?_, ?_⟩
    · simpa [lambertW] using hb.1
    · have := hb.2; simp only [lambertW, Complex.ofReal_one]; linarith
  have := isPreconnected_Ioi.subset_left_of_subset_union hu hv huv hsub ⟨1, h1⟩ hx
  exact ⟨this.2.1, this.2.2⟩

/-- On `(-1/e, ∞)` the principal branch is the real inverse of `y e^y` on `(-1, ∞)`. -/
lemma lwR4_principal_ofReal {x : ℝ} (hx : -Real.exp (-1) < x) :
    lambertW 0 x = ((lambertW 0 x).re : ℂ) ∧ -1 < (lambertW 0 x).re ∧
      (lambertW 0 x).re * Real.exp (lambertW 0 x).re = x := by
  obtain ⟨him, hre⟩ := lwR4_principal_real_gt hx
  have hW : lambertW 0 x = ((lambertW 0 x).re : ℂ) := Complex.ext (by simp) (by simpa using him)
  refine ⟨hW, hre, ?_⟩
  have heq := lambertW_equation 0 x (Or.inr rfl)
  rw [hW, ← Complex.ofReal_exp, ← Complex.ofReal_mul] at heq
  exact_mod_cast heq

/-- The principal inverse of `y e^y` for `y > -1`. -/
lemma lwR4_exp_inverse_gt {y : ℝ} (hy : -1 < y) : lambertW 0 ((y * Real.exp y : ℝ) : ℂ) = y := by
  have hx : -Real.exp (-1) < y * Real.exp y := lwR4_gt_branchPoint (by linarith)
  obtain ⟨hW, hre, heq⟩ := lwR4_principal_ofReal hx
  have : (lambertW 0 ↑(y * Real.exp y)).re = y :=
    lwR4_strictMonoOn.injOn (Set.mem_Ici.mpr hre.le) (Set.mem_Ici.mpr hy.le) heq
  rw [hW, this]

/-- The principal branch at the branch point, from the upper boundary normalization. -/
lemma lwR4_principal_branchPoint : lambertW 0 ((-Real.exp (-1) : ℝ) : ℂ) = -1 := by
  set a : ℝ := -Real.exp (-1)
  have hb := (Classical.choice exists_lambertBranchFamily).upper_boundary 0 a
    (by simp only [a]; linarith [Real.exp_pos (-1)])
  change Tendsto (lambertW 0) _ (𝓝 (lambertW 0 a)) at hb
  rw [Metric.tendsto_nhdsWithin_nhds] at hb
  set L := lambertW 0 a
  refine eq_of_forall_dist_le fun ε3 hε3 => ?_
  set ε := ε3 / 3
  have hε : 0 < ε := by positivity
  obtain ⟨δ, hδ, hL⟩ := hb ε hε
  -- a real point close to the branch point with value close to `-1`
  have hfc : ContinuousAt (fun y : ℝ => y * Real.exp y) (-1) :=
    (continuous_id.mul Real.continuous_exp).continuousAt
  obtain ⟨η, hη, hfη⟩ := Metric.continuousAt_iff.mp hfc (δ / 2) (by positivity)
  set t := min η ε / 2
  have ht : 0 < t := by positivity
  have htη : t < η := by have := min_le_left η ε; simp only [t]; linarith
  have htε : t < ε := by have := min_le_right η ε; simp only [t]; linarith
  set y := -1 + t
  set x := y * Real.exp y
  have hxa : dist x a < δ / 2 := by
    have := hfη (x := y) (by simp only [y, Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
    simpa [a, x] using this
  have hxa' : a < x := lwR4_gt_branchPoint (by simp only [y]; linarith)
  have hWx : lambertW 0 x = y := lwR4_exp_inverse_gt (by simp only [y]; linarith)
  -- move into the upper half-plane
  have hcx : ContinuousAt (lambertW 0) (x : ℂ) :=
    ((Classical.choice exists_lambertBranchFamily).principal_analytic _ (lwR4_mem_principal_real.mpr hxa')).continuousAt
  obtain ⟨δ', hδ', hW'⟩ := Metric.continuousAt_iff.mp hcx ε hε
  set s := min δ' (δ / 2) / 2
  have hs : 0 < s := by positivity
  have hsδ' : s < δ' := by have := min_le_left δ' (δ / 2); simp only [s]; linarith
  have hsδ : s < δ / 2 := by have := min_le_right δ' (δ / 2); simp only [s]; linarith
  set z : ℂ := x + s * I
  have hzx : dist z x < δ' := by
    simp only [z, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]; exact hsδ'
  have hzim : 0 < z.im := by simp [z, hs]
  have hza : dist z a < δ := by
    have h1 : dist z x = s := by
      simp only [z, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have h2 : dist (x : ℂ) (a : ℂ) = dist x a := by rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      Real.dist_eq]
    calc dist z a ≤ dist z x + dist (x : ℂ) a := dist_triangle _ _ _
      _ < δ := by rw [h1, h2]; linarith
  have e1 := hL hzim hza
  have e2 := hW' hzx
  rw [hWx] at e2
  have e3 : dist ((y : ℝ) : ℂ) (-1) = t := by
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by simp, dist_eq_norm, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    simp only [y]; rw [show -1 + t - -1 = t by ring, abs_of_pos ht]
  calc dist L (-1) ≤ dist L (lambertW 0 z) + dist (lambertW 0 z) (y : ℂ) + dist (y : ℂ) (-1) :=
        dist_triangle4 _ _ _ _
    _ ≤ ε3 := by rw [dist_comm L, e3]; simp only [ε] at *; linarith

/-- Exact branch-point, origin and exponential values, including both real lower branches. -/
@[dlmf 4.13.E2]
theorem lambertW_special_values  :
    lambertW 0 (-Real.exp (-1)) = -1 ∧
    lambertWLower 1 (-Real.exp (-1)) = -1 ∧
    lambertW (-1) (-Real.exp (-1)) = -1 ∧
    lambertW 0 0 = 0 ∧ lambertW 0 (Real.exp 1) = 1 := by
  sorry

/-- On the nonnegative axis there is exactly one real solution, increasing and nonnegative. -/
theorem lambertW_real_nonnegative  :
    StrictMonoOn (fun x : ℝ => (lambertW 0 x).re) (Ici 0) ∧
    ∀ x : ℝ, 0 ≤ x → (lambertW 0 x).im = 0 ∧ 0 ≤ (lambertW 0 x).re ∧
      ∀ y : ℝ, y * Real.exp y = x ↔ (y : ℂ) = lambertW 0 x := by
  have hpos : ∀ x : ℝ, 0 ≤ x → -Real.exp (-1) < x := fun x hx => by
    linarith [Real.exp_pos (-1)]
  -- the real part is nonnegative on the nonnegative axis
  have hnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ (lambertW 0 x).re := by
    intro x hx
    obtain ⟨_, _, heq⟩ := lwR4_principal_ofReal (hpos x hx)
    by_contra h
    replace h := not_le.mp h
    have : (lambertW 0 x).re * Real.exp (lambertW 0 x).re < 0 :=
      mul_neg_of_neg_of_pos h (Real.exp_pos _)
    linarith
  have hiff : ∀ x : ℝ, 0 ≤ x → ∀ y : ℝ, y * Real.exp y = x ↔ (y : ℂ) = lambertW 0 x := by
    intro x hx y
    obtain ⟨hW, hre, heq⟩ := lwR4_principal_ofReal (hpos x hx)
    constructor
    · intro hy
      have hy0 : 0 ≤ y := by
        by_contra h; replace h := not_le.mp h
        have : y * Real.exp y < 0 := mul_neg_of_neg_of_pos h (Real.exp_pos _)
        linarith
      rw [← hy]; exact (lwR4_exp_inverse_gt (by linarith)).symm
    · intro hy
      have : (lambertW 0 x).re = y := by rw [← hy]; simp
      rw [← this]; exact heq
  refine ⟨fun x1 hx1 x2 hx2 hlt => ?_, fun x hx => ⟨(lwR4_principal_real_gt (hpos x hx)).1,
    hnn x hx, hiff x hx⟩⟩
  obtain ⟨_, _, h1⟩ := lwR4_principal_ofReal (hpos x1 hx1)
  obtain ⟨_, _, h2⟩ := lwR4_principal_ofReal (hpos x2 hx2)
  have m1 := hnn x1 hx1; have m2 := hnn x2 hx2
  rw [← lwR4_strictMonoOn.lt_iff_lt (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith))]
  simp only
  rw [h1, h2]; exact hlt

/-- The two real branches on the negative interval have opposite monotonicities. -/
theorem lambertW_real_two_solutions  :
    StrictMonoOn (fun x : ℝ => (lambertW 0 x).re) (Ioo (-Real.exp (-1)) 0) ∧
    StrictAntiOn (fun x : ℝ => (lambertW (-1) x).re) (Ioo (-Real.exp (-1)) 0) ∧
    ∀ x : ℝ, x ∈ Ioo (-Real.exp (-1)) 0 →
      (lambertW 0 x).im = 0 ∧ (lambertW (-1) x).im = 0 ∧
      -1 < (lambertW 0 x).re ∧ (lambertW (-1) x).re < -1 ∧
      lambertWLower 1 x = lambertW (-1) x ∧
      ∀ y : ℝ, y * Real.exp y = x ↔
        (y : ℂ) = lambertW 0 x ∨ (y : ℂ) = lambertW (-1) x := by
  sorry

/-- Principal-branch holomorphy on the full square-root slit domain. -/
theorem lambertW_principal_analytic  : AnalyticOnNhd ℂ (lambertW 0) lambertPrincipalDomain := by
  exact (Classical.choice exists_lambertBranchFamily).principal_analytic

/-- Every nonprincipal branch is holomorphic on the logarithm slit plane. -/
theorem lambertW_other_analytic (k : ℤ) (hk : k ≠ 0) : AnalyticOnNhd ℂ (lambertW k) Complex.slitPlane := by
  exact (Classical.choice exists_lambertBranchFamily).other_analytic k hk

/-- Each branch is analytic on its domain. -/
lemma lwR4_analytic_dom (k : ℤ) : AnalyticOnNhd ℂ (lambertW k) (lwR4_dom k) := by
  unfold lwR4_dom; split_ifs with h
  · subst h; exact lambertW_principal_analytic
  · exact lambertW_other_analytic k h

/-- The inverse equation holds throughout each branch domain. -/
lemma lwR4_equation_dom {k : ℤ} {z : ℂ} (hz : z ∈ lwR4_dom k) :
    lambertW k z * Complex.exp (lambertW k z) = z := by
  apply lambertW_equation
  unfold lwR4_dom at hz; split_ifs at hz with h
  · exact Or.inr h
  · exact Or.inl (Complex.slitPlane_ne_zero hz)

/-- `1 + W_k(z) ≠ 0` on each branch domain. -/
lemma lwR4_one_add_ne_zero {k : ℤ} {z : ℂ} (hz : z ∈ lwR4_dom k) : 1 + lambertW k z ≠ 0 := by
  intro h
  have hW : lambertW k z = -1 := by linear_combination h
  have := lwR4_equation_dom hz
  rw [hW] at this
  apply lwR4_branchPoint_not_mem k
  convert hz using 1
  rw [← this]; push_cast; ring

/-- Branch values at nonzero arguments are nonzero. -/
lemma lwR4_ne_zero_of_ne {k : ℤ} {z : ℂ} (hz : z ∈ lwR4_dom k) (hne : z ≠ 0) :
    lambertW k z ≠ 0 := by
  intro h; have := lwR4_equation_dom hz; rw [h, zero_mul] at this; exact hne this.symm

/-- The derivative `e^{-W}/(1+W)` on each branch domain. -/
lemma lwR4_hasDerivAt {k : ℤ} {z : ℂ} (hz : z ∈ lwR4_dom k) :
    HasDerivAt (lambertW k) (Complex.exp (-lambertW k z) / (1 + lambertW k z)) z := by
  have hd := ((lwR4_analytic_dom k z hz).differentiableAt).hasDerivAt
  have hg : HasDerivAt (fun u => lambertW k u * Complex.exp (lambertW k u))
      ((lambertW k z + 1) * Complex.exp (lambertW k z) * deriv (lambertW k) z) z :=
    (((hasDerivAt_id (lambertW k z)).fun_mul (Complex.hasDerivAt_exp (lambertW k z))).congr_deriv
      (by simp only [id_eq, one_mul]; ring)).comp z hd
  have hid : HasDerivAt (fun u => lambertW k u * Complex.exp (lambertW k u)) 1 z := by
    apply (hasDerivAt_id z).congr_of_eventuallyEq
    filter_upwards [(lwR4_isOpen_dom k).mem_nhds hz] with u hu
    exact lwR4_equation_dom hu
  have hu := hg.unique hid
  have h1 := lwR4_one_add_ne_zero hz
  convert hd using 1
  rw [Complex.exp_neg]
  field_simp
  linear_combination -hu

/-- The principal branch is real throughout its full real domain. -/
theorem lambertW_principal_real {x : ℝ} (hx : -Real.exp (-1) ≤ x) : (lambertW 0 x).im = 0 := by
  rcases hx.lt_or_eq with h | h
  · exact (lwR4_principal_real_gt h).1
  · rw [← h, lwR4_principal_branchPoint]; simp

/-- The principal real inverse is valid through the branch point. -/
@[dlmf 4.13.E3_1]
theorem lambertW_exp_inverse {x : ℝ} (hx : -1 ≤ x) : lambertW 0 (x * Real.exp x) = x := by
  rcases hx.lt_or_eq with h | h
  · have := lwR4_exp_inverse_gt h; rwa [Complex.ofReal_mul] at this
  · subst h
    have : (((-1 : ℝ) : ℂ) * ((Real.exp (-1) : ℝ) : ℂ)) = ((-Real.exp (-1) : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, lwR4_principal_branchPoint]; simp

/-- Both indicated lower-branch cut values invert `x exp x` below minus one. -/
@[dlmf 4.13.E3_2]
theorem lambertW_lower_exp_inverse {x : ℝ} (hx : x < -1) :
    lambertW (-1) (x * Real.exp x) = x ∧ lambertWLower 1 (x * Real.exp x) = x := by
  sorry

/-- Derivative valid on each open analytic branch, including the removable principal origin. -/
@[dlmf 4.13.E4]
theorem lambertW_hasDerivAt (k : ℤ) {z : ℂ}
    (hz : if k = 0 then z ∈ lambertPrincipalDomain else z ∈ Complex.slitPlane) :
    HasDerivAt (lambertW k)
      (Complex.exp (-lambertW k z) / (1 + lambertW k z)) z := by
  exact lwR4_hasDerivAt ((lwR4_mem_dom_iff k z).mp hz)

/-- The equivalent derivative quotient requires a nonzero argument. -/
@[dlmf 4.13.E4]
theorem lambertW_deriv_quotient (k : ℤ) {z : ℂ} (hne : z ≠ 0)
    (hz : if k = 0 then z ∈ lambertPrincipalDomain else z ∈ Complex.slitPlane) :
    deriv (lambertW k) z = lambertW k z / (z * (1 + lambertW k z)) := by
  rw [lwR4_mem_dom_iff] at hz
  rw [(lwR4_hasDerivAt hz).deriv]
  have h1 := lwR4_one_add_ne_zero hz
  have hW := lwR4_ne_zero_of_ne hz hne
  have heq := lwR4_equation_dom hz
  generalize lambertW k z = w at *
  subst heq
  rw [Complex.exp_neg]
  have := Complex.exp_ne_zero w
  field_simp

open Polynomial in
/-- Vanishing above degree `n` and the leading coefficient `(-1)^n n!`. -/
lemma lwR4_derivPoly_coeff (n : ℕ) :
    (∀ m, n < m → (lambertDerivPolynomial n).coeff m = 0) ∧
    (lambertDerivPolynomial n).coeff n = (-1) ^ n * n.factorial := by
  induction n with
  | zero =>
    simp only [lambertDerivPolynomial, coeff_one]
    exact ⟨fun m hm => by simp; omega, by simp⟩
  | succ n ih =>
    obtain ⟨hz, hl⟩ := ih
    set P := lambertDerivPolynomial n
    have hP : lambertDerivPolynomial (n + 1) = derivative P + X * derivative P + P -
        C ((n + 1 : ℂ)) * (X * P) - C (3 * (n + 1 : ℂ)) * P := by
      rw [lambertDerivPolynomial]; simp only [map_mul, map_ofNat]; ring
    have hc : ∀ m, (lambertDerivPolynomial (n + 1)).coeff (m + 1) =
        P.coeff (m + 2) * (m + 2) + P.coeff (m + 1) * (m + 1) + P.coeff (m + 1) -
          (n + 1) * P.coeff m - 3 * (n + 1) * P.coeff (m + 1) := by
      intro m
      rw [hP]
      simp only [coeff_add, coeff_sub, coeff_derivative, coeff_X_mul, coeff_C_mul]
      push_cast; ring
    refine ⟨fun m hm => ?_, ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [hc, hz (m + 2) (by omega), hz (m + 1) (by omega), hz m (by omega)]; ring
    · rw [hc, hz (n + 2) (by omega), hz (n + 1) (by omega), hl]
      push_cast [Nat.factorial_succ]; ring

/-- The nth derivative polynomial has exactly degree n. -/
@[dlmf 4.13.E4_2]
theorem lambertDerivPolynomial_natDegree (n : ℕ) : (lambertDerivPolynomial n).natDegree = n := by
  obtain ⟨hz, hl⟩ := lwR4_derivPoly_coeff n
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => hz m (by exact_mod_cast hm)
  · rw [hl]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast n.factorial_ne_zero)

/-- The closed form of the `(m+1)`st derivative as a function of `w = W(z)`. -/
def lwR4_F (m : ℕ) (w : ℂ) : ℂ :=
  Complex.exp (-(m + 1 : ℂ) * w) * (lambertDerivPolynomial m).eval w / (1 + w) ^ (2 * m + 1)

/-- The derivative of the closed form `lwR4_F m`. -/
lemma lwR4_F_hasDerivAt (m : ℕ) {w : ℂ} (hw : 1 + w ≠ 0) :
    HasDerivAt (lwR4_F m)
      (((Complex.exp (-(m + 1 : ℂ) * w) * (-(m + 1 : ℂ)) * (lambertDerivPolynomial m).eval w +
        Complex.exp (-(m + 1 : ℂ) * w) * (lambertDerivPolynomial m).derivative.eval w) *
          (1 + w) ^ (2 * m + 1) -
        Complex.exp (-(m + 1 : ℂ) * w) * (lambertDerivPolynomial m).eval w *
          ((2 * m + 1 : ℕ) * (1 + w) ^ (2 * m + 1 - 1) * 1)) /
        ((1 + w) ^ (2 * m + 1)) ^ 2) w := by
  have he : HasDerivAt (fun x : ℂ => Complex.exp (-(m + 1 : ℂ) * x))
      (Complex.exp (-(m + 1 : ℂ) * w) * (-(m + 1 : ℂ))) w := by
    simpa using ((hasDerivAt_id w).const_mul (-(m + 1 : ℂ))).cexp
  have hp := (lambertDerivPolynomial m).hasDerivAt w
  have hq : HasDerivAt (fun x : ℂ => (1 + x) ^ (2 * m + 1))
      ((2 * m + 1 : ℕ) * (1 + w) ^ (2 * m + 1 - 1) * 1) w :=
    ((hasDerivAt_id w).const_add 1).pow (2 * m + 1)
  exact (he.mul hp).div hq (pow_ne_zero _ hw)

/-- The `(m+1)`st derivative of a branch on its domain, by induction. -/
lemma lwR4_iteratedDeriv_succ (k : ℤ) (m : ℕ) :
    ∀ z ∈ lwR4_dom k, iteratedDeriv (m + 1) (lambertW k) z = lwR4_F m (lambertW k z) := by
  induction m with
  | zero =>
    intro z hz
    rw [iteratedDeriv_one, (lwR4_hasDerivAt hz).deriv, lwR4_F]
    simp [lambertDerivPolynomial]
  | succ m ih =>
    intro z hz
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv (m + 1) (lambertW k) =ᶠ[𝓝 z] fun u => lwR4_F m (lambertW k u) := by
      filter_upwards [(lwR4_isOpen_dom k).mem_nhds hz] with u hu
      exact ih u hu
    rw [hev.deriv_eq]
    have h1 := lwR4_one_add_ne_zero hz
    have hc : HasDerivAt (fun u => lwR4_F m (lambertW k u)) _ z :=
      (lwR4_F_hasDerivAt m h1).comp z (lwR4_hasDerivAt hz)
    rw [hc.deriv]
    clear hc hev ih
    generalize lambertW k z = w at *
    rw [lwR4_F, lambertDerivPolynomial]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat]
    have e1 : Complex.exp (-(↑(m + 1) + 1 : ℂ) * w) =
        Complex.exp (-(m + 1 : ℂ) * w) * Complex.exp (-w) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    rw [e1]
    have hpow : (1 + w) ^ (2 * (m + 1) + 1) = (1 + w) ^ (2 * m + 1) * (1 + w) ^ 2 := by
      ring
    have hpow2 : (1 + w) ^ (2 * m + 1 - 1) * (1 + w) = (1 + w) ^ (2 * m + 1) := by
      rw [← pow_succ]; congr 1
    rw [hpow, ← hpow2]
    field_simp
    push_cast
    ring

/-- Every positive derivative order on every analytic branch. -/
@[dlmf 4.13.E4_1]
theorem lambertW_iteratedDeriv (k n : ℤ) (hn : 1 ≤ n) {z : ℂ}
    (hz : if k = 0 then z ∈ lambertPrincipalDomain else z ∈ Complex.slitPlane) :
    iteratedDeriv n.toNat (lambertW k) z =
      Complex.exp (-n * lambertW k z) *
        (lambertDerivPolynomial (n.toNat - 1)).eval (lambertW k z) /
      (1 + lambertW k z) ^ (2 * n.toNat - 1) := by
  rw [lwR4_mem_dom_iff] at hz
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  have hm : ((m : ℤ) + 1).toNat = m + 1 := by omega
  rw [hm, lwR4_iteratedDeriv_succ k m z hz, lwR4_F]
  simp only [Nat.add_sub_cancel, show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
  push_cast; ring_nf

end DLMF.Elementary
end
end
