/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.SpecialValues

/-!
# Uniqueness for the Jacobi system and an identity principle (helpers, round 3)

* Asymptotic helpers: `e(0) = 0` and `e' = O(zⁿ)` give `e = O(zⁿ⁺¹)`; an analytic function that is
  `O(zⁿ)` for every `n` vanishes near `0`.
* `p3j_ode_unique`: two solutions of `s' = cd`, `c' = -sd`, `d' = -κsc` near `0` with the same
  initial values agree near `0` (bootstrapping the error to infinite order).
* `p3j_eq_of_eventuallyEq`: two functions that are analytic or have a pole with junk value `0`
  at every point (`p3j_Dich`), and that agree near `0`, are equal (identity theorem for
  meromorphic functions on `ℂ`). The Glaisher functions `pq(·, k)` satisfy `p3j_Dich`
  (from `jacobiPQk_zeros_poles`), and it is preserved by `f ↦ c f(w/a)`.
-/

@[expose] public section

open Complex Asymptotics Filter
open scoped Topology

noncomputable section

namespace DLMF.JacobiElliptic

/-- If `e(0) = 0` and `e' = O(zⁿ)` near `0`, then `e = O(zⁿ⁺¹)` (mean value inequality). -/
theorem p3j_isBigO_of_deriv {e e' : ℂ → ℂ} {n : ℕ} (he : ∀ᶠ z in 𝓝 0, HasDerivAt e (e' z) z)
    (h0 : e 0 = 0) (h : e' =O[𝓝 0] fun z => z ^ n) : e =O[𝓝 0] fun z => z ^ (n + 1) := by
  obtain ⟨C, hC0, hC⟩ := h.exists_nonneg
  rw [IsBigOWith] at hC
  obtain ⟨r, hr0, hr⟩ := Metric.eventually_nhds_iff_ball.mp (he.and hC)
  refine IsBigO.of_bound C ?_
  filter_upwards [Metric.ball_mem_nhds 0 hr0] with z hz
  have hsub : Metric.closedBall (0 : ℂ) ‖z‖ ⊆ Metric.ball 0 r := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [Metric.mem_ball, dist_zero_right]
    rw [Metric.mem_ball, dist_zero_right] at hz
    linarith
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := e) (f' := e')
    (C := C * ‖z‖ ^ n) (s := Metric.closedBall 0 ‖z‖) (x := 0) (y := z)
    (fun w hw => ((hr w (hsub hw)).1).hasDerivWithinAt)
    (fun w hw => by
      have h1 := (hr w (hsub hw)).2
      rw [norm_pow] at h1
      have hw' : ‖w‖ ≤ ‖z‖ := by simpa using hw
      exact h1.trans (by gcongr))
    (convex_closedBall 0 _) (by simp) (by simp)
  rw [h0, sub_zero, sub_zero] at key
  rw [norm_pow, pow_succ]
  linarith [key]

/-- `zᵃ = O(zᵇ)` at `0` for `b ≤ a`. -/
theorem p3j_pow_isBigO_pow {a b : ℕ} (h : b ≤ a) :
    (fun z : ℂ => z ^ a) =O[𝓝 0] fun z => z ^ b := by
  have : (fun z : ℂ => z ^ a) = fun z => z ^ b * z ^ (a - b) := by
    funext z; rw [← pow_add, Nat.add_sub_cancel' h]
  rw [this]
  have h1 : (fun z : ℂ => z ^ (a - b)) =O[𝓝 0] fun _ => (1 : ℂ) :=
    ((continuous_pow (a - b)).tendsto (0 : ℂ)).isBigO_one ℂ
  simpa using (isBigO_refl (fun z : ℂ => z ^ b) (𝓝 0)).mul h1

/-- A function continuous at `0` is `O(1)` there. -/
theorem p3j_cont_isBigO_one {f : ℂ → ℂ} (hf : ContinuousAt f 0) :
    f =O[𝓝 0] fun _ => (1 : ℂ) := hf.tendsto.isBigO_one ℂ

/-- `O(1) · O(zʲ) = O(zʲ)`. -/
theorem p3j_mul_one {f g : ℂ → ℂ} {j : ℕ} (hf : f =O[𝓝 0] fun z => z ^ j)
    (hg : g =O[𝓝 0] fun _ => (1 : ℂ)) : (fun z => g z * f z) =O[𝓝 0] fun z => z ^ j := by
  simpa using hg.mul hf

/-- An analytic function that is `O(zⁿ)` at `0` for every `n` vanishes near `0`. -/
lemma p3j_eventually_zero {e : ℂ → ℂ} (he : AnalyticAt ℂ e 0)
    (h : ∀ n : ℕ, e =O[𝓝 0] fun z => z ^ n) : ∀ᶠ z in 𝓝 0, e z = 0 := by
  rw [← analyticOrderAt_eq_top]
  by_contra htop
  set N := analyticOrderNatAt e 0
  have hΘ := he.isTheta_pow_sub htop
  simp only [sub_zero] at hΘ
  have h1 : (fun z : ℂ => z ^ N) =O[𝓝 0] fun z => z ^ (N + 1) := hΘ.2.trans (h (N + 1))
  obtain ⟨C, hC⟩ := h1.bound
  obtain ⟨ε, hε, hεC⟩ := Metric.eventually_nhds_iff.mp hC
  set t : ℝ := min (ε / 2) (1 / (2 * (|C| + 1))) with ht
  have ht0 : 0 < t := lt_min (by linarith) (by positivity)
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hb := hεC (y := (t : ℂ)) (by simpa [abs_of_pos ht0] using htε)
  rw [pow_succ, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht0] at hb
  have hpow : 0 < t ^ N := pow_pos ht0 N
  have h2 : 1 ≤ C * t := by
    have : t ^ N * 1 ≤ t ^ N * (C * t) := by nlinarith
    exact le_of_mul_le_mul_left this hpow
  have h3 : C * t ≤ |C| * t := mul_le_mul_of_nonneg_right (le_abs_self C) ht0.le
  have h4 : |C| * t < 1 := by
    have : t ≤ 1 / (2 * (|C| + 1)) := min_le_right _ _
    have hC0 := abs_nonneg C
    calc |C| * t ≤ |C| * (1 / (2 * (|C| + 1))) := mul_le_mul_of_nonneg_left this hC0
      _ < 1 := by rw [mul_one_div, div_lt_one (by positivity)]; linarith
  linarith

/-- Uniqueness for the Jacobi system `s' = cd, c' = -sd, d' = -κsc` near `0`. -/
theorem p3j_ode_unique {s c d s₂ c₂ d₂ : ℂ → ℂ} {κ : ℂ}
    (hs : ∀ᶠ z in 𝓝 0, HasDerivAt s (c z * d z) z)
    (hc : ∀ᶠ z in 𝓝 0, HasDerivAt c (-(s z * d z)) z)
    (hd : ∀ᶠ z in 𝓝 0, HasDerivAt d (-(κ * s z * c z)) z)
    (hs₂ : ∀ᶠ z in 𝓝 0, HasDerivAt s₂ (c₂ z * d₂ z) z)
    (hc₂ : ∀ᶠ z in 𝓝 0, HasDerivAt c₂ (-(s₂ z * d₂ z)) z)
    (hd₂ : ∀ᶠ z in 𝓝 0, HasDerivAt d₂ (-(κ * s₂ z * c₂ z)) z)
    (h0s : s 0 = s₂ 0) (h0c : c 0 = c₂ 0) (h0d : d 0 = d₂ 0) :
    s =ᶠ[𝓝 0] s₂ ∧ c =ᶠ[𝓝 0] c₂ ∧ d =ᶠ[𝓝 0] d₂ := by
  set es := fun z => s z - s₂ z with hes_def
  set ec := fun z => c z - c₂ z with hec_def
  set ed := fun z => d z - d₂ z with hed_def
  have hes : ∀ᶠ z in 𝓝 0, HasDerivAt es (c z * ed z + d₂ z * ec z) z := by
    filter_upwards [hs, hs₂] with z h1 h2
    exact (h1.sub h2).congr_deriv (by simp only [hec_def, hed_def]; ring)
  have hec : ∀ᶠ z in 𝓝 0, HasDerivAt ec ((-1) * (s z * ed z) + (-1) * (d₂ z * es z)) z := by
    filter_upwards [hc, hc₂] with z h1 h2
    exact (h1.sub h2).congr_deriv (by simp only [hes_def, hed_def]; ring)
  have hed : ∀ᶠ z in 𝓝 0, HasDerivAt ed ((-κ) * (s z * ec z) + (-κ) * (c₂ z * es z)) z := by
    filter_upwards [hd, hd₂] with z h1 h2
    exact (h1.sub h2).congr_deriv (by simp only [hes_def, hec_def]; ring)
  have z0s : es 0 = 0 := by simp [hes_def, h0s]
  have z0c : ec 0 = 0 := by simp [hec_def, h0c]
  have z0d : ed 0 = 0 := by simp [hed_def, h0d]
  have b := fun {f : ℂ → ℂ} {f' : ℂ → ℂ} (h : ∀ᶠ z in 𝓝 0, HasDerivAt f (f' z) z) =>
    p3j_cont_isBigO_one h.self_of_nhds.continuousAt
  have bk : (fun _ : ℂ => (-1 : ℂ)) =O[𝓝 0] fun _ => (1 : ℂ) := isBigO_const_const _ one_ne_zero _
  have bκ : (fun _ : ℂ => (-κ : ℂ)) =O[𝓝 0] fun _ => (1 : ℂ) := isBigO_const_const _ one_ne_zero _
  have P : ∀ j : ℕ, es =O[𝓝 0] (fun z => z ^ j) ∧ ec =O[𝓝 0] (fun z => z ^ j) ∧
      ed =O[𝓝 0] (fun z => z ^ j) := by
    intro j
    induction j with
    | zero => simp only [pow_zero]; exact ⟨b hes, b hec, b hed⟩
    | succ j ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      refine ⟨p3j_isBigO_of_deriv hes z0s ?_, p3j_isBigO_of_deriv hec z0c ?_,
        p3j_isBigO_of_deriv hed z0d ?_⟩
      · exact (p3j_mul_one h3 (b hc)).add (p3j_mul_one h2 (b hd₂))
      · exact (p3j_mul_one (p3j_mul_one h3 (b hs)) bk).add
          (p3j_mul_one (p3j_mul_one h1 (b hd₂)) bk)
      · exact (p3j_mul_one (p3j_mul_one h2 (b hs)) bκ).add
          (p3j_mul_one (p3j_mul_one h1 (b hc₂)) bκ)
  have an : ∀ {f : ℂ → ℂ} {f' : ℂ → ℂ}, (∀ᶠ z in 𝓝 0, HasDerivAt f (f' z) z) →
      AnalyticAt ℂ f 0 := by
    intro f f' h
    obtain ⟨U, hU, hUo, h0U⟩ := mem_nhds_iff.mp h
    exact DifferentiableOn.analyticAt (fun z hz => (hU hz).differentiableAt.differentiableWithinAt)
      (hUo.mem_nhds h0U)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [p3j_eventually_zero ((an hs).sub (an hs₂)) fun n => (P n).1] with z hz
    exact sub_eq_zero.mp hz
  · filter_upwards [p3j_eventually_zero ((an hc).sub (an hc₂)) fun n => (P n).2.1] with z hz
    exact sub_eq_zero.mp hz
  · filter_upwards [p3j_eventually_zero ((an hd).sub (an hd₂)) fun n => (P n).2.2] with z hz
    exact sub_eq_zero.mp hz

/-- The pole dichotomy: analytic at `z`, or a pole at `z` with Lean's junk value `0`. -/
def p3j_Dich (f : ℂ → ℂ) : Prop :=
  ∀ z, AnalyticAt ℂ f z ∨ (meromorphicOrderAt f z < 0 ∧ f z = 0)

/-- A function with the pole dichotomy is meromorphic. -/
theorem p3j_Dich.meromorphicAt {f : ℂ → ℂ} (hf : p3j_Dich f) (z : ℂ) : MeromorphicAt f z := by
  rcases hf z with h | h
  · exact h.meromorphicAt
  · by_contra hm
    rw [meromorphicOrderAt_of_not_meromorphicAt hm] at h
    exact lt_irrefl _ h.1

/-- Identity theorem for functions with the pole dichotomy: agreement near `0` gives agreement
everywhere, including the junk values at the poles. -/
theorem p3j_eq_of_eventuallyEq {f g : ℂ → ℂ} (hf : p3j_Dich f) (hg : p3j_Dich g)
    (h0 : f =ᶠ[𝓝 0] g) : f = g := by
  have hm : MeromorphicOn (f - g) Set.univ := fun z _ =>
    (hf.meromorphicAt z).sub (hg.meromorphicAt z)
  have htop0 : meromorphicOrderAt (f - g) 0 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [nhdsWithin_le_nhds h0] with z hz
    simp [hz]
  have hev : ∀ y, f =ᶠ[𝓝[≠] y] g := by
    intro y
    have := hm.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ 0) (Set.mem_univ y) htop0
    rw [meromorphicOrderAt_eq_top_iff] at this
    filter_upwards [this] with z hz
    exact sub_eq_zero.mp hz
  funext y
  have hord := meromorphicOrderAt_congr (hev y)
  rcases hf y with h1 | h1 <;> rcases hg y with h2 | h2
  · exact tendsto_nhds_unique ((h1.continuousAt.tendsto).mono_left nhdsWithin_le_nhds)
      (((h2.continuousAt.tendsto).mono_left nhdsWithin_le_nhds).congr' (hev y).symm)
  · exact absurd (hord ▸ h1.meromorphicOrderAt_nonneg) (not_le.mpr h2.1)
  · exact absurd (hord ▸ h2.meromorphicOrderAt_nonneg) (not_le.mpr (hord ▸ h1.1))
  · rw [h1.2, h2.2]

/-- The pole dichotomy is preserved by `f ↦ c f(w/a)`. -/
theorem p3j_Dich.comp {f : ℂ → ℂ} (hf : p3j_Dich f) {a c : ℂ} (ha : a ≠ 0) (hc : c ≠ 0) :
    p3j_Dich fun w => c * f (w / a) := by
  intro z
  have hg : AnalyticAt ℂ (fun w : ℂ => w / a) z := by fun_prop
  rcases hf (z / a) with h | h
  · have : AnalyticAt ℂ (f ∘ fun w : ℂ => w / a) z := h.comp_of_eq hg rfl
    exact Or.inl (analyticAt_const.mul this)
  · right
    refine ⟨?_, by show c * f (z / a) = 0; rw [h.2, mul_zero]⟩
    have hd : deriv (fun w : ℂ => w / a) z ≠ 0 := by
      rw [deriv_div_const, deriv_id'']; exact one_div_ne_zero ha
    have e1 := meromorphicOrderAt_comp_of_deriv_ne_zero (f := f) hg hd
    have e2 := meromorphicOrderAt_const_smul_eq_meromorphicOrderAt (x := z)
      (f := f ∘ fun w : ℂ => w / a) hc
    have : (fun w => c * f (w / a)) = c • (f ∘ fun w : ℂ => w / a) := by
      funext w; simp
    rw [this, e2, e1]
    exact h.1

/-- The Glaisher functions have the pole dichotomy. -/
theorem p3j_dich_pq {k : ℂ} (hk : k ∈ jacobiModulusDomain) {p q : JacobiLetter} (hpq : p ≠ q) :
    p3j_Dich fun w => jacobiPQk p q w k := by
  intro z
  have hτ := jacobiTauk_im_pos hk
  have heq : (fun w => jacobiPQk p q w k) = fun w =>
      jacobiLetterTheta p (jacobiZetak w k) (jacobiTauk k) /
        jacobiLetterTheta q (jacobiZetak w k) (jacobiTauk k) := by
    funext w; simp [jacobiPQk, jacobiGlaisher, hpq]
  by_cases hq : jacobiLetterTheta q (jacobiZetak z k) (jacobiTauk k) = 0
  · right
    have hmem : z ∈ jacobiCongruentk (jacobiLetterPointk q k) k := by
      rw [p3j_cong_iff hk]
      rw [p3j_letter_eq] at hq
      exact (mul_eq_zero.mp hq).resolve_left (p3j_amp_ne hτ _ _)
    refine ⟨?_, ?_⟩
    · rw [((jacobiPQk_zeros_poles hk hpq z).2.1).mpr hmem]; decide
    · show jacobiPQk p q z k = 0
      rw [show jacobiPQk p q z k = _ from congrFun heq z, hq, div_zero]
  · left
    rw [heq]
    exact ((p3j_F_differentiable hk p).analyticAt z).div
      ((p3j_F_differentiable hk q).analyticAt z) hq

/-- Regularity near `0`, after the substitution `w ↦ w/a`. -/
theorem p3j_reg_near {k : ℂ} (hk : k ∈ jacobiModulusDomain) {q : JacobiLetter} (hq : q ≠ .s)
    (a : ℂ) : ∀ᶠ w in 𝓝 0, jacobiLetterTheta q (jacobiZetak (w / a) k) (jacobiTauk k) ≠ 0 := by
  have h := p22R1_eventually_ne hk (p22R1_reg0 hk hq)
  have ht : Tendsto (fun w : ℂ => w / a) (𝓝 0) (𝓝 0) := by
    have := ((continuous_id.div_const a).tendsto (0 : ℂ)); simpa using this
  exact ht.eventually h

end DLMF.JacobiElliptic
