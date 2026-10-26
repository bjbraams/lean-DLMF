/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Growth bounds for solutions of `y'' = P(x) y`

* `ODE.p2s_energy_complex_le`: for complex `y'' = P y` on `[0, L]` with `‖P‖ ≤ M + k²`,
  `k ≥ 1`, `M ≥ 0`, the energy `‖y'‖² + k² ‖y‖²` grows at most like `e^{(M + 2k) x}`
  (Grönwall). With `k² = |λ|` this gives the bound `e^{O(|λ|^{1/2})}` for solutions of
  `y'' = (Q - λ) y`.
* `ODE.p2s_real_lower_I`, `ODE.p2s_real_lower_II`: for real `y'' = p y` with `p ≥ s² > 0` on
  `[0, L]`, the solution with data `(1, 0)` satisfies `y(L) ≥ e^{sL} / 2`, and the solution with
  data `(0, 1)` satisfies `y'(L) ≥ 1`.
-/

@[expose] public section

open Set Filter Topology Real

namespace ODE

/-- **Complex energy estimate.** Let `y'' = P y` on `ℝ` (complex values) with `‖P x‖ ≤ M + k²`
on `[0, L]`, `0 ≤ M`, `1 ≤ k`. Then `‖y'‖² + k² ‖y‖² ≤ (‖y'(0)‖² + k² ‖y(0)‖²) e^{(M + 2k) x}`
on `[0, L]`. -/
theorem p2s_energy_complex_le {P y y' : ℝ → ℂ} {M L k : ℝ} (hM : 0 ≤ M) (hk : 1 ≤ k)
    (hP : ∀ x ∈ Icc 0 L, ‖P x‖ ≤ M + k ^ 2) (hy : ∀ x, HasDerivAt y (y' x) x)
    (hy' : ∀ x, HasDerivAt y' (P x * y x) x) {x : ℝ} (hx : x ∈ Icc 0 L) :
    ‖y' x‖ ^ 2 + k ^ 2 * ‖y x‖ ^ 2 ≤
      (‖y' 0‖ ^ 2 + k ^ 2 * ‖y 0‖ ^ 2) * exp ((M + 2 * k) * x) := by
  set E : ℝ → ℝ := fun x => ‖y' x‖ ^ 2 + k ^ 2 * ‖y x‖ ^ 2 with hE
  set E' : ℝ → ℝ := fun x => 2 * inner ℝ (y' x) (P x * y x) + k ^ 2 * (2 * inner ℝ (y x) (y' x))
  have hdE : ∀ x, HasDerivAt E (E' x) x := fun x =>
    ((hy' x).norm_sq).add (((hy x).norm_sq).const_mul (k ^ 2))
  have hbound : ∀ x ∈ Ico 0 L, E' x ≤ (M + 2 * k) * E x + 0 := by
    intro x hx
    set a := ‖y x‖
    set b := ‖y' x‖
    have ha : 0 ≤ a := norm_nonneg _
    have hb : 0 ≤ b := norm_nonneg _
    have hPx := hP x (Ico_subset_Icc_self hx)
    have i1 : inner ℝ (y' x) (P x * y x) ≤ b * ((M + k ^ 2) * a) := by
      refine (real_inner_le_norm _ _).trans ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPx ha) hb
    have i2 : inner ℝ (y x) (y' x) ≤ a * b := real_inner_le_norm _ _
    have i3 : 2 * k * a * b ≤ b ^ 2 + k ^ 2 * a ^ 2 := by nlinarith [sq_nonneg (b - k * a)]
    have i4 : M * a * b ≤ M * k * a * b := by
      have : 0 ≤ M * a * b := by positivity
      nlinarith
    show 2 * inner ℝ (y' x) (P x * y x) + k ^ 2 * (2 * inner ℝ (y x) (y' x)) ≤
      (M + 2 * k) * (b ^ 2 + k ^ 2 * a ^ 2) + 0
    have hk2 : 0 ≤ k ^ 2 := sq_nonneg k
    have hMk : 0 ≤ M + 2 * k := by linarith
    nlinarith [mul_le_mul_of_nonneg_left i2 hk2, mul_le_mul_of_nonneg_left i3 hMk]
  have hG := le_gronwallBound_of_liminf_deriv_right_le (f := E) (f' := E') (δ := E 0)
    (K := M + 2 * k) (ε := 0) (a := 0) (b := L)
    (fun x _ => (hdE x).continuousAt.continuousWithinAt)
    (fun x _ r hr => (hdE x).hasDerivWithinAt.liminf_right_slope_le hr) le_rfl hbound x hx
  rw [gronwallBound_ε0, sub_zero] at hG
  exact hG

/-- Monotonicity on `[0, L]` from a nonnegative derivative on `(0, L)`. -/
theorem p2s_le_of_deriv_nonneg {F F' : ℝ → ℝ} {L : ℝ} (hF : ∀ x, HasDerivAt F (F' x) x)
    (h : ∀ x ∈ Ioo 0 L, 0 ≤ F' x) {x : ℝ} (hx : x ∈ Icc 0 L) : F 0 ≤ F x := by
  have hmono : MonotoneOn F (Icc 0 L) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 L)
      (fun x _ => (hF x).continuousAt.continuousWithinAt) (fun x _ => (hF x).hasDerivWithinAt)
      fun x hx => h x (by rwa [interior_Icc] at hx)
  exact hmono ⟨le_rfl, hx.1.trans hx.2⟩ hx hx.1

/-- A continuous function with `f(0) = 1` and `f² ≥ 1` on `[0, L]` satisfies `f ≥ 1` there. -/
theorem p2s_one_le_of_sq {f : ℝ → ℝ} {L : ℝ} (hf : Continuous f) (h0 : f 0 = 1)
    (h : ∀ x ∈ Icc 0 L, 1 ≤ f x ^ 2) {x : ℝ} (hx : x ∈ Icc 0 L) : 1 ≤ f x := by
  by_contra hlt
  push Not at hlt
  have hneg : f x ≤ -1 := by nlinarith [h x hx]
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hx.1 hf.continuousOn
    (show (0 : ℝ) ∈ Icc (f x) (f 0) from ⟨by linarith, by rw [h0]; norm_num⟩)
  have := h c ⟨hc.1, hc.2.trans hx.2⟩
  rw [hc0] at this
  norm_num at this

/-- `y y'` is nondecreasing on `[0, L]` when `y'' = p y` with `p ≥ 0` there; with `y y' = 0` at
`0` it is nonnegative. -/
theorem p2s_mul_deriv_nonneg {p y y' : ℝ → ℝ} {L : ℝ} (hp : ∀ x ∈ Icc 0 L, 0 ≤ p x)
    (hy : ∀ x, HasDerivAt y (y' x) x) (hy' : ∀ x, HasDerivAt y' (p x * y x) x)
    (h0 : y 0 * y' 0 = 0) {x : ℝ} (hx : x ∈ Icc 0 L) : 0 ≤ y x * y' x := by
  have := p2s_le_of_deriv_nonneg (F := fun x => y x * y' x) (L := L)
    (fun x => (hy x).mul (hy' x)) (fun x hx' => by
      have := hp x (Ioo_subset_Icc_self hx')
      nlinarith [mul_self_nonneg (y' x), mul_nonneg this (mul_self_nonneg (y x))]) hx
  simpa [h0] using this

/-- **Lower bound, data `(1, 0)`.** If `y'' = p y` with `p ≥ s²` on `[0, L]`, `y(0) = 1`,
`y'(0) = 0`, then `y(L) ≥ e^{sL} / 2`. -/
theorem p2s_real_lower_I {p y y' : ℝ → ℝ} {L s : ℝ} (hL : 0 ≤ L)
    (hp : ∀ x ∈ Icc 0 L, s ^ 2 ≤ p x) (hy : ∀ x, HasDerivAt y (y' x) x)
    (hy' : ∀ x, HasDerivAt y' (p x * y x) x) (h0 : y 0 = 1) (h1 : y' 0 = 0) :
    exp (s * L) / 2 ≤ y L := by
  have hp0 : ∀ x ∈ Icc 0 L, 0 ≤ p x := fun x hx => (sq_nonneg s).trans (hp x hx)
  have hu := fun x (hx : x ∈ Icc 0 L) => p2s_mul_deriv_nonneg hp0 hy hy' (by simp [h1]) hx
  -- `y² ≥ 1`
  have hsq : ∀ x ∈ Icc 0 L, 1 ≤ y x ^ 2 := by
    intro x hx
    have := p2s_le_of_deriv_nonneg (F := fun x => y x ^ 2) (F' := fun x => 2 * (y x * y' x))
      (L := L) (fun x => ((hy x).pow 2).congr_deriv (by simp; ring))
      (fun x hx' => by linarith [hu x (Ioo_subset_Icc_self hx')]) hx
    simpa [h0] using this
  have hyc : Continuous y := continuous_iff_continuousAt.mpr fun x => (hy x).continuousAt
  have hy1 : ∀ x ∈ Icc 0 L, 1 ≤ y x := fun x hx => p2s_one_le_of_sq hyc h0 hsq hx
  have hy'0 : ∀ x ∈ Icc 0 L, 0 ≤ y' x := fun x hx => by
    have := hu x hx
    have := hy1 x hx
    by_contra h
    push Not at h
    nlinarith
  -- `G = y' + s y ≥ s e^{sx}`
  have hG : ∀ x ∈ Icc 0 L, s * exp (s * x) ≤ y' x + s * y x := by
    intro x hx
    have hd : ∀ x, HasDerivAt (fun x => (y' x + s * y x) * exp (-(s * x)))
        ((p x * y x + s * y' x - s * (y' x + s * y x)) * exp (-(s * x))) x := by
      intro x
      have he := ((hasDerivAt_id x).const_mul s).neg.exp
      refine (((hy' x).add ((hy x).const_mul s)).mul he).congr_deriv ?_
      simp only [id, Pi.neg_apply, Pi.add_apply]; ring
    have := p2s_le_of_deriv_nonneg hd (fun x hx' => by
      have hpx := hp x (Ioo_subset_Icc_self hx')
      have hyx := hy1 x (Ioo_subset_Icc_self hx')
      have : 0 ≤ p x * y x + s * y' x - s * (y' x + s * y x) := by nlinarith
      positivity) hx
    simp only [h0, h1, mul_zero, neg_zero, exp_zero, mul_one, zero_add] at this
    have hpos := exp_pos (s * x)
    have e : exp (-(s * x)) = (exp (s * x))⁻¹ := exp_neg _
    rw [e] at this
    rw [le_mul_inv_iff₀ hpos] at this
    linarith
  -- `F = y e^{sx} - e^{2sx}/2` is nondecreasing
  have hd : ∀ x, HasDerivAt (fun x => y x * exp (s * x) - exp (2 * s * x) / 2)
      ((y' x + s * y x - s * exp (s * x)) * exp (s * x)) x := by
    intro x
    have he := ((hasDerivAt_id x).const_mul s).exp
    have he2 := (((hasDerivAt_id x).const_mul (2 * s)).exp).div_const 2
    refine (((hy x).mul he).sub he2).congr_deriv ?_
    simp only [id]
    rw [show 2 * s * x = s * x + s * x by ring, exp_add]
    ring
  have key := p2s_le_of_deriv_nonneg hd (fun x hx' => by
    have := hG x (Ioo_subset_Icc_self hx')
    have : 0 ≤ y' x + s * y x - s * exp (s * x) := by linarith
    positivity) ⟨hL, le_rfl⟩
  simp only [h0, mul_zero, exp_zero, mul_one] at key
  have hpos := exp_pos (s * L)
  rw [show 2 * s * L = s * L + s * L by ring, exp_add] at key
  have : exp (s * L) * (exp (s * L) / 2) ≤ exp (s * L) * y L := by nlinarith
  exact le_of_mul_le_mul_left this hpos

/-- **Lower bound, data `(0, 1)`.** If `y'' = p y` with `p ≥ s²` on `[0, L]`, `y(0) = 0`,
`y'(0) = 1`, then `y'(L) ≥ 1`. -/
theorem p2s_real_lower_II {p y y' : ℝ → ℝ} {L s : ℝ} (hL : 0 ≤ L)
    (hp : ∀ x ∈ Icc 0 L, s ^ 2 ≤ p x) (hy : ∀ x, HasDerivAt y (y' x) x)
    (hy' : ∀ x, HasDerivAt y' (p x * y x) x) (h0 : y 0 = 0) (h1 : y' 0 = 1) :
    1 ≤ y' L := by
  have hp0 : ∀ x ∈ Icc 0 L, 0 ≤ p x := fun x hx => (sq_nonneg s).trans (hp x hx)
  have hu := fun x (hx : x ∈ Icc 0 L) => p2s_mul_deriv_nonneg hp0 hy hy' (by simp [h0]) hx
  have hsq : ∀ x ∈ Icc 0 L, 1 ≤ y' x ^ 2 := by
    intro x hx
    have := p2s_le_of_deriv_nonneg (F := fun x => y' x ^ 2 - s ^ 2 * y x ^ 2)
      (F' := fun x => 2 * (p x - s ^ 2) * (y x * y' x)) (L := L)
      (fun x => (((hy' x).pow 2).sub (((hy x).pow 2).const_mul (s ^ 2))).congr_deriv
        (by simp; ring))
      (fun x hx' => by
        have := hp x (Ioo_subset_Icc_self hx')
        have := hu x (Ioo_subset_Icc_self hx')
        have : 0 ≤ p x - s ^ 2 := by linarith
        positivity) hx
    simp only [h0, h1] at this
    nlinarith [sq_nonneg (s * y x)]
  have hyc : Continuous y' := continuous_iff_continuousAt.mpr fun x => (hy' x).continuousAt
  exact p2s_one_le_of_sq hyc h1 hsq ⟨hL, le_rfl⟩

end ODE
