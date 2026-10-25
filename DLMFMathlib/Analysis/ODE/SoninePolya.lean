/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The Sonine–Pólya theorem

For a solution of `(k y')' + φ y = 0` with `k > 0` and `φ > 0` on `[a, b]`, Sonine's function
`S = y² + (k y')² / (k φ)` has derivative `-(k y')² (k φ)' / (k φ)²`. Hence `S` decreases where
`k φ` increases and increases where `k φ` decreases. Since `S = y²` wherever `y' = 0`, the
successive relative maxima of `|y|` decrease (resp. increase) when `(k φ)' > 0`
(resp. `(k φ)' < 0`). This is Beals–Wong, Propositions 3.5.1–3.5.3, and Szegő, Theorem 7.31.1.

A solution is given by `y`, `y'` with `HasDerivAt y (y' x) x` and
`HasDerivAt (fun t => k t * y' t) (-(φ x * y x)) x`; the derivative of `k φ` is a function
`d`.

## Main results

* `ODE.antitoneOn_sonineFunction`, `ODE.monotoneOn_sonineFunction`: monotonicity of `S`.
* `ODE.abs_le_of_deriv_eq_zero_left`: if `(k φ)' ≥ 0` and `y'(a) = 0`, then `|y| ≤ |y(a)|`
  on `[a, b]`; `ODE.abs_le_of_deriv_eq_zero_right` is the mirror statement.
* `ODE.abs_lt_of_deriv_eq_zero`, `ODE.abs_lt_of_deriv_eq_zero'`: strict comparison of two
  relative extrema when `(k φ)'` has a strict sign.
-/

@[expose] public section

open Set Filter Topology

namespace ODE

variable {k φ y y' d : ℝ → ℝ} {a b : ℝ}

/-- Sonine's function `y² + (k y')² / (k φ)` for the equation `(k y')' + φ y = 0`. -/
noncomputable def sonineFunction (k φ y y' : ℝ → ℝ) (x : ℝ) : ℝ :=
  y x ^ 2 + (k x * y' x) ^ 2 / (k x * φ x)

theorem hasDerivAt_sonineFunction {x dx : ℝ} (hk : k x ≠ 0) (hφ : φ x ≠ 0)
    (hy : HasDerivAt y (y' x) x) (hky : HasDerivAt (fun t => k t * y' t) (-(φ x * y x)) x)
    (hkφ : HasDerivAt (fun t => k t * φ t) dx x) :
    HasDerivAt (sonineFunction k φ y y') (-((k x * y' x) ^ 2 * dx / (k x * φ x) ^ 2)) x := by
  have h := (hy.pow 2).add ((hky.pow 2).div hkφ (mul_ne_zero hk hφ))
  show HasDerivAt (fun t => y t ^ 2 + (k t * y' t) ^ 2 / (k t * φ t)) _ x
  convert h using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- Under the hypotheses of the Sonine–Pólya theorem, the derivative of Sonine's function. -/
theorem hasDerivAt_sonineFunction_of_mem
    (hk : ∀ x ∈ Icc a b, 0 < k x) (hφ : ∀ x ∈ Icc a b, 0 < φ x)
    (hy : ∀ x ∈ Icc a b, HasDerivAt y (y' x) x)
    (hky : ∀ x ∈ Icc a b, HasDerivAt (fun t => k t * y' t) (-(φ x * y x)) x)
    (hkφ : ∀ x ∈ Icc a b, HasDerivAt (fun t => k t * φ t) (d x) x) :
    ∀ x ∈ Icc a b, HasDerivAt (sonineFunction k φ y y')
      (-((k x * y' x) ^ 2 * d x / (k x * φ x) ^ 2)) x := fun x hx =>
  hasDerivAt_sonineFunction (hk x hx).ne' (hφ x hx).ne' (hy x hx) (hky x hx) (hkφ x hx)

/-- **Sonine–Pólya**: if `(k φ)' ≥ 0` on `(a, b)`, Sonine's function decreases on `[a, b]`. -/
theorem antitoneOn_sonineFunction
    (hk : ∀ x ∈ Icc a b, 0 < k x) (hφ : ∀ x ∈ Icc a b, 0 < φ x)
    (hy : ∀ x ∈ Icc a b, HasDerivAt y (y' x) x)
    (hky : ∀ x ∈ Icc a b, HasDerivAt (fun t => k t * y' t) (-(φ x * y x)) x)
    (hkφ : ∀ x ∈ Icc a b, HasDerivAt (fun t => k t * φ t) (d x) x)
    (hd : ∀ x ∈ Ioo a b, 0 ≤ d x) : AntitoneOn (sonineFunction k φ y y') (Icc a b) := by
  have hS := hasDerivAt_sonineFunction_of_mem hk hφ hy hky hkφ
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    (f' := fun x => -((k x * y' x) ^ 2 * d x / (k x * φ x) ^ 2))
    (fun x hx => (hS x hx).continuousAt.continuousWithinAt) (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Icc] at hx
    exact (hS x (Ioo_subset_Icc_self hx)).hasDerivWithinAt
  · rw [interior_Icc] at hx
    exact neg_nonpos.mpr (div_nonneg (mul_nonneg (sq_nonneg _) (hd x hx)) (sq_nonneg _))

/-- **Sonine–Pólya**: if `(k φ)' ≤ 0` on `(a, b)`, Sonine's function increases on `[a, b]`. -/
theorem monotoneOn_sonineFunction
    (hk : ∀ x ∈ Icc a b, 0 < k x) (hφ : ∀ x ∈ Icc a b, 0 < φ x)
    (hy : ∀ x ∈ Icc a b, HasDerivAt y (y' x) x)
    (hky : ∀ x ∈ Icc a b, HasDerivAt (fun t => k t * y' t) (-(φ x * y x)) x)
    (hkφ : ∀ x ∈ Icc a b, HasDerivAt (fun t => k t * φ t) (d x) x)
    (hd : ∀ x ∈ Ioo a b, d x ≤ 0) : MonotoneOn (sonineFunction k φ y y') (Icc a b) := by
  have hS := hasDerivAt_sonineFunction_of_mem hk hφ hy hky hkφ
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (f' := fun x => -((k x * y' x) ^ 2 * d x / (k x * φ x) ^ 2))
    (fun x hx => (hS x hx).continuousAt.continuousWithinAt) (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Icc] at hx
    exact (hS x (Ioo_subset_Icc_self hx)).hasDerivWithinAt
  · rw [interior_Icc] at hx
    rw [neg_nonneg, ← neg_neg (d x), mul_neg, neg_div]
    exact neg_nonpos.mpr
      (div_nonneg (mul_nonneg (sq_nonneg _) (neg_nonneg.mpr (hd x hx))) (sq_nonneg _))

theorem sq_le_sonineFunction {x : ℝ} (hk : 0 < k x) (hφ : 0 < φ x) :
    y x ^ 2 ≤ sonineFunction k φ y y' x :=
  le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (mul_pos hk hφ).le)

theorem sonineFunction_of_deriv_eq_zero {x : ℝ} (h : y' x = 0) :
    sonineFunction k φ y y' x = y x ^ 2 := by
  simp [sonineFunction, h]

/-- If `(k φ)' ≥ 0` and `y` has a critical point at `a`, then `|y| ≤ |y(a)|` on `[a, b]`. -/
theorem abs_le_of_deriv_eq_zero_left (hab : a ≤ b)
    (hk : ∀ x ∈ Icc a b, 0 < k x) (hφ : ∀ x ∈ Icc a b, 0 < φ x)
    (hy : ∀ x ∈ Icc a b, HasDerivAt y (y' x) x)
    (hky : ∀ x ∈ Icc a b, HasDerivAt (fun t => k t * y' t) (-(φ x * y x)) x)
    (hkφ : ∀ x ∈ Icc a b, HasDerivAt (fun t => k t * φ t) (d x) x)
    (hd : ∀ x ∈ Ioo a b, 0 ≤ d x) (hya : y' a = 0) :
    ∀ x ∈ Icc a b, |y x| ≤ |y a| := by
  intro x hx
  have hS := antitoneOn_sonineFunction hk hφ hy hky hkφ hd (left_mem_Icc.mpr hab) hx hx.1
  rw [sonineFunction_of_deriv_eq_zero hya] at hS
  exact sq_le_sq.mp ((sq_le_sonineFunction (hk x hx) (hφ x hx)).trans hS)

/-- If `(k φ)' ≤ 0` and `y` has a critical point at `b`, then `|y| ≤ |y(b)|` on `[a, b]`. -/
theorem abs_le_of_deriv_eq_zero_right (hab : a ≤ b)
    (hk : ∀ x ∈ Icc a b, 0 < k x) (hφ : ∀ x ∈ Icc a b, 0 < φ x)
    (hy : ∀ x ∈ Icc a b, HasDerivAt y (y' x) x)
    (hky : ∀ x ∈ Icc a b, HasDerivAt (fun t => k t * y' t) (-(φ x * y x)) x)
    (hkφ : ∀ x ∈ Icc a b, HasDerivAt (fun t => k t * φ t) (d x) x)
    (hd : ∀ x ∈ Ioo a b, d x ≤ 0) (hyb : y' b = 0) :
    ∀ x ∈ Icc a b, |y x| ≤ |y b| := by
  intro x hx
  have hS := monotoneOn_sonineFunction hk hφ hy hky hkφ hd hx (right_mem_Icc.mpr hab) hx.2
  rw [sonineFunction_of_deriv_eq_zero hyb] at hS
  exact sq_le_sq.mp ((sq_le_sonineFunction (hk x hx) (hφ x hx)).trans hS)

/-- If Sonine's function is constant on `[a, b]` and `(k φ)'` has no zero in `(a, b)`, the
solution vanishes on `[a, b]`. -/
theorem eq_zero_of_sonineFunction_const (hab : a < b)
    (hk : ∀ x ∈ Icc a b, 0 < k x) (hφ : ∀ x ∈ Icc a b, 0 < φ x)
    (hy : ∀ x ∈ Icc a b, HasDerivAt y (y' x) x)
    (hky : ∀ x ∈ Icc a b, HasDerivAt (fun t => k t * y' t) (-(φ x * y x)) x)
    (hkφ : ∀ x ∈ Icc a b, HasDerivAt (fun t => k t * φ t) (d x) x)
    (hd : ∀ x ∈ Ioo a b, d x ≠ 0)
    (hconst : ∀ x ∈ Icc a b, sonineFunction k φ y y' x = sonineFunction k φ y y' a) :
    ∀ x ∈ Icc a b, y x = 0 := by
  have hS := hasDerivAt_sonineFunction_of_mem hk hφ hy hky hkφ
  -- `k y'` vanishes on `(a, b)`
  have hg : ∀ x ∈ Ioo a b, k x * y' x = 0 := by
    intro x hx
    have hloc : sonineFunction k φ y y' =ᶠ[𝓝 x] fun _ => sonineFunction k φ y y' a := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht using hconst t (Ioo_subset_Icc_self ht)
    have h0 := (hS x (Ioo_subset_Icc_self hx)).unique
      ((hasDerivAt_const x (sonineFunction k φ y y' a)).congr_of_eventuallyEq hloc)
    have hkφ0 : (k x * φ x) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (mul_pos (hk x (Ioo_subset_Icc_self hx)) (hφ x (Ioo_subset_Icc_self hx))).ne'
    rw [neg_eq_zero, div_eq_zero_iff, mul_eq_zero] at h0
    rcases h0 with (h | h) | h
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    · exact absurd h (hd x hx)
    · exact absurd h hkφ0
  -- hence `φ y` vanishes on `(a, b)`
  have hin : ∀ x ∈ Ioo a b, y x = 0 := by
    intro x hx
    have hloc : (fun t => k t * y' t) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht using hg t ht
    have h0 := (hky x (Ioo_subset_Icc_self hx)).unique
      ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hloc)
    rw [neg_eq_zero, mul_eq_zero] at h0
    rcases h0 with h | h
    · exact absurd h (hφ x (Ioo_subset_Icc_self hx)).ne'
    · exact h
  intro x hx
  rcases hx.1.eq_or_lt with hax | hax
  · subst hax
    have ht := (hy a hx).continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi a))
    have ht0 : Tendsto y (𝓝[>] a) (𝓝 0) := tendsto_const_nhds.congr' <| by
      filter_upwards [Ioo_mem_nhdsGT hab] with t ht using (hin t ht).symm
    exact tendsto_nhds_unique ht ht0
  rcases hx.2.eq_or_lt with hxb | hxb
  · subst hxb
    have ht := (hy x hx).continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio x))
    have ht0 : Tendsto y (𝓝[<] x) (𝓝 0) := tendsto_const_nhds.congr' <| by
      filter_upwards [Ioo_mem_nhdsLT hab] with t ht using (hin t ht).symm
    exact tendsto_nhds_unique ht ht0
  · exact hin x ⟨hax, hxb⟩

/-- **Sonine–Pólya**, strict form: if `(k φ)' > 0` on `(a, b)` and `y` has critical points at
`a < b` with `y(b) ≠ 0`, then `|y(b)| < |y(a)|`: successive relative maxima of `|y|`
decrease. -/
theorem abs_lt_of_deriv_eq_zero (hab : a < b)
    (hk : ∀ x ∈ Icc a b, 0 < k x) (hφ : ∀ x ∈ Icc a b, 0 < φ x)
    (hy : ∀ x ∈ Icc a b, HasDerivAt y (y' x) x)
    (hky : ∀ x ∈ Icc a b, HasDerivAt (fun t => k t * y' t) (-(φ x * y x)) x)
    (hkφ : ∀ x ∈ Icc a b, HasDerivAt (fun t => k t * φ t) (d x) x)
    (hd : ∀ x ∈ Ioo a b, 0 < d x) (hya : y' a = 0) (hyb : y' b = 0) (hyb0 : y b ≠ 0) :
    |y b| < |y a| := by
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  have hanti := antitoneOn_sonineFunction hk hφ hy hky hkφ fun x hx => (hd x hx).le
  by_contra hcon
  push Not at hcon
  have hSa := sonineFunction_of_deriv_eq_zero (k := k) (φ := φ) (y := y) hya
  have hSb := sonineFunction_of_deriv_eq_zero (k := k) (φ := φ) (y := y) hyb
  have hsq : y a ^ 2 ≤ y b ^ 2 := sq_le_sq.mpr hcon
  have hconst : ∀ x ∈ Icc a b, sonineFunction k φ y y' x = sonineFunction k φ y y' a := by
    intro x hx
    have h1 := hanti ha hx hx.1
    have h2 := hanti hx hb hx.2
    linarith
  exact hyb0 (eq_zero_of_sonineFunction_const hab hk hφ hy hky hkφ (fun x hx => (hd x hx).ne')
    hconst b hb)

/-- **Sonine–Pólya**, strict form: if `(k φ)' < 0` on `(a, b)` and `y` has critical points at
`a < b` with `y(a) ≠ 0`, then `|y(a)| < |y(b)|`: successive relative maxima of `|y|`
increase. -/
theorem abs_lt_of_deriv_eq_zero' (hab : a < b)
    (hk : ∀ x ∈ Icc a b, 0 < k x) (hφ : ∀ x ∈ Icc a b, 0 < φ x)
    (hy : ∀ x ∈ Icc a b, HasDerivAt y (y' x) x)
    (hky : ∀ x ∈ Icc a b, HasDerivAt (fun t => k t * y' t) (-(φ x * y x)) x)
    (hkφ : ∀ x ∈ Icc a b, HasDerivAt (fun t => k t * φ t) (d x) x)
    (hd : ∀ x ∈ Ioo a b, d x < 0) (hya : y' a = 0) (hyb : y' b = 0) (hya0 : y a ≠ 0) :
    |y a| < |y b| := by
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  have hmono := monotoneOn_sonineFunction hk hφ hy hky hkφ fun x hx => (hd x hx).le
  by_contra hcon
  push Not at hcon
  have hSa := sonineFunction_of_deriv_eq_zero (k := k) (φ := φ) (y := y) hya
  have hSb := sonineFunction_of_deriv_eq_zero (k := k) (φ := φ) (y := y) hyb
  have hsq : y b ^ 2 ≤ y a ^ 2 := sq_le_sq.mpr hcon
  have hconst : ∀ x ∈ Icc a b, sonineFunction k φ y y' x = sonineFunction k φ y y' a := by
    intro x hx
    have h1 := hmono ha hx hx.1
    have h2 := hmono hx hb hx.2
    linarith
  exact hya0 (eq_zero_of_sonineFunction_const hab hk hφ hy hky hkφ (fun x hx => (hd x hx).ne)
    hconst a ha)

end ODE
