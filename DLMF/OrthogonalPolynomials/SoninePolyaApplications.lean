/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Sonine–Pólya bounds for the classical differential equations

Sonine's function `S = y² + (k/φ) y'²` for the self-adjoint form `(k y')' + φ y = 0` (see
`DLMFMathlib.Analysis.ODE.SoninePolya`) applied to the Jacobi, Hermite and Laguerre equations
(Szegő, §§7.2, 7.31–7.32; Beals–Wong, §3.5). Here `k` vanishes at the ends of the Jacobi and
Laguerre intervals, so `S` is written directly in terms of the equation in its usual form
and differentiated by hand. The results are stated for arbitrary solutions `y` with derivatives
`y'`, `y''`, so they apply to the classical polynomials once their differential equations are
supplied.

* `jacobi_ode_abs_le_max`: if `λ > 0` and `α + β + 1 > 0`, a solution of
  `(1 - x²) y'' + (β - α - (α + β + 2) x) y' + λ y = 0` satisfies
  `|y x| ≤ max |y (-1)| |y 1|` on `[-1, 1]`. This is the core of DLMF 18.14.1–2.
* `jacobi_ode_abs_le_right`: the one-sided form `|y x| ≤ |y 1|` when
  `β - α ≤ (α + β + 1) x` on `(-1, 1)` (the case `α + β + 1 ≤ 0 ≤ 2α + 1`).
* `jacobi_ode_sq_le_zero`, `jacobi_ode_sq_lt_zero`: for the symmetric equation with
  `2a + 1 ≤ 0` (Gegenbauer `λ ≤ 0`), `y x ² ≤ y 0 ² + y' 0 ² / λ`, strictly on `(0, 1]` when
  `2a + 1 < 0`; the core of DLMF 18.14.5–6.
* `hermite_ode_abs_le`: for `y'' - 2 x y' + λ y = 0`, `λ > 0`, and a critical point `b ≥ 0`,
  `|y| ≤ |y b|` on `[a, b]` with `0 ≤ a`: the relative maxima of `|H_n|` increase on `x ≥ 0`.
* `laguerre_ode_abs_le_right`, `laguerre_ode_abs_le_left`: for
  `x y'' + (α + 1 - x) y' + λ y = 0`, the relative maxima of `|y|` decrease on
  `[0, α + 1/2]` and increase on `[α + 1/2, ∞)`.
-/

@[expose] public section

open Set

namespace DLMF.OrthogonalPolynomials

section SoninePolya

variable {y y' y'' : ℝ → ℝ}

private lemma monotoneOn_of_hasDerivAt_nonneg' {S S' : ℝ → ℝ} {a b : ℝ}
    (hS : ∀ x ∈ Icc a b, HasDerivAt S (S' x) x) (h : ∀ x ∈ Ioo a b, 0 ≤ S' x) :
    MonotoneOn S (Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) (f' := S')
    (fun x hx => (hS x hx).continuousAt.continuousWithinAt) (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Icc] at hx
    exact (hS x (Ioo_subset_Icc_self hx)).hasDerivWithinAt
  · rw [interior_Icc] at hx
    exact h x hx

private lemma antitoneOn_of_hasDerivAt_nonpos' {S S' : ℝ → ℝ} {a b : ℝ}
    (hS : ∀ x ∈ Icc a b, HasDerivAt S (S' x) x) (h : ∀ x ∈ Ioo a b, S' x ≤ 0) :
    AntitoneOn S (Icc a b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) (f' := S')
    (fun x hx => (hS x hx).continuousAt.continuousWithinAt) (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Icc] at hx
    exact (hS x (Ioo_subset_Icc_self hx)).hasDerivWithinAt
  · rw [interior_Icc] at hx
    exact h x hx

/-- Derivative of `y² + w y'² / λ` for a differentiable weight `w`. -/
private lemma hasDerivAt_sonine {w w' : ℝ → ℝ} {lam x : ℝ}
    (hy : HasDerivAt y (y' x) x) (hy' : HasDerivAt y' (y'' x) x) (hw : HasDerivAt w (w' x) x) :
    HasDerivAt (fun t => y t ^ 2 + w t * y' t ^ 2 / lam)
      (2 * y x * y' x + (w' x * y' x ^ 2 + w x * (2 * y' x * y'' x)) / lam) x := by
  have h := (hy.pow 2).add ((hw.mul (hy'.pow 2)).div_const lam)
  convert h using 1
  simp

/-- **Sonine–Pólya for the Jacobi equation** (Szegő, Theorem 7.32.1). If `λ > 0` and
`α + β + 1 > 0`, every solution of `(1 - x²) y'' + (β - α - (α + β + 2) x) y' + λ y = 0` on
`[-1, 1]` takes its largest absolute value at an endpoint. -/
theorem jacobi_ode_abs_le_max {α β lam : ℝ} (hlam : 0 < lam) (hαβ : 0 < α + β + 1)
    (hy : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivAt y (y' x) x)
    (hy' : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivAt y' (y'' x) x)
    (hode : ∀ x ∈ Ioo (-1 : ℝ) 1,
      (1 - x ^ 2) * y'' x + (β - α - (α + β + 2) * x) * y' x + lam * y x = 0) :
    ∀ x ∈ Icc (-1 : ℝ) 1, |y x| ≤ max |y (-1)| |y 1| := by
  set S : ℝ → ℝ := fun t => y t ^ 2 + (1 - t ^ 2) * y' t ^ 2 / lam with hSdef
  set x₀ := (β - α) / (α + β + 1)
  have hS : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivAt S
      (2 * y x * y' x + ((-(2 * x)) * y' x ^ 2 + (1 - x ^ 2) * (2 * y' x * y'' x)) / lam) x := by
    intro x hx
    have hw : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * x)) x := by
      simpa using ((hasDerivAt_id x).pow 2).const_sub (1 : ℝ)
    exact hasDerivAt_sonine (w := fun t => 1 - t ^ 2) (w' := fun t => -(2 * t)) (hy x hx)
      (hy' x hx) hw
  have hS' : ∀ x ∈ Ioo (-1 : ℝ) 1,
      2 * y x * y' x + ((-(2 * x)) * y' x ^ 2 + (1 - x ^ 2) * (2 * y' x * y'' x)) / lam =
        2 * y' x ^ 2 * ((α + β + 1) * x - (β - α)) / lam := by
    intro x hx
    field_simp
    linear_combination (y' x) * hode x hx
  have hkey : ∀ t, x₀ ≤ t ↔ β - α ≤ (α + β + 1) * t := fun t => by
    rw [div_le_iff₀ hαβ, mul_comm]
  have hy2 : ∀ x ∈ Icc (-1 : ℝ) 1, y x ^ 2 ≤ S x := fun x hx => by
    have : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    exact le_add_of_nonneg_right (div_nonneg (mul_nonneg this (sq_nonneg _)) hlam.le)
  have hS1 : S 1 = y 1 ^ 2 := by simp [hSdef]
  have hSm1 : S (-1) = y (-1) ^ 2 := by simp [hSdef]
  intro x hx
  rcases le_or_gt x₀ x with hx₀ | hx₀
  · have hmono : MonotoneOn S (Icc x 1) := by
      refine monotoneOn_of_hasDerivAt_nonneg' (fun t ht => hS t ⟨hx.1.trans ht.1, ht.2⟩)
        fun t ht => ?_
      rw [hS' t ⟨hx.1.trans_lt ht.1, ht.2⟩]
      have h := (hkey t).mp (hx₀.trans ht.1.le)
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by linarith))
        hlam.le
    have h := hmono (left_mem_Icc.mpr hx.2) (right_mem_Icc.mpr hx.2) hx.2
    have h2 : |y x| ≤ |y 1| := sq_le_sq.mp ((hy2 x hx).trans (h.trans hS1.le))
    exact h2.trans (le_max_right _ _)
  · have hanti : AntitoneOn S (Icc (-1) x) := by
      refine antitoneOn_of_hasDerivAt_nonpos' (fun t ht => hS t ⟨ht.1, ht.2.trans hx.2⟩)
        fun t ht => ?_
      rw [hS' t ⟨ht.1, ht.2.trans_le hx.2⟩]
      have h : (α + β + 1) * t < β - α := by
        by_contra hc
        exact absurd ((hkey t).mpr (not_lt.mp hc)) (not_le.mpr (ht.2.trans hx₀))
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) (sq_nonneg _))
          (by linarith)) hlam.le
    have h := hanti (left_mem_Icc.mpr hx.1) (right_mem_Icc.mpr hx.1) hx.1
    have h2 : |y x| ≤ |y (-1)| := sq_le_sq.mp ((hy2 x hx).trans (h.trans hSm1.le))
    exact h2.trans (le_max_left _ _)

/-- A one-sided Sonine–Pólya bound for the Jacobi equation: if `λ > 0` and
`β - α ≤ (α + β + 1) x` on `(-1, 1)`, Sonine's function increases on `[-1, 1]`, so a solution
satisfies `|y x| ≤ |y 1|` there. This covers `α + β + 1 ≤ 0 ≤ 2 α + 1`. -/
theorem jacobi_ode_abs_le_right {α β lam : ℝ} (hlam : 0 < lam)
    (hsign : ∀ x ∈ Ioo (-1 : ℝ) 1, β - α ≤ (α + β + 1) * x)
    (hy : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivAt y (y' x) x)
    (hy' : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivAt y' (y'' x) x)
    (hode : ∀ x ∈ Ioo (-1 : ℝ) 1,
      (1 - x ^ 2) * y'' x + (β - α - (α + β + 2) * x) * y' x + lam * y x = 0) :
    ∀ x ∈ Icc (-1 : ℝ) 1, |y x| ≤ |y 1| := by
  set S : ℝ → ℝ := fun t => y t ^ 2 + (1 - t ^ 2) * y' t ^ 2 / lam with hSdef
  have hS : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivAt S
      (2 * y x * y' x + ((-(2 * x)) * y' x ^ 2 + (1 - x ^ 2) * (2 * y' x * y'' x)) / lam) x := by
    intro x hx
    have hw : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * x)) x := by
      simpa using ((hasDerivAt_id x).pow 2).const_sub (1 : ℝ)
    exact hasDerivAt_sonine (w := fun t => 1 - t ^ 2) (w' := fun t => -(2 * t)) (hy x hx)
      (hy' x hx) hw
  have hmono : MonotoneOn S (Icc (-1) 1) := by
    refine monotoneOn_of_hasDerivAt_nonneg' hS fun t ht => ?_
    have h : 2 * y t * y' t + ((-(2 * t)) * y' t ^ 2 + (1 - t ^ 2) * (2 * y' t * y'' t)) / lam =
        2 * y' t ^ 2 * ((α + β + 1) * t - (β - α)) / lam := by
      field_simp
      linear_combination (y' t) * hode t ht
    rw [h]
    have := hsign t ht
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by linarith))
      hlam.le
  intro x hx
  have hy2 : y x ^ 2 ≤ S x := by
    have : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    exact le_add_of_nonneg_right (div_nonneg (mul_nonneg this (sq_nonneg _)) hlam.le)
  have h := hmono hx (right_mem_Icc.mpr (by norm_num)) hx.2
  have hS1 : S 1 = y 1 ^ 2 := by simp [hSdef]
  exact sq_le_sq.mp (hy2.trans (h.trans hS1.le))

/-- Sonine–Pólya for the symmetric Jacobi equation with `2a + 1 ≤ 0` (Gegenbauer parameter
`λ = a + 1/2 ≤ 0`): Sonine's function increases on `[-1, 0]` and decreases on `[0, 1]`, so a
solution satisfies `y x ² ≤ y 0 ² + y' 0 ² / λ` on `[-1, 1]`. -/
theorem jacobi_ode_sq_le_zero {a lam : ℝ} (hlam : 0 < lam) (ha : 2 * a + 1 ≤ 0)
    (hy : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivAt y (y' x) x)
    (hy' : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivAt y' (y'' x) x)
    (hode : ∀ x ∈ Ioo (-1 : ℝ) 1,
      (1 - x ^ 2) * y'' x + (a - a - (a + a + 2) * x) * y' x + lam * y x = 0) :
    ∀ x ∈ Icc (-1 : ℝ) 1, y x ^ 2 ≤ y 0 ^ 2 + y' 0 ^ 2 / lam := by
  set S : ℝ → ℝ := fun t => y t ^ 2 + (1 - t ^ 2) * y' t ^ 2 / lam with hSdef
  have hS : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivAt S
      (2 * y x * y' x + ((-(2 * x)) * y' x ^ 2 + (1 - x ^ 2) * (2 * y' x * y'' x)) / lam) x := by
    intro x hx
    have hw : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * x)) x := by
      simpa using ((hasDerivAt_id x).pow 2).const_sub (1 : ℝ)
    exact hasDerivAt_sonine (w := fun t => 1 - t ^ 2) (w' := fun t => -(2 * t)) (hy x hx)
      (hy' x hx) hw
  have hS' : ∀ x ∈ Ioo (-1 : ℝ) 1,
      2 * y x * y' x + ((-(2 * x)) * y' x ^ 2 + (1 - x ^ 2) * (2 * y' x * y'' x)) / lam =
        2 * y' x ^ 2 * ((2 * a + 1) * x) / lam := by
    intro x hx
    field_simp
    linear_combination (y' x) * hode x hx
  have hy2 : ∀ x ∈ Icc (-1 : ℝ) 1, y x ^ 2 ≤ S x := fun x hx => by
    have : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    exact le_add_of_nonneg_right (div_nonneg (mul_nonneg this (sq_nonneg _)) hlam.le)
  have hS0 : S 0 = y 0 ^ 2 + y' 0 ^ 2 / lam := by simp [hSdef]
  intro x hx
  rw [← hS0]
  refine (hy2 x hx).trans ?_
  rcases le_total 0 x with hx0 | hx0
  · have hanti : AntitoneOn S (Icc 0 1) := by
      refine antitoneOn_of_hasDerivAt_nonpos' (fun t ht => hS t ⟨by linarith [ht.1], ht.2⟩)
        fun t ht => ?_
      rw [hS' t ⟨by linarith [ht.1], ht.2⟩]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) (sq_nonneg _))
          (mul_nonpos_of_nonpos_of_nonneg ha ht.1.le)) hlam.le
    exact hanti (left_mem_Icc.mpr (by norm_num)) ⟨hx0, hx.2⟩ hx0
  · have hmono : MonotoneOn S (Icc (-1) 0) := by
      refine monotoneOn_of_hasDerivAt_nonneg' (fun t ht => hS t ⟨ht.1, by linarith [ht.2]⟩)
        fun t ht => ?_
      rw [hS' t ⟨ht.1, by linarith [ht.2]⟩]
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (mul_nonneg_of_nonpos_of_nonpos ha ht.2.le)) hlam.le
    exact hmono ⟨hx.1, hx0⟩ (right_mem_Icc.mpr (by norm_num)) hx0

/-- Strict form of `jacobi_ode_sq_le_zero` on `(0, 1]`, for `2a + 1 < 0` and a solution whose
derivative does not vanish identically on any subinterval. -/
theorem jacobi_ode_sq_lt_zero {a lam : ℝ} (hlam : 0 < lam) (ha : 2 * a + 1 < 0)
    (hy : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivAt y (y' x) x)
    (hy' : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivAt y' (y'' x) x)
    (hode : ∀ x ∈ Ioo (-1 : ℝ) 1,
      (1 - x ^ 2) * y'' x + (a - a - (a + a + 2) * x) * y' x + lam * y x = 0)
    (hnz : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Ioo s t, y' u ≠ 0) :
    ∀ x ∈ Ioc (0 : ℝ) 1, y x ^ 2 < y 0 ^ 2 + y' 0 ^ 2 / lam := by
  set S : ℝ → ℝ := fun t => y t ^ 2 + (1 - t ^ 2) * y' t ^ 2 / lam with hSdef
  have hS : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivAt S
      (2 * y x * y' x + ((-(2 * x)) * y' x ^ 2 + (1 - x ^ 2) * (2 * y' x * y'' x)) / lam) x := by
    intro x hx
    have hw : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * x)) x := by
      simpa using ((hasDerivAt_id x).pow 2).const_sub (1 : ℝ)
    exact hasDerivAt_sonine (w := fun t => 1 - t ^ 2) (w' := fun t => -(2 * t)) (hy x hx)
      (hy' x hx) hw
  have hS' : ∀ x ∈ Ioo (-1 : ℝ) 1,
      2 * y x * y' x + ((-(2 * x)) * y' x ^ 2 + (1 - x ^ 2) * (2 * y' x * y'' x)) / lam =
        2 * y' x ^ 2 * ((2 * a + 1) * x) / lam := by
    intro x hx
    field_simp
    linear_combination (y' x) * hode x hx
  have hy2 : ∀ x ∈ Icc (-1 : ℝ) 1, y x ^ 2 ≤ S x := fun x hx => by
    have : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    exact le_add_of_nonneg_right (div_nonneg (mul_nonneg this (sq_nonneg _)) hlam.le)
  have hS0 : S 0 = y 0 ^ 2 + y' 0 ^ 2 / lam := by simp [hSdef]
  have hanti : AntitoneOn S (Icc 0 1) := by
    refine antitoneOn_of_hasDerivAt_nonpos' (fun t ht => hS t ⟨by linarith [ht.1], ht.2⟩)
      fun t ht => ?_
    rw [hS' t ⟨by linarith [ht.1], ht.2⟩]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) (sq_nonneg _))
        (mul_nonpos_of_nonpos_of_nonneg ha.le ht.1.le)) hlam.le
  intro x hx
  rw [← hS0]
  by_contra! hc
  have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  have hSx : S x ≤ S 0 := hanti (left_mem_Icc.mpr (by norm_num)) hxI hx.1.le
  have hconst : ∀ v ∈ Icc 0 x, S v = S 0 := fun v hv => by
    have h1 := hanti (left_mem_Icc.mpr (by norm_num)) ⟨hv.1, hv.2.trans hx.2⟩ hv.1
    have h2 := hanti ⟨hv.1, hv.2.trans hx.2⟩ hxI hv.2
    linarith [hy2 x ⟨by linarith [hx.1], hx.2⟩]
  obtain ⟨u, hu, hyu⟩ := hnz 0 x le_rfl hx.1 hx.2
  have hev : S =ᶠ[nhds u] fun _ => S 0 := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
    exact hconst v ⟨hv.1.le, hv.2.le⟩
  have huI : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], hu.2.trans_le hx.2⟩
  have h0 := (hS u (Ioo_subset_Icc_self huI)).unique
    ((hasDerivAt_const u (S 0)).congr_of_eventuallyEq hev)
  rw [hS' u huI] at h0
  have : y' u ^ 2 * (u * (2 * a + 1)) = 0 := by
    field_simp at h0; linarith
  rcases mul_eq_zero.mp this with h | h
  · exact hyu (pow_eq_zero_iff (by norm_num) |>.mp h)
  · rcases mul_eq_zero.mp h with h' | h'
    · linarith [hu.1]
    · linarith

/-- **Sonine–Pólya for the Hermite equation** (Szegő, Theorem 7.31.1). For a solution of
`y'' - 2 x y' + λ y = 0` with `λ > 0` on `[a, b] ⊆ [0, ∞)` and a critical point at `b`,
`|y| ≤ |y b|` on `[a, b]`: on `x ≥ 0` the relative maxima of `|y|` increase. -/
theorem hermite_ode_abs_le {lam a b : ℝ} (hlam : 0 < lam) (ha : 0 ≤ a) (hab : a ≤ b)
    (hy : ∀ x ∈ Icc a b, HasDerivAt y (y' x) x)
    (hy' : ∀ x ∈ Icc a b, HasDerivAt y' (y'' x) x)
    (hode : ∀ x ∈ Ioo a b, y'' x - 2 * x * y' x + lam * y x = 0) (hyb : y' b = 0) :
    ∀ x ∈ Icc a b, |y x| ≤ |y b| := by
  set S : ℝ → ℝ := fun t => y t ^ 2 + 1 * y' t ^ 2 / lam with hSdef
  have hS : ∀ x ∈ Icc a b, HasDerivAt S
      (2 * y x * y' x + (0 * y' x ^ 2 + 1 * (2 * y' x * y'' x)) / lam) x := fun x hx =>
    hasDerivAt_sonine (w := fun _ => 1) (w' := fun _ => 0) (hy x hx) (hy' x hx)
      (hasDerivAt_const x (1 : ℝ))
  have hmono : MonotoneOn S (Icc a b) := by
    refine monotoneOn_of_hasDerivAt_nonneg' hS fun t ht => ?_
    have h : 2 * y t * y' t + (0 * y' t ^ 2 + 1 * (2 * y' t * y'' t)) / lam =
        4 * t * y' t ^ 2 / lam := by
      field_simp
      linear_combination (2 * y' t) * hode t ht
    rw [h]
    have ht0 : 0 ≤ t := ha.trans ht.1.le
    positivity
  intro x hx
  have h := hmono hx (right_mem_Icc.mpr hab) hx.2
  have hSb : S b = y b ^ 2 := by simp [hSdef, hyb]
  have hy2 : y x ^ 2 ≤ S x :=
    le_add_of_nonneg_right (div_nonneg (by positivity) hlam.le)
  exact sq_le_sq.mp (hy2.trans (h.trans hSb.le))

/-- **Sonine–Pólya for the Laguerre equation** on `[α + 1/2, ∞)` (Szegő, Theorem 7.31.1): for
a solution of `x y'' + (α + 1 - x) y' + λ y = 0` with `λ > 0` on `[a, b]`,
`max 0 (α + 1/2) ≤ a`, and a critical point at `b`, `|y| ≤ |y b|` on `[a, b]`. -/
theorem laguerre_ode_abs_le_right {α lam a b : ℝ} (hlam : 0 < lam) (ha0 : 0 ≤ a)
    (ha : α + 1 / 2 ≤ a) (hab : a ≤ b)
    (hy : ∀ x ∈ Icc a b, HasDerivAt y (y' x) x)
    (hy' : ∀ x ∈ Icc a b, HasDerivAt y' (y'' x) x)
    (hode : ∀ x ∈ Ioo a b, x * y'' x + (α + 1 - x) * y' x + lam * y x = 0) (hyb : y' b = 0) :
    ∀ x ∈ Icc a b, |y x| ≤ |y b| := by
  set S : ℝ → ℝ := fun t => y t ^ 2 + t * y' t ^ 2 / lam with hSdef
  have hS : ∀ x ∈ Icc a b, HasDerivAt S
      (2 * y x * y' x + (1 * y' x ^ 2 + x * (2 * y' x * y'' x)) / lam) x := fun x hx =>
    hasDerivAt_sonine (w := fun t => t) (w' := fun _ => 1) (hy x hx) (hy' x hx)
      (hasDerivAt_id' x)
  have hmono : MonotoneOn S (Icc a b) := by
    refine monotoneOn_of_hasDerivAt_nonneg' hS fun t ht => ?_
    have h : 2 * y t * y' t + (1 * y' t ^ 2 + t * (2 * y' t * y'' t)) / lam =
        y' t ^ 2 * (2 * t - 2 * α - 1) / lam := by
      field_simp
      linear_combination (2 * y' t) * hode t ht
    rw [h]
    have : 0 ≤ 2 * t - 2 * α - 1 := by linarith [ht.1]
    positivity
  intro x hx
  have h := hmono hx (right_mem_Icc.mpr hab) hx.2
  have hSb : S b = y b ^ 2 := by simp [hSdef, hyb]
  have hy2 : y x ^ 2 ≤ S x :=
    le_add_of_nonneg_right (div_nonneg (mul_nonneg (ha0.trans hx.1) (sq_nonneg _)) hlam.le)
  exact sq_le_sq.mp (hy2.trans (h.trans hSb.le))

/-- **Sonine–Pólya for the Laguerre equation** on `[0, α + 1/2]`: for a solution of
`x y'' + (α + 1 - x) y' + λ y = 0` with `λ > 0` on `[a, b]`, `0 ≤ a`, `b ≤ α + 1/2`, and
`a y'(a) = 0` (a critical point, or `a = 0`), `|y| ≤ |y a|` on `[a, b]`. In particular
`|y| ≤ |y 0|` on `[0, α + 1/2]`. -/
theorem laguerre_ode_abs_le_left {α lam a b : ℝ} (hlam : 0 < lam) (ha0 : 0 ≤ a)
    (hb : b ≤ α + 1 / 2) (hab : a ≤ b)
    (hy : ∀ x ∈ Icc a b, HasDerivAt y (y' x) x)
    (hy' : ∀ x ∈ Icc a b, HasDerivAt y' (y'' x) x)
    (hode : ∀ x ∈ Ioo a b, x * y'' x + (α + 1 - x) * y' x + lam * y x = 0)
    (hya : a * y' a = 0) :
    ∀ x ∈ Icc a b, |y x| ≤ |y a| := by
  set S : ℝ → ℝ := fun t => y t ^ 2 + t * y' t ^ 2 / lam with hSdef
  have hS : ∀ x ∈ Icc a b, HasDerivAt S
      (2 * y x * y' x + (1 * y' x ^ 2 + x * (2 * y' x * y'' x)) / lam) x := fun x hx =>
    hasDerivAt_sonine (w := fun t => t) (w' := fun _ => 1) (hy x hx) (hy' x hx)
      (hasDerivAt_id' x)
  have hanti : AntitoneOn S (Icc a b) := by
    refine antitoneOn_of_hasDerivAt_nonpos' hS fun t ht => ?_
    have h : 2 * y t * y' t + (1 * y' t ^ 2 + t * (2 * y' t * y'' t)) / lam =
        y' t ^ 2 * (2 * t - 2 * α - 1) / lam := by
      field_simp
      linear_combination (2 * y' t) * hode t ht
    rw [h]
    have : 2 * t - 2 * α - 1 ≤ 0 := by linarith [ht.2]
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) this)
      hlam.le
  intro x hx
  have h := hanti (left_mem_Icc.mpr hab) hx hx.1
  have hSa : S a = y a ^ 2 := by
    simp only [hSdef]
    rw [show a * y' a ^ 2 = (a * y' a) * y' a by ring, hya]
    simp
  have hy2 : y x ^ 2 ≤ S x :=
    le_add_of_nonneg_right (div_nonneg (mul_nonneg (ha0.trans hx.1) (sq_nonneg _)) hlam.le)
  exact sq_le_sq.mp (hy2.trans (h.trans hSa.le))

end SoninePolya

end DLMF.OrthogonalPolynomials
