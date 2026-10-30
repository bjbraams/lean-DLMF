/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Appell.SeriesAndDifferentialEquations
public import DLMFMathlib.Analysis.Complex.BivariateCalculus

/-!
# Horn differential equations

The gamma-ratio coefficients of Horn G2 and G3 satisfy elementary shift recurrences.
Normal convergence and the bivariate series differentiation framework turn these
recurrences into the Euler-operator differential systems of DLMF 16.14(ii).

This module uses results of the Tau Ceti contributors; see also `CREDITS.md`.
-/

@[expose] public noncomputable section

open Complex Filter Set
open scoped Nat Topology

namespace DLMF.Hypergeometric

/-- The first Euler operator preserves joint complex analyticity. -/
private lemma analyticAt_appellThetaX {f : ℂ → ℂ → ℂ} {x y : ℂ}
    (hf : AnalyticAt ℂ (Function.uncurry f) (x, y)) :
    AnalyticAt ℂ (Function.uncurry (appellThetaX f)) (x, y) := by
  exact analyticAt_fst.mul (Complex.analyticAt_deriv_fst hf)

/-- The second Euler operator preserves joint complex analyticity. -/
private lemma analyticAt_appellThetaY {f : ℂ → ℂ → ℂ} {x y : ℂ}
    (hf : AnalyticAt ℂ (Function.uncurry f) (x, y)) :
    AnalyticAt ℂ (Function.uncurry (appellThetaY f)) (x, y) := by
  exact analyticAt_snd.mul (Complex.analyticAt_deriv_snd hf)

/-- The first Euler operator distributes over subtraction of analytic functions. -/
private lemma appellThetaX_sub {f g : ℂ → ℂ → ℂ} {x y : ℂ}
    (hf : AnalyticAt ℂ (Function.uncurry f) (x, y))
    (hg : AnalyticAt ℂ (Function.uncurry g) (x, y)) :
    appellThetaX (fun z w => f z w - g z w) x y =
      appellThetaX f x y - appellThetaX g x y := by
  have hfx : DifferentiableAt ℂ (fun z => f z y) x :=
    (hf.comp_of_eq (show AnalyticAt ℂ (fun z : ℂ => (z, y)) x from
      analyticAt_id.prod analyticAt_const) rfl).differentiableAt
  have hgx : DifferentiableAt ℂ (fun z => g z y) x :=
    (hg.comp_of_eq (show AnalyticAt ℂ (fun z : ℂ => (z, y)) x from
      analyticAt_id.prod analyticAt_const) rfl).differentiableAt
  unfold appellThetaX appellDx
  rw [deriv_fun_sub hfx hgx]
  ring

/-- The first Euler operator distributes over addition of analytic functions. -/
private lemma appellThetaX_add {f g : ℂ → ℂ → ℂ} {x y : ℂ}
    (hf : AnalyticAt ℂ (Function.uncurry f) (x, y))
    (hg : AnalyticAt ℂ (Function.uncurry g) (x, y)) :
    appellThetaX (fun z w => f z w + g z w) x y =
      appellThetaX f x y + appellThetaX g x y := by
  have hfx : DifferentiableAt ℂ (fun z => f z y) x :=
    (hf.comp_of_eq (show AnalyticAt ℂ (fun z : ℂ => (z, y)) x from
      analyticAt_id.prod analyticAt_const) rfl).differentiableAt
  have hgx : DifferentiableAt ℂ (fun z => g z y) x :=
    (hg.comp_of_eq (show AnalyticAt ℂ (fun z : ℂ => (z, y)) x from
      analyticAt_id.prod analyticAt_const) rfl).differentiableAt
  unfold appellThetaX appellDx
  rw [deriv_fun_add hfx hgx]
  ring

/-- The second Euler operator distributes over subtraction of analytic functions. -/
private lemma appellThetaY_sub {f g : ℂ → ℂ → ℂ} {x y : ℂ}
    (hf : AnalyticAt ℂ (Function.uncurry f) (x, y))
    (hg : AnalyticAt ℂ (Function.uncurry g) (x, y)) :
    appellThetaY (fun z w => f z w - g z w) x y =
      appellThetaY f x y - appellThetaY g x y := by
  have hfy : DifferentiableAt ℂ (f x) y :=
    (hf.comp (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hgy : DifferentiableAt ℂ (g x) y :=
    (hg.comp (analyticAt_const.prod analyticAt_id)).differentiableAt
  unfold appellThetaY appellDy
  rw [deriv_fun_sub hfy hgy]
  ring

/-- The second Euler operator distributes over addition of analytic functions. -/
private lemma appellThetaY_add {f g : ℂ → ℂ → ℂ} {x y : ℂ}
    (hf : AnalyticAt ℂ (Function.uncurry f) (x, y))
    (hg : AnalyticAt ℂ (Function.uncurry g) (x, y)) :
    appellThetaY (fun z w => f z w + g z w) x y =
      appellThetaY f x y + appellThetaY g x y := by
  have hfy : DifferentiableAt ℂ (f x) y :=
    (hf.comp (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hgy : DifferentiableAt ℂ (g x) y :=
    (hg.comp (analyticAt_const.prod analyticAt_id)).differentiableAt
  unfold appellThetaY appellDy
  rw [deriv_fun_add hfy hgy]
  ring

/-- The first Euler operator commutes with multiplication by a constant. -/
private lemma appellThetaX_const_mul (f : ℂ → ℂ → ℂ) (x y c : ℂ) :
    appellThetaX (fun z w => c * f z w) x y = c * appellThetaX f x y := by
  unfold appellThetaX appellDx
  rw [deriv_const_mul_field]
  ring

/-- The second Euler operator commutes with multiplication by a constant. -/
private lemma appellThetaY_const_mul (f : ℂ → ℂ → ℂ) (x y c : ℂ) :
    appellThetaY (fun z w => c * f z w) x y = c * appellThetaY f x y := by
  unfold appellThetaY appellDy
  rw [deriv_const_mul_field]
  ring

/-- The square of the first Euler operator expands into first and second partial derivatives. -/
private lemma appellThetaX_twice {f : ℂ → ℂ → ℂ} {x y : ℂ}
    (hf : AnalyticAt ℂ (Function.uncurry f) (x, y)) :
    appellThetaX (appellThetaX f) x y =
      x * appellDx f x y + x ^ 2 * appellDx (appellDx f) x y := by
  have hfx : AnalyticAt ℂ (fun z => f z y) x :=
    hf.comp_of_eq (show AnalyticAt ℂ (fun z : ℂ => (z, y)) x from
      analyticAt_id.prod analyticAt_const) rfl
  unfold appellThetaX appellDx
  change x * deriv (fun z => z * deriv (fun t => f t y) z) x = _
  have h := deriv_fun_mul differentiableAt_id hfx.deriv.differentiableAt
  dsimp only [id_eq] at h
  rw [h]
  simp only [deriv_id, one_mul]
  ring

/-- The square of the second Euler operator expands into first and second partial derivatives. -/
private lemma appellThetaY_twice {f : ℂ → ℂ → ℂ} {x y : ℂ}
    (hf : AnalyticAt ℂ (Function.uncurry f) (x, y)) :
    appellThetaY (appellThetaY f) x y =
      y * appellDy f x y + y ^ 2 * appellDy (appellDy f) x y := by
  have hfy : AnalyticAt ℂ (f x) y :=
    hf.comp (analyticAt_const.prod analyticAt_id)
  unfold appellThetaY appellDy
  change y * deriv (fun w => w * deriv (f x) w) y = _
  have h := deriv_fun_mul differentiableAt_id hfy.deriv.differentiableAt
  dsimp only [id_eq] at h
  rw [h]
  simp only [deriv_id, one_mul]
  ring

/-- The mixed Euler operator equals the mixed partial derivative times `x * y`. -/
private lemma appellThetaX_appellThetaY (f : ℂ → ℂ → ℂ) (x y : ℂ) :
    appellThetaX (appellThetaY f) x y = x * y * appellDx (appellDy f) x y := by
  unfold appellThetaX appellThetaY appellDx appellDy
  rw [deriv_const_mul_field]
  ring

/-- Joint analyticity identifies the reverse mixed Euler operator with the same mixed partial. -/
private lemma appellThetaY_appellThetaX {f : ℂ → ℂ → ℂ} {x y : ℂ}
    (hf : AnalyticAt ℂ (Function.uncurry f) (x, y)) :
    appellThetaY (appellThetaX f) x y = x * y * appellDx (appellDy f) x y := by
  unfold appellThetaX appellThetaY appellDx appellDy
  rw [deriv_const_mul_field]
  have h := Complex.deriv_snd_deriv_fst_comm hf
  change deriv (fun w => deriv (fun z => f z w) x) y =
    deriv (fun z => deriv (f z) y) x at h
  rw [h]
  ring

/-- An integral shift of a nonintegral complex parameter cannot vanish. -/
private lemma horn_nonint_shift_ne_zero {z : ℂ} (hz : ∀ k : ℤ, z ≠ k) (k : ℤ) :
    z + k ≠ 0 := by
  intro h
  apply hz (-k)
  push_cast
  linear_combination h

/-- Gamma recurrence gives the Horn G2 coefficient relation in the first index. -/
private lemma hornG2_coeff_recurrence_left (a a' b b' : ℂ) (ha : ∀ k : ℤ, a ≠ k)
    (hb : ∀ k : ℤ, b ≠ k)
    (hb' : ∀ k : ℤ, b' ≠ k) (m n : ℕ) :
    let c : ℕ × ℕ → ℂ := fun p =>
      Gamma (a + p.1) * Gamma (a' + p.2) * Gamma (b + p.2 - p.1) * Gamma (b' + p.1 - p.2) /
        (Gamma a * Gamma a' * Gamma b * Gamma b' * (p.1 ! * p.2 !))
    (m + 1 : ℂ) * (b + n - m - 1) * c (m + 1, n) = (a + m) * (b' + m - n) * c (m, n) := by
  dsimp only
  have ha0 : a + m ≠ 0 := by
    simpa using horn_nonint_shift_ne_zero ha (m : ℤ)
  have hb0 : b + n - m - 1 ≠ 0 := by
    convert horn_nonint_shift_ne_zero hb ((n : ℤ) - m - 1) using 1; push_cast; ring
  have hb'0 : b' + m - n ≠ 0 := by
    convert horn_nonint_shift_ne_zero hb' ((m : ℤ) - n) using 1; push_cast; ring
  have h1 := Gamma_add_one _ ha0
  have h2 := Gamma_add_one _ hb0
  have h3 := Gamma_add_one _ hb'0
  rw [show b + n - m - 1 + 1 = b + n - m by ring] at h2
  simp only [Nat.cast_add, Nat.cast_one, Nat.factorial_succ, Nat.cast_mul]
  rw [show a + (m : ℂ) + 1 = a + (m + 1) by ring] at h1
  rw [show b' + (m : ℂ) - n + 1 = b' + (m + 1) - n by ring] at h3
  rw [show b + n - ((m : ℂ) + 1) = b + n - m - 1 by ring, h1, h3, h2]
  have hm : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  field_simp [hm]

/-- Two forward gamma shifts and one backward shift give the Horn G3 first-index relation. -/
private lemma hornG3_coeff_recurrence_left (a a' : ℂ) (ha : ∀ k : ℤ, a ≠ k) (ha' : ∀ k : ℤ, a' ≠ k)
    (m n : ℕ) :
    let c : ℕ × ℕ → ℂ := fun p => Gamma (a + 2 * p.2 - p.1) * Gamma (a' + 2 * p.1 - p.2) /
      (Gamma a * Gamma a' * (p.1 ! * p.2 !))
    (m + 1 : ℂ) * (a + 2 * n - m - 1) * c (m + 1, n) =
      (a' + 2 * m - n) * (a' + 2 * m - n + 1) * c (m, n) := by
  dsimp only
  have ha0 : a + 2 * n - m - 1 ≠ 0 := by
    convert horn_nonint_shift_ne_zero ha (2 * (n : ℤ) - m - 1) using 1; push_cast; ring
  have ha'0 : a' + 2 * m - n ≠ 0 := by
    convert horn_nonint_shift_ne_zero ha' (2 * (m : ℤ) - n) using 1; push_cast; ring
  have ha'1 : a' + 2 * m - n + 1 ≠ 0 := by
    convert horn_nonint_shift_ne_zero ha' (2 * (m : ℤ) - n + 1) using 1; push_cast; ring
  have h1 := Gamma_add_one _ ha0
  have h2 := Gamma_add_one _ ha'0
  have h3 := Gamma_add_one _ ha'1
  rw [show a + 2 * n - m - 1 + 1 = a + 2 * n - m by ring] at h1
  rw [show a' + 2 * m - n + 1 + 1 = a' + 2 * ((m : ℂ) + 1) - n by ring] at h3
  simp only [Nat.cast_add, Nat.cast_one, Nat.factorial_succ, Nat.cast_mul]
  rw [show a + 2 * n - ((m : ℂ) + 1) = a + 2 * n - m - 1 by ring, h1, h3, h2]
  have hm : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  field_simp [hm]

/-- Absolute convergence on the small diamond gives a larger polydisc majorant and joint
    analyticity. -/
private lemma horn_series_local_data (c : ℕ × ℕ → ℂ)
    (hS : ∀ z w : ℂ, ‖z‖+‖w‖ < (1 / 4 : ℝ) →
      Summable (fun q => c q * z ^ q.1 * w ^ q.2)) {x y : ℂ}
    (hxy : ‖x‖+‖y‖ < (1 / 4 : ℝ)) :
    ∃ A B : ℝ, ‖x‖ < A ∧ ‖y‖ < B ∧
      Summable (fun q => ‖c q‖*A ^ q.1 * B ^ q.2) ∧
      AnalyticAt ℂ (fun p : ℂ × ℂ => ∑' q, c q * p.1 ^ q.1 * p.2 ^ q.2) (x, y) := by
  let δ := (1 / 4-‖x‖-‖y‖) / 4
  let A := ‖x‖+δ
  let B := ‖y‖+δ
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hA : ‖x‖ < A := by dsimp [A]; linarith
  have hB : ‖y‖ < B := by dsimp [B]; linarith
  have hA0 : 0 ≤ A := (norm_nonneg x).trans hA.le
  have hB0 : 0 ≤ B := (norm_nonneg y).trans hB.le
  have hAB : A + B < (1 / 4 : ℝ) := by dsimp [A, B, δ]; linarith
  have hSab := (hS A B (by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0,
      abs_of_nonneg hB0] using hAB)).norm
  have hCN : Summable (fun q => ‖c q‖*A ^ q.1 * B ^ q.2) := by
    simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hA0, abs_of_nonneg hB0] using hSab
  refine ⟨A, B, hA, hB, hCN, ?_⟩
  exact (ghaR4_double_series_hasSum_analytic c {p : ℂ × ℂ | ‖p.1‖ < A ∧ ‖p.2‖ < B}
    (fun p hp => ⟨A, B, hp.1, hp.2, hCN⟩)).2 (x, y) ⟨hA, hB⟩

/-- Horn G2 satisfies its two Euler-operator differential equations on the small diamond
`‖x‖ + ‖y‖ < 1/4`, for nonintegral parameters. -/
theorem hornG2_second_order_pde (a a' b b' : ℂ) (ha : ∀ k : ℤ, a ≠ k) (ha' : ∀ k : ℤ, a' ≠ k)
    (hb : ∀ k : ℤ, b ≠ k) (hb' : ∀ k : ℤ, b' ≠ k) {x y : ℂ}
    (hxy : ‖x‖+‖y‖ < (1 / 4 : ℝ)) :
    let f := hornG2 a a' b b'
    appellThetaX (fun x y => b * f x y + appellThetaY f x y - appellThetaX f x y) x y =
      x * (a * b' * f x y + (a + b') * appellThetaX f x y - a * appellThetaY f x y +
        appellThetaX (appellThetaX f) x y - appellThetaX (appellThetaY f) x y) ∧
    appellThetaY (fun x y => b' * f x y + appellThetaX f x y - appellThetaY f x y) x y =
      y * (a' * b * f x y + (a' + b) * appellThetaY f x y - a' * appellThetaX f x y +
        appellThetaY (appellThetaY f) x y - appellThetaX (appellThetaY f) x y) := by
  let f := hornG2 a a' b b'
  let c : ℕ × ℕ → ℂ := fun p =>
    Gamma (a + p.1) * Gamma (a' + p.2) * Gamma (b + p.2 - p.1) * Gamma (b' + p.1 - p.2) /
      (Gamma a * Gamma a' * Gamma b * Gamma b' * (p.1 ! * p.2 !))
  have hSc : ∀ z w : ℂ, ‖z‖+‖w‖ < (1 / 4 : ℝ) →
      Summable (fun q => c q * z ^ q.1 * w ^ q.2) := by
    intro z w hzw
    exact hornG2_summable a a' b b' (ghaR4_regular_of_nonint ha)
      (ghaR4_regular_of_nonint ha') hb hb' (by
        constructor <;> have := norm_nonneg z <;> have := norm_nonneg w <;> linarith)
  obtain ⟨A, B, hA, hB, hC, hf⟩ := horn_series_local_data c hSc hxy
  change AnalyticAt ℂ (Function.uncurry f) (x, y) at hf
  have hcX : ∀ m n : ℕ,
      (m + 1 : ℂ) * (m + (-1) * n + (1 - b)) * c (m + 1, n) =
        (-1) * (m + 0 * n + a) * (m + (-1) * n + b') * c (m, n) := by
    intro m n
    have h := hornG2_coeff_recurrence_left a a' b b' ha hb hb' m n
    change (m + 1 : ℂ) * (b + n - m - 1) * c (m + 1, n) = (a + m) * (b' + m - n) * c (m, n) at h
    linear_combination -h
  have hcY : ∀ m n : ℕ,
      (n + 1 : ℂ) * (n + (-1) * m + (1 - b')) * c (m, n + 1) =
        (-1) * (n + 0 * m + a') * (n + (-1) * m + b) * c (m, n) := by
    intro m n
    have h := hornG2_coeff_recurrence_left a' a b' b ha' hb' hb n m
    dsimp only at h
    have hswap : ∀ u v : ℕ,
        Gamma (a' + v) * Gamma (a + u) * Gamma (b' + u - v) * Gamma (b + v - u) /
          (Gamma a' * Gamma a * Gamma b' * Gamma b * (v ! * u !)) = c (u, v) := by
      intro u v
      dsimp only [c]
      simp only [mul_comm, mul_left_comm, mul_assoc]
    rw [hswap, hswap] at h
    linear_combination -h
  have hP := Complex.bivariateSeries_pde_x_of_coeff_recurrence hC hA hB
    (-1) 0 (-1) (-1) a b' (1 - b) hcX
  have hQ := Complex.bivariateSeries_pde_y_of_coeff_recurrence hC hA hB
    (-1) 0 (-1) (-1) a' b (1 - b') hcY
  dsimp only at hP hQ
  dsimp only
  constructor
  · rw [appellThetaX_sub (f := fun z w => b * f z w + appellThetaY f z w)
      ((analyticAt_const.mul hf).add (analyticAt_appellThetaY hf))
      (analyticAt_appellThetaX hf),
      appellThetaX_add (f := fun z w => b * f z w) (analyticAt_const.mul hf)
        (analyticAt_appellThetaY hf),
      appellThetaX_const_mul, appellThetaX_twice hf, appellThetaX_appellThetaY]
    unfold appellThetaX appellThetaY appellDx appellDy f hornG2
    dsimp only [c] at hP
    linear_combination (-x) * hP
  · rw [appellThetaY_sub (f := fun z w => b' * f z w + appellThetaX f z w)
      ((analyticAt_const.mul hf).add (analyticAt_appellThetaX hf))
      (analyticAt_appellThetaY hf),
      appellThetaY_add (f := fun z w => b' * f z w) (analyticAt_const.mul hf)
        (analyticAt_appellThetaX hf),
      appellThetaY_const_mul, appellThetaY_twice hf, appellThetaY_appellThetaX hf,
      appellThetaX_appellThetaY]
    unfold appellThetaX appellThetaY appellDx appellDy f hornG2
    dsimp only [c] at hQ
    linear_combination (-y) * hQ

/-- Horn G3 satisfies its two Euler-operator differential equations on the small diamond
`‖x‖ + ‖y‖ < 1/4`, for nonintegral parameters. -/
theorem hornG3_second_order_pde (a a' : ℂ) (ha : ∀ k : ℤ, a ≠ k) (ha' : ∀ k : ℤ, a' ≠ k)
    {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < (1 / 4 : ℝ)) :
    let g := hornG3 a a'
    appellThetaX (fun x y => a * g x y + 2 * appellThetaY g x y - appellThetaX g x y) x y =
      x * ((a' * (a' + 1)) * g x y + (4 * a' + 2) * appellThetaX g x y -
        (2 * a' + 1) * appellThetaY g x y +
        4 * appellThetaX (appellThetaX g) x y - 4 * appellThetaX (appellThetaY g) x y +
        appellThetaY (appellThetaY g) x y) ∧
    appellThetaY (fun x y => a' * g x y + 2 * appellThetaX g x y - appellThetaY g x y) x y =
      y * (a * (a + 1) * g x y + (4 * a + 2) * appellThetaY g x y - (2 * a + 1) * appellThetaX g x
          y +
        4 * appellThetaY (appellThetaY g) x y - 4 * appellThetaX (appellThetaY g) x y +
        appellThetaX (appellThetaX g) x y) := by
  let g := hornG3 a a'
  let d : ℕ × ℕ → ℂ := fun p => Gamma (a + 2 * p.2 - p.1) * Gamma (a' + 2 * p.1 - p.2) /
    (Gamma a * Gamma a' * (p.1 ! * p.2 !))
  obtain ⟨C, D, hC', hD, hE, hg⟩ := horn_series_local_data d (fun z w hzw =>
    hornG3_summable a a' ha ha' hzw) hxy
  change AnalyticAt ℂ (Function.uncurry g) (x, y) at hg
  have hdX : ∀ m n : ℕ,
      (m + 1 : ℂ) * (m + (-2) * n + (1 - a)) * d (m + 1, n) =
        (-4) * (m + (-1 / 2) * n + a' / 2) * (m + (-1 / 2) * n + (a' + 1) / 2) * d (m, n) := by
    intro m n
    have h := hornG3_coeff_recurrence_left a a' ha ha' m n
    change (m + 1 : ℂ) * (a + 2 * n - m - 1) * d (m + 1, n) =
      (a' + 2 * m - n) * (a' + 2 * m - n + 1) * d (m, n) at h
    linear_combination -h
  have hdY : ∀ m n : ℕ,
      (n + 1 : ℂ) * (n + (-2) * m + (1 - a')) * d (m, n + 1) =
        (-4) * (n + (-1 / 2) * m + a / 2) * (n + (-1 / 2) * m + (a + 1) / 2) * d (m, n) := by
    intro m n
    have h := hornG3_coeff_recurrence_left a' a ha' ha n m
    dsimp only at h
    have hswap : ∀ u v : ℕ,
        Gamma (a' + 2 * u - v) * Gamma (a + 2 * v - u) /
          (Gamma a' * Gamma a * (v ! * u !)) = d (u, v) := by
      intro u v
      dsimp only [d]
      simp only [mul_comm, mul_assoc]
    rw [hswap, hswap] at h
    linear_combination -h
  have hR := Complex.bivariateSeries_pde_x_of_coeff_recurrence hE hC' hD
    (-2) (-1 / 2) (-1 / 2) (-4) (a' / 2) ((a' + 1) / 2) (1 - a) hdX
  have hS := Complex.bivariateSeries_pde_y_of_coeff_recurrence hE hC' hD
    (-2) (-1 / 2) (-1 / 2) (-4) (a / 2) ((a + 1) / 2) (1 - a') hdY
  dsimp only at hR hS
  dsimp only
  constructor
  · rw [appellThetaX_sub (f := fun z w => a * g z w + 2 * appellThetaY g z w)
      ((analyticAt_const.mul hg).add
        ((analyticAt_const (v := (2 : ℂ))).mul (analyticAt_appellThetaY hg)))
      (analyticAt_appellThetaX hg),
      appellThetaX_add (f := fun z w => a * g z w)
        (g := fun z w => 2 * appellThetaY g z w) (analyticAt_const.mul hg)
        ((analyticAt_const (v := (2 : ℂ))).mul (analyticAt_appellThetaY hg)),
      appellThetaX_const_mul, appellThetaX_const_mul, appellThetaX_twice hg,
      appellThetaY_twice hg, appellThetaX_appellThetaY]
    unfold appellThetaX appellThetaY appellDx appellDy g hornG3
    dsimp only [d] at hR
    linear_combination (-x) * hR
  · rw [appellThetaY_sub (f := fun z w => a' * g z w + 2 * appellThetaX g z w)
      ((analyticAt_const.mul hg).add
        ((analyticAt_const (v := (2 : ℂ))).mul (analyticAt_appellThetaX hg)))
      (analyticAt_appellThetaY hg),
      appellThetaY_add (f := fun z w => a' * g z w)
        (g := fun z w => 2 * appellThetaX g z w) (analyticAt_const.mul hg)
        ((analyticAt_const (v := (2 : ℂ))).mul (analyticAt_appellThetaX hg)),
      appellThetaY_const_mul, appellThetaY_const_mul, appellThetaX_twice hg,
      appellThetaY_twice hg, appellThetaY_appellThetaX hg, appellThetaX_appellThetaY]
    unfold appellThetaX appellThetaY appellDx appellDy g hornG3
    dsimp only [d] at hS
    linear_combination (-y) * hS

/-- The Horn G2 and G3 series satisfy their paired second-order Euler-operator equations
on `‖x‖ + ‖y‖ < 1/4`, with all parameters nonintegral. -/
@[dlmf 16.14.ii]
theorem hornG2_G3_second_order_pde (a a' b b' : ℂ) (ha : ∀ k : ℤ, a ≠ k) (ha' : ∀ k : ℤ, a' ≠ k)
    (hb : ∀ k : ℤ, b ≠ k) (hb' : ∀ k : ℤ, b' ≠ k) {x y : ℂ}
    (hxy : ‖x‖+‖y‖ < (1 / 4 : ℝ)) :
    let f := hornG2 a a' b b'
    let g := hornG3 a a'
    appellThetaX (fun x y => b * f x y + appellThetaY f x y - appellThetaX f x y) x y =
      x * (a * b' * f x y + (a + b') * appellThetaX f x y - a * appellThetaY f x y +
        appellThetaX (appellThetaX f) x y - appellThetaX (appellThetaY f) x y) ∧
    appellThetaY (fun x y => b' * f x y + appellThetaX f x y - appellThetaY f x y) x y =
      y * (a' * b * f x y + (a' + b) * appellThetaY f x y - a' * appellThetaX f x y +
        appellThetaY (appellThetaY f) x y - appellThetaX (appellThetaY f) x y) ∧
    appellThetaX (fun x y => a * g x y + 2 * appellThetaY g x y - appellThetaX g x y) x y =
      x * ((a' * (a' + 1)) * g x y + (4 * a' + 2) * appellThetaX g x y -
        (2 * a' + 1) * appellThetaY g x y +
        4 * appellThetaX (appellThetaX g) x y - 4 * appellThetaX (appellThetaY g) x y +
        appellThetaY (appellThetaY g) x y) ∧
    appellThetaY (fun x y => a' * g x y + 2 * appellThetaX g x y - appellThetaY g x y) x y =
      y * (a * (a + 1) * g x y + (4 * a + 2) * appellThetaY g x y - (2 * a + 1) * appellThetaX g x
          y +
        4 * appellThetaY (appellThetaY g) x y - 4 * appellThetaX (appellThetaY g) x y +
        appellThetaX (appellThetaX g) x y) := by
  exact ⟨(hornG2_second_order_pde a a' b b' ha ha' hb hb' hxy).1,
    (hornG2_second_order_pde a a' b b' ha ha' hb hb' hxy).2,
    hornG3_second_order_pde a a' ha ha' hxy⟩

end DLMF.Hypergeometric
