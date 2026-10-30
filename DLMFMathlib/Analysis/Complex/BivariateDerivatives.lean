/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.Complex.ParametricHolomorphy

/-!
# Mixed derivatives and differential equations of bivariate power series

Mathlib's Cauchy estimate `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`
bounds mixed derivatives on smaller polydiscs. Together with locally dominated
series differentiation, it proves convergence and termwise evaluation of every
mixed derivative. Quadratic coefficient recurrences then give second order
partial differential equations, including points on the coordinate axes.
-/

@[expose] public noncomputable section

open Filter Set Metric
open scoped Topology Nat

namespace Complex


/-- A term of a mixed partial derivative of a bivariate monomial series. -/
def bivariateSeriesDerivTerm (c : ℕ × ℕ → ℂ) (i j : ℕ) (x y : ℂ) (q : ℕ × ℕ) : ℂ :=
  c q * (q.1.descFactorial i : ℂ) * (q.2.descFactorial j : ℂ) * x ^ (q.1 - i) * y ^ (q.2 - j)

/-- Mixed derivatives of a bivariate monomial have falling-factorial coefficients. -/
private lemma iteratedDeriv_monomial_mul_eq (c : ℂ) (m n i j : ℕ) (x y : ℂ) :
    iteratedDeriv i (fun z => iteratedDeriv j (fun w => c * z ^ m * w ^ n) y) x =
      c * (m.descFactorial i : ℂ) * (n.descFactorial j : ℂ) * x ^ (m - i) * y ^ (n - j) := by
  have heq : (fun z => iteratedDeriv j (fun w => c * z ^ m * w ^ n) y) =
      (fun z => (c * z ^ m) * ((n.descFactorial j : ℂ) * y ^ (n - j))) := by
    funext z
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
  rw [heq, iteratedDeriv_mul_const_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_pow]
  ring

/-- Cauchy's estimate bounds a partial derivative uniformly on a polydisc. -/
private lemma norm_iteratedDeriv_monomial_le {c x y : ℂ} {A B : ℝ} (hx : ‖x‖ ≤ A) (hy : ‖y‖ < B)
    (m n j : ℕ) :
    ‖iteratedDeriv j (fun w => c * x ^ m * w ^ n) y‖ ≤
      j.factorial * (‖c‖ * A ^ m * B ^ n)/((B - ‖y‖)/2) ^ j := by
  have hA : 0 ≤ A := (norm_nonneg x).trans hx
  have hr : 0 < (B - ‖y‖)/2 := by linarith
  apply norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hr
  · apply DifferentiableOn.diffContOnCl
    fun_prop
  · intro w hw
    have hwB : ‖w‖ ≤ B := by
      have hwy : dist w y = (B - ‖y‖)/2 := mem_sphere.mp hw
      have := norm_le_of_mem_closedBall (show w ∈ closedBall y ((B - ‖y‖)/2) from
        sphere_subset_closedBall hw)
      linarith
    simp only [norm_mul, norm_pow]
    gcongr

/-- Applying Cauchy's estimate twice bounds every mixed derivative of a bivariate monomial. -/
private lemma norm_mixed_iteratedDeriv_monomial_le {c x y : ℂ} {A B : ℝ}
    (hx : ‖x‖ < A) (hy : ‖y‖ < B) (m n i j : ℕ) :
    ‖iteratedDeriv i (fun z => iteratedDeriv j (fun w => c * z ^ m * w ^ n) y) x‖ ≤
      i.factorial * (j.factorial * (‖c‖ * A ^ m * B ^ n)/((B - ‖y‖)/2) ^ j)/((A - ‖x‖)/2) ^ i := by
  have hr : 0 < (A - ‖x‖)/2 := by linarith
  apply norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le i hr
  · apply DifferentiableOn.diffContOnCl
    simp_rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
    fun_prop
  · intro z hz
    have hzA : ‖z‖ ≤ A := by
      have := norm_le_of_mem_closedBall (show z ∈ closedBall x ((A - ‖x‖)/2) from
        sphere_subset_closedBall hz)
      linarith
    exact norm_iteratedDeriv_monomial_le hzA hy m n j

/-- The mixed derivative terms of a normally convergent bivariate series are summable
at every interior point of its convergence polydisc. -/
lemma summable_bivariateSeriesDerivTerm {c : ℕ × ℕ → ℂ} {A B : ℝ}
    (hc : Summable (fun q => ‖c q‖ * A ^ q.1 * B ^ q.2)) {x y : ℂ}
    (hx : ‖x‖ < A) (hy : ‖y‖ < B) (i j : ℕ) :
    Summable (bivariateSeriesDerivTerm c i j x y) := by
  have hsum := ((((hc.mul_left (j.factorial : ℝ)).div_const (((B - ‖y‖)/2) ^ j)).mul_left
    (i.factorial : ℝ)).div_const (((A - ‖x‖)/2) ^ i))
  refine Summable.of_norm_bounded hsum fun q => ?_
  have h := norm_mixed_iteratedDeriv_monomial_le (c := c q) hx hy q.1 q.2 i j
  rw [iteratedDeriv_monomial_mul_eq] at h
  simpa only [bivariateSeriesDerivTerm, mul_assoc] using h

/-- Every mixed partial derivative of a normally convergent bivariate series is
the sum of its termwise mixed derivatives. -/
lemma iteratedDeriv_bivariateSeries_eq_tsum {c : ℕ × ℕ → ℂ} {A B : ℝ}
    (hc : Summable (fun q => ‖c q‖ * A ^ q.1 * B ^ q.2)) {x y : ℂ}
    (hx : ‖x‖ < A) (hy : ‖y‖ < B) (i j : ℕ) :
    iteratedDeriv i (fun z => iteratedDeriv j
      (fun w => ∑' q : ℕ × ℕ, c q * z ^ q.1 * w ^ q.2) y) x =
      ∑' q : ℕ × ℕ, bivariateSeriesDerivTerm c i j x y q := by
  have hA : 0 ≤ A := (norm_nonneg x).trans hx.le
  have hB : 0 ≤ B := (norm_nonneg y).trans hy.le
  have hinner : ∀ z ∈ ball (0 : ℂ) A,
      iteratedDeriv j (fun w => ∑' q : ℕ × ℕ, c q * z ^ q.1 * w ^ q.2) y =
        ∑' q : ℕ × ℕ, iteratedDeriv j (fun w => c q * z ^ q.1 * w ^ q.2) y := by
    intro z hz
    have hdom : ∀ w ∈ ball (0 : ℂ) B, ∃ V ∈ 𝓝 w, ∃ g : ℕ × ℕ → ℝ,
        Summable g ∧ ∀ q, ∀ t ∈ V, ‖c q * z ^ q.1 * t ^ q.2‖ ≤ g q := by
      intro w hw
      refine ⟨ball 0 B, isOpen_ball.mem_nhds hw, _, hc, fun q t ht => ?_⟩
      rw [mem_ball_zero_iff] at hz ht
      simp only [norm_mul, norm_pow]
      gcongr
    exact iteratedDeriv_tsum_of_locally_dominated isOpen_ball (fun q => by fun_prop)
      hdom j (mem_ball_zero_iff.mpr hy)
  have heq : (fun z => iteratedDeriv j
      (fun w => ∑' q : ℕ × ℕ, c q * z ^ q.1 * w ^ q.2) y) =ᶠ[𝓝 x]
      (fun z => ∑' q : ℕ × ℕ, iteratedDeriv j (fun w => c q * z ^ q.1 * w ^ q.2) y) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hx)]
      with z hz using hinner z hz
  rw [heq.iteratedDeriv_eq i]
  have hdom : ∀ z ∈ ball (0 : ℂ) A, ∃ V ∈ 𝓝 z, ∃ g : ℕ × ℕ → ℝ,
      Summable g ∧ ∀ q, ∀ t ∈ V,
        ‖iteratedDeriv j (fun w => c q * t ^ q.1 * w ^ q.2) y‖ ≤ g q := by
    intro z hz
    refine ⟨ball 0 A, isOpen_ball.mem_nhds hz, _,
      (hc.mul_left (j.factorial : ℝ)).div_const (((B - ‖y‖)/2) ^ j), fun q t ht => ?_⟩
    exact norm_iteratedDeriv_monomial_le (mem_ball_zero_iff.mp ht).le hy q.1 q.2 j
  rw [iteratedDeriv_tsum_of_locally_dominated isOpen_ball (fun q => ?_) hdom i
    (mem_ball_zero_iff.mpr hx)]
  · exact tsum_congr fun q => iteratedDeriv_monomial_mul_eq (c q) q.1 q.2 i j x y
  · simp_rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
    fun_prop
/-- Coordinate polynomials applied to monomial derivatives give the two factors
in a quadratic coefficient recurrence. -/
private lemma pde_term_algebra (C x y κ α β a b γ : ℂ) (m n : ℕ) :
    let T : ℕ → ℕ → ℂ := fun i j =>
      C * (m.descFactorial i : ℂ) * (n.descFactorial j : ℂ) * x ^ (m - i) * y ^ (n - j)
    (x * T 2 0 + κ * y * T 1 1 + γ * T 1 0 =
      C * m * (m + κ * n + γ - 1) * x ^ (m - 1) * y ^ n) ∧
    (x ^ 2 * T 2 0 + (α + β) * x * y * T 1 1 + α * β * y ^ 2 * T 0 2 + (a + b + 1) * x * T 1 0 +
      (a * β + b * α + α * β) * y * T 0 1 + a * b * T 0 0 =
      C * (m + α * n + a) * (m + β * n + b) * x ^ m * y ^ n) := by
  dsimp only
  rcases m with _ | (_ | m) <;> rcases n with _ | (_ | n) <;> constructor <;>
    simp [Nat.descFactorial_succ, pow_succ] <;> ring

/-- A first-index coefficient recurrence gives the corresponding identity
between sums of derivative terms. -/
private lemma bivariateSeries_pde_terms {c : ℕ × ℕ → ℂ} {A B : ℝ}
    (hc : Summable (fun q => ‖c q‖ * A ^ q.1 * B ^ q.2)) {x y : ℂ}
    (hx : ‖x‖ < A) (hy : ‖y‖ < B) (κ α β ρ a b γ : ℂ)
    (hrec : ∀ m n : ℕ,
      (m + 1 : ℂ) * (m + κ * n + γ) * c (m + 1, n) =
        ρ * (m + α * n + a) * (m + β * n + b) * c (m, n)) :
    let D : ℕ → ℕ → ℂ := fun i j => ∑' q : ℕ × ℕ, bivariateSeriesDerivTerm c i j x y q
    x * (1 - ρ * x) * D 2 0 + y * (κ - ρ * (α + β) * x) * D 1 1 - ρ * α * β * y ^ 2 * D 0 2 +
      (γ - ρ * (a + b + 1) * x) * D 1 0 -
      ρ * (a * β + b * α + α * β) * y * D 0 1 - ρ * a * b * D 0 0 = 0 := by
  let D : ℕ → ℕ → ℂ := fun i j => ∑' q : ℕ × ℕ, bivariateSeriesDerivTerm c i j x y q
  change x * (1 - ρ * x) * D 2 0 + y * (κ - ρ * (α + β) * x) * D 1 1 - ρ * α * β * y ^ 2 * D 0 2 +
    (γ - ρ * (a + b + 1) * x) * D 1 0 -
      ρ * (a * β + b * α + α * β) * y * D 0 1 - ρ * a * b * D 0 0 = 0
  let L : ℕ × ℕ → ℂ := fun q =>
    c q * q.1 * (q.1 + κ * q.2 + γ - 1) * x ^ (q.1 - 1) * y ^ q.2
  let N : ℕ × ℕ → ℂ := fun q => c q * (q.1 + α * q.2 + a) * (q.1 + β * q.2 + b) * x ^ q.1 * y ^ q.2
  have hs (i j : ℕ) := summable_bivariateSeriesDerivTerm hc hx hy i j
  have hL : HasSum L (x * D 2 0 + κ * y * D 1 1 + γ * D 1 0) := by
    have ht := (((hs 2 0).hasSum.mul_left x).add
      ((hs 1 1).hasSum.mul_left (κ * y))).add ((hs 1 0).hasSum.mul_left γ)
    refine ht.congr_fun fun q => ?_
    simpa only [L, bivariateSeriesDerivTerm] using
      (pde_term_algebra (c q) x y κ α β a b γ q.1 q.2).1.symm
  have hN : HasSum N (x ^ 2 * D 2 0 + (α + β) * x * y * D 1 1 + α * β * y ^ 2 * D 0 2 +
      (a + b + 1) * x * D 1 0 + (a * β + b * α + α * β) * y * D 0 1 + a * b * D 0 0) := by
    have ht := (((((hs 2 0).hasSum.mul_left (x ^ 2)).add
      ((hs 1 1).hasSum.mul_left ((α + β) * x * y))).add
      ((hs 0 2).hasSum.mul_left (α * β * y ^ 2))).add
      ((hs 1 0).hasSum.mul_left ((a + b + 1) * x))).add
      ((hs 0 1).hasSum.mul_left ((a * β + b * α + α * β) * y)) |>.add
      ((hs 0 0).hasSum.mul_left (a * b))
    refine ht.congr_fun fun q => ?_
    simpa only [N, bivariateSeriesDerivTerm] using
      (pde_term_algebra (c q) x y κ α β a b γ q.1 q.2).2.symm
  let g : ℕ × ℕ → ℕ × ℕ := fun q => (q.1 + 1, q.2)
  have hg : Function.Injective g := by
    rintro ⟨m, n⟩ ⟨m', n'⟩ he
    simp only [g, Prod.mk.injEq] at he ⊢
    omega
  have hsupport : Function.support L ⊆ Set.range g := by
    rintro ⟨m, n⟩ hmn
    cases m with
    | zero => simp [Function.mem_support, L] at hmn
    | succ m => exact ⟨(m, n), rfl⟩
  have hLN : x * D 2 0 + κ * y * D 1 1 + γ * D 1 0 =
      ρ * (x ^ 2 * D 2 0 + (α + β) * x * y * D 1 1 + α * β * y ^ 2 * D 0 2 +
        (a + b + 1) * x * D 1 0 + (a * β + b * α + α * β) * y * D 0 1 + a * b * D 0 0) := by
    rw [← hL.tsum_eq, ← hN.tsum_eq, ← hg.tsum_eq hsupport, ←tsum_mul_left]
    apply tsum_congr
    intro q
    dsimp only [L, N, g]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    linear_combination (x ^ q.1 * y ^ q.2) * (hrec q.1 q.2)
  linear_combination hLN

/-- Swapping the coefficient indices and coordinates exchanges the mixed derivative orders. -/
private lemma tsum_bivariateSeriesDerivTerm_swap (c : ℕ × ℕ → ℂ) (i j : ℕ) (x y : ℂ) :
    (∑' q : ℕ × ℕ, bivariateSeriesDerivTerm (fun p => c (p.2, p.1)) i j y x q) =
      ∑' q : ℕ × ℕ, bivariateSeriesDerivTerm c j i x y q := by
  rw [←(Equiv.prodComm ℕ ℕ).tsum_eq]
  apply tsum_congr
  rintro ⟨m, n⟩
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, bivariateSeriesDerivTerm]
  ring

/-- A second-index coefficient recurrence gives the symmetric identity
between sums of derivative terms. -/
private lemma bivariateSeries_pde_y_terms {c : ℕ × ℕ → ℂ} {A B : ℝ}
    (hc : Summable (fun q => ‖c q‖ * A ^ q.1 * B ^ q.2)) {x y : ℂ}
    (hx : ‖x‖ < A) (hy : ‖y‖ < B) (κ α β ρ a b γ : ℂ)
    (hrec : ∀ m n : ℕ,
      (n + 1 : ℂ) * (n + κ * m + γ) * c (m, n + 1) =
        ρ * (n + α * m + a) * (n + β * m + b) * c (m, n)) :
    let D : ℕ → ℕ → ℂ := fun i j => ∑' q : ℕ × ℕ, bivariateSeriesDerivTerm c i j x y q
    y * (1 - ρ * y) * D 0 2 + x * (κ - ρ * (α + β) * y) * D 1 1 - ρ * α * β * x ^ 2 * D 2 0 +
      (γ - ρ * (a + b + 1) * y) * D 0 1 -
      ρ * (a * β + b * α + α * β) * x * D 1 0 - ρ * a * b * D 0 0 = 0 := by
  have hc' : Summable (fun q : ℕ × ℕ => ‖c (q.2, q.1)‖ * B ^ q.1 * A ^ q.2) := by
    have h := hc.comp_injective (Equiv.prodComm ℕ ℕ).injective
    convert h using 1
    ext q
    rcases q with ⟨m, n⟩
    simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.swap_prod_mk]
    ring
  have h := bivariateSeries_pde_terms (c := fun q => c (q.2, q.1)) hc' hy hx κ α β ρ a b γ
    (fun m n => hrec n m)
  dsimp only at h ⊢
  simpa only [tsum_bivariateSeriesDerivTerm_swap] using h

/-- A quadratic recurrence in the first coefficient index yields a second order
differential equation throughout the convergence polydisc. -/
lemma bivariateSeries_pde_x_of_coeff_recurrence {c : ℕ × ℕ → ℂ} {A B : ℝ}
    (hc : Summable (fun q => ‖c q‖ * A ^ q.1 * B ^ q.2)) {x y : ℂ}
    (hx : ‖x‖ < A) (hy : ‖y‖ < B) (κ α β ρ a b γ : ℂ)
    (hrec : ∀ m n : ℕ,
      (m + 1 : ℂ) * (m + κ * n + γ) * c (m + 1, n) =
        ρ * (m + α * n + a) * (m + β * n + b) * c (m, n)) :
    let F : ℂ → ℂ → ℂ := fun z w => ∑' q : ℕ × ℕ, c q * z ^ q.1 * w ^ q.2
    x * (1 - ρ * x) * deriv (deriv (fun z => F z y)) x +
      y * (κ - ρ * (α + β) * x) * deriv (fun z => deriv (F z) y) x -
      ρ * α * β * y ^ 2 * deriv (deriv (F x)) y +
      (γ - ρ * (a + b + 1) * x) * deriv (fun z => F z y) x -
      ρ * (a * β + b * α + α * β) * y * deriv (F x) y - ρ * a * b * F x y = 0 := by
  have h := bivariateSeries_pde_terms hc hx hy κ α β ρ a b γ hrec
  have hD (i j : ℕ) := iteratedDeriv_bivariateSeries_eq_tsum hc hx hy i j
  dsimp only at h ⊢
  rw [← hD 2 0, ← hD 1 1, ← hD 0 2, ← hD 1 0, ← hD 0 1, ← hD 0 0] at h
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h

/-- A quadratic recurrence in the second coefficient index yields the second-variable
equation, with an outer first-variable derivative in the mixed term. -/
lemma bivariateSeries_pde_y_of_coeff_recurrence {c : ℕ × ℕ → ℂ} {A B : ℝ}
    (hc : Summable (fun q => ‖c q‖ * A ^ q.1 * B ^ q.2)) {x y : ℂ}
    (hx : ‖x‖ < A) (hy : ‖y‖ < B) (κ α β ρ a b γ : ℂ)
    (hrec : ∀ m n : ℕ,
      (n + 1 : ℂ) * (n + κ * m + γ) * c (m, n + 1) =
        ρ * (n + α * m + a) * (n + β * m + b) * c (m, n)) :
    let F : ℂ → ℂ → ℂ := fun z w => ∑' q : ℕ × ℕ, c q * z ^ q.1 * w ^ q.2
    y * (1 - ρ * y) * deriv (deriv (F x)) y +
      x * (κ - ρ * (α + β) * y) * deriv (fun z => deriv (F z) y) x -
      ρ * α * β * x ^ 2 * deriv (deriv (fun z => F z y)) x +
      (γ - ρ * (a + b + 1) * y) * deriv (F x) y -
      ρ * (a * β + b * α + α * β) * x * deriv (fun z => F z y) x - ρ * a * b * F x y = 0 := by
  have h := bivariateSeries_pde_y_terms hc hx hy κ α β ρ a b γ hrec
  have hD (i j : ℕ) := iteratedDeriv_bivariateSeries_eq_tsum hc hx hy i j
  dsimp only at h ⊢
  rw [← hD 2 0, ← hD 1 1, ← hD 0 2, ← hD 1 0, ← hD 0 1, ← hD 0 0] at h
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h


end Complex
