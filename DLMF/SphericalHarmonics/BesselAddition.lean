/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Series

/-!
# Gegenbauer's addition theorem for Bessel functions (DLMF 10.23.8)

For complex `ν` with `Re ν > 0`, positive radii `r, ρ` and `w² = r² + ρ² - 2rρ cos φ > 0`,

$$
\frac{J_ν(w)}{w^ν} = \frac{2^ν Γ(ν)}{(rρ)^ν}
  \sum_{n=0}^∞ (ν+n) J_{ν+n}(r) J_{ν+n}(ρ) C^{(ν)}_n(\cos φ).
$$

The proof is by power series and works directly at complex `ν`. Write `F_c = ₀F̃₁(;c;·)`, so
that `J_ν(w)/w^ν = 2^{-ν} F_{ν+1}(x + y + z)` with `x = -r²/4`, `y = -ρ²/4`, `z = rρ cos φ / 2`.

* Taylor's theorem for the entire function `F_{ν+1}` gives `F_{ν+1}(s + z) = ∑ zᵏ/k! F_{ν+1+k}(s)`
  (`shBes_hasSum_shift`).
* Each `(2t)ᵏ` is expanded in Gegenbauer polynomials (`monomial_ultrasphPoly_expansion`, DLMF
  18.18.17), and the absolutely convergent double series is regrouped by the Gegenbauer degree
  (`shBes_equiv`, `shBes_norm_ultrasph_le`, `shBes_norm_F_le`).
* The inner sums are identified by the product formula
  `F_c(x) F_c(y) = ∑ₗ (xy)ˡ/(l! Γ(c+l)) F_{c+2l}(x+y)` (`shBes_hasSum_product`), itself proved from
  the Taylor shift and a finite identity obtained from the contiguous relation of `₀F₁`
  (`shBes_sum_choose`, a Chu–Vandermonde sum in disguise).

The theorem `besselJ_addition` was moved here verbatim from `DLMF/Bessel/Theorems.lean`, since the
Gegenbauer polynomial API it needs lives in modules that import that file.
-/

@[expose] public section

open Complex
open scoped Real Nat Topology
open DLMF.OrthogonalPolynomials
open DLMF.Hypergeometric
open DLMF.Confluent

noncomputable section

namespace DLMF.Bessel

/-- Iterated derivatives of regularized `₀F₁` raise the parameter. -/
theorem shBes_iteratedDeriv (c : ℂ) (k : ℕ) :
    iteratedDeriv k (regularizedHGFun (∅ : Multiset ℂ) {c}) =
      regularizedHGFun (∅ : Multiset ℂ) {c + k} := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    rw [deriv_regularized0F1]
    congr 2
    push_cast
    ring

/-- Taylor shift of regularized `₀F₁`: `F_c(s + z) = ∑ zᵏ/k! F_{c+k}(s)`. -/
theorem shBes_hasSum_shift (c s z : ℂ) :
    HasSum (fun k : ℕ => z ^ k / k ! * regularizedHGFun (∅ : Multiset ℂ) {c + k} s)
      (regularizedHGFun (∅ : Multiset ℂ) {c} (s + z)) := by
  have hf : Differentiable ℂ (regularizedHGFun (∅ : Multiset ℂ) {c}) :=
    fun w => (analyticAt_regularized0F1 c w).differentiableAt
  have h := Complex.hasSum_taylorSeries_of_entire hf s (s + z)
  simp only [add_sub_cancel_left, shBes_iteratedDeriv, smul_eq_mul] at h
  convert h using 2 with k
  ring

/-- The power series of regularized `₀F₁`. -/
theorem shBes_hasSum_series (c w : ℂ) :
    HasSum (fun m : ℕ => w ^ m / (m ! * Gamma (c + m)))
      (regularizedHGFun (∅ : Multiset ℂ) {c} w) := by
  have h := (hasFPowerSeriesOnBall_regularized0F1 c).hasSum_mul_pow (z := w) (by simp)
  simp only [regularizedHGFunCoeff_empty] at h
  convert h using 2 with m
  ring

/-- `‖Γ(c + N)⁻¹‖ ≤ ‖Γ(c)⁻¹‖ / N!` for `1 ≤ Re c`. -/
theorem shBes_norm_recip_Gamma_add_nat {c : ℂ} (hc : 1 ≤ c.re) (N : ℕ) :
    ‖(Gamma (c + N))⁻¹‖ ≤ ‖(Gamma c)⁻¹‖ / N ! := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hne : c + N ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have hge : (N + 1 : ℝ) ≤ ‖c + N‖ := by
      have := Complex.re_le_norm (c + N)
      simp at this
      linarith
    rw [show c + ((N + 1 : ℕ) : ℂ) = (c + N) + 1 by push_cast; ring, Gamma_add_one _ hne,
      mul_inv, norm_mul, norm_inv, Nat.factorial_succ, Nat.cast_mul]
    have hp : (0 : ℝ) < ‖c + N‖ := norm_pos_iff.mpr hne
    calc ‖c + N‖⁻¹ * ‖(Gamma (c + N))⁻¹‖ ≤ (N + 1 : ℝ)⁻¹ * (‖(Gamma c)⁻¹‖ / N !) := by
          gcongr
      _ = _ := by push_cast; field_simp

/-- `N! ≤ ‖(c)_N‖` for `1 ≤ Re c`. -/
theorem shBes_factorial_le_norm_poch {c : ℂ} (hc : 1 ≤ c.re) (N : ℕ) :
    (N ! : ℝ) ≤ ‖poch c N‖ := by
  induction N with
  | zero => simp [poch_zero]
  | succ N ih =>
    have hge : (N + 1 : ℝ) ≤ ‖c + N‖ := by
      have := Complex.re_le_norm (c + N)
      simp at this
      linarith
    rw [poch_succ, norm_mul, Nat.factorial_succ, Nat.cast_mul, mul_comm]
    push_cast
    gcongr

/-- `‖(ν)_k‖ ≤ k! (1 + ‖ν‖)^k`. -/
theorem shBes_norm_poch_le (ν : ℂ) (k : ℕ) :
    ‖poch ν k‖ ≤ k ! * (1 + ‖ν‖) ^ k := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    rw [poch_succ, norm_mul, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have h1 : ‖ν + k‖ ≤ (k + 1) * (1 + ‖ν‖) := by
      calc ‖ν + k‖ ≤ ‖ν‖ + k := by
            refine (norm_add_le _ _).trans ?_
            simp
        _ ≤ _ := by nlinarith [norm_nonneg ν, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    calc ‖poch ν k‖ * ‖ν + k‖ ≤ (k ! * (1 + ‖ν‖) ^ k) * ((k + 1) * (1 + ‖ν‖)) := by
          gcongr
      _ = _ := by push_cast; ring

/-- Bound for shifted regularized `₀F₁`: `‖F_{c+k}(s)‖ ≤ ‖Γ(c)⁻¹‖ E(‖s‖) / k!`. -/
theorem shBes_norm_F_le {c : ℂ} (hc : 1 ≤ c.re) (k : ℕ) (s : ℂ) :
    ‖regularizedHGFun (∅ : Multiset ℂ) {c + k} s‖ ≤
      ‖(Gamma c)⁻¹‖ * (∑' m : ℕ, ‖s‖ ^ m / m !) / k ! := by
  have hs := shBes_hasSum_series (c + k) s
  have hE := (Real.summable_pow_div_factorial ‖s‖).hasSum.mul_left (‖(Gamma c)⁻¹‖ / k !)
  rw [show ‖(Gamma c)⁻¹‖ * (∑' m : ℕ, ‖s‖ ^ m / m !) / (k ! : ℝ) =
    ‖(Gamma c)⁻¹‖ / (k ! : ℝ) * ∑' m : ℕ, ‖s‖ ^ m / (m ! : ℝ) by ring]
  refine hs.norm_le_of_bounded hE fun m => ?_
  have hG := shBes_norm_recip_Gamma_add_nat hc (k + m)
  have hfac : ((k ! : ℝ) * m !) ≤ (k + m) ! := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _)
      (Nat.factorial_mul_factorial_dvd_factorial_add k m)
  rw [norm_div, norm_mul, norm_pow, div_eq_mul_inv, mul_inv, Complex.norm_natCast]
  rw [show c + k + m = c + ((k + m : ℕ) : ℂ) by push_cast; ring]
  have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have hm : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
  rw [← norm_inv]
  calc ‖s‖ ^ m * ((m ! : ℝ)⁻¹ * ‖(Gamma (c + ((k + m : ℕ) : ℂ)))⁻¹‖)
      ≤ ‖s‖ ^ m * ((m ! : ℝ)⁻¹ * (‖(Gamma c)⁻¹‖ / (k + m) !)) := by gcongr
    _ ≤ ‖s‖ ^ m * ((m ! : ℝ)⁻¹ * (‖(Gamma c)⁻¹‖ / (k ! * m !))) := by
        gcongr
    _ ≤ ‖s‖ ^ m * (1 * (‖(Gamma c)⁻¹‖ / (k ! * m !))) := by
        gcongr
        exact inv_le_one_of_one_le₀
          (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m))
    _ = _ := by field_simp

/-- The contiguous relation for the shifted family `m ↦ F_{c+m}(x)`. -/
theorem shBes_contiguous (c x : ℂ) (m : ℕ) :
    regularizedHGFun (∅ : Multiset ℂ) {c + m} x =
      (c + m) * regularizedHGFun (∅ : Multiset ℂ) {c + ((m + 1 : ℕ) : ℂ)} x +
        x * regularizedHGFun (∅ : Multiset ℂ) {c + ((m + 2 : ℕ) : ℂ)} x := by
  rw [regularized0F1_contiguous (c + m) x]
  congr 4 <;> push_cast <;> ring

/-- A finite identity behind the product formula for regularized `₀F₁`:
`∑ₗ C(j,l) xˡ Γ(c+l)⁻¹ F_{c+l+j}(x) = Γ(c+j)⁻¹ F_c(x)`. -/
theorem shBes_sum_choose {c : ℂ} (hc : 0 < c.re) (x : ℂ) (j : ℕ) :
    ∑ l ∈ Finset.range (j + 1), (j.choose l : ℂ) * x ^ l * (Gamma (c + l))⁻¹ *
        regularizedHGFun (∅ : Multiset ℂ) {c + ((l + j : ℕ) : ℂ)} x =
      regularizedHGFun (∅ : Multiset ℂ) {c} x * (Gamma (c + j))⁻¹ := by
  set F : ℕ → ℂ := fun m => regularizedHGFun (∅ : Multiset ℂ) {c + m} x with hF
  set g : ℕ → ℂ := fun m => (Gamma (c + m))⁻¹ with hg
  have hgrec (m : ℕ) : g m = (c + m) * g (m + 1) := by
    simp only [hg]
    rw [one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c + m)]
    push_cast; ring_nf
  have hcj (m : ℕ) : c + m ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  let A : ℕ → ℂ := fun j => ∑ l ∈ Finset.range (j + 1), (j.choose l : ℂ) * x ^ l * g l * F (l + j)
  have hstep (j : ℕ) : A j = (c + j) * A (j + 1) := by
    let P : ℕ → ℂ := fun l => x ^ l * g l * F (l + j + 1)
    have h1 : A j = (c + j) * P 0 + ∑ l ∈ Finset.range (j + 1),
        ((j.choose (l + 1) : ℂ) * (c + (l + 1) + j) + (j.choose l : ℂ) * (c + l)) * P (l + 1) := by
      have hexp : A j = ∑ l ∈ Finset.range (j + 1), (j.choose l : ℂ) * (c + l + j) * P l +
          ∑ l ∈ Finset.range (j + 1), (j.choose l : ℂ) * (c + l) * P (l + 1) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        have hc' := shBes_contiguous c x (l + j)
        simp only [P, F]
        rw [hc', hgrec l]
        push_cast
        ring_nf
      have hext : ∑ k ∈ Finset.range j, (j.choose (k + 1) : ℂ) * (c + ((k + 1 : ℕ) : ℂ) + j) *
          P (k + 1) = ∑ k ∈ Finset.range (j + 1), (j.choose (k + 1) : ℂ) * (c + ((k : ℂ) + 1) + j) *
          P (k + 1) := by
        rw [Finset.sum_range_succ, Nat.choose_succ_self]
        push_cast
        simp
      rw [hexp, Finset.sum_range_succ' (fun l => (j.choose l : ℂ) * (c + l + j) * P l), hext]
      simp only [add_mul, Finset.sum_add_distrib, Nat.choose_zero_right]
      push_cast
      ring
    have h2 : (c + j) * A (j + 1) = (c + j) * P 0 + ∑ l ∈ Finset.range (j + 1),
        (((j.choose l : ℂ) + j.choose (l + 1)) * (c + j)) * P (l + 1) := by
      simp only [A]
      rw [Finset.mul_sum, Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, zero_add,
        Nat.choose_succ_succ, Nat.cast_add]
      rw [add_comm]
      congr 1
      · simp only [P]; ring_nf
      · refine Finset.sum_congr rfl fun l _ => ?_
        simp only [P]
        rw [show l + 1 + (j + 1) = l + 1 + j + 1 by ring]
        ring
    rw [h1, h2]
    congr 1
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hch := Nat.choose_succ_right_eq j l
    have hch' : (j.choose (l + 1) : ℂ) * (l + 1) = (j.choose l : ℂ) * ((j : ℂ) - l) := by
      rw [← Nat.cast_sub hl']
      exact_mod_cast hch
    linear_combination P (l + 1) * hch'
  have hmain : ∀ j, A j = F 0 * g j := by
    intro j
    induction j with
    | zero => simp [A, F, g, mul_comm]
    | succ j ih =>
      have h := hstep j
      rw [ih, hgrec j] at h
      exact mul_left_cancel₀ (hcj j) (by linear_combination -h)
  have := hmain j
  simp only [A, F, g, Nat.cast_zero, add_zero] at this
  exact this

/-- Product formula for regularized `₀F₁`:
`F_c(x) F_c(y) = ∑ₗ (xy)ˡ / (l! Γ(c+l)) F_{c+2l}(x+y)`. -/
theorem shBes_hasSum_product {c : ℂ} (hc : 1 ≤ c.re) (x y : ℂ) :
    HasSum (fun l : ℕ => (x * y) ^ l / l ! * (Gamma (c + l))⁻¹ *
        regularizedHGFun (∅ : Multiset ℂ) {c + ((2 * l : ℕ) : ℂ)} (x + y))
      (regularizedHGFun (∅ : Multiset ℂ) {c} x * regularizedHGFun (∅ : Multiset ℂ) {c} y) := by
  set T : ℕ × ℕ → ℂ := fun p => (x * y) ^ p.1 / p.1 ! * (Gamma (c + p.1))⁻¹ *
    (y ^ p.2 / p.2 ! * regularizedHGFun (∅ : Multiset ℂ) {c + ((2 * p.1 + p.2 : ℕ) : ℂ)} x) with hT
  have hrow (l : ℕ) : HasSum (fun b => T (l, b)) ((x * y) ^ l / l ! * (Gamma (c + l))⁻¹ *
      regularizedHGFun (∅ : Multiset ℂ) {c + ((2 * l : ℕ) : ℂ)} (x + y)) := by
    have h := (shBes_hasSum_shift (c + ((2 * l : ℕ) : ℂ)) x y).mul_left
      ((x * y) ^ l / l ! * (Gamma (c + l))⁻¹)
    convert h using 2 with b
    simp only [hT]
    push_cast
    ring_nf
  set E : ℝ := ∑' m : ℕ, ‖x‖ ^ m / (m ! : ℝ)
  set K : ℝ := ‖(Gamma c)⁻¹‖ * (‖(Gamma c)⁻¹‖ * E)
  have hE : 0 ≤ E := tsum_nonneg fun m => by positivity
  have hsum : Summable T := by
    have hu := Real.summable_pow_div_factorial (‖x‖ * ‖y‖)
    have hv := Real.summable_pow_div_factorial (‖y‖)
    have huv := (hu.mul_of_nonneg hv (fun _ => by positivity) (fun _ => by positivity)).mul_left K
    refine Summable.of_norm_bounded huv fun p => ?_
    have h1 := shBes_norm_recip_Gamma_add_nat hc p.1
    have h2 := shBes_norm_F_le hc (2 * p.1 + p.2) x
    have hf1 : (1 : ℝ) ≤ p.1 ! := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hf2 : (1 : ℝ) ≤ (2 * p.1 + p.2) ! := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h1' : ‖(Gamma (c + p.1))⁻¹‖ ≤ ‖(Gamma c)⁻¹‖ :=
      h1.trans (div_le_self (norm_nonneg _) hf1)
    have h2' : ‖regularizedHGFun (∅ : Multiset ℂ) {c + ((2 * p.1 + p.2 : ℕ) : ℂ)} x‖ ≤
        ‖(Gamma c)⁻¹‖ * E := h2.trans (div_le_self (by positivity) hf2)
    simp only [hT, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    calc (‖x‖ * ‖y‖) ^ p.1 / p.1 ! * ‖(Gamma (c + p.1))⁻¹‖ *
          (‖y‖ ^ p.2 / p.2 ! *
            ‖regularizedHGFun (∅ : Multiset ℂ) {c + ((2 * p.1 + p.2 : ℕ) : ℂ)} x‖)
        ≤ (‖x‖ * ‖y‖) ^ p.1 / p.1 ! * ‖(Gamma c)⁻¹‖ *
            (‖y‖ ^ p.2 / p.2 ! * (‖(Gamma c)⁻¹‖ * E)) := by
          gcongr
      _ = _ := by ring
  have hA := hsum.hasSum
  have hrows := hA.prod_fiberwise hrow
  have hdiag : HasSum (fun j => ∑ p ∈ Finset.antidiagonal j, T p) (∑' p, T p) := by
    have h := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff).mpr hA
    refine h.sigma fun j => ?_
    have := hasSum_fintype (fun q : (Finset.antidiagonal j) => T q)
    simpa [Finset.sum_attach] using this
  have hdj (j : ℕ) : ∑ p ∈ Finset.antidiagonal j, T p =
      regularizedHGFun (∅ : Multiset ℂ) {c} x * (y ^ j / (j ! * Gamma (c + j))) := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hs := shBes_sum_choose (by linarith : 0 < c.re) x j
    rw [show regularizedHGFun (∅ : Multiset ℂ) {c} x * (y ^ j / (j ! * Gamma (c + j))) =
      y ^ j / j ! * (regularizedHGFun (∅ : Multiset ℂ) {c} x * (Gamma (c + j))⁻¹) by ring,
      ← hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hl'
    simp only [hT, Nat.add_sub_cancel_left]
    have hch := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right l b)
    rw [Nat.add_sub_cancel_left] at hch
    have hch' : ((l + b).choose l : ℂ) * l ! * b ! = (l + b) ! := by exact_mod_cast hch
    have hl0 : (l ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hb0 : (b ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hc0 : ((l + b).choose l : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_right l b)).ne'
    rw [show 2 * l + b = l + (l + b) by ring, ← hch']
    field_simp
    ring
  have hcol := (shBes_hasSum_series c y).mul_left (regularizedHGFun (∅ : Multiset ℂ) {c} x)
  simp_rw [← hdj] at hcol
  rw [hdiag.unique hcol] at hrows
  exact hrows

/-- A crude bound for Gegenbauer polynomials on `[-1, 1]` with complex parameter:
`‖(ν + n) C_n^ν(cos φ)‖ ≤ (‖ν‖ + 1) (4 (1 + ‖ν‖))ⁿ`. -/
theorem shBes_norm_ultrasph_le {ν : ℂ} (hν : 0 < ν.re) (n : ℕ) (θ : ℝ) :
    ‖(ν + n) * ultrasphPoly ν n (Real.cos θ)‖ ≤ (‖ν‖ + 1) * (4 * (1 + ‖ν‖)) ^ n := by
  set B : ℝ := 1 + ‖ν‖
  have hB : 0 ≤ B := by positivity
  have hC : ‖ultrasphPoly ν n (Real.cos θ)‖ ≤ (n + 1) * B ^ n := by
    rw [ofReal_cos, ultrasphPoly_cos_sum (by linarith)]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ k ∈ Finset.range (n + 1),
        ‖poch ν k * poch ν (n - k) / ((k ! : ℂ) * (n - k) !) *
          cos (((n : ℂ) - 2 * k) * θ)‖ ≤ B ^ n := by
      intro k hk
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have h1 := shBes_norm_poch_le ν k
      have h2 := shBes_norm_poch_le ν (n - k)
      have hcos : ‖cos (((n : ℂ) - 2 * k) * θ)‖ ≤ 1 := by
        rw [show ((n : ℂ) - 2 * k) * θ = (((n : ℝ) - 2 * k) * θ : ℝ) by push_cast; ring,
          ← ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
        exact Real.abs_cos_le_one _
      have hkf : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
      have hnkf : (0 : ℝ) < (n - k) ! := by exact_mod_cast Nat.factorial_pos (n - k)
      rw [norm_mul, norm_div, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
      calc ‖poch ν k‖ * ‖poch ν (n - k)‖ / (k ! * (n - k) !) * ‖cos (((n : ℂ) - 2 * k) * θ)‖
          ≤ (k ! * B ^ k) * ((n - k) ! * B ^ (n - k)) / (k ! * (n - k) !) * 1 := by
            gcongr
        _ = B ^ n := by
            rw [show B ^ n = B ^ k * B ^ (n - k) by rw [← pow_add, Nat.add_sub_cancel' hk']]
            field_simp
    refine (Finset.sum_le_sum hterm).trans ?_
    simp
  have hn1 : (n + 1 : ℝ) ≤ 2 ^ n := by
    have := Nat.lt_two_pow_self (n := n)
    exact_mod_cast this
  rw [norm_mul]
  have hν' : ‖ν + n‖ ≤ (‖ν‖ + 1) * (n + 1) := by
    refine (norm_add_le _ _).trans ?_
    simp only [Complex.norm_natCast]
    nlinarith [norm_nonneg ν, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  calc ‖ν + n‖ * ‖ultrasphPoly ν n (Real.cos θ)‖ ≤ ((‖ν‖ + 1) * (n + 1)) * ((n + 1) * B ^ n) := by
        gcongr
    _ ≤ ((‖ν‖ + 1) * 2 ^ n) * (2 ^ n * B ^ n) := by gcongr
    _ = _ := by rw [mul_pow, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring

/-- The reindexing `(k, l) ↦ (k - 2l, l)` from `{(k, l) : 2l ≤ k}` onto `ℕ × ℕ`. -/
def shBes_equiv : (Σ k : ℕ, Fin (k / 2 + 1)) ≃ ℕ × ℕ where
  toFun p := (p.1 - 2 * p.2, p.2)
  invFun q := ⟨q.1 + 2 * q.2, ⟨q.2, by omega⟩⟩
  left_inv p := by
    obtain ⟨k, l, hl⟩ := p
    have h : k - 2 * l + 2 * l = k := by omega
    exact Sigma.ext h ((Fin.heq_ext_iff (by dsimp only; rw [h])).mpr rfl)
  right_inv q := by
    obtain ⟨n, l⟩ := q
    simp

/-- Gegenbauer's addition theorem, AAR (4.10.5), for positive radii and nonzero distance.
DLMF's radius-ordering restriction is unnecessary for `J`. -/
@[dlmf 10.23.E8]
theorem besselJ_addition {ν : ℂ} {r rho phi : ℝ} (hν : 0 < ν.re)
    (hr : 0 < r) (hrho : 0 < rho)
    (hR : 0 < r ^ 2 + rho ^ 2 - 2 * r * rho * Real.cos phi) :
    besselJ ν (Real.sqrt (r ^ 2 + rho ^ 2 - 2 * r * rho * Real.cos phi) : ℂ) /
        (Real.sqrt (r ^ 2 + rho ^ 2 - 2 * r * rho * Real.cos phi) : ℂ) ^ ν =
      (2 ^ ν * Gamma ν / (r * rho : ℂ) ^ ν) *
        ∑' n : ℕ, (ν + n) * besselJ (ν + n) r * besselJ (ν + n) rho *
          ultrasphPoly ν n (Real.cos phi) := by
  set W := Real.sqrt (r ^ 2 + rho ^ 2 - 2 * r * rho * Real.cos phi) with hWdef
  have hW : 0 < W := Real.sqrt_pos.mpr hR
  have hW2 : W ^ 2 = r ^ 2 + rho ^ 2 - 2 * r * rho * Real.cos phi := Real.sq_sqrt hR.le
  set t : ℝ := Real.cos phi with ht
  set x : ℂ := -((r : ℂ) ^ 2 / 4) with hx
  set y : ℂ := -((rho : ℂ) ^ 2 / 4) with hy
  set a : ℂ := (r : ℂ) * rho / 4 with ha
  set z : ℂ := a * (2 * t) with hz
  set s : ℂ := x + y with hs
  have hν0 : ν ≠ 0 := by rintro rfl; simp at hν
  have hre1 : 1 ≤ (ν + 1).re := by simp; linarith
  have hhalf (u : ℝ) (hu : 0 ≤ u) : ((u : ℂ) / 2) ^ ν = (u : ℂ) ^ ν * (1 / 2 : ℂ) ^ ν := by
    rw [div_eq_mul_one_div, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      mul_cpow_ofReal_nonneg hu (by norm_num)]
  have h2pow : (2 : ℂ) ^ ν * (1 / 2 : ℂ) ^ ν = 1 := by
    rw [show (2 : ℂ) ^ ν * (1 / 2 : ℂ) ^ ν = (((2 : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ)) ^ ν by
      rw [mul_cpow_ofReal_nonneg (by norm_num) (by norm_num)]; norm_num]
    norm_num
  have hcpow_ne (u : ℝ) (hu : 0 < u) : (u : ℂ) ^ ν ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    exact fun h => ofReal_ne_zero.mpr hu.ne' h.1
  -- the left side as a regularized `₀F₁`
  have hL : besselJ ν (W : ℂ) / (W : ℂ) ^ ν =
      (1 / 2 : ℂ) ^ ν * regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (s + z) := by
    rw [besselJ_eq_regularized, hhalf W hW.le]
    have harg : -((W : ℂ) ^ 2 / 4) = s + z := by
      have h : ((W ^ 2 : ℝ) : ℂ) = ((r ^ 2 + rho ^ 2 - 2 * r * rho * t : ℝ) : ℂ) := by rw [hW2]
      push_cast at h
      rw [h, hs, hx, hy, hz, ha]
      ring
    rw [harg]
    field_simp [hcpow_ne W hW]
  -- the double family
  set Xf : ℕ → ℂ := fun n => (ν + n) * ultrasphPoly ν n t with hXf
  set Yf : ℕ → ℕ → ℂ := fun n l => a ^ n * (a ^ 2) ^ l / l ! with hYf
  set Zf : ℕ → ℕ → ℂ := fun n l => ν⁻¹ * (poch (ν + 1) (n + l))⁻¹ with hZf
  set Vf : ℕ → ℕ → ℂ := fun n l =>
    regularizedHGFun (∅ : Multiset ℂ) {ν + 1 + ((n + 2 * l : ℕ) : ℂ)} s with hVf
  set G : ℕ × ℕ → ℂ := fun p => Xf p.1 * Yf p.1 p.2 * Zf p.1 p.2 * Vf p.1 p.2 with hG
  have hterm (k : ℕ) : z ^ k / k ! * regularizedHGFun (∅ : Multiset ℂ) {ν + 1 + k} s =
      ∑ l ∈ Finset.range (k / 2 + 1), G (k - 2 * l, l) := by
    have hm := monomial_ultrasphPoly_expansion hν k (t : ℂ)
    have hk0 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have h1 : z ^ k / k ! * regularizedHGFun (∅ : Multiset ℂ) {ν + 1 + k} s =
        (∑ l ∈ Finset.range (k / 2 + 1), (ν + k - 2 * l) / ν / (poch (ν + 1) (k - l) * l !) *
          ultrasphPoly ν (k - 2 * l) t) *
          (a ^ k * regularizedHGFun (∅ : Multiset ℂ) {ν + 1 + k} s) := by
      rw [hz, mul_pow, hm]
      field_simp
    rw [h1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l hl => ?_
    have h2l : 2 * l ≤ k := by have := Finset.mem_range.mp hl; omega
    simp only [hG, hXf, hYf, hZf, hVf]
    rw [Nat.sub_add_cancel h2l, show k - 2 * l + l = k - l by omega,
      show a ^ k = a ^ (k - 2 * l) * (a ^ 2) ^ l by
        rw [← pow_mul, ← pow_add, Nat.sub_add_cancel h2l], Nat.cast_sub h2l]
    push_cast
    ring
  -- summability
  set B : ℝ := 1 + ‖ν‖ with hB
  set M : ℝ := ‖(Gamma (ν + 1))⁻¹‖ * ∑' m : ℕ, ‖s‖ ^ m / (m ! : ℝ) with hM
  have hM0 : 0 ≤ M := mul_nonneg (norm_nonneg _) (tsum_nonneg fun m => by positivity)
  have hGs : Summable G := by
    have hu := Real.summable_pow_div_factorial (4 * B * ‖a‖)
    have hv := Real.summable_pow_div_factorial (‖a‖ ^ 2)
    have huv := (hu.mul_of_nonneg hv (fun _ => by positivity) (fun _ => by positivity)).mul_left
      ((‖ν‖ + 1) * ‖ν‖⁻¹ * M)
    refine Summable.of_norm_bounded huv fun p => ?_
    obtain ⟨n, l⟩ := p
    have h1 : ‖Xf n‖ ≤ (‖ν‖ + 1) * (4 * B) ^ n := shBes_norm_ultrasph_le hν n phi
    have h2 : ‖Yf n l‖ = ‖a‖ ^ n * (‖a‖ ^ 2) ^ l / l ! := by
      simp only [hYf, norm_div, norm_mul, norm_pow, Complex.norm_natCast]
    have h3 : ‖Zf n l‖ ≤ ‖ν‖⁻¹ := by
      simp only [hZf]
      rw [norm_mul, norm_inv, norm_inv]
      have hp := shBes_factorial_le_norm_poch hre1 (n + l)
      have hf : (1 : ℝ) ≤ (n + l) ! := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
      calc ‖ν‖⁻¹ * ‖poch (ν + 1) (n + l)‖⁻¹ ≤ ‖ν‖⁻¹ * 1 := by
            gcongr
            exact inv_le_one_of_one_le₀ (hf.trans hp)
        _ = _ := mul_one _
    have h4 : ‖Vf n l‖ ≤ M / n ! := by
      refine (shBes_norm_F_le hre1 (n + 2 * l) s).trans ?_
      gcongr
      omega
    simp only [hG]
    rw [norm_mul, norm_mul, norm_mul, h2]
    have hnf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    calc ‖Xf n‖ * (‖a‖ ^ n * (‖a‖ ^ 2) ^ l / l !) * ‖Zf n l‖ * ‖Vf n l‖
        ≤ ((‖ν‖ + 1) * (4 * B) ^ n) * (‖a‖ ^ n * (‖a‖ ^ 2) ^ l / l !) * ‖ν‖⁻¹ * (M / n !) := by
          gcongr
      _ = _ := by rw [mul_pow (4 * B)]; field_simp
  -- regrouping by total degree
  have hA := hGs.hasSum
  have hk : HasSum (fun k => ∑ l ∈ Finset.range (k / 2 + 1), G (k - 2 * l, l)) (∑' p, G p) := by
    have h := (shBes_equiv.hasSum_iff).mpr hA
    refine h.sigma fun k => ?_
    have := hasSum_fintype (fun i : Fin (k / 2 + 1) => (G ∘ shBes_equiv) ⟨k, i⟩)
    convert this using 1
    rw [← Fin.sum_univ_eq_sum_range (fun l => G (k - 2 * l, l))]
    rfl
  have hTG : ∑' p, G p = regularizedHGFun (∅ : Multiset ℂ) {ν + 1} (s + z) := by
    refine hk.unique ?_
    simpa only [hterm] using shBes_hasSum_shift (ν + 1) s z
  -- regrouping by Gegenbauer degree, with the product formula
  have hrow (n : ℕ) : HasSum (fun l => G (n, l)) (a ^ n * Xf n * Gamma ν *
      (regularizedHGFun (∅ : Multiset ℂ) {ν + 1 + n} x *
        regularizedHGFun (∅ : Multiset ℂ) {ν + 1 + n} y)) := by
    have hc : 1 ≤ (ν + 1 + n).re := by simp; linarith
    have h := (shBes_hasSum_product hc x y).mul_left (a ^ n * Xf n * Gamma ν)
    convert h using 1
    funext l
    have hxy : x * y = a ^ 2 := by rw [hx, hy, ha]; ring
    have hp : poch (ν + 1) (n + l) ≠ 0 := poch_ne_zero_of_re_pos (by simp; linarith) _
    have hg : Gamma ν ≠ 0 := Gamma_ne_zero_of_re_pos hν
    have hpg : ν⁻¹ * (poch (ν + 1) (n + l))⁻¹ = Gamma ν * (Gamma (ν + 1 + n + l))⁻¹ := by
      have h1 := DLMF.Gamma.poch_mul_recip_Gamma_add_nat (ν + 1) (n + l)
      rw [Gamma_add_one ν hν0] at h1
      push_cast at h1
      rw [← add_assoc] at h1
      rw [show (Gamma (ν + 1 + n + l))⁻¹ = (ν * Gamma ν)⁻¹ / poch (ν + 1) (n + l) by
        rw [eq_div_iff hp, ← h1]; ring]
      field_simp
    simp only [hG, hXf, hYf, hZf, hVf]
    rw [hpg, hxy, show ν + 1 + ((n + 2 * l : ℕ) : ℂ) = ν + 1 + n + ((2 * l : ℕ) : ℂ) by
      push_cast; ring]
    ring
  have hrows := hA.prod_fiberwise hrow
  rw [hTG] at hrows
  -- the right side
  have hJ (n : ℕ) (u : ℝ) (hu : 0 < u) : besselJ (ν + n) (u : ℂ) =
      (u : ℂ) ^ ν * (1 / 2 : ℂ) ^ ν * ((u : ℂ) / 2) ^ n *
        regularizedHGFun (∅ : Multiset ℂ) {ν + 1 + n} (-((u : ℂ) ^ 2 / 4)) := by
    rw [besselJ_eq_regularized, cpow_add _ _ (div_ne_zero (ofReal_ne_zero.mpr hu.ne') two_ne_zero),
      cpow_natCast, hhalf u hu.le, show ν + n + 1 = ν + 1 + n by ring]
  rw [hL, ← hrows.tsum_eq, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  funext n
  rw [hJ n r hr, hJ n rho hrho, mul_cpow_ofReal_nonneg hr.le hrho.le]
  simp only [hXf]
  rw [← hx, ← hy]
  have hrp := hcpow_ne r hr
  have hrhop := hcpow_ne rho hrho
  have hapow : a ^ n = ((r : ℂ) / 2) ^ n * ((rho : ℂ) / 2) ^ n := by
    rw [← mul_pow, ha]; ring
  rw [hapow, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hrp hrhop)]
  linear_combination (-1 : ℂ) * ((r : ℂ) ^ ν * (rho : ℂ) ^ ν * Gamma ν * (ν + n) *
    ultrasphPoly ν n t *
    ((r : ℂ) / 2) ^ n * ((rho : ℂ) / 2) ^ n * regularizedHGFun (∅ : Multiset ℂ) {ν + 1 + n} x *
    regularizedHGFun (∅ : Multiset ℂ) {ν + 1 + n} y * (1 / 2 : ℂ) ^ ν) * h2pow

end DLMF.Bessel
