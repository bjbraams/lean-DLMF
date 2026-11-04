/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Lame.Polynomials.Eigenvalues
public import DLMFMathlib.Analysis.SpecificLimits.PoincarePerron

/-!
# Ratio limits of the Fourier coefficients of Lamé functions

The Fourier coefficients of a Lamé function satisfy one of the three-term recurrences
`LameRecurrence` of DLMF §29.6, whose coefficients grow like `p²` with limiting characteristic
roots `k²/(1+k')²` and `(1+k')²/k²` (`k' = √(1 - k²)`). Bounded solutions that do not vanish
eventually are minimal, so by Perron's theorem the ratio of consecutive coefficients tends to
`k²/(1+k')²` (DLMF 29.6.7, 29.6.14, 29.6.22, 29.6.29, 29.6.37, 29.6.44, 29.6.52, 29.6.59).

A solution of the recurrence vanishes eventually only if it is a Lamé polynomial: going
backwards, the recurrence stops only where `γ_p = 0`, which happens exactly for `ν = t.order n`
and `p = n + 1`; then the coefficient vector is an eigenvector of the matrix 29.15.2, whose
eigenvalues are those of the first `n + 1` eigenfunctions.

## Main results

* `LamePolynomialType.tendsto_coeff_ratio`: if `c` solves the recurrence of type `t` with the
  eigenparameter of the `m`th eigenfunction of the boundary types of `t`, is bounded and not
  identically zero, and `ν = t.order n` only for `n < m`, then `c_{p+1}/c_p → k²/(1+k')²`.
* `abs_lameCosCoeff_le`, `abs_lameSinCoeff_le`: the Fourier coefficients of a continuous
  function are bounded.
-/

@[expose] public section

open Filter Set DLMF.Elliptic

open scoped Real Topology

noncomputable section

namespace DLMF.Lame

namespace CoefficientRatios

/-- A quotient of two quadratic functions of `q` (given through their values at `0` and `1` and
their leading coefficients) tends to the quotient of the leading coefficients. -/
private lemma tendsto_div_of_quadratic {f g : ℕ → ℝ} (a d : ℝ) (hd : d ≠ 0)
    (hf : ∀ q : ℕ, f q = a * q ^ 2 + (f 1 - f 0 - a) * q + f 0)
    (hg : ∀ q : ℕ, g q = d * q ^ 2 + (g 1 - g 0 - d) * q + g 0) :
    Tendsto (fun q => f q / g q) atTop (𝓝 (a / d)) := by
  have h1 := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hN : Tendsto (fun q : ℕ => a + (f 1 - f 0 - a) * (1 / (q : ℝ)) + f 0 * (1 / (q : ℝ)) ^ 2)
      atTop (𝓝 (a + (f 1 - f 0 - a) * 0 + f 0 * 0 ^ 2)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul h1)).add (tendsto_const_nhds.mul (h1.pow 2))
  have hD : Tendsto (fun q : ℕ => d + (g 1 - g 0 - d) * (1 / (q : ℝ)) + g 0 * (1 / (q : ℝ)) ^ 2)
      atTop (𝓝 (d + (g 1 - g 0 - d) * 0 + g 0 * 0 ^ 2)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul h1)).add (tendsto_const_nhds.mul (h1.pow 2))
  simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    at hN hD
  refine (hN.div hD hd).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with q hq
  have hq' : (q : ℝ) ≠ 0 := by positivity
  simp only [Pi.div_apply]
  rw [hf q, hg q]
  field_simp

/-- A quadratic function with nonzero leading coefficient is eventually nonzero. -/
private lemma eventually_ne_zero_of_quadratic {f : ℕ → ℝ} (a : ℝ) (ha : a ≠ 0)
    (hf : ∀ q : ℕ, f q = a * q ^ 2 + (f 1 - f 0 - a) * q + f 0) : ∀ᶠ q in atTop, f q ≠ 0 := by
  have h := tendsto_div_of_quadratic (g := fun q : ℕ => (q : ℝ) ^ 2) a 1 one_ne_zero hf
    (fun q => by simp)
  rw [div_one] at h
  filter_upwards [h.eventually_ne ha] with q hq h0
  exact hq (by rw [h0, zero_div])

end CoefficientRatios

open CoefficientRatios

/-- The ratio `(β_{q+1} - H)/α_{q+1}` of the recurrence coefficients tends to
`4(2 - k²)/(-2k²)`. -/
theorem LameRecurrence.tendsto_beta_sub_div_alpha (r : LameRecurrence) (ν k H : ℝ) (hk : k ≠ 0) :
    Tendsto (fun q : ℕ => (r.beta ν k (q + 1) - H) / r.alpha ν k (q + 1)) atTop
      (𝓝 (4 * (2 - k ^ 2) / (-2 * k ^ 2))) := by
  have hk2 : -2 * k ^ 2 ≠ 0 := by
    have := pow_ne_zero 2 hk; intro h; apply this; linarith
  cases r <;> refine tendsto_div_of_quadratic _ _ hk2 (fun q => ?_) (fun q => ?_) <;>
    simp [LameRecurrence.alpha, LameRecurrence.beta] <;> ring

/-- The ratio `γ_{q+1}/α_{q+1}` of the recurrence coefficients tends to `1`. -/
theorem LameRecurrence.tendsto_gamma_div_alpha (r : LameRecurrence) (ν k : ℝ) (hk : k ≠ 0) :
    Tendsto (fun q : ℕ => r.gamma ν k (q + 1) / r.alpha ν k (q + 1)) atTop (𝓝 1) := by
  have hk2 : -2 * k ^ 2 ≠ 0 := by
    have := pow_ne_zero 2 hk; intro h; apply this; linarith
  have h : Tendsto (fun q : ℕ => r.gamma ν k (q + 1) / r.alpha ν k (q + 1)) atTop
      (𝓝 (-2 * k ^ 2 / (-2 * k ^ 2))) := by
    cases r <;> refine tendsto_div_of_quadratic _ _ hk2 (fun q => ?_) (fun q => ?_) <;>
      simp [LameRecurrence.alpha, LameRecurrence.gamma] <;> ring
  rwa [div_self hk2] at h

/-- The coefficient `α_{q+1}` is eventually nonzero. -/
theorem LameRecurrence.eventually_alpha_ne_zero (r : LameRecurrence) (ν k : ℝ) (hk : k ≠ 0) :
    ∀ᶠ q : ℕ in atTop, r.alpha ν k (q + 1) ≠ 0 := by
  have hk2 : -2 * k ^ 2 ≠ 0 := by
    have := pow_ne_zero 2 hk; intro h; apply this; linarith
  cases r <;> refine eventually_ne_zero_of_quadratic _ hk2 (fun q => ?_) <;>
    simp [LameRecurrence.alpha] <;> ring

/-- `γ_p` (`p ≥ 1`) of the recurrence of type `t` vanishes only for `ν = t.order (p - 1)`. -/
theorem LamePolynomialType.eq_order_of_gamma_eq_zero (t : LamePolynomialType) {ν k : ℝ}
    (hν : -1 / 2 ≤ ν)
    (hk : k ≠ 0) {p : ℕ} (hp : 1 ≤ p) (h : t.recurrence.gamma ν k p = 0) :
    ν = (t.order (p - 1) : ℝ) := by
  obtain ⟨j, rfl⟩ : ∃ j, p = j + 1 := ⟨p - 1, by omega⟩
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hk2 : k ^ 2 ≠ 0 := pow_ne_zero 2 hk
  cases t <;>
    simp only [LamePolynomialType.recurrence, LameRecurrence.gamma, LamePolynomialType.order,
      Nat.add_sub_cancel, mul_eq_zero, div_eq_zero_iff, hk2, OfNat.ofNat_ne_zero, or_false]
      at h ⊢ <;>
    push_cast at h ⊢ <;>
    rcases h with h | h <;> linarith

/-- The order `t.order n` determines `n`. -/
theorem LamePolynomialType.order_injective (t : LamePolynomialType) :
    Function.Injective t.order := by
  intro a b h
  cases t <;> simp only [LamePolynomialType.order] at h <;> omega

/-- The Fourier coefficients `lameCosCoeff w k b j` of a continuous `w` are bounded in `j`. -/
theorem abs_lameCosCoeff_le {k : ℝ} (hk : k ^ 2 < 1) {w : ℝ → ℝ} (hw : Continuous w)
    (b : Bool) : ∃ C, ∀ j, |Real.lameCosCoeff w k b j| ≤ C := by
  set K := Real.completeEllipticKOfParameter (k ^ 2)
  set ρ : ℝ → ℝ := fun x => if b then Real.jacobiDnOfParameter x (k ^ 2) else 1
  have hρ : Continuous ρ := by
    simp only [ρ]; split_ifs
    · exact Real.continuous_jacobiDnOfParameter hk
    · exact continuous_const
  obtain ⟨M, hM⟩ := (isCompact_uIcc (a := 0) (b := K)).exists_bound_of_continuousOn
    (f := fun x => w x * ρ x) (hw.mul hρ).continuousOn
  refine ⟨4 / π * (M * |K - 0|), fun j => ?_⟩
  rw [Real.lameCosCoeff, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 / π)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  have := hM x (Set.uIoc_subset_uIcc hx)
  simp only [Real.norm_eq_abs] at this ⊢
  rw [show w x * Real.cos (j * Real.lamePhi x k) *
      (if b then Real.jacobiDnOfParameter x (k ^ 2) else 1) =
    (w x * ρ x) * Real.cos (j * Real.lamePhi x k) by simp only [ρ]; ring, abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)).trans this

/-- The Fourier coefficients `lameSinCoeff w k b j` of a continuous `w` are bounded in `j`. -/
theorem abs_lameSinCoeff_le {k : ℝ} (hk : k ^ 2 < 1) {w : ℝ → ℝ} (hw : Continuous w)
    (b : Bool) : ∃ C, ∀ j, |Real.lameSinCoeff w k b j| ≤ C := by
  set K := Real.completeEllipticKOfParameter (k ^ 2)
  set ρ : ℝ → ℝ := fun x => if b then Real.jacobiDnOfParameter x (k ^ 2) else 1
  have hρ : Continuous ρ := by
    simp only [ρ]; split_ifs
    · exact Real.continuous_jacobiDnOfParameter hk
    · exact continuous_const
  obtain ⟨M, hM⟩ := (isCompact_uIcc (a := 0) (b := K)).exists_bound_of_continuousOn
    (f := fun x => w x * ρ x) (hw.mul hρ).continuousOn
  refine ⟨4 / π * (M * |K - 0|), fun j => ?_⟩
  rw [Real.lameSinCoeff, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 / π)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  have := hM x (Set.uIoc_subset_uIcc hx)
  simp only [Real.norm_eq_abs] at this ⊢
  rw [show w x * Real.sin (j * Real.lamePhi x k) *
      (if b then Real.jacobiDnOfParameter x (k ^ 2) else 1) =
    (w x * ρ x) * Real.sin (j * Real.lamePhi x k) by simp only [ρ]; ring, abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)).trans this


open Matrix in
/-- A solution of the recurrence of type `t` with order `ν = t.order n` and the eigenparameter of
the `m`th eigenfunction, `n < m`, that vanishes beyond `n` vanishes identically: otherwise its
first `n + 1` entries form an eigenvector of the matrix 29.15.2, whose eigenvalues belong to the
first `n + 1` eigenfunctions. -/
theorem LamePolynomialType.eq_zero_of_eq_zero_of_lt (t : LamePolynomialType) {k : ℝ} (hk0 : 0 < k)
    (hk1 : k < 1) {n m : ℕ} (hnm : n < m) {c : ℕ → ℝ}
    (hrec0 : (t.recurrence.beta (t.order n) k 0 -
        (2 * Real.lameEigenvalue (t.order n) k (lamePolyOddZero t) (lamePolyOddK t) m -
          (t.order n : ℝ) * ((t.order n : ℝ) + 1) * k ^ 2)) * c 0 +
      t.recurrence.alpha (t.order n) k 0 * c 1 = 0)
    (hrec : ∀ p : ℕ, 1 ≤ p → t.recurrence.gamma (t.order n) k p * c (p - 1) +
      (t.recurrence.beta (t.order n) k p -
        (2 * Real.lameEigenvalue (t.order n) k (lamePolyOddZero t) (lamePolyOddK t) m -
          (t.order n : ℝ) * ((t.order n : ℝ) + 1) * k ^ 2)) * c p +
      t.recurrence.alpha (t.order n) k p * c (p + 1) = 0)
    (hsupp : ∀ p, n < p → c p = 0) : ∀ p, c p = 0 := by
  set ν : ℝ := (t.order n : ℝ)
  set E := Real.lameEigenvalue ν k (lamePolyOddZero t) (lamePolyOddK t)
  set H := 2 * E m - ν * (ν + 1) * k ^ 2 with hH
  set M := lameMatrix t.recurrence ν k n
  set v : Fin (n + 1) → ℝ := fun i => c i
  have hext : ∀ q, vecExtendZero v q = c q := by
    intro q
    unfold vecExtendZero
    split_ifs with h
    · rfl
    · exact (hsupp q (by omega)).symm
  have hM : M *ᵥ v = H • v := by
    ext ⟨p, hp⟩
    rw [show M = tridiagMatrix (t.recurrence.alpha ν k) (t.recurrence.beta ν k)
      (t.recurrence.gamma ν k) n from rfl, tridiagMatrix_mulVec_apply _ _ _ _ hp, hext, hext]
    simp only [Pi.smul_apply, smul_eq_mul, v]
    split_ifs with h0
    · subst h0; linear_combination hrec0
    · rw [hext]; linear_combination hrec p (by omega)
  by_cases hv : v = 0
  · intro p
    rcases le_or_gt p n with hp | hp
    · simpa [v] using congrFun hv ⟨p, by omega⟩
    · exact hsupp p hp
  exfalso
  have hdet : (Matrix.scalar (Fin (n + 1)) H - M).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, hM]
    ext i
    simp
  have hroot : H ∈ M.charpoly.roots := by
    rw [Polynomial.mem_roots (Matrix.charpoly_monic M).ne_zero, Polynomial.IsRoot,
      Matrix.eval_charpoly, hdet]
  obtain ⟨hcard, -, -⟩ := lamePolynomialH_strictMono hk0 hk1 t n
  set L := M.charpoly.roots.sort (· ≤ ·) with hL
  have hlen : L.length = n + 1 := by rw [hL, Multiset.length_sort]; exact hcard
  have hmem : H ∈ L := by rw [hL, Multiset.mem_sort]; exact hroot
  obtain ⟨j, hj, hjH⟩ := List.mem_iff_getElem.1 hmem
  have hjn : j ≤ n := by omega
  have hpoly : lamePolynomialH t n j k = H := by
    simp only [lamePolynomialH, lameMatrixEigenvalue]
    rw [← hL, List.getD_eq_getElem _ _ hj, hjH]
  have heq := lameEigenvalue_lamePolynomialType_eq hk0 hk1 t hjn
  rw [hpoly] at heq
  have hEm : E j = E m := by
    simp only [E, ν] at heq ⊢; rw [heq, hH]; ring
  have := (Real.lameEigenvalue_spec (ν := ν) hk0 hk1 (lamePolyOddZero t)
    (lamePolyOddK t)).2.1.injective hEm
  omega

/-- If a solution of the recurrence vanishes from `P` on and `γ_q ≠ 0` for all `q > p`, then
it vanishes at `p`. -/
private lemma LameRecurrence.eq_zero_of_eventually_eq_zero {r : LameRecurrence} {ν k H : ℝ}
    {c : ℕ → ℝ}
    (hrec : ∀ p : ℕ, 1 ≤ p → r.gamma ν k p * c (p - 1) + (r.beta ν k p - H) * c p +
      r.alpha ν k p * c (p + 1) = 0) {P : ℕ} (hP : ∀ p, P ≤ p → c p = 0) :
    ∀ d p, P ≤ p + d → (∀ q, p < q → r.gamma ν k q ≠ 0) → c p = 0 := by
  intro d
  induction d with
  | zero => intro p hp _; exact hP p (by omega)
  | succ d ih =>
    intro p hp hγ
    have h1 := ih (p + 1) (by omega) fun q hq => hγ q (by omega)
    have h2 := ih (p + 2) (by omega) fun q hq => hγ q (by omega)
    have hr := hrec (p + 1) (by omega)
    rw [Nat.add_sub_cancel, h1, show p + 1 + 1 = p + 2 by ring, h2] at hr
    have : r.gamma ν k (p + 1) * c p = 0 := by linear_combination hr
    exact (mul_eq_zero.1 this).resolve_left (hγ (p + 1) (by omega))

/-- **Ratio limit of Lamé Fourier coefficients** (DLMF 29.6.7, 29.6.14, 29.6.22, 29.6.29,
29.6.37, 29.6.44, 29.6.52, 29.6.59): if `c` solves the recurrence of type `t` with the
eigenparameter `H = 2h - ν(ν+1)k²` of the `m`th eigenvalue `h` of the boundary types of `t`, is
bounded and not identically zero, and `ν = t.order n` only for `n < m`, then
`c_{p+1}/c_p → k²/(1 + k')²`. -/
theorem LamePolynomialType.tendsto_coeff_ratio (t : LamePolynomialType) {ν k : ℝ} (hν : -1 / 2 ≤ ν)
    (hk0 : 0 < k) (hk1 : k < 1) {m : ℕ} {c : ℕ → ℝ}
    (hrec0 : (t.recurrence.beta ν k 0 -
        (2 * Real.lameEigenvalue ν k (lamePolyOddZero t) (lamePolyOddK t) m -
          ν * (ν + 1) * k ^ 2)) * c 0 + t.recurrence.alpha ν k 0 * c 1 = 0)
    (hrec : ∀ p : ℕ, 1 ≤ p → t.recurrence.gamma ν k p * c (p - 1) +
      (t.recurrence.beta ν k p -
        (2 * Real.lameEigenvalue ν k (lamePolyOddZero t) (lamePolyOddK t) m -
          ν * (ν + 1) * k ^ 2)) * c p + t.recurrence.alpha ν k p * c (p + 1) = 0)
    {C : ℝ} (hbdd : ∀ p, |c p| ≤ C) (hnz : ∃ p, c p ≠ 0)
    (hexc : ∀ n : ℕ, ν = (t.order n : ℝ) → n < m) :
    Tendsto (fun p => c (p + 1) / c p) atTop
      (𝓝 (k ^ 2 / (1 + Real.sqrt (1 - k ^ 2)) ^ 2)) := by
  have hk : k ≠ 0 := hk0.ne'
  set H := 2 * Real.lameEigenvalue ν k (lamePolyOddZero t) (lamePolyOddK t) m -
    ν * (ν + 1) * k ^ 2
  -- `c` is not eventually zero
  have hfreq : ∃ᶠ p in atTop, c p ≠ 0 := by
    intro hev
    obtain ⟨P, hP⟩ := eventually_atTop.1 hev
    have hP' : ∀ p, P ≤ p → c p = 0 := fun p hp => not_not.1 (hP p hp)
    have back := LameRecurrence.eq_zero_of_eventually_eq_zero hrec hP'
    obtain ⟨p₀, hp₀⟩ := hnz
    by_cases hex : ∃ n : ℕ, ν = (t.order n : ℝ)
    · obtain ⟨n, hn⟩ := hex
      have hnm := hexc n hn
      have hsupp : ∀ p, n < p → c p = 0 := fun p hp => back P p (by omega) fun q hq hγ => by
        have h := t.eq_order_of_gamma_eq_zero hν hk (by omega) hγ
        rw [hn] at h
        have := t.order_injective (Nat.cast_injective h)
        omega
      subst hn
      exact hp₀ (t.eq_zero_of_eq_zero_of_lt hk0 hk1 hnm hrec0 hrec hsupp p₀)
    · push Not at hex
      exact hp₀ (back P p₀ (by omega) fun q hq hγ =>
        hex (q - 1) (t.eq_order_of_gamma_eq_zero hν hk (by omega) hγ))
  -- the characteristic roots
  set s := Real.sqrt (1 - k ^ 2) with hs
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hs2 : s ^ 2 = 1 - k ^ 2 := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s < 1 := by nlinarith
  have hkpos : 0 < k ^ 2 := by positivity
  have h1s : 0 < 1 + s := by linarith
  set ρ₁ := k ^ 2 / (1 + s) ^ 2
  set ρ₂ := (1 + s) ^ 2 / k ^ 2
  have hρ₁ : ρ₁ < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  have hρ₂ : 1 < ρ₂ := by
    rw [one_lt_div hkpos]; nlinarith
  have hρ₁0 : 0 < ρ₁ := by positivity
  have hsum : 4 * (2 - k ^ 2) / (-2 * k ^ 2) = -(ρ₁ + ρ₂) := by
    rw [eq_neg_iff_add_eq_zero]
    simp only [ρ₁, ρ₂]
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_add_div _ _ (by nlinarith) (by positivity), div_eq_zero_iff]
    left
    linear_combination (-2 * k ^ 2 * (k ^ 2 + 1 - s ^ 2 + 2 * (1 + s) ^ 2)) * hs2
  have hprod : (1 : ℝ) = ρ₁ * ρ₂ := by
    simp only [ρ₁, ρ₂]; field_simp
  have hβ := t.recurrence.tendsto_beta_sub_div_alpha ν k H hk
  rw [hsum] at hβ
  have hγ := t.recurrence.tendsto_gamma_div_alpha ν k hk
  rw [hprod] at hγ
  refine tendsto_succ_div_of_three_term_recurrence_of_bounded (x := c)
    (α := fun q => t.recurrence.alpha ν k (q + 1))
    (β := fun q => t.recurrence.beta ν k (q + 1) - H)
    (γ := fun q => t.recurrence.gamma ν k (q + 1)) ?_ ?_
    (t.recurrence.eventually_alpha_ne_zero ν k hk) hβ hγ ?_ (C := C) (fun p => hbdd p) hfreq
  · rw [Real.norm_of_nonneg hρ₁0.le, Real.norm_of_nonneg (by linarith)]; linarith
  · rw [Real.norm_of_nonneg (by linarith)]; exact hρ₂
  · refine Eventually.of_forall fun q => ?_
    have := hrec (q + 1) (by omega)
    rw [Nat.add_sub_cancel, show q + 1 + 1 = q + 2 by ring] at this
    exact this

end DLMF.Lame
