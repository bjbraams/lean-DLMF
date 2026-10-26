/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import DLMF.Heun.LocalSolutions

/-!
# Heun functions, Heun polynomials and orthogonality (DLMF §§31.4–31.6, 31.9)

* §31.4: for discrete values `q_m` of the accessory parameter `Hl(a, q_m; …; z)` is analytic at
  `z = 1`, hence in `|z| < |a|` (`IsHeunEigenvalue01`, `heunFunction01`); the eigenvalues form an
  infinite discrete set and satisfy the continued-fraction equation 31.4.2.
* §31.5: for `α = -n` and `q` an eigenvalue of the tridiagonal matrix 31.5.1 the series of `Hl`
  terminates: the Heun polynomial `heunPoly` (31.5.2) of degree `n`.
* §31.6: path-multiplicative solutions (definition `IsPathMultiplicative` in Basic).
* §31.9: the single orthogonality of `(0,1)Hf_m` over the Pochhammer double loop
  `(1+, 0+, 1-, 0-)` with the normalization 31.9.3–31.9.4, and the double orthogonality 31.9.5 of
  Heun polynomials.

The index `m` of `q_m`, `(s₁,s₂)Hf_m`, `Hp_{n,m}` is not modelled (DLMF fixes no ordering of
the eigenvalues); statements are about eigenvalues `q`. The predicate `IsHeunFunctionOn` covers
finite pairs `s₁, s₂ ∈ {0, 1, a}` only. Contour integrals use `continuedPathIntegral` along the
explicit loop `pochhammerLoop` (four circles through the base point), with branches continued
along the path and principal values at the start (`localBranchCpow`).

Numerical checks (mpmath): the continued fraction 31.4.2 at an eigenvalue `q₀ ≈ 0.25992` for
`a = 3, α = 0.4, β = 1.2, γ = 0.7, δ = 0.6`; the Pochhammer integral 31.9.2 for the two
eigenvalues `q ≈ -2.9348, 0.25992` (off-diagonal `< 10⁻¹⁹`, diagonal equal to `θ_m` of 31.9.3 to
ten digits); Heun polynomials for `n ≤ 3` (terminating series, ODE residuals `< 10⁻²⁷`).
-/

@[expose] public section

open Complex Filter Set Polynomial
open scoped Topology Real

noncomputable section

namespace DLMF.Heun

variable {a q α β γ δ ε : ℂ}

/-! ### Heun functions (§31.4) -/

/-- DLMF §31.4: if `q = q_m` is an eigenvalue for the pair `(0, 1)` and `|a| > 1`, then
`Hl(a, q_m; α, β, γ, δ; ·)` continues analytically to the whole disk `|z| < |a|`, as a solution
of Heun's equation there (away from `0` and `1`). -/
@[dlmf 31.4, dlmf 31.4.E1]
theorem IsHeunEigenvalue01.analyticOn_ball (ha : 1 < ‖a‖) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ))
    (h : IsHeunEigenvalue01 a q α β γ δ) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f (Metric.ball 0 ‖a‖) ∧ f =ᶠ[𝓝 0] heunLocal a q α β γ δ ∧
      IsHeunSolOn a q α β γ δ (heunEps α β γ δ) f (Metric.ball 0 ‖a‖ \ {0, 1}) := by
  sorry

/-- DLMF 31.4.1: on the unit disk the Heun function `(0,1)Hf_m` is `Hl(a, q_m; …)` itself. -/
@[dlmf 31.4.E1]
theorem heunFunction01_eq_heunLocal (ha : 1 < ‖a‖) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ))
    (h : IsHeunEigenvalue01 a q α β γ δ) {z : ℂ} (hz : ‖z‖ < 1) :
    heunFunction01 a q α β γ δ z = heunLocal a q α β γ δ z := by
  obtain ⟨f, hf, hf0, -⟩ := h.analyticOn_ball ha hγ
  have hE : ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f (Metric.ball 0 ‖a‖) ∧
      f =ᶠ[𝓝 0] heunLocal a q α β γ δ := ⟨f, hf, hf0⟩
  have hza : z ∈ Metric.ball (0 : ℂ) ‖a‖ := mem_ball_zero_iff.2 (hz.trans ha)
  have ha0 : a ≠ 0 := norm_pos_iff.1 (one_pos.trans ha)
  have hrad : heunLocalRadius a = 1 := min_eq_left ha.le
  unfold heunFunction01
  rw [dite_eq_left_of_eq_true (eq_true hE), ite_eq_left_of_eq_true _ _ (eq_true hza)]
  obtain ⟨hg, hg0⟩ := hE.choose_spec
  have hHl := (heunLocal_isHeunSolOn (q := q) (α := α) (β := β) (δ := δ) ha0 hγ).1
  rw [hrad] at hHl
  have hsub : Metric.ball (0 : ℂ) 1 ⊆ Metric.ball 0 ‖a‖ := Metric.ball_subset_ball ha.le
  exact (hg.mono hsub).eqOn_of_preconnected_of_eventuallyEq hHl
    (convex_ball _ _).isPreconnected (Metric.mem_ball_self one_pos) hg0 (mem_ball_zero_iff.2 hz)

/-- DLMF §31.4: the eigenvalues `q_m`, `m = 0, 1, 2, …`, form an infinite discrete set: there are
infinitely many, and only finitely many in each disk. Stated for `|a| > 1`, `γ ∉ {0, -1, …}` and
`δ ∉ ℤ` (so that analyticity at `1` is a single condition on `q`, the vanishing of the entire
connection coefficient of the exponent `1 - δ` solution at `1`). -/
@[dlmf 31.4]
theorem heunEigenvalue01_infinite_discrete (ha : 1 < ‖a‖) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ))
    (hδ : ∀ n : ℤ, δ ≠ n) :
    {q | IsHeunEigenvalue01 a q α β γ δ}.Infinite ∧
      ∀ R : ℝ, {q | IsHeunEigenvalue01 a q α β γ δ ∧ ‖q‖ ≤ R}.Finite := by
  sorry

/-- DLMF 31.4.2: an eigenvalue `q_m` satisfies the continued-fraction equation
`q = aγP₁/(Q₁ + q - R₁P₂/(Q₂ + q - R₂P₃/(Q₃ + q - ⋯)))`: the approximants converge to `q`.
Hypotheses: `|a| > 1`, `α, β, γ ∉ {0, -1, -2, …}` (all partial numerators `R_{j-1}P_j` nonzero)
and no Maclaurin coefficient `c_j` of `Hl` vanishes (so that the ratios `c_j/c_{j-1}`, the tails
of the fraction by Pincherle's theorem, are defined). -/
@[dlmf 31.4.E2]
theorem tendsto_heunCFApprox (ha : 1 < ‖a‖) (hα : ∀ n : ℕ, α ≠ -(n : ℂ))
    (hβ : ∀ n : ℕ, β ≠ -(n : ℂ)) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ))
    (hc : ∀ j, heunLocalCoeff a q α β γ δ j ≠ 0) (h : IsHeunEigenvalue01 a q α β γ δ) :
    Tendsto (heunCFApprox a q α β γ δ) atTop (𝓝 q) := by
  sorry

/-! ### Heun polynomials (§31.5) -/

/-- Row `i` of `heunPolyMatrix` applied to a vector extended by zero. -/
theorem p2h_row (a β γ δ : ℂ) (n : ℕ) (w : ℕ → ℂ) (hw : w (n + 1) = 0) (i : Fin (n + 1)) :
    ∑ k : Fin (n + 1), heunPolyMatrix a β γ δ n i k * w k =
      if (i : ℕ) = 0 then a * γ * w 1 else
        heunRecP (-(n : ℂ)) β i * w (i - 1) - heunRecQ a (-(n : ℂ)) β γ δ i * w i +
          heunRecR a γ i * w (i + 1) := by
  simp only [heunPolyMatrix]
  rw [Fin.sum_univ_eq_sum_range (fun k => (if (i : ℕ) = 0 then (if k = 1 then a * γ else 0)
    else if k + 1 = i then heunRecP (-(n : ℂ)) β i
    else if k = i then -heunRecQ a (-(n : ℂ)) β γ δ i
    else if k = i + 1 then heunRecR a γ i
    else 0) * w k) (n + 1)]
  have hi := i.2
  split_ifs with h0
  · rw [Finset.sum_eq_single 1]
    · simp
    · intro b _ hb; simp [hb]
    · intro h1; simp at h1
      have : n = 0 := by omega
      subst this; simp [hw]
  · have e : ∀ k : ℕ, ((if k + 1 = (i : ℕ) then heunRecP (-(n : ℂ)) β i
        else if k = i then -heunRecQ a (-(n : ℂ)) β γ δ i
        else if k = i + 1 then heunRecR a γ i else 0) * w k) =
        (if k = (i : ℕ) - 1 then heunRecP (-(n : ℂ)) β i * w ((i : ℕ) - 1) else 0) +
        (if k = (i : ℕ) then -heunRecQ a (-(n : ℂ)) β γ δ i * w i else 0) +
        (if k = (i : ℕ) + 1 then heunRecR a γ i * w ((i : ℕ) + 1) else 0) := by
      intro k
      by_cases h1 : k + 1 = (i : ℕ)
      · have : k = (i : ℕ) - 1 := by omega
        subst this; simp [h1]; omega
      · by_cases h2 : k = (i : ℕ)
        · subst h2; simp; omega
        · by_cases h3 : k = (i : ℕ) + 1
          · subst h3; simp [h1]; omega
          · have : k ≠ (i : ℕ) - 1 := by omega
            simp [h1, h2, h3, this]
    simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
    have h1 : (i : ℕ) - 1 < n + 1 := by omega
    simp only [h1, hi, ite_true]
    by_cases h3 : (i : ℕ) + 1 < n + 1
    · simp only [h3, ite_true]; ring
    · have : (i : ℕ) = n := by omega
      rw [ite_eq_right_iff.mpr (fun h => absurd h h3), this, hw]; ring


/-- For an eigenvalue `q` of `heunPolyMatrix`, the last row of the eigen-equation holds for the
coefficients of `Hl(a, q; -n, …)`: `q = 0` if `n = 0`, and
`(Q_n + q)c_n - P_n c_{n-1} = 0` if `n ≥ 1`. -/
theorem p2h_eigen {a q β γ δ : ℂ} (ha : a ≠ 0) {n : ℕ}
    (hγ : ∀ k : ℕ, k < n → γ ≠ -(k : ℂ))
    (hq : (heunPolyMatrix a β γ δ n).charpoly.IsRoot q) :
    (n = 0 → q = 0) ∧ ∀ m : ℕ, n = m + 1 →
      (heunRecQ a (-((m + 1 : ℕ) : ℂ)) β γ δ (m + 1) + q) *
        heunLocalCoeff a q (-((m + 1 : ℕ) : ℂ)) β γ δ (m + 1) -
      heunRecP (-((m + 1 : ℕ) : ℂ)) β (m + 1) *
        heunLocalCoeff a q (-((m + 1 : ℕ) : ℂ)) β γ δ m = 0 := by
  set M := heunPolyMatrix a β γ δ n
  have hdet : (Matrix.scalar (Fin (n + 1)) q - M).det = 0 := by
    rw [← Matrix.eval_charpoly]; exact hq
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set w : ℕ → ℂ := fun j => if h : j < n + 1 then v ⟨j, h⟩ else 0 with hwdef
  have hw : w (n + 1) = 0 := by simp [w]
  have hwv : ∀ k : Fin (n + 1), w k = v k := fun k => by
    show (if h : (k : ℕ) < n + 1 then v ⟨k, h⟩ else 0) = v k
    simp [k.2]
  have hrow : ∀ i : Fin (n + 1), q * w i = ∑ k : Fin (n + 1), M i k * w k := by
    intro i
    have h := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, Pi.zero_apply] at h
    simp only [hwv]
    linear_combination h
  set c := heunLocalCoeff a q (-(n : ℂ)) β γ δ with hc
  have hR : ∀ j : ℕ, j < n → heunRecR a γ j ≠ 0 := by
    intro j hj
    unfold heunRecR
    refine mul_ne_zero (mul_ne_zero ha (by norm_cast)) fun h0 => hγ j hj ?_
    linear_combination h0
  have hmain : ∀ j : ℕ, (j ≤ n → w j = w 0 * c j) ∧ (j + 1 ≤ n → w (j + 1) = w 0 * c (j + 1)) := by
    intro j
    induction j with
    | zero =>
      refine ⟨fun _ => by simp [c], fun h1 => ?_⟩
      have h := hrow ⟨0, by omega⟩
      rw [p2h_row a β γ δ n w hw] at h
      simp only [ite_true] at h
      have hγ0 : γ ≠ 0 := by simpa using hγ 0 (by omega)
      show w 1 = w 0 * (q / (a * γ))
      field_simp
      linear_combination -h
    | succ j ih =>
      refine ⟨ih.2, fun h2 => ?_⟩
      have h := hrow ⟨j + 1, by omega⟩
      rw [p2h_row a β γ δ n w hw] at h
      simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] at h
      have hRj := hR (j + 1) (by omega)
      have e1 := ih.1 (by omega)
      have e2 := ih.2 (by omega)
      have hc2 : c (j + 1 + 1) = ((heunRecQ a (-(n : ℂ)) β γ δ (j + 1) + q) * c (j + 1) -
          heunRecP (-(n : ℂ)) β (j + 1) * c j) / heunRecR a γ (j + 1) := rfl
      rw [hc2]
      field_simp
      rw [e1, e2] at h
      linear_combination -h
  have hw0 : w 0 ≠ 0 := by
    intro h0
    apply hv0
    funext k
    rw [← hwv k, (hmain k).1 (by omega), h0, zero_mul, Pi.zero_apply]
  rcases n with _ | m
  · have h := hrow ⟨0, by omega⟩
    rw [p2h_row a β γ δ 0 w hw] at h
    simp only [ite_true] at h
    rw [show w 1 = 0 from hw, mul_zero] at h
    refine ⟨fun _ => ?_, fun m hm => by omega⟩
    rcases mul_eq_zero.1 h with h | h
    · exact h
    · exact absurd h hw0
  · have h := hrow ⟨m + 1, by omega⟩
    rw [p2h_row a β γ δ (m + 1) w hw] at h
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, hw, mul_zero, add_zero] at h
    have e1 := (hmain m).1 (by omega)
    have e2 := (hmain (m + 1)).1 (by omega)
    refine ⟨fun h => by omega, fun m' hm' => ?_⟩
    rw [show m' = m by omega]
    have hnum : (heunRecQ a (-((m + 1 : ℕ) : ℂ)) β γ δ (m + 1) + q) * c (m + 1) -
        heunRecP (-((m + 1 : ℕ) : ℂ)) β (m + 1) * c m = 0 := by
      refine (mul_eq_zero.1 ?_).resolve_left hw0
      push_cast at h e1 e2 ⊢
      rw [e1, e2] at h
      linear_combination h
    exact hnum

/-- For an eigenvalue `q` of `heunPolyMatrix`, the coefficient `c_{n+1}` of `Hl(a, q; -n, …)`
vanishes. -/
theorem p2h_coeff_succ_eq_zero {a q β γ δ : ℂ} (ha : a ≠ 0) {n : ℕ}
    (hγ : ∀ k : ℕ, k < n → γ ≠ -(k : ℂ))
    (hq : (heunPolyMatrix a β γ δ n).charpoly.IsRoot q) :
    heunLocalCoeff a q (-(n : ℂ)) β γ δ (n + 1) = 0 := by
  obtain ⟨h0, h1⟩ := p2h_eigen ha hγ hq
  rcases n with _ | m
  · simp [h0 rfl]
  · have h := h1 m rfl
    show (_ - _) / _ = 0
    rw [h, zero_div]

/-- For an eigenvalue `q` of `heunPolyMatrix`, the coefficients `c_j` of `Hl(a, q; -n, …)`
vanish for `j > n`. -/
theorem p2h_coeff_eq_zero {a q β γ δ : ℂ} (ha : a ≠ 0) {n : ℕ}
    (hγ : ∀ k : ℕ, k < n → γ ≠ -(k : ℂ))
    (hq : (heunPolyMatrix a β γ δ n).charpoly.IsRoot q) {j : ℕ} (hj : n < j) :
    heunLocalCoeff a q (-(n : ℂ)) β γ δ j = 0 := by
  set c := heunLocalCoeff a q (-(n : ℂ)) β γ δ with hc
  have h1 : c (n + 1) = 0 := p2h_coeff_succ_eq_zero ha hγ hq
  have key : ∀ k, c (n + 1 + k) = 0 ∧ c (n + 1 + k + 1) = 0 := by
    intro k
    induction k with
    | zero =>
      refine ⟨h1, ?_⟩
      have : c (n + 1 + 0 + 1) = ((heunRecQ a (-(n : ℂ)) β γ δ (n + 1) + q) * c (n + 1) -
          heunRecP (-(n : ℂ)) β (n + 1) * c n) / heunRecR a γ (n + 1) := rfl
      rw [this, h1]
      simp [heunRecP]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have : c (n + 1 + (k + 1) + 1) = ((heunRecQ a (-(n : ℂ)) β γ δ (n + 1 + k + 1) + q) *
          c (n + 1 + k + 1) - heunRecP (-(n : ℂ)) β (n + 1 + k + 1) * c (n + 1 + k)) /
          heunRecR a γ (n + 1 + k + 1) := rfl
      rw [this, ih.1, ih.2]
      simp
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hj
  have := (key k).1
  rwa [add_right_comm] at this

/-- The leading coefficient `c_n` of the Heun polynomial is nonzero. -/
theorem p2h_coeff_n_ne_zero {a q β γ δ : ℂ} (ha : a ≠ 0) {n : ℕ}
    (hγ : ∀ k : ℕ, k < n → γ ≠ -(k : ℂ)) (hβ : ∀ k : ℕ, k < n → β ≠ -(k : ℂ))
    (hq : (heunPolyMatrix a β γ δ n).charpoly.IsRoot q) :
    heunLocalCoeff a q (-(n : ℂ)) β γ δ n ≠ 0 := by
  set c := heunLocalCoeff a q (-(n : ℂ)) β γ δ with hc
  intro hn
  have hR : ∀ j : ℕ, j < n → heunRecR a γ j ≠ 0 := by
    intro j hj
    unfold heunRecR
    refine mul_ne_zero (mul_ne_zero ha (by norm_cast)) fun h0 => hγ j hj ?_
    linear_combination h0
  have hP : ∀ j : ℕ, 1 ≤ j → j ≤ n → heunRecP (-(n : ℂ)) β j ≠ 0 := by
    intro j hj1 hjn
    unfold heunRecP
    refine mul_ne_zero ?_ ?_
    · intro h0
      have : ((j : ℕ) : ℂ) = ((n + 1 : ℕ) : ℂ) := by push_cast; linear_combination h0
      have := Nat.cast_injective this
      omega
    · intro h0
      apply hβ (j - 1) (by omega)
      push_cast [Nat.cast_sub hj1]
      linear_combination h0
  have h1 := p2h_coeff_succ_eq_zero ha hγ hq
  obtain ⟨-, hres⟩ := p2h_eigen ha hγ hq
  -- downward induction
  have key : ∀ k, k ≤ n → c (n - k) = 0 ∧ c (n - k + 1) = 0 := by
    intro k
    induction k with
    | zero => intro _; simpa using ⟨hn, h1⟩
    | succ k ih =>
      intro hk
      obtain ⟨e0, e1⟩ := ih (by omega)
      refine ⟨?_, by rwa [show n - (k + 1) + 1 = n - k by omega]⟩
      set j := n - k with hj
      have hj1 : 1 ≤ j := by omega
      have hPj := hP j hj1 (by omega)
      rw [show n - (k + 1) = j - 1 by omega]
      have hrel : heunRecP (-(n : ℂ)) β j * c (j - 1) = 0 := by
        by_cases hjn : j = n
        · obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          have h := hres m hm
          subst hm
          rw [hjn] at e0 ⊢
          simp only [Nat.add_sub_cancel]
          rw [hc] at e0
          rw [e0, mul_zero, zero_sub, neg_eq_zero] at h
          exact h
        · obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          have hRj := hR j (by omega)
          have hdef : c (i + 1 + 1) = ((heunRecQ a (-(n : ℂ)) β γ δ (i + 1) + q) * c (i + 1) -
              heunRecP (-(n : ℂ)) β (i + 1) * c i) / heunRecR a γ (i + 1) := rfl
          rw [hi] at e0 e1 hRj ⊢
          rw [e1, e0, mul_zero, zero_sub, eq_comm, div_eq_zero_iff] at hdef
          simp only [Nat.add_sub_cancel]
          rcases hdef with h | h
          · exact neg_eq_zero.1 h
          · exact absurd h hRj
      exact (mul_eq_zero.1 hrel).resolve_left hPj
  have := (key n le_rfl).1
  simp [c] at this

/-- The coefficients of the Heun polynomial satisfy every equation of the recurrence. -/
theorem p2h_p1hE_eq_zero {a q β γ δ : ℂ} (ha : a ≠ 0) {n : ℕ}
    (hγ : ∀ k : ℕ, k < n → γ ≠ -(k : ℂ))
    (hq : (heunPolyMatrix a β γ δ n).charpoly.IsRoot q) (k : ℕ) :
    p1hE a q (-(n : ℂ)) β γ δ (heunLocalCoeff a q (-(n : ℂ)) β γ δ) k = 0 := by
  set c := heunLocalCoeff a q (-(n : ℂ)) β γ δ with hc
  obtain ⟨h0, hres⟩ := p2h_eigen ha hγ hq
  have hz : ∀ j, n < j → c j = 0 := fun j hj => p2h_coeff_eq_zero ha hγ hq hj
  rcases k with _ | _ | j
  · exact p1hE_zero _ _ _ _ _ _ _
  · rw [p1hE_one, hc, heunLocalCoeff_one, heunLocalCoeff_zero]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [h0 hn]
    · have hγ0 : γ ≠ 0 := by simpa using hγ 0 hn
      field_simp
      ring
  · rw [p1hE_add_two]
    rcases lt_trichotomy (j + 1) n with hj | hj | hj
    · have hR : heunRecR a γ (j + 1) ≠ 0 := by
        unfold heunRecR
        refine mul_ne_zero (mul_ne_zero ha (by norm_cast)) fun h0 => hγ (j + 1) hj ?_
        linear_combination h0
      have hdef : c (j + 2) = ((heunRecQ a (-(n : ℂ)) β γ δ (j + 1) + q) * c (j + 1) -
          heunRecP (-(n : ℂ)) β (j + 1) * c j) / heunRecR a γ (j + 1) := rfl
      rw [hdef, mul_div_cancel₀ _ hR]
      ring
    · have h := hres j hj.symm
      subst hj
      rw [hz (j + 2) (by omega)]
      linear_combination -h
    · rw [hz (j + 2) (by omega), hz (j + 1) hj]
      rcases Nat.lt_or_ge n j with hjn | hjn
      · rw [hz j hjn]; ring
      · have : j = n := by omega
        subst this
        simp [heunRecP]


/-- DLMF 31.5.1–31.5.2: if `α = -n` and `q = q_{n,m}` is an eigenvalue of the matrix 31.5.1,
then (for `a ≠ 0`, `γ ∉ {0, -1, …, 1 - n}`) the coefficients `c_j` of `Hl` vanish for `j > n`, so
`Hl(a, q; -n, β, γ, δ; z)` is the polynomial `Hp_{n,m}(z) = heunPoly a q β γ δ n` for every
`z`. -/
@[dlmf 31.5.E2]
theorem heunLocal_eq_heunPoly (ha : a ≠ 0) {n : ℕ} (hγ : ∀ k : ℕ, k < n → γ ≠ -(k : ℂ))
    (hq : (heunPolyMatrix a β γ δ n).charpoly.IsRoot q) (z : ℂ) :
    (∀ j, n < j → heunLocalCoeff a q (-(n : ℂ)) β γ δ j = 0) ∧
      heunLocal a q (-(n : ℂ)) β γ δ z = (heunPoly a q β γ δ n).eval z := by
  have hc : ∀ j, n < j → heunLocalCoeff a q (-(n : ℂ)) β γ δ j = 0 :=
    fun j hj => p2h_coeff_eq_zero ha hγ hq hj
  refine ⟨hc, ?_⟩
  rw [heunLocal, tsum_eq_sum (s := Finset.range (n + 1)) fun j hj => by
    rw [hc j (by simpa using hj), zero_mul]]
  simp [heunPoly, eval_finsetSum]

/-- DLMF §31.5: the Heun polynomial has degree exactly `n` (for `β ∉ {0, -1, …, 1 - n}`) and is a
solution of Heun's equation analytic at all three finite singularities `0, 1, a`. -/
@[dlmf 31.5, dlmf 31.5.E2]
theorem heunPoly_isHeunSolOn (ha : a ≠ 0) {n : ℕ} (hγ : ∀ k : ℕ, k < n → γ ≠ -(k : ℂ))
    (hβ : ∀ k : ℕ, k < n → β ≠ -(k : ℂ))
    (hq : (heunPolyMatrix a β γ δ n).charpoly.IsRoot q) :
    (heunPoly a q β γ δ n).natDegree = n ∧
      IsHeunSolOn a q (-(n : ℂ)) β γ δ (heunEps (-(n : ℂ)) β γ δ)
        (fun z => (heunPoly a q β γ δ n).eval z) {z | z ≠ 0 ∧ z ≠ 1 ∧ z ≠ a} := by
  set P := heunPoly a q β γ δ n with hPdef
  set c := heunLocalCoeff a q (-(n : ℂ)) β γ δ with hc
  have hcoeff : P.coeff n = c n := by
    simp [P, heunPoly, finsetSum_coeff, c]
  refine ⟨natDegree_eq_of_le_of_coeff_ne_zero ?_ (hcoeff ▸ p2h_coeff_n_ne_zero ha hγ hβ hq), ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (by simpa [Nat.lt_succ_iff] using hj)
  set f : ℂ → ℂ := fun z => P.eval z with hfdef
  have hf : heunLocal a q (-(n : ℂ)) β γ δ = f :=
    funext fun z => (heunLocal_eq_heunPoly ha hγ hq z).2
  have hps := p1h_hasFPowerSeriesOnBall (q := q) (α := -(n : ℂ)) (β := β) (γ := γ) (δ := δ) ha
  rw [hf] at hps
  have hd1 : deriv f = fun z => P.derivative.eval z := funext fun z => Polynomial.deriv P
  have hd2 : deriv (deriv f) = fun z => P.derivative.derivative.eval z := by
    rw [hd1]; exact funext fun z => Polynomial.deriv _
  set g : ℂ → ℂ := fun z => z * (heunOperator a (-(n : ℂ)) β γ δ (heunEps (-(n : ℂ)) β γ δ) f z -
    q * f z) with hgdef
  have hgball : ∀ z ∈ Metric.ball (0 : ℂ) (heunLocalRadius a), g z = 0 := by
    intro z hz
    have hz' : z ∈ Metric.eball (0 : ℂ) (ENNReal.ofReal (heunLocalRadius a)) := by
      rwa [Metric.eball_ofReal]
    have hT := p1h_hasSum_heunOperator (a := a) (q := q) (α := -(n : ℂ)) (β := β) (γ := γ)
      (δ := δ) hps hz'
    refine hT.unique ?_
    convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0) using 1
    funext k
    rw [p2h_p1hE_eq_zero ha hγ hq k, zero_mul]
  have hgd : Differentiable ℂ g := by
    have : g = fun z => z * (z * (z - 1) * (z - a) * P.derivative.derivative.eval z +
        (γ * (z - 1) * (z - a) + δ * z * (z - a) + heunEps (-(n : ℂ)) β γ δ * z * (z - 1)) *
          P.derivative.eval z + -(n : ℂ) * β * z * P.eval z - q * P.eval z) := by
      funext z
      simp only [g, heunOperator, f]
      rw [hd2, hd1]
    rw [this]
    fun_prop
  have hgA : AnalyticOnNhd ℂ g univ := fun z _ => hgd.analyticAt z
  have hg0 : EqOn g 0 univ := hgA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ 0) (by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (p1h_radius_pos ha)] with z hz
      exact hgball z hz)
  have hs : ∀ z ∈ {z : ℂ | z ≠ 0 ∧ z ≠ 1 ∧ z ≠ a}, z ≠ 0 ∧ z ≠ 1 ∧ z ≠ a := fun z hz => hz
  rw [isHeunSolOn_iff_heunOperator hs]
  intro z hz
  refine ⟨P.differentiable z, ?_, ?_⟩
  · rw [hd1]; exact P.derivative.differentiable z
  · have h := hg0 (mem_univ z)
    simp only [g, Pi.zero_apply] at h
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hz.1)

/-- DLMF §31.5: there are `n + 1` eigenvalues `q_{n,m}`, `m = 0, …, n`, counted with
multiplicity (the characteristic polynomial of the matrix 31.5.1 has degree `n + 1`). -/
@[dlmf 31.5]
theorem heunPolyMatrix_charpoly_natDegree (a β γ δ : ℂ) (n : ℕ) :
    (heunPolyMatrix a β γ δ n).charpoly.natDegree = n + 1 := by
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

/-! ### Orthogonality (§31.9) -/

/-- DLMF 31.9.2 (off-diagonal): for two distinct eigenvalues `q_m ≠ q_k` for the pair `(0, 1)`,
`∫_ζ^{(1+,0+,1-,0-)} t^{γ-1}(1-t)^{δ-1}(t-a)^{ε-1} w_m(t) w_k(t) dt = 0`, where
`w = (0,1)Hf(a, q; α, β, γ, δ; ·)`, `ζ ∈ (0, 1)`, the branches are continuous on the path and
principal at the beginning, and `a` lies outside the two circles of the loop
(`|a| > ζ`, `|a - 1| > 1 - ζ`). -/
@[dlmf 31.9.E1, dlmf 31.9.E2]
theorem heun_orthogonality_ne (ha : 1 < ‖a‖) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ))
    (hδ : ∀ n : ℕ, δ ≠ -(n : ℂ)) {ζ : ℝ} (hζ : ζ ∈ Ioo (0 : ℝ) 1) (ha1 : 1 - ζ < ‖a - 1‖)
    {q₁ q₂ : ℂ} (h₁ : IsHeunEigenvalue01 a q₁ α β γ δ) (h₂ : IsHeunEigenvalue01 a q₂ α β γ δ)
    (hne : q₁ ≠ q₂) :
    continuedPathIntegral (pochhammerLoop 0 1 ζ)
      (fun t => localBranchCpow ζ (γ - 1) t * localBranchCpow (1 - ζ) (δ - 1) (1 - t) *
        localBranchCpow (ζ - a) (heunEps α β γ δ - 1) (t - a) *
        heunLocal a q₁ α β γ δ t * heunLocal a q₂ α β γ δ t) = 0 := by
  sorry

/-- DLMF 31.9.2–31.9.4 (diagonal): for an eigenvalue `q_m` the Pochhammer integral of
`t^{γ-1}(1-t)^{δ-1}(t-a)^{ε-1} w_m(t)²` equals
`θ_m = (1 - e^{2πiγ})(1 - e^{2πiδ}) ζ^γ (1-ζ)^δ (ζ-a)^ε (f₀/f₁)(q_m, ζ)
∂_q 𝒲{f₀(q, ζ), f₁(q, ζ)}|_{q = q_m}`, with `f₀(q, z) = Hl(a, q; α, β, γ, δ; z)`,
`f₁(q, z) = Hl(1 - a, αβ - q; α, β, δ, γ; 1 - z)` and the Wronskian
`𝒲{f₀, f₁} = f₀ ∂_z f₁ - ∂_z f₀ f₁` (principal powers). -/
@[dlmf 31.9.E2, dlmf 31.9.E3, dlmf 31.9.E4]
theorem heun_orthogonality_self (ha : 1 < ‖a‖) (hγ : ∀ n : ℕ, γ ≠ -(n : ℂ))
    (hδ : ∀ n : ℕ, δ ≠ -(n : ℂ)) {ζ : ℝ} (hζ : ζ ∈ Ioo (0 : ℝ) 1) (ha1 : 1 - ζ < ‖a - 1‖)
    {qm : ℂ} (hm : IsHeunEigenvalue01 a qm α β γ δ) :
    continuedPathIntegral (pochhammerLoop 0 1 ζ)
      (fun t => localBranchCpow ζ (γ - 1) t * localBranchCpow (1 - ζ) (δ - 1) (1 - t) *
        localBranchCpow (ζ - a) (heunEps α β γ δ - 1) (t - a) *
        heunLocal a qm α β γ δ t * heunLocal a qm α β γ δ t) =
      (1 - cexp (2 * π * I * γ)) * (1 - cexp (2 * π * I * δ)) * (ζ : ℂ) ^ γ *
        (1 - (ζ : ℂ)) ^ δ * ((ζ : ℂ) - a) ^ heunEps α β γ δ *
        (heunLocal a qm α β γ δ ζ / heunLocal (1 - a) (α * β - qm) α β δ γ (1 - ζ)) *
        deriv (fun q => heunLocal a q α β γ δ ζ *
            deriv (fun z => heunLocal (1 - a) (α * β - q) α β δ γ (1 - z)) ζ -
          deriv (fun z => heunLocal a q α β γ δ z) ζ *
            heunLocal (1 - a) (α * β - q) α β δ γ (1 - ζ)) qm := by
  sorry

/-- DLMF 31.9.5–31.9.6, double orthogonality of Heun polynomials. Fix `a, γ, δ, ε`; for
`i = 1, 2` let `w_i = Hp_{n_i}(a, q_i; -n_i, β_i, γ, δ; ·)` with `β_i = γ + δ + ε - 1 + n_i`
(so that `ε` is the same) and `q_i` an eigenvalue of the matrix 31.5.1, the two being different.
For Pochhammer loops `𝓛₁`, `𝓛₂` around two distinct pairs `{p₁, p₂}`, `{p₃, p₄}` of
singularities from `{0, 1, a}` (base points `ζ₁, ζ₂` on the joining segments, the third
singularity outside both circles of each loop),
`∫_{𝓛₁}∫_{𝓛₂} ρ(s,t) w₁(s)w₁(t)w₂(s)w₂(t) ds dt = 0` with
`ρ(s,t) = (s-t)(st)^{γ-1}((s-1)(t-1))^{δ-1}((s-a)(t-a))^{ε-1}`. Since `ρ(s,t) = (s-t)h(s)h(t)`,
the double integral is stated in its factorized form
`(∫_{𝓛₁} s u(s) ds)(∫_{𝓛₂} u(t) dt) - (∫_{𝓛₁} u(s) ds)(∫_{𝓛₂} t u(t) dt)`,
`u = h w₁ w₂`, `h(x) = x^{γ-1}(x-1)^{δ-1}(x-a)^{ε-1}` (any initial branch). -/
@[dlmf 31.9.E5, dlmf 31.9.E6]
theorem heunPoly_double_orthogonality (ha0 : a ≠ 0) (ha1 : a ≠ 1) {n₁ n₂ : ℕ} {q₁ q₂ : ℂ}
    (hγ : ∀ k : ℕ, γ ≠ -(k : ℂ)) (hδ : ∀ k : ℕ, δ ≠ -(k : ℂ))
    (hq₁ : (heunPolyMatrix a (γ + δ + ε - 1 + n₁) γ δ n₁).charpoly.IsRoot q₁)
    (hq₂ : (heunPolyMatrix a (γ + δ + ε - 1 + n₂) γ δ n₂).charpoly.IsRoot q₂)
    (hne : n₁ ≠ n₂ ∨ q₁ ≠ q₂) {p₁ p₂ p₃ p₄ ζ₁ ζ₂ : ℂ}
    (hp : ∀ p ∈ ({p₁, p₂, p₃, p₄} : Set ℂ), p = 0 ∨ p = 1 ∨ p = a)
    (hp₁₂ : p₁ ≠ p₂) (hp₃₄ : p₃ ≠ p₄) (hpairs : ({p₁, p₂} : Set ℂ) ≠ {p₃, p₄})
    (hζ₁ : ∃ s ∈ Ioo (0 : ℝ) 1, ζ₁ = p₁ + s * (p₂ - p₁))
    (hζ₂ : ∃ s ∈ Ioo (0 : ℝ) 1, ζ₂ = p₃ + s * (p₄ - p₃))
    (hout₁ : ∀ r ∈ ({0, 1, a} : Set ℂ), r ≠ p₁ → r ≠ p₂ →
      ‖ζ₁ - p₁‖ < ‖r - p₁‖ ∧ ‖ζ₁ - p₂‖ < ‖r - p₂‖)
    (hout₂ : ∀ r ∈ ({0, 1, a} : Set ℂ), r ≠ p₃ → r ≠ p₄ →
      ‖ζ₂ - p₃‖ < ‖r - p₃‖ ∧ ‖ζ₂ - p₄‖ < ‖r - p₄‖) :
    let u : ℂ → ℂ → ℂ := fun ζ x => localBranchCpow ζ (γ - 1) x *
      localBranchCpow (ζ - 1) (δ - 1) (x - 1) * localBranchCpow (ζ - a) (ε - 1) (x - a) *
      (heunPoly a q₁ (γ + δ + ε - 1 + n₁) γ δ n₁).eval x *
      (heunPoly a q₂ (γ + δ + ε - 1 + n₂) γ δ n₂).eval x
    continuedPathIntegral (pochhammerLoop p₁ p₂ ζ₁) (fun s => s * u ζ₁ s) *
        continuedPathIntegral (pochhammerLoop p₃ p₄ ζ₂) (u ζ₂) -
      continuedPathIntegral (pochhammerLoop p₁ p₂ ζ₁) (u ζ₁) *
        continuedPathIntegral (pochhammerLoop p₃ p₄ ζ₂) (fun t => t * u ζ₂ t) = 0 := by
  sorry

end DLMF.Heun
