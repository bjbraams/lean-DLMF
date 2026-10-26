/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Data.Nat.Choose.Basic

/-!
# The general Fuchsian equation and Stieltjes polynomials (DLMF §§31.14–31.15)

* §31.14(i): the general Fuchsian equation 31.14.1 (`IsFuchsianSolOn`, DLMF/Heun/Basic.lean):
  the exponents `{0, 1-γ_j}` at `a_j` and `{α, β}` at `∞` with 31.14.2, the case `N = 3`
  (Heun's equation, proved), the normal form 31.14.3–31.14.5 and `∑ q̃_j = 0` (proved; it holds
  without the condition `∑ q_j = 0`, stronger than DLMF).
* §31.15: Stieltjes and Van Vleck polynomials (`IsVanVleckStieltjes`), the bound on their
  number, the equilibrium equations 31.15.2–31.15.3, the critical points of `G` (31.15.4), the
  existence and uniqueness of `S_𝐦` under 31.15.5–31.15.6 and the accessory parameters 31.15.7,
  the orthogonality of the products 31.15.8–31.15.12 and their completeness in `L²_ρ(Q)`.

The real configuration of §31.15(ii)–(iii) uses `N + 1` singular points `a_0 < ⋯ < a_N`
(DLMF's `N`), so the box `Q` has `N` factors and DLMF's count `(n+N-2 choose N-2)` becomes
`(n+N-1 choose N-1)`.

The parameter count `3N - 3` (§31.14(i)) and Kovacic's algorithm (§31.14(ii)) are not
acquired: the first is a remark, the second an algorithm. The electrostatic interpretation
(§31.15(ii)) is the reading of 31.15.2 and is covered by it.
-/

@[expose] public section

open Complex Filter Set Polynomial
open scoped Topology

noncomputable section

namespace DLMF.Heun

/-! ### The general Fuchsian equation (§31.14) -/

/-- Helper for DLMF 31.14.2: `(z - c)⁻¹ → 0` as `z → ∞` (in `ℂ`, any `c`). -/
theorem h31_tendsto_sub_inv_cobounded (c : ℂ) :
    Tendsto (fun z : ℂ => (z - c)⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := by
  have : Tendsto (fun z : ℂ => z - c) (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) := by
    simp [sub_eq_add_neg]
  exact tendsto_inv₀_cobounded.comp this

/-- Helper for DLMF 31.14.2: eventually `z - c ≠ 0` as `z → ∞` (in `ℂ`, any `c`). -/
theorem h31_eventually_sub_ne_zero_cobounded (c : ℂ) :
    ∀ᶠ z in Bornology.cobounded ℂ, z - c ≠ 0 := by
  filter_upwards [eventually_cobounded_le_norm (‖c‖ + 1)] with z hz h
  rw [sub_eq_zero] at h; subst h; linarith

/-- DLMF 31.14.1–31.14.2: at a finite singularity `a_j` (the `a_k` distinct) the indicial data
are `lim (z - a_j)p(z) = γ_j` and `lim (z - a_j)² r(z) = 0`, so the exponents are
`{0, 1 - γ_j}`. -/
@[dlmf 31.14.E1]
theorem fuchsian_exponents_finite {N : ℕ} {a : Fin N → ℂ} (ha : Function.Injective a)
    (γ q : Fin N → ℂ) (j : Fin N) :
    Tendsto (fun z => (z - a j) * fuchsianCoeffP a γ z) (𝓝[≠] a j) (𝓝 (γ j)) ∧
    Tendsto (fun z => (z - a j) ^ 2 * fuchsianCoeffR a q z) (𝓝[≠] a j) (𝓝 0) := by
  have hne : ∀ᶠ z in 𝓝[≠] a j, z - a j ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with z hz using sub_ne_zero.mpr hz
  have hc : ∀ k, k ≠ j → ContinuousAt (fun z => (z - a k)⁻¹) (a j) := by
    intro k hk
    exact (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr (ha.ne hk.symm))
  constructor
  · have key : ∀ z, z - a j ≠ 0 → (z - a j) * fuchsianCoeffP a γ z =
        γ j + ∑ k ∈ Finset.univ.erase j, γ k * ((z - a j) * (z - a k)⁻¹) := by
      intro z hz
      simp only [fuchsianCoeffP, Finset.mul_sum]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      congr 1
      · field_simp
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [div_eq_mul_inv]; ring
    have hT : Tendsto (fun z => γ j + ∑ k ∈ Finset.univ.erase j,
        γ k * ((z - a j) * (z - a k)⁻¹)) (𝓝[≠] a j) (𝓝 (γ j + ∑ k ∈ Finset.univ.erase j,
        γ k * ((a j - a j) * (a j - a k)⁻¹))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      refine tendsto_const_nhds.add (tendsto_finsetSum _ fun k hk => ?_)
      exact (((continuousAt_id.sub continuousAt_const).mul
        (hc k (Finset.ne_of_mem_erase hk))).const_mul (γ k)).tendsto
    simp only [sub_self, zero_mul, mul_zero, Finset.sum_const_zero, add_zero] at hT
    exact hT.congr' (by filter_upwards [hne] with z hz using (key z hz).symm)
  · have key : ∀ z, z - a j ≠ 0 → (z - a j) ^ 2 * fuchsianCoeffR a q z =
        (z - a j) * q j + ∑ k ∈ Finset.univ.erase j, q k * ((z - a j) ^ 2 * (z - a k)⁻¹) := by
      intro z hz
      simp only [fuchsianCoeffR, Finset.mul_sum]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      congr 1
      · field_simp
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [div_eq_mul_inv]; ring
    have hT : Tendsto (fun z => (z - a j) * q j + ∑ k ∈ Finset.univ.erase j,
        q k * ((z - a j) ^ 2 * (z - a k)⁻¹)) (𝓝[≠] a j) (𝓝 ((a j - a j) * q j +
        ∑ k ∈ Finset.univ.erase j, q k * ((a j - a j) ^ 2 * (a j - a k)⁻¹))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      refine (((continuousAt_id.sub continuousAt_const).mul continuousAt_const).tendsto).add
        (tendsto_finsetSum _ fun k hk => ?_)
      exact ((((continuousAt_id.sub continuousAt_const).pow 2).mul
        (hc k (Finset.ne_of_mem_erase hk))).const_mul (q k)).tendsto
    simp only [sub_self, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, Finset.sum_const_zero, add_zero] at hT
    exact hT.congr' (by filter_upwards [hne] with z hz using (key z hz).symm)

/-- DLMF 31.14.2: for `∑ q_j = 0` the indicial data at `∞` are `lim z p(z) = ∑ γ_j` and
`lim z² r(z) = ∑ a_j q_j`, so the exponents `{α, β}` at `∞` (solutions `~ z^{-α}, z^{-β}`)
satisfy `α + β + 1 = ∑ γ_j`, `αβ = ∑ a_j q_j`. -/
@[dlmf 31.14.E2, dlmf 31.14.E1]
theorem fuchsian_exponents_infinity {N : ℕ} (a γ q : Fin N → ℂ) (hq : ∑ j, q j = 0) :
    Tendsto (fun z => z * fuchsianCoeffP a γ z) (Bornology.cobounded ℂ) (𝓝 (∑ j, γ j)) ∧
    Tendsto (fun z => z ^ 2 * fuchsianCoeffR a q z) (Bornology.cobounded ℂ)
      (𝓝 (∑ j, a j * q j)) := by
  have hev : ∀ᶠ z in Bornology.cobounded ℂ, ∀ j, z - a j ≠ 0 :=
    Filter.eventually_all.mpr fun j => h31_eventually_sub_ne_zero_cobounded (a j)
  constructor
  · have : Tendsto (fun z => ∑ j, γ j * (1 + a j * (z - a j)⁻¹)) (Bornology.cobounded ℂ)
        (𝓝 (∑ j, γ j)) := by
      have := tendsto_finsetSum (Finset.univ : Finset (Fin N)) fun j _ =>
        ((h31_tendsto_sub_inv_cobounded (a j)).const_mul (a j)).const_add 1 |>.const_mul (γ j)
      simpa using this
    refine this.congr' ?_
    filter_upwards [hev] with z hz
    simp only [fuchsianCoeffP, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp [hz j]
    ring
  · have : Tendsto (fun z => ∑ j, (a j * q j + q j * a j ^ 2 * (z - a j)⁻¹))
        (Bornology.cobounded ℂ) (𝓝 (∑ j, a j * q j)) := by
      have := tendsto_finsetSum (Finset.univ : Finset (Fin N)) fun j _ =>
        ((h31_tendsto_sub_inv_cobounded (a j)).const_mul (q j * a j ^ 2)).const_add (a j * q j)
      simpa using this
    refine this.congr' ?_
    filter_upwards [hev] with z hz
    have h0 : z ^ 2 * fuchsianCoeffR a q z =
        z * ∑ j, q j + ∑ j, (a j * q j + q j * a j ^ 2 * (z - a j)⁻¹) := by
      simp only [fuchsianCoeffR, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp [hz j]
      ring
    rw [h0, hq]; ring

/-- DLMF 31.14.2: the indicial polynomial at `∞`, `ρ(ρ + 1) - (∑ γ_j)ρ + ∑ a_j q_j`, has the
roots `α, β` exactly when `α + β + 1 = ∑ γ_j` and `αβ = ∑ a_j q_j`. -/
@[dlmf 31.14.E2]
theorem fuchsian_indicial_infinity {N : ℕ} (a γ q : Fin N → ℂ) {α β : ℂ}
    (h₁ : α + β + 1 = ∑ j, γ j) (h₂ : α * β = ∑ j, a j * q j) (ρ : ℂ) :
    ρ * (ρ + 1) - (∑ j, γ j) * ρ + ∑ j, a j * q j = (ρ - α) * (ρ - β) := by
  rw [← h₁, ← h₂]; ring

/-- DLMF §31.14(i): Heun's equation is the case `N = 3` of 31.14.1, with
`(a_1, a_2, a_3) = (0, 1, a)`, `(γ_1, γ_2, γ_3) = (γ, δ, ε)` and accessory parameters
`q_1 = -q/a`, `q_2 = (αβ - q)/(1 - a)`, `q_3 = (αβa - q)/(a(a - 1))`; these satisfy
`∑ q_j = 0` and `∑ a_j q_j = αβ` (31.14.2). Off the singular points the two equations coincide. -/
@[dlmf 31.14.E1, dlmf 31.14.E2]
theorem isHeunSolOn_iff_isFuchsianSolOn {a q α β γ δ ε : ℂ} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    {w : ℂ → ℂ} {s : Set ℂ} (hs : ∀ z ∈ s, z ≠ 0 ∧ z ≠ 1 ∧ z ≠ a) :
    let qs : Fin 3 → ℂ := ![-q / a, (α * β - q) / (1 - a), (α * β * a - q) / (a * (a - 1))]
    (∑ j, qs j = 0 ∧ ∑ j, (![0, 1, a] : Fin 3 → ℂ) j * qs j = α * β) ∧
    (IsHeunSolOn a q α β γ δ ε w s ↔ IsFuchsianSolOn ![0, 1, a] ![γ, δ, ε] qs w s) := by
  intro qs
  have ha1' : (1 : ℂ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  have ha1'' : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  have hP : ∀ z, fuchsianCoeffP ![0, 1, a] ![γ, δ, ε] z = heunCoeffP a γ δ ε z := by
    intro z
    simp [fuchsianCoeffP, heunCoeffP, Fin.sum_univ_three]
  have hR : ∀ z ∈ s, fuchsianCoeffR ![0, 1, a] qs z = heunCoeffR a q α β z := by
    intro z hz
    obtain ⟨h0, h1, h2⟩ := hs z hz
    have h1' : z - 1 ≠ 0 := sub_ne_zero.mpr h1
    have h2' : z - a ≠ 0 := sub_ne_zero.mpr h2
    simp only [fuchsianCoeffR, heunCoeffR, Fin.sum_univ_three, qs]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, sub_zero]
    field_simp
    ring
  refine ⟨⟨?_, ?_⟩, ⟨fun h => ⟨h.1, fun z hz => ?_⟩, fun h => ⟨h.1, fun z hz => ?_⟩⟩⟩
  · simp only [Fin.sum_univ_three, qs, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    field_simp
    ring
  · simp only [Fin.sum_univ_three, qs, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    field_simp
    ring
  · rw [hP, hR z hz]; exact h.2 z hz
  · rw [← hP, ← hR z hz]; exact h.2 z hz

/-- DLMF 31.14.4–31.14.5: `∑_j q̃_j = -∑_j q_j`; in particular `∑_j q̃_j = 0` when
`∑_j q_j = 0` (31.14.4). No distinctness of the `a_j` is needed. -/
@[dlmf 31.14.E4, dlmf 31.14.E5]
theorem fuchsianNormalQ_sum {N : ℕ} (a γ q : Fin N → ℂ) :
    ∑ j, fuchsianNormalQ a γ q j = -∑ j, q j := by
  have hS : ∑ j, ∑ k ∈ Finset.univ.erase j, γ j * γ k / (a j - a k) = 0 := by
    have h1 : ∀ j, ∑ k ∈ Finset.univ.erase j, γ j * γ k / (a j - a k) =
        ∑ k, γ j * γ k / (a j - a k) := by
      intro j
      rw [Finset.sum_erase _ (by simp)]
    simp_rw [h1]
    have h2 : ∑ j, ∑ k, γ j * γ k / (a j - a k) = -∑ j, ∑ k, γ j * γ k / (a j - a k) := by
      conv_rhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← neg_sub, div_neg]; ring
    linear_combination (1 / 2 : ℂ) * h2
  simp only [fuchsianNormalQ, Finset.sum_sub_distrib, ← Finset.mul_sum, hS]
  ring

/-- DLMF 31.14.4 (with 31.14.5): `∑_j q̃_j = 0` when `∑_j q_j = 0`. -/
@[dlmf 31.14.E4]
theorem fuchsianNormalQ_sum_eq_zero {N : ℕ} (a γ q : Fin N → ℂ) (hq : ∑ j, q j = 0) :
    ∑ j, fuchsianNormalQ a γ q j = 0 := by
  rw [fuchsianNormalQ_sum, hq, neg_zero]

/-- DLMF 31.14.3–31.14.5, the normal form: if `w` solves 31.14.1 on an open set `U` on which
every `z - a_j` lies in `slitPlane`, then `W(z) = ∏_j (z - a_j)^{γ_j/2} w(z)` (principal powers,
so that `w = ∏_j (z - a_j)^{-γ_j/2} W` as in 31.14.3) solves
`W'' = ∑_j (γ̃_j/(z - a_j)² + q̃_j/(z - a_j)) W` (31.14.4). -/
@[dlmf 31.14.E3, dlmf 31.14.E4, dlmf 31.14.E5]
theorem fuchsian_normalForm {N : ℕ} {a γ q : Fin N → ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hUa : ∀ z ∈ U, ∀ j, z - a j ∈ slitPlane)
    (hw : IsFuchsianSolOn a γ q w U) :
    IsLinearODE2On 0 (fun z => -fuchsianNormalCoeff a γ q z)
      (fun z => (∏ j, (z - a j) ^ (γ j / 2)) * w z) U := by
  sorry

/-! ### Stieltjes polynomials (§31.15) -/

/-- Helper for DLMF 31.15.7: for `S = c ∏_k (X - z_k)` and `S(x) ≠ 0`,
`S'(x) = S(x) ∑_k 1/(x - z_k)`. -/
theorem h31_logDeriv_prod {n : ℕ} (c : ℂ) (z : Fin n → ℂ) (x : ℂ)
    (hx : (C c * ∏ k, (X - C (z k))).eval x ≠ 0) :
    (derivative (C c * ∏ k, (X - C (z k)))).eval x =
      (C c * ∏ k, (X - C (z k))).eval x * ∑ k, 1 / (x - z k) := by
  classical
  have hne : ∀ k, x - z k ≠ 0 := by
    intro k hk
    apply hx
    simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    rw [Finset.prod_eq_zero (Finset.mem_univ k) hk, mul_zero]
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_prod_finset,
    derivative_sub, derivative_X, derivative_C, sub_zero, mul_one, eval_mul, eval_C,
    eval_finsetSum, eval_prod, eval_sub, eval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  field_simp [hne k]

/-- DLMF §31.15(i): for distinct `a_j` there are at most `(n+N-2 choose N-2)` Van Vleck
polynomials `V` (degree `≤ N - 2`) for which 31.15.1 has a polynomial solution of degree `n`. -/
@[dlmf 31.15.i, dlmf 31.15.E1]
theorem vanVleck_card_le {N : ℕ} (hN : 2 ≤ N) {a : Fin N → ℂ} (ha : Function.Injective a)
    (γ : Fin N → ℂ) (n : ℕ) :
    {V : ℂ[X] | ∃ S, IsVanVleckStieltjes a γ n V S}.encard ≤ ((n + N - 2).choose (N - 2) : ℕ) := by
  sorry

/-- DLMF 31.15.2: if `S = c ∏_k (X - z_k)` (`c ≠ 0`) is a Stieltjes polynomial and the zero
`z_k` is none of the `a_j`, then `∑_j (γ_j/2)/(z_k - a_j) + ∑_{j ≠ k} 1/(z_k - z_j) = 0`. -/
@[dlmf 31.15.E2]
theorem stieltjes_zeros_equilibrium {N n : ℕ} {a γ : Fin N → ℂ} {V S : ℂ[X]}
    (hS : IsVanVleckStieltjes a γ n V S) {c : ℂ} {z : Fin n → ℂ}
    (hSz : S = C c * ∏ k, (X - C (z k))) (k : Fin n) (hk : ∀ j, z k ≠ a j) :
    ∑ j, (γ j / 2) / (z k - a j) + ∑ j ∈ Finset.univ.erase k, 1 / (z k - z j) = 0 := by
  sorry

/-- DLMF 31.15.3: if `t` is a zero of the Van Vleck polynomial `V` and
`S' = c ∏_j (X - z'_j)` (`c ≠ 0`, `n ≥ 1`), then either `S'(t) = 0` or (for `t` none of the
`a_j`) `∑_j γ_j/(t - a_j) + ∑_j 1/(t - z'_j) = 0`. -/
@[dlmf 31.15.E3]
theorem vanVleck_zeros {N n : ℕ} {a γ : Fin N → ℂ} {V S : ℂ[X]}
    (hS : IsVanVleckStieltjes a γ (n + 1) V S) {c : ℂ} {z' : Fin n → ℂ}
    (hSz : derivative S = C c * ∏ j, (X - C (z' j))) {t : ℂ} (ht : V.eval t = 0)
    (hta : ∀ j, t ≠ a j) :
    (derivative S).eval t = 0 ∨ ∑ j, γ j / (t - a j) + ∑ j, 1 / (t - z' j) = 0 := by
  classical
  by_cases hD : (derivative S).eval t = 0
  · exact Or.inl hD
  right
  have hne : ∀ j, t - a j ≠ 0 := fun j => sub_ne_zero.mpr (hta j)
  have hPi : (fuchsianPi a).eval t ≠ 0 := by
    simp only [fuchsianPi, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hne j
  have hG : (fuchsianGammaPoly a γ).eval t = (fuchsianPi a).eval t * ∑ j, γ j / (t - a j) := by
    simp only [fuchsianGammaPoly, fuchsianPi, eval_finsetSum, eval_mul, eval_C, eval_prod,
      eval_sub, eval_X, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    field_simp [hne j]
  have hD2 := h31_logDeriv_prod c z' t (hSz ▸ hD)
  rw [← hSz] at hD2
  have hE := congrArg (Polynomial.eval t) hS.2.2.2
  simp only [eval_add, eval_mul, ht, zero_mul, add_zero, eval_zero,
    hG, hD2] at hE
  have : (fuchsianPi a).eval t * (derivative S).eval t *
      (∑ j, γ j / (t - a j) + ∑ j, 1 / (t - z' j)) = 0 := by
    linear_combination hE
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (mul_ne_zero hPi hD)
  · exact h

/-- DLMF 31.15.4: the zeros `z_1, …, z_n` of a Stieltjes polynomial
`S = c ∏_k (X - z_k)`, none of them an `a_j`, are critical points of
`G(ζ) = ∏_k ∏_ℓ (ζ_k - a_ℓ)^{γ_ℓ/2} ∏_{j>k} (ζ_k - ζ_j)` (`stieltjesG`, principal powers, for
`z_k - a_ℓ ∈ slitPlane`): every partial derivative `∂G/∂ζ_k` vanishes at `ζ = z`. -/
@[dlmf 31.15.E4, dlmf 31.15.ii]
theorem stieltjes_zeros_critical {N n : ℕ} {a γ : Fin N → ℂ} {V S : ℂ[X]}
    (hS : IsVanVleckStieltjes a γ n V S) {c : ℂ} {z : Fin n → ℂ}
    (hSz : S = C c * ∏ k, (X - C (z k))) (hza : ∀ k ℓ, z k - a ℓ ∈ slitPlane) (k : Fin n) :
    HasDerivAt (fun x => stieltjesG a γ (Function.update z k x)) 0 (z k) := by
  sorry

/-- DLMF 31.15.5–31.15.6 and §31.15(iii): for real `a_0 < a_1 < ⋯ < a_N` and `γ_j > 0`, for
every multi-index `𝐦 = (m_0, …, m_{N-1})` there is a unique monic Stieltjes polynomial with
exactly `m_j` zeros in `(a_j, a_{j+1})` (so the `(n+N-1 choose N-1)` distributions of
`n = ∑ m_j` zeros give exactly that many Stieltjes polynomials of degree `n`). -/
@[dlmf 31.15.E5, dlmf 31.15.E6, dlmf 31.15.iii]
theorem existsUnique_stieltjesOfIndex {N : ℕ} {a γ : Fin (N + 1) → ℝ} (ha : StrictMono a)
    (hγ : ∀ j, 0 < γ j) (m : Fin N → ℕ) : ∃! S, IsStieltjesOfIndex a γ m S := by
  sorry

/-- DLMF 31.15.5–31.15.6, the count: under these conditions the monic Stieltjes polynomials of
degree `n` are exactly the `(n+N-1 choose N-1)` polynomials `S_𝐦`, `∑ m_j = n`
(here with `N + 1` singular points). -/
@[dlmf 31.15.E5, dlmf 31.15.E6]
theorem stieltjes_card {N : ℕ} {a γ : Fin (N + 1) → ℝ} (ha : StrictMono a)
    (hγ : ∀ j, 0 < γ j) (n : ℕ) :
    {S : ℂ[X] | S.Monic ∧ ∃ V, IsVanVleckStieltjes (fun j => (a j : ℂ)) (fun j => (γ j : ℂ)) n
      V S}.encard = ((n + N - 1).choose (N - 1) : ℕ) := by
  sorry

/-- DLMF 31.15.7: if `S = c ∏_k (X - z_k)` is a Stieltjes polynomial with Van Vleck polynomial
`V`, the `a_j` are distinct and `S(a_j) ≠ 0`, then the accessory parameter of 31.14.1
(`V/∏(X - a_k) = ∑_j q_j/(X - a_j)`), `q_j = V(a_j)/∏_{k≠j}(a_j - a_k)`, equals
`γ_j ∑_k 1/(z_k - a_j)`. DLMF states this under 31.15.5–31.15.6, where `S(a_j) ≠ 0` always
holds; the form here is stronger than DLMF. -/
@[dlmf 31.15.E7]
theorem stieltjes_accessory {N n : ℕ} {a γ : Fin N → ℂ} (ha : Function.Injective a)
    {V S : ℂ[X]} (hS : IsVanVleckStieltjes a γ n V S) {c : ℂ} {z : Fin n → ℂ}
    (hSz : S = C c * ∏ k, (X - C (z k))) (j : Fin N) (hSa : S.eval (a j) ≠ 0) :
    V.eval (a j) / ∏ k ∈ Finset.univ.erase j, (a j - a k) = γ j * ∑ k, 1 / (z k - a j) := by
  classical
  have hE := congrArg (Polynomial.eval (a j)) hS.2.2.2
  have hPi : (fuchsianPi a).eval (a j) = 0 := by
    simp only [fuchsianPi, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)
  have hP0 : ∏ k ∈ Finset.univ.erase j, (a j - a k) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr ?_
    exact ha.ne (Finset.ne_of_mem_erase hk).symm
  have hG : (fuchsianGammaPoly a γ).eval (a j) = γ j * ∏ k ∈ Finset.univ.erase j, (a j - a k) := by
    simp only [fuchsianGammaPoly, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), add_eq_left.mpr]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hi).symm,
      Finset.mem_univ j⟩) (sub_self _), mul_zero]
  have hD := h31_logDeriv_prod c z (a j) (hSz ▸ hSa)
  rw [← hSz] at hD
  simp only [eval_add, eval_mul, hPi, hG, zero_mul, zero_add,
    eval_zero] at hE
  rw [hD] at hE
  field_simp
  have hneg : ∑ k, 1 / (z k - a j) = -∑ k, 1 / (a j - z k) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← neg_sub, div_neg]
  rw [hneg]
  apply mul_right_cancel₀ hSa
  linear_combination hE

/-- DLMF 31.15.8–31.15.12: for distinct multi-indices `𝐦 ≠ 𝐥` the products
`S_𝐦(z_0) ⋯ S_𝐦(z_{N-1})` and `S_𝐥(z_0) ⋯ S_𝐥(z_{N-1})` are orthogonal in `L²_ρ(Q)`. -/
@[dlmf 31.15.E8, dlmf 31.15.E9, dlmf 31.15.E10, dlmf 31.15.E11, dlmf 31.15.E12]
theorem stieltjesProduct_orthogonal {N : ℕ} {a γ : Fin (N + 1) → ℝ} (ha : StrictMono a)
    (hγ : ∀ j, 0 < γ j) {m l : Fin N → ℕ} (hml : m ≠ l) :
    stieltjesInner a γ (stieltjesProduct a γ m) (stieltjesProduct a γ l) = 0 := by
  sorry

/-- DLMF §31.15(iii): the products 31.15.8 have positive norm in `L²_ρ(Q)` (so they can be
normalized). -/
@[dlmf 31.15.iii]
theorem stieltjesProduct_norm_pos {N : ℕ} {a γ : Fin (N + 1) → ℝ} (ha : StrictMono a)
    (hγ : ∀ j, 0 < γ j) (m : Fin N → ℕ) :
    0 < (stieltjesInner a γ (stieltjesProduct a γ m) (stieltjesProduct a γ m)).re := by
  sorry

/-- DLMF §31.15(iii): the normalized products 31.15.8 form an orthonormal basis of `L²_ρ(Q)`;
stated as completeness: a function `f` with `|f|²ρ` integrable on `Q` that is orthogonal to every
product `S_𝐦(z_0) ⋯ S_𝐦(z_{N-1})` vanishes almost everywhere on `Q`. -/
@[dlmf 31.15.iii]
theorem stieltjesProduct_complete {N : ℕ} {a γ : Fin (N + 1) → ℝ} (ha : StrictMono a)
    (hγ : ∀ j, 0 < γ j) {f : (Fin N → ℝ) → ℂ}
    (hf : MeasureTheory.IntegrableOn (fun z => ‖f z‖ ^ 2 * stieltjesWeight a γ z)
      (stieltjesBox a))
    (hfm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (stieltjesBox a)))
    (horth : ∀ m, stieltjesInner a γ f (stieltjesProduct a γ m) = 0) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (stieltjesBox a)), f z = 0 := by
  sorry

end DLMF.Heun
