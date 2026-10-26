/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic
public import DLMF.Heun.Equation
public import Mathlib.Algebra.Polynomial.FieldDivision
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

/-- Algebraic identity behind 31.14.4: with `L = ∑ (γ_j/2)/(z - a_j)`,
`L² + L' - ∑ q_j/(z - a_j)` is the normal-form coefficient. -/
theorem p2h_fuchsian_normal_identity {N : ℕ} {a γ q : Fin N → ℂ} (ha : Function.Injective a)
    {z : ℂ} (hz : ∀ j, z - a j ≠ 0) :
    fuchsianCoeffR a q z = -fuchsianNormalCoeff a γ q z + 0 * (∑ j, γ j / 2 / (z - a j)) +
      (∑ j, γ j / 2 / (z - a j)) ^ 2 + -∑ j, γ j / 2 / (z - a j) ^ 2 := by
  set A : Fin N → ℂ := fun j => 1 / (z - a j) with hA
  set s : Fin N → ℂ := fun j => γ j / 2 with hs
  have hpair : ∀ j k, s j * s k * (A j * A k) =
      (if j = k then s j ^ 2 * A j ^ 2 else 0) + s j * s k * (A j - A k) / (a j - a k) := by
    intro j k
    by_cases hjk : j = k
    · subst hjk; simp; ring
    · have hne : a j - a k ≠ 0 := sub_ne_zero.2 (ha.ne hjk)
      rw [ite_eq_right_iff.2 (fun h => absurd h hjk), zero_add]
      simp only [hA]
      field_simp [hz j, hz k]
      ring
  have hsq : (∑ j, s j * A j) ^ 2 = ∑ j, s j ^ 2 * A j ^ 2 +
      2 * ∑ j, ∑ k, s j * s k * A j / (a j - a k) := by
    rw [sq, Finset.sum_mul_sum]
    have e1 : ∀ j k, s j * A j * (s k * A k) = s j * s k * (A j * A k) := fun j k => by ring
    simp_rw [e1, hpair, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have e2 : ∀ j k, s j * s k * (A j - A k) / (a j - a k) =
        s j * s k * A j / (a j - a k) - s j * s k * A k / (a j - a k) := fun j k => by ring
    simp_rw [e2, Finset.sum_sub_distrib]
    have e3 : ∑ j, ∑ k, s j * s k * A k / (a j - a k) =
        -∑ j, ∑ k, s j * s k * A j / (a j - a k) := by
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← neg_sub (a k), div_neg]; ring
    rw [e3]; ring
  have hL : ∑ j, γ j / 2 / (z - a j) = ∑ j, s j * A j := by
    simp only [hA, hs]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  have hL' : ∑ j, γ j / 2 / (z - a j) ^ 2 = ∑ j, s j * A j ^ 2 := by
    simp only [hA, hs]; refine Finset.sum_congr rfl fun j _ => ?_; field_simp
  have hQ : ∀ j, fuchsianNormalQ a γ q j = 2 * ∑ k, s j * s k / (a j - a k) - q j := by
    intro j
    simp only [fuchsianNormalQ, hs]
    rw [Finset.sum_erase _ (by simp)]
    rw [Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hN : fuchsianNormalCoeff a γ q z = ∑ j, (s j * (s j - 1)) * A j ^ 2 +
      ∑ j, (2 * ∑ k, s j * s k / (a j - a k) - q j) * A j := by
    simp only [fuchsianNormalCoeff, fuchsianNormalGamma, hQ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hA, hs]
    field_simp
  have hR : fuchsianCoeffR a q z = ∑ j, q j * A j := by
    simp only [fuchsianCoeffR, hA]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  rw [hL, hL', hsq, hN, hR]
  have e6 : ∑ j, (2 * ∑ k, s j * s k / (a j - a k) - q j) * A j =
      2 * ∑ j, ∑ k, s j * s k * A j / (a j - a k) - ∑ j, q j * A j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sub_mul, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have e5 : ∑ j, s j * (s j - 1) * A j ^ 2 = ∑ j, s j ^ 2 * A j ^ 2 - ∑ j, s j * A j ^ 2 := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [e6, e5]
  ring

/-- DLMF 31.14.3–31.14.5, the normal form: if `w` solves 31.14.1 on an open set `U` on which
every `z - a_j` lies in `slitPlane`, then `W(z) = ∏_j (z - a_j)^{γ_j/2} w(z)` (principal powers,
so that `w = ∏_j (z - a_j)^{-γ_j/2} W` as in 31.14.3) solves
`W'' = ∑_j (γ̃_j/(z - a_j)² + q̃_j/(z - a_j)) W` (31.14.4). The singular points must be
distinct (`Function.Injective a`, implicit in DLMF; added 2026-10-26 after the counterexample
`p1h_fuchsian_normalForm_counterexample` for coinciding points). -/
@[dlmf 31.14.E3, dlmf 31.14.E4, dlmf 31.14.E5]
theorem fuchsian_normalForm {N : ℕ} {a γ q : Fin N → ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (ha : Function.Injective a)
    (hU : IsOpen U) (hUa : ∀ z ∈ U, ∀ j, z - a j ∈ slitPlane)
    (hw : IsFuchsianSolOn a γ q w U) :
    IsLinearODE2On 0 (fun z => -fuchsianNormalCoeff a γ q z)
      (fun z => (∏ j, (z - a j) ^ (γ j / 2)) * w z) U := by
  classical
  have hz0 : ∀ z ∈ U, ∀ j, z - a j ≠ 0 := fun z hz j => slitPlane_ne_zero (hUa z hz j)
  refine p1h_isLinearODE2On_mul (L := fun z => ∑ j, γ j / 2 / (z - a j))
    (L' := fun z => -∑ j, γ j / 2 / (z - a j) ^ 2) hU (fun z hz => ?_) (fun z hz => ?_)
    (fun z hz => ?_) (fun z hz => p2h_fuchsian_normal_identity ha (hz0 z hz)) hw
  · have hf : ∀ i ∈ (Finset.univ : Finset (Fin N)), HasDerivAt (fun z => (z - a i) ^ (γ i / 2))
        (γ i / 2 * 1 / (z - a i) * (z - a i) ^ (γ i / 2)) z := fun i _ =>
      p1h_hasDerivAt_cpow ((hasDerivAt_id z).sub_const (a i)) (hUa z hz i)
    have h := HasDerivAt.fun_finsetProd hf
    convert h using 1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    ring
  · have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      p1h_hasDerivAt_const_div_sub (γ i / 2) (a i) z (hz0 z hz i))
    convert h using 1
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · simp only [fuchsianCoeffP, Pi.zero_apply, zero_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-- `fuchsian_normalForm` (DLMF 31.14.3–31.14.5) fails without distinct singular points:
for `a = (0, 0)`, `γ = (2, 2)`, `q = 0`, `w = 1` on `slitPlane`, `W = z²` but the junk
`1/(a_j - a_k) = 0` makes the right-hand side `0`. -/
theorem p1h_fuchsian_normalForm_counterexample :
    ¬ ∀ (N : ℕ) (a γ q : Fin N → ℂ) (w : ℂ → ℂ) (U : Set ℂ), IsOpen U →
      (∀ z ∈ U, ∀ j, z - a j ∈ slitPlane) → IsFuchsianSolOn a γ q w U →
      IsLinearODE2On 0 (fun z => -fuchsianNormalCoeff a γ q z)
        (fun z => (∏ j, (z - a j) ^ (γ j / 2)) * w z) U := by
  intro h
  have hw : IsFuchsianSolOn (0 : Fin 2 → ℂ) (fun _ => 2) 0 (fun _ => 1) slitPlane :=
    ⟨fun z _ => differentiableAt_const _, fun z _ => by
      simpa [fuchsianCoeffR] using hasDerivAt_const z (0 : ℂ)⟩
  have := (h 2 0 (fun _ => 2) 0 (fun _ => 1) slitPlane isOpen_slitPlane
    (fun z hz _ => by simpa using hz) hw).hasDerivAt_deriv 1 one_mem_slitPlane
  have hW : (fun z : ℂ => (∏ j : Fin 2, (z - (0 : Fin 2 → ℂ) j) ^ ((2 : ℂ) / 2)) * 1) =
      fun z => z ^ 2 := by
    funext z; simp [sq]
  have hd : deriv (fun z : ℂ => z ^ 2) = fun z => 2 * z := by
    funext z; simp
  rw [hW, hd] at this
  have h2 := this.unique ((hasDerivAt_id 1).const_mul 2)
  simp [fuchsianNormalCoeff, fuchsianNormalGamma, fuchsianNormalQ] at h2

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

/-- A zero of a nonzero polynomial solution of `Π S'' + Γ S' + V S = 0` at which `Π` does not
vanish is simple. -/
theorem p2h_derivative_eval_ne_zero {P G V S : ℂ[X]} {x₀ : ℂ}
    (hE : P * derivative (derivative S) + G * derivative S + V * S = 0) (hS : S ≠ 0)
    (hroot : S.IsRoot x₀) (hP : P.eval x₀ ≠ 0) : (derivative S).eval x₀ ≠ 0 := by
  intro h
  have h' : (derivative S).IsRoot x₀ := h
  set m := S.rootMultiplicity x₀ with hm
  have hm1 : 1 < m := (one_lt_rootMultiplicity_iff_isRoot hS).2 ⟨hroot, h'⟩
  have h1 : (derivative S).rootMultiplicity x₀ = m - 1 := derivative_rootMultiplicity_of_root hroot
  have h2 : (derivative (derivative S)).rootMultiplicity x₀ = m - 1 - 1 := by
    rw [derivative_rootMultiplicity_of_root h', h1]
  have hd1 : (X - C x₀) ^ (m - 1) ∣ derivative S := h1 ▸ pow_rootMultiplicity_dvd _ x₀
  have hd0 : (X - C x₀) ^ (m - 1) ∣ S :=
    (pow_dvd_pow _ (Nat.sub_le m 1)).trans (pow_rootMultiplicity_dvd S x₀)
  have hPS : P * derivative (derivative S) = -(G * derivative S + V * S) := by
    linear_combination hE
  have hd : (X - C x₀) ^ (m - 1) ∣ P * derivative (derivative S) := by
    rw [hPS]
    exact (dvd_add (dvd_mul_of_dvd_right hd1 G) (dvd_mul_of_dvd_right hd0 V)).neg_right
  have hP0 : P ≠ 0 := fun h0 => hP (by rw [h0, eval_zero])
  by_cases hz : P * derivative (derivative S) = 0
  · have hS2 : derivative (derivative S) = 0 := (mul_eq_zero.1 hz).resolve_left hP0
    have hdeg := derivative_eq_zero.1 hS2
    rw [natDegree_eq_zero] at hdeg
    obtain ⟨b, hb⟩ := hdeg
    have hb0 : b = 0 := by rw [← hb] at h; simpa using h
    rw [hb0, map_zero] at hb
    have hdeg0 := derivative_eq_zero.1 hb.symm
    rw [natDegree_eq_zero] at hdeg0
    obtain ⟨b', hb'⟩ := hdeg0
    have : b' = 0 := by rw [← hb'] at hroot; simpa using hroot
    exact hS (by rw [← hb', this, map_zero])
  · have := (le_rootMultiplicity_iff hz).2 hd
    rw [rootMultiplicity_mul hz, rootMultiplicity_eq_zero (fun h0 => hP h0), h2] at this
    omega

/-- Logarithmic derivative of `c ∏_{j ∈ s} (X - z_j)`. -/
theorem p2h_logDeriv_prod_finset {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ℂ)
    (z : ι → ℂ) (x : ℂ) (hx : ∀ j ∈ s, x - z j ≠ 0) :
    (derivative (C c * ∏ j ∈ s, (X - C (z j)))).eval x =
      (C c * ∏ j ∈ s, (X - C (z j))).eval x * ∑ j ∈ s, 1 / (x - z j) := by
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_prod_finset,
    derivative_sub, derivative_X, derivative_C, sub_zero, mul_one, eval_mul, eval_C,
    eval_finsetSum, eval_prod, eval_sub, eval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← Finset.mul_prod_erase _ _ hk]
  field_simp [hx k hk]

/-- DLMF 31.15.2: if `S = c ∏_k (X - z_k)` (`c ≠ 0`) is a Stieltjes polynomial and the zero
`z_k` is none of the `a_j`, then `∑_j (γ_j/2)/(z_k - a_j) + ∑_{j ≠ k} 1/(z_k - z_j) = 0`. -/
@[dlmf 31.15.E2]
theorem stieltjes_zeros_equilibrium {N n : ℕ} {a γ : Fin N → ℂ} {V S : ℂ[X]}
    (hS : IsVanVleckStieltjes a γ n V S) {c : ℂ} {z : Fin n → ℂ}
    (hSz : S = C c * ∏ k, (X - C (z k))) (k : Fin n) (hk : ∀ j, z k ≠ a j) :
    ∑ j, (γ j / 2) / (z k - a j) + ∑ j ∈ Finset.univ.erase k, 1 / (z k - z j) = 0 := by
  classical
  set x₀ := z k with hx₀
  have hne : ∀ j, x₀ - a j ≠ 0 := fun j => sub_ne_zero.mpr (hk j)
  have hPi : (fuchsianPi a).eval x₀ ≠ 0 := by
    simp only [fuchsianPi, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hne j
  have hG : (fuchsianGammaPoly a γ).eval x₀ = (fuchsianPi a).eval x₀ * ∑ j, γ j / (x₀ - a j) := by
    simp only [fuchsianGammaPoly, fuchsianPi, eval_finsetSum, eval_mul, eval_C, eval_prod,
      eval_sub, eval_X, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    field_simp [hne j]
  set T := C c * ∏ j ∈ Finset.univ.erase k, (X - C (z j)) with hT
  have hST : S = (X - C x₀) * T := by
    rw [hSz, hT, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]; ring
  have hroot : S.IsRoot x₀ := by rw [hST]; simp
  have hD := p2h_derivative_eval_ne_zero hS.2.2.2 hS.2.2.1 hroot hPi
  have hd1 : derivative S = T + (X - C x₀) * derivative T := by
    rw [hST, derivative_mul]; simp
  have hd2 : derivative (derivative S) = 2 * derivative T +
      (X - C x₀) * derivative (derivative T) := by
    rw [hd1, derivative_add, derivative_mul]; simp; ring
  have hT0 : T.eval x₀ ≠ 0 := by
    rw [hd1] at hD; simpa using hD
  have hzj : ∀ j ∈ Finset.univ.erase k, x₀ - z j ≠ 0 := by
    intro j hj h0
    apply hT0
    simp only [hT, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    rw [Finset.prod_eq_zero hj h0, mul_zero]
  have hTd := p2h_logDeriv_prod_finset (Finset.univ.erase k) c z x₀ hzj
  rw [← hT] at hTd
  have hE := congrArg (Polynomial.eval x₀) hS.2.2.2
  rw [hd2, hd1] at hE
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero,
    eval_zero, hG, hTd, hroot.eq_zero, mul_zero, eval_ofNat] at hE
  have hsum : ∑ j, γ j / 2 / (x₀ - a j) = (∑ j, γ j / (x₀ - a j)) / 2 := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  have : (fuchsianPi a).eval x₀ * T.eval x₀ *
      (∑ j, γ j / (x₀ - a j) + 2 * ∑ j ∈ Finset.univ.erase k, 1 / (x₀ - z j)) = 0 := by
    linear_combination hE
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (mul_ne_zero hPi hT0)
  · linear_combination h / 2

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

/-- The zeros of a Stieltjes polynomial that avoid the singular points are distinct. -/
theorem p2h_stieltjes_injective {N n : ℕ} {a γ : Fin N → ℂ} {V S : ℂ[X]}
    (hS : IsVanVleckStieltjes a γ n V S) {c : ℂ} {z : Fin n → ℂ}
    (hSz : S = C c * ∏ k, (X - C (z k))) (hk : ∀ k j, z k ≠ a j) : Function.Injective z := by
  classical
  intro k j hkj
  by_contra hne
  have hne' : j ≠ k := Ne.symm hne
  set x₀ := z k with hx₀
  have hPi : (fuchsianPi a).eval x₀ ≠ 0 := by
    simp only [fuchsianPi, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr (hk k j)
  set T := C c * ∏ j ∈ Finset.univ.erase k, (X - C (z j)) with hT
  have hST : S = (X - C x₀) * T := by
    rw [hSz, hT, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]; ring
  have hroot : S.IsRoot x₀ := by rw [hST]; simp
  have hD := p2h_derivative_eval_ne_zero hS.2.2.2 hS.2.2.1 hroot hPi
  have hd1 : derivative S = T + (X - C x₀) * derivative T := by
    rw [hST, derivative_mul]; simp
  have hT0 : T.eval x₀ ≠ 0 := by
    rw [hd1] at hD; simpa using hD
  apply hT0
  simp only [hT, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hne', Finset.mem_univ j⟩) (by rw [hkj, sub_self]),
    mul_zero]

/-- Derivative of a coordinate of `Function.update z k x` in `x`. -/
theorem p2h_hasDerivAt_update_apply {n : ℕ} (z : Fin n → ℂ) (k i : Fin n) (t : ℂ) :
    HasDerivAt (fun x => Function.update z k x i) (if i = k then 1 else 0) t := by
  by_cases h : i = k
  · subst h; simpa using hasDerivAt_id' t
  · simp only [Function.update_of_ne h, h, ite_false]; exact hasDerivAt_const t _

/-- `logDeriv g x = g'/g(x)` from `HasDerivAt`. -/
theorem p2h_logDeriv_of_hasDerivAt {g : ℂ → ℂ} {g' x : ℂ} (h : HasDerivAt g g' x) :
    logDeriv g x = g' / g x := by
  rw [logDeriv_apply, h.deriv]

/-- DLMF 31.15.4: the zeros `z_1, …, z_n` of a Stieltjes polynomial
`S = c ∏_k (X - z_k)`, none of them an `a_j`, are critical points of
`G(ζ) = ∏_k ∏_ℓ (ζ_k - a_ℓ)^{γ_ℓ/2} ∏_{j>k} (ζ_k - ζ_j)` (`stieltjesG`, principal powers, for
`z_k - a_ℓ ∈ slitPlane`): every partial derivative `∂G/∂ζ_k` vanishes at `ζ = z`. -/
@[dlmf 31.15.E4, dlmf 31.15.ii]
theorem stieltjes_zeros_critical {N n : ℕ} {a γ : Fin N → ℂ} {V S : ℂ[X]}
    (hS : IsVanVleckStieltjes a γ n V S) {c : ℂ} {z : Fin n → ℂ}
    (hSz : S = C c * ∏ k, (X - C (z k))) (hza : ∀ k ℓ, z k - a ℓ ∈ slitPlane) (k : Fin n) :
    HasDerivAt (fun x => stieltjesG a γ (Function.update z k x)) 0 (z k) := by
  classical
  have hk : ∀ k j, z k ≠ a j := fun k j h => by
    have := hza k j; rw [h, sub_self] at this; exact slitPlane_ne_zero this rfl
  have hinj := p2h_stieltjes_injective hS hSz hk
  have heq := stieltjes_zeros_equilibrium hS hSz k (hk k)
  set u : ℂ → Fin n → ℂ := fun x => Function.update z k x with hu
  have hu0 : u (z k) = z := Function.update_eq_self k z
  have hud : ∀ i t, HasDerivAt (fun x => u x i) (if i = k then 1 else 0) t :=
    fun i t => p2h_hasDerivAt_update_apply z k i t
  -- factors
  set A : Fin n → Fin N → ℂ → ℂ := fun i ℓ x => (u x i - a ℓ) ^ (γ ℓ / 2) with hA
  set B : Fin n → Fin n → ℂ → ℂ := fun i j x => u x i - u x j with hB
  have hAd : ∀ i ℓ, HasDerivAt (A i ℓ) (γ ℓ / 2 * (if i = k then 1 else 0) / (z i - a ℓ) *
      A i ℓ (z k)) (z k) := by
    intro i ℓ
    have h := p1h_hasDerivAt_cpow (s := γ ℓ / 2) ((hud i (z k)).sub_const (a ℓ))
      (by simp only [hu0]; exact hza i ℓ)
    convert h using 1
    simp only [hA, hu0]
  have hBd : ∀ i j, HasDerivAt (B i j) ((if i = k then 1 else 0) - (if j = k then 1 else 0))
      (z k) := fun i j => (hud i (z k)).sub (hud j (z k))
  have hA0 : ∀ i ℓ, A i ℓ (z k) ≠ 0 := by
    intro i ℓ
    simp only [hA, hu0]
    exact cpow_ne_zero_iff.2 (Or.inl (sub_ne_zero.2 (hk i ℓ)))
  have hB0 : ∀ i j, i < j → B i j (z k) ≠ 0 := by
    intro i j hij
    simp only [hB, hu0]
    exact sub_ne_zero.2 (hinj.ne hij.ne)
  set F : Fin n → ℂ → ℂ := fun i x =>
    (∏ ℓ, A i ℓ x) * ∏ j ∈ Finset.univ.filter (fun j => i < j), B i j x with hF
  have hf : (fun x => stieltjesG a γ (Function.update z k x)) = fun x => ∏ i, F i x := rfl
  have hFd : ∀ i, DifferentiableAt ℂ (F i) (z k) := fun i =>
    (DifferentiableAt.fun_finsetProd fun ℓ _ => (hAd i ℓ).differentiableAt).mul
      (DifferentiableAt.fun_finsetProd fun j _ => (hBd i j).differentiableAt)
  have hF0 : ∀ i, F i (z k) ≠ 0 := fun i =>
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun ℓ _ => hA0 i ℓ)
      (Finset.prod_ne_zero_iff.2 fun j hj => hB0 i j (Finset.mem_filter.1 hj).2)
  have hlogF : ∀ i, logDeriv (F i) (z k) =
      ∑ ℓ, γ ℓ / 2 * (if i = k then 1 else 0) / (z i - a ℓ) +
        ∑ j ∈ Finset.univ.filter (fun j => i < j),
          ((if i = k then 1 else 0) - (if j = k then 1 else 0)) / (z i - z j) := by
    intro i
    rw [hF, logDeriv_fun_mul (z k) (Finset.prod_ne_zero_iff.2 fun ℓ _ => hA0 i ℓ)
      (Finset.prod_ne_zero_iff.2 fun j hj => hB0 i j (Finset.mem_filter.1 hj).2)
      (DifferentiableAt.fun_finsetProd fun ℓ _ => (hAd i ℓ).differentiableAt)
      (DifferentiableAt.fun_finsetProd fun j _ => (hBd i j).differentiableAt),
      logDeriv_fun_prod (fun ℓ _ => hA0 i ℓ) (fun ℓ _ => (hAd i ℓ).differentiableAt),
      logDeriv_fun_prod (fun j hj => hB0 i j (Finset.mem_filter.1 hj).2)
        (fun j _ => (hBd i j).differentiableAt)]
    congr 1
    · refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [p2h_logDeriv_of_hasDerivAt (hAd i ℓ), mul_div_cancel_right₀ _ (hA0 i ℓ)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [p2h_logDeriv_of_hasDerivAt (hBd i j)]
      simp only [hB, hu0]
  have hlog : logDeriv (fun x => ∏ i, F i x) (z k) = 0 := by
    rw [logDeriv_fun_prod (fun i _ => hF0 i) (fun i _ => hFd i)]
    simp only [hlogF, Finset.sum_add_distrib]
    have e1 : ∀ i, ∑ ℓ, γ ℓ / 2 * (if i = k then 1 else 0) / (z i - a ℓ) =
        if i = k then ∑ ℓ, γ ℓ / 2 / (z k - a ℓ) else 0 := by
      intro i; split_ifs with h
      · subst h; simp
      · simp
    have e2 : ∀ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ((if i = k then (1 : ℂ) else 0) - (if j = k then 1 else 0)) / (z i - z j) =
        (if i = k then ∑ j ∈ Finset.univ.filter (fun j => k < j), 1 / (z k - z j) else 0) -
          (if i < k then 1 / (z i - z k) else 0) := by
      intro i
      simp only [sub_div, Finset.sum_sub_distrib]
      congr 1
      · split_ifs with h
        · subst h; rfl
        · simp
      · rw [Finset.sum_filter]
        simp only [ite_div, one_div, zero_div]
        rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
        simp
    simp only [e1, e2, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have e3 : ∑ j ∈ Finset.univ.erase k, 1 / (z k - z j) =
        ∑ j ∈ Finset.univ.filter (fun j => k < j), 1 / (z k - z j) -
          ∑ i, (if i < k then 1 / (z i - z k) else 0) := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ k), sub_self, div_zero, sub_zero,
        Finset.sum_filter, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rcases lt_trichotomy k j with h | h | h
      · have h1 : ¬ j < k := not_lt.2 h.le
        simp [h, h1]
      · subst h; simp
      · have h1 : ¬ k < j := not_lt.2 h.le
        simp only [h1, h, ite_true, ite_false, zero_sub]
        rw [← neg_sub (z j) (z k), div_neg]
    rw [← e3]
    linear_combination heq
  have hfk : (fun x => ∏ i, F i x) (z k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hF0 i
  have hdiff : DifferentiableAt ℂ (fun x => ∏ i, F i x) (z k) :=
    DifferentiableAt.fun_finsetProd fun i _ => hFd i
  have hderiv : deriv (fun x => ∏ i, F i x) (z k) = 0 := by
    have := hlog
    rw [logDeriv_apply, div_eq_zero_iff] at this
    exact this.resolve_right hfk
  rw [hf]
  exact hderiv ▸ hdiff.hasDerivAt

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
