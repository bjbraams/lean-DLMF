/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

/-!
# Theta functions: power series (DLMF §20.6)

The exponential power series 20.6.2–20.6.5 of `θⱼ(πz|τ)` about `z = 0`, with the lattice sums
`δ_{2j}, α_{2j}, β_{2j}, γ_{2j}` of 20.6.6–20.6.9. The lattice sums are defined as iterated sums,
inner over `m` and outer over `n` (the Eisenstein order of DLMF); for `2j ≥ 4` the order is
irrelevant (`thetaDelta_hasSum_lattice`), for `2j = 2` it matters. The power series are stated with
an explicit summability claim, so that Lean's convention `∑' = 0` for divergent series plays no
role.
-/

@[expose] public section

open Complex Filter Topology
open scoped Real

noncomputable section

namespace DLMF.Theta

open DLMF.Elliptic

/-- DLMF 20.6.6: `δ_k(τ) = ∑_n ∑'_m (m + nτ)^{-k}` (`(m,n) ≠ (0,0)`; DLMF writes `δ_{2j}`,
`k = 2j`).
Iterated sum, inner over `m`. -/
@[dlmf 20.6.E6]
def thetaDelta (k : ℕ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, ∑' m : ℤ, if m = 0 ∧ n = 0 then 0 else ((m : ℂ) + n * τ) ^ (-(k : ℤ))

/-- DLMF 20.6.7: `α_k(τ) = ∑_n ∑_m (m - 1/2 + nτ)^{-k}` (`k = 2j`). -/
@[dlmf 20.6.E7]
def thetaAlpha (k : ℕ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, ∑' m : ℤ, ((m : ℂ) - 1 / 2 + n * τ) ^ (-(k : ℤ))

/-- DLMF 20.6.8: `β_k(τ) = ∑_n ∑_m (m - 1/2 + (n - 1/2)τ)^{-k}` (`k = 2j`). -/
@[dlmf 20.6.E8]
def thetaBeta (k : ℕ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, ∑' m : ℤ, ((m : ℂ) - 1 / 2 + (n - 1 / 2) * τ) ^ (-(k : ℤ))

/-- DLMF 20.6.9: `γ_k(τ) = ∑_n ∑_m (m + (n - 1/2)τ)^{-k}` (`k = 2j`). -/
@[dlmf 20.6.E9]
def thetaGamma (k : ℕ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, ∑' m : ℤ, ((m : ℂ) + (n - 1 / 2) * τ) ^ (-(k : ℤ))

/-- DLMF 20.6.1: the radius `min_{(m,n) ≠ (0,0)} |z_{m,n}| = min |(m + nτ)π|`; the power series
20.6.2–20.6.5 hold for `|πz|` below it. -/
@[dlmf 20.6.E1]
def thetaLatticeMinNorm (τ : ℂ) : ℝ :=
  ⨅ p : {p : ℤ × ℤ // p ≠ 0}, ‖((p.1.1 : ℂ) + p.1.2 * τ) * π‖

/-- DLMF 20.6.2: for `|πz| < min |z_{m,n}|`,
`θ₁(πz|τ) = πz θ₁'(0|τ) exp(-∑_{j≥1} δ_{2j}(τ) z^{2j}/(2j))`. -/
@[dlmf 20.6.E2]
theorem jacobiThetaOneTau_powerSeries {τ z : ℂ} (hτ : 0 < τ.im)
    (hz : ‖π * z‖ < thetaLatticeMinNorm τ) :
    ∃ S : ℂ, HasSum (fun j : ℕ => thetaDelta (2 * (j + 1)) τ * z ^ (2 * (j + 1)) /
        (2 * (j + 1))) S ∧
      jacobiThetaOneTau (π * z) τ = π * z * jacobiThetaOneDerivNullTau τ * cexp (-S) := by
  sorry

/-- DLMF 20.6.3: for `|πz| < min |z_{m,n}|`,
`θ₂(πz|τ) = θ₂(0|τ) exp(-∑_{j≥1} α_{2j}(τ) z^{2j}/(2j))`. -/
@[dlmf 20.6.E3]
theorem jacobiThetaTwoTau_powerSeries {τ z : ℂ} (hτ : 0 < τ.im)
    (hz : ‖π * z‖ < thetaLatticeMinNorm τ) :
    ∃ S : ℂ, HasSum (fun j : ℕ => thetaAlpha (2 * (j + 1)) τ * z ^ (2 * (j + 1)) /
        (2 * (j + 1))) S ∧
      jacobiThetaTwoTau (π * z) τ = jacobiThetaTwoNullTau τ * cexp (-S) := by
  sorry

/-- DLMF 20.6.4: for `|πz| < min |z_{m,n}|`,
`θ₃(πz|τ) = θ₃(0|τ) exp(-∑_{j≥1} β_{2j}(τ) z^{2j}/(2j))`. -/
@[dlmf 20.6.E4]
theorem jacobiThetaThreeTau_powerSeries {τ z : ℂ} (hτ : 0 < τ.im)
    (hz : ‖π * z‖ < thetaLatticeMinNorm τ) :
    ∃ S : ℂ, HasSum (fun j : ℕ => thetaBeta (2 * (j + 1)) τ * z ^ (2 * (j + 1)) /
        (2 * (j + 1))) S ∧
      jacobiThetaThreeTau (π * z) τ = jacobiThetaThreeNullTau τ * cexp (-S) := by
  sorry

/-- DLMF 20.6.5: for `|πz| < min |z_{m,n}|`,
`θ₄(πz|τ) = θ₄(0|τ) exp(-∑_{j≥1} γ_{2j}(τ) z^{2j}/(2j))`. -/
@[dlmf 20.6.E5]
theorem jacobiThetaFourTau_powerSeries {τ z : ℂ} (hτ : 0 < τ.im)
    (hz : ‖π * z‖ < thetaLatticeMinNorm τ) :
    ∃ S : ℂ, HasSum (fun j : ℕ => thetaGamma (2 * (j + 1)) τ * z ^ (2 * (j + 1)) /
        (2 * (j + 1))) S ∧
      jacobiThetaFourTau (π * z) τ = jacobiThetaFourNullTau τ * cexp (-S) := by
  sorry

/-- DLMF 20.6.10: `α_{2j}(τ) = 2^{2j} δ_{2j}(2τ) - δ_{2j}(τ)` and
`β_{2j}(τ) = 2^{2j} γ_{2j}(2τ) - γ_{2j}(τ)`, `j ≥ 1`, `Im τ > 0`. -/
@[dlmf 20.6.E10]
theorem thetaAlpha_thetaBeta_eq {τ : ℂ} (hτ : 0 < τ.im) (j : ℕ) (hj : 1 ≤ j) :
    thetaAlpha (2 * j) τ = 2 ^ (2 * j) * thetaDelta (2 * j) (2 * τ) - thetaDelta (2 * j) τ ∧
      thetaBeta (2 * j) τ = 2 ^ (2 * j) * thetaGamma (2 * j) (2 * τ) - thetaGamma (2 * j) τ := by
  sorry

/-- `∑_{a,b ≥ 0} (a + b + 2)^{-2}` diverges (helper). -/
lemma p20R1_not_summable_sq_add :
    ¬ Summable (fun p : ℕ × ℕ => (1 : ℝ) / ((p.1 : ℝ) + p.2 + 2) ^ 2) := by
  intro h
  have h0 : ∀ p : ℕ × ℕ, 0 ≤ (1 : ℝ) / ((p.1 : ℝ) + p.2 + 2) ^ 2 := fun _ => by positivity
  have hf : Summable (fun a : ℕ => ∑' b : ℕ, (1 : ℝ) / ((a : ℝ) + b + 2) ^ 2) := h.prod
  apply Real.not_summable_one_div_natCast
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun a => ?_) (hf.mul_left 4)
  have hs : Summable (fun b : ℕ => (1 : ℝ) / ((a : ℝ) + b + 2) ^ 2) := h.prod_factor a
  have hle := hs.sum_le_tsum (Finset.range (a + 1)) (fun b _ => by positivity)
  have hlow : ∀ b ∈ Finset.range (a + 1), (1 : ℝ) / (2 * ((a : ℝ) + 1)) ^ 2 ≤
      1 / ((a : ℝ) + b + 2) ^ 2 := by
    intro b hb
    have : (b : ℝ) ≤ a := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    gcongr
    linarith
  have hsum := Finset.sum_le_sum hlow
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have : (1 : ℝ) / ((a + 1 : ℕ) : ℝ) = 4 * (((a + 1 : ℕ) : ℝ) * (1 / (2 * ((a : ℝ) + 1)) ^ 2)) := by
    push_cast; field_simp; ring
  rw [this]
  push_cast at hsum ⊢
  nlinarith

/-- Absolute convergence of the (doubled, shifted) lattice sums for `k ≥ 3` (helper). -/
lemma p20R1_lattice_summable {τ : ℂ} (hτ : 0 < τ.im) (a b : ℤ) {k : ℕ} (hk : 3 ≤ k) :
    Summable (fun p : ℤ × ℤ =>
      (‖(((2 * p.1 + a : ℤ) : ℂ) + ((2 * p.2 + b : ℤ) : ℂ) * τ)‖⁻¹) ^ k) := by
  set z : UpperHalfPlane := ⟨τ, hτ⟩
  set x : ℤ × ℤ → (Fin 2 → ℤ) := fun p => ![2 * p.2 + b, 2 * p.1 + a] with hx
  have hinj : Function.Injective x := by
    intro p q h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    simp [hx] at h0 h1
    exact Prod.ext (by omega) (by omega)
  have hr := EisensteinSeries.r_pos z
  have hs := ((EisensteinSeries.summable_one_div_norm_rpow (k := k)
    (by exact_mod_cast (show 2 < k by omega))).comp_injective hinj).mul_left
      ((EisensteinSeries.r z)⁻¹ ^ k)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun p => ?_) hs
  simp only [Function.comp_apply]
  by_cases h0 : x p = 0
  · have e0 := congrFun h0 0; have e1 := congrFun h0 1
    simp [hx] at e0 e1
    have : (((2 * p.1 + a : ℤ) : ℂ) + ((2 * p.2 + b : ℤ) : ℂ) * τ) = 0 := by
      rw [show (2 * p.1 + a : ℤ) = 0 by omega, show (2 * p.2 + b : ℤ) = 0 by omega]; simp
    rw [this, norm_zero, inv_zero, zero_pow (by omega)]
    positivity
  · have hb := EisensteinSeries.r_mul_max_le z h0
    have heq : (x p 0 : ℂ) * (z : ℂ) + x p 1 =
        (((2 * p.1 + a : ℤ) : ℂ) + ((2 * p.2 + b : ℤ) : ℂ) * τ) := by
      simp [hx, z]; ring
    rw [heq] at hb
    have hxp : 0 < ‖x p‖ := norm_pos_iff.mpr h0
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, ← inv_pow, ← mul_pow]
    gcongr
    rw [← mul_inv]
    exact inv_anti₀ (by positivity) hb

/-- Summability of `g^{-k}` when `2g` runs over a shifted lattice (helper). -/
lemma p20R1_point_summable {τ : ℂ} (hτ : 0 < τ.im) (a b : ℤ) {k : ℕ} (hk : 3 ≤ k)
    {g : ℤ × ℤ → ℂ}
    (hg : ∀ p : ℤ × ℤ, 2 * g p = ((2 * p.1 + a : ℤ) : ℂ) + ((2 * p.2 + b : ℤ) : ℂ) * τ) :
    Summable (fun p : ℤ × ℤ => g p ^ (-(k : ℤ))) := by
  refine Summable.of_norm_bounded ((p20R1_lattice_summable hτ a b hk).mul_left (2 ^ k))
    (fun p => ?_)
  have hgp : g p = (((2 * p.1 + a : ℤ) : ℂ) + ((2 * p.2 + b : ℤ) : ℂ) * τ) / 2 := by
    rw [← hg p]; ring
  rw [hgp, norm_zpow, norm_div, zpow_neg, zpow_natCast, div_pow, inv_div, inv_pow,
    show ‖(2 : ℂ)‖ = 2 by norm_num, div_eq_mul_inv]

/-- An absolutely summable double series equals its iterated sum, inner over the first
coordinate (helper). -/
lemma p20R1_hasSum_iter {f : ℤ × ℤ → ℂ} (hf : Summable f) :
    HasSum f (∑' n : ℤ, ∑' m : ℤ, f (m, n)) := by
  have hs : Summable (f ∘ Prod.swap) := (Equiv.prodComm ℤ ℤ).summable_iff.mpr hf
  have h1 := hs.hasSum.prod_fiberwise (fun n => (hs.prod_factor n).hasSum)
  have h2 : HasSum f (∑' p, (f ∘ Prod.swap) p) :=
    (Equiv.prodComm ℤ ℤ).hasSum_iff.mp hs.hasSum
  have e : (∑' n : ℤ, ∑' m : ℤ, f (m, n)) = ∑' p, (f ∘ Prod.swap) p := h1.tsum_eq
  rw [e]; exact h2

/-- DLMF §20.6: for `2j ≥ 4` the order of summation in the lattice sums does not matter: the
double series converge absolutely, and their unordered sums equal the iterated sums. -/
@[dlmf 20.6]
theorem thetaDelta_hasSum_lattice {τ : ℂ} (hτ : 0 < τ.im) {j : ℕ} (hj : 2 ≤ j) :
    HasSum (fun p : ℤ × ℤ => if p.1 = 0 ∧ p.2 = 0 then 0 else
        ((p.1 : ℂ) + p.2 * τ) ^ (-((2 * j : ℕ) : ℤ))) (thetaDelta (2 * j) τ) ∧
      HasSum (fun p : ℤ × ℤ => ((p.1 : ℂ) - 1 / 2 + p.2 * τ) ^ (-((2 * j : ℕ) : ℤ)))
        (thetaAlpha (2 * j) τ) ∧
      HasSum (fun p : ℤ × ℤ => ((p.1 : ℂ) - 1 / 2 + (p.2 - 1 / 2) * τ) ^ (-((2 * j : ℕ) : ℤ)))
        (thetaBeta (2 * j) τ) ∧
      HasSum (fun p : ℤ × ℤ => ((p.1 : ℂ) + (p.2 - 1 / 2) * τ) ^ (-((2 * j : ℕ) : ℤ)))
        (thetaGamma (2 * j) τ) := by
  have hk : 3 ≤ 2 * j := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hs := p20R1_point_summable hτ 0 0 hk (g := fun p => (p.1 : ℂ) + p.2 * τ)
      (fun p => by push_cast; ring)
    have hs' : Summable (fun p : ℤ × ℤ => if p.1 = 0 ∧ p.2 = 0 then 0 else
        ((p.1 : ℂ) + p.2 * τ) ^ (-((2 * j : ℕ) : ℤ))) := by
      refine Summable.of_norm_bounded hs.norm (fun p => ?_)
      split_ifs <;> simp
      positivity
    exact p20R1_hasSum_iter hs'
  · exact p20R1_hasSum_iter (p20R1_point_summable hτ (-1) 0 hk (fun p => by push_cast; ring))
  · exact p20R1_hasSum_iter (p20R1_point_summable hτ (-1) (-1) hk (fun p => by push_cast; ring))
  · exact p20R1_hasSum_iter (p20R1_point_summable hτ 0 (-1) hk (fun p => by push_cast; ring))

/-- DLMF §20.6: for `j = 1` the order matters: the double series for `δ₂` is not absolutely
summable. -/
@[dlmf 20.6]
theorem thetaDelta_two_not_summable {τ : ℂ} (hτ : 0 < τ.im) :
    ¬ Summable (fun p : ℤ × ℤ => if p.1 = 0 ∧ p.2 = 0 then (0 : ℂ) else
        ((p.1 : ℂ) + p.2 * τ) ^ (-2 : ℤ)) := by
  intro h
  have hn := (summable_norm_iff.mpr h).comp_injective
    (i := fun p : ℕ × ℕ => (((p.1 + 1 : ℕ) : ℤ), ((p.2 + 1 : ℕ) : ℤ))) (by
      intro p q hpq
      simp only [Prod.mk.injEq, Nat.cast_inj, Nat.add_right_cancel_iff] at hpq
      exact Prod.ext hpq.1 hpq.2)
  apply p20R1_not_summable_sq_add
  set C := 1 + ‖τ‖ with hC
  have hC0 : 0 < C := by positivity
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun p => ?_) (hn.mul_left (C ^ 2))
  obtain ⟨a, b⟩ := p
  simp only [Function.comp_apply]
  have hne : ¬ ((((a + 1 : ℕ) : ℤ)) = 0 ∧ (((b + 1 : ℕ) : ℤ)) = 0) := by omega
  simp only [hne, ↓reduceIte]
  have hw : ((((a + 1 : ℕ) : ℤ) : ℂ) + (((b + 1 : ℕ) : ℤ) : ℂ) * τ) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    rcases this with h1 | h1
    · linarith [h1]
    · linarith
  rw [zpow_neg, norm_inv, zpow_two, norm_mul]
  set w := ((((a + 1 : ℕ) : ℤ) : ℂ) + (((b + 1 : ℕ) : ℤ) : ℂ) * τ)
  have hwp : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hwle : ‖w‖ ≤ C * ((a : ℝ) + b + 2) := by
    calc ‖w‖ ≤ ‖((((a + 1 : ℕ) : ℤ) : ℂ))‖ + ‖(((b + 1 : ℕ) : ℤ) : ℂ)‖ * ‖τ‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ = ((a : ℝ) + 1) + ((b : ℝ) + 1) * ‖τ‖ := by
          simp only [Int.cast_natCast, Complex.norm_natCast]; push_cast; ring
      _ ≤ C * ((a : ℝ) + b + 2) := by rw [hC]; nlinarith [norm_nonneg τ]
  rw [div_le_iff₀ (by positivity)]
  have : ‖w‖ * ‖w‖ ≤ (C * ((a : ℝ) + b + 2)) ^ 2 := by nlinarith
  calc (1 : ℝ) = (‖w‖ * ‖w‖)⁻¹ * (‖w‖ * ‖w‖) := by field_simp
    _ ≤ (‖w‖ * ‖w‖)⁻¹ * (C * ((a : ℝ) + b + 2)) ^ 2 := by gcongr
    _ = _ := by ring

end DLMF.Theta

end
