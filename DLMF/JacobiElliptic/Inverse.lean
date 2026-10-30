/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.SpecialValues
public import DLMF.JacobiElliptic.Related

/-!
# Inverse Jacobian elliptic functions (DLMF §22.15)

For real variables and real parameter `m = k² < 1` (`k'² = 1 - m`):

* `arcsn(x, k)` is the existing `DLMF.Elliptic.Real.jacobiArcsnm x m = F(arcsin x | m)`
  (`DLMF.Elliptic.SpecialValues`), with `sn(arcsn x) = x` (`Real.jacobiSnm_jacobiArcsnm`).
* `Real.jacobiArccnm x m = F(arccos x | m)` and
  `Real.jacobiArcdnm x m = F(arcsin √((1 - x²)/m) | m)` are the solutions of 22.15.2–22.15.3 in
  the principal ranges 22.15.6–22.15.7; their inverse properties and ranges are proved.
* The other nine inverse functions are *defined* by DLMF's integral representations
  22.15.15–22.15.23 (on DLMF's ranges of `x`; outside them the integrals are Lean's totalized
  values); that they invert `cd, sd, nd, dc, nc, sc, ns, ds, cs` is proved (by substitution in
  the integrals; the reciprocal ones by `t ↦ 1/t` from `arcdn, arccd, arccn, arcsn, arcsd`, and
  `arccs x = F(π/2 - arctan x | m)` by `t = cot φ`).

The representations 22.15.12–22.15.14 (and so 22.15.11, proved for `-K ≤ x ≤ K`, stronger than
DLMF's `-1 ≤ x ≤ 1`) and the general solutions 22.15.8–22.15.10 are proved.
-/

@[expose] public section

open Real DLMF.Elliptic
open scoped Topology

noncomputable section

namespace DLMF.JacobiElliptic

/-! ### Definitions -/

/-- `arccn(x, k) = F(arccos x | k²)`: the solution `η ∈ [0, 2K]` of `cn(η, k) = x`,
`-1 ≤ x ≤ 1` (DLMF 22.15.2, 22.15.4, 22.15.6). -/
@[dlmf 22.15.E4]
def Real.jacobiArccnm (x m : ℝ) : ℝ := Real.incEllIntFm (Real.arccos x) m

/-- `arcdn(x, k) = F(arcsin √((1 - x²)/k²) | k²)`: the solution `ζ ∈ [0, K]` of `dn(ζ, k) = x`,
`k' ≤ x ≤ 1` (DLMF 22.15.3, 22.15.4, 22.15.7); meaningful for `0 < m < 1`. -/
@[dlmf 22.15.E4]
def Real.jacobiArcdnm (x m : ℝ) : ℝ := Real.incEllIntFm (Real.arcsin (√((1 - x ^ 2) / m))) m

/-- `arccd(x, k) = ∫ₓ¹ dt/√((1 - t²)(1 - k²t²))`, `-1 ≤ x ≤ 1` (DLMF 22.15.15). -/
@[dlmf 22.15.E15]
def Real.jacobiArccdm (x m : ℝ) : ℝ := ∫ t in x..1, 1 / √((1 - t ^ 2) * (1 - m * t ^ 2))

/-- `arcsd(x, k) = ∫₀ˣ dt/√((1 - k'²t²)(1 + k²t²))`, `-1/k' ≤ x ≤ 1/k'` (DLMF 22.15.16). -/
@[dlmf 22.15.E16]
def Real.jacobiArcsdm (x m : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, 1 / √((1 - (1 - m) * t ^ 2) * (1 + m * t ^ 2))

/-- `arcnd(x, k) = ∫₁ˣ dt/√((t² - 1)(1 - k'²t²))`, `1 ≤ x ≤ 1/k'` (DLMF 22.15.17). -/
@[dlmf 22.15.E17]
def Real.jacobiArcndm (x m : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..x, 1 / √((t ^ 2 - 1) * (1 - (1 - m) * t ^ 2))

/-- `arcdc(x, k) = ∫₁ˣ dt/√((t² - 1)(t² - k²))`, `1 ≤ x < ∞` (DLMF 22.15.18). -/
@[dlmf 22.15.E18]
def Real.jacobiArcdcm (x m : ℝ) : ℝ := ∫ t in (1 : ℝ)..x, 1 / √((t ^ 2 - 1) * (t ^ 2 - m))

/-- `arcnc(x, k) = ∫₁ˣ dt/√((t² - 1)(k² + k'²t²))`, `1 ≤ x < ∞` (DLMF 22.15.19). -/
@[dlmf 22.15.E19]
def Real.jacobiArcncm (x m : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..x, 1 / √((t ^ 2 - 1) * (m + (1 - m) * t ^ 2))

/-- `arcsc(x, k) = ∫₀ˣ dt/√((1 + t²)(1 + k'²t²))`, `x ∈ ℝ` (DLMF 22.15.20). -/
@[dlmf 22.15.E20]
def Real.jacobiArcscm (x m : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, 1 / √((1 + t ^ 2) * (1 + (1 - m) * t ^ 2))

/-- `arcns(x, k) = ∫ₓ^∞ dt/√((t² - 1)(t² - k²))`, `1 ≤ x < ∞` (DLMF 22.15.21). -/
@[dlmf 22.15.E21]
def Real.jacobiArcnsm (x m : ℝ) : ℝ := ∫ t in Set.Ioi x, 1 / √((t ^ 2 - 1) * (t ^ 2 - m))

/-- `arcds(x, k) = ∫ₓ^∞ dt/√((t² + k²)(t² - k'²))`, `k' ≤ x < ∞` (DLMF 22.15.22). -/
@[dlmf 22.15.E22]
def Real.jacobiArcdsm (x m : ℝ) : ℝ := ∫ t in Set.Ioi x, 1 / √((t ^ 2 + m) * (t ^ 2 - (1 - m)))

/-- `arccs(x, k) = ∫ₓ^∞ dt/√((1 + t²)(t² + k'²))`, `x ∈ ℝ` (DLMF 22.15.23). -/
@[dlmf 22.15.E23]
def Real.jacobiArccsm (x m : ℝ) : ℝ := ∫ t in Set.Ioi x, 1 / √((1 + t ^ 2) * (t ^ 2 + (1 - m)))

/-! ### §22.15(i): the principal inverses of `sn, cn, dn` -/

section Principal

variable {m : ℝ}

/-- DLMF 22.15.2/22.15.4: `cn(arccn(x, k), k) = x` for `-1 ≤ x ≤ 1`. -/
@[dlmf 22.15.E2 "special case: real parameter m = k² < 1"]
theorem Real.jacobiCnm_jacobiArccnm (hm : m < 1) {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    Real.jacobiCnm (Real.jacobiArccnm x m) m = x := by
  rw [Real.jacobiCnm, Real.jacobiArccnm, Real.jacobiAmm_incEllIntFm hm, Real.cos_arccos hx0 hx1]

/-- DLMF 22.15.3/22.15.4: `dn(arcdn(x, k), k) = x` for `k' ≤ x ≤ 1`, `0 < k² < 1`. -/
@[dlmf 22.15.E3 "special case: real parameter 0 < m = k² < 1"]
theorem Real.jacobiDnm_jacobiArcdnm (hm0 : 0 < m) (hm : m < 1) {x : ℝ} (hx0 : √(1 - m) ≤ x)
    (hx1 : x ≤ 1) : Real.jacobiDnm (Real.jacobiArcdnm x m) m = x := by
  have hx : 0 ≤ x := le_trans (Real.sqrt_nonneg _) hx0
  have h1 : 1 - m ≤ x ^ 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - m by linarith)
    nlinarith [Real.sqrt_nonneg (1 - m)]
  have hq0 : 0 ≤ (1 - x ^ 2) / m := div_nonneg (by nlinarith) hm0.le
  have hq1 : (1 - x ^ 2) / m ≤ 1 := by rw [div_le_one hm0]; linarith
  have hs0 : 0 ≤ √((1 - x ^ 2) / m) := Real.sqrt_nonneg _
  have hs1 : √((1 - x ^ 2) / m) ≤ 1 := Real.sqrt_le_one.mpr hq1
  rw [Real.jacobiDnm, Real.jacobiSnm, Real.jacobiArcdnm, Real.jacobiAmm_incEllIntFm hm,
    Real.sin_arcsin (by linarith) hs1, Real.sq_sqrt hq0,
    show 1 - m * ((1 - x ^ 2) / m) = x ^ 2 by field_simp; ring, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq hx]

/-- DLMF 22.15.5: `-K ≤ arcsn(x, k) ≤ K` for `-1 ≤ x ≤ 1`. -/
@[dlmf 22.15.E5 "special case: real parameter m = k² < 1"]
theorem Real.jacobiArcsnm_mem_Icc (hm : m < 1) (x : ℝ) :
    Real.jacobiArcsnm x m ∈ Set.Icc (-Real.compEllIntKm m) (Real.compEllIntKm m) := by
  have hmono := (Real.strictMono_incEllIntFm hm).monotone
  refine ⟨?_, ?_⟩
  · have := hmono (Real.neg_pi_div_two_le_arcsin x)
    dsimp only at this
    rw [Real.incEllIntFm_neg, Real.incEllIntFm_pi_div_two] at this
    exact this
  · have := hmono (Real.arcsin_le_pi_div_two x)
    dsimp only at this
    rw [Real.incEllIntFm_pi_div_two] at this
    exact this

/-- DLMF 22.15.6: `0 ≤ arccn(x, k) ≤ 2K`. -/
@[dlmf 22.15.E6 "special case: real parameter m = k² < 1"]
theorem Real.jacobiArccnm_mem_Icc (hm : m < 1) (x : ℝ) :
    Real.jacobiArccnm x m ∈ Set.Icc 0 (2 * Real.compEllIntKm m) := by
  have hmono := (Real.strictMono_incEllIntFm hm).monotone
  refine ⟨?_, ?_⟩
  · have := hmono (Real.arccos_nonneg x)
    simpa [Real.incEllIntFm, Real.jacobiArccnm] using this
  · have h := Real.incEllIntFm_add_pi hm 0
    rw [zero_add, show Real.incEllIntFm 0 m = 0 by simp [Real.incEllIntFm], zero_add] at h
    have := hmono (Real.arccos_le_pi x)
    dsimp only at this
    rw [h] at this
    exact this

/-- DLMF 22.15.7: `0 ≤ arcdn(x, k) ≤ K`. -/
@[dlmf 22.15.E7 "special case: real parameter m = k² < 1"]
theorem Real.jacobiArcdnm_mem_Icc (hm : m < 1) (x : ℝ) :
    Real.jacobiArcdnm x m ∈ Set.Icc 0 (Real.compEllIntKm m) := by
  have hmono := (Real.strictMono_incEllIntFm hm).monotone
  refine ⟨?_, ?_⟩
  · have := hmono (Real.arcsin_nonneg.mpr (Real.sqrt_nonneg ((1 - x ^ 2) / m)))
    simpa [Real.incEllIntFm, Real.jacobiArcdnm] using this
  · have := hmono (Real.arcsin_le_pi_div_two (√((1 - x ^ 2) / m)))
    dsimp only at this
    rw [Real.incEllIntFm_pi_div_two] at this
    exact this

/-- Identity under the stated parameter and domain assumptions: `Real.incEllIntFm (φ + n * π) m =
Real.incEllIntFm φ m + 2 * n * Real.compEllIntKm m`. -/
lemma p22R1_F_add_int_pi {m : ℝ} (hm : m < 1) (φ : ℝ) (n : ℤ) :
    Real.incEllIntFm (φ + n * π) m = Real.incEllIntFm φ m + 2 * n * Real.compEllIntKm m := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    push_cast at ih ⊢
    rw [show φ + (n + 1) * π = φ + n * π + π by ring, Real.incEllIntFm_add_pi hm, ih]; ring
  | pred n ih =>
    push_cast at ih ⊢
    have h := Real.incEllIntFm_add_pi hm (φ + (-(n : ℝ) - 1) * π)
    rw [show φ + (-(n : ℝ) - 1) * π + π = φ + -(n : ℝ) * π by ring, ih] at h
    linarith

/-- Identity under the stated parameter and domain assumptions: `ξ = Real.incEllIntFm B m ↔
Real.jacobiAmm ξ m = B`. -/
lemma p22R1_eq_F_iff {m : ℝ} (hm : m < 1) (ξ B : ℝ) :
    ξ = Real.incEllIntFm B m ↔ Real.jacobiAmm ξ m = B := by
  constructor
  · rintro rfl; exact Real.jacobiAmm_incEllIntFm hm B
  · rintro rfl; exact (Real.incEllIntFm_jacobiAmm hm ξ).symm

/-- Identity under the stated parameter and domain assumptions: `Real.incEllIntFm ((-1) ^ n * a) m
= (-1) ^ n * Real.incEllIntFm a m`. -/
lemma p22R1_neg_one_zpow_F {m : ℝ} (n : ℤ) (a : ℝ) :
    Real.incEllIntFm ((-1) ^ n * a) m = (-1) ^ n * Real.incEllIntFm a m := by
  rcases Int.even_or_odd n with h | h
  · simp [h.neg_one_zpow]
  · simp [h.neg_one_zpow, Real.incEllIntFm_neg]

/-- Identity under the stated parameter and domain assumptions: `sin A = sin a ↔ ∃ n : ℤ, A = (-1)
^ n * a + n * π`. -/
lemma p22R1_sin_eq_iff (A a : ℝ) :
    sin A = sin a ↔ ∃ n : ℤ, A = (-1) ^ n * a + n * π := by
  rw [eq_comm, Real.sin_eq_sin_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨2 * k, by rw [(even_two_mul k).neg_one_zpow]; push_cast; linarith⟩
    · exact ⟨2 * k + 1, by rw [(odd_two_mul_add_one k).neg_one_zpow]; push_cast; linarith⟩
  · rintro ⟨n, rfl⟩
    rcases Int.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine ⟨j, Or.inl ?_⟩; rw [hj, (show Even (j + j) from ⟨j, rfl⟩).neg_one_zpow]
      push_cast; ring
    · refine ⟨j, Or.inr ?_⟩; rw [hj, (odd_two_mul_add_one j).neg_one_zpow]; push_cast; ring

/-- DLMF 22.15.8: the general real solution of `sn(ξ, k) = x`, `-1 ≤ x ≤ 1`, is
`ξ = (-1)ᵐ arcsn(x, k) + 2mK`, `m ∈ ℤ`. -/
@[dlmf 22.15.E8 "special case: real parameter k² < 1"]
theorem Real.jacobiSnm_eq_iff (hm : m < 1) {x ξ : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    Real.jacobiSnm ξ m = x ↔
      ∃ n : ℤ, ξ = (-1) ^ n * Real.jacobiArcsnm x m + 2 * n * Real.compEllIntKm m := by
  have key : ∀ n : ℤ, (-1) ^ n * Real.jacobiArcsnm x m + 2 * n * Real.compEllIntKm m =
      Real.incEllIntFm ((-1) ^ n * arcsin x + n * π) m := by
    intro n; rw [p22R1_F_add_int_pi hm, p22R1_neg_one_zpow_F, Real.jacobiArcsnm]
  simp only [key, p22R1_eq_F_iff hm]
  rw [Real.jacobiSnm, ← p22R1_sin_eq_iff, Real.sin_arcsin hx0 hx1]

/-- DLMF 22.15.9: the general real solution of `cn(η, k) = x`, `-1 ≤ x ≤ 1`, is
`η = ± arccn(x, k) + 4mK`, `m ∈ ℤ`. -/
@[dlmf 22.15.E9 "special case: real parameter k² < 1"]
theorem Real.jacobiCnm_eq_iff (hm : m < 1) {x η : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    Real.jacobiCnm η m = x ↔ ∃ n : ℤ, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      η = σ * Real.jacobiArccnm x m + 4 * n * Real.compEllIntKm m := by
  have key : ∀ (n : ℤ) (σ : ℝ), (σ = 1 ∨ σ = -1) →
      σ * Real.jacobiArccnm x m + 4 * n * Real.compEllIntKm m =
      Real.incEllIntFm (σ * arccos x + ((2 * n : ℤ) : ℝ) * π) m := by
    intro n σ hσ
    rw [p22R1_F_add_int_pi hm, Real.jacobiArccnm]
    rcases hσ with rfl | rfl
    · push_cast; ring
    · simp only [neg_one_mul, Real.incEllIntFm_neg]; push_cast; ring
  constructor
  · intro h
    rw [Real.jacobiCnm, ← Real.cos_arccos hx0 hx1, Real.cos_eq_cos_iff] at h
    obtain ⟨n, h | h⟩ := h
    · refine ⟨-n, 1, Or.inl rfl, ?_⟩
      rw [key (-n) 1 (Or.inl rfl), p22R1_eq_F_iff hm]; push_cast; linarith
    · refine ⟨n, -1, Or.inr rfl, ?_⟩
      rw [key n (-1) (Or.inr rfl), p22R1_eq_F_iff hm]; push_cast; linarith
  · rintro ⟨n, σ, hσ, h⟩
    rw [key n σ hσ, p22R1_eq_F_iff hm] at h
    rw [Real.jacobiCnm, h]
    push_cast
    rw [show σ * arccos x + 2 * n * π = σ * arccos x + (n : ℤ) * (2 * π) by ring,
      Real.cos_add_int_mul_two_pi]
    rcases hσ with rfl | rfl
    · simp [Real.cos_arccos hx0 hx1]
    · simp [Real.cos_arccos hx0 hx1]

/-- DLMF 22.15.10: the general real solution of `dn(ζ, k) = x`, `k' ≤ x ≤ 1`, is
`ζ = ± arcdn(x, k) + 2mK`, `m ∈ ℤ` (`0 < k² < 1`). -/
@[dlmf 22.15.E10 "special case: real parameter 0 < k² < 1"]
theorem Real.jacobiDnm_eq_iff (hm0 : 0 < m) (hm : m < 1) {x ζ : ℝ} (hx0 : √(1 - m) ≤ x)
    (hx1 : x ≤ 1) :
    Real.jacobiDnm ζ m = x ↔ ∃ n : ℤ, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ζ = σ * Real.jacobiArcdnm x m + 2 * n * Real.compEllIntKm m := by
  have hx : 0 ≤ x := le_trans (Real.sqrt_nonneg _) hx0
  have h1 : 1 - m ≤ x ^ 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - m by linarith)
    nlinarith [Real.sqrt_nonneg (1 - m)]
  have hq0 : 0 ≤ (1 - x ^ 2) / m := div_nonneg (by nlinarith) hm0.le
  have hq1 : (1 - x ^ 2) / m ≤ 1 := by rw [div_le_one hm0]; linarith
  set s0 := √((1 - x ^ 2) / m) with hs0
  have hs0sq : s0 ^ 2 = (1 - x ^ 2) / m := Real.sq_sqrt hq0
  have hs1 : s0 ≤ 1 := Real.sqrt_le_one.mpr hq1
  have hsn : sin (arcsin s0) = s0 := Real.sin_arcsin (by linarith [Real.sqrt_nonneg ((1 - x ^ 2) / m)]) hs1
  have key : ∀ (n : ℤ) (σ : ℝ), (σ = 1 ∨ σ = -1) →
      σ * Real.jacobiArcdnm x m + 2 * n * Real.compEllIntKm m =
      Real.incEllIntFm (σ * arcsin s0 + n * π) m := by
    intro n σ hσ
    rw [p22R1_F_add_int_pi hm, Real.jacobiArcdnm]
    rcases hσ with rfl | rfl
    · simp [hs0]
    · simp [Real.incEllIntFm_neg, hs0]
  -- dn ζ = x ↔ sin² am = s0²
  have hdn : Real.jacobiDnm ζ m = x ↔ sin (Real.jacobiAmm ζ m) ^ 2 = s0 ^ 2 := by
    have hp : 0 ≤ 1 - m * sin (Real.jacobiAmm ζ m) ^ 2 := by
      nlinarith [sin_sq_le_one (Real.jacobiAmm ζ m)]
    rw [Real.jacobiDnm, Real.jacobiSnm, ← Real.sqrt_eq_rpow, hs0sq]
    constructor
    · intro h
      have := Real.sq_sqrt hp
      rw [h] at this
      field_simp; linarith
    · intro h
      rw [h, show 1 - m * ((1 - x ^ 2) / m) = x ^ 2 by field_simp; ring, Real.sqrt_sq hx]
  rw [hdn]
  constructor
  · intro h
    have h' : sin (Real.jacobiAmm ζ m) = sin (arcsin s0) ∨
        sin (Real.jacobiAmm ζ m) = sin (-arcsin s0) := by
      rw [Real.sin_neg, hsn]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases h' with h' | h'
    · obtain ⟨n, hn⟩ := (p22R1_sin_eq_iff _ _).mp h'
      rcases Int.even_or_odd n with he | ho
      · refine ⟨n, 1, Or.inl rfl, ?_⟩
        rw [key n 1 (Or.inl rfl), p22R1_eq_F_iff hm, hn, he.neg_one_zpow]
      · refine ⟨n, -1, Or.inr rfl, ?_⟩
        rw [key n (-1) (Or.inr rfl), p22R1_eq_F_iff hm, hn, ho.neg_one_zpow]
    · obtain ⟨n, hn⟩ := (p22R1_sin_eq_iff _ _).mp h'
      rcases Int.even_or_odd n with he | ho
      · refine ⟨n, -1, Or.inr rfl, ?_⟩
        rw [key n (-1) (Or.inr rfl), p22R1_eq_F_iff hm, hn, he.neg_one_zpow]; ring
      · refine ⟨n, 1, Or.inl rfl, ?_⟩
        rw [key n 1 (Or.inl rfl), p22R1_eq_F_iff hm, hn, ho.neg_one_zpow]; ring
  · rintro ⟨n, σ, hσ, h⟩
    rw [key n σ hσ, p22R1_eq_F_iff hm] at h
    rw [h, Real.sin_add_int_mul_pi, mul_pow, ← zpow_natCast, ← zpow_mul]
    rcases hσ with rfl | rfl
    · rw [one_mul, hsn]; rw [Even.neg_one_zpow ⟨n, by push_cast; ring⟩]; ring
    · rw [neg_one_mul, Real.sin_neg, hsn]; rw [Even.neg_one_zpow ⟨n, by push_cast; ring⟩]; ring

end Principal

/-! ### §22.15(ii): integral representations -/

section Integrals

variable {m : ℝ}

/-- DLMF 22.15.12: `arcsn(x, k) = ∫₀ˣ dt/√((1 - t²)(1 - k²t²))` for `-1 ≤ x ≤ 1`. -/
@[dlmf 22.15.E12 "special case: real parameter m = k² < 1"]
theorem Real.jacobiArcsnm_eq_integral (hm : m < 1) {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    Real.jacobiArcsnm x m = ∫ t in (0 : ℝ)..x, 1 / √((1 - t ^ 2) * (1 - m * t ^ 2)) := by
  rcases le_total 0 x with hx | hx
  · rw [Real.integral_recip_sqrt_eq_incEllIntFm hm hx hx1, Real.jacobiArcsnm]
  · have h := Real.integral_recip_sqrt_eq_incEllIntFm hm (neg_nonneg.mpr hx) (by linarith)
    rw [Real.arcsin_neg, Real.incEllIntFm_neg] at h
    have hneg : (∫ t in (0 : ℝ)..x, 1 / √((1 - t ^ 2) * (1 - m * t ^ 2))) =
        -∫ t in (0 : ℝ)..-x, 1 / √((1 - t ^ 2) * (1 - m * t ^ 2)) := by
      have hc := intervalIntegral.integral_comp_neg (a := 0) (b := -x)
        (fun t => 1 / √((1 - t ^ 2) * (1 - m * t ^ 2)))
      simp only [neg_sq, neg_neg, neg_zero] at hc
      rw [hc, intervalIntegral.integral_symm x 0]
    rw [hneg, h, neg_neg, Real.jacobiArcsnm]

/-- DLMF 22.15.11: `x = ∫₀^{sn(x,k)} dt/√((1 - t²)(1 - k²t²))`; proved for `-K ≤ x ≤ K`
(stronger than DLMF's `-1 ≤ x ≤ 1`, since `K ≥ π/2 > 1`). -/
@[dlmf 22.15.E11 "stronger than DLMF: -K ≤ x ≤ K; real parameter m = k² < 1"]
theorem Real.eq_integral_jacobiSnm (hm : m < 1) {x : ℝ} (hx : |x| ≤ Real.compEllIntKm m) :
    x = ∫ t in (0 : ℝ)..Real.jacobiSnm x m, 1 / √((1 - t ^ 2) * (1 - m * t ^ 2)) := by
  have hs := (je22b_abs_le_one (m := m) x).1
  rw [← Real.jacobiArcsnm_eq_integral hm (neg_le_of_abs_le hs) (le_of_abs_le hs),
    Real.jacobiArcsnm_jacobiSnm hm hx]

open MeasureTheory Set in
/-- Substitution `t = f θ` for a continuous strictly decreasing `f` on `[a, b]`. -/
lemma p22R1_subst_anti {f f' g h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (ha : StrictAntiOn f (Icc a b))
    (hd : ∀ θ ∈ Ioo a b, HasDerivAt f (f' θ) θ)
    (hg : ∀ θ ∈ Ioo a b, |f' θ| * g (f θ) = h θ) :
    ∫ t in f b..f a, g t = ∫ θ in a..b, h θ := by
  have hfab : f b ≤ f a := ha.antitoneOn ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hcv := integral_image_eq_integral_abs_deriv_smul (f := f) (f' := f')
    (measurableSet_Ioo (a := a) (b := b)) (fun θ hθ => (hd θ hθ).hasDerivWithinAt)
    (ha.injOn.mono Ioo_subset_Icc_self) g
  rw [hc.image_Ioo_of_strictAntiOn hab ha] at hcv
  rw [intervalIntegral.integral_of_le hfab, integral_Ioc_eq_integral_Ioo, hcv,
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo fun θ hθ => by simp only [smul_eq_mul]; exact hg θ hθ

/-- DLMF 22.15.13: `arccn(x, k) = ∫ₓ¹ dt/√((1 - t²)(k'² + k²t²))` for `-1 ≤ x ≤ 1` (substitution `t = cos θ`). -/
@[dlmf 22.15.E13 "special case: real parameter m = k² < 1"]
theorem Real.jacobiArccnm_eq_integral (hm : m < 1) {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    Real.jacobiArccnm x m = ∫ t in x..1, 1 / √((1 - t ^ 2) * ((1 - m) + m * t ^ 2)) := by
  have hb := Real.arccos_nonneg x
  have hbπ := Real.arccos_le_pi x
  have h := p22R1_subst_anti (f := cos) (f' := fun θ => -sin θ)
    (g := fun t => 1 / √((1 - t ^ 2) * ((1 - m) + m * t ^ 2)))
    (h := fun θ => (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ)) hb continuous_cos.continuousOn
    (Real.strictAntiOn_cos.mono (Set.Icc_subset_Icc le_rfl hbπ))
    (fun θ _ => Real.hasDerivAt_cos θ) (fun θ hθ => ?_)
  · rw [Real.cos_arccos hx0 hx1, Real.cos_zero] at h
    rw [h, Real.jacobiArccnm, Real.incEllIntFm]
  · have hs : 0 < sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (lt_of_lt_of_le hθ.2 hbπ)
    have hp := one_sub_mul_sin_sq_pos hm θ
    rw [abs_neg, abs_of_pos hs,
      show (1 - cos θ ^ 2) * ((1 - m) + m * cos θ ^ 2) = sin θ ^ 2 * (1 - m * sin θ ^ 2) by
        linear_combination (2 * m * sin θ ^ 2 - 1 - m * (sin θ ^ 2 + cos θ ^ 2 - 1)) *
          Real.sin_sq_add_cos_sq θ,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs.le, Real.rpow_neg hp.le, ← Real.sqrt_eq_rpow]
    field_simp

/-- DLMF 22.15.14: `arcdn(x, k) = ∫ₓ¹ dt/√((1 - t²)(t² - k'²))` for `k' ≤ x ≤ 1` (substitution `t = dn`). -/
@[dlmf 22.15.E14 "special case: real parameter 0 < m = k² < 1"]
theorem Real.jacobiArcdnm_eq_integral (hm0 : 0 < m) (hm : m < 1) {x : ℝ} (hx0 : √(1 - m) ≤ x)
    (hx1 : x ≤ 1) :
    Real.jacobiArcdnm x m = ∫ t in x..1, 1 / √((1 - t ^ 2) * (t ^ 2 - (1 - m))) := by
  have hx : 0 ≤ x := le_trans (Real.sqrt_nonneg _) hx0
  have h1 : 1 - m ≤ x ^ 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - m by linarith)
    nlinarith [Real.sqrt_nonneg (1 - m)]
  have hq0 : 0 ≤ (1 - x ^ 2) / m := div_nonneg (by nlinarith) hm0.le
  have hq1 : (1 - x ^ 2) / m ≤ 1 := by rw [div_le_one hm0]; linarith
  set s0 := √((1 - x ^ 2) / m) with hs0
  have hs0sq : s0 ^ 2 = (1 - x ^ 2) / m := Real.sq_sqrt hq0
  have hs1 : s0 ≤ 1 := Real.sqrt_le_one.mpr hq1
  have hsn : sin (arcsin s0) = s0 :=
    Real.sin_arcsin (by linarith [Real.sqrt_nonneg ((1 - x ^ 2) / m)]) hs1
  set b := arcsin s0 with hbdef
  have hb0 : 0 ≤ b := Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _)
  have hb1 : b ≤ π / 2 := Real.arcsin_le_pi_div_two _
  have hpos := fun θ => one_sub_mul_sin_sq_pos hm θ
  have hanti : StrictAntiOn (fun θ => √(1 - m * sin θ ^ 2)) (Set.Icc 0 b) := by
    intro u hu v hv huv
    have hsu : 0 ≤ sin u := Real.sin_nonneg_of_nonneg_of_le_pi hu.1 (by linarith [hu.2, Real.pi_pos])
    have hsuv : sin u < sin v := Real.strictMonoOn_sin ⟨by linarith [hu.1, Real.pi_pos], by linarith [hu.2]⟩
      ⟨by linarith [hv.1, Real.pi_pos], by linarith [hv.2]⟩ huv
    apply Real.sqrt_lt_sqrt (hpos v).le
    have h2 : sin u ^ 2 < sin v ^ 2 := pow_lt_pow_left₀ hsuv hsu (by norm_num)
    nlinarith
  have h := p22R1_subst_anti (f := fun θ => √(1 - m * sin θ ^ 2))
    (f' := fun θ => -(m * sin θ * cos θ) / √(1 - m * sin θ ^ 2))
    (g := fun t => 1 / √((1 - t ^ 2) * (t ^ 2 - (1 - m))))
    (h := fun θ => (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ)) hb0
    (by fun_prop) hanti (fun θ _ => ?_) (fun θ hθ => ?_)
  · simp only [Real.sin_zero, hsn, hs0sq] at h
    rw [show 1 - m * ((1 - x ^ 2) / m) = x ^ 2 by field_simp; ring, Real.sqrt_sq hx] at h
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero,
      Real.sqrt_one] at h
    rw [h, Real.jacobiArcdnm, Real.incEllIntFm]
  · have hd := ((Real.hasDerivAt_sin θ).pow 2).const_mul m |>.const_sub 1
    convert hd.sqrt (hpos θ).ne' using 1
    simp; ring
  · have hs : 0 < sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hc : 0 < cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
    have hp := hpos θ
    have hsq : 0 < √(1 - m * sin θ ^ 2) := Real.sqrt_pos.mpr hp
    rw [Real.sq_sqrt hp.le,
      show (1 - (1 - m * sin θ ^ 2)) * (1 - m * sin θ ^ 2 - (1 - m)) = (m * sin θ * cos θ) ^ 2 by
        linear_combination (-(m ^ 2 * sin θ ^ 2)) * Real.sin_sq_add_cos_sq θ,
      Real.sqrt_sq (by positivity), abs_div, abs_neg, abs_of_pos (by positivity),
      abs_of_pos hsq, Real.rpow_neg hp.le, ← Real.sqrt_eq_rpow]
    field_simp

open Set in
/-- `∫_{t₀}^{f φ} g = F(φ|m)` for an increasing substitution `t = f θ` with `f 0 = t₀` and
`f' · g ∘ f = (1 - m sin²)^{-1/2}`. -/
lemma p22R1_arc_subst {m : ℝ} {f f' g : ℝ → ℝ} {a b φ : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b)
    (hφ : φ ∈ Icc a b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ θ ∈ Ioo a b, HasDerivAt f (f' θ) θ) (hpos : ∀ θ ∈ Ioo a b, 0 < f' θ)
    {t0 : ℝ} (f0 : f 0 = t0)
    (hg : ∀ θ ∈ Ioo a b, f' θ * g (f θ) = (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ)) :
    ∫ t in t0..f φ, g t = Real.incEllIntFm φ m := by
  have mono : StrictMonoOn f (Icc a b) := strictMonoOn_of_deriv_pos (convex_Icc a b) hc
    (fun x hx => by rw [interior_Icc] at hx; rw [(hd x hx).deriv]; exact hpos x hx)
  have hg' : ∀ θ ∈ Ioo a b, |f' θ| * g (f θ) = (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ) :=
    fun θ hθ => by rw [abs_of_pos (hpos θ hθ)]; exact hg θ hθ
  rw [Real.incEllIntFm]
  rcases le_total 0 φ with h | h
  · have hs : Icc 0 φ ⊆ Icc a b := Icc_subset_Icc ha hφ.2
    have hs' : Ioo 0 φ ⊆ Ioo a b := Ioo_subset_Ioo ha hφ.2
    have := p22R1_subst_mono h (hc.mono hs) (mono.mono hs) (fun θ hθ => hd θ (hs' hθ))
      (fun θ hθ => hg' θ (hs' hθ))
    rwa [f0] at this
  · have hs : Icc φ 0 ⊆ Icc a b := Icc_subset_Icc hφ.1 hb
    have hs' : Ioo φ 0 ⊆ Ioo a b := Ioo_subset_Ioo hφ.1 hb
    have := p22R1_subst_mono h (hc.mono hs) (mono.mono hs) (fun θ hθ => hd θ (hs' hθ))
      (fun θ hθ => hg' θ (hs' hθ))
    rw [f0] at this
    rw [intervalIntegral.integral_symm, this, ← intervalIntegral.integral_symm]

/-- DLMF 22.15.15: `arccd` inverts `cd`: `cd(arccd(x,k), k) = x` for `-1 ≤ x ≤ 1` (substitution `t = cos θ`). -/
@[dlmf 22.15.E15 "special case: real parameter m = k² < 1"]
theorem Real.jacobiCdm_jacobiArccdm (hm : m < 1) {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    Real.jacobiCnm (Real.jacobiArccdm x m) m / Real.jacobiDnm (Real.jacobiArccdm x m) m = x := by
  set g : ℝ → ℝ := fun t => 1 / √((1 - t ^ 2) * (1 - m * t ^ 2)) with hg
  have hK := Real.compEllIntKm_pos hm
  have I1 : ∫ t in (0 : ℝ)..1, g t = Real.compEllIntKm m :=
    (Real.compEllIntKm_eq_integral_algebraic hm).symm
  have I2 : ∫ t in (0 : ℝ)..(-1), g t = -Real.compEllIntKm m := by
    rw [← Real.jacobiArcsnm_eq_integral hm le_rfl (by norm_num), Real.jacobiArcsnm,
      Real.arcsin_neg_one, Real.incEllIntFm_neg, Real.incEllIntFm_pi_div_two]
  have h1 : IntervalIntegrable g MeasureTheory.volume 0 1 :=
    intervalIntegral.intervalIntegrable_of_integral_ne_zero (by rw [I1]; exact hK.ne')
  have h2 : IntervalIntegrable g MeasureTheory.volume 0 (-1) :=
    intervalIntegral.intervalIntegrable_of_integral_ne_zero (by rw [I2]; simpa using hK.ne')
  have h3 : IntervalIntegrable g MeasureTheory.volume (-1) 1 := h2.symm.trans h1
  have hx : IntervalIntegrable g MeasureTheory.volume 0 x :=
    h3.mono_set (by
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Set.uIcc_subset_Icc ⟨by norm_num, by norm_num⟩ ⟨hx0, hx1⟩)
  have harc : Real.jacobiArccdm x m = Real.compEllIntKm m - Real.jacobiArcsnm x m := by
    rw [Real.jacobiArccdm, ← intervalIntegral.integral_interval_sub_left h1 hx, I1,
      Real.jacobiArcsnm_eq_integral hm hx0 hx1]
  set a := Real.jacobiArcsnm x m
  obtain ⟨-, hc, hd⟩ := Real.jacobi_add_compEllIntKm hm (-a)
  obtain ⟨ns, nc, nd⟩ := jacobi_neg hm a
  rw [harc, show Real.compEllIntKm m - a = -a + Real.compEllIntKm m by ring, hc, hd, ns, nd]
  have hdn := (Real.jacobiDnm_pos hm a).ne'
  have hk : (1 - m) ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  rw [← Real.jacobiSnm_jacobiArcsnm hm hx0 hx1]
  field_simp
  rfl

/-- DLMF 22.15.16: `arcsd` inverts `sd` for `-1/k' ≤ x ≤ 1/k'` (substitution `t = sd`). -/
@[dlmf 22.15.E16 "special case: real parameter m = k² < 1"]
theorem Real.jacobiSdm_jacobiArcsdm (hm : m < 1) {x : ℝ} (hx : |x| ≤ 1 / √(1 - m)) :
    Real.jacobiSnm (Real.jacobiArcsdm x m) m / Real.jacobiDnm (Real.jacobiArcsdm x m) m = x := by
  have hp := fun θ => one_sub_mul_sin_sq_pos hm θ
  have hq := fun θ => Real.sqrt_pos.mpr (hp θ)
  have h1m : 0 < 1 - m := by linarith
  have hx2 : (1 - m) * x ^ 2 ≤ 1 := by
    have hs := Real.sqrt_pos.mpr h1m
    have : |x| * √(1 - m) ≤ 1 := by rw [le_div_iff₀ hs] at hx; exact hx
    have h2 : (|x| * √(1 - m)) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) this
    rwa [mul_pow, sq_abs, Real.sq_sqrt h1m.le, mul_comm] at h2
  have hD : 0 < 1 + m * x ^ 2 := by
    rcases eq_or_ne x 0 with h | h
    · simp [h]
    · nlinarith [sq_pos_of_ne_zero h]
  set y := x / √(1 + m * x ^ 2) with hy
  have hsD := Real.sqrt_pos.mpr hD
  have hy2 : y ^ 2 = x ^ 2 / (1 + m * x ^ 2) := by rw [hy, div_pow, Real.sq_sqrt hD.le]
  have hy1 : y ^ 2 ≤ 1 := by rw [hy2, div_le_one hD]; nlinarith
  have hyabs : -1 ≤ y ∧ y ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (y + 1), sq_nonneg (y - 1)]
  set φ := arcsin y with hφ
  have hsinφ : sin φ = y := Real.sin_arcsin hyabs.1 hyabs.2
  have hfφ : sin φ / √(1 - m * sin φ ^ 2) = x := by
    rw [hsinφ, hy2, show 1 - m * (x ^ 2 / (1 + m * x ^ 2)) = 1 / (1 + m * x ^ 2) by
      field_simp; ring, Real.sqrt_div' _ hD.le, Real.sqrt_one, hy, div_div_eq_mul_div, div_one,
      div_mul_cancel₀ x hsD.ne']
  have key := p22R1_arc_subst (m := m) (t0 := 0) (f := fun θ => sin θ / √(1 - m * sin θ ^ 2))
    (f' := fun θ => cos θ / √(1 - m * sin θ ^ 2) ^ 3)
    (g := fun t => 1 / √((1 - (1 - m) * t ^ 2) * (1 + m * t ^ 2)))
    (a := -(π / 2)) (b := π / 2) (φ := φ) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    ⟨Real.neg_pi_div_two_le_arcsin y, Real.arcsin_le_pi_div_two y⟩
    (Continuous.continuousOn (continuous_sin.div (by fun_prop) fun θ => (hq θ).ne'))
    (fun θ _ => ?_) (fun θ hθ => ?_) (by simp) (fun θ hθ => ?_)
  · rw [hfφ] at key
    rw [Real.jacobiArcsdm, key, Real.jacobiSnm, Real.jacobiDnm, Real.jacobiSnm,
      Real.jacobiAmm_incEllIntFm hm, ← Real.sqrt_eq_rpow, hfφ]
  · have hd := (hasDerivAt_sin θ).div
      ((((hasDerivAt_sin θ).pow 2).const_mul m).const_sub 1 |>.sqrt (hp θ).ne') (hq θ).ne'
    refine hd.congr_deriv ?_
    have h1 := Real.sin_sq_add_cos_sq θ
    have hq2 := Real.sq_sqrt (hp θ).le
    have hqn := (hq θ).ne'
    simp only [Pi.pow_apply]
    norm_num
    generalize √(1 - m * sin θ ^ 2) = q at *
    field_simp
    linear_combination cos θ * hq2
  · have := Real.cos_pos_of_mem_Ioo hθ
    have := hq θ
    positivity
  · have hc := Real.cos_pos_of_mem_Ioo hθ
    have hq2 := Real.sq_sqrt (hp θ).le
    have hqn := (hq θ).ne'
    have e : (1 - (1 - m) * (sin θ / √(1 - m * sin θ ^ 2)) ^ 2) *
        (1 + m * (sin θ / √(1 - m * sin θ ^ 2)) ^ 2) = (cos θ / √(1 - m * sin θ ^ 2) ^ 2) ^ 2 := by
      have h1 := Real.sin_sq_add_cos_sq θ
      generalize √(1 - m * sin θ ^ 2) = q at *
      field_simp
      linear_combination (-1 : ℝ) * h1 + (2 - sin θ ^ 2 + (q ^ 2 - 1 + m * sin θ ^ 2)) * hq2
    rw [e, Real.sqrt_sq (by positivity), Real.rpow_neg (hp θ).le, ← Real.sqrt_eq_rpow]
    field_simp

open Set in
/-- The substitution `s = 1/t` on `[1, x]`. -/
lemma p22R1_recip_subst {g h : ℝ → ℝ} {x : ℝ} (hx : 1 ≤ x)
    (hg : ∀ t ∈ Ioo 1 x, 1 / t ^ 2 * g (1 / t) = h t) :
    ∫ s in (1 / x)..1, g s = ∫ t in (1 : ℝ)..x, h t := by
  have h := p22R1_subst_anti (f := fun t : ℝ => 1 / t) (f' := fun t => -(1 / t ^ 2)) (g := g)
    (h := h) hx ?_ ?_ ?_ ?_
  · simpa using h
  · exact continuousOn_const.div continuousOn_id fun t ht => by linarith [ht.1]
  · intro a ha b hb hab
    exact one_div_lt_one_div_of_lt (by linarith [ha.1]) hab
  · intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have := (hasDerivAt_inv ht0)
    simpa [one_div] using this
  · intro t ht
    rw [abs_neg, abs_of_pos (by have := ht.1; positivity)]
    exact hg t ht

/-- DLMF 22.15.17: `arcnd` inverts `nd` for `1 ≤ x ≤ 1/k'`. -/
@[dlmf 22.15.E17 "special case: real parameter m = k² < 1"]
theorem Real.jacobiNdm_jacobiArcndm (hm : m < 1) {x : ℝ} (hx0 : 1 ≤ x) (hx1 : x ≤ 1 / √(1 - m)) :
    1 / Real.jacobiDnm (Real.jacobiArcndm x m) m = x := by
  rcases le_or_gt m 0 with hm0 | hm0
  · have hx : x = 1 := by
      have : 1 / √(1 - m) ≤ 1 := by
        rw [div_le_one (Real.sqrt_pos.mpr (by linarith))]
        exact Real.le_sqrt_of_sq_le (by linarith)
      linarith
    subst hx
    simp [Real.jacobiArcndm, Real.jacobiDnm, Real.jacobiSnm, Real.jacobiAmm_zero hm]
  have hs : 0 < √(1 - m) := Real.sqrt_pos.mpr (by linarith)
  have hxpos : 0 < x := by linarith
  have hy0 : √(1 - m) ≤ 1 / x := by
    rw [le_div_iff₀ hxpos]; rw [le_div_iff₀ hs] at hx1; linarith
  have hy1 : 1 / x ≤ 1 := by rw [div_le_one hxpos]; exact hx0
  have key : Real.jacobiArcndm x m = Real.jacobiArcdnm (1 / x) m := by
    rw [Real.jacobiArcdnm_eq_integral hm0 hm hy0 hy1, Real.jacobiArcndm]
    refine (p22R1_recip_subst hx0 fun t ht => ?_).symm
    have ht1 : 1 < t := ht.1
    have htx : t < x := ht.2
    have h1 : 0 < t ^ 2 - 1 := by nlinarith
    have h2 : 0 < 1 - (1 - m) * t ^ 2 := by
      have : (1 - m) * x ^ 2 ≤ 1 := by
        have h4 := hx1
        rw [le_div_iff₀ hs] at h4
        have h3 : (x * √(1 - m)) ^ 2 ≤ 1 := by nlinarith [mul_pos hxpos hs]
        rw [mul_pow, Real.sq_sqrt (by linarith)] at h3
        linarith
      nlinarith
    have ht0 : 0 < t := by linarith
    have e : (1 - (1 / t) ^ 2) * ((1 / t) ^ 2 - (1 - m)) =
        ((t ^ 2 - 1) * (1 - (1 - m) * t ^ 2)) / (t ^ 2) ^ 2 := by
      field_simp; try ring
    rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
    have := Real.sqrt_pos.mpr (mul_pos h1 h2)
    field_simp
  rw [key, Real.jacobiDnm_jacobiArcdnm hm0 hm hy0 hy1]
  field_simp

/-- DLMF 22.15.18: `arcdc` inverts `dc` for `1 ≤ x < ∞`. -/
@[dlmf 22.15.E18 "special case: real parameter 0 ≤ m = k² < 1"]
theorem Real.jacobiDcm_jacobiArcdcm (hm : m < 1) {x : ℝ} (hx : 1 ≤ x) :
    Real.jacobiDnm (Real.jacobiArcdcm x m) m / Real.jacobiCnm (Real.jacobiArcdcm x m) m = x := by
  have hxpos : 0 < x := by linarith
  have hy0 : -1 ≤ 1 / x := by have : 0 < 1 / x := by positivity
                              linarith
  have hy1 : 1 / x ≤ 1 := by rw [div_le_one hxpos]; exact hx
  have key : Real.jacobiArcdcm x m = Real.jacobiArccdm (1 / x) m := by
    rw [Real.jacobiArccdm, Real.jacobiArcdcm]
    refine (p22R1_recip_subst hx fun t ht => ?_).symm
    have ht1 : 1 < t := ht.1
    have h1 : 0 < t ^ 2 - 1 := by nlinarith
    have h2 : 0 < t ^ 2 - m := by nlinarith
    have ht0 : 0 < t := by linarith
    have e : (1 - (1 / t) ^ 2) * (1 - m * (1 / t) ^ 2) =
        ((t ^ 2 - 1) * (t ^ 2 - m)) / (t ^ 2) ^ 2 := by
      field_simp; try ring
    rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
    have := Real.sqrt_pos.mpr (mul_pos h1 h2)
    field_simp
  have h := Real.jacobiCdm_jacobiArccdm hm hy0 hy1
  rw [key, ← one_div_div, h]
  field_simp

/-- DLMF 22.15.19: `arcnc` inverts `nc` for `1 ≤ x < ∞`. -/
@[dlmf 22.15.E19 "special case: real parameter 0 ≤ m = k² < 1"]
theorem Real.jacobiNcm_jacobiArcncm (hm0 : 0 ≤ m) (hm : m < 1) {x : ℝ} (hx : 1 ≤ x) :
    1 / Real.jacobiCnm (Real.jacobiArcncm x m) m = x := by
  have hxpos : 0 < x := by linarith
  have hy0 : -1 ≤ 1 / x := by have : 0 < 1 / x := by positivity
                              linarith
  have hy1 : 1 / x ≤ 1 := by rw [div_le_one hxpos]; exact hx
  have key : Real.jacobiArcncm x m = Real.jacobiArccnm (1 / x) m := by
    rw [Real.jacobiArccnm_eq_integral hm hy0 hy1, Real.jacobiArcncm]
    refine (p22R1_recip_subst hx fun t ht => ?_).symm
    have ht1 : 1 < t := ht.1
    have h1 : 0 < t ^ 2 - 1 := by nlinarith
    have h2 : 0 < m + (1 - m) * t ^ 2 := by nlinarith
    have ht0 : 0 < t := by linarith
    have e : (1 - (1 / t) ^ 2) * ((1 - m) + m * (1 / t) ^ 2) =
        ((t ^ 2 - 1) * (m + (1 - m) * t ^ 2)) / (t ^ 2) ^ 2 := by
      field_simp; try ring
    rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
    have := Real.sqrt_pos.mpr (mul_pos h1 h2)
    field_simp
  rw [key, Real.jacobiCnm_jacobiArccnm hm hy0 hy1]
  field_simp

open Set MeasureTheory in
/-- The substitution `t = 1/s` taking `(0, 1/x)` onto `(x, ∞)`. -/
lemma p22R1_recip_subst_Ioi {g h : ℝ → ℝ} {x : ℝ} (hx : 0 < x)
    (hg : ∀ s ∈ Ioo 0 (1 / x), 1 / s ^ 2 * g (1 / s) = h s) :
    ∫ t in Ioi x, g t = ∫ s in (0 : ℝ)..(1 / x), h s := by
  have himg : (fun s : ℝ => 1 / s) '' Ioo 0 (1 / x) = Ioi x := by
    ext t
    simp only [mem_image, mem_Ioo, mem_Ioi]
    constructor
    · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
      rw [lt_div_iff₀ hs0]; rw [lt_div_iff₀ hx] at hs1; linarith
    · intro ht
      have ht0 : 0 < t := by linarith
      refine ⟨1 / t, ⟨by positivity, ?_⟩, by field_simp⟩
      exact one_div_lt_one_div_of_lt hx ht
  have hcv := integral_image_eq_integral_abs_deriv_smul (f := fun s : ℝ => 1 / s)
    (f' := fun s => -(1 / s ^ 2)) (measurableSet_Ioo (a := (0 : ℝ)) (b := 1 / x))
    (fun s hs => by
      have hs0 : s ≠ 0 := hs.1.ne'
      simpa [one_div] using (hasDerivAt_inv hs0).hasDerivWithinAt)
    (fun a ha b hb hab => by
      have := congrArg (fun y => 1 / y) hab
      simpa using this) g
  rw [himg] at hcv
  rw [hcv, intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  simp only [smul_eq_mul]
  rw [abs_neg, abs_of_pos (by have := hs.1; positivity)]
  exact hg s hs

/-- DLMF 22.15.21: `arcns` inverts `ns` for `1 ≤ x < ∞`. -/
@[dlmf 22.15.E21 "special case: real parameter 0 ≤ m = k² < 1"]
theorem Real.jacobiNsm_jacobiArcnsm (hm : m < 1) {x : ℝ} (hx : 1 ≤ x) :
    1 / Real.jacobiSnm (Real.jacobiArcnsm x m) m = x := by
  have hxpos : 0 < x := by linarith
  have hy0 : -1 ≤ 1 / x := by have : 0 < 1 / x := by positivity
                              linarith
  have hy1 : 1 / x ≤ 1 := by rw [div_le_one hxpos]; exact hx
  have key : Real.jacobiArcnsm x m = Real.jacobiArcsnm (1 / x) m := by
    rw [Real.jacobiArcsnm_eq_integral hm hy0 hy1, Real.jacobiArcnsm]
    refine p22R1_recip_subst_Ioi hxpos fun s hs => ?_
    have hs0 : 0 < s := hs.1
    have hs1 : s < 1 := lt_of_lt_of_le hs.2 hy1
    have h1 : 0 < 1 - s ^ 2 := by nlinarith
    have h2 : 0 < 1 - m * s ^ 2 := by nlinarith
    have e : ((1 / s) ^ 2 - 1) * ((1 / s) ^ 2 - m) = ((1 - s ^ 2) * (1 - m * s ^ 2)) / (s ^ 2) ^ 2 := by
      field_simp; try ring
    rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
    have := Real.sqrt_pos.mpr (mul_pos h1 h2)
    field_simp
  rw [key, Real.jacobiSnm_jacobiArcsnm hm hy0 hy1]
  field_simp

/-- DLMF 22.15.22: `arcds` inverts `ds` for `k' ≤ x < ∞` (`0 < m`). -/
@[dlmf 22.15.E22 "special case: real parameter 0 < m = k² < 1"]
theorem Real.jacobiDsm_jacobiArcdsm (hm0 : 0 < m) (hm : m < 1) {x : ℝ} (hx : √(1 - m) ≤ x) :
    Real.jacobiDnm (Real.jacobiArcdsm x m) m / Real.jacobiSnm (Real.jacobiArcdsm x m) m = x := by
  have hsq : 0 < √(1 - m) := Real.sqrt_pos.mpr (by linarith)
  have hxpos : 0 < x := lt_of_lt_of_le hsq hx
  have hy : |1 / x| ≤ 1 / √(1 - m) := by
    rw [abs_of_pos (by positivity)]; exact one_div_le_one_div_of_le hsq hx
  have key : Real.jacobiArcdsm x m = Real.jacobiArcsdm (1 / x) m := by
    rw [Real.jacobiArcsdm, Real.jacobiArcdsm]
    refine p22R1_recip_subst_Ioi hxpos fun s hs => ?_
    have hs0 : 0 < s := hs.1
    have hsx : s * x < 1 := by
      have h' := hs.2; rw [lt_div_iff₀ hxpos] at h'; linarith
    have h1 : 0 < 1 - (1 - m) * s ^ 2 := by
      have := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - m by linarith)
      have h5 : s * √(1 - m) ≤ s * x := mul_le_mul_of_nonneg_left hx hs0.le
      have h6 : (s * √(1 - m)) ^ 2 < 1 := by nlinarith [mul_pos hs0 hsq]
      rw [mul_pow, Real.sq_sqrt (by linarith)] at h6
      linarith
    have h2 : 0 < 1 + m * s ^ 2 := by positivity
    have e : ((1 / s) ^ 2 + m) * ((1 / s) ^ 2 - (1 - m)) =
        ((1 - (1 - m) * s ^ 2) * (1 + m * s ^ 2)) / (s ^ 2) ^ 2 := by
      field_simp; try ring
    rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
    have := Real.sqrt_pos.mpr (mul_pos h1 h2)
    field_simp
  have h := Real.jacobiSdm_jacobiArcsdm hm hy
  rw [key, ← one_div_div, h]
  field_simp

/-- DLMF 22.15.20: `arcsc` inverts `sc` on `ℝ` (substitution `t = tan θ`). -/
@[dlmf 22.15.E20 "special case: real parameter 0 ≤ m = k² < 1"]
theorem Real.jacobiScm_jacobiArcscm (hm : m < 1) (x : ℝ) :
    Real.jacobiSnm (Real.jacobiArcscm x m) m / Real.jacobiCnm (Real.jacobiArcscm x m) m = x := by
  set φ := arctan x with hφ
  have hb : |φ| < π / 2 := by rw [abs_lt]; exact ⟨Real.neg_pi_div_two_lt_arctan x, Real.arctan_lt_pi_div_two x⟩
  have hcos : ∀ θ ∈ Set.Icc (-|φ|) |φ|, 0 < cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have key := p22R1_arc_subst (m := m) (t0 := 0) (f := tan) (f' := fun θ => 1 / cos θ ^ 2)
    (g := fun t => 1 / √((1 + t ^ 2) * (1 + (1 - m) * t ^ 2)))
    (a := -|φ|) (b := |φ|) (φ := φ) (by simp) (abs_nonneg _) ⟨neg_abs_le φ, le_abs_self φ⟩
    (fun θ hθ => (Real.continuousAt_tan.mpr (hcos θ hθ).ne').continuousWithinAt)
    (fun θ hθ => Real.hasDerivAt_tan (hcos θ (Set.Ioo_subset_Icc_self hθ)).ne')
    (fun θ hθ => by have := hcos θ (Set.Ioo_subset_Icc_self hθ); positivity)
    Real.tan_zero (fun θ hθ => ?_)
  · rw [Real.tan_arctan] at key
    rw [Real.jacobiArcscm, key, Real.jacobiSnm, Real.jacobiCnm, Real.jacobiAmm_incEllIntFm hm,
      ← Real.tan_eq_sin_div_cos, Real.tan_arctan]
  · have hc := hcos θ (Set.Ioo_subset_Icc_self hθ)
    have hp := one_sub_mul_sin_sq_pos hm θ
    have e : (1 + tan θ ^ 2) * (1 + (1 - m) * tan θ ^ 2) =
        (√(1 - m * sin θ ^ 2) / cos θ ^ 2) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hp.le, Real.tan_eq_sin_div_cos]
      field_simp
      linear_combination (sin θ ^ 2 + cos θ ^ 2 + 1 - m * sin θ ^ 2) * Real.sin_sq_add_cos_sq θ
    rw [e, Real.sqrt_sq (by positivity), Real.rpow_neg hp.le, ← Real.sqrt_eq_rpow]
    have := Real.sqrt_pos.mpr hp
    field_simp

open Set MeasureTheory in
/-- DLMF 22.15.23: `arccs` inverts `cs` on `ℝ`. -/
@[dlmf 22.15.E23 "special case: real parameter 0 ≤ m = k² < 1"]
theorem Real.jacobiCsm_jacobiArccsm (hm : m < 1) (x : ℝ) :
    Real.jacobiCnm (Real.jacobiArccsm x m) m / Real.jacobiSnm (Real.jacobiArccsm x m) m = x := by
  set φ0 := π / 2 - Real.arctan x with hφ0
  have hφpos : 0 < φ0 := by linarith [Real.arctan_lt_pi_div_two x]
  have hφlt : φ0 < π := by linarith [Real.neg_pi_div_two_lt_arctan x]
  have hsinpos : ∀ φ ∈ Ioo 0 π, 0 < Real.sin φ := fun φ h => Real.sin_pos_of_pos_of_lt_pi h.1 h.2
  have hcot : ∀ t : ℝ, Real.cos (π / 2 - Real.arctan t) / Real.sin (π / 2 - Real.arctan t) = t :=
    fun t => by
      rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, ← Real.tan_eq_sin_div_cos,
        Real.tan_arctan]
  have hanti : ∀ a b : ℝ, 0 < a → a < b → b < π →
      Real.cos b / Real.sin b < Real.cos a / Real.sin a := by
    intro a b ha hab hb
    have hsa := hsinpos a ⟨ha, by linarith⟩
    have hsb := hsinpos b ⟨by linarith, hb⟩
    rw [div_lt_div_iff₀ hsb hsa]
    have : 0 < Real.sin (b - a) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [Real.sin_sub] at this
    linarith
  have himg : (fun φ => Real.cos φ / Real.sin φ) '' Ioo 0 φ0 = Ioi x := by
    ext t
    simp only [mem_image, mem_Ioo, mem_Ioi]
    constructor
    · rintro ⟨φ, ⟨h0, h1⟩, rfl⟩
      have hs := hsinpos φ ⟨h0, by linarith⟩
      have hs0 := hsinpos φ0 ⟨hφpos, hφlt⟩
      have e := hcot x
      rw [← hφ0] at e
      rw [← e, div_lt_div_iff₀ hs0 hs]
      have : 0 < Real.sin (φ0 - φ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      rw [Real.sin_sub] at this
      linarith
    · intro ht
      refine ⟨π / 2 - Real.arctan t, ⟨by linarith [Real.arctan_lt_pi_div_two t], ?_⟩, hcot t⟩
      have := Real.arctan_strictMono ht
      linarith
  have hcv := integral_image_eq_integral_abs_deriv_smul (f := fun φ => Real.cos φ / Real.sin φ)
    (f' := fun φ => -(1 / Real.sin φ ^ 2)) (measurableSet_Ioo (a := (0 : ℝ)) (b := φ0))
    (fun φ hφ => by
      have hs := (hsinpos φ ⟨hφ.1, by linarith [hφ.2]⟩).ne'
      have := (Real.hasDerivAt_cos φ).div (Real.hasDerivAt_sin φ) hs
      refine (this.congr_deriv ?_).hasDerivWithinAt
      field_simp
      linear_combination (-1 : ℝ) * Real.sin_sq_add_cos_sq φ)
    (fun a ha b hb hab => by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact absurd hab (hanti a b ha.1 h (by linarith [hb.2])).ne'
      · exact absurd hab (hanti b a hb.1 h (by linarith [ha.2])).ne)
    (fun t => 1 / √((1 + t ^ 2) * (t ^ 2 + (1 - m))))
  have hF : Real.jacobiArccsm x m = Real.incEllIntFm φ0 m := by
    rw [Real.jacobiArccsm, ← himg, hcv, Real.incEllIntFm, intervalIntegral.integral_of_le hφpos.le,
      integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun φ hφ => ?_
    have hs := hsinpos φ ⟨hφ.1, by linarith [hφ.2]⟩
    have hp := one_sub_mul_sin_sq_pos hm φ
    simp only [smul_eq_mul]
    rw [abs_neg, abs_of_pos (by positivity)]
    have e : (1 + (Real.cos φ / Real.sin φ) ^ 2) * ((Real.cos φ / Real.sin φ) ^ 2 + (1 - m)) =
        (1 - m * Real.sin φ ^ 2) / (Real.sin φ ^ 2) ^ 2 := by
      field_simp
      linear_combination (Real.sin φ ^ 2 + Real.cos φ ^ 2 + 1 - m * Real.sin φ ^ 2) *
        Real.sin_sq_add_cos_sq φ
    rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity), Real.rpow_neg hp.le,
      ← Real.sqrt_eq_rpow]
    have := Real.sqrt_pos.mpr hp
    field_simp
  rw [hF, Real.jacobiCnm, Real.jacobiSnm, Real.jacobiAmm_incEllIntFm hm, hφ0, hcot]

end Integrals

end DLMF.JacobiElliptic
