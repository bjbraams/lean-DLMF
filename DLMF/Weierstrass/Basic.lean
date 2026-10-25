/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Weierstrass lattices, `℘`, `ζ` and `σ` (DLMF §§23.2–23.3(i))

DLMF describes a lattice `𝕃` by half-periods `ω₁, ω₃` with `ℑ(ω₃/ω₁) > 0`; the lattice
generators are `2ω₁, 2ω₃` and `ω₂ = -ω₁ - ω₃` (23.2.1). Mathlib's `PeriodPair` instead stores
the *full* periods `ω₁, ω₂` (with no orientation condition). The structure `HalfPeriods`
records DLMF's data and `HalfPeriods.periodPair` is the bridge: its Mathlib periods are
`2ω₁` and `2ω₃`. Mathlib's names for full periods are therefore *not* DLMF's names; in this
area `H.ω₁, H.ω₂, H.ω₃` always denote DLMF's half-periods.

The Weierstrass `℘` and `℘'` are Mathlib's `PeriodPair.weierstrassP` and
`PeriodPair.derivWeierstrassP`; the invariants `g₂ = 60 G₄`, `g₃ = 140 G₆` are Mathlib's
`PeriodPair.g₂`, `PeriodPair.g₃`. Mathlib sums over all lattice points; the `w = 0` term is
`1/z²` in `℘` and vanishes in `G n` (`n ≥ 1`) because `0⁻¹ = 0`, which reproduces DLMF's sums
over `𝕃 ∖ {0}`. The same convention defines `weierstrassZeta` (23.2.5) and
`weierstrassSigma` (23.2.6) here: the `w = 0` summand of `ζ` is `1/z`, and the `w = 0` factor
of the product for `σ` is `1`. At lattice points the totalized values are junk where DLMF has
poles; every statement below states its domain.

The invariants-form `℘(z; g₂, g₃)` (23.3.8) is defined through a chosen lattice with the given
invariants; it agrees with `℘(z|𝕃)` for every lattice with those invariants, which uses the
(admitted) uniqueness of the lattice.
-/

@[expose] public section

open Complex PeriodPair
open scoped Real

noncomputable section

namespace DLMF.Weierstrass

/-! ### Lattices and half-periods (§23.2(i)) -/

/-- DLMF's lattice data (§23.2(i)): nonzero half-periods `ω₁, ω₃` with `ℑ(ω₃/ω₁) > 0`. The
lattice `𝕃` consists of the points `2mω₁ + 2nω₃`, `m, n ∈ ℤ`. -/
structure HalfPeriods where
  /-- The half-period `ω₁`. -/
  ω₁ : ℂ
  /-- The half-period `ω₃`. -/
  ω₃ : ℂ
  ω₁_ne_zero : ω₁ ≠ 0
  im_div_pos : 0 < (ω₃ / ω₁).im

namespace HalfPeriods

variable (H : HalfPeriods)

/-- The third half-period `ω₂ = -ω₁ - ω₃` (DLMF 23.2.1). -/
@[dlmf 23.2.E1]
def ω₂ : ℂ := -H.ω₁ - H.ω₃

/-- DLMF 23.2.1: `ω₁ + ω₂ + ω₃ = 0`. -/
@[dlmf 23.2.E1]
theorem ω₁_add_ω₂_add_ω₃ : H.ω₁ + H.ω₂ + H.ω₃ = 0 := by
  simp only [ω₂]; ring

/-- The lattice parameter `τ = ω₃/ω₁` (DLMF 23.6.1), with `ℑτ > 0`. -/
@[dlmf 23.6.E1]
def tau : ℂ := H.ω₃ / H.ω₁

/-- The nome `q = e^{iπτ}` (DLMF 23.6.1, 23.8.i). -/
@[dlmf 23.6.E1]
def nome : ℂ := cexp (π * I * H.tau)

theorem tau_im_pos : 0 < H.tau.im := H.im_div_pos

theorem ω₃_ne_zero : H.ω₃ ≠ 0 := by
  intro h
  have := H.im_div_pos
  simp [h] at this

/-- `2ω₁` and `2ω₃` are `ℝ`-linearly independent. -/
theorem linearIndependent_two_mul :
    LinearIndependent ℝ ![2 * H.ω₁, 2 * H.ω₃] := by
  refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
  have h1 := H.ω₁_ne_zero
  have key : (s : ℂ) + t * (H.ω₃ / H.ω₁) = 0 := by
    have : (2 * H.ω₁) * ((s : ℂ) + t * (H.ω₃ / H.ω₁)) = 0 := by
      rw [← hst]; simp only [Complex.real_smul]; field_simp
    simpa [h1] using this
  have hi := congrArg Complex.im key
  simp only [add_im, ofReal_im, mul_im, ofReal_re, zero_mul, add_zero, zero_add,
    Complex.zero_im] at hi
  have ht : t = 0 := by
    rcases mul_eq_zero.mp hi with h | h
    · exact h
    · exact absurd h (ne_of_gt H.im_div_pos)
  subst ht
  simpa using key

/-- Half-periods `ω₁ = ω`, `ω₃ = ωτ` for `τ` in the upper half-plane. With `ω = 1/2` the
lattice generators are `1, τ` (as in DLMF 23.19.3). -/
def ofTau (ω : ℂ) (hω : ω ≠ 0) (τ : UpperHalfPlane) : HalfPeriods :=
  ⟨ω, ω * τ, hω, by rw [mul_div_cancel_left₀ _ hω]; exact τ.im_pos⟩

@[simp] theorem ofTau_ω₁ (ω : ℂ) (hω : ω ≠ 0) (τ : UpperHalfPlane) : (ofTau ω hω τ).ω₁ = ω := rfl
@[simp] theorem ofTau_ω₃ (ω : ℂ) (hω : ω ≠ 0) (τ : UpperHalfPlane) :
    (ofTau ω hω τ).ω₃ = ω * τ := rfl

/-- The bridge to Mathlib: the `PeriodPair` with full periods `2ω₁, 2ω₃`. -/
def periodPair : PeriodPair := ⟨2 * H.ω₁, 2 * H.ω₃, H.linearIndependent_two_mul⟩

@[simp] theorem periodPair_ω₁ : H.periodPair.ω₁ = 2 * H.ω₁ := rfl
@[simp] theorem periodPair_ω₂ : H.periodPair.ω₂ = 2 * H.ω₃ := rfl

/-- The lattice `𝕃` with generators `2ω₁, 2ω₃`. -/
abbrev lattice : Submodule ℤ ℂ := H.periodPair.lattice

/-- DLMF §23.2(i): `𝕃 = {2mω₁ + 2nω₃ : m, n ∈ ℤ}`. -/
@[dlmf 23.2.i]
theorem mem_lattice_iff {z : ℂ} : z ∈ H.lattice ↔ ∃ m n : ℤ, z = 2 * m * H.ω₁ + 2 * n * H.ω₃ := by
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by simp; ring⟩
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by simp; ring⟩

theorem two_mul_ω₁_mem : 2 * H.ω₁ ∈ H.lattice := H.periodPair.ω₁_mem_lattice
theorem two_mul_ω₃_mem : 2 * H.ω₃ ∈ H.lattice := H.periodPair.ω₂_mem_lattice
theorem two_mul_ω₂_mem : 2 * H.ω₂ ∈ H.lattice := by
  have : 2 * H.ω₂ = -(2 * H.ω₁) - 2 * H.ω₃ := by simp [ω₂]; ring
  rw [this]
  exact sub_mem (neg_mem H.two_mul_ω₁_mem) H.two_mul_ω₃_mem

/-- DLMF §23.2(i): with `ω₂` as in 23.2.1, `2ω₂, 2ω₃` are also generators of `𝕃`. -/
@[dlmf 23.2.i]
theorem span_two_ω₂_two_ω₃ :
    Submodule.span ℤ {2 * H.ω₂, 2 * H.ω₃} = H.lattice := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (by
      rintro x (rfl | rfl)
      exacts [H.two_mul_ω₂_mem, H.two_mul_ω₃_mem])
  · refine Submodule.span_le.mpr ?_
    rintro x (rfl | rfl)
    · have : H.periodPair.ω₁ = -(2 * H.ω₂) - 2 * H.ω₃ := by simp [ω₂]; ring
      rw [this]
      exact sub_mem (neg_mem (Submodule.subset_span (by simp)))
        (Submodule.subset_span (by simp))
    · exact Submodule.subset_span (by simp)

/-- DLMF §23.2(i): `2ω₂, 2ω₁` are also generators of `𝕃`. -/
@[dlmf 23.2.i]
theorem span_two_ω₂_two_ω₁ :
    Submodule.span ℤ {2 * H.ω₂, 2 * H.ω₁} = H.lattice := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (by
      rintro x (rfl | rfl)
      exacts [H.two_mul_ω₂_mem, H.two_mul_ω₁_mem])
  · refine Submodule.span_le.mpr ?_
    rintro x (rfl | rfl)
    · exact Submodule.subset_span (by simp)
    · have : H.periodPair.ω₂ = -(2 * H.ω₂) - 2 * H.ω₁ := by simp [ω₂]; ring
      rw [this]
      exact sub_mem (neg_mem (Submodule.subset_span (by simp)))
        (Submodule.subset_span (by simp))

/-- Integer coordinates with respect to `2ω₁, 2ω₃` are unique. -/
theorem p23R1_int_coord_eq_zero {m n : ℤ} (h : (m : ℂ) * (2 * H.ω₁) + n * (2 * H.ω₃) = 0) :
    m = 0 ∧ n = 0 := by
  have := LinearIndependent.pair_iff.mp H.linearIndependent_two_mul (m : ℝ) (n : ℝ)
    (by simpa [Complex.real_smul] using h)
  exact_mod_cast this

/-- `ℑ((cω₁ + dω₃)/(aω₁ + bω₃)) = (ad - bc) ℑτ / |a + bτ|²`. -/
theorem p23R1_im_div (a b c d : ℤ) :
    ((c * H.ω₁ + d * H.ω₃) / (a * H.ω₁ + b * H.ω₃)).im =
      ((a * d - b * c : ℤ) : ℝ) * H.tau.im / normSq (a + b * H.tau) := by
  have h1 := H.ω₁_ne_zero
  have heq : (c * H.ω₁ + d * H.ω₃) / (a * H.ω₁ + b * H.ω₃) =
      (c + d * H.tau) / (a + b * H.tau) := by
    rw [← mul_div_mul_right (c + d * H.tau) (a + b * H.tau) h1]
    simp only [tau]
    congr 1 <;> field_simp
  rw [heq, div_im, ← sub_div]
  congr 1
  simp only [add_re, add_im, mul_re, mul_im, intCast_re, intCast_im, zero_mul, sub_zero,
    add_zero, zero_add]
  push_cast
  ring

/-- DLMF 23.2.2–23.2.3: for integers `a, b, c, d` and `χ₁ = aω₁ + bω₃`, `χ₃ = cω₁ + dω₃`,
the numbers `2χ₁, 2χ₃` are (DLMF-oriented, `ℑ(χ₃/χ₁) > 0`) generators of `𝕃` iff
`ad - bc = 1`. The orientation condition is part of DLMF's notion of generators
(§23.2(i)); without it the condition would be `ad - bc = ±1`. -/
@[dlmf 23.2.E2, dlmf 23.2.E3]
theorem generators_iff (a b c d : ℤ) :
    (Submodule.span ℤ {2 * (a * H.ω₁ + b * H.ω₃), 2 * (c * H.ω₁ + d * H.ω₃)} = H.lattice ∧
      0 < ((c * H.ω₁ + d * H.ω₃) / (a * H.ω₁ + b * H.ω₃)).im) ↔ a * d - b * c = 1 := by
  have hlat : H.lattice = Submodule.span ℤ {2 * H.ω₁, 2 * H.ω₃} := rfl
  have htau := H.tau_im_pos
  rw [H.p23R1_im_div, hlat]
  constructor
  · rintro ⟨hspan, hpos⟩
    have m1 : 2 * H.ω₁ ∈ Submodule.span ℤ {2 * (a * H.ω₁ + b * H.ω₃), 2 * (c * H.ω₁ + d * H.ω₃)} :=
      hspan ▸ Submodule.subset_span (by simp)
    have m3 : 2 * H.ω₃ ∈ Submodule.span ℤ {2 * (a * H.ω₁ + b * H.ω₃), 2 * (c * H.ω₁ + d * H.ω₃)} :=
      hspan ▸ Submodule.subset_span (by simp)
    obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp m1
    obtain ⟨r, s, hrs⟩ := Submodule.mem_span_pair.mp m3
    simp only [zsmul_eq_mul] at hpq hrs
    obtain ⟨e1, e2⟩ := H.p23R1_int_coord_eq_zero (m := p * a + q * c - 1) (n := p * b + q * d)
      (by push_cast; linear_combination hpq)
    obtain ⟨e3, e4⟩ := H.p23R1_int_coord_eq_zero (m := r * a + s * c) (n := r * b + s * d - 1)
      (by push_cast; linear_combination hrs)
    have hdet : (p * s - q * r) * (a * d - b * c) = 1 := by
      linear_combination (r * b + s * d) * e1 + e4 - (r * a + s * c) * e2 + 0 * e3
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exfalso
      rw [h] at hpos
      have : ((-1 : ℤ) : ℝ) * H.tau.im / normSq (a + b * H.tau) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by push_cast; linarith) (normSq_nonneg _)
      linarith
  · intro hdet
    refine ⟨le_antisymm ?_ ?_, ?_⟩
    · refine Submodule.span_le.mpr ?_
      rintro x (rfl | rfl)
      · rw [show 2 * (a * H.ω₁ + b * H.ω₃) = a • (2 * H.ω₁) + b • (2 * H.ω₃) by
          simp only [zsmul_eq_mul]; ring]
        exact Submodule.mem_span_pair.mpr ⟨a, b, rfl⟩
      · rw [show 2 * (c * H.ω₁ + d * H.ω₃) = c • (2 * H.ω₁) + d • (2 * H.ω₃) by
          simp only [zsmul_eq_mul]; ring]
        exact Submodule.mem_span_pair.mpr ⟨c, d, rfl⟩
    · refine Submodule.span_le.mpr ?_
      have hdet' : (a : ℂ) * d - b * c = 1 := by exact_mod_cast hdet
      rintro x (rfl | rfl)
      · refine Submodule.mem_span_pair.mpr ⟨d, -b, ?_⟩
        simp only [zsmul_eq_mul]; push_cast
        linear_combination (2 * H.ω₁) * hdet'
      · refine Submodule.mem_span_pair.mpr ⟨-c, a, ?_⟩
        simp only [zsmul_eq_mul]; push_cast
        linear_combination (2 * H.ω₃) * hdet'
    · rw [hdet]
      have hz : (a : ℂ) + b * H.tau ≠ 0 := by
        intro hz
        have hi := congrArg Complex.im hz
        have hr := congrArg Complex.re hz
        simp at hi hr
        rcases hi with hb | hi
        · subst hb; simp at hr; subst hr; simp at hdet
        · linarith
      have := normSq_pos.mpr hz
      push_cast
      positivity

end HalfPeriods

/-! ### The functions `ζ` and `σ` (§23.2(ii)) -/

/-- The Weierstrass zeta function (DLMF 23.2.5)
`ζ(z) = 1/z + ∑_{w ∈ 𝕃∖{0}} (1/(z-w) + 1/w + z/w²)`. The sum runs over all of `𝕃`: by Lean's
`1/0 = 0` the `w = 0` summand is `1/z`. At a lattice point `z = w₀` the summand `1/(z - w₀)`
is `0`, so the value there is the regular part of `ζ` at its pole. -/
@[dlmf 23.2.E5]
def weierstrassZeta (L : PeriodPair) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, (1 / (z - l) + 1 / l + z / l ^ 2)

/-- The Weierstrass sigma function (DLMF 23.2.6)
`σ(z) = z ∏_{w ∈ 𝕃∖{0}} (1 - z/w) exp(z/w + z²/(2w²))`. The product runs over all of `𝕃`:
by Lean's `z/0 = 0` the `w = 0` factor is `1`. -/
@[dlmf 23.2.E6]
def weierstrassSigma (L : PeriodPair) (z : ℂ) : ℂ :=
  z * ∏' l : L.lattice, ((1 - z / l) * cexp (z / l + z ^ 2 / (2 * l ^ 2)))

/-- The summand of the zeta series is `z²/(w²(z - w))`. -/
theorem wp23_zeta_summand (z w : ℂ) (hw : w ≠ 0) (hz : z ≠ w) :
    1 / (z - w) + 1 / w + z / w ^ 2 = z ^ 2 / (w ^ 2 * (z - w)) := by
  have : z - w ≠ 0 := sub_ne_zero.mpr hz
  field_simp
  ring

/-- Locally uniform bound for the zeta summand: `‖z²/(w²(z-w))‖ ≤ 2r²‖w‖⁻³`. -/
theorem wp23_zeta_bound (r : ℝ) (hr : 0 < r) (s : ℂ) (hs : ‖s‖ < r) (l : ℂ) (h : 2 * r ≤ ‖l‖) :
    ‖1 / (s - l) + 1 / l + s / l ^ 2‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
  have hl : 0 < ‖l‖ := by linarith
  have hl0 : l ≠ 0 := norm_pos_iff.mp hl
  have hsl : s ≠ l := by rintro rfl; linarith
  have hsl' : ‖l‖ / 2 ≤ ‖s - l‖ := by
    rw [norm_sub_rev]; exact .trans (by linarith) (norm_sub_norm_le l s)
  rw [wp23_zeta_summand s l hl0 hsl, norm_div, norm_mul, norm_pow, norm_pow,
    Real.rpow_neg hl.le]
  have h1 : ‖s‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hs.le 2
  calc ‖s‖ ^ 2 / (‖l‖ ^ 2 * ‖s - l‖) ≤ r ^ 2 / (‖l‖ ^ 2 * (‖l‖ / 2)) := by
        gcongr
    _ = 2 * r ^ 2 * (‖l‖ ^ 3)⁻¹ := by field_simp
    _ = _ := by norm_cast

/-- `ζ` is odd (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem weierstrassZeta_neg (L : PeriodPair) (z : ℂ) :
    weierstrassZeta L (-z) = -weierstrassZeta L z := by
  simp only [weierstrassZeta]
  rw [← (Equiv.neg L.lattice).tsum_eq, ← tsum_neg]
  refine tsum_congr fun l => ?_
  simp only [Equiv.neg_apply, NegMemClass.coe_neg]
  rw [show -z - -(l : ℂ) = -(z - l) by ring, div_neg, div_neg, neg_sq]
  ring

/-- `σ` is odd (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem weierstrassSigma_neg (L : PeriodPair) (z : ℂ) :
    weierstrassSigma L (-z) = -weierstrassSigma L z := by
  simp only [weierstrassSigma]
  rw [← (Equiv.neg L.lattice).tprod_eq, neg_mul]
  congr 2
  refine tprod_congr fun l => ?_
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, neg_div_neg_eq, neg_sq]

/-- `σ` vanishes at every lattice point (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem weierstrassSigma_eq_zero_of_mem (L : PeriodPair) {z : ℂ} (hz : z ∈ L.lattice) :
    weierstrassSigma L z = 0 := by
  by_cases h0 : z = 0
  · simp [weierstrassSigma, h0]
  rw [weierstrassSigma, (hasProd_zero_of_exists_eq_zero ⟨⟨z, hz⟩, by simp [h0]⟩).tprod_eq,
    mul_zero]

/-- The double series for `ζ` converges absolutely and locally uniformly on `ℂ` (with the
totalized summands at lattice points), DLMF §23.2(ii). -/
@[dlmf 23.2.ii]
theorem hasSumLocallyUniformly_weierstrassZeta (L : PeriodPair) :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) ↦ 1 / (z - l) + 1 / l + z / l ^ 2)
      (weierstrassZeta L) := by
  refine L.hasSumLocallyUniformly_aux (u := (2 * · ^ 2 * ‖·‖ ^ (-3 : ℝ))) _
    (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr ↦
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  exact wp23_zeta_bound r hr s hs l h

section p23R1Sigma

open Filter Topology

/-- The Weierstrass elementary factor bound: `‖(1 - u)e^{u + u²/2} - 1‖ ≤ 2‖u‖³` for
`‖u‖ ≤ 1/2`. -/
theorem p23R1_norm_elementary_factor_sub_one_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖(1 - u) * cexp (u + u ^ 2 / 2) - 1‖ ≤ 2 * ‖u‖ ^ 3 := by
  have hu1 : ‖-u‖ < 1 := by rw [norm_neg]; linarith
  have h1u : (1 : ℂ) - u ≠ 0 := by
    intro h
    have : u = 1 := by linear_combination -h
    rw [this, norm_one] at hu; linarith
  have hT : logTaylor (2 + 1) (-u) = -u - u ^ 2 / 2 := by
    simp [logTaylor, Finset.sum_range_succ]; ring
  have hb := norm_log_sub_logTaylor_le 2 hu1
  rw [hT, norm_neg, ← sub_eq_add_neg] at hb
  set w := log (1 - u) - (-u - u ^ 2 / 2) with hw
  have hwb : ‖w‖ ≤ 2 / 3 * ‖u‖ ^ 3 := by
    refine hb.trans ?_
    have h0 : 0 ≤ ‖u‖ := norm_nonneg u
    have : (1 - ‖u‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    push_cast
    calc ‖u‖ ^ (2 + 1) * (1 - ‖u‖)⁻¹ / (2 + 1) ≤ ‖u‖ ^ (2 + 1) * 2 / (2 + 1) := by
          gcongr
      _ = 2 / 3 * ‖u‖ ^ 3 := by ring
  have heq : (1 - u) * cexp (u + u ^ 2 / 2) = cexp w := by
    rw [hw, show log (1 - u) - (-u - u ^ 2 / 2) = log (1 - u) + (u + u ^ 2 / 2) by ring,
      Complex.exp_add (log _), Complex.exp_log h1u]
  rw [heq]
  have hw1 : ‖w‖ ≤ 1 := by
    refine hwb.trans ?_
    have : ‖u‖ ^ 3 ≤ (1 / 2) ^ 3 := by gcongr
    linarith
  calc ‖cexp w - 1‖ ≤ 2 * ‖w‖ := norm_exp_sub_one_le hw1
    _ ≤ 2 * (2 / 3 * ‖u‖ ^ 3) := by gcongr
    _ ≤ 2 * ‖u‖ ^ 3 := by nlinarith [pow_nonneg (norm_nonneg u) 3]

/-- The Weierstrass factor of `σ` at the lattice point `l`. -/
noncomputable def p23R1_sigmaFactor (l z : ℂ) : ℂ := (1 - z / l) * cexp (z / l + z ^ 2 / (2 * l ^ 2))

/-- Bound for the Weierstrass factor of `σ` on `‖z‖ < r` when `‖l‖ ≥ 2r`. -/
theorem p23R1_norm_sigmaFactor_sub_one_le {r : ℝ} {l z : ℂ} (hz : ‖z‖ < r) (hl : 2 * r ≤ ‖l‖) :
    ‖p23R1_sigmaFactor l z - 1‖ ≤ 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ) := by
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg z) hz
  have hl0 : 0 < ‖l‖ := by linarith
  have hu : ‖z / l‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ hl0]; linarith
  have h := p23R1_norm_elementary_factor_sub_one_le hu
  have he : p23R1_sigmaFactor l z = (1 - z / l) * cexp (z / l + (z / l) ^ 2 / 2) := by
    simp only [p23R1_sigmaFactor]; congr 3; ring
  rw [he]
  refine h.trans ?_
  rw [norm_div, div_pow, Real.rpow_neg hl0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, div_eq_mul_inv, ← mul_assoc]
  gcongr

/-- All but finitely many lattice points have norm at least `R`. -/
theorem p23R1_eventually_le_norm (L : PeriodPair) (R : ℝ) :
    ∀ᶠ l : L.lattice in cofinite, R ≤ ‖(l : ℂ)‖ := by
  refine (isCompact_iff_finite.mp (isCompact_closedBall (0 : L.lattice) R)).subset ?_
  intro l hl
  have hl' : ¬ R ≤ ‖(l : ℂ)‖ := hl
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact (not_le.mp hl').le

/-- The majorant `2r³‖l‖⁻³` is summable over the lattice. -/
theorem p23R1_summable_bound (L : PeriodPair) (r : ℝ) :
    Summable fun l : L.lattice => 2 * r ^ 3 * ‖(l : ℂ)‖ ^ (-3 : ℝ) :=
  (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _

/-- The product for `σ` converges locally uniformly on every ball. -/
theorem p23R1_hasProdLocallyUniformlyOn_sigma (L : PeriodPair) {r : ℝ} :
    HasProdLocallyUniformlyOn (fun (l : L.lattice) z => p23R1_sigmaFactor l z)
      (fun z => ∏' l : L.lattice, p23R1_sigmaFactor l z) (Metric.ball 0 r) := by
  have h := Summable.hasProdLocallyUniformlyOn_one_add (f := fun (l : L.lattice) z =>
      p23R1_sigmaFactor l z - 1) (K := Metric.ball (0 : ℂ) r) Metric.isOpen_ball
    (p23R1_summable_bound L r) ?_ ?_
  · simpa using h
  · filter_upwards [p23R1_eventually_le_norm L (2 * r)] with l hl z hz
    exact p23R1_norm_sigmaFactor_sub_one_le (by simpa using hz) hl
  · intro l
    exact (by unfold p23R1_sigmaFactor; fun_prop : Continuous fun z : ℂ =>
      p23R1_sigmaFactor l z - 1).continuousOn

/-- `∑ ‖E_l(z) - 1‖` converges for the Weierstrass factors `E_l` of `σ`. -/
theorem p23R1_summable_norm_sigmaFactor (L : PeriodPair) (z : ℂ) :
    Summable fun l : L.lattice => ‖p23R1_sigmaFactor l z - 1‖ := by
  refine Summable.of_norm_bounded_eventually (p23R1_summable_bound L (‖z‖ + 1)) ?_
  filter_upwards [p23R1_eventually_le_norm L (2 * (‖z‖ + 1))] with l hl
  rw [norm_norm]
  exact p23R1_norm_sigmaFactor_sub_one_le (by linarith) hl

/-- The Weierstrass factors of `σ` do not vanish off the lattice. -/
theorem p23R1_sigmaFactor_ne_zero (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice)
    (l : L.lattice) : p23R1_sigmaFactor l z ≠ 0 := by
  unfold p23R1_sigmaFactor
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  by_cases hl : (l : ℂ) = 0
  · simp [hl]
  · intro h
    have : z = l := by
      have := sub_eq_zero.mp h
      field_simp at this
      exact this.symm
    exact hz (this ▸ l.2)

/-- The logarithmic derivative of a Weierstrass factor of `σ` is a summand of `ζ` (the `l = 0`
summand `1/z` of `ζ` is accounted for separately). -/
theorem p23R1_logDeriv_sigmaFactor (L : PeriodPair) {x : ℂ} (hx : x ∉ L.lattice)
    (l : L.lattice) :
    logDeriv (p23R1_sigmaFactor l) x =
      (1 / (x - l) + 1 / l + x / l ^ 2) - if (l : ℂ) = 0 then 1 / x else 0 := by
  by_cases hl : (l : ℂ) = 0
  · have : p23R1_sigmaFactor l = fun _ => 1 := by
      funext z; simp [p23R1_sigmaFactor, hl]
    rw [this]
    simp [hl, logDeriv]
  · have hxl : x - l ≠ 0 := sub_ne_zero.mpr fun h => hx (h ▸ l.2)
    have h1 : HasDerivAt (fun z : ℂ => 1 - z / l) (-(1 / l)) x := by
      simpa using ((hasDerivAt_id x).div_const (l : ℂ)).const_sub 1
    have h2 : HasDerivAt (fun z : ℂ => z / l + z ^ 2 / (2 * l ^ 2)) (1 / l + 2 * x / (2 * l ^ 2)) x := by
      have := ((hasDerivAt_id' x).div_const (l : ℂ)).fun_add
        ((hasDerivAt_pow 2 x).div_const (2 * (l : ℂ) ^ 2))
      convert this using 1; simp
    have hd := h1.fun_mul h2.cexp
    have hf : p23R1_sigmaFactor l = fun z => (1 - z / l) * cexp (z / l + z ^ 2 / (2 * l ^ 2)) := rfl
    rw [logDeriv_apply, hf, hd.deriv]
    simp only [hl, ite_false, sub_zero]
    have he := Complex.exp_ne_zero (x / l + x ^ 2 / (2 * l ^ 2))
    have h1x : (1 : ℂ) - x / l ≠ 0 := by
      rw [one_sub_div hl]; exact div_ne_zero (by rwa [← neg_sub, neg_ne_zero]) hl
    rw [one_sub_div hl]
    have hlx : (l : ℂ) - x ≠ 0 := by rwa [← neg_sub, neg_ne_zero] at hxl
    field_simp
    ring

end p23R1Sigma

/-- The double product for `σ` converges (unconditionally) for every `z` (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem multipliable_weierstrassSigma (L : PeriodPair) (z : ℂ) :
    Multipliable fun l : L.lattice ↦ (1 - z / l) * cexp (z / l + z ^ 2 / (2 * l ^ 2)) :=
  ((p23R1_hasProdLocallyUniformlyOn_sigma L (r := ‖z‖ + 1)).hasProd
    (by simp)).multipliable

theorem wp23_differentiableOn_zeta_summand (L : PeriodPair) (l : L.lattice) :
    DifferentiableOn ℂ (fun z : ℂ ↦ 1 / (z - l) + 1 / l + z / l ^ 2) L.latticeᶜ := by
  intro z hz
  have : z - l ≠ 0 := sub_ne_zero.mpr fun h => hz (h ▸ l.2)
  have h : DifferentiableAt ℂ (fun w : ℂ ↦ 1 / (w - l) + 1 / l + w / l ^ 2) z := by
    fun_prop (disch := exact this)
  exact h.differentiableWithinAt

/-- `ζ` is differentiable off the lattice (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem differentiableOn_weierstrassZeta (L : PeriodPair) :
    DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ :=
  TendstoLocallyUniformlyOn.differentiableOn
    (hasSumLocallyUniformly_weierstrassZeta L).hasSumLocallyUniformlyOn
    (.of_forall fun _ ↦ .fun_sum fun l _ ↦ wp23_differentiableOn_zeta_summand L l)
    L.isClosed_lattice.isOpen_compl

/-- DLMF 23.2.7: `℘(z) = -ζ'(z)` for `z ∉ 𝕃`. -/
@[dlmf 23.2.E7]
theorem hasDerivAt_weierstrassZeta (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt (weierstrassZeta L) (-℘[L] z) z := by
  have hU : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have hd := (differentiableOn_weierstrassZeta L).differentiableAt (hU.mem_nhds hz)
  convert hd.hasDerivAt using 1
  have hT : TendstoLocallyUniformlyOn
      (fun (s : Finset L.lattice) (w : ℂ) ↦ ∑ l ∈ s, (1 / (w - l) + 1 / l + w / l ^ 2))
      (weierstrassZeta L) Filter.atTop L.latticeᶜ :=
    (hasSumLocallyUniformly_weierstrassZeta L).hasSumLocallyUniformlyOn
  have hD := (TendstoLocallyUniformlyOn.deriv hT (.of_forall fun s ↦ .fun_sum fun l _ ↦
    wp23_differentiableOn_zeta_summand L l) hU).tendsto_at hz
  have hS : HasSum (fun l : L.lattice ↦ -(1 / (z - l) ^ 2 - 1 / l ^ 2)) (-℘[L] z) :=
    (L.hasSum_weierstrassP z).neg
  refine (tendsto_nhds_unique hD ?_).symm
  have hS' : Filter.Tendsto (fun s : Finset L.lattice ↦ ∑ l ∈ s, -(1 / (z - l) ^ 2 - 1 / l ^ 2))
      Filter.atTop (nhds (-℘[L] z)) := hS
  · refine hS'.congr' (Filter.Eventually.of_forall fun s => ?_)
    simp only [Function.comp_apply]
    rw [deriv_fun_sum fun l _ =>
      (wp23_differentiableOn_zeta_summand L l).differentiableAt (hU.mem_nhds hz)]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hzl : z - l ≠ 0 := sub_ne_zero.mpr fun h => hz (h ▸ l.2)
    have : HasDerivAt (fun w : ℂ ↦ 1 / (w - l) + 1 / l + w / l ^ 2)
        (-(1 / (z - l) ^ 2 - 1 / l ^ 2)) z := by
      have h1 := ((hasDerivAt_id z).sub_const (l : ℂ)).inv hzl
      have h2 := (hasDerivAt_id z).div_const ((l : ℂ) ^ 2)
      convert (h1.add_const (1 / (l : ℂ))).add h2 using 1
      · ext w; simp [one_div]
      · simp only [id, one_div]; ring
    exact this.deriv.symm

/-- `σ` is entire (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem differentiable_weierstrassSigma (L : PeriodPair) :
    Differentiable ℂ (weierstrassSigma L) := by
  intro z
  have hU : IsOpen (Metric.ball (0 : ℂ) (‖z‖ + 1)) := Metric.isOpen_ball
  have hz : z ∈ Metric.ball (0 : ℂ) (‖z‖ + 1) := by simp
  have hd : DifferentiableOn ℂ (fun z => ∏' l : L.lattice, p23R1_sigmaFactor l z)
      (Metric.ball 0 (‖z‖ + 1)) := by
    refine (p23R1_hasProdLocallyUniformlyOn_sigma L).differentiableOn
      (.of_forall fun s => ?_) hU
    refine DifferentiableOn.fun_finsetProd fun l _ => ?_
    exact (by unfold p23R1_sigmaFactor; fun_prop : Differentiable ℂ (p23R1_sigmaFactor l))
      |>.differentiableOn
  exact (differentiableAt_id.mul (hd.differentiableAt (hU.mem_nhds hz)))

/-- The zeros of `σ` are exactly the lattice points (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem weierstrassSigma_eq_zero_iff (L : PeriodPair) {z : ℂ} :
    weierstrassSigma L z = 0 ↔ z ∈ L.lattice := by
  refine ⟨fun h => ?_, weierstrassSigma_eq_zero_of_mem L⟩
  by_contra hz
  have hz0 : z ≠ 0 := fun h0 => hz (h0 ▸ zero_mem _)
  have hne := tprod_one_add_ne_zero_of_summable (f := fun l : L.lattice => p23R1_sigmaFactor l z - 1)
    (fun l => by simpa using p23R1_sigmaFactor_ne_zero L hz l)
    (p23R1_summable_norm_sigmaFactor L z)
  simp only [add_sub_cancel] at hne
  exact mul_ne_zero hz0 hne h

/-- DLMF 23.2.8: `ζ(z) = σ'(z)/σ(z)` for `z ∉ 𝕃`. -/
@[dlmf 23.2.E8]
theorem weierstrassZeta_eq_deriv_div (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    weierstrassZeta L z = deriv (weierstrassSigma L) z / weierstrassSigma L z := by
  have hz0 : z ≠ 0 := fun h0 => hz (h0 ▸ zero_mem _)
  set U := Metric.ball (0 : ℂ) (‖z‖ + 1)
  have hU : IsOpen U := Metric.isOpen_ball
  have hzU : z ∈ U := by simp [U]
  have hfd : ∀ l : L.lattice, Differentiable ℂ (p23R1_sigmaFactor l) := fun l => by
    unfold p23R1_sigmaFactor; fun_prop
  have hprod := p23R1_hasProdLocallyUniformlyOn_sigma L (r := ‖z‖ + 1)
  have hP0 : ∏' l : L.lattice, p23R1_sigmaFactor l z ≠ 0 := by
    have := tprod_one_add_ne_zero_of_summable
      (f := fun l : L.lattice => p23R1_sigmaFactor l z - 1)
      (fun l => by simpa using p23R1_sigmaFactor_ne_zero L hz l)
      (p23R1_summable_norm_sigmaFactor L z)
    simpa using this
  -- the zeta series and the log-derivative series
  have hζ : HasSum (fun l : L.lattice => 1 / (z - l) + 1 / l + z / l ^ 2) (weierstrassZeta L z) :=
    (hasSumLocallyUniformly_weierstrassZeta L).hasSum
  have hlog : HasSum (fun l : L.lattice => logDeriv (p23R1_sigmaFactor l) z)
      (weierstrassZeta L z - 1 / z) := by
    have h0 := hasSum_ite_eq (0 : L.lattice) (1 / z)
    convert hζ.sub h0 using 1
    funext l
    rw [p23R1_logDeriv_sigmaFactor L hz l]
    congr 1
    by_cases hl : l = 0
    · subst hl; simp
    · have : (l : ℂ) ≠ 0 := by simpa using hl
      simp [hl, this]
  have hPd : DifferentiableOn ℂ (fun x => ∏' l : L.lattice, p23R1_sigmaFactor l x) U :=
    hprod.differentiableOn (.of_forall fun s => DifferentiableOn.fun_finsetProd fun l _ =>
      (hfd l).differentiableOn) hU
  have hLP := logDeriv_tprod_eq_tsum hU hzU (fun l => p23R1_sigmaFactor_ne_zero L hz l)
    (fun l => (hfd l).differentiableOn) hlog.summable ⟨_, hprod⟩ hP0
  have hσ : weierstrassSigma L = fun x => x * ∏' l : L.lattice, p23R1_sigmaFactor l x := rfl
  have hmul : logDeriv (weierstrassSigma L) z = logDeriv id z +
      logDeriv (fun x => ∏' l : L.lattice, p23R1_sigmaFactor l x) z := by
    rw [hσ]
    exact logDeriv_mul (f := id) z hz0 hP0 differentiableAt_id
      (hPd.differentiableAt (hU.mem_nhds hzU))
  rw [← logDeriv_apply, hmul, hLP, hlog.tsum_eq]
  simp [logDeriv]

/-- `ζ` has a simple pole with residue `1` at every lattice point: `ζ(z) - 1/(z - w)` is
analytic at `w ∈ 𝕃` (DLMF §23.2(ii)). With Lean's totalization the value at `z = w` is the
regular part. -/
@[dlmf 23.2.ii]
theorem analyticAt_weierstrassZeta_sub (L : PeriodPair) {w : ℂ} (hw : w ∈ L.lattice) :
    AnalyticAt ℂ (fun z ↦ weierstrassZeta L z - 1 / (z - w)) w := by
  classical
  set g : L.lattice → ℂ → ℂ := fun l z ↦
    if (l : ℂ) = w then 1 / w + z / w ^ 2 else 1 / (z - l) + 1 / l + z / l ^ 2 with hg
  have hsum : ∀ z, HasSum (fun l ↦ g l z) (weierstrassZeta L z - 1 / (z - w)) := by
    intro z
    have h1 := (hasSumLocallyUniformly_weierstrassZeta L).hasSum (x := z)
    have h2 := hasSum_ite_eq (⟨w, hw⟩ : L.lattice) (1 / (z - w))
    convert h1.sub h2 using 1
    funext l
    by_cases hl : (l : ℂ) = w
    · have : l = ⟨w, hw⟩ := Subtype.ext hl
      subst this; simp [hg]; ring
    · have : l ≠ ⟨w, hw⟩ := fun h => hl (by rw [h])
      simp [hg, hl, this]
  have hU : IsOpen ((L.lattice : Set ℂ) \ {w})ᶜ := L.isOpen_compl_lattice_sdiff
  have hloc : HasSumLocallyUniformly g (∑' l, g l ·) := by
    refine L.hasSumLocallyUniformly_aux (u := (2 * · ^ 2 * ‖·‖ ^ (-3 : ℝ))) _
      (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr ↦
      Filter.eventually_atTop.mpr ⟨max (2 * r) (‖w‖ + 1), ?_⟩
    rintro _ h s hs l rfl
    have hlw : (l : ℂ) ≠ w := by
      rintro hl; rw [hl] at h; linarith [le_max_right (2 * r) (‖w‖ + 1)]
    simp only [hg, hlw, ite_false]
    exact wp23_zeta_bound r hr s hs l ((le_max_left _ _).trans h)
  have hdiff : DifferentiableOn ℂ (∑' l, g l ·) ((L.lattice : Set ℂ) \ {w})ᶜ := by
    refine TendstoLocallyUniformlyOn.differentiableOn hloc.hasSumLocallyUniformlyOn
      (.of_forall fun _ ↦ .fun_sum fun l _ ↦ ?_) hU
    intro z hz
    by_cases hl : (l : ℂ) = w
    · simp only [hg, hl, ite_true]
      exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ ↦ 1 / w + z / w ^ 2) z)
        |>.differentiableWithinAt
    · have hzl : z - l ≠ 0 := sub_ne_zero.mpr fun h => hz ⟨h ▸ l.2, by simpa [h] using hl⟩
      simp only [hg, hl, ite_false]
      exact (by fun_prop (disch := exact hzl) :
        DifferentiableAt ℂ (fun w : ℂ ↦ 1 / (w - l) + 1 / l + w / l ^ 2) z)
        |>.differentiableWithinAt
  have heq : (fun z ↦ weierstrassZeta L z - 1 / (z - w)) = (∑' l, g l ·) :=
    funext fun z => ((hsum z).tsum_eq).symm
  rw [heq]
  exact hdiff.analyticAt (hU.mem_nhds (by simp))

/-- `ζ` is analytic off the lattice (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem analyticOnNhd_weierstrassZeta (L : PeriodPair) :
    AnalyticOnNhd ℂ (weierstrassZeta L) L.latticeᶜ :=
  (differentiableOn_weierstrassZeta L).analyticOnNhd L.isClosed_lattice.isOpen_compl

/-- The poles of `℘` are double with residue `0`: near `w ∈ 𝕃`,
`℘(z) = 1/(z-w)² + h(z)` with `h` analytic at `w` (DLMF §23.2(ii)). With Lean's totalization
the function `℘(z) - 1/(z - w)²` is itself analytic at `w`. -/
@[dlmf 23.2.ii]
theorem analyticAt_weierstrassP_sub (L : PeriodPair) {w : ℂ} (hw : w ∈ L.lattice) :
    AnalyticAt ℂ (fun z ↦ ℘[L] z - 1 / (z - w) ^ 2) w := by
  have heq : (fun z ↦ ℘[L] z - 1 / (z - w) ^ 2) = fun z ↦ ℘[L - w] z - 1 / w ^ 2 := by
    funext z
    rw [L.weierstrassPExcept_def ⟨w, hw⟩ z]
    ring
  rw [heq]
  exact (L.analyticAt_weierstrassPExcept w).sub analyticAt_const

/-- The complement of a period lattice is preconnected. -/
theorem wp23_isPreconnected_compl_lattice (L : PeriodPair) :
    IsPreconnected (L.latticeᶜ : Set ℂ) := by
  have hc : (L.lattice : Set ℂ).Countable := by
    have : Countable L.lattice := L.latticeEquivProd.toEquiv.injective.countable
    exact Set.countable_coe_iff.mp this
  exact (Set.Countable.isConnected_compl_of_one_lt_rank (by simp [rank_real_complex])
    hc).isPreconnected

/-- `ζ(z + w) - ζ(z)` is independent of `z ∉ 𝕃` for `w ∈ 𝕃`. -/
theorem wp23_zeta_add_sub_const (L : PeriodPair) {w : ℂ} (hw : w ∈ L.lattice) {z₁ z₂ : ℂ}
    (h₁ : z₁ ∉ L.lattice) (h₂ : z₂ ∉ L.lattice) :
    weierstrassZeta L (z₁ + w) - weierstrassZeta L z₁ =
      weierstrassZeta L (z₂ + w) - weierstrassZeta L z₂ := by
  have hU : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have hshift : ∀ z, z ∉ L.lattice → z + w ∉ L.lattice := fun z hz h =>
    hz (by simpa using sub_mem h hw)
  have hD : ∀ z ∈ (L.latticeᶜ : Set ℂ), HasDerivAt
      (fun z ↦ weierstrassZeta L (z + w) - weierstrassZeta L z) 0 z := by
    intro z hz
    have h1 := (hasDerivAt_weierstrassZeta L (hshift z hz)).comp_add_const z w
    have h2 := hasDerivAt_weierstrassZeta L hz
    convert h1.sub h2 using 1
    rw [L.weierstrassP_add_coe z ⟨w, hw⟩]; ring
  refine hU.is_const_of_deriv_eq_zero (wp23_isPreconnected_compl_lattice L)
    (fun z hz => (hD z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hD z hz).deriv) h₁ h₂

/-- `σ'(0) = 1`. -/
theorem p23R1_hasDerivAt_weierstrassSigma_zero (L : PeriodPair) :
    HasDerivAt (weierstrassSigma L) 1 0 := by
  have hU : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have hPd : DifferentiableOn ℂ (fun x => ∏' l : L.lattice, p23R1_sigmaFactor l x)
      (Metric.ball 0 1) :=
    (p23R1_hasProdLocallyUniformlyOn_sigma L).differentiableOn
      (.of_forall fun s => DifferentiableOn.fun_finsetProd fun l _ =>
        (by unfold p23R1_sigmaFactor; fun_prop : Differentiable ℂ (p23R1_sigmaFactor l))
          |>.differentiableOn) hU
  have hP0 : ∏' l : L.lattice, p23R1_sigmaFactor l 0 = 1 := by simp [p23R1_sigmaFactor]
  have h := (hasDerivAt_id (0 : ℂ)).mul
    (hPd.differentiableAt (hU.mem_nhds (by simp))).hasDerivAt
  have hσ : weierstrassSigma L = fun x => id x * ∏' l : L.lattice, p23R1_sigmaFactor l x := rfl
  rw [hσ]
  convert h using 1
  simp [hP0]

/-- `σ'(z) = ζ(z)σ(z)` off the lattice. -/
theorem p23R1_deriv_weierstrassSigma_eq (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    deriv (weierstrassSigma L) z = weierstrassZeta L z * weierstrassSigma L z := by
  have h := (weierstrassSigma_eq_zero_iff L).not.mpr hz
  rw [weierstrassZeta_eq_deriv_div L hz, div_mul_cancel₀ _ h]

/-- Quasi-periodicity of `σ` along any lattice vector, with an unspecified nonzero constant. -/
theorem p23R1_weierstrassSigma_add_mem (L : PeriodPair) {w : ℂ} (hw : w ∈ L.lattice) {z₀ : ℂ}
    (hz₀ : z₀ ∉ L.lattice) : ∃ a : ℂ, a ≠ 0 ∧ ∀ z, weierstrassSigma L (z + w) =
      a * cexp ((weierstrassZeta L (z₀ + w) - weierstrassZeta L z₀) * z) * weierstrassSigma L z := by
  set c := weierstrassZeta L (z₀ + w) - weierstrassZeta L z₀ with hc
  have hU : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have hshift : ∀ z, z ∉ L.lattice → z + w ∉ L.lattice := fun z hz h =>
    hz (by simpa using sub_mem h hw)
  have hσd := differentiable_weierstrassSigma L
  have hne : ∀ z, z ∉ L.lattice → weierstrassSigma L z ≠ 0 := fun z hz =>
    (weierstrassSigma_eq_zero_iff L).not.mpr hz
  set h : ℂ → ℂ := fun z => weierstrassSigma L (z + w) * cexp (-(c * z)) / weierstrassSigma L z
  have hD : ∀ z ∈ (L.latticeᶜ : Set ℂ), HasDerivAt h 0 z := by
    intro z hz
    have hzc : weierstrassZeta L (z + w) = weierstrassZeta L z + c := by
      have := wp23_zeta_add_sub_const L hw hz hz₀
      rw [hc]; linear_combination this
    have h1 : HasDerivAt (fun z => weierstrassSigma L (z + w))
        ((weierstrassZeta L z + c) * weierstrassSigma L (z + w)) z := by
      have := (hσd (z + w)).hasDerivAt.comp_add_const z w
      rwa [p23R1_deriv_weierstrassSigma_eq L (hshift z hz), hzc] at this
    have h2 : HasDerivAt (fun z => cexp (-(c * z))) (cexp (-(c * z)) * -c) z := by
      have := ((hasDerivAt_id z).const_mul c).neg.cexp
      simpa using this
    have h3 : HasDerivAt (weierstrassSigma L) (weierstrassZeta L z * weierstrassSigma L z) z := by
      have := (hσd z).hasDerivAt
      rwa [p23R1_deriv_weierstrassSigma_eq L hz] at this
    convert (h1.fun_mul h2).div h3 (hne z hz) using 1
    field_simp
    ring
  have hconst : ∀ z, z ∉ L.lattice → h z = h z₀ := fun z hz =>
    hU.is_const_of_deriv_eq_zero (wp23_isPreconnected_compl_lattice L)
      (fun y hy => (hD y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hD y hy).deriv) hz hz₀
  refine ⟨h z₀, ?_, fun z => ?_⟩
  · exact div_ne_zero (mul_ne_zero (hne _ (hshift z₀ hz₀)) (Complex.exp_ne_zero _))
      (hne z₀ hz₀)
  · by_cases hz : z ∈ L.lattice
    · rw [weierstrassSigma_eq_zero_of_mem L hz, weierstrassSigma_eq_zero_of_mem L (add_mem hz hw),
        mul_zero]
    · rw [← hconst z hz]
      simp only [h]
      have := hne z hz
      have he : cexp (-(z * c)) * cexp (z * c) = 1 := by rw [← Complex.exp_add]; simp
      field_simp
      linear_combination (-weierstrassSigma L (z + w)) * he

/-- The zeros of `σ` are simple (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem deriv_weierstrassSigma_ne_zero (L : PeriodPair) {z : ℂ} (hz : z ∈ L.lattice) :
    deriv (weierstrassSigma L) z ≠ 0 := by
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, z₀ ∉ L.lattice := ⟨_, L.ω₁_div_two_notMem_lattice⟩
  obtain ⟨a, ha, hfa⟩ := p23R1_weierstrassSigma_add_mem L hz hz₀
  set c := weierstrassZeta L (z₀ + z) - weierstrassZeta L z₀
  have h1 : HasDerivAt (fun y => weierstrassSigma L (y + z)) (deriv (weierstrassSigma L) z) 0 := by
    have := ((differentiable_weierstrassSigma L) (0 + z)).hasDerivAt.comp_add_const 0 z
    simpa using this
  have h2 : HasDerivAt (fun y => a * cexp (c * y) * weierstrassSigma L y) a 0 := by
    have he : HasDerivAt (fun y => cexp (c * y)) (cexp (c * 0) * c) 0 :=
      ((hasDerivAt_id (0 : ℂ)).const_mul c).cexp.congr_deriv (by simp)
    convert ((he.const_mul a).mul (p23R1_hasDerivAt_weierstrassSigma_zero L)) using 1
    simp [weierstrassSigma_eq_zero_of_mem L (zero_mem _)]
  rw [show (fun y => weierstrassSigma L (y + z)) = fun y => a * cexp (c * y) * weierstrassSigma L y
    from funext hfa] at h1
  rw [h1.unique h2]
  exact ha

/-! ### Liouville's theorem for elliptic functions and the values of `℘` at half-periods -/

section p23R1

open Filter Topology

/-- `℘ - c` has a pole of order exactly `2` at every lattice point. -/
theorem p23R1_order_weierstrassP_sub (L : PeriodPair) {x : ℂ} (hx : x ∈ L.lattice) (c : ℂ) :
    meromorphicOrderAt (fun z => ℘[L] z - c) x = -2 := by
  have hlt : meromorphicOrderAt ℘[L] x < meromorphicOrderAt (fun _ : ℂ => -c) x := by
    rw [L.order_weierstrassP x hx]
    exact lt_of_lt_of_le (by decide) (analyticAt_const.meromorphicOrderAt_nonneg)
  have h := meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const (-c) x) hlt
  rw [L.order_weierstrassP x hx] at h
  rw [← h]
  congr 1

/-- An analytic function with `g x = g'(x) = 0` has order at least `2` at `x`. -/
theorem p23R1_two_le_order {g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) (h0 : g x = 0)
    (h1 : deriv g x = 0) : (2 : WithTop ℤ) ≤ meromorphicOrderAt g x := by
  have h2 : ((2 : ℕ) : ℕ∞) ≤ analyticOrderAt g x := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg]
    intro i hi
    interval_cases i <;> simp [h0, h1]
  rw [hg.meromorphicOrderAt_eq]
  cases h : analyticOrderAt g x with
  | top => simp
  | coe n =>
    rw [h] at h2
    have : 2 ≤ n := by exact_mod_cast h2
    simp only [ENat.map_natCast]
    have e : ((2 : ℤ) : WithTop ℤ) ≤ ((n : ℤ) : WithTop ℤ) := WithTop.coe_le_coe.mpr (by omega)
    exact e

/-- `-2 + o ≥ 0` for an order `o ≥ 2`. -/
theorem p23R1_nonneg_add {o : WithTop ℤ} (h : 2 ≤ o) : 0 ≤ (-2 : WithTop ℤ) + o := by
  cases o with
  | top => simp
  | coe n =>
    have h' : ((2 : ℤ) : WithTop ℤ) ≤ (n : WithTop ℤ) := h
    have : (2 : ℤ) ≤ n := WithTop.coe_le_coe.mp h'
    have e : ((0 : ℤ) : WithTop ℤ) ≤ ((-2 + n : ℤ) : WithTop ℤ) := WithTop.coe_le_coe.mpr (by omega)
    exact e


/-- Liouville for elliptic functions: a lattice-periodic meromorphic function with nonnegative
order everywhere takes one constant value at every point where it is analytic. -/
theorem p23R1_eq_const_of_elliptic (L : PeriodPair) {f : ℂ → ℂ} (hf : Meromorphic f)
    (hper : ∀ z, ∀ l ∈ L.lattice, f (z + l) = f z)
    (hord : ∀ x, 0 ≤ meromorphicOrderAt f x) :
    ∃ c, ∀ x, AnalyticAt ℂ f x → f x = c := by
  have hfU : MeromorphicOn f Set.univ := hf.meromorphicOn
  set Q := toMeromorphicNFOn f Set.univ with hQ
  have hQan : ∀ x, AnalyticAt ℂ Q x := by
    intro x
    have hnf : MeromorphicNFAt Q x := meromorphicNFOn_toMeromorphicNFOn f Set.univ (Set.mem_univ x)
    refine hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
    rw [meromorphicOrderAt_congr (hfU.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ x))]
    exact hord x
  have hQd : Differentiable ℂ Q := fun x => (hQan x).differentiableAt
  have hQf : ∀ x, Q =ᶠ[𝓝[≠] x] f := fun x => hfU.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ x)
  have hper' : ∀ z w, w ∈ L.lattice → Q (z + w) = Q z := by
    intro z w hw
    have h1 : Tendsto (fun y => Q (y + w)) (𝓝[≠] z) (𝓝 (Q (z + w))) :=
      ((hQd.continuous.comp (continuous_id.add continuous_const : Continuous fun y : ℂ => y + w)).tendsto z).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto Q (𝓝[≠] z) (𝓝 (Q z)) :=
      (hQd.continuous.tendsto z).mono_left nhdsWithin_le_nhds
    have hmap : Tendsto (fun y => y + w) (𝓝[≠] z) (𝓝[≠] (z + w)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_id.add continuous_const : Continuous fun y : ℂ => y + w).tendsto z |>.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      simpa using hy
    have hev : (fun y => Q (y + w)) =ᶠ[𝓝[≠] z] Q := by
      filter_upwards [hmap.eventually (hQf (z + w)), hQf z] with y hy1 hy2
      rw [hy1, hy2, hper y w hw]
    exact tendsto_nhds_unique (h1.congr' hev) h2
  have hc := IsZLattice.isCompact_range_of_periodic L.lattice Q hQd.continuous hper'
  refine ⟨Q 0, fun x hx => ?_⟩
  have hQx : Q x = Q 0 := hQd.apply_eq_apply_of_bounded hc.isBounded x 0
  rw [← hQx]
  exact tendsto_nhds_unique ((hx.continuousAt.tendsto).mono_left nhdsWithin_le_nhds)
    (((hQd.continuous.tendsto x).mono_left nhdsWithin_le_nhds).congr' (hQf x))


/-- `℘'(a) = 0` for every half-lattice point `a` (`2a ∈ 𝕃`). -/
theorem p23R1_derivWeierstrassP_of_two_mul_mem (L : PeriodPair) {a : ℂ}
    (h2a : 2 * a ∈ L.lattice) : ℘'[L] a = 0 := by
  have h1 := L.derivWeierstrassP_sub_coe a ⟨_, h2a⟩
  have h2 := L.derivWeierstrassP_neg a
  rw [show a - ((⟨2 * a, h2a⟩ : L.lattice) : ℂ) = -a by simp; ring, h2] at h1
  exact CharZero.eq_neg_self_iff.mp h1.symm

/-- For a half-lattice point `a` the product `(℘(z + a) - ℘(a))(℘(z) - ℘(a))` is constant. -/
theorem p23R1_halfPeriod_product (L : PeriodPair) {a : ℂ} (ha : a ∉ L.lattice)
    (h2a : 2 * a ∈ L.lattice) :
    ∃ K, ∀ z, z ∉ L.lattice → z + a ∉ L.lattice →
      (℘[L] (z + a) - ℘[L] a) * (℘[L] z - ℘[L] a) = K := by
  have hP : AnalyticOnNhd ℂ ℘[L] L.latticeᶜ := L.analyticOnNhd_weierstrassP
  have hP'a := p23R1_derivWeierstrassP_of_two_mul_mem L h2a
  have hneg : ℘[L] (-a) = ℘[L] a := L.weierstrassP_neg a
  have hneg' : ℘'[L] (-a) = 0 := by rw [L.derivWeierstrassP_neg, hP'a, neg_zero]
  have hmer1 : Meromorphic (fun z => ℘[L] (z + a) - ℘[L] a) := fun x =>
    (meromorphicAt_fun_comp_add_const_iff_meromorphicAt.mpr (L.meromorphic_weierstrassP _)).sub
      (MeromorphicAt.const _ _)
  have hmer2 : Meromorphic (fun z => ℘[L] z - ℘[L] a) := fun x =>
    (L.meromorphic_weierstrassP x).sub (MeromorphicAt.const _ _)
  have hf : Meromorphic (fun z => (℘[L] (z + a) - ℘[L] a) * (℘[L] z - ℘[L] a)) :=
    fun x => (hmer1 x).mul (hmer2 x)
  have hper : ∀ z, ∀ l ∈ L.lattice, (fun z => (℘[L] (z + a) - ℘[L] a) * (℘[L] z - ℘[L] a))
      (z + l) = (fun z => (℘[L] (z + a) - ℘[L] a) * (℘[L] z - ℘[L] a)) z := by
    intro z l hl
    simp only
    rw [show z + l + a = (z + a) + l by ring, L.weierstrassP_add_coe (z + a) ⟨l, hl⟩,
      L.weierstrassP_add_coe z ⟨l, hl⟩]
  have hA1 : ∀ x, x + a ∉ L.lattice → AnalyticAt ℂ (fun z => ℘[L] (z + a) - ℘[L] a) x :=
    fun x hx => ((hP _ hx).comp_of_eq (analyticAt_id.add analyticAt_const) rfl).sub analyticAt_const
  have hA2 : ∀ x, x ∉ L.lattice → AnalyticAt ℂ (fun z => ℘[L] z - ℘[L] a) x :=
    fun x hx => (hP _ hx).sub analyticAt_const
  have hord : ∀ x, 0 ≤ meromorphicOrderAt
      (fun z => (℘[L] (z + a) - ℘[L] a) * (℘[L] z - ℘[L] a)) x := by
    intro x
    rw [show (fun z => (℘[L] (z + a) - ℘[L] a) * (℘[L] z - ℘[L] a)) =
        (fun z => ℘[L] (z + a) - ℘[L] a) * (fun z => ℘[L] z - ℘[L] a) from rfl,
      meromorphicOrderAt_mul (hmer1 x) (hmer2 x)]
    by_cases hx : x ∈ L.lattice
    · have hxa : x + a ∉ L.lattice := fun h => ha (by simpa using sub_mem h hx)
      rw [p23R1_order_weierstrassP_sub L hx, add_comm]
      refine p23R1_nonneg_add (p23R1_two_le_order (hA1 x hxa) ?_ ?_)
      · rw [add_comm, L.weierstrassP_add_coe a ⟨x, hx⟩, sub_self]
      · rw [deriv_sub_const, deriv_comp_add_const, deriv_weierstrassP, add_comm,
          L.derivWeierstrassP_add_coe a ⟨x, hx⟩, hP'a]
    · by_cases hxa : x + a ∈ L.lattice
      · have h1 := meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt
          (f := fun w => ℘[L] w - ℘[L] a) (c := a) (x := x)
        rw [h1, p23R1_order_weierstrassP_sub L hxa]
        have hx' : x = -a + ((⟨x + a, hxa⟩ : L.lattice) : ℂ) := by simp
        refine p23R1_nonneg_add (p23R1_two_le_order (hA2 x hx) ?_ ?_)
        · rw [hx', L.weierstrassP_add_coe, hneg, sub_self]
        · rw [deriv_sub_const, deriv_weierstrassP, hx', L.derivWeierstrassP_add_coe, hneg']
      · exact add_nonneg (hA1 x hxa).meromorphicOrderAt_nonneg
          (hA2 x hx).meromorphicOrderAt_nonneg
  obtain ⟨c, hc⟩ := p23R1_eq_const_of_elliptic L hf hper hord
  exact ⟨c, fun z hz hza => hc z ((hA1 z hza).mul (hA2 z hz))⟩

/-- `℘` is not locally constant at any point off the lattice. -/
theorem p23R1_weierstrassP_not_eventually_const (L : PeriodPair) {z₀ : ℂ}
    (hz₀ : z₀ ∉ L.lattice) (c : ℂ) : ¬ ∀ᶠ z in 𝓝 z₀, ℘[L] z = c := by
  intro h
  have hA : AnalyticOnNhd ℂ (fun z => ℘[L] z - c) L.latticeᶜ :=
    fun x hx => (L.analyticOnNhd_weierstrassP x hx).sub analyticAt_const
  have h0 : (fun z => ℘[L] z - c) =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [h] with z hz
    simp [hz]
  have hc : ∀ w ∈ (L.latticeᶜ : Set ℂ), ℘[L] w = c := fun w hw =>
    sub_eq_zero.mp (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (wp23_isPreconnected_compl_lattice L) hz₀ h0 hw)
  have hev : ℘[L] =ᶠ[𝓝[≠] 0] fun _ ↦ c := by
    filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
      self_mem_nhdsWithin] with w hw hw0
    exact hc w fun hl => hw ⟨hl, hw0⟩
  have h1 := L.order_weierstrassP 0 (zero_mem _)
  rw [meromorphicOrderAt_congr hev] at h1
  classical
  rw [meromorphicOrderAt_const] at h1
  split_ifs at h1 <;> revert h1 <;> decide

/-- `℘(b) ≠ ℘(a)` for a half-lattice point `a` unless `b ≡ ±a` modulo the lattice. -/
theorem p23R1_weierstrassP_ne_of_halfLattice (L : PeriodPair) {a b : ℂ} (ha : a ∉ L.lattice)
    (h2a : 2 * a ∈ L.lattice) (hb : b ∉ L.lattice) (hab : b + a ∉ L.lattice) :
    ℘[L] b ≠ ℘[L] a := by
  intro heq
  obtain ⟨K, hK⟩ := p23R1_halfPeriod_product L ha h2a
  have hK0 : K = 0 := by rw [← hK b hb hab, heq, sub_self, mul_zero]
  have hP : AnalyticOnNhd ℂ ℘[L] L.latticeᶜ := L.analyticOnNhd_weierstrassP
  have hopen : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have hA1 : AnalyticAt ℂ (fun z => ℘[L] (z + a) - ℘[L] a) b :=
    ((hP _ hab).comp_of_eq (analyticAt_id.add analyticAt_const) rfl).sub analyticAt_const
  have hA2 : AnalyticAt ℂ (fun z => ℘[L] z - ℘[L] a) b := (hP _ hb).sub analyticAt_const
  have hcont : Continuous fun z : ℂ => z + a := continuous_id.add continuous_const
  have hV : ∀ᶠ z in 𝓝 b, (℘[L] (z + a) - ℘[L] a) * (℘[L] z - ℘[L] a) = 0 := by
    have h1 : ∀ᶠ z in 𝓝 b, z + a ∉ L.lattice :=
      (hcont.tendsto b).eventually (hopen.mem_nhds hab)
    filter_upwards [hopen.mem_nhds hb, h1] with z hz hza
    rw [hK z hz hza, hK0]
  rcases hA2.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact p23R1_weierstrassP_not_eventually_const L hb (℘[L] a)
      (h.mono fun z hz => sub_eq_zero.mp hz)
  · have hfr : ∃ᶠ z in 𝓝[≠] b, ℘[L] (z + a) - ℘[L] a = 0 := by
      refine Filter.Eventually.frequently ?_
      filter_upwards [h, nhdsWithin_le_nhds hV] with z hz1 hz2
      exact (mul_eq_zero.mp hz2).resolve_right hz1
    have hev := hA1.frequently_zero_iff_eventually_zero.mp hfr
    have hsub : Filter.Tendsto (fun w : ℂ => w - a) (𝓝 (b + a)) (𝓝 b) := by
      have hc : Continuous fun w : ℂ => w - a := by fun_prop
      have := hc.tendsto (b + a)
      simpa only [add_sub_cancel_right] using this
    refine p23R1_weierstrassP_not_eventually_const L hab (℘[L] a) ?_
    filter_upwards [hsub.eventually hev] with w hw
    simpa using sub_eq_zero.mp hw

end p23R1

/-! ### Half-period values, `e_j` and `η_j` -/

namespace HalfPeriods

variable (H : HalfPeriods)

/-- The half-periods indexed as in DLMF: `ω_j` for `j = 1, 2, 3` (junk `0` otherwise). -/
def halfPeriod : ℕ → ℂ
  | 1 => H.ω₁
  | 2 => H.ω₂
  | 3 => H.ω₃
  | _ => 0

@[simp] theorem halfPeriod_one : H.halfPeriod 1 = H.ω₁ := rfl
@[simp] theorem halfPeriod_two : H.halfPeriod 2 = H.ω₂ := rfl
@[simp] theorem halfPeriod_three : H.halfPeriod 3 = H.ω₃ := rfl

/-- `℘(z|𝕃)` for DLMF lattice data. -/
abbrev weierstrassP (z : ℂ) : ℂ := ℘[H.periodPair] z
/-- `℘'(z|𝕃)` for DLMF lattice data. -/
abbrev derivWeierstrassP (z : ℂ) : ℂ := ℘'[H.periodPair] z
/-- `ζ(z|𝕃)` for DLMF lattice data. -/
abbrev weierstrassZeta (z : ℂ) : ℂ := DLMF.Weierstrass.weierstrassZeta H.periodPair z
/-- `σ(z|𝕃)` for DLMF lattice data. -/
abbrev weierstrassSigma (z : ℂ) : ℂ := DLMF.Weierstrass.weierstrassSigma H.periodPair z
/-- The invariant `g₂` (DLMF 23.3.1), Mathlib's `PeriodPair.g₂`. -/
abbrev g₂ : ℂ := H.periodPair.g₂
/-- The invariant `g₃` (DLMF 23.3.2), Mathlib's `PeriodPair.g₃`. -/
abbrev g₃ : ℂ := H.periodPair.g₃

/-- The lattice roots `e_j = ℘(ω_j)` (DLMF 23.3.9), `j = 1, 2, 3`. -/
@[dlmf 23.3.E9]
def e (j : ℕ) : ℂ := H.weierstrassP (H.halfPeriod j)

/-- The constants `η_j = ζ(ω_j)` (DLMF 23.2.12), `j = 1, 2, 3`. -/
@[dlmf 23.2.E12]
def eta (j : ℕ) : ℂ := H.weierstrassZeta (H.halfPeriod j)

theorem two_mul_halfPeriod_mem {j : ℕ} (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    2 * H.halfPeriod j ∈ H.lattice := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  exacts [H.two_mul_ω₁_mem, H.two_mul_ω₂_mem, H.two_mul_ω₃_mem]

theorem halfPeriod_notMem {j : ℕ} (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    H.halfPeriod j ∉ H.lattice := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  · simpa using H.periodPair.ω₁_div_two_notMem_lattice
  · intro h
    have h' : ((-1 / 2 : ℚ) : ℂ) * H.periodPair.ω₁ + ((-1 / 2 : ℚ) : ℂ) * H.periodPair.ω₂ ∈
        H.periodPair.lattice := by
      convert h using 1; simp [ω₂]; ring
    have := (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice).mp h'
    norm_num at this
  · simpa using H.periodPair.ω₂_div_two_notMem_lattice

/-- DLMF 23.2.9: `℘(z + 2ω_j) = ℘(z)`, `j = 1, 2, 3`. -/
@[dlmf 23.2.E9]
theorem weierstrassP_add_two_mul_halfPeriod (z : ℂ) {j : ℕ}
    (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    H.weierstrassP (z + 2 * H.halfPeriod j) = H.weierstrassP z :=
  H.periodPair.weierstrassP_add_coe z ⟨_, H.two_mul_halfPeriod_mem hj⟩

/-- DLMF 23.2.10: `℘'(ω_j) = 0`, `j = 1, 2, 3`. -/
@[dlmf 23.2.E10]
theorem derivWeierstrassP_halfPeriod {j : ℕ} (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    H.derivWeierstrassP (H.halfPeriod j) = 0 := by
  have h1 := H.periodPair.derivWeierstrassP_add_coe (-H.halfPeriod j)
    ⟨_, H.two_mul_halfPeriod_mem hj⟩
  have h2 := H.periodPair.derivWeierstrassP_neg (H.halfPeriod j)
  simp only at h1
  rw [show -H.halfPeriod j + 2 * H.halfPeriod j = H.halfPeriod j by ring, h2] at h1
  exact CharZero.eq_neg_self_iff.mp h1

/-- DLMF 23.2.11: `ζ` is quasi-periodic, `ζ(z + 2ω_j) = ζ(z) + 2η_j`, `j = 1, 2, 3`, for
`z ∉ 𝕃`. -/
@[dlmf 23.2.E11]
theorem weierstrassZeta_add_two_mul_halfPeriod {z : ℂ} (hz : z ∉ H.lattice) {j : ℕ}
    (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    H.weierstrassZeta (z + 2 * H.halfPeriod j) = H.weierstrassZeta z + 2 * H.eta j := by
  have hn := H.halfPeriod_notMem hj
  have hn' : -H.halfPeriod j ∉ H.lattice := fun h => hn (by simpa using neg_mem h)
  have := wp23_zeta_add_sub_const H.periodPair (H.two_mul_halfPeriod_mem hj) hz hn'
  rw [show -H.halfPeriod j + 2 * H.halfPeriod j = H.halfPeriod j by ring,
    DLMF.Weierstrass.weierstrassZeta_neg] at this
  simp only [HalfPeriods.weierstrassZeta, eta]
  linear_combination this

/-- DLMF 23.2.13: `η₁ + η₂ + η₃ = 0` (derived from the quasi-periodicity 23.2.11 and the
oddness of `ζ`). -/
@[dlmf 23.2.E13]
theorem eta_one_add_eta_two_add_eta_three : H.eta 1 + H.eta 2 + H.eta 3 = 0 := by
  have hn : H.ω₃ - H.ω₁ ∉ H.lattice := by
    intro h
    have h' : ((-1 / 2 : ℚ) : ℂ) * H.periodPair.ω₁ + ((1 / 2 : ℚ) : ℂ) * H.periodPair.ω₂ ∈
        H.periodPair.lattice := by
      convert h using 1; simp; ring
    have := (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice).mp h'
    norm_num at this
  have hn' : H.ω₁ - H.ω₃ ∉ H.lattice := by
    rw [show H.ω₁ - H.ω₃ = -(H.ω₃ - H.ω₁) by ring]
    exact fun h => hn (by simpa using neg_mem h)
  have h1 := H.weierstrassZeta_add_two_mul_halfPeriod hn (j := 1) (by simp)
  have h3 := H.weierstrassZeta_add_two_mul_halfPeriod hn' (j := 3) (by simp)
  simp only [halfPeriod_one, halfPeriod_three, HalfPeriods.weierstrassZeta] at h1 h3
  rw [show H.ω₃ - H.ω₁ + 2 * H.ω₁ = H.ω₁ + H.ω₃ by ring] at h1
  rw [show H.ω₁ - H.ω₃ + 2 * H.ω₃ = H.ω₁ + H.ω₃ by ring,
    show H.ω₁ - H.ω₃ = -(H.ω₃ - H.ω₁) by ring,
    DLMF.Weierstrass.weierstrassZeta_neg] at h3
  have h2 : H.eta 2 = -H.weierstrassZeta (H.ω₁ + H.ω₃) := by
    rw [eta, halfPeriod_two, ω₂, show -H.ω₁ - H.ω₃ = -(H.ω₁ + H.ω₃) by ring]
    simp only [HalfPeriods.weierstrassZeta, DLMF.Weierstrass.weierstrassZeta_neg]
  rw [h2]
  simp only [HalfPeriods.weierstrassZeta] at h1 h3 ⊢
  linear_combination (-(1 : ℂ) / 2) * (h1 + h3)

/-- DLMF 23.2.15: `σ(z + 2ω_j) = -e^{2η_j(z + ω_j)} σ(z)`, `j = 1, 2, 3`, for all `z ∈ ℂ`. -/
@[dlmf 23.2.E15]
theorem weierstrassSigma_add_two_mul_halfPeriod (z : ℂ) {j : ℕ}
    (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    H.weierstrassSigma (z + 2 * H.halfPeriod j) =
      -cexp (2 * H.eta j * (z + H.halfPeriod j)) * H.weierstrassSigma z := by
  set ω := H.halfPeriod j
  have hω : ω ∉ H.lattice := H.halfPeriod_notMem hj
  have hmω : -ω ∉ H.lattice := fun h => hω (by simpa using neg_mem h)
  obtain ⟨a, ha, hfa⟩ := p23R1_weierstrassSigma_add_mem H.periodPair
    (H.two_mul_halfPeriod_mem hj) hmω
  have hc : DLMF.Weierstrass.weierstrassZeta H.periodPair (-ω + 2 * ω) - DLMF.Weierstrass.weierstrassZeta H.periodPair (-ω) =
      2 * H.eta j := by
    rw [show -ω + 2 * ω = ω by ring, DLMF.Weierstrass.weierstrassZeta_neg]
    simp only [eta, HalfPeriods.weierstrassZeta, ω]; ring
  rw [hc] at hfa
  have hσω : DLMF.Weierstrass.weierstrassSigma H.periodPair ω ≠ 0 :=
    (DLMF.Weierstrass.weierstrassSigma_eq_zero_iff _).not.mpr hω
  have h1 := hfa (-ω)
  rw [show -ω + 2 * ω = ω by ring, DLMF.Weierstrass.weierstrassSigma_neg] at h1
  have ha' : a = -cexp (2 * H.eta j * ω) := by
    have he : cexp (2 * H.eta j * -ω) * cexp (2 * H.eta j * ω) = 1 := by
      rw [← Complex.exp_add]; simp
    have : (a + cexp (2 * H.eta j * ω)) * DLMF.Weierstrass.weierstrassSigma H.periodPair ω = 0 := by
      linear_combination (cexp (2 * H.eta j * ω)) * h1 - a * DLMF.Weierstrass.weierstrassSigma H.periodPair ω * he
    have := (mul_eq_zero.mp this).resolve_right hσω
    linear_combination this
  simp only [HalfPeriods.weierstrassSigma]
  rw [hfa z, ha', mul_add, Complex.exp_add]
  ring

/-- DLMF 23.2.16: `σ'(2ω_j) = -e^{2η_jω_j}`, `j = 1, 2, 3`. -/
@[dlmf 23.2.E16]
theorem deriv_weierstrassSigma_two_mul_halfPeriod {j : ℕ} (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    deriv H.weierstrassSigma (2 * H.halfPeriod j) = -cexp (2 * H.eta j * H.halfPeriod j) := by
  set ω := H.halfPeriod j
  have hfun : (fun y => H.weierstrassSigma (y + 2 * ω)) =
      fun y => -cexp (2 * H.eta j * (y + ω)) * H.weierstrassSigma y :=
    funext fun y => H.weierstrassSigma_add_two_mul_halfPeriod y hj
  have h1 : HasDerivAt (fun y => H.weierstrassSigma (y + 2 * ω))
      (deriv H.weierstrassSigma (2 * ω)) 0 := by
    have := ((DLMF.Weierstrass.differentiable_weierstrassSigma H.periodPair)
      (0 + 2 * ω)).hasDerivAt.comp_add_const 0 (2 * ω)
    simpa using this
  have he : HasDerivAt (fun y => cexp (2 * H.eta j * (y + ω)))
      (cexp (2 * H.eta j * (0 + ω)) * (2 * H.eta j)) 0 := by
    have := (((hasDerivAt_id (0 : ℂ)).add_const ω).const_mul (2 * H.eta j)).cexp
    simpa using this
  have h2 := he.neg.mul (p23R1_hasDerivAt_weierstrassSigma_zero H.periodPair)
  rw [hfun] at h1
  rw [h1.unique h2]
  simp [DLMF.Weierstrass.weierstrassSigma_eq_zero_of_mem H.periodPair (zero_mem _)]

/-! ### Invariants, roots and discriminant (§23.3(i)) -/

/-- Each half-period lies off the lattice; equivalently `e_j` is a finite value of `℘`. -/
theorem e_root_cubic {j : ℕ} (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    4 * H.e j ^ 3 - H.g₂ * H.e j - H.g₃ = 0 := by
  have h := H.periodPair.derivWeierstrassP_sq (H.halfPeriod j) (H.halfPeriod_notMem hj)
  have h0 := H.derivWeierstrassP_halfPeriod hj
  simp only [HalfPeriods.derivWeierstrassP] at h0
  rw [h0] at h
  simp only [e, HalfPeriods.weierstrassP]
  linear_combination -h

/-- DLMF 23.3.3: the lattice roots `e₁, e₂, e₃` satisfy `4z³ - g₂z - g₃ = 0`. -/
@[dlmf 23.3.E3]
theorem e_isRoot (j : ℕ) (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    4 * H.e j ^ 3 - H.g₂ * H.e j - H.g₃ = 0 :=
  H.e_root_cubic hj

/-- `e_k ≠ e_j` whenever `ω_k + ω_j ∉ 𝕃`. -/
theorem p23R1_e_ne {j k : ℕ} (hj : j ∈ ({1, 2, 3} : Finset ℕ)) (hk : k ∈ ({1, 2, 3} : Finset ℕ))
    (hjk : H.halfPeriod k + H.halfPeriod j ∉ H.lattice) : H.e k ≠ H.e j :=
  p23R1_weierstrassP_ne_of_halfLattice H.periodPair (H.halfPeriod_notMem hj)
    (H.two_mul_halfPeriod_mem hj) (H.halfPeriod_notMem hk) hjk

/-- DLMF §23.3(i): the lattice roots `e₁, e₂, e₃` are distinct. -/
@[dlmf 23.3.i]
theorem e_distinct : H.e 1 ≠ H.e 2 ∧ H.e 2 ≠ H.e 3 ∧ H.e 1 ≠ H.e 3 := by
  have hneg : ∀ j ∈ ({1, 2, 3} : Finset ℕ), -H.halfPeriod j ∉ H.lattice := fun j hj h =>
    H.halfPeriod_notMem hj (by simpa using neg_mem h)
  refine ⟨H.p23R1_e_ne (j := 2) (k := 1) (by simp) (by simp) ?_,
    H.p23R1_e_ne (j := 3) (k := 2) (by simp) (by simp) ?_,
    H.p23R1_e_ne (j := 3) (k := 1) (by simp) (by simp) ?_⟩
  · rw [show H.halfPeriod 1 + H.halfPeriod 2 = -H.halfPeriod 3 by simp [ω₂]; ring]
    exact hneg 3 (by simp)
  · rw [show H.halfPeriod 2 + H.halfPeriod 3 = -H.halfPeriod 1 by simp [ω₂]]
    exact hneg 1 (by simp)
  · rw [show H.halfPeriod 1 + H.halfPeriod 3 = -H.halfPeriod 2 by simp [ω₂]; ring]
    exact hneg 2 (by simp)

/-- DLMF 23.3.5: `e₁ + e₂ + e₃ = 0`. -/
@[dlmf 23.3.E5]
theorem e_sum : H.e 1 + H.e 2 + H.e 3 = 0 := by
  obtain ⟨h12, h23, h13⟩ := H.e_distinct
  have r1 := H.e_root_cubic (j := 1) (by simp)
  have r2 := H.e_root_cubic (j := 2) (by simp)
  have r3 := H.e_root_cubic (j := 3) (by simp)
  -- `4(e₁² + e₁e₂ + e₂²) = g₂` and likewise for `(1, 3)`.
  have a12 : 4 * (H.e 1 ^ 2 + H.e 1 * H.e 2 + H.e 2 ^ 2) = H.g₂ := by
    have : (H.e 1 - H.e 2) * (4 * (H.e 1 ^ 2 + H.e 1 * H.e 2 + H.e 2 ^ 2) - H.g₂) = 0 := by
      linear_combination r1 - r2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) h12
    · linear_combination h
  have a13 : 4 * (H.e 1 ^ 2 + H.e 1 * H.e 3 + H.e 3 ^ 2) = H.g₂ := by
    have : (H.e 1 - H.e 3) * (4 * (H.e 1 ^ 2 + H.e 1 * H.e 3 + H.e 3 ^ 2) - H.g₂) = 0 := by
      linear_combination r1 - r3
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) h13
    · linear_combination h
  have : (H.e 2 - H.e 3) * (4 * (H.e 1 + H.e 2 + H.e 3)) = 0 := by
    linear_combination a12 - a13
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) h23
  · linear_combination h / 4

/-- `4(e₁² + e₁e₂ + e₂²) = g₂`. -/
theorem wp23_g₂_eq : 4 * (H.e 1 ^ 2 + H.e 1 * H.e 2 + H.e 2 ^ 2) = H.g₂ := by
  obtain ⟨h12, -, -⟩ := H.e_distinct
  have r1 := H.e_root_cubic (j := 1) (by simp)
  have r2 := H.e_root_cubic (j := 2) (by simp)
  have : (H.e 1 - H.e 2) * (4 * (H.e 1 ^ 2 + H.e 1 * H.e 2 + H.e 2 ^ 2) - H.g₂) = 0 := by
    linear_combination r1 - r2
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) h12
  · linear_combination h

/-- DLMF 23.3.6: `g₂ = 2(e₁² + e₂² + e₃²) = -4(e₂e₃ + e₃e₁ + e₁e₂)`. -/
@[dlmf 23.3.E6]
theorem g₂_eq_e : H.g₂ = 2 * (H.e 1 ^ 2 + H.e 2 ^ 2 + H.e 3 ^ 2) ∧
    H.g₂ = -4 * (H.e 2 * H.e 3 + H.e 3 * H.e 1 + H.e 1 * H.e 2) := by
  have hs := H.e_sum
  have hg := H.wp23_g₂_eq
  have h3 : H.e 3 = -H.e 1 - H.e 2 := by linear_combination hs
  rw [h3] at ⊢
  constructor <;> linear_combination -hg

/-- DLMF 23.3.7: `g₃ = 4e₁e₂e₃ = (4/3)(e₁³ + e₂³ + e₃³)`. -/
@[dlmf 23.3.E7]
theorem g₃_eq_e : H.g₃ = 4 * H.e 1 * H.e 2 * H.e 3 ∧
    H.g₃ = 4 / 3 * (H.e 1 ^ 3 + H.e 2 ^ 3 + H.e 3 ^ 3) := by
  have hs := H.e_sum
  have hg := H.wp23_g₂_eq
  have r1 := H.e_root_cubic (j := 1) (by simp)
  have h3 : H.e 3 = -H.e 1 - H.e 2 := by linear_combination hs
  rw [h3]
  constructor
  · linear_combination -r1 + H.e 1 * hg
  · linear_combination -r1 + H.e 1 * hg

/-- DLMF §23.3(i): `4x³ - g₂x - g₃ = 4(x - e₁)(x - e₂)(x - e₃)`. -/
@[dlmf 23.3.i]
theorem cubic_eq_mul (x : ℂ) :
    4 * x ^ 3 - H.g₂ * x - H.g₃ = 4 * (x - H.e 1) * (x - H.e 2) * (x - H.e 3) := by
  have hs := H.e_sum
  have h2 := (H.g₂_eq_e).2
  have h3 := (H.g₃_eq_e).1
  rw [h2, h3]
  linear_combination (4 * x ^ 2) * hs

end HalfPeriods

/-- The discriminant `Δ = g₂³ - 27g₃²` of a lattice (DLMF 23.3.4). -/
@[dlmf 23.3.E4]
def latticeDiscriminant (L : PeriodPair) : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

namespace HalfPeriods

variable (H : HalfPeriods)

/-- DLMF 23.3.4: `Δ = g₂³ - 27g₃² = 16(e₂ - e₃)²(e₃ - e₁)²(e₁ - e₂)²`. -/
@[dlmf 23.3.E4]
theorem latticeDiscriminant_eq :
    latticeDiscriminant H.periodPair =
      16 * (H.e 2 - H.e 3) ^ 2 * (H.e 3 - H.e 1) ^ 2 * (H.e 1 - H.e 2) ^ 2 := by
  have hs := H.e_sum
  have h2 := (H.g₂_eq_e).2
  have h3 := (H.g₃_eq_e).1
  have h3' : H.e 3 = -H.e 1 - H.e 2 := by linear_combination hs
  simp only [latticeDiscriminant]
  change H.g₂ ^ 3 - 27 * H.g₃ ^ 2 = _
  rw [h2, h3, h3']
  ring

/-- DLMF §23.3(i): the discriminant of a lattice is nonzero. -/
@[dlmf 23.3.i]
theorem latticeDiscriminant_ne_zero : latticeDiscriminant H.periodPair ≠ 0 := by
  rw [H.latticeDiscriminant_eq]
  obtain ⟨h12, h23, h13⟩ := H.e_distinct
  have a : H.e 3 - H.e 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h13)
  have b := sub_ne_zero.mpr h12
  have c := sub_ne_zero.mpr h23
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 c)) (pow_ne_zero 2 a))
    (pow_ne_zero 2 b)

/-- DLMF §23.3(i): `g₂`, `g₃` and the set `{e₁, e₂, e₃}` depend only on the lattice, not on
the choice of generators. -/
@[dlmf 23.3.i]
theorem invariants_roots_eq_of_lattice_eq (H' : HalfPeriods) (h : H.lattice = H'.lattice) :
    H.g₂ = H'.g₂ ∧ H.g₃ = H'.g₃ ∧
      ({H.e 1, H.e 2, H.e 3} : Set ℂ) = {H'.e 1, H'.e 2, H'.e 3} := by
  have hG : ∀ n, H.periodPair.G n = H'.periodPair.G n := by
    intro n
    simp only [PeriodPair.G]
    rw [← (Equiv.subtypeEquivRight (fun x => by rw [show H.periodPair.lattice = H'.periodPair.lattice
      from h]) : H.periodPair.lattice ≃ H'.periodPair.lattice).tsum_eq]
    rfl
  have h2 : H.g₂ = H'.g₂ := by simp only [HalfPeriods.g₂, PeriodPair.g₂, hG]
  have h3 : H.g₃ = H'.g₃ := by simp only [HalfPeriods.g₃, PeriodPair.g₃, hG]
  have hroots : ∀ (K : HalfPeriods) (x : ℂ),
      x ∈ ({K.e 1, K.e 2, K.e 3} : Set ℂ) ↔ 4 * x ^ 3 - K.g₂ * x - K.g₃ = 0 := by
    intro K x
    rw [K.cubic_eq_mul]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, mul_eq_zero, sub_eq_zero]
    norm_num [or_assoc]
  refine ⟨h2, h3, Set.ext fun x => ?_⟩
  rw [hroots H, hroots H', h2, h3]

end HalfPeriods

/-! ### The invariants form `℘(z; g₂, g₃)` (DLMF 23.3.8) -/

theorem wp23_G_eq_of_lattice_eq (L L' : PeriodPair) (h : L.lattice = L'.lattice) (n : ℕ) :
    L.G n = L'.G n := by
  simp only [PeriodPair.G]
  rw [← (Equiv.subtypeEquivRight (fun x => by rw [h]) : L.lattice ≃ L'.lattice).tsum_eq]
  rfl

theorem wp23_ω₁_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  simpa using L.indep.ne_zero 0

theorem wp23_im_div_ne_zero (L : PeriodPair) : (L.ω₂ / L.ω₁).im ≠ 0 := by
  intro him
  have h1 := wp23_ω₁_ne_zero L
  have hq : L.ω₂ / L.ω₁ = ((L.ω₂ / L.ω₁).re : ℂ) := Complex.ext (by simp) (by simp [him])
  have h2 : L.ω₂ = ((L.ω₂ / L.ω₁).re : ℂ) * L.ω₁ := by
    rw [← hq]; field_simp
  have := LinearIndependent.pair_iff.mp L.indep ((L.ω₂ / L.ω₁).re) (-1)
    (by rw [Complex.real_smul, Complex.real_smul, ← h2]; simp)
  norm_num at this

/-- DLMF half-periods for an arbitrary Mathlib period pair: `ω₁ = L.ω₁/2` and
`ω₃ = ±L.ω₂/2`, the sign chosen so that `ℑ(ω₃/ω₁) > 0`. -/
def halfPeriodsOf (L : PeriodPair) : HalfPeriods :=
  if h : 0 < (L.ω₂ / L.ω₁).im then
    ⟨L.ω₁ / 2, L.ω₂ / 2, by simpa using wp23_ω₁_ne_zero L, by
      rwa [div_div_div_cancel_right₀ two_ne_zero]⟩
  else
    ⟨L.ω₁ / 2, -L.ω₂ / 2, by simpa using wp23_ω₁_ne_zero L, by
      rw [div_div_div_cancel_right₀ two_ne_zero, neg_div, neg_im]
      have := wp23_im_div_ne_zero L
      exact neg_pos.mpr (lt_of_le_of_ne (not_lt.mp h) this)⟩

theorem halfPeriodsOf_lattice (L : PeriodPair) : (halfPeriodsOf L).lattice = L.lattice := by
  unfold halfPeriodsOf
  split_ifs with h
  · simp only [HalfPeriods.lattice, PeriodPair.lattice, HalfPeriods.periodPair_ω₁,
      HalfPeriods.periodPair_ω₂]
    rw [show 2 * (L.ω₁ / 2) = L.ω₁ by ring, show 2 * (L.ω₂ / 2) = L.ω₂ by ring]
  · simp only [HalfPeriods.lattice, PeriodPair.lattice, HalfPeriods.periodPair_ω₁,
      HalfPeriods.periodPair_ω₂]
    rw [show 2 * (L.ω₁ / 2) = L.ω₁ by ring, show 2 * (-L.ω₂ / 2) = -L.ω₂ by ring]
    apply le_antisymm <;> refine Submodule.span_le.mpr ?_ <;> rintro x (rfl | rfl)
    · exact Submodule.subset_span (by simp)
    · exact neg_mem (Submodule.subset_span (by simp))
    · exact Submodule.subset_span (by simp)
    · simpa using neg_mem (Submodule.subset_span (R := ℤ) (s := {L.ω₁, -L.ω₂})
        (show -L.ω₂ ∈ ({L.ω₁, -L.ω₂} : Set ℂ) by simp))

/-- DLMF §23.3(i): the discriminant of every lattice is nonzero. -/
@[dlmf 23.3.i]
theorem latticeDiscriminant_ne_zero' (L : PeriodPair) : latticeDiscriminant L ≠ 0 := by
  have h := (halfPeriodsOf L).latticeDiscriminant_ne_zero
  have hl := halfPeriodsOf_lattice L
  simpa [latticeDiscriminant, PeriodPair.g₂, PeriodPair.g₃,
    wp23_G_eq_of_lattice_eq _ _ hl] using h

/-- DLMF §23.3(i): if `g₂³ ≠ 27g₃²` there is a lattice with invariants `g₂, g₃`. -/
@[dlmf 23.3.i]
theorem exists_periodPair_invariants (g₂ g₃ : ℂ) (h : g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0) :
    ∃ L : PeriodPair, L.g₂ = g₂ ∧ L.g₃ = g₃ := by
  sorry

section p23R1Uniq

open Filter Topology

/-- The differential equation of `℘` in terms of the regular part `p = ℘ - 1/z²` near `0`:
`(z³p' - 2)² = 4(1 + z²p)³ - g₂z⁴(1 + z²p) - g₃z⁶`. -/
theorem p23R1_ode_regularPart (L : PeriodPair) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), (z ^ 3 * deriv (fun w => ℘[L] w - 1 / w ^ 2) z - 2) ^ 2 =
      4 * (1 + z ^ 2 * (℘[L] z - 1 / z ^ 2)) ^ 3 -
        L.g₂ * z ^ 4 * (1 + z ^ 2 * (℘[L] z - 1 / z ^ 2)) - L.g₃ * z ^ 6 := by
  filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
    self_mem_nhdsWithin] with z hz hz0
  have hz0' : z ≠ 0 := hz0
  have hzL : z ∉ L.lattice := fun h => hz ⟨h, hz0⟩
  have hU : IsOpen (L.latticeᶜ : Set ℂ) := L.isClosed_lattice.isOpen_compl
  have h1 : HasDerivAt ℘[L] (℘'[L] z) z := by
    have := (L.differentiableOn_weierstrassP z hzL).differentiableAt (hU.mem_nhds hzL)
    simpa using this.hasDerivAt
  have h2 : HasDerivAt (fun w : ℂ => 1 / w ^ 2) (-(2 * z) / (z ^ 2) ^ 2) z := by
    have := (hasDerivAt_pow 2 z).inv (pow_ne_zero 2 hz0')
    convert this using 1
    · funext w; simp [one_div]
    · simp
  have hd : deriv (fun w => ℘[L] w - 1 / w ^ 2) z = ℘'[L] z + 2 / z ^ 3 := by
    rw [(h1.fun_sub h2).deriv]
    field_simp
    ring
  have ode := L.derivWeierstrassP_sq z hzL
  rw [hd]
  have e1 : z ^ 3 * (℘'[L] z + 2 / z ^ 3) - 2 = z ^ 3 * ℘'[L] z := by field_simp; ring
  have e2 : 1 + z ^ 2 * (℘[L] z - 1 / z ^ 2) = z ^ 2 * ℘[L] z := by field_simp; ring
  rw [e1, e2]
  linear_combination z ^ 6 * ode

/-- Two lattices with the same invariants have the same `℘` near `0`. -/
theorem p23R1_weierstrassP_eventuallyEq_of_invariants (L L' : PeriodPair) (h₂ : L.g₂ = L'.g₂)
    (h₃ : L.g₃ = L'.g₃) :
    ∀ᶠ z in 𝓝 (0 : ℂ), ℘[L] z - 1 / z ^ 2 - (℘[L'] z - 1 / z ^ 2) = 0 := by
  set p : ℂ → ℂ := fun w => ℘[L] w - 1 / w ^ 2 with hp
  set q : ℂ → ℂ := fun w => ℘[L'] w - 1 / w ^ 2 with hq
  have hpa : AnalyticAt ℂ p 0 := by
    have := analyticAt_weierstrassP_sub L (zero_mem _)
    simp only [sub_zero] at this; exact this
  have hqa : AnalyticAt ℂ q 0 := by
    have := analyticAt_weierstrassP_sub L' (zero_mem _)
    simp only [sub_zero] at this; exact this
  set d : ℂ → ℂ := fun w => p w - q w with hd
  have hda : AnalyticAt ℂ d 0 := hpa.sub hqa
  show ∀ᶠ z in 𝓝 (0 : ℂ), d z = 0
  rw [← analyticOrderAt_eq_top]
  by_contra htop
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  obtain ⟨g, hga, hg0, hgd⟩ := (hda.analyticOrderAt_eq_natCast (n := n)).mp hn.symm
  simp only [sub_zero, smul_eq_mul] at hgd
  -- `z d'(z) = zⁿ (n g + z g')` near `0`.
  have hzd : ∀ᶠ z in 𝓝 (0 : ℂ), z * deriv d z = z ^ n * (n * g z + z * deriv g z) := by
    filter_upwards [hgd.eventually_nhds, hga.eventually_analyticAt] with z hz hgz
    rw [EventuallyEq.deriv_eq hz]
    rw [deriv_fun_mul (by fun_prop) hgz.differentiableAt, deriv_pow_field]
    rcases n with _ | m
    · simp
    · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
      ring
  -- the two differential equations
  have hP := p23R1_ode_regularPart L
  have hQ := p23R1_ode_regularPart L'
  set A : ℂ → ℂ := fun z => z ^ 3 * (deriv p z + deriv q z) - 4
  set B : ℂ → ℂ := fun z => 4 * ((1 + z ^ 2 * p z) ^ 2 + (1 + z ^ 2 * p z) * (1 + z ^ 2 * q z) +
    (1 + z ^ 2 * q z) ^ 2) - L.g₂ * z ^ 4
  have hbr : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      (n * g z + z * deriv g z) * A z - g z * B z = 0 := by
    filter_upwards [hP, hQ, nhdsWithin_le_nhds hzd, nhdsWithin_le_nhds hgd,
      self_mem_nhdsWithin, nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
      nhdsWithin_le_nhds (L'.compl_lattice_sdiff_singleton_mem_nhds 0)]
      with z hPz hQz hzdz hgdz hz0 hzL hzL'
    have hz0' : z ≠ 0 := hz0
    have hdiff : ∀ M : PeriodPair, z ∉ M.lattice →
        DifferentiableAt ℂ (fun w => ℘[M] w - 1 / w ^ 2) z := by
      intro M hM
      have hU : IsOpen (M.latticeᶜ : Set ℂ) := M.isClosed_lattice.isOpen_compl
      have := (M.differentiableOn_weierstrassP z hM).differentiableAt (hU.mem_nhds hM)
      exact this.sub (by fun_prop (disch := exact pow_ne_zero 2 hz0'))
    have hdd : deriv d z = deriv p z - deriv q z :=
      deriv_sub (hdiff L fun h => hzL ⟨h, hz0⟩) (hdiff L' fun h => hzL' ⟨h, hz0⟩)
    have key : z ^ 2 * (z * deriv d z) * A z = z ^ 2 * d z * B z := by
      rw [hdd]
      simp only [A, B, d]
      rw [← h₂, ← h₃] at hQz
      linear_combination hPz - hQz
    rw [hzdz, hgdz] at key
    have hzn : z ^ 2 * z ^ n ≠ 0 := mul_ne_zero (pow_ne_zero _ hz0') (pow_ne_zero _ hz0')
    have : z ^ 2 * z ^ n * ((n * g z + z * deriv g z) * A z - g z * B z) = 0 := by
      linear_combination key
    exact (mul_eq_zero.mp this).resolve_left hzn
  have hcont : ContinuousAt (fun z => (n * g z + z * deriv g z) * A z - g z * B z) 0 := by
    have c1 := hga.continuousAt
    have c2 := hga.deriv.continuousAt
    have c3 := hpa.deriv.continuousAt
    have c4 := hqa.deriv.continuousAt
    have c5 := hpa.continuousAt
    have c6 := hqa.continuousAt
    simp only [A, B]
    fun_prop
  have h0 : (n * g 0 + 0 * deriv g 0) * A 0 - g 0 * B 0 = 0 :=
    tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (hbr.mono fun z hz => hz.symm))
  simp only [A, B] at h0
  have : (4 * (n : ℂ) + 12) * g 0 = 0 := by linear_combination -h0
  rcases mul_eq_zero.mp this with h | h
  · have : (4 * (n : ℝ) + 12) = 0 := by exact_mod_cast h
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  · exact hg0 h

/-- A lattice with the same `℘` near `0` as another is contained in it. -/
theorem p23R1_lattice_le_of_invariants (L L' : PeriodPair) (h₂ : L.g₂ = L'.g₂)
    (h₃ : L.g₃ = L'.g₃) : L.lattice ≤ L'.lattice := by
  have hev := p23R1_weierstrassP_eventuallyEq_of_invariants L L' h₂ h₃
  have hev' : ∀ᶠ z in 𝓝 (0 : ℂ), ℘[L] z = ℘[L'] z := hev.mono fun z hz => by
    linear_combination hz
  set U : Set ℂ := ((L.lattice : Set ℂ) ∪ L'.lattice)ᶜ with hUdef
  have hcount : ∀ M : PeriodPair, (M.lattice : Set ℂ).Countable := fun M => by
    have : Countable M.lattice := M.latticeEquivProd.toEquiv.injective.countable
    exact Set.countable_coe_iff.mp this
  have hUc : IsPreconnected U :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp [rank_real_complex])
      ((hcount L).union (hcount L'))).isPreconnected
  have hUo : IsOpen U := (L.isClosed_lattice.union L'.isClosed_lattice).isOpen_compl
  have hFa : AnalyticOnNhd ℂ (fun z => ℘[L] z - ℘[L'] z) U := fun z hz => by
    simp only [hUdef, Set.compl_union, Set.mem_inter_iff, Set.mem_compl_iff,
      SetLike.mem_coe] at hz
    exact (L.analyticOnNhd_weierstrassP z hz.1).sub (L'.analyticOnNhd_weierstrassP z hz.2)
  -- a point of `U` near `0` where `℘_L = ℘_{L'}` nearby
  have hpt : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ U ∧ ∀ᶠ y in 𝓝 z, ℘[L] y = ℘[L'] y := by
    filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
      nhdsWithin_le_nhds (L'.compl_lattice_sdiff_singleton_mem_nhds 0), self_mem_nhdsWithin,
      nhdsWithin_le_nhds hev'.eventually_nhds] with z h1 h2 h0 h3
    refine ⟨?_, h3⟩
    simp only [hUdef, Set.compl_union, Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe]
    exact ⟨fun h => h1 ⟨h, h0⟩, fun h => h2 ⟨h, h0⟩⟩
  obtain ⟨z₁, hz₁U, hz₁⟩ := hpt.exists
  have hzero : Set.EqOn (fun z => ℘[L] z - ℘[L'] z) 0 U :=
    hFa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hz₁U
      (hz₁.mono fun y hy => by simp [hy])
  intro l hl
  by_contra hl'
  have hord := L.order_weierstrassP l hl
  have hloc : ℘[L] =ᶠ[𝓝[≠] l] ℘[L'] := by
    filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds l),
      nhdsWithin_le_nhds (L'.isClosed_lattice.isOpen_compl.mem_nhds hl'), self_mem_nhdsWithin]
      with z h1 h2 h0
    have hzU : z ∈ U := by
      simp only [hUdef, Set.compl_union, Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe]
      exact ⟨fun h => h1 ⟨h, h0⟩, h2⟩
    exact sub_eq_zero.mp (hzero hzU)
  rw [meromorphicOrderAt_congr hloc] at hord
  have := (L'.analyticOnNhd_weierstrassP l hl').meromorphicOrderAt_nonneg
  rw [hord] at this
  exact absurd this (by decide)

end p23R1Uniq

/-- DLMF §23.3(i): the lattice is uniquely determined by its invariants. -/
@[dlmf 23.3.i]
theorem lattice_eq_of_invariants_eq (L L' : PeriodPair) (h₂ : L.g₂ = L'.g₂) (h₃ : L.g₃ = L'.g₃) :
    L.lattice = L'.lattice :=
  le_antisymm (p23R1_lattice_le_of_invariants L L' h₂ h₃)
    (p23R1_lattice_le_of_invariants L' L h₂.symm h₃.symm)

/-- The square lattice with half-periods `1, i`, used to see that `PeriodPair` is nonempty. -/
def wp23_squareHalfPeriods : HalfPeriods := ⟨1, I, one_ne_zero, by simp⟩

instance : Nonempty PeriodPair := ⟨wp23_squareHalfPeriods.periodPair⟩

/-- A chosen period pair with invariants `g₂, g₃` (junk `PeriodPair` when none exists, i.e.
when `g₂³ = 27g₃²`). Used to define the invariants form of the Weierstrass functions. -/
def periodPairOfInvariants (g₂ g₃ : ℂ) : PeriodPair :=
  Classical.epsilon fun L : PeriodPair ↦ L.g₂ = g₂ ∧ L.g₃ = g₃

/-- `℘(z; g₂, g₃)` (DLMF 23.3.8): `℘(z|𝕃)` for the lattice with invariants `g₂, g₃`; DLMF
assumes `g₂³ ≠ 27g₃²`. -/
@[dlmf 23.3.E8]
def weierstrassPInvariants (g₂ g₃ z : ℂ) : ℂ := ℘[periodPairOfInvariants g₂ g₃] z

/-- `ζ(z; g₂, g₃)` (DLMF §23.3(i)). -/
@[dlmf 23.3.i]
def weierstrassZetaInvariants (g₂ g₃ z : ℂ) : ℂ := weierstrassZeta (periodPairOfInvariants g₂ g₃) z

/-- `σ(z; g₂, g₃)` (DLMF §23.3(i)). -/
@[dlmf 23.3.i]
def weierstrassSigmaInvariants (g₂ g₃ z : ℂ) : ℂ :=
  weierstrassSigma (periodPairOfInvariants g₂ g₃) z

theorem periodPairOfInvariants_spec (g₂ g₃ : ℂ) (h : g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0) :
    (periodPairOfInvariants g₂ g₃).g₂ = g₂ ∧ (periodPairOfInvariants g₂ g₃).g₃ = g₃ := by
  unfold periodPairOfInvariants
  exact Classical.epsilon_spec (exists_periodPair_invariants g₂ g₃ h)

theorem wp23_weierstrassP_eq_of_lattice_eq (L L' : PeriodPair) (h : L.lattice = L'.lattice)
    (z : ℂ) : ℘[L] z = ℘[L'] z := by
  simp only [PeriodPair.weierstrassP]
  rw [← (Equiv.subtypeEquivRight (fun x => by rw [h]) : L.lattice ≃ L'.lattice).tsum_eq]
  rfl

theorem wp23_weierstrassZeta_eq_of_lattice_eq (L L' : PeriodPair) (h : L.lattice = L'.lattice)
    (z : ℂ) : weierstrassZeta L z = weierstrassZeta L' z := by
  simp only [weierstrassZeta]
  rw [← (Equiv.subtypeEquivRight (fun x => by rw [h]) : L.lattice ≃ L'.lattice).tsum_eq]
  rfl

theorem wp23_weierstrassSigma_eq_of_lattice_eq (L L' : PeriodPair) (h : L.lattice = L'.lattice)
    (z : ℂ) : weierstrassSigma L z = weierstrassSigma L' z := by
  simp only [weierstrassSigma]
  rw [← (Equiv.subtypeEquivRight (fun x => by rw [h]) : L.lattice ≃ L'.lattice).tprod_eq]
  rfl

/-- DLMF 23.3.8: `℘(z; g₂, g₃) = ℘(z|𝕃)` for every lattice `𝕃` with invariants `g₂, g₃`. -/
@[dlmf 23.3.E8]
theorem weierstrassPInvariants_eq (L : PeriodPair) (z : ℂ) :
    weierstrassPInvariants L.g₂ L.g₃ z = ℘[L] z := by
  have hΔ : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := latticeDiscriminant_ne_zero' L
  obtain ⟨h₂, h₃⟩ := periodPairOfInvariants_spec L.g₂ L.g₃ hΔ
  exact wp23_weierstrassP_eq_of_lattice_eq _ _ (lattice_eq_of_invariants_eq _ _ h₂ h₃) z

/-- DLMF §23.3(i): `σ(z; g₂, g₃)` is an entire function of `(z, g₂, g₃)` (restricted to
`g₂³ ≠ 27g₃²` it is the invariants form of `σ`). -/
@[dlmf 23.3.i]
theorem exists_entire_weierstrassSigmaInvariants :
    ∃ F : ℂ × ℂ × ℂ → ℂ, AnalyticOnNhd ℂ F Set.univ ∧
      ∀ g₂ g₃ z, g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0 → F (z, g₂, g₃) = weierstrassSigmaInvariants g₂ g₃ z := by
  sorry

end DLMF.Weierstrass
