/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
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

/-- DLMF 23.2.2–23.2.3: for integers `a, b, c, d` and `χ₁ = aω₁ + bω₃`, `χ₃ = cω₁ + dω₃`,
the numbers `2χ₁, 2χ₃` are (DLMF-oriented, `ℑ(χ₃/χ₁) > 0`) generators of `𝕃` iff
`ad - bc = 1`. The orientation condition is part of DLMF's notion of generators
(§23.2(i)); without it the condition would be `ad - bc = ±1`. -/
@[dlmf 23.2.E2, dlmf 23.2.E3]
theorem generators_iff (a b c d : ℤ) :
    (Submodule.span ℤ {2 * (a * H.ω₁ + b * H.ω₃), 2 * (c * H.ω₁ + d * H.ω₃)} = H.lattice ∧
      0 < ((c * H.ω₁ + d * H.ω₃) / (a * H.ω₁ + b * H.ω₃)).im) ↔ a * d - b * c = 1 := by
  sorry

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

/-- The double product for `σ` converges (unconditionally) for every `z` (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem multipliable_weierstrassSigma (L : PeriodPair) (z : ℂ) :
    Multipliable fun l : L.lattice ↦ (1 - z / l) * cexp (z / l + z ^ 2 / (2 * l ^ 2)) := by
  sorry

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
  sorry

/-- The zeros of `σ` are exactly the lattice points (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem weierstrassSigma_eq_zero_iff (L : PeriodPair) {z : ℂ} :
    weierstrassSigma L z = 0 ↔ z ∈ L.lattice := by
  sorry

/-- The zeros of `σ` are simple (DLMF §23.2(ii)). -/
@[dlmf 23.2.ii]
theorem deriv_weierstrassSigma_ne_zero (L : PeriodPair) {z : ℂ} (hz : z ∈ L.lattice) :
    deriv (weierstrassSigma L) z ≠ 0 := by
  sorry

/-- DLMF 23.2.8: `ζ(z) = σ'(z)/σ(z)` for `z ∉ 𝕃`. -/
@[dlmf 23.2.E8]
theorem weierstrassZeta_eq_deriv_div (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    weierstrassZeta L z = deriv (weierstrassSigma L) z / weierstrassSigma L z := by
  sorry

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

/-- DLMF 23.2.14 (Legendre's relation):
`η₃ω₂ - η₂ω₃ = η₂ω₁ - η₁ω₂ = η₁ω₃ - η₃ω₁ = πi/2`. -/
@[dlmf 23.2.E14]
theorem legendre_relation :
    H.eta 3 * H.ω₂ - H.eta 2 * H.ω₃ = π * I / 2 ∧
      H.eta 2 * H.ω₁ - H.eta 1 * H.ω₂ = π * I / 2 ∧
      H.eta 1 * H.ω₃ - H.eta 3 * H.ω₁ = π * I / 2 := by
  sorry

/-- DLMF 23.2.15: `σ(z + 2ω_j) = -e^{2η_j(z + ω_j)} σ(z)`, `j = 1, 2, 3`, for all `z ∈ ℂ`. -/
@[dlmf 23.2.E15]
theorem weierstrassSigma_add_two_mul_halfPeriod (z : ℂ) {j : ℕ}
    (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    H.weierstrassSigma (z + 2 * H.halfPeriod j) =
      -cexp (2 * H.eta j * (z + H.halfPeriod j)) * H.weierstrassSigma z := by
  sorry

/-- DLMF 23.2.16: `σ'(2ω_j) = -e^{2η_jω_j}`, `j = 1, 2, 3`. -/
@[dlmf 23.2.E16]
theorem deriv_weierstrassSigma_two_mul_halfPeriod {j : ℕ} (hj : j ∈ ({1, 2, 3} : Finset ℕ)) :
    deriv H.weierstrassSigma (2 * H.halfPeriod j) = -cexp (2 * H.eta j * H.halfPeriod j) := by
  sorry

/-- DLMF 23.2.17: for `j ≠ k` in `{1, 2, 3}` and `m, n ∈ ℤ`,
`σ(z + 2mω_j + 2nω_k)/σ(z) = (-1)^{m+n+mn} exp((2mη_j + 2nη_k)(mω_j + nω_k + z))`.
Stated in multiplied-out form, valid for all `z` (both sides vanish on `𝕃`). -/
@[dlmf 23.2.E17]
theorem weierstrassSigma_add_lattice (z : ℂ) {j k : ℕ} (hj : j ∈ ({1, 2, 3} : Finset ℕ))
    (hk : k ∈ ({1, 2, 3} : Finset ℕ)) (hjk : j ≠ k) (m n : ℤ) :
    H.weierstrassSigma (z + 2 * m * H.halfPeriod j + 2 * n * H.halfPeriod k) =
      (-1 : ℂ) ^ (m + n + m * n) *
        cexp ((2 * m * H.eta j + 2 * n * H.eta k) * (m * H.halfPeriod j + n * H.halfPeriod k + z)) *
        H.weierstrassSigma z := by
  sorry

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

/-- DLMF §23.3(i): the lattice roots `e₁, e₂, e₃` are distinct. -/
@[dlmf 23.3.i]
theorem e_distinct : H.e 1 ≠ H.e 2 ∧ H.e 2 ≠ H.e 3 ∧ H.e 1 ≠ H.e 3 := by
  sorry

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
  sorry

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

/-- DLMF §23.3(i): the lattice is uniquely determined by its invariants. -/
@[dlmf 23.3.i]
theorem lattice_eq_of_invariants_eq (L L' : PeriodPair) (h₂ : L.g₂ = L'.g₂) (h₃ : L.g₃ = L'.g₃) :
    L.lattice = L'.lattice := by
  sorry

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
