/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Relations
public import DLMF.Weierstrass.RealPaths
public import DLMF.Theta.Identities
public import DLMF.Elliptic.SpecialValues
public import DLMF.Gamma.BetaFunction.ParameterIntegrals
public import DLMF.EllipticIntegrals.EquianharmonicModulus
public import DLMF.Theta.ImaginaryAxisMonotonicity
public import DLMF.EllipticIntegrals.Quadratic
public import DLMF.EllipticIntegrals.Connection.CompleteIntegrals

/-!
# Real-valued Weierstrass functions and special lattices

Reality of the Weierstrass functions on the real axis (DLMF §23.5(i)) and the rectangular,
lemniscatic, rhombic and equianharmonic lattices (DLMF §23.5(ii)–(v)): signs and ordering of
the roots, the discriminant, and the explicit values of `η_j`, `e_j`, `g₂`, `g₃`, `τ` and the
modulus.

## Main definitions

* `conjPeriodPair`: the complex-conjugate period pair.
* `IsRectangular`, `IsLemniscatic`, `IsRhombic`, `IsEquianharmonic`: the special lattices of
  DLMF §23.5, as predicates on half-periods.
* `rectangular`, `rhombic`: explicit rectangular and rhombic half-periods.

## Main results

* `weierstrassP_real_iff`: DLMF §23.5(i), reality on the real axis.
* `IsRectangular.discriminant_pos`, `IsRectangular.roots`, `IsRectangular.e_two_g₃`,
  `rectangular_roots_monotone`: rectangular lattices (DLMF 23.5.1, §23.5(ii)).
* `IsLemniscatic.eta`, `IsLemniscatic.roots`, `IsLemniscatic.invariants`,
  `IsLemniscatic.modulus_sq`, `completeEllipticKOfParameter_lemniscatic`: DLMF 23.5.2–23.5.5.
* `IsRhombic.discriminant_neg`, `IsRhombic.roots`, `rhombic_e_one_monotone`: rhombic lattices
  (DLMF §23.5(iv)).
* `IsEquianharmonic.eta`, `IsEquianharmonic.roots`, `IsEquianharmonic.invariants`,
  `IsEquianharmonic.modulus_sq`, `completeEllipticK_equianharmonic`: DLMF 23.5.6–23.5.9.

## Implementation notes

Real numbers are complex numbers with vanishing imaginary part, and order statements are made
for real parts. The complete elliptic integral of 23.5.5 is the project's real
`DLMF.Elliptic.Real.completeEllipticKOfParameter` with parameter `m = k² = 1/2`; the complex values
in 23.5.9 use the principal complex integral `DLMF.EllipticIntegrals.completeEllipticK` (modulus
form) and the modulus `k = e^{iπ/6}` with `k² = e^{iπ/3}`.

For a rhombic lattice `τ = 1/2 + it`, and splitting the theta series into even and odd terms
gives `θ₃, θ₄(0|τ) = A ± iB` with `A, B = θ₃, θ₂(0|4it)`, so the roots are explicit in `A` and
`B`. The root `e₁` vanishes exactly when `(B/A)²`, the modulus at `4it`, is the smaller root of
`k² - 6k + 1`; since `t = K'/(4K)` is determined by the modulus, this happens only in the
pseudo-lemniscatic case, where `e₁ = 0` follows from the invariance of the lattice under `i`.
-/

@[expose] public section

open Complex PeriodPair DLMF.JacobiElliptic
open scoped Real

noncomputable section

namespace DLMF.Weierstrass

open DLMF.EllipticIntegrals
    (completeEllipticK completeEllipticKPrime completeEllipticK_singular_three_eq_integral
  exp_pi_mul_I_div_twelve completeEllipticK_exp_pi_mul_I_div_six)

section Conjugation
open Filter Topology
open scoped ComplexConjugate

/-- The complex-conjugate period pair `(ω̄₁, ω̄₂)`. -/
def conjPeriodPair (L : PeriodPair) : PeriodPair :=
  ⟨conj L.ω₁, conj L.ω₂, by
    have h := L.indep.map' Complex.conjLIE.toLinearEquiv.toLinearMap
      (LinearEquiv.ker _)
    convert h using 1
    funext i; fin_cases i <;> rfl⟩

/-- Membership in the conjugate lattice. -/
lemma mem_conjPeriodPair_lattice (L : PeriodPair) {z : ℂ} :
    z ∈ (conjPeriodPair L).lattice ↔ conj z ∈ L.lattice := by
  simp only [PeriodPair.mem_lattice, conjPeriodPair]
  constructor
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by simp⟩
  · rintro ⟨m, n, h⟩
    refine ⟨m, n, ?_⟩
    have := congrArg conj h
    simp only [map_add, map_mul, map_intCast, conj_conj] at this
    exact this

/-- Conjugation as a bijection `𝕃 ≃ 𝕃̄`. -/
def conjPeriodPairLatticeEquiv (L : PeriodPair) : L.lattice ≃ (conjPeriodPair L).lattice where
  toFun l := ⟨conj (l : ℂ), (mem_conjPeriodPair_lattice L).mpr (by simp)⟩
  invFun l := ⟨conj (l : ℂ), (mem_conjPeriodPair_lattice L).mp l.2⟩
  left_inv l := by ext; simp
  right_inv l := by ext; simp

/-- `℘(z|𝕃̄) = conj ℘(z̄|𝕃)`. -/
private lemma weierstrassP_conjPeriodPair (L : PeriodPair) (z : ℂ) :
    ℘[conjPeriodPair L] z = conj (℘[L] (conj z)) := by
  simp only [PeriodPair.weierstrassP]
  rw [← (conjPeriodPairLatticeEquiv L).tsum_eq, Complex.conj_tsum]
  refine tsum_congr fun l => ?_
  simp [conjPeriodPairLatticeEquiv, map_sub]

/-- `G_n(𝕃̄) = conj G_n(𝕃)`. -/
private lemma G_conjPeriodPair (L : PeriodPair) (n : ℕ) :
    (conjPeriodPair L).G n = conj (L.G n) := by
  simp only [PeriodPair.G]
  rw [← (conjPeriodPairLatticeEquiv L).tsum_eq, Complex.conj_tsum]
  refine tsum_congr fun l => ?_
  simp [conjPeriodPairLatticeEquiv]

/-- The conjugate lattice is the image of the lattice under conjugation. -/
private lemma coe_conjPeriodPair_lattice (L : PeriodPair) :
    ((conjPeriodPair L).lattice : Set ℂ) = (starRingEnd ℂ) '' (L.lattice : Set ℂ) := by
  ext z
  simp only [SetLike.mem_coe, Set.mem_image, mem_conjPeriodPair_lattice]
  constructor
  · intro h; exact ⟨conj z, h, by simp⟩
  · rintro ⟨w, hw, rfl⟩; simpa using hw

/-- DLMF §23.5(i): the Weierstrass functions are real on the real axis iff the lattice is
invariant under complex conjugation, equivalently iff `g₂, g₃ ∈ ℝ`. Stated for `℘`. -/
@[dlmf 23.5.i]
theorem weierstrassP_real_iff (L : PeriodPair) :
    ((∀ x : ℝ, (x : ℂ) ∉ L.lattice → (℘[L] x).im = 0) ↔
        (starRingEnd ℂ) '' (L.lattice : Set ℂ) = L.lattice) ∧
      ((starRingEnd ℂ) '' (L.lattice : Set ℂ) = L.lattice ↔ L.g₂.im = 0 ∧ L.g₃.im = 0) := by
  set L' := conjPeriodPair L with hL'
  have hc : (starRingEnd ℂ) '' (L.lattice : Set ℂ) = L.lattice ↔ L'.lattice = L.lattice := by
    rw [← coe_conjPeriodPair_lattice, SetLike.coe_set_eq]
  rw [hc]
  have hreal : ∀ w : ℂ, conj w = w ↔ w.im = 0 := fun w => Complex.conj_eq_iff_im
  refine ⟨⟨fun h => ?_, fun h x hx => ?_⟩, ⟨fun h => ?_, fun ⟨h2, h3⟩ => ?_⟩⟩
  · -- `℘` real on the real axis forces `𝕃̄ = 𝕃`
    have hpa : AnalyticAt ℂ (fun w => ℘[L] w - 1 / w ^ 2) 0 := by
      have := analyticAt_weierstrassP_sub L (zero_mem _)
      simp only [sub_zero] at this; exact this
    have hqa : AnalyticAt ℂ (fun w => ℘[L'] w - 1 / w ^ 2) 0 := by
      have := analyticAt_weierstrassP_sub L' (zero_mem _)
      simp only [sub_zero] at this; exact this
    have hR : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds |>.congr
          (fun _ => rfl) |> fun h => by simpa using h
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa using ht
    have heqR : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
        (fun w => ℘[L] w - 1 / w ^ 2) (t : ℂ) - (fun w => ℘[L'] w - 1 / w ^ 2) (t : ℂ) = 0 := by
      filter_upwards [hR.eventually (nhdsWithin_le_nhds
        (L.compl_lattice_sdiff_singleton_mem_nhds 0)),
        hR.eventually (self_mem_nhdsWithin (s := {(0 : ℂ)}ᶜ))] with t ht ht0
      have htL : (t : ℂ) ∉ L.lattice := fun hh => ht ⟨hh, ht0⟩
      have him := h t htL
      have : ℘[L'] (t : ℂ) = ℘[L] (t : ℂ) := by
        rw [hL', weierstrassP_conjPeriodPair, Complex.conj_ofReal, (hreal _).mpr him]
      simp [this]
    rcases (hpa.sub hqa).eventually_eq_or_eventually_ne (analyticAt_const (v := (0 : ℂ))) with
      hev | hne
    · have hev' : ∀ᶠ z in 𝓝 (0 : ℂ), ℘[L] z = ℘[L'] z := hev.mono fun z hz => by
        simp only [Pi.sub_apply] at hz; linear_combination hz
      exact le_antisymm (lattice_le_of_weierstrassP_eventuallyEq L' L
        (hev'.mono fun z hz => hz.symm)) (lattice_le_of_weierstrassP_eventuallyEq L L' hev')
    · exfalso
      have := (hR.eventually hne).and heqR
      obtain ⟨t, ht1, ht2⟩ := this.exists
      exact ht1 ht2
  · have e := weierstrassP_eq_of_lattice_eq L' L h (x : ℂ)
    rw [hL', weierstrassP_conjPeriodPair, Complex.conj_ofReal] at e
    exact (hreal _).mp e
  · have h4 := G_eq_of_lattice_eq L' L h 4
    have h6 := G_eq_of_lattice_eq L' L h 6
    rw [hL', G_conjPeriodPair] at h4 h6
    have r4 := (hreal _).mp h4
    have r6 := (hreal _).mp h6
    simp [PeriodPair.g₂, PeriodPair.g₃, r4, r6]
  · refine lattice_eq_of_invariants_eq L' L ?_ ?_
    · rw [hL', PeriodPair.g₂, G_conjPeriodPair, ← map_ofNat (starRingEnd ℂ) 60, ← map_mul]
      exact (hreal _).mpr h2
    · rw [hL', PeriodPair.g₃, G_conjPeriodPair, ← map_ofNat (starRingEnd ℂ) 140, ← map_mul]
      exact (hreal _).mpr h3


/-- A lattice invariant under conjugation has `℘(z̄) = conj ℘(z)`. -/
theorem weierstrassP_conj_of_conj_mem (L : PeriodPair)
    (hinv : ∀ z, z ∈ L.lattice → conj z ∈ L.lattice) (z : ℂ) :
    ℘[L] (conj z) = conj (℘[L] z) := by
  have hl : (conjPeriodPair L).lattice = L.lattice := by
    ext w
    rw [mem_conjPeriodPair_lattice]
    exact ⟨fun h => by simpa using hinv _ h, hinv w⟩
  have := weierstrassP_conjPeriodPair L (conj z)
  rw [weierstrassP_eq_of_lattice_eq _ _ hl, conj_conj] at this
  exact this

end Conjugation
namespace HalfPeriods

open scoped ComplexConjugate in
/-- `℘(z)` is real when `z̄ ≡ ±z` modulo a conjugation-invariant lattice. -/
theorem weierstrassP_im_eq_zero_of_conj {H : HalfPeriods}
    (hinv : ∀ z, z ∈ H.periodPair.lattice → conj z ∈ H.periodPair.lattice) {z l : ℂ}
    (hl : l ∈ H.lattice) (h : conj z = z + l ∨ conj z = -z + l) :
    (H.weierstrassP z).im = 0 := by
  have hc := weierstrassP_conj_of_conj_mem H.periodPair hinv z
  have heq : H.weierstrassP (conj z) = H.weierstrassP z := by
    rcases h with h | h
    · rw [h]; exact H.periodPair.weierstrassP_add_coe z ⟨l, hl⟩
    · rw [h]
      exact (H.periodPair.weierstrassP_add_coe (-z) ⟨l, hl⟩).trans
        (H.periodPair.weierstrassP_neg z)
  rw [← Complex.conj_eq_iff_im]
  exact hc.symm.trans heq

variable (H : HalfPeriods)

/-- A rectangular lattice (DLMF §23.5(ii)): `ω₁ > 0` and `ω₃/i > 0`. -/
def IsRectangular : Prop :=
  H.ω₁.im = 0 ∧ 0 < H.ω₁.re ∧ H.ω₃.re = 0 ∧ 0 < H.ω₃.im

/-- A lemniscatic lattice (DLMF §23.5(iii)): `ω₁ > 0` and `ω₃ = iω₁`. -/
def IsLemniscatic : Prop :=
  H.ω₁.im = 0 ∧ 0 < H.ω₁.re ∧ H.ω₃ = I * H.ω₁

/-- A rhombic lattice (DLMF §23.5(iv)): `ω₁ > 0`, `ℑω₃ > 0` and `ℜω₃ = ω₁/2`. (DLMF also lists
`Δ < 0`; this follows from the other conditions, see `IsRhombic.discriminant_neg`.) -/
def IsRhombic : Prop :=
  H.ω₁.im = 0 ∧ 0 < H.ω₁.re ∧ H.ω₃.re = H.ω₁.re / 2

/-- An equianharmonic lattice (DLMF §23.5(v)): `ω₁ > 0` and `ω₃ = e^{πi/3}ω₁`. -/
def IsEquianharmonic : Prop :=
  H.ω₁.im = 0 ∧ 0 < H.ω₁.re ∧ H.ω₃ = cexp (π * I / 3) * H.ω₁

open DLMF.Elliptic DLMF.Theta in
/-- Real data of a rectangular lattice: with `ω₁ = a`, `τ = it`, `A, B, C = θ₂, θ₃, θ₄(0|it)`
and `c = (π/(2a))²`, the roots, `K`, `k` and `k'` are explicit real numbers. -/
theorem exists_real_data_of_isRectangular {H : HalfPeriods} (h : H.IsRectangular) :
    ∃ a c A B C : ℝ, 0 < a ∧ H.ω₁ = a ∧ c = (π / (2 * a)) ^ 2 ∧ 0 < c ∧ 0 < A ∧ 1 ≤ B ∧ 0 < C ∧
      B ^ 4 = A ^ 4 + C ^ 4 ∧
      H.e 1 = ((c * (B ^ 4 + C ^ 4) / 3 : ℝ) : ℂ) ∧
      H.e 2 = ((c * (B ^ 4 + C ^ 4) / 3 - c * C ^ 4 : ℝ) : ℂ) ∧
      H.e 3 = ((c * (B ^ 4 + C ^ 4) / 3 - c * B ^ 4 : ℝ) : ℂ) ∧
      H.quarterK = ((π / 2 * B ^ 2 : ℝ) : ℂ) ∧ H.modulus = ((A ^ 2 / B ^ 2 : ℝ) : ℂ) ∧
      H.comodulus = ((C ^ 2 / B ^ 2 : ℝ) : ℂ) := by
  obtain ⟨h1i, h1r, h3r, h3i⟩ := h
  set a := H.ω₁.re
  set t := H.ω₃.im / a
  have ht : 0 < t := div_pos h3i h1r
  have hω1 : H.ω₁ = a := Complex.ext rfl (by simp [h1i])
  have hτ : H.tau = I * t := by
    rw [HalfPeriods.tau, hω1]
    have : H.ω₃ = I * H.ω₃.im := Complex.ext (by simp [h3r]) (by simp)
    rw [this]; simp only [t]; push_cast
    have : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr h1r.ne'
    field_simp
  have hB := one_le_jacobiThetaThreeImag ht
  have hC := jacobiThetaFourImag_pos ht
  have hA := jacobiThetaTwoImag_pos ht
  have h2 : jacobiThetaTwoTau 0 H.tau = (jacobiThetaTwoImag t : ℂ) :=
      by rw [hτ, jacobiThetaTwoTau_zero_I_mul_eq_div_sqrt ht]; rfl
  have h3 : jacobiThetaThreeTau 0 H.tau = (jacobiThetaThreeImag t : ℂ) :=
      by rw [hτ, jacobiThetaThreeTau_zero_I_mul_eq_imag]
  have h4 : jacobiThetaFourTau 0 H.tau = (jacobiThetaFourImag t : ℂ) :=
      by rw [hτ, jacobiThetaFourTau_zero_I_mul_eq_imag]
  obtain ⟨d3, d2⟩ := H.e_one_sub_e_three_and_e_one_sub_e_two
  have hs := H.e_sum
  set c : ℝ := (π / (2 * a)) ^ 2 with hc
  have hcc : (π / (2 * H.ω₁)) ^ 2 = (c : ℂ) := by rw [hc, hω1]; push_cast; ring
  rw [hcc, h3] at d3
  rw [hcc, h4] at d2
  have hB0 : (jacobiThetaThreeImag t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  refine ⟨a, c, jacobiThetaTwoImag t, jacobiThetaThreeImag t, jacobiThetaFourImag t, h1r, hω1, rfl,
      by positivity, hA, hB, hC,
    jacobiThetaThreeImag_pow_four ht, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · push_cast; linear_combination (d3 + d2 + hs) / 3
  · push_cast; linear_combination (d3 - 2 * d2 + hs) / 3
  · push_cast; linear_combination (-2 * d3 + d2 + hs) / 3
  · rw [HalfPeriods.quarterK, completeEllipticKOfTau, h3]; push_cast; ring
  · rw [HalfPeriods.modulus, jacobiModulusOfTau, h2, h3]; push_cast; ring
  · rw [HalfPeriods.comodulus, jacobiComodulusOfTau, h4, h3]; push_cast; ring

/-- DLMF §23.5(ii): for a rectangular lattice `Δ > 0`. -/
@[dlmf 23.5.ii]
theorem IsRectangular.discriminant_pos {H : HalfPeriods} (h : H.IsRectangular) :
    (latticeDiscriminant H.periodPair).im = 0 ∧ 0 < (latticeDiscriminant H.periodPair).re := by
  obtain ⟨a, c, A, B, C, -, -, -, hc, hA, hB, hC, hJ, e1, e2, e3, -⟩ :=
      exists_real_data_of_isRectangular h
  rw [H.latticeDiscriminant_eq, e1, e2, e3]
  have hA4 : 0 < A ^ 4 := by positivity
  have hC4 : 0 < C ^ 4 := by positivity
  rw [← ofReal_sub, ← ofReal_sub, ← ofReal_sub]
  norm_cast
  have h1 : c * (B ^ 4 + C ^ 4) / 3 - c * C ^ 4 - (c * (B ^ 4 + C ^ 4) / 3 - c * B ^ 4) ≠ 0 := by
    nlinarith
  have h2 : c * (B ^ 4 + C ^ 4) / 3 - c * B ^ 4 - c * (B ^ 4 + C ^ 4) / 3 ≠ 0 := by
    nlinarith
  have h3 : c * (B ^ 4 + C ^ 4) / 3 - (c * (B ^ 4 + C ^ 4) / 3 - c * C ^ 4) ≠ 0 := by
    nlinarith
  exact ⟨rfl, by positivity⟩

/-- DLMF 23.5.1: for a rectangular lattice the roots are real with `e₁ > e₂ > e₃` and
`e₁ > 0 > e₃`. -/
@[dlmf 23.5.E1]
theorem IsRectangular.roots {H : HalfPeriods} (h : H.IsRectangular) :
    (H.e 1).im = 0 ∧ (H.e 2).im = 0 ∧ (H.e 3).im = 0 ∧
      (H.e 2).re < (H.e 1).re ∧ (H.e 3).re < (H.e 2).re ∧ 0 < (H.e 1).re ∧ (H.e 3).re < 0 := by
  obtain ⟨a, c, A, B, C, -, -, -, hc, hA, hB, hC, hJ, e1, e2, e3, -⟩ :=
      exists_real_data_of_isRectangular h
  rw [e1, e2, e3]
  simp only [ofReal_im, ofReal_re, true_and]
  have hA4 : 0 < A ^ 4 := by positivity
  have hC4 : 0 < C ^ 4 := by positivity
  refine ⟨by nlinarith, by nlinarith, by positivity, by nlinarith⟩

/-- Rectangular half-periods `ω₁ = a`, `ω₃ = ib` with `a, b > 0`. -/
def rectangular (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : HalfPeriods :=
  ⟨a, b * I, by exact_mod_cast ha.ne', by
    rw [Complex.div_ofReal_im]; simpa using div_pos hb ha⟩

open DLMF.Theta in
/-- The roots of a rectangular lattice through the real theta constants at `τ = ib/a`. -/
private lemma rectangular_e_eq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (rectangular a b ha hb).e 1 = (((π / (2 * a)) ^ 2 *
        (jacobiThetaThreeImag (b / a) ^ 4 + jacobiThetaFourImag (b / a) ^ 4) / 3 : ℝ) : ℂ) ∧
      (rectangular a b ha hb).e 2 = (((π / (2 * a)) ^ 2 *
        (jacobiThetaThreeImag (b / a) ^ 4 - 2 * jacobiThetaFourImag (b / a) ^ 4) / 3 : ℝ) : ℂ) ∧
      (rectangular a b ha hb).e 3 = (((π / (2 * a)) ^ 2 *
        (jacobiThetaFourImag (b / a) ^ 4 - 2 * jacobiThetaThreeImag (b / a) ^ 4) / 3 : ℝ) : ℂ) := by
  set H := rectangular a b ha hb
  obtain ⟨d3, d2⟩ := H.e_one_sub_e_three_and_e_one_sub_e_two
  have hs := H.e_sum
  have hω : H.ω₁ = a := rfl
  have hτ : H.tau = I * ((b / a : ℝ) : ℂ) := by
    have : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    simp only [HalfPeriods.tau, H, rectangular]; push_cast; field_simp
  simp only [hτ, hω, jacobiThetaThreeTau_zero_I_mul_eq_imag,
    jacobiThetaFourTau_zero_I_mul_eq_imag] at d3 d2
  refine ⟨?_, ?_, ?_⟩
  all_goals push_cast
  · linear_combination (hs + d3 + d2) / 3
  · linear_combination (hs + d3 - 2 * d2) / 3
  · linear_combination (hs - 2 * d3 + d2) / 3

open DLMF.Theta in
/-- DLMF §23.5(ii): with `ω₁` fixed, `e₁` and `e₂` are decreasing and `e₃` is increasing
functions of `ℑω₃`. -/
@[dlmf 23.5.ii]
theorem rectangular_roots_monotone (a b₁ b₂ : ℝ) (ha : 0 < a) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hb : b₁ < b₂) :
    ((rectangular a b₂ ha hb₂).e 1).re < ((rectangular a b₁ ha hb₁).e 1).re ∧
      ((rectangular a b₂ ha hb₂).e 2).re < ((rectangular a b₁ ha hb₁).e 2).re ∧
      ((rectangular a b₁ ha hb₁).e 3).re < ((rectangular a b₂ ha hb₂).e 3).re := by
  obtain ⟨e11, e12, e13⟩ := rectangular_e_eq a b₁ ha hb₁
  obtain ⟨e21, e22, e23⟩ := rectangular_e_eq a b₂ ha hb₂
  rw [e11, e12, e13, e21, e22, e23]
  simp only [ofReal_re]
  set t₁ := b₁ / a
  set t₂ := b₂ / a
  have ht₁ : 0 < t₁ := div_pos hb₁ ha
  have ht : t₁ < t₂ := div_lt_div_of_pos_right hb ha
  have hc : 0 < (π / (2 * a)) ^ 2 := by have := Real.pi_pos; positivity
  have h4 : ∀ {x y : ℝ}, 0 ≤ x → x < y → x ^ 4 < y ^ 4 := fun hx hxy =>
    pow_lt_pow_left₀ hxy hx (by norm_num)
  have p3 : ∀ {t : ℝ}, 0 < t → 0 ≤ jacobiThetaThreeImag t := fun ht =>
    zero_le_one.trans (one_le_jacobiThetaThreeImag ht)
  have p4 : ∀ {t : ℝ}, 0 < t → 0 ≤ jacobiThetaFourImag t := fun ht =>
    (jacobiThetaFourImag_pos ht).le
  have a3 := h4 (p3 (ht₁.trans ht)) (jacobiThetaThreeImag_lt ht₁ ht)
  have a4 := h4 (p4 ht₁) (jacobiThetaFourImag_lt ht₁ ht)
  refine ⟨?_, ?_, ?_⟩
  · rw [jacobiThetaThreeImag_pow_four_add ht₁, jacobiThetaThreeImag_pow_four_add (ht₁.trans ht)]
    have b3 := h4 (p3 (by positivity)) (jacobiThetaThreeImag_lt (by positivity : 0 < 2 * t₁)
      (by linarith : 2 * t₁ < 2 * t₂))
    have b4 := h4 (p4 (by positivity)) (jacobiThetaFourImag_lt (by positivity : 0 < 2 * t₁)
      (by linarith : 2 * t₁ < 2 * t₂))
    gcongr ?_ * ?_ / 3
    linarith
  · gcongr ?_ * ?_ / 3
    linarith
  · gcongr ?_ * ?_ / 3
    linarith

/-- `ζ(cz) = c⁻¹ζ(z)` when multiplication by `c` preserves the lattice. -/
private lemma weierstrassZeta_mul_of_lattice_invariant (H : HalfPeriods) (c : ℂ) (hc : c ≠ 0)
    (hinv : ∀ z, z ∈ H.lattice ↔ z / c ∈ H.lattice) (z : ℂ) :
    H.weierstrassZeta (c * z) = c⁻¹ * H.weierstrassZeta z := by
  have hl : (scalePeriodPair c hc H.periodPair).lattice = H.periodPair.lattice := by
    ext w; rw [mem_scalePeriodPair_lattice_iff]; exact (hinv w).symm
  have := weierstrassZeta_scale c hc H.periodPair z
  rw [weierstrassZeta_eq_of_lattice_eq _ _ hl] at this
  exact this

/-- `e^{πi/3} = (1 + √3 i)/2`. -/
theorem exp_pi_I_div_three_eq : cexp (π * I / 3) = (1 + Real.sqrt 3 * I) / 2 := by
  rw [show (π : ℂ) * I / 3 = ((π / 3 : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring


/-- `℘(cz) = c⁻²℘(z)` when multiplication by `c` preserves the lattice. -/
theorem weierstrassP_mul_of_lattice_invariant (H : HalfPeriods) (c : ℂ) (hc : c ≠ 0)
    (hinv : ∀ z, z ∈ H.lattice ↔ z / c ∈ H.lattice) (z : ℂ) :
    H.weierstrassP (c * z) = c⁻¹ ^ 2 * H.weierstrassP z := by
  have hl : (scalePeriodPair c hc H.periodPair).lattice = H.periodPair.lattice := by
    ext w; rw [mem_scalePeriodPair_lattice_iff]; exact (hinv w).symm
  have := weierstrassP_scale c hc H.periodPair z
  rw [weierstrassP_eq_of_lattice_eq _ _ hl] at this
  exact this

/-- A lemniscatic lattice is invariant under multiplication by `i`. -/
private lemma mem_lattice_iff_div_I_of_ω₃_eq {H : HalfPeriods} (h3 : H.ω₃ = I * H.ω₁) :
    ∀ z, z ∈ H.lattice ↔ z / I ∈ H.lattice := by
  intro z
  simp only [H.mem_lattice_iff, h3]
  constructor
  · rintro ⟨m, n, rfl⟩; exact ⟨n, -m, by push_cast; field_simp; ring_nf; rw [I_sq]; ring⟩
  · rintro ⟨m, n, hmn⟩
    refine ⟨-n, m, ?_⟩
    have : z = I * (2 * m * H.ω₁ + 2 * n * (I * H.ω₁)) := by rw [← hmn]; field_simp
    rw [this]; push_cast; ring_nf; rw [I_sq]; ring

/-- DLMF 23.5.2: for a lemniscatic lattice `η₁ = iη₃ = π/(4ω₁)`. -/
@[dlmf 23.5.E2]
theorem IsLemniscatic.eta {H : HalfPeriods} (h : H.IsLemniscatic) :
    H.eta 1 = I * H.eta 3 ∧ H.eta 1 = π / (4 * H.ω₁) := by
  obtain ⟨-, -, h3⟩ := h
  have hω := H.ω₁_ne_zero
  have hinv : ∀ z, z ∈ H.lattice ↔ z / I ∈ H.lattice := by
    intro z
    simp only [H.mem_lattice_iff, h3]
    constructor
    · rintro ⟨m, n, rfl⟩; exact ⟨n, -m, by push_cast; field_simp; ring_nf; rw [I_sq]; ring⟩
    · rintro ⟨m, n, hmn⟩
      refine ⟨-n, m, ?_⟩
      have : z = I * (2 * m * H.ω₁ + 2 * n * (I * H.ω₁)) := by rw [← hmn]; field_simp
      rw [this]; push_cast; ring_nf; rw [I_sq]; ring
  have hz := H.weierstrassZeta_mul_of_lattice_invariant I I_ne_zero hinv H.ω₁
  have e3 : H.eta 3 = -I * H.eta 1 := by
    rw [HalfPeriods.eta, HalfPeriods.eta, halfPeriod_three, halfPeriod_one, h3, hz, inv_I]
  have hL := H.weierstrassSigma_eq_weierstrassSigmaTheta_and_eta_three.2
  rw [h3] at hL
  refine ⟨by rw [e3]; ring_nf; rw [I_sq]; ring, ?_⟩
  rw [e3] at hL
  field_simp at hL ⊢
  linear_combination hL

/-- DLMF 23.5.3: for a lemniscatic lattice `e₁ = -e₃ = Γ(1/4)⁴/(32πω₁²)` and `e₂ = 0`. -/
@[dlmf 23.5.E3]
theorem IsLemniscatic.roots {H : HalfPeriods} (h : H.IsLemniscatic) :
    H.e 1 = -H.e 3 ∧ H.e 1 = (Real.Gamma (1 / 4) : ℂ) ^ 4 / (32 * π * H.ω₁ ^ 2) ∧ H.e 2 = 0 := by
  have hτ : H.tau = I := by
    rw [HalfPeriods.tau, h.2.2, mul_div_assoc, div_self H.ω₁_ne_zero, mul_one]
  obtain ⟨-, -, h3⟩ := h
  have hω := H.ω₁_ne_zero
  have hp := H.weierstrassP_mul_of_lattice_invariant I I_ne_zero (mem_lattice_iff_div_I_of_ω₃_eq h3)
  have hI2 : (I⁻¹ : ℂ) ^ 2 = -1 := by rw [inv_I]; ring_nf; rw [I_sq]
  have e3 : H.e 3 = -H.e 1 := by
    rw [HalfPeriods.e, HalfPeriods.e, halfPeriod_three, halfPeriod_one, h3, hp, hI2]; ring
  have e2 : H.e 2 = 0 := by
    have h1 := hp H.ω₂
    have : I * H.ω₂ = H.ω₂ + 2 * H.halfPeriod 1 := by
      rw [halfPeriod_one, HalfPeriods.ω₂, h3]; ring_nf; rw [I_sq]; ring
    rw [this, H.weierstrassP_add_two_mul_halfPeriod _ (by simp), hI2] at h1
    have : H.e 2 = H.weierstrassP H.ω₂ := rfl
    rw [this]; linear_combination h1 / 2
  obtain ⟨-, -, d13⟩ := H.e_distinct
  have he1 : H.e 1 ≠ 0 := by
    intro h0; apply d13; rw [e3, h0]; ring
  have hd : H.e 1 - H.e 3 = 2 * H.e 1 := by rw [e3]; ring
  obtain ⟨-, hc⟩ := H.modulus_sq_eq
  rw [e2, hd] at hc
  have hc' : H.comodulus ^ 2 = 1 / 2 := by rw [hc]; field_simp; ring
  have hE := H.e_one_eq_jacobi
  rw [hc'] at hE
  set k : ℝ := Real.sqrt (1 / 2) with hkdef
  have hk2 : k ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hkpos : 0 < k := Real.sqrt_pos.mpr (by norm_num)
  have hKk : completeEllipticK k =
      (DLMF.Elliptic.Real.completeEllipticKOfParameter (1 / 2) : ℂ) := by
    rw [completeEllipticK_ofReal (by rw [hk2]; norm_num), hk2]
  have hKpk : completeEllipticKPrime k =
      (DLMF.Elliptic.Real.completeEllipticKOfParameter (1 / 2) : ℂ) := by
    rw [completeEllipticKPrime_ofReal (by rw [hk2]; norm_num), hk2]; norm_num
  have hval := DLMF.Elliptic.Real.completeEllipticKOfParameter_one_half
  have hG : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hK0 : (DLMF.Elliptic.Real.completeEllipticKOfParameter (1 / 2) : ℂ) ≠ 0 := by
    rw [hval]; exact_mod_cast (div_pos (pow_pos hG 2)
      (mul_pos (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos))).ne'
  have hdom : (k : ℂ) ∈ jacobiModulusDomain := by
    refine ⟨by simpa using hkpos, fun _ => ?_⟩
    simp only [ofReal_re]
    nlinarith
  have htk : jacobiTau k = I := by
    rw [jacobiTau, hKk, hKpk]; field_simp
  have hinv := (jacobi_inversion_k hdom).2.2
  rw [htk, hKk, hval] at hinv
  have hKq : H.quarterK = (Real.Gamma (1 / 4) : ℂ) ^ 2 / (4 * Real.sqrt π) := by
    rw [HalfPeriods.quarterK, hτ, hinv]; push_cast; rfl
  have hs : ((Real.sqrt π : ℝ) : ℂ) ^ 2 = π := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hs0 : ((Real.sqrt π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  refine ⟨by rw [e3]; ring, ?_, e2⟩
  rw [hE, hKq]
  field_simp
  rw [hs]; ring

/-- DLMF 23.5.4: for a lemniscatic lattice `g₂ = Γ(1/4)⁸/(256π²ω₁⁴)` and `g₃ = 0`. -/
@[dlmf 23.5.E4]
theorem IsLemniscatic.invariants {H : HalfPeriods} (h : H.IsLemniscatic) :
    H.g₂ = (Real.Gamma (1 / 4) : ℂ) ^ 8 / (256 * π ^ 2 * H.ω₁ ^ 4) ∧ H.g₃ = 0 := by
  obtain ⟨h13, h1, h2⟩ := h.roots
  have hω := H.ω₁_ne_zero
  have h3 : H.e 3 = -H.e 1 := by rw [h13]; ring
  refine ⟨?_, ?_⟩
  · rw [H.g₂_eq_e.1, h2, h3, h1]; field_simp; ring
  · rw [H.g₃_eq_e.1, h2]; ring

/-- DLMF §23.5(iii): for a lemniscatic lattice `τ = i`. -/
@[dlmf 23.5.iii]
theorem IsLemniscatic.tau {H : HalfPeriods} (h : H.IsLemniscatic) : H.tau = I := by
  rw [HalfPeriods.tau, h.2.2, mul_div_assoc, div_self H.ω₁_ne_zero, mul_one]

/-- DLMF 23.5.5: for a lemniscatic lattice the modulus defined by 23.6.16 satisfies
`k² = (e₂ - e₃)/(e₁ - e₃) = 1/2` (derived from 23.5.3). -/
@[dlmf 23.5.E5]
theorem IsLemniscatic.modulus_sq {H : HalfPeriods} (h : H.IsLemniscatic) :
    (H.e 2 - H.e 3) / (H.e 1 - H.e 3) = 1 / 2 := by
  obtain ⟨h13, h1, h2⟩ := h.roots
  have hne : H.e 1 ≠ 0 := by
    rw [h1]
    have hg : (Real.Gamma (1 / 4) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 4)).ne'
    have := H.ω₁_ne_zero
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hω := H.ω₁_ne_zero
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact div_ne_zero (pow_ne_zero 4 hg) (mul_ne_zero (mul_ne_zero (by norm_num) hπ)
      (pow_ne_zero 2 hω))
  have h3 : H.e 3 = -H.e 1 := by rw [h13]; ring
  rw [h2, h3]
  field_simp
  ring

/-- For a rectangular lattice, `e₂ = 0` forces `ω₃ = iω₁` (then `k² = 1/2`, so `K' = K`). -/
private lemma IsRectangular.eq_I_mul_of_e_two_eq_zero {H : HalfPeriods} (h : H.IsRectangular)
    (he : H.e 2 = 0) : H.ω₃ = I * H.ω₁ := by
  obtain ⟨h1i, h1r, h3r, h3i⟩ := h
  set a := H.ω₁.re
  set t := H.ω₃.im / a
  have ht : 0 < t := div_pos h3i h1r
  have hω1 : H.ω₁ = a := Complex.ext rfl (by simp [h1i])
  have hω3 : H.ω₃ = I * H.ω₃.im := Complex.ext (by simp [h3r]) (by simp)
  have hτ : H.tau = I * t := by
    rw [HalfPeriods.tau, hω1, hω3]; simp only [t]; push_cast
    have : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr h1r.ne'
    field_simp
  obtain ⟨d3, d2⟩ := H.e_one_sub_e_three_and_e_one_sub_e_two
  have hs := H.e_sum
  rw [hτ, jacobiThetaThreeTau_zero_I_mul_eq_imag] at d3
  rw [hτ, jacobiThetaFourTau_zero_I_mul_eq_imag] at d2
  have hc : (π / (2 * H.ω₁)) ^ 2 ≠ 0 := by
    have := H.ω₁_ne_zero; have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact pow_ne_zero _ (div_ne_zero this (mul_ne_zero two_ne_zero H.ω₁_ne_zero))
  have hBC : (jacobiThetaThreeImag t : ℂ) ^ 4 = 2 * (jacobiThetaFourImag t : ℂ) ^ 4 := by
    apply mul_left_cancel₀ hc
    linear_combination -d3 + 2 * d2 - hs + 3 * he
  have hBC' : jacobiThetaThreeImag t ^ 4 = 2 * jacobiThetaFourImag t ^ 4 := by
    exact_mod_cast hBC
  obtain ⟨-, -, -, -, -, -, hK1, hK2⟩ := jacobiModulusImag_spec ht
  have hB := one_le_jacobiThetaThreeImag ht
  have hJ := jacobiThetaThreeImag_pow_four ht
  have hk : jacobiModulusImag t ^ 2 = 1 / 2 := by
    rw [jacobiModulusImag]
    field_simp
    nlinarith
  rw [hk] at hK1
  rw [hk, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, hK1] at hK2
  have hB2 : 0 < π / 2 * jacobiThetaThreeImag t ^ 2 := by positivity
  have ht1 : t = 1 := by nlinarith
  have : H.ω₃.im = a := by
    have := ht1; simp only [t] at this; field_simp at this; linarith
  rw [hω3, this, hω1]

/-- DLMF §23.5(ii): for a rectangular lattice `e₂` and `g₃` have opposite signs unless
`ω₃ = iω₁`, in which case both vanish. -/
@[dlmf 23.5.ii]
theorem IsRectangular.e_two_g₃ {H : HalfPeriods} (h : H.IsRectangular) :
    H.g₃.im = 0 ∧ (H.ω₃ = I * H.ω₁ → H.e 2 = 0 ∧ H.g₃ = 0) ∧
      (H.ω₃ ≠ I * H.ω₁ → (H.e 2).re * H.g₃.re < 0) := by
  have hg := H.g₃_eq_e.1
  obtain ⟨a, c, A, B, C, ha, hω1, -, hc, hA, hB, hC, hJ, e1, e2, e3, -⟩ :=
    exists_real_data_of_isRectangular h
  set x := c * (B ^ 4 + C ^ 4) / 3
  set y := c * (B ^ 4 + C ^ 4) / 3 - c * C ^ 4
  set z := c * (B ^ 4 + C ^ 4) / 3 - c * B ^ 4
  have hg' : H.g₃ = ((4 * x * y * z : ℝ) : ℂ) := by
    rw [hg, e1, e2, e3]; push_cast; ring
  refine ⟨by rw [hg']; exact ofReal_im _, fun hl => ?_, fun hne => ?_⟩
  · have hL : H.IsLemniscatic := ⟨h.1, h.2.1, hl⟩
    exact ⟨hL.roots.2.2, hL.invariants.2⟩
  · rw [hg', e2]
    simp only [ofReal_re]
    have hy : y ≠ 0 := by
      intro h0; apply hne
      exact IsRectangular.eq_I_mul_of_e_two_eq_zero h (by rw [e2, h0, ofReal_zero])
    have hA4 : 0 < A ^ 4 := by positivity
    have hC4 : 0 < C ^ 4 := by positivity
    have hsq : 0 < y ^ 2 := by positivity
    have hx : 0 < x := by positivity
    have hz : z < 0 := by simp only [z]; nlinarith
    have : 4 * x * z < 0 := by nlinarith
    nlinarith

/-- DLMF 23.5.5: `K(k) = K'(k) = Γ(1/4)²/(4√π)` for `k² = 1/2` (parameter form; this is the
project's `DLMF.Elliptic.Real.completeEllipticKOfParameter_one_half`, and
`K' = K(1 - k²) = K(1/2)`). -/
@[dlmf 23.5.E5]
theorem completeEllipticKOfParameter_lemniscatic :
    DLMF.Elliptic.Real.completeEllipticKOfParameter (1 / 2) = Real.Gamma (1 / 4) ^ 2 /
        (4 * Real.sqrt π) ∧
      DLMF.Elliptic.Real.completeEllipticKOfParameter (1 - 1 / 2) =
          DLMF.Elliptic.Real.completeEllipticKOfParameter (1 / 2) :=
  ⟨DLMF.Elliptic.Real.completeEllipticKOfParameter_one_half, by norm_num⟩

open scoped ComplexConjugate in
/-- Rhombic lattices: `e₁` real and `e₃ = conj e₂ ∉ ℝ`. -/
private lemma isRhombic_e_conj {H : HalfPeriods} (h : H.IsRhombic) :
    conj (H.e 1) = H.e 1 ∧ H.e 3 = conj (H.e 2) ∧ (H.e 2).im ≠ 0 := by
  obtain ⟨h1i, -, h3r⟩ := h
  have hω1 : conj H.ω₁ = H.ω₁ := Complex.conj_eq_iff_im.mpr h1i
  have hω3 : conj H.ω₃ = H.ω₁ - H.ω₃ := by
    apply Complex.ext
    · simp [h3r]; ring
    · simp [h1i]
  have hinv : ∀ z, z ∈ H.lattice → conj z ∈ H.lattice := by
    intro z hz
    obtain ⟨m, n, rfl⟩ := H.mem_lattice_iff.mp hz
    refine H.mem_lattice_iff.mpr ⟨m + n, -n, ?_⟩
    simp only [map_add, map_mul, map_ofNat, map_intCast, hω1, hω3]
    push_cast; ring
  have hwp := weierstrassP_conj_of_conj_mem H.periodPair hinv
  have he1 : conj (H.e 1) = H.e 1 := by
    simp only [HalfPeriods.e, halfPeriod_one]
    rw [← hwp, hω1]
  have he3 : H.e 3 = conj (H.e 2) := by
    simp only [HalfPeriods.e, halfPeriod_three, halfPeriod_two]
    rw [← hwp]
    have : conj H.ω₂ = H.ω₃ - 2 * H.ω₁ := by
      simp only [HalfPeriods.ω₂, map_sub, map_neg, hω1, hω3]; ring
    rw [this]
    have := H.weierstrassP_add_two_mul_halfPeriod (H.ω₃ - 2 * H.ω₁) (j := 1) (by simp)
    simp only [halfPeriod_one, sub_add_cancel] at this
    exact this
  refine ⟨he1, he3, fun h0 => ?_⟩
  have : H.e 3 = H.e 2 := by rw [he3]; exact Complex.conj_eq_iff_im.mpr h0
  exact H.e_distinct.2.1 this.symm

/-- DLMF §23.5(iv): for a rhombic lattice `Δ < 0`. -/
@[dlmf 23.5.iv]
theorem IsRhombic.discriminant_neg {H : HalfPeriods} (h : H.IsRhombic) :
    (latticeDiscriminant H.periodPair).im = 0 ∧ (latticeDiscriminant H.periodPair).re < 0 := by
  obtain ⟨h1, h3, hy⟩ := isRhombic_e_conj h
  set r := (H.e 1).re
  set x := (H.e 2).re
  set y := (H.e 2).im
  have e1 : H.e 1 = r := by
    apply Complex.ext <;> simp [r, Complex.conj_eq_iff_im.mp h1]
  have e2 : H.e 2 = x + y * I := (Complex.re_add_im _).symm
  have e3 : H.e 3 = x - y * I := by
    rw [h3]; apply Complex.ext <;> simp [x, y]
  have key : latticeDiscriminant H.periodPair =
      ((-64 * y ^ 2 * ((r - x) ^ 2 + y ^ 2) ^ 2 : ℝ) : ℂ) := by
    rw [H.latticeDiscriminant_eq, e1, e2, e3]
    push_cast
    linear_combination 64 * (y : ℂ) ^ 2 * ((y : ℂ) ^ 4 * I ^ 4 - (2 * ((r : ℂ) - x) ^ 2 *
      (y : ℂ) ^ 2 + (y : ℂ) ^ 4) * I ^ 2 + (((r : ℂ) - x) ^ 2 + (y : ℂ) ^ 2) ^ 2) * I_sq
  rw [key, Complex.ofReal_im, Complex.ofReal_re]
  refine ⟨rfl, ?_⟩
  have hy2 : 0 < y ^ 2 := by positivity
  have : 0 < ((r - x) ^ 2 + y ^ 2) ^ 2 := by positivity
  nlinarith

open DLMF.Elliptic DLMF.Theta in
/-- At `τ = 1/2 + it`, `θ₃(0|τ) = A + iB` and `θ₄(0|τ) = A - iB` with `A = θ₃(0|4it)` and
`B = θ₂(0|4it)`. -/
private lemma jacobiThetaTau_half_add_I_mul {t : ℝ} (ht : 0 < t) :
    jacobiThetaThreeTau 0 (1 / 2 + I * t) =
        (jacobiThetaThreeImag (4 * t) : ℂ) + I * (jacobiThetaTwoImag (4 * t) : ℂ) ∧
      jacobiThetaFourTau 0 (1 / 2 + I * t) =
        (jacobiThetaThreeImag (4 * t) : ℂ) - I * (jacobiThetaTwoImag (4 * t) : ℂ) := by
  have hτ : 0 < (1 / 2 + I * (t : ℂ)).im := by simpa using ht
  have h4 : 4 * (1 / 2 + I * (t : ℂ)) = I * ((4 * t : ℝ) : ℂ) + 1 + 1 := by push_cast; ring
  have h4t : (0 : ℝ) < 4 * t := by positivity
  have e3 : jacobiThetaThreeTau 0 (4 * (1 / 2 + I * (t : ℂ))) = jacobiThetaThreeImag (4 * t) := by
    rw [h4, jacobiThetaThreeTau_add_one, jacobiThetaFourTau_add_one,
      jacobiThetaThreeTau_zero_I_mul_eq_imag]
  have hI : cexp (π * I / 4) * cexp (π * I / 4) = I := by
    rw [← Complex.exp_add, show (π : ℂ) * I / 4 + π * I / 4 = π / 2 * I by ring,
      Complex.exp_pi_div_two_mul_I]
  have e2 : jacobiThetaTwoTau 0 (4 * (1 / 2 + I * (t : ℂ))) =
      I * jacobiThetaTwoImag (4 * t) := by
    rw [h4, jacobiThetaTwoTau_add_one, jacobiThetaTwoTau_add_one,
      jacobiThetaTwoTau_zero_I_mul_eq_div_sqrt h4t, ← mul_assoc, hI]
    rfl
  constructor
  · rw [jacobiThetaThreeTau_eq_four_mul_tau _ _ hτ, mul_zero, e3, e2]
  · rw [jacobiThetaFourTau, zero_add, jacobiThetaThreeTau_eq_four_mul_tau _ _ hτ,
      show 2 * ((π : ℂ) / 2) = 0 + π by ring, jacobiThetaThreeTau_add_pi,
      jacobiThetaTwoTau_add_pi, e3, e2]
    ring

open DLMF.Elliptic DLMF.Theta in
/-- Real data of a rhombic lattice: with `ω₁ = a`, `ω₃ = a/2 + iat`, `A, B = θ₃, θ₂(0|4it)`,
`c = (π/(2a))²` and `P = A⁴ - 6A²B² + B⁴`, `e₁ = 2cP/3` and `e₂, e₃ = -cP/3 ± 4cAB(A² - B²)i`. -/
private lemma exists_real_data_of_isRhombic {H : HalfPeriods} (h : H.IsRhombic) :
    ∃ a t c A B : ℝ, 0 < a ∧ 0 < t ∧ H.ω₁ = a ∧ H.ω₃ = a / 2 + a * t * I ∧ 0 < c ∧
      0 < B ∧ B < A ∧ A = jacobiThetaThreeImag (4 * t) ∧ B = jacobiThetaTwoImag (4 * t) ∧
      H.e 1 = ((2 * c * (A ^ 4 - 6 * A ^ 2 * B ^ 2 + B ^ 4) / 3 : ℝ) : ℂ) ∧
      H.e 2 = ((-(c * (A ^ 4 - 6 * A ^ 2 * B ^ 2 + B ^ 4)) / 3 : ℝ) : ℂ) +
        ((4 * c * A * B * (A ^ 2 - B ^ 2) : ℝ) : ℂ) * I ∧
      H.e 3 = ((-(c * (A ^ 4 - 6 * A ^ 2 * B ^ 2 + B ^ 4)) / 3 : ℝ) : ℂ) -
        ((4 * c * A * B * (A ^ 2 - B ^ 2) : ℝ) : ℂ) * I := by
  obtain ⟨h1i, h1r, h3r⟩ := h
  set a := H.ω₁.re
  have hω1 : H.ω₁ = a := Complex.ext rfl (by simp [h1i])
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr h1r.ne'
  set t := H.ω₃.im / a
  have hdiv := H.im_div_pos
  rw [hω1, Complex.div_ofReal_im] at hdiv
  have ht : 0 < t := hdiv
  have hω3 : H.ω₃ = a / 2 + a * t * I := by
    apply Complex.ext
    · simp [h3r]
    · have : (a : ℂ) * t * I = ((a * t : ℝ) : ℂ) * I := by push_cast; ring
      rw [add_im, this, Complex.mul_I_im, ofReal_re, Complex.div_ofNat_im, ofReal_im]
      simp only [t]
      field_simp
      ring
  have hτ : H.tau = 1 / 2 + I * t := by
    rw [HalfPeriods.tau, hω1, hω3]; field_simp
  have h4t : (0 : ℝ) < 4 * t := by positivity
  set A := jacobiThetaThreeImag (4 * t)
  set B := jacobiThetaTwoImag (4 * t)
  have hB := jacobiThetaTwoImag_pos h4t
  have hA := one_le_jacobiThetaThreeImag h4t
  have hC := jacobiThetaFourImag_pos h4t
  have hJ := jacobiThetaThreeImag_pow_four h4t
  have hBA : B < A := by
    by_contra hle
    push Not at hle
    have : A ^ 4 ≤ B ^ 4 := pow_le_pow_left₀ (by linarith) hle 4
    have : 0 < jacobiThetaFourImag (4 * t) ^ 4 := by positivity
    linarith
  obtain ⟨th3, th4⟩ := jacobiThetaTau_half_add_I_mul ht
  obtain ⟨d3, d2⟩ := H.e_one_sub_e_three_and_e_one_sub_e_two
  have hs := H.e_sum
  set c : ℝ := (π / (2 * a)) ^ 2 with hc
  have hcc : (π / (2 * H.ω₁)) ^ 2 = (c : ℂ) := by rw [hc, hω1]; push_cast; ring
  rw [hcc, hτ, th3] at d3
  rw [hcc, hτ, th4] at d2
  refine ⟨a, t, c, A, B, h1r, ht, hω1, hω3, by positivity, hB, hBA, rfl, rfl, ?_, ?_, ?_⟩
  · push_cast
    linear_combination (d3 + d2 + hs) / 3 +
      2 * (B : ℂ) ^ 2 * c * (6 * A ^ 2 + B ^ 2 * I ^ 2 - B ^ 2) / 3 * I_sq
  · push_cast
    linear_combination (d3 - 2 * d2 + hs) / 3 -
      (B : ℂ) ^ 2 * c * (6 * A ^ 2 - 12 * A * B * I + B ^ 2 * I ^ 2 - B ^ 2) / 3 * I_sq
  · push_cast
    linear_combination (-2 * d3 + d2 + hs) / 3 -
      (B : ℂ) ^ 2 * c * (6 * A ^ 2 + 12 * A * B * I + B ^ 2 * I ^ 2 - B ^ 2) / 3 * I_sq

/-- If `2ω₃ = (1 + i)ω₁` the lattice is invariant under multiplication by `i`. -/
private lemma mem_lattice_iff_div_I_of_two_mul_ω₃_eq {H : HalfPeriods}
    (h3 : 2 * H.ω₃ = (1 + I) * H.ω₁) : ∀ z, z ∈ H.lattice ↔ z / I ∈ H.lattice := by
  intro z
  have hω3 : H.ω₃ = (1 + I) * H.ω₁ / 2 := by linear_combination h3 / 2
  simp only [H.mem_lattice_iff, Complex.div_I, hω3]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨m + n, -(2 * m + n), ?_⟩
    push_cast
    linear_combination (-(n : ℂ)) * H.ω₁ * I_sq
  · rintro ⟨m, n, hmn⟩
    refine ⟨-m - n, 2 * m + n, ?_⟩
    push_cast
    linear_combination I * hmn + ((n : ℂ) * H.ω₁ + z) * I_sq

/-- If `2ω₃ = (1 + i)ω₁` (the pseudo-lemniscatic case) then `e₁ = 0`. -/
private lemma e_one_eq_zero_of_two_mul_ω₃_eq {H : HalfPeriods}
    (h3 : 2 * H.ω₃ = (1 + I) * H.ω₁) : H.e 1 = 0 := by
  have hp := H.weierstrassP_mul_of_lattice_invariant I I_ne_zero
    (mem_lattice_iff_div_I_of_two_mul_ω₃_eq h3) H.ω₁
  have hI2 : (I⁻¹ : ℂ) ^ 2 = -1 := by rw [inv_I]; ring_nf; rw [I_sq]
  have hz : I * H.ω₁ = -H.ω₁ + 2 * H.halfPeriod 3 := by
    rw [halfPeriod_three]; linear_combination -h3
  rw [hz, H.weierstrassP_add_two_mul_halfPeriod _ (by simp), hI2] at hp
  have hneg : H.weierstrassP (-H.ω₁) = H.weierstrassP H.ω₁ := H.periodPair.weierstrassP_neg H.ω₁
  rw [hneg] at hp
  have : H.e 1 = H.weierstrassP H.ω₁ := rfl
  rw [this]; linear_combination hp / 2

/-- The real modulus `t ↦ θ₂²/θ₃²(0|it)` is injective on `(0, ∞)`: `t = K'(k)/K(k)`. -/
private lemma eq_of_jacobiModulusImag_eq {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (h : jacobiModulusImag s = jacobiModulusImag s') : s = s' := by
  obtain ⟨-, -, -, -, -, -, hK, hK'⟩ := jacobiModulusImag_spec hs
  obtain ⟨-, -, -, -, -, -, hL, hL'⟩ := jacobiModulusImag_spec hs'
  rw [h, hL] at hK
  rw [h, hL'] at hK'
  have hB := one_le_jacobiThetaThreeImag hs
  have hB' := one_le_jacobiThetaThreeImag hs'
  have h0 : 0 < π / 2 * jacobiThetaThreeImag s ^ 2 := by positivity
  have h1 : s' * (π / 2 * jacobiThetaThreeImag s' ^ 2) =
      s * (π / 2 * jacobiThetaThreeImag s ^ 2) := by linear_combination hK'
  rw [hK] at h1
  exact (mul_right_cancel₀ h0.ne' h1).symm

/-- For a rhombic lattice, `e₁ = 0` only in the pseudo-lemniscatic case `2ω₃ = (1 + i)ω₁`. -/
private lemma two_mul_ω₃_eq_of_e_one_eq_zero {H : HalfPeriods} (h : H.IsRhombic)
    (he : H.e 1 = 0) : 2 * H.ω₃ = (1 + I) * H.ω₁ := by
  have key : ∀ {H : HalfPeriods}, H.IsRhombic → H.e 1 = 0 → ∃ a t : ℝ, 0 < t ∧ H.ω₁ = a ∧
      H.ω₃ = a / 2 + a * t * I ∧
      (jacobiModulusImag (4 * t)) ^ 2 - 6 * jacobiModulusImag (4 * t) + 1 = 0 := by
    intro H h he
    obtain ⟨a, t, c, A, B, -, ht, hω1, hω3, hc, hB, hBA, hA, hBd, e1, -, -⟩ :=
      exists_real_data_of_isRhombic h
    refine ⟨a, t, ht, hω1, hω3, ?_⟩
    rw [he] at e1
    have hP : A ^ 4 - 6 * A ^ 2 * B ^ 2 + B ^ 4 = 0 := by
      have := congrArg Complex.re e1
      simp only [zero_re, ofReal_re] at this
      have : c * (A ^ 4 - 6 * A ^ 2 * B ^ 2 + B ^ 4) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hc.ne'
    rw [jacobiModulusImag, ← hA, ← hBd]
    have hA0 : A ≠ 0 := by linarith
    field_simp
    linear_combination hP
  obtain ⟨a, t, ht, hω1, hω3, hk⟩ := key h he
  let H₀ : HalfPeriods := ⟨1, 1 / 2 + 1 / 2 * I, one_ne_zero, by simp⟩
  have h₀ : H₀.IsRhombic := ⟨by simp [H₀], by simp [H₀], by simp [H₀]⟩
  have hps : 2 * H₀.ω₃ = (1 + I) * H₀.ω₁ := by simp [H₀]; ring
  obtain ⟨a₀, t₀, ht₀, hω1₀, hω3₀, hk₀⟩ := key h₀ (e_one_eq_zero_of_two_mul_ω₃_eq hps)
  have ha₀ : a₀ = 1 := by
    have := congrArg Complex.re hω1₀; simpa [H₀] using this.symm
  have ht₀' : t₀ = 1 / 2 := by
    have := congrArg Complex.im hω3₀; simp [H₀, ha₀] at this; linarith
  obtain ⟨k0, k1, -⟩ := jacobiModulusImag_spec (show (0 : ℝ) < 4 * t by positivity)
  obtain ⟨l0, l1, -⟩ := jacobiModulusImag_spec (show (0 : ℝ) < 4 * t₀ by positivity)
  have hkk : jacobiModulusImag (4 * t) = jacobiModulusImag (4 * t₀) := by
    have : (jacobiModulusImag (4 * t) - jacobiModulusImag (4 * t₀)) *
        (jacobiModulusImag (4 * t) + jacobiModulusImag (4 * t₀) - 6) = 0 := by
      linear_combination hk - hk₀
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · linarith
  have := eq_of_jacobiModulusImag_eq (by positivity) (by positivity) hkk
  have htt : t = 1 / 2 := by linarith
  rw [hω3, hω1, htt]; push_cast; ring

/-- DLMF §23.5(iv): for a rhombic lattice `e₁` is real and `e₃ = conj e₂` with `ℑe₂ > 0`; `e₁`
and `g₃` have the same sign unless `2ω₃ = (1 + i)ω₁` (the pseudo-lemniscatic case), when both
vanish. -/
@[dlmf 23.5.iv]
theorem IsRhombic.roots {H : HalfPeriods} (h : H.IsRhombic) :
    (H.e 1).im = 0 ∧ H.e 3 = (starRingEnd ℂ) (H.e 2) ∧ 0 < (H.e 2).im ∧ H.g₃.im = 0 ∧
      (2 * H.ω₃ = (1 + I) * H.ω₁ → H.e 1 = 0 ∧ H.g₃ = 0) ∧
      (2 * H.ω₃ ≠ (1 + I) * H.ω₁ → 0 < (H.e 1).re * H.g₃.re) := by
  obtain ⟨a, t, c, A, B, -, -, -, -, hc, hB, hBA, -, -, e1, e2, e3⟩ :=
    exists_real_data_of_isRhombic h
  set r : ℝ := 2 * c * (A ^ 4 - 6 * A ^ 2 * B ^ 2 + B ^ 4) / 3
  set x : ℝ := -(c * (A ^ 4 - 6 * A ^ 2 * B ^ 2 + B ^ 4)) / 3
  set y : ℝ := 4 * c * A * B * (A ^ 2 - B ^ 2) with hy
  have hy0 : 0 < y := by
    have : 0 < A ^ 2 - B ^ 2 := by nlinarith
    have : 0 < A := by linarith
    positivity
  have hg : H.g₃ = ((4 * r * (x ^ 2 + y ^ 2) : ℝ) : ℂ) := by
    rw [H.g₃_eq_e.1, e1, e2, e3]; push_cast
    linear_combination (-4 * (r : ℂ) * y ^ 2) * I_sq
  refine ⟨by rw [e1, ofReal_im], ?_, by simpa [e2] using hy0, by rw [hg, ofReal_im], ?_, ?_⟩
  · rw [e2, e3]; simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  · intro h3
    have h0 := e_one_eq_zero_of_two_mul_ω₃_eq h3
    exact ⟨h0, by rw [H.g₃_eq_e.1, h0]; ring⟩
  · intro h3
    have hr : r ≠ 0 := by
      intro h0; apply h3; apply two_mul_ω₃_eq_of_e_one_eq_zero h; rw [e1, h0, ofReal_zero]
    rw [e1, hg, ofReal_re, ofReal_re]
    have : 0 < r * r := mul_self_pos.mpr hr
    have : 0 < x ^ 2 + y ^ 2 := by positivity
    nlinarith


/-- Rhombic half-periods `ω₁ = a`, `ω₃ = a/2 + ib` with `a, b > 0`. -/
def rhombic (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : HalfPeriods :=
  ⟨a, a / 2 + b * I, by exact_mod_cast ha.ne', by
    rw [Complex.div_ofReal_im]; simpa using div_pos hb ha⟩

/-- DLMF §23.5(iv): for rhombic lattices with fixed `ω₁`, `e₁` is an increasing function of
`ℑe₃`. -/
@[dlmf 23.5.iv]
theorem rhombic_e_one_monotone (a b₁ b₂ : ℝ) (ha : 0 < a) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (h : ((rhombic a b₁ ha hb₁).e 3).im < ((rhombic a b₂ ha hb₂).e 3).im) :
    ((rhombic a b₁ ha hb₁).e 1).re < ((rhombic a b₂ ha hb₂).e 1).re := by
  sorry

/-- DLMF 23.5.6: for an equianharmonic lattice `η₁ = e^{πi/3}η₃ = π/(2√3 ω₁)`. -/
@[dlmf 23.5.E6]
theorem IsEquianharmonic.eta {H : HalfPeriods} (h : H.IsEquianharmonic) :
    H.eta 1 = cexp (π * I / 3) * H.eta 3 ∧ H.eta 1 = π / (2 * Real.sqrt 3 * H.ω₁) := by
  obtain ⟨-, -, h3⟩ := h
  have hω := H.ω₁_ne_zero
  set ρ := cexp (π * I / 3) with hρ
  have hρ0 : ρ ≠ 0 := Complex.exp_ne_zero _
  have hs : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
  have hρ2 : ρ ^ 2 = ρ - 1 := by
    rw [hρ, exp_pi_I_div_three_eq]; ring_nf; rw [I_sq, hs]; ring
  have hρi : ρ⁻¹ = 1 - ρ := by
    apply inv_eq_of_mul_eq_one_right; linear_combination -hρ2
  have hinv : ∀ z, z ∈ H.lattice ↔ z / ρ ∈ H.lattice := by
    intro z
    simp only [H.mem_lattice_iff, h3]
    constructor
    · rintro ⟨m, n, rfl⟩
      refine ⟨m + n, -m, ?_⟩
      rw [div_eq_mul_inv, hρi]; push_cast; linear_combination (-2 * n * H.ω₁) * hρ2
    · rintro ⟨m, n, hmn⟩
      refine ⟨-n, m + n, ?_⟩
      have : z = ρ * (2 * m * H.ω₁ + 2 * n * (ρ * H.ω₁)) := by rw [← hmn]; field_simp
      rw [this]; push_cast; linear_combination (2 * n * H.ω₁) * hρ2
  have hz := H.weierstrassZeta_mul_of_lattice_invariant ρ hρ0 hinv H.ω₁
  have e3 : H.eta 3 = ρ⁻¹ * H.eta 1 := by
    rw [HalfPeriods.eta, HalfPeriods.eta, halfPeriod_three, halfPeriod_one, h3, hz]
  have hL := H.weierstrassSigma_eq_weierstrassSigmaTheta_and_eta_three.2
  rw [h3, e3, hρi] at hL
  have hsq : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)).ne'
  refine ⟨by rw [e3, ← mul_assoc, mul_inv_cancel₀ hρ0, one_mul], ?_⟩
  have hd : H.eta 1 * (2 * ρ - 1) = π * I / (2 * H.ω₁) := by
    field_simp at hL ⊢; linear_combination hL
  have h2 : 2 * ρ - 1 = Real.sqrt 3 * I := by rw [hρ, exp_pi_I_div_three_eq]; ring
  rw [h2] at hd
  field_simp at hd ⊢
  linear_combination hd

section EquianharmonicValues

open MeasureTheory Set Filter Topology

/-- `Γ(1/2)Γ(1/6)/Γ(2/3) = 3·2^{2/3}Γ(1/3)³/(4π)`. -/
private lemma gamma_half_sixth_div :
    Real.Gamma (1 / 2) * Real.Gamma (1 / 6) / Real.Gamma (2 / 3) =
      3 * (2 : ℝ) ^ (2 / 3 : ℝ) * Real.Gamma (1 / 3) ^ 3 / (4 * π) := by
  have hdup := Real.Gamma_mul_Gamma_add_half (1 / 6)
  have hrefl := Real.Gamma_mul_Gamma_one_sub (1 / 3)
  rw [show (1 : ℝ) / 6 + 1 / 2 = 2 / 3 by norm_num, show (2 : ℝ) * (1 / 6) = 1 / 3 by norm_num,
    show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] at hdup
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, show π * (1 / 3) = π / 3 by ring,
    Real.sin_pi_div_three] at hrefl
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqπ : Real.sqrt π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  have hg23 : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hg13 : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  rw [Real.Gamma_one_half_eq, div_eq_div_iff hg23.ne' (by positivity)]
  have hπ := Real.pi_pos
  have hs3 : 0 < Real.sqrt 3 := by positivity
  -- Γ(2/3) = 2π/(√3 Γ(1/3))
  have hG : Real.Gamma (2 / 3) * (Real.sqrt 3 * Real.Gamma (1 / 3)) = 2 * π := by
    field_simp at hrefl
    linear_combination hrefl
  -- Γ(1/6) = Γ(1/3) 2^{2/3} √π / Γ(2/3)
  have h6 : Real.Gamma (1 / 6) * Real.Gamma (2 / 3) =
      Real.Gamma (1 / 3) * 2 ^ (2 / 3 : ℝ) * Real.sqrt π := hdup
  apply mul_right_cancel₀ hg23.ne'
  linear_combination 4 * π * Real.sqrt π * h6 +
    4 * π * Real.Gamma (1 / 3) * (2 : ℝ) ^ (2 / 3 : ℝ) * hsqπ -
    (2 : ℝ) ^ (2 / 3 : ℝ) * Real.Gamma (1 / 3) *
      (Real.Gamma (2 / 3) * (Real.sqrt 3 * Real.Gamma (1 / 3)) + 2 * π) * hG +
    (2 : ℝ) ^ (2 / 3 : ℝ) * Real.Gamma (1 / 3) ^ 3 * Real.Gamma (2 / 3) ^ 2 * hsq3


/-- `∫₀^∞ y^{-1/2}(1+y)^{-2/3} dy = B(1/2, 1/6)`. -/
private lemma integral_Ioi_rpow_mul_one_add_rpow :
    ∫ y in Ioi (0 : ℝ), y ^ (-(1 / 2) : ℝ) * (1 + y) ^ (-(2 / 3) : ℝ) =
      Real.Gamma (1 / 2) * Real.Gamma (1 / 6) / Real.Gamma (2 / 3) := by
  have h := DLMF.Gamma.beta_on_Ioi (a := 1 / 2) (b := 1 / 6)
  have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := 1 / 2) (t := 1 / 6) (by norm_num)
    (by norm_num)
  have hcongr :
      ∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((1 / 2 : ℂ) - 1) / (1 + (t : ℂ)) ^ ((1 / 2 : ℂ) + 1 / 6)
      = ∫ t : ℝ in Ioi 0, ((t ^ (-(1 / 2) : ℝ) * (1 + t) ^ (-(2 / 3) : ℝ) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) ≤ t := le_of_lt ht
    have h1 : (0 : ℝ) ≤ 1 + t := by linarith
    rw [show (1 / 2 : ℂ) - 1 = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
      show (1 / 2 : ℂ) + 1 / 6 = ((2 / 3 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow ht', show (1 : ℂ) + t = ((1 + t : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow h1, Real.rpow_neg h1, ← div_eq_mul_inv]
    push_cast; ring
  rw [hcongr, integral_complex_ofReal] at h
  have hG : betaIntegral (1 / 2) (1 / 6) =
      ((Real.Gamma (1 / 2) * Real.Gamma (1 / 6) / Real.Gamma (2 / 3) : ℝ) : ℂ) := by
    have hg : Complex.Gamma (1 / 2 + 1 / 6) ≠ 0 := by
      rw [show (1 / 2 + 1 / 6 : ℂ) = ((2 / 3 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
      exact_mod_cast (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3)).ne'
    have hB' : betaIntegral (1 / 2) (1 / 6) =
        Complex.Gamma (1 / 2) * Complex.Gamma (1 / 6) / Complex.Gamma (1 / 2 + 1 / 6) := by
      rw [eq_div_iff hg, mul_comm]; exact hB.symm
    rw [hB']
    rw [show (1 / 2 + 1 / 6 : ℂ) = ((2 / 3 : ℝ) : ℂ) by push_cast; ring,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      show (1 / 6 : ℂ) = ((1 / 6 : ℝ) : ℂ) by push_cast; ring]
    simp only [Complex.Gamma_ofReal]
    push_cast; ring
  rw [hG] at h
  exact_mod_cast h

/-- `∫_c^∞ du/√(u³ - c³) = B(1/2, 1/6)/(3√c)` for `c > 0`. -/
private lemma integral_Ioi_one_div_sqrt_cube_sub {c : ℝ} (hc : 0 < c) :
    ∫ u in Ioi c, 1 / Real.sqrt (u ^ 3 - c ^ 3) =
      1 / (3 * Real.sqrt c) * (Real.Gamma (1 / 2) * Real.Gamma (1 / 6) / Real.Gamma (2 / 3)) := by
  set φ : ℝ → ℝ := fun y => c * (1 + y) ^ ((3 : ℝ)⁻¹) with hφ
  set φ' : ℝ → ℝ := fun y => c * (1 * (3 : ℝ)⁻¹ * (1 + y) ^ ((3 : ℝ)⁻¹ - 1)) with hφ'
  have hcube : ∀ y : ℝ, 0 ≤ 1 + y → ((1 + y) ^ ((3 : ℝ)⁻¹)) ^ 3 = 1 + y := fun y hy => by
    simpa using Real.rpow_inv_natCast_pow hy (n := 3) (by norm_num)
  have hderiv : ∀ y ∈ Ioi (0 : ℝ), HasDerivWithinAt φ (φ' y) (Ioi 0) y := by
    intro y hy
    have hy' : (0 : ℝ) < 1 + y := by have := mem_Ioi.mp hy; linarith
    exact ((((hasDerivAt_id y).const_add 1).rpow_const (Or.inl hy'.ne')).const_mul c)
      |>.hasDerivWithinAt
  have hinj : InjOn φ (Ioi 0) := by
    intro x hx y hy hxy
    have h1 := congrArg (fun w => (w / c) ^ 3) hxy
    simp only [hφ, mul_div_cancel_left₀ _ hc.ne'] at h1
    rw [hcube x (by have := mem_Ioi.mp hx; linarith),
      hcube y (by have := mem_Ioi.mp hy; linarith)] at h1
    linarith
  have himg : φ '' Ioi 0 = Ioi c := by
    ext u
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : 1 < (1 + y) ^ ((3 : ℝ)⁻¹) :=
        Real.one_lt_rpow (by have := mem_Ioi.mp hy; linarith) (by norm_num)
      show c < c * (1 + y) ^ ((3 : ℝ)⁻¹)
      nlinarith
    · intro hu
      have hu' : c < u := hu
      refine ⟨(u / c) ^ 3 - 1, ?_, ?_⟩
      · have : 1 < u / c := (one_lt_div hc).mpr hu'
        show 0 < (u / c) ^ 3 - 1
        nlinarith [one_lt_pow₀ this (by norm_num : (3 : ℕ) ≠ 0)]
      · show c * (1 + ((u / c) ^ 3 - 1)) ^ ((3 : ℝ)⁻¹) = u
        rw [show 1 + ((u / c) ^ 3 - 1) = (u / c) ^ 3 by ring]
        have := Real.pow_rpow_inv_natCast (x := u / c) (n := 3) (div_pos (hc.trans hu') hc).le
          (by norm_num)
        simp only [Nat.cast_ofNat] at this
        rw [this]; field_simp
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj]
  rw [← integral_Ioi_rpow_mul_one_add_rpow, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  have hy1 : (0 : ℝ) < 1 + y := by linarith
  have h3 : φ y ^ 3 - c ^ 3 = c ^ 3 * y := by
    simp only [hφ]; rw [mul_pow, hcube y hy1.le]; ring
  simp only [smul_eq_mul]
  rw [h3, Real.sqrt_mul (by positivity), show c ^ 3 = c ^ 2 * c by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le]
  simp only [hφ']
  rw [show (3 : ℝ)⁻¹ - 1 = -(2 / 3) by norm_num, Real.rpow_neg hy1.le,
    abs_of_pos (by positivity), Real.rpow_neg hy0.le, ← Real.sqrt_eq_rpow]
  have := Real.sqrt_pos.mpr hc
  have := Real.sqrt_pos.mpr hy0
  field_simp


/-- `∫_c^∞ du/√(u³ - c³) = 2^{2/3}Γ(1/3)³/(4π√c)` for `c > 0`. -/
private lemma integral_Ioi_one_div_sqrt_cube_sub_eq {c : ℝ} (hc : 0 < c) :
    ∫ u in Ioi c, 1 / Real.sqrt (u ^ 3 - c ^ 3) =
      (2 : ℝ) ^ (2 / 3 : ℝ) * Real.Gamma (1 / 3) ^ 3 / (4 * π * Real.sqrt c) := by
  rw [integral_Ioi_one_div_sqrt_cube_sub hc, gamma_half_sixth_div]
  have := Real.sqrt_pos.mpr hc
  field_simp

/-- No integer multiple of `c > 0` lies strictly between `0` and `c`. -/
private lemma false_of_eq_int_mul_of_lt {c t : ℝ} (hc : 0 < c) {m : ℤ} (h : t = m * c)
    (h0 : 0 < t) (h1 : t < c) : False := by
  subst h
  have hm0 : (0 : ℝ) < m := by
    by_contra hh; rw [not_lt] at hh; nlinarith
  have hm1 : (m : ℝ) < 1 := by
    by_contra hh; rw [not_lt] at hh; nlinarith
  have : (0 : ℤ) < m := by exact_mod_cast hm0
  have : m < 1 := by exact_mod_cast hm1
  omega

/-- An equianharmonic lattice is invariant under multiplication by `e^{πi/3}`. -/
private lemma mem_lattice_iff_div_rho {H : HalfPeriods} (h3 : H.ω₃ = cexp (π * I / 3) * H.ω₁) :
    ∀ z, z ∈ H.lattice ↔ z / cexp (π * I / 3) ∈ H.lattice := by
  set ρ := cexp (π * I / 3) with hρ
  have hs : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
  have hρ2 : ρ ^ 2 = ρ - 1 := by
    rw [hρ, exp_pi_I_div_three_eq]; ring_nf; rw [I_sq, hs]; ring
  have hρ0 : ρ ≠ 0 := Complex.exp_ne_zero _
  have hρi : ρ⁻¹ = 1 - ρ := by
    apply inv_eq_of_mul_eq_one_right; linear_combination -hρ2
  intro z
  simp only [H.mem_lattice_iff, h3]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨m + n, -m, ?_⟩
    rw [div_eq_mul_inv, hρi]; push_cast; linear_combination (-2 * n * H.ω₁) * hρ2
  · rintro ⟨m, n, hmn⟩
    refine ⟨-n, m + n, ?_⟩
    have : z = ρ * (2 * m * H.ω₁ + 2 * n * (ρ * H.ω₁)) := by rw [← hmn]; field_simp
    rw [this]; push_cast; linear_combination (2 * n * H.ω₁) * hρ2

/-- For an equianharmonic lattice, `e₃ = -ρe₁` and `e₂ = (ρ - 1)e₁` with `ρ = e^{πi/3}`. -/
private lemma equianharmonic_e {H : HalfPeriods} (h3 : H.ω₃ = cexp (π * I / 3) * H.ω₁) :
    H.e 3 = -cexp (π * I / 3) * H.e 1 ∧ H.e 2 = (cexp (π * I / 3) - 1) * H.e 1 := by
  set ρ := cexp (π * I / 3) with hρ
  have hs : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
  have hρ2 : ρ ^ 2 = ρ - 1 := by
    rw [hρ, exp_pi_I_div_three_eq]; ring_nf; rw [I_sq, hs]; ring
  have hρ0 : ρ ≠ 0 := Complex.exp_ne_zero _
  have hρi : ρ⁻¹ = 1 - ρ := by
    apply inv_eq_of_mul_eq_one_right; linear_combination -hρ2
  have hp := H.weierstrassP_mul_of_lattice_invariant ρ hρ0 (mem_lattice_iff_div_rho h3)
  have e3 : H.e 3 = ρ⁻¹ ^ 2 * H.e 1 := by
    rw [HalfPeriods.e, HalfPeriods.e, HalfPeriods.halfPeriod_three, HalfPeriods.halfPeriod_one,
      h3, hp]
  have e2 : H.e 2 = ρ⁻¹ ^ 2 * H.e 3 := by
    have h1 := hp (ρ * H.ω₁)
    have hper : H.weierstrassP (ρ * (ρ * H.ω₁)) = H.weierstrassP H.ω₂ := by
      have hz : ρ * (ρ * H.ω₁) = -H.ω₂ - 2 * H.halfPeriod 1 := by
        rw [HalfPeriods.halfPeriod_one, HalfPeriods.ω₂, h3]; linear_combination H.ω₁ * hρ2
      have := H.weierstrassP_add_two_mul_halfPeriod (-H.ω₂ - 2 * H.halfPeriod 1) (j := 1)
        (by simp)
      rw [hz, ← this, show -H.ω₂ - 2 * H.halfPeriod 1 + 2 * H.halfPeriod 1 = -H.ω₂ by ring]
      exact H.periodPair.weierstrassP_neg H.ω₂
    have : H.e 3 = H.weierstrassP (ρ * H.ω₁) := by
      rw [HalfPeriods.e, HalfPeriods.halfPeriod_three, h3]
    rw [this, ← h1, hper]; rfl
  have hsq : ρ⁻¹ ^ 2 = -ρ := by rw [hρi]; linear_combination hρ2
  rw [hsq] at e2 e3
  refine ⟨e3, ?_⟩
  rw [e2, e3]; linear_combination (H.e 1) * hρ2

/-- DLMF 23.5.7: for an equianharmonic lattice
`e₁ = e^{2πi/3}e₃ = e^{-2πi/3}e₂ = Γ(1/3)⁶/(2^{14/3}π²ω₁²)`. -/
@[dlmf 23.5.E7]
theorem IsEquianharmonic.roots {H : HalfPeriods} (h : H.IsEquianharmonic) :
    H.e 1 = cexp (2 * π * I / 3) * H.e 3 ∧ H.e 1 = cexp (-(2 * π * I / 3)) * H.e 2 ∧
      H.e 1 = (Real.Gamma (1 / 3) : ℂ) ^ 6 / ((2 : ℂ) ^ (14 / 3 : ℂ) * π ^ 2 * H.ω₁ ^ 2) := by
  obtain ⟨h1im, h1re, h3⟩ := h
  obtain ⟨e3, e2⟩ := equianharmonic_e h3
  set ρ := cexp (π * I / 3) with hρ
  have hs : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
  have hρ2 : ρ ^ 2 = ρ - 1 := by
    rw [hρ, exp_pi_I_div_three_eq]; ring_nf; rw [I_sq, hs]; ring
  have hρ0 : ρ ≠ 0 := Complex.exp_ne_zero _
  have hA : cexp (2 * π * I / 3) = ρ ^ 2 := by
    rw [hρ, ← Complex.exp_nat_mul]; push_cast; ring_nf
  have hB : cexp (-(2 * π * I / 3)) = -ρ := by
    have h1 : cexp (-(2 * π * I / 3)) * ρ ^ 2 = 1 := by
      rw [← hA, ← Complex.exp_add]; simp
    have h2 : ρ ^ 2 * (-ρ) = 1 := by linear_combination (-(ρ + 1)) * hρ2
    exact mul_right_cancel₀ (pow_ne_zero 2 hρ0) (by rw [h1]; linear_combination -h2)
  refine ⟨by rw [hA, e3]; linear_combination (H.e 1 * (ρ + 1)) * hρ2,
    by rw [hB, e2]; linear_combination (H.e 1) * hρ2, ?_⟩
  -- the real half-period `a`
  set a := H.ω₁.re with ha_def
  have ha : 0 < a := h1re
  have hω₁ : H.ω₁ = (a : ℂ) := Complex.ext rfl (by simp [h1im])
  have hρv : ρ = (1 + Real.sqrt 3 * I) / 2 := by rw [hρ]; exact exp_pi_I_div_three_eq
  have hs3 : 0 < Real.sqrt 3 := by positivity
  -- lattice coordinates
  have hcoord : ∀ z ∈ H.lattice, ∃ n : ℤ, z.im = n * (a * Real.sqrt 3) ∧
      (z.im = 0 → ∃ m : ℤ, z.re = m * (2 * a)) := by
    intro z hz
    obtain ⟨m, n, rfl⟩ := H.mem_lattice_iff.mp hz
    rw [h3, hω₁, hρv]
    refine ⟨n, by simp; ring, fun h0 => ⟨m, ?_⟩⟩
    have hn0 : (n : ℝ) = 0 := by
      simp at h0
      rcases h0 with h | h
      · simp [h]
      · exact absurd h ha.ne'
    simp [hn0]; ring
  have hinv : ∀ z, z ∈ H.periodPair.lattice → (starRingEnd ℂ) z ∈ H.periodPair.lattice := by
    intro z hz
    obtain ⟨m, n, rfl⟩ := H.mem_lattice_iff.mp hz
    refine H.mem_lattice_iff.mpr ⟨m + n, -n, ?_⟩
    have hcρ : (starRingEnd ℂ) ρ = 1 - ρ := by
      rw [hρv, map_div₀, map_add, map_one, map_mul, conj_ofReal, conj_I, map_ofNat]; ring
    rw [h3, hω₁]
    simp only [map_add, map_mul, conj_ofReal, map_intCast, map_ofNat, hcρ]
    push_cast; ring
  have hR : ∀ t : ℝ, (H.weierstrassP (t : ℂ)).im = 0 := fun t =>
    weierstrassP_im_eq_zero_of_conj hinv (zero_mem _) (Or.inl (by simp))
  have hnotR : ∀ t : ℝ, 0 < t → t < 2 * a → (t : ℂ) ∉ H.lattice := by
    intro t ht0 ht1 hm
    obtain ⟨-, -, hm⟩ := hcoord _ hm
    obtain ⟨m, hm⟩ := hm (by simp)
    have hm' : t = m * (2 * a) := by simpa using hm
    exact false_of_eq_int_mul_of_lt (by linarith) hm' ht0 ht1
  set f : ℝ → ℝ := fun s => (H.weierstrassP (s : ℂ)).re with hf
  have hL : ∀ t ∈ Ioo 0 a, (t : ℂ) ∉ H.lattice ∧ 2 * (t : ℂ) ∉ H.lattice := fun t ht =>
    ⟨hnotR t ht.1 (by linarith [ht.2]), by
      have := hnotR (2 * t) (by linarith [ht.1]) (by linarith [ht.2])
      push_cast at this; exact this⟩
  have hγ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := fun t => by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hPF : ∀ t ∈ Ioo 0 a, HasDerivAt f (H.derivWeierstrassP (t : ℂ) * 1).re t ∧
      (H.derivWeierstrassP (t : ℂ) * 1).re ≠ 0 ∧
      |(H.derivWeierstrassP (t : ℂ) * 1).re| = 2 * Real.sqrt
        ‖(H.weierstrassP (t : ℂ) - H.e 1) * (H.weierstrassP (t : ℂ) - H.e 2) *
          (H.weierstrassP (t : ℂ) - H.e 3)‖ :=
    fun t ht => H.hasDerivAt_re_weierstrassP_comp (by simp) hγ hL (fun t _ => hR t) ht
  have hcont : ∀ t ∈ Ioc 0 a, ContinuousAt f t := fun t ht =>
    H.continuousAt_re_weierstrassP_comp hγ (hnotR t ht.1 (by linarith [ht.2]))
  obtain ⟨hSA, himg⟩ := strictAntiOn_Ioc_of_tendsto_atTop (c := a) hcont
    (fun t ht => (hPF t ht).1) (fun t ht => (hPF t ht).2.1)
    (tendsto_re_weierstrassP_ofReal_nhdsGT_zero H.periodPair)
  set c := (H.e 1).re with hc_def
  have he1 : H.e 1 = (c : ℂ) := by
    refine Complex.ext rfl ?_
    have := hR a
    simpa [HalfPeriods.e, hω₁] using this
  have hfa : f a = c := by simp [hf, hc_def, HalfPeriods.e, hω₁]
  have hc0 : c ≠ 0 := by
    intro h0
    obtain ⟨-, -, d13⟩ := H.e_distinct
    apply d13; rw [e3, he1, h0]; simp
  have himρ : ∀ t : ℝ, (ρ * (t : ℂ)).im = Real.sqrt 3 / 2 * t := fun t => by
    rw [hρv]; simp
  have hcpos : 0 < c := by
    by_contra hneg
    have hneg' : c < 0 := lt_of_le_of_ne (not_lt.mp hneg) hc0
    have h0 : (0 : ℝ) ∈ f '' Ioo 0 a := by rw [himg a ⟨ha, le_rfl⟩, hfa]; exact hneg'
    obtain ⟨t0, ht0, hft0⟩ := h0
    have hP0 : H.weierstrassP (t0 : ℂ) = 0 := Complex.ext hft0 (hR t0)
    have hnt0 : (t0 : ℂ) ∉ H.lattice := (hL t0 ht0).1
    -- a lattice point with imaginary part `±(√3/2) t0` is impossible
    have himpos : ∀ z ∈ H.lattice, z.im = Real.sqrt 3 / 2 * t0 ∨
        z.im = -(Real.sqrt 3 / 2 * t0) → False := by
      intro z hz hzim
      obtain ⟨n, hn, -⟩ := hcoord z hz
      rcases hzim with h | h
      · have : Real.sqrt 3 * t0 = Real.sqrt 3 * (n * (2 * a)) := by linarith
        exact false_of_eq_int_mul_of_lt (by linarith) (mul_left_cancel₀ hs3.ne' this) ht0.1
          (by linarith [ht0.2])
      · have : Real.sqrt 3 * t0 = Real.sqrt 3 * (((-n : ℤ) : ℝ) * (2 * a)) := by
          push_cast; linarith
        exact false_of_eq_int_mul_of_lt (by linarith) (mul_left_cancel₀ hs3.ne' this) ht0.1
          (by linarith [ht0.2])
    have hnρ : ρ * (t0 : ℂ) ∉ H.lattice := fun hm => himpos _ hm (Or.inl (himρ t0))
    have hp := H.weierstrassP_mul_of_lattice_invariant ρ hρ0 (mem_lattice_iff_div_rho h3) t0
    rw [hP0, mul_zero] at hp
    have hσ := weierstrassSigma_add_mul_sub H.periodPair hnt0 hnρ
    have hσ0 : DLMF.Weierstrass.weierstrassSigma H.periodPair (t0 + ρ * t0) *
        DLMF.Weierstrass.weierstrassSigma H.periodPair (t0 - ρ * t0) = 0 := by
      have hd : DLMF.Weierstrass.weierstrassSigma H.periodPair t0 ^ 2 *
          DLMF.Weierstrass.weierstrassSigma H.periodPair (ρ * t0) ^ 2 ≠ 0 := by
        have h1 := (DLMF.Weierstrass.weierstrassSigma_eq_zero_iff H.periodPair).not.mpr hnt0
        have h2 := (DLMF.Weierstrass.weierstrassSigma_eq_zero_iff H.periodPair).not.mpr hnρ
        exact mul_ne_zero (pow_ne_zero 2 h1) (pow_ne_zero 2 h2)
      have : ℘[H.periodPair] (ρ * t0) - ℘[H.periodPair] t0 = 0 := by
        change H.weierstrassP (ρ * t0) - H.weierstrassP t0 = 0
        rw [hp, hP0, sub_zero]
      rw [this, div_eq_zero_iff] at hσ
      exact hσ.resolve_right hd
    rcases mul_eq_zero.mp hσ0 with h | h
    · refine himpos _ ((DLMF.Weierstrass.weierstrassSigma_eq_zero_iff H.periodPair).mp h)
        (Or.inl ?_)
      rw [add_im, himρ]; simp
    · refine himpos _ ((DLMF.Weierstrass.weierstrassSigma_eq_zero_iff H.periodPair).mp h)
        (Or.inr ?_)
      rw [sub_im, himρ]; simp
  have hlt : ∀ t ∈ Ioo 0 a, c < f t := fun t ht => by
    have := hSA ⟨ht.1, ht.2.le⟩ ⟨ha, le_rfl⟩ ht.2
    rwa [hfa] at this
  have key := integral_image_one_div_sqrt (s := Ioo 0 a) measurableSet_Ioo (f := f)
    (f' := fun t => (H.derivWeierstrassP (t : ℂ) * 1).re) (Q := fun u => u ^ 3 - c ^ 3)
    (fun t (ht : t ∈ Ioo 0 a) => (hPF t ht).1.hasDerivWithinAt)
    (hSA.injOn.mono Ioo_subset_Ioc_self)
    (fun t (ht : t ∈ Ioo 0 a) =>
      sub_pos.mpr (pow_lt_pow_left₀ (hlt t ht) hcpos.le (by norm_num)))
    (fun t (ht : t ∈ Ioo 0 a) => by
      rw [(hPF t ht).2.2]
      have hPr : H.weierstrassP (t : ℂ) = (f t : ℂ) := Complex.ext rfl (by simp [hR t])
      rw [hPr, e2, e3, he1,
        show ((f t : ℂ) - c) * (f t - (ρ - 1) * c) * (f t - -ρ * c) = ((f t ^ 3 - c ^ 3 : ℝ) : ℂ) by
          push_cast; linear_combination (-((f t : ℂ) - c) * (c : ℂ) ^ 2) * hρ2,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (sub_pos.mpr (pow_lt_pow_left₀ (hlt t ht) hcpos.le (by norm_num)))])
  rw [himg a ⟨ha, le_rfl⟩, hfa, Real.volume_real_Ioo_of_le ha.le,
    integral_Ioi_one_div_sqrt_cube_sub_eq hcpos] at key
  -- algebra
  set p : ℝ := (2 : ℝ) ^ (2 / 3 : ℝ) with hp
  have hp3 : p ^ 3 = 4 := by
    rw [hp, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hppos : 0 < p := by positivity
  have h214 : (2 : ℂ) ^ (14 / 3 : ℂ) = ((16 * p : ℝ) : ℂ) := by
    rw [show (14 / 3 : ℂ) = ((14 / 3 : ℝ) : ℂ) by push_cast; ring,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2),
      show (14 / 3 : ℝ) = 4 + 2 / 3 by norm_num,
      Real.rpow_add (by norm_num), hp]
    norm_num
  rw [he1, hω₁, h214]
  have hsc := Real.sq_sqrt hcpos.le
  have hsc0 := Real.sqrt_pos.mpr hcpos
  have hG := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)
  have hreal : c = Real.Gamma (1 / 3) ^ 6 / (16 * p * π ^ 2 * a ^ 2) := by
    rw [eq_div_iff (by positivity)]
    have k2 : p * Real.Gamma (1 / 3) ^ 3 = 8 * π * a * Real.sqrt c := by
      field_simp at key; linarith
    apply mul_left_cancel₀ (pow_ne_zero 2 hppos.ne')
    linear_combination (16 * π ^ 2 * a ^ 2 * c) * hp3 - (64 * π ^ 2 * a ^ 2) * hsc -
      (p * Real.Gamma (1 / 3) ^ 3 + 8 * π * a * Real.sqrt c) * k2
  rw [hreal]
  push_cast
  ring

/-- DLMF 23.5.8: for an equianharmonic lattice `g₂ = 0` and `g₃ = Γ(1/3)¹⁸/(4πω₁)⁶`. -/
@[dlmf 23.5.E8]
theorem IsEquianharmonic.invariants {H : HalfPeriods} (h : H.IsEquianharmonic) :
    H.g₂ = 0 ∧ H.g₃ = (Real.Gamma (1 / 3) : ℂ) ^ 18 / (4 * π * H.ω₁) ^ 6 := by
  obtain ⟨-, -, hv⟩ := h.roots
  obtain ⟨e3, e2⟩ := equianharmonic_e h.2.2
  set ρ := cexp (π * I / 3) with hρ
  have hs : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
  have hρ2 : ρ ^ 2 = ρ - 1 := by
    rw [hρ, exp_pi_I_div_three_eq]; ring_nf; rw [I_sq, hs]; ring
  refine ⟨by rw [H.g₂_eq_e.2, e2, e3]; linear_combination (4 * H.e 1 ^ 2) * hρ2, ?_⟩
  have h2 : ((2 : ℂ) ^ (14 / 3 : ℂ)) ^ 3 = 2 ^ 14 := by
    rw [← Complex.cpow_nat_mul, show ((3 : ℕ) : ℂ) * (14 / 3) = ((14 : ℕ) : ℂ) by push_cast; ring,
      Complex.cpow_natCast]
  have h4 : 4 * H.e 1 * ((ρ - 1) * H.e 1) * (-ρ * H.e 1) = 4 * H.e 1 ^ 3 := by
    linear_combination (-4 * H.e 1 ^ 3) * hρ2
  have hω := H.ω₁_ne_zero
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [H.g₃_eq_e.1, e2, e3, h4, hv, div_pow, mul_pow, mul_pow, h2]
  field_simp
  ring

end EquianharmonicValues

/-- DLMF §23.5(v): for an equianharmonic lattice `τ = e^{iπ/3}`. -/
@[dlmf 23.5.v]
theorem IsEquianharmonic.tau {H : HalfPeriods} (h : H.IsEquianharmonic) :
    H.tau = cexp (π * I / 3) := by
  rw [HalfPeriods.tau, h.2.2, mul_div_assoc, div_self H.ω₁_ne_zero, mul_one]

/-- DLMF 23.5.9: for an equianharmonic lattice the modulus of 23.6.16 satisfies
`k² = (e₂ - e₃)/(e₁ - e₃) = e^{iπ/3}`. -/
@[dlmf 23.5.E9]
theorem IsEquianharmonic.modulus_sq {H : HalfPeriods} (h : H.IsEquianharmonic) :
    (H.e 2 - H.e 3) / (H.e 1 - H.e 3) = cexp (π * I / 3) := by
  obtain ⟨h13, h12, hv⟩ := h.roots
  set x := cexp (π * I / 3) with hx
  have hx3 : x ^ 3 = -1 := by
    rw [hx, ← Complex.exp_nat_mul]; push_cast
    rw [show (3 : ℂ) * (π * I / 3) = π * I by ring, Complex.exp_pi_mul_I]
  have hxre : x.re = 1 / 2 := by
    rw [hx, show (π : ℂ) * I / 3 = ((π / 3 : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]
  have hx1 : 1 + x ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [hxre] at this
    norm_num at this
  have hx0 : x ≠ 0 := Complex.exp_ne_zero _
  have hA : cexp (2 * π * I / 3) = x ^ 2 := by
    rw [hx, ← Complex.exp_nat_mul]; push_cast; ring_nf
  have hB : cexp (-(2 * π * I / 3)) = -x := by
    have : cexp (-(2 * π * I / 3)) * x ^ 2 = 1 := by
      rw [← hA, ← Complex.exp_add]; simp
    have h2 : x ^ 2 * (-x) = 1 := by linear_combination -hx3
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
    exact mul_right_cancel₀ hx2 (by rw [this]; linear_combination -h2)
  rw [hA] at h13
  rw [hB] at h12
  have he1 : H.e 1 ≠ 0 := by
    rw [hv]
    have hg : (Real.Gamma (1 / 3) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)).ne'
    have := H.ω₁_ne_zero
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : (2 : ℂ) ^ (14 / 3 : ℂ) ≠ 0 := by simp
    have hω := H.ω₁_ne_zero
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 : ℂ) ^ (14 / 3 : ℂ) ≠ 0 := by simp
    exact div_ne_zero (pow_ne_zero 6 hg) (mul_ne_zero (mul_ne_zero h2 (pow_ne_zero 2 hπ))
      (pow_ne_zero 2 hω))
  -- `e₂ = x² e₁` and `e₃ = -x e₁`.
  have he2 : H.e 2 = x ^ 2 * H.e 1 := by
    have : (-x) * (x ^ 2 * H.e 1) = H.e 1 := by linear_combination (-(H.e 1)) * hx3
    have hnx : -x ≠ 0 := neg_ne_zero.mpr hx0
    exact mul_left_cancel₀ hnx (by rw [this, ← h12])
  have he3 : H.e 3 = -x * H.e 1 := by
    have : x ^ 2 * (-x * H.e 1) = H.e 1 := by linear_combination (-(H.e 1)) * hx3
    exact mul_left_cancel₀ (pow_ne_zero 2 hx0) (by rw [this, ← h13])
  have hden : H.e 1 - -x * H.e 1 ≠ 0 := by
    rw [show H.e 1 - -x * H.e 1 = (1 + x) * H.e 1 by ring]
    exact mul_ne_zero hx1 he1
  rw [he2, he3, div_eq_iff hden]
  ring

open scoped ComplexConjugate in
open MeasureTheory Set in
/-- DLMF 23.5.9: for `k = e^{iπ/6}` (so `k² = e^{iπ/3}`),
`K(k) = e^{iπ/6}K'(k) = e^{iπ/12} 3^{1/4} Γ(1/3)³/(2^{7/3}π)`, with the principal complex
complete elliptic integrals. -/
@[dlmf 23.5.E9]
theorem completeEllipticK_equianharmonic :
    EllipticIntegrals.completeEllipticK (cexp (π * I / 6)) =
        cexp (π * I / 6) * EllipticIntegrals.completeEllipticKPrime (cexp (π * I / 6)) ∧
      EllipticIntegrals.completeEllipticK (cexp (π * I / 6)) =
        cexp (π * I / 12) * (3 : ℂ) ^ (1 / 4 : ℂ) * (Real.Gamma (1 / 3) : ℂ) ^ 3 /
          ((2 : ℂ) ^ (7 / 3 : ℂ) * π) := by
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3lt : √3 < 2 := by nlinarith [Real.sqrt_nonneg 3]
  have hs3c : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by rw [← ofReal_pow, hs3]; norm_num
  set s := √((2 - √3) / 4) with hs
  set c := √((2 + √3) / 4) with hc
  have hs2 : s ^ 2 = (2 - √3) / 4 := Real.sq_sqrt (by linarith)
  have hc2 : c ^ 2 = (2 + √3) / 4 := Real.sq_sqrt (by positivity)
  have hc0 : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hsc : s = (2 - √3) * c := by
    have h1 : 0 ≤ (2 - √3) * c := mul_nonneg (by linarith) hc0.le
    rw [← Real.sqrt_sq h1, ← Real.sqrt_sq hs0.le, mul_pow, hc2, hs2]
    congr 1; nlinarith
  have hk12 : cexp (π * I / 12) = c + s * I := exp_pi_mul_I_div_twelve
  obtain ⟨hk, hL, hKp⟩ := completeEllipticK_exp_pi_mul_I_div_six
  have hcs : (1 : ℝ) - s ^ 2 = c ^ 2 := by rw [hs2, hc2]; ring
  have hslit_s : 1 - (s : ℂ) ^ 2 ∈ slitPlane := by
    rw [← ofReal_pow, ← ofReal_one, ← ofReal_sub, hcs]
    exact ofReal_mem_slitPlane.2 (by positivity)
  have hkps : jacobiComodulus (s : ℂ) = c := by
    rw [jacobiComodulus, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_pow, ← ofReal_one, ← ofReal_sub, hcs, ← ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq hc0.le]
  obtain ⟨hI, -⟩ := EllipticIntegrals.compEllInt_imaginary_modulus hslit_s
  rw [hkps, show I * (s : ℂ) / c = I * (2 - √3) by
    have : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    rw [hsc]; push_cast; field_simp] at hI
  have hV : ∫ t in Ioi (1 : ℝ), (√(t ^ 3 - 1))⁻¹ =
      (2 : ℝ) ^ (2 / 3 : ℝ) * Real.Gamma (1 / 3) ^ 3 / (4 * π) := by
    have := integral_Ioi_one_div_sqrt_cube_sub_eq (c := 1) one_pos
    simpa [one_div] using this
  have hint : IntegrableOn (fun t : ℝ => (√(t ^ 3 - 1))⁻¹) (Ioi 1) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [hV]; have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3); positivity
  have hKs := completeEllipticK_singular_three_eq_integral hint
  rw [hV] at hKs
  set R : ℝ := (3 : ℝ) ^ (1 / 4 : ℝ) / 2 * ((2 : ℝ) ^ (2 / 3 : ℝ) * Real.Gamma (1 / 3) ^ 3 /
    (4 * π)) with hR
  have hK : completeEllipticK (cexp (π * I / 6)) = (1 + I * (2 - √3)) * ((c * R : ℝ) : ℂ) := by
    rw [hL, hI, hKs]; push_cast; ring
  have hc12 : cexp (π * I / 12) = (1 + I * (2 - √3)) * c := by rw [hk12, hsc]; push_cast; ring
  have h3 : (3 : ℂ) ^ (1 / 4 : ℂ) = (((3 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow (by norm_num)]; push_cast; ring
  have h2 : (2 : ℂ) ^ (7 / 3 : ℂ) = (((2 : ℝ) ^ (7 / 3 : ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow (by norm_num)]; push_cast; ring
  have h27 : (2 : ℝ) ^ (2 / 3 : ℝ) * (2 : ℝ) ^ (7 / 3 : ℝ) = 8 := by
    rw [← Real.rpow_add (by norm_num), show (2 / 3 : ℝ) + 7 / 3 = (3 : ℕ) by norm_num,
      Real.rpow_natCast]; norm_num
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (7 / 3 : ℝ) := by positivity
  refine ⟨?_, ?_⟩
  · rw [hKp, hK, hk]
    simp only [map_mul, map_add, map_one, map_sub, conj_I, conj_ofReal, map_ofNat]
    push_cast
    linear_combination ((1 - √3 / 2) * ((c : ℂ) * R)) * I_sq - (I / 2 * ((c : ℂ) * R)) * hs3c
  · have hRv : R = (3 : ℝ) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 3) ^ 3 /
        ((2 : ℝ) ^ (7 / 3 : ℝ) * π) := by
      rw [hR]
      field_simp
      rw [h27]; norm_num
    rw [hK, hc12, h3, h2, hRv]; push_cast; ring

end HalfPeriods

end DLMF.Weierstrass
