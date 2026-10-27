/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Weierstrass.Relations
public import DLMF.Elliptic.SpecialValues

/-!
# Real-valued Weierstrass functions and special lattices (DLMF §23.5)

Rectangular, lemniscatic, rhombic and equianharmonic lattices are described by predicates on
DLMF half-periods. Real numbers are complex numbers with vanishing imaginary part, and order
statements are made for real parts. The complete elliptic integral of 23.5.5 is the project's
real `DLMF.Elliptic.Real.compEllIntKm` with parameter `m = k² = 1/2`; the complex values in
23.5.9 use the principal complex integral `DLMF.JacobiElliptic.compEllIntKk` (modulus form) of the
Chapter 22 acquisition, and the modulus `k = e^{iπ/6}` with `k² = e^{iπ/3}`.
-/

@[expose] public section

open Complex PeriodPair DLMF.JacobiElliptic
open scoped Real

noncomputable section

namespace DLMF.Weierstrass

section p3wConj

open Filter Topology
open scoped ComplexConjugate

/-- The complex-conjugate period pair `(ω̄₁, ω̄₂)`. -/
def p3w_conjPair (L : PeriodPair) : PeriodPair :=
  ⟨conj L.ω₁, conj L.ω₂, by
    have h := L.indep.map' Complex.conjLIE.toLinearEquiv.toLinearMap
      (LinearEquiv.ker _)
    convert h using 1
    funext i; fin_cases i <;> rfl⟩

/-- Membership in the conjugate lattice. -/
lemma p3w_mem_conjPair (L : PeriodPair) {z : ℂ} :
    z ∈ (p3w_conjPair L).lattice ↔ conj z ∈ L.lattice := by
  simp only [PeriodPair.mem_lattice, p3w_conjPair]
  constructor
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by simp⟩
  · rintro ⟨m, n, h⟩
    refine ⟨m, n, ?_⟩
    have := congrArg conj h
    simp only [map_add, map_mul, map_intCast, conj_conj] at this
    exact this

/-- Conjugation as a bijection `𝕃 ≃ 𝕃̄`. -/
def p3w_conjEquiv (L : PeriodPair) : L.lattice ≃ (p3w_conjPair L).lattice where
  toFun l := ⟨conj (l : ℂ), (p3w_mem_conjPair L).mpr (by simp)⟩
  invFun l := ⟨conj (l : ℂ), (p3w_mem_conjPair L).mp l.2⟩
  left_inv l := by ext; simp
  right_inv l := by ext; simp

/-- `℘(z|𝕃̄) = conj ℘(z̄|𝕃)`. -/
lemma p3w_weierstrassP_conjPair (L : PeriodPair) (z : ℂ) :
    ℘[p3w_conjPair L] z = conj (℘[L] (conj z)) := by
  simp only [PeriodPair.weierstrassP]
  rw [← (p3w_conjEquiv L).tsum_eq, Complex.conj_tsum]
  refine tsum_congr fun l => ?_
  simp [p3w_conjEquiv, map_sub]

/-- `G_n(𝕃̄) = conj G_n(𝕃)`. -/
lemma p3w_G_conjPair (L : PeriodPair) (n : ℕ) :
    (p3w_conjPair L).G n = conj (L.G n) := by
  simp only [PeriodPair.G]
  rw [← (p3w_conjEquiv L).tsum_eq, Complex.conj_tsum]
  refine tsum_congr fun l => ?_
  simp [p3w_conjEquiv]

/-- The conjugate lattice is the image of the lattice under conjugation. -/
lemma p3w_conjPair_lattice (L : PeriodPair) :
    ((p3w_conjPair L).lattice : Set ℂ) = (starRingEnd ℂ) '' (L.lattice : Set ℂ) := by
  ext z
  simp only [SetLike.mem_coe, Set.mem_image, p3w_mem_conjPair]
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
  set L' := p3w_conjPair L with hL'
  have hc : (starRingEnd ℂ) '' (L.lattice : Set ℂ) = L.lattice ↔ L'.lattice = L.lattice := by
    rw [← p3w_conjPair_lattice, SetLike.coe_set_eq]
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
        rw [hL', p3w_weierstrassP_conjPair, Complex.conj_ofReal, (hreal _).mpr him]
      simp [this]
    rcases (hpa.sub hqa).eventually_eq_or_eventually_ne (analyticAt_const (v := (0 : ℂ))) with
      hev | hne
    · have hev' : ∀ᶠ z in 𝓝 (0 : ℂ), ℘[L] z = ℘[L'] z := hev.mono fun z hz => by
        simp only [Pi.sub_apply] at hz; linear_combination hz
      exact le_antisymm (p3w_lattice_le_of_eventuallyEq L' L
        (hev'.mono fun z hz => hz.symm)) (p3w_lattice_le_of_eventuallyEq L L' hev')
    · exfalso
      have := (hR.eventually hne).and heqR
      obtain ⟨t, ht1, ht2⟩ := this.exists
      exact ht1 ht2
  · have e := wp23_weierstrassP_eq_of_lattice_eq L' L h (x : ℂ)
    rw [hL', p3w_weierstrassP_conjPair, Complex.conj_ofReal] at e
    exact (hreal _).mp e
  · have h4 := wp23_G_eq_of_lattice_eq L' L h 4
    have h6 := wp23_G_eq_of_lattice_eq L' L h 6
    rw [hL', p3w_G_conjPair] at h4 h6
    have r4 := (hreal _).mp h4
    have r6 := (hreal _).mp h6
    simp [PeriodPair.g₂, PeriodPair.g₃, r4, r6]
  · refine lattice_eq_of_invariants_eq L' L ?_ ?_
    · rw [hL', PeriodPair.g₂, p3w_G_conjPair, ← map_ofNat (starRingEnd ℂ) 60, ← map_mul]
      exact (hreal _).mpr h2
    · rw [hL', PeriodPair.g₃, p3w_G_conjPair, ← map_ofNat (starRingEnd ℂ) 140, ← map_mul]
      exact (hreal _).mpr h3


/-- A lattice invariant under conjugation has `℘(z̄) = conj ℘(z)`. -/
lemma p3w_weierstrassP_conj_of_inv (L : PeriodPair)
    (hinv : ∀ z, z ∈ L.lattice → conj z ∈ L.lattice) (z : ℂ) :
    ℘[L] (conj z) = conj (℘[L] z) := by
  have hl : (p3w_conjPair L).lattice = L.lattice := by
    ext w
    rw [p3w_mem_conjPair]
    exact ⟨fun h => by simpa using hinv _ h, hinv w⟩
  have := p3w_weierstrassP_conjPair L (conj z)
  rw [wp23_weierstrassP_eq_of_lattice_eq _ _ hl, conj_conj] at this
  exact this

end p3wConj

namespace HalfPeriods

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
theorem p23R1_rect_data {H : HalfPeriods} (h : H.IsRectangular) :
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
  have hB := p22R1_B_ge ht
  have hC := p22R1_C_pos ht
  have hA := p22R1_A_pos ht
  have h2 : jacobiThetaTwoTau 0 H.tau = (p22R1_A t : ℂ) := by rw [hτ, p22R1_two ht]; rfl
  have h3 : jacobiThetaThreeTau 0 H.tau = (p22R1_B t : ℂ) := by rw [hτ, p22R1_three]
  have h4 : jacobiThetaFourTau 0 H.tau = (p22R1_C t : ℂ) := by rw [hτ, p22R1_four]
  obtain ⟨d3, d2⟩ := H.p23R1_e_diff
  have hs := H.e_sum
  set c : ℝ := (π / (2 * a)) ^ 2 with hc
  have hcc : (π / (2 * H.ω₁)) ^ 2 = (c : ℂ) := by rw [hc, hω1]; push_cast; ring
  rw [hcc, h3] at d3
  rw [hcc, h4] at d2
  have hB0 : (p22R1_B t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  refine ⟨a, c, p22R1_A t, p22R1_B t, p22R1_C t, h1r, hω1, rfl, by positivity, hA, hB, hC,
    p22R1_fourth ht, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · push_cast; linear_combination (d3 + d2 + hs) / 3
  · push_cast; linear_combination (d3 - 2 * d2 + hs) / 3
  · push_cast; linear_combination (-2 * d3 + d2 + hs) / 3
  · rw [HalfPeriods.quarterK, compEllIntKTau, h3]; push_cast; ring
  · rw [HalfPeriods.modulus, jacobiModulusTau, h2, h3]; push_cast; ring
  · rw [HalfPeriods.comodulus, jacobiComodulusTau, h4, h3]; push_cast; ring

/-- DLMF §23.5(ii): for a rectangular lattice `Δ > 0`. -/
@[dlmf 23.5.ii]
theorem IsRectangular.discriminant_pos {H : HalfPeriods} (h : H.IsRectangular) :
    (latticeDiscriminant H.periodPair).im = 0 ∧ 0 < (latticeDiscriminant H.periodPair).re := by
  obtain ⟨a, c, A, B, C, -, -, -, hc, hA, hB, hC, hJ, e1, e2, e3, -⟩ := p23R1_rect_data h
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
  obtain ⟨a, c, A, B, C, -, -, -, hc, hA, hB, hC, hJ, e1, e2, e3, -⟩ := p23R1_rect_data h
  rw [e1, e2, e3]
  simp only [ofReal_im, ofReal_re, true_and]
  have hA4 : 0 < A ^ 4 := by positivity
  have hC4 : 0 < C ^ 4 := by positivity
  refine ⟨by nlinarith, by nlinarith, by positivity, by nlinarith⟩

/-- DLMF §23.5(ii): for a rectangular lattice `e₂` and `g₃` have opposite signs unless
`ω₃ = iω₁`, in which case both vanish. -/
@[dlmf 23.5.ii]
theorem IsRectangular.e_two_g₃ {H : HalfPeriods} (h : H.IsRectangular) :
    H.g₃.im = 0 ∧ (H.ω₃ = I * H.ω₁ → H.e 2 = 0 ∧ H.g₃ = 0) ∧
      (H.ω₃ ≠ I * H.ω₁ → (H.e 2).re * H.g₃.re < 0) := by
  sorry

/-- Rectangular half-periods `ω₁ = a`, `ω₃ = ib` with `a, b > 0`. -/
def rectangular (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : HalfPeriods :=
  ⟨a, b * I, by exact_mod_cast ha.ne', by
    rw [Complex.div_ofReal_im]; simpa using div_pos hb ha⟩

/-- DLMF §23.5(ii): with `ω₁` fixed, `e₁` and `e₂` are decreasing and `e₃` is increasing
functions of `ℑω₃`. -/
@[dlmf 23.5.ii]
theorem rectangular_roots_monotone (a b₁ b₂ : ℝ) (ha : 0 < a) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hb : b₁ < b₂) :
    ((rectangular a b₂ ha hb₂).e 1).re < ((rectangular a b₁ ha hb₁).e 1).re ∧
      ((rectangular a b₂ ha hb₂).e 2).re < ((rectangular a b₁ ha hb₁).e 2).re ∧
      ((rectangular a b₁ ha hb₁).e 3).re < ((rectangular a b₂ ha hb₂).e 3).re := by
  sorry

/-- `ζ(cz) = c⁻¹ζ(z)` when multiplication by `c` preserves the lattice. -/
lemma p23R1_zeta_rot (H : HalfPeriods) (c : ℂ) (hc : c ≠ 0)
    (hinv : ∀ z, z ∈ H.lattice ↔ z / c ∈ H.lattice) (z : ℂ) :
    H.weierstrassZeta (c * z) = c⁻¹ * H.weierstrassZeta z := by
  have hl : (scalePeriodPair c hc H.periodPair).lattice = H.periodPair.lattice := by
    ext w; rw [wp23_mem_scale_iff]; exact (hinv w).symm
  have := weierstrassZeta_scale c hc H.periodPair z
  rw [wp23_weierstrassZeta_eq_of_lattice_eq _ _ hl] at this
  exact this

/-- `e^{πi/3} = (1 + √3 i)/2`. -/
theorem p23R1_rho_eq : cexp (π * I / 3) = (1 + Real.sqrt 3 * I) / 2 := by
  rw [show (π : ℂ) * I / 3 = ((π / 3 : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring


/-- `℘(cz) = c⁻²℘(z)` when multiplication by `c` preserves the lattice. -/
theorem p23R1_wp_rot (H : HalfPeriods) (c : ℂ) (hc : c ≠ 0)
    (hinv : ∀ z, z ∈ H.lattice ↔ z / c ∈ H.lattice) (z : ℂ) :
    H.weierstrassP (c * z) = c⁻¹ ^ 2 * H.weierstrassP z := by
  have hl : (scalePeriodPair c hc H.periodPair).lattice = H.periodPair.lattice := by
    ext w; rw [wp23_mem_scale_iff]; exact (hinv w).symm
  have := weierstrassP_scale c hc H.periodPair z
  rw [wp23_weierstrassP_eq_of_lattice_eq _ _ hl] at this
  exact this

/-- A lemniscatic lattice is invariant under multiplication by `i`. -/
lemma p23R1_lemn_inv {H : HalfPeriods} (h3 : H.ω₃ = I * H.ω₁) :
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
  have hz := H.p23R1_zeta_rot I I_ne_zero hinv H.ω₁
  have e3 : H.eta 3 = -I * H.eta 1 := by
    rw [HalfPeriods.eta, HalfPeriods.eta, halfPeriod_three, halfPeriod_one, h3, hz, inv_I]
  have hL := H.p23R1_sigma_theta.2
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
  have hp := H.p23R1_wp_rot I I_ne_zero (p23R1_lemn_inv h3)
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
  have hKk : compEllIntKk k = (DLMF.Elliptic.Real.compEllIntKm (1 / 2) : ℂ) := by
    rw [compEllIntKk_ofReal (by rw [hk2]; norm_num), hk2]
  have hKpk : compEllIntKpk k = (DLMF.Elliptic.Real.compEllIntKm (1 / 2) : ℂ) := by
    rw [compEllIntKpk_ofReal (by rw [hk2]; norm_num), hk2]; norm_num
  have hval := DLMF.Elliptic.Real.compEllIntKm_one_half
  have hG : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hK0 : (DLMF.Elliptic.Real.compEllIntKm (1 / 2) : ℂ) ≠ 0 := by
    rw [hval]; exact_mod_cast (div_pos (pow_pos hG 2)
      (mul_pos (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos))).ne'
  have hdom : (k : ℂ) ∈ jacobiModulusDomain := by
    refine ⟨by simpa using hkpos, fun _ => ?_⟩
    simp only [ofReal_re]
    nlinarith
  have htk : jacobiTauk k = I := by
    rw [jacobiTauk, hKk, hKpk]; field_simp
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

/-- DLMF 23.5.5: `K(k) = K'(k) = Γ(1/4)²/(4√π)` for `k² = 1/2` (parameter form; this is the
project's `DLMF.Elliptic.Real.compEllIntKm_one_half`, and `K' = K(1 - k²) = K(1/2)`). -/
@[dlmf 23.5.E5]
theorem compEllIntKm_lemniscatic :
    DLMF.Elliptic.Real.compEllIntKm (1 / 2) = Real.Gamma (1 / 4) ^ 2 / (4 * Real.sqrt π) ∧
      DLMF.Elliptic.Real.compEllIntKm (1 - 1 / 2) = DLMF.Elliptic.Real.compEllIntKm (1 / 2) :=
  ⟨DLMF.Elliptic.Real.compEllIntKm_one_half, by norm_num⟩

open scoped ComplexConjugate in
/-- Rhombic lattices: `e₁` real and `e₃ = conj e₂ ∉ ℝ`. -/
lemma p3w_rhombic_roots {H : HalfPeriods} (h : H.IsRhombic) :
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
  have hwp := p3w_weierstrassP_conj_of_inv H.periodPair hinv
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
  obtain ⟨h1, h3, hy⟩ := p3w_rhombic_roots h
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

/-- DLMF §23.5(iv): for a rhombic lattice `e₁` is real and `e₃ = conj e₂` with `ℑe₂ > 0`; `e₁`
and `g₃` have the same sign unless `2ω₃ = (1 + i)ω₁` (the pseudo-lemniscatic case), when both
vanish. -/
@[dlmf 23.5.iv]
theorem IsRhombic.roots {H : HalfPeriods} (h : H.IsRhombic) :
    (H.e 1).im = 0 ∧ H.e 3 = (starRingEnd ℂ) (H.e 2) ∧ 0 < (H.e 2).im ∧ H.g₃.im = 0 ∧
      (2 * H.ω₃ = (1 + I) * H.ω₁ → H.e 1 = 0 ∧ H.g₃ = 0) ∧
      (2 * H.ω₃ ≠ (1 + I) * H.ω₁ → 0 < (H.e 1).re * H.g₃.re) := by
  sorry

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
    rw [hρ, p23R1_rho_eq]; ring_nf; rw [I_sq, hs]; ring
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
  have hz := H.p23R1_zeta_rot ρ hρ0 hinv H.ω₁
  have e3 : H.eta 3 = ρ⁻¹ * H.eta 1 := by
    rw [HalfPeriods.eta, HalfPeriods.eta, halfPeriod_three, halfPeriod_one, h3, hz]
  have hL := H.p23R1_sigma_theta.2
  rw [h3, e3, hρi] at hL
  have hsq : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)).ne'
  refine ⟨by rw [e3, ← mul_assoc, mul_inv_cancel₀ hρ0, one_mul], ?_⟩
  have hd : H.eta 1 * (2 * ρ - 1) = π * I / (2 * H.ω₁) := by
    field_simp at hL ⊢; linear_combination hL
  have h2 : 2 * ρ - 1 = Real.sqrt 3 * I := by rw [hρ, p23R1_rho_eq]; ring
  rw [h2] at hd
  field_simp at hd ⊢
  linear_combination hd

/-- DLMF 23.5.7: for an equianharmonic lattice
`e₁ = e^{2πi/3}e₃ = e^{-2πi/3}e₂ = Γ(1/3)⁶/(2^{14/3}π²ω₁²)`. -/
@[dlmf 23.5.E7]
theorem IsEquianharmonic.roots {H : HalfPeriods} (h : H.IsEquianharmonic) :
    H.e 1 = cexp (2 * π * I / 3) * H.e 3 ∧ H.e 1 = cexp (-(2 * π * I / 3)) * H.e 2 ∧
      H.e 1 = (Real.Gamma (1 / 3) : ℂ) ^ 6 / ((2 : ℂ) ^ (14 / 3 : ℂ) * π ^ 2 * H.ω₁ ^ 2) := by
  sorry

/-- DLMF 23.5.8: for an equianharmonic lattice `g₂ = 0` and `g₃ = Γ(1/3)¹⁸/(4πω₁)⁶`. -/
@[dlmf 23.5.E8]
theorem IsEquianharmonic.invariants {H : HalfPeriods} (h : H.IsEquianharmonic) :
    H.g₂ = 0 ∧ H.g₃ = (Real.Gamma (1 / 3) : ℂ) ^ 18 / (4 * π * H.ω₁) ^ 6 := by
  sorry

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

/-- DLMF 23.5.9: for `k = e^{iπ/6}` (so `k² = e^{iπ/3}`),
`K(k) = e^{iπ/6}K'(k) = e^{iπ/12} 3^{1/4} Γ(1/3)³/(2^{7/3}π)`, with the principal complex
complete elliptic integrals. -/
@[dlmf 23.5.E9]
theorem compEllIntKk_equianharmonic :
    JacobiElliptic.compEllIntKk (cexp (π * I / 6)) =
        cexp (π * I / 6) * JacobiElliptic.compEllIntKpk (cexp (π * I / 6)) ∧
      JacobiElliptic.compEllIntKk (cexp (π * I / 6)) =
        cexp (π * I / 12) * (3 : ℂ) ^ (1 / 4 : ℂ) * (Real.Gamma (1 / 3) : ℂ) ^ 3 /
          ((2 : ℂ) ^ (7 / 3 : ℂ) * π) := by
  sorry

end HalfPeriods

end DLMF.Weierstrass
