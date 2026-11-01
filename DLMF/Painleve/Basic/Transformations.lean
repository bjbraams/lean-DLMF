/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.Basic.Equations
public import DLMF.Painleve.Basic.BealsWong
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic.Polynomial.Basic

/-!
# Transformations of the Painlevé equations: DLMF §32.2(ii)–(v)

Renormalizations, alternative forms and symmetric forms of the Painlevé equations in the DLMF
normalization, and the bridge between DLMF's `PII` and Beals–Wong's `PII`.

## Main results

* `isPainleveIIOn_iff_isPIIOn`: DLMF's `PII` with parameter `α` is Beals–Wong's `PII(-α)`.
* `IsODE2SolutionOn.affine`: an affine change of both variables in `w'' = F(z, w, w')`.
* `painleveIII_renormalize_gamma_delta`, `painleveIII_renormalize_alpha_delta`,
  `painleveIII_renormalize_beta_gamma`, `painleveV_renormalize_delta`: the renormalized
  parameter values of DLMF §32.2(ii), with `IsPainleveIIIOn.renormalize_gamma_delta` etc. for
  solutions.
* `IsPainleveIIIPrimeOn.isPainleveIIIOn`, `isPainleveIIIOn_exp_of_sineGordon`,
  `isPainleveIVOn_of_quintic`, `isPainleveVOn_coth_sq`: the alternative forms
  DLMF 32.2.9–32.2.12.
* `isPainleveIVOn_of_symmetric`, `isPainleveVOn_of_symmetric`: the symmetric forms
  (DLMF 32.2.15–32.2.23).

## Implementation notes

The alternative forms 32.2.9–32.2.12 are stated in the branch-free direction, from the new
unknown to `w`. The elliptic form of `PVI` (32.2.13–32.2.14) and the Painlevé property are in
`DLMF.Painleve.Equations`; the coalescence cascade is in `DLMF.Painleve.Basic.Coalescence`.
-/

@[expose] public noncomputable section

open Set Filter Complex
open scoped Topology

namespace DLMF.Painleve

/-! ## The bridge to Beals–Wong -/

/-- DLMF 32.2.2 and Beals–Wong (15.2.9): `w'' = 2w³ + zw + α` is Beals–Wong's `PII(c)`,
`u'' = 2u³ + xu - c`, with `c = -α`. -/
theorem isPainleveIIOn_iff_isPIIOn {α : ℂ} {w : ℂ → ℂ} {U : Set ℂ} :
    IsPainleveIIOn α w U ↔ IsPIIOn (-α) w U := by
  constructor
  · intro h
    exact ⟨h.differentiableAt, fun z hz => (h.hasDerivAt_deriv z hz).congr_deriv (by
      simp only [painleveIIRhs]; ring)⟩
  · intro h
    exact ⟨h.differentiableAt, fun z hz => (h.hasDerivAt_deriv z hz).congr_deriv (by
      simp only [painleveIIRhs]; ring)⟩

/-! ## Affine changes of variables -/

/-- An affine change of both variables, `W(ζ) = (w(c + dζ) - a)/b`, transforms a solution of
`w'' = F(z, w, w')` into a solution of `W'' = (d²/b) F(c + dζ, a + bW, bW'/d)`. -/
theorem IsODE2SolutionOn.affine {F : ℂ → ℂ → ℂ → ℂ} {w : ℂ → ℂ} {U V : Set ℂ}
    (h : IsODE2SolutionOn F w U) (hV : IsOpen V) {a b c d : ℂ} (hb : b ≠ 0) (hd : d ≠ 0)
    (hVU : ∀ ζ ∈ V, c + d * ζ ∈ U) :
    IsODE2SolutionOn (fun ζ X Y => d ^ 2 / b * F (c + d * ζ) (a + b * X) (b * Y / d))
      (fun ζ => (w (c + d * ζ) - a) / b) V := by
  have haff (ζ : ℂ) : HasDerivAt (fun ζ => c + d * ζ) d ζ := by
    simpa using ((hasDerivAt_id ζ).const_mul d).const_add c
  refine isODE2SolutionOn_of_hasDerivAt hV (v := fun ζ => d * deriv w (c + d * ζ) / b)
    (fun ζ hζ => ?_) (fun ζ hζ => ?_)
  · have h1 := (h.hasDerivAt (hVU ζ hζ)).comp ζ (haff ζ)
    exact ((h1.sub_const a).div_const b).congr_deriv (by ring)
  · have h1 := (h.hasDerivAt_deriv _ (hVU ζ hζ)).comp ζ (haff ζ)
    refine ((h1.const_mul d).div_const b).congr_deriv ?_
    have e1 : a + b * ((w (c + d * ζ) - a) / b) = w (c + d * ζ) := by field_simp; ring
    have e2 : b * (d * deriv w (c + d * ζ) / b) / d = deriv w (c + d * ζ) := by field_simp
    rw [e1, e2]
    ring

/-! ## Renormalizations (§32.2(ii)) -/

/-- Scaling of `PIII`: if `w` solves `PIII(α, β, γ, δ)` then `W(z) = a w(bz)` solves
`PIII(αb/a, βab, γb²/a², δa²b²)`. This is the rescaling behind §32.2(ii). -/
theorem IsPainleveIIIOn.scale {α β γ δ a b : ℂ} {w : ℂ → ℂ} {U V : Set ℂ}
    (h : IsPainleveIIIOn α β γ δ w U) (hV : IsOpen V) (ha : a ≠ 0) (hb : b ≠ 0)
    (hVU : ∀ z ∈ V, b * z ∈ U) :
    IsPainleveIIIOn (α * b / a) (β * a * b) (γ * b ^ 2 / a ^ 2) (δ * a ^ 2 * b ^ 2)
      (fun z => a * w (b * z)) V := by
  have hW := h.ode.affine hV (a := 0) (b := a⁻¹) (c := 0) (d := b) (inv_ne_zero ha) hb
    (by simpa using hVU)
  have hz0 (z : ℂ) (hz : z ∈ V) : z ≠ 0 := by
    intro h0; exact h.ne_zero _ (hVU z hz) (by simp [h0])
  refine ⟨?_, hz0, fun z hz => mul_ne_zero ha (h.w_ne_zero _ (hVU z hz))⟩
  have he : (fun ζ => (w (0 + b * ζ) - 0) / a⁻¹) = fun z => a * w (b * z) := by
    funext ζ; field_simp; simp
  rw [he] at hW
  refine hW.congr_rhs fun z hz => ?_
  have hw0 := h.w_ne_zero _ (hVU z hz)
  have hz' := hz0 z hz
  simp only [painleveIIIRhs, zero_add]
  field_simp

/-- DLMF §32.2(ii), first case: if `γδ ≠ 0`, a rescaling `W(z) = a w(bz)` normalizes
`PIII` to `γ = 1`, `δ = -1`. -/
@[dlmf 32.2.ii]
theorem painleveIII_renormalize_gamma_delta {γ δ : ℂ} (hγ : γ ≠ 0) (hδ : δ ≠ 0) :
    ∃ a b : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ γ * b ^ 2 / a ^ 2 = 1 ∧ δ * a ^ 2 * b ^ 2 = -1 := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (-γ / δ) (by norm_num : 0 < 4)
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq γ (by norm_num : 0 < 2)
  have ha0 : a ≠ 0 := by
    have : a ^ 4 ≠ 0 := by rw [ha]; exact div_ne_zero (neg_ne_zero.mpr hγ) hδ
    exact fun h0 => this (by simp [h0])
  have hc0 : c ≠ 0 := fun h0 => hγ (by rw [← hc, h0]; ring)
  have : a ^ 4 * δ = -γ := by rw [ha]; field_simp
  refine ⟨a, a / c, ha0, div_ne_zero ha0 hc0, ?_, ?_⟩
  · rw [div_pow, ← hc]; field_simp
  · rw [div_pow, hc]; field_simp; linear_combination this

/-- DLMF §32.2(ii), second case: if `γ = 0` and `αδ ≠ 0`, a rescaling normalizes `PIII` to
`α = 1`, `δ = -1` (and `γ` stays `0`). -/
@[dlmf 32.2.ii]
theorem painleveIII_renormalize_alpha_delta {α δ : ℂ} (hα : α ≠ 0) (hδ : δ ≠ 0) :
    ∃ a b : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ α * b / a = 1 ∧ δ * a ^ 2 * b ^ 2 = -1 := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (-α ^ 2 / δ) (by norm_num : 0 < 4)
  have ha0 : a ≠ 0 := by
    have : a ^ 4 ≠ 0 := by rw [ha]; exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ hα)) hδ
    exact fun h0 => this (by simp [h0])
  refine ⟨a, a / α, ha0, div_ne_zero ha0 hα, by field_simp, ?_⟩
  have : a ^ 4 * δ = -α ^ 2 := by rw [ha]; field_simp
  field_simp; linear_combination this

/-- DLMF §32.2(ii), third case: if `δ = 0` and `βγ ≠ 0`, a rescaling normalizes `PIII` to
`β = -1`, `γ = 1` (and `δ` stays `0`). -/
@[dlmf 32.2.ii]
theorem painleveIII_renormalize_beta_gamma {β γ : ℂ} (hβ : β ≠ 0) (hγ : γ ≠ 0) :
    ∃ a b : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ β * a * b = -1 ∧ γ * b ^ 2 / a ^ 2 = 1 := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (γ / β ^ 2) (by norm_num : 0 < 4)
  have ha0 : a ≠ 0 := by
    have : a ^ 4 ≠ 0 := by rw [ha]; exact div_ne_zero hγ (pow_ne_zero _ hβ)
    exact fun h0 => this (by simp [h0])
  refine ⟨a, -1 / (β * a), ha0, by simp [ha0, hβ], by field_simp, ?_⟩
  have : a ^ 4 * β ^ 2 = γ := by rw [ha]; field_simp
  field_simp; linear_combination -this

/-- Scaling of `PV` in `z`: if `w` solves `PV(α, β, γ, δ)` then `W(z) = w(bz)` solves
`PV(α, β, γb, δb²)`. -/
theorem IsPainleveVOn.scale {α β γ δ b : ℂ} {w : ℂ → ℂ} {U V : Set ℂ}
    (h : IsPainleveVOn α β γ δ w U) (hV : IsOpen V) (hb : b ≠ 0)
    (hVU : ∀ z ∈ V, b * z ∈ U) :
    IsPainleveVOn α β (γ * b) (δ * b ^ 2) (fun z => w (b * z)) V := by
  have hW := h.ode.affine hV (a := 0) (b := 1) (c := 0) (d := b) one_ne_zero hb
    (by simpa using hVU)
  have hz0 (z : ℂ) (hz : z ∈ V) : z ≠ 0 := by
    intro h0; exact h.ne_zero _ (hVU z hz) (by simp [h0])
  refine ⟨?_, hz0, fun z hz => h.w_ne_zero _ (hVU z hz), fun z hz => h.w_ne_one _ (hVU z hz)⟩
  simp only [zero_add, sub_zero, div_one] at hW
  refine hW.congr_rhs fun z hz => ?_
  have hw0 := h.w_ne_zero _ (hVU z hz)
  have hw1 : w (b * z) - 1 ≠ 0 := sub_ne_zero.mpr (h.w_ne_one _ (hVU z hz))
  have hz' := hz0 z hz
  simp only [painleveVRhs, one_mul]
  field_simp

/-- DLMF §32.2(ii): if `δ ≠ 0` in `PV`, the rescaling `z ↦ bz` with `b² = -1/(2δ)` gives
`δ = -1/2`. -/
@[dlmf 32.2.ii]
theorem painleveV_renormalize_delta {δ : ℂ} (hδ : δ ≠ 0) :
    ∃ b : ℂ, b ≠ 0 ∧ δ * b ^ 2 = -1 / 2 := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (-1 / (2 * δ)) (by norm_num : 0 < 2)
  refine ⟨b, ?_, ?_⟩
  · have : b ^ 2 ≠ 0 := by rw [hb]; exact div_ne_zero (by norm_num) (mul_ne_zero two_ne_zero hδ)
    exact fun h0 => this (by simp [h0])
  · rw [hb]; field_simp


/-- DLMF §32.2(ii) for `PIII` with `γδ ≠ 0`: some rescaling `W(z) = a w(bz)` is a solution
of `PIII` with `γ = 1`, `δ = -1`, on every open `V` with `bV ⊆ U`. -/
@[dlmf 32.2.ii]
theorem IsPainleveIIIOn.renormalize_gamma_delta {α β γ δ : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIIIOn α β γ δ w U) (hγ : γ ≠ 0) (hδ : δ ≠ 0) :
    ∃ a b : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ ∀ V : Set ℂ, IsOpen V → (∀ z ∈ V, b * z ∈ U) →
      IsPainleveIIIOn (α * b / a) (β * a * b) 1 (-1) (fun z => a * w (b * z)) V := by
  obtain ⟨a, b, ha, hb, h1, h2⟩ := painleveIII_renormalize_gamma_delta hγ hδ
  refine ⟨a, b, ha, hb, fun V hV hVU => ?_⟩
  simpa only [h1, h2] using h.scale hV ha hb hVU

/-- DLMF §32.2(ii) for `PIII` with `γ = 0`, `αδ ≠ 0`: some rescaling gives `α = 1`,
`δ = -1`. -/
@[dlmf 32.2.ii]
theorem IsPainleveIIIOn.renormalize_alpha_delta {α β δ : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIIIOn α β 0 δ w U) (hα : α ≠ 0) (hδ : δ ≠ 0) :
    ∃ a b : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ ∀ V : Set ℂ, IsOpen V → (∀ z ∈ V, b * z ∈ U) →
      IsPainleveIIIOn 1 (β * a * b) 0 (-1) (fun z => a * w (b * z)) V := by
  obtain ⟨a, b, ha, hb, h1, h2⟩ := painleveIII_renormalize_alpha_delta hα hδ
  refine ⟨a, b, ha, hb, fun V hV hVU => ?_⟩
  simpa only [h1, h2, zero_mul, zero_div] using h.scale hV ha hb hVU

/-- DLMF §32.2(ii) for `PIII` with `δ = 0`, `βγ ≠ 0`: some rescaling gives `β = -1`,
`γ = 1`. -/
@[dlmf 32.2.ii]
theorem IsPainleveIIIOn.renormalize_beta_gamma {α β γ : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIIIOn α β γ 0 w U) (hβ : β ≠ 0) (hγ : γ ≠ 0) :
    ∃ a b : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ ∀ V : Set ℂ, IsOpen V → (∀ z ∈ V, b * z ∈ U) →
      IsPainleveIIIOn (α * b / a) (-1) 1 0 (fun z => a * w (b * z)) V := by
  obtain ⟨a, b, ha, hb, h1, h2⟩ := painleveIII_renormalize_beta_gamma hβ hγ
  refine ⟨a, b, ha, hb, fun V hV hVU => ?_⟩
  simpa only [h1, h2, zero_mul] using h.scale hV ha hb hVU

/-- DLMF §32.2(ii) for `PV` with `δ ≠ 0`: some rescaling `W(z) = w(bz)` gives
`δ = -1/2`. -/
@[dlmf 32.2.ii]
theorem IsPainleveVOn.renormalize_delta {α β γ δ : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveVOn α β γ δ w U) (hδ : δ ≠ 0) :
    ∃ b : ℂ, b ≠ 0 ∧ ∀ V : Set ℂ, IsOpen V → (∀ z ∈ V, b * z ∈ U) →
      IsPainleveVOn α β (γ * b) (-1 / 2) (fun z => w (b * z)) V := by
  obtain ⟨b, hb, h1⟩ := painleveV_renormalize_delta hδ
  exact ⟨b, hb, fun V hV hVU => by simpa only [h1] using h.scale hV hb hVU⟩

/-! ## Alternative forms (§32.2(iii)) -/

/-- DLMF 32.2.9 (`P'III`): if `u` solves `P'III` on `V`, then `w(z) = ζ^{-1/2} u(ζ)` with
`ζ = z²`, that is `w(z) = u(z²)/z`, solves `PIII` with the same parameters wherever
`z² ∈ V`. Stated in this branch-free direction; every branch `z = ±ζ^{1/2}` is covered. -/
@[dlmf 32.2.E9]
theorem IsPainleveIIIPrimeOn.isPainleveIIIOn {α β γ δ : ℂ} {u : ℂ → ℂ} {V : Set ℂ}
    (h : IsPainleveIIIPrimeOn α β γ δ u V) (hV : IsOpen V) :
    IsPainleveIIIOn α β γ δ (fun z => u (z ^ 2) / z) ((fun z : ℂ => z ^ 2) ⁻¹' V) := by
  have hU : IsOpen ((fun z : ℂ => z ^ 2) ⁻¹' V) := hV.preimage (continuous_pow 2)
  have hz0 (z : ℂ) (hz : z ∈ (fun z : ℂ => z ^ 2) ⁻¹' V) : z ≠ 0 := by
    intro h0; exact h.ne_zero _ hz (by simp [h0])
  refine ⟨?_, hz0, fun z hz => div_ne_zero (h.w_ne_zero _ hz) (hz0 z hz)⟩
  refine isODE2SolutionOn_of_hasDerivAt hU
    (v := fun z => 2 * deriv u (z ^ 2) - u (z ^ 2) / z ^ 2) (fun z hz => ?_) (fun z hz => ?_)
  · have hz' := hz0 z hz
    have hz2 : z ^ 2 ∈ V := hz
    have hq : HasDerivAt (fun z : ℂ => z ^ 2) (2 * z) z := by
      simpa using hasDerivAt_pow 2 z
    have h1 := ((h.ode.hasDerivAt hz2).comp (h := fun z : ℂ => z ^ 2) z hq).div
      (hasDerivAt_id z) hz'
    refine h1.congr_deriv ?_
    simp only [Function.comp, id]
    field_simp
  · have hz' := hz0 z hz
    have hz2 : z ^ 2 ∈ V := hz
    have hu0 := h.w_ne_zero _ hz2
    have hζ : (z ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hz'
    have hq : HasDerivAt (fun z : ℂ => z ^ 2) (2 * z) z := by
      simpa using hasDerivAt_pow 2 z
    have h1 := (((h.ode.hasDerivAt_deriv _ hz2).comp (h := fun z : ℂ => z ^ 2) z
      hq).const_mul 2).sub (((h.ode.hasDerivAt hz2).comp (h := fun z : ℂ => z ^ 2) z hq).div hq hζ)
    refine h1.congr_deriv ?_
    simp only [Function.comp, painleveIIIRhs, painleveIIIPrimeRhs]
    field_simp
    ring

/-- DLMF 32.2.10: if `u` solves `u'' + u'/z = (2α/z) sin u + 2γ sin 2u` on `V` (with
`0 ∉ V`), then `w = exp(-iu)` solves `PIII` with `β = -α`, `δ = -γ`. Stated in the
branch-free direction from `u` to `w`. -/
@[dlmf 32.2.E10]
theorem isPainleveIIIOn_exp_of_sineGordon {α γ : ℂ} {u : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (h : IsODE2SolutionOn (fun z u v => -v / z + 2 * α / z * Complex.sin u +
      2 * γ * Complex.sin (2 * u)) u V) (h0 : ∀ z ∈ V, z ≠ 0) :
    IsPainleveIIIOn α (-α) γ (-γ) (fun z => Complex.exp (-Complex.I * u z)) V := by
  refine ⟨?_, h0, fun z _ => Complex.exp_ne_zero _⟩
  refine isODE2SolutionOn_of_hasDerivAt hV
    (v := fun z => -Complex.I * deriv u z * Complex.exp (-Complex.I * u z))
    (fun z hz => ?_) (fun z hz => ?_)
  · exact (((h.hasDerivAt hz).const_mul (-Complex.I)).cexp).congr_deriv (by ring)
  · have hE := ((h.hasDerivAt hz).const_mul (-Complex.I)).cexp
    have h1 := ((h.hasDerivAt_deriv z hz).const_mul (-Complex.I)).mul hE
    refine h1.congr_deriv ?_
    have hz' := h0 z hz
    have hE0 := Complex.exp_ne_zero (-Complex.I * u z)
    simp only [painleveIIIRhs, Complex.sin, two_mul]
    rw [show -(u z + u z) * Complex.I = -(Complex.I * u z) + -(Complex.I * u z) by ring,
      show (u z + u z) * Complex.I = Complex.I * u z + Complex.I * u z by ring,
      show -u z * Complex.I = -(Complex.I * u z) by ring,
      show -Complex.I * u z = -(Complex.I * u z) by ring,
      show u z * Complex.I = Complex.I * u z by ring, Complex.exp_add, Complex.exp_add,
      Complex.exp_neg]
    have hG := Complex.exp_ne_zero (Complex.I * u z)
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring

/-- DLMF 32.2.11: if `u` solves `u'' = 3u⁵ + 2ζu³ + (ζ²/4 - ν - 1/2)u + β/(32u³)` on `V`
(where `u ≠ 0`), then `w(z) = 2√2 u(ζ)²` with `ζ = √2 z` solves `PIV` with `α = 2ν + 1`.
Stated for any `r` with `r² = 2` in place of `√2` (stronger than DLMF: both signs). -/
@[dlmf 32.2.E11]
theorem isPainleveIVOn_of_quintic {ν β r : ℂ} (hr : r ^ 2 = 2) {u : ℂ → ℂ} {V : Set ℂ}
    (hV : IsOpen V)
    (h : IsODE2SolutionOn (fun ζ u _ => 3 * u ^ 5 + 2 * ζ * u ^ 3 +
      (ζ ^ 2 / 4 - ν - 1 / 2) * u + β / (32 * u ^ 3)) u V) (hu : ∀ ζ ∈ V, u ζ ≠ 0) :
    IsPainleveIVOn (2 * ν + 1) β (fun z => 2 * r * u (r * z) ^ 2)
      ((fun z => r * z) ⁻¹' V) := by
  have hr0 : r ≠ 0 := by rintro rfl; norm_num at hr
  have hU : IsOpen ((fun z => r * z) ⁻¹' V) := hV.preimage (continuous_const.mul continuous_id)
  have hq (z : ℂ) : HasDerivAt (fun z : ℂ => r * z) r z := by
    simpa using (hasDerivAt_id z).const_mul r
  refine ⟨?_, fun z hz => mul_ne_zero (mul_ne_zero two_ne_zero hr0) (pow_ne_zero 2 (hu _ hz))⟩
  refine isODE2SolutionOn_of_hasDerivAt hU
    (v := fun z => 4 * r ^ 2 * (u (r * z) * deriv u (r * z))) (fun z hz => ?_) (fun z hz => ?_)
  · have hz' : r * z ∈ V := hz
    have h1 := (((h.hasDerivAt hz').comp (h := fun z : ℂ => r * z) z (hq z)).pow 2).const_mul
      (2 * r)
    refine h1.congr_deriv ?_
    simp only [Function.comp]
    ring
  · have hz' : r * z ∈ V := hz
    have hu0 := hu _ hz'
    have h1 := (((h.hasDerivAt hz').comp (h := fun z : ℂ => r * z) z (hq z)).mul
      ((h.hasDerivAt_deriv _ hz').comp (h := fun z : ℂ => r * z) z (hq z))).const_mul
      (4 * r ^ 2)
    refine h1.congr_deriv ?_
    simp only [Function.comp, painleveIVRhs]
    have hp (n : ℕ) : r ^ (n + 2) = 2 * r ^ n := by rw [pow_add, hr]; ring
    field_simp
    ring_nf
    simp only [show r ^ 6 = 8 by simp [hp]; norm_num, show r ^ 5 = 4 * r by simp [hp]; ring,
      show r ^ 4 = 4 by simp [hp]; norm_num, show r ^ 3 = 2 * r by simp [hp], hr]
    ring

/-- DLMF 32.2.12: if `u` solves
`u'' = -α cosh u/(2 sinh³u) - β sinh u/(2 cosh³u) - γ e^ζ sinh(2u)/4 - δ e^{2ζ} sinh(4u)/8`
on `V`, where `sinh u` and `cosh u` do not vanish, then `w(z) = coth²(u(ζ))` with
`ζ = ln z` (principal branch, `z` in the slit plane) solves `PV`. -/
@[dlmf 32.2.E12]
theorem isPainleveVOn_coth_sq {α β γ δ : ℂ} {u : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (h : IsODE2SolutionOn (fun ζ u _ => -α * Complex.cosh u / (2 * Complex.sinh u ^ 3) -
      β * Complex.sinh u / (2 * Complex.cosh u ^ 3) -
      γ * Complex.exp ζ * Complex.sinh (2 * u) / 4 -
      δ * Complex.exp (2 * ζ) * Complex.sinh (4 * u) / 8) u V)
    (hs : ∀ ζ ∈ V, Complex.sinh (u ζ) ≠ 0) (hc : ∀ ζ ∈ V, Complex.cosh (u ζ) ≠ 0) :
    IsPainleveVOn α β γ δ (fun z => (Complex.cosh (u (Complex.log z)) /
      Complex.sinh (u (Complex.log z))) ^ 2) {z | z ∈ Complex.slitPlane ∧ Complex.log z ∈ V} := by
  have hopen : IsOpen {z | z ∈ Complex.slitPlane ∧ Complex.log z ∈ V} :=
    ContinuousOn.isOpen_inter_preimage (fun z hz => (continuousAt_clog hz).continuousWithinAt)
      Complex.isOpen_slitPlane hV
  refine ⟨isODE2SolutionOn_of_hasDerivAt hopen (v := fun z => ((2 * (Complex.cosh (u (Complex.log
      z)) / Complex.sinh (u (Complex.log z)))) * (((1 - ((Complex.cosh (u (Complex.log z)) /
      Complex.sinh (u (Complex.log z))) ^ 2)) * deriv u (Complex.log z)) / z))) (fun z hz => ?_)
      (fun z hz => ?_),
    fun z hz => Complex.slitPlane_ne_zero hz.1, fun z hz => ?_, fun z hz => ?_⟩
  · have hsl := hz.1
    have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hsl
    have hS0 := hs _ hz.2
    have hC0 := hc _ hz.2
    have hT0 : (Complex.cosh (u (Complex.log z)) / Complex.sinh (u (Complex.log z))) ≠ 0 :=
        div_ne_zero hC0 hS0
    have hcs := Complex.cosh_sq_sub_sinh_sq (u (Complex.log z))
    have e1 : (Complex.cosh (u (Complex.log z)) / Complex.sinh (u (Complex.log z))) ^ 2 - 1 = 1 /
        Complex.sinh (u (Complex.log z)) ^ 2 := by
      field_simp
      linear_combination hcs
    have e2 : (Complex.cosh (u (Complex.log z)) / Complex.sinh (u (Complex.log z))) ^ 2 + 1 =
        (Complex.cosh (u (Complex.log z)) ^ 2 + Complex.sinh (u (Complex.log z)) ^ 2) /
        Complex.sinh (u (Complex.log z)) ^ 2 := by
      field_simp
    have hT1 : (Complex.cosh (u (Complex.log z)) / Complex.sinh (u (Complex.log z))) ^ 2 - 1 ≠ 0 :=
        by
      rw [e1]
      exact one_div_ne_zero (pow_ne_zero 2 hS0)
    have hlog := Complex.hasDerivAt_log hsl
    have hu1 : HasDerivAt (fun x => u (Complex.log x)) (deriv u (Complex.log z) * z⁻¹) z :=
      (h.differentiableAt _ hz.2).hasDerivAt.comp z hlog
    have hT : HasDerivAt (fun x => Complex.cosh (u (Complex.log x)) / Complex.sinh (u (Complex.log
        x)))
        ((1 - (Complex.cosh (u (Complex.log z)) / Complex.sinh (u (Complex.log z))) ^ 2) * deriv u
            (Complex.log z) / z) z := by
      have hce : ∀ y, Complex.cosh y = (Complex.exp y + Complex.exp (-y)) / 2 := fun y => by
        rw [← Complex.two_cosh]
        ring
      have hse : ∀ y, Complex.sinh y = (Complex.exp y - Complex.exp (-y)) / 2 := fun y => by
        rw [← Complex.two_sinh]
        ring
      have hE := hu1.cexp
      have hE' := hu1.neg.cexp
      have hd : (Complex.exp (u (Complex.log z)) - Complex.exp (-u (Complex.log z))) / 2 ≠ 0 := by
        rw [← hse]
        exact hS0
      have hq := ((hE.add hE').div_const 2).div ((hE.sub hE').div_const 2) hd
      convert hq using 1
      · funext x
        simp only [hce, hse, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply]
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
        rw [hce, hse]
        generalize Complex.exp (u (Complex.log z)) = E at hd ⊢
        generalize Complex.exp (-u (Complex.log z)) = E' at hd ⊢
        have hd2 : E - E' ≠ 0 := fun h' => hd (by rw [h', zero_div])
        field_simp
        ring
    have hp : HasDerivAt (fun x => deriv u (Complex.log x)) ((-α * (Complex.cosh (u (Complex.log
        z)) / Complex.sinh (u (Complex.log z))) * ((Complex.cosh (u (Complex.log z)) / Complex.sinh
        (u (Complex.log z))) ^ 2 - 1) / 2 - β * ((Complex.cosh (u (Complex.log z)) / Complex.sinh
        (u (Complex.log z))) ^ 2 - 1) / (2 * (Complex.cosh (u (Complex.log z)) / Complex.sinh (u
        (Complex.log z))) ^ 3) - γ * z * (Complex.cosh (u (Complex.log z)) / Complex.sinh (u
        (Complex.log z))) / (2 * ((Complex.cosh (u (Complex.log z)) / Complex.sinh (u (Complex.log
        z))) ^ 2 - 1)) - δ * z ^ 2 * (Complex.cosh (u (Complex.log z)) / Complex.sinh (u
        (Complex.log z))) * ((Complex.cosh (u (Complex.log z)) / Complex.sinh (u (Complex.log z)))
        ^ 2 + 1) / (2 * ((Complex.cosh (u (Complex.log z)) / Complex.sinh (u (Complex.log z))) ^ 2
        - 1) ^ 2)) / z) z := by
      refine ((h.hasDerivAt_deriv _ hz.2).comp z hlog).congr_deriv ?_
      beta_reduce
      rw [show Complex.exp (2 * Complex.log z) = z ^ 2 by
        rw [two_mul, Complex.exp_add, Complex.exp_log hz0]; ring, Complex.exp_log hz0,
        show (4 : ℂ) * u (Complex.log z) = 2 * (2 * u (Complex.log z)) by ring]
      simp only [Complex.sinh_two_mul, Complex.cosh_two_mul]
      rw [e1, e2]
      field_simp
      ring
    have hid := hasDerivAt_id z
    have hc := (hT).pow 2
    convert hc using 1
    all_goals first
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; done)
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
      | skip
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVRhs]
  · have hsl := hz.1
    have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hsl
    have hS0 := hs _ hz.2
    have hC0 := hc _ hz.2
    have hT0 : (Complex.cosh (u (Complex.log z)) / Complex.sinh (u (Complex.log z))) ≠ 0 :=
        div_ne_zero hC0 hS0
    have hcs := Complex.cosh_sq_sub_sinh_sq (u (Complex.log z))
    have e1 : (Complex.cosh (u (Complex.log z)) / Complex.sinh (u (Complex.log z))) ^ 2 - 1 = 1 /
        Complex.sinh (u (Complex.log z)) ^ 2 := by
      field_simp
      linear_combination hcs
    have e2 : (Complex.cosh (u (Complex.log z)) / Complex.sinh (u (Complex.log z))) ^ 2 + 1 =
        (Complex.cosh (u (Complex.log z)) ^ 2 + Complex.sinh (u (Complex.log z)) ^ 2) /
        Complex.sinh (u (Complex.log z)) ^ 2 := by
      field_simp
    have hT1 : (Complex.cosh (u (Complex.log z)) / Complex.sinh (u (Complex.log z))) ^ 2 - 1 ≠ 0 :=
        by
      rw [e1]
      exact one_div_ne_zero (pow_ne_zero 2 hS0)
    have hlog := Complex.hasDerivAt_log hsl
    have hu1 : HasDerivAt (fun x => u (Complex.log x)) (deriv u (Complex.log z) * z⁻¹) z :=
      (h.differentiableAt _ hz.2).hasDerivAt.comp z hlog
    have hT : HasDerivAt (fun x => Complex.cosh (u (Complex.log x)) / Complex.sinh (u (Complex.log
        x)))
        ((1 - (Complex.cosh (u (Complex.log z)) / Complex.sinh (u (Complex.log z))) ^ 2) * deriv u
            (Complex.log z) / z) z := by
      have hce : ∀ y, Complex.cosh y = (Complex.exp y + Complex.exp (-y)) / 2 := fun y => by
        rw [← Complex.two_cosh]
        ring
      have hse : ∀ y, Complex.sinh y = (Complex.exp y - Complex.exp (-y)) / 2 := fun y => by
        rw [← Complex.two_sinh]
        ring
      have hE := hu1.cexp
      have hE' := hu1.neg.cexp
      have hd : (Complex.exp (u (Complex.log z)) - Complex.exp (-u (Complex.log z))) / 2 ≠ 0 := by
        rw [← hse]
        exact hS0
      have hq := ((hE.add hE').div_const 2).div ((hE.sub hE').div_const 2) hd
      convert hq using 1
      · funext x
        simp only [hce, hse, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply]
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
        rw [hce, hse]
        generalize Complex.exp (u (Complex.log z)) = E at hd ⊢
        generalize Complex.exp (-u (Complex.log z)) = E' at hd ⊢
        have hd2 : E - E' ≠ 0 := fun h' => hd (by rw [h', zero_div])
        field_simp
        ring
    have hp : HasDerivAt (fun x => deriv u (Complex.log x)) ((-α * (Complex.cosh (u (Complex.log
        z)) / Complex.sinh (u (Complex.log z))) * ((Complex.cosh (u (Complex.log z)) / Complex.sinh
        (u (Complex.log z))) ^ 2 - 1) / 2 - β * ((Complex.cosh (u (Complex.log z)) / Complex.sinh
        (u (Complex.log z))) ^ 2 - 1) / (2 * (Complex.cosh (u (Complex.log z)) / Complex.sinh (u
        (Complex.log z))) ^ 3) - γ * z * (Complex.cosh (u (Complex.log z)) / Complex.sinh (u
        (Complex.log z))) / (2 * ((Complex.cosh (u (Complex.log z)) / Complex.sinh (u (Complex.log
        z))) ^ 2 - 1)) - δ * z ^ 2 * (Complex.cosh (u (Complex.log z)) / Complex.sinh (u
        (Complex.log z))) * ((Complex.cosh (u (Complex.log z)) / Complex.sinh (u (Complex.log z)))
        ^ 2 + 1) / (2 * ((Complex.cosh (u (Complex.log z)) / Complex.sinh (u (Complex.log z))) ^ 2
        - 1) ^ 2)) / z) z := by
      refine ((h.hasDerivAt_deriv _ hz.2).comp z hlog).congr_deriv ?_
      beta_reduce
      rw [show Complex.exp (2 * Complex.log z) = z ^ 2 by
        rw [two_mul, Complex.exp_add, Complex.exp_log hz0]; ring, Complex.exp_log hz0,
        show (4 : ℂ) * u (Complex.log z) = 2 * (2 * u (Complex.log z)) by ring]
      simp only [Complex.sinh_two_mul, Complex.cosh_two_mul]
      rw [e1, e2]
      field_simp
      ring
    have hid := hasDerivAt_id z
    have hc := ((hT).const_mul 2).mul ((((((hT).pow 2).const_sub 1).mul (hp)).div (hid) hz0))
    convert hc using 1
    all_goals first
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; done)
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
      | skip
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVRhs]
    generalize deriv u (Complex.log z) = P
    generalize Complex.cosh (u (log z)) / Complex.sinh (u (log z)) = T at hT0 hT1 ⊢
    field_simp
    all_goals set_option maxRecDepth 100000 in ring
  · exact pow_ne_zero 2 (div_ne_zero (hc _ hz.2) (hs _ hz.2))
  · intro h'
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero 2 (hs _ hz.2))] at h'
    have := Complex.cosh_sq_sub_sinh_sq (u (Complex.log z))
    rw [h', sub_self] at this
    exact zero_ne_one this

/-! ## Symmetric forms (§32.2(v)) -/

/-- DLMF 32.2.15–32.2.18: if `f₁, f₂, f₃` satisfy the symmetric system
`f_j' + f_j(f_{j+1} - f_{j+2}) + 2μ_j = 0` with `μ₁ + μ₂ + μ₃ = 1` and
`f₁ + f₂ + f₃ + 2z = 0`, then `w = f₁` solves `PIV` with `(α, β) = (μ₃ - μ₂, -2μ₁²)`
wherever `f₁ ≠ 0`. (The third equation of 32.2.15 follows from the other two and the
constraints, and is not needed.) -/
@[dlmf 32.2.E15, dlmf 32.2.E16, dlmf 32.2.E17, dlmf 32.2.E18]
theorem isPainleveIVOn_of_symmetric {μ₁ μ₂ μ₃ : ℂ} {f₁ f₂ f₃ : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hμ : μ₁ + μ₂ + μ₃ = 1) (hsum : ∀ z ∈ U, f₁ z + f₂ z + f₃ z + 2 * z = 0)
    (h₁ : ∀ z ∈ U, HasDerivAt f₁ (-(f₁ z * (f₂ z - f₃ z)) - 2 * μ₁) z)
    (h₂ : ∀ z ∈ U, HasDerivAt f₂ (-(f₂ z * (f₃ z - f₁ z)) - 2 * μ₂) z)
    (hf : ∀ z ∈ U, f₁ z ≠ 0) :
    IsPainleveIVOn (μ₃ - μ₂) (-2 * μ₁ ^ 2) f₁ U := by
  have hf3 : ∀ z ∈ U, f₃ z = -2 * z - f₁ z - f₂ z := fun z hz => by
    linear_combination hsum z hz
  have hf3' : EqOn f₃ (fun z => -2 * z - f₁ z - f₂ z) U := fun z hz => hf3 z hz
  refine ⟨?_, hf⟩
  refine isODE2SolutionOn_of_hasDerivAt hU
    (v := fun z => -(f₁ z * (2 * f₂ z + 2 * z + f₁ z)) - 2 * μ₁) (fun z hz => ?_)
    (fun z hz => ?_)
  · exact (h₁ z hz).congr_deriv (by rw [hf3 z hz]; ring)
  · have hd := (((h₁ z hz).mul ((((h₂ z hz).const_mul 2).add
      ((hasDerivAt_id z).const_mul 2)).add (h₁ z hz))).neg).sub_const (2 * μ₁)
    refine hd.congr_deriv ?_
    have h0 := hf z hz
    have hμ3 : μ₃ = 1 - μ₁ - μ₂ := by linear_combination hμ
    simp only [painleveIVRhs, id, Pi.add_apply, hf3 z hz, hμ3]
    field_simp
    ring

/-- DLMF 32.2.19–32.2.23: if `f₁, …, f₄` satisfy the symmetric system 32.2.19 with
`μ₁ + μ₂ + μ₃ + μ₄ = 1` and `f₁ + f₃ = f₂ + f₄ = √z`, then `w = 1 - √z/f₁` solves `PV`
with `(α, β, γ, δ) = (μ₁²/2, -μ₃²/2, μ₄ - μ₂, -1/2)`. Branch-free: `√z` is any function
`s` on `U` with `s² = z` and `s' = 1/(2s)`; the set `U` avoids `z = 0`, `f₁ = 0` and
`f₃ = 0` (where `w ∈ {∞, 0}`). -/
@[dlmf 32.2.E19, dlmf 32.2.E20, dlmf 32.2.E21, dlmf 32.2.E22, dlmf 32.2.E23]
theorem isPainleveVOn_of_symmetric {μ₁ μ₂ μ₃ μ₄ : ℂ} {f₁ f₂ f₃ f₄ s : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hμ : μ₁ + μ₂ + μ₃ + μ₄ = 1)
    (hs : ∀ z ∈ U, s z ^ 2 = z) (hs' : ∀ z ∈ U, HasDerivAt s (1 / (2 * s z)) z)
    (h13 : ∀ z ∈ U, f₁ z + f₃ z = s z) (h24 : ∀ z ∈ U, f₂ z + f₄ z = s z)
    (h₁ : ∀ z ∈ U, HasDerivAt f₁
      ((f₁ z * f₃ z * (f₂ z - f₄ z) + (1 / 2 - μ₃) * f₁ z + μ₁ * f₃ z) / z) z)
    (h₂ : ∀ z ∈ U, HasDerivAt f₂
      ((f₂ z * f₄ z * (f₃ z - f₁ z) + (1 / 2 - μ₄) * f₂ z + μ₂ * f₄ z) / z) z)
    (h0 : ∀ z ∈ U, z ≠ 0) (hf₁ : ∀ z ∈ U, f₁ z ≠ 0) (hf₃ : ∀ z ∈ U, f₃ z ≠ 0) :
    IsPainleveVOn (μ₁ ^ 2 / 2) (-μ₃ ^ 2 / 2) (μ₄ - μ₂) (-1 / 2)
      (fun z => 1 - s z / f₁ z) U := by
  have hμ4 : μ₄ = 1 - μ₁ - μ₂ - μ₃ := by linear_combination hμ
  refine ⟨?_, h0, fun z hz => ?_, fun z hz h' => ?_⟩
  rotate_left
  · rw [show 1 - s z / f₁ z = -f₃ z / f₁ z by
      rw [eq_div_iff (hf₁ z hz), sub_mul, div_mul_cancel₀ _ (hf₁ z hz)]
      linear_combination h13 z hz]
    exact div_ne_zero (neg_ne_zero.mpr (hf₃ z hz)) (hf₁ z hz)
  · have : s z / f₁ z = 0 := by linear_combination -h'
    rcases div_eq_zero_iff.mp this with h'' | h''
    · exact h0 z hz (by rw [← hs z hz, h'', zero_pow two_ne_zero])
    · exact hf₁ z hz h''
  refine isODE2SolutionOn_of_hasDerivAt hU (v := fun z => (((((f₁ z * (1 - (2 * μ₃))) + (((2 * f₁
      z) * ((-f₁ z) + s z)) * ((2 * f₂ z) - s z))) - f₁ z) + ((2 * μ₁) * ((-f₁ z) + s z))) / ((2 *
      (f₁ z ^ 2)) * s z))) (fun z hz => ?_) (fun z hz => ?_)
  · have hS := hs' z hz
    have hF1 := h₁ z hz
    have hF2 := h₂ z hz
    have hid := hasDerivAt_id z
    have hS0 : s z ≠ 0 := fun h' => h0 z hz (by rw [← hs z hz, h', zero_pow two_ne_zero])
    have hF10 := hf₁ z hz
    have hW : f₁ z - s z ≠ 0 := fun h' => hf₃ z hz (by linear_combination h13 z hz - h')
    have hf3e : f₃ z = s z - f₁ z := by linear_combination h13 z hz
    have hf4e : f₄ z = s z - f₂ z := by linear_combination h24 z hz
    have hsq : z = s z ^ 2 := (hs z hz).symm
    have hc := (((hS).div (hF1) hF10)).const_sub 1
    convert hc using 1
    all_goals first
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; done)
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
      | skip
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVRhs]
    try rw [hf3e]
    try rw [hf4e]
    try rw [hμ4]
    generalize s z = S at hS0 hsq hW ⊢
    generalize f₁ z = F1 at hF10 hW ⊢
    generalize f₂ z = F2
    subst hsq
    field_simp
    try ring_nf
    try field_simp
    all_goals set_option maxRecDepth 100000 in ring
  · have hS := hs' z hz
    have hF1 := h₁ z hz
    have hF2 := h₂ z hz
    have hid := hasDerivAt_id z
    have hS0 : s z ≠ 0 := fun h' => h0 z hz (by rw [← hs z hz, h', zero_pow two_ne_zero])
    have hF10 := hf₁ z hz
    have hW : f₁ z - s z ≠ 0 := fun h' => hf₃ z hz (by linear_combination h13 z hz - h')
    have hf3e : f₃ z = s z - f₁ z := by linear_combination h13 z hz
    have hf4e : f₄ z = s z - f₂ z := by linear_combination h24 z hz
    have hsq : z = s z ^ 2 := (hs z hz).symm
    have hc := ((((((hF1).mul_const (1 - (2 * μ₃))).add ((((hF1).const_mul 2).mul (((hF1).neg).add
        (hS))).mul (((hF2).const_mul 2).sub (hS)))).sub (hF1)).add ((((hF1).neg).add
        (hS)).const_mul (2 * μ₁))).div ((((hF1).pow 2).const_mul 2).mul (hS)) (mul_ne_zero
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 hF10)) hS0))
    convert hc using 1
    all_goals first
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; done)
      | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
          Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
      | skip
    try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.div_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, painleveVRhs]
    try rw [hf3e]
    try rw [hf4e]
    try rw [hμ4]
    generalize s z = S at hS0 hsq hW ⊢
    generalize f₁ z = F1 at hF10 hW ⊢
    generalize f₂ z = F2
    subst hsq
    field_simp
    try ring_nf
    try field_simp
    all_goals set_option maxRecDepth 100000 in ring

end DLMF.Painleve
