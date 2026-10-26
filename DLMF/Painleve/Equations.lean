/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.Defs
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The Painlevé equations: DLMF §32.2

* The bridge `isPainleveIIOn_iff_isPIIOn`: DLMF's `PII` with parameter `α` is Beals–Wong's
  `PII(-α)` of `DLMF.Painleve.Basic`.
* Renormalizations (§32.2(ii)): scaling lemmas for `PIII` and `PV`, with the normalized
  parameter values of DLMF.
* Alternative forms (§32.2(iii)): `P'III` (32.2.9) and the forms 32.2.10–32.2.12, in the
  branch-free direction (from the new unknown to `w`).
* The elliptic form of `PVI` (32.2.13–32.2.14), the symmetric forms (§32.2(v)) and the
  coalescence cascade (§32.2(vi)): exact transformed equations and their limits.
* The Painlevé property (prose of §32.2(i)) for `PI` and `PII`.
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
  sorry

/-- DLMF 32.2.13–32.2.14, the elliptic form of `PVI`. With the operator
`I = z(1-z) d²/dz² + (1-2z) d/dz - 1/4` (32.2.14) and
`Φ(z) = ∫_∞^{w(z)} dt/√(t(t-1)(t-z))`, a solution of `PVI` satisfies
`z(1-z) I Φ = √(w(w-1)(w-z)) (α + βz/w² + γ(z-1)/(w-1)² + (δ - 1/2) z(z-1)/(w-z)²)`.

Branch convention (made precise here; DLMF leaves it implicit): the path of integration is the
ray `t = w(z)/s`, `0 < s ≤ 1`, and the square root is the principal one, which is assumed to be
continuous along the ray (the polynomial stays in the slit plane); so
`Φ(z) = -∫₀¹ (w/s²) (P(w/s))^{-1/2} ds` with `P(t) = t(t-1)(t-z)`. -/
@[dlmf 32.2.E13, dlmf 32.2.E14]
theorem IsPainleveVIOn.ellipticForm {α β γ δ : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveVIOn α β γ δ w U) (hU : IsOpen U)
    (hcut : ∀ z ∈ U, ∀ s : ℝ, 0 < s → s ≤ 1 →
      (w z / s) * (w z / s - 1) * (w z / s - z) ∈ Complex.slitPlane)
    {Φ : ℂ → ℂ}
    (hΦ : ∀ z ∈ U, Φ z = -∫ s in (0 : ℝ)..1, (w z / (s : ℂ) ^ 2) /
      ((w z / s) * (w z / s - 1) * (w z / s - z)) ^ (1 / 2 : ℂ)) :
    ∀ z ∈ U, z * (1 - z) * (z * (1 - z) * deriv (deriv Φ) z + (1 - 2 * z) * deriv Φ z -
        Φ z / 4) =
      (w z * (w z - 1) * (w z - z)) ^ (1 / 2 : ℂ) *
        (α + β * z / w z ^ 2 + γ * (z - 1) / (w z - 1) ^ 2 +
          (δ - 1 / 2) * z * (z - 1) / (w z - z) ^ 2) := by
  sorry

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
  sorry

/-! ## Coalescence cascade (§32.2(vi)) -/

/-- DLMF 32.2.25–32.2.27, exact form: if `w` solves `PII` with `α = 4ε⁻¹⁵` and
`w = εW(ζ) + ε⁻⁵`, `z = ε²ζ - 6ε⁻¹⁰`, then
`W'' = 6W² + ζ + ε⁶(2W³ + ζW)` exactly; as `ε → 0` this is `PI`. -/
@[dlmf 32.2.E25, dlmf 32.2.E26, dlmf 32.2.E27]
theorem IsPainleveIIOn.coalescence_I {ε : ℂ} (hε : ε ≠ 0) {w : ℂ → ℂ} {U V : Set ℂ}
    (h : IsPainleveIIOn (4 / ε ^ 15) w U) (hV : IsOpen V)
    (hVU : ∀ ζ ∈ V, ε ^ 2 * ζ - 6 / ε ^ 10 ∈ U) :
    IsODE2SolutionOn (fun ζ W _ => 6 * W ^ 2 + ζ + ε ^ 6 * (2 * W ^ 3 + ζ * W))
      (fun ζ => (w (ε ^ 2 * ζ - 6 / ε ^ 10) - 1 / ε ^ 5) / ε) V := by
  have hW := IsODE2SolutionOn.affine h hV (a := 1 / ε ^ 5) (b := ε) (c := -6 / ε ^ 10)
    (d := ε ^ 2) hε (pow_ne_zero 2 hε) (fun ζ hζ => by
      convert hVU ζ hζ using 1; ring)
  have he : (fun ζ => (w (-6 / ε ^ 10 + ε ^ 2 * ζ) - 1 / ε ^ 5) / ε) =
      fun ζ => (w (ε ^ 2 * ζ - 6 / ε ^ 10) - 1 / ε ^ 5) / ε := by
    funext ζ; congr 3; ring
  rw [he] at hW
  refine hW.congr_rhs fun ζ _ => ?_
  simp only [painleveIIRhs]
  field_simp
  ring

/-- The `PI` limit of 32.2.27: the right-hand side `6W² + ζ + ε⁶(2W³ + ζW)` tends to the
right-hand side of `PI` as `ε → 0`. -/
@[dlmf 32.2.vi]
theorem painleveII_coalescence_I_tendsto (ζ X Y : ℂ) :
    Tendsto (fun ε : ℂ => 6 * X ^ 2 + ζ + ε ^ 6 * (2 * X ^ 3 + ζ * X)) (𝓝 0)
      (𝓝 (painleveIRhs ζ X Y)) := by
  have hc : Continuous (fun ε : ℂ => 6 * X ^ 2 + ζ + ε ^ 6 * (2 * X ^ 3 + ζ * X)) := by
    fun_prop
  simpa [painleveIRhs] using hc.tendsto 0

/-- DLMF 32.2.28–32.2.29 (`PIII → PII`): with `w = 1 + 2εW(ζ)`, `z = 1 + ε²ζ`,
`α = -ε⁻⁶/2`, `β = ε⁻⁶/2 + 2aε⁻³`, `γ = -δ = ε⁻⁶/4`, the equation satisfied by `W`
(`IsODE2SolutionOn.affine`) has right-hand side
`(ε⁴/(2ε)) PIII-rhs(1 + ε²ζ, 1 + 2εW, 2εW'/ε²)`, which tends to the right-hand side of
`PII` with `α = a` as `ε → 0`. -/
@[dlmf 32.2.E28, dlmf 32.2.E29, dlmf 32.2.E24]
theorem painleveIII_coalescence_II_tendsto (a ζ X Y : ℂ) :
    Tendsto (fun ε : ℂ => (ε ^ 2) ^ 2 / (2 * ε) *
      painleveIIIRhs (-1 / (2 * ε ^ 6)) (1 / (2 * ε ^ 6) + 2 * a / ε ^ 3) (1 / (4 * ε ^ 6))
        (-1 / (4 * ε ^ 6)) (1 + ε ^ 2 * ζ) (1 + 2 * ε * X) (2 * ε * Y / ε ^ 2))
      (𝓝[≠] 0) (𝓝 (painleveIIRhs a ζ X Y)) := by
  sorry

/-- DLMF 32.2.30–32.2.31 (`PIV → PII`): with `w = 2^{2/3}ε⁻¹W(ζ) + ε⁻³`,
`z = 2^{-2/3}εζ - ε⁻³`, `α = -2a - ε⁻⁶/2`, `β = -ε⁻¹²/2`, the right-hand side of the equation
for `W` tends to that of `PII` with `α = a`. Here `2^{2/3}` is `t²` for `t = 2^{1/3}` real. -/
@[dlmf 32.2.E30, dlmf 32.2.E31, dlmf 32.2.E24]
theorem painleveIV_coalescence_II_tendsto (a ζ X Y : ℂ) :
    let t : ℂ := ((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ)
    Tendsto (fun ε : ℂ => (ε / t ^ 2) ^ 2 / (t ^ 2 / ε) *
      painleveIVRhs (-2 * a - 1 / (2 * ε ^ 6)) (-1 / (2 * ε ^ 12)) (ε / t ^ 2 * ζ - 1 / ε ^ 3)
        (1 / ε ^ 3 + t ^ 2 / ε * X) (t ^ 2 / ε * Y / (ε / t ^ 2)))
      (𝓝[≠] 0) (𝓝 (painleveIIRhs a ζ X Y)) := by
  sorry

/-- DLMF 32.2.32–32.2.33 (`PV → PIII`): with `w = 1 + εζW(ζ)`, `z = ζ²`,
`α = a/(4ε) + c/(8ε²)`, `β = -c/(8ε²)`, `γ = εb/4`, `δ = ε²d/8`, `W` satisfies (for
`ε ≠ 0`) an equation whose right-hand side tends to that of `PIII(a, b, c, d)` as `ε → 0`.
Stated for solutions: the limit holds at every jet `(ζ, W, W')` with `ζ ≠ 0`, `W ≠ 0`, where
the `ε`-equation is obtained from `PV` by the stated substitution. -/
@[dlmf 32.2.E32, dlmf 32.2.E33, dlmf 32.2.E24]
theorem painleveV_coalescence_III_tendsto (a b c d ζ X Y : ℂ) (hζ : ζ ≠ 0) (hX : X ≠ 0) :
    Tendsto (fun ε : ℂ =>
      -- `w = 1 + εζX`, `w_z = (εX + εζY)/(2ζ)`; solve `w_zz = PV-rhs` for `W''`.
      ((2 * ζ) ^ 2 * painleveVRhs (a / (4 * ε) + c / (8 * ε ^ 2)) (-c / (8 * ε ^ 2))
          (ε * b / 4) (ε ^ 2 * d / 8) (ζ ^ 2) (1 + ε * ζ * X) ((ε * X + ε * ζ * Y) / (2 * ζ)) +
        (ε * X + ε * ζ * Y) / ζ - 2 * ε * Y) / (ε * ζ))
      (𝓝[≠] 0) (𝓝 (painleveIIIRhs a b c d ζ X Y)) := by
  sorry

/-- DLMF 32.2.34–32.2.35 (`PV → PIV`): with `w = (√2/2)εW(ζ)`, `z = 1 + √2εζ`,
`α = ε⁻⁴/2`, `β = b/4`, `γ = -ε⁻⁴`, `δ = aε⁻² - ε⁻⁴/2`, the right-hand side of the equation for
`W` tends to that of `PIV(a, b)` as `ε → 0` (at jets with `W ≠ 0`). -/
@[dlmf 32.2.E34, dlmf 32.2.E35, dlmf 32.2.E24]
theorem painleveV_coalescence_IV_tendsto (a b ζ X Y : ℂ) (hX : X ≠ 0) :
    let r : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)
    Tendsto (fun ε : ℂ => (r * ε) ^ 2 / (r / 2 * ε) *
      painleveVRhs (1 / (2 * ε ^ 4)) (b / 4) (-1 / ε ^ 4) (a / ε ^ 2 - 1 / (2 * ε ^ 4))
        (1 + r * ε * ζ) (r / 2 * ε * X) (r / 2 * ε * Y / (r * ε)))
      (𝓝[≠] 0) (𝓝 (painleveIVRhs a b ζ X Y)) := by
  sorry

/-- DLMF 32.2.36–32.2.37 (`PVI → PV`): with `w = W(ζ)`, `z = 1 + εζ`, `γ = cε⁻¹ - dε⁻²`,
`δ = dε⁻²` (and `α = a`, `β = b`), the right-hand side of the equation for `W` tends to that
of `PV(a, b, c, d)` as `ε → 0` (at jets with `ζ ≠ 0`, `W ∉ {0, 1}`). -/
@[dlmf 32.2.E36, dlmf 32.2.E37, dlmf 32.2.E24]
theorem painleveVI_coalescence_V_tendsto (a b c d ζ X Y : ℂ) (hζ : ζ ≠ 0) (hX0 : X ≠ 0)
    (hX1 : X ≠ 1) :
    Tendsto (fun ε : ℂ => ε ^ 2 / 1 *
      painleveVIRhs a b (c / ε - d / ε ^ 2) (d / ε ^ 2) (1 + ε * ζ) (0 + 1 * X) (1 * Y / ε))
      (𝓝[≠] 0) (𝓝 (painleveVRhs a b c d ζ X Y)) := by
  sorry

/-! ## The Painlevé property (§32.2(i)) -/

/-- DLMF §32.2(i): the Painlevé property of `PI` in its global form: every solution on a
connected open set is the restriction of a function meromorphic in the whole plane. -/
@[dlmf 32.2.i]
theorem IsPainleveIOn.exists_meromorphic {w : ℂ → ℂ} {U : Set ℂ} (h : IsPainleveIOn w U)
    (hU : IsOpen U) (hc : IsConnected U) :
    ∃ W : ℂ → ℂ, MeromorphicOn W univ ∧ EqOn W w U := by
  sorry

/-- DLMF §32.2(i): the Painlevé property of `PII`: every solution on a connected open set
extends to a function meromorphic in the whole plane. -/
@[dlmf 32.2.i]
theorem IsPainleveIIOn.exists_meromorphic {α : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIIOn α w U) (hU : IsOpen U) (hc : IsConnected U) :
    ∃ W : ℂ → ℂ, MeromorphicOn W univ ∧ EqOn W w U := by
  sorry

/-- DLMF §32.2(i): the Painlevé property of `PIV`: every solution on a connected open set
extends to a function meromorphic in the whole plane. -/
@[dlmf 32.2.i]
theorem IsPainleveIVOn.exists_meromorphic {α β : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIVOn α β w U) (hU : IsOpen U) (hc : IsConnected U) :
    ∃ W : ℂ → ℂ, MeromorphicOn W univ ∧ EqOn W w U := by
  sorry

/-- DLMF §32.2(i): the Painlevé property of `PIII` (fixed singularity at `0`): for a solution
on a connected open set `U`, the function `t ↦ w(eᵗ)` extends to a function meromorphic in
the whole `t`-plane. -/
@[dlmf 32.2.i]
theorem IsPainleveIIIOn.exists_meromorphic_exp {α β γ δ : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveIIIOn α β γ δ w U) (hU : IsOpen U) {T : Set ℂ} (hT : IsOpen T)
    (hTc : IsConnected T) (hTU : ∀ t ∈ T, Complex.exp t ∈ U) :
    ∃ W : ℂ → ℂ, MeromorphicOn W univ ∧ ∀ t ∈ T, W t = w (Complex.exp t) := by
  sorry

/-- DLMF §32.2(i): the Painlevé property of `PV` (fixed singularity at `0`): `t ↦ w(eᵗ)`
extends to a function meromorphic in the whole `t`-plane. -/
@[dlmf 32.2.i]
theorem IsPainleveVOn.exists_meromorphic_exp {α β γ δ : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (h : IsPainleveVOn α β γ δ w U) (hU : IsOpen U) {T : Set ℂ} (hT : IsOpen T)
    (hTc : IsConnected T) (hTU : ∀ t ∈ T, Complex.exp t ∈ U) :
    ∃ W : ℂ → ℂ, MeromorphicOn W univ ∧ ∀ t ∈ T, W t = w (Complex.exp t) := by
  sorry

end DLMF.Painleve
