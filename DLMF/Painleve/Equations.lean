/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.Basic
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import DLMF.Painleve.Basic
public import Mathlib.Tactic.Polynomial.Basic

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

/-- A function that agrees near `0` (off `0`) with a function continuous at `0` tends to the
value of the latter at `0`. -/
lemma p3a_tendsto_of_eventuallyEq {F G : ℂ → ℂ} {L : ℂ}
    (hFG : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), F ε = G ε) (hG : ContinuousAt G 0) (hL : G 0 = L) :
    Tendsto F (𝓝[≠] 0) (𝓝 L) := by
  rw [← hL]
  exact (hG.tendsto.mono_left nhdsWithin_le_nhds).congr' (hFG.mono fun _ h => h.symm)

/-- A continuous function that does not vanish at `0` does not vanish near `0`. -/
lemma p3a_eventually_ne {f : ℂ → ℂ} (hf : Continuous f) (h0 : f 0 ≠ 0) :
    ∀ᶠ ε in 𝓝[≠] (0 : ℂ), f ε ≠ 0 :=
  nhdsWithin_le_nhds (hf.continuousAt.eventually_ne h0)

/-- Points of the punctured neighbourhood of `0` are nonzero. -/
lemma p3a_eventually_self_ne : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), ε ≠ 0 := self_mem_nhdsWithin

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
  refine p3a_tendsto_of_eventuallyEq (G := fun ε => (2 * X ^ 4 * ε ^ 3 * ζ + 2 * X ^ 4 * ε +
      4 * X ^ 3 * ε ^ 2 * ζ + 2 * X ^ 3 + 3 * X ^ 2 * ε * ζ - 2 * X * Y * ε ^ 3 + 2 * X * a * ε +
      X * ζ + 2 * Y ^ 2 * ε ^ 3 * ζ + 2 * Y ^ 2 * ε - Y * ε ^ 2 + a) /
      ((1 + 2 * ε * X) * (1 + ε ^ 2 * ζ))) ?_ ?_ ?_
  · filter_upwards [p3a_eventually_self_ne,
      p3a_eventually_ne (f := fun ε => 1 + 2 * ε * X) (by fun_prop) (by simp),
      p3a_eventually_ne (f := fun ε => 1 + ε ^ 2 * ζ) (by fun_prop) (by simp)] with ε h0 h1 h2
    simp only [painleveIIIRhs]
    generalize e1 : 1 + 2 * ε * X = A at h1 ⊢
    generalize e2 : 1 + ε ^ 2 * ζ = B at h2 ⊢
    field_simp
    subst e1 e2
    ring
  · exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)
  · simp [painleveIIRhs]
    ring

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
  intro t
  have ht : t ^ 3 = 2 := by
    simp only [t]
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have ht0 : t ≠ 0 := by rintro h; rw [h] at ht; norm_num at ht
  refine p3a_tendsto_of_eventuallyEq (G := fun ε => (3 * X ^ 4 * ε ^ 2 * t ^ 12 +
      8 * X ^ 3 * ε ^ 4 * t ^ 8 * ζ + 4 * X ^ 3 * t ^ 10 + 8 * X ^ 2 * a * ε ^ 4 * t ^ 8 +
      4 * X ^ 2 * ε ^ 6 * t ^ 4 * ζ ^ 2 + 16 * X ^ 2 * ε ^ 2 * t ^ 6 * ζ +
      16 * X * a * ε ^ 2 * t ^ 6 + 8 * X * ε ^ 4 * t ^ 2 * ζ ^ 2 + 8 * X * t ^ 4 * ζ +
      Y ^ 2 * ε ^ 2 * t ^ 12 + 8 * a * t ^ 4 + 4 * ε ^ 2 * ζ ^ 2) /
      (2 * t ^ 10 * (1 + t ^ 2 * ε ^ 2 * X))) ?_ ?_ ?_
  · filter_upwards [p3a_eventually_self_ne,
      p3a_eventually_ne (f := fun ε => 1 + t ^ 2 * ε ^ 2 * X) (by fun_prop) (by simp)]
      with ε h0 h1
    simp only [painleveIVRhs]
    have h1' : 1 / ε ^ 3 + t ^ 2 / ε * X ≠ 0 := by
      rw [show 1 / ε ^ 3 + t ^ 2 / ε * X = (1 + t ^ 2 * ε ^ 2 * X) / ε ^ 3 by field_simp]
      exact div_ne_zero h1 (pow_ne_zero 3 h0)
    generalize e1 : 1 / ε ^ 3 + t ^ 2 / ε * X = A at h1' ⊢
    generalize e2 : 1 + t ^ 2 * ε ^ 2 * X = B at h1 ⊢
    field_simp
    subst e1 e2
    field_simp
    ring
  · exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp [ht0])
  · have h6 : t ^ 6 = 4 := by rw [show t ^ 6 = (t ^ 3) ^ 2 by ring, ht]; norm_num
    have h10 : t ^ 10 = 4 * t ^ 4 := by rw [show t ^ 10 = t ^ 6 * t ^ 4 by ring, h6]
    have h12 : t ^ 12 = 16 := by rw [show t ^ 12 = (t ^ 6) ^ 2 by ring, h6]; norm_num
    simp only [painleveIIRhs]
    field_simp
    linear_combination (-(2 * X * ζ + 2 * a)) * h10

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
  refine p3a_tendsto_of_eventuallyEq (G := fun ε => (2 * X ^ 5 * a * ε ^ 2 * ζ ^ 2 +
      X ^ 5 * c * ε * ζ ^ 2 + 4 * X ^ 4 * a * ε * ζ + 2 * X ^ 4 * c * ζ + 2 * X ^ 3 * a +
      2 * X ^ 3 * b * ε ^ 2 * ζ ^ 2 + X ^ 3 * d * ε ^ 3 * ζ ^ 4 + X ^ 3 * ε +
      4 * X ^ 2 * b * ε * ζ + 4 * X ^ 2 * d * ε ^ 2 * ζ ^ 3 + 3 * X * Y ^ 2 * ε * ζ ^ 2 -
      2 * X * Y + 2 * X * b + 5 * X * d * ε * ζ ^ 2 + 2 * Y ^ 2 * ζ + 2 * d * ζ) /
      (2 * X * ζ * (1 + ε * ζ * X))) ?_ ?_ ?_
  · filter_upwards [p3a_eventually_self_ne,
      p3a_eventually_ne (f := fun ε => 1 + ε * ζ * X) (by fun_prop) (by simp)] with ε h0 h1
    have h2 : 1 + ε * ζ * X - 1 ≠ 0 := by simp [h0, hζ, hX]
    simp only [painleveVRhs]
    generalize e1 : 1 + ε * ζ * X = A at h1 h2 ⊢
    field_simp
    subst e1
    ring
  · exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp [hX, hζ])
  · simp only [painleveIIIRhs]
    field_simp
    ring

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
  intro r
  have hr : r ^ 2 = 2 := by
    simp only [r]; rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hr0 : r ≠ 0 := by rintro h; rw [h] at hr; norm_num at hr
  refine p3a_tendsto_of_eventuallyEq (G := fun ε => (r * X ^ 5 * ε - 6 * X ^ 4 +
      8 * r * X ^ 3 * a * ε ^ 3 * ζ ^ 2 + 16 * X ^ 3 * a * ε ^ 2 * ζ + 4 * r * X ^ 3 * a * ε +
      r * X ^ 3 * b * ε ^ 3 - 4 * r * X ^ 3 * ε * ζ ^ 2 - 16 * X ^ 3 * ζ -
      4 * r * X ^ 2 * Y * ε ^ 3 * ζ - 4 * X ^ 2 * Y * ε ^ 2 + 16 * X ^ 2 * a * ε ^ 2 * ζ ^ 2 +
      16 * r * X ^ 2 * a * ε * ζ + 8 * X ^ 2 * a - 6 * X ^ 2 * b * ε ^ 2 - 8 * X ^ 2 * ζ ^ 2 +
      6 * r * X * Y ^ 2 * ε ^ 3 * ζ ^ 2 + 12 * X * Y ^ 2 * ε ^ 2 * ζ + 3 * r * X * Y ^ 2 * ε +
      8 * X * Y * ε ^ 2 * ζ + 4 * r * X * Y * ε + 6 * r * X * b * ε - 4 * Y ^ 2 * ε ^ 2 * ζ ^ 2 -
      4 * r * Y ^ 2 * ε * ζ - 2 * Y ^ 2 - 4 * b) /
      (2 * X * (r / 2 * ε * X - 1) * 2 * (1 + r * ε * ζ) ^ 2)) ?_ ?_ ?_
  · filter_upwards [p3a_eventually_self_ne,
      p3a_eventually_ne (f := fun ε => 1 + r * ε * ζ) (by fun_prop) (by simp),
      p3a_eventually_ne (f := fun ε => r / 2 * ε * X - 1) (by fun_prop) (by simp)]
      with ε h0 h1 h2
    have h3 : r / 2 * ε * X ≠ 0 := by simp [h0, hr0, hX]
    simp only [painleveVRhs]
    generalize e1 : 1 + r * ε * ζ = A at h1 ⊢
    generalize e2 : r / 2 * ε * X - 1 = B at h2 ⊢
    field_simp
    subst e1 e2
    have hr3 : r ^ 3 = 2 * r := by rw [pow_succ, hr]
    have hr4 : r ^ 4 = 4 := by rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hr]; norm_num
    have hr5 : r ^ 5 = 4 * r := by rw [pow_succ, hr4]
    have hr6 : r ^ 6 = 8 := by rw [pow_succ, hr5]; linear_combination 4 * hr
    have hr7 : r ^ 7 = 8 * r := by rw [pow_succ, hr6]
    have hr8 : r ^ 8 = 16 := by rw [pow_succ, hr7]; linear_combination 8 * hr
    ring_nf
    simp only [hr, hr3, hr4, hr5, hr6, hr7, hr8]
    ring_nf
  · exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp [hX])
  · simp only [painleveIVRhs]
    field_simp
    ring

/-- DLMF 32.2.36–32.2.37 (`PVI → PV`): with `w = W(ζ)`, `z = 1 + εζ`, `γ = cε⁻¹ - dε⁻²`,
`δ = dε⁻²` (and `α = a`, `β = b`), the right-hand side of the equation for `W` tends to that
of `PV(a, b, c, d)` as `ε → 0` (at jets with `ζ ≠ 0`, `W ∉ {0, 1}`). -/
@[dlmf 32.2.E36, dlmf 32.2.E37, dlmf 32.2.E24]
theorem painleveVI_coalescence_V_tendsto (a b c d ζ X Y : ℂ) (hζ : ζ ≠ 0) (hX0 : X ≠ 0)
    (hX1 : X ≠ 1) :
    Tendsto (fun ε : ℂ => ε ^ 2 / 1 *
      painleveVIRhs a b (c / ε - d / ε ^ 2) (d / ε ^ 2) (1 + ε * ζ) (0 + 1 * X) (1 * Y / ε))
      (𝓝[≠] 0) (𝓝 (painleveVRhs a b c d ζ X Y)) := by
  refine p3a_tendsto_of_eventuallyEq (G := fun ε => (-2 * X ^ 6 * a + 4 * X ^ 5 * a * ε * ζ +
      8 * X ^ 5 * a - 2 * X ^ 4 * a * ε ^ 2 * ζ ^ 2 - 12 * X ^ 4 * a * ε * ζ - 12 * X ^ 4 * a -
      2 * X ^ 4 * b * ε * ζ - 2 * X ^ 4 * b - 2 * X ^ 4 * c * ζ - 2 * X ^ 4 * d * ζ ^ 2 +
      4 * X ^ 3 * Y * ε ^ 2 * ζ ^ 3 + 6 * X ^ 3 * Y * ε * ζ ^ 2 + 2 * X ^ 3 * Y * ζ +
      4 * X ^ 3 * a * ε ^ 2 * ζ ^ 2 + 12 * X ^ 3 * a * ε * ζ + 8 * X ^ 3 * a +
      4 * X ^ 3 * b * ε ^ 2 * ζ ^ 2 + 12 * X ^ 3 * b * ε * ζ + 8 * X ^ 3 * b +
      4 * X ^ 3 * c * ε * ζ ^ 2 + 4 * X ^ 3 * c * ζ - 3 * X ^ 2 * Y ^ 2 * ε ^ 2 * ζ ^ 4 -
      6 * X ^ 2 * Y ^ 2 * ε * ζ ^ 3 - 3 * X ^ 2 * Y ^ 2 * ζ ^ 2 - 2 * X ^ 2 * Y * ε ^ 3 * ζ ^ 4 -
      10 * X ^ 2 * Y * ε ^ 2 * ζ ^ 3 - 12 * X ^ 2 * Y * ε * ζ ^ 2 - 4 * X ^ 2 * Y * ζ -
      2 * X ^ 2 * a * ε ^ 2 * ζ ^ 2 - 4 * X ^ 2 * a * ε * ζ - 2 * X ^ 2 * a -
      2 * X ^ 2 * b * ε ^ 3 * ζ ^ 3 - 14 * X ^ 2 * b * ε ^ 2 * ζ ^ 2 - 24 * X ^ 2 * b * ε * ζ -
      12 * X ^ 2 * b - 2 * X ^ 2 * c * ε ^ 2 * ζ ^ 3 - 4 * X ^ 2 * c * ε * ζ ^ 2 -
      2 * X ^ 2 * c * ζ + 2 * X ^ 2 * d * ε * ζ ^ 3 + 2 * X ^ 2 * d * ζ ^ 2 +
      2 * X * Y ^ 2 * ε ^ 3 * ζ ^ 5 + 8 * X * Y ^ 2 * ε ^ 2 * ζ ^ 4 + 10 * X * Y ^ 2 * ε * ζ ^ 3 +
      4 * X * Y ^ 2 * ζ ^ 2 + 2 * X * Y * ε ^ 3 * ζ ^ 4 + 6 * X * Y * ε ^ 2 * ζ ^ 3 +
      6 * X * Y * ε * ζ ^ 2 + 2 * X * Y * ζ + 4 * X * b * ε ^ 3 * ζ ^ 3 +
      16 * X * b * ε ^ 2 * ζ ^ 2 + 20 * X * b * ε * ζ + 8 * X * b - Y ^ 2 * ε ^ 3 * ζ ^ 5 -
      3 * Y ^ 2 * ε ^ 2 * ζ ^ 4 - 3 * Y ^ 2 * ε * ζ ^ 3 - Y ^ 2 * ζ ^ 2 - 2 * b * ε ^ 3 * ζ ^ 3 -
      6 * b * ε ^ 2 * ζ ^ 2 - 6 * b * ε * ζ - 2 * b) /
      (2 * X * ζ ^ 2 * (X - 1) * (1 + ε * ζ) ^ 2 * (1 + ε * ζ - X))) ?_ ?_ ?_
  · filter_upwards [p3a_eventually_self_ne,
      p3a_eventually_ne (f := fun ε => 1 + ε * ζ) (by fun_prop) (by simp),
      p3a_eventually_ne (f := fun ε => X - (1 + ε * ζ)) (by fun_prop)
        (by simpa [sub_eq_zero] using hX1),
      p3a_eventually_ne (f := fun ε => 1 + ε * ζ - X) (by fun_prop)
        (by simpa [sub_eq_zero] using hX1.symm)] with ε h0 h1 h2 h5
    have h3 : 1 + ε * ζ - 1 ≠ 0 := by simp [h0, hζ]
    have h4 : X - 1 ≠ 0 := sub_ne_zero.mpr hX1
    simp only [painleveVIRhs, zero_add, one_mul]
    generalize e1 : 1 + ε * ζ = A at h1 h2 h3 h5 ⊢
    generalize e2 : X - 1 = X1 at h4 ⊢
    field_simp
    subst e1 e2
    ring
  · exact ContinuousAt.div (by fun_prop) (by fun_prop)
      (by simp [hX0, hζ, sub_eq_zero.not.mpr hX1, sub_eq_zero.not.mpr hX1.symm])
  · have h4 : X - 1 ≠ 0 := sub_ne_zero.mpr hX1
    have h5 : 1 - X ≠ 0 := fun h => h4 (by linear_combination -h)
    simp only [painleveVRhs, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero]
    generalize e2 : X - 1 = X1 at h4 ⊢
    field_simp
    subst e2
    ring

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
