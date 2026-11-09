/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.ZeroClassification

/-!
# Zeros of the error functions and Fresnel integrals (DLMF §7.13)

Enumerations of the complex zeros of `erf`, `erfc`, `w` and the Fresnel integrals, their
classification, and the asymptotic expansions of the zeros. Numerical tables (Tables
7.13.1–7.13.4) are excluded.

## Main definitions

* `errorFunctionZero`: the zeros of `erf` (resp. `erfc`) in the upper half-plane, indexed from
  one by increasing modulus.
* `fresnelFunctionZero`: the zeros of `C` (resp. `S`) in the first octant; the other octants
  follow by symmetry.
* `errorZeroLambda`, `errorZeroMu`: the variables `λ`, `μ` of DLMF 7.13.2, 7.13.4.
* `fresnelZeroLambda`, `fresnelZeroAlpha`: the variables of DLMF 7.13.6, 7.13.7.

## Main results

* `erf_zero_simple`, `fresnel_zero_orders`: the zeros at the origin.
* `errorFunctionZero_spec`, `errorFunctionZero_spec_iff`, `fresnelFunctionZero_spec`: the
  enumerations are well defined; `errorFunctionZero_spec_iff` reduces this to distinct moduli
  and infinitely many zeros in the sector.
* `errorFunctionZero_ordered`, `fresnelFunctionZero_ordered`: the moduli increase strictly.
* `erf_zero_classification`, `erfc_zero_classification`, `faddeevaW_zero_classification`,
  `fresnel_zero_classification`, `fresnelTail_zero_classification`: the complete zero sets
  (DLMF §7.13(ii)–(iv)).
* `errorFunctionZero_asymptotic`: all-order expansions of the zeros of `erf` and `erfc`
  (DLMF 7.13.1, 7.13.3).
* `fresnelFunctionZero_asymptotic`: all-order expansions of the Fresnel zeros (DLMF 7.13.5).

## Implementation notes

The orderings and classifications are derived from the enumeration statements
`errorFunctionZero_spec` and `fresnelFunctionZero_spec` together with the zero localizations of
`DLMF.ErrorFunctions.ZeroClassification`.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
open DLMF.Core

namespace DLMF.Confluent

/-- The selected upper-half-plane error-function zeros, indexed from one. -/
def errorFunctionZero (complement : Bool) (k : ℕ) : ℂ :=
  orderedZero (if complement then erfc else erf)
      (if complement then {z : ℂ | π/2 < arg z ∧ arg z < 3*π/4} else
      {z : ℂ | 0 < z.re ∧ 0 < z.im}) k

/-- Fresnel representatives in the first octant; the other octants follow by symmetry. -/
def fresnelFunctionZero (sine : Bool) (k : ℕ) : ℂ :=
  orderedZero (if sine then fresnelS else fresnelC) {z : ℂ | 0 < arg z ∧ arg z < π/4} k

/-- Identity under the stated parameter and domain assumptions: `erf 0=0 ∧ deriv erf 0=2/Real.sqrt
π`. -/
theorem erf_zero_simple  :
    erf 0=0 ∧ deriv erf 0=2/Real.sqrt π := by
  refine ⟨erf_zero, ?_⟩
  rw [(hasDerivAt_erf_complex 0).deriv]
  simp

/-- The simple C zero and triple S zero at the origin. -/
theorem fresnel_zero_orders  :
    fresnelC 0=0 ∧ deriv fresnelC 0=1 ∧ fresnelS 0=0 ∧ deriv fresnelS 0=0 ∧
        iteratedDeriv 2 fresnelS 0=0 ∧ iteratedDeriv 3 fresnelS 0=π := by
  have hS1 : deriv fresnelS = fun z => sin (π*z^2/2) :=
    funext fun z => (hasDerivAt_fresnelS_complex z).deriv
  have hd2 (z : ℂ) : HasDerivAt (fun z : ℂ => sin (π*z^2/2)) (cos (π*z^2/2)*(π*z)) z := by
    have h := (((hasDerivAt_id' z).pow 2).const_mul (π:ℂ)).div_const 2 |>.csin
    convert h using 1
    simp only [Pi.pow_apply]
    ring
  have hS2 : iteratedDeriv 2 fresnelS = fun z => cos (π*z^2/2)*(π*z) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hS1]
    exact funext fun z => (hd2 z).deriv
  have hd3 : HasDerivAt (fun z : ℂ => cos (π*z^2/2)*(π*z))
      (-sin (π*0^2/2)*(π*0)*(π*0)+cos (π*0^2/2)*π) 0 := by
    have h1 := (((hasDerivAt_id' (0:ℂ)).pow 2).const_mul (π:ℂ)).div_const 2 |>.ccos
    have h2 := ((hasDerivAt_id' (0:ℂ)).const_mul (π:ℂ))
    convert h1.mul h2 using 1
    simp
  refine ⟨primitive_zero _, ?_, primitive_zero _, ?_, ?_, ?_⟩
  · rw [(hasDerivAt_fresnelC_complex 0).deriv]; simp
  · rw [hS1]; simp
  · rw [hS2]; simp
  · rw [iteratedDeriv_succ, hS2, hd3.deriv]; simp

/-- The stated relation follows from the given hypotheses: `let f`. -/
theorem errorFunctionZero_spec (complement : Bool) {k : ℕ} (hk : 1 ≤ k) :
    let f := if complement then erfc else erf
    let S := if complement then {z : ℂ | π/2 < arg z ∧ arg z < 3*π/4}
      else {z : ℂ | 0 < z.re ∧ 0 < z.im}
    errorFunctionZero complement k ∈ S ∧ f (errorFunctionZero complement k)=0 ∧
      ({z : ℂ | z ∈ S ∧ f z=0 ∧ ‖z‖ < ‖errorFunctionZero complement k‖} : Set ℂ).ncard=k-1 := by
  sorry

/-- The enumeration `errorFunctionZero` is well defined for every index exactly when the zeros of
`erf` in the first quadrant (resp. of `erfc` in `π/2 < ph z < 3π/4`) have pairwise distinct moduli
and are infinitely many. This isolates the analytic content of `errorFunctionZero_spec`. -/
theorem errorFunctionZero_spec_iff (complement : Bool) :
    let f := if complement then erfc else erf
    let S := if complement then {z : ℂ | π/2 < arg z ∧ arg z < 3*π/4} else
        {z : ℂ | 0 < z.re ∧ 0 < z.im}
    (∀ k : ℕ, 1 ≤ k → errorFunctionZero complement k ∈ S ∧ f (errorFunctionZero complement k)=0 ∧
      ({z : ℂ | z ∈ S ∧ f z=0 ∧ ‖z‖ < ‖errorFunctionZero complement k‖} : Set ℂ).ncard=k-1) ↔
    (Set.InjOn (fun z : ℂ => ‖z‖) {z : ℂ | z ∈ S ∧ f z = 0} ∧
        {z : ℂ | z ∈ S ∧ f z = 0}.Infinite) := by
  cases complement
  · exact Core.orderedZero_spec_iff
      (Core.finite_zeros_lt differentiable_erf_complex
          (ZeroClassification.erf_ofReal_ne_zero one_ne_zero) _)
  · exact Core.orderedZero_spec_iff
      (Core.finite_zeros_lt ZeroClassification.differentiable_erfc (x := 0)
          (by simp [erfc, erf_zero]) _)

/-- Identity under the stated parameter and domain assumptions: `StrictMonoOn (fun k =>
‖errorFunctionZero complement k‖) (Ici 1)`. -/
theorem errorFunctionZero_ordered (complement : Bool) :
    StrictMonoOn (fun k => ‖errorFunctionZero complement k‖) (Ici 1) := by
  cases complement
  · exact Core.orderedZero_strictMonoOn
      (Core.finite_zeros_lt differentiable_erf_complex
          (ZeroClassification.erf_ofReal_ne_zero one_ne_zero) _)
      (fun k hk => errorFunctionZero_spec false hk)
  · exact Core.orderedZero_strictMonoOn
      (Core.finite_zeros_lt ZeroClassification.differentiable_erfc (x := 0)
          (by simp [erfc, erf_zero]) _)
      (fun k hk => errorFunctionZero_spec true hk)

/-- Estimate under the stated parameter and domain assumptions: `erf z=0 ↔ z=0 ∨ ∃ k : ℕ, 1 ≤ k ∧
let u`. -/
theorem erf_zero_classification (z : ℂ) :
    erf z=0 ↔ z=0 ∨ ∃ k : ℕ, 1 ≤ k ∧ let u := errorFunctionZero false k; z=u ∨ z = -u ∨ z=star u ∨
        z = -star u := by
  set Q : Set ℂ := {z : ℂ | 0 < z.re ∧ 0 < z.im}
  have hfin := Core.finite_zeros_lt differentiable_erf_complex
    (ZeroClassification.erf_ofReal_ne_zero one_ne_zero) Q
  have hspec : ∀ k : ℕ, 1 ≤ k → orderedZero erf Q k ∈ Q ∧ erf (orderedZero erf Q k) = 0 ∧
      ({w : ℂ | w ∈ Q ∧ erf w = 0 ∧ ‖w‖ < ‖orderedZero erf Q k‖} : Set ℂ).ncard = k - 1 :=
    fun k hk => errorFunctionZero_spec false hk
  have hu : ∀ k, errorFunctionZero false k = orderedZero erf Q k := fun _ => rfl
  have hconj : ∀ w : ℂ, erf (star w) = star (erf w) := ZeroClassification.erf_conj
  have henum : ∀ w, w ∈ Q → erf w = 0 → ∃ k : ℕ, 1 ≤ k ∧ w = errorFunctionZero false k :=
    fun w hw hw0 => Core.eq_orderedZero hfin hspec hw hw0
  constructor
  · intro h0
    by_cases hz : z = 0
    · exact Or.inl hz
    right
    have hre : z.re ≠ 0 := by
      intro hre
      have hz' : z = I * (z.im : ℂ) := by apply Complex.ext <;> simp [hre]
      have him : z.im ≠ 0 := fun him => hz (Complex.ext (by simp [hre]) (by simp [him]))
      exact ZeroClassification.erf_I_mul_ofReal_ne_zero him (hz' ▸ h0)
    have him : z.im ≠ 0 := by
      intro him
      have hz' : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
      exact ZeroClassification.erf_ofReal_ne_zero hre (hz' ▸ h0)
    rcases hre.lt_or_gt with hr | hr <;> rcases him.lt_or_gt with hi | hi
    · obtain ⟨k, hk, hkz⟩ := henum (-z) ⟨by simp; linarith, by simp; linarith⟩
        (by rw [erf_negative, h0, neg_zero])
      exact ⟨k, hk, Or.inr (Or.inl (by rw [← hkz, neg_neg]))⟩
    · obtain ⟨k, hk, hkz⟩ := henum (-star z) ⟨by simp; linarith, by simp; linarith⟩
        (by rw [erf_negative, hconj, h0, star_zero, neg_zero])
      exact ⟨k, hk, Or.inr (Or.inr (Or.inr (by rw [← hkz, star_neg, star_star, neg_neg])))⟩
    · obtain ⟨k, hk, hkz⟩ := henum (star z) ⟨by simp; linarith, by simp; linarith⟩
        (by rw [hconj, h0, star_zero])
      exact ⟨k, hk, Or.inr (Or.inr (Or.inl (by rw [← hkz, star_star])))⟩
    · obtain ⟨k, hk, hkz⟩ := henum z ⟨hr, hi⟩ h0
      exact ⟨k, hk, Or.inl hkz⟩
  · rintro (rfl | ⟨k, hk, h⟩)
    · exact erf_zero
    have hu0 : erf (errorFunctionZero false k) = 0 := (hspec k hk).2.1
    rcases h with rfl | rfl | rfl | rfl
    · exact hu0
    · rw [erf_negative, hu0, neg_zero]
    · rw [hconj, hu0, star_zero]
    · rw [erf_negative, hconj, hu0, star_zero, neg_zero]

/-- Estimate under the stated parameter and domain assumptions: `erfc z=0 ↔ ∃ k : ℕ, 1 ≤ k ∧
(z=errorFunctionZero true k ∨ z=star (errorFunctionZero true k))`. -/
theorem erfc_zero_classification (z : ℂ) :
    erfc z=0 ↔ ∃ k : ℕ, 1 ≤ k ∧
        (z=errorFunctionZero true k ∨ z=star (errorFunctionZero true k)) := by
  set S : Set ℂ := {z : ℂ | π/2 < arg z ∧ arg z < 3*π/4}
  have hfin := Core.finite_zeros_lt ZeroClassification.differentiable_erfc (x := 0)
    (by simp [erfc, erf_zero]) S
  have hspec : ∀ k : ℕ, 1 ≤ k → orderedZero erfc S k ∈ S ∧ erfc (orderedZero erfc S k) = 0 ∧
      ({w : ℂ | w ∈ S ∧ erfc w = 0 ∧ ‖w‖ < ‖orderedZero erfc S k‖} : Set ℂ).ncard = k - 1 :=
    fun k hk => errorFunctionZero_spec true hk
  have hconj : ∀ w : ℂ, erfc (star w) = star (erfc w) := ZeroClassification.erfc_conj
  constructor
  · intro h0
    rcases ZeroClassification.erfc_zero_mem_sector h0 with hS | hS
    · obtain ⟨k, hk, hkz⟩ := Core.eq_orderedZero hfin hspec hS h0
      exact ⟨k, hk, Or.inl hkz⟩
    · obtain ⟨k, hk, hkz⟩ := Core.eq_orderedZero hfin hspec (z := star z) hS
        (by rw [hconj, h0, star_zero])
      exact ⟨k, hk, Or.inr (by rw [← star_star z]; exact congrArg star hkz)⟩
  · rintro ⟨k, hk, h | h⟩
    · rw [h]; exact (hspec k hk).2.1
    · rw [h, hconj]
      exact (congrArg star (hspec k hk).2.1).trans (star_zero _)

/-- Estimate under the stated parameter and domain assumptions: `faddeevaW z=0 ↔ ∃ k : ℕ, 1 ≤ k ∧
(z=I*errorFunctionZero true k ∨ z=I*star (errorFunctionZero true k))`. -/
theorem faddeevaW_zero_classification (z : ℂ) :
    faddeevaW z=0 ↔ ∃ k : ℕ, 1 ≤ k ∧
        (z=I*errorFunctionZero true k ∨ z=I*star (errorFunctionZero true k)) := by
  have hI : ∀ w : ℂ, -I * z = w ↔ z = I * w := fun w => by
    constructor
    · rintro rfl; ring_nf; rw [I_sq]; ring
    · rintro rfl; ring_nf; rw [I_sq]; ring
  rw [faddeevaW, mul_eq_zero, or_iff_right (Complex.exp_ne_zero _),
    erfc_zero_classification]
  simp only [hI]

/-- The stated relation follows from the given hypotheses: `let f`. -/
theorem fresnelFunctionZero_spec (sine : Bool) {k : ℕ} (hk : 1 ≤ k) :
    let f := if sine then fresnelS else fresnelC; 0 < arg (fresnelFunctionZero sine k) ∧
        arg (fresnelFunctionZero sine k) < π/4 ∧ f (fresnelFunctionZero sine k)=0 ∧
        ({z : ℂ | 0 < arg z ∧ arg z < π/4 ∧ f z=0 ∧ ‖z‖ < ‖fresnelFunctionZero sine k‖} : Set
        ℂ).ncard=k-1 := by
  sorry

/-- Identity under the stated parameter and domain assumptions: `StrictMonoOn (fun k =>
‖fresnelFunctionZero sine k‖) (Ici 1)`. -/
theorem fresnelFunctionZero_ordered (sine : Bool) :
    StrictMonoOn (fun k => ‖fresnelFunctionZero sine k‖) (Ici 1) := by
  obtain ⟨-, hC1, -, -, -, hS3⟩ := fresnel_zero_orders
  have hconv : ∀ (s : Bool) (k : ℕ), 1 ≤ k →
      let f := if s then fresnelS else fresnelC
      let S : Set ℂ := {z : ℂ | 0 < arg z ∧ arg z < π/4}
      orderedZero f S k ∈ S ∧ f (orderedZero f S k) = 0 ∧
        ({w : ℂ | w ∈ S ∧ f w = 0 ∧ ‖w‖ < ‖orderedZero f S k‖} : Set ℂ).ncard = k - 1 := by
    intro s k hk
    obtain ⟨h1, h2, h3, h4⟩ := fresnelFunctionZero_spec s hk
    refine ⟨⟨h1, h2⟩, h3, ?_⟩
    simp only [fresnelFunctionZero] at h4
    simpa only [Set.mem_ofPred_eq, and_assoc] using h4
  cases sine
  · have hx : ∃ x, fresnelC x ≠ 0 := by
      by_contra h
      push Not at h
      have : fresnelC = fun _ => 0 := funext h
      rw [this, deriv_const] at hC1
      exact zero_ne_one hC1
    obtain ⟨x, hx⟩ := hx
    exact Core.orderedZero_strictMonoOn
      (Core.finite_zeros_lt (fun z => (hasDerivAt_fresnelC_complex z).differentiableAt) hx _)
      (fun k hk => hconv false k hk)
  · have hx : ∃ x, fresnelS x ≠ 0 := by
      by_contra h
      push Not at h
      have : fresnelS = fun _ => 0 := funext h
      rw [this, iteratedDeriv_const] at hS3
      simp at hS3
      exact Real.pi_ne_zero (by exact_mod_cast hS3.symm)
    obtain ⟨x, hx⟩ := hx
    exact Core.orderedZero_strictMonoOn
      (Core.finite_zeros_lt (fun z => (hasDerivAt_fresnelS_complex z).differentiableAt) hx _)
      (fun k hk => hconv true k hk)

/-- Estimate under the stated parameter and domain assumptions: `(if sine then fresnelS z
else fresnelC z)=0 ↔ z=0 ∨ ∃ k : ℕ, 1 ≤ k ∧ let u`. -/
theorem fresnel_zero_classification (sine : Bool) (z : ℂ) :
    (if sine then fresnelS z else fresnelC z)=0 ↔ z=0 ∨ ∃ k : ℕ, 1 ≤ k ∧
        let u := fresnelFunctionZero sine k; z=u ∨ z = -u ∨ z=star u ∨ z = -star u ∨ z=I*u ∨ z =
        -I*u ∨ z=I*star u ∨ z = -I*star u := by
  obtain ⟨hC0, hC1, hS0, -, -, hS3⟩ := fresnel_zero_orders
  have hspec : ∀ k : ℕ, 1 ≤ k →
      let f := if sine then fresnelS else fresnelC
      let S : Set ℂ := {z : ℂ | 0 < arg z ∧ arg z < π/4}
      orderedZero f S k ∈ S ∧ f (orderedZero f S k) = 0 ∧
        ({w : ℂ | w ∈ S ∧ f w = 0 ∧ ‖w‖ < ‖orderedZero f S k‖} : Set ℂ).ncard = k - 1 := by
    intro k hk
    obtain ⟨h1, h2, h3, h4⟩ := fresnelFunctionZero_spec sine hk
    refine ⟨⟨h1, h2⟩, h3, ?_⟩
    simp only [fresnelFunctionZero] at h4
    simpa only [Set.mem_ofPred_eq, and_assoc] using h4
  have hstar : ∀ w : ℂ, star w = (starRingEnd ℂ) w := fun _ => rfl
  cases sine
  · have hx : ∃ x, fresnelC x ≠ 0 := ⟨1, by
      simpa using ZeroClassification.fresnelC_ofReal_ne_zero (x := 1) one_ne_zero⟩
    obtain ⟨x, hx⟩ := hx
    simpa [fresnelFunctionZero] using ZeroClassification.octant_classification (f := fresnelC)
      (Core.finite_zeros_lt (fun z => (hasDerivAt_fresnelC_complex z).differentiableAt) hx _)
      (hspec · ·) hC0
      (fun w => by rw [ZeroClassification.fresnelC_neg, neg_eq_zero])
      (fun w => by rw [hstar, ZeroClassification.fresnelC_conj, map_eq_zero])
      (fun w => by rw [ZeroClassification.fresnelC_I_mul, mul_eq_zero, or_iff_right I_ne_zero])
      (fun x hx => ZeroClassification.fresnelC_ofReal_ne_zero hx)
      (fun x hx => ZeroClassification.fresnelC_diag_ne_zero hx) z
  · have hx : ∃ x, fresnelS x ≠ 0 := ⟨1, by
      simpa using ZeroClassification.fresnelS_ofReal_ne_zero (x := 1) one_ne_zero⟩
    obtain ⟨x, hx⟩ := hx
    simpa [fresnelFunctionZero] using ZeroClassification.octant_classification (f := fresnelS)
      (Core.finite_zeros_lt (fun z => (hasDerivAt_fresnelS_complex z).differentiableAt) hx _)
      (hspec · ·) hS0
      (fun w => by rw [ZeroClassification.fresnelS_neg, neg_eq_zero])
      (fun w => by rw [hstar, ZeroClassification.fresnelS_conj, map_eq_zero])
      (fun w => by rw [ZeroClassification.fresnelS_I_mul, mul_eq_zero,
                     or_iff_right (neg_ne_zero.mpr I_ne_zero)])
      (fun x hx => ZeroClassification.fresnelS_ofReal_ne_zero hx)
      (fun x hx => ZeroClassification.fresnelS_diag_ne_zero hx) z

/-- The complete Fresnel-tail zero correspondence in DLMF §7.13(iv). -/
theorem fresnelTail_zero_classification (z : ℂ) :
    fresnelTail z=0 ↔ erfc (Real.sqrt π/(1+I)*z)=0 := by
  have h := fresnel_signed_erf z (ε:=1) (Or.inl rfl)
  have hz : fresnelZetaComplex 1 z = Real.sqrt π/(1+I)*z := by
    have h1 : (1+I) ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this
    unfold fresnelZetaComplex
    simp only [Complex.ofReal_one, one_mul]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have ht : fresnelTail z = (1+I)/2*erfc (Real.sqrt π/(1+I)*z) := by
    rw [fresnelTail, erfc, ← hz]
    simp only [Complex.ofReal_one, one_mul] at h
    linear_combination -h
  have hne : (1+I)/2 ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this
  rw [ht, mul_eq_zero, or_iff_right hne]

/-- Large error-function zero variable λ. -/
@[dlmf 7.13.E2, dlmf 7.13.E4]
def errorZeroLambda (k : ℕ) : ℝ :=
  Real.sqrt (((k : ℝ)-1/8)*π)

/-- Logarithmic error-function zero variable μ. -/
@[dlmf 7.13.E2, dlmf 7.13.E4]
def errorZeroMu (complement : Bool) (k : ℕ) : ℝ :=
  Real.log ((if complement then 2 else 1)*errorZeroLambda k*Real.sqrt (2*π))

/-- All-order polynomial-logarithmic expansions of both coordinates. -/
@[dlmf 7.13.E1, dlmf 7.13.E3]
theorem errorFunctionZero_asymptotic (complement : Bool) :
    ∃ p q : ℕ → Polynomial ℝ,
        (∀ μ : ℝ, (p 0).eval μ=(if complement then -1 else 1) ∧ (q 0).eval μ=1 ∧
        (p 1).eval μ=(if complement then 1 else -1)*μ/4 ∧ (q 1).eval μ=μ/4 ∧
        (p 2).eval μ=(if complement then -1 else 1)*(1-μ+μ^2/2)/16 ∧ (q 2).eval μ=(1-μ+μ^2/2)/16) ∧
        ∀ N : ℕ, (IsBigO atTop
        (fun k : ℕ => (errorFunctionZero complement (k+1)).re-∑ n ∈ Finset.range N,
        (p n).eval (errorZeroMu complement (k+1))*errorZeroLambda (k+1)^((1 : ℤ)-2*n))
        (fun k : ℕ => errorZeroLambda (k+1)^((1 : ℤ)-2*N)*(1+|errorZeroMu complement (k+1)|)^N)) ∧
        (IsBigO atTop (fun k : ℕ => (errorFunctionZero complement (k+1)).im-∑ n ∈ Finset.range N,
        (q n).eval (errorZeroMu complement (k+1))*errorZeroLambda (k+1)^((1 : ℤ)-2*n))
        (fun k : ℕ => errorZeroLambda
        (k+1)^((1 : ℤ)-2*N)*(1+|errorZeroMu complement (k+1)|)^N)) := by
  sorry

/-- Fresnel zero variable λ. -/
@[dlmf 7.13.E6, dlmf 7.13.E7]
def fresnelZeroLambda (sine : Bool) (k : ℕ) : ℝ :=
  if sine then 2*Real.sqrt k else Real.sqrt (4*(k : ℝ)-1)

/-- Fresnel zero logarithmic variable α. -/
@[dlmf 7.13.E6, dlmf 7.13.E7]
def fresnelZeroAlpha (sine : Bool) (k : ℕ) : ℝ :=
  2/π*Real.log (π*fresnelZeroLambda sine k)

/-- DLMF 7.13.5 to all orders: `x_n` and `y_n` expand in odd powers of `λ` with polynomial
coefficients in `α`, `x_n ∼ λ + (α(απ - 4)/(8π) + 1/π²) λ⁻³ + ⋯` and
`y_n ∼ α/(2λ) - 1/(π³λ³) + ⋯`. The coefficient of `λ^{1-2j}` in `x_n` has degree at most `j`
in `α`, and that of `λ^{-1-2j}` in `y_n` at most `j + 1`. -/
@[dlmf 7.13.E5]
theorem fresnelFunctionZero_asymptotic (sine : Bool) :
    ∃ p q : ℕ → Polynomial ℝ,
        (∀ α : ℝ, (p 0).eval α = 1 ∧ (p 1).eval α = 0 ∧
          (p 2).eval α = α * (α * π - 4) / (8 * π) + 1 / π ^ 2 ∧
          (q 0).eval α = α / 2 ∧ (q 1).eval α = -1 / π ^ 3) ∧ ∀ N : ℕ,
        (IsBigO atTop (fun k : ℕ => (fresnelFunctionZero sine (k+1)).re-∑ n ∈ Finset.range N,
        (p n).eval (fresnelZeroAlpha sine (k+1))*fresnelZeroLambda sine (k+1)^((1 : ℤ)-2*n))
        (fun k : ℕ => fresnelZeroLambda sine
        (k+1)^((1 : ℤ)-2*N)*(1+|fresnelZeroAlpha sine (k+1)|)^N)) ∧
        (IsBigO atTop (fun k : ℕ => (fresnelFunctionZero sine (k+1)).im-∑ n ∈ Finset.range N,
        (q n).eval (fresnelZeroAlpha sine (k+1))*fresnelZeroLambda sine (k+1)^((-1 : ℤ)-2*n))
        (fun k : ℕ => fresnelZeroLambda sine
        (k+1)^((-1 : ℤ)-2*N)*(1+|fresnelZeroAlpha sine (k+1)|)^(N+1))) := by
  sorry

end DLMF.Confluent
