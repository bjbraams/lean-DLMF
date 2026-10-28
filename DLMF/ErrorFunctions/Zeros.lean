/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.ZeroClassification

/-!
# Zero distributions and asymptotics, DLMF §7.13

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results, numerical
tables (Tables 7.13.1–7.13.4) and application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.

The orderings and zero classifications (`errorFunctionZero_ordered`, `erf_zero_classification`,
`erfc_zero_classification`, `faddeevaW_zero_classification`, `fresnelFunctionZero_ordered`,
`fresnel_zero_classification`) are derived from the enumeration statements
`errorFunctionZero_spec` and `fresnelFunctionZero_spec` together with the zero localizations of
`DLMF/ErrorFunctions/ZeroClassification.lean`, so they depend on those two admissions only.
`errorFunctionZero_spec_iff` reduces `errorFunctionZero_spec` to distinct moduli and infinitely
many zeros in the sector.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- The selected upper-half-plane error-function zeros, indexed from one. -/
def errorFunctionZero (complement : Bool) (k : ℕ) : ℂ :=
  orderedZero (if complement then erfc else erf) (if complement then {z : ℂ | π/2 < arg z ∧ arg z < 3*π/4} else {z : ℂ | 0 < z.re ∧ 0 < z.im}) k

/-- Fresnel representatives in the first octant; the other octants follow by symmetry. -/
def fresnelFunctionZero (sine : Bool) (k : ℕ) : ℂ :=
  orderedZero (if sine then fresnelSinInt else fresnelCosInt) {z : ℂ | 0 < arg z ∧ arg z < π/4} k

/-- Identity under the stated parameter and domain assumptions: `erf 0=0 ∧ deriv erf 0=2/Real.sqrt
π`. -/
theorem erf_zero_simple  :
    erf 0=0 ∧ deriv erf 0=2/Real.sqrt π := by
  refine ⟨erf_zero, ?_⟩
  rw [(hasDerivAt_erf_complex 0).deriv]
  simp

/-- The simple C zero and triple S zero at the origin. -/
theorem fresnel_zero_orders  :
    fresnelCosInt 0=0 ∧ deriv fresnelCosInt 0=1 ∧ fresnelSinInt 0=0 ∧ deriv fresnelSinInt 0=0 ∧ iteratedDeriv 2 fresnelSinInt 0=0 ∧ iteratedDeriv 3 fresnelSinInt 0=π := by
  have hS1 : deriv fresnelSinInt = fun z => sin (π*z^2/2) :=
    funext fun z => (hasDerivAt_fresnelSinInt_complex z).deriv
  have hd2 (z : ℂ) : HasDerivAt (fun z : ℂ => sin (π*z^2/2)) (cos (π*z^2/2)*(π*z)) z := by
    have h := (((hasDerivAt_id' z).pow 2).const_mul (π:ℂ)).div_const 2 |>.csin
    convert h using 1
    simp only [Pi.pow_apply]
    ring
  have hS2 : iteratedDeriv 2 fresnelSinInt = fun z => cos (π*z^2/2)*(π*z) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hS1]
    exact funext fun z => (hd2 z).deriv
  have hd3 : HasDerivAt (fun z : ℂ => cos (π*z^2/2)*(π*z))
      (-sin (π*0^2/2)*(π*0)*(π*0)+cos (π*0^2/2)*π) 0 := by
    have h1 := (((hasDerivAt_id' (0:ℂ)).pow 2).const_mul (π:ℂ)).div_const 2 |>.ccos
    have h2 := ((hasDerivAt_id' (0:ℂ)).const_mul (π:ℂ))
    convert h1.mul h2 using 1
    simp
  refine ⟨primitive_zero _, ?_, primitive_zero _, ?_, ?_, ?_⟩
  · rw [(hasDerivAt_fresnelCosInt_complex 0).deriv]; simp
  · rw [hS1]; simp
  · rw [hS2]; simp
  · rw [iteratedDeriv_succ, hS2, hd3.deriv]; simp

/-- The stated relation follows from the given hypotheses: `let f`. -/
theorem errorFunctionZero_spec (complement : Bool) {k : ℕ} (hk : 1 ≤ k) :
    let f := if complement then erfc else erf; let S := if complement then {z : ℂ | π/2 < arg z ∧ arg z < 3*π/4} else {z : ℂ | 0 < z.re ∧ 0 < z.im}; errorFunctionZero complement k ∈ S ∧ f (errorFunctionZero complement k)=0 ∧ ({z : ℂ | z ∈ S ∧ f z=0 ∧ ‖z‖ < ‖errorFunctionZero complement k‖} : Set ℂ).ncard=k-1 := by
  sorry

/-- The enumeration `errorFunctionZero` is well defined for every index exactly when the zeros of
`erf` in the first quadrant (resp. of `erfc` in `π/2 < ph z < 3π/4`) have pairwise distinct moduli
and are infinitely many. This isolates the analytic content of `errorFunctionZero_spec`. -/
theorem errorFunctionZero_spec_iff (complement : Bool) :
    let f := if complement then erfc else erf
    let S := if complement then {z : ℂ | π/2 < arg z ∧ arg z < 3*π/4} else {z : ℂ | 0 < z.re ∧ 0 < z.im}
    (∀ k : ℕ, 1 ≤ k → errorFunctionZero complement k ∈ S ∧ f (errorFunctionZero complement k)=0 ∧
      ({z : ℂ | z ∈ S ∧ f z=0 ∧ ‖z‖ < ‖errorFunctionZero complement k‖} : Set ℂ).ncard=k-1) ↔
    (Set.InjOn (fun z : ℂ => ‖z‖) {z : ℂ | z ∈ S ∧ f z = 0} ∧ {z : ℂ | z ∈ S ∧ f z = 0}.Infinite) := by
  cases complement
  · exact zcnt_orderedZero_spec_iff
      (zcnt_finite_zeros_lt differentiable_erf_complex (zcnt_erf_ofReal_ne_zero one_ne_zero) _)
  · exact zcnt_orderedZero_spec_iff
      (zcnt_finite_zeros_lt zcnt_differentiable_erfc (x := 0) (by simp [erfc, erf_zero]) _)

/-- Identity under the stated parameter and domain assumptions: `StrictMonoOn (fun k =>
‖errorFunctionZero complement k‖) (Ici 1)`. -/
theorem errorFunctionZero_ordered (complement : Bool) :
    StrictMonoOn (fun k => ‖errorFunctionZero complement k‖) (Ici 1) := by
  cases complement
  · exact zcnt_orderedZero_strictMonoOn
      (zcnt_finite_zeros_lt differentiable_erf_complex (zcnt_erf_ofReal_ne_zero one_ne_zero) _)
      (fun k hk => errorFunctionZero_spec false hk)
  · exact zcnt_orderedZero_strictMonoOn
      (zcnt_finite_zeros_lt zcnt_differentiable_erfc (x := 0) (by simp [erfc, erf_zero]) _)
      (fun k hk => errorFunctionZero_spec true hk)

/-- Estimate under the stated parameter and domain assumptions: `erf z=0 ↔ z=0 ∨ ∃ k : ℕ, 1 ≤ k ∧
let u`. -/
theorem erf_zero_classification (z : ℂ) :
    erf z=0 ↔ z=0 ∨ ∃ k : ℕ, 1 ≤ k ∧ let u := errorFunctionZero false k; z=u ∨ z = -u ∨ z=star u ∨ z = -star u := by
  set Q : Set ℂ := {z : ℂ | 0 < z.re ∧ 0 < z.im}
  have hfin := zcnt_finite_zeros_lt differentiable_erf_complex
    (zcnt_erf_ofReal_ne_zero one_ne_zero) Q
  have hspec : ∀ k : ℕ, 1 ≤ k → orderedZero erf Q k ∈ Q ∧ erf (orderedZero erf Q k) = 0 ∧
      ({w : ℂ | w ∈ Q ∧ erf w = 0 ∧ ‖w‖ < ‖orderedZero erf Q k‖} : Set ℂ).ncard = k - 1 :=
    fun k hk => errorFunctionZero_spec false hk
  have hu : ∀ k, errorFunctionZero false k = orderedZero erf Q k := fun _ => rfl
  have hconj : ∀ w : ℂ, erf (star w) = star (erf w) := zcnt_erf_conj
  have henum : ∀ w, w ∈ Q → erf w = 0 → ∃ k : ℕ, 1 ≤ k ∧ w = errorFunctionZero false k :=
    fun w hw hw0 => zcnt_eq_orderedZero hfin hspec hw hw0
  constructor
  · intro h0
    by_cases hz : z = 0
    · exact Or.inl hz
    right
    have hre : z.re ≠ 0 := by
      intro hre
      have hz' : z = I * (z.im : ℂ) := by apply Complex.ext <;> simp [hre]
      have him : z.im ≠ 0 := fun him => hz (Complex.ext (by simp [hre]) (by simp [him]))
      exact zcnt_erf_I_mul_ofReal_ne_zero him (hz' ▸ h0)
    have him : z.im ≠ 0 := by
      intro him
      have hz' : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
      exact zcnt_erf_ofReal_ne_zero hre (hz' ▸ h0)
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
    erfc z=0 ↔ ∃ k : ℕ, 1 ≤ k ∧ (z=errorFunctionZero true k ∨ z=star (errorFunctionZero true k)) := by
  set S : Set ℂ := {z : ℂ | π/2 < arg z ∧ arg z < 3*π/4}
  have hfin := zcnt_finite_zeros_lt zcnt_differentiable_erfc (x := 0)
    (by simp [erfc, erf_zero]) S
  have hspec : ∀ k : ℕ, 1 ≤ k → orderedZero erfc S k ∈ S ∧ erfc (orderedZero erfc S k) = 0 ∧
      ({w : ℂ | w ∈ S ∧ erfc w = 0 ∧ ‖w‖ < ‖orderedZero erfc S k‖} : Set ℂ).ncard = k - 1 :=
    fun k hk => errorFunctionZero_spec true hk
  have hconj : ∀ w : ℂ, erfc (star w) = star (erfc w) := zcnt_erfc_conj
  constructor
  · intro h0
    rcases zcnt_erfc_zero_mem_sector h0 with hS | hS
    · obtain ⟨k, hk, hkz⟩ := zcnt_eq_orderedZero hfin hspec hS h0
      exact ⟨k, hk, Or.inl hkz⟩
    · obtain ⟨k, hk, hkz⟩ := zcnt_eq_orderedZero hfin hspec (z := star z) hS
        (by rw [hconj, h0, star_zero])
      exact ⟨k, hk, Or.inr (by rw [← star_star z]; exact congrArg star hkz)⟩
  · rintro ⟨k, hk, h | h⟩
    · rw [h]; exact (hspec k hk).2.1
    · rw [h, hconj]
      exact (congrArg star (hspec k hk).2.1).trans (star_zero _)

/-- Estimate under the stated parameter and domain assumptions: `faddeevaW z=0 ↔ ∃ k : ℕ, 1 ≤ k ∧
(z=I*errorFunctionZero true k ∨ z=I*star (errorFunctionZero true k))`. -/
theorem faddeevaW_zero_classification (z : ℂ) :
    faddeevaW z=0 ↔ ∃ k : ℕ, 1 ≤ k ∧ (z=I*errorFunctionZero true k ∨ z=I*star (errorFunctionZero true k)) := by
  have hI : ∀ w : ℂ, -I * z = w ↔ z = I * w := fun w => by
    constructor
    · rintro rfl; ring_nf; rw [I_sq]; ring
    · rintro rfl; ring_nf; rw [I_sq]; ring
  rw [faddeevaW, mul_eq_zero, or_iff_right (Complex.exp_ne_zero _),
    erfc_zero_classification]
  simp only [hI]

/-- The stated relation follows from the given hypotheses: `let f`. -/
theorem fresnelFunctionZero_spec (sine : Bool) {k : ℕ} (hk : 1 ≤ k) :
    let f := if sine then fresnelSinInt else fresnelCosInt; 0 < arg (fresnelFunctionZero sine k) ∧ arg (fresnelFunctionZero sine k) < π/4 ∧ f (fresnelFunctionZero sine k)=0 ∧ ({z : ℂ | 0 < arg z ∧ arg z < π/4 ∧ f z=0 ∧ ‖z‖ < ‖fresnelFunctionZero sine k‖} : Set ℂ).ncard=k-1 := by
  sorry

/-- Identity under the stated parameter and domain assumptions: `StrictMonoOn (fun k =>
‖fresnelFunctionZero sine k‖) (Ici 1)`. -/
theorem fresnelFunctionZero_ordered (sine : Bool) :
    StrictMonoOn (fun k => ‖fresnelFunctionZero sine k‖) (Ici 1) := by
  obtain ⟨-, hC1, -, -, -, hS3⟩ := fresnel_zero_orders
  have hconv : ∀ (s : Bool) (k : ℕ), 1 ≤ k →
      let f := if s then fresnelSinInt else fresnelCosInt
      let S : Set ℂ := {z : ℂ | 0 < arg z ∧ arg z < π/4}
      orderedZero f S k ∈ S ∧ f (orderedZero f S k) = 0 ∧
        ({w : ℂ | w ∈ S ∧ f w = 0 ∧ ‖w‖ < ‖orderedZero f S k‖} : Set ℂ).ncard = k - 1 := by
    intro s k hk
    obtain ⟨h1, h2, h3, h4⟩ := fresnelFunctionZero_spec s hk
    refine ⟨⟨h1, h2⟩, h3, ?_⟩
    simp only [fresnelFunctionZero] at h4
    simpa only [Set.mem_ofPred_eq, and_assoc] using h4
  cases sine
  · have hx : ∃ x, fresnelCosInt x ≠ 0 := by
      by_contra h
      push Not at h
      have : fresnelCosInt = fun _ => 0 := funext h
      rw [this, deriv_const] at hC1
      exact zero_ne_one hC1
    obtain ⟨x, hx⟩ := hx
    exact zcnt_orderedZero_strictMonoOn
      (zcnt_finite_zeros_lt (fun z => (hasDerivAt_fresnelCosInt_complex z).differentiableAt) hx _)
      (fun k hk => hconv false k hk)
  · have hx : ∃ x, fresnelSinInt x ≠ 0 := by
      by_contra h
      push Not at h
      have : fresnelSinInt = fun _ => 0 := funext h
      rw [this, iteratedDeriv_const] at hS3
      simp at hS3
      exact Real.pi_ne_zero (by exact_mod_cast hS3.symm)
    obtain ⟨x, hx⟩ := hx
    exact zcnt_orderedZero_strictMonoOn
      (zcnt_finite_zeros_lt (fun z => (hasDerivAt_fresnelSinInt_complex z).differentiableAt) hx _)
      (fun k hk => hconv true k hk)

/-- Estimate under the stated parameter and domain assumptions: `(if sine then fresnelSinInt z
else fresnelCosInt z)=0 ↔ z=0 ∨ ∃ k : ℕ, 1 ≤ k ∧ let u`. -/
theorem fresnel_zero_classification (sine : Bool) (z : ℂ) :
    (if sine then fresnelSinInt z else fresnelCosInt z)=0 ↔ z=0 ∨ ∃ k : ℕ, 1 ≤ k ∧ let u := fresnelFunctionZero sine k; z=u ∨ z = -u ∨ z=star u ∨ z = -star u ∨ z=I*u ∨ z = -I*u ∨ z=I*star u ∨ z = -I*star u := by
  obtain ⟨hC0, hC1, hS0, -, -, hS3⟩ := fresnel_zero_orders
  have hspec : ∀ k : ℕ, 1 ≤ k →
      let f := if sine then fresnelSinInt else fresnelCosInt
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
  · have hx : ∃ x, fresnelCosInt x ≠ 0 := ⟨1, by
      simpa using zcnt_fresnelCosInt_ofReal_ne_zero (x := 1) one_ne_zero⟩
    obtain ⟨x, hx⟩ := hx
    simpa [fresnelFunctionZero] using zcnt_octant_classification (f := fresnelCosInt)
      (zcnt_finite_zeros_lt (fun z => (hasDerivAt_fresnelCosInt_complex z).differentiableAt) hx _)
      (hspec · ·) hC0
      (fun w => by rw [zcnt_fresnelCosInt_neg, neg_eq_zero])
      (fun w => by rw [hstar, zcnt_fresnelCosInt_conj, map_eq_zero])
      (fun w => by rw [zcnt_fresnelCosInt_I_mul, mul_eq_zero, or_iff_right I_ne_zero])
      (fun x hx => zcnt_fresnelCosInt_ofReal_ne_zero hx)
      (fun x hx => zcnt_fresnelCosInt_diag_ne_zero hx) z
  · have hx : ∃ x, fresnelSinInt x ≠ 0 := ⟨1, by
      simpa using zcnt_fresnelSinInt_ofReal_ne_zero (x := 1) one_ne_zero⟩
    obtain ⟨x, hx⟩ := hx
    simpa [fresnelFunctionZero] using zcnt_octant_classification (f := fresnelSinInt)
      (zcnt_finite_zeros_lt (fun z => (hasDerivAt_fresnelSinInt_complex z).differentiableAt) hx _)
      (hspec · ·) hS0
      (fun w => by rw [zcnt_fresnelSinInt_neg, neg_eq_zero])
      (fun w => by rw [hstar, zcnt_fresnelSinInt_conj, map_eq_zero])
      (fun w => by rw [zcnt_fresnelSinInt_I_mul, mul_eq_zero, or_iff_right (neg_ne_zero.mpr I_ne_zero)])
      (fun x hx => zcnt_fresnelSinInt_ofReal_ne_zero hx)
      (fun x hx => zcnt_fresnelSinInt_diag_ne_zero hx) z

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
    ∃ p q : ℕ → Polynomial ℝ, (∀ μ : ℝ, (p 0).eval μ=(if complement then -1 else 1) ∧ (q 0).eval μ=1 ∧ (p 1).eval μ=(if complement then 1 else -1)*μ/4 ∧ (q 1).eval μ=μ/4 ∧ (p 2).eval μ=(if complement then -1 else 1)*(1-μ+μ^2/2)/16 ∧ (q 2).eval μ=(1-μ+μ^2/2)/16) ∧ ∀ N : ℕ, (IsBigO atTop (fun k : ℕ => (errorFunctionZero complement (k+1)).re-∑ n ∈ Finset.range N, (p n).eval (errorZeroMu complement (k+1))*errorZeroLambda (k+1)^((1 : ℤ)-2*n)) (fun k : ℕ => errorZeroLambda (k+1)^((1 : ℤ)-2*N)*(1+|errorZeroMu complement (k+1)|)^N)) ∧ (IsBigO atTop (fun k : ℕ => (errorFunctionZero complement (k+1)).im-∑ n ∈ Finset.range N, (q n).eval (errorZeroMu complement (k+1))*errorZeroLambda (k+1)^((1 : ℤ)-2*n)) (fun k : ℕ => errorZeroLambda (k+1)^((1 : ℤ)-2*N)*(1+|errorZeroMu complement (k+1)|)^N)) := by
  sorry

/-- Fresnel zero variable λ. -/
@[dlmf 7.13.E6, dlmf 7.13.E7]
def fresnelZeroLambda (sine : Bool) (k : ℕ) : ℝ :=
  if sine then 2*Real.sqrt k else Real.sqrt (4*(k : ℝ)-1)

/-- Fresnel zero logarithmic variable α. -/
@[dlmf 7.13.E6, dlmf 7.13.E7]
def fresnelZeroAlpha (sine : Bool) (k : ℕ) : ℝ :=
  2/π*Real.log (π*fresnelZeroLambda sine k)

/-- All-order Fresnel zero expansions with logarithmic-polynomial coefficients. -/
@[dlmf 7.13.E5]
theorem fresnelFunctionZero_asymptotic (sine : Bool) :
    ∃ p q : ℕ → Polynomial ℝ, (∀ α : ℝ, (p 0).eval α=1 ∧ (p 1).eval α=α*(α*π-4)/(8*π) ∧ (q 0).eval α=α/2) ∧ ∀ N : ℕ, (IsBigO atTop (fun k : ℕ => (fresnelFunctionZero sine (k+1)).re-∑ n ∈ Finset.range N, (p n).eval (fresnelZeroAlpha sine (k+1))*fresnelZeroLambda sine (k+1)^((1 : ℤ)-4*n)) (fun k : ℕ => fresnelZeroLambda sine (k+1)^((1 : ℤ)-4*N)*(1+|fresnelZeroAlpha sine (k+1)|)^(2*N))) ∧ (IsBigO atTop (fun k : ℕ => (fresnelFunctionZero sine (k+1)).im-∑ n ∈ Finset.range N, (q n).eval (fresnelZeroAlpha sine (k+1))*fresnelZeroLambda sine (k+1)^((-1 : ℤ)-4*n)) (fun k : ℕ => fresnelZeroLambda sine (k+1)^((-1 : ℤ)-4*N)*(1+|fresnelZeroAlpha sine (k+1)|)^(2*N+1))) := by
  sorry

end DLMF.Confluent
