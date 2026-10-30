/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.ModulusInversion

/-!
# Analytic properties of Jacobian elliptic quotients

Glaisher relations, theta-quotient holomorphy and reality of the Jacobian functions.

Source references and common attribution are retained in
`DLMF.JacobiElliptic.Basic`.
-/

@[expose] public section

open Complex DLMF.Elliptic

open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

/-! ### §22.2: theta-quotient forms, Glaisher relations, Neville form, parity -/

/-- Glaisher's reciprocal relation `pq = 1/qp` (DLMF 22.2.10, and the second equalities of
22.2.4–22.2.9). It holds identically, including Lean's junk values at poles. -/
@[dlmf 22.2.E10, dlmf 22.2.E4, dlmf 22.2.E5, dlmf 22.2.E6, dlmf 22.2.E7, dlmf 22.2.E8,
  dlmf 22.2.E9]
theorem jacobiPQk_eq_one_div (p q : JacobiLetter) (z k : ℂ) :
    jacobiPQk p q z k = 1 / jacobiPQk q p z k := by
  unfold jacobiPQk jacobiGlaisher
  by_cases hpq : p = q
  · subst hpq; simp
  · simp only [hpq, Ne.symm hpq, ↓reduceIte, one_div_div]

/-- Glaisher's quotient relation `pq = pr/qr` (DLMF 22.2.10) for three distinct letters, at
points where the `·r` functions are finite. -/
@[dlmf 22.2.E10]
theorem jacobiPQk_eq_div {p q r : JacobiLetter} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {z k : ℂ} (hr : jacobiRegulark r z k) :
    jacobiPQk p q z k = jacobiPQk p r z k / jacobiPQk q r z k := by
  unfold jacobiPQk jacobiGlaisher
  simp only [hpq, hpr, hqr, ↓reduceIte]
  rw [div_div_div_cancel_right₀ hr]

/-- The convention `pp = 1` (DLMF 22.2.10). -/
@[dlmf 22.2.E10]
theorem jacobiPQk_self (p : JacobiLetter) (z k : ℂ) : jacobiPQk p p z k = 1 := by
  simp [jacobiPQk, jacobiGlaisher]

/-- `ζ = πz/(2K)` is odd in `z`. -/
theorem jacobiZetak_neg (z k : ℂ) : jacobiZetak (-z) k = -jacobiZetak z k := by
  simp only [jacobiZetak]; ring

/-- The normalized theta functions: `θ_s` is odd, `θ_c, θ_d, θ_n` are even. -/
theorem jacobiLetterTheta_neg (p : JacobiLetter) (ζ τ : ℂ) :
    jacobiLetterTheta p (-ζ) τ = (if p = .s then -1 else 1) * jacobiLetterTheta p ζ τ := by
  cases p <;> simp [jacobiLetterTheta, jacobiThetaOneTau_neg, jacobiThetaTwoTau_neg,
    jacobiThetaThreeTau_neg, jacobiThetaFourTau_neg]

/-- Parity (DLMF §22.2): the six functions whose name contains the letter `s` are odd in `z`;
the other six are even. Holds for all `z` and `k`. -/
@[dlmf 22.2]
theorem jacobiPQk_neg (p q : JacobiLetter) (z k : ℂ) :
    jacobiPQk p q (-z) k =
      (if (p = .s) ≠ (q = .s) then -jacobiPQk p q z k else jacobiPQk p q z k) := by
  unfold jacobiPQk jacobiGlaisher
  rw [jacobiZetak_neg]
  by_cases hpq : p = q
  · subst hpq; simp
  · simp only [hpq, ↓reduceIte, jacobiLetterTheta_neg]
    cases p <;> cases q <;> simp_all <;> ring

/-- The theta-quotient forms of DLMF 22.2.4–22.2.9 with `τ = iK'/K`, `ζ = πz/(2K)`: e.g.
`sn(z, k) = θ₃(0)/θ₂(0) · θ₁(ζ)/θ₄(ζ)`. Uses only `Im τ > 0`. -/
@[dlmf 22.2.E4, dlmf 22.2.E5, dlmf 22.2.E6, dlmf 22.2.E7, dlmf 22.2.E8, dlmf 22.2.E9]
theorem jacobi_eq_theta_quotients {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiSnk z k = jacobiThetaThreeTau 0 (jacobiTauk k) / jacobiThetaTwoTau 0 (jacobiTauk k) *
        (jacobiThetaOneTau (jacobiZetak z k) (jacobiTauk k) /
          jacobiThetaFourTau (jacobiZetak z k) (jacobiTauk k)) ∧
      jacobiCnk z k = jacobiThetaFourTau 0 (jacobiTauk k) / jacobiThetaTwoTau 0 (jacobiTauk k) *
        (jacobiThetaTwoTau (jacobiZetak z k) (jacobiTauk k) /
          jacobiThetaFourTau (jacobiZetak z k) (jacobiTauk k)) ∧
      jacobiDnk z k = jacobiThetaFourTau 0 (jacobiTauk k) / jacobiThetaThreeTau 0 (jacobiTauk k) *
        (jacobiThetaThreeTau (jacobiZetak z k) (jacobiTauk k) /
          jacobiThetaFourTau (jacobiZetak z k) (jacobiTauk k)) ∧
      jacobiSdk z k = jacobiThetaThreeTau 0 (jacobiTauk k) ^ 2 /
        (jacobiThetaTwoTau 0 (jacobiTauk k) * jacobiThetaFourTau 0 (jacobiTauk k)) *
        (jacobiThetaOneTau (jacobiZetak z k) (jacobiTauk k) /
          jacobiThetaThreeTau (jacobiZetak z k) (jacobiTauk k)) ∧
      jacobiCdk z k = jacobiThetaThreeTau 0 (jacobiTauk k) / jacobiThetaTwoTau 0 (jacobiTauk k) *
        (jacobiThetaTwoTau (jacobiZetak z k) (jacobiTauk k) /
          jacobiThetaThreeTau (jacobiZetak z k) (jacobiTauk k)) ∧
      jacobiSck z k = jacobiThetaThreeTau 0 (jacobiTauk k) / jacobiThetaFourTau 0 (jacobiTauk k) *
        (jacobiThetaOneTau (jacobiZetak z k) (jacobiTauk k) /
          jacobiThetaTwoTau (jacobiZetak z k) (jacobiTauk k)) := by
  have hτ : 0 < (jacobiTauk k).im := jacobiTauk_im_pos hk
  have h2 := je22a_thetaTwo_zero_ne_zero hτ
  have h3 := je22a_thetaThree_zero_ne_zero hτ
  have h4 := je22a_thetaFour_zero_ne_zero hτ
  simp only [jacobiSnk, jacobiCnk, jacobiDnk, jacobiSdk, jacobiCdk, jacobiSck, jacobiPQk,
    jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp

/-! ### Holomorphy of the normalized theta functions in `(ζ, τ)` -/
/-- Quotients of holomorphic functions on `ℂ × ℂ`. -/
lemma p22R1_differentiableAt_div {f g : ℂ × ℂ → ℂ} {x : ℂ × ℂ} (hf : DifferentiableAt ℂ f x)
    (hg : DifferentiableAt ℂ g x) (h : g x ≠ 0) : DifferentiableAt ℂ (fun y => f y / g y) x := by
  exact (hf.mul (hg.inv h)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => by simp [div_eq_mul_inv])

/-- `(ζ, τ) ↦ θ₃(f(ζ, τ)|τ)` is holomorphic where `f` is and `Im τ > 0`. -/
lemma p22R1_differentiableAt_three_comp {f : ℂ × ℂ → ℂ} {x : ℂ × ℂ} (hf : DifferentiableAt ℂ f x)
    (hx : 0 < x.2.im) : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaThreeTau (f y) y.2) x := by
  have h1 := (hasFDerivAt_jacobiTheta₂ (f x / π) hx).differentiableAt
  have h2 : DifferentiableAt ℂ (fun y : ℂ × ℂ => (f y / π, y.2)) x :=
    (p22R1_differentiableAt_div hf (differentiableAt_const _) pi_ne_zero').prodMk
      differentiableAt_snd
  exact h1.comp (f := fun y : ℂ × ℂ => (f y / π, y.2)) x h2

/-- Differentiability at the specified argument: `DifferentiableAt ℂ (fun y : ℂ × ℂ =>
jacobiThetaTwoTau (f y) y.2) x`. -/
lemma p22R1_differentiableAt_two_comp {f : ℂ × ℂ → ℂ} {x : ℂ × ℂ} (hf : DifferentiableAt ℂ f x)
    (hx : 0 < x.2.im) : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaTwoTau (f y) y.2) x := by
  have h := p22R1_differentiableAt_three_comp (f := fun y => f y + π * y.2 / 2)
    (hf.add (p22R1_differentiableAt_div (differentiableAt_snd.const_mul (π : ℂ))
      (differentiableAt_const _) two_ne_zero)) hx
  have he : DifferentiableAt ℂ (fun y : ℂ × ℂ => cexp (π * I * y.2 / 4 + I * f y)) x :=
    ((p22R1_differentiableAt_div (differentiableAt_snd.const_mul (π * I : ℂ))
      (differentiableAt_const _) (by norm_num : (4 : ℂ) ≠ 0)).add (hf.const_mul I)).cexp
  exact he.mul h

/-- The normalized theta functions are jointly holomorphic in `(ζ, τ)` for `Im τ > 0`. -/
theorem p22R1_differentiableAt_letterTheta (p : JacobiLetter) {x : ℂ × ℂ} (hx : 0 < x.2.im) :
    DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiLetterTheta p y.1 y.2) x := by
  have c2 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaTwoTau 0 y.2) x :=
    p22R1_differentiableAt_two_comp (f := fun _ => 0) (differentiableAt_const _) hx
  have c3 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaThreeTau 0 y.2) x :=
    p22R1_differentiableAt_three_comp (f := fun _ => 0) (differentiableAt_const _) hx
  have c4 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaFourTau 0 y.2) x :=
    p22R1_differentiableAt_three_comp (f := fun _ => 0 + π / 2) (differentiableAt_const _) hx
  have d2 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaTwoTau y.1 y.2) x :=
    p22R1_differentiableAt_two_comp (f := fun y => y.1) differentiableAt_fst hx
  have d3 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaThreeTau y.1 y.2) x :=
    p22R1_differentiableAt_three_comp (f := fun y => y.1) differentiableAt_fst hx
  have d4 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaFourTau y.1 y.2) x :=
    p22R1_differentiableAt_three_comp (f := fun y => y.1 + π / 2)
      (differentiableAt_fst.add_const _) hx
  have d1 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaOneTau y.1 y.2) x := by
    have h := (p22R1_differentiableAt_two_comp (f := fun y => y.1 + π / 2)
      (differentiableAt_fst.add_const _) hx).const_mul (-1 : ℂ)
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp [jacobiThetaOneTau]
  have n2 := je22a_thetaTwo_zero_ne_zero hx
  have n3 := je22a_thetaThree_zero_ne_zero hx
  have n4 := je22a_thetaFour_zero_ne_zero hx
  cases p
  · exact (p22R1_differentiableAt_div c3 (c2.mul c4) (mul_ne_zero n2 n4)).mul d1
  · exact p22R1_differentiableAt_div d2 c2 n2
  · exact p22R1_differentiableAt_div d3 c3 n3
  · exact p22R1_differentiableAt_div d4 c4 n4

/-- DLMF 22.2.11: `pq(z, k) = θ_p(z|τ)/θ_q(z|τ)` in Neville's theta functions,
`τ = iK'/K` (22.2.12), for distinct letters. This needs Jacobi's `θ₁'(0) = θ₂θ₃θ₄(0)`
(DLMF 20.4.6). -/
@[dlmf 22.2.E11]
theorem jacobiPQk_eq_neville {k : ℂ} (hk : k ∈ jacobiModulusDomain) {p q : JacobiLetter}
    (hpq : p ≠ q) (z : ℂ) :
    jacobiPQk p q z k = jacobiNevilleTau p z (jacobiTauk k) / jacobiNevilleTau q z (jacobiTauk k) :=
        by
  have hτ := jacobiTauk_im_pos hk
  have hK := (jacobi_inversion_k hk).2.2
  have h2 := je22a_thetaTwo_zero_ne_zero hτ
  have h3 := je22a_thetaThree_zero_ne_zero hτ
  have h4 := je22a_thetaFour_zero_ne_zero hτ
  have hζ : jacobiZetak z k = z / jacobiThetaThreeTau 0 (jacobiTauk k) ^ 2 := by
    rw [jacobiZetak, ← hK, compEllIntKTau]
    field_simp [pi_ne_zero']
  have key : ∀ r : JacobiLetter, jacobiNevilleTau r z (jacobiTauk k) =
      jacobiLetterTheta r (jacobiZetak z k) (jacobiTauk k) := by
    intro r
    rw [hζ]
    cases r
    · have hd := DLMF.Theta.jacobiThetaOneDerivNullTau_eq_mul hτ
      simp only [jacobiNevilleTau, jacobiLetterTheta]
      rw [show deriv (fun w => jacobiThetaOneTau w (jacobiTauk k)) 0 =
        DLMF.Theta.jacobiThetaOneDerivNullTau (jacobiTauk k) from rfl, hd]
      simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
        DLMF.Theta.jacobiThetaFourNullTau]
      field_simp
    all_goals rfl
  rw [key, key, jacobiPQk, jacobiGlaisher]
  simp only [hpq, ↓reduceIte]

/-- DLMF §22.2: for fixed `z` each `pq(z, k)` is meromorphic in `k` (on
`jacobiModulusDomain`, where the principal-branch definition is used). -/
@[dlmf 22.2]
theorem jacobiPQk_meromorphicOn_modulus (p q : JacobiLetter) (z : ℂ) :
    MeromorphicOn (fun k => jacobiPQk p q z k) jacobiModulusDomain := by
  intro k hk
  have hU := p22R1_isOpen_domain.mem_nhds hk
  have hτ : DifferentiableAt ℂ jacobiTauk k := p22R1_differentiableOn_tau.differentiableAt hU
  have hK : DifferentiableAt ℂ compEllIntKk k := p22R1_differentiableOn_K.differentiableAt hU
  have hζ : DifferentiableAt ℂ (fun k => jacobiZetak z k) k :=
    (differentiableAt_const _).div (hK.const_mul _)
      (mul_ne_zero two_ne_zero (p22R1_compEllIntKk_ne_zero hk))
  have hpair : DifferentiableAt ℂ (fun k => (jacobiZetak z k, jacobiTauk k)) k := hζ.prodMk hτ
  -- each letter theta along the curve is holomorphic near `k`
  have hl : ∀ r : JacobiLetter, ∀ᶠ k' in nhds k,
      DifferentiableAt ℂ (fun k => jacobiLetterTheta r (jacobiZetak z k) (jacobiTauk k)) k' := by
    intro r
    filter_upwards [hU] with k' hk'
    have hU' := p22R1_isOpen_domain.mem_nhds hk'
    have hζ' : DifferentiableAt ℂ (fun k => jacobiZetak z k) k' :=
      (differentiableAt_const _).div
        ((p22R1_differentiableOn_K.differentiableAt hU').const_mul _)
        (mul_ne_zero two_ne_zero (p22R1_compEllIntKk_ne_zero hk'))
    exact (p22R1_differentiableAt_letterTheta r (x := (jacobiZetak z k', jacobiTauk k'))
      (jacobiTauk_im_pos hk')).comp (f := fun k => (jacobiZetak z k, jacobiTauk k)) k'
      (hζ'.prodMk (p22R1_differentiableOn_tau.differentiableAt hU'))
  have ha : ∀ r : JacobiLetter,
      AnalyticAt ℂ (fun k => jacobiLetterTheta r (jacobiZetak z k) (jacobiTauk k)) k :=
    fun r => DifferentiableOn.analyticAt (s := {k' | DifferentiableAt ℂ
      (fun k => jacobiLetterTheta r (jacobiZetak z k) (jacobiTauk k)) k'})
      (fun _ h => h.differentiableWithinAt) (hl r)
  unfold jacobiPQk jacobiGlaisher
  by_cases hpq : p = q
  · simp only [hpq, ↓reduceIte]; exact analyticAt_const.meromorphicAt
  · simp only [hpq, ↓reduceIte]
    exact (ha p).meromorphicAt.div (ha q).meromorphicAt

/-! ### Reality on the real axis -/
/-- `conj θ₃(ζ|τ) = θ₃(conj ζ| -conj τ)`. -/
lemma p22R1_conj_three (ζ τ : ℂ) :
    (starRingEnd ℂ) (jacobiThetaThreeTau ζ τ) =
      jacobiThetaThreeTau ((starRingEnd ℂ) ζ) (-(starRingEnd ℂ) τ) := by
  rw [jacobiThetaThreeTau, jacobiTheta₂_conj, jacobiThetaThreeTau, map_div₀, conj_ofReal]

/-- `conj θ₄(ζ|τ) = θ₄(conj ζ| -conj τ)`. -/
lemma p22R1_conj_four (ζ τ : ℂ) :
    (starRingEnd ℂ) (jacobiThetaFourTau ζ τ) =
      jacobiThetaFourTau ((starRingEnd ℂ) ζ) (-(starRingEnd ℂ) τ) := by
  rw [jacobiThetaFourTau, p22R1_conj_three, jacobiThetaFourTau]
  simp [map_add, map_div₀, conj_ofReal, map_ofNat]

/-- `conj θ₂(ζ|τ) = θ₂(conj ζ| -conj τ)`. -/
lemma p22R1_conj_two (ζ τ : ℂ) :
    (starRingEnd ℂ) (jacobiThetaTwoTau ζ τ) =
      jacobiThetaTwoTau ((starRingEnd ℂ) ζ) (-(starRingEnd ℂ) τ) := by
  set ζ' := (starRingEnd ℂ) ζ
  set τ' := -(starRingEnd ℂ) τ
  conv_rhs => rw [← jacobiThetaTwoTau_neg, jacobiThetaTwoTau,
    show -ζ' + π * τ' / 2 = -(ζ' - π * τ' / 2) by ring, jacobiThetaThreeTau_neg]
  rw [jacobiThetaTwoTau, map_mul, ← exp_conj, p22R1_conj_three]
  congr 2
  · simp only [map_add, map_mul, map_div₀, conj_ofReal, conj_I, map_ofNat, ζ', τ']; ring
  · simp only [map_add, map_mul, map_div₀, conj_ofReal, map_ofNat, ζ', τ']; ring

/-- `conj θ₁(ζ|τ) = θ₁(conj ζ| -conj τ)`. -/
lemma p22R1_conj_one (ζ τ : ℂ) :
    (starRingEnd ℂ) (jacobiThetaOneTau ζ τ) =
      jacobiThetaOneTau ((starRingEnd ℂ) ζ) (-(starRingEnd ℂ) τ) := by
  rw [jacobiThetaOneTau, map_neg, p22R1_conj_two, jacobiThetaOneTau]
  simp [map_add, map_div₀, conj_ofReal, map_ofNat]

/-- Conjugation of the normalized theta functions. -/
lemma p22R1_conj_letterTheta (p : JacobiLetter) (ζ τ : ℂ) :
    (starRingEnd ℂ) (jacobiLetterTheta p ζ τ) =
      jacobiLetterTheta p ((starRingEnd ℂ) ζ) (-(starRingEnd ℂ) τ) := by
  have h0 : (starRingEnd ℂ) (0 : ℂ) = 0 := map_zero _
  cases p <;> simp only [jacobiLetterTheta, map_mul, map_div₀, p22R1_conj_one, p22R1_conj_two,
    p22R1_conj_three, p22R1_conj_four, h0]

/-- Conjugation of Glaisher's quotients. -/
lemma p22R1_conj_glaisher (p q : JacobiLetter) (ζ τ : ℂ) :
    (starRingEnd ℂ) (jacobiGlaisher p q ζ τ) =
      jacobiGlaisher p q ((starRingEnd ℂ) ζ) (-(starRingEnd ℂ) τ) := by
  unfold jacobiGlaisher
  split_ifs
  · simp
  · rw [map_div₀, p22R1_conj_letterTheta, p22R1_conj_letterTheta]

/-- DLMF §22.2: for `0 < k < 1` all twelve functions are real for real `z`.
(`k = 0, 1` are the limiting forms of §22.5(ii).) -/
@[dlmf 22.2]
theorem jacobiPQk_real {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (p q : JacobiLetter) (x : ℝ) :
    (jacobiPQk p q x k).im = 0 := by
  obtain ⟨t, -, ht, -⟩ := p22R1_inversion_real hk0 hk1
  have hK := compEllIntKk_ofReal (k := k) (by nlinarith)
  have hζ : jacobiZetak x k = ((π * x / (2 * Real.compEllIntKm (k ^ 2)) : ℝ) : ℂ) := by
    rw [jacobiZetak, hK]; push_cast; ring
  have hτ : -(starRingEnd ℂ) (I * t) = I * t := by simp
  rw [← conj_eq_iff_im, jacobiPQk, ht, hζ, p22R1_conj_glaisher, conj_ofReal, hτ]

/-- `θ₃(·|τ)` is entire for `Im τ > 0`. -/
lemma je22a_differentiable_thetaThree {τ : ℂ} (hτ : 0 < τ.im) :
    Differentiable ℂ fun ζ => jacobiThetaThreeTau ζ τ := fun ζ =>
  (differentiableAt_jacobiTheta₂_fst (ζ / π) hτ).comp (f := fun w : ℂ => w / π) ζ
    ((differentiableAt_id).div_const _)

/-- The normalized theta functions are entire in `ζ` for `Im τ > 0`. -/
lemma je22a_differentiable_letterTheta {τ : ℂ} (hτ : 0 < τ.im) (p : JacobiLetter) :
    Differentiable ℂ fun ζ => jacobiLetterTheta p ζ τ := by
  have h3 := je22a_differentiable_thetaThree hτ
  have h2 : Differentiable ℂ fun ζ => jacobiThetaTwoTau ζ τ := fun ζ =>
    ((differentiable_exp.comp ((differentiable_const _).add
      (differentiable_id.const_mul I))) ζ).mul
      ((h3.comp (differentiable_id.add_const _)) ζ)
  cases p
  · exact (differentiable_const _).mul fun ζ => ((h2.comp (differentiable_id.add_const _)) ζ).neg
  · exact h2.div_const _
  · exact h3.div_const _
  · exact (h3.comp (differentiable_id.add_const _)).div_const _

/-- DLMF §22.2: for fixed `k` each Jacobian function is meromorphic in `z` (a quotient of entire
theta functions). -/
@[dlmf 22.2]
theorem jacobiPQk_meromorphicAt {k : ℂ} (hk : k ∈ jacobiModulusDomain) (p q : JacobiLetter)
    (z : ℂ) : MeromorphicAt (fun w => jacobiPQk p q w k) z := by
  have hτ := jacobiTauk_im_pos hk
  have hζ : Differentiable ℂ fun w => jacobiZetak w k := fun w =>
    ((differentiableAt_id.const_mul _).div_const _)
  unfold jacobiPQk jacobiGlaisher
  by_cases hpq : p = q
  · simp only [hpq, ↓reduceIte]; exact analyticAt_const.meromorphicAt
  · simp only [hpq, ↓reduceIte]
    exact (((je22a_differentiable_letterTheta hτ p).comp hζ).analyticAt z).meromorphicAt.div
      (((je22a_differentiable_letterTheta hτ q).comp hζ).analyticAt z).meromorphicAt

end DLMF.JacobiElliptic

end
end
