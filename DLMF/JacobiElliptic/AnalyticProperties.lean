/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic.Properties
public import DLMF.JacobiElliptic.ModulusInversion

/-!
# Analytic properties of Jacobian elliptic quotients

The theta-quotient and Neville forms, meromorphy in `z` and in `k`, and reality of the
Jacobian elliptic functions (DLMF §22.2). Glaisher's relations and parity are in
`DLMF.JacobiElliptic.Basic.Properties`.

## Main results

* `jacobi_eq_theta_quotients`: the theta-quotient forms DLMF 22.2.4–22.2.9.
* `jacobiPQ_eq_neville`: DLMF 22.2.11 in Neville's theta functions, `τ = iK'/K`.
* `jacobiPQ_meromorphicAt`, `jacobiPQ_meromorphicOn_modulus`: meromorphy in `z` for fixed
  `k`, and in `k` for fixed `z` on `jacobiModulusDomain`.
* `jacobiPQ_real`: for `0 < k < 1` all twelve functions are real for real `z`.
-/

@[expose] public section

open Complex DLMF.Elliptic

open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

open DLMF.EllipticIntegrals (completeEllipticK completeEllipticKPrime)

/-! ### §22.2: theta-quotient forms and Neville form -/

/-- The theta-quotient forms of DLMF 22.2.4–22.2.9 with `τ = iK'/K`, `ζ = πz/(2K)`: e.g.
`sn(z, k) = θ₃(0)/θ₂(0) · θ₁(ζ)/θ₄(ζ)`. Uses only `Im τ > 0`. -/
@[dlmf 22.2.E4, dlmf 22.2.E5, dlmf 22.2.E6, dlmf 22.2.E7, dlmf 22.2.E8, dlmf 22.2.E9]
theorem jacobi_eq_theta_quotients {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiSn z k = jacobiThetaThreeTau 0 (jacobiTau k) / jacobiThetaTwoTau 0 (jacobiTau k) *
        (jacobiThetaOneTau (jacobiThetaArgument z k) (jacobiTau k) /
          jacobiThetaFourTau (jacobiThetaArgument z k) (jacobiTau k)) ∧
      jacobiCn z k = jacobiThetaFourTau 0 (jacobiTau k) / jacobiThetaTwoTau 0 (jacobiTau k) *
        (jacobiThetaTwoTau (jacobiThetaArgument z k) (jacobiTau k) /
          jacobiThetaFourTau (jacobiThetaArgument z k) (jacobiTau k)) ∧
      jacobiDn z k = jacobiThetaFourTau 0 (jacobiTau k) / jacobiThetaThreeTau 0 (jacobiTau k) *
        (jacobiThetaThreeTau (jacobiThetaArgument z k) (jacobiTau k) /
          jacobiThetaFourTau (jacobiThetaArgument z k) (jacobiTau k)) ∧
      jacobiSd z k = jacobiThetaThreeTau 0 (jacobiTau k) ^ 2 /
        (jacobiThetaTwoTau 0 (jacobiTau k) * jacobiThetaFourTau 0 (jacobiTau k)) *
        (jacobiThetaOneTau (jacobiThetaArgument z k) (jacobiTau k) /
          jacobiThetaThreeTau (jacobiThetaArgument z k) (jacobiTau k)) ∧
      jacobiCd z k = jacobiThetaThreeTau 0 (jacobiTau k) / jacobiThetaTwoTau 0 (jacobiTau k) *
        (jacobiThetaTwoTau (jacobiThetaArgument z k) (jacobiTau k) /
          jacobiThetaThreeTau (jacobiThetaArgument z k) (jacobiTau k)) ∧
      jacobiSc z k = jacobiThetaThreeTau 0 (jacobiTau k) / jacobiThetaFourTau 0 (jacobiTau k) *
        (jacobiThetaOneTau (jacobiThetaArgument z k) (jacobiTau k) /
          jacobiThetaTwoTau (jacobiThetaArgument z k) (jacobiTau k)) := by
  have hτ : 0 < (jacobiTau k).im := jacobiTau_im_pos hk
  have h2 := jacobiThetaTwoTau_zero_ne_zero hτ
  have h3 := jacobiThetaThreeTau_zero_ne_zero hτ
  have h4 := jacobiThetaFourTau_zero_ne_zero hτ
  simp only [jacobiSn, jacobiCn, jacobiDn, jacobiSd, jacobiCd, jacobiSc, jacobiPQ,
    jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp

/-! ### Holomorphy of the normalized theta functions in `(ζ, τ)` -/
/-- Quotients of holomorphic functions on `ℂ × ℂ`. -/
private lemma differentiableAt_div_prod {f g : ℂ × ℂ → ℂ} {x : ℂ × ℂ} (hf : DifferentiableAt ℂ f x)
    (hg : DifferentiableAt ℂ g x) (h : g x ≠ 0) : DifferentiableAt ℂ (fun y => f y / g y) x := by
  exact (hf.mul (hg.inv h)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => by simp [div_eq_mul_inv])

/-- `(ζ, τ) ↦ θ₃(f(ζ, τ)|τ)` is holomorphic where `f` is and `Im τ > 0`. -/
private lemma differentiableAt_jacobiThetaThreeTau_comp {f : ℂ × ℂ → ℂ} {x : ℂ × ℂ}
    (hf : DifferentiableAt ℂ f x)
    (hx : 0 < x.2.im) : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaThreeTau (f y) y.2) x := by
  have h1 := (hasFDerivAt_jacobiTheta₂ (f x / π) hx).differentiableAt
  have h2 : DifferentiableAt ℂ (fun y : ℂ × ℂ => (f y / π, y.2)) x :=
    (differentiableAt_div_prod hf (differentiableAt_const _) pi_ne_zero').prodMk
      differentiableAt_snd
  exact h1.comp (f := fun y : ℂ × ℂ => (f y / π, y.2)) x h2

/-- Differentiability at the specified argument: `DifferentiableAt ℂ (fun y : ℂ × ℂ =>
jacobiThetaTwoTau (f y) y.2) x`. -/
private lemma differentiableAt_jacobiThetaTwoTau_comp {f : ℂ × ℂ → ℂ} {x : ℂ × ℂ}
    (hf : DifferentiableAt ℂ f x)
    (hx : 0 < x.2.im) : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaTwoTau (f y) y.2) x := by
  have h := differentiableAt_jacobiThetaThreeTau_comp (f := fun y => f y + π * y.2 / 2)
    (hf.add (differentiableAt_div_prod (differentiableAt_snd.const_mul (π : ℂ))
      (differentiableAt_const _) two_ne_zero)) hx
  have he : DifferentiableAt ℂ (fun y : ℂ × ℂ => cexp (π * I * y.2 / 4 + I * f y)) x :=
    ((differentiableAt_div_prod (differentiableAt_snd.const_mul (π * I : ℂ))
      (differentiableAt_const _) (by norm_num : (4 : ℂ) ≠ 0)).add (hf.const_mul I)).cexp
  exact he.mul h

/-- The normalized theta functions are jointly holomorphic in `(ζ, τ)` for `Im τ > 0`. -/
theorem differentiableAt_jacobiLetterTheta_uncurry (p : JacobiLetter) {x : ℂ × ℂ}
    (hx : 0 < x.2.im) :
    DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiLetterTheta p y.1 y.2) x := by
  have c2 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaTwoTau 0 y.2) x :=
    differentiableAt_jacobiThetaTwoTau_comp (f := fun _ => 0) (differentiableAt_const _) hx
  have c3 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaThreeTau 0 y.2) x :=
    differentiableAt_jacobiThetaThreeTau_comp (f := fun _ => 0) (differentiableAt_const _) hx
  have c4 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaFourTau 0 y.2) x :=
    differentiableAt_jacobiThetaThreeTau_comp (f := fun _ => 0 + π / 2)
        (differentiableAt_const _) hx
  have d2 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaTwoTau y.1 y.2) x :=
    differentiableAt_jacobiThetaTwoTau_comp (f := fun y => y.1) differentiableAt_fst hx
  have d3 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaThreeTau y.1 y.2) x :=
    differentiableAt_jacobiThetaThreeTau_comp (f := fun y => y.1) differentiableAt_fst hx
  have d4 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaFourTau y.1 y.2) x :=
    differentiableAt_jacobiThetaThreeTau_comp (f := fun y => y.1 + π / 2)
      (differentiableAt_fst.add_const _) hx
  have d1 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaOneTau y.1 y.2) x := by
    have h := (differentiableAt_jacobiThetaTwoTau_comp (f := fun y => y.1 + π / 2)
      (differentiableAt_fst.add_const _) hx).const_mul (-1 : ℂ)
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp [jacobiThetaOneTau]
  have n2 := jacobiThetaTwoTau_zero_ne_zero hx
  have n3 := jacobiThetaThreeTau_zero_ne_zero hx
  have n4 := jacobiThetaFourTau_zero_ne_zero hx
  cases p
  · exact (differentiableAt_div_prod c3 (c2.mul c4) (mul_ne_zero n2 n4)).mul d1
  · exact differentiableAt_div_prod d2 c2 n2
  · exact differentiableAt_div_prod d3 c3 n3
  · exact differentiableAt_div_prod d4 c4 n4

/-- DLMF 22.2.11: `pq(z, k) = θ_p(z|τ)/θ_q(z|τ)` in Neville's theta functions,
`τ = iK'/K` (22.2.12), for distinct letters. This needs Jacobi's `θ₁'(0) = θ₂θ₃θ₄(0)`
(DLMF 20.4.6). -/
@[dlmf 22.2.E11]
theorem jacobiPQ_eq_neville {k : ℂ} (hk : k ∈ jacobiModulusDomain) {p q : JacobiLetter}
    (hpq : p ≠ q) (z : ℂ) :
    jacobiPQ p q z k = nevilleThetaOfTau p z (jacobiTau k) / nevilleThetaOfTau q z (jacobiTau k) :=
        by
  have hτ := jacobiTau_im_pos hk
  have hK := (jacobi_inversion_k hk).2.2
  have h2 := jacobiThetaTwoTau_zero_ne_zero hτ
  have h3 := jacobiThetaThreeTau_zero_ne_zero hτ
  have h4 := jacobiThetaFourTau_zero_ne_zero hτ
  have hζ : jacobiThetaArgument z k = z / jacobiThetaThreeTau 0 (jacobiTau k) ^ 2 := by
    rw [jacobiThetaArgument, ← hK, completeEllipticKOfTau]
    field_simp [pi_ne_zero']
  have key : ∀ r : JacobiLetter, nevilleThetaOfTau r z (jacobiTau k) =
      jacobiLetterTheta r (jacobiThetaArgument z k) (jacobiTau k) := by
    intro r
    rw [hζ]
    cases r
    · have hd := DLMF.Theta.jacobiThetaOneDerivNullTau_eq_mul hτ
      simp only [nevilleThetaOfTau, jacobiLetterTheta]
      rw [show deriv (fun w => jacobiThetaOneTau w (jacobiTau k)) 0 =
        DLMF.Theta.jacobiThetaOneDerivNullTau (jacobiTau k) from rfl, hd]
      simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
        DLMF.Theta.jacobiThetaFourNullTau]
      field_simp
    all_goals rfl
  rw [key, key, jacobiPQ, jacobiGlaisher]
  simp only [hpq, ↓reduceIte]

/-- DLMF §22.2: for fixed `z` each `pq(z, k)` is meromorphic in `k` (on
`jacobiModulusDomain`, where the principal-branch definition is used). -/
@[dlmf 22.2]
theorem jacobiPQ_meromorphicOn_modulus (p q : JacobiLetter) (z : ℂ) :
    MeromorphicOn (fun k => jacobiPQ p q z k) jacobiModulusDomain := by
  intro k hk
  have hU := isOpen_jacobiModulusDomain.mem_nhds hk
  have hτ : DifferentiableAt ℂ jacobiTau k := differentiableOn_jacobiTau.differentiableAt hU
  have hK : DifferentiableAt ℂ completeEllipticK k :=
      differentiableOn_completeEllipticK.differentiableAt hU
  have hζ : DifferentiableAt ℂ (fun k => jacobiThetaArgument z k) k :=
    (differentiableAt_const _).div (hK.const_mul _)
      (mul_ne_zero two_ne_zero (completeEllipticK_ne_zero_of_mem_jacobiModulusDomain hk))
  have hpair : DifferentiableAt ℂ (fun k => (jacobiThetaArgument z k, jacobiTau k))
      k := hζ.prodMk hτ
  -- each letter theta along the curve is holomorphic near `k`
  have hl : ∀ r : JacobiLetter, ∀ᶠ k' in nhds k,
      DifferentiableAt ℂ (fun k =>
          jacobiLetterTheta r (jacobiThetaArgument z k) (jacobiTau k)) k' := by
    intro r
    filter_upwards [hU] with k' hk'
    have hU' := isOpen_jacobiModulusDomain.mem_nhds hk'
    have hζ' : DifferentiableAt ℂ (fun k => jacobiThetaArgument z k) k' :=
      (differentiableAt_const _).div
        ((differentiableOn_completeEllipticK.differentiableAt hU').const_mul _)
        (mul_ne_zero two_ne_zero (completeEllipticK_ne_zero_of_mem_jacobiModulusDomain hk'))
    exact (differentiableAt_jacobiLetterTheta_uncurry r
        (x := (jacobiThetaArgument z k', jacobiTau k'))
      (jacobiTau_im_pos hk')).comp (f := fun k => (jacobiThetaArgument z k, jacobiTau k)) k'
      (hζ'.prodMk (differentiableOn_jacobiTau.differentiableAt hU'))
  have ha : ∀ r : JacobiLetter,
      AnalyticAt ℂ (fun k => jacobiLetterTheta r (jacobiThetaArgument z k) (jacobiTau k)) k :=
    fun r => DifferentiableOn.analyticAt (s := {k' | DifferentiableAt ℂ
      (fun k => jacobiLetterTheta r (jacobiThetaArgument z k) (jacobiTau k)) k'})
      (fun _ h => h.differentiableWithinAt) (hl r)
  unfold jacobiPQ jacobiGlaisher
  by_cases hpq : p = q
  · simp only [hpq, ↓reduceIte]; exact analyticAt_const.meromorphicAt
  · simp only [hpq, ↓reduceIte]
    exact (ha p).meromorphicAt.div (ha q).meromorphicAt

/-! ### Reality on the real axis -/
/-- `conj θ₃(ζ|τ) = θ₃(conj ζ| -conj τ)`. -/
private lemma conj_jacobiThetaThreeTau (ζ τ : ℂ) :
    (starRingEnd ℂ) (jacobiThetaThreeTau ζ τ) =
      jacobiThetaThreeTau ((starRingEnd ℂ) ζ) (-(starRingEnd ℂ) τ) := by
  rw [jacobiThetaThreeTau, jacobiTheta₂_conj, jacobiThetaThreeTau, map_div₀, conj_ofReal]

/-- `conj θ₄(ζ|τ) = θ₄(conj ζ| -conj τ)`. -/
private lemma conj_jacobiThetaFourTau (ζ τ : ℂ) :
    (starRingEnd ℂ) (jacobiThetaFourTau ζ τ) =
      jacobiThetaFourTau ((starRingEnd ℂ) ζ) (-(starRingEnd ℂ) τ) := by
  rw [jacobiThetaFourTau, conj_jacobiThetaThreeTau, jacobiThetaFourTau]
  simp [map_add, map_div₀, conj_ofReal, map_ofNat]

/-- `conj θ₂(ζ|τ) = θ₂(conj ζ| -conj τ)`. -/
private lemma conj_jacobiThetaTwoTau (ζ τ : ℂ) :
    (starRingEnd ℂ) (jacobiThetaTwoTau ζ τ) =
      jacobiThetaTwoTau ((starRingEnd ℂ) ζ) (-(starRingEnd ℂ) τ) := by
  set ζ' := (starRingEnd ℂ) ζ
  set τ' := -(starRingEnd ℂ) τ
  conv_rhs => rw [← jacobiThetaTwoTau_neg, jacobiThetaTwoTau,
    show -ζ' + π * τ' / 2 = -(ζ' - π * τ' / 2) by ring, jacobiThetaThreeTau_neg]
  rw [jacobiThetaTwoTau, map_mul, ← exp_conj, conj_jacobiThetaThreeTau]
  congr 2
  · simp only [map_add, map_mul, map_div₀, conj_ofReal, conj_I, map_ofNat, ζ', τ']; ring
  · simp only [map_add, map_mul, map_div₀, conj_ofReal, map_ofNat, ζ', τ']; ring

/-- `conj θ₁(ζ|τ) = θ₁(conj ζ| -conj τ)`. -/
private lemma conj_jacobiThetaOneTau (ζ τ : ℂ) :
    (starRingEnd ℂ) (jacobiThetaOneTau ζ τ) =
      jacobiThetaOneTau ((starRingEnd ℂ) ζ) (-(starRingEnd ℂ) τ) := by
  rw [jacobiThetaOneTau, map_neg, conj_jacobiThetaTwoTau, jacobiThetaOneTau]
  simp [map_add, map_div₀, conj_ofReal, map_ofNat]

/-- Conjugation of the normalized theta functions. -/
private lemma conj_jacobiLetterTheta (p : JacobiLetter) (ζ τ : ℂ) :
    (starRingEnd ℂ) (jacobiLetterTheta p ζ τ) =
      jacobiLetterTheta p ((starRingEnd ℂ) ζ) (-(starRingEnd ℂ) τ) := by
  have h0 : (starRingEnd ℂ) (0 : ℂ) = 0 := map_zero _
  cases p <;> simp only
      [jacobiLetterTheta, map_mul, map_div₀, conj_jacobiThetaOneTau, conj_jacobiThetaTwoTau,
    conj_jacobiThetaThreeTau, conj_jacobiThetaFourTau, h0]

/-- Conjugation of Glaisher's quotients. -/
private lemma conj_jacobiGlaisher (p q : JacobiLetter) (ζ τ : ℂ) :
    (starRingEnd ℂ) (jacobiGlaisher p q ζ τ) =
      jacobiGlaisher p q ((starRingEnd ℂ) ζ) (-(starRingEnd ℂ) τ) := by
  unfold jacobiGlaisher
  split_ifs
  · simp
  · rw [map_div₀, conj_jacobiLetterTheta, conj_jacobiLetterTheta]

/-- DLMF §22.2: for `0 < k < 1` all twelve functions are real for real `z`.
(`k = 0, 1` are the limiting forms of §22.5(ii).) -/
@[dlmf 22.2]
theorem jacobiPQ_real {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (p q : JacobiLetter) (x : ℝ) :
    (jacobiPQ p q x k).im = 0 := by
  obtain ⟨t, -, ht, -⟩ := exists_jacobiTau_eq_I_mul_of_real hk0 hk1
  have hK := completeEllipticK_ofReal (k := k) (by nlinarith)
  have hζ : jacobiThetaArgument x k =
      ((π * x / (2 * Real.completeEllipticKOfParameter (k ^ 2)) : ℝ) : ℂ) := by
    rw [jacobiThetaArgument, hK]; push_cast; ring
  have hτ : -(starRingEnd ℂ) (I * t) = I * t := by simp
  rw [← conj_eq_iff_im, jacobiPQ, ht, hζ, conj_jacobiGlaisher, conj_ofReal, hτ]

/-- `θ₃(·|τ)` is entire for `Im τ > 0`. -/
private lemma differentiable_jacobiThetaThreeTau {τ : ℂ} (hτ : 0 < τ.im) :
    Differentiable ℂ fun ζ => jacobiThetaThreeTau ζ τ := fun ζ =>
  (differentiableAt_jacobiTheta₂_fst (ζ / π) hτ).comp (f := fun w : ℂ => w / π) ζ
    ((differentiableAt_id).div_const _)

/-- The normalized theta functions are entire in `ζ` for `Im τ > 0`. -/
private lemma differentiable_jacobiLetterTheta {τ : ℂ} (hτ : 0 < τ.im) (p : JacobiLetter) :
    Differentiable ℂ fun ζ => jacobiLetterTheta p ζ τ := by
  have h3 := differentiable_jacobiThetaThreeTau hτ
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
theorem jacobiPQ_meromorphicAt {k : ℂ} (hk : k ∈ jacobiModulusDomain) (p q : JacobiLetter)
    (z : ℂ) : MeromorphicAt (fun w => jacobiPQ p q w k) z := by
  have hτ := jacobiTau_im_pos hk
  have hζ : Differentiable ℂ fun w => jacobiThetaArgument w k := fun w =>
    ((differentiableAt_id.const_mul _).div_const _)
  unfold jacobiPQ jacobiGlaisher
  by_cases hpq : p = q
  · simp only [hpq, ↓reduceIte]; exact analyticAt_const.meromorphicAt
  · simp only [hpq, ↓reduceIte]
    exact (((differentiable_jacobiLetterTheta hτ p).comp hζ).analyticAt z).meromorphicAt.div
      (((differentiable_jacobiLetterTheta hτ q).comp hζ).analyticAt z).meromorphicAt

end DLMF.JacobiElliptic

end
end
