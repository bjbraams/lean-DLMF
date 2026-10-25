/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.Basic
public import DLMF.JacobiElliptic.ElementaryIdentities
public import DLMF.Elliptic.JacobiIdentities

/-!
# Derivatives and differential equations of the Jacobian elliptic functions (DLMF §22.13)

* **Table 22.13.1** (`22.13.T1`): each derivative `d pq(z,k)/dz` is a constant multiple of the
  product of the two copolar functions. For complex `z` and `k ∈ jacobiModulusDomain` these are
  stated for the theta-quotient functions `jacobiSnk … jacobiCsk` of `DLMF.JacobiElliptic.Basic`
  away from the poles (the theta function in the denominator is nonzero). They are proved from
  the theta-function Wronskians `θ_p'θ_q - θ_pθ_q' = const · θ_rθ_s`, obtained by differentiating
  the mixed product identities of `DLMF.JacobiElliptic.Addition` at `v = 0` and using
  `θ₁'(0) = θ₂(0)θ₃(0)θ₄(0)`, together with `K = (π/2)θ₃²(0)` (22.2.2).
  For real argument and real parameter `m = k² < 1` the nine quotient functions
  `sd, cd, nd, dc, nc, sc, ns, ds, cs` are proved from the existing real `sn, cn, dn`
  (`DLMF.Elliptic.Real.hasDerivAt_jacobiSnm` …); the three basic entries for real argument are
  `Real.hasDerivAt_jacobiSnm`, `Real.hasDerivAt_jacobiCnm`, `Real.hasDerivAt_jacobiDnm` in
  `DLMF.Elliptic.Jacobi`.
* **First-order equations** 22.13.1–22.13.12 and **second-order equations** 22.13.13–22.13.24:
  complex forms proved from Table 22.13.1 and the sums of squares (22.6.1–22.6.4);
  real-argument forms proved for the nine quotient functions (first order) and for `cd, sd, nd`
  (second order, no real poles). For `sn, cn, dn` the real forms are
  `Real.jacobiSnm_deriv_sq` … and `Real.iteratedDeriv_two_jacobiSnm` …
  in `DLMF.Elliptic.JacobiIdentities`.

Poles carry Lean's junk value `x / 0 = 0`, so every complex statement assumes that `z` is not a
pole of the function concerned (the theta function of the second letter does not vanish at
`ζ = πz/(2K)`); real statements assume `cn x ≠ 0` or `sn x ≠ 0` where DLMF divides.
In the real forms `k'² = 1 - m`.
-/

@[expose] public section

open Complex DLMF.Elliptic
open scoped Real Topology

noncomputable section

namespace DLMF.JacobiElliptic

local notation "θ₁" => jacobiThetaOneTau
local notation "θ₂" => jacobiThetaTwoTau
local notation "θ₃" => jacobiThetaThreeTau
local notation "θ₄" => jacobiThetaFourTau

/-! ### Theta-function Wronskians and the derivative of a theta quotient (helpers) -/

lemma p22R1_deriv_even {f : ℂ → ℂ} (hf : Differentiable ℂ f) (he : ∀ z, f (-z) = f z) :
    deriv f 0 = 0 := by
  have h1 : HasDerivAt f (deriv f 0) (-0) := by rw [neg_zero]; exact (hf 0).hasDerivAt
  have h2 := h1.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
  have h3 : (f ∘ fun x => -x) = f := funext fun z => he z
  rw [h3] at h2
  have := h2.unique (hf 0).hasDerivAt
  linear_combination -this / 2

lemma p22R1_wr {f g A B C E : ℂ → ℂ} {f' g' b' e' : ℂ} (κ x : ℂ)
    (hfg : ∀ y, κ * (f (x + y) * g (x - y)) = A x * B y + C x * E y)
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (hB : HasDerivAt B b' 0)
    (hE : HasDerivAt E e' 0) : κ * (f' * g x - f x * g') = A x * b' + C x * e' := by
  have hf' : HasDerivAt f f' (x + 0) := by rwa [add_zero]
  have hg' : HasDerivAt g g' (x - 0) := by rwa [sub_zero]
  have hL := ((hf'.comp_const_add x 0).mul (hg'.comp_const_sub x 0)).const_mul κ
  have hR := (hB.const_mul (A x)).add (hE.const_mul (C x))
  have hL2 : HasDerivAt (fun y => A x * B y + C x * E y)
      (κ * (f' * g (x - 0) + f (x + 0) * -g')) 0 := by
    convert hL using 1; funext y; exact (hfg y).symm
  have := hL2.unique hR
  simp only [add_zero, sub_zero] at this
  linear_combination this

section
variable {τ : ℂ} (hτ : 0 < τ.im)
include hτ

lemma p22R1_hd1 (z : ℂ) : HasDerivAt (fun w => θ₁ w τ) (deriv (fun w => θ₁ w τ) z) z :=
  ((DLMF.Theta.differentiable_jacobiThetaTau 1 hτ) z).hasDerivAt
lemma p22R1_hd2 (z : ℂ) : HasDerivAt (fun w => θ₂ w τ) (deriv (fun w => θ₂ w τ) z) z :=
  ((DLMF.Theta.differentiable_jacobiThetaTau 2 hτ) z).hasDerivAt
lemma p22R1_hd3 (z : ℂ) : HasDerivAt (fun w => θ₃ w τ) (deriv (fun w => θ₃ w τ) z) z :=
  ((DLMF.Theta.differentiable_jacobiThetaTau 3 hτ) z).hasDerivAt
lemma p22R1_hd4 (z : ℂ) : HasDerivAt (fun w => θ₄ w τ) (deriv (fun w => θ₄ w τ) z) z :=
  ((DLMF.Theta.differentiable_jacobiThetaTau 4 hτ) z).hasDerivAt

lemma p22R1_d2zero : deriv (fun w => θ₂ w τ) 0 = 0 :=
  p22R1_deriv_even (DLMF.Theta.differentiable_jacobiThetaTau 2 hτ)
    fun z => jacobiThetaTwoTau_neg z τ
lemma p22R1_d3zero : deriv (fun w => θ₃ w τ) 0 = 0 :=
  p22R1_deriv_even (DLMF.Theta.differentiable_jacobiThetaTau 3 hτ)
    fun z => jacobiThetaThreeTau_neg z τ
lemma p22R1_d4zero : deriv (fun w => θ₄ w τ) 0 = 0 :=
  p22R1_deriv_even (DLMF.Theta.differentiable_jacobiThetaTau 4 hτ)
    fun z => jacobiThetaFourTau_neg z τ
lemma p22R1_d1zero : deriv (fun w => θ₁ w τ) 0 = θ₂ 0 τ * θ₃ 0 τ * θ₄ 0 τ :=
  DLMF.Theta.jacobiThetaOneDerivNullTau_eq_mul hτ

/-- Wronskian `θ₁'θ₄ - θ₁θ₄' = θ₄(0)² θ₂θ₃`. -/
lemma p22R1_W14 (x : ℂ) :
    deriv (fun w => θ₁ w τ) x * θ₄ x τ - θ₁ x τ * deriv (fun w => θ₄ w τ) x =
      θ₄ 0 τ ^ 2 * (θ₂ x τ * θ₃ x τ) := by
  have h := p22R1_wr (f := fun w => θ₁ w τ) (g := fun w => θ₄ w τ)
    (A := fun w => θ₁ w τ * θ₄ w τ) (B := fun w => θ₂ w τ * θ₃ w τ)
    (C := fun w => θ₂ w τ * θ₃ w τ) (E := fun w => θ₁ w τ * θ₄ w τ) (θ₂ 0 τ * θ₃ 0 τ) x
    (fun y => p22R1_mixed14 x y τ hτ) (p22R1_hd1 hτ x) (p22R1_hd4 hτ x)
    ((p22R1_hd2 hτ 0).mul (p22R1_hd3 hτ 0)) ((p22R1_hd1 hτ 0).mul (p22R1_hd4 hτ 0))
  simp only [p22R1_d1zero hτ, p22R1_d2zero hτ, p22R1_d3zero hτ, p22R1_d4zero hτ,
    je22a_thetaOne_zero] at h
  obtain ⟨h2, h3, -, -⟩ := p22R1_nulls τ hτ
  apply mul_left_cancel₀ (mul_ne_zero h2 h3)
  linear_combination h

lemma p22R1_W24 (x : ℂ) :
    deriv (fun w => θ₂ w τ) x * θ₄ x τ - θ₂ x τ * deriv (fun w => θ₄ w τ) x =
      -(θ₃ 0 τ ^ 2 * (θ₁ x τ * θ₃ x τ)) := by
  have h := p22R1_wr (f := fun w => θ₂ w τ) (g := fun w => θ₄ w τ)
    (A := fun w => θ₂ w τ * θ₄ w τ) (B := fun w => θ₂ w τ * θ₄ w τ)
    (C := fun w => -(θ₁ w τ * θ₃ w τ)) (E := fun w => θ₁ w τ * θ₃ w τ) (θ₂ 0 τ * θ₄ 0 τ) x
    (fun y => by have := p22R1_mixed24 x y τ hτ; linear_combination this)
    (p22R1_hd2 hτ x) (p22R1_hd4 hτ x)
    ((p22R1_hd2 hτ 0).mul (p22R1_hd4 hτ 0)) ((p22R1_hd1 hτ 0).mul (p22R1_hd3 hτ 0))
  simp only [p22R1_d1zero hτ, p22R1_d2zero hτ, p22R1_d3zero hτ, p22R1_d4zero hτ,
    je22a_thetaOne_zero] at h
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  apply mul_left_cancel₀ (mul_ne_zero h2 h4)
  linear_combination h

lemma p22R1_W34 (x : ℂ) :
    deriv (fun w => θ₃ w τ) x * θ₄ x τ - θ₃ x τ * deriv (fun w => θ₄ w τ) x =
      -(θ₂ 0 τ ^ 2 * (θ₁ x τ * θ₂ x τ)) := by
  have h := p22R1_wr (f := fun w => θ₃ w τ) (g := fun w => θ₄ w τ)
    (A := fun w => θ₃ w τ * θ₄ w τ) (B := fun w => θ₃ w τ * θ₄ w τ)
    (C := fun w => -(θ₁ w τ * θ₂ w τ)) (E := fun w => θ₁ w τ * θ₂ w τ) (θ₃ 0 τ * θ₄ 0 τ) x
    (fun y => by have := p22R1_mixed34 x y τ hτ; linear_combination this)
    (p22R1_hd3 hτ x) (p22R1_hd4 hτ x)
    ((p22R1_hd3 hτ 0).mul (p22R1_hd4 hτ 0)) ((p22R1_hd1 hτ 0).mul (p22R1_hd2 hτ 0))
  simp only [p22R1_d1zero hτ, p22R1_d2zero hτ, p22R1_d3zero hτ, p22R1_d4zero hτ,
    je22a_thetaOne_zero] at h
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  apply mul_left_cancel₀ (mul_ne_zero h3 h4)
  linear_combination h

lemma p22R1_W23 (x : ℂ) :
    deriv (fun w => θ₂ w τ) x * θ₃ x τ - θ₂ x τ * deriv (fun w => θ₃ w τ) x =
      -(θ₄ 0 τ ^ 2 * (θ₁ x τ * θ₄ x τ)) := by
  have h := p22R1_wr (f := fun w => θ₂ w τ) (g := fun w => θ₃ w τ)
    (A := fun w => θ₂ w τ * θ₃ w τ) (B := fun w => θ₂ w τ * θ₃ w τ)
    (C := fun w => -(θ₁ w τ * θ₄ w τ)) (E := fun w => θ₁ w τ * θ₄ w τ) (θ₂ 0 τ * θ₃ 0 τ) x
    (fun y => by have := p22R1_P23 x y τ hτ; linear_combination this)
    (p22R1_hd2 hτ x) (p22R1_hd3 hτ x)
    ((p22R1_hd2 hτ 0).mul (p22R1_hd3 hτ 0)) ((p22R1_hd1 hτ 0).mul (p22R1_hd4 hτ 0))
  simp only [p22R1_d1zero hτ, p22R1_d2zero hτ, p22R1_d3zero hτ, p22R1_d4zero hτ,
    je22a_thetaOne_zero] at h
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  apply mul_left_cancel₀ (mul_ne_zero h2 h3)
  linear_combination h

lemma p22R1_W13 (x : ℂ) :
    deriv (fun w => θ₁ w τ) x * θ₃ x τ - θ₁ x τ * deriv (fun w => θ₃ w τ) x =
      θ₃ 0 τ ^ 2 * (θ₂ x τ * θ₄ x τ) := by
  have h := p22R1_wr (f := fun w => θ₁ w τ) (g := fun w => θ₃ w τ)
    (A := fun w => θ₂ w τ * θ₄ w τ) (B := fun w => θ₁ w τ * θ₃ w τ)
    (C := fun w => θ₁ w τ * θ₃ w τ) (E := fun w => θ₂ w τ * θ₄ w τ) (θ₂ 0 τ * θ₄ 0 τ) x
    (fun y => by have := p22R1_P13 x y τ hτ; linear_combination this)
    (p22R1_hd1 hτ x) (p22R1_hd3 hτ x)
    ((p22R1_hd1 hτ 0).mul (p22R1_hd3 hτ 0)) ((p22R1_hd2 hτ 0).mul (p22R1_hd4 hτ 0))
  simp only [p22R1_d1zero hτ, p22R1_d2zero hτ, p22R1_d3zero hτ, p22R1_d4zero hτ,
    je22a_thetaOne_zero] at h
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  apply mul_left_cancel₀ (mul_ne_zero h2 h4)
  linear_combination h

lemma p22R1_W12 (x : ℂ) :
    deriv (fun w => θ₁ w τ) x * θ₂ x τ - θ₁ x τ * deriv (fun w => θ₂ w τ) x =
      θ₂ 0 τ ^ 2 * (θ₃ x τ * θ₄ x τ) := by
  have h := p22R1_wr (f := fun w => θ₁ w τ) (g := fun w => θ₂ w τ)
    (A := fun w => θ₁ w τ * θ₂ w τ) (B := fun w => θ₃ w τ * θ₄ w τ)
    (C := fun w => θ₃ w τ * θ₄ w τ) (E := fun w => θ₁ w τ * θ₂ w τ) (θ₃ 0 τ * θ₄ 0 τ) x
    (fun y => by have := p22R1_P12 x y τ hτ; linear_combination this)
    (p22R1_hd1 hτ x) (p22R1_hd2 hτ x)
    ((p22R1_hd3 hτ 0).mul (p22R1_hd4 hτ 0)) ((p22R1_hd1 hτ 0).mul (p22R1_hd2 hτ 0))
  simp only [p22R1_d1zero hτ, p22R1_d2zero hτ, p22R1_d3zero hτ, p22R1_d4zero hτ,
    je22a_thetaOne_zero] at h
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  apply mul_left_cancel₀ (mul_ne_zero h3 h4)
  linear_combination h

lemma p22R1_W41 (x : ℂ) :
    deriv (fun w => θ₄ w τ) x * θ₁ x τ - θ₄ x τ * deriv (fun w => θ₁ w τ) x =
      -(θ₄ 0 τ ^ 2 * (θ₂ x τ * θ₃ x τ)) := by
  linear_combination -(p22R1_W14 hτ x)

lemma p22R1_W42 (x : ℂ) :
    deriv (fun w => θ₄ w τ) x * θ₂ x τ - θ₄ x τ * deriv (fun w => θ₂ w τ) x =
      -(-(θ₃ 0 τ ^ 2 * (θ₁ x τ * θ₃ x τ))) := by
  linear_combination -(p22R1_W24 hτ x)

lemma p22R1_W43 (x : ℂ) :
    deriv (fun w => θ₄ w τ) x * θ₃ x τ - θ₄ x τ * deriv (fun w => θ₃ w τ) x =
      -(-(θ₂ 0 τ ^ 2 * (θ₁ x τ * θ₂ x τ))) := by
  linear_combination -(p22R1_W34 hτ x)

lemma p22R1_W32 (x : ℂ) :
    deriv (fun w => θ₃ w τ) x * θ₂ x τ - θ₃ x τ * deriv (fun w => θ₂ w τ) x =
      -(-(θ₄ 0 τ ^ 2 * (θ₁ x τ * θ₄ x τ))) := by
  linear_combination -(p22R1_W23 hτ x)

lemma p22R1_W31 (x : ℂ) :
    deriv (fun w => θ₃ w τ) x * θ₁ x τ - θ₃ x τ * deriv (fun w => θ₁ w τ) x =
      -(θ₃ 0 τ ^ 2 * (θ₂ x τ * θ₄ x τ)) := by
  linear_combination -(p22R1_W13 hτ x)

lemma p22R1_W21 (x : ℂ) :
    deriv (fun w => θ₂ w τ) x * θ₁ x τ - θ₂ x τ * deriv (fun w => θ₁ w τ) x =
      -(θ₂ 0 τ ^ 2 * (θ₃ x τ * θ₄ x τ)) := by
  linear_combination -(p22R1_W12 hτ x)

end

/-- Normalizing constant of `jacobiLetterTheta` (helper). -/
noncomputable def p22R1_N : JacobiLetter → ℂ → ℂ
  | .s, τ => θ₃ 0 τ / (θ₂ 0 τ * θ₄ 0 τ)
  | .c, τ => 1 / θ₂ 0 τ
  | .d, τ => 1 / θ₃ 0 τ
  | .n, τ => 1 / θ₄ 0 τ

/-- The theta function of a letter (helper). -/
noncomputable def p22R1_th : JacobiLetter → ℂ → ℂ → ℂ
  | .s => θ₁
  | .c => θ₂
  | .d => θ₃
  | .n => θ₄

lemma p22R1_letter_eq (p : JacobiLetter) (ζ τ : ℂ) :
    jacobiLetterTheta p ζ τ = p22R1_N p τ * p22R1_th p ζ τ := by
  cases p <;> simp [jacobiLetterTheta, p22R1_N, p22R1_th] <;> ring

lemma p22R1_differentiable_th (p : JacobiLetter) {τ : ℂ} (hτ : 0 < τ.im) :
    Differentiable ℂ (fun w => p22R1_th p w τ) := by
  cases p
  · exact DLMF.Theta.differentiable_jacobiThetaTau 1 hτ
  · exact DLMF.Theta.differentiable_jacobiThetaTau 2 hτ
  · exact DLMF.Theta.differentiable_jacobiThetaTau 3 hτ
  · exact DLMF.Theta.differentiable_jacobiThetaTau 4 hτ

lemma p22R1_hasDerivAt_PQ {k : ℂ} (hk : k ∈ jacobiModulusDomain) {p q : JacobiLetter}
    (hpq : p ≠ q) {z : ℂ} (hz : jacobiLetterTheta q (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiPQk p q z k)
      (p22R1_N p (jacobiTauk k) / p22R1_N q (jacobiTauk k) * (π / (2 * compEllIntKk k)) *
        (deriv (fun w => p22R1_th p w (jacobiTauk k)) (jacobiZetak z k) *
            p22R1_th q (jacobiZetak z k) (jacobiTauk k) -
          p22R1_th p (jacobiZetak z k) (jacobiTauk k) *
            deriv (fun w => p22R1_th q w (jacobiTauk k)) (jacobiZetak z k)) /
        p22R1_th q (jacobiZetak z k) (jacobiTauk k) ^ 2) z := by
  have hτ := jacobiTauk_im_pos hk
  have hK := p22R1_compEllIntKk_ne_zero hk
  have hfun : (fun z => jacobiPQk p q z k) = fun z =>
      (p22R1_N p (jacobiTauk k) * p22R1_th p (jacobiZetak z k) (jacobiTauk k)) /
        (p22R1_N q (jacobiTauk k) * p22R1_th q (jacobiZetak z k) (jacobiTauk k)) := by
    funext w; simp [jacobiPQk, jacobiGlaisher, hpq, p22R1_letter_eq]
  rw [hfun]
  rw [p22R1_letter_eq] at hz
  have hζ : HasDerivAt (fun z => jacobiZetak z k) (π / (2 * compEllIntKk k)) z := by
    have := ((hasDerivAt_id z).const_mul (π : ℂ)).div_const (2 * compEllIntKk k)
    simpa [jacobiZetak] using this
  have hp := (((p22R1_differentiable_th p hτ) _).hasDerivAt.comp z hζ).const_mul
    (p22R1_N p (jacobiTauk k))
  have hq := (((p22R1_differentiable_th q hτ) _).hasDerivAt.comp z hζ).const_mul
    (p22R1_N q (jacobiTauk k))
  convert hp.div hq hz using 1
  · funext y; rfl
  have hN : p22R1_N q (jacobiTauk k) ≠ 0 := left_ne_zero_of_mul hz
  have hT : p22R1_th q (jacobiZetak z k) (jacobiTauk k) ≠ 0 := right_ne_zero_of_mul hz
  simp only [Function.comp_def]
  field_simp

/-! ### Table 22.13.1, complex argument -/

section Complex

variable {k : ℂ}

lemma p22R1_sq_d1 (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    jacobiCdk z k ^ 2 + jacobiComodulusk k ^ 2 * jacobiSdk z k ^ 2 = 1 := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.1]
  have hz' : θ₃ (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hz; simp [jacobiLetterTheta, h']
  simp only [jacobiSdk, jacobiCdk, 
    jacobiPQk, jacobiGlaisher, jacobiLetterTheta, jacobiComodulusTau, reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz' ⊢
  generalize jacobiTauk k = τ at hτ hz' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have e := DLMF.Theta.jacobiTheta_sq_two_three x τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e
  field_simp
  linear_combination -e

lemma p22R1_sq_d2 (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    jacobiNdk z k ^ 2 - k ^ 2 * jacobiSdk z k ^ 2 = 1 := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hz' : θ₃ (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hz; simp [jacobiLetterTheta, h']
  simp only [jacobiSdk, jacobiNdk, 
    jacobiPQk, jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz' ⊢
  generalize jacobiTauk k = τ at hτ hz' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have e := DLMF.Theta.jacobiTheta_sq_three_four x τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e
  field_simp
  linear_combination e

lemma p22R1_sq_c1 (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    jacobiNck z k ^ 2 - jacobiSck z k ^ 2 = 1 := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hz' : θ₂ (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hz; simp [jacobiLetterTheta, h']
  simp only [jacobiSck, jacobiNck, 
    jacobiPQk, jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz' ⊢
  generalize jacobiTauk k = τ at hτ hz' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have e := DLMF.Theta.jacobiTheta_sq_two_four x τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e
  field_simp
  linear_combination e

lemma p22R1_sq_c2 (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    jacobiDck z k ^ 2 - jacobiComodulusk k ^ 2 * jacobiSck z k ^ 2 = 1 := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.1]
  have hz' : θ₂ (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hz; simp [jacobiLetterTheta, h']
  simp only [jacobiSck, jacobiDck, 
    jacobiPQk, jacobiGlaisher, jacobiLetterTheta, jacobiComodulusTau, reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz' ⊢
  generalize jacobiTauk k = τ at hτ hz' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have e := DLMF.Theta.jacobiTheta_sq_two_three x τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e
  field_simp
  linear_combination e

lemma p22R1_sq_s1 (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    jacobiNsk z k ^ 2 - jacobiCsk z k ^ 2 = 1 := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  have hz' : θ₁ (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hz; simp [jacobiLetterTheta, h']
  simp only [jacobiNsk, jacobiCsk,
    jacobiPQk, jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ↓reduceIte]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz' ⊢
  generalize jacobiTauk k = τ at hτ hz' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have e := DLMF.Theta.jacobiTheta_sq_two_four x τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e
  field_simp
  linear_combination e

lemma p22R1_sq_s2 (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    jacobiDsk z k ^ 2 - jacobiCsk z k ^ 2 = jacobiComodulusk k ^ 2 := by
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.1]
  have hz' : θ₁ (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
    intro h'; apply hz; simp [jacobiLetterTheta, h']
  simp only [jacobiCsk,
    jacobiDsk, jacobiPQk, jacobiGlaisher, jacobiLetterTheta, jacobiComodulusTau, reduceCtorEq,
    ↓reduceIte]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz' ⊢
  generalize jacobiTauk k = τ at hτ hz' hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have e := DLMF.Theta.jacobiTheta_sq_two_three x τ hτ
  simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
    DLMF.Theta.jacobiThetaFourNullTau] at e
  field_simp
  linear_combination e

lemma p22R1_eventually_ne (hk : k ∈ jacobiModulusDomain) {p : JacobiLetter} {z : ℂ}
    (hz : jacobiLetterTheta p (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    ∀ᶠ w in 𝓝 z, jacobiLetterTheta p (jacobiZetak w k) (jacobiTauk k) ≠ 0 := by
  have hτ := jacobiTauk_im_pos hk
  have hc : Continuous fun w => jacobiLetterTheta p (jacobiZetak w k) (jacobiTauk k) := by
    simp only [p22R1_letter_eq]
    exact continuous_const.mul ((p22R1_differentiable_th p hτ).continuous.comp
      (by unfold jacobiZetak; fun_prop))
  exact hc.continuousAt.eventually_ne hz

/-- DLMF Table 22.13.1: `d sn(z,k)/dz = cn(z,k) dn(z,k)`, for `k ∈ jacobiModulusDomain` and `z`
not a pole of `sn` (`θ₄(πz/(2K)) ≠ 0`). -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiSnk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiSnk z k) (jacobiCnk z k * jacobiDnk z k) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .s) (q := .n) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiCnk, jacobiDnk, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W14 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d cn(z,k)/dz = -sn(z,k) dn(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiCnk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiCnk z k) (-(jacobiSnk z k * jacobiDnk z k)) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .c) (q := .n) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiDnk, jacobiSnk, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W24 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d dn(z,k)/dz = -k² sn(z,k) cn(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiDnk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiDnk z k) (-(k ^ 2 * jacobiSnk z k * jacobiCnk z k)) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .d) (q := .n) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiCnk, jacobiSnk, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W34 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d cd(z,k)/dz = -k'² sd(z,k) nd(z,k)`, away from the poles
(`θ₃(πz/(2K)) ≠ 0`). -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiCdk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiCdk z k)
      (-(jacobiComodulusk k ^ 2 * jacobiSdk z k * jacobiNdk z k)) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .c) (q := .d) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [← (jacobi_inversion_k hk).2.1]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiNdk, jacobiSdk, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      jacobiComodulusTau, reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W23 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d sd(z,k)/dz = cd(z,k) nd(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiSdk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiSdk z k) (jacobiCdk z k * jacobiNdk z k) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .s) (q := .d) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiCdk, jacobiNdk, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W13 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d nd(z,k)/dz = k² sd(z,k) cd(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiNdk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiNdk z k) (k ^ 2 * jacobiSdk z k * jacobiCdk z k) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .n) (q := .d) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiCdk, jacobiSdk, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W43 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d dc(z,k)/dz = k'² sc(z,k) nc(z,k)`, away from the poles
(`θ₂(πz/(2K)) ≠ 0`). -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiDck (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiDck z k)
      (jacobiComodulusk k ^ 2 * jacobiSck z k * jacobiNck z k) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .d) (q := .c) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [← (jacobi_inversion_k hk).2.1]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiNck, jacobiSck, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      jacobiComodulusTau, reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W32 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d nc(z,k)/dz = sc(z,k) dc(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiNck (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiNck z k) (jacobiSck z k * jacobiDck z k) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .n) (q := .c) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiDck, jacobiSck, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W42 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d sc(z,k)/dz = dc(z,k) nc(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiSck (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiSck z k) (jacobiDck z k * jacobiNck z k) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .s) (q := .c) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiDck, jacobiNck, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W12 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d ns(z,k)/dz = -ds(z,k) cs(z,k)`, away from the poles
(`θ₁(πz/(2K)) ≠ 0`). -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiNsk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiNsk z k) (-(jacobiDsk z k * jacobiCsk z k)) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .n) (q := .s) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiCsk, jacobiDsk, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W41 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d ds(z,k)/dz = -cs(z,k) ns(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiDsk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiDsk z k) (-(jacobiCsk z k * jacobiNsk z k)) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .d) (q := .s) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiCsk, jacobiNsk, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W31 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-- DLMF Table 22.13.1: `d cs(z,k)/dz = -ns(z,k) ds(z,k)`, away from the poles. -/
@[dlmf 22.13.T1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem hasDerivAt_jacobiCsk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    HasDerivAt (fun z => jacobiCsk z k) (-(jacobiNsk z k * jacobiDsk z k)) z := by
  have h := p22R1_hasDerivAt_PQ hk (p := .c) (q := .s) (by decide) hz
  refine h.congr_deriv ?_
  have hτ := jacobiTauk_im_pos hk
  have hmod := (jacobi_inversion_k hk).1
  rw [← (jacobi_inversion_k hk).2.2]
  rw [p22R1_letter_eq] at hz
  simp only [jacobiDsk, jacobiNsk, jacobiPQk, jacobiGlaisher, p22R1_letter_eq, p22R1_N, p22R1_th,
      reduceCtorEq, ↓reduceIte] at hz ⊢
  rw [p22R1_W21 hτ, compEllIntKTau]
  rw [jacobiModulusTau] at hmod
  generalize jacobiZetak z k = x at hz ⊢
  generalize jacobiTauk k = τ at hτ hz hmod ⊢
  subst hmod
  obtain ⟨h2, h3, h4, -⟩ := p22R1_nulls τ hτ
  have hx := right_ne_zero_of_mul hz
  field_simp

/-! ### First-order differential equations 22.13.1–22.13.12, complex argument -/

/-- DLMF 22.13.1: `(sn')² = (1 - sn²)(1 - k² sn²)`, away from the poles. -/
@[dlmf 22.13.E1 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiSnk_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiSnk z k) z ^ 2 =
      (1 - jacobiSnk z k ^ 2) * (1 - k ^ 2 * jacobiSnk z k ^ 2) := by
  have R := jacobi_sq_sum hk hz
  have R1 := R.1
  have R2 : k ^ 2 * jacobiSnk z k ^ 2 + jacobiDnk z k ^ 2 = 1 := R.2
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiSnk hk hz).deriv]
  linear_combination ((jacobiDnk z k) ^ 2) * R1 + (1 - (jacobiSnk z k) ^ 2) * R2

/-- DLMF 22.13.2: `(cn')² = (1 - cn²)(k'² + k² cn²)`, away from the poles. -/
@[dlmf 22.13.E2 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiCnk_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiCnk z k) z ^ 2 =
      (1 - jacobiCnk z k ^ 2) * (jacobiComodulusk k ^ 2 + k ^ 2 * jacobiCnk z k ^ 2) := by
  have R := jacobi_sq_sum hk hz
  have R1 := R.1
  have R2 : k ^ 2 * jacobiSnk z k ^ 2 + jacobiDnk z k ^ 2 = 1 := R.2
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiCnk hk hz).deriv]
  linear_combination ((jacobiCnk z k) ^ 2 * k ^ 2 - k ^ 2 * (jacobiSnk z k) ^ 2 +
    (jacobiComodulusk k) ^ 2) * R1 + ((jacobiSnk z k) ^ 2) * R2 + (-(jacobiSnk z k) ^ 2) * hK

/-- DLMF 22.13.3: `(dn')² = (1 - dn²)(dn² - k'²)`, away from the poles. -/
@[dlmf 22.13.E3 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiDnk_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiDnk z k) z ^ 2 =
      (1 - jacobiDnk z k ^ 2) * (jacobiDnk z k ^ 2 - jacobiComodulusk k ^ 2) := by
  have R := jacobi_sq_sum hk hz
  have R1 := R.1
  have R2 : k ^ 2 * jacobiSnk z k ^ 2 + jacobiDnk z k ^ 2 = 1 := R.2
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiDnk hk hz).deriv]
  linear_combination (k ^ 4 * (jacobiSnk z k) ^ 2) * R1 +
    ((jacobiDnk z k) ^ 2 - k ^ 2 * (jacobiSnk z k) ^ 2 - (jacobiComodulusk k) ^ 2) * R2 +
    (k ^ 2 * (jacobiSnk z k) ^ 2) * hK

/-- DLMF 22.13.4: `(cd')² = (1 - cd²)(1 - k² cd²)`, away from the poles. -/
@[dlmf 22.13.E4 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiCdk_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiCdk z k) z ^ 2 =
      (1 - jacobiCdk z k ^ 2) * (1 - k ^ 2 * jacobiCdk z k ^ 2) := by
  have R1 := p22R1_sq_d1 hk hz
  have R2 := p22R1_sq_d2 hk hz
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiCdk hk hz).deriv]
  linear_combination (-(jacobiCdk z k) ^ 2 * k ^ 2 +
    k ^ 2 * (jacobiComodulusk k) ^ 2 * (jacobiSdk z k) ^ 2 + 1) * R1 +
    ((jacobiComodulusk k) ^ 4 * (jacobiSdk z k) ^ 2) * R2 +
    ((jacobiComodulusk k) ^ 2 * (jacobiSdk z k) ^ 2) * hK

/-- DLMF 22.13.5: `(sd')² = (1 - k'² sd²)(1 + k² sd²)`, away from the poles. -/
@[dlmf 22.13.E5 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiSdk_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiSdk z k) z ^ 2 =
      (1 - jacobiComodulusk k ^ 2 * jacobiSdk z k ^ 2) * (1 + k ^ 2 * jacobiSdk z k ^ 2) := by
  have R1 := p22R1_sq_d1 hk hz
  have R2 := p22R1_sq_d2 hk hz
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiSdk hk hz).deriv]
  linear_combination ((jacobiNdk z k) ^ 2) * R1 +
    (-(jacobiComodulusk k) ^ 2 * (jacobiSdk z k) ^ 2 + 1) * R2

/-- DLMF 22.13.6: `(nd')² = (nd² - 1)(1 - k'² nd²)`, away from the poles. -/
@[dlmf 22.13.E6 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiNdk_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiNdk z k) z ^ 2 =
      (jacobiNdk z k ^ 2 - 1) * (1 - jacobiComodulusk k ^ 2 * jacobiNdk z k ^ 2) := by
  have R1 := p22R1_sq_d1 hk hz
  have R2 := p22R1_sq_d2 hk hz
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiNdk hk hz).deriv]
  linear_combination (k ^ 4 * (jacobiSdk z k) ^ 2) * R1 +
    (k ^ 2 * (jacobiComodulusk k) ^ 2 * (jacobiSdk z k) ^ 2 +
    (jacobiComodulusk k) ^ 2 * (jacobiNdk z k) ^ 2 - 1) * R2 + (k ^ 2 * (jacobiSdk z k) ^ 2) * hK

/-- DLMF 22.13.7: `(dc')² = (dc² - 1)(dc² - k²)`, away from the poles. -/
@[dlmf 22.13.E7 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiDck_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiDck z k) z ^ 2 =
      (jacobiDck z k ^ 2 - 1) * (jacobiDck z k ^ 2 - k ^ 2) := by
  have R1 := p22R1_sq_c1 hk hz
  have R2 := p22R1_sq_c2 hk hz
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiDck hk hz).deriv]
  linear_combination ((jacobiComodulusk k) ^ 4 * (jacobiSck z k) ^ 2) * R1 +
    (-(jacobiDck z k) ^ 2 + k ^ 2 - (jacobiComodulusk k) ^ 2 * (jacobiSck z k) ^ 2) * R2 +
    ((jacobiComodulusk k) ^ 2 * (jacobiSck z k) ^ 2) * hK

/-- DLMF 22.13.8: `(nc')² = (k² + k'² nc²)(nc² - 1)`, away from the poles. -/
@[dlmf 22.13.E8 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiNck_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiNck z k) z ^ 2 =
      (k ^ 2 + jacobiComodulusk k ^ 2 * jacobiNck z k ^ 2) * (jacobiNck z k ^ 2 - 1) := by
  have R1 := p22R1_sq_c1 hk hz
  have R2 := p22R1_sq_c2 hk hz
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiNck hk hz).deriv]
  linear_combination (-k ^ 2 - (jacobiComodulusk k) ^ 2 *
    (jacobiNck z k) ^ 2 - (jacobiComodulusk k) ^ 2 * (jacobiSck z k) ^ 2) * R1 +
    ((jacobiSck z k) ^ 2) * R2 + (-(jacobiSck z k) ^ 2) * hK

/-- DLMF 22.13.9: `(sc')² = (1 + sc²)(1 + k'² sc²)`, away from the poles. -/
@[dlmf 22.13.E9 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiSck_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiSck z k) z ^ 2 =
      (1 + jacobiSck z k ^ 2) * (1 + jacobiComodulusk k ^ 2 * jacobiSck z k ^ 2) := by
  have R1 := p22R1_sq_c1 hk hz
  have R2 := p22R1_sq_c2 hk hz
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiSck hk hz).deriv]
  linear_combination ((jacobiDck z k) ^ 2) * R1 + ((jacobiSck z k) ^ 2 + 1) * R2

/-- DLMF 22.13.10: `(ns')² = (ns² - k²)(ns² - 1)`, away from the poles. -/
@[dlmf 22.13.E10 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiNsk_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiNsk z k) z ^ 2 =
      (jacobiNsk z k ^ 2 - k ^ 2) * (jacobiNsk z k ^ 2 - 1) := by
  have R1 := p22R1_sq_s1 hk hz
  have R2 := p22R1_sq_s2 hk hz
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiNsk hk hz).deriv]
  linear_combination (-(jacobiCsk z k) ^ 2 + k ^ 2 - (jacobiNsk z k) ^ 2) * R1 +
    ((jacobiCsk z k) ^ 2) * R2 + ((jacobiCsk z k) ^ 2) * hK

/-- DLMF 22.13.11: `(ds')² = (ds² - k'²)(k² + ds²)`, away from the poles. -/
@[dlmf 22.13.E11 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiDsk_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiDsk z k) z ^ 2 =
      (jacobiDsk z k ^ 2 - jacobiComodulusk k ^ 2) * (k ^ 2 + jacobiDsk z k ^ 2) := by
  have R1 := p22R1_sq_s1 hk hz
  have R2 := p22R1_sq_s2 hk hz
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiDsk hk hz).deriv]
  linear_combination ((jacobiCsk z k) ^ 2) * R1 +
    (-(jacobiCsk z k) ^ 2 - (jacobiDsk z k) ^ 2 - k ^ 2) * R2 + (-(jacobiCsk z k) ^ 2) * hK

/-- DLMF 22.13.12: `(cs')² = (1 + cs²)(k'² + cs²)`, away from the poles. -/
@[dlmf 22.13.E12 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem deriv_jacobiCsk_sq (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    deriv (fun z => jacobiCsk z k) z ^ 2 =
      (1 + jacobiCsk z k ^ 2) * (jacobiComodulusk k ^ 2 + jacobiCsk z k ^ 2) := by
  have R1 := p22R1_sq_s1 hk hz
  have R2 := p22R1_sq_s2 hk hz
  have hK := jacobiComodulusk_sq k
  rw [(hasDerivAt_jacobiCsk hk hz).deriv]
  linear_combination ((jacobiDsk z k) ^ 2) * R1 + ((jacobiCsk z k) ^ 2 + 1) * R2

/-! ### Second-order differential equations 22.13.13–22.13.24, complex argument -/

/-- DLMF 22.13.13: `sn'' = -(1 + k²) sn + 2k² sn³`, away from the poles. -/
@[dlmf 22.13.E13 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiSnk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiSnk z k) z =
      -(1 + k ^ 2) * jacobiSnk z k + 2 * k ^ 2 * jacobiSnk z k ^ 3 := by
  have R := jacobi_sq_sum hk hz
  have R1 := R.1
  have R2 : k ^ 2 * jacobiSnk z k ^ 2 + jacobiDnk z k ^ 2 = 1 := R.2
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiSnk z k) w) =ᶠ[𝓝 z]
    fun w => jacobiCnk w k * jacobiDnk w k :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiSnk hk hw).deriv
  have hg :=
    ((hasDerivAt_jacobiCnk hk hz).mul (hasDerivAt_jacobiDnk hk hz)).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (-k ^ 2 * (jacobiSnk z k)) * R1 + (-(jacobiSnk z k)) * R2

/-- DLMF 22.13.14: `cn'' = -(k'² - k²) cn - 2k² cn³`, away from the poles. -/
@[dlmf 22.13.E14 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiCnk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiCnk z k) z =
      -(jacobiComodulusk k ^ 2 - k ^ 2) * jacobiCnk z k - 2 * k ^ 2 * jacobiCnk z k ^ 3 := by
  have R := jacobi_sq_sum hk hz
  have R1 := R.1
  have R2 : k ^ 2 * jacobiSnk z k ^ 2 + jacobiDnk z k ^ 2 = 1 := R.2
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiCnk z k) w) =ᶠ[𝓝 z]
    fun w => -(jacobiSnk w k * jacobiDnk w k) :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiCnk hk hw).deriv
  have hg :=
    (((hasDerivAt_jacobiSnk hk hz).mul (hasDerivAt_jacobiDnk hk hz)).neg).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (2 * (jacobiCnk z k) * k ^ 2) * R1 + (-(jacobiCnk z k)) * R2 +
    ((jacobiCnk z k)) * hK

/-- DLMF 22.13.15: `dn'' = (1 + k'²) dn - 2 dn³`, away from the poles. -/
@[dlmf 22.13.E15 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiDnk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiDnk z k) z =
      (1 + jacobiComodulusk k ^ 2) * jacobiDnk z k - 2 * jacobiDnk z k ^ 3 := by
  have R := jacobi_sq_sum hk hz
  have R1 := R.1
  have R2 : k ^ 2 * jacobiSnk z k ^ 2 + jacobiDnk z k ^ 2 = 1 := R.2
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiDnk z k) w) =ᶠ[𝓝 z]
    fun w => -(k ^ 2 * jacobiSnk w k * jacobiCnk w k) :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiDnk hk hw).deriv
  have hg :=
    ((((hasDerivAt_jacobiSnk hk hz).const_mul (k ^ 2)).mul
      (hasDerivAt_jacobiCnk hk hz)).neg).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (-(jacobiDnk z k) * k ^ 2) * R1 + (2 * (jacobiDnk z k)) * R2 +
    (-(jacobiDnk z k)) * hK

/-- DLMF 22.13.16: `cd'' = -(1 + k²) cd + 2k² cd³`, away from the poles. -/
@[dlmf 22.13.E16 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiCdk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiCdk z k) z =
      -(1 + k ^ 2) * jacobiCdk z k + 2 * k ^ 2 * jacobiCdk z k ^ 3 := by
  have R1 := p22R1_sq_d1 hk hz
  have R2 := p22R1_sq_d2 hk hz
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiCdk z k) w) =ᶠ[𝓝 z]
    fun w => -(jacobiComodulusk k ^ 2 * jacobiSdk w k * jacobiNdk w k) :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiCdk hk hw).deriv
  have hg :=
    ((((hasDerivAt_jacobiSdk hk hz).const_mul (jacobiComodulusk k ^ 2)).mul
      (hasDerivAt_jacobiNdk hk hz)).neg).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (-2 * (jacobiCdk z k) * k ^ 2) * R1 +
    (-(jacobiCdk z k) * (jacobiComodulusk k) ^ 2) * R2 + (-(jacobiCdk z k)) * hK

/-- DLMF 22.13.17: `sd'' = (k² - k'²) sd - 2k²k'² sd³`, away from the poles. -/
@[dlmf 22.13.E17 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiSdk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiSdk z k) z =
      (k ^ 2 - jacobiComodulusk k ^ 2) * jacobiSdk z k -
        2 * k ^ 2 * jacobiComodulusk k ^ 2 * jacobiSdk z k ^ 3 := by
  have R1 := p22R1_sq_d1 hk hz
  have R2 := p22R1_sq_d2 hk hz
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiSdk z k) w) =ᶠ[𝓝 z]
    fun w => jacobiCdk w k * jacobiNdk w k :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiSdk hk hw).deriv
  have hg :=
    ((hasDerivAt_jacobiCdk hk hz).mul (hasDerivAt_jacobiNdk hk hz)).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (k ^ 2 * (jacobiSdk z k)) * R1 +
    (-(jacobiComodulusk k) ^ 2 * (jacobiSdk z k)) * R2

/-- DLMF 22.13.18: `nd'' = (1 + k'²) nd - 2k'² nd³`, away from the poles. -/
@[dlmf 22.13.E18 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiNdk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .d (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiNdk z k) z =
      (1 + jacobiComodulusk k ^ 2) * jacobiNdk z k -
        2 * jacobiComodulusk k ^ 2 * jacobiNdk z k ^ 3 := by
  have R1 := p22R1_sq_d1 hk hz
  have R2 := p22R1_sq_d2 hk hz
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiNdk z k) w) =ᶠ[𝓝 z]
    fun w => k ^ 2 * jacobiSdk w k * jacobiCdk w k :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiNdk hk hw).deriv
  have hg :=
    (((hasDerivAt_jacobiSdk hk hz).const_mul (k ^ 2)).mul
      (hasDerivAt_jacobiCdk hk hz)).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (k ^ 2 * (jacobiNdk z k)) * R1 +
    (2 * (jacobiComodulusk k) ^ 2 * (jacobiNdk z k)) * R2 + ((jacobiNdk z k)) * hK

/-- DLMF 22.13.19: `dc'' = -(1 + k²) dc + 2 dc³`, away from the poles. -/
@[dlmf 22.13.E19 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiDck (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiDck z k) z =
      -(1 + k ^ 2) * jacobiDck z k + 2 * jacobiDck z k ^ 3 := by
  have R1 := p22R1_sq_c1 hk hz
  have R2 := p22R1_sq_c2 hk hz
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiDck z k) w) =ᶠ[𝓝 z]
    fun w => jacobiComodulusk k ^ 2 * jacobiSck w k * jacobiNck w k :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiDck hk hw).deriv
  have hg :=
    (((hasDerivAt_jacobiSck hk hz).const_mul (jacobiComodulusk k ^ 2)).mul
      (hasDerivAt_jacobiNck hk hz)).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination ((jacobiDck z k) * (jacobiComodulusk k) ^ 2) * R1 +
    (-2 * (jacobiDck z k)) * R2 + ((jacobiDck z k)) * hK

/-- DLMF 22.13.20: `nc'' = (k² - k'²) nc + 2k'² nc³`, away from the poles. -/
@[dlmf 22.13.E20 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiNck (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiNck z k) z =
      (k ^ 2 - jacobiComodulusk k ^ 2) * jacobiNck z k +
        2 * jacobiComodulusk k ^ 2 * jacobiNck z k ^ 3 := by
  have R1 := p22R1_sq_c1 hk hz
  have R2 := p22R1_sq_c2 hk hz
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiNck z k) w) =ᶠ[𝓝 z]
    fun w => jacobiSck w k * jacobiDck w k :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiNck hk hw).deriv
  have hg :=
    ((hasDerivAt_jacobiSck hk hz).mul (hasDerivAt_jacobiDck hk hz)).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (-2 * (jacobiComodulusk k) ^ 2 * (jacobiNck z k)) * R1 +
    ((jacobiNck z k)) * R2 + (-(jacobiNck z k)) * hK

/-- DLMF 22.13.21: `sc'' = (1 + k'²) sc + 2k'² sc³`, away from the poles. -/
@[dlmf 22.13.E21 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiSck (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .c (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiSck z k) z =
      (1 + jacobiComodulusk k ^ 2) * jacobiSck z k +
        2 * jacobiComodulusk k ^ 2 * jacobiSck z k ^ 3 := by
  have R1 := p22R1_sq_c1 hk hz
  have R2 := p22R1_sq_c2 hk hz
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiSck z k) w) =ᶠ[𝓝 z]
    fun w => jacobiDck w k * jacobiNck w k :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiSck hk hw).deriv
  have hg :=
    ((hasDerivAt_jacobiDck hk hz).mul (hasDerivAt_jacobiNck hk hz)).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination ((jacobiComodulusk k) ^ 2 * (jacobiSck z k)) * R1 + ((jacobiSck z k)) * R2

/-- DLMF 22.13.22: `ns'' = -(1 + k²) ns + 2 ns³`, away from the poles. -/
@[dlmf 22.13.E22 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiNsk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiNsk z k) z =
      -(1 + k ^ 2) * jacobiNsk z k + 2 * jacobiNsk z k ^ 3 := by
  have R1 := p22R1_sq_s1 hk hz
  have R2 := p22R1_sq_s2 hk hz
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiNsk z k) w) =ᶠ[𝓝 z]
    fun w => -(jacobiDsk w k * jacobiCsk w k) :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiNsk hk hw).deriv
  have hg :=
    (((hasDerivAt_jacobiDsk hk hz).mul (hasDerivAt_jacobiCsk hk hz)).neg).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination (-2 * (jacobiNsk z k)) * R1 + ((jacobiNsk z k)) * R2 + ((jacobiNsk z k)) * hK

/-- DLMF 22.13.23: `ds'' = (k² - k'²) ds + 2 ds³`, away from the poles. -/
@[dlmf 22.13.E23 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiDsk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiDsk z k) z =
      (k ^ 2 - jacobiComodulusk k ^ 2) * jacobiDsk z k + 2 * jacobiDsk z k ^ 3 := by
  have R1 := p22R1_sq_s1 hk hz
  have R2 := p22R1_sq_s2 hk hz
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiDsk z k) w) =ᶠ[𝓝 z]
    fun w => -(jacobiCsk w k * jacobiNsk w k) :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiDsk hk hw).deriv
  have hg :=
    (((hasDerivAt_jacobiCsk hk hz).mul (hasDerivAt_jacobiNsk hk hz)).neg).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination ((jacobiDsk z k)) * R1 + (-2 * (jacobiDsk z k)) * R2 + (-(jacobiDsk z k)) * hK

/-- DLMF 22.13.24: `cs'' = (1 + k'²) cs + 2 cs³`, away from the poles. -/
@[dlmf 22.13.E24 "domain: k ∈ jacobiModulusDomain, z not a pole"]
theorem iteratedDeriv_two_jacobiCsk (hk : k ∈ jacobiModulusDomain) {z : ℂ}
    (hz : jacobiLetterTheta .s (jacobiZetak z k) (jacobiTauk k) ≠ 0) :
    iteratedDeriv 2 (fun z => jacobiCsk z k) z =
      (1 + jacobiComodulusk k ^ 2) * jacobiCsk z k + 2 * jacobiCsk z k ^ 3 := by
  have R1 := p22R1_sq_s1 hk hz
  have R2 := p22R1_sq_s2 hk hz
  have hK := jacobiComodulusk_sq k
  have hev : (fun w => deriv (fun z => jacobiCsk z k) w) =ᶠ[𝓝 z]
    fun w => -(jacobiNsk w k * jacobiDsk w k) :=
    (p22R1_eventually_ne hk hz).mono fun w hw => (hasDerivAt_jacobiCsk hk hw).deriv
  have hg :=
    (((hasDerivAt_jacobiNsk hk hz).mul (hasDerivAt_jacobiDsk hk hz)).neg).congr_of_eventuallyEq hev
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hg.deriv]
  linear_combination ((jacobiCsk z k)) * R1 + ((jacobiCsk z k)) * R2

end Complex

/-! ### Real argument: Table 22.13.1 for the nine quotient functions -/

section RealArgument

open Real

variable {m : ℝ}

/-- `sn² + cn² = 1` and `m sn² + dn² = 1` at one point (helper). -/
lemma je22b_identities (hm : m < 1) (u : ℝ) :
    Real.jacobiSnm u m ^ 2 + Real.jacobiCnm u m ^ 2 = 1 ∧
      m * Real.jacobiSnm u m ^ 2 + Real.jacobiDnm u m ^ 2 = 1 :=
  ⟨Real.jacobiSnm_sq_add_jacobiCnm_sq u m, Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm u⟩

/-- DLMF Table 22.13.1, real argument: `d sd/du = cd nd` with `sd = sn/dn`, `cd = cn/dn`,
`nd = 1/dn`, for real parameter `m < 1`. -/
@[dlmf 22.13.T1 "special case: real argument, real parameter m = k² < 1"]
theorem Real.hasDerivAt_jacobiSdm (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => Real.jacobiSnm u m / Real.jacobiDnm u m)
      (Real.jacobiCnm u m / Real.jacobiDnm u m * (1 / Real.jacobiDnm u m)) u := by
  have hd := (Real.jacobiDnm_pos hm u).ne'
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  refine ((Real.hasDerivAt_jacobiSnm hm u).div (Real.hasDerivAt_jacobiDnm hm u) hd).congr_deriv ?_
  field_simp
  linear_combination (Real.jacobiCnm u m) * h2

/-- DLMF Table 22.13.1, real argument: `d cd/du = -k'² sd nd`, `k'² = 1 - m`. -/
@[dlmf 22.13.T1 "special case: real argument, real parameter m = k² < 1"]
theorem Real.hasDerivAt_jacobiCdm (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => Real.jacobiCnm u m / Real.jacobiDnm u m)
      (-((1 - m) * (Real.jacobiSnm u m / Real.jacobiDnm u m) * (1 / Real.jacobiDnm u m))) u := by
  have hd := (Real.jacobiDnm_pos hm u).ne'
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  refine ((Real.hasDerivAt_jacobiCnm hm u).div (Real.hasDerivAt_jacobiDnm hm u) hd).congr_deriv ?_
  field_simp
  linear_combination -(Real.jacobiSnm u m) * h2 + m * Real.jacobiSnm u m * h1

/-- DLMF Table 22.13.1, real argument: `d nd/du = k² sd cd`, `k² = m`. -/
@[dlmf 22.13.T1 "special case: real argument, real parameter m = k² < 1"]
theorem Real.hasDerivAt_jacobiNdm (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => 1 / Real.jacobiDnm u m)
      (m * (Real.jacobiSnm u m / Real.jacobiDnm u m) * (Real.jacobiCnm u m / Real.jacobiDnm u m))
      u := by
  have hd := (Real.jacobiDnm_pos hm u).ne'
  refine ((hasDerivAt_const u (1 : ℝ)).div (Real.hasDerivAt_jacobiDnm hm u) hd).congr_deriv ?_
  field_simp
  ring

/-- DLMF Table 22.13.1, real argument: `d dc/du = k'² sc nc`, where `cn u ≠ 0`. -/
@[dlmf 22.13.T1 "special case: real argument, real parameter m = k² < 1, cn u ≠ 0"]
theorem Real.hasDerivAt_jacobiDcm (hm : m < 1) {u : ℝ} (hc : Real.jacobiCnm u m ≠ 0) :
    HasDerivAt (fun u => Real.jacobiDnm u m / Real.jacobiCnm u m)
      ((1 - m) * (Real.jacobiSnm u m / Real.jacobiCnm u m) * (1 / Real.jacobiCnm u m)) u := by
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  refine ((Real.hasDerivAt_jacobiDnm hm u).div (Real.hasDerivAt_jacobiCnm hm u) hc).congr_deriv ?_
  field_simp
  linear_combination (Real.jacobiSnm u m) * h2 - m * Real.jacobiSnm u m * h1

/-- DLMF Table 22.13.1, real argument: `d nc/du = sc dc`, where `cn u ≠ 0`. -/
@[dlmf 22.13.T1 "special case: real argument, real parameter m = k² < 1, cn u ≠ 0"]
theorem Real.hasDerivAt_jacobiNcm (hm : m < 1) {u : ℝ} (hc : Real.jacobiCnm u m ≠ 0) :
    HasDerivAt (fun u => 1 / Real.jacobiCnm u m)
      (Real.jacobiSnm u m / Real.jacobiCnm u m * (Real.jacobiDnm u m / Real.jacobiCnm u m)) u := by
  refine ((hasDerivAt_const u (1 : ℝ)).div (Real.hasDerivAt_jacobiCnm hm u) hc).congr_deriv ?_
  field_simp
  ring

/-- DLMF Table 22.13.1, real argument: `d sc/du = dc nc`, where `cn u ≠ 0`. -/
@[dlmf 22.13.T1 "special case: real argument, real parameter m = k² < 1, cn u ≠ 0"]
theorem Real.hasDerivAt_jacobiScm (hm : m < 1) {u : ℝ} (hc : Real.jacobiCnm u m ≠ 0) :
    HasDerivAt (fun u => Real.jacobiSnm u m / Real.jacobiCnm u m)
      (Real.jacobiDnm u m / Real.jacobiCnm u m * (1 / Real.jacobiCnm u m)) u := by
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  refine ((Real.hasDerivAt_jacobiSnm hm u).div (Real.hasDerivAt_jacobiCnm hm u) hc).congr_deriv ?_
  field_simp
  linear_combination (Real.jacobiDnm u m) * h1

/-- DLMF Table 22.13.1, real argument: `d ns/du = -ds cs`, where `sn u ≠ 0`. -/
@[dlmf 22.13.T1 "special case: real argument, real parameter m = k² < 1, sn u ≠ 0"]
theorem Real.hasDerivAt_jacobiNsm (hm : m < 1) {u : ℝ} (hs : Real.jacobiSnm u m ≠ 0) :
    HasDerivAt (fun u => 1 / Real.jacobiSnm u m)
      (-(Real.jacobiDnm u m / Real.jacobiSnm u m * (Real.jacobiCnm u m / Real.jacobiSnm u m)))
      u := by
  refine ((hasDerivAt_const u (1 : ℝ)).div (Real.hasDerivAt_jacobiSnm hm u) hs).congr_deriv ?_
  field_simp
  ring

/-- DLMF Table 22.13.1, real argument: `d ds/du = -cs ns`, where `sn u ≠ 0`. -/
@[dlmf 22.13.T1 "special case: real argument, real parameter m = k² < 1, sn u ≠ 0"]
theorem Real.hasDerivAt_jacobiDsm (hm : m < 1) {u : ℝ} (hs : Real.jacobiSnm u m ≠ 0) :
    HasDerivAt (fun u => Real.jacobiDnm u m / Real.jacobiSnm u m)
      (-(Real.jacobiCnm u m / Real.jacobiSnm u m * (1 / Real.jacobiSnm u m))) u := by
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  refine ((Real.hasDerivAt_jacobiDnm hm u).div (Real.hasDerivAt_jacobiSnm hm u) hs).congr_deriv ?_
  field_simp
  linear_combination -(Real.jacobiCnm u m) * h2

/-- DLMF Table 22.13.1, real argument: `d cs/du = -ns ds`, where `sn u ≠ 0`. -/
@[dlmf 22.13.T1 "special case: real argument, real parameter m = k² < 1, sn u ≠ 0"]
theorem Real.hasDerivAt_jacobiCsm (hm : m < 1) {u : ℝ} (hs : Real.jacobiSnm u m ≠ 0) :
    HasDerivAt (fun u => Real.jacobiCnm u m / Real.jacobiSnm u m)
      (-(1 / Real.jacobiSnm u m * (Real.jacobiDnm u m / Real.jacobiSnm u m))) u := by
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  refine ((Real.hasDerivAt_jacobiCnm hm u).div (Real.hasDerivAt_jacobiSnm hm u) hs).congr_deriv ?_
  field_simp
  linear_combination -(Real.jacobiDnm u m) * h1


/-! ### Real argument: first-order equations 22.13.4–22.13.12 -/

/-- DLMF 22.13.4, real argument: the first-order equation of `cd = Real.jacobiCnm / Real.jacobiDnm`
for real parameter `m = k² < 1` (`k'² = 1 - m`). -/
@[dlmf 22.13.E4 "special case: real argument, real parameter m = k² < 1"]
theorem Real.deriv_jacobiCdm_sq (hm : m < 1) (u : ℝ) :
    deriv (fun u => Real.jacobiCnm u m / Real.jacobiDnm u m) u ^ 2 =
      (1 - (Real.jacobiCnm u m / Real.jacobiDnm u m) ^ 2) * (1 - m * (Real.jacobiCnm u m /
          Real.jacobiDnm u m) ^ 2) := by
  have hd := (Real.jacobiDnm_pos hm u).ne'
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  rw [(Real.hasDerivAt_jacobiCdm hm u).deriv]
  field_simp
  linear_combination (-(Real.jacobiCnm u m)^2*m + (Real.jacobiDnm u m)^2*m - m + 1) * h1 +
      ((Real.jacobiCnm u m)^2 - (Real.jacobiDnm u m)^2 + m - 1) * h2

/-- DLMF 22.13.5, real argument: the first-order equation of `sd = Real.jacobiSnm / Real.jacobiDnm`
for real parameter `m = k² < 1` (`k'² = 1 - m`). -/
@[dlmf 22.13.E5 "special case: real argument, real parameter m = k² < 1"]
theorem Real.deriv_jacobiSdm_sq (hm : m < 1) (u : ℝ) :
    deriv (fun u => Real.jacobiSnm u m / Real.jacobiDnm u m) u ^ 2 =
      (1 - (1 - m) * (Real.jacobiSnm u m / Real.jacobiDnm u m) ^ 2) * (1 + m *
          (Real.jacobiSnm u m / Real.jacobiDnm u m) ^ 2) := by
  have hd := (Real.jacobiDnm_pos hm u).ne'
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  rw [(Real.hasDerivAt_jacobiSdm hm u).deriv]
  field_simp
  linear_combination (-(Real.jacobiDnm u m)^2*m + (Real.jacobiDnm u m)^2 -
      m^2*(Real.jacobiSnm u m)^2 + m*(Real.jacobiSnm u m)^2 + m) * h1 + ((Real.jacobiCnm u m)^2*m -
      (Real.jacobiCnm u m)^2 - (Real.jacobiDnm u m)^2 - m) * h2

/-- DLMF 22.13.6, real argument: the first-order equation of `nd = 1 / Real.jacobiDnm`
for real parameter `m = k² < 1` (`k'² = 1 - m`). -/
@[dlmf 22.13.E6 "special case: real argument, real parameter m = k² < 1"]
theorem Real.deriv_jacobiNdm_sq (hm : m < 1) (u : ℝ) :
    deriv (fun u => 1 / Real.jacobiDnm u m) u ^ 2 =
      ((1 / Real.jacobiDnm u m) ^ 2 - 1) * (1 - (1 - m) * (1 / Real.jacobiDnm u m) ^ 2) := by
  have hd := (Real.jacobiDnm_pos hm u).ne'
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  rw [(Real.hasDerivAt_jacobiNdm hm u).deriv]
  field_simp
  linear_combination (-(Real.jacobiDnm u m)^2*m + m) * h1 + ((Real.jacobiCnm u m)^2*m +
      (Real.jacobiDnm u m)^2 - 1) * h2

/-- DLMF 22.13.7, real argument: the first-order equation of `dc = Real.jacobiDnm / Real.jacobiCnm`
for real parameter `m = k² < 1` (`k'² = 1 - m`), cn u ≠ 0. -/
@[dlmf 22.13.E7 "special case: real argument, real parameter m = k² < 1, cn u ≠ 0"]
theorem Real.deriv_jacobiDcm_sq (hm : m < 1) {u : ℝ} (hc : Real.jacobiCnm u m ≠ 0) :
    deriv (fun u => Real.jacobiDnm u m / Real.jacobiCnm u m) u ^ 2 =
      ((Real.jacobiDnm u m / Real.jacobiCnm u m) ^ 2 - 1) * ((Real.jacobiDnm u m /
          Real.jacobiCnm u m) ^ 2 - m) := by
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  rw [(Real.hasDerivAt_jacobiDcm hm hc).deriv]
  field_simp
  linear_combination (-(Real.jacobiCnm u m)^2*m + (Real.jacobiDnm u m)^2*m - m + 1) * h1 +
      ((Real.jacobiCnm u m)^2 - (Real.jacobiDnm u m)^2 + m - 1) * h2

/-- DLMF 22.13.8, real argument: the first-order equation of `nc = 1 / Real.jacobiCnm`
for real parameter `m = k² < 1` (`k'² = 1 - m`), cn u ≠ 0. -/
@[dlmf 22.13.E8 "special case: real argument, real parameter m = k² < 1, cn u ≠ 0"]
theorem Real.deriv_jacobiNcm_sq (hm : m < 1) {u : ℝ} (hc : Real.jacobiCnm u m ≠ 0) :
    deriv (fun u => 1 / Real.jacobiCnm u m) u ^ 2 =
      (m + (1 - m) * (1 / Real.jacobiCnm u m) ^ 2) * ((1 / Real.jacobiCnm u m) ^ 2 - 1) := by
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  rw [(Real.hasDerivAt_jacobiNcm hm hc).deriv]
  field_simp
  linear_combination ((Real.jacobiCnm u m)^2*m + (Real.jacobiDnm u m)^2 - m) * h1 + (1 -
      (Real.jacobiCnm u m)^2) * h2

/-- DLMF 22.13.9, real argument: the first-order equation of `sc = Real.jacobiSnm / Real.jacobiCnm`
for real parameter `m = k² < 1` (`k'² = 1 - m`), cn u ≠ 0. -/
@[dlmf 22.13.E9 "special case: real argument, real parameter m = k² < 1, cn u ≠ 0"]
theorem Real.deriv_jacobiScm_sq (hm : m < 1) {u : ℝ} (hc : Real.jacobiCnm u m ≠ 0) :
    deriv (fun u => Real.jacobiSnm u m / Real.jacobiCnm u m) u ^ 2 =
      (1 + (Real.jacobiSnm u m / Real.jacobiCnm u m) ^ 2) * (1 + (1 - m) * (Real.jacobiSnm u m /
          Real.jacobiCnm u m) ^ 2) := by
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  rw [(Real.hasDerivAt_jacobiScm hm hc).deriv]
  field_simp
  linear_combination (-(Real.jacobiCnm u m)^2 + m*(Real.jacobiSnm u m)^2 - (Real.jacobiSnm u m)^2 -
      1) * h1 + (1) * h2

/-- DLMF 22.13.10, real argument: the first-order equation of `ns = 1 / Real.jacobiSnm`
for real parameter `m = k² < 1` (`k'² = 1 - m`), sn u ≠ 0. -/
@[dlmf 22.13.E10 "special case: real argument, real parameter m = k² < 1, sn u ≠ 0"]
theorem Real.deriv_jacobiNsm_sq (hm : m < 1) {u : ℝ} (hs : Real.jacobiSnm u m ≠ 0) :
    deriv (fun u => 1 / Real.jacobiSnm u m) u ^ 2 =
      ((1 / Real.jacobiSnm u m) ^ 2 - m) * ((1 / Real.jacobiSnm u m) ^ 2 - 1) := by
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  rw [(Real.hasDerivAt_jacobiNsm hm hs).deriv]
  field_simp
  linear_combination (-m*(Real.jacobiSnm u m)^2 + 1) * h1 + ((Real.jacobiCnm u m)^2) * h2

/-- DLMF 22.13.11, real argument: the first-order equation of `ds = Real.jacobiDnm / Real.jacobiSnm`
for real parameter `m = k² < 1` (`k'² = 1 - m`), sn u ≠ 0. -/
@[dlmf 22.13.E11 "special case: real argument, real parameter m = k² < 1, sn u ≠ 0"]
theorem Real.deriv_jacobiDsm_sq (hm : m < 1) {u : ℝ} (hs : Real.jacobiSnm u m ≠ 0) :
    deriv (fun u => Real.jacobiDnm u m / Real.jacobiSnm u m) u ^ 2 =
      ((Real.jacobiDnm u m / Real.jacobiSnm u m) ^ 2 - (1 - m)) * (m + (Real.jacobiDnm u m /
          Real.jacobiSnm u m) ^ 2) := by
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  rw [(Real.hasDerivAt_jacobiDsm hm hs).deriv]
  field_simp
  linear_combination (-(Real.jacobiDnm u m)^2*m + (Real.jacobiDnm u m)^2 -
      m^2*(Real.jacobiSnm u m)^2 + m*(Real.jacobiSnm u m)^2 + m) * h1 + ((Real.jacobiCnm u m)^2*m -
      (Real.jacobiCnm u m)^2 - (Real.jacobiDnm u m)^2 - m) * h2

/-- DLMF 22.13.12, real argument: the first-order equation of `cs = Real.jacobiCnm / Real.jacobiSnm`
for real parameter `m = k² < 1` (`k'² = 1 - m`), sn u ≠ 0. -/
@[dlmf 22.13.E12 "special case: real argument, real parameter m = k² < 1, sn u ≠ 0"]
theorem Real.deriv_jacobiCsm_sq (hm : m < 1) {u : ℝ} (hs : Real.jacobiSnm u m ≠ 0) :
    deriv (fun u => Real.jacobiCnm u m / Real.jacobiSnm u m) u ^ 2 =
      (1 + (Real.jacobiCnm u m / Real.jacobiSnm u m) ^ 2) * ((1 - m) + (Real.jacobiCnm u m /
          Real.jacobiSnm u m) ^ 2) := by
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  rw [(Real.hasDerivAt_jacobiCsm hm hs).deriv]
  field_simp
  linear_combination (-(Real.jacobiCnm u m)^2 + m*(Real.jacobiSnm u m)^2 - (Real.jacobiSnm u m)^2 -
      1) * h1 + (1) * h2

/-! ### Real argument: second-order equations 22.13.16–22.13.24 -/

/-- DLMF 22.13.16, real argument: the second-order equation of `cd = Real.jacobiCnm /
Real.jacobiDnm`
for real parameter `m = k² < 1` (`k'² = 1 - m`). -/
@[dlmf 22.13.E16 "special case: real argument, real parameter m = k² < 1"]
theorem Real.iteratedDeriv_two_jacobiCdm (hm : m < 1) (u : ℝ) :
    iteratedDeriv 2 (fun u => Real.jacobiCnm u m / Real.jacobiDnm u m) u =
      -(1 + m) * (Real.jacobiCnm u m / Real.jacobiDnm u m) + 2 * m * (Real.jacobiCnm u m /
          Real.jacobiDnm u m) ^ 3 := by
  have hd0 := (Real.jacobiDnm_pos hm u).ne'
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  have h' : HasDerivAt (fun v => -((1 - m) * (Real.jacobiSnm v m / Real.jacobiDnm v m) * (1 /
      Real.jacobiDnm v m))) _ u :=
    (((Real.hasDerivAt_jacobiSdm hm u).const_mul (1 - m)).mul (Real.hasDerivAt_jacobiNdm hm u)).neg
  have hd : deriv (fun u => Real.jacobiCnm u m / Real.jacobiDnm u m) = fun v => _ :=
    funext fun v => (Real.hasDerivAt_jacobiCdm hm v).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd, h'.deriv]
  field_simp
  linear_combination (-2*(Real.jacobiCnm u m)*m) * h1 + ((Real.jacobiCnm u m)*m +
      (Real.jacobiCnm u m)) * h2

/-- DLMF 22.13.17, real argument: the second-order equation of `sd = Real.jacobiSnm /
Real.jacobiDnm`
for real parameter `m = k² < 1` (`k'² = 1 - m`). -/
@[dlmf 22.13.E17 "special case: real argument, real parameter m = k² < 1"]
theorem Real.iteratedDeriv_two_jacobiSdm (hm : m < 1) (u : ℝ) :
    iteratedDeriv 2 (fun u => Real.jacobiSnm u m / Real.jacobiDnm u m) u =
      (m - (1 - m)) * (Real.jacobiSnm u m / Real.jacobiDnm u m) - 2 * m * (1 - m) *
          (Real.jacobiSnm u m / Real.jacobiDnm u m) ^ 3 := by
  have hd0 := (Real.jacobiDnm_pos hm u).ne'
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  have h' : HasDerivAt (fun v => (Real.jacobiCnm v m / Real.jacobiDnm v m) * (1 /
      Real.jacobiDnm v m)) _ u :=
    (Real.hasDerivAt_jacobiCdm hm u).mul (Real.hasDerivAt_jacobiNdm hm u)
  have hd : deriv (fun u => Real.jacobiSnm u m / Real.jacobiDnm u m) = fun v => _ :=
    funext fun v => (Real.hasDerivAt_jacobiSdm hm v).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd, h'.deriv]
  field_simp
  linear_combination (m*(Real.jacobiSnm u m)) * h1 + (-2*m*(Real.jacobiSnm u m) +
      (Real.jacobiSnm u m)) * h2

/-- DLMF 22.13.18, real argument: the second-order equation of `nd = 1 / Real.jacobiDnm`
for real parameter `m = k² < 1` (`k'² = 1 - m`). -/
@[dlmf 22.13.E18 "special case: real argument, real parameter m = k² < 1"]
theorem Real.iteratedDeriv_two_jacobiNdm (hm : m < 1) (u : ℝ) :
    iteratedDeriv 2 (fun u => 1 / Real.jacobiDnm u m) u =
      (1 + (1 - m)) * (1 / Real.jacobiDnm u m) - 2 * (1 - m) * (1 / Real.jacobiDnm u m) ^ 3 := by
  have hd0 := (Real.jacobiDnm_pos hm u).ne'
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  have h' : HasDerivAt (fun v => m * (Real.jacobiSnm v m / Real.jacobiDnm v m) *
      (Real.jacobiCnm v m / Real.jacobiDnm v m)) _ u :=
    ((Real.hasDerivAt_jacobiSdm hm u).const_mul m).mul (Real.hasDerivAt_jacobiCdm hm u)
  have hd : deriv (fun u => 1 / Real.jacobiDnm u m) = fun v => _ :=
    funext fun v => (Real.hasDerivAt_jacobiNdm hm v).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd, h'.deriv]
  field_simp
  linear_combination (m) * h1 + (m - 2) * h2

/-- DLMF 22.13.19, real argument: the second-order equation of `dc = Real.jacobiDnm /
Real.jacobiCnm`
for real parameter `m = k² < 1` (`k'² = 1 - m`), cn u ≠ 0. -/
@[dlmf 22.13.E19 "special case: real argument, real parameter m = k² < 1, cn u ≠ 0"]
theorem Real.iteratedDeriv_two_jacobiDcm (hm : m < 1) {u : ℝ} (hc : Real.jacobiCnm u m ≠ 0) :
    iteratedDeriv 2 (fun u => Real.jacobiDnm u m / Real.jacobiCnm u m) u =
      -(1 + m) * (Real.jacobiDnm u m / Real.jacobiCnm u m) + 2 * (Real.jacobiDnm u m /
          Real.jacobiCnm u m) ^ 3 := by
  have hd0 := (Real.jacobiDnm_pos hm u).ne'
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  have h' : HasDerivAt (fun v => (1 - m) * (Real.jacobiSnm v m / Real.jacobiCnm v m) * (1 /
      Real.jacobiCnm v m)) _ u :=
    ((Real.hasDerivAt_jacobiScm hm hc).const_mul (1 - m)).mul (Real.hasDerivAt_jacobiNcm hm hc)
  have hev : ∀ᶠ v in 𝓝 u, Real.jacobiCnm v m ≠ 0 :=
    (Real.hasDerivAt_jacobiCnm hm u).continuousAt.eventually_ne hc
  have hd : deriv (fun u => Real.jacobiDnm u m / Real.jacobiCnm u m) =ᶠ[𝓝 u] fun v => _ :=
    hev.mono fun v hv => (Real.hasDerivAt_jacobiDcm hm hv).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd.deriv_eq, h'.deriv]
  field_simp
  linear_combination (m + 1) * h1 + (-2) * h2

/-- DLMF 22.13.20, real argument: the second-order equation of `nc = 1 / Real.jacobiCnm`
for real parameter `m = k² < 1` (`k'² = 1 - m`), cn u ≠ 0. -/
@[dlmf 22.13.E20 "special case: real argument, real parameter m = k² < 1, cn u ≠ 0"]
theorem Real.iteratedDeriv_two_jacobiNcm (hm : m < 1) {u : ℝ} (hc : Real.jacobiCnm u m ≠ 0) :
    iteratedDeriv 2 (fun u => 1 / Real.jacobiCnm u m) u =
      (m - (1 - m)) * (1 / Real.jacobiCnm u m) + 2 * (1 - m) * (1 / Real.jacobiCnm u m) ^ 3 := by
  have hd0 := (Real.jacobiDnm_pos hm u).ne'
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  have h' : HasDerivAt (fun v => (Real.jacobiSnm v m / Real.jacobiCnm v m) * (Real.jacobiDnm v m /
      Real.jacobiCnm v m)) _ u :=
    (Real.hasDerivAt_jacobiScm hm hc).mul (Real.hasDerivAt_jacobiDcm hm hc)
  have hev : ∀ᶠ v in 𝓝 u, Real.jacobiCnm v m ≠ 0 :=
    (Real.hasDerivAt_jacobiCnm hm u).continuousAt.eventually_ne hc
  have hd : deriv (fun u => 1 / Real.jacobiCnm u m) =ᶠ[𝓝 u] fun v => _ :=
    hev.mono fun v hv => (Real.hasDerivAt_jacobiNcm hm hv).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd.deriv_eq, h'.deriv]
  field_simp
  linear_combination (1 - 2*m) * h1 + (1) * h2

/-- DLMF 22.13.21, real argument: the second-order equation of `sc = Real.jacobiSnm /
Real.jacobiCnm`
for real parameter `m = k² < 1` (`k'² = 1 - m`), cn u ≠ 0. -/
@[dlmf 22.13.E21 "special case: real argument, real parameter m = k² < 1, cn u ≠ 0"]
theorem Real.iteratedDeriv_two_jacobiScm (hm : m < 1) {u : ℝ} (hc : Real.jacobiCnm u m ≠ 0) :
    iteratedDeriv 2 (fun u => Real.jacobiSnm u m / Real.jacobiCnm u m) u =
      (1 + (1 - m)) * (Real.jacobiSnm u m / Real.jacobiCnm u m) + 2 * (1 - m) *
          (Real.jacobiSnm u m / Real.jacobiCnm u m) ^ 3 := by
  have hd0 := (Real.jacobiDnm_pos hm u).ne'
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  have h' : HasDerivAt (fun v => (Real.jacobiDnm v m / Real.jacobiCnm v m) * (1 /
      Real.jacobiCnm v m)) _ u :=
    (Real.hasDerivAt_jacobiDcm hm hc).mul (Real.hasDerivAt_jacobiNcm hm hc)
  have hev : ∀ᶠ v in 𝓝 u, Real.jacobiCnm v m ≠ 0 :=
    (Real.hasDerivAt_jacobiCnm hm u).continuousAt.eventually_ne hc
  have hd : deriv (fun u => Real.jacobiSnm u m / Real.jacobiCnm u m) =ᶠ[𝓝 u] fun v => _ :=
    hev.mono fun v hv => (Real.hasDerivAt_jacobiScm hm hv).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd.deriv_eq, h'.deriv]
  field_simp
  linear_combination (m*(Real.jacobiSnm u m) - 2*(Real.jacobiSnm u m)) * h1 +
      ((Real.jacobiSnm u m)) * h2

/-- DLMF 22.13.22, real argument: the second-order equation of `ns = 1 / Real.jacobiSnm`
for real parameter `m = k² < 1` (`k'² = 1 - m`), sn u ≠ 0. -/
@[dlmf 22.13.E22 "special case: real argument, real parameter m = k² < 1, sn u ≠ 0"]
theorem Real.iteratedDeriv_two_jacobiNsm (hm : m < 1) {u : ℝ} (hs : Real.jacobiSnm u m ≠ 0) :
    iteratedDeriv 2 (fun u => 1 / Real.jacobiSnm u m) u =
      -(1 + m) * (1 / Real.jacobiSnm u m) + 2 * (1 / Real.jacobiSnm u m) ^ 3 := by
  have hd0 := (Real.jacobiDnm_pos hm u).ne'
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  have h' : HasDerivAt (fun v => -((Real.jacobiDnm v m / Real.jacobiSnm v m) *
      (Real.jacobiCnm v m / Real.jacobiSnm v m))) _ u :=
    ((Real.hasDerivAt_jacobiDsm hm hs).mul (Real.hasDerivAt_jacobiCsm hm hs)).neg
  have hev : ∀ᶠ v in 𝓝 u, Real.jacobiSnm v m ≠ 0 :=
    (Real.hasDerivAt_jacobiSnm hm u).continuousAt.eventually_ne hs
  have hd : deriv (fun u => 1 / Real.jacobiSnm u m) =ᶠ[𝓝 u] fun v => _ :=
    hev.mono fun v hv => (Real.hasDerivAt_jacobiNsm hm hv).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd.deriv_eq, h'.deriv]
  field_simp
  linear_combination (1) * h1 + (1) * h2

/-- DLMF 22.13.23, real argument: the second-order equation of `ds = Real.jacobiDnm /
Real.jacobiSnm`
for real parameter `m = k² < 1` (`k'² = 1 - m`), sn u ≠ 0. -/
@[dlmf 22.13.E23 "special case: real argument, real parameter m = k² < 1, sn u ≠ 0"]
theorem Real.iteratedDeriv_two_jacobiDsm (hm : m < 1) {u : ℝ} (hs : Real.jacobiSnm u m ≠ 0) :
    iteratedDeriv 2 (fun u => Real.jacobiDnm u m / Real.jacobiSnm u m) u =
      (m - (1 - m)) * (Real.jacobiDnm u m / Real.jacobiSnm u m) + 2 * (Real.jacobiDnm u m /
          Real.jacobiSnm u m) ^ 3 := by
  have hd0 := (Real.jacobiDnm_pos hm u).ne'
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  have h' : HasDerivAt (fun v => -((Real.jacobiCnm v m / Real.jacobiSnm v m) * (1 /
      Real.jacobiSnm v m))) _ u :=
    ((Real.hasDerivAt_jacobiCsm hm hs).mul (Real.hasDerivAt_jacobiNsm hm hs)).neg
  have hev : ∀ᶠ v in 𝓝 u, Real.jacobiSnm v m ≠ 0 :=
    (Real.hasDerivAt_jacobiSnm hm u).continuousAt.eventually_ne hs
  have hd : deriv (fun u => Real.jacobiDnm u m / Real.jacobiSnm u m) =ᶠ[𝓝 u] fun v => _ :=
    hev.mono fun v hv => (Real.hasDerivAt_jacobiDsm hm hv).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd.deriv_eq, h'.deriv]
  field_simp
  linear_combination (1) * h1 + (-2) * h2

/-- DLMF 22.13.24, real argument: the second-order equation of `cs = Real.jacobiCnm /
Real.jacobiSnm`
for real parameter `m = k² < 1` (`k'² = 1 - m`), sn u ≠ 0. -/
@[dlmf 22.13.E24 "special case: real argument, real parameter m = k² < 1, sn u ≠ 0"]
theorem Real.iteratedDeriv_two_jacobiCsm (hm : m < 1) {u : ℝ} (hs : Real.jacobiSnm u m ≠ 0) :
    iteratedDeriv 2 (fun u => Real.jacobiCnm u m / Real.jacobiSnm u m) u =
      (1 + (1 - m)) * (Real.jacobiCnm u m / Real.jacobiSnm u m) + 2 * (Real.jacobiCnm u m /
          Real.jacobiSnm u m) ^ 3 := by
  have hd0 := (Real.jacobiDnm_pos hm u).ne'
  obtain ⟨h1, h2⟩ := je22b_identities hm u
  have h' : HasDerivAt (fun v => -((1 / Real.jacobiSnm v m) * (Real.jacobiDnm v m /
      Real.jacobiSnm v m))) _ u :=
    ((Real.hasDerivAt_jacobiNsm hm hs).mul (Real.hasDerivAt_jacobiDsm hm hs)).neg
  have hev : ∀ᶠ v in 𝓝 u, Real.jacobiSnm v m ≠ 0 :=
    (Real.hasDerivAt_jacobiSnm hm u).continuousAt.eventually_ne hs
  have hd : deriv (fun u => Real.jacobiCnm u m / Real.jacobiSnm u m) =ᶠ[𝓝 u] fun v => _ :=
    hev.mono fun v hv => (Real.hasDerivAt_jacobiCsm hm hv).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd.deriv_eq, h'.deriv]
  field_simp
  linear_combination (-2*(Real.jacobiCnm u m)) * h1 + ((Real.jacobiCnm u m)) * h2

end RealArgument

end DLMF.JacobiElliptic
