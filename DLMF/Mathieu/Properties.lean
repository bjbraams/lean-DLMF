/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Basic
public import DLMF.Elementary.Trigonometric
public import DLMFMathlib.Analysis.ODE.Singularities

/-!
# Basic properties of Mathieu's equation and its solutions (DLMF §28.2)

The algebraic forms of Mathieu's equation (28.2.2, 28.2.3), the symmetries 28.2.4, the parity,
Wronskian and half-period relations of the basic solutions (28.2.5–28.2.13), Floquet theory
(28.2.14–28.2.20), the eigenvalues (28.2.21–28.2.28, Table 28.2.1) and the eigenfunctions
(Table 28.2.2, 28.2.29–28.2.39).

Proved here from the definitions of `DLMF.Mathieu.Basic` (hence relative to the admitted
existence theorem `exists_isMathieuSolution`, and for eigenvalue statements to the admitted
`mathieuSpecA_exists`, `mathieuSpecB_exists`): the algebraic forms, the symmetries, parity,
the Wronskian, 28.2.7–28.2.13, the connection formula 28.2.17 and the Floquet dichotomy of
§28.2(iv), the boundary conditions 28.2.21–28.2.22, the periodicity and parity of Table 28.2.2
and 28.2.38–28.2.39. Spectral statements (Sturm–Liouville theory, Ince's theorem) are
admitted.

The principal characteristic exponent `ν̂ = π⁻¹ arccos w_I(π; a, q)` uses the project's
principal arccosine `DLMF.Elementary.arccosPrincipal` (DLMF 4.23.16); no new definition is
made.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real

namespace DLMF.Mathieu

/-! ### Algebraic forms (§28.2(i)) -/

/-- **Algebraic form** of Mathieu's equation (DLMF 28.2.2): with `ζ = sin² z` and
`w(z) = W(ζ)`, `w'' + (a - 2q cos 2z) w` equals four times
`ζ(1-ζ)W'' + ½(1-2ζ)W' + ¼(a - 2q(1-2ζ))W` at `ζ = sin² z`. Hence `w` solves 28.2.1 iff `W`
solves 28.2.2 along `ζ = sin² z`. -/
@[dlmf 28.2.E2]
theorem algebraic_form_sin_sq (a q : ℂ) {W W' W'' : ℂ → ℂ}
    (h1 : ∀ ζ, HasDerivAt W (W' ζ) ζ) (h2 : ∀ ζ, HasDerivAt W' (W'' ζ) ζ) (z : ℂ) :
    deriv (deriv fun z => W (Complex.sin z ^ 2)) z +
        (a - 2 * q * Complex.cos (2 * z)) * W (Complex.sin z ^ 2) =
      4 * (Complex.sin z ^ 2 * (1 - Complex.sin z ^ 2) * W'' (Complex.sin z ^ 2) +
        1 / 2 * (1 - 2 * Complex.sin z ^ 2) * W' (Complex.sin z ^ 2) +
        1 / 4 * (a - 2 * q * (1 - 2 * Complex.sin z ^ 2)) * W (Complex.sin z ^ 2)) := by
  have hs : ∀ z : ℂ, HasDerivAt (fun z => Complex.sin z ^ 2)
      (2 * Complex.sin z * Complex.cos z) z := by
    intro z
    have := (Complex.hasDerivAt_sin z).mul (Complex.hasDerivAt_sin z)
    convert this using 1
    · funext y; rw [Pi.mul_apply]; ring
    · ring
  have hd : deriv (fun z => W (Complex.sin z ^ 2)) =
      fun z => W' (Complex.sin z ^ 2) * (2 * Complex.sin z * Complex.cos z) := by
    funext z
    exact (((h1 _).comp z (hs z)) :
      HasDerivAt (fun z => W (Complex.sin z ^ 2)) _ z).deriv
  have hsc : ∀ z : ℂ, HasDerivAt (fun z => 2 * Complex.sin z * Complex.cos z)
      (2 * Complex.cos z * Complex.cos z - 2 * Complex.sin z * Complex.sin z) z := by
    intro z
    have := ((Complex.hasDerivAt_sin z).const_mul 2).mul (Complex.hasDerivAt_cos z)
    convert this using 1; ring
  have e : HasDerivAt (fun z => W' (Complex.sin z ^ 2) * (2 * Complex.sin z * Complex.cos z))
      (W'' (Complex.sin z ^ 2) * (2 * Complex.sin z * Complex.cos z) *
        (2 * Complex.sin z * Complex.cos z) + W' (Complex.sin z ^ 2) *
        (2 * Complex.cos z * Complex.cos z - 2 * Complex.sin z * Complex.sin z)) z :=
    ((h2 _).comp z (hs z)).mul (hsc z)
  rw [hd, e.deriv]
  have hc2 : Complex.cos (2 * z) = 1 - 2 * Complex.sin z ^ 2 := by
    rw [Complex.cos_two_mul, ← Complex.sin_sq_add_cos_sq z]; ring
  have hp := Complex.sin_sq_add_cos_sq z
  rw [hc2]
  linear_combination (4 * Complex.sin z ^ 2 * W'' (Complex.sin z ^ 2) +
    2 * W' (Complex.sin z ^ 2)) * hp

/-- **Second algebraic form** of Mathieu's equation (DLMF 28.2.3): with `ζ = cos z` and
`w(z) = W(ζ)`, `w'' + (a - 2q cos 2z) w = (1-ζ²)W'' - ζW' + (a + 2q - 4qζ²)W` at `ζ = cos z`. -/
@[dlmf 28.2.E3]
theorem algebraic_form_cos (a q : ℂ) {W W' W'' : ℂ → ℂ}
    (h1 : ∀ ζ, HasDerivAt W (W' ζ) ζ) (h2 : ∀ ζ, HasDerivAt W' (W'' ζ) ζ) (z : ℂ) :
    deriv (deriv fun z => W (Complex.cos z)) z +
        (a - 2 * q * Complex.cos (2 * z)) * W (Complex.cos z) =
      (1 - Complex.cos z ^ 2) * W'' (Complex.cos z) - Complex.cos z * W' (Complex.cos z) +
        (a + 2 * q - 4 * q * Complex.cos z ^ 2) * W (Complex.cos z) := by
  have hd : deriv (fun z => W (Complex.cos z)) =
      fun z => W' (Complex.cos z) * (-Complex.sin z) := by
    funext z
    exact (((h1 _).comp z (Complex.hasDerivAt_cos z)) :
      HasDerivAt (fun z => W (Complex.cos z)) _ z).deriv
  have e : HasDerivAt (fun z => W' (Complex.cos z) * -Complex.sin z)
      (W'' (Complex.cos z) * -Complex.sin z * -Complex.sin z +
        W' (Complex.cos z) * -Complex.cos z) z :=
    ((h2 _).comp z (Complex.hasDerivAt_cos z)).mul (Complex.hasDerivAt_sin z).neg
  rw [hd, e.deriv]
  have hc2 : Complex.cos (2 * z) = 2 * Complex.cos z ^ 2 - 1 := Complex.cos_two_mul z
  have hp := Complex.sin_sq_add_cos_sq z
  rw [hc2]
  linear_combination W'' (Complex.cos z) * hp

/-- **Singularities of the algebraic form** (DLMF §28.2(i)): the normalized equation 28.2.2,
`W'' + c₁ W' + c₀ W = 0` with `c₁ = (1 - 2ζ)/(2ζ(1 - ζ))`, `c₀ = (a - 2q(1 - 2ζ))/(4ζ(1 - ζ))`,
has regular singularities at `ζ = 0` and `ζ = 1`, both with exponents `0` and `1/2` (the
indicial equation is `r(r - 1) + r/2 = 0`: `ζ c₁ → 1/2`, `ζ² c₀ → 0` at `0`, and likewise
`(ζ - 1) c₁ → 1/2`, `(ζ - 1)² c₀ → 0` at `1`), and for `q ≠ 0` an irregular singularity at `∞`. -/
@[dlmf 28.2.i]
theorem mathieu_algebraic_form_singularities (a q : ℂ) :
    let c : Fin 2 → ℂ → ℂ := ![fun ζ => (a - 2 * q * (1 - 2 * ζ)) / (4 * ζ * (1 - ζ)),
      fun ζ => (1 - 2 * ζ) / (2 * ζ * (1 - ζ))]
    Complex.linearODERegularSingularAt c 0 ∧ Complex.linearODERegularSingularAt c 1 ∧
      Tendsto (fun ζ => ζ * c 1 ζ) (𝓝[≠] 0) (𝓝 (1 / 2)) ∧
      Tendsto (fun ζ => ζ ^ 2 * c 0 ζ) (𝓝[≠] 0) (𝓝 0) ∧
      Tendsto (fun ζ => (ζ - 1) * c 1 ζ) (𝓝[≠] 1) (𝓝 (1 / 2)) ∧
      Tendsto (fun ζ => (ζ - 1) ^ 2 * c 0 ζ) (𝓝[≠] 1) (𝓝 0) ∧
      (q ≠ 0 → Complex.linearODEIrregularAtInfinity c) := by
  sorry

/-! ### Symmetries (28.2.4) -/

namespace IsMathieuSolution

variable {a q : ℂ} {w : ℂ → ℂ}

/-- Affine changes of variable `z ↦ σz + c` with `σ² = 1` map solutions for `(a, q)` to
solutions for `(a, q')` whenever `q cos 2(σz + c) = q' cos 2z`. -/
theorem comp_affine (h : IsMathieuSolution a q w) {σ c q' : ℂ} (hσ : σ ^ 2 = 1)
    (hc : ∀ z, q * Complex.cos (2 * (σ * z + c)) = q' * Complex.cos (2 * z)) :
    IsMathieuSolution a q' (fun z => w (σ * z + c)) := by
  have hl : ∀ z : ℂ, HasDerivAt (fun z => σ * z + c) σ z := fun z => by
    simpa using ((hasDerivAt_id z).const_mul σ).add_const c
  have hd : deriv (fun z => w (σ * z + c)) = fun z => σ * deriv w (σ * z + c) := by
    funext z
    have e : HasDerivAt (fun z => w (σ * z + c)) (deriv w (σ * z + c) * σ) z :=
      (h.differentiable _).hasDerivAt.comp z (hl z)
    rw [e.deriv, mul_comm]
  refine ⟨fun z => ((h.differentiable _).hasDerivAt.comp z (hl z)).differentiableAt,
    fun z => ?_⟩
  rw [hd]
  have := ((h.hasDerivAt_deriv (σ * z + c)).comp z (hl z)).const_mul σ
  convert this using 1
  simp only [Function.comp]
  linear_combination (-(2 : ℂ) * w (σ * z + c)) * hc z -
    (2 * q * Complex.cos (2 * (σ * z + c)) - a) * w (σ * z + c) * hσ

/-- **Reflection** `z ↦ -z` (DLMF 28.2.4) leaves Mathieu's equation unchanged. -/
@[dlmf 28.2.E4]
theorem comp_neg (h : IsMathieuSolution a q w) : IsMathieuSolution a q (fun z => w (-z)) := by
  have := h.comp_affine (σ := -1) (c := 0) (q' := q) (by norm_num)
    (fun z => by rw [show 2 * (-1 * z + 0) = -(2 * z) by ring, Complex.cos_neg])
  simpa using this

/-- **Translation** `z ↦ z + π` (DLMF 28.2.4) leaves Mathieu's equation unchanged. -/
@[dlmf 28.2.E4]
theorem comp_add_pi (h : IsMathieuSolution a q w) :
    IsMathieuSolution a q (fun z => w (z + π)) := by
  have := h.comp_affine (σ := 1) (c := π) (q' := q) (by norm_num)
    (fun z => by
      rw [show 2 * (1 * z + (π : ℂ)) = 2 * z + 2 * π by ring, Complex.cos_add_two_pi])
  simpa using this

/-- **Translation** `z ↦ z - π` (DLMF 28.2.4) leaves Mathieu's equation unchanged. -/
@[dlmf 28.2.E4]
theorem comp_sub_pi (h : IsMathieuSolution a q w) :
    IsMathieuSolution a q (fun z => w (z - π)) := by
  have := h.comp_affine (σ := 1) (c := -π) (q' := q) (by norm_num)
    (fun z => by
      rw [show 2 * (1 * z + -(π : ℂ)) = 2 * z - 2 * π by ring, Complex.cos_sub_two_pi])
  simpa [sub_eq_add_neg] using this

/-- **Half-period translation** `z ↦ z + π/2`, `q ↦ -q` (DLMF 28.2.4). -/
@[dlmf 28.2.E4]
theorem comp_add_half_pi (h : IsMathieuSolution a q w) :
    IsMathieuSolution a (-q) (fun z => w (z + π / 2)) := by
  have := h.comp_affine (σ := 1) (c := π / 2) (q' := -q) (by norm_num)
    (fun z => by
      rw [show 2 * (1 * z + (π : ℂ) / 2) = 2 * z + π by ring, Complex.cos_add_pi]; ring)
  simpa using this

/-- **Half-period translation** `z ↦ z - π/2`, `q ↦ -q` (DLMF 28.2.4). -/
@[dlmf 28.2.E4]
theorem comp_sub_half_pi (h : IsMathieuSolution a q w) :
    IsMathieuSolution a (-q) (fun z => w (z - π / 2)) := by
  have := h.comp_affine (σ := 1) (c := -(π / 2)) (q' := -q) (by norm_num)
    (fun z => by
      rw [show 2 * (1 * z + -((π : ℂ) / 2)) = 2 * z - π by ring, Complex.cos_sub_pi]; ring)
  simpa [sub_eq_add_neg] using this

/-- The reflection `z ↦ π - z` leaves Mathieu's equation unchanged (from 28.2.4). -/
theorem comp_pi_sub (h : IsMathieuSolution a q w) :
    IsMathieuSolution a q (fun z => w (π - z)) := by
  have := h.comp_affine (σ := -1) (c := π) (q' := q) (by norm_num)
    (fun z => by
      rw [show 2 * (-1 * z + (π : ℂ)) = -(2 * z) + 2 * π by ring, Complex.cos_add_two_pi,
        Complex.cos_neg])
  simpa [neg_mul, one_mul, neg_add_eq_sub] using this

/-- Derivative of `z ↦ w(σz + c)`. -/
theorem m28a_deriv_comp_affine (h : IsMathieuSolution a q w) (σ c z : ℂ) :
    deriv (fun z => w (σ * z + c)) z = σ * deriv w (σ * z + c) := by
  have hl : HasDerivAt (fun z => σ * z + c) σ z := by
    simpa using ((hasDerivAt_id z).const_mul σ).add_const c
  have e : HasDerivAt (fun z => w (σ * z + c)) (deriv w (σ * z + c) * σ) z :=
    (h.differentiable _).hasDerivAt.comp z hl
  rw [e.deriv, mul_comm]

end IsMathieuSolution

/-- Derivative of a linear combination `c f + d g`. -/
theorem m28a_deriv_lincomb {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℂ g z) (c d : ℂ) :
    deriv (fun x => c * f x + d * g x) z = c * deriv f z + d * deriv g z :=
  ((hf.hasDerivAt.const_mul c).add (hg.hasDerivAt.const_mul d)).deriv

/-- Derivative of a linear combination `c f - d g`. -/
theorem m28a_deriv_lincomb_sub {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℂ g z) (c d : ℂ) :
    deriv (fun x => c * f x - d * g x) z = c * deriv f z - d * deriv g z :=
  ((hf.hasDerivAt.const_mul c).sub (hg.hasDerivAt.const_mul d)).deriv

/-! ### The basic solutions (§28.2(ii)) -/

section Basic

variable (a q : ℂ)

local notation "wI" => mathieuWI a q
local notation "wII" => mathieuWII a q

/-- `w_I(z; a, q)` is even (DLMF §28.2(ii)). -/
@[dlmf 28.2.ii]
theorem mathieuWI_neg (z : ℂ) : wI (-z) = wI z := by
  obtain ⟨h, h0, h1⟩ := mathieuWI_spec a q
  have := h.comp_neg.eq_of_initial h (z₀ := 0) (by simp) (by
    rw [show deriv (fun z => wI (-z)) 0 = -deriv wI (-0) from deriv_comp_neg _ _]; simp [h1])
  exact congrFun this z

/-- `w_II(z; a, q)` is odd (DLMF §28.2(ii)). -/
@[dlmf 28.2.ii]
theorem mathieuWII_neg (z : ℂ) : wII (-z) = -wII z := by
  obtain ⟨h, h0, h1⟩ := mathieuWII_spec a q
  have := (h.comp_neg.const_mul (-1)).eq_of_initial h (z₀ := 0) (by simp [h0]) (by
    rw [show deriv (fun z => -1 * wII (-z)) 0 = -1 * deriv (fun z => wII (-z)) 0 from
      deriv_const_mul _ (h.differentiable.comp differentiable_neg 0)]
    rw [show deriv (fun z => wII (-z)) 0 = -deriv wII (-0) from deriv_comp_neg _ _]; simp [h1])
  have := congrFun this z
  linear_combination -this

/-- The derivative of `w_I` is odd. -/
theorem deriv_mathieuWI_neg (z : ℂ) : deriv wI (-z) = -deriv wI z := by
  have h := congrArg (fun f => deriv f z) (funext (mathieuWI_neg a q))
  rw [deriv_comp_neg] at h
  simpa using congrArg Neg.neg h

/-- The derivative of `w_II` is even. -/
theorem deriv_mathieuWII_neg (z : ℂ) : deriv wII (-z) = deriv wII z := by
  have h := congrArg (fun f => deriv f z) (funext (mathieuWII_neg a q))
  have hn : deriv (fun x => -wII x) z = -deriv wII z :=
    ((isMathieuSolution_mathieuWII a q).differentiable z).hasDerivAt.neg.deriv
  rw [deriv_comp_neg, hn] at h
  simpa using h

/-- **Wronskian** of the basic solutions (DLMF 28.2.6): `𝒲{w_I, w_II} = 1`. -/
@[dlmf 28.2.E6]
theorem mathieuWI_wronskian (z : ℂ) : wI z * deriv wII z - deriv wI z * wII z = 1 := by
  obtain ⟨h1, h10, h11⟩ := mathieuWI_spec a q
  obtain ⟨h2, h20, h21⟩ := mathieuWII_spec a q
  have hW : ∀ z, HasDerivAt (fun z => wI z * deriv wII z - deriv wI z * wII z) 0 z := by
    intro z
    have := ((h1.differentiable z).hasDerivAt.mul (h2.hasDerivAt_deriv z)).sub
      ((h1.hasDerivAt_deriv z).mul (h2.differentiable z).hasDerivAt)
    convert this using 1; ring
  have := is_const_of_deriv_eq_zero (fun z => (hW z).differentiableAt) (fun z => (hW z).deriv)
    z 0
  rw [this]; simp [h10, h11, h20, h21]

/-- Half-period reflection identity for `w_I` about `π/2`:
`w_I(π - z) = (AB' + A'B) w_I(z) - 2AA' w_II(z)` with `A = w_I(π/2)`, `B = w_II(π/2)`. -/
theorem m28a_mathieuWI_pi_sub (z : ℂ) :
    wI (π - z) = (wI (π / 2) * deriv wII (π / 2) + deriv wI (π / 2) * wII (π / 2)) * wI z -
      2 * wI (π / 2) * deriv wI (π / 2) * wII z := by
  obtain ⟨h1, -, -⟩ := mathieuWI_spec a q
  obtain ⟨h2, -, -⟩ := mathieuWII_spec a q
  have hW := mathieuWI_wronskian a q (π / 2)
  have hr := h1.comp_pi_sub
  have hc := (h1.const_mul (wI (π / 2) * deriv wII (π / 2) + deriv wI (π / 2) * wII (π / 2))).add
    (h2.const_mul (-(2 * wI (π / 2) * deriv wI (π / 2))))
  have key := hr.eq_of_initial hc (z₀ := π / 2) (by
      rw [show (π : ℂ) - π / 2 = π / 2 by ring]; linear_combination -(wI (π / 2)) * hW)
    (by
      rw [show deriv (fun z => wI (π - z)) (π / 2) = -deriv wI (π - π / 2) from
        deriv_comp_const_sub _ _ _]
      rw [show deriv (fun z => (wI (π / 2) * deriv wII (π / 2) + deriv wI (π / 2) * wII (π / 2)) *
          wI z + -(2 * wI (π / 2) * deriv wI (π / 2)) * wII z) (π / 2) =
          (wI (π / 2) * deriv wII (π / 2) + deriv wI (π / 2) * wII (π / 2)) * deriv wI (π / 2) +
          -(2 * wI (π / 2) * deriv wI (π / 2)) * deriv wII (π / 2) from
        m28a_deriv_lincomb (h1.differentiable _) (h2.differentiable _) _ _]
      rw [show (π : ℂ) - π / 2 = π / 2 by ring]
      linear_combination deriv wI (π / 2) * hW)
  have := congrFun key z
  linear_combination this

/-- Half-period reflection identity for `w_II` about `π/2`:
`w_II(π - z) = 2BB' w_I(z) - (AB' + A'B) w_II(z)`. -/
theorem m28a_mathieuWII_pi_sub (z : ℂ) :
    wII (π - z) = 2 * wII (π / 2) * deriv wII (π / 2) * wI z -
      (wI (π / 2) * deriv wII (π / 2) + deriv wI (π / 2) * wII (π / 2)) * wII z := by
  obtain ⟨h1, -, -⟩ := mathieuWI_spec a q
  obtain ⟨h2, -, -⟩ := mathieuWII_spec a q
  have hW := mathieuWI_wronskian a q (π / 2)
  have hr := h2.comp_pi_sub
  have hc := (h1.const_mul (2 * wII (π / 2) * deriv wII (π / 2))).add
    (h2.const_mul (-(wI (π / 2) * deriv wII (π / 2) + deriv wI (π / 2) * wII (π / 2))))
  have key := hr.eq_of_initial hc (z₀ := π / 2) (by
      rw [show (π : ℂ) - π / 2 = π / 2 by ring]; linear_combination -(wII (π / 2)) * hW)
    (by
      rw [show deriv (fun z => wII (π - z)) (π / 2) = -deriv wII (π - π / 2) from
        deriv_comp_const_sub _ _ _]
      rw [show deriv (fun z => 2 * wII (π / 2) * deriv wII (π / 2) * wI z +
          -(wI (π / 2) * deriv wII (π / 2) + deriv wI (π / 2) * wII (π / 2)) * wII z) (π / 2) =
          2 * wII (π / 2) * deriv wII (π / 2) * deriv wI (π / 2) +
          -(wI (π / 2) * deriv wII (π / 2) + deriv wI (π / 2) * wII (π / 2)) *
            deriv wII (π / 2) from
        m28a_deriv_lincomb (h1.differentiable _) (h2.differentiable _) _ _]
      rw [show (π : ℂ) - π / 2 = π / 2 by ring]
      linear_combination deriv wII (π / 2) * hW)
  have := congrFun key z
  linear_combination this

/-- Derivative of the reflection identity for `w_I` at `z = 0`. -/
theorem m28a_deriv_mathieuWI_pi :
    deriv wI π = 2 * wI (π / 2) * deriv wI (π / 2) := by
  obtain ⟨h1, -, h11⟩ := mathieuWI_spec a q
  obtain ⟨h2, -, h21⟩ := mathieuWII_spec a q
  have e := congrArg (fun f => deriv f 0) (funext (m28a_mathieuWI_pi_sub a q))
  rw [deriv_comp_const_sub, m28a_deriv_lincomb_sub (h1.differentiable _) (h2.differentiable _),
    h11, h21] at e
  simp only [sub_zero] at e
  linear_combination -e

/-- Derivative of the reflection identity for `w_II` at `z = 0`. -/
theorem m28a_deriv_mathieuWII_pi :
    deriv wII π = wI (π / 2) * deriv wII (π / 2) + deriv wI (π / 2) * wII (π / 2) := by
  obtain ⟨h1, -, h11⟩ := mathieuWI_spec a q
  obtain ⟨h2, -, h21⟩ := mathieuWII_spec a q
  have e := congrArg (fun f => deriv f 0) (funext (m28a_mathieuWII_pi_sub a q))
  rw [deriv_comp_const_sub, m28a_deriv_lincomb_sub (h1.differentiable _) (h2.differentiable _),
    h11, h21] at e
  simp only [sub_zero] at e
  linear_combination -e

/-- `w_I(π) = AB' + A'B` (from the reflection identity at `z = 0`). -/
theorem m28a_mathieuWI_pi :
    wI π = wI (π / 2) * deriv wII (π / 2) + deriv wI (π / 2) * wII (π / 2) := by
  have := m28a_mathieuWI_pi_sub a q 0
  simp [(mathieuWI_spec a q).2.1, (mathieuWII_spec a q).2.1] at this
  exact this

/-- **DLMF 28.2.9**: `w_I(π; a, q) = w_II'(π; a, q)`. -/
@[dlmf 28.2.E9]
theorem mathieuWI_pi_eq_deriv_mathieuWII_pi : wI π = deriv wII π := by
  rw [m28a_mathieuWI_pi, m28a_deriv_mathieuWII_pi]

/-- **DLMF 28.2.10**: `w_I(π) - 1 = 2 w_I'(π/2) w_II(π/2)`. -/
@[dlmf 28.2.E10]
theorem mathieuWI_pi_sub_one : wI π - 1 = 2 * deriv wI (π / 2) * wII (π / 2) := by
  rw [m28a_mathieuWI_pi]; linear_combination (mathieuWI_wronskian a q (π / 2))

/-- **DLMF 28.2.11**: `w_I(π) + 1 = 2 w_I(π/2) w_II'(π/2)`. -/
@[dlmf 28.2.E11]
theorem mathieuWI_pi_add_one : wI π + 1 = 2 * wI (π / 2) * deriv wII (π / 2) := by
  rw [m28a_mathieuWI_pi]; linear_combination -(mathieuWI_wronskian a q (π / 2))

/-- **DLMF 28.2.12**: `w_I'(π) = 2 w_I(π/2) w_I'(π/2)`. -/
@[dlmf 28.2.E12]
theorem deriv_mathieuWI_pi : deriv wI π = 2 * wI (π / 2) * deriv wI (π / 2) :=
  m28a_deriv_mathieuWI_pi a q

/-- **DLMF 28.2.13**: `w_II(π) = 2 w_II(π/2) w_II'(π/2)`. -/
@[dlmf 28.2.E13]
theorem mathieuWII_pi : wII π = 2 * wII (π / 2) * deriv wII (π / 2) := by
  have := m28a_mathieuWII_pi_sub a q 0
  simpa [(mathieuWI_spec a q).2.1, (mathieuWII_spec a q).2.1] using this

/-- **DLMF 28.2.7** (upper sign): `w_I(z + π) = w_I(π) w_I(z) + w_I'(π) w_II(z)`. -/
@[dlmf 28.2.E7]
theorem mathieuWI_add_pi (z : ℂ) : wI (z + π) = wI π * wI z + deriv wI π * wII z := by
  have h := (isMathieuSolution_mathieuWI a q).comp_add_pi.eq_combination
  have := congrFun h z
  simp only [zero_add] at this
  rw [this, deriv_comp_add_const, zero_add]

/-- **DLMF 28.2.7** (lower sign): `w_I(z - π) = w_I(π) w_I(z) - w_I'(π) w_II(z)`. -/
@[dlmf 28.2.E7]
theorem mathieuWI_sub_pi (z : ℂ) : wI (z - π) = wI π * wI z - deriv wI π * wII z := by
  have h := (isMathieuSolution_mathieuWI a q).comp_sub_pi.eq_combination
  have := congrFun h z
  simp only [zero_sub] at this
  rw [this, deriv_comp_sub_const, zero_sub, mathieuWI_neg, deriv_mathieuWI_neg]; ring

/-- **DLMF 28.2.8** (upper sign): `w_II(z + π) = w_II(π) w_I(z) + w_II'(π) w_II(z)`. -/
@[dlmf 28.2.E8]
theorem mathieuWII_add_pi (z : ℂ) : wII (z + π) = wII π * wI z + deriv wII π * wII z := by
  have h := (isMathieuSolution_mathieuWII a q).comp_add_pi.eq_combination
  have := congrFun h z
  simp only [zero_add] at this
  rw [this, deriv_comp_add_const, zero_add]

/-- **DLMF 28.2.8** (lower sign): `w_II(z - π) = -w_II(π) w_I(z) + w_II'(π) w_II(z)`. -/
@[dlmf 28.2.E8]
theorem mathieuWII_sub_pi (z : ℂ) : wII (z - π) = -wII π * wI z + deriv wII π * wII z := by
  have h := (isMathieuSolution_mathieuWII a q).comp_sub_pi.eq_combination
  have := congrFun h z
  simp only [zero_sub] at this
  rw [this, deriv_comp_sub_const, zero_sub, mathieuWII_neg, deriv_mathieuWII_neg]

/-- **Analytic dependence** (DLMF §28.2(ii)): the solution with given initial values at a point
is an entire function of `z`, `a` and `q`; for the basic solutions, `(z, a, q) ↦ w_I(z; a, q)`
and `(z, a, q) ↦ w_II(z; a, q)` are entire on `ℂ³`. -/
@[dlmf 28.2.ii]
theorem differentiable_mathieuWI_mathieuWII :
    Differentiable ℂ (fun p : ℂ × ℂ × ℂ => mathieuWI p.2.1 p.2.2 p.1) ∧
      Differentiable ℂ (fun p : ℂ × ℂ × ℂ => mathieuWII p.2.1 p.2.2 p.1) := by
  sorry

end Basic

/-! ### Floquet theory (§28.2(iii)–(iv)) -/

/-- **Floquet's theorem** (DLMF 28.2.14–28.2.15): Mathieu's equation has a nontrivial solution
with `w(z + π) = e^{πiν} w(z)` iff `e^{πiν}` is an eigenvalue of the monodromy matrix 28.2.15. -/
@[dlmf 28.2.E14, dlmf 28.2.E15]
theorem exists_isFloquetSolution_iff (a q ν : ℂ) :
    (∃ w, IsFloquetSolution a q ν w) ↔
      ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
        (mathieuMonodromy a q).mulVec v = Complex.exp (π * I * ν) • v := by
  sorry

/-- **Characteristic equation** (DLMF 28.2.16): a Floquet solution with respect to `ν` exists iff
`cos πν = w_I(π; a, q)`. -/
@[dlmf 28.2.E16]
theorem exists_isFloquetSolution_iff_charExp (a q ν : ℂ) :
    (∃ w, IsFloquetSolution a q ν w) ↔ IsMathieuCharExp a q ν := by
  sorry

/-- **DLMF 28.2.16** (second equality): `w_I(π; a, q) = w_I(π; a, -q)`. -/
@[dlmf 28.2.E16]
theorem mathieuWI_pi_neg_q (a q : ℂ) : mathieuWI a q π = mathieuWI a (-q) π := by
  sorry

/-- `cos πν` is an entire function of `a` and `q²` (DLMF §28.2(iii)): there is an entire
function `F` on `ℂ²` with `w_I(π; a, q) = F(a, q²)`. -/
@[dlmf 28.2.iii]
theorem exists_entire_mathieuWI_pi :
    ∃ F : ℂ × ℂ → ℂ, Differentiable ℂ F ∧ ∀ a q, mathieuWI a q π = F (a, q ^ 2) := by
  sorry

/-- **Principal characteristic exponent** (DLMF §28.2(iii)): `ν̂ = π⁻¹ arccos w_I(π; a, q)`
(principal branch, §4.23(ii)) is a characteristic exponent, and the general solution of 28.2.16
is `ν = ±ν̂ + 2n`, `n ∈ ℤ`. -/
@[dlmf 28.2.iii]
theorem isMathieuCharExp_iff (a q ν : ℂ) :
    IsMathieuCharExp a q ν ↔ ∃ n : ℤ,
      ν = DLMF.Elementary.arccosPrincipal (mathieuWI a q π) / π + 2 * n ∨
        ν = -(DLMF.Elementary.arccosPrincipal (mathieuWI a q π) / π) + 2 * n := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have key : IsMathieuCharExp a q ν ↔ Complex.cos (DLMF.Elementary.arccosPrincipal
      (mathieuWI a q π)) = Complex.cos (π * ν) := by
    rw [DLMF.Elementary.cos_arccos_principal, IsMathieuCharExp, eq_comm]
  rw [key, Complex.cos_eq_cos_iff]
  constructor
  · rintro ⟨k, hk | hk⟩
    · refine ⟨k, Or.inl ?_⟩
      field_simp
      linear_combination hk
    · refine ⟨k, Or.inr ?_⟩
      field_simp
      linear_combination hk
  · rintro ⟨k, hk | hk⟩
    · refine ⟨k, Or.inl ?_⟩
      rw [hk]; field_simp; ring
    · refine ⟨k, Or.inr ?_⟩
      rw [hk]; field_simp; ring

/-- The principal exponent satisfies `0 ≤ ℜν̂ ≤ 1` (DLMF §28.2(iii)). -/
@[dlmf 28.2.iii]
theorem re_arccosPrincipal_mathieuWI_div_pi_mem (a q : ℂ) :
    0 ≤ (DLMF.Elementary.arccosPrincipal (mathieuWI a q π) / π).re ∧
      (DLMF.Elementary.arccosPrincipal (mathieuWI a q π) / π).re ≤ 1 := by
  sorry

/-- **Double roots** (DLMF §28.2(iii)): `ν` is a double root of the characteristic equation
(the derivative `-π sin πν` of `cos πν - w_I(π)` also vanishes) iff `ν` is an integer. -/
@[dlmf 28.2.iii]
theorem isMathieuCharExp_double_iff (a q ν : ℂ) (h : IsMathieuCharExp a q ν) :
    Complex.sin (π * ν) = 0 ↔ ∃ n : ℤ, ν = n := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [Complex.sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [mul_comm] at hk; exact mul_right_cancel₀ hπ hk⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩

/-- **Connection formula** (DLMF 28.2.17): every solution satisfies
`w(z + π) + w(z - π) = 2 cos(πν) w(z)` for a characteristic exponent `ν`. -/
@[dlmf 28.2.E17]
theorem IsMathieuSolution.add_pi_add_sub_pi {a q ν : ℂ} {w : ℂ → ℂ}
    (h : IsMathieuSolution a q w) (hν : IsMathieuCharExp a q ν) (z : ℂ) :
    w (z + π) + w (z - π) = 2 * Complex.cos (π * ν) * w z := by
  have e := h.eq_combination
  rw [hν, e]
  simp only
  rw [mathieuWI_add_pi, mathieuWI_sub_pi, mathieuWII_add_pi, mathieuWII_sub_pi,
    ← mathieuWI_pi_eq_deriv_mathieuWII_pi]
  ring

/-- **Floquet dichotomy** (DLMF §28.2(iv)): a nontrivial solution `w` is either a Floquet solution
with respect to `ν`, or `w(z + π) - e^{iνπ} w(z)` is a Floquet solution with respect to `-ν`. -/
@[dlmf 28.2.iv]
theorem IsMathieuSolution.isFloquet_or {a q ν : ℂ} {w : ℂ → ℂ}
    (h : IsMathieuSolution a q w) (hw : w ≠ 0) (hν : IsMathieuCharExp a q ν) :
    IsFloquetSolution a q ν w ∨
      IsFloquetSolution a q (-ν) (fun z => w (z + π) - Complex.exp (I * ν * π) * w z) := by
  by_cases hu : (fun z => w (z + π) - Complex.exp (I * ν * π) * w z) = 0
  · left
    refine ⟨h, hw, fun z => ?_⟩
    have := congrFun hu z
    simp only [Pi.zero_apply] at this
    rw [show (π : ℂ) * I * ν = I * ν * π by ring]
    linear_combination this
  · right
    refine ⟨by simpa [sub_eq_add_neg] using
      h.comp_add_pi.add (h.const_mul (-Complex.exp (I * ν * π))), hu, fun z => ?_⟩
    · have h2 := h.add_pi_add_sub_pi hν (z + π)
      rw [show z + π - π = z by ring, show z + π + π = z + 2 * π by ring] at h2
      have hc : 2 * Complex.cos (π * ν) =
          Complex.exp (I * ν * π) + (Complex.exp (I * ν * π))⁻¹ := by
        rw [Complex.cos, show (π : ℂ) * ν * I = I * ν * π by ring,
          show -((π : ℂ) * ν) * I = -(I * ν * π) by ring, Complex.exp_neg]; ring
      rw [hc] at h2
      rw [show (π : ℂ) * I * -ν = -(I * ν * π) by ring, Complex.exp_neg]
      beta_reduce
      rw [show z + π + π = z + 2 * π by ring]
      have he : (Complex.exp (I * ν * π))⁻¹ * Complex.exp (I * ν * π) = 1 :=
        inv_mul_cancel₀ (Complex.exp_ne_zero _)
      linear_combination h2 + w z * he

/-- **Theorem of Ince** (DLMF §28.2(iv)): for `q ≠ 0` the Floquet solution with respect to a
given `ν` is unique up to a constant factor. -/
@[dlmf 28.2.iv]
theorem IsFloquetSolution.unique {a q ν : ℂ} (hq : q ≠ 0) {w v : ℂ → ℂ}
    (hw : IsFloquetSolution a q ν w) (hv : IsFloquetSolution a q ν v) :
    ∃ c : ℂ, v = fun z => c * w z := by
  sorry

/-- **Fourier series of a Floquet solution** (DLMF 28.2.18–28.2.19): a Floquet solution with
respect to `ν` is `w(z) = ∑_{n ∈ ℤ} c_{2n} e^{i(ν+2n)z}`, absolutely convergent (and locally
uniformly on `ℂ`), and the coefficients satisfy
`q c_{2n+2} - (a - (ν+2n)²) c_{2n} + q c_{2n-2} = 0`. (`c n` stands for DLMF's `c_{2n}`.) -/
@[dlmf 28.2.E18, dlmf 28.2.E19]
theorem IsFloquetSolution.exists_fourier {a q ν : ℂ} {w : ℂ → ℂ}
    (hw : IsFloquetSolution a q ν w) :
    ∃ c : ℤ → ℂ, (∀ z, Summable (fun n => ‖c n * Complex.exp (I * (ν + 2 * n) * z)‖)) ∧
      (∀ z, HasSum (fun n => c n * Complex.exp (I * (ν + 2 * n) * z)) (w z)) ∧
      ∀ n : ℤ, q * c (n + 1) - (a - (ν + 2 * n) ^ 2) * c n + q * c (n - 1) = 0 := by
  sorry

/-- **Converse** (DLMF 28.2.20): a nontrivial solution `c_{2n}` of the recurrence 28.2.19 with
`|c_{2n}|^{1/|n|} → 0` as `n → ±∞` yields a Floquet solution `∑ c_{2n} e^{i(ν+2n)z}`. -/
@[dlmf 28.2.E20]
theorem isFloquetSolution_of_recurrence {a q ν : ℂ} {c : ℤ → ℂ} (hc : c ≠ 0)
    (hrec : ∀ n : ℤ, q * c (n + 1) - (a - (ν + 2 * n) ^ 2) * c n + q * c (n - 1) = 0)
    (hlim : Tendsto (fun n : ℤ => ‖c n‖ ^ (1 / (|n| : ℝ))) (Filter.cofinite) (𝓝 0)) :
    IsFloquetSolution a q ν (fun z => ∑' n : ℤ, c n * Complex.exp (I * (ν + 2 * n) * z)) := by
  sorry

/-! ### Eigenvalues (§28.2(v)) -/

/-- **Discrete set of eigenvalues** (DLMF §28.2(v)): for given `ν` and `q`, the set of `a`
satisfying the characteristic equation 28.2.16 is infinite and has no finite accumulation
point. -/
@[dlmf 28.2.v]
theorem charExp_set_infinite_discrete (q ν : ℂ) :
    {a : ℂ | IsMathieuCharExp a q ν}.Infinite ∧
      ∀ K : Set ℂ, IsCompact K → (K ∩ {a : ℂ | IsMathieuCharExp a q ν}).Finite := by
  sorry

/-- **DLMF 28.2.21** (even `n`): `w_I'(π/2; a_{2n}(q), q) = 0`. -/
@[dlmf 28.2.E21]
theorem deriv_mathieuWI_half_pi_mathieuA_even (n : ℕ) (q : ℝ) :
    deriv (mathieuWI (mathieuA (2 * n) q) q) (π / 2) = 0 := by
  have := (mathieuA_spec (2 * n) q).1
  simpa [mathieuSpecA] using this

/-- **DLMF 28.2.21** (odd `n`): `w_I(π/2; a_{2n+1}(q), q) = 0`. -/
@[dlmf 28.2.E21]
theorem mathieuWI_half_pi_mathieuA_odd (n : ℕ) (q : ℝ) :
    mathieuWI (mathieuA (2 * n + 1) q) q (π / 2) = 0 := by
  have := (mathieuA_spec (2 * n + 1) q).1
  simpa [mathieuSpecA, Nat.not_even_bit1] using this

/-- **DLMF 28.2.22** (odd `n`): `w_II'(π/2; b_{2n+1}(q), q) = 0`. -/
@[dlmf 28.2.E22]
theorem deriv_mathieuWII_half_pi_mathieuB_odd (n : ℕ) (q : ℝ) :
    deriv (mathieuWII (mathieuB (2 * n + 1) q) q) (π / 2) = 0 := by
  have := (mathieuB_spec (n := 2 * n + 1) (by omega) q).1
  simpa [mathieuSpecB, Nat.not_even_bit1] using this

/-- **DLMF 28.2.22** (even `n`): `w_II(π/2; b_{2n+2}(q), q) = 0`. -/
@[dlmf 28.2.E22]
theorem mathieuWII_half_pi_mathieuB_even (n : ℕ) (q : ℝ) :
    mathieuWII (mathieuB (2 * n + 2) q) q (π / 2) = 0 := by
  have := (mathieuB_spec (n := 2 * n + 2) (by omega) q).1
  have he : Even (2 * n + 2) := ⟨n + 1, by ring⟩
  simpa [mathieuSpecB, he] using this

/-- **Table 28.2.1** (`ν̂ = 0`, `w'(0) = w'(π/2) = 0`): for real `q` the even `π`-periodic
solutions occur exactly for `a = a_{2n}(q)`: a nontrivial solution with `w'(0) = w'(π/2) = 0`
exists iff `a = a_{2n}(q)` for some `n`. -/
@[dlmf 28.2.T1]
theorem exists_solution_neumann_iff (a q : ℝ) :
    (∃ w, IsMathieuSolution a q w ∧ w ≠ 0 ∧ deriv w 0 = 0 ∧ deriv w (π / 2) = 0) ↔
      ∃ n : ℕ, a = mathieuA (2 * n) q := by
  sorry

/-- **Table 28.2.1** (`ν̂ = 1`, `w'(0) = w(π/2) = 0`): exactly for `a = a_{2n+1}(q)`. -/
@[dlmf 28.2.T1]
theorem exists_solution_neumann_dirichlet_iff (a q : ℝ) :
    (∃ w, IsMathieuSolution a q w ∧ w ≠ 0 ∧ deriv w 0 = 0 ∧ w (π / 2) = 0) ↔
      ∃ n : ℕ, a = mathieuA (2 * n + 1) q := by
  sorry

/-- **Table 28.2.1** (`ν̂ = 1`, `w(0) = w'(π/2) = 0`): exactly for `a = b_{2n+1}(q)`. -/
@[dlmf 28.2.T1]
theorem exists_solution_dirichlet_neumann_iff (a q : ℝ) :
    (∃ w, IsMathieuSolution a q w ∧ w ≠ 0 ∧ w 0 = 0 ∧ deriv w (π / 2) = 0) ↔
      ∃ n : ℕ, a = mathieuB (2 * n + 1) q := by
  sorry

/-- **Table 28.2.1** (`ν̂ = 0`, `w(0) = w(π/2) = 0`): exactly for `a = b_{2n+2}(q)`. -/
@[dlmf 28.2.T1]
theorem exists_solution_dirichlet_iff (a q : ℝ) :
    (∃ w, IsMathieuSolution a q w ∧ w ≠ 0 ∧ w 0 = 0 ∧ w (π / 2) = 0) ↔
      ∃ n : ℕ, a = mathieuB (2 * n + 2) q := by
  sorry

/-- **Monotone ordering** within each spectrum (DLMF §28.2(v)): `a_{2n} < a_{2n+2}`,
`a_{2n+1} < a_{2n+3}`, `b_{2n+1} < b_{2n+3}`, `b_{2n+2} < b_{2n+4}` (real `q`). -/
@[dlmf 28.2.v]
theorem mathieuA_lt_mathieuA_add_two (n : ℕ) (q : ℝ) : mathieuA n q < mathieuA (n + 2) q := by
  sorry

/-- Monotone ordering within each spectrum of the `b_n` (DLMF §28.2(v)), `n ≥ 1`. -/
@[dlmf 28.2.v]
theorem mathieuB_lt_mathieuB_add_two {n : ℕ} (hn : n ≠ 0) (q : ℝ) :
    mathieuB n q < mathieuB (n + 2) q := by
  sorry

/-- **DLMF 28.2.23**: `a_n(0) = n²`, `n = 0, 1, 2, …`. -/
@[dlmf 28.2.E23]
theorem mathieuA_zero (n : ℕ) : mathieuA n 0 = (n : ℝ) ^ 2 := by
  sorry

/-- **DLMF 28.2.24**: `b_n(0) = n²`, `n = 1, 2, 3, …`. -/
@[dlmf 28.2.E24]
theorem mathieuB_zero {n : ℕ} (hn : n ≠ 0) : mathieuB n 0 = (n : ℝ) ^ 2 := by
  sorry

/-- **Distribution of the eigenvalues** (DLMF 28.2.25), `q > 0`:
`a_0 < b_1 < a_1 < b_2 < a_2 < b_3 < ⋯`. -/
@[dlmf 28.2.E25]
theorem mathieu_eigenvalues_interlace_pos {q : ℝ} (hq : 0 < q) (n : ℕ) :
    mathieuA n q < mathieuB (n + 1) q ∧ mathieuB (n + 1) q < mathieuA (n + 1) q := by
  sorry

/-- **Distribution of the eigenvalues** (DLMF 28.2.25), `q < 0`:
`a_0 < a_1 < b_1 < b_2 < a_2 < a_3 < b_3 < b_4 < ⋯`. -/
@[dlmf 28.2.E25]
theorem mathieu_eigenvalues_interlace_neg {q : ℝ} (hq : q < 0) (n : ℕ) :
    mathieuA (2 * n) q < mathieuA (2 * n + 1) q ∧
      mathieuA (2 * n + 1) q < mathieuB (2 * n + 1) q ∧
      mathieuB (2 * n + 1) q < mathieuB (2 * n + 2) q ∧
      mathieuB (2 * n + 2) q < mathieuA (2 * n + 2) q := by
  sorry

/-- **DLMF 28.2.26**: `a_{2n}(-q) = a_{2n}(q)`. -/
@[dlmf 28.2.E26]
theorem mathieuA_even_neg (n : ℕ) (q : ℝ) : mathieuA (2 * n) (-q) = mathieuA (2 * n) q := by
  sorry

/-- **DLMF 28.2.27**: `a_{2n+1}(-q) = b_{2n+1}(q)`. -/
@[dlmf 28.2.E27]
theorem mathieuA_odd_neg (n : ℕ) (q : ℝ) :
    mathieuA (2 * n + 1) (-q) = mathieuB (2 * n + 1) q := by
  sorry

/-- **DLMF 28.2.28**: `b_{2n+2}(-q) = b_{2n+2}(q)`. -/
@[dlmf 28.2.E28]
theorem mathieuB_even_neg (n : ℕ) (q : ℝ) :
    mathieuB (2 * n + 2) (-q) = mathieuB (2 * n + 2) q := by
  sorry

/-! ### Eigenfunctions (§28.2(vi)) -/

/-- `∫₀^{2π} |f|² > 0` for a continuous `f` that is nonzero just to the right of `0`. -/
theorem m28a_integral_normSq_pos {f : ℂ → ℂ} (hf : Continuous f)
    (h0 : ∀ᶠ x : ℝ in 𝓝[>] 0, f x ≠ 0) : 0 < ∫ x in (0 : ℝ)..2 * π, ‖f x‖ ^ 2 := by
  have hc : Continuous fun x : ℝ => ‖f x‖ ^ 2 := (hf.comp Complex.continuous_ofReal).norm.pow 2
  obtain ⟨u, hu, hsub0⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h0
  have h2π : (0 : ℝ) < 2 * π := by positivity
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae'
    (Eventually.of_forall fun x => by positivity) (hc.intervalIntegrable _ _)]
  refine ⟨h2π, ?_⟩
  have hsub : Ioo 0 (min u (2 * π)) ⊆
      Function.support (fun x : ℝ => ‖f x‖ ^ 2) ∩ Ioc 0 (2 * π) := by
    intro x hx
    refine ⟨?_, hx.1, le_of_lt (lt_of_lt_of_le hx.2 (min_le_right _ _))⟩
    have : f x ≠ 0 := hsub0 ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
    simpa [Function.mem_support] using this
  refine lt_of_lt_of_le ?_ (MeasureTheory.measure_mono hsub)
  have hu' : (0 : ℝ) < u := hu
  rw [Real.volume_Ioo]; simp [hu', Real.pi_pos]

/-- `ce_n(0, q) > 0` (the sign convention of `mathieuCe`, DLMF §28.2(vi)). -/
theorem mathieuCeZero_pos (n : ℕ) (q : ℝ) : 0 < mathieuCeZero n q := by
  obtain ⟨h, h0, -⟩ := mathieuWI_spec (mathieuA n q) q
  have hev : ∀ᶠ x : ℝ in 𝓝 0, mathieuWI (mathieuA n q) q x ≠ 0 :=
    (h.differentiable.continuous.comp Complex.continuous_ofReal).continuousAt.eventually_ne
      (by simp [h0])
  exact Real.sqrt_pos.mpr (div_pos Real.pi_pos
    (m28a_integral_normSq_pos h.differentiable.continuous (nhdsWithin_le_nhds hev)))

/-- `se_n'(0, q) > 0` (the sign convention of `mathieuSe`, DLMF §28.2(vi)). -/
theorem mathieuSeDerivZero_pos (n : ℕ) (q : ℝ) : 0 < mathieuSeDerivZero n q := by
  obtain ⟨h, h0, h1⟩ := mathieuWII_spec (mathieuB n q) q
  have hd : HasDerivAt (fun x : ℝ => mathieuWII (mathieuB n q) q x) 1 0 := by
    have := (h.differentiable _).hasDerivAt.comp_ofReal (z := 0)
    simpa [h1] using this
  have hev := hd.eventually_ne (c := 0) one_ne_zero
  have hev' : ∀ᶠ x : ℝ in 𝓝[>] 0, mathieuWII (mathieuB n q) q x ≠ 0 := by
    exact nhdsWithin_mono (0 : ℝ) (fun x (hx : x ∈ Ioi (0 : ℝ)) => ne_of_gt hx) hev
  exact Real.sqrt_pos.mpr (div_pos Real.pi_pos
    (m28a_integral_normSq_pos h.differentiable.continuous hev'))

/-- **DLMF 28.2.38**: `ce_n(z, q) / ce_n(0, q) = w_I(z; a_n(q), q)`. -/
@[dlmf 28.2.E38]
theorem mathieuCe_div_mathieuCe_zero (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuCe n z q / mathieuCe n 0 q = mathieuWI (mathieuA n q) q z := by
  rw [mathieuCe_zero, mathieuCe]
  have : (mathieuCeZero n q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mathieuCeZero_pos n q).ne'
  field_simp

/-- **DLMF 28.2.39**: `se_n(z, q) / se_n'(0, q) = w_II(z; b_n(q), q)`. -/
@[dlmf 28.2.E39]
theorem mathieuSe_div_deriv_mathieuSe_zero (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuSe n z q / deriv (fun z => mathieuSe n z q) 0 = mathieuWII (mathieuB n q) q z := by
  rw [deriv_mathieuSe_zero, mathieuSe]
  have : (mathieuSeDerivZero n q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mathieuSeDerivZero_pos n q).ne'
  field_simp

/-! ### Periodicity and parity of the eigenfunctions (Table 28.2.2) -/

section Periodicity

variable {a q : ℂ}

/-- If `w_I'(π/2) = 0` then `w_I` has period `π`. -/
theorem m28a_mathieuWI_periodic (h : deriv (mathieuWI a q) (π / 2) = 0) (z : ℂ) :
    mathieuWI a q (z + π) = mathieuWI a q z := by
  have hW := mathieuWI_wronskian a q (π / 2)
  have e := m28a_mathieuWI_pi_sub a q (-z)
  rw [h] at e hW
  rw [show z + π = π - -z by ring, e, mathieuWI_neg]
  linear_combination mathieuWI a q z * hW

/-- If `w_I(π/2) = 0` then `w_I` has antiperiod `π`. -/
theorem m28a_mathieuWI_antiperiodic (h : mathieuWI a q (π / 2) = 0) (z : ℂ) :
    mathieuWI a q (z + π) = -mathieuWI a q z := by
  have hW := mathieuWI_wronskian a q (π / 2)
  have e := m28a_mathieuWI_pi_sub a q (-z)
  rw [h] at e hW
  rw [show z + π = π - -z by ring, e, mathieuWI_neg]
  linear_combination -(mathieuWI a q z) * hW

/-- If `w_II'(π/2) = 0` then `w_II` has antiperiod `π`. -/
theorem m28a_mathieuWII_antiperiodic (h : deriv (mathieuWII a q) (π / 2) = 0) (z : ℂ) :
    mathieuWII a q (z + π) = -mathieuWII a q z := by
  have hW := mathieuWI_wronskian a q (π / 2)
  have e := m28a_mathieuWII_pi_sub a q (-z)
  rw [h] at e hW
  rw [show z + π = π - -z by ring, e, mathieuWII_neg]
  linear_combination -(mathieuWII a q z) * hW

/-- If `w_II(π/2) = 0` then `w_II` has period `π`. -/
theorem m28a_mathieuWII_periodic (h : mathieuWII a q (π / 2) = 0) (z : ℂ) :
    mathieuWII a q (z + π) = mathieuWII a q z := by
  have hW := mathieuWI_wronskian a q (π / 2)
  have e := m28a_mathieuWII_pi_sub a q (-z)
  rw [h] at e hW
  rw [show z + π = π - -z by ring, e, mathieuWII_neg]
  linear_combination mathieuWII a q z * hW

end Periodicity

/-- **Table 28.2.2**: `ce_n(z, q)` is even. -/
@[dlmf 28.2.T2]
theorem mathieuCe_neg (n : ℕ) (z : ℂ) (q : ℝ) : mathieuCe n (-z) q = mathieuCe n z q := by
  simp [mathieuCe, mathieuWI_neg]

/-- **Table 28.2.2**: `se_n(z, q)` is odd. -/
@[dlmf 28.2.T2]
theorem mathieuSe_neg (n : ℕ) (z : ℂ) (q : ℝ) : mathieuSe n (-z) q = -mathieuSe n z q := by
  simp [mathieuSe, mathieuWII_neg]

/-- **Table 28.2.2**: `ce_{2n}(z, q)` has period `π`. -/
@[dlmf 28.2.T2]
theorem mathieuCe_even_add_pi (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuCe (2 * n) (z + π) q = mathieuCe (2 * n) z q := by
  simp only [mathieuCe]
  rw [m28a_mathieuWI_periodic (deriv_mathieuWI_half_pi_mathieuA_even n q)]

/-- **Table 28.2.2**: `ce_{2n+1}(z, q)` has antiperiod `π`. -/
@[dlmf 28.2.T2]
theorem mathieuCe_odd_add_pi (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuCe (2 * n + 1) (z + π) q = -mathieuCe (2 * n + 1) z q := by
  simp only [mathieuCe]
  rw [m28a_mathieuWI_antiperiodic (mathieuWI_half_pi_mathieuA_odd n q)]; ring

/-- **Table 28.2.2**: `se_{2n+1}(z, q)` has antiperiod `π`. -/
@[dlmf 28.2.T2]
theorem mathieuSe_odd_add_pi (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuSe (2 * n + 1) (z + π) q = -mathieuSe (2 * n + 1) z q := by
  simp only [mathieuSe]
  rw [m28a_mathieuWII_antiperiodic (deriv_mathieuWII_half_pi_mathieuB_odd n q)]; ring

/-- **Table 28.2.2**: `se_{2n+2}(z, q)` has period `π`. -/
@[dlmf 28.2.T2]
theorem mathieuSe_even_add_pi (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuSe (2 * n + 2) (z + π) q = mathieuSe (2 * n + 2) z q := by
  simp only [mathieuSe]
  rw [m28a_mathieuWII_periodic (mathieuWII_half_pi_mathieuB_even n q)]

/-- **DLMF 28.2.29**: `ce_0(z, 0) = 1/√2`. -/
@[dlmf 28.2.E29]
theorem mathieuCe_zero_zero (z : ℂ) : mathieuCe 0 z 0 = 1 / Real.sqrt 2 := by
  sorry

/-- **DLMF 28.2.29**: `ce_n(z, 0) = cos nz`, `n = 1, 2, 3, …`. -/
@[dlmf 28.2.E29]
theorem mathieuCe_q_zero {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    mathieuCe n z 0 = Complex.cos (n * z) := by
  sorry

/-- **DLMF 28.2.29**: `se_n(z, 0) = sin nz`, `n = 1, 2, 3, …`. -/
@[dlmf 28.2.E29]
theorem mathieuSe_q_zero {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    mathieuSe n z 0 = Complex.sin (n * z) := by
  sorry

/-- **Normalization** (DLMF 28.2.30): `∫₀^{2π} ce_n(x, q)² dx = π` (real `q`). -/
@[dlmf 28.2.E30]
theorem integral_mathieuCe_sq (n : ℕ) (q : ℝ) :
    ∫ x in (0 : ℝ)..2 * π, mathieuCe n x q ^ 2 = π := by
  sorry

/-- **Normalization** (DLMF 28.2.30): `∫₀^{2π} se_n(x, q)² dx = π`, `n ≥ 1` (real `q`). -/
@[dlmf 28.2.E30]
theorem integral_mathieuSe_sq {n : ℕ} (hn : n ≠ 0) (q : ℝ) :
    ∫ x in (0 : ℝ)..2 * π, mathieuSe n x q ^ 2 = π := by
  sorry

/-- **Orthogonality** (DLMF 28.2.31): `∫₀^{2π} ce_m ce_n = 0` for `m ≠ n` (real `q`). -/
@[dlmf 28.2.E31]
theorem integral_mathieuCe_mul_mathieuCe {m n : ℕ} (hmn : m ≠ n) (q : ℝ) :
    ∫ x in (0 : ℝ)..2 * π, mathieuCe m x q * mathieuCe n x q = 0 := by
  sorry

/-- **Orthogonality** (DLMF 28.2.32): `∫₀^{2π} se_m se_n = 0` for `m ≠ n`, `m, n ≥ 1`. -/
@[dlmf 28.2.E32]
theorem integral_mathieuSe_mul_mathieuSe {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ≠ n)
    (q : ℝ) : ∫ x in (0 : ℝ)..2 * π, mathieuSe m x q * mathieuSe n x q = 0 := by
  sorry

/-- **Orthogonality** (DLMF 28.2.33): `∫₀^{2π} ce_m se_n = 0`. -/
@[dlmf 28.2.E33]
theorem integral_mathieuCe_mul_mathieuSe (m n : ℕ) (q : ℝ) :
    ∫ x in (0 : ℝ)..2 * π, mathieuCe m x q * mathieuSe n x q = 0 := by
  sorry

/-- **Change of sign of `q`** (DLMF 28.2.34): `ce_{2n}(z, -q) = (-1)ⁿ ce_{2n}(π/2 - z, q)`. -/
@[dlmf 28.2.E34]
theorem mathieuCe_even_neg_q (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuCe (2 * n) z (-q) = (-1) ^ n * mathieuCe (2 * n) (π / 2 - z) q := by
  sorry

/-- **Change of sign of `q`** (DLMF 28.2.35):
`ce_{2n+1}(z, -q) = (-1)ⁿ se_{2n+1}(π/2 - z, q)`. -/
@[dlmf 28.2.E35]
theorem mathieuCe_odd_neg_q (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuCe (2 * n + 1) z (-q) = (-1) ^ n * mathieuSe (2 * n + 1) (π / 2 - z) q := by
  sorry

/-- **Change of sign of `q`** (DLMF 28.2.36):
`se_{2n+1}(z, -q) = (-1)ⁿ ce_{2n+1}(π/2 - z, q)`. -/
@[dlmf 28.2.E36]
theorem mathieuSe_odd_neg_q (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuSe (2 * n + 1) z (-q) = (-1) ^ n * mathieuCe (2 * n + 1) (π / 2 - z) q := by
  sorry

/-- **Change of sign of `q`** (DLMF 28.2.37):
`se_{2n+2}(z, -q) = (-1)ⁿ se_{2n+2}(π/2 - z, q)`. -/
@[dlmf 28.2.E37]
theorem mathieuSe_even_neg_q (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuSe (2 * n + 2) z (-q) = (-1) ^ n * mathieuSe (2 * n + 2) (π / 2 - z) q := by
  sorry

end DLMF.Mathieu
