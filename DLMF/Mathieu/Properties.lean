/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Basic
public import DLMF.Elementary.Trigonometric
public import DLMFMathlib.Analysis.ODE.Singularities
public import DLMFMathlib.Analysis.ODE.P1oParamHolomorphic
public import SeveralComplexVariables.SeparateAnalytic
public import DLMFMathlib.Analysis.Fourier.P1a2EntirePeriodic

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
and 28.2.38–28.2.39, Floquet's theorem 28.2.14–28.2.16, the half-period relations between
`q` and `-q` (28.2.16, 28.2.26–28.2.28), the ordering within each spectrum, the values at
`q = 0` (28.2.23, 28.2.24, 28.2.29), the normalization and orthogonality 28.2.30–28.2.32, and
(from the admitted analytic dependence on `a`) the characterizations of Table 28.2.1.
Also proved (2026-10-26, round 2): the singularities of the algebraic form (§28.2(i)), the joint
analyticity of `w_I`, `w_II` in `(z, a, q)` (§28.2(ii), by holomorphic parameter dependence and
Hartogs's theorem from lean-codes), `cos πν` as an entire function of `(a, q²)` (§28.2(iii)), the
Fourier series of Floquet solutions and its converse (28.2.18–28.2.20), and Ince's theorem
(§28.2(iv)) by the Casoratian of the Fourier coefficient recurrences (no coexistence for
`q ≠ 0`). Interlacing (Sturm–Liouville theory), the signs in 28.2.34–28.2.37 and the infinitude
of the characteristic set (§28.2(v)) remain admitted.
28.2.33 carries the hypothesis `n ≠ 0` (added 2026-10-26): for the junk value `n = 0` it
fails (`p1a1_integral_mathieuCe_mul_mathieuSe_zero_ne`).

The principal characteristic exponent `ν̂ = π⁻¹ arccos w_I(π; a, q)` uses the project's
principal arccosine `DLMF.Elementary.arccosPrincipal` (DLMF 4.23.16); no new definition is
made.
-/

@[expose] public noncomputable section

open Complex Set Filter ComplexConjugate
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

/-- A function with `(z - z₀) f(z) → L ≠ 0` has no analytic extension at `z₀`. -/
theorem p2f_not_eventuallyEq_analytic {f : ℂ → ℂ} {z₀ L : ℂ} (hL : L ≠ 0)
    (h : Tendsto (fun z => (z - z₀) * f z) (𝓝[≠] z₀) (𝓝 L)) :
    ¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ f =ᶠ[𝓝[≠] z₀] g := by
  rintro ⟨g, hg, hfg⟩
  have h2 : Tendsto (fun z => (z - z₀) * g z) (𝓝[≠] z₀) (𝓝 0) := by
    have : ContinuousAt (fun z => (z - z₀) * g z) z₀ :=
      (continuousAt_id.sub continuousAt_const).mul hg.continuousAt
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have h3 : Tendsto (fun z => (z - z₀) * f z) (𝓝[≠] z₀) (𝓝 0) :=
    h2.congr' (hfg.mono fun z hz => by simp [hz])
  exact hL (tendsto_nhds_unique h h3)

/-- Punctured limit from agreement with a continuous function. -/
theorem p2f_tendsto_of_eq {f g : ℂ → ℂ} {z₀ : ℂ} (hg : ContinuousAt g z₀)
    (h : ∀ z, z ≠ z₀ → f z = g z) : Tendsto f (𝓝[≠] z₀) (𝓝 (g z₀)) :=
  (hg.tendsto.mono_left nhdsWithin_le_nhds).congr'
    (eventually_nhdsWithin_of_forall fun z hz => (h z hz).symm)

/-- Two raw coefficients of a second-order equation after `z = 1/u`. -/
theorem p2f_recipRaw_zero_two (c₀ c₁ : ℂ → ℂ) {u : ℂ} (hu : u ≠ 0) :
    Complex.linearODEReciprocalRaw ![c₀, c₁] 0 u = c₀ u⁻¹ ∧
    Complex.linearODEReciprocalRaw ![c₀, c₁] 2 u = u ^ 4 := by
  have hz : u⁻¹ ≠ 0 := inv_ne_zero hu
  have e2 : deriv (fun z : ℂ => (z⁻¹ - u) ^ 2 / 2) =ᶠ[𝓝 u⁻¹]
      fun z => -((z⁻¹ - u) * (z ^ 2)⁻¹) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with z hz'
    have h := (((hasDerivAt_inv hz').sub_const u).pow 2).div_const 2
    refine h.deriv.trans ?_
    norm_num
    ring
  have d2 : HasDerivAt (fun z : ℂ => -((z⁻¹ - u) * (z ^ 2)⁻¹)) (u ^ 4) u⁻¹ := by
    have h := (((hasDerivAt_inv hz).sub_const u).mul
      ((hasDerivAt_pow 2 u⁻¹).inv (pow_ne_zero 2 hz))).neg
    convert h using 1
    simp only [Pi.inv_apply, inv_pow, Nat.cast_ofNat, inv_inv]
    field_simp
    ring
  simp only [Complex.linearODEReciprocalRaw, Complex.linearODEValue, Fin.sum_univ_two]
  refine ⟨?_, ?_⟩
  · simp [iteratedDeriv_succ]
  · simp only [Nat.factorial_two, Nat.cast_ofNat, iteratedDeriv_succ, iteratedDeriv_zero,
      Fin.val_zero, Fin.val_one, e2.deriv_eq, d2.deriv, e2.eq_of_nhds]
    simp [inv_inv]

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
  intro c
  have hc0 : ∀ ζ, c 0 ζ = (a - 2 * q * (1 - 2 * ζ)) / (4 * ζ * (1 - ζ)) := fun _ => rfl
  have hc1 : ∀ ζ, c 1 ζ = (1 - 2 * ζ) / (2 * ζ * (1 - ζ)) := fun _ => rfl
  -- limits at 0
  have L1 : Tendsto (fun ζ => ζ * c 1 ζ) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    have := p2f_tendsto_of_eq (f := fun ζ => ζ * c 1 ζ)
      (g := fun ζ => (1 - 2 * ζ) / (2 * (1 - ζ))) (z₀ := 0) (by fun_prop (disch := norm_num))
      (fun ζ hζ => by
        rcases eq_or_ne ζ 1 with rfl | h1
        · simp [hc1]
        have : 1 - ζ ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
        rw [hc1]; field_simp)
    simpa using this
  have L2 : Tendsto (fun ζ => ζ ^ 2 * c 0 ζ) (𝓝[≠] 0) (𝓝 0) := by
    have := p2f_tendsto_of_eq (f := fun ζ => ζ ^ 2 * c 0 ζ)
      (g := fun ζ => ζ * (a - 2 * q * (1 - 2 * ζ)) / (4 * (1 - ζ))) (z₀ := 0)
      (by fun_prop (disch := norm_num))
      (fun ζ hζ => by
        rcases eq_or_ne ζ 1 with rfl | h1
        · simp [hc0]
        have : 1 - ζ ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
        rw [hc0]; field_simp)
    simpa using this
  have L3 : Tendsto (fun ζ => (ζ - 1) * c 1 ζ) (𝓝[≠] 1) (𝓝 (1 / 2)) := by
    have := p2f_tendsto_of_eq (f := fun ζ => (ζ - 1) * c 1 ζ)
      (g := fun ζ => -(1 - 2 * ζ) / (2 * ζ)) (z₀ := 1) (by fun_prop (disch := norm_num))
      (fun ζ hζ => by
        rcases eq_or_ne ζ 0 with rfl | h0
        · simp [hc1]
        have : 1 - ζ ≠ 0 := sub_ne_zero.2 (Ne.symm hζ)
        rw [hc1]; field_simp; ring)
    convert this using 2; norm_num
  have L4 : Tendsto (fun ζ => (ζ - 1) ^ 2 * c 0 ζ) (𝓝[≠] 1) (𝓝 0) := by
    have := p2f_tendsto_of_eq (f := fun ζ => (ζ - 1) ^ 2 * c 0 ζ)
      (g := fun ζ => -(ζ - 1) * (a - 2 * q * (1 - 2 * ζ)) / (4 * ζ)) (z₀ := 1)
      (by fun_prop (disch := norm_num))
      (fun ζ hζ => by
        rcases eq_or_ne ζ 0 with rfl | h0
        · simp [hc0]
        have : 1 - ζ ≠ 0 := sub_ne_zero.2 (Ne.symm hζ)
        rw [hc0]; field_simp; ring)
    simpa using this
  refine ⟨⟨fun h => ?_, ?_⟩, ⟨fun h => ?_, ?_⟩, L1, L2, L3, L4, fun hq => ?_⟩
  · exact p2f_not_eventuallyEq_analytic (L := 1 / 2) (by norm_num) (by simpa using L1) (h 1)
  · intro j
    fin_cases j
    · refine ⟨fun ζ => ζ * (a - 2 * q * (1 - 2 * ζ)) / (4 * (1 - ζ)),
        by fun_prop (disch := norm_num), eventually_nhdsWithin_of_forall fun ζ hζ => ?_⟩
      simp only [Fin.zero_eta, Fin.isValue, Nat.sub_zero, sub_zero]
      rcases eq_or_ne ζ 1 with rfl | h1
      · simp [hc0]
      have : 1 - ζ ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
      have hζ : ζ ≠ 0 := hζ
      rw [hc0]; field_simp
    · refine ⟨fun ζ => (1 - 2 * ζ) / (2 * (1 - ζ)),
        by fun_prop (disch := norm_num), eventually_nhdsWithin_of_forall fun ζ hζ => ?_⟩
      simp only [Fin.mk_one, Fin.isValue, sub_zero, Nat.reduceSub, pow_one]
      rcases eq_or_ne ζ 1 with rfl | h1
      · simp [hc1]
      have : 1 - ζ ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
      have hζ : ζ ≠ 0 := hζ
      rw [hc1]; field_simp
  · exact p2f_not_eventuallyEq_analytic (L := 1 / 2) (by norm_num) L3 (h 1)
  · intro j
    fin_cases j
    · refine ⟨fun ζ => -(ζ - 1) * (a - 2 * q * (1 - 2 * ζ)) / (4 * ζ),
        by fun_prop (disch := norm_num), eventually_nhdsWithin_of_forall fun ζ hζ => ?_⟩
      simp only [Fin.zero_eta, Fin.isValue, Nat.sub_zero]
      rcases eq_or_ne ζ 0 with rfl | h0
      · simp [hc0]
      have : 1 - ζ ≠ 0 := sub_ne_zero.2 (Ne.symm hζ)
      rw [hc0]; field_simp; ring
    · refine ⟨fun ζ => -(1 - 2 * ζ) / (2 * ζ),
        by fun_prop (disch := norm_num), eventually_nhdsWithin_of_forall fun ζ hζ => ?_⟩
      simp only [Fin.mk_one, Fin.isValue, Nat.reduceSub, pow_one]
      rcases eq_or_ne ζ 0 with rfl | h0
      · simp [hc1]
      have : 1 - ζ ≠ 0 := sub_ne_zero.2 (Ne.symm hζ)
      rw [hc1]; field_simp; ring
  · -- at infinity: the weighted coefficient `u² R₀(u)` has a pole at `0`
    have key : ¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
        (fun u => (u - 0) ^ (2 - (0 : Fin 2).val) * Complex.linearODEReciprocalCoeff c 0 u)
          =ᶠ[𝓝[≠] 0] g := by
      refine p2f_not_eventuallyEq_analytic (L := -q) (neg_ne_zero.2 hq) ?_
      have := p2f_tendsto_of_eq (f := fun u => (u - 0) *
          ((u - 0) ^ (2 - (0 : Fin 2).val) * Complex.linearODEReciprocalCoeff c 0 u))
        (g := fun u => (a * u - 2 * q * u + 4 * q) / (4 * (u - 1))) (z₀ := 0)
        (by fun_prop (disch := norm_num)) (fun u hu => ?_)
      · convert this using 2; field_simp; ring
      · obtain ⟨r0, r2⟩ := p2f_recipRaw_zero_two (c 0) (c 1) hu
        have hcc : c = ![c 0, c 1] := by ext i; fin_cases i <;> rfl
        simp only [Complex.linearODEReciprocalCoeff, Fin.val_zero]
        rw [hcc, r0, r2, hc0]
        rcases eq_or_ne u 1 with rfl | h1
        · simp
        have : u - 1 ≠ 0 := sub_ne_zero.2 h1
        have : 1 - u⁻¹ ≠ 0 := by
          rw [show 1 - u⁻¹ = (u - 1) / u by field_simp]; exact div_ne_zero this hu
        simp only [Nat.sub_zero, sub_zero]
        field_simp
        ring
    refine ⟨fun h => key ?_, fun h => key (h 0)⟩
    obtain ⟨g, hg, hfg⟩ := h 0
    exact ⟨fun u => (u - 0) ^ (2 - (0 : Fin 2).val) * g u, by fun_prop,
      hfg.mono fun u hu => by simp only at hu ⊢; rw [hu]⟩

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

/-- Restriction of a Mathieu solution to the ray `t ↦ t z`: derivatives in `t`. -/
theorem p2f_ray_hasDerivAt {a q : ℂ} {w : ℂ → ℂ} (hw : IsMathieuSolution a q w) (z : ℂ)
    (t : ℝ) :
    HasDerivAt (fun t : ℝ => w (t * z)) (z * deriv w (t * z)) t ∧
      HasDerivAt (fun t : ℝ => z * deriv w (t * z))
        (z ^ 2 * (2 * q * Complex.cos (2 * (t * z)) - a) * w (t * z)) t := by
  have hm : ∀ s : ℂ, HasDerivAt (fun s : ℂ => s * z) z s := fun s => hasDerivAt_mul_const z
  constructor
  · have h := ((hw.differentiable (t * z)).hasDerivAt.comp (t : ℂ) (hm t)).comp_ofReal
    exact h.congr_deriv (by ring)
  · have h := (((hw.hasDerivAt_deriv (t * z)).comp (t : ℂ) (hm t)).const_mul z).comp_ofReal
    exact h.congr_deriv (by ring)

/-- Separate holomorphy in `a` and in `q` of a family of Mathieu solutions with fixed initial
data at `0`. -/
theorem p2f_differentiable_param {W : ℂ → ℂ → ℂ → ℂ}
    (hW : ∀ a q, IsMathieuSolution a q (W a q)) {y₀ y₁ : ℂ} (h₀ : ∀ a q, W a q 0 = y₀)
    (h₁ : ∀ a q, deriv (W a q) 0 = y₁) (q z : ℂ) :
    Differentiable ℂ (fun a => W a q z) ∧ Differentiable ℂ (fun a => deriv (W a q) z) := by
  have := ODE.differentiable_param_of_linear_ode (p₀ := fun _ => 0) (p₁ := fun _ => 0)
    (q₀ := fun t : ℝ => z ^ 2 * (2 * q * Complex.cos (2 * (t * z)))) (q₁ := fun _ => -z ^ 2)
    continuous_const continuous_const (by fun_prop) continuous_const (t₀ := 0) (y₀ := y₀)
    (y₁ := z * y₁) (F := fun t a => W a q (t * z)) (F' := fun t a => z * deriv (W a q) (t * z))
    (fun a t => by
      obtain ⟨k1, k2⟩ := p2f_ray_hasDerivAt (hW a q) z t
      exact ⟨k1, k2.congr_deriv (by ring)⟩)
    (fun a => by simp [h₀]) (fun a => by simp [h₁]) 1
  simp only [Complex.ofReal_one, one_mul] at this
  refine ⟨this.1, ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [h₁]; exact differentiable_const _
  · have := this.2.const_mul z⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ hz] using this

/-- Separate holomorphy in `q` (companion of `p2f_differentiable_param`). -/
theorem p2f_differentiable_param_q {W : ℂ → ℂ → ℂ → ℂ}
    (hW : ∀ a q, IsMathieuSolution a q (W a q)) {y₀ y₁ : ℂ} (h₀ : ∀ a q, W a q 0 = y₀)
    (h₁ : ∀ a q, deriv (W a q) 0 = y₁) (a z : ℂ) :
    Differentiable ℂ (fun q => W a q z) ∧ Differentiable ℂ (fun q => deriv (W a q) z) := by
  have := ODE.differentiable_param_of_linear_ode (p₀ := fun _ => 0) (p₁ := fun _ => 0)
    (q₀ := fun _ => -(z ^ 2 * a)) (q₁ := fun t : ℝ => z ^ 2 * (2 * Complex.cos (2 * (t * z))))
    continuous_const continuous_const continuous_const (by fun_prop) (t₀ := 0) (y₀ := y₀)
    (y₁ := z * y₁) (F := fun t q => W a q (t * z)) (F' := fun t q => z * deriv (W a q) (t * z))
    (fun q t => by
      obtain ⟨k1, k2⟩ := p2f_ray_hasDerivAt (hW a q) z t
      exact ⟨k1, k2.congr_deriv (by ring)⟩)
    (fun q => by simp [h₀]) (fun q => by simp [h₁]) 1
  simp only [Complex.ofReal_one, one_mul] at this
  refine ⟨this.1, ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [h₁]; exact differentiable_const _
  · have := this.2.const_mul z⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ hz] using this

/-- Hartogs for three variables on `ℂ × ℂ × ℂ`. -/
theorem p2f_differentiable_of_separately {f : ℂ × ℂ × ℂ → ℂ}
    (h1 : ∀ b c, Differentiable ℂ (fun x => f (x, b, c)))
    (h2 : ∀ x c, Differentiable ℂ (fun b => f (x, b, c)))
    (h3 : ∀ x b, Differentiable ℂ (fun c => f (x, b, c))) : Differentiable ℂ f := by
  let g : (Fin 3 → ℂ) → ℂ := fun v => f (v 0, v 1, v 2)
  have hg : AnalyticOnNhd ℂ g univ := by
    refine SeveralComplexVariables.analyticOnNhd_of_separately_analytic isOpen_univ ?_
    intro v _ i
    fin_cases i
    · have := (h1 (v 1) (v 2)).analyticAt (v 0)
      simpa [g, Function.update] using this
    · have := (h2 (v 0) (v 2)).analyticAt (v 1)
      simpa [g, Function.update] using this
    · have := (h3 (v 0) (v 1)).analyticAt (v 2)
      simpa [g, Function.update] using this
  have hL : Differentiable ℂ (fun p : ℂ × ℂ × ℂ => (![p.1, p.2.1, p.2.2] : Fin 3 → ℂ)) := by
    refine differentiable_pi.2 fun i => ?_
    fin_cases i <;> simp
  exact (differentiableOn_univ.1 hg.differentiableOn).comp hL

/-- **Analytic dependence** (DLMF §28.2(ii)): the solution with given initial values at a point
is an entire function of `z`, `a` and `q`; for the basic solutions, `(z, a, q) ↦ w_I(z; a, q)`
and `(z, a, q) ↦ w_II(z; a, q)` are entire on `ℂ³`. -/
@[dlmf 28.2.ii]
theorem differentiable_mathieuWI_mathieuWII :
    Differentiable ℂ (fun p : ℂ × ℂ × ℂ => mathieuWI p.2.1 p.2.2 p.1) ∧
      Differentiable ℂ (fun p : ℂ × ℂ × ℂ => mathieuWII p.2.1 p.2.2 p.1) := by
  have hI := p2f_differentiable_param (W := mathieuWI) isMathieuSolution_mathieuWI
    (fun a q => (mathieuWI_spec a q).2.1) (fun a q => (mathieuWI_spec a q).2.2)
  have hI' := p2f_differentiable_param_q (W := mathieuWI) isMathieuSolution_mathieuWI
    (fun a q => (mathieuWI_spec a q).2.1) (fun a q => (mathieuWI_spec a q).2.2)
  have hII := p2f_differentiable_param (W := mathieuWII) isMathieuSolution_mathieuWII
    (fun a q => (mathieuWII_spec a q).2.1) (fun a q => (mathieuWII_spec a q).2.2)
  have hII' := p2f_differentiable_param_q (W := mathieuWII) isMathieuSolution_mathieuWII
    (fun a q => (mathieuWII_spec a q).2.1) (fun a q => (mathieuWII_spec a q).2.2)
  exact ⟨p2f_differentiable_of_separately
      (fun a q => (isMathieuSolution_mathieuWI a q).differentiable)
      (fun z q => (hI q z).1) (fun z a => (hI' a z).1),
    p2f_differentiable_of_separately (fun a q => (isMathieuSolution_mathieuWII a q).differentiable)
      (fun z q => (hII q z).1) (fun z a => (hII' a z).1)⟩

end Basic

/-! ### Change of sign of `q` for the basic solutions (from 28.2.4) -/

/-- Derivative of `z ↦ c f(z + s) - d g(z + s)`. -/
theorem p1a1_deriv_shift_lincomb {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (c d s z : ℂ) :
    deriv (fun x => c * f (x + s) - d * g (x + s)) z =
      c * deriv f (z + s) - d * deriv g (z + s) := by
  have h1 : HasDerivAt (fun x => f (x + s)) (deriv f (z + s)) z := by
    simpa using (hf (z + s)).hasDerivAt.comp_add_const z s
  have h2 : HasDerivAt (fun x => g (x + s)) (deriv g (z + s)) z := by
    simpa using (hg (z + s)).hasDerivAt.comp_add_const z s
  exact ((h1.const_mul c).sub (h2.const_mul d)).deriv

/-- `w_I(z; a, -q) = B' w_I(z + π/2; a, q) - A' w_II(z + π/2; a, q)` with `A = w_I(π/2)`,
`B = w_II(π/2)` (from the half-period symmetry 28.2.4). -/
theorem p1a1_mathieuWI_neg_q (a q z : ℂ) :
    mathieuWI a (-q) z = deriv (mathieuWII a q) (π / 2) * mathieuWI a q (z + π / 2) -
      deriv (mathieuWI a q) (π / 2) * mathieuWII a q (z + π / 2) := by
  obtain ⟨h1, -, -⟩ := mathieuWI_spec a q
  obtain ⟨h2, -, -⟩ := mathieuWII_spec a q
  obtain ⟨g, g0, g1⟩ := mathieuWI_spec a (-q)
  have hc := (h1.comp_add_half_pi.const_mul (deriv (mathieuWII a q) (π / 2))).add
    (h2.comp_add_half_pi.const_mul (-deriv (mathieuWI a q) (π / 2)))
  have hW := mathieuWI_wronskian a q (π / 2)
  have key := g.eq_of_initial hc (z₀ := 0)
    (by simp only [zero_add]; rw [g0]; linear_combination -hW)
    (by
      rw [g1]
      simp only [neg_mul, ← sub_eq_add_neg]
      rw [p1a1_deriv_shift_lincomb h1.differentiable h2.differentiable]
      simp only [zero_add]; ring)
  have := congrFun key z
  rw [this]; ring

/-- `w_II(z; a, -q) = -B w_I(z + π/2; a, q) + A w_II(z + π/2; a, q)`. -/
theorem p1a1_mathieuWII_neg_q (a q z : ℂ) :
    mathieuWII a (-q) z = mathieuWI a q (π / 2) * mathieuWII a q (z + π / 2) -
      mathieuWII a q (π / 2) * mathieuWI a q (z + π / 2) := by
  obtain ⟨h1, -, -⟩ := mathieuWI_spec a q
  obtain ⟨h2, -, -⟩ := mathieuWII_spec a q
  obtain ⟨g, g0, g1⟩ := mathieuWII_spec a (-q)
  have hc := (h2.comp_add_half_pi.const_mul (mathieuWI a q (π / 2))).add
    (h1.comp_add_half_pi.const_mul (-mathieuWII a q (π / 2)))
  have hW := mathieuWI_wronskian a q (π / 2)
  have key := g.eq_of_initial hc (z₀ := 0) (by simp only [zero_add]; rw [g0]; ring)
    (by
      rw [g1]
      simp only [neg_mul, ← sub_eq_add_neg]
      rw [p1a1_deriv_shift_lincomb h2.differentiable h1.differentiable]
      simp only [zero_add]; linear_combination -hW)
  have := congrFun key z
  rw [this]; ring

theorem p1a1_mathieuWI_half_pi_neg_q (a q : ℂ) :
    mathieuWI a (-q) (π / 2) = deriv (mathieuWII a q) (π / 2) := by
  rw [p1a1_mathieuWI_neg_q, show (π : ℂ) / 2 + π / 2 = π by ring, mathieuWII_pi,
    m28a_mathieuWI_pi]
  linear_combination deriv (mathieuWII a q) (π / 2) * mathieuWI_wronskian a q (π / 2)

theorem p1a1_mathieuWII_half_pi_neg_q (a q : ℂ) :
    mathieuWII a (-q) (π / 2) = mathieuWII a q (π / 2) := by
  rw [p1a1_mathieuWII_neg_q, show (π : ℂ) / 2 + π / 2 = π by ring, mathieuWII_pi,
    m28a_mathieuWI_pi]
  linear_combination mathieuWII a q (π / 2) * mathieuWI_wronskian a q (π / 2)

theorem p1a1_deriv_mathieuWI_half_pi_neg_q (a q : ℂ) :
    deriv (mathieuWI a (-q)) (π / 2) = deriv (mathieuWI a q) (π / 2) := by
  have e : mathieuWI a (-q) = fun z => deriv (mathieuWII a q) (π / 2) *
      mathieuWI a q (z + π / 2) - deriv (mathieuWI a q) (π / 2) * mathieuWII a q (z + π / 2) :=
    funext (p1a1_mathieuWI_neg_q a q)
  rw [e, p1a1_deriv_shift_lincomb (isMathieuSolution_mathieuWI a q).differentiable
    (isMathieuSolution_mathieuWII a q).differentiable,
    show (π : ℂ) / 2 + π / 2 = π by ring, deriv_mathieuWI_pi, m28a_deriv_mathieuWII_pi]
  linear_combination deriv (mathieuWI a q) (π / 2) * mathieuWI_wronskian a q (π / 2)

theorem p1a1_deriv_mathieuWII_half_pi_neg_q (a q : ℂ) :
    deriv (mathieuWII a (-q)) (π / 2) = mathieuWI a q (π / 2) := by
  have e : mathieuWII a (-q) = fun z => mathieuWI a q (π / 2) * mathieuWII a q (z + π / 2) -
      mathieuWII a q (π / 2) * mathieuWI a q (z + π / 2) :=
    funext (p1a1_mathieuWII_neg_q a q)
  rw [e, p1a1_deriv_shift_lincomb (isMathieuSolution_mathieuWII a q).differentiable
    (isMathieuSolution_mathieuWI a q).differentiable,
    show (π : ℂ) / 2 + π / 2 = π by ring, deriv_mathieuWI_pi, m28a_deriv_mathieuWII_pi]
  linear_combination mathieuWI a q (π / 2) * mathieuWI_wronskian a q (π / 2)


/-- The derivative of a solution at `π`, in terms of the basic solutions. -/
theorem IsMathieuSolution.p1a1_deriv_eq {a q : ℂ} {w : ℂ → ℂ} (h : IsMathieuSolution a q w)
    (z : ℂ) : deriv w z = w 0 * deriv (mathieuWI a q) z + deriv w 0 * deriv (mathieuWII a q) z := by
  conv_lhs => rw [h.eq_combination]
  exact m28a_deriv_lincomb ((isMathieuSolution_mathieuWI a q).differentiable z)
    ((isMathieuSolution_mathieuWII a q).differentiable z) _ _

/-! ### Floquet theory (§28.2(iii)–(iv)) -/

/-- **Floquet's theorem** (DLMF 28.2.14–28.2.15): Mathieu's equation has a nontrivial solution
with `w(z + π) = e^{πiν} w(z)` iff `e^{πiν}` is an eigenvalue of the monodromy matrix 28.2.15. -/
@[dlmf 28.2.E14, dlmf 28.2.E15]
theorem exists_isFloquetSolution_iff (a q ν : ℂ) :
    (∃ w, IsFloquetSolution a q ν w) ↔
      ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
        (mathieuMonodromy a q).mulVec v = Complex.exp (π * I * ν) • v := by
  set μ := Complex.exp (π * I * ν)
  obtain ⟨h1, h10, h11⟩ := mathieuWI_spec a q
  obtain ⟨h2, h20, h21⟩ := mathieuWII_spec a q
  constructor
  · rintro ⟨w, hw, hne, hper⟩
    refine ⟨![w 0, deriv w 0], ?_, ?_⟩
    · intro hv
      have e0 : w 0 = 0 := by simpa using congrFun hv 0
      have e1 : deriv w 0 = 0 := by simpa using congrFun hv 1
      apply hne
      rw [hw.eq_combination]; funext z; simp [e0, e1]
    · have hf : (fun z => w (z + π)) = fun z => μ * w z := funext hper
      have d1 : deriv w π = μ * deriv w 0 := by
        have := congrArg (fun f => deriv f 0) hf
        rw [deriv_comp_add_const, zero_add,
          deriv_const_mul _ (hw.differentiable 0)] at this
        exact this
      have v0 : w π = μ * w 0 := by simpa using hper 0
      have c0 := congrFun hw.eq_combination π
      have c1 := hw.p1a1_deriv_eq π
      ext i; fin_cases i
      · simp [mathieuMonodromy, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        rw [← v0, c0]; ring
      · simp [mathieuMonodromy, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        rw [← d1, c1]; ring
  · rintro ⟨v, hv, hM⟩
    have m0 := congrFun hM 0
    have m1 := congrFun hM 1
    simp [mathieuMonodromy, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at m0 m1
    set w := fun z => v 0 * mathieuWI a q z + v 1 * mathieuWII a q z with hwdef
    have hw : IsMathieuSolution a q w := (h1.const_mul _).add (h2.const_mul _)
    have hw0 : w 0 = v 0 := by simp [w, h10, h20]
    have hw1 : deriv w 0 = v 1 := by
      rw [hwdef, m28a_deriv_lincomb (h1.differentiable 0) (h2.differentiable 0), h11, h21]
      ring
    refine ⟨w, hw, ?_, fun z => ?_⟩
    · intro hz
      apply hv
      have e0 : v 0 = 0 := by rw [← hw0, hz]; rfl
      have e1 : v 1 = 0 := by rw [← hw1, hz]; simp
      ext i; fin_cases i <;> simp [e0, e1]
    · have key := hw.comp_add_pi.eq_of_initial (hw.const_mul μ) (z₀ := 0)
        (by simp only [zero_add, w, h10, h20]; linear_combination m0)
        (by
          rw [deriv_comp_add_const, zero_add, deriv_const_mul _ (hw.differentiable 0), hw1,
            hwdef, m28a_deriv_lincomb (h1.differentiable _) (h2.differentiable _)]
          linear_combination m1)
      exact congrFun key z

/-- **Characteristic equation** (DLMF 28.2.16): a Floquet solution with respect to `ν` exists iff
`cos πν = w_I(π; a, q)`. -/
@[dlmf 28.2.E16]
theorem exists_isFloquetSolution_iff_charExp (a q ν : ℂ) :
    (∃ w, IsFloquetSolution a q ν w) ↔ IsMathieuCharExp a q ν := by
  rw [exists_isFloquetSolution_iff]
  set μ := Complex.exp (π * I * ν)
  have hμ : μ ≠ 0 := Complex.exp_ne_zero _
  set M := mathieuMonodromy a q
  have e1 : (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M.mulVec v = μ • v) ↔
      ∃ v ≠ 0, (M - μ • (1 : Matrix (Fin 2) (Fin 2) ℂ)).mulVec v = 0 := by
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
  rw [e1, Matrix.exists_mulVec_eq_zero_iff, Matrix.det_fin_two]
  have hW := mathieuWI_wronskian a q π
  have h9 := mathieuWI_pi_eq_deriv_mathieuWII_pi a q
  have hcos : Complex.cos (π * ν) = (μ + μ⁻¹) / 2 := by
    rw [Complex.cos, show (π : ℂ) * ν * I = π * I * ν by ring,
      show -((π : ℂ) * ν) * I = -(π * I * ν) by ring, Complex.exp_neg]
  simp only [M, mathieuMonodromy, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul]
  simp only [Fin.isValue, ↓reduceIte, mul_one, mul_zero, sub_zero, zero_ne_one, one_ne_zero]
  rw [IsMathieuCharExp, hcos]
  rw [← h9] at hW ⊢
  constructor
  · intro h
    field_simp
    linear_combination h - hW
  · intro h
    field_simp at h
    linear_combination h + hW

/-- **DLMF 28.2.16** (second equality): `w_I(π; a, q) = w_I(π; a, -q)`. -/
@[dlmf 28.2.E16]
theorem mathieuWI_pi_neg_q (a q : ℂ) : mathieuWI a q π = mathieuWI a (-q) π := by
  rw [m28a_mathieuWI_pi, m28a_mathieuWI_pi a (-q), p1a1_mathieuWI_half_pi_neg_q,
    p1a1_mathieuWII_half_pi_neg_q, p1a1_deriv_mathieuWI_half_pi_neg_q,
    p1a1_deriv_mathieuWII_half_pi_neg_q]
  ring

/-- If `g` is entire and even, `s ↦ g(√s)` is entire. -/
theorem p2f_differentiable_comp_sqrt {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hev : ∀ w, g (-w) = g w) : Differentiable ℂ (fun s => g (s ^ (2⁻¹ : ℂ))) := by
  have key : ∀ s w : ℂ, w ^ 2 = s → g (s ^ (2⁻¹ : ℂ)) = g w := by
    intro s w hw
    have : w ^ 2 = (s ^ (2⁻¹ : ℂ)) ^ 2 := by rw [hw, Complex.cpow_ofNat_inv_pow]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h
    · rw [h]
    · rw [h, hev]
  have hne : ∀ s₀ : ℂ, s₀ ≠ 0 → DifferentiableAt ℂ (fun s => g (s ^ (2⁻¹ : ℂ))) s₀ := by
    intro s₀ hs₀
    by_cases hsl : s₀ ∈ Complex.slitPlane
    · exact (hg _).comp s₀ (differentiableAt_id.cpow_const hsl)
    · have hsl' : -s₀ ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff] at hsl ⊢
        push Not at hsl
        left
        have hre : s₀.re ≠ 0 := fun h => hs₀ (Complex.ext h hsl.2)
        simp only [neg_re]
        exact neg_pos.2 (lt_of_le_of_ne hsl.1 hre)
      have e : (fun s => g (s ^ (2⁻¹ : ℂ))) = fun s => g (I * (-s) ^ (2⁻¹ : ℂ)) := by
        funext s
        apply key
        rw [mul_pow, Complex.cpow_ofNat_inv_pow, I_sq]; ring
      rw [e]
      exact (hg _).comp s₀ (differentiableAt_const _ |>.mul
        ((differentiableAt_id.neg).cpow_const hsl'))
  have hc : ContinuousAt (fun s => g (s ^ (2⁻¹ : ℂ))) 0 :=
    (hg _).continuousAt.comp (continuousAt_cpow_const_of_re_pos (Or.inl (by simp)) (by norm_num))
  intro s₀
  rcases eq_or_ne s₀ 0 with rfl | hs₀
  · have := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (f := fun s => g (s ^ (2⁻¹ : ℂ))) (s := univ) (c := 0) univ_mem).1
      ⟨fun s hs => (hne s hs.2).differentiableWithinAt, hc⟩
    exact this.differentiableAt univ_mem
  · exact hne s₀ hs₀

/-- Hartogs for two variables on `ℂ × ℂ`. -/
theorem p2f_differentiable_of_separately₂ {f : ℂ × ℂ → ℂ}
    (h1 : ∀ b, Differentiable ℂ (fun x => f (x, b)))
    (h2 : ∀ x, Differentiable ℂ (fun b => f (x, b))) : Differentiable ℂ f := by
  let g : (Fin 2 → ℂ) → ℂ := fun v => f (v 0, v 1)
  have hg : AnalyticOnNhd ℂ g univ := by
    refine SeveralComplexVariables.analyticOnNhd_of_separately_analytic isOpen_univ ?_
    intro v _ i
    fin_cases i
    · have := (h1 (v 1)).analyticAt (v 0)
      simpa [g, Function.update] using this
    · have := (h2 (v 0)).analyticAt (v 1)
      simpa [g, Function.update] using this
  have hL : Differentiable ℂ (fun p : ℂ × ℂ => (![p.1, p.2] : Fin 2 → ℂ)) := by
    refine differentiable_pi.2 fun i => ?_
    fin_cases i <;> simp
  exact (differentiableOn_univ.1 hg.differentiableOn).comp hL

/-- `cos πν` is an entire function of `a` and `q²` (DLMF §28.2(iii)): there is an entire
function `F` on `ℂ²` with `w_I(π; a, q) = F(a, q²)`. -/
@[dlmf 28.2.iii]
theorem exists_entire_mathieuWI_pi :
    ∃ F : ℂ × ℂ → ℂ, Differentiable ℂ F ∧ ∀ a q, mathieuWI a q π = F (a, q ^ 2) := by
  have hI := p2f_differentiable_param (W := mathieuWI) isMathieuSolution_mathieuWI
    (fun a q => (mathieuWI_spec a q).2.1) (fun a q => (mathieuWI_spec a q).2.2)
  have hI' := p2f_differentiable_param_q (W := mathieuWI) isMathieuSolution_mathieuWI
    (fun a q => (mathieuWI_spec a q).2.1) (fun a q => (mathieuWI_spec a q).2.2)
  have hev : ∀ a q : ℂ, mathieuWI a (-q) π = mathieuWI a q π := fun a q =>
    (mathieuWI_pi_neg_q a q).symm
  refine ⟨fun p => mathieuWI p.1 (p.2 ^ (2⁻¹ : ℂ)) π, ?_, fun a q => ?_⟩
  · exact p2f_differentiable_of_separately₂ (fun s => (hI (s ^ (2⁻¹ : ℂ)) π).1)
      (fun a => p2f_differentiable_comp_sqrt (g := fun q => mathieuWI a q π) (hI' a _).1
        (hev a))
  · have : q ^ 2 = ((q ^ 2) ^ (2⁻¹ : ℂ)) ^ 2 := by rw [Complex.cpow_ofNat_inv_pow]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h
    · simp only; rw [← h]
    · show mathieuWI a q π = mathieuWI a ((q ^ 2) ^ (2⁻¹ : ℂ)) π
      rw [← hev a ((q ^ 2) ^ (2⁻¹ : ℂ)), ← h]

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

/-- `ℜ √z ≥ 0` for the principal square root. -/
theorem p1a1_re_sqrt_nonneg (z : ℂ) : 0 ≤ (Complex.sqrt z).re := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Complex.sqrt, Complex.zero_cpow (by norm_num : (2⁻¹ : ℂ) ≠ 0)]
  · rw [Complex.sqrt, Complex.cpow_def_of_ne_zero hz, Complex.exp_re]
    refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩)
    · have := Complex.neg_pi_lt_arg z
      have e : (Complex.log z * 2⁻¹).im = Complex.arg z / 2 := by
        simp [Complex.log_im]; ring
      rw [e]; linarith
    · have := Complex.arg_le_pi z
      have e : (Complex.log z * 2⁻¹).im = Complex.arg z / 2 := by
        simp [Complex.log_im]; ring
      rw [e]; linarith

/-- `0 ≤ ℜ(arccos c / π) ≤ 1` for the principal arccosine. -/
theorem p1a1_re_arccosPrincipal_div_pi_mem (c : ℂ) :
    0 ≤ (DLMF.Elementary.arccosPrincipal c / π).re ∧
      (DLMF.Elementary.arccosPrincipal c / π).re ≤ 1 := by
  set s := Complex.sqrt (1 - c ^ 2)
  set w := s + I * c
  have hs : s ^ 2 = 1 - c ^ 2 := DLMF.Elementary.trig_sqrt_sq _
  have hprod : w * (s - I * c) = 1 := by
    simp only [w]; linear_combination hs - c ^ 2 * Complex.I_sq
  have hw0 : w ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have hre : 0 ≤ w.re := by
    have hinv : s - I * c = w⁻¹ := eq_inv_of_mul_eq_one_right hprod
    have h2 : w.re + (w⁻¹).re = 2 * s.re := by
      rw [← hinv]; simp only [w, Complex.add_re, Complex.sub_re]; ring
    rw [Complex.inv_re] at h2
    have hn : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw0
    have hsr := p1a1_re_sqrt_nonneg (1 - c ^ 2)
    by_contra hneg
    rw [not_le] at hneg
    have : w.re / Complex.normSq w < 0 := div_neg_of_neg_of_pos hneg hn
    linarith
  have harg := (Complex.abs_arg_le_pi_div_two_iff).mpr hre
  rw [abs_le] at harg
  have e : (DLMF.Elementary.arccosPrincipal c / π).re = (π / 2 - Complex.arg w) / π := by
    rw [Complex.div_ofReal_re]
    congr 1
    simp [DLMF.Elementary.arccosPrincipal, DLMF.Elementary.arcsinPrincipal, Complex.log_im, w, s]
    ring
  rw [e]
  constructor
  · apply div_nonneg _ Real.pi_pos.le; linarith
  · rw [div_le_one Real.pi_pos]; linarith [Real.pi_pos]

/-- The principal exponent satisfies `0 ≤ ℜν̂ ≤ 1` (DLMF §28.2(iii)). -/
@[dlmf 28.2.iii]
theorem re_arccosPrincipal_mathieuWI_div_pi_mem (a q : ℂ) :
    0 ≤ (DLMF.Elementary.arccosPrincipal (mathieuWI a q π) / π).re ∧
      (DLMF.Elementary.arccosPrincipal (mathieuWI a q π) / π).re ≤ 1 :=
  p1a1_re_arccosPrincipal_div_pi_mem _

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

/-- Derivative periodicity from periodicity. -/
theorem p1a2_deriv_periodic {f : ℂ → ℂ} {T : ℂ} (hf : ∀ z, f (z + T) = f z) (z : ℂ) :
    deriv f (z + T) = deriv f z := by
  have : (fun z => f (z + T)) = f := funext hf
  have h := deriv_comp_add_const (f := f) (a := T) (x := z)
  rw [this] at h
  exact h.symm

/-- Integration-by-parts identity behind the recurrences 28.4.5–28.4.8 (cosine form). -/
theorem p1a2_cos_rec {a q : ℂ} {f : ℂ → ℂ} (hf : IsMathieuSolution a q f)
    (hper : ∀ z, f (z + 2 * π) = f z) (k : ℤ) :
    (a - (k : ℂ) ^ 2) * ∫ x in (0 : ℝ)..2 * π, f x * Complex.cos (k * x) =
      q * ((∫ x in (0 : ℝ)..2 * π, f x * Complex.cos (((k - 2 : ℤ) : ℂ) * x)) +
        ∫ x in (0 : ℝ)..2 * π, f x * Complex.cos (((k + 2 : ℤ) : ℂ) * x)) := by
  set K : ℂ := (k : ℂ)
  let g : ℝ → ℂ := fun x => deriv f x * Complex.cos (K * x) + K * f x * Complex.sin (K * x)
  have hg : ∀ x : ℝ, HasDerivAt g
      ((2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * Complex.cos (K * x))) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => deriv f x)
        ((2 * q * Complex.cos (2 * x) - a) * f x) x := (hf.hasDerivAt_deriv x).comp_ofReal
    have h0 : HasDerivAt (fun x : ℝ => f x) (deriv f x) x :=
      (hf.differentiable x).hasDerivAt.comp_ofReal
    have hl : HasDerivAt (fun x : ℝ => K * (x : ℂ)) K x := by
      simpa using ((hasDerivAt_id (x : ℂ)).const_mul K).comp_ofReal
    have hc : HasDerivAt (fun x : ℝ => Complex.cos (K * x)) (-Complex.sin (K * x) * K) x :=
      (Complex.hasDerivAt_cos _).comp x hl
    have hs : HasDerivAt (fun x : ℝ => Complex.sin (K * x)) (Complex.cos (K * x) * K) x :=
      (Complex.hasDerivAt_sin _).comp x hl
    convert (h1.mul hc).add ((h0.const_mul K).mul hs) using 1
    ring
  have hcont : Continuous fun x : ℝ =>
      (2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * Complex.cos (K * x)) := by
    have := hf.differentiable.continuous
    fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 2 * π)
    (fun x _ => hg x) (hcont.intervalIntegrable _ _)
  have hK1 : Complex.cos (K * ((2 * π : ℝ) : ℂ)) = 1 := by
    rw [show K * ((2 * π : ℝ) : ℂ) = (k : ℂ) * (2 * π) by push_cast; ring]
    exact Complex.cos_int_mul_two_pi k
  have hK2 : Complex.sin (K * ((2 * π : ℝ) : ℂ)) = 0 := by
    rw [show K * ((2 * π : ℝ) : ℂ) = (k : ℂ) * (2 * π) by push_cast; ring]
    exact Complex.sin_int_mul_pi (2 * k) |>.symm ▸ by push_cast; ring_nf
  have hper' := p1a2_deriv_periodic hper 0
  rw [zero_add] at hper'
  have h0 : ∫ x in (0 : ℝ)..2 * π,
      (2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * Complex.cos (K * x)) = 0 := by
    rw [hint]
    simp only [g, hK1, hK2]
    push_cast
    rw [hper', show f (2 * π) = f 0 by simpa using hper 0]
    simp
  have hpt : ∀ x : ℝ, (2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * Complex.cos (K * x)) =
      q * (f x * Complex.cos (((k - 2 : ℤ) : ℂ) * x)) +
        q * (f x * Complex.cos (((k + 2 : ℤ) : ℂ) * x)) +
        (K ^ 2 - a) * (f x * Complex.cos (K * x)) := by
    intro x
    push_cast
    rw [show (K - 2) * (x : ℂ) = K * x - 2 * x by ring,
      show (K + 2) * (x : ℂ) = K * x + 2 * x by ring, Complex.cos_sub, Complex.cos_add]
    ring
  have hc : ∀ j : ℤ, Continuous fun x : ℝ => f x * Complex.cos ((j : ℂ) * x) := by
    intro j
    have := hf.differentiable.continuous
    fun_prop
  simp_rw [hpt] at h0
  rw [intervalIntegral.integral_add (((hc _).intervalIntegrable _ _).const_mul _ |>.add
      (((hc _).intervalIntegrable _ _).const_mul _)) (((hc k).intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_add (((hc _).intervalIntegrable _ _).const_mul _)
      (((hc _).intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h0
  linear_combination -h0

/-- Integration-by-parts identity behind the recurrences 28.4.5–28.4.8 (sine form). -/
theorem p1a2_sin_rec {a q : ℂ} {f : ℂ → ℂ} (hf : IsMathieuSolution a q f)
    (hper : ∀ z, f (z + 2 * π) = f z) (k : ℤ) :
    (a - (k : ℂ) ^ 2) * ∫ x in (0 : ℝ)..2 * π, f x * Complex.sin (k * x) =
      q * ((∫ x in (0 : ℝ)..2 * π, f x * Complex.sin (((k - 2 : ℤ) : ℂ) * x)) +
        ∫ x in (0 : ℝ)..2 * π, f x * Complex.sin (((k + 2 : ℤ) : ℂ) * x)) := by
  set K : ℂ := (k : ℂ)
  let g : ℝ → ℂ := fun x => deriv f x * Complex.sin (K * x) - K * f x * Complex.cos (K * x)
  have hg : ∀ x : ℝ, HasDerivAt g
      ((2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * Complex.sin (K * x))) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => deriv f x)
        ((2 * q * Complex.cos (2 * x) - a) * f x) x := (hf.hasDerivAt_deriv x).comp_ofReal
    have h0 : HasDerivAt (fun x : ℝ => f x) (deriv f x) x :=
      (hf.differentiable x).hasDerivAt.comp_ofReal
    have hl : HasDerivAt (fun x : ℝ => K * (x : ℂ)) K x := by
      simpa using ((hasDerivAt_id (x : ℂ)).const_mul K).comp_ofReal
    have hc : HasDerivAt (fun x : ℝ => Complex.cos (K * x)) (-Complex.sin (K * x) * K) x :=
      (Complex.hasDerivAt_cos _).comp x hl
    have hs : HasDerivAt (fun x : ℝ => Complex.sin (K * x)) (Complex.cos (K * x) * K) x :=
      (Complex.hasDerivAt_sin _).comp x hl
    convert (h1.mul hs).sub ((h0.const_mul K).mul hc) using 1
    ring
  have hcont : Continuous fun x : ℝ =>
      (2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * Complex.sin (K * x)) := by
    have := hf.differentiable.continuous
    fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 2 * π)
    (fun x _ => hg x) (hcont.intervalIntegrable _ _)
  have hK1 : Complex.cos (K * ((2 * π : ℝ) : ℂ)) = 1 := by
    rw [show K * ((2 * π : ℝ) : ℂ) = (k : ℂ) * (2 * π) by push_cast; ring]
    exact Complex.cos_int_mul_two_pi k
  have hK2 : Complex.sin (K * ((2 * π : ℝ) : ℂ)) = 0 := by
    rw [show K * ((2 * π : ℝ) : ℂ) = (k : ℂ) * (2 * π) by push_cast; ring]
    exact Complex.sin_int_mul_pi (2 * k) |>.symm ▸ by push_cast; ring_nf
  have h0 : ∫ x in (0 : ℝ)..2 * π,
      (2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * Complex.sin (K * x)) = 0 := by
    rw [hint]
    simp only [g, hK1, hK2]
    push_cast
    rw [show f (2 * π) = f 0 by simpa using hper 0]
    simp
  have hpt : ∀ x : ℝ, (2 * q * Complex.cos (2 * x) - a + K ^ 2) * (f x * Complex.sin (K * x)) =
      q * (f x * Complex.sin (((k - 2 : ℤ) : ℂ) * x)) +
        q * (f x * Complex.sin (((k + 2 : ℤ) : ℂ) * x)) +
        (K ^ 2 - a) * (f x * Complex.sin (K * x)) := by
    intro x
    push_cast
    rw [show (K - 2) * (x : ℂ) = K * x - 2 * x by ring,
      show (K + 2) * (x : ℂ) = K * x + 2 * x by ring, Complex.sin_sub, Complex.sin_add]
    ring
  have hc : ∀ j : ℤ, Continuous fun x : ℝ => f x * Complex.sin ((j : ℂ) * x) := by
    intro j
    have := hf.differentiable.continuous
    fun_prop
  simp_rw [hpt] at h0
  rw [intervalIntegral.integral_add (((hc _).intervalIntegrable _ _).const_mul _ |>.add
      (((hc _).intervalIntegrable _ _).const_mul _)) (((hc k).intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_add (((hc _).intervalIntegrable _ _).const_mul _)
      (((hc _).intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h0
  linear_combination -h0

/-- Exponential decay of the cosine integrals of an even entire `2π`-periodic function. -/
theorem p2f_cos_coeff_decay {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hper : ∀ z, F (z + 2 * π) = F z) (hev : ∀ z, F (-z) = F z) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ m : ℕ,
      ‖∫ x in (0 : ℝ)..2 * π, F x * Complex.cos (m * x)‖ ≤ C * Real.exp (-(R * m)) := by
  have hc := hF.continuous
  obtain ⟨C, hC0, hC⟩ := p1a2_fourierInt_decay hF hper R
  refine ⟨C, hC0, fun m => ?_⟩
  have hs0 : ∫ x in (0 : ℝ)..2 * π, F x * Complex.sin (((m : ℤ) : ℂ) * x) = 0 := by
    apply p1a2_integral_odd_periodic (p1a2_periodic_mul_sin hper m)
    intro x
    push_cast
    rw [hev, show (m : ℂ) * -x = -(m * x) by ring, Complex.sin_neg]; ring
  have h := hC m
  rw [p1a2_fourierInt_eq hc, hs0, mul_zero, sub_zero] at h
  push_cast at h
  simpa using h

/-- Exponential decay of the sine integrals of an odd entire `2π`-periodic function. -/
theorem p2f_sin_coeff_decay {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hper : ∀ z, F (z + 2 * π) = F z) (hodd : ∀ z, F (-z) = -F z) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ m : ℕ,
      ‖∫ x in (0 : ℝ)..2 * π, F x * Complex.sin (m * x)‖ ≤ C * Real.exp (-(R * m)) := by
  have hc := hF.continuous
  obtain ⟨C, hC0, hC⟩ := p1a2_fourierInt_decay hF hper R
  refine ⟨C, hC0, fun m => ?_⟩
  have hc0 : ∫ x in (0 : ℝ)..2 * π, F x * Complex.cos (((m : ℤ) : ℂ) * x) = 0 := by
    apply p1a2_integral_odd_periodic (p1a2_periodic_mul_cos hper m)
    intro x
    push_cast
    rw [hodd, show (m : ℂ) * -x = -(m * x) by ring, Complex.cos_neg]; ring
  have h := hC m
  rw [p1a2_fourierInt_eq hc, hc0, zero_sub, norm_neg, norm_mul, Complex.norm_I, one_mul] at h
  push_cast at h
  simpa using h

/-- A sequence satisfying a three-term recurrence with `q ≠ 0` and two vanishing initial
values vanishes. -/
theorem p2f_chain_zero {q : ℂ} (hq : q ≠ 0) {b x : ℕ → ℂ}
    (hrec : ∀ j, b j * x (j + 1) = q * (x j + x (j + 2))) (h0 : x 0 = 0) (h1 : x 1 = 0) :
    ∀ j, x j = 0 := by
  have : ∀ j, x j = 0 ∧ x (j + 1) = 0 := by
    intro j
    induction j with
    | zero => exact ⟨h0, h1⟩
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      have h := hrec j
      rw [ih.1, ih.2, mul_zero, zero_add] at h
      exact (mul_eq_zero.1 h.symm).resolve_left hq
  exact fun j => (this j).1

/-- The Casoratian of two solutions of the same three-term recurrence is constant. -/
theorem p2f_chain_const {q : ℂ} (hq : q ≠ 0) {b x y : ℕ → ℂ}
    (hx : ∀ j, b j * x (j + 1) = q * (x j + x (j + 2)))
    (hy : ∀ j, b j * y (j + 1) = q * (y j + y (j + 2))) (j : ℕ) :
    x j * y (j + 1) - x (j + 1) * y j = x 0 * y 1 - x 1 * y 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← ih]
    have h : q * ((x (j + 1) * y (j + 1 + 1) - x (j + 1 + 1) * y (j + 1)) -
        (x j * y (j + 1) - x (j + 1) * y j)) = 0 := by
      linear_combination y (j + 1) * hx j - x (j + 1) * hy j
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hq)

/-- **Coexistence is impossible** (Ince): for `q ≠ 0` an even and an odd solution of Mathieu's
equation cannot both be `π`-periodic, or both `π`-antiperiodic. -/
theorem p2f_ince_core {a q μ : ℂ} (hq : q ≠ 0) (hμ : μ = 1 ∨ μ = -1) {F G : ℂ → ℂ}
    (hF : IsMathieuSolution a q F) (hG : IsMathieuSolution a q G) (hFe : ∀ z, F (-z) = F z)
    (hGo : ∀ z, G (-z) = -G z) (hFp : ∀ z, F (z + π) = μ * F z)
    (hGp : ∀ z, G (z + π) = μ * G z) : F = 0 ∨ G = 0 := by
  have hμ2 : μ * μ = 1 := by rcases hμ with rfl | rfl <;> norm_num
  have hF2 : ∀ z, F (z + 2 * π) = F z := fun z => by
    rw [show z + 2 * π = z + π + π by ring, hFp, hFp, ← mul_assoc, hμ2, one_mul]
  have hG2 : ∀ z, G (z + 2 * π) = G z := fun z => by
    rw [show z + 2 * π = z + π + π by ring, hGp, hGp, ← mul_assoc, hμ2, one_mul]
  set α : ℤ → ℂ := fun k => ∫ x in (0 : ℝ)..2 * π, F x * Complex.cos (k * x) with hα
  set β : ℤ → ℂ := fun k => ∫ x in (0 : ℝ)..2 * π, G x * Complex.sin (k * x) with hβ
  have recα : ∀ k : ℤ, (a - (k : ℂ) ^ 2) * α k = q * (α (k - 2) + α (k + 2)) :=
    p1a2_cos_rec hF hF2
  have recβ : ∀ k : ℤ, (a - (k : ℂ) ^ 2) * β k = q * (β (k - 2) + β (k + 2)) :=
    p1a2_sin_rec hG hG2
  have αneg : ∀ k : ℤ, α (-k) = α k := fun k => by
    simp only [α]; congr 1; funext x; push_cast; rw [neg_mul, Complex.cos_neg]
  have βneg : ∀ k : ℤ, β (-k) = -β k := fun k => by
    simp only [β]; rw [← intervalIntegral.integral_neg]; congr 1; funext x; push_cast
    rw [neg_mul, Complex.sin_neg]; ring
  have β0 : β 0 = 0 := by simp [β]
  -- the sign of `cos m(x + π)`, `sin m(x + π)`
  have hcs : ∀ m : ℕ, ∀ x : ℂ, Complex.cos (m * (x + π)) = (-1) ^ m * Complex.cos (m * x) ∧
      Complex.sin (m * (x + π)) = (-1) ^ m * Complex.sin (m * x) := by
    intro m x
    have hc : Complex.cos (m * π) = (-1) ^ m := by
      induction m with
      | zero => simp
      | succ m ih => push_cast; rw [add_mul, one_mul, Complex.cos_add_pi, ih]; ring
    rw [show (m : ℂ) * (x + π) = m * x + m * π by ring, Complex.cos_add, Complex.sin_add,
      hc, Complex.sin_nat_mul_pi]
    constructor <;> ring
  -- wrong parity coefficients vanish
  have hwrong : ∀ m : ℕ, (-1 : ℂ) ^ m * μ = -1 → α m = 0 ∧ β m = 0 := by
    intro m hm
    have hFc := hF.differentiable.continuous
    have hGc := hG.differentiable.continuous
    constructor
    · simp only [α]
      apply p1a2_integral_antiperiodic (by push_cast; fun_prop)
      intro x; push_cast
      rw [hFp, (hcs m x).1]
      linear_combination (F x * Complex.cos (m * x)) * hm
    · simp only [β]
      apply p1a2_integral_antiperiodic (by push_cast; fun_prop)
      intro x; push_cast
      rw [hGp, (hcs m x).2]
      linear_combination (G x * Complex.sin (m * x)) * hm
  -- decay of the coefficients
  obtain ⟨Cα, hCα0, hCα⟩ := p2f_cos_coeff_decay hF.differentiable hF2 hFe 1
  obtain ⟨Cβ, hCβ0, hCβ⟩ := p2f_sin_coeff_decay hG.differentiable hG2 hGo 1
  have tα : ∀ k₀ : ℕ, Tendsto (fun j : ℕ => α ((k₀ + 2 * j : ℕ) : ℤ)) atTop (𝓝 0) := by
    intro k₀
    have hlim := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul Cα
    rw [mul_zero] at hlim
    refine squeeze_zero_norm (fun j => ?_) hlim
    have := hCα (k₀ + 2 * j)
    simp only [α, Int.cast_natCast, Function.comp_apply]
    refine this.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCα0)
    push_cast; linarith [(Nat.cast_nonneg k₀ : (0 : ℝ) ≤ k₀), (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have tβ : ∀ k₀ : ℕ, Tendsto (fun j : ℕ => β ((k₀ + 2 * j : ℕ) : ℤ)) atTop (𝓝 0) := by
    intro k₀
    have hlim := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul Cβ
    rw [mul_zero] at hlim
    refine squeeze_zero_norm (fun j => ?_) hlim
    have := hCβ (k₀ + 2 * j)
    simp only [β, Int.cast_natCast, Function.comp_apply]
    refine this.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCβ0)
    push_cast; linarith [(Nat.cast_nonneg k₀ : (0 : ℝ) ≤ k₀), (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  -- the chains of coefficients of the right parity
  have hx : ∀ k₀ : ℕ, ∀ j : ℕ, (a - (((k₀ + 2 * (j + 1) : ℕ) : ℤ) : ℂ) ^ 2) *
      α ((k₀ + 2 * (j + 1) : ℕ) : ℤ) =
      q * (α ((k₀ + 2 * j : ℕ) : ℤ) + α ((k₀ + 2 * (j + 2) : ℕ) : ℤ)) := by
    intro k₀ j
    rw [recα]
    congr 3; push_cast; ring
  have hy : ∀ k₀ : ℕ, ∀ j : ℕ, (a - (((k₀ + 2 * (j + 1) : ℕ) : ℤ) : ℂ) ^ 2) *
      β ((k₀ + 2 * (j + 1) : ℕ) : ℤ) =
      q * (β ((k₀ + 2 * j : ℕ) : ℤ) + β ((k₀ + 2 * (j + 2) : ℕ) : ℤ)) := by
    intro k₀ j
    rw [recβ]
    congr 3; push_cast; ring
  have hD : ∀ k₀ : ℕ, α ((k₀ : ℕ) : ℤ) * β ((k₀ + 2 : ℕ) : ℤ) -
      α ((k₀ + 2 : ℕ) : ℤ) * β ((k₀ : ℕ) : ℤ) = 0 := by
    intro k₀
    have hc := p2f_chain_const hq (x := fun j => α ((k₀ + 2 * j : ℕ) : ℤ))
      (y := fun j => β ((k₀ + 2 * j : ℕ) : ℤ))
      (b := fun j => a - (((k₀ + 2 * (j + 1) : ℕ) : ℤ) : ℂ) ^ 2) (hx k₀) (hy k₀)
    have ht : Tendsto (fun j : ℕ => α ((k₀ + 2 * j : ℕ) : ℤ) * β ((k₀ + 2 * (j + 1) : ℕ) : ℤ) -
        α ((k₀ + 2 * (j + 1) : ℕ) : ℤ) * β ((k₀ + 2 * j : ℕ) : ℤ)) atTop (𝓝 0) := by
      have h1 := (tα k₀).comp (tendsto_add_atTop_nat 1)
      have h2 := (tβ k₀).comp (tendsto_add_atTop_nat 1)
      simpa using ((tα k₀).mul h2).sub (h1.mul (tβ k₀))
    simp only [hc] at ht
    have := tendsto_nhds_unique tendsto_const_nhds ht
    simpa using this
  have hzero : ∀ k₀ : ℕ, (∀ m : ℕ, (-1 : ℂ) ^ m * μ = 1 → ∃ j, m = k₀ + 2 * j) →
      ((α ((k₀ : ℕ) : ℤ) = 0 ∧ α ((k₀ + 2 : ℕ) : ℤ) = 0) → F = 0) ∧
      ((β ((k₀ : ℕ) : ℤ) = 0 ∧ β ((k₀ + 2 : ℕ) : ℤ) = 0) → G = 0) := by
    intro k₀ hk₀
    have hsign : ∀ m : ℕ, (-1 : ℂ) ^ m * μ = 1 ∨ (-1 : ℂ) ^ m * μ = -1 := by
      intro m
      rcases neg_one_pow_eq_or ℂ m with h | h <;> rcases hμ with rfl | rfl <;> simp [h]
    constructor
    · rintro ⟨h0, h1⟩
      have hall := p2f_chain_zero hq (x := fun j => α ((k₀ + 2 * j : ℕ) : ℤ))
        (b := fun j => a - (((k₀ + 2 * (j + 1) : ℕ) : ℤ) : ℂ) ^ 2) (hx k₀)
        (by simpa using h0) (by simpa using h1)
      have hm : ∀ m : ℕ, α m = 0 := by
        intro m
        rcases hsign m with h | h
        · obtain ⟨j, rfl⟩ := hk₀ m h
          exact_mod_cast hall j
        · exact (hwrong m h).1
      funext z
      have := p1a2_hasSum_cos hF.differentiable hF2 hFe z
      have e : ∀ m : ℕ, (∫ x in (0 : ℝ)..2 * π, F x * Complex.cos (m * x)) = 0 := fun m => by
        simpa [α] using hm m
      simp only [e, mul_zero, zero_mul] at this
      exact this.unique hasSum_zero
    · rintro ⟨h0, h1⟩
      have hall := p2f_chain_zero hq (x := fun j => β ((k₀ + 2 * j : ℕ) : ℤ))
        (b := fun j => a - (((k₀ + 2 * (j + 1) : ℕ) : ℤ) : ℂ) ^ 2) (hy k₀)
        (by simpa using h0) (by simpa using h1)
      have hm : ∀ m : ℕ, β m = 0 := by
        intro m
        rcases hsign m with h | h
        · obtain ⟨j, rfl⟩ := hk₀ m h
          exact_mod_cast hall j
        · exact (hwrong m h).2
      funext z
      have := p1a2_hasSum_sin hG.differentiable hG2 hGo z
      have e : ∀ m : ℕ, (∫ x in (0 : ℝ)..2 * π, G x * Complex.sin (m * x)) = 0 := fun m => by
        simpa [β] using hm m
      simp only [e, mul_zero, zero_mul] at this
      exact this.unique hasSum_zero
  rcases hμ with rfl | rfl
  · -- `π`-periodic case: the even chain
    obtain ⟨hzF, hzG⟩ := hzero 0 (fun m hm => by
      rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
      · exact ⟨j, by ring⟩
      · simp [pow_succ, pow_mul] at hm; norm_num at hm)
    have hD0 := hD 0
    simp only [Nat.cast_zero, zero_add, Nat.cast_ofNat, β0, mul_zero, sub_zero] at hD0
    rcases mul_eq_zero.1 hD0 with h | h
    · left
      refine hzF ⟨by simpa using h, ?_⟩
      have h0 := recα 0
      rw [show (0 : ℤ) - 2 = -2 by ring, zero_add, αneg, h] at h0
      simp only [Int.cast_zero] at h0
      have : q * (2 * α 2) = 0 := by linear_combination -h0
      simpa [hq] using this
    · right
      exact hzG ⟨by simpa using β0, by simpa using h⟩
  · -- `π`-antiperiodic case: the odd chain
    obtain ⟨hzF, hzG⟩ := hzero 1 (fun m hm => by
      rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
      · simp [pow_mul] at hm; norm_num at hm
      · exact ⟨j, by ring⟩)
    have hD1 := hD 1
    have hα1 := recα 1
    have hβ1 := recβ 1
    rw [show (1 : ℤ) - 2 = -1 by ring, αneg] at hα1
    rw [show (1 : ℤ) - 2 = -1 by ring, βneg] at hβ1
    norm_num at hD1 hα1 hβ1
    have h2 : q * (2 * (α 1 * β 1)) = 0 := by
      linear_combination q * hD1 - β 1 * hα1 + α 1 * hβ1
    rcases mul_eq_zero.1 ((mul_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left hq)).resolve_left
      two_ne_zero) with h | h
    · left
      refine hzF ⟨by simpa using h, ?_⟩
      have : q * α 3 = 0 := by linear_combination -hα1 + (a - 1 - q) * h
      simpa [hq] using this
    · right
      refine hzG ⟨by simpa using h, ?_⟩
      have : q * β 3 = 0 := by linear_combination -hβ1 + (a - 1 + q) * h
      simpa [hq] using this

/-- **Theorem of Ince** (DLMF §28.2(iv)): for `q ≠ 0` the Floquet solution with respect to a
given `ν` is unique up to a constant factor. -/
@[dlmf 28.2.iv]
theorem IsFloquetSolution.unique {a q ν : ℂ} (hq : q ≠ 0) {w v : ℂ → ℂ}
    (hw : IsFloquetSolution a q ν w) (hv : IsFloquetSolution a q ν v) :
    ∃ c : ℂ, v = fun z => c * w z := by
  obtain ⟨hws, hw0, hwf⟩ := hw
  obtain ⟨hvs, -, hvf⟩ := hv
  set μ := Complex.exp (π * I * ν)
  have ew := hws.eq_combination
  have ev := hvs.eq_combination
  set w0 := w 0
  set w1 := deriv w 0
  set v0 := v 0
  set v1 := deriv v 0
  by_cases hdet : w0 * v1 - w1 * v0 = 0
  · by_cases h0 : w0 = 0
    · have h1 : w1 ≠ 0 := by
        intro h1
        apply hw0
        rw [ew]; funext z; simp [h0, h1]
      have hv0 : v0 = 0 := by
        rw [h0, zero_mul, zero_sub, neg_eq_zero] at hdet
        exact (mul_eq_zero.1 hdet).resolve_left h1
      refine ⟨v1 / w1, ?_⟩
      rw [ev]; funext z
      rw [congrFun ew z, h0, hv0]
      field_simp
      ring
    · refine ⟨v0 / w0, ?_⟩
      rw [ev]; funext z
      rw [congrFun ew z, div_mul_eq_mul_div, eq_div_iff h0]
      linear_combination (mathieuWII a q z) * hdet
  · exfalso
    have hI : ∀ z, mathieuWI a q z = (v1 * w z - w1 * v z) / (w0 * v1 - w1 * v0) := by
      intro z
      rw [eq_div_iff hdet, congrFun ew z, congrFun ev z]
      ring
    have hII : ∀ z, mathieuWII a q z = (w0 * v z - v0 * w z) / (w0 * v1 - w1 * v0) := by
      intro z
      rw [eq_div_iff hdet, congrFun ew z, congrFun ev z]
      ring
    have hIp : ∀ z, mathieuWI a q (z + π) = μ * mathieuWI a q z := by
      intro z; rw [hI, hI, hwf, hvf]; ring
    have hIIp : ∀ z, mathieuWII a q (z + π) = μ * mathieuWII a q z := by
      intro z; rw [hII, hII, hwf, hvf]; ring
    have hμ : μ * μ = 1 := by
      have h1 := hIp (-π)
      rw [neg_add_cancel, (mathieuWI_spec a q).2.1, mathieuWI_neg] at h1
      have h2 := hIp 0
      rw [zero_add, (mathieuWI_spec a q).2.1, mul_one] at h2
      rw [h2] at h1
      exact h1.symm
    have hμ' : μ = 1 ∨ μ = -1 := mul_self_eq_one_iff.1 hμ
    rcases p2f_ince_core hq hμ' (isMathieuSolution_mathieuWI a q)
      (isMathieuSolution_mathieuWII a q) (mathieuWI_neg a q) (mathieuWII_neg a q) hIp hIIp
      with h | h
    · have := (mathieuWI_spec a q).2.1
      rw [h] at this
      simp at this
    · have := (mathieuWII_spec a q).2.2
      rw [h] at this
      simp at this

/-- Integration by parts behind the Floquet recurrence 28.2.19. -/
theorem p2f_floquet_int_rec {a q ν : ℂ} {w : ℂ → ℂ} (hf : IsMathieuSolution a q w)
    (hfl : ∀ z, w (z + π) = Complex.exp (π * I * ν) * w z) (n : ℤ) :
    q * (∫ x in (0 : ℝ)..π, w x * Complex.exp (-(I * (ν + 2 * ((n + 1 : ℤ) : ℂ)) * x))) -
      (a - (ν + 2 * n) ^ 2) * (∫ x in (0 : ℝ)..π, w x * Complex.exp (-(I * (ν + 2 * n) * x))) +
      q * (∫ x in (0 : ℝ)..π, w x * Complex.exp (-(I * (ν + 2 * ((n - 1 : ℤ) : ℂ)) * x))) =
      0 := by
  set μ : ℂ := ν + 2 * n with hμ
  let E : ℝ → ℂ := fun x => Complex.exp (-(I * μ * x))
  let g : ℝ → ℂ := fun x => deriv w x * E x + I * μ * w x * E x
  have hE : ∀ x : ℝ, HasDerivAt E (-(I * μ) * E x) x := by
    intro x
    have hl : HasDerivAt (fun x : ℝ => -(I * μ) * (x : ℂ)) (-(I * μ)) x := by
      simpa using ((hasDerivAt_id (x : ℂ)).const_mul (-(I * μ))).comp_ofReal
    have := (Complex.hasDerivAt_exp _).comp x hl
    convert this using 1
    · funext y; simp only [E, Function.comp_apply]; ring_nf
    · simp only [E]; ring_nf
  have hg : ∀ x : ℝ, HasDerivAt g
      ((2 * q * Complex.cos (2 * x) - a + μ ^ 2) * (w x * E x)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => deriv w x)
        ((2 * q * Complex.cos (2 * x) - a) * w x) x := (hf.hasDerivAt_deriv x).comp_ofReal
    have h0 : HasDerivAt (fun x : ℝ => w x) (deriv w x) x :=
      (hf.differentiable x).hasDerivAt.comp_ofReal
    convert (h1.mul (hE x)).add (((h0.const_mul (I * μ))).mul (hE x)) using 1
    ring_nf
    rw [I_sq]
    ring
  have hcont : Continuous fun x : ℝ =>
      (2 * q * Complex.cos (2 * x) - a + μ ^ 2) * (w x * E x) := by
    have := hf.differentiable.continuous
    fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := π)
    (fun x _ => hg x) (hcont.intervalIntegrable _ _)
  have hwd : deriv w π = Complex.exp (π * I * ν) * deriv w 0 := by
    have h := congrArg (fun f => deriv f 0) (funext hfl)
    rw [deriv_comp_add_const, zero_add] at h
    rw [h, deriv_const_mul _ (hf.differentiable 0)]
  have hw0 : w π = Complex.exp (π * I * ν) * w 0 := by simpa using hfl 0
  have hEπ : E π * Complex.exp (π * I * ν) = 1 := by
    simp only [E, ← Complex.exp_add]
    rw [show -(I * μ * ((π : ℝ) : ℂ)) + π * I * ν = (-n : ℤ) * (2 * π * I) by
      rw [hμ]; push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  have h0 : ∫ x in (0 : ℝ)..π, (2 * q * Complex.cos (2 * x) - a + μ ^ 2) * (w x * E x) = 0 := by
    rw [hint]
    simp only [g]
    rw [hwd, hw0]
    simp only [E, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one]
    linear_combination (deriv w 0 + I * μ * w 0) * hEπ
  have hpt : ∀ x : ℝ, (2 * q * Complex.cos (2 * x) - a + μ ^ 2) * (w x * E x) =
      q * (w x * Complex.exp (-(I * (ν + 2 * ((n + 1 : ℤ) : ℂ)) * x))) +
        q * (w x * Complex.exp (-(I * (ν + 2 * ((n - 1 : ℤ) : ℂ)) * x))) +
        (μ ^ 2 - a) * (w x * E x) := by
    intro x
    have e1 : Complex.exp (-(I * (ν + 2 * ((n + 1 : ℤ) : ℂ)) * x)) =
        E x * Complex.exp (-(2 * x) * I) := by
      simp only [E, ← Complex.exp_add]; congr 1; rw [hμ]; push_cast; ring
    have e2 : Complex.exp (-(I * (ν + 2 * ((n - 1 : ℤ) : ℂ)) * x)) =
        E x * Complex.exp ((2 * x) * I) := by
      simp only [E, ← Complex.exp_add]; congr 1; rw [hμ]; push_cast; ring
    rw [e1, e2, Complex.cos]
    ring
  have hc : ∀ m : ℂ, Continuous fun x : ℝ => w x * Complex.exp (-(I * m * x)) := by
    intro m
    have := hf.differentiable.continuous
    fun_prop
  have hcE : Continuous fun x : ℝ => w x * E x := hc μ
  simp_rw [hpt] at h0
  rw [intervalIntegral.integral_add (((hc _).intervalIntegrable _ _).const_mul _ |>.add
      (((hc _).intervalIntegrable _ _).const_mul _)) ((hcE.intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_add (((hc _).intervalIntegrable _ _).const_mul _)
      (((hc _).intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h0
  linear_combination h0

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
  obtain ⟨hf, -, hfl⟩ := hw
  set U : ℂ → ℂ := fun z => Complex.exp (-(I * ν * (z / 2))) * w (z / 2) with hUdef
  have hU : Differentiable ℂ U := by
    have := hf.differentiable
    fun_prop
  have hUper : ∀ z, U (z + 2 * π) = U z := by
    intro z
    simp only [U]
    rw [show (z + 2 * π) / 2 = z / 2 + π by ring, hfl, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  set c : ℤ → ℂ := fun k => (1 / (2 * π) : ℂ) *
    ∫ x in (0 : ℝ)..2 * π, U x * Complex.exp (-(k * x * I)) with hc
  have hcJ : ∀ k : ℤ, c k = (1 / π : ℂ) *
      ∫ x in (0 : ℝ)..π, w x * Complex.exp (-(I * (ν + 2 * k) * x)) := by
    intro k
    have h := intervalIntegral.integral_comp_div (a := 0) (b := 2 * π)
      (fun s : ℝ => w s * Complex.exp (-(I * (ν + 2 * k) * s))) (two_ne_zero (α := ℝ))
    simp only [zero_div, show 2 * π / 2 = π by ring] at h
    simp only [c]
    rw [show (∫ x in (0 : ℝ)..2 * π, U x * Complex.exp (-(k * x * I))) =
        ∫ x in (0 : ℝ)..2 * π, w ((x / 2 : ℝ) : ℂ) *
          Complex.exp (-(I * (ν + 2 * k) * ((x / 2 : ℝ) : ℂ))) from ?_, h]
    · rw [real_smul]; push_cast; field_simp
    · congr 1; funext x
      simp only [U]; push_cast
      rw [mul_comm (Complex.exp _) (w _), mul_assoc, ← Complex.exp_add]
      congr 2; ring
  refine ⟨c, fun z => ?_, fun z => ?_, fun n => ?_⟩
  · obtain ⟨C, hC0, hC⟩ := p1a2_fourierInt_decay hU hUper (2 * |z.im| + 1)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      (p1a2_summable_exp_neg_abs.mul_left
        (‖(1 / (2 * π) : ℂ)‖ * C * Real.exp (-(ν * z).im)))
    rw [norm_mul, norm_mul, Complex.norm_exp]
    have h1 := hC k
    have hre : (I * (ν + 2 * k) * z).re = -(ν * z).im - 2 * k * z.im := by
      simp [mul_re, mul_im]; ring
    rw [hre]
    have h2 : -(ν * z).im - 2 * k * z.im ≤ -(ν * z).im + 2 * |(k : ℝ)| * |z.im| := by
      have := neg_abs_le ((k : ℝ) * z.im)
      rw [abs_mul] at this
      linarith
    calc ‖(1 / (2 * π) : ℂ)‖ * ‖∫ x in (0 : ℝ)..2 * π, U x * Complex.exp (-(k * x * I))‖ *
          Real.exp (-(ν * z).im - 2 * k * z.im)
        ≤ ‖(1 / (2 * π) : ℂ)‖ * (C * Real.exp (-((2 * |z.im| + 1) * |(k : ℝ)|))) *
          Real.exp (-(ν * z).im + 2 * |(k : ℝ)| * |z.im|) := by
          gcongr
          · push_cast at h1 ⊢; exact h1
      _ = _ := by
          rw [show -(ν * z).im + 2 * |(k : ℝ)| * |z.im| =
            -(ν * z).im + -|(k : ℝ)| + (2 * |z.im| + 1) * |(k : ℝ)| by ring,
            Real.exp_add, Real.exp_add]
          have e : Real.exp (-((2 * |z.im| + 1) * |(k : ℝ)|)) *
              Real.exp ((2 * |z.im| + 1) * |(k : ℝ)|) = 1 := by
            rw [← Real.exp_add]; simp
          linear_combination (‖(1 / (2 * π) : ℂ)‖ * C * Real.exp (-(ν * z).im) *
            Real.exp (-|(k : ℝ)|)) * e
  · have h := (p1a2_hasSum_fourier hU hUper (2 * z)).mul_left (Complex.exp (I * ν * z))
    have e : Complex.exp (I * ν * z) * U (2 * z) = w z := by
      simp only [U]
      rw [show 2 * z / 2 = z by ring, ← mul_assoc, ← Complex.exp_add]
      rw [show I * ν * z + -(I * ν * z) = 0 by ring, Complex.exp_zero, one_mul]
    rw [e] at h
    convert h using 2 with k
    simp only [c]
    rw [show I * (ν + 2 * k) * z = k * (2 * z) * I + I * ν * z by ring, Complex.exp_add]
    ring
  · rw [hcJ, hcJ, hcJ]
    have := p2f_floquet_int_rec hf hfl n
    push_cast at this ⊢
    linear_combination (1 / π : ℂ) * this

/-- A function on `ℤ` that is eventually (cofinitely) at most `1` is bounded above. -/
theorem p2f_bound_cofinite {f : ℤ → ℝ} (h : ∀ᶠ n in cofinite, f n ≤ 1) :
    ∃ C, 0 ≤ C ∧ ∀ n, f n ≤ C := by
  have hfin : {n | ¬ f n ≤ 1}.Finite := Filter.eventually_cofinite.1 h
  obtain ⟨M, hM⟩ := (hfin.image f).bddAbove
  refine ⟨max 1 M, by positivity, fun n => ?_⟩
  by_cases hn : f n ≤ 1
  · exact hn.trans (le_max_left _ _)
  · exact (hM ⟨n, hn, rfl⟩).trans (le_max_right _ _)

/-- Exponential decay of a sequence with `|c_n|^{1/|n|} → 0`. -/
theorem p2f_coeff_decay {c : ℤ → ℂ}
    (hlim : Tendsto (fun n : ℤ => ‖c n‖ ^ (1 / (|n| : ℝ))) cofinite (𝓝 0)) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ n, ‖c n‖ ≤ C * Real.exp (-(R * |(n : ℝ)|)) := by
  have h1 : ∀ᶠ n : ℤ in cofinite, ‖c n‖ ^ (1 / (|n| : ℝ)) < Real.exp (-R) :=
    hlim.eventually (gt_mem_nhds (Real.exp_pos _))
  have h2 : ∀ᶠ n : ℤ in cofinite, n ≠ 0 := Filter.eventually_cofinite_ne 0
  obtain ⟨C, hC0, hC⟩ := p2f_bound_cofinite (f := fun n => ‖c n‖ * Real.exp (R * |(n : ℝ)|))
    (by
      filter_upwards [h1, h2] with n hn hn0
      have hpos : (0 : ℝ) < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn0)
      have e : ‖c n‖ = (‖c n‖ ^ (1 / (|n| : ℝ))) ^ (|(n : ℝ)|) := by
        rw [← Real.rpow_mul (norm_nonneg _), one_div,
          inv_mul_cancel₀ hpos.ne', Real.rpow_one]
      have hle : ‖c n‖ ≤ Real.exp (-R) ^ (|(n : ℝ)|) := by
        rw [e]
        exact Real.rpow_le_rpow (by positivity) hn.le hpos.le
      rw [← Real.exp_mul] at hle
      calc ‖c n‖ * Real.exp (R * |(n : ℝ)|) ≤ Real.exp (-R * |(n : ℝ)|) *
            Real.exp (R * |(n : ℝ)|) := by gcongr
        _ = 1 := by rw [← Real.exp_add]; simp)
  refine ⟨C, hC0, fun n => ?_⟩
  have := hC n
  have hp := Real.exp_pos (R * |(n : ℝ)|)
  calc ‖c n‖ = ‖c n‖ * Real.exp (R * |(n : ℝ)|) * Real.exp (-(R * |(n : ℝ)|)) := by
        rw [mul_assoc, ← Real.exp_add]; simp
    _ ≤ C * Real.exp (-(R * |(n : ℝ)|)) := by gcongr

/-- `‖x‖^k ≤ e^{2‖x‖}` for `k ≤ 2`. -/
theorem p2f_norm_pow_le {x : ℂ} {k : ℕ} (hk : k ≤ 2) : ‖x ^ k‖ ≤ Real.exp (2 * ‖x‖) := by
  rw [norm_pow]
  have h1 : max 1 ‖x‖ ≤ Real.exp ‖x‖ := max_le (Real.one_le_exp (norm_nonneg _))
    ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _) |>.trans_eq' rfl)
  calc ‖x‖ ^ k ≤ (max 1 ‖x‖) ^ k := by gcongr; exact le_max_right _ _
    _ ≤ (max 1 ‖x‖) ^ 2 := pow_le_pow_right₀ (le_max_left _ _) hk
    _ ≤ Real.exp ‖x‖ ^ 2 := by gcongr
    _ = Real.exp (2 * ‖x‖) := by rw [← Real.exp_nat_mul]; norm_num

/-- Uniform bound for the terms `c_n (i(ν+2n))^k e^{i(ν+2n)z}`, `k ≤ 2`, `‖z‖ ≤ ρ`. -/
theorem p2f_floquet_term_bound {c : ℤ → ℂ}
    (hlim : Tendsto (fun n : ℤ => ‖c n‖ ^ (1 / (|n| : ℝ))) cofinite (𝓝 0)) (ν : ℂ) (ρ : ℝ) :
    ∃ u : ℤ → ℝ, Summable u ∧ ∀ (k : ℕ), k ≤ 2 → ∀ n (z : ℂ), ‖z‖ ≤ ρ →
      ‖c n * (I * (ν + 2 * n)) ^ k * Complex.exp (I * (ν + 2 * n) * z)‖ ≤ u n := by
  obtain ⟨C, hC0, hC⟩ := p2f_coeff_decay hlim (2 * (2 + ρ) + 1)
  refine ⟨fun n => C * Real.exp ((2 + ρ) * ‖ν‖) * Real.exp (-|(n : ℝ)|),
    p1a2_summable_exp_neg_abs.mul_left _, fun k hk n z hz => ?_⟩
  set X : ℝ := ‖ν‖ + 2 * |(n : ℝ)|
  have hX : ‖I * (ν + 2 * n)‖ ≤ X := by
    rw [norm_mul, Complex.norm_I, one_mul]
    refine (norm_add_le _ _).trans ?_
    simp [X]
  have hX0 : 0 ≤ X := by positivity
  rw [norm_mul, norm_mul, Complex.norm_exp]
  have e1 := p2f_norm_pow_le (x := I * (ν + 2 * n)) hk
  have e2 : (I * (ν + 2 * n) * z).re ≤ X * ρ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul]
    exact mul_le_mul hX hz (norm_nonneg _) hX0
  calc ‖c n‖ * ‖(I * (ν + 2 * n)) ^ k‖ * Real.exp (I * (ν + 2 * n) * z).re
      ≤ (C * Real.exp (-((2 * (2 + ρ) + 1) * |(n : ℝ)|))) * Real.exp (2 * X) *
          Real.exp (X * ρ) := by
        gcongr
        · exact hC n
        · exact e1.trans (Real.exp_le_exp.2 (by linarith))
    _ = _ := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        simp only
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        simp only [X]; ring

/-- **Converse** (DLMF 28.2.20): a nontrivial solution `c_{2n}` of the recurrence 28.2.19 with
`|c_{2n}|^{1/|n|} → 0` as `n → ±∞` yields a Floquet solution `∑ c_{2n} e^{i(ν+2n)z}`. -/
@[dlmf 28.2.E20]
theorem isFloquetSolution_of_recurrence {a q ν : ℂ} {c : ℤ → ℂ} (hc : c ≠ 0)
    (hrec : ∀ n : ℤ, q * c (n + 1) - (a - (ν + 2 * n) ^ 2) * c n + q * c (n - 1) = 0)
    (hlim : Tendsto (fun n : ℤ => ‖c n‖ ^ (1 / (|n| : ℝ))) (Filter.cofinite) (𝓝 0)) :
    IsFloquetSolution a q ν (fun z => ∑' n : ℤ, c n * Complex.exp (I * (ν + 2 * n) * z)) := by
  set g : ℕ → ℤ → ℂ → ℂ := fun k n z =>
    c n * (I * (ν + 2 * n)) ^ k * Complex.exp (I * (ν + 2 * n) * z) with hgdef
  have hsum : ∀ k, k ≤ 2 → ∀ z, Summable (fun n => g k n z) := by
    intro k hk z
    obtain ⟨u, hu, hb⟩ := p2f_floquet_term_bound hlim ν ‖z‖
    exact Summable.of_norm_bounded hu fun n => hb k hk n z le_rfl
  have hder : ∀ k, k ≤ 1 → ∀ y,
      HasDerivAt (fun z => ∑' n, g k n z) (∑' n, g (k + 1) n y) y := by
    intro k hk y
    obtain ⟨u, hu, hb⟩ := p2f_floquet_term_bound hlim ν (‖y‖ + 1)
    refine hasDerivAt_tsum_of_isPreconnected (t := Metric.ball 0 (‖y‖ + 1)) (y₀ := 0) hu
      Metric.isOpen_ball (convex_ball _ _).isPreconnected (fun n z _ => ?_)
      (fun n z hz => hb (k + 1) (by omega) n z (by simpa using (mem_ball_zero_iff.1 hz).le))
      (by simp; positivity) (hsum k (by omega) 0) (by simp)
    have := ((hasDerivAt_id z).const_mul (I * (ν + 2 * n))).cexp.const_mul
      (c n * (I * (ν + 2 * n)) ^ k)
    simp only [hgdef]
    convert this using 1
    · funext x; simp
    · simp; ring
  set w : ℂ → ℂ := fun z => ∑' n, g 0 n z with hwdef
  have hwe : (fun z => ∑' n : ℤ, c n * Complex.exp (I * (ν + 2 * n) * z)) = w := by
    funext z; simp [w, g]
  rw [hwe]
  have hdw : deriv w = fun z => ∑' n, g 1 n z := funext fun z => (hder 0 (by norm_num) z).deriv
  have hdiff : Differentiable ℂ w := fun z => (hder 0 (by norm_num) z).differentiableAt
  -- the differential equation
  have hode : ∀ z, ∑' n, g 2 n z = (2 * q * Complex.cos (2 * z) - a) * w z := by
    intro z
    set e : ℤ → ℂ := fun n => Complex.exp (I * (ν + 2 * n) * z)
    have S0 : HasSum (fun n => c n * e n) (w z) := by
      have := (hsum 0 (by norm_num) z).hasSum
      simpa [g, e, w] using this
    have Sp : HasSum (fun n => c (n + 1) * e n) (Complex.exp (-(2 * z) * I) * w z) := by
      have h := S0.mul_left (Complex.exp (-(2 * z) * I))
      have h' := (Equiv.addRight (1 : ℤ)).hasSum_iff.2 h
      convert h' using 1
      funext n
      simp only [Function.comp_apply, Equiv.coe_addRight, e]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2; push_cast; ring
    have Sm : HasSum (fun n => c (n - 1) * e n) (Complex.exp ((2 * z) * I) * w z) := by
      have h := S0.mul_left (Complex.exp ((2 * z) * I))
      have h' := (Equiv.subRight (1 : ℤ)).hasSum_iff.2 h
      convert h' using 1
      funext n
      simp only [Function.comp_apply, Equiv.subRight_apply, e]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2; push_cast; ring
    have S2 : HasSum (fun n => g 2 n z) (q * (Complex.exp (-(2 * z) * I) * w z) +
        q * (Complex.exp ((2 * z) * I) * w z) - a * w z) := by
      have := ((Sp.mul_left q).add (Sm.mul_left q)).sub (S0.mul_left a)
      convert this using 1
      funext n
      simp only [g, e]
      have hr := hrec n
      have hI : (I * (ν + 2 * n)) ^ 2 = -(ν + 2 * n) ^ 2 := by rw [mul_pow, I_sq]; ring
      rw [hI]
      linear_combination (-Complex.exp (I * (ν + 2 * n) * z)) * hr
    rw [S2.tsum_eq, Complex.cos]
    ring
  refine ⟨⟨hdiff, fun z => ?_⟩, ?_, fun z => ?_⟩
  · rw [hdw, ← hode]
    exact hder 1 le_rfl z
  · -- nontriviality: the coefficients are recovered by integration over `[0, π]`
    intro hw0
    obtain ⟨m, hm⟩ := Function.ne_iff.1 hc
    obtain ⟨C, hC0, hC⟩ := p2f_coeff_decay hlim 1
    have hcs : Summable fun n => ‖c n‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hC
        (p1a2_summable_exp_neg_abs.mul_left C |>.congr fun n => by simp)
    have hlimt : ∀ t : ℝ, HasSum (fun n => c n * Complex.exp (2 * I * (n - m) * t)) 0 := by
      intro t
      have h0 : HasSum (fun n => g 0 n t) 0 := by
        have := (hsum 0 (by norm_num) t).hasSum
        rwa [show (∑' n, g 0 n t) = w t from rfl, hw0] at this
      have := h0.mul_left (Complex.exp (-(I * (ν + 2 * m) * t)))
      rw [mul_zero] at this
      convert this using 1
      funext n
      simp only [g, pow_zero, mul_one]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2; ring
    have hint := intervalIntegral.hasSum_integral_of_dominated_convergence (a := 0) (b := π)
      (μ := MeasureTheory.volume) (F := fun n (t : ℝ) => c n * Complex.exp (2 * I * (n - m) * t))
      (f := fun _ => 0) (fun n _ => ‖c n‖)
      (fun n => (by fun_prop : Continuous fun t : ℝ =>
        c n * Complex.exp (2 * I * (n - m) * t)).aestronglyMeasurable)
      (fun n => MeasureTheory.ae_of_all _ fun t _ => by
        rw [norm_mul, Complex.norm_exp]
        simp [mul_re, mul_im])
      (MeasureTheory.ae_of_all _ fun t _ => hcs) intervalIntegrable_const
      (MeasureTheory.ae_of_all _ fun t _ => hlimt t)
    simp only [intervalIntegral.integral_zero] at hint
    have hval : ∀ n : ℤ, (∫ t in (0 : ℝ)..π, c n * Complex.exp (2 * I * (n - m) * t)) =
        if n = m then c m * π else 0 := by
      intro n
      rw [intervalIntegral.integral_const_mul]
      split_ifs with hnm
      · subst hnm; simp [mul_comm]
      · have hne : 2 * I * ((n : ℂ) - m) ≠ 0 := by
          refine mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (sub_ne_zero.2 ?_)
          exact_mod_cast hnm
        rw [integral_exp_mul_complex hne]
        have : Complex.exp (2 * I * ((n : ℂ) - m) * (π : ℝ)) = 1 := by
          rw [show 2 * I * ((n : ℂ) - m) * ((π : ℝ) : ℂ) = ((n - m : ℤ) : ℂ) * (2 * π * I) by
            push_cast; ring]
          exact Complex.exp_int_mul_two_pi_mul_I _
        simp [this]
    simp only [hval] at hint
    have := hint.unique (hasSum_ite_eq m (c m * π))
    exact hm (by
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simpa [hπ] using this.symm)
  · simp only [w, g, pow_zero, mul_one]
    rw [← tsum_mul_left]
    congr 1; funext n
    rw [show I * (ν + 2 * n) * (z + π) = (π * I * ν + I * (ν + 2 * n) * z) +
      (n : ℂ) * (2 * π * I) by ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
      Complex.exp_add]
    ring

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

/-! ### Discreteness of the spectra -/

/-- An entire function that does not vanish at some real point has finitely many real zeros in
every compact interval. -/
theorem p1a1_finite_real_zeros {g : ℂ → ℂ} (hg : Differentiable ℂ g) {y : ℝ} (hy : g y ≠ 0)
    (s t : ℝ) : {x : ℝ | x ∈ Icc s t ∧ g x = 0}.Finite := by
  by_contra hinf
  obtain ⟨x, -, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf isCompact_Icc
    (fun x hx => hx.1)
  rw [accPt_iff_frequently_nhdsNE] at hx
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] x) (𝓝[≠] (x : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (Complex.continuous_ofReal.tendsto x).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact fun h => hz (Complex.ofReal_injective h)
  have hfr : ∃ᶠ z in 𝓝[≠] (x : ℂ), g z = 0 :=
    ht.frequently (hx.mono fun z hz => hz.2)
  have := AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (fun z _ => hg.analyticAt z) isPreconnected_univ (mem_univ (x : ℂ)) hfr (mem_univ (y : ℂ))
  exact hy this

/-- A set of zeros of such a function, bounded below, has finitely many elements below any `a`. -/
theorem p1a1_spec_finite {S : Set ℝ} {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hSg : ∀ x ∈ S, g x = 0) {x₀ : ℝ} (hx₀ : ∀ y ∈ S, x₀ ≤ y) {y : ℝ} (hy : g y ≠ 0) (a : ℝ) :
    (S ∩ Iio a).Finite :=
  (p1a1_finite_real_zeros hg hy x₀ a).subset fun x hx =>
    ⟨⟨hx₀ x hx.1, (Set.mem_Iio.mp hx.2).le⟩, hSg x hx.1⟩

/-- An element of `S` with finitely many smaller elements is some `nthLeast S k`. -/
theorem p1a1_exists_eq_nthLeast {S : Set ℝ} {a : ℝ} (ha : a ∈ S) (hfin : (S ∩ Iio a).Finite) :
    ∃ k : ℕ, a = nthLeast S k :=
  ⟨(S ∩ Iio a).ncard, (nthLeast_eq_of ha hfin.cast_ncard_eq.symm).symm⟩

/-- The least element of a spectrum. -/
theorem p1a1_le_of_encard_zero {S : Set ℝ} {x₀ : ℝ} (h : (S ∩ Iio x₀).encard = (0 : ℕ)) :
    ∀ y ∈ S, x₀ ≤ y := by
  intro y hy
  by_contra hlt
  rw [not_le] at hlt
  have : (S ∩ Iio x₀) = ∅ := by exact_mod_cast Set.encard_eq_zero.mp (by exact_mod_cast h)
  exact (Set.eq_empty_iff_forall_notMem.mp this) y ⟨hy, hlt⟩

/-- `a ↦ w_I(z; a, q)` and `a ↦ w_II(z; a, q)` are entire (from 28.2(ii)). -/
theorem p1a1_differentiable_param (z q : ℂ) :
    Differentiable ℂ (fun a => mathieuWI a q z) ∧ Differentiable ℂ (fun a => mathieuWII a q z) := by
  have hl : Differentiable ℂ (fun a : ℂ => (z, a, q)) := by fun_prop
  exact ⟨differentiable_mathieuWI_mathieuWII.1.comp hl,
    differentiable_mathieuWI_mathieuWII.2.comp hl⟩

/-- A spectrum with an element having no smaller elements is bounded below. -/
theorem p1a1_least (S : Set ℝ) (h : ∃ x ∈ S, (S ∩ Iio x).encard = (0 : ℕ)) :
    ∃ x₀, ∀ y ∈ S, x₀ ≤ y := by
  obtain ⟨x, -, hx⟩ := h; exact ⟨x, p1a1_le_of_encard_zero hx⟩

/-- **Table 28.2.1** (`ν̂ = 0`, `w'(0) = w'(π/2) = 0`): for real `q` the even `π`-periodic
solutions occur exactly for `a = a_{2n}(q)`: a nontrivial solution with `w'(0) = w'(π/2) = 0`
exists iff `a = a_{2n}(q)` for some `n`. -/
@[dlmf 28.2.T1]
theorem exists_solution_neumann_iff (a q : ℝ) :
    (∃ w, IsMathieuSolution a q w ∧ w ≠ 0 ∧ deriv w 0 = 0 ∧ deriv w (π / 2) = 0) ↔
      ∃ n : ℕ, a = mathieuA (2 * n) q := by
  constructor
  · rintro ⟨w, hw, hne, h0, h1⟩
    have hw0 : w 0 ≠ 0 := by
      intro h; apply hne; rw [hw.eq_combination]; funext z; simp [h, h0]
    have hA' : deriv (mathieuWI a q) (π / 2) = 0 := by
      have := hw.p1a1_deriv_eq (π / 2)
      rw [h0, zero_mul, add_zero, h1] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hw0
    set S := mathieuSpecA 0 q
    have hS : ∀ k, mathieuSpecA (2 * k) q = S := by
      intro k; simp [S, mathieuSpecA]
    have haS : a ∈ S := by simpa [S, mathieuSpecA] using hA'
    obtain ⟨x₀, hx₀⟩ := p1a1_least S (mathieuSpecA_exists 0 q 0)
    obtain ⟨y₀, hy₀⟩ := p1a1_least (mathieuSpecB 2 q) (mathieuSpecB_exists 2 q 0)
    have hfin : (S ∩ Iio a).Finite := by
      refine p1a1_spec_finite (g := fun b => mathieuWI b q π - 1)
        ((p1a1_differentiable_param _ _).1.sub_const 1) (fun x hx => ?_) hx₀
        (y := min x₀ y₀ - 1) ?_ a
      · have : deriv (mathieuWI x q) (π / 2) = 0 := by simpa [S, mathieuSpecA] using hx
        simp only [mathieuWI_pi_sub_one, this]; ring
      · intro h0
        simp only [mathieuWI_pi_sub_one] at h0
        rcases mul_eq_zero.mp h0 with h | h
        · rcases mul_eq_zero.mp h with h | h
          · norm_num at h
          · have := hx₀ (min x₀ y₀ - 1) (by
              simp only [S, mathieuSpecA, Even.zero, ↓reduceIte, Set.mem_ofPred_eq]; exact h)
            linarith [min_le_left x₀ y₀]
        · have := hy₀ (min x₀ y₀ - 1) (by
            simp only [mathieuSpecB, even_two, ↓reduceIte, Set.mem_ofPred_eq]; exact h)
          linarith [min_le_right x₀ y₀]
    obtain ⟨k, hk⟩ := p1a1_exists_eq_nthLeast haS hfin
    refine ⟨k, ?_⟩
    rw [hk, mathieuA, hS, show 2 * k / 2 = k by omega]
  · rintro ⟨n, rfl⟩
    obtain ⟨h1, h10, h11⟩ := mathieuWI_spec (mathieuA (2 * n) q : ℂ) q
    exact ⟨_, h1, fun h => by simpa [h10] using congrFun h 0, h11,
      deriv_mathieuWI_half_pi_mathieuA_even n q⟩

/-- **Table 28.2.1** (`ν̂ = 1`, `w'(0) = w(π/2) = 0`): exactly for `a = a_{2n+1}(q)`. -/
@[dlmf 28.2.T1]
theorem exists_solution_neumann_dirichlet_iff (a q : ℝ) :
    (∃ w, IsMathieuSolution a q w ∧ w ≠ 0 ∧ deriv w 0 = 0 ∧ w (π / 2) = 0) ↔
      ∃ n : ℕ, a = mathieuA (2 * n + 1) q := by
  constructor
  · rintro ⟨w, hw, hne, h0, h1⟩
    have hw0 : w 0 ≠ 0 := by
      intro h; apply hne; rw [hw.eq_combination]; funext z; simp [h, h0]
    have hA : mathieuWI a q (π / 2) = 0 := by
      have := congrFun hw.eq_combination (π / 2)
      rw [h0, zero_mul, add_zero, h1] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hw0
    set S := mathieuSpecA 1 q
    have hS : ∀ k, mathieuSpecA (2 * k + 1) q = S := by
      intro k; simp [S, mathieuSpecA, Nat.not_even_bit1]
    have hmem : ∀ x : ℝ, x ∈ S ↔ mathieuWI x q (π / 2) = 0 := by
      intro x; simp only [S, mathieuSpecA, Nat.not_even_one, ↓reduceIte, Set.mem_ofPred_eq]
    obtain ⟨x₀, hx₀⟩ := p1a1_least S (mathieuSpecA_exists 1 q 0)
    have hfin : (S ∩ Iio a).Finite := by
      refine p1a1_spec_finite (g := fun b => mathieuWI b q (π / 2))
        (p1a1_differentiable_param _ _).1 (fun x hx => (hmem x).mp hx) hx₀
        (y := x₀ - 1) (fun h0 => ?_) a
      have := hx₀ _ ((hmem _).mpr h0); linarith
    obtain ⟨k, hk⟩ := p1a1_exists_eq_nthLeast ((hmem a).mpr hA) hfin
    refine ⟨k, ?_⟩
    rw [hk, mathieuA, hS, show (2 * k + 1) / 2 = k by omega]
  · rintro ⟨n, rfl⟩
    obtain ⟨h1, h10, h11⟩ := mathieuWI_spec (mathieuA (2 * n + 1) q : ℂ) q
    exact ⟨_, h1, fun h => by simpa [h10] using congrFun h 0, h11,
      mathieuWI_half_pi_mathieuA_odd n q⟩

/-- **Table 28.2.1** (`ν̂ = 1`, `w(0) = w'(π/2) = 0`): exactly for `a = b_{2n+1}(q)`. -/
@[dlmf 28.2.T1]
theorem exists_solution_dirichlet_neumann_iff (a q : ℝ) :
    (∃ w, IsMathieuSolution a q w ∧ w ≠ 0 ∧ w 0 = 0 ∧ deriv w (π / 2) = 0) ↔
      ∃ n : ℕ, a = mathieuB (2 * n + 1) q := by
  constructor
  · rintro ⟨w, hw, hne, h0, h1⟩
    have hw0 : deriv w 0 ≠ 0 := by
      intro h; apply hne; rw [hw.eq_combination]; funext z; simp [h, h0]
    have hB' : deriv (mathieuWII a q) (π / 2) = 0 := by
      have := hw.p1a1_deriv_eq (π / 2)
      rw [h0, zero_mul, zero_add, h1] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hw0
    set S := mathieuSpecB 1 q
    have hS : ∀ k, mathieuSpecB (2 * k + 1) q = S := by
      intro k; simp [S, mathieuSpecB, Nat.not_even_bit1]
    have hmem : ∀ x : ℝ, x ∈ S ↔ deriv (mathieuWII x q) (π / 2) = 0 := by
      intro x; simp only [S, mathieuSpecB, Nat.not_even_one, ↓reduceIte, Set.mem_ofPred_eq]
    have hmemA : ∀ x : ℝ, x ∈ mathieuSpecA 1 q ↔ mathieuWI x q (π / 2) = 0 := by
      intro x; simp only [mathieuSpecA, Nat.not_even_one, ↓reduceIte, Set.mem_ofPred_eq]
    obtain ⟨x₀, hx₀⟩ := p1a1_least S (mathieuSpecB_exists 1 q 0)
    obtain ⟨y₀, hy₀⟩ := p1a1_least (mathieuSpecA 1 q) (mathieuSpecA_exists 1 q 0)
    have hfin : (S ∩ Iio a).Finite := by
      refine p1a1_spec_finite (g := fun b => mathieuWI b q π + 1)
        ((p1a1_differentiable_param _ _).1.add_const 1) (fun x hx => ?_) hx₀
        (y := min x₀ y₀ - 1) ?_ a
      · simp only [mathieuWI_pi_add_one, (hmem x).mp hx]; ring
      · intro h0
        simp only [mathieuWI_pi_add_one] at h0
        rcases mul_eq_zero.mp h0 with h | h
        · rcases mul_eq_zero.mp h with h | h
          · norm_num at h
          · have := hy₀ _ ((hmemA _).mpr h)
            linarith [min_le_right x₀ y₀]
        · have := hx₀ _ ((hmem _).mpr h)
          linarith [min_le_left x₀ y₀]
    obtain ⟨k, hk⟩ := p1a1_exists_eq_nthLeast ((hmem a).mpr hB') hfin
    refine ⟨k, ?_⟩
    rw [hk]; simp only [mathieuB, show 2 * k + 1 ≠ 0 by omega, ↓reduceIte]
    rw [hS, show (2 * k + 1 - 1) / 2 = k by omega]
  · rintro ⟨n, rfl⟩
    obtain ⟨h1, h10, h11⟩ := mathieuWII_spec (mathieuB (2 * n + 1) q : ℂ) q
    exact ⟨_, h1, fun h => by
      have := congrArg (fun f => deriv f 0) h; simp [h11] at this, h10,
      deriv_mathieuWII_half_pi_mathieuB_odd n q⟩

/-- **Table 28.2.1** (`ν̂ = 0`, `w(0) = w(π/2) = 0`): exactly for `a = b_{2n+2}(q)`. -/
@[dlmf 28.2.T1]
theorem exists_solution_dirichlet_iff (a q : ℝ) :
    (∃ w, IsMathieuSolution a q w ∧ w ≠ 0 ∧ w 0 = 0 ∧ w (π / 2) = 0) ↔
      ∃ n : ℕ, a = mathieuB (2 * n + 2) q := by
  constructor
  · rintro ⟨w, hw, hne, h0, h1⟩
    have hw0 : deriv w 0 ≠ 0 := by
      intro h; apply hne; rw [hw.eq_combination]; funext z; simp [h, h0]
    have hB : mathieuWII a q (π / 2) = 0 := by
      have := congrFun hw.eq_combination (π / 2)
      rw [h0, zero_mul, zero_add, h1] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hw0
    set S := mathieuSpecB 2 q
    have hS : ∀ k, mathieuSpecB (2 * k + 2) q = S := by
      intro k
      have : Even (2 * k + 2) := ⟨k + 1, by ring⟩
      simp [S, mathieuSpecB, this]
    have hmem : ∀ x : ℝ, x ∈ S ↔ mathieuWII x q (π / 2) = 0 := by
      intro x; simp only [S, mathieuSpecB, even_two, ↓reduceIte, Set.mem_ofPred_eq]
    obtain ⟨x₀, hx₀⟩ := p1a1_least S (mathieuSpecB_exists 2 q 0)
    have hfin : (S ∩ Iio a).Finite := by
      refine p1a1_spec_finite (g := fun b => mathieuWII b q (π / 2))
        (p1a1_differentiable_param _ _).2 (fun x hx => (hmem x).mp hx) hx₀
        (y := x₀ - 1) (fun h0 => ?_) a
      have := hx₀ _ ((hmem _).mpr h0); linarith
    obtain ⟨k, hk⟩ := p1a1_exists_eq_nthLeast ((hmem a).mpr hB) hfin
    refine ⟨k, ?_⟩
    rw [hk]; simp only [mathieuB, show 2 * k + 2 ≠ 0 by omega, ↓reduceIte]
    rw [hS, show (2 * k + 2 - 1) / 2 = k by omega]
  · rintro ⟨n, rfl⟩
    obtain ⟨h1, h10, h11⟩ := mathieuWII_spec (mathieuB (2 * n + 2) q : ℂ) q
    exact ⟨_, h1, fun h => by
      have := congrArg (fun f => deriv f 0) h; simp [h11] at this, h10,
      mathieuWII_half_pi_mathieuB_even n q⟩

/-- The `(k+1)`-st smallest element exceeds the `k`-th. -/
theorem p1a1_nthLeast_lt {S : Set ℝ} {k : ℕ} (hk : ∃ x ∈ S, (S ∩ Iio x).encard = k)
    (hk1 : ∃ x ∈ S, (S ∩ Iio x).encard = (k + 1 : ℕ)) : nthLeast S k < nthLeast S (k + 1) := by
  obtain ⟨-, hx⟩ := nthLeast_spec hk
  obtain ⟨-, hy⟩ := nthLeast_spec hk1
  by_contra hle
  rw [not_lt] at hle
  have h := Set.encard_le_encard (inter_subset_inter_right S (Iio_subset_Iio hle))
  rw [hx, hy] at h
  have : ((k + 1 : ℕ) : ℕ∞) ≤ k := h
  norm_cast at this
  omega

/-- **Monotone ordering** within each spectrum (DLMF §28.2(v)): `a_{2n} < a_{2n+2}`,
`a_{2n+1} < a_{2n+3}`, `b_{2n+1} < b_{2n+3}`, `b_{2n+2} < b_{2n+4}` (real `q`). -/
@[dlmf 28.2.v]
theorem mathieuA_lt_mathieuA_add_two (n : ℕ) (q : ℝ) : mathieuA n q < mathieuA (n + 2) q := by
  have hS : mathieuSpecA (n + 2) q = mathieuSpecA n q := by
    simp [mathieuSpecA, Nat.even_add]
  simp only [mathieuA, hS, show (n + 2) / 2 = n / 2 + 1 by omega]
  exact p1a1_nthLeast_lt (mathieuSpecA_exists n q _) (mathieuSpecA_exists n q _)

/-- Monotone ordering within each spectrum of the `b_n` (DLMF §28.2(v)), `n ≥ 1`. -/
@[dlmf 28.2.v]
theorem mathieuB_lt_mathieuB_add_two {n : ℕ} (hn : n ≠ 0) (q : ℝ) :
    mathieuB n q < mathieuB (n + 2) q := by
  have hS : mathieuSpecB (n + 2) q = mathieuSpecB n q := by
    simp [mathieuSpecB, Nat.even_add]
  simp only [mathieuB, hn, show n + 2 ≠ 0 by omega, ite_false, hS,
    show (n + 2 - 1) / 2 = (n - 1) / 2 + 1 by omega]
  exact p1a1_nthLeast_lt (mathieuSpecB_exists n q _) (mathieuSpecB_exists n q _)

/-- The eigenvalues `a_n(q)` are pairwise distinct. -/
theorem p1a1_mathieuA_injective (q : ℝ) : Function.Injective fun n => mathieuA n q := by
  intro m n hmn
  simp only at hmn
  have hW := mathieuWI_wronskian (mathieuA m q) q (π / 2)
  obtain ⟨hm1, hm2⟩ := mathieuA_spec m q
  obtain ⟨hn1, hn2⟩ := mathieuA_spec n q
  rcases Nat.even_or_odd m with hm | hm <;> rcases Nat.even_or_odd n with hn | hn
  · have hS : mathieuSpecA m q = mathieuSpecA n q := by simp [mathieuSpecA, hm, hn]
    rw [hS, hmn, hn2] at hm2
    have : (n / 2 : ℕ) = m / 2 := by exact_mod_cast hm2
    obtain ⟨i, rfl⟩ := hm; obtain ⟨j, rfl⟩ := hn; omega
  · simp only [mathieuSpecA, hm, ↓reduceIte, Set.mem_ofPred_eq] at hm1
    simp only [mathieuSpecA, Nat.not_even_iff_odd.mpr hn, ↓reduceIte, Set.mem_ofPred_eq] at hn1
    rw [← hmn] at hn1
    rw [hm1, hn1] at hW; simp at hW
  · simp only [mathieuSpecA, Nat.not_even_iff_odd.mpr hm, ↓reduceIte, Set.mem_ofPred_eq] at hm1
    simp only [mathieuSpecA, hn, ↓reduceIte, Set.mem_ofPred_eq] at hn1
    rw [← hmn] at hn1
    rw [hm1, hn1] at hW; simp at hW
  · have hS : mathieuSpecA m q = mathieuSpecA n q := by
      simp [mathieuSpecA, Nat.not_even_iff_odd.mpr hm, Nat.not_even_iff_odd.mpr hn]
    rw [hS, hmn, hn2] at hm2
    have : (n / 2 : ℕ) = m / 2 := by exact_mod_cast hm2
    obtain ⟨i, rfl⟩ := hm; obtain ⟨j, rfl⟩ := hn; omega

/-- The eigenvalues `b_n(q)`, `n ≥ 1`, are pairwise distinct. -/
theorem p1a1_mathieuB_injective {m n : ℕ} (hm0 : m ≠ 0) (hn0 : n ≠ 0) (q : ℝ)
    (hmn : mathieuB m q = mathieuB n q) : m = n := by
  have hW := mathieuWI_wronskian (mathieuB m q) q (π / 2)
  obtain ⟨hm1, hm2⟩ := mathieuB_spec hm0 q
  obtain ⟨hn1, hn2⟩ := mathieuB_spec hn0 q
  rcases Nat.even_or_odd m with hm | hm <;> rcases Nat.even_or_odd n with hn | hn
  · have hS : mathieuSpecB m q = mathieuSpecB n q := by simp [mathieuSpecB, hm, hn]
    rw [hS, hmn, hn2] at hm2
    have : ((n - 1) / 2 : ℕ) = (m - 1) / 2 := by exact_mod_cast hm2
    obtain ⟨i, rfl⟩ := hm; obtain ⟨j, rfl⟩ := hn; omega
  · simp only [mathieuSpecB, hm, ↓reduceIte, Set.mem_ofPred_eq] at hm1
    simp only [mathieuSpecB, Nat.not_even_iff_odd.mpr hn, ↓reduceIte, Set.mem_ofPred_eq] at hn1
    rw [← hmn] at hn1
    rw [hm1, hn1] at hW; simp at hW
  · simp only [mathieuSpecB, Nat.not_even_iff_odd.mpr hm, ↓reduceIte, Set.mem_ofPred_eq] at hm1
    simp only [mathieuSpecB, hn, ↓reduceIte, Set.mem_ofPred_eq] at hn1
    rw [← hmn] at hn1
    rw [hm1, hn1] at hW; simp at hW
  · have hS : mathieuSpecB m q = mathieuSpecB n q := by
      simp [mathieuSpecB, Nat.not_even_iff_odd.mpr hm, Nat.not_even_iff_odd.mpr hn]
    rw [hS, hmn, hn2] at hm2
    have : ((n - 1) / 2 : ℕ) = (m - 1) / 2 := by exact_mod_cast hm2
    obtain ⟨i, rfl⟩ := hm; obtain ⟨j, rfl⟩ := hn; omega

/-! ### The case `q = 0` -/

/-- Derivative of `cos(sz)`. -/
theorem p1a1_hasDerivAt_cos_mul (s z : ℂ) :
    HasDerivAt (fun z => Complex.cos (s * z)) (-Complex.sin (s * z) * s) z := by
  have := ((hasDerivAt_id' z).const_mul s).ccos
  convert this using 1; ring

/-- Derivative of `sin(sz)/s`. -/
theorem p1a1_hasDerivAt_sin_mul_div {s : ℂ} (hs0 : s ≠ 0) (z : ℂ) :
    HasDerivAt (fun z => Complex.sin (s * z) / s) (Complex.cos (s * z)) z := by
  have := (((hasDerivAt_id' z).const_mul s).csin).div_const s
  convert this using 1; field_simp

/-- `w_I(z; a, 0) = cos(sz)` for any `s` with `s² = a`. -/
theorem p1a1_mathieuWI_q_zero {a s : ℂ} (hs : s ^ 2 = a) (z : ℂ) :
    mathieuWI a 0 z = Complex.cos (s * z) := by
  obtain ⟨h, h0, h1⟩ := mathieuWI_spec a 0
  have hdd : ∀ z, HasDerivAt (fun z => -Complex.sin (s * z) * s)
      (-(Complex.cos (s * z) * s) * s) z := fun z => by
    have := (((hasDerivAt_id' z).const_mul s).csin).neg.mul_const s
    convert this using 1; ring
  have hc : IsMathieuSolution a 0 (fun z => Complex.cos (s * z)) := by
    refine ⟨fun z => (p1a1_hasDerivAt_cos_mul s z).differentiableAt, fun z => ?_⟩
    rw [show deriv (fun z => Complex.cos (s * z)) = fun z => -Complex.sin (s * z) * s from
      funext fun z => (p1a1_hasDerivAt_cos_mul s z).deriv]
    convert hdd z using 1; rw [← hs]; ring
  have := h.eq_of_initial hc (z₀ := 0) (by simp [h0])
    (by rw [h1, (p1a1_hasDerivAt_cos_mul s 0).deriv]; simp)
  exact congrFun this z

/-- `w_II(z; a, 0) = sin(sz)/s` for any `s ≠ 0` with `s² = a`. -/
theorem p1a1_mathieuWII_q_zero {a s : ℂ} (hs : s ^ 2 = a) (hs0 : s ≠ 0) (z : ℂ) :
    mathieuWII a 0 z = Complex.sin (s * z) / s := by
  obtain ⟨h, h0, h1⟩ := mathieuWII_spec a 0
  have hc : IsMathieuSolution a 0 (fun z => Complex.sin (s * z) / s) := by
    refine ⟨fun z => (p1a1_hasDerivAt_sin_mul_div hs0 z).differentiableAt, fun z => ?_⟩
    rw [show deriv (fun z => Complex.sin (s * z) / s) = fun z => Complex.cos (s * z) from
      funext fun z => (p1a1_hasDerivAt_sin_mul_div hs0 z).deriv]
    convert p1a1_hasDerivAt_cos_mul s z using 1; rw [← hs]; field_simp; ring
  have := h.eq_of_initial hc (z₀ := 0) (by simp [h0])
    (by rw [h1, (p1a1_hasDerivAt_sin_mul_div hs0 0).deriv]; simp)
  exact congrFun this z

/-- `w_II(z; 0, 0) = z`. -/
theorem p1a1_mathieuWII_zero_zero (z : ℂ) : mathieuWII 0 0 z = z := by
  obtain ⟨h, h0, h1⟩ := mathieuWII_spec 0 0
  have hc : IsMathieuSolution 0 0 (fun z => z) := by
    refine ⟨differentiable_id, fun z => ?_⟩
    rw [show deriv (fun z : ℂ => z) = fun _ => 1 from funext fun z => deriv_id z]
    simpa using hasDerivAt_const z (1 : ℂ)
  have := h.eq_of_initial hc (z₀ := 0) (by simp [h0]) (by rw [h1]; simp)
  exact congrFun this z

/-- `deriv w_I(·; s², 0) = -s sin(s ·)`. -/
theorem p1a1_deriv_mathieuWI_q_zero {a s : ℂ} (hs : s ^ 2 = a) (z : ℂ) :
    deriv (mathieuWI a 0) z = -Complex.sin (s * z) * s := by
  rw [show mathieuWI a 0 = fun z => Complex.cos (s * z) from funext (p1a1_mathieuWI_q_zero hs)]
  exact (p1a1_hasDerivAt_cos_mul s z).deriv

/-- `deriv w_II(·; s², 0) = cos(s ·)`, `s ≠ 0`. -/
theorem p1a1_deriv_mathieuWII_q_zero {a s : ℂ} (hs : s ^ 2 = a) (hs0 : s ≠ 0) (z : ℂ) :
    deriv (mathieuWII a 0) z = Complex.cos (s * z) := by
  rw [show mathieuWII a 0 = fun z => Complex.sin (s * z) / s from
    funext (p1a1_mathieuWII_q_zero hs hs0)]
  exact (p1a1_hasDerivAt_sin_mul_div hs0 z).deriv

/-- The `n`-th smallest element of the range of a strictly increasing sequence. -/
theorem p1a1_nthLeast_range {f : ℕ → ℝ} (hf : StrictMono f) (n : ℕ) :
    nthLeast (range f) n = f n := by
  apply nthLeast_eq_of (Set.mem_range_self n)
  have e : range f ∩ Iio (f n) = f '' (Iio n) := by
    ext x; constructor
    · rintro ⟨⟨k, rfl⟩, hk⟩; exact Set.mem_image_of_mem f (hf.lt_iff_lt.mp hk)
    · rintro ⟨k, hk, rfl⟩; exact ⟨Set.mem_range_self k, hf (Set.mem_Iio.mp hk)⟩
  rw [e, hf.injective.injOn.encard_image]
  simp [Set.encard_eq_coe_toFinset_card]

/-- `s` with `s ⋅ π/2 = m π` is `2m`. -/
theorem p1a1_eq_two_mul_of_sin {s : ℂ} (h : Complex.sin (s * (π / 2)) = 0) :
    ∃ m : ℤ, s = 2 * m := by
  obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp h
  refine ⟨m, ?_⟩
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply mul_right_cancel₀ hπ; linear_combination 2 * hm

/-- `s` with `cos(s ⋅ π/2) = 0` is `2m + 1`. -/
theorem p1a1_eq_two_mul_add_one_of_cos {s : ℂ} (h : Complex.cos (s * (π / 2)) = 0) :
    ∃ m : ℤ, s = 2 * m + 1 := by
  obtain ⟨m, hm⟩ := Complex.cos_eq_zero_iff.mp h
  refine ⟨m, ?_⟩
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply mul_right_cancel₀ hπ; linear_combination 2 * hm

/-- `|m|² = m²` in `ℂ`. -/
theorem p1a1_natAbs_sq (m : ℤ) : ((m.natAbs : ℕ) : ℂ) ^ 2 = (m : ℂ) ^ 2 := by
  have := congrArg (fun t : ℤ => (t : ℂ)) (Int.natAbs_sq m)
  simpa only [Int.cast_pow, Int.cast_natCast] using this

/-- An odd integer squared is `(2j+1)²` for a natural `j`. -/
theorem p1a1_odd_sq (m : ℤ) : ∃ j : ℕ, ((2 * m + 1 : ℂ)) ^ 2 = ((2 * j + 1 : ℕ) : ℂ) ^ 2 := by
  rcases le_or_gt 0 m with hm | hm
  · refine ⟨m.toNat, ?_⟩
    have : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm
    have h2 : ((m.toNat : ℕ) : ℂ) = (m : ℂ) := by exact_mod_cast this
    push_cast; rw [h2]
  · refine ⟨(-m - 1).toNat, ?_⟩
    have : (((-m - 1).toNat : ℕ) : ℤ) = -m - 1 := Int.toNat_of_nonneg (by omega)
    have h2 : (((-m - 1).toNat : ℕ) : ℂ) = ((-m - 1 : ℤ) : ℂ) := by exact_mod_cast this
    push_cast; rw [h2]; push_cast; ring

/-- The spectrum of the `a_{2k}` at `q = 0` is `{(2j)²}`. -/
theorem p1a1_specA_even_zero (k : ℕ) :
    mathieuSpecA (2 * k) 0 = range fun j : ℕ => ((2 * j : ℕ) : ℝ) ^ 2 := by
  ext a
  simp only [mathieuSpecA, show Even (2 * k) from even_two_mul k, ↓reduceIte,
    Set.mem_ofPred_eq, mem_range, Complex.ofReal_zero]
  constructor
  · intro h
    set s := Complex.sqrt a
    have hs : s ^ 2 = a := DLMF.Elementary.trig_sqrt_sq _
    rw [p1a1_deriv_mathieuWI_q_zero hs] at h
    obtain ⟨m, hm⟩ : ∃ m : ℤ, s = 2 * m := by
      rcases mul_eq_zero.mp h with h | h
      · exact p1a1_eq_two_mul_of_sin (by simpa using h)
      · exact ⟨0, by simp [h]⟩
    refine ⟨m.natAbs, ?_⟩
    have : ((a : ℝ) : ℂ) = ((((2 * m.natAbs : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
      rw [← hs, hm]; push_cast; rw [mul_pow, mul_pow, p1a1_natAbs_sq]
    exact_mod_cast this.symm
  · rintro ⟨j, rfl⟩
    have hs : ((2 * j : ℕ) : ℂ) ^ 2 = (((((2 * j : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [p1a1_deriv_mathieuWI_q_zero hs]
    have : Complex.sin (((2 * j : ℕ) : ℂ) * (π / 2)) = 0 := by
      rw [Complex.sin_eq_zero_iff]; exact ⟨j, by push_cast; ring⟩
    rw [this]; simp

/-- The spectrum of the `a_{2k+1}` at `q = 0` is `{(2j+1)²}`. -/
theorem p1a1_specA_odd_zero (k : ℕ) :
    mathieuSpecA (2 * k + 1) 0 = range fun j : ℕ => ((2 * j + 1 : ℕ) : ℝ) ^ 2 := by
  ext a
  simp only [mathieuSpecA, Nat.not_even_bit1, ↓reduceIte,
    Set.mem_ofPred_eq, mem_range, Complex.ofReal_zero]
  constructor
  · intro h
    set s := Complex.sqrt a
    have hs : s ^ 2 = a := DLMF.Elementary.trig_sqrt_sq _
    rw [p1a1_mathieuWI_q_zero hs] at h
    obtain ⟨m, hm⟩ := p1a1_eq_two_mul_add_one_of_cos h
    obtain ⟨j, hj⟩ := p1a1_odd_sq m
    refine ⟨j, ?_⟩
    have : ((a : ℝ) : ℂ) = ((((2 * j + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
      rw [← hs, hm, hj]; push_cast; ring
    exact_mod_cast this.symm
  · rintro ⟨j, rfl⟩
    have hs : ((2 * j + 1 : ℕ) : ℂ) ^ 2 = (((((2 * j + 1 : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [p1a1_mathieuWI_q_zero hs, Complex.cos_eq_zero_iff]
    exact ⟨j, by push_cast; ring⟩

/-- The spectrum of the `b_{2k+1}` at `q = 0` is `{(2j+1)²}`. -/
theorem p1a1_specB_odd_zero (k : ℕ) :
    mathieuSpecB (2 * k + 1) 0 = range fun j : ℕ => ((2 * j + 1 : ℕ) : ℝ) ^ 2 := by
  ext a
  simp only [mathieuSpecB, Nat.not_even_bit1, ↓reduceIte,
    Set.mem_ofPred_eq, mem_range, Complex.ofReal_zero]
  constructor
  · intro h
    set s := Complex.sqrt a
    have hs : s ^ 2 = a := DLMF.Elementary.trig_sqrt_sq _
    rcases eq_or_ne s 0 with hs0 | hs0
    · exfalso
      have ha : (a : ℂ) = 0 := by rw [← hs, hs0]; ring
      rw [ha] at h
      rw [show mathieuWII 0 0 = fun z => z from funext p1a1_mathieuWII_zero_zero] at h
      simp at h
    rw [p1a1_deriv_mathieuWII_q_zero hs hs0] at h
    obtain ⟨m, hm⟩ := p1a1_eq_two_mul_add_one_of_cos h
    obtain ⟨j, hj⟩ := p1a1_odd_sq m
    refine ⟨j, ?_⟩
    have : ((a : ℝ) : ℂ) = ((((2 * j + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
      rw [← hs, hm, hj]; push_cast; ring
    exact_mod_cast this.symm
  · rintro ⟨j, rfl⟩
    have hs : ((2 * j + 1 : ℕ) : ℂ) ^ 2 = (((((2 * j + 1 : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [p1a1_deriv_mathieuWII_q_zero hs (Nat.cast_ne_zero.mpr (by omega)), Complex.cos_eq_zero_iff]
    exact ⟨j, by push_cast; ring⟩

/-- The spectrum of the `b_{2k+2}` at `q = 0` is `{(2j+2)²}`. -/
theorem p1a1_specB_even_zero (k : ℕ) :
    mathieuSpecB (2 * k + 2) 0 = range fun j : ℕ => ((2 * j + 2 : ℕ) : ℝ) ^ 2 := by
  ext a
  have he : Even (2 * k + 2) := ⟨k + 1, by ring⟩
  simp only [mathieuSpecB, he, ↓reduceIte, Set.mem_ofPred_eq, mem_range, Complex.ofReal_zero]
  constructor
  · intro h
    set s := Complex.sqrt a
    have hs : s ^ 2 = a := DLMF.Elementary.trig_sqrt_sq _
    rcases eq_or_ne s 0 with hs0 | hs0
    · exfalso
      have ha : (a : ℂ) = 0 := by rw [← hs, hs0]; ring
      rw [ha, p1a1_mathieuWII_zero_zero] at h
      have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      exact hπ (by linear_combination 2 * h)
    rw [p1a1_mathieuWII_q_zero hs hs0, div_eq_zero_iff, or_iff_left hs0] at h
    obtain ⟨m, hm⟩ := p1a1_eq_two_mul_of_sin h
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hs0 hm
    refine ⟨m.natAbs - 1, ?_⟩
    have hna : ((m.natAbs - 1 : ℕ) : ℂ) = (m.natAbs : ℂ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have : ((a : ℝ) : ℂ) = ((((2 * (m.natAbs - 1) + 2 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
      rw [← hs, hm]; push_cast; rw [hna]
      linear_combination (-4 : ℂ) * p1a1_natAbs_sq m
    exact_mod_cast this.symm
  · rintro ⟨j, rfl⟩
    have hs : ((2 * j + 2 : ℕ) : ℂ) ^ 2 = (((((2 * j + 2 : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [p1a1_mathieuWII_q_zero hs (Nat.cast_ne_zero.mpr (by omega))]
    have : Complex.sin (((2 * j + 2 : ℕ) : ℂ) * (π / 2)) = 0 := by
      rw [Complex.sin_eq_zero_iff]; exact ⟨j + 1, by push_cast; ring⟩
    rw [this, zero_div]

/-- **DLMF 28.2.23**: `a_n(0) = n²`, `n = 0, 1, 2, …`. -/
@[dlmf 28.2.E23]
theorem mathieuA_zero (n : ℕ) : mathieuA n 0 = (n : ℝ) ^ 2 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [mathieuA, p1a1_specA_even_zero, show 2 * k / 2 = k by omega,
      p1a1_nthLeast_range (by intro i j h; simp only; gcongr)]
  · rw [mathieuA, p1a1_specA_odd_zero, show (2 * k + 1) / 2 = k by omega,
      p1a1_nthLeast_range (by intro i j h; simp only; gcongr)]

/-- **DLMF 28.2.24**: `b_n(0) = n²`, `n = 1, 2, 3, …`. -/
@[dlmf 28.2.E24]
theorem mathieuB_zero {n : ℕ} (hn : n ≠ 0) : mathieuB n 0 = (n : ℝ) ^ 2 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [mathieuB, hn, ↓reduceIte]
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, p1a1_specB_even_zero,
      show (2 * j + 2 - 1) / 2 = j by omega,
      p1a1_nthLeast_range (by intro i j h; simp only; gcongr)]
  · simp only [mathieuB, hn, ↓reduceIte]
    rw [p1a1_specB_odd_zero, show (2 * k + 1 - 1) / 2 = k by omega,
      p1a1_nthLeast_range (by intro i j h; simp only; gcongr)]

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
  have hS : mathieuSpecA (2 * n) (-q) = mathieuSpecA (2 * n) q := by
    ext a
    simp [mathieuSpecA, p1a1_deriv_mathieuWI_half_pi_neg_q]
  simp only [mathieuA, hS]

/-- **DLMF 28.2.27**: `a_{2n+1}(-q) = b_{2n+1}(q)`. -/
@[dlmf 28.2.E27]
theorem mathieuA_odd_neg (n : ℕ) (q : ℝ) :
    mathieuA (2 * n + 1) (-q) = mathieuB (2 * n + 1) q := by
  have hS : mathieuSpecA (2 * n + 1) (-q) = mathieuSpecB (2 * n + 1) q := by
    ext a
    simp [mathieuSpecA, mathieuSpecB, Nat.not_even_bit1, p1a1_mathieuWI_half_pi_neg_q]
  simp only [mathieuA, mathieuB, hS, show 2 * n + 1 ≠ 0 by omega, ite_false,
    show (2 * n + 1) / 2 = (2 * n + 1 - 1) / 2 by omega]

/-- **DLMF 28.2.28**: `b_{2n+2}(-q) = b_{2n+2}(q)`. -/
@[dlmf 28.2.E28]
theorem mathieuB_even_neg (n : ℕ) (q : ℝ) :
    mathieuB (2 * n + 2) (-q) = mathieuB (2 * n + 2) q := by
  have hS : mathieuSpecB (2 * n + 2) (-q) = mathieuSpecB (2 * n + 2) q := by
    ext a
    have he : Even (2 * n + 2) := ⟨n + 1, by ring⟩
    simp [mathieuSpecB, he, p1a1_mathieuWII_half_pi_neg_q]
  simp only [mathieuB, hS]

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

/-! ### Normalization and orthogonality helpers -/

/-- Complex conjugation: `conj ∘ w ∘ conj` solves Mathieu's equation for `(conj a, conj q)`. -/
theorem IsMathieuSolution.p1a1_conj {a q : ℂ} {w : ℂ → ℂ} (h : IsMathieuSolution a q w) :
    IsMathieuSolution (conj a) (conj q) (conj ∘ w ∘ conj) := by
  refine ⟨fun z => ?_, fun z => ?_⟩
  · simpa using (h.differentiable (conj z)).conj_conj
  · rw [deriv_conj_conj]
    have := (h.hasDerivAt_deriv (conj z)).conj_conj
    simp only [Complex.conj_conj] at this
    convert this using 1
    simp only [Function.comp, map_mul, map_sub, map_ofNat, ← Complex.cos_conj, Complex.conj_conj]

/-- `w_I(z; conj a, conj q) = conj (w_I(conj z; a, q))`. -/
theorem p1a1_mathieuWI_conj (a q z : ℂ) :
    mathieuWI (conj a) (conj q) z = conj (mathieuWI a q (conj z)) := by
  obtain ⟨h, h0, h1⟩ := mathieuWI_spec a q
  obtain ⟨g, g0, g1⟩ := mathieuWI_spec (conj a) (conj q)
  have key := g.eq_of_initial h.p1a1_conj (z₀ := 0) (by simp [g0, h0])
    (by rw [deriv_conj_conj]; simp [g1, h1])
  exact congrFun key z

/-- `w_II(z; conj a, conj q) = conj (w_II(conj z; a, q))`. -/
theorem p1a1_mathieuWII_conj (a q z : ℂ) :
    mathieuWII (conj a) (conj q) z = conj (mathieuWII a q (conj z)) := by
  obtain ⟨h, h0, h1⟩ := mathieuWII_spec a q
  obtain ⟨g, g0, g1⟩ := mathieuWII_spec (conj a) (conj q)
  have key := g.eq_of_initial h.p1a1_conj (z₀ := 0) (by simp [g0, h0])
    (by rw [deriv_conj_conj]; simp [g1, h1])
  exact congrFun key z

/-- `w_I(x; a, q)` is real for real `x`, `a`, `q`. -/
theorem p1a1_mathieuWI_real (a q x : ℝ) : conj (mathieuWI a q x) = mathieuWI a q x := by
  have := p1a1_mathieuWI_conj a q x
  simp only [Complex.conj_ofReal] at this
  exact this.symm

/-- `w_II(x; a, q)` is real for real `x`, `a`, `q`. -/
theorem p1a1_mathieuWII_real (a q x : ℝ) : conj (mathieuWII a q x) = mathieuWII a q x := by
  have := p1a1_mathieuWII_conj a q x
  simp only [Complex.conj_ofReal] at this
  exact this.symm

/-- `w_I'(x; a, q)` is real for real `x`, `a`, `q`. -/
theorem p1a1_deriv_mathieuWI_real (a q x : ℝ) :
    conj (deriv (mathieuWI a q) x) = deriv (mathieuWI a q) x := by
  have e : mathieuWI (a : ℂ) q = conj ∘ mathieuWI (a : ℂ) q ∘ conj := by
    funext z; have := p1a1_mathieuWI_conj a q z; simpa using this
  conv_rhs => rw [e, deriv_conj_conj]
  simp

/-- `w_II'(x; a, q)` is real for real `x`, `a`, `q`. -/
theorem p1a1_deriv_mathieuWII_real (a q x : ℝ) :
    conj (deriv (mathieuWII a q) x) = deriv (mathieuWII a q) x := by
  have e : mathieuWII (a : ℂ) q = conj ∘ mathieuWII (a : ℂ) q ∘ conj := by
    funext z; have := p1a1_mathieuWII_conj a q z; simpa using this
  conv_rhs => rw [e, deriv_conj_conj]
  simp

/-- A real complex number squared is its squared norm. -/
theorem p1a1_sq_eq_norm_sq {z : ℂ} (h : conj z = z) : z ^ 2 = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨r, rfl⟩ := Complex.conj_eq_iff_real.mp h
  simp [Complex.norm_real, sq_abs]

/-- `∫₀^{2π} ‖w_I(x; a, q)‖² > 0`. -/
theorem p1a1_integral_normSq_mathieuWI_pos (a q : ℂ) :
    0 < ∫ x in (0 : ℝ)..2 * π, ‖mathieuWI a q x‖ ^ 2 := by
  obtain ⟨h, h0, -⟩ := mathieuWI_spec a q
  have hev : ∀ᶠ x : ℝ in 𝓝 0, mathieuWI a q x ≠ 0 :=
    (h.differentiable.continuous.comp Complex.continuous_ofReal).continuousAt.eventually_ne
      (by simp [h0])
  exact m28a_integral_normSq_pos h.differentiable.continuous (nhdsWithin_le_nhds hev)

/-- `∫₀^{2π} ‖w_II(x; a, q)‖² > 0`. -/
theorem p1a1_integral_normSq_mathieuWII_pos (a q : ℂ) :
    0 < ∫ x in (0 : ℝ)..2 * π, ‖mathieuWII a q x‖ ^ 2 := by
  obtain ⟨h, h0, h1⟩ := mathieuWII_spec a q
  have hd : HasDerivAt (fun x : ℝ => mathieuWII a q x) 1 0 := by
    have := (h.differentiable _).hasDerivAt.comp_ofReal (z := 0)
    simpa [h1] using this
  have hev := hd.eventually_ne (c := 0) one_ne_zero
  have hev' : ∀ᶠ x : ℝ in 𝓝[>] 0, mathieuWII a q x ≠ 0 :=
    nhdsWithin_mono (0 : ℝ) (fun x (hx : x ∈ Ioi (0 : ℝ)) => ne_of_gt hx) hev
  exact m28a_integral_normSq_pos h.differentiable.continuous hev'

/-- `∫₀^{2π} (c f)² = π` when `f` is real on the real axis and `c = (π / ∫ ‖f‖²)^{1/2}`. -/
theorem p1a1_integral_normalized_sq {f : ℂ → ℂ}
    (hr : ∀ x : ℝ, conj (f x) = f x) (hpos : 0 < ∫ x in (0 : ℝ)..2 * π, ‖f x‖ ^ 2) :
    ∫ x in (0 : ℝ)..2 * π,
      ((Real.sqrt (π / ∫ x in (0 : ℝ)..2 * π, ‖f x‖ ^ 2) : ℂ) * f x) ^ 2 = π := by
  set I := ∫ x in (0 : ℝ)..2 * π, ‖f x‖ ^ 2
  have e : ∀ x : ℝ, ((Real.sqrt (π / I) : ℂ) * f x) ^ 2 =
      (((Real.sqrt (π / I)) ^ 2 * ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    intro x; rw [mul_pow, p1a1_sq_eq_norm_sq (hr x)]; push_cast; ring
  simp_rw [e]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
    Real.sq_sqrt (div_pos Real.pi_pos hpos).le, div_mul_cancel₀ _ hpos.ne']

/-- `∫₀^{2π} cos²(nx) dx = π`, `n ≠ 0`. -/
theorem p1a1_integral_cos_sq {n : ℕ} (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..2 * π, Real.cos (n * x) ^ 2 = π := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x ^ 2) hn', integral_cos_sq]
  have : Real.sin (n * (2 * π)) = 0 := by
    rw [show (n : ℝ) * (2 * π) = ((2 * n : ℕ) : ℝ) * π by push_cast; ring]
    exact Real.sin_nat_mul_pi _
  rw [this]; simp; field_simp

/-- `∫₀^{2π} sin²(nx) dx = π`, `n ≠ 0`. -/
theorem p1a1_integral_sin_sq {n : ℕ} (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..2 * π, Real.sin (n * x) ^ 2 = π := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x ^ 2) hn', integral_sin_sq]
  have : Real.sin (n * (2 * π)) = 0 := by
    rw [show (n : ℝ) * (2 * π) = ((2 * n : ℕ) : ℝ) * π by push_cast; ring]
    exact Real.sin_nat_mul_pi _
  rw [this]; simp; field_simp

/-- `‖cos(nx)‖² = cos²(nx)` for real `x`. -/
theorem p1a1_norm_cos_sq (n : ℕ) (x : ℝ) :
    ‖Complex.cos (n * x)‖ ^ 2 = Real.cos (n * x) ^ 2 := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_cos, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- `‖sin(nx)/n‖² = sin²(nx)/n²` for real `x`. -/
theorem p1a1_norm_sin_div_sq {n : ℕ} (x : ℝ) :
    ‖Complex.sin (n * x) / n‖ ^ 2 = Real.sin (n * x) ^ 2 / (n : ℝ) ^ 2 := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_sin, ← Complex.ofReal_div,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow]

/-- `w_I(z; n², 0) = cos nz`. -/
theorem p1a1_mathieuWI_sq_q_zero (n : ℕ) :
    mathieuWI (((n : ℝ) ^ 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) = fun z => Complex.cos (n * z) := by
  funext z; rw [Complex.ofReal_zero]; exact p1a1_mathieuWI_q_zero (by push_cast; ring) z

/-- `w_II(z; n², 0) = sin(nz)/n`, `n ≠ 0`. -/
theorem p1a1_mathieuWII_sq_q_zero {n : ℕ} (hn : n ≠ 0) :
    mathieuWII (((n : ℝ) ^ 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) = fun z => Complex.sin (n * z) / n := by
  funext z; rw [Complex.ofReal_zero]
  exact p1a1_mathieuWII_q_zero (by push_cast; ring) (Nat.cast_ne_zero.mpr hn) z

/-- **Orthogonality** (Sturm–Liouville): `2π`-periodic solutions of Mathieu's equation for
distinct `a₁ ≠ a₂` (same `q`) are orthogonal on `[0, 2π]`. -/
theorem p1a1_integral_mul_eq_zero {a₁ a₂ q : ℂ} {u v : ℂ → ℂ} (hu : IsMathieuSolution a₁ q u)
    (hv : IsMathieuSolution a₂ q v) (hup : ∀ z, u (z + 2 * π) = u z)
    (hvp : ∀ z, v (z + 2 * π) = v z) (hne : a₁ ≠ a₂) :
    ∫ x in (0 : ℝ)..2 * π, u x * v x = 0 := by
  have hdp : ∀ {w : ℂ → ℂ}, (∀ z, w (z + 2 * π) = w z) → ∀ z, deriv w (z + 2 * π) = deriv w z := by
    intro w hw z
    have := congrArg (fun f => deriv f z) (funext hw)
    simp only [deriv_comp_add_const] at this
    exact this
  have hF : ∀ x : ℝ, HasDerivAt (fun x : ℝ => deriv u x * v x - u x * deriv v x)
      ((a₂ - a₁) * (u x * v x)) x := by
    intro x
    have h1 := ((hu.hasDerivAt_deriv x).mul (hv.differentiable x).hasDerivAt).sub
      ((hu.differentiable x).hasDerivAt.mul (hv.hasDerivAt_deriv x))
    have := h1.comp_ofReal
    convert this using 1; ring
  have hint : IntervalIntegrable (fun x : ℝ => (a₂ - a₁) * (u x * v x)) MeasureTheory.volume
      0 (2 * π) := by
    apply Continuous.intervalIntegrable
    have := hu.differentiable.continuous
    have := hv.differentiable.continuous
    fun_prop
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x) hint
  have e2 : ((2 * π : ℝ) : ℂ) = 0 + 2 * π := by push_cast; ring
  rw [e2, hup, hvp, hdp hup, hdp hvp, Complex.ofReal_zero, sub_self,
    intervalIntegral.integral_const_mul] at key
  rcases mul_eq_zero.mp key with h | h
  · exact absurd (sub_eq_zero.mp h).symm hne
  · exact h

/-- `ce_n(z, q)` has period `2π`. -/
theorem p1a1_mathieuCe_add_two_pi (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuCe n (z + 2 * π) q = mathieuCe n z q := by
  rw [show z + 2 * π = z + π + π by ring]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [mathieuCe_even_add_pi, mathieuCe_even_add_pi]
  · rw [mathieuCe_odd_add_pi, mathieuCe_odd_add_pi, neg_neg]

/-- `se_n(z, q)`, `n ≥ 1`, has period `2π`. -/
theorem p1a1_mathieuSe_add_two_pi {n : ℕ} (hn : n ≠ 0) (z : ℂ) (q : ℝ) :
    mathieuSe n (z + 2 * π) q = mathieuSe n z q := by
  rw [show z + 2 * π = z + π + π by ring]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, mathieuSe_even_add_pi, mathieuSe_even_add_pi]
  · rw [mathieuSe_odd_add_pi, mathieuSe_odd_add_pi, neg_neg]

/-- **DLMF 28.2.29**: `ce_0(z, 0) = 1/√2`. -/
@[dlmf 28.2.E29]
theorem mathieuCe_zero_zero (z : ℂ) : mathieuCe 0 z 0 = 1 / Real.sqrt 2 := by
  have e := p1a1_mathieuWI_sq_q_zero 0
  simp only [Nat.cast_zero, zero_mul, Complex.cos_zero] at e
  rw [mathieuCe, mathieuCeZero, mathieuA_zero 0]
  simp only [Nat.cast_zero] at e ⊢
  rw [e]
  simp only [norm_one, one_pow, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  rw [show π / (2 * π) = (2 : ℝ)⁻¹ by field_simp, Real.sqrt_inv]
  push_cast; ring

/-- **DLMF 28.2.29**: `ce_n(z, 0) = cos nz`, `n = 1, 2, 3, …`. -/
@[dlmf 28.2.E29]
theorem mathieuCe_q_zero {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    mathieuCe n z 0 = Complex.cos (n * z) := by
  rw [mathieuCe, mathieuCeZero, mathieuA_zero n, p1a1_mathieuWI_sq_q_zero n]
  simp only [p1a1_norm_cos_sq, p1a1_integral_cos_sq hn, div_self Real.pi_ne_zero,
    Real.sqrt_one, Complex.ofReal_one, one_mul]

/-- **DLMF 28.2.29**: `se_n(z, 0) = sin nz`, `n = 1, 2, 3, …`. -/
@[dlmf 28.2.E29]
theorem mathieuSe_q_zero {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    mathieuSe n z 0 = Complex.sin (n * z) := by
  rw [mathieuSe, mathieuSeDerivZero, mathieuB_zero hn, p1a1_mathieuWII_sq_q_zero hn]
  simp only [p1a1_norm_sin_div_sq]
  rw [intervalIntegral.integral_div, p1a1_integral_sin_sq hn]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [show π / (π / (n : ℝ) ^ 2) = (n : ℝ) ^ 2 by field_simp, Real.sqrt_sq (Nat.cast_nonneg n)]
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  push_cast; field_simp

/-- **Normalization** (DLMF 28.2.30): `∫₀^{2π} ce_n(x, q)² dx = π` (real `q`). -/
@[dlmf 28.2.E30]
theorem integral_mathieuCe_sq (n : ℕ) (q : ℝ) :
    ∫ x in (0 : ℝ)..2 * π, mathieuCe n x q ^ 2 = π := by
  have := p1a1_integral_normalized_sq (f := mathieuWI (mathieuA n q) q)
    (fun x => p1a1_mathieuWI_real _ _ x) (p1a1_integral_normSq_mathieuWI_pos _ _)
  exact this

/-- **Normalization** (DLMF 28.2.30): `∫₀^{2π} se_n(x, q)² dx = π`, `n ≥ 1` (real `q`). -/
@[dlmf 28.2.E30]
theorem integral_mathieuSe_sq {n : ℕ} (hn : n ≠ 0) (q : ℝ) :
    ∫ x in (0 : ℝ)..2 * π, mathieuSe n x q ^ 2 = π := by
  exact p1a1_integral_normalized_sq (f := mathieuWII (mathieuB n q) q)
    (fun x => p1a1_mathieuWII_real _ _ x) (p1a1_integral_normSq_mathieuWII_pos _ _)

/-- **Orthogonality** (DLMF 28.2.31): `∫₀^{2π} ce_m ce_n = 0` for `m ≠ n` (real `q`). -/
@[dlmf 28.2.E31]
theorem integral_mathieuCe_mul_mathieuCe {m n : ℕ} (hmn : m ≠ n) (q : ℝ) :
    ∫ x in (0 : ℝ)..2 * π, mathieuCe m x q * mathieuCe n x q = 0 :=
  p1a1_integral_mul_eq_zero (isMathieuSolution_mathieuCe m q) (isMathieuSolution_mathieuCe n q)
    (fun z => p1a1_mathieuCe_add_two_pi m z q) (fun z => p1a1_mathieuCe_add_two_pi n z q)
    (fun h => hmn (p1a1_mathieuA_injective q (by exact_mod_cast h)))

/-- **Orthogonality** (DLMF 28.2.32): `∫₀^{2π} se_m se_n = 0` for `m ≠ n`, `m, n ≥ 1`. -/
@[dlmf 28.2.E32]
theorem integral_mathieuSe_mul_mathieuSe {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ≠ n)
    (q : ℝ) : ∫ x in (0 : ℝ)..2 * π, mathieuSe m x q * mathieuSe n x q = 0 :=
  p1a1_integral_mul_eq_zero (isMathieuSolution_mathieuSe m q) (isMathieuSolution_mathieuSe n q)
    (fun z => p1a1_mathieuSe_add_two_pi hm z q) (fun z => p1a1_mathieuSe_add_two_pi hn z q)
    (fun h => hmn (p1a1_mathieuB_injective hm hn q (by exact_mod_cast h)))


/-- **Counterexample** to DLMF 28.2.33 as stated for `n = 0` (where `se_0` is a junk value):
at `q = 0`, `∫₀^{2π} ce_0 se_0 ≠ 0`, since `se_0(x, 0)` is a positive multiple of `x`. -/
theorem p1a1_integral_mathieuCe_mul_mathieuSe_zero_ne :
    ∫ x in (0 : ℝ)..2 * π, mathieuCe 0 x 0 * mathieuSe 0 x 0 ≠ 0 := by
  have hB : mathieuB 0 0 = 0 := by simp [mathieuB]
  have hse : ∀ x : ℂ, mathieuSe 0 x 0 = mathieuSeDerivZero 0 0 * x := by
    intro x; rw [mathieuSe, hB]; push_cast; rw [p1a1_mathieuWII_zero_zero]
  simp_rw [mathieuCe_zero_zero, hse]
  have e : ∀ x : ℝ, (1 / (Real.sqrt 2 : ℂ)) * ((mathieuSeDerivZero 0 0 : ℂ) * (x : ℂ)) =
      ((1 / Real.sqrt 2 * mathieuSeDerivZero 0 0 * x : ℝ) : ℂ) := by
    intro x; push_cast; ring
  simp_rw [e]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul, integral_id]
  have h2 : 0 < Real.sqrt 2 := by positivity
  have := mathieuSeDerivZero_pos 0 0
  rw [Complex.ofReal_ne_zero]
  have : 0 < 1 / Real.sqrt 2 * mathieuSeDerivZero 0 0 * (((2 * π) ^ 2 - 0 ^ 2) / 2) := by
    have hπ := Real.pi_pos
    refine mul_pos (mul_pos (by positivity) this) ?_
    nlinarith
  exact this.ne'

/-- DLMF 28.2.33 for `n ≥ 1`: `∫₀^{2π} ce_m se_n = 0`, by parity and periodicity. -/
theorem p1a1_integral_mathieuCe_mul_mathieuSe {m n : ℕ} (hn : n ≠ 0) (q : ℝ) :
    ∫ x in (0 : ℝ)..2 * π, mathieuCe m x q * mathieuSe n x q = 0 := by
  set f : ℝ → ℂ := fun x => mathieuCe m x q * mathieuSe n x q
  have hp : Function.Periodic f (2 * π) := fun x => by
    simp only [f]; push_cast
    rw [p1a1_mathieuCe_add_two_pi, p1a1_mathieuSe_add_two_pi hn]
  have hodd : ∀ x, f (-x) = -f x := fun x => by
    simp only [f]; push_cast; rw [mathieuCe_neg, mathieuSe_neg]; ring
  have h1 : ∫ x in (0 : ℝ)..2 * π, f x = ∫ x in (-π)..π, f x := by
    have := hp.intervalIntegral_add_eq 0 (-π)
    rw [zero_add, show -π + 2 * π = π by ring] at this
    exact this
  have h2 : ∫ x in (-π)..π, f x = -∫ x in (-π)..π, f x := by
    have := intervalIntegral.integral_comp_neg (a := -π) (b := π) f
    rw [neg_neg] at this
    conv_lhs => rw [← this]
    simp only [hodd, intervalIntegral.integral_neg]
  show ∫ x in (0 : ℝ)..2 * π, f x = 0
  rw [h1]
  linear_combination h2 / 2

/-- **Orthogonality** (DLMF 28.2.33): `∫₀^{2π} ce_m se_n = 0` for `n ≥ 1`. The hypothesis
`n ≠ 0` was added on 2026-10-26: DLMF does not define `se_0`, and for the junk value `n = 0`
the statement fails (`p1a1_integral_mathieuCe_mul_mathieuSe_zero_ne`). -/
@[dlmf 28.2.E33]
theorem integral_mathieuCe_mul_mathieuSe (m n : ℕ) (hn : n ≠ 0) (q : ℝ) :
    ∫ x in (0 : ℝ)..2 * π, mathieuCe m x q * mathieuSe n x q = 0 :=
  p1a1_integral_mathieuCe_mul_mathieuSe hn q

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
