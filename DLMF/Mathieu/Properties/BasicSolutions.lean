/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.SpectralExistence
public import DLMF.Mathieu.P2sBridge
public import DLMF.Elementary.Trigonometric
public import DLMFMathlib.Analysis.ODE.Singularities
public import SeveralComplexVariables.SeparateAnalytic
public import DLMFMathlib.Analysis.Fourier.P1a2EntirePeriodic
public import Mathlib.Analysis.Convex.Contractible

/-!
# Basic Mathieu solutions and symmetries

Algebraic forms, normalized basic solutions and sign-change symmetries of Mathieu equation.

Source references and common attribution are retained in
`DLMF.Mathieu.Properties`.
-/

@[expose] public noncomputable section

open Complex Set Filter ComplexConjugate

open scoped Topology Real

namespace DLMF.Mathieu

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
lemma p2f_not_eventuallyEq_analytic {f : ℂ → ℂ} {z₀ L : ℂ} (hL : L ≠ 0)
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
lemma p2f_tendsto_of_eq {f g : ℂ → ℂ} {z₀ : ℂ} (hg : ContinuousAt g z₀)
    (h : ∀ z, z ≠ z₀ → f z = g z) : Tendsto f (𝓝[≠] z₀) (𝓝 (g z₀)) :=
  (hg.tendsto.mono_left nhdsWithin_le_nhds).congr'
    (eventually_nhdsWithin_of_forall fun z hz => (h z hz).symm)

/-- Two raw coefficients of a second-order equation after `z = 1/u`. -/
lemma p2f_recipRaw_zero_two (c₀ c₁ : ℂ → ℂ) {u : ℂ} (hu : u ≠ 0) :
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

end IsMathieuSolution

/-- Derivative of a linear combination `c f + d g`. -/
lemma m28a_deriv_lincomb {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℂ g z) (c d : ℂ) :
    deriv (fun x => c * f x + d * g x) z = c * deriv f z + d * deriv g z :=
  ((hf.hasDerivAt.const_mul c).add (hg.hasDerivAt.const_mul d)).deriv

/-- Derivative of a linear combination `c f - d g`. -/
lemma m28a_deriv_lincomb_sub {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z)
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
lemma m28a_mathieuWI_pi_sub (z : ℂ) :
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
lemma m28a_mathieuWII_pi_sub (z : ℂ) :
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
theorem deriv_mathieuWI_pi : deriv wI π = 2 * wI (π / 2) * deriv wI (π / 2) := by
  obtain ⟨h1, -, h11⟩ := mathieuWI_spec a q
  obtain ⟨h2, -, h21⟩ := mathieuWII_spec a q
  have e := congrArg (fun f => deriv f 0) (funext (m28a_mathieuWI_pi_sub a q))
  rw [deriv_comp_const_sub, m28a_deriv_lincomb_sub (h1.differentiable _) (h2.differentiable _),
    h11, h21] at e
  simp only [sub_zero] at e
  linear_combination -e

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
lemma p2f_ray_hasDerivAt {a q : ℂ} {w : ℂ → ℂ} (hw : IsMathieuSolution a q w) (z : ℂ)
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
lemma p2f_differentiable_of_separately {f : ℂ × ℂ × ℂ → ℂ}
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
lemma p1a1_deriv_shift_lincomb {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
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

/-- `w_I(π/2; a, -q) = w_II'(π/2; a, q)`: the value at `π/2` under `q ↦ -q`. -/
theorem p1a1_mathieuWI_half_pi_neg_q (a q : ℂ) :
    mathieuWI a (-q) (π / 2) = deriv (mathieuWII a q) (π / 2) := by
  rw [p1a1_mathieuWI_neg_q, show (π : ℂ) / 2 + π / 2 = π by ring, mathieuWII_pi,
    m28a_mathieuWI_pi]
  linear_combination deriv (mathieuWII a q) (π / 2) * mathieuWI_wronskian a q (π / 2)

/-- `w_II(π/2; a, -q) = w_II(π/2; a, q)`: the value at `π/2` under `q ↦ -q`. -/
theorem p1a1_mathieuWII_half_pi_neg_q (a q : ℂ) :
    mathieuWII a (-q) (π / 2) = mathieuWII a q (π / 2) := by
  rw [p1a1_mathieuWII_neg_q, show (π : ℂ) / 2 + π / 2 = π by ring, mathieuWII_pi,
    m28a_mathieuWI_pi]
  linear_combination mathieuWII a q (π / 2) * mathieuWI_wronskian a q (π / 2)

/-- `w_I'(π/2; a, -q) = w_I'(π/2; a, q)`: the derivative at `π/2` under `q ↦ -q`. -/
theorem p1a1_deriv_mathieuWI_half_pi_neg_q (a q : ℂ) :
    deriv (mathieuWI a (-q)) (π / 2) = deriv (mathieuWI a q) (π / 2) := by
  have e : mathieuWI a (-q) = fun z => deriv (mathieuWII a q) (π / 2) *
      mathieuWI a q (z + π / 2) - deriv (mathieuWI a q) (π / 2) * mathieuWII a q (z + π / 2) :=
    funext (p1a1_mathieuWI_neg_q a q)
  rw [e, p1a1_deriv_shift_lincomb (isMathieuSolution_mathieuWI a q).differentiable
    (isMathieuSolution_mathieuWII a q).differentiable,
    show (π : ℂ) / 2 + π / 2 = π by ring, deriv_mathieuWI_pi, m28a_deriv_mathieuWII_pi]
  linear_combination deriv (mathieuWI a q) (π / 2) * mathieuWI_wronskian a q (π / 2)

/-- `w_II'(π/2; a, -q) = w_I(π/2; a, q)`: the derivative at `π/2` under `q ↦ -q`. -/
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
lemma IsMathieuSolution.p1a1_deriv_eq {a q : ℂ} {w : ℂ → ℂ} (h : IsMathieuSolution a q w)
    (z : ℂ) : deriv w z = w 0 * deriv (mathieuWI a q) z + deriv w 0 * deriv (mathieuWII a q) z := by
  conv_lhs => rw [h.eq_combination]
  exact m28a_deriv_lincomb ((isMathieuSolution_mathieuWI a q).differentiable z)
    ((isMathieuSolution_mathieuWII a q).differentiable z) _ _

end DLMF.Mathieu
end
