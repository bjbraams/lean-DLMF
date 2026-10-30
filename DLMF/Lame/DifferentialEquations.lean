/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Heun.Basic
public import DLMF.Lame.Eigenvalues
public import DLMF.Lame.P3lWeierstrass
public import DLMFMathlib.Analysis.ODE.Singularities

/-!
# Lamé's equation: singularities and other forms (DLMF §§29.2, 29.10, 29.11)

* §29.2(i): the singularities `2pK + (2q+1)iK'` of 29.2.1 are regular singular points, all
  other points are ordinary (proved).
* §29.2(ii): the algebraic form 29.2.2 in `ξ = sn²` (proved), the trigonometric form 29.2.4
  in `φ = π/2 - am` (proved), the Weierstrass forms 29.2.9 (admitted) and 29.2.10 (proved),
  and the identification of 29.2.2 as Heun's equation 31.2.1 (proved; DLMF states this for the
  equivalent 29.2.10).
* §29.10: the substitution `h = ν(ν+1) - h'`, `z' = i(z - K - iK')` maps Lamé's equation with
  modulus `k'` to that with modulus `k` (admitted); the functions 29.10.4 on the line
  `Re z = K` solve 29.2.1 (proved from `sn(K + is, k) = nd(s, k')`) and their imaginary
  periods (proved from Table 29.3.2).
* §29.11: the Lamé wave equation reduces to 29.2.1 for `ω = 0` (proved).
-/

@[expose] public section

open Complex DLMF.JacobiElliptic DLMF.Elliptic Filter Set
open scoped Real Topology

noncomputable section

namespace DLMF.Lame

variable {h ν k : ℝ}

/-! ### Singularities (§29.2(i)) -/

/-- `0` is not a pole of `sn, cn, dn`. -/
lemma p1l_regular_at_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiLetterTheta .n (jacobiZetak 0 k) (jacobiTauk k) ≠ 0 := by
  have hτ := jacobiTauk_im_pos hk
  simp only [jacobiZetak, mul_zero, zero_div, jacobiLetterTheta]
  exact div_ne_zero (je22a_thetaFour_zero_ne_zero hτ) (je22a_thetaFour_zero_ne_zero hτ)

/-- For real `0 < k < 1`, `sn(·, k)` is analytic at every point other than the poles
`2pK + (2q+1)iK'` (the zeros of `θ₄` at `ζ = πz/(2K)`, §20.2(iv)). -/
lemma p1l_analyticAt_sn (hk0 : 0 < k) (hk1 : k < 1) {z : ℂ}
    (hz : ∀ p q : ℤ,
      z ≠ 2 * p * Real.compEllIntKm (k ^ 2) + (2 * q + 1) * I * Real.compEllIntKm (1 - k ^ 2)) :
    AnalyticAt ℂ (fun z => jacobiSnk z k) z := by
  have hkD : (k : ℂ) ∈ jacobiModulusDomain := p22R1_ofReal_mem hk0 hk1
  have hτ := jacobiTauk_im_pos hkD
  have hK : compEllIntKk (k : ℂ) = (Real.compEllIntKm (k ^ 2) : ℂ) :=
    compEllIntKk_ofReal (by nlinarith)
  have hK' : compEllIntKpk (k : ℂ) = (Real.compEllIntKm (1 - k ^ 2) : ℂ) :=
    compEllIntKpk_ofReal (by positivity)
  have hK0 := compEllIntKk_ne_zero hkD
  set W : Set ℂ := {w | jacobiLetterTheta .n (jacobiZetak w k) (jacobiTauk k) ≠ 0}
  have hcont : Continuous fun w => jacobiLetterTheta .n (jacobiZetak w k) (jacobiTauk k) := by
    simp only [p22R1_letter_eq]
    exact continuous_const.mul ((p22R1_differentiable_th .n hτ).continuous.comp
      (by unfold jacobiZetak; fun_prop))
  have hW : IsOpen W := isOpen_ne_fun hcont continuous_const
  have hzW : z ∈ W := by
    intro h0
    have h4 : jacobiThetaFourTau (jacobiZetak z k) (jacobiTauk k) = 0 := by
      simp only [jacobiLetterTheta, div_eq_zero_iff] at h0
      exact h0.resolve_right (je22a_thetaFour_zero_ne_zero hτ)
    obtain ⟨m, n, hmn⟩ := ((DLMF.Theta.jacobiThetaTau_eq_zero_iff hτ _).2.2.2).1 h4
    apply hz m n
    rw [jacobiZetak, jacobiTauk, hK', hK] at hmn
    rw [hK] at hK0
    field_simp at hmn
    linear_combination hmn
  have hdiff : DifferentiableOn ℂ (fun z => jacobiSnk z k) W := fun w hw =>
    (hasDerivAt_jacobiSnk hkD hw).differentiableAt.differentiableWithinAt
  exact hdiff.analyticAt (hW.mem_nhds hzW)

/-- Near a pole `z₀ = 2pK + (2q+1)iK'`: `sn²(z₀ + u, k) = 1/(k² sn²(u, k))`
(Table 22.4.3, `sn(z + iK') = ns(z)/k`, and the periods `2K`, `2iK'` of `sn²`). -/
lemma p1l_sn_sq_pole (hk0 : 0 < k) (hk1 : k < 1) (p q : ℤ) (u : ℂ) :
    jacobiSnk (2 * p * Real.compEllIntKm (k ^ 2) + (2 * q + 1) * I * Real.compEllIntKm (1 - k ^ 2)
      + u) k ^ 2 = 1 / ((k : ℂ) ^ 2 * jacobiSnk u k ^ 2) := by
  have hkD : (k : ℂ) ∈ jacobiModulusDomain := p22R1_ofReal_mem hk0 hk1
  have hK : compEllIntKk (k : ℂ) = (Real.compEllIntKm (k ^ 2) : ℂ) :=
    compEllIntKk_ofReal (by nlinarith)
  have hK' : compEllIntKpk (k : ℂ) = (Real.compEllIntKm (1 - k ^ 2) : ℂ) :=
    compEllIntKpk_ofReal (by positivity)
  have sh := jacobiSnk_shift hkD
  rw [hK, hK'] at sh
  set K : ℂ := (Real.compEllIntKm (k ^ 2) : ℂ)
  set K' : ℂ := (Real.compEllIntKm (1 - k ^ 2) : ℂ)
  have h1 : Function.Periodic (fun w => jacobiSnk w k ^ 2) (2 * K) := fun w => by
    simp only [(sh w).2.2.2.1, neg_sq]
  have h2 : Function.Periodic (fun w => jacobiSnk w k ^ 2) (2 * (I * K')) := fun w => by
    simp only [(sh w).2.2.2.2.2]
  have e : 2 * p * K + (2 * q + 1) * I * K' + u = (u + I * K') + p * (2 * K) + q * (2 * (I * K'))
    := by ring
  have p2 := (h2.int_mul q) (u + I * K' + p * (2 * K))
  have p1 := (h1.int_mul p) (u + I * K')

  rw [e, p2, p1, (sh u).2.2.1, jacobiNsk, jacobiPQk_eq_one_div, ← jacobiSnk]
  field_simp

/-- §29.2(i): for `0 < k < 1` and `ν(ν+1) ≠ 0` the points `2pK + (2q+1)iK'`, `p, q ∈ ℤ`, are
regular singularities of Lamé's equation 29.2.1. Proved from `sn²(z₀ + u) = 1/(k² sn²(u))`
and `sn(u) = u G(u)` with `G` analytic, `G(0) = 1`. -/
@[dlmf 29.2.i]
theorem lame_regularSingularAt (hk0 : 0 < k) (hk1 : k < 1) (hν : ν * (ν + 1) ≠ 0) (h : ℂ)
    (p q : ℤ) :
    Complex.LinearODERegularSingularAt (lameODECoeff h ν k)
      (2 * p * Real.compEllIntKm (k ^ 2) + (2 * q + 1) * I * Real.compEllIntKm (1 - k ^ 2)) := by
  set z₀ : ℂ := 2 * p * Real.compEllIntKm (k ^ 2) + (2 * q + 1) * I * Real.compEllIntKm (1 - k ^ 2)
  have hkD : (k : ℂ) ∈ jacobiModulusDomain := p22R1_ofReal_mem hk0 hk1
  have hk0' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hν' : (ν : ℂ) * (ν + 1) ≠ 0 := by exact_mod_cast hν
  -- `sn` is analytic at `0` with `sn(0) = 0`, `sn'(0) = 1`
  have hK'pos : 0 < Real.compEllIntKm (1 - k ^ 2) := Real.compEllIntKm_pos (by nlinarith)
  have ha0 : AnalyticAt ℂ (fun z => jacobiSnk z k) 0 := by
    refine p1l_analyticAt_sn hk0 hk1 fun p q h0 => ?_
    have := congrArg Complex.im h0
    simp at this
    have : (2 * (q : ℝ) + 1) = 0 := by
      rcases this with h | h
      · exact h
      · exact absurd h hK'pos.ne'
    have : (2 * q + 1 : ℤ) = 0 := by exact_mod_cast this
    omega
  set G := dslope (fun z => jacobiSnk z k) 0
  have hGa : AnalyticAt ℂ G 0 := ha0.dslope 0
  have hG0 : G 0 = 1 := by
    simp only [G, dslope_same]
    rw [(hasDerivAt_jacobiSnk hkD (p1l_regular_at_zero hkD)).deriv, jacobiCnk_zero hkD,
      jacobiDnk_zero hkD, mul_one]
  have hsnG : ∀ u, jacobiSnk u k = u * G u := fun u => by
    have := sub_smul_dslope (fun z => jacobiSnk z k) 0 u
    simp only [sub_zero, smul_eq_mul, jacobiSnk_zero hkD] at this
    exact this.symm
  -- the key formula `(z - z₀)² c₀(z) = (z - z₀)² h - ν(ν+1)/G(z - z₀)²` for `z ≠ z₀`
  have hkey : ∀ z, z ≠ z₀ → (z - z₀) ^ 2 * lameODECoeff h ν k 0 z =
      (z - z₀) ^ 2 * h - ν * (ν + 1) / G (z - z₀) ^ 2 := by
    intro z hz
    have hu : z - z₀ ≠ 0 := sub_ne_zero.2 hz
    have := p1l_sn_sq_pole hk0 hk1 p q (z - z₀)
    rw [show z₀ + (z - z₀) = z by ring] at this
    simp only [lameODECoeff, Matrix.cons_val_zero]
    rw [this, hsnG]
    field_simp
  have hga : AnalyticAt ℂ (fun z => (z - z₀) ^ 2 * h - ν * (ν + 1) / G (z - z₀) ^ 2) z₀ := by
    have hGz : AnalyticAt ℂ (fun z => G (z - z₀)) z₀ :=
      hGa.comp_of_eq (f := fun z => z - z₀) (analyticAt_id.sub analyticAt_const) (by simp)
    refine ((analyticAt_id.sub analyticAt_const).pow 2).mul analyticAt_const |>.sub
      (analyticAt_const.div (hGz.pow 2) ?_)
    simp [hG0]
  refine ⟨fun hord => ?_, fun j => ?_⟩
  · obtain ⟨g, hg, hgeq⟩ := hord 0
    have hlim1 : Tendsto (fun z => (z - z₀) ^ 2 * g z) (𝓝[≠] z₀) (𝓝 ((z₀ - z₀) ^ 2 * g z₀)) :=
      (((continuous_id.sub continuous_const).pow 2).continuousAt.mul
        hg.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    have hlim2 := hga.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {z₀}ᶜ))
    have hev : (fun z => (z - z₀) ^ 2 * g z) =ᶠ[𝓝[≠] z₀]
        fun z => (z - z₀) ^ 2 * h - ν * (ν + 1) / G (z - z₀) ^ 2 := by
      filter_upwards [hgeq, self_mem_nhdsWithin] with z hz hz'
      rw [← hz, hkey z hz']
    have := tendsto_nhds_unique (hlim1.congr' hev) hlim2
    simp [hG0] at this
    exact hν' (mul_eq_zero.2 (this.imp (by exact_mod_cast id) id))
  · fin_cases j
    · exact ⟨_, hga, Filter.eventually_of_mem self_mem_nhdsWithin fun z hz => by
        simpa using hkey z hz⟩
    · refine ⟨fun _ => 0, analyticAt_const, Filter.Eventually.of_forall fun z => ?_⟩
      simp [lameODECoeff]

/-- §29.2(i): every other point is an ordinary point of 29.2.1. Proved from the zeros of `θ₄`
(§20.2(iv)). -/
@[dlmf 29.2.i]
theorem lame_ordinaryAt (hk0 : 0 < k) (hk1 : k < 1) (h z : ℂ)
    (hz : ∀ p q : ℤ,
      z ≠ 2 * p * Real.compEllIntKm (k ^ 2) + (2 * q + 1) * I * Real.compEllIntKm (1 - k ^ 2)) :
    Complex.LinearODEOrdinaryAt (lameODECoeff h ν k) z := by
  have ha := p1l_analyticAt_sn hk0 hk1 hz
  intro j
  refine ⟨lameODECoeff h ν k j, ?_, Filter.EventuallyEq.rfl⟩
  fin_cases j
  · simp only [lameODECoeff, Fin.zero_eta, Matrix.cons_val_zero]
    exact analyticAt_const.sub (analyticAt_const.mul (ha.pow 2))
  · simp only [lameODECoeff, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact analyticAt_const

/-! ### Other forms (§29.2(ii)) -/

/-- Where `sn(z, k) ≠ 0`, the point `z` is not a pole of `sn, cn, dn`. -/
lemma p1l_regular_of_sn_ne_zero {z k : ℂ} (hs : jacobiSnk z k ≠ 0) :
    jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0 := by
  intro h0
  apply hs
  simp [jacobiSnk, jacobiPQk, jacobiGlaisher, h0]

/-- 29.2.2–29.2.3: if `w` solves the algebraic form 29.2.2 on an open set `V` not containing
`0, 1, k⁻²`, then `z ↦ w(sn²(z, k))` solves Lamé's equation 29.2.1 on `{z | sn²(z, k) ∈ V}`.
Proved by the chain rule with `sn' = cn dn` and 22.6.1 (the poles of `sn` are excluded since the
value there is `0 ∉ V`). -/
@[dlmf 29.2.E2, dlmf 29.2.E3]
theorem isLameSolutionOn_comp_sn_sq (hk0 : 0 < k) (hk1 : k < 1) {w : ℂ → ℂ} {V : Set ℂ}
    (hV : IsOpen V) (h0 : (0 : ℂ) ∉ V) (h1 : (1 : ℂ) ∉ V) (h2 : ((k : ℂ) ^ 2)⁻¹ ∉ V)
    (hw : IsLameAlgebraicSolutionOn h ν k w V) :
    IsLameSolutionOn h ν k (fun z => w (jacobiSnk z k ^ 2)) {z | jacobiSnk z k ^ 2 ∈ V} := by
  have hkD : (k : ℂ) ∈ jacobiModulusDomain := p22R1_ofReal_mem hk0 hk1
  have hk0' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hreg : ∀ z, jacobiSnk z k ^ 2 ∈ V →
      jacobiLetterTheta .n (jacobiZetak z k) (jacobiTauk k) ≠ 0 := fun z hz =>
    p1l_regular_of_sn_ne_zero fun hs => h0 (by simpa [hs] using hz)
  have hW : ∀ z, jacobiSnk z k ^ 2 ∈ V → HasDerivAt (fun z => w (jacobiSnk z k ^ 2))
      (deriv w (jacobiSnk z k ^ 2) * (2 * jacobiSnk z k * (jacobiCnk z k * jacobiDnk z k))) z :=
    fun z hz => ((hw.differentiableAt _ hz).hasDerivAt.comp z
      ((hasDerivAt_jacobiSnk hkD (hreg z hz)).pow 2)).congr_deriv (by ring)
  refine ⟨fun z hz => (hW z hz).differentiableAt, fun z hz => ?_⟩
  have hz' := hreg z hz
  set s := jacobiSnk z k
  set c := jacobiCnk z k
  set d := jacobiDnk z k
  have hev : ∀ᶠ y in 𝓝 z, jacobiSnk y k ^ 2 ∈ V :=
    (((hasDerivAt_jacobiSnk hkD hz').continuousAt.pow 2)).preimage_mem_nhds (hV.mem_nhds hz)
  have hderiv : deriv (fun z => w (jacobiSnk z k ^ 2)) =ᶠ[𝓝 z] fun y =>
      deriv w (jacobiSnk y k ^ 2) * (2 * jacobiSnk y k * (jacobiCnk y k * jacobiDnk y k)) :=
    hev.mono fun y hy => (hW y hy).deriv
  have hs := hasDerivAt_jacobiSnk hkD hz'
  have hc := hasDerivAt_jacobiCnk hkD hz'
  have hd := hasDerivAt_jacobiDnk hkD hz'
  have hG := ((hw.hasDerivAt_deriv _ hz).comp z (hs.pow 2)).mul
    ((hs.const_mul 2).mul (hc.mul hd))
  refine (hG.congr_of_eventuallyEq hderiv).congr_deriv ?_
  obtain ⟨e1, e2⟩ := jacobi_sq_sum hkD hz'
  have hξ0 : s ^ 2 ≠ 0 := fun h' => h0 (h' ▸ hz)
  have hξ1 : s ^ 2 - 1 ≠ 0 := fun h' => h1 (by rw [← sub_eq_zero.1 h']; exact hz)
  have hξk : s ^ 2 - ((k : ℂ) ^ 2)⁻¹ ≠ 0 := fun h' => h2 (by rw [← sub_eq_zero.1 h']; exact hz)
  have hs0 : s ≠ 0 := fun h' => hξ0 (by rw [h']; ring)
  set κ : ℂ := ((k : ℂ) ^ 2)⁻¹ with hκdef
  have hκ : κ * (k : ℂ) ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hk0')
  set A := deriv w (s ^ 2)
  set B := w (s ^ 2)
  set E := -(1 / 2 * (1 / s ^ 2 + 1 / (s ^ 2 - 1) + 1 / (s ^ 2 - κ)) * A) -
      ((h : ℂ) * κ - ν * (ν + 1) * s ^ 2) / (4 * s ^ 2 * (s ^ 2 - 1) * (s ^ 2 - κ)) * B
  have q1 : E * (4 * s ^ 2 * (s ^ 2 - 1) * (s ^ 2 - κ)) =
      -2 * ((s ^ 2 - 1) * (s ^ 2 - κ) + s ^ 2 * (s ^ 2 - κ) + s ^ 2 * (s ^ 2 - 1)) * A -
        ((h : ℂ) * κ - ν * (ν + 1) * s ^ 2) * B := by
    simp only [E]
    field_simp
    ring
  have step : E * (4 * s ^ 2 * (1 - s ^ 2) * (1 - k ^ 2 * s ^ 2)) +
      A * (2 * ((1 - s ^ 2) * (1 - k ^ 2 * s ^ 2) - s ^ 2 * (1 - k ^ 2 * s ^ 2) -
        k ^ 2 * s ^ 2 * (1 - s ^ 2))) = -(h - ν * (ν + 1) * k ^ 2 * s ^ 2) * B := by
    linear_combination (k : ℂ) ^ 2 * q1 +
      (-4 * E * s ^ 2 * (1 - s ^ 2) - 2 * (1 - 2 * s ^ 2) * A - h * B) * hκ
  simp only [Pi.mul_apply, Pi.pow_apply, Function.comp_apply, show (2 : ℕ) - 1 = 1 from rfl,
    pow_one]
  linear_combination step + E * 4 * s ^ 2 * ((1 - s ^ 2) * e2 + d ^ 2 * e1) +
    A * (2 * ((1 - s ^ 2) * e2 + d ^ 2 * e1) - 2 * s ^ 2 * e2 - 2 * k ^ 2 * s ^ 2 * e1)

/-- 29.2.4–29.2.5: if `W` solves the trigonometric form 29.2.4 on `ℝ`, then
`x ↦ W(φ(x))`, `φ = π/2 - am(x, k)`, solves Lamé's equation 29.2.1 on `ℝ`. -/
@[dlmf 29.2.E4, dlmf 29.2.E5]
theorem Real.isLameSolution_comp_lamePhi (hk0 : 0 < k) (hk1 : k < 1) {W : ℝ → ℝ}
    (hW : Real.IsLameTrigSolution h ν k W) :
    Real.IsLameSolution h ν k (fun x => W (Real.lamePhi x k)) := by
  have hm : k ^ 2 < 1 := l29_sq_lt_one hk0 hk1
  have hφ : ∀ x, HasDerivAt (fun x => Real.lamePhi x k) (-Real.jacobiDnm x (k ^ 2)) x := by
    intro x
    have := (Real.hasDerivAt_jacobiAmm hm x).const_sub (π / 2)
    simpa [Real.lamePhi, Real.jacobiDnm, Real.jacobiSnm] using this
  have h1 : ∀ x, HasDerivAt (fun x => W (Real.lamePhi x k))
      (deriv W (Real.lamePhi x k) * -Real.jacobiDnm x (k ^ 2)) x :=
    fun x => (hW.differentiable _).hasDerivAt.comp x (hφ x)
  have hderiv : deriv (fun x => W (Real.lamePhi x k)) =
      fun x => deriv W (Real.lamePhi x k) * -Real.jacobiDnm x (k ^ 2) :=
    funext fun x => (h1 x).deriv
  refine ⟨fun x => (h1 x).differentiableAt, fun x => ?_⟩
  rw [hderiv]
  have h2 := ((hW.differentiable_deriv _).hasDerivAt.comp x (hφ x)).mul
    (Real.hasDerivAt_jacobiDnm hm x).neg
  refine h2.congr_deriv ?_
  have hode := hW.ode (Real.lamePhi x k)
  have hcos : Real.cos (Real.lamePhi x k) = Real.jacobiSnm x (k ^ 2) := by
    simp [Real.lamePhi, Real.cos_pi_div_two_sub, Real.jacobiSnm]
  have hsin : Real.sin (Real.lamePhi x k) = Real.jacobiCnm x (k ^ 2) := by
    simp [Real.lamePhi, Real.sin_pi_div_two_sub, Real.jacobiCnm]
  have hdn := Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm x
  rw [hcos, hsin] at hode
  simp only [Function.comp_apply, Pi.neg_apply]
  linear_combination hode + deriv (deriv W) (Real.lamePhi x k) * hdn

/-- 29.2.6–29.2.9 and 29.2.12: let `e₁ > e₂ > e₃` be real with `e₁ + e₂ + e₃ = 0` and
`(e₂ - e₃)/(e₁ - e₃) = k²`, `g = (e₁ - e₃)h + ν(ν+1)e₃` (29.2.7), `η = (e₁-e₃)^{-1/2}(z - iK')`
(29.2.8) and `g₂ = -4(e₂e₃ + e₃e₁ + e₁e₂)`, `g₃ = 4e₁e₂e₃` (29.2.12). If `w` solves Lamé's
equation 29.2.1 on `U`, then `η ↦ w((e₁-e₃)^{1/2} η + iK')` solves the Weierstrass form 29.2.9
on the corresponding set. Proved in `DLMF.Lame.P3lWeierstrass` (`p3l_weierstrass`). -/
@[dlmf 29.2.E6, dlmf 29.2.E7, dlmf 29.2.E8, dlmf 29.2.E9, dlmf 29.2.E12]
theorem isLameWeierstrassSolutionOn_of_isLameSolutionOn (hk0 : 0 < k) (hk1 : k < 1)
    {e₁ e₂ e₃ : ℝ} (h12 : e₂ < e₁) (h23 : e₃ < e₂) (hsum : e₁ + e₂ + e₃ = 0)
    (hk2 : (e₂ - e₃) / (e₁ - e₃) = k ^ 2) {w : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hw : IsLameSolutionOn h ν k w U) :
    IsLameWeierstrassSolutionOn ((e₁ - e₃) * h + ν * (ν + 1) * e₃) ν
      (-4 * (e₂ * e₃ + e₃ * e₁ + e₁ * e₂)) (4 * e₁ * e₂ * e₃)
      (fun η => w (Real.sqrt (e₁ - e₃) * η + I * Real.compEllIntKm (1 - k ^ 2)))
      {η | (Real.sqrt (e₁ - e₃) : ℂ) * η + I * Real.compEllIntKm (1 - k ^ 2) ∈ U} :=
  p3l_weierstrass hk0 hk1 h12 h23 hsum hk2 hU hw

open PeriodPair in
/-- 29.2.10–29.2.11: if `v` solves the algebraic Weierstrass form 29.2.10 on an open set `V`
not containing `e₁, e₂, e₃`, then `η ↦ v(℘(η; g₂, g₃))` (`ζ = ℘(η)`, 29.2.11) solves 29.2.9 on
any open set `U` on which `℘` is holomorphic with values in `V`. Proved from 23.3.10 and 23.3.12
(`PeriodPair.derivWeierstrassP_sq`, `DLMF.Weierstrass.deriv_derivWeierstrassP`); it uses the
admitted existence of a lattice with given invariants (`periodPairOfInvariants_spec`). -/
@[dlmf 29.2.E10, dlmf 29.2.E11]
theorem isLameWeierstrassSolutionOn_comp_wp {e₁ e₂ e₃ : ℝ} (h12 : e₂ < e₁) (h23 : e₃ < e₂)
    (hsum : e₁ + e₂ + e₃ = 0) {g : ℂ} {v : ℂ → ℂ} {V U : Set ℂ}
    (he : (e₁ : ℂ) ∉ V ∧ (e₂ : ℂ) ∉ V ∧ (e₃ : ℂ) ∉ V) (hU : IsOpen U)
    (hwp : ∀ η ∈ U, DifferentiableAt ℂ
      (DLMF.Weierstrass.weierstrassPInvariants (-4 * (e₂ * e₃ + e₃ * e₁ + e₁ * e₂))
        (4 * e₁ * e₂ * e₃)) η ∧
      DLMF.Weierstrass.weierstrassPInvariants (-4 * (e₂ * e₃ + e₃ * e₁ + e₁ * e₂))
        (4 * e₁ * e₂ * e₃) η ∈ V)
    (hv : IsLameWeierstrassAlgebraicSolutionOn g ν e₁ e₂ e₃ v V) :
    IsLameWeierstrassSolutionOn g ν (-4 * (e₂ * e₃ + e₃ * e₁ + e₁ * e₂)) (4 * e₁ * e₂ * e₃)
      (fun η => v (DLMF.Weierstrass.weierstrassPInvariants
        (-4 * (e₂ * e₃ + e₃ * e₁ + e₁ * e₂)) (4 * e₁ * e₂ * e₃) η)) U := by
  set g₂ : ℂ := -4 * (e₂ * e₃ + e₃ * e₁ + e₁ * e₂)
  set g₃ : ℂ := 4 * e₁ * e₂ * e₃
  set L := DLMF.Weierstrass.periodPairOfInvariants g₂ g₃
  have hs : (e₁ : ℂ) = -e₂ - e₃ := by
    have : (e₁ : ℂ) + e₂ + e₃ = 0 := by exact_mod_cast hsum
    linear_combination this
  have hΔ : g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0 := by
    have hd : g₂ ^ 3 - 27 * g₃ ^ 2 =
        16 * ((e₁ - e₂ : ℂ) * (e₂ - e₃) * (e₁ - e₃)) ^ 2 := by
      simp only [g₂, g₃]; rw [hs]; ring
    rw [hd]
    have h1 : (e₁ - e₂ : ℂ) ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast h12.ne'
    have h2 : (e₂ - e₃ : ℂ) ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast h23.ne'
    have h3 : (e₁ - e₃ : ℂ) ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast (h23.trans h12).ne'
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero h1 h2) h3))
  obtain ⟨hg₂, hg₃⟩ := DLMF.Weierstrass.periodPairOfInvariants_spec g₂ g₃ hΔ
  have hP : DLMF.Weierstrass.weierstrassPInvariants g₂ g₃ = ℘[L] := rfl
  rw [hP] at hwp ⊢
  have hnot : ∀ η ∈ U, η ∉ L.lattice := fun η hη hl =>
    L.not_continuousAt_weierstrassP η hl (hwp η hη).1.continuousAt
  have hW : ∀ η ∈ U, HasDerivAt (fun η => v (℘[L] η)) (deriv v (℘[L] η) * ℘'[L] η) η := by
    intro η hη
    have h1 := (hwp η hη).1.hasDerivAt
    rw [PeriodPair.deriv_weierstrassP] at h1
    exact (hv.differentiableAt _ (hwp η hη).2).hasDerivAt.comp η h1
  refine ⟨fun η hη => (hW η hη).differentiableAt, fun η hη => ?_⟩
  rw [hP]
  have hderiv : deriv (fun η => v (℘[L] η)) =ᶠ[𝓝 η] fun y => deriv v (℘[L] y) * ℘'[L] y :=
    Filter.eventually_of_mem (hU.mem_nhds hη) fun y hy => (hW y hy).deriv
  have h1 := (hwp η hη).1.hasDerivAt
  rw [PeriodPair.deriv_weierstrassP] at h1
  have h2 : HasDerivAt ℘'[L] (6 * ℘[L] η ^ 2 - L.g₂ / 2) η := by
    have := (L.analyticOnNhd_derivWeierstrassP η (hnot η hη)).differentiableAt.hasDerivAt
    rwa [DLMF.Weierstrass.deriv_derivWeierstrassP L (hnot η hη)] at this
  have hG := ((hv.hasDerivAt_deriv _ (hwp η hη).2).comp η h1).mul h2
  refine (hG.congr_of_eventuallyEq hderiv).congr_deriv ?_
  have hsq := L.derivWeierstrassP_sq η (hnot η hη)
  have hg₂' : L.g₂ = g₂ := hg₂
  have hg₃' : L.g₃ = g₃ := hg₃
  rw [hg₂', hg₃'] at hsq
  rw [hg₂']
  set ζ := ℘[L] η
  have hζ := (hwp η hη).2
  have z1 : ζ - e₁ ≠ 0 := fun h' => he.1 (by rw [← sub_eq_zero.1 h']; exact hζ)
  have z2 : ζ - e₂ ≠ 0 := fun h' => he.2.1 (by rw [← sub_eq_zero.1 h']; exact hζ)
  have z3 : ζ - e₃ ≠ 0 := fun h' => he.2.2 (by rw [← sub_eq_zero.1 h']; exact hζ)
  have hsq' : ℘'[L] η ^ 2 = 4 * ((ζ - e₁) * (ζ - e₂) * (ζ - e₃)) := by
    rw [hsq]; simp only [g₂, g₃]; rw [hs]; ring
  simp only [Function.comp_apply]
  set A := deriv v ζ
  set B := v ζ
  set P := ℘'[L] η
  rw [show (-(1 / 2 * (1 / (ζ - e₁) + 1 / (ζ - e₂) + 1 / (ζ - e₃)) * A) -
      (g - ν * (ν + 1) * ζ) / (4 * (ζ - e₁) * (ζ - e₂) * (ζ - e₃)) * B) * P * P =
      (-(1 / 2 * (1 / (ζ - e₁) + 1 / (ζ - e₂) + 1 / (ζ - e₃)) * A) -
      (g - ν * (ν + 1) * ζ) / (4 * (ζ - e₁) * (ζ - e₂) * (ζ - e₃)) * B) * P ^ 2 by ring, hsq']
  field_simp
  simp only [g₂]
  rw [hs]
  ring

/-- §29.2(ii): the algebraic form 29.2.2 is Heun's equation 31.2.1 with `a = k⁻²`,
`q = -hk⁻²/4`, `α = -ν/2`, `β = (ν+1)/2`, `γ = δ = ε = 1/2`. DLMF states this for 29.2.10,
which is 29.2.2 after the affine change `ζ = e₃ + (e₁ - e₃)ξ`. -/
@[dlmf 29.2.ii "29.2.2 as Heun's equation (DLMF states it for the equivalent 29.2.10)"]
theorem isLameAlgebraicSolutionOn_iff_isHeunSolOn {h ν k : ℂ} {w : ℂ → ℂ} {U : Set ℂ} :
    IsLameAlgebraicSolutionOn h ν k w U ↔
      DLMF.Heun.IsHeunSolOn (k ^ 2)⁻¹ (-(h * (k ^ 2)⁻¹) / 4) (-ν / 2) ((ν + 1) / 2) (1 / 2)
        (1 / 2) (1 / 2) w U := by
  constructor
  · intro hw
    refine ⟨hw.differentiableAt, fun z hz => (hw.hasDerivAt_deriv z hz).congr_deriv ?_⟩
    simp only [DLMF.Heun.heunCoeffP, DLMF.Heun.heunCoeffR]
    rw [show ∀ x : ℂ, x / (4 * z * (z - 1) * (z - (k ^ 2)⁻¹)) =
      x / 4 / (z * (z - 1) * (z - (k ^ 2)⁻¹)) from fun x => by rw [div_div]; congr 1; ring]
    ring
  · intro hw
    refine ⟨hw.differentiableAt, fun z hz => (hw.hasDerivAt_deriv z hz).congr_deriv ?_⟩
    simp only [DLMF.Heun.heunCoeffP, DLMF.Heun.heunCoeffR]
    rw [show ∀ x : ℂ, x / (4 * z * (z - 1) * (z - (k ^ 2)⁻¹)) =
      x / 4 / (z * (z - 1) * (z - (k ^ 2)⁻¹)) from fun x => by rw [div_div]; congr 1; ring]
    ring

/-! ### Imaginary periods (§29.10) -/

/-- `k' = √(1 - k²)` as the complex comodulus of a real modulus. -/
lemma p2l_comod_ofReal {x : ℝ} (hx : x ^ 2 ≤ 1) :
    jacobiComodulusk (x : ℂ) = ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) := by
  rw [jacobiComodulusk, show (1 - (x : ℂ) ^ 2) = ((1 - x ^ 2 : ℝ) : ℂ) by push_cast; ring,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by linarith), Real.sqrt_eq_rpow]

/-- The imaginary transformation behind 29.10: with `k' = √(1 - k²)`,
`k'² sn²(i(z - K - iK'), k') = dn²(z, k)` (identically, including Lean's junk values). -/
lemma p2l_comod_sq_sn_imag (hk0 : 0 < k) (hk1 : k < 1) (z : ℂ) :
    ((Real.sqrt (1 - k ^ 2) : ℝ) : ℂ) ^ 2 *
      jacobiSnk (I * (z - Real.compEllIntKm (k ^ 2) - I * Real.compEllIntKm (1 - k ^ 2)))
        ((Real.sqrt (1 - k ^ 2) : ℝ) : ℂ) ^ 2 = jacobiDnk z k ^ 2 := by
  obtain ⟨hc0, hc1, hc2⟩ := l29_comodulus hk0 hk1
  set c := Real.sqrt (1 - k ^ 2)
  have hkD : (k : ℂ) ∈ jacobiModulusDomain := p22R1_ofReal_mem hk0 hk1
  have hcD : (c : ℂ) ∈ jacobiModulusDomain := p22R1_ofReal_mem hc0 hc1
  have hKc : compEllIntKk (c : ℂ) = (Real.compEllIntKm (1 - k ^ 2) : ℂ) := by
    rw [compEllIntKk_ofReal (by nlinarith), hc2]
  have hK : compEllIntKk (k : ℂ) = (Real.compEllIntKm (k ^ 2) : ℂ) :=
    compEllIntKk_ofReal (by nlinarith)
  have hcc : jacobiComodulusk (c : ℂ) = k := by
    rw [p2l_comod_ofReal (by nlinarith), hc2, show 1 - (1 - k ^ 2) = k ^ 2 by ring,
      Real.sqrt_sq hk0.le]
  have hck : jacobiComodulusk (k : ℂ) = c := p2l_comod_ofReal (by nlinarith)
  have hc0' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  rw [show I * (z - Real.compEllIntKm (k ^ 2) - I * Real.compEllIntKm (1 - k ^ 2)) =
      I * (z - Real.compEllIntKm (k ^ 2)) + compEllIntKk (c : ℂ) by
    rw [hKc]; ring_nf; rw [I_sq]; ring,
    (jacobiSnk_shift hcD _).1, ((jacobi_imaginary_transformation hcD _).2.2.2.1), hcc]
  have hd := (jacobiDnk_shift hkD (z - Real.compEllIntKm (k ^ 2))).1
  rw [hK, sub_add_cancel, hck] at hd
  rw [hd]
  ring

/-- A solution of Lamé's equation on an open set containing a pole `2pK + (2q+1)iK'` of `sn`
vanishes there (for `ν(ν+1) ≠ 0`). -/
lemma p2l_lame_eq_zero_at_pole (hk0 : 0 < k) (hk1 : k < 1) {a b : ℂ} {w : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hw : IsLameSolutionOn a b k w U) (hb : b * (b + 1) ≠ 0) (p q : ℤ)
    (hz : (2 * p * Real.compEllIntKm (k ^ 2) + (2 * q + 1) * I * Real.compEllIntKm (1 - k ^ 2) :
      ℂ) ∈ U) :
    w (2 * p * Real.compEllIntKm (k ^ 2) + (2 * q + 1) * I * Real.compEllIntKm (1 - k ^ 2)) =
      0 := by
  set z₀ : ℂ := 2 * p * Real.compEllIntKm (k ^ 2) + (2 * q + 1) * I * Real.compEllIntKm (1 - k ^ 2)
  have hkD : (k : ℂ) ∈ jacobiModulusDomain := p22R1_ofReal_mem hk0 hk1
  have hk0' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hK'pos : 0 < Real.compEllIntKm (1 - k ^ 2) := Real.compEllIntKm_pos (by nlinarith)
  have ha0 : AnalyticAt ℂ (fun z => jacobiSnk z k) 0 := by
    refine p1l_analyticAt_sn hk0 hk1 fun p q h0 => ?_
    have := congrArg Complex.im h0
    simp at this
    have : (2 * (q : ℝ) + 1) = 0 := by
      rcases this with h | h
      · exact h
      · exact absurd h hK'pos.ne'
    have : (2 * q + 1 : ℤ) = 0 := by exact_mod_cast this
    omega
  set G := dslope (fun z => jacobiSnk z k) 0
  have hGa : AnalyticAt ℂ G 0 := ha0.dslope 0
  have hG0 : G 0 = 1 := by
    simp only [G, dslope_same]
    rw [(hasDerivAt_jacobiSnk hkD (p1l_regular_at_zero hkD)).deriv, jacobiCnk_zero hkD,
      jacobiDnk_zero hkD, mul_one]
  have hsnG : ∀ u, jacobiSnk u k = u * G u := fun u => by
    have := sub_smul_dslope (fun z => jacobiSnk z k) 0 u
    simp only [sub_zero, smul_eq_mul, jacobiSnk_zero hkD] at this
    exact this.symm
  have hd1 : DifferentiableOn ℂ (deriv w) U := fun z hz =>
    (hw.hasDerivAt_deriv z hz).differentiableAt.differentiableWithinAt
  have hw2 : ContinuousAt (deriv (deriv w)) z₀ :=
    ((hd1.analyticAt (hU.mem_nhds hz)).deriv).continuousAt
  have hw0 : ContinuousAt w z₀ := (hw.differentiableAt z₀ hz).continuousAt
  set R : ℂ → ℂ := fun u => u ^ 2 * G u ^ 2 *
    (deriv (deriv w) (z₀ + u) + a * w (z₀ + u)) / (b * (b + 1))
  have hR : Tendsto R (𝓝[≠] 0) (𝓝 0) := by
    have hc : ContinuousAt R 0 := by
      have h1 : ContinuousAt (fun u : ℂ => z₀ + u) 0 := by fun_prop
      have h2 : ContinuousAt (fun u => deriv (deriv w) (z₀ + u)) 0 :=
        ContinuousAt.comp (g := deriv (deriv w)) (by simpa using hw2) h1
      have h3 : ContinuousAt (fun u => w (z₀ + u)) 0 :=
        ContinuousAt.comp (g := w) (by simpa using hw0) h1
      exact ((((continuousAt_id.pow 2).mul (hGa.continuousAt.pow 2)).mul
        (h2.add (continuousAt_const.mul h3))).div_const _)
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    simpa [R] using this
  have hF : Tendsto (fun u => w (z₀ + u)) (𝓝[≠] 0) (𝓝 (w z₀)) := by
    have h1 : Tendsto (fun u : ℂ => z₀ + u) (𝓝 0) (𝓝 z₀) := by
      exact (continuous_const.add continuous_id).tendsto' 0 z₀ (add_zero _)
    exact (hw0.tendsto.comp h1).mono_left nhdsWithin_le_nhds
  have hev : (fun u => w (z₀ + u)) =ᶠ[𝓝[≠] 0] R := by
    have hU' : ∀ᶠ u in 𝓝 (0 : ℂ), z₀ + u ∈ U := by
      have h1 : Tendsto (fun u : ℂ => z₀ + u) (𝓝 0) (𝓝 z₀) := by
        exact (continuous_const.add continuous_id).tendsto' 0 z₀ (add_zero _)
      exact h1 (hU.mem_nhds hz)
    have hG' : ∀ᶠ u in 𝓝 (0 : ℂ), G u ≠ 0 :=
      hGa.continuousAt.eventually_ne (by rw [hG0]; exact one_ne_zero)
    filter_upwards [nhdsWithin_le_nhds hU', nhdsWithin_le_nhds hG', self_mem_nhdsWithin]
      with u hu hGu hu0
    have hu0' : u ≠ 0 := hu0
    have hpole := p1l_sn_sq_pole hk0 hk1 p q u
    have hode := (hw.hasDerivAt_deriv _ hu).deriv
    rw [hpole, hsnG] at hode
    simp only [R]
    rw [hode, eq_div_iff hb]
    field_simp
    ring
  exact tendsto_nhds_unique (hF.congr' hev) hR

/-- 29.10.1–29.10.3: with `h = ν(ν+1) - h'` and `z' = i(z - K - iK')`, a solution `w` of
Lamé's equation with modulus `k' = √(1 - k²)` and eigenparameter `h'` (29.10.3) gives the
solution `z ↦ w(i(z - K - iK'))` of 29.2.1 with modulus `k` and parameter `h`. Proved from
`k'² sn²(z', k') = dn²(z, k)` (Jacobi's imaginary transformation and Table 22.4.3,
`p2l_comod_sq_sn_imag`); at the poles of `sn(z, k)` the solution `w` vanishes
(`p2l_lame_eq_zero_at_pole`). -/
@[dlmf 29.10.E1, dlmf 29.10.E2, dlmf 29.10.E3]
theorem isLameSolutionOn_imaginary (hk0 : 0 < k) (hk1 : k < 1) {h' : ℂ} {w : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hw : IsLameSolutionOn h' ν (Real.sqrt (1 - k ^ 2)) w U) :
    IsLameSolutionOn (ν * (ν + 1) - h') ν k
      (fun z => w (I * (z - Real.compEllIntKm (k ^ 2) - I * Real.compEllIntKm (1 - k ^ 2))))
      {z | I * (z - Real.compEllIntKm (k ^ 2) - I * Real.compEllIntKm (1 - k ^ 2)) ∈ U} := by
  obtain ⟨hc0, hc1, hc2⟩ := l29_comodulus hk0 hk1
  set c := Real.sqrt (1 - k ^ 2)
  have hkD : (k : ℂ) ∈ jacobiModulusDomain := p22R1_ofReal_mem hk0 hk1
  set φ : ℂ → ℂ := fun z => I * (z - Real.compEllIntKm (k ^ 2) - I * Real.compEllIntKm (1 - k ^ 2))
  have hφ : ∀ z, HasDerivAt φ I z := fun z => by
    simpa using (((hasDerivAt_id z).sub_const _).sub_const _).const_mul I
  have hS : IsOpen {z | φ z ∈ U} := hU.preimage (by fun_prop)
  have hf : ∀ z ∈ {z | φ z ∈ U}, HasDerivAt (fun z => w (φ z)) (deriv w (φ z) * I) z :=
    fun z hz => (hw.differentiableAt (φ z) hz).hasDerivAt.comp z (hφ z)
  refine ⟨fun z hz => (hf z hz).differentiableAt, fun z hz => ?_⟩
  have hev : deriv (fun z => w (φ z)) =ᶠ[𝓝 z] fun y => deriv w (φ y) * I := by
    filter_upwards [hS.mem_nhds hz] with y hy using (hf y hy).deriv
  have h2 := ((hw.hasDerivAt_deriv (φ z) hz).comp z (hφ z)).mul_const I
  refine (h2.congr_of_eventuallyEq hev).congr_deriv ?_
  have hkey : (ν : ℂ) * (ν + 1) * (1 - k ^ 2 * jacobiSnk z k ^ 2 -
      (c : ℂ) ^ 2 * jacobiSnk (φ z) c ^ 2) * w (φ z) = 0 := by
    by_cases hpole : ∀ p q : ℤ,
        z ≠ 2 * p * Real.compEllIntKm (k ^ 2) + (2 * q + 1) * I * Real.compEllIntKm (1 - k ^ 2)
    · have hreg := p2p_regular hk0 hk1 hpole
      rw [p2l_comod_sq_sn_imag hk0 hk1 z, ← (jacobi_sq_sum hkD hreg).2]
      ring
    · simp only [not_forall, not_not] at hpole
      obtain ⟨p, q, hpq⟩ := hpole
      by_cases hb : (ν : ℂ) * (ν + 1) = 0
      · rw [hb]; ring
      have e : φ z = 2 * ((-q : ℤ) : ℂ) * (Real.compEllIntKm (c ^ 2) : ℂ) +
          (2 * ((p - 1 : ℤ) : ℂ) + 1) * I * (Real.compEllIntKm (1 - c ^ 2) : ℂ) := by
        rw [hc2, show 1 - (1 - k ^ 2) = k ^ 2 by ring]
        simp only [φ, hpq]
        push_cast
        ring_nf
        rw [I_sq]
        ring
      have hz' : φ z ∈ U := hz
      rw [e] at hz'
      rw [show w (φ z) = 0 by rw [e]; exact p2l_lame_eq_zero_at_pole hc0 hc1 hU hw hb _ _ hz',
        mul_zero]
  linear_combination hkey + (-(h' - ν * (ν + 1) * (c : ℂ) ^ 2 *
    jacobiSnk (φ z) c ^ 2) * w (φ z)) * I_sq

/-- On the line `Re z = K`: `k'² sn²(K' - s, k') = 1 - k² sn²(K + is, k)` for real `s`, in the
form used for 29.10.4 (`sn(K + is, k) = 1/dn(s, k')`, `sn(K' - s, k') = cn(s, k')/dn(s, k')`). -/
lemma p1l_sn_line (hk0 : 0 < k) (hk1 : k < 1) (s : ℝ) :
    jacobiSnk ((Real.compEllIntKm (k ^ 2) : ℂ) + I * s) k =
        1 / (Real.jacobiDnm s (Real.sqrt (1 - k ^ 2) ^ 2) : ℂ) ∧
      (Real.jacobiSnm (Real.compEllIntKm (1 - k ^ 2) - s) (Real.sqrt (1 - k ^ 2) ^ 2) : ℂ) =
        (Real.jacobiCnm s (Real.sqrt (1 - k ^ 2) ^ 2) : ℂ) /
          (Real.jacobiDnm s (Real.sqrt (1 - k ^ 2) ^ 2) : ℂ) := by
  obtain ⟨h0, h1, h2⟩ := l29_comodulus hk0 hk1
  set k' := Real.sqrt (1 - k ^ 2)
  have hkD : (k : ℂ) ∈ jacobiModulusDomain := p22R1_ofReal_mem hk0 hk1
  have hk'D : (k' : ℂ) ∈ jacobiModulusDomain := p22R1_ofReal_mem h0 h1
  have hcomod : jacobiComodulusk (k : ℂ) = k' := by
    rw [jacobiComodulusk, show (1 - (k : ℂ) ^ 2) = ((1 - k ^ 2 : ℝ) : ℂ) by push_cast; ring,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by nlinarith)]
    simp only [k', Real.sqrt_eq_rpow]
  have hreg := p22R1_reg_real h0 h1 s
  constructor
  · rw [show (Real.compEllIntKm (k ^ 2) : ℂ) + I * s = I * s + compEllIntKk (k : ℂ) by
      rw [compEllIntKk_ofReal (by nlinarith)]; ring, (jacobiSnk_shift hkD _).1,
      (jacobi_imaginary_transformation hkD s).2.2.2.1, hcomod, jacobiNdk, jacobiPQk_eq_one_div,
      ← jacobiDnk, jacobiDnk_ofReal h0 h1]
  · rw [← jacobiSnk_ofReal h0 h1, ← jacobiCnk_ofReal h0 h1, ← jacobiDnk_ofReal h0 h1]
    have hK : compEllIntKk (k' : ℂ) = (Real.compEllIntKm (1 - k ^ 2) : ℂ) := by
      rw [compEllIntKk_ofReal (by nlinarith), h2]
    push_cast
    rw [show (Real.compEllIntKm (1 - k ^ 2) : ℂ) - s = -s + compEllIntKk (k' : ℂ) by
      rw [hK]; ring, (jacobiSnk_shift hk'D _).1]
    have hneg := jacobiPQk_neg .c .d (s : ℂ) k'
    simp only [reduceCtorEq, ne_eq, not_true_eq_false, ↓reduceIte] at hneg
    rw [jacobiCdk, hneg, jacobiCnk, jacobiDnk]
    exact jacobiPQk_eq_div (p := .c) (q := .d) (r := .n) (by decide) (by decide) (by decide) hreg

/-- The computation behind 29.10.4 for any real solution `f` of Lamé's equation with modulus
`k' = √(1 - k²)`. -/
lemma p1l_imaginary_solution (hk0 : 0 < k) (hk1 : k < 1) {a : ℝ} {f : ℝ → ℝ}
    (hf : Real.IsLameSolution a ν (Real.sqrt (1 - k ^ 2)) f) (s : ℝ) :
    -(deriv (deriv fun s => f (Real.compEllIntKm (1 - k ^ 2) - s)) s : ℂ) +
      ((ν * (ν + 1) - a : ℝ) -
        ν * (ν + 1) * k ^ 2 * jacobiSnk (Real.compEllIntKm (k ^ 2) + I * s) k ^ 2) *
      f (Real.compEllIntKm (1 - k ^ 2) - s) = 0 := by
  obtain ⟨h0, h1, h2⟩ := l29_comodulus hk0 hk1
  obtain ⟨e1, e2⟩ := p1l_sn_line hk0 hk1 s
  generalize Real.sqrt (1 - k ^ 2) = k' at hf h0 h1 h2 e1 e2 ⊢
  generalize Real.compEllIntKm (1 - k ^ 2) = K' at e2 ⊢
  have hl : ∀ y : ℝ, HasDerivAt (fun s => K' - s) (-1) y := fun y => by
    simpa using (hasDerivAt_id y).const_sub K'
  have hd1 : deriv (fun s => (f (K' - s) : ℂ)) = fun y => ((-deriv f (K' - y) : ℝ) : ℂ) := by
    funext y
    exact (((hf.differentiable _).hasDerivAt.comp y (hl y)).congr_deriv
      (by ring)).ofReal_comp.deriv
  have hd2 : deriv (fun y => ((-deriv f (K' - y) : ℝ) : ℂ)) s =
      ((-(a - ν * (ν + 1) * k' ^ 2 * Real.jacobiSnm (K' - s) (k' ^ 2) ^ 2) * f (K' - s) : ℝ) :
        ℂ) :=
    (((hf.hasDerivAt_deriv (K' - s)).comp s (hl s)).neg.congr_deriv
      (by ring)).ofReal_comp.deriv
  rw [hd1, hd2, e1]
  have hsq : (Real.jacobiSnm (K' - s) (k' ^ 2) : ℂ) ^ 2 =
      (Real.jacobiCnm s (k' ^ 2) : ℂ) ^ 2 / (Real.jacobiDnm s (k' ^ 2) : ℂ) ^ 2 := by
    rw [e2, div_pow]
  have hm : k' ^ 2 < 1 := by nlinarith
  have hdn : (Real.jacobiDnm s (k' ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.jacobiDnm_pos hm s).ne'
  have hsc : (Real.jacobiSnm s (k' ^ 2) : ℂ) ^ 2 + (Real.jacobiCnm s (k' ^ 2) : ℂ) ^ 2 = 1 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) (Real.jacobiSnm_sq_add_jacobiCnm_sq s (k' ^ 2))
    simpa only [ofReal_add, ofReal_pow, ofReal_one] using h
  have hsd : ((k' ^ 2 : ℝ) : ℂ) * (Real.jacobiSnm s (k' ^ 2) : ℂ) ^ 2 +
      (Real.jacobiDnm s (k' ^ 2) : ℂ) ^ 2 = 1 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) (Real.mul_jacobiSnm_sq_add_jacobiDnm_sq hm s)
    simpa only [ofReal_add, ofReal_mul, ofReal_pow, ofReal_one] using h
  have hk2 : ((k' ^ 2 : ℝ) : ℂ) = 1 - (k : ℂ) ^ 2 := by rw [h2]; push_cast; ring
  rw [hk2] at hsd
  push_cast
  rw [hsq]
  field_simp
  rw [show ((k' : ℂ)) ^ 2 = 1 - (k : ℂ) ^ 2 by rw [← hk2]; push_cast; ring]
  linear_combination (-(ν : ℂ) * (ν + 1) * (f (K' - s) : ℂ)) * ((1 - (k : ℂ) ^ 2) * hsc - hsd)

/-- 29.10.4, `Ec`: on the line `z = K + is`, `s ∈ ℝ`, the function
`Ec^m_ν(i(z - K - iK'), k'²) = Ec^m_ν(K' - s, k'²)` solves Lamé's equation 29.2.1 with
`h = ν(ν+1) - a^m_ν(k'²)`: `-v''(s) + (h - ν(ν+1)k² sn²(K + is, k)) v(s) = 0`.
Special case: DLMF's complex `z`, here restricted to the line `Re z = K` on which the
argument is real. Proved from `sn(K + is, k) = nd(s, k')` (Tables 22.4.3 and 22.6.1). -/
@[dlmf 29.10.E4 "special case: on the line Re z = K"]
theorem Real.lameEck_imaginary_solution (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ)
    (s : ℝ) :
    -(deriv (deriv fun s => Real.lameEck ν m (Real.compEllIntKm (1 - k ^ 2) - s)
        (Real.sqrt (1 - k ^ 2))) s : ℂ) +
      ((ν * (ν + 1) - Real.lameAk ν m (Real.sqrt (1 - k ^ 2)) : ℝ) -
        ν * (ν + 1) * k ^ 2 * jacobiSnk (Real.compEllIntKm (k ^ 2) + I * s) k ^ 2) *
      Real.lameEck ν m (Real.compEllIntKm (1 - k ^ 2) - s) (Real.sqrt (1 - k ^ 2)) = 0 := by
  obtain ⟨h0, h1, -⟩ := l29_comodulus hk0 hk1
  exact p1l_imaginary_solution hk0 hk1 (Real.lameEck_isLameEigenfunction hν h0 h1 m).1 s

/-- 29.10.4, `Es`: as `Real.lameEck_imaginary_solution` with `h = ν(ν+1) - b^m_ν(k'²)`.
Special case: on the line `Re z = K`. Proved as `Real.lameEck_imaginary_solution`. -/
@[dlmf 29.10.E4 "special case: on the line Re z = K"]
theorem Real.lameEsk_imaginary_solution (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ)
    (s : ℝ) :
    -(deriv (deriv fun s => Real.lameEsk ν m (Real.compEllIntKm (1 - k ^ 2) - s)
        (Real.sqrt (1 - k ^ 2))) s : ℂ) +
      ((ν * (ν + 1) - Real.lameBk ν m (Real.sqrt (1 - k ^ 2)) : ℝ) -
        ν * (ν + 1) * k ^ 2 * jacobiSnk (Real.compEllIntKm (k ^ 2) + I * s) k ^ 2) *
      Real.lameEsk ν m (Real.compEllIntKm (1 - k ^ 2) - s) (Real.sqrt (1 - k ^ 2)) = 0 := by
  obtain ⟨h0, h1, -⟩ := l29_comodulus hk0 hk1
  exact p1l_imaginary_solution hk0 hk1 (Real.lameEsk_isLameEigenfunction hν h0 h1 m).1 s

/-- §29.10, periods: on the line `z = K + is`, the functions 29.10.4 built from `Ec^{2m}_ν`
and `Es^{2m+2}_ν` have period `2iK'` (period `2K'` in `s`), those from `Ec^{2m+1}_ν` and
`Es^{2m+1}_ν` have period `4iK'`. Proved from Table 29.3.2 for the modulus `k'`. -/
@[dlmf 29.10 "periods along the line Re z = K"]
theorem Real.lame_imaginary_periods (hν : -1 / 2 ≤ ν) (hk0 : 0 < k) (hk1 : k < 1) (m : ℕ)
    (s : ℝ) :
    Real.lameEck ν m (Real.compEllIntKm (1 - k ^ 2) - (s + 2 * Real.compEllIntKm (1 - k ^ 2)))
        (Real.sqrt (1 - k ^ 2)) =
      (-1) ^ m * Real.lameEck ν m (Real.compEllIntKm (1 - k ^ 2) - s) (Real.sqrt (1 - k ^ 2)) ∧
    Real.lameEsk ν m (Real.compEllIntKm (1 - k ^ 2) - (s + 2 * Real.compEllIntKm (1 - k ^ 2)))
        (Real.sqrt (1 - k ^ 2)) =
      (-1) ^ m * Real.lameEsk ν m (Real.compEllIntKm (1 - k ^ 2) - s) (Real.sqrt (1 - k ^ 2)) := by
  obtain ⟨h0, h1, h2⟩ := l29_comodulus hk0 hk1
  have hK : Real.compEllIntKm (Real.sqrt (1 - k ^ 2) ^ 2) = Real.compEllIntKm (1 - k ^ 2) := by
    rw [h2]
  set K' := Real.compEllIntKm (1 - k ^ 2)
  have hc := (Real.lameEck_parity hν h0 h1 m (K' - s - 2 * K')).2.2.2.1
  have hs := (Real.lameEsk_parity hν h0 h1 m (K' - s - 2 * K')).2.2.2.1
  rw [hK, show K' - s - 2 * K' + 2 * K' = K' - s by ring] at hc hs
  rw [show K' - (s + 2 * K') = K' - s - 2 * K' by ring]
  constructor
  · rw [hc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
  · rw [hs, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp

/-! ### The Lamé wave equation (§29.11) -/

/-- §29.11: for `ω = 0` the Lamé wave equation 29.11.1 reduces to Lamé's equation 29.2.1. -/
@[dlmf 29.11]
theorem isLameWaveSolutionOn_zero_iff {h ν k : ℂ} {w : ℂ → ℂ} {U : Set ℂ} :
    IsLameWaveSolutionOn h ν k 0 w U ↔ IsLameSolutionOn h ν k w U := by
  constructor
  · intro hw
    exact ⟨hw.differentiableAt, fun z hz => (hw.hasDerivAt_deriv z hz).congr_deriv (by ring)⟩
  · intro hw
    exact ⟨hw.differentiableAt, fun z hz => (hw.hasDerivAt_deriv z hz).congr_deriv (by ring)⟩

end DLMF.Lame
