/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.UniformCoordinates
public import DLMF.Legendre.Conical

/-!
# Uniform conical asymptotics and coordinate maps

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

open DLMF.Bessel

/-- conicalP large tau uniform. -/
@[dlmf 14.20.E15]
theorem conicalP_large_tau_uniform {μ : ℝ} (hμ : 0 ≤ μ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun p : ℝ × ℝ => conicalP p.1 μ (Real.cos p.2)/((p.1:ℂ)^(-(μ:ℂ))*(p.2/Real.sin p.2:ℂ)^(1/2:ℂ)*besselI μ (p.1*p.2))-1) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ π-δ}] (fun p : ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- conicalQHat large tau uniform. -/
@[dlmf 14.20.E16]
theorem conicalQHat_large_tau_uniform {μ : ℝ} (hμ : 0 ≤ μ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun p : ℝ × ℝ => conicalQHat p.1 μ (Real.cos p.2)/((p.1:ℂ)^(-(μ:ℂ))*(p.2/Real.sin p.2:ℂ)^(1/2:ℂ)*besselK μ (p.1*p.2))-1) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ π-δ}] (fun p : ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- conicalAlpha. -/
@[dlmf 14.20.E19]
def conicalAlpha (μ τ : ℝ) : ℝ :=
  μ/τ

/-- conicalSigma. -/
@[dlmf 14.20.E20]
def conicalSigma (μ τ : ℝ) : ℝ :=
  Real.exp (μ-τ*Real.arctan (conicalAlpha μ τ))/(μ^2+τ^2)^(μ/2)

/-- ConicalEtaRelation. -/
@[dlmf 14.20.E21]
def ConicalEtaRelation (α x η : ℝ) : Prop :=
  Real.sqrt (α^2+η)+α/2*Real.log η-α*Real.log (Real.sqrt (α^2+η)+α)=Real.arccos (x/Real.sqrt (1+α^2))+α/2*Real.log ((1+α^2+(α^2-1)*x^2-2*α*x*Real.sqrt (1+α^2-x^2))/((1+α^2)*(1-x^2)))

/-- conicalEta. -/
@[dlmf 14.20.E21]
def conicalEta (α x : ℝ) : ℝ :=
  Classical.epsilon (fun η : ℝ => 0 < η ∧ ConicalEtaRelation α x η)

/-- The left side of DLMF 14.20.21 as a function of `η`. -/
noncomputable def conE_L (α η : ℝ) : ℝ :=
  Real.sqrt (α^2+η)+α/2*Real.log η-α*Real.log (Real.sqrt (α^2+η)+α)

/-- `L'(η) = √(α²+η)/(2η)`. -/
theorem conE_hasDerivAt {α η : ℝ} (hα : 0 ≤ α) (hη : 0 < η) :
    HasDerivAt (conE_L α) (Real.sqrt (α^2+η)/(2*η)) η := by
  have hp : 0 < α^2+η := by positivity
  set s := Real.sqrt (α^2+η) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hp
  have hs2 : s^2 = α^2+η := Real.sq_sqrt hp.le
  have hsd : HasDerivAt (fun η => Real.sqrt (α^2+η)) (1/(2*s)) η := by
    have := ((hasDerivAt_id η).const_add (α^2)).sqrt hp.ne'
    simpa using this
  have hsa : 0 < s + α := by linarith
  have h := (hsd.add ((Real.hasDerivAt_log hη.ne').const_mul (α/2))).sub
    ((hsd.add_const α).log hsa.ne' |>.const_mul α)
  convert h using 1
  · funext y; simp only [conE_L, Pi.add_apply, Pi.sub_apply]
  · rw [← hs]
    field_simp
    linear_combination s * hs2

/-- `L` increases strictly on `(0, ∞)`. -/
theorem conE_strictMonoOn {α : ℝ} (hα : 0 ≤ α) : StrictMonoOn (conE_L α) (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun η hη => (conE_hasDerivAt hα hη).continuousAt.continuousWithinAt) fun η hη => ?_
  rw [interior_Ioi] at hη
  have hη : (0:ℝ) < η := hη
  rw [(conE_hasDerivAt hα hη).deriv]
  have : 0 < Real.sqrt (α^2+η) := Real.sqrt_pos.2 (by positivity)
  positivity

/-- `L → -∞` as `η → 0⁺` when `α > 0`. -/
theorem conE_tendsto_zero {α : ℝ} (hα : 0 < α) : Tendsto (conE_L α) (𝓝[>] 0) atBot := by
  have hg : ContinuousAt (fun η : ℝ => Real.sqrt (α^2+η) - α*Real.log (Real.sqrt (α^2+η)+α)) 0 := by
    have h : Real.sqrt (α^2+0)+α ≠ 0 := by positivity
    fun_prop (disch := exact h)
  have := (Real.tendsto_log_nhdsGT_zero.const_mul_atBot (show 0 < α/2 by positivity)).atBot_add
    (hg.tendsto.mono_left nhdsWithin_le_nhds)
  refine this.congr fun η => ?_
  simp only [conE_L]; ring

/-- `L → ∞` as `η → ∞`. -/
theorem conE_tendsto_atTop {α : ℝ} (hα : 0 ≤ α) : Tendsto (conE_L α) atTop atTop := by
  have hb : ∀ᶠ η in atTop, Real.sqrt η - α/2*Real.log 3 ≤ conE_L α η := by
    filter_upwards [eventually_ge_atTop (3*α^2+1)] with η hη
    have hη0 : 0 < η := by nlinarith [sq_nonneg α]
    have hp : 0 < α^2+η := by positivity
    set s := Real.sqrt (α^2+η) with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 hp
    have hs2 : s^2 = α^2+η := Real.sq_sqrt hp.le
    have hsη : Real.sqrt η ≤ s := Real.sqrt_le_sqrt (by nlinarith)
    have hs2a : 2*α ≤ s := by nlinarith
    have hsa : 0 < s + α := by linarith
    have hq : 1/3 ≤ η/(s+α)^2 := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    have hl : Real.log (1/3) ≤ Real.log η - 2*Real.log (s+α) := by
      rw [show (2:ℝ) * Real.log (s+α) = ((2:ℕ):ℝ) * Real.log (s+α) by norm_num, ← Real.log_pow,
        ← Real.log_div hη0.ne' (by positivity)]
      exact Real.log_le_log (by norm_num) hq
    rw [one_div, Real.log_inv] at hl
    simp only [conE_L]
    rw [← hs]
    nlinarith
  exact tendsto_atTop_mono' _ hb
    (tendsto_atTop_add_const_right _ _ Real.tendsto_sqrt_atTop)

/-- conicalEta spec. -/
@[dlmf 14.20.E21]
theorem conicalEta_spec {α x : ℝ} (hα : 0 ≤ α) (hx : x ∈ Ioo (-1:ℝ) 1) :
    0 < conicalEta α x ∧ ConicalEtaRelation α x (conicalEta α x) ∧ ∀ η : ℝ, 0 < η → ConicalEtaRelation α x η → η=conicalEta α x := by
  have hrel : ∀ η, ConicalEtaRelation α x η ↔ conE_L α η = Real.arccos (x/Real.sqrt (1+α^2))+α/2*Real.log ((1+α^2+(α^2-1)*x^2-2*α*x*Real.sqrt (1+α^2-x^2))/((1+α^2)*(1-x^2))) :=
    fun η => Iff.rfl
  have hex : ∃ η : ℝ, 0 < η ∧ ConicalEtaRelation α x η := by
    rcases hα.lt_or_eq with hα | hα
    · obtain ⟨η, hη, h⟩ := dblZero_exists_eq_of_tendsto
        (fun η hη => (conE_hasDerivAt hα.le hη).continuousAt.continuousWithinAt)
        (conE_tendsto_zero hα) (conE_tendsto_atTop hα.le) _
      exact ⟨η, hη, (hrel η).2 h⟩
    · subst hα
      have hac : 0 < Real.arccos x := Real.arccos_pos.2 hx.2
      refine ⟨Real.arccos x ^ 2, by positivity, ?_⟩
      simp [ConicalEtaRelation, Real.sqrt_sq hac.le]
  have hs := Classical.epsilon_spec hex
  refine ⟨hs.1, hs.2, fun η hη h => ?_⟩
  exact (conE_strictMonoOn hα).injOn hη hs.1 (((hrel η).1 h).trans ((hrel _).1 hs.2).symm)

/-- The right side of DLMF 14.20.21 as a function of `x`. -/
noncomputable def conE_R (α x : ℝ) : ℝ :=
  Real.arccos (x/Real.sqrt (1+α^2))+α/2*Real.log ((1+α^2+(α^2-1)*x^2-2*α*x*Real.sqrt (1+α^2-x^2))/((1+α^2)*(1-x^2)))

/-- The argument of the logarithm in DLMF 14.20.21 is positive. -/
theorem conE_Q_pos {α x : ℝ} (hα : 0 < α) (hx : x ∈ Ioo (-1:ℝ) 1) :
    0 < 1+α^2+(α^2-1)*x^2-2*α*x*Real.sqrt (1+α^2-x^2) := by
  have hx2 : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
  have hS : Real.sqrt (1+α^2-x^2) ^ 2 = 1+α^2-x^2 := Real.sq_sqrt (by nlinarith [sq_nonneg α])
  set S := Real.sqrt (1+α^2-x^2)
  have hNN : (1+α^2+(α^2-1)*x^2-2*α*x*S) * (1+α^2+(α^2-1)*x^2+2*α*x*S)
      = (1+α^2)^2*(1-x^2)^2 := by
    linear_combination (-4*α^2*x^2) * hS
  have hp : 0 < (1+α^2+(α^2-1)*x^2-2*α*x*S) * (1+α^2+(α^2-1)*x^2+2*α*x*S) := by
    rw [hNN]; positivity
  have hsum : 0 < (1+α^2+(α^2-1)*x^2-2*α*x*S) + (1+α^2+(α^2-1)*x^2+2*α*x*S) := by
    nlinarith [sq_nonneg x, sq_nonneg α, mul_nonneg (sq_nonneg α) (sq_nonneg x)]
  by_contra h
  push Not at h
  nlinarith

/-- `R'(x) = -√(1+α²-x²)/(1-x²)`. -/
theorem conE_R_hasDerivAt {α x : ℝ} (hα : 0 < α) (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (conE_R α) (-(Real.sqrt (1+α^2-x^2)/(1-x^2))) x := by
  have hx2 : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
  have hA : 0 < 1 + α^2 := by positivity
  have hR : 0 < 1+α^2-x^2 := by nlinarith [sq_nonneg α]
  set S := Real.sqrt (1+α^2-x^2) with hSdef
  have hS0 : 0 < S := Real.sqrt_pos.2 hR
  have hS : S^2 = 1+α^2-x^2 := Real.sq_sqrt hR.le
  set r := Real.sqrt (1+α^2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hA
  have hr2 : r^2 = 1+α^2 := Real.sq_sqrt hA.le
  have hQ := conE_Q_pos hα hx
  have hu1 : x / r < 1 := by
    rw [div_lt_one hr0]; nlinarith [sq_nonneg α]
  have hu2 : -1 < x / r := by
    rw [lt_div_iff₀ hr0]; nlinarith [sq_nonneg α]
  have hac := (Real.hasDerivAt_arccos hu2.ne' hu1.ne).comp x ((hasDerivAt_id x).div_const r)
  have hSd : HasDerivAt (fun x => Real.sqrt (1+α^2-x^2)) (-(2*x)/(2*S)) x := by
    have : HasDerivAt (fun x => 1+α^2-x^2) (-(2*x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_sub (1+α^2)
    exact this.sqrt hR.ne'
  have hQd : HasDerivAt (fun x => 1+α^2+(α^2-1)*x^2-2*α*x*Real.sqrt (1+α^2-x^2))
      ((α^2-1)*(2*x) - (2*α*S + 2*α*x*(-(2*x)/(2*S)))) x := by
    have h1 : HasDerivAt (fun x => (α^2-1)*x^2) ((α^2-1)*(2*x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_mul (α^2-1)
    have h2 := ((hasDerivAt_id x).const_mul (2*α)).mul hSd
    simp only [id, mul_one] at h2
    have := ((h1.const_add (1+α^2))).sub h2
    convert this using 1
  have hDd : HasDerivAt (fun x : ℝ => (1+α^2)*(1 - x^2)) ((1+α^2)*(-(2*x))) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub 1).const_mul (1+α^2)
  have hL := (hQd.div hDd (by positivity)).log (div_pos hQ (by positivity)).ne'
  have := hac.add (hL.const_mul (α/2))
  convert this using 1
  · funext y; simp [conE_R, Function.comp, ← hr]
  · simp only [Pi.div_apply]
    rw [← hSdef]
    have h1u : 1 - (x/r)^2 = S^2/r^2 := by
      rw [hS, hr2]; field_simp; linear_combination x^2 * hr2
    rw [h1u, Real.sqrt_div' _ (sq_nonneg r), Real.sqrt_sq hS0.le, Real.sqrt_sq hr0.le]
    field_simp
    have hQ2 : 1 + α^2 + x^2*(α^2-1) - S*x*α*2 ≠ 0 := by
      have : 1 + α^2 + x^2*(α^2-1) - S*x*α*2 = 1+α^2+(α^2-1)*x^2-2*α*x*S := by ring
      rw [this]; exact hQ.ne'
    field_simp
    linear_combination (2*S*α*x + x^2 - 1) * hS

/-- `R(-x) = π - R(x)`. -/
theorem conE_R_symm {α x : ℝ} (hα : 0 < α) (hx : x ∈ Ioo (-1:ℝ) 1) :
    conE_R α (-x) = π - conE_R α x := by
  have hx2 : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
  have hS : Real.sqrt (1+α^2-x^2) ^ 2 = 1+α^2-x^2 := Real.sq_sqrt (by nlinarith [sq_nonneg α])
  have hQ := conE_Q_pos hα hx
  have hQ' := conE_Q_pos hα (x := -x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  simp only [neg_sq, neg_mul, mul_neg, sub_neg_eq_add] at hQ'
  unfold conE_R
  simp only [neg_sq, neg_mul, mul_neg, sub_neg_eq_add, neg_div, Real.arccos_neg]
  set S := Real.sqrt (1+α^2-x^2)
  set Q := 1+α^2+(α^2-1)*x^2-2*α*x*S
  have hD : 0 < (1+α^2)*(1-x^2) := by positivity
  have hNN : (1+α^2+(α^2-1)*x^2+2*α*x*S) = ((1+α^2)*(1-x^2))^2 / Q := by
    rw [eq_div_iff hQ.ne']; linear_combination (-4*α^2*x^2) * hS
  rw [hNN, show ((1+α^2)*(1-x^2))^2 / Q / ((1+α^2)*(1-x^2)) = (Q / ((1+α^2)*(1-x^2)))⁻¹ by
    field_simp, Real.log_inv]
  ring

/-- `R → ∞` as `x → -1⁺`. -/
theorem conE_R_tendsto_neg_one {α : ℝ} (hα : 0 < α) :
    Tendsto (conE_R α) (𝓝[>] (-1:ℝ)) atTop := by
  have hQc : Tendsto (fun x : ℝ => 1+α^2+(α^2-1)*x^2-2*α*x*Real.sqrt (1+α^2-x^2))
      (𝓝[>] (-1:ℝ)) (𝓝 (4*α^2)) := by
    have hc : Continuous fun x : ℝ => 1+α^2+(α^2-1)*x^2-2*α*x*Real.sqrt (1+α^2-x^2) := by
      fun_prop
    have e : 1+α^2+(α^2-1)*(-1:ℝ)^2-2*α*(-1)*Real.sqrt (1+α^2-(-1)^2) = 4*α^2 := by
      rw [show 1+α^2-(-1:ℝ)^2 = α^2 by ring, Real.sqrt_sq hα.le]; ring
    have h := hc.tendsto (-1)
    rw [e] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hD : Tendsto (fun x : ℝ => ((1+α^2)*(1 - x^2))⁻¹) (𝓝[>] (-1:ℝ)) atTop := by
    refine tendsto_inv_nhdsGT_zero.comp ?_
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Continuous fun x : ℝ => (1+α^2)*(1 - x^2) := by fun_prop
      have h := this.tendsto (-1)
      rw [show (1+α^2)*(1-(-1:ℝ)^2) = 0 by ring] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (-1:ℝ) < 1 by norm_num)] with x hx
      show 0 < (1+α^2)*(1 - x^2)
      have : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
      positivity
  have hq := hQc.pos_mul_atTop (by positivity) hD
  have hl := (Real.tendsto_log_atTop.comp hq).const_mul_atTop (show 0 < α/2 by positivity)
  have hac : Tendsto (fun x : ℝ => Real.arccos (x/Real.sqrt (1+α^2))) (𝓝[>] (-1:ℝ))
      (𝓝 (Real.arccos ((-1)/Real.sqrt (1+α^2)))) :=
    ((Real.continuous_arccos.comp (continuous_id.div_const _)).tendsto _).mono_left
      nhdsWithin_le_nhds
  refine (hl.atTop_add hac).congr fun x => ?_
  simp only [conE_R, Function.comp, div_eq_mul_inv]
  ring

/-- `R → -∞` as `x → 1⁻`. -/
theorem conE_R_tendsto_one {α : ℝ} (hα : 0 < α) :
    Tendsto (conE_R α) (𝓝[<] (1:ℝ)) atBot := by
  have hneg : Tendsto (fun x : ℝ => -x) (𝓝[<] (1:ℝ)) (𝓝[>] (-1:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h := (continuous_neg (G := ℝ)).tendsto 1
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      show -1 < -x
      have : x < 1 := hx
      linarith
  have h := (tendsto_atBot_add_const_left _ π
    (tendsto_neg_atTop_atBot.comp ((conE_R_tendsto_neg_one hα).comp hneg)))
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num)] with x hx
  simp only [Function.comp]
  rw [conE_R_symm hα hx]; ring

/-- Mapping and endpoints in DLMF 14.20(viii). The hypothesis is `0 < α` (corrected
2026-10-20): at `α = 0` the relation is `sqrt η = arccos x`, so `η → π^2` as `x → -1`. -/
theorem conicalEta_mapping {α : ℝ} (hα : 0 < α) :
    Set.BijOn (conicalEta α) (Ioo (-1:ℝ) 1) (Ioi 0) ∧ StrictAntiOn (conicalEta α) (Ioo (-1:ℝ) 1) ∧ Tendsto (conicalEta α) (𝓝[>] (-1:ℝ)) atTop ∧ Tendsto (conicalEta α) (𝓝[<] (1:ℝ)) (𝓝 0) := by
  have hE : ∀ x ∈ Ioo (-1:ℝ) 1, 0 < conicalEta α x ∧ conE_L α (conicalEta α x) = conE_R α x :=
    fun x hx => ⟨(conicalEta_spec hα.le hx).1, (conicalEta_spec hα.le hx).2.1⟩
  have hL := conE_strictMonoOn hα.le
  have hRc : ContinuousOn (conE_R α) (Ioo (-1:ℝ) 1) :=
    fun x hx => (conE_R_hasDerivAt hα hx).continuousAt.continuousWithinAt
  have hR : StrictAntiOn (conE_R α) (Ioo (-1:ℝ) 1) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) hRc fun x hx => ?_
    rw [interior_Ioo] at hx
    rw [(conE_R_hasDerivAt hα hx).deriv, neg_lt_zero]
    have hx2 : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
    have : 0 < Real.sqrt (1+α^2-x^2) := Real.sqrt_pos.2 (by nlinarith [sq_nonneg α])
    positivity
  have hanti : StrictAntiOn (conicalEta α) (Ioo (-1:ℝ) 1) := by
    intro x hx y hy hxy
    have h1 := hR hx hy hxy
    rw [← (hE x hx).2, ← (hE y hy).2] at h1
    exact (hL.lt_iff_lt (hE y hy).1 (hE x hx).1).1 h1
  have hIoo : ∀ᶠ x in 𝓝[>] (-1:ℝ), x ∈ Ioo (-1:ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  have hIoo' : ∀ᶠ x in 𝓝[<] (1:ℝ), x ∈ Ioo (-1:ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  refine ⟨⟨fun x hx => (hE x hx).1, hanti.injOn, fun e he => ?_⟩, hanti, ?_, ?_⟩
  · have he : (0:ℝ) < e := he
    obtain ⟨a, ha, haI⟩ := (((conE_R_tendsto_neg_one hα).eventually
      (eventually_gt_atTop (conE_L α e))).and hIoo).exists
    obtain ⟨b, hb, hbI⟩ := (((conE_R_tendsto_one hα).eventually
      (eventually_lt_atBot (conE_L α e))).and hIoo').exists
    have hab : a ≤ b := by
      by_contra h
      push Not at h
      have := hR hbI haI h
      linarith
    have hsub : Icc a b ⊆ Ioo (-1:ℝ) 1 := Icc_subset_Ioo haI.1 hbI.2
    obtain ⟨c, hc, hcy⟩ := intermediate_value_Icc' hab (hRc.mono hsub) ⟨hb.le, ha.le⟩
    refine ⟨c, hsub hc, ?_⟩
    exact ((conicalEta_spec hα.le (hsub hc)).2.2 e he hcy.symm).symm
  · refine tendsto_atTop.2 fun M => ?_
    have hM : (0:ℝ) < max M 1 := lt_max_of_lt_right one_pos
    filter_upwards [(conE_R_tendsto_neg_one hα).eventually
      (eventually_gt_atTop (conE_L α (max M 1))), hIoo] with x hx hxI
    rw [← (hE x hxI).2] at hx
    exact (le_max_left _ _).trans ((hL.lt_iff_lt hM (hE x hxI).1).1 hx).le
  · refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
    · filter_upwards [hIoo'] with x hxI
      exact ha.trans (hE x hxI).1
    · filter_upwards [(conE_R_tendsto_one hα).eventually (eventually_lt_atBot (conE_L α b)),
        hIoo'] with x hx hxI
      rw [← (hE x hxI).2] at hx
      exact (hL.lt_iff_lt (hE x hxI).1 hb).1 hx

/-- conicalP two large tau uniform. -/
@[dlmf 14.20.E17]
theorem conicalP_two_large_tau_uniform {A δ : ℝ} (hA : 0 < A) (hδ : 0 < δ) (hδ2 : δ < 2) :
    (fun p : ℝ × ℝ × ℝ => let τ:=p.1; let μ:=p.2.1; let x:=p.2.2; let α:=conicalAlpha μ τ; let η:=conicalEta α x; conicalP τ μ x/(conicalSigma μ τ*((α^2+η)/(1+α^2-x^2):ℂ)^(1/4:ℂ)*besselI μ (τ*Real.sqrt η))-1) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ico (-1+δ) 1 ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ A*p.1}] (fun p : ℝ × ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- conicalQHat two large tau uniform. -/
@[dlmf 14.20.E18]
theorem conicalQHat_two_large_tau_uniform {A δ : ℝ} (hA : 0 < A) (hδ : 0 < δ) (hδ2 : δ < 2) :
    (fun p : ℝ × ℝ × ℝ => let τ:=p.1; let μ:=p.2.1; let x:=p.2.2; let α:=conicalAlpha μ τ; let η:=conicalEta α x; conicalQHat τ μ x/(conicalSigma μ τ*((α^2+η)/(1+α^2-x^2):ℂ)^(1/4:ℂ)*besselK μ (τ*Real.sqrt η))-1) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ico (-1+δ) 1 ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ A*p.1}] (fun p : ℝ × ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

/-- conicalBeta. -/
@[dlmf 14.20.E23]
def conicalBeta (μ τ : ℝ) : ℝ :=
  τ/μ

/-- conicalRho. -/
@[dlmf 14.20.E24]
def conicalRho (β x : ℝ) : ℝ :=
  Real.log (((1-β^2)*x^2+1+β^2+2*x*Real.sqrt (1+β^2-β^2*x^2))/(1-x^2))/2+β*Real.arctan (β*x/Real.sqrt (1+β^2-β^2*x^2))-Real.log (1+β^2)/2

/-- `ρ'(x) = √(1+β²-β²x²)/(1-x²)` on `(-1, 1)`. -/
theorem conR_hasDerivAt (β : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (conicalRho β) (Real.sqrt (1+β^2-β^2*x^2)/(1-x^2)) x := by
  have hx2 : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
  have hR : 1 ≤ 1+β^2-β^2*x^2 := by nlinarith [sq_nonneg β]
  set S := Real.sqrt (1+β^2-β^2*x^2) with hSdef
  have hS1 : 1 ≤ S := by rw [hSdef]; exact Real.one_le_sqrt.2 hR
  have hS : S^2 = 1+β^2-β^2*x^2 := Real.sq_sqrt (by linarith)
  have hS0 : S ≠ 0 := by linarith
  set N := (1-β^2)*x^2+1+β^2+2*x*S with hN
  have hNN : N * ((1-β^2)*x^2+1+β^2-2*x*S) = (1+β^2)^2*(1-x^2)^2 := by
    rw [hN]; linear_combination (-4*x^2) * hS
  have hN0 : 0 < N := by
    have hp : 0 < N * ((1-β^2)*x^2+1+β^2-2*x*S) := by rw [hNN]; positivity
    have hsum : 0 < N + ((1-β^2)*x^2+1+β^2-2*x*S) := by
      rw [hN]; nlinarith [sq_nonneg x, sq_nonneg β, mul_nonneg (sq_nonneg β) hx2.le]
    by_contra h
    push Not at h
    nlinarith
  have hSd : HasDerivAt (fun x => Real.sqrt (1+β^2-β^2*x^2)) (-(β^2*(2*x))/(2*S)) x := by
    have : HasDerivAt (fun x => 1+β^2-β^2*x^2) (-(β^2*(2*x))) x := by
      simpa using ((hasDerivAt_pow 2 x).const_mul (β^2)).const_sub (1+β^2)
    exact this.sqrt (by linarith)
  have hNd : HasDerivAt (fun x => (1-β^2)*x^2+1+β^2+2*x*Real.sqrt (1+β^2-β^2*x^2))
      ((1-β^2)*(2*x) + (2*S + 2*x*(-(β^2*(2*x))/(2*S)))) x := by
    have h1 : HasDerivAt (fun x => (1-β^2)*x^2) ((1-β^2)*(2*x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_mul (1-β^2)
    have h2 := ((hasDerivAt_id x).const_mul 2).mul hSd
    simp only [id, mul_one] at h2
    have := (h1.add_const (1+β^2)).add h2
    convert this using 1
    · funext y; simp only [Pi.add_apply, Pi.mul_apply]; ring
  have hDd : HasDerivAt (fun x : ℝ => 1 - x^2) (-(2*x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_sub 1
  have hL := (hNd.div hDd hx2.ne').log (div_pos hN0 hx2).ne'
  have hA := ((((hasDerivAt_id x).const_mul β).div hSd hS0).arctan).const_mul β
  have := ((hL.div_const 2).add hA).sub_const (Real.log (1+β^2)/2)
  convert this using 1
  · funext y; simp [conicalRho]
  · simp only [id, Pi.div_apply]
    rw [← hSdef, ← hN]
    have h1S : 1 + (β * x / S)^2 = (1+β^2)/S^2 := by
      field_simp; linear_combination hS
    rw [h1S]
    have hb : (0:ℝ) < 1 + β^2 := by positivity
    field_simp
    rw [hN]
    linear_combination (-x*(-2*S*β^2*x^2 - 2*S + β^4*x^3 - β^4*x - β^2*x^3 + β^2*x)) * hS

/-- The argument of the logarithm in `ρ` is positive on `(-1, 1)`. -/
theorem conR_N_pos (β : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    0 < (1-β^2)*x^2+1+β^2+2*x*Real.sqrt (1+β^2-β^2*x^2) := by
  have hx2 : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
  have hS : Real.sqrt (1+β^2-β^2*x^2) ^ 2 = 1+β^2-β^2*x^2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg β, mul_nonneg (sq_nonneg β) hx2.le])
  set S := Real.sqrt (1+β^2-β^2*x^2)
  have hNN : ((1-β^2)*x^2+1+β^2+2*x*S) * ((1-β^2)*x^2+1+β^2-2*x*S) = (1+β^2)^2*(1-x^2)^2 := by
    linear_combination (-4*x^2) * hS
  have hp : 0 < ((1-β^2)*x^2+1+β^2+2*x*S) * ((1-β^2)*x^2+1+β^2-2*x*S) := by
    rw [hNN]; positivity
  have hsum : 0 < ((1-β^2)*x^2+1+β^2+2*x*S) + ((1-β^2)*x^2+1+β^2-2*x*S) := by
    nlinarith [sq_nonneg x, sq_nonneg β, mul_nonneg (sq_nonneg β) hx2.le]
  by_contra h
  push Not at h
  nlinarith

/-- `ρ` is odd. -/
theorem conR_odd (β : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) : conicalRho β (-x) = -conicalRho β x := by
  have hx2 : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
  have hS : Real.sqrt (1+β^2-β^2*x^2) ^ 2 = 1+β^2-β^2*x^2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg β, mul_nonneg (sq_nonneg β) hx2.le])
  have hN := conR_N_pos β hx
  have hN' := conR_N_pos β (x := -x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  simp only [neg_sq, neg_mul, mul_neg] at hN' ⊢
  set S := Real.sqrt (1+β^2-β^2*x^2)
  set N := (1-β^2)*x^2+1+β^2+2*x*S
  have hNN : ((1-β^2)*x^2+1+β^2+-(2*x*S)) = (1+β^2)^2*(1-x^2)^2 / N := by
    rw [eq_div_iff hN.ne']; linear_combination (-4*x^2) * hS
  have hb : (0:ℝ) < 1 + β^2 := by positivity
  unfold conicalRho
  simp only [neg_sq, neg_mul, mul_neg]
  rw [hNN, show (1+β^2)^2*(1-x^2)^2 / N / (1-x^2) = (1+β^2)^2 / (N/(1-x^2)) by
    field_simp, Real.log_div (by positivity) (div_pos hN hx2).ne', Real.log_pow]
  push_cast
  simp only [mul_neg, neg_div, Real.arctan_neg]
  ring

/-- `ρ → ∞` as `x → 1⁻`. -/
theorem conR_tendsto_one (β : ℝ) : Tendsto (conicalRho β) (𝓝[<] (1:ℝ)) atTop := by
  have hcN : Tendsto (fun x : ℝ => (1-β^2)*x^2+1+β^2+2*x*Real.sqrt (1+β^2-β^2*x^2))
      (𝓝[<] (1:ℝ)) (𝓝 4) := by
    have : Continuous fun x : ℝ => (1-β^2)*x^2+1+β^2+2*x*Real.sqrt (1+β^2-β^2*x^2) := by
      fun_prop
    have e : (1-β^2)*(1:ℝ)^2+1+β^2+2*1*Real.sqrt (1+β^2-β^2*1^2) = 4 := by
      rw [show 1+β^2-β^2*(1:ℝ)^2 = 1 by ring, Real.sqrt_one]; ring
    have h4 := this.tendsto 1
    rw [e] at h4
    exact h4.mono_left nhdsWithin_le_nhds
  have hD : Tendsto (fun x : ℝ => (1 - x^2)⁻¹) (𝓝[<] (1:ℝ)) atTop := by
    refine tendsto_inv_nhdsGT_zero.comp ?_
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Continuous fun x : ℝ => 1 - x^2 := by fun_prop
      have h := this.tendsto 1
      rw [show (1:ℝ) - 1^2 = 0 by norm_num] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx
      show 0 < 1 - x^2
      nlinarith [hx.1, hx.2]
  have hq := (hcN.pos_mul_atTop (by norm_num) hD)
  have hl := (Real.tendsto_log_atTop.comp hq).atTop_div_const (show (0:ℝ) < 2 by norm_num)
  have hA : Tendsto (fun x : ℝ => β*Real.arctan (β*x/Real.sqrt (1+β^2-β^2*x^2)))
      (𝓝[<] (1:ℝ)) (𝓝 (β*Real.arctan (β*1/Real.sqrt (1+β^2-β^2*1^2)))) := by
    have : ContinuousAt (fun x : ℝ => β*Real.arctan (β*x/Real.sqrt (1+β^2-β^2*x^2))) 1 := by
      have h1 : Real.sqrt (1+β^2-β^2*1^2) ≠ 0 := by norm_num
      fun_prop (disch := exact h1)
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have := (hl.atTop_add hA).atTop_add (tendsto_const_nhds (x := -(Real.log (1+β^2)/2)))
  refine this.congr fun x => ?_
  simp only [conicalRho, Function.comp, div_eq_mul_inv]
  ring

/-- `ρ → -∞` as `x → -1⁺`. -/
theorem conR_tendsto_neg_one (β : ℝ) : Tendsto (conicalRho β) (𝓝[>] (-1:ℝ)) atBot := by
  have hneg : Tendsto (fun x : ℝ => -x) (𝓝[>] (-1:ℝ)) (𝓝[<] (1:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h := (continuous_neg (G := ℝ)).tendsto (-1)
      rw [neg_neg] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      show -x < 1
      have : (-1:ℝ) < x := hx
      linarith
  have h := tendsto_neg_atTop_atBot.comp ((conR_tendsto_one β).comp hneg)
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (-1:ℝ) < 1 by norm_num)] with x hx
  simp only [Function.comp]
  rw [conR_odd β hx, neg_neg]

/-- Mapping and endpoints in DLMF 14.20(ix). -/
theorem conicalRho_mapping (β : ℝ) :
    Set.BijOn (conicalRho β) (Ioo (-1:ℝ) 1) univ ∧ StrictMonoOn (conicalRho β) (Ioo (-1:ℝ) 1) ∧ conicalRho β 0=0 ∧ Tendsto (conicalRho β) (𝓝[>] (-1:ℝ)) atBot ∧ Tendsto (conicalRho β) (𝓝[<] (1:ℝ)) atTop := by
  have hcont : ContinuousOn (conicalRho β) (Ioo (-1:ℝ) 1) :=
    fun x hx => (conR_hasDerivAt β hx).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn (conicalRho β) (Ioo (-1:ℝ) 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) hcont fun x hx => ?_
    rw [interior_Ioo] at hx
    rw [(conR_hasDerivAt β hx).deriv]
    have hx2 : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
    have : 0 < Real.sqrt (1+β^2-β^2*x^2) :=
      Real.sqrt_pos.2 (by nlinarith [sq_nonneg β, mul_nonneg (sq_nonneg β) hx2.le])
    positivity
  have h0 : conicalRho β 0 = 0 := by simp [conicalRho]
  refine ⟨⟨mapsTo_univ _ _, hmono.injOn, fun y _ => ?_⟩, hmono, h0, conR_tendsto_neg_one β,
    conR_tendsto_one β⟩
  obtain ⟨a, ha, hay⟩ := (((conR_tendsto_neg_one β).eventually (eventually_lt_atBot y)).and
    (Ioo_mem_nhdsGT (show (-1:ℝ) < 1 by norm_num))).exists
  obtain ⟨b, hb, hby⟩ := (((conR_tendsto_one β).eventually (eventually_gt_atTop y)).and
    (Ioo_mem_nhdsLT (show (-1:ℝ) < 1 by norm_num))).exists
  have hab : a ≤ b := by
    by_contra h
    push Not at h
    have := hmono hby hay h
    linarith
  have hsub : Icc a b ⊆ Ioo (-1:ℝ) 1 := Icc_subset_Ioo hay.1 hby.2
  obtain ⟨c, hc, hcy⟩ := intermediate_value_Icc hab (hcont.mono hsub) ⟨ha.le, hb.le⟩
  exact ⟨c, hsub hc, hcy⟩

/-- conicalP two large mu uniform. -/
@[dlmf 14.20.E22]
theorem conicalP_two_large_mu_uniform {A : ℝ} (hA : 0 < A) :
    (fun p : ℝ × ℝ × ℝ => let μ:=p.1; let τ:=p.2.1; let x:=p.2.2; let β:=conicalBeta μ τ; conicalP τ μ x/(exp (μ*β*Real.arctan β)/(Gamma (μ+1)*(1+β^2:ℂ)^((μ:ℂ)/2))*exp (-μ*conicalRho β x)/(1+β^2-x^2*β^2:ℂ)^(1/4:ℂ))-1) =O[legendreUniformFilter {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ioo (-1:ℝ) 1 ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ A*p.1}] (fun p : ℝ × ℝ × ℝ => (p.1:ℂ)⁻¹) := by
  sorry

end DLMF.Legendre
