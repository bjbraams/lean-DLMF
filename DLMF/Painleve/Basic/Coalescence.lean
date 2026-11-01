/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.Basic.Transformations

/-!
# The coalescence cascade of the Painlevé equations: DLMF §32.2(vi)

The limits `PII → PI`, `PIII → PII`, `PIV → PII`, `PV → PIII`, `PV → PIV` and `PVI → PV`
(DLMF 32.2.24–32.2.37), in the DLMF normalization.

## Main results

* `IsPainleveIIOn.coalescence_I`: the exact transformed equation of DLMF 32.2.25–32.2.27.
* `painleveII_coalescence_I_tendsto`, `painleveIII_coalescence_II_tendsto`,
  `painleveIV_coalescence_II_tendsto`, `painleveV_coalescence_III_tendsto`,
  `painleveV_coalescence_IV_tendsto`, `painleveVI_coalescence_V_tendsto`: the limits of the
  transformed right-hand sides (DLMF 32.2.24–32.2.37).

## Implementation notes

The transformed equations come from `IsODE2SolutionOn.affine`
(`DLMF.Painleve.Basic.Transformations`); for each coalescence both the exact right-hand side
and its limit as `ε → 0` are given.
-/

@[expose] public noncomputable section

open Set Filter Complex
open scoped Topology

namespace DLMF.Painleve

/-! ## Coalescence cascade (§32.2(vi)) -/

/-- DLMF 32.2.25–32.2.27, exact form: if `w` solves `PII` with `α = 4ε⁻¹⁵` and
`w = εW(ζ) + ε⁻⁵`, `z = ε²ζ - 6ε⁻¹⁰`, then
`W'' = 6W² + ζ + ε⁶(2W³ + ζW)` exactly; as `ε → 0` this is `PI`. -/
@[dlmf 32.2.E25, dlmf 32.2.E26, dlmf 32.2.E27]
theorem IsPainleveIIOn.coalescence_I {ε : ℂ} (hε : ε ≠ 0) {w : ℂ → ℂ} {U V : Set ℂ}
    (h : IsPainleveIIOn (4 / ε ^ 15) w U) (hV : IsOpen V)
    (hVU : ∀ ζ ∈ V, ε ^ 2 * ζ - 6 / ε ^ 10 ∈ U) :
    IsODE2SolutionOn (fun ζ W _ => 6 * W ^ 2 + ζ + ε ^ 6 * (2 * W ^ 3 + ζ * W))
      (fun ζ => (w (ε ^ 2 * ζ - 6 / ε ^ 10) - 1 / ε ^ 5) / ε) V := by
  have hW := IsODE2SolutionOn.affine h hV (a := 1 / ε ^ 5) (b := ε) (c := -6 / ε ^ 10)
    (d := ε ^ 2) hε (pow_ne_zero 2 hε) (fun ζ hζ => by
      convert hVU ζ hζ using 1; ring)
  have he : (fun ζ => (w (-6 / ε ^ 10 + ε ^ 2 * ζ) - 1 / ε ^ 5) / ε) =
      fun ζ => (w (ε ^ 2 * ζ - 6 / ε ^ 10) - 1 / ε ^ 5) / ε := by
    funext ζ; congr 3; ring
  rw [he] at hW
  refine hW.congr_rhs fun ζ _ => ?_
  simp only [painleveIIRhs]
  field_simp
  ring

/-- The `PI` limit of 32.2.27: the right-hand side `6W² + ζ + ε⁶(2W³ + ζW)` tends to the
right-hand side of `PI` as `ε → 0`. -/
@[dlmf 32.2.vi]
theorem painleveII_coalescence_I_tendsto (ζ X Y : ℂ) :
    Tendsto (fun ε : ℂ => 6 * X ^ 2 + ζ + ε ^ 6 * (2 * X ^ 3 + ζ * X)) (𝓝 0)
      (𝓝 (painleveIRhs ζ X Y)) := by
  have hc : Continuous (fun ε : ℂ => 6 * X ^ 2 + ζ + ε ^ 6 * (2 * X ^ 3 + ζ * X)) := by
    fun_prop
  simpa [painleveIRhs] using hc.tendsto 0

/-- A function that agrees near `0` (off `0`) with a function continuous at `0` tends to the
value of the latter at `0`. -/
private lemma tendsto_punctured_of_eventuallyEq {F G : ℂ → ℂ} {L : ℂ}
    (hFG : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), F ε = G ε) (hG : ContinuousAt G 0) (hL : G 0 = L) :
    Tendsto F (𝓝[≠] 0) (𝓝 L) := by
  rw [← hL]
  exact (hG.tendsto.mono_left nhdsWithin_le_nhds).congr' (hFG.mono fun _ h => h.symm)

/-- A continuous function that does not vanish at `0` does not vanish near `0`. -/
private lemma eventually_ne_zero_of_continuous {f : ℂ → ℂ} (hf : Continuous f) (h0 : f 0 ≠ 0) :
    ∀ᶠ ε in 𝓝[≠] (0 : ℂ), f ε ≠ 0 :=
  nhdsWithin_le_nhds (hf.continuousAt.eventually_ne h0)

/-- Points of the punctured neighbourhood of `0` are nonzero. -/
private lemma eventually_ne_zero_punctured : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), ε ≠ 0 := self_mem_nhdsWithin

/-- DLMF 32.2.28–32.2.29 (`PIII → PII`): with `w = 1 + 2εW(ζ)`, `z = 1 + ε²ζ`,
`α = -ε⁻⁶/2`, `β = ε⁻⁶/2 + 2aε⁻³`, `γ = -δ = ε⁻⁶/4`, the equation satisfied by `W`
(`IsODE2SolutionOn.affine`) has right-hand side
`(ε⁴/(2ε)) PIII-rhs(1 + ε²ζ, 1 + 2εW, 2εW'/ε²)`, which tends to the right-hand side of
`PII` with `α = a` as `ε → 0`. -/
@[dlmf 32.2.E28, dlmf 32.2.E29, dlmf 32.2.E24]
theorem painleveIII_coalescence_II_tendsto (a ζ X Y : ℂ) :
    Tendsto (fun ε : ℂ => (ε ^ 2) ^ 2 / (2 * ε) *
      painleveIIIRhs (-1 / (2 * ε ^ 6)) (1 / (2 * ε ^ 6) + 2 * a / ε ^ 3) (1 / (4 * ε ^ 6))
        (-1 / (4 * ε ^ 6)) (1 + ε ^ 2 * ζ) (1 + 2 * ε * X) (2 * ε * Y / ε ^ 2))
      (𝓝[≠] 0) (𝓝 (painleveIIRhs a ζ X Y)) := by
  refine tendsto_punctured_of_eventuallyEq (G := fun ε => (2 * X ^ 4 * ε ^ 3 * ζ + 2 * X ^ 4 * ε +
      4 * X ^ 3 * ε ^ 2 * ζ + 2 * X ^ 3 + 3 * X ^ 2 * ε * ζ - 2 * X * Y * ε ^ 3 + 2 * X * a * ε +
      X * ζ + 2 * Y ^ 2 * ε ^ 3 * ζ + 2 * Y ^ 2 * ε - Y * ε ^ 2 + a) /
      ((1 + 2 * ε * X) * (1 + ε ^ 2 * ζ))) ?_ ?_ ?_
  · filter_upwards [eventually_ne_zero_punctured,
      eventually_ne_zero_of_continuous (f := fun ε => 1 + 2 * ε * X) (by fun_prop) (by simp),
      eventually_ne_zero_of_continuous (f := fun ε => 1 + ε ^ 2 * ζ) (by fun_prop)
          (by simp)] with ε h0 h1 h2
    simp only [painleveIIIRhs]
    generalize e1 : 1 + 2 * ε * X = A at h1 ⊢
    generalize e2 : 1 + ε ^ 2 * ζ = B at h2 ⊢
    field_simp
    subst e1 e2
    ring
  · exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)
  · simp [painleveIIRhs]
    ring

/-- DLMF 32.2.30–32.2.31 (`PIV → PII`): with `w = 2^{2/3}ε⁻¹W(ζ) + ε⁻³`,
`z = 2^{-2/3}εζ - ε⁻³`, `α = -2a - ε⁻⁶/2`, `β = -ε⁻¹²/2`, the right-hand side of the equation
for `W` tends to that of `PII` with `α = a`. Here `2^{2/3}` is `t²` for `t = 2^{1/3}` real. -/
@[dlmf 32.2.E30, dlmf 32.2.E31, dlmf 32.2.E24]
theorem painleveIV_coalescence_II_tendsto (a ζ X Y : ℂ) :
    let t : ℂ := ((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ)
    Tendsto (fun ε : ℂ => (ε / t ^ 2) ^ 2 / (t ^ 2 / ε) *
      painleveIVRhs (-2 * a - 1 / (2 * ε ^ 6)) (-1 / (2 * ε ^ 12)) (ε / t ^ 2 * ζ - 1 / ε ^ 3)
        (1 / ε ^ 3 + t ^ 2 / ε * X) (t ^ 2 / ε * Y / (ε / t ^ 2)))
      (𝓝[≠] 0) (𝓝 (painleveIIRhs a ζ X Y)) := by
  intro t
  have ht : t ^ 3 = 2 := by
    simp only [t]
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have ht0 : t ≠ 0 := by rintro h; rw [h] at ht; norm_num at ht
  refine tendsto_punctured_of_eventuallyEq (G := fun ε => (3 * X ^ 4 * ε ^ 2 * t ^ 12 +
      8 * X ^ 3 * ε ^ 4 * t ^ 8 * ζ + 4 * X ^ 3 * t ^ 10 + 8 * X ^ 2 * a * ε ^ 4 * t ^ 8 +
      4 * X ^ 2 * ε ^ 6 * t ^ 4 * ζ ^ 2 + 16 * X ^ 2 * ε ^ 2 * t ^ 6 * ζ +
      16 * X * a * ε ^ 2 * t ^ 6 + 8 * X * ε ^ 4 * t ^ 2 * ζ ^ 2 + 8 * X * t ^ 4 * ζ +
      Y ^ 2 * ε ^ 2 * t ^ 12 + 8 * a * t ^ 4 + 4 * ε ^ 2 * ζ ^ 2) /
      (2 * t ^ 10 * (1 + t ^ 2 * ε ^ 2 * X))) ?_ ?_ ?_
  · filter_upwards [eventually_ne_zero_punctured,
      eventually_ne_zero_of_continuous (f := fun ε => 1 + t ^ 2 * ε ^ 2 * X) (by fun_prop)
          (by simp)]
      with ε h0 h1
    simp only [painleveIVRhs]
    have h1' : 1 / ε ^ 3 + t ^ 2 / ε * X ≠ 0 := by
      rw [show 1 / ε ^ 3 + t ^ 2 / ε * X = (1 + t ^ 2 * ε ^ 2 * X) / ε ^ 3 by field_simp]
      exact div_ne_zero h1 (pow_ne_zero 3 h0)
    generalize e1 : 1 / ε ^ 3 + t ^ 2 / ε * X = A at h1' ⊢
    generalize e2 : 1 + t ^ 2 * ε ^ 2 * X = B at h1 ⊢
    field_simp
    subst e1 e2
    field_simp
    ring
  · exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp [ht0])
  · have h6 : t ^ 6 = 4 := by rw [show t ^ 6 = (t ^ 3) ^ 2 by ring, ht]; norm_num
    have h10 : t ^ 10 = 4 * t ^ 4 := by rw [show t ^ 10 = t ^ 6 * t ^ 4 by ring, h6]
    have h12 : t ^ 12 = 16 := by rw [show t ^ 12 = (t ^ 6) ^ 2 by ring, h6]; norm_num
    simp only [painleveIIRhs]
    field_simp
    linear_combination (-(2 * X * ζ + 2 * a)) * h10

/-- DLMF 32.2.32–32.2.33 (`PV → PIII`): with `w = 1 + εζW(ζ)`, `z = ζ²`,
`α = a/(4ε) + c/(8ε²)`, `β = -c/(8ε²)`, `γ = εb/4`, `δ = ε²d/8`, `W` satisfies (for
`ε ≠ 0`) an equation whose right-hand side tends to that of `PIII(a, b, c, d)` as `ε → 0`.
Stated for solutions: the limit holds at every jet `(ζ, W, W')` with `ζ ≠ 0`, `W ≠ 0`, where
the `ε`-equation is obtained from `PV` by the stated substitution. -/
@[dlmf 32.2.E32, dlmf 32.2.E33, dlmf 32.2.E24]
theorem painleveV_coalescence_III_tendsto (a b c d ζ X Y : ℂ) (hζ : ζ ≠ 0) (hX : X ≠ 0) :
    Tendsto (fun ε : ℂ =>
      -- `w = 1 + εζX`, `w_z = (εX + εζY)/(2ζ)`; solve `w_zz = PV-rhs` for `W''`.
      ((2 * ζ) ^ 2 * painleveVRhs (a / (4 * ε) + c / (8 * ε ^ 2)) (-c / (8 * ε ^ 2))
          (ε * b / 4) (ε ^ 2 * d / 8) (ζ ^ 2) (1 + ε * ζ * X) ((ε * X + ε * ζ * Y) / (2 * ζ)) +
        (ε * X + ε * ζ * Y) / ζ - 2 * ε * Y) / (ε * ζ))
      (𝓝[≠] 0) (𝓝 (painleveIIIRhs a b c d ζ X Y)) := by
  refine tendsto_punctured_of_eventuallyEq (G := fun ε => (2 * X ^ 5 * a * ε ^ 2 * ζ ^ 2 +
      X ^ 5 * c * ε * ζ ^ 2 + 4 * X ^ 4 * a * ε * ζ + 2 * X ^ 4 * c * ζ + 2 * X ^ 3 * a +
      2 * X ^ 3 * b * ε ^ 2 * ζ ^ 2 + X ^ 3 * d * ε ^ 3 * ζ ^ 4 + X ^ 3 * ε +
      4 * X ^ 2 * b * ε * ζ + 4 * X ^ 2 * d * ε ^ 2 * ζ ^ 3 + 3 * X * Y ^ 2 * ε * ζ ^ 2 -
      2 * X * Y + 2 * X * b + 5 * X * d * ε * ζ ^ 2 + 2 * Y ^ 2 * ζ + 2 * d * ζ) /
      (2 * X * ζ * (1 + ε * ζ * X))) ?_ ?_ ?_
  · filter_upwards [eventually_ne_zero_punctured,
      eventually_ne_zero_of_continuous (f := fun ε => 1 + ε * ζ * X) (by fun_prop)
          (by simp)] with ε h0 h1
    have h2 : 1 + ε * ζ * X - 1 ≠ 0 := by simp [h0, hζ, hX]
    simp only [painleveVRhs]
    generalize e1 : 1 + ε * ζ * X = A at h1 h2 ⊢
    field_simp
    subst e1
    ring
  · exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp [hX, hζ])
  · simp only [painleveIIIRhs]
    field_simp
    ring

/-- DLMF 32.2.34–32.2.35 (`PV → PIV`): with `w = (√2/2)εW(ζ)`, `z = 1 + √2εζ`,
`α = ε⁻⁴/2`, `β = b/4`, `γ = -ε⁻⁴`, `δ = aε⁻² - ε⁻⁴/2`, the right-hand side of the equation for
`W` tends to that of `PIV(a, b)` as `ε → 0` (at jets with `W ≠ 0`). -/
@[dlmf 32.2.E34, dlmf 32.2.E35, dlmf 32.2.E24]
theorem painleveV_coalescence_IV_tendsto (a b ζ X Y : ℂ) (hX : X ≠ 0) :
    let r : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)
    Tendsto (fun ε : ℂ => (r * ε) ^ 2 / (r / 2 * ε) *
      painleveVRhs (1 / (2 * ε ^ 4)) (b / 4) (-1 / ε ^ 4) (a / ε ^ 2 - 1 / (2 * ε ^ 4))
        (1 + r * ε * ζ) (r / 2 * ε * X) (r / 2 * ε * Y / (r * ε)))
      (𝓝[≠] 0) (𝓝 (painleveIVRhs a b ζ X Y)) := by
  intro r
  have hr : r ^ 2 = 2 := by
    simp only [r]; rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hr0 : r ≠ 0 := by rintro h; rw [h] at hr; norm_num at hr
  refine tendsto_punctured_of_eventuallyEq (G := fun ε => (r * X ^ 5 * ε - 6 * X ^ 4 +
      8 * r * X ^ 3 * a * ε ^ 3 * ζ ^ 2 + 16 * X ^ 3 * a * ε ^ 2 * ζ + 4 * r * X ^ 3 * a * ε +
      r * X ^ 3 * b * ε ^ 3 - 4 * r * X ^ 3 * ε * ζ ^ 2 - 16 * X ^ 3 * ζ -
      4 * r * X ^ 2 * Y * ε ^ 3 * ζ - 4 * X ^ 2 * Y * ε ^ 2 + 16 * X ^ 2 * a * ε ^ 2 * ζ ^ 2 +
      16 * r * X ^ 2 * a * ε * ζ + 8 * X ^ 2 * a - 6 * X ^ 2 * b * ε ^ 2 - 8 * X ^ 2 * ζ ^ 2 +
      6 * r * X * Y ^ 2 * ε ^ 3 * ζ ^ 2 + 12 * X * Y ^ 2 * ε ^ 2 * ζ + 3 * r * X * Y ^ 2 * ε +
      8 * X * Y * ε ^ 2 * ζ + 4 * r * X * Y * ε + 6 * r * X * b * ε - 4 * Y ^ 2 * ε ^ 2 * ζ ^ 2 -
      4 * r * Y ^ 2 * ε * ζ - 2 * Y ^ 2 - 4 * b) /
      (2 * X * (r / 2 * ε * X - 1) * 2 * (1 + r * ε * ζ) ^ 2)) ?_ ?_ ?_
  · filter_upwards [eventually_ne_zero_punctured,
      eventually_ne_zero_of_continuous (f := fun ε => 1 + r * ε * ζ) (by fun_prop) (by simp),
      eventually_ne_zero_of_continuous (f := fun ε => r / 2 * ε * X - 1) (by fun_prop) (by simp)]
      with ε h0 h1 h2
    have h3 : r / 2 * ε * X ≠ 0 := by simp [h0, hr0, hX]
    simp only [painleveVRhs]
    generalize e1 : 1 + r * ε * ζ = A at h1 ⊢
    generalize e2 : r / 2 * ε * X - 1 = B at h2 ⊢
    field_simp
    subst e1 e2
    have hr3 : r ^ 3 = 2 * r := by rw [pow_succ, hr]
    have hr4 : r ^ 4 = 4 := by rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hr]; norm_num
    have hr5 : r ^ 5 = 4 * r := by rw [pow_succ, hr4]
    have hr6 : r ^ 6 = 8 := by rw [pow_succ, hr5]; linear_combination 4 * hr
    have hr7 : r ^ 7 = 8 * r := by rw [pow_succ, hr6]
    have hr8 : r ^ 8 = 16 := by rw [pow_succ, hr7]; linear_combination 8 * hr
    ring_nf
    simp only [hr, hr3, hr4, hr5, hr6, hr7, hr8]
    ring_nf
  · exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp [hX])
  · simp only [painleveIVRhs]
    field_simp
    ring

/-- DLMF 32.2.36–32.2.37 (`PVI → PV`): with `w = W(ζ)`, `z = 1 + εζ`, `γ = cε⁻¹ - dε⁻²`,
`δ = dε⁻²` (and `α = a`, `β = b`), the right-hand side of the equation for `W` tends to that
of `PV(a, b, c, d)` as `ε → 0` (at jets with `ζ ≠ 0`, `W ∉ {0, 1}`). -/
@[dlmf 32.2.E36, dlmf 32.2.E37, dlmf 32.2.E24]
theorem painleveVI_coalescence_V_tendsto (a b c d ζ X Y : ℂ) (hζ : ζ ≠ 0) (hX0 : X ≠ 0)
    (hX1 : X ≠ 1) :
    Tendsto (fun ε : ℂ => ε ^ 2 / 1 *
      painleveVIRhs a b (c / ε - d / ε ^ 2) (d / ε ^ 2) (1 + ε * ζ) (0 + 1 * X) (1 * Y / ε))
      (𝓝[≠] 0) (𝓝 (painleveVRhs a b c d ζ X Y)) := by
  refine tendsto_punctured_of_eventuallyEq (G := fun ε => (-2 * X ^ 6 * a + 4 * X ^ 5 * a * ε * ζ +
      8 * X ^ 5 * a - 2 * X ^ 4 * a * ε ^ 2 * ζ ^ 2 - 12 * X ^ 4 * a * ε * ζ - 12 * X ^ 4 * a -
      2 * X ^ 4 * b * ε * ζ - 2 * X ^ 4 * b - 2 * X ^ 4 * c * ζ - 2 * X ^ 4 * d * ζ ^ 2 +
      4 * X ^ 3 * Y * ε ^ 2 * ζ ^ 3 + 6 * X ^ 3 * Y * ε * ζ ^ 2 + 2 * X ^ 3 * Y * ζ +
      4 * X ^ 3 * a * ε ^ 2 * ζ ^ 2 + 12 * X ^ 3 * a * ε * ζ + 8 * X ^ 3 * a +
      4 * X ^ 3 * b * ε ^ 2 * ζ ^ 2 + 12 * X ^ 3 * b * ε * ζ + 8 * X ^ 3 * b +
      4 * X ^ 3 * c * ε * ζ ^ 2 + 4 * X ^ 3 * c * ζ - 3 * X ^ 2 * Y ^ 2 * ε ^ 2 * ζ ^ 4 -
      6 * X ^ 2 * Y ^ 2 * ε * ζ ^ 3 - 3 * X ^ 2 * Y ^ 2 * ζ ^ 2 - 2 * X ^ 2 * Y * ε ^ 3 * ζ ^ 4 -
      10 * X ^ 2 * Y * ε ^ 2 * ζ ^ 3 - 12 * X ^ 2 * Y * ε * ζ ^ 2 - 4 * X ^ 2 * Y * ζ -
      2 * X ^ 2 * a * ε ^ 2 * ζ ^ 2 - 4 * X ^ 2 * a * ε * ζ - 2 * X ^ 2 * a -
      2 * X ^ 2 * b * ε ^ 3 * ζ ^ 3 - 14 * X ^ 2 * b * ε ^ 2 * ζ ^ 2 - 24 * X ^ 2 * b * ε * ζ -
      12 * X ^ 2 * b - 2 * X ^ 2 * c * ε ^ 2 * ζ ^ 3 - 4 * X ^ 2 * c * ε * ζ ^ 2 -
      2 * X ^ 2 * c * ζ + 2 * X ^ 2 * d * ε * ζ ^ 3 + 2 * X ^ 2 * d * ζ ^ 2 +
      2 * X * Y ^ 2 * ε ^ 3 * ζ ^ 5 + 8 * X * Y ^ 2 * ε ^ 2 * ζ ^ 4 + 10 * X * Y ^ 2 * ε * ζ ^ 3 +
      4 * X * Y ^ 2 * ζ ^ 2 + 2 * X * Y * ε ^ 3 * ζ ^ 4 + 6 * X * Y * ε ^ 2 * ζ ^ 3 +
      6 * X * Y * ε * ζ ^ 2 + 2 * X * Y * ζ + 4 * X * b * ε ^ 3 * ζ ^ 3 +
      16 * X * b * ε ^ 2 * ζ ^ 2 + 20 * X * b * ε * ζ + 8 * X * b - Y ^ 2 * ε ^ 3 * ζ ^ 5 -
      3 * Y ^ 2 * ε ^ 2 * ζ ^ 4 - 3 * Y ^ 2 * ε * ζ ^ 3 - Y ^ 2 * ζ ^ 2 - 2 * b * ε ^ 3 * ζ ^ 3 -
      6 * b * ε ^ 2 * ζ ^ 2 - 6 * b * ε * ζ - 2 * b) /
      (2 * X * ζ ^ 2 * (X - 1) * (1 + ε * ζ) ^ 2 * (1 + ε * ζ - X))) ?_ ?_ ?_
  · filter_upwards [eventually_ne_zero_punctured,
      eventually_ne_zero_of_continuous (f := fun ε => 1 + ε * ζ) (by fun_prop) (by simp),
      eventually_ne_zero_of_continuous (f := fun ε => X - (1 + ε * ζ)) (by fun_prop)
        (by simpa [sub_eq_zero] using hX1),
      eventually_ne_zero_of_continuous (f := fun ε => 1 + ε * ζ - X) (by fun_prop)
        (by simpa [sub_eq_zero] using hX1.symm)] with ε h0 h1 h2 h5
    have h3 : 1 + ε * ζ - 1 ≠ 0 := by simp [h0, hζ]
    have h4 : X - 1 ≠ 0 := sub_ne_zero.mpr hX1
    simp only [painleveVIRhs, zero_add, one_mul]
    generalize e1 : 1 + ε * ζ = A at h1 h2 h3 h5 ⊢
    generalize e2 : X - 1 = X1 at h4 ⊢
    field_simp
    subst e1 e2
    ring
  · exact ContinuousAt.div (by fun_prop) (by fun_prop)
      (by simp [hX0, hζ, sub_eq_zero.not.mpr hX1, sub_eq_zero.not.mpr hX1.symm])
  · have h4 : X - 1 ≠ 0 := sub_ne_zero.mpr hX1
    have h5 : 1 - X ≠ 0 := fun h => h4 (by linear_combination -h)
    simp only [painleveVRhs, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero]
    generalize e2 : X - 1 = X1 at h4 ⊢
    field_simp
    subst e2
    ring

end DLMF.Painleve
