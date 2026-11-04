/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Painleve.Basic.Solutions
public import DLMF.Airy.Framework
public import DLMF.Confluent.ParabolicCylinder
public import Mathlib.Basic.Real.Sign

/-!
# Asymptotic approximations for real variables (DLMF §32.11)

Real solutions of `PI`, `PII` with `α = 0`, the modified `PII` equation 32.11.12, `PIII` with
`α = -β = 2ν`, `γ = -δ = 1` and `PIV` with `α = 2ν + 1`, `β = 0`, as functions `ℝ → ℝ`
solving the equation on a real interval (`IsRealODE2SolutionOn`, `DLMF.Painleve.Basic.Solutions`).
Asymptotic relations use `Asymptotics.IsEquivalent` (`~`), `IsLittleO` and `IsBigO` at
`atTop`, `atBot` or a one-sided neighbourhood. `ph` is `Complex.arg` (DLMF: the branch is
immaterial, the phases enter only through `sin` or `cos`), `Ai` is `DLMF.Airy.Real.airyAi`, `U` is
the real part of `parabolicCylinderU` on the real line. The results are the connection theorems of
Hastings–McLeod, Ablowitz–Segur, Deift–Zhou, McCoy–Tracy–Wu and Its–Kapaev.

## Main results

* `painleveI_oscillating`, `painleveI_sqrt`, `painleveI_not_global`, `painleveI_trichotomy`:
  real solutions of `PI` (DLMF 32.11.1–32.11.3, §32.11(i)).
* `painleveII_decaying_airy`, `painleveII_existsUnique_airy`: decaying solutions of `PII` with
  `α = 0` are asymptotic to `k Ai(x)` (DLMF 32.11.4–32.11.5).
* `painleveII_ablowitzSegur`, `painleveII_hastingsMcLeod`, `painleveII_pole`: the behaviour of
  `w_k` at `-∞` for `|k| < 1`, `|k| = 1` and `|k| > 1` (DLMF 32.11.6–32.11.11).
* `modifiedPainleveII_negInfty`, `modifiedPainleveII_airy`, `modifiedPainleveII_generic`: the
  modified `PII` equation (DLMF 32.11.12–32.11.24).
* `painleveIII_connection`: the connection formulas for `PIII` (DLMF 32.11.25–32.11.28).
* `painleveIV_decaying_pcf`, `painleveIV_existsUnique_pcf`: decaying solutions of `PIV`
  (DLMF 32.11.29–32.11.30).
* `painleveIV_noPoles`, `painleveIV_hermiteAsymptotics`, `painleveIV_oscillating`,
  `painleveIV_critical`, `painleveIV_pole`: the behaviour of `w_h` (DLMF 32.11.31–32.11.38).

## Implementation notes

`painleveII_ablowitzSegur` and `painleveII_hastingsMcLeod` assert that `w_k` exists on all
of `ℝ` (stronger than DLMF).

**Conventions made explicit.** In 32.11.6–32.11.9, 32.11.13–32.11.24 and 32.11.33–32.11.36 the
pair `(d, θ₀)` (or `(d, χ)`) is determined by the solution only up to `(d, θ₀) ↦ (-d, θ₀ + π)`;
the connection formulas fix the sign `d > 0` (with `d < 0` the parity in 32.11.17 and the sign
`σ` in 32.11.21 would flip). DLMF states `d > 0` only in 32.11.34; the statements below take
`d > 0` throughout. The numerical bounds on `k₁`, `k₂` in §32.11(i) are out of scope.
-/

@[expose] public noncomputable section

open Set Filter Asymptotics
open scoped Topology
open DLMF.Airy DLMF.Confluent

namespace DLMF.Painleve

/-! ## `PI` (§32.11(i)) -/

/-- DLMF 32.11.1–32.11.2: there are real solutions of `PI` on a half-line `(-∞, x₀)` with
`w(x) = -√(|x|/6) + d|x|^{-1/8} sin(φ(x) - θ₀) + o(|x|^{-1/8})` as `x → -∞`, where
`φ(x) = 24^{1/4}(4/5 |x|^{5/4} - 5/8 d² ln|x|)` and `d ≠ 0`, `θ₀` are constants. -/
@[dlmf 32.11.E1, dlmf 32.11.E2]
theorem painleveI_oscillating :
    ∃ (w : ℝ → ℝ) (x₀ d θ₀ : ℝ), d ≠ 0 ∧ IsRealODE2SolutionOn realPainleveIRhs w (Iio x₀) ∧
      (fun x => w x - (-Real.sqrt (|x| / 6) + d * |x| ^ (-(1 / 8 : ℝ)) *
        Real.sin ((24 : ℝ) ^ (1 / 4 : ℝ) * (4 / 5 * |x| ^ (5 / 4 : ℝ) -
          5 / 8 * d ^ 2 * Real.log |x|) - θ₀))) =o[atBot] fun x => |x| ^ (-(1 / 8 : ℝ)) := by
  sorry

/-- DLMF 32.11.3: there are real solutions of `PI` with `w(x) ~ √(|x|/6)` as `x → -∞`. -/
@[dlmf 32.11.E3]
theorem painleveI_sqrt :
    ∃ (w : ℝ → ℝ) (x₀ : ℝ), IsRealODE2SolutionOn realPainleveIRhs w (Iio x₀) ∧
      w ~[atBot] fun x => Real.sqrt (|x| / 6) := by
  sorry

/-- A function whose derivative is nonnegative on `(a, ∞)` is monotone on `[a, ∞)`. -/
private lemma monotoneOn_Ici_of_hasDerivAt {f f' : ℝ → ℝ} {a : ℝ}
    (hf : ∀ x, a ≤ x → HasDerivAt f (f' x) x) (h0 : ∀ x, a < x → 0 ≤ f' x) :
    MonotoneOn f (Ici a) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := f') (convex_Ici a)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt) (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Ici] at hx
    exact (hf x (le_of_lt hx)).hasDerivWithinAt
  · rw [interior_Ici] at hx
    exact h0 x hx

/-- §32.11(i): for real `k`, the solution of `PI` with `w(0) = 0`, `w'(0) = k` has at least one
pole on the real axis, i.e. no real solution of `PI` on all of `ℝ` has these initial values. -/
@[dlmf 32.11.i]
theorem painleveI_not_global (k : ℝ) :
    ¬∃ w : ℝ → ℝ, IsRealODE2SolutionOn realPainleveIRhs w univ ∧ w 0 = 0 ∧ deriv w 0 = k := by
  rintro ⟨w, hw, -, -⟩
  set v := deriv w with hv_def
  have hW : ∀ x, HasDerivAt w (v x) x := fun x => (hw.differentiableAt x trivial).hasDerivAt
  have hV : ∀ x, HasDerivAt v (6 * w x ^ 2 + x) x := fun x => hw.hasDerivAt_deriv x trivial
  -- `v x - x` is monotone on `[1, ∞)`
  have h1 : MonotoneOn (fun x => v x - x) (Ici 1) :=
    monotoneOn_Ici_of_hasDerivAt (f' := fun x => 6 * w x ^ 2 + x - 1)
      (fun x _ => (hV x).sub (hasDerivAt_id x)) (fun x hx => by nlinarith [sq_nonneg (w x)])
  set a : ℝ := 1 + |v 1| + 1 with ha
  have hva : ∀ x, a ≤ x → 1 ≤ v x := by
    intro x hx
    have := h1 (mem_Ici.mpr le_rfl)
      (show x ∈ Ici 1 by simp only [mem_Ici]; linarith [abs_nonneg (v 1)])
      (by linarith [abs_nonneg (v 1)])
    simp only at this
    linarith [neg_abs_le (v 1)]
  have h2 : MonotoneOn (fun x => w x - x) (Ici a) :=
    monotoneOn_Ici_of_hasDerivAt (f' := fun x => v x - 1)
      (fun x _ => (hW x).sub (hasDerivAt_id x)) (fun x hx => by linarith [hva x hx.le])
  set b : ℝ := a + |w a| + 1 with hb
  have hab : a ≤ b := by linarith [abs_nonneg (w a)]
  have hwb : ∀ x, b ≤ x → 1 + (x - b) ≤ w x := by
    intro x hx
    have := h2 (mem_Ici.mpr le_rfl) (show x ∈ Ici a from hab.trans hx) (hab.trans hx)
    simp only at this
    linarith [neg_abs_le (w a)]
  have hb1 : 1 ≤ b := by linarith [abs_nonneg (v 1)]
  -- the energy `v² - 4w³` is monotone on `[b, ∞)`
  have h3 : MonotoneOn (fun x => v x ^ 2 - 4 * w x ^ 3) (Ici b) := by
    refine monotoneOn_Ici_of_hasDerivAt (f' := fun x => 2 * v x * x) (fun x _ => ?_)
      (fun x hx => by nlinarith [hva x (hab.trans hx.le)])
    convert ((hV x).pow 2).sub (((hW x).pow 3).const_mul 4) using 1
    push_cast
    ring
  set E : ℝ := v b ^ 2 - 4 * w b ^ 3 with hE
  set c : ℝ := b + |E| with hc
  have hbc : b ≤ c := by linarith [abs_nonneg E]
  have hwc : ∀ x, c ≤ x → 1 ≤ w x ∧ 1 ≤ v x ∧ w x ^ 3 ≤ v x ^ 2 := by
    intro x hx
    have hx' : b ≤ x := hbc.trans hx
    have hw1 := hwb x hx'
    have hEx := h3 (mem_Ici.mpr le_rfl) (show x ∈ Ici b from hx') hx'
    simp only at hEx
    have hw1' : 1 ≤ w x := by linarith
    have hw3 : w x ≤ w x ^ 3 := by
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ w x)
        (by linarith : (0 : ℝ) ≤ w x - 1)) (by linarith : (0 : ℝ) ≤ w x + 1)]
    refine ⟨hw1', hva x (hab.trans hx'), ?_⟩
    nlinarith [le_abs_self E, neg_abs_le E]
  -- `√(1/w) + x/2` is antitone on `[c, ∞)`
  have h4 : AntitoneOn (fun x => Real.sqrt (w x)⁻¹ + x / 2) (Ici c) := by
    have := monotoneOn_Ici_of_hasDerivAt (a := c)
      (f := fun x => -(Real.sqrt (w x)⁻¹ + x / 2))
      (f' := fun x => -((-v x / w x ^ 2) / (2 * Real.sqrt (w x)⁻¹) + 1 / 2))
      (fun x hx => by
        obtain ⟨hw1, -, -⟩ := hwc x hx
        have hw0 : w x ≠ 0 := by positivity
        exact ((((hW x).inv hw0).sqrt (inv_ne_zero hw0)).add
          ((hasDerivAt_id x).div_const 2)).neg)
      (fun x hx => by
        obtain ⟨hw1, hv1, hwv⟩ := hwc x hx.le
        have hw0 : 0 < w x := by linarith
        have hs : 0 < Real.sqrt (w x)⁻¹ := Real.sqrt_pos.mpr (inv_pos.mpr hw0)
        have hle : Real.sqrt (w x)⁻¹ ≤ v x / w x ^ 2 := by
          rw [Real.sqrt_le_iff]
          refine ⟨by positivity, ?_⟩
          rw [div_pow, inv_eq_one_div, div_le_div_iff₀ hw0 (by positivity)]
          nlinarith
        have h2 : 1 / 2 ≤ v x / w x ^ 2 / (2 * Real.sqrt (w x)⁻¹) := by
          rw [le_div_iff₀ (by positivity)]
          linarith
        have h3 : -v x / w x ^ 2 / (2 * Real.sqrt (w x)⁻¹) =
            -(v x / w x ^ 2 / (2 * Real.sqrt (w x)⁻¹)) := by ring
        rw [h3]
        linarith)
    intro x hx y hy hxy
    have := this hx hy hxy
    simp only [neg_le_neg_iff] at this
    exact this
  set s : ℝ := Real.sqrt (w c)⁻¹
  have hy : c ≤ c + 2 * s + 2 := by linarith [Real.sqrt_nonneg (w c)⁻¹]
  have := h4 (mem_Ici.mpr le_rfl) (show c + 2 * s + 2 ∈ Ici c from hy) hy
  simp only at this
  linarith [Real.sqrt_nonneg (w (c + 2 * s + 2))⁻¹]

/-- §32.11(i): there are two special values `k₁ < k₂` such that, for the solution of `PI` with
`w(0) = 0`, `w'(0) = k` and `x₀` the first pole on the negative real axis,
(a) if `k < k₁`, then `w(x) > 0` for `x₀ < x < 0`;
(b) if `k₁ < k < k₂`, then `w` has no pole on the negative axis and oscillates about, and is
asymptotic to, `-√(|x|/6)` as `x → -∞`;
(c) if `k₂ < k`, then `w` changes sign once, from positive to negative, on `(x₀, 0)`.
A first pole `x₀` is encoded as the left end of an interval `(x₀, c)`, `c > 0`, of solution on
which `|w| → ∞` at `x₀+`. (The numerical bounds `-0.451428 < k₁ < -0.451427`,
`1.851853 < k₂ < 1.851855` are not formalized: excluded: numerical.) -/
@[dlmf 32.11.i]
theorem painleveI_trichotomy :
    ∃ k₁ k₂ : ℝ, k₁ < k₂ ∧
      (∀ k < k₁, ∀ (w : ℝ → ℝ) (x₀ c : ℝ), x₀ < 0 → 0 < c →
        IsRealODE2SolutionOn realPainleveIRhs w (Ioo x₀ c) → w 0 = 0 → deriv w 0 = k →
        Tendsto (fun x => |w x|) (𝓝[>] x₀) atTop → ∀ x ∈ Ioo x₀ 0, 0 < w x) ∧
      (∀ k ∈ Ioo k₁ k₂, ∃ (w : ℝ → ℝ) (c : ℝ), 0 < c ∧
        IsRealODE2SolutionOn realPainleveIRhs w (Iio c) ∧ w 0 = 0 ∧ deriv w 0 = k ∧
        (w ~[atBot] fun x => -Real.sqrt (|x| / 6)) ∧
        (∃ᶠ x in atBot, w x < -Real.sqrt (|x| / 6)) ∧
        ∃ᶠ x in atBot, -Real.sqrt (|x| / 6) < w x) ∧
      (∀ k, k₂ < k → ∀ (w : ℝ → ℝ) (x₀ c : ℝ), x₀ < 0 → 0 < c →
        IsRealODE2SolutionOn realPainleveIRhs w (Ioo x₀ c) → w 0 = 0 → deriv w 0 = k →
        Tendsto (fun x => |w x|) (𝓝[>] x₀) atTop →
        ∃ x₁ ∈ Ioo x₀ 0, (∀ x ∈ Ioo x₀ x₁, 0 < w x) ∧ ∀ x ∈ Ioo x₁ 0, w x < 0) := by
  sorry

/-! ## `PII` with `α = 0` (§32.11(ii)) -/

/-- DLMF 32.11.4–32.11.5, §32.11(ii): any nontrivial real solution of `w'' = 2w³ + xw` on a
half-line `(x₀, ∞)` with `w(x) → 0` as `x → +∞` is asymptotic to `k Ai(x)` for some nonzero
real `k`. -/
@[dlmf 32.11.E4, dlmf 32.11.E5, dlmf 32.11.ii]
theorem painleveII_decaying_airy {w : ℝ → ℝ} {x₀ : ℝ}
    (hw : IsRealODE2SolutionOn (realPainleveIIRhs 0) w (Ioi x₀))
    (h0 : Tendsto w atTop (𝓝 0)) (hnt : ∃ x ∈ Ioi x₀, w x ≠ 0) :
    ∃ k : ℝ, k ≠ 0 ∧ w ~[atTop] fun x => k * DLMF.Airy.Real.airyAi x := by
  sorry

/-- §32.11(ii): conversely, for any nonzero real `k` there is a unique solution `w_k` of
32.11.4 asymptotic to `k Ai(x)` as `x → +∞` (unique: two such solutions agree on the common
half-line). -/
@[dlmf 32.11.ii]
theorem painleveII_existsUnique_airy {k : ℝ} (hk : k ≠ 0) :
    (∃ (w : ℝ → ℝ) (x₀ : ℝ), IsRealODE2SolutionOn (realPainleveIIRhs 0) w (Ioi x₀) ∧
      w ~[atTop] fun x => k * DLMF.Airy.Real.airyAi x) ∧
    ∀ (w₁ w₂ : ℝ → ℝ) (x₁ x₂ : ℝ), IsRealODE2SolutionOn (realPainleveIIRhs 0) w₁ (Ioi x₁) →
      IsRealODE2SolutionOn (realPainleveIIRhs 0) w₂ (Ioi x₂) →
      (w₁ ~[atTop] fun x => k * DLMF.Airy.Real.airyAi x) →
          (w₂ ~[atTop] fun x => k * DLMF.Airy.Real.airyAi x) →
      EqOn w₁ w₂ (Ioi (max x₁ x₂)) := by
  sorry

/-- DLMF 32.11.6–32.11.9 (stronger than DLMF: `w_k` is stated to exist on all of `ℝ`): if
`0 < |k| < 1`, then the solution `w_k` with `w_k ~ k Ai` at `+∞` satisfies
`w_k(x) = d|x|^{-1/4} sin(φ(x) - θ₀) + o(|x|^{-1/4})` as `x → -∞`, with
`φ(x) = (2/3)|x|^{3/2} - (3/4)d² ln|x|`, `d² = -π⁻¹ ln(1 - k²)` (`d > 0`) and
`θ₀ = (3/2)d² ln 2 + ph Γ(1 - i d²/2) + (π/4)(1 - 2 sign k)`. -/
@[dlmf 32.11.E6, dlmf 32.11.E7, dlmf 32.11.E8, dlmf 32.11.E9]
theorem painleveII_ablowitzSegur {k : ℝ} (hk : k ≠ 0) (hk1 : |k| < 1) :
    let d := Real.sqrt (-Real.pi⁻¹ * Real.log (1 - k ^ 2))
    let θ₀ := 3 / 2 * d ^ 2 * Real.log 2 +
      Complex.arg (Complex.Gamma (1 - Complex.I * ((d ^ 2 / 2 : ℝ) : ℂ))) +
      Real.pi / 4 * (1 - 2 * Real.sign k)
    ∃ w : ℝ → ℝ, IsRealODE2SolutionOn (realPainleveIIRhs 0) w univ ∧
      (w ~[atTop] fun x => k * DLMF.Airy.Real.airyAi x) ∧
      (fun x => w x - d * |x| ^ (-(1 / 4 : ℝ)) *
        Real.sin (2 / 3 * |x| ^ (3 / 2 : ℝ) - 3 / 4 * d ^ 2 * Real.log |x| - θ₀)) =o[atBot]
        fun x => |x| ^ (-(1 / 4 : ℝ)) := by
  sorry

/-- DLMF 32.11.10 (stronger than DLMF: `w_k` exists on all of `ℝ`): if `|k| = 1`, then
`w_k(x) ~ sign(k) √(|x|/2)` as `x → -∞` (the Hastings–McLeod solution). -/
@[dlmf 32.11.E10]
theorem painleveII_hastingsMcLeod {k : ℝ} (hk : |k| = 1) :
    ∃ w : ℝ → ℝ, IsRealODE2SolutionOn (realPainleveIIRhs 0) w univ ∧
      (w ~[atTop] fun x => k * DLMF.Airy.Real.airyAi x) ∧
      w ~[atBot] fun x => Real.sign k * Real.sqrt (|x| / 2) := by
  sorry

/-- DLMF 32.11.11: if `|k| > 1`, then `w_k` has a pole at a finite point `c₀` (depending on
`k`): it solves 32.11.4 on `(c₀, ∞)` and `w_k(x) ~ sign(k)/(x - c₀)` as `x → c₀+`. -/
@[dlmf 32.11.E11]
theorem painleveII_pole {k : ℝ} (hk : 1 < |k|) :
    ∃ (w : ℝ → ℝ) (c₀ : ℝ), IsRealODE2SolutionOn (realPainleveIIRhs 0) w (Ioi c₀) ∧
      (w ~[atTop] fun x => k * DLMF.Airy.Real.airyAi x) ∧
      w ~[𝓝[>] c₀] fun x => Real.sign k * (x - c₀)⁻¹ := by
  sorry

/-! ## Modified `PII` (§32.11(iii)) -/

/-- DLMF 32.11.13–32.11.14: any nontrivial real solution of `w'' = -2w³ + xw` (32.11.12) on a
half-line `(-∞, x₀)` satisfies `w(x) = d|x|^{-1/4} sin(φ(x) - χ) + O(|x|^{-5/4} ln|x|)` as
`x → -∞`, `φ(x) = (2/3)|x|^{3/2} + (3/4)d² ln|x|`, for real constants `d > 0` and `χ`. -/
@[dlmf 32.11.E13, dlmf 32.11.E14]
theorem modifiedPainleveII_negInfty {w : ℝ → ℝ} {x₀ : ℝ}
    (hw : IsRealODE2SolutionOn modifiedPainleveIIRhs w (Iio x₀)) (hnt : ∃ x ∈ Iio x₀, w x ≠ 0) :
    ∃ d χ : ℝ, 0 < d ∧
      (fun x => w x - d * |x| ^ (-(1 / 4 : ℝ)) *
        Real.sin (2 / 3 * |x| ^ (3 / 2 : ℝ) + 3 / 4 * d ^ 2 * Real.log |x| - χ)) =O[atBot]
        fun x => |x| ^ (-(5 / 4 : ℝ)) * Real.log |x| := by
  sorry

/-- DLMF 32.11.15–32.11.17: let `w` be a real solution of 32.11.12 on `ℝ` with the behaviour
32.11.13 at `-∞` (`d > 0`). If `χ + (3/2)d² ln 2 - π/4 - ph Γ(i d²/2) = nπ`, `n ∈ ℤ`, then
`w(x) ~ k Ai(x)` as `x → +∞` with `d² = π⁻¹ ln(1 + k²)` and `sign k = (-1)ⁿ`. -/
@[dlmf 32.11.E15, dlmf 32.11.E16, dlmf 32.11.E17]
theorem modifiedPainleveII_airy {w : ℝ → ℝ} {d χ : ℝ} (hd : 0 < d)
    (hw : IsRealODE2SolutionOn modifiedPainleveIIRhs w univ)
    (hasym : (fun x => w x - d * |x| ^ (-(1 / 4 : ℝ)) *
        Real.sin (2 / 3 * |x| ^ (3 / 2 : ℝ) + 3 / 4 * d ^ 2 * Real.log |x| - χ)) =O[atBot]
        fun x => |x| ^ (-(5 / 4 : ℝ)) * Real.log |x|)
    {n : ℤ} (hn : (χ + 3 / 2 * d ^ 2 * Real.log 2 - Real.pi / 4 -
      Complex.arg (Complex.Gamma (Complex.I * ((d ^ 2 / 2 : ℝ) : ℂ)))) = n * Real.pi) :
    ∃ k : ℝ, k ≠ 0 ∧ (w ~[atTop] fun x => k * DLMF.Airy.Real.airyAi x) ∧
      d ^ 2 = Real.pi⁻¹ * Real.log (1 + k ^ 2) ∧ Real.sign k = (-1 : ℝ) ^ n := by
  sorry

/-- DLMF 32.11.18–32.11.24: in the generic case `χ + (3/2)d² ln 2 - π/4 - ph Γ(i d²/2) ≠ nπ`,
with `s = (exp(πd²) - 1)^{1/2} exp(i((3/2)d² ln 2 - π/4 + χ - ph Γ(i d²/2)))`, the solution
satisfies `w(x) = σ√(x/2) + σρ(2x)^{-1/4} cos(ψ(x) + θ) + O(x⁻¹)` as `x → +∞`, where
`ψ(x) = (2/3)√2 x^{3/2} - (3/2)ρ² ln x`, `σ = -sign(ℑs)`,
`ρ² = π⁻¹ ln((1 + |s|²)/|2ℑs|)` (`ρ ≥ 0`) and
`θ = -(3/4)π - (7/2)ρ² ln 2 + ph(1 + s²) + ph Γ(iρ²)`. -/
@[dlmf 32.11.E18, dlmf 32.11.E19, dlmf 32.11.E20, dlmf 32.11.E21, dlmf 32.11.E22,
  dlmf 32.11.E23, dlmf 32.11.E24]
theorem modifiedPainleveII_generic {w : ℝ → ℝ} {d χ : ℝ} (hd : 0 < d)
    (hw : IsRealODE2SolutionOn modifiedPainleveIIRhs w univ)
    (hasym : (fun x => w x - d * |x| ^ (-(1 / 4 : ℝ)) *
        Real.sin (2 / 3 * |x| ^ (3 / 2 : ℝ) + 3 / 4 * d ^ 2 * Real.log |x| - χ)) =O[atBot]
        fun x => |x| ^ (-(5 / 4 : ℝ)) * Real.log |x|)
    (hgen : ∀ n : ℤ, (χ + 3 / 2 * d ^ 2 * Real.log 2 - Real.pi / 4 -
      Complex.arg (Complex.Gamma (Complex.I * ((d ^ 2 / 2 : ℝ) : ℂ)))) ≠ n * Real.pi) :
    let s : ℂ := (Real.sqrt (Real.exp (Real.pi * d ^ 2) - 1) : ℂ) *
      Complex.exp (Complex.I * (((χ + 3 / 2 * d ^ 2 * Real.log 2 - Real.pi / 4 -
        Complex.arg (Complex.Gamma (Complex.I * ((d ^ 2 / 2 : ℝ) : ℂ)))) : ℝ) : ℂ))
    let σ := -Real.sign s.im
    let ρ := Real.sqrt (Real.pi⁻¹ * Real.log ((1 + ‖s‖ ^ 2) / |2 * s.im|))
    let θ := -(3 / 4) * Real.pi - 7 / 2 * ρ ^ 2 * Real.log 2 + Complex.arg (1 + s ^ 2) +
      Complex.arg (Complex.Gamma (Complex.I * ((ρ ^ 2 : ℝ) : ℂ)))
    (fun x => w x - (σ * Real.sqrt (x / 2) + σ * ρ * (2 * x) ^ (-(1 / 4 : ℝ)) *
      Real.cos (2 / 3 * Real.sqrt 2 * x ^ (3 / 2 : ℝ) - 3 / 2 * ρ ^ 2 * Real.log x + θ)))
      =O[atTop] fun x => x⁻¹ := by
  sorry

/-! ## `PIII` (§32.11(iv)) -/

/-- DLMF 32.11.25–32.11.28: for `PIII` with `α = -β = 2ν`, `γ = -δ = 1` (`ν > -1/2`) and real
`λ` with `|πλ| < 1`, there is a solution on `(0, ∞)` with
`w(x) - 1 ~ -λΓ(ν + 1/2)2^{-2ν}x^{-ν-1/2}e^{-2x}` as `x → +∞`; it satisfies `w(x) ~ Bx^σ` as
`x → 0+`, with `σ = (2/π) arcsin(πλ)` (so `|σ| < 1`) and
`B = 2^{-2σ}Γ²((1 - σ)/2)Γ((1 + σ)/2 + ν)/(Γ²((1 + σ)/2)Γ((1 - σ)/2 + ν))`. (The restriction
`ν > -1/2` keeps the Gamma factors finite and positive.) -/
@[dlmf 32.11.E25, dlmf 32.11.E26, dlmf 32.11.E27, dlmf 32.11.E28]
theorem painleveIII_connection {ν l : ℝ} (hν : -1 / 2 < ν) (hl : |Real.pi * l| < 1) :
    let σ := 2 / Real.pi * Real.arcsin (Real.pi * l)
    let B := (2 : ℝ) ^ (-2 * σ) * Real.Gamma ((1 - σ) / 2) ^ 2 * Real.Gamma ((1 + σ) / 2 + ν) /
      (Real.Gamma ((1 + σ) / 2) ^ 2 * Real.Gamma ((1 - σ) / 2 + ν))
    ∃ w : ℝ → ℝ, IsRealODE2SolutionOn (realPainleveIIIRhs (2 * ν) (-2 * ν) 1 (-1)) w (Ioi 0) ∧
      (∀ x ∈ Ioi (0 : ℝ), w x ≠ 0) ∧
      ((fun x => w x - 1) ~[atTop] fun x => -l * Real.Gamma (ν + 1 / 2) * (2 : ℝ) ^ (-2 * ν) *
        x ^ (-ν - 1 / 2) * Real.exp (-2 * x)) ∧
      w ~[𝓝[>] 0] fun x => B * x ^ σ := by
  sorry

/-! ## `PIV` (§32.11(v)) -/

/-- DLMF 32.11.29–32.11.30, §32.11(v): any nontrivial solution of 32.11.29 (`PIV` with
`α = 2ν + 1`, `β = 0`) on a half-line `(x₀, ∞)`, nonvanishing there, with `w(x) → 0` as
`x → +∞`, is asymptotic to `hU²(-ν - 1/2, √2x)` for a constant `h ≠ 0`. -/
@[dlmf 32.11.E29, dlmf 32.11.E30, dlmf 32.11.v]
theorem painleveIV_decaying_pcf {ν : ℝ} {w : ℝ → ℝ} {x₀ : ℝ}
    (hw : IsRealODE2SolutionOn (realPainleveIVRhs (2 * ν + 1) 0) w (Ioi x₀))
    (hw0 : ∀ x ∈ Ioi x₀, w x ≠ 0) (h0 : Tendsto w atTop (𝓝 0)) :
    ∃ h : ℝ, h ≠ 0 ∧ w ~[atTop] fun x => h * (parabolicCylinderU (-(ν : ℂ) - 1 / 2) ((Real.sqrt 2
        * x : ℝ) : ℂ)).re ^ 2 := by
  sorry

/-- §32.11(v): conversely, for any `h ≠ 0` there is a unique solution `w_h` of 32.11.29
asymptotic to `hU²(-ν - 1/2, √2x)` as `x → +∞` (two such solutions agree on the common
half-line). -/
@[dlmf 32.11.v]
theorem painleveIV_existsUnique_pcf {ν h : ℝ} (hh : h ≠ 0) :
    (∃ (w : ℝ → ℝ) (x₀ : ℝ), IsRealODE2SolutionOn (realPainleveIVRhs (2 * ν + 1) 0) w (Ioi x₀) ∧
      (∀ x ∈ Ioi x₀, w x ≠ 0) ∧ w ~[atTop] fun x => h *
          (parabolicCylinderU (-(ν : ℂ) - 1 / 2) ((Real.sqrt 2
          * x : ℝ) : ℂ)).re ^ 2) ∧
    ∀ (w₁ w₂ : ℝ → ℝ) (x₁ x₂ : ℝ),
      IsRealODE2SolutionOn (realPainleveIVRhs (2 * ν + 1) 0) w₁ (Ioi x₁) →
      IsRealODE2SolutionOn (realPainleveIVRhs (2 * ν + 1) 0) w₂ (Ioi x₂) →
      (∀ x ∈ Ioi x₁, w₁ x ≠ 0) → (∀ x ∈ Ioi x₂, w₂ x ≠ 0) →
      (w₁ ~[atTop] fun x => h *
          (parabolicCylinderU (-(ν : ℂ) - 1 / 2) ((Real.sqrt 2 * x : ℝ) : ℂ)).re ^ 2)
          → (w₂ ~[atTop] fun x => h * (parabolicCylinderU (-(ν : ℂ) - 1 / 2) ((Real.sqrt 2
              * x : ℝ) : ℂ)).re ^ 2) →
      EqOn w₁ w₂ (Ioi (max x₁ x₂)) := by
  sorry

/-- DLMF 32.11.31: if `0 < h < h* = 1/(π^{1/2}Γ(ν + 1))`, then `w_h` has no poles on the real
axis: it solves 32.11.29 on all of `ℝ` (and does not vanish). (Stated for `Γ(ν + 1) > 0`, so
that `h* > 0`; `h = 0` gives `w ≡ 0`, which is not a solution of `PIV`.) -/
@[dlmf 32.11.E31]
theorem painleveIV_noPoles {ν h : ℝ} (hΓ : 0 < Real.Gamma (ν + 1)) (hh : 0 < h)
    (hh' : h < 1 / (Real.sqrt Real.pi * Real.Gamma (ν + 1))) :
    ∃ w : ℝ → ℝ, IsRealODE2SolutionOn (realPainleveIVRhs (2 * ν + 1) 0) w univ ∧
      (∀ x, w x ≠ 0) ∧ w ~[atTop] fun x => h * (parabolicCylinderU (-(ν : ℂ) - 1 / 2) ((Real.sqrt 2
          * x : ℝ) : ℂ)).re ^ 2 := by
  sorry

/-- DLMF 32.11.32: if `ν = n ∈ ℕ` and `0 < h < h*`, then `w_h(x) ~ h2ⁿx^{2n}exp(-x²)` as
`x → -∞`. -/
@[dlmf 32.11.E32]
theorem painleveIV_hermiteAsymptotics {n : ℕ} {h : ℝ} (hh : 0 < h)
    (hh' : h < 1 / (Real.sqrt Real.pi * Real.Gamma (n + 1))) {w : ℝ → ℝ}
    (hw : IsRealODE2SolutionOn (realPainleveIVRhs (2 * n + 1) 0) w univ) (hw0 : ∀ x, w x ≠ 0)
    (hasym : w ~[atTop] fun x => h *
        (parabolicCylinderU (-(n : ℂ) - 1 / 2) ((Real.sqrt 2 * x : ℝ) : ℂ)).re ^ 2) :
    w ~[atBot] fun x => h * 2 ^ n * x ^ (2 * n) * Real.exp (-x ^ 2) := by
  sorry

/-- DLMF 32.11.33–32.11.37: if `ν` is not zero or a positive integer and `0 < h < h*`, then
`w_h(x) = -(2/3)x + (4/3)d√3 sin(φ(x) - θ₀) + O(x⁻¹)` as `x → -∞`, where
`φ(x) = (1/3)√3 x² - (4/3)d²√3 ln(√2|x|)`, `μ = 1 + 2ihπ^{3/2}exp(-iπν)/Γ(-ν)`,
`d² = -(1/4)√3π⁻¹ ln(1 - |μ|²)` (`d > 0`) and
`θ₀ = (1/3)d²√3 ln 3 + (2/3)πν + (7/12)π + ph μ + ph Γ(-(2/3)i√3 d²)`. -/
@[dlmf 32.11.E33, dlmf 32.11.E34, dlmf 32.11.E35, dlmf 32.11.E36, dlmf 32.11.E37]
theorem painleveIV_oscillating {ν h : ℝ} (hν : ∀ n : ℕ, ν ≠ n) (hΓ : 0 < Real.Gamma (ν + 1))
    (hh : 0 < h) (hh' : h < 1 / (Real.sqrt Real.pi * Real.Gamma (ν + 1))) {w : ℝ → ℝ}
    (hw : IsRealODE2SolutionOn (realPainleveIVRhs (2 * ν + 1) 0) w univ) (hw0 : ∀ x, w x ≠ 0)
    (hasym : w ~[atTop] fun x => h *
        (parabolicCylinderU (-(ν : ℂ) - 1 / 2) ((Real.sqrt 2 * x : ℝ) : ℂ)).re ^ 2) :
    let μ : ℂ := 1 + 2 * Complex.I * h * (Real.pi : ℂ) ^ (3 / 2 : ℂ) *
      Complex.exp (-Complex.I * Real.pi * ν) / Complex.Gamma (-ν)
    let d := Real.sqrt (-(1 / 4) * Real.sqrt 3 * Real.pi⁻¹ * Real.log (1 - ‖μ‖ ^ 2))
    let θ₀ := 1 / 3 * d ^ 2 * Real.sqrt 3 * Real.log 3 + 2 / 3 * Real.pi * ν +
      7 / 12 * Real.pi + Complex.arg μ +
      Complex.arg (Complex.Gamma (-(2 / 3) * Complex.I * ((Real.sqrt 3 * d ^ 2 : ℝ) : ℂ)))
    ‖μ‖ < 1 ∧
      (fun x => w x - (-(2 / 3) * x + 4 / 3 * d * Real.sqrt 3 *
        Real.sin (1 / 3 * Real.sqrt 3 * x ^ 2 -
          4 / 3 * d ^ 2 * Real.sqrt 3 * Real.log (Real.sqrt 2 * |x|) - θ₀)))
        =O[atBot] fun x => x⁻¹ := by
  sorry

/-- DLMF 32.11.38: for `h = h*`, `w_{h*}` has no poles on the real axis and
`w_{h*}(x) ~ -2x` as `x → -∞`. -/
@[dlmf 32.11.E38]
theorem painleveIV_critical {ν : ℝ} (hΓ : 0 < Real.Gamma (ν + 1)) :
    ∃ w : ℝ → ℝ, IsRealODE2SolutionOn (realPainleveIVRhs (2 * ν + 1) 0) w univ ∧
      (∀ x, w x ≠ 0) ∧
      (w ~[atTop] fun x => 1 / (Real.sqrt Real.pi * Real.Gamma (ν + 1)) *
          (parabolicCylinderU (-(ν : ℂ)
          - 1 / 2) ((Real.sqrt 2 * x : ℝ) : ℂ)).re ^ 2) ∧
      w ~[atBot] fun x => -2 * x := by
  sorry

/-- §32.11(v): if `h > h*`, then `w_h` has a simple pole on the real axis, at a point `c`
depending on `h`: `w_h` solves 32.11.29 on `(c, ∞)` and `(x - c)w_h(x)` tends to a nonzero
limit as `x → c+`. -/
@[dlmf 32.11.v]
theorem painleveIV_pole {ν h : ℝ} (hΓ : 0 < Real.Gamma (ν + 1))
    (hh : 1 / (Real.sqrt Real.pi * Real.Gamma (ν + 1)) < h) :
    ∃ (w : ℝ → ℝ) (c r : ℝ), r ≠ 0 ∧
      IsRealODE2SolutionOn (realPainleveIVRhs (2 * ν + 1) 0) w (Ioi c) ∧
      (∀ x ∈ Ioi c, w x ≠ 0) ∧
          (w ~[atTop] fun x => h * (parabolicCylinderU (-(ν : ℂ) - 1 / 2) ((Real.sqrt 2
          * x : ℝ) : ℂ)).re ^ 2) ∧
      Tendsto (fun x => (x - c) * w x) (𝓝[>] c) (𝓝 r) := by
  sorry

end DLMF.Painleve
