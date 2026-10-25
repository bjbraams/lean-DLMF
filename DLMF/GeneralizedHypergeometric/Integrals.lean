/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic
public import DLMFMathlib.Analysis.Complex.SeparatingContour

/-!
# Generalized hypergeometric integrals: DLMF §16.5

Barnes contours are specified by absolute continuity on finite pieces, their exact
oriented tails, and separation of the two pole families into distinct components
of the contour complement. This permits finite indentations for arbitrary upper
parameters; positive-real-part upper parameters are not imposed. The logarithm
sheet of `-z` is explicit. Inverse Laplace integrals assert convergence of both
oscillatory tails, not absolute Bochner integrability where that would be false.
-/

@[expose] public section
open Complex Filter Set Finset MeasureTheory
open scoped Topology Real
noncomputable section
namespace DLMF.Hypergeometric

/-- Topological separation of the upper-parameter poles from the nonnegative integers. -/
def genBarnesSeparates (a : Multiset ℂ) (L : ℝ → ℂ) : Prop :=
  Complex.separatesPoleSets L {s | ∃ x ∈ a, ∃ n : ℕ, s = -x - n}
    {s | ∃ n : ℕ, s = n}

/-- An upward Barnes contour with finite indentations and two vertical tails. -/
def genVerticalBarnesContour (a : Multiset ℂ) (L : ℝ → ℂ) : Prop :=
  (∀ T : ℝ, 0 < T → AbsolutelyContinuousOnInterval L (-T) T) ∧
  genBarnesSeparates a L ∧ Complex.hasVerticalTails L

/-- A negatively oriented right-infinite Barnes loop, with horizontal tails. -/
def genRightBarnesContour (a : Multiset ℂ) (L : ℝ → ℂ) : Prop :=
  (∀ T : ℝ, 0 < T → AbsolutelyContinuousOnInterval L (-T) T) ∧
  genBarnesSeparates a L ∧ Complex.hasHorizontalRightTails L

/-- Approach to zero on a closed sector of the logarithmic cover. -/
def genZeroLogSector (θ : ℝ) : Filter ℂ :=
  comap Complex.re atBot ⊓ 𝓟 {w : ℂ | |w.im| ≤ θ}

/-- Separating Barnes contours exist for every nonsingular upper parameter family. -/
theorem genBarnesContours_exist (a : Multiset ℂ) (ha : genDenRegular a) :
    (∃ L : ℝ → ℂ, genVerticalBarnesContour a L) ∧
    (∃ L : ℝ → ℂ, genRightBarnesContour a L) := by
  sorry

/-- The right-loop integral in the entire case and the full open disk in the balanced case. -/
@[dlmf 16.5.E1]
theorem genHG_barnes_right (a b : Multiset ℂ) (ha : genDenRegular a) (hb : genDenRegular b)
    (L : ℝ → ℂ) (hL : genRightBarnesContour a L) (w : ℂ)
    (h : a.card ≤ b.card ∨ (a.card = b.card + 1 ∧ w.re < 0)) :
    genHasBarnesValueLog a b L w (genHG a b (-Complex.exp w)) := by
  sorry

/-- The full vertical convergence sector; for p=q or p=q+1 it gives the principal continued function. -/
@[dlmf 16.5.E1]
theorem genHG_barnes_vertical (a b : Multiset ℂ) (ha : genDenRegular a) (hb : genDenRegular b)
    (L : ℝ → ℂ) (hL : genVerticalBarnesContour a L) (w : ℂ)
    (hpq : b.card < a.card + 1)
    (harg : |w.im| < (a.card + 1 - b.card : ℝ) * Real.pi / 2) :
    genHasBarnesValueLog a b L w (genBarnesHGLog a b L w) ∧
    (a.card ≤ b.card + 1 → genBarnesHGLog a b L w = genHG a b (-Complex.exp w)) := by
  sorry

/-- For p>q+1 the divergent formal series is the Barnes value asymptotic on every closed proper logarithmic sector. -/
@[dlmf 16.5.E1]
theorem genHG_barnes_formal_asymptotic (a b : Multiset ℂ) (ha : genDenRegular a) (hb : genDenRegular b)
    (hpq : b.card + 1 < a.card) (L : ℝ → ℂ) (hL : genVerticalBarnesContour a L)
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδpq : δ < a.card + 1 - b.card) :
    Asymptotics.IsBigO (genZeroLogSector ((a.card + 1 - b.card - δ) * Real.pi / 2))
      (fun w => genBarnesHGLog a b L w -
        ∑ n ∈ range N, genCoeff a b n * (-Complex.exp w) ^ n)
      (fun w : ℂ => Real.exp (N * w.re)) := by
  sorry

/-- Euler integral on the entire domain or the full continued principal slit, with convergence. -/
@[dlmf 16.5.E2]
theorem genHG_euler_integral (a b : Multiset ℂ) (a₀ b₀ : ℂ) (hb : genDenRegular b)
    (ha₀ : 0 < a₀.re) (hb₀ : a₀.re < b₀.re) {z : ℂ}
    (h : a.card ≤ b.card ∨ (a.card = b.card + 1 ∧ z ∈ cutPlane)) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (a₀ - 1) *
      (1 - (t : ℂ)) ^ (b₀ - a₀ - 1) * genHG a b (z * t)) volume 0 1 ∧
    genHG (a₀ ::ₘ a) (b₀ ::ₘ b) z = Gamma b₀ / (Gamma a₀ * Gamma (b₀ - a₀)) *
      ∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ (a₀ - 1) *
        (1 - (t : ℂ)) ^ (b₀ - a₀ - 1) * genHG a b (z * t) := by
  sorry

/-- Laplace integral with the z restriction removed whenever p<q. -/
@[dlmf 16.5.E3]
theorem genHG_laplace_integral (a b : Multiset ℂ) (a₀ : ℂ) (hb : genDenRegular b)
    (ha₀ : 0 < a₀.re) (hpq : a.card ≤ b.card) {z : ℂ}
    (hz : a.card < b.card ∨ z.re < 1) :
    IntegrableOn (fun t : ℝ => Complex.exp (-t) * (t : ℂ) ^ (a₀ - 1) * genHG a b (z * t)) (Ioi 0) ∧
    DLMF.HasIntegralAtTop
      (fun t : ℝ => Complex.exp (-t) * (t : ℂ) ^ (a₀ - 1) * genHG a b (z * t)) 0
      (Gamma a₀ * genHG (a₀ ::ₘ a) b z) := by
  sorry

/-- Inverse Laplace integral with separate oscillatory tails and the full p=q+1 extension. -/
@[dlmf 16.5.E4]
theorem genHG_inverse_laplace (a b : Multiset ℂ) (b₀ : ℂ) (hb : genDenRegular b) (hb₀ : 0 < b₀.re)
    {c : ℝ} (hc : 0 < c) (z : ℂ)
    (h : a.card ≤ b.card ∨ (a.card = b.card + 1 ∧ max 0 z.re < c)) :
    DLMF.HasIntegralWholeLine (fun y : ℝ =>
      Complex.exp (c + y * I) * (c + y * I) ^ (-b₀) * genHG a b (z / (c + y * I)))
      (2 * Real.pi / Gamma b₀ * genHG a (b₀ ::ₘ b) z) := by
  sorry

end DLMF.Hypergeometric
