/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.AppellF4
public import DLMF.GeneralizedHypergeometric.GHATools
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import TauCeti.Topology.LocallyConstant.Preconnected

/-!
# Appell functions and their defining series

Appell series, coefficient identities and differential relations in two complex variables.

Source references and common attribution are retained in
`DLMF.GeneralizedHypergeometric.Appell`.
This module uses results of the Tau Ceti contributors; see also `CREDITS.md`.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory Polynomial

open scoped Real Topology Nat Interval

namespace DLMF.Hypergeometric

/-- A bivariate power series at zero has only its constant term. -/
theorem appell_tsum_zero (c : ℕ × ℕ→ℂ) :
    (∑' p : ℕ × ℕ,c p*0^p.1*0^p.2)=c (0,0) := by
  rw [tsum_eq_single (0,0)]
  · simp
  · rintro ⟨m,n⟩ hp
    by_cases hm : m=0
    · subst m
      have hn : n≠0 := fun hn => hp (by simp [hn])
      simp [hn]
    · simp [hm]

/-- Appell denominator parameters avoid every nonpositive integer. -/
def AppellRegular (c : ℂ) : Prop := ∀ n : ℕ,c≠ -(n:ℂ)

/-- Bidisc of absolute convergence for F1 and F3. -/
def appellBidisc : Set (ℂ × ℂ) := {p | ‖p.1‖<1 ∧ ‖p.2‖<1}

/-- Diamond of absolute convergence for F2. -/
def appellDiamond : Set (ℂ × ℂ) := {p | ‖p.1‖+‖p.2‖<1}

/-- Exact open convergence region of F4. -/
def appellF4Domain : Set (ℂ × ℂ) := {p | Real.sqrt ‖p.1‖+Real.sqrt ‖p.2‖<1}

/-- The first-variable derivative of a bivariate complex function. -/
def appellDx (f : ℂ→ℂ→ℂ) (x y : ℂ) : ℂ := deriv (fun t => f t y) x

/-- The second-variable derivative of a bivariate complex function. -/
def appellDy (f : ℂ→ℂ→ℂ) (x y : ℂ) : ℂ := deriv (f x) y

/-- The first Euler operator in two variables. -/
def appellThetaX (f : ℂ→ℂ→ℂ) : ℂ→ℂ→ℂ := fun x y => x*appellDx f x y

/-- The second Euler operator in two variables. -/
def appellThetaY (f : ℂ→ℂ→ℂ) : ℂ→ℂ→ℂ := fun x y => y*appellDy f x y

/-- Analytic continuation of a two-variable germ along a continuous parameterized path.
This is the two-variable domain analogue of TauCeti.IsAnalyticContinuationAlong. -/
structure IsAppellContinuation (F : ℝ→(ℂ × ℂ→ℂ)) (γ : ℝ→ℂ × ℂ) : Prop where
  /-- The path is continuous on `[0,1]`. -/
  continuousOn : ContinuousOn γ (Icc 0 1)
  /-- Each germ `F t` is analytic at the path point `γ t`. -/
  analyticAt : ∀ t∈Icc 0 1,AnalyticAt ℂ (F t) (γ t)
  /-- Nearby germs agree near the path: `F u = F t` near `γ u` for `u` close to `t`. -/
  locallyEq : ∀ t∈Icc 0 1,∀ᶠ u in 𝓝[Icc 0 1] t,F u=ᶠ[𝓝 (γ u)] F t

/-- A chosen branch is reached from a seed germ by a specified analytic continuation. -/
def IsAppellBranchAt (seed : ℂ × ℂ→ℂ) (p : ℂ × ℂ) (f : ℂ × ℂ→ℂ) : Prop :=
  ∃ γ : ℝ→ℂ × ℂ,∃ F : ℝ→(ℂ × ℂ→ℂ),IsAppellContinuation F γ ∧ γ 0=(0,0) ∧ γ 1=p ∧
    F 0=ᶠ[𝓝 (0,0)] seed ∧ F 1=ᶠ[𝓝 p] f

/-- Appell F1 double-series coefficient. -/
@[dlmf 16.13.E1]
def appF1Coeff (a b b' c : ℂ) (m n : ℕ) : ℂ :=
  poch a (m+n)*poch b m*poch b' n/(poch c (m+n)*(m !*n !))

/-- Appell F2 double-series coefficient. -/
@[dlmf 16.13.E2]
def appF2Coeff (a b b' c c' : ℂ) (m n : ℕ) : ℂ :=
  poch a (m+n)*poch b m*poch b' n/(poch c m*poch c' n*(m !*n !))

/-- Appell F3 double-series coefficient. -/
@[dlmf 16.13.E3]
def appF3Coeff (a a' b b' c : ℂ) (m n : ℕ) : ℂ :=
  poch a m*poch a' n*poch b m*poch b' n/(poch c (m+n)*(m !*n !))

/-- Appell's F₁ as the totalized double series `∑ₘₙ cₘₙ xᵐ yⁿ` (DLMF 16.13.E1);
continuations are represented by analytic germs. -/
@[dlmf 16.13.E1]
def appF1 (a b b' c x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ,appF1Coeff a b b' c p.1 p.2*x^p.1*y^p.2

/-- Appell's F₂ as the totalized double series `∑ₘₙ cₘₙ xᵐ yⁿ` (DLMF 16.13.E2);
continuations are represented by analytic germs. -/
@[dlmf 16.13.E2]
def appF2 (a b b' c c' x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ,appF2Coeff a b b' c c' p.1 p.2*x^p.1*y^p.2

/-- Appell's F₃ as the totalized double series `∑ₘₙ cₘₙ xᵐ yⁿ` (DLMF 16.13.E3);
continuations are represented by analytic germs. -/
@[dlmf 16.13.E3]
def appF3 (a a' b b' c x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ,appF3Coeff a a' b b' c p.1 p.2*x^p.1*y^p.2

/-- Subexponential bound for the F1 coefficients. -/
lemma ghaR4_appF1Coeff_bound (a b b' c : ℂ) (hc : AppellRegular c) {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, ∀ q : ℕ × ℕ, ‖appF1Coeff a b b' c q.1 q.2‖ ≤ C * σ ^ (q.1 + q.2) := by
  obtain ⟨τ, hτ, hτσ⟩ := ghaR4_exists_pow_le hσ 2
  obtain ⟨C1, hC1, h1⟩ := ghaR4_norm_poch_le a c hc hτ
  obtain ⟨C2, hC2, h2⟩ := ghaR4_norm_poch_le_factorial b hτ
  obtain ⟨C3, hC3, h3⟩ := ghaR4_norm_poch_le_factorial b' hτ
  refine ⟨C1 * C2 * C3, fun ⟨m, n⟩ => ?_⟩
  have hcN : 0 < ‖poch c (m + n)‖ := norm_pos_iff.mpr (poch_ne_zero_of_not_neg_nat hc _)
  have hm : (0 : ℝ) < m ! := by exact_mod_cast m.factorial_pos
  have hn : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  have hτ0 : 0 ≤ τ := by linarith
  simp only [appF1Coeff, norm_div, norm_mul, Complex.norm_natCast]
  rw [div_le_iff₀ (by positivity)]
  calc ‖poch a (m + n)‖ * ‖poch b m‖ * ‖poch b' n‖
      ≤ (C1 * τ ^ (m + n) * ‖poch c (m + n)‖) * (C2 * τ ^ m * m !) * (C3 * τ ^ n * n !) := by
        gcongr
        exacts [h1 _, h2 _, h3 _]
    _ = C1 * C2 * C3 * (τ ^ 2) ^ (m + n) * (‖poch c (m + n)‖ * (m ! * n !)) := by ring
    _ ≤ C1 * C2 * C3 * σ ^ (m + n) * (‖poch c (m + n)‖ * (m ! * n !)) := by
        gcongr

/-- Binomially weighted subexponential bound for the F2 coefficients. -/
lemma ghaR4_appF2Coeff_bound (a b b' c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c')
    {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, ∀ q : ℕ × ℕ, ‖appF2Coeff a b b' c c' q.1 q.2‖ ≤
      C * σ ^ (q.1 + q.2) * ((q.1 + q.2).choose q.1 : ℝ) := by
  obtain ⟨τ, hτ, hτσ⟩ := ghaR4_exists_pow_le hσ 2
  obtain ⟨C1, hC1, h1⟩ := ghaR4_norm_poch_le_factorial a hτ
  obtain ⟨C2, hC2, h2⟩ := ghaR4_norm_poch_le b c hc hτ
  obtain ⟨C3, hC3, h3⟩ := ghaR4_norm_poch_le b' c' hc' hτ
  refine ⟨C1 * C2 * C3, fun ⟨m, n⟩ => ?_⟩
  have hcm : 0 < ‖poch c m‖ := norm_pos_iff.mpr (poch_ne_zero_of_not_neg_nat hc _)
  have hcn : 0 < ‖poch c' n‖ := norm_pos_iff.mpr (poch_ne_zero_of_not_neg_nat hc' _)
  have hm : (0 : ℝ) < m ! := by exact_mod_cast m.factorial_pos
  have hn : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  have hτ0 : 0 ≤ τ := by linarith
  have hfac : ((m + n) ! : ℝ) = ((m + n).choose m : ℝ) * m ! * n ! := by
    have := Nat.add_choose_mul_factorial_mul_factorial m n
    rw [← Nat.choose_symm_add] at this
    exact_mod_cast this.symm
  simp only [appF2Coeff, norm_div, norm_mul, Complex.norm_natCast]
  rw [div_le_iff₀ (by positivity)]
  calc ‖poch a (m + n)‖ * ‖poch b m‖ * ‖poch b' n‖
      ≤ (C1 * τ ^ (m + n) * (m + n) !) * (C2 * τ ^ m * ‖poch c m‖) *
          (C3 * τ ^ n * ‖poch c' n‖) := by
        gcongr
        exacts [h1 _, h2 _, h3 _]
    _ = C1 * C2 * C3 * (τ ^ 2) ^ (m + n) * ((m + n).choose m : ℝ) *
          (‖poch c m‖ * ‖poch c' n‖ * (m ! * n !)) := by rw [hfac]; ring
    _ ≤ C1 * C2 * C3 * σ ^ (m + n) * ((m + n).choose m : ℝ) *
          (‖poch c m‖ * ‖poch c' n‖ * (m ! * n !)) := by
        gcongr

/-- Subexponential bound for the F3 coefficients. -/
lemma ghaR4_appF3Coeff_bound (a a' b b' c : ℂ) (hc : AppellRegular c) {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, ∀ q : ℕ × ℕ, ‖appF3Coeff a a' b b' c q.1 q.2‖ ≤ C * σ ^ (q.1 + q.2) := by
  obtain ⟨τ, hτ, hτσ⟩ := ghaR4_exists_pow_le hσ 3
  obtain ⟨C1, hC1, h1⟩ := ghaR4_norm_poch_le_factorial a hτ
  obtain ⟨C2, hC2, h2⟩ := ghaR4_norm_poch_le_factorial a' hτ
  obtain ⟨C3, hC3, h3⟩ := ghaR4_norm_poch_le_factorial b hτ
  obtain ⟨C4, hC4, h4⟩ := ghaR4_norm_poch_le_factorial b' hτ
  obtain ⟨C5, hC5, h5⟩ := ghaR4_factorial_le_norm_poch c hc hτ
  refine ⟨C1 * C2 * C3 * C4 * C5, fun ⟨m, n⟩ => ?_⟩
  have hcN : 0 < ‖poch c (m + n)‖ := norm_pos_iff.mpr (poch_ne_zero_of_not_neg_nat hc _)
  have hm : (0 : ℝ) < m ! := by exact_mod_cast m.factorial_pos
  have hn : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  have hτ0 : 0 ≤ τ := by linarith
  have hfac : (m ! : ℝ) * n ! ≤ (m + n) ! := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add m n)
  have h6 : (m ! : ℝ) * n ! ≤ C5 * τ ^ (m + n) * ‖poch c (m + n)‖ := hfac.trans (h5 _)
  simp only [appF3Coeff, norm_div, norm_mul, Complex.norm_natCast]
  rw [div_le_iff₀ (by positivity)]
  calc ‖poch a m‖ * ‖poch a' n‖ * ‖poch b m‖ * ‖poch b' n‖
      ≤ (C1 * τ ^ m * m !) * (C2 * τ ^ n * n !) * (C3 * τ ^ m * m !) * (C4 * τ ^ n * n !) := by
        gcongr
        exacts [h1 _, h2 _, h3 _, h4 _]
    _ = C1 * C2 * C3 * C4 * (τ ^ 2) ^ (m + n) * (m ! * n !) * (m ! * n !) := by ring
    _ ≤ C1 * C2 * C3 * C4 * (τ ^ 2) ^ (m + n) * (C5 * τ ^ (m + n) * ‖poch c (m + n)‖) *
          (m ! * n !) := by gcongr
    _ = C1 * C2 * C3 * C4 * C5 * (τ ^ 3) ^ (m + n) * (‖poch c (m + n)‖ * (m ! * n !)) := by ring
    _ ≤ C1 * C2 * C3 * C4 * C5 * σ ^ (m + n) * (‖poch c (m + n)‖ * (m ! * n !)) := by
        gcongr

/-- Squared-binomial subexponential bound for the F4 coefficients. -/
lemma ghaR4_appF4Coeff_bound (a b c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c')
    {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, ∀ q : ℕ × ℕ, ‖appF4Coeff a b c c' q.1 q.2‖ ≤
      C * σ ^ (q.1 + q.2) * ((q.1 + q.2).choose q.1 : ℝ) ^ 2 := by
  obtain ⟨τ, hτ, hτσ⟩ := ghaR4_exists_pow_le hσ 3
  obtain ⟨C1, hC1, h1⟩ := ghaR4_norm_poch_le_factorial a hτ
  obtain ⟨C2, hC2, h2⟩ := ghaR4_norm_poch_le_factorial b hτ
  obtain ⟨C3, hC3, h3⟩ := ghaR4_factorial_le_norm_poch c hc hτ
  obtain ⟨C4, hC4, h4⟩ := ghaR4_factorial_le_norm_poch c' hc' hτ
  refine ⟨C1 * C2 * C3 * C4, fun ⟨m, n⟩ => ?_⟩
  have hcm : 0 < ‖poch c m‖ := norm_pos_iff.mpr (poch_ne_zero_of_not_neg_nat hc _)
  have hcn : 0 < ‖poch c' n‖ := norm_pos_iff.mpr (poch_ne_zero_of_not_neg_nat hc' _)
  have hm : (0 : ℝ) < m ! := by exact_mod_cast m.factorial_pos
  have hn : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  have hτ0 : 0 ≤ τ := by linarith
  have hfac : ((m + n) ! : ℝ) = ((m + n).choose m : ℝ) * m ! * n ! := by
    have := Nat.add_choose_mul_factorial_mul_factorial m n
    rw [← Nat.choose_symm_add] at this
    exact_mod_cast this.symm
  simp only [appF4Coeff, norm_div, norm_mul, Complex.norm_natCast]
  rw [div_le_iff₀ (by positivity)]
  calc ‖poch a (m + n)‖ * ‖poch b (m + n)‖
      ≤ (C1 * τ ^ (m + n) * (m + n) !) * (C2 * τ ^ (m + n) * (m + n) !) := by
        gcongr
        exacts [h1 _, h2 _]
    _ = C1 * C2 * (τ ^ 2) ^ (m + n) * ((m + n).choose m : ℝ) ^ 2 * (m ! * n !) *
          (m ! * n !) := by rw [hfac]; ring
    _ ≤ C1 * C2 * (τ ^ 2) ^ (m + n) * ((m + n).choose m : ℝ) ^ 2 * (m ! * n !) *
          ((C3 * τ ^ m * ‖poch c m‖) * (C4 * τ ^ n * ‖poch c' n‖)) := by
        gcongr
        exacts [h3 _, h4 _]
    _ = C1 * C2 * C3 * C4 * (τ ^ 3) ^ (m + n) * ((m + n).choose m : ℝ) ^ 2 *
          (‖poch c m‖ * ‖poch c' n‖ * (m ! * n !)) := by ring
    _ ≤ C1 * C2 * C3 * C4 * σ ^ (m + n) * ((m + n).choose m : ℝ) ^ 2 *
          (‖poch c m‖ * ‖poch c' n‖ * (m ! * n !)) := by
        gcongr

/-- 16.13.E1: hasSum appF1. -/
@[dlmf 16.13.E1]
theorem hasSum_appF1 (a b b' c : ℂ) (hc : AppellRegular c) {x y : ℂ} (hxy : (x,y)∈appellBidisc) :
    HasSum (fun p : ℕ × ℕ => appF1Coeff a b b' c p.1 p.2*x^p.1*y^p.2) (appF1 a b b' c x y) := by
  exact (ghaR4_double_series_hasSum_analytic (fun q => appF1Coeff a b b' c q.1 q.2) appellBidisc
    (fun _ hp => ghaR4_dom_bidisc _ (fun _ hσ => ghaR4_appF1Coeff_bound a b b' c hc hσ)
      hp.1 hp.2)).1 (x, y) hxy

/-- 16.13: analytic appF1. -/
@[dlmf 16.13]
theorem analytic_appF1 (a b b' c : ℂ) (hc : AppellRegular c) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF1 a b b' c p.1 p.2) appellBidisc := by
  exact (ghaR4_double_series_hasSum_analytic (fun q => appF1Coeff a b b' c q.1 q.2) appellBidisc
    (fun _ hp => ghaR4_dom_bidisc _ (fun _ hσ => ghaR4_appF1Coeff_bound a b b' c hc hσ)
      hp.1 hp.2)).2

/-- 16.13.E2: hasSum appF2. -/
@[dlmf 16.13.E2]
theorem hasSum_appF2 (a b b' c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') {x y : ℂ} (hxy : (x,y)∈appellDiamond) :
    HasSum (fun p : ℕ × ℕ => appF2Coeff a b b' c c' p.1 p.2*x^p.1*y^p.2) (appF2 a b b' c c' x y) := by
  exact (ghaR4_double_series_hasSum_analytic (fun q => appF2Coeff a b b' c c' q.1 q.2)
    appellDiamond (fun _ hp => ghaR4_dom_diamond _
      (fun _ hσ => ghaR4_appF2Coeff_bound a b b' c c' hc hc' hσ) hp)).1 (x, y) hxy

/-- 16.13: analytic appF2. -/
@[dlmf 16.13]
theorem analytic_appF2 (a b b' c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF2 a b b' c c' p.1 p.2) appellDiamond := by
  exact (ghaR4_double_series_hasSum_analytic (fun q => appF2Coeff a b b' c c' q.1 q.2)
    appellDiamond (fun _ hp => ghaR4_dom_diamond _
      (fun _ hσ => ghaR4_appF2Coeff_bound a b b' c c' hc hc' hσ) hp)).2

/-- 16.13.E3: hasSum appF3. -/
@[dlmf 16.13.E3]
theorem hasSum_appF3 (a a' b b' c : ℂ) (hc : AppellRegular c) {x y : ℂ} (hxy : (x,y)∈appellBidisc) :
    HasSum (fun p : ℕ × ℕ => appF3Coeff a a' b b' c p.1 p.2*x^p.1*y^p.2) (appF3 a a' b b' c x y) := by
  exact (ghaR4_double_series_hasSum_analytic (fun q => appF3Coeff a a' b b' c q.1 q.2)
    appellBidisc (fun _ hp => ghaR4_dom_bidisc _
      (fun _ hσ => ghaR4_appF3Coeff_bound a a' b b' c hc hσ) hp.1 hp.2)).1 (x, y) hxy

/-- 16.13: analytic appF3. -/
@[dlmf 16.13]
theorem analytic_appF3 (a a' b b' c : ℂ) (hc : AppellRegular c) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF3 a a' b b' c p.1 p.2) appellBidisc := by
  exact (ghaR4_double_series_hasSum_analytic (fun q => appF3Coeff a a' b b' c q.1 q.2)
    appellBidisc (fun _ hp => ghaR4_dom_bidisc _
      (fun _ hσ => ghaR4_appF3Coeff_bound a a' b b' c hc hσ) hp.1 hp.2)).2

/-- 16.13.E4: hasSum appF4. -/
@[dlmf 16.13.E4]
theorem hasSum_appF4 (a b c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') {x y : ℂ} (hxy : (x,y)∈appellF4Domain) :
    HasSum (fun p : ℕ × ℕ => appF4Coeff a b c c' p.1 p.2*x^p.1*y^p.2) (appF4 a b c c' x y) := by
  exact (ghaR4_double_series_hasSum_analytic (fun q => appF4Coeff a b c c' q.1 q.2)
    appellF4Domain (fun _ hp => ghaR4_dom_F4 _
      (fun _ hσ => ghaR4_appF4Coeff_bound a b c c' hc hc' hσ) hp)).1 (x, y) hxy

/-- 16.13: analytic appF4. -/
@[dlmf 16.13]
theorem analytic_appF4 (a b c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF4 a b c c' p.1 p.2) appellF4Domain := by
  exact (ghaR4_double_series_hasSum_analytic (fun q => appF4Coeff a b c c' q.1 q.2)
    appellF4Domain (fun _ hp => ghaR4_dom_F4 _
      (fun _ hσ => ghaR4_appF4Coeff_bound a b c c' hc hc' hσ) hp)).2

/-- 16.13.E1: appF1 zero. -/
@[dlmf 16.13.E1]
theorem appF1_zero (a b b' c : ℂ) : appF1 a b b' c 0 0=1 := by
  rw [appF1,appell_tsum_zero]; simp [appF1Coeff,poch_zero]

/-- 16.13.E2: appF2 zero. -/
@[dlmf 16.13.E2]
theorem appF2_zero (a b b' c c' : ℂ) : appF2 a b b' c c' 0 0=1 := by
  rw [appF2,appell_tsum_zero]; simp [appF2Coeff,poch_zero]

/-- 16.13.E3: appF3 zero. -/
@[dlmf 16.13.E3]
theorem appF3_zero (a a' b b' c : ℂ) : appF3 a a' b b' c 0 0=1 := by
  rw [appF3,appell_tsum_zero]; simp [appF3Coeff,poch_zero]

/-- Concrete parameter witnesses make the prose non-product claim mathematically precise. -/
@[dlmf 16.13]
theorem appell_generic_nonseparable :
    (¬∃ f g : ℂ→ℂ,AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ g 0 ∧
      (fun p : ℂ × ℂ => appF1 1 1 1 2 p.1 p.2)=ᶠ[𝓝 (0,0)] (fun p => f p.1*g p.2)) ∧
    (¬∃ f g : ℂ→ℂ,AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ g 0 ∧
      (fun p : ℂ × ℂ => appF2 1 1 1 1 1 p.1 p.2)=ᶠ[𝓝 (0,0)] (fun p => f p.1*g p.2)) ∧
    (¬∃ f g : ℂ→ℂ,AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ g 0 ∧
      (fun p : ℂ × ℂ => appF3 1 1 1 1 2 p.1 p.2)=ᶠ[𝓝 (0,0)] (fun p => f p.1*g p.2)) ∧
    (¬∃ f g : ℂ→ℂ,AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ g 0 ∧
      (fun p : ℂ × ℂ => appF4 1 1 1 1 p.1 p.2)=ᶠ[𝓝 (0,0)] (fun p => f p.1*g p.2)) := by
  sorry

/-- 16.14.E1: appF1 pde. -/
@[dlmf 16.14.E1]
theorem appF1_pde (a b b' c : ℂ) (hc : AppellRegular c) {x y : ℂ} (hxy : (x,y)∈appellBidisc) :
    let f := appF1 a b b' c
    x*(1-x)*appellDx (appellDx f) x y+y*(1-x)*appellDx (appellDy f) x y+(c-(a+b+1)*x)*appellDx f x y-b*y*appellDy f x y-a*b*f x y=0 ∧
    y*(1-y)*appellDy (appellDy f) x y+x*(1-y)*appellDx (appellDy f) x y+(c-(a+b'+1)*y)*appellDy f x y-b'*x*appellDx f x y-a*b'*f x y=0 := by
  sorry

/-- 16.14.E2: appF2 pde. -/
@[dlmf 16.14.E2]
theorem appF2_pde (a b b' c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') {x y : ℂ} (hxy : (x,y)∈appellDiamond) :
    let f := appF2 a b b' c c'
    x*(1-x)*appellDx (appellDx f) x y-x*y*appellDx (appellDy f) x y+(c-(a+b+1)*x)*appellDx f x y-b*y*appellDy f x y-a*b*f x y=0 ∧
    y*(1-y)*appellDy (appellDy f) x y-x*y*appellDx (appellDy f) x y+(c'-(a+b'+1)*y)*appellDy f x y-b'*x*appellDx f x y-a*b'*f x y=0 := by
  sorry

/-- 16.14.E3: appF3 pde. -/
@[dlmf 16.14.E3]
theorem appF3_pde (a a' b b' c : ℂ) (hc : AppellRegular c) {x y : ℂ} (hxy : (x,y)∈appellBidisc) :
    let f := appF3 a a' b b' c
    x*(1-x)*appellDx (appellDx f) x y+y*appellDx (appellDy f) x y+(c-(a+b+1)*x)*appellDx f x y-a*b*f x y=0 ∧
    y*(1-y)*appellDy (appellDy f) x y+x*appellDx (appellDy f) x y+(c-(a'+b'+1)*y)*appellDy f x y-a'*b'*f x y=0 := by
  sorry

/-- 16.14.E4: appF4 pde. -/
@[dlmf 16.14.E4]
theorem appF4_pde (a b c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') {x y : ℂ} (hxy : (x,y)∈appellF4Domain) :
    let f := appF4 a b c c'
    x*(1-x)*appellDx (appellDx f) x y-2*x*y*appellDx (appellDy f) x y-y^2*appellDy (appellDy f) x y+(c-(a+b+1)*x)*appellDx f x y-(a+b+1)*y*appellDy f x y-a*b*f x y=0 ∧
    y*(1-y)*appellDy (appellDy f) x y-2*x*y*appellDx (appellDy f) x y-x^2*appellDx (appellDx f) x y+(c'-(a+b+1)*y)*appellDy f x y-(a+b+1)*x*appellDx f x y-a*b*f x y=0 := by
  sorry

/-- Horn G2 in the gamma-ratio normalization. -/
@[dlmf 16.14.E5]
def hornG2 (a a' b b' x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ,Gamma (a+p.1)*Gamma (a'+p.2)*Gamma (b+p.2-p.1)*Gamma (b'+p.1-p.2)/
    (Gamma a*Gamma a'*Gamma b*Gamma b'*(p.1 !*p.2 !))*x^p.1*y^p.2

/-- Horn G3 in the gamma-ratio normalization. -/
@[dlmf 16.14.E6]
def hornG3 (a a' x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ,Gamma (a+2*p.2-p.1)*Gamma (a'+2*p.1-p.2)/
    (Gamma a*Gamma a'*(p.1 !*p.2 !))*x^p.1*y^p.2

/-- A non-integral parameter is regular. -/
lemma ghaR4_regular_of_nonint {b : ℂ} (hb : ∀ k : ℤ, b ≠ k) : ∀ k : ℕ, b ≠ -k :=
  fun k h => hb (-(k : ℤ)) (by rw [h]; push_cast; ring)

/-- `Γ(b+j) = (b)ⱼ Γ(b)` at regular `b`. -/
lemma ghaR4_gamma_add_nat {b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (j : ℕ) :
    Gamma (b + j) = poch b j * Gamma b := by
  have h := Complex.Gamma_add_nat_div_Gamma_eq (n := j) b hb
  rw [div_eq_iff (Complex.Gamma_ne_zero hb)] at h
  exact h

/-- `Γ(b+j)Γ(b'-j) = (-1)^j (b)ⱼ/(1-b')ⱼ · Γ(b)Γ(b')` for non-integral `b, b'`. -/
lemma ghaR4_gamma_pair {b b' : ℂ} (hb : ∀ k : ℤ, b ≠ k) (hb' : ∀ k : ℤ, b' ≠ k) (j : ℕ) :
    Gamma (b + j) * Gamma (b' - j) =
      (-1) ^ j * poch b j / poch (1 - b') j * (Gamma b * Gamma b') := by
  have hbr := ghaR4_regular_of_nonint hb
  have hb'r : ∀ k : ℕ, b' - j ≠ -k := fun k h => hb' (j - k) (by
    push_cast; linear_combination h)
  have h1 := ghaR4_gamma_add_nat hb'r j
  rw [sub_add_cancel] at h1
  have hr := poch_reflect (1 - b') j
  rw [show 1 - (1 - b') - (j : ℂ) = b' - j by ring] at hr
  have h1b' : ∀ k : ℕ, 1 - b' ≠ -k := fun k h => hb' (k + 1) (by push_cast; linear_combination -h)
  have hp := poch_ne_zero_of_not_neg_nat h1b' j
  have hpj : poch (b' - j) j ≠ 0 := by rw [hr]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hp
  rw [ghaR4_gamma_add_nat hbr j]
  have hG : Gamma (b' - j) = Gamma b' / poch (b' - j) j := by
    rw [h1]; field_simp
  rw [hG, hr]
  have hs : (-1 : ℂ) ^ (j * 2) = 1 := by rw [pow_mul']; norm_num
  field_simp
  linear_combination (-(poch b j * Gamma b * Gamma b')) * hs

/-- Subexponential bound for the Horn G2 Gamma pair `Γ(b+n-m)Γ(b'+m-n)`. -/
lemma ghaR4_gamma_shift_bound {b b' : ℂ} (hb : ∀ k : ℤ, b ≠ k) (hb' : ∀ k : ℤ, b' ≠ k)
    {σ : ℝ} (hσ : 1 < σ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m n : ℕ,
      ‖Gamma (b + n - m) * Gamma (b' + m - n)‖ ≤ C * σ ^ (m + n) * ‖Gamma b * Gamma b'‖ := by
  have h1b' : ∀ k : ℕ, 1 - b' ≠ -k := fun k h => hb' (k + 1) (by push_cast; linear_combination -h)
  have h1b : ∀ k : ℕ, 1 - b ≠ -k := fun k h => hb (k + 1) (by push_cast; linear_combination -h)
  obtain ⟨C1, hC1, h1⟩ := ghaR4_norm_poch_le b (1 - b') h1b' hσ
  obtain ⟨C2, hC2, h2⟩ := ghaR4_norm_poch_le b' (1 - b) h1b hσ
  refine ⟨C1 + C2, by positivity, fun m n => ?_⟩
  have hσ0 : 0 ≤ σ := by linarith
  have hG0 := norm_nonneg (Gamma b * Gamma b')
  rcases le_total m n with hmn | hnm
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have e1 : b + ((m + j : ℕ) : ℂ) - m = b + j := by push_cast; ring
    have e2 : b' + (m : ℂ) - ((m + j : ℕ) : ℂ) = b' - j := by push_cast; ring
    rw [e1, e2, ghaR4_gamma_pair hb hb' j]
    have hp := norm_pos_iff.mpr (poch_ne_zero_of_not_neg_nat h1b' j)
    rw [norm_mul, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have hj : ‖poch b j‖ / ‖poch (1 - b') j‖ ≤ C1 * σ ^ j := by
      rw [div_le_iff₀ hp]; exact h1 j
    have hσj : σ ^ j ≤ σ ^ (m + (m + j)) := pow_le_pow_right₀ hσ.le (by omega)
    calc ‖poch b j‖ / ‖poch (1 - b') j‖ * ‖Gamma b * Gamma b'‖
        ≤ C1 * σ ^ j * ‖Gamma b * Gamma b'‖ := by gcongr
      _ ≤ (C1 + C2) * σ ^ (m + (m + j)) * ‖Gamma b * Gamma b'‖ := by
        gcongr
        · linarith
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have e1 : b + (n : ℂ) - ((n + j : ℕ) : ℂ) = b - j := by push_cast; ring
    have e2 : b' + ((n + j : ℕ) : ℂ) - n = b' + j := by push_cast; ring
    rw [e1, e2, mul_comm, ghaR4_gamma_pair hb' hb j, mul_comm (Gamma b') (Gamma b)]
    have hp := norm_pos_iff.mpr (poch_ne_zero_of_not_neg_nat h1b j)
    rw [norm_mul, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have hj : ‖poch b' j‖ / ‖poch (1 - b) j‖ ≤ C2 * σ ^ j := by
      rw [div_le_iff₀ hp]; exact h2 j
    have hσj : σ ^ j ≤ σ ^ (n + j + n) := pow_le_pow_right₀ hσ.le (by omega)
    calc ‖poch b' j‖ / ‖poch (1 - b) j‖ * ‖Gamma b * Gamma b'‖
        ≤ C2 * σ ^ j * ‖Gamma b * Gamma b'‖ := by gcongr
      _ ≤ (C1 + C2) * σ ^ (n + j + n) * ‖Gamma b * Gamma b'‖ := by
        gcongr
        · linarith

/-- 16.14.E5: hornG2 summable. -/
@[dlmf 16.14.E5]
theorem hornG2_summable (a a' b b' : ℂ) (ha : AppellRegular a) (ha' : AppellRegular a')
    (hb : ∀ k : ℤ,b≠k) (hb' : ∀ k : ℤ,b'≠k) {x y : ℂ} (hxy : (x,y)∈appellBidisc) :
    Summable (fun p : ℕ × ℕ => Gamma (a+p.1)*Gamma (a'+p.2)*Gamma (b+p.2-p.1)*Gamma (b'+p.1-p.2)/
      (Gamma a*Gamma a'*Gamma b*Gamma b'*(p.1 !*p.2 !))*x^p.1*y^p.2) := by
  have hGa := Complex.Gamma_ne_zero ha
  have hGa' := Complex.Gamma_ne_zero ha'
  have hGb := Complex.Gamma_ne_zero (ghaR4_regular_of_nonint hb)
  have hGb' := Complex.Gamma_ne_zero (ghaR4_regular_of_nonint hb')
  have hbound : ∀ σ : ℝ, 1 < σ → ∃ C : ℝ, ∀ q : ℕ × ℕ,
      ‖Gamma (a+q.1)*Gamma (a'+q.2)*Gamma (b+q.2-q.1)*Gamma (b'+q.1-q.2)/
        (Gamma a*Gamma a'*Gamma b*Gamma b'*(q.1 !*q.2 !))‖ ≤ C * σ ^ (q.1 + q.2) := by
    intro σ hσ
    obtain ⟨τ, hτ, hτσ⟩ := ghaR4_exists_pow_le hσ 2
    obtain ⟨C1, hC1, h1⟩ := ghaR4_norm_poch_le_factorial a hτ
    obtain ⟨C2, hC2, h2⟩ := ghaR4_norm_poch_le_factorial a' hτ
    obtain ⟨C3, hC3, h3⟩ := ghaR4_gamma_shift_bound hb hb' hτ
    refine ⟨C1 * C2 * C3, fun ⟨m, n⟩ => ?_⟩
    simp only
    have hm : (0 : ℝ) < m ! := by exact_mod_cast m.factorial_pos
    have hn : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
    have hτ0 : 0 ≤ τ := by linarith
    rw [ghaR4_gamma_add_nat ha m, ghaR4_gamma_add_nat ha' n]
    have e : poch a m * Gamma a * (poch a' n * Gamma a') * Gamma (b + n - m) * Gamma (b' + m - n) /
        (Gamma a * Gamma a' * Gamma b * Gamma b' * (m ! * n !)) =
        poch a m * poch a' n * (Gamma (b + n - m) * Gamma (b' + m - n)) /
          ((Gamma b * Gamma b') * (m ! * n !)) := by
      field_simp
    have hm0 : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hn0 : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hden : 0 < ‖Gamma b * Gamma b' * ((m ! : ℂ) * n !)‖ :=
      norm_pos_iff.mpr (mul_ne_zero (mul_ne_zero hGb hGb') (mul_ne_zero hm0 hn0))
    rw [e, norm_div, div_le_iff₀ hden]
    calc ‖poch a m * poch a' n * (Gamma (b + n - m) * Gamma (b' + m - n))‖
        = ‖poch a m‖ * ‖poch a' n‖ * ‖Gamma (b + n - m) * Gamma (b' + m - n)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ (C1 * τ ^ m * m !) * (C2 * τ ^ n * n !) *
            (C3 * τ ^ (m + n) * ‖Gamma b * Gamma b'‖) := by
          gcongr
          exacts [h1 m, h2 n, h3 m n]
      _ = C1 * C2 * C3 * (τ ^ 2) ^ (m + n) * ‖Gamma b * Gamma b' * ((m ! : ℂ) * n !)‖ := by
          simp only [norm_mul, Complex.norm_natCast]
          ring
      _ ≤ C1 * C2 * C3 * σ ^ (m + n) * ‖Gamma b * Gamma b' * ((m ! : ℂ) * n !)‖ := by gcongr
  obtain ⟨A, B, hA, hB, hS⟩ := ghaR4_dom_bidisc _ hbound hxy.1 hxy.2
  refine Summable.of_norm_bounded hS fun q => ?_
  rw [norm_mul, norm_mul, norm_pow, norm_pow]
  have hA0 : 0 ≤ A := (norm_nonneg _).trans hA.le
  have := norm_nonneg (Gamma (a+q.1)*Gamma (a'+q.2)*Gamma (b+q.2-q.1)*Gamma (b'+q.1-q.2)/
        (Gamma a*Gamma a'*Gamma b*Gamma b'*(q.1 !*q.2 !)))
  gcongr

/-- Gamma bounds at forward and backward integer shifts of a non-integral parameter. -/
lemma ghaR4_gamma_int_bound {a : ℂ} (ha : ∀ k : ℤ, a ≠ k) {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, ‖Gamma (a + j)‖ ≤ C * σ ^ j * j ! ∧
      ‖Gamma (a - j)‖ * j ! ≤ C * σ ^ j := by
  have har := ghaR4_regular_of_nonint ha
  have h1a : ∀ k : ℕ, 1 - a ≠ -k := fun k h => ha (k + 1) (by push_cast; linear_combination -h)
  obtain ⟨C1, hC1, h1⟩ := ghaR4_norm_poch_le_factorial a hσ
  obtain ⟨C2, hC2, h2⟩ := ghaR4_factorial_le_norm_poch (1 - a) h1a hσ
  refine ⟨(C1 + C2) * ‖Gamma a‖, by positivity, fun j => ⟨?_, ?_⟩⟩
  · rw [ghaR4_gamma_add_nat har j, norm_mul]
    calc ‖poch a j‖ * ‖Gamma a‖ ≤ (C1 * σ ^ j * j !) * ‖Gamma a‖ := by gcongr; exact h1 j
      _ ≤ (C1 + C2) * ‖Gamma a‖ * σ ^ j * j ! := by
        have : 0 ≤ C2 * ‖Gamma a‖ * σ ^ j * j ! := by positivity
        nlinarith
  · -- Γ(a) = (a-j)ⱼ Γ(a-j) with (a-j)ⱼ = (-1)^j (1-a)ⱼ
    have hb'r : ∀ k : ℕ, a - j ≠ -k := fun k h => ha (j - k) (by push_cast; linear_combination h)
    have hG := ghaR4_gamma_add_nat hb'r j
    rw [sub_add_cancel] at hG
    have hr := poch_reflect (1 - a) j
    rw [show 1 - (1 - a) - (j : ℂ) = a - j by ring] at hr
    rw [hr] at hG
    have hn : ‖Gamma a‖ = ‖poch (1 - a) j‖ * ‖Gamma (a - j)‖ := by
      rw [hG, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [hn]
    have hG0 := norm_nonneg (Gamma (a - j))
    calc ‖Gamma (a - j)‖ * j ! ≤ ‖Gamma (a - j)‖ * (C2 * σ ^ j * ‖poch (1 - a) j‖) := by
          gcongr; exact h2 j
      _ ≤ (C1 + C2) * (‖poch (1 - a) j‖ * ‖Gamma (a - j)‖) * σ ^ j := by
        have : 0 ≤ C1 * (‖poch (1 - a) j‖ * ‖Gamma (a - j)‖) * σ ^ j := by positivity
        nlinarith

/-- `(A+B)! ≤ 2^(A+B) A! B!`. -/
lemma ghaR4_choose_fact {A B : ℕ} : ((A + B) ! : ℝ) ≤ 2 ^ (A + B) * (A ! * B !) := by
  have h := Nat.add_choose_mul_factorial_mul_factorial A B
  rw [← Nat.choose_symm_add] at h
  have h2 : (((A + B).choose A : ℕ) : ℝ) ≤ 2 ^ (A + B) := by exact_mod_cast Nat.choose_le_two_pow _ _
  calc ((A + B) ! : ℝ) = ((A + B).choose A : ℕ) * (A ! * B !) := by
        rw [← h]; push_cast; ring
    _ ≤ _ := by gcongr

/-- The mixed case of `ghaR4_gamma_G3_bound`: a forward Gamma factor at shift
`k = (j+1) + N` and a backward one at shift `j+1 ≤ N` multiply to at most
`C₁ C₂ σ^{4N} 4^N N!`. -/
private lemma ghaR4_gamma_mixed_bound {σ C1 C2 : ℝ} (hσ : 1 < σ) (hC1 : 0 ≤ C1)
    (hC2 : 0 ≤ C2) {x y : ℂ} {k j N : ℕ} (hkN : k = (j + 1) + N) (hjN : j + 1 ≤ N)
    (hx : ‖x‖ ≤ C1 * σ ^ k * k !) (hy : ‖y‖ * (j + 1) ! ≤ C2 * σ ^ (j + 1)) :
    ‖x‖ * ‖y‖ ≤ C1 * C2 * σ ^ (4 * N) * 4 ^ N * N ! := by
  have hσ0 : 0 ≤ σ := by linarith
  have hf : ((k ! : ℕ) : ℝ) ≤ 2 ^ k * ((j + 1) ! * N !) := by
    rw [hkN]; exact ghaR4_choose_fact
  have hj0 : (0 : ℝ) < (j + 1) ! := by exact_mod_cast (j + 1).factorial_pos
  have hy' : ‖y‖ ≤ C2 * σ ^ (j + 1) / (j + 1) ! := by rw [le_div_iff₀ hj0]; exact hy
  calc ‖x‖ * ‖y‖ ≤ (C1 * σ ^ k * k !) * (C2 * σ ^ (j + 1) / (j + 1) !) :=
        mul_le_mul hx hy' (norm_nonneg _) (by positivity)
    _ ≤ (C1 * σ ^ k * (2 ^ k * ((j + 1) ! * N !))) * (C2 * σ ^ (j + 1) / (j + 1) !) := by
        gcongr
    _ = C1 * C2 * σ ^ (k + (j + 1)) * 2 ^ k * N ! := by
        rw [pow_add]; field_simp; ring
    _ ≤ C1 * C2 * σ ^ (4 * N) * 2 ^ (2 * N) * N ! := by
        have hs := pow_le_pow_right₀ hσ.le (show k + (j + 1) ≤ 4 * N by omega)
        have h2' := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num)
          (show k ≤ 2 * N by omega)
        have h0 : 0 ≤ C1 * C2 := by positivity
        have := mul_le_mul (mul_le_mul_of_nonneg_left hs h0) h2' (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right this (by positivity)
    _ = _ := by rw [show (2:ℝ) ^ (2 * N) = 4 ^ N by rw [pow_mul]; norm_num]

/-- Gamma bound for the Horn G3 pair:
`|Γ(a+2n-m) Γ(a'+2m-n)| ≤ C σ^{4(m+n)} 4^{m+n} (m+n)!` for non-integral `a, a'`. -/
lemma ghaR4_gamma_G3_bound {a a' : ℂ} (ha : ∀ k : ℤ, a ≠ k) (ha' : ∀ k : ℤ, a' ≠ k)
    {σ : ℝ} (hσ : 1 < σ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m n : ℕ,
      ‖Gamma (a + 2 * n - m) * Gamma (a' + 2 * m - n)‖ ≤
        C * σ ^ (4 * (m + n)) * 4 ^ (m + n) * (m + n) ! := by
  obtain ⟨C1, hC1, h1⟩ := ghaR4_gamma_int_bound ha hσ
  obtain ⟨C2, hC2, h2⟩ := ghaR4_gamma_int_bound ha' hσ
  refine ⟨C1 * C2, by positivity, fun m n => ?_⟩
  have hσ0 : 0 ≤ σ := by linarith
  have h41 : (1 : ℝ) ≤ 4 ^ (m + n) := one_le_pow₀ (by norm_num)
  have hfN : (0 : ℝ) < (m + n) ! := by exact_mod_cast (m + n).factorial_pos
  rw [norm_mul]
  rcases le_or_gt m (2 * n) with hm | hm
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
    have e1 : a + 2 * (n : ℂ) - m = a + k := by
      have : (2 * n : ℕ) = m + k := hk
      rw [show (2 : ℂ) * n = ((2 * n : ℕ) : ℂ) by push_cast; ring, this]; push_cast; ring
    rw [e1]
    rcases le_or_gt n (2 * m) with hn | hn
    · -- both arguments are a shift by a natural number
      obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le hn
      have e2 : a' + 2 * (m : ℂ) - n = a' + l := by
        have : (2 * m : ℕ) = n + l := hl
        rw [show (2 : ℂ) * m = ((2 * m : ℕ) : ℂ) by push_cast; ring, this]; push_cast; ring
      have hkl : k + l = m + n := by omega
      rw [e2]
      have hf : ((k ! : ℕ) : ℝ) * l ! ≤ (m + n) ! := by
        rw [← hkl]; exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _)
          (Nat.factorial_mul_factorial_dvd_factorial_add k l)
      calc ‖Gamma (a + k)‖ * ‖Gamma (a' + l)‖ ≤ (C1 * σ ^ k * k !) * (C2 * σ ^ l * l !) :=
            mul_le_mul (h1 k).1 (h2 l).1 (norm_nonneg _) (by positivity)
        _ = C1 * C2 * σ ^ (k + l) * (k ! * l !) := by rw [pow_add]; ring
        _ ≤ C1 * C2 * σ ^ (4 * (m + n)) * (m + n) ! := by
            have hs := pow_le_pow_right₀ hσ.le (show k + l ≤ 4 * (m + n) by omega)
            have h0 : 0 ≤ C1 * C2 := by positivity
            exact mul_le_mul (mul_le_mul_of_nonneg_left hs h0) hf (by positivity) (by positivity)
        _ ≤ _ := by
            have : 0 ≤ C1 * C2 * σ ^ (4 * (m + n)) * (m + n) ! := by positivity
            nlinarith
    · -- `2m < n`: the first argument is a forward shift, the second a backward one
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt hn
      have e2 : a' + 2 * (m : ℂ) - n = a' - ((j + 1 : ℕ) : ℂ) := by
        rw [hj]; push_cast; ring
      rw [e2]
      exact ghaR4_gamma_mixed_bound hσ hC1 hC2 (by omega) (by omega) (h1 k).1 (h2 (j + 1)).2
  · -- `2n < m`
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt hm
    obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le (show n ≤ 2 * m by omega)
    have e1 : a + 2 * (n : ℂ) - m = a - ((j + 1 : ℕ) : ℂ) := by
      rw [hj]; push_cast; ring
    have e2 : a' + 2 * (m : ℂ) - n = a' + l := by
      have : (2 * m : ℕ) = n + l := hl
      rw [show (2 : ℂ) * m = ((2 * m : ℕ) : ℂ) by push_cast; ring, this]; push_cast; ring
    rw [e1, e2, mul_comm ‖Gamma (a - _)‖, mul_comm C1 C2]
    exact ghaR4_gamma_mixed_bound hσ hC2 hC1 (by omega) (by omega) (h2 l).1 (h1 (j + 1)).2

/-- 16.14.E6: hornG3 summable. -/
@[dlmf 16.14.E6]
theorem hornG3_summable (a a' : ℂ) (ha : ∀ k : ℤ,a≠k) (ha' : ∀ k : ℤ,a'≠k)
    {x y : ℂ} (hxy : ‖x‖+‖y‖<(1/4:ℝ)) :
    Summable (fun p : ℕ × ℕ => Gamma (a+2*p.2-p.1)*Gamma (a'+2*p.1-p.2)/
      (Gamma a*Gamma a'*(p.1 !*p.2 !))*x^p.1*y^p.2) := by
  have hGa := Complex.Gamma_ne_zero (ghaR4_regular_of_nonint ha)
  have hGa' := Complex.Gamma_ne_zero (ghaR4_regular_of_nonint ha')
  set c : ℕ × ℕ → ℂ := fun p => Gamma (a+2*p.2-p.1)*Gamma (a'+2*p.1-p.2)/
      (Gamma a*Gamma a'*(p.1 !*p.2 !)) / 4 ^ (p.1 + p.2) with hc
  have hbound : ∀ σ : ℝ, 1 < σ → ∃ C : ℝ, ∀ q : ℕ × ℕ,
      ‖c q‖ ≤ C * σ ^ (q.1 + q.2) * ((q.1 + q.2).choose q.1 : ℝ) := by
    intro σ hσ
    obtain ⟨τ, hτ, hτσ⟩ := ghaR4_exists_pow_le hσ 4
    obtain ⟨C, hC0, hC⟩ := ghaR4_gamma_G3_bound ha ha' hτ
    have hGn : 0 < ‖Gamma a * Gamma a'‖ := norm_pos_iff.mpr (mul_ne_zero hGa hGa')
    refine ⟨C / ‖Gamma a * Gamma a'‖, fun ⟨m, n⟩ => ?_⟩
    have hm : (0 : ℝ) < m ! := by exact_mod_cast m.factorial_pos
    have hn : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
    have hfac : ((m + n) ! : ℝ) = ((m + n).choose m : ℝ) * m ! * n ! := by
      have := Nat.add_choose_mul_factorial_mul_factorial m n
      rw [← Nat.choose_symm_add] at this
      exact_mod_cast this.symm
    have hm0 : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hn0 : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hden : 0 < ‖Gamma a * Gamma a' * ((m ! : ℂ) * n !)‖ * ‖(4 : ℂ) ^ (m + n)‖ := by
      have := norm_pos_iff.mpr (mul_ne_zero (mul_ne_zero hGa hGa') (mul_ne_zero hm0 hn0))
      have h4 : 0 < ‖(4 : ℂ) ^ (m + n)‖ := norm_pos_iff.mpr (pow_ne_zero _ (by norm_num))
      positivity
    simp only [hc]
    rw [norm_div, norm_div, div_div, div_le_iff₀ hden]
    have hτ4 : (τ ^ 4) ^ (m + n) ≤ σ ^ (m + n) := pow_le_pow_left₀ (by positivity) hτσ _
    calc ‖Gamma (a + 2 * n - m) * Gamma (a' + 2 * m - n)‖
        ≤ C * τ ^ (4 * (m + n)) * 4 ^ (m + n) * (m + n) ! := hC m n
      _ = C / ‖Gamma a * Gamma a'‖ * (τ ^ 4) ^ (m + n) * ((m + n).choose m : ℝ) *
          (‖Gamma a * Gamma a' * ((m ! : ℂ) * n !)‖ * ‖(4 : ℂ) ^ (m + n)‖) := by
          rw [hfac, ← pow_mul]
          simp only [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_ofNat]
          field_simp
      _ ≤ C / ‖Gamma a * Gamma a'‖ * σ ^ (m + n) * ((m + n).choose m : ℝ) *
          (‖Gamma a * Gamma a' * ((m ! : ℂ) * n !)‖ * ‖(4 : ℂ) ^ (m + n)‖) := by gcongr
  have hxy4 : ‖4 * x‖ + ‖4 * y‖ < 1 := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]; linarith
  obtain ⟨A, B, hA, hB, hS⟩ := ghaR4_dom_diamond c hbound hxy4
  refine Summable.of_norm_bounded hS fun q => ?_
  have e : Gamma (a+2*q.2-q.1)*Gamma (a'+2*q.1-q.2)/(Gamma a*Gamma a'*(q.1 !*q.2 !))*x^q.1*y^q.2 =
      c q * (4 * x) ^ q.1 * (4 * y) ^ q.2 := by
    simp only [hc, mul_pow, pow_add]
    field_simp
  rw [e, norm_mul, norm_mul, norm_pow, norm_pow]
  have hA0 : 0 ≤ A := (norm_nonneg _).trans hA.le
  have := norm_nonneg (c q)
  gcongr

/-- 16.14.ii: hornG2 G3 second order pde. -/
@[dlmf 16.14.ii]
theorem hornG2_G3_second_order_pde (a a' b b' : ℂ) (ha : ∀ k : ℤ,a≠k) (ha' : ∀ k : ℤ,a'≠k)
    (hb : ∀ k : ℤ,b≠k) (hb' : ∀ k : ℤ,b'≠k) {x y : ℂ}
    (hxy : ‖x‖+‖y‖<(1/4:ℝ)) :
    let f := hornG2 a a' b b'
    let g := hornG3 a a'
    appellThetaX (fun x y => b*f x y+appellThetaY f x y-appellThetaX f x y) x y=
      x*(a*b'*f x y+(a+b')*appellThetaX f x y-a*appellThetaY f x y+
        appellThetaX (appellThetaX f) x y-appellThetaX (appellThetaY f) x y) ∧
    appellThetaY (fun x y => b'*f x y+appellThetaX f x y-appellThetaY f x y) x y=
      y*(a'*b*f x y+(a'+b)*appellThetaY f x y-a'*appellThetaX f x y+
        appellThetaY (appellThetaY f) x y-appellThetaX (appellThetaY f) x y) ∧
    appellThetaX (fun x y => a*g x y+2*appellThetaY g x y-appellThetaX g x y) x y=
      x*((a'*(a'+1))*g x y+(4*a'+2)*appellThetaX g x y-(2*a'+1)*appellThetaY g x y+
        4*appellThetaX (appellThetaX g) x y-4*appellThetaX (appellThetaY g) x y+
        appellThetaY (appellThetaY g) x y) ∧
    appellThetaY (fun x y => a'*g x y+2*appellThetaX g x y-appellThetaY g x y) x y=
      y*(a*(a+1)*g x y+(4*a+2)*appellThetaY g x y-(2*a+1)*appellThetaX g x y+
        4*appellThetaY (appellThetaY g) x y-4*appellThetaX (appellThetaY g) x y+
        appellThetaX (appellThetaX g) x y) := by
  sorry

/-- 16.14.ii: hornG3 nonmaximal region. -/
@[dlmf 16.14.ii]
theorem hornG3_nonmaximal_region (a a' : ℂ) (ha : ∀ k : ℤ,a≠k) (ha' : ∀ k : ℤ,a'≠k) :
    ∃ x y : ℂ,(1/4:ℝ)≤‖x‖+‖y‖ ∧
      Summable (fun p : ℕ × ℕ => Gamma (a+2*p.2-p.1)*Gamma (a'+2*p.1-p.2)/
        (Gamma a*Gamma a'*(p.1 !*p.2 !))*x^p.1*y^p.2) := by
  sorry

/-- Germ agreement of two functions analytic at a point of `ℂ × ℂ` is locally constant.
Adapted from TauCeti's one-variable `eventually_eventuallyEq_iff_of_analyticAt`. -/
lemma ghaR4_eventually_eventuallyEq_iff {F G : ℂ × ℂ → ℂ} {z : ℂ × ℂ}
    (hF : AnalyticAt ℂ F z) (hG : AnalyticAt ℂ G z) :
    ∀ᶠ w in 𝓝 z, ((F =ᶠ[𝓝 w] G) ↔ (F =ᶠ[𝓝 z] G)) := by
  obtain ⟨r₁, hr₁, hF'⟩ := hF.exists_ball_analyticOnNhd
  obtain ⟨r₂, hr₂, hG'⟩ := hG.exists_ball_analyticOnNhd
  have hr : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  have hFr : AnalyticOnNhd ℂ F (Metric.ball z (min r₁ r₂)) :=
    hF'.mono (Metric.ball_subset_ball (min_le_left _ _))
  have hGr : AnalyticOnNhd ℂ G (Metric.ball z (min r₁ r₂)) :=
    hG'.mono (Metric.ball_subset_ball (min_le_right _ _))
  have hz : z ∈ Metric.ball z (min r₁ r₂) := Metric.mem_ball_self hr
  have key : ∀ {u v : ℂ × ℂ}, u ∈ Metric.ball z (min r₁ r₂) → v ∈ Metric.ball z (min r₁ r₂) →
      F =ᶠ[𝓝 u] G → F =ᶠ[𝓝 v] G := fun hu hv h =>
    eventually_of_mem (Metric.isOpen_ball.mem_nhds hv)
      (hFr.eqOn_of_preconnected_of_eventuallyEq hGr (convex_ball z _).isPreconnected hu h)
  filter_upwards [Metric.ball_mem_nhds z hr] with w hw
  exact ⟨fun h => key hw hz h, fun h => key hz hw h⟩

/-- 16.16: appell continuation unique. -/
@[dlmf 16.16]
theorem appell_continuation_unique {F G : ℝ→(ℂ × ℂ→ℂ)} {γ : ℝ→ℂ × ℂ}
    (hF : IsAppellContinuation F γ) (hG : IsAppellContinuation G γ)
    (h0 : F 0=ᶠ[𝓝 (γ 0)] G 0) : F 1=ᶠ[𝓝 (γ 1)] G 1 := by
  -- Adapted from TauCeti `IsAnalyticContinuationAlong.eventuallyEq`.
  have hloc : ∀ t ∈ Icc (0:ℝ) 1, ∀ᶠ u in 𝓝[Icc 0 1] t,
      ((F u =ᶠ[𝓝 (γ u)] G u) ↔ (F t =ᶠ[𝓝 (γ t)] G t)) := by
    intro t ht
    have hball := ghaR4_eventually_eventuallyEq_iff (hF.analyticAt t ht) (hG.analyticAt t ht)
    filter_upwards [(hF.continuousOn t ht).eventually hball, hF.locallyEq t ht,
      hG.locallyEq t ht] with u hiff hfu hgu
    exact ⟨fun h => hiff.mp (hfu.symm.trans (h.trans hgu)),
      fun h => hfu.trans ((hiff.mpr h).trans hgu.symm)⟩
  exact (isPreconnected_Icc.apply_eq_of_eventually_eq
    (f := fun t => F t =ᶠ[𝓝 (γ t)] G t)
    (fun _ ht => ((hloc _ ht).mono fun _ h => propext h))
    (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)) ▸ h0

end DLMF.Hypergeometric
end
