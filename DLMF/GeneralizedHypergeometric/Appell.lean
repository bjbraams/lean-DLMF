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
# Appell functions and Horn's double series (DLMF §§16.13–16.16)

Acquired 2026-10-24. The ordinary double series are totalized outside convergence and at
exceptional denominator parameters. Convergence, differentiation and integral representations
therefore state their exact domains. Euler integrals provide analytic branches beyond the
series domains. Transformation formulas are identities of germs at the origin, transported
along compatible analytic continuations; no divergent totalized series is silently identified
with a continued function. The infinity connection formula explicitly specifies continuation.

The existing `appF4` and Bailey product theorem are reused. One-variable continuation uses the
pinned TauCeti continuation API; the two-variable definition below is its direct domain extension.
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
  continuousOn : ContinuousOn γ (Icc 0 1)
  analyticAt : ∀ t∈Icc 0 1,AnalyticAt ℂ (F t) (γ t)
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

/-- The totalized double series; continuations are represented by analytic germs. -/
@[dlmf 16.13.E1]
def appF1 (a b b' c x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ,appF1Coeff a b b' c p.1 p.2*x^p.1*y^p.2

/-- The totalized double series; continuations are represented by analytic germs. -/
@[dlmf 16.13.E2]
def appF2 (a b b' c c' x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ,appF2Coeff a b b' c c' p.1 p.2*x^p.1*y^p.2

/-- The totalized double series; continuations are represented by analytic germs. -/
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

/-- Gamma bound for the Horn G3 pair. -/
lemma ghaR4_gamma_G3_bound {a a' : ℂ} (ha : ∀ k : ℤ, a ≠ k) (ha' : ∀ k : ℤ, a' ≠ k)
    {σ : ℝ} (hσ : 1 < σ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ m n : ℕ,
      ‖Gamma (a + 2 * n - m) * Gamma (a' + 2 * m - n)‖ ≤
        C * σ ^ (4 * (m + n)) * 4 ^ (m + n) * (m + n) ! := by
  obtain ⟨C1, hC1, h1⟩ := ghaR4_gamma_int_bound ha hσ
  obtain ⟨C2, hC2, h2⟩ := ghaR4_gamma_int_bound ha' hσ
  refine ⟨C1 * C2, by positivity, fun m n => ?_⟩
  have hσ0 : 0 ≤ σ := by linarith
  have hσ1 : ∀ i j : ℕ, i ≤ j → σ ^ i ≤ σ ^ j := fun i j h => pow_le_pow_right₀ hσ.le h
  have h4 : ∀ i j : ℕ, i ≤ j → (2 : ℝ) ^ i ≤ 2 ^ j := fun i j h => pow_le_pow_right₀ (by norm_num) h
  have h41 : (1 : ℝ) ≤ 4 ^ (m + n) := one_le_pow₀ (by norm_num)
  have hfN : (0 : ℝ) < (m + n) ! := by exact_mod_cast (m + n).factorial_pos
  rw [norm_mul]
  rcases le_or_gt m (2 * n) with hm | hm
  · rcases le_or_gt n (2 * m) with hn | hn
    · -- both arguments are a shift by a natural number
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
      obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le hn
      have e1 : a + 2 * (n : ℂ) - m = a + k := by
        have : (2 * n : ℕ) = m + k := hk; rw [show (2 : ℂ) * n = ((2 * n : ℕ) : ℂ) by push_cast; ring, this]; push_cast; ring
      have e2 : a' + 2 * (m : ℂ) - n = a' + l := by
        have : (2 * m : ℕ) = n + l := hl; rw [show (2 : ℂ) * m = ((2 * m : ℕ) : ℂ) by push_cast; ring, this]; push_cast; ring
      have hkl : k + l = m + n := by omega
      rw [e1, e2]
      have hf : ((k ! : ℕ) : ℝ) * l ! ≤ (m + n) ! := by
        rw [← hkl]; exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _)
          (Nat.factorial_mul_factorial_dvd_factorial_add k l)
      calc ‖Gamma (a + k)‖ * ‖Gamma (a' + l)‖ ≤ (C1 * σ ^ k * k !) * (C2 * σ ^ l * l !) :=
            mul_le_mul (h1 k).1 (h2 l).1 (norm_nonneg _) (by positivity)
        _ = C1 * C2 * σ ^ (k + l) * (k ! * l !) := by rw [pow_add]; ring
        _ ≤ C1 * C2 * σ ^ (4 * (m + n)) * (m + n) ! := by
            have hs := hσ1 (k + l) (4 * (m + n)) (by omega)
            have h0 : 0 ≤ C1 * C2 := by positivity
            exact mul_le_mul (mul_le_mul_of_nonneg_left hs h0) hf (by positivity) (by positivity)
        _ ≤ _ := by
            have : 0 ≤ C1 * C2 * σ ^ (4 * (m + n)) * (m + n) ! := by positivity
            nlinarith
    · -- `2m < n`: the first argument is a forward shift, the second a backward one
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt hn
      -- n = 2m + j + 1; first argument a + (2n - m), second a' - (j+1)
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
      have e1 : a + 2 * (n : ℂ) - m = a + k := by
        have : (2 * n : ℕ) = m + k := hk; rw [show (2 : ℂ) * n = ((2 * n : ℕ) : ℂ) by push_cast; ring, this]; push_cast; ring
      have e2 : a' + 2 * (m : ℂ) - n = a' - ((j + 1 : ℕ) : ℂ) := by
        rw [hj]; push_cast; ring
      rw [e1, e2]
      have hkN : k = (j + 1) + (m + n) := by omega
      have hf : ((k ! : ℕ) : ℝ) ≤ 2 ^ k * ((j + 1) ! * (m + n) !) := by
        rw [hkN]; exact ghaR4_choose_fact
      have hj0 : (0 : ℝ) < (j + 1) ! := by exact_mod_cast (j + 1).factorial_pos
      have hb2 := (h2 (j + 1)).2
      have hb2' : ‖Gamma (a' - ((j + 1 : ℕ) : ℂ))‖ ≤ C2 * σ ^ (j + 1) / (j + 1) ! := by
        rw [le_div_iff₀ hj0]; exact hb2
      calc ‖Gamma (a + k)‖ * ‖Gamma (a' - ((j + 1 : ℕ) : ℂ))‖
          ≤ (C1 * σ ^ k * k !) * (C2 * σ ^ (j + 1) / (j + 1) !) :=
            mul_le_mul (h1 k).1 hb2' (norm_nonneg _) (by positivity)
        _ ≤ (C1 * σ ^ k * (2 ^ k * ((j + 1) ! * (m + n) !))) * (C2 * σ ^ (j + 1) / (j + 1) !) := by
            gcongr
        _ = C1 * C2 * σ ^ (k + (j + 1)) * 2 ^ k * (m + n) ! := by
            rw [pow_add]; field_simp; ring
        _ ≤ C1 * C2 * σ ^ (4 * (m + n)) * 2 ^ (2 * (m + n)) * (m + n) ! := by
            have hs := hσ1 (k + (j + 1)) (4 * (m + n)) (by omega)
            have h2' := h4 k (2 * (m + n)) (by omega)
            have h0 : 0 ≤ C1 * C2 := by positivity
            have := mul_le_mul (mul_le_mul_of_nonneg_left hs h0) h2' (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_right this (by positivity)
        _ = _ := by rw [show (2:ℝ) ^ (2 * (m + n)) = 4 ^ (m + n) by rw [pow_mul]; norm_num]
  · -- `2n < m`
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt hm
    have hn : n ≤ 2 * m := by omega
    obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le hn
    have e1 : a + 2 * (n : ℂ) - m = a - ((j + 1 : ℕ) : ℂ) := by
      rw [hj]; push_cast; ring
    have e2 : a' + 2 * (m : ℂ) - n = a' + l := by
      have : (2 * m : ℕ) = n + l := hl; rw [show (2 : ℂ) * m = ((2 * m : ℕ) : ℂ) by push_cast; ring, this]; push_cast; ring
    rw [e1, e2]
    have hlN : l = (j + 1) + (m + n) := by omega
    have hf : ((l ! : ℕ) : ℝ) ≤ 2 ^ l * ((j + 1) ! * (m + n) !) := by
      rw [hlN]; exact ghaR4_choose_fact
    have hj0 : (0 : ℝ) < (j + 1) ! := by exact_mod_cast (j + 1).factorial_pos
    have hb1' : ‖Gamma (a - ((j + 1 : ℕ) : ℂ))‖ ≤ C1 * σ ^ (j + 1) / (j + 1) ! := by
      rw [le_div_iff₀ hj0]; exact (h1 (j + 1)).2
    calc ‖Gamma (a - ((j + 1 : ℕ) : ℂ))‖ * ‖Gamma (a' + l)‖
        ≤ (C1 * σ ^ (j + 1) / (j + 1) !) * (C2 * σ ^ l * l !) :=
          mul_le_mul hb1' (h2 l).1 (norm_nonneg _) (by positivity)
      _ ≤ (C1 * σ ^ (j + 1) / (j + 1) !) * (C2 * σ ^ l * (2 ^ l * ((j + 1) ! * (m + n) !))) := by
          gcongr
      _ = C1 * C2 * σ ^ (l + (j + 1)) * 2 ^ l * (m + n) ! := by
          rw [pow_add]; field_simp; ring
      _ ≤ C1 * C2 * σ ^ (4 * (m + n)) * 2 ^ (2 * (m + n)) * (m + n) ! := by
          have hs := hσ1 (l + (j + 1)) (4 * (m + n)) (by omega)
          have h2' := h4 l (2 * (m + n)) (by omega)
          have h0 : 0 ≤ C1 * C2 := by positivity
          have := mul_le_mul (mul_le_mul_of_nonneg_left hs h0) h2' (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by rw [show (2:ℝ) ^ (2 * (m + n)) = 4 ^ (m + n) by rw [pow_mul]; norm_num]

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


/-! ## Euler integral branches with actual integrability -/

/-- Natural principal cut plane for the two separate Euler denominator factors. -/
def appellEulerDomain : Set (ℂ × ℂ) := {p | 1-p.1∈slitPlane ∧ 1-p.2∈slitPlane}

/-- The square-integral denominator stays on its principal branch at every integration point. -/
def appellSquareSlit (p : ℂ × ℂ) : Prop :=
  ∀ u∈Icc (0:ℝ) 1,∀ v∈Icc (0:ℝ) 1,1-(u:ℂ)*p.1-(v:ℂ)*p.2∈slitPlane

/-- Euler's integration triangle, including its measure-zero boundary. -/
def appellTriangle : Set (ℝ × ℝ) := {p | 0≤p.1 ∧ 0≤p.2 ∧ p.1+p.2≤1}

/-- The Euler kernel for F1, with all powers principal on their stated domain. -/
def appF1EulerKernel (a b b' c x y : ℂ) (u : ℝ) : ℂ :=
  (u:ℂ)^(a-1)*((1-u:ℝ):ℂ)^(c-a-1)/(1-u*x)^b/(1-u*y)^b'

/-- The Euler kernel for F2. -/
def appF2EulerKernel (a b b' c c' x y : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1:ℂ)^(b-1)*(p.2:ℂ)^(b'-1)*((1-p.1:ℝ):ℂ)^(c-b-1)*
    ((1-p.2:ℝ):ℂ)^(c'-b'-1)/(1-p.1*x-p.2*y)^a

/-- The simplex Euler kernel for F3. -/
def appF3EulerKernel (a a' b b' c x y : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1:ℂ)^(b-1)*(p.2:ℂ)^(b'-1)*((1-p.1-p.2:ℝ):ℂ)^(c-b-b'-1)/
    (1-p.1*x)^a/(1-p.2*y)^a'

/-- The transformed Euler kernel for F4. -/
def appF4EulerKernel (a b c c' x y : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1:ℂ)^(a-1)*(p.2:ℂ)^(b-1)*((1-p.1:ℝ):ℂ)^(c-a-1)*
    ((1-p.2:ℝ):ℂ)^(c'-b-1)/(1-p.1*x)^(c+c'-a-1)/(1-p.2*y)^(c+c'-b-1)/
    (1-p.1*x-p.2*y)^(a+b-c-c'+1)

/-- The Euler integral branch of F1, distinct from its totalized double series. -/
@[dlmf 16.15.E1]
def appF1Euler (a b b' c x y : ℂ) : ℂ :=
  Gamma c/(Gamma a*Gamma (c-a))*∫ u in (0:ℝ)..1,appF1EulerKernel a b b' c x y u

/-- The Euler square-integral branch of F2. -/
@[dlmf 16.15.E2]
def appF2Euler (a b b' c c' x y : ℂ) : ℂ :=
  Gamma c*Gamma c'/(Gamma b*Gamma b'*Gamma (c-b)*Gamma (c'-b'))*
    ∫ p in Icc (0:ℝ) 1×ˢIcc (0:ℝ) 1,appF2EulerKernel a b b' c c' x y p

/-- The Euler simplex-integral branch of F3. -/
@[dlmf 16.15.E3]
def appF3Euler (a a' b b' c x y : ℂ) : ℂ :=
  Gamma c/(Gamma b*Gamma b'*Gamma (c-b-b'))*
    ∫ p in appellTriangle,appF3EulerKernel a a' b b' c x y p

/-- The Euler branch at the transformed arguments x(1-y),y(1-x). -/
@[dlmf 16.15.E4]
def appF4Euler (a b c c' x y : ℂ) : ℂ :=
  Gamma c*Gamma c'/(Gamma a*Gamma b*Gamma (c-a)*Gamma (c'-b))*
    ∫ p in Icc (0:ℝ) 1×ˢIcc (0:ℝ) 1,appF4EulerKernel a b c c' x y p

/-- The segment from `1` to `1 - w` stays in the slit plane. -/
lemma ghaR4_slit_segment {w : ℂ} (hw : 1 - w ∈ slitPlane) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    1 - (u:ℂ) * w ∈ slitPlane := by
  have := starConvex_one_slitPlane.add_smul_mem (y := -w) (by simpa [sub_eq_add_neg] using hw)
    hu.1 hu.2
  convert this using 1
  simp [Complex.real_smul]
  ring

/-- A reciprocal principal power of a slit-valued continuous function is bounded on a compact set. -/
lemma ghaR4_inv_cpow_bound {α : Type*} [TopologicalSpace α] {f : α → ℂ} {s : Set α}
    (hs : IsCompact s) (hf : ContinuousOn f s)
    (hslit : ∀ u ∈ s, f u ∈ slitPlane) (b : ℂ) :
    ∃ M : ℝ, ∀ u ∈ s, ‖(f u ^ b)⁻¹‖ ≤ M := by
  have hc : ContinuousOn (fun u => (f u ^ b)⁻¹) s := by
    refine ContinuousOn.inv₀ (hf.cpow_const hslit) fun u hu => ?_
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => slitPlane_ne_zero (hslit u hu) h.1
  exact hs.exists_bound_of_continuousOn hc

/-- The Euler beta kernel is integrable on `[0,1]`. -/
lemma ghaR4_beta_integrableOn {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^(u-1) * (1 - (t:ℂ))^(v-1)) (Icc 0 1) := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc,
    ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact Complex.betaIntegral_convergent hu hv

/-- The product of two beta kernels is integrable on the unit square. -/
lemma ghaR4_beta_prod_integrableOn {u v u' v' : ℂ} (hu : 0 < u.re) (hv : 0 < v.re)
    (hu' : 0 < u'.re) (hv' : 0 < v'.re) :
    IntegrableOn (fun p : ℝ × ℝ => ‖(p.1:ℂ)^(u-1) * (1 - (p.1:ℂ))^(v-1)‖ *
      ‖(p.2:ℂ)^(u'-1) * (1 - (p.2:ℂ))^(v'-1)‖) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact (ghaR4_beta_integrableOn hu hv).norm.mul_prod (ghaR4_beta_integrableOn hu' hv').norm

/-- The set where `1 - x` lies in the slit plane is open. -/
lemma ghaR4_isOpen_slitPre : IsOpen {x : ℂ | 1 - x ∈ slitPlane} :=
  isOpen_slitPlane.preimage (by fun_prop)

/-- A closed ball on which `1 - x` stays in the slit plane. -/
lemma ghaR4_exists_closedBall_slit {x₀ : ℂ} (hx : 1 - x₀ ∈ slitPlane) :
    ∃ r > 0, Metric.closedBall x₀ r ⊆ {x : ℂ | 1 - x ∈ slitPlane} := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp ghaR4_isOpen_slitPre x₀ hx
  exact ⟨r / 2, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans hsub⟩

/-- Uniform bound for `(1 - u x)^(-b)` over `u ∈ [0,1]` and `x` in a slit-admissible closed ball. -/
lemma ghaR4_inv_cpow_bound_param {x₀ : ℂ} {r : ℝ}
    (hr : Metric.closedBall x₀ r ⊆ {x : ℂ | 1 - x ∈ slitPlane}) (b : ℂ) :
    ∃ M : ℝ, ∀ u ∈ Icc (0:ℝ) 1, ∀ x ∈ Metric.closedBall x₀ r, ‖((1 - (u:ℂ) * x) ^ b)⁻¹‖ ≤ M := by
  obtain ⟨M, hM⟩ := ghaR4_inv_cpow_bound (f := fun q : ℝ × ℂ => 1 - (q.1:ℂ) * q.2)
    (isCompact_Icc.prod (isCompact_closedBall x₀ r)) (by fun_prop)
    (fun q hq => ghaR4_slit_segment (hr hq.2) hq.1) b
  exact ⟨M, fun u hu x hx => hM (u, x) ⟨hu, hx⟩⟩

/-- Differentiability of `x ↦ (1 - u x)^(-b)` on the Euler domain. -/
lemma ghaR4_differentiableAt_inv_cpow {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) {x : ℂ}
    (hx : 1 - x ∈ slitPlane) (b : ℂ) :
    DifferentiableAt ℂ (fun x : ℂ => ((1 - (u:ℂ) * x) ^ b)⁻¹) x := by
  have hs := ghaR4_slit_segment hx hu
  refine (((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)).cpow
    (differentiableAt_const b) hs).inv ?_
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => slitPlane_ne_zero hs h.1

/-- The square-slit condition is open. -/
lemma ghaR4_square_eventually {p₀ : ℂ × ℂ} (h : appellSquareSlit p₀) :
    ∀ᶠ p in 𝓝 p₀, appellSquareSlit p := by
  have hK : IsCompact (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have := hK.eventually_forall_of_forall_eventually (x₀ := p₀)
    (P := fun p q => 1 - (q.1:ℂ) * p.1 - (q.2:ℂ) * p.2 ∈ slitPlane) (fun q hq => by
      have hc : Continuous fun z : (ℂ × ℂ) × (ℝ × ℝ) => 1 - (z.2.1:ℂ) * z.1.1 - (z.2.2:ℂ) * z.1.2 := by
        fun_prop
      exact hc.continuousAt.preimage_mem_nhds (isOpen_slitPlane.mem_nhds (h q.1 hq.1 q.2 hq.2)))
  filter_upwards [this] with p hp u hu v hv
  exact hp (u, v) ⟨hu, hv⟩

/-- The F2/F4 Euler domain is open. -/
lemma ghaR4_isOpen_square : IsOpen {p : ℂ × ℂ | appellSquareSlit p} :=
  isOpen_iff_mem_nhds.mpr fun _ hp => ghaR4_square_eventually hp

/-- A closed ball inside the F2/F4 Euler domain. -/
lemma ghaR4_exists_closedBall_square {p₀ : ℂ × ℂ} (h : appellSquareSlit p₀) :
    ∃ r > 0, ∀ p ∈ Metric.closedBall p₀ r, appellSquareSlit p := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp ghaR4_isOpen_square p₀ h
  exact ⟨r / 2, by positivity, fun p hp => hsub (Metric.closedBall_subset_ball (by linarith) hp)⟩

/-- A uniform bound for a reciprocal power along the square, for parameters near a point. -/
lemma ghaR4_square_inv_cpow_bound {p₀ : ℂ × ℂ} {r : ℝ}
    {f : (ℂ × ℂ) × (ℝ × ℝ) → ℂ} (hf : Continuous f)
    (hs : ∀ p ∈ Metric.closedBall p₀ r, ∀ q ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, f (p, q) ∈ slitPlane)
    (b : ℂ) :
    ∃ M : ℝ, ∀ p ∈ Metric.closedBall p₀ r, ∀ q ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1,
      ‖(f (p, q) ^ b)⁻¹‖ ≤ M := by
  obtain ⟨M, hM⟩ := ghaR4_inv_cpow_bound (f := f)
    ((isCompact_closedBall p₀ r).prod (isCompact_Icc.prod isCompact_Icc)) hf.continuousOn
    (fun z hz => hs z.1 hz.1 z.2 hz.2) b
  exact ⟨M, fun p hp q hq => hM (p, q) ⟨hp, hq⟩⟩

/-- Differentiability of the square-integral denominator power. -/
lemma ghaR4_differentiableAt_inv_cpow_square {p : ℂ × ℂ} {u v : ℝ}
    (hs : 1 - (u:ℂ) * p.1 - (v:ℂ) * p.2 ∈ slitPlane) (b : ℂ) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ => ((1 - (u:ℂ) * p.1 - (v:ℂ) * p.2) ^ b)⁻¹) p := by
  have hf : DifferentiableAt ℂ (fun p : ℂ × ℂ => 1 - (u:ℂ) * p.1 - (v:ℂ) * p.2) p := by fun_prop
  refine (hf.cpow (differentiableAt_const b) hs).inv ?_
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => slitPlane_ne_zero hs h.1

/-- Termwise integration of a series with a bounded integrable weight. -/
lemma ghaR4_hasSum_integral {α ι : Type*} [MeasurableSpace α] [Countable ι] {μ : Measure α}
    {w : α → ℂ} (hw : Integrable w μ) {d : ι → ℂ} (hd : Summable fun i => ‖d i‖)
    {e : ι → α → ℂ} (he : ∀ i, AEStronglyMeasurable (e i) μ) (hbd : ∀ i, ∀ᵐ t ∂μ, ‖e i t‖ ≤ 1)
    {g : α → ℂ} (hg : ∀ᵐ t ∂μ, HasSum (fun i => d i * e i t) (g t)) :
    HasSum (fun i => d i * ∫ t, w t * e i t ∂μ) (∫ t, w t * g t ∂μ) := by
  have h := hasSum_integral_of_dominated_convergence (μ := μ)
    (F := fun i t => w t * (d i * e i t)) (f := fun t => w t * g t)
    (fun i t => ‖d i‖ * ‖w t‖)
    (fun i => hw.aestronglyMeasurable.mul (aestronglyMeasurable_const.mul (he i)))
    (fun i => by
      filter_upwards [hbd i] with t ht
      rw [norm_mul, norm_mul]
      calc ‖w t‖ * (‖d i‖ * ‖e i t‖) ≤ ‖w t‖ * (‖d i‖ * 1) := by gcongr
        _ = _ := by ring)
    (Eventually.of_forall fun t => hd.mul_right _)
    (by simp_rw [tsum_mul_right]; exact hw.norm.const_mul _)
    (by filter_upwards [hg] with t ht using ht.mul_left (w t))
  refine h.congr_fun fun i => ?_
  rw [← integral_const_mul]
  congr 1; funext t; ring

/-- Absolute convergence of the binomial series `∑ (b)ₘ xᵐ/m!` in the unit disk. -/
lemma ghaR4_summable_norm_binom (b : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable fun m : ℕ => ‖poch b m / m ! * x ^ m‖ := by
  set σ := 2 / (1 + ‖x‖) with hσ
  have hx0 := norm_nonneg x
  have hσ1 : 1 < σ := by rw [hσ, lt_div_iff₀ (by linarith)]; linarith
  have hσx : σ * ‖x‖ < 1 := by
    rw [hσ, div_mul_eq_mul_div, div_lt_one (by linarith)]; linarith
  obtain ⟨C, hC0, hC⟩ := ghaR4_norm_poch_le_factorial b hσ1
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    ((summable_geometric_of_lt_one (by positivity) hσx).mul_left C)
  have hf : (0 : ℝ) < m ! := by exact_mod_cast m.factorial_pos
  rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow, div_mul_eq_mul_div,
    div_le_iff₀ hf, mul_pow]
  calc ‖poch b m‖ * ‖x‖ ^ m ≤ (C * σ ^ m * m !) * ‖x‖ ^ m := by gcongr; exact hC m
    _ = _ := by ring

/-- Binomially weighted bound for the two-variable binomial coefficients. -/
lemma ghaR4_binom2_coeff_bound (a : ℂ) {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, ∀ q : ℕ × ℕ, ‖poch a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ)‖ ≤
      C * σ ^ (q.1 + q.2) * ((q.1 + q.2).choose q.1 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := ghaR4_norm_poch_le_factorial a hσ
  refine ⟨C, fun ⟨m, n⟩ => ?_⟩
  have hm : (0 : ℝ) < m ! := by exact_mod_cast m.factorial_pos
  have hn : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  have hfac : ((m + n) ! : ℝ) = ((m + n).choose m : ℝ) * m ! * n ! := by
    have := Nat.add_choose_mul_factorial_mul_factorial m n
    rw [← Nat.choose_symm_add] at this
    exact_mod_cast this.symm
  simp only
  rw [norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast, div_le_iff₀ (by positivity)]
  calc ‖poch a (m + n)‖ ≤ C * σ ^ (m + n) * (m + n) ! := hC _
    _ = _ := by rw [hfac]; ring

/-- The two-variable binomial series `(1-s-t)^(-a) = ∑ (a)ₘ₊ₙ sᵐ tⁿ/(m! n!)`. -/
lemma ghaR4_hasSum_binom2 (a : ℂ) {s t : ℂ} (hst : ‖s‖ + ‖t‖ < 1) :
    HasSum (fun q : ℕ × ℕ => poch a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ) * s ^ q.1 * t ^ q.2)
      ((1 - s - t) ^ (-a)) ∧
    Summable (fun q : ℕ × ℕ => ‖poch a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ) * s ^ q.1 * t ^ q.2‖) := by
  set f := fun q : ℕ × ℕ => poch a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ) * s ^ q.1 * t ^ q.2 with hf
  have hnorm : Summable fun q => ‖f q‖ := by
    obtain ⟨A, B, hA, hB, hS⟩ := ghaR4_dom_diamond
      (fun q : ℕ × ℕ => poch a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ))
      (fun _ hσ => ghaR4_binom2_coeff_bound a hσ) hst
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_) hS
    simp only [hf, norm_mul, norm_pow]
    have := norm_nonneg (poch a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ))
    have hA0 : 0 ≤ A := (norm_nonneg _).trans hA.le
    gcongr
  refine ⟨?_, hnorm⟩
  have hT := (Summable.of_norm hnorm).hasSum
  have hT' : HasSum (f ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) (∑' q, f q) :=
    (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff).mpr hT
  have hfib : ∀ N : ℕ, HasSum (fun c : Finset.antidiagonal N =>
      (f ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) ⟨N, c⟩) (poch a N / N ! * (s + t) ^ N) := by
    intro N
    convert hasSum_fintype (fun c : Finset.antidiagonal N =>
      (f ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) ⟨N, c⟩) using 1
    rw [(Commute.all s t).add_pow', Finset.mul_sum, ← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun c _ => ?_
    obtain ⟨⟨m, n⟩, hc⟩ := c
    have hmn : m + n = N := Finset.mem_antidiagonal.mp hc
    subst hmn
    simp only [Function.comp, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply, hf, nsmul_eq_mul]
    have hm : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hfac : (((m + n) ! : ℕ) : ℂ) = ((m + n).choose m : ℂ) * m ! * n ! := by
      have := Nat.add_choose_mul_factorial_mul_factorial m n
      rw [← Nat.choose_symm_add] at this
      exact_mod_cast this.symm
    have hC : ((m + n).choose m : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
    rw [hfac]
    field_simp
  have hG := hT'.sigma hfib
  have hst' : ‖s + t‖ < 1 := (norm_add_le s t).trans_lt hst
  have h1 := hasSum_poch_div_factorial (β := a) hst'
  rw [show 1 - s - t = 1 - (s + t) by ring, h1.unique hG]
  exact hT

/-- Beta-integral moments on `[0,1]`. -/
lemma ghaR4_beta_moment {b γ : ℂ} (m : ℕ) :
    (∫ u in Icc (0:ℝ) 1, (u:ℂ) ^ (b - 1) * ((1 - u : ℝ) : ℂ) ^ (γ - 1) * (u:ℂ) ^ m) =
      betaIntegral (b + m) γ := by
  rw [integral_Icc_eq_integral_Ioc, betaIntegral, intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  have hu0 : (u:ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.1.ne'
  rw [show b + (m : ℂ) - 1 = (b - 1) + (m : ℂ) by ring, cpow_add _ _ hu0, cpow_natCast]
  push_cast
  ring

/-- The normalized beta moment `Γ(c)B(b+m,c-b)/(Γ(b)Γ(c-b)) = (b)ₘ/(c)ₘ`. -/
lemma ghaR4_gamma_beta {b c : ℂ} (hb : 0 < b.re) (hcb : 0 < (c - b).re) (m : ℕ) :
    Gamma c / (Gamma b * Gamma (c - b)) * betaIntegral (b + m) (c - b) = poch b m / poch c m := by
  have hE := euler_term_eq_gaussHGCoeff (a := 1) (b := b) (c := c) m hb hcb
  have hf : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hc : ∀ k : ℕ, c ≠ -k := not_neg_nat_of_re_pos (re_c_pos_of hb hcb)
  rw [poch_nat_one, div_self hf, one_mul] at hE
  rw [hE, gaussHGCoeff, poch_nat_one]
  have hpc := poch_ne_zero_of_not_neg_nat hc m
  field_simp

/-- 16.15.E1: appF1 euler integrable. -/
@[dlmf 16.15.E1]
theorem appF1_euler_integrable (a b b' c : ℂ) (ha : 0<a.re) (hca : 0<(c-a).re) {x y : ℂ} (hxy : (x,y)∈appellEulerDomain) :
    IntegrableOn (appF1EulerKernel a b b' c x y) (Icc (0:ℝ) 1) := by
  obtain ⟨M1, hM1⟩ := ghaR4_inv_cpow_bound (f := fun u : ℝ => 1 - (u:ℂ) * x) isCompact_Icc
    (by fun_prop) (fun u hu => ghaR4_slit_segment hxy.1 hu) b
  obtain ⟨M2, hM2⟩ := ghaR4_inv_cpow_bound (f := fun u : ℝ => 1 - (u:ℂ) * y) isCompact_Icc
    (by fun_prop) (fun u hu => ghaR4_slit_segment hxy.2 hu) b'
  have hβ : IntegrableOn (fun u : ℝ => (u:ℂ)^(a-1) * (1 - (u:ℂ))^(c-a-1)) (Icc 0 1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc,
      ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    simpa using Complex.betaIntegral_convergent ha hca
  refine (hβ.norm.mul_const (M1 * M2)).mono' ?_ ?_
  · exact (by unfold appF1EulerKernel; fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have h1 := hM1 u hu
    have h2 := hM2 u hu
    have hM1' := (norm_nonneg _).trans h1
    simp only [appF1EulerKernel, div_eq_mul_inv, norm_mul, Complex.ofReal_sub, Complex.ofReal_one]
    calc ‖(u:ℂ) ^ (a - 1)‖ * ‖(1 - (u:ℂ)) ^ (c - a - 1)‖ * ‖((1 - (u:ℂ) * x) ^ b)⁻¹‖ *
          ‖((1 - (u:ℂ) * y) ^ b')⁻¹‖
        ≤ ‖(u:ℂ) ^ (a - 1)‖ * ‖(1 - (u:ℂ)) ^ (c - a - 1)‖ * M1 * M2 := by gcongr
      _ = _ := by ring

/-- 16.15.E1: appF1 euler analytic. -/
@[dlmf 16.15.E1]
theorem appF1_euler_analytic (a b b' c : ℂ) (ha : 0<a.re) (hca : 0<(c-a).re) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF1Euler a b b' c p.1 p.2) appellEulerDomain := by
  have hU : IsOpen appellEulerDomain :=
    (ghaR4_isOpen_slitPre.preimage continuous_fst).inter
      (ghaR4_isOpen_slitPre.preimage continuous_snd)
  have hβ : IntegrableOn (fun u : ℝ => (u:ℂ)^(a-1) * (1 - (u:ℂ))^(c-a-1)) (Icc 0 1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc,
      ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    simpa using Complex.betaIntegral_convergent ha hca
  have hΙ : Ι (0:ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  have hd : DifferentiableOn ℂ
      (fun p : ℂ × ℂ => ∫ u in (0:ℝ)..1, appF1EulerKernel a b b' c p.1 p.2 u) appellEulerDomain := by
    refine differentiableOn_intervalIntegral_of_locally_dominated hU 0 1
      (fun p _ => (by unfold appF1EulerKernel; fun_prop : Measurable _).aestronglyMeasurable)
      ?_ ?_
    · rw [hΙ]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hu' : u ∈ Icc (0:ℝ) 1 := Ioc_subset_Icc_self hu
      intro p hp
      have h1 := ghaR4_differentiableAt_inv_cpow hu' hp.1 b
      have h2 := ghaR4_differentiableAt_inv_cpow hu' hp.2 b'
      have e : (fun q : ℂ × ℂ => appF1EulerKernel a b b' c q.1 q.2 u) = fun q =>
          (u:ℂ) ^ (a - 1) * ((1 - u:ℝ):ℂ) ^ (c - a - 1) * ((1 - (u:ℂ) * q.1) ^ b)⁻¹ *
            ((1 - (u:ℂ) * q.2) ^ b')⁻¹ := by
        funext q; simp only [appF1EulerKernel, div_eq_mul_inv]
      rw [e]
      exact (((differentiableAt_const _).mul (h1.comp p differentiableAt_fst)).mul
        (h2.comp p differentiableAt_snd)).differentiableWithinAt
    · intro p hp
      obtain ⟨r1, hr1, hs1⟩ := ghaR4_exists_closedBall_slit hp.1
      obtain ⟨r2, hr2, hs2⟩ := ghaR4_exists_closedBall_slit hp.2
      obtain ⟨M1, hM1⟩ := ghaR4_inv_cpow_bound_param hs1 b
      obtain ⟨M2, hM2⟩ := ghaR4_inv_cpow_bound_param hs2 b'
      refine ⟨Metric.ball p.1 r1 ×ˢ Metric.ball p.2 r2,
        prod_mem_nhds (Metric.ball_mem_nhds _ hr1) (Metric.ball_mem_nhds _ hr2),
        fun u => ‖(u:ℂ)^(a-1) * (1 - (u:ℂ))^(c-a-1)‖ * (M1 * M2), ?_, ?_⟩
      · rw [hΙ]
        exact (hβ.mono_set Ioc_subset_Icc_self).norm.mul_const _
      · rw [hΙ]
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        have hu' : u ∈ Icc (0:ℝ) 1 := Ioc_subset_Icc_self hu
        intro q hq
        have h1 := hM1 u hu' q.1 (Metric.ball_subset_closedBall hq.1)
        have h2 := hM2 u hu' q.2 (Metric.ball_subset_closedBall hq.2)
        have hM1' := (norm_nonneg _).trans h1
        simp only [appF1EulerKernel, div_eq_mul_inv, norm_mul, Complex.ofReal_sub,
          Complex.ofReal_one]
        calc ‖(u:ℂ) ^ (a - 1)‖ * ‖(1 - (u:ℂ)) ^ (c - a - 1)‖ * ‖((1 - (u:ℂ) * q.1) ^ b)⁻¹‖ *
              ‖((1 - (u:ℂ) * q.2) ^ b')⁻¹‖
            ≤ ‖(u:ℂ) ^ (a - 1)‖ * ‖(1 - (u:ℂ)) ^ (c - a - 1)‖ * M1 * M2 := by gcongr
          _ = _ := by ring
  have : DifferentiableOn ℂ (fun p : ℂ × ℂ => appF1Euler a b b' c p.1 p.2) appellEulerDomain :=
    (differentiableOn_const _).mul hd
  exact this.analyticOnNhd_of_finiteDimensional hU

/-- 16.15.E1: appF1 euler germ. -/
@[dlmf 16.15.E1]
theorem appF1_euler_germ (a b b' c : ℂ) (ha : 0<a.re) (hca : 0<(c-a).re) :
    (fun p : ℂ × ℂ => appF1 a b b' c p.1 p.2)=ᶠ[𝓝 (0,0)] (fun p => appF1Euler a b b' c p.1 p.2) := by
  have hcre := re_c_pos_of ha hca
  have hc : AppellRegular c := not_neg_nat_of_re_pos hcre
  have hU : {p : ℂ × ℂ | ‖p.1‖ < 1 ∧ ‖p.2‖ < 1} ∈ 𝓝 ((0:ℂ), (0:ℂ)) :=
    ((isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)).mem_nhds (by simp)
  filter_upwards [hU] with p hp
  obtain ⟨x, y⟩ := p
  obtain ⟨hx, hy⟩ := hp
  simp only at hx hy ⊢
  set w : ℝ → ℂ := fun u => (u:ℂ) ^ (a - 1) * ((1 - u : ℝ) : ℂ) ^ (c - a - 1) with hwdef
  set d : ℕ × ℕ → ℂ := fun q => poch b q.1 / q.1 ! * x ^ q.1 * (poch b' q.2 / q.2 ! * y ^ q.2)
    with hddef
  have hw : Integrable w (volume.restrict (Ioc (0:ℝ) 1)) := by
    have := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (Complex.betaIntegral_convergent ha hca)
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp [hwdef]
  have hd : Summable fun q => ‖d q‖ := by
    have := (ghaR4_summable_norm_binom b hx).mul_of_nonneg (ghaR4_summable_norm_binom b' hy)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    refine this.congr fun q => ?_
    simp only [hddef, norm_mul]
  have key := ghaR4_hasSum_integral (μ := volume.restrict (Ioc (0:ℝ) 1)) hw hd
    (e := fun q u => (u:ℂ) ^ (q.1 + q.2)) (fun q => by fun_prop)
    (fun q => by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1]
      exact pow_le_one₀ hu.1.le hu.2)
    (g := fun u => ((1 - (u:ℂ) * x) ^ b)⁻¹ * ((1 - (u:ℂ) * y) ^ b')⁻¹)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hu' : u ∈ Icc (0:ℝ) 1 := Ioc_subset_Icc_self hu
      have h1 := hasSum_one_sub_mul_cpow (a := b) hu' hx
      have h2 := hasSum_one_sub_mul_cpow (a := b') hu' hy
      have hs : Summable fun q : ℕ × ℕ => (poch b q.1 / q.1 ! * (x * u) ^ q.1) *
          (poch b' q.2 / q.2 ! * (y * u) ^ q.2) := by
        refine Summable.of_norm ?_
        have hux : ‖x * u‖ < 1 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1]
          nlinarith [norm_nonneg x, hu.2]
        have huy : ‖y * u‖ < 1 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1]
          nlinarith [norm_nonneg y, hu.2]
        have := (ghaR4_summable_norm_binom b hux).mul_of_nonneg (ghaR4_summable_norm_binom b' huy)
          (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
        exact this.congr fun q => by simp only [norm_mul]
      have := h1.mul h2 hs
      rw [cpow_neg, cpow_neg, mul_comm x, mul_comm y] at this
      refine this.congr_fun fun q => ?_
      simp only [hddef]
      rw [pow_add, mul_pow, mul_pow]
      ring)
  have hsum := hasSum_appF1 a b b' c hc (x := x) (y := y) ⟨hx, hy⟩
  refine hsum.unique ?_
  unfold appF1Euler
  rw [intervalIntegral.integral_of_le zero_le_one]
  have e1 : (∫ u in Ioc (0:ℝ) 1, appF1EulerKernel a b b' c x y u) =
      ∫ u in Ioc (0:ℝ) 1, w u * (((1 - (u:ℂ) * x) ^ b)⁻¹ * ((1 - (u:ℂ) * y) ^ b')⁻¹) := by
    congr 1; funext u; simp only [appF1EulerKernel, hwdef, div_eq_mul_inv]; ring
  rw [e1]
  refine (key.mul_left (Gamma c / (Gamma a * Gamma (c - a)))).congr_fun fun q => ?_
  obtain ⟨m, n⟩ := q
  simp only
  have hbeta : (∫ u in Ioc (0:ℝ) 1, w u * (u:ℂ) ^ (m + n)) = betaIntegral (a + (m + n : ℕ)) (c - a) := by
    rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    have hu0 : (u:ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.1.ne'
    simp only [hwdef]
    rw [show a + ((m + n : ℕ) : ℂ) - 1 = (a - 1) + ((m + n : ℕ) : ℂ) by ring, cpow_add _ _ hu0,
      cpow_natCast, show c - a - 1 = c - a - 1 by ring]
    push_cast
    ring
  rw [hbeta]
  have hE := euler_term_eq_gaussHGCoeff (a := 1) (b := a) (c := c) (m + n) ha hca
  have hf : ((m + n) ! : ℂ) ≠ 0 := by exact_mod_cast (m + n).factorial_ne_zero
  have hB : Gamma c / (Gamma a * Gamma (c - a)) * betaIntegral (a + (m + n : ℕ)) (c - a) =
      poch a (m + n) / poch c (m + n) := by
    rw [poch_nat_one, div_self hf, one_mul] at hE
    rw [hE, gaussHGCoeff, poch_nat_one]
    have hpc := poch_ne_zero_of_not_neg_nat hc (m + n)
    field_simp
  calc appF1Coeff a b b' c m n * x ^ m * y ^ n
      = (Gamma c / (Gamma a * Gamma (c - a)) * betaIntegral (a + (m + n : ℕ)) (c - a)) *
          (poch b m / m ! * x ^ m * (poch b' n / n ! * y ^ n)) := by
        rw [hB, appF1Coeff]
        have hm : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
        have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
        have hpc := poch_ne_zero_of_not_neg_nat hc (m + n)
        field_simp
    _ = _ := by simp only [hddef]; ring

/-- 16.15.E2: appF2 euler integrable. -/
@[dlmf 16.15.E2]
theorem appF2_euler_integrable (a b b' c c' : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hcb : b.re<c.re) (hcb' : b'.re<c'.re) {x y : ℂ} (hxy : (x,y)∈{p | appellSquareSlit p}) :
    IntegrableOn (appF2EulerKernel a b b' c c' x y) (Icc (0:ℝ) 1×ˢIcc (0:ℝ) 1) := by
  obtain ⟨M, hM⟩ := ghaR4_inv_cpow_bound (f := fun p : ℝ × ℝ => 1 - (p.1:ℂ) * x - (p.2:ℂ) * y)
    (isCompact_Icc.prod isCompact_Icc) (by fun_prop) (fun p hp => hxy p.1 hp.1 p.2 hp.2) a
  have hcb1 : 0 < (c - b).re := by simp; linarith
  have hcb2 : 0 < (c' - b').re := by simp; linarith
  refine ((ghaR4_beta_prod_integrableOn hb hcb1 hb' hcb2).mul_const M).mono' ?_ ?_
  · exact (by unfold appF2EulerKernel; fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    have h1 := hM p hp
    have hM0 := (norm_nonneg _).trans h1
    simp only [appF2EulerKernel, div_eq_mul_inv, norm_mul, Complex.ofReal_sub, Complex.ofReal_one]
    calc ‖(p.1:ℂ) ^ (b - 1)‖ * ‖(p.2:ℂ) ^ (b' - 1)‖ * ‖(1 - (p.1:ℂ)) ^ (c - b - 1)‖ *
          ‖(1 - (p.2:ℂ)) ^ (c' - b' - 1)‖ * ‖((1 - (p.1:ℂ) * x - (p.2:ℂ) * y) ^ a)⁻¹‖
        ≤ ‖(p.1:ℂ) ^ (b - 1)‖ * ‖(p.2:ℂ) ^ (b' - 1)‖ * ‖(1 - (p.1:ℂ)) ^ (c - b - 1)‖ *
          ‖(1 - (p.2:ℂ)) ^ (c' - b' - 1)‖ * M := by gcongr
      _ = _ := by ring

/-- 16.15.E2: appF2 euler analytic. -/
@[dlmf 16.15.E2]
theorem appF2_euler_analytic (a b b' c c' : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hcb : b.re<c.re) (hcb' : b'.re<c'.re) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF2Euler a b b' c c' p.1 p.2) {p | appellSquareSlit p} := by
  have hU := ghaR4_isOpen_square
  have hcb1 : 0 < (c - b).re := by simp; linarith
  have hcb2 : 0 < (c' - b').re := by simp; linarith
  have hsq : MeasurableSet (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc
  have hd : DifferentiableOn ℂ (fun p : ℂ × ℂ =>
      ∫ q in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, appF2EulerKernel a b b' c c' p.1 p.2 q)
      {p | appellSquareSlit p} := by
    refine differentiableOn_integral_of_locally_dominated hU
      (fun p _ => (by unfold appF2EulerKernel; fun_prop : Measurable _).aestronglyMeasurable)
      ?_ ?_
    · filter_upwards [ae_restrict_mem hsq] with q hq
      intro p hp
      have h1 := ghaR4_differentiableAt_inv_cpow_square (p := p) (hp q.1 hq.1 q.2 hq.2) a
      have e : (fun p : ℂ × ℂ => appF2EulerKernel a b b' c c' p.1 p.2 q) = fun p =>
          (q.1:ℂ) ^ (b - 1) * (q.2:ℂ) ^ (b' - 1) * ((1 - q.1:ℝ):ℂ) ^ (c - b - 1) *
            ((1 - q.2:ℝ):ℂ) ^ (c' - b' - 1) * ((1 - (q.1:ℂ) * p.1 - (q.2:ℂ) * p.2) ^ a)⁻¹ := by
        funext p; simp only [appF2EulerKernel, div_eq_mul_inv]
      rw [e]
      exact ((differentiableAt_const _).mul h1).differentiableWithinAt
    · intro p hp
      obtain ⟨r, hr, hs⟩ := ghaR4_exists_closedBall_square hp
      obtain ⟨M, hM⟩ := ghaR4_square_inv_cpow_bound
        (f := fun z : (ℂ × ℂ) × (ℝ × ℝ) => 1 - (z.2.1:ℂ) * z.1.1 - (z.2.2:ℂ) * z.1.2)
        (by fun_prop) (fun p hp q hq => hs p hp q.1 hq.1 q.2 hq.2) a
      refine ⟨Metric.ball p r, Metric.ball_mem_nhds _ hr,
        fun q => ‖(q.1:ℂ)^(b-1) * (1 - (q.1:ℂ))^(c-b-1)‖ *
          ‖(q.2:ℂ)^(b'-1) * (1 - (q.2:ℂ))^(c'-b'-1)‖ * M, ?_, ?_⟩
      · exact (ghaR4_beta_prod_integrableOn hb hcb1 hb' hcb2).mul_const M
      · filter_upwards [ae_restrict_mem hsq] with q hq
        intro z hz
        have h1 := hM z (Metric.ball_subset_closedBall hz) q hq
        have hM0 := (norm_nonneg _).trans h1
        simp only [appF2EulerKernel, div_eq_mul_inv, norm_mul, Complex.ofReal_sub,
          Complex.ofReal_one]
        calc ‖(q.1:ℂ) ^ (b - 1)‖ * ‖(q.2:ℂ) ^ (b' - 1)‖ * ‖(1 - (q.1:ℂ)) ^ (c - b - 1)‖ *
              ‖(1 - (q.2:ℂ)) ^ (c' - b' - 1)‖ * ‖((1 - (q.1:ℂ) * z.1 - (q.2:ℂ) * z.2) ^ a)⁻¹‖
            ≤ ‖(q.1:ℂ) ^ (b - 1)‖ * ‖(q.2:ℂ) ^ (b' - 1)‖ * ‖(1 - (q.1:ℂ)) ^ (c - b - 1)‖ *
              ‖(1 - (q.2:ℂ)) ^ (c' - b' - 1)‖ * M := by gcongr
          _ = _ := by ring
  have : DifferentiableOn ℂ (fun p : ℂ × ℂ => appF2Euler a b b' c c' p.1 p.2)
      {p | appellSquareSlit p} := (differentiableOn_const _).mul hd
  exact this.analyticOnNhd_of_finiteDimensional hU

/-- 16.15.E2: appF2 euler germ. -/
@[dlmf 16.15.E2]
theorem appF2_euler_germ (a b b' c c' : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hcb : b.re<c.re) (hcb' : b'.re<c'.re) :
    (fun p : ℂ × ℂ => appF2 a b b' c c' p.1 p.2)=ᶠ[𝓝 (0,0)] (fun p => appF2Euler a b b' c c' p.1 p.2) := by
  have hcb1 : 0 < (c - b).re := by simp; linarith
  have hcb2 : 0 < (c' - b').re := by simp; linarith
  have hc : AppellRegular c := not_neg_nat_of_re_pos (re_c_pos_of hb hcb1)
  have hc' : AppellRegular c' := not_neg_nat_of_re_pos (re_c_pos_of hb' hcb2)
  have hU : {p : ℂ × ℂ | ‖p.1‖ + ‖p.2‖ < 1} ∈ 𝓝 ((0:ℂ), (0:ℂ)) :=
    (isOpen_lt ((continuous_norm.comp continuous_fst).add (continuous_norm.comp continuous_snd))
      continuous_const).mem_nhds (by simp)
  filter_upwards [hU] with p hp
  obtain ⟨x, y⟩ := p
  simp only at hp ⊢
  set f1 : ℕ → ℝ → ℂ := fun m u => (u:ℂ) ^ (b - 1) * ((1 - u : ℝ) : ℂ) ^ (c - b - 1) * (u:ℂ) ^ m
    with hf1
  set f2 : ℕ → ℝ → ℂ := fun n u => (u:ℂ) ^ (b' - 1) * ((1 - u : ℝ) : ℂ) ^ (c' - b' - 1) * (u:ℂ) ^ n
    with hf2
  set w : ℝ × ℝ → ℂ := fun q => f1 0 q.1 * f2 0 q.2 with hwdef
  set d : ℕ × ℕ → ℂ := fun q => poch a (q.1 + q.2) / (q.1 ! * q.2 ! : ℂ) * x ^ q.1 * y ^ q.2
    with hddef
  have hsq : MeasurableSet (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc
  have hint0 : ∀ {β γ : ℂ}, 0 < β.re → 0 < γ.re →
      IntegrableOn (fun u : ℝ => (u:ℂ) ^ (β - 1) * ((1 - u : ℝ) : ℂ) ^ (γ - 1)) (Icc 0 1) := by
    intro β γ hβ hγ
    refine (ghaR4_beta_integrableOn hβ hγ).congr_fun (fun u _ => ?_) measurableSet_Icc
    push_cast; ring
  have hw : Integrable w (volume.restrict (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    refine ((hint0 hb hcb1).mul_prod (hint0 hb' hcb2)).congr (Eventually.of_forall fun q => ?_)
    simp [hwdef, hf1, hf2]
  have hd : Summable fun q => ‖d q‖ := (ghaR4_hasSum_binom2 a hp).2
  have key := ghaR4_hasSum_integral (μ := volume.restrict (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)) hw hd
    (e := fun q z => (z.1:ℂ) ^ q.1 * (z.2:ℂ) ^ q.2) (fun q => by fun_prop)
    (fun q => by
      filter_upwards [ae_restrict_mem hsq] with z hz
      rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hz.1.1, abs_of_nonneg hz.2.1]
      calc z.1 ^ q.1 * z.2 ^ q.2 ≤ 1 * 1 :=
            mul_le_mul (pow_le_one₀ hz.1.1 hz.1.2) (pow_le_one₀ hz.2.1 hz.2.2)
              (pow_nonneg hz.2.1 _) zero_le_one
        _ = 1 := one_mul 1)
    (g := fun z => ((1 - (z.1:ℂ) * x - (z.2:ℂ) * y) ^ a)⁻¹)
    (by
      filter_upwards [ae_restrict_mem hsq] with z hz
      have hz1 : ‖x * z.1‖ ≤ ‖x‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz.1.1]
        nlinarith [norm_nonneg x, hz.1.2]
      have hz2 : ‖y * z.2‖ ≤ ‖y‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz.2.1]
        nlinarith [norm_nonneg y, hz.2.2]
      have h := (ghaR4_hasSum_binom2 a (s := x * z.1) (t := y * z.2) (by linarith)).1
      rw [cpow_neg, mul_comm x, mul_comm y] at h
      refine h.congr_fun fun q => ?_
      simp only [hddef]
      rw [mul_pow, mul_pow]
      ring)
  have hsum := hasSum_appF2 a b b' c c' hc hc' (x := x) (y := y) hp
  refine hsum.unique ?_
  unfold appF2Euler
  have e1 : (∫ z in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, appF2EulerKernel a b b' c c' x y z) =
      ∫ z in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, w z * ((1 - (z.1:ℂ) * x - (z.2:ℂ) * y) ^ a)⁻¹ := by
    congr 1; funext z; simp only [appF2EulerKernel, hwdef, hf1, hf2, div_eq_mul_inv]; ring
  rw [e1]
  refine (key.mul_left (Gamma c * Gamma c' / (Gamma b * Gamma b' * Gamma (c - b) *
    Gamma (c' - b')))).congr_fun fun q => ?_
  obtain ⟨m, n⟩ := q
  simp only
  have hI : (∫ z in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, w z * ((z.1:ℂ) ^ m * (z.2:ℂ) ^ n)) =
      betaIntegral (b + m) (c - b) * betaIntegral (b' + n) (c' - b') := by
    have e2 : (fun z : ℝ × ℝ => w z * ((z.1:ℂ) ^ m * (z.2:ℂ) ^ n)) =
        fun z => f1 m z.1 * f2 n z.2 := by
      funext z; simp only [hwdef, hf1, hf2, pow_zero, mul_one]; ring
    rw [e2, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_mul]
    rw [show c - b - 1 = (c - b) - 1 by ring] at hf1
    simp only [hf1, hf2]
    rw [ghaR4_beta_moment m, ghaR4_beta_moment n]
  rw [hI]
  have hB1 := ghaR4_gamma_beta hb hcb1 m
  have hB2 := ghaR4_gamma_beta hb' hcb2 n
  have hG : Gamma c * Gamma c' / (Gamma b * Gamma b' * Gamma (c - b) * Gamma (c' - b')) *
      (betaIntegral (b + m) (c - b) * betaIntegral (b' + n) (c' - b')) =
      poch b m / poch c m * (poch b' n / poch c' n) := by
    rw [← hB1, ← hB2]; ring
  have hm : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hpc := poch_ne_zero_of_not_neg_nat hc m
  have hpc' := poch_ne_zero_of_not_neg_nat hc' n
  calc appF2Coeff a b b' c c' m n * x ^ m * y ^ n
      = (poch b m / poch c m * (poch b' n / poch c' n)) *
          (poch a (m + n) / (m ! * n ! : ℂ) * x ^ m * y ^ n) := by
        rw [appF2Coeff]; field_simp
    _ = _ := by rw [← hG]; simp only [hddef]; ring

/-- 16.15.E3: appF3 euler integrable. -/
@[dlmf 16.15.E3]
theorem appF3_euler_integrable (a a' b b' c : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hrest : 0<(c-b-b').re) {x y : ℂ} (hxy : (x,y)∈appellEulerDomain) :
    IntegrableOn (appF3EulerKernel a a' b b' c x y) appellTriangle := by
  sorry

/-- 16.15.E3: appF3 euler analytic. -/
@[dlmf 16.15.E3]
theorem appF3_euler_analytic (a a' b b' c : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hrest : 0<(c-b-b').re) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF3Euler a a' b b' c p.1 p.2) appellEulerDomain := by
  sorry

/-- 16.15.E3: appF3 euler germ. -/
@[dlmf 16.15.E3]
theorem appF3_euler_germ (a a' b b' c : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hrest : 0<(c-b-b').re) :
    (fun p : ℂ × ℂ => appF3 a a' b b' c p.1 p.2)=ᶠ[𝓝 (0,0)] (fun p => appF3Euler a a' b b' c p.1 p.2) := by
  sorry

/-- 16.15.E4: appF4 euler integrable. -/
@[dlmf 16.15.E4]
theorem appF4_euler_integrable (a b c c' : ℂ) (ha : 0<a.re) (hb : 0<b.re) (hca : a.re<c.re) (hcb : b.re<c'.re) {x y : ℂ} (hxy : (x,y)∈{p | appellSquareSlit p}) :
    IntegrableOn (appF4EulerKernel a b c c' x y) (Icc (0:ℝ) 1×ˢIcc (0:ℝ) 1) := by
  have hK : IsCompact (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := left_mem_Icc.mpr zero_le_one
  obtain ⟨M1, hM1⟩ := ghaR4_inv_cpow_bound (f := fun p : ℝ × ℝ => 1 - (p.1:ℂ) * x)
    hK (by fun_prop) (fun p hp => by simpa using hxy p.1 hp.1 0 h0) (c + c' - a - 1)
  obtain ⟨M2, hM2⟩ := ghaR4_inv_cpow_bound (f := fun p : ℝ × ℝ => 1 - (p.2:ℂ) * y)
    hK (by fun_prop) (fun p hp => by simpa using hxy 0 h0 p.2 hp.2) (c + c' - b - 1)
  obtain ⟨M3, hM3⟩ := ghaR4_inv_cpow_bound (f := fun p : ℝ × ℝ => 1 - (p.1:ℂ) * x - (p.2:ℂ) * y)
    hK (by fun_prop) (fun p hp => hxy p.1 hp.1 p.2 hp.2) (a + b - c - c' + 1)
  have hca1 : 0 < (c - a).re := by simp; linarith
  have hcb1 : 0 < (c' - b).re := by simp; linarith
  refine ((ghaR4_beta_prod_integrableOn ha hca1 hb hcb1).mul_const (M1 * M2 * M3)).mono' ?_ ?_
  · exact (by unfold appF4EulerKernel; fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    have h1 := hM1 p hp
    have h2 := hM2 p hp
    have h3 := hM3 p hp
    have hM10 := (norm_nonneg _).trans h1
    have hM20 := (norm_nonneg _).trans h2
    have hM30 := (norm_nonneg _).trans h3
    simp only [appF4EulerKernel, div_eq_mul_inv, norm_mul, Complex.ofReal_sub, Complex.ofReal_one]
    calc ‖(p.1:ℂ) ^ (a - 1)‖ * ‖(p.2:ℂ) ^ (b - 1)‖ * ‖(1 - (p.1:ℂ)) ^ (c - a - 1)‖ *
          ‖(1 - (p.2:ℂ)) ^ (c' - b - 1)‖ * ‖((1 - (p.1:ℂ) * x) ^ (c + c' - a - 1))⁻¹‖ *
          ‖((1 - (p.2:ℂ) * y) ^ (c + c' - b - 1))⁻¹‖ *
          ‖((1 - (p.1:ℂ) * x - (p.2:ℂ) * y) ^ (a + b - c - c' + 1))⁻¹‖
        ≤ ‖(p.1:ℂ) ^ (a - 1)‖ * ‖(p.2:ℂ) ^ (b - 1)‖ * ‖(1 - (p.1:ℂ)) ^ (c - a - 1)‖ *
          ‖(1 - (p.2:ℂ)) ^ (c' - b - 1)‖ * M1 * M2 * M3 := by gcongr
      _ = _ := by ring

/-- 16.15.E4: appF4 euler analytic. -/
@[dlmf 16.15.E4]
theorem appF4_euler_analytic (a b c c' : ℂ) (ha : 0<a.re) (hb : 0<b.re) (hca : a.re<c.re) (hcb : b.re<c'.re) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF4Euler a b c c' p.1 p.2) {p | appellSquareSlit p} := by
  have hU := ghaR4_isOpen_square
  have hca1 : 0 < (c - a).re := by simp; linarith
  have hcb1 : 0 < (c' - b).re := by simp; linarith
  have hsq : MeasurableSet (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := left_mem_Icc.mpr zero_le_one
  have hd : DifferentiableOn ℂ (fun p : ℂ × ℂ =>
      ∫ q in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, appF4EulerKernel a b c c' p.1 p.2 q)
      {p | appellSquareSlit p} := by
    refine differentiableOn_integral_of_locally_dominated hU
      (fun p _ => (by unfold appF4EulerKernel; fun_prop : Measurable _).aestronglyMeasurable)
      ?_ ?_
    · filter_upwards [ae_restrict_mem hsq] with q hq
      intro p hp
      have h1 := ghaR4_differentiableAt_inv_cpow_square (p := p) (u := q.1) (v := 0)
        (by simpa using hp q.1 hq.1 0 h0) (c + c' - a - 1)
      have h2 := ghaR4_differentiableAt_inv_cpow_square (p := p) (u := 0) (v := q.2)
        (by simpa using hp 0 h0 q.2 hq.2) (c + c' - b - 1)
      have h3 := ghaR4_differentiableAt_inv_cpow_square (p := p) (hp q.1 hq.1 q.2 hq.2)
        (a + b - c - c' + 1)
      have e : (fun p : ℂ × ℂ => appF4EulerKernel a b c c' p.1 p.2 q) = fun p =>
          (q.1:ℂ) ^ (a - 1) * (q.2:ℂ) ^ (b - 1) * ((1 - q.1:ℝ):ℂ) ^ (c - a - 1) *
            ((1 - q.2:ℝ):ℂ) ^ (c' - b - 1) *
            ((1 - (q.1:ℂ) * p.1 - ((0:ℝ):ℂ) * p.2) ^ (c + c' - a - 1))⁻¹ *
            ((1 - ((0:ℝ):ℂ) * p.1 - (q.2:ℂ) * p.2) ^ (c + c' - b - 1))⁻¹ *
            ((1 - (q.1:ℂ) * p.1 - (q.2:ℂ) * p.2) ^ (a + b - c - c' + 1))⁻¹ := by
        funext p; simp only [appF4EulerKernel, div_eq_mul_inv]; simp
      rw [e]
      exact ((((differentiableAt_const _).mul h1).mul h2).mul h3).differentiableWithinAt
    · intro p hp
      obtain ⟨r, hr, hs⟩ := ghaR4_exists_closedBall_square hp
      obtain ⟨M1, hM1⟩ := ghaR4_square_inv_cpow_bound
        (f := fun z : (ℂ × ℂ) × (ℝ × ℝ) => 1 - (z.2.1:ℂ) * z.1.1)
        (by fun_prop) (fun p hp q hq => by simpa using hs p hp q.1 hq.1 0 h0) (c + c' - a - 1)
      obtain ⟨M2, hM2⟩ := ghaR4_square_inv_cpow_bound
        (f := fun z : (ℂ × ℂ) × (ℝ × ℝ) => 1 - (z.2.2:ℂ) * z.1.2)
        (by fun_prop) (fun p hp q hq => by simpa using hs p hp 0 h0 q.2 hq.2) (c + c' - b - 1)
      obtain ⟨M3, hM3⟩ := ghaR4_square_inv_cpow_bound
        (f := fun z : (ℂ × ℂ) × (ℝ × ℝ) => 1 - (z.2.1:ℂ) * z.1.1 - (z.2.2:ℂ) * z.1.2)
        (by fun_prop) (fun p hp q hq => hs p hp q.1 hq.1 q.2 hq.2) (a + b - c - c' + 1)
      refine ⟨Metric.ball p r, Metric.ball_mem_nhds _ hr,
        fun q => ‖(q.1:ℂ)^(a-1) * (1 - (q.1:ℂ))^(c-a-1)‖ *
          ‖(q.2:ℂ)^(b-1) * (1 - (q.2:ℂ))^(c'-b-1)‖ * (M1 * M2 * M3), ?_, ?_⟩
      · exact (ghaR4_beta_prod_integrableOn ha hca1 hb hcb1).mul_const _
      · filter_upwards [ae_restrict_mem hsq] with q hq
        intro z hz
        have hz' := Metric.ball_subset_closedBall hz
        have h1 := hM1 z hz' q hq
        have h2 := hM2 z hz' q hq
        have h3 := hM3 z hz' q hq
        have hM10 := (norm_nonneg _).trans h1
        have hM20 := (norm_nonneg _).trans h2
        have hM30 := (norm_nonneg _).trans h3
        simp only [appF4EulerKernel, div_eq_mul_inv, norm_mul, Complex.ofReal_sub,
          Complex.ofReal_one]
        calc ‖(q.1:ℂ) ^ (a - 1)‖ * ‖(q.2:ℂ) ^ (b - 1)‖ * ‖(1 - (q.1:ℂ)) ^ (c - a - 1)‖ *
              ‖(1 - (q.2:ℂ)) ^ (c' - b - 1)‖ * ‖((1 - (q.1:ℂ) * z.1) ^ (c + c' - a - 1))⁻¹‖ *
              ‖((1 - (q.2:ℂ) * z.2) ^ (c + c' - b - 1))⁻¹‖ *
              ‖((1 - (q.1:ℂ) * z.1 - (q.2:ℂ) * z.2) ^ (a + b - c - c' + 1))⁻¹‖
            ≤ ‖(q.1:ℂ) ^ (a - 1)‖ * ‖(q.2:ℂ) ^ (b - 1)‖ * ‖(1 - (q.1:ℂ)) ^ (c - a - 1)‖ *
              ‖(1 - (q.2:ℂ)) ^ (c' - b - 1)‖ * M1 * M2 * M3 := by gcongr
          _ = _ := by ring
  have : DifferentiableOn ℂ (fun p : ℂ × ℂ => appF4Euler a b c c' p.1 p.2)
      {p | appellSquareSlit p} := (differentiableOn_const _).mul hd
  exact this.analyticOnNhd_of_finiteDimensional hU

/-- 16.15.E4: appF4 euler germ. -/
@[dlmf 16.15.E4]
theorem appF4_euler_germ (a b c c' : ℂ) (ha : 0<a.re) (hb : 0<b.re) (hca : a.re<c.re) (hcb : b.re<c'.re) :
    (fun p : ℂ × ℂ => appF4 a b c c' (p.1*(1-p.2)) (p.2*(1-p.1)))=ᶠ[𝓝 (0,0)] (fun p => appF4Euler a b c c' p.1 p.2) := by
  sorry

/-- 16.16.E1: appF1 reduction gauss. -/
@[dlmf 16.16.E1]
theorem appF1_reduction_gauss (a b b' : ℂ) (hc : AppellRegular (b+b')) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF1 a b b' (b+b') x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-y)^(-a)*₂F₁ a b (b+b') ((x-y)/(1-y))) := by
  sorry

/-- The Gauss series in the unit disk, as a scalar `HasSum`. -/
lemma ghaR4_gauss_hasSum {a b c z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => gaussHGCoeff a b c n * z ^ n) (₂F₁ a b c z) := by
  have := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).hasSum
    (y := z) (by simpa using mem_eball_one_of_norm_lt_one hz)
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using this

/-- 16.16.E2: appF2 reduction gauss. -/
@[dlmf 16.16.E2]
theorem appF2_reduction_gauss (a b b' c : ℂ) (hc : AppellRegular c) (hb' : AppellRegular b') :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF2 a b b' c b' x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-y)^(-a)*₂F₁ a b c (x/(1-y))) := by
  have hU : {p : ℂ × ℂ | ‖p.1‖ + ‖p.2‖ < 1} ∈ 𝓝 ((0:ℂ), (0:ℂ)) :=
    (isOpen_lt ((continuous_norm.comp continuous_fst).add (continuous_norm.comp continuous_snd))
      continuous_const).mem_nhds (by simp)
  filter_upwards [hU] with p hp
  obtain ⟨x, y⟩ := p
  simp only at hp ⊢
  have hy : ‖y‖ < 1 := by linarith [norm_nonneg x]
  have h1y : 1 - y ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h] at hy; simp at hy
  have hny : 1 - ‖y‖ ≤ ‖1 - y‖ := by
    have := norm_sub_norm_le (1 : ℂ) y; simpa using this
  have hz : ‖x / (1 - y)‖ < 1 := by
    rw [norm_div, div_lt_one (by linarith)]; linarith
  have hsum := hasSum_appF2 a b b' c b' hc hb' (x := x) (y := y) hp
  have hfib : ∀ m : ℕ, HasSum (fun n => appF2Coeff a b b' c b' m n * x ^ m * y ^ n)
      (gaussHGCoeff a b c m * x ^ m * (1 - y) ^ (-(a + m))) := by
    intro m
    have h := (hasSum_poch_div_factorial (β := a + m) hy).mul_left (gaussHGCoeff a b c m * x ^ m)
    refine h.congr_fun fun n => ?_
    have hpb := poch_ne_zero_of_not_neg_nat hb' n
    have hpc := poch_ne_zero_of_not_neg_nat hc m
    have hm : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    rw [appF2Coeff, gaussHGCoeff, poch_add a m n]
    field_simp
  have hG := hsum.prod_fiberwise hfib
  refine hG.unique ?_
  have h2 := (ghaR4_gauss_hasSum (a := a) (b := b) (c := c) hz).mul_left ((1 - y) ^ (-a))
  refine h2.congr_fun fun m => ?_
  rw [show -(a + (m : ℂ)) = -a + -(m : ℂ) by ring, cpow_add _ _ h1y, cpow_neg (1 - y) (m : ℂ),
    cpow_natCast, div_pow]
  field_simp

/-- 16.16.E3: appF2 reduction appF1. -/
@[dlmf 16.16.E3]
theorem appF2_reduction_appF1 (a b b' c : ℂ) (hc : AppellRegular c) (ha : AppellRegular a) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF2 a b b' c a x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-y)^(-b')*appF1 b (a-b') b' c x (x/(1-y))) := by
  sorry

/-- 16.16.E4: appF3 reduction appF1. -/
@[dlmf 16.16.E4]
theorem appF3_reduction_appF1 (a b b' c : ℂ) (hc : AppellRegular c) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF3 a (c-a) b b' c x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-y)^(-b')*appF1 a b b' c x (y/(y-1))) := by
  sorry

/-- 16.16.E5: appF3 reduction gauss. -/
@[dlmf 16.16.E5]
theorem appF3_reduction_gauss (a b c : ℂ) (hc : AppellRegular c) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF3 a (c-a) b (c-b) c x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-y)^(a+b-c)*₂F₁ a b c (x+y-x*y)) := by
  sorry

/-- 16.16.E5_5: appF4 reduction appF1. -/
@[dlmf 16.16.E5_5]
theorem appF4_reduction_appF1 (a b c : ℂ) (hc : AppellRegular c) (hb : AppellRegular b) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF4 a b c b (x*(1-y)) (y*(1-x)))=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-x)^(-a)*(1-y)^(-a)*appF1 a (c-b) (a-c+1) c (x/(x-1)) (x*y/((1-x)*(1-y)))) := by
  sorry

/-- A geometric bound for the F4 coefficients at regular lower parameters. -/
lemma ghaR4_appF4Coeff_geom (a b c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m n : ℕ, ‖appF4Coeff a b c c' m n‖ ≤ C * (8 ^ m * 8 ^ n) := by
  obtain ⟨C, hC⟩ := ghaR4_appF4Coeff_bound a b c c' hc hc' (σ := 2) (by norm_num)
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC (0, 0))
    simpa using this
  refine ⟨C, hC0, fun m n => (hC (m, n)).trans ?_⟩
  have h1 : (((m + n).choose m : ℕ) : ℝ) ≤ 2 ^ (m + n) := by exact_mod_cast Nat.choose_le_two_pow _ _
  calc C * 2 ^ (m + n) * (((m + n).choose m : ℕ) : ℝ) ^ 2 ≤ C * 2 ^ (m + n) * (2 ^ (m + n)) ^ 2 := by
        gcongr
    _ = C * (8 ^ m * 8 ^ n) := by
        have : (8:ℝ) ^ m * 8 ^ n = (2 ^ (m + n)) ^ 3 := by
          rw [← pow_add, show (8:ℝ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
        rw [this]; ring

/-- Bailey's product formula at all regular lower parameters (stronger than `appF4_bailey`,
which assumes positive real parts). The proof is that of `appF4_bailey` in
`DLMF.Hypergeometric.AppellF4`, with its coefficient bound replaced by `ghaR4_appF4Coeff_geom`. -/
lemma ghaR4_appF4_bailey {a b c c' : ℂ} (hcc : c + c' = a + b + 1) (hc : AppellRegular c)
    (hc' : AppellRegular c') : ∃ δ > 0, ∀ X Y : ℂ, ‖X‖ < δ → ‖Y‖ < δ →
      HasSum (fun p : ℕ × ℕ => appF4Coeff a b c c' p.1 p.2 * (X * (1 - Y)) ^ p.1 *
        (Y * (1 - X)) ^ p.2) (₂F₁ a b c X * ₂F₁ a b c' Y) := by
  obtain ⟨C, hC0, hCb⟩ := ghaR4_appF4Coeff_geom a b c c' hc hc'
  refine ⟨1 / 1024, by norm_num, fun X Y hX hY => ?_⟩
  have hpc : ∀ k, poch c k ≠ 0 := poch_ne_zero_of_not_neg_nat hc
  have hpc' : ∀ k, poch c' k ≠ 0 := poch_ne_zero_of_not_neg_nat hc'
  have hsq : ∀ W : ℂ, ‖W‖ < 1 / 1024 → Real.sqrt ‖W‖ < 1 / 32 := by
    intro W hW
    rw [show (1 / 32 : ℝ) = Real.sqrt (1 / 1024) by
      rw [show (1 / 1024 : ℝ) = (1 / 32) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] ]
    exact Real.sqrt_lt_sqrt (norm_nonneg _) hW
  have hX1 : ‖X‖ ≤ 1 := by linarith
  have hY1 : ‖Y‖ ≤ 1 := by linarith
  set sX := Real.sqrt ‖X‖ with hsX
  set sY := Real.sqrt ‖Y‖ with hsY
  have hsX0 : 0 ≤ sX := Real.sqrt_nonneg _
  have hsY0 : 0 ≤ sY := Real.sqrt_nonneg _
  have hsXQ : sX < 1 / 32 := hsq X hX
  have hsYQ : sY < 1 / 32 := hsq Y hY
  have hsX1 : sX < 1 := by linarith
  have hsY1 : sY < 1 := by linarith
  set rX := 2 * 8 * sX with hrX
  set rY := 2 * 8 * sY with hrY
  have hrX0 : 0 ≤ rX := by positivity
  have hrY0 : 0 ≤ rY := by positivity
  have hrX1 : rX < 1 := by rw [hrX]; linarith
  have hrY1 : rY < 1 := by rw [hrY]; linarith
  have hgeo : ∀ u v : ℝ, 0 ≤ u → u < 1 → 0 ≤ v → v < 1 →
      Summable fun p : ℕ × ℕ => u ^ p.1 * v ^ p.2 := fun u v hu0 hu1 hv0 hv1 =>
    (summable_geometric_of_lt_one hu0 hu1).mul_of_nonneg (summable_geometric_of_lt_one hv0 hv1)
      (fun _ => by positivity) (fun _ => by positivity)
  have hD : Summable fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
      C * ((rX ^ p.1.1 * rY ^ p.1.2) * (sX ^ p.2.1 * sY ^ p.2.2)) :=
    ((hgeo rX rY hrX0 hrX1 hrY0 hrY1).mul_of_nonneg (hgeo sX sY hsX0 hsX1 hsY0 hsY1)
      (fun _ => by positivity) (fun _ => by positivity)).mul_left C
  have hsum : Summable (appF4Fam a b c c' X Y) := by
    refine Summable.of_norm_bounded hD fun p => ?_
    obtain ⟨⟨m, n⟩, ⟨M, N⟩⟩ := p
    unfold appF4Fam
    simp only
    rw [norm_mul, norm_mul]
    have h1 := hCb m n
    have h2 := appF4E_norm_le m n M hX1
    have h3 := appF4E_norm_le n m N hY1
    calc ‖appF4Coeff a b c c' m n‖ * ‖appF4E m n M * X ^ M‖ * ‖appF4E n m N * Y ^ N‖
        ≤ (C * (8 ^ m * 8 ^ n)) * (2 ^ n * sX ^ m * sX ^ M) * (2 ^ m * sY ^ n * sY ^ N) := by
          gcongr
      _ = _ := by rw [hrX, hrY]; simp only [mul_pow]; ring
  have hS := hsum.hasSum
  have hfib1 : ∀ p : ℕ × ℕ, HasSum (fun q => appF4Fam a b c c' X Y (p, q))
      (appF4Coeff a b c c' p.1 p.2 * (X * (1 - Y)) ^ p.1 * (Y * (1 - X)) ^ p.2) := by
    rintro ⟨m, n⟩
    have hfin := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _)
      (s := Finset.range (m + n + 1) ×ˢ Finset.range (m + n + 1))
      (f := fun q => appF4Fam a b c c' X Y ((m, n), q)) (fun q hq => by
        obtain ⟨M, N⟩ := q
        simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hq
        unfold appF4Fam
        simp only
        rcases hq with h | h
        · rw [appF4E_eq_zero_of_lt (by omega)]; simp
        · rw [appF4E_eq_zero_of_lt (m := n) (n := m) (by omega)]; simp)
    convert hfin using 1
    rw [Finset.sum_product]
    simp only [appF4Fam]
    have h1 := appF4E_sum m n X
    have h2 := appF4E_sum n m Y
    rw [show n + m + 1 = m + n + 1 by ring] at h2
    have : ∑ x ∈ Finset.range (m + n + 1), ∑ y ∈ Finset.range (m + n + 1),
        appF4Coeff a b c c' m n * (appF4E m n x * X ^ x) * (appF4E n m y * Y ^ y) =
        appF4Coeff a b c c' m n * ((∑ x ∈ Finset.range (m + n + 1), appF4E m n x * X ^ x) *
          (∑ y ∈ Finset.range (m + n + 1), appF4E n m y * Y ^ y)) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [this, h1, h2]
    simp only [mul_pow]
    ring
  have hF4 := hS.prod_fiberwise hfib1
  have hfib2 : ∀ q : ℕ × ℕ, HasSum (fun p => appF4Fam a b c c' X Y (p, q))
      (gaussHGCoeff a b c q.1 * X ^ q.1 * (gaussHGCoeff a b c' q.2 * Y ^ q.2)) := by
    rintro ⟨M, N⟩
    have hfin := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _)
      (s := Finset.range (M + 1) ×ˢ Finset.range (N + 1))
      (f := fun p => appF4Fam a b c c' X Y (p, (M, N))) (fun p hp => by
        obtain ⟨m, n⟩ := p
        simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hp
        unfold appF4Fam appF4E
        simp only
        rcases hp with h | h
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; simp
        · rw [ite_eq_right_of_eq_false (c := n ≤ N) _ _ (eq_false (by omega))]; simp)
    convert hfin using 1
    rw [Finset.sum_product]
    simp only
    rw [show gaussHGCoeff a b c M * X ^ M * (gaussHGCoeff a b c' N * Y ^ N) =
      (gaussHGCoeff a b c M * gaussHGCoeff a b c' N) * (X ^ M * Y ^ N) by ring,
      ← appF4_coeff hcc hpc hpc' M N, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hmM : m ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    unfold appF4Fam appF4Term appF4E
    simp only
    rw [ite_eq_left_of_eq_true _ _ (eq_true hmM), ite_eq_left_of_eq_true _ _ (eq_true hnN)]
    ring
  have hS' : HasSum (fun x : (ℕ × ℕ) × (ℕ × ℕ) => appF4Fam a b c c' X Y (x.2, x.1))
      (∑' p, appF4Fam a b c c' X Y p) :=
    ((Equiv.prodComm (ℕ × ℕ) (ℕ × ℕ)).hasSum_iff (f := appF4Fam a b c c' X Y)).mpr hS
  have hG := hS'.prod_fiberwise hfib2
  have hXs := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one (show ‖X‖ < 1 by linarith))
  have hYs := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c').hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one (show ‖Y‖ < 1 by linarith))
  have hprod := hXs.mul hYs hG.summable
  rw [hG.unique hprod] at hF4
  exact hF4

/-- 16.16.E6: appF4 product germ. -/
@[dlmf 16.16.E6]
theorem appF4_product_germ (a b c : ℂ) (hc : AppellRegular c) (hc' : AppellRegular (a+b-c+1)) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF4 a b c (a+b-c+1) (x*(1-y)) (y*(1-x)))=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; ₂F₁ a b c x*₂F₁ a b (a+b-c+1) y) := by
  obtain ⟨δ, hδ, h⟩ := ghaR4_appF4_bailey (a := a) (b := b) (c := c) (c' := a + b - c + 1)
    (by ring) hc hc'
  have hU : {p : ℂ × ℂ | ‖p.1‖ < δ ∧ ‖p.2‖ < δ} ∈ 𝓝 ((0:ℂ), (0:ℂ)) :=
    ((isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)).mem_nhds
      (by simp [hδ])
  filter_upwards [hU] with p hp
  exact (h p.1 p.2 hp.1 hp.2).tsum_eq

/-- 16.16.E8: appF1 pfaff first. -/
@[dlmf 16.16.E8]
theorem appF1_pfaff_first (a b b' c : ℂ) (hc : AppellRegular c) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF1 a b b' c x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-x)^(-b)*(1-y)^(-b')*appF1 (c-a) b b' c (x/(x-1)) (y/(y-1))) := by
  sorry

/-- 16.16.E8: appF1 pfaff second. -/
@[dlmf 16.16.E8]
theorem appF1_pfaff_second (a b b' c : ℂ) (hc : AppellRegular c) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF1 a b b' c x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-x)^(-a)*appF1 a (c-b-b') b' c (x/(x-1)) ((y-x)/(1-x))) := by
  sorry

/-- 16.16.E9: appF2 pfaff. -/
@[dlmf 16.16.E9]
theorem appF2_pfaff (a b b' c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF2 a b b' c c' x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-x)^(-a)*appF2 a (c-b) b' c c' (x/(x-1)) (y/(1-x))) := by
  sorry

/-- 16.16.E7: appF4 burchnall chaundy. -/
@[dlmf 16.16.E7]
theorem appF4_burchnall_chaundy (a b c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') :
    ∃ δ>0,∀ x y : ℂ,‖x‖<δ→‖y‖<δ→
      HasSum (fun k : ℕ => poch a k*poch b k*poch (a+b-c-c'+1) k/
        (poch c k*poch c' k*k !)*x^k*y^k*₂F₁ (a+k) (b+k) (c+k) x*
          ₂F₁ (a+k) (b+k) (c'+k) y) (appF4 a b c c' (x*(1-y)) (y*(1-x))) := by
  sorry

/-- The large-variable formula is a branch reached by analytic continuation, not a divergent-series identity. -/
@[dlmf 16.16.E10]
theorem appF4_infinity_connection (a b c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c')
    (hab : ∀ k : ℤ,a-b≠k) {x y : ℂ}
    (hconv : (x/y,1/y)∈appellF4Domain) (hy : -y∈slitPlane) :
    IsAppellBranchAt (fun p : ℂ × ℂ => appF4 a b c c' p.1 p.2) (x,y)
      (fun p => Gamma c'*Gamma (b-a)/(Gamma (c'-a)*Gamma b)*(-p.2)^(-a)*
        appF4 a (a-c'+1) c (a-b+1) (p.1/p.2) (1/p.2)+
        Gamma c'*Gamma (a-b)/(Gamma (c'-b)*Gamma a)*(-p.2)^(-b)*
        appF4 b (b-c'+1) c (b-a+1) (p.1/p.2) (1/p.2)) := by
  sorry

/-- Coalescing exponent parameters require the combined connection expression limit. -/
@[dlmf 16.16.E10]
theorem appF4_infinity_resonance_limits {a b c c' : ℂ} (hc : AppellRegular c) (hc' : AppellRegular c')
    (k : ℤ) (hab : a-b=k) {x y : ℂ} (hconv : (x/y,1/y)∈appellF4Domain) (hy : -y∈slitPlane) :
    ∃ L : ℂ,Tendsto (fun a' : ℂ =>
      Gamma c'*Gamma (b-a')/(Gamma (c'-a')*Gamma b)*(-y)^(-a')*
        appF4 a' (a'-c'+1) c (a'-b+1) (x/y) (1/y)+
      Gamma c'*Gamma (a'-b)/(Gamma (c'-b)*Gamma a')*(-y)^(-b)*
        appF4 b (b-c'+1) c (b-a'+1) (x/y) (1/y)) (𝓝[≠] a) (𝓝 L) := by
  sorry


end DLMF.Hypergeometric
