/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.Basic.Hyperbolic
public import DLMF.IncompleteGamma.FractionTools
public import DLMF.Legendre.Series
public import DLMFMathlib.Analysis.ContinuedFraction.JacobiValueRegion
public import DLMFMathlib.Analysis.Complex.RealSegmentComplement
public import TauCeti.Analysis.Complex.Conformal.Vitali

/-!
# Continued fractions for the logarithm and inverse tangent

The Jacobi fraction with numerators `1,-1²,-2²,…` and denominators `x,3x,5x,…` converges to
`½ log((x+1)/(x-1))` off the real segment `[-1,1]`. Real convergence follows from the minimal
Legendre solution. Holomorphic convergence then follows from Jacobi value bounds and Vitali's
theorem. Substitution yields the elementary fractions of DLMF 4.9.2, 4.25.4 and 4.39.3.
-/

@[expose] public noncomputable section

open Complex Filter Set GenContFract
open scoped Topology Nat

namespace DLMF.Elementary.LogarithmContinuedFraction

/-- The Jacobi numerators for the Cauchy transform of the uniform measure on `[-1,1]`. -/
def numerator (k : ℕ) : ℂ := if k = 0 then 1 else -(k : ℂ) ^ 2

/-- The Jacobi denominators for the logarithmic continued fraction. -/
def denominator (z : ℂ) (k : ℕ) : ℂ := (2 * k + 1) * z

/-- The finite logarithmic Jacobi convergent. -/
def convergent (n : ℕ) (z : ℂ) : ℂ := (ofFun 0 numerator (denominator z)).convs n

/-- The principal logarithmic Cauchy transform on the complement of the unit segment. -/
def logarithm (z : ℂ) : ℂ := 1 / 2 * Complex.log ((z + 1) / (z - 1))

/-- Every finite convergent is pole-free and uniformly bounded off the real unit segment. -/
theorem convergent_bound {z : ℂ} (hz : z ∈ realSegmentComplement (-1) 1) (n : ℕ) :
    (ofFun 0 numerator (denominator z)).dens n ≠ 0 ∧
      ‖convergent n z‖ ≤ 1 / max (|z.re| - 1) |z.im| := by
  have h := ofFun_jacobi_bound (a := numerator) (b := denominator z)
    (c := fun k => (k : ℝ)) (d := fun k => 2 * (k : ℝ) + 1)
    (max_abs_re_sub_one_abs_im_pos hz) (fun k => Nat.cast_nonneg k) (fun k => by positivity)
    (fun k => by push_cast; linarith)
    (fun k hk => by simp [numerator, show k ≠ 0 by omega]) (fun k => by
      simp only [denominator]; push_cast; rfl) n
  simpa [convergent, numerator] using h

/-- Every finite logarithmic convergent is holomorphic off the real unit segment. -/
theorem differentiableOn_convergent (n : ℕ) :
    DifferentiableOn ℂ (convergent n) (realSegmentComplement (-1) 1) := by
  apply ofFun_convs_differentiableOn (differentiableOn_const (0 : ℂ))
    (fun k => differentiableOn_const (numerator k)) (fun k => ?_) n
    (fun z hz => (convergent_bound hz n).1)
  exact (differentiableOn_const (2 * (k : ℂ) + 1)).mul differentiableOn_id

/-- The principal logarithmic target is holomorphic off the real unit segment. -/
theorem differentiableOn_logarithm :
    DifferentiableOn ℂ logarithm (realSegmentComplement (-1) 1) := by
  intro z hz
  have hz1 : z - 1 ≠ 0 := by
    intro he
    have hz' : z = 1 := sub_eq_zero.mp he
    rw [hz'] at hz
    norm_num [realSegmentComplement] at hz
  have hd : DifferentiableAt ℂ (fun z : ℂ => (z + 1) / (z - 1)) z :=
    (differentiableAt_id.add_const (1 : ℂ)).div
      (differentiableAt_id.sub_const (1 : ℂ)) hz1
  exact (hd.clog (add_one_div_sub_one_mem_slitPlane hz)).const_mul (1 / 2) |>.differentiableWithinAt

/-- The logarithmic convergents are locally bounded throughout the exterior segment domain. -/
theorem isLocallyBoundedOn_convergent :
    TauCeti.IsLocallyBoundedOn convergent (realSegmentComplement (-1) 1) := by
  have hβ : ContinuousOn (fun z : ℂ => 1 / max (|z.re| - 1) |z.im|)
      (realSegmentComplement (-1) 1) :=
    continuousOn_const.div
      (((continuous_re.abs.sub continuous_const).max continuous_im.abs).continuousOn)
      (fun z hz => (max_abs_re_sub_one_abs_im_pos hz).ne')
  refine TauCeti.isLocallyBoundedOn_def.mpr fun K hKΩ hK => ?_
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hβ.mono hKΩ)
  exact ⟨C, fun n z hz => (convergent_bound (hKΩ hz) n).2.trans
    ((Real.le_norm_self _).trans (hC z hz))⟩

/-- On the positive exterior real axis the logarithmic fraction is the minimal Legendre solution. -/
theorem tendsto_convergent_ofReal {x : ℝ} (hx : 1 < x) :
    Tendsto (fun n => convergent n x) atTop (𝓝 (logarithm x)) := by
  let w := DLMF.Legendre.ContinuedFraction.backwardQ 0 0 x
  have hxs : (x : ℂ) - 1 ∈ slitPlane := Or.inl (by simp; linarith)
  have hnum (k : ℕ) : DLMF.Legendre.legendreQCFNum 0 0 (k + 1) = numerator (k + 1) := by
    simp only [DLMF.Legendre.legendreQCFNum, numerator, Nat.add_one_ne_zero,
      ↓reduceIte, zero_add, sub_zero]
    ring
  have hrec (k : ℕ) : w k = denominator x k * w (k + 1) +
      numerator (k + 1) * w (k + 2) := by
    have h := DLMF.Legendre.ContinuedFraction.backwardQ_recurrence 0 0 hx k
    rw [hnum] at h
    simpa [w, denominator, DLMF.Legendre.legendreQCFDen] using h
  have hw1 : w 1 = DLMF.Legendre.legendreQ 0 x := by
    have h := DLMF.Legendre.olverQ_nat_zero_order 0 (z := (x : ℂ))
    simpa [w, DLMF.Legendre.ContinuedFraction.backwardQ] using h
  have hw2 : w 2 = DLMF.Legendre.legendreQ 1 x := by
    have h := DLMF.Legendre.olverQ_nat_zero_order 1 (z := (x : ℂ))
    norm_num [w, DLMF.Legendre.ContinuedFraction.backwardQ]
    simpa using h
  have hw0 : w 0 = 1 := by
    have h := hrec 0
    rw [hw1, hw2, DLMF.Legendre.legendreQ_one hxs] at h
    norm_num [denominator, numerator] at h
    linear_combination h
  have ha : ∀ k, numerator k ≠ 0 := by
    intro k
    by_cases hk : k = 0
    · simp [numerator, hk]
    · simp only [numerator, hk, ↓reduceIte, neg_ne_zero, ne_eq, pow_eq_zero_iff,
        OfNat.ofNat_ne_zero, not_false_eq_true]
      exact_mod_cast hk
  obtain ⟨hlim, hne⟩ := DLMF.Legendre.ContinuedFraction.backwardQ_ratio 0 0 hx
  have hlim' : Tendsto (fun k => -(w k / (numerator (k + 1) * w (k + 2)))) atTop
      (𝓝 ((DLMF.Legendre.FourierHypergeometric.invJoukowski x ^ 2)⁻¹)) := by
    simp_rw [hnum] at hlim
    exact hlim
  have hρ : 1 < ‖(DLMF.Legendre.FourierHypergeometric.invJoukowski x ^ 2)⁻¹‖ := by
    rw [norm_inv, norm_pow]
    have hζ0 := DLMF.Legendre.FourierHypergeometric.invJoukowski_ne_zero hxs
    have hζ1 := DLMF.Legendre.FourierHypergeometric.norm_invJoukowski_lt_one hxs
    rw [one_lt_inv₀ (by positivity)]
    nlinarith [norm_pos_iff.mpr hζ0]
  have h := tendsto_ofFun_convs_of_tendsto_ratio (h := 0) hrec (by rw [hw0]; norm_num)
    ha hne hρ hlim'
  simpa [convergent, hw0, hw1, numerator, logarithm, DLMF.Legendre.legendreQ_zero hxs] using h

/-- The Jacobi fraction converges to the principal logarithmic transform off `[-1,1]`. -/
theorem tendsto_convergent {z : ℂ} (hz : z ∈ realSegmentComplement (-1) 1) :
    Tendsto (fun n => convergent n z) atTop (𝓝 (logarithm z)) := by
  let Ω := realSegmentComplement (-1) 1
  have hΩ : IsOpen Ω := isOpen_realSegmentComplement _ _
  have hpre : IsPreconnected Ω := isPreconnected_realSegmentComplement _ _
  let A : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Ioi 1
  have hAΩ : A ⊆ Ω := by
    rintro _ ⟨t, ht, rfl⟩
    exact Or.inr (Or.inr (by simpa using ht))
  have htend : Tendsto (fun n : ℕ => (((2 : ℝ) + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop
      (𝓝[≠] (2 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (2 : ℝ)
      simp only [add_zero] at h
      simpa [Function.comp_def] using (continuous_ofReal.tendsto 2).comp h
    · simp only [mem_compl_iff, mem_singleton_iff]
      have hn : (2 : ℝ) + 1 / ((n : ℝ) + 1) ≠ 2 := by
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      exact_mod_cast hn
  have hmem : ∀ n : ℕ, (((2 : ℝ) + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) ∈ A := by
    intro n
    refine ⟨(2 : ℝ) + 1 / ((n : ℝ) + 1), ?_, rfl⟩
    change 1 < (2 : ℝ) + 1 / ((n : ℝ) + 1)
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hacc : AccPt (2 : ℂ) (𝓟 A) :=
    accPt_iff_frequently_nhdsNE.mpr (htend.frequently (Frequently.of_forall hmem))
  have htwo : (2 : ℂ) ∈ Ω := Or.inr (Or.inr (by norm_num))
  obtain ⟨g, hg, hgA, hconv⟩ := TauCeti.vitali_of_tendsto hΩ hpre
    differentiableOn_convergent isLocallyBoundedOn_convergent hAΩ htwo hacc
    (g := logarithm) (by
      rintro _ ⟨t, ht, rfl⟩
      exact tendsto_convergent_ofReal ht)
  have hEq : EqOn g logarithm Ω :=
    (hg.analyticOnNhd hΩ).eqOn_of_preconnected_of_frequently_eq
      (differentiableOn_logarithm.analyticOnNhd hΩ) hpre htwo
      (htend.frequently (Frequently.of_forall fun n => hgA (hmem n)))
  rw [← hEq hz]
  exact hconv.tendsto_at hz

/-- The transformed logarithmic Jacobi convergents converge to principal `arctanh`. -/
theorem tendsto_arctanh {z : ℂ} (hz0 : z ≠ 0)
    (hz : z.im ≠ 0 ∨ |z.re| < 1) :
    Tendsto (ofFun 0 (fun k => if k = 0 then z else -(k : ℂ) ^ 2 * z ^ 2)
      (fun k => (2 * k + 1 : ℂ))).convs atTop (𝓝 (arctanh z)) := by
  have h := tendsto_convergent (inv_mem_realSegmentComplement hz0 hz)
  have heq (n : ℕ) :
      (ofFun 0 (fun k => if k = 0 then z else -(k : ℂ) ^ 2 * z ^ 2)
        (fun k => (2 * k + 1 : ℂ))).convs n = convergent n z⁻¹ := by
    have he := ofFun_convs_equiv (h := (0 : ℂ)) (a := numerator) (b := denominator z⁻¹)
      (fun _ => z) (fun _ => hz0) n
    convert he using 2
    · congr 1
      · funext k
        by_cases hk : k = 0 <;> simp [numerator, hk]
        ring
      · funext k
        dsimp [denominator]
        field_simp
    · rfl
  have heLog : logarithm z⁻¹ = arctanh z := by
    rw [logarithm, arctanh]
    have he : (z⁻¹ + 1) / (z⁻¹ - 1) = (1 + z) / (1 - z) := by
      field_simp
    rw [he]
    ring
  simpa only [← heq, heLog] using h

/-- The principal inverse hyperbolic tangent has its Jacobi continued fraction. -/
theorem hasContinuedFraction_arctanh {z : ℂ} (hz : z.im ≠ 0 ∨ |z.re| < 1) :
    DLMF.Core.HasContinuedFraction
      (fun k => if k = 0 then z else -(k : ℂ) ^ 2 * z ^ 2)
      (fun k => (2 * k + 1 : ℂ)) (arctanh z) := by
  by_cases hz0 : z = 0
  · subst z
    unfold DLMF.Core.HasContinuedFraction
    have he (n : ℕ) : DLMF.Core.continuedFractionTail
        (fun k => if k = 0 then (0 : ℂ) else -(k : ℂ) ^ 2 * 0 ^ 2)
        (fun k => (2 * k + 1 : ℂ)) 0 n = 0 := by
      cases n with
      | zero => simp [DLMF.Core.continuedFractionTail,
          DLMF.Core.continuedFractionContinuants]
      | succ n =>
        rw [DLMF.Confluent.IncompleteGammaFractions.continuedFractionTail_freeze
          (by norm_num) (by omega)]
        norm_num
    change Tendsto (fun n => _) atTop _
    simp_rw [he]
    simp [arctanh]
  · rw [DLMF.Confluent.IncompleteGammaFractions.hasContinuedFraction_iff]
    · exact tendsto_arctanh hz0 hz
    · intro k hk
      simp only [show k ≠ 0 by omega, ↓reduceIte, mul_ne_zero_iff, neg_ne_zero,
        pow_ne_zero_iff (by omega : 2 ≠ 0)]
      exact ⟨by exact_mod_cast (show k ≠ 0 by omega), hz0⟩

/-- Multiplying the leading numerator scales the inverse hyperbolic tangent fraction. -/
theorem hasContinuedFraction_scaled_arctanh (c : ℂ) {z : ℂ}
    (hz : z.im ≠ 0 ∨ |z.re| < 1) :
    DLMF.Core.HasContinuedFraction
      (fun k => if k = 0 then c * z else -(k : ℂ) ^ 2 * z ^ 2)
      (fun k => (2 * k + 1 : ℂ)) (c * arctanh z) := by
  by_cases hz0 : z = 0
  · subst z
    simpa [arctanh] using hasContinuedFraction_arctanh hz
  · rw [DLMF.Confluent.IncompleteGammaFractions.hasContinuedFraction_iff]
    · have h := (tendsto_arctanh hz0 hz).const_mul c
      have he (n : ℕ) := ofFun_convs_mul_first_num
        (a := fun k => if k = 0 then z else -(k : ℂ) ^ 2 * z ^ 2)
        (b := fun k => (2 * k + 1 : ℂ)) c n
      simp only [↓reduceIte] at he
      have heq : (fun k : ℕ => if k = 0 then c * z
          else if k = 0 then z else -(k : ℂ) ^ 2 * z ^ 2) =
          (fun k : ℕ => if k = 0 then c * z else -(k : ℂ) ^ 2 * z ^ 2) := by
        funext k
        by_cases hk : k = 0 <;> simp [hk]
      simp only [heq] at he
      simpa only [← he] using h
    · intro k hk
      simp only [show k ≠ 0 by omega, ↓reduceIte, mul_ne_zero_iff, neg_ne_zero,
        pow_ne_zero_iff (by omega : 2 ≠ 0)]
      exact ⟨by exact_mod_cast (show k ≠ 0 by omega), hz0⟩

/-- The odd logarithm fraction on the principal two-ray slit domain. -/
theorem hasContinuedFraction_log_ratio {z : ℂ} (hz : z.im ≠ 0 ∨ |z.re| < 1) :
    DLMF.Core.HasContinuedFraction
      (fun k => if k = 0 then 2 * z else -(k : ℂ) ^ 2 * z ^ 2)
      (fun k => (2 * k + 1 : ℂ)) (Complex.log ((1 + z) / (1 - z))) := by
  convert hasContinuedFraction_scaled_arctanh 2 hz using 1
  rw [arctanh]
  ring

/-- Rotation of the logarithmic fraction gives the principal inverse tangent fraction. -/
theorem hasContinuedFraction_arctan {z : ℂ} (hz : z.re ≠ 0 ∨ |z.im| < 1) :
    DLMF.Core.HasContinuedFraction
      (fun k => if k = 0 then z else (k : ℂ) ^ 2 * z ^ 2)
      (fun k => (2 * k + 1 : ℂ)) (Complex.arctan z) := by
  have hdom : (I * z).im ≠ 0 ∨ |(I * z).re| < 1 := by simpa using hz
  have h := hasContinuedFraction_scaled_arctanh (-I) hdom
  have ha : -I * arctanh (I * z) = Complex.arctan z := by
    rw [arctanh, Complex.arctan, mul_comm I z]
    ring
  have hnum : (fun k : ℕ => if k = 0 then -I * (I * z)
      else -(k : ℂ) ^ 2 * (I * z) ^ 2) =
      (fun k : ℕ => if k = 0 then z else (k : ℂ) ^ 2 * z ^ 2) := by
    funext k
    by_cases hk : k = 0 <;> simp [hk, mul_pow, ← mul_assoc]
  simpa only [hnum, ha] using h

end DLMF.Elementary.LogarithmContinuedFraction
