/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Symmetric
public import DLMF.EllipticIntegrals.SymmetricDerivatives
public import Carlson.Elliptic.Asymptotic
public import Carlson.Mean.Real
public import Dirichlet.Average.Merge
public import Dirichlet.Average.TwoNode
public import Carlson.R.IntegralExercises
import DLMFMathlib.Analysis.Integral.ReciprocalSquareRootProducts
import DLMF.EllipticIntegrals.LegendreSymmetricForms
import TauCeti.Analysis.SpecialFunctions.Beta
import DLMF.EllipticIntegrals.SymmetricRelations
import DLMF.Hypergeometric.BetaIntegrals

/-!
# Integrals of elliptic integrals (DLMF §19.28)

Mellin transforms on `(0, 1)` of the complete integrals `R_F(0, t, 1)`, `R_G(0, t, 1)`,
`R_D(0, t, 1)` and of the two-variable `R_{-a}(b₁, b₂; t, 1)`, with `B` Mathlib's
`Complex.betaIntegral`; and integrals of `R_D`, `R_J`, `R_F` over one of their variables.

## Main results

* `integral_cpow_mul_symmetricEllipticRF_zero`, `integral_cpow_mul_symmetricEllipticRG_zero`,
  `integral_cpow_mul_symmetricEllipticRD_zero`, `integral_cpow_mul_symmetricEllipticR_two`: the
  Mellin transforms (DLMF 19.28.1–19.28.4).
* `integral_Ioi_symmetricEllipticRD`: `∫_z^∞ R_D(x, y, t) dt = 6 R_F(x, y, z)` (DLMF 19.28.5).
* `integral_symmetricEllipticRD_interp`: `R_J` as an integral of `R_D` (DLMF 19.28.6).
* `integral_symmetricEllipticRJ_sq`, `integral_symmetricEllipticRJ_scale`: DLMF 19.28.7, 19.28.8.
* `integral_symmetricEllipticRF_sin_cos`: DLMF 19.28.9, with the added hypothesis `x + y ≤ π/2`.
* `integral_symmetricEllipticRF_cosh`: DLMF 19.28.10.

## Implementation notes

All functions are DLMF's (`DLMF.EllipticIntegrals.symmetricEllipticRF` etc.). The integrals are
Lebesgue integrals; each left side is absolutely convergent under the stated hypotheses (the
integrands have at worst logarithmic or integrable power singularities), so the Lean statements
carry DLMF's meaning. The standing assumptions `ℜσ > 0` and `x, y, z, p > 0` (19.28.p1,
19.28.p2) are carried as hypotheses; 19.28.p3 points to (19.16.24) and to Carlson (1963, (7.9))
with no further formula.

**Correction.** DLMF states (19.28.5)–(19.28.9) under "x, y, z, p real and positive". For
(19.28.9), where `x` and `y` are angles, this is not sufficient: numerically (mpmath) the
identity holds for `x, y > 0` with `x + y ≤ π/2` and fails beyond, e.g. at `x = 2, y = 1.3`
the two sides are `2.6343` and `6.3569`, and at `x = y = 0.8` they differ by `0.0918`. The
statement here adds the hypothesis `x + y ≤ π/2`.

**Proofs.** The Mellin identities use the endpoint beta integral
`DLMF.Hypergeometric.integral_cpow_mul_ordinaryHypergeometric`, which cancels a parameter in
`Carlson.TwoVariable.betaIntegral_mul_threeFTwo` and applies Gauss summation. The `R_D` case
then follows from the algebraic `R_F` and `R_G` relation.

The integral (19.28.5) follows from the node derivative of `R_F`, Mathlib's improper
fundamental theorem for a nonpositive derivative, and the Carlson asymptotic
`Carlson.isEquivalent_carlsonRF_atTop`. Positivity and real-valuedness of `R_D` use
`Carlson.ofReal_carlsonRReal` and `Carlson.carlsonRReal_pos`. The interpolation identity
(19.28.6) uses the positive-parameter merging formula
`Dirichlet.regCarlsonDirichletAverage_ofReal_eq_merge` from `lean-codes`, followed by the
change of variable `u = v²` (`Carlson.integral_Ioo_sq_eq`).

The integration in the square of the last `R_J` node uses Fubini,
`TauCeti.integral_rpow_div_sq_add_sq`, and the reciprocal square-root kernel substitution.
The simultaneous scaling of two `R_J` nodes uses Fubini and a positive linear scaling of
the square-root kernel.

## References

* NIST DLMF §19.28.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-- DLMF 19.28.4: for real `a`, `b₁`, `b₂` with `c = b₁ + b₂ > 0` and `ℜσ > max(0, a - b₂)`,
`∫₀¹ t^{σ-1} (1 - t)^{c-1} R_{-a}(b₁, b₂; t, 1) dt =
Γ(c) Γ(σ) Γ(σ + b₂ - a) / (Γ(σ + c - a) Γ(σ + b₂))`. Here `R_{-a}` is DLMF's
`symmetricEllipticR a` (on `t ∈ (0, 1)` Carlson's `R`-function). -/
@[dlmf 19.28.E4]
theorem integral_cpow_mul_symmetricEllipticR_two {a b₁ b₂ : ℝ} {σ : ℂ} (hc : 0 < b₁ + b₂)
    (hσ : max 0 (a - b₂) < σ.re) :
    ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (σ - 1) * ((1 - t : ℝ) : ℂ) ^ ((b₁ + b₂ : ℝ) - 1 : ℂ) *
        symmetricEllipticR a ![(b₁ : ℂ), b₂] ![(t : ℂ), 1] =
      Gamma (b₁ + b₂ : ℝ) * Gamma σ * Gamma (σ + b₂ - a) /
        (Gamma (σ + (b₁ + b₂ : ℝ) - a) * Gamma (σ + b₂)) := by
  let F : ℝ → ℂ := fun t => (t : ℂ) ^ (σ - 1) *
    ((1 - t : ℝ) : ℂ) ^ ((b₁ + b₂ : ℝ) - 1 : ℂ) *
      symmetricEllipticR a ![(b₁ : ℂ), b₂] ![(t : ℂ), 1]
  have hrefl := intervalIntegral.integral_comp_sub_left F (a := 0) (b := 1) 1
  norm_num only [sub_self, sub_zero] at hrefl
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at hrefl
  rw [← hrefl]
  have hσ0 : 0 < σ.re := lt_of_le_of_lt (le_max_left 0 (a - b₂)) hσ
  have hσb : a - b₂ < σ.re := lt_of_le_of_lt (le_max_right 0 (a - b₂)) hσ
  have hreg : ∀ n : ℕ, (b₁ : ℂ) + b₂ ≠ -n := by
    intro n he
    have := congrArg Complex.re he
    simp only [add_re, ofReal_re, neg_re, natCast_re] at this
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have heq : ∀ u ∈ Ioo (0 : ℝ) 1, F (1 - u) =
      (u : ℂ) ^ (((b₁ + b₂ : ℝ) : ℂ) - 1) * (1 - (u : ℂ)) ^ (σ - 1) *
        ordinaryHypergeometric (a : ℂ) b₁ ((b₁ + b₂ : ℝ) : ℂ) (u : ℂ) := by
    intro u hu
    have hu0 : 0 < u := hu.1
    have hu1 : 0 < 1 - u := sub_pos.mpr hu.2
    dsimp only [F]
    have harg : arg (((1 - u : ℝ) : ℂ)) - arg (1 : ℂ) ∈ Ioo (-π) π := by
      rw [arg_one, arg_ofReal_of_nonneg hu1.le, sub_self]
      exact ⟨by have := Real.pi_pos; linarith, Real.pi_pos⟩
    rw [symmetricEllipticR_two_eq_ordinaryHypergeometric a b₁ b₂ hreg
      (ofReal_mem_slitPlane.mpr hu1) one_mem_slitPlane (by
        have hsub : (1 : ℂ) - ((1 - u : ℝ) : ℂ) = (u : ℂ) := by push_cast; ring
        rw [div_one, hsub, norm_real, Real.norm_of_nonneg hu0.le]
        exact hu.2) harg]
    push_cast
    simp only [one_cpow, one_mul, div_one]
    rw [show (1 : ℂ) - (1 - u) = u by ring]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioo heq]
  rw [DLMF.Hypergeometric.integral_cpow_mul_ordinaryHypergeometric
    (by simpa only [ofReal_re] using hc) hσ0 (by
      simp only [sub_re, add_re, ofReal_re]
      linarith)]
  congr 2 <;> push_cast <;> ring_nf


/-- DLMF 19.28.1: `∫₀¹ t^{σ-1} R_F(0, t, 1) dt = (1/2) B(σ, 1/2)²`, `ℜσ > 0`. -/
@[dlmf 19.28.E1]
theorem integral_cpow_mul_symmetricEllipticRF_zero {σ : ℂ} (hσ : 0 < σ.re) :
    ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (σ - 1) * symmetricEllipticRF 0 t 1 =
      1 / 2 * betaIntegral σ (1 / 2) ^ 2 := by
  have H := integral_cpow_mul_symmetricEllipticR_two
    (a := 1 / 2) (b₁ := 1 / 2) (b₂ := 1 / 2) (σ := σ)
    (by norm_num) (by simpa using hσ)
  have hR : (∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (σ - 1) *
      symmetricEllipticR (1 / 2) ![1 / 2, 1 / 2] ![(t : ℂ), 1]) =
      Gamma σ ^ 2 / Gamma (σ + 1 / 2) ^ 2 := by
    convert H using 1 <;> norm_num; ring_nf
  calc
    _ = (π / 2) * ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (σ - 1) *
        symmetricEllipticR (1 / 2) ![1 / 2, 1 / 2] ![(t : ℂ), 1] := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
      rw [symmetricEllipticRF_zero_left (ofReal_mem_slitPlane.mpr ht.1) one_mem_slitPlane]
      ring
    _ = _ := by
      rw [hR, betaIntegral_eq_Gamma_mul_div σ (1 / 2) hσ (by norm_num),
        div_pow, mul_pow, pow_two (Gamma (1 / 2)), Gamma_one_half_mul_self]
      ring

/-- DLMF 19.28.2: `∫₀¹ t^{σ-1} R_G(0, t, 1) dt = σ/(4σ + 2) B(σ, 1/2)²`, `ℜσ > 0`. -/
@[dlmf 19.28.E2]
theorem integral_cpow_mul_symmetricEllipticRG_zero {σ : ℂ} (hσ : 0 < σ.re) :
    ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (σ - 1) * symmetricEllipticRG 0 t 1 =
      σ / (4 * σ + 2) * betaIntegral σ (1 / 2) ^ 2 := by
  have H := integral_cpow_mul_symmetricEllipticR_two
    (a := -1 / 2) (b₁ := 1 / 2) (b₂ := 1 / 2) (σ := σ)
    (by norm_num) (lt_of_le_of_lt (by norm_num) hσ)
  have hR : (∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (σ - 1) *
      symmetricEllipticR (-1 / 2) ![1 / 2, 1 / 2] ![(t : ℂ), 1]) =
      Gamma σ * Gamma (σ + 1) / (Gamma (σ + 3 / 2) * Gamma (σ + 1 / 2)) := by
    convert H using 1 <;> norm_num; ring_nf
  calc
    _ = (π / 4) * ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (σ - 1) *
        symmetricEllipticR (-1 / 2) ![1 / 2, 1 / 2] ![(t : ℂ), 1] := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
      rw [(symmetricEllipticRG_zero_left (ofReal_mem_slitPlane.mpr ht.1) one_mem_slitPlane).1]
      ring
    _ = _ := by
      have hσ0 : σ ≠ 0 := ne_of_apply_ne Complex.re (ne_of_gt hσ)
      have hh : 0 < (σ + 1 / 2).re := by norm_num; linarith [hσ]
      have hh0 : σ + 1 / 2 ≠ 0 := ne_of_apply_ne Complex.re (ne_of_gt hh)
      have h4 : 4 * σ + 2 ≠ 0 := by
        intro he
        have := congrArg Complex.re he
        norm_num [mul_re] at this
        linarith
      rw [hR, betaIntegral_eq_Gamma_mul_div σ (1 / 2) hσ (by norm_num),
        div_pow, mul_pow, pow_two (Gamma (1 / 2)), Gamma_one_half_mul_self,
        show σ + 3 / 2 = (σ + 1 / 2) + 1 by ring,
        Gamma_add_one _ hσ0, Gamma_add_one _ hh0]
      generalize heq : Gamma (σ + 1 / 2) = G
      have hG : G ≠ 0 := by rw [← heq]; exact Gamma_ne_zero_of_re_pos hh
      have h2 : 1 + σ * 2 ≠ 0 := by
        intro he
        apply h4
        linear_combination 2 * he
      field_simp [hh0, h4, hG]
      ring_nf
      field_simp [h2]
      ring

/-- DLMF 19.28.3: `∫₀¹ t^{σ-1} (1 - t) R_D(0, t, 1) dt = 3/(4σ + 2) B(σ, 1/2)²`, `ℜσ > 0`. -/
@[dlmf 19.28.E3]
theorem integral_cpow_mul_symmetricEllipticRD_zero {σ : ℂ} (hσ : 0 < σ.re) :
    ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (σ - 1) * (1 - t) * symmetricEllipticRD 0 t 1 =
      3 / (4 * σ + 2) * betaIntegral σ (1 / 2) ^ 2 := by
  have hF := integral_cpow_mul_symmetricEllipticRF_zero hσ
  have hG := integral_cpow_mul_symmetricEllipticRG_zero hσ
  have hσ0 : σ ≠ 0 := ne_of_apply_ne Complex.re (ne_of_gt hσ)
  have hh : 0 < (σ + 1 / 2).re := by norm_num; linarith [hσ]
  have h4 : 4 * σ + 2 ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    norm_num [mul_re] at this
    linarith [hσ]
  have hB : betaIntegral σ (1 / 2) ≠ 0 := by
    rw [betaIntegral_eq_Gamma_mul_div σ (1 / 2) hσ (by norm_num)]
    exact div_ne_zero (mul_ne_zero (Gamma_ne_zero_of_re_pos hσ)
      (Gamma_ne_zero_of_re_pos (by norm_num))) (Gamma_ne_zero_of_re_pos hh)
  have hiF : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (σ - 1) * symmetricEllipticRF 0 t 1)
      (Ioo 0 1) := by
    apply Integrable.of_integral_ne_zero
    rw [hF]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hB)
  have hiG : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (σ - 1) * symmetricEllipticRG 0 t 1)
      (Ioo 0 1) := by
    apply Integrable.of_integral_ne_zero
    rw [hG]
    exact mul_ne_zero (div_ne_zero hσ0 h4) (pow_ne_zero 2 hB)
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1,
      (t : ℂ) ^ (σ - 1) * (1 - t) * symmetricEllipticRD 0 t 1 =
      3 * ((t : ℂ) ^ (σ - 1) * symmetricEllipticRF 0 t 1) -
        6 * ((t : ℂ) ^ (σ - 1) * symmetricEllipticRG 0 t 1) := by
    intro t ht
    have h := two_mul_symmetricEllipticRG (Or.inr (rfl : (0 : ℂ) = 0))
      (ofReal_mem_slitPlane.mpr ht.1) one_mem_slitPlane
    norm_num only [one_mul, sub_zero, zero_sub, zero_cpow (by norm_num : (1 / 2 : ℂ) ≠ 0),
      zero_mul, add_zero] at h
    linear_combination (3 * (t : ℂ) ^ (σ - 1)) * h
  rw [setIntegral_congr_fun measurableSet_Ioo hpt,
    integral_sub (hiF.const_mul 3) (hiG.const_mul 6), integral_const_mul,
    integral_const_mul, hF, hG]
  have h4' : 2 + σ * 4 ≠ 0 := by rw [add_comm, mul_comm]; exact h4
  field_simp [h4]
  ring_nf
  field_simp [h4']
  ring


/-- For positive real nodes, `R_D` is real and nonnegative, as a positive Carlson average. -/
lemma symmetricEllipticRD_real_nonneg {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    symmetricEllipticRD x y z = ((symmetricEllipticRD x y z).re : ℂ) ∧ 0 ≤
        (symmetricEllipticRD x y z).re := by
  have hb : (![1 / 2, 1 / 2, 3 / 2] : Fin 3 → ℝ) ∈ ProbabilityTheory.mvRealBetaDomain := by
    intro i; fin_cases i <;> norm_num
  have hv : ∀ i : Fin 3, 0 < (![x, y, z] : Fin 3 → ℝ) i := by
    intro i; fin_cases i <;> assumption
  have H := Carlson.ofReal_carlsonRReal (-3 / 2) hb hv
  have hnodes : (fun i => ((![x, y, z] : Fin 3 → ℝ) i : ℂ)) = ![(x : ℂ), y, z] := by
    funext i; fin_cases i <;> rfl
  have hparams : (fun i => ((![1 / 2, 1 / 2, 3 / 2] : Fin 3 → ℝ) i : ℂ)) =
      ![1 / 2, 1 / 2, 3 / 2] := by funext i; fin_cases i <;> norm_num
  rw [hnodes, hparams] at H
  rw [symmetricEllipticRD_eq_symmetricEllipticR (ofReal_mem_slitPlane.mpr hx)
      (ofReal_mem_slitPlane.mpr hy)
    (ofReal_mem_slitPlane.mpr hz), symmetricEllipticR_of_mem _ _
      (vec3_mem_carlsonRSlitDomain (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy)
        (ofReal_mem_slitPlane.mpr hz)), show (-(3 / 2) : ℂ) = ((-3 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← H]
  simp only [ofReal_re]
  exact ⟨trivial, (Carlson.carlsonRReal_pos (-3 / 2) hb hv).le⟩

/-- With fixed positive first two nodes, the Carlson asymptotic formula implies `R_F → 0`. -/
lemma tendsto_symmetricEllipticRF_atTop {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun t : ℝ => symmetricEllipticRF x y t) atTop (𝓝 0) := by
  let c := 4 / (Real.sqrt x + Real.sqrt y)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hlog : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have H := (hlog.comp (Real.tendsto_sqrt_atTop.const_mul_atTop hc)).const_mul c
  simp only [mul_zero] at H
  have H' : Tendsto (fun t : ℝ => Real.log (4 * Real.sqrt t / (Real.sqrt x + Real.sqrt y)) /
      Real.sqrt t) atTop (𝓝 0) := by
    apply H.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    dsimp only [Function.comp_def, c]
    field_simp [(Real.sqrt_pos.mpr ht).ne']
  have HC := (continuous_ofReal.tendsto (0 : ℝ)).comp H'
  simp only [ofReal_zero, Function.comp_def] at HC
  have Hrf := (Carlson.isEquivalent_carlsonRF_atTop hx hy).symm.tendsto_nhds HC
  apply Hrf.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (symmetricEllipticRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr hx)
    (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr ht)).symm

/-- DLMF 19.28.5: `∫_z^∞ R_D(x, y, t) dt = 6 R_F(x, y, z)` for `x, y, z > 0`. -/
@[dlmf 19.28.E5]
theorem integral_Ioi_symmetricEllipticRD {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ∫ t in Ioi z, symmetricEllipticRD x y t = 6 * symmetricEllipticRF x y z := by
  have hderiv : ∀ t ∈ Ici z, HasDerivAt (fun s : ℝ => (symmetricEllipticRF x y s).re)
      (-(1 / 6) * (symmetricEllipticRD x y t).re) t := by
    intro t ht
    have H := (hasDerivAt_symmetricEllipticRF_right (ofReal_mem_slitPlane.mpr hx)
      (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr (hz.trans_le ht))).real_of_complex
    convert H using 1
    simp [mul_re]
  have hnonpos : ∀ t ∈ Ioi z, -(1 / 6) * (symmetricEllipticRD x y t).re ≤ 0 := by
    intro t ht
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
        (symmetricEllipticRD_real_nonneg hx hy (hz.trans ht)).2
  have hlim := (Complex.continuous_re.tendsto (0 : ℂ)).comp
      (tendsto_symmetricEllipticRF_atTop hx hy)
  simp only [zero_re, Function.comp_def] at hlim
  have H := integral_Ioi_of_hasDerivAt_of_nonpos' hderiv hnonpos hlim
  rw [integral_const_mul, zero_sub] at H
  have H' : ∫ t in Ioi z, (symmetricEllipticRD x y t).re = 6 * (symmetricEllipticRF x y z).re := by
    linarith
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => (symmetricEllipticRD_real_nonneg hx hy (hz.trans ht)).1),
    integral_complex_ofReal, H', ofReal_mul, ofReal_ofNat]
  congr 1
  apply Complex.ext
  · simp
  · rw [ofReal_im, symmetricEllipticRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr hx)
      (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hz),
      Carlson.carlsonRF_ofReal_eq_integral hx hy hz, ofReal_im]

/-- DLMF 19.28.6: `∫₀¹ R_D(x, y, v² z + (1 - v²) p) dv = R_J(x, y, z, p)` for
`x, y, z, p > 0`. -/
@[dlmf 19.28.E6]
theorem integral_symmetricEllipticRD_interp {x y z p : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hp : 0 < p) :
    ∫ v in Ioo (0 : ℝ) 1, symmetricEllipticRD x y (v ^ 2 * z + (1 - v ^ 2) * p : ℝ) =
      symmetricEllipticRJ x y z p := by
  let b : Fin 4 → ℝ := ![1 / 2, 1 / 2, 1 / 2, 1]
  let Z : Fin 4 → ℂ := ![(x : ℂ), y, z, p]
  have hb : b ∈ ProbabilityTheory.mvRealBetaDomain := by intro i; fin_cases i <;> norm_num [b]
  have hZ : Z ∈ Carlson.carlsonRVariableDomain := by intro i; fin_cases i <;> assumption
  have hcont : ContinuousOn (fun u => Dirichlet.carlsonAffineForm Z u ^ (-(3 / 2) : ℂ))
      (Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) := by
    exact (Dirichlet.continuous_carlsonAffineForm Z).continuousOn.cpow continuousOn_const
      (fun u hu => Or.inl (Carlson.carlsonAffineForm_mem_rightHalfPlane hZ hu))
  have H := Dirichlet.regCarlsonDirichletAverage_ofReal_eq_merge
    (a := (2 : Fin 4)) (a' := 3) (f := fun v : ℂ => v ^ (-(3 / 2) : ℂ)) (by decide) hb Z hcont
  have hbc : (fun i => (b i : ℂ)) = (![1 / 2, 1 / 2, 1 / 2, 1] : Fin 4 → ℂ) := by
    funext i; fin_cases i <;> norm_num [b]
  rw [hbc, Dirichlet.regCarlsonDirichletAverage_fin_two, Dirichlet.regEulerIntegral] at H
  simp only [Dirichlet.pairParam, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_self, cpow_zero, mul_one, Gamma_one] at H
  norm_num [b] at H
  let e : Fin 3 ≃ {i : Fin 4 // i ≠ 3} := finSuccAboveEquiv (Fin.last 3)
  have hecoe (i : Fin 3) : (e i : Fin 4) = i.castSucc := by
    change (Fin.last 3).succAbove i = i.castSucc
    rw [Fin.succAbove_last]
  have hparams : (Dirichlet.mergeParam (2 : Fin 4) 3 ![1 / 2, 1 / 2, 1 / 2, 1]) ∘ e =
      (![1 / 2, 1 / 2, 3 / 2] : Fin 3 → ℂ) := by
    funext i
    simp only [Function.comp_apply, Dirichlet.mergeParam, hecoe]
    fin_cases i <;> norm_num
  have hnodes (w : ℂ) : (Dirichlet.mergeNodes (2 : Fin 4) 3 Z w) ∘ e = ![(x : ℂ), y, w] := by
    funext i
    simp only [Function.comp_apply, Dirichlet.mergeNodes, hecoe]
    fin_cases i <;> norm_num [Z]
  have hinner {w : ℂ} (hw : 0 < w.re) :
      Dirichlet.regCarlsonDirichletAverage
        (Dirichlet.mergeParam (2 : Fin 4) 3 ![1 / 2, 1 / 2, 1 / 2, 1])
        (Dirichlet.mergeNodes (2 : Fin 4) 3 Z w) (fun v => v ^ (-(3 / 2) : ℂ)) =
        symmetricEllipticRD x y w / Gamma (5 / 2) := by
    have hdom : Dirichlet.mergeNodes (2 : Fin 4) 3 Z w ∈ Carlson.carlsonRVariableDomain := by
      intro i
      have hi := e.surjective i
      obtain ⟨j, rfl⟩ := hi
      have he : Dirichlet.mergeNodes (2 : Fin 4) 3 Z w (e j) = ![(x : ℂ), y, w] j :=
          congrFun (hnodes w) j
      change 0 < (Dirichlet.mergeNodes (2 : Fin 4) 3 Z w (e j)).re
      rw [he]
      fin_cases j <;> assumption
    have heq := Carlson.regCarlsonR_comp_equiv e (-3 / 2)
      (Carlson.carlsonRVariableDomain_subset_slitDomain hdom)
      ((Dirichlet.mergeParam (2 : Fin 4) 3 ![1 / 2, 1 / 2, 1 / 2, 1]) ∘ e)
    simp only [Function.comp_def, Equiv.apply_symm_apply] at heq
    rw [show (-3 / 2 : ℂ) = -(3 / 2) by ring] at heq
    change Carlson.regCarlsonR (-(3 / 2))
      ((Dirichlet.mergeParam (2 : Fin 4) 3 ![1 / 2, 1 / 2, 1 / 2, 1]) ∘ e)
      ((Dirichlet.mergeNodes (2 : Fin 4) 3 Z w) ∘ e) =
      Carlson.regCarlsonR (-(3 / 2)) (Dirichlet.mergeParam (2 : Fin 4) 3 ![1 / 2, 1 / 2, 1 / 2, 1])
        (Dirichlet.mergeNodes (2 : Fin 4) 3 Z w) at heq
    rw [hnodes, hparams] at heq
    have hbeta : Dirichlet.mergeParam (2 : Fin 4) 3
        (![1 / 2, 1 / 2, 1 / 2, 1] : Fin 4 → ℂ) ∈ Complex.mvBetaConvergent := by
      intro i
      rcases i with ⟨i, hi⟩
      fin_cases i <;> norm_num [Dirichlet.mergeParam] at *
    rw [← Carlson.regCarlsonRIntegral, ← Carlson.regCarlsonR_eq_regCarlsonRIntegral _ hbeta
      hdom, ← heq, symmetricEllipticRD_eq_symmetricEllipticR (ofReal_mem_slitPlane.mpr hx)
      (ofReal_mem_slitPlane.mpr hy) (Or.inl hw), symmetricEllipticR_of_mem _ _
      (vec3_mem_carlsonRSlitDomain (ofReal_mem_slitPlane.mpr hx)
          (ofReal_mem_slitPlane.mpr hy) (Or.inl hw)),
      Carlson.carlsonR]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    norm_num
    apply (eq_div_iff (Gamma_ne_zero_of_re_pos (by norm_num : 0 < (5 / 2 : ℂ).re))).2
    ring
  have H' : symmetricEllipticRJ x y z p = (1 / 2) * ∫ u in Ioo (0 : ℝ) 1,
      (u : ℂ) ^ (-(1 / 2) : ℂ) * symmetricEllipticRD x y (u * z + (1 - u) * p : ℝ) := by
    rw [symmetricEllipticRJ_eq_symmetricEllipticR (ofReal_mem_slitPlane.mpr hx)
        (ofReal_mem_slitPlane.mpr hy)
      (ofReal_mem_slitPlane.mpr hz) (ofReal_mem_slitPlane.mpr hp), symmetricEllipticR_of_mem _ _
      (vec4_mem_carlsonRSlitDomain (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy)
        (ofReal_mem_slitPlane.mpr hz) (ofReal_mem_slitPlane.mpr hp)), Carlson.carlsonR,
      Carlson.regCarlsonR_eq_regCarlsonRIntegral _ (fun i => by fin_cases i <;> norm_num) hZ,
      Carlson.regCarlsonRIntegral, H]
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]
    norm_num
    simp_rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have hu0 := hu.1
    have hu1 := hu.2
    have hw : 0 < u * z + (1 - u) * p := by positivity
    have hwC : (u : ℂ) * Z 2 + (1 - u) * Z 3 = ((u * z + (1 - u) * p : ℝ) : ℂ) := by
      change (u : ℂ) * (z : ℂ) + (1 - u) * (p : ℂ) = _
      push_cast; ring
    rw [hwC, hinner (by exact hw)]
    rw [Gamma_five_halves_eq_mul, Carlson.Gamma_three_halves]
    push_cast
    field_simp
    have hcancel := mul_inv_cancel₀ Gamma_one_half_ne_zero
    linear_combination ((u : ℂ) ^ (-(1 / 2) : ℂ) *
      symmetricEllipticRD x y ((u : ℂ) * z + (1 - u) * p)) * hcancel
  rw [H']
  have HS := Carlson.integral_Ioo_sq_eq
    (fun u => (u : ℂ) ^ (-(1 / 2) : ℂ) * symmetricEllipticRD x y (u * z + (1 - u) * p : ℝ))
    (x := 0) (y := 1) le_rfl zero_lt_one
  norm_num only [zero_pow two_ne_zero, one_pow] at HS
  rw [HS, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  have hv0 : (v : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hv.1)
  have he : (((v ^ 2 : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) = (v : ℂ)⁻¹ := by
    rw [ofReal_pow, show (-(1 / 2) : ℂ) = -(2⁻¹) by norm_num, cpow_neg,
      sq_cpow_two_inv (by exact hv.1)]
  rw [he]
  push_cast
  field_simp


/-- DLMF 19.28.7: `∫₀^∞ R_J(x, y, z, r²) dr = (3/2) π R_F(xy, xz, yz)` for `x, y, z > 0`. -/
@[dlmf 19.28.E7]
theorem integral_symmetricEllipticRJ_sq {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ∫ r in Ioi (0 : ℝ), symmetricEllipticRJ x y z (r ^ 2 : ℝ) =
      3 / 2 * π * symmetricEllipticRF (x * y : ℝ) (x * z : ℝ) (y * z : ℝ) := by
  have quadratic_resolvent_halfline {t : ℝ} (ht : 0 < t) :
      (∫ r in Ioi (0 : ℝ), (t + r ^ 2)⁻¹) = π / (2 * Real.sqrt t) := by
    have hs := Real.sqrt_pos.mpr ht
    have h := TauCeti.integral_rpow_div_sq_add_sq (s := 1) (by norm_num) (by norm_num)
      (t := Real.sqrt t) hs.ne'
    norm_num [Real.sq_sqrt ht.le, abs_of_pos hs, Real.rpow_neg_one, add_comm] at h
    rw [h]
    ring

  have quadratic_resolvent_halfline_integrable {t : ℝ} (ht : 0 < t) :
      IntegrableOn (fun r : ℝ => (t + r ^ 2)⁻¹) (Ioi 0) := by
    have h := TauCeti.integrableOn_rpow_div_sq_add_sq (s := 1) (by norm_num) (by norm_num)
      (t := Real.sqrt t) (Real.sqrt_pos.mpr ht).ne'
    simpa only [sub_self, Real.rpow_zero, one_div, Real.sq_sqrt ht.le, add_comm] using h
  let f : ℝ × ℝ → ℝ := fun q =>
    (Real.sqrt (q.1 + x) * Real.sqrt (q.1 + y) * Real.sqrt (q.1 + z))⁻¹ *
      (q.1 + q.2 ^ 2)⁻¹
  let g : ℝ → ℝ := fun t => (Real.sqrt t * (Real.sqrt (t + x) *
    Real.sqrt (t + y) * Real.sqrt (t + z)))⁻¹
  have hinner (t : ℝ) (ht : 0 < t) : ∫ r in Ioi (0 : ℝ), f (t, r) = π / 2 * g t := by
    dsimp only [f, g]
    rw [integral_const_mul, quadratic_resolvent_halfline ht]
    ring
  have hf : Integrable f ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    refine (integrable_prod_iff ((by fun_prop : Measurable f).aestronglyMeasurable)).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      dsimp only [f]
      exact (quadratic_resolvent_halfline_integrable ht).const_mul _
    · refine ((Real.integrableOn_inv_sqrt_mul_sqrt_add_mul_sqrt_add_mul_sqrt_add
        hx hy hz).const_mul (π / 2)).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      rw [← hinner t ht]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      dsimp only
      rw [Real.norm_eq_abs, abs_of_nonneg]
      dsimp only [f]
      positivity
  have hf' : Integrable (Function.uncurry (fun t r : ℝ => f (t, r)))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    have heq : Function.uncurry (fun t r : ℝ => f (t, r)) = f := by
      funext q
      rcases q with ⟨t, r⟩
      rfl
    rw [heq]
    exact hf
  have hswap := integral_integral_swap hf'
  have hRJ (r : ℝ) (hr : 0 < r) :
      symmetricEllipticRJ x y z (r ^ 2 : ℝ) = ((3 / 2 * ∫ t in Ioi (0 : ℝ), f (t, r) : ℝ) : ℂ) := by
    have hp : ¬ IsNegReal ((r ^ 2 : ℝ) : ℂ) :=
      not_isNegReal_of_mem_slitPlane (ofReal_mem_slitPlane.mpr (sq_pos_of_pos hr))
    rw [symmetricEllipticRJ, ite_eq_right hp]
    conv_rhs => rw [ofReal_mul, ← integral_complex_ofReal]
    norm_num only [ofReal_div, ofReal_ofNat]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    simp only [f, carlsonRootProduct, ofReal_inv, ofReal_mul, ofReal_add, ofReal_pow,
      mul_inv]
    rw [
      ofReal_sqrt_eq_cpow_half (by linarith [ht0] : 0 ≤ t + x),
      ofReal_sqrt_eq_cpow_half (by linarith [ht0] : 0 ≤ t + y),
      ofReal_sqrt_eq_cpow_half (by linarith [ht0] : 0 ≤ t + z)]
    push_cast
    ring
  have hRF : symmetricEllipticRF (x * y : ℝ) (x * z : ℝ) (y * z : ℝ) =
      ((1 / 2 * ∫ u in Ioi (0 : ℝ), (Real.sqrt (u + x * y) * Real.sqrt (u + x * z) *
        Real.sqrt (u + y * z))⁻¹ : ℝ) : ℂ) := by
    rw [symmetricEllipticRF]
    conv_rhs => rw [ofReal_mul, ← integral_complex_ofReal]
    norm_num only [ofReal_div, ofReal_ofNat]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 < u := hu
    simp only [carlsonRootProduct, ofReal_inv, ofReal_mul]
    rw [ofReal_sqrt_eq_cpow_half (by positivity : 0 ≤ u + x * y),
      ofReal_sqrt_eq_cpow_half (by positivity : 0 ≤ u + x * z),
      ofReal_sqrt_eq_cpow_half (by positivity : 0 ≤ u + y * z)]
    push_cast
    rfl
  calc
    _ = ∫ r in Ioi (0 : ℝ), ((3 / 2 * ∫ t in Ioi (0 : ℝ), f (t, r) : ℝ) : ℂ) :=
      setIntegral_congr_fun measurableSet_Ioi hRJ
    _ = ((3 / 2 * ∫ r in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), f (t, r) : ℝ) : ℂ) := by
      rw [integral_complex_ofReal, integral_const_mul]
    _ = ((3 / 2 * (π / 2 * ∫ t in Ioi (0 : ℝ), g t) : ℝ) : ℂ) := by
      rw [hswap.symm]
      congr 2
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi hinner
    _ = _ := by
      dsimp only [g]
      rw [hRF, Real.integral_inv_sqrt_mul_sqrt_add_mul_sqrt_add_mul_sqrt_add hx hy hz]
      push_cast
      ring

/-- The positive-real defining integral of `R_C`, written with real square roots. -/
private lemma symmetricEllipticRC_ofReal_eq_half_integral {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    symmetricEllipticRC p x =
      ((1 / 2 * ∫ v in Ioi (0 : ℝ), (Real.sqrt (v + p) * (v + x))⁻¹ : ℝ) : ℂ) := by
  rw [symmetricEllipticRC,
    ite_eq_right (not_isNegReal_of_mem_slitPlane (ofReal_mem_slitPlane.mpr hx))]
  conv_rhs => rw [ofReal_mul, ← integral_complex_ofReal]
  norm_num only [ofReal_div, ofReal_ofNat]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hv0 : 0 < v := hv
  rw [ofReal_inv, ofReal_mul, ofReal_sqrt_eq_cpow_half (by positivity : 0 ≤ v + p)]
  push_cast
  rfl

/-- The positive-real defining integral of `R_F(0,y,z)`, written with real square roots. -/
private lemma symmetricEllipticRF_zero_ofReal_eq_half_integral {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    symmetricEllipticRF 0 y z = ((1 / 2 * ∫ u in Ioi (0 : ℝ),
      (Real.sqrt u * Real.sqrt (u + y) * Real.sqrt (u + z))⁻¹ : ℝ) : ℂ) := by
  rw [symmetricEllipticRF]
  conv_rhs => rw [ofReal_mul, ← integral_complex_ofReal]
  norm_num only [ofReal_div, ofReal_ofNat]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : 0 < u := hu
  simp only [carlsonRootProduct, ofReal_inv, ofReal_mul, add_zero]
  rw [ofReal_sqrt_eq_cpow_half hu.le, ofReal_sqrt_eq_cpow_half (by positivity : 0 ≤ u + y),
    ofReal_sqrt_eq_cpow_half (by positivity : 0 ≤ u + z)]
  push_cast
  rfl


/-- DLMF 19.28.8: `∫₀^∞ R_J(tx, y, z, tp) dt = (6/√p) R_C(p, x) R_F(0, y, z)` for
`x, y, z, p > 0`. -/
@[dlmf 19.28.E8]
theorem integral_symmetricEllipticRJ_scale {x y z p : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hp : 0 < p) :
    ∫ t in Ioi (0 : ℝ), symmetricEllipticRJ (t * x : ℝ) y z (t * p : ℝ) =
      6 / (√p : ℝ) * symmetricEllipticRC p x * symmetricEllipticRF 0 y z := by
  let f : ℝ × ℝ → ℝ := fun q =>
    (Real.sqrt (q.1 + y) * Real.sqrt (q.1 + z))⁻¹ *
      (Real.sqrt (q.1 + x * q.2) * (q.1 + p * q.2))⁻¹
  let g : ℝ → ℝ := fun u =>
    (Real.sqrt u * Real.sqrt (u + y) * Real.sqrt (u + z))⁻¹
  let c : ℝ := (Real.sqrt p)⁻¹ *
    ∫ v in Ioi (0 : ℝ), (Real.sqrt (v + p) * (v + x))⁻¹
  have hinner (u : ℝ) (hu : 0 < u) : ∫ t in Ioi (0 : ℝ), f (u, t) = c * g u := by
    dsimp only [f, g, c]
    rw [integral_const_mul, Real.integral_inv_sqrt_add_mul_add_linear hu hp hx]
    ring
  have hf : Integrable f ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    refine (integrable_prod_iff ((by fun_prop : Measurable f).aestronglyMeasurable)).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      dsimp only [f]
      exact (Real.integrableOn_inv_sqrt_add_mul_add_linear hu hp hx).const_mul _
    · refine ((Real.integrableOn_inv_sqrt_mul_sqrt_add_mul_sqrt_add hy hz).const_mul c).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := hu
      rw [← hinner u hu]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      rw [Real.norm_eq_abs, abs_of_nonneg]
      dsimp only [f]
      positivity
  have hf' : Integrable (Function.uncurry (fun u t : ℝ => f (u, t)))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    simpa only [Function.uncurry_def] using hf
  have hswap := integral_integral_swap hf'
  have hRJ (t : ℝ) (ht : 0 < t) :
      symmetricEllipticRJ (t * x : ℝ) y z (t * p : ℝ) =
        ((3 / 2 * ∫ u in Ioi (0 : ℝ), f (u, t) : ℝ) : ℂ) := by
    have htp : ¬ IsNegReal ((t * p : ℝ) : ℂ) :=
      not_isNegReal_of_mem_slitPlane (ofReal_mem_slitPlane.mpr (mul_pos ht hp))
    rw [symmetricEllipticRJ, ite_eq_right htp]
    conv_rhs => rw [ofReal_mul, ← integral_complex_ofReal]
    norm_num only [ofReal_div, ofReal_ofNat]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 < u := hu
    simp only [f, carlsonRootProduct, ofReal_inv, ofReal_mul]
    rw [ofReal_sqrt_eq_cpow_half (by positivity : 0 ≤ u + y),
      ofReal_sqrt_eq_cpow_half (by positivity : 0 ≤ u + z),
      ofReal_sqrt_eq_cpow_half (by positivity : 0 ≤ u + x * t)]
    push_cast
    simp only [mul_inv]
    ring_nf
  calc
    _ = ∫ t in Ioi (0 : ℝ), ((3 / 2 * ∫ u in Ioi (0 : ℝ), f (u, t) : ℝ) : ℂ) :=
      setIntegral_congr_fun measurableSet_Ioi hRJ
    _ = ((3 / 2 * ∫ t in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), f (u, t) : ℝ) : ℂ) := by
      rw [integral_complex_ofReal, integral_const_mul]
    _ = ((3 / 2 * (c * ∫ u in Ioi (0 : ℝ), g u) : ℝ) : ℂ) := by
      rw [hswap.symm]
      congr 2
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi hinner
    _ = _ := by
      rw [symmetricEllipticRC_ofReal_eq_half_integral hp hx,
        symmetricEllipticRF_zero_ofReal_eq_half_integral hy hz]
      dsimp only [c, g]
      push_cast
      ring

/-- DLMF 19.28.9, **with the added hypothesis `x + y ≤ π/2`** (see the module docstring; DLMF
assumes only `x, y > 0`, under which the identity is false):
`∫₀^{π/2} R_F(sin²θ cos²(x + y), sin²θ cos²(x - y), 1) dθ = R_F(0, cos²x, 1) R_F(0, cos²y, 1)`. -/
@[dlmf 19.28.E9]
theorem integral_symmetricEllipticRF_sin_cos {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y ≤ π / 2) :
    ∫ θ in Ioo (0 : ℝ) (π / 2),
        symmetricEllipticRF (Real.sin θ ^ 2 * Real.cos (x + y) ^ 2 : ℝ)
          (Real.sin θ ^ 2 * Real.cos (x - y) ^ 2 : ℝ) 1 =
      symmetricEllipticRF 0 (Real.cos x ^ 2 : ℝ) 1 *
          symmetricEllipticRF 0 (Real.cos y ^ 2 : ℝ) 1 := by
  sorry

/-- DLMF 19.28.10: for `a, b, c, d > 0`,
`∫₀^∞ R_F((ac + bd)², (ad + bc)², 4abcd cosh² z) dz = (1/2) R_F(0, a², b²) R_F(0, c², d²)`. -/
@[dlmf 19.28.E10]
theorem integral_symmetricEllipticRF_cosh {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) :
    ∫ z in Ioi (0 : ℝ),
        symmetricEllipticRF ((a * c + b * d) ^ 2 : ℝ) ((a * d + b * c) ^ 2 : ℝ)
          (4 * a * b * c * d * Real.cosh z ^ 2 : ℝ) =
      1 / 2 * symmetricEllipticRF 0 (a ^ 2 : ℝ) (b ^ 2 : ℝ) *
          symmetricEllipticRF 0 (c ^ 2 : ℝ) (d ^ 2 : ℝ) := by
  sorry

end DLMF.EllipticIntegrals
