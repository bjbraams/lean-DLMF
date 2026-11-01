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

/-!
# Integrals of elliptic integrals (DLMF §19.28)

Mellin transforms on `(0, 1)` of the complete integrals `R_F(0, t, 1)`, `R_G(0, t, 1)`,
`R_D(0, t, 1)` and of the two-variable `R_{-a}(b₁, b₂; t, 1)`, with `B` Mathlib's
`Complex.betaIntegral`; and integrals of `R_D`, `R_J`, `R_F` over one of their variables.

## Main results

* `integral_cpow_mul_symEllIntRF_zero`, `integral_cpow_mul_symEllIntRG_zero`,
  `integral_cpow_mul_symEllIntRD_zero`, `integral_cpow_mul_symEllIntR_two`: the Mellin
  transforms (DLMF 19.28.1–19.28.4).
* `integral_Ioi_symEllIntRD`: `∫_z^∞ R_D(x, y, t) dt = 6 R_F(x, y, z)` (DLMF 19.28.5).
* `integral_symEllIntRD_interp`: `R_J` as an integral of `R_D` (DLMF 19.28.6).
* `integral_symEllIntRJ_sq`, `integral_symEllIntRJ_scale`: DLMF 19.28.7, 19.28.8.
* `integral_symEllIntRF_sin_cos`: DLMF 19.28.9, with the added hypothesis `x + y ≤ π/2`.
* `integral_symEllIntRF_cosh`: DLMF 19.28.10.

## Implementation notes

All functions are DLMF's (`DLMF.EllipticIntegrals.symEllIntRF` etc.). The integrals are
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

**Proofs.** The integral (19.28.5) follows from the node derivative of `R_F`, Mathlib's improper
fundamental theorem for a nonpositive derivative, and the Carlson asymptotic
`Carlson.isEquivalent_carlsonRF_atTop`. Positivity and real-valuedness of `R_D` use
`Carlson.ofReal_carlsonRReal` and `Carlson.carlsonRReal_pos`. The interpolation identity
(19.28.6) uses the positive-parameter merging formula
`Dirichlet.regCarlsonDirichletAverage_ofReal_eq_merge` from `lean-codes`, followed by the
change of variable `u = v²` (`Carlson.integral_Ioo_sq_eq`).

## References

* NIST DLMF §19.28.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-- DLMF 19.28.1: `∫₀¹ t^{σ-1} R_F(0, t, 1) dt = (1/2) B(σ, 1/2)²`, `ℜσ > 0`. -/
@[dlmf 19.28.E1]
theorem integral_cpow_mul_symEllIntRF_zero {σ : ℂ} (hσ : 0 < σ.re) :
    ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (σ - 1) * symEllIntRF 0 t 1 =
      1 / 2 * betaIntegral σ (1 / 2) ^ 2 := by
  sorry

/-- DLMF 19.28.2: `∫₀¹ t^{σ-1} R_G(0, t, 1) dt = σ/(4σ + 2) B(σ, 1/2)²`, `ℜσ > 0`. -/
@[dlmf 19.28.E2]
theorem integral_cpow_mul_symEllIntRG_zero {σ : ℂ} (hσ : 0 < σ.re) :
    ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (σ - 1) * symEllIntRG 0 t 1 =
      σ / (4 * σ + 2) * betaIntegral σ (1 / 2) ^ 2 := by
  sorry

/-- DLMF 19.28.3: `∫₀¹ t^{σ-1} (1 - t) R_D(0, t, 1) dt = 3/(4σ + 2) B(σ, 1/2)²`, `ℜσ > 0`. -/
@[dlmf 19.28.E3]
theorem integral_cpow_mul_symEllIntRD_zero {σ : ℂ} (hσ : 0 < σ.re) :
    ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (σ - 1) * (1 - t) * symEllIntRD 0 t 1 =
      3 / (4 * σ + 2) * betaIntegral σ (1 / 2) ^ 2 := by
  sorry

/-- DLMF 19.28.4: for real `a`, `b₁`, `b₂` with `c = b₁ + b₂ > 0` and `ℜσ > max(0, a - b₂)`,
`∫₀¹ t^{σ-1} (1 - t)^{c-1} R_{-a}(b₁, b₂; t, 1) dt =
Γ(c) Γ(σ) Γ(σ + b₂ - a) / (Γ(σ + c - a) Γ(σ + b₂))`. Here `R_{-a}` is DLMF's
`symEllIntR a` (on `t ∈ (0, 1)` Carlson's `R`-function). -/
@[dlmf 19.28.E4]
theorem integral_cpow_mul_symEllIntR_two {a b₁ b₂ : ℝ} {σ : ℂ} (hc : 0 < b₁ + b₂)
    (hσ : max 0 (a - b₂) < σ.re) :
    ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (σ - 1) * ((1 - t : ℝ) : ℂ) ^ ((b₁ + b₂ : ℝ) - 1 : ℂ) *
        symEllIntR a ![(b₁ : ℂ), b₂] ![(t : ℂ), 1] =
      Gamma (b₁ + b₂ : ℝ) * Gamma σ * Gamma (σ + b₂ - a) /
        (Gamma (σ + (b₁ + b₂ : ℝ) - a) * Gamma (σ + b₂)) := by
  sorry

/-- For positive real nodes, `R_D` is real and nonnegative, as a positive Carlson average. -/
lemma symEllIntRD_real_nonneg {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    symEllIntRD x y z = ((symEllIntRD x y z).re : ℂ) ∧ 0 ≤ (symEllIntRD x y z).re := by
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
  rw [symEllIntRD_eq_symEllIntR (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy)
    (ofReal_mem_slitPlane.mpr hz), symEllIntR_of_mem _ _
      (vec3_mem_carlsonRSlitDomain (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy)
        (ofReal_mem_slitPlane.mpr hz)), show (-(3 / 2) : ℂ) = ((-3 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← H]
  simp only [ofReal_re]
  exact ⟨trivial, (Carlson.carlsonRReal_pos (-3 / 2) hb hv).le⟩

/-- With fixed positive first two nodes, the Carlson asymptotic formula implies `R_F → 0`. -/
lemma tendsto_symEllIntRF_atTop {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun t : ℝ => symEllIntRF x y t) atTop (𝓝 0) := by
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
  exact (symEllIntRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr hx)
    (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr ht)).symm

/-- DLMF 19.28.5: `∫_z^∞ R_D(x, y, t) dt = 6 R_F(x, y, z)` for `x, y, z > 0`. -/
@[dlmf 19.28.E5]
theorem integral_Ioi_symEllIntRD {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ∫ t in Ioi z, symEllIntRD x y t = 6 * symEllIntRF x y z := by
  have hderiv : ∀ t ∈ Ici z, HasDerivAt (fun s : ℝ => (symEllIntRF x y s).re)
      (-(1 / 6) * (symEllIntRD x y t).re) t := by
    intro t ht
    have H := (hasDerivAt_symEllIntRF_right (ofReal_mem_slitPlane.mpr hx)
      (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr (hz.trans_le ht))).real_of_complex
    convert H using 1
    simp [mul_re]
  have hnonpos : ∀ t ∈ Ioi z, -(1 / 6) * (symEllIntRD x y t).re ≤ 0 := by
    intro t ht
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (symEllIntRD_real_nonneg hx hy (hz.trans ht)).2
  have hlim := (Complex.continuous_re.tendsto (0 : ℂ)).comp (tendsto_symEllIntRF_atTop hx hy)
  simp only [zero_re, Function.comp_def] at hlim
  have H := integral_Ioi_of_hasDerivAt_of_nonpos' hderiv hnonpos hlim
  rw [integral_const_mul, zero_sub] at H
  have H' : ∫ t in Ioi z, (symEllIntRD x y t).re = 6 * (symEllIntRF x y z).re := by
    linarith
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => (symEllIntRD_real_nonneg hx hy (hz.trans ht)).1),
    integral_complex_ofReal, H', ofReal_mul, ofReal_ofNat]
  congr 1
  apply Complex.ext
  · simp
  · rw [ofReal_im, symEllIntRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr hx)
      (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hz),
      Carlson.carlsonRF_ofReal_eq_integral hx hy hz, ofReal_im]

/-- DLMF 19.28.6: `∫₀¹ R_D(x, y, v² z + (1 - v²) p) dv = R_J(x, y, z, p)` for
`x, y, z, p > 0`. -/
@[dlmf 19.28.E6]
theorem integral_symEllIntRD_interp {x y z p : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hp : 0 < p) :
    ∫ v in Ioo (0 : ℝ) 1, symEllIntRD x y (v ^ 2 * z + (1 - v ^ 2) * p : ℝ) =
      symEllIntRJ x y z p := by
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
        symEllIntRD x y w / Gamma (5 / 2) := by
    have hdom : Dirichlet.mergeNodes (2 : Fin 4) 3 Z w ∈ Carlson.carlsonRVariableDomain := by
      intro i
      have hi := e.surjective i
      obtain ⟨j, rfl⟩ := hi
      have he : Dirichlet.mergeNodes (2 : Fin 4) 3 Z w (e j) = ![(x : ℂ), y, w] j := congrFun (hnodes w) j
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
      hdom, ← heq, symEllIntRD_eq_symEllIntR (ofReal_mem_slitPlane.mpr hx)
      (ofReal_mem_slitPlane.mpr hy) (Or.inl hw), symEllIntR_of_mem _ _
      (vec3_mem_carlsonRSlitDomain (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy) (Or.inl hw)),
      Carlson.carlsonR]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    norm_num
    apply (eq_div_iff (Gamma_ne_zero_of_re_pos (by norm_num : 0 < (5 / 2 : ℂ).re))).2
    ring
  have H' : symEllIntRJ x y z p = (1 / 2) * ∫ u in Ioo (0 : ℝ) 1,
      (u : ℂ) ^ (-(1 / 2) : ℂ) * symEllIntRD x y (u * z + (1 - u) * p : ℝ) := by
    rw [symEllIntRJ_eq_symEllIntR (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy)
      (ofReal_mem_slitPlane.mpr hz) (ofReal_mem_slitPlane.mpr hp), symEllIntR_of_mem _ _
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
      symEllIntRD x y ((u : ℂ) * z + (1 - u) * p)) * hcancel
  rw [H']
  have HS := Carlson.integral_Ioo_sq_eq
    (fun u => (u : ℂ) ^ (-(1 / 2) : ℂ) * symEllIntRD x y (u * z + (1 - u) * p : ℝ))
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
theorem integral_symEllIntRJ_sq {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ∫ r in Ioi (0 : ℝ), symEllIntRJ x y z (r ^ 2 : ℝ) =
      3 / 2 * π * symEllIntRF (x * y : ℝ) (x * z : ℝ) (y * z : ℝ) := by
  sorry

/-- DLMF 19.28.8: `∫₀^∞ R_J(tx, y, z, tp) dt = (6/√p) R_C(p, x) R_F(0, y, z)` for
`x, y, z, p > 0`. -/
@[dlmf 19.28.E8]
theorem integral_symEllIntRJ_scale {x y z p : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hp : 0 < p) :
    ∫ t in Ioi (0 : ℝ), symEllIntRJ (t * x : ℝ) y z (t * p : ℝ) =
      6 / (√p : ℝ) * symEllIntRC p x * symEllIntRF 0 y z := by
  sorry

/-- DLMF 19.28.9, **with the added hypothesis `x + y ≤ π/2`** (see the module docstring; DLMF
assumes only `x, y > 0`, under which the identity is false):
`∫₀^{π/2} R_F(sin²θ cos²(x + y), sin²θ cos²(x - y), 1) dθ = R_F(0, cos²x, 1) R_F(0, cos²y, 1)`. -/
@[dlmf 19.28.E9]
theorem integral_symEllIntRF_sin_cos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x + y ≤ π / 2) :
    ∫ θ in Ioo (0 : ℝ) (π / 2),
        symEllIntRF (Real.sin θ ^ 2 * Real.cos (x + y) ^ 2 : ℝ)
          (Real.sin θ ^ 2 * Real.cos (x - y) ^ 2 : ℝ) 1 =
      symEllIntRF 0 (Real.cos x ^ 2 : ℝ) 1 * symEllIntRF 0 (Real.cos y ^ 2 : ℝ) 1 := by
  sorry

/-- DLMF 19.28.10: for `a, b, c, d > 0`,
`∫₀^∞ R_F((ac + bd)², (ad + bc)², 4abcd cosh² z) dz = (1/2) R_F(0, a², b²) R_F(0, c², d²)`. -/
@[dlmf 19.28.E10]
theorem integral_symEllIntRF_cosh {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) :
    ∫ z in Ioi (0 : ℝ),
        symEllIntRF ((a * c + b * d) ^ 2 : ℝ) ((a * d + b * c) ^ 2 : ℝ)
          (4 * a * b * c * d * Real.cosh z ^ 2 : ℝ) =
      1 / 2 * symEllIntRF 0 (a ^ 2 : ℝ) (b ^ 2 : ℝ) * symEllIntRF 0 (c ^ 2 : ℝ) (d ^ 2 : ℝ) := by
  sorry

end DLMF.EllipticIntegrals
