/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Green.IndexOne
public import DLMF.AlgebraicAnalytic.Calculus.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Covering.Besicovitch
import DLMF.AlgebraicAnalytic.Calculus.SeveralVariables
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Green's theorem in the plane and Stokes's theorem (DLMF 1.6.43–1.6.44, 1.6.57)

The area formulas below DLMF 1.6.44, derived from Green's theorem, and Stokes's theorem 1.6.57
for a parametrized surface over a plane region.

## Main results

* `volume_real_eq_green_area`: the area of the region bounded by a closed curve as a line
  integral (DLMF §1.6(iv), after 1.6.44).
* `fluxIntegral_curl_eq_lineIntegral`: Stokes's theorem for a parametrized surface
  (DLMF 1.6.57).

## Implementation notes

Green's theorem 1.6.44 is TauCeti's `TauCeti.Green.green_ac_index_one` (credited in the
pointer file `DLMF.AlgebraicAnalytic.Calculus.MathlibCoverage`): the plane is `ℂ`, the curve
`γ` is closed and absolutely continuous on `[a, b]`, and the region `S` is the part of the
filled hull of the trace off the trace, on which the winding number of `γ` is `1`. This
covers DLMF's positively oriented simple closed piecewise differentiable curves (whose
interior has winding number `1` by the Jordan curve theorem, not in Mathlib), and more: the
curve may cross itself. The parametrized Stokes proof uses Mathlib’s exterior-derivative
naturality together with TauCeti’s pullback regularity and two-vector evaluation APIs
(`ContDiffAt.differentialForm_pullback`, `TauCeti.extDeriv_apply_pair`).
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology Matrix

namespace DLMF.AlgebraicAnalytic

/-- Green's theorem for a field with constant curl `1` gives the area of the region. -/
private lemma volume_filledHull_eq_integral_of_curl_eq_one {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hindex : ∀ z ∈ TauCeti.filledHull (γ '' uIcc a b) \ (γ '' uIcc a b),
      TauCeti.Contour.windingNumber γ a b z = 1)
    {P Q : ℂ → ℝ} (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q)
    (hcurl : ∀ z, TauCeti.Green.curl P Q z = 1) :
    volume.real (TauCeti.filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)) =
      ∫ t in a..b, (P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im) := by
  obtain ⟨-, -, h⟩ := TauCeti.Green.green_ac_index_one hab hγ hclosed isOpen_univ
    (subset_univ _) hP.contDiffOn hQ.contDiffOn hindex
  simp only [TauCeti.Green.circulationFun, hcurl] at h
  rw [h, setIntegral_const, smul_eq_mul, mul_one]

/-- DLMF §1.6(iv), after 1.6.44: the area of the region `S` bounded by `γ` (winding number `1`
on `S`) is `∫_C -y dx = ∫_C x dy = ½ ∫_C (x dy - y dx)`. -/
@[dlmf 1.6.iv]
theorem volume_real_eq_green_area {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hindex : ∀ z ∈ TauCeti.filledHull (γ '' uIcc a b) \ (γ '' uIcc a b),
      TauCeti.Contour.windingNumber γ a b z = 1) :
    let A := volume.real (TauCeti.filledHull (γ '' uIcc a b) \ (γ '' uIcc a b))
    A = ∫ t in a..b, -(γ t).im * (deriv γ t).re ∧
      A = ∫ t in a..b, (γ t).re * (deriv γ t).im ∧
      A = ∫ t in a..b, (-(γ t).im / 2 * (deriv γ t).re + (γ t).re / 2 * (deriv γ t).im) := by
  intro A
  have hre (z : ℂ) : HasFDerivAt (fun z : ℂ => z.re) Complex.reCLM z :=
    Complex.reCLM.hasFDerivAt
  have him (z : ℂ) : HasFDerivAt (fun z : ℂ => z.im) Complex.imCLM z :=
    Complex.imCLM.hasFDerivAt
  have cre : ContDiff ℝ 1 (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have cim : ContDiff ℝ 1 (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have hn (z : ℂ) : HasFDerivAt (fun z : ℂ => -z.im) (-Complex.imCLM) z := (him z).neg
  have h0 (z : ℂ) : HasFDerivAt (fun _ : ℂ => (0 : ℝ)) (0 : ℂ →L[ℝ] ℝ) z := hasFDerivAt_const _ _
  have hn2 (z : ℂ) : HasFDerivAt (fun z : ℂ => -z.im / 2) ((2 : ℝ)⁻¹ • -Complex.imCLM) z := by
    simp only [div_eq_mul_inv]; exact (hn z).mul_const _
  have hr2 (z : ℂ) : HasFDerivAt (fun z : ℂ => z.re / 2) ((2 : ℝ)⁻¹ • Complex.reCLM) z := by
    simp only [div_eq_mul_inv]; exact (hre z).mul_const _
  refine ⟨?_, ?_, ?_⟩
  · have h := volume_filledHull_eq_integral_of_curl_eq_one hab hγ hclosed hindex
        (P := fun z => -z.im) (Q := fun _ => 0)
      cim.neg contDiff_const (fun z => by
        rw [TauCeti.Green.curl, (hn z).fderiv, (h0 z).fderiv]; simp)
    simpa using h
  · have h := volume_filledHull_eq_integral_of_curl_eq_one hab hγ hclosed hindex (P := fun _ => 0)
        (Q := fun z => z.re)
      contDiff_const cre (fun z => by
        rw [TauCeti.Green.curl, (hre z).fderiv, (h0 z).fderiv]; simp)
    simpa using h
  · have h := volume_filledHull_eq_integral_of_curl_eq_one hab hγ hclosed hindex
        (P := fun z => -z.im / 2)
      (Q := fun z => z.re / 2) (cim.neg.div_const 2) (cre.div_const 2) (fun z => by
        rw [TauCeti.Green.curl, (hn2 z).fderiv, (hr2 z).fderiv]; simp; norm_num)
    exact h

/-- Curl is the alternating part of the derivative of a vector field, evaluated on two vectors. -/
private lemma curl_dotProduct_cross_eq_fderiv {F : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {x : Fin 3 → ℝ} (hF : DifferentiableAt ℝ F x) (u v : Fin 3 → ℝ) :
    curl F x ⬝ᵥ (u ⨯₃ v) = (fderiv ℝ F x u) ⬝ᵥ v - (fderiv ℝ F x v) ⬝ᵥ u := by
  have hcomponent (j : Fin 3) : HasFDerivAt (fun y => F y j)
      ((ContinuousLinearMap.proj j).comp (fderiv ℝ F x)) x := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (ContinuousLinearMap.proj j).hasFDerivAt.comp x hF.hasFDerivAt
  have hp (i j : Fin 3) : partialDeriv i (fun y => F y j) x =
      (fderiv ℝ F x (Pi.single i 1)) j := by
    rw [partialDeriv_eq_fderiv i (hcomponent j).differentiableAt, (hcomponent j).fderiv]
    rfl
  have hlin (A : (Fin 3 → ℝ) →L[ℝ] Fin 3 → ℝ) (u : Fin 3 → ℝ) :
      A u = ∑ j : Fin 3, u j • A (Pi.single j 1) := by
    refine (A.toLinearMap.pi_apply_eq_sum_univ u).trans (Finset.sum_congr rfl fun j _ => ?_)
    apply congrArg (fun w => u j • A w)
    funext i
    simp [Pi.single_apply, eq_comm]
  rw [hlin _ u, hlin _ v]
  simp only [curl, hp, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [dotProduct, Fin.isValue, crossProduct, Nat.succ_eq_add_one, Nat.reduceAdd,
    LinearMap.mk₂_apply, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Finset.univ_unique, Fin.default_eq_zero, Matrix.cons_val_fin_one, Finset.sum_const,
    Finset.card_singleton, one_smul, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_singleton]
  ring

/-- The planar curl of a pulled-back field equals its spatial curl dotted with the oriented
tangent area element. -/
private lemma green_curl_pullback_eq_curl_dotProduct_cross {F : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {A : ℂ → Fin 3 → ℝ} (hF : ContDiff ℝ 1 F) (hA : ContDiff ℝ 2 A) (z : ℂ) :
    TauCeti.Green.curl (fun y => F (A y) ⬝ᵥ (fderiv ℝ A y 1))
      (fun y => F (A y) ⬝ᵥ (fderiv ℝ A y Complex.I)) z =
        curl F (A z) ⬝ᵥ ((fderiv ℝ A z 1) ⨯₃ (fderiv ℝ A z Complex.I)) := by
  let L : (Fin 3 → ℝ) →L[ℝ] ((Fin 3 → ℝ) →L[ℝ] ℝ) :=
    ∑ i : Fin 3, (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj i)
  have hL (x v : Fin 3 → ℝ) : L x v = x ⬝ᵥ v := by simp [L, dotProduct]
  let ω : (Fin 3 → ℝ) → (Fin 3 → ℝ) [⋀^Fin 1]→L[ℝ] ℝ := fun x =>
    ContinuousAlternatingMap.ofSubsingleton ℝ (Fin 3 → ℝ) ℝ (0 : Fin 1) (L (F x))
  have hω : ContDiff ℝ 1 ω :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Fin 3 → ℝ) (F := ℝ)
      (0 : Fin 1)).toContinuousLinearEquiv.contDiff.comp (L.contDiff.comp hF)
  have hωder (x : Fin 3 → ℝ) : HasFDerivAt ω
      ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Fin 3 → ℝ) (F := ℝ)
        (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (L.comp (fderiv ℝ F x))) x := by
    exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Fin 3 → ℝ) (F := ℝ)
      (0 : Fin 1)).toContinuousLinearEquiv.hasFDerivAt.comp x
        (L.hasFDerivAt.comp x (hF.differentiable one_ne_zero x).hasFDerivAt)
  let η : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ := fun y =>
    (ω (A y)).compContinuousLinearMap (fderiv ℝ A y)
  have hη : ContDiff ℝ 1 η := contDiff_iff_contDiffAt.mpr fun y =>
    hA.contDiffAt.differentialForm_pullback hω.contDiffAt
  have he (y : ℂ) (v : ℂ) : η y (fun _ => v) = F (A y) ⬝ᵥ (fderiv ℝ A y v) := by
    simp [η, ω, hL]
  have hpull := extDeriv_pullback (hω.differentiable one_ne_zero (A z)) hA.contDiffAt
    (by norm_num)
  have h := congrArg (fun θ : ℂ [⋀^Fin 2]→L[ℝ] ℝ => θ ![1, Complex.I]) hpull
  rw [TauCeti.extDeriv_apply_pair_of_differentiableAt (hη.differentiable one_ne_zero z)] at h
  simp only [he, ContinuousAlternatingMap.compContinuousLinearMap_apply] at h
  have hv : (fun i : Fin 2 => fderiv ℝ A z (![1, Complex.I] i)) =
      ![fderiv ℝ A z 1, fderiv ℝ A z Complex.I] := by
    funext i; fin_cases i <;> rfl
  simp only [Function.comp_def] at h
  rw [hv, TauCeti.extDeriv_apply_pair, (hωder (A z)).fderiv] at h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousAlternatingMap.ofSubsingletonLIE] at h
  rw [TauCeti.Green.curl]
  exact h.trans (curl_dotProduct_cross_eq_fderiv
    (hF.differentiable one_ne_zero (A z)) _ _).symm

/-- DLMF 1.6.57 (Stokes's theorem) for a parametrized surface: let the parameter region
`D ⊆ ℝ²` be the region bounded by the closed absolutely continuous curve `γ` in the
`(u, v)`-plane (identified with `ℂ`; winding number `1` on `D`, i.e. `∂D` positively
oriented), `Φ` of class `C²` on `ℝ²`, and `F` of class `C¹`. Then, with `S = Φ(D)` oriented by
`T_u × T_v` and `∂S = Φ ∘ γ` (anticlockwise relative to that normal),
`∬_S (∇ × F) · dS = ∫_{∂S} F · ds`. -/
@[dlmf 1.6.E57]
theorem fluxIntegral_curl_eq_lineIntegral {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hindex : ∀ z ∈ TauCeti.filledHull (γ '' uIcc a b) \ (γ '' uIcc a b),
      TauCeti.Contour.windingNumber γ a b z = 1)
    {Φ : ℝ × ℝ → Fin 3 → ℝ} (hΦ : ContDiff ℝ 2 Φ)
    {F : (Fin 3 → ℝ) → Fin 3 → ℝ} (hF : ContDiff ℝ 1 F) :
    fluxIntegral (curl F) Φ
        (Complex.equivRealProd '' (TauCeti.filledHull (γ '' uIcc a b) \ (γ '' uIcc a b))) =
      lineIntegral F (fun t => Φ (Complex.equivRealProd (γ t))) a b := by
  let A : ℂ → Fin 3 → ℝ := fun z => Φ (Complex.equivRealProd z)
  have hA : ContDiff ℝ 2 A := hΦ.comp Complex.equivRealProdCLM.contDiff
  have hDA : ContDiff ℝ 1 (fderiv ℝ A) := hA.fderiv_right (by norm_num)
  have hFA : ContDiff ℝ 1 (fun z => F (A z)) := hF.comp (hA.of_le (by norm_num))
  have hAU : ContDiff ℝ 1 (fun z => fderiv ℝ A z 1) := hDA.clm_apply contDiff_const
  have hAV : ContDiff ℝ 1 (fun z => fderiv ℝ A z Complex.I) := hDA.clm_apply contDiff_const
  let P : ℂ → ℝ := fun z => F (A z) ⬝ᵥ fderiv ℝ A z 1
  let Q : ℂ → ℝ := fun z => F (A z) ⬝ᵥ fderiv ℝ A z Complex.I
  have hP : ContDiff ℝ 1 P := by
    dsimp only [P, dotProduct]
    apply ContDiff.sum
    intro i _
    exact (contDiff_pi.mp hFA i).mul (contDiff_pi.mp hAU i)
  have hQ : ContDiff ℝ 1 Q := by
    dsimp only [Q, dotProduct]
    apply ContDiff.sum
    intro i _
    exact (contDiff_pi.mp hFA i).mul (contDiff_pi.mp hAV i)
  have hderA (z : ℂ) : HasFDerivAt A ((fderiv ℝ Φ (Complex.equivRealProd z)).comp
      Complex.equivRealProdCLM.toContinuousLinearMap) z := by
    exact (hΦ.differentiable (by norm_num) _).hasFDerivAt.comp z
      Complex.equivRealProdCLM.hasFDerivAt
  have hT (z : ℂ) : fderiv ℝ A z 1 = tangentU Φ (Complex.equivRealProd z) ∧
      fderiv ℝ A z Complex.I = tangentV Φ (Complex.equivRealProd z) := by
    constructor
    · rw [tangentU_eq_fderiv (hΦ.differentiable (by norm_num) _), (hderA z).fderiv]
      rfl
    · rw [tangentV_eq_fderiv (hΦ.differentiable (by norm_num) _), (hderA z).fderiv]
      rfl
  let D := TauCeti.filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)
  have hD : MeasurableSet D :=
    (IsClosed.isOpen_filledHull_sdiff
      (isCompact_uIcc.image_of_continuousOn hγ.continuousOn).isClosed).measurableSet
  have hg := TauCeti.Green.green_ac_index_one hab hγ hclosed isOpen_univ
    (subset_univ _) hP.contDiffOn hQ.contDiffOn hindex
  calc
    _ = ∫ z in D, curl F (Φ (Complex.equivRealProd z)) ⬝ᵥ
        (tangentU Φ (Complex.equivRealProd z) ⨯₃ tangentV Φ (Complex.equivRealProd z)) := by
      exact Complex.volume_preserving_equiv_real_prod.setIntegral_image_emb
        Complex.measurableEquivRealProd.measurableEmbedding _ D
    _ = ∫ z in D, TauCeti.Green.curl P Q z := by
      apply setIntegral_congr_fun hD
      intro z _
      dsimp only [P, Q]
      rw [green_curl_pullback_eq_curl_dotProduct_cross hF hA, (hT z).1, (hT z).2]
    _ = ∫ t in a..b, TauCeti.Green.circulationFun P Q γ t := hg.2.2.symm
    _ = _ := by
      rw [lineIntegral]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht htmem
      have hdγ := ht (uIoc_subset_uIcc htmem)
      have hc : HasDerivAt (fun t => A (γ t)) (fderiv ℝ A (γ t) (deriv γ t)) t :=
        (hA.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t hdγ.hasDerivAt
      rw [hc.deriv]
      have hlin (L : ℂ →L[ℝ] Fin 3 → ℝ) (v : ℂ) :
          L v = v.re • L 1 + v.im • L Complex.I := by
        rw [← map_smul, ← map_smul, ← map_add]
        congr 1
        apply Complex.ext <;> simp
      rw [hlin _ (deriv γ t), dotProduct_add, dotProduct_smul, dotProduct_smul]
      dsimp only [TauCeti.Green.circulationFun, P, Q, A]
      simp only [smul_eq_mul]
      ring

end DLMF.AlgebraicAnalytic
