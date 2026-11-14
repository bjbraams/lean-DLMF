/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Basic.SymmetricProperties
public import Mathlib.Analysis.Analytic.Basic
import DLMF.EllipticIntegrals.Symmetric
import DLMF.EllipticIntegrals.LegendreSymmetricForms
import Carlson.TwoVariable.QuadraticHybrid
import Carlson.TwoVariable.R.ElementaryValues
import Carlson.TwoVariable.Reduction
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Complementary addition for the degenerate elliptic integral

The complementary addition formula DLMF 19.26.17 follows from the arcsine and arccosine
representations on positive real arguments, analytic continuation to the twice slit plane,
and positive homogeneity. The principal square roots and a zero argument are included.

## Main results

* `analyticAt_symmetricEllipticRC_comp`: analytic dependence on slit-plane arguments.
* `sqrt_mul_symmetricEllipticRC_zero`: the value with one zero argument.
* `symmetricEllipticRC_addition_zero`: the complementary addition formula.

The proof uses `lean-codes`' `Carlson.TwoVariable.arcsin_eq_mul_carlsonRC`,
`Carlson.TwoVariable.arccos_eq_mul_carlsonRC`, `Carlson.analyticAt_carlsonR_comp`, and
`Carlson.TwoVariable.carlsonRC_mul_of_pos`. Positive scaling of the slit plane and
principal powers uses the corresponding TauCeti APIs.
-/

public noncomputable section

open Complex Set Filter
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-- The complementary arcsine and arccosine identity in symmetric integral form. -/
private lemma symmetricEllipticRC_addition_one_ofReal {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    (x : ℂ) ^ (1 / 2 : ℂ) * symmetricEllipticRC (1 - x) 1 +
      (1 - (x : ℂ)) ^ (1 / 2 : ℂ) * symmetricEllipticRC x 1 = π / 2 := by
  have hx' : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hx1' : Real.sqrt x < 1 := (Real.sqrt_lt' zero_lt_one).mpr (by simpa using hx1)
  have hs : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have h1 : 1 - (x : ℂ) ∈ slitPlane := by
    rw [← ofReal_one, ← ofReal_sub]; exact ofReal_mem_slitPlane.mpr (by linarith)
  rw [symmetricEllipticRC_eq_carlsonRC h1 one_mem_slitPlane,
    symmetricEllipticRC_eq_carlsonRC (ofReal_mem_slitPlane.mpr hx) one_mem_slitPlane,
    ← ofReal_sqrt_eq_cpow_half hx.le,
    show 1 - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_sqrt_eq_cpow_half (by linarith : 0 ≤ 1 - x)]
  have ha := Carlson.TwoVariable.arcsin_eq_mul_carlsonRC hx' hx1'
  have hc := Carlson.TwoVariable.arccos_eq_mul_carlsonRC hx' hx1'
  rw [hs] at ha hc
  rw [← ha, ← hc, ← ofReal_add, Real.arccos_eq_pi_div_two_sub_arcsin]
  push_cast
  ring


/-- The degenerate symmetric elliptic integral is analytic in slit-plane arguments. -/
theorem analyticAt_symmetricEllipticRC_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {p : E}
    (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hfp : f p ∈ slitPlane) (hgp : g p ∈ slitPlane) :
    AnalyticAt ℂ (fun q => symmetricEllipticRC (f q) (g q)) p := by
  have ha : AnalyticAt ℂ (fun q =>
      Carlson.carlsonR (-(1 / 2)) ![1 / 2, 1] ![f q, g q]) p := by
    refine Carlson.analyticAt_carlsonR_comp analyticAt_const analyticAt_const ?_
      (vec2_mem_carlsonRSlitDomain hfp hgp) ?_
    · refine analyticAt_pi_iff.mpr fun i => ?_
      fin_cases i <;> simpa
    · intro n
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      intro h
      have h' := congrArg Complex.re h
      norm_num at h'
      linarith [hn]
  refine ha.congr ?_
  have hfe := hf.continuousAt.preimage_mem_nhds (isOpen_slitPlane.mem_nhds hfp)
  have hge := hg.continuousAt.preimage_mem_nhds (isOpen_slitPlane.mem_nhds hgp)
  filter_upwards [hfe, hge] with q hqf hqg
  rw [symmetricEllipticRC_eq_symmetricEllipticR hqf hqg,
    symmetricEllipticR_of_mem _ _ (vec2_mem_carlsonRSlitDomain hqf hqg)]

/-- Analytic continuation of the complementary inverse-trigonometric identity. -/
private lemma symmetricEllipticRC_addition_one {z : ℂ} (hz : z ∈ slitPlane)
    (hz1 : 1 - z ∈ slitPlane) :
    z ^ (1 / 2 : ℂ) * symmetricEllipticRC (1 - z) 1 +
      (1 - z) ^ (1 / 2 : ℂ) * symmetricEllipticRC z 1 = π / 2 := by
  let U : Set ℂ := {w | w ∈ slitPlane ∧ 1 - w ∈ slitPlane}
  have hU : StarConvex ℝ (1 / 2 : ℂ) U := by
    intro w hw a b ha hb hab
    have hcv := starConvex_ofReal_slitPlane (x := 1 / 2) (by norm_num)
    have h1 := hcv hw.1 ha hb hab
    have h2 := hcv hw.2 ha hb hab
    have hc : (a : ℂ) + b = 1 := by exact_mod_cast hab
    constructor
    · simpa only [ofReal_div, ofReal_one, ofReal_ofNat] using h1
    · convert h2 using 1
      simp only [real_smul, ofReal_div, ofReal_one, ofReal_ofNat]
      linear_combination -hc
  have hA : AnalyticOnNhd ℂ (fun z => z ^ (1 / 2 : ℂ) * symmetricEllipticRC (1 - z) 1 +
      (1 - z) ^ (1 / 2 : ℂ) * symmetricEllipticRC z 1) U := by
    intro w hw
    exact ((analyticAt_id.cpow analyticAt_const hw.1).mul
      (analyticAt_symmetricEllipticRC_comp (analyticAt_const.sub analyticAt_id)
        analyticAt_const hw.2 one_mem_slitPlane)).add
      (((analyticAt_const.sub analyticAt_id).cpow analyticAt_const hw.2).mul
      (analyticAt_symmetricEllipticRC_comp analyticAt_id
        analyticAt_const hw.1 one_mem_slitPlane))
  have hcenter : (1 / 2 : ℂ) ∈ U := by
    constructor <;> rw [mem_slitPlane_iff] <;> norm_num
  refine hA.eqOn_of_preconnected_of_frequently_eq (analyticOnNhd_const (v := (π / 2 : ℂ)))
    (hU.isPathConnected hcenter).isConnected.isPreconnected hcenter ?_ ⟨hz, hz1⟩
  have hfreq := Carlson.TwoVariable.frequently_ofReal_Ioo (a := 1 / 2) (ε := 1 / 2)
    (P := fun z : ℂ => z ^ (1 / 2 : ℂ) * symmetricEllipticRC (1 - z) 1 +
      (1 - z) ^ (1 / 2 : ℂ) * symmetricEllipticRC z 1 = π / 2) (by norm_num)
    (fun x h1 h2 => symmetricEllipticRC_addition_one_ofReal (by linarith) (by linarith))
  norm_num only [ofReal_div, ofReal_one, ofReal_ofNat] at hfreq
  exact hfreq

/-- The zero-argument value of the degenerate elliptic integral, with principal square root. -/
theorem sqrt_mul_symmetricEllipticRC_zero {z : ℂ} (hz : z ∈ slitPlane) :
    z ^ (1 / 2 : ℂ) * symmetricEllipticRC 0 z = π / 2 := by
  rw [symmetricEllipticRC_eq_symmetricEllipticRF 0 (not_isNegReal_of_mem_slitPlane hz),
    symmetricEllipticRF_zero_left hz hz]
  have hv : (![z, z] : Fin 2 → ℂ) = fun _ => z := by funext i; fin_cases i <;> rfl
  rw [hv, symmetricEllipticR_const _ _ hz (by simp [Fin.sum_univ_two]; norm_num),
    show -(1 / 2 : ℂ) = -1 / 2 by ring, ← inv_cpow_half_eq_cpow_neg_half]
  have hroot : z ^ (1 / 2 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero hz))
  field_simp [hroot]


/-- DLMF 19.26.17: `√α R_C(β, α + β) + √β R_C(α, α + β) = π/2`, for
`α, β ∈ ℂ \ (-∞, 0)` with `α + β > 0`. -/
@[dlmf 19.26.E17]
theorem symmetricEllipticRC_addition_zero {α β : ℂ} (hα : IsCarlsonArgument α)
    (hβ : IsCarlsonArgument β)
    (hαβ : 0 < (α + β).re) (hαβ' : (α + β).im = 0) :
    α ^ (1 / 2 : ℂ) * symmetricEllipticRC β (α + β) + β ^ (1 / 2 : ℂ) *
        symmetricEllipticRC α (α + β) = π / 2 := by
  rcases hα with hα | rfl
  · rcases hβ with hβ | rfl
    · set c : ℝ := (α + β).re
      have hc : 0 < c := hαβ
      have hsum : α + β = (c : ℂ) := by apply Complex.ext <;> simp [c, hαβ']
      have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
      set u : ℂ := α / c
      set v : ℂ := β / c
      have hu : u ∈ slitPlane := by
        dsimp only [u]
        rw [div_eq_inv_mul, ← ofReal_inv]
        exact TauCeti.ofReal_mul_mem_slitPlane (inv_pos.mpr hc) hα
      have hv : v ∈ slitPlane := by
        dsimp only [v]
        rw [div_eq_inv_mul, ← ofReal_inv]
        exact TauCeti.ofReal_mul_mem_slitPlane (inv_pos.mpr hc) hβ
      have huv : u + v = 1 := by dsimp only [u, v]; rw [← add_div, hsum, div_self hc0]
      have hvu : 1 - u = v := by linear_combination -huv
      have h := symmetricEllipticRC_addition_one hu (by simpa [hvu] using hv)
      rw [hvu] at h
      have eu : (c : ℂ) * u = α := by dsimp only [u]; field_simp [hc0]
      have ev : (c : ℂ) * v = β := by dsimp only [v]; field_simp [hc0]
      rw [hsum, ← eu, ← ev,
        symmetricEllipticRC_eq_carlsonRC (TauCeti.ofReal_mul_mem_slitPlane hc hv)
          (ofReal_mem_slitPlane.mpr hc),
        symmetricEllipticRC_eq_carlsonRC (TauCeti.ofReal_mul_mem_slitPlane hc hu)
          (ofReal_mem_slitPlane.mpr hc)]
      have hsU := Carlson.TwoVariable.carlsonRC_mul_of_pos hc hv one_mem_slitPlane
      have hsV := Carlson.TwoVariable.carlsonRC_mul_of_pos hc hu one_mem_slitPlane
      simp only [mul_one] at hsU hsV
      rw [hsU, hsV, TauCeti.ofReal_mul_cpow hc.le, TauCeti.ofReal_mul_cpow hc.le,
        ← inv_cpow_half_eq_cpow_neg_half,
        ← symmetricEllipticRC_eq_carlsonRC hv one_mem_slitPlane,
        ← symmetricEllipticRC_eq_carlsonRC hu one_mem_slitPlane]
      have hroot : (c : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hc0)
      convert h using 1; field_simp [hroot]
    · simp only [add_zero, zero_cpow (by norm_num : (1 / 2 : ℂ) ≠ 0),
        zero_mul, add_zero]
      exact sqrt_mul_symmetricEllipticRC_zero hα
  · simp only [zero_add, zero_cpow (by norm_num : (1 / 2 : ℂ) ≠ 0), zero_mul]
    have hβ' : β ∈ slitPlane := by
      rw [mem_slitPlane_iff]
      left
      simpa using hαβ
    exact sqrt_mul_symmetricEllipticRC_zero hβ'

end DLMF.EllipticIntegrals
