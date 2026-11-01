/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.PrincipalBranch

public import DLMF.Hypergeometric.Continuation
public import DLMF.Hypergeometric.Basic.CutPlane

/-!
# Contiguous relations and Euler's transformation on the cut plane (DLMF §§15.5, 15.8)

The continuation `regularizedGaussHG` of the regularized function `𝐅(a,b;c;z) = F(a,b;c;z)/Γ(c)`
is defined in `DLMF.Hypergeometric.Basic.PrincipalBranch`; its analyticity on the cut plane
`ℂ ∖ [1, ∞)`, its agreement with `𝐅` on the unit disk and the derivative formulas are in
`DLMF.Hypergeometric.Basic.CutPlane`. The contiguous relations and Euler's transformation are
lifted here from the unit disk with the identity principle `eqOn_cutPlane_of_eqOn_disk`.

## Main results

* `regularizedGaussHG_contiguous_c`, `regularizedGaussHG_contiguous_a` and the other
  `regularizedGaussHG_contiguous_*` lemmas: contiguous relations on the cut plane.
* `regularizedGaussHG_euler`: Euler's transformation 15.8.1 on the cut plane.
-/

@[expose] public section

open Complex Filter Set MeasureTheory intervalIntegral
open scoped Real Nat Topology Interval ComplexOrder

noncomputable section

set_option autoImplicit false

namespace DLMF.Hypergeometric

/-! ### Identities on the cut plane

Every identity between analytic expressions proved on the unit disk lifts to the cut plane by
`eqOn_cutPlane_of_eqOn_disk`. -/

/-- `regularizedGaussHGFun_contiguous_c` on the cut plane. -/
theorem regularizedGaussHG_contiguous_c (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    regularizedGaussHG a b c z =
      (c - a) * regularizedGaussHG a b (c + 1) z + a * regularizedGaussHG (a + 1) b (c + 1) z :=
  eqOn_cutPlane_of_eqOn_disk (f := fun z => regularizedGaussHG a b c z)
    (g := fun z => (c - a) * regularizedGaussHG a b (c + 1) z + a
        * regularizedGaussHG (a + 1) b (c + 1) z)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_c a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_shift_b` on the cut plane. -/
theorem regularizedGaussHG_contiguous_shift_b (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    regularizedGaussHG a b c z - regularizedGaussHG a (b + 1) c z = -(a * z)
        * regularizedGaussHG (a + 1) (b + 1) (c + 1) z :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => regularizedGaussHG a b c z - regularizedGaussHG a (b + 1) c z)
    (g := fun z => -(a * z) * regularizedGaussHG (a + 1) (b + 1) (c + 1) z)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_shift_b a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_a` on the cut plane. -/
theorem regularizedGaussHG_contiguous_a (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    (c - a) * regularizedGaussHG (a - 1) b c z + (2 * a - c + (b - a) * z)
        * regularizedGaussHG a b c z + a * (z - 1) * regularizedGaussHG (a + 1) b c z = 0 :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => (c - a) * regularizedGaussHG (a - 1) b c z + (2 * a - c + (b - a) * z)
          * regularizedGaussHG a b c z + a * (z - 1) * regularizedGaussHG (a + 1) b c z)
    (g := fun z => 0)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_a a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_ab` on the cut plane. -/
theorem regularizedGaussHG_contiguous_ab (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    (b - a) * regularizedGaussHG a b c z + a * regularizedGaussHG (a + 1) b c z - b
        * regularizedGaussHG a (b + 1) c z = 0 :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => (b - a) * regularizedGaussHG a b c z + a * regularizedGaussHG (a + 1) b c z - b
          * regularizedGaussHG a (b + 1) c z)
    (g := fun z => 0)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_ab a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_a_b_pred` on the cut plane. -/
theorem regularizedGaussHG_contiguous_a_b_pred (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    (c - a - b) * regularizedGaussHG a b c z + a * (1 - z) * regularizedGaussHG (a + 1) b c z
        - (c - b) * regularizedGaussHG a (b - 1) c z = 0 :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => (c - a - b) * regularizedGaussHG a b c z + a * (1 - z)
          * regularizedGaussHG (a + 1) b c z - (c - b) * regularizedGaussHG a (b - 1) c z)
    (g := fun z => 0)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_a_b_pred a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_c_succ_deriv` on the cut plane. -/
theorem regularizedGaussHG_contiguous_c_succ_deriv (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    (1 - z) * (a * b) * regularizedGaussHG (a + 1) (b + 1) (c + 1) z = (c - a) * (c - b)
        * regularizedGaussHG a b (c + 1) z + (a + b - c) * regularizedGaussHG a b c z :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => (1 - z) * (a * b) * regularizedGaussHG (a + 1) (b + 1) (c + 1) z)
    (g := fun z => (c - a) * (c - b) * regularizedGaussHG a b (c + 1) z + (a + b - c)
        * regularizedGaussHG a b c z)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_c_succ_deriv a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_a_c_succ` on the cut plane. -/
theorem regularizedGaussHG_contiguous_a_c_succ (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    (a + (b - c) * z) * regularizedGaussHG a b c z - a * (1 - z) * regularizedGaussHG (a + 1) b c z
        + (c - a) * (c - b) * z * regularizedGaussHG a b (c + 1) z = 0 :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => (a + (b - c) * z) * regularizedGaussHG a b c z - a * (1 - z)
          * regularizedGaussHG (a + 1) b c z + (c - a) * (c - b) * z
              * regularizedGaussHG a b (c + 1) z)
    (g := fun z => 0)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_a_c_succ a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_a_succ_c_pred` on the cut plane. -/
theorem regularizedGaussHG_contiguous_a_succ_c_pred (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    (c - a - 1) * regularizedGaussHG a b c z + a * regularizedGaussHG (a + 1) b c z
        - regularizedGaussHG a b (c - 1) z = 0 :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => (c - a - 1) * regularizedGaussHG a b c z + a * regularizedGaussHG (a + 1) b c z
          - regularizedGaussHG a b (c - 1) z)
    (g := fun z => 0)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_a_succ_c_pred a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_a_pred_c_succ` on the cut plane. -/
theorem regularizedGaussHG_contiguous_a_pred_c_succ (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    (1 - z) * regularizedGaussHG a b c z - regularizedGaussHG (a - 1) b c z + (c - b) * z
        * regularizedGaussHG a b (c + 1) z = 0 :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => (1 - z) * regularizedGaussHG a b c z - regularizedGaussHG (a - 1) b c z
          + (c - b) * z * regularizedGaussHG a b (c + 1) z)
    (g := fun z => 0)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_a_pred_c_succ a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_a_pred_c_pred` on the cut plane. -/
theorem regularizedGaussHG_contiguous_a_pred_c_pred (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    (a - 1 + (b + 1 - c) * z) * regularizedGaussHG a b c z + (c - a)
        * regularizedGaussHG (a - 1) b c z - (1 - z) * regularizedGaussHG a b (c - 1) z = 0 :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => (a - 1 + (b + 1 - c) * z) * regularizedGaussHG a b c z + (c - a)
          * regularizedGaussHG (a - 1) b c z - (1 - z) * regularizedGaussHG a b (c - 1) z)
    (g := fun z => 0)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_a_pred_c_pred a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_c_three` on the cut plane. -/
theorem regularizedGaussHG_contiguous_c_three (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    (z - 1) * regularizedGaussHG a b (c - 1) z + (c - 1 - (2 * c - a - b - 1) * z)
        * regularizedGaussHG a b c z + (c - a) * (c - b) * z * regularizedGaussHG a b (c + 1) z
            = 0 :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => (z - 1) * regularizedGaussHG a b (c - 1) z + (c - 1 - (2 * c - a - b - 1) * z)
          * regularizedGaussHG a b c z + (c - a) * (c - b) * z * regularizedGaussHG a b (c + 1) z)
    (g := fun z => 0)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_c_three a b c hz) hz

/-- `regularizedGaussHGFun_contiguous_diagonal` on the cut plane. -/
theorem regularizedGaussHG_contiguous_diagonal (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    z * (1 - z) * (a + 1) * (b + 1) * regularizedGaussHG (a + 2) (b + 2) (c + 2) z
        + (c - (a + b + 1) * z) * regularizedGaussHG (a + 1) (b + 1) (c + 1) z
            - regularizedGaussHG a b c z = 0 :=
  eqOn_cutPlane_of_eqOn_disk
      (f := fun z => z * (1 - z) * (a + 1) * (b + 1) * regularizedGaussHG (a + 2) (b + 2) (c + 2) z
          + (c - (a + b + 1) * z) * regularizedGaussHG (a + 1) (b + 1) (c + 1) z
              - regularizedGaussHG a b c z)
    (g := fun z => 0)
    (by intro z hz; fun_prop (disch := assumption)) (by intro z hz; fun_prop (disch := assumption))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_contiguous_diagonal a b c hz) hz

/-- Euler's transformation 15.8.1 on the cut plane:
`𝐅(a,b;c;z) = (1-z)^(c-a-b) 𝐅(c-a,c-b;c;z)`. -/
theorem regularizedGaussHG_euler (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    regularizedGaussHG a b c z = (1 - z) ^ (c - a - b) * regularizedGaussHG (c - a) (c - b) c z :=
  eqOn_cutPlane_of_eqOn_disk (f := fun z => regularizedGaussHG a b c z)
    (g := fun z => (1 - z) ^ (c - a - b) * regularizedGaussHG (c - a) (c - b) c z)
    (by intro z hz; fun_prop (disch := assumption))
    (by
      intro z hz
      exact ((analyticAt_const.sub analyticAt_id).cpow analyticAt_const hz).mul
        (analyticAt_regularizedGaussHG _ _ _ hz))
    (fun z hz => by
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz]
      exact regularizedGaussHGFun_euler a b c hz) hz

/-- The Pfaff map `z ↦ z/(z-1)` preserves the cut plane. -/
theorem div_sub_one_mem_cutPlane {z : ℂ} (hz : z ∈ cutPlane) : z / (z - 1) ∈ cutPlane := by
  have h0 : 1 - z ≠ 0 := one_sub_ne_zero_of_mem_cutPlane hz
  have h1 : z - 1 ≠ 0 := fun h => h0 (by linear_combination -h)
  show 1 - z / (z - 1) ∈ slitPlane
  have : 1 - z / (z - 1) = (1 - z)⁻¹ := by
    field_simp
    ring
  rw [this]
  have hz' : 1 - z ∈ slitPlane := hz
  rw [mem_slitPlane_iff] at hz' ⊢
  rw [inv_re, inv_im]
  have hn : 0 < normSq (1 - z) := normSq_pos.mpr h0
  rcases hz' with h | h
  · exact Or.inl (div_pos h hn)
  · right
    rw [neg_div, neg_ne_zero]
    exact div_ne_zero h hn.ne'

/-- Pfaff's transformation 15.8.1 on the cut plane:
`𝐅(a,b;c;z) = (1-z)^(-a) 𝐅(a,c-b;c;z/(z-1))`. -/
theorem regularizedGaussHG_pfaff (a b c : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
    regularizedGaussHG a b c z = (1 - z) ^ (-a) * regularizedGaussHG a (c - b) c (z / (z - 1)) :=
  eqOn_cutPlane_of_eqOn_ball (f := fun z => regularizedGaussHG a b c z)
    (g := fun z => (1 - z) ^ (-a) * regularizedGaussHG a (c - b) c (z / (z - 1)))
    (by intro z hz; fun_prop (disch := assumption))
    (by
      intro z hz
      have h1 : z - 1 ≠ 0 := fun h => one_sub_ne_zero_of_mem_cutPlane hz (by linear_combination -h)
      have hmap : AnalyticAt ℂ (fun w : ℂ => w / (w - 1)) z :=
        AnalyticAt.fun_div (f := fun w : ℂ => w) (g := fun w : ℂ => w - 1) (x := z)
          analyticAt_id (analyticAt_id.sub analyticAt_const) h1
      exact ((analyticAt_const.sub analyticAt_id).cpow analyticAt_const hz).mul
        ((analyticAt_regularizedGaussHG a (c - b) c (div_sub_one_mem_cutPlane hz)).comp
          (f := fun w : ℂ => w / (w - 1)) hmap))
    (r := 1 / 2) (by norm_num)
    (fun z hz => by
      have hz1 : ‖z‖ < 1 := by linarith
      have hlow : 1 - ‖z‖ ≤ ‖z - 1‖ := by
        have := norm_sub_norm_le (1 : ℂ) z
        rwa [norm_one, norm_sub_rev] at this
      have hzt : ‖z / (z - 1)‖ < 1 := by
        rw [norm_div, div_lt_one (by linarith)]
        linarith
      simp only [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hz1,
          regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hzt]
      exact regularizedGaussHGFun_pfaff a b c hz1 hzt) hz

end DLMF.Hypergeometric
