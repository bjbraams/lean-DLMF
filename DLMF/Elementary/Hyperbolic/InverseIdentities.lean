/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.Hyperbolic.InverseBranches

/-!
# Addition identities for inverse hyperbolic functions

Series convergence and compatible-branch sum and difference identities for inverse hyperbolic
values.

Source references and common attribution are retained in
`DLMF.Elementary.Hyperbolic`.
The transformed series follows from the proved Euler arctangent series by rotation
through `-i`; its principal logarithm formula is preserved exactly.
-/

@[expose] public noncomputable section

open Complex Filter Set MeasureTheory

open scoped Real Topology

namespace DLMF.Elementary

/-- Natural-order odd series for the principal `arctanh` on the closed disk minus `±1`. -/
theorem errC_tendsto_arctanh {z : ℂ} (hn : ‖z‖ ≤ 1) (hz : z ≠ 1 ∧ z ≠ -1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ (2*n+1) / (2*n+1 : ℂ))
      atTop (𝓝 (arctanh z)) := by
  have h := (logBoundary_odd hn hz.1 hz.2).div_const 2
  rw [arctanh]
  refine h.congr (fun N => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  ring

/-- Absolute summability of the odd power series strictly inside the unit disk. -/
theorem errC_summable_odd {w : ℂ} (hn : ‖w‖ < 1) :
    Summable (fun n : ℕ => w ^ (2*n+1) / (2*n+1 : ℂ)) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => ‖w‖ ^ (2*n+1)) ?_ (fun n => ?_)
  · have hg : Summable (fun n : ℕ => ‖w‖ * (‖w‖ ^ 2) ^ n) :=
      (summable_geometric_of_lt_one (by positivity)
        (by nlinarith [norm_nonneg w])).mul_left _
    refine hg.congr (fun n => ?_)
    ring
  · rw [norm_div, norm_pow]
    have h1 : (1 : ℝ) ≤ ‖(2*n+1 : ℂ)‖ := by
      have : (2*n+1 : ℂ) = ((2*n+1 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    exact div_le_self (by positivity) h1

/-- The odd principal-logarithm correction outside the unit disk. -/
theorem errC_arctanh_large_eq {z : ℂ} (hz : z.im ≠ 0) :
    arctanh z - (if 0 < z.im then 1 else -1) * I * π / 2 =
      Complex.log ((1 + z⁻¹) / (1 - z⁻¹)) / 2 := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have h1 : 1 - z ≠ 0 := by
    intro h; apply hz; have := congrArg Complex.im h; simp at this; linarith
  have hz1 : z - 1 ≠ 0 := by intro h; apply h1; linear_combination -h
  set v := (1 + z) / (1 - z) with hv
  have hu : (1 + z⁻¹) / (1 - z⁻¹) = -v := by
    rw [hv]; field_simp; ring
  rw [hu, arctanh, ← hv]
  have hvim : v.im = 2 * z.im / Complex.normSq (1 - z) := by
    rw [hv, Complex.div_im]
    simp [Complex.normSq_apply]
    field_simp
    ring
  have hns : 0 < Complex.normSq (1 - z) := Complex.normSq_pos.mpr h1
  have hu0 : -v ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp [hvim] at this
    rcases this with h | h
    · exact hz h
    · exact h1 h
  split_ifs with hpos
  · -- Im v > 0, so Im(-v) < 0 and log v = log(-v) + iπ
    have him : (-v).im < 0 := by simp [hvim]; positivity
    have harg := Complex.arg_neg_iff.mpr him
    have hl : Complex.log v = Complex.log (-v) + π * I := by
      have he : Complex.exp (Complex.log (-v) + π * I) = v := by
        rw [Complex.exp_add, Complex.exp_log hu0, Complex.exp_pi_mul_I]; ring
      conv_lhs => rw [← he]
      rw [Complex.log_exp]
      all_goals try simp only [Complex.add_im, Complex.log_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
      all_goals nlinarith [Complex.neg_pi_lt_arg (-v), Complex.arg_le_pi (-v), Real.pi_pos]
    rw [hl]; ring
  · have hneg : z.im < 0 := lt_of_le_of_ne (not_lt.mp hpos) hz
    have him : 0 < (-v).im := by
      simp [hvim]; exact div_neg_of_neg_of_pos (by linarith) hns
    have harg : 0 < (-v).arg := by
      refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr him.le) (fun h => ?_)
      have := (Complex.arg_eq_zero_iff.mp h.symm).2
      linarith
    have hl : Complex.log v = Complex.log (-v) - π * I := by
      have he : Complex.exp (Complex.log (-v) - π * I) = v := by
        rw [Complex.exp_sub, Complex.exp_log hu0, Complex.exp_pi_mul_I]; field_simp
      conv_lhs => rw [← he]
      rw [Complex.log_exp]
      all_goals try simp only [Complex.sub_im, Complex.log_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
      all_goals nlinarith [Complex.neg_pi_lt_arg (-v), Complex.arg_le_pi (-v), Real.pi_pos]
    rw [hl]; ring

/-- Maclaurin series of the principal `arctanh` on the full DLMF domain `|z| ≤ 1`, `z ≠ ±1`,
as a limit of natural-order partial sums (the boundary series converge only conditionally). -/
@[dlmf 4.38.E5]
theorem tendsto_arctanh_series {z : ℂ} (hn : ‖z‖ ≤ 1) (hz : z ≠ 1 ∧ z ≠ -1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ (2*n+1) / (2*n+1 : ℂ))
      atTop (𝓝 (arctanh z)) :=
  errC_tendsto_arctanh hn hz

/-- Maclaurin series of the principal `arctanh`, unordered sum strictly inside the unit disk.
Corrected from the earlier transcription: it asserted unordered `HasSum` on the closed disk,
which is false on the unit circle (at `z = i` the term norms are `1/(2n+1)`); the boundary
points are covered by `tendsto_arctanh_series` in natural order. -/
@[dlmf 4.38.E5]
theorem hasSum_arctanh {z : ℂ} (hn : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ (2*n+1) / (2*n+1 : ℂ)) (arctanh z) := by
  have hs := errC_summable_odd hn
  have hz : z ≠ 1 ∧ z ≠ -1 := by
    constructor <;> rintro rfl <;> simp at hn
  rw [← tendsto_nhds_unique hs.hasSum.tendsto_sum_nat (errC_tendsto_arctanh hn.le hz)]
  exact hs.hasSum

/-- Reciprocal series of the principal `arctanh` on the full DLMF domain `|z| ≥ 1`, `Im z ≷ 0`,
as a limit of natural-order partial sums. -/
@[dlmf 4.38.E6]
theorem tendsto_arctanh_large_series {z : ℂ} (hn : 1 ≤ ‖z‖) (hz : z.im ≠ 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, 1 / ((2*n+1 : ℂ) * z ^ (2*n+1)))
      atTop (𝓝 (arctanh z - (if 0 < z.im then 1 else -1) * I * π / 2)) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hw : ‖z⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact (inv_le_one₀ (norm_pos_iff.mpr hz0)).2 hn
  have hp : z⁻¹ ≠ 1 := by
    intro h; apply hz; rw [inv_eq_one.mp h]; simp
  have hm : z⁻¹ ≠ -1 := by
    intro h; apply hz; rw [show z = -1 by simpa using congrArg (fun w : ℂ => w⁻¹) h]; simp
  have h := (logBoundary_odd hw hp hm).div_const 2
  rw [errC_arctanh_large_eq hz]
  refine h.congr (fun N => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [inv_pow]
  field_simp

/-- Reciprocal series of the principal `arctanh`, unordered sum strictly outside the unit disk.
Corrected from the earlier transcription: it asserted unordered `HasSum` for `|z| ≥ 1`, which is
false on the unit circle (at `z = i` the term norms are `1/(2n+1)`); the boundary points are
covered by `tendsto_arctanh_large_series` in natural order. -/
@[dlmf 4.38.E6]
theorem hasSum_arctanh_large {z : ℂ} (hn : 1 < ‖z‖) (hz : z.im ≠ 0) :
    HasSum (fun n : ℕ => 1 / ((2*n+1 : ℂ) * z ^ (2*n+1)))
      (arctanh z - (if 0 < z.im then 1 else -1) * I * π / 2) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hn; linarith
  have hw : ‖z⁻¹‖ < 1 := by
    rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hn
  have hs : Summable (fun n : ℕ => 1 / ((2*n+1 : ℂ) * z ^ (2*n+1))) :=
    (errC_summable_odd hw).congr (fun n => by rw [inv_pow]; field_simp)
  rw [← tendsto_nhds_unique hs.hasSum.tendsto_sum_nat
    (tendsto_arctanh_large_series hn.le hz)]
  exact hs.hasSum

/-- The factorial-coefficient expansion of the principal `arctanh` quotient on
`Re (z²) < 1/2`, normalized to one at zero. -/
@[dlmf 4.38.E7]
theorem hasSum_arctanh_transformed {z : ℂ} (hz : (z^2).re<1/2) : HasSum (fun n : ℕ => (4:ℂ)^n*(n.factorial:ℂ)^2/((2*n+1).factorial:ℂ)*(z^2/(z^2-1))^n) (if z=0 then 1 else (1-z^2)/z*arctanh z) := by
  by_cases hz0 : z=0
  · subst z
    convert hasSum_ite_eq (0:ℕ) (1:ℂ) using 1
    · funext n
      by_cases hn : n=0
      · simp [hn]
      · simp [hn]
    · simp
  have hs : (-I*z)^2 = -z^2 := by simp [mul_pow, Complex.I_sq]
  have ht : -(1/2:ℝ)<((-I*z)^2).re := by rw [hs, Complex.neg_re]; linarith
  have hd : 1-z^2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  have hw : (-I*z)^2/(1+(-I*z)^2) = z^2/(z^2-1) := by
    rw [hs, show 1 + -z^2 = -(z^2-1) by ring, div_neg, neg_div, neg_neg]
  have ha : Complex.arctan (-I*z) = -I*arctanh z := by
    rw [Complex.arctan, show (-I*z)*I=z by calc
      _ = -(I*I)*z := by ring
      _ = z := by simp, arctanh]
    ring
  have hpref : (I*(1-z^2)/z)*((-I*z)/(1+(-I*z)^2)) = 1 := by
    rw [hs, show 1 + -z^2 = 1-z^2 by ring]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have h := (hasSum_arctan_euler ht).mul_left (I*(1-z^2)/z)
  rw [hw] at h
  simp only [ite_eq_right hz0]
  convert h using 1
  · funext n
    calc (4:ℂ)^n*(n.factorial:ℂ)^2/((2*n+1).factorial:ℂ)*(z^2/(z^2-1))^n =
        ((I*(1-z^2)/z)*((-I*z)/(1+(-I*z)^2)))*
          ((4:ℂ)^n*(n.factorial:ℂ)^2/((2*n+1).factorial:ℂ)*(z^2/(z^2-1))^n) := by rw [hpref]; ring
      _ = _ := by ring
  · rw [ha]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring

/-- The stated relation follows from the given hypotheses: `(z^2).re<1/2 ↔ z.re^2-z.im^2<1/2`. -/
@[dlmf 4.38.E8]
theorem arctanh_transformed_region (z : ℂ) : (z^2).re<1/2 ↔ z.re^2-z.im^2<1/2 := by
  simp [Complex.mul_re,pow_two]

/-- At `z`, the function `arcsinh` has derivative `((Complex.sqrt (1+z^2))⁻¹)`. -/
@[dlmf 4.38.E9]
theorem hasDerivAt_arcsinh {z : ℂ} (hz : z∈arcsinhDomain) : HasDerivAt arcsinh ((Complex.sqrt (1+z^2))⁻¹) z := by
  exact hyper_hasDerivAt_arcsinh hz

/-- At `z`, the function `arccosh` has derivative `((Complex.sqrt (z-1)*Complex.sqrt (z+1))⁻¹)`. -/
@[dlmf 4.38.E10]
theorem hasDerivAt_arccosh {z : ℂ} (hz : z∈arccoshDomain) : HasDerivAt arccosh ((Complex.sqrt (z-1)*Complex.sqrt (z+1))⁻¹) z := by
  exact hypR4_hasDerivAt_arccosh hz

/-- At `z`, the function `arccosh` has derivative `((if 0<z.re then 1 else -1)*(Complex.sqrt
(z^2-1))⁻¹)`. -/
@[dlmf 4.38.E10]
theorem hasDerivAt_arccosh_signed {z : ℂ} (hz : z∈arccoshDomain) (hre : z.re≠0) : HasDerivAt arccosh ((if 0<z.re then 1 else -1)*(Complex.sqrt (z^2-1))⁻¹) z := by
  have h := hypR4_hasDerivAt_arccosh hz
  rw [hypR4_acosh_root_signed hz hre] at h
  convert h using 1
  split_ifs <;> simp

/-- At `z`, the function `arctanh` has derivative `(1/(1-z^2))`. -/
@[dlmf 4.38.E11]
theorem hasDerivAt_arctanh {z : ℂ} (hz : z∈arctanhDomain) : HasDerivAt arctanh (1/(1-z^2)) z := by
  exact hyper_hasDerivAt_arctanh hz

/-- At `z`, the function `arccsch` has derivative `(-1/(z^2*Complex.sqrt (1+z⁻¹^2)))`. -/
@[dlmf 4.38.E12]
theorem hasDerivAt_arccsch {z : ℂ} (hz : z∈arccschDomain) : HasDerivAt arccsch (-1/(z^2*Complex.sqrt (1+z⁻¹^2))) z := by
  have hd:=(hyper_hasDerivAt_arcsinh hz.2).comp z ((hasDerivAt_id z).inv hz.1)
  convert hd using 1
  · rfl
  · dsimp only [id]
    field_simp <;> ring

/-- `1 + w²` lies in the principal slit plane on the open inverse-sinh domain. -/
private lemma hypR4_one_add_sq_slit {w : ℂ} (hw : w.re ≠ 0 ∨ |w.im| < 1) :
    1+w^2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  rcases hw with hr | hi
  · by_cases hy : w.im = 0
    · left; simp [pow_two, Complex.mul_re, hy]; nlinarith [sq_nonneg w.re]
    · right; simp [pow_two, Complex.mul_im]
      intro h; apply mul_ne_zero (mul_ne_zero two_ne_zero hr) hy; linear_combination h
  · left
    simp [pow_two, Complex.mul_re]
    nlinarith [abs_lt.mp hi, sq_nonneg w.re]

/-- On the right half-plane `z √(1+z⁻²)` is the principal `√(1+z²)`. -/
private lemma hypR4_acsch_root_pos {z : ℂ} (hre : 0 < z.re) :
    z*Complex.sqrt (1+z⁻¹^2) = Complex.sqrt (1+z^2) := by
  set V := {z : ℂ | 0 < z.re}
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hVc : IsPreconnected V := (convex_halfSpace_re_gt 0).isPreconnected
  have h1V : (1:ℂ) ∈ V := by show (0:ℝ) < (1:ℂ).re; norm_num
  have hinvre : ∀ w ∈ V, 0 < (w⁻¹).re := fun w hw => by
    rw [Complex.inv_re]
    have : w ≠ 0 := fun h => by subst h; exact absurd (show (0:ℝ) < (0:ℂ).re from hw) (by simp)
    exact div_pos hw (Complex.normSq_pos.mpr this)
  have hr : AnalyticOnNhd ℂ (fun w => w*Complex.sqrt (1+w⁻¹^2)) V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    have hw0 : w ≠ 0 := fun h => by subst h; exact absurd (show (0:ℝ) < (0:ℂ).re from hw) (by simp)
    have hsl := hypR4_one_add_sq_slit (Or.inl (hinvre w hw).ne')
    exact (differentiableAt_id.mul ((Complex.differentiableAt_sqrt hsl).comp w
      (by fun_prop (disch := exact hw0) : DifferentiableAt ℂ (fun w : ℂ => 1+w⁻¹^2) w))).differentiableWithinAt
  have hs : AnalyticOnNhd ℂ (fun w => Complex.sqrt (1+w^2)) V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    have hsl := hypR4_one_add_sq_slit (Or.inl (ne_of_gt hw))
    exact ((Complex.differentiableAt_sqrt hsl).comp w
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 1+w^2) w)).differentiableWithinAt
  refine hypR4_sq_eq_continuation hVo hVc hr hs ?_ h1V ?_ ?_ z hre
  · intro w hw
    have hw0 : w ≠ 0 := fun h => by subst h; exact absurd (show (0:ℝ) < (0:ℂ).re from hw) (by simp)
    rw [mul_pow, trig_sqrt_sq, trig_sqrt_sq]; field_simp; ring
  · norm_num
  · intro h
    have := trig_sqrt_sq (1+(1:ℂ)^2)
    rw [h] at this; norm_num at this

/-- `z √(1+z⁻²) = ±√(1+z²)` according to the sign of `Re z`. -/
private lemma hypR4_acsch_root_signed {z : ℂ} (hre : z.re ≠ 0) :
    z*Complex.sqrt (1+z⁻¹^2) = (if 0<z.re then 1 else -1)*Complex.sqrt (1+z^2) := by
  rcases lt_or_gt_of_ne hre with hneg | hpos
  · simp only [show ¬ (0 < z.re) from not_lt.mpr hneg.le, ↓reduceIte]
    have h := hypR4_acsch_root_pos (z := -z) (by simpa using hneg)
    rw [inv_neg, neg_sq, neg_sq] at h
    linear_combination -h
  · simp only [hpos, ↓reduceIte, one_mul]; exact hypR4_acsch_root_pos hpos

/-- At `z`, the function `arccsch` has derivative `(-(if 0<z.re then 1 else -1)/(z*Complex.sqrt
(1+z^2)))`. -/
@[dlmf 4.38.E12]
theorem hasDerivAt_arccsch_signed {z : ℂ} (hz : z∈arccschDomain) (hre : z.re≠0) : HasDerivAt arccsch (-(if 0<z.re then 1 else -1)/(z*Complex.sqrt (1+z^2))) z := by
  have h := hasDerivAt_arccsch hz
  have hz0 : z ≠ 0 := hz.1
  have e := hypR4_acsch_root_signed hre
  convert h using 1
  rw [show z^2*Complex.sqrt (1+z⁻¹^2) = z*(z*Complex.sqrt (1+z⁻¹^2)) by ring, e]
  split_ifs <;> field_simp

/-- At `z`, the function `arcsech` has derivative `(-1/(z*Complex.sqrt (1-z^2)))`. -/
@[dlmf 4.38.E13]
theorem hasDerivAt_arcsech {z : ℂ} (hz : z∈arcsechDomain) : HasDerivAt arcsech (-1/(z*Complex.sqrt (1-z^2))) z := by
  have hz0 : z ≠ 0 := hz.1
  have h := (hypR4_hasDerivAt_arccosh hz.2).comp z (hasDerivAt_inv hz0)
  have e := hypR4_asech_root hz
  have hS : Complex.sqrt (z⁻¹-1)*Complex.sqrt (z⁻¹+1) ≠ 0 := hypR4_acosh_root_ne hz.2
  have hf : arcsech = arccosh ∘ (fun w : ℂ => w⁻¹) := rfl
  rw [hf]
  convert h using 1
  rw [← e]
  field_simp

/-- At `z`, the function `arccoth` has derivative `(1/(1-z^2))`. -/
@[dlmf 4.38.E14]
theorem hasDerivAt_arccoth {z : ℂ} (hz : z∈arccothDomain) : HasDerivAt arccoth (1/(1-z^2)) z := by
  obtain ⟨hz0,hi⟩:=hyper_acoth_inv_mem hz
  have hd:=(hyper_hasDerivAt_arctanh hi).comp z ((hasDerivAt_id z).inv hz0)
  have hd':HasDerivAt (fun w:ℂ=>arctanh w⁻¹) (1/(1-z^2)) z := by
    convert hd using 1
    · rfl
    · dsimp only [id]
      field_simp [hz0]
      have heq:(1-z^2)⁻¹= -(-1+z^2)⁻¹ := by
        rw [show (1-z^2)= -(-1+z^2) by ring,inv_neg]
      convert heq using 1 <;> ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hz0] with w hw
  exact arccoth_eq_inv hw

/-- The former unrestricted full-set acquisition of 4.38.15 loses branch compatibility:
at u=v=i it includes zero on the right, whereas the actual sum cannot contain zero.
This diagnoses the acquisition, not the branch-qualified DLMF formula. -/
theorem arcsinh_values_add_unrestricted_counterexample :
    (0:ℂ)∈{w | ∃ r s : ℂ,r^2=1+I^2 ∧ s^2=1+I^2 ∧ w∈arcsinhValues (I*r+I*s)} ∧
    (0:ℂ)∉Set.image2 (fun a b : ℂ=>a+b) (arcsinhValues I) (arcsinhValues I) := by
  constructor
  · refine ⟨0,0,?_,?_,?_⟩ <;> simp [arcsinhValues]
  · rintro ⟨a,ha,b,hb,hab⟩
    change Complex.sinh a=I at ha
    change Complex.sinh b=I at hb
    have hba:b= -a := by linear_combination hab
    rw [hba,Complex.sinh_neg,ha] at hb
    have hc:(I:ℂ)=0 := by linear_combination -hb/2
    exact Complex.I_ne_zero hc

/-- DLMF4.38.15 with compatible branches: the same two square-root witnesses determine
both sinh and cosh of the sum. The cosh condition retains the missing parity information,
including u=v=i; every pair of complex parameters and every inverse branch is retained. -/
@[dlmf 4.38.E15]
theorem arcsinh_values_add (u v : ℂ) :
    Set.image2 (fun a b : ℂ => a+b) (arcsinhValues u) (arcsinhValues v)=
      {w | ∃ r s : ℂ,r^2=1+v^2 ∧ s^2=1+u^2 ∧
        w∈arcsinhValues (u*r+v*s) ∧ Complex.cosh w=s*r+u*v} := by
  ext w
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    change Complex.sinh a=u at ha
    change Complex.sinh b=v at hb
    refine ⟨Complex.cosh b,Complex.cosh a,?_,?_,?_,?_⟩
    · rw [Complex.cosh_sq,hb];ring
    · rw [Complex.cosh_sq,ha];ring
    · change Complex.sinh (a+b)=u*Complex.cosh b+v*Complex.cosh a
      rw [Complex.sinh_add,ha,hb]
      ring
    · rw [Complex.cosh_add,ha,hb] <;> ring
  · rintro ⟨r,s,hr,hs,hw,hc⟩
    have ha:=hyper_sinh_cosh_log_lift u s hs
    let a:=Complex.log (s+u)
    refine ⟨a,ha.1,w-a,?_,by ring⟩
    change Complex.sinh (w-a)=v
    change Complex.sinh w=u*r+v*s at hw
    rw [Complex.sinh_sub,ha.1,ha.2,hw,hc]
    linear_combination v*hs

/-- Formula under the stated hypotheses: `Set.image2 (fun a b : ℂ => a+b) (arccoshValues u)
(arccoshValues v)= {w | ∃ r : ℂ, r^2=(u^2-1)*(v^2-1) ∧ w ∈ arccoshValues (u*v+r)}`. -/
@[dlmf 4.38.E16]
theorem arccosh_values_add (u v : ℂ) :
    Set.image2 (fun a b : ℂ => a+b) (arccoshValues u) (arccoshValues v)=
      {w | ∃ r : ℂ, r^2=(u^2-1)*(v^2-1) ∧ w ∈ arccoshValues (u*v+r)} := by
  ext w
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    change Complex.cosh a=u at ha
    change Complex.cosh b=v at hb
    refine ⟨Complex.sinh a*Complex.sinh b,?_,?_⟩
    · simp only [mul_pow,Complex.sinh_sq,ha,hb]
    · change Complex.cosh (a+b)=u*v+Complex.sinh a*Complex.sinh b
      rw [Complex.cosh_add,ha,hb]
  · rintro ⟨r,hr,hc⟩
    change Complex.cosh w=u*v+r at hc
    have hs:(v-u*Complex.cosh w)^2=(Complex.sinh w*Complex.sinh (arccosh u))^2 := by
      simp only [mul_pow,Complex.sinh_sq,hyper_cosh_arccosh,hc]
      linear_combination hr
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hs|hs
    · refine ⟨-arccosh u,?_,w+arccosh u,?_,by ring⟩
      · change Complex.cosh (-arccosh u)=u
        rw [Complex.cosh_neg,hyper_cosh_arccosh]
      · change Complex.cosh (w+arccosh u)=v
        rw [Complex.cosh_add,hyper_cosh_arccosh]
        linear_combination -hs
    · refine ⟨arccosh u,hyper_cosh_arccosh u,w-arccosh u,?_,by ring⟩
      change Complex.cosh (w-arccosh u)=v
      rw [Complex.cosh_sub,hyper_cosh_arccosh]
      linear_combination -hs

/-- Off `±1`, the finite inverse-tanh values are the solutions of `exp (2w) (1-z) = 1+z`. -/
private lemma hypR4_mem_arctanhValues_iff {z w : ℂ} (h1 : z ≠ 1) (h2 : z ≠ -1) :
    w ∈ arctanhValues z ↔ Complex.exp (2*w)*(1-z) = 1+z := by
  obtain ⟨hc, hs⟩ := hypR4_cosh_sinh_exp w
  have hE : Complex.exp w ≠ 0 := Complex.exp_ne_zero w
  constructor
  · rintro ⟨hc0, ht⟩
    rw [Complex.tanh_eq_sinh_div_cosh, div_eq_iff hc0] at ht
    linear_combination -hs + z*hc + 2*Complex.exp w*ht
  · intro h'
    have hc0 : Complex.cosh w ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hc
      have : (2:ℂ) = 0 := by linear_combination -h' - (1-z)*hc
      norm_num at this
    refine ⟨hc0, ?_⟩
    rw [Complex.tanh_eq_sinh_div_cosh, div_eq_iff hc0]
    apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hE)
    linear_combination hs - z*hc + h'

/-- Off `±1`, the finite inverse-coth values are the solutions of `exp (2w) (z-1) = z+1`. -/
private lemma hypR4_mem_arccothValues_iff {z w : ℂ} (h1 : z ≠ 1) (h2 : z ≠ -1) :
    w ∈ arccothValues z ↔ Complex.exp (2*w)*(z-1) = z+1 := by
  obtain ⟨hc, hs⟩ := hypR4_cosh_sinh_exp w
  have hE : Complex.exp w ≠ 0 := Complex.exp_ne_zero w
  constructor
  · rintro ⟨hs0, ht⟩
    rw [coth, div_eq_iff hs0] at ht
    linear_combination hc - z*hs - 2*Complex.exp w*ht
  · intro h'
    have hs0 : Complex.sinh w ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hs
      have : (2:ℂ) = 0 := by linear_combination -h' + (1-z)*hs
      norm_num at this
    refine ⟨hs0, ?_⟩
    rw [coth, div_eq_iff hs0]
    apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hE)
    linear_combination hc - z*hs - h'

/-- Solution sets of `exp (2w) c = d` add (Minkowski sum) by multiplying the coefficients. -/
private lemma hypR4_expSet_add {c₁ d₁ c₂ d₂ : ℂ} (hc₁ : c₁ ≠ 0) (hd₁ : d₁ ≠ 0) :
    Set.image2 (fun a b : ℂ => a+b) {w | Complex.exp (2*w)*c₁ = d₁} {w | Complex.exp (2*w)*c₂ = d₂} =
      {w | Complex.exp (2*w)*(c₁*c₂) = d₁*d₂} := by
  ext w
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [mul_add, Complex.exp_add, ← ha, ← hb]; ring
  · intro hw
    simp only [Set.mem_ofPred_eq] at hw
    set a := Complex.log (d₁/c₁)/2
    have ha : Complex.exp (2*a)*c₁ = d₁ := by
      rw [show 2*a = Complex.log (d₁/c₁) by simp [a]; ring, Complex.exp_log (div_ne_zero hd₁ hc₁)]
      field_simp
    refine ⟨a, ha, w-a, ?_, by ring⟩
    simp only [Set.mem_ofPred_eq]
    have hEa : Complex.exp (2*a) ≠ 0 := Complex.exp_ne_zero _
    have e : Complex.exp (2*(w-a)) = Complex.exp (2*w)/Complex.exp (2*a) := by
      rw [← Complex.exp_sub]; ring_nf
    rw [e, div_mul_eq_mul_div, div_eq_iff hEa]
    apply mul_left_cancel₀ hc₁
    linear_combination hw - d₂*ha

/-- Solution sets of `exp (2w) c = d` subtract by cross-multiplying the coefficients. -/
private lemma hypR4_expSet_sub {c₁ d₁ c₂ d₂ : ℂ} (hc₁ : c₁ ≠ 0) (hd₁ : d₁ ≠ 0) :
    Set.image2 (fun a b : ℂ => a-b) {w | Complex.exp (2*w)*c₁ = d₁} {w | Complex.exp (2*w)*c₂ = d₂} =
      {w | Complex.exp (2*w)*(c₁*d₂) = d₁*c₂} := by
  have hneg : {w : ℂ | Complex.exp (2*w)*c₂ = d₂} = (fun w => -w) '' {w | Complex.exp (2*w)*d₂ = c₂} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro h; refine ⟨-w, ?_, neg_neg w⟩
      have hE : Complex.exp (2*w) ≠ 0 := Complex.exp_ne_zero _
      rw [show 2*(-w) = -(2*w) by ring, Complex.exp_neg, ← h]; field_simp
    · rintro ⟨b, hb, rfl⟩
      have hE : Complex.exp (2*b) ≠ 0 := Complex.exp_ne_zero _
      rw [show 2*(-b) = -(2*b) by ring, Complex.exp_neg, ← hb]; field_simp
  rw [hneg, Set.image2_image_right, ← hypR4_expSet_add hc₁ hd₁]
  simp only [sub_neg_eq_add]

/-- Two solution sets of `exp (2w) c = d` coincide when the ratios `d/c` agree. -/
private lemma hypR4_expSet_congr {c d c' d' : ℂ} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (h : c*d' = c'*d) : {w : ℂ | Complex.exp (2*w)*c = d} = {w | Complex.exp (2*w)*c' = d'} := by
  ext w
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hw; apply mul_left_cancel₀ hc; linear_combination c'*hw - h
  · intro hw; apply mul_left_cancel₀ hc'; linear_combination c*hw + h

/-- Identity under the stated parameter and domain assumptions: `Set.image2 (fun a b : ℂ => a+b)
(arctanhValues u) (arctanhValues v)=arctanhValues ((u+v)/(1+u*v))`. -/
@[dlmf 4.38.E17]
theorem arctanh_values_add {u v : ℂ} (hu : u≠1 ∧ u≠ -1) (hv : v≠1 ∧ v≠ -1) (hp : 1+u*v≠0) :
    Set.image2 (fun a b : ℂ => a+b) (arctanhValues u) (arctanhValues v)=arctanhValues ((u+v)/(1+u*v)) := by
  have hu1 : 1-u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu.1)
  have hu2 : 1+u ≠ 0 := fun h => hu.2 (by first | linear_combination h | linear_combination -h)
  have hv1 : 1-v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv.1)
  have hv2 : 1+v ≠ 0 := fun h => hv.2 (by first | linear_combination h | linear_combination -h)
  have ht1 : (u+v)/(1+u*v) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hp]; intro h
    exact mul_ne_zero hu1 hv1 (by first | linear_combination h | linear_combination -h)
  have ht2 : (u+v)/(1+u*v) ≠ -1 := by
    rw [Ne, div_eq_iff hp]; intro h
    exact mul_ne_zero hu2 hv2 (by first | linear_combination h | linear_combination -h)
  have ht3 : 1-(u+v)/(1+u*v) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have e0 : arctanhValues (u) = {w : ℂ | Complex.exp (2*w)*(1-(u)) = 1+(u)} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff hu.1 hu.2
  have e1 : arctanhValues (v) = {w : ℂ | Complex.exp (2*w)*(1-(v)) = 1+(v)} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff hv.1 hv.2
  have e2 : arctanhValues ((u+v)/(1+u*v)) = {w : ℂ | Complex.exp (2*w)*(1-((u+v)/(1+u*v))) = 1+((u+v)/(1+u*v))} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff ht1 ht2
  rw [e0, e1, e2, hypR4_expSet_add hu1 hu2]
  apply hypR4_expSet_congr (mul_ne_zero hu1 hv1) ht3
  field_simp
  ring

/-- The former mixed full-set acquisitions also discarded branch parity. At u=i,v=1,
their inverse-cosh side admits -pi*i/2, whereas every actual sum or difference has sinh=i. -/
theorem arcsinh_arccosh_values_unrestricted_counterexample :
    (-(π*I/2):ℂ)∈{w | ∃ r s : ℂ,r^2=1+I^2 ∧ s^2=(1:ℂ)^2-1 ∧
      w∈arccoshValues (r+I*s)} ∧
    (-(π*I/2):ℂ)∈{w | ∃ r s : ℂ,r^2=1+I^2 ∧ s^2=(1:ℂ)^2-1 ∧
      w∈arccoshValues (r-I*s)} ∧
    (-(π*I/2):ℂ)∉Set.image2 (fun a b : ℂ=>a+b) (arcsinhValues I) (arccoshValues 1) ∧
    (-(π*I/2):ℂ)∉Set.image2 (fun a b : ℂ=>a-b) (arcsinhValues I) (arccoshValues 1) := by
  have hw:-(π*I/2:ℂ)=(-π/2)*I := by ring
  have hcos:Complex.cosh (-(π*I/2):ℂ)=0 := by
    rw [hw,Complex.cosh_mul_I]
    simp [neg_div]
  have hsin:Complex.sinh (-(π*I/2):ℂ)= -I := by
    rw [hw,Complex.sinh_mul_I]
    simp [neg_div]
  have hnot (σ : ℂ) (hσ : σ=1 ∨ σ= -1) :
      (-(π*I/2):ℂ)∉Set.image2 (fun a b : ℂ=>a+σ*b) (arcsinhValues I) (arccoshValues 1) := by
    rintro ⟨a,ha,b,hb,hab⟩
    change Complex.sinh a=I at ha
    change Complex.cosh b=1 at hb
    have hsb:Complex.sinh b=0 := by
      apply sq_eq_zero_iff.mp
      rw [Complex.sinh_sq,hb]
      ring
    have hval:Complex.sinh (a+σ*b)=I := by
      rcases hσ with rfl|rfl <;> simp [Complex.sinh_add,Complex.sinh_neg,Complex.cosh_neg,ha,hb,hsb]
    change a+σ*b= -(π*I/2:ℂ) at hab
    rw [hab,hsin] at hval
    have hc:(I:ℂ)=0 := by linear_combination -hval/2
    exact Complex.I_ne_zero hc
  refine ⟨?_,?_,?_,?_⟩
  · refine ⟨0,0,?_,?_,?_⟩ <;> simp [arccoshValues,hcos]
  · refine ⟨0,0,?_,?_,?_⟩ <;> simp [arccoshValues,hcos]
  · simpa only [one_mul] using hnot 1 (Or.inl rfl)
  · simpa only [neg_one_mul,sub_eq_add_neg] using hnot (-1) (Or.inr rfl)

/-- DLMF4.38.18 interpreted with shared inverse branches. Both inverse descriptions
retain the paired sinh/cosh equations, including all critical parameter values. -/
@[dlmf 4.38.E18]
theorem arcsinh_arccosh_values_add (u v : ℂ) :
    Set.image2 (fun a b : ℂ => a + b) (arcsinhValues u) (arccoshValues v)=
      {w | ∃ r s : ℂ,r^2=1+u^2 ∧ s^2=v^2-1 ∧
        w∈arcsinhValues (u*v + r*s) ∧ Complex.cosh w=v*r + u*s} ∧
    Set.image2 (fun a b : ℂ => a + b) (arcsinhValues u) (arccoshValues v)=
      {w | ∃ r s : ℂ,r^2=1+u^2 ∧ s^2=v^2-1 ∧
        w∈arccoshValues (v*r + u*s) ∧ Complex.sinh w=u*v + r*s} := by
  have hfirst :
      Set.image2 (fun a b : ℂ => a + b) (arcsinhValues u) (arccoshValues v)=
        {w | ∃ r s : ℂ,r^2=1+u^2 ∧ s^2=v^2-1 ∧
          w∈arcsinhValues (u*v + r*s) ∧ Complex.cosh w=v*r + u*s} := by
    simpa only [one_mul,neg_one_mul,sub_eq_add_neg,arcsinhValues,Set.mem_setOf_eq] using
      hyper_mixed_inverse_fiber u v 1 (Or.inl rfl)
  refine ⟨hfirst,?_⟩
  rw [hfirst]
  ext w
  constructor
  · rintro ⟨r,s,hr,hs,hw,hc⟩
    exact ⟨r,s,hr,hs,hc,hw⟩
  · rintro ⟨r,s,hr,hs,hc,hw⟩
    exact ⟨r,s,hr,hs,hw,hc⟩

/-- Identity under the stated parameter and domain assumptions: `Set.image2 (fun a b : ℂ => a+b)
(arctanhValues u) (arccothValues v)=arctanhValues ((u*v+1)/(v+u)) ∧ Set.image2 (fun a b : ℂ =>
a+b) (arctanhValues u) (arccothValues v)=arccothValues ((v+u)/(u*v+1))`. -/
@[dlmf 4.38.E19]
theorem arctanh_arccoth_values_add {u v : ℂ} (hu : u≠1 ∧ u≠ -1) (hv : v≠1 ∧ v≠ -1)
    (hp : v+u≠0) (hq : u*v+1≠0) :
    Set.image2 (fun a b : ℂ => a+b) (arctanhValues u) (arccothValues v)=arctanhValues ((u*v+1)/(v+u)) ∧
    Set.image2 (fun a b : ℂ => a+b) (arctanhValues u) (arccothValues v)=arccothValues ((v+u)/(u*v+1)) := by
  have hu1 : 1-u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu.1)
  have hu2 : 1+u ≠ 0 := fun h => hu.2 (by first | linear_combination h | linear_combination -h)
  have hv1 : v-1 ≠ 0 := sub_ne_zero.mpr hv.1
  have hv2 : v+1 ≠ 0 := fun h => hv.2 (by first | linear_combination h | linear_combination -h)
  have ht1 : (u*v+1)/(v+u) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hp]; intro h
    exact mul_ne_zero hu1 hv1 (by first | linear_combination h | linear_combination -h)
  have ht2 : (u*v+1)/(v+u) ≠ -1 := by
    rw [Ne, div_eq_iff hp]; intro h
    exact mul_ne_zero hu2 hv2 (by first | linear_combination h | linear_combination -h)
  have hs1 : (v+u)/(u*v+1) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hq]; intro h
    exact mul_ne_zero hu1 hv1 (by first | linear_combination h | linear_combination -h)
  have hs2 : (v+u)/(u*v+1) ≠ -1 := by
    rw [Ne, div_eq_iff hq]; intro h
    exact mul_ne_zero hu2 hv2 (by first | linear_combination h | linear_combination -h)
  have ht3 : 1-(u*v+1)/(v+u) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have hs3 : (v+u)/(u*v+1)-1 ≠ 0 := sub_ne_zero.mpr hs1
  have e0 : arctanhValues (u) = {w : ℂ | Complex.exp (2*w)*(1-(u)) = 1+(u)} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff hu.1 hu.2
  have e1 : arccothValues (v) = {w : ℂ | Complex.exp (2*w)*((v)-1) = (v)+1} :=
    Set.ext fun w => hypR4_mem_arccothValues_iff hv.1 hv.2
  have e2 : arctanhValues ((u*v+1)/(v+u)) = {w : ℂ | Complex.exp (2*w)*(1-((u*v+1)/(v+u))) = 1+((u*v+1)/(v+u))} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff ht1 ht2
  have e3 : arccothValues ((v+u)/(u*v+1)) = {w : ℂ | Complex.exp (2*w)*(((v+u)/(u*v+1))-1) = ((v+u)/(u*v+1))+1} :=
    Set.ext fun w => hypR4_mem_arccothValues_iff hs1 hs2
  rw [e0, e1, e2, e3, hypR4_expSet_add hu1 hu2]
  constructor
  · apply hypR4_expSet_congr (mul_ne_zero hu1 hv1) ht3
    field_simp
    ring
  · apply hypR4_expSet_congr (mul_ne_zero hu1 hv1) hs3
    field_simp
    ring

/-- The former unrestricted subtraction acquisition loses the same parity information:
at u=v=i the right side includes pi*i, which is not a difference of two inverse values. -/
theorem arcsinh_values_sub_unrestricted_counterexample :
    (π*I:ℂ)∈{w | ∃ r s : ℂ,r^2=1+I^2 ∧ s^2=1+I^2 ∧ w∈arcsinhValues (I*r-I*s)} ∧
    (π*I:ℂ)∉Set.image2 (fun a b : ℂ=>a-b) (arcsinhValues I) (arcsinhValues I) := by
  constructor
  · refine ⟨0,0,?_,?_,?_⟩ <;> simp [arcsinhValues,Complex.sinh_mul_I]
  · rintro ⟨a,ha,b,hb,hab⟩
    change Complex.sinh a=I at ha
    change Complex.sinh b=I at hb
    have hab':a=b+π*I := by linear_combination hab
    rw [hab',Complex.sinh_add_pi_mul_I,hb] at ha
    have hc:(I:ℂ)=0 := by linear_combination -ha/2
    exact Complex.I_ne_zero hc

/-- DLMF4.38.15 with compatible subtraction branches. The paired cosh equation fixes
parity without excluding parameters, including the critical values ±i. -/
@[dlmf 4.38.E15]
theorem arcsinh_values_sub (u v : ℂ) :
    Set.image2 (fun a b : ℂ => a-b) (arcsinhValues u) (arcsinhValues v)=
      {w | ∃ r s : ℂ,r^2=1+v^2 ∧ s^2=1+u^2 ∧
        w∈arcsinhValues (u*r-v*s) ∧ Complex.cosh w=s*r-u*v} := by
  ext w
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    change Complex.sinh a=u at ha
    change Complex.sinh b=v at hb
    refine ⟨Complex.cosh b,Complex.cosh a,?_,?_,?_,?_⟩
    · rw [Complex.cosh_sq,hb];ring
    · rw [Complex.cosh_sq,ha];ring
    · change Complex.sinh (a-b)=u*Complex.cosh b-v*Complex.cosh a
      rw [Complex.sinh_sub,ha,hb]
      ring
    · rw [Complex.cosh_sub,ha,hb] <;> ring
  · rintro ⟨r,s,hr,hs,hw,hc⟩
    have ha:=hyper_sinh_cosh_log_lift u s hs
    let a:=Complex.log (s+u)
    refine ⟨a,ha.1,a-w,?_,by ring⟩
    change Complex.sinh (a-w)=v
    change Complex.sinh w=u*r-v*s at hw
    rw [Complex.sinh_sub,ha.1,ha.2,hw,hc]
    linear_combination v*hs

/-- Formula under the stated hypotheses: `Set.image2 (fun a b : ℂ => a-b) (arccoshValues u)
(arccoshValues v)= {w | ∃ r : ℂ, r^2=(u^2-1)*(v^2-1) ∧ w ∈ arccoshValues (u*v-r)}`. -/
@[dlmf 4.38.E16]
theorem arccosh_values_sub (u v : ℂ) :
    Set.image2 (fun a b : ℂ => a-b) (arccoshValues u) (arccoshValues v)=
      {w | ∃ r : ℂ, r^2=(u^2-1)*(v^2-1) ∧ w ∈ arccoshValues (u*v-r)} := by
  ext w
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    change Complex.cosh a=u at ha
    change Complex.cosh b=v at hb
    refine ⟨Complex.sinh a*Complex.sinh b,?_,?_⟩
    · simp only [mul_pow,neg_sq,Complex.sinh_sq,ha,hb]
    · change Complex.cosh (a-b)=u*v-Complex.sinh a*Complex.sinh b
      rw [Complex.cosh_sub,ha,hb]
  · rintro ⟨r,hr,hc⟩
    change Complex.cosh w=u*v-r at hc
    have hs:(v-u*Complex.cosh w)^2=(Complex.sinh w*Complex.sinh (arccosh u))^2 := by
      simp only [mul_pow,Complex.sinh_sq,hyper_cosh_arccosh,hc]
      linear_combination hr
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hs|hs
    · refine ⟨-arccosh u,?_, -w-arccosh u,?_,by ring⟩
      · change Complex.cosh (-arccosh u)=u
        rw [Complex.cosh_neg,hyper_cosh_arccosh]
      · change Complex.cosh (-w-arccosh u)=v
        rw [show -w-arccosh u= -(w+arccosh u) by ring,Complex.cosh_neg,
          Complex.cosh_add,hyper_cosh_arccosh]
        linear_combination -hs
    · refine ⟨arccosh u,hyper_cosh_arccosh u,arccosh u-w,?_,by ring⟩
      change Complex.cosh (arccosh u-w)=v
      rw [Complex.cosh_sub,hyper_cosh_arccosh]
      linear_combination -hs

/-- Identity under the stated parameter and domain assumptions: `Set.image2 (fun a b : ℂ => a-b)
(arctanhValues u) (arctanhValues v)=arctanhValues ((u-v)/(1-u*v))`. -/
@[dlmf 4.38.E17]
theorem arctanh_values_sub {u v : ℂ} (hu : u≠1 ∧ u≠ -1) (hv : v≠1 ∧ v≠ -1) (hp : 1-u*v≠0) :
    Set.image2 (fun a b : ℂ => a-b) (arctanhValues u) (arctanhValues v)=arctanhValues ((u-v)/(1-u*v)) := by
  have hu1 : 1-u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu.1)
  have hu2 : 1+u ≠ 0 := fun h => hu.2 (by first | linear_combination h | linear_combination -h)
  have hv1 : 1-v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv.1)
  have hv2 : 1+v ≠ 0 := fun h => hv.2 (by first | linear_combination h | linear_combination -h)
  have ht1 : (u-v)/(1-u*v) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hp]; intro h
    exact mul_ne_zero hu1 hv2 (by first | linear_combination h | linear_combination -h)
  have ht2 : (u-v)/(1-u*v) ≠ -1 := by
    rw [Ne, div_eq_iff hp]; intro h
    exact mul_ne_zero hu2 hv1 (by first | linear_combination h | linear_combination -h)
  have ht3 : 1-(u-v)/(1-u*v) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have e0 : arctanhValues (u) = {w : ℂ | Complex.exp (2*w)*(1-(u)) = 1+(u)} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff hu.1 hu.2
  have e1 : arctanhValues (v) = {w : ℂ | Complex.exp (2*w)*(1-(v)) = 1+(v)} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff hv.1 hv.2
  have e2 : arctanhValues ((u-v)/(1-u*v)) = {w : ℂ | Complex.exp (2*w)*(1-((u-v)/(1-u*v))) = 1+((u-v)/(1-u*v))} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff ht1 ht2
  rw [e0, e1, e2, hypR4_expSet_sub hu1 hu2]
  apply hypR4_expSet_congr (mul_ne_zero hu1 hv2) ht3
  field_simp
  ring

/-- DLMF4.38.18 interpreted with shared inverse branches. Both inverse descriptions
retain the paired sinh/cosh equations, including all critical parameter values. -/
@[dlmf 4.38.E18]
theorem arcsinh_arccosh_values_sub (u v : ℂ) :
    Set.image2 (fun a b : ℂ => a - b) (arcsinhValues u) (arccoshValues v)=
      {w | ∃ r s : ℂ,r^2=1+u^2 ∧ s^2=v^2-1 ∧
        w∈arcsinhValues (u*v - r*s) ∧ Complex.cosh w=v*r - u*s} ∧
    Set.image2 (fun a b : ℂ => a - b) (arcsinhValues u) (arccoshValues v)=
      {w | ∃ r s : ℂ,r^2=1+u^2 ∧ s^2=v^2-1 ∧
        w∈arccoshValues (v*r - u*s) ∧ Complex.sinh w=u*v - r*s} := by
  have hfirst :
      Set.image2 (fun a b : ℂ => a - b) (arcsinhValues u) (arccoshValues v)=
        {w | ∃ r s : ℂ,r^2=1+u^2 ∧ s^2=v^2-1 ∧
          w∈arcsinhValues (u*v - r*s) ∧ Complex.cosh w=v*r - u*s} := by
    simpa only [one_mul,neg_one_mul,sub_eq_add_neg,arcsinhValues,Set.mem_setOf_eq] using
      hyper_mixed_inverse_fiber u v (-1) (Or.inr rfl)
  refine ⟨hfirst,?_⟩
  rw [hfirst]
  ext w
  constructor
  · rintro ⟨r,s,hr,hs,hw,hc⟩
    exact ⟨r,s,hr,hs,hc,hw⟩
  · rintro ⟨r,s,hr,hs,hc,hw⟩
    exact ⟨r,s,hr,hs,hw,hc⟩

/-- Identity under the stated parameter and domain assumptions: `Set.image2 (fun a b : ℂ => a-b)
(arctanhValues u) (arccothValues v)=arctanhValues ((u*v-1)/(v-u)) ∧ Set.image2 (fun a b : ℂ =>
a-b) (arctanhValues u) (arccothValues v)=arccothValues ((v-u)/(u*v-1))`. -/
@[dlmf 4.38.E19]
theorem arctanh_arccoth_values_sub {u v : ℂ} (hu : u≠1 ∧ u≠ -1) (hv : v≠1 ∧ v≠ -1)
    (hp : v-u≠0) (hq : u*v-1≠0) :
    Set.image2 (fun a b : ℂ => a-b) (arctanhValues u) (arccothValues v)=arctanhValues ((u*v-1)/(v-u)) ∧
    Set.image2 (fun a b : ℂ => a-b) (arctanhValues u) (arccothValues v)=arccothValues ((v-u)/(u*v-1)) := by
  have hu1 : 1-u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu.1)
  have hu2 : 1+u ≠ 0 := fun h => hu.2 (by first | linear_combination h | linear_combination -h)
  have hv1 : v-1 ≠ 0 := sub_ne_zero.mpr hv.1
  have hv2 : v+1 ≠ 0 := fun h => hv.2 (by first | linear_combination h | linear_combination -h)
  have ht1 : (u*v-1)/(v-u) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hp]; intro h
    exact mul_ne_zero hu1 hv2 (by first | linear_combination h | linear_combination -h)
  have ht2 : (u*v-1)/(v-u) ≠ -1 := by
    rw [Ne, div_eq_iff hp]; intro h
    exact mul_ne_zero hu2 hv1 (by first | linear_combination h | linear_combination -h)
  have hs1 : (v-u)/(u*v-1) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hq]; intro h
    exact mul_ne_zero hu1 hv2 (by first | linear_combination h | linear_combination -h)
  have hs2 : (v-u)/(u*v-1) ≠ -1 := by
    rw [Ne, div_eq_iff hq]; intro h
    exact mul_ne_zero hu2 hv1 (by first | linear_combination h | linear_combination -h)
  have ht3 : 1-(u*v-1)/(v-u) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have hs3 : (v-u)/(u*v-1)-1 ≠ 0 := sub_ne_zero.mpr hs1
  have e0 : arctanhValues (u) = {w : ℂ | Complex.exp (2*w)*(1-(u)) = 1+(u)} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff hu.1 hu.2
  have e1 : arccothValues (v) = {w : ℂ | Complex.exp (2*w)*((v)-1) = (v)+1} :=
    Set.ext fun w => hypR4_mem_arccothValues_iff hv.1 hv.2
  have e2 : arctanhValues ((u*v-1)/(v-u)) = {w : ℂ | Complex.exp (2*w)*(1-((u*v-1)/(v-u))) = 1+((u*v-1)/(v-u))} :=
    Set.ext fun w => hypR4_mem_arctanhValues_iff ht1 ht2
  have e3 : arccothValues ((v-u)/(u*v-1)) = {w : ℂ | Complex.exp (2*w)*(((v-u)/(u*v-1))-1) = ((v-u)/(u*v-1))+1} :=
    Set.ext fun w => hypR4_mem_arccothValues_iff hs1 hs2
  rw [e0, e1, e2, e3, hypR4_expSet_sub hu1 hu2]
  constructor
  · apply hypR4_expSet_congr (mul_ne_zero hu1 hv2) ht3
    field_simp
    ring
  · apply hypR4_expSet_congr (mul_ne_zero hu1 hv2) hs3
    field_simp
    ring

end DLMF.Elementary
end
