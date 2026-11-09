/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AsymptoticApproximations.Basics.Basic
public import DLMFMathlib.Analysis.Asymptotics.AsymptoticInversion
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Transcendental equations (DLMF §2.2)

Asymptotic solution of transcendental equations and Lagrange's reversion formula.

## Main results

* `existsUnique_root_of_isEquivalent`, `root_isEquivalent`: if `f` is continuous and strictly
  increasing on `[a, ∞)` with `f(x) ∼ x`, the equation `f(x) = y` has a unique root `x(y) > a`
  for `y > f(a)`, and `x(y) ∼ y` (DLMF 2.2.1–2.2.2).
* `existsUnique_sq_sub_log_eq`, `sq_sub_log_root_isEquivalent`, `sq_sub_log_root_sq`,
  `sq_sub_log_root_second`: the example `t² - ln t = y` (DLMF 2.2.3–2.2.6).
* `lagrange_reversion`: Lagrange's formula for the reversion of `f(x) ∼ x + f₀ + f₁x⁻¹ + ⋯`
  with the coefficients `lagrangeReversionCoeff` (DLMF 2.2.7–2.2.8).

## Implementation notes

The project's general asymptotic inversion theorem is
`Asymptotics.HasAsymptoticPowerSeries.inversion`.
-/

@[expose] public noncomputable section

open Filter Asymptotics Set
open scoped Topology

namespace DLMF.AsymptoticApproximations

/-- DLMF 2.2.1 and the statement after it: if `f` is continuous and strictly increasing on
`[a, ∞)` and `f(x) ∼ x` as `x → ∞`, then for every `y > f(a)` the equation `f(x) = y` has a
unique root `x` in `(a, ∞)`. -/
@[dlmf 2.2.E1, dlmf 2.2]
theorem existsUnique_root_of_isEquivalent {f : ℝ → ℝ} {a : ℝ} (hf : ContinuousOn f (Ici a))
    (hmono : StrictMonoOn f (Ici a)) (hfx : f ~[atTop] id) {y : ℝ} (hy : f a < y) :
    ∃! x, a < x ∧ f x = y := by
  have htop : Tendsto f atTop atTop := hfx.symm.tendsto_atTop tendsto_id
  obtain ⟨b, hb⟩ := (htop.eventually (eventually_gt_atTop y)).and (eventually_ge_atTop a)
    |>.exists
  obtain ⟨x, hx, hfx'⟩ := intermediate_value_Icc hb.2 (hf.mono Icc_subset_Ici_self)
    ⟨hy.le, hb.1.le⟩
  have hax : a < x := lt_of_le_of_ne hx.1 fun h => by subst h; exact hy.ne hfx'
  refine ⟨x, ⟨hax, hfx'⟩, fun x' hx' => ?_⟩
  exact hmono.injOn (mem_Ici.mpr hx'.1.le) (mem_Ici.mpr hax.le) (hx'.2.trans hfx'.symm)

/-- DLMF 2.2.2: under the hypotheses of 2.2.1, the root `x(y)` of `f(x) = y` in `(a, ∞)`
satisfies `x(y) ∼ y` as `y → ∞`. Any function `x(·)` that is eventually such a root is
covered. -/
@[dlmf 2.2.E2, dlmf 2.2]
theorem root_isEquivalent {f : ℝ → ℝ} {a : ℝ} (hmono : StrictMonoOn f (Ici a))
    (hfx : f ~[atTop] id) {g : ℝ → ℝ} (hg : ∀ᶠ y in atTop, a < g y ∧ f (g y) = y) :
    g ~[atTop] id := by
  have hgt : Tendsto g atTop atTop := by
    refine tendsto_atTop.mpr fun M => ?_
    set M' := max M a
    filter_upwards [hg, eventually_gt_atTop (f M')] with y hy hyM
    by_contra hlt
    push Not at hlt
    have h1 : f (g y) ≤ f M' := hmono.monotoneOn (mem_Ici.mpr hy.1.le)
      (mem_Ici.mpr (le_max_right M a)) (hlt.le.trans (le_max_left M a))
    linarith [hy.2]
  have h := hfx.comp_tendsto hgt
  refine (IsEquivalent.congr_left h ?_).symm
  filter_upwards [hg] with y hy
  simpa using hy.2

/-- The function `f(x) = x - ½ ln x` of the example 2.2.3 (with `x = t²`) is strictly
increasing on `[½, ∞)`. -/
theorem strictMonoOn_sub_half_log : StrictMonoOn (fun x : ℝ => x - Real.log x / 2)
    (Ici (1 / 2)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ fun x hx => ?_
  · refine (continuousOn_id.sub ((Real.continuousOn_log.mono fun x hx => ?_).div_const 2))
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) (mem_Ici.mp hx))
  · rw [interior_Ici] at hx
    have hx0 : 0 < x := lt_trans (by norm_num) hx
    have hd : HasDerivAt (fun x : ℝ => x - Real.log x / 2) (1 - x⁻¹ / 2) x :=
      (hasDerivAt_id x).sub ((Real.hasDerivAt_log hx0.ne').div_const 2)
    rw [hd.deriv]
    have : x⁻¹ < 2 := by
      rw [inv_lt_comm₀ hx0 (by norm_num)]; simpa [one_div] using mem_Ioi.mp hx
    linarith

/-- `x - ½ ln x ∼ x` as `x → ∞`. -/
theorem sub_half_log_isEquivalent : (fun x : ℝ => x - Real.log x / 2) ~[atTop] id := by
  have h : (fun x : ℝ => -(Real.log x / 2)) =o[atTop] id :=
    (Real.isLittleO_log_id_atTop.const_mul_left (1 / 2)).neg_left.congr_left fun x => by ring
  exact h.congr_left fun x => by simp [sub_eq_add_neg]

/-- DLMF 2.2.3: for every `y > ½(1 + ln 2)` the equation `t² - ln t = y` has a unique root
`t > 2^{-1/2}` (with `x = t²`, `f(x) = x - ½ ln x`, `a = ½`). -/
@[dlmf 2.2.E3]
theorem existsUnique_sq_sub_log_eq {y : ℝ} (hy : (1 + Real.log 2) / 2 < y) :
    ∃! t : ℝ, (Real.sqrt 2)⁻¹ < t ∧ t ^ 2 - Real.log t = y := by
  have hf0 : (fun x : ℝ => x - Real.log x / 2) (1 / 2) < y := by
    simp only [one_div, Real.log_inv]; linarith
  obtain ⟨x, ⟨hx, hfx⟩, hu⟩ := existsUnique_root_of_isEquivalent
    ((continuousOn_id.sub ((Real.continuousOn_log.mono fun x hx =>
      ne_of_gt (lt_of_lt_of_le (by norm_num) (mem_Ici.mp hx))).div_const 2)))
    strictMonoOn_sub_half_log sub_half_log_isEquivalent hf0
  have hx0 : 0 < x := lt_trans (by norm_num) hx
  have hlogsqrt : ∀ u : ℝ, 0 < u → Real.log (Real.sqrt u) = Real.log u / 2 := fun u hu => by
    rw [Real.log_sqrt hu.le]
  have hs2 : (Real.sqrt 2)⁻¹ = Real.sqrt (1 / 2) := by
    rw [Real.sqrt_div' 1 (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_one, one_div]
  refine ⟨Real.sqrt x, ⟨?_, ?_⟩, fun t ht => ?_⟩
  · rw [hs2]; exact Real.sqrt_lt_sqrt (by norm_num) hx
  · rw [Real.sq_sqrt hx0.le, hlogsqrt x hx0]; exact hfx
  · have ht0 : 0 < t := lt_trans (by positivity) ht.1
    have h1 : 1 / 2 < t ^ 2 := by
      have := pow_lt_pow_left₀ ht.1 (by positivity) (two_ne_zero)
      rwa [inv_pow, Real.sq_sqrt (by norm_num), ← one_div] at this
    have h2 := hu (t ^ 2) ⟨h1, by
      show t ^ 2 - Real.log (t ^ 2) / 2 = y
      rw [Real.log_pow]; push_cast; linarith [ht.2]⟩
    rw [← h2, Real.sqrt_sq ht0.le]

/-- Squaring the positive root reduces its leading asymptotics to inverse-function asymptotics. -/
private lemma sq_sub_log_root_sq_isEquivalent {t : ℝ → ℝ}
    (ht : ∀ᶠ y in atTop, (Real.sqrt 2)⁻¹ < t y ∧ t y ^ 2 - Real.log (t y) = y) :
    (fun y => t y ^ 2) ~[atTop] id := by
  apply root_isEquivalent strictMonoOn_sub_half_log sub_half_log_isEquivalent
  filter_upwards [ht] with y hy
  have ht0 : 0 < t y := lt_trans (by positivity) hy.1
  constructor
  · have h := pow_lt_pow_left₀ hy.1 (by positivity) two_ne_zero
    rwa [inv_pow, Real.sq_sqrt (by norm_num), ← one_div] at h
  · rw [Real.log_pow]
    push_cast
    linarith [hy.2]


/-- DLMF 2.2.4: a root `t(y) > 2^{-1/2}` of `t² - ln t = y` satisfies
`t = y^{1/2}(1 + o(1))`, that is, `t(y) ∼ y^{1/2}` as `y → ∞`. -/
@[dlmf 2.2.E4]
theorem sq_sub_log_root_isEquivalent {t : ℝ → ℝ}
    (ht : ∀ᶠ y in atTop, (Real.sqrt 2)⁻¹ < t y ∧ t y ^ 2 - Real.log (t y) = y) :
    t ~[atTop] fun y => Real.sqrt y := by
  have hs := sq_sub_log_root_sq_isEquivalent ht
  have hy : (fun y : ℝ => max y 0) =ᶠ[atTop] id := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    exact max_eq_left hy
  have hsq : (fun y => t y ^ 2) ~[atTop] fun y => max y 0 := hs.congr_right hy.symm
  have hr := hsq.rpow (fun y => le_max_right y 0) (r := (1 / 2 : ℝ))
  refine hr.congr_left ?_ |>.congr_right ?_
  · filter_upwards [ht] with y hy
    change (t y ^ 2) ^ (1 / 2 : ℝ) = t y
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (lt_trans (by positivity) hy.1).le]
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    change (max y 0) ^ (1 / 2 : ℝ) = Real.sqrt y
    rw [max_eq_left hy, ← Real.sqrt_eq_rpow]

/-- DLMF 2.2.5: `t² = y + ln t = y + ½ ln y + o(1)` as `y → ∞`. -/
@[dlmf 2.2.E5]
theorem sq_sub_log_root_sq {t : ℝ → ℝ}
    (ht : ∀ᶠ y in atTop, (Real.sqrt 2)⁻¹ < t y ∧ t y ^ 2 - Real.log (t y) = y) :
    (∀ᶠ y in atTop, t y ^ 2 = y + Real.log (t y)) ∧
      (fun y => t y ^ 2 - (y + Real.log y / 2)) =o[atTop] fun _ => (1 : ℝ) := by
  have hsq : ∀ᶠ y in atTop, t y ^ 2 = y + Real.log (t y) := by
    filter_upwards [ht] with y hy
    linarith [hy.2]
  refine ⟨hsq, ?_⟩
  have hz : ∀ᶠ y : ℝ in atTop, Real.sqrt y ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    exact (Real.sqrt_pos.mpr hy).ne'
  have hratio := (isEquivalent_iff_tendsto_one hz).mp (sq_sub_log_root_isEquivalent ht)
  have hlog := Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0) |>.tendsto.comp hratio
  rw [Real.log_one] at hlog
  apply (isLittleO_one_iff ℝ).mpr
  refine hlog.congr' ?_
  filter_upwards [ht, hsq, eventually_gt_atTop (0 : ℝ)] with y hy hsq hy0
  have ht0 : 0 < t y := lt_trans (by positivity) hy.1
  change Real.log (t y / Real.sqrt y) = t y ^ 2 - (y + Real.log y / 2)
  rw [Real.log_div ht0.ne' (Real.sqrt_pos.mpr hy0).ne', Real.log_sqrt hy0.le, hsq]
  ring

/-- DLMF 2.2.6: `t = y^{1/2}(1 + ¼ y⁻¹ ln y + o(y⁻¹))` as `y → ∞`. -/
@[dlmf 2.2.E6]
theorem sq_sub_log_root_second {t : ℝ → ℝ}
    (ht : ∀ᶠ y in atTop, (Real.sqrt 2)⁻¹ < t y ∧ t y ^ 2 - Real.log (t y) = y) :
    (fun y => t y - Real.sqrt y * (1 + y⁻¹ * Real.log y / 4)) =o[atTop]
      fun y => Real.sqrt y * y⁻¹ := by
  have hlead := sq_sub_log_root_isEquivalent ht
  have htt : Tendsto t atTop atTop := hlead.symm.tendsto_atTop Real.tendsto_sqrt_atTop
  have htn : ∀ᶠ y in atTop, t y ≠ 0 := by
    filter_upwards [ht] with y hy using (lt_trans (by positivity) hy.1).ne'
  have hr := (isEquivalent_iff_tendsto_one htn).mp hlead.symm
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp htt
  have hq : Tendsto (fun y => Real.log (t y) / (t y + Real.sqrt y)) atTop (𝓝 0) := by
    have hh := hl.div (tendsto_const_nhds.add hr) (by norm_num : (1 : ℝ) + 1 ≠ 0)
    simp only [zero_div] at hh
    refine hh.congr' ?_
    filter_upwards [ht, eventually_gt_atTop (0 : ℝ)] with y hy hy0
    have ht0 : 0 < t y := lt_trans (by positivity) hy.1
    change (Real.log (t y) / t y) / (1 + Real.sqrt y / t y) = _
    field_simp
  have he := (isLittleO_one_iff ℝ).mp (sq_sub_log_root_sq ht).2
  have hscaled := (he.div_const 2).sub ((hq.pow 2).div_const 2)
  simp only [zero_div, zero_pow two_ne_zero, sub_zero] at hscaled
  apply (isLittleO_iff_tendsto' (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    exact fun hz => False.elim ((mul_ne_zero (Real.sqrt_pos.mpr hy).ne'
      (inv_ne_zero hy.ne')) hz))).mpr
  refine hscaled.congr' ?_
  filter_upwards [ht, eventually_gt_atTop (0 : ℝ)] with y hy hy0
  have ht0 : 0 < t y := lt_trans (by positivity) hy.1
  have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hs : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy0.le
  change (t y ^ 2 - (y + Real.log y / 2)) / 2 -
      (Real.log (t y) / (t y + Real.sqrt y)) ^ 2 / 2 = _
  have heq : Real.log (t y) = (t y - Real.sqrt y) * (t y + Real.sqrt y) := by
    nlinarith [hy.2]
  rw [heq, mul_div_cancel_right₀ _ (by positivity : t y + Real.sqrt y ≠ 0)]
  field_simp
  nlinarith [hy.2]

/-- DLMF's reversion coefficients are the negatives of the McMahon coefficients. -/
theorem lagrangeReversionCoeff_eq_neg_coeff_mcMahonSeries {𝕜 : Type*}
    [NormedField 𝕜] [CharZero 𝕜] (fc : ℕ → 𝕜) (n : ℕ) :
    lagrangeReversionCoeff fc n = -PowerSeries.coeff n (mcMahonSeries (PowerSeries.mk fc)) := by
  cases n with
  | zero =>
    simpa [lagrangeReversionCoeff] using
      congrArg Neg.neg (mcMahonSeries_coeff_le_two (PowerSeries.mk fc)).1.symm
  | succ n =>
    have h := natCast_mul_coeff_mcMahonSeries (PowerSeries.mk fc) (Nat.succ_pos n)
    dsimp only [lagrangeReversionCoeff]
    have hn : ((n + 1 : ℕ) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    apply mul_left_cancel₀ hn
    rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul, mul_neg, h, neg_neg]

/-- The first three coefficients in DLMF's Lagrange reversion formula. -/
theorem lagrangeReversionCoeff_le_two {𝕜 : Type*} [NormedField 𝕜] [CharZero 𝕜]
    (fc : ℕ → 𝕜) :
    lagrangeReversionCoeff fc 0 = fc 0 ∧ lagrangeReversionCoeff fc 1 = fc 1 ∧
      lagrangeReversionCoeff fc 2 = fc 2 + fc 0 * fc 1 := by
  have h := mcMahonSeries_coeff_le_two (PowerSeries.mk fc)
  simp only [PowerSeries.coeff_mk] at h
  simp only [lagrangeReversionCoeff_eq_neg_coeff_mcMahonSeries, h.1, h.2.1, h.2.2, neg_neg]
  exact ⟨True.intro, True.intro, True.intro⟩

/-- Affine translation has no positive-degree reversion coefficients: its inverse is
exactly `y ↦ y-a`. -/
theorem lagrangeReversionCoeff_affine {𝕜 : Type*} [NormedField 𝕜] [CharZero 𝕜] (a : 𝕜) :
    lagrangeReversionCoeff (fun n => if n = 0 then a else 0) =
      (fun n => if n = 0 then a else 0) := by
  have hP : PowerSeries.mk (fun n : ℕ => if n = 0 then a else 0) = PowerSeries.C a := by
    ext n
    simp [PowerSeries.coeff_C]
  have hM : mcMahonSeries (PowerSeries.C a) = -(PowerSeries.C a) := by
    simpa only [PowerSeries.subst_C, ← PowerSeries.C_apply] using!
      (mcMahonSeries_spec (PowerSeries.C a)).2
  funext n
  rw [lagrangeReversionCoeff_eq_neg_coeff_mcMahonSeries, hP, hM]
  simp [PowerSeries.coeff_C]

/-- Lagrange reversion on sets in a normed field, including complex inverse branches.
The inverse branch is selected by `x(y) ∼ y` and eventual membership in the original set. -/
theorem lagrange_reversion_of_isEquivalent {𝕜 : Type*} [NormedField 𝕜] [CharZero 𝕜]
    {S T : Set 𝕜} {f x : 𝕜 → 𝕜} {fc : ℕ → 𝕜}
    (hf : HasPoincareExpansion S fc fun z => f z - z)
    (hx : x ~[Bornology.cobounded 𝕜 ⊓ 𝓟 T] id)
    (hxy : ∀ᶠ y in Bornology.cobounded 𝕜 ⊓ 𝓟 T, x y ∈ S ∧ f (x y) = y) :
    HasPoincareExpansion T (fun s => -lagrangeReversionCoeff fc s) (fun y => x y - y) := by
  let l := Bornology.cobounded 𝕜 ⊓ 𝓟 T
  have hnorm : Tendsto (fun y : 𝕜 => ‖y‖) l atTop :=
    tendsto_norm_cobounded_atTop.mono_left inf_le_left
  obtain ⟨C, hC, hb⟩ := hx.symm.isBigO.exists_pos
  have hxc : Tendsto x l (Bornology.cobounded 𝕜) := by
    apply tendsto_norm_atTop_iff_cobounded.mp
    refine tendsto_atTop.mpr fun R => ?_
    filter_upwards [hb.bound, hnorm.eventually (eventually_ge_atTop (C * R))] with y hy hyR
    exact (mul_le_mul_iff_right₀ hC).mp (hyR.trans hy)
  have hxs : Tendsto x l (Bornology.cobounded 𝕜 ⊓ 𝓟 S) :=
    tendsto_inf.mpr ⟨hxc, tendsto_principal.mpr (hxy.mono fun _ h => h.1)⟩
  have hi := HasAsymptoticPowerSeries.mcMahon_inversion
    (ξ := id) (C := PowerSeries.mk fc)
    (tendsto_inv₀_cobounded.mono_left inf_le_left)
    ((Bornology.eventually_ne_cobounded (0 : 𝕜)).filter_mono inf_le_left)
    (by simpa [HasAsymptoticPowerSeries, HasPoincareExpansion] using hf) hxs
    (T := id) (hxy.mono fun _ h => by simpa using h.2)
  exact hi.congr_coeff (funext fun n => by
    simp only [lagrangeReversionCoeff_eq_neg_coeff_mcMahonSeries, neg_neg])

/-- DLMF 2.2.7–2.2.8 (Lagrange's formula for the reversion of series): if
`f(x) ∼ x + f₀ + f₁x⁻¹ + f₂x⁻² + ⋯` as `x → +∞` (2.2.7) and `x(y) → ∞` solves `f(x(y)) = y`
for large `y`, then `x(y) ∼ y - F₀ - F₁y⁻¹ - F₂y⁻² - ⋯` as `y → +∞`, where `F₀ = f₀` and `sFₛ` is
the coefficient of `x⁻¹` in the expansion of `f(x)ˢ` (`lagrangeReversionCoeff`). Expansions
as `x → +∞` are Poincaré expansions on `𝐗 = (0, ∞)`. -/
@[dlmf 2.2.E7, dlmf 2.2.E8]
theorem lagrange_reversion {f : ℝ → ℝ} {fc : ℕ → ℝ}
    (hf : HasPoincareExpansion (Ioi 0) fc fun x => f x - x) {x : ℝ → ℝ}
    (hx : Tendsto x atTop atTop) (hxy : ∀ᶠ y in atTop, f (x y) = y) :
    HasPoincareExpansion (Ioi 0) (fun s => -lagrangeReversionCoeff fc s) fun y => x y - y := by
  have hl : Bornology.cobounded ℝ ⊓ 𝓟 (Ioi (0 : ℝ)) = atTop := by
    apply le_antisymm
    · change Tendsto id (Bornology.cobounded ℝ ⊓ 𝓟 (Ioi (0 : ℝ))) atTop
      refine tendsto_atTop.mpr fun b => ?_
      have hnorm := (tendsto_norm_cobounded_atTop.eventually (eventually_ge_atTop b)).filter_mono
        (show Bornology.cobounded ℝ ⊓ 𝓟 (Ioi (0 : ℝ)) ≤ Bornology.cobounded ℝ from inf_le_left)
      have hpos : ∀ᶠ y in Bornology.cobounded ℝ ⊓ 𝓟 (Ioi (0 : ℝ)), 0 < y :=
        eventually_inf_principal.mpr (Eventually.of_forall fun y hy => hy)
      filter_upwards [hnorm, hpos] with y hy hypos
      simpa only [id_eq, Real.norm_eq_abs, abs_of_pos hypos] using hy
    · exact le_inf IsOrderBornology.atTop_le_cobounded
        (le_principal_iff.mpr (Ioi_mem_atTop 0))
  rw [HasPoincareExpansion, hl] at hf ⊢
  have hseries : HasAsymptoticPowerSeries atTop (fun y : ℝ => y⁻¹)
      (PowerSeries.mk fc) (fun y => f y - y) := by simpa [HasAsymptoticPowerSeries] using hf
  have hinv := hasAsymptoticPowerSeries_mcMahon_atTop hseries hx
    (T := id) (hxy.mono fun y hy => by simpa using hy)
  exact hinv.congr_coeff (funext fun n => by
    simp only [lagrangeReversionCoeff_eq_neg_coeff_mcMahonSeries, neg_neg])

end DLMF.AsymptoticApproximations
