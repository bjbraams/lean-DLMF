/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.SymmetricRelations
public import DLMFMathlib.Analysis.Integral.PrincipalValue
public import DLMFMathlib.Analysis.Integral.PrincipalValueExcision

/-!
# Principal values of `R_J` (DLMF §19.16(i), 19.21.15)

For real `p < 0` DLMF defines `R_J(x, y, z, p)` as the Cauchy principal value of
`(3/2) ∫₀^∞ dt/(s(t)(t + p))` about `t = -p`. We show that the integrand minus its singular part
`s(-p)⁻¹/(t + p)` is integrable, so that the principal value exists and equals the limit of the
excised integrals for every excision `[-p - α, -p + β]` with `α, β → 0⁺` and `α/β → 1`. This
makes it possible to transport the principal value through a change of variables. As an
application we prove the change of parameter (19.21.15) of `R_J(0, y, z, p)` by the inversion
`t ↦ yz/t`, including the principal-value case `p, q < 0`.

## Main results

* `integrableOn_carlsonRootProduct_mul_sub_inv_sub_indicator`: the integrand of `R_J(x, y, z, -c)`
  minus its singular part is integrable on `(0, ∞)`.
* `tendsto_integral_symmetricEllipticRJ_of_neg`, `tendsto_integral_symmetricEllipticRJ_of_neg_symm`:
  the excised integrals converge to `(2/3) R_J(x, y, z, p)` for `p < 0`.
* `carlsonRootProduct_zero_inv_ofReal`, `carlsonRootProduct_zero_inv_mul_add_inv`: the behaviour of
  the integrand of `R_J(0, y, z, p)` under `t ↦ yz/t`.
* `mul_symmetricEllipticRJ_zero_add_mul`: DLMF 19.21.15, `p R_J(0, y, z, p) + q R_J(0, y, z, q) =
  3 R_F(0, y, z)` for real `pq = yz > 0`.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-- Off an open interval `(a, b)` about `c > 0` (with `a > 0`), the integrand
`(s(t)(t - c))⁻¹` of `R_J(x, y, z, -c)` is integrable on `(0, ∞)`. -/
theorem integrableOn_carlsonRootProduct_mul_sub_inv_diff_Ioo {x y z : ℂ}
    (hx : x ∈ slitPlane ∨ x = 0)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) {a b c : ℝ} (hac : a < c) (hcb : c < b) :
    IntegrableOn (fun t : ℝ => (carlsonRootProduct x y z t * ((t : ℂ) - c))⁻¹)
        (Ioi 0 \ Ioo a b) := by
  have hk := integrableOn_symmetricEllipticRJ_integrand hx hy hz one_mem_slitPlane
  set d := min (c - a) (b - c) with hd
  have hd0 : 0 < d := lt_min (by linarith) (by linarith)
  have hm : MeasurableSet (Ioi (0 : ℝ) \ Ioo a b) := measurableSet_Ioi.diff measurableSet_Ioo
  set kf : ℝ → ℂ := fun t : ℝ => (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y) ^ (1 / 2 : ℂ) *
        ((t : ℂ) + z) ^ (1 / 2 : ℂ) * ((t : ℂ) + 1))⁻¹ with hkf
  refine IntegrableOn.congr_fun (f := fun t => kf t * (((t : ℂ) + 1) / ((t : ℂ) - c))) ?_
    (fun t ht => ?_) hm
  · refine Integrable.mono' ((hk.mono_set sdiff_subset).norm.mul_const (1 + (|c| + 1) / d))
      ((hk.mono_set sdiff_subset).aestronglyMeasurable.mul
        (by fun_prop : Measurable fun t : ℝ => ((t : ℂ) + 1) / ((t : ℂ) - c)).aestronglyMeasurable)
      ((ae_restrict_mem hm).mono fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    have htd : d ≤ |t - c| := by
      by_contra hc'
      push Not at hc'
      refine ht.2 ⟨?_, ?_⟩
      · have := (abs_lt.mp (lt_of_lt_of_le hc' (min_le_left _ _))).1; linarith
      · have := (abs_lt.mp (lt_of_lt_of_le hc' (min_le_right _ _))).2; linarith
    rw [norm_mul]
    gcongr
    rw [show ((t : ℂ) + 1) / ((t : ℂ) - c) = ((((t + 1) / (t - c)) : ℝ) : ℂ) by push_cast; rfl,
      norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : 0 < t + 1)]
    have hap : 0 < |t - c| := hd0.trans_le htd
    rw [div_le_iff₀ hap]
    have h1 : t + 1 ≤ |t - c| + (|c| + 1) := by linarith [le_abs_self (t - c), le_abs_self c]
    have h2 : (|c| + 1) / d * |t - c| ≥ |c| + 1 := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hd0]
      nlinarith [abs_nonneg c]
    nlinarith
  · have ht0 : 0 < t := ht.1
    have h1 : (t : ℂ) + 1 ≠ 0 := by
      rw [← ofReal_one, ← ofReal_add]; exact ofReal_ne_zero.mpr (by linarith)
    have htc : (t : ℂ) - c ≠ 0 := by
      rw [← ofReal_sub]; refine ofReal_ne_zero.mpr fun h => ht.2 ⟨?_, ?_⟩ <;> linarith
    simp only [hkf, carlsonRootProduct, mul_inv, div_eq_mul_inv]
    field_simp

/-- `t ↦ s(t)⁻¹` is real-differentiable at `t > 0`. -/
theorem differentiableAt_carlsonRootProduct_inv {x y z : ℂ} (hx : x ∈ slitPlane ∨ x = 0)
    (hy : y ∈ slitPlane ∨ y = 0) (hz : z ∈ slitPlane ∨ z = 0) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (fun u : ℝ => (carlsonRootProduct x y z u)⁻¹) t := by
  have hsx := ofReal_pos_add_mem_slitPlane ht hx
  have hsy := ofReal_pos_add_mem_slitPlane ht hy
  have hsz := ofReal_pos_add_mem_slitPlane ht hz
  have he : DifferentiableAt ℂ (fun w : ℂ => ((w + x) ^ (1 / 2 : ℂ) * (w + y) ^ (1 / 2 : ℂ) *
      (w + z) ^ (1 / 2 : ℂ))⁻¹) (t : ℂ) :=
    ((((differentiableAt_id.add_const x).cpow_const hsx).mul
      ((differentiableAt_id.add_const y).cpow_const hsy)).mul
      ((differentiableAt_id.add_const z).cpow_const hsz)).inv
      (mul_ne_zero (mul_ne_zero (ofReal_pos_add_cpow_half_ne_zero ht hx)
        (ofReal_pos_add_cpow_half_ne_zero ht hy)) (ofReal_pos_add_cpow_half_ne_zero ht hz))
  exact he.hasDerivAt.comp_ofReal.differentiableAt

/-- The integrand of `R_J(x, y, z, -c)`, `c > 0`, minus its singular part
`s(c)⁻¹/(t - c)` on `[c/2, 3c/2]`, is integrable on `(0, ∞)`. -/
theorem integrableOn_carlsonRootProduct_mul_sub_inv_sub_indicator {x y z : ℂ}
    (hx : x ∈ slitPlane ∨ x = 0) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) {c : ℝ}
    (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (carlsonRootProduct x y z t * ((t : ℂ) - c))⁻¹ -
      (Icc (c / 2) (3 * c / 2)).indicator
        (fun t : ℝ => (carlsonRootProduct x y z c)⁻¹ / ((t : ℂ) - c)) t) (Ioi 0) := by
  set a := c / 2
  set b := 3 * c / 2
  have hac : a < c := by simp only [a]; linarith
  have hcb : c < b := by simp only [b]; linarith
  have ha0 : 0 < a := by simp only [a]; linarith
  set f : ℝ → ℂ := fun t => (carlsonRootProduct x y z t)⁻¹ with hf
  have hfc : ContinuousOn f (Icc a b) := fun t ht =>
    (differentiableAt_carlsonRootProduct_inv hx (Or.inl hy) (Or.inl hz)
      (ha0.trans_le ht.1)).continuousAt.continuousWithinAt
  have h1 := pv_integrableOn_sub_of_differentiableAt (hfc.integrableOn_Icc)
    (differentiableAt_carlsonRootProduct_inv hx (Or.inl hy) (Or.inl hz) hc)
  have hsplit : Ioi (0 : ℝ) ⊆ (Ioi 0 \ Ioo a b) ∪ Icc a b := by
    intro t ht
    by_cases h : t ∈ Ioo a b
    · exact Or.inr ⟨h.1.le, h.2.le⟩
    · exact Or.inl ⟨ht, h⟩
  refine IntegrableOn.mono_set (IntegrableOn.union ?_ ?_) hsplit
  · refine (integrableOn_carlsonRootProduct_mul_sub_inv_diff_Ioo hx hy hz hac hcb).sub ?_
    rw [integrableOn_indicator_iff measurableSet_Icc.nullMeasurableSet]
    refine IntegrableOn.of_measure_zero (measure_mono_null (t := {a, b}) ?_
      ((Set.toFinite _).measure_zero _))
    rintro t ⟨⟨h1, h2⟩, -, h3⟩
    simp only [mem_Ioo, not_and_or, not_lt] at h3
    rcases h3 with h3 | h3
    · exact Or.inl (le_antisymm h3 h1)
    · exact Or.inr (le_antisymm h2 h3)
  · refine h1.congr_fun (fun t ht => ?_) measurableSet_Icc
    rw [indicator_of_mem ht]
    simp only [hf, mul_inv, div_eq_mul_inv]


/-- For real `p < 0`, the integrals of `(s(t)(t + p))⁻¹` over `(0, ∞)` with an interval
`[-p - α, -p + β]` excised converge to `(2/3) R_J(x, y, z, p)` (the Cauchy principal value) as
`α, β → 0⁺` with `α/β → 1`. -/
theorem tendsto_integral_symmetricEllipticRJ_of_neg {x y z : ℂ} (hx : x ∈ slitPlane ∨ x = 0)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) {p : ℝ} (hp : p < 0) {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {α β : ι → ℝ} (hα : Tendsto α l (𝓝[>] 0))
    (hβ : Tendsto β l (𝓝[>] 0)) (hαβ : Tendsto (fun i => α i / β i) l (𝓝 1)) :
    Tendsto (fun i => ∫ t in Ioi 0 \ Icc (-p - α i) (-p + β i),
      (carlsonRootProduct x y z t * ((t : ℂ) + p))⁻¹) l
          (𝓝 ((2 / 3) * symmetricEllipticRJ x y z p)) := by
  have hc : 0 < -p := by linarith
  have hG := integrableOn_carlsonRootProduct_mul_sub_inv_sub_indicator hx hy hz hc
  have hsub : Icc (-p / 2) (3 * -p / 2) ⊆ Ioi 0 := fun t ht => by
    simp only [mem_Ioi]; linarith [ht.1]
  have h1 := tendsto_setIntegral_diff_Icc_symm_of_integrableOn_sub _ (by linarith)
    (by linarith) measurableSet_Ioi hsub hG
  have h2 := tendsto_setIntegral_diff_Icc_of_integrableOn_sub _ (by linarith)
    (by linarith) measurableSet_Ioi hsub hG hα hβ hαβ
  simp only [ofReal_neg, sub_neg_eq_add] at h1 h2
  have hneg : IsNegReal (p : ℂ) := ⟨by simp, by simpa using hp⟩
  have hRJ : symmetricEllipticRJ x y z p = (3 / 2) * principalValueIoi
      (fun t => (carlsonRootProduct x y z t * ((t : ℂ) + p))⁻¹) (-p) := by
    simp only [symmetricEllipticRJ, hneg, ↓reduceIte, ofReal_re]
  rw [hRJ, principalValueIoi, h1.limUnder_eq]
  convert h2 using 2
  ring

/-- For real `p < 0`, the symmetric truncations of `∫₀^∞ (s(t)(t + p))⁻¹ dt` about `t = -p`
converge to `(2/3) R_J(x, y, z, p)`: the Cauchy principal value defining `R_J` exists. -/
theorem tendsto_integral_symmetricEllipticRJ_of_neg_symm {x y z : ℂ} (hx : x ∈ slitPlane ∨ x = 0)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) {p : ℝ} (hp : p < 0) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi 0 \ Icc (-p - ε) (-p + ε),
      (carlsonRootProduct x y z t * ((t : ℂ) + p))⁻¹) (𝓝[>] 0)
          (𝓝 ((2 / 3) * symmetricEllipticRJ x y z p)) := by
  refine tendsto_integral_symmetricEllipticRJ_of_neg hx hy hz hp tendsto_id tendsto_id
    (tendsto_const_nhds.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (div_self (ne_of_gt hε)).symm

/-- For real `u > 0` and `y, z ≥ 0`, `s(u) = √(u (u + y)(u + z))` with `x = 0`. -/
theorem carlsonRootProduct_zero_ofReal {y z u : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) (hu : 0 < u) :
    carlsonRootProduct 0 y z u = ((√(u * (u + y) * (u + z)) : ℝ) : ℂ) := by
  rw [carlsonRootProduct, add_zero, ← ofReal_add, ← ofReal_add, Carlson.ofReal_cpow_half hu.le,
    Carlson.ofReal_cpow_half (by linarith), Carlson.ofReal_cpow_half (by linarith),
    Real.sqrt_mul (by positivity), Real.sqrt_mul hu.le]
  push_cast
  ring

/-- Under `t ↦ yz/t`, `s(yz/t) = (yz/t²) s(t)` (with `x = 0`). -/
theorem carlsonRootProduct_zero_inv_ofReal {y z t : ℝ} (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) :
    carlsonRootProduct 0 y z (y * z / t) = (((y * z / t ^ 2) : ℝ) : ℂ) *
        carlsonRootProduct 0 y z t := by
  rw [carlsonRootProduct_zero_ofReal hy.le hz.le (by positivity),
      carlsonRootProduct_zero_ofReal hy.le hz.le ht,
    ← ofReal_mul]
  congr 1
  rw [← Real.sqrt_sq (by positivity : 0 ≤ y * z / t ^ 2), ← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp
  ring


/-- The integrand identity behind DLMF 19.21.15: for `t > 0`, `t + p ≠ 0` and `pq = yz`,
`(yz/t²) (s(yz/t)(yz/t + q))⁻¹ = q⁻¹ s(t)⁻¹ - (p/q)(s(t)(t + p))⁻¹` (with `x = 0`). -/
theorem carlsonRootProduct_zero_inv_mul_add_inv {y z p q t : ℝ} (hy : 0 < y)
    (hz : 0 < z) (hp : p ≠ 0)
    (hpq : p * q = y * z) (ht : 0 < t) (htp : t + p ≠ 0) :
    (y * z / t ^ 2) • (carlsonRootProduct 0 y z (y * z / t) * (((y * z / t : ℝ) : ℂ) + q))⁻¹ =
      (q : ℂ)⁻¹ * (carlsonRootProduct 0 y z t)⁻¹ -
        ((p / q : ℝ) : ℂ) * (carlsonRootProduct 0 y z t * ((t : ℂ) + p))⁻¹ := by
  have hq : q ≠ 0 := by
    rintro rfl; rw [mul_zero] at hpq; exact (mul_pos hy hz).ne' hpq.symm
  have hS : carlsonRootProduct 0 y z t ≠ 0 := by
    rw [carlsonRootProduct_zero_ofReal hy.le hz.le ht]
    exact ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [carlsonRootProduct_zero_inv_ofReal hy hz ht, real_smul]
  have hq' : (q : ℂ) = y * z / p := by
    rw [eq_div_iff (ofReal_ne_zero.mpr hp)]; exact_mod_cast (by linarith : q * p = y * z)
  have htp' : (t : ℂ) + p ≠ 0 := by exact_mod_cast htp
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hp' : (p : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp
  have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  have hz' : (z : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz.ne'
  push_cast
  rw [hq']
  field_simp
  ring_nf
  rw [← add_mul, show (t : ℂ) * p + t ^ 2 = t * (t + p) by ring, mul_assoc, mul_inv_cancel₀ htp',
    mul_one]


/-- DLMF 19.21.15 for real `p, q ≠ 0` with `pq = yz`, `y, z > 0` (Cauchy principal values when
`p, q < 0`): `p R_J(0, y, z, p) + q R_J(0, y, z, q) = 3 R_F(0, y, z)`. -/
theorem mul_symmetricEllipticRJ_zero_add_mul {y z p q : ℝ} (hy : 0 < y) (hz : 0 < z) (hp : p ≠ 0)
    (hpq : p * q = y * z) :
    (p : ℂ) * symmetricEllipticRJ 0 y z p + (q : ℂ) * symmetricEllipticRJ 0 y z q = 3 *
        symmetricEllipticRF 0 y z := by
  have hK : 0 < y * z := mul_pos hy hz
  have hq : q ≠ 0 := by rintro rfl; rw [mul_zero] at hpq; exact hK.ne' hpq.symm
  have hy' : (y : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hy
  have hz' : (z : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hz
  set S : ℝ → ℂ := fun t => (carlsonRootProduct 0 y z t)⁻¹ with hSdef
  have hSi : IntegrableOn S (Ioi 0) :=
      integrableOn_symmetricEllipticRF_integrand (Or.inr rfl) hy' hz'
  have hRF : symmetricEllipticRF 0 y z = (1 / 2) * ∫ t in Ioi (0 : ℝ), S t := rfl
  have hS0 : ∀ t : ℝ, 0 < t → carlsonRootProduct 0 y z t ≠ 0 := fun t ht => by
    rw [carlsonRootProduct_zero_ofReal hy.le hz.le ht]
    exact ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  set ψ : ℝ → ℝ → ℂ := fun r u => (carlsonRootProduct 0 y z u * ((u : ℂ) + r))⁻¹ with hψ
  have hpre : (fun t : ℝ => y * z / t) ⁻¹' Ioi 0 = Ioi 0 := by
    ext t; simp only [mem_preimage, mem_Ioi]
    constructor
    · intro h; by_contra h'; push Not at h'
      exact absurd h (not_lt.mpr (div_nonpos_of_nonneg_of_nonpos hK.le h'))
    · intro h; positivity
  rcases lt_or_gt_of_ne hp with hpn | hpp
  · have hqn : q < 0 := by
      by_contra h; push Not at h; nlinarith [mul_nonpos_of_nonpos_of_nonneg hpn.le h]
    set c := -p with hcdef
    set c' := -q with hc'def
    have hc : 0 < c := by linarith
    have hc' : 0 < c' := by linarith
    have hcc : c * c' = y * z := by rw [hcdef, hc'def, ← hpq]; ring
    set α : ℝ → ℝ := fun ε => c * ε / (c' + ε) with hαdef
    set β : ℝ → ℝ := fun ε => c * ε / (c' - ε) with hβdef
    have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < c' :=
      Ioo_mem_nhdsGT hc'
    have hα : Tendsto α (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Tendsto α (𝓝 0) (𝓝 (α 0)) := by
          refine ContinuousAt.tendsto ?_
          simp only [hαdef]
          exact (continuousAt_const.mul continuousAt_id).div
            (continuousAt_const.add continuousAt_id) (by simp; linarith)
        simpa [hαdef] using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [hsmall] with ε h
        simp only [hαdef, mem_Ioi]; exact div_pos (by nlinarith) (by linarith)
    have hβ : Tendsto β (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Tendsto β (𝓝 0) (𝓝 (β 0)) := by
          refine ContinuousAt.tendsto ?_
          simp only [hβdef]
          exact (continuousAt_const.mul continuousAt_id).div
            (continuousAt_const.sub continuousAt_id) (by simp; linarith)
        simpa [hβdef] using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [hsmall] with ε h
        simp only [hβdef, mem_Ioi]; exact div_pos (by nlinarith) (by linarith [h.2])
    have hαβ : Tendsto (fun ε => α ε / β ε) (𝓝[>] 0) (𝓝 1) := by
      have h1 : Tendsto (fun ε : ℝ => (c' - ε) / (c' + ε)) (𝓝 0) (𝓝 ((c' - 0) / (c' + 0))) :=
        ((continuous_const.sub continuous_id).tendsto 0).div
          ((continuous_const.add continuous_id).tendsto 0) (by simp; linarith)
      rw [sub_zero, add_zero, div_self hc'.ne'] at h1
      refine (h1.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [hsmall] with ε h
      simp only [hαdef, hβdef]
      have h1 : c' + ε ≠ 0 := by linarith [h.1]
      have h2 : c' - ε ≠ 0 := by linarith [h.2]
      have h3 : c * ε ≠ 0 := by nlinarith [h.1]
      have h4 : ε ≠ 0 := h.1.ne'
      field_simp
    -- the preimage of a symmetric truncation
    have hpreε : ∀ ε, 0 < ε → ε < c' → (fun t : ℝ => y * z / t) ⁻¹' (Ioi 0 \ Icc (c' - ε) (c' + ε))
        = Ioi 0 \ Icc (c - α ε) (c + β ε) := by
      intro ε h0 h1
      have e1 : c - α ε = y * z / (c' + ε) := by
        simp only [hαdef]; rw [← hcc]; field_simp; ring
      have e2 : c + β ε = y * z / (c' - ε) := by
        simp only [hβdef]; rw [← hcc]; field_simp; ring
      rw [e1, e2]
      ext t
      simp only [mem_preimage, Set.mem_sdiff, mem_Ioi, mem_Icc]
      constructor
      · rintro ⟨h2, h3⟩
        have ht : 0 < t := by
          by_contra h'; push Not at h'
          exact absurd h2 (not_lt.mpr (div_nonpos_of_nonneg_of_nonpos hK.le h'))
        refine ⟨ht, fun ⟨h4, h5⟩ => h3 ⟨?_, ?_⟩⟩
        · rw [le_div_iff₀ ht]; rw [le_div_iff₀ (by linarith)] at h5; nlinarith
        · rw [div_le_iff₀ ht]; rw [div_le_iff₀ (by linarith)] at h4; nlinarith
      · rintro ⟨ht, h3⟩
        refine ⟨by positivity, fun ⟨h4, h5⟩ => h3 ⟨?_, ?_⟩⟩
        · rw [div_le_iff₀ ht] at h5; rw [div_le_iff₀ (by linarith)]; nlinarith
        · rw [le_div_iff₀ ht] at h4; rw [le_div_iff₀ (by linarith)]; nlinarith
    -- the substitution on each truncation
    have hkey : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ u in Ioi 0 \ Icc (-q - ε) (-q + ε), ψ q u =
        (q : ℂ)⁻¹ * (∫ t in Ioi 0 \ Icc (-p - α ε) (-p + β ε), S t) -
          ((p / q : ℝ) : ℂ) * ∫ t in Ioi 0 \ Icc (-p - α ε) (-p + β ε), ψ p t := by
      filter_upwards [hsmall] with ε h
      have ha : 0 < α ε := div_pos (by nlinarith [h.1]) (by linarith)
      have hb : 0 < β ε := div_pos (by nlinarith [h.1]) (by linarith [h.2])
      have hsub0 : Ioi 0 \ Icc (-q - ε) (-q + ε) ⊆ Ioi (0 : ℝ) := sdiff_subset
      rw [setIntegral_comp_const_div hK (measurableSet_Ioi.diff measurableSet_Icc) hsub0,
        hpreε ε h.1 h.2]
      have hm : MeasurableSet (Ioi (0 : ℝ) \ Icc (c - α ε) (c + β ε)) :=
        measurableSet_Ioi.diff measurableSet_Icc
      have hJi : IntegrableOn (ψ p) (Ioi (0 : ℝ) \ Icc (c - α ε) (c + β ε)) := by
        have := integrableOn_carlsonRootProduct_mul_sub_inv_diff_Ioo (Or.inr rfl) hy' hz'
          (a := c - α ε) (b := c + β ε) (c := c) (by linarith) (by linarith)
        refine (this.mono_set (sdiff_subset_sdiff_right Ioo_subset_Icc_self)).congr_fun
          (fun t _ => ?_) hm
        simp only [hψ, hcdef, ofReal_neg, sub_neg_eq_add]
      rw [← integral_const_mul, ← integral_const_mul, ← integral_sub
        ((hSi.mono_set sdiff_subset).const_mul _) (hJi.const_mul _)]
      refine setIntegral_congr_fun hm fun t ht => ?_
      refine carlsonRootProduct_zero_inv_mul_add_inv hy hz hp hpq ht.1 fun h => ht.2 ⟨?_, ?_⟩
      · linarith
      · linarith
    have hL := tendsto_integral_symmetricEllipticRJ_of_neg_symm (Or.inr rfl) hy' hz' hqn
    have hR1 : Tendsto (fun ε => ∫ t in Ioi 0 \ Icc (-p - α ε) (-p + β ε), S t) (𝓝[>] 0)
        (𝓝 (∫ t in Ioi (0 : ℝ), S t)) := by
      have := tendsto_setIntegral_diff_Icc_of_integrableOn_sub (F := S) (S := Ioi 0) (a := c / 2)
        (b := 3 * c / 2) (c := c) 0 (by linarith) (by linarith) measurableSet_Ioi
        (fun t ht => by simp only [mem_Ioi]; linarith [ht.1]) (by simpa using hSi) hα hβ hαβ
      simpa using this
    have hR2 := tendsto_integral_symmetricEllipticRJ_of_neg (Or.inr rfl) hy' hz' hpn hα hβ hαβ
    have hR := (hR1.const_mul ((q : ℂ)⁻¹)).sub (hR2.const_mul ((p / q : ℝ) : ℂ))
    have heq := tendsto_nhds_unique (hL.congr' hkey) hR
    rw [hRF]
    have hq' : (q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq
    push_cast at heq
    field_simp at heq
    linear_combination (1 / 2 : ℂ) * heq
  · have hqp : 0 < q := by
      by_contra h; push Not at h; nlinarith [mul_nonpos_of_nonneg_of_nonpos hpp.le h]
    have hpS : (p : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hpp
    have hqS : (q : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hqp
    have hJ : ∀ r : ℝ, 0 < r → symmetricEllipticRJ 0 y z r = (3 / 2) * ∫ t in Ioi (0 : ℝ), ψ r t :=
      fun r hr => by
        rw [symmetricEllipticRJ]
        simp only [not_isNegReal_of_mem_slitPlane (ofReal_mem_slitPlane.mpr hr), ite_false]
        rfl
    have hJpi : IntegrableOn (ψ p) (Ioi 0) :=
      integrableOn_symmetricEllipticRJ_integrand (Or.inr rfl) hy' hz' hpS
    have hsubst : ∫ u in Ioi (0 : ℝ), ψ q u =
        (q : ℂ)⁻¹ * (∫ t in Ioi (0 : ℝ), S t) -
          ((p / q : ℝ) : ℂ) * ∫ t in Ioi (0 : ℝ), ψ p t := by
      rw [setIntegral_comp_const_div hK measurableSet_Ioi subset_rfl, hpre,
        ← integral_const_mul, ← integral_const_mul, ← integral_sub (hSi.const_mul _)
          (hJpi.const_mul _)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      exact carlsonRootProduct_zero_inv_mul_add_inv hy hz hp hpq ht (by linarith [ht.out])
    rw [hJ p hpp, hJ q hqp, hsubst, hRF]
    have hq' : (q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq
    push_cast
    field_simp
    ring

end DLMF.EllipticIntegrals
