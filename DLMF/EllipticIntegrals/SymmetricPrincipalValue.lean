/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.LegendreIdentities
public import DLMF.EllipticIntegrals.SymmetricLegendreConnection
public import DLMFMathlib.Analysis.Integral.PrincipalValue
public import DLMFMathlib.Analysis.Integral.PrincipalValueExcision
public import DLMFMathlib.Analysis.Integral.ImproperDerivatives
public import DLMFMathlib.Analysis.Integral.PrincipalValueLogarithm

/-!
# Principal values and the change of parameter of `R_J` (DLMF §19.16(i), §19.21(iii))

For real `p < 0` DLMF defines `R_J(x, y, z, p)` as the Cauchy principal value of
`(3/2) ∫₀^∞ dt/(s(t)(t + p))` about `t = -p`. We show that the integrand minus its singular part
`s(-p)⁻¹/(t + p)` is integrable, so that the principal value exists and equals the limit of the
excised integrals for every excision `[-p - α, -p + β]` with `α, β → 0⁺` and `α/β → 1`. This
makes it possible to transport the principal value through a change of variables. The complete
case (19.21.15) follows by the inversion `t ↦ yz/t`. For the general change of parameter
(19.21.12–19.21.13), a rational square-root substitution gives a quadratic tail integral when
the parameters are positive. Negative parameters are handled by subtracting their logarithmic
comparison kernels and integrating one smooth logarithmic primitive. The results include
principal values at one or two poles and a zero node.

## Main results

* `integrableOn_carlsonRootProduct_mul_sub_inv_sub_indicator`: the integrand of `R_J(x, y, z, -c)`
  minus its singular part is integrable on `(0, ∞)`.
* `tendsto_integral_symmetricEllipticRJ_of_neg`, `tendsto_integral_symmetricEllipticRJ_of_neg_symm`:
  the excised integrals converge to `(2/3) R_J(x, y, z, p)` for `p < 0`.
* `carlsonRootProduct_zero_inv_ofReal`, `carlsonRootProduct_zero_inv_mul_add_inv`: the behaviour of
  the integrand of `R_J(0, y, z, p)` under `t ↦ yz/t`.
* `mul_symmetricEllipticRJ_zero_add_mul`: DLMF 19.21.15, `p R_J(0, y, z, p) + q R_J(0, y, z, q) =
  3 R_F(0, y, z)` for real `pq = yz > 0`.
* `symmetricEllipticRJ_change_parameter_of_pos`,
  `symmetricEllipticRJ_change_parameter_of_neg_difference`: the general identity
  (19.21.12–19.21.13), assembled here as `symmetricEllipticRJ_change_parameter'`,
  allowing `p = x` or `q = x`; `SymmetricConnection` gives the DLMF corollary.
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

/-- A negative-parameter `R_J` is the integral after subtraction of its singular part. -/
theorem symmetricEllipticRJ_of_neg_eq_integral_sub {x y z : ℂ}
    (hx : x ∈ slitPlane ∨ x = 0) (hy : y ∈ slitPlane) (hz : z ∈ slitPlane)
    {p : ℝ} (hp : p < 0) :
    symmetricEllipticRJ x y z p = (3 / 2) * ∫ t in Ioi (0 : ℝ),
      (carlsonRootProduct x y z t * ((t : ℂ) + p))⁻¹ -
        (Icc (-p / 2) (3 * -p / 2)).indicator
          (fun t => (carlsonRootProduct x y z (-p))⁻¹ / ((t : ℂ) + p)) t := by
  have hc : 0 < -p := by linarith
  have hreg := integrableOn_carlsonRootProduct_mul_sub_inv_sub_indicator hx hy hz hc
  have H := tendsto_setIntegral_diff_Icc_symm_of_integrableOn_sub
    (carlsonRootProduct x y z (-p))⁻¹ (by linarith : -p / 2 < -p)
    (by linarith : -p < 3 * -p / 2) measurableSet_Ioi
    (fun t ht => by change 0 < t; linarith [ht.1]) hreg
  have hr : (3 * -p / 2 - -p) / (-p - -p / 2) = 1 := by
    field_simp [hp.ne]
    <;> ring
  rw [hr, Real.log_one, ofReal_zero, mul_zero, add_zero] at H
  simp only [ofReal_neg, sub_neg_eq_add] at H
  have he := tendsto_nhds_unique H (tendsto_integral_symmetricEllipticRJ_of_neg_symm hx hy hz hp)
  linear_combination -(3 / 2 : ℂ) * he

/-- For nonnegative `x` and positive `y`, `R_C(x,y)` is a quadratic-kernel tail integral. -/
theorem symmetricEllipticRC_eq_integral_quadratic_tail {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    IntegrableOn (fun u : ℝ => ((u ^ 2 + y - x : ℝ) : ℂ)⁻¹) (Ioi (Real.sqrt x)) ∧
      symmetricEllipticRC x y =
        ∫ u in Ioi (Real.sqrt x), ((u ^ 2 + y - x : ℝ) : ℂ)⁻¹ := by
  have hx' : (x : ℂ) ∈ slitPlane ∨ (x : ℂ) = 0 := by
    rcases hx.eq_or_lt with h | h
    · right; exact_mod_cast h.symm
    · exact Or.inl (ofReal_mem_slitPlane.mpr h)
  have hy' := ofReal_mem_slitPlane.mpr hy
  have hi := integrableOn_symmetricEllipticRF_integrand hx' hy' hy'
  have hkernel : ∀ t : ℝ, 0 < t →
      (carlsonRootProduct (x : ℂ) y y t)⁻¹ =
        (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y))⁻¹ := by
    intro t ht
    rw [carlsonRootProduct, mul_assoc, cpow_half_mul_cpow_half]
  have hi' : IntegrableOn
      (fun t : ℝ => (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y))⁻¹) (Ioi 0) :=
    hi.congr_fun (fun t ht => hkernel t ht) measurableSet_Ioi
  let f : ℝ → ℝ := fun u => u ^ 2 - x
  let g : ℝ → ℂ := fun t => (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y))⁻¹
  have hd : ∀ u ∈ Ioi (Real.sqrt x), HasDerivWithinAt f (2 * u) (Ioi (Real.sqrt x)) u := by
    intro u hu
    convert (((hasDerivAt_id u).pow 2).sub_const x).hasDerivWithinAt using 1 <;> simp [f]
  have hm : MonotoneOn f (Ioi (Real.sqrt x)) := by
    intro u hu v hv huv
    simp only [mem_Ioi] at hu hv
    dsimp [f]
    nlinarith [Real.sqrt_nonneg x]
  have himage : f '' Ioi (Real.sqrt x) = Ioi 0 := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      simp only [mem_Ioi]
      change Real.sqrt x < u at hu
      dsimp [f]
      nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x]
    · intro ht
      change 0 < t at ht
      refine ⟨Real.sqrt (t + x), ?_, ?_⟩
      · exact Real.sqrt_lt_sqrt hx (by linarith)
      · dsimp [f]
        rw [Real.sq_sqrt (by linarith)]
        ring
  have heq : ∀ u ∈ Ioi (Real.sqrt x), (2 * u) • g (f u) =
      2 * ((u ^ 2 + y - x : ℝ) : ℂ)⁻¹ := by
    intro u hu
    have hu0 : 0 < u := (Real.sqrt_nonneg x).trans_lt hu
    have h1 : ((f u : ℝ) : ℂ) + x = ((u ^ 2 : ℝ) : ℂ) := by dsimp [f]; push_cast; ring
    dsimp [g]
    rw [h1, Carlson.ofReal_cpow_half (sq_nonneg u), Real.sqrt_sq hu0.le]
    dsimp [f]
    push_cast
    field_simp [ofReal_ne_zero.mpr hu0.ne']
    ring
  have htrans := integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Ioi hd hm g
  rw [himage, setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul] at htrans
  have hitrans := (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
    measurableSet_Ioi hd hm g).mp (by simpa only [himage] using hi')
  have hi2 : IntegrableOn (fun u : ℝ => 2 * ((u ^ 2 + y - x : ℝ) : ℂ)⁻¹)
      (Ioi (Real.sqrt x)) := hitrans.congr_fun heq measurableSet_Ioi
  have hfin := hi2.const_mul (1 / 2 : ℂ)
  simp only [← mul_assoc, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_mul] at hfin
  refine ⟨hfin, ?_⟩
  rw [symmetricEllipticRC_eq_integral (not_isNegReal_of_mem_slitPlane hy'), htrans]
  ring

/-- The logarithmic formula for `R_C` when the difference of its arguments is negative. -/
lemma neg_two_mul_symmetricEllipticRC_eq_log_abs {x y : ℝ} (hx : 0 ≤ x) (hy : y ≠ 0)
    (hyx : y < x) :
    -2 * symmetricEllipticRC x y =
      (((Real.log |y| - 2 * Real.log (Real.sqrt x + Real.sqrt (x - y))) /
        Real.sqrt (x - y) : ℝ) : ℂ) := by
  have hS : 0 < Real.sqrt x + Real.sqrt (x - y) := by positivity
  have ha : 0 < Real.sqrt (x - y) := Real.sqrt_pos.mpr (sub_pos.mpr hyx)
  have habs : 0 < |y| := abs_pos.mpr hy
  have hRC : symmetricEllipticRC x y =
      ((Real.log ((Real.sqrt x + Real.sqrt (x - y)) / Real.sqrt |y|) /
        Real.sqrt (x - y) : ℝ) : ℂ) := by
    rcases lt_or_gt_of_ne hy with hy | hy
    · simpa only [abs_of_neg hy] using (symmetricEllipticRC_of_neg hy hx).2.2
    · simpa only [abs_of_pos hy] using (symmetricEllipticRC_of_gt hy hyx).2
  rw [hRC, Real.log_div hS.ne' (Real.sqrt_pos.mpr habs).ne', Real.log_sqrt habs.le]
  push_cast
  ring

namespace SymmetricParameterChange

/-- The square-root rational substitution in the change of parameter of `R_J`. -/
def substitution (x y z t : ℝ) : ℝ := Real.sqrt ((t + y) * (t + z) / (t + x))

/-- The substitution is positive in the interior of the integration ray. -/
lemma substitution_pos {x y z t : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hz : 0 ≤ z) (ht : 0 < t) :
    0 < substitution x y z t := by
  dsimp [substitution]
  positivity

/-- The square of the substitution. -/
lemma substitution_sq {x y z t : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hz : 0 ≤ z) (ht : 0 ≤ t) :
    substitution x y z t ^ 2 = (t + y) * (t + z) / (t + x) := by
  exact Real.sq_sqrt (by positivity)

/-- The rational relation between the two parameters becomes a quadratic denominator. -/
lemma substitution_sq_add {x y z p q t : ℝ} (htx : t + x ≠ 0)
    (hx : x ≠ 0) (hsub : substitution x y z t ^ 2 = (t + y) * (t + z) / (t + x))
    (hpq : (p - x) * (q - x) = (y - x) * (z - x)) :
    substitution x y z t ^ 2 + p * q / x - y * z / x = (t + p) * (t + q) / (t + x) := by
  rw [hsub]
  field_simp
  linear_combination t * hpq

/-- The derivative of the rational square-root substitution. -/
lemma hasDerivAt_substitution {x y z t : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ht : 0 < t) :
    HasDerivAt (substitution x y z)
      (((2 * t + y + z) * (t + x) - (t + y) * (t + z)) /
        (2 * substitution x y z t * (t + x) ^ 2)) t := by
  have htx : t + x ≠ 0 := by positivity
  have hv : 0 < (t + y) * (t + z) / (t + x) := by positivity
  have H := ((((hasDerivAt_id t).add_const y).mul ((hasDerivAt_id t).add_const z)).div
    ((hasDerivAt_id t).add_const x) htx).sqrt hv.ne'
  change HasDerivAt (fun u => Real.sqrt ((u + y) * (u + z) / (u + x))) _ t
  convert H using 1 <;> dsimp [substitution] <;> field_simp <;> ring

/-- The root product is a linear factor times the rational square root. -/
lemma carlsonRootProduct_eq {x y z t : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ht : 0 < t) :
    carlsonRootProduct x y z t = (((t + x) * substitution x y z t : ℝ) : ℂ) := by
  have htx : 0 < t + x := by positivity
  have hty : 0 < t + y := by positivity
  have htz : 0 < t + z := by positivity
  have hu := substitution_pos hx hy hz ht
  have husq := substitution_sq hx hy hz ht.le
  have hroot : Real.sqrt (t + x) * Real.sqrt (t + y) * Real.sqrt (t + z) =
      (t + x) * substitution x y z t := by
    have h1 := Real.sq_sqrt htx.le
    have h2 := Real.sq_sqrt hty.le
    have h3 := Real.sq_sqrt htz.le
    have h4 : ((t + x) * substitution x y z t) ^ 2 =
        (t + x) * (t + y) * (t + z) := by
      rw [mul_pow, husq]
      field_simp
    have h5 : (Real.sqrt (t + x) * Real.sqrt (t + y) * Real.sqrt (t + z)) ^ 2 =
        (t + x) * (t + y) * (t + z) := by rw [mul_pow, mul_pow, h1, h2, h3]
    exact (sq_eq_sq₀ (by positivity) (by positivity)).mp (h5.trans h4.symm)
  rw [carlsonRootProduct, ← ofReal_add, ← ofReal_add, ← ofReal_add,
    Carlson.ofReal_cpow_half htx.le, Carlson.ofReal_cpow_half hty.le,
    Carlson.ofReal_cpow_half htz.le, ← ofReal_mul, ← ofReal_mul, hroot]

/-- The substitution tends to infinity along the integration ray. -/
lemma tendsto_substitution_atTop {x y z : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Tendsto (substitution x y z) atTop atTop := by
  apply Real.tendsto_sqrt_atTop.comp
  apply tendsto_atTop_mono' _ ?_ (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  filter_upwards [eventually_ge_atTop x] with t ht
  have htx : 0 < t + x := by linarith
  rw [le_div_iff₀ htx]
  simp only [id_eq]
  have ht0 : 0 ≤ t := by linarith
  nlinarith [mul_nonneg hy hz, mul_nonneg ht0 hy, mul_nonneg ht0 hz,
    mul_nonneg ht0 (sub_nonneg.mpr ht)]

/-- A negative parameter gives a negative quadratic difference and an explicit residue root. -/
lemma carlsonRootProduct_at_neg_parameter {x y z p q : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hp : p < 0) (hpq : (p - x) * (q - x) = (y - x) * (z - x)) :
    p * q / x - y * z / x < 0 ∧
      carlsonRootProduct x y z (-p) =
        (((x - p) * Real.sqrt (-(p * q / x - y * z / x)) : ℝ) : ℂ) := by
  have ht : 0 < -p := neg_pos.mpr hp
  have hu := substitution_pos hx hy hz ht
  have H := substitution_sq_add (t := -p) (by positivity) hx.ne'
    (substitution_sq hx hy hz ht.le) hpq
  simp only [neg_add_cancel, zero_mul, zero_div] at H
  have he : substitution x y z (-p) ^ 2 = -(p * q / x - y * z / x) := by
    linear_combination H
  have hC : p * q / x - y * z / x < 0 := by nlinarith [sq_pos_of_pos hu]
  refine ⟨hC, ?_⟩
  rw [← he, Real.sqrt_sq hu.le, carlsonRootProduct_eq hx hy hz ht]
  push_cast
  ring

end SymmetricParameterChange

/-- Integrability of the `R_F` and `R_J` kernels with at most one zero real node. -/
lemma integrableOn_carlsonRootProduct_inv_of_nonneg {x y z : ℝ} (hx : 0 < x)
    (hy : 0 ≤ y) (hz : 0 ≤ z) (hyz : y = 0 → z ≠ 0) {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t => (carlsonRootProduct x y z t)⁻¹) (Ioi 0) ∧
      IntegrableOn (fun t => (carlsonRootProduct x y z t * ((t : ℂ) + p))⁻¹) (Ioi 0) := by
  have hx' := ofReal_mem_slitPlane.mpr hx
  have hp' := ofReal_mem_slitPlane.mpr hp
  by_cases hy0 : y = 0
  · have hz' := ofReal_mem_slitPlane.mpr (lt_of_le_of_ne hz (Ne.symm (hyz hy0)))
    subst y
    have hF := integrableOn_symmetricEllipticRF_integrand (Or.inr rfl) hx' hz'
    have hJ := integrableOn_symmetricEllipticRJ_integrand (Or.inr rfl) hx' hz' hp'
    constructor
    · simpa only [carlsonRootProduct, ofReal_zero, mul_comm, mul_left_comm, mul_assoc] using hF
    · simpa only [carlsonRootProduct, ofReal_zero, mul_comm, mul_left_comm, mul_assoc] using hJ
  have hy' := ofReal_mem_slitPlane.mpr (lt_of_le_of_ne hy (Ne.symm hy0))
  by_cases hz0 : z = 0
  · subst z
    have hF := integrableOn_symmetricEllipticRF_integrand (Or.inr rfl) hx' hy'
    have hJ := integrableOn_symmetricEllipticRJ_integrand (Or.inr rfl) hx' hy' hp'
    constructor
    · simpa only [carlsonRootProduct, ofReal_zero, mul_comm, mul_left_comm, mul_assoc] using hF
    · simpa only [carlsonRootProduct, ofReal_zero, mul_comm, mul_left_comm, mul_assoc] using hJ
  have hz' := ofReal_mem_slitPlane.mpr (lt_of_le_of_ne hz (Ne.symm hz0))
  exact ⟨integrableOn_symmetricEllipticRF_integrand (Or.inl hx') hy' hz',
    integrableOn_symmetricEllipticRJ_integrand (Or.inl hx') hy' hz' hp'⟩

/-- Subtraction of a negative-parameter pole with at most one zero real node. -/
lemma symmetricEllipticRJ_of_neg_eq_integral_sub_of_nonneg {x y z p : ℝ} (hx : 0 < x)
    (hy : 0 ≤ y) (hz : 0 ≤ z) (hyz : y = 0 → z ≠ 0) (hp : p < 0) :
    IntegrableOn (fun t : ℝ => (carlsonRootProduct x y z t * ((t : ℂ) + p))⁻¹ -
      (Icc (-p / 2) (3 * -p / 2)).indicator
        (fun t => (carlsonRootProduct x y z (-p))⁻¹ / ((t : ℂ) + p)) t) (Ioi 0) ∧
      symmetricEllipticRJ x y z p = (3 / 2) * ∫ t in Ioi (0 : ℝ),
        (carlsonRootProduct x y z t * ((t : ℂ) + p))⁻¹ -
          (Icc (-p / 2) (3 * -p / 2)).indicator
            (fun t => (carlsonRootProduct x y z (-p))⁻¹ / ((t : ℂ) + p)) t := by
  have hs (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) :
      IntegrableOn (fun t : ℝ => (carlsonRootProduct a b c t * ((t : ℂ) + p))⁻¹ -
        (Icc (-p / 2) (3 * -p / 2)).indicator
          (fun t => (carlsonRootProduct a b c (-p))⁻¹ / ((t : ℂ) + p)) t) (Ioi 0) ∧
        symmetricEllipticRJ a b c p = (3 / 2) * ∫ t in Ioi (0 : ℝ),
          (carlsonRootProduct a b c t * ((t : ℂ) + p))⁻¹ -
            (Icc (-p / 2) (3 * -p / 2)).indicator
              (fun t => (carlsonRootProduct a b c (-p))⁻¹ / ((t : ℂ) + p)) t := by
    have ha' : (a : ℂ) ∈ slitPlane ∨ (a : ℂ) = 0 := by
      rcases ha.eq_or_lt with ha | ha
      · right; exact_mod_cast ha.symm
      · exact Or.inl (ofReal_mem_slitPlane.mpr ha)
    have hb' := ofReal_mem_slitPlane.mpr hb
    have hc' := ofReal_mem_slitPlane.mpr hc
    constructor
    · simpa only [ofReal_neg, sub_neg_eq_add] using
        integrableOn_carlsonRootProduct_mul_sub_inv_sub_indicator ha' hb' hc' (neg_pos.mpr hp)
    · exact symmetricEllipticRJ_of_neg_eq_integral_sub ha' hb' hc' hp
  by_cases hy0 : y = 0
  · have hz' := lt_of_le_of_ne hz (Ne.symm (hyz hy0))
    subst y
    obtain ⟨hI, hV⟩ := hs 0 x z le_rfl hx hz'
    rw [symmetricEllipticRJ_comm_left] at hV
    constructor
    · simpa only [carlsonRootProduct, ofReal_zero, mul_comm, mul_left_comm, mul_assoc] using hI
    · simpa only [carlsonRootProduct, ofReal_zero, mul_comm, mul_left_comm, mul_assoc] using hV
  have hy' := lt_of_le_of_ne hy (Ne.symm hy0)
  by_cases hz0 : z = 0
  · subst z
    obtain ⟨hI, hV⟩ := hs 0 x y le_rfl hx hy'
    rw [symmetricEllipticRJ_comm_left, symmetricEllipticRJ_comm_right] at hV
    constructor
    · simpa only [carlsonRootProduct, ofReal_zero, mul_comm, mul_left_comm, mul_assoc] using hI
    · simpa only [carlsonRootProduct, ofReal_zero, mul_comm, mul_left_comm, mul_assoc] using hV
  exact hs x y z hx.le hy' (lt_of_le_of_ne hz (Ne.symm hz0))

namespace SymmetricParameterChange

/-- The parameter contribution after subtracting a logarithmic comparison kernel. -/
def regularizedParameterKernel (x y z A p t : ℝ) : ℂ :=
  -((p - x : ℝ) : ℂ) * (carlsonRootProduct x y z t * ((t : ℂ) + p))⁻¹ -
    (A : ℂ)⁻¹ * (((t : ℂ) + p)⁻¹ - ((t : ℂ) + 1)⁻¹)

/-- The regularized parameter contribution is integrable and its integral is explicit. -/
lemma integrableOn_regularizedParameterKernel_and_integral {x y z A p : ℝ} (hx : 0 < x)
    (hy : 0 ≤ y) (hz : 0 ≤ z) (hyz : y = 0 → z ≠ 0) (hp : p ≠ 0)
    (hres : p < 0 → -((p - x : ℝ) : ℂ) * (carlsonRootProduct x y z (-p))⁻¹ = (A : ℂ)⁻¹) :
    IntegrableOn (regularizedParameterKernel x y z A p) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), regularizedParameterKernel x y z A p t =
        -(2 / 3) * ((p - x : ℝ) : ℂ) * symmetricEllipticRJ x y z p +
          (A : ℂ)⁻¹ * (Real.log |p| : ℂ) := by
  rcases lt_or_gt_of_ne hp with hp | hp
  · let J : ℝ → ℂ := fun t => (carlsonRootProduct x y z t * ((t : ℂ) + p))⁻¹ -
      (Icc (-p / 2) (3 * -p / 2)).indicator
        (fun t => (carlsonRootProduct x y z (-p))⁻¹ / ((t : ℂ) + p)) t
    let K : ℝ → ℂ := fun t => ((t : ℂ) + p)⁻¹ - ((t : ℂ) + 1)⁻¹ -
      (Icc (-p / 2) (3 * -p / 2)).indicator (fun t : ℝ => ((t : ℂ) + p)⁻¹) t
    obtain ⟨hiJ, hV⟩ := symmetricEllipticRJ_of_neg_eq_integral_sub_of_nonneg hx hy hz hyz hp
    change IntegrableOn J (Ioi 0) at hiJ
    change symmetricEllipticRJ x y z p = (3 / 2) * ∫ t in Ioi (0 : ℝ), J t at hV
    have hiK : IntegrableOn K (Ioi 0) := by
      simpa only [ofReal_neg, sub_neg_eq_add] using
        integrableOn_complex_inv_sub_inv_add_sub_indicator (neg_pos.mpr hp)
    have hK : ∫ t in Ioi (0 : ℝ), K t = (-Real.log (-p) : ℝ) := by
      simpa only [ofReal_neg, sub_neg_eq_add] using
        integral_complex_inv_sub_inv_add_sub_indicator (neg_pos.mpr hp)
    have heq : regularizedParameterKernel x y z A p =
        fun t => -((p - x : ℝ) : ℂ) * J t - (A : ℂ)⁻¹ * K t := by
      funext t
      have hr := hres hp
      simp only [regularizedParameterKernel, J, K, div_eq_mul_inv, mul_neg]
      by_cases ht : t ∈ Icc (-p * (2 : ℝ)⁻¹) (-(3 * p) * (2 : ℝ)⁻¹)
      · simp only [indicator_of_mem ht]
        linear_combination (((t : ℂ) + p)⁻¹) * hr
      · simp only [indicator_of_notMem ht, sub_zero]
    have hi := (hiJ.const_mul (-((p - x : ℝ) : ℂ))).sub (hiK.const_mul (A : ℂ)⁻¹)
    refine ⟨by rw [heq]; exact hi, ?_⟩
    rw [heq, integral_sub (hiJ.const_mul _) (hiK.const_mul _), integral_const_mul,
      integral_const_mul, hK, abs_of_neg hp]
    push_cast
    linear_combination (2 / 3 : ℂ) * ((p : ℂ) - x) * hV
  · have hiJ := (integrableOn_carlsonRootProduct_inv_of_nonneg hx hy hz hyz hp).2
    have hiB := integrableOn_complex_inv_add_sub_inv_add hp
    have hi := (hiJ.const_mul (-((p - x : ℝ) : ℂ))).sub (hiB.const_mul (A : ℂ)⁻¹)
    refine ⟨hi, ?_⟩
    have hI := integral_sub (hiJ.const_mul (-((p - x : ℝ) : ℂ)))
      (hiB.const_mul (A : ℂ)⁻¹)
    change (∫ t in Ioi (0 : ℝ), -((p - x : ℝ) : ℂ) *
      (carlsonRootProduct x y z t * ((t : ℂ) + p))⁻¹ -
        (A : ℂ)⁻¹ * (((t : ℂ) + p)⁻¹ - ((t : ℂ) + 1)⁻¹)) = _
    rw [hI, integral_const_mul, integral_const_mul, integral_complex_inv_add_sub_inv_add hp,
      abs_of_pos hp]
    simp only [symmetricEllipticRJ,
      not_isNegReal_of_mem_slitPlane (ofReal_mem_slitPlane.mpr hp), ↓reduceIte]
    push_cast
    ring

end SymmetricParameterChange

namespace SymmetricParameterChange

/-- A smooth primitive after all parameter poles have been subtracted. -/
def logarithmicPrimitive (x y z A t : ℝ) : ℝ :=
  (2 * Real.log (t + 1) - Real.log (t + x) -
    2 * Real.log (substitution x y z t + A)) / A

/-- The derivative of the smooth logarithmic primitive. -/
lemma hasDerivAt_logarithmicPrimitive {x y z A t : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hA : 0 < A) (ht : 0 < t) :
    HasDerivAt (logarithmicPrimitive x y z A)
      ((2 / (t + 1) - 1 / (t + x) -
        2 * (((2 * t + y + z) * (t + x) - (t + y) * (t + z)) /
          (2 * substitution x y z t * (t + x) ^ 2)) /
            (substitution x y z t + A)) / A) t := by
  have hu := substitution_pos hx hy hz ht
  have H := (((((hasDerivAt_id t).add_const 1).log
    (show id t + 1 ≠ 0 by simp only [id_eq]; positivity)).const_mul 2).sub
      (((hasDerivAt_id t).add_const x).log
        (show id t + x ≠ 0 by simp only [id_eq]; positivity))).sub
      ((((hasDerivAt_substitution hx hy hz ht).add_const A).log (by positivity)).const_mul 2)
  have H' := H.div_const A
  convert H' using 1
  · funext s; rfl
  · simp only [id_eq, one_mul, mul_one]
    ring

/-- The smooth logarithmic primitive vanishes at infinity. -/
lemma tendsto_logarithmicPrimitive {x y z A : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hA : 0 < A) :
    Tendsto (logarithmicPrimitive x y z A) atTop (𝓝 0) := by
  let u := substitution x y z
  have hu := tendsto_substitution_atTop hx hy hz
  have hsmall : Tendsto (fun t => A / u t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hu
  have harg := (tendsto_const_nhds (x := (1 : ℝ))).add hsmall
  simp only [add_zero] at harg
  have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp harg
  simp only [Real.log_one] at hlog
  have H := (((Real.tendsto_log_add_sub_log_add_atTop 1 y).add
    (Real.tendsto_log_add_sub_log_add_atTop 1 z)).sub (hlog.const_mul 2)).div_const A
  simp only [zero_add, mul_zero, sub_zero, zero_sub, zero_div, Function.comp_def] at H
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have ht1 : 0 < t + 1 := by positivity
  have htx : 0 < t + x := by positivity
  have hty : 0 < t + y := by positivity
  have htz : 0 < t + z := by positivity
  have hut : 0 < u t := substitution_pos hx hy hz ht
  have hsq := substitution_sq hx hy hz ht.le
  change (u t) ^ 2 = (t + y) * (t + z) / (t + x) at hsq
  have hLogSq : 2 * Real.log (u t) =
      Real.log (t + y) + Real.log (t + z) - Real.log (t + x) := by
    have hlogpow := Real.log_pow (u t) 2
    norm_num only [Nat.cast_ofNat] at hlogpow
    rw [← hlogpow, hsq, Real.log_div (by positivity) htx.ne',
      Real.log_mul hty.ne' htz.ne']
  have hLogAdd : Real.log (u t + A) = Real.log (u t) + Real.log (1 + A / u t) := by
    rw [← Real.log_mul hut.ne' (by positivity : (1 + A / u t : ℝ) ≠ 0)]
    congr 1
    field_simp
  change _ = logarithmicPrimitive x y z A t
  dsimp only [logarithmicPrimitive]
  change _ = (2 * Real.log (t + 1) - Real.log (t + x) - 2 * Real.log (u t + A)) / A
  rw [hLogAdd]
  congr 1
  linear_combination hLogSq

/-- The smooth logarithmic primitive is continuous at the endpoint of the integration ray. -/
lemma continuousAt_logarithmicPrimitive_zero {x y z A : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hA : 0 < A) : ContinuousAt (logarithmicPrimitive x y z A) 0 := by
  have hu : ContinuousAt (substitution x y z) 0 := by
    change ContinuousAt (fun t : ℝ => Real.sqrt ((t + y) * (t + z) / (t + x))) 0
    fun_prop (disch := positivity)
  have hu0 : 0 ≤ substitution x y z 0 := Real.sqrt_nonneg _
  change ContinuousAt (fun t : ℝ => (2 * Real.log (t + 1) - Real.log (t + x) -
    2 * Real.log (substitution x y z t + A)) / A) 0
  fun_prop (disch := positivity)

end SymmetricParameterChange

namespace SymmetricParameterChange

/-- The smooth primitive differentiates to the sum of the regularized parameter kernels. -/
lemma logarithmicPrimitive_derivative_eq {x y z A p q t : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hA : 0 < A) (ht : 0 < t) (htp : t + p ≠ 0) (htq : t + q ≠ 0)
    (hpq : (p - x) * (q - x) = (y - x) * (z - x))
    (hAsq : A ^ 2 = -(p * q / x - y * z / x)) :
    (((2 / (t + 1) - 1 / (t + x) -
        2 * (((2 * t + y + z) * (t + x) - (t + y) * (t + z)) /
          (2 * substitution x y z t * (t + x) ^ 2)) /
            (substitution x y z t + A)) / A : ℝ) : ℂ) =
      (carlsonRootProduct x y z t)⁻¹ + regularizedParameterKernel x y z A p t +
        regularizedParameterKernel x y z A q t := by
  let u := substitution x y z t
  let d := ((2 * t + y + z) * (t + x) - (t + y) * (t + z)) / (2 * u * (t + x) ^ 2)
  have hu : 0 < u := substitution_pos hx hy hz ht
  have htx : t + x ≠ 0 := by positivity
  have hden : u ^ 2 - A ^ 2 = (t + p) * (t + q) / (t + x) := by
    rw [hAsq]
    simpa only [u, sub_neg_eq_add, add_sub_assoc] using
      substitution_sq_add htx hx.ne' (substitution_sq hx hy hz ht.le) hpq
  have hdenne : u ^ 2 - A ^ 2 ≠ 0 := by
    rw [hden]
    exact div_ne_zero (mul_ne_zero htp htq) htx
  have hF : (1 - (p - x) / (t + p) - (q - x) / (t + q)) / ((t + x) * u) =
      2 * d / (u ^ 2 - A ^ 2) := by
    rw [hden]
    dsimp [d]
    field_simp [hu.ne']
    linear_combination -hpq
  have hsum : 1 / (t + p) + 1 / (t + q) - 1 / (t + x) =
      2 * u * d / (u ^ 2 - A ^ 2) := by
    rw [hden]
    dsimp [d]
    field_simp [hu.ne']
    linear_combination -hpq
  have hsumpq : 1 / (t + p) + 1 / (t + q) =
      1 / (t + x) + 2 * u * d / (u ^ 2 - A ^ 2) := by linear_combination hsum
  have halg : (2 / (t + 1) - 1 / (t + x) - 2 * d / (u + A)) / A =
      (1 - (p - x) / (t + p) - (q - x) / (t + q)) / ((t + x) * u) -
        A⁻¹ * (1 / (t + p) + 1 / (t + q) - 2 / (t + 1)) := by
    rw [hF, hsumpq]
    field_simp [hdenne, hA.ne', show u + A ≠ 0 by positivity]
    ring
  have hc := congrArg (fun r : ℝ => (r : ℂ)) halg
  push_cast at hc
  simp only [regularizedParameterKernel, carlsonRootProduct_eq hx hy hz ht]
  convert hc using 1 <;> simp only [d, u, div_eq_mul_inv, mul_inv, ofReal_add, ofReal_mul,
    ofReal_pow, ofReal_ofNat, ofReal_sub, ofReal_inv, ofReal_div, ofReal_one, ofReal_neg] <;> ring

end SymmetricParameterChange

/-- The change of parameter of `R_J` for positive real variables and parameters. -/
theorem symmetricEllipticRJ_change_parameter_of_pos {x y z p q : ℝ} (hx : 0 < x)
    (hy : 0 ≤ y) (hz : 0 ≤ z) (hyz : y = 0 → z ≠ 0) (hp : 0 < p) (hq : 0 < q)
    (hpq : (p - x) * (q - x) = (y - x) * (z - x)) :
    ((p - x : ℝ) : ℂ) * symmetricEllipticRJ x y z p + ((q - x : ℝ) : ℂ) *
      symmetricEllipticRJ x y z q =
        3 * symmetricEllipticRF x y z -
          3 * symmetricEllipticRC (y * z / x : ℝ) (p * q / x : ℝ) := by
  let C : ℝ := p * q / x - y * z / x
  let u := SymmetricParameterChange.substitution x y z
  let G : ℝ → ℂ := fun v => ∫ s in Ioi v, ((s ^ 2 + C : ℝ) : ℂ)⁻¹
  let F : ℝ → ℂ := fun t => (carlsonRootProduct x y z t)⁻¹ -
    ((p - x : ℝ) : ℂ) * (carlsonRootProduct x y z t * ((t : ℂ) + p))⁻¹ -
    ((q - x : ℝ) : ℂ) * (carlsonRootProduct x y z t * ((t : ℂ) + q))⁻¹
  have hG : ∀ v : ℝ, 0 < v → 0 < v ^ 2 + C →
      HasDerivAt G (-((v ^ 2 + C : ℝ) : ℂ)⁻¹) v := by
    intro v hv hden
    have hb : Real.sqrt (max 0 (-C)) < v := by
      calc
        Real.sqrt (max 0 (-C)) < Real.sqrt (v ^ 2) :=
          Real.sqrt_lt_sqrt (le_max_left _ _) (max_lt (by positivity) (by linarith))
        _ = v := Real.sqrt_sq hv.le
    obtain ⟨a, hba, hav⟩ := exists_between hb
    have ha : 0 < a := (Real.sqrt_nonneg _).trans_lt hba
    have haC : 0 < a ^ 2 + C := by
      have hb2 := Real.sq_sqrt (le_max_left 0 (-C))
      have haa := pow_lt_pow_left₀ hba (Real.sqrt_nonneg _) two_ne_zero
      linarith [le_max_right 0 (-C)]
    have hi : IntegrableOn (fun s : ℝ => ((s ^ 2 + C : ℝ) : ℂ)⁻¹) (Ioi a) := by
      have H := (symmetricEllipticRC_eq_integral_quadratic_tail (sq_nonneg a) haC).1
      simpa only [Real.sqrt_sq ha.le, show ∀ s : ℝ, s ^ 2 + (a ^ 2 + C) - a ^ 2 =
        s ^ 2 + C by intro s; ring] using H
    have hm : StronglyMeasurable (fun s : ℝ => ((s ^ 2 + C : ℝ) : ℂ)⁻¹) :=
      (by fun_prop : Measurable fun s : ℝ => ((s ^ 2 + C : ℝ) : ℂ)⁻¹).stronglyMeasurable
    exact hi.hasDerivAt_integral_Ioi hav hm.stronglyMeasurableAtFilter
      (ContinuousAt.inv₀ (by fun_prop) (ofReal_ne_zero.mpr hden.ne'))
  have hu (t : ℝ) (ht : 0 < t) : 0 < u t :=
    SymmetricParameterChange.substitution_pos hx hy hz ht
  have hunonneg (t : ℝ) : 0 ≤ u t := Real.sqrt_nonneg _
  have hden (t : ℝ) (ht : 0 ≤ t) : (u t) ^ 2 + C = (t + p) * (t + q) / (t + x) := by
    simpa only [u, C, add_sub_assoc] using
      SymmetricParameterChange.substitution_sq_add (by positivity) hx.ne'
        (SymmetricParameterChange.substitution_sq hx hy hz ht) hpq
  have hdenpos (t : ℝ) (ht : 0 ≤ t) : 0 < (u t) ^ 2 + C := by
    rw [hden t ht]
    positivity
  have hderiv (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun t => G (u t)) (-(1 / 2 : ℂ) * F t) t := by
    have hd : HasDerivAt u
        (((2 * t + y + z) * (t + x) - (t + y) * (t + z)) /
          (2 * u t * (t + x) ^ 2)) t := by
      simpa only [u] using
        SymmetricParameterChange.hasDerivAt_substitution hx hy hz ht
    have H := (hG (u t) (hu t ht) (hdenpos t ht.le)).scomp t hd
    have htx : (t + x : ℝ) ≠ 0 := by positivity
    have htp : (t + p : ℝ) ≠ 0 := by positivity
    have htq : (t + q : ℝ) ≠ 0 := by positivity
    have halg : -((u t) ^ 2 + C)⁻¹ *
        (((2 * t + y + z) * (t + x) - (t + y) * (t + z)) /
          (2 * u t * (t + x) ^ 2)) =
        -(1 / 2 : ℝ) * ((1 - (p - x) / (t + p) - (q - x) / (t + q)) /
          ((t + x) * u t)) := by
      rw [hden t ht.le]
      field_simp [(hu t ht).ne']
      linear_combination -hpq
    refine H.congr_deriv ?_
    dsimp only [F]
    rw [SymmetricParameterChange.carlsonRootProduct_eq hx hy hz ht]
    have hc := congrArg (fun r : ℝ => (r : ℂ)) halg
    push_cast at hc
    simp only [Complex.real_smul]
    convert hc using 1 <;> simp only [div_eq_mul_inv, mul_inv, ofReal_add, ofReal_mul,
      ofReal_pow, ofReal_ofNat, ofReal_sub, ofReal_inv, ofReal_div, ofReal_one,
      ofReal_neg] <;> ring
  have hps := ofReal_mem_slitPlane.mpr hp
  have hqs := ofReal_mem_slitPlane.mpr hq
  obtain ⟨hiF, hiP⟩ := integrableOn_carlsonRootProduct_inv_of_nonneg hx hy hz hyz hp
  have hiQ := (integrableOn_carlsonRootProduct_inv_of_nonneg hx hy hz hyz hq).2
  have hi : IntegrableOn F (Ioi 0) :=
    (hiF.sub (hiP.const_mul ((p - x : ℝ) : ℂ))).sub (hiQ.const_mul ((q - x : ℝ) : ℂ))
  have hucont : ContinuousAt u 0 := by
    change ContinuousAt (fun t : ℝ => Real.sqrt ((t + y) * (t + z) / (t + x))) 0
    fun_prop (disch := positivity)
  have hcont : ContinuousWithinAt (fun t => G (u t)) (Ici 0) 0 := by
    by_cases hu0 : u 0 = 0
    · have hC : 0 < C := by
        simpa only [hu0, zero_pow two_ne_zero, zero_add] using hdenpos 0 le_rfl
      have hiG : IntegrableOn (fun s : ℝ => ((s ^ 2 + C : ℝ) : ℂ)⁻¹) (Ioi 0) := by
        simpa only [Real.sqrt_zero, sub_zero, add_zero] using
          (symmetricEllipticRC_eq_integral_quadratic_tail (x := 0) le_rfl hC).1
      have hm : StronglyMeasurable (fun s : ℝ => ((s ^ 2 + C : ℝ) : ℂ)⁻¹) :=
        (by fun_prop : Measurable fun s : ℝ => ((s ^ 2 + C : ℝ) : ℂ)⁻¹).stronglyMeasurable
      have hcg := hiG.continuousWithinAt_integral_Ioi le_rfl hm.stronglyMeasurableAtFilter
        (show ContinuousAt (fun s : ℝ => ((s ^ 2 + C : ℝ) : ℂ)⁻¹) 0 by
          apply ContinuousAt.inv₀ (by fun_prop)
          simpa only [zero_pow two_ne_zero, zero_add] using ofReal_ne_zero.mpr hC.ne')
      change ContinuousWithinAt G (Ici 0) 0 at hcg
      have hcg' : ContinuousWithinAt G (Ici 0) (u 0) := by simpa only [hu0] using hcg
      exact hcg'.comp hucont.continuousWithinAt (fun t ht => hunonneg t)
    · exact ((hG (u 0) (lt_of_le_of_ne (hunonneg 0) (Ne.symm hu0))
        (hdenpos 0 le_rfl)).continuousAt.comp hucont).continuousWithinAt
  have hlim : Tendsto (fun t => G (u t)) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero (SymmetricParameterChange.tendsto_substitution_atTop hx hy hz)
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun t ht => hderiv t ht) (hi.const_mul (-(1 / 2 : ℂ))) hlim
  have hu0 : u 0 = Real.sqrt (y * z / x) := by simp [u, SymmetricParameterChange.substitution]
  have hRC := (symmetricEllipticRC_eq_integral_quadratic_tail
    (by positivity : 0 ≤ y * z / x) (by positivity : 0 < p * q / x)).2
  have hG0 : G (u 0) = symmetricEllipticRC (y * z / x : ℝ) (p * q / x : ℝ) := by
    rw [hu0, hRC]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp [G, C]
    congr 2
    ring
  rw [integral_const_mul, zero_sub, hG0] at hI
  have hInt : ∫ t in Ioi (0 : ℝ), F t =
      2 * symmetricEllipticRF x y z - (2 / 3) * ((p - x : ℝ) : ℂ) * symmetricEllipticRJ x y z p -
        (2 / 3) * ((q - x : ℝ) : ℂ) * symmetricEllipticRJ x y z q := by
    rw [show (∫ t in Ioi (0 : ℝ), F t) =
      (∫ t in Ioi (0 : ℝ), (carlsonRootProduct x y z t)⁻¹) -
        ((p - x : ℝ) : ℂ) * (∫ t in Ioi (0 : ℝ),
          (carlsonRootProduct x y z t * ((t : ℂ) + p))⁻¹) -
        ((q - x : ℝ) : ℂ) * (∫ t in Ioi (0 : ℝ),
          (carlsonRootProduct x y z t * ((t : ℂ) + q))⁻¹) by
      dsimp [F]
      have h1 := integral_sub (hiF.sub (hiP.const_mul ((p - x : ℝ) : ℂ)))
        (hiQ.const_mul ((q - x : ℝ) : ℂ))
      have h2 := integral_sub hiF (hiP.const_mul ((p - x : ℝ) : ℂ))
      simp only [Pi.sub_apply] at h1 h2
      rw [h1, h2, integral_const_mul, integral_const_mul]]
    simp only [symmetricEllipticRF, symmetricEllipticRJ,
      not_isNegReal_of_mem_slitPlane hps, not_isNegReal_of_mem_slitPlane hqs, ↓reduceIte]
    ring
  rw [hInt] at hI
  linear_combination 3 * hI

/-- The change of parameter of `R_J` when the quadratic difference is negative. -/
theorem symmetricEllipticRJ_change_parameter_of_neg_difference {x y z p q : ℝ}
    (hx : 0 < x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hyz : y = 0 → z ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : (p - x) * (q - x) = (y - x) * (z - x))
    (hC : p * q / x - y * z / x < 0) :
    ((p - x : ℝ) : ℂ) * symmetricEllipticRJ x y z p + ((q - x : ℝ) : ℂ) *
      symmetricEllipticRJ x y z q =
        3 * symmetricEllipticRF x y z -
          3 * symmetricEllipticRC (y * z / x : ℝ) (p * q / x : ℝ) := by
  let C := p * q / x - y * z / x
  let A := Real.sqrt (-C)
  have hA : 0 < A := Real.sqrt_pos.mpr (neg_pos.mpr hC)
  have hAsq : A ^ 2 = -(p * q / x - y * z / x) := Real.sq_sqrt (by linarith)
  have hres (r s : ℝ) (hr : r < 0) (hrs : r * s = p * q)
      (hrel : (r - x) * (s - x) = (y - x) * (z - x)) :
      -((r - x : ℝ) : ℂ) * (carlsonRootProduct x y z (-r))⁻¹ = (A : ℂ)⁻¹ := by
    have hroot := (SymmetricParameterChange.carlsonRootProduct_at_neg_parameter
      hx hy hz hr hrel).2
    rw [hrs] at hroot
    change carlsonRootProduct x y z (-r) = (((x - r) * A : ℝ) : ℂ) at hroot
    rw [hroot]
    have hxr : (x : ℂ) - r ≠ 0 := by
      exact_mod_cast (show x - r ≠ 0 by linarith)
    push_cast
    rw [show -((r : ℂ) - x) = (x : ℂ) - r by ring, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ hxr, one_mul]
  obtain ⟨hiP, hIP⟩ :=
    SymmetricParameterChange.integrableOn_regularizedParameterKernel_and_integral
      hx hy hz hyz hp (fun hr => hres p q hr rfl hpq)
  obtain ⟨hiQ, hIQ⟩ :=
    SymmetricParameterChange.integrableOn_regularizedParameterKernel_and_integral
      hx hy hz hyz hq (fun hr => hres q p hr (mul_comm _ _)
        (by rw [mul_comm]; exact hpq))
  have hiF := (integrableOn_carlsonRootProduct_inv_of_nonneg hx hy hz hyz
    (p := 1) zero_lt_one).1
  let R : ℝ → ℂ := fun t => (carlsonRootProduct x y z t)⁻¹ +
    SymmetricParameterChange.regularizedParameterKernel x y z A p t +
      SymmetricParameterChange.regularizedParameterKernel x y z A q t
  let H := SymmetricParameterChange.logarithmicPrimitive x y z A
  let D : ℝ → ℂ := fun t => ((deriv H t : ℝ) : ℂ)
  have hiR : IntegrableOn R (Ioi 0) := (hiF.add hiP).add hiQ
  have heq : D =ᵐ[volume.restrict (Ioi (0 : ℝ))] R := by
    have hpAE : ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)), t ≠ -p := by
      rw [ae_iff]
      simpa only [not_not, ofPred_eq_eq_singleton] using
        (measure_singleton (-p) : volume.restrict (Ioi (0 : ℝ)) {-p} = 0)
    have hqAE : ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)), t ≠ -q := by
      rw [ae_iff]
      simpa only [not_not, ofPred_eq_eq_singleton] using
        (measure_singleton (-q) : volume.restrict (Ioi (0 : ℝ)) {-q} = 0)
    filter_upwards [ae_restrict_mem measurableSet_Ioi, hpAE, hqAE] with t ht htp htq
    dsimp only [D, H]
    rw [(SymmetricParameterChange.hasDerivAt_logarithmicPrimitive hx hy hz hA ht).deriv]
    exact SymmetricParameterChange.logarithmicPrimitive_derivative_eq hx hy hz hA ht
      (by intro h; exact htp (by linarith)) (by intro h; exact htq (by linarith)) hpq hAsq
  have hiD : IntegrableOn D (Ioi 0) := hiR.congr_fun_ae heq.symm
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt (fun t => (H t : ℂ)) (D t) t := by
    have hh := SymmetricParameterChange.hasDerivAt_logarithmicPrimitive hx hy hz hA ht
    exact hh.differentiableAt.hasDerivAt.ofReal_comp
  have hc0 : ContinuousAt H 0 :=
    SymmetricParameterChange.continuousAt_logarithmicPrimitive_zero hx hy hz hA
  have hc : ContinuousWithinAt (fun t => (H t : ℂ)) (Ici 0) 0 :=
    (Complex.continuous_ofReal.continuousAt.comp hc0).continuousWithinAt
  have hlim : Tendsto (fun t => (H t : ℂ)) atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp
      (SymmetricParameterChange.tendsto_logarithmicPrimitive hx hy hz hA)
    simpa only [Function.comp_def, ofReal_zero] using h
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hc (fun t ht => hd t ht) hiD hlim
  rw [integral_congr_ae heq, zero_sub] at hFTC
  have hIR : ∫ t in Ioi (0 : ℝ), R t =
      2 * symmetricEllipticRF x y z - (2 / 3) * ((p - x : ℝ) : ℂ) * symmetricEllipticRJ x y z p -
        (2 / 3) * ((q - x : ℝ) : ℂ) * symmetricEllipticRJ x y z q +
          (A : ℂ)⁻¹ * ((Real.log |p| : ℂ) + Real.log |q|) := by
    have h1 : (∫ t in Ioi (0 : ℝ), R t) =
        (∫ t in Ioi (0 : ℝ), (carlsonRootProduct x y z t)⁻¹ +
          SymmetricParameterChange.regularizedParameterKernel x y z A p t) +
        ∫ t in Ioi (0 : ℝ), SymmetricParameterChange.regularizedParameterKernel x y z A q t := by
      simpa only [Pi.add_apply] using integral_add (hiF.add hiP) hiQ
    have h2 : (∫ t in Ioi (0 : ℝ), (carlsonRootProduct x y z t)⁻¹ +
        SymmetricParameterChange.regularizedParameterKernel x y z A p t) =
        (∫ t in Ioi (0 : ℝ), (carlsonRootProduct x y z t)⁻¹) +
          ∫ t in Ioi (0 : ℝ), SymmetricParameterChange.regularizedParameterKernel x y z A p t := by
      simpa only [Pi.add_apply] using integral_add hiF hiP
    rw [h1, h2, hIP, hIQ]
    simp only [symmetricEllipticRF]
    ring
  rw [hIR] at hFTC
  have hη : p * q / x ≠ 0 := div_ne_zero (mul_ne_zero hp hq) hx.ne'
  have hlog : Real.log |p * q / x| = Real.log |p| + Real.log |q| - Real.log x := by
    rw [abs_div, abs_mul, abs_of_pos hx,
      Real.log_div (mul_ne_zero (abs_pos.mpr hp).ne' (abs_pos.mpr hq).ne') hx.ne',
      Real.log_mul (abs_pos.mpr hp).ne' (abs_pos.mpr hq).ne']
  have hRC := neg_two_mul_symmetricEllipticRC_eq_log_abs
    (by positivity : 0 ≤ y * z / x) hη (by linarith : p * q / x < y * z / x)
  have hsqrt : Real.sqrt (y * z / x - p * q / x) = A := by
    congr 1
    dsimp [C, A]
    ring
  rw [hsqrt, hlog] at hRC
  have hu0 : SymmetricParameterChange.substitution x y z 0 = Real.sqrt (y * z / x) := by
    simp [SymmetricParameterChange.substitution]
  have hRCeq : (A : ℂ)⁻¹ * ((Real.log |p| : ℂ) + Real.log |q|) + (H 0 : ℂ) =
      -2 * symmetricEllipticRC (y * z / x : ℝ) (p * q / x : ℝ) := by
    rw [hRC]
    dsimp only [H, SymmetricParameterChange.logarithmicPrimitive]
    simp only [zero_add, Real.log_one, mul_zero, zero_sub, hu0]
    push_cast
    field_simp
    ring
  linear_combination -(3 / 2 : ℂ) * hFTC + (3 / 2 : ℂ) * hRCeq

/-- The change of parameter of `R_J`, stronger than DLMF, which assumes `p ≠ x` and `q ≠ x`.
The identity also holds at these exceptional parameters whenever `p,q` are nonzero. -/
@[dlmf 19.21.E12 "stronger than DLMF: allows p = x or q = x",
  dlmf 19.21.E13 "stronger than DLMF: allows p = x or q = x"]
theorem symmetricEllipticRJ_change_parameter' {x y z p q : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hyz : y = 0 → z ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : (p - x) * (q - x) = (y - x) * (z - x)) :
    ((p - x : ℝ) : ℂ) * symmetricEllipticRJ x y z p + ((q - x : ℝ) : ℂ) *
      symmetricEllipticRJ x y z q =
        3 * symmetricEllipticRF x y z -
          3 * symmetricEllipticRC (y * z / x : ℝ) (p * q / x : ℝ) := by
  rcases lt_or_gt_of_ne hp with hpn | hpp
  · exact symmetricEllipticRJ_change_parameter_of_neg_difference hx hy hz hyz hp hq hpq
      (SymmetricParameterChange.carlsonRootProduct_at_neg_parameter hx hy hz hpn hpq).1
  rcases lt_or_gt_of_ne hq with hqn | hqp
  · apply symmetricEllipticRJ_change_parameter_of_neg_difference hx hy hz hyz hp hq hpq
    have hrel : (q - x) * (p - x) = (y - x) * (z - x) := by rw [mul_comm]; exact hpq
    simpa only [mul_comm q p] using
      (SymmetricParameterChange.carlsonRootProduct_at_neg_parameter hx hy hz hqn hrel).1
  · exact symmetricEllipticRJ_change_parameter_of_pos hx hy hz hyz hpp hqp hpq

end DLMF.EllipticIntegrals
