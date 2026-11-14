/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.SymmetricPrincipalValue
public import DLMF.EllipticIntegrals.SymmetricRelations

/-!
# Symmetric elliptic integrals: connection formulas (DLMF §19.21)

Legendre's relation and the connection formulas of the complete integrals (§19.21(i)), the
relations between `R_F`, `R_D`, `R_G` of the incomplete integrals (§19.21(ii)), and the change
of parameter of `R_J` (§19.21(iii)).

## Main results

* `analyticAt_symmetricEllipticRF_zero_comp`, `analyticAt_symmetricEllipticRD_zero_comp`: analytic
  dependence of the complete symmetric integrals on slit-plane arguments.
* `legendreRelation_symmetricElliptic`, `lemniscate_product`: Legendre's relation in symmetric form
  and its case `z = 1` (DLMF 19.21.1).
* `symmetricEllipticRF_zero_eq_symmetricEllipticRD`, `symmetricEllipticRG_zero_eq`: DLMF 19.21.2,
  19.21.3.
* `symmetricEllipticRF_zero_connection`, `symmetricEllipticRG_zero_connection`: DLMF 19.21.4,
  19.21.5.
* `symmetricEllipticRJ_zero_eq_RF_RD`: DLMF 19.21.6.
* `symmetricEllipticRD_move`, `symmetricEllipticRD_cyclic_sum`,
  `symmetricEllipticRD_cyclic_mul_sum`: DLMF 19.21.7–19.21.9.
* `two_mul_symmetricEllipticRG_eq`, `six_mul_symmetricEllipticRG_eq`: `R_G` in terms of `R_F` and
  `R_D` (DLMF 19.21.10, 19.21.11).
* `symmetricEllipticRJ_change_parameter`, `symmetricEllipticRJ_change_parameter_identities`,
  `symmetricEllipticRJ_change_parameter_zero`: the change of parameter of `R_J`
  (DLMF 19.21.12–19.21.15).

## Implementation notes

DLMF's conditions are kept; where DLMF says "the variables satisfy §19.16(i)" we require
slit-plane variables (nonzero where DLMF divides). The relations were checked numerically
(mpmath) at complex arguments. §19.21(iii) is real: `x, y, z ≥ 0`, at most one zero, and the
parameters `p, q` real and nonzero (Cauchy principal values when negative). The prose
19.21.ii.p2 (connection formulas for `R_{-a}` in Carlson (1977b)) is bibliographic.

The analytic composition lemmas use `lean-codes`' `Carlson.analyticAt_carlsonR_comp`; the
symmetric Legendre relation uses `DLMF.Elliptic.legendre_relation` and analytic continuation.

## References

* NIST DLMF §19.21.
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-! ### §19.21(i) Complete integrals -/

/-- Legendre's relation in symmetric form for positive real arguments. -/
private lemma legendreRelation_symmetricElliptic_ofReal {x : ℝ} (hx : 0 < x) :
    symmetricEllipticRF 0 ((x + 1 : ℝ) : ℂ) x * symmetricEllipticRD 0 ((x + 1 : ℝ) : ℂ) 1 +
      symmetricEllipticRD 0 ((x + 1 : ℝ) : ℂ) x *
        symmetricEllipticRF 0 ((x + 1 : ℝ) : ℂ) 1 = 3 * π / (2 * (x : ℂ)) := by
  set m : ℝ := 1 / (x + 1)
  have hm0 : 0 < m := by dsimp only [m]; positivity
  have hm1 : m < 1 := by dsimp only [m]; rw [div_lt_one (by positivity)]; linarith
  set k : ℂ := (Real.sqrt m : ℂ)
  set l : ℂ := (Real.sqrt (1 - m) : ℂ)
  have hk : k ^ 2 = (m : ℂ) := by simpa [k] using ofReal_sqrt_sq_of_nonneg hm0.le
  have hl : l ^ 2 = ((1 - m : ℝ) : ℂ) := by
    simpa [l] using ofReal_sqrt_sq_of_nonneg (by linarith : 0 ≤ 1 - m)
  have hkm : 1 - k ^ 2 ∈ slitPlane := by
    rw [hk, ← ofReal_one, ← ofReal_sub]; exact ofReal_mem_slitPlane.mpr (by linarith)
  have hlm : 1 - l ^ 2 ∈ slitPlane := by
    rw [hl, ← ofReal_one, ← ofReal_sub, sub_sub_cancel]
    exact ofReal_mem_slitPlane.mpr hm0
  have hE := (completeEllipticE_eq_symmetricElliptic hkm).2.2.2.2
  have hE' := (completeEllipticE_eq_symmetricElliptic hlm).2.2.2.2
  have hK := completeEllipticK_eq_symmetricEllipticRF hkm
  have hK' := completeEllipticK_eq_symmetricEllipticRF hlm
  rw [hk] at hE hK
  rw [hl] at hE' hK'
  have hL := DLMF.Elliptic.legendre_relation hm0 hm1
  have hLc : completeEllipticE k * completeEllipticK l + completeEllipticE l *
      completeEllipticK k - completeEllipticK k * completeEllipticK l = π / 2 := by
    rw [completeEllipticK_eq_ofReal hk hm1.le, completeEllipticE_eq_ofReal hk hm1.le,
      completeEllipticK_eq_ofReal hl (by linarith), completeEllipticE_eq_ofReal hl (by linarith)]
    exact_mod_cast hL
  have hxp : 0 < x + 1 := by linarith
  have hscaleK := symmetricEllipticRF_scale hxp 0 (1 - m) 1
  have hscaleK' := symmetricEllipticRF_scale hxp 0 m 1
  have hma : 1 - (m : ℂ) ∈ slitPlane := by simpa [hk] using hkm
  have hscaleD := symmetricEllipticRD_scale hxp 0 1 (1 - m)
    (not_isNegReal_of_mem_slitPlane hma)
  have hscaleD' := symmetricEllipticRD_scale hxp 0 1 m
    (not_isNegReal_of_mem_slitPlane (ofReal_mem_slitPlane.mpr hm0))
  have hxp0 : (x : ℂ) + 1 ≠ 0 := by exact_mod_cast hxp.ne'
  have ex : ((x + 1 : ℝ) : ℂ) * (1 - (m : ℂ)) = x := by
    dsimp only [m]
    push_cast
    field_simp [hxp0]
    ring
  have em : ((x + 1 : ℝ) : ℂ) * (m : ℂ) = 1 := by
    dsimp only [m]
    push_cast
    field_simp [hxp0]
  simp only [mul_zero, mul_one] at hscaleK hscaleK' hscaleD hscaleD'
  rw [ex] at hscaleK hscaleD
  rw [em] at hscaleK' hscaleD'
  rw [symmetricEllipticRF_comm_right] at hscaleK hscaleK'
  rw [hscaleK, hscaleK', hscaleD, hscaleD']
  rw [← hK]
  rw [show 1 - ((1 - m : ℝ) : ℂ) = (m : ℂ) by push_cast; ring] at hK' hE'
  rw [← hK']
  have hroot2 := ofReal_cpow_half_sq (l := x + 1)
  have hroot0 := ofReal_cpow_half_ne_zero hxp
  generalize ((x + 1 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = r at hroot2 hroot0 ⊢
  have hmc : (m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm0.ne'
  have hac : 1 - (m : ℂ) ≠ 0 := by exact_mod_cast (by linarith : 1 - m ≠ 0)
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hprod : (m : ℂ) * (1 - (m : ℂ)) * r ^ 4 = x := by
    rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hroot2]
    dsimp only [m]
    push_cast
    field_simp [hxp0]
    ring
  field_simp [hroot0, hx0]
  apply mul_left_cancel₀ (mul_ne_zero hmc hac)
  push_cast at hE'
  linear_combination (6 * (x : ℂ)) * hLc -
    (6 * (x : ℂ) * completeEllipticK l) * hE -
    (6 * (x : ℂ) * completeEllipticK k) * hE' -
    (3 * (π : ℂ)) * hprod

/-- A complete first-kind symmetric integral is analytic in its two slit-plane arguments. -/
theorem analyticAt_symmetricEllipticRF_zero_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {p : E}
    (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hfp : f p ∈ slitPlane) (hgp : g p ∈ slitPlane) :
    AnalyticAt ℂ (fun q => symmetricEllipticRF 0 (f q) (g q)) p := by
  have ha : AnalyticAt ℂ (fun q => (π / 2 : ℂ) *
      Carlson.carlsonR (-(1 / 2)) ![1 / 2, 1 / 2] ![f q, g q]) p := by
    refine analyticAt_const.mul (Carlson.analyticAt_carlsonR_comp analyticAt_const
      analyticAt_const ?_ (vec2_mem_carlsonRSlitDomain hfp hgp) ?_)
    · refine analyticAt_pi_iff.mpr fun i => ?_
      fin_cases i <;> simpa
    · intro n
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num
      exact_mod_cast (by omega : (1 : ℤ) ≠ -(n : ℤ))
  refine ha.congr ?_
  have hfe := hf.continuousAt.preimage_mem_nhds (isOpen_slitPlane.mem_nhds hfp)
  have hge := hg.continuousAt.preimage_mem_nhds (isOpen_slitPlane.mem_nhds hgp)
  filter_upwards [hfe, hge] with q hqf hqg
  rw [symmetricEllipticRF_zero_left hqf hqg,
    symmetricEllipticR_of_mem _ _ (vec2_mem_carlsonRSlitDomain hqf hqg)]

/-- A complete second-kind symmetric integral is analytic in its two slit-plane arguments. -/
theorem analyticAt_symmetricEllipticRD_zero_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {p : E}
    (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hfp : f p ∈ slitPlane) (hgp : g p ∈ slitPlane) :
    AnalyticAt ℂ (fun q => symmetricEllipticRD 0 (f q) (g q)) p := by
  have ha : AnalyticAt ℂ (fun q => (3 * π / 4 : ℂ) *
      Carlson.carlsonR (-(3 / 2)) ![1 / 2, 3 / 2] ![f q, g q]) p := by
    refine analyticAt_const.mul (Carlson.analyticAt_carlsonR_comp analyticAt_const
      analyticAt_const ?_ (vec2_mem_carlsonRSlitDomain hfp hgp) ?_)
    · refine analyticAt_pi_iff.mpr fun i => ?_
      fin_cases i <;> simpa
    · intro n
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num
      exact_mod_cast (by omega : (2 : ℤ) ≠ -(n : ℤ))
  refine ha.congr ?_
  have hfe := hf.continuousAt.preimage_mem_nhds (isOpen_slitPlane.mem_nhds hfp)
  have hge := hg.continuousAt.preimage_mem_nhds (isOpen_slitPlane.mem_nhds hgp)
  filter_upwards [hfe, hge] with q hqf hqg
  rw [symmetricEllipticRD_zero_left hqf hqg,
    symmetricEllipticR_of_mem _ _ (vec2_mem_carlsonRSlitDomain hqf hqg)]


/-- DLMF 19.21.1: Legendre's relation (19.7.1) in symmetric form,
`R_F(0, z+1, z) R_D(0, z+1, 1) + R_D(0, z+1, z) R_F(0, z+1, 1) = 3π/(2z)`, `z ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.21.E1]
theorem legendreRelation_symmetricElliptic {z : ℂ} (hz : z ∈ slitPlane) :
    symmetricEllipticRF 0 (z + 1) z * symmetricEllipticRD 0 (z + 1) 1 +
      symmetricEllipticRD 0 (z + 1) z * symmetricEllipticRF 0 (z + 1) 1 = 3 * π / (2 * z) := by
  have hA : AnalyticOnNhd ℂ (fun z => symmetricEllipticRF 0 (z + 1) z *
      symmetricEllipticRD 0 (z + 1) 1 +
      symmetricEllipticRD 0 (z + 1) z * symmetricEllipticRF 0 (z + 1) 1) slitPlane := by
    intro w hw
    have hw1 : w + 1 ∈ slitPlane := by
      rcases hw with hw | hw
      · left; simpa using (by linarith : 0 < w.re + 1)
      · right; simpa using hw
    exact ((analyticAt_symmetricEllipticRF_zero_comp (analyticAt_id.add analyticAt_const)
      analyticAt_id hw1 hw).mul
      (analyticAt_symmetricEllipticRD_zero_comp (analyticAt_id.add analyticAt_const)
      analyticAt_const hw1 one_mem_slitPlane)).add
      ((analyticAt_symmetricEllipticRD_zero_comp (analyticAt_id.add analyticAt_const)
      analyticAt_id hw1 hw).mul
      (analyticAt_symmetricEllipticRF_zero_comp (analyticAt_id.add analyticAt_const)
      analyticAt_const hw1 one_mem_slitPlane))
  have hB : AnalyticOnNhd ℂ (fun z => 3 * (π : ℂ) / (2 * z)) slitPlane := fun w hw =>
    analyticAt_const.div (analyticAt_const.mul analyticAt_id)
      (mul_ne_zero two_ne_zero (slitPlane_ne_zero hw))
  refine hA.eqOn_of_preconnected_of_frequently_eq hB
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
    one_mem_slitPlane ?_ hz
  refine Carlson.TwoVariable.frequently_ofReal_Ioo (a := 1) (ε := 1 / 2) (by norm_num)
    (fun x h1 _ => ?_)
  have h := legendreRelation_symmetricElliptic_ofReal (x := x) (by linarith)
  simpa only [ofReal_add, ofReal_one] using h

/-- DLMF 19.21.1, case `z = 1`: the product of the two lemniscate constants (19.20.2), (19.20.22)
is `π/4`: `R_F(0, 1, 2) · (1/3) R_D(0, 2, 1) = π/4`. -/
@[dlmf 19.21.E1]
theorem lemniscate_product : symmetricEllipticRF 0 1 2 *
    ((1 / 3) * symmetricEllipticRD 0 2 1) = π / 4 := by
  exact symmetricEllipticRF_mul_symmetricEllipticRD_lemniscate

/-- DLMF 19.21.2: `3 R_F(0, y, z) = z R_D(0, y, z) + y R_D(0, z, y)`, `y, z ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.21.E2]
theorem symmetricEllipticRF_zero_eq_symmetricEllipticRD {y z : ℂ} (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    3 * symmetricEllipticRF 0 y z = z * symmetricEllipticRD 0 y z + y *
        symmetricEllipticRD 0 z y := by
  have h := symmetricEllipticRD_cyclic_mul_sum_of_isCarlsonArgument (Or.inr rfl) hy hz
  rw [symmetricEllipticRD_comm 0 z y] at h
  linear_combination -h

/-- DLMF 19.21.3: `6 R_G(0, y, z) = yz (R_D(0, y, z) + R_D(0, z, y))
= 3z R_F(0, y, z) + z(y - z) R_D(0, y, z)`, `y, z ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.21.E3]
theorem symmetricEllipticRG_zero_eq {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    6 * symmetricEllipticRG 0 y z = y * z *
        (symmetricEllipticRD 0 y z + symmetricEllipticRD 0 z y) ∧
      6 * symmetricEllipticRG 0 y z = 3 * z * symmetricEllipticRF 0 y z + z * (y - z) *
          symmetricEllipticRD 0 y z := by
  have h1 := two_mul_symmetricEllipticRG (Or.inr rfl) hy hz
  have h2 := symmetricEllipticRD_cyclic_mul_sum_of_isCarlsonArgument (Or.inr rfl) hy hz
  rw [symmetricEllipticRD_comm 0 z y] at h2
  rw [zero_cpow (by norm_num : (1 / 2 : ℂ) ≠ 0)] at h1
  constructor
  · linear_combination 3 * h1 - z * h2
  · linear_combination 3 * h1

/-- DLMF 19.21.4: `R_F(0, z - 1, z) = R_F(0, 1 - z, 1) ∓ i R_F(0, z, 1)`, upper sign for
`0 < ph z < π`, lower sign for `-π < ph z < 0`; written with `s = sign(Im z)`. -/
@[dlmf 19.21.E4]
theorem symmetricEllipticRF_zero_connection {z : ℂ} (hz : z.im ≠ 0) :
    symmetricEllipticRF 0 (z - 1) z =
      symmetricEllipticRF 0 (1 - z) 1 - (SignType.sign z.im : ℂ) * I *
          symmetricEllipticRF 0 z 1 := by
  sorry

/-- DLMF 19.21.5: `2R_G(0, z-1, z) = 2R_G(0, 1-z, 1) ± 2i R_G(0, z, 1) + (z-1) R_F(0, 1-z, 1)
∓ iz R_F(0, z, 1)`, upper signs for `0 < ph z < π`, lower for `-π < ph z < 0`
(`s = sign(Im z)`). -/
@[dlmf 19.21.E5]
theorem symmetricEllipticRG_zero_connection {z : ℂ} (hz : z.im ≠ 0) :
    2 * symmetricEllipticRG 0 (z - 1) z =
      2 * symmetricEllipticRG 0 (1 - z) 1 + (SignType.sign z.im : ℂ) * I *
          (2 * symmetricEllipticRG 0 z 1) +
        (z - 1) * symmetricEllipticRF 0 (1 - z) 1 - (SignType.sign z.im : ℂ) * I * z *
            symmetricEllipticRF 0 z 1 := by
  sorry

/-- DLMF 19.21.6: for positive distinct `y, z, p` with `y` not between `z` and `p`,
`r = (y - p)/(y - z) > 0`,
`(√(rp)/z) R_J(0, y, z, p) = (r - 1) R_F(0, y, z) R_D(p, rz, z) + R_D(0, y, z) R_F(p, rz, z)`. -/
@[dlmf 19.21.E6]
theorem symmetricEllipticRJ_zero_eq_RF_RD {y z p : ℝ} (hy : 0 < y) (hz : 0 < z) (hp : 0 < p)
    (hyz : y ≠ z) (hyp : y ≠ p) (hzp : z ≠ p) (hr : 0 < (y - p) / (y - z)) :
    let r : ℝ := (y - p) / (y - z)
    (Real.sqrt (r * p) / z : ℝ) * symmetricEllipticRJ 0 y z p =
      ((r - 1 : ℝ) : ℂ) * symmetricEllipticRF 0 y z * symmetricEllipticRD p (r * z : ℝ) z +
        symmetricEllipticRD 0 y z * symmetricEllipticRF p (r * z : ℝ) z := by
  sorry

/-! ### §19.21(ii) Incomplete integrals -/

/-- DLMF 19.21.7: `(x - y) R_D(y, z, x) + (z - y) R_D(x, y, z) = 3R_F(x, y, z) - 3 y^{1/2} x^{-1/2}
z^{-1/2}` (moves the nonzero `x` to the third position); slit-plane variables. -/
@[dlmf 19.21.E7]
theorem symmetricEllipticRD_move {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    (x - y) * symmetricEllipticRD y z x + (z - y) * symmetricEllipticRD x y z =
      3 * symmetricEllipticRF x y z - 3 * y ^ (1 / 2 : ℂ) * x ^ (-1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ) :=
  symmetricEllipticRD_two_term_relation hx hy hz

/-- DLMF 19.21.8: `R_D(y, z, x) + R_D(z, x, y) + R_D(x, y, z) = 3 x^{-1/2} y^{-1/2} z^{-1/2}`. -/
@[dlmf 19.21.E8]
theorem symmetricEllipticRD_cyclic_sum {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    symmetricEllipticRD y z x + symmetricEllipticRD z x y + symmetricEllipticRD x y z =
      3 * x ^ (-1 / 2 : ℂ) * y ^ (-1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ) :=
  symmetricEllipticRD_cyclic_sum' hx hy hz

/-- DLMF 19.21.9: `x R_D(y, z, x) + y R_D(z, x, y) + z R_D(x, y, z) = 3 R_F(x, y, z)`. -/
@[dlmf 19.21.E9]
theorem symmetricEllipticRD_cyclic_mul_sum {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    x * symmetricEllipticRD y z x + y * symmetricEllipticRD z x y + z * symmetricEllipticRD x y z =
      3 * symmetricEllipticRF x y z :=
  symmetricEllipticRD_cyclic_mul_sum_of_isCarlsonArgument (Or.inl hx) hy hz

/-- DLMF 19.21.10: `2R_G(x, y, z) = z R_F(x, y, z) - (1/3)(x - z)(y - z) R_D(x, y, z)
+ x^{1/2} y^{1/2} z^{-1/2}`, `z ≠ 0`; slit-plane variables. -/
@[dlmf 19.21.E10]
theorem two_mul_symmetricEllipticRG_eq {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    2 * symmetricEllipticRG x y z = z * symmetricEllipticRF x y z - (1 / 3) * (x - z) * (y - z) *
        symmetricEllipticRD x y z +
      x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ) * z ^ (-1 / 2 : ℂ) :=
  two_mul_symmetricEllipticRG (Or.inl hx) hy hz

/-- DLMF 19.21.11: `6R_G(x, y, z) = 3(x + y + z) R_F(x, y, z) - ∑ x² R_D(y, z, x)
= ∑ x(y + z) R_D(y, z, x)`, sums over the three cyclic permutations. -/
@[dlmf 19.21.E11]
theorem six_mul_symmetricEllipticRG_eq {x y z : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (hz : z ∈ slitPlane) :
    6 * symmetricEllipticRG x y z = 3 * (x + y + z) * symmetricEllipticRF x y z -
        (x ^ 2 * symmetricEllipticRD y z x + y ^ 2 * symmetricEllipticRD z x y + z ^ 2 *
            symmetricEllipticRD x y z) ∧
      6 * symmetricEllipticRG x y z = x * (y + z) * symmetricEllipticRD y z x + y * (z + x) *
          symmetricEllipticRD z x y +
        z * (x + y) * symmetricEllipticRD x y z := by
  have h1 := six_mul_symmetricEllipticRG hx hy hz
  have h2 := symmetricEllipticRD_cyclic_mul_sum_of_isCarlsonArgument (Or.inl hx) hy hz
  exact ⟨h1, by linear_combination h1 - (x + y + z) * h2⟩

/-! ### §19.21(iii) Change of parameter of `R_J` -/

/-- DLMF 19.21.12 with 19.21.13: for real `x > 0`, `y, z ≥ 0` (at most one zero), real
`p, q ≠ 0`, `p, q ≠ x`, with `(p - x)(q - x) = (y - x)(z - x)`, `ξ = yz/x`, `η = pq/x`,
`(p - x) R_J(x, y, z, p) + (q - x) R_J(x, y, z, q) = 3R_F(x, y, z) - 3R_C(ξ, η)`
(principal values for negative `p, q`). -/
@[dlmf 19.21.E12, dlmf 19.21.E13]
theorem symmetricEllipticRJ_change_parameter {x y z p q : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hyz : y = 0 → z ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) (hpx : p ≠ x) (hqx : q ≠ x)
    (hpq : (p - x) * (q - x) = (y - x) * (z - x)) :
    ((p - x : ℝ) : ℂ) * symmetricEllipticRJ x y z p + ((q - x : ℝ) : ℂ) *
        symmetricEllipticRJ x y z q =
      3 * symmetricEllipticRF x y z - 3 * symmetricEllipticRC (y * z / x : ℝ) (p * q / x : ℝ) := by
  exact symmetricEllipticRJ_change_parameter' hx hy hz hyz hp hq hpq

/-- DLMF 19.21.14: under (19.21.13) (with `x ≠ y`, `x ≠ z`, `p, q ≠ x`),
`η - ξ = p + q - y - z = (p-y)(p-z)/(p-x) = (q-y)(q-z)/(q-x) = (p-y)(q-y)/(x-y)
= (p-z)(q-z)/(x-z)`. -/
@[dlmf 19.21.E14]
theorem symmetricEllipticRJ_change_parameter_identities {x y z p q : ℝ} (hx : x ≠ 0) (hpx : p ≠ x)
    (hqx : q ≠ x) (hxy : x ≠ y) (hxz : x ≠ z)
    (hpq : (p - x) * (q - x) = (y - x) * (z - x)) :
    p * q / x - y * z / x = p + q - y - z ∧ p + q - y - z = (p - y) * (p - z) / (p - x) ∧
      p + q - y - z = (q - y) * (q - z) / (q - x) ∧ p + q - y - z = (p - y) * (q - y) / (x - y) ∧
      p + q - y - z = (p - z) * (q - z) / (x - z) := by
  have hpx' : p - x ≠ 0 := sub_ne_zero.mpr hpx
  have hqx' : q - x ≠ 0 := sub_ne_zero.mpr hqx
  have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hxz' : x - z ≠ 0 := sub_ne_zero.mpr hxz
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;>
    first | linear_combination hpq | linear_combination -hpq

/-- DLMF 19.21.15: the case `x = 0` (`ξ = η = ∞`, `R_C(ξ, η) = 0`): for `y, z > 0` and real
`p, q ≠ 0` with `pq = yz`, `p R_J(0, y, z, p) + q R_J(0, y, z, q) = 3 R_F(0, y, z)`. -/
@[dlmf 19.21.E15]
theorem symmetricEllipticRJ_change_parameter_zero {y z p q : ℝ} (hy : 0 < y)
    (hz : 0 < z) (hp : p ≠ 0)
    (hpq : p * q = y * z) :
    (p : ℂ) * symmetricEllipticRJ 0 y z p + (q : ℂ) * symmetricEllipticRJ 0 y z q = 3 *
        symmetricEllipticRF 0 y z :=
  mul_symmetricEllipticRJ_zero_add_mul hy hz hp hpq

end DLMF.EllipticIntegrals
