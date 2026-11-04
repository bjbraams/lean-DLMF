/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.RPolynomial.Appell
public import DLMF.EllipticIntegrals.SymmetricPrincipalValue
public import DLMF.EllipticIntegrals.SymmetricRelations
public import DLMF.EllipticIntegrals.SymmetricSeries
public import DLMFMathlib.Analysis.SpecialFunctions.Complex.ArgLog

/-!
# Symmetric elliptic integrals: special cases (DLMF §19.20)

Special values, homogeneity, degenerate cases, limits and principal values of `R_F`, `R_G` and
`R_J` (§19.20(i)–(iii)); the cases of `R_D` and `R_{-a}(𝐛; 𝐳)` (§19.20(iv)–(v)) are in
`DLMF.EllipticIntegrals.SymmetricSpecialCasesRD`.

## Main results

* `symmetricEllipticRF_self`, `symmetricEllipticRF_smul`, `symmetricEllipticRF_self_right`,
  `symmetricEllipticRF_zero_self`, `not_integrableOn_symmetricEllipticRF_zero_zero`: special cases
  of `R_F` (DLMF 19.20.1).
* `lemniscate_first_symmetricEllipticRF`: the first lemniscate constant (DLMF 19.20.2).
* `symmetricEllipticRF_lemniscatic`, `symmetricEllipticRF_lemniscatic_complex`: the lemniscatic
  case (DLMF 19.20.3).
* `symmetricEllipticRG_self`, `symmetricEllipticRG_smul`, `symmetricEllipticRG_zero_self`,
  `two_mul_symmetricEllipticRG_self_right`: special cases of `R_G` (DLMF 19.20.4, 19.20.5).
* `symmetricEllipticRJ_self`, `symmetricEllipticRJ_smul`, `symmetricEllipticRJ_self_self_self_eq`,
  `symmetricEllipticRJ_zero_self_self`, `symmetricEllipticRJ_self_right_eq`,
  `symmetricEllipticRJ_zero_sqrt`: special cases of `R_J` (DLMF 19.20.6, 19.20.8, 19.20.9).
* `tendsto_symmetricEllipticRJ_zero`, `tendsto_symmetricEllipticRJ_zero_left`,
  `symmetricEllipticRJ_zero_asymptotic`, `tendsto_mul_symmetricEllipticRJ`: limits of `R_J` (DLMF
  19.20.7, 19.20.10–19.20.12).
* `symmetricEllipticRJ_special_p`, `symmetricEllipticRJ_principalValue`,
  `symmetricEllipticRJ_principalValue_p`, `symmetricEllipticRJ_principalValue_complete`: DLMF
  19.20.13–19.20.17.

## Implementation notes

As DLMF says (19.20.i.p1), the variables satisfy the constraints of §19.16(i) unless stated
otherwise; we state them explicitly (slit-plane membership, admissible zeros, real variables
where DLMF uses real ones, e.g. for Cauchy principal values). Homogeneity is stated for real
`λ > 0` (for complex `λ` see `symmetricEllipticR_mul`). "`= ∞`" is formalized as non-integrability
of the defining integrand, "`→ +∞`" as `Tendsto … atTop` of the (real) value. Decimal values of
the lemniscate constants (19.20.2), (19.20.22) are excluded as numerical.

The lemniscatic formulas follow from a quadratic transformation of `R` at three arguments in
arithmetic progression. Its real form uses the exact positive-ray substitution
`u = t² + (x + y)t`; the complex form uses the identity theorem
`Carlson.TwoVariable.eqOn_rightHalfPlane₂_of_real` from `lean-codes`.

**Domain corrections.** The lemniscatic cases (19.20.3), (19.20.23) are stated for real
positive `x, y`, and in corrected complex forms for `ℜ x, ℜ y > 0`; with arbitrary complex
arguments they fail without a branch condition (numerically, at `x = -1 + 0.3i`, `y = 2 + i`
the two sides differ by a factor `-i`).

## References

* NIST DLMF §19.20.
-/

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory Asymptotics
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-- Formula under the stated hypotheses: `arg (l : ℂ) + arg x ∈ Ioo (-π) π`. -/
private lemma arg_ofReal_add_arg_mem_Ioo {l : ℝ} (hl : 0 < l) {x : ℂ} (hx : x ∈ slitPlane) :
    arg (l : ℂ) + arg x ∈ Ioo (-π) π := by
  rw [arg_ofReal_of_nonneg hl.le, zero_add]
  exact ⟨neg_pi_lt_arg _, lt_of_le_of_ne (arg_le_pi _) (mem_slitPlane_iff_arg.mp hx).1⟩

/-- Identity under the stated parameter and domain assumptions:
`symmetricEllipticR a b (fun i => (l : ℂ)
* z i) = (l : ℂ) ^ (-a) * symmetricEllipticR a b z`. -/
private lemma symmetricEllipticR_ofReal_mul {ι : Type*} [Fintype ι] (a : ℂ) (b : ι → ℂ)
    {l : ℝ} (hl : 0 < l)
    {z : ι → ℂ} (hz : z ∈ Carlson.carlsonRSlitDomain) :
    symmetricEllipticR a b (fun i => (l : ℂ) * z i) = (l : ℂ) ^ (-a) * symmetricEllipticR a b z :=
  symmetricEllipticR_mul a b hz (ofReal_mem_slitPlane.mpr hl) fun i =>
      arg_ofReal_add_arg_mem_Ioo hl (hz i)

/-- Squaring the translated radial variable gives the quadratic integral substitution
for three arguments in arithmetic progression. -/
lemma integral_cpow_arithmetic_progression_quadratic {x y a : ℝ} (hx : 0 < x) (hy : 0 < y) :
    let m := (x + y) / 2
    (∫ u in Ioi (0 : ℝ), (((u + m ^ 2 : ℝ) : ℂ) ^ (((-(a + 1) / 2 : ℝ) : ℂ)) *
      ((u + x * y : ℝ) : ℂ) ^ ((-1 / 2 : ℝ) : ℂ))) =
    2 * ∫ t in Ioi (0 : ℝ), ((t + x : ℝ) : ℂ) ^ ((-1 / 2 : ℝ) : ℂ) *
      ((t + y : ℝ) : ℂ) ^ ((-1 / 2 : ℝ) : ℂ) * ((t + m : ℝ) : ℂ) ^ ((-a : ℝ) : ℂ) := by
  intro m
  have hm : 0 < m := by dsimp only [m]; positivity
  let g : ℝ → ℝ := fun t => t ^ 2 + 2 * m * t
  have hmono : StrictMonoOn g (Ioi 0) := by
    intro s hs t ht hst
    change 0 < s at hs
    change 0 < t at ht
    dsimp only [g]
    nlinarith
  have himg : g '' Ioi 0 = Ioi 0 := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      change 0 < g t
      change 0 < t at ht
      dsimp only [g]
      positivity
    · intro hu
      change 0 < u at hu
      let t := Real.sqrt (u + m ^ 2) - m
      have hsq : Real.sqrt (u + m ^ 2) ^ 2 = u + m ^ 2 := Real.sq_sqrt (by positivity)
      have ht : 0 < t := by dsimp only [t]; nlinarith [Real.sqrt_nonneg (u + m ^ 2)]
      refine ⟨t, ht, ?_⟩
      dsimp only [g, t]
      nlinarith
  let G : ℝ → ℂ := fun u => ((u + m ^ 2 : ℝ) : ℂ) ^ (((-(a + 1) / 2 : ℝ) : ℂ)) *
      ((u + x * y : ℝ) : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)
  have H := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (f := g) (f' := fun t => 2 * (t + m))
    (fun t _ => ((((hasDerivAt_id t).pow 2).add
        ((hasDerivAt_id t).const_mul (2 * m))).hasDerivWithinAt).congr_deriv (by simp; ring))
    hmono.injOn G
  rw [himg] at H
  change (∫ u in Ioi (0 : ℝ), G u) = _
  rw [H, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  change 0 < t at ht
  have htx : 0 < t + x := by linarith
  have hty : 0 < t + y := by linarith
  have htm : 0 < t + m := by linarith
  have e1 : g t + m ^ 2 = (t + m) ^ 2 := by dsimp only [g]; ring
  have e2 : g t + x * y = (t + x) * (t + y) := by dsimp only [g, m]; ring
  simp only [G, e1, e2, abs_of_pos (by positivity : 0 < 2 * (t + m)), Complex.real_smul]
  rw [← ofReal_cpow (sq_nonneg _) _, ← ofReal_cpow (mul_nonneg htx.le hty.le) _,
    ← ofReal_cpow htx.le _, ← ofReal_cpow hty.le _, ← ofReal_cpow htm.le _]
  have Hreal : (2 * (t + m)) *
      (((t + m) ^ 2) ^ (-(a + 1) / 2) * ((t + x) * (t + y)) ^ (-1 / 2 : ℝ)) =
      2 * ((t + x) ^ (-1 / 2 : ℝ) * (t + y) ^ (-1 / 2 : ℝ) * (t + m) ^ (-a)) := by
    rw [Real.mul_rpow htx.le hty.le, ← Real.rpow_natCast_mul htm.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (-(a + 1) / 2) = -a - 1 by ring]
    have he : (t + m) * (t + m) ^ (-a - 1) = (t + m) ^ (-a) := by
      calc _ = (t + m) ^ (1 + (-a - 1)) := by rw [Real.rpow_add htm, Real.rpow_one]
        _ = _ := by congr 1; ring
    linear_combination (2 * (t + x) ^ (-(1 / 2) : ℝ) * (t + y) ^ (-(1 / 2) : ℝ)) * he
  exact_mod_cast Hreal

/-- The quadratic transformation of a three-node R-function at its middle argument,
for positive real arguments and positive real exponent. -/
lemma symmetricEllipticR_arithmetic_progression_quadratic_ofReal {x y a : ℝ} (hx : 0 < x)
    (hy : 0 < y) (ha : 0 < a) :
    symmetricEllipticR (a : ℂ) ![1 / 2, 1 / 2, (a : ℂ)] ![(x : ℂ), y, ((x + y) / 2 : ℝ)] =
      symmetricEllipticR ((a / 2 : ℝ) : ℂ) ![(((a + 1) / 2 : ℝ) : ℂ), 1 / 2]
        ![((((x + y) / 2) ^ 2 : ℝ) : ℂ), ((x * y : ℝ) : ℂ)] := by
  let m := (x + y) / 2
  have hm : 0 < m := by dsimp only [m]; positivity
  have hleft := symmetricEllipticR_eq_integral (a := (a : ℂ)) (a' := 1)
    (b := ![1 / 2, 1 / 2, (a : ℂ)])
    (show 0 < (a : ℂ).re from ha) (by norm_num)
    (by simp [Fin.sum_univ_three]; ring) (vec3_mem_carlsonRSlitDomain
      (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hm))
  have hright := symmetricEllipticR_eq_integral (a := ((a / 2 : ℝ) : ℂ)) (a' := 1)
    (b := ![(((a + 1) / 2 : ℝ) : ℂ), 1 / 2])
    (by simp; positivity) (by norm_num)
    (by simp [Fin.sum_univ_two]; ring) (vec2_mem_carlsonRSlitDomain
      (ofReal_mem_slitPlane.mpr (sq_pos_of_pos hm)) (ofReal_mem_slitPlane.mpr (mul_pos hx hy)))
  rw [hleft, hright, Complex.betaIntegral_eval_one_right (show 0 < (a : ℂ).re from ha),
    Complex.betaIntegral_eval_one_right (by simp; positivity)]
  simp only [one_div, inv_inv, sub_self, cpow_zero, one_mul, Fin.prod_univ_three, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
  have H := integral_cpow_arithmetic_progression_quadratic (a := a) hx hy
  change (∫ u in Ioi (0 : ℝ), ((u + m ^ 2 : ℝ) : ℂ) ^ (((-(a + 1) / 2 : ℝ) : ℂ)) *
      ((u + x * y : ℝ) : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)) =
    2 * ∫ t in Ioi (0 : ℝ), ((t + x : ℝ) : ℂ) ^ ((-1 / 2 : ℝ) : ℂ) *
      ((t + y : ℝ) : ℂ) ^ ((-1 / 2 : ℝ) : ℂ) * ((t + m : ℝ) : ℂ) ^ ((-a : ℝ) : ℂ) at H
  push_cast at H ⊢
  norm_num only [neg_div] at H ⊢
  rw [H]
  ring

/-- Composing `R` with an analytic node map is analytic whenever the nodes stay on their
principal slit branches at the base point. -/
lemma analyticAt_symmetricEllipticR_comp {n : ℕ} (a : ℂ) (b : Fin n → ℂ)
    {f : ℂ → Fin n → ℂ} {w : ℂ} (hf : AnalyticAt ℂ f w)
    (hw : f w ∈ Carlson.carlsonRSlitDomain) :
    AnalyticAt ℂ (fun v => symmetricEllipticR a b (f v)) w := by
  have H : AnalyticAt ℂ (fun v => Carlson.carlsonR (-a) b (f v)) w := by
    unfold Carlson.carlsonR
    exact analyticAt_const.mul (Carlson.analyticAt_regCarlsonR_comp
      analyticAt_const analyticAt_const hf hw)
  apply H.congr
  filter_upwards [hf.continuousAt.eventually
      (Carlson.isOpen_carlsonRSlitDomain.mem_nhds hw)] with v hv
  exact (symmetricEllipticR_of_mem a b hv).symm

/-- The arithmetic-progression quadratic transformation continues to all pairs of nodes
in the open right half-plane. -/
lemma symmetricEllipticR_arithmetic_progression_quadratic {a : ℝ} (ha : 0 < a) {x y : ℂ}
    (hx : 0 < x.re) (hy : 0 < y.re) :
    symmetricEllipticR (a : ℂ) ![1 / 2, 1 / 2, (a : ℂ)] ![x, y, (x + y) / 2] =
      symmetricEllipticR ((a / 2 : ℝ) : ℂ) ![(((a + 1) / 2 : ℝ) : ℂ), 1 / 2]
        ![((x + y) / 2) ^ 2, x * y] := by
  have hm (X Y : ℂ) (hX : 0 < X.re) (hY : 0 < Y.re) : 0 < ((X + Y) / 2).re := by
    simp only [div_ofNat_re, add_re]; linarith
  apply Carlson.TwoVariable.eqOn_rightHalfPlane₂_of_real
    (F := fun X Y => symmetricEllipticR (a : ℂ) ![1 / 2, 1 / 2, (a : ℂ)] ![X, Y, (X + Y) / 2])
    (G := fun X Y => symmetricEllipticR ((a / 2 : ℝ) : ℂ) ![(((a + 1) / 2 : ℝ) : ℂ), 1 / 2]
      ![((X + Y) / 2) ^ 2, X * Y]) ?_ ?_ ?_ ?_ ?_ hx hy
  · intro Y hY X hX
    apply analyticAt_symmetricEllipticR_comp
    · apply analyticAt_pi_iff.mpr
      intro i; fin_cases i <;> dsimp <;> fun_prop
    · exact vec3_mem_carlsonRSlitDomain (Or.inl hX) (Or.inl hY) (Or.inl (hm X Y hX hY))
  · intro Y hY X hX
    apply analyticAt_symmetricEllipticR_comp
    · apply analyticAt_pi_iff.mpr
      intro i; fin_cases i <;> dsimp <;> fun_prop
    · exact vec2_mem_carlsonRSlitDomain
        (by simpa only [pow_two] using
          Carlson.mul_mem_slitPlane_of_re_pos (hm X Y hX hY) (hm X Y hX hY))
        (Carlson.mul_mem_slitPlane_of_re_pos hX hY)
  · intro X hX Y hY
    apply analyticAt_symmetricEllipticR_comp
    · apply analyticAt_pi_iff.mpr
      intro i; fin_cases i <;> dsimp <;> fun_prop
    · exact vec3_mem_carlsonRSlitDomain (Or.inl hX) (Or.inl hY) (Or.inl (hm X Y hX hY))
  · intro X hX Y hY
    apply analyticAt_symmetricEllipticR_comp
    · apply analyticAt_pi_iff.mpr
      intro i; fin_cases i <;> dsimp <;> fun_prop
    · exact vec2_mem_carlsonRSlitDomain
        (by simpa only [pow_two] using
          Carlson.mul_mem_slitPlane_of_re_pos (hm X Y hX hY) (hm X Y hX hY))
        (Carlson.mul_mem_slitPlane_of_re_pos hX hY)
  · intro X Y hY hYX
    have H := symmetricEllipticR_arithmetic_progression_quadratic_ofReal (hY.trans hYX) hY ha
    simpa only [ofReal_pow, ofReal_div, ofReal_add, ofReal_ofNat, ofReal_mul] using H

/-! ### §19.20(i) `R_F` -/

/-- DLMF 19.20.1 (first): `R_F(x, x, x) = x^{-1/2}`, `x ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.20.E1]
theorem symmetricEllipticRF_self {x : ℂ} (hx : x ∈ slitPlane) : symmetricEllipticRF x x x =
    x ^ (-1 / 2 : ℂ) := by
  rw [symmetricEllipticRF_eq_carlsonRF hx hx hx, Carlson.carlsonRF_self hx]

/-- DLMF 19.20.1 (second): `R_F(λx, λy, λz) = λ^{-1/2} R_F(x, y, z)`, `λ > 0`. -/
@[dlmf 19.20.E1]
theorem symmetricEllipticRF_smul {l : ℝ} (hl : 0 < l) {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    symmetricEllipticRF (l * x) (l * y) (l * z) = (l : ℂ) ^ (-1 / 2 : ℂ) *
        symmetricEllipticRF x y z := by
  rw [symmetricEllipticRF_eq_symmetricEllipticR (Complex.ofReal_mul_mem_slitPlane hl hx)
      (Complex.ofReal_mul_mem_slitPlane hl hy)
    (Complex.ofReal_mul_mem_slitPlane hl hz), symmetricEllipticRF_eq_symmetricEllipticR hx hy hz]
  have : (![(l : ℂ) * x, l * y, l * z] : Fin 3 → ℂ) = fun i => (l : ℂ) * ![x, y, z] i := by
    funext i; fin_cases i <;> rfl
  rw [this, symmetricEllipticR_ofReal_mul _ _ hl (vec3_mem_carlsonRSlitDomain hx hy hz)]
  congr 2; ring

/-- DLMF 19.20.1 (third): `R_F(x, y, y) = R_C(x, y)` (for every `x` and `y` not a negative real;
see `symmetricEllipticRC_eq_symmetricEllipticRF`). -/
@[dlmf 19.20.E1]
theorem symmetricEllipticRF_self_right (x : ℂ) {y : ℂ} (hy : ¬ IsNegReal y) :
    symmetricEllipticRF x y y = symmetricEllipticRC x y :=
  (symmetricEllipticRC_eq_symmetricEllipticRF x hy).symm

/-- DLMF 19.20.1 (fourth): `R_F(0, y, y) = (π/2) y^{-1/2}`, `y ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.20.E1]
theorem symmetricEllipticRF_zero_self {y : ℂ} (hy : y ∈ slitPlane) :
    symmetricEllipticRF 0 y y = (π / 2) * y ^ (-1 / 2 : ℂ) := by
  rw [symmetricEllipticRF_zero_left hy hy]
  have : (![y, y] : Fin 2 → ℂ) = fun _ => y := by funext i; fin_cases i <;> rfl
  rw [this, symmetricEllipticR_const _ _ hy (Complex.Gamma_ne_zero_of_re_pos (by simp))]
  congr 2; ring

/-- DLMF 19.20.1 (fifth): `R_F(0, 0, z) = ∞`: the defining integrand is not integrable. -/
@[dlmf 19.20.E1]
theorem not_integrableOn_symmetricEllipticRF_zero_zero {z : ℂ} (hz : z ∈ slitPlane) :
    ¬ IntegrableOn (fun t => (carlsonRootProduct 0 0 z t)⁻¹) (Ioi 0) :=
  not_integrableOn_symmetricEllipticRF_integrand_zero_zero hz

/-- DLMF 19.20.2: the first lemniscate constant
`∫₀¹ dt/√(1 - t⁴) = R_F(0, 1, 2) = Γ(1/4)² / (4 (2π)^{1/2})` (decimal value excluded: numerical). -/
@[dlmf 19.20.E2]
theorem lemniscate_first_symmetricEllipticRF :
    ((∫ t in (0 : ℝ)..1, 1 / Real.sqrt (1 - t ^ 4) : ℝ) : ℂ) = symmetricEllipticRF 0 1 2 ∧
      symmetricEllipticRF 0 1 2 = ((Real.Gamma (1 / 4) ^ 2 / (4 * Real.sqrt (2 * π)) : ℝ) : ℂ) := by
  rw [symmetricEllipticRF_zero_one_two, DLMF.Elliptic.integral_recip_sqrt_one_sub_pow_four]
  exact ⟨rfl, rfl⟩

/-- DLMF 19.20.3 (general lemniscatic case), **domain-restricted** to real `x, y > 0`:
`R_F(x, a, y) = R_{-1/4}(3/4, 1/2; a², xy)`, `a = (x + y)/2`. -/
@[dlmf 19.20.E3 "domain-restricted: real positive x, y; see the complex form for Re x, Re y > 0"]
theorem symmetricEllipticRF_lemniscatic {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    symmetricEllipticRF x ((x + y) / 2 : ℝ) y =
      symmetricEllipticR (1 / 4) ![3 / 4, 1 / 2]
          ![((((x + y) / 2) ^ 2 : ℝ) : ℂ), ((x * y : ℝ) : ℂ)] := by
  have hm : 0 < (x + y) / 2 := by positivity
  rw [symmetricEllipticRF_comm_right,
      symmetricEllipticRF_eq_symmetricEllipticR (ofReal_mem_slitPlane.mpr hx)
    (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hm)]
  have H := symmetricEllipticR_arithmetic_progression_quadratic_ofReal (a := 1 / 2) hx
      hy (by norm_num)
  norm_num at H
  have hb : (![1 / 2, 1 / 2, 1 / 2] : Fin 3 → ℂ) = fun _ => 1 / 2 := by
    funext i; fin_cases i <;> rfl
  rw [hb] at H
  convert H using 1 <;> norm_num


/-- DLMF 19.20.3, corrected complex form: `R_F(x, a, y) = R_{-1 / 4}(3 / 4, 1/2; a², xy)`,
`a = (x + y)/2`, for complex `x, y` with `ℜ x > 0` and `ℜ y > 0`. **Corrected from the printed DLMF
formula**: DLMF states it under the 19.16(i) constraints only, but it fails there, e.g. at
`x = -1 + i`, `y = -1 + 2i` the two sides differ by a factor `±i` (independent mpmath check,
2026-10-25). -/
@[dlmf 19.20.E3 "corrected: complex x, y with Re x, Re y > 0"]
theorem symmetricEllipticRF_lemniscatic_complex {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    symmetricEllipticRF x ((x + y) / 2) y =
      symmetricEllipticR (1 / 4) ![3 / 4, 1 / 2] ![((x + y) / 2) ^ 2, x * y] := by
  have hm : 0 < ((x + y) / 2).re := by simp only [div_ofNat_re, add_re]; linarith
  rw [symmetricEllipticRF_comm_right,
      symmetricEllipticRF_eq_symmetricEllipticR (Or.inl hx) (Or.inl hy) (Or.inl hm)]
  have H := symmetricEllipticR_arithmetic_progression_quadratic (a := 1 / 2) (by norm_num) hx hy
  norm_num at H
  have hb : (![1 / 2, 1 / 2, 1 / 2] : Fin 3 → ℂ) = fun _ => 1 / 2 := by
    funext i; fin_cases i <;> rfl
  rw [hb] at H
  exact H


/-! ### §19.20(ii) `R_G` -/

/-- DLMF 19.20.4 (first): `R_G(x, x, x) = x^{1/2}`. -/
@[dlmf 19.20.E4]
theorem symmetricEllipticRG_self {x : ℂ} (hx : x ∈ slitPlane) : symmetricEllipticRG x x x =
    x ^ (1 / 2 : ℂ) := by
  rw [symmetricEllipticRG_eq_symmetricEllipticR hx hx hx]
  have : (![x, x, x] : Fin 3 → ℂ) = fun _ => x := by funext i; fin_cases i <;> rfl
  rw [this, symmetricEllipticR_const _ _ hx (Complex.Gamma_ne_zero_of_re_pos (by simp))]
  congr 1; ring

/-- DLMF 19.20.4 (second): `R_G(λx, λy, λz) = λ^{1/2} R_G(x, y, z)`, `λ > 0`. -/
@[dlmf 19.20.E4]
theorem symmetricEllipticRG_smul {l : ℝ} (hl : 0 < l) {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    symmetricEllipticRG (l * x) (l * y) (l * z) = (l : ℂ) ^ (1 / 2 : ℂ) *
        symmetricEllipticRG x y z := by
  rw [symmetricEllipticRG_eq_symmetricEllipticR (Complex.ofReal_mul_mem_slitPlane hl hx)
      (Complex.ofReal_mul_mem_slitPlane hl hy)
    (Complex.ofReal_mul_mem_slitPlane hl hz), symmetricEllipticRG_eq_symmetricEllipticR hx hy hz]
  have : (![(l : ℂ) * x, l * y, l * z] : Fin 3 → ℂ) = fun i => (l : ℂ) * ![x, y, z] i := by
    funext i; fin_cases i <;> rfl
  rw [this, symmetricEllipticR_ofReal_mul _ _ hl (vec3_mem_carlsonRSlitDomain hx hy hz)]
  congr 2; ring

/-- `∫₀^∞ dt / ((t + z)^{1/2} (t + z)) = 2 z^{-1/2}` for `z ∈ ℂ \ (-∞, 0]`. -/
private lemma integral_Ioi_inv_cpow_half_mul {z : ℂ} (hz : z ∈ slitPlane) :
    ∫ t in Ioi (0 : ℝ), (((t : ℂ) + z) ^ (1 / 2 : ℂ) * ((t : ℂ) + z))⁻¹ =
      2 * (z ^ (1 / 2 : ℂ))⁻¹ := by
  obtain ⟨c1, hc1, h1⟩ := exists_mul_sqrt_add_one_le_norm_cpow_half hz
  obtain ⟨c2, hc2, h2⟩ := exists_mul_add_one_le_norm_ofReal_add hz
  have hz' : ∀ t : ℝ, 0 ≤ t → (t : ℂ) + z ∈ slitPlane := fun t ht => by
    rcases ht.eq_or_lt with rfl | ht
    · simpa using hz
    · exact ofReal_pos_add_mem_slitPlane ht (Or.inl hz)
  have hint : IntegrableOn (fun t : ℝ => (((t : ℂ) + z) ^ (1 / 2 : ℂ) * ((t : ℂ) + z))⁻¹)
      (Ioi 0) := by
    refine integrableOn_Ioi_of_norm_le_inv_sqrt_mul (C := (c1 * c2)⁻¹) ?_ fun t ht => ?_
    · refine ((continuousOn_ofReal_add_cpow_half (Or.inl hz)).mul
        (continuous_ofReal.add continuous_const).continuousOn).inv₀ fun t ht => ?_
      exact mul_ne_zero (ofReal_pos_add_cpow_half_ne_zero ht (Or.inl hz))
        (slitPlane_ne_zero (ofReal_pos_add_mem_slitPlane ht (Or.inl hz)))
    · have a1 := h1 t ht.le
      have a2 := h2 t ht.le
      have hs : Real.sqrt t ≤ Real.sqrt (t + 1) := Real.sqrt_le_sqrt (by linarith)
      have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
      rw [norm_inv, norm_mul, ← mul_inv]
      have hp : 0 < ‖((t : ℂ) + z) ^ (1 / 2 : ℂ)‖ * ‖(t : ℂ) + z‖ :=
        mul_pos (lt_of_lt_of_le (by positivity) a1) (lt_of_lt_of_le (by positivity) a2)
      rw [inv_le_inv₀ hp (by positivity)]
      calc c1 * c2 * (Real.sqrt t * (t + 1)) = (c1 * Real.sqrt t) * (c2 * (t + 1)) := by ring
        _ ≤ (c1 * Real.sqrt (t + 1)) * (c2 * (t + 1)) := by gcongr
        _ ≤ _ := mul_le_mul a1 a2 (by positivity) (norm_nonneg _)
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun s : ℝ => -2 * (((s : ℂ) + z) ^ (1 / 2 : ℂ))⁻¹)
      ((((t : ℂ) + z) ^ (1 / 2 : ℂ) * ((t : ℂ) + z))⁻¹) t := by
    intro t ht
    have h := ((hasDerivAt_ofReal_add_cpow_half (hz' t (le_of_lt ht))).inv
      (ofReal_pos_add_cpow_half_ne_zero ht (Or.inl hz))).const_mul (-2 : ℂ)
    convert h using 1
    have hu0 := ofReal_pos_add_cpow_half_ne_zero ht (Or.inl hz)
    have hw0 := slitPlane_ne_zero (ofReal_pos_add_mem_slitPlane ht (Or.inl hz))
    field_simp
  have hcont : ContinuousWithinAt (fun s : ℝ => -2 * (((s : ℂ) + z) ^ (1 / 2 : ℂ))⁻¹) (Ici 0) 0 :=
    (continuousAt_const.mul ((continuousAt_ofReal_add_cpow_half (hz' 0 le_rfl)).inv₀
      (cpow_half_ne_zero_of_mem_slitPlane (hz' 0 le_rfl)))).continuousWithinAt
  have hlim : Tendsto (fun s : ℝ => -2 * (((s : ℂ) + z) ^ (1 / 2 : ℂ))⁻¹) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun t => 2 * (c1 * Real.sqrt (t + 1))⁻¹) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with t ht
      have a1 := h1 t ht.le
      rw [norm_mul, norm_inv, norm_neg, Complex.norm_ofNat]
      gcongr
    · have : Tendsto (fun t : ℝ => Real.sqrt (t + 1)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)
      simpa using ((this.const_mul_atTop hc1).inv_tendsto_atTop).const_mul 2
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim]
  simp

/-- DLMF 19.20.4 (third and fourth): `R_G(0, y, y) = (π/4) y^{1/2}` and
`R_G(0, 0, z) = (1/2) z^{1/2}`, `y, z ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.20.E4]
theorem symmetricEllipticRG_zero_self {y z : ℂ} (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    symmetricEllipticRG 0 y y = (π / 4) * y ^ (1 / 2 : ℂ) ∧
      symmetricEllipticRG 0 0 z = (1 / 2) * z ^ (1 / 2 : ℂ) := by
  refine ⟨?_, ?_⟩
  · rw [(symmetricEllipticRG_zero_left hy hy).1]
    have : (![y, y] : Fin 2 → ℂ) = fun _ => y := by funext i; fin_cases i <;> rfl
    rw [this, symmetricEllipticR_const _ _ hy (Complex.Gamma_ne_zero_of_re_pos (by simp))]
    congr 2; ring
  · have hI := integral_Ioi_inv_cpow_half_mul hz
    have e : ∀ t ∈ Ioi (0 : ℝ), (carlsonRootProduct 0 0 z t)⁻¹ *
        (0 / ((t : ℂ) + 0) + 0 / ((t : ℂ) + 0) + z / ((t : ℂ) + z)) * t =
        z * (((t : ℂ) + z) ^ (1 / 2 : ℂ) * ((t : ℂ) + z))⁻¹ := by
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
      simp only [carlsonRootProduct, add_zero, zero_div, zero_add]
      rw [cpow_half_mul_cpow_half]
      have hu0 := ofReal_pos_add_cpow_half_ne_zero ht (Or.inl hz)
      have hw0 := slitPlane_ne_zero (ofReal_pos_add_mem_slitPlane ht (Or.inl hz))
      field_simp
    rw [symmetricEllipticRG, setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul, hI]
    have hz0 := cpow_half_ne_zero_of_mem_slitPlane hz
    have hsq := cpow_half_mul_cpow_half z
    field_simp
    linear_combination (-4 : ℂ) * hsq

/-- DLMF 19.20.5: `2 R_G(x, y, y) = y R_C(x, y) + √x`, `x` admissible, `y ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.20.E5]
theorem two_mul_symmetricEllipticRG_self_right {x y : ℂ} (hx : IsCarlsonArgument x)
    (hy : y ∈ slitPlane) :
    2 * symmetricEllipticRG x y y = y * symmetricEllipticRC x y + x ^ (1 / 2 : ℂ) := by
  rw [two_mul_symmetricEllipticRG hx hy hy, symmetricEllipticRC_eq_symmetricEllipticRF x
    (not_isNegReal_of_mem_slitPlane hy)]
  have hy0 : y ^ (1 / 2 : ℂ) ≠ 0 := cpow_half_ne_zero_of_mem_slitPlane hy
  rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, cpow_neg]
  field_simp
  ring

/-! ### §19.20(iii) `R_J` -/

/-- DLMF 19.20.6 (first): `R_J(x, x, x, x) = x^{-3/2}`. -/
@[dlmf 19.20.E6]
theorem symmetricEllipticRJ_self {x : ℂ} (hx : x ∈ slitPlane) :
    symmetricEllipticRJ x x x x = x ^ (-3 / 2 : ℂ) := by
  rw [symmetricEllipticRJ_eq_symmetricEllipticR hx hx hx hx]
  have : (![x, x, x, x] : Fin 4 → ℂ) = fun _ => x := by funext i; fin_cases i <;> rfl
  have hG : Gamma (∑ i, (![1 / 2, 1 / 2, 1 / 2, 1] : Fin 4 → ℂ) i) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp [Fin.sum_univ_four]; norm_num)
  rw [this, symmetricEllipticR_const _ _ hx hG]
  congr 1; ring

/-- DLMF 19.20.6 (second): `R_J(λx, λy, λz, λp) = λ^{-3/2} R_J(x, y, z, p)`, `λ > 0`
(slit-plane variables). -/
@[dlmf 19.20.E6]
theorem symmetricEllipticRJ_smul {l : ℝ} (hl : 0 < l) {x y z p : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    symmetricEllipticRJ (l * x) (l * y) (l * z) (l * p) = (l : ℂ) ^ (-3 / 2 : ℂ) *
        symmetricEllipticRJ x y z p := by
  rw [symmetricEllipticRJ_eq_symmetricEllipticR (Complex.ofReal_mul_mem_slitPlane hl hx)
      (Complex.ofReal_mul_mem_slitPlane hl hy)
    (Complex.ofReal_mul_mem_slitPlane hl hz) (Complex.ofReal_mul_mem_slitPlane hl hp),
    symmetricEllipticRJ_eq_symmetricEllipticR hx hy hz hp]
  have : (![(l : ℂ) * x, l * y, l * z, l * p] : Fin 4 → ℂ) =
      fun i => (l : ℂ) * ![x, y, z, p] i := by
    funext i; fin_cases i <;> rfl
  rw [this, symmetricEllipticR_ofReal_mul _ _ hl (vec4_mem_carlsonRSlitDomain hx hy hz hp)]
  congr 2; ring

/-- DLMF 19.20.6 (third) and 19.20.8 (fourth): `R_J(x, y, z, z) = R_D(x, y, z)` (definitional). -/
@[dlmf 19.20.E6, dlmf 19.20.E8]
theorem symmetricEllipticRJ_self_right (x y z : ℂ) : symmetricEllipticRJ x y z z =
    symmetricEllipticRD x y z := rfl

/-- DLMF 19.20.6 (fourth): `R_J(0, 0, z, p) = ∞`: the defining integrand is not integrable. -/
@[dlmf 19.20.E6]
theorem not_integrableOn_symmetricEllipticRJ_zero_zero {z p : ℂ} (hz : z ∈ slitPlane)
    (hp : p ∈ slitPlane) :
    ¬ IntegrableOn (fun t => (carlsonRootProduct 0 0 z t * ((t : ℂ) + p))⁻¹) (Ioi 0) :=
  not_integrableOn_symmetricEllipticRJ_integrand_zero_zero hz hp

/-- DLMF 19.20.6 (fifth, first equality): `R_J(x, x, x, p) = R_D(p, p, x)`, for `x, p` not
negative reals (stronger than DLMF: no further condition; the integrands agree). -/
@[dlmf 19.20.E6]
theorem symmetricEllipticRJ_self_self_self (p : ℂ) {x : ℂ} (hx : ¬ IsNegReal x)
    (hp : ¬ IsNegReal p) :
    symmetricEllipticRJ x x x p = symmetricEllipticRD p p x := by
  simp only [symmetricEllipticRD, symmetricEllipticRJ, hx, hp, ↓reduceIte, carlsonRootProduct]
  congr 2; funext t
  rw [mul_assoc (((t : ℂ) + x) ^ (1 / 2 : ℂ)), cpow_half_mul_cpow_half,
    cpow_half_mul_cpow_half ((t : ℂ) + p)]
  ring

/-- DLMF 19.20.6 (fifth, second equality): `R_J(x, x, x, p) = 3/(x - p) (R_C(x, p) - 1/√x)`,
`x ≠ p`, `xp ≠ 0`; `x ∈ ℂ \ (-∞, 0]`, `p ∈ ℂ \ (-∞, 0]` (principal-value case: see 19.20.8). -/
@[dlmf 19.20.E6]
theorem symmetricEllipticRJ_self_self_self_eq {x p : ℂ} (hx : x ∈ slitPlane) (hp : p ∈ slitPlane)
    (hxp : x ≠ p) :
    symmetricEllipticRJ x x x p = 3 / (x - p) *
        (symmetricEllipticRC x p - 1 / x ^ (1 / 2 : ℂ)) := by
  rw [symmetricEllipticRJ_self_self_self p (not_isNegReal_of_mem_slitPlane hx)
    (not_isNegReal_of_mem_slitPlane hp)]
  exact symmetricEllipticRD_self_left_eq_sub_symmetricEllipticRC hp hx (Ne.symm hxp)

/-- DLMF 19.20.7: `R_J(x, y, z, p) → +∞` as `p → 0±`, for `x, y, z > 0` (for `p < 0` the
principal value). -/
@[dlmf 19.20.E7]
theorem tendsto_symmetricEllipticRJ_zero {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Tendsto (fun p : ℝ => (symmetricEllipticRJ x y z p).re) (𝓝[≠] 0) atTop := by
  sorry

/-- DLMF 19.20.8 (first): `R_J(0, y, y, p) = 3π / (2(y√p + p√y))`, `p > 0`, `y ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.20.E8]
theorem symmetricEllipticRJ_zero_self_self {y : ℂ} (hy : y ∈ slitPlane) {p : ℝ} (hp : 0 < p) :
    symmetricEllipticRJ 0 y y p = 3 * π /
        (2 * (y * (p : ℂ) ^ (1 / 2 : ℂ) + p * y ^ (1 / 2 : ℂ))) := by
  have hp' : (p : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hp
  have e : ∀ w : ℂ, w ^ (-1 / 2 : ℂ) = (w ^ (1 / 2 : ℂ))⁻¹ := fun w => by
    rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, cpow_neg]
  have hRC : ∀ w : ℂ, w ∈ slitPlane → symmetricEllipticRC 0 w = (π / 2) * (w ^ (1 / 2 : ℂ))⁻¹ :=
    fun w hw => by
      rw [← symmetricEllipticRF_self_right 0 (not_isNegReal_of_mem_slitPlane hw),
        symmetricEllipticRF_zero_self hw, e]
  have hY0 := cpow_half_ne_zero_of_mem_slitPlane hy
  have hP0 := cpow_half_ne_zero_of_mem_slitPlane hp'
  have hY2 := Carlson.cpow_half_sq y
  have hP2 := Carlson.cpow_half_sq (p : ℂ)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  by_cases hpy : (p : ℂ) = y
  · have hD : symmetricEllipticRD 0 (p : ℂ) p = (3 * π / 4) * (p : ℂ) ^ (-3 / 2 : ℂ) := by
      rw [symmetricEllipticRD_zero_left hp' hp']
      have : (![(p : ℂ), p] : Fin 2 → ℂ) = fun _ => (p : ℂ) := by funext i; fin_cases i <;> rfl
      rw [this, symmetricEllipticR_const _ _ hp'
          (Complex.Gamma_ne_zero_of_re_pos (by simp; norm_num))]
      congr 2; ring
    rw [← hpy, symmetricEllipticRJ_self_right, hD]
    rw [show (-3 / 2 : ℂ) = -(1 / 2) + (-1) by norm_num, cpow_add _ _ (slitPlane_ne_zero hp'),
      cpow_neg_one, cpow_neg]
    have hp0 : (p : ℂ) ≠ 0 := slitPlane_ne_zero hp'
    field_simp
    ring
  · rw [symmetricEllipticRJ_self_right_eq_sub_symmetricEllipticRC (Or.inr rfl) hy hp' hpy,
        hRC y hy, hRC _ hp']
    generalize y ^ (1 / 2 : ℂ) = Y at *
    generalize (p : ℂ) ^ (1 / 2 : ℂ) = P at *
    generalize (p : ℂ) = q at *
    subst hY2 hP2
    have h1 : P - Y ≠ 0 := fun h => hpy (by rw [sub_eq_zero.mp h])
    have h2 : P + Y ≠ 0 := fun h => hpy (by rw [eq_neg_of_add_eq_zero_left h]; ring)
    have h3 : P ^ 2 - Y ^ 2 ≠ 0 := by
      rw [show P ^ 2 - Y ^ 2 = (P - Y) * (P + Y) by ring]; exact mul_ne_zero h1 h2
    have h4 : Y ^ 2 * P + P ^ 2 * Y ≠ 0 := by
      rw [show Y ^ 2 * P + P ^ 2 * Y = Y * P * (P + Y) by ring]
      exact mul_ne_zero (mul_ne_zero hY0 hP0) h2
    rw [eq_div_iff (mul_ne_zero two_ne_zero h4)]
    field_simp
    rw [show P ^ 2 - Y ^ 2 = (P - Y) * (P + Y) by ring]
    field_simp
    ring

/-- DLMF 19.20.8 (third), principal-value case, by partial fractions in the truncated
integrals. -/
private lemma symmetricEllipticRJ_self_right_of_neg_aux {x y p : ℝ} (hx : 0 ≤ x)
    (hy : 0 < y) (hp : p < 0) :
    symmetricEllipticRJ x y y p = 3 / ((p : ℂ) - y) *
        (symmetricEllipticRC x y - symmetricEllipticRC x p) := by
  set A : ℝ → Set ℝ := fun ε => Ioi (0 : ℝ) \ Icc (-p - ε) (-p + ε) with hA
  set F : ℝ → ℂ := fun t => (carlsonRootProduct x y y t)⁻¹ with hF
  set g : ℝ → ℂ := fun t => (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + y))⁻¹ with hg
  set h : ℝ → ℂ := fun t => (((t : ℂ) + x) ^ (1 / 2 : ℂ) * ((t : ℂ) + p))⁻¹ with hh
  set f : ℝ → ℂ := fun t => (carlsonRootProduct x y y t * ((t : ℂ) + p))⁻¹ with hf
  have hxa : (x : ℂ) ∈ slitPlane ∨ (x : ℂ) = 0 := by
    rcases hx.eq_or_lt with h0 | h0
    · right; simp [← h0]
    · left; exact ofReal_mem_slitPlane.mpr h0
  have hys : (y : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hy
  have hFi : IntegrableOn F (Ioi 0) := by
    simpa [F, carlsonRootProduct] using integrableOn_symmetricEllipticRF_integrand hxa hys hys
  have hgF : ∀ t ∈ Ioi (0 : ℝ), g t = F t := by
    intro t _
    simp only [g, F, carlsonRootProduct, mul_assoc, cpow_half_mul_cpow_half]
  have hgi : IntegrableOn g (Ioi 0) :=
    hFi.congr_fun (fun t ht => (hgF t ht).symm) measurableSet_Ioi
  have hAm : ∀ ε, MeasurableSet (A ε) := fun ε => measurableSet_Ioi.diff measurableSet_Icc
  have hmemA : ∀ ε, ∀ t ∈ A ε, 0 < t ∧ ε < |t + p| := by
    intro ε t ht
    refine ⟨ht.1, ?_⟩
    by_contra hc
    push Not at hc
    exact ht.2 ⟨by linarith [(abs_le.mp hc).1], by linarith [(abs_le.mp hc).2]⟩
  have hpy : (p : ℂ) - y ≠ 0 := by
    rw [← ofReal_sub]; exact ofReal_ne_zero.mpr (by linarith)
  have hfid : ∀ t, 0 < t → t ≠ -p → f t = ((p : ℂ) - y)⁻¹ * (g t - h t) := by
    intro t ht htp
    have h1 : ((t : ℂ) + x) ^ (1 / 2 : ℂ) ≠ 0 := ofReal_pos_add_cpow_half_ne_zero ht hxa
    have h2 : (t : ℂ) + y ≠ 0 := slitPlane_ne_zero (ofReal_pos_add_mem_slitPlane ht (Or.inl hys))
    have h3 : (t : ℂ) + p ≠ 0 := by
      rw [← ofReal_add]; exact ofReal_ne_zero.mpr (fun e => htp (by linarith))
    simp only [f, g, h, carlsonRootProduct, mul_assoc, cpow_half_mul_cpow_half]
    field_simp
    ring
  have hhi : ∀ ε, 0 < ε → IntegrableOn h (A ε) := by
    intro ε hε
    have hmeas : AEStronglyMeasurable h (volume.restrict (A ε)) :=
      (by fun_prop : Measurable h).aestronglyMeasurable
    refine Integrable.mono' ((hgi.mono_set sdiff_subset).norm.mul_const (1 + (y - p) / ε)) hmeas ?_
    refine (ae_restrict_mem (hAm ε)).mono fun t ht => ?_
    obtain ⟨ht0, htp⟩ := hmemA ε t ht
    have h3 : (t : ℂ) + p ≠ 0 := by
      rw [← ofReal_add]; exact ofReal_ne_zero.mpr (fun e => by simp [e] at htp; linarith)
    have hht : h t = g t * (((t : ℂ) + y) / ((t : ℂ) + p)) := by
      have h1 : ((t : ℂ) + x) ^ (1 / 2 : ℂ) ≠ 0 := ofReal_pos_add_cpow_half_ne_zero ht0 hxa
      have h2 : (t : ℂ) + y ≠ 0 :=
        slitPlane_ne_zero (ofReal_pos_add_mem_slitPlane ht0 (Or.inl hys))
      simp only [g, h]; field_simp
    rw [hht, norm_mul]
    gcongr
    rw [← ofReal_add, ← ofReal_add, ← ofReal_div, norm_real, Real.norm_eq_abs,
      abs_div, abs_of_pos (by linarith : 0 < t + y)]
    have hap : 0 < |t + p| := lt_trans hε htp
    rw [div_le_iff₀ hap]
    have : t + y ≤ |t + p| + (y - p) := by linarith [le_abs_self (t + p)]
    have h2 : (y - p) / ε * |t + p| ≥ (y - p) := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hε]
      nlinarith
    nlinarith
  have hkey : ∀ ε, 0 < ε → ∫ t in A ε, f t =
      ((p : ℂ) - y)⁻¹ * ((∫ t in A ε, g t) - ∫ t in A ε, h t) := by
    intro ε hε
    rw [setIntegral_congr_fun (hAm ε) (fun t ht => hfid t (hmemA ε t ht).1 (fun e => by
      have := (hmemA ε t ht).2; rw [e, neg_add_cancel, abs_zero] at this; linarith)),
      integral_const_mul, integral_sub (hgi.mono_set sdiff_subset) (hhi ε hε)]
  have hlg := tendsto_setIntegral_diff_Icc_nhdsGT hgi (-p)
  have hlh := tendsto_integral_symmetricEllipticRC_truncated hx hp
  have hgv : ∫ t in Ioi (0 : ℝ), g t = 2 * symmetricEllipticRC x y := by
    rw [symmetricEllipticRC_eq_integral
      (fun hn => by have := hn.2; simp at this; linarith : ¬ IsNegReal (y : ℂ))]
    ring
  have hlim : Tendsto (fun ε => ∫ t in A ε, f t) (𝓝[>] 0)
      (𝓝 (((p : ℂ) - y)⁻¹ * (2 * symmetricEllipticRC x y - 2 * symmetricEllipticRC x p))) := by
    rw [← hgv]
    refine ((hlg.sub hlh).const_mul _).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hkey ε hε).symm
  have hneg : IsNegReal (p : ℂ) := ⟨by simp, by simpa using hp⟩
  simp only [symmetricEllipticRJ, hneg, ↓reduceIte, principalValueIoi, ofReal_re]
  rw [hlim.limUnder_eq]
  field_simp


/-- DLMF 19.20.8 (second): `R_J(0, y, y, -q) = -3π / (2√y (y + q))`, `q > 0` (Cauchy principal
value), `y > 0`. -/
@[dlmf 19.20.E8]
theorem symmetricEllipticRJ_zero_self_self_neg {y q : ℝ} (hy : 0 < y) (hq : 0 < q) :
    symmetricEllipticRJ 0 y y (-q : ℝ) = -3 * π / (2 * (y : ℂ) ^ (1 / 2 : ℂ) * (y + q)) := by
  have H := symmetricEllipticRJ_self_right_of_neg_aux le_rfl hy (by linarith : -q < 0)
  have hys : (y : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hy
  have hRC : symmetricEllipticRC 0 (y : ℂ) = (π / 2) * ((y : ℂ) ^ (1 / 2 : ℂ))⁻¹ := by
    rw [← symmetricEllipticRF_self_right 0 (not_isNegReal_of_mem_slitPlane hys),
      symmetricEllipticRF_zero_self hys, show (-1 / 2 : ℂ) = -(1 / 2) by ring, cpow_neg]
  have hRC0 : symmetricEllipticRC ((0 : ℝ) : ℂ) ((-q : ℝ) : ℂ) = 0 := by
    rw [(symmetricEllipticRC_of_neg (by linarith : -q < 0) le_rfl).2.2]
    simp
  rw [ofReal_zero] at H hRC0
  rw [H, hRC, hRC0]
  have hY0 := cpow_half_ne_zero_of_mem_slitPlane hys
  have h1 : ((y : ℂ) + q) ≠ 0 := by rw [← ofReal_add]; exact ofReal_ne_zero.mpr (by linarith)
  have h2 : ((-q : ℝ) : ℂ) - y ≠ 0 := by
    rw [← ofReal_sub]; exact ofReal_ne_zero.mpr (by linarith)
  push_cast at h2 ⊢
  field_simp
  ring


/-- DLMF 19.20.8 (third): `R_J(x, y, y, p) = 3/(p - y) (R_C(x, y) - R_C(x, p))`, `p ≠ y`,
for `x` admissible, `y, p ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.20.E8]
theorem symmetricEllipticRJ_self_right_eq {x y p : ℂ} (hx : IsCarlsonArgument x)
    (hy : y ∈ slitPlane)
    (hp : p ∈ slitPlane) (hpy : p ≠ y) :
    symmetricEllipticRJ x y y p = 3 / (p - y) *
        (symmetricEllipticRC x y - symmetricEllipticRC x p) :=
  symmetricEllipticRJ_self_right_eq_sub_symmetricEllipticRC hx hy hp hpy

/-- DLMF 19.20.8 (third), principal-value case: real `x ≥ 0`, `y > 0`, `p < 0`. -/
@[dlmf 19.20.E8]
theorem symmetricEllipticRJ_self_right_eq_of_neg {x y p : ℝ} (hx : 0 ≤ x)
    (hy : 0 < y) (hp : p < 0) :
    symmetricEllipticRJ x y y p = 3 / ((p : ℂ) - y) *
        (symmetricEllipticRC x y - symmetricEllipticRC x p) :=
  symmetricEllipticRJ_self_right_of_neg_aux hx hy hp

/-- DLMF 19.20.9: `R_J(0, y, z, ±√(yz)) = ±3/(2√(yz)) R_F(0, y, z)`, `y, z > 0` (the lower sign
is a Cauchy principal value). -/
@[dlmf 19.20.E9]
theorem symmetricEllipticRJ_zero_sqrt {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    symmetricEllipticRJ 0 y z (Real.sqrt (y * z) : ℝ) =
        3 / (2 * Real.sqrt (y * z) : ℝ) * symmetricEllipticRF 0 y z ∧
      symmetricEllipticRJ 0 y z (-Real.sqrt (y * z) : ℝ) =
        -(3 / (2 * Real.sqrt (y * z) : ℝ)) * symmetricEllipticRF 0 y z := by
  have hr : 0 < Real.sqrt (y * z) := Real.sqrt_pos.mpr (mul_pos hy hz)
  have hr2 : Real.sqrt (y * z) * Real.sqrt (y * z) = y * z := Real.mul_self_sqrt (by positivity)
  have h1 := mul_symmetricEllipticRJ_zero_add_mul hy hz hr.ne' hr2
  have h2 := mul_symmetricEllipticRJ_zero_add_mul hy hz (neg_ne_zero.mpr hr.ne')
    (by rw [neg_mul_neg]; exact hr2)
  have hr' : ((Real.sqrt (y * z) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  push_cast at h1 h2 ⊢
  constructor
  · field_simp
    linear_combination h1
  · field_simp
    linear_combination -h2

/-- DLMF 19.20.10: `lim_{p→0+} √p R_J(0, y, z, p) = 3π/(2√y√z)` and
`lim_{p→0-} R_J(0, y, z, p) = -R_D(0, y, z) - R_D(0, z, y) = -6/(yz) R_G(0, y, z)`, for
`y, z > 0`. -/
@[dlmf 19.20.E10]
theorem tendsto_symmetricEllipticRJ_zero_left {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    Tendsto (fun p : ℝ => (Real.sqrt p : ℂ) * symmetricEllipticRJ 0 y z p) (𝓝[>] 0)
        (𝓝 (3 * π / (2 * Real.sqrt y * Real.sqrt z) : ℝ)) ∧
      Tendsto (fun p : ℝ => symmetricEllipticRJ 0 y z p) (𝓝[<] 0)
        (𝓝 (-symmetricEllipticRD 0 y z - symmetricEllipticRD 0 z y)) ∧
      -symmetricEllipticRD 0 y z - symmetricEllipticRD 0 z y = -6 / ((y : ℂ) * z) *
          symmetricEllipticRG 0 y z := by
  sorry

/-- DLMF 19.20.11: `R_J(0, y, z, p) = 3/(2p√z) ln(16z/y) - (3/p) R_C(z, p) + O(y ln y)` as
`y → 0+`, for real `p ≠ 0` and `z > 0`. -/
@[dlmf 19.20.E11]
theorem symmetricEllipticRJ_zero_asymptotic {z p : ℝ} (hz : 0 < z) (hp : p ≠ 0) :
    (fun y : ℝ => symmetricEllipticRJ 0 y z p -
        ((3 / (2 * p * Real.sqrt z) * Real.log (16 * z / y) : ℝ) -
        3 / (p : ℂ) * symmetricEllipticRC z p)) =O[𝓝[>] 0] fun y => ((y * Real.log y : ℝ) : ℂ) := by
  sorry

/-- A lower bound `u / 2 ≤ ‖u + w‖` for real `u ≥ 2‖w‖`. -/
private theorem half_le_norm_ofReal_add {w : ℂ} {u : ℝ} (hu : 2 * ‖w‖ ≤ u) :
    u / 2 ≤ ‖(u : ℂ) + w‖ := by
  have h1 := norm_sub_norm_le (u : ℂ) (-w)
  rw [sub_neg_eq_add, norm_neg, norm_real,
    Real.norm_of_nonneg (by linarith [norm_nonneg w])] at h1
  linarith

/-- `u + w` lies in the slit plane when `u > 0` and `u ≥ 2‖w‖`. -/
private theorem ofReal_add_mem_slitPlane_of_le {w : ℂ} {u : ℝ} (hu : 2 * ‖w‖ ≤ u) (hu0 : 0 < u) :
    (u : ℂ) + w ∈ slitPlane := by
  left
  simp only [add_re, ofReal_re]
  have := neg_abs_le w.re
  have := abs_re_le_norm w
  linarith

/-- A bound for `‖(u + w)^r‖` with `r ≤ 0` when `u ≥ 2‖w‖`. -/
private theorem norm_ofReal_add_cpow_le {w : ℂ} {u : ℝ} (hu : 2 * ‖w‖ ≤ u) (hu0 : 0 < u) {r : ℝ}
    (hr : r ≤ 0) : ‖((u : ℂ) + w) ^ (r : ℂ)‖ ≤ (u / 2) ^ r := by
  rw [norm_cpow_real]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (half_le_norm_ofReal_add hu) hr

/-- A Lipschitz bound for `u ↦ (u + w)^(-1/2)` on `[T, ∞)` with `T ≥ 2‖w‖`. -/
private theorem norm_ofReal_add_cpow_neg_half_sub_le {w : ℂ} {T u v : ℝ} (hT : 0 < T)
    (hTw : 2 * ‖w‖ ≤ T) (hu : T ≤ u) (hv : T ≤ v) :
    ‖((u : ℂ) + w) ^ (-(1 / 2) : ℂ) - ((v : ℂ) + w) ^ (-(1 / 2) : ℂ)‖ ≤
      (1 / 2) * (T / 2) ^ (-(3 / 2) : ℝ) * |u - v| := by
  have hder : ∀ s ∈ Ici T, HasDerivWithinAt (fun s : ℝ => ((s : ℂ) + w) ^ (-(1 / 2) : ℂ))
      ((-(1 / 2) : ℂ) * ((s : ℂ) + w) ^ ((-(1 / 2) : ℂ) - 1) * 1) (Ici T) s := by
    intro s hs
    have hs' : T ≤ s := hs
    have hmem := ofReal_add_mem_slitPlane_of_le (w := w) (by linarith) (by linarith)
    have H := ((hasDerivAt_id (s : ℂ)).add_const w).cpow_const (c := (-(1 / 2) : ℂ)) hmem
    exact (H.comp_ofReal).hasDerivWithinAt
  have hb : ∀ s ∈ Ici T, ‖(-(1 / 2) : ℂ) * ((s : ℂ) + w) ^ ((-(1 / 2) : ℂ) - 1) * 1‖ ≤
      (1 / 2) * (T / 2) ^ (-(3 / 2) : ℝ) := by
    intro s hs
    have hs' : T ≤ s := hs
    rw [mul_one, norm_mul, show (-(1 / 2) : ℂ) - 1 = ((-(3 / 2) : ℝ) : ℂ) by push_cast; ring]
    simp only [norm_neg, norm_div, norm_one, Complex.norm_ofNat]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (norm_ofReal_add_cpow_le (by linarith) (by linarith) (by norm_num)).trans ?_
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hb (convex_Ici T)
    (show v ∈ Ici T from hv) (show u ∈ Ici T from hu)
  rwa [Real.norm_eq_abs] at this


/-- A bound for `‖(u + w)^(-1/2)‖` on `[T, ∞)` with `T ≥ 2‖w‖`. -/
private theorem norm_ofReal_add_cpow_neg_half_le_of_le {w : ℂ} {T u : ℝ} (hT : 0 < T)
    (hTw : 2 * ‖w‖ ≤ T) (hu : T ≤ u) :
    ‖((u : ℂ) + w) ^ (-(1 / 2) : ℂ)‖ ≤ (T / 2) ^ (-(1 / 2) : ℝ) := by
  have h := norm_ofReal_add_cpow_le (w := w) (u := u) (by linarith) (by linarith)
    (r := -(1 / 2)) (by norm_num)
  push_cast at h
  exact h.trans (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num))

/-- The factor `s(t)⁻¹` of the `R_F` integrand as a product of three powers. -/
private theorem carlsonRootProduct_inv_eq_mul (x y z : ℂ) (t : ℝ) :
    (carlsonRootProduct x y z t)⁻¹ = ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) := by
  simp only [carlsonRootProduct, mul_inv, cpow_neg]

/-- Telescoping bound for the difference of `s(t)⁻¹` at two large arguments. -/
private theorem norm_carlsonRootProduct_inv_sub_le {x y z : ℂ} {T t c : ℝ} (hT : 0 < T)
    (hx : 2 * ‖x‖ ≤ T)
    (hy : 2 * ‖y‖ ≤ T) (hz : 2 * ‖z‖ ≤ T) (ht : T ≤ t) (hc : T ≤ c) :
    ‖(carlsonRootProduct x y z t)⁻¹ - (carlsonRootProduct x y z c)⁻¹‖ ≤
      3 * ((T / 2) ^ (-(1 / 2) : ℝ)) ^ 2 * ((1 / 2) * (T / 2) ^ (-(3 / 2) : ℝ)) * |t - c| := by
  rw [carlsonRootProduct_inv_eq_mul, carlsonRootProduct_inv_eq_mul]
  set P := (T / 2) ^ (-(1 / 2) : ℝ)
  set D := (1 / 2) * (T / 2) ^ (-(3 / 2) : ℝ) * |t - c|
  have hP0 : 0 ≤ P := by positivity
  have ha1 := norm_ofReal_add_cpow_neg_half_le_of_le hT hx ht
  have ha2 := norm_ofReal_add_cpow_neg_half_le_of_le hT hy ht
  have ha3 := norm_ofReal_add_cpow_neg_half_le_of_le hT hz ht
  have hb1 := norm_ofReal_add_cpow_neg_half_le_of_le hT hx hc
  have hb2 := norm_ofReal_add_cpow_neg_half_le_of_le hT hy hc
  have hd1 := norm_ofReal_add_cpow_neg_half_sub_le hT hx ht hc
  have hd2 := norm_ofReal_add_cpow_neg_half_sub_le hT hy ht hc
  have hd3 := norm_ofReal_add_cpow_neg_half_sub_le hT hz ht hc
  set a1 := ((t : ℂ) + x) ^ (-(1 / 2) : ℂ)
  set a2 := ((t : ℂ) + y) ^ (-(1 / 2) : ℂ)
  set a3 := ((t : ℂ) + z) ^ (-(1 / 2) : ℂ)
  set b1 := ((c : ℂ) + x) ^ (-(1 / 2) : ℂ)
  set b2 := ((c : ℂ) + y) ^ (-(1 / 2) : ℂ)
  set b3 := ((c : ℂ) + z) ^ (-(1 / 2) : ℂ)
  have hid : a1 * a2 * a3 - b1 * b2 * b3 =
      (a1 - b1) * a2 * a3 + b1 * (a2 - b2) * a3 + b1 * b2 * (a3 - b3) := by ring
  rw [hid]
  refine norm_add₃_le.trans ?_
  simp only [norm_mul]
  have e1 : ‖a1 - b1‖ * ‖a2‖ * ‖a3‖ ≤ D * P * P := by
    gcongr
  have e2 : ‖b1‖ * ‖a2 - b2‖ * ‖a3‖ ≤ P * D * P := by
    gcongr
  have e3 : ‖b1‖ * ‖b2‖ * ‖a3 - b3‖ ≤ P * P * D := by
    gcongr
  have : D * P * P + P * D * P + P * P * D =
      3 * P ^ 2 * ((1 / 2) * (T / 2) ^ (-(3 / 2) : ℝ)) * |t - c| := by
    simp only [D]; ring
  linarith

/-- The principal value `(2/3) R_J(x, y, z, -c)` as the integral of the integrand minus
its singular part. -/
private theorem two_thirds_symmetricEllipticRJ_neg_eq {x y z : ℂ} (hx : x ∈ slitPlane ∨ x = 0)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) {c : ℝ} (hc : 0 < c) :
    (2 / 3) * symmetricEllipticRJ x y z (-c : ℝ) = ∫ t in Ioi 0,
        ((carlsonRootProduct x y z t * ((t : ℂ) - c))⁻¹ -
      (Icc (c / 2) (3 * c / 2)).indicator
        (fun t : ℝ => (carlsonRootProduct x y z c)⁻¹ / ((t : ℂ) - c)) t) := by
  have hG := integrableOn_carlsonRootProduct_mul_sub_inv_sub_indicator hx hy hz hc
  have hsub : Icc (c / 2) (3 * c / 2) ⊆ Ioi 0 := fun t ht => by
    simp only [mem_Ioi]; linarith [ht.1]
  have h1 := tendsto_setIntegral_diff_Icc_symm_of_integrableOn_sub _ (by linarith)
    (by linarith) measurableSet_Ioi hsub hG
  have h2 := tendsto_integral_symmetricEllipticRJ_of_neg_symm hx hy hz (p := -c) (by linarith)
  simp only [neg_neg, ofReal_neg, ← sub_eq_add_neg] at h2
  have h := tendsto_nhds_unique h2 h1
  rw [ofReal_neg, h, show (3 * c / 2 - c) / (c - c / 2) = 1 by field_simp; ring, Real.log_one,
    ofReal_zero, mul_zero, add_zero]


/-- `|t / (t - c)| ≤ 2` off the interval `[c/2, 3c/2]`. -/
private theorem abs_div_sub_le_two {c t : ℝ} (hc : 0 < c) (ht : t ∉ Icc (c / 2) (3 * c / 2)) :
    |c / (c - t)| ≤ 2 := by
  simp only [mem_Icc, not_and_or, not_le] at ht
  rcases ht with ht | ht
  · rw [abs_of_pos (div_pos hc (by linarith)), div_le_iff₀ (by linarith)]; linarith
  · rw [abs_div, abs_of_pos hc, abs_of_neg (by linarith), div_le_iff₀ (by linarith)]; linarith

/-- `-c R_J(x, y, z, -c) → 3 R_F(x, y, z)` as `c → ∞` (principal value). -/
private theorem tendsto_neg_mul_symmetricEllipticRJ_neg {x y z : ℂ} (hx : x ∈ slitPlane ∨ x = 0)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    Tendsto (fun c : ℝ => ((-c : ℝ) : ℂ) * symmetricEllipticRJ x y z (-c : ℝ)) atTop
      (𝓝 (3 * symmetricEllipticRF x y z)) := by
  set f : ℝ → ℂ := fun t => (carlsonRootProduct x y z t)⁻¹ with hfdef
  have hf : IntegrableOn f (Ioi 0) := integrableOn_symmetricEllipticRF_integrand hx hy hz
  set I : ℝ → Set ℝ := fun c => Icc (c / 2) (3 * c / 2) with hI
  set H : ℝ → ℝ → ℂ := fun c t => (I c)ᶜ.indicator (fun t => f t * ((c : ℂ) / ((c : ℂ) - t))) t
    with hH
  set M : ℝ → ℝ → ℂ := fun c t =>
    (I c).indicator (fun t => -(c : ℂ) * ((f t - f c) / ((t : ℂ) - c))) t with hM
  have hHmeas : ∀ c, AEStronglyMeasurable (H c) (volume.restrict (Ioi 0)) := by
    intro c
    refine AEStronglyMeasurable.indicator ?_ measurableSet_Icc.compl
    exact hf.aestronglyMeasurable.mul
      (by fun_prop : Measurable fun t : ℝ => (c : ℂ) / ((c : ℂ) - t)).aestronglyMeasurable
  have hHbd : ∀ c, 0 < c → ∀ t, ‖H c t‖ ≤ 2 * ‖f t‖ := by
    intro c hc t
    by_cases ht : t ∈ I c
    · simp only [hH, indicator_of_notMem (notMem_compl_iff.mpr ht), norm_zero]; positivity
    · rw [hH]
      simp only [indicator_of_mem (mem_compl ht), norm_mul]
      rw [show (c : ℂ) / ((c : ℂ) - t) = ((c / (c - t) : ℝ) : ℂ) by push_cast; rfl, norm_real,
        Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (abs_div_sub_le_two hc ht) (norm_nonneg _)
  have hHint : ∀ c, 0 < c → IntegrableOn (H c) (Ioi 0) := fun c hc =>
    Integrable.mono' (hf.norm.const_mul 2) (hHmeas c)
      (Filter.Eventually.of_forall fun t => hHbd c hc t)
  have hpt : ∀ c : ℝ, 0 < c → ∀ t : ℝ, (-(c : ℂ)) *
      ((carlsonRootProduct x y z t * ((t : ℂ) - c))⁻¹ -
      (Icc (c / 2) (3 * c / 2)).indicator
        (fun t : ℝ => (carlsonRootProduct x y z c)⁻¹ / ((t : ℂ) - c)) t) = H c t + M c t := by
    intro c hc t
    by_cases ht : t ∈ I c
    · simp only [hH, hM, indicator_of_notMem (notMem_compl_iff.mpr ht),
        indicator_of_mem ht]
      rw [indicator_of_mem ht, mul_inv]
      simp only [hfdef]
      ring
    · simp only [hH, hM, indicator_of_mem (mem_compl ht), indicator_of_notMem ht, add_zero]
      rw [indicator_of_notMem ht, sub_zero, mul_inv, ← neg_sub (t : ℂ), div_neg]
      simp only [hfdef]
      ring
  have hdec : ∀ c : ℝ, 0 < c → ((-c : ℝ) : ℂ) * symmetricEllipticRJ x y z (-c : ℝ) =
      (3 / 2) * ((∫ t in Ioi 0, H c t) + ∫ t in Ioi 0, M c t) := by
    intro c hc
    have hG := integrableOn_carlsonRootProduct_mul_sub_inv_sub_indicator hx hy hz hc
    have hMint : IntegrableOn (M c) (Ioi 0) := by
      refine IntegrableOn.congr_fun ((hG.const_mul (-(c : ℂ))).sub (hHint c hc))
        (fun t _ => ?_) measurableSet_Ioi
      simp only [Pi.sub_apply]
      rw [hpt c hc t]; ring
    have h23 := two_thirds_symmetricEllipticRJ_neg_eq hx hy hz hc
    rw [← integral_add (hHint c hc) hMint, ← setIntegral_congr_fun measurableSet_Ioi
      (fun t _ => hpt c hc t), MeasureTheory.integral_const_mul, ← h23]
    push_cast
    ring
  have hHlim : Tendsto (fun c => ∫ t in Ioi 0, H c t) atTop (𝓝 (∫ t in Ioi 0, f t)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun t => 2 * ‖f t‖)
      (Filter.Eventually.of_forall hHmeas) ?_ (hf.norm.const_mul 2) ?_
    · filter_upwards [eventually_gt_atTop 0] with c hc
      exact Filter.Eventually.of_forall fun t => hHbd c hc t
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      have hlim : Tendsto (fun c : ℝ => c / (c - t)) atTop (𝓝 1) := by
        have h1 : Tendsto (fun c : ℝ => t / c) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        have h2 : Tendsto (fun c : ℝ => (1 - t / c)⁻¹) atTop (𝓝 ((1 - 0)⁻¹)) :=
          (tendsto_const_nhds.sub h1).inv₀ (by norm_num)
        rw [sub_zero, inv_one] at h2
        refine h2.congr' ?_
        filter_upwards [eventually_gt_atTop (2 * t)] with c hc
        have hc0 : 0 < c := by linarith
        field_simp
      have hlimC := ((continuous_ofReal.tendsto 1).comp hlim).const_mul (f t)
      rw [ofReal_one, mul_one] at hlimC
      refine hlimC.congr' ?_
      filter_upwards [eventually_gt_atTop (2 * t)] with c hc
      have hnot : t ∉ I c := fun h => by simp only [hI, mem_Icc] at h; linarith [h.1]
      simp only [hH, indicator_of_mem (mem_compl hnot), Function.comp_apply]
      push_cast
      rfl
  have hMlim : Tendsto (fun c => ∫ t in Ioi 0, M c t) atTop (𝓝 0) := by
    set R := max (max ‖x‖ ‖y‖) ‖z‖ with hR
    set B : ℝ → ℝ := fun c =>
      c * (3 * ((c / 4) ^ (-(1 / 2) : ℝ)) ^ 2 * ((1 / 2) * (c / 4) ^ (-(3 / 2) : ℝ))) * c
      with hB
    have hbd : ∀ c : ℝ, 4 * R + 1 ≤ c → ‖∫ t in Ioi 0, M c t‖ ≤ B c := by
      intro c hc
      have hR0 : 0 ≤ R := (norm_nonneg x).trans ((le_max_left _ _).trans (le_max_left _ _))
      have hc0 : 0 < c := by linarith
      have hT : 0 < c / 2 := by linarith
      have hxR : ‖x‖ ≤ R := (le_max_left _ _).trans (le_max_left _ _)
      have hyR : ‖y‖ ≤ R := (le_max_right _ _).trans (le_max_left _ _)
      have hzR : ‖z‖ ≤ R := le_max_right _ _
      have hsub : I c ⊆ Ioi 0 := fun t ht => by simp only [hI, mem_Icc] at ht; simp; linarith
      rw [hM, setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr hsub]
      set K := 3 * ((c / 2 / 2) ^ (-(1 / 2) : ℝ)) ^ 2 * ((1 / 2) * (c / 2 / 2) ^ (-(3 / 2) : ℝ))
      have hK0 : 0 ≤ K := by positivity
      have hpt' : ∀ t ∈ I c, ‖-(c : ℂ) * ((f t - f c) / ((t : ℂ) - c))‖ ≤ c * K := by
        intro t ht
        simp only [hI, mem_Icc] at ht
        by_cases htc : t = c
        · subst htc; simp only [sub_self, zero_div, mul_zero, norm_zero]; positivity
        · have hd := norm_carlsonRootProduct_inv_sub_le (x := x) (y := y) (z := z) hT (by linarith)
            (by linarith) (by linarith) ht.1 (by linarith : c / 2 ≤ c)
          have hne : 0 < |t - c| := abs_pos.mpr (sub_ne_zero.mpr htc)
          rw [norm_mul, norm_neg, norm_real, Real.norm_of_nonneg hc0.le, norm_div,
            show (t : ℂ) - c = ((t - c : ℝ) : ℂ) by push_cast; rfl, norm_real, Real.norm_eq_abs]
          refine mul_le_mul_of_nonneg_left ?_ hc0.le
          rw [div_le_iff₀ hne]
          exact hd
      refine (norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top hpt').trans (le_of_eq ?_)
      rw [Real.volume_real_Icc_of_le (by linarith)]
      simp only [hB, K]
      ring_nf
    have hBlim : Tendsto B atTop (𝓝 0) := by
      have h := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 4))).const_mul 24
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with c hc
      simp only [hB, Function.comp_apply, id]
      set u := c / 4 with hu
      have hu0 : 0 < u := by positivity
      have hcu : c = 4 * u := by rw [hu]; ring
      have e1 : (u ^ (-(1 / 2) : ℝ)) ^ 2 = u⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num [Real.rpow_neg_one]
      have e2 : u ^ (-(3 / 2) : ℝ) = u ^ (-(1 / 2) : ℝ) * u⁻¹ := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hu0]; norm_num
      rw [e1, e2, hcu]
      field_simp
      ring
    refine squeeze_zero_norm' ?_ hBlim
    filter_upwards [eventually_ge_atTop (4 * R + 1)] with c hc
    exact hbd c hc
  have hRF : 3 * symmetricEllipticRF x y z = (3 / 2) * ((∫ t in Ioi 0, f t) + 0) := by
    rw [symmetricEllipticRF, add_zero]; ring
  rw [hRF]
  refine ((hHlim.add hMlim).const_mul (3 / 2)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  exact (hdec c hc).symm

/-- DLMF 19.20.12 when `y, z` lie in the slit plane and `x` is in the slit plane or zero. -/
private theorem tendsto_mul_symmetricEllipticRJ_of_mem {x y z : ℂ} (hx : x ∈ slitPlane ∨ x = 0)
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    Tendsto (fun p : ℝ => (p : ℂ) * symmetricEllipticRJ x y z p) atTop
        (𝓝 (3 * symmetricEllipticRF x y z)) ∧
      Tendsto (fun p : ℝ => (p : ℂ) * symmetricEllipticRJ x y z p) atBot
        (𝓝 (3 * symmetricEllipticRF x y z)) := by
  constructor
  · set f : ℝ → ℂ := fun t => (carlsonRootProduct x y z t)⁻¹ with hfdef
    have hf : IntegrableOn f (Ioi 0) := integrableOn_symmetricEllipticRF_integrand hx hy hz
    have hRJ : ∀ p : ℝ, 0 < p → (p : ℂ) * symmetricEllipticRJ x y z p =
        (3 / 2) * ∫ t in Ioi 0, f t * ((p : ℂ) / ((t : ℂ) + p)) := by
      intro p hp
      have hn : ¬ IsNegReal (p : ℂ) := fun h => by have := h.2; simp at this; linarith
      simp only [symmetricEllipticRJ, hn, ↓reduceIte]
      rw [mul_left_comm, ← MeasureTheory.integral_const_mul]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp only [hfdef, mul_inv]
      ring
    have hlim : Tendsto (fun p : ℝ => ∫ t in Ioi 0, f t * ((p : ℂ) / ((t : ℂ) + p))) atTop
        (𝓝 (∫ t in Ioi 0, f t)) := by
      refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun t => ‖f t‖)
        (Filter.Eventually.of_forall fun p => hf.aestronglyMeasurable.mul
          (by fun_prop : Measurable fun t : ℝ => (p : ℂ) / ((t : ℂ) + p)).aestronglyMeasurable)
        ?_ hf.norm ?_
      · filter_upwards [eventually_gt_atTop 0] with p hp
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := ht
        rw [norm_mul, show (p : ℂ) / ((t : ℂ) + p) = ((p / (t + p) : ℝ) : ℂ) by push_cast; rfl,
          norm_real, Real.norm_of_nonneg (by positivity)]
        exact mul_le_of_le_one_right (norm_nonneg _) ((div_le_one (by linarith)).mpr (by linarith))
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := ht
        have h1 : Tendsto (fun p : ℝ => p / (t + p)) atTop (𝓝 1) := by
          have h2 : Tendsto (fun p : ℝ => (1 + t / p)⁻¹) atTop (𝓝 ((1 + 0)⁻¹)) :=
            (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).inv₀
              (by norm_num)
          rw [add_zero, inv_one] at h2
          refine h2.congr' ?_
          filter_upwards [eventually_gt_atTop 0] with p hp
          field_simp
          ring
        have h3 := ((continuous_ofReal.tendsto 1).comp h1).const_mul (f t)
        rw [ofReal_one, mul_one] at h3
        refine h3.congr' (Filter.Eventually.of_forall fun p => ?_)
        simp only [Function.comp_apply]
        push_cast
        rfl
    have hRF : 3 * symmetricEllipticRF x y z = (3 / 2) * ∫ t in Ioi 0, f t := by
      rw [symmetricEllipticRF]; ring
    rw [hRF]
    refine (hlim.const_mul (3 / 2)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with p hp
    exact (hRJ p hp).symm
  · refine ((tendsto_neg_mul_symmetricEllipticRJ_neg hx hy hz).comp
        tendsto_neg_atBot_atTop).congr ?_
    intro p
    simp only [Function.comp_apply, neg_neg]

/-- DLMF 19.20.12: `lim_{p→±∞} p R_J(x, y, z, p) = 3 R_F(x, y, z)` (real `p`; for `p < 0` the
principal value), `x, y, z` in the domain of §19.16(i). -/
@[dlmf 19.20.E12]
theorem tendsto_mul_symmetricEllipticRJ {x y z : ℂ} (h : CarlsonRFDomain x y z) :
    Tendsto (fun p : ℝ => (p : ℂ) * symmetricEllipticRJ x y z p) atTop
        (𝓝 (3 * symmetricEllipticRF x y z)) ∧
      Tendsto (fun p : ℝ => (p : ℂ) * symmetricEllipticRJ x y z p) atBot
          (𝓝 (3 * symmetricEllipticRF x y z)) := by
  obtain ⟨hx, hy, hz, hx0, hy0⟩ := h
  have mem : ∀ {w : ℂ}, IsCarlsonArgument w → w ≠ 0 → w ∈ slitPlane := fun hw hw0 =>
    hw.resolve_right hw0
  by_cases hxz : x = 0
  · obtain ⟨hy', hz'⟩ := hx0 hxz
    exact tendsto_mul_symmetricEllipticRJ_of_mem (Or.inr hxz) (mem hy hy') (mem hz hz')
  have hxs := mem hx hxz
  by_cases hyz : y = 0
  · have H := tendsto_mul_symmetricEllipticRJ_of_mem (Or.inr hyz) hxs (mem hz (hy0 hyz))
    have e1 : ∀ p : ℂ, symmetricEllipticRJ y x z p = symmetricEllipticRJ x y z p := fun p =>
      symmetricEllipticRJ_comm_left _ _ _ _
    simpa only [e1, symmetricEllipticRF_comm_left] using H
  have hys := mem hy hyz
  by_cases hzz : z = 0
  · have H := tendsto_mul_symmetricEllipticRJ_of_mem (x := z) (y := x) (z := y) (Or.inr hzz) hxs hys
    have e1 : ∀ p : ℂ, symmetricEllipticRJ z x y p = symmetricEllipticRJ x y z p := fun p => by
      rw [symmetricEllipticRJ_comm_left, symmetricEllipticRJ_comm_right]
    have e2 : symmetricEllipticRF z x y = symmetricEllipticRF x y z := by
      rw [symmetricEllipticRF_comm_left, symmetricEllipticRF_comm_right]
    simpa only [e1, e2] using H
  exact tendsto_mul_symmetricEllipticRJ_of_mem (Or.inl hxs) hys (mem hz hzz)

/-- DLMF 19.20.13: `2(p - x) R_J(x, y, z, p) = 3 R_F(x, y, z) - 3√x R_C(yz, p²)` for
`p = x ± √((y - x)(z - x))`; real `x ≥ 0`, `y, z > 0` with `(y - x)(z - x) ≥ 0` and `p ≠ 0`
(principal value when `p < 0`; `x, y, z` may be permuted). -/
@[dlmf 19.20.E13]
theorem symmetricEllipticRJ_special_p {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : 0 ≤ (y - x) * (z - x)) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hp : x + s * Real.sqrt ((y - x) * (z - x)) ≠ 0) :
    let p : ℝ := x + s * Real.sqrt ((y - x) * (z - x))
    2 * ((p : ℂ) - x) * symmetricEllipticRJ x y z p =
      3 * symmetricEllipticRF x y z - 3 * (x : ℂ) ^ (1 / 2 : ℂ) *
          symmetricEllipticRC (y * z) ((p : ℂ) ^ 2) := by
  sorry

/-- DLMF 19.20.14 with 19.20.15: the Cauchy principal value of `R_J`. For `0 ≤ x < y < z`,
`q > 0` and `p = (z(x + y + q) - xy)/(z + q)`,
`(q + z) R_J(x, y, z, -q) = (p - z) R_J(x, y, z, p) - 3 R_F(x, y, z)
  + 3 (xyz/(xy + pq))^{1/2} R_C(xy + pq, pq)`. -/
@[dlmf 19.20.E14, dlmf 19.20.E15]
theorem symmetricEllipticRJ_principalValue {x y z q : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hyz : y < z)
    (hq : 0 < q) :
    let p : ℝ := (z * (x + y + q) - x * y) / (z + q)
    ((q + z : ℝ) : ℂ) * symmetricEllipticRJ x y z (-q : ℝ) =
      ((p - z : ℝ) : ℂ) * symmetricEllipticRJ x y z p - 3 * symmetricEllipticRF x y z +
        3 * (Real.sqrt (x * y * z / (x * y + p * q)) : ℂ) *
          symmetricEllipticRC (x * y + p * q : ℝ) (p * q : ℝ) := by
  sorry

/-- DLMF 19.20.16: `p = w y + (1 - w) z` with `w = (z - x)/(z + q) ∈ (0, 1)`, so that
`x < y < p < z` (`p` in a hyperbolic region). -/
@[dlmf 19.20.E16]
theorem symmetricEllipticRJ_principalValue_p {x y z q : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hyz : y < z)
    (hq : 0 < q) :
    (z * (x + y + q) - x * y) / (z + q) =
        (z - x) / (z + q) * y + (1 - (z - x) / (z + q)) * z ∧
      0 < (z - x) / (z + q) ∧ (z - x) / (z + q) < 1 := by
  have hzq : 0 < z + q := by linarith
  refine ⟨by field_simp; ring, div_pos (by linarith) hzq, (div_lt_one hzq).mpr (by linarith)⟩

/-- DLMF 19.20.17: the complete case `x = 0` of (19.20.14): for `0 < y < z`, `q > 0`,
`p = z(y + q)/(z + q)`, `(q + z) R_J(0, y, z, -q) = (p - z) R_J(0, y, z, p) - 3 R_F(0, y, z)`. -/
@[dlmf 19.20.E17]
theorem symmetricEllipticRJ_principalValue_complete {y z q : ℝ} (hy : 0 < y)
    (hyz : y < z) (hq : 0 < q) :
    let p : ℝ := z * (y + q) / (z + q)
    ((q + z : ℝ) : ℂ) * symmetricEllipticRJ 0 y z (-q : ℝ) =
      ((p - z : ℝ) : ℂ) * symmetricEllipticRJ 0 y z p - 3 * symmetricEllipticRF 0 y z := by
  sorry

end DLMF.EllipticIntegrals
