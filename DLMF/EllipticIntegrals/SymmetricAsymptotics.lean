/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.EllipticIntegrals.Symmetric
public import Carlson.Elliptic.Asymptotic
public import DLMF.EllipticIntegrals.SymmetricAddition
public import DLMF.EllipticIntegrals.SymmetricSpecialCasesRD
public import DLMF.EllipticIntegrals.SymmetricInequalities

/-!
# Asymptotic approximations of the symmetric elliptic integrals (DLMF §19.27)

DLMF §19.27 gives approximations of `R_F`, `R_G`, `R_D`, `R_J` with real nonnegative
arguments when some arguments are much smaller than the others, with relative or absolute
`O`-terms (from Carlson and Gustafson, SIAM J. Math. Anal. 25 (1994), with explicit bounds).

## Main definitions

* `ellAsymA`, `ellAsymB`, `ellAsymC`, `ellAsymF`, `ellAsymG`, `ellAsymH`: the means
  `a, b, c, f, g, h` of DLMF 19.27.1.
* `ellAsymPair`, `ellAsymTriple`: the approach sets for two or three small arguments.

## Main results

* `symmetricEllipticRF_asymp_small_x`: DLMF 19.27.3.
* `symmetricEllipticRF_isEquivalent_atTop`, `symmetricEllipticRF_zero_isEquivalent`: the leading
  term of 19.27.2 as an asymptotic equivalence.
* `symmetricEllipticRG_asymp_large_z`, `symmetricEllipticRG_asymp_small_x`,
  `symmetricEllipticRG_zero_asymp`: DLMF 19.27.4–19.27.6.
* `symmetricEllipticRD_asymp_large_z`, `symmetricEllipticRD_asymp_small_z`,
  `symmetricEllipticRD_asymp_large_x`, `symmetricEllipticRD_asymp_small_x`: DLMF 19.27.7–19.27.10
  (19.27.8 corrected).
* `symmetricEllipticRJ_small_p_bounds`: the corrected DLMF 19.27.12.
* `symmetricEllipticRJ_asymp_small_xy`, `symmetricEllipticRJ_asymp_large_x`: DLMF 19.27.13 and
  19.27.16.

The logarithmic formula 19.27.2 is in
`DLMF.EllipticIntegrals.SymmetricLogarithmicAsymptotics`.
The endpoint formulas 19.27.11, 19.27.14 and 19.27.15 are in
`DLMF.EllipticIntegrals.SymmetricEndpointRegularization`.

## Implementation notes

**Reading of the `O`-terms.** DLMF writes, e.g.,
`R_F(x, y, z) = (1/(2√z)) ln(8z/(a + g)) (1 + O(a/z))` as `a/z → 0`. All formulas are
homogeneous, so the limit is realized here by letting the **small arguments tend to `0`
jointly** (through DLMF's domain: real, nonnegative, at most one of `x, y, z` zero, `p > 0`)
with the **large arguments fixed** and positive; the `O`-term is then a Mathlib
`Asymptotics.IsBigO` along `𝓝[S] 0` (or `𝓝[>] 0`, `𝓝[≥] 0`). Uniformity in the fixed
arguments, which Carlson–Gustafson's explicit bounds also provide, is not asserted. Every
statement was checked numerically (mpmath, random directions of approach).

**Corrections.**
* **19.27.8.** DLMF: `R_D(x, y, z) = 3/√(xyz) - (6/(xy)) R_G(x, y, 0) (1 + O(z/g))`. The
  relative error of the bracket is of order `√(z/g)`, not `z/g`: numerically, for
  `x = 2, y = 3`, `(3/√(xyz) - R_D)/((6/(xy)) R_G(x, y, 0)) - 1 ≈ -1.2895 √(z/g)` for
  `z = 10⁻⁴, …, 10⁻¹⁰`. This agrees with Carlson–Gustafson (1994, (37)):
  `R_D = 3/√(xyz) - (6/(xy)) R_G(x, y, 0) + (6a√z/g³)(1 - (πθ/4)√(z/a))` with bounded `θ`. The
  statement here has `O(√(z/g))`.
* **19.27.12.** DLMF: `R_J(x, y, z, p) = (3/(2√(xyz))) (ln(4f/p) - 2)(1 + O(p/f))`. This fails
  unless `x = y = z`: for `(x, y, z) = (1, 2, 3)` the difference
  `R_J - (3/(2√(xyz)))(ln(4f/p) - 2)` tends to `-0.0381…`, not `0`, as `p → 0`.
  Carlson–Gustafson (1994, (42)) state `R_J = (3/(2√(xyz))) (ln(4f/p) - 2 + r)` with
  `-ln(f/H) < r < (3p/(2(f - p))) ln(f/p)`, where `H = 3/(x⁻¹ + y⁻¹ + z⁻¹)` is the harmonic mean
  (`r → 0` only when `f = H`). That bounded form (with non-strict inequalities, checked
  numerically on 400 random triples and `0 < p < f`) is the statement here.

**Proofs.** Carlson's (9.2-10) and (8.3-16) (`Carlson.isEquivalent_carlsonRF_atTop`,
`Carlson.isEquivalent_carlsonRK_zero`) give the leading term of (19.27.2) as an asymptotic
equivalence along rays (weaker than DLMF's relative `O(a/z)`). The small-first-variable formula
(19.27.3) follows by applying `R_F` duplication in the coordinate `t = √x`. All duplicated
nodes are positive at `t = 0`, so the holomorphic Taylor remainder gives the stated `O(x)`
error. The `R_G` counterpart (19.27.5) uses the same coordinate and the `R_G` duplication
identity; its first derivative at the origin vanishes. The `R_D` formula (19.27.10) uses
duplication and the elementary negative-total-parameter value (19.20.25) to evaluate the
corresponding first derivative.

**Prose of §19.27.** The standing assumptions of 19.27.ii.p1, iii.p1, iv.p1 and v.p1 are
carried as hypotheses. 19.27.vi.p1 and vi.p2 are commentary (bounds of Carlson–Gustafson;
convergent but slowly converging asymptotic series of Wong, Carlson–Gustafson, López; the
`R_{-a}` analogue in Carlson (1985)) with no further explicit formula.

## References

* NIST DLMF §19.27.
* B. C. Carlson and J. L. Gustafson, *Asymptotic approximations for symmetric elliptic
  integrals*, SIAM J. Math. Anal. 25 (1994) 288–303.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Real Topology

namespace DLMF.EllipticIntegrals

/-- The quadratic Taylor remainder of a holomorphic function at the origin. -/
private lemma analyticAt_sub_linear_isBigO {f : ℂ → ℂ} {d : ℂ}
    (ha : AnalyticAt ℂ f 0) (hd : HasDerivAt f d 0) :
    (fun t : ℂ => f t - f 0 - d * t) =O[𝓝 0] fun t : ℂ => ‖t‖ ^ 2 := by
  obtain ⟨p, hp⟩ := ha
  have H := hp.isBigO_sub_partialSum_pow 2
  have h0 : p.coeff 0 = f 0 := hp.coeff_zero _
  have h1 : p.coeff 1 = d := hp.hasDerivAt.unique hd
  simpa [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
    FormalMultilinearSeries.apply_eq_prod_smul_coeff, h0, h1, smul_eq_mul, sub_add_eq_sub_sub,
        mul_comm] using H

/-- The chain rule for a continued R-function along a path with equal node derivatives. -/
private lemma hasDerivAt_carlsonR_comp_common {ι : Type*} [Fintype ι]
    (a : ℂ) (b : ι → ℂ) {q : ℂ → ι → ℂ} {t k : ℂ}
    (hq : HasDerivAt q (fun _ => k) t) (hp : q t ∈ Carlson.carlsonRSlitDomain) :
    HasDerivAt (fun w => Carlson.carlsonR a b (q w))
      (k * a * Carlson.carlsonR (a - 1) b (q t)) t := by
  let F := Carlson.carlsonR a b
  let v : ι → ℂ := fun _ => 1
  have hF : DifferentiableAt ℂ F (q t) :=
    (analyticAt_const.mul (Carlson.analyticOnNhd_regCarlsonR a b (q t) hp)).differentiableAt
  have hv : HasDerivAt (fun w : ℂ => fun i => w + q t i) v 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa [v] using (hasDerivAt_id (0 : ℂ)).add_const (q t i)
  have HV := hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hv (by funext i; simp)
  have HD := (Carlson.hasDerivAt_regCarlsonR_translate a b (q t)
    (x := 0) (by simpa using hp)).const_mul (Gamma (∑ i, b i))
  have HD' : HasDerivAt (fun w => F (fun i => w + q t i))
      (a * Carlson.carlsonR (a - 1) b (q t)) 0 := by
    convert HD using 1
    · rfl
    · unfold Carlson.carlsonR
      simp only [zero_add]
      ring
  have HL : (fderiv ℂ F (q t)) v = a * Carlson.carlsonR (a - 1) b (q t) := HV.unique HD'
  have hq' : HasDerivAt q (k • v) t := by
    convert hq using 1
    funext i
    simp [v, smul_eq_mul]
  have HC := hF.hasFDerivAt.comp_hasDerivAt t hq'
  change HasDerivAt _ ((fderiv ℂ F (q t)) (k • v)) t at HC
  rw [map_smul, HL] at HC
  convert HC using 1 <;> first | rfl | simp [smul_eq_mul, mul_assoc]

/-- When all three node derivatives agree, the first-kind derivative is elementary. -/
private lemma hasDerivAt_carlsonRF_comp_common {f g h : ℂ → ℂ} {t k : ℂ}
    (hf : HasDerivAt f k t) (hg : HasDerivAt g k t) (hh : HasDerivAt h k t)
    (hfs : f t ∈ slitPlane) (hgs : g t ∈ slitPlane) (hhs : h t ∈ slitPlane) :
    HasDerivAt (fun w => Carlson.carlsonRF (f w) (g w) (h w))
      (-k / 2 * ((f t) ^ (-1 / 2 : ℂ) * (g t) ^ (-1 / 2 : ℂ) * (h t) ^ (-1 / 2 : ℂ))) t := by
  have hq : HasDerivAt (fun w => ![f w, g w, h w]) (fun _ : Fin 3 => k) t := by
    apply hasDerivAt_pi.mpr
    intro i; fin_cases i <;> assumption
  have hp := vec3_mem_carlsonRSlitDomain hfs hgs hhs
  have HS := symmetricEllipticR_sum (fun _ : Fin 3 => (1 / 2 : ℂ)) hp (by
    apply Complex.Gamma_ne_zero_of_re_pos
    norm_num [Fin.sum_univ_three])
  rw [symmetricEllipticR_of_mem _ _ hp] at HS
  norm_num [Fin.sum_univ_three] at HS
  have H := hasDerivAt_carlsonR_comp_common (-1 / 2) (fun _ : Fin 3 => 1 / 2) hq hp
  change HasDerivAt (fun w => Carlson.carlsonRF (f w) (g w) (h w)) _ t at H
  refine H.congr_deriv ?_
  rw [show (-1 / 2 : ℂ) - 1 = -(3 / 2) by norm_num, HS]
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp only [neg_div]
  ring

/-- The product of square roots at the duplication boundary factors into two elementary
symmetric expressions. -/
private lemma sqrt_product_duplication_boundary {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    √(√y * √z) * √(y + √y * √z) * √(z + √y * √z) =
      (√y * √z) * (√y + √z) := by
  have hy' : y + √y * √z = √y * (√y + √z) := by nlinarith [Real.sq_sqrt hy]
  have hz' : z + √y * √z = √z * (√y + √z) := by nlinarith [Real.sq_sqrt hz]
  rw [hy', hz', Real.sqrt_mul (Real.sqrt_nonneg y),
    Real.sqrt_mul (Real.sqrt_nonneg y), Real.sqrt_mul (Real.sqrt_nonneg z)]
  calc _ = √(√y) ^ 2 * √(√z) ^ 2 * √(√y + √z) ^ 2 := by ring
       _ = _ := by rw [Real.sq_sqrt (Real.sqrt_nonneg y),
                     Real.sq_sqrt (Real.sqrt_nonneg z), Real.sq_sqrt (by positivity)]

/-- Duplication expresses `R_F` at a nonnegative first argument through positive nodes that
are polynomial in its square root. -/
private lemma symmetricEllipticRF_duplication_sqrt {x y z : ℝ} (hx : 0 ≤ x)
    (hy : 0 < y) (hz : 0 < z) :
    let l := √y * √z + (√y + √z) * √x
    symmetricEllipticRF x y z = 2 * Carlson.carlsonRF (x + l : ℝ) (y + l : ℝ) (z + l : ℝ) := by
  let l := √y * √z + (√y + √z) * √x
  have hl : 0 < l := by dsimp only [l]; positivity
  have hs : duplicationLambda x y z = (l : ℂ) := by
    unfold duplicationLambda
    rw [Carlson.ofReal_cpow_half hx, Carlson.ofReal_cpow_half hy.le, Carlson.ofReal_cpow_half hz.le]
    dsimp only [l]
    push_cast
    ring
  have H : symmetricEllipticRF x y z = 2 *
      symmetricEllipticRF (x + l : ℝ) (y + l : ℝ) (z + l : ℝ) := by
    by_cases hx0 : x = 0
    · subst x
      have H := symmetricEllipticRF_duplication_zero (ofReal_mem_slitPlane.mpr hy)
        (ofReal_mem_slitPlane.mpr hz)
      simp only [ofReal_zero] at hs
      rw [hs] at H
      simpa only [ofReal_zero, zero_add, ← ofReal_add] using H
    · have H := symmetricEllipticRF_duplication
        (ofReal_mem_slitPlane.mpr (lt_of_le_of_ne hx (Ne.symm hx0)))
        (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hz)
      rw [hs] at H
      simpa only [← ofReal_add] using H
  rw [H, symmetricEllipticRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr (by linarith))
    (ofReal_mem_slitPlane.mpr (by linarith)) (ofReal_mem_slitPlane.mpr (by linarith))]

/-! ### Notation (19.27.1) -/

/-- DLMF 19.27.1: `a = (x + y)/2`. -/
@[dlmf 19.27.E1]
def ellAsymA (x y : ℝ) : ℝ := (x + y) / 2

/-- DLMF 19.27.1: `b = (y + z)/2`. -/
@[dlmf 19.27.E1]
def ellAsymB (y z : ℝ) : ℝ := (y + z) / 2

/-- DLMF 19.27.1: `c = (x + y + z)/3`. -/
@[dlmf 19.27.E1]
def ellAsymC (x y z : ℝ) : ℝ := (x + y + z) / 3

/-- DLMF 19.27.1: `f = (xyz)^{1/3}`. -/
@[dlmf 19.27.E1]
def ellAsymF (x y z : ℝ) : ℝ := (x * y * z) ^ (1 / 3 : ℝ)

/-- DLMF 19.27.1: `g = (xy)^{1/2}`. -/
@[dlmf 19.27.E1]
def ellAsymG (x y : ℝ) : ℝ := √(x * y)

/-- DLMF 19.27.1: `h = (yz)^{1/2}`. -/
@[dlmf 19.27.E1]
def ellAsymH (y z : ℝ) : ℝ := √(y * z)

/-- The approach set for two small nonnegative arguments, not both zero. -/
def ellAsymPair : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q ≠ 0}

/-- The approach set for three small nonnegative arguments, at most one of them zero. -/
def ellAsymTriple : Set (ℝ × ℝ × ℝ) :=
  {q | 0 ≤ q.1 ∧ 0 ≤ q.2.1 ∧ 0 ≤ q.2.2 ∧
    (q.1 = 0 → q.2.1 ≠ 0 ∧ q.2.2 ≠ 0) ∧ (q.2.1 = 0 → q.2.2 ≠ 0)}

/-! ### §19.27(ii) `R_F` -/

/-- DLMF 19.27.3: `R_F(x, y, z) = R_F(0, y, z) - (1/√h)(√(x/h) + O(x/h))` as `x/h → 0`: for
fixed `y, z > 0`, as `x → 0+`. -/
@[dlmf 19.27.E3]
theorem symmetricEllipticRF_asymp_small_x {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    (fun x : ℝ => symmetricEllipticRF x y z - symmetricEllipticRF 0 y z +
        ((√(x / ellAsymH y z) / √(ellAsymH y z) : ℝ) : ℂ)) =O[𝓝[≥] 0]
      (fun x : ℝ => ((x / ellAsymH y z / √(ellAsymH y z) : ℝ) : ℂ)) := by
  let r := √y * √z
  let k := √y + √z
  let l : ℂ → ℂ := fun t => (r : ℂ) + (k : ℂ) * t
  let F : ℂ → ℂ := fun t => 2 * Carlson.carlsonRF (t ^ 2 + l t) ((y : ℂ) + l t) ((z : ℂ) + l t)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hk : 0 < k := by dsimp only [k]; positivity
  have hyr : 0 < y + r := by positivity
  have hzr : 0 < z + r := by positivity
  have hnodes : l 0 ∈ slitPlane ∧ (y : ℂ) + l 0 ∈ slitPlane ∧ (z : ℂ) + l 0 ∈ slitPlane := by
    dsimp only [l]
    simp only [mul_zero, add_zero, ← ofReal_add]
    exact ⟨ofReal_mem_slitPlane.mpr hr, ofReal_mem_slitPlane.mpr hyr, ofReal_mem_slitPlane.mpr hzr⟩
  have ha : AnalyticAt ℂ F 0 := by
    apply analyticAt_const.mul
    apply Carlson.analyticAt_carlsonRF_comp
    · exact (analyticAt_id.pow 2).add (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
    · exact analyticAt_const.add (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
    · exact analyticAt_const.add (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
    · simpa using hnodes.1
    · exact hnodes.2.1
    · exact hnodes.2.2
  have hl : HasDerivAt l (k : ℂ) 0 := by
    simpa [l] using ((hasDerivAt_id (0 : ℂ)).const_mul (k : ℂ)).const_add (r : ℂ)
  have hfirst : HasDerivAt (fun t : ℂ => t ^ 2 + l t) (k : ℂ) 0 := by
    have H := ((hasDerivAt_id (0 : ℂ)).pow 2).add hl
    convert H using 1 <;> first | rfl | simp
  have HD := (hasDerivAt_carlsonRF_comp_common hfirst (hl.const_add (y : ℂ))
    (hl.const_add (z : ℂ)) (by simpa using hnodes.1) hnodes.2.1 hnodes.2.2).const_mul (2 : ℂ)
  have hS : √r * √(y + r) * √(z + r) = r * k :=
    sqrt_product_duplication_boundary hy.le hz.le
  have HD' : HasDerivAt F (-((√(y * z))⁻¹ : ℂ)) 0 := by
    refine HD.congr_deriv ?_
    simp only [l, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero, zero_add]
    rw [← ofReal_add, ← ofReal_add, ← inv_cpow_half_eq_cpow_neg_half,
        ← inv_cpow_half_eq_cpow_neg_half,
      ← inv_cpow_half_eq_cpow_neg_half, Carlson.ofReal_cpow_half hr.le,
          Carlson.ofReal_cpow_half hyr.le,
      Carlson.ofReal_cpow_half hzr.le]
    rw [Real.sqrt_mul hy.le]
    change 2 * (-(k : ℂ) / 2 * _) = -((r : ℝ) : ℂ)⁻¹
    have H := congrArg (fun a : ℝ => (a : ℂ)) hS
    push_cast at H
    calc _ = -(k : ℂ) * ((√r : ℂ) * √(y + r) * √(z + r))⁻¹ := by
               simp only [mul_inv_rev]; ring
         _ = -(k : ℂ) * ((r : ℂ) * k)⁻¹ := by rw [H]
         _ = _ := by
           field_simp [ofReal_ne_zero.mpr hk.ne', ofReal_ne_zero.mpr hr.ne']
  have H := analyticAt_sub_linear_isBigO ha HD'
  have hF (x : ℝ) (hx : 0 ≤ x) : F (√x : ℂ) = symmetricEllipticRF x y z := by
    have H := symmetricEllipticRF_duplication_sqrt hx hy hz
    dsimp only [F, l, r, k]
    rw [← ofReal_pow, Real.sq_sqrt hx]
    simpa only [ofReal_add, ofReal_mul] using H.symm
  have hlim : Tendsto (fun x : ℝ => (√x : ℂ)) (𝓝[≥] 0) (𝓝 0) := by
    have H : Tendsto (fun x : ℝ => (√x : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
      simpa only [Function.comp_def, Real.sqrt_zero, ofReal_zero] using
        ((continuous_ofReal.comp Real.continuous_sqrt).tendsto (0 : ℝ))
    exact H.mono_left nhdsWithin_le_nhds
  have HH := H.comp_tendsto hlim
  have he0 : F 0 = symmetricEllipticRF 0 y z := by simpa using hF 0 le_rfl
  have he : (fun x : ℝ => F (√x : ℂ) - F 0 - (-((√(y*z))⁻¹ : ℂ)) * (√x : ℂ))
      =ᶠ[𝓝[≥] 0] fun x : ℝ => symmetricEllipticRF x y z - symmetricEllipticRF 0 y z +
        ((√(x / ellAsymH y z) / √(ellAsymH y z) : ℝ) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [hF x hx, he0]
    have hh : 0 < ellAsymH y z := by dsimp only [ellAsymH]; positivity
    have hcor : √(x / ellAsymH y z) / √(ellAsymH y z) = √x / ellAsymH y z := by
      rw [Real.sqrt_div hx, div_div, ← pow_two, Real.sq_sqrt hh.le]
    rw [hcor]
    simp only [ellAsymH, ofReal_div]
    ring
  refine (HH.congr' he Filter.EventuallyEq.rfl).trans ?_
  apply IsBigO.of_bound (√(ellAsymH y z) * ellAsymH y z)
  filter_upwards [self_mem_nhdsWithin] with x hx
  dsimp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hh : 0 < ellAsymH y z := by dsimp only [ellAsymH]; positivity
  have hhS := Real.sqrt_pos.mpr hh
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hx,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (div_nonneg hx hh.le) hhS.le)]
  apply le_of_eq
  field_simp

/-- Bridge (proved, from `lean-codes` (9.2-10)): for fixed `x, y > 0`,
`R_F(x, y, z) ∼ (1/(2√z)) ln(8z/(a + g))` as `z → ∞`, the leading term of (19.27.2) as an
asymptotic equivalence (weaker than DLMF's relative `O(a/z)`). -/
@[dlmf 19.27.E2]
theorem symmetricEllipticRF_isEquivalent_atTop {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IsEquivalent atTop (fun z : ℝ => symmetricEllipticRF x y z)
      (fun z : ℝ => ((Real.log (8 * z / (ellAsymA x y + ellAsymG x y)) / (2 * √z) : ℝ) : ℂ)) := by
  have H := Carlson.isEquivalent_carlsonRF_atTop hx hy
  have hl : (fun z : ℝ => Carlson.carlsonRF x y z) =ᶠ[atTop] fun z : ℝ =>
      symmetricEllipticRF x y z := by
    filter_upwards [eventually_gt_atTop 0] with z hz
    rw [symmetricEllipticRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy)
      (ofReal_mem_slitPlane.mpr hz)]
  have hr : (fun z : ℝ => ((Real.log (4 * √z / (√x + √y)) / √z : ℝ) : ℂ)) =ᶠ[atTop]
      fun z : ℝ => ((Real.log (8 * z / (ellAsymA x y + ellAsymG x y)) / (2 * √z) : ℝ) : ℂ) := by
    filter_upwards [eventually_gt_atTop 0] with z hz
    have hsx := Real.sqrt_pos.mpr hx
    have hsy := Real.sqrt_pos.mpr hy
    have hsz := Real.sqrt_pos.mpr hz
    have hsum : 0 < √x + √y := by positivity
    have e : 8 * z / (ellAsymA x y + ellAsymG x y) = (4 * √z / (√x + √y)) ^ 2 := by
      simp only [ellAsymA, ellAsymG]
      rw [Real.sqrt_mul hx.le, div_pow, mul_pow, Real.sq_sqrt hz.le]
      have : (√x + √y) ^ 2 = x + y + 2 * (√x * √y) := by
        rw [add_sq, Real.sq_sqrt hx.le, Real.sq_sqrt hy.le]; ring
      rw [this]
      have : 0 < x + y + 2 * (√x * √y) := by positivity
      field_simp
      ring
    rw [e, Real.log_pow]
    congr 1
    field_simp
    push_cast
    ring
  exact (H.congr_left hl).congr_right hr

/-- Bridge (proved, from `lean-codes` (8.3-16)): the case `x = 0` of (19.27.2) as an asymptotic
equivalence: for fixed `z > 0`, `R_F(0, y, z) ∼ (1/(2√z)) ln(16z/y)` as `y → 0+` (here
`a = y/2`, `g = 0`). Weaker than DLMF's relative `O(y/z)`. -/
@[dlmf 19.27.E2]
theorem symmetricEllipticRF_zero_isEquivalent {z : ℝ} (hz : 0 < z) :
    IsEquivalent (𝓝[>] 0) (fun y : ℝ => symmetricEllipticRF 0 y z)
      (fun y : ℝ => ((Real.log (16 * z / y) / (2 * √z) : ℝ) : ℂ)) := by
  have H := (IsEquivalent.refl (u := fun _ : ℝ => ((π / 2 : ℝ) : ℂ)) (l := 𝓝[>] 0)).mul
    (Carlson.isEquivalent_carlsonRK_zero hz)
  have hl : ((fun _ : ℝ => ((π / 2 : ℝ) : ℂ)) * fun y : ℝ => Carlson.TwoVariable.carlsonRK z y)
      =ᶠ[𝓝[>] 0] fun y : ℝ => symmetricEllipticRF 0 y z := by
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    simp only [Pi.mul_apply]
    rw [symmetricEllipticRF_comm_right, symmetricEllipticRF_zero_left (ofReal_mem_slitPlane.mpr hz)
      (ofReal_mem_slitPlane.mpr hy), symmetricEllipticR_of_mem _ _ (vec2_mem_carlsonRSlitDomain
        (ofReal_mem_slitPlane.mpr hz) (ofReal_mem_slitPlane.mpr hy))]
    simp only [Carlson.TwoVariable.carlsonRK, Carlson.TwoVariable.pair]
    push_cast
    congr 2
    ring
  have hr : ((fun _ : ℝ => ((π / 2 : ℝ) : ℂ)) *
      fun y : ℝ => ((Real.log (16 * z / y) / (π * √z) : ℝ) : ℂ))
      =ᶠ[𝓝[>] 0] fun y : ℝ => ((Real.log (16 * z / y) / (2 * √z) : ℝ) : ℂ) := by
    filter_upwards with y
    simp only [Pi.mul_apply]
    have := Real.sqrt_pos.mpr hz
    push_cast
    field_simp
  exact (H.congr_left hl).congr_right hr

/-! ### §19.27(iii) `R_G` -/

/-- DLMF 19.27.4: `R_G(x, y, z) = (√z/2)(1 + O((a/z) ln(z/a)))` as `a/z → 0`: for fixed
`z > 0`, as `(x, y) → 0` through nonnegative pairs not both zero. -/
@[dlmf 19.27.E4]
theorem symmetricEllipticRG_asymp_large_z {z : ℝ} (hz : 0 < z) :
    (fun q : ℝ × ℝ => symmetricEllipticRG q.1 q.2 z - ((√z / 2 : ℝ) : ℂ)) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((√z / 2 * (ellAsymA q.1 q.2 / z *
        Real.log (z / ellAsymA q.1 q.2)) : ℝ) : ℂ)) := by
  sorry

/-- DLMF 19.27.5: `R_G(x, y, z) = R_G(0, y, z) + √x O(√(x/h))` as `x/h → 0`: for fixed
`y, z > 0`, as `x → 0+`. -/
@[dlmf 19.27.E5]
theorem symmetricEllipticRG_asymp_small_x {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    (fun x : ℝ => symmetricEllipticRG x y z - symmetricEllipticRG 0 y z) =O[𝓝[≥] 0]
      (fun x : ℝ => ((√x * √(x / ellAsymH y z) : ℝ) : ℂ)) := by
  let r := √y * √z
  let k := √y + √z
  let l : ℂ → ℂ := fun t => (r : ℂ) + (k : ℂ) * t
  let q : ℂ → Fin 3 → ℂ := fun t => ![t ^ 2 + l t, (y : ℂ) + l t, (z : ℂ) + l t]
  let RF : ℂ → ℂ := fun t => Carlson.carlsonRF (q t 0) (q t 1) (q t 2)
  let RG : ℂ → ℂ := fun t => Carlson.carlsonR (1 / 2) (fun _ : Fin 3 => 1 / 2) (q t)
  let F : ℂ → ℂ := fun t => 2 * RG t - l t * RF t - (t + √y + √z) / 2
  have hr : 0 < r := by dsimp only [r]; positivity
  have hk : 0 < k := by dsimp only [k]; positivity
  have hyr : 0 < y + r := by positivity
  have hzr : 0 < z + r := by positivity
  have hp : q 0 ∈ Carlson.carlsonRSlitDomain := by
    intro i
    fin_cases i
    · simpa [q, l] using ofReal_mem_slitPlane.mpr hr
    · simpa [q, l, ← ofReal_add] using ofReal_mem_slitPlane.mpr hyr
    · simpa [q, l, ← ofReal_add] using ofReal_mem_slitPlane.mpr hzr
  have hl : HasDerivAt l (k : ℂ) 0 := by
    simpa [l] using ((hasDerivAt_id (0 : ℂ)).const_mul (k : ℂ)).const_add (r : ℂ)
  have hfirst : HasDerivAt (fun t : ℂ => t ^ 2 + l t) (k : ℂ) 0 := by
    convert ((hasDerivAt_id (0 : ℂ)).pow 2).add hl using 1 <;> first | rfl | simp
  have hq : HasDerivAt q (fun _ => (k : ℂ)) 0 := by
    apply hasDerivAt_pi.mpr
    intro i; fin_cases i
    · exact hfirst
    · exact hl.const_add (y : ℂ)
    · exact hl.const_add (z : ℂ)
  have haRF : AnalyticAt ℂ RF 0 := by
    apply Carlson.analyticAt_carlsonRF_comp
    · exact (analyticAt_id.pow 2).add (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
    · exact analyticAt_const.add (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
    · exact analyticAt_const.add (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
    · exact hp 0
    · exact hp 1
    · exact hp 2
  have haRG : AnalyticAt ℂ RG 0 := by
    unfold RG Carlson.carlsonR
    apply analyticAt_const.mul
    apply Carlson.analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
    · apply analyticAt_pi_iff.mpr
      intro i; fin_cases i
      · exact (analyticAt_id.pow 2).add (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
      · exact analyticAt_const.add (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
      · exact analyticAt_const.add (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
    · exact hp
  have ha : AnalyticAt ℂ F 0 := by
    apply ((analyticAt_const.mul haRG).sub
      ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).mul haRF)).sub
    exact ((analyticAt_id.add analyticAt_const).add analyticAt_const).div_const
  have HDG := hasDerivAt_carlsonR_comp_common (1 / 2) (fun _ : Fin 3 => 1 / 2) hq hp
  have HDG' : HasDerivAt RG ((k : ℂ) / 2 * RF 0) 0 := by
    convert HDG using 1
    norm_num [RF, Carlson.carlsonRF, q, mul_assoc]
    ring
  have HDF := hasDerivAt_carlsonRF_comp_common hfirst (hl.const_add (y : ℂ))
    (hl.const_add (z : ℂ)) (hp 0) (hp 1) (hp 2)
  have hS : √r * √(y + r) * √(z + r) = r * k :=
    sqrt_product_duplication_boundary hy.le hz.le
  have HDF' : HasDerivAt RF (-(1 / (2 * (r : ℂ)))) 0 := by
    refine HDF.congr_deriv ?_
    simp only [l, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero, zero_add]
    rw [← ofReal_add, ← ofReal_add, ← inv_cpow_half_eq_cpow_neg_half,
        ← inv_cpow_half_eq_cpow_neg_half,
      ← inv_cpow_half_eq_cpow_neg_half, Carlson.ofReal_cpow_half hr.le,
          Carlson.ofReal_cpow_half hyr.le,
      Carlson.ofReal_cpow_half hzr.le]
    have H := congrArg (fun a : ℝ => (a : ℂ)) hS
    push_cast at H
    calc _ = -(k : ℂ) / 2 * ((√r : ℂ) * √(y + r) * √(z + r))⁻¹ := by
               simp only [mul_inv_rev]; ring
         _ = -(k : ℂ) / 2 * ((r : ℂ) * k)⁻¹ := by rw [H]
         _ = _ := by field_simp [ofReal_ne_zero.mpr hk.ne', ofReal_ne_zero.mpr hr.ne']
  have HD : HasDerivAt F 0 0 := by
    have H := ((HDG'.const_mul 2).sub (hl.mul HDF')).sub
      ((((hasDerivAt_id (0 : ℂ)).add_const ((√y : ℝ) : ℂ)).add_const ((√z : ℝ) : ℂ)).div_const 2)
    change HasDerivAt F _ 0 at H
    refine H.congr_deriv ?_
    dsimp only [l]
    simp only [mul_zero, add_zero]
    field_simp [ofReal_ne_zero.mpr hr.ne']
    ring
  have HT := analyticAt_sub_linear_isBigO ha HD
  have hF (x : ℝ) (hx : 0 ≤ x) : F (√x : ℂ) = symmetricEllipticRG x y z := by
    have hdom : CarlsonNonnegDomain x y z := ⟨hx, hy.le, hz.le, fun _ => ⟨hy, hz⟩,
      fun hh => False.elim (hy.ne' hh)⟩
    have hscale : (√x * √y + √y * √z + √z * √x : ℝ) = r + k * √x := by
      dsimp only [r, k]; ring
    have H := symmetricEllipticRG_duplication hdom
    have hf : symmetricEllipticRF x y z = 2 * RF (√x : ℂ) := by
      have H := symmetricEllipticRF_duplication_sqrt hx hy hz
      dsimp only [RF, q, l, r, k]
      rw [← ofReal_pow, Real.sq_sqrt hx]
      simpa only [ofReal_add, ofReal_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using H
    have hg : symmetricEllipticRG (x + (r + k * √x) : ℝ) (y + (r + k * √x) : ℝ)
        (z + (r + k * √x) : ℝ) = RG (√x : ℂ) := by
      rw [symmetricEllipticRG_eq_symmetricEllipticR, symmetricEllipticR_of_mem]
      · simp only [RG, q, l, neg_div, neg_neg]
        congr 1
        funext i; fin_cases i <;> simp [Real.sq_sqrt hx, ← ofReal_pow]
      all_goals first
      | apply vec3_mem_carlsonRSlitDomain <;> exact ofReal_mem_slitPlane.mpr (by positivity)
      | exact ofReal_mem_slitPlane.mpr (by positivity)
    dsimp only at H
    rw [hscale, hg, hf] at H
    dsimp only [F, l]
    push_cast at H ⊢
    linear_combination (-1 / 2 : ℂ) * H
  have hlim : Tendsto (fun x : ℝ => (√x : ℂ)) (𝓝[≥] 0) (𝓝 0) := by
    have H : Tendsto (fun x : ℝ => (√x : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
      simpa only [Function.comp_def, Real.sqrt_zero, ofReal_zero] using
        ((continuous_ofReal.comp Real.continuous_sqrt).tendsto (0 : ℝ))
    exact H.mono_left nhdsWithin_le_nhds
  have HH := HT.comp_tendsto hlim
  have h0 : F 0 = symmetricEllipticRG 0 y z := by simpa using hF 0 le_rfl
  have he : (fun x : ℝ => F (√x : ℂ) - F 0 - 0 * (√x : ℂ)) =ᶠ[𝓝[≥] 0]
      fun x : ℝ => symmetricEllipticRG x y z - symmetricEllipticRG 0 y z := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [hF x hx, h0]; ring
  refine (HH.congr' he Filter.EventuallyEq.rfl).trans ?_
  apply IsBigO.of_bound (√(ellAsymH y z))
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hh : 0 < ellAsymH y z := by dsimp only [ellAsymH]; positivity
  have hhS := Real.sqrt_pos.mpr hh
  dsimp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hx,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [Real.sqrt_div hx]
  apply le_of_eq
  field_simp
  nlinarith [Real.sq_sqrt hx]


/-- DLMF 19.27.6: `R_G(0, y, z) = √z/2 + (y/(8√z))(ln(16z/y) - 1)(1 + O(y/z))` as `y/z → 0`:
for fixed `z > 0`, as `y → 0+`. -/
@[dlmf 19.27.E6]
theorem symmetricEllipticRG_zero_asymp {z : ℝ} (hz : 0 < z) :
    (fun y : ℝ => symmetricEllipticRG 0 y z -
        ((√z / 2 + y / (8 * √z) * (Real.log (16 * z / y) - 1) : ℝ) : ℂ)) =O[𝓝[>] 0]
      (fun y : ℝ => ((y / (8 * √z) * (Real.log (16 * z / y) - 1) * (y / z) : ℝ) : ℂ)) := by
  sorry

/-! ### §19.27(iv) `R_D` -/

/-- DLMF 19.27.7: `R_D(x, y, z) = (3/(2z^{3/2}))(ln(8z/(a + g)) - 2)(1 + O(a/z))` as
`a/z → 0`: for fixed `z > 0`, as `(x, y) → 0` through nonnegative pairs not both zero. -/
@[dlmf 19.27.E7]
theorem symmetricEllipticRD_asymp_large_z {z : ℝ} (hz : 0 < z) :
    (fun q : ℝ × ℝ => symmetricEllipticRD q.1 q.2 z - ((3 / (2 * z ^ (3 / 2 : ℝ)) *
        (Real.log (8 * z / (ellAsymA q.1 q.2 + ellAsymG q.1 q.2)) - 2) : ℝ) : ℂ))
      =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((ellAsymA q.1 q.2 / z * (3 / (2 * z ^ (3 / 2 : ℝ)) *
        (Real.log (8 * z / (ellAsymA q.1 q.2 + ellAsymG q.1 q.2)) - 2)) : ℝ) : ℂ)) := by
  sorry

/-- DLMF 19.27.8, **corrected** (see the module docstring: DLMF prints `O(z/g)`; the correct
order is `O(√(z/g))`): `R_D(x, y, z) = 3/√(xyz) - (6/(xy)) R_G(x, y, 0)(1 + O(√(z/g)))` as
`z/g → 0`: for fixed `x, y > 0`, as `z → 0+`. -/
@[dlmf 19.27.E8]
theorem symmetricEllipticRD_asymp_small_z {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (fun z : ℝ => symmetricEllipticRD x y z -
        (((3 / √(x * y * z) : ℝ) : ℂ) - 6 / (x * y : ℝ) * symmetricEllipticRG x y 0)) =O[𝓝[>] 0]
      (fun z : ℝ => 6 / (x * y : ℝ) * symmetricEllipticRG x y 0 *
          ((√(z / ellAsymG x y) : ℝ) : ℂ)) := by
  let r : ℝ := √x * √y
  let k : ℝ := √x + √y
  let l : ℂ → ℂ := fun t => (r : ℂ) + (k : ℂ) * t
  let q : ℂ → Fin 3 → ℂ := fun t => ![(x : ℂ) + l t, (y : ℂ) + l t, t ^ 2 + l t]
  let G : ℂ → ℂ := fun t => Carlson.carlsonR (-3 / 2) ![1 / 2, 1 / 2, 3 / 2] (q t)
  let F : ℂ → ℂ := fun t => 2 * G t - 3 * ((k : ℂ) + t) /
    ((r : ℂ) * (t ^ 2 + l t))
  have hr : 0 < r := by dsimp [r]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hxr : 0 < x + r := by positivity
  have hyr : 0 < y + r := by positivity
  have hp : q 0 ∈ Carlson.carlsonRSlitDomain := by
    intro i
    fin_cases i
    · simpa [q, l, ← ofReal_add] using ofReal_mem_slitPlane.mpr hxr
    · simpa [q, l, ← ofReal_add] using ofReal_mem_slitPlane.mpr hyr
    · simpa [q, l] using ofReal_mem_slitPlane.mpr hr
  have hl : AnalyticAt ℂ l 0 := analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hq : AnalyticAt ℂ q 0 := by
    apply analyticAt_pi_iff.mpr
    intro i
    fin_cases i
    · exact analyticAt_const.add hl
    · exact analyticAt_const.add hl
    · exact (analyticAt_id.pow 2).add hl
  have hG : AnalyticAt ℂ G 0 := by
    unfold G Carlson.carlsonR
    exact analyticAt_const.mul ((Carlson.analyticOnNhd_regCarlsonR _ _ _ hp).comp hq)
  have ha : AnalyticAt ℂ F 0 := by
    apply (analyticAt_const.mul hG).sub
    apply (analyticAt_const.mul (analyticAt_const.add analyticAt_id)).div
      (analyticAt_const.mul ((analyticAt_id.pow 2).add hl))
    simpa [l] using mul_ne_zero (ofReal_ne_zero.mpr hr.ne') (ofReal_ne_zero.mpr hr.ne')
  have hGval (t : ℝ) (ht : 0 ≤ t) : G t =
      symmetricEllipticRD (x + (r + k * t) : ℝ) (y + (r + k * t) : ℝ)
        (t ^ 2 + (r + k * t) : ℝ) := by
    have hlp : 0 < r + k * t := add_pos_of_pos_of_nonneg hr (mul_nonneg hk.le ht)
    rw [symmetricEllipticRD_eq_symmetricEllipticR
      (ofReal_mem_slitPlane.mpr (by linarith : 0 < x + (r + k * t)))
      (ofReal_mem_slitPlane.mpr (by linarith : 0 < y + (r + k * t)))
      (ofReal_mem_slitPlane.mpr (by nlinarith : 0 < t ^ 2 + (r + k * t))),
      symmetricEllipticR_of_mem _ _ (by
        intro i
        fin_cases i <;> exact ofReal_mem_slitPlane.mpr (by positivity))]
    dsimp only [G, q, l]
    push_cast
    simp only [neg_div]
  have hF (z : ℝ) (hz : 0 < z) : F (√z : ℂ) =
      symmetricEllipticRD x y z - ((3 / √(x * y * z) : ℝ) : ℂ) := by
    have hd := symmetricEllipticRD_duplication_of_nonneg hx.le hy hz
    have hlv : √x * √y + √y * √z + √z * √x = r + k * √z := by dsimp [r, k]; ring
    rw [hlv] at hd
    dsimp only at hd
    dsimp only [F, l]
    rw [hGval _ (Real.sqrt_nonneg z)]
    simp only [← ofReal_pow, Real.sq_sqrt hz.le]
    have hsr : √(x * y * z) = r * √z := by
      rw [Real.sqrt_mul (mul_pos hx hy).le, Real.sqrt_mul hx.le]
    rw [hsr]
    have hrat : -(3 * (k + √z) / (r * (z + (r + k * √z)))) =
        3 / (√z * (z + (r + k * √z))) - 3 / (r * √z) := by
      field_simp [hr.ne', (Real.sqrt_pos.mpr hz).ne',
        show z + (r + k * √z) ≠ 0 by positivity]
      nlinarith [Real.sq_sqrt hz.le]
    have hc := congrArg (fun v : ℝ => (v : ℂ)) hrat
    push_cast at hd hc ⊢
    linear_combination hc - hd
  have hF0 : F 0 = -6 / (x * y : ℝ) * symmetricEllipticRG x y 0 := by
    have hdup : 2 * symmetricEllipticRG 0 x y =
        4 * symmetricEllipticRG r (x + r : ℝ) (y + r : ℝ) -
          (r : ℂ) * symmetricEllipticRF 0 x y - k := by
      have H := symmetricEllipticRG_duplication_of_nonneg (x := 0) le_rfl hx hy
      simp only [Real.sqrt_zero, zero_mul, mul_zero, zero_add, add_zero, ofReal_zero] at H
      dsimp only [r, k]
      push_cast at H ⊢
      linear_combination H
    have hrf : symmetricEllipticRF 0 x y =
        2 * symmetricEllipticRF r (x + r : ℝ) (y + r : ℝ) := by
      have H := symmetricEllipticRF_duplication_sqrt (x := 0) le_rfl hx hy
      simp only [Real.sqrt_zero, mul_zero, zero_add, add_zero, ofReal_zero] at H
      rw [symmetricEllipticRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr hr)
        (ofReal_mem_slitPlane.mpr hxr) (ofReal_mem_slitPlane.mpr hyr)]
      exact H
    have htwo := two_mul_symmetricEllipticRG
      (Or.inl (ofReal_mem_slitPlane.mpr hxr)) (ofReal_mem_slitPlane.mpr hyr)
      (ofReal_mem_slitPlane.mpr hr)
    rw [Carlson.ofReal_cpow_half hxr.le, Carlson.ofReal_cpow_half hyr.le,
      show (-1 / 2 : ℂ) = -(1 / 2) by ring, cpow_neg, Carlson.ofReal_cpow_half hr.le] at htwo
    have hs : √(x + r) * √(y + r) / √r = k := by
      have H := sqrt_product_duplication_boundary hx.le hy.le
      change √r * √(x + r) * √(y + r) = r * k at H
      apply (div_eq_iff (Real.sqrt_pos.mpr hr).ne').mpr
      apply mul_left_cancel₀ (Real.sqrt_pos.mpr hr).ne'
      rw [← mul_assoc, H]
      linear_combination -(k : ℝ) * Real.sq_sqrt hr.le
    have hsC := congrArg (fun v : ℝ => (v : ℂ)) hs
    push_cast at hsC
    rw [show (√(x + r) : ℂ) * √(y + r) * (√r : ℂ)⁻¹ = (k : ℂ) by
      exact hsC] at htwo
    rw [symmetricEllipticRG_comm_right, symmetricEllipticRG_comm_left,
      symmetricEllipticRF_comm_right, symmetricEllipticRF_comm_left] at htwo
    have hr2 : r ^ 2 = x * y := by
      dsimp [r]
      rw [mul_pow, Real.sq_sqrt hx.le, Real.sq_sqrt hy.le]
    have hg0 : G 0 = symmetricEllipticRD (x + r : ℝ) (y + r : ℝ) r := by
      simpa only [ofReal_zero, mul_zero, zero_pow two_ne_zero, zero_add, add_zero] using
        hGval 0 le_rfl
    dsimp only [F, l]
    rw [hg0]
    simp only [zero_pow two_ne_zero, mul_zero, zero_add, add_zero]
    rw [symmetricEllipticRG_comm_right, symmetricEllipticRG_comm_left, ← hr2]
    push_cast at hdup hrf htwo ⊢
    have hr2C : (r : ℂ) ^ 2 = (x : ℂ) * y := by exact_mod_cast hr2
    field_simp [ofReal_ne_zero.mpr hr.ne']
    linear_combination 3 * hdup - 3 * (r : ℂ) * hrf + 6 * htwo +
      2 * symmetricEllipticRD ((x : ℂ) + r) ((y : ℂ) + r) r * hr2C
  have hlim : Tendsto (fun z : ℝ => (√z : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, ofReal_zero] using
      ((continuous_ofReal.comp Real.continuous_sqrt).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have H := ha.differentiableAt.isBigO_sub.comp_tendsto hlim
  have he : (fun z : ℝ => F (√z : ℂ) - F 0) =ᶠ[𝓝[>] 0]
      fun z : ℝ => symmetricEllipticRD x y z -
        (((3 / √(x * y * z) : ℝ) : ℂ) - 6 / (x * y : ℝ) * symmetricEllipticRG x y 0) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [hF z hz, hF0]
    ring
  refine (H.congr' he Filter.EventuallyEq.rfl).trans ?_
  have hg : symmetricEllipticRG x y 0 ≠ 0 := by
    have hpos : 0 < (symmetricEllipticRG 0 x y).re := by
      rcases le_total x y with hxy | hxy
      · have H := (symmetricEllipticRG_zero_bounds hx.le hxy hy).1
        have hs := Real.sqrt_pos.mpr hy
        nlinarith [inv_pos.mpr hs]
      · have H := (symmetricEllipticRG_zero_bounds hy.le hxy hx).1
        rw [symmetricEllipticRG_comm_right] at H
        have hs := Real.sqrt_pos.mpr hx
        nlinarith [inv_pos.mpr hs]
    intro H
    rw [symmetricEllipticRG_comm_right, symmetricEllipticRG_comm_left] at H
    rw [H, zero_re] at hpos
    exact lt_irrefl _ hpos
  have hc : (6 : ℂ) / (x * y : ℝ) * symmetricEllipticRG x y 0 ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (ofReal_ne_zero.mpr (mul_pos hx hy).ne')) hg
  have hG : 0 < ellAsymG x y := by dsimp [ellAsymG]; positivity
  apply IsBigO.of_bound ((√(ellAsymG x y)) * ‖(6 : ℂ) / (x * y : ℝ) * symmetricEllipticRG x y 0‖⁻¹)
  filter_upwards [self_mem_nhdsWithin] with z hz
  simp only [Function.comp_def, sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [Real.sqrt_div hz.le]
  have hnorm := norm_pos_iff.mpr hc
  have hs := Real.sqrt_pos.mpr hG
  apply le_of_eq
  field_simp

/-- DLMF 19.27.9: `R_D(x, y, z) = 3/(√(xz)(√y + √z)) (1 + O((b/x) ln(x/b)))` as `b/x → 0`: for
fixed `x > 0`, as `(y, z) → 0` with `y ≥ 0`, `z > 0`. -/
@[dlmf 19.27.E9]
theorem symmetricEllipticRD_asymp_large_x {x : ℝ} (hx : 0 < x) :
    (fun q : ℝ × ℝ => symmetricEllipticRD x q.1 q.2 -
        ((3 / (√(x * q.2) * (√q.1 + √q.2)) : ℝ) : ℂ)) =O[𝓝[{q | 0 ≤ q.1 ∧ 0 < q.2}] 0]
      (fun q : ℝ × ℝ => ((3 / (√(x * q.2) * (√q.1 + √q.2)) *
        (ellAsymB q.1 q.2 / x * Real.log (x / ellAsymB q.1 q.2)) : ℝ) : ℂ)) := by
  sorry

/-- DLMF 19.27.10: `R_D(x, y, z) = R_D(0, y, z) - (3√x/(hz))(1 + O(√(x/h)))` as `x/h → 0`: for
fixed `y, z > 0`, as `x → 0+`. -/
@[dlmf 19.27.E10]
theorem symmetricEllipticRD_asymp_small_x {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    (fun x : ℝ => symmetricEllipticRD x y z - symmetricEllipticRD 0 y z +
        ((3 * √x / (ellAsymH y z * z) : ℝ) : ℂ)) =O[𝓝[≥] 0]
      (fun x : ℝ => ((3 * √x / (ellAsymH y z * z) * √(x / ellAsymH y z) : ℝ) : ℂ)) := by
  let r := √y * √z
  let k := √y + √z
  let l : ℂ → ℂ := fun t => (r : ℂ) + (k : ℂ) * t
  let b : Fin 3 → ℂ := ![1 / 2, 1 / 2, 3 / 2]
  let q : ℂ → Fin 3 → ℂ := fun t => ![t ^ 2 + l t, (y : ℂ) + l t, (z : ℂ) + l t]
  let G : ℂ → ℂ := fun t => Carlson.carlsonR (-3 / 2) b (q t)
  let F : ℂ → ℂ := fun t => 2 * G t + (3 / (√z : ℂ)) * ((z : ℂ) + l t)⁻¹
  have hr : 0 < r := by dsimp only [r]; positivity
  have hk : 0 < k := by dsimp only [k]; positivity
  have hyr : 0 < y + r := by positivity
  have hzr : 0 < z + r := by positivity
  have hp : q 0 ∈ Carlson.carlsonRSlitDomain := by
    intro i
    fin_cases i
    · simpa [q, l] using ofReal_mem_slitPlane.mpr hr
    · simpa [q, l, ← ofReal_add] using ofReal_mem_slitPlane.mpr hyr
    · simpa [q, l, ← ofReal_add] using ofReal_mem_slitPlane.mpr hzr
  have hl : HasDerivAt l (k : ℂ) 0 := by
    simpa [l] using ((hasDerivAt_id (0 : ℂ)).const_mul (k : ℂ)).const_add (r : ℂ)
  have hfirst : HasDerivAt (fun t : ℂ => t ^ 2 + l t) (k : ℂ) 0 := by
    convert ((hasDerivAt_id (0 : ℂ)).pow 2).add hl using 1 <;> first | rfl | simp
  have hq : HasDerivAt q (fun _ => (k : ℂ)) 0 := by
    apply hasDerivAt_pi.mpr
    intro i; fin_cases i
    · exact hfirst
    · exact hl.const_add (y : ℂ)
    · exact hl.const_add (z : ℂ)
  have haG : AnalyticAt ℂ G 0 := by
    unfold G Carlson.carlsonR
    apply analyticAt_const.mul
    apply Carlson.analyticAt_regCarlsonR_comp analyticAt_const analyticAt_const
    · apply analyticAt_pi_iff.mpr
      intro i; fin_cases i
      · exact (analyticAt_id.pow 2).add (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
      · exact analyticAt_const.add (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
      · exact analyticAt_const.add (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
    · exact hp
  have hzne : (z : ℂ) + l 0 ≠ 0 := by
    simp only [l, mul_zero, add_zero, ← ofReal_add]
    exact ofReal_ne_zero.mpr hzr.ne'
  have ha : AnalyticAt ℂ F 0 := by
    apply (analyticAt_const.mul haG).add
    apply analyticAt_const.mul
    exact (analyticAt_const.add
        (analyticAt_const.add (analyticAt_const.mul analyticAt_id))).inv hzne
  have hS : √r * √(y + r) * √(z + r) = r * k :=
    sqrt_product_duplication_boundary hy.le hz.le
  have hb : ∑ i, b i = 5 / 2 := by norm_num [b, Fin.sum_univ_three]
  have HB := symmetricEllipticR_sum b hp (by
    apply Complex.Gamma_ne_zero_of_re_pos
    rw [hb]
    norm_num)
  rw [symmetricEllipticR_of_mem _ _ hp, hb] at HB
  have HG := hasDerivAt_carlsonR_comp_common (-3 / 2) b hq hp
  have HG' : HasDerivAt G (-(3 / (2 * (r : ℂ) * ((z : ℂ) + r)))) 0 := by
    refine HG.congr_deriv ?_
    rw [show (-3 / 2 : ℂ) - 1 = -(5 / 2) by norm_num, HB]
    simp only [b, q, l, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero, zero_add,
      Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [← ofReal_add, ← ofReal_add,
      show (-(3 / 2) : ℂ) = (-1 / 2) + (-1) by norm_num,
      cpow_add _ _ (ofReal_ne_zero.mpr hzr.ne'), cpow_neg_one]
    simp only [cpow_neg]
    rw [← inv_cpow_half_eq_cpow_neg_half]
    rw [Carlson.ofReal_cpow_half hr.le, Carlson.ofReal_cpow_half hyr.le,
      Carlson.ofReal_cpow_half hzr.le]
    push_cast
    have HS := congrArg (fun a : ℝ => (a : ℂ)) hS
    push_cast at HS
    calc _ = -(3 / 2 : ℂ) * k * ((√r : ℂ) * √(y + r) * √(z + r))⁻¹ * ((z : ℂ) + r)⁻¹ := by
               simp only [mul_inv_rev]; ring
         _ = _ := by rw [HS]; field_simp [ofReal_ne_zero.mpr hr.ne', ofReal_ne_zero.mpr hk.ne']
  have HD : HasDerivAt F (-(3 / ((r : ℂ) * z))) 0 := by
    have H := (HG'.const_mul 2).add (((hl.const_add (z : ℂ)).inv hzne).const_mul (3 / (√z : ℂ)))
    change HasDerivAt F _ 0 at H
    refine H.congr_deriv ?_
    simp only [l, mul_zero, add_zero]
    have hK : (k : ℂ) * (√z : ℂ) = (z : ℂ) + r := by
      have HE : k * √z = z + r := by dsimp only [k, r]; nlinarith [Real.sq_sqrt hz.le]
      exact_mod_cast HE
    have hsz : (√z : ℂ) ^ 2 = z := by exact_mod_cast Real.sq_sqrt hz.le
    have hZC : (z : ℂ) + r ≠ 0 := by exact_mod_cast hzr.ne'
    field_simp [ofReal_ne_zero.mpr hr.ne', ofReal_ne_zero.mpr hz.ne',
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hz).ne', hZC]
    linear_combination (-(r : ℂ) * (√z : ℂ)) * hK + ((r : ℂ) * k) * hsz
  have HT := analyticAt_sub_linear_isBigO ha HD
  have hF (x : ℝ) (hx : 0 ≤ x) : F (√x : ℂ) = symmetricEllipticRD x y z := by
    have hscale : (√x * √y + √y * √z + √z * √x : ℝ) = r + k * √x := by
      dsimp only [r, k]; ring
    have H := symmetricEllipticRD_duplication_of_nonneg hx hy hz
    dsimp only at H
    rw [hscale] at H
    have hg : symmetricEllipticRD (x + (r + k * √x) : ℝ) (y + (r + k * √x) : ℝ)
        (z + (r + k * √x) : ℝ) = G (√x : ℂ) := by
      rw [symmetricEllipticRD_eq_symmetricEllipticR, symmetricEllipticR_of_mem]
      · simp only [G, b, q, l, neg_div]
        congr 1
        funext i; fin_cases i <;> simp [Real.sq_sqrt hx, ← ofReal_pow]
      all_goals first
      | apply vec3_mem_carlsonRSlitDomain <;> exact ofReal_mem_slitPlane.mpr (by positivity)
      | exact ofReal_mem_slitPlane.mpr (by positivity)
    rw [hg] at H
    dsimp only [F, l]
    push_cast at H ⊢
    rw [H]
    field_simp
  have hlim : Tendsto (fun x : ℝ => (√x : ℂ)) (𝓝[≥] 0) (𝓝 0) := by
    have H : Tendsto (fun x : ℝ => (√x : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
      simpa only [Function.comp_def, Real.sqrt_zero, ofReal_zero] using
        ((continuous_ofReal.comp Real.continuous_sqrt).tendsto (0 : ℝ))
    exact H.mono_left nhdsWithin_le_nhds
  have HH := HT.comp_tendsto hlim
  have h0 : F 0 = symmetricEllipticRD 0 y z := by simpa using hF 0 le_rfl
  have he : (fun x : ℝ => F (√x : ℂ) - F 0 - (-(3 / ((r : ℂ) * z))) * (√x : ℂ)) =ᶠ[𝓝[≥] 0]
      fun x : ℝ => symmetricEllipticRD x y z - symmetricEllipticRD 0 y z +
          ((3 * √x / (ellAsymH y z * z) : ℝ) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [hF x hx, h0]
    simp only [ellAsymH, Real.sqrt_mul hy.le, ofReal_div, ofReal_mul, ofReal_ofNat]
    dsimp only [r]
    push_cast
    ring
  refine (HH.congr' he Filter.EventuallyEq.rfl).trans ?_
  have hh : 0 < ellAsymH y z := by dsimp only [ellAsymH]; positivity
  have hC : 0 < 3 / (ellAsymH y z * z * √(ellAsymH y z)) := by positivity
  have HId : (fun x : ℝ => ‖(√x : ℂ)‖ ^ 2) =O[𝓝[≥] 0]
      fun x : ℝ => ((3 * √x / (ellAsymH y z * z) * √(x / ellAsymH y z) : ℝ) : ℂ) := by
    apply IsBigO.of_bound ((3 / (ellAsymH y z * z * √(ellAsymH y z)))⁻¹)
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hx,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [Real.sqrt_div hx]
    apply le_of_eq
    field_simp
    nlinarith [Real.sq_sqrt hx]
  exact HId


/-! ### §19.27(v) `R_J` -/

/-- DLMF 19.27.12, **corrected** to Carlson–Gustafson (1994, (42)) (see the module docstring;
DLMF's relative error `O(p/f)` is false unless `x = y = z`): for `x, y, z > 0` and `0 < p < f`,
`R_J(x, y, z, p) = (3/(2√(xyz)))(ln(4f/p) - 2 + r)` with
`-ln(f/H) ≤ r ≤ (3p/(2(f - p))) ln(f/p)`, `H = 3/(x⁻¹ + y⁻¹ + z⁻¹)`. In particular
`R_J = (3/(2√(xyz)))(ln(4f/p) - 2 + O(1))` as `p/f → 0`. The bounds on `r` were checked
numerically (no violation at 500 random triples, mpmath, 2026-10-25), not against the paper. -/
@[dlmf 19.27.E12]
theorem symmetricEllipticRJ_small_p_bounds {x y z p : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hp : 0 < p) (hpf : p < ellAsymF x y z) :
    ∃ r : ℝ, symmetricEllipticRJ x y z p =
        ((3 / (2 * √(x * y * z)) * (Real.log (4 * ellAsymF x y z / p) - 2 + r) : ℝ) : ℂ) ∧
      -Real.log (ellAsymF x y z / (3 / (x⁻¹ + y⁻¹ + z⁻¹))) ≤ r ∧
      r ≤ 3 * p / (2 * (ellAsymF x y z - p)) * Real.log (ellAsymF x y z / p) := by
  sorry

/-- DLMF 19.27.13: `R_J(x, y, z, p) = (3/(2√z p))(ln(8z/(a + g)) - 2 R_C(1, p/z)
+ O((a/z + a/p) ln(p/a)))` as `max(x, y)/min(z, p) → 0`: for fixed `z, p > 0`, as
`(x, y) → 0` through nonnegative pairs not both zero. -/
@[dlmf 19.27.E13]
theorem symmetricEllipticRJ_asymp_small_xy {z p : ℝ} (hz : 0 < z) (hp : 0 < p) :
    (fun q : ℝ × ℝ => symmetricEllipticRJ q.1 q.2 z p -
        ((3 / (2 * √z * p) : ℝ) : ℂ) *
          (((Real.log (8 * z / (ellAsymA q.1 q.2 + ellAsymG q.1 q.2)) : ℝ) : ℂ) -
            2 * symmetricEllipticRC 1 (p / z : ℝ))) =O[𝓝[ellAsymPair] 0]
      (fun q : ℝ × ℝ => ((3 / (2 * √z * p) * ((ellAsymA q.1 q.2 / z + ellAsymA q.1 q.2 / p) *
        Real.log (p / ellAsymA q.1 q.2)) : ℝ) : ℂ)) := by
  sorry

/-- DLMF 19.27.16: `R_J(x, y, z, p) = (3/√x) R_C((h + p)², 2(b + h)p)
+ O(x^{-3/2} ln(x/(b + h)))` as `max(y, z, p)/x → 0`: for fixed `x > 0`, as `(y, z, p) → 0` with
`y, z ≥ 0` not both zero and `p > 0`. -/
@[dlmf 19.27.E16]
theorem symmetricEllipticRJ_asymp_large_x {x : ℝ} (hx : 0 < x) :
    (fun q : ℝ × ℝ × ℝ => symmetricEllipticRJ x q.1 q.2.1 q.2.2 -
        3 / (√x : ℝ) * symmetricEllipticRC ((ellAsymH q.1 q.2.1 + q.2.2) ^ 2 : ℝ)
          (2 * (ellAsymB q.1 q.2.1 + ellAsymH q.1 q.2.1) * q.2.2 : ℝ))
      =O[𝓝[{q | 0 ≤ q.1 ∧ 0 ≤ q.2.1 ∧ (q.1, q.2.1) ≠ 0 ∧ 0 < q.2.2}] 0]
      (fun q : ℝ × ℝ × ℝ => ((x ^ (-(3 / 2) : ℝ) *
        Real.log (x / (ellAsymB q.1 q.2.1 + ellAsymH q.1 q.2.1)) : ℝ) : ℂ)) := by
  sorry

end DLMF.EllipticIntegrals
