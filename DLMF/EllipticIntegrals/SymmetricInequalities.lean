/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.CapacityBound
public import Carlson.Elliptic.LegendreStandard
public import Carlson.Mean.Capacity
public import Carlson.Mean.StrictOrder
public import DLMF.EllipticIntegrals.Inequalities
public import DLMF.EllipticIntegrals.Symmetric
public import DLMF.EllipticIntegrals.SymmetricQuadratic

/-!
# Inequalities for the symmetric elliptic integrals (DLMF §19.24)

Inequalities for the complete integrals (§19.24(i)) and the incomplete integrals (§19.24(ii)).
All variables are real and positive (or nonnegative where DLMF says so); on such arguments the
symmetric integrals of `DLMF.EllipticIntegrals` are real, and the inequalities are stated for
their real parts (`symEllIntRF_ofReal_im` etc. record that the imaginary parts vanish).

* (19.24.1)–(19.24.4): bounds for `R_F(0, y, z)`, `R_G(0, y, z)`, `R_G(0, y², z²)` and
  `R_J(0, y, z, p)`; the condition `y ≤ z` in (19.24.1)–(19.24.2) only identifies the smaller
  variable (19.24.i.p1). `R_D(0, y, z)` is the case `p = z` of (19.24.4) (19.24.i.p2).
* (19.24.5)–(19.24.6): the AGM bounds `1/aₙ ≤ (2/π) R_F(0, a₀², g₀²) ≤ 1/gₙ`.
* (19.24.7): the perimeter of an ellipse `L(a, b) = 8 R_G(0, a², b²)` (`ellipsePerimeter` of
  §19.9(i)); the approximations of §19.9(i) then apply (19.24.i.p4).
* (19.24.8)–(19.24.9): strict product and sum bounds for `R_F(x, y, 0)`, `R_G(x, y, 0)` and
  Neuman's bounds for `R_G/R_F` through the first AGM step.
* (19.24.10)–(19.24.12): bounds for `R_F`, `R_J`, `R_G` by elementary means (special cases of
  Carlson (1966), Theorems 2 and 3; "all variables are positive", 19.24.ii.p1); the cases
  `R_C`, `R_D` are included (19.24.Px1.p1).
* (19.24.13)–(19.24.15): Neuman's bounds `R_a R_{-a} > 1`, `R_a + R_{-a} > 2`, their special
  case `R_F R_G > 1`, `R_F + R_G > 2`, and `R_C(x, (y+z)/2) ≤ R_F(x, y, z) ≤ R_C(x, √(yz))`.

The lower bound in (19.24.10) is proved from `lean-codes`' capacity bound
`Carlson.inv_dupMean_le_carlsonRF_sq` (Carlson 1966, Theorem 3). The AGM bounds in
(19.24.5) use the RF–AGM identity from §19.22 and Mathlib's `NNReal.agmSequences` bounds.
The upper bound in (19.24.10) uses monotonicity of Carlson's hypergeometric mean;
(19.24.13)–(19.24.14) use strict exponential Jensen inequalities for the real R-averages.
The `R_J` bounds use the five-node capacity inequality and order monotonicity; the `R_G`
bounds are Jensen bounds before and after Euler transformation. The `R_F`–`R_C` bounds in
(19.24.15) compare the real integral kernels using strict arithmetic–geometric mean
inequalities and `lean-codes`' `integral_lt_integral_of_ae_lt`. The complete `R_G` bounds
in (19.24.2) use `Carlson.carlsonRE_eq_compEllIntEk` and the bounds for `E(k)` from §19.9.

## References

* NIST DLMF §19.24.
* B. C. Carlson, *Some inequalities for hypergeometric functions*, Proc. AMS 17 (1966);
  formalized in `lean-codes` (`Carlson.Mean.*`, `Carlson.Elliptic.CapacityBound`).
* E. Neuman, *Bounds for symmetric elliptic integrals*, J. Approx. Theory 122 (2003).
-/

@[expose] public noncomputable section

open Complex Set MeasureTheory
open scoped Real NNReal

namespace DLMF.EllipticIntegrals

/-! ### Reality on nonnegative arguments -/

/-- Identity under the stated parameter and domain assumptions: `((t : ℂ) + (r : ℂ)) ^ (1 / 2 : ℂ)
= ((√(t + r) : ℝ) : ℂ)`. -/
lemma ei19d_ofReal_add_cpow_half {t r : ℝ} (h : 0 ≤ t + r) :
    ((t : ℂ) + (r : ℂ)) ^ (1 / 2 : ℂ) = ((√(t + r) : ℝ) : ℂ) := by
  rw [← ofReal_add, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow h, Real.sqrt_eq_rpow]

/-- Identity under the stated parameter and domain assumptions: `symEllIntS (x : ℂ) (y : ℂ) (z :
ℂ) t = ((√(t + x) * √(t + y) * √(t + z) : ℝ) : ℂ)`. -/
lemma ei19d_symEllIntS_ofReal {x y z t : ℝ} (hx : 0 ≤ t + x) (hy : 0 ≤ t + y)
    (hz : 0 ≤ t + z) :
    symEllIntS (x : ℂ) (y : ℂ) (z : ℂ) t = ((√(t + x) * √(t + y) * √(t + z) : ℝ) : ℂ) := by
  rw [symEllIntS, ei19d_ofReal_add_cpow_half hx, ei19d_ofReal_add_cpow_half hy,
    ei19d_ofReal_add_cpow_half hz]
  push_cast; ring

/-- `R_F(x, y, z)` is real for nonnegative real `x, y, z`. -/
theorem symEllIntRF_ofReal_im {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (symEllIntRF x y z).im = 0 := by
  have h : (∫ t in Ioi (0 : ℝ), (symEllIntS (x : ℂ) (y : ℂ) (z : ℂ) t)⁻¹) =
      ∫ t in Ioi (0 : ℝ), (((√(t + x) * √(t + y) * √(t + z))⁻¹ : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    rw [ei19d_symEllIntS_ofReal (by linarith) (by linarith) (by linarith), ofReal_inv]
  rw [symEllIntRF, h, integral_complex_ofReal]
  simp

/-! ### Strict comparisons for the R-function -/

/-- DLMF 19.24.13 (Neuman): if `a ≠ 0` is real, all components of `𝐛` and `𝐳` are positive and
the components of `𝐳` are not all equal, then `R_a(𝐛; 𝐳) R_{-a}(𝐛; 𝐳) > 1` and
`R_a(𝐛; 𝐳) + R_{-a}(𝐛; 𝐳) > 2`. In `symEllIntR a 𝐛 𝐳 = R_{-a}(𝐛; 𝐳)` notation,
`R_a(𝐛; 𝐳) = symEllIntR (-a) 𝐛 𝐳`. -/
@[dlmf 19.24.E13]
theorem symEllIntR_mul_neg_gt {ι : Type*} [Fintype ι] {a : ℝ} (ha : a ≠ 0) {b z : ι → ℝ}
    (hb : ∀ i, 0 < b i) (hz : ∀ i, 0 < z i) (hne : ∃ i j, z i ≠ z j) :
    1 < (symEllIntR (-a : ℂ) (fun i => (b i : ℂ)) (fun i => (z i : ℂ))).re *
        (symEllIntR (a : ℂ) (fun i => (b i : ℂ)) (fun i => (z i : ℂ))).re ∧
      2 < (symEllIntR (-a : ℂ) (fun i => (b i : ℂ)) (fun i => (z i : ℂ))).re +
        (symEllIntR (a : ℂ) (fun i => (b i : ℂ)) (fun i => (z i : ℂ))).re := by
  have : Nonempty ι := ⟨hne.choose⟩
  have hdom : (fun i => (z i : ℂ)) ∈ Carlson.carlsonRSlitDomain :=
    fun i => ofReal_mem_slitPlane.mpr (hz i)
  have he (t : ℝ) :
      (symEllIntR (t : ℂ) (fun i => (b i : ℂ)) (fun i => (z i : ℂ))).re =
        Carlson.carlsonRReal (-t) b z := by
    rw [symEllIntR_of_mem _ _ hdom, ← ofReal_neg,
      ← Carlson.ofReal_carlsonRReal (-t) hb hz, ofReal_re]
  rw [show (-a : ℂ) = ((-a : ℝ) : ℂ) by simp, he, he, neg_neg]
  have hp := Carlson.carlsonRReal_pos a hb hz
  have hn := Carlson.carlsonRReal_pos (-a) hb hz
  have h₁ := Carlson.mul_carlsonLReal_zero_lt_log_carlsonRReal ha hb hz hne
  have h₂ := Carlson.mul_carlsonLReal_zero_lt_log_carlsonRReal (neg_ne_zero.mpr ha) hb hz hne
  have hm : 1 < Carlson.carlsonRReal a b z * Carlson.carlsonRReal (-a) b z := by
    apply (Real.log_lt_log_iff (by positivity) (mul_pos hp hn)).mp
    rw [Real.log_one, Real.log_mul hp.ne' hn.ne']
    linarith
  exact ⟨hm, by nlinarith [sq_nonneg (Carlson.carlsonRReal a b z -
    Carlson.carlsonRReal (-a) b z)]⟩

/-! ### §19.24(i) Complete integrals -/

/-- DLMF 19.24.1: `ln 4 ≤ √z R_F(0, y, z) + ln √(y/z) ≤ π/2` for `0 < y ≤ z` (the condition
`y ≤ z` only identifies the smaller variable, 19.24.i.p1). -/
@[dlmf 19.24.E1]
theorem symEllIntRF_zero_log_bounds {y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) :
    Real.log 4 ≤ √z * (symEllIntRF 0 y z).re + Real.log √(y / z) ∧
      √z * (symEllIntRF 0 y z).re + Real.log √(y / z) ≤ π / 2 := by
  sorry

/-- DLMF 19.24.2: `1/2 ≤ z^{-1/2} R_G(0, y, z) ≤ π/4` for `0 ≤ y ≤ z`, `z > 0`. -/
@[dlmf 19.24.E2]
theorem symEllIntRG_zero_bounds {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) (hz : 0 < z) :
    1 / 2 ≤ (√z)⁻¹ * (symEllIntRG 0 y z).re ∧ (√z)⁻¹ * (symEllIntRG 0 y z).re ≤ π / 4 := by
  have hsz : 0 < √z := Real.sqrt_pos.mpr hz
  have hpower : (z : ℂ) ^ (1 / 2 : ℂ) = (√z : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow hz.le, ← Real.sqrt_eq_rpow]
  by_cases hy0 : y = 0
  · subst y
    simp only [ofReal_zero]
    rw [(symEllIntRG_zero_self (y := (1 : ℂ)) one_mem_slitPlane
      (ofReal_mem_slitPlane.mpr hz)).2, hpower]
    simp only [mul_re, div_ofNat_re, one_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    have he : (√z)⁻¹ * ((1 / 2) * √z) = 1 / 2 := by field_simp
    rw [he]
    exact ⟨le_rfl, by linarith [Real.two_le_pi]⟩
  have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  by_cases heq : y = z
  · subst z
    rw [(symEllIntRG_zero_self (ofReal_mem_slitPlane.mpr hy')
      (z := (1 : ℂ)) one_mem_slitPlane).1, hpower]
    simp only [mul_re, div_ofNat_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    have he : (√y)⁻¹ * (π / 4 * √y) = π / 4 := by field_simp
    rw [he]
    exact ⟨by linarith [Real.two_le_pi], le_rfl⟩
  have hyz' : y < z := lt_of_le_of_ne hyz heq
  have hb : 0 < 1 - y / z := sub_pos.mpr ((div_lt_one hz).mpr hyz')
  have hb1 : 1 - y / z < 1 := by linarith [div_pos hy' hz]
  have hk0 : 0 < √(1 - y / z) := Real.sqrt_pos.mpr hb
  have hk1 : √(1 - y / z) < 1 := (Real.sqrt_lt' zero_lt_one).mpr (by simpa using hb1)
  have hk2 : √(1 - y / z) ^ 2 < 1 := by nlinarith
  have hRE := Carlson.carlsonRE_eq_compEllIntEk hy' hyz
  rw [← compEllIntEk_ofReal hk2.le] at hRE
  have hRG : symEllIntRG 0 y z = ((√z / 2 : ℝ) : ℂ) * compEllIntEk (√(1 - y / z)) := by
    rw [p19sR1_symEllIntRG_zero_eq_carlsonRE (ofReal_mem_slitPlane.mpr hy')
      (ofReal_mem_slitPlane.mpr hz), hRE]
    push_cast
    field_simp
    ring
  have he : (√z)⁻¹ * (symEllIntRG 0 y z).re = (compEllIntEk (√(1 - y / z))).re / 2 := by
    rw [hRG]
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    field_simp
  rw [he]
  obtain ⟨hL, hU⟩ := one_le_compEllIntEk_le hk0 hk1
  constructor <;> linarith

/-- DLMF 19.24.3: `((y^{3/2} + z^{3/2})/2)^{2/3} ≤ (4/π) R_G(0, y², z²) ≤ ((y² + z²)/2)^{1/2}`
for `y, z > 0`. -/
@[dlmf 19.24.E3]
theorem symEllIntRG_zero_sq_bounds {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    ((y ^ (3 / 2 : ℝ) + z ^ (3 / 2 : ℝ)) / 2) ^ (2 / 3 : ℝ) ≤
        4 / π * (symEllIntRG 0 ((y ^ 2 : ℝ) : ℂ) ((z ^ 2 : ℝ) : ℂ)).re ∧
      4 / π * (symEllIntRG 0 ((y ^ 2 : ℝ) : ℂ) ((z ^ 2 : ℝ) : ℂ)).re ≤ √((y ^ 2 + z ^ 2) / 2) := by
  sorry

/-- DLMF 19.24.4: `(2/√p) (2yz + yp + zp)^{-1/2} ≤ (4/(3π)) R_J(0, y, z, p) ≤ (y z p²)^{-3/8}`
for `y, z, p > 0`; the case `p = z` gives bounds for `R_D(0, y, z)` (19.24.i.p2). -/
@[dlmf 19.24.E4]
theorem symEllIntRJ_zero_bounds {y z p : ℝ} (hy : 0 < y) (hz : 0 < z) (hp : 0 < p) :
    2 / √p * (2 * y * z + y * p + z * p) ^ (-1 / 2 : ℝ) ≤
        4 / (3 * π) * (symEllIntRJ 0 y z p).re ∧
      4 / (3 * π) * (symEllIntRJ 0 y z p).re ≤ (y * z * p ^ 2) ^ (-3 / 8 : ℝ) := by
  sorry

/-- DLMF 19.24.5 with 19.24.6: for `a₀ ≥ g₀ > 0` and the AGM sequences
`a_{n+1} = (aₙ + gₙ)/2`, `g_{n+1} = √(aₙ gₙ)` (19.24.6, §19.8(i)),
`1/aₙ ≤ (2/π) R_F(0, a₀², g₀²) ≤ 1/gₙ` for every `n`. -/
@[dlmf 19.24.E5, dlmf 19.24.E6]
theorem symEllIntRF_zero_agm_bounds {a g : ℕ → ℝ} (hg0 : 0 < g 0) (hag : g 0 ≤ a 0)
    (ha : ∀ n, a (n + 1) = (a n + g n) / 2) (hg : ∀ n, g (n + 1) = √(a n * g n)) (n : ℕ) :
    1 / a n ≤ 2 / π * (symEllIntRF 0 ((a 0 ^ 2 : ℝ) : ℂ) ((g 0 ^ 2 : ℝ) : ℂ)).re ∧
      2 / π * (symEllIntRF 0 ((a 0 ^ 2 : ℝ) : ℂ) ((g 0 ^ 2 : ℝ) : ℂ)).re ≤ 1 / g n := by
  let a₀ : ℝ≥0 := ⟨a 0, (hg0.trans_le hag).le⟩
  let g₀ : ℝ≥0 := ⟨g 0, hg0.le⟩
  have ha₀ : 0 < a₀ := hg0.trans_le hag
  have hg₀ : 0 < g₀ := hg0
  have hseq : ∀ n, a n = agmA a₀ g₀ n ∧ g n = agmG a₀ g₀ n := by
    intro n
    induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n ih =>
      rw [ha, hg, ih.1, ih.2, p19sR1_agmA_succ, p19sR1_agmG_succ]
      exact ⟨rfl, rfl⟩
  have hpos : ∀ n, 0 < a n ∧ 0 < g n := by
    intro n
    induction n with
    | zero => exact ⟨hg0.trans_le hag, hg0⟩
    | succ n ih =>
      rw [ha, hg]
      exact ⟨by linarith [ih.1, ih.2], Real.sqrt_pos.2 (mul_pos ih.1 ih.2)⟩
  have hbounds : g n ≤ (NNReal.agm a₀ g₀ : ℝ) ∧ (NNReal.agm a₀ g₀ : ℝ) ≤ a n := by
    rw [(hseq n).1, (hseq n).2]
    cases n with
    | zero =>
      have hga : g₀ ≤ a₀ := hag
      have hl : g₀ ≤ NNReal.agm a₀ g₀ := by
        simpa [min_eq_right hga] using (NNReal.min_le_agm (x := a₀) (y := g₀))
      have hu : NNReal.agm a₀ g₀ ≤ a₀ := by
        simpa [max_eq_left hga] using (NNReal.agm_le_max (x := a₀) (y := g₀))
      exact ⟨by exact_mod_cast hl, by exact_mod_cast hu⟩
    | succ n =>
      exact ⟨by exact_mod_cast (NNReal.agmSequences_fst_le_agm (x := a₀) (y := g₀) n),
        by exact_mod_cast (NNReal.agm_le_agmSequences_snd (x := a₀) (y := g₀) n)⟩
  have hRF := congrArg Complex.re (symEllIntRF_zero_eq_inv_agm ha₀ hg₀)
  have hRF' : 2 / π * (symEllIntRF 0 ((a 0 ^ 2 : ℝ) : ℂ) ((g 0 ^ 2 : ℝ) : ℂ)).re =
      (NNReal.agm a₀ g₀ : ℝ)⁻¹ := by
    have hcoef : (2 / (π : ℂ)) = ((2 / π : ℝ) : ℂ) := by push_cast; rfl
    rw [hcoef, ← Complex.ofReal_inv] at hRF
    change ((((2 / π : ℝ) : ℂ) * symEllIntRF 0 ((a 0 : ℂ) ^ 2) ((g 0 : ℂ) ^ 2)).re) = _ at hRF
    simpa only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using hRF
  rw [hRF', one_div, one_div]
  exact ⟨inv_anti₀ (by exact_mod_cast NNReal.agm_pos ha₀ hg₀) hbounds.2,
    inv_anti₀ (hpos n).2 hbounds.1⟩

/-- DLMF 19.24.7: the perimeter of an ellipse with semiaxes `a, b`,
`L(a, b) = 8 R_G(0, a², b²)`, with `L` the arc-length integral `ellipsePerimeter` of §19.9(i)
(`DLMF.EllipticIntegrals.ellipsePerimeter`). Valid for all real `a, b` (both sides depend on
`a², b²` only). -/
@[dlmf 19.24.E7]
theorem ellipsePerimeter_eq_symEllIntRG (a b : ℝ) :
    (ellipsePerimeter a b : ℂ) = 8 * symEllIntRG 0 ((a ^ 2 : ℝ) : ℂ) ((b ^ 2 : ℝ) : ℂ) := by
  sorry

/-- DLMF 19.24.8: for `x, y > 0`, `x ≠ y`,
`R_F(x, y, 0) R_G(x, y, 0) > π²/8` and `R_F(x, y, 0) + 2 R_G(x, y, 0) > π`. -/
@[dlmf 19.24.E8]
theorem symEllIntRF_symEllIntRG_complete_bounds {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≠ y) :
    π ^ 2 / 8 < (symEllIntRF x y 0).re * (symEllIntRG x y 0).re ∧
      π < (symEllIntRF x y 0).re + 2 * (symEllIntRG x y 0).re := by
  have h := symEllIntR_mul_neg_gt (a := -1/2) (by norm_num)
    (b := fun _ : Fin 2 => 1/2) (z := ![x,y]) (by intro i; norm_num)
    (by intro i; fin_cases i <;> assumption) ⟨0,1,hxy⟩
  have he : (fun i => ((![x,y] : Fin 2 → ℝ) i : ℂ)) = ![(x:ℂ),y] := by
    ext i; fin_cases i <;> rfl
  simp only [ofReal_neg, ofReal_div, ofReal_one, ofReal_ofNat, neg_div, neg_neg, he] at h
  have hb : (![1/2,1/2] : Fin 2 → ℂ) = (fun _ => 1/2) := by
    ext i; fin_cases i <;> rfl
  have hF : symEllIntRF x y 0 = (π/2) * symEllIntR (1/2) (fun _ : Fin 2 => 1/2) ![x,y] := by
    rw [← symEllIntRF_comm_right, ← symEllIntRF_comm_left]
    simpa only [hb] using symEllIntRF_zero_left (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy)
  have hG : symEllIntRG x y 0 = (π/4) * symEllIntR (-1/2) (fun _ : Fin 2 => 1/2) ![x,y] := by
    rw [← symEllIntRG_comm_right, ← symEllIntRG_comm_left]
    simpa only [hb] using (symEllIntRG_zero_left (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy)).1
  rw [hF, hG]
  simp only [mul_re, div_ofNat_re, ofReal_re, ofReal_im, div_ofNat_im, zero_div,
    zero_mul, sub_zero]
  constructor
  · have := mul_pos Real.pi_pos Real.pi_pos
    nlinarith [mul_lt_mul_of_pos_left h.1 (div_pos this (by norm_num : (0:ℝ)<8))]
  · nlinarith [mul_lt_mul_of_pos_left h.2 Real.pi_pos]

/-- DLMF 19.24.9 (Neuman): with `a₁ = (a₀ + g₀)/2`, `g₁ = √(a₀ g₀)` (19.24.6) and `a₀ ≥ g₀ > 0`,
`g₁²/2 ≤ R_G(a₀², g₀², 0)/R_F(a₀², g₀², 0) ≤ a₁²/2`, with equality (in either inequality) iff
`a₀ = g₀`. -/
@[dlmf 19.24.E9]
theorem symEllIntRG_div_symEllIntRF_agm_bounds {a₀ g₀ : ℝ} (hg : 0 < g₀) (hag : g₀ ≤ a₀) :
    let a₁ := (a₀ + g₀) / 2
    let g₁ := √(a₀ * g₀)
    let r := (symEllIntRG ((a₀ ^ 2 : ℝ) : ℂ) ((g₀ ^ 2 : ℝ) : ℂ) 0).re /
      (symEllIntRF ((a₀ ^ 2 : ℝ) : ℂ) ((g₀ ^ 2 : ℝ) : ℂ) 0).re
    g₁ ^ 2 / 2 ≤ r ∧ r ≤ a₁ ^ 2 / 2 ∧ (g₁ ^ 2 / 2 = r ↔ a₀ = g₀) ∧ (r = a₁ ^ 2 / 2 ↔ a₀ = g₀) := by
  sorry

/-! ### §19.24(ii) Incomplete integrals -/

/-- DLMF 19.24.10 (lower bound): `3/(√x + √y + √z) ≤ R_F(x, y, z)` for positive `x, y, z`.
From `lean-codes`' `Carlson.inv_dupMean_le_carlsonRF_sq` (Carlson 1966, Theorem 3). The AGM bounds in
(19.24.5) use the RF–AGM identity from §19.22 and Mathlib's `NNReal.agmSequences` bounds.
The upper bound in (19.24.10) uses monotonicity of Carlson's hypergeometric mean;
(19.24.13)–(19.24.14) use strict exponential Jensen inequalities for the real R-averages.
The `R_J` bounds use the five-node capacity inequality and order monotonicity; the `R_G`
bounds are Jensen bounds before and after Euler transformation. The `R_F`–`R_C` bounds in
(19.24.15) compare the real integral kernels using strict arithmetic–geometric mean
inequalities and `lean-codes`' `integral_lt_integral_of_ae_lt`. The complete `R_G` bounds
in (19.24.2) use `Carlson.carlsonRE_eq_compEllIntEk` and the bounds for `E(k)` from §19.9. -/
@[dlmf 19.24.E10]
theorem symEllIntRF_ge {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    3 / (√x + √y + √z) ≤ (symEllIntRF x y z).re := by
  have h := Carlson.inv_dupMean_le_carlsonRF_sq (Real.sqrt_pos.mpr hx) (Real.sqrt_pos.mpr hy)
    (Real.sqrt_pos.mpr hz)
  simp only [Real.sq_sqrt hx.le, Real.sq_sqrt hy.le, Real.sq_sqrt hz.le, Carlson.dupMean,
    inv_div] at h
  rw [symEllIntRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr hx) (ofReal_mem_slitPlane.mpr hy)
    (ofReal_mem_slitPlane.mpr hz)]
  exact h

/-- DLMF 19.24.10 (upper bound): `R_F(x, y, z) ≤ (xyz)^{-1/6}` for positive `x, y, z`. -/
@[dlmf 19.24.E10]
theorem symEllIntRF_le {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (symEllIntRF x y z).re ≤ (x * y * z) ^ (-1 / 6 : ℝ) := by
  let b : Fin 3 → ℝ := fun _ => 1 / 2
  let v : Fin 3 → ℝ := ![x, y, z]
  have hb : b ∈ ProbabilityTheory.mvRealBetaDomain := by intro i; norm_num [b]
  have hv : ∀ i, 0 < v i := by intro i; fin_cases i <;> assumption
  have hm := Carlson.monotone_carlsonMeanReal hb hv
    (show -(∑ i, b i) ≤ (-1 / 2 : ℝ) by norm_num [b, Fin.sum_univ_succ])
  dsimp only at hm
  rw [Carlson.carlsonMeanReal_neg_sum hb hv] at hm
  have hbound := Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hm (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  rw [Carlson.carlsonMeanReal_rpow (by norm_num : (-1 / 2 : ℝ) ≠ 0) hb hv] at hbound
  rw [symEllIntRF_eq_carlsonRF (ofReal_mem_slitPlane.mpr hx)
    (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hz), Carlson.carlsonRF]
  have he := Carlson.ofReal_carlsonRReal (-1 / 2) hb hv
  norm_num only [b, v, ofReal_neg, ofReal_div, ofReal_one, ofReal_ofNat] at he
  rw [neg_div]
  rw [← show (fun i => ((![x,y,z] : Fin 3 → ℝ) i : ℂ)) = ![(x:ℂ),y,z] by ext i; fin_cases i <;> rfl,
    ← he, ofReal_re]
  simp only [neg_div] at hbound
  refine hbound.trans_eq ?_
  rw [← Real.exp_mul]
  rw [Real.rpow_def_of_pos (mul_pos (mul_pos hx hy) hz)]
  congr 1
  simp only [b, v, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Real.log_mul hx.ne' hy.ne', Real.log_mul (mul_pos hx hy).ne' hz.ne']
  ring

/-- On positive real nodes, the real part of `R_J(x, y, z, p)` is the real Carlson
R-average with five half-parameters and repeated last node `p`. This makes the general
capacity bound applicable without a separate equal-node aggregation argument. -/
private lemma p19sR2_symEllIntRJ_re_eq_carlsonRReal {x y z p : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hp : 0 < p) :
    (symEllIntRJ x y z p).re = Carlson.carlsonRReal (-3/2)
      (fun _ : Fin 5 => 1/2) ![x,y,z,p,p] := by
  have hv : ∀ i, 0 < (![x,y,z,p,p] : Fin 5 → ℝ) i := by
    intro i; fin_cases i <;> assumption
  have hc := Carlson.capacity_integral_eq_carlsonRReal hv (by norm_num)
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at hc
  rw [neg_div, ← hc]
  have hnp : ¬ IsNegReal (p:ℂ) := ei19c_not_isNegReal_of_mem_slitPlane
    (ofReal_mem_slitPlane.mpr hp)
  rw [symEllIntRJ, ite_eq_right hnp]
  have he : (∫ t in Ioi (0:ℝ), (symEllIntS x y z t * ((t:ℂ)+p))⁻¹) =
      ((∫ t in Ioi (0:ℝ), Carlson.capacityKernel (![x,y,z,p,p] : Fin 5 → ℝ) t : ℝ):ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    change 0 < t at ht
    rw [ei19d_symEllIntS_ofReal (by linarith) (by linarith) (by linarith)]
    simp only [Carlson.capacityKernel, Fin.prod_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one]
    simp only [Fin.prod_univ_zero, mul_one]
    rw [← ofReal_add, ← ofReal_mul, ← ofReal_inv]
    congr 2
    have hpp := Real.sq_sqrt (show 0 ≤ t+p by linarith)
    nth_rw 1 [← hpp]
    ring
  rw [he]
  norm_num [mul_re]

/-- DLMF 19.24.11: `(5/(√x + √y + √z + 2√p))³ ≤ R_J(x, y, z, p) ≤ (x y z p²)^{-3/10}` for
positive `x, y, z, p`. -/
@[dlmf 19.24.E11]
theorem symEllIntRJ_bounds {x y z p : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hp : 0 < p) :
    (5 / (√x + √y + √z + 2 * √p)) ^ 3 ≤ (symEllIntRJ x y z p).re ∧
      (symEllIntRJ x y z p).re ≤ (x * y * z * p ^ 2) ^ (-3 / 10 : ℝ) := by
  let b : Fin 5 → ℝ := fun _ => 1 / 2
  let v : Fin 5 → ℝ := ![x,y,z,p,p]
  have hb : b ∈ ProbabilityTheory.mvRealBetaDomain := by intro i; norm_num [b]
  have hv : ∀ i, 0 < v i := by intro i; fin_cases i <;> assumption
  rw [p19sR2_symEllIntRJ_re_eq_carlsonRReal hx hy hz hp]
  constructor
  · by_cases hn : ∃ i j, v i ≠ v j
    · have h := (Carlson.carlsonRReal_capacity_lower_bound hv (by norm_num) hn).le
      have hs : ∑ i, √(v i) = √x + √y + √z + 2 * √p := by
        norm_num [v, Fin.sum_univ_succ]; ring
      simpa only [Fintype.card_fin, Nat.cast_ofNat, hs, show (1-(5:ℝ)/2) = -3/2 by norm_num] using h
    · push Not at hn
      have hxp : x=p := hn 0 3
      have hyp : y=p := hn 1 3
      have hzp : z=p := hn 2 3
      subst x; subst y; subst z
      have hv' : (![p,p,p,p,p] : Fin 5 → ℝ) = fun _ => p := by ext i; fin_cases i <;> rfl
      rw [hv', Carlson.carlsonRReal_const (-3/2) p hb]
      have he : √p+√p+√p+2*√p = 5*√p := by ring
      rw [he, div_mul_eq_div_div, div_self (by norm_num : (5:ℝ) ≠ 0),
        one_div, inv_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hp.le,
        ← Real.rpow_neg hp.le]
      norm_num
  · have hm := Carlson.monotone_carlsonMeanReal hb hv
      (show -(∑ i, b i) ≤ (-3 / 2 : ℝ) by norm_num [b, Fin.sum_univ_succ])
    dsimp only at hm
    rw [Carlson.carlsonMeanReal_neg_sum hb hv] at hm
    have hbound := Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hm (by norm_num : (-3/2:ℝ) ≤ 0)
    rw [Carlson.carlsonMeanReal_rpow (by norm_num : (-3/2:ℝ) ≠ 0) hb hv] at hbound
    refine hbound.trans_eq ?_
    rw [← Real.exp_mul, Real.rpow_def_of_pos (by positivity : 0 < x*y*z*p^2)]
    congr 1
    simp only [b, v, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Real.log_mul hx.ne' hy.ne', Real.log_mul (mul_pos hx hy).ne' hz.ne',
      Real.log_mul (mul_pos (mul_pos hx hy) hz).ne' (pow_ne_zero 2 hp.ne'), Real.log_pow]
    ring

/-- DLMF 19.24.12: `(√x + √y + √z)/3 ≤ R_G(x, y, z) ≤
min(√((x + y + z)/3), (x² + y² + z²)/(3√(xyz)))` for positive `x, y, z`. -/
@[dlmf 19.24.E12]
theorem symEllIntRG_bounds {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (√x + √y + √z) / 3 ≤ (symEllIntRG x y z).re ∧
      (symEllIntRG x y z).re ≤ min (√((x + y + z) / 3)) ((x ^ 2 + y ^ 2 + z ^ 2) / (3 * √(x * y *
        z))) := by
  let b : Fin 3 → ℝ := fun _ => 1 / 2
  let v : Fin 3 → ℝ := ![x,y,z]
  have hb : b ∈ ProbabilityTheory.mvRealBetaDomain := by intro i; norm_num [b]
  have hv : ∀ i, 0 < v i := by intro i; fin_cases i <;> assumption
  have he : (symEllIntRG x y z).re = Carlson.carlsonRReal (1 / 2) b v := by
    rw [symEllIntRG_eq_symEllIntR (ofReal_mem_slitPlane.mpr hx)
      (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hz),
      symEllIntR_of_mem _ _ (ei19c_slit3 (ofReal_mem_slitPlane.mpr hx)
        (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hz)), neg_div, neg_neg]
    have hc := Carlson.ofReal_carlsonRReal (1 / 2) hb hv
    norm_num only [b, v, ofReal_div, ofReal_one, ofReal_ofNat] at hc
    rw [← show (fun i => ((![x,y,z] : Fin 3 → ℝ) i : ℂ)) = ![(x:ℂ),y,z] by ext i; fin_cases i <;> rfl,
      ← hc, ofReal_re]
  rw [he, le_min_iff]
  have h := Carlson.carlsonRReal_bounds_of_nonneg_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) ≤ 1) hb hv
  have hs : (∑ i, (b i / ∑ j, b j) * v i) = (x+y+z)/3 := by
    norm_num [b, v, Fin.sum_univ_succ]; ring
  have hp : (∑ i, (b i / ∑ j, b j) * v i ^ (1/2:ℝ)) = (√x+√y+√z)/3 := by
    simp only [← Real.sqrt_eq_rpow]
    norm_num [b, v, Fin.sum_univ_succ]; ring
  refine ⟨by simpa only [hp] using h.2, ⟨?_, ?_⟩⟩
  · simpa only [hs, ← Real.sqrt_eq_rpow] using h.1
  · rw [Carlson.carlsonRReal_euler (1/2) hb hv]
    norm_num only [b, Fin.sum_univ_succ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.cast_ofNat]
    have hneg := (Carlson.carlsonRReal_bounds_of_nonpos (by norm_num : (-2:ℝ) ≤ 0)
      hb (fun i => inv_pos.mpr (hv i))).2
    have hfac : (∏ i, v i ^ (-b i)) = (√(x*y*z))⁻¹ := by
      simp only [b, Real.rpow_neg (hv _).le, ← Real.sqrt_eq_rpow, Finset.prod_inv_distrib]
      congr 1
      norm_num [v, Fin.prod_univ_succ]
      rw [Real.sqrt_mul (mul_nonneg hx.le hy.le), Real.sqrt_mul hx.le]
      ring
    have hsum : (∑ i, (b i / ∑ j, b j) * (v i)⁻¹ ^ (-2:ℝ)) = (x^2+y^2+z^2)/3 := by
      simp only [Real.inv_rpow (hv _).le, Real.rpow_neg (hv _).le, inv_inv, Real.rpow_two]
      norm_num [b, v, Fin.sum_univ_succ]; ring
    rw [hfac]
    refine (mul_le_mul_of_nonneg_left hneg (by positivity)).trans_eq ?_
    rw [hsum]
    ring
/-- DLMF 19.24.14: for positive `x, y, z`, not all equal, `R_F(x, y, z) R_G(x, y, z) > 1` and
`R_F(x, y, z) + R_G(x, y, z) > 2` (the case `a = 1/2` of (19.24.13)). -/
@[dlmf 19.24.E14]
theorem symEllIntRF_symEllIntRG_gt {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hne : ¬ (x = y ∧ y = z)) :
    1 < (symEllIntRF x y z).re * (symEllIntRG x y z).re ∧
      2 < (symEllIntRF x y z).re + (symEllIntRG x y z).re := by
  have hn : ∃ i j, (![x, y, z] : Fin 3 → ℝ) i ≠ ![x, y, z] j := by
    by_contra! hn
    exact hne ⟨hn 0 1, hn 1 2⟩
  have hp : ∀ i, 0 < (![x, y, z] : Fin 3 → ℝ) i := by
    intro i; fin_cases i <;> assumption
  have h := symEllIntR_mul_neg_gt (a := -1 / 2) (by norm_num) (b := fun _ : Fin 3 => 1 / 2)
    (by intro i; norm_num) hp hn
  rw [symEllIntRF_eq_symEllIntR (ofReal_mem_slitPlane.mpr hx)
    (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hz),
    symEllIntRG_eq_symEllIntR (ofReal_mem_slitPlane.mpr hx)
      (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hz)]
  have he : (fun i => ((![x, y, z] : Fin 3 → ℝ) i : ℂ)) = ![(x : ℂ), y, z] := by
    ext i; fin_cases i <;> rfl
  simpa only [ofReal_neg, ofReal_div, ofReal_one, ofReal_ofNat, neg_div, neg_neg, he] using h

/-- On nonnegative real arguments, `R_F` is its convergent real square-root integral. -/
private lemma symEllIntRF_re_integral_and_integrable {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z) :
    (symEllIntRF x y z).re =
        (1 / 2) * ∫ t in Ioi (0 : ℝ), (√(t + x) * √(t + y) * √(t + z))⁻¹ ∧
      IntegrableOn (fun t => (√(t + x) * √(t + y) * √(t + z))⁻¹) (Ioi (0 : ℝ)) := by
  have he : (fun t : ℝ => (symEllIntS x y z t)⁻¹) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => (((√(t + x) * √(t + y) * √(t + z))⁻¹ : ℝ) : ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    rw [ei19d_symEllIntS_ofReal (by linarith) (by linarith) (by linarith), ofReal_inv]
  have hxc : SymEllIntArg (x : ℂ) := by
    rcases hx.eq_or_lt with hh | hh
    · exact Or.inr (by exact_mod_cast hh.symm)
    · exact Or.inl (ofReal_mem_slitPlane.mpr hh)
  have hi := (p19sR1_integrableOn_RF hxc (ofReal_mem_slitPlane.mpr hy)
    (ofReal_mem_slitPlane.mpr hz)).congr he
  constructor
  · rw [symEllIntRF, integral_congr_ae he, integral_complex_ofReal]
    simp
  · change Integrable (fun t : ℝ => (√(t + x) * √(t + y) * √(t + z))⁻¹)
      (volume.restrict (Ioi (0 : ℝ)))
    have hir := hi.re
    convert hir using 1

/-- Replacing two distinct positive arguments by their arithmetic or geometric mean
strictly brackets the real `R_F` kernel. -/
private lemma symEllIntRF_RC_kernel_bounds {x y z t : ℝ}
    (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) (hyz : y ≠ z) :
    (√(t + x) * (t + (y + z) / 2))⁻¹ < (√(t + x) * √(t + y) * √(t + z))⁻¹ ∧
      (√(t + x) * √(t + y) * √(t + z))⁻¹ < (√(t + x) * (t + √(y * z)))⁻¹ := by
  have hp : 0 < √(t + x) := Real.sqrt_pos.mpr (by linarith)
  have hq : 0 < √(t + y) * √(t + z) :=
    mul_pos (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_pos.mpr (by linarith))
  have hs : (√(t + y) * √(t + z)) ^ 2 = (t + y) * (t + z) := by
    rw [mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
  have ha : √(t + y) * √(t + z) < t + (y + z) / 2 := by
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hyz)]
  have hne : √y ≠ √z := by
    intro h
    exact hyz ((Real.sqrt_inj hy.le hz.le).mp h)
  have hg : 0 < y + z - 2 * √(y * z) := by
    rw [Real.sqrt_mul hy.le]
    nlinarith [Real.sq_sqrt hy.le, Real.sq_sqrt hz.le,
      sq_pos_of_ne_zero (sub_ne_zero.mpr hne)]
  have hb : t + √(y * z) < √(t + y) * √(t + z) := by
    nlinarith [Real.sq_sqrt (mul_pos hy hz).le, Real.sqrt_nonneg (y * z), mul_pos ht hg]
  constructor
  · rw [mul_assoc]
    exact (inv_lt_inv₀ (by positivity) (by positivity)).mpr (mul_lt_mul_of_pos_left ha hp)
  · rw [mul_assoc]
    exact (inv_lt_inv₀ (by positivity) (by positivity)).mpr (mul_lt_mul_of_pos_left hb hp)

/-- DLMF 19.24.15: `R_C(x, (y + z)/2) ≤ R_F(x, y, z) ≤ R_C(x, √(yz))` for `x ≥ 0` and `y, z > 0`,
with equality (in either inequality) iff `y = z`. -/
@[dlmf 19.24.E15]
theorem symEllIntRF_symEllIntRC_bounds {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z) :
    (symEllIntRC x (((y + z) / 2 : ℝ) : ℂ)).re ≤ (symEllIntRF x y z).re ∧
      (symEllIntRF x y z).re ≤ (symEllIntRC x ((√(y * z) : ℝ) : ℂ)).re ∧
      ((symEllIntRC x (((y + z) / 2 : ℝ) : ℂ)).re = (symEllIntRF x y z).re ↔ y = z) ∧
      ((symEllIntRF x y z).re = (symEllIntRC x ((√(y * z) : ℝ) : ℂ)).re ↔ y = z) := by
  have hA : 0 < (y + z) / 2 := by positivity
  have hG : 0 < √(y * z) := Real.sqrt_pos.mpr (mul_pos hy hz)
  have hrc (q : ℝ) (hq : 0 < q) : symEllIntRC x q = symEllIntRF x q q :=
    symEllIntRC_eq_symEllIntRF _
      (ei19c_not_isNegReal_of_mem_slitPlane (ofReal_mem_slitPlane.mpr hq))
  rw [hrc _ hA, hrc _ hG]
  by_cases hyz : y = z
  · subst z
    rw [show (y + y) / 2 = y by ring,
      show √(y * y) = y by rw [← sq, Real.sqrt_sq hy.le]]
    simp
  · have hi := symEllIntRF_re_integral_and_integrable hx hy hz
    have hia := symEllIntRF_re_integral_and_integrable hx hA hA
    have hig := symEllIntRF_re_integral_and_integrable hx hG hG
    have : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨by
      intro hzero
      have h := Measure.restrict_eq_zero.mp hzero
      simp at h⟩
    have hprod (q t : ℝ) (hq : 0 < q) (ht : 0 < t) :
        (√(t + x) * √(t + q) * √(t + q))⁻¹ = (√(t + x) * (t + q))⁻¹ := by
      rw [mul_assoc, ← sq, Real.sq_sqrt (by linarith)]
    have hL : (∫ t in Ioi (0 : ℝ),
        (√(t + x) * √(t + (y + z) / 2) * √(t + (y + z) / 2))⁻¹) <
        ∫ t in Ioi (0 : ℝ), (√(t + x) * √(t + y) * √(t + z))⁻¹ := by
      apply integral_lt_integral_of_ae_lt hia.2 hi.2
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      rw [hprod _ _ hA ht]
      exact (symEllIntRF_RC_kernel_bounds hx hy hz ht hyz).1
    have hU : (∫ t in Ioi (0 : ℝ), (√(t + x) * √(t + y) * √(t + z))⁻¹) <
        ∫ t in Ioi (0 : ℝ), (√(t + x) * √(t + √(y * z)) * √(t + √(y * z)))⁻¹ := by
      apply integral_lt_integral_of_ae_lt hi.2 hig.2
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      rw [hprod _ _ hG ht]
      exact (symEllIntRF_RC_kernel_bounds hx hy hz ht hyz).2
    have hL' : (symEllIntRF x (((y + z) / 2 : ℝ) : ℂ) (((y + z) / 2 : ℝ) : ℂ)).re <
        (symEllIntRF x y z).re := by
      rw [hia.1, hi.1]
      linarith
    have hU' : (symEllIntRF x y z).re <
        (symEllIntRF x ((√(y * z) : ℝ) : ℂ) ((√(y * z) : ℝ) : ℂ)).re := by
      rw [hi.1, hig.1]
      linarith
    exact ⟨hL'.le, hU'.le, iff_of_false (ne_of_lt hL') hyz,
      iff_of_false (ne_of_lt hU') hyz⟩

end DLMF.EllipticIntegrals
