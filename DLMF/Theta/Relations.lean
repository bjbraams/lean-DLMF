/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.AnalyticProperties
public import DLMF.EllipticIntegrals.Symmetric
public import DLMF.EllipticIntegrals.SymmetricRelations

/-!
# Theta functions: relations to other functions (DLMF §20.9)

The modulus `k = θ₂²(0|τ)/θ₃²(0|τ)`, Jacobi's `K = (π/2)θ₃²(0|τ)`, `K' = -iτK`, the
symmetric-integral forms DLMF 20.9.3–20.9.5, Jacobi's inversion problem and the elliptic
modular function `k²` (DLMF §20.9(ii)).

## Main definitions

* `thetaModulusK`: the modulus `k = θ₂²(0|τ)/θ₃²(0|τ)` (DLMF 20.9.1).
* `thetaComplModulusK`: the complementary modulus `k' = θ₄²(0|τ)/θ₃²(0|τ)`.

## Main results

* `compEllIntK_eq_jacobiThetaThreeNullTau`: DLMF 20.9.2 in the rectangular case.
* `completeEllipticK_eq_jacobiThetaThreeNullTau_fundamental`: DLMF 20.9.2 for complex `τ` on the
  region where it holds.
* `symmetricEllipticRF_jacobiTheta`, `symmetricEllipticRF_jacobiTheta_rect`,
  `symmetricEllipticRF_jacobiTheta_eventually`: domain-corrected forms of DLMF 20.9.3.
* `symmetricEllipticRF_zero_jacobiThetaNull`: DLMF 20.9.4.
* `exp_symmetricEllipticRF_ratio_eq_nome`: DLMF 20.9.5.
* `thetaModulusK_inversion`: Jacobi's inversion problem (DLMF §20.9(ii)).
* `thetaModulusK_sq_modular`: `k²` is the elliptic modular function (DLMF §20.9(ii)).

## Implementation notes

The project's complete elliptic integral `Real.completeEllipticKOfParameter` is real, so 20.9.2 is
stated in the rectangular case `τ = it`, `t > 0` (real nome `q = e^{-πt}`), which is DLMF's
principal case (§20.1). For complex `τ` the printed `K(k) = (π/2)θ₃²` holds only on part of the
upper half-plane with the principal branch of `K` (checked numerically): the translates `F + 2n` of
the fundamental region `F` of `Γ(2)`, stated with the complex principal `K` of Chapter 22 in
`completeEllipticK_eq_jacobiThetaThreeNullTau_fundamental`. Carlson's `R_F` is the complex
Chapter 19 integral `DLMF.EllipticIntegrals.symmetricEllipticRF` (DLMF 19.16.1).

**Domain correction (20.9.3).** The printed identity holds for real `z` only when
`|z| ≤ π/2` (and `z ≠ 0`, where the right side is a removable singularity); the left side is
`π`-periodic and even in `z` while the right side is not, and numerically (mpmath,
`τ = 0.8i`) the two sides differ for `z = 1.6, 2, 2.5`. For `τ = it` the identity holds for
complex `z` in the open period rectangle `|Re z| < π/2`, `|Im z| < πt/2`, and for general `τ`
it holds near `z = 0`; it fails at some points of the period parallelogram `π(s + rτ)`,
`|s|, |r| < 1/2`, for non-rectangular `τ`.

The relation between `θⱼ` and the Jacobian and Weierstrass elliptic functions (§20.9(ii),
DLMF §§22.2, 23.6(i)) is treated in the Chapter 22 and 23 modules.
`DLMF.Elliptic.Real.completeEllipticKOfParameter_eq_jacobiThetaThreeNullQ` proves 20.9.2 for a real
nome in the form `m = 1 - θ₄⁴/θ₃⁴`.
-/

@[expose] public section

open Complex Filter Topology
open scoped Real

noncomputable section

namespace DLMF.Theta

open DLMF.Elliptic DLMF.JacobiElliptic
open DLMF.EllipticIntegrals (symmetricEllipticRF)

/-- DLMF 20.9.1: the modulus `k = θ₂²(0|τ)/θ₃²(0|τ)`. -/
@[dlmf 20.9.E1]
def thetaModulusK (τ : ℂ) : ℂ := jacobiThetaTwoNullTau τ ^ 2 / jacobiThetaThreeNullTau τ ^ 2

/-- The complementary modulus `k' = θ₄²(0|τ)/θ₃²(0|τ)` (DLMF 20.9.1 with 20.7.5). -/
def thetaComplModulusK (τ : ℂ) : ℂ := jacobiThetaFourNullTau τ ^ 2 / jacobiThetaThreeNullTau τ ^ 2

/-- On the imaginary axis `k(it) = ρ(t)` is real (from
`DLMF.JacobiElliptic.jacobiModulusImag_spec`). -/
theorem thetaModulusK_I_mul {t : ℝ} (ht : 0 < t) :
    thetaModulusK (I * t) = (jacobiModulusImag t : ℂ) :=
  (jacobiModulusImag_spec ht).2.2.2.1
/-- `R_F(0, 1 - k², 1) = K(k)` and `R_F(0, k², 1) = K'(k)` at `k = ρ(t)`, in terms of
`B = θ₃(0|it)`. -/
private lemma symmetricEllipticRF_realThetaModulus {t : ℝ} (ht : 0 < t) :
    symmetricEllipticRF 0 ((1 - jacobiModulusImag t ^ 2 : ℝ) : ℂ) 1 = π / 2 *
        (jacobiThetaThreeImag t : ℂ) ^ 2 ∧
      symmetricEllipticRF 0 ((jacobiModulusImag t ^ 2 : ℝ) : ℂ) 1 = π / 2 * t *
          (jacobiThetaThreeImag t : ℂ) ^ 2 := by
  obtain ⟨h0, h1, -, -, -, -, a1, a2⟩ := jacobiModulusImag_spec ht
  have hk2 : jacobiModulusImag t ^ 2 < 1 := by nlinarith
  constructor
  · rw [← DLMF.EllipticIntegrals.completeEllipticK_ofReal_eq_symmetricEllipticRF hk2,
      completeEllipticK_ofReal hk2, a1]
    push_cast; ring
  · set κ := Real.sqrt (1 - jacobiModulusImag t ^ 2)
    have hκ : κ ^ 2 = 1 - jacobiModulusImag t ^ 2 := Real.sq_sqrt (by linarith)
    have hκ1 : κ ^ 2 < 1 := by rw [hκ]; nlinarith
    have e : (1 - κ ^ 2 : ℝ) = jacobiModulusImag t ^ 2 := by rw [hκ]; ring
    rw [← e, ← DLMF.EllipticIntegrals.completeEllipticK_ofReal_eq_symmetricEllipticRF hκ1,
      completeEllipticK_ofReal hκ1, hκ, a2]
    push_cast; ring

/-- DLMF 20.9.2 (rectangular case `τ = it`, `t > 0`): with `k = θ₂²(0|it)/θ₃²(0|it)` (real),
`K(k) = (π/2) θ₃²(0|it)` and `K'(k) = K(k') = -iτ K(k) = t K(k)`. Here `K(k) =
Real.completeEllipticKOfParameter (k²)`.
Corrected from the printed DLMF formula: with the principal complex `K(k)` the printed identity
fails for some complex `τ` (58 of 308 samples), so this form is restricted to `τ = it`; the
full-domain form with its region of validity is
`completeEllipticK_eq_jacobiThetaThreeNullTau_fundamental`. -/
@[dlmf 20.9.E2]
theorem compEllIntK_eq_jacobiThetaThreeNullTau {t : ℝ} (ht : 0 < t) :
    (thetaModulusK (I * t)).im = 0 ∧
    ((Real.completeEllipticKOfParameter ((thetaModulusK (I * t)).re ^ 2) : ℂ) =
      π / 2 * jacobiThetaThreeNullTau (I * t) ^ 2) ∧
    ((Real.completeEllipticKOfParameter (1 - (thetaModulusK (I * t)).re ^ 2) : ℂ) =
      -I * (I * t) * Real.completeEllipticKOfParameter ((thetaModulusK (I * t)).re ^ 2)) := by
  obtain ⟨-, -, -, -, -, -, h1, h2⟩ := jacobiModulusImag_spec ht
  rw [thetaModulusK_I_mul ht, ofReal_re, ofReal_im, h1, h2, jacobiThetaThreeNullTau,
    jacobiThetaThreeTau_zero_I_mul_eq_imag]
  refine ⟨rfl, by push_cast; ring, ?_⟩
  rw [← mul_assoc, neg_mul, I_mul_I]
  push_cast; ring

/-- DLMF 20.9.2, **corrected full-domain form** with the principal complex `K(k)`
(`DLMF.EllipticIntegrals.completeEllipticK`,
`K'(k) = DLMF.EllipticIntegrals.completeEllipticKPrime`): with `k = θ₂²(0|τ)/θ₃²(0|τ)`,
`K(k) = (π/2) θ₃²(0|τ)` and `K'(k) = -iτ K(k)` for `τ` in the fundamental region
`F = {|Re τ| < 1, |τ - 1/2| > 1/2, |τ + 1/2| > 1/2}` of `Γ(2)`, and `K(k) = (π/2) θ₃²(0|τ)` for
every translate `τ + 2n` of `F` (both sides are 2-periodic; `K'` is not). Corrected from the printed
DLMF formula: the printed identity has no condition on `τ`, but with the principal `K` it fails off
these translates (e.g. 58 of 308 random samples). Checked with mpmath: no failure at 205 + 471
points of `F` and exact agreement of the region `⋃ₙ (F + 2n)` with the set where `K = (π/2)θ₃²`
holds at 500 random points. -/
@[dlmf 20.9.E2 "corrected full-domain form: region of validity of the principal K"]
theorem completeEllipticK_eq_jacobiThetaThreeNullTau_fundamental {τ : ℂ} (hτ : 0 < τ.im)
    (hre : |τ.re| < 1) (h₁ : 1 / 2 < ‖τ - 1 / 2‖) (h₂ : 1 / 2 < ‖τ + 1 / 2‖) :
    DLMF.EllipticIntegrals.completeEllipticK (thetaModulusK τ) =
        π / 2 * jacobiThetaThreeNullTau τ ^ 2 ∧
      DLMF.EllipticIntegrals.completeEllipticKPrime (thetaModulusK τ) =
        -I * τ * DLMF.EllipticIntegrals.completeEllipticK (thetaModulusK τ) ∧
      ∀ n : ℤ, DLMF.EllipticIntegrals.completeEllipticK (thetaModulusK (τ + 2 * n)) =
        π / 2 * jacobiThetaThreeNullTau (τ + 2 * n) ^ 2 := by
  sorry

/-- `θ₄(x|it)` is real for real `x`. -/
private lemma jacobiThetaFourTau_I_mul_im (t x : ℝ) :
    (jacobiThetaFourTau (x : ℂ) (I * t)).im = 0 := by
  rw [← Complex.conj_eq_iff_im, jacobiThetaFourTau, jacobiThetaThreeTau, jacobiTheta₂_conj]
  congr 1
  · rw [show ((x : ℂ) + π / 2) / π = (((x + π / 2) / π : ℝ) : ℂ) by push_cast; ring,
      Complex.conj_ofReal]
  · simp

/-- `θ₄(x|it) > 0` for real `x`, `t > 0`. -/
private lemma jacobiThetaFourTau_I_mul_re_pos {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 < (jacobiThetaFourTau (x : ℂ) (I * t)).re := by
  have hτ : 0 < (I * (t : ℂ)).im := by simpa using ht
  set f : ℝ → ℝ := fun y => (jacobiThetaFourTau (y : ℂ) (I * t)).re with hf
  have hcont : Continuous f :=
    Complex.continuous_re.comp ((differentiable_jacobiThetaTau 4 hτ).continuous.comp
      Complex.continuous_ofReal)
  have hne : ∀ y : ℝ, f y ≠ 0 := by
    intro y hy
    have h0 : jacobiThetaFourTau (y : ℂ) (I * t) = 0 := by
      apply Complex.ext
      · exact hy
      · exact jacobiThetaFourTau_I_mul_im t y
    obtain ⟨m, n, hmn⟩ := ((jacobiThetaTau_eq_zero_iff hτ y).2.2.2).mp h0
    have := congrArg Complex.im hmn
    simp at this
    rcases this with h | h
    · have h' : (2 * n + 1 : ℤ) = 0 := by exact_mod_cast (by linarith : (2 * n + 1 : ℝ) = 0)
      omega
    · exact ht.ne' h
  have h0 : 0 < f 0 := by
    simp only [hf, Complex.ofReal_zero]
    rw [jacobiThetaFourTau_zero_I_mul_eq_imag, ofReal_re]
    exact jacobiThetaFourImag_pos ht
  by_contra hneg
  push Not at hneg
  rcases le_total 0 x with hx | hx
  · obtain ⟨c, -, hc⟩ := intermediate_value_Icc' hx hcont.continuousOn ⟨hneg, h0.le⟩
    exact hne c hc
  · obtain ⟨c, -, hc⟩ := intermediate_value_Icc hx hcont.continuousOn ⟨hneg, h0.le⟩
    exact hne c hc

/-- `((r²)^{1/2}) = r` for `r > 0`, as complex numbers. -/
private lemma ofReal_sq_cpow_one_half {r : ℝ} (hr : 0 < r) :
    ((r ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = r := by
  have h := Complex.ofReal_cpow (sq_nonneg r) (1 / 2)
  rw [show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by push_cast; ring] at h
  rw [← h, ← Real.sqrt_eq_rpow, Real.sqrt_sq hr.le]

open DLMF.EllipticIntegrals
    (completeEllipticK symmetricEllipticRF_scale incompleteEllipticF_eq_ofReal
  incompleteEllipticF_eq_symmetricEllipticRF') in
/-- DLMF 20.9.3 for `0 < x ≤ π/2` (helper). -/
private lemma symmetricEllipticRF_jacobiTheta_of_pos {t : ℝ} (ht : 0 < t) {x : ℝ} (hx0 : 0 < x)
    (hx : x ≤ π / 2) :
    symmetricEllipticRF
      ((jacobiThetaTwoTau x (I * t) ^ 2 / jacobiThetaTwoNullTau (I * t) ^ 2).re : ℂ)
      ((jacobiThetaThreeTau x (I * t) ^ 2 / jacobiThetaThreeNullTau (I * t) ^ 2).re : ℂ)
      ((jacobiThetaFourTau x (I * t) ^ 2 / jacobiThetaFourNullTau (I * t) ^ 2).re : ℂ) =
      jacobiThetaOneDerivNullTau (I * t) / jacobiThetaOneTau x (I * t) * x := by
  obtain ⟨hk0, hk1, hτk, -, -, hKτ, -, -⟩ := jacobiModulusImag_spec ht
  set k := jacobiModulusImag t with hkdef
  set τ : ℂ := I * t with hτdef
  have hτ : 0 < τ.im := by simpa [hτdef] using ht
  have hm : k ^ 2 < 1 := by nlinarith
  set K := Real.completeEllipticKOfParameter (k ^ 2) with hKdef
  have hKpos : 0 < K := Real.completeEllipticKOfParameter_pos hm
  have hKk : completeEllipticK k = (K : ℂ) := completeEllipticK_ofReal hm
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hKN : (K : ℂ) = π / 2 * jacobiThetaThreeTau 0 τ ^ 2 := by
    rw [← hKk, ← hKτ, completeEllipticKOfTau]
  set u : ℝ := 2 * K * x / π with hudef
  have hu0 : 0 < u := by positivity
  have huK : u ≤ K := by
    rw [hudef, div_le_iff₀ Real.pi_pos]; nlinarith
  have hK0 : (K : ℂ) ≠ 0 := ofReal_ne_zero.mpr hKpos.ne'
  have hz : jacobiThetaArgument (u : ℂ) k = x := by
    rw [jacobiThetaArgument, hKk, hudef]; push_cast; field_simp
  have h2 := jacobiThetaTwoTau_zero_ne_zero hτ
  have h3 := jacobiThetaThreeTau_zero_ne_zero hτ
  have h4 := jacobiThetaFourTau_zero_ne_zero hτ
  -- the theta quotients
  have hsn := jacobiSn_ofReal hk0 hk1 u
  have hcn := jacobiCn_ofReal hk0 hk1 u
  have hdn := jacobiDn_ofReal hk0 hk1 u
  simp only [jacobiSn, jacobiCn, jacobiDn, jacobiPQ, jacobiGlaisher, jacobiLetterTheta,
    reduceCtorEq, ↓reduceIte, hz, hτk] at hsn hcn hdn
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau]
  rw [jacobiThetaOneDerivNullTau_eq_mul hτ]
  simp only [jacobiThetaTwoNullTau, jacobiThetaThreeNullTau, jacobiThetaFourNullTau]
  set sn := Real.jacobiSnOfParameter u (k ^ 2) with hsndef
  set cn := Real.jacobiCnOfParameter u (k ^ 2) with hcndef
  set dn := Real.jacobiDnOfParameter u (k ^ 2) with hdndef
  -- `θ₄(x)/θ₄(0)` is a positive real
  have hT4im : (jacobiThetaFourTau (x : ℂ) τ).im = 0 := jacobiThetaFourTau_I_mul_im t x
  have hT4 : jacobiThetaFourTau (x : ℂ) τ = ((jacobiThetaFourTau (x : ℂ) τ).re : ℂ) :=
    Complex.ext (by simp) (by simp [hT4im])
  have hN4 : jacobiThetaFourTau 0 τ = (jacobiThetaFourImag t : ℂ) :=
    jacobiThetaFourTau_zero_I_mul_eq_imag t
  set aR := (jacobiThetaFourTau (x : ℂ) τ).re / jacobiThetaFourImag t with haRdef
  have haR : 0 < aR :=
    div_pos (jacobiThetaFourTau_I_mul_re_pos ht x) (jacobiThetaFourImag_pos ht)
  have ha : jacobiThetaFourTau (x : ℂ) τ / jacobiThetaFourTau 0 τ = (aR : ℂ) := by
    rw [haRdef, ofReal_div, ← hT4, hN4]
  have haC : (aR : ℂ) ≠ 0 := ofReal_ne_zero.mpr haR.ne'
  rw [ha] at hsn hcn hdn
  have e2 : jacobiThetaTwoTau (x : ℂ) τ / jacobiThetaTwoTau 0 τ = cn * aR := by
    rw [← hcn]; field_simp
  have e3 : jacobiThetaThreeTau (x : ℂ) τ / jacobiThetaThreeTau 0 τ = dn * aR := by
    rw [← hdn]; field_simp
  have e1 : jacobiThetaOneTau (x : ℂ) τ = sn * aR * jacobiThetaTwoTau 0 τ *
      jacobiThetaFourTau 0 τ / jacobiThetaThreeTau 0 τ := by
    rw [← hsn]; field_simp
  have hsc := symmetricEllipticRF_scale (l := aR ^ 2) (by positivity) ((cn ^ 2 : ℝ) : ℂ)
    ((dn ^ 2 : ℝ) : ℂ) 1
  rw [mul_one, ofReal_sq_cpow_one_half haR] at hsc
  rw [← div_pow, e2, ← div_pow, e3, ← div_pow, ha,
    show ((cn : ℂ) * aR) ^ 2 = ((cn * aR) ^ 2 : ℝ) by push_cast; ring,
    show ((dn : ℂ) * aR) ^ 2 = ((dn * aR) ^ 2 : ℝ) by push_cast; ring,
    show ((aR : ℂ)) ^ 2 = ((aR ^ 2 : ℝ) : ℂ) by push_cast; ring, ofReal_re, ofReal_re, ofReal_re,
    show (((cn * aR) ^ 2 : ℝ) : ℂ) = ((aR ^ 2 : ℝ) : ℂ) * ((cn ^ 2 : ℝ) : ℂ) by push_cast; ring,
    show (((dn * aR) ^ 2 : ℝ) : ℂ) = ((aR ^ 2 : ℝ) : ℂ) * ((dn ^ 2 : ℝ) : ℂ) by push_cast; ring,
    hsc]
  -- `R_F(cn², dn², 1) = u / sn` from DLMF 19.25.5 at `φ = am u`
  set φ := Real.jacobiAmOfParameter u (k ^ 2) with hφdef
  have hmono : StrictMono (fun v => Real.jacobiAmOfParameter v (k ^ 2)) := by
    simp only [Real.jacobiAmOfParameter, hm, ↓reduceDIte]
    exact (Real.incompleteEllipticFOfParameterOrderIso hm).symm.strictMono
  have hφ0 : 0 < φ := by
    have := hmono hu0; simpa [Real.jacobiAmOfParameter_zero hm] using this
  have hφ1 : φ ≤ π / 2 := by
    have hK2 : Real.jacobiAmOfParameter K (k ^ 2) = π / 2 :=
        Real.jacobiAmOfParameter_completeEllipticKOfParameter hm
    exact hK2 ▸ hmono.monotone huK
  have hsin : Real.sin φ = sn := rfl
  have hcos : Real.cos φ = cn := rfl
  have hsnpos : 0 < sn := by
    rw [← hsin]; exact Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith [Real.pi_pos])
  obtain ⟨hp1, hp2⟩ := jacobiSnOfParameter_sq_add_jacobiCnOfParameter_sq_and hm u
  have hsn0 : (sn : ℂ) ≠ 0 := ofReal_ne_zero.mpr hsnpos.ne'
  have hp1' : (sn : ℂ) ^ 2 + (cn : ℂ) ^ 2 = 1 := by exact_mod_cast hp1
  have hp2' : (k : ℂ) ^ 2 * (sn : ℂ) ^ 2 + (dn : ℂ) ^ 2 = 1 := by exact_mod_cast hp2
  have hsc' := symmetricEllipticRF_scale (l := (1 / sn) ^ 2) (by positivity) ((cn ^ 2 : ℝ) : ℂ)
    ((dn ^ 2 : ℝ) : ℂ) 1
  rw [mul_one, ofReal_sq_cpow_one_half (by positivity)] at hsc'
  have hF := incompleteEllipticF_eq_symmetricEllipticRF' (k := (k : ℂ)) hφ0 hφ1
  simp only at hF
  rw [incompleteEllipticF_eq_ofReal (m := k ^ 2) (by push_cast; ring) hm.le φ,
    Real.incompleteEllipticFOfParameter_jacobiAmOfParameter hm, hsin] at hF
  rw [show ((1 / sn ^ 2 : ℝ) : ℂ) - 1 = (((1 / sn) ^ 2 : ℝ) : ℂ) * ((cn ^ 2 : ℝ) : ℂ) by
      push_cast; field_simp; linear_combination (-1 : ℂ) * hp1',
    show ((1 / sn ^ 2 : ℝ) : ℂ) - (k : ℂ) ^ 2 = (((1 / sn) ^ 2 : ℝ) : ℂ) * ((dn ^ 2 : ℝ) : ℂ) by
      push_cast; field_simp; linear_combination (-1 : ℂ) * hp2',
    show ((1 / sn ^ 2 : ℝ) : ℂ) = (((1 / sn) ^ 2 : ℝ) : ℂ) by push_cast; ring, hsc'] at hF
  have hR : symmetricEllipticRF ((cn ^ 2 : ℝ) : ℂ) ((dn ^ 2 : ℝ) : ℂ) 1 = u / sn := by
    rw [hF]; push_cast; field_simp
  rw [hR, e1, hudef]
  push_cast
  rw [hKN]
  field_simp


/-- DLMF 20.9.3 (rectangular case, **domain-corrected**): for `τ = it`, `t > 0`, and real `z` with
`0 < |z| ≤ π/2`, `R_F(θ₂²(z)/θ₂²(0), θ₃²(z)/θ₃²(0), θ₄²(z)/θ₄²(0)) = z θ₁'(0)/θ₁(z)`.
Corrected from the printed DLMF formula: the printed identity has no branch condition, but the
left side is `π`-periodic and even in real `z` and the right side is not (it fails at
`z = 1.6`, `τ = 0.8i`); the true condition is a branch condition (continuation from `z = 0`).
`R_F` is the complex `symmetricEllipticRF` at the real arguments; the complex-`z` forms are
`symmetricEllipticRF_jacobiTheta_rect` and `symmetricEllipticRF_jacobiTheta_eventually`. -/
@[dlmf 20.9.E3 "domain-corrected: valid for real 0 < |z| ≤ π/2"]
theorem symmetricEllipticRF_jacobiTheta {t : ℝ} (ht : 0 < t) {x : ℝ} (hx0 : 0 < |x|)
    (hx : |x| ≤ π / 2) :
    symmetricEllipticRF
      ((jacobiThetaTwoTau x (I * t) ^ 2 / jacobiThetaTwoNullTau (I * t) ^ 2).re : ℂ)
      ((jacobiThetaThreeTau x (I * t) ^ 2 / jacobiThetaThreeNullTau (I * t) ^ 2).re : ℂ)
      ((jacobiThetaFourTau x (I * t) ^ 2 / jacobiThetaFourNullTau (I * t) ^ 2).re : ℂ) =
      jacobiThetaOneDerivNullTau (I * t) / jacobiThetaOneTau x (I * t) * x := by
  rcases lt_or_gt_of_ne (abs_pos.mp hx0) with hneg | hpos
  · rw [abs_of_neg hneg] at hx
    have h := symmetricEllipticRF_jacobiTheta_of_pos ht (x := -x) (by linarith) (by linarith)
    push_cast at h
    rw [jacobiThetaTwoTau_neg, jacobiThetaThreeTau_neg, jacobiThetaFourTau_neg,
      jacobiThetaOneTau_neg] at h
    rw [h]
    ring
  · rw [abs_of_pos hpos] at hx
    exact symmetricEllipticRF_jacobiTheta_of_pos ht hpos hx

/-- DLMF 20.9.3, **corrected complex form** (rectangular case): for `τ = it`, `t > 0`, and
complex `z ≠ 0` in the open period rectangle `|Re z| < π/2`, `|Im z| < πt/2`,
`R_F(θ₂²(z)/θ₂²(0), θ₃²(z)/θ₃²(0), θ₄²(z)/θ₄²(0)) = z θ₁'(0)/θ₁(z)` with the complex `R_F` of
DLMF 19.16.1. Corrected from the printed DLMF formula, which has no condition on `z`: the
printed identity fails at real `z = 1.6` (`τ = 0.8i`) and, for `τ = it`, at 373 of 500 sampled
points with `π t/2 < |Im z| < 0.9 π t`. Checked with mpmath (`elliprf`, `jtheta`): no failure at
3500 points of the rectangle, including points within `10⁻⁴` of its edges, for
`0.05 ≤ t ≤ 4`. -/
@[dlmf 20.9.E3 "corrected complex form: τ = it, z in the open period rectangle"]
theorem symmetricEllipticRF_jacobiTheta_rect {t : ℝ} (ht : 0 < t) {z : ℂ} (hz0 : z ≠ 0)
    (hre : |z.re| < π / 2) (him : |z.im| < π * t / 2) :
    symmetricEllipticRF
      (jacobiThetaTwoTau z (I * t) ^ 2 / jacobiThetaTwoNullTau (I * t) ^ 2)
      (jacobiThetaThreeTau z (I * t) ^ 2 / jacobiThetaThreeNullTau (I * t) ^ 2)
      (jacobiThetaFourTau z (I * t) ^ 2 / jacobiThetaFourNullTau (I * t) ^ 2) =
      jacobiThetaOneDerivNullTau (I * t) / jacobiThetaOneTau z (I * t) * z := by
  sorry

/-- DLMF 20.9.3, **corrected complex form** (general `τ`): for every `τ` in the upper half-plane
the identity `R_F(θ₂²(z)/θ₂²(0), θ₃²(z)/θ₃²(0), θ₄²(z)/θ₄²(0)) = z θ₁'(0)/θ₁(z)` holds for all
`z ≠ 0` in a neighbourhood of `0` (the branch of `R_F` continued from `z = 0`, where all three
arguments equal `1`). Corrected from the printed DLMF formula, which has no condition on `z`:
for non-rectangular `τ` the identity fails at some points of the period parallelogram
`π(s + rτ)`, `|s|, |r| < 1/2` (e.g. `τ = 0.448 + 0.520i`, `s = -0.400`, `r = -0.318`; 362 of
3000 samples with `τ` in the `Γ(2)` fundamental region). Checked with mpmath: no failure at
1000 random `τ` with `|z| ≤ 0.07 min(1, Im τ)`. -/
@[dlmf 20.9.E3 "corrected complex form: general τ, z near 0"]
theorem symmetricEllipticRF_jacobiTheta_eventually {τ : ℂ} (hτ : 0 < τ.im) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      symmetricEllipticRF
        (jacobiThetaTwoTau z τ ^ 2 / jacobiThetaTwoNullTau τ ^ 2)
        (jacobiThetaThreeTau z τ ^ 2 / jacobiThetaThreeNullTau τ ^ 2)
        (jacobiThetaFourTau z τ ^ 2 / jacobiThetaFourNullTau τ ^ 2) =
        jacobiThetaOneDerivNullTau τ / jacobiThetaOneTau z τ * z := by
  sorry

/-- DLMF 20.9.4 (rectangular case `τ = it`): `R_F(0, θ₃⁴(0,q), θ₄⁴(0,q)) = π/2`. -/
@[dlmf 20.9.E4]
theorem symmetricEllipticRF_zero_jacobiThetaNull {t : ℝ} (ht : 0 < t) :
    symmetricEllipticRF 0 ((jacobiThetaThreeNullTau (I * t) ^ 4).re : ℂ)
      ((jacobiThetaFourNullTau (I * t) ^ 4).re : ℂ) = π / 2 := by
  have hB1 := one_le_jacobiThetaThreeImag ht
  have hB : 0 < jacobiThetaThreeImag t := by linarith
  have hC := jacobiThetaFourImag_pos ht
  have hf := jacobiThetaThreeImag_pow_four ht
  rw [jacobiThetaThreeNullTau, jacobiThetaFourNullTau, jacobiThetaThreeTau_zero_I_mul_eq_imag,
      jacobiThetaFourTau_zero_I_mul_eq_imag, ← ofReal_pow,
    ← ofReal_pow, ofReal_re, ofReal_re]
  set b := jacobiThetaThreeImag t ^ 4
  set c := jacobiThetaFourImag t ^ 4
  have hb : 0 < b := by positivity
  have hc : 0 < c := by positivity
  have hslit (x : ℝ) (hx : 0 < x) : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hx
  have hρ2 : 1 - jacobiModulusImag t ^ 2 = c / b := by
    simp only [jacobiModulusImag, b, c]; field_simp; linarith
  have hK := (symmetricEllipticRF_realThetaModulus ht).1
  rw [hρ2] at hK
  rw [DLMF.EllipticIntegrals.symmetricEllipticRF_zero_eq_pi_div_two_mul_carlsonRK
      (hslit b hb) (hslit c hc)]
  rw [DLMF.EllipticIntegrals.symmetricEllipticRF_zero_eq_pi_div_two_mul_carlsonRK
      (hslit _ (by positivity))
    one_mem_slitPlane, Carlson.TwoVariable.carlsonRK_comm (hslit _ (by positivity))
    one_mem_slitPlane] at hK
  have hsc := Carlson.carlsonRK_mul_of_pos hb (x := 1) (y := ((c / b : ℝ) : ℂ)) one_mem_slitPlane
    (hslit _ (by positivity))
  rw [mul_one, ← ofReal_mul, mul_div_cancel₀ _ hb.ne'] at hsc
  rw [hsc]
  have hpow : ((b : ℝ) : ℂ) ^ (-1 / 2 : ℂ) = ((jacobiThetaThreeImag t ^ 2)⁻¹ : ℝ) := by
    rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hb.le]
    congr 1
    rw [show b = (jacobiThetaThreeImag t ^ 2) ^ (2 : ℝ) by simp only [b]; rw [Real.rpow_two]; ring,
      ← Real.rpow_mul (by positivity)]
    norm_num
    exact Real.rpow_neg_one _
  rw [hpow]
  have hB2 : (jacobiThetaThreeImag t : ℂ) ≠ 0 := ofReal_ne_zero.mpr hB.ne'
  calc (π / 2 : ℂ) * (((jacobiThetaThreeImag t ^ 2)⁻¹ : ℝ) *
         Carlson.TwoVariable.carlsonRK 1 ((c / b : ℝ) : ℂ))
      = ((jacobiThetaThreeImag t ^ 2)⁻¹ : ℝ) * ((π / 2 : ℂ) * Carlson.TwoVariable.carlsonRK 1
          ((c / b : ℝ) : ℂ)) := by ring
    _ = π / 2 := by
      rw [hK]; push_cast; field_simp

/-- DLMF 20.9.5 (rectangular case `τ = it`, real nome `q = e^{-πt}`):
`exp(-π R_F(0, k², 1)/R_F(0, k'², 1)) = q` with `k = θ₂²(0)/θ₃²(0)`, `k'² = 1 - k²`. -/
@[dlmf 20.9.E5]
theorem exp_symmetricEllipticRF_ratio_eq_nome {t : ℝ} (ht : 0 < t) :
    Complex.exp (-(π * symmetricEllipticRF 0 (((thetaModulusK (I * t)).re ^ 2 : ℝ) : ℂ) 1 /
      symmetricEllipticRF 0 ((1 - (thetaModulusK (I * t)).re ^ 2 : ℝ) : ℂ) 1)) =
      Real.exp (-(π * t)) := by
  obtain ⟨e1, e2⟩ := symmetricEllipticRF_realThetaModulus ht
  rw [thetaModulusK_I_mul ht, ofReal_re, e1, e2, ofReal_exp]
  have hB : (jacobiThetaThreeImag t : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (by linarith [one_le_jacobiThetaThreeImag ht])
  congr 1
  push_cast
  field_simp [pi_ne_zero']

/-- DLMF §20.9(ii): Jacobi's inversion problem. Every modulus `0 < k < 1` is `θ₂²(0|it)/θ₃²(0|it)`
for exactly one `t > 0` (and then `t = K'(k)/K(k)` by 20.9.2). -/
@[dlmf 20.9.ii]
theorem thetaModulusK_inversion {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    ∃! t : ℝ, 0 < t ∧ thetaModulusK (I * t) = k := by
  obtain ⟨t, ht, hρ⟩ := exists_jacobiModulusImag_eq hk0 hk1
  refine ⟨t, ⟨ht, by rw [thetaModulusK_I_mul ht, hρ]⟩, ?_⟩
  rintro s ⟨hs, hsk⟩
  rw [thetaModulusK_I_mul hs] at hsk
  have hsk' : jacobiModulusImag s = k := by exact_mod_cast hsk
  obtain ⟨-, -, -, -, -, -, a1, a2⟩ := jacobiModulusImag_spec ht
  obtain ⟨-, -, -, -, -, -, b1, b2⟩ := jacobiModulusImag_spec hs
  rw [hρ] at a1 a2
  rw [hsk'] at b1 b2
  have hB : 0 < jacobiThetaThreeImag s := by linarith [one_le_jacobiThetaThreeImag hs]
  have hB' : 0 < jacobiThetaThreeImag t := by linarith [one_le_jacobiThetaThreeImag ht]
  have e1 : π / 2 * jacobiThetaThreeImag s ^ 2 = π / 2 * jacobiThetaThreeImag t ^ 2 :=
      by rw [← b1, a1]
  have e2 : π / 2 * s * jacobiThetaThreeImag s ^ 2 = π / 2 * t * jacobiThetaThreeImag t ^ 2 :=
      by rw [← b2, a2]
  have hc : 0 < π / 2 * jacobiThetaThreeImag t ^ 2 := by positivity
  have e3 : (s - t) * (π / 2 * jacobiThetaThreeImag t ^ 2) = 0 := by linear_combination e2 - s * e1
  rcases mul_eq_zero.mp e3 with h | h
  · linarith
  · linarith

/-- DLMF §20.9(ii): `k² = θ₂⁴(0|τ)/θ₃⁴(0|τ)` is the elliptic modular function `λ(τ)`: it is
invariant
under `τ ↦ τ + 2` and satisfies `λ(-1/τ) = 1 - λ(τ)` (compare DLMF 23.15.2, 23.15.6). -/
@[dlmf 20.9.ii]
theorem thetaModulusK_sq_modular {τ : ℂ} (hτ : 0 < τ.im) :
    thetaModulusK (τ + 2) ^ 2 = thetaModulusK τ ^ 2 ∧
      thetaModulusK (-1 / τ) ^ 2 = 1 - thetaModulusK τ ^ 2 := by
  obtain ⟨h2, h3, h4⟩ := jacobiThetaNullTau_ne_zero hτ
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  constructor
  · have he : cexp (π * I / 4) ^ 8 = 1 := by
      rw [← exp_nat_mul, show ((8 : ℕ) : ℂ) * (π * I / 4) = 2 * π * I by push_cast; ring,
        exp_two_pi_mul_I]
    simp only [thetaModulusK, jacobiThetaTwoNullTau, jacobiThetaThreeNullTau]
    rw [show τ + 2 = τ + 1 + 1 by ring, jacobiThetaTwoTau_add_one, jacobiThetaTwoTau_add_one,
      jacobiThetaThreeTau_add_one, jacobiThetaFourTau_add_one]
    calc ((cexp (π * I / 4) * (cexp (π * I / 4) * jacobiThetaTwoTau 0 τ)) ^ 2 /
          jacobiThetaThreeTau 0 τ ^ 2) ^ 2 =
        cexp (π * I / 4) ^ 8 * (jacobiThetaTwoTau 0 τ ^ 2 / jacobiThetaThreeTau 0 τ ^ 2) ^ 2 := by
          ring
      _ = _ := by rw [he, one_mul]
  · have hc : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 :=
      cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ0))
    have e3 := jacobiThetaThreeTau_neg_inv hτ 0
    have e4 := jacobiThetaFourTau_neg_inv hτ 0
    simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_div, exp_zero, one_mul] at e3 e4
    have h5 := jacobiThetaNull_fourth_power τ hτ
    simp only [thetaModulusK, jacobiThetaTwoNullTau, jacobiThetaThreeNullTau,
      jacobiThetaFourNullTau] at h2 h3 h5 ⊢
    rw [← e3, ← e4]
    field_simp
    linear_combination (-1 : ℂ) * h5

end DLMF.Theta

end
