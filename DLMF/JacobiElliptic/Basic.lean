/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Jacobi
public import DLMF.Elliptic.Theta
public import DLMF.QSeries.Identities
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Jacobian elliptic functions: definitions (DLMF §22.2)

DLMF 22.2 defines the twelve Jacobian elliptic functions `pq(z, k)` (Glaisher's notation:
`p, q ∈ {s, c, d, n}`, `pp = 1`) as quotients of theta functions with nome
`q = exp(-π K'(k)/K(k))` and argument `ζ = π z/(2K(k))`.

## Design

* **Letters.** `JacobiLetter` has the four Glaisher letters `s, c, d, n`. For each letter
  `jacobiLetterTheta p ζ τ` is the normalized theta function
  `θ_s = θ₃(0)/(θ₂(0)θ₄(0)) θ₁(ζ)`, `θ_c = θ₂(ζ)/θ₂(0)`, `θ_d = θ₃(ζ)/θ₃(0)`, `θ_n = θ₄(ζ)/θ₄(0)`
  (all `θ_j(·|τ)` are the project's `DLMF.Elliptic.jacobiThetaOneTau … jacobiThetaFourTau`).
  By Jacobi's `θ₁'(0) = θ₂(0)θ₃(0)θ₄(0)` (DLMF 20.4.6) these are Neville's theta functions of
  §20.1, so `jacobiGlaisher p q ζ τ = θ_p/θ_q` (`= 1` when `p = q`) is DLMF 22.2.11, and the
  constants reproduce DLMF 22.2.4–22.2.9 exactly. Each `pq` is a *reduced* theta quotient, so its
  removable singularities are filled in (e.g. `sd` is finite where `sn` and `dn` have poles).
  Poles carry Lean's junk value `x / 0 = 0`.
* **Lattice form.** `jacobiPQTau p q z τ` uses `τ` (`Im τ > 0`) as the primary parameter, with
  `k = θ₂²(0|τ)/θ₃²(0|τ)`, `k' = θ₄²/θ₃²`, `K = (π/2)θ₃²(0|τ)`, `K' = -iτK` (DLMF 22.2.2,
  22.2.12) and `ζ = πz/(2K)`. All identities that follow from theta-function identities are
  proved in this form.
* **Modulus form.** `jacobiPQk p q z k` is DLMF's literal definition for complex `z` and `k`:
  `K(k) = compEllIntKk k` is the principal-branch integral 19.2.8,
  `K'(k) = compEllIntKpk k = K(√(1-k²))`, `τ = iK'/K` (22.2.12), `q = e^{iπτ}` (22.2.1) and
  `ζ = πz/(2K)` (22.2.3). DLMF's identities (with literal `k`, `k' = √(1-k²)`) hold on
  `jacobiModulusDomain = {Re k > 0} \ [1, ∞)`, where `k² ∈ ℂ \ ((-∞, 0] ∪ [1, ∞))`; there the
  inversion 22.2.2 is the (admitted) theorem `jacobi_inversion_k`. On the other side of the
  imaginary axis the definition depends only on `k²`, so it gives the functions of `-k`.
* **Real functions.** The existing real-variable `DLMF.Elliptic.Real.jacobiSnm/Cnm/Dnm` (in the
  parameter `m = k²`, defined through the amplitude) are bridged in `JacobiElliptic.Basic`
  by `jacobiSnk_ofReal` etc. for `0 < k < 1` (admitted).

Mathlib and TauCeti have no Jacobian elliptic functions (checked 2026-10-25).
-/

@[expose] public section

open Complex DLMF.Elliptic
open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

/-! ### Glaisher letters and normalized theta functions -/

/-- The four letters `s, c, d, n` of Glaisher's notation (DLMF 22.2.10). They label the four
lattice points `0, K, K + iK', iK'` of the fundamental unit cell (DLMF §22.4(ii)). -/
inductive JacobiLetter
  | s
  | c
  | d
  | n
  deriving DecidableEq, Repr

/-- The index `1, 2, 3, 4` of the theta function attached to a letter `s, c, d, n`
(DLMF 22.2.11). -/
def JacobiLetter.index : JacobiLetter → ℕ
  | .s => 1
  | .c => 2
  | .d => 3
  | .n => 4

/-- The theta functions normalized as in DLMF 22.2.4–22.2.9:
`θ_s(ζ) = θ₃(0)/(θ₂(0)θ₄(0)) θ₁(ζ)`, `θ_c(ζ) = θ₂(ζ)/θ₂(0)`, `θ_d(ζ) = θ₃(ζ)/θ₃(0)`,
`θ_n(ζ) = θ₄(ζ)/θ₄(0)`, all with `θ_j = θ_j(·|τ)` and `ζ` the *theta* argument `πz/(2K)`.
By DLMF 20.4.6 they coincide with Neville's theta functions (§20.1) as functions of `z`. -/
def jacobiLetterTheta : JacobiLetter → ℂ → ℂ → ℂ
  | .s, ζ, τ => jacobiThetaThreeTau 0 τ / (jacobiThetaTwoTau 0 τ * jacobiThetaFourTau 0 τ) *
      jacobiThetaOneTau ζ τ
  | .c, ζ, τ => jacobiThetaTwoTau ζ τ / jacobiThetaTwoTau 0 τ
  | .d, ζ, τ => jacobiThetaThreeTau ζ τ / jacobiThetaThreeTau 0 τ
  | .n, ζ, τ => jacobiThetaFourTau ζ τ / jacobiThetaFourTau 0 τ

/-- Glaisher's quotient `pq = θ_p/θ_q` in the theta argument `ζ` (DLMF 22.2.10–22.2.11), with
the convention `pp = 1`. -/
def jacobiGlaisher (p q : JacobiLetter) (ζ τ : ℂ) : ℂ :=
  if p = q then 1 else jacobiLetterTheta p ζ τ / jacobiLetterTheta q ζ τ

/-! ### The lattice (`τ`) parametrization -/

/-- The quarter period `K = (π/2) θ₃²(0|τ)` as a function of the lattice parameter
(DLMF 22.2.2, third formula). -/
@[dlmf 22.2.E2]
def compEllIntKTau (τ : ℂ) : ℂ := π / 2 * jacobiThetaThreeTau 0 τ ^ 2

/-- The complementary quarter period `K' = -iτK`, i.e. `τ = iK'/K` (DLMF 22.2.12). -/
@[dlmf 22.2.E12]
def compEllIntKpTau (τ : ℂ) : ℂ := -I * τ * compEllIntKTau τ

/-- The modulus `k = θ₂²(0|τ)/θ₃²(0|τ)` (DLMF 22.2.2, first formula). -/
@[dlmf 22.2.E2]
def jacobiModulusTau (τ : ℂ) : ℂ := jacobiThetaTwoTau 0 τ ^ 2 / jacobiThetaThreeTau 0 τ ^ 2

/-- The complementary modulus `k' = θ₄²(0|τ)/θ₃²(0|τ)` (DLMF 22.2.2, second formula). -/
@[dlmf 22.2.E2]
def jacobiComodulusTau (τ : ℂ) : ℂ := jacobiThetaFourTau 0 τ ^ 2 / jacobiThetaThreeTau 0 τ ^ 2

/-- The theta argument `ζ = πz/(2K)` (DLMF 22.2.3) in the lattice parametrization; it equals
`z/θ₃²(0|τ)`. -/
@[dlmf 22.2.E3]
def jacobiZetaTau (z τ : ℂ) : ℂ := π * z / (2 * compEllIntKTau τ)

/-- Glaisher's function `pq(z)` for the lattice parameter `τ` (`Im τ > 0`), DLMF 22.2.4–22.2.11
with `k = jacobiModulusTau τ`. -/
def jacobiPQTau (p q : JacobiLetter) (z τ : ℂ) : ℂ := jacobiGlaisher p q (jacobiZetaTau z τ) τ

/-! ### The modulus (`k`) parametrization -/

/-- Legendre's complete elliptic integral of the first kind for complex modulus,
`K(k) = ∫₀^{π/2} (1 - k² sin²θ)^{-1/2} dθ` with the principal power (DLMF 19.2.8); it is the
principal branch for `k² ∈ ℂ \ [1, ∞)`. -/
@[dlmf 19.2.E8]
def compEllIntKk (k : ℂ) : ℂ :=
  ∫ θ in (0 : ℝ)..(π / 2), (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))

/-- The complementary integral `K'(k) = K(k') = ∫₀^{π/2} (1 - (1 - k²) sin²θ)^{-1/2} dθ`
(DLMF 19.2.9), principal for `k² ∈ ℂ \ (-∞, 0]`. -/
@[dlmf 19.2.E9]
def compEllIntKpk (k : ℂ) : ℂ :=
  ∫ θ in (0 : ℝ)..(π / 2), (1 - (1 - k ^ 2) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))

/-- The complementary modulus `k' = √(1 - k²)` (principal square root, DLMF §22.1). -/
def jacobiComodulusk (k : ℂ) : ℂ := (1 - k ^ 2) ^ (1 / 2 : ℂ)

/-- The lattice parameter `τ = iK'(k)/K(k)` of the modulus `k` (DLMF 22.2.12). -/
@[dlmf 22.2.E12]
def jacobiTauk (k : ℂ) : ℂ := I * compEllIntKpk k / compEllIntKk k

/-- The nome `q = exp(-πK'(k)/K(k))` (DLMF 22.2.1). -/
@[dlmf 22.2.E1]
def jacobiNomek (k : ℂ) : ℂ := cexp (-(π * compEllIntKpk k / compEllIntKk k))

/-- The theta argument `ζ = πz/(2K(k))` (DLMF 22.2.3). -/
@[dlmf 22.2.E3]
def jacobiZetak (z k : ℂ) : ℂ := π * z / (2 * compEllIntKk k)

/-- The domain of moduli on which DLMF's formulas hold with literal `k` and the principal
`k' = √(1 - k²)`: `Re k > 0` and `k ∉ [1, ∞)`, equivalently `k² ∈ ℂ \ ((-∞, 0] ∪ [1, ∞))` with
`Re k > 0`. It contains `0 < k < 1`. -/
def jacobiModulusDomain : Set ℂ := {k | 0 < k.re ∧ (k.im = 0 → k.re < 1)}

/-- Glaisher's function `pq(z, k)` of DLMF 22.2.4–22.2.10 for complex `z` and `k`: the theta
quotient with `τ = iK'/K` (nome `q = e^{iπτ}`) at `ζ = πz/(2K)`. -/
def jacobiPQk (p q : JacobiLetter) (z k : ℂ) : ℂ :=
  jacobiGlaisher p q (jacobiZetak z k) (jacobiTauk k)

/-! ### The twelve functions in the modulus `k` -/

/-- `sn(z, k)` (DLMF 22.2.4). -/
@[dlmf 22.2.E4]
def jacobiSnk (z k : ℂ) : ℂ := jacobiPQk .s .n z k
/-- `cn(z, k)` (DLMF 22.2.5). -/
@[dlmf 22.2.E5]
def jacobiCnk (z k : ℂ) : ℂ := jacobiPQk .c .n z k
/-- `dn(z, k)` (DLMF 22.2.6). -/
@[dlmf 22.2.E6]
def jacobiDnk (z k : ℂ) : ℂ := jacobiPQk .d .n z k
/-- `sd(z, k)` (DLMF 22.2.7). -/
@[dlmf 22.2.E7]
def jacobiSdk (z k : ℂ) : ℂ := jacobiPQk .s .d z k
/-- `cd(z, k)` (DLMF 22.2.8). -/
@[dlmf 22.2.E8]
def jacobiCdk (z k : ℂ) : ℂ := jacobiPQk .c .d z k
/-- `sc(z, k)` (DLMF 22.2.9). -/
@[dlmf 22.2.E9]
def jacobiSck (z k : ℂ) : ℂ := jacobiPQk .s .c z k
/-- `ns(z, k) = 1/sn(z, k)` (DLMF 22.2.4). -/
@[dlmf 22.2.E4]
def jacobiNsk (z k : ℂ) : ℂ := jacobiPQk .n .s z k
/-- `nc(z, k) = 1/cn(z, k)` (DLMF 22.2.5). -/
@[dlmf 22.2.E5]
def jacobiNck (z k : ℂ) : ℂ := jacobiPQk .n .c z k
/-- `nd(z, k) = 1/dn(z, k)` (DLMF 22.2.6). -/
@[dlmf 22.2.E6]
def jacobiNdk (z k : ℂ) : ℂ := jacobiPQk .n .d z k
/-- `ds(z, k) = 1/sd(z, k)` (DLMF 22.2.7). -/
@[dlmf 22.2.E7]
def jacobiDsk (z k : ℂ) : ℂ := jacobiPQk .d .s z k
/-- `dc(z, k) = 1/cd(z, k)` (DLMF 22.2.8). -/
@[dlmf 22.2.E8]
def jacobiDck (z k : ℂ) : ℂ := jacobiPQk .d .c z k
/-- `cs(z, k) = 1/sc(z, k)` (DLMF 22.2.9). -/
@[dlmf 22.2.E9]
def jacobiCsk (z k : ℂ) : ℂ := jacobiPQk .c .s z k

/-! ### The twelve functions in the lattice parameter `τ` -/

/-- `sn(z|τ)`: `sn` with modulus `k = θ₂²(0|τ)/θ₃²(0|τ)` (DLMF 22.2.4). -/
def jacobiSnTau (z τ : ℂ) : ℂ := jacobiPQTau .s .n z τ
/-- `cn(z|τ)` (DLMF 22.2.5). -/
def jacobiCnTau (z τ : ℂ) : ℂ := jacobiPQTau .c .n z τ
/-- `dn(z|τ)` (DLMF 22.2.6). -/
def jacobiDnTau (z τ : ℂ) : ℂ := jacobiPQTau .d .n z τ
/-- `sd(z|τ)` (DLMF 22.2.7). -/
def jacobiSdTau (z τ : ℂ) : ℂ := jacobiPQTau .s .d z τ
/-- `cd(z|τ)` (DLMF 22.2.8). -/
def jacobiCdTau (z τ : ℂ) : ℂ := jacobiPQTau .c .d z τ
/-- `sc(z|τ)` (DLMF 22.2.9). -/
def jacobiScTau (z τ : ℂ) : ℂ := jacobiPQTau .s .c z τ
/-- `ns(z|τ)`. -/
def jacobiNsTau (z τ : ℂ) : ℂ := jacobiPQTau .n .s z τ
/-- `nc(z|τ)`. -/
def jacobiNcTau (z τ : ℂ) : ℂ := jacobiPQTau .n .c z τ
/-- `nd(z|τ)`. -/
def jacobiNdTau (z τ : ℂ) : ℂ := jacobiPQTau .n .d z τ
/-- `ds(z|τ)`. -/
def jacobiDsTau (z τ : ℂ) : ℂ := jacobiPQTau .d .s z τ
/-- `dc(z|τ)`. -/
def jacobiDcTau (z τ : ℂ) : ℂ := jacobiPQTau .d .c z τ
/-- `cs(z|τ)`. -/
def jacobiCsTau (z τ : ℂ) : ℂ := jacobiPQTau .c .s z τ


/-! ### Theta toolkit: nonvanishing of the theta constants and half-period shifts -/

open DLMF.QSeries DLMF.QSeries.TripleProduct in
/-- The triple-product form of `jacobiTheta₂`:
`jacobiTheta₂ a τ = (Q;Q)_∞ (w;Q)_∞ (Q/w;Q)_∞` with `Q = e^{2πiτ}`, `w = -e^{πiτ + 2πia}`. -/
theorem je22a_jacobiTheta₂_eq_prod (a : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta₂ a τ =
      qPochhammerInf (cexp (2 * π * I * τ)) (cexp (2 * π * I * τ)) *
        qPochhammerInf (-cexp (π * I * τ + 2 * π * I * a)) (cexp (2 * π * I * τ)) *
        qPochhammerInf (cexp (2 * π * I * τ) / -cexp (π * I * τ + 2 * π * I * a))
          (cexp (2 * π * I * τ)) := by
  set Q := cexp (2 * π * I * τ) with hQ
  set w := -cexp (π * I * τ + 2 * π * I * a) with hw
  have hQn : ‖Q‖ < 1 := by
    rw [hQ, Complex.norm_exp]
    simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero, I_re,
      mul_im, zero_mul, add_zero, I_im, mul_one, zero_sub]
    simpa using Real.exp_lt_exp.mpr (show -(2 * π * τ.im) < 0 by nlinarith [Real.pi_pos])
  have hwne : w ≠ 0 := neg_ne_zero.mpr (Complex.exp_ne_zero _)
  rw [jacobi_triple_product hQn hwne, jacobiTheta₂]
  refine tsum_congr fun n => ?_
  have ht : ((tri n : ℤ) : ℂ) = (n : ℂ) * ((n : ℂ) - 1) / 2 := by
    rw [eq_div_iff two_ne_zero]; exact_mod_cast tri_mul_two n
  rw [jacobiTheta₂_term, cpow_tri, hw, neg_eq_neg_one_mul (cexp _), mul_zpow, ← mul_assoc,
    mul_assoc ((-1 : ℂ) ^ n), mul_comm (Q ^ tri n), ← mul_assoc, ← mul_zpow,
    show ((-1 : ℂ) * -1) = 1 by norm_num, one_zpow, one_mul, hQ, ← Complex.exp_int_mul,
    ← Complex.exp_int_mul, ← Complex.exp_add, ht]
  congr 1
  ring

/-- `‖e^{iπτ}‖ < 1` for `Im τ > 0`. -/
lemma je22a_norm_exp_pi_I_mul_lt_one {c : ℝ} (hc : 0 < c) {τ : ℂ} (hτ : 0 < τ.im) :
    ‖cexp (c * π * I * τ)‖ < 1 := by
  rw [Complex.norm_exp]
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, I_re, mul_im, zero_mul, add_zero,
    I_im, mul_one, zero_sub]
  simpa using Real.exp_lt_exp.mpr (show -(c * π * τ.im) < 0 by
    have := Real.pi_pos; have : 0 < c * π * τ.im := by positivity
    linarith)

/-- `θ₃(0|τ) ≠ 0` for `Im τ > 0` (Jacobi triple product). -/
theorem je22a_thetaThree_zero_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : jacobiThetaThreeTau 0 τ ≠ 0 := by
  have hQ := je22a_norm_exp_pi_I_mul_lt_one (c := 2) two_pos hτ
  have hE := je22a_norm_exp_pi_I_mul_lt_one (c := 1) one_pos hτ
  simp only [ofReal_one, one_mul] at hE
  have hQ' : ‖cexp (2 * π * I * τ)‖ < 1 := by simpa using hQ
  rw [jacobiThetaThreeTau, zero_div, je22a_jacobiTheta₂_eq_prod 0 hτ]
  have hw : -cexp (π * I * τ + 2 * π * I * 0) = -cexp (π * I * τ) := by simp
  have hQw : cexp (2 * π * I * τ) / -cexp (π * I * τ) = -cexp (π * I * τ) := by
    rw [show (2 : ℂ) * π * I * τ = π * I * τ + π * I * τ by ring, exp_add]
    field_simp [Complex.exp_ne_zero]
  rw [hw, hQw]
  have h1 : ‖-cexp (π * I * τ)‖ < 1 := by rwa [norm_neg]
  exact mul_ne_zero (mul_ne_zero (DLMF.QSeries.qPochhammerInf_ne_zero_of_norm_lt_one hQ' hQ')
    (DLMF.QSeries.qPochhammerInf_ne_zero_of_norm_lt_one h1 hQ'))
    (DLMF.QSeries.qPochhammerInf_ne_zero_of_norm_lt_one h1 hQ')

/-- `θ₄(0|τ) ≠ 0` for `Im τ > 0` (Jacobi triple product). -/
theorem je22a_thetaFour_zero_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : jacobiThetaFourTau 0 τ ≠ 0 := by
  have hE := je22a_norm_exp_pi_I_mul_lt_one (c := 1) one_pos hτ
  simp only [ofReal_one, one_mul] at hE
  have hQ' : ‖cexp (2 * π * I * τ)‖ < 1 := by
    simpa using je22a_norm_exp_pi_I_mul_lt_one (c := 2) two_pos hτ
  rw [jacobiThetaFourTau, jacobiThetaThreeTau, zero_add,
    show (π : ℂ) / 2 / π = 1 / 2 by field_simp [pi_ne_zero'], je22a_jacobiTheta₂_eq_prod _ hτ]
  have hw : -cexp (π * I * τ + 2 * π * I * (1 / 2)) = cexp (π * I * τ) := by
    rw [show π * I * τ + 2 * π * I * (1 / 2) = π * I * τ + π * I by ring, exp_add, exp_pi_mul_I]
    ring
  have hQw : cexp (2 * π * I * τ) / cexp (π * I * τ) = cexp (π * I * τ) := by
    rw [show (2 : ℂ) * π * I * τ = π * I * τ + π * I * τ by ring, exp_add]
    field_simp [Complex.exp_ne_zero]
  rw [hw, hQw]
  exact mul_ne_zero (mul_ne_zero (DLMF.QSeries.qPochhammerInf_ne_zero_of_norm_lt_one hQ' hQ')
    (DLMF.QSeries.qPochhammerInf_ne_zero_of_norm_lt_one hE hQ'))
    (DLMF.QSeries.qPochhammerInf_ne_zero_of_norm_lt_one hE hQ')

/-- `θ₂(0|τ) ≠ 0` for `Im τ > 0` (Jacobi triple product). -/
theorem je22a_thetaTwo_zero_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : jacobiThetaTwoTau 0 τ ≠ 0 := by
  have hQ' : ‖cexp (2 * π * I * τ)‖ < 1 := by
    simpa using je22a_norm_exp_pi_I_mul_lt_one (c := 2) two_pos hτ
  rw [jacobiThetaTwoTau, jacobiThetaThreeTau, zero_add,
    show (π : ℂ) * τ / 2 / π = τ / 2 by field_simp [pi_ne_zero'], je22a_jacobiTheta₂_eq_prod _ hτ]
  have hw : -cexp (π * I * τ + 2 * π * I * (τ / 2)) = -cexp (2 * π * I * τ) := by
    congr 2; ring
  have hQw : cexp (2 * π * I * τ) / -cexp (2 * π * I * τ) = -1 := by
    field_simp [Complex.exp_ne_zero]
  rw [hw, hQw]
  refine mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (mul_ne_zero
    (DLMF.QSeries.qPochhammerInf_ne_zero_of_norm_lt_one hQ' hQ')
    (DLMF.QSeries.qPochhammerInf_ne_zero_of_norm_lt_one (by rwa [norm_neg]) hQ'))
    (DLMF.QSeries.qPochhammerInf_ne_zero hQ' fun n => ?_))
  rcases n with _ | n
  · norm_num
  · rw [neg_one_mul, sub_neg_eq_add]
    intro h
    have h1 : ‖cexp (2 * π * I * τ) ^ (n + 1)‖ = 1 := by
      rw [show cexp (2 * π * I * τ) ^ (n + 1) = -1 by linear_combination h, norm_neg, norm_one]
    rw [norm_pow] at h1
    have : ‖cexp (2 * π * I * τ)‖ ^ (n + 1) < 1 := pow_lt_one₀ (norm_nonneg _) hQ' (by omega)
    linarith

/-- `θ₁(0|τ) = 0`. -/
theorem je22a_thetaOne_zero (τ : ℂ) : jacobiThetaOneTau 0 τ = 0 := by
  have h := jacobiThetaOneTau_neg 0 τ
  rw [neg_zero] at h
  exact CharZero.eq_neg_self_iff.mp h

/-- `θ₁(ζ + π/2) = θ₂(ζ)`. -/
theorem je22a_thetaOne_add_half_pi (ζ τ : ℂ) :
    jacobiThetaOneTau (ζ + π / 2) τ = jacobiThetaTwoTau ζ τ := by
  rw [jacobiThetaOneTau, show ζ + π / 2 + π / 2 = ζ + π by ring, jacobiThetaTwoTau_add_pi, neg_neg]

/-- `θ₂(ζ + π/2) = -θ₁(ζ)`. -/
theorem je22a_thetaTwo_add_half_pi (ζ τ : ℂ) :
    jacobiThetaTwoTau (ζ + π / 2) τ = -jacobiThetaOneTau ζ τ := by
  rw [jacobiThetaOneTau, neg_neg]

/-- `θ₃(ζ + π/2) = θ₄(ζ)`. -/
theorem je22a_thetaThree_add_half_pi (ζ τ : ℂ) :
    jacobiThetaThreeTau (ζ + π / 2) τ = jacobiThetaFourTau ζ τ := rfl

/-- `θ₄(ζ + π/2) = θ₃(ζ)`. -/
theorem je22a_thetaFour_add_half_pi (ζ τ : ℂ) :
    jacobiThetaFourTau (ζ + π / 2) τ = jacobiThetaThreeTau ζ τ := by
  rw [jacobiThetaFourTau, show ζ + π / 2 + π / 2 = ζ + π by ring, jacobiThetaThreeTau_add_pi]

/-- The multiplier `e^{-iπτ/4 - iζ}` of the half-period shift `ζ ↦ ζ + πτ/2`. -/
def je22a_shiftFactor (ζ τ : ℂ) : ℂ := cexp (-(π * I * τ / 4 + I * ζ))

lemma je22a_shiftFactor_ne_zero (ζ τ : ℂ) : je22a_shiftFactor ζ τ ≠ 0 := Complex.exp_ne_zero _

/-- `θ₃(ζ + πτ/2) = e^{-iπτ/4-iζ} θ₂(ζ)`. -/
theorem je22a_thetaThree_add_half_tau (ζ τ : ℂ) :
    jacobiThetaThreeTau (ζ + π * τ / 2) τ = je22a_shiftFactor ζ τ * jacobiThetaTwoTau ζ τ := by
  rw [jacobiThetaTwoTau, je22a_shiftFactor, ← mul_assoc, ← exp_add, neg_add_cancel, exp_zero,
    one_mul]

/-- `θ₂(ζ + πτ/2) = e^{-iπτ/4-iζ} θ₃(ζ)`. -/
theorem je22a_thetaTwo_add_half_tau (ζ τ : ℂ) :
    jacobiThetaTwoTau (ζ + π * τ / 2) τ = je22a_shiftFactor ζ τ * jacobiThetaThreeTau ζ τ := by
  rw [jacobiThetaTwoTau, show ζ + π * τ / 2 + π * τ / 2 = ζ + π * τ by ring,
    jacobiThetaThreeTau_add_pi_mul, je22a_shiftFactor, ← mul_assoc, ← exp_add]
  congr 2
  ring

lemma je22a_exp_neg_half_pi_I : cexp (-(π / 2 * I)) = -I := by
  rw [Complex.exp_neg, Complex.exp_pi_div_two_mul_I, inv_I]

/-- `θ₁(ζ + πτ/2) = i e^{-iπτ/4-iζ} θ₄(ζ)`. -/
theorem je22a_thetaOne_add_half_tau (ζ τ : ℂ) :
    jacobiThetaOneTau (ζ + π * τ / 2) τ = I * je22a_shiftFactor ζ τ * jacobiThetaFourTau ζ τ := by
  rw [jacobiThetaOneTau, jacobiThetaTwoTau, show ζ + π * τ / 2 + π / 2 + π * τ / 2 =
    (ζ + π / 2) + π * τ by ring, jacobiThetaThreeTau_add_pi_mul, je22a_shiftFactor,
    ← jacobiThetaFourTau, ← mul_assoc, ← exp_add]
  have h : π * I * τ / 4 + I * (ζ + π * τ / 2 + π / 2) + (-(π * I * τ) - 2 * I * (ζ + π / 2)) =
      -(π * I * τ / 4 + I * ζ) + (-(π / 2 * I)) := by ring
  rw [h, exp_add, je22a_exp_neg_half_pi_I]
  ring

/-- `θ₄(ζ + πτ/2) = i e^{-iπτ/4-iζ} θ₁(ζ)`. -/
theorem je22a_thetaFour_add_half_tau (ζ τ : ℂ) :
    jacobiThetaFourTau (ζ + π * τ / 2) τ = I * je22a_shiftFactor ζ τ * jacobiThetaOneTau ζ τ := by
  rw [jacobiThetaFourTau, show ζ + π * τ / 2 + π / 2 = (ζ + π / 2) + π * τ / 2 by ring,
    je22a_thetaThree_add_half_tau, je22a_thetaTwo_add_half_pi, je22a_shiftFactor,
    je22a_shiftFactor, show -(π * I * τ / 4 + I * (ζ + π / 2)) =
      -(π * I * τ / 4 + I * ζ) + (-(π / 2 * I)) by ring, exp_add, je22a_exp_neg_half_pi_I]
  ring

/-! ### Basic relations between the parametrizations -/

/-- The nome is `q = e^{iπτ}` with `τ = iK'/K` (DLMF 22.2.1 and 22.2.12). -/
@[dlmf 22.2.E1]
theorem jacobiNomek_eq_exp_tau (k : ℂ) : jacobiNomek k = cexp (π * I * jacobiTauk k) := by
  rw [jacobiNomek, jacobiTauk]
  congr 1
  rw [mul_div_assoc', ← mul_assoc, mul_assoc (π : ℂ) I I, I_mul_I]
  ring

/-- **Admitted.** For `k ∈ jacobiModulusDomain` the lattice parameter `τ = iK'/K` lies in the
upper half-plane (`|q| < 1`). This is the classical fact that `iK'/K` inverts the modular
`λ`-function on the cut plane `k² ∈ ℂ \ ((-∞, 0] ∪ [1, ∞))`. -/
@[dlmf 22.2.E1 "domain: Re k > 0, k ∉ [1, ∞), so |q| < 1"]
theorem jacobiTauk_im_pos {k : ℂ} (hk : k ∈ jacobiModulusDomain) : 0 < (jacobiTauk k).im := by
  sorry

/-- **Admitted (DLMF 22.2.2).** For `k ∈ jacobiModulusDomain` and `τ = iK'(k)/K(k)`:
`k = θ₂²(0|τ)/θ₃²(0|τ)`, `k' = θ₄²(0|τ)/θ₃²(0|τ)` with the principal `k' = √(1-k²)`, and
`K(k) = (π/2)θ₃²(0|τ)`. The sign of `k` requires `Re k > 0`; the right-hand sides depend on
`k²` only. -/
@[dlmf 22.2.E2 "domain: Re k > 0, k ∉ [1, ∞); fixes the sign of k and of k'"]
theorem jacobi_inversion_k {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiModulusTau (jacobiTauk k) = k ∧
      jacobiComodulusTau (jacobiTauk k) = jacobiComodulusk k ∧
      compEllIntKTau (jacobiTauk k) = compEllIntKk k := by
  sorry

/-- The modulus form is the lattice form at `τ = iK'/K`, given the third relation of
DLMF 22.2.2. -/
theorem jacobiPQk_eq_jacobiPQTau_of {k : ℂ} (hK : compEllIntKTau (jacobiTauk k) = compEllIntKk k)
    (p q : JacobiLetter) (z : ℂ) : jacobiPQk p q z k = jacobiPQTau p q z (jacobiTauk k) := by
  rw [jacobiPQk, jacobiPQTau, jacobiZetak, jacobiZetaTau, hK]

/-- The modulus form is the lattice form at `τ = iK'/K` on `jacobiModulusDomain`
(from the admitted DLMF 22.2.2). -/
theorem jacobiPQk_eq_jacobiPQTau {k : ℂ} (hk : k ∈ jacobiModulusDomain) (p q : JacobiLetter)
    (z : ℂ) : jacobiPQk p q z k = jacobiPQTau p q z (jacobiTauk k) :=
  jacobiPQk_eq_jacobiPQTau_of (jacobi_inversion_k hk).2.2 p q z

/-- For real `k` with `k² < 1` the complex integral `K(k)` is the real `K(m)`, `m = k²`. -/
theorem compEllIntKk_ofReal {k : ℝ} (hk : k ^ 2 < 1) :
    compEllIntKk k = (Real.compEllIntKm (k ^ 2) : ℂ) := by
  rw [compEllIntKk, Real.compEllIntKm, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hpos : 0 ≤ 1 - k ^ 2 * Real.sin θ ^ 2 := (one_sub_mul_sin_sq_pos hk θ).le
  rw [ofReal_cpow hpos]
  push_cast
  ring_nf

/-- For real `k` with `0 < k²` the complex `K'(k)` is the real `K(1 - m)`, `m = k²`. -/
theorem compEllIntKpk_ofReal {k : ℝ} (hk : 0 < k ^ 2) :
    compEllIntKpk k = (Real.compEllIntKm (1 - k ^ 2) : ℂ) := by
  rw [compEllIntKpk, Real.compEllIntKm, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hpos : 0 ≤ 1 - (1 - k ^ 2) * Real.sin θ ^ 2 :=
    (one_sub_mul_sin_sq_pos (by linarith) θ).le
  rw [ofReal_cpow hpos]
  push_cast
  ring_nf

/-- **Admitted.** Bridge to the real-variable `sn` (defined through the amplitude):
for `0 < k < 1` and real `u`, `sn(u, k) = Real.jacobiSnm u (k²)`. -/
@[dlmf 22.2.E4 "real bridge: 0 < k < 1, real argument; parameter m = k²"]
theorem jacobiSnk_ofReal {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (u : ℝ) :
    jacobiSnk u k = (Real.jacobiSnm u (k ^ 2) : ℂ) := by
  sorry

/-- **Admitted.** Bridge to the real-variable `cn`: for `0 < k < 1` and real `u`,
`cn(u, k) = Real.jacobiCnm u (k²)`. -/
@[dlmf 22.2.E5 "real bridge: 0 < k < 1, real argument; parameter m = k²"]
theorem jacobiCnk_ofReal {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (u : ℝ) :
    jacobiCnk u k = (Real.jacobiCnm u (k ^ 2) : ℂ) := by
  sorry

/-- **Admitted.** Bridge to the real-variable `dn`: for `0 < k < 1` and real `u`,
`dn(u, k) = Real.jacobiDnm u (k²)`. -/
@[dlmf 22.2.E6 "real bridge: 0 < k < 1, real argument; parameter m = k²"]
theorem jacobiDnk_ofReal {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (u : ℝ) :
    jacobiDnk u k = (Real.jacobiDnm u (k ^ 2) : ℂ) := by
  sorry

/-! ### §22.2: theta-quotient forms, Glaisher relations, Neville form, parity -/

/-- `z` is not congruent to the corner of letter `r` (the zeros of `θ_r(ζ)`); equivalently, the
functions `pr(z, k)` are finite at `z`. -/
def jacobiRegulark (r : JacobiLetter) (z k : ℂ) : Prop :=
  jacobiLetterTheta r (jacobiZetak z k) (jacobiTauk k) ≠ 0

/-- Glaisher's reciprocal relation `pq = 1/qp` (DLMF 22.2.10, and the second equalities of
22.2.4–22.2.9). It holds identically, including Lean's junk values at poles. -/
@[dlmf 22.2.E10, dlmf 22.2.E4, dlmf 22.2.E5, dlmf 22.2.E6, dlmf 22.2.E7, dlmf 22.2.E8,
  dlmf 22.2.E9]
theorem jacobiPQk_eq_one_div (p q : JacobiLetter) (z k : ℂ) :
    jacobiPQk p q z k = 1 / jacobiPQk q p z k := by
  unfold jacobiPQk jacobiGlaisher
  by_cases hpq : p = q
  · subst hpq; simp
  · simp only [hpq, Ne.symm hpq, ↓reduceIte, one_div_div]

/-- Glaisher's quotient relation `pq = pr/qr` (DLMF 22.2.10) for three distinct letters, at
points where the `·r` functions are finite. -/
@[dlmf 22.2.E10]
theorem jacobiPQk_eq_div {p q r : JacobiLetter} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {z k : ℂ} (hr : jacobiRegulark r z k) :
    jacobiPQk p q z k = jacobiPQk p r z k / jacobiPQk q r z k := by
  unfold jacobiPQk jacobiGlaisher
  simp only [hpq, hpr, hqr, ↓reduceIte]
  rw [div_div_div_cancel_right₀ hr]

/-- The convention `pp = 1` (DLMF 22.2.10). -/
@[dlmf 22.2.E10]
theorem jacobiPQk_self (p : JacobiLetter) (z k : ℂ) : jacobiPQk p p z k = 1 := by
  simp [jacobiPQk, jacobiGlaisher]

/-- `ζ = πz/(2K)` is odd in `z`. -/
lemma jacobiZetak_neg (z k : ℂ) : jacobiZetak (-z) k = -jacobiZetak z k := by
  simp only [jacobiZetak]; ring

/-- The normalized theta functions: `θ_s` is odd, `θ_c, θ_d, θ_n` are even. -/
lemma jacobiLetterTheta_neg (p : JacobiLetter) (ζ τ : ℂ) :
    jacobiLetterTheta p (-ζ) τ = (if p = .s then -1 else 1) * jacobiLetterTheta p ζ τ := by
  cases p <;> simp [jacobiLetterTheta, jacobiThetaOneTau_neg, jacobiThetaTwoTau_neg,
    jacobiThetaThreeTau_neg, jacobiThetaFourTau_neg]

/-- Parity (DLMF §22.2): the six functions whose name contains the letter `s` are odd in `z`;
the other six are even. Holds for all `z` and `k`. -/
@[dlmf 22.2]
theorem jacobiPQk_neg (p q : JacobiLetter) (z k : ℂ) :
    jacobiPQk p q (-z) k =
      (if (p = .s) ≠ (q = .s) then -jacobiPQk p q z k else jacobiPQk p q z k) := by
  unfold jacobiPQk jacobiGlaisher
  rw [jacobiZetak_neg]
  by_cases hpq : p = q
  · subst hpq; simp
  · simp only [hpq, ↓reduceIte, jacobiLetterTheta_neg]
    cases p <;> cases q <;> simp_all <;> ring

/-- The theta-quotient forms of DLMF 22.2.4–22.2.9 with `τ = iK'/K`, `ζ = πz/(2K)`: e.g.
`sn(z, k) = θ₃(0)/θ₂(0) · θ₁(ζ)/θ₄(ζ)`. Uses only `Im τ > 0`. -/
@[dlmf 22.2.E4, dlmf 22.2.E5, dlmf 22.2.E6, dlmf 22.2.E7, dlmf 22.2.E8, dlmf 22.2.E9]
theorem jacobi_eq_theta_quotients {k : ℂ} (hk : k ∈ jacobiModulusDomain) (z : ℂ) :
    jacobiSnk z k = jacobiThetaThreeTau 0 (jacobiTauk k) / jacobiThetaTwoTau 0 (jacobiTauk k) *
        (jacobiThetaOneTau (jacobiZetak z k) (jacobiTauk k) /
          jacobiThetaFourTau (jacobiZetak z k) (jacobiTauk k)) ∧
      jacobiCnk z k = jacobiThetaFourTau 0 (jacobiTauk k) / jacobiThetaTwoTau 0 (jacobiTauk k) *
        (jacobiThetaTwoTau (jacobiZetak z k) (jacobiTauk k) /
          jacobiThetaFourTau (jacobiZetak z k) (jacobiTauk k)) ∧
      jacobiDnk z k = jacobiThetaFourTau 0 (jacobiTauk k) / jacobiThetaThreeTau 0 (jacobiTauk k) *
        (jacobiThetaThreeTau (jacobiZetak z k) (jacobiTauk k) /
          jacobiThetaFourTau (jacobiZetak z k) (jacobiTauk k)) ∧
      jacobiSdk z k = jacobiThetaThreeTau 0 (jacobiTauk k) ^ 2 /
        (jacobiThetaTwoTau 0 (jacobiTauk k) * jacobiThetaFourTau 0 (jacobiTauk k)) *
        (jacobiThetaOneTau (jacobiZetak z k) (jacobiTauk k) /
          jacobiThetaThreeTau (jacobiZetak z k) (jacobiTauk k)) ∧
      jacobiCdk z k = jacobiThetaThreeTau 0 (jacobiTauk k) / jacobiThetaTwoTau 0 (jacobiTauk k) *
        (jacobiThetaTwoTau (jacobiZetak z k) (jacobiTauk k) /
          jacobiThetaThreeTau (jacobiZetak z k) (jacobiTauk k)) ∧
      jacobiSck z k = jacobiThetaThreeTau 0 (jacobiTauk k) / jacobiThetaFourTau 0 (jacobiTauk k) *
        (jacobiThetaOneTau (jacobiZetak z k) (jacobiTauk k) /
          jacobiThetaTwoTau (jacobiZetak z k) (jacobiTauk k)) := by
  have hτ : 0 < (jacobiTauk k).im := jacobiTauk_im_pos hk
  have h2 := je22a_thetaTwo_zero_ne_zero hτ
  have h3 := je22a_thetaThree_zero_ne_zero hτ
  have h4 := je22a_thetaFour_zero_ne_zero hτ
  simp only [jacobiSnk, jacobiCnk, jacobiDnk, jacobiSdk, jacobiCdk, jacobiSck, jacobiPQk,
    jacobiGlaisher, jacobiLetterTheta, reduceCtorEq, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp

/-- Neville's theta functions (DLMF §20.1) as functions of the Jacobi argument `z`, with
`u = z/θ₃²(0|τ)`: `θ_s = θ₃²(0) θ₁(u)/θ₁'(0)`, `θ_c = θ₂(u)/θ₂(0)`, `θ_d = θ₃(u)/θ₃(0)`,
`θ_n = θ₄(u)/θ₄(0)`. -/
def jacobiNevilleTau (p : JacobiLetter) (z τ : ℂ) : ℂ :=
  let u := z / jacobiThetaThreeTau 0 τ ^ 2
  match p with
  | .s => jacobiThetaThreeTau 0 τ ^ 2 * jacobiThetaOneTau u τ /
      deriv (fun w => jacobiThetaOneTau w τ) 0
  | .c => jacobiThetaTwoTau u τ / jacobiThetaTwoTau 0 τ
  | .d => jacobiThetaThreeTau u τ / jacobiThetaThreeTau 0 τ
  | .n => jacobiThetaFourTau u τ / jacobiThetaFourTau 0 τ

/-- **Admitted.** DLMF 22.2.11: `pq(z, k) = θ_p(z|τ)/θ_q(z|τ)` in Neville's theta functions,
`τ = iK'/K` (22.2.12), for distinct letters. This needs Jacobi's `θ₁'(0) = θ₂θ₃θ₄(0)`
(DLMF 20.4.6). -/
@[dlmf 22.2.E11]
theorem jacobiPQk_eq_neville {k : ℂ} (hk : k ∈ jacobiModulusDomain) {p q : JacobiLetter}
    (hpq : p ≠ q) (z : ℂ) :
    jacobiPQk p q z k = jacobiNevilleTau p z (jacobiTauk k) / jacobiNevilleTau q z (jacobiTauk k) :=
        by
  sorry

/-- **Admitted.** DLMF §22.2: for fixed `z` each `pq(z, k)` is meromorphic in `k` (on
`jacobiModulusDomain`, where the principal-branch definition is used). -/
@[dlmf 22.2]
theorem jacobiPQk_meromorphicOn_modulus (p q : JacobiLetter) (z : ℂ) :
    MeromorphicOn (fun k => jacobiPQk p q z k) jacobiModulusDomain := by
  sorry

/-- **Admitted.** DLMF §22.2: for `0 < k < 1` all twelve functions are real for real `z`.
(`k = 0, 1` are the limiting forms of §22.5(ii).) -/
@[dlmf 22.2]
theorem jacobiPQk_real {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (p q : JacobiLetter) (x : ℝ) :
    (jacobiPQk p q x k).im = 0 := by
  sorry

/-- `θ₃(·|τ)` is entire for `Im τ > 0`. -/
lemma je22a_differentiable_thetaThree {τ : ℂ} (hτ : 0 < τ.im) :
    Differentiable ℂ fun ζ => jacobiThetaThreeTau ζ τ := fun ζ =>
  (differentiableAt_jacobiTheta₂_fst (ζ / π) hτ).comp (f := fun w : ℂ => w / π) ζ
    ((differentiableAt_id).div_const _)

/-- The normalized theta functions are entire in `ζ` for `Im τ > 0`. -/
lemma je22a_differentiable_letterTheta {τ : ℂ} (hτ : 0 < τ.im) (p : JacobiLetter) :
    Differentiable ℂ fun ζ => jacobiLetterTheta p ζ τ := by
  have h3 := je22a_differentiable_thetaThree hτ
  have h2 : Differentiable ℂ fun ζ => jacobiThetaTwoTau ζ τ := fun ζ =>
    ((differentiable_exp.comp ((differentiable_const _).add
      (differentiable_id.const_mul I))) ζ).mul
      ((h3.comp (differentiable_id.add_const _)) ζ)
  cases p
  · exact (differentiable_const _).mul fun ζ => ((h2.comp (differentiable_id.add_const _)) ζ).neg
  · exact h2.div_const _
  · exact h3.div_const _
  · exact (h3.comp (differentiable_id.add_const _)).div_const _

/-- DLMF §22.2: for fixed `k` each Jacobian function is meromorphic in `z` (a quotient of entire
theta functions). -/
@[dlmf 22.2]
theorem jacobiPQk_meromorphicAt {k : ℂ} (hk : k ∈ jacobiModulusDomain) (p q : JacobiLetter)
    (z : ℂ) : MeromorphicAt (fun w => jacobiPQk p q w k) z := by
  have hτ := jacobiTauk_im_pos hk
  have hζ : Differentiable ℂ fun w => jacobiZetak w k := fun w =>
    ((differentiableAt_id.const_mul _).div_const _)
  unfold jacobiPQk jacobiGlaisher
  by_cases hpq : p = q
  · simp only [hpq, ↓reduceIte]; exact analyticAt_const.meromorphicAt
  · simp only [hpq, ↓reduceIte]
    exact (((je22a_differentiable_letterTheta hτ p).comp hζ).analyticAt z).meromorphicAt.div
      (((je22a_differentiable_letterTheta hτ q).comp hζ).analyticAt z).meromorphicAt

end DLMF.JacobiElliptic
