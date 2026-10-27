/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Theta.Identities
public import DLMF.Elliptic.ThetaAGM

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
  inversion 22.2.2 is the theorem `jacobi_inversion_k`. On the other side of the
  imaginary axis the definition depends only on `k²`, so it gives the functions of `-k`.
* **Real functions.** The existing real-variable `DLMF.Elliptic.Real.jacobiSnm/Cnm/Dnm` (in the
  parameter `m = k²`, defined through the amplitude) are bridged in
  `JacobiElliptic.SpecialValues` by `jacobiSnk_ofReal` etc. for `0 < k < 1` (proved by ODE
  uniqueness).

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
lemma je22a_jacobiTheta₂_eq_prod (a : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
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

theorem je22a_shiftFactor_ne_zero (ζ τ : ℂ) : je22a_shiftFactor ζ τ ≠ 0 := Complex.exp_ne_zero _

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

/-! ### `Im τ > 0`: positivity of `Re(K' conj K)` -/
/-- Sign facts for the principal square root `w^{1/2}`. -/
theorem p22R1_sqrt_parts (w : ℂ) :
    0 ≤ (w ^ (1 / 2 : ℂ)).re ∧ (0 ≤ w.im → 0 ≤ (w ^ (1 / 2 : ℂ)).im) ∧
      (w.im < 0 → (w ^ (1 / 2 : ℂ)).im ≤ 0) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  rw [cpow_def_of_ne_zero hw]
  have hre : (log w * (1 / 2 : ℂ)).re = Real.log ‖w‖ / 2 := by
    simp [log_re]; ring
  have him : (log w * (1 / 2 : ℂ)).im = arg w / 2 := by
    simp [log_im]; ring
  rw [exp_re, exp_im, hre, him]
  have h1 := neg_pi_lt_arg w
  have h2 := arg_le_pi w
  have hp := Real.exp_pos (Real.log ‖w‖ / 2)
  refine ⟨mul_nonneg hp.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩),
    fun h => mul_nonneg hp.le (Real.sin_nonneg_of_nonneg_of_le_pi
      (by have := arg_nonneg_iff.mpr h; linarith) (by linarith)), fun h => ?_⟩
  have := arg_neg_iff.mpr h
  exact mul_nonpos_of_nonneg_of_nonpos hp.le
    (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith))

/-- `(w^{1/2})^2 = w`. -/
theorem p22R1_sqrt_sq (w : ℂ) : (w ^ (1 / 2 : ℂ)) ^ 2 = w := by
  rw [← cpow_natCast, ← cpow_mul]
  · norm_num
  all_goals simp [log_im]; nlinarith [neg_pi_lt_arg w, arg_le_pi w, Real.pi_pos]

/-- Pointwise positivity: for `Im m > 0` and `s, t ∈ [0, 1]`,
`Re(√(1-(1-m)s) · conj √(1-mt)) > 0`. -/
lemma p22R1_re_sqrt_mul_conj_pos_of_im_pos {m : ℂ} (hm : 0 < m.im) {s t : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < ((1 - (1 - m) * s) ^ (1 / 2 : ℂ) * (starRingEnd ℂ) ((1 - m * t) ^ (1 / 2 : ℂ))).re := by
  set a := (1 - (1 - m) * s) ^ (1 / 2 : ℂ) with ha
  set b := (1 - m * t) ^ (1 / 2 : ℂ) with hb
  have hw1 : (1 - (1 - m) * (s : ℂ)).im = s * m.im := by simp; ring
  have hw2 : (1 - m * (t : ℂ)).im = -(t * m.im) := by simp; ring
  obtain ⟨ha0, ha1, -⟩ := p22R1_sqrt_parts (1 - (1 - m) * s)
  obtain ⟨hb0, -, hb2⟩ := p22R1_sqrt_parts (1 - m * t)
  have hai : 0 ≤ a.im := ha1 (by rw [hw1]; positivity)
  rcases ht0.eq_or_lt with rfl | htp
  · -- `b = 1`
    have : b = 1 := by rw [hb]; simp
    rw [this]
    simp only [map_one, mul_one]
    rcases hs0.eq_or_lt with rfl | hsp
    · rw [ha]; simp
    · -- `Im (a^2) = s Im m > 0`, so `Re a > 0`
      have h2 := p22R1_sqrt_sq (1 - (1 - m) * s)
      rw [← ha] at h2
      have him := congrArg Complex.im h2
      rw [hw1, pow_two, mul_im] at him
      have : 0 < s * m.im := mul_pos hsp hm
      nlinarith
  have hbi : b.im ≤ 0 := hb2 (by rw [hw2]; nlinarith)
  set z := a * (starRingEnd ℂ) b with hz
  have hzi : 0 ≤ z.im := by
    rw [hz, mul_im, conj_re, conj_im]; nlinarith
  have hz2 : z ^ 2 = (1 - (1 - m) * s) * (starRingEnd ℂ) (1 - m * t) := by
    rw [hz, mul_pow, ← map_pow, ha, hb, p22R1_sqrt_sq, p22R1_sqrt_sq]
  have him := congrArg Complex.im hz2
  rw [pow_two, mul_im] at him
  have hrhs : ((1 - (1 - m) * (s : ℂ)) * (starRingEnd ℂ) (1 - m * t)).im =
      m.im * (t * (1 - s) + s) := by
    simp [mul_im]; ring
  rw [hrhs] at him
  have : 0 < m.im * (t * (1 - s) + s) := mul_pos hm (by nlinarith)
  nlinarith


/-- Pointwise positivity of `Re(√(1-(1-m)s) · conj √(1-mt))` for `m ∉ (-∞, 0] ∪ [1, ∞)`. -/
lemma p22R1_re_sqrt_mul_conj_pos {m : ℂ} (hm : m.im ≠ 0 ∨ (m.im = 0 ∧ 0 < m.re ∧ m.re < 1))
    {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < ((1 - (1 - m) * s) ^ (1 / 2 : ℂ) * (starRingEnd ℂ) ((1 - m * t) ^ (1 / 2 : ℂ))).re := by
  rcases hm with hm | ⟨hm0, hm1, hm2⟩
  · rcases hm.lt_or_gt with hm | hm
    · have hc : 0 < ((starRingEnd ℂ) m).im := by simpa using hm
      have h := p22R1_re_sqrt_mul_conj_pos_of_im_pos hc hs0 hs1 ht0 ht1
      have harg1 : (1 - (1 - m) * (s : ℂ)).arg ≠ π := by
        rw [Ne, arg_eq_pi_iff]; intro ⟨h1, h2⟩
        simp at h1 h2
        rcases h2 with h2 | h2 <;> first | exact hm.ne h2 | (subst h2; simp at h1; linarith)
      have harg2 : (1 - m * (t : ℂ)).arg ≠ π := by
        rw [Ne, arg_eq_pi_iff]; intro ⟨h1, h2⟩
        simp at h1 h2
        rcases h2 with h2 | h2 <;> first | exact hm.ne h2 | (subst h2; simp at h1; linarith)
      have e1 := cpow_conj (1 - (1 - m) * (s : ℂ)) (1 / 2) harg1
      have e2 := cpow_conj (1 - m * (t : ℂ)) (1 / 2) harg2
      simp only [map_div₀, map_one, map_ofNat, map_sub, map_mul, conj_ofReal] at e1 e2
      rw [← conj_re, map_mul, Complex.conj_conj, e1, e2, Complex.conj_conj]
      exact h
    · exact p22R1_re_sqrt_mul_conj_pos_of_im_pos hm hs0 hs1 ht0 ht1
  · have hmr : m = (m.re : ℂ) := by apply Complex.ext <;> simp [hm0]
    have hw1 : (1 - (1 - m) * (s : ℂ)) = ((1 - (1 - m.re) * s : ℝ) : ℂ) := by
      rw [hmr]; push_cast; simp
    have hw2 : (1 - m * (t : ℂ)) = ((1 - m.re * t : ℝ) : ℂ) := by
      rw [hmr]; push_cast; simp
    have hp1 : 0 < 1 - (1 - m.re) * s := by nlinarith
    have hp2 : 0 < 1 - m.re * t := by nlinarith
    rw [hw1, hw2, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hp1.le, ← ofReal_cpow hp2.le, conj_ofReal, ← ofReal_mul,
      ofReal_re]
    exact mul_pos (Real.rpow_pos_of_pos hp1 _) (Real.rpow_pos_of_pos hp2 _)


/-- On `jacobiModulusDomain`, `k²` is non-real or lies in `(0, 1)`. -/
theorem p22R1_sq_of_mem_domain {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    (k ^ 2).im ≠ 0 ∨ ((k ^ 2).im = 0 ∧ 0 < (k ^ 2).re ∧ (k ^ 2).re < 1) := by
  obtain ⟨h0, h1⟩ := hk
  by_cases him : k.im = 0
  · right
    have := h1 him
    simp only [pow_two, mul_im, mul_re, him]
    refine ⟨by ring, by nlinarith, by nlinarith⟩
  · left
    simp only [pow_two, mul_im]
    intro h
    have : k.re * k.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact him h'

/-- The integrands of `K` and `K'` stay in the slit plane. -/
lemma p22R1_mem_slitPlane {m : ℂ} (hm : m.im ≠ 0 ∨ (m.im = 0 ∧ 0 < m.re ∧ m.re < 1))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    1 - (1 - m) * (s : ℂ) ∈ slitPlane ∧ 1 - m * (s : ℂ) ∈ slitPlane := by
  rw [mem_slitPlane_iff, mem_slitPlane_iff]
  rcases hs0.eq_or_lt with rfl | hs
  · simp
  rcases hm with hm | ⟨hm0, hm1, hm2⟩
  · exact ⟨Or.inr (by simp; exact ⟨hm, hs.ne'⟩), Or.inr (by simp; exact ⟨hm, hs.ne'⟩)⟩
  · constructor <;> left <;> simp [hm0] <;> nlinarith


/-- For `k ∈ jacobiModulusDomain` the lattice parameter `τ = iK'/K` lies in the
upper half-plane (`|q| < 1`). Proof: `Re(K' conj K) = ∫∫ Re(F(θ) conj G(φ)) > 0` pointwise, where
`F`, `G` are the integrands of `K'`, `K`; the pointwise positivity follows from
`Im(w₁ conj w₂) = Im(k²)(t(1-s)+s)` for `w₁ = 1-(1-k²)s`, `w₂ = 1-k²t`. -/
@[dlmf 22.2.E1 "domain: Re k > 0, k ∉ [1, ∞), so |q| < 1"]
theorem jacobiTauk_im_pos {k : ℂ} (hk : k ∈ jacobiModulusDomain) : 0 < (jacobiTauk k).im := by
  have hm := p22R1_sq_of_mem_domain hk
  set m := k ^ 2 with hmdef
  set F : ℝ → ℂ := fun θ => (1 - (1 - m) * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) with hFdef
  set G : ℝ → ℂ := fun θ => (1 - m * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) with hGdef
  have hsq (θ : ℝ) : (Real.sin θ : ℂ) ^ 2 = ((Real.sin θ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hs0 (θ : ℝ) : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hs1 (θ : ℝ) : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hF : Continuous F := Continuous.cpow (by fun_prop) continuous_const fun θ => by
    rw [hsq]; exact (p22R1_mem_slitPlane hm (hs0 θ) (hs1 θ)).1
  have hG : Continuous G := Continuous.cpow (by fun_prop) continuous_const fun θ => by
    rw [hsq]; exact (p22R1_mem_slitPlane hm (hs0 θ) (hs1 θ)).2
  have hKp : compEllIntKpk k = ∫ θ in (0 : ℝ)..(π / 2), F θ := rfl
  have hK : compEllIntKk k = ∫ θ in (0 : ℝ)..(π / 2), G θ := rfl
  set K := compEllIntKk k
  set K' := compEllIntKpk k
  have hpi : (0 : ℝ) < π / 2 := by positivity
  have hpt (θ φ : ℝ) : 0 < (F θ * (starRingEnd ℂ) (G φ)).re := by
    have h := p22R1_re_sqrt_mul_conj_pos hm (hs0 θ) (hs1 θ) (hs0 φ) (hs1 φ)
    simp only [hFdef, hGdef, hsq]
    rw [cpow_neg, cpow_neg, map_inv₀, ← mul_inv, inv_re]
    exact div_pos h (normSq_pos.mpr fun h0 => by rw [h0] at h; simp at h)
  have key : 0 < (K' * (starRingEnd ℂ) K).re := by
    have e1 : K' * (starRingEnd ℂ) K = ∫ θ in (0 : ℝ)..(π / 2), F θ * (starRingEnd ℂ) K := by
      rw [hKp, intervalIntegral.integral_mul_const]
    have hc1 : Continuous fun θ => F θ * (starRingEnd ℂ) K := hF.mul continuous_const
    have r1 := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (μ := MeasureTheory.volume)
      (hc1.intervalIntegrable 0 (π / 2))
    simp only [RCLike.re_to_complex] at r1
    rw [e1, ← r1]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((Complex.continuous_re.comp hc1).intervalIntegrable _ _) (fun θ _ => ?_) hpi
    have e2 : F θ * (starRingEnd ℂ) K =
        ∫ φ in (0 : ℝ)..(π / 2), F θ * (starRingEnd ℂ) (G φ) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.intervalIntegral_conj, hK]
    have hc2 : Continuous fun φ => F θ * (starRingEnd ℂ) (G φ) :=
      continuous_const.mul (Complex.continuous_conj.comp hG)
    have r2 := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (μ := MeasureTheory.volume)
      (hc2.intervalIntegrable 0 (π / 2))
    simp only [RCLike.re_to_complex] at r2
    show 0 < (F θ * (starRingEnd ℂ) K).re
    rw [e2, ← r2]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      ((Complex.continuous_re.comp hc2).intervalIntegrable _ _) (fun φ _ => hpt θ φ) hpi
  have hK0 : K ≠ 0 := fun h0 => by simp [h0] at key
  have hns : 0 < normSq K := normSq_pos.mpr hK0
  have : (jacobiTauk k).im = (K' * (starRingEnd ℂ) K).re / normSq K := by
    simp only [jacobiTauk, div_eq_mul_inv, inv_def, mul_im, mul_re, I_re, I_im, conj_re, conj_im]
    simp
    ring
  rw [this]
  exact div_pos key hns

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

/-! ### DLMF 22.2.2: the inversion `k = θ₂²/θ₃²(iK'/K)`

The real case `0 < k < 1` comes from Jacobi's `K = (π/2)θ₃²` for a real nome (the AGM,
`Real.compEllIntKm_eq_jacobiThetaThreeNullQ`), the modular transformation `τ ↦ -1/τ` and
Jacobi's identity `θ₃⁴ = θ₂⁴ + θ₄⁴` on the imaginary axis (proved here by lattice sums), with
the intermediate value theorem for `t ↦ θ₂²/θ₃²(it)`. The complex case follows by the identity
theorem: both sides are holomorphic on the connected open domain. -/

section p22R1Inversion

open Filter Topology MeasureTheory
open scoped Interval
section
open Set

/-- `P(q) = ∑_{n∈ℤ} q^{n²+n}`, so that `θ₂(q) = q^{1/4} P(q)`. -/
noncomputable def p22R1_P (q : ℝ) : ℝ := ∑' n : ℤ, q ^ (n ^ 2 + n)

lemma p22R1_summable_P {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun n : ℤ => q ^ (n ^ 2 + n) := by
  refine ((summable_zpow_abs hq0 hq1).mul_right q⁻¹).of_nonneg_of_le
    (fun _ => (zpow_pos hq0 _).le) fun n => ?_
  rw [← zpow_neg_one, ← zpow_add₀ hq0.ne']
  apply zpow_le_zpow_right_of_le_one₀ hq0 hq1.le
  rcases le_or_gt 0 n with h | h
  · rw [abs_of_nonneg h]; nlinarith
  · rw [abs_of_neg h]; nlinarith

/-- The odd sublattice `{(a,b) : a + b odd}` is parametrized by `(u,v) ↦ (u+v+1, u-v)`. -/
def p22R1_oddLatticeEquiv : ℤ × ℤ ≃ {p : ℤ × ℤ // ¬ Even (p.1 + p.2)} where
  toFun uv := ⟨(uv.1 + uv.2 + 1, uv.1 - uv.2), by
    rw [Int.not_even_iff_odd]; exact ⟨uv.1, by ring⟩⟩
  invFun p := ((p.1.1 + p.1.2 - 1) / 2, (p.1.1 - p.1.2 - 1) / 2)
  left_inv uv := by
    simp only
    rw [show uv.1 + uv.2 + 1 + (uv.1 - uv.2) - 1 = 2 * uv.1 by ring,
      show uv.1 + uv.2 + 1 - (uv.1 - uv.2) - 1 = 2 * uv.2 by ring]
    simp
  right_inv p := by
    obtain ⟨⟨a, b⟩, hp⟩ := p
    rw [Int.not_even_iff_odd] at hp
    obtain ⟨r, hr⟩ := hp
    simp only at hr ⊢
    have h1 : (a + b - 1) / 2 = r := by rw [hr]; omega
    have h2 : (a - b - 1) / 2 = r - b := by omega
    ext <;> simp [h1, h2]
    omega

/-- `θ₃(q)² - θ₄(q)² = 2q P(q²)²`. -/
lemma p22R1_three_sq_sub_four_sq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Real.jacobiThetaThreeNullQ q ^ 2 - Real.jacobiThetaFourNullQ q ^ 2 =
      2 * q * p22R1_P (q ^ 2) ^ 2 := by
  have hs3 := summable_zpow_sq hq0 hq1
  have hs4 := summable_neg_one_zpow_mul hq0 hq1
  have hq2 : 0 < q ^ 2 := by positivity
  have hq21 : q ^ 2 < 1 := by nlinarith
  have hsP := p22R1_summable_P hq2 hq21
  have h33 := tsum_mul_tsum_of_summable_norm hs3.norm hs3.norm
  have h44 := tsum_mul_tsum_of_summable_norm hs4.norm hs4.norm
  have hPP := tsum_mul_tsum_of_summable_norm hsP.norm hsP.norm
  have hP3 := summable_mul_of_summable_norm hs3.norm hs3.norm
  have hP4 := summable_mul_of_summable_norm hs4.norm hs4.norm
  set H : ℤ × ℤ → ℝ := fun p => q ^ (p.1 ^ 2) * q ^ (p.2 ^ 2) -
    (-1 : ℝ) ^ p.1 * q ^ (p.1 ^ 2) * ((-1 : ℝ) ^ p.2 * q ^ (p.2 ^ 2)) with hH
  have hHs : Summable H := hP3.sub hP4
  rw [Real.jacobiThetaThreeNullQ, Real.jacobiThetaFourNullQ, p22R1_P, sq, sq, sq,
      h33, h44, hPP, ← hP3.tsum_sub hP4]
  change ∑' p, H p = _
  rw [← hHs.tsum_subtype_add_tsum_subtype_compl {p : ℤ × ℤ | Even (p.1 + p.2)}]
  have heven : ∀ p : ↥({p : ℤ × ℤ | Even (p.1 + p.2)}), H p = 0 := by
    rintro ⟨⟨a, b⟩, hp⟩
    simp only [mem_ofPred_eq] at hp
    simp only [hH]
    rw [mul_mul_mul_comm, neg_one_zpow_add, hp.neg_one_zpow]
    ring
  rw [tsum_congr heven, tsum_zero, zero_add, ← tsum_mul_left]
  rw [show (∑' p : ↥({p : ℤ × ℤ | Even (p.1 + p.2)}ᶜ), H p) =
      ∑' p : {p : ℤ × ℤ // ¬ Even (p.1 + p.2)}, H p from rfl, ← p22R1_oddLatticeEquiv.tsum_eq]
  refine tsum_congr fun uv => ?_
  simp only [p22R1_oddLatticeEquiv, Equiv.coe_fn_mk, hH]
  have hodd : Odd (uv.1 + uv.2 + 1 + (uv.1 - uv.2)) := ⟨uv.1, by ring⟩
  rw [mul_mul_mul_comm, neg_one_zpow_add, hodd.neg_one_zpow]
  have e : q ^ ((uv.1 + uv.2 + 1) ^ 2) * q ^ ((uv.1 - uv.2) ^ 2) =
      q * ((q ^ 2) ^ (uv.1 ^ 2 + uv.1) * (q ^ 2) ^ (uv.2 ^ 2 + uv.2)) := by
    rw [← zpow_add₀ hq0.ne', ← zpow_add₀ (by positivity), ← zpow_natCast, ← zpow_mul,
      ← zpow_one_add₀ hq0.ne']
    congr 1; push_cast; ring
  rw [e]; ring

/-- `P(q)² = 2 P(q²) θ₃(q²)`. -/
lemma p22R1_P_sq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    p22R1_P q ^ 2 = 2 * (p22R1_P (q ^ 2) * Real.jacobiThetaThreeNullQ (q ^ 2)) := by
  have hq2 : 0 < q ^ 2 := by positivity
  have hq21 : q ^ 2 < 1 := by nlinarith
  have hsP := p22R1_summable_P hq0 hq1
  have hsP' := p22R1_summable_P hq2 hq21
  have hs3' := summable_zpow_sq hq2 hq21
  have hPP := tsum_mul_tsum_of_summable_norm hsP.norm hsP.norm
  have hP3 := tsum_mul_tsum_of_summable_norm hsP'.norm hs3'.norm
  have hHs := summable_mul_of_summable_norm hsP.norm hsP.norm
  set H : ℤ × ℤ → ℝ := fun p => q ^ (p.1 ^ 2 + p.1) * q ^ (p.2 ^ 2 + p.2) with hH
  rw [p22R1_P, sq, hPP, p22R1_P, Real.jacobiThetaThreeNullQ, hP3, two_mul]
  change ∑' p, H p = _
  rw [← hHs.tsum_subtype_add_tsum_subtype_compl {p : ℤ × ℤ | Even (p.1 + p.2)}]
  congr 1
  · rw [show (∑' p : ↥{p : ℤ × ℤ | Even (p.1 + p.2)}, H p) =
      ∑' p : {p : ℤ × ℤ // Even (p.1 + p.2)}, H p from rfl, ← evenLatticeEquiv.tsum_eq]
    refine tsum_congr fun uv => ?_
    simp only [evenLatticeEquiv, Equiv.coe_fn_mk, hH]
    rw [← zpow_add₀ hq0.ne', ← zpow_add₀ (by positivity), ← zpow_natCast, ← zpow_mul]
    congr 1; push_cast; ring
  · rw [show (∑' p : ↥({p : ℤ × ℤ | Even (p.1 + p.2)}ᶜ), H p) =
        ∑' p : {p : ℤ × ℤ // ¬ Even (p.1 + p.2)}, H p from rfl,
      ← p22R1_oddLatticeEquiv.tsum_eq]
    -- reorder the product and shift `u ↦ u - 1`
    have hswap := (Equiv.prodComm ℤ ℤ).tsum_eq
      (fun p : ℤ × ℤ => (q ^ 2) ^ (p.1 ^ 2 + p.1) * (q ^ 2) ^ (p.2 ^ 2))
    have hshift := (Equiv.prodCongr (Equiv.addRight (1 : ℤ)) (Equiv.refl ℤ)).tsum_eq
      (fun p : ℤ × ℤ => (q ^ 2) ^ (p.2 ^ 2 + p.2) * (q ^ 2) ^ (p.1 ^ 2))
    rw [← hswap]
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [← hshift]
    refine tsum_congr fun uv => ?_
    simp only [p22R1_oddLatticeEquiv, Equiv.coe_fn_mk, hH, Equiv.prodCongr_apply,
      Equiv.coe_refl, Equiv.coe_addRight, Prod.map_fst, Prod.map_snd, id_eq]
    rw [← zpow_add₀ hq0.ne', ← zpow_add₀ (by positivity), ← zpow_natCast, ← zpow_mul]
    congr 1; push_cast; ring

/-- Jacobi's identity for a real nome: `θ₃(q)⁴ = θ₄(q)⁴ + q P(q)⁴`, i.e. `θ₃⁴ = θ₂⁴ + θ₄⁴`. -/
lemma p22R1_jacobi_real {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Real.jacobiThetaThreeNullQ q ^ 4 = Real.jacobiThetaFourNullQ q ^ 4 + q * p22R1_P q ^ 4 := by
  have h1 := Real.jacobiThetaThreeNullQ_sq_add_jacobiThetaFourNullQ_sq hq0 hq1
  have h2 := p22R1_three_sq_sub_four_sq hq0 hq1
  have h3 := p22R1_P_sq hq0 hq1
  have e4 : p22R1_P q ^ 4 = (p22R1_P q ^ 2) ^ 2 := by ring
  rw [e4, h3]
  linear_combination (Real.jacobiThetaThreeNullQ q ^ 2 - Real.jacobiThetaFourNullQ q ^ 2) * h1 +
    2 * Real.jacobiThetaThreeNullQ (q ^ 2) ^ 2 * h2


lemma p22R1_two_eq_P (t : ℝ) :
    jacobiThetaTwoTau 0 (I * t) =
      ((Real.exp (-(π * t) / 4) * p22R1_P (Real.exp (-(π * t))) : ℝ) : ℂ) := by
  rw [jacobiThetaTwoTau, jacobiThetaThreeTau_eq_tsum, p22R1_P, ofReal_mul, ofReal_tsum,
    ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_zpow, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_int_mul,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]
  ring

end

/-- `θ₃(0|it)` as a real function of `t`. -/
noncomputable def p22R1_B (t : ℝ) : ℝ := Real.jacobiThetaThreeNullQ (Real.exp (-(π * t)))
/-- `θ₄(0|it)` as a real function of `t`. -/
noncomputable def p22R1_C (t : ℝ) : ℝ := Real.jacobiThetaFourNullQ (Real.exp (-(π * t)))

lemma p22R1_nome {t : ℝ} (ht : 0 < t) : 0 < Real.exp (-(π * t)) ∧ Real.exp (-(π * t)) < 1 :=
  ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])⟩

theorem p22R1_B_ge {t : ℝ} (ht : 0 < t) : 1 ≤ p22R1_B t :=
  Real.one_le_jacobiThetaThreeNullQ (p22R1_nome ht).1 (p22R1_nome ht).2

theorem p22R1_C_pos {t : ℝ} (ht : 0 < t) : 0 < p22R1_C t :=
  Real.jacobiThetaFourNullQ_pos (p22R1_nome ht).1 (p22R1_nome ht).2

theorem p22R1_three (t : ℝ) : jacobiThetaThreeTau 0 (I * t) = p22R1_B t :=
  jacobiThetaThreeTau_zero_I_mul t

theorem p22R1_four (t : ℝ) : jacobiThetaFourTau 0 (I * t) = p22R1_C t :=
  jacobiThetaFourTau_zero_I_mul t

lemma p22R1_cpow_half {t : ℝ} (ht : 0 ≤ t) : (t : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt t : ℂ) := by
  rw [Real.sqrt_eq_rpow, ofReal_cpow ht]; push_cast; ring_nf

lemma p22R1_neg_inv_I {t : ℝ} (ht : 0 < t) : -1 / (I * t) = I * ((1 / t : ℝ) : ℂ) := by
  have : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  push_cast
  field_simp
  rw [I_sq]

lemma p22R1_negI {t : ℝ} : -I * (I * t) = (t : ℂ) := by
  rw [← mul_assoc, neg_mul, I_mul_I]; ring

lemma p22R1_im_pos {t : ℝ} (ht : 0 < t) : 0 < (I * (t : ℂ)).im := by simpa using ht

/-- `θ₃(0|i/t) = √t θ₃(0|it)`. -/
lemma p22R1_B_inv {t : ℝ} (ht : 0 < t) : p22R1_B (1 / t) = Real.sqrt t * p22R1_B t := by
  have h := DLMF.Theta.jacobiThetaThreeTau_neg_inv (p22R1_im_pos ht) 0
  rw [p22R1_negI, p22R1_neg_inv_I ht, p22R1_cpow_half ht.le, p22R1_three] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    exp_zero, one_mul, zero_mul] at h
  rw [p22R1_three] at h
  exact_mod_cast h.symm

/-- `θ₂(0|it) = θ₄(0|i/t)/√t`. -/
theorem p22R1_two {t : ℝ} (ht : 0 < t) :
    jacobiThetaTwoTau 0 (I * t) = ((p22R1_C (1 / t) / Real.sqrt t : ℝ) : ℂ) := by
  have h := DLMF.Theta.jacobiThetaTwoTau_neg_inv (p22R1_im_pos ht) 0
  rw [p22R1_negI, p22R1_neg_inv_I ht, p22R1_cpow_half ht.le] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    exp_zero, one_mul, zero_mul] at h
  rw [p22R1_four] at h
  have hs : (Real.sqrt t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ht).ne'
  push_cast
  rw [← h]; field_simp


/-- `θ₂(0|it)` as a real function, `θ₄(0|i/t)/√t`. -/
noncomputable def p22R1_A (t : ℝ) : ℝ := p22R1_C (1 / t) / Real.sqrt t

theorem p22R1_A_pos {t : ℝ} (ht : 0 < t) : 0 < p22R1_A t :=
  div_pos (p22R1_C_pos (by positivity)) (Real.sqrt_pos.mpr ht)

/-- Jacobi's identity on the imaginary axis: `B⁴ = A⁴ + C⁴`. -/
theorem p22R1_fourth {t : ℝ} (ht : 0 < t) :
    p22R1_B t ^ 4 = p22R1_A t ^ 4 + p22R1_C t ^ 4 := by
  have h := p22R1_jacobi_real (p22R1_nome ht).1 (p22R1_nome ht).2
  have hA : p22R1_A t = Real.exp (-(π * t) / 4) * p22R1_P (Real.exp (-(π * t))) := by
    have e := (p22R1_two ht).symm.trans (p22R1_two_eq_P t)
    exact_mod_cast e
  have he : Real.exp (-(π * t) / 4) ^ 4 = Real.exp (-(π * t)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [p22R1_B, p22R1_C, h, hA, mul_pow, he]
  ring

lemma p22R1_A_inv {t : ℝ} (ht : 0 < t) : p22R1_A (1 / t) = p22R1_C t * Real.sqrt t := by
  rw [p22R1_A, one_div_one_div, Real.sqrt_div' _ ht.le, Real.sqrt_one]
  field_simp

lemma p22R1_B_inv' {t : ℝ} (ht : 0 < t) : p22R1_B t = Real.sqrt (1 / t) * p22R1_B (1 / t) := by
  have h := p22R1_B_inv (t := 1 / t) (by positivity)
  rwa [one_div_one_div] at h

/-- `ρ(t) = θ₂²(0|it)/θ₃²(0|it)`. -/
noncomputable def p22R1_rho (t : ℝ) : ℝ := (p22R1_A t / p22R1_B t) ^ 2

lemma p22R1_rho_inv {t : ℝ} (ht : 0 < t) :
    p22R1_rho (1 / t) = (p22R1_C t / p22R1_B t) ^ 2 := by
  rw [p22R1_rho, p22R1_A_inv ht, p22R1_B_inv ht]
  have := Real.sqrt_pos.mpr ht
  have := p22R1_B_ge ht
  congr 1
  field_simp

lemma p22R1_continuousOn_B : ContinuousOn p22R1_B (Set.Ioi 0) := by
  intro t ht
  have h : ContinuousAt (fun s : ℝ => jacobiThetaThreeTau 0 (I * s)) t := by
    have h1 : ContinuousAt (fun τ => jacobiTheta₂ (0 / π) τ) (I * t) :=
      (differentiableAt_jacobiTheta₂_snd _ (p22R1_im_pos ht)).continuousAt
    exact h1.comp (f := fun s : ℝ => I * (s : ℂ)) (by fun_prop)
  have h2 := (Complex.continuous_re.continuousAt).comp h
  refine (h2.congr (Filter.Eventually.of_forall fun s => ?_)).continuousWithinAt
  simp [p22R1_three]

lemma p22R1_continuousOn_C : ContinuousOn p22R1_C (Set.Ioi 0) := by
  intro t ht
  have h : ContinuousAt (fun s : ℝ => jacobiThetaFourTau 0 (I * s)) t := by
    have h1 : ContinuousAt (fun τ => jacobiTheta₂ ((0 + π / 2) / π) τ) (I * t) :=
      (differentiableAt_jacobiTheta₂_snd _ (p22R1_im_pos ht)).continuousAt
    exact h1.comp (f := fun s : ℝ => I * (s : ℂ)) (by fun_prop)
  have h2 := (Complex.continuous_re.continuousAt).comp h
  refine (h2.congr (Filter.Eventually.of_forall fun s => ?_)).continuousWithinAt
  simp [p22R1_four]

lemma p22R1_continuousOn_rho : ContinuousOn p22R1_rho (Set.Ioi 0) := by
  have hC' : ContinuousOn (fun t => p22R1_C (1 / t)) (Set.Ioi 0) :=
    p22R1_continuousOn_C.comp (continuousOn_const.div continuousOn_id fun t ht => ht.ne')
      fun t ht => by simp only [Set.mem_Ioi] at ht ⊢; positivity
  have hA : ContinuousOn p22R1_A (Set.Ioi 0) :=
    hC'.div Real.continuous_sqrt.continuousOn fun t ht => (Real.sqrt_pos.mpr ht).ne'
  exact (hA.div p22R1_continuousOn_B fun t ht => by
    have := p22R1_B_ge ht; positivity).pow 2

lemma p22R1_tendsto_nome : Tendsto (fun t : ℝ => Real.exp (-(π * t))) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun t => Real.exp_pos _⟩
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
    (Tendsto.const_mul_atTop Real.pi_pos tendsto_id))

lemma p22R1_tendsto_CB : Tendsto (fun t => p22R1_C t / p22R1_B t) atTop (𝓝 1) := by
  have h3 := Real.tendsto_jacobiThetaThreeNullQ.comp p22R1_tendsto_nome
  have h4 := Real.tendsto_jacobiThetaFourNullQ.comp p22R1_tendsto_nome
  have h := h4.div h3 one_ne_zero
  rw [div_one] at h
  exact h

/-- Every `0 < k < 1` is `θ₂²(0|it)/θ₃²(0|it)` for some `t > 0`. -/
theorem p22R1_exists_rho {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    ∃ t : ℝ, 0 < t ∧ p22R1_rho t = k := by
  have hev1 : ∀ᶠ T in atTop, k < (p22R1_C T / p22R1_B T) ^ 2 := by
    have := (p22R1_tendsto_CB.pow 2)
    simp only [one_pow] at this
    exact this.eventually (lt_mem_nhds (by nlinarith))
  have hev2 : ∀ᶠ T in atTop, 1 - (p22R1_C T / p22R1_B T) ^ 4 < k ^ 2 := by
    have := ((p22R1_tendsto_CB.pow 4).const_sub 1)
    simp only [one_pow, sub_self] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  obtain ⟨T, h1, h2, hT⟩ := (hev1.and (hev2.and (eventually_gt_atTop 1))).exists
  have hT0 : 0 < T := by linarith
  have hle : 1 / T ≤ T := by
    rw [div_le_iff₀ hT0]; nlinarith
  have hcont : ContinuousOn p22R1_rho (Set.Icc (1 / T) T) :=
    p22R1_continuousOn_rho.mono fun t ht => by
      simp only [Set.mem_Ioi]; exact lt_of_lt_of_le (by positivity) ht.1
  have hρT : p22R1_rho T < k := by
    have hf := p22R1_fourth hT0
    have hB := p22R1_B_ge hT0
    have hsq : p22R1_rho T ^ 2 = 1 - (p22R1_C T / p22R1_B T) ^ 4 := by
      rw [p22R1_rho]; field_simp; linarith
    have hρ0 : 0 ≤ p22R1_rho T := sq_nonneg _
    nlinarith
  have hρT' : k < p22R1_rho (1 / T) := by rw [p22R1_rho_inv hT0]; exact h1
  obtain ⟨t, ht, hte⟩ := intermediate_value_Icc' hle hcont ⟨hρT.le, hρT'.le⟩
  exact ⟨t, lt_of_lt_of_le (by positivity) ht.1, hte⟩


/-- The real case of DLMF 22.2.2 at `τ = it`: `k = ρ(t) = θ₂²/θ₃²(0|it) ∈ (0, 1)`,
`τ(k) = it`, the three relations at `τ = it`, and `K(k) = (π/2)θ₃²`, `K'(k) = t K(k)`. -/
theorem p22R1_real_at {t : ℝ} (ht : 0 < t) :
    0 < p22R1_rho t ∧ p22R1_rho t < 1 ∧ jacobiTauk (p22R1_rho t) = I * t ∧
      jacobiModulusTau (I * t) = p22R1_rho t ∧
      jacobiComodulusTau (I * t) = jacobiComodulusk (p22R1_rho t) ∧
      compEllIntKTau (I * t) = compEllIntKk (p22R1_rho t) ∧
      Real.compEllIntKm (p22R1_rho t ^ 2) = π / 2 * p22R1_B t ^ 2 ∧
      Real.compEllIntKm (1 - p22R1_rho t ^ 2) = π / 2 * t * p22R1_B t ^ 2 := by
  set k := p22R1_rho t with hk
  have hρ : p22R1_rho t = k := rfl
  have hA := p22R1_A_pos ht
  have hB := p22R1_B_ge ht
  have hB0 : 0 < p22R1_B t := by linarith
  have hC := p22R1_C_pos ht
  have hf := p22R1_fourth ht
  have hA' : jacobiThetaTwoTau 0 (I * t) = p22R1_A t := p22R1_two ht
  -- `k² = 1 - (C/B)⁴` and `1 - k² = (C/B)⁴`
  have hk2 : k ^ 2 = 1 - (p22R1_C t / p22R1_B t) ^ 4 := by
    rw [← hρ, p22R1_rho]; field_simp; linarith
  have hk0 : 0 < k := by rw [hk, p22R1_rho]; positivity
  have hk1 : k < 1 := by
    have : k ^ 2 < 1 := by
      rw [hk2]; have : 0 < (p22R1_C t / p22R1_B t) ^ 4 := by positivity
      linarith
    nlinarith
  have hKm (s : ℝ) (hs : 0 < s) : Real.compEllIntKm (1 - (p22R1_C s / p22R1_B s) ^ 4) =
      π / 2 * p22R1_B s ^ 2 :=
    Real.compEllIntKm_eq_jacobiThetaThreeNullQ (p22R1_nome hs).1 (p22R1_nome hs).2
  have hKk : compEllIntKk k = π / 2 * (p22R1_B t : ℂ) ^ 2 := by
    rw [compEllIntKk_ofReal (by nlinarith), hk2, hKm t ht]
    push_cast; ring
  have hKmk : Real.compEllIntKm (k ^ 2) = π / 2 * p22R1_B t ^ 2 := by rw [hk2, hKm t ht]
  have hKmk' : Real.compEllIntKm (1 - k ^ 2) = π / 2 * t * p22R1_B t ^ 2 := by
    have ht' : (0 : ℝ) < 1 / t := by positivity
    have e : 1 - k ^ 2 = 1 - (p22R1_C (1 / t) / p22R1_B (1 / t)) ^ 4 := by
      have h1 : p22R1_C (1 / t) = p22R1_A t * Real.sqrt t := by
        rw [p22R1_A]; field_simp [(Real.sqrt_pos.mpr ht).ne']
      rw [h1, p22R1_B_inv ht, ← hρ, p22R1_rho]
      have := Real.sqrt_pos.mpr ht
      field_simp
    rw [e, hKm _ ht', p22R1_B_inv ht, mul_pow, Real.sq_sqrt ht.le]
    ring
  have hKpk : compEllIntKpk k = π / 2 * t * (p22R1_B t : ℂ) ^ 2 := by
    have ht' : (0 : ℝ) < 1 / t := by positivity
    have e : 1 - k ^ 2 = 1 - (p22R1_C (1 / t) / p22R1_B (1 / t)) ^ 4 := by
      have h1 : p22R1_C (1 / t) = p22R1_A t * Real.sqrt t := by
        rw [p22R1_A]; field_simp [(Real.sqrt_pos.mpr ht).ne']
      rw [h1, p22R1_B_inv ht, ← hρ, p22R1_rho]
      have := Real.sqrt_pos.mpr ht
      field_simp
    rw [compEllIntKpk_ofReal (by positivity), e, hKm _ ht', p22R1_B_inv ht, mul_pow,
      Real.sq_sqrt ht.le]
    push_cast
    ring
  have hKne : compEllIntKk k ≠ 0 := by
    rw [hKk]
    exact mul_ne_zero (div_ne_zero pi_ne_zero' two_ne_zero)
      (pow_ne_zero _ (ofReal_ne_zero.mpr hB0.ne'))
  refine ⟨hk0, hk1, ?_, ?_, ?_, ?_, hKmk, hKmk'⟩
  · rw [jacobiTauk, hKpk, hKk]
    have : (p22R1_B t : ℂ) ≠ 0 := ofReal_ne_zero.mpr hB0.ne'
    have := pi_ne_zero'
    field_simp
  · rw [jacobiModulusTau, hA', p22R1_three, ← hρ, p22R1_rho]
    push_cast; ring
  · rw [jacobiComodulusTau, jacobiComodulusk, p22R1_four, p22R1_three,
      show (1 : ℂ) - (k : ℂ) ^ 2 = ((1 - k ^ 2 : ℝ) : ℂ) by push_cast; ring,
      p22R1_cpow_half (by nlinarith), hk2,
      show 1 - (1 - (p22R1_C t / p22R1_B t) ^ 4) = ((p22R1_C t / p22R1_B t) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
    push_cast; ring
  · rw [compEllIntKTau, p22R1_three, hKk]

/-- The real case of DLMF 22.2.2: for `0 < k < 1`, `τ(k) = it` with `t > 0` and the three
relations hold at `τ = it`. -/
lemma p22R1_inversion_real {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    ∃ t : ℝ, 0 < t ∧ jacobiTauk k = I * t ∧ jacobiModulusTau (I * t) = k ∧
      jacobiComodulusTau (I * t) = jacobiComodulusk k ∧ compEllIntKTau (I * t) = compEllIntKk k := by
  obtain ⟨t, ht, hρ⟩ := p22R1_exists_rho hk0 hk1
  obtain ⟨-, -, h1, h2, h3, h4, -⟩ := p22R1_real_at ht
  rw [hρ] at h1 h2 h3 h4
  exact ⟨t, ht, h1, h2, h3, h4⟩

/-- Holomorphy of the parametric integrals `∫₀^{π/2} (1 - c(k) sin²θ)^{-1/2} dθ`. -/
lemma p22R1_differentiableOn_integral {U : Set ℂ} (hU : IsOpen U) {c : ℂ → ℂ}
    (hc : Differentiable ℂ c)
    (hslit : ∀ k ∈ U, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 1 - c k * (s : ℂ) ∈ slitPlane) :
    DifferentiableOn ℂ
      (fun k => ∫ θ in (0 : ℝ)..(π / 2), (1 - c k * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) U := by
  have hsq (θ : ℝ) : (Real.sin θ : ℂ) ^ 2 = ((Real.sin θ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hsl (k : ℂ) (hk : k ∈ U) (θ : ℝ) : 1 - c k * (Real.sin θ : ℂ) ^ 2 ∈ slitPlane := by
    rw [hsq]; exact hslit k hk _ (sq_nonneg _) (Real.sin_sq_le_one θ)
  refine Complex.differentiableOn_intervalIntegral_of_locally_dominated hU 0 (π / 2)
    (fun k hk => ?_) (Eventually.of_forall fun θ => ?_) (fun k hk => ?_)
  · exact (Continuous.cpow (by fun_prop) continuous_const (hsl k hk)).aestronglyMeasurable
  · intro k hk
    exact ((((hc k).mul (differentiableAt_const _)).const_sub 1).cpow_const
      (hsl k hk θ)).differentiableWithinAt
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU k hk
    have hsub : Metric.closedBall k (ε / 2) ⊆ U :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    have hcpt : IsCompact (Metric.closedBall k (ε / 2) ×ˢ Set.Icc (0 : ℝ) 1) :=
      (isCompact_closedBall _ _).prod isCompact_Icc
    have hcont : ContinuousOn (fun p : ℂ × ℝ => (1 - c p.1 * (p.2 : ℂ)) ^ (-(1 / 2 : ℂ)))
        (Metric.closedBall k (ε / 2) ×ˢ Set.Icc (0 : ℝ) 1) := by
      intro p hp
      have hcc : Continuous c := hc.continuous
      refine ContinuousAt.continuousWithinAt (ContinuousAt.cpow (by fun_prop)
        continuousAt_const (hslit p.1 (hsub hp.1) p.2 hp.2.1 hp.2.2))
    obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn hcont
    refine ⟨Metric.closedBall k (ε / 2), Metric.closedBall_mem_nhds _ (by linarith),
      fun _ => M, ?_, Eventually.of_forall fun θ y hy => ?_⟩
    · rw [Set.uIoc_of_le (by positivity)]
      exact (integrableOn_Icc_iff_integrableOn_Ioc (μ := volume)).mp
        continuous_const.integrableOn_Icc
    · rw [hsq]
      exact hM (y, Real.sin θ ^ 2) ⟨hy, sq_nonneg _, Real.sin_sq_le_one θ⟩


/-- `K(k) ≠ 0` on `jacobiModulusDomain`. -/
theorem p22R1_compEllIntKk_ne_zero {k : ℂ} (hk : k ∈ jacobiModulusDomain) : compEllIntKk k ≠ 0 := by
  intro h
  have := jacobiTauk_im_pos hk
  simp [jacobiTauk, h] at this

theorem p22R1_domain_eq :
    jacobiModulusDomain = {k : ℂ | 0 < k.re} ∩ {k : ℂ | 1 - k ^ 2 ∈ slitPlane} := by
  ext k
  simp only [jacobiModulusDomain, Set.mem_ofPred_eq, Set.mem_inter_iff, mem_slitPlane_iff]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, ?_⟩
    by_cases him : k.im = 0
    · left; have := h1 him; simp [pow_two, him]; nlinarith
    · right; simp [pow_two]; intro h
      have : k.re * k.im = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · exact him h'
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun him => ?_⟩
    rcases h1 with h1 | h1
    · simp [pow_two, him] at h1; nlinarith
    · simp [pow_two, him] at h1

theorem p22R1_isOpen_domain : IsOpen jacobiModulusDomain := by
  rw [p22R1_domain_eq]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_slitPlane.preimage (by fun_prop))

lemma p22R1_half_mem : (1 / 2 : ℂ) ∈ jacobiModulusDomain := by
  refine ⟨by norm_num, fun _ => by norm_num⟩

theorem p22R1_ofReal_mem {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : (x : ℂ) ∈ jacobiModulusDomain :=
  ⟨by simpa using h0, fun _ => by simpa using h1⟩

lemma p22R1_isPreconnected_domain : IsPreconnected jacobiModulusDomain := by
  refine (StarConvex.isPathConnected (a := (1 / 2 : ℂ)) ?_ p22R1_half_mem).isConnected.isPreconnected
  intro k hk a b ha hb hab
  obtain ⟨hk0, hk1⟩ := hk
  have hre : (a • (1 / 2 : ℂ) + b • k).re = a / 2 + b * k.re := by simp; ring
  have him : (a • (1 / 2 : ℂ) + b • k).im = b * k.im := by simp
  refine ⟨?_, fun h => ?_⟩
  · rw [hre]
    rcases hb.eq_or_lt with rfl | hb'
    · simp at hab; subst hab; norm_num
    · nlinarith
  · rw [hre]
    rw [him] at h
    rcases hb.eq_or_lt with rfl | hb'
    · simp at hab; subst hab; norm_num
    · have : k.im = 0 := by
        rcases mul_eq_zero.mp h with h | h
        · linarith
        · exact h
      have := hk1 this
      nlinarith

lemma p22R1_differentiableOn_K : DifferentiableOn ℂ compEllIntKk jacobiModulusDomain :=
  p22R1_differentiableOn_integral (c := fun k => k ^ 2) p22R1_isOpen_domain (by fun_prop)
    fun k hk s hs0 hs1 => (p22R1_mem_slitPlane (p22R1_sq_of_mem_domain hk) hs0 hs1).2

lemma p22R1_differentiableOn_Kp : DifferentiableOn ℂ compEllIntKpk jacobiModulusDomain :=
  p22R1_differentiableOn_integral (c := fun k => 1 - k ^ 2) p22R1_isOpen_domain (by fun_prop)
    fun k hk s hs0 hs1 => (p22R1_mem_slitPlane (p22R1_sq_of_mem_domain hk) hs0 hs1).1

lemma p22R1_differentiableOn_tau : DifferentiableOn ℂ jacobiTauk jacobiModulusDomain :=
  ((differentiableOn_const I).mul p22R1_differentiableOn_Kp).div p22R1_differentiableOn_K
    fun _ hk => p22R1_compEllIntKk_ne_zero hk

theorem p22R1_differentiableAt_three {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (fun τ => jacobiThetaThreeTau 0 τ) τ :=
  differentiableAt_jacobiTheta₂_snd _ hτ

lemma p22R1_differentiableAt_four {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (fun τ => jacobiThetaFourTau 0 τ) τ :=
  differentiableAt_jacobiTheta₂_snd _ hτ

theorem p22R1_differentiableAt_two {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (fun τ => jacobiThetaTwoTau 0 τ) τ := by
  have h : DifferentiableAt ℂ (fun σ => jacobiTheta₂ ((0 + π * σ / 2) / π) σ) τ := by
    have h1 := (hasFDerivAt_jacobiTheta₂ ((0 + π * τ / 2) / π) hτ).differentiableAt
    have h2 : DifferentiableAt ℂ (fun σ : ℂ => ((0 + π * σ / 2) / π, σ)) τ := by fun_prop
    exact h1.comp (f := fun σ : ℂ => ((0 + π * σ / 2) / π, σ)) τ h2
  exact (by fun_prop : DifferentiableAt ℂ (fun σ : ℂ => cexp (π * I * σ / 4 + I * 0)) τ).mul h

/-- Composition of a theta constant with `τ(k)` is holomorphic on the domain. -/
theorem p22R1_differentiableOn_comp {f : ℂ → ℂ}
    (hf : ∀ τ : ℂ, 0 < τ.im → DifferentiableAt ℂ f τ) :
    DifferentiableOn ℂ (fun k => f (jacobiTauk k)) jacobiModulusDomain := fun k hk =>
  ((hf _ (jacobiTauk_im_pos hk)).comp k
    (p22R1_differentiableOn_tau.differentiableAt
      (p22R1_isOpen_domain.mem_nhds hk))).differentiableWithinAt

/-- Identity theorem on the domain from agreement on `(0, 1)`. -/
theorem p22R1_eqOn_of_real {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f jacobiModulusDomain)
    (hg : DifferentiableOn ℂ g jacobiModulusDomain)
    (hreal : ∀ x : ℝ, 0 < x → x < 1 → f x = g x) : Set.EqOn f g jacobiModulusDomain := by
  refine (hf.analyticOnNhd p22R1_isOpen_domain).eqOn_of_preconnected_of_frequently_eq
    (hg.analyticOnNhd p22R1_isOpen_domain) p22R1_isPreconnected_domain p22R1_half_mem ?_
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (1 / 2 : ℝ)) (𝓝[≠] (1 / 2 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun x hx => ?_⟩
    · have := (Complex.continuous_ofReal.tendsto (1 / 2 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := {(1 / 2 : ℝ)}ᶜ))
      simpa using this
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
      intro h; apply hx; have := congrArg Complex.re h; simpa using this
  refine ht.frequently (Eventually.frequently ?_)
  filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1))] with x hx
  exact hreal x hx.1 hx.2

end p22R1Inversion

/-- **DLMF 22.2.2.** For `k ∈ jacobiModulusDomain` and `τ = iK'(k)/K(k)`:
`k = θ₂²(0|τ)/θ₃²(0|τ)`, `k' = θ₄²(0|τ)/θ₃²(0|τ)` with the principal `k' = √(1-k²)`, and
`K(k) = (π/2)θ₃²(0|τ)`. The sign of `k` requires `Re k > 0`; the right-hand sides depend on
`k²` only. -/
@[dlmf 22.2.E2 "domain: Re k > 0, k ∉ [1, ∞); fixes the sign of k and of k'"]
theorem jacobi_inversion_k {k : ℂ} (hk : k ∈ jacobiModulusDomain) :
    jacobiModulusTau (jacobiTauk k) = k ∧
      jacobiComodulusTau (jacobiTauk k) = jacobiComodulusk k ∧
      compEllIntKTau (jacobiTauk k) = compEllIntKk k := by
  have h3 := p22R1_differentiableOn_comp fun τ hτ => p22R1_differentiableAt_three hτ
  have h2 := p22R1_differentiableOn_comp fun τ hτ => p22R1_differentiableAt_two hτ
  have h4 := p22R1_differentiableOn_comp fun τ hτ => p22R1_differentiableAt_four hτ
  have h3ne : ∀ k ∈ jacobiModulusDomain, jacobiThetaThreeTau 0 (jacobiTauk k) ^ 2 ≠ 0 :=
    fun k hk => pow_ne_zero _ (je22a_thetaThree_zero_ne_zero (jacobiTauk_im_pos hk))
  refine ⟨?_, ?_, ?_⟩
  · refine p22R1_eqOn_of_real (f := fun k => jacobiModulusTau (jacobiTauk k)) (g := id)
      ((h2.pow 2).div (h3.pow 2) h3ne) differentiableOn_id (fun x hx0 hx1 => ?_) hk
    obtain ⟨t, -, ht, hm, -, -⟩ := p22R1_inversion_real hx0 hx1
    simp only [id, ht, hm]
  · refine p22R1_eqOn_of_real (f := fun k => jacobiComodulusTau (jacobiTauk k))
      (g := jacobiComodulusk) ((h4.pow 2).div (h3.pow 2) h3ne) ?_ (fun x hx0 hx1 => ?_) hk
    · intro k hk
      rw [p22R1_domain_eq] at hk
      exact ((by fun_prop : DifferentiableAt ℂ (fun k : ℂ => 1 - k ^ 2) k).cpow_const
        hk.2).differentiableWithinAt
    · obtain ⟨t, -, ht, -, hc, -⟩ := p22R1_inversion_real hx0 hx1
      simp only [ht, hc]
  · refine p22R1_eqOn_of_real (f := fun k => compEllIntKTau (jacobiTauk k))
      (g := compEllIntKk) ((differentiableOn_const _).mul (h3.pow 2))
      p22R1_differentiableOn_K (fun x hx0 hx1 => ?_) hk
    obtain ⟨t, -, ht, -, -, hK⟩ := p22R1_inversion_real hx0 hx1
    simp only [ht, hK]

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
theorem jacobiZetak_neg (z k : ℂ) : jacobiZetak (-z) k = -jacobiZetak z k := by
  simp only [jacobiZetak]; ring

/-- The normalized theta functions: `θ_s` is odd, `θ_c, θ_d, θ_n` are even. -/
theorem jacobiLetterTheta_neg (p : JacobiLetter) (ζ τ : ℂ) :
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

/-! ### Holomorphy of the normalized theta functions in `(ζ, τ)` -/
/-- Quotients of holomorphic functions on `ℂ × ℂ`. -/
lemma p22R1_differentiableAt_div {f g : ℂ × ℂ → ℂ} {x : ℂ × ℂ} (hf : DifferentiableAt ℂ f x)
    (hg : DifferentiableAt ℂ g x) (h : g x ≠ 0) : DifferentiableAt ℂ (fun y => f y / g y) x := by
  exact (hf.mul (hg.inv h)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => by simp [div_eq_mul_inv])

/-- `(ζ, τ) ↦ θ₃(f(ζ, τ)|τ)` is holomorphic where `f` is and `Im τ > 0`. -/
lemma p22R1_differentiableAt_three_comp {f : ℂ × ℂ → ℂ} {x : ℂ × ℂ} (hf : DifferentiableAt ℂ f x)
    (hx : 0 < x.2.im) : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaThreeTau (f y) y.2) x := by
  have h1 := (hasFDerivAt_jacobiTheta₂ (f x / π) hx).differentiableAt
  have h2 : DifferentiableAt ℂ (fun y : ℂ × ℂ => (f y / π, y.2)) x :=
    (p22R1_differentiableAt_div hf (differentiableAt_const _) pi_ne_zero').prodMk
      differentiableAt_snd
  exact h1.comp (f := fun y : ℂ × ℂ => (f y / π, y.2)) x h2

lemma p22R1_differentiableAt_two_comp {f : ℂ × ℂ → ℂ} {x : ℂ × ℂ} (hf : DifferentiableAt ℂ f x)
    (hx : 0 < x.2.im) : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaTwoTau (f y) y.2) x := by
  have h := p22R1_differentiableAt_three_comp (f := fun y => f y + π * y.2 / 2)
    (hf.add (p22R1_differentiableAt_div (differentiableAt_snd.const_mul (π : ℂ))
      (differentiableAt_const _) two_ne_zero)) hx
  have he : DifferentiableAt ℂ (fun y : ℂ × ℂ => cexp (π * I * y.2 / 4 + I * f y)) x :=
    ((p22R1_differentiableAt_div (differentiableAt_snd.const_mul (π * I : ℂ))
      (differentiableAt_const _) (by norm_num : (4 : ℂ) ≠ 0)).add (hf.const_mul I)).cexp
  exact he.mul h

/-- The normalized theta functions are jointly holomorphic in `(ζ, τ)` for `Im τ > 0`. -/
theorem p22R1_differentiableAt_letterTheta (p : JacobiLetter) {x : ℂ × ℂ} (hx : 0 < x.2.im) :
    DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiLetterTheta p y.1 y.2) x := by
  have c2 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaTwoTau 0 y.2) x :=
    p22R1_differentiableAt_two_comp (f := fun _ => 0) (differentiableAt_const _) hx
  have c3 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaThreeTau 0 y.2) x :=
    p22R1_differentiableAt_three_comp (f := fun _ => 0) (differentiableAt_const _) hx
  have c4 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaFourTau 0 y.2) x :=
    p22R1_differentiableAt_three_comp (f := fun _ => 0 + π / 2) (differentiableAt_const _) hx
  have d2 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaTwoTau y.1 y.2) x :=
    p22R1_differentiableAt_two_comp (f := fun y => y.1) differentiableAt_fst hx
  have d3 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaThreeTau y.1 y.2) x :=
    p22R1_differentiableAt_three_comp (f := fun y => y.1) differentiableAt_fst hx
  have d4 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaFourTau y.1 y.2) x :=
    p22R1_differentiableAt_three_comp (f := fun y => y.1 + π / 2)
      (differentiableAt_fst.add_const _) hx
  have d1 : DifferentiableAt ℂ (fun y : ℂ × ℂ => jacobiThetaOneTau y.1 y.2) x := by
    have h := (p22R1_differentiableAt_two_comp (f := fun y => y.1 + π / 2)
      (differentiableAt_fst.add_const _) hx).const_mul (-1 : ℂ)
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp [jacobiThetaOneTau]
  have n2 := je22a_thetaTwo_zero_ne_zero hx
  have n3 := je22a_thetaThree_zero_ne_zero hx
  have n4 := je22a_thetaFour_zero_ne_zero hx
  cases p
  · exact (p22R1_differentiableAt_div c3 (c2.mul c4) (mul_ne_zero n2 n4)).mul d1
  · exact p22R1_differentiableAt_div d2 c2 n2
  · exact p22R1_differentiableAt_div d3 c3 n3
  · exact p22R1_differentiableAt_div d4 c4 n4

/-- DLMF 22.2.11: `pq(z, k) = θ_p(z|τ)/θ_q(z|τ)` in Neville's theta functions,
`τ = iK'/K` (22.2.12), for distinct letters. This needs Jacobi's `θ₁'(0) = θ₂θ₃θ₄(0)`
(DLMF 20.4.6). -/
@[dlmf 22.2.E11]
theorem jacobiPQk_eq_neville {k : ℂ} (hk : k ∈ jacobiModulusDomain) {p q : JacobiLetter}
    (hpq : p ≠ q) (z : ℂ) :
    jacobiPQk p q z k = jacobiNevilleTau p z (jacobiTauk k) / jacobiNevilleTau q z (jacobiTauk k) :=
        by
  have hτ := jacobiTauk_im_pos hk
  have hK := (jacobi_inversion_k hk).2.2
  have h2 := je22a_thetaTwo_zero_ne_zero hτ
  have h3 := je22a_thetaThree_zero_ne_zero hτ
  have h4 := je22a_thetaFour_zero_ne_zero hτ
  have hζ : jacobiZetak z k = z / jacobiThetaThreeTau 0 (jacobiTauk k) ^ 2 := by
    rw [jacobiZetak, ← hK, compEllIntKTau]
    field_simp [pi_ne_zero']
  have key : ∀ r : JacobiLetter, jacobiNevilleTau r z (jacobiTauk k) =
      jacobiLetterTheta r (jacobiZetak z k) (jacobiTauk k) := by
    intro r
    rw [hζ]
    cases r
    · have hd := DLMF.Theta.jacobiThetaOneDerivNullTau_eq_mul hτ
      simp only [jacobiNevilleTau, jacobiLetterTheta]
      rw [show deriv (fun w => jacobiThetaOneTau w (jacobiTauk k)) 0 =
        DLMF.Theta.jacobiThetaOneDerivNullTau (jacobiTauk k) from rfl, hd]
      simp only [DLMF.Theta.jacobiThetaTwoNullTau, DLMF.Theta.jacobiThetaThreeNullTau,
        DLMF.Theta.jacobiThetaFourNullTau]
      field_simp
    all_goals rfl
  rw [key, key, jacobiPQk, jacobiGlaisher]
  simp only [hpq, ↓reduceIte]

/-- DLMF §22.2: for fixed `z` each `pq(z, k)` is meromorphic in `k` (on
`jacobiModulusDomain`, where the principal-branch definition is used). -/
@[dlmf 22.2]
theorem jacobiPQk_meromorphicOn_modulus (p q : JacobiLetter) (z : ℂ) :
    MeromorphicOn (fun k => jacobiPQk p q z k) jacobiModulusDomain := by
  intro k hk
  have hU := p22R1_isOpen_domain.mem_nhds hk
  have hτ : DifferentiableAt ℂ jacobiTauk k := p22R1_differentiableOn_tau.differentiableAt hU
  have hK : DifferentiableAt ℂ compEllIntKk k := p22R1_differentiableOn_K.differentiableAt hU
  have hζ : DifferentiableAt ℂ (fun k => jacobiZetak z k) k :=
    (differentiableAt_const _).div (hK.const_mul _)
      (mul_ne_zero two_ne_zero (p22R1_compEllIntKk_ne_zero hk))
  have hpair : DifferentiableAt ℂ (fun k => (jacobiZetak z k, jacobiTauk k)) k := hζ.prodMk hτ
  -- each letter theta along the curve is holomorphic near `k`
  have hl : ∀ r : JacobiLetter, ∀ᶠ k' in nhds k,
      DifferentiableAt ℂ (fun k => jacobiLetterTheta r (jacobiZetak z k) (jacobiTauk k)) k' := by
    intro r
    filter_upwards [hU] with k' hk'
    have hU' := p22R1_isOpen_domain.mem_nhds hk'
    have hζ' : DifferentiableAt ℂ (fun k => jacobiZetak z k) k' :=
      (differentiableAt_const _).div
        ((p22R1_differentiableOn_K.differentiableAt hU').const_mul _)
        (mul_ne_zero two_ne_zero (p22R1_compEllIntKk_ne_zero hk'))
    exact (p22R1_differentiableAt_letterTheta r (x := (jacobiZetak z k', jacobiTauk k'))
      (jacobiTauk_im_pos hk')).comp (f := fun k => (jacobiZetak z k, jacobiTauk k)) k'
      (hζ'.prodMk (p22R1_differentiableOn_tau.differentiableAt hU'))
  have ha : ∀ r : JacobiLetter,
      AnalyticAt ℂ (fun k => jacobiLetterTheta r (jacobiZetak z k) (jacobiTauk k)) k :=
    fun r => DifferentiableOn.analyticAt (s := {k' | DifferentiableAt ℂ
      (fun k => jacobiLetterTheta r (jacobiZetak z k) (jacobiTauk k)) k'})
      (fun _ h => h.differentiableWithinAt) (hl r)
  unfold jacobiPQk jacobiGlaisher
  by_cases hpq : p = q
  · simp only [hpq, ↓reduceIte]; exact analyticAt_const.meromorphicAt
  · simp only [hpq, ↓reduceIte]
    exact (ha p).meromorphicAt.div (ha q).meromorphicAt

/-! ### Reality on the real axis -/
/-- `conj θ₃(ζ|τ) = θ₃(conj ζ| -conj τ)`. -/
lemma p22R1_conj_three (ζ τ : ℂ) :
    (starRingEnd ℂ) (jacobiThetaThreeTau ζ τ) =
      jacobiThetaThreeTau ((starRingEnd ℂ) ζ) (-(starRingEnd ℂ) τ) := by
  rw [jacobiThetaThreeTau, jacobiTheta₂_conj, jacobiThetaThreeTau, map_div₀, conj_ofReal]

/-- `conj θ₄(ζ|τ) = θ₄(conj ζ| -conj τ)`. -/
lemma p22R1_conj_four (ζ τ : ℂ) :
    (starRingEnd ℂ) (jacobiThetaFourTau ζ τ) =
      jacobiThetaFourTau ((starRingEnd ℂ) ζ) (-(starRingEnd ℂ) τ) := by
  rw [jacobiThetaFourTau, p22R1_conj_three, jacobiThetaFourTau]
  simp [map_add, map_div₀, conj_ofReal, map_ofNat]

/-- `conj θ₂(ζ|τ) = θ₂(conj ζ| -conj τ)`. -/
lemma p22R1_conj_two (ζ τ : ℂ) :
    (starRingEnd ℂ) (jacobiThetaTwoTau ζ τ) =
      jacobiThetaTwoTau ((starRingEnd ℂ) ζ) (-(starRingEnd ℂ) τ) := by
  set ζ' := (starRingEnd ℂ) ζ
  set τ' := -(starRingEnd ℂ) τ
  conv_rhs => rw [← jacobiThetaTwoTau_neg, jacobiThetaTwoTau,
    show -ζ' + π * τ' / 2 = -(ζ' - π * τ' / 2) by ring, jacobiThetaThreeTau_neg]
  rw [jacobiThetaTwoTau, map_mul, ← exp_conj, p22R1_conj_three]
  congr 2
  · simp only [map_add, map_mul, map_div₀, conj_ofReal, conj_I, map_ofNat, ζ', τ']; ring
  · simp only [map_add, map_mul, map_div₀, conj_ofReal, map_ofNat, ζ', τ']; ring

/-- `conj θ₁(ζ|τ) = θ₁(conj ζ| -conj τ)`. -/
lemma p22R1_conj_one (ζ τ : ℂ) :
    (starRingEnd ℂ) (jacobiThetaOneTau ζ τ) =
      jacobiThetaOneTau ((starRingEnd ℂ) ζ) (-(starRingEnd ℂ) τ) := by
  rw [jacobiThetaOneTau, map_neg, p22R1_conj_two, jacobiThetaOneTau]
  simp [map_add, map_div₀, conj_ofReal, map_ofNat]

/-- Conjugation of the normalized theta functions. -/
lemma p22R1_conj_letterTheta (p : JacobiLetter) (ζ τ : ℂ) :
    (starRingEnd ℂ) (jacobiLetterTheta p ζ τ) =
      jacobiLetterTheta p ((starRingEnd ℂ) ζ) (-(starRingEnd ℂ) τ) := by
  have h0 : (starRingEnd ℂ) (0 : ℂ) = 0 := map_zero _
  cases p <;> simp only [jacobiLetterTheta, map_mul, map_div₀, p22R1_conj_one, p22R1_conj_two,
    p22R1_conj_three, p22R1_conj_four, h0]

/-- Conjugation of Glaisher's quotients. -/
lemma p22R1_conj_glaisher (p q : JacobiLetter) (ζ τ : ℂ) :
    (starRingEnd ℂ) (jacobiGlaisher p q ζ τ) =
      jacobiGlaisher p q ((starRingEnd ℂ) ζ) (-(starRingEnd ℂ) τ) := by
  unfold jacobiGlaisher
  split_ifs
  · simp
  · rw [map_div₀, p22R1_conj_letterTheta, p22R1_conj_letterTheta]

/-- DLMF §22.2: for `0 < k < 1` all twelve functions are real for real `z`.
(`k = 0, 1` are the limiting forms of §22.5(ii).) -/
@[dlmf 22.2]
theorem jacobiPQk_real {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (p q : JacobiLetter) (x : ℝ) :
    (jacobiPQk p q x k).im = 0 := by
  obtain ⟨t, -, ht, -⟩ := p22R1_inversion_real hk0 hk1
  have hK := compEllIntKk_ofReal (k := k) (by nlinarith)
  have hζ : jacobiZetak x k = ((π * x / (2 * Real.compEllIntKm (k ^ 2)) : ℝ) : ℂ) := by
    rw [jacobiZetak, hK]; push_cast; ring
  have hτ : -(starRingEnd ℂ) (I * t) = I * t := by simp
  rw [← conj_eq_iff_im, jacobiPQk, ht, hζ, p22R1_conj_glaisher, conj_ofReal, hτ]

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
