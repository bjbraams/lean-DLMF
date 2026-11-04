/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Basic.Theta
public import DLMF.EllipticIntegrals.Basic.Complete

/-!
# Theta-quotient definitions of Jacobian elliptic functions

DLMF §22.2 defines the twelve Jacobian elliptic functions `pq(z, k)` (Glaisher's notation:
`p, q ∈ {s, c, d, n}`, `pp = 1`) as quotients of theta functions with nome
`q = exp(-π K'(k)/K(k))` and argument `ζ = π z/(2K(k))`. This file gives these definitions in
lattice form (parameter `τ`) and in DLMF's literal modulus form.

## Main definitions

* `JacobiLetter`: the four Glaisher letters `s, c, d, n`; `JacobiLetter.index` gives the
  attached theta index.
* `jacobiLetterTheta`: the normalized theta functions of DLMF 22.2.4–22.2.9.
* `jacobiGlaisher`: Glaisher's quotient `pq = θ_p/θ_q` in the theta argument `ζ`.
* `completeEllipticKOfTau`, `completeEllipticKPrimeOfTau`, `jacobiModulusOfTau`,
  `jacobiComodulusOfTau`, `jacobiThetaArgumentOfTau`: `K`, `K'`, `k`, `k'` and `ζ` as functions of
  the lattice parameter (DLMF 22.2.2, 22.2.3, 22.2.12).
* `jacobiPQOfTau`: Glaisher's function `pq(z)` for the lattice parameter `τ`, with the named
  functions `jacobiSnOfTau`, …, `jacobiCsOfTau`.
* `jacobiComodulus`: `k' = √(1 - k²)`; `K(k)`, `K'(k)` are
  `DLMF.EllipticIntegrals.completeEllipticK`, `completeEllipticKPrime` (DLMF 19.2.8, 19.2.9).
* `jacobiTau`, `jacobiNome`, `jacobiThetaArgument`: `τ = iK'/K`, the nome and `ζ` of the modulus `k`
  (DLMF 22.2.12, 22.2.1, 22.2.3).
* `jacobiModulusDomain`: the moduli `Re k > 0`, `k ∉ [1, ∞)`, on which DLMF's formulas hold.
* `jacobiPQ`: Glaisher's function `pq(z, k)` for complex `z` and `k`, with the twelve named
  functions `jacobiSn`, `jacobiCn`, `jacobiDn`, `jacobiSd`, `jacobiCd`, `jacobiSc`,
  `jacobiNs`, `jacobiNc`, `jacobiNd`, `jacobiDs`, `jacobiDc`, `jacobiCs`
  (DLMF 22.2.4–22.2.9).
* `IsJacobiRegular`: `z` is not a zero of `θ_r(ζ)`, so that the functions `pr(z, k)` are finite.
* `nevilleThetaOfTau`: Neville's theta functions (DLMF §20.1) in the Jacobi argument `z`.

## Implementation notes

* **Letters.** For each letter, `jacobiLetterTheta p ζ τ` is the normalized theta function
  `θ_s = θ₃(0)/(θ₂(0)θ₄(0)) θ₁(ζ)`, `θ_c = θ₂(ζ)/θ₂(0)`, `θ_d = θ₃(ζ)/θ₃(0)`, `θ_n = θ₄(ζ)/θ₄(0)`
  (all `θ_j(·|τ)` are the project's `DLMF.Elliptic.jacobiThetaOneTau … jacobiThetaFourTau`).
  By Jacobi's `θ₁'(0) = θ₂(0)θ₃(0)θ₄(0)` (DLMF 20.4.6) these are Neville's theta functions of
  §20.1, so `jacobiGlaisher p q ζ τ = θ_p/θ_q` (`= 1` when `p = q`) is DLMF 22.2.11, and the
  constants reproduce DLMF 22.2.4–22.2.9 exactly. Each `pq` is a *reduced* theta quotient, so
  its removable singularities are filled in (e.g. `sd` is finite where `sn` and `dn` have
  poles). Poles carry Lean's junk value `x / 0 = 0`.
* **Lattice form.** `jacobiPQOfTau p q z τ` uses `τ` (`Im τ > 0`) as the primary parameter, with
  `k = θ₂²(0|τ)/θ₃²(0|τ)`, `k' = θ₄²/θ₃²`, `K = (π/2)θ₃²(0|τ)`, `K' = -iτK` (DLMF 22.2.2,
  22.2.12) and `ζ = πz/(2K)`. Identities that follow from theta-function identities are
  proved in this form.
* **Modulus form.** `jacobiPQ p q z k` is DLMF's literal definition for complex `z` and `k`:
  `K(k) = completeEllipticK k` is the principal-branch integral 19.2.8,
  `K'(k) = completeEllipticKPrime k = K(√(1-k²))`, `τ = iK'/K` (22.2.12), `q = e^{iπτ}` (22.2.1) and
  `ζ = πz/(2K)` (22.2.3). DLMF's identities (with literal `k`, `k' = √(1-k²)`) hold on
  `jacobiModulusDomain = {Re k > 0} \ [1, ∞)`, where `k² ∈ ℂ \ ((-∞, 0] ∪ [1, ∞))`; there the
  inversion 22.2.2 is the theorem `jacobi_inversion_k`. On the other side of the imaginary
  axis the definition depends only on `k²`, so it gives the functions of `-k`.
* **Real functions.** The real-variable `DLMF.Elliptic.Real.jacobiSnOfParameter/Cnm/Dnm` (in the
  parameter `m = k²`, defined through the amplitude) are bridged to the modulus form by
  `jacobiSn_ofReal` and its companions for `0 < k < 1`, by ODE uniqueness.

Mathlib and TauCeti have no Jacobian elliptic functions.
-/

@[expose] public section

open Complex DLMF.Elliptic

open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

open DLMF.EllipticIntegrals (completeEllipticK completeEllipticKPrime)

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
def completeEllipticKOfTau (τ : ℂ) : ℂ := π / 2 * jacobiThetaThreeTau 0 τ ^ 2

/-- The complementary quarter period `K' = -iτK`, i.e. `τ = iK'/K` (DLMF 22.2.12). -/
@[dlmf 22.2.E12]
def completeEllipticKPrimeOfTau (τ : ℂ) : ℂ := -I * τ * completeEllipticKOfTau τ

/-- The modulus `k = θ₂²(0|τ)/θ₃²(0|τ)` (DLMF 22.2.2, first formula). -/
@[dlmf 22.2.E2]
def jacobiModulusOfTau (τ : ℂ) : ℂ := jacobiThetaTwoTau 0 τ ^ 2 / jacobiThetaThreeTau 0 τ ^ 2

/-- The complementary modulus `k' = θ₄²(0|τ)/θ₃²(0|τ)` (DLMF 22.2.2, second formula). -/
@[dlmf 22.2.E2]
def jacobiComodulusOfTau (τ : ℂ) : ℂ := jacobiThetaFourTau 0 τ ^ 2 / jacobiThetaThreeTau 0 τ ^ 2

/-- The theta argument `ζ = πz/(2K)` (DLMF 22.2.3) in the lattice parametrization; it equals
`z/θ₃²(0|τ)`. -/
@[dlmf 22.2.E3]
def jacobiThetaArgumentOfTau (z τ : ℂ) : ℂ := π * z / (2 * completeEllipticKOfTau τ)

/-- Glaisher's function `pq(z)` for the lattice parameter `τ` (`Im τ > 0`), DLMF 22.2.4–22.2.11
with `k = jacobiModulusOfTau τ`. -/
def jacobiPQOfTau (p q : JacobiLetter) (z τ : ℂ) : ℂ :=
    jacobiGlaisher p q (jacobiThetaArgumentOfTau z τ) τ

/-! ### The modulus (`k`) parametrization -/

/-- The complementary modulus `k' = √(1 - k²)` (principal square root, DLMF §22.1). -/
def jacobiComodulus (k : ℂ) : ℂ := (1 - k ^ 2) ^ (1 / 2 : ℂ)

/-- The lattice parameter `τ = iK'(k)/K(k)` of the modulus `k` (DLMF 22.2.12). -/
@[dlmf 22.2.E12]
def jacobiTau (k : ℂ) : ℂ := I * completeEllipticKPrime k / completeEllipticK k

/-- The nome `q = exp(-πK'(k)/K(k))` (DLMF 22.2.1). -/
@[dlmf 22.2.E1]
def jacobiNome (k : ℂ) : ℂ := cexp (-(π * completeEllipticKPrime k / completeEllipticK k))

/-- The theta argument `ζ = πz/(2K(k))` (DLMF 22.2.3). -/
@[dlmf 22.2.E3]
def jacobiThetaArgument (z k : ℂ) : ℂ := π * z / (2 * completeEllipticK k)

/-- The domain of moduli on which DLMF's formulas hold with literal `k` and the principal
`k' = √(1 - k²)`: `Re k > 0` and `k ∉ [1, ∞)`, equivalently `k² ∈ ℂ \ ((-∞, 0] ∪ [1, ∞))` with
`Re k > 0`. It contains `0 < k < 1`. -/
def jacobiModulusDomain : Set ℂ := {k | 0 < k.re ∧ (k.im = 0 → k.re < 1)}

/-- Glaisher's function `pq(z, k)` of DLMF 22.2.4–22.2.10 for complex `z` and `k`: the theta
quotient with `τ = iK'/K` (nome `q = e^{iπτ}`) at `ζ = πz/(2K)`. -/
def jacobiPQ (p q : JacobiLetter) (z k : ℂ) : ℂ :=
  jacobiGlaisher p q (jacobiThetaArgument z k) (jacobiTau k)

/-! ### The twelve functions in the modulus `k` -/

/-- `sn(z, k)` (DLMF 22.2.4). -/
@[dlmf 22.2.E4]
def jacobiSn (z k : ℂ) : ℂ := jacobiPQ .s .n z k
/-- `cn(z, k)` (DLMF 22.2.5). -/
@[dlmf 22.2.E5]
def jacobiCn (z k : ℂ) : ℂ := jacobiPQ .c .n z k
/-- `dn(z, k)` (DLMF 22.2.6). -/
@[dlmf 22.2.E6]
def jacobiDn (z k : ℂ) : ℂ := jacobiPQ .d .n z k
/-- `sd(z, k)` (DLMF 22.2.7). -/
@[dlmf 22.2.E7]
def jacobiSd (z k : ℂ) : ℂ := jacobiPQ .s .d z k
/-- `cd(z, k)` (DLMF 22.2.8). -/
@[dlmf 22.2.E8]
def jacobiCd (z k : ℂ) : ℂ := jacobiPQ .c .d z k
/-- `sc(z, k)` (DLMF 22.2.9). -/
@[dlmf 22.2.E9]
def jacobiSc (z k : ℂ) : ℂ := jacobiPQ .s .c z k
/-- `ns(z, k) = 1/sn(z, k)` (DLMF 22.2.4). -/
@[dlmf 22.2.E4]
def jacobiNs (z k : ℂ) : ℂ := jacobiPQ .n .s z k
/-- `nc(z, k) = 1/cn(z, k)` (DLMF 22.2.5). -/
@[dlmf 22.2.E5]
def jacobiNc (z k : ℂ) : ℂ := jacobiPQ .n .c z k
/-- `nd(z, k) = 1/dn(z, k)` (DLMF 22.2.6). -/
@[dlmf 22.2.E6]
def jacobiNd (z k : ℂ) : ℂ := jacobiPQ .n .d z k
/-- `ds(z, k) = 1/sd(z, k)` (DLMF 22.2.7). -/
@[dlmf 22.2.E7]
def jacobiDs (z k : ℂ) : ℂ := jacobiPQ .d .s z k
/-- `dc(z, k) = 1/cd(z, k)` (DLMF 22.2.8). -/
@[dlmf 22.2.E8]
def jacobiDc (z k : ℂ) : ℂ := jacobiPQ .d .c z k
/-- `cs(z, k) = 1/sc(z, k)` (DLMF 22.2.9). -/
@[dlmf 22.2.E9]
def jacobiCs (z k : ℂ) : ℂ := jacobiPQ .c .s z k

/-! ### The twelve functions in the lattice parameter `τ` -/

/-- `sn(z|τ)`: `sn` with modulus `k = θ₂²(0|τ)/θ₃²(0|τ)` (DLMF 22.2.4). -/
def jacobiSnOfTau (z τ : ℂ) : ℂ := jacobiPQOfTau .s .n z τ
/-- `cn(z|τ)` (DLMF 22.2.5). -/
def jacobiCnOfTau (z τ : ℂ) : ℂ := jacobiPQOfTau .c .n z τ
/-- `dn(z|τ)` (DLMF 22.2.6). -/
def jacobiDnOfTau (z τ : ℂ) : ℂ := jacobiPQOfTau .d .n z τ
/-- `sd(z|τ)` (DLMF 22.2.7). -/
def jacobiSdOfTau (z τ : ℂ) : ℂ := jacobiPQOfTau .s .d z τ
/-- `cd(z|τ)` (DLMF 22.2.8). -/
def jacobiCdOfTau (z τ : ℂ) : ℂ := jacobiPQOfTau .c .d z τ
/-- `sc(z|τ)` (DLMF 22.2.9). -/
def jacobiScOfTau (z τ : ℂ) : ℂ := jacobiPQOfTau .s .c z τ
/-- `ns(z|τ)`. -/
def jacobiNsOfTau (z τ : ℂ) : ℂ := jacobiPQOfTau .n .s z τ
/-- `nc(z|τ)`. -/
def jacobiNcOfTau (z τ : ℂ) : ℂ := jacobiPQOfTau .n .c z τ
/-- `nd(z|τ)`. -/
def jacobiNdOfTau (z τ : ℂ) : ℂ := jacobiPQOfTau .n .d z τ
/-- `ds(z|τ)`. -/
def jacobiDsOfTau (z τ : ℂ) : ℂ := jacobiPQOfTau .d .s z τ
/-- `dc(z|τ)`. -/
def jacobiDcOfTau (z τ : ℂ) : ℂ := jacobiPQOfTau .d .c z τ
/-- `cs(z|τ)`. -/
def jacobiCsOfTau (z τ : ℂ) : ℂ := jacobiPQOfTau .c .s z τ

/-- `z` is not congruent to the corner of letter `r` (the zeros of `θ_r(ζ)`); equivalently, the
functions `pr(z, k)` are finite at `z`. -/
def IsJacobiRegular (r : JacobiLetter) (z k : ℂ) : Prop :=
  jacobiLetterTheta r (jacobiThetaArgument z k) (jacobiTau k) ≠ 0

/-- Neville's theta functions (DLMF §20.1) as functions of the Jacobi argument `z`, with
`u = z/θ₃²(0|τ)`: `θ_s = θ₃²(0) θ₁(u)/θ₁'(0)`, `θ_c = θ₂(u)/θ₂(0)`, `θ_d = θ₃(u)/θ₃(0)`,
`θ_n = θ₄(u)/θ₄(0)`. -/
def nevilleThetaOfTau (p : JacobiLetter) (z τ : ℂ) : ℂ :=
  let u := z / jacobiThetaThreeTau 0 τ ^ 2
  match p with
  | .s => jacobiThetaThreeTau 0 τ ^ 2 * jacobiThetaOneTau u τ /
      deriv (fun w => jacobiThetaOneTau w τ) 0
  | .c => jacobiThetaTwoTau u τ / jacobiThetaTwoTau 0 τ
  | .d => jacobiThetaThreeTau u τ / jacobiThetaThreeTau 0 τ
  | .n => jacobiThetaFourTau u τ / jacobiThetaFourTau 0 τ

end DLMF.JacobiElliptic
end
end
